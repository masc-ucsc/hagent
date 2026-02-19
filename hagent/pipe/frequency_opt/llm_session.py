# See LICENSE for details
"""
Persistent LLM conversation manager for cross-step memory.

This module provides LLM session management that persists conversation
state to YAML, enabling feedback loops across step boundaries.

Key features:
- Maintains conversation history for iterative refinement
- Supports feedback injection (LEC failures, timing regressions)
- Serializes to YAML for pipeline persistence
- Tracks token usage and cost across the pipeline
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional

from hagent.core.llm_wrap import LLM_wrap


@dataclass
class ConversationMessage:
    """A single message in the LLM conversation."""

    role: str  # 'user', 'assistant', 'system'
    content: str
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class LLMSessionState:
    """
    Serializable LLM session state for YAML persistence.

    This state is written to YAML after each LLM step and restored
    when the step runs again (e.g., during retry loops).
    """

    model: str = ''
    messages: List[ConversationMessage] = field(default_factory=list)
    total_tokens: int = 0
    total_cost: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to YAML-compatible dict."""
        return {
            'model': self.model,
            'messages': [{'role': m.role, 'content': m.content, 'metadata': m.metadata} for m in self.messages],
            'total_tokens': self.total_tokens,
            'total_cost': self.total_cost,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'LLMSessionState':
        """Deserialize from YAML dict."""
        messages = [
            ConversationMessage(
                role=m.get('role', 'user'),
                content=m.get('content', ''),
                metadata=m.get('metadata', {}),
            )
            for m in data.get('messages', [])
        ]
        return cls(
            model=data.get('model', ''),
            messages=messages,
            total_tokens=data.get('total_tokens', 0),
            total_cost=data.get('total_cost', 0.0),
        )


class PersistentLLMSession:
    """
    LLM session that persists conversation state to YAML.

    This class wraps LLM_wrap and adds:
    - Conversation history management
    - Feedback injection for retry scenarios
    - State serialization for YAML output

    Usage:
        # Create or restore session
        session = PersistentLLMSession.from_yaml_data(llm_wrap, data)

        # Add feedback if retrying
        if feedback:
            session.add_feedback('lec_failure', feedback_details)

        # Call LLM with history
        responses = session.call_with_history(prompt_dict, 'optimize_prompt')

        # Save state for next step
        output['llm_session'] = session.get_state_dict()
    """

    def __init__(self, llm: LLM_wrap, state: Optional[LLMSessionState] = None):
        """
        Initialize session.

        Args:
            llm: The LLM_wrap instance to use for API calls
            state: Optional existing state to restore
        """
        self.llm = llm
        self.state = state or LLMSessionState(model=llm.llm_args.get('model', ''))

    def add_user_message(self, content: str, metadata: Optional[Dict] = None):
        """Add a user message to the conversation history."""
        self.state.messages.append(
            ConversationMessage(
                role='user',
                content=content,
                metadata=metadata or {},
            )
        )

    def add_assistant_response(self, content: str, metadata: Optional[Dict] = None):
        """Add an assistant response to the conversation history."""
        self.state.messages.append(
            ConversationMessage(
                role='assistant',
                content=content,
                metadata=metadata or {},
            )
        )

    def add_feedback(self, feedback_type: str, details: str, metadata: Optional[Dict] = None):
        """
        Add feedback to the conversation for retry scenarios.

        This is the key method for iterative refinement:
        - Elaboration failure: include compilation/elaboration error message
        - LEC failure: include error message and counterexample
        - Timing regression: include old vs new timing numbers

        Args:
            feedback_type: Type of feedback ('lec_failure', 'timing_regression')
            details: Human-readable feedback details
            metadata: Optional metadata dict
        """
        feedback_content = f'[{feedback_type.upper()} FEEDBACK]\n{details}'
        self.add_user_message(feedback_content, metadata={'feedback_type': feedback_type, **(metadata or {})})

    def get_history_for_prompt(self, max_messages: int = 10) -> List[Dict[str, str]]:
        """
        Get conversation history formatted for LLM prompt.

        Args:
            max_messages: Maximum number of recent messages to include

        Returns:
            List of message dicts with 'role' and 'content' keys
        """
        recent = self.state.messages[-max_messages:] if max_messages > 0 else self.state.messages
        return [{'role': m.role, 'content': m.content} for m in recent]

    def call_with_history(
        self,
        prompt_dict: Dict,
        prompt_index: str,
        n: int = 1,
        max_history: int = 6,
    ) -> List[str]:
        """
        Call LLM with conversation history included.

        The history is injected into LLM_wrap's chat_history, allowing
        the LLM to "remember" previous attempts and their failures.

        Args:
            prompt_dict: Variables for prompt template
            prompt_index: Name of prompt template in config
            n: Number of responses to generate
            max_history: Number of recent messages to include

        Returns:
            List of response strings from LLM
        """
        # Inject history
        self.llm.chat_history = self.get_history_for_prompt(max_history)

        # Make the call
        responses = self.llm.inference(prompt_dict, prompt_index, n=n, max_history=max_history)

        # Update state
        self.state.total_tokens += self.llm.total_tokens
        self.state.total_cost += self.llm.total_cost

        # Record the exchange
        if responses:
            self.add_assistant_response(responses[0], metadata={'prompt_index': prompt_index})

        return responses

    def get_state(self) -> LLMSessionState:
        """Get the session state object."""
        return self.state

    def get_state_dict(self) -> Dict[str, Any]:
        """Get session state as YAML-serializable dict."""
        return self.state.to_dict()

    @classmethod
    def from_yaml_data(cls, llm: LLM_wrap, data: Dict) -> 'PersistentLLMSession':
        """
        Create or restore session from YAML data.

        Args:
            llm: The LLM_wrap instance
            data: Pipeline data dict (may contain 'llm_session' key)

        Returns:
            PersistentLLMSession instance (new or restored)
        """
        if 'llm_session' in data and data['llm_session']:
            state = LLMSessionState.from_dict(data['llm_session'])
            return cls(llm, state)
        return cls(llm)
