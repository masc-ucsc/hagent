# See LICENSE for details
"""
LLM conversation session manager.

This module provides LLM session management with conversation history,
feedback injection, and optional YAML persistence for pipeline state.

Key features:
- Maintains conversation history for iterative refinement
- Supports feedback injection (LEC failures, timing regressions)
- Context truncation for variant-level isolation
- Optional serialization to YAML for cross-step persistence
- Tracks token usage and cost
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
    # messages are in chronological order (initial prompt first, then conversation)
    messages: List[ConversationMessage] = field(default_factory=list)
    initial_prompt_count: int = 0  # number of initial template messages (system + user)
    total_tokens: int = 0
    total_cost: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to YAML-compatible dict."""
        return {
            'model': self.model,
            'messages': [{'role': m.role, 'content': m.content, 'metadata': m.metadata} for m in self.messages],
            'initial_prompt_count': self.initial_prompt_count,
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
            initial_prompt_count=data.get('initial_prompt_count', 0),
            total_tokens=data.get('total_tokens', 0),
            total_cost=data.get('total_cost', 0.0),
        )


class LLMSession:
    """
    Manages a conversation with an LLM.

    Stores the full conversation including the initial system+user prompt
    (captured from the first LLM call) and all subsequent exchanges.

    The template (system + user prompt) comes from the YAML config and is
    always formatted by LLM_wrap for the API call. This session stores a
    copy of the initial prompt for completeness and passes only non-template
    messages as chat_history. Truncation to max_history is handled solely
    by LLM_wrap._call_llm (single truncation point).

    Usage:
        # Create a fresh session
        session = LLMSession.create(llm_wrap)

        # Or restore from YAML
        session = LLMSession.from_yaml_data(llm_wrap, data)

        # Call LLM with history
        responses = session.call_with_history(prompt_dict, 'optimize_prompt')

        # Add feedback for retry
        session.add_feedback('lec_failure', feedback_details)

        # Truncate history (e.g., between variant deep-dives)
        session.truncate()

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

    @classmethod
    def create(cls, llm: LLM_wrap) -> 'LLMSession':
        """Create a fresh session with no prior state."""
        return cls(llm)

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

    def truncate(self, keep_count: int = 0):
        """Discard conversation history, preserving the initial prompt.

        The initial system + user prompt (first initial_prompt_count messages)
        is always kept. keep_count controls how many additional messages
        beyond the initial prompt to retain.

        keep_count=0 means "reset to just the initial prompt" -- the next
        call will behave like a fresh conversation.

        Args:
            keep_count: Number of messages to retain AFTER the initial prompt (default: 0)
        """
        ipc = self.state.initial_prompt_count
        self.state.messages = self.state.messages[: ipc + keep_count]
        self.llm.chat_history = []

    def get_history_for_prompt(self) -> List[Dict[str, str]]:
        """
        Get conversation history formatted for LLM prompt.

        Returns all non-initial-prompt messages. The initial prompt is excluded
        because LLM_wrap always includes it via template formatting. Truncation
        to max_history is handled by LLM_wrap._call_llm (single truncation point).

        Returns:
            List of message dicts with 'role' and 'content' keys
        """
        non_initial = self.state.messages[self.state.initial_prompt_count :]
        return [{'role': m.role, 'content': m.content} for m in non_initial]

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
        Truncation is handled solely by LLM_wrap._call_llm via max_history.

        Args:
            prompt_dict: Variables for prompt template
            prompt_index: Name of prompt template in config
            n: Number of responses to generate
            max_history: Number of recent history messages to include (truncated by LLM_wrap)

        Returns:
            List of response strings from LLM
        """
        # Inject all non-initial history (as LLM_wrap has initial system + user message via prompt_dict);
        # LLM_wrap handles truncation via max_history
        self.llm.chat_history = self.get_history_for_prompt()

        # Make the call
        responses = self.llm.inference(prompt_dict, prompt_index, n=n, max_history=max_history)

        # Capture initial prompt on first call (for complete conversation record)
        # TODO: make system prompt a standalone field of this class,
        # record the initial user prompt in the `self.state.initial_prompt`
        if self.state.initial_prompt_count == 0 and self.llm._last_formatted_messages:
            initial_msgs = [
                ConversationMessage(
                    role=m['role'],
                    content=m['content'],
                    metadata={'is_initial_prompt': True},
                )
                for m in self.llm._last_formatted_messages
            ]
            self.state.messages = initial_msgs + self.state.messages
            self.state.initial_prompt_count = len(initial_msgs)
        elif self.state.initial_prompt_count > 0 and self.llm._last_formatted_messages:
            # Non-first call: record user message from re-formatted template
            # so state.messages maintains proper user/assistant alternation.
            # Skip 'system' role — it's already in the initial prompt and doesn't change.
            for m in self.llm._last_formatted_messages:
                if m['role'] == 'user':
                    self.add_user_message(m['content'], metadata={'prompt_index': prompt_index})

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
    def from_yaml_data(cls, llm: LLM_wrap, data: Dict) -> 'LLMSession':
        """
        Create or restore session from YAML data.

        Args:
            llm: The LLM_wrap instance
            data: Pipeline data dict (may contain 'llm_session' key)

        Returns:
            LLMSession instance (new or restored)
        """
        if 'llm_session' in data and data['llm_session']:
            state = LLMSessionState.from_dict(data['llm_session'])
            return cls(llm, state)
        return cls(llm)


# Backward compatibility alias
PersistentLLMSession = LLMSession
