
# HAgent Software Design & Contribution Guidelines

These guidelines define the **engineering standards** for HAgent. The goal is to ensure correctness, extensibility, reproducibility, and long-term maintainability.

---

## 1. Core Design Principles (Mandatory)

### 1.1 Single Responsibility
- Every **module, class, and function must have exactly one responsibility**.
- If a component changes for more than one reason, it must be split.

### 1.2 Separation of Concerns
- Keep **agent logic, LLM interaction, tool execution, parsing, configuration, logging, and testing** in separate layers.

### 1.3 High Cohesion, Low Coupling
- Code inside a module should be **tightly related**.
- Dependencies between modules must be **minimal and explicit**.

### 1.4 Law of Demeter
- Do not chain through internal object structures.
- Only call:
  - Your own methods
  - Methods of parameters
  - Methods of objects you directly own or create

---

## 2. Extensibility & Architecture

### 2.1 Open/Closed Principle
- Core abstractions (agent steps, passes, tool adapters) must be:
  - **Open for extension**
  - **Closed for modification**
- New functionality should be added via:
  - New derived classes
  - New plugins
  - New registered steps

### 2.2 Composition over Inheritance
- Favor **composition of behaviors** instead of deep class hierarchies.
- Inheritance is allowed only for:
  - Stable abstraction contracts
  - True “is-a” relationships

### 2.3 Backward Compatibility
- Changes must not break:
  - Existing configs
  - Existing agent pipelines
  - Existing datasets
- Breaking changes require:
  - Version bump
  - Migration notes

---

## 3. Simplicity & Over-Engineering Control

### 3.1 KISS
- Prefer the **simplest correct implementation**.
- Avoid cleverness that reduces readability.

### 3.2 YAGNI
- Do **not** add:
  - Anticipated features
  - Speculative abstractions
  - Future-proofing without a concrete use-case

### 3.3 DRY (With Restraint)
- Do not duplicate logic.
- Refactor only after a clear pattern emerges.
- Follow the **Rule of Three** before abstracting.

---

## 4. Correctness & Robustness

### 4.1 Design by Contract
- All external-facing functions must define:
  - Preconditions
  - Postconditions
  - Invariants
- Use:
  - Assertions
  - Explicit error types
  - Clear failure modes

### 4.2 Fail Fast
- Detect invalid states immediately.
- Abort early with precise diagnostic messages.
- Silent failure is prohibited.

---

## 5. Testing & Reproducibility

### 5.1 Automated Testing
- Every contribution must include:
  - Unit tests for pure logic
  - Integration tests for tool wrapping
- Tests must be:
  - Deterministic
  - Independent
  - Fast

### 5.2 Command–Query Separation
- A function must either:
  - **Return data**, or
  - **Modify state**
- Never do both.

---

## 6. Code Quality & Style

### 6.1 Naming & Readability
- Use:
  - Descriptive identifiers
  - Domain-accurate terminology
- Avoid:
  - Abbreviations
  - Cryptic variable names
  - Implicit meaning

### 6.2 Function & Class Size
- Functions should generally be:
  - < 100 lines
  - One logical operation
- Classes should encapsulate a **single abstraction**.

### 6.3 Documentation
- Comments must:
  - Explain *why*, not *what*
  - Justify non-obvious logic with # WARNING: txt

### 6.4 Code Hygiene (Boy Scout Rule)
- Every PR should:
  - Improve clarity or structure
  - Not introduce tech debt
  - Remove dead code if encountered

---

## 7. HAgent-Specific Rules

- All **agent steps must be composable** and execution-order independent.
- LLM outputs must **never directly control external tools** without validation.
- Tool adapters must be:
  - Deterministic
  - Restart-safe
  - Side-effect isolated
- Logs must be:
  - Structured
  - Machine-parsable
  - Reproducibility-friendly

---

## 8. Summary Checklist (PR Gate)

Before submitting a PR, confirm:

- [ ] Single responsibility satisfied
- [ ] No unnecessary abstraction
- [ ] Inputs validated
- [ ] Failure modes explicit
- [ ] Unit tests added
- [ ] Integration tests updated
- [ ] Deterministic behavior preserved
- [ ] No new technical debt introduced
