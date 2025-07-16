## 📘 README — `sva_gen.py`

This script auto-generates **SystemVerilog Assertions (SVAs)** using LLMs based on RTL code and optional specifications. It extracts preconditions/postconditions and produces immediate and concurrent assertions for each signal.

---

### 🛠️ Requirements

* Python 3.8+
* [Poetry](https://python-poetry.org/)
* OpenAI API access (configured in `llm_config.yaml`)

---

### 📂 Input Files

Defined in `io_config.yaml`:

```yaml
# io_config.yaml
verilog_code_file: path/to/design.sv
module_spec: path/to/spec.md                 # Optional; use 'none' if not available
parse_tree: path/to/tree.txt                # Optional; use 'none' if not available
extracted_signals: path/to/signals.yaml

output_precondition_file: outputs/preconditions/design_preconditions.txt
output_assertion_file: outputs/assertions/design_assertions.txt
jg_assertion_file: outputs/jg_assertions/design_jg_assertion.sv

llm_log_file: logs/llm_response_log.yaml
```

---

### 📄 LLM Config Example

```yaml
# llm_config.yaml (uses GPT-4o or compatible model)
default:
  llm:
    model: openai/gpt-4o
    max_tokens: 2048
  precondition:
    - role: system
      content: "...precondition prompt here..."
    - role: user
      content: "...signal slices, RTL, spec..."
  assertion:
    - role: system
      content: "...assertion prompt format..."
    - role: user
      content: "...preconditions and RTL..."
```

---

### 🚀 Run the Script

```bash
# Clone the repository:
git clone https://github.com/masc-ucsc/hagent.git
cd hagent

# Install dependencies with Poetry
poetry install

#Set OpenAI API Key (or other LLM provider)
export OPENAI_API_KEY=your-api-key

# Cleanup old logs and outputs
rm -rf gpt_logs/ outputs/ logs/ jg_proj/

# Run via poetry
poetry run python hagent/step/sva_gen/sva_gen.py \
    hagent/step/sva_gen/io_config.yaml \
    hagent/step/sva_gen/llm_config.yaml
```

---

### 📄 Output Files

* `outputs/preconditions/*.txt` – Extracted pre/post-conditions
* `outputs/assertions/*.txt` – Generated assertions
* `outputs/jg_assertions/*.sv` – SVAs formatted for JasperGold
* `logs/llm_response_log.yaml` – Full LLM response logs

---
