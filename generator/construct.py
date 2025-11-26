import os
import argparse
from typing import Any, Dict, List, Tuple, Optional
from abc import ABC, abstractmethod
import openai
import subprocess
import tempfile
import re
import time
import json
from dataclasses import dataclass, field, asdict

@dataclass
class GenerationStatistics:
    """Track statistics about the generation and correction process."""
    # Timing
    start_time: float = field(default_factory=time.time)
    end_time: Optional[float] = None
    cfg_generation_time: float = 0.0
    initial_generator_time: float = 0.0
    correction_time: float = 0.0
    
    # LLM usage
    total_llm_calls: int = 0
    cfg_llm_calls: int = 0
    generator_llm_calls: int = 0
    refinement_llm_calls: int = 0
    repair_llm_calls: int = 0
    
    # Token usage (if available from API)
    total_prompt_tokens: int = 0
    total_completion_tokens: int = 0
    total_tokens: int = 0
    
    # Correction iterations
    correction_iterations: int = 0
    max_iterations: int = 0
    
    # Generation and validation stats
    total_terms_generated: int = 0
    total_terms_valid: int = 0
    terms_per_iteration: List[int] = field(default_factory=list)
    valid_per_iteration: List[int] = field(default_factory=list)
    passing_rate_per_iteration: List[float] = field(default_factory=list)
    
    # Error tracking
    execution_errors: int = 0
    syntax_errors: int = 0
    solver_errors: int = 0
    unique_error_types: List[str] = field(default_factory=list)
    
    # Generator info
    theory_name: str = ""
    theory_abbrev: str = ""
    backend: str = ""
    model: str = ""
    
    def finalize(self):
        """Mark the end of statistics collection."""
        self.end_time = time.time()
    
    @property
    def total_time(self) -> float:
        """Total elapsed time in seconds."""
        end = self.end_time if self.end_time else time.time()
        return end - self.start_time
    
    @property
    def overall_passing_rate(self) -> float:
        """Overall passing rate across all generations."""
        if self.total_terms_generated == 0:
            return 0.0
        return self.total_terms_valid / self.total_terms_generated
    
    @property
    def final_passing_rate(self) -> float:
        """Passing rate in the final iteration."""
        if not self.passing_rate_per_iteration:
            return 0.0
        return self.passing_rate_per_iteration[-1]
    
    def to_dict(self) -> Dict:
        """Convert to dictionary for JSON serialization."""
        data = asdict(self)
        # Add computed properties
        data['total_time'] = self.total_time
        data['overall_passing_rate'] = self.overall_passing_rate
        data['final_passing_rate'] = self.final_passing_rate
        return data
    
    def to_json(self, filepath: Optional[str] = None) -> str:
        """Export statistics as JSON string or file."""
        json_str = json.dumps(self.to_dict(), indent=2)
        if filepath:
            with open(filepath, 'w') as f:
                f.write(json_str)
        return json_str
    
    def print_summary(self):
        """Print a human-readable summary of statistics."""
        print("\n" + "=" * 60)
        print("GENERATION STATISTICS SUMMARY")
        print("=" * 60)
        
        print(f"\n📊 Theory: {self.theory_name} ({self.theory_abbrev})")
        print(f"🤖 Model: {self.backend} - {self.model}")
        
        print(f"\n⏱️  TIMING:")
        print(f"  Total time: {self.total_time:.2f}s")
        print(f"  - CFG generation: {self.cfg_generation_time:.2f}s")
        print(f"  - Initial generator: {self.initial_generator_time:.2f}s")
        print(f"  - Correction process: {self.correction_time:.2f}s")
        
        print(f"\n🔄 LLM CALLS:")
        print(f"  Total API calls: {self.total_llm_calls}")
        print(f"  - CFG generation: {self.cfg_llm_calls}")
        print(f"  - Generator creation: {self.generator_llm_calls}")
        print(f"  - Refinements: {self.refinement_llm_calls}")
        print(f"  - Repairs: {self.repair_llm_calls}")
        
        if self.total_tokens > 0:
            print(f"\n💰 TOKEN USAGE:")
            print(f"  Prompt tokens: {self.total_prompt_tokens:,}")
            print(f"  Completion tokens: {self.total_completion_tokens:,}")
            print(f"  Total tokens: {self.total_tokens:,}")
            
            # Rough cost estimation (update prices as needed)
            cost_map = {
                "gpt-4": (0.03, 0.06),  # per 1K tokens (input, output)
                "gpt-4-turbo": (0.01, 0.03),
                "gpt-3.5-turbo": (0.0015, 0.002),
                "claude-3-5-sonnet": (0.003, 0.015),
                "deepseek-chat": (0.0001, 0.0002),
            }
            
            for model_name, (input_price, output_price) in cost_map.items():
                if model_name in self.model.lower():
                    estimated_cost = (self.total_prompt_tokens / 1000 * input_price +
                                    self.total_completion_tokens / 1000 * output_price)
                    print(f"  Estimated cost: ${estimated_cost:.4f}")
                    break
        
        print(f"\n🔧 CORRECTION PROCESS:")
        print(f"  Iterations: {self.correction_iterations}/{self.max_iterations}")
        print(f"  Execution errors: {self.execution_errors}")
        print(f"  Syntax errors: {self.syntax_errors}")
        print(f"  Solver errors: {self.solver_errors}")
        
        print(f"\n✅ VALIDATION RESULTS:")
        print(f"  Total terms generated: {self.total_terms_generated}")
        print(f"  Total valid terms: {self.total_terms_valid}")
        print(f"  Overall passing rate: {self.overall_passing_rate:.1%}")
        print(f"  Final passing rate: {self.final_passing_rate:.1%}")
        
        if self.passing_rate_per_iteration:
            print(f"\n📈 PASSING RATE PER ITERATION:")
            for i, rate in enumerate(self.passing_rate_per_iteration, 1):
                valid = self.valid_per_iteration[i-1] if i-1 < len(self.valid_per_iteration) else 0
                total = self.terms_per_iteration[i-1] if i-1 < len(self.terms_per_iteration) else 0
                bar_length = int(rate * 20)
                bar = "█" * bar_length + "░" * (20 - bar_length)
                print(f"  Iter {i}: {bar} {rate:.1%} ({valid}/{total})")
        
        print("\n" + "=" * 60)


GRAMMAR_PROMPT_TEMPLATE = """
Please generate a context-free grammar (CFG) in BNF or EBNF format that produces Boolean terms valid in the SMT-LIB syntax for the {theory_name} theory. The grammar should accurately reflect the following theory-specific constructs and constraints:

```
{documentation}
```
"""

GENERATOR_PROMPT_TEMPLATE = """
You are a senior Python and SMT-LIB2 developer. Write a **single self-contained Python module** that implements a random formula generator for the {theory_name} theory, following the CFG below **exactly**.

CFG:
```
{cfg}
```

## Task

Implement **exactly one** public function:

    generate_{theory_abbrev}_formula_with_decls()

Requirements:

1. **Signature & return value**
   - Takes **no arguments**.
   - Returns a **tuple (decls, formula)** where:
     - `decls`: SMT-LIB2 declarations of all functions, constants, and sorts used.
     - `formula`: a single SMT-LIB2 Boolean **term only** (no `(assert ...)`, no `(check-sat)`, no `(set-logic ...)`, etc.).

2. **SMT-LIB2 and CFG compliance**
   - Every generated formula must:
     - Be derivable from the CFG above.
     - Be well-typed and consistent with the declarations.
     - Use standard SMT-LIB2 syntax when appropriate.
   - Every symbol used in `formula` must be declared in `decls` with correct sort and arity.

3. **Randomness**
   - Use only the Python standard library (especially `random`).
   - Randomize: number of variables, functions/consts, operators, and term structure.
   - Enforce a hard recursion/depth limit to avoid infinite or huge terms.
   - Formulas should usually be non-trivial (nested connectives, arithmetic, etc.), but simple ones are allowed due to randomness.

4. **Symbol naming**
   - All sorts, functions, and variables must have randomly generated names.
   - Each name:
     - ≥ 5 characters.
     - Only lowercase ASCII letters `[a-z]`.
     - Must not be an SMT-LIB keyword (e.g., `and`, `or`, `not`, `ite`, `true`, `false`, `exists`, `forall`, etc.).
   - Avoid overusing the same few names.

5. **Code constraints**
   - **Pure Python only** in a single module; no imports beyond the standard library.
   - No I/O (no file/network access, no printing).
   - No `if __name__ == "__main__":`, no tests or demo code.
   - Implement all helpers in this module (name generation, term construction, CFG-based recursion, etc.).

6. **Output format (strict)**
   - Respond with **one fenced code block** containing the complete Python module.
   - Use this exact format:

```python
# complete Python module
import random

# helper functions ...

def generate_{theory_abbrev}_formula_with_decls():
    ...
    return decls_str, formula_str
```

   - Do **not** include any explanation or text outside that single ```python code block.
"""

REFINE_PROMPT_TEMPLATE = """
The provided Python code for an SMT formula generator is producing syntactically invalid term and causing solver errors. Your task is to correct the Python code to ensure it generates syntactically valid terms. Focus solely on fixing the errors and improving the validity of the generated terms. Provide only the complete, corrected Python implementation, wrapped in triple backticks (```). 

### Invalid terms and the corresponding errors
{errors}

### Current generator implementation
```python
{generator_code}
```
"""

# Prompt template for repairing non-executable generator code (syntax/runtime/import errors)
REPAIR_PROMPT_TEMPLATE = """
The provided Python module for an SMT formula generator fails to execute (syntax/import/runtime error). Your task is to FIX the code so that it imports and runs successfully and meets the generator requirements.

### Error traceback / execution failure
{error}

### Requirements (must all be satisfied)
- Pure Python single module using only the standard library
- Define exactly one public function named generate_*_formula_with_decls() (already present; keep its contract)
- The function returns (decls, formula) where:
    - decls: SMT-LIB2 declarations of all symbols used
    - formula: a single SMT-LIB2 Boolean term only (no assert/check-sat/set-logic)
- Include all helpers in the same module
- Avoid I/O, printing, and external imports

### Current module implementation
```python
{generator_code}
```

Provide ONLY the complete corrected Python module wrapped in triple backticks (```), with no extra commentary.
"""


class LLMClient(ABC):
    """Abstract base class for LLM clients."""
    def __init__(self, name: str, temperature: float = 0.2, max_tokens: int = 2048):
        self.name = name
        self.temperature = temperature
        self.max_tokens = max_tokens
        self.stats: Optional[GenerationStatistics] = None

    def set_statistics(self, stats: 'GenerationStatistics'):
        """Set the statistics object to track usage."""
        self.stats = stats

    @abstractmethod
    def chat(self, messages: List[Dict[str, str]]) -> str:
        """Send a chat request and return the response."""
        pass


class OpenAIClient(LLMClient):
    """LLM client using OpenAI's API (openai>=1.0 style)."""
    def __init__(self, model: str = "gpt-4", temperature: float = 0.2, max_tokens: int = 2048):
        super().__init__(model, temperature, max_tokens)

        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ValueError("OPENAI_API_KEY environment variable not set")

        # Support custom base URL via OPENAI_BASE_URL
        base_url = os.getenv("OPENAI_BASE_URL")

        # Use the new client-based API from openai>=1.0.0
        # We intentionally keep a dedicated client instance on the object
        # instead of relying on global openai.* attributes.
        self.client = openai.OpenAI(api_key=api_key, base_url=base_url)

    def chat(self, messages: List[Dict[str, str]]) -> str:
        """Send a chat completion request and return the assistant's reply text."""
        try:
            response = self.client.chat.completions.create(
                model=self.name,
                messages=messages,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
            )
            # Track token usage if stats object is available
            if self.stats and hasattr(response, 'usage') and response.usage:
                self.stats.total_prompt_tokens += response.usage.prompt_tokens
                self.stats.total_completion_tokens += response.usage.completion_tokens
                self.stats.total_tokens += response.usage.total_tokens
                self.stats.total_llm_calls += 1
            
            # New SDK returns a choice object where message.content is a string
            return response.choices[0].message.content.strip()
        except Exception as e:
            raise RuntimeError(f"OpenAI API call failed: {e}")


class AnthropicClient(LLMClient):
    """LLM client using Anthropic's API."""
    def __init__(self, model: str = "claude-3-5-sonnet-20241022", temperature: float = 0.2, max_tokens: int = 2048):
        super().__init__(model, temperature, max_tokens)
        self.api_key = os.getenv("ANTHROPIC_API_KEY")
        if not self.api_key:
            raise ValueError("ANTHROPIC_API_KEY environment variable not set")
        
        try:
            import anthropic
            self.client = anthropic.Anthropic(api_key=self.api_key)
        except ImportError:
            raise ImportError("anthropic package not installed. Install with: pip install anthropic")

    def chat(self, messages: List[Dict[str, str]]) -> str:
        try:
            # Extract system message if present
            system_message = None
            user_messages = []
            for msg in messages:
                if msg["role"] == "system":
                    system_message = msg["content"]
                else:
                    user_messages.append(msg)
            
            # Create Anthropic request
            kwargs = {
                "model": self.name,
                "max_tokens": self.max_tokens,
                "temperature": self.temperature,
                "messages": user_messages,
            }
            if system_message:
                kwargs["system"] = system_message
            
            response = self.client.messages.create(**kwargs)
            
            # Track token usage if stats object is available
            if self.stats and hasattr(response, 'usage') and response.usage:
                self.stats.total_prompt_tokens += response.usage.input_tokens
                self.stats.total_completion_tokens += response.usage.output_tokens
                self.stats.total_tokens += response.usage.input_tokens + response.usage.output_tokens
                self.stats.total_llm_calls += 1
            
            return response.content[0].text.strip()
        except Exception as e:
            raise RuntimeError(f"Anthropic API call failed: {e}")


class DeepSeekClient(LLMClient):
    """LLM client using DeepSeek's API (OpenAI-compatible)."""
    def __init__(self, model: str = "deepseek-chat", temperature: float = 0.2, max_tokens: int = 2048):
        super().__init__(model, temperature, max_tokens)
        self.api_key = os.getenv("DEEPSEEK_API_KEY")
        if not self.api_key:
            raise ValueError("DEEPSEEK_API_KEY environment variable not set")
        
        self.base_url = os.getenv("DEEPSEEK_BASE_URL", "https://api.deepseek.com")
        self.client = openai.OpenAI(api_key=self.api_key, base_url=self.base_url)

    def chat(self, messages: List[Dict[str, str]]) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.name,
                messages=messages,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
            )
            # Track token usage if stats object is available
            if self.stats and hasattr(response, 'usage') and response.usage:
                self.stats.total_prompt_tokens += response.usage.prompt_tokens
                self.stats.total_completion_tokens += response.usage.completion_tokens
                self.stats.total_tokens += response.usage.total_tokens
                self.stats.total_llm_calls += 1
            
            return response.choices[0].message.content.strip()
        except Exception as e:
            raise RuntimeError(f"DeepSeek API call failed: {e}")


class GeminiClient(LLMClient):
    """LLM client using Google Gemini's API (OpenAI-compatible endpoint)."""
    def __init__(self, model: str = "gemini-pro", temperature: float = 0.2, max_tokens: int = 2048):
        super().__init__(model, temperature, max_tokens)
        self.api_key = os.getenv("GOOGLE_API_KEY") or os.getenv("GEMINI_API_KEY")
        if not self.api_key:
            raise ValueError("GOOGLE_API_KEY or GEMINI_API_KEY environment variable not set")
        
        self.base_url = os.getenv("GEMINI_BASE_URL", "https://generativelanguage.googleapis.com/v1beta/openai/")
        self.client = openai.OpenAI(api_key=self.api_key, base_url=self.base_url)

    def chat(self, messages: List[Dict[str, str]]) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.name,
                messages=messages,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
            )
            # Track token usage if stats object is available
            if self.stats and hasattr(response, 'usage') and response.usage:
                self.stats.total_prompt_tokens += response.usage.prompt_tokens
                self.stats.total_completion_tokens += response.usage.completion_tokens
                self.stats.total_tokens += response.usage.total_tokens
                self.stats.total_llm_calls += 1
            
            return response.choices[0].message.content.strip()
        except Exception as e:
            raise RuntimeError(f"Gemini API call failed: {e}")


class QwenClient(LLMClient):
    """LLM client using Qwen's API (OpenAI-compatible DashScope endpoint)."""
    def __init__(self, model: str = "qwen-turbo", temperature: float = 0.2, max_tokens: int = 2048):
        super().__init__(model, temperature, max_tokens)
        self.api_key = os.getenv("DASHSCOPE_API_KEY")
        if not self.api_key:
            raise ValueError("DASHSCOPE_API_KEY environment variable not set")
        
        # Beijing region by default (use QWEN_BASE_URL for Singapore region)
        self.base_url = os.getenv("QWEN_BASE_URL", "https://dashscope.aliyuncs.com/compatible-mode/v1")
        self.client = openai.OpenAI(api_key=self.api_key, base_url=self.base_url)

    def chat(self, messages: List[Dict[str, str]]) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.name,
                messages=messages,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
            )
            # Track token usage if stats object is available
            if self.stats and hasattr(response, 'usage') and response.usage:
                self.stats.total_prompt_tokens += response.usage.prompt_tokens
                self.stats.total_completion_tokens += response.usage.completion_tokens
                self.stats.total_tokens += response.usage.total_tokens
                self.stats.total_llm_calls += 1
            
            return response.choices[0].message.content.strip()
        except Exception as e:
            raise RuntimeError(f"Qwen API call failed: {e}")


def make_llm_client(
    backend: str = "openai",
    model: str = None,
    temperature: float = 0.2,
    max_tokens: int = 2048,
) -> LLMClient:
    """
    Factory function to create an LLM client.
    
    Args:
        backend: The backend to use ('openai', 'anthropic', 'deepseek', 'gemini', 'qwen')
        model: The model name (if None, uses default for backend)
        temperature: Sampling temperature
        max_tokens: Maximum tokens to generate
        
    Returns:
        An LLMClient instance
    """
    if backend == "openai":
        model = model or "gpt-4"
        return OpenAIClient(model=model, temperature=temperature, max_tokens=max_tokens)
    elif backend == "anthropic":
        model = model or "claude-3-5-sonnet-20241022"
        return AnthropicClient(model=model, temperature=temperature, max_tokens=max_tokens)
    elif backend == "deepseek":
        model = model or "deepseek-chat"
        return DeepSeekClient(model=model, temperature=temperature, max_tokens=max_tokens)
    elif backend == "gemini":
        model = model or "gemini-pro"
        return GeminiClient(model=model, temperature=temperature, max_tokens=max_tokens)
    elif backend == "qwen":
        model = model or "qwen-turbo"
        return QwenClient(model=model, temperature=temperature, max_tokens=max_tokens)
    else:
        raise ValueError(f"Unsupported backend: {backend}. Choose from: openai, anthropic, deepseek, gemini, qwen")


def summarize_cfg(documentation: str, theory_name: str, llm_client: LLMClient) -> str:
    """
    Use an LLM to summarize the context-free grammar (CFG) for an SMT theory.

    Args:
        documentation: The documentation text for the SMT theory.
        theory_name: Name of the SMT theory.
        llm_client: An instance of LLMClient.

    Returns:
        The summarized CFG as a string.
    """
    start_time = time.time()
    prompt = GRAMMAR_PROMPT_TEMPLATE.format(
        theory_name=theory_name,
        documentation=documentation
    )
    messages = [
        {"role": "system", "content": "You are an expert in SMT-LIB and formal grammars."},
        {"role": "user", "content": prompt}
    ]
    response = llm_client.chat(messages)
    
    # Track statistics
    if llm_client.stats:
        llm_client.stats.cfg_generation_time = time.time() - start_time
        llm_client.stats.cfg_llm_calls += 1
    
    return response


def generate_smt_generator(cfg: str, theory_name: str, theory_abbrev: str, llm_client: LLMClient) -> str:
    """
    Use an LLM to generate code for an SMT theory generator from a CFG.

    Args:
        cfg: The context-free grammar for the SMT theory.
        theory_name: Name of the SMT theory.
        theory_abbrev: Abbreviated name for the theory (used in function names).
        llm_client: An instance of LLMClient.

    Returns:
        The generated code as a string.
    """
    start_time = time.time()
    prompt = GENERATOR_PROMPT_TEMPLATE.format(
        cfg=cfg,
        theory_name=theory_name,
        theory_abbrev=theory_abbrev
    )
    messages = [
        {"role": "system", "content": "You are an expert in SMT-LIB and code generation."},
        {"role": "user", "content": prompt}
    ]
    response = llm_client.chat(messages)
    
    # Track statistics
    if llm_client.stats:
        llm_client.stats.initial_generator_time = time.time() - start_time
        llm_client.stats.generator_llm_calls += 1
    
    return response


def correct_generator(
    generator_code: str,
    llm_client: LLMClient,
    solvers: List[Any],
    max_iter: int = 10,
    sample_size: int = 20,
    min_valid: int = 18,
) -> str:
    """
    Self-correct an SMT generator using LLM-guided refinement and solver feedback.

    Args:
        generator_code: The initial generator implementation (as code string).
        llm_client: An instance of LLMClient.
        solvers: List of SMT solver interfaces to use for validation.
        max_iter: Maximum number of refinement iterations.
        sample_size: Number of terms to generate per iteration.
        min_valid: Minimum number of valid terms to consider the generator correct.

    Returns:
        The best (most valid) generator code found.
    """
    correction_start = time.time()
    
    # Track statistics
    stats = llm_client.stats
    if stats:
        stats.max_iterations = max_iter
    
    # Extract code from markdown if present (initial code might have markdown wrapper)
    generator_code = extract_code_from_response(generator_code)
    
    iteration = 0
    best_generator = generator_code
    max_valid = 0

    while max_valid < min_valid and iteration < max_iter:
        iteration += 1
        print(f"Iteration {iteration}: Testing generator...")
        
        if stats:
            stats.correction_iterations = iteration

        # --- phase 1: make sure the generator code can actually run ---
        exe_ok, exe_error = check_generator_executable(generator_code)
        if not exe_ok:
            # Truncate very long error messages for readability and prompt size
            MAX_ERR_LEN = 1000
            display_error = exe_error
            if len(display_error) > MAX_ERR_LEN:
                half = MAX_ERR_LEN // 2
                display_error = display_error[:half] + "\n... (omitted middle of long error message) ...\n" + display_error[-half:]

            print(f"Generator not executable: {display_error}")
            
            # Track error
            if stats:
                stats.execution_errors += 1
                if "SyntaxError" in display_error or "IndentationError" in display_error:
                    stats.syntax_errors += 1
            
            # Treat this as a single aggregated error for refinement
            errors = [display_error]
            valid_count = 0

            # Immediately invoke LLM to repair non-executable generator code
            repair_prompt = REPAIR_PROMPT_TEMPLATE.format(
                error=display_error,
                generator_code=generator_code
            )
            try:
                repaired = llm_client.chat([
                    {"role": "system", "content": "You are an expert in Python and SMT-LIB code repair."},
                    {"role": "user", "content": repair_prompt}
                ])
                # Extract code from markdown if present
                generator_code = extract_code_from_response(repaired)
                
                if stats:
                    stats.repair_llm_calls += 1
                    
            except Exception as e:
                print(f"LLM repair failed: {e}")
                break

            # Continue to next iteration to retest the repaired code
            continue
        else:
            # --- phase 2: exercise the generator and validate produced terms ---
            errors = []
            term_tuples = generate_terms(generator_code, sample_size)
            valid_count = 0

            for term_tuple in term_tuples:
                is_valid, error_msg = parse_term(term_tuple, solvers)
                if not is_valid:
                    errors.append(error_msg)
                    # Track error types
                    if stats and error_msg not in stats.unique_error_types:
                        stats.unique_error_types.append(error_msg)
                    if stats:
                        stats.solver_errors += 1
                else:
                    valid_count += 1

            # Track generation statistics
            if stats:
                stats.total_terms_generated += len(term_tuples)
                stats.total_terms_valid += valid_count
                stats.terms_per_iteration.append(len(term_tuples))
                stats.valid_per_iteration.append(valid_count)
                if len(term_tuples) > 0:
                    stats.passing_rate_per_iteration.append(valid_count / len(term_tuples))
                else:
                    stats.passing_rate_per_iteration.append(0.0)

            print(f"Valid terms: {valid_count}/{len(term_tuples)}")

            if valid_count > max_valid:
                max_valid = valid_count
                best_generator = generator_code

            # Print summary of errors
            if errors:
                print(f"Encountered {len(errors)} errors. Sample errors:")
                for sample_error in errors[:5]:
                    print(f"- {sample_error}")

        # Only refine if less than 90% of terms are valid (or 0 when not executable)
        if valid_count < sample_size * 0.9:
            # Always refine based on the best generator found so far
            prompt = construct_prompt(errors, best_generator)
            try:
                new_code = llm_client.chat([
                    {"role": "system", "content": "You are an expert in SMT-LIB and code correction."},
                    {"role": "user", "content": prompt}
                ])
                # Extract code from markdown blocks if present
                generator_code = extract_code_from_response(new_code)
                
                if stats:
                    stats.refinement_llm_calls += 1
                    
            except Exception as e:
                print(f"LLM refinement failed: {e}")
                break
        else:
            break

    if stats:
        stats.correction_time = time.time() - correction_start
        
    return best_generator


def check_generator_executable(generator_code: str) -> Tuple[bool, str]:
    """Quickly check that the generated Python module is syntactically and
    import-time executable.

    We execute the code in a fresh Python subprocess that simply imports the
    generated function and runs it once. Any exception (syntax/import/runtime)
    is captured and returned as a string to be fed back into the LLM.

    Returns:
        (ok, error_message)
    """
    temp_file = None
    try:
        # Detect the function name so we can call it once.
        function_name = extract_function_name(generator_code)

        with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
            temp_file = f.name
            full_code = f"""
import random
import string

{generator_code}

try:
    fn = {function_name}
    # Call once to make sure it runs; ignore its output.
    _ = fn()
except Exception as e:
    import sys, traceback
    traceback.print_exc(file=sys.stderr)
    sys.exit(1)
"""
            f.write(full_code)
            f.flush()

        result = subprocess.run(
            ["python", temp_file],
            capture_output=True,
            text=True,
            timeout=20,
        )

        if result.returncode == 0:
            return True, ""
        else:
            stderr = result.stderr.strip() or result.stdout.strip()
            return False, f"Execution error: {stderr}" if stderr else "Unknown execution error"

    except Exception as e:
        return False, f"Execution check exception: {e}"
    finally:
        if temp_file:
            try:
                os.unlink(temp_file)
            except Exception:
                pass


def generate_terms(generator_code: str, n: int) -> List[Tuple[str, str]]:
    """
    Execute generator code to produce sample SMT terms with declarations.
    
    Args:
        generator_code: Python code that defines a generator function
        n: Number of terms to generate
        
    Returns:
        List of tuples (declarations, formula) as strings
    """
    temp_file = None
    try:
        # Create a temporary file with the generator code
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            temp_file = f.name
            # Detect function name from the code
            function_name = extract_function_name(generator_code)
            
            # Add import statements and execution code
            full_code = f"""
import random
import string

{generator_code}

# Generate terms
import json
terms = []
for _ in range({n}):
    try:
        result = {function_name}()
        if isinstance(result, tuple) and len(result) == 2:
            # Store both declarations and formula
            terms.append({{"decls": str(result[0]), "formula": str(result[1])}})
        else:
            # Fallback: treat as formula-only with no declarations
            terms.append({{"decls": "", "formula": str(result)}})
    except Exception as e:
        # Skip failed generations
        continue

print(json.dumps(terms))
"""
            f.write(full_code)
            f.flush()
            
            # Execute the code and capture output
            result = subprocess.run(
                ['python', f.name], 
                capture_output=True, 
                text=True, 
                timeout=30
            )
            
            if result.returncode == 0:
                import json
                try:
                    terms_data = json.loads(result.stdout.strip())
                    return [(item['decls'], item['formula']) for item in terms_data[:n]]
                except json.JSONDecodeError as e:
                    print(f"Failed to parse generator output as JSON: {e}")
                    print(f"Output was: {result.stdout[:500]}")  # Show first 500 chars
                    return []
            else:
                print(f"Generator execution failed with return code {result.returncode}")
                if result.stderr:
                    print(f"Error: {result.stderr[:500]}")  # Show first 500 chars
                if result.stdout:
                    print(f"Output: {result.stdout[:500]}")  # Show first 500 chars
                return []
                
    except Exception as e:
        print(f"Error generating terms: {e}")
        return []
    finally:
        # Clean up temporary file
        if temp_file:
            try:
                os.unlink(temp_file)
            except:
                pass


def parse_term(term_tuple: Tuple[str, str], solvers: List[Any]) -> Tuple[bool, str]:
    """
    Validate an SMT term (with declarations) using multiple solvers.
    
    Args:
        term_tuple: Tuple of (declarations, formula) as SMT-LIB strings
        solvers: List of solver instances or command strings
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    decls, formula = term_tuple
    
    if not formula.strip():
        return False, "Empty formula"
    
    if not solvers:
        return False, "No solvers available"
    
    temp_file = None
    # Try each solver
    for solver in solvers:
        try:
            # Create a complete SMT-LIB script with declarations and formula
            smt_script = "(set-logic ALL)\n"
            if decls.strip():
                smt_script += decls.strip() + "\n"
            smt_script += f"(assert {formula})\n(check-sat)\n"
            
            # Write to temporary file and run solver
            with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
                temp_file = f.name
                f.write(smt_script)
                f.flush()
                
                # Run solver (assume it's a command-line tool)
                # If solver is cvc5, add --parse-only flag
                cmd = [str(solver), f.name]
                is_parse_only = False
                if "cvc5" in str(solver).lower():
                    cmd.insert(1, "--parse-only")
                    is_parse_only = True

                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=10
                )
                
                if result.returncode == 0:
                    # With --parse-only, empty output means success
                    if is_parse_only:
                        return True, ""
                    # Otherwise check if solver output indicates success
                    output = result.stdout.strip().lower()
                    if 'sat' in output or 'unsat' in output:
                        return True, ""
                    else:
                        return False, f"Solver output: {result.stdout.strip()}"
                else:
                    # Provide detailed error information including the formula
                    stderr = result.stderr.strip()
                    stdout = result.stdout.strip()
                    error_detail = stderr if stderr else stdout if stdout else "Unknown solver error"
                    # Truncate formula if too long
                    formula_preview = formula[:100] + "..." if len(formula) > 100 else formula
                    return False, f"Solver error (rc={result.returncode}): {error_detail} | Formula: {formula_preview}"
                    
        except subprocess.TimeoutExpired:
            formula_preview = formula[:100] + "..." if len(formula) > 100 else formula
            return False, f"Solver timeout | Formula: {formula_preview}"
        except Exception as e:
            return False, f"Solver exception: {str(e)}"
        finally:
            if temp_file:
                try:
                    os.unlink(temp_file)
                    temp_file = None
                except:
                    pass
    
    return False, "All solvers failed"


def construct_prompt(errors: List[str], generator_code: str) -> str:
    """
    Construct a prompt for LLM-based generator refinement.
    
    Args:
        errors: List of error messages from solver validation
        generator_code: Current generator code
        
    Returns:
        Formatted prompt string
    """
    if not errors:
        return REFINE_PROMPT_TEMPLATE.format(
            errors="No specific errors found",
            common_errors="No frequent errors",
            error_count=0,
            unique_error_count=0,
            generator_code=generator_code
        )
    
    # Summarize and deduplicate errors
    unique_errors = list(set(errors))
    error_summary = "\n".join(f"- {error}" for error in unique_errors[:20])
    
    # Count error frequencies
    error_counts = {}
    for error in errors:
        error_counts[error] = error_counts.get(error, 0) + 1
    
    # Get most common errors
    common_errors = sorted(error_counts.items(), key=lambda x: x[1], reverse=True)[:5]
    common_error_text = "\n".join(f"- {error} (occurred {count} times)" 
                                 for error, count in common_errors)
    
    # Format the prompt using the template
    prompt = REFINE_PROMPT_TEMPLATE.format(
        generator_code=generator_code,
        errors=error_summary,
        common_errors=common_error_text,
        error_count=len(errors),
        unique_error_count=len(unique_errors)
    )
    
    return prompt


def extract_function_name(generator_code: str) -> str:
    """
    Extract the main generator function name from the code.
    
    Args:
        generator_code: Python code containing the generator function
        
    Returns:
        Function name, defaults to 'generate' if not found
    """
    import re
    # 1) Prefer the canonical public API generate_*_formula_with_decls
    preferred = re.search(r'def\s+(generate_[a-zA-Z0-9_]+_formula_with_decls)\s*\(', generator_code)
    if preferred:
        return preferred.group(1)

    # 2) Otherwise, find zero-argument functions starting with generate*
    zero_arg_funcs = re.findall(r'def\s+(generate[\w_]*)\s*\(\s*\)\s*:', generator_code)
    if zero_arg_funcs:
        # Return the first zero-arg generate function
        return zero_arg_funcs[0]

    # 3) Fallback: any generate* function, but avoid ones with required params like (depth)
    any_generate = re.findall(r'def\s+(generate[\w_]*)\s*\(.*?\)\s*:', generator_code)
    for fn in any_generate:
        # Heuristic: skip helpers commonly named with suffixes like _term, _expr, etc. if they require params
        if fn.endswith(('_term', '_expr', '_node')):
            continue
        return fn

    # 4) Final fallback
    return 'generate'


def extract_code_from_response(response: str) -> str:
    """
    Extract Python code from LLM response that may contain markdown formatting.
    
    Args:
        response: Raw LLM response
        
    Returns:
        Extracted Python code
    """
    # Look for code blocks
    import re
    
    # Try to find code within triple backticks
    pattern = r'```(?:python)?\s*(.*?)\s*```'
    match = re.search(pattern, response, re.DOTALL)
    if match:
        return match.group(1).strip()
    
    # If no code blocks found, return the response as-is
    return response.strip()


def parse_arguments():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="SMT Formula Generator Construction Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Using default LIA example
  python construct.py
  
  # Using custom theory documentation
  python construct.py --doc-file theory.txt --theory-name "Arrays" --theory-abbrev "arrays"
  
  # Specify LLM backend
  export LLM_BACKEND=anthropic
  export ANTHROPIC_API_KEY=your-key
  python construct.py --doc-file theory.txt --theory-name "Strings" --theory-abbrev "strings"
  
  # Override default model
  export LLM_MODEL=gpt-4-turbo
  python construct.py --doc-file bitvectors.txt --theory-name "BitVectors" --theory-abbrev "bv"
  
  # Specify solvers for correction
  python construct.py --doc-file theory.txt --theory-name "Ints" --theory-abbrev "ints" \\
                      --solvers /usr/local/bin/z3 /usr/local/bin/cvc5
  
  # Control correction parameters
  python construct.py --doc-file theory.txt --theory-name "Reals" --theory-abbrev "reals" \\
                      --max-iter 15 --sample-size 30 --min-valid 27
        """
    )
    
    parser.add_argument(
        "--doc-file",
        type=str,
        help="Path to text file containing theory documentation (if not provided, uses built-in LIA example)"
    )
    
    parser.add_argument(
        "--theory-name",
        type=str,
        help="Name of the SMT theory (e.g., 'Ints', 'Arrays', 'BitVectors')"
    )
    
    parser.add_argument(
        "--theory-abbrev",
        type=str,
        help="Abbreviated name for the theory used in function names (e.g., 'ints', 'arrays', 'bv')"
    )
    
    parser.add_argument(
        "--solvers",
        nargs="+",
        type=str,
        default=None,
        help="Paths to SMT solver executables for validation (e.g., /usr/local/bin/z3 /usr/local/bin/cvc5)"
    )
    
    parser.add_argument(
        "--max-iter",
        type=int,
        default=10,
        help="Maximum number of refinement iterations (default: 10)"
    )
    
    parser.add_argument(
        "--sample-size",
        type=int,
        default=20,
        help="Number of terms to generate per iteration (default: 20)"
    )
    
    parser.add_argument(
        "--min-valid",
        type=int,
        default=18,
        help="Minimum number of valid terms to consider generator correct (default: 18)"
    )
    
    parser.add_argument(
        "--skip-correction",
        action="store_true",
        help="Skip the self-correction phase (useful for quick testing)"
    )
    
    parser.add_argument(
        "--output",
        type=str,
        help="Output file path to save the generated generator code (optional)"
    )
    
    parser.add_argument(
        "--stats-output",
        type=str,
        help="Output file path to save statistics as JSON (optional)"
    )
    
    parser.add_argument(
        "--backend",
        type=str,
        choices=["openai", "anthropic", "deepseek", "gemini", "qwen"],
        help="LLM backend to use (can also be set via LLM_BACKEND env var)"
    )
    
    parser.add_argument(
        "--model",
        type=str,
        help="LLM model name (can also be set via LLM_MODEL env var)"
    )
    
    parser.add_argument(
        "--temperature",
        type=float,
        default=1,
        help="LLM sampling temperature (default: 1)"
    )
    
    parser.add_argument(
        "--max-tokens",
        type=int,
        default=2048,
        help="Maximum tokens for LLM generation (default: 2048)"
    )
    
    return parser.parse_args()


if __name__ == "__main__":
    # Parse command-line arguments
    args = parse_arguments()
    
    # Initialize statistics
    stats = GenerationStatistics()
    
    # Example usage of the SMT generator construction pipeline
    print("SMT Generator Construction - Example Usage")
    print("=" * 50)
    
    # Initialize LLM client
    # Command-line args override environment variables
    backend = args.backend or os.getenv("LLM_BACKEND", "openai")
    model = args.model or os.getenv("LLM_MODEL")  # Optional: override default model
    
    try:
        llm_client = make_llm_client(
            backend=backend,
            model=model,
            temperature=args.temperature,
            max_tokens=args.max_tokens
        )
        # Set statistics tracking
        llm_client.set_statistics(stats)
        stats.backend = backend
        stats.model = llm_client.name
        
        print(f"Using {backend} backend with model: {llm_client.name}")
        print(f"Temperature: {args.temperature}, Max tokens: {args.max_tokens}")
    except ValueError as e:
        print(f"Error: {e}")
        print(f"\nPlease set the appropriate API key environment variable:")
        print("  - OpenAI: OPENAI_API_KEY")
        print("  - Anthropic: ANTHROPIC_API_KEY")
        print("  - DeepSeek: DEEPSEEK_API_KEY")
        print("  - Gemini: GOOGLE_API_KEY or GEMINI_API_KEY")
        print("  - Qwen: DASHSCOPE_API_KEY")
        exit(1)
    
    # Load theory configuration
    if args.doc_file:
        # Load from file
        if not os.path.exists(args.doc_file):
            print(f"Error: Documentation file not found: {args.doc_file}")
            exit(1)
        
        if not args.theory_name or not args.theory_abbrev:
            print("Error: --theory-name and --theory-abbrev are required when using --doc-file")
            exit(1)
        
        try:
            with open(args.doc_file, 'r', encoding='utf-8') as f:
                documentation = f.read()
            theory_name = args.theory_name
            theory_abbrev = args.theory_abbrev
            print(f"\nLoaded theory documentation from: {args.doc_file}")
            print(f"Theory: {theory_name} (abbrev: {theory_abbrev})")
            print(f"Documentation length: {len(documentation)} characters")
        except Exception as e:
            print(f"Error reading documentation file: {e}")
            exit(1)
    else:
        # Use built-in example: Linear Integer Arithmetic (LIA) theory
        print("\nUsing built-in Linear Integer Arithmetic (LIA) example")
        print("(Use --doc-file to provide custom theory documentation)")
        theory_name = "Ints"
        theory_abbrev = "ints"
        
        documentation = """
    Linear Integer Arithmetic (LIA) theory supports:
    - Integer constants and variables
    - Linear arithmetic operators: +, -, *, div, mod
    - Comparison operators: =, <, <=, >, >=, distinct
    - Boolean connectives: and, or, not, =>, iff
    - Quantifiers: forall, exists (over integer variables)
    
    Syntax:
    - Integer literals: 0, 1, -5, 42
    - Variables: declared with (declare-fun x () Int)
    - Arithmetic: (+ x y), (- x 5), (* 3 x)
    - Comparisons: (< x y), (= x 0)
    - Boolean: (and (> x 0) (< x 10))
    """
    
    # Track theory info in statistics
    stats.theory_name = theory_name
    stats.theory_abbrev = theory_abbrev
    
    print()
    
    try:
        # Step 1: Generate CFG from documentation
        print("=" * 50)
        print("Step 1: Generating CFG from theory documentation...")
        print("=" * 50)
        cfg = summarize_cfg(documentation, theory_name, llm_client)
        print("Generated CFG:")
        print(cfg[:300] + "..." if len(cfg) > 300 else cfg)
        print()
        
        # Step 2: Generate initial SMT generator code
        print("=" * 50)
        print("Step 2: Generating SMT generator code...")
        print("=" * 50)
        generator_code = generate_smt_generator(cfg, theory_name, theory_abbrev, llm_client)
        # Extract code from markdown blocks if present
        generator_code = extract_code_from_response(generator_code)
        print("Generated generator function:")
        print(generator_code[:400] + "..." if len(generator_code) > 400 else generator_code)
        print()
        
        # Step 3: Test the generator
        print("=" * 50)
        print("Step 3: Testing generator...")
        print("=" * 50)
        sample_terms = generate_terms(generator_code, 5)
        print(f"Generated {len(sample_terms)} sample terms:")
        for i, (decls, formula) in enumerate(sample_terms, 1):
            print(f"  {i}. Declarations:")
            if decls.strip():
                for line in decls.strip().split('\n')[:3]:  # Show first 3 lines
                    print(f"     {line}")
                if len(decls.strip().split('\n')) > 3:
                    print(f"    ...")
            else:
                print(f"     (none)")
            print(f"     Formula: {formula[:100]}{'...' if len(formula) > 100 else ''}")
        print()
        
        # Step 4: Self-correction (if not skipped)
        if not args.skip_correction:
            print("=" * 50)
            print("Step 4: Self-correction process...")
            print("=" * 50)
            
            # Use provided solvers or mock solvers for demonstration
            solvers = args.solvers if args.solvers else ["z3", "cvc5"]
            
            if args.solvers:
                print(f"Using provided solvers: {', '.join(args.solvers)}")
                # Verify solvers exist
                missing_solvers = []
                for solver in args.solvers:
                    if not os.path.exists(solver) and not os.path.isfile(f"/usr/bin/{solver}") and not os.path.isfile(f"/usr/local/bin/{solver}"):
                        missing_solvers.append(solver)
                
                if missing_solvers:
                    print(f"Warning: Some solvers may not be found: {', '.join(missing_solvers)}")
                    print("The correction process may fail if solvers are not accessible")
            else:
                print("Note: Using default solver names (z3, cvc5)")
                print("Provide actual solver paths with --solvers for real validation")
            
            print(f"Max iterations: {args.max_iter}")
            print(f"Sample size: {args.sample_size}")
            print(f"Minimum valid terms: {args.min_valid}")
            print()
            
            try:
                corrected_generator = correct_generator(
                    generator_code=generator_code,
                    llm_client=llm_client,
                    solvers=solvers,
                    max_iter=args.max_iter,
                    sample_size=args.sample_size,
                    min_valid=args.min_valid
                )
                print("\nGenerator correction completed!")
                generator_code = corrected_generator  # Use corrected version
                
            except Exception as e:
                print(f"\nCorrection process encountered an error: {e}")
                if not args.solvers:
                    print("This is expected when using default solver names without actual executables")
                    print("Use --solvers to provide actual solver paths, or --skip-correction to skip this step")
                print("Continuing with uncorrected generator...")
        else:
            print("=" * 50)
            print("Step 4: Skipped (--skip-correction flag set)")
            print("=" * 50)
        
        # Save output if requested
        if args.output:
            try:
                if "```" in generator_code:
                    generator_code = extract_code_from_response(generator_code)
                with open(args.output, 'w', encoding='utf-8') as f:
                    f.write(generator_code)
                print(f"\n{'=' * 50}")
                print(f"Generator code saved to: {args.output}")
                print(f"{'=' * 50}")
            except Exception as e:
                print(f"\nError saving output file: {e}")
        
        print("\n" + "=" * 50)
        print("Example completed successfully!")
        print("=" * 50)
        
        # Finalize and print statistics
        stats.finalize()
        stats.print_summary()
        
        # Save statistics to JSON if requested
        if args.stats_output:
            try:
                stats.to_json(args.stats_output)
                print(f"\nStatistics saved to: {args.stats_output}")
            except Exception as e:
                print(f"\nError saving statistics file: {e}")
        
    except Exception as e:
        print(f"\nError during execution: {e}")
        import traceback
        traceback.print_exc()
        print("\nMake sure you have:")
        print("  1. A valid API key set for your chosen backend")
        print("  2. Internet connection for API calls")
        print("  3. Valid theory documentation (if using --doc-file)")
        exit(1)
    
#     # Additional example: Testing utility functions
#     print("\n" + "="*50)
#     print("Testing utility functions...")
    
#     # Test function name extraction
#     sample_code = '''
# def generate_example_formula_with_decls():
#     return "declarations", "formula"
# '''
#     func_name = extract_function_name(sample_code)
#     print(f"Extracted function name: {func_name}")
    
#     # Test code extraction from markdown
#     markdown_response = '''
# Here's the corrected code:

# ```python
# def generate_fixed_formula():
#     return "fixed", "formula"
# ```

# This should work better.
# '''
#     extracted_code = extract_code_from_response(markdown_response)
#     print(f"Extracted code from markdown:\n{extracted_code}")