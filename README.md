# Reliable Proof Generation with LLMs via Analogical Retrieval and Symbolic Verification: <br> A Case Study in Euclidean Geometry

> ## 🎉 **Accepted to the Findings of EMNLP 2026 (Budapest, Hungary)!** 🎉

This repository contains the code, prompts, and experimental results for the paper: https://arxiv.org/abs/2505.14479 </br>
**Authors: Oren Sultan, Eitan Stern, Dafna Shahaf — The Hebrew University of Jerusalem, Israel** </br>

LLMs struggle with formal domains that require rigorous logical deduction and symbolic reasoning, such as mathematical proof generation. We propose a **neuro-symbolic approach** built on the hypothesis that *structurally analogous problems often admit similar proofs*. As a proof of concept, we focus on SAT-level Euclidean geometry problems from the FormalGeo-7K dataset. Our pipeline is two-fold:

1. **Analogical retrieval** – we abstract problems, train a regressor to predict proof similarity, and retrieve analogous problems whose proofs (and the theorems they use) guide the LLM as few-shot examples with a narrowed theorem dictionary.
2. **Symbolic verification** – a formal verifier (FormalGeo + Z3 SMT) checks each generated proof and returns tiered feedback (syntax errors, violated theorem premises, goal not reached), letting the LLM fix incorrect proofs over several retries and runs.

The complete pipeline raises proof accuracy to **68%–96%**, compared with **10%–44%** for LLM-only baselines that use neither analogy retrieval nor verifier feedback, across four models from three model families (OpenAI, Google, Anthropic).


## 📊 Main Results

We evaluate **OpenAI o1**, **GPT-5**, **Gemini-2.5-Flash**, and **Claude Sonnet 4.6** on 50 FormalGeo-7K problems (10 per difficulty level, levels 1–5). Each model is run in two variants: the **base model** (5 random few-shot problems + the full theorem dictionary) and **ours** (5 retrieved analogous problems + an analogy-derived theorem dictionary). `base_{i,j}` / `ours_{i,j}` denote up to *i* independent runs and *j* verifier-guided retries per run.

**Proof accuracy (%) – Table 2 of the paper**

| Model | base<sub>1,1</sub> | ours<sub>1,1</sub> | Δ | base<sub>1,5</sub> | ours<sub>1,5</sub> | Δ | base<sub>3,5</sub> | ours<sub>3,5</sub> | Δ |
|---|---|---|---|---|---|---|---|---|---|
| o1 | 10% | 48% | +38 | 38% | 68% | +30 | 52% | 80% | +28 |
| GPT-5 | 44% | 64% | +20 | 80% | 96% | +16 | 88% | 96% | +8 |
| Gemini-2.5-Flash | 22% | 48% | +26 | 58% | 74% | +16 | 72% | 86% | +14 |
| Claude Sonnet 4.6 | 28% | 60% | +32 | 58% | 78% | +20 | 78% | 86% | +8 |

Our method consistently improves proof accuracy across all models and inference settings. With the same verifier feedback and inference budget (`base_{3,5}` vs. `ours_{3,5}`), analogical guidance alone improves accuracy from 88% to 96% for GPT-5, 78% to 86% for Claude Sonnet 4.6, 72% to 86% for Gemini-2.5-Flash, and 52% to 80% for o1.

**Controlled ablation of analogy retrieval and dictionary construction – Table 3 of the paper**

| Setting | Few-shot examples | Theorem dictionary | Gemini 1 run | Gemini 1 run + retries | Gemini 3 runs + retries | Claude 1 run | Claude 1 run + retries | Claude 3 runs + retries |
|---|---|---|---|---|---|---|---|---|
| **Ours** | Analogies | Analogy-derived | **48%** | **74%** | **86%** | **60%** | **78%** | **86%** |
| (i) | Analogies | Full | 30% | 68% | 78% | 42% | 62% | 78% |
| (ii) | Random | Random-derived | 24% | 54% | 72% | 28% | 60% | 72% |
| (iii) | Analogies | Random (size-matched) | 32% | 60% | 78% | 36% | 66% | 74% |
| Baseline | Random | Full | 22% | 58% | 72% | 28% | 58% | 78% |

Additional findings (see Section 5.3 and the appendix of the paper):
- **Fewer retries and runs**: on o1, our method needs 4.6 retries and 1.58 runs per problem on average vs. 8.92 retries and 2.12 runs for the base model.
- **Lower cost**: our analogy-derived dictionary (~2.5K tokens) replaces the full dictionary (~18K tokens), making the baseline roughly 3× more expensive. Evaluating 50 problems costs approximately $100 (o1), $3 (GPT-5), $1 (Gemini-2.5-Flash), and $10 (Claude Sonnet 4.6).
- **Stability**: adding 10 more problems per level (50 → 100) changes accuracy by only ~3% per level on average.
- **Error analysis**: Tier-1 syntax errors are the most frequent and are easily fixed with verifier feedback; Tier-2 errors (violated theorem premises) are rarer but reflect deeper reasoning failures.


## 🚀 Setup

The code is implemented in **Python 3.10**.

### Create and activate the conda environment

```bash
conda env create -f environment.yml
conda activate FormalGeo_env
```

### API keys

Set the API key for the provider you want to run (or pass `--api_key` on the command line where supported):

```bash
export OPENAI_API_KEY=<your-key>      # o1 and GPT-5 solvers
export GEMINI_API_KEY=<your-key>      # Gemini solver (OpenAI-compatible endpoint; see GEMINI_API_BASE in the script)
export ANTHROPIC_API_KEY=<your-key>   # Claude solver
```

### Running a solver

Run from the repository root with `src/` on the Python path (see `run_solver.sh` for a wrapper that also keeps a Mac awake):

```bash
export PYTHONPATH="$(pwd)"
python src/formalgeo/LLM_analogy_based_solver.py        --variant analogy_based --model_name o1
python src/formalgeo/LLM_gpt5_analogy_based_solver.py   --variant analogy_based --model_name gpt-5 --reasoning_effort medium
python src/formalgeo/LLM_gemini_analogy_based_solver.py --variant analogy_based --model_name gemini-2.5-flash
python src/formalgeo/LLM_claude_analogy_based_solver.py --variant analogy_based --model_name claude-sonnet-4-6
```

`--variant` selects the prompting configuration:

| Variant | Few-shot examples | Theorem dictionary | Used for |
|---|---|---|---|
| `analogy_based` | retrieved analogies | analogy-derived | **Ours** (Table 2) |
| `random_all_theorems` | random | full | **Baseline** (Table 2) |
| `analogy_based_all_theorems` | retrieved analogies | full | ablation (i), Table 3 |
| `random_narrowed` | random | random-derived | ablation (ii), Table 3 (Gemini/Claude solvers) |
| `analogy_random_dict` | retrieved analogies | random, size-matched | ablation (iii), Table 3 (Gemini/Claude solvers) |

The problems to solve are set in `chosen_problems_by_level` inside each solver; the Gemini and Claude solvers also accept `--problems '{"1": [1168, 1490], "2": [...]}'` to override it from the command line. Output proofs and logs are written to `results/level_<k>/` (o1) or `results/level_<k>/<gpt5|gemini|claude>/`.


## 📁 Important Folders and Files

### `src/formalgeo/`

- `create_problems_proofs_similarity_dataset.py`
  Creation of the abstracted problem dataset used to train the similarity regressor (Section 3.1).
- `similar_proofs_model.py`
  Training of the proof-similarity regressor (Section 3.2). Run with `--run-model-pred 1` to run the trained model (`similar_proofs_model.pth`).
- `similar_proofs_retrieval.py`
  Retrieval of analogous problems for our method, or random problems for the baseline (Section 3.2). Used by the LLM solvers.
- `LLM_analogy_based_solver.py`, `LLM_gpt5_analogy_based_solver.py`, `LLM_gemini_analogy_based_solver.py`, `LLM_claude_analogy_based_solver.py`
  The LLM solver with verifier-guided feedback loop for o1, GPT-5, Gemini-2.5-Flash, and Claude Sonnet 4.6, respectively (Sections 3.3–3.4). Model settings follow the paper: o1 with default settings, GPT-5 with medium reasoning, Gemini-2.5-Flash with t=0.7, Claude Sonnet 4.6 with t=1.0.
- `geometric_verifier.py`
  Our SMT-based verifier built on the Z3 theorem prover, including symbolic workarounds for trigonometric functions (Section 3.4, Appendix C).
- `verifier/verifier.py`
  The verifier for Tier-1 (syntax) errors, based on the FormalGeo codebase (Section 3.4).
- `prompt/geometry_similar_problems_prompt.txt`
  The system prompt given to the LLM solver (Figure 5; few-shot examples as in Figure 6).
- `experiments/plot_results.py`
  Generates the per-level accuracy plots for each model (Figures 8–11).

### `formalgeo7k_v1/`

The FormalGeo-7K dataset:

- `formalgeo7k_v1/gdl/theorem_GDL.json`
  The **Geometry Definition Language (GDL)** theorem dictionary used across the dataset.
- `formalgeo7k_v1/problems/`
  Individual problem JSON files.

### `results/`

- **Evaluation data**
  `level_1` … `level_5`, one folder per difficulty level. Each holds the generated proofs and logs for every evaluated problem, variant, and run: o1 files directly in the level folder, and `gpt5/`, `gemini/`, `claude/` subfolders for the other models (the Gemini and Claude folders also contain the Table 3 ablation runs and the 100-problem stability runs).
- **Figures from the paper**
  - `retries_and_runs.png` – *Figure 3*: average retries and runs per problem by difficulty level
  - `tier_error_distribution.png` – *Figure 4*: verifier error distribution by tier
  - `correct_proofs_ablation_gpt_o1.png` – *Figure 8*: % correct proofs per level, o1
  - `correct_proofs_ablation_claude.png` – *Figure 9*: % correct proofs per level, Claude Sonnet 4.6
  - `correct_proofs_ablation_gemini.png` – *Figure 10*: % correct proofs per level, Gemini-2.5-Flash
  - `correct_proofs_ablation_gpt5.png` – *Figure 11*: % correct proofs per level, GPT-5
  - `analogy_stability.png` – *Figure 12*: stability when increasing the sample from 50 to 100 problems

### `docs/paper_submission/`

LaTeX source of the paper.


## ⚠️ Important Notes

You should **manually overwrite** the following files in your conda environment:

- Replace `~/miniforge3/envs/FormalGeo_env/lib/python3.10/site-packages/formalgeo/solver/interactive.py`
  with `src/formalgeo/solver/interactive.py`
- Replace `~/miniforge3/envs/FormalGeo_env/lib/python3.10/site-packages/formalgeo/tools/output.py`
  with `src/formalgeo/tools/output.py`

This ensures that the solver and output behavior match the modified logic described in the paper and used in our experiments.


## Cite

```bibtex
@inproceedings{sultan2026reliable,
  title     = {Reliable Proof Generation with LLMs via Analogical Retrieval and Symbolic Verification: A Case Study in Euclidean Geometry},
  author    = {Sultan, Oren and Stern, Eitan and Shahaf, Dafna},
  booktitle = {Findings of the Association for Computational Linguistics: EMNLP 2026},
  year      = {2026},
  address   = {Budapest, Hungary},
  url       = {https://arxiv.org/abs/2505.14479}
}
```


## Contact
For inquiries, please send an email to oren.sultan@mail.huji.ac.il.
