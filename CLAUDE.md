# CLAUDE.md — DSC 190: Learning Theory

## Project Overview
Learning theory homework repository for DSC 190. Work is organized by assignment in numbered folders (`hw1/`, `hw2/`, etc.).

## Repository Structure
dsc190_learning_theory/
├── hw1/
│   ├── *.py                  # Implementation + experiment logic
│   ├── *.ipynb               # Notebook: same experiments + discussion
│   ├── plots/                # Auto-generated PNGs
│   ├── theory_solution.tex   # Written theory
│   └── *.pdf                 # Problem statement
├── hw2/
│   └── ...
└── style/                    # Shared style assets

## Code Conventions

### Python files
- All reusable logic lives in `.py` files as importable functions with docstrings
- Notebooks import from `.py` files — do not duplicate logic
- `if __name__ == '__main__':` guard in every script so it is safely importable
- Use `matplotlib.use('Agg')` at the top of `.py` scripts; notebooks handle their own display
- Plots saved to `hw<N>/plots/` via `PLOTS_DIR` defined at module level using `__file__`

### Notebooks
- Edit `.ipynb` as valid JSON
- Do not use IPython magics (e.g. `%matplotlib inline`) — they break `ast.parse` validation
- Each experiment gets its own labelled markdown cell above and findings cell below

## Running Experiments
```bash
cd hw<N>
python <script>.py             # runs all experiments, saves plots to hw<N>/plots/
jupyter notebook <notebook>.ipynb   # interactive version
```

## Preferences
- Modular functions with docstrings; no monolithic scripts
- Plots: two-panel figures where one panel tests linearity and the other compares to the bound
- Use log scale on y-axis when bound and actual values differ by orders of magnitude
- Clip `fill_between` lower band at 0 (counts are non-negative)
- Single quotes for Python string literals in code cells
- All plots saved as `.png` to `hw<N>/plots/`; filenames match the experiment

## Sanity Checks
Each homework should include a `run_sanity_checks()` function that validates:
- Data generation correctness
- Implementation correctness (manual one-step traces)
- Convergence on separable data
- Theoretical bound verification across multiple random trials