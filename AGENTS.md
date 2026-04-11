# AGENTS.md

## Repository Purpose
- This repository stores DSC 190/291 Learning Theory assignments.
- Keep each assignment in its own folder such as `hw1/`.
- Treat the repo as a reproducible homework submission record: code, plots, writeups, and reports should live together.

## File Organization
- Put Python source, notebooks, generated plots, and writeups inside the relevant homework folder.
- Keep shared LaTeX resources under `style/`.
- Do not commit generated Python cache files such as `__pycache__/`.

## LaTeX Conventions
- When creating or editing LaTeX files for theory writeups, use the style file at `style/latex/dhruv_theory_style.sty`.
- Match its theorem environments, spacing, math shortcuts, and section styling instead of introducing a separate style system.

## Experiment And Writing Expectations
- Explanations must match the actual plots and printed experiment outputs.
- Avoid overstating conclusions: if a trend is approximate or noisy, say so explicitly.
- If a bound dominates the scale of a figure, prefer plotting choices that keep the empirical curve readable.
- When discussing empirical scaling, distinguish between qualitative agreement with theory and exact confirmation.

## Part C Preferences
- Use Python for Perceptron implementations and experiments.
- Include both the implementation file and the notebook used to run or explain experiments.
- Save plots inside the assignment folder, for example `hw1/plots/`.
- Add sanity checks or small tests that verify the update rule, data generator, and theoretical bound behavior.

## Git Hygiene
- Before committing, check `git status` and keep commits focused on the current assignment task.
- Prefer committing source files, notebooks, plots, and writeups, while ignoring transient artifacts.
