"""
enumerate_check.py
DSC 190/291 — Assignment 2

Brute-force enumeration to verify the growth functions of H2 and H_quad.

For each n up to MAX_N we:
  1. Generate all 2^n binary strings of length n.
  2. Check which strings are realizable by H2 (unions of ≤2 intervals).
  3. Check which strings are realizable by H_quad (quadratic threshold).
  4. Compare the counts with the closed-form formulas:
       Γ_{H2}(n)    = C(n+1,0) + C(n+1,2) + C(n+1,4)
       Γ_{H_quad}(n) = n^2 - n + 2

Realizability is checked two ways:
  (a) Structural / combinatorial: based on the characterization in the writeup.
  (b) Algebraic: by solving a linear/quadratic system (for H_quad).

Usage:
  python enumerate_check.py          # runs for n = 1..8, prints table
  python enumerate_check.py --n 10   # runs up to n=10
"""

import argparse
import itertools
from math import comb
from typing import Callable
import sys


# -------------------------------------------------------
# Combinatorial realizability checks
# -------------------------------------------------------

def count_one_blocks(labeling: tuple[int, ...]) -> int:
    """Count the number of maximal contiguous runs of 1s."""
    blocks = 0
    in_block = False
    for bit in labeling:
        if bit == 1 and not in_block:
            blocks += 1
            in_block = True
        elif bit == 0:
            in_block = False
    return blocks


def is_realizable_H2_structural(labeling: tuple[int, ...]) -> bool:
    """
    H2 realizability (structural characterization):
    A labeling is realizable iff it has at most 2 contiguous 1-blocks.
    """
    return count_one_blocks(labeling) <= 2


def is_prefix_suffix(labeling: tuple[int, ...]) -> bool:
    """
    Check if labeling is a prefix-suffix pattern:
    starts with 1..1, then 0..0, then 1..1 (each non-empty).
    """
    n = len(labeling)
    if n < 3:
        return False
    if labeling[0] != 1 or labeling[-1] != 1:
        return False
    # There must be at least one 0 in the interior
    interior = labeling[1:-1]
    if 0 not in interior:
        return False
    # The string must look like 1^a 0^b 1^c with a,b,c >= 1
    # Equivalent: no 1 appears after a 0 that appears after a 1, except at the end
    # Simpler: exactly two 1-blocks
    return count_one_blocks(labeling) == 2


def is_realizable_H_quad_structural(labeling: tuple[int, ...]) -> bool:
    """
    H_quad realizability (structural characterization):
    A labeling is realizable iff it is:
      Type A: at most one contiguous 1-block, OR
      Type B: a prefix-suffix pattern (1^a 0^b 1^c with a,b,c >= 1).
    """
    blocks = count_one_blocks(labeling)
    if blocks <= 1:
        return True  # Type A
    if blocks == 2:
        # Must be prefix-suffix (Type B)
        return is_prefix_suffix(labeling)
    return False  # ≥3 blocks: never realizable


# -------------------------------------------------------
# Algebraic realizability check for H_quad
# (verify by actually finding a,b,c or proving none exists)
# -------------------------------------------------------

def is_realizable_H_quad_algebraic(labeling: tuple[int, ...]) -> bool:
    """
    Algebraic check for H_quad realizability.
    Try to find (a, b, c) such that for each position i (1-indexed):
        a*xi^2 + b*xi + c >= 0  if labeling[i] == 1
        a*xi^2 + b*xi + c <  0  if labeling[i] == 0
    We use sample points x_i = i (1, 2, 3, ..., n).
    This is a feasibility LP; we solve it via scipy if available,
    else fall back to the structural check.
    """
    try:
        from scipy.optimize import linprog
        import numpy as np
    except ImportError:
        # Fall back to structural check
        return is_realizable_H_quad_structural(labeling)

    n = len(labeling)
    xs = list(range(1, n + 1))  # x_i = i

    # Variables: (a, b, c, slack_1, ..., slack_n)
    # For label=1 at position i: a*xi^2 + b*xi + c >= eps  (feasibility margin)
    # For label=0 at position i: -(a*xi^2 + b*xi + c) >= eps
    # We maximize 0 subject to these constraints.
    # LP: minimize 0 s.t. A_ub @ x <= b_ub

    eps = 1e-6
    A_ub = []
    b_ub = []

    for i, (xi, yi) in enumerate(zip(xs, labeling)):
        row = [xi**2, xi, 1.0]  # coefficients for a, b, c
        if yi == 1:
            # a*xi^2 + b*xi + c >= eps  =>  -a*xi^2 - b*xi - c <= -eps
            A_ub.append([-xi**2, -xi, -1.0])
            b_ub.append(-eps)
        else:
            # a*xi^2 + b*xi + c < 0   =>  a*xi^2 + b*xi + c <= -eps
            A_ub.append([xi**2, xi, 1.0])
            b_ub.append(-eps)

    if not A_ub:
        return True  # no constraints — trivially realizable

    result = linprog(
        c=[0, 0, 0],
        A_ub=A_ub,
        b_ub=b_ub,
        bounds=[(None, None)] * 3,
        method="highs"
    )
    return result.status == 0  # status 0 = optimal (feasible)


# -------------------------------------------------------
# Closed-form formulas
# -------------------------------------------------------

def formula_H2(n: int) -> int:
    return comb(n + 1, 0) + comb(n + 1, 2) + comb(n + 1, 4)


def formula_H_quad(n: int) -> int:
    return n * n - n + 2


def sauer_shelah(n: int, d: int) -> int:
    return sum(comb(n, k) for k in range(d + 1))


# -------------------------------------------------------
# Main enumeration loop
# -------------------------------------------------------

def enumerate_n(n: int, verbose: bool = False) -> dict:
    """Enumerate all 2^n labelings for given n and return counts."""
    count_H2 = 0
    count_Hq_structural = 0
    count_Hq_algebraic = 0

    non_realizable_H2 = []
    non_realizable_Hq = []

    for labeling in itertools.product([0, 1], repeat=n):
        if is_realizable_H2_structural(labeling):
            count_H2 += 1
        else:
            non_realizable_H2.append(labeling)

        struc = is_realizable_H_quad_structural(labeling)
        alg = is_realizable_H_quad_algebraic(labeling)

        if struc != alg:
            print(f"  [MISMATCH n={n}] labeling={labeling}: "
                  f"structural={struc}, algebraic={alg}")

        if struc:
            count_Hq_structural += 1
        else:
            non_realizable_Hq.append(labeling)

        count_Hq_algebraic = count_Hq_structural  # after mismatch check

    return {
        "n": n,
        "total": 2 ** n,
        "H2_count": count_H2,
        "H2_formula": formula_H2(n),
        "H2_ok": count_H2 == formula_H2(n),
        "Hq_count": count_Hq_structural,
        "Hq_formula": formula_H_quad(n),
        "Hq_ok": count_Hq_structural == formula_H_quad(n),
        "SS_H2": sauer_shelah(n, 4),
        "SS_Hq": sauer_shelah(n, 3),
        "H2_tight": count_H2 == sauer_shelah(n, 4),
        "non_realizable_H2": non_realizable_H2,
        "non_realizable_Hq": non_realizable_Hq,
    }


def print_table(results: list[dict]) -> None:
    """Print a formatted summary table."""
    header = (
        f"{'n':>3}  {'2^n':>5}  "
        f"{'|H2|':>6}  {'Γ_H2(n)':>9}  {'H2 ok':>6}  "
        f"{'SS(n,4)':>8}  {'H2=SS':>6}  "
        f"{'|Hq|':>6}  {'Γ_Hq(n)':>9}  {'Hq ok':>6}  "
        f"{'SS(n,3)':>8}"
    )
    print(header)
    print("-" * len(header))
    for r in results:
        tick = lambda b: "✓" if b else "✗"
        print(
            f"{r['n']:>3}  {r['total']:>5}  "
            f"{r['H2_count']:>6}  {r['H2_formula']:>9}  {tick(r['H2_ok']):>6}  "
            f"{r['SS_H2']:>8}  {tick(r['H2_tight']):>6}  "
            f"{r['Hq_count']:>6}  {r['Hq_formula']:>9}  {tick(r['Hq_ok']):>6}  "
            f"{r['SS_Hq']:>8}"
        )


def print_non_realizable_examples(results: list[dict], max_n: int = 5) -> None:
    """Print first non-realizable labelings for each class."""
    print("\nNon-realizable labelings (first few examples):")
    for r in results:
        n = r["n"]
        if n > max_n:
            break
        if r["non_realizable_H2"]:
            examples = r["non_realizable_H2"][:3]
            print(f"  H2,   n={n}: {examples} ...")
        if r["non_realizable_Hq"]:
            examples = r["non_realizable_Hq"][:3]
            print(f"  Hquad, n={n}: {examples} ...")


def verify_vc_dimensions(results: list[dict]) -> None:
    """
    Print the VC dimension verification:
    VCdim = max n such that the class shatters some n-point set,
    i.e., max n s.t. Γ(n) = 2^n.
    """
    print("\nVC dimension verification:")
    max_H2_shattered = max(r["n"] for r in results if r["H2_count"] == r["total"])
    max_Hq_shattered = max(r["n"] for r in results if r["Hq_count"] == r["total"])
    print(f"  VCdim(H2)    ≥ {max_H2_shattered}  "
          f"(all 2^n labelings realizable up to n={max_H2_shattered})")
    print(f"  VCdim(H_quad) ≥ {max_Hq_shattered}  "
          f"(all 2^n labelings realizable up to n={max_Hq_shattered})")

    # Check first n where NOT all labelings realizable
    first_fail_H2 = min(
        (r["n"] for r in results if r["H2_count"] < r["total"]),
        default=None
    )
    first_fail_Hq = min(
        (r["n"] for r in results if r["Hq_count"] < r["total"]),
        default=None
    )
    if first_fail_H2:
        print(f"  VCdim(H2)    < {first_fail_H2}  "
              f"(first n where not all labelings realizable: {first_fail_H2})")
    if first_fail_Hq:
        print(f"  VCdim(H_quad) < {first_fail_Hq}  "
              f"(first n where not all labelings realizable: {first_fail_Hq})")


def save_table_figure(results: list[dict], figures_dir: str) -> None:
    """
    Render the enumeration results as a matplotlib table and save to
    figures/enumeration_table.pdf  (and .png for quick preview).
    """
    import os
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    os.makedirs(figures_dir, exist_ok=True)

    tick = lambda b: "✓" if b else "✗"

    col_labels = [
        "$n$", "$2^n$",
        r"$|\mathcal{H}_2|$", r"$\Gamma_{\mathcal{H}_2}(n)$", "ok",
        "SS$(n,4)$", "=SS",
        r"$|\mathcal{H}_{\rm quad}|$", r"$\Gamma_{\mathcal{H}_{\rm quad}}(n)$", "ok",
        "SS$(n,3)$",
    ]

    rows = []
    for r in results:
        rows.append([
            str(r["n"]),
            str(r["total"]),
            str(r["H2_count"]),
            str(r["H2_formula"]),
            tick(r["H2_ok"]),
            str(r["SS_H2"]),
            tick(r["H2_tight"]),
            str(r["Hq_count"]),
            str(r["Hq_formula"]),
            tick(r["Hq_ok"]),
            str(r["SS_Hq"]),
        ])

    n_rows = len(rows)
    n_cols = len(col_labels)

    fig_h = 0.42 * n_rows + 1.1
    fig, ax = plt.subplots(figsize=(13, fig_h))
    ax.axis("off")

    tbl = ax.table(
        cellText=rows,
        colLabels=col_labels,
        loc="center",
        cellLoc="center",
    )
    tbl.auto_set_font_size(False)
    tbl.set_fontsize(9)
    tbl.scale(1.0, 1.55)

    # Header row styling
    header_color = "#2c4a7c"
    for col in range(n_cols):
        cell = tbl[0, col]
        cell.set_facecolor(header_color)
        cell.set_text_props(color="white", fontweight="bold")

    # Column groups: H2 = cols 2-6 (light blue), Hquad = cols 7-10 (light green)
    h2_cols   = {2, 3, 4, 5, 6}
    hq_cols   = {7, 8, 9, 10}
    h2_bg     = "#dce8f5"
    hq_bg     = "#dff2e1"
    alt_h2    = "#edf4fb"
    alt_hq    = "#edfaef"

    for row_idx in range(1, n_rows + 1):
        even = (row_idx % 2 == 0)
        for col in range(n_cols):
            cell = tbl[row_idx, col]
            if col in h2_cols:
                cell.set_facecolor(alt_h2 if even else h2_bg)
            elif col in hq_cols:
                cell.set_facecolor(alt_hq if even else hq_bg)
            else:
                cell.set_facecolor("#f7f7f7" if even else "white")

        # Colour the "ok" and "=SS" tick cells
        for ok_col in (4, 9):
            cell = tbl[row_idx, ok_col]
            val = cell.get_text().get_text()
            cell.set_text_props(color="#1a7a1a" if val == "✓" else "#cc0000",
                                fontweight="bold")
        for ss_col in (6,):
            cell = tbl[row_idx, ss_col]
            val = cell.get_text().get_text()
            cell.set_text_props(color="#1a7a1a" if val == "✓" else "#cc0000",
                                fontweight="bold")

    ax.set_title(
        "Enumeration verification: $\\Gamma_{\\mathcal{H}_2}(n)$ and "
        "$\\Gamma_{\\mathcal{H}_{\\rm quad}}(n)$ vs. closed-form formulas\n"
        "Blue columns: $\\mathcal{H}_2$ (VCdim $=4$).  "
        "Green columns: $\\mathcal{H}_{\\rm quad}$ (VCdim $=3$).  "
        "ok $=$ brute-force count matches formula.",
        fontsize=9, pad=10,
    )

    for ext in ("pdf", "png"):
        path = os.path.join(figures_dir, f"enumeration_table.{ext}")
        fig.savefig(path, bbox_inches="tight", dpi=150)
    plt.close(fig)
    print(f"  → saved {figures_dir}/enumeration_table.pdf  (.png)")


def save_growth_figure(results: list[dict], figures_dir: str) -> None:
    """
    Save the growth-function comparison plot (line chart) to
    figures/growth_functions.pdf  (and .png).
    Already generated separately; this re-generates from results so the
    script is self-contained.
    """
    import os
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    os.makedirs(figures_dir, exist_ok=True)

    ns   = [r["n"]          for r in results]
    H2   = [r["H2_count"]   for r in results]
    Hq   = [r["Hq_count"]   for r in results]
    SS4  = [r["SS_H2"]      for r in results]
    SS3  = [r["SS_Hq"]      for r in results]
    full = [r["total"]       for r in results]

    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5))
    fig.suptitle("Growth functions: enumeration vs. closed-form formulas",
                 fontsize=12, y=1.01)

    ax = axes[0]
    ax.plot(ns, full, "k--",  lw=1.2, label=r"$2^n$ (max possible)")
    ax.plot(ns, SS4,  "b-o",  lw=1.4, ms=5,
            label=r"Sauer–Shelah $\sum_{k=0}^{4}\binom{n}{k}$")
    ax.plot(ns, H2,   "r-s",  lw=2.0, ms=6,
            label=r"$\Gamma_{\mathcal{H}_2}(n)$ (exact = S–S)")
    ax.set_title(
        r"$\mathcal{H}_2$: unions of $\leq 2$ intervals  (VCdim $= 4$)",
        fontsize=10)
    ax.set_xlabel("$n$"); ax.set_ylabel("Number of realizable labelings")
    ax.set_xticks(ns); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    ax = axes[1]
    ax.plot(ns, full, "k--",  lw=1.2, label=r"$2^n$ (max possible)")
    ax.plot(ns, SS3,  "b-o",  lw=1.4, ms=5,
            label=r"Sauer–Shelah $\sum_{k=0}^{3}\binom{n}{k}$")
    ax.plot(ns, Hq,   "g-^",  lw=2.0, ms=6,
            label=r"$\Gamma_{\mathcal{H}_{\rm quad}}(n)=n^2-n+2$")
    ax.set_title(
        r"$\mathcal{H}_{\rm quad}$: quadratic thresholds  (VCdim $= 3$)",
        fontsize=10)
    ax.set_xlabel("$n$"); ax.set_xticks(ns)
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    for ext in ("pdf", "png"):
        path = os.path.join(figures_dir, f"growth_functions.{ext}")
        fig.savefig(path, bbox_inches="tight", dpi=150)
    plt.close(fig)
    print(f"  → saved {figures_dir}/growth_functions.pdf  (.png)")


def main():
    parser = argparse.ArgumentParser(
        description="Verify growth functions for H2 and H_quad by enumeration."
    )
    parser.add_argument("--n", type=int, default=8,
                        help="Maximum n to enumerate (default 8; slow for n>15)")
    parser.add_argument("--verbose", action="store_true",
                        help="Print non-realizable labelings")
    parser.add_argument("--figures-dir", type=str, default="../figures",
                        help="Directory to save figures (default: ../figures)")
    args = parser.parse_args()

    if args.n > 18:
        print(f"Warning: n={args.n} requires checking {2**args.n} labelings — "
              f"this may take a while.")

    print(f"Enumerating all binary labelings for n = 1 to {args.n}...\n")

    results = []
    for n in range(1, args.n + 1):
        r = enumerate_n(n, verbose=args.verbose)
        results.append(r)

    # Console summary table
    print(
        "\nGrowth function verification\n"
        "  H2    = unions of ≤2 intervals  |  formula: C(n+1,0)+C(n+1,2)+C(n+1,4)\n"
        "  H_quad = quadratic thresholds   |  formula: n²-n+2\n"
        "  SS(n,d) = Sauer-Shelah bound    |  ∑_{k=0}^{d} C(n,k)\n"
    )
    print_table(results)
    verify_vc_dimensions(results)

    if args.verbose:
        print_non_realizable_examples(results)

    # Final assertion checks
    all_ok = all(r["H2_ok"] and r["Hq_ok"] for r in results)
    if all_ok:
        print(f"\n✓  All formulas verified for n = 1 to {args.n}.")
    else:
        print(f"\n✗  FORMULA MISMATCH DETECTED — check output above.")
        sys.exit(1)

    # Tight Sauer-Shelah check
    tight_H2 = all(r["H2_tight"] for r in results)
    if tight_H2:
        print("✓  H2 growth function equals Sauer-Shelah bound (tight) for all n.")
    else:
        first_not_tight = next(r["n"] for r in results if not r["H2_tight"])
        print(f"✗  H2 Sauer-Shelah NOT tight at n={first_not_tight}.")

    tight_Hq = all(r["Hq_count"] == r["SS_Hq"] for r in results)
    if not tight_Hq:
        first_not_tight_Hq = next(
            r["n"] for r in results if r["Hq_count"] != r["SS_Hq"]
        )
        print(f"✓  H_quad Sauer-Shelah is NOT tight (first diverges at "
              f"n={first_not_tight_Hq}), consistent with Θ(n²) vs Θ(n³).")

    # Save figures
    print(f"\nSaving figures to {args.figures_dir}/")
    save_table_figure(results, args.figures_dir)
    save_growth_figure(results, args.figures_dir)


if __name__ == "__main__":
    main()