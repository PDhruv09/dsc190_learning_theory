"""
hw5_a3_experiment.py
DSC 190/291 Assignment 5 -- Part A.3

Compares:
  1. Proper sparse 0-1 search (brute-force support enumeration + weight grid search)
  2. Convex surrogate: L1-penalized logistic regression

Experiments:
  A. Runtime and 0-1 error vs. dimension d (k=2 fixed)
  B. Runtime vs. sparsity k (d=10 fixed)

Reproduces the tables in the write-up.
"""

import itertools
import time

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from sklearn.linear_model import LogisticRegression

# -- Reproducibility ---------------------------------------------------------
RNG = np.random.default_rng(42)

# -- Weight grid used by brute-force baseline --------------------------------
GRID = np.linspace(-2.0, 2.0, 7)   # 7 values: -2, -4/3, -2/3, 0, 2/3, 4/3, 2


# -- Data generation ---------------------------------------------------------

def make_sparse_data(d: int, k: int, n: int = 150, noise: float = 0.05):
    """
    Draw n samples from a k-sparse halfspace with small Gaussian noise.

    The true weight vector has k nonzero coordinates, each +1 or -1.
    Labels are sign(<w*, x> + noise).
    """
    support = RNG.choice(d, k, replace=False)
    w_true = np.zeros(d)
    w_true[support] = RNG.choice([-1.0, 1.0], k)
    X = RNG.standard_normal((n, d))
    y = np.sign(X @ w_true + noise * RNG.standard_normal(n))
    y[y == 0] = 1.0
    return X, y


# -- 0-1 loss ----------------------------------------------------------------

def zero_one_loss(X, y, w):
    """Empirical 0-1 loss of the classifier sign(<w, x>)."""
    preds = np.sign(X @ w)
    preds[preds == 0] = 1.0
    return float(np.mean(preds != y))


# -- Method 1: Proper sparse 0-1 search --------------------------------------

def brute_force_sparse(X, y, k, grid=GRID):
    """
    Exact over the finite weight grid:
      Enumerate all C(d, k) supports of size k.
      For each support, grid-search over weights in `grid` per active coordinate.
      Return the weight vector minimising empirical 0-1 loss.

    This is an *approximate* ERM overall (the true minimiser may not lie on
    the grid), but on low-noise data it consistently recovers the true support.
    """
    d = X.shape[1]
    best_err = 1.0
    best_w = np.zeros(d)

    for support in itertools.combinations(range(d), k):
        for weights in itertools.product(grid, repeat=k):
            w = np.zeros(d)
            w[list(support)] = weights
            err = zero_one_loss(X, y, w)
            if err < best_err:
                best_err = err
                best_w = w.copy()

    return best_w, best_err


# -- Method 2: L1-logistic regression (convex surrogate) ---------------------

def l1_logistic(X, y, C=0.5):
    """
    L1-penalised logistic regression.

    This is a *convex* programme; it minimises the logistic surrogate loss
    subject to an implicit L1 penalty.  The output is generally NOT k-sparse:
    the L1 penalty encourages sparsity but does not enforce ||w||_0 <= k.
    The learner is therefore *improper* with respect to H_{d,k}.
    """
    clf = LogisticRegression(
        penalty="l1", C=C, solver="liblinear", max_iter=1000
    )
    clf.fit(X, y)
    w = clf.coef_[0]
    return w, zero_one_loss(X, y, w)


# -- Experiment A: vary d, fix k = 2 -----------------------------------------

def experiment_vs_d(d_values, k=2, n=150):
    print(f"\n{'='*60}")
    print(f"Experiment A: Runtime and 0-1 error vs. d  (k={k}, n={n})")
    print(f"{'='*60}")
    print(f"{'d':>4}  {'BF time':>10}  {'LR time':>10}  {'BF err':>8}  {'LR err':>8}")
    print("-" * 50)

    results = dict(d=[], t_bf=[], t_lr=[], e_bf=[], e_lr=[])

    for d in d_values:
        X, y = make_sparse_data(d, k, n)

        t0 = time.perf_counter()
        _, e_bf = brute_force_sparse(X, y, k)
        t_bf = time.perf_counter() - t0

        t0 = time.perf_counter()
        _, e_lr = l1_logistic(X, y)
        t_lr = time.perf_counter() - t0

        print(f"{d:>4}  {t_bf:>10.3f}  {t_lr:>10.4f}  {e_bf:>8.3f}  {e_lr:>8.3f}")
        results["d"].append(d)
        results["t_bf"].append(t_bf)
        results["t_lr"].append(t_lr)
        results["e_bf"].append(e_bf)
        results["e_lr"].append(e_lr)

    return results


# -- Experiment B: vary k, fix d = 10 ----------------------------------------

def experiment_vs_k(k_values, d=10, n=150):
    print(f"\n{'='*60}")
    print(f"Experiment B: Runtime vs. k  (d={d}, n={n})")
    print(f"{'='*60}")
    print(f"{'k':>4}  {'BF time':>10}  {'LR time':>10}")
    print("-" * 30)

    results = dict(k=[], t_bf=[], t_lr=[])

    for k in k_values:
        X, y = make_sparse_data(d, k, n)

        t0 = time.perf_counter()
        brute_force_sparse(X, y, k)
        t_bf = time.perf_counter() - t0

        t0 = time.perf_counter()
        l1_logistic(X, y)
        t_lr = time.perf_counter() - t0

        print(f"{k:>4}  {t_bf:>10.3f}  {t_lr:>10.4f}")
        results["k"].append(k)
        results["t_bf"].append(t_bf)
        results["t_lr"].append(t_lr)

    return results


# -- Plotting -----------------------------------------------------------------

def make_plots(res_d, res_k, outpath="hw5_a3_experiment.png"):
    fig, axes = plt.subplots(1, 3, figsize=(14, 4))
    fig.suptitle(
        "Part A.3: Proper Sparse 0-1 Search vs. L1-Logistic Surrogate",
        fontsize=12, fontweight="bold",
    )

    BF_COL = "royalblue"
    LR_COL = "tomato"
    LW = 2

    # Panel 1: runtime vs d
    ax = axes[0]
    ax.plot(res_d["d"], res_d["t_bf"], "o-", label="Brute-force (proper 0-1)",
            color=BF_COL, lw=LW)
    ax.plot(res_d["d"], res_d["t_lr"], "s--", label="L1-logistic (surrogate)",
            color=LR_COL, lw=LW)
    ax.set_xlabel("d (dimension)")
    ax.set_ylabel("Wall-clock time (s)")
    ax.set_title("Runtime vs. d  (k=2 fixed)")
    ax.legend(fontsize=8)
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)

    # Panel 2: runtime vs k
    ax = axes[1]
    ax.plot(res_k["k"], res_k["t_bf"], "o-", label="Brute-force (proper 0-1)",
            color=BF_COL, lw=LW)
    ax.plot(res_k["k"], res_k["t_lr"], "s--", label="L1-logistic (surrogate)",
            color=LR_COL, lw=LW)
    ax.set_xlabel("k (sparsity)")
    ax.set_ylabel("Wall-clock time (s)")
    ax.set_title("Runtime vs. k  (d=10 fixed)")
    ax.legend(fontsize=8)
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)

    # Panel 3: 0-1 error vs d
    ax = axes[2]
    ax.plot(res_d["d"], res_d["e_bf"], "o-", label="Brute-force 0-1 error",
            color=BF_COL, lw=LW)
    ax.plot(res_d["d"], res_d["e_lr"], "s--", label="L1-logistic 0-1 error",
            color=LR_COL, lw=LW)
    ax.set_xlabel("d")
    ax.set_ylabel("Empirical 0-1 error")
    ax.set_title("0-1 Error vs. d  (k=2 fixed)")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(outpath, dpi=150, bbox_inches="tight")
    print(f"\nFigure saved to {outpath}")


# -- Main ---------------------------------------------------------------------

if __name__ == "__main__":
    res_d = experiment_vs_d(d_values=[6, 8, 10, 12], k=2)
    res_k = experiment_vs_k(k_values=[1, 2, 3, 4], d=10)
    make_plots(res_d, res_k)
