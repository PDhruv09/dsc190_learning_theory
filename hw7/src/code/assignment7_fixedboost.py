"""
Assignment 7 FixedBoost Experiments.

This file collects the Python code used across Parts D1 and D2 of the
assignment. It includes:

1. A direct implementation of FixedBoost on a sign matrix.
2. A linear-program solver for the optimal normalized empirical l1 margin.
3. Two synthetic instances:
   - a large-margin instance with one strongly aligned coordinate,
   - a small-margin instance with random labels and weak coordinate structure.
4. A plotting routine that compares the FixedBoost normalized margin against
   the optimal margin returned by the linear program.

Interpretation of the two instances:
- In the large-margin instance, the labels are mostly determined by the first
  coordinate, so one signed coordinate predictor already has strong alignment
  with the labels. This leads to a large weak-learning edge and a large
  optimal normalized margin.
- In the small-margin instance, the labels are random and independent of the
  coordinates. No single coordinate predictor is consistently useful, and even
  convex combinations cannot drive all example margins far above zero. As a
  result, the optimal normalized margin is small.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import linprog


def fixed_boost(A, eta=0.1, T=500):
    """
    Run FixedBoost directly on the sign matrix A.

    Parameters
    ----------
    A : np.ndarray
        Matrix of shape (n, m), where A[i, g] = y_i g(x_i).
    eta : float
        Fixed step size.
    T : int
        Number of boosting rounds.

    Returns
    -------
    margins : list[float]
        Normalized empirical margin at each round.
    l1_norms : list[float]
        L1 norm of the coefficient vector at each round.
    weights : np.ndarray
        Final coefficient vector over base predictors.
    """
    n, m = A.shape
    w = np.zeros(m)

    margins = []
    l1_norms = []

    for t in range(1, T + 1):
        scores = A @ w
        exp_weights = np.exp(-scores)
        D = exp_weights / exp_weights.sum()

        correlations = D @ A
        g_t = np.argmax(correlations)

        w[g_t] += eta

        l1 = np.sum(np.abs(w))
        scores = A @ w

        if l1 > 0:
            normalized_margin = np.min(scores) / l1
        else:
            normalized_margin = 0.0

        margins.append(normalized_margin)
        l1_norms.append(l1)

    return margins, l1_norms, w


def optimal_margin_lp(A):
    """
    Solve the LP for the optimal normalized l1 margin.

    max rho
    subject to A p >= rho 1
               sum p = 1
               p >= 0

    Parameters
    ----------
    A : np.ndarray
        Sign matrix of shape (n, m).

    Returns
    -------
    rho_opt : float
        Optimal normalized margin.
    p_opt : np.ndarray
        Optimal distribution over base predictors.
    """
    n, m = A.shape

    # Variables are [p_1, ..., p_m, rho]
    c = np.zeros(m + 1)
    c[-1] = -1  # maximize rho = minimize -rho

    A_ub = []
    b_ub = []

    for i in range(n):
        row = np.zeros(m + 1)
        row[:m] = -A[i, :]
        row[-1] = 1
        A_ub.append(row)
        b_ub.append(0)

    A_eq = np.zeros((1, m + 1))
    A_eq[0, :m] = 1
    b_eq = np.array([1])

    bounds = [(0, None)] * m + [(None, None)]

    result = linprog(
        c,
        A_ub=np.array(A_ub),
        b_ub=np.array(b_ub),
        A_eq=A_eq,
        b_eq=b_eq,
        bounds=bounds,
        method="highs",
    )

    if not result.success:
        raise RuntimeError(result.message)

    p_opt = result.x[:m]
    rho_opt = result.x[-1]

    return rho_opt, p_opt


def make_large_margin_instance(n=100, d=20, seed=0):
    """
    Construct an easy instance where one coordinate is strongly aligned
    with the labels, so the optimal margin is large.
    """
    rng = np.random.default_rng(seed)

    X = rng.choice([-1, 1], size=(n, d))
    y = X[:, 0].copy()

    # Add small label noise.
    flip = rng.random(n) < 0.05
    y[flip] *= -1

    A_pos = y[:, None] * X
    A_neg = y[:, None] * (-X)
    A = np.concatenate([A_pos, A_neg], axis=1)

    return A


def make_small_margin_instance(n=100, d=20, seed=1):
    """
    Construct a harder instance where labels are mostly random,
    so no coordinate predictor has strong edge under all distributions.
    """
    rng = np.random.default_rng(seed)

    X = rng.choice([-1, 1], size=(n, d))
    y = rng.choice([-1, 1], size=n)

    A_pos = y[:, None] * X
    A_neg = y[:, None] * (-X)
    A = np.concatenate([A_pos, A_neg], axis=1)

    return A


def run_experiment(A, title, eta=0.1, T=500):
    """
    Run FixedBoost and compare its normalized margin trajectory against
    the optimal margin returned by the linear program.
    """
    rho_opt, _ = optimal_margin_lp(A)
    margins, l1_norms, w = fixed_boost(A, eta=eta, T=T)

    rounds = np.arange(1, T + 1)

    plt.figure(figsize=(8, 5))
    plt.plot(rounds, margins, label="FixedBoost normalized margin")
    plt.axhline(rho_opt, linestyle="--", label=f"Optimal margin = {rho_opt:.3f}")
    plt.xlabel("Round")
    plt.ylabel("Normalized empirical margin")
    plt.title(title)
    plt.legend()
    plt.tight_layout()
    plt.show()

    return rho_opt, margins, l1_norms, w


if __name__ == "__main__":
    A_easy = make_large_margin_instance()
    A_hard = make_small_margin_instance()

    easy_opt, easy_margins, _, _ = run_experiment(
        A_easy,
        "Large-margin instance",
        eta=0.1,
        T=500,
    )

    hard_opt, hard_margins, _, _ = run_experiment(
        A_hard,
        "Small-margin instance",
        eta=0.1,
        T=500,
    )

    print("Easy optimal margin:", easy_opt)
    print("Easy final FixedBoost margin:", easy_margins[-1])

    print("Hard optimal margin:", hard_opt)
    print("Hard final FixedBoost margin:", hard_margins[-1])
