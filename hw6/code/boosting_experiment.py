"""
Assignment 6 Part A4: Sparse boosting versus convex surrogate.

This script compares AdaBoost over signed coordinate predictors against
logistic regression with L1 regularization on two datasets:

1. An easy sparse-margin dataset with a small-coefficient separator.
2. The hard construction from Part A3, where the separator exists but
the best coordinate edge is exponentially small.

Metrics tracked over boosting rounds:
- training error
- exponential loss
- observed weak edge
- support size
- normalized margin
"""

import numpy as np
from sklearn.linear_model import LogisticRegression


def make_easy_sparse_data(n=200, d=50, s=5, seed=0):
    rng = np.random.default_rng(seed)
    X = rng.choice([-1, 1], size=(n, d))
    w = np.zeros(d)
    w[:s] = 1.0
    scores = X @ w
    y = np.where(scores >= 0, 1, -1)

    # Remove exact-zero margin points if they occur.
    keep = scores != 0
    return X[keep], y[keep], w


def make_hard_construction(m=5):
    """
    Constructs the Part A3 matrix for s = 2m + 1.
    Labels are all +1.
    """
    s = 2 * m + 1
    rows = s
    cols = []

    # Base column
    col = [1]
    for r in range(1, m + 1):
        col.extend([1, -1])
    cols.append(col)

    # Flip columns
    for flip in range(1, m + 1):
        col = [1]
        for r in range(1, m + 1):
            if r == flip:
                col.extend([-1, 1])
            else:
                col.extend([1, -1])
        cols.append(col)

    # Carry columns
    for carry in range(1, m + 1):
        col = [-1]
        for r in range(1, m + 1):
            if r < carry:
                col.extend([-1, -1])
            elif r == carry:
                col.extend([1, 1])
            else:
                col.extend([1, -1])
        cols.append(col)

    A = np.array(cols).T
    y = np.ones(rows)

    q = [1]
    for r in range(1, m + 1):
        q.extend([2 ** (r - 1), 2 ** (r - 1)])
    q = np.array(q, dtype=float)
    q = q / q.sum()

    w_star = np.linalg.solve(A, np.ones(rows))
    return A, y, q, w_star


def adaboost_coordinates(X, y, T=50, sample_weights=None):
    n, d = X.shape

    if sample_weights is None:
        D = np.ones(n) / n
    else:
        D = sample_weights.copy()
        D = D / D.sum()

    alphas = []
    coords = []
    signs = []

    history = []

    F = np.zeros(n)

    for t in range(T):
        correlations = np.array([
            np.sum(D * y * X[:, j])
            for j in range(d)
        ])

        j = np.argmax(np.abs(correlations))
        sigma = 1 if correlations[j] >= 0 else -1

        preds = sigma * X[:, j]
        err = np.sum(D[preds != y])
        err = np.clip(err, 1e-12, 1 - 1e-12)

        edge = 0.5 - err
        alpha = 0.5 * np.log((1 - err) / err)

        D *= np.exp(-alpha * y * preds)
        D /= D.sum()

        F += alpha * preds

        alphas.append(alpha)
        coords.append(j)
        signs.append(sigma)

        train_pred = np.where(F >= 0, 1, -1)
        train_err = np.mean(train_pred != y)
        exp_loss = np.mean(np.exp(-y * F))
        support_size = len(set(coords))

        if np.sum(np.abs(alphas)) > 0:
            normalized_margin = np.min(y * F) / np.sum(np.abs(alphas))
        else:
            normalized_margin = 0.0

        history.append({
            "round": t + 1,
            "train_error": train_err,
            "exp_loss": exp_loss,
            "edge": edge,
            "support_size": support_size,
            "normalized_margin": normalized_margin,
            "chosen_coord": j,
            "alpha": alpha,
        })

    return history, alphas, coords, signs


def run_logistic_l1(X, y):
    clf = LogisticRegression(
        penalty="l1",
        solver="liblinear",
        C=1.0,
        fit_intercept=False,
        max_iter=5000,
    )
    clf.fit(X, y)

    preds = clf.predict(X)
    train_err = np.mean(preds != y)
    w = clf.coef_.ravel()
    support = np.sum(np.abs(w) > 1e-8)

    if np.sum(np.abs(w)) > 0:
        normalized_margin = np.min(y * (X @ w)) / np.sum(np.abs(w))
    else:
        normalized_margin = 0.0

    return {
        "train_error": train_err,
        "support_size": support,
        "l1_norm": np.sum(np.abs(w)),
        "linf_norm": np.max(np.abs(w)),
        "normalized_margin": normalized_margin,
    }


def print_history_summary(name, history, logistic_result):
    print(f"\n===== {name} =====")
    print("AdaBoost selected rounds:")
    for row in history[::max(1, len(history)//10)]:
        print(row)

    print("\nFinal AdaBoost:")
    print(history[-1])

    print("\nL1 Logistic Regression:")
    print(logistic_result)


def main():
    # Easy sparse-margin data
    X_easy, y_easy, _ = make_easy_sparse_data(n=500, d=50, s=5, seed=1)
    hist_easy, *_ = adaboost_coordinates(X_easy, y_easy, T=50)
    log_easy = run_logistic_l1(X_easy, y_easy)
    print_history_summary("Easy sparse-margin data", hist_easy, log_easy)

    # Hard Part A3 construction
    X_hard, y_hard, q_hard, w_hard = make_hard_construction(m=6)
    hist_hard, *_ = adaboost_coordinates(X_hard, y_hard, T=100, sample_weights=q_hard)
    log_hard = run_logistic_l1(X_hard, y_hard)
    print_history_summary("Hard construction", hist_hard, log_hard)

    print("\nHard construction true separator:")
    print("support size:", np.sum(np.abs(w_hard) > 1e-8))
    print("l1 norm:", np.sum(np.abs(w_hard)))
    print("linf norm:", np.max(np.abs(w_hard)))


if __name__ == "__main__":
    main()
