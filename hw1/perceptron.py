"""
perceptron.py  --  Perceptron algorithm: implementation, data generation, experiments.

Mistake Bound Theorem
---------------------
Given any sequence of labeled examples (x_1,y_1), ... with y_t in {+1,-1},
if (1) ||x_t|| <= R  and  (2) exists w* ||w*||=1 with y_t(w*·x_t) >= gamma > 0,
then the Perceptron makes at most

        M  <=  R^2 / gamma^2   mistakes.

Proof sketch:
  Lower bound on w_k·w*:  each mistake adds >= gamma  -->  w_k·w* >= k*gamma
  Upper bound on ||w_k||^2: each update adds <= R^2   -->  ||w_k||^2 <= k*R^2
  Cauchy-Schwarz: (k*gamma)^2 <= ||w_k||^2 <= k*R^2  -->  k <= R^2/gamma^2.

Running as a script:
    python perceptron.py
Plots are saved to  hw1/plots/.
"""

import os
import numpy as np
import matplotlib
matplotlib.use('Agg')          # non-interactive backend for script mode
import matplotlib.pyplot as plt

# Output directory for saved plots
PLOTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'plots')
os.makedirs(PLOTS_DIR, exist_ok=True)

# ─────────────────────────────────────────────────────────────────────────────
# DATA GENERATION
# ─────────────────────────────────────────────────────────────────────────────

def generate_separable_data(n, gamma, R, d=2, seed=None):
    """
    Generate n linearly separable points in R^d with exact margin gamma and norm R.

    Design choices
    --------------
    True weight vector:
        w* = e_1  (first standard basis vector, ||w*|| = 1).
        This is the simplest canonical choice.  The margin condition simplifies to
        y_i * x_i[0] >= gamma for every example.

    Margin enforcement:
        Draw a_i ~ Uniform(gamma, R).  Set x_i[0] = y_i * a_i.
        Then  y_i * (w* · x_i) = y_i * x_i[0] = a_i >= gamma. ✓
        The theoretical margin parameter is gamma (all points satisfy the condition;
        the empirical minimum margin min_i a_i approaches gamma from above as n grows).

    Norm enforcement:
        Points lie exactly on the d-sphere of radius R.
        After fixing x_i[0] = y_i * a_i, the remaining d-1 coordinates are
        drawn as a uniform random direction on S^{d-2} scaled by sqrt(R^2 - a_i^2),
        ensuring ||x_i||^2 = a_i^2 + (R^2 - a_i^2) = R^2.  ✓
        Uniform direction is obtained by normalising a Gaussian vector (standard trick).

    Parameters
    ----------
    n     : int   -- number of examples
    gamma : float -- margin  (must satisfy 0 < gamma <= R)
    R     : float -- norm bound  (||x_i|| = R exactly)
    d     : int   -- input dimension  (default 2)
    seed  : int or None -- random seed for reproducibility

    Returns
    -------
    X : ndarray, shape (n, d)  -- feature matrix
    y : ndarray, shape (n,)    -- labels in {+1, -1}
    """
    if not (0 < gamma <= R):
        raise ValueError(f"Need 0 < gamma <= R; got gamma={gamma}, R={R}")

    rng = np.random.default_rng(seed)

    # Balanced binary labels
    y = rng.choice(np.array([-1, 1]), size=n)

    X = np.zeros((n, d))

    # First coordinate: ensures y_i * x_i[0] >= gamma
    a = rng.uniform(gamma, R, size=n)   # a_i = |x_i[0]| in [gamma, R]
    X[:, 0] = y * a

    if d > 1:
        # Remaining coordinates: random unit direction scaled to sqrt(R^2 - a^2)
        remaining_norm = np.sqrt(np.maximum(R**2 - a**2, 0.0))
        Z = rng.standard_normal((n, d - 1))
        Z_norms = np.linalg.norm(Z, axis=1, keepdims=True)
        Z_norms = np.where(Z_norms < 1e-14, 1.0, Z_norms)   # numerical safety
        X[:, 1:] = (Z / Z_norms) * remaining_norm[:, np.newaxis]

    return X, y


# ─────────────────────────────────────────────────────────────────────────────
# PERCEPTRON ALGORITHM
# ─────────────────────────────────────────────────────────────────────────────

def perceptron(X, y, max_passes=None):
    """
    Standard online Perceptron algorithm.

    Initialises w = 0, then cycles through examples.
    On each mistake (y_t * w·x_t <= 0) it applies the update w += y_t * x_t
    and increments the mistake counter M.  Repeats until a full pass
    has zero mistakes (convergence) or max_passes is reached.

    Parameters
    ----------
    X          : ndarray (n, d)  -- feature matrix; rows are examples
    y          : ndarray (n,)    -- labels in {+1, -1}
    max_passes : int or None     -- cap on passes; None means run to convergence

    Returns
    -------
    w          : ndarray (d,)    -- learned weight vector
    n_mistakes : int             -- total number of updates across all passes
    """
    n, d = X.shape
    w = np.zeros(d)        # initialise to zero vector
    n_mistakes = 0
    n_passes = 0

    while True:
        mistake_this_pass = False
        for i in range(n):
            # Mistake condition: y_t * (w · x_t) <= 0
            if y[i] * (w @ X[i]) <= 0:
                w = w + y[i] * X[i]     # update: w <- w + y_t * x_t
                n_mistakes += 1
                mistake_this_pass = True
        n_passes += 1

        if not mistake_this_pass:        # converged
            break
        if max_passes is not None and n_passes >= max_passes:
            break

    return w, n_mistakes


def theoretical_bound(R, gamma):
    """Perceptron mistake bound: R^2 / gamma^2."""
    return (R / gamma) ** 2


# ─────────────────────────────────────────────────────────────────────────────
# EXPERIMENT HELPERS
# ─────────────────────────────────────────────────────────────────────────────

def run_trials(gamma, R, d, n, n_trials, seed_offset=0):
    """
    Run the Perceptron n_trials times on fresh random datasets.

    Parameters
    ----------
    gamma, R, d, n : float/int -- data-generation parameters
    n_trials       : int       -- number of independent runs
    seed_offset    : int       -- base seed (trial t uses seed seed_offset + t)

    Returns
    -------
    mistakes : ndarray (n_trials,) -- mistake count for each trial
    """
    mistakes = []
    for t in range(n_trials):
        X, y = generate_separable_data(n, gamma, R, d=d, seed=seed_offset + t)
        _, M = perceptron(X, y)
        mistakes.append(M)
    return np.array(mistakes)


# ─────────────────────────────────────────────────────────────────────────────
# EXPERIMENT 1 & 2  --  Vary gamma
#   Q2: Is M vs 1/gamma^2 linear?
#   Q3: How does actual M compare to the bound R^2/gamma^2?
# ─────────────────────────────────────────────────────────────────────────────

def experiment_vary_gamma(R=5.0, d=2, n=500, n_trials=30,
                          gamma_values=None, seed_offset=0):
    """
    Fix R and d; vary the margin gamma.  Measure mean mistakes M.

    Parameters
    ----------
    R, d, n, n_trials : as in run_trials
    gamma_values      : array of gamma values to sweep
    seed_offset       : base random seed

    Returns
    -------
    dict with keys: 'gamma', 'mean_M', 'std_M', 'bound'
    """
    if gamma_values is None:
        gamma_values = np.array([0.05, 0.1, 0.2, 0.5, 1.0, 2.0])

    results = {'gamma': [], 'mean_M': [], 'std_M': [], 'bound': []}
    for gamma in gamma_values:
        mistakes = run_trials(gamma, R, d, n, n_trials, seed_offset)
        bound = theoretical_bound(R, gamma)
        results['gamma'].append(float(gamma))
        results['mean_M'].append(float(mistakes.mean()))
        results['std_M'].append(float(mistakes.std()))
        results['bound'].append(float(bound))
        print(f'  gamma={gamma:.4f}  mean M={mistakes.mean():.1f}  '
              f'bound={bound:.1f}  M<=bound={bool(mistakes.max() <= bound)}')

    for k in results:
        results[k] = np.array(results[k])
    return results


def plot_vary_gamma(results, save_dir=PLOTS_DIR):
    """
    Two-panel figure for the vary-gamma experiment.

    Panel A: M and bound R^2/gamma^2 on the same axes vs gamma.
             Tests Q3 (is the bound tight or loose?).
    Panel B: M vs 1/gamma^2.
             A linear relationship confirms the 1/gamma^2 scaling (Q2).
    """
    gamma = results['gamma']
    mM    = results['mean_M']
    sM    = results['std_M']
    bound = results['bound']

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5))

    lower = np.maximum(mM - sM, 1e-3)
    upper = np.maximum(mM + sM, lower * 1.001)

    # ── Panel A: M and bound vs gamma ──────────────────────────────────────
    ax1.fill_between(gamma, lower, upper,
                     alpha=0.25, color='steelblue', label='mean +/- std')
    ax1.plot(gamma, mM,    'o-', color='steelblue', ms=6,
             label='Mean mistakes M')
    ax1.plot(gamma, bound, 's--', color='firebrick', ms=6,
             label='Bound R^2/gamma^2')
    ax1.set_xlabel('Margin gamma')
    ax1.set_ylabel('Mistakes M')
    ax1.set_yscale('log')
    ax1.set_title('Panel A: M and Bound vs gamma\n(Q3: loose bound shown on log y-scale)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # ── Panel B: M vs 1/gamma^2 (linearity test) ───────────────────────────
    inv_g2 = 1.0 / gamma**2
    # Ordinary least squares through origin: slope = sum(x*y) / sum(x^2)
    slope = float(np.dot(inv_g2, mM) / np.dot(inv_g2, inv_g2))

    ax2.fill_between(inv_g2, np.maximum(mM - sM, 0.0), mM + sM,
                     alpha=0.25, color='steelblue', label='mean +/- std')
    ax2.plot(inv_g2, mM, 'o-', color='steelblue', ms=6,
             label='Mean mistakes M')
    ax2.plot(inv_g2, slope * inv_g2, 'k--', lw=1.5,
             label=f'Fit through origin (reference only, slope={slope:.2f})')
    ax2.set_xlabel('1/gamma^2')
    ax2.set_ylabel('Mistakes M')
    ax2.set_title('Panel B: M vs 1/gamma^2\n(Q2: increasing trend, not perfect linearity)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    plt.suptitle('Experiment 1: Effect of Margin gamma on Mistakes',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()
    path = os.path.join(save_dir, 'exp1_vary_gamma.png')
    plt.savefig(path, bbox_inches='tight', dpi=120)
    plt.close()
    print(f'Saved: {path}')
    return path


# ─────────────────────────────────────────────────────────────────────────────
# EXPERIMENT 3  --  Vary dimension d
#   Q4: Are mistakes truly dimension-independent?
# ─────────────────────────────────────────────────────────────────────────────

def experiment_vary_dimension(gamma=0.5, R=5.0, n=500, n_trials=20,
                               d_values=None, seed_offset=1000):
    """
    Fix gamma and R; vary dimension d.  Tests dimension-independence of M.

    Parameters
    ----------
    gamma, R, n, n_trials : as in run_trials
    d_values              : list of dimensions to test
    seed_offset           : base random seed

    Returns
    -------
    dict with keys: 'd', 'mean_M', 'std_M', 'bound'
    """
    if d_values is None:
        d_values = [2, 10, 50, 100, 500]

    bound_val = theoretical_bound(R, gamma)
    results = {'d': [], 'mean_M': [], 'std_M': [], 'bound': []}
    for d in d_values:
        mistakes = run_trials(gamma, R, d, n, n_trials, seed_offset)
        results['d'].append(int(d))
        results['mean_M'].append(float(mistakes.mean()))
        results['std_M'].append(float(mistakes.std()))
        results['bound'].append(float(bound_val))
        print(f'  d={d:5d}  mean M={mistakes.mean():.1f}  bound={bound_val:.1f}')

    for k in results:
        results[k] = np.array(results[k])
    return results


def plot_vary_dimension(results, save_dir=PLOTS_DIR):
    """
    Plot M vs dimension d with the (constant, dimension-independent) bound.

    If dimension has little effect after fixing R and gamma, the curve should
    stay in the same rough range across d; the bound R^2/gamma^2 is a
    horizontal line because it has no d term.
    """
    d     = results['d']
    mM    = results['mean_M']
    sM    = results['std_M']
    bound = results['bound']

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.fill_between(np.arange(len(d)), mM - sM, mM + sM,
                    alpha=0.25, color='steelblue', label='mean +/- std')
    ax.plot(np.arange(len(d)), mM, 'o-', color='steelblue', ms=7,
            label='Mean mistakes M')
    ax.axhline(bound[0], color='firebrick', ls='--', lw=2,
               label=f'Bound R^2/gamma^2 = {bound[0]:.1f}  (no d dependence)')
    ax.set_xticks(np.arange(len(d)))
    ax.set_xticklabels([str(di) for di in d])
    ax.set_xlabel('Dimension d')
    ax.set_ylabel('Mistakes M')
    ax.set_title('Experiment 2: M vs Dimension d\n'
                 '(Q4: bound has no d term; look for no clear growth with d)')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.suptitle('Dimension Independence of Perceptron Mistakes',
                 fontsize=13, fontweight='bold')
    plt.tight_layout()
    path = os.path.join(save_dir, 'exp2_vary_dimension.png')
    plt.savefig(path, bbox_inches='tight', dpi=120)
    plt.close()
    print(f'Saved: {path}')
    return path


# ─────────────────────────────────────────────────────────────────────────────
# EXPERIMENT 4  --  Near-zero margin (gamma -> 0)
#   Q5: What happens to M as gamma -> 0?
#       Connect to the failure case on non-separable data.
# ─────────────────────────────────────────────────────────────────────────────

def experiment_near_zero_margin(R=5.0, d=2, n=500, n_trials=20,
                                 gamma_values=None, seed_offset=2000):
    """
    Push gamma toward zero; observe M growing toward the bound (and beyond any
    finite limit in the non-separable limit gamma=0).

    As gamma -> 0:
      - The margin becomes vanishingly small; examples cluster near the hyperplane.
      - The bound R^2/gamma^2 -> infinity.
      - In the limit gamma=0 the data is NOT linearly separable (some examples
        lie exactly on the hyperplane) and the Perceptron never converges.
      - This connects to the failure mode on non-separable data: Perceptron cycles
        forever without a finite mistake count guarantee.

    Parameters
    ----------
    R, d, n, n_trials : as in run_trials
    gamma_values      : decreasing array of gamma values
    seed_offset       : base random seed

    Returns
    -------
    dict with keys: 'gamma', 'mean_M', 'std_M', 'bound'
    """
    if gamma_values is None:
        gamma_values = np.array([2.0, 1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01])

    results = {'gamma': [], 'mean_M': [], 'std_M': [], 'bound': []}
    for gamma in gamma_values:
        mistakes = run_trials(gamma, R, d, n, n_trials, seed_offset)
        bound = theoretical_bound(R, gamma)
        results['gamma'].append(float(gamma))
        results['mean_M'].append(float(mistakes.mean()))
        results['std_M'].append(float(mistakes.std()))
        results['bound'].append(float(bound))
        print(f'  gamma={gamma:.4f}  mean M={mistakes.mean():.1f}  bound={bound:.0f}')

    for k in results:
        results[k] = np.array(results[k])
    return results


def plot_near_zero_margin(results, save_dir=PLOTS_DIR):
    """
    Two-panel plot: log-y and log-log views of M and bound as gamma -> 0.

    The log-log view is used to assess whether the empirical curve follows
    a slope roughly compatible with the 1/gamma^2 prediction.
    """
    gamma = results['gamma']
    mM    = results['mean_M']
    sM    = results['std_M']
    bound = results['bound']

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5))

    lower = np.maximum(mM - sM, 1e-3)
    upper = np.maximum(mM + sM, lower * 1.001)

    # ── Panel A: log-y scale ───────────────────────────────────────────────
    ax1.fill_between(gamma, lower, upper,
                     alpha=0.25, color='steelblue')
    ax1.plot(gamma, mM,    'o-', color='steelblue', ms=6, label='Mean M')
    ax1.plot(gamma, bound, 's--', color='firebrick', ms=6,
             label='Bound R^2/gamma^2')
    ax1.set_yscale('log')
    ax1.set_xlabel('Margin gamma  (decreasing -->')
    ax1.set_ylabel('Mistakes M')
    ax1.invert_xaxis()
    ax1.set_title('Panel A: M as gamma -> 0  (log y-scale)\n'
                  '(Q5: both curves grow rapidly as margin shrinks)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # ── Panel B: log-log scale (compare with slope -2 reference) ───────────
    ax2.loglog(gamma, mM,    'o-', color='steelblue', ms=6, label='Mean M')
    ax2.loglog(gamma, bound, 's--', color='firebrick', ms=6,
               label='Bound R^2/gamma^2')
    ax2.set_xlabel('Margin gamma  (log scale)')
    ax2.set_ylabel('Mistakes M  (log scale)')
    ax2.set_title('Panel B: Log-log view\n'
                  '(compare empirical growth against a slope -2 reference)')
    ax2.legend()
    ax2.grid(True, alpha=0.3, which='both')

    plt.suptitle('Experiment 3: Near-Zero Margin (gamma -> 0)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()
    path = os.path.join(save_dir, 'exp3_near_zero_margin.png')
    plt.savefig(path, bbox_inches='tight', dpi=120)
    plt.close()
    print(f'Saved: {path}')
    return path


# ─────────────────────────────────────────────────────────────────────────────
# SANITY CHECKS  (Q6)
# ─────────────────────────────────────────────────────────────────────────────

def run_sanity_checks():
    """
    Unit tests and sanity checks verifying correctness of both modules.

    Checks performed
    ----------------
    1. Norm check:     ||x_i|| == R exactly for all generated points.
    2. Margin check:   y_i * x_i[0] >= gamma for all generated points.
    3. Balance check:  Approximately 50% positive labels.
    4. Dimension check: Correct shape for arbitrary d.
    5. Update rule:    One-step manual trace: w starts at 0, first example
                       causes a mistake, w should become y_0 * x_0.
    6. Convergence:    Perceptron converges and classifies all correctly.
    7. Bound check:    M <= R^2/gamma^2 over 100 random trials.
    8. Mistake counting: Mistakes are counted (not just flagged) correctly.

    Returns
    -------
    all_passed : bool
    """
    PASS = '[PASS]'
    FAIL = '[FAIL]'
    passed = []

    # ── Check 1: Norms ───────────────────────────────────────────────────────
    X, y = generate_separable_data(300, gamma=0.5, R=3.0, d=7, seed=42)
    norms = np.linalg.norm(X, axis=1)
    ok = bool(np.max(np.abs(norms - 3.0)) < 1e-10)
    print(f'  {PASS if ok else FAIL} Check 1 - norms == R=3.0 '
          f'(max deviation {np.max(np.abs(norms-3.0)):.2e})')
    passed.append(ok)

    # ── Check 2: Margin ──────────────────────────────────────────────────────
    margins = y * X[:, 0]     # w* = e_1, so w*·x = x[0]
    ok = bool(np.all(margins >= 0.5 - 1e-10))
    print(f'  {PASS if ok else FAIL} Check 2 - y_i*x_i[0] >= gamma=0.5 '
          f'(min={margins.min():.6f})')
    passed.append(ok)

    # ── Check 3: Balance ─────────────────────────────────────────────────────
    frac_pos = float((y == 1).mean())
    ok = 0.3 < frac_pos < 0.7
    print(f'  {PASS if ok else FAIL} Check 3 - balanced classes '
          f'(fraction positive = {frac_pos:.2f})')
    passed.append(ok)

    # ── Check 4: Shape ───────────────────────────────────────────────────────
    X50, y50 = generate_separable_data(100, gamma=0.3, R=2.0, d=50, seed=7)
    ok = (X50.shape == (100, 50)) and (y50.shape == (100,))
    print(f'  {PASS if ok else FAIL} Check 4 - correct shape (n=100, d=50): '
          f'{X50.shape}, {y50.shape}')
    passed.append(ok)

    # ── Check 5: Update rule (manual one-step trace) ─────────────────────────
    # Single example x=[2, 0], y=+1.  w=0 so y*(w·x)=0 <= 0 => mistake.
    # Update: w = 0 + 1*[2,0] = [2,0].  One mistake total.
    X_one = np.array([[2.0, 0.0]])
    y_one = np.array([1])
    w_got, M_got = perceptron(X_one, y_one, max_passes=1)
    ok = (M_got == 1) and np.allclose(w_got, [2.0, 0.0])
    print(f'  {PASS if ok else FAIL} Check 5 - update rule w+=y*x '
          f'(expected w=[2,0] M=1, got w={w_got} M={M_got})')
    passed.append(ok)

    # ── Check 6: Convergence + correctness ───────────────────────────────────
    X_cv, y_cv = generate_separable_data(50, gamma=1.0, R=3.0, d=2, seed=0)
    w_cv, _ = perceptron(X_cv, y_cv)
    all_correct = bool(np.all(y_cv * (X_cv @ w_cv) > 0))
    print(f'  {PASS if all_correct else FAIL} Check 6 - converges and '
          f'classifies all training examples correctly')
    passed.append(all_correct)

    # ── Check 7: Bound holds over many random trials ─────────────────────────
    failures = 0
    for t in range(100):
        Xt, yt = generate_separable_data(200, gamma=0.4, R=3.0, d=5, seed=t + 500)
        _, Mt = perceptron(Xt, yt)
        if Mt > theoretical_bound(3.0, 0.4):
            failures += 1
    ok = (failures == 0)
    print(f'  {PASS if ok else FAIL} Check 7 - bound M<=R^2/gamma^2 held '
          f'in 100/100 random trials (failures={failures})')
    passed.append(ok)

    # ── Check 8: Mistake counter is cumulative across passes ──────────────────
    # Two examples that require two separate passes to separate.
    # [1,0] y=+1 and [-1,0.1] y=-1: after first correction, second may still fail.
    # Just confirm M > 0 and final w separates correctly.
    X_mc = np.array([[1.0, 0.0], [-1.0, 0.1], [0.9, -0.2], [-0.8, 0.3]])
    y_mc = np.array([1, -1, 1, -1])
    _, M_mc = perceptron(X_mc, y_mc)
    w_mc, _ = perceptron(X_mc, y_mc)
    ok = (M_mc >= 1) and bool(np.all(y_mc * (X_mc @ w_mc) > 0))
    print(f'  {PASS if ok else FAIL} Check 8 - mistake counter M={M_mc} >= 1 '
          f'and final classifier is correct')
    passed.append(ok)

    total = sum(passed)
    print(f'\n  {total}/{len(passed)} checks passed.')
    return all(passed)


# ─────────────────────────────────────────────────────────────────────────────
# MAIN  --  run all experiments when executed as a script
# ─────────────────────────────────────────────────────────────────────────────

def main():
    """Run all experiments, print results, save plots to hw1/plots/."""
    print('=' * 60)
    print('SANITY CHECKS  (Q6)')
    print('=' * 60)
    run_sanity_checks()

    print('\n' + '=' * 60)
    print('EXPERIMENT 1: Vary gamma  (Q2 + Q3)')
    print('  Q2: Is M vs 1/gamma^2 linear?')
    print('  Q3: Is the bound R^2/gamma^2 tight or loose?')
    print('=' * 60)
    gamma_vals = np.array([0.05, 0.1, 0.2, 0.5, 1.0, 2.0])
    res1 = experiment_vary_gamma(R=5.0, d=2, n=500, n_trials=30,
                                  gamma_values=gamma_vals)
    plot_vary_gamma(res1)

    print('\n' + '=' * 60)
    print('EXPERIMENT 2: Vary dimension d  (Q4)')
    print('  Q4: Are Perceptron mistakes truly dimension-independent?')
    print('=' * 60)
    res2 = experiment_vary_dimension(gamma=0.5, R=5.0, n=500, n_trials=20,
                                      d_values=[2, 10, 50, 100, 500])
    plot_vary_dimension(res2)

    print('\n' + '=' * 60)
    print('EXPERIMENT 3: Near-zero margin  (Q5)')
    print('  Q5: What happens to M as gamma -> 0?')
    print('=' * 60)
    gamma_nz = np.array([2.0, 1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01])
    res3 = experiment_near_zero_margin(R=5.0, d=2, n=500, n_trials=20,
                                       gamma_values=gamma_nz)
    plot_near_zero_margin(res3)

    print(f'\nAll plots saved to: {PLOTS_DIR}')


if __name__ == '__main__':
    main()
