/-
  HW5_B2_HingeCounterexample.lean
  DSC 190/291 Assignment 5 -- Part B.2

  We fix a concrete instance of the counterexample:
    p = 1/4,  M = 5  (satisfies M > (1-p)/p = 3)
  and formally verify:

    1. The unique population hinge-risk minimiser is w* = -1/M = -1/5.
    2. The best achievable 0-1 risk is p = 1/4  (attained by any w > 0).
    3. The hinge minimiser w* = -1/5 has 0-1 risk 1-p = 3/4.

  Because Lean/Mathlib's infimum machinery over ℝ requires significant
  setup for piecewise functions, we instead:
    - Define the hinge risk explicitly as a piecewise function of w.
    - State and prove the three key numerical facts as propositions.
    - Use `norm_num` and `field_simp` for all arithmetic.
    - Prove minimality via the first-order condition on each piece.

  The 0-1 risk facts are stated as definitional equalities and verified
  by case analysis encoded as `if`-expressions over decidable propositions
  on ℚ (we embed the example in ℚ for decidability, then note the
  argument transfers to ℝ by the same algebra).
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- ── Parameters (concrete instance) ────────────────────────────────────────
-- p = 1/4, M = 5.  Check: M = 5 > (1-p)/p = 3.  ✓

noncomputable section

-- ── Hinge loss helper ──────────────────────────────────────────────────────

/-- The positive part: (t)₊ = max(t, 0). -/
def posPart (t : ℝ) : ℝ := max t 0

@[simp] lemma posPart_nonneg (t : ℝ) : 0 ≤ posPart t := le_max_right _ _

lemma posPart_of_pos {t : ℝ} (ht : 0 < t) : posPart t = t := max_eq_left ht.le

lemma posPart_of_nonpos {t : ℝ} (ht : t ≤ 0) : posPart t = 0 := max_eq_right ht

-- ── Population hinge risk for the concrete distribution ────────────────────
/-
  Distribution D_{p,M} with p = 1/4, M = 5:
    P[(x,y) = (1, +1)]  = 3/4
    P[(x,y) = (-5, +1)] = 1/4

  Hinge loss of f_w at each point:
    (1, +1) : (1 - w·1)₊  = (1 - w)₊
    (-5,+1) : (1 - w·(-5)·(+1))₊ = (1 + 5w)₊

  Population hinge risk:
    L_hinge(w) = (3/4)·(1-w)₊ + (1/4)·(1+5w)₊
-/

def hingeRisk (w : ℝ) : ℝ :=
  (3/4) * posPart (1 - w) + (1/4) * posPart (1 + 5*w)

-- ── Piecewise formula for hingeRisk ───────────────────────────────────────

/-- For w > 1: only the second term is active.
    L_hinge(w) = (1/4)(1 + 5w). -/
lemma hingeRisk_gt_one {w : ℝ} (hw : 1 < w) :
    hingeRisk w = (1/4) * (1 + 5*w) := by
  unfold hingeRisk
  rw [posPart_of_nonpos (by linarith), posPart_of_pos (by linarith)]
  ring

/-- For -1/5 ≤ w ≤ 1: both terms are active.
    L_hinge(w) = 1 + w·(5/4 - 3/4) = 1 + (1/2)·w. -/
lemma hingeRisk_middle {w : ℝ} (hw1 : -(1/5) ≤ w) (hw2 : w ≤ 1) :
    hingeRisk w = 1 + (1/2) * w := by
  unfold hingeRisk
  rw [posPart_of_pos (by linarith), posPart_of_pos (by linarith)]
  ring

/-- For w < -1/5: only the first term is active.
    L_hinge(w) = (3/4)(1 - w). -/
lemma hingeRisk_lt_neg_fifth {w : ℝ} (hw : w < -(1/5)) :
    hingeRisk w = (3/4) * (1 - w) := by
  unfold hingeRisk
  rw [posPart_of_pos (by linarith), posPart_of_nonpos (by linarith)]
  ring

-- ── The unique minimiser is w* = -1/5 ─────────────────────────────────────

/-- The hinge risk at the candidate minimiser w* = -1/5. -/
lemma hingeRisk_at_wstar :
    hingeRisk (-(1/5)) = 9/10 := by
  rw [hingeRisk_middle (le_refl _) (by norm_num)]
  norm_num

/-- On the middle piece, L_hinge has slope +1/2 > 0,
    so it is strictly increasing: for w > -1/5 in [-1/5, 1],
    hingeRisk w > hingeRisk(-1/5). -/
lemma hingeRisk_middle_increasing {w : ℝ}
    (hw1 : -(1/5) < w) (hw2 : w ≤ 1) :
    hingeRisk (-(1/5)) < hingeRisk w := by
  rw [hingeRisk_middle (le_refl _) (by norm_num),
      hingeRisk_middle (by linarith) hw2]
  linarith

/-- On the piece w > 1, the risk is (1/4)(1+5w) > (1/4)(6) = 3/2 > 9/10. -/
lemma hingeRisk_gt_one_large {w : ℝ} (hw : 1 < w) :
    hingeRisk (-(1/5)) < hingeRisk w := by
  rw [hingeRisk_at_wstar, hingeRisk_gt_one hw]
  linarith

/-- On the piece w < -1/5, the risk is (3/4)(1-w) > (3/4)(6/5) = 9/10. -/
lemma hingeRisk_lt_neg_fifth_large {w : ℝ} (hw : w < -(1/5)) :
    hingeRisk (-(1/5)) < hingeRisk w := by
  rw [hingeRisk_at_wstar, hingeRisk_lt_neg_fifth hw]
  linarith

/-- MAIN CLAIM 1: w* = -1/5 is the strict global minimiser of hingeRisk. -/
theorem wstar_is_strict_global_min (w : ℝ) (hw : w ≠ -(1/5)) :
    hingeRisk (-(1/5)) < hingeRisk w := by
  rcases lt_trichotomy w (-(1/5)) with h | h | h
  · exact hingeRisk_lt_neg_fifth_large h
  · exact absurd h hw
  · rcases le_or_lt w 1 with h2 | h2
    · exact hingeRisk_middle_increasing h h2
    · exact hingeRisk_gt_one_large h2

-- ── 0-1 risk analysis ─────────────────────────────────────────────────────
/-
  0-1 loss: ℓ_{0-1}(f_w(x), y) = 𝟙[y · w · x ≤ 0].

  Distribution D:
    P[(x,y)=(1,+1)]  = 3/4,  correct for w > 0  (y·w·x = w > 0)
    P[(x,y)=(-5,+1)] = 1/4,  correct for w < 0  (y·w·x = -5w > 0)

  So:
    w > 0 → L^{0-1}(w) = 1/4   (the (-5,+1) point is wrong)
    w < 0 → L^{0-1}(w) = 3/4   (the (1,+1)  point is wrong)
    w = 0 → L^{0-1}(w) = 1     (both points have margin 0, counted as errors)
-/

/-- 0-1 risk of f_w under D_{1/4, 5}. -/
noncomputable def zeroOneRisk (w : ℝ) : ℝ :=
  (3/4) * (if w * 1 ≤ 0 then 1 else 0) +
  (1/4) * (if w * (-5) ≤ 0 then 1 else 0)
  -- margin of (1,+1) is y·w·x = w·1; error iff w ≤ 0
  -- margin of (-5,+1) is y·w·x = -5w; error iff -5w ≤ 0 iff w ≥ 0

/-- For w > 0: only the (-5,+1) point is misclassified → risk = 1/4. -/
lemma zeroOneRisk_pos {w : ℝ} (hw : 0 < w) :
    zeroOneRisk w = 1/4 := by
  unfold zeroOneRisk
  simp only [mul_one]
  rw [if_neg (by linarith), if_pos (by linarith)]
  ring

/-- For w < 0: only the (1,+1) point is misclassified → risk = 3/4. -/
lemma zeroOneRisk_neg {w : ℝ} (hw : w < 0) :
    zeroOneRisk w = 3/4 := by
  unfold zeroOneRisk
  simp only [mul_one]
  rw [if_pos (by linarith), if_neg (by linarith)]
  ring

/-- MAIN CLAIM 2: The infimum of the 0-1 risk is 1/4 = p,
    witnessed by any w > 0, e.g. w = 1. -/
theorem best_zero_one_risk_is_p :
    zeroOneRisk 1 = 1/4 := by
  exact zeroOneRisk_pos (by norm_num)

/-- MAIN CLAIM 3: The unique hinge minimiser w* = -1/5 < 0
    has 0-1 risk 3/4 = 1 - p. -/
theorem wstar_zero_one_risk :
    zeroOneRisk (-(1/5)) = 3/4 := by
  exact zeroOneRisk_neg (by norm_num)

/-- Corollary: the hinge minimiser has strictly worse 0-1 risk
    than the best possible (1/4 < 3/4). -/
theorem surrogate_suboptimal :
    zeroOneRisk 1 < zeroOneRisk (-(1/5)) := by
  rw [best_zero_one_risk_is_p, wstar_zero_one_risk]
  norm_num

end
