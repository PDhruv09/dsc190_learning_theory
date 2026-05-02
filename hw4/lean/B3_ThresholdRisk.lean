/-
DSC 190/291 Assignment 4, Part B.3
Scoped Lean artifact: disagreement-count arithmetic for thresholds.
-/

import Mathlib.Data.Nat.Basic

namespace HW4

/-- The number of domain points where thresholds `t` and `tau` disagree is `dist t tau`. -/
def thresholdDisagreementCount (t tau : Nat) : Nat := Nat.dist t tau

/-- Symmetry of threshold disagreement count. -/
theorem disagreement_symmetric (t tau : Nat) :
    thresholdDisagreementCount t tau = thresholdDisagreementCount tau t := by
  simp [thresholdDisagreementCount, Nat.dist_comm]

/-- The true threshold has zero disagreement with itself. -/
theorem disagreement_self (tau : Nat) :
    thresholdDisagreementCount tau tau = 0 := by
  simp [thresholdDisagreementCount]

end HW4
