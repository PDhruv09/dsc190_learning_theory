/-
DSC 190/291 Assignment 4, Part B.4
Scoped Lean artifact: pigeonhole-style structure for fixed-prior attacks.
The analytic statement about real-valued probabilities is left to the paper proof.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace HW4

/-- Internal threshold indices for a domain of size `N` are those satisfying 2 <= t <= N. -/
def IsInternalThreshold (N t : Nat) : Prop := 2 <= t ∧ t <= N

/-- If a sample contains the two adjacent support points around `tau`, then the only
consistent threshold index is `tau`. This captures the deterministic core of Part B.4. -/
theorem adjacent_points_force_singleton {tau t : Nat}
    (hneg : tau - 1 < t) (hpos : t <= tau) (htau : 1 <= tau) : t = tau := by
  omega

end HW4
