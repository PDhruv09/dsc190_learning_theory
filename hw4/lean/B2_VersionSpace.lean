/-
DSC 190/291 Assignment 4, Part B.2
Scoped Lean artifact: deterministic interval form of a threshold version space.
-/

import Mathlib.Data.Finset.Basic

namespace HW4

/-- Threshold classifier on the finite ordered domain, encoded as Bool. -/
def threshold (t x : Nat) : Bool := decide (t <= x)

/-- A threshold index is consistent with summary statistics `a` and `b`. -/
def InVersionSpace (a b t : Nat) : Prop := a < t ∧ t <= b

/-- The version-space condition is exactly the interval condition. -/
theorem version_space_interval (a b t : Nat) :
    InVersionSpace a b t ↔ a < t ∧ t <= b := by
  rfl

/-- If `a < b`, then the endpoint `b` lies in the version space. -/
theorem right_endpoint_in_version_space {a b : Nat} (h : a < b) :
    InVersionSpace a b b := by
  exact ⟨h, le_rfl⟩

end HW4
