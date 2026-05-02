/-
DSC 190/291 Assignment 4, Part A.5
Scoped Lean artifact: support enumeration and computational-cost skeleton.
This file intentionally formalizes deterministic structure only, not LP feasibility.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace HW4

/-- Number of supports of size `k` inside `[d]` is `Nat.choose d k`. -/
def numSupports (d k : Nat) : Nat := Nat.choose d k

/-- A symbolic brute-force runtime shape: number of supports times a polynomial oracle. -/
def bruteForceRuntime (d k n : Nat) (polyFeasibility : Nat -> Nat -> Nat) : Nat :=
  numSupports d k * polyFeasibility n k

/-- Constant-sparsity enumeration has the expected support count expression. -/
theorem runtime_unfold (d k n : Nat) (polyFeasibility : Nat -> Nat -> Nat) :
    bruteForceRuntime d k n polyFeasibility = Nat.choose d k * polyFeasibility n k := by
  rfl

end HW4
