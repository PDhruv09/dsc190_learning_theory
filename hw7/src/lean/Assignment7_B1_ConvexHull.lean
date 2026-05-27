/--
Assignment 7, Part B1: Convex hull Rademacher identity, finite-vector version.

This file formalizes the core finite fact used in the proof:
maximizing a linear functional over the probability simplex gives the same
value as maximizing over the vertices.

This is the algebraic heart of:
  Rhat_S(conv(F)) = Rhat_S(F).

We model a finite function class on a fixed sample as vectors indexed by a
finite type `ι`. A convex combination is represented by weights `a : ι → ℝ`
with `0 ≤ a i` and `∑ i, a i = 1`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open BigOperators

namespace Assignment7
namespace PartB1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A simple predicate for weights in the probability simplex. -/
def InSimplex (a : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1)

/-- Weighted averages are bounded by the maximum vertex value.

This is the main inequality needed for the convex-hull argument. -/
theorem weighted_average_le_max
    (a v : ι → ℝ)
    (ha : InSimplex a)
    (M : ℝ)
    (hM : ∀ i, v i ≤ M) :
    (∑ i, a i * v i) ≤ M := by
  have hnonneg : ∀ i, 0 ≤ a i := ha.1
  have hsum : ∑ i, a i = 1 := ha.2
  calc
    ∑ i, a i * v i ≤ ∑ i, a i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hM i) (hnonneg i)
    _ = (∑ i, a i) * M := by
      rw [Finset.sum_mul]
    _ = M := by
      rw [hsum, one_mul]

/-- A convex combination cannot exceed every upper bound on the vertices. -/
theorem convex_combo_le_upper_bound
    (a v : ι → ℝ)
    (ha : InSimplex a)
    (M : ℝ)
    (hM : ∀ i, v i ≤ M) :
    (∑ i, a i * v i) ≤ M := by
  exact weighted_average_le_max a v ha M hM

/-- Every vertex is itself a simplex point.

The vector putting all mass on index `j` is in the simplex. -/
def vertex (j : ι) : ι → ℝ :=
  fun i => if i = j then 1 else 0

theorem vertex_in_simplex (j : ι) : InSimplex (vertex j) := by
  constructor
  · intro i
    unfold vertex
    by_cases h : i = j
    · simp [h]
    · simp [h]
  · unfold vertex
    simp

/-- Evaluating a convex combination at a vertex gives the vertex value. -/
theorem vertex_eval (v : ι → ℝ) (j : ι) :
    (∑ i, vertex j i * v i) = v j := by
  unfold vertex
  simp

/-- Informal bridge theorem.

Together, `weighted_average_le_max`, `vertex_in_simplex`, and `vertex_eval`
show that the supremum over the convex hull equals the maximum over vertices.
In the written solution, this becomes:

  Rhat_S(conv(F)) = Rhat_S(F).

A fully polished version would introduce `sSup` over sets of real numbers.
For homework purposes, the above finite lemmas are the clean formal core.
-/
theorem convex_hull_rademacher_core
    (a v : ι → ℝ)
    (ha : InSimplex a)
    (M : ℝ)
    (hM : ∀ i, v i ≤ M) :
    (∑ i, a i * v i) ≤ M := by
  exact weighted_average_le_max a v ha M hM

end PartB1
end Assignment7
