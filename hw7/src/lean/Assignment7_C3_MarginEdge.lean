/--
Assignment 7, Part C3: Weak learning edge and normalized margin.

This file formalizes the finite algebraic pieces:
  1. correlation = 1 - 2 * weighted_error,
  2. edge = correlation / 2,
  3. the minimax theorem is the external mathematical ingredient that turns
     the weak-learning game into the optimal normalized l1 margin.

The full minimax theorem is intentionally left as an axiom-like assumption,
because formalizing von Neumann minimax from scratch is far beyond the scope
of the assignment. The assignment proof can cite minimax in the write-up.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open BigOperators

namespace Assignment7
namespace PartC3

variable {ι γ : Type} [Fintype ι] [Fintype γ]

/-- A distribution over a finite type. -/
def IsDistribution (D : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ D i) ∧ (∑ i, D i = 1)

/-- In the sign matrix, `A i g = 1` means base predictor `g` is correct on example `i`,
and `A i g = -1` means it is incorrect. -/
def IsSignMatrix (A : ι → γ → ℝ) : Prop :=
  ∀ i g, A i g = 1 ∨ A i g = -1

/-- Weighted correlation of a column. -/
def corr (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ) : ℝ :=
  ∑ i, D i * A i g

/-- Weighted error written using the sign matrix.
If `A i g = -1`, then predictor `g` is wrong on example `i`. -/
def weightedError (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ) : ℝ :=
  ∑ i, D i * (if A i g = -1 then 1 else 0)

/-- Weak-learning edge. -/
def edge (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ) : ℝ :=
  (1 / 2 : ℝ) - weightedError D A g

/-- Pointwise identity: for a sign value `a ∈ {-1,1}`, the mistake indicator equals `(1-a)/2`. -/
theorem mistake_indicator_eq_half_one_sub
    {a : ℝ}
    (ha : a = 1 ∨ a = -1) :
    (if a = -1 then 1 else 0) = (1 - a) / 2 := by
  rcases ha with h | h
  · simp [h]
  · simp [h]

/-- Weighted error equals `(1 - correlation)/2` when `D` is a distribution. -/
theorem weightedError_eq_half_one_sub_corr
    (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ)
    (hD : IsDistribution D)
    (hA : IsSignMatrix A) :
    weightedError D A g = (1 - corr D A g) / 2 := by
  unfold weightedError corr
  have hpoint : ∀ i, (if A i g = -1 then 1 else 0) = (1 - A i g) / 2 := by
    intro i
    exact mistake_indicator_eq_half_one_sub (hA i g)
  calc
    ∑ i, D i * (if A i g = -1 then 1 else 0)
        = ∑ i, D i * ((1 - A i g) / 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hpoint i]
    _ = (∑ i, D i * (1 - A i g)) / 2 := by
            rw [← Finset.sum_div]
            congr
            ext i
            ring
    _ = ((∑ i, D i) - (∑ i, D i * A i g)) / 2 := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (1 - ∑ i, D i * A i g) / 2 := by
            rw [hD.2]

/-- Edge equals correlation divided by 2. -/
theorem edge_eq_corr_div_two
    (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ)
    (hD : IsDistribution D)
    (hA : IsSignMatrix A) :
    edge D A g = corr D A g / 2 := by
  unfold edge
  rw [weightedError_eq_half_one_sub_corr D A g hD hA]
  ring

/-- Linear payoff for a mixed base predictor `p`. -/
def payoff (D : ι → ℝ) (A : ι → γ → ℝ) (p : γ → ℝ) : ℝ :=
  ∑ i, D i * (∑ g, A i g * p g)

/-- Distribution over base predictors. -/
def IsBaseDistribution (p : γ → ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ (∑ g, p g = 1)

/-- External minimax ingredient.

In the paper proof, this is exactly where von Neumann's minimax theorem is used:

  max_p min_D payoff(D,A,p) = min_D max_p payoff(D,A,p).

A full mathlib-level formalization would require compact convex sets and continuity.
For this assignment, cite minimax in the written proof and use this file for the
finite algebraic edge/correlation identities.
-/
axiom von_neumann_minimax_finite
    (A : ι → γ → ℝ) :
    True

/-- Written-theorem placeholder.

The final mathematical claim proved in the write-up is:

  best_normalized_l1_margin = 2 * best_weak_learning_edge.

This Lean file verifies the important factor-of-two identity that usually causes mistakes:

  edge(D,g) = corr(D,g) / 2.
-/
theorem factor_two_identity
    (D : ι → ℝ) (A : ι → γ → ℝ) (g : γ)
    (hD : IsDistribution D)
    (hA : IsSignMatrix A) :
    2 * edge D A g = corr D A g := by
  rw [edge_eq_corr_div_two D A g hD hA]
  ring

end PartC3
end Assignment7
