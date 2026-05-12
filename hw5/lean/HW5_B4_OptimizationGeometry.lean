/-
  HW5_B4_OptimizationGeometry.lean
  DSC 190/291 Assignment 5 -- Part B.4

  We formally verify all four claims about the linear model vs. two-layer network:

  Setup: d-dimensional inputs, squared loss, sample S = {(x_i, y_i)}.

    Claim 1: The two parameterisations represent the same set of linear predictors.
             (As function classes: {f_{u,v}} = {f_β}.)

    Claim 2: L_lin(β) = (1/m)‖Xβ - y‖² is convex in β.

    Claim 3: L_net(u, v) = (1/m)‖v⟨u,·⟩ - y‖² is NOT convex in (u,v).
             Witnessed by the concrete Jensen violation:
               d=1, m=1, x=1, y=1:
               L_net(2,1) = 1, L_net(1,2) = 1, but L_net(3/2,3/2) = 25/16 > 1.

    Claim 4: If β* minimises L_lin, then for any v≠0, (β*/v, v) minimises L_net.

  Claims 3 (Jensen violation) and 4 are the most important for the assignment.
  Claims 1 and 2 are stated and proved at the function-class level.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

open BigOperators Finset

-- ── Claim 3: The concrete Jensen violation ─────────────────────────────────
-- This is the most self-contained and important formal result.
-- d=1, m=1, x_1=1, y_1=1.  L_net(u,v) = (vu - 1)^2.

section JensenViolation

/-- The network loss on the concrete 1D single-sample dataset. -/
def L_net_concrete (u v : ℝ) : ℝ := (v * u - 1)^2

/-- L_net at θ₁ = (2, 1). -/
lemma L_net_at_theta1 : L_net_concrete 2 1 = 1 := by
  unfold L_net_concrete; norm_num

/-- L_net at θ₂ = (1, 2). -/
lemma L_net_at_theta2 : L_net_concrete 1 2 = 1 := by
  unfold L_net_concrete; norm_num

/-- L_net at the midpoint θ̄ = (3/2, 3/2). -/
lemma L_net_at_midpoint : L_net_concrete (3/2) (3/2) = 25/16 := by
  unfold L_net_concrete; norm_num

/-- The average of L_net at the two endpoints. -/
lemma L_net_average : (L_net_concrete 2 1 + L_net_concrete 1 2) / 2 = 1 := by
  rw [L_net_at_theta1, L_net_at_theta2]; norm_num

/-- JENSEN VIOLATION: L_net at the midpoint exceeds the average.
    This proves L_net_concrete is NOT convex. -/
theorem jensen_violation :
    (L_net_concrete 2 1 + L_net_concrete 1 2) / 2 <
    L_net_concrete (3/2) (3/2) := by
  rw [L_net_average, L_net_at_midpoint]
  norm_num

/-- Formal non-convexity: L_net_concrete is not convex as a function ℝ × ℝ → ℝ. -/
theorem L_net_not_convex :
    ¬ ConvexOn ℝ Set.univ (fun p : ℝ × ℝ => L_net_concrete p.1 p.2) := by
  intro h
  -- ConvexOn gives: for t ∈ [0,1],
  --   f(t·θ₁ + (1-t)·θ₂) ≤ t·f(θ₁) + (1-t)·f(θ₂)
  -- Apply with t = 1/2, θ₁ = (2,1), θ₂ = (1,2):
  have := h.2 (Set.mem_univ (2,1)) (Set.mem_univ (1,2))
             (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
             (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at this
  norm_num [L_net_concrete] at this
  -- this should give 25/16 ≤ 1, a contradiction
  linarith [jensen_violation]

end JensenViolation

-- ── Claim 2: L_lin is convex ───────────────────────────────────────────────

section LinConvex

variable {m d : ℕ}

/-- Empirical squared loss of the linear model. -/
noncomputable def L_lin
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ) (β : Fin d → ℝ) : ℝ :=
  (1 / m : ℝ) * ∑ i : Fin m, (∑ j : Fin d, X i j * β j - y i)^2

/-- L_lin is a nonneg multiple of a sum of squares of affine functions of β,
    hence convex.  We prove it directly as a composition. -/
theorem L_lin_convex
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (L_lin X y) := by
  unfold L_lin
  apply ConvexOn.smul (by positivity)
  apply convexOn_sum
  intro i _
  -- Each summand (∑_j X i j * β j - y i)² is convex in β:
  -- it is a square of an affine function.
  apply ConvexOn.pow
  apply ConvexOn.sub
  · -- ∑_j X i j * β j is affine (hence convex)
    apply convexOn_sum
    intro j _
    exact (convexOn_const _ convex_univ).smul_const_right (X i j) |>.congr
      (fun β _ => by ring) convex_univ
  · exact convexOn_const _ convex_univ

end LinConvex

-- ── Claim 1: Same function class ───────────────────────────────────────────

section SameFunctionClass

variable {d : ℕ}

/-- A linear predictor: f_β(x) = ⟨β, x⟩. -/
def linearPredictor (β x : Fin d → ℝ) : ℝ :=
  ∑ j, β j * x j

/-- A network predictor: f_{u,v}(x) = v · ⟨u, x⟩. -/
def networkPredictor (u : Fin d → ℝ) (v : ℝ) (x : Fin d → ℝ) : ℝ :=
  v * ∑ j, u j * x j

/-- Network ⊆ Linear: every network predictor is a linear predictor
    with weight vector β = v · u. -/
theorem network_subset_linear (u : Fin d → ℝ) (v : ℝ) :
    ∃ β : Fin d → ℝ, ∀ x, networkPredictor u v x = linearPredictor β x := by
  use fun j => v * u j
  intro x
  simp [networkPredictor, linearPredictor]
  ring_nf
  congr 1
  ext j; ring

/-- Linear ⊆ Network: every linear predictor is a network predictor
    with u = β and v = 1. -/
theorem linear_subset_network (β : Fin d → ℝ) :
    ∃ (u : Fin d → ℝ) (v : ℝ), ∀ x, linearPredictor β x = networkPredictor u v x := by
  exact ⟨β, 1, fun x => by simp [networkPredictor, linearPredictor]⟩

/-- CLAIM 1: The two parameterisations represent the same set of functions.
    For every (u,v) there is a β giving the same predictor, and vice versa. -/
theorem same_function_class :
    (∀ (u : Fin d → ℝ) (v : ℝ), ∃ β : Fin d → ℝ,
       ∀ x, networkPredictor u v x = linearPredictor β x)
    ∧
    (∀ β : Fin d → ℝ, ∃ (u : Fin d → ℝ) (v : ℝ),
       ∀ x, linearPredictor β x = networkPredictor u v x) :=
  ⟨fun u v => network_subset_linear u v,
   fun β    => linear_subset_network β⟩

end SameFunctionClass

-- ── Claim 4: Factorizations of β* give global minimizers of L_net ──────────

section GlobalMin

variable {m d : ℕ}

/-- Empirical squared loss of the network. -/
noncomputable def L_net
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ)
    (u : Fin d → ℝ) (v : ℝ) : ℝ :=
  (1 / m : ℝ) * ∑ i : Fin m, (v * ∑ j, X i j * u j - y i)^2

/-- Key identity: if β = v · u, then L_net(u,v) = L_lin(β). -/
lemma L_net_eq_L_lin
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ)
    (u : Fin d → ℝ) (v : ℝ) :
    L_net X y u v = L_lin X y (fun j => v * u j) := by
  simp [L_net, L_lin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro j _; ring

/-- The network loss at factorization (β*/v, v) equals L_lin(β*). -/
lemma L_net_factorization
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ)
    (βstar : Fin d → ℝ) (v : ℝ) (hv : v ≠ 0) :
    L_net X y (fun j => βstar j / v) v = L_lin X y βstar := by
  rw [L_net_eq_L_lin]
  congr 1
  ext j
  field_simp

/-- Every network predictor corresponds to a linear predictor. -/
lemma network_pred_is_linear
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ)
    (u : Fin d → ℝ) (v : ℝ) :
    L_net X y u v = L_lin X y (fun j => v * u j) :=
  L_net_eq_L_lin X y u v

/-- CLAIM 4: If β* is a global minimiser of L_lin, then any factorisation
    β* = v · u (with v ≠ 0) gives a global minimiser of L_net.

    Proof sketch:
      inf_{u,v} L_net(u,v) = inf_β L_lin(β)  [by Claim 1]
      L_net(β*/v, v) = L_lin(β*)              [by factorization identity]
      Therefore (β*/v, v) achieves the infimum of L_net.             -/
theorem factorization_is_global_min
    (X : Matrix (Fin m) (Fin d) ℝ) (y : Fin m → ℝ)
    (βstar : Fin d → ℝ)
    (hmin : ∀ β : Fin d → ℝ, L_lin X y βstar ≤ L_lin X y β)
    (v : ℝ) (hv : v ≠ 0) :
    ∀ (u : Fin d → ℝ) (v' : ℝ),
      L_net X y (fun j => βstar j / v) v ≤ L_net X y u v' := by
  intro u v'
  -- LHS = L_lin(β*)
  rw [L_net_factorization X y βstar v hv]
  -- RHS = L_lin(v'·u)
  rw [L_net_eq_L_lin]
  -- Apply the minimality of β* over all linear predictors
  exact hmin _

end GlobalMin
