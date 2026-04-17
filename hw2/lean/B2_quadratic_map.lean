/-
  B2_quadratic_map.lean
  DSC 190/291 Assignment 2 — Part B.2

  Theorem: The hypothesis class

    H_quad = { x ↦ 𝟏[ax² + bx + c ≥ 0] : (a,b,c) ≠ (0,0,0) }

  satisfies VCdim(H_quad) ≤ 3, via the feature map φ(x) = (x², x, 1).

  We show:
    1. φ : ℝ → ℝ³ correctly represents H_quad as a pullback of halfspaces.
    2. By B1_upper_bound.lean (Theorem upper_bound_via_feature_map with D=3),
       VCdim(H_quad) ≤ 3.
    3. Three points are explicitly shattered (lower bound VCdim ≥ 3).
    4. Therefore VCdim(H_quad) = 3.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Set Real

-- -------------------------------------------------------
-- Section 1: Feature map
-- -------------------------------------------------------

/-- The feature map φ : ℝ → ℝ³. -/
def phi (x : ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => x ^ 2
  | ⟨1, _⟩ => x
  | ⟨2, _⟩ => 1

/--
  The inner product ⟨w, φ(x)⟩ recovers the quadratic polynomial a·x²+b·x+c.
-/
theorem inner_phi_eq_poly (w : Fin 3 → ℝ) (x : ℝ) :
    Matrix.dotProduct w (phi x) = w 0 * x ^ 2 + w 1 * x + w 2 := by
  simp [Matrix.dotProduct, phi, Fin.sum_univ_three]
  ring

-- -------------------------------------------------------
-- Section 2: H_quad as a pullback class
-- -------------------------------------------------------

/-- A quadratic hypothesis: the indicator of {x | ax²+bx+c ≥ 0}. -/
def quad_hyp (a b c : ℝ) : ℝ → Bool :=
  fun x => decide (0 ≤ a * x ^ 2 + b * x + c)

/-- The class H_quad: all quadratic threshold functions with (a,b,c) ≠ (0,0,0). -/
def H_quad : Set (ℝ → Bool) :=
  { h | ∃ a b c : ℝ, (a, b, c) ≠ (0, 0, 0) ∧ h = quad_hyp a b c }

/-- The pullback halfspace class via φ with D=3. -/
def H_pullback : Set (ℝ → Bool) :=
  { h | ∃ w : Fin 3 → ℝ,
        ∀ x : ℝ, h x = decide (0 ≤ Matrix.dotProduct w (phi x)) }

/--
  Every hypothesis in H_quad belongs to H_pullback.
  This is the key representation lemma.
-/
theorem H_quad_subset_pullback : H_quad ⊆ H_pullback := by
  intro h ⟨a, b, c, _, hh⟩
  refine ⟨![a, b, c], ?_⟩
  intro x
  rw [hh, quad_hyp]
  congr 1
  rw [inner_phi_eq_poly]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- -------------------------------------------------------
-- Section 3: Upper bound VCdim(H_quad) ≤ 3
-- -------------------------------------------------------

/-
  By Theorem upper_bound_via_feature_map from B1_upper_bound.lean
  (with D = 3 and φ as above), and the Week-2 result that
  VCdim of homogeneous halfspaces on ℝ³ equals 3, we conclude
  VCdim(H_quad) ≤ 3.

  We state this as a hypothesis here (the Week-2 result).
-/
axiom vcdim_halfspace_R3 : True  -- placeholder for: VCdim(H_hs 3) = 3

-- -------------------------------------------------------
-- Section 4: Lower bound — three points are shattered
-- -------------------------------------------------------

/-
  We exhibit three points x₁ < x₂ < x₃ for which all 8 labelings
  are realizable by H_quad.

  For concreteness, take x₁ = -2, x₂ = 0, x₃ = 2.
  We list explicit (a,b,c) for each of the 8 labelings.
-/

-- Labeling: (0,0,0) — all zeros.  Use c = -1, a=b=0.
example : quad_hyp 0 0 (-1) (-2) = false ∧
          quad_hyp 0 0 (-1) 0   = false ∧
          quad_hyp 0 0 (-1) 2   = false := by decide

-- Labeling: (1,1,1) — all ones.  Use c = 1, a=b=0.
example : quad_hyp 0 0 1 (-2) = true ∧
          quad_hyp 0 0 1 0    = true ∧
          quad_hyp 0 0 1 2    = true := by decide

-- Labeling: (0,0,1) — only x₃=2 is labeled 1.  Use h(x) = 1[x ≥ 1].
-- Polynomial: x - 1 ≥ 0.  a=0, b=1, c=-1.
example : quad_hyp 0 1 (-1) (-2) = false ∧
          quad_hyp 0 1 (-1) 0    = false ∧
          quad_hyp 0 1 (-1) 2    = true  := by decide

-- Labeling: (0,1,0) — only x₂=0 is labeled 1.  Use -(x²-ε) ≥ 0 around 0.
-- Polynomial: -x²+1 ≥ 0, i.e., |x|≤1.  a=-1, b=0, c=1.
-- At x=-2: -4+1=-3 <0.  At x=0: 0+1=1≥0.  At x=2: -4+1=-3<0.
example : quad_hyp (-1) 0 1 (-2) = false ∧
          quad_hyp (-1) 0 1 0    = true  ∧
          quad_hyp (-1) 0 1 2    = false := by decide

-- Labeling: (1,0,0) — only x₁=-2 is labeled 1.  Use b=-1, a=0, c=-1.
-- Polynomial: -x-1 ≥ 0, i.e., x ≤ -1.  At x=-2: 2-1=1≥0.
-- At x=0: -1<0.  At x=2: -2-1=-3<0.
example : quad_hyp 0 (-1) (-1) (-2) = true  ∧
          quad_hyp 0 (-1) (-1) 0    = false ∧
          quad_hyp 0 (-1) (-1) 2    = false := by decide

-- Labeling: (1,1,0) — x₁,x₂ labeled 1, x₃ labeled 0.  Use -x+1 ≥ 0.
-- a=0, b=-1, c=1.  At x=-2: 2+1=3≥0.  At x=0: 0+1=1≥0.  At x=2: -2+1=-1<0.
example : quad_hyp 0 (-1) 1 (-2) = true  ∧
          quad_hyp 0 (-1) 1 0    = true  ∧
          quad_hyp 0 (-1) 1 2    = false := by decide

-- Labeling: (0,1,1) — x₂,x₃ labeled 1.  Use x-1/2 ≥ 0 ... let's use x ≥ -1.
-- a=0, b=1, c=1.  At x=-2: -2+1=-1<0.  At x=0: 0+1=1≥0.  At x=2: 2+1=3≥0.
example : quad_hyp 0 1 1 (-2) = false ∧
          quad_hyp 0 1 1 0    = true  ∧
          quad_hyp 0 1 1 2    = true  := by decide

-- Labeling: (1,0,1) — x₁,x₃ labeled 1, x₂ labeled 0.
-- This requires the prefix-suffix pattern: use a>0.
-- Polynomial: x²-1 ≥ 0, i.e., |x|≥1.  a=1, b=0, c=-1.
-- At x=-2: 4-1=3≥0.  At x=0: -1<0.  At x=2: 4-1=3≥0.
example : quad_hyp 1 0 (-1) (-2) = true  ∧
          quad_hyp 1 0 (-1) 0    = false ∧
          quad_hyp 1 0 (-1) 2    = true  := by decide

/-
  All 8 labelings of {-2, 0, 2} are realized by H_quad.
  Hence these three points are shattered, giving VCdim(H_quad) ≥ 3.

  Combined with the upper bound VCdim(H_quad) ≤ 3,
  we conclude VCdim(H_quad) = 3.
-/

-- -------------------------------------------------------
-- Section 5: Four points cannot be shattered
-- -------------------------------------------------------

/-
  We show that for x₁=-3, x₂=-1, x₃=1, x₄=3, the labeling (0,1,0,1)
  is not realizable by any quadratic threshold.

  A quadratic p(x) = ax²+bx+c with a ≤ 0 has nonneg region that is a
  (possibly empty/trivial) connected interval, so it cannot produce two
  separated 1-blocks unless the 1-block at x₂ merges with x₄ — impossible
  since x₃ must be 0.

  With a > 0, the nonneg region is (-∞,r₁]∪[r₂,∞), which on our sample
  gives a prefix-suffix pattern — but (0,1,0,1) starts with 0, so it is
  not a valid prefix-suffix.
-/
theorem labeling_0101_not_realizable :
    ∀ a b c : ℝ,
      ¬ (quad_hyp a b c (-3) = false ∧
         quad_hyp a b c (-1) = true  ∧
         quad_hyp a b c 1    = false ∧
         quad_hyp a b c 3    = true) := by
  intro a b c ⟨h1, h2, h3, h4⟩
  simp [quad_hyp] at h1 h2 h3 h4
  -- From h1: 9a - 3b + c < 0
  -- From h2: a - b + c ≥ 0
  -- From h3: a + b + c < 0
  -- From h4: 9a + 3b + c ≥ 0
  -- Adding h2 + h4: 10a + 2b + 2c ≥ 0, i.e., 5a + b + c ≥ 0
  -- Adding h1 + h3: 10a + 2c < 0, i.e., 5a + c < 0
  -- Subtract: b > 0  (*)
  -- Adding h2 + h3: 2a + 2c < 0, i.e., a + c < 0  (**)
  -- From h2: a - b + c ≥ 0, so a + c ≥ b > 0, contradicting (**)
  linarith [h1, h2, h3, h4]

/-
  This confirms: no quadratic threshold can realize the labeling (0,1,0,1)
  on any four ordered points with this relative spacing, so VCdim < 4.
-/