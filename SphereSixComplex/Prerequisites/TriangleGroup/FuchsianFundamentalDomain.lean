module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianPingPong
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import all SphereSixComplex.Prerequisites.TriangleGroup.FuchsianAction

/-!
# A concrete fundamental triangle and cusp displacement

The reflection triangle for the `(3, 4, ∞)` action is bounded by the vertical geodesics
`Re z = -√2 / 2`, `Re z = 1 / 2`, and the unit semicircle.  This file records that region and
proves the exact displacement estimates for the parabolic product of the two elliptic generators.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

open SphereSixComplex.TriangleGroup
open scoped Pointwise

/-- Width of the parabolic translation obtained from the two elliptic generators. -/
@[expose] public noncomputable def cuspWidth : ℝ := 1 + Real.sqrt 2

public theorem cuspWidth_pos : 0 < cuspWidth := by
  unfold cuspWidth
  positivity

/-- The closed reflection triangle with elliptic vertices of orders three and four and ideal
vertex at infinity. -/
@[expose] public noncomputable def fundamentalTriangle : Set UpperHalfPlane :=
  {z | -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 ≤ Complex.normSq (z : ℂ)}

/-- The two finite vertices of the triangle lie on its unit-circle side. -/
public theorem fuchsianOneFixedPoint_mem_fundamentalTriangle :
    fuchsianOneFixedPoint ∈ fundamentalTriangle := by
  change -Real.sqrt 2 / 2 ≤ (1 : ℝ) / 2 ∧
    (1 : ℝ) / 2 ≤ 1 / 2 ∧
      1 ≤ Complex.normSq (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ)
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · linarith
  constructor
  · norm_num
  · norm_num [Complex.normSq_apply]
    nlinarith

public theorem fuchsianTwoFixedPoint_mem_fundamentalTriangle :
    fuchsianTwoFixedPoint ∈ fundamentalTriangle := by
  change -Real.sqrt 2 / 2 ≤ -Real.sqrt 2 / 2 ∧
    -Real.sqrt 2 / 2 ≤ (1 : ℝ) / 2 ∧
      1 ≤ Complex.normSq (⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ : ℂ)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rfl
  constructor
  · linarith
  · norm_num [Complex.normSq_apply]
    nlinarith






/-- The product `g₁g₂` is the positive cusp translation. -/
public theorem product_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ) = z + cuspWidth := by
  rw [map_mul, fuchsianSourceAction_g₁, fuchsianSourceAction_g₂]
  unfold cuspWidth
  push_cast
  exact fuchsianProductPerm_apply z

/-- Every positive power of the parabolic product has exact linear displacement. -/
public theorem product_pow_apply (n : ℕ) (z : UpperHalfPlane) :
    (((fuchsianSourceAction ((g₁ * g₂) ^ n)) z : UpperHalfPlane) : ℂ) =
      z + n * cuspWidth := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul]
      change (((fuchsianSourceAction ((g₁ * g₂) ^ n))
        (fuchsianSourceAction (g₁ * g₂) z) : UpperHalfPlane) : ℂ) = _
      rw [ih, product_apply]
      push_cast
      ring

/-- Every positive power of the cusp generator has exact negative linear displacement. -/
public theorem cusp_pow_apply (n : ℕ) (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₀ ^ n)) z : UpperHalfPlane) : ℂ) =
      z - n * cuspWidth := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul]
      change (((fuchsianSourceAction (g₀ ^ n))
        (fuchsianSourceAction g₀ z) : UpperHalfPlane) : ℂ) = _
      rw [ih, fuchsianSourceAction_g₀_apply]
      push_cast
      unfold cuspWidth
      push_cast
      ring










end SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
