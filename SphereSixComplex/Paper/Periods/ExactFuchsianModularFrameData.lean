module

public import SphereSixComplex.Paper.Periods.FuchsianPeriodAssembly
public import SphereSixComplex.Paper.Periods.ExactFuchsianCuspBounds

/-!
# Exact lifted modular frame data

This module records the public interface of the lifted `O(-1)` modular frame.  Its genuine
construction from the established uniformization is kept in a separate module so the analytic
ramification, square-root, and completed-cusp arguments can be checked independently.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup
open Filter Metric

/-- Pullback of the normalized weight-four Eisenstein series by the established modular
parameter. -/
@[expose] public def liftedEisensteinFour
    (E : NormalizedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ (E.modularParameter.tau z)

/-- Pullback of the normalized weight-six Eisenstein series by the established modular
parameter. -/
@[expose] public def liftedEisensteinSix
    (E : NormalizedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₆ (E.modularParameter.tau z)

/-- Pullback of the modular discriminant by the established modular parameter. -/
@[expose] public def liftedModularDiscriminant
    (E : NormalizedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.discriminant (E.modularParameter.tau z)

/-- The weight-minus-one modular expression associated to a chosen square root of `E₆`. -/
@[expose] public def modularNegOneFrame
    (E : NormalizedFuchsianModularParameter) (root : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ℂ :=
  liftedEisensteinFour E z ^ 2 * root z / liftedModularDiscriminant E z

/-- Exact classical modular-form data used in Lemma 3.10 of the paper.

The square root is included together with its square identity and exact divisor data.  The final
cusp identity says, as a germ at infinity, that `coordinate⁻¹ * frame` extends as a holomorphic
unit in the completed cusp coordinate. -/
public structure ExactLiftedModularNegOneFrame
    (E : NormalizedFuchsianModularParameter) where
  /-- The chosen holomorphic square root of the pulled-back weight-six Eisenstein series. -/
  sqrtEisensteinSix : UpperHalfPlane → ℂ
  /-- Holomorphicity of the chosen square root. -/
  sqrtEisensteinSix_holomorphic : MDiff sqrtEisensteinSix
  /-- The chosen function really is a square root. -/
  sqrtEisensteinSix_sq : ∀ z,
    sqrtEisensteinSix z ^ 2 = liftedEisensteinSix E z
  /-- Holomorphicity of the pulled-back frame. -/
  frame_holomorphic : MDiff (modularNegOneFrame E sqrtEisensteinSix)
  /-- Exact order-two zero over the order-three orbifold point. -/
  frame_branch_one :
    HasExactHolomorphicBranchAt (modularNegOneFrame E sqrtEisensteinSix) fuchsianOneFixedPoint 0 2
  /-- Exact order-one zero over the order-four orbifold point. -/
  frame_branch_two :
    HasExactHolomorphicBranchAt (modularNegOneFrame E sqrtEisensteinSix) fuchsianTwoFixedPoint 0 1
  /-- There are no further zeros. -/
  frame_zero_iff : ∀ z, modularNegOneFrame E sqrtEisensteinSix z = 0 ↔
    (∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z) ∨
      ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z
  /-- The order-three homogeneous automorphy factor. -/
  frame_one : ∀ z, modularNegOneFrame E sqrtEisensteinSix (fuchsianSourceAction g₁ • z) =
    -modularNegOneFrame E sqrtEisensteinSix z / E.modularParameter.tau z
  /-- The order-four homogeneous automorphy factor. -/
  frame_two : ∀ z, modularNegOneFrame E sqrtEisensteinSix (fuchsianSourceAction g₂ • z) =
    modularNegOneFrame E sqrtEisensteinSix z / E.modularParameter.tau z
  /-- The holomorphic unit after removing the simple pole at the completed cusp. -/
  cuspUnit : ℂ → ℂ
  /-- Radius of a completed cusp-coordinate neighbourhood. -/
  cuspRadius : ℝ
  /-- The completed cusp-coordinate neighbourhood is nontrivial. -/
  cuspRadius_pos : 0 < cuspRadius
  /-- The cusp unit is holomorphic on a neighbourhood of zero. -/
  cuspUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspRadius → MDiffAt cuspUnit q
  /-- The cusp unit is nonzero at the completed point. -/
  cuspUnit_zero_ne : cuspUnit 0 ≠ 0
  /-- Sufficiently far into the cusp, the reciprocal quotient coordinate lies in a compact
  subdisc of the unit's analytic domain. -/
  inverse_coordinate_eventually_mem_closedBall :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      (E.sourceCoordinate.coordinate z)⁻¹ ∈ Metric.closedBall 0 (cuspRadius / 2)
  /-- Exact simple-pole normalization as a germ at the completed cusp. -/
  cusp_factorization_eventually : ∀ᶠ z in upperHalfPlaneAtInfinity,
    (E.sourceCoordinate.coordinate z)⁻¹ * modularNegOneFrame E sqrtEisensteinSix z =
      cuspUnit ((E.sourceCoordinate.coordinate z)⁻¹)

/-- The modular frame is determined by the chosen square root. -/
@[expose] public def ExactLiftedModularNegOneFrame.frame
    {E : NormalizedFuchsianModularParameter} (F : ExactLiftedModularNegOneFrame E) :
    UpperHalfPlane → ℂ := modularNegOneFrame E F.sqrtEisensteinSix

end SphereSixComplex.Periods
