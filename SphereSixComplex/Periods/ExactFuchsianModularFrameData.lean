module

public import SphereSixComplex.Periods.FuchsianPeriodAssembly
public import SphereSixComplex.Periods.ExactFuchsianCuspBounds

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
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ (E.modularParameter.tau z)

/-- Pullback of the normalized weight-six Eisenstein series by the established modular
parameter. -/
@[expose] public def liftedEisensteinSix
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₆ (E.modularParameter.tau z)

/-- Pullback of the modular discriminant by the established modular parameter. -/
@[expose] public def liftedModularDiscriminant
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) : ℂ :=
  ModularForm.discriminant (E.modularParameter.tau z)

/-- Exact classical modular-form data used in Lemma 3.10 of the paper.

The square root is included together with its square identity and exact divisor data.  The final
cusp identity says, as a germ at infinity, that `coordinate⁻¹ * frame` extends as a holomorphic
unit in the completed cusp coordinate. -/
public structure ExactLiftedModularNegOneFrame
    (E : EstablishedFuchsianModularParameter) where
  /-- The chosen holomorphic square root of the pulled-back weight-six Eisenstein series. -/
  sqrtEisensteinSix : UpperHalfPlane → ℂ
  /-- Holomorphicity of the chosen square root. -/
  sqrtEisensteinSix_holomorphic : MDiff sqrtEisensteinSix
  /-- The chosen function really is a square root. -/
  sqrtEisensteinSix_sq : ∀ z,
    sqrtEisensteinSix z ^ 2 = liftedEisensteinSix E z
  /-- The meromorphic modular expression, holomorphic on the source because the discriminant
  never vanishes there. -/
  frame : UpperHalfPlane → ℂ
  /-- Identification with the normalized modular-form expression. -/
  frame_eq : ∀ z,
    frame z = liftedEisensteinFour E z ^ 2 * sqrtEisensteinSix z /
      liftedModularDiscriminant E z
  /-- Holomorphicity of the pulled-back frame. -/
  frame_holomorphic : MDiff frame
  /-- Exact order-two zero over the order-three orbifold point. -/
  frame_branch_one : HasExactHolomorphicBranchAt frame fuchsianOneFixedPoint 0 2
  /-- Exact order-one zero over the order-four orbifold point. -/
  frame_branch_two : HasExactHolomorphicBranchAt frame fuchsianTwoFixedPoint 0 1
  /-- There are no further zeros. -/
  frame_zero_iff : ∀ z, frame z = 0 ↔
    (∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z) ∨
      ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z
  /-- The order-three homogeneous automorphy factor. -/
  frame_one : ∀ z, frame (fuchsianSourceAction g₁ • z) =
    -frame z / E.modularParameter.tau z
  /-- The order-four homogeneous automorphy factor. -/
  frame_two : ∀ z, frame (fuchsianSourceAction g₂ • z) =
    frame z / E.modularParameter.tau z
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
    (E.sourceCoordinate.coordinate z)⁻¹ * frame z =
      cuspUnit ((E.sourceCoordinate.coordinate z)⁻¹)

end SphereSixComplex.Periods
