module

public import SphereSixComplex.Topology.EquivariantHomotopyEquivalenceDescent
public import SphereSixComplex.Topology.PuncturedAffineHalfPlaneRadial

/-!
# Equivariant radial-domain descent

The radial equivalence between nested punctured domains can be lifted across an unchanged fibre
and then descended through a diagonal group action.  The quotient is never identified with a
product: its monodromy remains part of the orbit relation.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.EquivariantQuotientHomeomorph

namespace ComplexRadialDomain

variable {X Y : Set ℂ} {radius : ℝ}

/-- Radial homotopy on the smaller domain, with endpoints written as the composite of
normalization after inclusion and the identity. -/
public def smallerCompositeHomotopy
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius)
    (hXY : X ⊆ Y) :
    ContinuousMap.Homotopy
      ((small.normalizeTo big).comp (inclusion hXY)) (ContinuousMap.id X) where
  toFun := small.radialHomotopyFunction
  continuous_toFun := small.continuous_radialHomotopyFunction
  map_zero_left x := by
    apply Subtype.ext
    change ((0 : ℝ) + (1 - (0 : ℝ)) * radius * ‖x.1‖⁻¹) • x.1 =
      (radius * ‖x.1‖⁻¹) • x.1
    congr 1
    ring
  map_one_left := small.radialHomotopyFunction_one

/-- Radial homotopy on the larger domain, with endpoints written as inclusion after
normalization and the identity. -/
public def largerCompositeHomotopy
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius)
    (hXY : X ⊆ Y) :
    ContinuousMap.Homotopy
      ((inclusion hXY).comp (small.normalizeTo big)) (ContinuousMap.id Y) where
  toFun := big.radialHomotopyFunction
  continuous_toFun := big.continuous_radialHomotopyFunction
  map_zero_left y := by
    apply Subtype.ext
    change ((0 : ℝ) + (1 - (0 : ℝ)) * radius * ‖y.1‖⁻¹) • y.1 =
      (radius * ‖y.1‖⁻¹) • y.1
    congr 1
    ring
  map_one_left := big.radialHomotopyFunction_one

end ComplexRadialDomain

universe u

variable {G : Type*} [Group G]
variable {X Y : Set ℂ} {radius : ℝ}

/-- The exact equivariance hypotheses for a nested radial-domain inclusion.  Keeping both
restricted actions explicit permits applications in which the domains are invariant lifts of
regions in a quotient coordinate. -/
public structure EquivariantRadialDomainInclusionData
    (G : Type*) [Group G]
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius)
    (hXY : X ⊆ Y) where
  smallAction : MulAction G X
  bigAction : MulAction G Y
  inclusion_equivariant : ∀ (g : G) (x : X),
    ComplexRadialDomain.inclusion hXY (actionMap smallAction g x) =
      actionMap bigAction g (ComplexRadialDomain.inclusion hXY x)
  normalization_equivariant : ∀ (g : G) (y : Y),
    small.normalizeTo big (actionMap bigAction g y) =
      actionMap smallAction g (small.normalizeTo big y)
  smallerHomotopy_equivariant : ∀ (g : G) (t : unitInterval) (x : X),
    small.smallerCompositeHomotopy big hXY (t, actionMap smallAction g x) =
      actionMap smallAction g (small.smallerCompositeHomotopy big hXY (t, x))
  largerHomotopy_equivariant : ∀ (g : G) (t : unitInterval) (y : Y),
    small.largerCompositeHomotopy big hXY (t, actionMap bigAction g y) =
      actionMap bigAction g (small.largerCompositeHomotopy big hXY (t, y))

namespace EquivariantRadialDomainInclusionData

variable {small : ComplexRadialDomain X radius} {big : ComplexRadialDomain Y radius}
    {hXY : X ⊆ Y} (R : EquivariantRadialDomainInclusionData G small big hXY)

/-- A nested equivariant radial-domain inclusion is an equivariant homotopy equivalence before
passing to quotients. -/
public def toEquivariantHomotopyEquivData :
    EquivariantHomotopyEquivData R.smallAction R.bigAction where
  toFun := ComplexRadialDomain.inclusion hXY
  invFun := small.normalizeTo big
  toFun_equivariant := R.inclusion_equivariant
  invFun_equivariant := R.normalization_equivariant
  leftInvHomotopy := small.smallerCompositeHomotopy big hXY
  rightInvHomotopy := small.largerCompositeHomotopy big hXY
  leftInvHomotopy_equivariant := R.smallerHomotopy_equivariant
  rightInvHomotopy_equivariant := R.largerHomotopy_equivariant

/-- The literal radial inclusion descends to a homotopy equivalence of orbit quotients. -/
public theorem quotientInclusion_isHomotopyEquivalence
    (smallContinuous : letI := R.smallAction; ContinuousConstSMul G X)
    (bigContinuous : letI := R.bigAction; ContinuousConstSMul G Y) :
    IsHomotopyEquivalence R.toEquivariantHomotopyEquivData.quotientToFun :=
  R.toEquivariantHomotopyEquivData.quotientToFun_isHomotopyEquivalence
    smallContinuous bigContinuous

/-- After adjoining any equivariant fibre, the diagonal quotient of the radial inclusion is a
homotopy equivalence.  This is the monodromy-preserving replacement for a global product
trivialization. -/
public theorem productQuotientInclusion_isHomotopyEquivalence
    {Z : Type u} [TopologicalSpace Z] (fiberAction : MulAction G Z)
    (smallContinuous : letI := R.smallAction; ContinuousConstSMul G X)
    (bigContinuous : letI := R.bigAction; ContinuousConstSMul G Y)
    (fiberContinuous : letI := fiberAction; ContinuousConstSMul G Z) :
    IsHomotopyEquivalence
      (R.toEquivariantHomotopyEquivData.prodRightId fiberAction).quotientToFun := by
  apply EquivariantHomotopyEquivData.quotientToFun_isHomotopyEquivalence
  · exact explicitProductAction_continuous R.smallAction fiberAction
      smallContinuous fiberContinuous
  · exact explicitProductAction_continuous R.bigAction fiberAction
      bigContinuous fiberContinuous

end EquivariantRadialDomainInclusionData

end SphereSixComplex
