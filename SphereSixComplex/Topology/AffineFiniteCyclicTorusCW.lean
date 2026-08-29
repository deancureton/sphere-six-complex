module

public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Finite CW type of affine finite-cyclic torus quotients

This file isolates the classical triangulation input for the reduced elliptic fibres.  A free
finite cyclic action on a full-rank four-torus whose generator lifts to an affine automorphism of
the covering vector space has a compact smooth four-manifold quotient.  Smooth triangulation
therefore supplies a finite CW model, with no cells above dimension four (and hence above six).
-/

open SphereSixComplex.Geometry SphereSixComplex.Periods

namespace SphereSixComplex.Topology.AffineFiniteCyclicTorusCW

open Geometry.ComplexTorus
open Geometry.AnalyticTorusFamily
open Geometry.EllipticFamilySpecialization
open Geometry.EllipticFixedPointCriterion
open Geometry.GlobalTorusFamily LatticeData TriangleGroup
open PaperEllipticFillingRadialRetraction

noncomputable section

/-- The two cyclic orders that occur in the elliptic central-fibre calculation. -/
public inductive AffineFiniteCyclicOrder : ℕ → Type
  | orderThree : AffineFiniteCyclicOrder 3
  | orderFour : AffineFiniteCyclicOrder 4

/-- An inferred certificate restricting the affine quotient construction to order three or
order four. -/
public class SupportedAffineFiniteCyclicOrder (m : ℕ) where
  order : AffineFiniteCyclicOrder m

public instance : SupportedAffineFiniteCyclicOrder 3 := ⟨.orderThree⟩
public instance : SupportedAffineFiniteCyclicOrder 4 := ⟨.orderFour⟩

/-- The classical smooth-triangulation input, restricted exactly to the order-three and
order-four affine torus quotients used in this development. -/
public structure OrderThreeFourAffineGeneratorFiniteCWModels where
  orderThree :
    ∀ (p : Parameters) (_hfull : FullRank p)
      (D : RadialEllipticActionData 3 (AdditiveTorus p))
      (lift : ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace) (translation : ComplexTwoSpace)
      (_generator_mk : ∀ z,
        D.actionData.fiberGenerator (Quotient.mk _ z) =
          Quotient.mk _ (lift z + translation))
      (_hfree : letI := D.actionData.diagonalAction
        IsCancelSMul (FiniteCyclic 3) D.Product),
      FiniteCWModelSix D.reducedCentralFiber
  orderFour :
    ∀ (p : Parameters) (_hfull : FullRank p)
      (D : RadialEllipticActionData 4 (AdditiveTorus p))
      (lift : ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace) (translation : ComplexTwoSpace)
      (_generator_mk : ∀ z,
        D.actionData.fiberGenerator (Quotient.mk _ z) =
          Quotient.mk _ (lift z + translation))
      (_hfree : letI := D.actionData.diagonalAction
        IsCancelSMul (FiniteCyclic 4) D.Product),
      FiniteCWModelSix D.reducedCentralFiber

/-- Smooth triangulation for the two actual finite cyclic orders.  This is the sole residual
input in the module. -/
public axiom orderThreeFourAffineGeneratorFiniteCWModels :
    OrderThreeFourAffineGeneratorFiniteCWModels

/-- A common wrapper for the two supported cyclic orders.  The order certificate is inferred at
all current call sites, while the classical residual itself is stated only for orders three and
four. -/
public noncomputable def finiteCWModelSix_reducedCentralFiber_of_affineGenerator
    {m : ℕ} [NeZero m] [SupportedAffineFiniteCyclicOrder m]
    (p : Parameters) (hfull : FullRank p)
    (D : RadialEllipticActionData m (AdditiveTorus p))
    (lift : ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace) (translation : ComplexTwoSpace)
    (generator_mk : ∀ z,
      D.actionData.fiberGenerator (Quotient.mk _ z) =
        Quotient.mk _ (lift z + translation))
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product) :
    FiniteCWModelSix D.reducedCentralFiber := by
  cases SupportedAffineFiniteCyclicOrder.order (m := m) with
  | orderThree =>
      exact orderThreeFourAffineGeneratorFiniteCWModels.orderThree
        p hfull D lift translation generator_mk hfree
  | orderFour =>
      exact orderThreeFourAffineGeneratorFiniteCWModels.orderFour
        p hfull D lift translation generator_mk hfree

variable (A : PaperAnalyticData)

/-- The order-three reduced central fibre follows from the single affine-quotient triangulation
input. -/
public noncomputable def orderThreeReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderThreeReducedCentralFiber A.periods) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  let D := orderThreeRadialActionData A.periods
  apply finiteCWModelSix_reducedCentralFiber_of_affineGenerator p.1
    (FullRank.ofSetupInequalities p.1 p.2) D
    (periodTransport g₁ p) ((3 : ℂ)⁻¹ • periodVector p.1 epsilon)
  · intro z
    change affineEquiv (orderThreeFiberAutomorphism A.periods)
        (orderThreeTranslation p.1) (Quotient.mk _ z) = _
    rw [affineEquiv_apply, orderThreeFiberAutomorphism_mk]
    change Quotient.mk _ (periodTransport g₁ p z) +
        additiveTorusProjection p.1 ((3 : ℂ)⁻¹ • periodVector p.1 epsilon) = _
    exact (additiveTorusProjection_add p.1 _ _).symm
  · exact A.orderThreeAction_free

/-- The order-four reduced central fibre follows from the same affine-quotient triangulation
input. -/
public noncomputable def orderFourReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderFourReducedCentralFiber A.periods) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  let D := orderFourRadialActionData A.periods
  apply finiteCWModelSix_reducedCentralFiber_of_affineGenerator p.1
    (FullRank.ofSetupInequalities p.1 p.2) D
    (periodTransport g₂ p) ((4 : ℂ)⁻¹ • periodVector p.1 (-epsilon'))
  · intro z
    change affineEquiv (orderFourFiberAutomorphism A.periods)
        (orderFourTranslation p.1) (Quotient.mk _ z) = _
    rw [affineEquiv_apply, orderFourFiberAutomorphism_mk]
    change Quotient.mk _ (periodTransport g₂ p z) +
        additiveTorusProjection p.1 ((4 : ℂ)⁻¹ • periodVector p.1 (-epsilon')) = _
    exact (additiveTorusProjection_add p.1 _ _).symm
  · exact A.orderFourAction_free

end

end SphereSixComplex.Topology.AffineFiniteCyclicTorusCW
