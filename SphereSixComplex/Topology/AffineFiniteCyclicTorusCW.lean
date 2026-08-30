module

public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
public import SphereSixComplex.Topology.EstablishedCompactManifoldFiniteCW

/-!
# Finite CW type of affine finite-cyclic torus quotients

This file derives finite CW models for the reduced elliptic fibres.  Their explicit free cyclic
actions give surjective coverings from compact four-tori.  The compact-manifold finite-CW theorem
then supplies models with no cells above dimension four, and hence none above dimension six.
-/

open SphereSixComplex.Geometry SphereSixComplex.Periods
open scoped ContinuousMap

namespace SphereSixComplex.Topology.AffineFiniteCyclicTorusCW

open EstablishedCompactManifoldFiniteCW

open Geometry.ComplexTorus
open Geometry.AnalyticTorusFamily
open Geometry.EllipticLocalCoordinates
open Geometry.EllipticFamilySpecialization
open Geometry.EllipticFixedPointCriterion
open Geometry.EquivariantQuotientHomeomorph
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

/-- Finite-CW descent along a covering by a full-rank four-torus. -/
public noncomputable def finiteCWModelSix_of_fullRankTorusCover
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : Parameters) (hfull : FullRank p)
    (projection : C(AdditiveTorus p, X)) (hcover : IsCoveringMap projection)
    (hsurjective : Function.Surjective projection) :
    FiniteCWModelSix X := by
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p) := inferInstance
  let _ : CompactSpace (AdditiveTorus p) := torus_compactSpace p hfull
  exact (establishedFiniteCWModelFour_of_compactComplexSurfaceCover
    (torus_isManifold_and_projection_isLocalDiffeomorph p hfull 0).1
    (inferInstance : CompactSpace (AdditiveTorus p)) projection hcover
    hsurjective).toFiniteCWModelSix (by omega)

namespace RadialEllipticActionData

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T)

private abbrev centralFiberCoverSource :=
  {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
    D.reducedCentralFiber}

private def centralFiberCoverProjection :
    C(centralFiberCoverSource D, D.reducedCentralFiber) where
  toFun p := ⟨Quotient.mk _ p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quot_mk.comp continuous_subtype_val) _

private theorem mem_centralSlice_iff_quotient_mem_reducedCentralFiber (p : D.Product) :
    Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈ D.reducedCentralFiber ↔
      p ∈ D.centralSlice := by
  constructor
  · intro hp
    rw [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber] at hp
    obtain ⟨q, hq, heq⟩ := hp
    have horbit := Quotient.exact heq.symm
    change ∃ g : FiniteCyclic m,
      actionMap D.actionData.diagonalAction g q = p at horbit
    obtain ⟨g, rfl⟩ := horbit
    have h := congrArg Prod.fst (D.retract_equivariant g q)
    rw [D.retract_fixed q hq] at h
    change discCenter = (actionMap D.actionData.diagonalAction g q).1 at h
    change (actionMap D.actionData.diagonalAction g q).1 = discCenter
    exact h.symm
  · intro hp
    rw [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber]
    exact ⟨p, hp, rfl⟩

private def centralFiberCoverSourceOfTorus (x : T) : centralFiberCoverSource D :=
  ⟨(D.actionData.center, x), by
    apply (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D
      (D.actionData.center, x)).2
    exact D.center_eq⟩

private def centralFiberCoverSourceHomeomorph : centralFiberCoverSource D ≃ₜ T where
  toFun p := p.1.2
  invFun := centralFiberCoverSourceOfTorus D
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have hp := (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D p.1).1 p.2
      exact D.center_eq.trans hp.symm
    · rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (continuous_const.prodMk continuous_id) _

variable [T2Space D.Product] [LocallyCompactSpace D.Product]

private theorem centralFiberCoverProjection_isCovering
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product) :
    IsCoveringMap (centralFiberCoverProjection D) := by
  let action := D.actionData.diagonalAction
  let _ := action
  let _ : IsCancelSMul (FiniteCyclic m) D.Product := hfree
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic m) D.Product := inferInstance
  let hq : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product)) (FiniteCyclic m) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have hq' : IsQuotientCoveringMap
      (Quotient.mk (orbitRelOf D.actionData.diagonalAction) : D.Product → D.FillingQuotient)
      (FiniteCyclic m) := by
    change IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product)) (FiniteCyclic m)
    exact hq
  have h := hq'.isCoveringMap.restrictPreimage D.reducedCentralFiber
  let e : centralFiberCoverSource D ≃ₜ
      {p : D.Product | Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
        D.reducedCentralFiber} := Homeomorph.refl _
  have he := h.comp_homeomorph e
  convert he using 1
  ext
  rfl

private def torusCentralFiberProjection : C(T, D.reducedCentralFiber) :=
  (centralFiberCoverProjection D).comp
    { toFun := (centralFiberCoverSourceHomeomorph D).symm
      continuous_toFun := (centralFiberCoverSourceHomeomorph D).symm.continuous }

private theorem torusCentralFiberProjection_isCovering
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product) :
    IsCoveringMap (torusCentralFiberProjection D) := by
  have h := (centralFiberCoverProjection_isCovering D hfree).comp_homeomorph
    (centralFiberCoverSourceHomeomorph D).symm
  convert h using 1
  ext x
  rfl

omit [T2Space D.Product] [LocallyCompactSpace D.Product] in
private theorem torusCentralFiberProjection_surjective :
    Function.Surjective (torusCentralFiberProjection D) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp, rfl⟩ := hq
  refine ⟨p.2, ?_⟩
  apply Subtype.ext
  apply Quotient.sound
  change ∃ g : FiniteCyclic m,
    actionMap D.actionData.diagonalAction g p = (D.actionData.center, p.2)
  refine ⟨1, ?_⟩
  simp only [actionMap, one_smul]
  apply Prod.ext
  · exact hp.trans D.center_eq.symm
  · rfl

end RadialEllipticActionData

private noncomputable def finiteCWModelSix_reducedCentralFiber_of_freeAction
    {m : ℕ} [NeZero m] (p : Parameters) (hfull : FullRank p)
    (D : RadialEllipticActionData m (AdditiveTorus p))
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product) :
    FiniteCWModelSix D.reducedCentralFiber := by
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p) := inferInstance
  let _ : CompactSpace (AdditiveTorus p) := torus_compactSpace p hfull
  let _ : LocallyCompactSpace (AdditiveTorus p) := inferInstance
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  let _ := D.actionData.diagonalAction
  let _ : IsCancelSMul (FiniteCyclic m) D.Product := hfree
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic m) D.Product := inferInstance
  let _ : T2Space D.FillingQuotient := by
    change T2Space (Quotient (MulAction.orbitRel (FiniteCyclic m) D.Product))
    infer_instance
  let _ : T2Space D.reducedCentralFiber := inferInstance
  exact finiteCWModelSix_of_fullRankTorusCover p hfull
    (RadialEllipticActionData.torusCentralFiberProjection D)
    (RadialEllipticActionData.torusCentralFiberProjection_isCovering D hfree)
    (RadialEllipticActionData.torusCentralFiberProjection_surjective D)

/-- A finite CW model for the actual order-three reduced elliptic fibre. -/
public noncomputable def orderThreeReducedCentralFiberFiniteCWModelSixOfPeriodFunctions
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    FiniteCWModelSix (OrderThreeReducedCentralFiber F) := by
  let p := parameterMap F U.zOne
  exact finiteCWModelSix_reducedCentralFiber_of_freeAction p.1
    (FullRank.ofSetupInequalities p.1 p.2) (orderThreeRadialActionData F)
    (EllipticFixedPointCriterion.orderThreeAction_free F)

/-- A finite CW model for the actual order-four reduced elliptic fibre. -/
public noncomputable def orderFourReducedCentralFiberFiniteCWModelSixOfPeriodFunctions
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    FiniteCWModelSix (OrderFourReducedCentralFiber F) := by
  let p := parameterMap F U.zTwo
  exact finiteCWModelSix_reducedCentralFiber_of_freeAction p.1
    (FullRank.ofSetupInequalities p.1 p.2) (orderFourRadialActionData F)
    (EllipticFixedPointCriterion.orderFourAction_free F)

/-- The paper's two reduced-fibre models follow from their explicit torus coverings. -/
public theorem establishedEllipticReducedCentralFiberFiniteCWModels
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    Nonempty
      (FiniteCWModelSix (OrderThreeReducedCentralFiber F) ×
        FiniteCWModelSix (OrderFourReducedCentralFiber F)) :=
  ⟨orderThreeReducedCentralFiberFiniteCWModelSixOfPeriodFunctions F,
    orderFourReducedCentralFiberFiniteCWModelSixOfPeriodFunctions F⟩

variable (A : PaperAnalyticData)

/-- The order-three reduced central fibre follows from the single affine-quotient triangulation
input. -/
public noncomputable def orderThreeReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderThreeReducedCentralFiber A.periods) :=
  orderThreeReducedCentralFiberFiniteCWModelSixOfPeriodFunctions A.periods

/-- The order-four reduced central fibre follows from the same affine-quotient triangulation
input. -/
public noncomputable def orderFourReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderFourReducedCentralFiber A.periods) :=
  orderFourReducedCentralFiberFiniteCWModelSixOfPeriodFunctions A.periods

end

end SphereSixComplex.Topology.AffineFiniteCyclicTorusCW
