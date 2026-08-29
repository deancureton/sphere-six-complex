module

public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Finite-cover models of the reduced elliptic central fibres

The reduced central fibres are the actual finite cyclic quotients of the central four-tori.
This file constructs their covering projections and isolates the finite-CW inputs that are not
currently available in Mathlib.
-/

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- Package an explicit constant-degree finite cover by a four-torus into the Section 7 model. -/
@[expose] public noncomputable def finiteFourTorusCoverModelOfFiniteCover
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) (degree : ℕ) (hdegree : 0 < degree)
    (hcard : ∀ x, Nat.card {y : E // p y = x} = degree)
    (coverHomology : FourTorusHomologicalModel E) (quotientFiniteCW : FiniteCWModelSix X) :
    FiniteFourTorusCoverModel X where
  toFiniteCoverModelSix :=
    { Cover := E
      coverTopology := inferInstance
      projection := p
      isCovering := hp
      degree := degree
      degree_pos := hdegree
      fiberCardinality := hcard
      coverHomologyFiniteSix := coverHomology.integralHomologyFiniteSix
      quotientFiniteCW := quotientFiniteCW }
  coverHomology := coverHomology

namespace Topology.PaperEllipticReducedCentralFiberCoverModels

open Geometry Geometry.ComplexTorus Geometry.EllipticFixedPointCriterion
open Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open Topology.PaperEllipticFillingRadialRetraction

noncomputable section

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T)

namespace RadialEllipticActionData

/-- The inverse image of the reduced central fibre under the full orbit projection. -/
public abbrev centralFiberCoverSource :=
  {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p ∈
    D.reducedCentralFiber}

/-- Restriction of the full orbit projection to the reduced central fibre. -/
@[expose] public def centralFiberCoverProjection :
    C(centralFiberCoverSource D, D.reducedCentralFiber) where
  toFun p := ⟨Quotient.mk _ p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quot_mk.comp continuous_subtype_val) _

/-- A point maps into the reduced central fibre exactly when it lies in the central slice. -/
public theorem mem_centralSlice_iff_quotient_mem_reducedCentralFiber (p : D.Product) :
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

/-- Insert a torus point into the inverse image of the reduced central fibre. -/
public def centralFiberCoverSourceOfTorus (x : T) : centralFiberCoverSource D :=
  ⟨(D.actionData.center, x), by
    apply (mem_centralSlice_iff_quotient_mem_reducedCentralFiber D
      (D.actionData.center, x)).2
    exact D.center_eq⟩

/-- The restricted covering source is canonically the original central four-torus. -/
public def centralFiberCoverSourceHomeomorph :
    centralFiberCoverSource D ≃ₜ T where
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

/-- The central-fibre projection is the restriction of the full finite cyclic quotient
covering. -/
public theorem centralFiberCoverProjection_isCovering
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

/-- A fibre of the restricted central projection is canonically a fibre of the full orbit
projection. -/
@[expose] public def centralFiberCoverFiberEquivFullFiber
    (x : D.reducedCentralFiber) :
    {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} ≃
      {p : D.Product // Quotient.mk (orbitRelOf D.actionData.diagonalAction) p = x.1} where
  toFun y := ⟨y.1.1, congrArg Subtype.val y.2⟩
  invFun p := ⟨⟨p.1, by rw [p.2]; exact x.2⟩, by
    apply Subtype.ext
    exact p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every fibre of the reduced central projection has exactly `m` points. -/
public theorem centralFiberCoverProjection_fiberCardinality
    (hfree : letI := D.actionData.diagonalAction
      IsCancelSMul (FiniteCyclic m) D.Product)
    (x : D.reducedCentralFiber) :
    Nat.card {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} = m := by
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
  have hx := x.2
  simp only [PaperEllipticFillingRadialRetraction.RadialEllipticActionData.reducedCentralFiber]
    at hx
  obtain ⟨p, _hp, hpx⟩ := hx
  let pFiber : {q : D.Product //
      Quotient.mk (orbitRelOf D.actionData.diagonalAction) q = x.1} := ⟨p, hpx⟩
  calc
    Nat.card {y : centralFiberCoverSource D // centralFiberCoverProjection D y = x} =
        Nat.card {q : D.Product //
          Quotient.mk (orbitRelOf D.actionData.diagonalAction) q = x.1} :=
      Nat.card_congr (centralFiberCoverFiberEquivFullFiber D x)
    _ = Nat.card (FiniteCyclic m) := Nat.card_congr (hq'.fiberEquivGroup pFiber)
    _ = m := finiteCyclic_card m

end RadialEllipticActionData

open Geometry.AnalyticTorusFamily Geometry.EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- A free affine order-three quotient of the full-rank central four-torus has finite CW type of
dimension at most six. -/
public axiom orderThreeReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderThreeReducedCentralFiber A.periods)

/-- A free affine order-four quotient of the full-rank central four-torus has finite CW type of
dimension at most six. -/
public axiom orderFourReducedCentralFiberFiniteCWModelSix :
    FiniteCWModelSix (OrderFourReducedCentralFiber A.periods)

/-- The actual order-three reduced central fibre is a three-sheeted quotient of its central
four-torus. -/
@[expose] public noncomputable def orderThreeReducedCentralFiberCoverModel :
    FiniteFourTorusCoverModel (OrderThreeReducedCentralFiber A.periods) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  let hfull := FullRank.ofSetupInequalities p.1 p.2
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p.1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p.1) := inferInstance
  let _ : CompactSpace (AdditiveTorus p.1) := torus_compactSpace p.1 hfull
  let _ : LocallyCompactSpace (AdditiveTorus p.1) := inferInstance
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  let D := orderThreeRadialActionData A.periods
  let coverHomology : FourTorusHomologicalModel
      (RadialEllipticActionData.centralFiberCoverSource D) :=
    (EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 hfull).homeomorph
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)
  exact finiteFourTorusCoverModelOfFiniteCover
    (RadialEllipticActionData.centralFiberCoverProjection D)
    (RadialEllipticActionData.centralFiberCoverProjection_isCovering D
      A.orderThreeAction_free)
    3 (by norm_num)
    (RadialEllipticActionData.centralFiberCoverProjection_fiberCardinality D
      A.orderThreeAction_free)
    coverHomology
    (orderThreeReducedCentralFiberFiniteCWModelSix A)

/-- The actual order-four reduced central fibre is a four-sheeted quotient of its central
four-torus. -/
@[expose] public noncomputable def orderFourReducedCentralFiberCoverModel :
    FiniteFourTorusCoverModel (OrderFourReducedCentralFiber A.periods) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  let hfull := FullRank.ofSetupInequalities p.1 p.2
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p.1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hfull
  let _ : T2Space (AdditiveTorus p.1) := inferInstance
  let _ : CompactSpace (AdditiveTorus p.1) := torus_compactSpace p.1 hfull
  let _ : LocallyCompactSpace (AdditiveTorus p.1) := inferInstance
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  let D := orderFourRadialActionData A.periods
  let coverHomology : FourTorusHomologicalModel
      (RadialEllipticActionData.centralFiberCoverSource D) :=
    (EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 hfull).homeomorph
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)
  exact finiteFourTorusCoverModelOfFiniteCover
    (RadialEllipticActionData.centralFiberCoverProjection D)
    (RadialEllipticActionData.centralFiberCoverProjection_isCovering D
      A.orderFourAction_free)
    4 (by norm_num)
    (RadialEllipticActionData.centralFiberCoverProjection_fiberCardinality D
      A.orderFourAction_free)
    coverHomology
    (orderFourReducedCentralFiberFiniteCWModelSix A)

end

end Topology.PaperEllipticReducedCentralFiberCoverModels

namespace Geometry.PaperAnalyticData.SectionSevenLocalEulerModels

open CuspPuncturedCollarBridge
open Topology.PaperEllipticFillingRealPeriodRadial
open Topology.PaperEllipticReducedCentralFiberCoverModels

variable (A : PaperAnalyticData)

/-- Supply only the cusp and bundle models; the two elliptic radial charts and finite-cover
models are the explicit constructions above. -/
@[expose] public noncomputable def ofCuspAndBundleModels
    (cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (centralBundle : FourTorusBundleModel A.openEmbeddingStarData.central)
    (cuspCells : CuspToricCellModel
      (cuspRetraction.quotientCentralFiber A.starCuspWitness))
    (collarBundle : ∀ i : Fin 3, FourTorusBundleModel
      (A.openEmbeddingStarData.collarSource i)) :
    A.SectionSevenLocalEulerModels where
  cuspRetraction := cuspRetraction
  orderThreeRadialChart := orderThreeSelectedAffineRadialCompatibility A
  orderFourRadialChart := orderFourSelectedAffineRadialCompatibility A
  centralBundle := centralBundle
  cuspCells := cuspCells
  orderThreeCover := orderThreeReducedCentralFiberCoverModel A
  orderFourCover := orderFourReducedCentralFiberCoverModel A
  collarBundle := collarBundle

end Geometry.PaperAnalyticData.SectionSevenLocalEulerModels

end SphereSixComplex
