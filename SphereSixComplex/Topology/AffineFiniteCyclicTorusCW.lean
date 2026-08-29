module

public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Finite CW type of affine finite-cyclic torus quotients

This file isolates the classical triangulation input for the reduced elliptic fibres.  A free
finite cyclic action on a full-rank four-torus whose generator lifts to an affine automorphism of
the covering vector space has a compact four-manifold quotient.  The finite-dimensional ANR
theorem therefore supplies a finite CW model, with no cells above dimension four (and hence above
six).
-/

open SphereSixComplex.Geometry SphereSixComplex.Periods
open scoped ContinuousMap

namespace SphereSixComplex.Topology.AffineFiniteCyclicTorusCW

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

/-- A homotopy model by a finite CW complex of dimension at most `d`. -/
public structure FiniteCWModelAtMost (d : ℕ) (X : Type) [TopologicalSpace X] where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : let _ := topology; T2Space Carrier
  homotopyEquiv : let _ := topology; X ≃ₕ Carrier
  cwComplex : let _ := topology; Topology.CWComplex (Set.univ : Set Carrier)
  finite : let _ := topology; let _ := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set Carrier)
  cellsAbove : let _ := topology; let _ := cwComplex
    ∀ n, d < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Carrier) n)

/-- Forget a sharper dimension bound when constructing a model supported through degree six. -/
public noncomputable def FiniteCWModelAtMost.toFiniteCWModelSix
    {d : ℕ} {X : Type} [TopologicalSpace X] (M : FiniteCWModelAtMost d X) (hd : d ≤ 6) :
    FiniteCWModelSix X where
  Carrier := M.Carrier
  topology := M.topology
  t2 := M.t2
  homotopyEquiv := M.homotopyEquiv
  cwComplex := M.cwComplex
  finite := M.finite
  cellsAboveSix n hn := M.cellsAbove n (hd.trans_lt hn)

/-- A compact Hausdorff space charted by `ℂ²` has finite CW homotopy type of real dimension at
most four.  This is the classical finite-dimensional ANR theorem for compact topological
manifolds, specialized to the dimension used here. -/
public axiom establishedFiniteCWModelFour_of_compactComplexTwoChartedSpace
    {X : Type} [TopologicalSpace X] [ChartedSpace ComplexTwoSpace X]
    [T2Space X] [CompactSpace X] :
    FiniteCWModelAtMost 4 X

/-- A compact topological complex surface has finite CW homotopy type, of real dimension at most
four, and this remains true of the Hausdorff base of a surjective covering. -/
public noncomputable def establishedFiniteCWModelFour_of_compactComplexSurfaceCover
    {E X : Type} [TopologicalSpace E] [ChartedSpace ComplexTwoSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    (_hManifold : IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) 0 E)
    (_hcompact : CompactSpace E)
    (projection : C(E, X)) (_hcover : IsCoveringMap projection)
    (_hsurjective : Function.Surjective projection) :
    FiniteCWModelAtMost 4 X := by
  letI : CompactSpace X := isCompact_univ_iff.mp (by
    have himage := isCompact_univ.image projection.continuous
    rw [Set.image_univ, _hsurjective.range_eq] at himage
    exact himage)
  have hcharts :
      ∀ x : X, ∃ e : OpenPartialHomeomorph X ComplexTwoSpace, x ∈ e.source := by
    intro x
    obtain ⟨e, rfl⟩ := _hsurjective x
    obtain ⟨u, heu, hu⟩ := _hcover.isLocalHomeomorph e
    refine ⟨u.symm.trans (chartAt ComplexTwoSpace e), ?_⟩
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [u.symm_source]
      rw [hu]
      exact u.map_source heu
    · change u.symm (projection e) ∈ (chartAt ComplexTwoSpace e).source
      rw [hu, u.left_inv heu]
      exact mem_chart_source ComplexTwoSpace e
  let chart (x : X) := (hcharts x).choose
  letI : ChartedSpace ComplexTwoSpace X := {
    atlas := Set.range chart
    chartAt := chart
    mem_chart_source x := (hcharts x).choose_spec
    chart_mem_atlas x := Set.mem_range_self x
  }
  exact establishedFiniteCWModelFour_of_compactComplexTwoChartedSpace

/-- Classical finite-CW descent along a covering by a full-rank four-torus.  The residual ANR
input says that a compact Hausdorff four-manifold has finite CW type, with no cells above
dimension four (and hence none above dimension six). -/
public noncomputable def finiteCWModelSix_of_fullRankTorusCover
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : Parameters) (_hfull : FullRank p)
    (projection : C(AdditiveTorus p, X)) (_hcover : IsCoveringMap projection)
    (_hsurjective : Function.Surjective projection) :
    FiniteCWModelSix X := by
  let _ : ProperlyDiscontinuousSMul (PeriodGroup p) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul _hfull
  let _ : T2Space (AdditiveTorus p) := inferInstance
  let _ : CompactSpace (AdditiveTorus p) := torus_compactSpace p _hfull
  exact (establishedFiniteCWModelFour_of_compactComplexSurfaceCover
    (torus_isManifold_and_projection_isLocalDiffeomorph p _hfull 0).1
    (inferInstance : CompactSpace (AdditiveTorus p)) projection _hcover
    _hsurjective).toFiniteCWModelSix (by omega)

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

/-- The order-three and order-four affine quotient models follow from the torus-cover residual. -/
public noncomputable def orderThreeFourAffineGeneratorFiniteCWModels :
    OrderThreeFourAffineGeneratorFiniteCWModels where
  orderThree p hfull D _lift _translation _generator_mk hfree :=
    finiteCWModelSix_reducedCentralFiber_of_freeAction p hfull D hfree
  orderFour p hfull D _lift _translation _generator_mk hfree :=
    finiteCWModelSix_reducedCentralFiber_of_freeAction p hfull D hfree

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
