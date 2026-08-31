module

public import SphereSixComplex.Topology.PaperCuspFiniteFiberDegreeOneKilledSection
public import SphereSixComplex.Topology.PaperCuspRadialClutchingConstruction
public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationGeometricReduction

/-!
# Angular vanishing on the marked cusp fibre

The angular coordinate of the universal cusp cover descends to a circle-valued map on the
punctured collar.  On the marked period fibre this map is constant.  This file isolates that
point-set calculation and its first-homology consequence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology
open SphereSixComplex.Topology.EstablishedFirstHurewicz

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- The logarithmic angular coordinate upstairs, reduced modulo integral translation. -/
private def additiveCuspAngularCircleMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(additiveCuspRadiusCover W.localWitness.radius, UnitAddCircle) where
  toFun p := ((p.1.2.re : ℝ) : UnitAddCircle)
  continuous_toFun :=
    (AddCircle.continuous_mk' 1).comp
      (Complex.continuous_re.comp (continuous_snd.comp continuous_subtype_val))

private theorem additiveCuspAngularCircleMap_factors
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.FactorsThrough (additiveCuspAngularCircleMap W)
      (additiveCuspBoundaryProjection W) := by
  intro p q hpq
  obtain ⟨k, hk, _⟩ := additiveCuspBoundaryProjection_eq_period_data W p q hpq
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨-k, ?_⟩
  have hre := congrArg Complex.re hk
  norm_num at hre ⊢
  linarith

/-- The angular circle coordinate on the punctured cusp collar. -/
private noncomputable def cuspBoundaryAngularCircleMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(puncturedLocalCuspQuotient W, UnitAddCircle) :=
  (additiveCuspBoundaryProjection_isQuotientMap W).lift
    (additiveCuspAngularCircleMap W) (additiveCuspAngularCircleMap_factors W)

@[simp]
private theorem cuspBoundaryAngularCircleMap_projection
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularCircleMap W (additiveCuspBoundaryProjection W p) =
      ((p.1.2.re : ℝ) : UnitAddCircle) := by
  exact ContinuousMap.congr_fun
    ((additiveCuspBoundaryProjection_isQuotientMap W).lift_comp
      (additiveCuspAngularCircleMap W) (additiveCuspAngularCircleMap_factors W)) p

private theorem markedFiberToPuncturedCuspForAngularComparison_projection
    (G : ActualCuspRadialClutchingData W)
    (y : let _ := G.fiberTopology; G.Fiber) :
    let _ := G.fiberTopology
    markedFiberToPuncturedCuspForAngularComparison G y =
      additiveCuspBoundaryProjection W
        ⟨((G.fiberHomeomorph y).out, G.markingParameter), G.markingParameter_mem⟩ := by
  let _ := G.fiberTopology
  have hy : G.fiberHomeomorph y =
      additiveTorusProjection G.fiberParameter (G.fiberHomeomorph y).out := by
    exact (Quotient.out_eq (G.fiberHomeomorph y)).symm
  rw [show markedFiberToPuncturedCuspForAngularComparison G =
      G.markedFiberToPuncturedCusp from rfl]
  rw [G.markedFiberToPuncturedCusp_eq_actualCuspCollarPeriodPoint
    y (G.fiberHomeomorph y).out hy]
  rfl

/-- On the literal marked period fibre the descended angular circle coordinate is constant. -/
private theorem cuspBoundaryAngularCircleMap_comp_markedFiber
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    (cuspBoundaryAngularCircleMap W).comp
        (markedFiberToPuncturedCuspForAngularComparison G) =
      ContinuousMap.const G.Fiber ((G.markingParameter.re : ℝ) : UnitAddCircle) := by
  let _ := G.fiberTopology
  ext y
  rw [ContinuousMap.comp_apply, markedFiberToPuncturedCuspForAngularComparison_projection]
  rw [cuspBoundaryAngularCircleMap_projection]
  rfl

private theorem integralSingularHomologyMap_const_eq_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (y : Y) (x : IntegralSingularHomology 1 X) :
    integralSingularHomologyMap 1 (ContinuousMap.const X y) x = 0 := by
  let b := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
  let H := Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData X b
  obtain ⟨a, rfl⟩ := H.equiv.surjective x
  obtain ⟨p, rfl⟩ := Topology.EstablishedFirstHurewicz.loopClass_surjective a
  rw [H.equiv_loopClass]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  have hp : p.map (ContinuousMap.const X y).continuous = Path.refl y := by
    ext t
    rfl
  rw [hp]
  exact Topology.FirstHurewiczProof.loopHomologyClass_refl
    ((ContinuousMap.const X y) b)

/-- The circle-valued angular coordinate kills degree-one homology carried by the marked
fibre. -/
private theorem cuspBoundaryAngularCircleMap_markedFiber_homology_eq_zero
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 1 G.Fiber) :
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 (cuspBoundaryAngularCircleMap W)
        (integralSingularHomologyMap 1
          (markedFiberToPuncturedCuspForAngularComparison G) x) = 0 := by
  let _ := G.fiberTopology
  let _ : PathConnectedSpace (AdditiveTorus G.fiberParameter) :=
    CuspRadialClutchingConstruction.additiveTorus_pathConnected G.fiberParameter
  let _ : PathConnectedSpace G.Fiber :=
    G.fiberHomeomorph.symm.surjective.pathConnectedSpace G.fiberHomeomorph.symm.continuous
  rw [integralSingularHomologyMap_comp_wang]
  rw [cuspBoundaryAngularCircleMap_comp_markedFiber]
  exact integralSingularHomologyMap_const_eq_zero _ x

/-- The angular coordinate based at a selected point of the additive universal cover. -/
private def additiveCuspBasedAngularCircleMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    C(additiveCuspRadiusCover W.localWitness.radius, UnitAddCircle) where
  toFun p := ((p.1.2.re - e.1.2.re : ℝ) : UnitAddCircle)
  continuous_toFun :=
    (AddCircle.continuous_mk' 1).comp
      ((Complex.continuous_re.comp (continuous_snd.comp continuous_subtype_val)).sub
        continuous_const)

private theorem additiveCuspBasedAngularCircleMap_factors
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    Function.FactorsThrough (additiveCuspBasedAngularCircleMap W e)
      (additiveCuspBoundaryProjection W) := by
  intro p q hpq
  obtain ⟨k, hk, _⟩ := additiveCuspBoundaryProjection_eq_period_data W p q hpq
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨-k, ?_⟩
  have hre := congrArg Complex.re hk
  norm_num at hre ⊢
  linarith

private noncomputable def cuspBoundaryBasedAngularCircleMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    C(puncturedLocalCuspQuotient W, UnitAddCircle) :=
  (additiveCuspBoundaryProjection_isQuotientMap W).lift
    (additiveCuspBasedAngularCircleMap W e)
    (additiveCuspBasedAngularCircleMap_factors W e)

@[simp]
private theorem cuspBoundaryBasedAngularCircleMap_projection
    (W : ActualPuncturedCuspCollarWitness N M)
    (e p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryBasedAngularCircleMap W e (additiveCuspBoundaryProjection W p) =
      ((p.1.2.re - e.1.2.re : ℝ) : UnitAddCircle) := by
  exact ContinuousMap.congr_fun
    ((additiveCuspBoundaryProjection_isQuotientMap W).lift_comp
      (additiveCuspBasedAngularCircleMap W e)
      (additiveCuspBasedAngularCircleMap_factors W e)) p

@[simp]
private theorem cuspBoundaryBasedAngularCircleMap_base
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryBasedAngularCircleMap W e (additiveCuspBoundaryProjection W e) = 0 := by
  rw [cuspBoundaryBasedAngularCircleMap_projection]
  simp

private def cuspBoundaryAngularDeckHom :
    paperCuspBoundaryDeck →*
      Multiplicative (AddSubgroup.zmultiples (1 : ℝ)) where
  toFun g := Multiplicative.ofAdd
    (StandardCircleHomologyLiftDegree.intToUnitDeck (-g.right.toAdd))
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp [SemidirectProduct.mul_right, add_comm]

private def additiveCuspBasedAngularRealLift
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    C(additiveCuspRadiusCover W.localWitness.radius, ℝ) where
  toFun p := p.1.2.re - e.1.2.re
  continuous_toFun :=
    (Complex.continuous_re.comp (continuous_snd.comp continuous_subtype_val)).sub
      continuous_const

private noncomputable def cuspBoundaryAngularCoverMapData
    (W : ActualPuncturedCuspCollarWitness N M)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    letI := paperCuspBoundaryDeckAction W
    QuotientCoverMapData
      (G := paperCuspBoundaryDeck)
      (H := Multiplicative (AddSubgroup.zmultiples (1 : ℝ)))
      (additiveCuspBoundaryProjection W)
      (⟨fun x : ℝ ↦ (x : UnitAddCircle), continuous_quotient_mk'⟩ : C(ℝ, UnitAddCircle)) := by
  let _ := paperCuspBoundaryDeckAction W
  exact
    { deckMap := cuspBoundaryAngularDeckHom
      lift := additiveCuspBasedAngularRealLift W e
      baseMap := cuspBoundaryBasedAngularCircleMap W e
      commutes := fun p ↦ by
        rw [cuspBoundaryBasedAngularCircleMap_projection]
        rfl
      equivariant := fun g p ↦ by
        change (g • p).1.2.re - e.1.2.re =
          ((cuspBoundaryAngularDeckHom g).toAdd : ℝ) + (p.1.2.re - e.1.2.re)
        rw [paperCuspBoundaryDeck_smul_apply]
        change (p.1.2 - g.right.toAdd).re - e.1.2.re =
          ((StandardCircleHomologyLiftDegree.intToUnitDeck (-g.right.toAdd) :
            AddSubgroup.zmultiples (1 : ℝ)) : ℝ) + (p.1.2.re - e.1.2.re)
        simp only [StandardCircleHomologyLiftDegree.intToUnitDeck, AddEquiv.ofBijective_apply]
        change (p.1.2 - g.right.toAdd).re - e.1.2.re =
          ((-g.right.toAdd : ℤ) : ℝ) + (p.1.2.re - e.1.2.re)
        simp
        ring }

private theorem unitCircleWinding_firstHurewicz
    (a : FundamentalGroup UnitAddCircle 0) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        ((Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData
          UnitAddCircle 0).equiv
          (Additive.ofMul (Abelianization.of a))) =
      (StandardCircleHomologyLiftDegree.unitCircleFundamentalGroupEquiv a).toAdd := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      ((Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData
        UnitAddCircle 0).equiv
        (Topology.EstablishedFirstHurewicz.loopClass p)) = _
  rw [(Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData
    UnitAddCircle 0).equiv_loopClass]
  rw [StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_loop]
  rw [StandardCircleHomologyLiftDegree.basedLoopWinding_loop]

private theorem cuspBoundaryBasedAngularCircleMap_fundamentalGroup
    (W : ActualPuncturedCuspCollarWitness N M)
    (b : puncturedLocalCuspQuotient W) (g : paperCuspBoundaryDeck) :
    letI := paperCuspBoundaryDeckAction W
    letI := paperCuspFillingDeckAction W
    let U := paperCuspUnwrappedFillingCover W b
    let T := U.toToricFillingCoverModel
    let Q : C(ℝ, UnitAddCircle) :=
      ⟨fun x : ℝ ↦ (x : UnitAddCircle), continuous_quotient_mk'⟩
    let C := cuspBoundaryAngularCoverMapData W U.base
    let γ := T.boundaryFundamentalGroupEquiv.symm (MulOpposite.op g)
    let he : C.lift U.base = 0 := by
      change U.base.1.2.re - U.base.1.2.re = 0
      ring
    let δ := FundamentalGroup.mapOfEq C.baseMap
      ((C.commutes U.base).trans (congrArg Q he)) γ
    StandardCircleHomologyLiftDegree.unitCircleFundamentalGroupEquiv δ =
      Multiplicative.ofAdd (-g.right.toAdd) := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let Q : C(ℝ, UnitAddCircle) :=
    ⟨fun x : ℝ ↦ (x : UnitAddCircle), continuous_quotient_mk'⟩
  let hp := U.boundaryQuotient
  let hq := IsAddQuotientCoveringMap.toMultiplicative
    (fun x : ℝ ↦ (x : UnitAddCircle)) (AddSubgroup.zmultiples (1 : ℝ))
    (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ))
  let C := cuspBoundaryAngularCoverMapData W U.base
  let γ := T.boundaryFundamentalGroupEquiv.symm (MulOpposite.op g)
  have he : C.lift U.base = 0 := by
    change U.base.1.2.re - U.base.1.2.re = 0
    ring
  let δ := FundamentalGroup.mapOfEq C.baseMap
    ((C.commutes U.base).trans (congrArg Q he)) γ
  change StandardCircleHomologyLiftDegree.unitCircleFundamentalGroupEquiv δ =
    Multiplicative.ofAdd (-g.right.toAdd)
  have hnat := establishedQuotientCoverFundamentalGroupNaturality_of_lift_eq
    hp hq C U.base 0 he γ
  have hsource : hp.fundamentalGroupEquiv ⟨U.base, rfl⟩ γ = MulOpposite.op g := by
    change T.boundaryFundamentalGroupEquiv γ = MulOpposite.op g
    exact T.boundaryFundamentalGroupEquiv.apply_symm_apply _
  rw [hsource] at hnat
  change MulOpposite.op (cuspBoundaryAngularDeckHom g) =
    hq.fundamentalGroupEquiv ⟨0, rfl⟩ δ at hnat
  have htarget : hq.fundamentalGroupEquiv ⟨0, rfl⟩ δ =
      MulOpposite.op (cuspBoundaryAngularDeckHom g) := hnat.symm
  apply Multiplicative.toAdd.injective
  change StandardCircleHomologyLiftDegree.intToUnitDeck.symm
      ((hq.fundamentalGroupEquiv ⟨0, rfl⟩ δ).unop.toAdd) = -g.right.toAdd
  rw [htarget]
  simp [cuspBoundaryAngularDeckHom]

private theorem unitCircleWinding_map_firstHurewicz
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(X, UnitAddCircle)) (b : X) (h : f b = 0)
    (a : FundamentalGroup X b) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 f
          ((Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData X b).equiv
            (Additive.ofMul (Abelianization.of a)))) =
      (StandardCircleHomologyLiftDegree.unitCircleFundamentalGroupEquiv
        (FundamentalGroup.mapOfEq f h a)).toAdd := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 f
        ((Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData X b).equiv
          (Topology.EstablishedFirstHurewicz.loopClass p))) = _
  rw [(Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData X b).equiv_loopClass]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  rw [← StandardCircleHomologyLiftDegree.loopHomologyClass_cast
    (p.map f.continuous) h.symm]
  rw [StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_loop]
  rw [StandardCircleHomologyLiftDegree.basedLoopWinding_loop]
  rw [FundamentalGroup.mapOfEq_apply]
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]

private theorem cuspBoundaryAngularHomologyCoordinate_eq_neg_winding
    (W : ActualPuncturedCuspCollarWitness N M)
    (b : puncturedLocalCuspQuotient W)
    (x : IntegralSingularHomology 1 (puncturedLocalCuspQuotient W)) :
    letI := paperCuspBoundaryDeckAction W
    letI := paperCuspFillingDeckAction W
    let U := paperCuspUnwrappedFillingCover W b
    cuspBoundaryAngularHomologyCoordinate W b x =
      -StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (cuspBoundaryBasedAngularCircleMap W U.base) x) := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  let e := T.boundaryFundamentalGroupEquiv
  let hOne := deckHOneEquivOfFundamentalGroupEquivOpposite
    (T.boundaryProjection T.base) e
  obtain ⟨z, rfl⟩ := hOne.surjective x
  cases z with
  | ofMul z =>
    obtain ⟨g, rfl⟩ := Quotient.exists_rep z
    let γ := e.symm (MulOpposite.op g)
    have hdeck : deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
        (T.boundaryProjection T.base) e
          (Additive.ofMul (Abelianization.of g)) =
        Additive.ofMul (Abelianization.of γ) := by
      apply (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
        (T.boundaryProjection T.base) e).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      change Abelianization.of g =
        abelianizationMulOppositeEquiv paperCuspBoundaryDeck
          (Abelianization.of (e γ))
      rw [e.apply_symm_apply, abelianizationMulOppositeEquiv_of_op]
    change cuspDeckAngularAbelianizationCoordinate
        (hOne.symm (hOne (Additive.ofMul (Abelianization.of g)))) = _
    rw [hOne.symm_apply_apply]
    change g.right.toAdd = _
    change _ = -StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (cuspBoundaryBasedAngularCircleMap W U.base)
          (hOne (Additive.ofMul (Abelianization.of g))))
    rw [show hOne (Additive.ofMul (Abelianization.of g)) =
        (Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData _
          (T.boundaryProjection T.base)).equiv
          (Additive.ofMul (Abelianization.of γ)) by
      change (Topology.EstablishedFirstHurewicz.establishedFirstHurewiczData _
          (T.boundaryProjection T.base)).equiv
            (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
              (T.boundaryProjection T.base) e
                (Additive.ofMul (Abelianization.of g))) = _
      rw [hdeck]]
    have hbase : T.boundaryProjection T.base =
        additiveCuspBoundaryProjection W U.base := rfl
    have hzero : cuspBoundaryBasedAngularCircleMap W U.base
        (T.boundaryProjection T.base) = 0 := by
      rw [hbase]
      exact cuspBoundaryBasedAngularCircleMap_base W U.base
    rw [unitCircleWinding_map_firstHurewicz
      (cuspBoundaryBasedAngularCircleMap W U.base)
      (T.boundaryProjection T.base)
      hzero γ]
    have hfg := cuspBoundaryBasedAngularCircleMap_fundamentalGroup W b g
    change StandardCircleHomologyLiftDegree.unitCircleFundamentalGroupEquiv
        (FundamentalGroup.mapOfEq
          (cuspBoundaryBasedAngularCircleMap W U.base) hzero γ) =
      Multiplicative.ofAdd (-g.right.toAdd) at hfg
    rw [hfg]
    simp

private theorem cuspBoundaryBasedAngularCircleMap_comp_markedFiber
    (G : ActualCuspRadialClutchingData W)
    (e : additiveCuspRadiusCover W.localWitness.radius) :
    let _ := G.fiberTopology
    (cuspBoundaryBasedAngularCircleMap W e).comp
        (markedFiberToPuncturedCuspForAngularComparison G) =
      ContinuousMap.const G.Fiber
        ((G.markingParameter.re - e.1.2.re : ℝ) : UnitAddCircle) := by
  let _ := G.fiberTopology
  ext y
  rw [ContinuousMap.comp_apply, markedFiberToPuncturedCuspForAngularComparison_projection]
  rw [cuspBoundaryBasedAngularCircleMap_projection]
  rfl

private theorem cuspBoundaryBasedAngularCircleMap_markedFiber_homology_eq_zero
    (G : ActualCuspRadialClutchingData W)
    (e : additiveCuspRadiusCover W.localWitness.radius)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 1 G.Fiber) :
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 (cuspBoundaryBasedAngularCircleMap W e)
        (integralSingularHomologyMap 1
          (markedFiberToPuncturedCuspForAngularComparison G) x) = 0 := by
  let _ := G.fiberTopology
  let _ : PathConnectedSpace (AdditiveTorus G.fiberParameter) :=
    CuspRadialClutchingConstruction.additiveTorus_pathConnected G.fiberParameter
  let _ : PathConnectedSpace G.Fiber :=
    G.fiberHomeomorph.symm.surjective.pathConnectedSpace G.fiberHomeomorph.symm.continuous
  rw [integralSingularHomologyMap_comp_wang]
  rw [cuspBoundaryBasedAngularCircleMap_comp_markedFiber]
  exact integralSingularHomologyMap_const_eq_zero _ x

/-- The actual marked cusp fibre has zero angular coordinate in degree-one homology. -/
public theorem cuspAngularCoordinateVanishesOnMarkedFiber
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    CuspAngularCoordinateVanishesOnMarkedFiber G b := by
  let _ := G.fiberTopology
  intro x
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  rw [cuspBoundaryAngularHomologyCoordinate_eq_neg_winding W b]
  rw [cuspBoundaryBasedAngularCircleMap_markedFiber_homology_eq_zero G U.base x]
  simp

/-- The actual cusp filling therefore supplies the killed degree-one Wang section. -/
public theorem actualCuspDegreeOne_section
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHOnePresentation G.clutching).GeometricSection,
      (rawDegreeOneTotalSpecialization G).comp S.lift = 0 :=
  degreeOne_section_of_angularCoordinateVanishesOnMarkedFiber G b
    (cuspAngularCoordinateVanishesOnMarkedFiber G b)

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
