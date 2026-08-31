module

public import SphereSixComplex.Topology.CuspFiberSpecializationGeometricObligations
public import SphereSixComplex.Topology.RankOneWangHomologySplitting

/-!
# The killed degree-one cusp Wang section

The angular deck meridian of the punctured cusp is killed by the toric filling.  First Hurewicz
therefore gives a canonical killed class in the first homology of the radial mapping torus.  The
only remaining geometric input needed for a killed Wang section is that this class is primitive
in the invariant quotient; its sign is immaterial.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology
open SphereSixComplex.Topology.EstablishedFirstHurewicz

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- The homology class of the angular deck meridian in the punctured cusp collar. -/
public noncomputable def cuspBoundaryMeridianHomologyClass
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    IntegralSingularHomology 1 (puncturedLocalCuspQuotient W) := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  exact (establishedFirstHurewiczData _ (T.boundaryProjection T.base)).equiv
    (Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian))

/-- The actual toric cusp filling kills the angular meridian in first homology. -/
public theorem puncturedLocalCuspToFilling_cuspBoundaryMeridianHomologyClass
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    integralSingularHomologyMap 1
        ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
        (cuspBoundaryMeridianHomologyClass W b) = 0 := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : SimplyConnectedSpace (CuspLocalPhaseAction.LocalCarrier M W.localWitness.radius) :=
    U.fillingSimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
    U.fillingQuotient.surjective.pathConnectedSpace U.fillingProjection.continuous
  have hpi : FundamentalGroup.map T.coverMap.baseMap (T.boundaryProjection T.base)
      U.fundamentalGroupData.meridian = 1 := by
    change U.fundamentalGroupData.meridian ∈
      (FundamentalGroup.map T.coverMap.baseMap (T.boundaryProjection T.base)).ker
    rw [U.fundamentalGroupData.ker_map]
    apply Subgroup.subset_normalClosure
    exact Or.inr (Set.mem_singleton _)
  have hab : abelianPi1Map T.coverMap.baseMap (T.boundaryProjection T.base)
      (Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian)) = 0 := by
    change Additive.ofMul (Abelianization.of
      (FundamentalGroup.map T.coverMap.baseMap (T.boundaryProjection T.base)
        U.fundamentalGroupData.meridian)) = 0
    rw [hpi]
    rfl
  have hnat := establishedFirstHurewiczData_naturality T.coverMap.baseMap
    (T.boundaryProjection T.base)
    (Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian))
  rw [hab, map_zero] at hnat
  exact hnat.symm

/-- The angular coordinate on the abelianized cusp deck group. -/
public def cuspDeckAngularAbelianizationCoordinate :
    Additive (Abelianization paperCuspBoundaryDeck) →ₗ[ℤ] ℤ where
  toFun := (Abelianization.lift
    (SemidirectProduct.rightHom
      (φ := integerAffineMonodromy paperCuspMonodromy))).toAdditiveLeft
  map_add' := (Abelianization.lift
    (SemidirectProduct.rightHom
      (φ := integerAffineMonodromy paperCuspMonodromy))).toAdditiveLeft.map_add
  map_smul' n a := by
    exact map_intCast_smul
      (Abelianization.lift
        (SemidirectProduct.rightHom
          (φ := integerAffineMonodromy paperCuspMonodromy))).toAdditiveLeft
        ℤ ℤ n a

/-- The first-homology angular coordinate obtained directly from the universal cusp cover. -/
public noncomputable def cuspBoundaryAngularHomologyCoordinate
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    IntegralSingularHomology 1 (puncturedLocalCuspQuotient W) →ₗ[ℤ] ℤ := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  exact cuspDeckAngularAbelianizationCoordinate.comp
    (deckHOneEquivOfFundamentalGroupEquivOpposite
      (T.boundaryProjection T.base) T.boundaryFundamentalGroupEquiv).symm.toLinearMap

/-- In the cover-theoretic coordinate, the selected angular meridian is the positive
generator. -/
public theorem cuspBoundaryAngularHomologyCoordinate_meridian
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    cuspBoundaryAngularHomologyCoordinate W b
      (cuspBoundaryMeridianHomologyClass W b) = 1 := by
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
  have hdeck : deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
      (T.boundaryProjection T.base) e
        (Additive.ofMul (Abelianization.of paperCuspBoundaryMeridian)) =
      Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian) := by
    apply (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
      (T.boundaryProjection T.base) e).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change Abelianization.of paperCuspBoundaryMeridian =
      abelianizationMulOppositeEquiv paperCuspBoundaryDeck
        (Abelianization.of (e U.fundamentalGroupData.meridian))
    have he : e U.fundamentalGroupData.meridian =
        MulOpposite.op paperCuspBoundaryMeridian :=
      U.fundamentalGroupData.meridian_deck
    rw [he, abelianizationMulOppositeEquiv_of_op]
  change cuspDeckAngularAbelianizationCoordinate
      (hOne.symm
        ((establishedFirstHurewiczData _ (T.boundaryProjection T.base)).equiv
          (Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian)))) = 1
  rw [← hdeck]
  change cuspDeckAngularAbelianizationCoordinate
      (hOne.symm (hOne (Additive.ofMul (Abelianization.of paperCuspBoundaryMeridian)))) = 1
  rw [hOne.symm_apply_apply]
  rfl

/-- The angular meridian, transported through the radial collar homotopy equivalence. -/
public noncomputable def cuspMappingTorusMeridianHomologyClass
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) := by
  let _ := G.fiberTopology
  exact integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
      (cuspBoundaryMeridianHomologyClass W b)

/-- The transported angular meridian is killed by raw degree-one specialization. -/
public theorem rawDegreeOneTotalSpecialization_cuspMappingTorusMeridianHomologyClass
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    rawDegreeOneTotalSpecialization G (cuspMappingTorusMeridianHomologyClass G b) = 0 := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  change integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
      (e.symm (e (cuspBoundaryMeridianHomologyClass W b))) = 0
  rw [e.symm_apply_apply,
    puncturedLocalCuspToFilling_cuspBoundaryMeridianHomologyClass]

/-- The cover-theoretic angular coordinate, transported to the radial mapping torus. -/
public noncomputable def cuspMappingTorusAngularHomologyCoordinate
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) →ₗ[ℤ] ℤ := by
  let _ := G.fiberTopology
  exact (cuspBoundaryAngularHomologyCoordinate W b).comp
    (integralSingularHomologyEquivOfHomotopyEquiv 1
      G.totalHomotopyEquiv).symm.toIntLinearEquiv.toLinearMap

/-- The transported angular meridian still has angular coordinate one. -/
public theorem cuspMappingTorusAngularHomologyCoordinate_meridian
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    cuspMappingTorusAngularHomologyCoordinate G b
      (cuspMappingTorusMeridianHomologyClass G b) = 1 := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  change cuspBoundaryAngularHomologyCoordinate W b
      (e.symm (e (cuspBoundaryMeridianHomologyClass W b))) = 1
  rw [e.symm_apply_apply, cuspBoundaryAngularHomologyCoordinate_meridian]

/-- The marked mapping-torus fibre, included back into the punctured cusp collar. -/
public def markedFiberToPuncturedCuspForAngularComparison
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    C(G.Fiber, puncturedLocalCuspQuotient W) := by
  let _ := G.fiberTopology
  let s : C(G.Fiber,
      OpenRadialInterval W.localWitness.radius × CircleMappingTorus G.clutching) :=
    (ContinuousMap.const G.Fiber G.markingRadius).prodMk
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
  exact (⟨G.totalHomeomorph.symm, G.totalHomeomorph.symm.continuous⟩ :
    C(OpenRadialInterval W.localWitness.radius × CircleMappingTorus G.clutching,
      puncturedLocalCuspQuotient W)).comp s

private theorem totalHomotopyEquiv_comp_markedFiberToPuncturedCuspForAngularComparison
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.toFun.comp (markedFiberToPuncturedCuspForAngularComparison G) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching) := by
  let _ := G.fiberTopology
  ext y
  change openRadialIntervalProdHomotopyEquiv _
      (G.totalHomeomorph (G.totalHomeomorph.symm
        (G.markingRadius,
          finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching) y))) = _
  rw [G.totalHomeomorph.apply_symm_apply]
  rfl

/-- The sole geometric comparison needed by the factorization argument: the independent angular
coordinate vanishes on every class carried by the marked fibre. -/
public def CuspAngularCoordinateVanishesOnMarkedFiber
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) : Prop :=
  let _ := G.fiberTopology
    ∀ x : IntegralSingularHomology 1 G.Fiber,
    cuspBoundaryAngularHomologyCoordinate W b
      (integralSingularHomologyMap 1
        (markedFiberToPuncturedCuspForAngularComparison G) x) = 0

private theorem markedFiberToPuncturedCusp_homologyOne_eq_coinvariants
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 1 G.Fiber) :
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
    e.symm
        ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
          (Submodule.Quotient.mk x)) =
      integralSingularHomologyMap 1
        (markedFiberToPuncturedCuspForAngularComparison G) x := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  let P := circleMappingTorusHOnePresentation G.clutching
  apply e.injective
  rw [e.apply_symm_apply]
  change P.coinvariantsToTotal (Submodule.Quotient.mk x) =
    integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 1
        (markedFiberToPuncturedCuspForAngularComparison G) x)
  rw [integralSingularHomologyMap_comp_wang]
  rw [totalHomotopyEquiv_comp_markedFiberToPuncturedCuspForAngularComparison]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  rfl

/-- Vanishing on the literal marked fibre implies vanishing on the full Wang coinvariant
subgroup. -/
public theorem cuspMappingTorusAngularHomologyCoordinate_comp_coinvariantsToTotal_eq_zero
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : CuspAngularCoordinateVanishesOnMarkedFiber G b) :
    let _ := G.fiberTopology
    (cuspMappingTorusAngularHomologyCoordinate G b).comp
        (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal = 0 := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  change cuspBoundaryAngularHomologyCoordinate W b
      ((integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).symm
        (P.coinvariantsToTotal (Submodule.Quotient.mk x))) = 0
  rw [markedFiberToPuncturedCusp_homologyOne_eq_coinvariants]
  exact h x

/-- The canonical integer coordinate on the degree-one Wang invariant term. -/
public def degreeOneWangInvariantEquivInteger (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Invariants ≃ₗ[ℤ] ℤ := by
  let _ := G.fiberTopology
  exact (invariantsEquivOfConjugacy G.monodromyCoordinates.degreeZero.toIntLinearEquiv
    (circleMonodromyDifference G.clutching 0).toIntLinearMap 0
    G.monodromyCoordinates.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt

private theorem primitiveWangLift_of_coordinate
    {HighRelations High Total LowRelations Low : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Module.Projective ℤ P.Invariants] (e : P.Invariants ≃ₗ[ℤ] ℤ)
    (f : Total →ₗ[ℤ] ℤ) (s : Total)
    (hcoin : f.comp P.coinvariantsToTotal = 0) (hs : f s = 1) :
    e (P.totalToInvariants s) = 1 ∨ e (P.totalToInvariants s) = -1 := by
  let S := WangHomologyPresentation.GeometricSection.ofProjective P
  let q : P.Invariants →ₗ[ℤ] ℤ := f.comp S.lift
  have hsection (z : P.Invariants) : P.totalToInvariants (S.lift z) = z := by
    have hz := DFunLike.congr_fun S.rightInverse z
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using hz
  have hresidual : f (s - S.lift (P.totalToInvariants s)) = 0 := by
    have hp : P.totalToInvariants (s - S.lift (P.totalToInvariants s)) = 0 := by
      rw [map_sub, hsection, sub_self]
    obtain ⟨y, hy⟩ :=
      (P.exact_coinvariantsToTotal_totalToInvariants _).mp hp
    rw [← hy]
    have hyzero := DFunLike.congr_fun hcoin y
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] using hyzero
  have hq : q (P.totalToInvariants s) = 1 := by
    change f (S.lift (P.totalToInvariants s)) = 1
    have hsame : f s = f (S.lift (P.totalToInvariants s)) := by
      rw [map_sub, sub_eq_zero] at hresidual
      exact hresidual
    rw [← hsame, hs]
  let n := e (P.totalToInvariants s)
  let k := q (e.symm 1)
  have hmul : n * k = 1 := by
    calc
      n * k = n • k := by rw [smul_eq_mul]
      _ = q (n • e.symm 1) := (map_smul q n (e.symm 1)).symm
      _ = q (e.symm (n • 1)) := by simp only [map_smul]
      _ = q (e.symm n) := by rw [smul_eq_mul, mul_one]
      _ = q (P.totalToInvariants s) := by
        change q (e.symm (e (P.totalToInvariants s))) = _
        rw [e.symm_apply_apply]
      _ = 1 := hq
  have hn : IsUnit n := IsUnit.of_mul_eq_one k hmul
  simpa only [n] using (Int.isUnit_iff.mp hn)

/-- The precise residual assertion: the killed angular meridian is a primitive Wang lift.
The disjunction deliberately forgets orientation, which is irrelevant for constructing a
section. -/
public def CuspMeridianIsPrimitiveWangLift
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) : Prop :=
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let s := cuspMappingTorusMeridianHomologyClass G b
  degreeOneWangInvariantEquivInteger G (P.totalToInvariants s) = 1 ∨
    degreeOneWangInvariantEquivInteger G (P.totalToInvariants s) = -1

/-- If the independent angular coordinate kills the marked fibre, exactness forces the killed
meridian to be a primitive Wang lift.  The comparison is determined only up to orientation. -/
public theorem cuspMeridianIsPrimitiveWangLift_of_angularCoordinateVanishesOnMarkedFiber
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : CuspAngularCoordinateVanishesOnMarkedFiber G b) :
    CuspMeridianIsPrimitiveWangLift G b := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let e := degreeOneWangInvariantEquivInteger G
  let _ : Module.Projective ℤ P.Invariants := Module.Projective.of_equiv' e.symm
  exact primitiveWangLift_of_coordinate P e
    (cuspMappingTorusAngularHomologyCoordinate G b)
    (cuspMappingTorusMeridianHomologyClass G b)
    (cuspMappingTorusAngularHomologyCoordinate_comp_coinvariantsToTotal_eq_zero G b h)
    (cuspMappingTorusAngularHomologyCoordinate_meridian G b)

private def geometricSectionOfPositiveWangLift
    {HighRelations High Total LowRelations Low : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (e : P.Invariants ≃ₗ[ℤ] ℤ) (s : Total)
    (hs : e (P.totalToInvariants s) = 1) : P.GeometricSection where
  lift := e.toLinearMap.smulRight s
  rightInverse := by
    apply LinearMap.ext
    intro x
    apply e.injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, map_smul, hs, smul_eq_mul, mul_one]
    rfl

private theorem map_comp_geometricSectionOfPositiveWangLift_eq_zero
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (e : P.Invariants ≃ₗ[ℤ] ℤ) (s : Total)
    (hs : e (P.totalToInvariants s) = 1) (f : Total →ₗ[ℤ] L) (hfs : f s = 0) :
    f.comp (geometricSectionOfPositiveWangLift P e s hs).lift = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, geometricSectionOfPositiveWangLift,
    LinearMap.smulRight_apply, map_smul, hfs, smul_zero, LinearMap.zero_apply]

/-- Primitivity of the explicitly killed cusp meridian supplies the required degree-one Wang
section. -/
public theorem degreeOne_section_of_cuspMeridianIsPrimitiveWangLift
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : CuspMeridianIsPrimitiveWangLift G b) :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHOnePresentation G.clutching).GeometricSection,
      (rawDegreeOneTotalSpecialization G).comp S.lift = 0 := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let e := degreeOneWangInvariantEquivInteger G
  let s := cuspMappingTorusMeridianHomologyClass G b
  have hfs : rawDegreeOneTotalSpecialization G s = 0 :=
    rawDegreeOneTotalSpecialization_cuspMappingTorusMeridianHomologyClass G b
  rcases h with hs | hs
  · let S := geometricSectionOfPositiveWangLift P e s hs
    exact ⟨S, map_comp_geometricSectionOfPositiveWangLift_eq_zero P e s hs
      (rawDegreeOneTotalSpecialization G) hfs⟩
  · have hsneg : e (P.totalToInvariants (-s)) = 1 := by
      rw [map_neg, map_neg, hs]
      simp
    have hfsneg : rawDegreeOneTotalSpecialization G (-s) = 0 := by
      rw [map_neg, hfs, neg_zero]
    let S := geometricSectionOfPositiveWangLift P e (-s) hsneg
    exact ⟨S, map_comp_geometricSectionOfPositiveWangLift_eq_zero P e (-s) hsneg
      (rawDegreeOneTotalSpecialization G) hfsneg⟩

/-- The marked-fibre angular comparison is sufficient for the requested killed degree-one Wang
section. -/
public theorem degreeOne_section_of_angularCoordinateVanishesOnMarkedFiber
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : CuspAngularCoordinateVanishesOnMarkedFiber G b) :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHOnePresentation G.clutching).GeometricSection,
      (rawDegreeOneTotalSpecialization G).comp S.lift = 0 :=
  degreeOne_section_of_cuspMeridianIsPrimitiveWangLift G b
    (cuspMeridianIsPrimitiveWangLift_of_angularCoordinateVanishesOnMarkedFiber G b h)

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
