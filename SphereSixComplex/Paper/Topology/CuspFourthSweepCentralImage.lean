module
public import SphereSixComplex.Paper.Topology.CuspFourthCircle
public import SphereSixComplex.Paper.Topology.CuspFixedCircleSweep
public import SphereSixComplex.Paper.Topology.CentralInvariantCircleBoundary
public import SphereSixComplex.Paper.Topology.CuspWangKernel
/-! The actual fourth-period cusp sweep factors through the global invariant circle action and has zero elliptic Mayer–Vietoris boundary. Raw index five has the same Wang class. This refutes the current marked invariant-basis residual, whose index-five coefficient is asserted to be one; the paper assigns the nonzero boundary to the third-period sweep instead. -/

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion

public theorem centralFourthPeriodCircle_regular (A : PaperAnalyticData)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) (t : ℝ) :
    A.centralFourthPeriodCircle ((t : UnitAddCircle),
      A.puncturedBaseHomeomorphTwicePuncturedComplex (Quotient.mk _ b)) =
    A.centralQuotientProjection (projection (regularParameterMap A.periods)
      (b, t • periodVector (regularParameterMap A.periods b).1 ![0,0,0,1])) := by
  change invariantPeriodCircle A.periods ![0,0,0,1] rhoLambda_fourthBasis
    ((t : UnitAddCircle), A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
      (A.puncturedBaseHomeomorphTwicePuncturedComplex (Quotient.mk _ b))) = _
  rw [Homeomorph.symm_apply_apply, invariantPeriodCircle_real]
  rfl

public theorem centralFourthPeriodCircle_cusp (A : PaperAnalyticData)
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (t : ℝ) :
    A.centralFourthPeriodCircle ((t : UnitAddCircle),
      A.centralFamilyCoordinate
        (additiveCuspCoverToGlobal A.starCuspWitness ⟨(0, s), hs⟩)) =
      additiveCuspCoverToGlobal A.starCuspWitness
        ⟨(t • periodVector (cuspBasePoint A.cuspCoordinate s).1 ![0,0,0,1], s), hs⟩ := by
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  convert centralFourthPeriodCircle_regular A
    ((additiveCuspBundleHomeomorph A.starCuspWitness ⟨(0, s), hs⟩).1.1) t using 1
  · rfl
  · rw [additiveCuspCoverToGlobal_eq_quotientProjections]
    rfl

open SectionSevenEllipticTwoDiscCoverData
public theorem actualCuspFullFibreSlice_fourthCircle_real (A : PaperAnalyticData)
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (t : ℝ) :
    actualCuspFullFibreSlice (A := A) s hs
      (cuspFourthCircle (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)) (fun _ ↦ (t : UnitAddCircle))) =
    additiveCuspBoundaryProjection A.starCuspWitness
      ⟨(t • periodVector (cuspBasePoint A.cuspCoordinate s).1 ![0,0,0,1], s), hs⟩ := by
  rw [cuspFourthCircle_real]
  have h : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) s
      (t • periodVector (cuspBasePoint A.cuspCoordinate s).1 ![0,0,0,1]) =
      t • periodVector (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 ![0,0,0,1] := by
    rw [collarFiberEquiv_apply]
    change (fullRankDomain _).realEquiv ((fullRankDomain _).realEquiv.symm
      (t • periodVector _ ![0,0,0,1])) = _
    rw [map_smul, realEquiv_symm_periodVector, map_smul,
      (fullRankDomain _).map_integer]
  rw [← h]
  exact actualCuspFullFibreSlice_additiveTorusProjection s hs _

public theorem actualCuspFullFibreSlice_fourthCircle_central (A : PaperAnalyticData)
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (t : ℝ) :
    A.starToCentral 0
      (actualCuspFullFibreSlice (A := A) s hs
        (cuspFourthCircle (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)) (fun _ ↦ (t : UnitAddCircle)))) =
    A.centralFourthPeriodCircle ((t : UnitAddCircle),
      A.centralFamilyCoordinate
        (additiveCuspCoverToGlobal A.starCuspWitness ⟨(0, s), hs⟩)) := by
  rw [actualCuspFullFibreSlice_fourthCircle_real, centralFourthPeriodCircle_cusp]
  exact puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection A.starCuspWitness _


open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open SphereSixComplex.CyclicAngularFundamentalDomain
public def cuspFourthSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  cuspFixedCircleSweep A (cuspFourthFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness)))

public theorem cuspFourthSweep_real (A : PaperAnalyticData) (r : ℝ)
    (z : StdTorus 1) :
    cuspFourthSweep A ((r : UnitAddCircle), z) =
      actualCuspFullFibreSlice (A := A)
        (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r)
        (by rw [norm_cuspQ_cuspParameterOfPolar _ _ (by
              have := A.starCuspWitness.localWitness.radius_pos; linarith)]
            have := A.starCuspWitness.localWitness.radius_pos; linarith)
        (cuspFourthCircle (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)) z) :=
  cuspFixedCircleSweep_real A _ r z

public theorem cuspFourthSweep_central (A : PaperAnalyticData)
    (u : UnitAddCircle) (z : StdTorus 1) :
    A.starToCentral 0 (cuspFourthSweep A (u, z)) =
      A.centralFourthPeriodCircle (z 0,
        A.centralFamilyCoordinate (A.starToCentral 0 (cuspFourthSweep A (u, 0)))) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (z 0)
  have hz : z = fun _ ↦ (t : UnitAddCircle) := by
    ext i
    fin_cases i
    exact ht.symm
  rw [hz, cuspFourthSweep_real, cuspFourthSweep_real]
  rw [actualCuspFullFibreSlice_fourthCircle_central]
  have hzero := actualCuspFullFibreSlice_fourthCircle_central A
    (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r)
    (by rw [norm_cuspQ_cuspParameterOfPolar _ _ (by
          have := A.starCuspWitness.localWitness.radius_pos; linarith)]
        have := A.starCuspWitness.localWitness.radius_pos; linarith) 0
  change A.starToCentral 0 (actualCuspFullFibreSlice _ _
    (cuspFourthCircle _ 0)) = _ at hzero
  rw [hzero, centralFourthPeriodCircle_coordinate]

public def cuspFourthSweepFactor (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, UnitAddCircle × TwicePuncturedComplex) where
  toFun p := (p.2 0,
    A.centralFamilyCoordinate (A.starToCentral 0 (cuspFourthSweep A (p.1, 0))))
  continuous_toFun := ((continuous_apply 0).comp continuous_snd).prodMk
    (A.centralFamilyCoordinate_continuous.comp
      ((A.starToCentral_isOpenEmbedding 0).continuous.comp ((cuspFourthSweep A).continuous.comp
        (continuous_fst.prodMk continuous_const))))


public def cuspToEllipticUnionMap {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C(A.openEmbeddingStarData.collarSource 0,
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior)) := by
  refine ⟨fun q ↦ ⟨D.cuspToEllipticInteriorMap q, ?_⟩, ?_⟩
  · rw [D.sides_cover]; trivial
  · exact D.cuspToEllipticInteriorMap.hom.continuous.subtype_mk _

public theorem cuspToEllipticUnionMap_central {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (q : A.openEmbeddingStarData.collarSource 0) :
    A.sectionSevenEllipticCentralImageHomeomorph
      ⟨D.cuspToEllipticInteriorMap q, D.cuspToEllipticInteriorMap_mem_centralImage q⟩ =
      A.starToCentral 0 q := by
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage]
  exact (A.centralToSectionSevenEulerPiece_starToCentral 0 q).symm

public theorem cuspFourthSweep_factor {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    (cuspToEllipticUnionMap D).comp (cuspFourthSweep A) =
      (centralFourthPeriodCircleToUnion D).comp (cuspFourthSweepFactor A) := by
  ext1 p
  apply Subtype.ext
  have h := cuspToEllipticUnionMap_central D (cuspFourthSweep A p)
  rw [cuspFourthSweep_central] at h
  have h' := congrArg A.sectionSevenEllipticCentralImageHomeomorph.symm h
  rw [Homeomorph.symm_apply_apply] at h'
  exact congrArg (fun x : A.sectionSevenEllipticCentralImage ↦ x.1) h'


public theorem cuspFourthSweepFactor_projection_zero (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2 productFiberProjection
      (integralSingularHomologyMap 2 (cuspFourthSweepFactor A) x) = 0 := by
  let f : C(UnitAddCircle × StdTorus 1, StdTorus 1) :=
    ⟨fun p _ ↦ p.1, continuous_pi fun _ ↦ continuous_fst⟩
  let g : C(StdTorus 1, TwicePuncturedComplex) :=
    ⟨fun z ↦ A.centralFamilyCoordinate
      (A.starToCentral 0 (cuspFourthSweep A (z 0, 0))),
      A.centralFamilyCoordinate_continuous.comp
        ((A.starToCentral_isOpenEmbedding 0).continuous.comp
          ((cuspFourthSweep A).continuous.comp
            ((continuous_apply 0).prodMk continuous_const)))⟩
  have h : productFiberProjection.comp (cuspFourthSweepFactor A) = g.comp f := rfl
  let : Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
    constructor
    intro x y
    apply (stdTorusHomologyTwo 1).injective
    funext i
    exact Fin.elim0 i
  rw [integralSingularHomologyMap_comp_wang, h, ← integralSingularHomologyMap_comp_wang]
  rw [Subsingleton.elim (integralSingularHomologyMap 2 f x) 0, map_zero]

public theorem cuspFourthSweep_union_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    SectionSevenEllipticTwoDiscHomologyCoordinates.canonicalBoundary R.twoDiscCover 1
      (integralSingularHomologyMap 2 (cuspToEllipticUnionMap R.twoDiscCover)
        (integralSingularHomologyMap 2 (cuspFourthSweep A) x)) = 0 := by
  rw [integralSingularHomologyMap_comp_wang, cuspFourthSweep_factor,
    ← integralSingularHomologyMap_comp_wang]
  exact centralFourthPeriodCircle_boundary_of_projection_zero R _
    (cuspFourthSweepFactor_projection_zero A x)


open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscHomologyCoordinates
private theorem homologyHomeomorphMap_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (k : ℕ)
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyEquiv k e x = integralSingularHomologyMap k (e : C(X, Y)) x := rfl

public theorem cuspToEllipticUnionMap_homology {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    integralSingularHomologyMap 2 (cuspToEllipticUnionMap D) x =
      cuspToEllipticUnionHomology D 2 x := by
  let e := topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
    (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover
  have hm : integralSingularHomologyEquiv 2 e
      (integralSingularHomologyMap 2 (cuspToEllipticUnionMap D) x) =
      integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x := by
    rw [homologyHomeomorphMap_apply, integralSingularHomologyMap_comp_wang]
    rfl
  exact (integralSingularHomologyEquiv 2 e).injective
    (hm.trans (D.cuspToEllipticInteriorMap_homology 2 x))

public theorem cuspFourthSweep_pulled_back_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (integralSingularHomologyMap 2 (cuspFourthSweep A) x) = 0 := by
  rw [cuspPulledBackBoundaryHom_apply,
    ← R.twoDiscCover.canonicalBoundary_cuspToEllipticUnionHomology,
    ← cuspToEllipticUnionMap_homology]
  exact cuspFourthSweep_union_boundary R x

public theorem cuspFourthSweep_to_mapping_torus (A : PaperAnalyticData) :
    A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun.comp (cuspFourthSweep A) =
      fixedLoopMappingTorusMap (cuspFiberClutching _)
        (cuspFourthFixedCircle (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness))) :=
  cuspFixedCircleSweep_to_mapping_torus A _

public theorem cuspFourthSweep_wang (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne
      (actualCuspWangBoundaryHom A
        (integralSingularHomologyMap 2 (cuspFourthSweep A)
          PositiveCircleCross.positiveCircleProductGenerator)) = Pi.single 3 1 := by
  change (cuspMonodromyCoordinates _).degreeOne
    ((circleMappingTorusWangPresentationOfCover _ 1).boundary
      (integralSingularHomologyMap 2 A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 2 (cuspFourthSweep A) _))) = _
  erw [integralSingularHomologyMap_comp_wang, cuspFourthSweep_to_mapping_torus]
  exact CuspRadialClutchingConstruction.cuspFourthSweep_wang _


public theorem cuspRawFive_pulled_back_boundary_zero {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 0 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  let y := integralSingularHomologyMap 2 (cuspFourthSweep A)
    PositiveCircleCross.positiveCircleProductGenerator
  have h : R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) =
      R.twoDiscCover.cuspPulledBackBoundaryHom y := by
    apply cuspPulledBackBoundary_eq_of_wang_eq R
    apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
    rw [actualCuspWangBoundaryHom_rawBasis, AddEquiv.apply_symm_apply]
    rw [show A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
      (actualCuspWangBoundaryHom A y) = Pi.single 3 1 from cuspFourthSweep_wang A]
    ext i
    fin_cases i <;> rfl
  rw [h]
  exact cuspFourthSweep_pulled_back_boundary R _

public theorem actualCuspIndexFiveBoundaryCoefficient_zero {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    actualCuspIndexFiveBoundaryCoefficient R = 0 := by
  rw [actualCuspIndexFiveBoundaryCoefficient, cuspRawFive_pulled_back_boundary_zero, map_zero]

public theorem actualCuspIndexFiveBoundaryCoefficient_not_unit {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ actualCuspIndexFiveBoundaryCoefficient R * actualCuspIndexFiveBoundaryCoefficient R = 1 := by
  rw [actualCuspIndexFiveBoundaryCoefficient_zero]
  norm_num


public theorem not_cuspPulledBackMarkedInvariantBasisData {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ CuspPulledBackMarkedInvariantBasisData R := by
  intro h
  exact actualCuspIndexFiveBoundaryCoefficient_not_unit R
    (actualCuspIndexFiveBoundaryCoefficient_sq_eq_one_of_invariantBasisData R h)

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
