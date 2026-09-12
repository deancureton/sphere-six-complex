module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSlice
public import SphereSixComplex.Prerequisites.Topology.RealMappingTorusFiberSlice
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof

@[expose] public section

noncomputable section

open AlgebraicTopology
open CategoryTheory.Limits

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CircleMappingTorusHomologyBases

namespace EllipticTwoDiscCoverData

private theorem circleMappingTorusBoundary_coordinates
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 2 (CircleMappingTorus phi)) :
    B.degreeOne ((circleMappingTorusHTwoPresentation phi).boundary y) =
      ![0, 0, S.circleMappingTorusHTwoAddEquiv y 4,
        S.circleMappingTorusHTwoAddEquiv y 5] := by
  funext i
  fin_cases i
  · simp
    have hb : (circleMonodromyDifference phi 1).toIntLinearMap
        ((circleMappingTorusHTwoPresentation phi).boundary y) = 0 :=
      (circleMappingTorusHTwoPresentation phi).lowDifference_boundary y
    have h := DFunLike.congr_fun B.degreeOneDifference_conjugacy
      ((circleMappingTorusHTwoPresentation phi).boundary y)
    simp only [LinearMap.comp_apply, hb, map_zero] at h
    have hz := (mem_ker_mZeroDifference_iff _).mp (LinearMap.mem_ker.mpr h.symm)
    exact hz.1
  · simp
    have hb : (circleMonodromyDifference phi 1).toIntLinearMap
        ((circleMappingTorusHTwoPresentation phi).boundary y) = 0 :=
      (circleMappingTorusHTwoPresentation phi).lowDifference_boundary y
    have h := DFunLike.congr_fun B.degreeOneDifference_conjugacy
      ((circleMappingTorusHTwoPresentation phi).boundary y)
    simp only [LinearMap.comp_apply, hb, map_zero] at h
    have hz := (mem_ker_mZeroDifference_iff _).mp (LinearMap.mem_ker.mpr h.symm)
    exact hz.2
  · simp
    rw [circleMappingTorusHTwoAddEquiv_apply]
    rfl
  · simp
    rw [circleMappingTorusHTwoAddEquiv_apply]
    rfl

public theorem actualCuspWangBoundaryHom_rawCoordinates
    (A : AnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne (actualCuspWangBoundaryHom A x) =
      ![0, 0, (A.cuspRawHomologyTwoEquiv x) 4,
        (A.cuspRawHomologyTwoEquiv x) 5] := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  exact circleMappingTorusBoundary_coordinates
    A.actualCuspRadialClutchingData.monodromyCoordinates
    A.actualCuspRadialClutchingData.geometricWangSections
    (integralSingularHomologyMap 2
      A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun x)

/-- The marked first-homology coordinates of the Wang boundary on a raw degree-two basis
vector. -/
public def actualCuspWangBoundaryRawBasisCoordinates (i : Fin 6) : Fin 4 → ℤ :=
  ![0, 0, (Pi.single i 1 : Fin 6 → ℤ) 4, (Pi.single i 1 : Fin 6 → ℤ) 5]

/-- The actual Wang boundary on each raw basis vector, expressed as an explicit element of the
marked first homology of the fibre. -/
public theorem actualCuspWangBoundaryHom_rawBasis (A : AnalyticData) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangBoundaryHom A
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
      G.monodromyCoordinates.degreeOne.symm
        (actualCuspWangBoundaryRawBasisCoordinates i) := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
  rw [actualCuspWangBoundaryHom_rawCoordinates]
  simp [actualCuspWangBoundaryRawBasisCoordinates]


private theorem openRadialIntervalProdHomotopyEquiv_apply_snd
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    (p : OpenRadialInterval r × X) :
    openRadialIntervalProdHomotopyEquiv hr p = p.2 := by
  rfl

private theorem totalHomeomorph_actualCuspFullFiberSlice_snd
    {A : AnalyticData} (s : ℂ)
    (hs : ‖SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s‖ <
      A.starCuspWitness.localWitness.radius)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (G.totalHomeomorph (actualCuspFullFiberSlice (A := A) s hs y)).2 =
      SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph G.clutching
        (Quotient.mk
          (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid G.clutching)
          (s.re, y)) := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change (A.actualCuspRadialClutchingData.totalHomeomorph
    (A.actualCuspRadialClutchingData.totalHomeomorph.symm
      (⟨‖SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s‖,
          SphereSixComplex.Geometry.CuspRadialClutchingConstruction.norm_cuspQ_pos s, hs⟩,
        SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph
          A.actualCuspRadialClutchingData.clutching
          (Quotient.mk
            (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid
              A.actualCuspRadialClutchingData.clutching)
            (s.re, y))))).2 = _
  rw [A.actualCuspRadialClutchingData.totalHomeomorph.apply_symm_apply]

private theorem cuspOpenCoverConnectingHom_eq_zero_of_intersection_image
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0))
    (w : IntegralSingularHomology 2
      ((TopologicalSpace.Opens.toTopCat
        (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)))
    (hw : integralSingularHomologyMap 2
      (TopologicalSpace.Opens.inclusion'
        (R.twoDiscCover.cuspOrderThreeOpen ⊓
          R.twoDiscCover.cuspOrderFourOpen)).hom w = x) :
    R.twoDiscCover.cuspOpenCoverConnectingHom x = 0 := by
  let C := R.twoDiscCover.cuspOpenCoverHomologyComparison.toIntegralMayerVietorisData
    R.twoDiscCover.cuspOpenCover
  apply (C.exact_at_union 1 x).2
  let U := R.twoDiscCover.cuspOrderThreeOpen
  let V := R.twoDiscCover.cuspOrderFourOpen
  let u := integralSingularHomologyMap 2
    ((TopologicalSpace.Opens.toTopCat _).map
      (TopologicalSpace.Opens.infLELeft U V)).hom w
  let HU : AddCommGrpCat :=
    (BinaryOpenCover.integralHomologyFunctor 2).obj
      ((TopologicalSpace.Opens.toTopCat _).obj U)
  let HV : AddCommGrpCat :=
    (BinaryOpenCover.integralHomologyFunctor 2).obj
      ((TopologicalSpace.Opens.toTopCat _).obj V)
  let p : ↑(HU ⊞ HV : AddCommGrpCat) :=
    (biprod.inl : HU ⟶ HU ⊞ HV).hom u
  refine ⟨p, ?_⟩
  dsimp [p]
  unfold BinaryOpenCover.integralMVFromBiprod
  rw [← CategoryTheory.comp_apply, biprod.inl_desc]
  change integralSingularHomologyMap 2
    (TopologicalSpace.Opens.inclusion' U).hom u = x
  dsimp [u]
  rw [SphereSixComplex.integralSingularHomologyMap_comp_wang]
  exact hw

private theorem actualCuspWangFiberSlice_to_mappingTorus
    {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.toFun.comp
        ((TopologicalSpace.Opens.inclusion' (R.twoDiscCover.cuspOrderThreeOpen ⊓
          R.twoDiscCover.cuspOrderFourOpen)).hom.comp
          (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R)) =
      CyclicAngularFundamentalDomain.realFiberSlice G.clutching
        (A.cuspAngularLiftPoint (actualCuspFullFiberCrossingTime A)).1.2.re := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  ext y
  change openRadialIntervalProdHomotopyEquiv _
    (A.actualCuspRadialClutchingData.totalHomeomorph
      (((TopologicalSpace.Opens.inclusion' _).hom.comp
        (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R)) y)) = _
  rw [openRadialIntervalProdHomotopyEquiv_apply_snd]
  change (A.actualCuspRadialClutchingData.totalHomeomorph
    (actualCuspFullFiberSlice (A := A)
      (A.cuspAngularLiftPoint (actualCuspFullFiberCrossingTime A)).1.2
      (A.cuspAngularLiftPoint (actualCuspFullFiberCrossingTime A)).2 y)).2 = _
  exact totalHomeomorph_actualCuspFullFiberSlice_snd _ _ y


end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
