module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice
public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationProof

@[expose] public section

noncomputable section

open AlgebraicTopology
open CategoryTheory.Limits

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CircleMappingTorusHomologyBases

namespace SectionSevenEllipticTwoDiscCoverData

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
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne (actualCuspWangBoundaryHom A x) =
      ![0, 0, (A.actualCuspRawHomologyTwoEquiv x) 4,
        (A.actualCuspRawHomologyTwoEquiv x) 5] := by
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
public theorem actualCuspWangBoundaryHom_rawBasis (A : PaperAnalyticData) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangBoundaryHom A
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
      G.monodromyCoordinates.degreeOne.symm
        (actualCuspWangBoundaryRawBasisCoordinates i) := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
  rw [actualCuspWangBoundaryHom_rawCoordinates]
  simp [actualCuspWangBoundaryRawBasisCoordinates]

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_castAdd (i : Fin 4) :
    actualCuspWangBoundaryRawBasisCoordinates (Fin.castAdd 2 i) = 0 := by
  fin_cases i <;> simp [actualCuspWangBoundaryRawBasisCoordinates]

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_four :
    actualCuspWangBoundaryRawBasisCoordinates (4 : Fin 6) = ![0, 0, 1, 0] := by
  rfl

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_five :
    actualCuspWangBoundaryRawBasisCoordinates (5 : Fin 6) = ![0, 0, 0, 1] := by
  rfl

/-- The explicit value occurring for the first four raw basis vectors maps to zero in the
cover intersection. -/
public theorem actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm 0) = 0 := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  simp only [map_zero]

private theorem openRadialIntervalProdHomotopyEquiv_apply_snd
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    (p : OpenRadialInterval r × X) :
    openRadialIntervalProdHomotopyEquiv hr p = p.2 := by
  rfl

private theorem totalHomeomorph_actualCuspFullFibreSlice_snd
    {A : PaperAnalyticData} (s : ℂ)
    (hs : ‖SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s‖ <
      A.starCuspWitness.localWitness.radius)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (G.totalHomeomorph (actualCuspFullFibreSlice (A := A) s hs y)).2 =
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

private def circleMappingTorusRealFibreSlice
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    C(F, CircleMappingTorus phi) :=
  ⟨fun y ↦ SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (Quotient.mk
        (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid phi) (a, y)),
    (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp (continuous_const.prodMk continuous_id))⟩

private def circleMappingTorusRealFibreSliceHomotopy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    ContinuousMap.Homotopy (circleMappingTorusRealFibreSlice phi a)
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) where
  toFun q :=
    SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (Quotient.mk
        (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
        ((1 - (q.1 : ℝ)) * a, q.2))
  continuous_toFun :=
    (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          continuous_const).prodMk continuous_snd))
  map_zero_left x := by
    simp [circleMappingTorusRealFibreSlice]
  map_one_left x := by
    simpa using
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.realMappingTorusHomeomorph_mk_zero
        phi x

private theorem cuspOpenCoverConnectingHom_eq_zero_of_intersection_image
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
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

private theorem actualCuspWangFibreSlice_to_mappingTorus
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.toFun.comp
        ((TopologicalSpace.Opens.inclusion' (R.twoDiscCover.cuspOrderThreeOpen ⊓
          R.twoDiscCover.cuspOrderFourOpen)).hom.comp
          (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) =
      circleMappingTorusRealFibreSlice G.clutching
        (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).1.2.re := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  ext y
  change openRadialIntervalProdHomotopyEquiv _
    (A.actualCuspRadialClutchingData.totalHomeomorph
      (((TopologicalSpace.Opens.inclusion' _).hom.comp
        (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) y)) = _
  rw [openRadialIntervalProdHomotopyEquiv_apply_snd]
  change (A.actualCuspRadialClutchingData.totalHomeomorph
    (actualCuspFullFibreSlice (A := A)
      (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).1.2
      (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).2 y)).2 = _
  exact totalHomeomorph_actualCuspFullFibreSlice_snd _ _ y

private theorem actualCuspRawCastAdd_mem_cuspCoverIntersectionImage
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
    (i : Fin 4) :
    ∃ w : IntegralSingularHomology 2
        ((TopologicalSpace.Opens.toTopCat
          (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)),
      integralSingularHomologyMap 2
          (TopologicalSpace.Opens.inclusion'
            (R.twoDiscCover.cuspOrderThreeOpen ⊓
              R.twoDiscCover.cuspOrderFourOpen)).hom w =
        A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := A.actualCuspRawHomologyTwoEquiv.symm
    (Pi.single (Fin.castAdd 2 i) 1)
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let y := e x
  let P := circleMappingTorusHTwoPresentation G.clutching
  have hb : P.boundary y = 0 := by
    change actualCuspWangBoundaryHom A x = 0
    rw [actualCuspWangBoundaryHom_rawBasis,
      actualCuspWangBoundaryRawBasisCoordinates_castAdd]
    exact G.monodromyCoordinates.degreeOne.symm.map_zero
  have hy : y ∈ Set.range P.inclusion := by
    exact (P.exact_inclusion_boundary y).mp hb
  obtain ⟨z, hz⟩ := hy
  let w := integralSingularHomologyMap 2
    (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R) z
  refine ⟨w, ?_⟩
  apply e.injective
  change integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 2
        (TopologicalSpace.Opens.inclusion'
          (R.twoDiscCover.cuspOrderThreeOpen ⊓
            R.twoDiscCover.cuspOrderFourOpen)).hom
        (integralSingularHomologyMap 2
          (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R) z)) = y
  have hsquare := congrArg (fun f ↦ f z)
    (congrArg (integralSingularHomologyMap 2)
      (actualCuspWangFibreSlice_to_mappingTorus R))
  calc
    _ = integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 2
          ((TopologicalSpace.Opens.inclusion'
            (R.twoDiscCover.cuspOrderThreeOpen ⊓
              R.twoDiscCover.cuspOrderFourOpen)).hom.comp
            (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) z) := by
      rw [← SphereSixComplex.integralSingularHomologyMap_comp_wang]
    _ = integralSingularHomologyMap 2
        (G.totalHomotopyEquiv.toFun.comp
          ((TopologicalSpace.Opens.inclusion'
            (R.twoDiscCover.cuspOrderThreeOpen ⊓
              R.twoDiscCover.cuspOrderFourOpen)).hom.comp
            (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R))) z :=
      SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _
    _ = integralSingularHomologyMap 2
        (circleMappingTorusRealFibreSlice G.clutching
          (A.actualCuspAngularLiftPoint
            (actualCuspFullFibreCrossingTime A)).1.2.re) z := hsquare
    _ = integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) z := by
      rw [integralSingularHomologyMap_eq_of_homotopy 2
        (circleMappingTorusRealFibreSliceHomotopy G.clutching
          (A.actualCuspAngularLiftPoint
            (actualCuspFullFibreCrossingTime A)).1.2.re)]
    _ = y := hz

/-- The four raw degree-two basis vectors with zero Wang boundary are represented by the
full-fibre slice inside the cusp-cover intersection, so their cover connecting classes vanish. -/
public theorem cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
    (i : Fin 4) :
    R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1)) = 0 := by
  obtain ⟨w, hw⟩ := actualCuspRawCastAdd_mem_cuspCoverIntersectionImage R i
  exact cuspOpenCoverConnectingHom_eq_zero_of_intersection_image R _ w hw

/-- The remaining comparison after evaluating the Wang boundary on all six raw basis vectors.
It involves only the explicit full-fibre images of two invariant generators and four zeros. -/
public def ActualCuspWangFullFibreSliceExplicitFiniteResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  (∀ i : Fin 4,
    R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)) = 0) ∧
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm
          ![0, 0, 1, 0]) =
      R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) ∧
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm
          ![0, 0, 0, 1]) =
      R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- After exactness kills the four zero-boundary basis vectors, only the two invariant
degree-two generators remain to be compared with the cover boundary. -/
public def ActualCuspWangFullFibreSliceInvariantResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
      (G.monodromyCoordinates.degreeOne.symm ![0, 0, 1, 0]) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) ∧
  actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
      (G.monodromyCoordinates.degreeOne.symm ![0, 0, 0, 1]) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- The former six-equation residual is equivalent to the strictly smaller pair of invariant
generator comparisons. -/
public theorem explicitFiniteResidual_iff_invariantResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspWangFullFibreSliceExplicitFiniteResidual R ↔
      ActualCuspWangFullFibreSliceInvariantResidual R := by
  dsimp [ActualCuspWangFullFibreSliceExplicitFiniteResidual,
    ActualCuspWangFullFibreSliceInvariantResidual]
  constructor
  · rintro ⟨_, hfour, hfive⟩
    exact ⟨hfour, hfive⟩
  · rintro ⟨hfour, hfive⟩
    exact ⟨cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero R, hfour, hfive⟩

/-- The original six basis comparisons are equivalent to the finite residual in which the Wang
boundary has been completely evaluated. -/
public theorem wangBoundaryBasisComparison_iff_explicitFiniteResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     ∀ i : Fin 6,
       ((actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
           (actualCuspWangBoundaryHom A))
             (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
         R.twoDiscCover.cuspOpenCoverConnectingHom
           (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) ↔
      ActualCuspWangFullFibreSliceExplicitFiniteResidual R := by
  dsimp [ActualCuspWangFullFibreSliceExplicitFiniteResidual]
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  simp only [actualCuspWangBoundaryHom_rawBasis]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := (h (Fin.castAdd 2 i)).symm
      rw [actualCuspWangBoundaryRawBasisCoordinates_castAdd] at hi
      exact hi.trans
        (actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero R)
    · simpa only [actualCuspWangBoundaryRawBasisCoordinates_four] using h 4
    · simpa only [actualCuspWangBoundaryRawBasisCoordinates_five] using h 5
  · rintro ⟨hzero, hfour, hfive⟩ i
    by_cases hi : i.val < 4
    · let j : Fin 4 := ⟨i.val, hi⟩
      have hij : Fin.castAdd 2 j = i := Fin.ext rfl
      rw [← hij, actualCuspWangBoundaryRawBasisCoordinates_castAdd,
        actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero, hzero j]
    · have hi45 : i = 4 ∨ i = 5 := by omega
      rcases hi45 with rfl | rfl
      · exact hfour
      · exact hfive

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
