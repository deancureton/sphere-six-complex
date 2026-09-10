module

public import SphereSixComplex.Paper.Topology.CuspFourthSweepCentralImage
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspActualCoordinateScalarsFromExistingGeometry
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCanonicalCuspFiberRadialHomotopyCompletion

/-!
# Fibre-coordinate parity of the actual fourth-period sweep

The raw Wang section is normalized by toric specialization, so it may differ from the
explicit fourth-period sweep by a fibre class. Such a difference has fibre coordinate
`12 * raw[1] + 2 * raw[2]`. Its evenness constructs a primitive class in the elliptic boundary kernel when the sweep
has odd fibre coordinate. This does not control the cusp specialization of that class.
-/

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology
open SectionSevenEllipticTwoDiscCoverData SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

public def cuspEllipticFiberCoordinate (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ :=
  (coordinateAfterAddEquiv
    (R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S)
      0).comp (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom)

public theorem cuspEllipticFiberCoordinate_raw_fiber (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (i : Fin 4) :
    A.cuspEllipticFiberCoordinate R S
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)) =
      ![0, 12, 2, 0] i := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)
  have hx : integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x =
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
        (Pi.single (Fin.castAdd 2 i) 1) := by
    apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
    rw [← actualCuspRawHomologyTwoEquiv_apply_mappingTorus A x]
    simp [x]
  change R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
    (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom x) 0 = _
  rw [R.twoDiscCover.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x, hx]
  exact congrFun (affineActualCuspDegreeTwoFiberBasis_scalarValues R S
    (canonicalCuspFiberBandTopologicalCompatibility R)) i

public theorem cuspEllipticFiberCoordinate_wang_kernel (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0))
    (hx : actualCuspWangBoundaryHom A x = 0) :
    A.cuspEllipticFiberCoordinate R S x =
      12 * (A.actualCuspRawHomologyTwoEquiv x) 1 +
        2 * (A.actualCuspRawHomologyTwoEquiv x) 2 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  let E := A.actualCuspRawHomologyTwoEquiv
  let u := E x
  have hw := actualCuspWangBoundaryHom_rawCoordinates A x
  dsimp only at hw
  rw [hx, map_zero] at hw
  have h4 : u 4 = 0 := (congrFun hw (2 : Fin 4)).symm
  have h5 : u 5 = 0 := (congrFun hw (3 : Fin 4)).symm
  have hu : u = u 0 • Pi.single (0 : Fin 6) (1 : ℤ) +
      u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 + u 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp [h4, h5]
  have he : x = E.symm (u 0 • Pi.single (0 : Fin 6) (1 : ℤ) +
      u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 + u 3 • Pi.single 3 1) := by
    rw [← hu]
    exact (E.symm_apply_apply x).symm
  conv_lhs => rw [he]
  simp only [map_add, map_zsmul]
  have h0 := A.cuspEllipticFiberCoordinate_raw_fiber R S 0
  have h1 := A.cuspEllipticFiberCoordinate_raw_fiber R S 1
  have h2 := A.cuspEllipticFiberCoordinate_raw_fiber R S 2
  have h3 := A.cuspEllipticFiberCoordinate_raw_fiber R S 3
  change A.cuspEllipticFiberCoordinate R S (E.symm (Pi.single 0 1)) = 0 at h0
  change A.cuspEllipticFiberCoordinate R S (E.symm (Pi.single 1 1)) = 12 at h1
  change A.cuspEllipticFiberCoordinate R S (E.symm (Pi.single 2 1)) = 2 at h2
  change A.cuspEllipticFiberCoordinate R S (E.symm (Pi.single 3 1)) = 0 at h3
  rw [h0, h1, h2, h3]
  change u 0 * 0 + u 1 * 12 + u 2 * 2 + u 3 * 0 = _
  change _ = 12 * u 1 + 2 * u 2
  ring

public def actualCuspFourthSweepClass (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) :=
  integralSingularHomologyMap 2 (actualCuspFourthSweep A)
    PositiveCircleCross.positiveCircleProductGenerator

public theorem actualCuspRawFive_sub_fourthSweep_wang_zero (A : PaperAnalyticData) :
    actualCuspWangBoundaryHom A
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) -
        A.actualCuspFourthSweepClass) = 0 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
  rw [actualCuspWangBoundaryHom_rawBasis, AddEquiv.apply_symm_apply]
  have h := actualCuspFourthSweep_wang A
  change A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
    (actualCuspWangBoundaryHom A A.actualCuspFourthSweepClass) = Pi.single 3 1 at h
  rw [h]
  ext i
  fin_cases i <;> rfl

public theorem actualCuspRawFive_sub_fourthSweep_fiberCoordinate (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    A.cuspEllipticFiberCoordinate R S
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) -
      A.cuspEllipticFiberCoordinate R S A.actualCuspFourthSweepClass =
        12 * (A.actualCuspRawHomologyTwoEquiv
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) -
            A.actualCuspFourthSweepClass)) 1 +
        2 * (A.actualCuspRawHomologyTwoEquiv
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) -
            A.actualCuspFourthSweepClass)) 2 := by
  rw [← map_sub]
  exact A.cuspEllipticFiberCoordinate_wang_kernel R S _
    A.actualCuspRawFive_sub_fourthSweep_wang_zero

public theorem actualCuspRawFive_sub_fourthSweep_fiberCoordinate_even (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    Even (A.cuspEllipticFiberCoordinate R S
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) -
      A.cuspEllipticFiberCoordinate R S A.actualCuspFourthSweepClass) := by
  rw [A.actualCuspRawFive_sub_fourthSweep_fiberCoordinate R S]
  refine ⟨6 * (A.actualCuspRawHomologyTwoEquiv
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) -
      A.actualCuspFourthSweepClass)) 1 +
    (A.actualCuspRawHomologyTwoEquiv
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) -
        A.actualCuspFourthSweepClass)) 2, ?_⟩
  ring

public theorem actualCuspRawFive_fiberCoordinate_odd_of_fourthSweep (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (hs : Odd (A.cuspEllipticFiberCoordinate R S A.actualCuspFourthSweepClass)) :
    Odd (A.cuspEllipticFiberCoordinate R S
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨m, hm⟩ := A.actualCuspRawFive_sub_fourthSweep_fiberCoordinate_even R S
  exact ⟨k + m, by omega⟩

public theorem exists_cuspBoundaryKernel_fiberCoordinate_one_of_fourthSweep_odd
    (A : PaperAnalyticData) (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (hs : Odd (A.cuspEllipticFiberCoordinate R S A.actualCuspFourthSweepClass)) :
    ∃ x, R.twoDiscCover.cuspPulledBackBoundaryHom x = 0 ∧
      A.cuspEllipticFiberCoordinate R S x = 1 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  obtain ⟨k, hk⟩ := A.actualCuspRawFive_fiberCoordinate_odd_of_fourthSweep R S hs
  let b₂ := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (2 : Fin 6) 1)
  let b₅ := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
  have h₂ : A.cuspEllipticFiberCoordinate R S b₂ = 2 :=
    A.cuspEllipticFiberCoordinate_raw_fiber R S 2
  have hb₂ : R.twoDiscCover.cuspPulledBackBoundaryHom b₂ = 0 := by
    apply cuspPulledBackBoundary_eq_zero_of_wang_zero R
    rw [actualCuspWangBoundaryHom_rawBasis]
    rw [show actualCuspWangBoundaryRawBasisCoordinates 2 = 0 by
      ext i
      fin_cases i <;> rfl, map_zero]
  refine ⟨b₅ - k • b₂, ?_, ?_⟩
  · rw [map_sub, map_zsmul, hb₂, smul_zero, sub_zero]
    exact actualCuspRawFive_pulledBack_boundary_zero R
  · rw [map_sub, map_zsmul, h₂]
    change A.cuspEllipticFiberCoordinate R S b₅ - k * 2 = 1
    change A.cuspEllipticFiberCoordinate R S b₅ = 2 * k + 1 at hk
    omega

public theorem actualCuspRawFive_fiberCoordinate_normalization (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    A.cuspEllipticFiberCoordinate R S
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) =
      A.cuspEllipticFiberCoordinate R S A.actualCuspFourthSweepClass -
        12 * (A.actualCuspRawHomologyTwoEquiv A.actualCuspFourthSweepClass) 1 -
        2 * (A.actualCuspRawHomologyTwoEquiv A.actualCuspFourthSweepClass) 2 := by
  have h := A.actualCuspRawFive_sub_fourthSweep_fiberCoordinate R S
  simp only [map_sub, AddEquiv.apply_symm_apply, Pi.sub_apply] at h
  norm_num [Pi.single_apply] at h
  omega

end SphereSixComplex.Geometry.PaperAnalyticData
