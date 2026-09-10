module
public import SphereSixComplex.Topology.PaperEllipticInteriorCycleDecomposition

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex

public def cuspCorrectedSectionSevenTwoCoordinateChange : (Fin 6 → ℤ) ≃+ (Fin 6 → ℤ) where
  toFun x := ![x 5, x 4, -x 0, -x 1, -x 2, x 3]
  invFun y := ![-y 2, -y 3, -y 4, y 5, y 1, y 0]
  map_add' x y := by funext i; fin_cases i <;> simp <;> abel
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv y := by funext i; fin_cases i <;> simp

public theorem cuspCorrectedSectionSevenTwoCoordinateChange_fiber (x : Fin 6 → ℤ) :
    sectionSevenMayerVietorisFinalTwoHom (cuspCorrectedSectionSevenTwoCoordinateChange x) 0 =
      12 * x 1 + 2 * x 2 + x 5 := by
  simp [cuspCorrectedSectionSevenTwoCoordinateChange, sectionSevenMayerVietorisFinalTwoHom,
    sectionSevenMayerVietorisFinalTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

public theorem cuspCorrectedSectionSevenTwoCoordinateChange_boundary (x : Fin 6 → ℤ) :
    sectionSevenMayerVietorisFinalTwoHom (cuspCorrectedSectionSevenTwoCoordinateChange x) 1 = x 4 := by
  simp [cuspCorrectedSectionSevenTwoCoordinateChange, sectionSevenMayerVietorisFinalTwoHom,
    sectionSevenMayerVietorisFinalTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem cuspCorrectedSectionSevenTwoCoordinateChange_specialization (x : Fin 6 → ℤ) :
    (fun i : Fin 4 ↦ x (Fin.castAdd 2 i)) =
      fun i ↦ -sectionSevenMayerVietorisFinalTwoHom
        (cuspCorrectedSectionSevenTwoCoordinateChange x) (Fin.natAdd 2 i) := by
  funext i
  fin_cases i <;>
    simp [cuspCorrectedSectionSevenTwoCoordinateChange, sectionSevenMayerVietorisFinalTwoHom,
      sectionSevenMayerVietorisFinalTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

namespace Geometry.PaperAnalyticData
open SphereSixComplex.Topology
open SectionSevenEllipticTwoDiscHomologyCoordinates
open CuspPuncturedCollarBridge

public def actualCuspCorrectedHomologyTwoEquiv (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) :=
  A.actualCuspRawHomologyTwoEquiv.trans cuspCorrectedSectionSevenTwoCoordinateChange

public def correctedCuspLocalBases {A : PaperAnalyticData}
    (B : A.SectionSevenCollarInteriorHomologyBases) : A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := A.actualCuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := B.ellipticInteriorOne
  cuspCollarTwo := A.actualCuspCorrectedHomologyTwoEquiv
  cuspFillingTwo := (A.withActualGeometricCuspBases B).cuspFillingTwo
  ellipticInteriorTwo := B.ellipticInteriorTwo

public theorem correctedCuspFillingInclusionCoordinates (A : PaperAnalyticData)
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.ActualCuspFillingInclusionCoordinates (correctedCuspLocalBases B) where
  degreeOne x := (A.actualCuspFillingInclusionCoordinates B).degreeOne x
  degreeTwo x := by
    change actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    rw [EstablishedStandardA2CuspSpecialization.degreeTwo A x]
    exact cuspCorrectedSectionSevenTwoCoordinateChange_specialization
      (A.actualCuspRawHomologyTwoEquiv x)

public def correctedNormalizedLocalBases {A : PaperAnalyticData}
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    A.SectionSevenCollarInteriorHomologyBases :=
  correctedCuspLocalBases (A.sectionSevenActualNormalizedLocalBases B S)

public theorem correctedFinalInteriorOne {A : PaperAnalyticData}
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ y : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv y)) (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases (correctedNormalizedLocalBases B S)).interiorOne
      (integralSingularHomologyMap 1
        (IntegralMayerVietoris.interToLeft
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenFirstBoundaryHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases
          (correctedNormalizedLocalBases B S)).overlapOne x) (Fin.castAdd 2 i) := by
  let e := integralSingularHomologyEquiv 1 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h : B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) =
      ![sectionSevenFirstBoundaryHom (A.actualCuspSectionSevenHomologyOneEquiv y) 0] := by
    funext i
    fin_cases i
    exact (hOne y).trans (sectionSevenFirstBoundaryHom_actualCusp_zero y).symm
  calc
    _ = ![sectionSevenFirstBoundaryHom (A.actualCuspSectionSevenHomologyOneEquiv y) 0] := by
      simpa [e, y, correctedNormalizedLocalBases, correctedCuspLocalBases,
        sectionSevenActualNormalizedLocalBases, sectionSevenNormalizedCollarInteriorHomologyBases,
        sectionSevenFinalSixHomologyBasesOfLocalBases, sectionSevenFinalSixHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyOneEquiv, normalizedUnionHomologyOneEquiv] using h
    _ = _ := by
      funext i
      fin_cases i
      rfl

public theorem correctedFinalInteriorTwo {A : PaperAnalyticData}
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hFiber : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 0 =
        12 * A.actualCuspRawHomologyTwoEquiv y 1 + 2 * A.actualCuspRawHomologyTwoEquiv y 2 +
          A.actualCuspRawHomologyTwoEquiv y 5)
    (hBoundary : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 1 =
        A.actualCuspRawHomologyTwoEquiv y 4) (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases (correctedNormalizedLocalBases B S)).interiorTwo
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenMayerVietorisFinalTwoHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases
          (correctedNormalizedLocalBases B S)).overlapTwo x) (Fin.castAdd 4 i) := by
  let e := integralSingularHomologyEquiv 2 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h : B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) =
      ![sectionSevenMayerVietorisFinalTwoHom (A.actualCuspCorrectedHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom (A.actualCuspCorrectedHomologyTwoEquiv y) 1] := by
    funext i
    fin_cases i
    · exact (hFiber y).trans (cuspCorrectedSectionSevenTwoCoordinateChange_fiber _).symm
    · exact (hBoundary y).trans (cuspCorrectedSectionSevenTwoCoordinateChange_boundary _).symm
  calc
    _ = ![sectionSevenMayerVietorisFinalTwoHom (A.actualCuspCorrectedHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom (A.actualCuspCorrectedHomologyTwoEquiv y) 1] := by
      simpa [e, y, correctedNormalizedLocalBases, correctedCuspLocalBases,
        sectionSevenActualNormalizedLocalBases, sectionSevenNormalizedCollarInteriorHomologyBases,
        sectionSevenFinalSixHomologyBasesOfLocalBases, sectionSevenFinalSixHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyTwoEquiv, normalizedUnionHomologyTwoEquiv] using h
    _ = _ := by
      funext i
      fin_cases i <;> rfl

public def correctedPositiveDegreeHomologyAssembly {A : PaperAnalyticData}
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ y : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv y))
    (hFiber : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 0 =
        12 * A.actualCuspRawHomologyTwoEquiv y 1 + 2 * A.actualCuspRawHomologyTwoEquiv y 2 +
          A.actualCuspRawHomologyTwoEquiv y 5)
    (hBoundary : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 1 =
        A.actualCuspRawHomologyTwoEquiv y 4) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  A.sectionSevenPositiveDegreeHomologyAssemblyOfLocalBases (correctedNormalizedLocalBases B S)
    ((A.correctedCuspFillingInclusionCoordinates (A.sectionSevenActualNormalizedLocalBases B S)).toFinalInclusionCoordinates
      (correctedFinalInteriorOne B S hOne) (correctedFinalInteriorTwo B S hFiber hBoundary))

end Geometry.PaperAnalyticData
end SphereSixComplex
end
