module
public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorCycleDecomposition

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

namespace Geometry.AnalyticData
open SphereSixComplex.Topology
open EllipticTwoDiscHomologyCoordinates
open CuspCollar

public def cuspCorrectedHomologyTwoEquiv (A : AnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) :=
  A.cuspRawHomologyTwoEquiv.trans cuspCorrectedSectionSevenTwoCoordinateChange

public def correctedCuspLocalBases {A : AnalyticData}
    (B : A.CollarInteriorHomologyBases) : A.CollarInteriorHomologyBases where
  cuspCollarOne := A.cuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := B.ellipticInteriorOne
  cuspCollarTwo := A.cuspCorrectedHomologyTwoEquiv
  cuspFillingTwo := (A.withActualGeometricCuspBases B).cuspFillingTwo
  ellipticInteriorTwo := B.ellipticInteriorTwo

public theorem correctedCuspFillingInclusionCoordinates (A : AnalyticData)
    (B : A.CollarInteriorHomologyBases) :
    A.CuspFillingInclusionCoordinates (correctedCuspLocalBases B) where
  degreeOne x := (A.cuspFillingInclusionCoordinates B).degreeOne x
  degreeTwo x := by
    change A.actualCuspFillingHomologyTwoEquiv
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    exact (CuspSpecialization.degreeTwo A x).trans
      (cuspCorrectedSectionSevenTwoCoordinateChange_specialization
        (A.cuspRawHomologyTwoEquiv x))

public def correctedNormalizedLocalBases {A : AnalyticData}
    {D : A.EllipticTwoDiscCoverData}
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    A.CollarInteriorHomologyBases :=
  correctedCuspLocalBases (A.actualNormalizedLocalBases B S)

public theorem correctedFinalInteriorOne {A : AnalyticData}
    {D : A.EllipticTwoDiscCoverData}
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ y : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) 0 =
        cuspEllipticDegreeOneRawCoordinate (A.cuspRawHomologyOneEquiv y)) (x) :
    (A.cuspAttachmentHomologyBasesOfLocalBases (correctedNormalizedLocalBases B S)).interiorOne
      (integralSingularHomologyMap 1
        (IntegralMayerVietoris.interToLeft
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenFirstBoundaryHom
        ((A.cuspAttachmentHomologyBasesOfLocalBases
          (correctedNormalizedLocalBases B S)).overlapOne x) (Fin.castAdd 2 i) := by
  let e := integralSingularHomologyEquiv 1 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h : B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) =
      ![sectionSevenFirstBoundaryHom (A.cuspSectionSevenHomologyOneEquiv y) 0] := by
    funext i
    fin_cases i
    exact (hOne y).trans (cuspAttachmentBoundaryOne_actualCusp_zero y).symm
  calc
    _ = ![sectionSevenFirstBoundaryHom (A.cuspSectionSevenHomologyOneEquiv y) 0] := by
      simpa [e, y, correctedNormalizedLocalBases, correctedCuspLocalBases,
        actualNormalizedLocalBases, normalizedCollarInteriorHomologyBases,
        cuspAttachmentHomologyBasesOfLocalBases, cuspAttachmentHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyOneEquiv, normalizedUnionHomologyOneEquiv] using h
    _ = _ := by
      funext i
      fin_cases i
      rfl

public theorem correctedFinalInteriorTwo {A : AnalyticData}
    {D : A.EllipticTwoDiscCoverData}
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hFiber : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 0 =
        12 * A.cuspRawHomologyTwoEquiv y 1 + 2 * A.cuspRawHomologyTwoEquiv y 2 +
          A.cuspRawHomologyTwoEquiv y 5)
    (hBoundary : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 1 =
        A.cuspRawHomologyTwoEquiv y 4) (x) :
    (A.cuspAttachmentHomologyBasesOfLocalBases (correctedNormalizedLocalBases B S)).interiorTwo
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenMayerVietorisFinalTwoHom
        ((A.cuspAttachmentHomologyBasesOfLocalBases
          (correctedNormalizedLocalBases B S)).overlapTwo x) (Fin.castAdd 4 i) := by
  let e := integralSingularHomologyEquiv 2 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h : B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) =
      ![sectionSevenMayerVietorisFinalTwoHom (A.cuspCorrectedHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom (A.cuspCorrectedHomologyTwoEquiv y) 1] := by
    funext i
    fin_cases i
    · exact (hFiber y).trans (cuspCorrectedSectionSevenTwoCoordinateChange_fiber _).symm
    · exact (hBoundary y).trans (cuspCorrectedSectionSevenTwoCoordinateChange_boundary _).symm
  calc
    _ = ![sectionSevenMayerVietorisFinalTwoHom (A.cuspCorrectedHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom (A.cuspCorrectedHomologyTwoEquiv y) 1] := by
      simpa [e, y, correctedNormalizedLocalBases, correctedCuspLocalBases,
        actualNormalizedLocalBases, normalizedCollarInteriorHomologyBases,
        cuspAttachmentHomologyBasesOfLocalBases, cuspAttachmentHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyTwoEquiv, normalizedUnionHomologyTwoEquiv] using h
    _ = _ := by
      funext i
      fin_cases i <;> rfl

public def correctedPositiveDegreeHomologyAssembly {A : AnalyticData}
    {D : A.EllipticTwoDiscCoverData}
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ y : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 y) 0 =
        cuspEllipticDegreeOneRawCoordinate (A.cuspRawHomologyOneEquiv y))
    (hFiber : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 0 =
        12 * A.cuspRawHomologyTwoEquiv y 1 + 2 * A.cuspRawHomologyTwoEquiv y 2 +
          A.cuspRawHomologyTwoEquiv y 5)
    (hBoundary : ∀ y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 y) 1 =
        A.cuspRawHomologyTwoEquiv y 4) :
    A.PositiveDegreeHomologyAssembly :=
  A.positiveDegreeHomologyAssemblyOfLocalBases (correctedNormalizedLocalBases B S)
    ((A.correctedCuspFillingInclusionCoordinates (A.actualNormalizedLocalBases B S)).toFinalInclusionCoordinates
      (correctedFinalInteriorOne B S hOne) (correctedFinalInteriorTwo B S hFiber hBoundary))

end Geometry.AnalyticData
end SphereSixComplex
end
