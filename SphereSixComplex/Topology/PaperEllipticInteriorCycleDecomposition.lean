module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization
public import SphereSixComplex.Topology.PaperSectionSevenNormalizedLocalBases

/-!
# Cycle-level comparison at the final cusp attachment

The final inclusion into the elliptic interior is computed before choosing coordinates.  Its
degree-one classes are fibre coinvariants.  Its degree-two classes are the sum of a fibre
coinvariant and the geometrically normalized swept cycle.  These are the exact cycle statements
behind the two interior blocks of the final Section 7 Mayer--Vietoris matrix.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

/-- Local bases using the actual geometric cusp clutching and the normalized elliptic splitting. -/
public noncomputable def sectionSevenActualNormalizedLocalBases
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    A.SectionSevenCollarInteriorHomologyBases :=
  A.withActualGeometricCuspBases
    (A.sectionSevenNormalizedCollarInteriorHomologyBases
      A.actualCuspCollarRadialMappingTorusRealization B S)

/-- Pull the actual cusp-collar inclusion into the literal union used by the elliptic
Mayer--Vietoris presentation. -/
public noncomputable def cuspToEllipticUnionHomology
    (D : A.SectionSevenEllipticTwoDiscCoverData) (k : ℕ)
    (x : IntegralSingularHomology k (A.openEmbeddingStarData.collarSource 0)) :
    IntegralSingularHomology k
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
  (integralSingularHomologyEquiv k
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
    (integralSingularHomologyMap k
      (IntegralMayerVietoris.interToLeft
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3))
      (integralSingularHomologyEquiv k
        A.cuspCollarToSectionSevenFinalOverlapHomeomorph x))

/-- The geometric content of Lemma 7.19 at the remaining cusp boundary.

This records equalities of actual singular-homology cycles in the two-disc Mayer--Vietoris total
groups.  It does not mention the final signed difference map or the homology of the completed
star. -/
public structure SectionSevenEllipticInteriorCycleDecomposition
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) : Prop where
  degreeOne : ∀ x :
      IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
    cuspToEllipticUnionHomology D 1 x =
      (presentationOne (D := D)).coinvariantsToTotal
        ((B.degreeOneCoinvariantEquiv).symm
          (sectionSevenFirstBoundaryHom (A.actualCuspSectionSevenHomologyOneEquiv x) 0))
  degreeTwo : ∀ x :
      IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
    cuspToEllipticUnionHomology D 2 x =
      (presentationTwo (D := D)).coinvariantsToTotal
          ((B.degreeTwoCoinvariantEquiv).symm
            (sectionSevenMayerVietorisFinalTwoHom
              (A.actualCuspSectionSevenHomologyTwoEquiv x) 0)) +
        S.sweptSection
          ((B.degreeTwoInvariantEquiv).symm
            (sectionSevenMayerVietorisFinalTwoHom
              (A.actualCuspSectionSevenHomologyTwoEquiv x) 1))

/-- The first final degree-one coordinate is the raw cusp meridian coordinate. -/
public theorem sectionSevenFirstBoundaryHom_actualCusp_zero
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenFirstBoundaryHom (A.actualCuspSectionSevenHomologyOneEquiv x) 0 =
      A.actualCuspRawHomologyOneEquiv x 2 := by
  simp [actualCuspSectionSevenHomologyOneEquiv, cuspSectionSevenOneCoordinateChange,
    sectionSevenFirstBoundaryHom, sectionSevenFirstBoundaryMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The first final degree-two coordinate is the first raw cusp suspension coordinate. -/
public theorem sectionSevenMayerVietorisFinalTwoHom_actualCusp_zero
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenMayerVietorisFinalTwoHom
        (A.actualCuspSectionSevenHomologyTwoEquiv x) 0 =
      A.actualCuspRawHomologyTwoEquiv x 4 := by
  simp [actualCuspSectionSevenHomologyTwoEquiv, cuspSectionSevenTwoCoordinateChange,
    sectionSevenMayerVietorisFinalTwoHom, sectionSevenMayerVietorisFinalTwoMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The second final degree-two coordinate is the second raw cusp suspension coordinate. -/
public theorem sectionSevenMayerVietorisFinalTwoHom_actualCusp_one
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenMayerVietorisFinalTwoHom
        (A.actualCuspSectionSevenHomologyTwoEquiv x) 1 =
      A.actualCuspRawHomologyTwoEquiv x 5 := by
  simp [actualCuspSectionSevenHomologyTwoEquiv, cuspSectionSevenTwoCoordinateChange,
    sectionSevenMayerVietorisFinalTwoHom, sectionSevenMayerVietorisFinalTwoMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

namespace SectionSevenEllipticInteriorCycleDecomposition

variable {B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D}
  {S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))}

/-- Construct the cycle decomposition from the three scalar identities supplied by a marked
cycle-level comparison. -/
public theorem ofRawScalarCoordinates
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 x) 0 =
        A.actualCuspRawHomologyOneEquiv x 2)
    (hTwoZero : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) 0 =
        A.actualCuspRawHomologyTwoEquiv x 4)
    (hTwoOne : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) 1 =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    A.SectionSevenEllipticInteriorCycleDecomposition B S where
  degreeOne x := by
    apply B.normalizedUnionHomologyOneEquiv.injective
    rw [B.normalizedUnionHomologyOneEquiv_coinvariantsToTotal,
      LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i
    simpa [sectionSevenFirstBoundaryHom_actualCusp_zero] using hOne x
  degreeTwo x := by
    apply (B.normalizedUnionHomologyTwoEquiv S).injective
    rw [B.normalizedUnionHomologyTwoEquiv_add, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i
    · simpa [sectionSevenMayerVietorisFinalTwoHom_actualCusp_zero] using hTwoZero x
    · simpa [sectionSevenMayerVietorisFinalTwoHom_actualCusp_one] using hTwoOne x

variable (C : A.SectionSevenEllipticInteriorCycleDecomposition B S)

include C in
/-- The degree-one cycle decomposition gives the first interior coordinate. -/
public theorem normalizedDegreeOne_onCuspCollar
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 x) =
      ![sectionSevenFirstBoundaryHom (A.actualCuspSectionSevenHomologyOneEquiv x) 0] := by
  rw [C.degreeOne, B.normalizedUnionHomologyOneEquiv_coinvariantsToTotal,
    LinearEquiv.apply_symm_apply]

include C in
/-- The degree-two cycle decomposition gives the fibre and swept-cycle coordinates. -/
public theorem normalizedDegreeTwo_onCuspCollar
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) =
      ![sectionSevenMayerVietorisFinalTwoHom
          (A.actualCuspSectionSevenHomologyTwoEquiv x) 0,
        sectionSevenMayerVietorisFinalTwoHom
          (A.actualCuspSectionSevenHomologyTwoEquiv x) 1] := by
  rw [C.degreeTwo, B.normalizedUnionHomologyTwoEquiv_add,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

include C in
/-- Transport the degree-one comparison from the original cusp collar to the final overlap. -/
public theorem finalInteriorOne (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases
      (A.sectionSevenActualNormalizedLocalBases B S)).interiorOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenFirstBoundaryHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases
          (A.sectionSevenActualNormalizedLocalBases B S)).overlapOne x)
          (Fin.castAdd 2 i) := by
  let e := integralSingularHomologyEquiv 1
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h := C.normalizedDegreeOne_onCuspCollar y
  calc
    _ = ![sectionSevenFirstBoundaryHom
          (A.actualCuspSectionSevenHomologyOneEquiv y) 0] := by
      simpa [e, y, sectionSevenActualNormalizedLocalBases,
        sectionSevenNormalizedCollarInteriorHomologyBases,
        sectionSevenFinalSixHomologyBasesOfLocalBases, sectionSevenFinalSixHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyOneEquiv, normalizedUnionHomologyOneEquiv]
        using h
    _ = _ := by
      funext i
      fin_cases i
      rfl

include C in
/-- Transport the degree-two comparison from the original cusp collar to the final overlap. -/
public theorem finalInteriorTwo (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases
      (A.sectionSevenActualNormalizedLocalBases B S)).interiorTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenMayerVietorisFinalTwoHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases
          (A.sectionSevenActualNormalizedLocalBases B S)).overlapTwo x)
          (Fin.castAdd 4 i) := by
  let e := integralSingularHomologyEquiv 2
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h := C.normalizedDegreeTwo_onCuspCollar y
  calc
    _ = ![sectionSevenMayerVietorisFinalTwoHom
          (A.actualCuspSectionSevenHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom
          (A.actualCuspSectionSevenHomologyTwoEquiv y) 1] := by
      simpa [e, y, sectionSevenActualNormalizedLocalBases,
        sectionSevenNormalizedCollarInteriorHomologyBases,
        sectionSevenFinalSixHomologyBasesOfLocalBases, sectionSevenFinalSixHomologyBases,
        withActualGeometricCuspBases, cuspToEllipticUnionHomology,
        normalizedEllipticInteriorHomologyTwoEquiv, normalizedUnionHomologyTwoEquiv]
        using h
    _ = _ := by
      funext i
      fin_cases i <;> rfl

include C in
/-- The cycle comparison and the already established cusp specialization supply all four actual
final inclusion coordinates. -/
public noncomputable def finalInclusionCoordinates :
    A.SectionSevenFinalInclusionCoordinates
      (A.sectionSevenFinalSixHomologyBasesOfLocalBases
        (A.sectionSevenActualNormalizedLocalBases B S)) :=
  (A.actualCuspFillingInclusionCoordinates
      (A.sectionSevenNormalizedCollarInteriorHomologyBases
        A.actualCuspCollarRadialMappingTorusRealization B S)).toFinalInclusionCoordinates
    C.finalInteriorOne C.finalInteriorTwo

include C in
/-- Assemble the production positive-degree homology package from the cycle-level comparison. -/
public noncomputable def positiveDegreeHomologyAssembly :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  A.sectionSevenPositiveDegreeHomologyAssemblyOfLocalBases
    (A.sectionSevenActualNormalizedLocalBases B S) C.finalInclusionCoordinates

end SectionSevenEllipticInteriorCycleDecomposition

end SphereSixComplex.Geometry.PaperAnalyticData
