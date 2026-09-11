module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenNormalizedLocalBases

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

open EllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} {D : A.EllipticTwoDiscCoverData}

/-- The elliptic-interior degree-one coordinate in the raw cusp Wang basis. -/
public def cuspEllipticDegreeOneRawCoordinate (x : Fin 3 → ℤ) : ℤ :=
  12 * x 0 + x 2

/-- The elliptic-interior degree-two fibre coordinate in the raw cusp Wang basis. -/
public def cuspEllipticDegreeTwoFiberRawCoordinate (x : Fin 6 → ℤ) : ℤ :=
  12 * x 1 + 2 * x 2 + x 4

/-- Local bases using the actual geometric cusp clutching and the normalized elliptic splitting. -/
public noncomputable def actualNormalizedLocalBases
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    A.CollarInteriorHomologyBases :=
  A.withActualGeometricCuspBases
    (A.normalizedCollarInteriorHomologyBases
      A.cuspCollarRadialMappingTorusRealization B S)

/-- The geometric content of Lemma 7.19 at the remaining cusp boundary.

This records equalities of actual singular-homology cycles in the two-disc Mayer--Vietoris total
groups.  It does not mention the final signed difference map or the homology of the completed
star. -/
public structure EllipticInteriorCycleDecomposition
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) : Prop where
  degreeOne : ∀ x :
      IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0),
    cuspToEllipticUnionHomology D 1 x =
      (presentationOne (D := D)).coinvariantsToTotal
        ((B.degreeOneCoinvariantEquiv).symm
          (sectionSevenFirstBoundaryHom (A.cuspSectionSevenHomologyOneEquiv x) 0))
  degreeTwo : ∀ x :
      IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
    cuspToEllipticUnionHomology D 2 x =
      (presentationTwo (D := D)).coinvariantsToTotal
          ((B.degreeTwoCoinvariantEquiv).symm
            (sectionSevenMayerVietorisFinalTwoHom
              (A.cuspSectionSevenHomologyTwoEquiv x) 0)) +
        S.sweptSection
          ((B.degreeTwoInvariantEquiv).symm
            (sectionSevenMayerVietorisFinalTwoHom
              (A.cuspSectionSevenHomologyTwoEquiv x) 1))

/-- The first final degree-one coordinate is the corrected elliptic cusp functional. -/
public theorem cuspAttachmentBoundaryOne_actualCusp_zero
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenFirstBoundaryHom (A.cuspSectionSevenHomologyOneEquiv x) 0 =
      cuspEllipticDegreeOneRawCoordinate (A.cuspRawHomologyOneEquiv x) := by
  simp [cuspSectionSevenHomologyOneEquiv, cuspSectionSevenOneCoordinateChange,
    cuspEllipticDegreeOneRawCoordinate,
    sectionSevenFirstBoundaryHom, sectionSevenFirstBoundaryMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The first final degree-two coordinate is the corrected elliptic cusp fibre functional. -/
public theorem cuspAttachmentBoundaryTwo_actualCusp_zero
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenMayerVietorisFinalTwoHom
        (A.cuspSectionSevenHomologyTwoEquiv x) 0 =
      cuspEllipticDegreeTwoFiberRawCoordinate (A.cuspRawHomologyTwoEquiv x) := by
  simp [cuspSectionSevenHomologyTwoEquiv, cuspSectionSevenTwoCoordinateChange,
    cuspEllipticDegreeTwoFiberRawCoordinate,
    sectionSevenMayerVietorisFinalTwoHom, sectionSevenMayerVietorisFinalTwoMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The second final degree-two coordinate is the second raw cusp suspension coordinate. -/
public theorem cuspAttachmentBoundaryTwo_actualCusp_one
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    sectionSevenMayerVietorisFinalTwoHom
        (A.cuspSectionSevenHomologyTwoEquiv x) 1 =
      A.cuspRawHomologyTwoEquiv x 5 := by
  simp [cuspSectionSevenHomologyTwoEquiv, cuspSectionSevenTwoCoordinateChange,
    sectionSevenMayerVietorisFinalTwoHom, sectionSevenMayerVietorisFinalTwoMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

namespace EllipticInteriorCycleDecomposition

variable {B : A.EllipticTwoDiscHomologyCoordinates D}
  {S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))}

/-- Construct the cycle decomposition from the three scalar identities supplied by a marked
cycle-level comparison. -/
public theorem ofRawScalarCoordinates
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 x) 0 =
        cuspEllipticDegreeOneRawCoordinate (A.cuspRawHomologyOneEquiv x))
    (hTwoFiber : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) 0 =
        cuspEllipticDegreeTwoFiberRawCoordinate (A.cuspRawHomologyTwoEquiv x))
    (hTwoOne : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) 1 =
        A.cuspRawHomologyTwoEquiv x 5) :
    A.EllipticInteriorCycleDecomposition B S where
  degreeOne x := by
    apply B.normalizedUnionHomologyOneEquiv.injective
    rw [B.normalizedUnionHomologyOneEquiv_coinvariantsToTotal,
      LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i
    simpa [cuspAttachmentBoundaryOne_actualCusp_zero] using hOne x
  degreeTwo x := by
    apply (B.normalizedUnionHomologyTwoEquiv S).injective
    rw [B.normalizedUnionHomologyTwoEquiv_add, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i
    · simpa [cuspAttachmentBoundaryTwo_actualCusp_zero] using hTwoFiber x
    · simpa [cuspAttachmentBoundaryTwo_actualCusp_one] using hTwoOne x

variable (C : A.EllipticInteriorCycleDecomposition B S)

include C in
/-- The degree-one cycle decomposition gives the first interior coordinate. -/
public theorem normalizedDegreeOne_onCuspCollar
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    B.normalizedUnionHomologyOneEquiv (cuspToEllipticUnionHomology D 1 x) =
      ![sectionSevenFirstBoundaryHom (A.cuspSectionSevenHomologyOneEquiv x) 0] := by
  rw [C.degreeOne, B.normalizedUnionHomologyOneEquiv_coinvariantsToTotal,
    LinearEquiv.apply_symm_apply]

include C in
/-- The degree-two cycle decomposition gives the fibre and swept-cycle coordinates. -/
public theorem normalizedDegreeTwo_onCuspCollar
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    B.normalizedUnionHomologyTwoEquiv S (cuspToEllipticUnionHomology D 2 x) =
      ![sectionSevenMayerVietorisFinalTwoHom
          (A.cuspSectionSevenHomologyTwoEquiv x) 0,
        sectionSevenMayerVietorisFinalTwoHom
          (A.cuspSectionSevenHomologyTwoEquiv x) 1] := by
  rw [C.degreeTwo, B.normalizedUnionHomologyTwoEquiv_add,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

include C in
/-- Transport the degree-one comparison from the original cusp collar to the final overlap. -/
public theorem finalInteriorOne (x) :
    (A.cuspAttachmentHomologyBasesOfLocalBases
      (A.actualNormalizedLocalBases B S)).interiorOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenFirstBoundaryHom
        ((A.cuspAttachmentHomologyBasesOfLocalBases
          (A.actualNormalizedLocalBases B S)).overlapOne x)
          (Fin.castAdd 2 i) := by
  let e := integralSingularHomologyEquiv 1
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h := C.normalizedDegreeOne_onCuspCollar y
  calc
    _ = ![sectionSevenFirstBoundaryHom
          (A.cuspSectionSevenHomologyOneEquiv y) 0] := by
      simpa [e, y, actualNormalizedLocalBases,
        normalizedCollarInteriorHomologyBases,
        cuspAttachmentHomologyBasesOfLocalBases, cuspAttachmentHomologyBases,
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
    (A.cuspAttachmentHomologyBasesOfLocalBases
      (A.actualNormalizedLocalBases B S)).interiorTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ sectionSevenMayerVietorisFinalTwoHom
        ((A.cuspAttachmentHomologyBasesOfLocalBases
          (A.actualNormalizedLocalBases B S)).overlapTwo x)
          (Fin.castAdd 4 i) := by
  let e := integralSingularHomologyEquiv 2
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let y := e.symm x
  have h := C.normalizedDegreeTwo_onCuspCollar y
  calc
    _ = ![sectionSevenMayerVietorisFinalTwoHom
          (A.cuspSectionSevenHomologyTwoEquiv y) 0,
        sectionSevenMayerVietorisFinalTwoHom
          (A.cuspSectionSevenHomologyTwoEquiv y) 1] := by
      simpa [e, y, actualNormalizedLocalBases,
        normalizedCollarInteriorHomologyBases,
        cuspAttachmentHomologyBasesOfLocalBases, cuspAttachmentHomologyBases,
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
    A.CuspAttachmentInclusionCoordinates
      (A.cuspAttachmentHomologyBasesOfLocalBases
        (A.actualNormalizedLocalBases B S)) :=
  (A.cuspFillingInclusionCoordinates
      (A.normalizedCollarInteriorHomologyBases
        A.cuspCollarRadialMappingTorusRealization B S)).toFinalInclusionCoordinates
    C.finalInteriorOne C.finalInteriorTwo

include C in
/-- Assemble the production positive-degree homology package from the cycle-level comparison. -/
public noncomputable def positiveDegreeHomologyAssembly :
    A.PositiveDegreeHomologyAssembly :=
  A.positiveDegreeHomologyAssemblyOfLocalBases
    (A.actualNormalizedLocalBases B S) C.finalInclusionCoordinates

end EllipticInteriorCycleDecomposition

/-- Once the actual finite-cover calculations are fixed, band naturality, a normalized swept
section, and the three cycle identities are the complete positive-degree input. -/
public noncomputable def positiveDegreeHomologyAssemblyOfActualEllipticData
    (N : A.EllipticBandHomologyAlignment D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (C : A.EllipticInteriorCycleDecomposition N.actualHomologyCoordinates S) :
    A.PositiveDegreeHomologyAssembly :=
  C.positiveDegreeHomologyAssembly

end SphereSixComplex.Geometry.PaperAnalyticData
