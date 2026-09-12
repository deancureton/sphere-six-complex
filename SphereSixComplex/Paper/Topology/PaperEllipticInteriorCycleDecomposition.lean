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

namespace SphereSixComplex.Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates

variable {A : AnalyticData} {D : A.EllipticTwoDiscCoverData}

/-- The elliptic-interior degree-one coordinate in the raw cusp Wang basis. -/
public def cuspEllipticDegreeOneRawCoordinate (x : Fin 3 → ℤ) : ℤ :=
  12 * x 0 + x 2


/-- Local bases using the actual geometric cusp clutching and the normalized elliptic splitting. -/
public noncomputable def actualNormalizedLocalBases
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    A.CollarInteriorHomologyBases :=
  A.withActualGeometricCuspBases
    (A.normalizedCollarInteriorHomologyBases
      A.cuspCollarRadialMappingTorusRealization B S)


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



end SphereSixComplex.Geometry.AnalyticData
