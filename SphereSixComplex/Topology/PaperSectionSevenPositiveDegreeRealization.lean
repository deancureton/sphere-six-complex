module

public import SphereSixComplex.Topology.PaperEllipticInteriorCycleDecomposition
public import SphereSixComplex.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

/-!
# Production input for the Section 7 positive-degree calculation

The finite-cover homology calculation is now fixed.  The remaining input is geometric: a radial
two-disc realization, its marked band transport, a swept-cycle splitting, and the cycle comparison
at the cusp boundary.  This module packages exactly those dependent choices and derives the
positive-degree homology assembly without adding a trust boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}

/-- The marked band and cusp-cycle data remaining after the actual finite-cover calculation. -/
public structure SectionSevenEllipticInteriorMarkedCycleData
    (D : A.SectionSevenEllipticTwoDiscCoverData) where
  alignment : A.EllipticBandHomologyAlignment D
  splitting :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))
  cycleDecomposition :
    A.SectionSevenEllipticInteriorCycleDecomposition
      alignment.actualHomologyCoordinates splitting

namespace SectionSevenEllipticInteriorMarkedCycleData

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  (M : A.SectionSevenEllipticInteriorMarkedCycleData D)

/-- Build the marked-cycle package from the three scalar comparisons supplied by a concrete
cycle model. -/
public def ofRawScalarCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1 x) 0 =
        A.actualCuspRawHomologyOneEquiv x 2)
    (hTwoZero : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
          (cuspToEllipticUnionHomology D 2 x) 0 =
        A.actualCuspRawHomologyTwoEquiv x 4)
    (hTwoOne : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
          (cuspToEllipticUnionHomology D 2 x) 1 =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    A.SectionSevenEllipticInteriorMarkedCycleData D where
  alignment := N
  splitting := S
  cycleDecomposition :=
    SectionSevenEllipticInteriorCycleDecomposition.ofRawScalarCoordinates
      hOne hTwoZero hTwoOne

/-- Build the marked-cycle package from a cusp boundary formula and the remaining fibre
coordinate formula.  The included positive cusp `e₅` class determines the swept-cycle section,
so no arbitrary splitting is supplied. -/
public noncomputable def ofCuspBoundaryCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1 x) 0 =
        A.actualCuspRawHomologyOneEquiv x 2)
    (hBoundary : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5)
    (hTwoZero : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates hBoundary)
          (cuspToEllipticUnionHomology D 2 x) 0 =
        A.actualCuspRawHomologyTwoEquiv x 4) :
    A.SectionSevenEllipticInteriorMarkedCycleData D := by
  let B := N.actualHomologyCoordinates
  let S := B.degreeTwoCuspE5SplittingOfCoordinates hBoundary
  apply ofRawScalarCoordinates N S hOne hTwoZero
  intro x
  rw [B.normalizedUnionHomologyTwoEquiv_one]
  exact hBoundary x

/-- The marked-cycle data supplies the production positive-degree homology assembly. -/
public def positiveDegreeHomologyAssembly :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  sectionSevenPositiveDegreeHomologyAssemblyOfActualEllipticData
    M.alignment M.splitting M.cycleDecomposition

end SectionSevenEllipticInteriorMarkedCycleData

/-- The exact remaining geometric realization for the Section 7 positive-degree calculation. -/
public structure SectionSevenPositiveDegreeGeometricRealization (A : PaperAnalyticData) where
  allocation : A.SectionSevenEllipticCentralAllocation
  radial : allocation.RadialRealization
  markedCycles :
    A.SectionSevenEllipticInteriorMarkedCycleData
      radial.toSectionSevenEllipticTwoDiscCoverData

namespace SectionSevenPositiveDegreeGeometricRealization

variable (R : SectionSevenPositiveDegreeGeometricRealization A)

/-- A complete geometric realization discharges the positive-degree Section 7 input. -/
public def positiveDegreeHomologyAssembly :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  R.markedCycles.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeGeometricRealization

end SphereSixComplex.Geometry.PaperAnalyticData
