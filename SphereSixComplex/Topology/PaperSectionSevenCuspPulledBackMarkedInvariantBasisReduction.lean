module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof

/-!
# Reduction of the cusp invariant-basis evaluations

The mapping-torus cover has two overlap legs.  Its Mayer--Vietoris boundary is antidiagonal: the
high leg is the negative of the low leg.  Consequently, the full connecting class must be
transported as a signed low-minus-high overlap class, rather than as the image of one fibre slice.

The geometric low/high slice comparison is not yet available for the actual cusp cover.  The
structure below records its precise homology-level output: a signed overlap carrier which
simultaneously identifies the two connecting maps and the marked coordinate.  This is the
minimal two-legged comparison needed for the invariant-basis calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- First homology of the actual cusp mapping-torus fibre. -/
public abbrev ActualCuspFiberHomologyOne (A : PaperAnalyticData) :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  IntegralSingularHomology 1 G.Fiber

/-- First homology of the overlap of the two pulled-back cusp-cover pieces. -/
public abbrev CuspCoverIntersectionHomologyOne
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :=
  IntegralSingularHomology 1
    ((TopologicalSpace.Opens.toTopCat
      (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
      (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen))

/-- The exact homology-level output of an oriented low/high overlap comparison.

For a class `a` represented by the first, low Wang leg, `signedOverlap a` represents the
transport of `low_*(a) + high_*(-a)`.  Thus it carries the whole antidiagonal overlap class, not
the image of either slice alone.  The two equations assert compatibility with the connecting map
and with the marked fourth coordinate. -/
public structure ActualCuspWangSignedOverlapComparison
    (R : A.SectionSevenAffineRadialCompletionInput) where
  signedOverlap : ActualCuspFiberHomologyOne A →+ CuspCoverIntersectionHomologyOne R
  boundary :
    signedOverlap.comp (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom
  markedBandDifference :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
        (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp signedOverlap) =
      actualCuspFiberFourthCoordinateHom A

namespace ActualCuspWangSignedOverlapComparison

/-- A signed low/high overlap comparison gives the marked connecting-morphism square. -/
public theorem connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspWangSignedOverlapComparison R) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment := by
  constructor
  rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp, ← C.boundary]
  have h := congrArg (fun q ↦ q.comp (actualCuspWangBoundaryHom A))
    C.markedBandDifference
  simpa only [AddMonoidHom.comp_assoc] using h

/-- A signed low/high overlap comparison implies the two marked invariant-basis evaluations. -/
public theorem invariantBasisData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspWangSignedOverlapComparison R) :
    CuspPulledBackMarkedInvariantBasisData R := by
  have hSquare := (C.connectingNaturality R).square
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

end ActualCuspWangSignedOverlapComparison

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
