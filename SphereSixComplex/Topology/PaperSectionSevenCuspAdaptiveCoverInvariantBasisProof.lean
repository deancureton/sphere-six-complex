module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveSectorBounds
public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverOrientationObstruction
public import SphereSixComplex.Topology.PaperSectionSevenCuspSwappedCoverGeometryProof
public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspWangBoundaryNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedInvariantBasisFromFullFibreNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedBoundaryExactResidual

/-!
# The adaptive cusp cover and its exact marked residual

Neither fixed vertex--edge orientation refines the affine cusp cover.  The honest adaptive
cover is therefore the pullback of the two affine height opens themselves.  This file records
its Mayer--Vietoris naturality square and identifies the exact remaining marked comparison with
the canonical period-marked Wang boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The Mayer--Vietoris boundary of the genuine height-preimage cover is natural under the
radial mapping-torus equivalence.  This uses the exact pullback cover, rather than either of the
two refuted fixed vertex--edge refinements. -/
public theorem actualCuspHeightPreimageCover_boundary_naturality
    (R : A.SectionSevenAffineRadialCompletionInput) (n : ℕ) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundary n ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
          (actualCuspMappingTorusToCollarTopCatMap A)
          R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen n =
      (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (actualCuspMappingTorusToCollarTopCatMap A) ≫
        R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary n := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
    (actualCuspMappingTorusToCollarTopCatMap A)
    R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen
    (actualCuspMappingTorusPulledBackHomologyComparison R)
    R.twoDiscCover.cuspOpenCoverHomologyComparison
    (SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen
      (actualCuspMappingTorusPulledBackOpenCover R)
      R.twoDiscCover.cuspOpenCover) n

/-- The canonical map from the actual cusp fibre to the elliptic overlap preserves the fourth
period coordinate. -/
public theorem canonicalCuspFiberToBand_fourthCoordinate
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
        R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspFiberFourthCoordinateHom A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hMarking :
      R.twoDiscCover.CanonicalCuspFiberBandPeriodMarking R.homologyAlignment :=
    R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree R.homologyAlignment
      (R.canonicalCuspFiberOrderThreePeriodMarking
        (actualCuspFiberPeriodMarkingCompatibility A))
  apply AddMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hMarking x
  change
    R.homologyAlignment.actualHomologyCoordinates.bandOne
        (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne x) 3 =
      G.monodromyCoordinates.degreeOne x 3
  exact congrFun hx 3

/-- The two invariant-basis evaluations are equivalent to one honest marked naturality square:
the Mayer--Vietoris boundary of the height-preimage cover agrees, after the fourth period
coordinate, with the canonical Wang boundary. -/
public theorem
    cuspPulledBackMarkedInvariantBasisData_iff_canonicalMarkedHeightPreimageBoundary
    (R : A.SectionSevenAffineRadialCompletionInput) :
    CuspPulledBackMarkedInvariantBasisData R ↔
      (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
          R.twoDiscCover.cuspPulledBackBoundaryHom =
        (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
          (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne.comp
            (actualCuspWangBoundaryHom A)) := by
  rw [cuspPulledBackMarkedInvariantBasisData_iff_markedConnectingNaturality]
  constructor
  · intro h
    rw [h.square, ← AddMonoidHom.comp_assoc,
      canonicalCuspFiberToBand_fourthCoordinate R]
  · intro h
    constructor
    rw [h, ← AddMonoidHom.comp_assoc,
      canonicalCuspFiberToBand_fourthCoordinate R]

/-- Thus the remaining unmarked Wang-boundary comparison is sufficient for the invariant-basis
calculation.  The cover in this statement is the genuine height-preimage cover above, so this
does not assume either impossible fixed refinement. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_canonicalHeightPreimageBoundary
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : R.twoDiscCover.CanonicalCuspWangBoundaryNaturality) :
    CuspPulledBackMarkedInvariantBasisData R := by
  apply
    (cuspPulledBackMarkedInvariantBasisData_iff_canonicalMarkedHeightPreimageBoundary R).2
  rw [CanonicalCuspWangBoundaryNaturality] at h
  rw [h]

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
