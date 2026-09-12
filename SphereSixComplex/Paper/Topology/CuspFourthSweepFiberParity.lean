module

public import SphereSixComplex.Paper.Topology.CuspFourthSweepCentralImage
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspActualCoordinateScalarsFromExistingGeometry
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport
public import SphereSixComplex.Prerequisites.Topology.RealMappingTorusFiberSlice

/-!
# The elliptic fiber coordinate and fourth-period sweep class

These definitions record the fiber coordinate associated with a chosen normalized elliptic Wang
splitting and the actual fourth-period sweep class in the cusp collar.
-/

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology
open EllipticTwoDiscCoverData EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

public def cuspEllipticFiberCoordinate (A : AnalyticData)
    (R : A.AffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ :=
  (coordinateAfterAddEquiv
    (R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S)
      0).comp (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom)


public def cuspFourthSweepClass (A : AnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) :=
  integralSingularHomologyMap 2 (cuspFourthSweep A)
    PositiveCircleCross.positiveCircleProductGenerator


end SphereSixComplex.Geometry.AnalyticData
