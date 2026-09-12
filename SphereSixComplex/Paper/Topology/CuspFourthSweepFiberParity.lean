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

public theorem cuspEllipticFiberCoordinate_raw_fiber (A : AnalyticData)
    (R : A.AffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (i : Fin 4) :
    A.cuspEllipticFiberCoordinate R S
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)) =
      ![0, 12, 2, 0] i := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)
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


public def cuspFourthSweepClass (A : AnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) :=
  integralSingularHomologyMap 2 (cuspFourthSweep A)
    PositiveCircleCross.positiveCircleProductGenerator







end SphereSixComplex.Geometry.AnalyticData
