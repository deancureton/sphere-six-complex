module

public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateCalculationProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof

/-!
# Geometric reduction of the cusp-to-elliptic marked coordinates

The marked invariant-basis calculation determines the canonical pulled-back boundary bridge.
The positive-degree cusp inclusion still requires independent geometry: a common meridian
projection, explicit mapping-torus prism cycles, and the orientation of the first invariant
suspension prism.  These data imply the finite marked-coordinate calculation without any
additional coordinate assumption.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The canonical pulled-back boundary bridge constructed from the two invariant-basis
evaluations, with no established input. -/
public theorem pulledBackBoundaryBasisBridgeOfInvariantBasisData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R) :
    R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge R.homologyAlignment :=
  SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
    R.homologyAlignment
    (R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
      R.homologyAlignment
      (cuspMarkedConnectingNaturality_of_invariantBasisData R h))

/-- The exact geometric residue for the marked cusp-to-elliptic calculation.  It consists of
the mapping-torus meridian projection and explicit prism cycles, together with identification
of the first invariant-suspension prism with the positively oriented normalized fibre class. -/
public structure ActualCuspEllipticMarkedGeometricResidue
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R) where
  prismGeometry :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      (pulledBackBoundaryBasisBridgeOfInvariantBasisData R h)
  indexFourPrismClass :
    R.twoDiscCover.NormalizedIndexFourPrismCalculation prismGeometry

/-- The invariant-basis boundary calculation and the exact meridian/prism geometry imply all
eight marked cusp-to-elliptic coordinate evaluations. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_of_geometricResidue
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R)
    (C : ActualCuspEllipticMarkedGeometricResidue R h) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R
      (pulledBackBoundaryBasisBridgeOfInvariantBasisData R h) := by
  apply actualCuspFiberEllipticMarkedCoordinateCalculation_of_inclusionNaturality
  apply CuspEllipticMappingTorusCoordinateComparison.inclusionNaturality
  exact
    { degreeOne := C.prismGeometry.meridianProjection.degreeOne
      degreeTwoFiber := by
        rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic
          C.prismGeometry.modelHomotopy]
        exact (C.prismGeometry.suspensionPrismComparison C.indexFourPrismClass).degreeTwoFiber }

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
