module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorCycleDecomposition
public import SphereSixComplex.Paper.Topology.PaperCuspEllipticCoverCoordinates

/-!
# Geometric compatibility for the final cusp clutching

The cover calculation identifies the cusp generator with `g₀`, its action on the integral
period lattice with `M₀`, and the local cusp base coordinate with the affine elliptic base
coordinate.  This file isolates the remaining topological comparison at the same unmarked level:
an actual homology map from the cusp fibre to the elliptic band, its compatibility with the two
connecting maps, and the cycle decomposition of the cusp inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} {D : A.EllipticTwoDiscCoverData}

namespace EllipticTwoDiscCoverData

/-- An unmarked comparison between the actual cusp Wang boundary and the boundary of the
pulled-back elliptic cover, together with compatibility of the chosen fibre markings. -/
public structure SectionSevenCuspWangBandCompatibility
    (N : A.EllipticBandHomologyAlignment D) where
  fiberToBandHomologyOne :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)
  boundary_naturality :
    fiberToBandHomologyOne.comp (actualCuspWangBoundaryHom A) =
      D.cuspPulledBackBoundaryHom
  marking_naturality :
    (D.ellipticBandFourthCoordinateHom N).comp fiberToBandHomologyOne =
      actualCuspFiberFourthCoordinateHom A

namespace SectionSevenCuspWangBandCompatibility

variable {N : A.EllipticBandHomologyAlignment D}

/-- The marked connecting square follows from the unmarked boundary square and compatibility
of the fibre markings. -/
public theorem connectingNaturality
    (C : D.SectionSevenCuspWangBandCompatibility N) :
    (D.ellipticBandFourthCoordinateHom N).comp
        D.cuspPulledBackBoundaryHom =
      (EllipticTwoDiscCoverData.actualCuspFiberFourthCoordinateHom A).comp
        (EllipticTwoDiscCoverData.actualCuspWangBoundaryHom A) := by
  ext x
  calc
    D.ellipticBandFourthCoordinateHom N (D.cuspPulledBackBoundaryHom x) =
        D.ellipticBandFourthCoordinateHom N
          (C.fiberToBandHomologyOne (actualCuspWangBoundaryHom A x)) := by
      exact congrArg (D.ellipticBandFourthCoordinateHom N)
        (DFunLike.congr_fun C.boundary_naturality x).symm
    _ = actualCuspFiberFourthCoordinateHom A (actualCuspWangBoundaryHom A x) := by
      exact DFunLike.congr_fun C.marking_naturality _

/-- The canonical pulled-back boundary basis bridge obtained from the unmarked comparison. -/
public theorem pulledBackBoundaryBasisBridge
    (C : D.SectionSevenCuspWangBandCompatibility N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N :=
  EllipticTwoDiscCoverData.boundaryBasisBridge_of_coordinate_eq N
    (D.boundaryCoordinate_eq_of_connecting_eq N
      C.connectingNaturality)

end SectionSevenCuspWangBandCompatibility

/-- The remaining geometric clutching input after the explicit `g₀`/`M₀` cover calculation.
Its second field is an equality of actual singular-homology cycles, before taking any of the
three marked coordinates used by the final matrix calculation. -/
public structure SectionSevenCuspClutchingCompatibility
    (N : A.EllipticBandHomologyAlignment D) where
  wangBand : D.SectionSevenCuspWangBandCompatibility N
  cycleDecomposition :
    A.EllipticInteriorCycleDecomposition N.actualHomologyCoordinates
      (D.cuspNormalizedDegreeTwoSplitting N wangBand.pulledBackBoundaryBasisBridge)

namespace SectionSevenCuspClutchingCompatibility

variable {N : A.EllipticBandHomologyAlignment D}

/-- The cycle comparison implies the two marked naturality squares for the actual inclusion. -/
public theorem inclusionNaturality
    (C : D.SectionSevenCuspClutchingCompatibility N) :
    D.SectionSevenCuspEllipticInclusionNaturality N
      C.wangBand.pulledBackBoundaryBasisBridge where
  degreeOne := by
    ext x
    change D.ellipticInteriorDegreeOneCoordinateHom N
      (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) = _
    rw [D.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap]
    have h := C.cycleDecomposition.normalizedDegreeOne_onCuspCollar x
    simpa [cuspDegreeOneCoordinateHom_apply,
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv,
      cuspAttachmentBoundaryOne_actualCusp_zero] using congrFun h 0
  degreeTwoFiber := by
    ext x
    change D.ellipticInteriorDegreeTwoFiberCoordinateHom N
      C.wangBand.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) = _
    rw [D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap]
    have h := C.cycleDecomposition.normalizedDegreeTwo_onCuspCollar x
    simpa [cuspDegreeTwoFiberCoordinateHom_apply,
      actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv,
      cuspNormalizedDegreeTwoSplitting,
      cuspAttachmentBoundaryTwo_actualCusp_zero] using congrFun h 0

/-- The unmarked Wang comparison and actual cycle decomposition supply the three marked squares
isolated by the affine completion reduction. -/
public theorem markedCompletionInput
    {R : A.AffineRadialCompletionInput}
    (C : R.twoDiscCover.SectionSevenCuspClutchingCompatibility R.homologyAlignment) :
    A.AffineMarkedCompletionInput R where
  connectingNaturality := C.wangBand.connectingNaturality
  inclusionNaturality := C.inclusionNaturality

end SectionSevenCuspClutchingCompatibility

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
