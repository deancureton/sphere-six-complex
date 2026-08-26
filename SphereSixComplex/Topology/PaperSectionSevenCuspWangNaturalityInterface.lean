module

public import SphereSixComplex.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# The remaining cusp Wang naturality square

The canonical Mayer--Vietoris boundary is already natural under pullback.  The Wang sequence used
for the radial cusp collar, however, is currently supplied only as four exact homomorphisms.  Its
statement does not identify its boundary with a chain-level connecting morphism, so exactness
alone cannot determine the orientation of that boundary.

This file isolates the smallest general interface needed here: naturality after applying one
marked coordinate to each connecting homomorphism.  Everything from that standard
connecting-morphism square to the Section 7 boundary comparison is proved below.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

/-- Naturality of two connecting homomorphisms after applying marked target coordinates.  This is
the coordinate-level consequence of the usual naturality square for connecting morphisms. -/
public structure ConnectingCoordinateNaturality
    {Source LeftTarget RightTarget Coordinate : Type*}
    [AddCommGroup Source] [AddCommGroup LeftTarget] [AddCommGroup RightTarget]
    [AddCommGroup Coordinate]
    (leftBoundary : Source →+ LeftTarget) (rightBoundary : Source →+ RightTarget)
    (leftCoordinate : LeftTarget →+ Coordinate)
    (rightCoordinate : RightTarget →+ Coordinate) : Prop where
  square : leftCoordinate.comp leftBoundary = rightCoordinate.comp rightBoundary

namespace Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The actual cusp Wang connecting homomorphism before taking monodromy-invariant
coordinates. -/
public noncomputable def actualCuspWangBoundaryHom (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  exact P.boundary.comp
    (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).toAddMonoidHom

public theorem actualCuspWangBoundaryHom_apply
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    actualCuspWangBoundaryHom A x = actualCuspWangBoundary A x :=
  rfl

/-- The fourth marked coordinate on the actual elliptic band overlap. -/
public noncomputable def ellipticBandFourthCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) →+ ℤ :=
  coordinateAfterAddEquiv N.actualHomologyCoordinates.bandOne 3

/-- The fourth marked coordinate on the fibre in the actual cusp Wang presentation. -/
public noncomputable def actualCuspFiberFourthCoordinateHom (A : PaperAnalyticData) :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) →+ ℤ := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact coordinateAfterAddEquiv G.monodromyCoordinates.degreeOne 3

/-- The precise standard naturality input still absent from the current Wang API: the canonical
boundary of the pulled-back cusp cover and the Wang connecting homomorphism commute after the
fourth marked fibre coordinate is applied. -/
public def CuspMarkedConnectingNaturality
    (N : A.EllipticBandHomologyAlignment D) : Prop :=
  ConnectingCoordinateNaturality D.cuspPulledBackBoundaryHom
    (actualCuspWangBoundaryHom A) (D.ellipticBandFourthCoordinateHom N)
      (actualCuspFiberFourthCoordinateHom A)

/-- The general marked connecting-morphism square supplies the exact Section 7 cusp boundary
comparison. -/
public theorem sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
    (N : A.EllipticBandHomologyAlignment D)
    (h : D.CuspMarkedConnectingNaturality N) :
    D.SectionSevenCuspMarkedBoundaryComparison N where
  fourthCoordinate x := by
    have hx := DFunLike.congr_fun h.square x
    simpa [ellipticBandFourthCoordinateHom, actualCuspFiberFourthCoordinateHom,
      coordinateAfterAddEquiv_apply, cuspPulledBackBoundaryHom_apply,
      actualCuspWangBoundaryHom_apply] using hx

/-- Equivalently, the marked connecting-morphism square supplies the bundled homomorphism
comparison used by the six basis calculations. -/
public theorem sectionSevenCuspPulledBackWangBoundaryComparison_of_connectingNaturality
    (N : A.EllipticBandHomologyAlignment D)
    (h : D.CuspMarkedConnectingNaturality N) :
    D.SectionSevenCuspPulledBackWangBoundaryComparison N :=
  SectionSevenCuspMarkedBoundaryComparison.toPulledBackWangBoundaryComparison D N
    (D.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality N h)

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex
