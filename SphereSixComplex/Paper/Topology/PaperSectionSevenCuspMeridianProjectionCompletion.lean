module

public import SphereSixComplex.Prerequisites.Topology.MappingTorusBaseCircleProjection
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Prerequisites.Topology.StandardCircleHomologyLiftDegree

/-!
# The exact geometric residue in the cusp meridian projection comparison

The mapping-torus height always descends to its base circle.  This gives the angular summand of
the desired cusp coordinate, but not its finite-cover fibre summand.  The latter has coefficient
`12` in the raw Wang basis, whereas the base-circle projection is constant on every fibre.

This file isolates the remaining geometric construction without replacing it by the resulting
homology equality.  Once independently constructed circle maps realize the two marked degree-one
coordinates, the only compatibility still needed is their literal pointwise equality after
composition with the actual cusp-to-elliptic map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.PaperAnalyticData

open CircleMappingTorusHomologyBases
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- Independent circle-valued realizations of the two marked degree-one coordinates.

This deliberately contains no compatibility between the two maps.  In particular, it is not a
rephrasing of the desired equality after mapping cusp homology into the elliptic interior. -/
public structure CuspEllipticMeridianCircleCoordinateRealization
    (N : A.EllipticBandHomologyAlignment D) where
  sourceProjection :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, UnitAddCircle)
  targetProjection : C(A.ellipticInterior, UnitAddCircle)
  sourceCoordinate_eq :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 sourceProjection)
  targetCoordinate_eq :
    D.ellipticInteriorDegreeOneCoordinateHom N =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 targetProjection)

namespace CuspEllipticMeridianCircleCoordinateRealization

variable {D : A.EllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}

/-- Coordinate-realizing circle maps and a homotopy-commutative circle projection square give
the requested common-base comparison. -/
public noncomputable def toMeridianProjectionComparison
    (P : D.CuspEllipticMeridianCircleCoordinateRealization N)
    (h :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      (P.targetProjection.comp D.cuspMappingTorusToEllipticInteriorMap).Homotopic
        P.sourceProjection) :
    D.CuspEllipticMappingTorusMeridianProjectionComparison N where
  Base := UnitAddCircle
  baseTopology := inferInstance
  baseCoordinate := StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
  sourceProjection :=
    { projection := P.sourceProjection
      coordinate_eq := P.sourceCoordinate_eq }
  targetProjection :=
    { projection := P.targetProjection
      coordinate_eq := P.targetCoordinate_eq }
  projectionHomotopy := h

/-- The sharp point-set constructor: after separately realizing both coordinates by circle maps,
the remaining input is the literal equality of the two projections at every mapping-torus point.
-/
public noncomputable def toMeridianProjectionComparison_of_pointwise_projection
    (P : D.CuspEllipticMeridianCircleCoordinateRealization N)
    (h :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∀ x : CircleMappingTorus G.clutching,
        P.targetProjection (D.cuspMappingTorusToEllipticInteriorMap x) =
          P.sourceProjection x) :
    D.CuspEllipticMappingTorusMeridianProjectionComparison N := by
  apply P.toMeridianProjectionComparison
  have hmaps : P.targetProjection.comp D.cuspMappingTorusToEllipticInteriorMap =
      P.sourceProjection := by
    ext x
    exact h x
  rw [hmaps]

end CuspEllipticMeridianCircleCoordinateRealization

end EllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex

end
