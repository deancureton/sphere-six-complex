module

public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison

/-!
# The cusp meridian from a base-projection square

The distinguished last degree-one Wang coordinate is the base-circle coordinate.  This file
isolates the general homotopy-naturality argument: once source and target coordinates are
realized by maps to the same circle model, a homotopy-commutative projection square proves the
required coordinate identity.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData

/-- A degree-one homology coordinate realized by a continuous projection to a common base. -/
public structure HomologyOneCoordinateProjection
    (X Base : Type) [TopologicalSpace X] [TopologicalSpace Base]
    (coordinate : IntegralSingularHomology 1 X →+ ℤ)
    (baseCoordinate : IntegralSingularHomology 1 Base →+ ℤ) where
  projection : C(X, Base)
  coordinate_eq :
    coordinate = baseCoordinate.comp (integralSingularHomologyMap 1 projection)

namespace HomologyOneCoordinateProjection

variable {X Y Base : Type}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Base]
  {sourceCoordinate : IntegralSingularHomology 1 X →+ ℤ}
  {targetCoordinate : IntegralSingularHomology 1 Y →+ ℤ}
  {baseCoordinate : IntegralSingularHomology 1 Base →+ ℤ}

/-- A homotopy-commutative square over a common base preserves the represented degree-one
coordinate. -/
public theorem naturality
    (source : HomologyOneCoordinateProjection X Base sourceCoordinate baseCoordinate)
    (target : HomologyOneCoordinateProjection Y Base targetCoordinate baseCoordinate)
    (f : C(X, Y)) (h : (target.projection.comp f).Homotopic source.projection) :
    targetCoordinate.comp (integralSingularHomologyMap 1 f) = sourceCoordinate := by
  apply AddMonoidHom.ext
  intro x
  change targetCoordinate (integralSingularHomologyMap 1 f x) = sourceCoordinate x
  rw [target.coordinate_eq, source.coordinate_eq]
  change baseCoordinate
      (integralSingularHomologyMap 1 target.projection
        (integralSingularHomologyMap 1 f x)) =
    baseCoordinate (integralSingularHomologyMap 1 source.projection x)
  have hcomp := DFunLike.congr_fun
    (integralSingularHomologyMap_comp 1 f target.projection) x
  have hbase := DFunLike.congr_fun
    (coordinate_comp_integralSingularHomologyMap_eq_of_homotopic h 1 baseCoordinate) x
  exact (congrArg baseCoordinate hcomp).symm.trans hbase

end HomologyOneCoordinateProjection

namespace Geometry.PaperAnalyticData

open CircleMappingTorusHomologyBases
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- A common base projection realizing both the geometric Wang meridian and the marked
elliptic-interior degree-one coordinate.  The last field is the sole geometric square: the
cusp-to-elliptic mapping-torus map commutes with the two projections up to homotopy. -/
public structure CuspEllipticMappingTorusMeridianProjectionComparison
    (N : A.EllipticBandHomologyAlignment D) where
  Base : Type
  baseTopology : TopologicalSpace Base
  baseCoordinate :
    let _ := baseTopology
    IntegralSingularHomology 1 Base →+ ℤ
  sourceProjection :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let _ := baseTopology
    HomologyOneCoordinateProjection (CircleMappingTorus G.clutching) Base
      (actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv)
      baseCoordinate
  targetProjection :
    let _ := baseTopology
    HomologyOneCoordinateProjection A.SectionSevenEllipticInterior Base
      (D.ellipticInteriorDegreeOneCoordinateHom N) baseCoordinate
  projectionHomotopy :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let _ := baseTopology
    (targetProjection.projection.comp D.cuspMappingTorusToEllipticInteriorMap).Homotopic
      sourceProjection.projection

namespace CuspEllipticMappingTorusMeridianProjectionComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}

/-- The projection square computes the first residual cusp coordinate. -/
public theorem degreeOne
    (C : D.CuspEllipticMappingTorusMeridianProjectionComparison N) :
    (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let _ := C.baseTopology
  exact HomologyOneCoordinateProjection.naturality C.sourceProjection C.targetProjection
    D.cuspMappingTorusToEllipticInteriorMap C.projectionHomotopy

end CuspEllipticMappingTorusMeridianProjectionComparison

/-- The sharpened residual cusp package.  The meridian calculation is supplied by a
homotopy-commutative base-projection square; only the first invariant-suspension calculation
remains on an explicit reference map. -/
public structure CuspEllipticMappingTorusMeridianGeometricComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) where
  meridianProjection : D.CuspEllipticMappingTorusMeridianProjectionComparison N
  referenceMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)
  modelHomotopy :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.cuspMappingTorusToEllipticInteriorMap.Homotopic referenceMap
  referenceDegreeTwoFiber :
    (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀).comp
        (integralSingularHomologyMap 2 referenceMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv

namespace CuspEllipticMappingTorusMeridianGeometricComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The projection square and the reference-map calculation give the two mapping-torus
coordinates required by the cusp comparison. -/
public theorem coordinateComparison
    (C : D.CuspEllipticMappingTorusMeridianGeometricComparison N G₀) :
    D.CuspEllipticMappingTorusCoordinateComparison N G₀ where
  degreeOne := C.meridianProjection.degreeOne
  degreeTwoFiber := by
    rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
    exact C.referenceDegreeTwoFiber

end CuspEllipticMappingTorusMeridianGeometricComparison

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex

end
