module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSlice
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization
public import SphereSixComplex.Paper.Topology.PaperCuspUnwrappedFillingCover
public import SphereSixComplex.Prerequisites.Topology.RankOneWangHomologySplitting
public import Mathlib.Topology.Subpath
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Prerequisites.Topology.IntervalClutchingQuotientCore
public import Mathlib.Topology.Instances.AddCircle.Real
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof

@[expose] public section

noncomputable section

open AlgebraicTopology Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open Hurewicz
open SphereSixComplex.StandardCircleHomologyLiftDegree
open CuspCollar

variable (A : AnalyticData)

public noncomputable def cuspAngularPuncturedLoop :
    Path A.cuspLocalBoundaryBase A.cuspLocalBoundaryBase := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  exact (A.cuspAngularLiftPath.map
    (additiveCuspBoundaryProjection W).continuous).cast
      (by
        exact (additiveCuspBoundaryProjection_basePreimage W
          A.cuspLocalBoundaryBase).symm)
      (by
        exact ((additiveCuspBoundaryProjection_paperCuspBoundaryDeck_smul W
          paperCuspBoundaryMeridian A.cuspBoundaryCoverBase).trans
            (additiveCuspBoundaryProjection_basePreimage W
              A.cuspLocalBoundaryBase)).symm)


end SphereSixComplex.Geometry.AnalyticData

end
