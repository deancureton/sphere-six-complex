module
public import SphereSixComplex.Paper.Topology.CuspEllipticHomologyFullIterate
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianWangSectionProof
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
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverAssembly
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspActualCoordinateScalarsFromExistingGeometry

public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport
public import SphereSixComplex.Prerequisites.Topology.RealMappingTorusFiberSlice

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex
open StandardCircleHomologyLiftDegree

public theorem loopHomologyClass_eq_of_pointwise {X : Type} [TopologicalSpace X]
    {x y : X} (p : Path x x) (q : Path y y) (h : ∀ t, p t = q t) :
    loopHomologyClass p = loopHomologyClass q := by
  have hxy : x = y := p.source.symm.trans ((h 0).trans q.source)
  erw [← loopHomologyClass_cast q hxy]
  congr 1
  ext t
  exact h t

namespace Geometry.AnalyticData
open SphereSixComplex.Topology Hurewicz.Chains
open CuspCollar
variable (A : AnalyticData)

public theorem cuspBridgeMeridian_hurewicz :
    hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian =
      loopHomologyClass A.cuspAngularProjectedLoop := by
  erw [cuspAffineBridgeMeridian,
    A.cuspAffineBridgeMeridian_eq_angularProjectedLoop, hurewiczFunction_baseEq]
  rfl

public theorem cuspOverlapToInterior_comp_collar
    (D : A.EllipticTwoDiscCoverData) :
    A.cuspOverlapToEllipticInterior.comp
      (⟨A.cuspCollarToStarOverlapHomeomorph,
        A.cuspCollarToStarOverlapHomeomorph.continuous⟩ :
          C(PuncturedLocalCuspQuotient A.starCuspWitness, _)) =
      D.cuspToEllipticInteriorMap.hom := by
  ext x
  rfl

public theorem cuspBridgeMeridian_homology_image
    (D : A.EllipticTwoDiscCoverData) :
    integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian) =
    integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom
      (loopHomologyClass A.cuspAngularPuncturedLoop) := by
  erw [A.cuspBridgeMeridian_hurewicz]
  erw [← A.cuspOverlapToInterior_comp_collar D]
  erw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  apply Subtype.ext
  rfl


end Geometry.AnalyticData
end SphereSixComplex
end
