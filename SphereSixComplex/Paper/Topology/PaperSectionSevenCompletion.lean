module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Prod
public import SphereSixComplex.Paper.Topology.EllipticFourthHomologySweep
public import SphereSixComplex.Paper.Topology.CuspChosenThirdSweep
public import SphereSixComplex.Paper.Topology.LocalToricCircleSweep
public import SphereSixComplex.Paper.Topology.CuspFourthCircle
public import SphereSixComplex.Paper.Topology.CuspFixedCircleSweep
public import SphereSixComplex.Paper.Topology.GlobalInvariantPeriodCircle
public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedComplexFundamentalGroupGeneration
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport
public import SphereSixComplex.Prerequisites.Topology.RealMappingTorusFiberSlice
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverAssembly
public import SphereSixComplex.Prerequisites.Topology.UnitCircleExponential
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry
public import SphereSixComplex.Paper.Topology.EllipticFillingHomology
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSlice
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization
public import SphereSixComplex.Paper.Topology.PaperCuspUnwrappedFillingCover
public import SphereSixComplex.Prerequisites.Topology.RankOneWangHomologySplitting
public import Mathlib.Topology.Subpath
public import SphereSixComplex.Prerequisites.Topology.IntervalClutchingQuotientCore
public import Mathlib.Topology.Instances.AddCircle.Real
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof
public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking

public import SphereSixComplex.Paper.Topology.CuspFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenAffineCompletion
public import SphereSixComplex.Paper.Topology.StarSecondHomology
public import SphereSixComplex.Paper.Topology.EllipticHomologyVanishing
public import SphereSixComplex.Paper.Topology.StarFirstHomology
public import SphereSixComplex.Paper.Geometry.StarHomology
public import SphereSixComplex.Prerequisites.Topology.MayerVietorisFiniteRank
public import Mathlib.LinearAlgebra.Pi

/-!
# Topology of the glued analytic threefold

The fundamental group and homology computations concern the same geometric glued carrier.
-/

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

variable (P : AnalyticData)

/-- The global circle action and cusp attachment kill second homology. -/
public theorem star_homologyTwo_subsingleton :
    Subsingleton (IntegralSingularHomology 2 P.VanKampenSpace) :=
  star_homologyTwo_subsingleton_of_interior P.affineRadialCompletionInput
    (ellipticInterior_homologyTwo_eq_zero P.affineRadialCompletionInput)

/-- Low-degree vanishing and the Euler calculation give the integral homology of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) :=
  P.star_nonempty_homologyEquiv_sixSphere_of_lowDegrees
    P.star_homologyOne_subsingleton P.star_homologyTwo_subsingleton

/-- The cusp relations make the fundamental group abelian, and vanishing first homology kills it. -/
public theorem star_simplyConnectedSpace :
    SimplyConnectedSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let _ := P.star_homologyOne_subsingleton
  exact P.star_simplyConnectedSpace_of_homologyOne_subsingleton P.cuspCentralNaturality

end SphereSixComplex.Geometry.AnalyticData
