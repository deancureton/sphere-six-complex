module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Prod
public import SphereSixComplex.Elliptic.Homology.FourthHomologySweep
public import SphereSixComplex.Cusp.Sweep.ChosenThirdSweep
public import SphereSixComplex.Toric.Homology.CircleSweep
public import SphereSixComplex.Cusp.Sweep.FourthCircle
public import SphereSixComplex.Cusp.Sweep.FixedCircleSweep
public import SphereSixComplex.Regular.Transport.InvariantPeriodCircle
public import SphereSixComplex.Prerequisites.Topology.PuncturedPlane.TwicePuncturedGenerators
public import SphereSixComplex.Prerequisites.Topology.Hurewicz.ChainInverse
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.CircleCross
public import SphereSixComplex.Cusp.Wang.FiberSliceComparison
public import SphereSixComplex.Elliptic.Band.OverlapCompletionData
public import SphereSixComplex.Regular.Transport.Fiber
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.FiberSlice
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.ProductBoundaryNaturality
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.OrientedRefinement
public import SphereSixComplex.Elliptic.Band.RadialCompletionData
public import SphereSixComplex.Cusp.CollarPairProperness
public import SphereSixComplex.TorusFamily.RealPeriodTrivialization
public import SphereSixComplex.Cusp.Cover.BoundaryUniversalCover
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.WangExactness
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.Comparison
public import SphereSixComplex.Prerequisites.Topology.Torus.CircleExponential
public import SphereSixComplex.Cusp.Wang.BandCoordinates
public import SphereSixComplex.Periods.LatticeData
public import SphereSixComplex.FundamentalGroup.Presentation
public import SphereSixComplex.Prerequisites.Topology.Covering.AffineVanKampen
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Prerequisites.Topology.PuncturedPlane.PowerFactorization
public import SphereSixComplex.Elliptic.Cover.FillingDeckTransport
public import SphereSixComplex.Elliptic.Collar.CanonicalFiniteMarking
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting
public import SphereSixComplex.Elliptic.FundamentalGroup.Relators
public import SphereSixComplex.Elliptic.Band.MarkedDisc
public import SphereSixComplex.Elliptic.Band.OverlapInterleaving
public import SphereSixComplex.Periods.FuchsianModularLift.Ramification
public import SphereSixComplex.Prerequisites.Topology.Homotopy.FreeLoopProduct
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.ContinuousMap.Ordered
public import SphereSixComplex.TriangleGroup.Representation
public import SphereSixComplex.TorusFamily.FiberFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.FreeLoop
public import SphereSixComplex.Cusp.Wang.FiberSlice
public import SphereSixComplex.Cusp.Specialization.Coordinates
public import SphereSixComplex.Cusp.Cover.BoundaryBasepoint
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.RankOneSplitting
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.IntervalClutching
public import Mathlib.Topology.Instances.AddCircle.Real
public import SphereSixComplex.Cusp.Specialization.FiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Cusp.Specialization.WangCoordinates
public import SphereSixComplex.Cusp.Wang.NormalizedBandMarking

public import SphereSixComplex.Cusp.FundamentalGroup.FundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.Sphere.Homology
public import SphereSixComplex.Elliptic.Band.RadialCompletion
public import SphereSixComplex.Homology.Second
public import SphereSixComplex.Elliptic.Homology.HomologyVanishing
public import SphereSixComplex.Homology.First
public import SphereSixComplex.Homology.SphereComparison
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.FiniteRank
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
