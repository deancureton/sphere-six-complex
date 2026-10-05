module

public import SphereSixComplex.Periods.LatticeData
public import SphereSixComplex.FundamentalGroup.Presentation
public import SphereSixComplex.Prerequisites.Topology.Covering.AffineVanKampen
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Prerequisites.Topology.PuncturedPlane.PowerFactorization
public import SphereSixComplex.Elliptic.Cover.FillingDeckTransport
public import SphereSixComplex.Cusp.Cover.BoundaryUniversalCover
public import SphereSixComplex.Elliptic.Collar.CanonicalFiniteMarking
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting
public import SphereSixComplex.Elliptic.FundamentalGroup.Relators
public import SphereSixComplex.Elliptic.Band.MarkedDisc
public import SphereSixComplex.Elliptic.Band.OverlapCompletionData
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
public import SphereSixComplex.Elliptic.Sweep.FourthInteriorTranslation
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.CircleCross

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology CircleProductIdentityMappingTorus Hurewicz.Chains

public def ellipticFourthHomologySweep (A : AnalyticData) :
    IntegralSingularHomology 1 A.ellipticInterior →+
      IntegralSingularHomology 2 A.ellipticInterior :=
  (integralSingularHomologyMap 2 A.ellipticFourthTranslation).comp (normalizedCircleCross 1)

end SphereSixComplex.Geometry.AnalyticData
