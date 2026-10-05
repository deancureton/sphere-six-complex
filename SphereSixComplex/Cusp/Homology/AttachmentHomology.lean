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
public import SphereSixComplex.Cusp.Cover.BoundaryBasepoint
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.RankOneSplitting
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.IntervalClutching
public import Mathlib.Topology.Instances.AddCircle.Real
public import SphereSixComplex.Cusp.Specialization.FiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Cusp.Specialization.WangCoordinates
public import SphereSixComplex.Cusp.Wang.NormalizedBandMarking

public import SphereSixComplex.Cusp.Specialization.Coordinates

@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData

public theorem cuspToFilling_homologyTwo_surjective (A : AnalyticData) :
    Function.Surjective (integralSingularHomologyMap 2
      (A.openEmbeddingStarData.toFilling 0).hom) := by
  have hp (x) : A.actualCuspFillingHomologyTwoEquiv
      (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
      fun i ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i) :=
    CuspSpecialization.degreeTwo A x
  intro y
  refine ⟨A.cuspRawHomologyTwoEquiv.symm
    (Fin.append (A.actualCuspFillingHomologyTwoEquiv y) (0 : Fin 2 → ℤ)), ?_⟩
  apply A.actualCuspFillingHomologyTwoEquiv.injective
  rw [hp, AddEquiv.apply_symm_apply]
  ext i
  simp

end SphereSixComplex.Geometry.AnalyticData
