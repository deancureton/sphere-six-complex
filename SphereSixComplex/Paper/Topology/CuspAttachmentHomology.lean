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
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly
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
public import SphereSixComplex.Paper.LatticeData
public import SphereSixComplex.Paper.Topology.PaperVanKampenAlgebraAdapter
public import SphereSixComplex.Prerequisites.Topology.EstablishedAffineVanKampen
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Prerequisites.Topology.ExactLocalFactorizationCircleHomotopy
public import SphereSixComplex.Paper.Topology.PaperActualEllipticFillingDeckTransport
public import SphereSixComplex.Paper.Topology.PaperActualEllipticCanonicalFiniteMarking
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting
public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import SphereSixComplex.Paper.Topology.PaperSectionSevenSmallMarkedDiscWitness
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving
public import SphereSixComplex.Paper.Periods.FuchsianModularLift.Ramification
public import SphereSixComplex.Prerequisites.Topology.FreeLoopProductHomotopy
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.ContinuousMap.Ordered
public import SphereSixComplex.Paper.TriangleGroup.Representation
public import SphereSixComplex.Paper.Geometry.GlobalTorusFiberFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSlice
public import SphereSixComplex.Paper.Topology.PaperCuspUnwrappedFillingCover
public import SphereSixComplex.Prerequisites.Topology.RankOneWangHomologySplitting
public import SphereSixComplex.Prerequisites.Topology.IntervalClutchingQuotientCore
public import Mathlib.Topology.Instances.AddCircle.Real
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof
public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

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
