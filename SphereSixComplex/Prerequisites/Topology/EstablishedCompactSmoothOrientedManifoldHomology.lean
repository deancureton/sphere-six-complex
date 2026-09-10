module

public import SphereSixComplex.Prerequisites.Topology.IntegralPoincareDuality
public import SphereSixComplex.Prerequisites.Topology.IntegralUniversalCoefficients
public import SphereSixComplex.Prerequisites.Topology.SmoothTriangulation
public import SphereSixComplex.Prerequisites.Topology.IntegralPoincareUCT

/-!
# Integral homology of compact smooth oriented manifolds

This file derives the reduced homological interface used by Section 7 from three independent,
dimension-generic classical inputs: smooth triangulation, the integral UCT, and integral Poincare
duality.  The orientation input itself is concrete atlas data and is proved for complex manifolds
in `SmoothAtlasOrientation`.
-/

@[expose] public section

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The homological consequences of smooth triangulation, the integral UCT, and integral Poincare
duality for a compact smooth oriented manifold without boundary. -/
public noncomputable def SmoothAtlasOrientation.integralPoincareUCT
    (d : ℕ) (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℝ E) 1 X)
    (hOrientation : SmoothAtlasOrientation d E X)
    (hCompact : CompactSpace X) :
    IntegralPoincareUCTData d X := by
  let P := PoincareDuality.nonempty_addEquiv d E X hManifold hOrientation hCompact
  let M0 := SmoothManifold.finiteCWModel E X hManifold hCompact
  let M : CWType.FiniteModelOfDimension d X := hOrientation.dimension_eq ▸ M0
  refine {
    topEquivDualZero := ?_
    complementEquivDual := ?_
    finite_homology := M.finite_homology
    subsingleton_homology_of_lt := M.subsingleton_homology_of_lt }
  · exact (Classical.choice (P 0)).symm.trans
      (IntegralCohomology.universalCoefficients.zeroEquiv X)
  · intro k hk hFree
    exact (Classical.choice (P k)).symm.trans
      (integralSingularCohomologyEquivDualOfPreviousFree X k.1 hk hFree)

end SphereSixComplex
