module

public import SphereSixComplex.Prerequisites.Topology.Manifold.PoincareDuality
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.UniversalCoefficients
public import SphereSixComplex.Prerequisites.Topology.Manifold.Triangulation
public import SphereSixComplex.Prerequisites.Topology.Manifold.PoincareUniversalCoefficients

/-!
# Integral homology of compact simply connected manifolds

This file combines smooth triangulation and the integral UCT with proved Poincaré duality
for simply connected compact manifolds.
-/

@[expose] public section

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Integral homology data for a simply connected compact manifold. -/
public noncomputable def SmoothManifold.integralPoincareUCT
    (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [SecondCountableTopology X] [SimplyConnectedSpace X]
    (hManifold : IsManifold (modelWithCornersSelf ℝ E) 1 X)
    (hCompact : CompactSpace X) :
    IntegralPoincareUCTData (Module.finrank ℝ E) X := by
  let _ := hManifold
  let _ := hCompact
  have P (k : Fin (Module.finrank ℝ E + 1)) : Nonempty
      (IntegralSingularCohomology k.1 X ≃+ IntegralSingularHomology (Module.finrank ℝ E - k.1) X) :=
    PoincareDuality.nonempty_addEquiv_of_simplyConnected E X k.1 (Module.finrank ℝ E - k.1) (by omega)
  let M := SmoothManifold.finiteCWModel E X hManifold hCompact
  refine {
    topEquivDualZero := ?_
    complementEquivDual := ?_
    finite_homology := M.finite_homology
    subsingleton_homology_of_lt := M.subsingleton_homology_of_lt }
  · exact (Classical.choice (P 0)).symm.trans
      (Classical.choice (IntegralCohomology.universal_coefficients X).1)
  · intro k hk hFree
    exact (Classical.choice (P k)).symm.trans
      (integralSingularCohomologyEquivDualOfPreviousFree X k.1 hk hFree)

end SphereSixComplex
