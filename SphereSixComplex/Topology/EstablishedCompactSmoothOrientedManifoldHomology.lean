module

public import SphereSixComplex.Topology.IntegralPoincareUCT
public import SphereSixComplex.Topology.SmoothAtlasOrientation

/-!
# Integral homology of compact smooth oriented manifolds

This file is the single boundary for classical algebraic topology not yet present in Mathlib.
Mathlib currently lacks the compact-manifold finite-CW theorem, singular cohomology and its integral
UCT, manifold fundamental classes, and Poincare duality.  Those standard results are packaged here
as one dimension-generic theorem.  The orientation input itself is concrete atlas data and is
proved for complex manifolds in `SmoothAtlasOrientation`.
-/

@[expose] public section

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Classical finite-CW, dimension-vanishing, integral UCT, and Poincare-duality theorem for a
compact smooth oriented manifold without boundary.

The self model gives a manifold without boundary.  Hausdorffness and second countability are the
standard hypotheses used in smooth triangulation/finite-CW arguments.  This is the only new axiom:
its conclusion is the reduced homological interface, not an application-specific homology answer. -/
public axiom establishedCompactSmoothOrientedManifoldHomologyTheory
    (d : ℕ) (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℝ E) 1 X)
    (hOrientation : SmoothAtlasOrientation d E X)
    (hCompact : CompactSpace X) :
    IntegralPoincareUCTData d X

end SphereSixComplex
