module

public import SphereSixComplex.Topology.IntegralSingularCohomology
public import SphereSixComplex.Topology.SmoothAtlasOrientation

/-!
# Integral Poincaré duality

This file isolates integral Poincaré duality for arbitrary compact oriented manifolds without
boundary.  It is independent of the dimension-six application.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The group-level integral Poincaré duality theorem for every compact, second-countable,
Hausdorff, oriented real `C¹` manifold without boundary, in arbitrary finite dimension.

For every `0 ≤ k ≤ d`, the theorem supplies the additive equivalence
`H^k(X; ℤ) ≃ H_{d-k}(X; ℤ)`.  The `Nonempty` wrapper deliberately does not claim that the
chosen equivalence is canonical: cap products and fundamental classes are not yet constructed in
the project. -/
public axiom classicalIntegralPoincareDuality
    (d : ℕ) (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℝ E) 1 X)
    (hOrientation : SmoothAtlasOrientation d E X)
    (hCompact : CompactSpace X) :
    ∀ k : Fin (d + 1), Nonempty
      (IntegralSingularCohomology k.1 X ≃+ IntegralSingularHomology (d - k.1) X)

end SphereSixComplex

end

end
