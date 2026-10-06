module

public import SphereSixComplex.Prerequisites.Topology.Sphere.SmoothRecognition

/-! # Smooth six-sphere recognition

Smooth Poincare in dimension six is the remaining classical trust boundary.
-/

@[expose] public section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Smooth Poincare in dimension six for the specified smooth atlas. Equivalently, this is the
dimension-six generalized Poincare and h-cobordism argument together with the Kervaire--Milnor
calculation that the group of smooth homotopy six-spheres is trivial. -/
public axiom SmoothSixSphere.poincare
    (M : Type) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] (hM : Nonempty (M ≃ₕ SixSphere)) :
    Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M SixSphere ∞)

end SphereSixComplex
