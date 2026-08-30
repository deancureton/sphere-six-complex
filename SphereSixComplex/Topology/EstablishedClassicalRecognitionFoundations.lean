module

public import SphereSixComplex.Topology.HurewiczWhiteheadStages
public import SphereSixComplex.Topology.SmoothSixSphereClassification

/-!
# Classical foundations for smooth six-sphere recognition

This module is the complete classical trust boundary for recognizing the standard smooth
six-sphere. The four assumptions are source-independent theorems of classical topology and
differential topology. Their exact hypotheses are exposed here so that none of the paper-specific
geometry is hidden in the recognition step.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The degree-six consequence of the Hurewicz theorem. For a simply connected space, vanishing
integral homology in degrees one through five and an infinite-cyclic sixth homology group produce
a spherical generator of sixth homology. This is obtained by applying Hurewicz successively in
degrees two through six. -/
public axiom establishedHigherHurewiczSixGenerator
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    (hLower : ∀ n : ℕ, 0 < n → n < 6 → Subsingleton (IntegralSingularHomology n X))
    (hTop : Nonempty (IntegralSingularHomology 6 X ≃+ ℤ)) :
    HasTopDimensionalSphericalGenerator X

/-- Every compact second-countable smooth six-manifold has the homotopy type of a classical CW
complex. This is the standard smooth-triangulation, equivalently Morse-handle, theorem in the
fixed real six-dimensional model used by the construction. -/
public axiom establishedCompactSmoothSixManifoldClassicalCWType
    (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] [IsManifold 𝓘(ℝ, RealModel) ∞ X] [CompactSpace X] :
    HasClassicalCWType X

/-- The homological Whitehead theorem for simply connected spaces of classical CW type. The
simple-connectivity hypotheses are essential: the corresponding unrestricted integral-homology
statement is false. -/
public axiom establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    ClassicalCWIntegralHomologyWhiteheadProperty X Y

/-- Smooth Poincare in dimension six for the specified smooth atlas. Equivalently, this is the
dimension-six generalized Poincare and h-cobordism argument together with the Kervaire--Milnor
calculation that the group of smooth homotopy six-spheres is trivial. -/
public axiom establishedSmoothPoincareSixStandardModel :
    SmoothPoincareSixStandardModel

end SphereSixComplex
