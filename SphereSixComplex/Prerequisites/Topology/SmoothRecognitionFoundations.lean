module

public import SphereSixComplex.Prerequisites.Topology.HurewiczWhitehead
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Foundations for smooth recognition in dimension six

This file records the part of the recognition argument that can be proved with the current
mathlib API and separates the remaining classical theorems along their mathematical boundaries.

Mathlib defines cubical higher homotopy groups, but currently has no functorial maps on those
groups, Hurewicz homomorphism, homological Whitehead theorem for spaces of CW type, or theorem
that manifolds have CW type.  Its Poincare-conjecture file states, but does not prove, the relevant
topological and smooth recognition theorems.  Mathlib also has no h-cobordism theorem or
formalization of the Kervaire--Milnor computation that the group of smooth homotopy six-spheres is
trivial.  Consequently those results cannot yet be discharged from existing library theorems.

The results below are not new recognition assumptions in disguise.  They prove two concrete
facts: simple connectivity kills the zeroth and first homotopy groups in mathlib's actual cubical
model, and the smooth Poincare step factors exactly into topological Poincare followed by the
nonexistence of exotic smooth structures on the topological six-sphere.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold Topology

namespace SphereSixComplex







/-- The absence of an exotic smooth structure on a fixed topological six-sphere.  Globally, this
is the dimension-six Kervaire--Milnor input. -/
public def HomeomorphismToDiffeomorphismSixSphereObligation
    (X : Type) [TopologicalSpace X] [ChartedSpace RealModel X] : Prop :=
  IsManifold 𝓘(ℝ, RealModel) ∞ X →
    Nonempty (X ≃ₜ SixSphere) → SmoothSixSphere.IsDiffeomorphic X




end SphereSixComplex
