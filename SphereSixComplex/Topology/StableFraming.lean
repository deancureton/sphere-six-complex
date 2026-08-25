module

public import SphereSixComplex.Topology.OrientedSmoothHomotopySphere
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Stable framings of smooth manifolds

This module introduces the concrete differential-topological datum used by the
Pontryagin--Thom construction.  A stable framing is not represented by a proposition saying that
one exists: it is a global smooth frame of the Whitney sum of the tangent bundle with a trivial
bundle.

For a six-manifold the classical stabilization is by one real line, so the resulting bundle has a
frame indexed by `Fin 7`.  Constructing such a frame on every homotopy six-sphere is the stable
parallelizability theorem; it is deliberately exposed as a separate obligation below.
-/

@[expose] public section

noncomputable section

open Bundle Module
open scoped Bundle ContDiff Manifold

namespace SphereSixComplex

universe u

/-- A smooth stable framing of a manifold.

The sections take values in `TM ⊕ (M × F)`.  `IsLocalFrameOn ... Set.univ` asserts both that
they form a basis in every fiber and that every section is smooth.  Thus this structure retains
the geometric data needed by Pontryagin--Thom, rather than only the fact that a stable
trivialization exists. -/
public structure SmoothStableFraming
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F ι : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The global sections of the stabilized tangent bundle. -/
  sections : ι → (x : M) →
    (TangentSpace I x × Bundle.Trivial M F x)
  /-- At every point the sections are a basis, and they vary smoothly. -/
  isFrame : IsLocalFrameOn I (E × F) ∞ sections Set.univ

namespace SmoothStableFraming

/-- The basis of a stabilized tangent fiber supplied by a stable framing. -/
public def basisAt
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SmoothStableFraming (M := M) I F ι) (x : M) :
    Basis ι ℝ (TangentSpace I x × Bundle.Trivial M F x) :=
  f.isFrame.toBasisAt (Set.mem_univ x)

@[simp]
public theorem basisAt_apply
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SmoothStableFraming (M := M) I F ι) (x : M) (i : ι) :
    f.basisAt x i = f.sections i x := by
  exact f.isFrame.toBasisAt_coe (Set.mem_univ x) i

end SmoothStableFraming

/-- The concrete stable-framing datum relevant to a smooth six-manifold: a seven-element smooth
frame of `TM ⊕ ε¹`. -/
public abbrev SmoothStableFramingSix
    {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] :=
  SmoothStableFraming (M := M) 𝓘(ℝ, RealModel) ℝ (Fin 7)

/-- Stable parallelizability of a smooth six-manifold, stated using an actual global smooth
frame. -/
public def StablyParallelizableSixManifold
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] : Prop :=
  Nonempty (SmoothStableFramingSix (M := M))

/-- The classical theorem that every smooth homotopy six-sphere is stably parallelizable.

This is a named proof obligation, not an axiom.  Its conclusion contains a concrete frame that can
feed a future Pontryagin--Thom construction. -/
public def HomotopySixSpheresStablyParallelizable : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    StablyParallelizableSixManifold S.carrier

end SphereSixComplex
