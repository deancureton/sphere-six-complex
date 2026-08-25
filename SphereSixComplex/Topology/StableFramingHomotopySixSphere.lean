module

public import SphereSixComplex.Topology.StableFraming
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Reducing stable framings of homotopy six-spheres to bundle triviality

This file records the strongest construction currently supported by Mathlib's smooth vector-bundle
API.  A global compatible trivialization of `TM ⊕ ε¹` produces the concrete seven-element smooth
frame required by `SmoothStableFramingSix`.

The remaining classical input is therefore isolated precisely: for every marked smooth homotopy
six-sphere, the stabilized tangent bundle must admit a smooth fiberwise-linear trivialization.
The marking is only a topological homotopy equivalence, so it cannot be differentiated to
construct this trivialization.  A second, stronger adapter records what follows from a global
trivialization that is literally present in Mathlib's designated bundle atlas.
-/

@[expose] public section

noncomputable section

open Bundle Module
open scoped Bundle ContDiff Manifold

namespace SphereSixComplex

universe u

/-- The fiber family of the tangent bundle of a six-manifold stabilized by one trivial real
line. -/
public abbrev StabilizedTangentFiberSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    (x : M) : Type :=
  TangentSpace 𝓘(ℝ, RealModel) x × Bundle.Trivial M ℝ x

/-- A fixed seven-element basis of the model fiber `ℝ⁶ × ℝ`.

Using a fixed basis makes the passage from a global bundle trivialization to a stable frame
completely canonical up to this harmless coordinate choice. -/
public noncomputable def stabilizedRealModelBasisSix :
    Basis (Fin 7) ℝ (RealModel × ℝ) :=
  (((EuclideanSpace.basisFun (Fin 6) ℝ).toBasis.prod
      (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv)

/-- A smooth fiberwise-linear trivialization of `TM ⊕ ε¹`, expressed without requiring an
arbitrary global trivialization to be literally present in Mathlib's designated local atlas.

The fiberwise equivalence gives the bundle trivialization.  Smoothness is recorded on the inverse
images of a fixed basis; by linearity these are exactly the seven smooth sections needed for a
stable frame. -/
public structure SmoothStableTangentTrivializationSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] where
  /-- A linear identification of the fixed seven-dimensional model with every stabilized tangent
  fiber. -/
  fiberEquiv : (x : M) →
    (RealModel × ℝ) ≃ₗ[ℝ]
      (TangentSpace 𝓘(ℝ, RealModel) x × Bundle.Trivial M ℝ x)
  /-- The inverse images of the fixed coordinate basis vary smoothly. -/
  contMDiffOn_basis (i : Fin 7) :
    ContMDiffOn 𝓘(ℝ, RealModel)
      (𝓘(ℝ, RealModel).prod 𝓘(ℝ, RealModel × ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (RealModel × ℝ) x
        (fiberEquiv x (stabilizedRealModelBasisSix i))) Set.univ

/-- A smooth fiberwise-linear trivialization of `TM ⊕ ε¹` supplies a stable frame. -/
public def SmoothStableTangentTrivializationSix.toSmoothStableFraming
    {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M]
    (t : SmoothStableTangentTrivializationSix M) :
    SmoothStableFramingSix (M := M) where
  sections i x := t.fiberEquiv x (stabilizedRealModelBasisSix i)
  isFrame :=
    { linearIndependent := by
        intro x _
        exact (stabilizedRealModelBasisSix.map (t.fiberEquiv x)).linearIndependent
      generating := by
        intro x _
        exact (stabilizedRealModelBasisSix.map (t.fiberEquiv x)).span_eq.ge
      contMDiffOn := t.contMDiffOn_basis }

/-- Conversely, a stable frame determines a smooth fiberwise-linear trivialization by mapping the
fixed model basis to the given frame at each point. -/
public def SmoothStableFraming.toSmoothStableTangentTrivializationSix
    {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M]
    (f : SmoothStableFramingSix (M := M)) :
    SmoothStableTangentTrivializationSix M where
  fiberEquiv x := stabilizedRealModelBasisSix.equiv (f.basisAt x) (Equiv.refl (Fin 7))
  contMDiffOn_basis i := by
    simpa only [Basis.equiv_apply, Equiv.refl_apply, SmoothStableFraming.basisAt_apply] using
      f.isFrame.contMDiffOn i

/-- The bundle-triviality formulation and the concrete stable-frame formulation are equivalent.
This pins down the missing geometric result without introducing an axiom. -/
public theorem nonempty_smoothStableTangentTrivializationSix_iff_stablyParallelizable
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] :
    Nonempty (SmoothStableTangentTrivializationSix M) ↔
      StablyParallelizableSixManifold M := by
  constructor
  · rintro ⟨t⟩
    exact ⟨t.toSmoothStableFraming⟩
  · rintro ⟨f⟩
    exact ⟨f.toSmoothStableTangentTrivializationSix⟩

/-- An atlas-level bundle-theoretic input sufficient to construct a smooth stable framing.

The trivialization is required to be a member of the designated smooth vector-bundle atlas and
to have all of `M` as its base set.  These two conditions respectively encode smooth
compatibility and globality.  This is deliberately stronger than intrinsic smooth triviality:
for bundles built from a `FiberBundleCore`, Mathlib's designated atlas contains the original local
trivializations rather than every smoothly compatible trivialization. -/
public def StabilizedTangentBundleTrivialSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] : Prop :=
  ∃ e : Trivialization (RealModel × ℝ)
      (TotalSpace.proj :
        TotalSpace (RealModel × ℝ) (StabilizedTangentFiberSix M) → M),
    e ∈ FiberBundle.trivializationAtlas (RealModel × ℝ) (StabilizedTangentFiberSix M) ∧
      e.baseSet = Set.univ

/-- A global smooth-compatible trivialization of `TM ⊕ ε¹` gives the concrete stable
framing used by the Pontryagin--Thom layer. -/
public theorem smoothStableFramingSix_of_stabilizedTangentBundleTrivial
    {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M]
    (h : StabilizedTangentBundleTrivialSix M) :
    Nonempty (SmoothStableFramingSix (M := M)) := by
  obtain ⟨e, he, hbase⟩ := h
  let _ : MemTrivializationAtlas e := ⟨he⟩
  refine ⟨
    { sections := e.localFrame stabilizedRealModelBasisSix
      isFrame := ?_ }⟩
  simpa only [hbase] using
    e.isLocalFrameOn_localFrame_baseSet 𝓘(ℝ, RealModel) ∞ stabilizedRealModelBasisSix

/-- The stronger atlas-level bundle-triviality statement for marked smooth homotopy six-spheres. -/
public def HomotopySixSphereAtlasStableTangentTriviality : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    StabilizedTangentBundleTrivialSix S.carrier

/-- Once the stronger atlas-level stable tangent bundle triviality is supplied, the existing
stable-framing obligation is discharged without any further geometric input. -/
public theorem homotopySixSpheresStablyParallelizable_of_stableTangentTriviality
    (h : HomotopySixSphereAtlasStableTangentTriviality) :
    HomotopySixSpheresStablyParallelizable := by
  intro S
  exact smoothStableFramingSix_of_stabilizedTangentBundleTrivial (h S)

/-- The mathematically intrinsic stable tangent triviality obligation for marked homotopy
six-spheres. -/
public def HomotopySixSphereStableTangentTriviality : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    Nonempty (SmoothStableTangentTrivializationSix S.carrier)

/-- The intrinsic stable tangent triviality statement is exactly equivalent to the stable-framing
obligation already used by the project. -/
public theorem homotopySixSphereStableTangentTriviality_iff_stablyParallelizable :
    HomotopySixSphereStableTangentTriviality ↔
      HomotopySixSpheresStablyParallelizable := by
  constructor
  · intro h S
    exact (nonempty_smoothStableTangentTrivializationSix_iff_stablyParallelizable
      S.carrier).mp (h S)
  · intro h S
    exact (nonempty_smoothStableTangentTrivializationSix_iff_stablyParallelizable
      S.carrier).mpr (h S)

end SphereSixComplex
