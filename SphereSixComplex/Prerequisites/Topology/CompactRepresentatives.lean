module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact representatives and bounds on translates

Surjective local homeomorphisms lift compact sets into images of compact sets. Properly
discontinuous actions give uniform positive bounds on the relevant compact translates.
-/

@[expose] public section

open TopologicalSpace Topology

namespace SphereSixComplex

noncomputable section

/-- A compact subset of the target of a surjective local homeomorphism has a compact set of
local representatives. -/
public theorem IsLocalHomeomorph.exists_compact_source_cover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose x hx using fun y : K ↦ hsurj y
  let e (y : K) : OpenPartialHomeomorph Y X := hf.localInverseAt (x y)
  have hy_source (y : K) : (y : Y) ∈ (e y).source := by
    rw [← hx y]
    exact hf.apply_self_mem_localInverseAt_source
  choose C hCcompact hyC hCsource using fun y : K ↦
    exists_compact_subset (e y).open_source (hy_source y)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun y : K ↦ interior (C y)) (fun _ ↦ isOpen_interior) (by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyC ⟨y, hy⟩⟩)
  let L : Set X := ⋃ y ∈ t, (e y) '' C y
  refine ⟨L, ?_, ?_⟩
  · exact t.isCompact_biUnion fun y _ ↦
      (hCcompact y).image_of_continuousOn ((e y).continuousOn.mono (hCsource y))
  · intro y hy
    obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine ⟨e z y, ?_, ?_⟩
    · exact Set.mem_iUnion₂.mpr ⟨z, hzt,
        ⟨y, interior_subset hyz, rfl⟩⟩
    · exact hf.apply_localInverseAt_of_mem ((hCsource z) (interior_subset hyz))


end

end SphereSixComplex
