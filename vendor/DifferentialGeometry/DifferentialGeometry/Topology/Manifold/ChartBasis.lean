module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Bases

@[expose] public section

open Set TopologicalSpace

namespace ChartedSpace

theorem exists_isTopologicalBasis_homeomorph_open
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] :
    ∃ B : Set (Set M), IsTopologicalBasis B ∧
      (∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B) ∧
      ∀ U ∈ B, ∃ S : Set H, IsOpen S ∧ Nonempty (U ≃ₜ S) := by
  let B : Set (Set M) := {U | IsOpen U ∧ ∃ p : M, U ⊆ (chartAt H p).source}
  refine ⟨B, ?_, ?_, ?_⟩
  · apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1)
    intro x U hx hU
    exact ⟨U ∩ (chartAt H x).source,
      ⟨hU.inter (chartAt H x).open_source, x, inter_subset_right⟩,
      ⟨hx, mem_chart_source H x⟩, inter_subset_left⟩
  · rintro U ⟨hU, p, hp⟩ V ⟨hV, _⟩
    exact ⟨hU.inter hV, p, inter_subset_left.trans hp⟩
  · rintro U ⟨hU, p, hp⟩
    exact ⟨(chartAt H p) '' U, (chartAt H p).isOpen_image_of_subset_source hU hp,
      ⟨(chartAt H p).homeomorphOfImageSubsetSource hp rfl⟩⟩

end ChartedSpace

namespace ModelWithCorners

theorem exists_isTopologicalBasis_homeomorph_open
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    ∃ B : Set (Set M), IsTopologicalBasis B ∧
      (∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B) ∧
      ∀ U ∈ B, ∃ S : Set E, IsOpen S ∧ Nonempty (U ≃ₜ S) := by
  obtain ⟨B, hB, hinter, hchart⟩ := ChartedSpace.exists_isTopologicalBasis_homeomorph_open H M
  refine ⟨B, hB, hinter, ?_⟩
  intro U hU
  obtain ⟨S, hS, ⟨e⟩⟩ := hchart U hU
  exact ⟨I.toHomeomorph '' S, I.toHomeomorph.isOpenMap _ hS,
    ⟨e.trans (I.toHomeomorph.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
      (subset_univ S) rfl)⟩⟩

end ModelWithCorners
