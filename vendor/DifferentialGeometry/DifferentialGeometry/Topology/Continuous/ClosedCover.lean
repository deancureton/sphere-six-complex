module

public import Mathlib.Topology.ContinuousOn

@[expose] public section

namespace DifferentialGeometry.Topology

open Set

section Generic

variable {X : Type*} [TopologicalSpace X]

theorem continuousOn_of_isClosed_cover {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    {s t u : Set X} (hs : IsClosed s) (ht : IsClosed t) (hu : u ⊆ s ∪ t)
    (hfs : ContinuousOn f (u ∩ s)) (hft : ContinuousOn f (u ∩ t)) : ContinuousOn f u := by
  intro x hx
  have hu' : u = (u ∩ s) ∪ (u ∩ t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hu]
  rw [hu']
  refine ContinuousWithinAt.union ?_ ?_
  · by_cases hxs : x ∈ s
    · exact hfs x ⟨hx, hxs⟩
    · exact continuousWithinAt_of_notMem_closure fun h =>
        hxs ((hs.closure_subset_iff.2 inter_subset_right) h)
  · by_cases hxt : x ∈ t
    · exact hft x ⟨hx, hxt⟩
    · exact continuousWithinAt_of_notMem_closure fun h =>
        hxt ((ht.closure_subset_iff.2 inter_subset_right) h)

end Generic

end DifferentialGeometry.Topology
