module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {ι : Type v} [Nonempty ι]

theorem integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (α : integralCompactlySupportedCohomology n X) :
    ∃ (i : ι) (β : integralCompactlySupportedCohomology n (U i)),
      integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion (U i))
        (hU i).isOpenEmbedding_subtypeVal β = α := by
  obtain ⟨K, γ, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
  obtain ⟨i, hKi⟩ := K.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact subset_univ _) hdir
  exact ⟨i, integralRelativeToCompactlySupportedCohomologyOn n (U i) K hKi γ,
    integralRelativeToCompactlySupportedCohomologyOn_pushforward n (U i) (hU i) K hKi γ⟩

omit [Nonempty ι] in
theorem integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (i : ι) (β : integralCompactlySupportedCohomology n (U i))
    (hβ : integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion (U i))
      (hU i).isOpenEmbedding_subtypeVal β = 0) :
    ∃ (j : ι) (hij : U i ⊆ U j),
      integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion hij)
        (_root_.Topology.IsOpenEmbedding.inclusion hij
          ((hU i).preimage
            (continuous_subtype_val : Continuous ((Subtype.val : U j → X))))) β = 0 := by
  let : Nonempty ι := ⟨i⟩
  obtain ⟨K, hKi, γ, rfl⟩ :=
    integralCompactlySupportedCohomologyOn_exists_representative n (U i) (hU i) β
  rw [integralRelativeToCompactlySupportedCohomologyOn_pushforward n (U i) (hU i)] at hβ
  obtain ⟨L, hKL, hLγ⟩ :=
    (integralRelativeToCompactlySupportedCohomology_eq_zero_iff n K γ).mp hβ
  obtain ⟨j, hLj⟩ := L.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact subset_univ _) hdir
  obtain ⟨l, hil, hjl⟩ := hdir i j
  refine ⟨l, hil, ?_⟩
  rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U i) (U l) hil
    ((hU i).preimage continuous_subtype_val)]
  exact (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff n (U l) (hU l)
    K (hKi.trans hil) γ).mpr ⟨L, hLj.trans hjl, hKL, hLγ⟩

end DifferentialGeometry.Topology

end
