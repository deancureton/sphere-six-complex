module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem integralCompactlySupportedCohomologyOn_union_exists_representative
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (α : integralCompactlySupportedCohomology n ↥(U ∪ V)) :
    ∃ (A B : Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
      (β : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ),
      integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (union_subset_union hA hB) β = α := by
  obtain ⟨K, hK, γ, hγ⟩ := integralCompactlySupportedCohomologyOn_exists_representative
    n (U ∪ V) (hU.union hV) α
  obtain ⟨A, B, hAc, hBc, hAU, hBV, hAB⟩ := K.isCompact.binary_compact_cover hU hV hK
  let KA : Compacts X := ⟨A, hAc⟩
  let KB : Compacts X := ⟨B, hBc⟩
  have hKAB : K ≤ KA ⊔ KB := by
    change (K : Set X) ⊆ A ∪ B
    rw [hAB]
  let β := integralRelativeCohomologyMap n (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) ((KA ⊔ KB : Compacts X) : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr hKAB) γ
  refine ⟨KA, KB, hAU, hBV, β, ?_⟩
  exact (integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) K (KA ⊔ KB)
    hKAB hK (union_subset_union hAU hBV) γ).trans hγ

theorem integralCompactlySupportedCohomologyOn_union_hom_ext
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {P : Type*} [AddCommMonoid P] [Module ℤ P]
    {f g : integralCompactlySupportedCohomology n ↥(U ∪ V) →ₗ[ℤ] P}
    (h : ∀ (A B : Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
      (β : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ),
      f (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (union_subset_union hA hB) β) =
      g (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (union_subset_union hA hB) β)) : f = g := by
  ext α
  obtain ⟨A, B, hA, hB, β, rfl⟩ :=
    integralCompactlySupportedCohomologyOn_union_exists_representative n U V hU hV α
  exact h A B hA hB β

end DifferentialGeometry.Topology
