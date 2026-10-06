module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionNaturality
public import Mathlib.Topology.Compactness.Compact

@[expose] public section



noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



theorem exists_isCompact_subset_integralSingularChainsIn (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ c ∈ integralSingularChainsIn n K := by
  refine ⟨⋃ σ ∈ (integralSingularChainRepr n X c).support,
    range (integralSingularSimplexEquiv n X σ), ?_, ?_, ?_⟩
  · exact (integralSingularChainRepr n X c).support.finite_toSet.isCompact_biUnion
      (fun σ _ => isCompact_range (integralSingularSimplexEquiv n X σ).continuous)
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨σ, hσ, hx⟩ := hx
    exact (integralSingularChainsIn_mem_iff n A c).mp hc σ (Finsupp.mem_support_iff.mp hσ) hx
  · rw [integralSingularChainsIn_mem_iff]
    intro σ hσ x hx
    exact Set.mem_iUnion₂.mpr ⟨σ, Finsupp.mem_support_iff.mpr hσ, hx⟩



theorem exists_isCompact_integralSingularChainsIn (n : ℕ)
    (c : (integralSingularChains X).X n) :
    ∃ K : Set X, IsCompact K ∧ c ∈ integralSingularChainsIn n K := by
  have hc : c ∈ integralSingularChainsIn n (univ : Set X) := by
    rw [integralSingularChainsIn_univ]
    exact Submodule.mem_top
  obtain ⟨K, hK, -, hcK⟩ :=
    exists_isCompact_subset_integralSingularChainsIn n (univ : Set X) hc
  exact ⟨K, hK, hcK⟩



theorem exists_isCompact_integralSingularHomologyMap_eq (n : ℕ)
    (α : integralSingularHomology (n + 1) X) :
    ∃ K : Set X, IsCompact K ∧ ∃ β : integralSingularHomology (n + 1) K,
      integralSingularHomologyMap (n + 1) (singularSubspaceInclusion K) β = α := by
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc (n + 1)) α
  have hdc : (integralSingularChains X).d (n + 1) n c.val = 0 := by
    have h : (integralSingularChains X).d (n + 1)
        ((ComplexShape.down ℕ).next (n + 1)) c.val = 0 := LinearMap.mem_ker.mp c.property
    rwa [ChainComplex.next_nat_succ] at h
  obtain ⟨K, hK, hcK⟩ := exists_isCompact_integralSingularChainsIn (n + 1) c.val
  rw [integralSingularChainsIn_eq_range] at hcK
  obtain ⟨c', hc'⟩ := hcK
  have hdc' : (integralSingularChains K).d (n + 1) n c' = 0 := by
    apply integralSingularChainInclusion_injective n K
    rw [integralSingularChainMap_boundary n (singularSubspaceInclusion K) c', hc']
    exact hdc.trans (LinearMap.map_zero _).symm
  have hdc'' : (integralSingularChains K).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1)) c' = 0 := by
    rw [ChainComplex.next_nat_succ]
    exact hdc'
  refine ⟨K, hK,
    moduleHomologyClass ((integralSingularChains K).sc (n + 1)) ⟨c', hdc''⟩, ?_⟩
  exact (moduleHomologyClass_map
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
        (n + 1)).map (integralSingularChainMap (singularSubspaceInclusion K)))
      ⟨c', hdc''⟩).trans
    ((congrArg (moduleHomologyClass ((integralSingularChains X).sc (n + 1)))
      (Subtype.ext hc')).trans hc)



theorem integralSingularHomology_succ_subsingleton_of_forall_isCompact_subset (n : ℕ)
    (h : ∀ K : Set X, IsCompact K →
      ∃ U : Set X, K ⊆ U ∧ Subsingleton (integralSingularHomology (n + 1) U)) :
    Subsingleton (integralSingularHomology (n + 1) X) := by
  have hzero : ∀ α : integralSingularHomology (n + 1) X, α = 0 := by
    intro α
    obtain ⟨K, hK, β, hβ⟩ := exists_isCompact_integralSingularHomologyMap_eq n α
    obtain ⟨U, hKU, hU⟩ := h K hK
    let ι : C(K, U) := ⟨Set.inclusion hKU, continuous_inclusion hKU⟩
    have hcomp : (singularSubspaceInclusion U).comp ι = singularSubspaceInclusion K :=
      ContinuousMap.ext fun _ => rfl
    have hmap : integralSingularHomologyMap (n + 1) ι β = 0 := hU.elim _ _
    rw [← hβ, ← hcomp, integralSingularHomologyMap_comp, LinearMap.comp_apply, hmap, map_zero]
  exact ⟨fun α β => by rw [hzero α, hzero β]⟩

end DifferentialGeometry.Topology
