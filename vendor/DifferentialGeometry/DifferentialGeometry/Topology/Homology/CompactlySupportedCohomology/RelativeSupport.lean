module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.OpenEmbedding

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def RelativeSupport.compactSupportIn (U : Set X) (K : Compacts X) (hKU : (K : Set X) ⊆ U) : Compacts U :=
  ⟨Subtype.val ⁻¹' (K : Set X),
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' K.isCompact
      (by simpa only [Subtype.range_coe] using hKU)⟩

def integralRelativeToCompactlySupportedCohomologyOn (n : ℕ) (U : Set X)
    (K : Compacts X) (hKU : (K : Set X) ⊆ U) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ]
      integralCompactlySupportedCohomology n U :=
  (integralRelativeToCompactlySupportedCohomology n (RelativeSupport.compactSupportIn U K hKU)).comp
    (integralRelativeCohomologyMap n (singularSubspaceInclusion U)
      (show MapsTo (singularSubspaceInclusion U) (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ
        (K : Set X)ᶜ from fun _ hx => hx))

theorem integralRelativeToCompactlySupportedCohomologyOn_mono (n : ℕ) (U : Set X)
    (K L : Compacts X) (hKL : K ≤ L) (hKU : (K : Set X) ⊆ U) (hLU : (L : Set X) ⊆ U)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralRelativeToCompactlySupportedCohomologyOn n U L hLU
        (integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr hKL) α) =
      integralRelativeToCompactlySupportedCohomologyOn n U K hKU α := by
  let hK : MapsTo (singularSubspaceInclusion U) (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ
      (K : Set X)ᶜ := fun _ hx => hx
  let hL : MapsTo (singularSubspaceInclusion U) (RelativeSupport.compactSupportIn U L hLU : Set U)ᶜ
      (L : Set X)ᶜ := fun _ hx => hx
  have hKL' : RelativeSupport.compactSupportIn U K hKU ≤ RelativeSupport.compactSupportIn U L hLU := fun _ hx => hKL hx
  let hLX : MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ := compl_subset_compl.mpr hKL
  let hLU' : MapsTo (ContinuousMap.id U) (RelativeSupport.compactSupportIn U L hLU : Set U)ᶜ
      (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ := compl_subset_compl.mpr hKL'
  have h₁ := integralRelativeCohomologyMap_comp n (singularSubspaceInclusion U) (ContinuousMap.id X)
    hL hLX
  have h₂ := integralRelativeCohomologyMap_comp n (ContinuousMap.id U) (singularSubspaceInclusion U)
    hLU' hK
  have h := LinearMap.congr_fun (h₁.symm.trans h₂) α
  change integralRelativeToCompactlySupportedCohomology n (RelativeSupport.compactSupportIn U L hLU)
    ((integralRelativeCohomologyMap n (singularSubspaceInclusion U) hL)
      (integralRelativeCohomologyMap n (ContinuousMap.id X) hLX α)) = _
  simp only [LinearMap.comp_apply] at h
  rw [h]
  exact integralRelativeToCompactlySupportedCohomology_map n
    (RelativeSupport.compactSupportIn U K hKU) (RelativeSupport.compactSupportIn U L hLU) hKL' _

theorem integralRelativeToCompactlySupportedCohomologyOn_pushforward
    [T2Space X] (n : ℕ) (U : Set X) (hU : IsOpen U)
    (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion U)
        hU.isOpenEmbedding_subtypeVal (integralRelativeToCompactlySupportedCohomologyOn n U K hKU α) =
      integralRelativeToCompactlySupportedCohomology n K α := by
  have hmap : (RelativeSupport.compactSupportIn U K hKU).map (singularSubspaceInclusion U)
      (singularSubspaceInclusion U).continuous = K := by
    apply SetLike.coe_injective
    change Subtype.val '' (Subtype.val ⁻¹' (K : Set X)) = K
    rw [image_preimage_eq_of_subset]
    simpa only [Subtype.range_coe] using hKU
  have aux (L : Compacts X) (hL : (RelativeSupport.compactSupportIn U K hKU).map (singularSubspaceInclusion U)
      (singularSubspaceInclusion U).continuous = L)
      (hf : MapsTo (singularSubspaceInclusion U) (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ (L : Set X)ᶜ)
      (β : integralRelativeCohomology n (L : Set X)ᶜ) :
      integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion U)
          hU.isOpenEmbedding_subtypeVal
          (integralRelativeToCompactlySupportedCohomology n (RelativeSupport.compactSupportIn U K hKU)
            (integralRelativeCohomologyMap n (singularSubspaceInclusion U) hf β)) =
        integralRelativeToCompactlySupportedCohomology n L β := by
    subst L
    exact integralCompactlySupportedCohomologyPushforward_relative n (singularSubspaceInclusion U)
      hU.isOpenEmbedding_subtypeVal (RelativeSupport.compactSupportIn U K hKU) β
  exact aux K hmap (fun _ hx => hx) α

end DifferentialGeometry.Topology

end

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

theorem integralCompactlySupportedCohomologyOn_exists_representative
    (n : ℕ) (U : Set X) (hU : IsOpen U) (α : integralCompactlySupportedCohomology n U) :
    ∃ (K : Compacts X) (hKU : (K : Set X) ⊆ U)
      (β : integralRelativeCohomology n (K : Set X)ᶜ),
      integralRelativeToCompactlySupportedCohomologyOn n U K hKU β = α := by
  obtain ⟨L, γ, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
  let f := singularSubspaceInclusion U
  let K := L.map f f.continuous
  have hKU : (K : Set X) ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hL : RelativeSupport.compactSupportIn U K hKU = L := by
    apply SetLike.coe_injective
    change Subtype.val ⁻¹' (Subtype.val '' (L : Set U)) = (L : Set U)
    exact preimage_image_eq _ Subtype.val_injective
  have hb := integralRelativeCohomologyMap_bijective_of_isOpenEmbedding n f hU.isOpenEmbedding_subtypeVal L
  obtain ⟨β, hβ⟩ := hb.surjective γ
  refine ⟨K, hKU, β, ?_⟩
  have aux (N : Compacts U) (hN : N = L)
      (hf : MapsTo f (N : Set U)ᶜ (K : Set X)ᶜ) :
      integralRelativeToCompactlySupportedCohomology n N (integralRelativeCohomologyMap n f hf β) =
        integralRelativeToCompactlySupportedCohomology n L γ := by
    subst N
    exact congrArg (integralRelativeToCompactlySupportedCohomology n L) hβ
  exact aux (RelativeSupport.compactSupportIn U K hKU) hL (fun _ hx => hx)

theorem integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff
    (n : ℕ) (U : Set X) (hU : IsOpen U) (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralRelativeToCompactlySupportedCohomologyOn n U K hKU α = 0 ↔
      ∃ (L : Compacts X) (_ : (L : Set X) ⊆ U) (hKL : K ≤ L),
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr hKL) α = 0 := by
  constructor
  · intro hα
    change integralRelativeToCompactlySupportedCohomology n (RelativeSupport.compactSupportIn U K hKU) _ = 0 at hα
    obtain ⟨N, hKN, hzero⟩ := (integralRelativeToCompactlySupportedCohomology_eq_zero_iff n
      (RelativeSupport.compactSupportIn U K hKU) _).1 hα
    let f := singularSubspaceInclusion U
    let L := N.map f f.continuous
    have hLU : (L : Set X) ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
    have hKL : K ≤ L := by
      intro x hx
      exact ⟨⟨x, hKU hx⟩, hKN hx, rfl⟩
    refine ⟨L, hLU, hKL, ?_⟩
    let hf : MapsTo f (N : Set U)ᶜ (L : Set X)ᶜ :=
      mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)
    have hinj := (integralRelativeCohomologyMap_bijective_of_isOpenEmbedding n f
      hU.isOpenEmbedding_subtypeVal N).injective
    apply hinj
    erw [map_zero]
    have h₁ := integralRelativeCohomologyMap_comp n f (ContinuousMap.id X) hf
      (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from compl_subset_compl.mpr hKL)
    have h₂ := integralRelativeCohomologyMap_comp n (ContinuousMap.id U) f
      (show MapsTo (ContinuousMap.id U) (N : Set U)ᶜ (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ from
        compl_subset_compl.mpr hKN)
      (show MapsTo f (RelativeSupport.compactSupportIn U K hKU : Set U)ᶜ (K : Set X)ᶜ from fun _ hx => hx)
    exact (LinearMap.congr_fun (h₁.symm.trans h₂) α).trans hzero
  · rintro ⟨L, hLU, hKL, hα⟩
    rw [← integralRelativeToCompactlySupportedCohomologyOn_mono n U K L hKL hKU hLU α,
      hα, map_zero]

end DifferentialGeometry.Topology

end

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralRelativeToCompactlySupportedCohomologyOn_inclusion
    (n : ℕ) (U V : Set X) [T2Space V] (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → X) ⁻¹' U))
    (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion hUV)
        (_root_.Topology.IsOpenEmbedding.inclusion hUV hU)
        (integralRelativeToCompactlySupportedCohomologyOn n U K hKU α) =
      integralRelativeToCompactlySupportedCohomologyOn n V K (hKU.trans hUV) α := by
  let f := ContinuousMap.inclusion hUV
  let hf := _root_.Topology.IsOpenEmbedding.inclusion hUV hU
  let KU := RelativeSupport.compactSupportIn U K hKU
  let KV := RelativeSupport.compactSupportIn V K (hKU.trans hUV)
  have hmap : KU.map f f.continuous = KV := by
    apply SetLike.coe_injective
    change Set.inclusion hUV '' (Subtype.val ⁻¹' (K : Set X)) = Subtype.val ⁻¹' (K : Set X)
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val, hKU hx⟩, hx, rfl⟩
  let hρU : MapsTo (singularSubspaceInclusion U) (KU : Set U)ᶜ (K : Set X)ᶜ :=
    fun _ hx => hx
  let hρf : MapsTo f (KU : Set U)ᶜ (KV : Set V)ᶜ := fun _ hx => hx
  let hρV : MapsTo (singularSubspaceInclusion V) (KV : Set V)ᶜ (K : Set X)ᶜ :=
    fun _ hx => hx
  let βU := integralRelativeCohomologyMap n (singularSubspaceInclusion U) hρU α
  let βV := integralRelativeCohomologyMap n (singularSubspaceInclusion V) hρV α
  have hcomp := integralRelativeCohomologyMap_comp n f (singularSubspaceInclusion V)
    hρf hρV
  have hmaprel : integralRelativeCohomologyMap n f hρf βV = βU := by
    exact (LinearMap.congr_fun hcomp α).symm
  change integralCompactlySupportedCohomologyPushforward n f hf
      (integralRelativeToCompactlySupportedCohomology n KU βU) =
    integralRelativeToCompactlySupportedCohomology n KV βV
  rw [← hmaprel]
  have aux (L : Compacts V) (hL : KU.map f f.continuous = L)
      (hρ : MapsTo f (KU : Set U)ᶜ (L : Set V)ᶜ)
      (β : integralRelativeCohomology n (L : Set V)ᶜ) :
      integralCompactlySupportedCohomologyPushforward n f hf
          (integralRelativeToCompactlySupportedCohomology n KU
            (integralRelativeCohomologyMap n f hρ β)) =
        integralRelativeToCompactlySupportedCohomology n L β := by
    subst L
    exact integralCompactlySupportedCohomologyPushforward_relative n f hf KU β
  exact aux KV hmap hρf βV

end DifferentialGeometry.Topology

end
