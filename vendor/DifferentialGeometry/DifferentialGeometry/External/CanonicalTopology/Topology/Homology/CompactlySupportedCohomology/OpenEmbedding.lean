module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Defs
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainExcision

@[expose] public section
noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

omit [T2Space Y] in
theorem OpenEmbedding.compact_support_excision_mapsTo (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K : Compacts X) :
    MapsTo f (K : Set X)ᶜ (K.map f f.continuous : Set Y)ᶜ :=
  mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)

def OpenEmbedding.compactSupportExcision (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K : Compacts X) :
    integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ ≃ₗ[ℤ]
      integralRelativeCohomology n (K : Set X)ᶜ :=
  LinearEquiv.ofBijective (integralRelativeCohomologyMap n f
    (OpenEmbedding.compact_support_excision_mapsTo f hf K))
    (integralRelativeCohomologyMap_bijective_of_isOpenEmbedding n f hf K)

theorem OpenEmbedding.compact_support_excision_natural (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K L : Compacts X) (h : K ≤ L)
    (β : integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ) :
    OpenEmbedding.compactSupportExcision n f hf L
        (integralRelativeCohomologyMap n (ContinuousMap.id Y)
          (show MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
            (K.map f f.continuous : Set Y)ᶜ from
              compl_subset_compl.mpr (image_mono h)) β) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (OpenEmbedding.compactSupportExcision n f hf K β) := by
  have h₁ := integralRelativeCohomologyMap_comp n f (ContinuousMap.id Y)
    (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
      MapsTo f (L : Set X)ᶜ (L.map f f.continuous : Set Y)ᶜ)
    (show MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
      (K.map f f.continuous : Set Y)ᶜ from
        compl_subset_compl.mpr (image_mono h))
  have h₂ := integralRelativeCohomologyMap_comp n (ContinuousMap.id X) f
    (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr h)
    (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
      MapsTo f (K : Set X)ᶜ (K.map f f.continuous : Set Y)ᶜ)
  exact LinearMap.congr_fun (h₁.symm.trans h₂) β

def integralCompactlySupportedCohomologyPushforward (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) :
    integralCompactlySupportedCohomology n X →ₗ[ℤ]
      integralCompactlySupportedCohomology n Y :=
  integralCompactlySupportedCohomologyDesc n
    (fun K => (integralRelativeToCompactlySupportedCohomology n
      (K.map f f.continuous)).comp (OpenEmbedding.compactSupportExcision n f hf K).symm.toLinearMap)
    (by
      intro K L h α
      have heq : (OpenEmbedding.compactSupportExcision n f hf L).symm
          (integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
              compl_subset_compl.mpr h) α) =
          integralRelativeCohomologyMap n (ContinuousMap.id Y)
            (show MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
              (K.map f f.continuous : Set Y)ᶜ from
                compl_subset_compl.mpr (image_mono h))
            ((OpenEmbedding.compactSupportExcision n f hf K).symm α) := by
        apply (OpenEmbedding.compactSupportExcision n f hf L).injective
        rw [LinearEquiv.apply_symm_apply,
          OpenEmbedding.compact_support_excision_natural n f hf K L h,
          LinearEquiv.apply_symm_apply]
      change integralRelativeToCompactlySupportedCohomology n (L.map f f.continuous)
        ((OpenEmbedding.compactSupportExcision n f hf L).symm _) = _
      rw [heq]
      exact integralRelativeToCompactlySupportedCohomology_map n
        (K.map f f.continuous) (L.map f f.continuous) (image_mono h) _)

private theorem compact_support_pushforward_representative
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) (K : Compacts X)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K α) =
      integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous)
        ((OpenEmbedding.compactSupportExcision n f hf K).symm α) :=
  integralCompactlySupportedCohomologyDesc_representative n _ _ K α

theorem integralCompactlySupportedCohomologyPushforward_relative
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) (K : Compacts X)
    (β : integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K
          (integralRelativeCohomologyMap n f
            (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β)) =
      integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous) β := by
  rw [compact_support_pushforward_representative]
  exact congrArg (integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous))
    ((OpenEmbedding.compactSupportExcision n f hf K).symm_apply_apply β)

private theorem compact_support_pushforward_relative_of_eq
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (L : Compacts Y) (h : K.map f f.continuous = L)
    (hρ : MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ)
    (β : integralRelativeCohomology n (L : Set Y)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K
          (integralRelativeCohomologyMap n f hρ β)) =
      integralRelativeToCompactlySupportedCohomology n L β := by
  subst L
  exact integralCompactlySupportedCohomologyPushforward_relative n f hf K β

theorem integralCompactlySupportedCohomologyPushforward_forget
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) :
    (integralSingularCohomologyMap n f).comp
        ((integralCompactlySupportedToSingularCohomology n Y).comp
          (integralCompactlySupportedCohomologyPushforward n f hf)) =
      integralCompactlySupportedToSingularCohomology n X := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  let hρ := OpenEmbedding.compact_support_excision_mapsTo f hf K
  obtain ⟨β, hβ⟩ := (OpenEmbedding.compactSupportExcision n f hf K).surjective α
  change integralRelativeCohomologyMap n f hρ β = α at hβ
  simp only [LinearMap.comp_apply]
  rw [← hβ, compact_support_pushforward_relative_of_eq n f hf K
    (K.map f f.continuous) rfl hρ β,
    integralCompactlySupportedToSingularCohomology_representative,
    integralCompactlySupportedToSingularCohomology_representative]
  exact (LinearMap.congr_fun (integralRelativeToAbsoluteCohomology_natural n f hρ) β).symm

theorem integralCompactlySupportedCohomologyPushforward_id
    {X : Type u} [TopologicalSpace X] [T2Space X] (n : ℕ) :
    integralCompactlySupportedCohomologyPushforward n (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id = LinearMap.id := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  have hmap : K.map (ContinuousMap.id X) (ContinuousMap.id X).continuous = K :=
    Compacts.map_id K
  have h := compact_support_pushforward_relative_of_eq n (ContinuousMap.id X)
    _root_.Topology.IsOpenEmbedding.id K K hmap (show MapsTo (ContinuousMap.id X)
      (K : Set X)ᶜ (K : Set X)ᶜ from fun _ hx => hx) α
  rw [integralRelativeCohomologyMap_id, LinearMap.id_apply] at h
  exact h

theorem integralCompactlySupportedCohomologyPushforward_comp
    {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    (n : ℕ) (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g) :
    integralCompactlySupportedCohomologyPushforward n (g.comp f) (hg.comp hf) =
      (integralCompactlySupportedCohomologyPushforward n g hg).comp
        (integralCompactlySupportedCohomologyPushforward n f hf) := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  let L := K.map f f.continuous
  let N := L.map g g.continuous
  let hρf : MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ :=
    OpenEmbedding.compact_support_excision_mapsTo f hf K
  let hρg : MapsTo g (L : Set Y)ᶜ (N : Set Z)ᶜ :=
    OpenEmbedding.compact_support_excision_mapsTo g hg L
  obtain ⟨δ, hδ⟩ := (OpenEmbedding.compactSupportExcision n f hf K).surjective α
  change integralRelativeCohomologyMap n f hρf δ = α at hδ
  obtain ⟨β, hβ⟩ := (OpenEmbedding.compactSupportExcision n g hg L).surjective δ
  change integralRelativeCohomologyMap n g hρg β = δ at hβ
  simp only [LinearMap.comp_apply]
  rw [← hδ, ← hβ,
    compact_support_pushforward_relative_of_eq n f hf K L rfl hρf,
    compact_support_pushforward_relative_of_eq n g hg L N rfl hρg]
  have hmap : K.map (g.comp f) (g.comp f).continuous = N :=
    Compacts.map_comp g f g.continuous f.continuous K
  have hcomp := LinearMap.congr_fun (integralRelativeCohomologyMap_comp n f g hρf hρg) β
  have heq := congrArg (fun γ : integralRelativeCohomology n (K : Set X)ᶜ =>
    integralCompactlySupportedCohomologyPushforward n (g.comp f) (hg.comp hf)
      (integralRelativeToCompactlySupportedCohomology n K γ)) hcomp
  exact heq.symm.trans (compact_support_pushforward_relative_of_eq n (g.comp f)
    (hg.comp hf) K N hmap (hρg.comp hρf) β)

end DifferentialGeometry.Topology

end
