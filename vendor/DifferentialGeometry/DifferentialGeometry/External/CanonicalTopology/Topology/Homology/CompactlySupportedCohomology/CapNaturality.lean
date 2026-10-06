module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Cap
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.OpenEmbedding
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapToAbsoluteHomology
public import Mathlib.Topology.Sets.Compacts

@[expose] public section
noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

private theorem compact_support_cap_representative_natural
    (k m : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) (cX : integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (cY : integralRelativeHomology (k + m) (K.map f f.continuous : Set Y)ᶜ)
    (hc : integralRelativeHomologyMap (k + m) f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) cX = cY)
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y)
    (β : integralRelativeCohomology k (K.map f f.continuous : Set Y)ᶜ)
    (hX : DX (integralRelativeToCompactlySupportedCohomology k K
      (integralRelativeCohomologyMap k f
        (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β)) =
      integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m
        (integralRelativeCohomologyMap k f
          (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β) cX)
    (hY : DY (integralRelativeToCompactlySupportedCohomology k (K.map f f.continuous) β) =
      integralRelativeCohomologyCapToAbsolute (K.map f f.continuous : Set Y)ᶜ k m β cY) :
    integralSingularHomologyMap m f
        (DX (integralRelativeToCompactlySupportedCohomology k K
          (integralRelativeCohomologyMap k f
            (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β))) =
      DY (integralCompactlySupportedCohomologyPushforward k f hf
        (integralRelativeToCompactlySupportedCohomology k K
          (integralRelativeCohomologyMap k f
            (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β))) := by
  rw [hX, integralCompactlySupportedCohomologyPushforward_relative, hY]
  exact (integralRelativeCohomologyCapToAbsolute_natural k m f
    (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β cX).trans
      (congrArg (integralRelativeCohomologyCapToAbsolute
        (K.map f f.continuous : Set Y)ᶜ k m β) hc)

private theorem compact_support_hom_ext_of_open_excision
    (k : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    {P : Type*} [AddCommMonoid P] [Module ℤ P]
    (a b : integralCompactlySupportedCohomology k X →ₗ[ℤ] P)
    (h : ∀ (K : Compacts X)
      (β : integralRelativeCohomology k (K.map f f.continuous : Set Y)ᶜ),
      a (integralRelativeToCompactlySupportedCohomology k K
          (integralRelativeCohomologyMap k f
            (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β)) =
        b (integralRelativeToCompactlySupportedCohomology k K
          (integralRelativeCohomologyMap k f
            (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β))) : a = b := by
  apply integralCompactlySupportedCohomology_hom_ext k (f := a) (g := b)
  intro K α
  obtain ⟨β, hβ⟩ :=
    (integralRelativeCohomologyMap_bijective_of_isOpenEmbedding k f hf K).surjective α
  exact (congrArg (fun γ => a (integralRelativeToCompactlySupportedCohomology k K γ)) hβ).symm.trans
    ((h K β).trans
      (congrArg (fun γ => b (integralRelativeToCompactlySupportedCohomology k K γ)) hβ))

private theorem compact_support_cap_natural
    (k m : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (cY : ∀ L : Compacts Y, integralRelativeHomology (k + m) (L : Set Y)ᶜ)
    (hc : ∀ K : Compacts X,
      integralRelativeHomologyMap (k + m) f
        (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) (cX K) =
          cY (K.map f f.continuous))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y)
    (hX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K))
    (hY : ∀ (L : Compacts Y) (β : integralRelativeCohomology k (L : Set Y)ᶜ),
      DY (integralRelativeToCompactlySupportedCohomology k L β) =
        integralRelativeCohomologyCapToAbsolute (L : Set Y)ᶜ k m β (cY L)) :
    (integralSingularHomologyMap m f).comp DX =
      DY.comp (integralCompactlySupportedCohomologyPushforward k f hf) := by
  apply compact_support_hom_ext_of_open_excision k f hf
    ((integralSingularHomologyMap m f).comp DX)
    (DY.comp (integralCompactlySupportedCohomologyPushforward k f hf))
  intro K β
  exact compact_support_cap_representative_natural k m f hf K (cX K)
    (cY (K.map f f.continuous)) (hc K) DX DY β
    (hX K (integralRelativeCohomologyMap k f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) β))
    (hY (K.map f f.continuous) β)

theorem exists_integralCompactlySupportedCohomology_cap_natural
    (k m : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (cY : ∀ L : Compacts Y, integralRelativeHomology (k + m) (L : Set Y)ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (cX L) = cX K)
    (hY : ∀ (K L : Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id Y)
        (show MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ from
          compl_subset_compl.mpr h) (cY L) = cY K)
    (hc : ∀ K : Compacts X,
      integralRelativeHomologyMap (k + m) f
        (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) (cX K) =
          cY (K.map f f.continuous)) :
    ∃ (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
      (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y),
      (∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        DX (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) ∧
      (∀ (L : Compacts Y) (β : integralRelativeCohomology k (L : Set Y)ᶜ),
        DY (integralRelativeToCompactlySupportedCohomology k L β) =
          integralRelativeCohomologyCapToAbsolute (L : Set Y)ᶜ k m β (cY L)) ∧
      (integralSingularHomologyMap m f).comp DX =
        DY.comp (integralCompactlySupportedCohomologyPushforward k f hf) := by
  obtain ⟨DX, hDX, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cX hX
  obtain ⟨DY, hDY, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cY hY
  exact ⟨DX, DY, hDX, hDY, compact_support_cap_natural k m f hf cX cY hc DX DY hDX hDY⟩

theorem exists_integralCompactlySupportedCohomology_cap_of_absolute_natural
    (k m : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (c : integralSingularHomology (k + m) X) :
    ∃ (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
      (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y),
      (∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        DX (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α
            (integralAbsoluteToRelative (k + m) (K : Set X)ᶜ c)) ∧
      (∀ (L : Compacts Y) (β : integralRelativeCohomology k (L : Set Y)ᶜ),
        DY (integralRelativeToCompactlySupportedCohomology k L β) =
          integralRelativeCohomologyCapToAbsolute (L : Set Y)ᶜ k m β
            (integralAbsoluteToRelative (k + m) (L : Set Y)ᶜ
              (integralSingularHomologyMap (k + m) f c))) ∧
      (∀ α : integralCompactlySupportedCohomology k X,
        DX α = integralSingularCohomologyCapProduct k m
          (integralCompactlySupportedToSingularCohomology k X α) c) ∧
      (∀ β : integralCompactlySupportedCohomology k Y,
        DY β = integralSingularCohomologyCapProduct k m
          (integralCompactlySupportedToSingularCohomology k Y β)
          (integralSingularHomologyMap (k + m) f c)) ∧
      (integralSingularHomologyMap m f).comp DX =
        DY.comp (integralCompactlySupportedCohomologyPushforward k f hf) := by
  obtain ⟨DX, ⟨hDX, hDX'⟩, _⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap_of_absolute k m c
  obtain ⟨DY, ⟨hDY, hDY'⟩, _⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap_of_absolute k m
      (integralSingularHomologyMap (k + m) f c)
  refine ⟨DX, DY, hDX, hDY, hDX', hDY', ?_⟩
  apply compact_support_cap_natural k m f hf
    (fun K => integralAbsoluteToRelative (k + m) (K : Set X)ᶜ c)
    (fun L => integralAbsoluteToRelative (k + m) (L : Set Y)ᶜ
      (integralSingularHomologyMap (k + m) f c)) ?_ DX DY hDX hDY
  intro K
  exact (LinearMap.congr_fun (integralAbsoluteToRelative_natural (k + m) f
    (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective))) c).symm

end DifferentialGeometry.Topology

end
