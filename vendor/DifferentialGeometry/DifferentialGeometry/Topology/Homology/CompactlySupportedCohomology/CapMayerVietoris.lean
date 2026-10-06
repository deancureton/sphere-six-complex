module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.MayerVietoris
public import DifferentialGeometry.Topology.Homology.RelativeCapMayerVietoris
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.SupportPairRepresentatives
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Cap

@[expose] public section

noncomputable section

open Set TopologicalSpace

open CategoryTheory

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

private def compactSubsetPreimage (W : Set X) (K : Compacts X) (hKW : (K : Set X) ⊆ W) : Compacts W :=
  ⟨Subtype.val ⁻¹' (K : Set X),
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' K.isCompact
      (by simpa only [Subtype.range_coe] using hKW)⟩

private theorem compactSubsetPreimage_map (W : Set X) (K : Compacts X)
    (hKW : (K : Set X) ⊆ W) :
    (compactSubsetPreimage W K hKW).map (singularSubspaceInclusion W)
      (singularSubspaceInclusion W).continuous = K := by
  apply SetLike.coe_injective
  change Subtype.val '' (Subtype.val ⁻¹' (K : Set X)) = (K : Set X)
  apply image_preimage_eq_of_subset
  simpa only [Subtype.range_coe] using hKW

private theorem integralCompactlySupportedCohomology_cap_family_on
    (k m : ℕ) (W : Set X)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m + 1) (K : Set X)ᶜ)
    (cW : ∀ L : Compacts W, integralRelativeHomology ((k + 1) + m) (L : Set W)ᶜ)
    (hc : ∀ L : Compacts W,
      integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion W)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW L) =
      (eqToHom (congrArg (fun n => integralRelativeHomology n
        (L.map (singularSubspaceInclusion W) (singularSubspaceInclusion W).continuous : Set X)ᶜ)
        (show k + m + 1 = (k + 1) + m by omega)))
        (cX (L.map (singularSubspaceInclusion W) (singularSubspaceInclusion W).continuous)))
    (K : Compacts X) (hKW : (K : Set X) ⊆ W) :
    integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion W)
      (show MapsTo (singularSubspaceInclusion W)
        (compactSubsetPreimage W K hKW : Set W)ᶜ (K : Set X)ᶜ from fun _ hx => hx)
      (cW (compactSubsetPreimage W K hKW)) =
    (eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set X)ᶜ)
      (show k + m + 1 = (k + 1) + m by omega))) (cX K) := by
  let L := compactSubsetPreimage W K hKW
  have aux (J : Compacts X)
      (hJ : L.map (singularSubspaceInclusion W) (singularSubspaceInclusion W).continuous = J)
      (hmap : MapsTo (singularSubspaceInclusion W) (L : Set W)ᶜ (J : Set X)ᶜ) :
      integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion W) hmap (cW L) =
        (eqToHom (congrArg (fun n => integralRelativeHomology n (J : Set X)ᶜ)
          (show k + m + 1 = (k + 1) + m by omega))) (cX J) := by
    subst J
    exact hc L
  exact aux K (compactSubsetPreimage_map W K hKW) _

private theorem integralCompactlySupportedCohomology_cap_on_representative
    (k m : ℕ) (W : Set X)
    (c : ∀ L : Compacts W, integralRelativeHomology (k + m) (L : Set W)ᶜ)
    (D : integralCompactlySupportedCohomology k W →ₗ[ℤ] integralSingularHomology m W)
    (hD : ∀ (L : Compacts W) (β : integralRelativeCohomology k (L : Set W)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k L β) =
        integralRelativeCohomologyCapToAbsolute (L : Set W)ᶜ k m β (c L))
    (K : Compacts X) (hKW : (K : Set X) ⊆ W)
    (α : integralRelativeCohomology k (K : Set X)ᶜ) :
    D (integralRelativeToCompactlySupportedCohomologyOn k W K hKW α) =
      integralRelativeCohomologyCapToAbsolute (compactSubsetPreimage W K hKW : Set W)ᶜ k m
        (integralRelativeCohomologyMap k (singularSubspaceInclusion W)
          (show MapsTo (singularSubspaceInclusion W)
            (compactSubsetPreimage W K hKW : Set W)ᶜ (K : Set X)ᶜ from fun _ hx => hx) α)
        (c (compactSubsetPreimage W K hKW)) :=
  hD (compactSubsetPreimage W K hKW) _

private theorem integralCompactlySupportedCohomology_cap_family_inter
    [T2Space X] (k m : ℕ) (W : Set X)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m + 1) (K : Set X)ᶜ)
    (cW : ∀ L : Compacts W, integralRelativeHomology ((k + 1) + m) (L : Set W)ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hc : ∀ L : Compacts W,
      integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion W)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW L) =
      (eqToHom (congrArg (fun n => integralRelativeHomology n
        (L.map (singularSubspaceInclusion W) (singularSubspaceInclusion W).continuous : Set X)ᶜ)
        (show k + m + 1 = (k + 1) + m by omega)))
        (cX (L.map (singularSubspaceInclusion W) (singularSubspaceInclusion W).continuous)))
    (A B : Compacts X) (hABW : ((A ⊓ B : Compacts X) : Set X) ⊆ W) :
    integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion W)
      (show MapsTo (singularSubspaceInclusion W)
        (compactSubsetPreimage W (A ⊓ B) hABW : Set W)ᶜ ((A ⊓ B : Compacts X) : Set X)ᶜ
        from fun _ hx => hx)
      (cW (compactSubsetPreimage W (A ⊓ B) hABW)) =
    (eqToHom (congrArg (fun n => integralRelativeHomology n ((A ⊓ B : Compacts X) : Set X)ᶜ)
      (show k + m + 1 = (k + 1) + m by omega)))
      (integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
        (show ((A ⊔ B : Compacts X) : Set X)ᶜ ⊆ ((A ⊓ B : Compacts X) : Set X)ᶜ from
          compl_subset_compl.mpr (inf_le_left.trans le_sup_left)) (cX (A ⊔ B))) := by
  rw [hX (A ⊓ B) (A ⊔ B) (inf_le_left.trans le_sup_left)]
  exact integralCompactlySupportedCohomology_cap_family_on k m W cX cW hc (A ⊓ B) hABW


theorem integralCompactlySupportedCohomology_cap_mayerVietoris
    {X : Type} [TopologicalSpace X] [T2Space X]
    (k m : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m + 1) (K : Set X)ᶜ)
    (cW : ∀ L : Compacts ↥(U ∩ V),
      integralRelativeHomology ((k + 1) + m) (L : Set ↥(U ∩ V))ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hc : ∀ L : Compacts ↥(U ∩ V),
      integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW L) =
      (eqToHom (congrArg (fun n => integralRelativeHomology n
        (L.map (singularSubspaceInclusion (U ∩ V))
          (singularSubspaceInclusion (U ∩ V)).continuous : Set X)ᶜ)
        (show k + m + 1 = (k + 1) + m by omega)))
        (cX (L.map (singularSubspaceInclusion (U ∩ V))
          (singularSubspaceInclusion (U ∩ V)).continuous)))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology (m + 1) X)
    (DW : integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V) →ₗ[ℤ]
      integralSingularHomology m ↥(U ∩ V))
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k (m + 1) α (cX K))
    (hDW : ∀ (L : Compacts ↥(U ∩ V))
      (β : integralRelativeCohomology (k + 1) (L : Set ↥(U ∩ V))ᶜ),
      DW (integralRelativeToCompactlySupportedCohomology (k + 1) L β) =
        integralRelativeCohomologyCapToAbsolute (L : Set ↥(U ∩ V))ᶜ (k + 1) m β (cW L))
    (α : integralCompactlySupportedCohomology k ↥(U ∪ V)) :
    DW (integralCompactlySupportedMayerVietorisConnecting k U V hU hV α) =
      (-1 : ℤ) ^ (k + 1) •
        Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
          (TopCat.of X) U V hU hV hUV m
          (DX (integralCompactlySupportedCohomologyPushforward k
            (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal α)) := by
  obtain ⟨A, B, hA, hB, β, rfl⟩ :=
    integralCompactlySupportedCohomologyOn_union_exists_representative k U V hU hV α
  rw [integralCompactlySupportedMayerVietorisConnecting_representative k U V hU hV A B hA hB,
    integralRelativeToCompactlySupportedCohomologyOn_pushforward k (U ∪ V) (hU.union hV)
      (A ⊔ B) (union_subset_union hA hB), hDX]
  have hrep := integralCompactlySupportedCohomology_cap_on_representative
    (k + 1) m (U ∩ V) cW DW hDW (A ⊓ B) (fun _ hx => ⟨hA hx.1, hB hx.2⟩)
    (integralCohomologyWithSupportMayerVietorisConnecting k (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed β)
  apply hrep.trans
  exact integralCohomologyWithSupportCapToAbsolute_mayerVietoris k m U V
    (A : Set X) (B : Set X) hU hV A.isCompact.isClosed B.isCompact.isClosed hUV hA hB
    β (cX (A ⊔ B))
    (cW (compactSubsetPreimage (U ∩ V) (A ⊓ B) (fun _ hx => ⟨hA hx.1, hB hx.2⟩)))
    (integralCompactlySupportedCohomology_cap_family_inter k m (U ∩ V) cX cW hX hc
      A B (fun _ hx => ⟨hA hx.1, hB hx.2⟩))

theorem exists_integralCompactlySupportedCohomology_cap_mayerVietoris
    {X : Type} [TopologicalSpace X] [T2Space X]
    (k m : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m + 1) (K : Set X)ᶜ)
    (cW : ∀ L : Compacts ↥(U ∩ V),
      integralRelativeHomology ((k + 1) + m) (L : Set ↥(U ∩ V))ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m + 1) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hW : ∀ (K L : Compacts ↥(U ∩ V)) (h : K ≤ L),
      integralRelativeHomologyMap ((k + 1) + m) (ContinuousMap.id ↥(U ∩ V))
        (show (L : Set ↥(U ∩ V))ᶜ ⊆ (K : Set ↥(U ∩ V))ᶜ from
          compl_subset_compl.mpr h) (cW L) = cW K)
    (hc : ∀ L : Compacts ↥(U ∩ V),
      integralRelativeHomologyMap ((k + 1) + m) (singularSubspaceInclusion (U ∩ V))
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW L) =
      (eqToHom (congrArg (fun n => integralRelativeHomology n
        (L.map (singularSubspaceInclusion (U ∩ V))
          (singularSubspaceInclusion (U ∩ V)).continuous : Set X)ᶜ)
        (show k + m + 1 = (k + 1) + m by omega)))
        (cX (L.map (singularSubspaceInclusion (U ∩ V))
          (singularSubspaceInclusion (U ∩ V)).continuous)))
    : ∃ (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology (m + 1) X)
      (DW : integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V) →ₗ[ℤ]
        integralSingularHomology m ↥(U ∩ V)),
      (∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        DX (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k (m + 1) α (cX K)) ∧
      (∀ (L : Compacts ↥(U ∩ V))
        (β : integralRelativeCohomology (k + 1) (L : Set ↥(U ∩ V))ᶜ),
        DW (integralRelativeToCompactlySupportedCohomology (k + 1) L β) =
          integralRelativeCohomologyCapToAbsolute (L : Set ↥(U ∩ V))ᶜ (k + 1) m β (cW L)) ∧
      ∀ α : integralCompactlySupportedCohomology k ↥(U ∪ V),
        DW (integralCompactlySupportedMayerVietorisConnecting k U V hU hV α) =
          (-1 : ℤ) ^ (k + 1) •
            Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
              (TopCat.of X) U V hU hV hUV m
              (DX (integralCompactlySupportedCohomologyPushforward k
                (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal α)) := by
  obtain ⟨DX, hDX, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k (m + 1) cX hX
  obtain ⟨DW, hDW, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap (k + 1) m cW hW
  exact ⟨DX, DW, hDX, hDW,
    integralCompactlySupportedCohomology_cap_mayerVietoris k m U V hU hV hUV
      cX cW hX hc DX DW hDX hDW⟩

end DifferentialGeometry.Topology
