module

public import DifferentialGeometry.Topology.Homology.CohomologyWithSupportMayerVietoris
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

def MayerVietoris.supportPairConnecting (n : ℕ) (U V : Set X) (K L : Compacts X)
    (hKU : (K : Set X) ⊆ U) (hLV : (L : Set X) ⊆ V) :
    integralRelativeCohomology n ((K ⊔ L : Compacts X) : Set X)ᶜ →ₗ[ℤ]
      integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V) :=
  (integralRelativeToCompactlySupportedCohomologyOn (n + 1) (U ∩ V) (K ⊓ L)
      (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩)).comp
    (integralCohomologyWithSupportMayerVietorisConnecting n (K : Set X) (L : Set X)
      K.isCompact.isClosed L.isCompact.isClosed)

theorem MayerVietoris.exists_compact_support_pair (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (K : Compacts X) :
    ∃ (A B : Compacts X), (A : Set X) ⊆ U ∧ (B : Set X) ⊆ V ∧ K ≤ A ⊔ B := by
  obtain ⟨A, B, hA, hB, hAU, hBV, hK⟩ := K.isCompact.binary_compact_cover hU hV
    (show (K : Set X) ⊆ U ∪ V from hUV ▸ subset_univ _)
  exact ⟨⟨A, hA⟩, ⟨B, hB⟩, hAU, hBV, by change (K : Set X) ⊆ A ∪ B; rw [hK]⟩

def MayerVietoris.relativeSupportMap (n : ℕ) (K L : Compacts X) (h : K ≤ L) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ] integralRelativeCohomology n (L : Set X)ᶜ :=
  integralRelativeCohomologyMap n (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from compl_subset_compl.mpr h)

omit [T2Space X] in
theorem MayerVietoris.relativeSupportMap_comp (n : ℕ) (K L N : Compacts X)
    (hKL : K ≤ L) (hLN : L ≤ N) :
    (MayerVietoris.relativeSupportMap n L N hLN).comp (MayerVietoris.relativeSupportMap n K L hKL) =
      MayerVietoris.relativeSupportMap n K N (hKL.trans hLN) :=
  (integralRelativeCohomologyMap_comp n (ContinuousMap.id X) (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) (N : Set X)ᶜ (L : Set X)ᶜ from compl_subset_compl.mpr hLN)
    (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from compl_subset_compl.mpr hKL)).symm

omit [T2Space X] in
private theorem relativeSupportMap_id (n : ℕ) (K : Compacts X) :
    MayerVietoris.relativeSupportMap n K K le_rfl = LinearMap.id := integralRelativeCohomologyMap_id n (K : Set X)ᶜ

def MayerVietoris.supportPairConnectingFrom (n : ℕ) (U V : Set X) (K A B : Compacts X)
    (hK : K ≤ A ⊔ B) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ]
      integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V) :=
  (MayerVietoris.supportPairConnecting n U V A B hA hB).comp (MayerVietoris.relativeSupportMap n K (A ⊔ B) hK)

theorem MayerVietoris.supportPairConnecting_mono (n : ℕ) (U V : Set X)
    (A B C D : Compacts X) (hAC : A ≤ C) (hBD : B ≤ D)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V)
    (hCU : (C : Set X) ⊆ U) (hDV : (D : Set X) ⊆ V)
    (α : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ) :
    MayerVietoris.supportPairConnecting n U V C D hCU hDV
        (MayerVietoris.relativeSupportMap n (A ⊔ B) (C ⊔ D) (sup_le_sup hAC hBD) α) =
      MayerVietoris.supportPairConnecting n U V A B hAU hBV α := by
  have h := integralCohomologyWithSupportMayerVietorisConnecting_natural n
    (A : Set X) (B : Set X) (C : Set X) (D : Set X)
    A.isCompact.isClosed B.isCompact.isClosed C.isCompact.isClosed D.isCompact.isClosed
    hAC hBD
  simp only [MayerVietoris.supportPairConnecting, MayerVietoris.relativeSupportMap, LinearMap.comp_apply]
  have hh := LinearMap.congr_fun h α
  simp only [LinearMap.comp_apply] at hh
  rw [← hh]
  exact integralRelativeToCompactlySupportedCohomologyOn_mono (n + 1) (U ∩ V)
    (A ⊓ B) (C ⊓ D) (inf_le_inf hAC hBD) _ _ _

theorem MayerVietoris.supportPairConnectingFrom_mono (n : ℕ) (U V : Set X)
    (K A B C D : Compacts X) (hK : K ≤ A ⊔ B) (hAC : A ≤ C) (hBD : B ≤ D)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V)
    (hCU : (C : Set X) ⊆ U) (hDV : (D : Set X) ⊆ V) :
    MayerVietoris.supportPairConnectingFrom n U V K C D (hK.trans (sup_le_sup hAC hBD)) hCU hDV =
      MayerVietoris.supportPairConnectingFrom n U V K A B hK hAU hBV := by
  ext α
  have h := LinearMap.congr_fun (MayerVietoris.relativeSupportMap_comp n K (A ⊔ B) (C ⊔ D)
    hK (sup_le_sup hAC hBD)) α
  change MayerVietoris.supportPairConnecting n U V C D hCU hDV
    (MayerVietoris.relativeSupportMap n K (C ⊔ D) _ α) = _
  rw [← h]
  exact MayerVietoris.supportPairConnecting_mono n U V A B C D hAC hBD hAU hBV hCU hDV _

theorem MayerVietoris.supportPairConnectingFrom_independent (n : ℕ) (U V : Set X)
    (K A B C D : Compacts X) (hK : K ≤ A ⊔ B) (hK' : K ≤ C ⊔ D)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V)
    (hCU : (C : Set X) ⊆ U) (hDV : (D : Set X) ⊆ V) :
    MayerVietoris.supportPairConnectingFrom n U V K A B hK hAU hBV =
      MayerVietoris.supportPairConnectingFrom n U V K C D hK' hCU hDV := by
  exact (MayerVietoris.supportPairConnectingFrom_mono n U V K A B (A ⊔ C) (B ⊔ D) hK
    le_sup_left le_sup_left hAU hBV (union_subset hAU hCU) (union_subset hBV hDV)).symm.trans
      (MayerVietoris.supportPairConnectingFrom_mono n U V K C D (A ⊔ C) (B ⊔ D) hK'
        le_sup_right le_sup_right hCU hDV (union_subset hAU hCU) (union_subset hBV hDV))

def MayerVietoris.supportCoverPair (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (K : Compacts X) :
    { p : Compacts X × Compacts X // (p.1 : Set X) ⊆ U ∧ (p.2 : Set X) ⊆ V ∧ K ≤ p.1 ⊔ p.2 } :=
  Classical.choice (by
    obtain ⟨A, B, hA, hB, hK⟩ := MayerVietoris.exists_compact_support_pair U V hU hV hUV K
    exact ⟨⟨(A, B), hA, hB, hK⟩⟩)

def MayerVietoris.supportCoverConnectingAt (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (K : Compacts X) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ]
      integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V) :=
  let p := MayerVietoris.supportCoverPair U V hU hV hUV K
  MayerVietoris.supportPairConnectingFrom n U V K p.val.1 p.val.2 p.property.2.2 p.property.1 p.property.2.1

theorem MayerVietoris.supportCoverConnectingAt_eq (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (K A B : Compacts X) (hK : K ≤ A ⊔ B)
    (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V) :
    MayerVietoris.supportCoverConnectingAt n U V hU hV hUV K =
      MayerVietoris.supportPairConnectingFrom n U V K A B hK hA hB := by
  exact MayerVietoris.supportPairConnectingFrom_independent n U V K _ _ A B _ hK _ _ hA hB

theorem MayerVietoris.supportCoverConnectingAt_mono (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (K L : Compacts X) (hKL : K ≤ L)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    MayerVietoris.supportCoverConnectingAt n U V hU hV hUV L (MayerVietoris.relativeSupportMap n K L hKL α) =
      MayerVietoris.supportCoverConnectingAt n U V hU hV hUV K α := by
  obtain ⟨A, B, hA, hB, hL⟩ := MayerVietoris.exists_compact_support_pair U V hU hV hUV L
  rw [MayerVietoris.supportCoverConnectingAt_eq n U V hU hV hUV L A B hL hA hB,
    MayerVietoris.supportCoverConnectingAt_eq n U V hU hV hUV K A B (hKL.trans hL) hA hB]
  exact congrArg (MayerVietoris.supportPairConnecting n U V A B hA hB)
    (LinearMap.congr_fun (MayerVietoris.relativeSupportMap_comp n K L (A ⊔ B) hKL hL) α)

def MayerVietoris.compactSupportCoverConnecting (n : ℕ)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) :
    integralCompactlySupportedCohomology n X →ₗ[ℤ]
      integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V) :=
  integralCompactlySupportedCohomologyDesc n (MayerVietoris.supportCoverConnectingAt n U V hU hV hUV)
    (MayerVietoris.supportCoverConnectingAt_mono n U V hU hV hUV)

private theorem compactSupportCoverConnecting_representative (n : ℕ)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (A B : Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
    (α : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ) :
    MayerVietoris.compactSupportCoverConnecting n U V hU hV hUV
        (integralRelativeToCompactlySupportedCohomology n (A ⊔ B) α) =
      integralRelativeToCompactlySupportedCohomologyOn (n + 1) (U ∩ V) (A ⊓ B)
        (fun _ hx => ⟨hA hx.1, hB hx.2⟩)
        (integralCohomologyWithSupportMayerVietorisConnecting n (A : Set X) (B : Set X)
          A.isCompact.isClosed B.isCompact.isClosed α) := by
  have h := integralCompactlySupportedCohomologyDesc_representative n
    (MayerVietoris.supportCoverConnectingAt n U V hU hV hUV)
    (MayerVietoris.supportCoverConnectingAt_mono n U V hU hV hUV) (A ⊔ B) α
  refine h.trans ?_
  rw [MayerVietoris.supportCoverConnectingAt_eq n U V hU hV hUV (A ⊔ B) A B le_rfl hA hB]
  simp only [MayerVietoris.supportPairConnectingFrom, relativeSupportMap_id, LinearMap.comp_id,
    MayerVietoris.supportPairConnecting, LinearMap.comp_apply]

private theorem supportPairConnecting_eq_zero_iff (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (A B : Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
    (α : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ) :
    MayerVietoris.supportPairConnecting n U V A B hA hB α = 0 ↔
      ∃ (C D : Compacts X) (hAC : A ≤ C) (hBD : B ≤ D),
        (C : Set X) ⊆ U ∧ (D : Set X) ⊆ V ∧
        integralCohomologyWithSupportMayerVietorisConnecting n (C : Set X) (D : Set X)
          C.isCompact.isClosed D.isCompact.isClosed
          (MayerVietoris.relativeSupportMap n (A ⊔ B) (C ⊔ D) (sup_le_sup hAC hBD) α) = 0 := by
  constructor
  · intro hα
    obtain ⟨L, hL, hABL, hzero⟩ :=
      (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff (n + 1) (U ∩ V)
        (hU.inter hV) (A ⊓ B) (fun _ hx => ⟨hA hx.1, hB hx.2⟩) _).1 hα
    refine ⟨A ⊔ L, B ⊔ L, le_sup_left, le_sup_left,
      union_subset hA (fun _ hx => (hL hx).1),
      union_subset hB (fun _ hx => (hL hx).2), ?_⟩
    have hLC : L ≤ (A ⊔ L) ⊓ (B ⊔ L) := le_inf le_sup_right le_sup_right
    have hcomp := LinearMap.congr_fun
      (MayerVietoris.relativeSupportMap_comp (n + 1) (A ⊓ B) L ((A ⊔ L) ⊓ (B ⊔ L)) hABL hLC)
      (integralCohomologyWithSupportMayerVietorisConnecting n (A : Set X) (B : Set X)
        A.isCompact.isClosed B.isCompact.isClosed α)
    have hnat := LinearMap.congr_fun
      (integralCohomologyWithSupportMayerVietorisConnecting_natural n
        (A : Set X) (B : Set X) ((A ⊔ L : Compacts X) : Set X)
        ((B ⊔ L : Compacts X) : Set X) A.isCompact.isClosed B.isCompact.isClosed
        (A ⊔ L).isCompact.isClosed (B ⊔ L).isCompact.isClosed le_sup_left le_sup_left) α
    simp only [LinearMap.comp_apply] at hnat hcomp
    change MayerVietoris.relativeSupportMap (n + 1) (A ⊓ B) L hABL _ = 0 at hzero
    exact hnat.symm.trans (hcomp.symm.trans (by rw [hzero, map_zero]))
  · rintro ⟨C, D, hAC, hBD, hC, hD, hzero⟩
    rw [← MayerVietoris.supportPairConnecting_mono n U V A B C D hAC hBD hA hB hC hD α]
    simp only [MayerVietoris.supportPairConnecting, LinearMap.comp_apply, hzero, map_zero]

omit [T2Space X] in
private theorem support_pair_sum_representative_on (n : ℕ) (W : Set X) (A B : Compacts X)
    (hA : (A : Set X) ⊆ W) (hB : (B : Set X) ⊆ W)
    (a : integralRelativeCohomology n (A : Set X)ᶜ)
    (b : integralRelativeCohomology n (B : Set X)ᶜ) :
    integralRelativeToCompactlySupportedCohomologyOn n W A hA a +
        integralRelativeToCompactlySupportedCohomologyOn n W B hB b =
      integralRelativeToCompactlySupportedCohomologyOn n W (A ⊔ B) (union_subset hA hB)
        (MayerVietoris.relativeSupportMap n A (A ⊔ B) le_sup_left a +
          MayerVietoris.relativeSupportMap n B (A ⊔ B) le_sup_right b) := by
  rw [map_add]
  exact congrArg₂ (· + ·)
    (integralRelativeToCompactlySupportedCohomologyOn_mono n W A (A ⊔ B) le_sup_left
      hA (union_subset hA hB) a).symm
    (integralRelativeToCompactlySupportedCohomologyOn_mono n W B (A ⊔ B) le_sup_right
      hB (union_subset hA hB) b).symm

private theorem exists_compact_support_pair_in_union (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (K : Compacts X) (hKU : (K : Set X) ⊆ U ∪ V) :
    ∃ (A B : Compacts X), (A : Set X) ⊆ U ∧ (B : Set X) ⊆ V ∧ K ≤ A ⊔ B := by
  obtain ⟨A, B, hA, hB, hAU, hBV, hK⟩ := K.isCompact.binary_compact_cover hU hV hKU
  exact ⟨⟨A, hA⟩, ⟨B, hB⟩, hAU, hBV, by change (K : Set X) ⊆ A ∪ B; rw [hK]⟩

private theorem compact_support_inclusion_sum_zero_on_union (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (γ : integralCompactlySupportedCohomology n ↥(U ∩ V)) :
    integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
          (hU.preimage continuous_subtype_val))
        (integralCompactlySupportedCohomologyPushforward n
          (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
          (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
            ((hU.inter hV).preimage continuous_subtype_val)) γ) +
      integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
          (hV.preimage continuous_subtype_val))
        (-integralCompactlySupportedCohomologyPushforward n
          (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
          (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
            ((hU.inter hV).preimage continuous_subtype_val)) γ) = 0 := by
  obtain ⟨K, hK, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n
    (U ∩ V) (hU.inter hV) γ
  have hleft := integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U ∩ V) U
    inter_subset_left ((hU.inter hV).preimage continuous_subtype_val) K hK α
  have hright := integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U ∩ V) V
    inter_subset_right ((hU.inter hV).preimage continuous_subtype_val) K hK α
  rw [hleft, hright, map_neg,
    integralRelativeToCompactlySupportedCohomologyOn_inclusion n U (U ∪ V) subset_union_left
      (hU.preimage continuous_subtype_val) K
      (hK.trans inter_subset_left) α,
    integralRelativeToCompactlySupportedCohomologyOn_inclusion n V (U ∪ V) subset_union_right
      (hV.preimage continuous_subtype_val) K
      (hK.trans inter_subset_right) α, add_neg_cancel]


end DifferentialGeometry.Topology

end

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

def MayerVietoris.unionIntersectionHomeomorph (U V : Set X) :
    ↥((Subtype.val : ↥(U ∪ V) → X) ⁻¹' U ∩
      (Subtype.val : ↥(U ∪ V) → X) ⁻¹' V) ≃ₜ ↥(U ∩ V) :=
  _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (show U ∩ V ⊆ Set.range (Subtype.val : ↥(U ∪ V) → X) from by
      rw [Subtype.range_coe]
      exact inter_subset_left.trans subset_union_left)

def integralCompactlySupportedMayerVietorisConnecting
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    integralCompactlySupportedCohomology n ↥(U ∪ V) →ₗ[ℤ]
      integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V) :=
  (integralCompactlySupportedCohomologyPushforward (n + 1)
      (↑(MayerVietoris.unionIntersectionHomeomorph U V) : C(_, _))
      (MayerVietoris.unionIntersectionHomeomorph U V).isOpenEmbedding).comp
    (MayerVietoris.compactSupportCoverConnecting n
      ((Subtype.val : ↥(U ∪ V) → X) ⁻¹' U)
      ((Subtype.val : ↥(U ∪ V) → X) ⁻¹' V)
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      (by ext x; exact iff_of_true x.property (mem_univ x)))

private def compactPreimage (W : Set X) (K : Compacts X) (hKW : (K : Set X) ⊆ W) : Compacts W :=
  ⟨Subtype.val ⁻¹' (K : Set X),
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' K.isCompact
      (by simpa only [Subtype.range_coe] using hKW)⟩

private theorem compact_support_preimage_pushforward
    (n : ℕ) (W S : Set X) (hSW : S ⊆ W) (K : Compacts X) (hKS : (K : Set X) ⊆ S)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    let KW := compactPreimage W K (hKS.trans hSW)
    let S' := (Subtype.val : W → X) ⁻¹' S
    let e : S' ≃ₜ S := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe] using hSW)
    integralCompactlySupportedCohomologyPushforward n (↑e : C(_, _)) e.isOpenEmbedding
      (integralRelativeToCompactlySupportedCohomologyOn n S' KW
        (fun _ hx => hKS hx)
        (integralRelativeCohomologyMap n (singularSubspaceInclusion W)
          (show MapsTo (singularSubspaceInclusion W) (KW : Set W)ᶜ (K : Set X)ᶜ from
            fun _ hx => hx) α)) =
    integralRelativeToCompactlySupportedCohomologyOn n S K hKS α := by
  dsimp only
  let KW := compactPreimage W K (hKS.trans hSW)
  let S' := (Subtype.val : W → X) ⁻¹' S
  let e : S' ≃ₜ S := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by simpa only [Subtype.range_coe] using hSW)
  let KN : Compacts S' := compactPreimage S' KW (fun _ hx => hKS hx)
  let KT : Compacts S := compactPreimage S K hKS
  let i := singularSubspaceInclusion W
  let j := singularSubspaceInclusion S'
  let k := singularSubspaceInclusion S
  let hi : MapsTo i (KW : Set W)ᶜ (K : Set X)ᶜ := fun _ hx => hx
  let hj : MapsTo j (KN : Set S')ᶜ (KW : Set W)ᶜ := fun _ hx => hx
  let hk : MapsTo k (KT : Set S)ᶜ (K : Set X)ᶜ := fun _ hx => hx
  let he : MapsTo (↑e : C(S', S)) (KN : Set S')ᶜ (KT : Set S)ᶜ := fun _ hx => hx
  have hcomp₁ := integralRelativeCohomologyMap_comp n j i hj hi
  have hcomp₂ := integralRelativeCohomologyMap_comp n (↑e : C(S', S)) k he hk
  have hcomp : integralRelativeCohomologyMap n j hj
      (integralRelativeCohomologyMap n i hi α) =
    integralRelativeCohomologyMap n (↑e : C(S', S)) he
      (integralRelativeCohomologyMap n k hk α) := by
    exact LinearMap.congr_fun (hcomp₁.symm.trans hcomp₂) α
  change integralCompactlySupportedCohomologyPushforward n (↑e : C(S', S)) e.isOpenEmbedding
    (integralRelativeToCompactlySupportedCohomology n KN
      (integralRelativeCohomologyMap n j hj (integralRelativeCohomologyMap n i hi α))) =
    integralRelativeToCompactlySupportedCohomology n KT (integralRelativeCohomologyMap n k hk α)
  rw [hcomp]
  have hmap : KN.map (↑e : C(S', S)) (↑e : C(S', S)).continuous = KT := by
    apply SetLike.coe_injective
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change (e.symm x).val.val ∈ (K : Set X)
      have hv : (e.symm x).val.val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
      rw [hv]
      exact hx
  have aux (L : Compacts S) (hL : KN.map (↑e : C(S', S)) (↑e : C(S', S)).continuous = L)
      (hρ : MapsTo (↑e : C(S', S)) (KN : Set S')ᶜ (L : Set S)ᶜ)
      (γ : integralRelativeCohomology n (L : Set S)ᶜ) :
      integralCompactlySupportedCohomologyPushforward n (↑e : C(S', S)) e.isOpenEmbedding
          (integralRelativeToCompactlySupportedCohomology n KN
            (integralRelativeCohomologyMap n (↑e : C(S', S)) hρ γ)) =
        integralRelativeToCompactlySupportedCohomology n L γ := by
    subst L
    exact integralCompactlySupportedCohomologyPushforward_relative n
      (↑e : C(S', S)) e.isOpenEmbedding KN γ
  exact aux KT hmap he _

private theorem compact_preimage_connecting_map
    (n : ℕ) (W : Set X) (A B : Compacts X)
    (hA : (A : Set X) ⊆ W) (hB : (B : Set X) ⊆ W)
    (α : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ) :
    let AW := compactPreimage W A hA
    let BW := compactPreimage W B hB
    integralCohomologyWithSupportMayerVietorisConnecting n (AW : Set W) (BW : Set W)
        AW.isCompact.isClosed BW.isCompact.isClosed
        (integralRelativeCohomologyMap n (singularSubspaceInclusion W)
          (show MapsTo (singularSubspaceInclusion W)
              ((AW ⊔ BW : Compacts W) : Set W)ᶜ ((A ⊔ B : Compacts X) : Set X)ᶜ from
            fun _ hx => hx) α) =
      integralRelativeCohomologyMap (n + 1) (singularSubspaceInclusion W)
        (show MapsTo (singularSubspaceInclusion W)
            ((AW ⊓ BW : Compacts W) : Set W)ᶜ ((A ⊓ B : Compacts X) : Set X)ᶜ from
          fun _ hx => hx)
        (integralCohomologyWithSupportMayerVietorisConnecting n (A : Set X) (B : Set X)
          A.isCompact.isClosed B.isCompact.isClosed α) := by
  dsimp only
  exact (LinearMap.congr_fun
    (integralCohomologyWithSupportMayerVietorisConnecting_map n (singularSubspaceInclusion W)
      (compactPreimage W A hA : Set W) (compactPreimage W B hB : Set W)
      (A : Set X) (B : Set X)
      (compactPreimage W A hA).isCompact.isClosed (compactPreimage W B hB).isCompact.isClosed
      A.isCompact.isClosed B.isCompact.isClosed (fun _ hx => hx) (fun _ hx => hx)) α).symm

theorem integralCompactlySupportedMayerVietorisConnecting_representative
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A B : Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
    (α : integralRelativeCohomology n ((A ⊔ B : Compacts X) : Set X)ᶜ) :
    integralCompactlySupportedMayerVietorisConnecting n U V hU hV
        (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
          (union_subset_union hA hB) α) =
      integralRelativeToCompactlySupportedCohomologyOn (n + 1) (U ∩ V) (A ⊓ B)
        (fun _ hx => ⟨hA hx.1, hB hx.2⟩)
        (integralCohomologyWithSupportMayerVietorisConnecting n (A : Set X) (B : Set X)
          A.isCompact.isClosed B.isCompact.isClosed α) := by
  let W := ↥(U ∪ V)
  let i := singularSubspaceInclusion (U ∪ V)
  let UW : Set W := i ⁻¹' U
  let VW : Set W := i ⁻¹' V
  let AW := compactPreimage (U ∪ V) A (hA.trans subset_union_left)
  let BW := compactPreimage (U ∪ V) B (hB.trans subset_union_right)
  let hAW : (AW : Set W) ⊆ UW := fun _ hx => hA hx
  let hBW : (BW : Set W) ⊆ VW := fun _ hx => hB hx
  let hα : MapsTo i ((AW ⊔ BW : Compacts W) : Set W)ᶜ ((A ⊔ B : Compacts X) : Set X)ᶜ :=
    fun _ hx => hx
  let αW := integralRelativeCohomologyMap n i hα α
  let hUW : IsOpen UW := hU.preimage i.continuous
  let hVW : IsOpen VW := hV.preimage i.continuous
  let hW : UW ∪ VW = univ := by ext x; exact iff_of_true x.property (mem_univ x)
  let e := MayerVietoris.unionIntersectionHomeomorph U V
  have hrep : integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (union_subset_union hA hB) α =
      integralRelativeToCompactlySupportedCohomology n (AW ⊔ BW) αW := rfl
  rw [hrep]
  unfold integralCompactlySupportedMayerVietorisConnecting
  simp only [LinearMap.comp_apply]
  have hcover := compactSupportCoverConnecting_representative
    n UW VW hUW hVW hW AW BW hAW hBW αW
  erw [hcover]
  let β := integralCohomologyWithSupportMayerVietorisConnecting n (A : Set X) (B : Set X)
    A.isCompact.isClosed B.isCompact.isClosed α
  have hnat := compact_preimage_connecting_map n (U ∪ V) A B
    (hA.trans subset_union_left) (hB.trans subset_union_right) α
  erw [hnat]
  exact compact_support_preimage_pushforward (n + 1) (U ∪ V) (U ∩ V)
    (inter_subset_left.trans subset_union_left) (A ⊓ B)
    (fun _ hx => ⟨hA hx.1, hB hx.2⟩) β

end DifferentialGeometry.Topology

end

noncomputable section
open Set TopologicalSpace
universe u
namespace DifferentialGeometry.Topology
variable {X : Type u} [TopologicalSpace X] [T2Space X]

theorem integralCompactlySupportedCohomology_mayerVietoris_exact_middle
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (a : integralCompactlySupportedCohomology n U)
    (b : integralCompactlySupportedCohomology n V) :
    integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
          (hU.preimage continuous_subtype_val)) a +
      integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
          (hV.preimage continuous_subtype_val)) b = 0 ↔
    ∃ γ : integralCompactlySupportedCohomology n ↥(U ∩ V),
      integralCompactlySupportedCohomologyPushforward n
          (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
          (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
            ((hU.inter hV).preimage continuous_subtype_val)) γ = a ∧
      -integralCompactlySupportedCohomologyPushforward n
          (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
          (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
            ((hU.inter hV).preimage continuous_subtype_val)) γ = b := by
  constructor
  · intro hab
    obtain ⟨A, hA, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n U hU a
    obtain ⟨B, hB, β, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n V hV b
    rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n U (U ∪ V) subset_union_left
      (hU.preimage continuous_subtype_val) A hA α,
      integralRelativeToCompactlySupportedCohomologyOn_inclusion n V (U ∪ V) subset_union_right
      (hV.preimage continuous_subtype_val) B hB β,
      support_pair_sum_representative_on] at hab
    obtain ⟨L, hLUV, hABL, hzero⟩ :=
      (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff n (U ∪ V)
        (hU.union hV) (A ⊔ B) _ _).1 hab
    obtain ⟨E, F, hE, hF, hL⟩ := exists_compact_support_pair_in_union U V hU hV L hLUV
    let C := A ⊔ E
    let D := B ⊔ F
    have hAC : A ≤ C := le_sup_left
    have hBD : B ≤ D := le_sup_left
    have hC : (C : Set X) ⊆ U := union_subset hA hE
    have hD : (D : Set X) ⊆ V := union_subset hB hF
    have hLCD : L ≤ C ⊔ D := hL.trans (sup_le_sup le_sup_right le_sup_right)
    have hmap_comp (P Q R : Compacts X) (hPQ : P ≤ Q) (hQR : Q ≤ R)
        (ξ : integralRelativeCohomology n (P : Set X)ᶜ) :
        MayerVietoris.relativeSupportMap n Q R hQR (MayerVietoris.relativeSupportMap n P Q hPQ ξ) =
          MayerVietoris.relativeSupportMap n P R (hPQ.trans hQR) ξ :=
      LinearMap.congr_fun (MayerVietoris.relativeSupportMap_comp n P Q R hPQ hQR) ξ
    have hs : MayerVietoris.relativeSupportMap n C (C ⊔ D) le_sup_left (MayerVietoris.relativeSupportMap n A C hAC α) +
        MayerVietoris.relativeSupportMap n D (C ⊔ D) le_sup_right (MayerVietoris.relativeSupportMap n B D hBD β) = 0 := by
      have hz := congrArg (MayerVietoris.relativeSupportMap n L (C ⊔ D) hLCD) hzero
      change MayerVietoris.relativeSupportMap n L (C ⊔ D) hLCD
        (MayerVietoris.relativeSupportMap n (A ⊔ B) L hABL _) = _ at hz
      simpa only [map_add, hmap_comp, map_zero] using hz
    obtain ⟨γ, hγC, hγD⟩ :=
      (integralCohomologyWithSupport_mayerVietoris_middle_exact n (C : Set X) (D : Set X)
        C.isCompact.isClosed D.isCompact.isClosed
        (MayerVietoris.relativeSupportMap n A C hAC α) (MayerVietoris.relativeSupportMap n B D hBD β)).1 hs
    refine ⟨integralRelativeToCompactlySupportedCohomologyOn n (U ∩ V) (C ⊓ D)
      (fun _ hx => ⟨hC hx.1, hD hx.2⟩) γ, ?_, ?_⟩
    · erw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U ∩ V) U
        inter_subset_left ((hU.inter hV).preimage continuous_subtype_val)]
      rw [← integralRelativeToCompactlySupportedCohomologyOn_mono n U (C ⊓ D) C
        inf_le_left _ hC, hγC]
      exact integralRelativeToCompactlySupportedCohomologyOn_mono n U A C hAC hA hC α
    · erw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U ∩ V) V
        inter_subset_right ((hU.inter hV).preimage continuous_subtype_val)]
      rw [← integralRelativeToCompactlySupportedCohomologyOn_mono n V (C ⊓ D) D
        inf_le_right _ hD, ← map_neg, hγD]
      exact integralRelativeToCompactlySupportedCohomologyOn_mono n V B D hBD hB hD β
  · rintro ⟨γ, hγU, hγV⟩
    rw [← hγU, ← hγV]
    exact compact_support_inclusion_sum_zero_on_union n U V hU hV γ

theorem integralCompactlySupportedCohomology_mayerVietoris_exact_union
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (x : integralCompactlySupportedCohomology n ↥(U ∪ V)) :
    integralCompactlySupportedMayerVietorisConnecting n U V hU hV x = 0 ↔
      ∃ a : integralCompactlySupportedCohomology n U,
        ∃ b : integralCompactlySupportedCohomology n V,
          integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
              (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
                (hU.preimage continuous_subtype_val)) a +
            integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
              (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
                (hV.preimage continuous_subtype_val)) b = x := by
  constructor
  · intro hx
    obtain ⟨K, hKUV, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n
      (U ∪ V) (hU.union hV) x
    obtain ⟨A, B, hA, hB, hK⟩ := exists_compact_support_pair_in_union U V hU hV K hKUV
    let α' := MayerVietoris.relativeSupportMap n K (A ⊔ B) hK α
    have hre : integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (union_subset_union hA hB) α' =
        integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) K hKUV α :=
      integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) K (A ⊔ B) hK
        hKUV (union_subset_union hA hB) α
    rw [← hre, integralCompactlySupportedMayerVietorisConnecting_representative
      n U V hU hV A B hA hB α'] at hx
    obtain ⟨C, D, hAC, hBD, hC, hD, hzero⟩ :=
      (supportPairConnecting_eq_zero_iff n U V hU hV A B hA hB α').1 hx
    obtain ⟨a, b, hab⟩ :=
      (integralCohomologyWithSupport_mayerVietoris_exact_union n (C : Set X) (D : Set X)
        C.isCompact.isClosed D.isCompact.isClosed _).1 hzero
    refine ⟨integralRelativeToCompactlySupportedCohomologyOn n U C hC a,
      integralRelativeToCompactlySupportedCohomologyOn n V D hD b, ?_⟩
    rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n U (U ∪ V) subset_union_left
      (hU.preimage continuous_subtype_val) C hC a,
      integralRelativeToCompactlySupportedCohomologyOn_inclusion n V (U ∪ V) subset_union_right
      (hV.preimage continuous_subtype_val) D hD b,
      support_pair_sum_representative_on]
    exact (congrArg (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (C ⊔ D)
      (union_subset_union hC hD)) hab).trans
      ((integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) (A ⊔ B) (C ⊔ D)
        (sup_le_sup hAC hBD) (union_subset_union hA hB) (union_subset_union hC hD) α').trans hre)
  · rintro ⟨a, b, rfl⟩
    obtain ⟨A, hA, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n U hU a
    obtain ⟨B, hB, β, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n V hV b
    rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n U (U ∪ V) subset_union_left
      (hU.preimage continuous_subtype_val) A hA α,
      integralRelativeToCompactlySupportedCohomologyOn_inclusion n V (U ∪ V) subset_union_right
      (hV.preimage continuous_subtype_val) B hB β,
      support_pair_sum_representative_on,
      integralCompactlySupportedMayerVietorisConnecting_representative n U V hU hV A B hA hB]
    have hzero := (integralCohomologyWithSupport_mayerVietoris_exact_union n (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed _).2 ⟨α, β, rfl⟩
    simp only [MayerVietoris.relativeSupportMap]
    rw [hzero, map_zero]

theorem integralCompactlySupportedCohomology_mayerVietoris_exact_inter
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (x : integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V)) :
    (integralCompactlySupportedCohomologyPushforward (n + 1)
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
          ((hU.inter hV).preimage continuous_subtype_val)) x = 0 ∧
      integralCompactlySupportedCohomologyPushforward (n + 1)
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
          ((hU.inter hV).preimage continuous_subtype_val)) x = 0) ↔
      ∃ y : integralCompactlySupportedCohomology n ↥(U ∪ V),
        integralCompactlySupportedMayerVietorisConnecting n U V hU hV y = x := by
  constructor
  · rintro ⟨hxU, hxV⟩
    obtain ⟨K, hK, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative
      (n + 1) (U ∩ V) (hU.inter hV) x
    rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion (n + 1) (U ∩ V) U
      inter_subset_left ((hU.inter hV).preimage continuous_subtype_val)] at hxU
    rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion (n + 1) (U ∩ V) V
      inter_subset_right ((hU.inter hV).preimage continuous_subtype_val)] at hxV
    obtain ⟨A, hA, hKA, hαA⟩ :=
      (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff (n + 1) U hU K
        (hK.trans inter_subset_left) α).1 hxU
    obtain ⟨B, hB, hKB, hαB⟩ :=
      (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff (n + 1) V hV K
        (hK.trans inter_subset_right) α).1 hxV
    let β := MayerVietoris.relativeSupportMap (n + 1) K (A ⊓ B) (le_inf hKA hKB) α
    have hβA : MayerVietoris.relativeSupportMap (n + 1) (A ⊓ B) A inf_le_left β = 0 :=
      (LinearMap.congr_fun (MayerVietoris.relativeSupportMap_comp (n + 1) K (A ⊓ B) A
        (le_inf hKA hKB) inf_le_left) α).trans hαA
    have hβB : MayerVietoris.relativeSupportMap (n + 1) (A ⊓ B) B inf_le_right β = 0 :=
      (LinearMap.congr_fun (MayerVietoris.relativeSupportMap_comp (n + 1) K (A ⊓ B) B
        (le_inf hKA hKB) inf_le_right) α).trans hαB
    obtain ⟨γ, hγ⟩ :=
      (integralCohomologyWithSupport_mayerVietoris_exact_inter n (A : Set X) (B : Set X)
        A.isCompact.isClosed B.isCompact.isClosed β).1 ⟨hβA, hβB⟩
    refine ⟨integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
      (union_subset_union hA hB) γ, ?_⟩
    rw [integralCompactlySupportedMayerVietorisConnecting_representative
      n U V hU hV A B hA hB, hγ]
    exact integralRelativeToCompactlySupportedCohomologyOn_mono (n + 1) (U ∩ V)
      K (A ⊓ B) (le_inf hKA hKB) hK _ α
  · rintro ⟨y, rfl⟩
    obtain ⟨K, hKUV, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n
      (U ∪ V) (hU.union hV) y
    obtain ⟨A, B, hA, hB, hK⟩ := exists_compact_support_pair_in_union U V hU hV K hKUV
    rw [← integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) K (A ⊔ B) hK
        hKUV (union_subset_union hA hB) α,
      integralCompactlySupportedMayerVietorisConnecting_representative
        n U V hU hV A B hA hB]
    have hzero := (integralCohomologyWithSupport_mayerVietoris_exact_inter n
      (A : Set X) (B : Set X) A.isCompact.isClosed B.isCompact.isClosed _).2
      ⟨MayerVietoris.relativeSupportMap n K (A ⊔ B) hK α, rfl⟩
    constructor
    · erw [integralRelativeToCompactlySupportedCohomologyOn_inclusion (n + 1) (U ∩ V) U
        inter_subset_left ((hU.inter hV).preimage continuous_subtype_val)]
      erw [← integralRelativeToCompactlySupportedCohomologyOn_mono (n + 1) U
        (A ⊓ B) A inf_le_left _ hA, hzero.1, map_zero]
    · erw [integralRelativeToCompactlySupportedCohomologyOn_inclusion (n + 1) (U ∩ V) V
        inter_subset_right ((hU.inter hV).preimage continuous_subtype_val)]
      erw [← integralRelativeToCompactlySupportedCohomologyOn_mono (n + 1) V
        (A ⊓ B) B inf_le_right _ hB, hzero.2, map_zero]

private abbrev intersectionPushforward (n : ℕ) (U V U' V' : Set X)
    (hUU' : U ⊆ U') (hVV' : V ⊆ V') (hU : IsOpen U) (hV : IsOpen V) :=
  integralCompactlySupportedCohomologyPushforward (n + 1)
    (ContinuousMap.inclusion (inter_subset_inter hUU' hVV'))
    (_root_.Topology.IsOpenEmbedding.inclusion (inter_subset_inter hUU' hVV')
      ((hU.inter hV).preimage continuous_subtype_val))

private abbrev unionPushforward (n : ℕ) (U V U' V' : Set X)
    (hUU' : U ⊆ U') (hVV' : V ⊆ V') (hU : IsOpen U) (hV : IsOpen V) :=
  integralCompactlySupportedCohomologyPushforward n
    (ContinuousMap.inclusion (union_subset_union hUU' hVV'))
    (_root_.Topology.IsOpenEmbedding.inclusion (union_subset_union hUU' hVV')
      ((hU.union hV).preimage continuous_subtype_val))

private theorem connecting_natural_representative
    (n : ℕ) (U V U' V' : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hU' : IsOpen U') (hV' : IsOpen V') (hUU' : U ⊆ U') (hVV' : V ⊆ V')
    (C D : Compacts X) (hC : (C : Set X) ⊆ U) (hD : (D : Set X) ⊆ V)
    (β : integralRelativeCohomology n ((C ⊔ D : Compacts X) : Set X)ᶜ) :
    intersectionPushforward n U V U' V' hUU' hVV' hU hV
      (integralCompactlySupportedMayerVietorisConnecting n U V hU hV
        (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (C ⊔ D)
          (union_subset_union hC hD) β)) =
      integralCompactlySupportedMayerVietorisConnecting n U' V' hU' hV'
        (unionPushforward n U V U' V' hUU' hVV' hU hV
          (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (C ⊔ D)
            (union_subset_union hC hD) β)) := by
  rw [integralCompactlySupportedMayerVietorisConnecting_representative n U V hU hV C D hC hD]
  have htarget := integralRelativeToCompactlySupportedCohomologyOn_inclusion (n + 1)
    (U ∩ V) (U' ∩ V') (inter_subset_inter hUU' hVV')
    ((hU.inter hV).preimage continuous_subtype_val) (C ⊓ D)
    (fun _ hx => ⟨hC hx.1, hD hx.2⟩)
    (integralCohomologyWithSupportMayerVietorisConnecting n (C : Set X) (D : Set X)
      C.isCompact.isClosed D.isCompact.isClosed β)
  erw [htarget]
  have hsource := integralRelativeToCompactlySupportedCohomologyOn_inclusion n
    (U ∪ V) (U' ∪ V') (union_subset_union hUU' hVV')
    ((hU.union hV).preimage continuous_subtype_val) (C ⊔ D) (union_subset_union hC hD) β
  erw [hsource]
  exact (integralCompactlySupportedMayerVietorisConnecting_representative n U' V' hU' hV'
    C D (hC.trans hUU') (hD.trans hVV') β).symm

theorem integralCompactlySupportedMayerVietorisConnecting_natural
    (n : ℕ) (U V U' V' : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hU' : IsOpen U') (hV' : IsOpen V') (hUU' : U ⊆ U') (hVV' : V ⊆ V') :
    (integralCompactlySupportedCohomologyPushforward (n + 1)
      (ContinuousMap.inclusion (inter_subset_inter hUU' hVV'))
      (_root_.Topology.IsOpenEmbedding.inclusion (inter_subset_inter hUU' hVV')
        ((hU.inter hV).preimage continuous_subtype_val))).comp
      (integralCompactlySupportedMayerVietorisConnecting n U V hU hV) =
      (integralCompactlySupportedMayerVietorisConnecting n U' V' hU' hV').comp
        (integralCompactlySupportedCohomologyPushforward n
          (ContinuousMap.inclusion (union_subset_union hUU' hVV'))
          (_root_.Topology.IsOpenEmbedding.inclusion (union_subset_union hUU' hVV')
            ((hU.union hV).preimage continuous_subtype_val))) := by
  ext x
  obtain ⟨K, hK, α, rfl⟩ := integralCompactlySupportedCohomologyOn_exists_representative n
    (U ∪ V) (hU.union hV) x
  obtain ⟨A, B, hAc, hBc, hA, hB, hAB⟩ := K.isCompact.binary_compact_cover hU hV hK
  let C : Compacts X := ⟨A, hAc⟩
  let D : Compacts X := ⟨B, hBc⟩
  have hKCD : K ≤ C ⊔ D := by change (K : Set X) ⊆ A ∪ B; rw [hAB]
  let β := integralRelativeCohomologyMap n (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) ((C ⊔ D : Compacts X) : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr hKCD) α
  have hre : integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (C ⊔ D)
      (union_subset_union hA hB) β =
      integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) K hK α :=
    integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) K (C ⊔ D)
      hKCD hK (union_subset_union hA hB) α
  rw [← hre]
  exact connecting_natural_representative n U V U' V' hU hV hU' hV' hUU' hVV' C D hA hB β


end DifferentialGeometry.Topology
end
