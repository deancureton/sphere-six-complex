module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.CapNaturality
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapMayerVietoris
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Homeomorph
public import DifferentialGeometry.Topology.Homology.MayerVietorisExactness
public import DifferentialGeometry.Topology.Homology.CompactHomologyFamilyNaturality
public import Mathlib.Algebra.FiveLemma

@[expose] public section

noncomputable section

open CategoryTheory Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

@[reducible] local instance integerProdModule (P Q : Type*)
    [AddCommGroup P] [AddCommGroup Q] [Module ℤ P] [Module ℤ Q] :
    Module ℤ (P × Q) := Prod.instModule

local instance CapGluing.integerSmulComm (P : Type*) [AddCommGroup P]
    [h : Module ℤ P] : @SMulCommClass ℤ ℤ P h.toSMul h.toSMul :=
  @smulCommClass_self ℤ P inferInstance h.toMulAction

@[reducible] local instance integerLinearModule (P Q : Type*)
    [AddCommGroup P] [AddCommGroup Q] [Module ℤ P] [Module ℤ Q] :
    Module ℤ (P →ₗ[ℤ] Q) := LinearMap.module

private theorem prescribed_cap_natural
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    (k m : ℕ) (f : C(Y, Z)) (hf : _root_.Topology.IsOpenEmbedding f)
    (cY : ∀ K : Compacts Y, integralRelativeHomology (k + m) (K : Set Y)ᶜ)
    (cZ : ∀ K : Compacts Z, integralRelativeHomology (k + m) (K : Set Z)ᶜ)
    (hY : ∀ (K L : Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id Y)
        (show (L : Set Y)ᶜ ⊆ (K : Set Y)ᶜ from compl_subset_compl.mpr h) (cY L) = cY K)
    (hZ : ∀ (K L : Compacts Z) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id Z)
        (show (L : Set Z)ᶜ ⊆ (K : Set Z)ᶜ from compl_subset_compl.mpr h) (cZ L) = cZ K)
    (hc : ∀ K : Compacts Y,
      integralRelativeHomologyMap (k + m) f
        (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) (cY K) =
          cZ (K.map f f.continuous))
    (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y)
    (DZ : integralCompactlySupportedCohomology k Z →ₗ[ℤ] integralSingularHomology m Z)
    (hDY : ∀ (K : Compacts Y) (α : integralRelativeCohomology k (K : Set Y)ᶜ),
      DY (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set Y)ᶜ k m α (cY K))
    (hDZ : ∀ (K : Compacts Z) (α : integralRelativeCohomology k (K : Set Z)ᶜ),
      DZ (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set Z)ᶜ k m α (cZ K)) :
    (integralSingularHomologyMap m f).comp DY =
      DZ.comp (integralCompactlySupportedCohomologyPushforward k f hf) := by
  obtain ⟨DY', DZ', hDY', hDZ', hn⟩ :=
    exists_integralCompactlySupportedCohomology_cap_natural k m f hf cY cZ hY hZ hc
  have hy : DY = DY' := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hDY K α).trans (hDY' K α).symm)
  have hz : DZ = DZ' := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hDZ K α).trans (hDZ' K α).symm)
  rwa [hy, hz]

private theorem relative_homology_map_cast
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {a b : ℕ} (h : a = b) (f : C(Y, Z)) {A : Set Y} {B : Set Z}
    (hf : MapsTo f A B) (c : integralRelativeHomology a A) :
    integralRelativeHomologyMap b f hf
      ((eqToHom (congrArg (fun n => integralRelativeHomology n A) h)) c) =
      (eqToHom (congrArg (fun n => integralRelativeHomology n B) h))
        (integralRelativeHomologyMap a f hf c) := by
  subst b
  rfl

private theorem compact_homology_family_coherent_of_map
    {Y X : Type u} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
    (n : ℕ) (f : ContinuousMap Y X) (hf : _root_.Topology.IsOpenEmbedding f)
    (cY : ∀ K : Compacts Y, integralRelativeHomology n (K : Set Y)ᶜ)
    (cX : ∀ K : Compacts X, integralRelativeHomology n (K : Set X)ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hc : ∀ K : Compacts Y,
      integralRelativeHomologyMap n f
        (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)) (cY K) =
          cX (K.map f f.continuous)) :
    ∀ (K L : Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap n (ContinuousMap.id Y)
        (show (L : Set Y)ᶜ ⊆ (K : Set Y)ᶜ from compl_subset_compl.mpr h) (cY L) = cY K := by
  intro K L h
  let hK : MapsTo f (K : Set Y)ᶜ (K.map f f.continuous : Set X)ᶜ :=
    mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)
  let hL : MapsTo f (L : Set Y)ᶜ (L.map f f.continuous : Set X)ᶜ :=
    mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective)
  let hY : MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ :=
    compl_subset_compl.mpr h
  have hmap : K.map f f.continuous ≤ L.map f f.continuous := image_mono h
  let hXmap : MapsTo (ContinuousMap.id X)
      (L.map f f.continuous : Set X)ᶜ (K.map f f.continuous : Set X)ᶜ :=
    compl_subset_compl.mpr hmap
  apply (integralRelativeHomologyMap_bijective_of_isOpenEmbedding n f hf K).injective
  calc
    integralRelativeHomologyMap n f hK
        (integralRelativeHomologyMap n (ContinuousMap.id Y) hY (cY L)) =
      integralRelativeHomologyMap n f (hK.comp hY) (cY L) :=
        (LinearMap.congr_fun
          (integralRelativeHomologyMap_comp n (ContinuousMap.id Y) f hY hK) (cY L)).symm
    _ = integralRelativeHomologyMap n (ContinuousMap.id X) hXmap
        (integralRelativeHomologyMap n f hL (cY L)) :=
      LinearMap.congr_fun
        (integralRelativeHomologyMap_comp n f (ContinuousMap.id X) hL hXmap) (cY L)
    _ = cX (K.map f f.continuous) :=
      (congrArg (integralRelativeHomologyMap n (ContinuousMap.id X) hXmap) (hc L)).trans
        (hX _ _ hmap)
    _ = integralRelativeHomologyMap n f hK (cY K) := (hc K).symm


variable {X : Type} [TopologicalSpace X] [T2Space X]

private def compactMayerVietorisDifference (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    integralCompactlySupportedCohomology n ↥(U ∩ V) →ₗ[ℤ]
      (integralCompactlySupportedCohomology n U × integralCompactlySupportedCohomology n V) :=
  (integralCompactlySupportedCohomologyPushforward n
    (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
    (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
      ((hU.inter hV).preimage continuous_subtype_val))).prod
  (-(integralCompactlySupportedCohomologyPushforward n
    (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
    (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
      ((hU.inter hV).preimage continuous_subtype_val))))

private def compactMayerVietorisSum (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    (integralCompactlySupportedCohomology n U × integralCompactlySupportedCohomology n V) →ₗ[ℤ]
      integralCompactlySupportedCohomology n ↥(U ∪ V) :=
  (integralCompactlySupportedCohomologyPushforward n
    (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
    (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
      (hU.preimage continuous_subtype_val))).coprod
  (integralCompactlySupportedCohomologyPushforward n
    (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
    (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
      (hV.preimage continuous_subtype_val)))

private theorem compact_mayerVietoris_exact_sum (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    Function.Exact (compactMayerVietorisDifference n U V hU hV)
      (compactMayerVietorisSum n U V hU hV) := by
  rintro ⟨a, b⟩
  simpa only [compactMayerVietorisDifference, compactMayerVietorisSum,
    LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod_apply, LinearMap.neg_apply,
    Set.mem_range, Prod.mk.injEq] using
    integralCompactlySupportedCohomology_mayerVietoris_exact_middle n U V hU hV a b

private theorem compact_mayerVietoris_exact_connecting (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    Function.Exact (compactMayerVietorisSum n U V hU hV)
      (integralCompactlySupportedMayerVietorisConnecting n U V hU hV) := by
  intro x
  simpa only [compactMayerVietorisSum, LinearMap.coprod_apply, Set.mem_range,
    Prod.exists] using
    integralCompactlySupportedCohomology_mayerVietoris_exact_union n U V hU hV x

private theorem compact_mayerVietoris_exact_difference (n : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    Function.Exact (integralCompactlySupportedMayerVietorisConnecting n U V hU hV)
      (compactMayerVietorisDifference (n + 1) U V hU hV) := by
  intro x
  simpa only [compactMayerVietorisDifference, LinearMap.prod_apply, Function.prod_apply, LinearMap.neg_apply,
    Prod.mk_eq_zero, neg_eq_zero, Set.mem_range] using
    integralCompactlySupportedCohomology_mayerVietoris_exact_inter n U V hU hV x

private theorem compact_union_inclusion_bijective (k : ℕ) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ x : X, x ∈ U ∨ x ∈ V) :
    Function.Bijective (integralCompactlySupportedCohomologyPushforward k
      (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal) := by
  let e : ↥(U ∪ V) ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hcover x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun x => hcover x) }
  exact integralCompactlySupportedCohomologyPushforward_homeomorph_bijective k e

private theorem cap_bijective_of_two_open_diagram
    (k r : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology (r + 1) X)
    (DU : integralCompactlySupportedCohomology k U →ₗ[ℤ] integralSingularHomology (r + 1) U)
    (DV : integralCompactlySupportedCohomology k V →ₗ[ℤ] integralSingularHomology (r + 1) V)
    (DW : integralCompactlySupportedCohomology k ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology (r + 1) ↥(U ∩ V))
    (EU : integralCompactlySupportedCohomology (k + 1) U →ₗ[ℤ] integralSingularHomology r U)
    (EV : integralCompactlySupportedCohomology (k + 1) V →ₗ[ℤ] integralSingularHomology r V)
    (EW : integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology r ↥(U ∩ V))
    (hWU : (integralSingularHomologyMap (r + 1)
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))).comp DW =
      DU.comp (integralCompactlySupportedCohomologyPushforward k
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hWV : (integralSingularHomologyMap (r + 1)
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))).comp DW =
      DV.comp (integralCompactlySupportedCohomologyPushforward k
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hEWU : (integralSingularHomologyMap r
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))).comp EW =
      EU.comp (integralCompactlySupportedCohomologyPushforward (k + 1)
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hEWV : (integralSingularHomologyMap r
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))).comp EW =
      EV.comp (integralCompactlySupportedCohomologyPushforward (k + 1)
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hUX : (integralSingularHomologyMap (r + 1) (singularSubspaceInclusion U)).comp DU =
      DX.comp (integralCompactlySupportedCohomologyPushforward k
        (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal))
    (hVX : (integralSingularHomologyMap (r + 1) (singularSubspaceInclusion V)).comp DV =
      DX.comp (integralCompactlySupportedCohomologyPushforward k
        (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal))
    (hconn : ∀ α : integralCompactlySupportedCohomology k ↥(U ∪ V),
      EW (integralCompactlySupportedMayerVietorisConnecting k U V hU hV α) =
        (-1 : ℤ) ^ (k + 1) •
          Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
            (TopCat.of X) U V hU hV hcover r
            (DX (integralCompactlySupportedCohomologyPushforward k
              (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal α)))
    (hDW : Function.Surjective DW) (hDU : Function.Bijective DU)
    (hDV : Function.Bijective DV) (hEW : Function.Bijective EW)
    (hEU : Function.Injective EU) (hEV : Function.Injective EV) :
    Function.Bijective DX := by
  let f₁ := compactMayerVietorisDifference k U V hU hV
  let f₂ := compactMayerVietorisSum k U V hU hV
  let f₃ := integralCompactlySupportedMayerVietorisConnecting k U V hU hV
  let f₄ := compactMayerVietorisDifference (k + 1) U V hU hV
  let g₁ := Homology.singularMayerVietorisDifferenceMap integralSingularCoefficients
    (TopCat.of X) U V (r + 1)
  let g₂ := Homology.singularMayerVietorisSumMap integralSingularCoefficients
    (TopCat.of X) U V (r + 1)
  let g₃ := (Homology.singularMayerVietorisConnectingMap integralSingularCoefficients
    (TopCat.of X) U V hU hV hcover r).hom
  let g₄ := Homology.singularMayerVietorisDifferenceMap integralSingularCoefficients
    (TopCat.of X) U V r
  let P := integralCompactlySupportedCohomologyPushforward k
    (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal
  let sign := (-1 : ℤ) ^ (k + 1)
  have hsign : sign * sign = 1 := by simp [sign, ← mul_pow]
  have hsign_smul {M : Type} [AddCommGroup M] [Module ℤ M] (x : M) :
      sign • (sign • x) = x := by rw [← mul_smul, hsign, one_smul]
  have hc₁ : g₁.comp DW = (DU.prodMap DV).comp f₁ := by
    ext a
    · exact LinearMap.congr_fun hWU a
    · change -integralSingularHomologyMap (r + 1)
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) (DW a) = DV (-_)
      have h := LinearMap.congr_fun hWV a
      dsimp only [LinearMap.comp_apply] at h
      rw [h, map_neg]
  have hc₂ : g₂.comp (DU.prodMap DV) = (DX.comp P).comp f₂ := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change integralSingularHomologyMap (r + 1) (singularSubspaceInclusion U) (DU a) +
      integralSingularHomologyMap (r + 1) (singularSubspaceInclusion V) (DV b) = _
    have hu := LinearMap.congr_fun hUX a
    have hv := LinearMap.congr_fun hVX b
    dsimp only [LinearMap.comp_apply] at hu hv
    rw [hu, hv]
    change DX _ + DX _ = DX (P (_ + _))
    rw [map_add, map_add]
    congr 1
    · have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp k
        (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
        (singularSubspaceInclusion (U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
          (hU.preimage continuous_subtype_val)) (hU.union hV).isOpenEmbedding_subtypeVal) a
      exact congrArg DX h
    · have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp k
        (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
        (singularSubspaceInclusion (U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
          (hV.preimage continuous_subtype_val)) (hU.union hV).isOpenEmbedding_subtypeVal) b
      exact congrArg DX h
  have hc₃ : g₃.comp (DX.comp P) = (sign • EW).comp f₃ := by
    ext a
    change g₃ (DX (P a)) = sign • EW (f₃ a)
    rw [hconn]
    exact (hsign_smul (g₃ (DX (P a)))).symm
  have hc₄ : g₄.comp (sign • EW) = (sign • (EU.prodMap EV)).comp f₄ := by
    ext a
    · change integralSingularHomologyMap r
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) (sign • EW a) =
          sign • EU _
      have h := LinearMap.congr_fun hEWU a
      dsimp only [LinearMap.comp_apply] at h
      have hm := (integralSingularHomologyMap r
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))).toAddMonoidHom.map_zsmul
          sign (EW a)
      exact hm.trans (congrArg (fun z => sign • z) h)
    · change -integralSingularHomologyMap r
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) (sign • EW a) =
          sign • EV (-_)
      have h := LinearMap.congr_fun hEWV a
      dsimp only [LinearMap.comp_apply] at h
      have hm := (integralSingularHomologyMap r
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))).toAddMonoidHom.map_zsmul
          sign (EW a)
      refine (congrArg Neg.neg hm).trans ((congrArg (fun z => -(sign • z)) h).trans ?_)
      exact (zsmul_neg _ sign).symm.trans
        (congrArg (fun z => sign • z) (map_neg EV _).symm)
  have hsEW : Function.Bijective (sign • EW) := by
    constructor
    · intro a b hab
      apply hEW.injective
      exact (hsign_smul (EW a)).symm.trans
        ((congrArg (fun y => sign • y) hab).trans (hsign_smul (EW b)))
    · intro z
      obtain ⟨a, ha⟩ := hEW.surjective (sign • z)
      refine ⟨a, ?_⟩
      change sign • EW a = z
      rw [ha, hsign_smul]
  have hsEUV : Function.Injective (sign • (EU.prodMap EV)) := by
    intro a b hab
    apply hEU.prodMap hEV
    exact (hsign_smul ((EU.prodMap EV) a)).symm.trans
      ((congrArg (fun y => sign • y) hab).trans (hsign_smul ((EU.prodMap EV) b)))
  have hmid := LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ DW (DU.prodMap DV) (DX.comp P) (sign • EW)
    (sign • (EU.prodMap EV)) hc₁ hc₂ hc₃ hc₄
    (compact_mayerVietoris_exact_sum k U V hU hV)
    (compact_mayerVietoris_exact_connecting k U V hU hV)
    (compact_mayerVietoris_exact_difference k U V hU hV)
    (Homology.singularMayerVietoris_exact_sum integralSingularCoefficients
      (TopCat.of X) U V hU hV hcover (r + 1))
    (Homology.singularMayerVietoris_exact_connecting integralSingularCoefficients
      (TopCat.of X) U V hU hV hcover r)
    (Homology.singularMayerVietoris_exact_difference integralSingularCoefficients
      (TopCat.of X) U V hU hV hcover r)
    hDW (hDU.prodMap hDV) hsEW hsEUV
  have hP := compact_union_inclusion_bijective k U V hU hV hcover
  exact ⟨fun a b hab => by
    obtain ⟨a', rfl⟩ := hP.surjective a
    obtain ⟨b', rfl⟩ := hP.surjective b
    exact congrArg P (hmid.injective hab), fun x => by
      obtain ⟨a, ha⟩ := hmid.surjective x
      exact ⟨P a, ha⟩⟩

theorem integralCompactlySupportedCohomology_cap_bijective_succ_of_two_open_cover
    (k r : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + r + 1) (K : Set X)ᶜ)
    (cU : ∀ K : Compacts U, integralRelativeHomology (k + r + 1) (K : Set U)ᶜ)
    (cV : ∀ K : Compacts V, integralRelativeHomology (k + r + 1) (K : Set V)ᶜ)
    (cW : ∀ K : Compacts ↥(U ∩ V), integralRelativeHomology (k + r + 1) (K : Set ↥(U ∩ V))ᶜ)
    (hXfamily : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + r + 1) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hcUX : ∀ K : Compacts U,
      integralRelativeHomologyMap (k + r + 1) (singularSubspaceInclusion U)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cU K) =
          cX (K.map (singularSubspaceInclusion U) (singularSubspaceInclusion U).continuous))
    (hcVX : ∀ K : Compacts V,
      integralRelativeHomologyMap (k + r + 1) (singularSubspaceInclusion V)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cV K) =
          cX (K.map (singularSubspaceInclusion V) (singularSubspaceInclusion V).continuous))
    (hcWX : ∀ K : Compacts ↥(U ∩ V),
      integralRelativeHomologyMap (k + r + 1) (singularSubspaceInclusion (U ∩ V))
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW K) =
          cX (K.map (singularSubspaceInclusion (U ∩ V)) (singularSubspaceInclusion (U ∩ V)).continuous))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology (r + 1) X)
    (DU : integralCompactlySupportedCohomology k U →ₗ[ℤ] integralSingularHomology (r + 1) U)
    (DV : integralCompactlySupportedCohomology k V →ₗ[ℤ] integralSingularHomology (r + 1) V)
    (DW : integralCompactlySupportedCohomology k ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology (r + 1) ↥(U ∩ V))
    (EU : integralCompactlySupportedCohomology (k + 1) U →ₗ[ℤ] integralSingularHomology r U)
    (EV : integralCompactlySupportedCohomology (k + 1) V →ₗ[ℤ] integralSingularHomology r V)
    (EW : integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology r ↥(U ∩ V))
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k (r + 1) α (cX K))
    (hDU : ∀ (K : Compacts U) (α : integralRelativeCohomology k (K : Set U)ᶜ),
      DU (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set U)ᶜ k (r + 1) α (cU K))
    (hDV : ∀ (K : Compacts V) (α : integralRelativeCohomology k (K : Set V)ᶜ),
      DV (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set V)ᶜ k (r + 1) α (cV K))
    (hDW : ∀ (K : Compacts ↥(U ∩ V)) (α : integralRelativeCohomology k (K : Set ↥(U ∩ V))ᶜ),
      DW (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set ↥(U ∩ V))ᶜ k (r + 1) α (cW K))
    (hEU : ∀ (K : Compacts U) (α : integralRelativeCohomology (k + 1) (K : Set U)ᶜ),
      EU (integralRelativeToCompactlySupportedCohomology (k + 1) K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set U)ᶜ (k + 1) r α
          ((eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set U)ᶜ)
            (show k + r + 1 = (k + 1) + r by omega))) (cU K)))
    (hEV : ∀ (K : Compacts V) (α : integralRelativeCohomology (k + 1) (K : Set V)ᶜ),
      EV (integralRelativeToCompactlySupportedCohomology (k + 1) K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set V)ᶜ (k + 1) r α
          ((eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set V)ᶜ)
            (show k + r + 1 = (k + 1) + r by omega))) (cV K)))
    (hEW : ∀ (K : Compacts ↥(U ∩ V)) (α : integralRelativeCohomology (k + 1) (K : Set ↥(U ∩ V))ᶜ),
      EW (integralRelativeToCompactlySupportedCohomology (k + 1) K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set ↥(U ∩ V))ᶜ (k + 1) r α
          ((eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set ↥(U ∩ V))ᶜ)
            (show k + r + 1 = (k + 1) + r by omega))) (cW K)))
    (hsurjDW : Function.Surjective DW) (hbijDU : Function.Bijective DU)
    (hbijDV : Function.Bijective DV) (hbijEW : Function.Bijective EW)
    (hinjEU : Function.Injective EU) (hinjEV : Function.Injective EV) :
    Function.Bijective DX := by
  have hUfamily := compact_homology_family_coherent_of_map (k + r + 1)
    (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal cU cX hXfamily hcUX
  have hVfamily := compact_homology_family_coherent_of_map (k + r + 1)
    (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal cV cX hXfamily hcVX
  have hWfamily := compact_homology_family_coherent_of_map (k + r + 1)
    (singularSubspaceInclusion (U ∩ V)) (hU.inter hV).isOpenEmbedding_subtypeVal
    cW cX hXfamily hcWX
  have hdegree : k + r + 1 = (k + 1) + r := by omega
  let cUnext (K : Compacts U) : integralRelativeHomology ((k + 1) + r) (K : Set U)ᶜ :=
    (eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set U)ᶜ) hdegree)) (cU K)
  have hUnext (K L : Compacts U) (h : K ≤ L) :
      integralRelativeHomologyMap ((k + 1) + r) (ContinuousMap.id U)
        (show (L : Set U)ᶜ ⊆ (K : Set U)ᶜ from compl_subset_compl.mpr h) (cUnext L) = cUnext K := by
    exact (relative_homology_map_cast hdegree (ContinuousMap.id U)
      (show (L : Set U)ᶜ ⊆ (K : Set U)ᶜ from compl_subset_compl.mpr h) (cU L)).trans
        (congrArg (fun c => (eqToHom (congrArg
          (fun n => integralRelativeHomology n (K : Set U)ᶜ) hdegree)) c)
          (hUfamily K L h))
  let cVnext (K : Compacts V) : integralRelativeHomology ((k + 1) + r) (K : Set V)ᶜ :=
    (eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set V)ᶜ) hdegree)) (cV K)
  have hVnext (K L : Compacts V) (h : K ≤ L) :
      integralRelativeHomologyMap ((k + 1) + r) (ContinuousMap.id V)
        (show (L : Set V)ᶜ ⊆ (K : Set V)ᶜ from compl_subset_compl.mpr h) (cVnext L) = cVnext K := by
    exact (relative_homology_map_cast hdegree (ContinuousMap.id V)
      (show (L : Set V)ᶜ ⊆ (K : Set V)ᶜ from compl_subset_compl.mpr h) (cV L)).trans
        (congrArg (fun c => (eqToHom (congrArg
          (fun n => integralRelativeHomology n (K : Set V)ᶜ) hdegree)) c)
          (hVfamily K L h))
  let cWnext (K : Compacts ↥(U ∩ V)) : integralRelativeHomology ((k + 1) + r) (K : Set ↥(U ∩ V))ᶜ :=
    (eqToHom (congrArg (fun n => integralRelativeHomology n (K : Set ↥(U ∩ V))ᶜ) hdegree)) (cW K)
  have hWnext (K L : Compacts ↥(U ∩ V)) (h : K ≤ L) :
      integralRelativeHomologyMap ((k + 1) + r) (ContinuousMap.id ↥(U ∩ V))
        (show (L : Set ↥(U ∩ V))ᶜ ⊆ (K : Set ↥(U ∩ V))ᶜ from compl_subset_compl.mpr h) (cWnext L) = cWnext K := by
    exact (relative_homology_map_cast hdegree (ContinuousMap.id ↥(U ∩ V))
      (show (L : Set ↥(U ∩ V))ᶜ ⊆ (K : Set ↥(U ∩ V))ᶜ from compl_subset_compl.mpr h) (cW L)).trans
        (congrArg (fun c => (eqToHom (congrArg
          (fun n => integralRelativeHomology n (K : Set ↥(U ∩ V))ᶜ) hdegree)) c)
          (hWfamily K L h))
  have hcWU := integralRelativeHomology_family_map_of_comp (k + r + 1)
    (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) (singularSubspaceInclusion U)
    (Set.inclusion_injective inter_subset_left) hU.isOpenEmbedding_subtypeVal
    cW cU cX hcWX hcUX
  have hcWUnext (K : Compacts ↥(U ∩ V)) :
      integralRelativeHomologyMap ((k + 1) + r)
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
        (mapsTo_iff_image_subset.mpr (image_compl_subset (Set.inclusion_injective inter_subset_left)))
        (cWnext K) = cUnext (K.map (ContinuousMap.inclusion inter_subset_left)
          (ContinuousMap.inclusion inter_subset_left).continuous) := by
    dsimp only [cWnext, cUnext]
    rw [relative_homology_map_cast hdegree, hcWU]
    rfl
  have hcWV := integralRelativeHomology_family_map_of_comp (k + r + 1)
    (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) (singularSubspaceInclusion V)
    (Set.inclusion_injective inter_subset_right) hV.isOpenEmbedding_subtypeVal
    cW cV cX hcWX hcVX
  have hcWVnext (K : Compacts ↥(U ∩ V)) :
      integralRelativeHomologyMap ((k + 1) + r)
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
        (mapsTo_iff_image_subset.mpr (image_compl_subset (Set.inclusion_injective inter_subset_right)))
        (cWnext K) = cVnext (K.map (ContinuousMap.inclusion inter_subset_right)
          (ContinuousMap.inclusion inter_subset_right).continuous) := by
    dsimp only [cWnext, cVnext]
    rw [relative_homology_map_cast hdegree, hcWV]
    rfl
  apply cap_bijective_of_two_open_diagram k r U V hU hV hcover
    DX DU DV DW EU EV EW
  · exact prescribed_cap_natural k (r + 1)
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
        ((hU.inter hV).preimage continuous_subtype_val))
      cW cU hWfamily hUfamily hcWU
      DW DU hDW hDU
  · exact prescribed_cap_natural k (r + 1)
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
        ((hU.inter hV).preimage continuous_subtype_val))
      cW cV hWfamily hVfamily hcWV
      DW DV hDW hDV
  · exact prescribed_cap_natural (k + 1) r
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
        ((hU.inter hV).preimage continuous_subtype_val))
      cWnext cUnext hWnext hUnext hcWUnext
      EW EU hEW hEU
  · exact prescribed_cap_natural (k + 1) r
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
        ((hU.inter hV).preimage continuous_subtype_val))
      cWnext cVnext hWnext hVnext hcWVnext
      EW EV hEW hEV
  · exact prescribed_cap_natural k (r + 1) (singularSubspaceInclusion U)
      hU.isOpenEmbedding_subtypeVal cU cX hUfamily hXfamily hcUX DU DX hDU hDX
  · exact prescribed_cap_natural k (r + 1) (singularSubspaceInclusion V)
      hV.isOpenEmbedding_subtypeVal cV cX hVfamily hXfamily hcVX DV DX hDV hDX
  · apply integralCompactlySupportedCohomology_cap_mayerVietoris k r U V hU hV hcover
      cX cWnext hXfamily ?_ DX EW hDX hEW
    intro K
    dsimp only [cWnext]
    rw [relative_homology_map_cast hdegree, hcWX]
    rfl
  · exact hsurjDW
  · exact hbijDU
  · exact hbijDV
  · exact hbijEW
  · exact hinjEU
  · exact hinjEV

private theorem cap_bijective_zero_of_two_open_diagram
    (k : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology 0 X)
    (DU : integralCompactlySupportedCohomology k U →ₗ[ℤ] integralSingularHomology 0 U)
    (DV : integralCompactlySupportedCohomology k V →ₗ[ℤ] integralSingularHomology 0 V)
    (DW : integralCompactlySupportedCohomology k ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology 0 ↥(U ∩ V))
    (hWU : (integralSingularHomologyMap 0
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))).comp DW =
      DU.comp (integralCompactlySupportedCohomologyPushforward k
        (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hWV : (integralSingularHomologyMap 0
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))).comp DW =
      DV.comp (integralCompactlySupportedCohomologyPushforward k
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
        (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
          ((hU.inter hV).preimage continuous_subtype_val))))
    (hUX : (integralSingularHomologyMap 0 (singularSubspaceInclusion U)).comp DU =
      DX.comp (integralCompactlySupportedCohomologyPushforward k
        (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal))
    (hVX : (integralSingularHomologyMap 0 (singularSubspaceInclusion V)).comp DV =
      DX.comp (integralCompactlySupportedCohomologyPushforward k
        (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal))
    (hDW : Function.Surjective DW) (hDU : Function.Bijective DU)
    (hDV : Function.Bijective DV)
    [Subsingleton (integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V))] :
    Function.Bijective DX := by
  let f₁ := compactMayerVietorisDifference k U V hU hV
  let f₂ := compactMayerVietorisSum k U V hU hV
  let g₁ := Homology.singularMayerVietorisDifferenceMap integralSingularCoefficients
    (TopCat.of X) U V 0
  let g₂ := Homology.singularMayerVietorisSumMap integralSingularCoefficients
    (TopCat.of X) U V 0
  let P := integralCompactlySupportedCohomologyPushforward k
    (singularSubspaceInclusion (U ∪ V)) (hU.union hV).isOpenEmbedding_subtypeVal
  have hc₁ : g₁.comp DW = (DU.prodMap DV).comp f₁ := by
    ext a
    · exact LinearMap.congr_fun hWU a
    · change -integralSingularHomologyMap 0
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) (DW a) = DV (-_)
      have h := LinearMap.congr_fun hWV a
      dsimp only [LinearMap.comp_apply] at h
      rw [h, map_neg]
  have hc₂ : g₂.comp (DU.prodMap DV) = (DX.comp P).comp f₂ := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change integralSingularHomologyMap 0 (singularSubspaceInclusion U) (DU a) +
      integralSingularHomologyMap 0 (singularSubspaceInclusion V) (DV b) = _
    have hu := LinearMap.congr_fun hUX a
    have hv := LinearMap.congr_fun hVX b
    dsimp only [LinearMap.comp_apply] at hu hv
    rw [hu, hv]
    change DX _ + DX _ = DX (P (_ + _))
    rw [map_add, map_add]
    congr 1
    · have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp k
        (ContinuousMap.inclusion (subset_union_left : U ⊆ U ∪ V))
        (singularSubspaceInclusion (U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_left
          (hU.preimage continuous_subtype_val)) (hU.union hV).isOpenEmbedding_subtypeVal) a
      exact congrArg DX h
    · have h := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp k
        (ContinuousMap.inclusion (subset_union_right : V ⊆ U ∪ V))
        (singularSubspaceInclusion (U ∪ V))
        (_root_.Topology.IsOpenEmbedding.inclusion subset_union_right
          (hV.preimage continuous_subtype_val)) (hU.union hV).isOpenEmbedding_subtypeVal) b
      exact congrArg DX h
  have hf₂ : Function.Surjective f₂ := by
    intro x
    obtain ⟨a, b, hab⟩ :=
      (integralCompactlySupportedCohomology_mayerVietoris_exact_union k U V hU hV x).mp
        (Subsingleton.elim _ _)
    exact ⟨(a, b), hab⟩
  have hmid := LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    f₁ f₂ g₁ g₂ DW (DU.prodMap DV) (DX.comp P) hc₁ hc₂
    (compact_mayerVietoris_exact_sum k U V hU hV)
    (Homology.singularMayerVietoris_exact_sum integralSingularCoefficients
      (TopCat.of X) U V hU hV hcover 0)
    hDW (hDU.prodMap hDV) hf₂
    (Homology.singularMayerVietorisSumMap_zero_surjective integralSingularCoefficients
      (TopCat.of X) U V hcover)
  have hP := compact_union_inclusion_bijective k U V hU hV hcover
  exact ⟨fun a b hab => by
    obtain ⟨a', rfl⟩ := hP.surjective a
    obtain ⟨b', rfl⟩ := hP.surjective b
    exact congrArg P (hmid.injective hab), fun x => by
      obtain ⟨a, ha⟩ := hmid.surjective x
      exact ⟨P a, ha⟩⟩

theorem integralCompactlySupportedCohomology_cap_bijective_zero_of_two_open_cover
    (k : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (cX : ∀ K : Compacts X, integralRelativeHomology k (K : Set X)ᶜ)
    (cU : ∀ K : Compacts U, integralRelativeHomology k (K : Set U)ᶜ)
    (cV : ∀ K : Compacts V, integralRelativeHomology k (K : Set V)ᶜ)
    (cW : ∀ K : Compacts ↥(U ∩ V), integralRelativeHomology k (K : Set ↥(U ∩ V))ᶜ)
    (hXfamily : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap k (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hcUX : ∀ K : Compacts U,
      integralRelativeHomologyMap k (singularSubspaceInclusion U)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cU K) =
          cX (K.map (singularSubspaceInclusion U) (singularSubspaceInclusion U).continuous))
    (hcVX : ∀ K : Compacts V,
      integralRelativeHomologyMap k (singularSubspaceInclusion V)
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cV K) =
          cX (K.map (singularSubspaceInclusion V) (singularSubspaceInclusion V).continuous))
    (hcWX : ∀ K : Compacts ↥(U ∩ V),
      integralRelativeHomologyMap k (singularSubspaceInclusion (U ∩ V))
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (cW K) =
          cX (K.map (singularSubspaceInclusion (U ∩ V)) (singularSubspaceInclusion (U ∩ V)).continuous))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology 0 X)
    (DU : integralCompactlySupportedCohomology k U →ₗ[ℤ] integralSingularHomology 0 U)
    (DV : integralCompactlySupportedCohomology k V →ₗ[ℤ] integralSingularHomology 0 V)
    (DW : integralCompactlySupportedCohomology k ↥(U ∩ V) →ₗ[ℤ] integralSingularHomology 0 ↥(U ∩ V))
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k 0 α (cX K))
    (hDU : ∀ (K : Compacts U) (α : integralRelativeCohomology k (K : Set U)ᶜ),
      DU (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set U)ᶜ k 0 α (cU K))
    (hDV : ∀ (K : Compacts V) (α : integralRelativeCohomology k (K : Set V)ᶜ),
      DV (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set V)ᶜ k 0 α (cV K))
    (hDW : ∀ (K : Compacts ↥(U ∩ V)) (α : integralRelativeCohomology k (K : Set ↥(U ∩ V))ᶜ),
      DW (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set ↥(U ∩ V))ᶜ k 0 α (cW K))
    (hsurjDW : Function.Surjective DW) (hbijDU : Function.Bijective DU)
    (hbijDV : Function.Bijective DV)
    [Subsingleton (integralCompactlySupportedCohomology (k + 1) ↥(U ∩ V))] :
    Function.Bijective DX := by
  have hUfamily := compact_homology_family_coherent_of_map k
    (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal cU cX hXfamily hcUX
  have hVfamily := compact_homology_family_coherent_of_map k
    (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal cV cX hXfamily hcVX
  have hWfamily := compact_homology_family_coherent_of_map k
    (singularSubspaceInclusion (U ∩ V)) (hU.inter hV).isOpenEmbedding_subtypeVal
    cW cX hXfamily hcWX
  have hcWU := integralRelativeHomology_family_map_of_comp k
    (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) (singularSubspaceInclusion U)
    (Set.inclusion_injective inter_subset_left) hU.isOpenEmbedding_subtypeVal
    cW cU cX hcWX hcUX
  have hcWV := integralRelativeHomology_family_map_of_comp k
    (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) (singularSubspaceInclusion V)
    (Set.inclusion_injective inter_subset_right) hV.isOpenEmbedding_subtypeVal
    cW cV cX hcWX hcVX
  apply cap_bijective_zero_of_two_open_diagram k U V hU hV hcover DX DU DV DW
  · exact prescribed_cap_natural k 0
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_left
        ((hU.inter hV).preimage continuous_subtype_val))
      cW cU hWfamily hUfamily hcWU DW DU hDW hDU
  · exact prescribed_cap_natural k 0
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))
      (_root_.Topology.IsOpenEmbedding.inclusion inter_subset_right
        ((hU.inter hV).preimage continuous_subtype_val))
      cW cV hWfamily hVfamily hcWV DW DV hDW hDV
  · exact prescribed_cap_natural k 0 (singularSubspaceInclusion U)
      hU.isOpenEmbedding_subtypeVal cU cX hUfamily hXfamily hcUX DU DX hDU hDX
  · exact prescribed_cap_natural k 0 (singularSubspaceInclusion V)
      hV.isOpenEmbedding_subtypeVal cV cX hVfamily hXfamily hcVX DV DX hDV hDX
  · exact hsurjDW
  · exact hbijDU
  · exact hbijDV

end DifferentialGeometry.Topology
