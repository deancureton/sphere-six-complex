module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.CapNaturality
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.DirectedUnion
public import DifferentialGeometry.Topology.Homology.DirectedUnion
public import DifferentialGeometry.Topology.Homology.CompactHomologyFamilyNaturality
public import DifferentialGeometry.Topology.Homology.CompactHomologyOpenEmbedding
public import DifferentialGeometry.Topology.Homology.CompactHomologyLocalGenerators
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Vanishing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u v

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

private theorem compact_support_cap_natural_of_representatives
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
          cY (K.map f f.continuous))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y)
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K))
    (hDY : ∀ (L : Compacts Y) (β : integralRelativeCohomology k (L : Set Y)ᶜ),
      DY (integralRelativeToCompactlySupportedCohomology k L β) =
        integralRelativeCohomologyCapToAbsolute (L : Set Y)ᶜ k m β (cY L)) :
    (integralSingularHomologyMap m f).comp DX =
      DY.comp (integralCompactlySupportedCohomologyPushforward k f hf) := by
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    exists_integralCompactlySupportedCohomology_cap_natural k m f hf cX cY hX hY hc
  have hAD : A = DX := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hA K α).trans (hDX K α).symm)
  have hBD : B = DY := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hB K α).trans (hDY K α).symm)
  rwa [hAD, hBD] at hAB

private theorem compact_support_cap_bijective_of_directed_natural
    [T2Space X] {ι : Type v} [Nonempty ι]
    (k m : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (d : ∀ i, integralCompactlySupportedCohomology k (U i) →ₗ[ℤ]
      integralSingularHomology m (U i))
    (hd : ∀ i, Function.Bijective (d i))
    (hnat : ∀ i, (integralSingularHomologyMap m (singularSubspaceInclusion (U i))).comp
      (d i) = D.comp (integralCompactlySupportedCohomologyPushforward k
        (singularSubspaceInclusion (U i)) (hU i).isOpenEmbedding_subtypeVal))
    (htrans : ∀ i j (hij : U i ⊆ U j),
      (integralSingularHomologyMap m (ContinuousMap.inclusion hij)).comp (d i) =
        (d j).comp (integralCompactlySupportedCohomologyPushforward k
          (ContinuousMap.inclusion hij) (_root_.Topology.IsOpenEmbedding.inclusion hij
            ((hU i).preimage continuous_subtype_val)))) :
    Function.Bijective D := by
  constructor
  · apply (injective_iff_map_eq_zero D).mpr
    intro α hα
    obtain ⟨i, β, rfl⟩ :=
      integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover
        k U hU hdir hcover α
    have hz : integralSingularHomologyMap m (singularSubspaceInclusion (U i)) (d i β) = 0 :=
      (LinearMap.congr_fun (hnat i) β).trans hα
    obtain ⟨j, hij, hj⟩ :=
      exists_integralSingularHomologyMap_inclusion_eq_zero_of_directed_open_cover
        m U hU hdir hcover i (d i β) hz
    let p := integralCompactlySupportedCohomologyPushforward k (ContinuousMap.inclusion hij)
      (_root_.Topology.IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val))
    have hp : p β = 0 := (hd j).injective
      (((LinearMap.congr_fun (htrans i j hij) β).symm.trans hj).trans (map_zero (d j)).symm)
    have he := LinearMap.congr_fun (integralCompactlySupportedCohomologyPushforward_comp
      k (ContinuousMap.inclusion hij) (singularSubspaceInclusion (U j))
      (_root_.Topology.IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val))
      (hU j).isOpenEmbedding_subtypeVal) β
    change integralCompactlySupportedCohomologyPushforward k (singularSubspaceInclusion (U i))
      (hU i).isOpenEmbedding_subtypeVal β =
      integralCompactlySupportedCohomologyPushforward k (singularSubspaceInclusion (U j))
        (hU j).isOpenEmbedding_subtypeVal (p β) at he
    exact he.trans ((congrArg (integralCompactlySupportedCohomologyPushforward k
      (singularSubspaceInclusion (U j)) (hU j).isOpenEmbedding_subtypeVal) hp).trans (map_zero _))
  · intro γ
    obtain ⟨i, δ, hδ⟩ := exists_integralSingularHomologyMap_eq_of_directed_open_cover
      m U hU hdir hcover γ
    obtain ⟨β, hβ⟩ := (hd i).surjective δ
    refine ⟨integralCompactlySupportedCohomologyPushforward k
      (singularSubspaceInclusion (U i)) (hU i).isOpenEmbedding_subtypeVal β, ?_⟩
    exact (LinearMap.congr_fun (hnat i) β).symm.trans
      ((congrArg (integralSingularHomologyMap m (singularSubspaceInclusion (U i))) hβ).trans hδ)


theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_directed_open_cover
    [T2Space X] {ι : Type v} [Nonempty ι]
    (k m : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (ci : ∀ i, ∀ K : Compacts (U i), integralRelativeHomology (k + m) (K : Set (U i))ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (cX L) = cX K)
    (hi : ∀ i (K L : Compacts (U i)) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id (U i))
        (show MapsTo (ContinuousMap.id (U i)) (L : Set (U i))ᶜ (K : Set (U i))ᶜ from
          compl_subset_compl.mpr h) (ci i L) = ci i K)
    (hc : ∀ i (K : Compacts (U i)),
      integralRelativeHomologyMap (k + m) (singularSubspaceInclusion (U i))
        (mapsTo_iff_image_subset.mpr (image_compl_subset Subtype.val_injective)) (ci i K) =
          cX (K.map (singularSubspaceInclusion (U i)) continuous_subtype_val))
    (d : ∀ i, integralCompactlySupportedCohomology k (U i) →ₗ[ℤ]
      integralSingularHomology m (U i))
    (hd : ∀ i (K : Compacts (U i)) (α : integralRelativeCohomology k (K : Set (U i))ᶜ),
      d i (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set (U i))ᶜ k m α (ci i K))
    (hbij : ∀ i, Function.Bijective (d i)) :
    ∃! D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X,
      (∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) ∧
      Function.Bijective D := by
  obtain ⟨D, hD, huniq⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cX hX
  refine ⟨D, ⟨hD, ?_⟩, fun D' hD' => huniq D' hD'.1⟩
  apply compact_support_cap_bijective_of_directed_natural k m U hU hdir hcover D d hbij
  · intro i
    exact compact_support_cap_natural_of_representatives k m
      (singularSubspaceInclusion (U i)) (hU i).isOpenEmbedding_subtypeVal
      (ci i) cX (hi i) hX (hc i) (d i) D (hd i) hD
  · intro i j hij
    apply compact_support_cap_natural_of_representatives k m (ContinuousMap.inclusion hij)
      (_root_.Topology.IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val))
      (ci i) (ci j) (hi i) (hi j) ?_ (d i) (d j) (hd i) (hd j)
    exact integralRelativeHomology_family_map_of_comp (k + m)
      (ContinuousMap.inclusion hij) (singularSubspaceInclusion (U j))
      (Set.inclusion_injective hij) (hU j).isOpenEmbedding_subtypeVal
      (ci i) (ci j) cX (hc i) (hc j)

theorem integralCompactlySupportedCohomology_cap_bijective_of_local_generators_of_directed_open_cover
    [T2Space X] {ι : Type v}
    (k m : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (hX : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hgen : ∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p}))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K))
    (hlocal : ∀ i
      (c : ∀ K : Compacts (U i), integralRelativeHomology (k + m) (K : Set (U i))ᶜ),
      (∀ (K L : Compacts (U i)) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id (U i))
          (show (L : Set (U i))ᶜ ⊆ (K : Set (U i))ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
      (∀ p : U i, Function.Bijective (fun z : ℤ => z • c {p})) →
      ∀ D : integralCompactlySupportedCohomology k (U i) →ₗ[ℤ] integralSingularHomology m (U i),
        (∀ (K : Compacts (U i)) (α : integralRelativeCohomology k (K : Set (U i))ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set (U i))ᶜ k m α (c K)) →
          Function.Bijective D) :
    Function.Bijective DX := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ : IsEmpty X := ⟨fun x => by
      have hx : x ∈ ⋃ i, U i := hcover ▸ mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact isEmptyElim i⟩
    let _ := integralCompactlySupportedCohomology_subsingleton_of_isEmpty (X := X) k
    let _ : Subsingleton (integralSingularHomology m X) := by
      cases m with
      | zero =>
        let e := integralTotallyDisconnectedZeroEquiv (X := X)
        exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
      | succ n =>
        exact integralSingularHomology_subsingleton_of_totallyDisconnected (n + 1)
          (Nat.succ_ne_zero n) X
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr hι =>
    have hexists (i : ι) := exists_unique_compact_homology_family_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion (U i)) (hU i).isOpenEmbedding_subtypeVal cX hX
    choose ci hci using fun i => (hexists i).exists
    have hcap (i : ι) := exists_unique_integralCompactlySupportedCohomology_cap
      k m (ci i) (hci i).1
    choose Di hDi using fun i => (hcap i).exists
    have hbij (i : ι) : Function.Bijective (Di i) := by
      apply hlocal i (ci i) (hci i).1 ?_ (Di i) (hDi i)
      intro p
      apply (compact_homology_family_local_generator_iff_of_isOpenEmbedding (k + m)
        (singularSubspaceInclusion (U i)) (hU i).isOpenEmbedding_subtypeVal p
        (ci i) cX ((hci i).2 {p})).mpr
      exact hgen p.val
    obtain ⟨D, ⟨hD, hD_bij⟩, _⟩ :=
      exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_directed_open_cover
        k m U hU hdir hcover cX ci hX (fun i => (hci i).1) (fun i => (hci i).2) Di hDi hbij
    have heq : DX = D := integralCompactlySupportedCohomology_hom_ext k
      (fun K α => (hDX K α).trans (hD K α).symm)
    exact heq.symm ▸ hD_bij

end DifferentialGeometry.Topology

end
