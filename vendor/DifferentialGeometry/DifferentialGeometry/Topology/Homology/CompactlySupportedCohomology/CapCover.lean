module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapGluing
public import DifferentialGeometry.Topology.Homology.CompactHomologyOpenEmbedding
public import DifferentialGeometry.Topology.Homology.CompactHomologyLocalGenerators

@[expose] public section

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace DifferentialGeometry.Topology

private theorem cap_cover_exists_of_degree_eq
    {S : Type} [TopologicalSpace S] (n i j : ℕ) (hdeg : n = i + j)
    (c : ∀ K : Compacts S, integralRelativeHomology n (K : Set S)ᶜ)
    (hc : ∀ (K L : Compacts S) (h : K ≤ L),
      integralRelativeHomologyMap n (ContinuousMap.id S)
          (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (c L) = c K)
    (hp : ∀ p : S, Function.Bijective (fun z : ℤ => z • c {p}))
    (hlocal : ∀ (c : ∀ K : Compacts S, integralRelativeHomology (i + j) (K : Set S)ᶜ),
      (∀ (K L : Compacts S) (h : K ≤ L),
        integralRelativeHomologyMap (i + j) (ContinuousMap.id S)
          (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (c L) = c K) →
      (∀ p : S, Function.Bijective (fun z : ℤ => z • c {p})) →
      ∀ D : integralCompactlySupportedCohomology i S →ₗ[ℤ] integralSingularHomology j S,
        (∀ (K : Compacts S) (α : integralRelativeCohomology i (K : Set S)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology i K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ i j α (c K)) → Function.Bijective D) :
    ∃ D : integralCompactlySupportedCohomology i S →ₗ[ℤ] integralSingularHomology j S,
      (∀ (K : Compacts S) (α : integralRelativeCohomology i (K : Set S)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology i K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ i j α
          ((eqToHom (congrArg (fun q => integralRelativeHomology q (K : Set S)ᶜ) hdeg)) (c K))) ∧
      Function.Bijective D := by
  subst n
  obtain ⟨D, hD, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap i j c hc
  exact ⟨D, hD, hlocal c hc hp D hD⟩

theorem integralCompactlySupportedCohomology_cap_bijective_of_two_open_cover
    {X : Type} [TopologicalSpace X] [T2Space X]
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
    (hlocal : ∀ (S : Set X), (S = U ∨ S = V ∨ S = U ∩ V) →
      ∀ (i j : ℕ), i + j = n →
      ∀ (cS : ∀ K : Compacts S, integralRelativeHomology (i + j) (K : Set S)ᶜ),
      (∀ (K L : Compacts S) (h : K ≤ L),
        integralRelativeHomologyMap (i + j) (ContinuousMap.id S)
          (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (cS L) = cS K) →
      (∀ p : S, Function.Bijective (fun z : ℤ => z • cS {p})) →
      ∀ D : integralCompactlySupportedCohomology i S →ₗ[ℤ] integralSingularHomology j S,
        (∀ (K : Compacts S) (α : integralRelativeCohomology i (K : Set S)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology i K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ i j α (cS K)) → Function.Bijective D)
    (hvanish : ∀ q : ℕ, n < q →
      Subsingleton (integralCompactlySupportedCohomology q ↥(U ∩ V)))
    (k m : ℕ) (hkm : k + m = n)
    (cX : ∀ K : Compacts X, integralRelativeHomology (k + m) (K : Set X)ᶜ)
    (hXfamily : ∀ (K L : Compacts X) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
          (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K)
    (hpoint : ∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p}))
    (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (hDX : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      DX (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) :
    Function.Bijective DX := by
  obtain ⟨cU, ⟨hcU, hcUX⟩, _⟩ :=
    exists_unique_compact_homology_family_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal cX hXfamily
  have hpU (p : U) : Function.Bijective (fun z : ℤ => z • cU {p}) :=
    (compact_homology_family_local_generator_iff_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion U) hU.isOpenEmbedding_subtypeVal p
      cU cX (hcUX {p})).mpr (hpoint p)
  obtain ⟨DU, hDU, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cU hcU
  have hbijDU := hlocal U (Or.inl rfl) k m hkm cU hcU hpU DU hDU
  obtain ⟨cV, ⟨hcV, hcVX⟩, _⟩ :=
    exists_unique_compact_homology_family_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal cX hXfamily
  have hpV (p : V) : Function.Bijective (fun z : ℤ => z • cV {p}) :=
    (compact_homology_family_local_generator_iff_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion V) hV.isOpenEmbedding_subtypeVal p
      cV cX (hcVX {p})).mpr (hpoint p)
  obtain ⟨DV, hDV, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cV hcV
  have hbijDV := hlocal V (Or.inr (Or.inl rfl)) k m hkm cV hcV hpV DV hDV
  obtain ⟨cW, ⟨hcW, hcWX⟩, _⟩ :=
    exists_unique_compact_homology_family_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion (U ∩ V)) (hU.inter hV).isOpenEmbedding_subtypeVal cX hXfamily
  have hpW (p : ↥(U ∩ V)) : Function.Bijective (fun z : ℤ => z • cW {p}) :=
    (compact_homology_family_local_generator_iff_of_isOpenEmbedding (k + m)
      (singularSubspaceInclusion (U ∩ V)) (hU.inter hV).isOpenEmbedding_subtypeVal p
      cW cX (hcWX {p})).mpr (hpoint p)
  obtain ⟨DW, hDW, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cW hcW
  have hbijDW := hlocal (U ∩ V) (Or.inr (Or.inr rfl)) k m hkm cW hcW hpW DW hDW
  cases m with
  | zero =>
    let _ := hvanish (k + 1) (by omega)
    exact integralCompactlySupportedCohomology_cap_bijective_zero_of_two_open_cover
      k U V hU hV hcover cX cU cV cW hXfamily hcUX hcVX hcWX
      DX DU DV DW hDX hDU hDV hDW hbijDW.surjective hbijDU hbijDV
  | succ r =>
    have hdeg : k + r + 1 = (k + 1) + r := by omega
    obtain ⟨EU, hEU, hbijEU⟩ := cap_cover_exists_of_degree_eq
      (k + r + 1) (k + 1) r hdeg cU hcU hpU
      (hlocal U (Or.inl rfl) (k + 1) r (by omega))
    obtain ⟨EV, hEV, hbijEV⟩ := cap_cover_exists_of_degree_eq
      (k + r + 1) (k + 1) r hdeg cV hcV hpV
      (hlocal V (Or.inr (Or.inl rfl)) (k + 1) r (by omega))
    obtain ⟨EW, hEW, hbijEW⟩ := cap_cover_exists_of_degree_eq
      (k + r + 1) (k + 1) r hdeg cW hcW hpW
      (hlocal (U ∩ V) (Or.inr (Or.inr rfl)) (k + 1) r (by omega))
    exact integralCompactlySupportedCohomology_cap_bijective_succ_of_two_open_cover
      k r U V hU hV hcover cX cU cV cW hXfamily hcUX hcVX hcWX
      DX DU DV DW EU EV EW hDX hDU hDV hDW hEU hEV hEW
      hbijDW.surjective hbijDU hbijDV hbijEW hbijEU.injective hbijEV.injective

end DifferentialGeometry.Topology

end
