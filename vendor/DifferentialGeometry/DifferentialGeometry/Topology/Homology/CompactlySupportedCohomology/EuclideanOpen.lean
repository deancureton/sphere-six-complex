module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CapBasis
public import DifferentialGeometry.Topology.OpenBox
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.EuclideanHomeomorph
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.VanishingBasis

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

theorem integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_finrank_lt
    (S : Set E) (hS : IsOpen S) (n : ℕ) (hn : Module.finrank ℝ E < n) :
    Subsingleton (integralCompactlySupportedCohomology n S) := by
  obtain ⟨B, hB, hinter, hhomeo⟩ :=
    exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional (E := E)
  apply integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_basis hB
    (fun U hU V hV => Or.inl (hinter U hU V hV)) (Module.finrank ℝ E) ?_ hS n hn
  intro U hU k hk
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · exact integralCompactlySupportedCohomology_subsingleton_of_isEmpty k
  · obtain ⟨e⟩ := hhomeo U hU hUne
    let ι := Module.Free.ChooseBasisIndex ℝ E
    let b : Module.Basis ι ℝ E := Module.Free.chooseBasis ℝ E
    let c : E ≃L[ℝ] (ι → ℝ) := b.equivFunL
    have hdim : k ≠ Module.finrank ℝ (ι → ℝ) := by
      rw [← c.toLinearEquiv.finrank_eq]
      exact hk.ne'
    exact integralCompactlySupportedCohomology_subsingleton_of_homeomorph_of_ne_finrank
      (c.symm.toHomeomorph.trans e.symm) k hdim

end DifferentialGeometry.Topology

end

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry.Topology

private theorem compact_support_euclidean_open_seed
    {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty → Nonempty (S ≃ₜ E))
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cS : ∀ K : Compacts S, integralRelativeHomology (k + m) (K : Set S)ᶜ)
    (hcS : ∀ (K L : Compacts S) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id S)
        (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (cS L) = cS K)
    (hpS : ∀ p : S, Function.Bijective (fun z : ℤ => z • cS {p}))
    (D : integralCompactlySupportedCohomology k S →ₗ[ℤ] integralSingularHomology m S)
    (hD : ∀ (K : Compacts S) (α : integralRelativeCohomology k (K : Set S)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ k m α (cS K)) :
    Function.Bijective D := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · let _ := integralCompactlySupportedCohomology_subsingleton_of_isEmpty
      (X := (∅ : Set E)) k
    let _ : Subsingleton (integralSingularHomology m (∅ : Set E)) := by
      cases m with
      | zero =>
        let e := integralTotallyDisconnectedZeroEquiv (X := (∅ : Set E))
        exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
      | succ n =>
        exact integralSingularHomology_subsingleton_of_totallyDisconnected (n + 1)
          (Nat.succ_ne_zero n) (∅ : Set E)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨e⟩ := hS hSne
    let ι := Module.Free.ChooseBasisIndex ℝ E
    let b : Module.Basis ι ℝ E := Module.Free.chooseBasis ℝ E
    let c : E ≃L[ℝ] (ι → ℝ) := b.equivFunL
    have hdim : k + m = Module.finrank ℝ (ι → ℝ) :=
      hkm.trans c.toLinearEquiv.finrank_eq
    let eS : (ι → ℝ) ≃ₜ S := c.symm.toHomeomorph.trans e.symm
    obtain ⟨D', ⟨hD', hbij⟩, _⟩ :=
      exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_homeomorph_of_local_generator
        eS k m hdim 0 cS hcS (hpS (eS 0))
    have heq : D = D' := integralCompactlySupportedCohomology_hom_ext k
      (fun K α => (hD K α).trans (hD' K α).symm)
    exact heq.symm ▸ hbij

end DifferentialGeometry.Topology

end

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry.Topology

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

theorem integralCompactlySupportedCohomology_cap_bijective_of_isOpen
    (S : Set E) (hS : IsOpen S) (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cS : ∀ K : Compacts S, integralRelativeHomology (k + m) (K : Set S)ᶜ)
    (hcS : ∀ (K L : Compacts S) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id S)
        (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (cS L) = cS K)
    (hpS : ∀ p : S, Function.Bijective (fun z : ℤ => z • cS {p}))
    (D : integralCompactlySupportedCohomology k S →ₗ[ℤ] integralSingularHomology m S)
    (hD : ∀ (K : Compacts S) (α : integralRelativeCohomology k (K : Set S)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ k m α (cS K)) :
    Function.Bijective D := by
  obtain ⟨B, hB, hinter, hhomeo⟩ :=
    exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional (E := E)
  exact integralCompactlySupportedCohomology_cap_bijective_of_basis
    (Module.finrank ℝ E) B hB (fun U hU V hV => Or.inl (hinter U hU V hV))
    (fun U hU i j hij c hc hp DU hDU =>
      compact_support_euclidean_open_seed U (hhomeo U hU) i j hij c hc hp DU hDU)
    (fun q hq U hU => integralCompactlySupportedCohomology_subsingleton_of_isOpen_of_finrank_lt
      U hU q hq) S hS k m hkm cS hcS hpS D hD

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_isOpen
    (S : Set E) (hS : IsOpen S) (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (cS : ∀ K : Compacts S, integralRelativeHomology (k + m) (K : Set S)ᶜ)
    (hcS : ∀ (K L : Compacts S) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id S)
        (show (L : Set S)ᶜ ⊆ (K : Set S)ᶜ from compl_subset_compl.mpr h) (cS L) = cS K)
    (hpS : ∀ p : S, Function.Bijective (fun z : ℤ => z • cS {p})) :
    ∃! D : integralCompactlySupportedCohomology k S →ₗ[ℤ] integralSingularHomology m S,
      (∀ (K : Compacts S) (α : integralRelativeCohomology k (K : Set S)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set S)ᶜ k m α (cS K)) ∧
      Function.Bijective D := by
  obtain ⟨D, hD, huniq⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m cS hcS
  exact ⟨D, ⟨hD, integralCompactlySupportedCohomology_cap_bijective_of_isOpen
    S hS k m hkm cS hcS hpS D hD⟩, fun D' hD' => huniq D' hD'.1⟩

end DifferentialGeometry.Topology

end
