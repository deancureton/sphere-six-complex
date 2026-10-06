module

public import DifferentialGeometry.Topology.Homology.Punctures.DiskComplement

/-!
# Acyclicity of punctured homology spheres

The puncture argument is adapted from DifferentialGeometry's
`acyclic_compl_singleton_of_homotopyEquiv_sphere` at commit
`788efe97894474c032de6dfb1289d515f613d15a`, replacing the homotopy equivalence by
homology vanishing and surjectivity onto top local homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [PathConnectedSpace M]

theorem acyclic_compl_singleton_of_isZero (hn : 2 ≤ n) (c : M)
    (hM : ∀ k, k ≠ n → k ≠ 0 → IsZero (singularHomology R (TopCat.of M) k))
    (hsurj : Epi (relπ R (TopCat.of M) {c}ᶜ n)) :
    acyclic R (TopCat.of ({c}ᶜ : Set M)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : 1 ≤ m + 2 := by omega
  have hrel : ∀ k, k ≠ m + 2 → IsZero (relativeHomology R (TopCat.of M) {c}ᶜ k) :=
    fun k hk ↦ isZero_relativeHomology_compl_singleton_manifold R hn1 c hk
  have hmono : Mono (relπ R (TopCat.of M) {c}ᶜ (m + 2)) :=
    mono_relπ_compl_singleton R hn1 c
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · by_cases hkn : k = m + 2
    · subst hkn
      have hincl : inclMap R (TopCat.of M) {c}ᶜ (m + 2) = 0 :=
        (les_exact₂ R (TopCat.of M) {c}ᶜ (m + 2)).mono_g_iff.1 hmono
      exact (les_exact₁ R (TopCat.of M) {c}ᶜ (m + 2)).isZero_X₂
        ((hrel (m + 3) (by omega)).eq_zero_of_src _) hincl
    by_cases hkn' : k = m + 1
    · subst hkn'
      have hδ : δ R (TopCat.of M) {c}ᶜ (m + 1) = 0 :=
        (les_exact₃ R (TopCat.of M) {c}ᶜ (m + 1)).epi_f_iff.1 hsurj
      exact (les_exact₁ R (TopCat.of M) {c}ᶜ (m + 1)).isZero_X₂ hδ
        ((hM (m + 1) (by omega) (by omega)).eq_zero_of_tgt _)
    · exact (les_exact₁ R (TopCat.of M) {c}ᶜ k).isZero_X₂
        ((hrel (k + 1) (by omega)).eq_zero_of_src _)
        ((hM k hkn (by omega)).eq_zero_of_tgt _)
  · exact (les_red_exact₁ R (TopCat.of M) {c}ᶜ).isZero_X₂
      ((hrel 1 (by omega)).eq_zero_of_src _)
      ((isZero_reducedHomologyZero_of_pathConnected R (TopCat.of M)).eq_zero_of_tgt _)

theorem acyclic_compl_image_diskInterior_of_isZero (hn : 2 ≤ n)
    {e : Disk n → M} (he : isChartDisk e)
    (hM : ∀ k, k ≠ n → k ≠ 0 → IsZero (singularHomology R (TopCat.of M) k))
    (hsurj : Epi (relπ R (TopCat.of M) {e (diskCenter n)}ᶜ n)) :
    acyclic R (TopCat.of ((e '' diskInterior n)ᶜ : Set M)) :=
  acyclic_of_homotopyEquivInclusion R he.isHomotopyEquivInclusion_compl_diskInterior
    (acyclic_compl_singleton_of_isZero R hn (e (diskCenter n)) hM hsurj)

theorem isZero_relativeHomology_compl_chartDisks_of_isZero (hn : 2 ≤ n)
    {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁))
    (hM : ∀ k, k ≠ n → k ≠ 0 → IsZero (singularHomology R (TopCat.of M) k))
    (hsurj : Epi (relπ R (TopCat.of M) {e₁ (diskCenter n)}ᶜ n)) (k : ℕ) :
    IsZero (relativeHomology R
      (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k) := by
  have := contractibleSpace_preimage_val_range h₀ hdisj
  exact (isZero_relativeHomology_of_contractible_of_acyclic' R
    (acyclic_compl_image_diskInterior_of_isZero R hn h₁ hM hsurj) k).of_iso
      (relativeHomologyTwoDiskComplementIso R h₀ hdisj k)

theorem relHomologyVanishes_compl_chartDisks_of_isZero (hn : 2 ≤ n)
    {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁))
    (hM : ∀ k, k ≠ n → k ≠ 0 →
      IsZero (singularHomology integerCoefficients.{u} (TopCat.of M) k))
    (hsurj : Epi (relπ integerCoefficients.{u} (TopCat.of M) {e₁ (diskCenter n)}ᶜ n)) :
    relHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) :=
  fun k ↦ isZero_relativeHomology_compl_chartDisks_of_isZero
    integerCoefficients hn h₀ h₁ hdisj hM hsurj k

end DifferentialGeometry.Topology.SingularPair
