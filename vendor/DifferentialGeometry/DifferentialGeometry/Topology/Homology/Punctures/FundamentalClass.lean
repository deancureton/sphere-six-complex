module

public import DifferentialGeometry.Topology.Homology.Bockstein
public import DifferentialGeometry.Topology.Homology.Punctures.PuncturedAcyclic

@[expose] public section

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

lemma integerCoefficients_eq_zsmul_one (a : integerCoefficients.{u}) : a = a.down • (ULift.up 1 : integerCoefficients.{u}) :=
  ULift.ext (by simp)

lemma exists_zsmul_eq_of_iso_integerCoefficients {A : ModuleCat.{u} ℤ} (i : A ≅ integerCoefficients.{u}) (x : A) :
    ∃ m : ℤ, m • i.inv (ULift.up 1) = x := by
  refine ⟨(i.hom x).down, ?_⟩
  rw [← map_zsmul, ← integerCoefficients_eq_zsmul_one, Iso.hom_inv_id_apply]

lemma iso_integerCoefficients_inv_one_ne_zero {A : ModuleCat.{u} ℤ} (i : A ≅ integerCoefficients.{u}) : i.inv (ULift.up 1) ≠ 0 := by
  intro h
  have h1 : i.hom (i.inv (ULift.up 1)) = (ULift.up 1 : integerCoefficients.{u}) := Iso.inv_hom_id_apply i _
  rw [h, map_zero] at h1
  exact one_ne_zero (congrArg ULift.down h1).symm

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem epi_relπ_compl_singleton_modularCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M) (d : ℕ) [NeZero d] :
    Epi (relπ (modularCoefficients.{u} d) (TopCat.of M) {c}ᶜ n) := by
  have hn1 : 1 ≤ n := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  have hmono : Mono (relπ (modularCoefficients.{u} d) (TopCat.of M) {c}ᶜ n) :=
    mono_relπ_compl_singleton (modularCoefficients d) hn1 c
  let iH : singularHomology (modularCoefficients.{u} d) (TopCat.of M) n ≅ modularCoefficients.{u} d :=
    Sphere.singularHomologyTopIsoOfHomotopyEquivSphere (modularCoefficients d) e (by omega)
  let iR : relativeHomology (modularCoefficients.{u} d) (TopCat.of M) {c}ᶜ n ≅ modularCoefficients.{u} d :=
    relativeHomologyManifoldPointIso (modularCoefficients d) hn1 c
  set f : modularCoefficients.{u} d ⟶ modularCoefficients.{u} d := iH.inv ≫ relπ (modularCoefficients.{u} d) (TopCat.of M) {c}ᶜ n ≫ iR.hom with hf
  have hfmono : Mono f := by infer_instance
  have hfepi : Epi f := by
    rw [ModuleCat.epi_iff_surjective]
    exact (Finite.injective_iff_bijective.1 ((ModuleCat.mono_iff_injective f).1 hfmono)).2
  have : relπ (modularCoefficients.{u} d) (TopCat.of M) {c}ᶜ n = iH.hom ≫ f ≫ iR.inv := by
    simp [hf]
  rw [this]
  infer_instance

theorem epi_relπ_compl_singleton_integerCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M) :
    Epi (relπ integerCoefficients.{u} (TopCat.of M) {c}ᶜ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : 1 ≤ m + 2 := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  set X : TopCat.{u} := TopCat.of M with hX
  set φ := relπ integerCoefficients.{u} X {c}ᶜ (m + 2) with hφ
  have hmono : Mono φ := mono_relπ_compl_singleton integerCoefficients hn1 c
  let iH : singularHomology integerCoefficients.{u} X (m + 2) ≅ integerCoefficients.{u} := Sphere.singularHomologyTopIsoOfHomotopyEquivSphere integerCoefficients e (by omega)
  let iR : relativeHomology integerCoefficients.{u} X {c}ᶜ (m + 2) ≅ integerCoefficients.{u} := relativeHomologyManifoldPointIso integerCoefficients hn1 c
  set g₀ : singularHomology integerCoefficients.{u} X (m + 2) := iH.inv (ULift.up 1) with hg₀
  set r₀ : relativeHomology integerCoefficients.{u} X {c}ᶜ (m + 2) := iR.inv (ULift.up 1) with hr₀
  set a : ℤ := (iR.hom (φ g₀)).down with ha
  have hφg₀ : φ g₀ = a • r₀ := by
    rw [hr₀, ← map_zsmul, ← integerCoefficients_eq_zsmul_one, Iso.hom_inv_id_apply]
  have ha0 : a ≠ 0 := by
    intro h0
    apply iso_integerCoefficients_inv_one_ne_zero iH
    apply (ModuleCat.mono_iff_injective φ).1 hmono
    rw [map_zero, ← hg₀, hφg₀, h0, zero_smul]
  set d : ℕ := a.natAbs with hd
  have : NeZero d := ⟨Int.natAbs_ne_zero.2 ha0⟩
  have hδφ : ∀ x, δ integerCoefficients.{u} X {c}ᶜ (m + 1) (φ x) = 0 := fun x => by
    have h0 : relπ integerCoefficients.{u} X {c}ᶜ (m + 2) ≫ δ integerCoefficients.{u} X {c}ᶜ (m + 1) = 0 :=
      (pair X {c}ᶜ).comp_homologyδ integerCoefficients (m + 2) (m + 1) rfl
    rw [← ModuleCat.comp_apply, hφ, h0]
    rfl
  have h1 : ∀ g : singularHomology integerCoefficients.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1), (d : ℤ) • g = 0 := by
    intro g
    have hincl : inclMap integerCoefficients.{u} X {c}ᶜ (m + 1) g = 0 := by
      rw [(Sphere.isZero_singularHomology_of_homotopyEquiv_sphere integerCoefficients e (m + 1) (by omega) (by omega)).eq_zero_of_tgt
        (inclMap integerCoefficients.{u} X {c}ᶜ (m + 1))]
      rfl
    obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1 (les_exact₁ integerCoefficients X {c}ᶜ (m + 1)) g hincl
    obtain ⟨k, hk⟩ := exists_zsmul_eq_of_iso_integerCoefficients iR β
    obtain ⟨q, hq⟩ : a ∣ (d : ℤ) := Int.dvd_natAbs.2 dvd_rfl
    change δ integerCoefficients.{u} X {c}ᶜ (m + 1) β = g at hβ
    rw [← hβ, ← map_zsmul, ← hk, smul_comm, hq, mul_smul, smul_comm a, ← hφg₀]
    simp only [map_zsmul, hδφ]
    rw [zsmul_zero, zsmul_zero]
  have h2 : IsZero (singularHomology (modularCoefficients.{u} d) (TopCat.of ({c}ᶜ : Set M)) (m + 1)) :=
    (acyclic_compl_singleton_of_homotopyEquiv_sphere (modularCoefficients d) hn e c
      (epi_relπ_compl_singleton_modularCoefficients hn e c d)).1 (m + 1) (by omega)
  have hG : IsZero (singularHomology integerCoefficients.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1)) := by
    have : Subsingleton (singularHomology integerCoefficients.{u} (TopCat.of ({c}ᶜ : Set M)) (m + 1)) := by
      refine subsingleton_of_forall_eq 0 fun g => ?_
      obtain ⟨g', hg'⟩ := exists_smul_eq_of_isZero d _ (m + 1) h2 g
      rw [← hg', h1]
    exact ModuleCat.isZero_of_subsingleton _
  exact (les_exact₃ integerCoefficients X {c}ᶜ (m + 1)).epi_f_iff.2 (hG.eq_zero_of_tgt _)

theorem isIso_relπ_compl_singleton_integerCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M) :
    IsIso (relπ integerCoefficients.{u} (TopCat.of M) {c}ᶜ n) := by
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere (by omega) e
  have := mono_relπ_compl_singleton integerCoefficients (by omega : 1 ≤ n) c
  have := epi_relπ_compl_singleton_integerCoefficients hn e c
  exact isIso_of_mono_of_epi _

theorem acyclic_compl_singleton_integerCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M) :
    acyclic integerCoefficients.{u} (TopCat.of ({c}ᶜ : Set M)) :=
  acyclic_compl_singleton_of_homotopyEquiv_sphere integerCoefficients hn e c (epi_relπ_compl_singleton_integerCoefficients hn e c)

theorem isZero_singularHomology_compl_singleton_integerCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M) :
    IsZero (singularHomology integerCoefficients.{u} (TopCat.of ({c}ᶜ : Set M)) (n - 1)) :=
  (acyclic_compl_singleton_integerCoefficients hn e c).1 (n - 1) (by omega)

end charted

end DifferentialGeometry.Topology.SingularPair

end
