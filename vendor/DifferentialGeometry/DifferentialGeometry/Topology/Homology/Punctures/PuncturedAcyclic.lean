module

public import DifferentialGeometry.Topology.Homology.Relative.DeltaIso
public import DifferentialGeometry.Topology.Homology.Local.ChartTransport
public import DifferentialGeometry.Topology.Homology.Local.Injectivity
public import DifferentialGeometry.Topology.Morse.Strip.Defs

@[expose] public section

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

abbrev acyclic (X : TopCat.{u}) : Prop :=
  (∀ k, 1 ≤ k → IsZero (singularHomology R X k)) ∧ IsZero (reducedHomologyZero R X)

theorem acyclic.of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (h : acyclic R (TopCat.of Y)) :
    acyclic R (TopCat.of X) :=
  ⟨fun k hk => (h.1 k hk).of_iso (homologyIso R e k), h.2.of_iso (reducedHomologyZeroIso R e)⟩

theorem acyclic_of_homotopyEquivInclusion {M : Type u} [TopologicalSpace M] {A B : Set M}
    (hAB : isHomotopyEquivInclusion A B) (h : acyclic R (TopCat.of B)) :
    acyclic R (TopCat.of A) := by
  obtain ⟨e, -⟩ := hAB
  exact acyclic.of_homotopyEquiv R e h

theorem acyclic.of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    acyclic R (TopCat.of X) :=
  ⟨fun k hk => isZero_of_contractible R X k (by omega), isZero_reducedHomologyZero_of_contractible R X⟩

theorem isIso_ε_of_isZero_reducedHomologyZero (X : TopCat.{u}) [Nonempty X] (h0 : IsZero (reducedHomologyZero R X)) :
    IsIso (ε R X) := by
  have hmono : Mono (ε R X) := Preadditive.mono_of_isZero_kernel _ h0
  have hepi : Epi (ε R X) :=
    IsSplitEpi.epi _ (hf := ⟨⟨⟨εSection R X, εSection_ε R X⟩⟩⟩)
  exact isIso_of_mono_of_epi _

theorem epi_inclMap_zero_of_contractible (X : TopCat.{u}) (A : Set X) [ContractibleSpace A]
    (h0 : IsZero (reducedHomologyZero R X)) : Epi (inclMap R X A 0) := by
  have hA : Nonempty (TopCat.of A) := inferInstanceAs (Nonempty A)
  have hX : Nonempty X := ⟨(Classical.arbitrary A : A).1⟩
  have hεA : IsIso (ε R (TopCat.of A)) := isIso_ε_of_contractible R A
  have hεX : IsIso (ε R X) := isIso_ε_of_isZero_reducedHomologyZero R X h0
  have h : inclMap R X A 0 = ε R (TopCat.of A) ≫ inv (ε R X) := by
    rw [← inclMap_ε, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

theorem isZero_relativeHomology_of_contractible_of_acyclic {X : TopCat.{u}} {A : Set X} [ContractibleSpace A]
    (h : ∀ k, 1 ≤ k → IsZero (singularHomology R X k)) (h0 : IsZero (reducedHomologyZero R X)) (k : ℕ) :
    IsZero (relativeHomology R X A k) := by
  rcases k with _ | _ | i
  · exact isZero_relativeHomology_zero_of_epi R X A (epi_inclMap_zero_of_contractible R X A h0)
  · exact (les_red_exact₃ R X A).isZero_X₂ ((h 1 le_rfl).eq_zero_of_src _)
      ((isZero_reducedHomologyZero_of_contractible R A).eq_zero_of_tgt _)
  · exact (les_exact₃ R X A (i + 1)).isZero_X₂ ((h (i + 2) (by omega)).eq_zero_of_src _)
      ((isZero_of_contractible R A (i + 1) i.succ_ne_zero).eq_zero_of_tgt _)

theorem isZero_relativeHomology_of_contractible_of_acyclic' {X : TopCat.{u}} {A : Set X}
    [ContractibleSpace A] (h : acyclic R X) (k : ℕ) : IsZero (relativeHomology R X A k) :=
  isZero_relativeHomology_of_contractible_of_acyclic R h.1 h.2 k

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

theorem pathConnectedSpace_of_homotopyEquiv_sphere (hn : 1 ≤ n) (e : M ≃ₕ unitSphere n) :
    PathConnectedSpace M := by
  have := Sphere.pathConnectedSpace_of_one_le hn
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.arbitrary (unitSphere n))⟩, fun x y => ?_⟩
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

variable [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem acyclic_compl_singleton_of_homotopyEquiv_sphere (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M)
    (hsurj : Epi (relπ R (TopCat.of M) {c}ᶜ n)) :
    (∀ k, 1 ≤ k → IsZero (singularHomology R (TopCat.of ({c}ᶜ : Set M)) k)) ∧
      IsZero (reducedHomologyZero R (TopCat.of ({c}ᶜ : Set M))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : 1 ≤ m + 2 := by omega
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_sphere hn1 e
  have hM : ∀ k, k ≠ m + 2 → k ≠ 0 → IsZero (singularHomology R (TopCat.of M) k) := fun k hk hk0 =>
    Sphere.isZero_singularHomology_of_homotopyEquiv_sphere R e k hk hk0
  have hMred : IsZero (reducedHomologyZero R (TopCat.of M)) :=
    Sphere.isZero_reducedHomologyZero_of_homotopyEquiv_sphere R e (by omega)
  have hrel : ∀ k, k ≠ m + 2 → IsZero (relativeHomology R (TopCat.of M) {c}ᶜ k) := fun k hk =>
    isZero_relativeHomology_compl_singleton_manifold R hn1 c hk
  have hmono : Mono (relπ R (TopCat.of M) {c}ᶜ (m + 2)) := mono_relπ_compl_singleton R hn1 c
  refine ⟨fun k hk => ?_, ?_⟩
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
      ((hrel 1 (by omega)).eq_zero_of_src _) (hMred.eq_zero_of_tgt _)

theorem acyclic.compl_singleton_of_homotopyEquiv_sphere (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n) (c : M)
    (hsurj : Epi (relπ R (TopCat.of M) {c}ᶜ n)) : acyclic R (TopCat.of ({c}ᶜ : Set M)) :=
  acyclic_compl_singleton_of_homotopyEquiv_sphere R hn e c hsurj

end charted

end DifferentialGeometry.Topology.SingularPair

end
