module

public import DifferentialGeometry.Topology.Homology.Local.ChartTransport

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

abbrev ptRes (X : TopCat.{u}) (n : ℕ) (c : singularHomology R X n) (x : X) : relativeHomology R X {x}ᶜ n :=
  relπ R X {x}ᶜ n c

lemma subset_compl_singleton_of_notMem {X : Type*} {K : Set X} {y : X} (hy : y ∉ K) :
    K ⊆ {y}ᶜ :=
  fun _ hz hzy => hy (Set.mem_singleton_iff.1 hzy ▸ hz)

lemma ptRes_eq_zero_of_notMem {X : TopCat.{u}} {K : Set X} {n : ℕ} {c : singularHomology R X n}
    (hc : c ∈ Set.range (inclMap R X K n)) {y : X} (hy : y ∉ K) : ptRes R X n c y = 0 := by
  obtain ⟨a, rfl⟩ := hc
  have h0 : inclMap R X {y}ᶜ n ≫ relπ R X {y}ᶜ n = 0 :=
    (pair X {y}ᶜ).homologyMap_hom_homologyπ R n
  change relπ R X {y}ᶜ n (inclMap R X K n a) = 0
  rw [inclMap_eq_singularHomologyMap, ← inclOfLE_incl (subset_compl_singleton_of_notMem hy), singularHomologyMap_comp,
    ModuleCat.comp_apply, ← inclMap_eq_singularHomologyMap, ← ModuleCat.comp_apply, h0]
  rfl

lemma relπ_comp_relativeHomologyMap_compl_mapsTo {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A)
    (n : ℕ) :
    relπ R X Aᶜ n ≫ relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n = relπ R X {x}ᶜ n := by
  rw [relπ_natural R (𝟙 X) (compl_mapsTo hx) n, singularHomologyMap_id, Category.id_comp]

lemma ptRes_res {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A) (n : ℕ) (c : singularHomology R X n) :
    relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n (relπ R X Aᶜ n c) = ptRes R X n c x := by
  rw [← ModuleCat.comp_apply, relπ_comp_relativeHomologyMap_compl_mapsTo R hx n]

lemma ptRes_eq_zero_iff_of_mono {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A) (n : ℕ)
    (hmono : Mono (relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n)) (c : singularHomology R X n) :
    ptRes R X n c x = 0 ↔ relπ R X Aᶜ n c = 0 := by
  rw [← ptRes_res R hx n c]
  exact map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 hmono)

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

lemma exists_nhds_ptRes_eq_zero_iff (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n) (x : M) :
    ∃ U ∈ nhds x, ∀ y ∈ U,
      (ptRes R (TopCat.of M) n c y = 0 ↔ ptRes R (TopCat.of M) n c x = 0) := by
  obtain ⟨D, -, hxD, hiso⟩ := exists_chartBall_isIso_ptRes R hn x
  refine ⟨interior D, isOpen_interior.mem_nhds hxD, fun y hy => ?_⟩
  have hx : x ∈ D := interior_subset hxD
  have hy' : y ∈ D := interior_subset hy
  rw [ptRes_eq_zero_iff_of_mono R hy' n (have := hiso y hy'; inferInstance),
    ptRes_eq_zero_iff_of_mono R hx n (have := hiso x hx; inferInstance)]

theorem isOpen_ptRes_eq_zero (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n) :
    IsOpen {x | ptRes R (TopCat.of M) n c x = 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hUx⟩ := exists_nhds_ptRes_eq_zero_iff R hn c x
  exact Filter.mem_of_superset hU fun y hy => (hUx y hy).2 hx

theorem isClosed_ptRes_eq_zero (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n) :
    IsClosed {x | ptRes R (TopCat.of M) n c x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hUx⟩ := exists_nhds_ptRes_eq_zero_iff R hn c x
  exact Filter.mem_of_superset hU fun y hy hy0 => hx ((hUx y hy).1 hy0)

theorem isClopen_ptRes_eq_zero (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n) :
    IsClopen {x | ptRes R (TopCat.of M) n c x = 0} :=
  ⟨isClosed_ptRes_eq_zero R hn c, isOpen_ptRes_eq_zero R hn c⟩

theorem ptRes_eq_zero_of_exists [ConnectedSpace M] (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n)
    (h : ∃ x, ptRes R (TopCat.of M) n c x = 0) : ∀ x, ptRes R (TopCat.of M) n c x = 0 :=
  Set.eq_univ_iff_forall.1 ((isClopen_ptRes_eq_zero R hn c).eq_univ h)

end charted

end DifferentialGeometry.Topology.SingularPair

end
