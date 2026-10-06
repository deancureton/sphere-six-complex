module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactVanishing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCompactHomology
public import Mathlib.Topology.Compactness.LocallyCompact
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMayerVietoris
public import Mathlib.Topology.Compactness.Compact
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactSupport

@[expose] public section


section

noncomputable section

open CategoryTheory Module Set

universe u v

namespace DifferentialGeometry.Topology

private theorem relative_compact_chart_high_degree_vanishing
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] (n : ℕ) (hn : finrank ℝ E < n)
    (e : OpenPartialHomeomorph X E) (K : Set X) (hK : IsCompact K)
    (hs : K ⊆ e.source) : Subsingleton (integralRelativeHomology n Kᶜ) := by
  have himage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hs)
  have ht : e '' K ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hinverse : e.symm '' (e '' K) = K :=
    e.toPartialEquiv.symm_image_image_of_subset_source hs
  let := integralRelativeHomology_subsingleton_of_compact n hn (e '' K) himage
  have h := (integralRelativeHomologyOpenPartialHomeomorphIso n e
    (e '' K) himage ht).toLinearEquiv
  rw [hinverse] at h
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩

private theorem relative_finite_chart_union_high_degree_vanishing
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] {ι : Type v}
    (s : Finset ι) (e : ι → OpenPartialHomeomorph X E) (K : ι → Set X)
    (hcompact : ∀ i ∈ s, IsCompact (K i)) (hsource : ∀ i ∈ s, K i ⊆ (e i).source)
    (n : ℕ) (hn : finrank ℝ E < n) :
    Subsingleton (integralRelativeHomology n (⋃ i ∈ s, K i)ᶜ) := by
  classical
  induction s using Finset.induction_on generalizing K n with
  | empty =>
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, compl_empty] using
      integralRelativeHomology_univ_subsingleton (X := X) n
  | @insert i s hi ih =>
    have hki : IsCompact (K i) := hcompact i (Finset.mem_insert_self i s)
    have hsi : K i ⊆ (e i).source := hsource i (Finset.mem_insert_self i s)
    have hks : ∀ j ∈ s, IsCompact (K j) :=
      fun j hj => hcompact j (Finset.mem_insert_of_mem hj)
    have hss : ∀ j ∈ s, K j ⊆ (e j).source :=
      fun j hj => hsource j (Finset.mem_insert_of_mem hj)
    let U := ⋃ j ∈ s, K j
    have hU : IsCompact U := s.isCompact_biUnion hks
    let := relative_compact_chart_high_degree_vanishing n hn (e i) (K i) hki hsi
    let : Subsingleton (integralRelativeHomology n Uᶜ) := ih K hks hss n hn
    let : Subsingleton (integralRelativeHomology (n + 1) ((K i)ᶜ ∪ Uᶜ)) := by
      rw [← compl_inter]
      have h := ih (fun j => K i ∩ K j)
        (fun j hj => hki.inter (hks j hj))
        (fun j hj => inter_subset_right.trans (hss j hj)) (n + 1) (by omega)
      simpa only [U, inter_iUnion] using h
    have h : Subsingleton (integralRelativeHomology n (K i ∪ U)ᶜ) := by
      rw [compl_union]
      exact ⟨fun a b => relative_homology_inter_eq_of_restrictions_eq n (K i)ᶜ Uᶜ
        hki.isClosed.isOpen_compl hU.isClosed.isOpen_compl a b
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, U] using h

theorem integralRelativeHomology_subsingleton_of_finrank_lt
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E < n) (K : Set X) (hK : IsCompact K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  classical
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  have hlocal (x : K) : ∃ C : Set X, IsCompact C ∧ x.val ∈ interior C ∧
      C ⊆ (chartAt E x.val).source := by
    obtain ⟨C, hC, hxC, hCs⟩ := exists_compact_between isCompact_singleton
      (chartAt E x.val).open_source (singleton_subset_iff.mpr (mem_chart_source E x.val))
    exact ⟨C, hC, hxC (mem_singleton _), hCs⟩
  choose C hC hxC hCs using hlocal
  have hcover : K ⊆ ⋃ x : K, interior (C x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxC _⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (C x))
    (fun _ => isOpen_interior) hcover
  have hEq : (⋃ x ∈ s, K ∩ C x) = K := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun _ _ => inter_subset_left
    · intro x hx
      rcases mem_iUnion₂.mp (hs hx) with ⟨y, hy, hxy⟩
      exact mem_iUnion₂.mpr ⟨y, hy, hx, interior_subset hxy⟩
  have h := relative_finite_chart_union_high_degree_vanishing s
    (fun x : K => chartAt E x.val) (fun x => K ∩ C x)
    (fun x _ => hK.inter (hC x)) (fun x _ => inter_subset_right.trans (hCs x)) n hn
  rwa [hEq] at h

end DifferentialGeometry.Topology

end

end


section

open Set Module

universe u

namespace DifferentialGeometry.Topology

private theorem relative_restriction_union_eq_zero
    {X : Type u} [TopologicalSpace X] (n : ℕ) (K A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B)
    [Subsingleton (integralRelativeHomology (n + 1) (A ∩ B)ᶜ)]
    (hAK : A ⊆ K) (hBK : B ⊆ K) (a : integralRelativeHomology n Kᶜ)
    (ha : integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ Aᶜ from compl_subset_compl.mpr hAK) a = 0)
    (hb : integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ Bᶜ from compl_subset_compl.mpr hBK) a = 0) :
    integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ (A ∪ B)ᶜ from compl_subset_compl.mpr (union_subset hAK hBK)) a = 0 := by
  let hKU : MapsTo (ContinuousMap.id X) Kᶜ (A ∪ B)ᶜ :=
    compl_subset_compl.mpr (union_subset hAK hBK)
  let hUA : MapsTo (ContinuousMap.id X) (A ∪ B)ᶜ Aᶜ :=
    compl_subset_compl.mpr subset_union_left
  let hUB : MapsTo (ContinuousMap.id X) (A ∪ B)ᶜ Bᶜ :=
    compl_subset_compl.mpr subset_union_right
  let b := integralRelativeHomologyMap n (ContinuousMap.id X) hKU a
  have hbA : integralRelativeHomologyMap n (ContinuousMap.id X) hUA b = 0 := by
    have h := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X) hKU hUA) a
    exact h.symm.trans ha
  have hbB : integralRelativeHomologyMap n (ContinuousMap.id X) hUB b = 0 := by
    have h := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X) hKU hUB) a
    exact h.symm.trans hb
  let : Subsingleton (integralRelativeHomology (n + 1) (Aᶜ ∪ Bᶜ)) := by
    rw [← compl_inter]
    infer_instance
  have aux (C : Set X) (hC : C = Aᶜ ∩ Bᶜ)
      (hCA : MapsTo (ContinuousMap.id X) C Aᶜ)
      (hCB : MapsTo (ContinuousMap.id X) C Bᶜ) (c : integralRelativeHomology n C)
      (hcA : integralRelativeHomologyMap n (ContinuousMap.id X) hCA c = 0)
      (hcB : integralRelativeHomologyMap n (ContinuousMap.id X) hCB c = 0) : c = 0 := by
    subst C
    apply relative_homology_inter_eq_of_restrictions_eq n Aᶜ Bᶜ
      hA.isOpen_compl hB.isOpen_compl c 0
    · simpa only [map_zero] using hcA
    · simpa only [map_zero] using hcB
  exact aux (A ∪ B)ᶜ (compl_union A B) hUA hUB b hbA hbB

end DifferentialGeometry.Topology

end


section

open Set

universe u

namespace DifferentialGeometry.Topology

private theorem relative_compact_class_eq_zero_of_compact_vanishing
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K : Set X) (hK : IsCompact K)
    (hvan : ∀ L : Set X, IsCompact L → L ⊆ K →
      Subsingleton (integralRelativeHomology (n + 1) Lᶜ))
    (a : integralRelativeHomology n Kᶜ)
    (ha : ∀ x (hx : x ∈ K), integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = 0) : a = 0 := by
  have hp : ∃ (L : Set X) (hLK : L ⊆ K), IsCompact L ∧ K ⊆ L ∧
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK) a = 0 := by
    apply hK.induction_on (p := fun S => ∃ (L : Set X) (hLK : L ⊆ K),
      IsCompact L ∧ S ⊆ L ∧ integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK) a = 0)
    · let : Subsingleton (integralRelativeHomology n (∅ : Set X)ᶜ) := by
        simpa only [compl_empty] using integralRelativeHomology_univ_subsingleton (X := X) n
      exact ⟨∅, empty_subset K, isCompact_empty, subset_rfl, Subsingleton.elim _ _⟩
    · intro S T hST hT
      obtain ⟨L, hLK, hL, hTL, haL⟩ := hT
      exact ⟨L, hLK, hL, hST.trans hTL, haL⟩
    · intro S T hS hT
      obtain ⟨L, hLK, hL, hSL, haL⟩ := hS
      obtain ⟨N, hNK, hN, hTN, haN⟩ := hT
      let : Subsingleton (integralRelativeHomology (n + 1) (L ∩ N)ᶜ) :=
        hvan (L ∩ N) (hL.inter hN) (inter_subset_left.trans hLK)
      exact ⟨L ∪ N, union_subset hLK hNK, hL.union hN, union_subset_union hSL hTN,
        relative_restriction_union_eq_zero n K L N hL.isClosed hN.isClosed hLK hNK a haL haN⟩
    · intro x hx
      obtain ⟨L, hL, hxL, _, haL⟩ := exists_compact_neighborhood_relative_restriction_eq_zero
        n K univ x hx isOpen_univ (mem_univ x) a (ha x hx)
      refine ⟨K ∩ interior L, inter_mem_nhdsWithin K (isOpen_interior.mem_nhds hxL),
        K ∩ L, inter_subset_left, hK.inter hL, ?_, haL⟩
      exact inter_subset_inter_right K interior_subset
  obtain ⟨L, hLK, _, hKL, haL⟩ := hp
  have hLK' : L = K := subset_antisymm hLK hKL
  subst L
  rw [integralRelativeHomologyMap_id] at haL
  exact haL

end DifferentialGeometry.Topology

end


section

open Set Module

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomology_eq_zero_of_local_restrictions
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (K : Set X) (hK : IsCompact K)
    (a : integralRelativeHomology n Kᶜ)
    (ha : ∀ x (hx : x ∈ K), integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = 0) : a = 0 := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  exact relative_compact_class_eq_zero_of_compact_vanishing n K hK
    (fun L hL _ => integralRelativeHomology_subsingleton_of_finrank_lt
      (E := E) (n + 1) (by omega) L hL) a ha

theorem integralRelativeHomology_eq_of_local_restrictions
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (K : Set X) (hK : IsCompact K)
    (a b : integralRelativeHomology n Kᶜ)
    (hab : ∀ x (hx : x ∈ K), integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Kᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) b) : a = b := by
  apply sub_eq_zero.mp
  apply integralRelativeHomology_eq_zero_of_local_restrictions
    (E := E) n hn K hK (a - b)
  intro x hx
  rw [map_sub, hab x hx, sub_self]

theorem exists_nonzero_local_restriction_of_compact
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (K : Set X) (hK : IsCompact K)
    (a : integralRelativeHomology n Kᶜ) (ha : a ≠ 0) :
    ∃ (x : X) (hx : x ∈ K), integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a ≠ 0 := by
  by_contra h
  apply ha
  apply integralRelativeHomology_eq_zero_of_local_restrictions (E := E) n hn K hK a
  intro x hx
  by_contra hxa
  exact h ⟨x, hx, hxa⟩

end DifferentialGeometry.Topology

end


section

open Set Module

universe u

namespace DifferentialGeometry.Topology

private theorem relative_local_restriction_comp
    {X : Type u} [TopologicalSpace X] (n : ℕ) (K L : Set X) (hLK : L ⊆ K)
    (x : X) (hx : x ∈ L) (a : integralRelativeHomology n Kᶜ) :
    integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr (hLK hx))) a =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Lᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (singleton_subset_iff.mpr hx))
        (integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK) a) :=
  LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id X) (ContinuousMap.id X)
    (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK)
    (show Lᶜ ⊆ ({x}ᶜ : Set X) from
      compl_subset_compl.mpr (singleton_subset_iff.mpr hx))) a

theorem exists_unique_compact_class_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (K : Set X) (hK : IsCompact K)
    (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x ∈ K, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ K ∩ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy.2)) a = μ y) :
    ∃! a : integralRelativeHomology n Kᶜ, ∀ x (hx : x ∈ K),
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Kᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = μ x := by
  have hp : ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧ L ⊆ K ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ x (hx : x ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({x}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = μ x := by
    apply hK.induction_on (p := fun S => ∃ L : Set X, IsCompact L ∧ S ⊆ L ∧ L ⊆ K ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ x (hx : x ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({x}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = μ x)
    · exact ⟨∅, isCompact_empty, subset_rfl, empty_subset K, 0, fun _ hx => hx.elim⟩
    · intro S T hST hT
      obtain ⟨L, hL, hTL, hLK, a, ha⟩ := hT
      exact ⟨L, hL, hST.trans hTL, hLK, a, ha⟩
    · intro S T hS hT
      obtain ⟨A, hA, hSA, hAK, a, ha⟩ := hS
      obtain ⟨B, hB, hTB, hBK, b, hb⟩ := hT
      let hAI : MapsTo (ContinuousMap.id X) Aᶜ (A ∩ B)ᶜ :=
        compl_subset_compl.mpr inter_subset_left
      let hBI : MapsTo (ContinuousMap.id X) Bᶜ (A ∩ B)ᶜ :=
        compl_subset_compl.mpr inter_subset_right
      have hab : integralRelativeHomologyMap n (ContinuousMap.id X) hAI a =
          integralRelativeHomologyMap n (ContinuousMap.id X) hBI b := by
        apply integralRelativeHomology_eq_of_local_restrictions
          (E := E) n hn (A ∩ B) (hA.inter hB)
        intro x hx
        calc
          integralRelativeHomologyMap n (ContinuousMap.id X)
              (show (A ∩ B)ᶜ ⊆ ({x}ᶜ : Set X) from
                compl_subset_compl.mpr (singleton_subset_iff.mpr hx))
              (integralRelativeHomologyMap n (ContinuousMap.id X) hAI a) =
              integralRelativeHomologyMap n (ContinuousMap.id X)
                (show Aᶜ ⊆ ({x}ᶜ : Set X) from
                  compl_subset_compl.mpr (singleton_subset_iff.mpr hx.1)) a :=
            (relative_local_restriction_comp n A (A ∩ B) inter_subset_left x hx a).symm
          _ = μ x := ha x hx.1
          _ = integralRelativeHomologyMap n (ContinuousMap.id X)
              (show Bᶜ ⊆ ({x}ᶜ : Set X) from
                compl_subset_compl.mpr (singleton_subset_iff.mpr hx.2)) b := (hb x hx.2).symm
          _ = integralRelativeHomologyMap n (ContinuousMap.id X)
              (show (A ∩ B)ᶜ ⊆ ({x}ᶜ : Set X) from
                compl_subset_compl.mpr (singleton_subset_iff.mpr hx))
              (integralRelativeHomologyMap n (ContinuousMap.id X) hBI b) :=
            relative_local_restriction_comp n B (A ∩ B) inter_subset_right x hx b
      obtain ⟨c, hcA, hcB⟩ := exists_relative_homology_union_class n A B
        hA.isClosed hB.isClosed a b hab
      refine ⟨A ∪ B, hA.union hB, union_subset_union hSA hTB, union_subset hAK hBK, c, ?_⟩
      intro x hx
      rcases hx with hx | hx
      · calc
          integralRelativeHomologyMap n (ContinuousMap.id X) _ c =
              integralRelativeHomologyMap n (ContinuousMap.id X)
                (show Aᶜ ⊆ ({x}ᶜ : Set X) from
                  compl_subset_compl.mpr (singleton_subset_iff.mpr hx))
                (integralRelativeHomologyMap n (ContinuousMap.id X)
                  (show (A ∪ B)ᶜ ⊆ Aᶜ from compl_subset_compl.mpr subset_union_left) c) :=
            relative_local_restriction_comp n (A ∪ B) A subset_union_left x hx c
          _ = μ x := by rw [hcA]; exact ha x hx
      · calc
          integralRelativeHomologyMap n (ContinuousMap.id X) _ c =
              integralRelativeHomologyMap n (ContinuousMap.id X)
                (show Bᶜ ⊆ ({x}ᶜ : Set X) from
                  compl_subset_compl.mpr (singleton_subset_iff.mpr hx))
                (integralRelativeHomologyMap n (ContinuousMap.id X)
                  (show (A ∪ B)ᶜ ⊆ Bᶜ from compl_subset_compl.mpr subset_union_right) c) :=
            relative_local_restriction_comp n (A ∪ B) B subset_union_right x hx c
          _ = μ x := by rw [hcB]; exact hb x hx
    · intro x hx
      obtain ⟨L, hL, hxL, a, ha⟩ := hlocal x hx
      refine ⟨K ∩ interior L, inter_mem_nhdsWithin K (isOpen_interior.mem_nhds hxL),
        K ∩ L, hK.inter hL, inter_subset_inter_right K interior_subset, inter_subset_left,
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ (K ∩ L)ᶜ from compl_subset_compl.mpr inter_subset_right) a, ?_⟩
      intro y hy
      exact (relative_local_restriction_comp n L (K ∩ L) inter_subset_right y hy a).symm.trans
        (ha y hy)
  obtain ⟨L, _, hKL, hLK, a, ha⟩ := hp
  have hLK' : L = K := subset_antisymm hLK hKL
  subst L
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact integralRelativeHomology_eq_of_local_restrictions (E := E) n hn K hK b a
    (fun x hx => (hb x hx).trans (ha x hx).symm)

end DifferentialGeometry.Topology

end
