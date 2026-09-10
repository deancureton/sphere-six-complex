/-
Adapted from plby/HopfProblem, Solution.lean, lines 1511–1586 and 164521–164621,
commit 9ac8a456b526527837d7082ff775213ca8bc9809 (Apache-2.0):
https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean
Changes: focused imports, namespace and formatting.
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

noncomputable section

open Set Function Manifold
open scoped ContDiff

namespace SphereSixComplex.Analysis.HolomorphicCousin

theorem exists_smoothPartitionOfUnity_normalized_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          closure V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                Set.EqOn (ρ i₀) (fun _ ↦ 1) (closure V) ∧
                  ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) (closure V) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hVo, hKV, hVU⟩ := normal_exists_closure_subset hK (hUo i₀) hKU
  let W : ι → Set M := fun i ↦ if i = i₀ then U i else U i \ closure V
  have hWo (i : ι) : IsOpen (W i) := by
    by_cases hi : i = i₀
    · simpa only [W, ite_eq_left hi] using hUo i
    · simpa only [W, ite_eq_right hi] using (hUo i).sdiff isClosed_closure
  have hWc : Set.univ ⊆ ⋃ i, W i := by
    intro x hx
    by_cases hxV : x ∈ closure V
    · apply Set.mem_iUnion_of_mem i₀
      simpa only [W, ite_eq_left rfl] using hVU hxV
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUc hx)
      apply Set.mem_iUnion_of_mem i
      by_cases hi : i = i₀
      · simpa only [W, ite_eq_left hi] using hxi
      · simpa only [W, ite_eq_right hi, Set.mem_sdiff] using And.intro hxi hxV
  obtain ⟨ρ, hρW⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W hWo hWc
  have hρU : ρ.IsSubordinate U := by
    intro i x hx
    have hxi := hρW i hx
    by_cases hi : i = i₀
    · simpa only [W, ite_eq_left hi] using hxi
    · exact (show x ∈ U i \ closure V by simpa only [W, ite_eq_right hi] using hxi).1
  have hdisjoint (i : ι) (hi : i ≠ i₀) : Disjoint (tsupport (ρ i)) (closure V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hxi : x ∈ U i \ closure V := by simpa only [W, ite_eq_right hi] using hρW i hx
    exact hxi.2 hxV
  have hzero (x : M) (hx : x ∈ closure V) (i : ι) (hi : i ≠ i₀) : ρ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs ↦ Set.disjoint_left.mp (hdisjoint i hi) hs hx
  refine ⟨V, hVo, hKV, hVU, ρ, hρU, ?_, hdisjoint⟩
  intro x hx
  exact
    (finsum_eq_single (fun i ↦ ρ i x) i₀ (hzero x hx)).symm.trans (ρ.sum_eq_one (Set.mem_univ x))

theorem exists_smoothPartitionOfUnity_eq_one_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                (∀ x ∈ V, ρ i₀ x = 1) ∧
                  (∀ i, i ≠ i₀ → ∀ x ∈ V, ρ i x = 0) ∧
                    ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) V := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρU, hρone, hρdisjoint⟩ :=
    exists_smoothPartitionOfUnity_normalized_near_closed I U hUo hUc i₀ hK hKU
  refine ⟨V, hVo, hKV, subset_closure.trans hVU, ρ, hρU, ?_, ?_, ?_⟩
  · intro x hx
    exact hρone (subset_closure hx)
  · intro i hi x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs ↦ Set.disjoint_left.mp (hρdisjoint i hi) hs (subset_closure hx)
  · intro i hi
    exact (hρdisjoint i hi).mono_right subset_closure

def partitionCochain {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : SmoothPartitionOfUnity ι I M Set.univ) (h : ι → ι → M → F) (i : ι) (x : M) : F :=
  ∑ᶠ k, ρ k x • h i k x

theorem mem_cover_of_mem_finsupport {ι E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ}
    (hρ : ρ.IsSubordinate U) {x : M} {k : ι} (hk : k ∈ ρ.finsupport x) : x ∈ U k := by
  apply hρ k
  apply subset_tsupport
  simpa only [ρ.mem_finsupport, Function.mem_support] using hk

theorem partitionCochain_contMDiffOn {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F} (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j)) (i : ι) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (partitionCochain ρ h i) (U i) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply ρ.contMDiffAt_finsum
  intro k hk
  exact (hh i k).contMDiffAt ((hU i).inter (hU k) |>.mem_nhds ⟨hx, hρ k hk⟩)

theorem partitionCochain_sub_eq {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U) {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) :
    partitionCochain ρ h i x - partitionCochain ρ h j x = h i j x := by
  classical
  unfold partitionCochain
  rw [← ρ.sum_finsupport_smul_eq_finsum x (h i), ← ρ.sum_finsupport_smul_eq_finsum x (h j), ←
    Finset.sum_sub_distrib]
  calc
    (∑ k ∈ ρ.finsupport x, (ρ k x • h i k x - ρ k x • h j k x)) =
        ∑ k ∈ ρ.finsupport x, ρ k x • h i j x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← smul_sub,
        sub_eq_iff_eq_add.mpr (hc i j k x hi hj (mem_cover_of_mem_finsupport hρ hk)).symm]
    _ = (∑ k ∈ ρ.finsupport x, ρ k x) • h i j x := (Finset.sum_smul ..).symm
    _ = h i j x := by rw [ρ.sum_finsupport x (Set.mem_univ x), one_smul]

theorem partitionCochain_eq_zero_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (j : ι) {x : M}
    (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) : partitionCochain ρ h j x = 0 := by
  have hdiag : h j j x = 0 := add_eq_left.mp (hc j j j x hj hj hj)
  have hz : ∀ k, ρ k x • h j k x = 0 := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [hdiag, smul_zero]
    · rw [hρ0 k hkj, zero_smul]
  simp only [partitionCochain, hz, finsum_zero]

theorem partitionCochain_eq_overlap_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) :
    partitionCochain ρ h i x = h i j x := by
  have he := partitionCochain_sub_eq hρ hc i j hi hj
  rwa [partitionCochain_eq_zero_of_weights_single hc j hj hρ0, sub_zero] at he

theorem exists_normalized_smooth_cocycle_cochain {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i₀ : ι)
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ (V : Set M) (s : ι → M → F),
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            (∀ i, ContMDiffOn I 𝓘(ℝ, F) ∞ (s i) (U i)) ∧
              (∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x) ∧
                Set.EqOn (s i₀) (fun _ ↦ 0) V ∧ ∀ i, Set.EqOn (s i) (h i i₀) (U i ∩ V) := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρ, _, hρ0, _⟩ :=
    exists_smoothPartitionOfUnity_eq_one_near_closed I U hU
      (fun x _ ↦ Set.mem_iUnion.mpr (hcover x)) i₀ hK hKU
  refine
    ⟨V, partitionCochain ρ h, hVo, hKV, hVU, partitionCochain_contMDiffOn hU hρ hh,
      fun i j _ hi hj ↦ partitionCochain_sub_eq hρ hc i j hi hj, ?_, ?_⟩
  · intro x hx
    exact partitionCochain_eq_zero_of_weights_single hc i₀ (hVU hx) (fun k hk ↦ hρ0 k hk x hx)
  · intro i x hx
    exact
      partitionCochain_eq_overlap_of_weights_single hρ hc i i₀ hx.1 (hVU hx.2)
        (fun k hk ↦ hρ0 k hk x hx.2)

end SphereSixComplex.Analysis.HolomorphicCousin
