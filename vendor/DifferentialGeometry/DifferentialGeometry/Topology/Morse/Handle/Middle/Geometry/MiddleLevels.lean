module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Homology.MiddleHandleHomology
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

section PushOff

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

omit [I.Boundaryless] in
theorem exists_pushOff_chart {m : ℕ} {F : (Fin m → ℝ) → M} (hF : ContinuousOn F (Icc 0 1))
    {A : Set (Fin m → ℝ)} (hA : IsClosed A) {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (G : ∀ i, (Fin (d i) → ℝ) → M) (Ω K : ∀ i, Set (Fin (d i) → ℝ))
    (hΩ : ∀ i ∈ s, IsOpen (Ω i)) (hK : ∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ Ω i)
    (hG : ∀ i ∈ s, ContMDiffOn 𝓘(ℝ, Fin (d i) → ℝ) I 1 (G i) (Ω i)) (hdim : ∀ i ∈ s, d i + m < n)
    (hAC : ∀ y ∈ A ∩ Icc 0 1, ∀ i ∈ s, F y ∉ G i '' K i) {U : Set M} (hU : IsOpen U)
    (hFU : MapsTo F (Icc 0 1) U) (x₀ : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (extChartAt I x₀ x₀) (2 * r) ⊆ (extChartAt I x₀).target)
    (hballU : (extChartAt I x₀).symm '' Metric.closedBall (extChartAt I x₀ x₀) (2 * r) ⊆ U)
    {L : Set (Fin m → ℝ)} (hL : IsClosed L)
    (hLavoid : ∀ y ∈ L ∩ Icc 0 1, ∀ i ∈ s, F y ∉ G i '' K i) :
    ∃ Hm : ℝ → (Fin m → ℝ) → M, ContinuousOn (fun p : ℝ × (Fin m → ℝ) => Hm p.1 p.2)
        (Icc 0 1 ×ˢ Icc 0 1) ∧ (∀ y, Hm 0 y = F y) ∧ (∀ t y, y ∈ A → Hm t y = F y) ∧
      (∀ t y, (F y ∉ (extChartAt I x₀).source ∨
        2 * r ≤ dist (extChartAt I x₀ (F y)) (extChartAt I x₀ x₀)) → Hm t y = F y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Icc 0 1) U) ∧
      ∀ y ∈ Icc (0 : Fin m → ℝ) 1, (y ∈ L ∨ (F y ∈ (extChartAt I x₀).source ∧
        dist (extChartAt I x₀ (F y)) (extChartAt I x₀ x₀) ≤ r)) → ∀ i ∈ s, Hm 1 y ∉ G i '' K i := by
  classical
  have _hUopen : IsOpen U := hU
  set e := extChartAt I x₀ with he
  set z₀ : Fin n → ℝ := e x₀ with hz₀
  have hsrc : IsOpen e.source := isOpen_extChartAt_source x₀
  have heC : ContinuousOn e e.source := continuousOn_extChartAt x₀
  have hsymmC : ContinuousOn e.symm e.target := continuousOn_extChartAt_symm x₀
  have hTgt : ∀ z, dist z z₀ ≤ 2 * r → z ∈ e.target := fun z hz =>
    hball (Metric.mem_closedBall.2 hz)
  let V : ℝ → Set M := fun ρ => e.source ∩ e ⁻¹' Metric.ball z₀ ρ
  let T : ℝ → Set M := fun ρ => e.source ∩ e ⁻¹' Metric.closedBall z₀ ρ
  have hVopen : ∀ ρ, IsOpen (V ρ) := fun ρ => isOpen_extChartAt_preimage' x₀ Metric.isOpen_ball
  have hTcpt : ∀ ρ, ρ ≤ 2 * r → IsCompact (T ρ) := by
    intro ρ hρ
    have hsub : Metric.closedBall z₀ ρ ⊆ e.target := fun z hz =>
      hTgt z ((Metric.mem_closedBall.1 hz).trans hρ)
    have heq : T ρ = e.symm '' Metric.closedBall z₀ ρ := by
      ext p
      constructor
      · rintro ⟨hp, hpb⟩
        exact ⟨e p, hpb, e.left_inv hp⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨e.map_target (hsub hz), ?_⟩
        change e (e.symm z) ∈ Metric.closedBall z₀ ρ
        rw [e.right_inv (hsub hz)]
        exact hz
    rw [heq]
    exact (isCompact_closedBall z₀ ρ).image_of_continuousOn (hsymmC.mono hsub)
  have hTclosed : ∀ ρ, ρ ≤ 2 * r → IsClosed (T ρ) := fun ρ hρ => (hTcpt ρ hρ).isClosed
  have hVT : ∀ ρ ρ', ρ ≤ ρ' → V ρ ⊆ T ρ' := fun ρ ρ' h p hp =>
    ⟨hp.1, Metric.mem_closedBall.2 ((le_of_lt (Metric.mem_ball.1 hp.2)).trans h)⟩
  have hTV : ∀ ρ ρ', ρ < ρ' → T ρ ⊆ V ρ' := fun ρ ρ' h p hp =>
    ⟨hp.1, Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hp.2) h)⟩
  have hTT : ∀ ρ ρ', ρ ≤ ρ' → T ρ ⊆ T ρ' := fun ρ ρ' h p hp =>
    ⟨hp.1, Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hp.2).trans h)⟩
  set C : Set M := ⋃ i ∈ s, G i '' K i with hC
  have hCcpt : IsCompact C := s.isCompact_biUnion fun i hi =>
    (hK i hi).1.image_of_continuousOn ((hG i hi).continuousOn.mono (hK i hi).2)
  have hCclosed : IsClosed C := hCcpt.isClosed
  have hmemC : ∀ p, p ∈ C ↔ ∃ i ∈ s, p ∈ G i '' K i := by
    intro p
    simp only [hC, mem_iUnion, exists_prop]
  set C' : Set (Fin n → ℝ) := Metric.closedBall z₀ (2 * r) ∩ e.symm ⁻¹' C with hC'
  have hC'closed : IsClosed C' :=
    (hsymmC.mono hball).preimage_isClosed_of_isClosed Metric.isClosed_closedBall hCclosed
  set Q : Set (Fin m → ℝ) := Icc 0 1 with hQ
  have hQcpt : IsCompact Q := isCompact_Icc
  set eF : (Fin m → ℝ) → (Fin n → ℝ) := fun y => e (F y) with heF
  set S₂ : Set (Fin m → ℝ) := Q ∩ F ⁻¹' T (7 * r / 4) with hS₂
  have hS₂closed : IsClosed S₂ :=
    hF.preimage_isClosed_of_isClosed isClosed_Icc (hTclosed _ (by linarith))
  have hS₂cpt : IsCompact S₂ := hQcpt.of_isClosed_subset hS₂closed inter_subset_left
  have heFcont : ContinuousOn eF S₂ :=
    heC.comp (hF.mono inter_subset_left) (fun y hy => hy.2.1)
  set J : Set (Fin n → ℝ) := eF '' ((A ∪ L) ∩ S₂) with hJ
  have hJcpt : IsCompact J :=
    (hS₂cpt.of_isClosed_subset ((hA.union hL).inter hS₂closed)
      inter_subset_right).image_of_continuousOn (heFcont.mono inter_subset_right)
  have hJC' : Disjoint J C' := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, ⟨hyAL, hyS⟩, rfl⟩ ⟨_, hyC⟩
    have hFy : e.symm (eF y) = F y := e.left_inv hyS.2.1
    have hmem : F y ∈ C := by rw [← hFy]; exact hyC
    rw [hmemC] at hmem
    obtain ⟨i, hi, hiK⟩ := hmem
    rcases hyAL with hyA | hyL
    · exact hAC y ⟨hyA, hyS.1⟩ i hi hiK
    · exact hLavoid y ⟨hyL, hyS.1⟩ i hi hiK
  obtain ⟨δ, hδ, hdisj⟩ := hJC'.exists_cthickenings hJcpt hC'closed
  have hJfar : ∀ a ∈ J, ∀ c ∈ C', δ < dist a c := by
    intro a ha c hc
    by_contra hlt
    push Not at hlt
    exact Set.disjoint_left.1 hdisj
      (Metric.mem_cthickening_of_dist_le c a δ J ha (by rwa [dist_comm]))
      (Metric.self_subset_cthickening C' hc)
  set S₁ : Set (Fin m → ℝ) := Q ∩ F ⁻¹' T r with hS₁
  have hS₁closed : IsClosed S₁ :=
    hF.preimage_isClosed_of_isClosed isClosed_Icc (hTclosed _ (by linarith))
  have hS₁S₂ : S₁ ⊆ S₂ := fun y hy => ⟨hy.1, hTT _ _ (by linarith) hy.2⟩
  set X₁ : Set (Fin m → ℝ) := S₁ ∩ eF ⁻¹' Metric.cthickening δ C' with hX₁
  have hX₁closed : IsClosed X₁ :=
    (heFcont.mono hS₁S₂).preimage_isClosed_of_isClosed hS₁closed Metric.isClosed_cthickening
  set X₀ : Set (Fin m → ℝ) := A ∪ (Q ∩ F ⁻¹' (V (3 * r / 2))ᶜ) with hX₀
  have hX₀closed : IsClosed X₀ :=
    hA.union (hF.preimage_isClosed_of_isClosed isClosed_Icc (hVopen _).isClosed_compl)
  have hX₀₁ : Disjoint X₀ X₁ := by
    rw [Set.disjoint_left]
    rintro y hy0 ⟨hy1, hyth⟩
    rcases hy0 with hyA | ⟨_, hyV⟩
    · have hJy : eF y ∈ J := ⟨y, ⟨Or.inl hyA, hS₁S₂ hy1⟩, rfl⟩
      exact Set.disjoint_left.1 hdisj (Metric.self_subset_cthickening J hJy) hyth
    · exact hyV (hTV _ _ (by linarith) hy1.2)
  obtain ⟨lam, hlam0, hlam1, hlamI⟩ :=
    exists_continuous_zero_one_of_isClosed hX₀closed hX₁closed hX₀₁
  set ε : ℝ := min (δ / 2) (r / 8) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : 2 * ε ≤ δ := by have := min_le_left (δ / 2) (r / 8); linarith
  have hεr : 2 * ε ≤ r / 4 := by have := min_le_right (δ / 2) (r / 8); linarith
  have hSW : ∀ (S : Set (Fin m → ℝ)), IsCompact S → ∀ g : (Fin m → ℝ) → ℝ, ContinuousOn g S →
      ∀ η : ℝ, 0 < η → ∃ Φ : (Fin m → ℝ) → ℝ, ContDiff ℝ 1 Φ ∧ ∀ y ∈ S, |Φ y - g y| < η := by
    intro S hS g hg η hη
    have : CompactSpace S := isCompact_iff_compactSpace.1 hS
    let B : Subalgebra ℝ C(S, ℝ) :=
      { carrier := {h | ∃ Φ : (Fin m → ℝ) → ℝ, ContDiff ℝ 1 Φ ∧ ∀ z : S, h z = Φ z}
        mul_mem' := by
          rintro a b ⟨Φ, hΦ, ha⟩ ⟨Ψ, hΨ, hb⟩
          exact ⟨Φ * Ψ, hΦ.mul hΨ, fun z => by simp [ha z, hb z]⟩
        add_mem' := by
          rintro a b ⟨Φ, hΦ, ha⟩ ⟨Ψ, hΨ, hb⟩
          exact ⟨Φ + Ψ, hΦ.add hΨ, fun z => by simp [ha z, hb z]⟩
        algebraMap_mem' := fun c => ⟨fun _ => c, contDiff_const, fun z => rfl⟩ }
    have hsep : B.SeparatesPoints := by
      intro x y hxy
      have hne : (x : Fin m → ℝ) ≠ y := fun h => hxy (Subtype.ext h)
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ⟨fun z : S => (z : Fin m → ℝ) j,
        ⟨⟨fun z : S => (z : Fin m → ℝ) j, (continuous_apply j).comp continuous_subtype_val⟩,
          ⟨fun y => y j, contDiff_apply ℝ ℝ j, fun z => rfl⟩, rfl⟩, hj⟩
    obtain ⟨h, hh⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints B
      hsep (fun z : S => g z) (continuousOn_iff_continuous_domRestrict.1 hg) η hη
    obtain ⟨Φ, hΦ, hhΦ⟩ := h.2
    refine ⟨Φ, hΦ, fun y hy => ?_⟩
    have := hh ⟨y, hy⟩
    rwa [Real.norm_eq_abs, hhΦ] at this
  have hφex : ∃ φ : (Fin m → ℝ) → (Fin n → ℝ), ContDiff ℝ 1 φ ∧
      ∀ y ∈ S₂, ‖φ y - eF y‖ < ε := by
    have hcoord : ∀ j : Fin n, ∃ Φ : (Fin m → ℝ) → ℝ, ContDiff ℝ 1 Φ ∧
        ∀ y ∈ S₂, |Φ y - eF y j| < ε := fun j =>
      hSW S₂ hS₂cpt (fun y => eF y j) ((continuous_apply j).comp_continuousOn heFcont) ε hεpos
    choose Φ hΦ hΦS using hcoord
    refine ⟨fun y j => Φ j y, contDiff_pi.2 hΦ, fun y hy => ?_⟩
    rw [pi_norm_lt_iff hεpos]
    intro j
    rw [Real.norm_eq_abs]
    exact hΦS j y hy
  obtain ⟨φ, hφ, hφS⟩ := hφex
  let W : ∀ i, Set (Fin (d i) → ℝ) := fun i => Ω i ∩ G i ⁻¹' e.source
  set Bad : Set (Fin n → ℝ) := ⋃ i ∈ (s : Set ι),
      (fun p : (Fin m → ℝ) × (Fin (d i) → ℝ) => e (G i p.2) - φ p.1) '' (S₂ ×ˢ (K i ∩ W i))
    with hBad
  have hvex : ∃ v : Fin n → ℝ, ‖v‖ < ε ∧ v ∉ Bad := by
    rcases s.eq_empty_or_nonempty with hs | ⟨i₀, hi₀⟩
    · refine ⟨0, by simpa using hεpos, ?_⟩
      simp [hBad, hs]
    · have hdimB : dimH Bad < (Module.finrank ℝ (Fin n → ℝ) : ENNReal) := by
        rw [Module.finrank_fin_fun, hBad, dimH_bUnion s.countable_toSet]
        refine lt_of_le_of_lt (iSup₂_le fun i hi => ?_)
          (show ((n - 1 : ℕ) : ENNReal) < n by
            have := hdim i₀ hi₀
            exact_mod_cast (by omega : n - 1 < n))
        have hi' : i ∈ s := hi
        have hWo : IsOpen (W i) :=
          (hG i hi').continuousOn.isOpen_inter_preimage (hΩ i hi') hsrc
        have hGd : ContDiffOn ℝ 1 (e ∘ G i) (W i) :=
          contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_iff_target.1 (hG i hi')).2 x₀)
        calc dimH ((fun p : (Fin m → ℝ) × (Fin (d i) → ℝ) => e (G i p.2) - φ p.1) ''
                (S₂ ×ˢ (K i ∩ W i)))
            ≤ dimH (S₂ ×ˢ (K i ∩ W i)) := by
              apply dimH_image_le_of_locally_lipschitzOn
              intro p hp
              have hcd : ContDiffAt ℝ 1
                  (fun p : (Fin m → ℝ) × (Fin (d i) → ℝ) => e (G i p.2) - φ p.1) p := by
                have h1 : ContDiffAt ℝ 1 (e ∘ G i) p.2 := hGd.contDiffAt (hWo.mem_nhds hp.2.2)
                exact (h1.comp p contDiffAt_snd).sub (hφ.contDiffAt.comp p contDiffAt_fst)
              obtain ⟨K', t, ht, hK'⟩ := hcd.exists_lipschitzOnWith
              exact ⟨K', t, mem_nhdsWithin_of_mem_nhds ht, hK'⟩
          _ ≤ dimH (univ : Set ((Fin m → ℝ) × (Fin (d i) → ℝ))) := dimH_mono (subset_univ _)
          _ = ((m + d i : ℕ) : ENNReal) := by
              rw [Real.dimH_univ_eq_finrank, Module.finrank_prod, Module.finrank_fin_fun,
                Module.finrank_fin_fun]
          _ ≤ ((n - 1 : ℕ) : ENNReal) := by
              have := hdim i hi'
              exact_mod_cast (by omega : m + d i ≤ n - 1)
      obtain ⟨v, hvB, hvb⟩ := (dense_compl_of_dimH_lt_finrank hdimB).exists_mem_open
        Metric.isOpen_ball (Metric.nonempty_ball.2 hεpos : (Metric.ball (0 : Fin n → ℝ) ε).Nonempty)
      exact ⟨v, mem_ball_zero_iff.1 hvb, hvB⟩
  obtain ⟨v, hvε, hvBad⟩ := hvex
  have hdisp : ∀ y ∈ Q, F y ∈ V (7 * r / 4) → ‖φ y + v - eF y‖ < 2 * ε := by
    intro y hy hyV
    have h1 := hφS y ⟨hy, hVT _ _ le_rfl hyV⟩
    calc ‖φ y + v - eF y‖ = ‖(φ y - eF y) + v‖ := by congr 1; abel
      _ ≤ ‖φ y - eF y‖ + ‖v‖ := norm_add_le _ _
      _ < ε + ε := add_lt_add h1 hvε
      _ = 2 * ε := by ring
  have hstep : ∀ y ∈ Q, F y ∈ V (7 * r / 4) → ∀ σ : ℝ, σ ∈ Icc (0 : ℝ) 1 →
      dist (eF y + σ • (φ y + v - eF y)) (eF y) < 2 * ε := by
    intro y hy hyV σ hσ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    calc σ * ‖φ y + v - eF y‖ ≤ 1 * ‖φ y + v - eF y‖ :=
          mul_le_mul_of_nonneg_right hσ.2 (norm_nonneg _)
      _ = ‖φ y + v - eF y‖ := one_mul _
      _ < 2 * ε := hdisp y hy hyV
  have hin : ∀ y ∈ Q, F y ∈ V (7 * r / 4) → ∀ σ : ℝ, σ ∈ Icc (0 : ℝ) 1 →
      dist (eF y + σ • (φ y + v - eF y)) z₀ ≤ 2 * r := by
    intro y hy hyV σ hσ
    have h1 := hstep y hy hyV σ hσ
    have h2 : dist (eF y) z₀ < 7 * r / 4 := hyV.2
    linarith [dist_triangle (eF y + σ • (φ y + v - eF y)) (eF y) z₀]
  have hσI : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, t * lam y ∈ Icc (0 : ℝ) 1 := fun t ht y =>
    ⟨mul_nonneg ht.1 (hlamI y).1, (mul_le_of_le_one_left (hlamI y).1 ht.2).trans (hlamI y).2⟩
  let Hm : ℝ → (Fin m → ℝ) → M := fun t y =>
    if F y ∈ V (7 * r / 4) then e.symm (eF y + (t * lam y) • (φ y + v - eF y)) else F y
  have hHmV : ∀ t y, F y ∈ V (7 * r / 4) →
      Hm t y = e.symm (eF y + (t * lam y) • (φ y + v - eF y)) := fun t y h => ite_eq_left h
  have hHmF : ∀ t y, F y ∉ V (7 * r / 4) → Hm t y = F y := fun t y h => ite_eq_right h
  have hfix : ∀ t y, F y ∈ V (7 * r / 4) → t * lam y = 0 → Hm t y = F y := by
    intro t y h h0
    rw [hHmV t y h, h0, zero_smul, add_zero]
    exact e.left_inv h.1
  refine ⟨Hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hsnd : Tendsto (fun p : ℝ × (Fin m → ℝ) => p.2) (𝓝[Icc 0 1 ×ˢ Q] (t, y)) (𝓝[Q] y) :=
      continuous_snd.continuousWithinAt.tendsto_nhdsWithin (fun p hp => hp.2)
    have hQev : ∀ᶠ p in 𝓝[Icc (0 : ℝ) 1 ×ˢ Q] (t, y), p.2 ∈ Q :=
      hsnd.eventually self_mem_nhdsWithin
    by_cases hyV : F y ∈ V (7 * r / 4)
    · have hVev : ∀ᶠ p in 𝓝[Icc (0 : ℝ) 1 ×ˢ Q] (t, y), F p.2 ∈ V (7 * r / 4) :=
        hsnd.eventually ((hF y hy).preimage_mem_nhdsWithin ((hVopen _).mem_nhds hyV))
      set Wset : Set (ℝ × (Fin m → ℝ)) := Icc 0 1 ×ˢ (Q ∩ F ⁻¹' V (7 * r / 4)) with hWset
      have hWmem : Wset ∈ 𝓝[Icc (0 : ℝ) 1 ×ˢ Q] (t, y) := by
        filter_upwards [self_mem_nhdsWithin, hVev] with p hp hpV
        exact ⟨hp.1, hp.2, hpV⟩
      have hinner : ContinuousOn (fun p : ℝ × (Fin m → ℝ) =>
          eF p.2 + (p.1 * lam p.2) • (φ p.2 + v - eF p.2)) Wset := by
        have hE : ContinuousOn (fun p : ℝ × (Fin m → ℝ) => eF p.2) Wset :=
          heFcont.comp continuousOn_snd (fun p hp => ⟨hp.2.1, hVT _ _ le_rfl hp.2.2⟩)
        have hl : Continuous (fun p : ℝ × (Fin m → ℝ) => p.1 * lam p.2) := by fun_prop
        have hφc : Continuous (fun p : ℝ × (Fin m → ℝ) => φ p.2) :=
          hφ.continuous.comp continuous_snd
        exact hE.add (hl.continuousOn.smul ((hφc.continuousOn.add continuousOn_const).sub hE))
      have hg : ContinuousOn (fun p : ℝ × (Fin m → ℝ) =>
          e.symm (eF p.2 + (p.1 * lam p.2) • (φ p.2 + v - eF p.2))) Wset :=
        hsymmC.comp hinner (fun p hp => hTgt _ (hin p.2 hp.2.1 hp.2.2 _ (hσI p.1 hp.1 p.2)))
      refine ((hg (t, y) ⟨ht, hy, hyV⟩).mono_of_mem_nhdsWithin hWmem).congr_of_eventuallyEq ?_
        (hHmV t y hyV)
      filter_upwards [hVev] with p hpV
      exact hHmV p.1 p.2 hpV
    · have hT : F y ∉ T (3 * r / 2) := fun h => hyV (hTV _ _ (by linarith) h)
      have hTev : ∀ᶠ p in 𝓝[Icc (0 : ℝ) 1 ×ˢ Q] (t, y), F p.2 ∉ T (3 * r / 2) :=
        hsnd.eventually ((hF y hy).preimage_mem_nhdsWithin
          ((hTclosed _ (by linarith)).isOpen_compl.mem_nhds hT))
      have hFc : ContinuousWithinAt (fun p : ℝ × (Fin m → ℝ) => F p.2) (Icc 0 1 ×ˢ Q) (t, y) :=
        (hF y hy).comp continuous_snd.continuousWithinAt (fun p hp => hp.2)
      refine hFc.congr_of_eventuallyEq ?_ (hHmF t y hyV)
      filter_upwards [hTev, hQev] with p hpT hpQ
      by_cases hpV : F p.2 ∈ V (7 * r / 4)
      · have hp0 : lam p.2 = 0 := hlam0 (Or.inr ⟨hpQ, fun h => hpT (hVT _ _ le_rfl h)⟩)
        exact hfix p.1 p.2 hpV (by rw [hp0, mul_zero])
      · exact hHmF p.1 p.2 hpV
  · intro y
    by_cases hyV : F y ∈ V (7 * r / 4)
    · exact hfix 0 y hyV (zero_mul _)
    · exact hHmF 0 y hyV
  · intro t y hyA
    by_cases hyV : F y ∈ V (7 * r / 4)
    · have h0 : lam y = 0 := hlam0 (Or.inl hyA)
      exact hfix t y hyV (by rw [h0, mul_zero])
    · exact hHmF t y hyV
  · intro t y hy
    apply hHmF
    rintro ⟨hsrcy, hdy⟩
    rcases hy with h | h
    · exact h hsrcy
    · have h' : dist (e (F y)) z₀ < 7 * r / 4 := hdy
      linarith
  · intro t ht y hy
    by_cases hyV : F y ∈ V (7 * r / 4)
    · rw [hHmV t y hyV]
      exact hballU ⟨_, Metric.mem_closedBall.2 (hin y hy hyV _ (hσI t ht y)), rfl⟩
    · rw [hHmF t y hyV]
      exact hFU hy
  · intro y hy hyc i hi hGi
    by_cases hyV : F y ∈ V (7 * r / 4)
    · rw [hHmV 1 y hyV, one_mul] at hGi
      set w := eF y + lam y • (φ y + v - eF y) with hw
      have hwb : dist w z₀ ≤ 2 * r := hin y hy hyV (lam y) (hlamI y)
      have hwT : w ∈ e.target := hTgt w hwb
      have hyS₂ : y ∈ S₂ := ⟨hy, hVT _ _ le_rfl hyV⟩
      by_cases hyX : y ∈ X₁
      · have h1 : lam y = 1 := hlam1 hyX
        have hw1 : w = φ y + v := by rw [hw, h1, one_smul]; abel
        obtain ⟨k, hk, hkG⟩ := hGi
        apply hvBad
        refine Set.mem_iUnion₂.2 ⟨i, hi, ⟨(y, k), ⟨hyS₂, hk, (hK i hi).2 hk, ?_⟩, ?_⟩⟩
        · change G i k ∈ e.source
          rw [hkG]
          exact e.map_target hwT
        · change e (G i k) - φ y = v
          rw [hkG, e.right_inv hwT, hw1]
          abel
      · have hwC' : w ∈ C' := ⟨Metric.mem_closedBall.2 hwb, (hmemC _).2 ⟨i, hi, hGi⟩⟩
        have hclose : dist (eF y) w < δ := by
          have := hstep y hy hyV (lam y) (hlamI y)
          rw [dist_comm]
          linarith
        rcases hyc with hyL | ⟨hysrc, hyr⟩
        · have hJy : eF y ∈ J := ⟨y, ⟨Or.inr hyL, hyS₂⟩, rfl⟩
          exact absurd (hJfar _ hJy w hwC') (not_lt.2 hclose.le)
        · apply hyX
          refine ⟨⟨hy, hysrc, Metric.mem_closedBall.2 hyr⟩, ?_⟩
          exact Metric.mem_cthickening_of_dist_le _ w δ C' hwC' hclose.le
    · rw [hHmF 1 y hyV] at hGi
      rcases hyc with hyL | ⟨hysrc, hyr⟩
      · exact hLavoid y ⟨hyL, hy⟩ i hi hGi
      · exact hyV ⟨hysrc, Metric.mem_ball.2 (by linarith)⟩

theorem exists_pushOff {m : ℕ} {F : (Fin m → ℝ) → M} (hF : ContinuousOn F (Icc 0 1))
    {A : Set (Fin m → ℝ)} (hA : IsClosed A) {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (G : ∀ i, (Fin (d i) → ℝ) → M) (Ω K : ∀ i, Set (Fin (d i) → ℝ))
    (hΩ : ∀ i ∈ s, IsOpen (Ω i)) (hK : ∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ Ω i)
    (hG : ∀ i ∈ s, ContMDiffOn 𝓘(ℝ, Fin (d i) → ℝ) I 1 (G i) (Ω i)) (hdim : ∀ i ∈ s, d i + m < n)
    (hAC : ∀ y ∈ A ∩ Icc 0 1, ∀ i ∈ s, F y ∉ G i '' K i) {U : Set M} (hU : IsOpen U)
    (hFU : MapsTo F (Icc 0 1) U) :
    ∃ Hm : ℝ → (Fin m → ℝ) → M, ContinuousOn (fun p : ℝ × (Fin m → ℝ) => Hm p.1 p.2)
        (Icc 0 1 ×ˢ Icc 0 1) ∧ (∀ y, Hm 0 y = F y) ∧ (∀ t y, y ∈ A → Hm t y = F y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Icc 0 1) U) ∧
      ∀ y ∈ Icc (0 : Fin m → ℝ) 1, ∀ i ∈ s, Hm 1 y ∉ G i '' K i := by
  classical
  have hGc : ∀ i ∈ s, ContinuousOn (G i) (K i) := fun i hi =>
    ((hG i hi).continuousOn).mono (hK i hi).2
  have hρex : ∀ p ∈ U, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall (extChartAt I p p) (2 * ρ) ⊆ (extChartAt I p).target ∧
      (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) (2 * ρ) ⊆ U := by
    intro p hp
    have hO : IsOpen ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U) :=
      (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p) hU
    have hcO : extChartAt I p p ∈ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U :=
      ⟨mem_extChartAt_target p, by simpa [extChartAt_to_inv p] using hp⟩
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO _ hcO
    refine ⟨ε / 3, by positivity, ?_, ?_⟩
    · intro z hz
      exact (hεO (Metric.closedBall_subset_ball (by linarith) hz)).1
    · rintro _ ⟨z, hz, rfl⟩
      exact (hεO (Metric.closedBall_subset_ball (by linarith) hz)).2
  choose! ρ hρpos hρball hρU using hρex
  set Hb : M → Set M := fun p => (extChartAt I p).source ∩
    extChartAt I p ⁻¹' Metric.ball (extChartAt I p p) (ρ p / 2) with hHb
  set Q : M → Set M := fun p =>
    (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) (ρ p / 2) with hQ
  have hHbopen : ∀ p, IsOpen (Hb p) := fun p =>
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
      Metric.isOpen_ball
  have hQclosed : ∀ p ∈ U, IsClosed (Q p) := by
    intro p hp
    refine IsCompact.isClosed ?_
    refine (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono ?_)
    refine subset_trans (Metric.closedBall_subset_closedBall ?_) (hρball p hp)
    linarith [hρpos p hp]
  have hHbQ : ∀ p, Hb p ⊆ Q p := by
    intro p x hx
    refine ⟨extChartAt I p x, Metric.ball_subset_closedBall hx.2, ?_⟩
    exact (extChartAt I p).left_inv hx.1
  have hFc : IsCompact (F '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hF
  obtain ⟨T, hTF, hTcov⟩ := hFc.elim_nhds_subcover Hb (fun p hp =>
    (hHbopen p).mem_nhds ⟨mem_extChartAt_source p, by simp [hρpos p (hFU.image_subset hp)]⟩)
  have hTU : ∀ p ∈ T, p ∈ U := fun p hp => hFU.image_subset (hTF p hp)
  set W : Set M := ⋃ p ∈ T, Hb p with hW
  have hWopen : IsOpen W := isOpen_biUnion fun p _ => hHbopen p
  set Tg : Finset M → ∀ i, Set (Fin (d i) → ℝ) := fun S i =>
    K i ∩ G i ⁻¹' ((⋃ p ∈ S, Q p) ∪ Wᶜ) with hTg
  have hTgK : ∀ S : Finset M, (∀ p ∈ S, p ∈ U) → ∀ i ∈ s, IsCompact (Tg S i) ∧ Tg S i ⊆ Ω i := by
    intro S hS i hi
    refine ⟨(hK i hi).1.of_isClosed_subset ?_ inter_subset_left,
      inter_subset_left.trans (hK i hi).2⟩
    refine (hGc i hi).preimage_isClosed_of_isClosed (hK i hi).1.isClosed ?_
    exact (isClosed_biUnion_finset fun p hp => hQclosed p (hS p hp)).union hWopen.isClosed_compl
  have key : ∀ S : Finset M, (∀ p ∈ S, p ∈ U) →
      ∃ Hm : ℝ → (Fin m → ℝ) → M, ContinuousOn (fun p : ℝ × (Fin m → ℝ) => Hm p.1 p.2)
        (Icc 0 1 ×ˢ Icc 0 1) ∧ (∀ y, Hm 0 y = F y) ∧ (∀ t y, y ∈ A → Hm t y = F y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Icc 0 1) U) ∧
      ∀ y ∈ Icc (0 : Fin m → ℝ) 1, ∀ i ∈ s, Hm 1 y ∉ G i '' Tg S i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ y => F y, ?_, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => hFU, ?_⟩
      · exact hF.comp continuousOn_snd (fun q hq => hq.2)
      · rintro y hy i hi ⟨k, hk, hkF⟩
        have hk2 := hk.2
        simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, empty_union,
          mem_preimage, mem_compl_iff] at hk2
        exact hk2 (hkF ▸ hTcov (mem_image_of_mem F hy))
    | insert p S hpS ih =>
      intro hS
      have hpU : p ∈ U := hS p (Finset.mem_insert_self p S)
      obtain ⟨Hm, hHc, hH0, hHA, hHU, hHav⟩ :=
        ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
      set F₁ : (Fin m → ℝ) → M := Hm 1 with hF₁
      have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      have hF₁c : ContinuousOn F₁ (Icc 0 1) :=
        hHc.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨h1, hy⟩)
      have hF₁U : MapsTo F₁ (Icc 0 1) U := hHU 1 h1
      have hF₁A : ∀ y ∈ A ∩ Icc 0 1, ∀ i ∈ s, F₁ y ∉ G i '' Tg (insert p S) i := by
        rintro y hy i hi ⟨k, hk, hkF⟩
        refine hAC y hy i hi ⟨k, hk.1, ?_⟩
        rw [hkF, hF₁, hHA 1 y hy.1]
      set Z : Set M := ((extChartAt I p).source ∩
        extChartAt I p ⁻¹' Metric.ball (extChartAt I p p) (ρ p))ᶜ with hZ
      have hZc : IsClosed Z := isClosed_compl_iff.2
        ((continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
          Metric.isOpen_ball)
      have hLc : IsClosed (Icc (0 : Fin m → ℝ) 1 ∩ F₁ ⁻¹' Z) :=
        hF₁c.preimage_isClosed_of_isClosed isClosed_Icc hZc
      have hLav : ∀ y ∈ (Icc (0 : Fin m → ℝ) 1 ∩ F₁ ⁻¹' Z) ∩ Icc 0 1, ∀ i ∈ s,
          F₁ y ∉ G i '' Tg (insert p S) i := by
        rintro y ⟨⟨hy, hyZ⟩, -⟩ i hi ⟨k, hk, hkF⟩
        have hk2 := hk.2
        simp only [Finset.set_biUnion_insert, mem_preimage, mem_union] at hk2
        rcases hk2 with (hkQ | hkS) | hkW
        · obtain ⟨z, hz, hzk⟩ := hkQ
          have hzt : z ∈ (extChartAt I p).target := hρball p hpU
            (Metric.closedBall_subset_closedBall (by linarith [hρpos p hpU]) hz)
          apply hyZ
          rw [← hkF, ← hzk]
          refine ⟨(extChartAt I p).map_target hzt, ?_⟩
          rw [mem_preimage, (extChartAt I p).right_inv hzt, Metric.mem_ball]
          have := Metric.mem_closedBall.1 hz
          linarith [hρpos p hpU]
        · exact hHav y hy i hi ⟨k, ⟨hk.1, Or.inl hkS⟩, hkF⟩
        · exact hHav y hy i hi ⟨k, ⟨hk.1, Or.inr hkW⟩, hkF⟩
      obtain ⟨Hm', hH'c, hH'0, hH'A, -, hH'U, hH'av⟩ :=
        exists_pushOff_chart hF₁c hA s d G Ω (Tg (insert p S)) hΩ (hTgK _ hS) hG hdim hF₁A hU
          hF₁U p (hρpos p hpU) (hρball p hpU) (hρU p hpU) hLc hLav
      refine ⟨fun t y => if t ≤ 1 / 2 then Hm (2 * t) y else Hm' (2 * t - 1) y, ?_, ?_, ?_, ?_, ?_⟩
      · have e1 : ContinuousOn (fun q : ℝ × (Fin m → ℝ) => Hm (2 * q.1) q.2)
            (Icc 0 (1 / 2) ×ˢ Icc 0 1) :=
          hHc.comp ((continuousOn_const.mul continuousOn_fst).prodMk continuousOn_snd)
            (fun q hq => by
              refine ⟨⟨?_, ?_⟩, hq.2⟩ <;> simp only [Pi.mul_apply] <;>
                linarith [hq.1.1, hq.1.2])
        have e2 : ContinuousOn (fun q : ℝ × (Fin m → ℝ) => Hm' (2 * q.1 - 1) q.2)
            (Icc (1 / 2) 1 ×ˢ Icc 0 1) :=
          hH'c.comp (((continuousOn_const.mul continuousOn_fst).sub continuousOn_const).prodMk
            continuousOn_snd)
            (fun q hq => by
              refine ⟨⟨?_, ?_⟩, hq.2⟩ <;> simp only [Pi.mul_apply, Pi.sub_apply] <;>
                linarith [hq.1.1, hq.1.2])
        refine (ContinuousOn.union_of_isClosed (e1.congr ?_) (e2.congr ?_)
          (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc)).mono ?_
        · intro q hq
          simp only [hq.1.2, ↓reduceIte]
        · intro q hq
          by_cases hq2 : q.1 ≤ 1 / 2
          · have hqe : q.1 = 1 / 2 := le_antisymm hq2 hq.1.1
            simp only [hq2, ↓reduceIte]
            rw [hqe, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
              hH'0, hF₁]
          · simp only [hq2, ↓reduceIte]
        · rintro q ⟨hq1, hq2⟩
          rcases le_total q.1 (1 / 2) with h | h
          · exact Or.inl ⟨⟨hq1.1, h⟩, hq2⟩
          · exact Or.inr ⟨⟨h, hq1.2⟩, hq2⟩
      · intro y
        simp [hH0]
      · intro t y hy
        by_cases ht : t ≤ 1 / 2
        · simp only [ht, ↓reduceIte]
          exact hHA _ y hy
        · simp only [ht, ↓reduceIte]
          rw [hH'A _ y hy, hF₁, hHA 1 y hy]
      · intro t ht y hy
        by_cases ht2 : t ≤ 1 / 2
        · simp only [ht2, ↓reduceIte]
          exact hHU _ ⟨by linarith [ht.1], by linarith⟩ hy
        · simp only [ht2, ↓reduceIte]
          exact hH'U _ ⟨by linarith, by linarith [ht.2]⟩ hy
      · intro y hy i hi
        have hn : ¬ ((1 : ℝ) ≤ 1 / 2) := by norm_num
        simp only [hn, ↓reduceIte]
        rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num]
        refine hH'av y hy ?_ i hi
        by_cases hyZ : F₁ y ∈ Z
        · exact Or.inl ⟨hy, hyZ⟩
        · right
          have hyZ' : F₁ y ∈ (extChartAt I p).source ∩
              extChartAt I p ⁻¹' Metric.ball (extChartAt I p p) (ρ p) := not_not.1 hyZ
          exact ⟨hyZ'.1, (Metric.mem_ball.1 hyZ'.2).le⟩
  obtain ⟨Hm, hHc, hH0, hHA, hHU, hHav⟩ := key T hTU
  refine ⟨Hm, hHc, hH0, hHA, hHU, ?_⟩
  rintro y hy i hi ⟨k, hk, hkF⟩
  refine hHav y hy i hi ⟨k, ⟨hk, ?_⟩, hkF⟩
  by_cases hkW : G i k ∈ W
  · left
    rw [hW, mem_iUnion₂] at hkW
    obtain ⟨q, hq, hkq⟩ := hkW
    exact mem_biUnion hq (hHbQ q hkq)
  · exact Or.inr hkW

end PushOff

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

def sphereUnion (D : GradientLikeStrip I f a b crit) (L R : Finset M) (ε c : ℝ) : Set M :=
  (⋃ (q : M) (hq : q ∈ crit) (_ : q ∈ L), D.leftSphere q hq ε c) ∪
    ⋃ (p : M) (hp : p ∈ crit) (_ : p ∈ R), D.rightSphere p hp ε c

theorem exists_level_pushOff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {ε c κ : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) (hκ : 0 < κ)
    (hcκ : a ≤ c - κ ∧ c + κ ≤ b)
    (hU : ∀ y, f y ∈ Icc (c - κ) (c + κ) → ∀ x hx, y ∉ D.smallBall x hx) (L R : Finset M) {m : ℕ}
    (hL : ∀ q (hq : q ∈ crit), q ∈ L → c + κ < f q - ε ∧ (D.chart q hq).k + m < n)
    (hR : ∀ p (hp : p ∈ crit), p ∈ R → f p + ε < c - κ ∧ n - (D.chart p hp).k + m < n)
    {G : Set M} (hG : IsOpen G) {F : (Fin m → ℝ) → M} (hF : ContinuousOn F (Icc 0 1))
    (hFY : MapsTo F (Icc 0 1) (f ⁻¹' {c} ∩ G)) {A : Set (Fin m → ℝ)} (hA : IsClosed A)
    (hAC : ∀ y ∈ A ∩ Icc 0 1, F y ∉ D.sphereUnion L R ε c) :
    ∃ Hm : ℝ → (Fin m → ℝ) → M, ContinuousOn (fun p : ℝ × (Fin m → ℝ) => Hm p.1 p.2)
        (Icc 0 1 ×ˢ Icc 0 1) ∧ (∀ y, Hm 0 y = F y) ∧ (∀ t y, y ∈ A → Hm t y = F y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Icc 0 1) (f ⁻¹' {c} ∩ G)) ∧
      ∀ y ∈ Icc (0 : Fin m → ℝ) 1, Hm 1 y ∉ D.sphereUnion L R ε c := by
  classical
  have hfc : Continuous f := hf.continuous
  have hcIcc : c ∈ Icc a b := ⟨by linarith [hcκ.1], by linarith [hcκ.2]⟩
  have hcIoo : c ∈ Ioo a b := ⟨by linarith [hcκ.1], by linarith [hcκ.2]⟩
  have hlev : ∀ s : M, f s = c → ∀ σ : ℝ, |σ| ≤ κ → f (D.flow σ s) = c - σ := by
    intro s hs σ hσ
    rw [abs_le] at hσ
    have h := f_flow_eq_sub_of_levels (D := D) hf (x := s) (T := σ)
      (by rw [hs]; exact hcIcc) (by rw [hs]; constructor <;> linarith [hcκ.1, hcκ.2])
      (by
        intro y hy
        apply hU
        rw [hs, mem_uIcc] at hy
        rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith)
      σ right_mem_uIcc
    rw [h, hs]
  have hΩc : ∀ x : M, f x = c → x ∈ D.regularFlowDomain c := by
    intro x hx
    refine ⟨hx ▸ hcIoo, fun s hs p hp hmem => ?_⟩
    rw [hx, sub_self, uIcc_self, mem_singleton_iff] at hs
    rw [hs, flow_zero] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy' : morseNorm n y ≤ (D.chart p hp).r₀ := hy
    have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' :=
      mem_ball_of_morseNorm_lt (hy'.trans_lt (D.r₀_lt_R' p hp))
    have hcont : ContinuousAt (fun t : ℝ => f ((D.chart p hp).χ (t • y))) 1 := by
      have h1 : ContinuousAt (fun t : ℝ => t • y) 1 :=
        (continuous_id.smul continuous_const).continuousAt
      have h2 : ContinuousAt (D.chart p hp).χ ((1 : ℝ) • y) := by
        rw [one_smul]; exact (D.chart p hp).χ.continuousAt ((D.chart p hp).hball hyball)
      exact hfc.continuousAt.comp (ContinuousAt.comp (f := fun t : ℝ => t • y) h2 h1)
    have h1c : f ((D.chart p hp).χ ((1 : ℝ) • y)) = c := by rw [one_smul]; exact hx
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ),
        f ((D.chart p hp).χ (t • y)) ∈ Ioo (c - κ) (c + κ) ∧ t ∈ Ioo 0 1 := by
      refine Filter.Eventually.and ?_ (Ioo_mem_nhdsLT one_pos)
      exact nhdsWithin_le_nhds (hcont.eventually
        (Ioo_mem_nhds
          (by change c - κ < f ((D.chart p hp).χ ((1 : ℝ) • y)); rw [h1c]; linarith)
          (by change f ((D.chart p hp).χ ((1 : ℝ) • y)) < c + κ; rw [h1c]; linarith)))
    obtain ⟨t, ht1, ht2⟩ := hev.exists
    apply hU _ (Ioo_subset_Icc_self ht1) p hp
    refine ⟨t • y, ?_, rfl⟩
    change morseNorm n (t • y) < (D.chart p hp).r₀
    rw [ModelField.morseNorm_smul, abs_of_pos ht2.1]
    have hr₀ := (D.chart p hp).hr₀
    calc t * morseNorm n y ≤ t * (D.chart p hp).r₀ := mul_le_mul_of_nonneg_left hy' ht2.1.le
      _ < (D.chart p hp).r₀ := by nlinarith [ht2.2]
  set U : Set M := D.regularFlowDomain c ∩ D.π c ⁻¹' G ∩ f ⁻¹' Ioo (c - κ / 2) (c + κ / 2) with hUdef
  have hUo : IsOpen U :=
    ((D.isOpen_regularFlowDomain hfc c).inter (hG.preimage (D.continuous_π hf c))).inter
      (isOpen_Ioo.preimage hfc)
  have hFU : MapsTo F (Icc 0 1) U := by
    intro y hy
    obtain ⟨h1, h2⟩ := hFY hy
    have h1' : f (F y) = c := h1
    refine ⟨⟨hΩc _ h1', ?_⟩, ?_⟩
    · change D.π c (F y) ∈ G
      rw [π_eq_self_of_level h1']
      exact h2
    · change f (F y) ∈ Ioo _ _
      rw [h1']
      constructor <;> linarith
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hεr x hx).2
    have h2 := (D.hrm x hx).2
    have h3 := D.rm_pos x hx
    nlinarith
  have gen : ∀ (x : M) (hx : x ∈ crit) (d : ℕ) (ι : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin n → ℝ))
      (S : Set (Fin n → ℝ)) (T : ℝ), S ⊆ Metric.ball 0 (D.chart x hx).R' →
      (∀ y ∈ S, ∃ u, ‖u‖ ^ 2 = 2 * ε ∧ ι u = y) → (∀ u, ‖u‖ ^ 2 = 2 * ε → ι u ∈ S) →
      ∃ (Gi : (Fin d → ℝ) → M) (Ωi Ki : Set (Fin d → ℝ)), IsOpen Ωi ∧ IsCompact Ki ∧ Ki ⊆ Ωi ∧
        ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I 1 Gi Ωi ∧
        (∀ z ∈ Gi '' Ki, ∃ s ∈ D.flow T '' ((D.chart x hx).χ '' S), f s = c ∧
          ∃ σ : ℝ, |σ| ≤ κ / 2 ∧ z = D.flow σ s) ∧
        (∀ s ∈ D.flow T '' ((D.chart x hx).χ '' S), f s = c → ∀ σ : ℝ, |σ| ≤ κ / 2 →
          D.flow σ s ∈ Gi '' Ki) := by
    intro x hx d ι S T hSball hS1 hS2
    set e := EuclideanSpace.equiv (Fin d) ℝ with he
    obtain ⟨ν, hν⟩ : ∃ ν : (Fin d → ℝ) → ℝ, ν = fun w => ‖e.symm w‖ := ⟨_, rfl⟩
    have hνw : ∀ w, ν w = ‖e.symm w‖ := fun w => by rw [hν]
    obtain ⟨P, hP⟩ : ∃ P : (Fin d → ℝ) → Fin n → ℝ,
        P = fun w => ι ((Real.sqrt (2 * ε) / ν w) • e.symm w) := ⟨_, rfl⟩
    have hPw : ∀ w, P w = ι ((Real.sqrt (2 * ε) / ν w) • e.symm w) := fun w => by rw [hP]
    obtain ⟨g, hg⟩ : ∃ g : (Fin d → ℝ) → M, g = fun w => D.flow T ((D.chart x hx).χ (P w)) :=
      ⟨_, rfl⟩
    have hgw : ∀ w, g w = D.flow T ((D.chart x hx).χ (P w)) := fun w => by rw [hg]
    have hsq : Real.sqrt (2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
    have hsqpos : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
    have hν0 : ∀ w : Fin d → ℝ, w ≠ 0 → ν w ≠ 0 := by
      intro w hw
      rw [hνw]
      exact norm_ne_zero_iff.2 (fun h => hw (e.symm.map_eq_zero_iff.1 h))
    have hPS : ∀ w : Fin d → ℝ, w ≠ 0 → P w ∈ S := by
      intro w hw
      rw [hPw]
      apply hS2
      have h0 := hν0 w hw
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, hsq, ← hνw]
      field_simp
    have hνs : ∀ w : Fin d → ℝ, w ≠ 0 → ContDiffAt ℝ ∞ ν w := by
      intro w hw
      rw [hν]
      exact (e.symm.contDiff.contDiffAt).norm ℝ (fun h => hw (e.symm.map_eq_zero_iff.1 h))
    have hPs : ∀ w : Fin d → ℝ, w ≠ 0 → ContDiffAt ℝ ∞ P w := by
      intro w hw
      rw [hP]
      exact ι.contDiff.contDiffAt.comp w
        ((contDiffAt_const.div (hνs w hw) (hν0 w hw)).smul e.symm.contDiff.contDiffAt)
    have hgs : ∀ w : Fin d → ℝ, w ≠ 0 → ContMDiffAt 𝓘(ℝ, Fin d → ℝ) I ∞ g w := by
      intro w hw
      have hχ : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart x hx).χ (P w) :=
        (D.chart x hx).hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds (hSball (hPS w hw)))
      have hPm : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ P w :=
        contMDiffAt_iff_contDiffAt.2 (hPs w hw)
      rw [hg]
      exact (D.contMDiff_flow T _).comp w (hχ.comp w hPm)
    have hGs : ∀ w : Fin d → ℝ, w ≠ 0 →
        ContMDiffAt 𝓘(ℝ, Fin d → ℝ) I ∞ (fun w => D.flow (κ * (ν w - 3 / 2)) (g w)) w := by
      intro w hw
      have ht : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun w => κ * (ν w - 3 / 2)) w :=
        contMDiffAt_iff_contDiffAt.2 (contDiffAt_const.mul ((hνs w hw).sub contDiffAt_const))
      exact D.contMDiff_flow_joint.contMDiffAt.comp (f := fun w => (κ * (ν w - 3 / 2), g w)) w
        (ht.prodMk (hgs w hw))
    have hνc : Continuous ν := by rw [hν]; exact e.symm.continuous.norm
    have hA : IsClosed {w : Fin d → ℝ | ν w ∈ Icc (1 : ℝ) 2} := isClosed_Icc.preimage hνc
    have hne : ∀ w ∈ {w : Fin d → ℝ | ν w ∈ Icc (1 : ℝ) 2}, w ≠ 0 := by
      intro w hw h0
      have h1 := hw.1
      rw [hνw, h0, map_zero, norm_zero] at h1
      linarith
    have hgc : ContinuousOn g {w : Fin d → ℝ | ν w ∈ Icc (1 : ℝ) 2} := fun w hw =>
      (hgs w (hne w hw)).continuousAt.continuousWithinAt
    refine ⟨fun w => D.flow (κ * (ν w - 3 / 2)) (g w), {w | w ≠ 0},
      {w | ν w ∈ Icc (1 : ℝ) 2} ∩ (fun w => f (g w)) ⁻¹' {c}, isOpen_compl_singleton, ?_, fun w hw => hne w hw.1,
      fun w hw => ((hGs w hw).of_le (by norm_num)).contMDiffWithinAt, ?_, ?_⟩
    · have hcl := (hfc.comp_continuousOn hgc).preimage_isClosed_of_isClosed hA (isClosed_singleton (x := c))
      refine ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 2).image
        e.continuous).of_isClosed_subset hcl ?_
      intro w hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [mem_closedBall_zero_iff, ← hνw]
      exact hw.1.2
    · rintro z ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have hw0 := hne w hw1
      refine ⟨g w, ⟨(D.chart x hx).χ (P w), ⟨P w, hPS w hw0, rfl⟩, (hgw w).symm⟩, hw2,
        κ * (ν w - 3 / 2), ?_, rfl⟩
      have h1 := hw1.1
      have h2 := hw1.2
      rw [abs_le]
      constructor <;> nlinarith
    · rintro s ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hs σ hσ
      obtain ⟨u, hu, rfl⟩ := hS1 y hy
      have hun : ‖u‖ = Real.sqrt (2 * ε) := by rw [← hu, Real.sqrt_sq (norm_nonneg u)]
      rw [abs_le] at hσ
      have hτ1 : -(1 / 2) ≤ σ / κ := by rw [le_div_iff₀ hκ]; linarith
      have hτ2 : σ / κ ≤ 1 / 2 := by rw [div_le_iff₀ hκ]; linarith
      set l := (σ / κ + 3 / 2) / ‖u‖ with hl
      have hu0 : ‖u‖ ≠ 0 := by rw [hun]; exact hsqpos.ne'
      have hlpos : 0 < l := by rw [hl, hun]; exact div_pos (by linarith) hsqpos
      set w := e (l • u) with hw
      have hew : e.symm w = l • u := by rw [hw, e.symm_apply_apply]
      have hνw' : ν w = σ / κ + 3 / 2 := by
        rw [hνw, hew, norm_smul, Real.norm_eq_abs, abs_of_pos hlpos, hl]
        field_simp
      have hPw' : P w = ι u := by
        rw [hPw, hew, smul_smul, hνw']
        have : Real.sqrt (2 * ε) / (σ / κ + 3 / 2) * l = 1 := by
          rw [hl, hun]
          field_simp
          exact div_self (by linarith)
        rw [this, one_smul]
      have hgw' : g w = D.flow T ((D.chart x hx).χ (ι u)) := by rw [hgw, hPw']
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · change ν w ∈ Icc (1 : ℝ) 2
        rw [hνw']
        constructor <;> linarith
      · change f (g w) = c
        rw [hgw']
        exact hs
      · change D.flow (κ * (ν w - 3 / 2)) (g w) = D.flow σ (D.flow T ((D.chart x hx).χ (ι u)))
        rw [hνw', hgw']
        congr 1
        field_simp
        ring
  let Ix := {q // q ∈ crit} ⊕ {p // p ∈ crit}
  let dI : Ix → ℕ := Sum.elim (fun q => (D.chart q.1 q.2).k) (fun p => n - (D.chart p.1 p.2).k)
  let Sph : Ix → Set M :=
    Sum.elim (fun q => D.leftSphere q.1 q.2 ε c) (fun p => D.rightSphere p.1 p.2 ε c)
  have hex : ∀ i : Ix, ∃ (Gi : (Fin (dI i) → ℝ) → M) (Ωi Ki : Set (Fin (dI i) → ℝ)),
      IsOpen Ωi ∧ IsCompact Ki ∧ Ki ⊆ Ωi ∧ ContMDiffOn 𝓘(ℝ, Fin (dI i) → ℝ) I 1 Gi Ωi ∧
      (∀ z ∈ Gi '' Ki, ∃ s ∈ Sph i, f s = c ∧ ∃ σ : ℝ, |σ| ≤ κ / 2 ∧ z = D.flow σ s) ∧
      (∀ s ∈ Sph i, f s = c → ∀ σ : ℝ, |σ| ≤ κ / 2 → D.flow σ s ∈ Gi '' Ki) := by
    rintro (⟨q, hq⟩ | ⟨p, hp⟩)
    · refine gen q hq _ ((ModelField.recombineL (D.chart q hq).hk).comp
        (ContinuousLinearMap.inl ℝ _ _)) ((D.chart q hq).leftModelSphere ε) (f q - ε - c)
        ?_ ?_ ?_
      · intro y hy
        exact (D.chart q hq).le_subset_ball (D.chart q hq).hRR'
          ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere (hεR q hq) hy)
      · intro y hy
        refine ⟨negPart (D.chart q hq).hk y, hy.2, ?_⟩
        change ModelField.recombineL (D.chart q hq).hk (negPart (D.chart q hq).hk y, 0) = y
        rw [ModelField.recombineL_apply, ← hy.1,
          DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]
      · intro u hu
        change ModelField.recombineL (D.chart q hq).hk (u, 0) ∈ _
        rw [ModelField.recombineL_apply]
        exact ⟨ModelField.posPart_recombine _ _ _, by
          rw [ModelField.negPart_recombine]; exact hu⟩
    · refine gen p hp _ ((ModelField.recombineL (D.chart p hp).hk).comp
        (ContinuousLinearMap.inr ℝ _ _)) ((D.chart p hp).rightModelSphere ε) (f p + ε - c)
        ?_ ?_ ?_
      · intro y hy
        exact (D.chart p hp).le_subset_ball (D.chart p hp).hRR'
          ((D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere (hεR p hp) hy)
      · intro y hy
        refine ⟨posPart (D.chart p hp).hk y, hy.2, ?_⟩
        change ModelField.recombineL (D.chart p hp).hk (0, posPart (D.chart p hp).hk y) = y
        rw [ModelField.recombineL_apply, ← hy.1,
          DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]
      · intro u hu
        change ModelField.recombineL (D.chart p hp).hk (0, u) ∈ _
        rw [ModelField.recombineL_apply]
        exact ⟨ModelField.negPart_recombine _ _ _, by
          rw [ModelField.posPart_recombine]; exact hu⟩
  choose Gm Ωm Km hΩm hKm hKΩ hGm hcov1 hcov2 using hex
  let s : Finset Ix := (Finset.univ.filter (fun q : {q // q ∈ crit} => q.1 ∈ L)).disjSum
    (Finset.univ.filter (fun p : {p // p ∈ crit} => p.1 ∈ R))
  have hsL : ∀ q : {q // q ∈ crit}, (Sum.inl q : Ix) ∈ s ↔ q.1 ∈ L := fun q => by
    rw [Finset.inl_mem_disjSum, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hsR : ∀ p : {p // p ∈ crit}, (Sum.inr p : Ix) ∈ s ↔ p.1 ∈ R := fun p => by
    rw [Finset.inr_mem_disjSum, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hsu1 : ∀ z, z ∈ D.sphereUnion L R ε c → ∃ i ∈ s, z ∈ Sph i := by
    intro z hz
    rcases hz with hz | hz
    · simp only [mem_iUnion] at hz
      obtain ⟨q, hq, hqL, hz⟩ := hz
      exact ⟨Sum.inl ⟨q, hq⟩, (hsL ⟨q, hq⟩).2 hqL, hz⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨p, hp, hpR, hz⟩ := hz
      exact ⟨Sum.inr ⟨p, hp⟩, (hsR ⟨p, hp⟩).2 hpR, hz⟩
  have hsu2 : ∀ i ∈ s, ∀ z ∈ Sph i, z ∈ D.sphereUnion L R ε c := by
    rintro (⟨q, hq⟩ | ⟨p, hp⟩) hi z hz
    · have hqL : q ∈ L := (hsL ⟨q, hq⟩).1 hi
      left
      simp only [mem_iUnion]
      exact ⟨q, hq, hqL, hz⟩
    · have hpR : p ∈ R := (hsR ⟨p, hp⟩).1 hi
      right
      simp only [mem_iUnion]
      exact ⟨p, hp, hpR, hz⟩
  have hdim : ∀ i ∈ s, dI i + m < n := by
    rintro (⟨q, hq⟩ | ⟨p, hp⟩) hi
    · have hqL : q ∈ L := (hsL ⟨q, hq⟩).1 hi
      exact (hL q hq hqL).2
    · have hpR : p ∈ R := (hsR ⟨p, hp⟩).1 hi
      exact (hR p hp hpR).2
  have hAC' : ∀ y ∈ A ∩ Icc 0 1, ∀ i ∈ s, F y ∉ Gm i '' Km i := by
    intro y hy i hi hmem
    obtain ⟨s0, hs0, hfs0, σ, hσ, hz⟩ := hcov1 i (F y) hmem
    have hFc : f (F y) = c := (hFY hy.2).1
    have hσκ : |σ| ≤ κ := hσ.trans (by linarith)
    have h1 := hlev s0 hfs0 σ hσκ
    rw [← hz, hFc] at h1
    have hσ0 : σ = 0 := by linarith
    rw [hσ0, flow_zero] at hz
    exact hAC y hy (hsu2 i hi _ (hz ▸ hs0))
  obtain ⟨Hm, hHc, hH0, hHA, hHU, hH1⟩ := exists_pushOff (I := I) hF hA s dI Gm Ωm Km
    (fun i _ => hΩm i) (fun i _ => ⟨hKm i, hKΩ i⟩) (fun i _ => hGm i) hdim hAC' hUo hFU
  refine ⟨fun t y => if y ∈ Icc (0 : Fin m → ℝ) 1 then D.π c (Hm t y) else F y, ?_, ?_, ?_, ?_,
    ?_⟩
  · refine ((D.continuous_π hf c).comp_continuousOn hHc).congr ?_
    rintro ⟨t, y⟩ ⟨_, hy⟩
    simp only [hy, ↓reduceIte, Function.comp_apply]
  · intro y
    by_cases hy : y ∈ Icc (0 : Fin m → ℝ) 1
    · simp only [hy, ↓reduceIte, hH0]
      exact π_eq_self_of_level (hFY hy).1
    · simp only [hy, ↓reduceIte]
  · intro t y hyA
    by_cases hy : y ∈ Icc (0 : Fin m → ℝ) 1
    · simp only [hy, ↓reduceIte, hHA t y hyA]
      exact π_eq_self_of_level (hFY hy).1
    · simp only [hy, ↓reduceIte]
  · intro t ht y hy
    simp only [hy, ↓reduceIte]
    have hz := hHU t ht hy
    exact ⟨f_π hf hcIcc hz.1.1, hz.1.2⟩
  · intro y hy hmem
    simp only [hy, ↓reduceIte] at hmem
    have hz : Hm 1 y ∈ U := hHU 1 ⟨zero_le_one, le_rfl⟩ hy
    obtain ⟨i, hi, hzi⟩ := hsu1 _ hmem
    have hfπ : f (D.π c (Hm 1 y)) = c := f_π hf hcIcc hz.1.1
    have hσ : |c - f (Hm 1 y)| ≤ κ / 2 := by
      have h2 := hz.2
      simp only [mem_preimage, mem_Ioo] at h2
      rw [abs_le]
      constructor <;> linarith [h2.1, h2.2]
    have hcov := hcov2 i (D.π c (Hm 1 y)) hzi hfπ (c - f (Hm 1 y)) hσ
    have heq : D.flow (c - f (Hm 1 y)) (D.π c (Hm 1 y)) = Hm 1 y := by
      unfold GradientLikeStrip.π
      rw [flow_flow, show f (Hm 1 y) - c + (c - f (Hm 1 y)) = 0 by ring, flow_zero]
    rw [heq] at hcov
    exact hH1 y hy i hi hcov

theorem simplyConnected_level_diff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {ε c κ : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) (hκ : 0 < κ)
    (hcκ : a ≤ c - κ ∧ c + κ ≤ b) (hU : ∀ y, f y ∈ Icc (c - κ) (c + κ) → ∀ x hx, y ∉ D.smallBall x hx)
    (L R : Finset M)
    (hL : ∀ q (hq : q ∈ crit), q ∈ L → c + κ < f q - ε ∧ (D.chart q hq).k + 3 ≤ n)
    (hR : ∀ p (hp : p ∈ crit), p ∈ R → f p + ε < c - κ ∧ 3 ≤ (D.chart p hp).k)
    {G : Set M} (hG : IsOpen G) (hY : SimplyConnectedSpace ↥(f ⁻¹' {c} ∩ G)) :
    SimplyConnectedSpace ↥((f ⁻¹' {c} ∩ G) \ D.sphereUnion L R ε c) := by
  classical
  set Y : Set M := f ⁻¹' {c} ∩ G with hYdef
  set S : Set M := D.sphereUnion L R ε c with hSdef
  have push : ∀ {m : ℕ}, m ≤ 2 → ∀ {F : (Fin m → ℝ) → M}, ContinuousOn F (Icc 0 1) →
      MapsTo F (Icc 0 1) Y → ∀ {A : Set (Fin m → ℝ)}, IsClosed A →
      (∀ y ∈ A ∩ Icc 0 1, F y ∉ S) →
      ∃ Hm : ℝ → (Fin m → ℝ) → M, ContinuousOn (fun p : ℝ × (Fin m → ℝ) => Hm p.1 p.2)
        (Icc 0 1 ×ˢ Icc 0 1) ∧ (∀ y, Hm 0 y = F y) ∧ (∀ t y, y ∈ A → Hm t y = F y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Icc 0 1) Y) ∧
      ∀ y ∈ Icc (0 : Fin m → ℝ) 1, Hm 1 y ∉ S := by
    intro m hm F hF hFY A hA hAC
    refine exists_level_pushOff hf D hε hεr hκ hcκ hU L R ?_ ?_ hG hF hFY hA hAC
    · intro q hq hqL
      obtain ⟨h1, h2⟩ := hL q hq hqL
      exact ⟨h1, by omega⟩
    · intro p hp hpR
      obtain ⟨h1, h2⟩ := hR p hp hpR
      have := (D.chart p hp).hk
      exact ⟨h1, by omega⟩
  have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have := hY
  have hne : Nonempty ↥(Y \ S) := by
    obtain ⟨y₀⟩ := (inferInstance : PathConnectedSpace ↥Y).nonempty
    obtain ⟨Hm, -, -, -, hmaps, hS⟩ := push (m := 1) (by norm_num)
      (F := fun _ => (y₀ : M)) continuousOn_const (fun _ _ => y₀.2) (A := ∅) isClosed_empty
      (by simp)
    have h0 : (0 : Fin 1 → ℝ) ∈ Icc (0 : Fin 1 → ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    exact ⟨⟨Hm 1 0, hmaps 1 h01 h0, hS 0 h0⟩⟩
  have hpc : PathConnectedSpace ↥(Y \ S) := by
    refine ⟨hne, fun x y => ?_⟩
    let γ : Path (⟨x.1, x.2.1⟩ : ↥Y) ⟨y.1, y.2.1⟩ := PathConnectedSpace.somePath _ _
    let F : (Fin 1 → ℝ) → M := fun v => (γ (projIcc 0 1 zero_le_one (v 0)) : M)
    have hFc : Continuous F :=
      continuous_subtype_val.comp (γ.continuous.comp (continuous_projIcc.comp (continuous_apply 0)))
    have hF0 : ∀ v : Fin 1 → ℝ, v 0 = 0 → F v = x.1 := by
      intro v hv
      simp only [F, hv, Set.projIcc_left]
      exact congrArg Subtype.val γ.source
    have hF1 : ∀ v : Fin 1 → ℝ, v 0 = 1 → F v = y.1 := by
      intro v hv
      simp only [F, hv, Set.projIcc_right]
      exact congrArg Subtype.val γ.target
    obtain ⟨Hm, hHc, -, hHA, hmaps, hS⟩ := push (m := 1) (by norm_num) hFc.continuousOn
      (fun v _ => (γ _).2) (A := {v | v 0 = 0} ∪ {v | v 0 = 1})
      ((isClosed_eq (continuous_apply 0) continuous_const).union
        (isClosed_eq (continuous_apply 0) continuous_const))
      (by
        rintro v ⟨hv | hv, -⟩
        · rw [hF0 v hv]; exact x.2.2
        · rw [hF1 v hv]; exact y.2.2)
    have hcube : ∀ t : unitInterval, (fun _ : Fin 1 => (t : ℝ)) ∈ Icc (0 : Fin 1 → ℝ) 1 :=
      fun t => ⟨fun _ => t.2.1, fun _ => t.2.2⟩
    refine ⟨{ toFun := fun t => ⟨Hm 1 (fun _ => (t : ℝ)), hmaps 1 h01 (hcube t), hS _ (hcube t)⟩
              continuous_toFun := ?_, source' := ?_, target' := ?_ }⟩
    · refine Continuous.subtype_mk ?_ _
      exact hHc.comp_continuous (f := fun t : unitInterval => ((1 : ℝ), fun _ : Fin 1 => (t : ℝ)))
        (by fun_prop) (fun t => ⟨h01, hcube t⟩)
    · apply Subtype.ext
      change Hm 1 (fun _ => ((0 : unitInterval) : ℝ)) = x.1
      have hv : (fun _ : Fin 1 => ((0 : unitInterval) : ℝ)) 0 = 0 := rfl
      exact (hHA 1 _ (Or.inl hv)).trans (hF0 (fun _ : Fin 1 => ((0 : unitInterval) : ℝ)) hv)
    · apply Subtype.ext
      change Hm 1 (fun _ => ((1 : unitInterval) : ℝ)) = y.1
      have hv : (fun _ : Fin 1 => ((1 : unitInterval) : ℝ)) 0 = 1 := rfl
      exact (hHA 1 _ (Or.inr hv)).trans (hF1 (fun _ : Fin 1 => ((1 : unitInterval) : ℝ)) hv)
  rw [simply_connected_iff_paths_homotopic']
  refine ⟨hpc, fun {x y} p q => ?_⟩
  let ι : ↥(Y \ S) → ↥Y := fun z => ⟨z.1, z.2.1⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic (p.map hι) (q.map hι)
  let pr : ℝ → unitInterval := projIcc 0 1 zero_le_one
  let F : (Fin 2 → ℝ) → M := fun v => (H (pr (v 0), pr (v 1)) : M)
  have hFc : Continuous F :=
    continuous_subtype_val.comp (H.continuous.comp
      ((continuous_projIcc.comp (continuous_apply 0)).prodMk
        (continuous_projIcc.comp (continuous_apply 1))))
  have hprv : ∀ t : unitInterval, pr (t : ℝ) = t := fun t => Set.projIcc_val _ t
  have hpr0 : pr 0 = 0 := Set.projIcc_left _
  have hpr1 : pr 1 = 1 := Set.projIcc_right _
  have hFs0 : ∀ v : Fin 2 → ℝ, v 0 = 0 → F v = (p (pr (v 1))).1 := by
    intro v hv
    simp only [F, hv, hpr0, H.apply_zero]
    rfl
  have hFs1 : ∀ v : Fin 2 → ℝ, v 0 = 1 → F v = (q (pr (v 1))).1 := by
    intro v hv
    simp only [F, hv, hpr1, H.apply_one]
    rfl
  have hFt0 : ∀ v : Fin 2 → ℝ, v 1 = 0 → F v = x.1 := by
    intro v hv
    simp only [F, hv, hpr0, H.source]
    rfl
  have hFt1 : ∀ v : Fin 2 → ℝ, v 1 = 1 → F v = y.1 := by
    intro v hv
    simp only [F, hv, hpr1, H.target]
    rfl
  obtain ⟨Hm, hHc, -, hHA, hmaps, hS⟩ := push (m := 2) le_rfl hFc.continuousOn
    (fun v _ => (H _).2)
    (A := {v | v 0 = 0} ∪ {v | v 0 = 1} ∪ {v | v 1 = 0} ∪ {v | v 1 = 1})
    ((((isClosed_eq (continuous_apply 0) continuous_const).union
      (isClosed_eq (continuous_apply 0) continuous_const)).union
      (isClosed_eq (continuous_apply 1) continuous_const)).union
      (isClosed_eq (continuous_apply 1) continuous_const))
    (by
      rintro v ⟨((hv | hv) | hv) | hv, -⟩
      · rw [hFs0 v hv]; exact (p _).2.2
      · rw [hFs1 v hv]; exact (q _).2.2
      · rw [hFt0 v hv]; exact x.2.2
      · rw [hFt1 v hv]; exact y.2.2)
  let pt : unitInterval → unitInterval → Fin 2 → ℝ := fun s t => ![(s : ℝ), (t : ℝ)]
  have hpt0 : ∀ s t, pt s t 0 = s := fun _ _ => rfl
  have hpt1 : ∀ s t, pt s t 1 = t := fun _ _ => rfl
  have hcube : ∀ s t, pt s t ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    intro s t
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
    · exact s.2.1
    · exact t.2.1
    · exact s.2.2
    · exact t.2.2
  have hptc : Continuous fun st : unitInterval × unitInterval => pt st.1 st.2 := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_subtype_val.comp continuous_fst
    · exact continuous_subtype_val.comp continuous_snd
  refine ⟨{ toFun := fun st => ⟨Hm 1 (pt st.1 st.2), hmaps 1 h01 (hcube _ _), hS _ (hcube _ _)⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · refine Continuous.subtype_mk ?_ _
    exact hHc.comp_continuous
      (f := fun st : unitInterval × unitInterval => ((1 : ℝ), pt st.1 st.2))
      (continuous_const.prodMk hptc) (fun st => ⟨h01, hcube _ _⟩)
  · intro t
    apply Subtype.ext
    change Hm 1 (pt 0 t) = (p t).1
    have hv : pt 0 t 0 = 0 := rfl
    rw [hHA 1 _ (Or.inl (Or.inl (Or.inl hv))), hFs0 _ hv, hpt1, hprv]
  · intro t
    apply Subtype.ext
    change Hm 1 (pt 1 t) = (q t).1
    have hv : pt 1 t 0 = 1 := rfl
    rw [hHA 1 _ (Or.inl (Or.inl (Or.inr hv))), hFs1 _ hv, hpt1, hprv]
  · intro s t ht
    apply Subtype.ext
    change Hm 1 (pt s t) = (p t).1
    rcases ht with rfl | rfl
    · have hv : pt s 0 1 = 0 := rfl
      rw [hHA 1 _ (Or.inl (Or.inr hv)), hFt0 _ hv, p.source]
    · have hv : pt s 1 1 = 1 := rfl
      rw [hHA 1 _ (Or.inr hv), hFt1 _ hv, p.target]

theorem simplyConnected_level_of_diff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {ε c κ : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) (hκ : 0 < κ)
    (hcκ : a ≤ c - κ ∧ c + κ ≤ b) (hU : ∀ y, f y ∈ Icc (c - κ) (c + κ) → ∀ x hx, y ∉ D.smallBall x hx)
    (L R : Finset M)
    (hL : ∀ q (hq : q ∈ crit), q ∈ L → c + κ < f q - ε ∧ (D.chart q hq).k + 2 ≤ n)
    (hR : ∀ p (hp : p ∈ crit), p ∈ R → f p + ε < c - κ ∧ 2 ≤ (D.chart p hp).k)
    {G : Set M} (hG : IsOpen G)
    (hY : SimplyConnectedSpace ↥((f ⁻¹' {c} ∩ G) \ D.sphereUnion L R ε c)) :
    SimplyConnectedSpace ↥(f ⁻¹' {c} ∩ G) := by
  classical
  set Y : Set M := f ⁻¹' {c} ∩ G with hYdef
  set S : Set M := D.sphereUnion L R ε c with hSdef
  have hL' : ∀ m : ℕ, m ≤ 1 → ∀ q (hq : q ∈ crit), q ∈ L →
      c + κ < f q - ε ∧ (D.chart q hq).k + m < n := by
    intro m hm q hq hqL
    obtain ⟨h1, h2⟩ := hL q hq hqL
    exact ⟨h1, by omega⟩
  have hR' : ∀ m : ℕ, m ≤ 1 → ∀ p (hp : p ∈ crit), p ∈ R →
      f p + ε < c - κ ∧ n - (D.chart p hp).k + m < n := by
    intro m hm p hp hpR
    obtain ⟨h1, h2⟩ := hR p hp hpR
    have h3 := (D.chart p hp).hk
    exact ⟨h1, by omega⟩
  have hpt : ∀ y : ↥Y, ∃ y' : ↥Y, (y' : M) ∉ S ∧ Nonempty (Path y y') := by
    intro y
    have hAC0 : ∀ z ∈ (∅ : Set (Fin 0 → ℝ)) ∩ Icc 0 1, (fun _ : Fin 0 → ℝ => (y : M)) z ∉ S :=
      fun z hz => absurd hz.1 (Set.notMem_empty z)
    obtain ⟨Hm, hHc, hH0, -, hHY, hH1⟩ := D.exists_level_pushOff hf hε hεr hκ hcκ hU L R
      (hL' 0 (by norm_num)) (hR' 0 (by norm_num)) hG (F := fun _ => (y : M)) continuousOn_const
      (fun _ _ => y.2) isClosed_empty hAC0
    have h0 : (0 : Fin 0 → ℝ) ∈ Icc (0 : Fin 0 → ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hmem : ∀ t : unitInterval, Hm t 0 ∈ Y := fun t => hHY t t.2 h0
    have h1mem : Hm 1 0 ∈ Y := hHY 1 ⟨zero_le_one, le_rfl⟩ h0
    refine ⟨⟨Hm 1 0, h1mem⟩, hH1 0 h0, ⟨?_⟩⟩
    exact
      { toFun := fun t => ⟨Hm t 0, hmem t⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact hHc.comp_continuous (f := fun t : unitInterval => ((t : ℝ), (0 : Fin 0 → ℝ)))
            (continuous_subtype_val.prodMk continuous_const) (fun t => ⟨t.2, h0⟩)
        source' := Subtype.ext (by simp [hH0])
        target' := rfl }
  have hpath : ∀ {x y : ↥Y}, (x : M) ∉ S → (y : M) ∉ S → ∀ q : Path x y,
      ∃ q' : Path x y, q.Homotopic q' ∧ ∀ s, (q' s : M) ∉ S := by
    intro x y hx hy q
    have hAc : IsClosed ({z : Fin 1 → ℝ | z 0 = 0} ∪ {z | z 0 = 1}) :=
      (isClosed_eq (continuous_apply 0) continuous_const).union
        (isClosed_eq (continuous_apply 0) continuous_const)
    have hFc : Continuous (fun z : Fin 1 → ℝ => (q.extend (z 0) : M)) :=
      continuous_subtype_val.comp (q.continuous_extend.comp (continuous_apply 0))
    have hAC : ∀ z ∈ ({z : Fin 1 → ℝ | z 0 = 0} ∪ {z | z 0 = 1}) ∩ Icc 0 1,
        (fun z : Fin 1 → ℝ => (q.extend (z 0) : M)) z ∉ S := by
      intro z hz
      rcases hz.1 with h | h
      · have h' : z 0 = 0 := h
        simp only [h', Path.extend_zero]
        exact hx
      · have h' : z 0 = 1 := h
        simp only [h', Path.extend_one]
        exact hy
    obtain ⟨Hm, hHc, hH0, hHA, hHY, hH1⟩ := D.exists_level_pushOff hf hε hεr hκ hcκ hU L R
      (hL' 1 le_rfl) (hR' 1 le_rfl) hG (F := fun z => (q.extend (z 0) : M)) hFc.continuousOn
      (fun z _ => (q.extend (z 0)).2) hAc hAC
    have hcube : ∀ s : unitInterval, (fun _ : Fin 1 => (s : ℝ)) ∈ Icc (0 : Fin 1 → ℝ) 1 :=
      fun s => ⟨fun _ => s.2.1, fun _ => s.2.2⟩
    have hmem : ∀ t s : unitInterval, Hm t (fun _ => (s : ℝ)) ∈ Y :=
      fun t s => hHY t t.2 (hcube s)
    have hHcont : Continuous
        (fun ts : unitInterval × unitInterval => Hm ts.1 (fun _ => (ts.2 : ℝ))) :=
      hHc.comp_continuous
        (f := fun ts : unitInterval × unitInterval => ((ts.1 : ℝ), fun _ : Fin 1 => (ts.2 : ℝ)))
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_pi fun _ => continuous_subtype_val.comp continuous_snd))
        (fun ts => ⟨ts.1.2, hcube ts.2⟩)
    have hA0 : ∀ t : ℝ, Hm t (fun _ => (0 : ℝ)) = (x : M) := fun t => by
      rw [hHA t _ (Or.inl rfl)]
      simp
    have hA1 : ∀ t : ℝ, Hm t (fun _ => (1 : ℝ)) = (y : M) := fun t => by
      rw [hHA t _ (Or.inr rfl)]
      simp
    let q' : Path x y :=
      { toFun := fun s => ⟨Hm 1 (fun _ => (s : ℝ)), hmem 1 s⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact hHcont.comp
            ((continuous_const : Continuous fun _ : unitInterval => (1 : unitInterval)).prodMk
              continuous_id)
        source' := Subtype.ext (hA0 1)
        target' := Subtype.ext (hA1 1) }
    have hz : ∀ s : unitInterval, Hm 0 (fun _ => (s : ℝ)) = (q s : M) := fun s => by
      rw [hH0]
      simp
    let hom : Path.Homotopy q q' :=
      { toFun := fun ts => ⟨Hm ts.1 (fun _ => (ts.2 : ℝ)), hmem ts.1 ts.2⟩
        continuous_toFun := hHcont.subtype_mk _
        map_zero_left := fun s => Subtype.ext (hz s)
        map_one_left := fun s => rfl
        prop' := fun t s hs => by
          rcases hs with rfl | rfl
          · exact Subtype.ext ((hA0 t).trans (congrArg Subtype.val q.source.symm))
          · exact Subtype.ext ((hA1 t).trans (congrArg Subtype.val q.target.symm)) }
    exact ⟨q', ⟨hom⟩, fun s => hH1 _ (hcube s)⟩
  have hZY : Y \ S ⊆ Y := sdiff_subset
  let ι : C(↥(Y \ S), ↥Y) := ⟨Set.inclusion hZY, continuous_inclusion hZY⟩
  have hlift : ∀ {x y : ↥Y} (hx : (x : M) ∉ S) (hy : (y : M) ∉ S) (q₁ q₂ : Path x y),
      (∀ s, (q₁ s : M) ∉ S) → (∀ s, (q₂ s : M) ∉ S) → q₁.Homotopic q₂ := by
    intro x y hx hy q₁ q₂ h₁ h₂
    let lift : ∀ q : Path x y, (∀ s, (q s : M) ∉ S) →
        Path (⟨x, x.2, hx⟩ : ↥(Y \ S)) ⟨y, y.2, hy⟩ := fun q hq =>
      { toFun := fun s => ⟨q s, (q s).2, hq s⟩
        continuous_toFun := (continuous_subtype_val.comp q.continuous).subtype_mk _
        source' := by simp
        target' := by simp }
    exact (SimplyConnectedSpace.paths_homotopic (lift q₁ h₁) (lift q₂ h₂)).map ι
  rw [simply_connected_iff_paths_homotopic']
  have hjoinZ : ∀ x y : ↥Y, (x : M) ∉ S → (y : M) ∉ S → Joined x y := fun x y hx hy =>
    (PathConnectedSpace.joined (⟨x, x.2, hx⟩ : ↥(Y \ S)) ⟨y, y.2, hy⟩).map ι.continuous
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨z⟩ := (inferInstance : PathConnectedSpace ↥(Y \ S)).nonempty
    exact ⟨ι z⟩
  · intro x y
    obtain ⟨x', hx', ⟨γx⟩⟩ := hpt x
    obtain ⟨y', hy', ⟨γy⟩⟩ := hpt y
    exact Joined.trans (Joined.trans ⟨γx⟩ (hjoinZ x' y' hx' hy')) (Joined.symm ⟨γy⟩)
  · intro x y p₁ p₂
    obtain ⟨x', hx', ⟨γx⟩⟩ := hpt x
    obtain ⟨y', hy', ⟨γy⟩⟩ := hpt y
    obtain ⟨q₁, hq₁, hS₁⟩ := hpath hx' hy' (γx.symm.trans (p₁.trans γy))
    obtain ⟨q₂, hq₂, hS₂⟩ := hpath hx' hy' (γx.symm.trans (p₂.trans γy))
    have hq : (γx.symm.trans (p₁.trans γy)).Homotopic (γx.symm.trans (p₂.trans γy)) :=
      hq₁.trans ((hlift hx' hy' q₁ q₂ hS₁ hS₂).trans hq₂.symm)
    have key : ∀ p : Path x y,
        p.Homotopic ((γx.trans (γx.symm.trans (p.trans γy))).trans γy.symm) := by
      intro p
      have e1 : p.Homotopic (p.trans (Path.refl y)) := ⟨(Path.Homotopy.transRefl p).symm⟩
      have e2 : (p.trans (Path.refl y)).Homotopic (p.trans (γy.trans γy.symm)) :=
        Path.Homotopic.hcomp (Path.Homotopic.refl p) ⟨Path.Homotopy.reflTransSymm γy⟩
      have e3 : (p.trans (γy.trans γy.symm)).Homotopic ((p.trans γy).trans γy.symm) :=
        ⟨(Path.Homotopy.transAssoc p γy γy.symm).symm⟩
      have e4 : ((p.trans γy).trans γy.symm).Homotopic
          (((Path.refl x).trans (p.trans γy)).trans γy.symm) :=
        Path.Homotopic.hcomp ⟨(Path.Homotopy.reflTrans (p.trans γy)).symm⟩
          (Path.Homotopic.refl _)
      have e5 : (((Path.refl x).trans (p.trans γy)).trans γy.symm).Homotopic
          (((γx.trans γx.symm).trans (p.trans γy)).trans γy.symm) :=
        Path.Homotopic.hcomp (Path.Homotopic.hcomp ⟨Path.Homotopy.reflTransSymm γx⟩
          (Path.Homotopic.refl _)) (Path.Homotopic.refl _)
      have e6 : (((γx.trans γx.symm).trans (p.trans γy)).trans γy.symm).Homotopic
          ((γx.trans (γx.symm.trans (p.trans γy))).trans γy.symm) :=
        Path.Homotopic.hcomp ⟨Path.Homotopy.transAssoc γx γx.symm (p.trans γy)⟩
          (Path.Homotopic.refl _)
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
    exact (key p₁).trans ((Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl γx) hq)
      (Path.Homotopic.refl γy.symm)).trans (key p₂).symm)

theorem pathConnectedSpace_level (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {c : ℝ} (hac : a < c)
    (hcb : c < b) (hreg : ∀ y, f y = c → ∀ x hx, y ∉ D.smallBall x hx)
    (hidx : ∀ x ∈ crit, f x < c → 2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hV₀ : PathConnectedSpace ↥(f ⁻¹' {a})) : PathConnectedSpace ↥(f ⁻¹' {c}) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hcritab : ∀ x ∈ crit, a < f x ∧ f x < b := fun x hx => ((hcrit x).1 hx).1
  have hcritc : ∀ x ∈ crit, f x ≠ c := fun x hx h => hreg x h x hx (D.p_mem_smallBall x hx)
  have hsmall : ∀ d : ℝ, 0 < d → ∀ᶠ e in 𝓝[>] (0 : ℝ), 8 * e < d := by
    intro d hd
    have h8 : ∀ᶠ e in 𝓝 (0 : ℝ), e < d / 8 := eventually_lt_nhds (by positivity)
    filter_upwards [nhdsWithin_le_nhds h8] with e he
    linarith
  have h1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  have h2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 8 * e < 8 * ε := hsmall _ (by linarith)
  have h3 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 8 * e < 1 / 2 := hsmall _ (by norm_num)
  have h4 : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ x ∈ crit, 8 * e < f x - a ∧ 8 * e < |f x - c| := by
    refine (Filter.eventually_all_finset crit).2 fun x hx => ?_
    exact (hsmall _ (by linarith [(hcritab x hx).1])).and
      (hsmall _ (abs_pos.2 (sub_ne_zero.2 (hcritc x hx))))
  have h5 : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ x ∈ crit, ∀ y ∈ crit, f x ≠ f y → 8 * e < |f x - f y| := by
    refine (Filter.eventually_all_finset crit).2 fun x hx => ?_
    refine (Filter.eventually_all_finset crit).2 fun y hy => ?_
    by_cases hxy : f x = f y
    · exact Filter.Eventually.of_forall fun e h => absurd hxy h
    · filter_upwards [hsmall _ (abs_pos.2 (sub_ne_zero.2 hxy))] with e he _ using he
  obtain ⟨e, he0, heε, he1, he4, he5⟩ := (h1.and (h2.and (h3.and (h4.and h5)))).exists
  obtain ⟨E, -, -, hEr, -⟩ := D.exists_shrink_field hfs he0 one_pos (by norm_num; linarith)
    (fun x hx => by linarith [(hεr x hx).2])
  have hEεr : ∀ x hx, (E.chart x hx).r₀ ^ 2 < 2 * e ∧ 8 * e < E.rm x hx ^ 2 := by
    intro x hx
    refine ⟨(hEr x hx).1, ?_⟩
    rw [(hEr x hx).2]
    rcases min_cases (1 : ℝ) (D.rm x hx) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · linarith
    · linarith [(hεr x hx).2]
  have hEball : ∀ x (hx : x ∈ crit) y, y ∈ E.smallBall x hx → |f y - f x| < e := by
    intro x hx y hy
    have := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hy
    linarith [(hEr x hx).1]
  have hidxE : ∀ x (hx : x ∈ crit), f x < c →
      2 ≤ (E.chart x hx).k ∧ (E.chart x hx).k + 2 ≤ n := by
    intro x hx hxc
    rw [← (E.chart x hx).hkidx]
    exact hidx x hx hxc
  have htrans : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      (∀ x ∈ crit, f x ≤ s - e ∨ t + e ≤ f x) →
      IsPathConnected (f ⁻¹' {s}) → IsPathConnected (f ⁻¹' {t}) := by
    intro s t has hst htb hsep hP
    have hU : ∀ y, f y ∈ Icc s t → ∀ p (hp : p ∈ crit), y ∉ E.smallBall p hp := by
      intro y hy p hp hmem
      have h := abs_lt.1 (hEball p hp y hmem)
      rcases hsep p hp with h' | h' <;> linarith [hy.1, hy.2, h.1, h.2]
    obtain ⟨hl1, hl2⟩ := GradientLikeStrip.flow_level_transport (D := E) hfs has hst htb hU
    have heq : E.flow (s - t) '' (f ⁻¹' {s}) = f ⁻¹' {t} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hl2 x hx).1
      · intro hz
        refine ⟨E.flow (t - s) z, (hl1 z hz).1, ?_⟩
        rw [E.flow_flow, show t - s + (s - t) = 0 by ring, E.flow_zero]
    rw [← heq]
    exact hP.image (E.continuous_flow _)
  have hjoin : ∀ (g : ℝ → M) (F : Set M) (x y : M), ContinuousOn g (Icc 0 1) → g 0 = x →
      g 1 = y → (∀ s ∈ Icc (0 : ℝ) 1, g s ∈ F) → JoinedIn F x y := by
    intro g F x y hg hg0 hg1 hgF
    exact ⟨{ toFun := fun s => g s
             continuous_toFun := hg.comp_continuous continuous_subtype_val (fun s => s.2)
             source' := hg0
             target' := hg1 }, fun s => hgF s s.2⟩
  have hpush : ∀ (t : ℝ) (L R : Finset M), a ≤ t - e → t + e ≤ b →
      (∀ x ∈ crit, f x ≤ t - 2 * e ∨ t + 2 * e ≤ f x) →
      (∀ q (hq : q ∈ crit), q ∈ L → t + e < f q - e ∧ (E.chart q hq).k + 1 < n) →
      (∀ p (hp : p ∈ crit), p ∈ R → f p + e < t - e ∧ n - (E.chart p hp).k + 1 < n) →
      (∀ y ∈ f ⁻¹' {t}, ∃ z ∈ f ⁻¹' {t} \ E.sphereUnion L R e t, JoinedIn (f ⁻¹' {t}) y z) ∧
      (∀ y₀ ∈ f ⁻¹' {t} \ E.sphereUnion L R e t, ∀ y₁ ∈ f ⁻¹' {t} \ E.sphereUnion L R e t,
        JoinedIn (f ⁻¹' {t}) y₀ y₁ → JoinedIn (f ⁻¹' {t} \ E.sphereUnion L R e t) y₀ y₁) := by
    intro t L R hat htb hsep hL hR
    have hU : ∀ y, f y ∈ Icc (t - e) (t + e) → ∀ x (hx : x ∈ crit), y ∉ E.smallBall x hx := by
      intro y hy x hx hmem
      have h := abs_lt.1 (hEball x hx y hmem)
      rcases hsep x hx with h' | h' <;> linarith [hy.1, hy.2, h.1, h.2]
    constructor
    · intro y hy
      obtain ⟨Hm, hHc, hH0, -, hHmaps, hHav⟩ :=
        E.exists_level_pushOff hfs (c := t) (κ := e) he0 hEεr he0 ⟨hat, htb⟩ hU L R (m := 0)
          (fun q hq hqL => ⟨(hL q hq hqL).1, by have := (hL q hq hqL).2; omega⟩)
          (fun p hp hpR => ⟨(hR p hp hpR).1, by have := (hR p hp hpR).2; omega⟩)
          isOpen_univ (F := fun _ => y) continuousOn_const
          (fun _ _ => ⟨hy, mem_univ _⟩) (A := ∅) isClosed_empty
          (fun v hv => absurd hv.1 (notMem_empty v))
      have h0mem : (0 : Fin 0 → ℝ) ∈ Icc (0 : Fin 0 → ℝ) 1 := ⟨le_rfl, fun i => i.elim0⟩
      refine ⟨Hm 1 0, ⟨(hHmaps 1 ⟨zero_le_one, le_rfl⟩ h0mem).1, hHav 0 h0mem⟩, ?_⟩
      refine hjoin (fun s => Hm s 0) _ _ _ ?_ (hH0 0) rfl ?_
      · exact hHc.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => ⟨hs, h0mem⟩)
      · intro s hs
        exact (hHmaps s hs h0mem).1
    · intro y₀ hy₀ y₁ hy₁ hJ
      obtain ⟨γ, hγ⟩ := hJ
      set F : (Fin 1 → ℝ) → M := fun v => γ.extend (v 0) with hFdef
      have hFc : Continuous F := γ.continuous_extend.comp (continuous_apply 0)
      have hFmem : ∀ v, F v ∈ f ⁻¹' {t} := by
        intro v
        have hr : γ.extend (v 0) ∈ range γ.extend := mem_range_self _
        rw [Path.extend_range] at hr
        obtain ⟨u, hu⟩ := hr
        change γ.extend (v 0) ∈ f ⁻¹' {t}
        rw [← hu]
        exact hγ u
      set A : Set (Fin 1 → ℝ) := {v | v 0 = 0} ∪ {v | v 0 = 1} with hAdef
      have hA : IsClosed A :=
        (isClosed_eq (continuous_apply 0) continuous_const).union
          (isClosed_eq (continuous_apply 0) continuous_const)
      have hFA0 : ∀ v : Fin 1 → ℝ, v 0 = 0 → F v = y₀ := by
        intro v hv
        change γ.extend (v 0) = y₀
        rw [hv, Path.extend_zero]
      have hFA1 : ∀ v : Fin 1 → ℝ, v 0 = 1 → F v = y₁ := by
        intro v hv
        change γ.extend (v 0) = y₁
        rw [hv, Path.extend_one]
      have hAC : ∀ v ∈ A ∩ Icc 0 1, F v ∉ E.sphereUnion L R e t := by
        rintro v ⟨hv | hv, -⟩
        · rw [hFA0 v hv]
          exact hy₀.2
        · rw [hFA1 v hv]
          exact hy₁.2
      obtain ⟨Hm, hHc, -, hHA, hHmaps, hHav⟩ :=
        E.exists_level_pushOff hfs (c := t) (κ := e) he0 hEεr he0 ⟨hat, htb⟩ hU L R (m := 1)
          hL hR isOpen_univ hFc.continuousOn (fun v _ => ⟨hFmem v, mem_univ _⟩) hA hAC
      have hcube : ∀ s ∈ Icc (0 : ℝ) 1, (fun _ : Fin 1 => s) ∈ Icc (0 : Fin 1 → ℝ) 1 :=
        fun s hs => ⟨fun _ => hs.1, fun _ => hs.2⟩
      refine hjoin (fun s => Hm 1 (fun _ => s)) _ _ _ ?_ ?_ ?_ ?_
      · exact hHc.comp (continuous_const.prodMk (continuous_pi fun _ => continuous_id)).continuousOn
          (fun s hs => ⟨⟨zero_le_one, le_rfl⟩, hcube s hs⟩)
      · show Hm 1 (fun _ => 0) = y₀
        rw [hHA 1 (fun _ => 0) (Or.inl rfl)]
        exact hFA0 (fun _ => 0) rfl
      · show Hm 1 (fun _ => 1) = y₁
        rw [hHA 1 (fun _ => 1) (Or.inr rfl)]
        exact hFA1 (fun _ => 1) rfl
      · intro s hs
        exact ⟨(hHmaps 1 ⟨zero_le_one, le_rfl⟩ (hcube s hs)).1, hHav _ (hcube s hs)⟩
  have hempty : ∀ t : ℝ, a ≤ t → t ≤ c → (∀ x ∈ crit, 3 * e ≤ |f x - t|) →
      (∀ x ∈ crit, ¬ f x < t) → IsPathConnected (f ⁻¹' {t}) := by
    intro t hat htc hgood hno
    refine htrans a t le_rfl hat (htc.trans hcb.le) (fun x hx => Or.inr ?_)
      (isPathConnected_iff_pathConnectedSpace.2 hV₀)
    have h := hno x hx
    rcases le_abs.1 (hgood x hx) with h' | h' <;> linarith
  have key : ∀ N : ℕ, ∀ t : ℝ, (crit.filter (fun x => f x < t)).card ≤ N → a ≤ t → t ≤ c →
      (∀ x ∈ crit, 3 * e ≤ |f x - t|) → IsPathConnected (f ⁻¹' {t}) := by
    intro N
    induction N with
    | zero =>
      intro t hN hat htc hgood
      refine hempty t hat htc hgood fun x hx hxt => ?_
      have h0 : (crit.filter (fun x => f x < t)).card = 0 := by omega
      rw [Finset.card_eq_zero] at h0
      have hmem : x ∈ crit.filter (fun x => f x < t) := Finset.mem_filter.2 ⟨hx, hxt⟩
      rw [h0] at hmem
      exact Finset.notMem_empty _ hmem
    | succ N ih =>
      intro t hN hat htc hgood
      by_cases hne : (crit.filter (fun x => f x < t)).Nonempty
      swap
      · exact hempty t hat htc hgood fun x hx hxt => hne ⟨x, Finset.mem_filter.2 ⟨hx, hxt⟩⟩
      set St := crit.filter (fun x => f x < t) with hSt
      set τ := (St.image f).max' (hne.image f) with hτ
      obtain ⟨x₀, hx₀St, hx₀τ⟩ := Finset.mem_image.1 (Finset.max'_mem (St.image f) (hne.image f))
      rw [← hτ] at hx₀τ
      have hmax : ∀ x ∈ crit, f x < t → f x ≤ τ := fun x hx hxt =>
        Finset.le_max' _ _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hx, hxt⟩))
      obtain ⟨hx₀, hx₀t⟩ := Finset.mem_filter.1 hx₀St
      rw [hx₀τ] at hx₀t
      have hτt : τ + 3 * e ≤ t := by
        have h := hgood x₀ hx₀
        rw [hx₀τ] at h
        rcases le_abs.1 h with h' | h' <;> linarith
      have hτa : a + 8 * e < τ := by
        have h := (he4 x₀ hx₀).1
        rw [hx₀τ] at h
        linarith
      have hτc : τ + 8 * e < c := by
        have h := (he4 x₀ hx₀).2
        rw [hx₀τ] at h
        rcases lt_abs.1 h with h' | h' <;> linarith
      have hsepτ : ∀ x ∈ crit, f x = τ ∨ 8 * e < |f x - τ| := by
        intro x hx
        by_cases h : f x = τ
        · exact Or.inl h
        · right
          rw [← hx₀τ]
          exact he5 x hx x₀ hx₀ (by rw [hx₀τ]; exact h)
      have hsepτ' : ∀ x ∈ crit, f x = τ ∨ f x < τ - 8 * e ∨ τ + 8 * e < f x := by
        intro x hx
        rcases hsepτ x hx with h | h
        · exact Or.inl h
        · right
          rcases lt_abs.1 h with h' | h'
          · right; linarith
          · left; linarith
      have hcb' : c < b := hcb
      have hP₁ : IsPathConnected (f ⁻¹' {τ - 3 * e}) := by
        refine ih (τ - 3 * e) ?_ (by linarith) (by linarith) ?_
        · have hsub : crit.filter (fun x => f x < τ - 3 * e) ⊂ St := by
            rw [Finset.ssubset_iff_of_subset]
            · refine ⟨x₀, hx₀St, fun h => ?_⟩
              have := (Finset.mem_filter.1 h).2
              rw [hx₀τ] at this
              linarith
            · intro x hx
              obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
              exact Finset.mem_filter.2 ⟨hx1, by linarith⟩
          have := Finset.card_lt_card hsub
          omega
        · intro x hx
          rcases hsepτ' x hx with h | h | h
          · rw [h, show τ - (τ - 3 * e) = 3 * e by ring, abs_of_pos (by linarith)]
          · exact le_abs.2 (Or.inr (by linarith))
          · exact le_abs.2 (Or.inl (by linarith))
      set Lτ := crit.filter (fun x => f x = τ) with hLτ
      obtain ⟨hA0, hA1⟩ := hpush (τ - 3 * e) Lτ ∅ (by linarith) (by linarith)
        (by
          intro x hx
          rcases hsepτ' x hx with h | h | h
          · right; linarith
          · left; linarith
          · right; linarith)
        (by
          intro q hq hqL
          have hfq := (Finset.mem_filter.1 hqL).2
          have := hidxE q hq (by linarith)
          exact ⟨by linarith, by omega⟩)
        (fun p hp hpR => absurd hpR (Finset.notMem_empty p))
      have hP₁' : IsPathConnected (f ⁻¹' {τ - 3 * e} \ E.sphereUnion Lτ ∅ e (τ - 3 * e)) := by
        rw [isPathConnected_iff]
        obtain ⟨y, hy⟩ := hP₁.nonempty
        obtain ⟨z, hz, -⟩ := hA0 y hy
        exact ⟨⟨z, hz⟩, fun y₀ hy₀ y₁ hy₁ => hA1 y₀ hy₀ y₁ hy₁ (hP₁.joinedIn y₀ hy₀.1 y₁ hy₁.1)⟩
      have hS₁ : E.sphereUnion Lτ ∅ e (τ - 3 * e) =
          ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), E.leftSphere x hx e (τ - 3 * e) := by
        ext z
        simp only [GradientLikeStrip.sphereUnion, hLτ, Finset.mem_filter, Finset.notMem_empty,
          iUnion_of_empty, iUnion_empty, union_empty, mem_iUnion, exists_prop, exists_and_left]
        constructor
        · rintro ⟨i, ⟨-, hfi⟩, hx, hz⟩
          exact ⟨i, hfi, hx, hz⟩
        · rintro ⟨i, hfi, hx, hz⟩
          exact ⟨i, ⟨hx, hfi⟩, hx, hz⟩
      obtain ⟨φ⟩ := E.nonempty_homeomorph_level_diff hfs hcrit he0 hEεr (c₁ := τ - 3 * e)
        (τ := τ) (c₂ := τ + 3 * e) (by linarith) (by linarith) (by linarith) (by linarith)
        (by
          intro x hx hxI
          rcases hsepτ' x hx with h | h | h
          · exact h
          · linarith [hxI.1]
          · linarith [hxI.2])
        (by
          intro y hy x hx hmem
          have h := abs_lt.1 (hEball x hx y hmem)
          rcases hsepτ' x hx with h' | h' | h' <;>
          rcases hy with hy | hy <;> linarith [hy.1, hy.2, h.1, h.2])
      rw [hS₁] at hP₁'
      have := isPathConnected_iff_pathConnectedSpace.1 hP₁'
      have hP₂' := isPathConnected_iff_pathConnectedSpace.2 φ.symm.pathConnectedSpace
      have hS₂ : E.sphereUnion ∅ Lτ e (τ + 3 * e) =
          ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), E.rightSphere x hx e (τ + 3 * e) := by
        ext z
        simp only [GradientLikeStrip.sphereUnion, hLτ, Finset.mem_filter, Finset.notMem_empty,
          iUnion_of_empty, iUnion_empty, empty_union, mem_iUnion, exists_prop, exists_and_left]
        constructor
        · rintro ⟨i, ⟨-, hfi⟩, hx, hz⟩
          exact ⟨i, hfi, hx, hz⟩
        · rintro ⟨i, hfi, hx, hz⟩
          exact ⟨i, ⟨hx, hfi⟩, hx, hz⟩
      rw [← hS₂] at hP₂'
      obtain ⟨hB0, -⟩ := hpush (τ + 3 * e) ∅ Lτ (by linarith) (by linarith)
        (by
          intro x hx
          rcases hsepτ' x hx with h | h | h
          · left; linarith
          · left; linarith
          · right; linarith)
        (fun q hq hqL => absurd hqL (Finset.notMem_empty q))
        (by
          intro p hp hpL
          have hfp := (Finset.mem_filter.1 hpL).2
          have := hidxE p hp (by linarith)
          exact ⟨by linarith, by omega⟩)
      have hP₂ : IsPathConnected (f ⁻¹' {τ + 3 * e}) := by
        rw [isPathConnected_iff]
        obtain ⟨z₀, hz₀⟩ := hP₂'.nonempty
        refine ⟨⟨z₀, hz₀.1⟩, fun y₀ hy₀ y₁ hy₁ => ?_⟩
        obtain ⟨w₀, hw₀, hj₀⟩ := hB0 y₀ hy₀
        obtain ⟨w₁, hw₁, hj₁⟩ := hB0 y₁ hy₁
        exact hj₀.trans (((hP₂'.joinedIn w₀ hw₀ w₁ hw₁).mono sdiff_subset).trans hj₁.symm)
      refine htrans (τ + 3 * e) t (by linarith) hτt (htc.trans hcb.le) ?_ hP₂
      intro x hx
      by_cases hxt : f x < t
      · left
        linarith [hmax x hx hxt]
      · right
        rcases le_abs.1 (hgood x hx) with h' | h' <;> linarith
  have hPc := key _ c le_rfl hac.le le_rfl (fun x hx => by linarith [(he4 x hx).2])
  exact isPathConnected_iff_pathConnectedSpace.1 hPc

theorem discClass_leftDisc_eq_of_rescale {g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {p : M} (hp : p ∈ crit) {μ : ℕ} (hμ : (D.chart p hp).k = μ) {ε ε' c : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hrm : 8 * ε < D.rm p hp ^ 2) (hrm' : 8 * ε' < D'.rm p hp ^ 2)
    (hgp : g p = f p) (hfg : ∀ y, f y ≤ f p → g y = f y)
    (hφ : ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
      ∀ x, f x ≤ f p → D'.V x = φ x • D.V x)
    (hpa : a < f p - max ε ε') (hpc : f p < c)
    (hU : ∀ y, f y ∈ Icc a (f p - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hU' : ∀ y, g y ∈ Icc a (g p - ε') → ∀ x hx, y ∉ D'.smallBall x hx)
    (gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk μ)))
      (ULift.down ⁻¹' diskSphere μ) μ) :
    Handle.discClass (f ⁻¹' Icc a c) (f ⁻¹' {a}) (D'.leftDiscMap p μ ε' a) gD =
      Handle.discClass (f ⁻¹' Icc a c) (f ⁻¹' {a}) (D.leftDiscMap p μ ε a) gD := by
  subst hμ
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ := hφ
  have hk := (D.chart p hp).hk
  let Ch : ℝ → EuclideanSpace ℝ (Fin (D.chart p hp).k) → M := fun r y =>
    (D.chart p hp).χ (recombine (D.chart p hp).hk (r • y) 0)
  have hreidx : ∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k),
      (EuclideanSpace.equiv (Fin (D.chart p hp).k) ℝ).symm (Handle.reidx y) = y := by
    intro y
    ext i
    simp [Handle.reidx]
  have hconv : ∀ (h : M → ℝ) (e : MorseNormalChart I h p), e.χ = (D.chart p hp).χ →
      e.k = (D.chart p hp).k → ∀ (r : ℝ) (y : EuclideanSpace ℝ (Fin (D.chart p hp).k)),
      e.χ (recombine e.hk (r • e.toE (Handle.reidx y)) 0) = Ch r y ∧
      e.χ (e.sphereParam r (Handle.reidx y)) = Ch (Real.sqrt (2 * r) / ‖y‖) y := by
    intro h e he hke r y
    obtain ⟨k', hk', hkidx', χ', R, R', r₀, hr₀, hr₀R, hRR', hχ0, hball, hsrc, hnorm, hχs,
      hχsymm⟩ := e
    simp only at he hke
    subst he hke
    simp only [MorseNormalChart.sphereParam, MorseNormalChart.toE, hreidx, Ch, and_self]
  have hDdisc : ∀ e y, D.leftDiscMap p (D.chart p hp).k e a y =
      if ‖y‖ ≤ 1 / 2 then Ch (2 * Real.sqrt (2 * e)) y
      else D.flow ((2 * ‖y‖ - 1) * (f p - e - a)) (Ch (Real.sqrt (2 * e) / ‖y‖) y) := by
    intro e y
    have h := hconv f (D.chart p hp) rfl rfl
    simp only [GradientLikeStrip.leftDiscMap, hp, ↓reduceDIte, (h _ y).1, (h e y).2]
  have hD'disc : ∀ e y, D'.leftDiscMap p (D.chart p hp).k e a y =
      if ‖y‖ ≤ 1 / 2 then Ch (2 * Real.sqrt (2 * e)) y
      else D'.flow ((2 * ‖y‖ - 1) * (f p - e - a)) (Ch (Real.sqrt (2 * e) / ‖y‖) y) := by
    intro e y
    have h := hconv g (D'.chart p hp) (hχ p hp).1 (hχ p hp).2
    simp only [GradientLikeStrip.leftDiscMap, hp, ↓reduceDIte, (h _ y).1, (h e y).2, hgp]
  have hmn : ∀ u : EuclideanSpace ℝ (Fin (D.chart p hp).k),
      morseNorm n (recombine (D.chart p hp).hk u 0) = ‖u‖ := by
    intro u
    have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart p hp).hk (recombine (D.chart p hp).hk u 0)
    rw [ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero] at h
    exact (sq_eq_sq₀ (ModelField.morseNorm_nonneg _) (norm_nonneg _)).1 (by rw [h]; ring)
  have hnfgen : ∀ (h : M → ℝ) (e : MorseNormalChart I h p), e.χ = (D.chart p hp).χ →
      e.k = (D.chart p hp).k → ∀ u : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖u‖ ≤ e.R →
      recombine (D.chart p hp).hk u 0 ∈ (D.chart p hp).χ.source ∧
      h ((D.chart p hp).χ (recombine (D.chart p hp).hk u 0)) = h p - ‖u‖ ^ 2 / 2 := by
    intro h e he hke u hu
    obtain ⟨k', hk', hkidx', χ', R, R', r₀, hr₀, hr₀R, hRR', hχ0, hball, hsrc, hnorm, hχs,
      hχsymm⟩ := e
    simp only at he hke hu
    subst he hke
    refine ⟨hsrc _ (by rw [hmn]; exact hu), ?_⟩
    rw [hnorm _ (by rw [hmn]; exact hu),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero]
    ring
  have hRD : Real.sqrt (2 * ε) ≤ (D.chart p hp).R := by
    have h1 := (D.hrm p hp).2
    have h2 := D.rm_pos p hp
    have h3 := pow_le_pow_left₀ h2.le h1 2
    rw [show (D.chart p hp).R = Real.sqrt ((D.chart p hp).R ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRD' : Real.sqrt (2 * ε') ≤ (D'.chart p hp).R := by
    have h1 := (D'.hrm p hp).2
    have h2 := D'.rm_pos p hp
    have h3 := pow_le_pow_left₀ h2.le h1 2
    rw [show (D'.chart p hp).R = Real.sqrt ((D'.chart p hp).R ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hfD := hnfgen f (D.chart p hp) rfl rfl
  have hgD' := hnfgen g (D'.chart p hp) (hχ p hp).1 (hχ p hp).2
  have hfpab : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  set η := max ε ε' with hηdef
  have hsqη : Real.sqrt (2 * η) = max (Real.sqrt (2 * ε)) (Real.sqrt (2 * ε')) := by
    rcases le_total ε ε' with h | h
    · rw [hηdef, max_eq_right h, max_eq_right (Real.sqrt_le_sqrt (by linarith))]
    · rw [hηdef, max_eq_left h, max_eq_left (Real.sqrt_le_sqrt (by linarith))]
  have hsrcη : ∀ u : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖u‖ ≤ Real.sqrt (2 * η) →
      recombine (D.chart p hp).hk u 0 ∈ (D.chart p hp).χ.source := by
    intro u hu
    rw [hsqη] at hu
    rcases le_total (Real.sqrt (2 * ε)) (Real.sqrt (2 * ε')) with h | h
    · rw [max_eq_right h] at hu; exact (hgD' u (hu.trans hRD')).1
    · rw [max_eq_left h] at hu; exact (hfD u (hu.trans hRD)).1
  have hRcont : Continuous (fun u : EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
      recombine (D.chart p hp).hk u 0) := by
    have : (fun u : EuclideanSpace ℝ (Fin (D.chart p hp).k) => recombine (D.chart p hp).hk u 0) =
        fun u => ModelField.recombineL (D.chart p hp).hk (u, 0) :=
      funext fun u => (ModelField.recombineL_apply _ _ _).symm
    rw [this]
    exact (ModelField.recombineL (D.chart p hp).hk).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hChc : ContinuousOn (fun u : EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
      (D.chart p hp).χ (recombine (D.chart p hp).hk u 0)) {u | ‖u‖ ≤ Real.sqrt (2 * η)} :=
    (D.chart p hp).χ.continuousOn.comp hRcont.continuousOn fun u hu => hsrcη u hu
  have hconn : ∀ (γ : ℝ → M) (A B : ℝ), ContinuousOn γ (Icc A B) →
      (∀ s ∈ Icc A B, g (γ s) < f p) → f (γ A) ≤ f p → ∀ s ∈ Icc A B, f (γ s) ≤ f p := by
    intro γ A B hγ hlt hA
    have hfc : ContinuousOn (fun s => f (γ s)) (Icc A B) := hf.continuous.comp_continuousOn hγ
    have hcl : IsClosed ({s | f (γ s) ≤ f p} ∩ Icc A B) := by
      have := hfc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := f p))
      rw [inter_comm]
      exact this
    intro s hs
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hcl hA ?_ hs
    rintro x ⟨hx, hxI⟩
    have hxlt : f (γ x) < f p := by
      have h1 : g (γ x) = f (γ x) := hfg _ hx
      have h2 := hlt x (Ico_subset_Icc_self hxI)
      linarith
    have hcw : ContinuousWithinAt (fun s => f (γ s)) (Icc A B) x := hfc x (Ico_subset_Icc_self hxI)
    have h1 : ∀ᶠ s in 𝓝[Icc A B] x, f (γ s) < f p := hcw (Iio_mem_nhds hxlt)
    have h2 : 𝓝[>] x ≤ 𝓝[Icc A B] x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hxI)
    exact Filter.mem_of_superset (h2 h1) fun s (hs : f (γ s) < f p) => show f (γ s) ≤ f p from le_of_lt hs
  have hfray : ∀ u : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖u‖ ≤ Real.sqrt (2 * η) →
      f ((D.chart p hp).χ (recombine (D.chart p hp).hk u 0)) = f p - ‖u‖ ^ 2 / 2 := by
    intro u hu
    by_cases hue : ‖u‖ ≤ Real.sqrt (2 * ε)
    · exact (hfD u (hue.trans hRD)).2
    rw [not_le] at hue
    have hu' : ‖u‖ ≤ Real.sqrt (2 * ε') := by
      rw [hsqη] at hu
      rcases le_total (Real.sqrt (2 * ε)) (Real.sqrt (2 * ε')) with h | h
      · rwa [max_eq_right h] at hu
      · rw [max_eq_left h] at hu; linarith
    have hupos : 0 < ‖u‖ := lt_of_le_of_lt (Real.sqrt_nonneg _) hue
    have hsε : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
    set s₀ := Real.sqrt (2 * ε) / ‖u‖ with hs₀
    have hs₀pos : 0 < s₀ := div_pos hsε hupos
    have hs₀1 : s₀ ≤ 1 := by rw [hs₀, div_le_one hupos]; exact hue.le
    have hs₀u : s₀ * ‖u‖ = Real.sqrt (2 * ε) := by rw [hs₀]; field_simp
    have hns : ∀ s ∈ Icc s₀ 1, ‖s • u‖ = s * ‖u‖ := fun s hs => by
      rw [norm_smul, Real.norm_of_nonneg (hs₀pos.le.trans hs.1)]
    have hle : ∀ s ∈ Icc s₀ 1, ‖s • u‖ ≤ Real.sqrt (2 * ε') := fun s hs => by
      rw [hns s hs]; exact (mul_le_of_le_one_left (norm_nonneg u) hs.2).trans hu'
    have hγc : ContinuousOn
        (fun s : ℝ => (D.chart p hp).χ (recombine (D.chart p hp).hk (s • u) 0)) (Icc s₀ 1) :=
      hChc.comp (continuous_id.smul continuous_const).continuousOn fun s hs =>
        (hle s hs).trans (by rw [hsqη]; exact le_max_right _ _)
    have hglt : ∀ s ∈ Icc s₀ 1,
        g ((D.chart p hp).χ (recombine (D.chart p hp).hk (s • u) 0)) < f p := by
      intro s hs
      rw [(hgD' _ ((hle s hs).trans hRD')).2, hgp, hns s hs]
      have : 0 < s * ‖u‖ := mul_pos (hs₀pos.trans_le hs.1) hupos
      have := pow_pos this 2
      linarith
    have hfA : f ((D.chart p hp).χ (recombine (D.chart p hp).hk (s₀ • u) 0)) ≤ f p := by
      have hn : ‖s₀ • u‖ = Real.sqrt (2 * ε) := by rw [hns s₀ ⟨le_rfl, hs₀1⟩, hs₀u]
      rw [(hfD _ (by rw [hn]; exact hRD)).2]
      linarith [sq_nonneg ‖s₀ • u‖]
    have h1 := hconn _ s₀ 1 hγc hglt hfA 1 ⟨hs₀1, le_rfl⟩
    simp only [one_smul] at h1
    have hg1 := (hgD' u (hu'.trans hRD')).2
    rw [hfg _ h1] at hg1
    rw [hg1, hgp]
  have hVeq : ∀ z, f z < f p → a ≤ f z → f z ≤ f p - η → D'.V z = D.V z := by
    intro z hz1 hz2 hz3
    have hgz : g z = f z := hfg z hz1.le
    have hev : g =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_lt hf.continuous continuous_const).mem_nhds hz1] with w hw
      exact hfg w (le_of_lt hw)
    have hε1 : ε ≤ η := le_max_left _ _
    have hε2 : ε' ≤ η := le_max_right _ _
    have h1 : dfV I f D.V z = -1 :=
      D.unit z ⟨hz2, by linarith [hfpab.2]⟩ fun x hx => hU z ⟨hz2, by linarith⟩ x hx
    have h2 : dfV I g D'.V z = -1 :=
      D'.unit z ⟨by rw [hgz]; exact hz2, by rw [hgz]; linarith [hfpab.2]⟩ fun x hx =>
        hU' z ⟨by rw [hgz]; exact hz2, by rw [hgz, hgp]; linarith⟩ x hx
    have h3 : dfV I g D'.V z = φ z * dfV I f D.V z := by
      unfold dfV
      rw [hev.mfderiv_eq, hφV z hz1.le]
      simp only [map_smul, smul_eq_mul]
      rfl
    have hφ1 : φ z = 1 := by rw [h3, h1] at h2; linarith
    rw [hφV z hz1.le, hφ1, one_smul]
  have hagree : ∀ (x : M) (T : ℝ), 0 < T →
      (∀ s ∈ Icc 0 T, D'.V (D.flow s x) = D.V (D.flow s x)) →
      ∀ s ∈ Icc 0 T, D'.flow s x = D.flow s x := by
    intro x T hT hV
    let γ : ℝ → M := fun t => if t ≤ 0 then D'.flow t x else D.flow t x
    have hγD : ∀ t, 0 ≤ t → γ t = D.flow t x := by
      intro t ht
      by_cases h : t ≤ 0
      · have h0 : t = 0 := le_antisymm h ht
        subst h0
        simp only [γ, le_refl, ↓reduceIte, D.flow_zero, D'.flow_zero]
      · simp only [γ, h, ↓reduceIte]
    have hγD' : ∀ t, t ≤ 0 → γ t = D'.flow t x := fun t ht => by simp only [γ, ht, ↓reduceIte]
    have hint : IsMIntegralCurveOn γ D'.V (Ioo (-1) T) := by
      intro t ht
      apply HasMFDerivAt.hasMFDerivWithinAt
      rcases lt_trichotomy t 0 with h | h | h
      · have hev : γ =ᶠ[𝓝 t] (fun t => D'.flow t x) := by
          filter_upwards [Iio_mem_nhds h] with u hu using hγD' u hu.le
        have := (D'.isMIntegralCurve_flow x t).congr_of_eventuallyEq_abuse hev
        rw [hγD' t h.le]
        exact this
      · subst h
        have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Iic 0) 0
            ((1 : ℝ →L[ℝ] ℝ).smulRight (D'.V (γ 0))) := by
          have := ((D'.isMIntegralCurve_flow x 0).hasMFDerivWithinAt (s := Iic 0)).congr_mono
            (fun u hu => hγD' u hu) (hγD' 0 le_rfl) subset_rfl
          rw [hγD' 0 le_rfl]
          exact this
        have h2 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) 0
            ((1 : ℝ →L[ℝ] ℝ).smulRight (D'.V (γ 0))) := by
          have := ((D.isMIntegralCurve_flow x 0).hasMFDerivWithinAt (s := Ici 0)).congr_mono
            (fun u hu => hγD u hu) (hγD 0 le_rfl) subset_rfl
          rw [hγD 0 le_rfl, hV 0 ⟨le_rfl, hT.le⟩]
          exact this
        have h3 := h1.union h2
        rw [Iic_union_Ici] at h3
        exact hasMFDerivWithinAt_univ.1 h3
      · have hev : γ =ᶠ[𝓝 t] (fun t => D.flow t x) := by
          filter_upwards [Ioi_mem_nhds h] with u hu using hγD u hu.le
        have := (D.isMIntegralCurve_flow x t).congr_of_eventuallyEq_abuse hev
        rw [hγD t h.le, hV t ⟨h.le, ht.2.le⟩]
        exact this
    have hint' : IsMIntegralCurveOn (fun t => D'.flow t x) D'.V (Ioo (-1) T) :=
      fun t _ => (D'.isMIntegralCurve_flow x t).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := -1 / 2) ⟨by norm_num, by linarith⟩ D'.smooth_one hint hint'
      (hγD' _ (by norm_num))
    have hcl : IsClosed {s : ℝ | D'.flow s x = D.flow s x} :=
      isClosed_eq (D'.continuous_flow_curve x) (D.continuous_flow_curve x)
    have hsub : Ioo 0 T ⊆ {s : ℝ | D'.flow s x = D.flow s x} := by
      intro s hs
      have := heq ⟨by linarith [hs.1], hs.2⟩
      change D'.flow s x = D.flow s x
      rw [← hγD s hs.1.le]
      exact this.symm
    intro s hs
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioo hT.ne] at this
    exact this hs
  have hε1 : ε ≤ η := le_max_left _ _
  have hε2 : ε' ≤ η := le_max_right _ _
  have hnsp : ∀ e : ℝ, ∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k), y ≠ 0 →
      ‖(Real.sqrt (2 * e) / ‖y‖) • y‖ = Real.sqrt (2 * e) := by
    intro e y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hy'.le)]
    field_simp
  have hsqle : ∀ e, e ≤ η → Real.sqrt (2 * e) ≤ Real.sqrt (2 * η) := fun e he =>
    Real.sqrt_le_sqrt (by linarith)
  have hfx₀ : ∀ e, 0 ≤ e → e ≤ η → ∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k), y ≠ 0 →
      f (Ch (Real.sqrt (2 * e) / ‖y‖) y) = f p - e := by
    intro e he0 he y hy
    have := hfray _ ((hnsp e y hy).le.trans (hsqle e he))
    rw [hnsp e y hy, Real.sq_sqrt (by linarith)] at this
    rw [show f p - e = f p - 2 * e / 2 by ring, ← this]
  have hflowD : ∀ e, ε ≤ e → e ≤ η → ∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k), y ≠ 0 →
      ∀ s ∈ Icc 0 (f p - e - a), f (D.flow s (Ch (Real.sqrt (2 * e) / ‖y‖) y)) = f p - e - s := by
    intro e he1 he2 y hy s hs
    have hx := hfx₀ e (by linarith) he2 y hy
    have := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hf
      (x := Ch (Real.sqrt (2 * e) / ‖y‖) y) (T := f p - e - a)
      (by rw [hx]; exact ⟨by linarith, by linarith [hfpab.2]⟩)
      (by rw [hx]; exact ⟨by linarith, by linarith [hfpab.2]⟩)
      (fun z hz x' hx' => hU z (by
        rw [hx, uIcc_of_ge (by linarith)] at hz
        exact ⟨by linarith [hz.1], by linarith [hz.2]⟩) x' hx')
      s (by rw [uIcc_of_le (by linarith [hs.2, hs.1])]; exact hs)
    rw [this, hx]
  have hflowD' : ∀ e, ε' ≤ e → e ≤ η → ∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k), y ≠ 0 →
      ∀ s ∈ Icc 0 (f p - e - a), f (D'.flow s (Ch (Real.sqrt (2 * e) / ‖y‖) y)) = f p - e - s := by
    intro e he1 he2 y hy s hs
    have hx := hfx₀ e (by linarith) he2 y hy
    have hgx : g (Ch (Real.sqrt (2 * e) / ‖y‖) y) = f p - e := by
      rw [hfg _ (by rw [hx]; linarith), hx]
    have hgs : ∀ s ∈ Icc 0 (f p - e - a),
        g (D'.flow s (Ch (Real.sqrt (2 * e) / ‖y‖) y)) = f p - e - s := by
      intro s hs
      have := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D') hg
        (x := Ch (Real.sqrt (2 * e) / ‖y‖) y) (T := f p - e - a)
        (by rw [hgx]; exact ⟨by linarith, by linarith [hfpab.2]⟩)
        (by rw [hgx]; exact ⟨by linarith, by linarith [hfpab.2]⟩)
        (fun z hz x' hx' => hU' z (by
          rw [hgx, uIcc_of_ge (by linarith)] at hz
          exact ⟨by linarith [hz.1], by rw [hgp]; linarith [hz.2]⟩) x' hx')
        s (by rw [uIcc_of_le (by linarith [hs.2, hs.1])]; exact hs)
      rw [this, hgx]
    have hle := hconn (fun s => D'.flow s (Ch (Real.sqrt (2 * e) / ‖y‖) y)) 0 s
      (D'.continuous_flow_curve _).continuousOn
      (fun s' hs' => by
        rw [hgs s' ⟨hs'.1, hs'.2.trans hs.2⟩]; linarith [hs'.1])
      (by simp only [D'.flow_zero]; rw [hx]; linarith) s ⟨hs.1, le_rfl⟩
    rw [← hfg _ hle, hgs s hs]
  have hE : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart p hp).k)) 1,
      D'.leftDiscMap p (D.chart p hp).k η a y = D.leftDiscMap p (D.chart p hp).k η a y := by
    intro y hy
    rw [hDdisc, hD'disc]
    split_ifs with h
    · rfl
    rw [not_le] at h
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    have hT : 0 < f p - η - a := by linarith
    refine hagree _ (f p - η - a) hT (fun s hs => ?_) _
      ⟨mul_nonneg (by linarith) hT.le, mul_le_of_le_one_left hT.le (by linarith)⟩
    have hfz := hflowD η hε1 le_rfl y hy0 s hs
    exact hVeq _ (by rw [hfz]; linarith [hs.1, hε]) (by rw [hfz]; linarith [hs.2])
      (by rw [hfz]; linarith [hs.1])
  have hcontgen : ∀ (Fl : ℝ → M → M), Continuous (fun q : ℝ × M => Fl q.1 q.2) →
      (∀ x, Fl 0 x = x) → ∀ (e : ℝ → ℝ), Continuous e → (∀ t ∈ Icc (0 : ℝ) 1, 0 < e t ∧ e t ≤ η) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
        if ‖q.2‖ ≤ 1 / 2 then Ch (2 * Real.sqrt (2 * e q.1)) q.2
        else Fl ((2 * ‖q.2‖ - 1) * (f p - e q.1 - a)) (Ch (Real.sqrt (2 * e q.1) / ‖q.2‖) q.2))
        (Icc 0 1 ×ˢ Metric.closedBall 0 1) := by
    intro Fl hFl hFl0 e he hebd
    have hnc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) => ‖q.2‖) :=
      continuous_norm.comp continuous_snd
    have hsq : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
        Real.sqrt (2 * e q.1)) :=
      Real.continuous_sqrt.comp (continuous_const.mul (he.comp continuous_fst))
    apply ContinuousOn.if
    · rintro q ⟨hq, hqf⟩
      have h12 : ‖q.2‖ = 1 / 2 := frontier_le_subset_eq hnc continuous_const hqf
      rw [h12, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, zero_mul, hFl0]
      congr 1
      ring
    · have hcl : closure {q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) | ‖q.2‖ ≤ 1 / 2} =
          {q | ‖q.2‖ ≤ 1 / 2} := (isClosed_le hnc continuous_const).closure_eq
      rw [hcl]
      refine hChc.comp ((hsq.const_mul 2).smul continuous_snd).continuousOn ?_
      rintro q ⟨⟨hq1, -⟩, hq2⟩
      change ‖q.2‖ ≤ 1 / 2 at hq2
      change ‖(2 * Real.sqrt (2 * e q.1)) • q.2‖ ≤ Real.sqrt (2 * η)
      have hb := hebd q.1 hq1
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc 2 * Real.sqrt (2 * e q.1) * ‖q.2‖ ≤ 2 * Real.sqrt (2 * e q.1) * (1 / 2) := by
            gcongr
        _ = Real.sqrt (2 * e q.1) := by ring
        _ ≤ Real.sqrt (2 * η) := hsqle _ hb.2
    · have hcl : closure {q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) | ¬ ‖q.2‖ ≤ 1 / 2} ⊆
          {q | 1 / 2 ≤ ‖q.2‖} := by
        simp only [not_le]
        exact closure_lt_subset_le continuous_const hnc
      have hsub : Icc 0 1 ×ˢ Metric.closedBall 0 1 ∩
          closure {q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) | ¬ ‖q.2‖ ≤ 1 / 2} ⊆
          {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ 1 / 2 ≤ ‖q.2‖} := fun q hq => ⟨hq.1.1, hcl hq.2⟩
      refine ContinuousOn.mono ?_ hsub
      have hne : ∀ q ∈ {q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) |
          q.1 ∈ Icc (0 : ℝ) 1 ∧ 1 / 2 ≤ ‖q.2‖}, ‖q.2‖ ≠ 0 := fun q hq => by
        have := hq.2; positivity
      have hu : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
          (Real.sqrt (2 * e q.1) / ‖q.2‖) • q.2)
          {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ 1 / 2 ≤ ‖q.2‖} :=
        (hsq.continuousOn.div hnc.continuousOn hne).smul continuous_snd.continuousOn
      have hP : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
          Ch (Real.sqrt (2 * e q.1) / ‖q.2‖) q.2)
          {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ 1 / 2 ≤ ‖q.2‖} := by
        refine hChc.comp hu ?_
        intro q hq
        have hq0 : q.2 ≠ 0 := fun h0 => hne q hq (by rw [h0, norm_zero])
        change ‖(Real.sqrt (2 * e q.1) / ‖q.2‖) • q.2‖ ≤ Real.sqrt (2 * η)
        rw [hnsp _ _ hq0]
        exact hsqle _ (hebd q.1 hq.1).2
      have hτ : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
          (2 * ‖q.2‖ - 1) * (f p - e q.1 - a)) :=
        ((continuous_const.mul hnc).sub continuous_const).mul
          ((continuous_const.sub (he.comp continuous_fst)).sub continuous_const)
      exact hFl.comp_continuousOn (hτ.continuousOn.prodMk hP)
  have hrangegen : ∀ (Fl : ℝ → M → M) (e : ℝ), 0 < e → e ≤ η →
      (∀ y : EuclideanSpace ℝ (Fin (D.chart p hp).k), y ≠ 0 → ∀ s ∈ Icc 0 (f p - e - a),
        f (Fl s (Ch (Real.sqrt (2 * e) / ‖y‖) y)) = f p - e - s) →
      MapsTo (fun y : EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
        if ‖y‖ ≤ 1 / 2 then Ch (2 * Real.sqrt (2 * e)) y
        else Fl ((2 * ‖y‖ - 1) * (f p - e - a)) (Ch (Real.sqrt (2 * e) / ‖y‖) y))
        (Metric.closedBall 0 1) (f ⁻¹' Icc a c) ∧
      MapsTo (fun y : EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
        if ‖y‖ ≤ 1 / 2 then Ch (2 * Real.sqrt (2 * e)) y
        else Fl ((2 * ‖y‖ - 1) * (f p - e - a)) (Ch (Real.sqrt (2 * e) / ‖y‖) y))
        (Metric.sphere 0 1) (f ⁻¹' {a}) := by
    intro Fl e he0 heη hFl
    constructor
    · intro y hy
      have hy1 : ‖y‖ ≤ 1 := by simpa using hy
      simp only [mem_preimage]
      split_ifs with h
      · have hn : ‖(2 * Real.sqrt (2 * e)) • y‖ ≤ Real.sqrt (2 * η) := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          calc 2 * Real.sqrt (2 * e) * ‖y‖ ≤ 2 * Real.sqrt (2 * e) * (1 / 2) := by gcongr
            _ = Real.sqrt (2 * e) := by ring
            _ ≤ Real.sqrt (2 * η) := hsqle _ heη
        have hf1 := hfray _ hn
        have hsq : ‖(2 * Real.sqrt (2 * e)) • y‖ ^ 2 ≤ 2 * η := by
          have h0 := pow_le_pow_left₀ (norm_nonneg _) hn 2
          rwa [Real.sq_sqrt (by linarith)] at h0
        change f (Ch (2 * Real.sqrt (2 * e)) y) ∈ Icc a c
        exact ⟨by rw [hf1]; linarith, by rw [hf1]; linarith [sq_nonneg ‖(2 * Real.sqrt (2 * e)) • y‖]⟩
      · rw [not_le] at h
        have hy0 : y ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
        have hT : 0 ≤ f p - e - a := by linarith
        have hs0 : 0 ≤ (2 * ‖y‖ - 1) * (f p - e - a) := mul_nonneg (by linarith) hT
        have hs1 : (2 * ‖y‖ - 1) * (f p - e - a) ≤ f p - e - a :=
          mul_le_of_le_one_left hT (by linarith)
        rw [hFl y hy0 _ ⟨hs0, hs1⟩]
        exact ⟨by linarith, by linarith⟩
    · intro y hy
      have hy1 : ‖y‖ = 1 := by simpa using hy
      have hy0 : y ≠ 0 := fun h0 => by rw [h0, norm_zero] at hy1; linarith
      have hn : ¬ ‖y‖ ≤ 1 / 2 := by rw [hy1]; norm_num
      have hT : 0 ≤ f p - e - a := by linarith
      simp only [mem_preimage, mem_singleton_iff, hn, ↓reduceIte]
      rw [show (2 * ‖y‖ - 1) * (f p - e - a) = f p - e - a by rw [hy1]; ring,
        hFl y hy0 _ ⟨hT, le_rfl⟩]
      ring
  have he1 : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ε' + t * (η - ε') ∧ ε' + t * (η - ε') ≤ η ∧
      ε' ≤ ε' + t * (η - ε') := fun t ht => by
    have h1 : 0 ≤ t * (η - ε') := mul_nonneg ht.1 (by linarith)
    have h2 : t * (η - ε') ≤ η - ε' := mul_le_of_le_one_left (by linarith) ht.2
    exact ⟨by linarith, by linarith, by linarith⟩
  have he2 : ∀ t ∈ Icc (0 : ℝ) 1, 0 < η + t * (ε - η) ∧ η + t * (ε - η) ≤ η ∧
      ε ≤ η + t * (ε - η) := fun t ht => by
    have h1 : t * (ε - η) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 (by linarith)
    have h2 : 1 * (ε - η) ≤ t * (ε - η) := mul_le_mul_of_nonpos_right ht.2 (by linarith)
    exact ⟨by linarith, by linarith, by linarith⟩
  refine (Handle.discClass_eq_of_homotopy (f ⁻¹' Icc a c) (f ⁻¹' {a})
    (D'.leftDiscMap p (D.chart p hp).k ε' a) (D.leftDiscMap p (D.chart p hp).k η a)
    (fun t y => D'.leftDiscMap p (D.chart p hp).k (ε' + t * (η - ε')) a y) ?_ ?_ ?_ ?_ ?_ gD).trans
    (Handle.discClass_eq_of_homotopy (f ⁻¹' Icc a c) (f ⁻¹' {a})
    (D.leftDiscMap p (D.chart p hp).k η a) (D.leftDiscMap p (D.chart p hp).k ε a)
    (fun t y => D.leftDiscMap p (D.chart p hp).k (η + t * (ε - η)) a y) ?_ ?_ ?_ ?_ ?_ gD)
  · simp only [hD'disc]
    exact hcontgen D'.flow D'.continuous_flow_joint D'.flow_zero (fun t => ε' + t * (η - ε'))
      (continuous_const.add (continuous_id.mul continuous_const))
      fun t ht => ⟨(he1 t ht).1, (he1 t ht).2.1⟩
  · intro y _
    simp only [zero_mul, add_zero]
  · intro y hy
    simp only [one_mul, add_sub_cancel]
    exact hE y hy
  · intro t ht y hy
    have := (hrangegen D'.flow _ (he1 t ht).1 (he1 t ht).2.1
      (fun y hy s hs => hflowD' _ (he1 t ht).2.2 (he1 t ht).2.1 y hy s hs)).1 hy
    simp only [hD'disc]
    exact this
  · intro t ht y hy
    have := (hrangegen D'.flow _ (he1 t ht).1 (he1 t ht).2.1
      (fun y hy s hs => hflowD' _ (he1 t ht).2.2 (he1 t ht).2.1 y hy s hs)).2 hy
    simp only [hD'disc]
    exact this
  · simp only [hDdisc]
    exact hcontgen D.flow D.continuous_flow_joint D.flow_zero (fun t => η + t * (ε - η))
      (continuous_const.add (continuous_id.mul continuous_const))
      fun t ht => ⟨(he2 t ht).1, (he2 t ht).2.1⟩
  · intro y _
    simp only [zero_mul, add_zero]
  · intro y _
    simp only [one_mul, add_sub_cancel]
  · intro t ht y hy
    have := (hrangegen D.flow _ (he2 t ht).1 (he2 t ht).2.1
      (fun y hy s hs => hflowD _ (he2 t ht).2.2 (he2 t ht).2.1 y hy s hs)).1 hy
    simp only [hDdisc]
    exact this
  · intro t ht y hy
    have := (hrangegen D.flow _ (he2 t ht).1 (he2 t ht).2.1
      (fun y hy s hs => hflowD _ (he2 t ht).2.2 (he2 t ht).2.1 y hy s hs)).2 hy
    simp only [hDdisc]
    exact this

end GradientLikeStrip

def coordN {m : ℕ} (y : Fin m → ℝ) (j : ℕ) : ℝ := if h : j < m then y ⟨j, h⟩ else 0

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

structure CollarChart (D : GradientLikeStrip I f a b crit) (c κ : ℝ) where
  U : Set (Fin (n - 1) → ℝ)
  isOpen_U : IsOpen U
  φ : (Fin (n - 1) → ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ φ U
  immersion : ∀ y ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ y)
  inj : InjOn φ U
  level : ∀ y ∈ U, f (φ y) = c
  open_image : ∀ V ⊆ U, IsOpen V → ∃ G : Set M, IsOpen G ∧ φ '' V = G ∩ f ⁻¹' {c}
  hκ : 0 < κ
  strip : a ≤ c - κ ∧ c + κ ≤ b
  avoid : ∀ y ∈ U, ∀ s ∈ Icc (-κ) κ, ∀ x (hx : x ∈ crit),
    D.flow s (φ y) ∉ (D.chart x hx).χ '' {z | morseNorm n z < D.rm x hx}

def CollarChart.realizes {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ)
    (K : Set (Fin (n - 1) → ℝ)) (H₁ : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ))
    (Z : (x : M) → TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)) ∧
    IsCompact (tsupport Z) ∧ (∀ x, dfV I f Z x = 0) ∧
    tsupport Z ⊆ (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (K ×ˢ Ioo (-κ) κ) ∧
    ∀ E : GradientLikeStrip I f a b crit, (∀ x, E.V x = D.V x + Z x) →
      ∀ y ∈ Ch.U, E.flow (2 * κ) (D.flow (-κ) (Ch.φ y)) = D.flow κ (Ch.φ (H₁ y))

theorem CollarChart.exists_boxInverse (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ) :
    (∀ V ⊆ Ch.U ×ˢ Ioo (-κ) κ, IsOpen V →
        IsOpen ((fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' V)) ∧
      ∃ inv : M → (Fin (n - 1) → ℝ) × ℝ,
        ContMDiffOn I 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) ∞ inv
          ((fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (Ch.U ×ˢ Ioo (-κ) κ)) ∧
        ∀ p ∈ Ch.U ×ˢ Ioo (-κ) κ, inv (D.flow p.2 (Ch.φ p.1)) = p := by
  classical
  set W : Set ((Fin (n - 1) → ℝ) × ℝ) := Ch.U ×ˢ Ioo (-κ) κ with hW
  set box : (Fin (n - 1) → ℝ) × ℝ → M := fun p => D.flow p.2 (Ch.φ p.1) with hbox_def
  have hWo : IsOpen W := Ch.isOpen_U.prod isOpen_Ioo
  have hbox : ContMDiffOn 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I ∞ box W := by
    have h1 : ContMDiffOn 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : (Fin (n - 1) → ℝ) × ℝ => (p.2, Ch.φ p.1)) W := by
      refine ContMDiffOn.prodMk ?_ ?_
      · exact (contDiff_snd.contMDiff).contMDiffOn
      · refine Ch.smooth.comp (contDiff_fst.contMDiff).contMDiffOn ?_
        intro p hp
        exact hp.1
    exact D.contMDiff_flow_joint.comp_contMDiffOn h1
  have hlev : ∀ p ∈ W, f (box p) = c - p.2 := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    have hx : f (Ch.φ y) ∈ Icc a b := by
      rw [Ch.level y hy]
      constructor <;> linarith [Ch.strip.1, Ch.strip.2, Ch.hκ]
    have hxT : f (Ch.φ y) - s ∈ Icc a b := by
      rw [Ch.level y hy]
      constructor <;> linarith [Ch.strip.1, Ch.strip.2, hs.1, hs.2]
    have h := f_flow_eq_sub_of_avoid_uIcc (D := D) hf hx hxT (by
      intro u hu p hp hmem
      have hu' : u ∈ Icc (-κ) κ := by
        rcases le_total 0 s with h0 | h0
        · rw [uIcc_of_le h0] at hu
          exact ⟨by linarith [hu.1, Ch.hκ], by linarith [hu.2, hs.2]⟩
        · rw [uIcc_of_ge h0] at hu
          exact ⟨by linarith [hu.1, hs.1], by linarith [hu.2, Ch.hκ]⟩
      refine Ch.avoid y hy u hu' p hp ?_
      obtain ⟨z, hz, hz'⟩ := hmem
      exact ⟨z, lt_trans hz (D.r₀_lt_rm p hp), hz'⟩)
    have := h s right_mem_uIcc
    simpa [box, Ch.level y hy] using this
  have hinj : InjOn box W := by
    rintro ⟨y, s⟩ hp ⟨y', s'⟩ hq heq
    have hs : s = s' := by
      have h1 := hlev _ hp
      have h2 := hlev _ hq
      rw [heq] at h1
      simp only at h1 h2
      linarith
    subst hs
    have h3 : D.flow s (Ch.φ y) = D.flow s (Ch.φ y') := heq
    have := D.flow_injective s h3
    exact Prod.ext (Ch.inj hp.1 hq.1 this) rfl
  have hderiv : ∀ p₀ ∈ W,
      Function.Injective (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p₀) := by
    rintro ⟨y₀, s₀⟩ hp₀
    have hmd : MDifferentiableAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y₀, s₀) :=
      ((hbox _ hp₀).contMDiffAt (hWo.mem_nhds hp₀)).mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (box (y₀, s₀)) :=
      (hf _).mdifferentiableAt (by simp)
    have hev : (f ∘ box) =ᶠ[𝓝 (y₀, s₀)] (fun p : (Fin (n - 1) → ℝ) × ℝ => c - p.2) :=
      eventuallyEq_of_mem (hWo.mem_nhds hp₀) (fun p hp => hlev p hp)
    have hcomp := mfderiv_comp (y₀, s₀) hfd hmd
    have h2 := hev.mfderiv_eq (I := 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ)) (I' := 𝓘(ℝ, ℝ))
    rw [mfderiv_eq_fderiv (f := fun p : (Fin (n - 1) → ℝ) × ℝ => c - p.2),
      (hasFDerivAt_snd.const_sub c).fderiv] at h2
    have hφd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ y₀ :=
      (Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hp₀.1)).mdifferentiableAt (by simp)
    have hfl : ∀ t : ℝ, ∀ z : M, MDifferentiableAt I I (D.flow t) z :=
      fun t z => (D.contMDiff_flow t z).mdifferentiableAt (by simp)
    have hflinj : Function.Injective (mfderiv I I (D.flow s₀) (Ch.φ y₀)) := by
      have hid : (D.flow (-s₀) ∘ D.flow s₀) = id := funext fun z => D.flow_neg_flow z s₀
      have hc := mfderiv_comp (Ch.φ y₀) (hfl (-s₀) (D.flow s₀ (Ch.φ y₀))) (hfl s₀ (Ch.φ y₀))
      rw [hid, mfderiv_id] at hc
      intro u₁ u₂ hu
      have e1 : u₁ = mfderiv I I (D.flow (-s₀)) (D.flow s₀ (Ch.φ y₀))
          (mfderiv I I (D.flow s₀) (Ch.φ y₀) u₁) := DFunLike.congr_fun hc u₁
      have e2 : u₂ = mfderiv I I (D.flow (-s₀)) (D.flow s₀ (Ch.φ y₀))
          (mfderiv I I (D.flow s₀) (Ch.φ y₀) u₂) := DFunLike.congr_fun hc u₂
      exact e1.trans ((congrArg (mfderiv I I (D.flow (-s₀)) (D.flow s₀ (Ch.φ y₀))) hu).trans
        e2.symm)
    set ι : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ) × ℝ := fun y => (y, s₀) with hι
    have hιd : HasFDerivAt ι ((ContinuousLinearMap.id ℝ _).prod 0) y₀ :=
      (hasFDerivAt_id y₀).prodMk (hasFDerivAt_const s₀ y₀)
    have hιm : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) ι y₀ :=
      hιd.differentiableAt.mdifferentiableAt
    have hcι := mfderiv_comp y₀ hmd hιm
    have hbι : box ∘ ι = D.flow s₀ ∘ Ch.φ := rfl
    rw [hbι, mfderiv_comp y₀ (hfl s₀ (Ch.φ y₀)) hφd, mfderiv_eq_fderiv, hιd.fderiv] at hcι
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨v, t⟩ hw
    have ht : t = 0 := by
      have e1 : mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, ℝ) (f ∘ box) (y₀, s₀) (v, t) =
          mfderiv I 𝓘(ℝ, ℝ) f (box (y₀, s₀))
            (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y₀, s₀) (v, t)) :=
        DFunLike.congr_fun hcomp (v, t)
      have e2 : mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, ℝ) (f ∘ box) (y₀, s₀) (v, t) = -t :=
        DFunLike.congr_fun h2 (v, t)
      rw [hw, map_zero] at e1
      rw [e1] at e2
      have e3 : (0 : ℝ) = -t := e2
      exact neg_eq_zero.mp e3.symm
    subst ht
    have hv : v = 0 := by
      have e1 : mfderiv I I (D.flow s₀) (Ch.φ y₀) (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ y₀ v) =
          mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y₀, s₀) (v, 0) :=
        DFunLike.congr_fun hcι v
      rw [hw] at e1
      have e3 : mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ y₀ v = 0 :=
        hflinj (e1.trans (map_zero _).symm)
      exact Ch.immersion y₀ hp₀.1 (e3.trans (map_zero _).symm)
    rw [hv]
    rfl
  have key : ∀ p₀ ∈ W, ∃ Ψ : (Fin n → ℝ) → (Fin (n - 1) → ℝ) × ℝ,
      ContMDiffAt I 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) ∞ (Ψ ∘ extChartAt I (box p₀)) (box p₀) ∧
      ∀ N ∈ 𝓝 p₀, ∀ᶠ x in 𝓝 (box p₀), Ψ (extChartAt I (box p₀) x) ∈ N ∧
        box (Ψ (extChartAt I (box p₀) x)) = x := by
    intro p₀ hp₀
    set x₀ := box p₀ with hx₀
    set e := extChartAt I x₀ with he
    set g : (Fin (n - 1) → ℝ) × ℝ → (Fin n → ℝ) := e ∘ box with hg_def
    have hboxAt : ContMDiffAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I ∞ box p₀ :=
      (hbox _ hp₀).contMDiffAt (hWo.mem_nhds hp₀)
    have hmd : MDifferentiableAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p₀ :=
      hboxAt.mdifferentiableAt (by simp)
    have hgAt : ContDiffAt ℝ ∞ g p₀ := by
      have : ContMDiffAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ g p₀ :=
        contMDiffAt_extChartAt.comp p₀ hboxAt
      exact contMDiffAt_iff_contDiffAt.1 this
    have hfdg : fderiv ℝ g p₀ = (mfderiv I 𝓘(ℝ, Fin n → ℝ) e x₀).comp
        (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p₀) := by
      have hc := mfderiv_comp p₀ (mdifferentiableAt_extChartAt (mem_chart_source H x₀)) hmd
      rw [mfderiv_eq_fderiv] at hc
      apply ContinuousLinearMap.ext
      intro v
      exact DFunLike.congr_fun hc v
    have hinjg : Function.Injective (fderiv ℝ g p₀) := by
      intro w₁ w₂ hw
      apply hderiv p₀ hp₀
      have h := mfderiv_extChartAt_self (I := I) (x := x₀)
      rw [hfdg, h] at hw
      exact hw
    have hdim : Module.finrank ℝ ((Fin (n - 1) → ℝ) × ℝ) = Module.finrank ℝ (Fin n → ℝ) := by
      have hle := LinearMap.finrank_le_finrank_of_injective
        (f := (fderiv ℝ g p₀ : ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ))) hinjg
      simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at hle ⊢
      omega
    let F' : ((Fin (n - 1) → ℝ) × ℝ) ≃L[ℝ] (Fin n → ℝ) :=
      (LinearMap.linearEquivOfInjective
        (fderiv ℝ g p₀ : ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ)) hinjg
        hdim).toContinuousLinearEquiv
    have hF' : (F' : ((Fin (n - 1) → ℝ) × ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ g p₀ := by
      exact ContinuousLinearMap.ext fun w => rfl
    have hgd : HasFDerivAt g (F' : ((Fin (n - 1) → ℝ) × ℝ) →L[ℝ] (Fin n → ℝ)) p₀ := by
      rw [hF']
      exact (hgAt.differentiableAt (by simp)).hasFDerivAt
    have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hΨ : ContDiffAt ℝ ∞ (hgAt.localInverse hgd hn0) (g p₀) := hgAt.to_localInverse hgd hn0
    have hs : HasStrictFDerivAt g (F' : ((Fin (n - 1) → ℝ) × ℝ) →L[ℝ] (Fin n → ℝ)) p₀ :=
      hgAt.hasStrictFDerivAt' hgd hn0
    refine ⟨hgAt.localInverse hgd hn0, ?_, ?_⟩
    · exact hΨ.contMDiffAt.comp x₀ contMDiffAt_extChartAt
    · intro N hN
      have hN' : N ∩ box ⁻¹' e.source ∈ 𝓝 p₀ :=
        inter_mem hN (hboxAt.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds x₀))
      have h1 : ∀ᶠ z in 𝓝 (g p₀), hs.localInverse g F' p₀ z ∈ N ∩ box ⁻¹' e.source ∧
          g (hs.localInverse g F' p₀ z) = z :=
        (hs.localInverse_tendsto.eventually hN').and hs.eventually_right_inverse
      have h2 := (continuousAt_extChartAt (I := I) x₀).eventually h1
      filter_upwards [h2, extChartAt_source_mem_nhds (I := I) x₀] with x hx hxs
      exact ⟨hx.1.1, e.injOn hx.1.2 hxs hx.2⟩
  refine ⟨?_, Function.invFunOn box W, ?_, ?_⟩
  · intro V hVW hVo
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨p₀, hp₀V, rfl⟩
    obtain ⟨Ψ, -, hΨ⟩ := key p₀ (hVW hp₀V)
    filter_upwards [hΨ V (hVo.mem_nhds hp₀V)] with x hx
    exact ⟨_, hx.1, hx.2⟩
  · rintro x ⟨p₀, hp₀, rfl⟩
    obtain ⟨Ψ, hsm, hΨ⟩ := key p₀ hp₀
    have heq : Function.invFunOn box W =ᶠ[𝓝 (box p₀)] (Ψ ∘ extChartAt I (box p₀)) := by
      filter_upwards [hΨ W (hWo.mem_nhds hp₀)] with x hx
      have := hinj.leftInvOn_invFunOn hx.1
      rw [hx.2] at this
      exact this
    exact (hsm.congr_of_eventuallyEq heq).contMDiffWithinAt
  · intro p hp
    exact hinj.leftInvOn_invFunOn hp

end GradientLikeStrip

theorem exists_isotopy_generator {m : ℕ} {K : Set (Fin m → ℝ)} (hK : IsCompact K)
    (Hs : ℝ → (Fin m → ℝ) → (Fin m → ℝ))
    (hHs : ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => Hs p.1 p.2))
    (hbij : ∀ t, Function.Bijective (Hs t))
    (hdiff : ∀ t y, Function.Bijective (fderiv ℝ (Hs t) y))
    (hsupp : ∀ t y, y ∉ K → Hs t y = y) (h0 : ∀ t, t ≤ 0 → ∀ y, Hs t y = y)
    (h1 : ∀ t, 1 ≤ t → ∀ y, Hs t y = Hs 1 y) :
    ∃ Y : ℝ → (Fin m → ℝ) → (Fin m → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => Y p.1 p.2) ∧ (∀ t y, y ∉ K → Y t y = 0) ∧
      (∀ t y, (t ≤ 0 ∨ 1 ≤ t) → Y t y = 0) ∧
      ∀ t y, HasDerivAt (fun s => Hs s y) (Y t (Hs t y)) t := by
  classical
  have _ := hK
  set F : ℝ × (Fin m → ℝ) → (Fin m → ℝ) := fun p => Hs p.1 p.2 with hFdef
  set Φ : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) := fun p => (p.1, F p) with hΦdef
  have hΦsmooth : ContDiff ℝ ∞ Φ := contDiff_fst.prodMk hHs
  have hFstrict : ∀ p, HasStrictFDerivAt F (fderiv ℝ F p) p := fun p =>
    hHs.contDiffAt.hasStrictFDerivAt (by simp)
  have hΦstrict : ∀ p, HasStrictFDerivAt Φ
      ((ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).prod (fderiv ℝ F p)) p := fun p =>
    hasStrictFDerivAt_fst.prodMk (hFstrict p)
  have hpartial : ∀ (t : ℝ) (y v : Fin m → ℝ),
      fderiv ℝ F (t, y) (0, v) = fderiv ℝ (Hs t) y v := by
    intro t y v
    have h1 : HasFDerivAt (fun z : Fin m → ℝ => F (t, z))
        ((fderiv ℝ F (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin m → ℝ))) y :=
      (hFstrict (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
    have h2 : (fun z : Fin m → ℝ => F (t, z)) = Hs t := rfl
    rw [h2] at h1
    rw [h1.fderiv]
    simp
  have hLbij : ∀ p : ℝ × (Fin m → ℝ), Function.Bijective
      ((ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).prod (fderiv ℝ F p)) := by
    rintro ⟨t, y⟩
    obtain ⟨hinj, hsurj⟩ := hdiff t y
    have hsplit : ∀ u : ℝ, ∀ v : Fin m → ℝ,
        fderiv ℝ F (t, y) (u, v) = fderiv ℝ F (t, y) (u, 0) + fderiv ℝ (Hs t) y v := by
      intro u v
      rw [← hpartial, ← map_add]
      simp
    refine ⟨?_, ?_⟩
    · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.mk.injEq] at h
      obtain ⟨hu, hv⟩ := h
      subst hu
      rw [hsplit u₁ v₁, hsplit u₁ v₂] at hv
      have := hinj (add_left_cancel hv)
      rw [this]
    · rintro ⟨u, w⟩
      obtain ⟨v, hv⟩ := hsurj (w - fderiv ℝ F (t, y) (u, 0))
      refine ⟨(u, v), ?_⟩
      refine Prod.ext rfl ?_
      change fderiv ℝ F (t, y) (u, v) = w
      rw [hsplit, hv]
      abel
  let L : ℝ × (Fin m → ℝ) → (ℝ × (Fin m → ℝ)) ≃L[ℝ] (ℝ × (Fin m → ℝ)) := fun p =>
    (LinearEquiv.ofBijective
      (((ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).prod (fderiv ℝ F p)) :
        (ℝ × (Fin m → ℝ)) →ₗ[ℝ] (ℝ × (Fin m → ℝ))) (hLbij p)).toContinuousLinearEquiv
  have hLcoe : ∀ p, (L p : (ℝ × (Fin m → ℝ)) →L[ℝ] (ℝ × (Fin m → ℝ))) =
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).prod (fderiv ℝ F p) := by
    intro p
    ext x <;> rfl
  have hΦstrict' : ∀ p, HasStrictFDerivAt Φ
      (L p : (ℝ × (Fin m → ℝ)) →L[ℝ] (ℝ × (Fin m → ℝ))) p := fun p => by
    rw [hLcoe]; exact hΦstrict p
  have hΦbij : Function.Bijective Φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨t₁, y₁⟩ ⟨t₂, y₂⟩ h
      simp only [hΦdef, hFdef, Prod.mk.injEq] at h
      obtain ⟨ht, hy⟩ := h
      subst ht
      rw [(hbij t₁).1 hy]
    · rintro ⟨t, z⟩
      obtain ⟨y, hy⟩ := (hbij t).2 z
      exact ⟨(t, y), by simp [hΦdef, hFdef, hy]⟩
  let e : (ℝ × (Fin m → ℝ)) ≃ₜ (ℝ × (Fin m → ℝ)) :=
    (Equiv.ofBijective Φ hΦbij).toHomeomorphOfContinuousOpen hΦsmooth.continuous
      (isOpenMap_of_hasStrictFDerivAt_equiv hΦstrict')
  have he : (e : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ)) = Φ := rfl
  have hesymm : ContDiff ℝ ∞ (e.symm : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ)) :=
    e.contDiff_symm (f₀' := L) (fun a => (hΦstrict' a).hasFDerivAt) (by rw [he]; exact hΦsmooth)
  have hinv1 : ∀ q : ℝ × (Fin m → ℝ), (e.symm q).1 = q.1 ∧ Hs q.1 (e.symm q).2 = q.2 := by
    intro q
    have h := e.apply_symm_apply q
    rw [he] at h
    have h1 : (e.symm q).1 = q.1 := by
      conv_rhs => rw [← h]
    refine ⟨h1, ?_⟩
    have h2 : F (e.symm q) = q.2 := by
      conv_rhs => rw [← h]
    rw [← h1]
    exact h2
  have hinv2 : ∀ t y, e.symm (t, Hs t y) = (t, y) := by
    intro t y
    have : e (t, y) = (t, Hs t y) := rfl
    rw [← this, e.symm_apply_apply]
  have hderiv : ∀ t y, HasDerivAt (fun s => Hs s y) (fderiv ℝ F (t, y) (1, 0)) t := by
    intro t y
    have hc : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : Fin m → ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (hFstrict (t, y)).hasFDerivAt.comp_hasDerivAt t hc
  have hderiv' : ∀ t z, HasDerivAt (fun s => Hs s (e.symm (t, z)).2)
      (fderiv ℝ F (e.symm (t, z)) (1, 0)) t := by
    intro t z
    have h := hderiv t (e.symm (t, z)).2
    have h1 : (e.symm (t, z)).1 = t := (hinv1 (t, z)).1
    have h3 : e.symm (t, z) = (t, (e.symm (t, z)).2) := by
      ext
      · exact h1
      · rfl
    rw [h3]
    exact h
  refine ⟨fun t z => fderiv ℝ F (e.symm (t, z)) (1, 0), ?_, ?_, ?_, ?_⟩
  · have hdF : ContDiff ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) :=
      (hHs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact hdF.comp (hesymm.comp (contDiff_fst.prodMk contDiff_snd))
  · intro t z hz
    obtain ⟨_, h2⟩ := hinv1 (t, z)
    set y := (e.symm (t, z)).2 with hy
    have hyK : y ∉ K := by
      intro hyK
      have hzfix : Hs t z = z := hsupp t z hz
      have : Hs t y = Hs t z := by rw [hzfix]; exact h2
      have := (hbij t).1 this
      exact hz (this ▸ hyK)
    have hconst : (fun s => Hs s y) = fun _ => y := funext fun s => hsupp s y hyK
    have h0' : HasDerivAt (fun s => Hs s y) 0 t := by
      rw [hconst]; exact hasDerivAt_const t y
    exact (hderiv' t z).unique h0'
  · intro t z ht
    set y := (e.symm (t, z)).2 with hy
    rcases ht with ht | ht
    · have hw : HasDerivWithinAt (fun s => Hs s y) 0 (Iic t) t :=
        (hasDerivWithinAt_const t (Iic t) y).congr
          (fun s hs => h0 s (le_trans hs ht) y) (h0 t ht y)
      exact (uniqueDiffWithinAt_Iic t).eq_deriv _ (hderiv' t z).hasDerivWithinAt hw
    · have hw : HasDerivWithinAt (fun s => Hs s y) 0 (Ici t) t :=
        (hasDerivWithinAt_const t (Ici t) (Hs 1 y)).congr
          (fun s hs => h1 s (le_trans ht hs) y) (h1 t ht y)
      exact (uniqueDiffWithinAt_Ici t).eq_deriv _ (hderiv' t z).hasDerivWithinAt hw
  · intro t y
    have h := hderiv t y
    simp only [hinv2]
    exact h

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem CollarChart.exists_boxField (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ)
    {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ Ch.U)
    (Y : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ))
    (hY : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n - 1) → ℝ) => Y p.1 p.2))
    (hYK : ∀ t y, y ∉ K → Y t y = 0) (hY01 : ∀ t y, (t ≤ 0 ∨ 1 ≤ t) → Y t y = 0) :
    ∃ lam : ℝ → ℝ, ContDiff ℝ ∞ lam ∧ (∀ s, s ≤ -κ / 2 → lam s = 0) ∧
      (∀ s, κ / 2 ≤ s → lam s = 1) ∧
      ∃ Z : (x : M) → TangentSpace I x,
        ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport Z) ∧ (∀ x, dfV I f Z x = 0) ∧
        tsupport Z ⊆ (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (K ×ˢ Ioo (-κ) κ) ∧
        ∀ y ∈ Ch.U, ∀ s ∈ Ioo (-κ) κ,
          Z (D.flow s (Ch.φ y)) = mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I
            (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) (y, s)
            (deriv lam s • Y (lam s) y, 0) := by
  classical
  have _ := hY01
  obtain ⟨hopen, inv, hinv, hinvl⟩ := Ch.exists_boxInverse hf
  have hκ := Ch.hκ
  set box : (Fin (n - 1) → ℝ) × ℝ → M := fun p => D.flow p.2 (Ch.φ p.1) with hboxdef
  set S : Set ((Fin (n - 1) → ℝ) × ℝ) := Ch.U ×ˢ Ioo (-κ) κ with hSdef
  have hSopen : IsOpen S := Ch.isOpen_U.prod isOpen_Ioo
  have hBopen : IsOpen (box '' S) := hopen S subset_rfl hSopen
  have hboxsmooth : ContMDiffOn 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I ∞ box S := by
    have h1 : ContMDiffOn 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : (Fin (n - 1) → ℝ) × ℝ => (p.2, Ch.φ p.1)) S := by
      refine ContMDiffOn.prodMk ?_ ?_
      · exact (contDiff_snd.contMDiff).contMDiffOn
      · exact Ch.smooth.comp (contDiff_fst.contMDiff).contMDiffOn fun p hp => hp.1
    exact D.contMDiff_flow_joint.comp_contMDiffOn h1
  have hlevel : ∀ q ∈ S, f (box q) = c - q.2 := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    have hfy : f (Ch.φ y) = c := Ch.level y hy
    have hsub : ∀ u ∈ uIcc 0 s, u ∈ Icc (-κ) κ := by
      intro u hu
      rcases mem_uIcc.1 hu with h | h <;> constructor <;> linarith [hs.1, hs.2, h.1, h.2]
    have key := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := s)
      (by rw [hfy]; constructor <;> linarith [Ch.strip.1, Ch.strip.2])
      (by rw [hfy]; constructor <;> linarith [Ch.strip.1, Ch.strip.2, hs.1, hs.2])
      (fun u hu p hp hmem => Ch.avoid y hy u (hsub u hu) p hp
        (image_mono (fun z hz => lt_trans hz (D.r₀_lt_rm p hp)) hmem)) s right_mem_uIcc
    rw [hfy] at key
    exact key
  set lam : ℝ → ℝ := fun s => Real.smoothTransition ((s + κ / 2) / κ) with hlamdef
  have hlam : ContDiff ℝ ∞ lam :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const κ)
  have hlam0 : ∀ s, s ≤ -κ / 2 → lam s = 0 := by
    intro s hs
    refine Real.smoothTransition.zero_of_nonpos ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hκ.le
  have hlam1 : ∀ s, κ / 2 ≤ s → lam s = 1 := by
    intro s hs
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hκ]
    linarith
  have hdlam : ContDiff ℝ ∞ (deriv lam) := (contDiff_infty_iff_deriv.1 hlam).2
  have hdlam0 : ∀ s, s ∉ Icc (-κ / 2) (κ / 2) → deriv lam s = 0 := by
    intro s hs
    rcases not_and_or.1 hs with h | h
    · have hev : lam =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (lt_of_not_ge h)] with u hu
        exact hlam0 u (le_of_lt hu)
      rw [hev.deriv_eq, deriv_const]
    · have hev : lam =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with u hu
        exact hlam1 u (le_of_lt hu)
      rw [hev.deriv_eq, deriv_const]
  set W : (Fin (n - 1) → ℝ) × ℝ → (Fin (n - 1) → ℝ) × ℝ :=
    fun p => (deriv lam p.2 • Y (lam p.2) p.1, (0 : ℝ)) with hWdef
  have hW : ContDiff ℝ ∞ W := by
    refine ContDiff.prodMk ?_ contDiff_const
    refine (hdlam.comp contDiff_snd).smul ?_
    exact hY.comp ((hlam.comp contDiff_snd).prodMk contDiff_fst)
  set T : Set ((Fin (n - 1) → ℝ) × ℝ) := K ×ˢ Icc (-κ / 2) (κ / 2) with hTdef
  have hTS : T ⊆ S := fun p hp =>
    ⟨hKU hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hTK : T ⊆ K ×ˢ Ioo (-κ) κ := fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hW0 : ∀ p, p ∉ T → W p = 0 := by
    intro p hp
    rcases not_and_or.1 hp with h | h
    · simp only [hWdef, hYK _ _ h, smul_zero]
      rfl
    · simp only [hWdef, hdlam0 _ h, zero_smul]
      rfl
  have hTc : IsCompact T := hK.prod isCompact_Icc
  have hBTc : IsCompact (box '' T) :=
    hTc.image_of_continuousOn (hboxsmooth.continuousOn.mono hTS)
  have hBTcl : IsClosed (box '' T) := hBTc.isClosed
  let Z : (x : M) → TangentSpace I x := fun x =>
    if x ∈ box '' S then
      (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (inv x) (W (inv x)) : Fin n → ℝ)
    else 0
  have hZbox : ∀ p ∈ S, Z (box p) = mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p (W p) := by
    intro p hp
    have key : ∀ q, q = p →
        (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box q (W q) : Fin n → ℝ) =
          mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p (W p) := by
      rintro q rfl
      rfl
    change (if box p ∈ box '' S then
      (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (inv (box p)) (W (inv (box p))) : Fin n → ℝ)
      else 0) = _
    simp only [mem_image_of_mem _ hp, ↓reduceIte]
    exact key _ (hinvl p hp)
  have hZ0 : ∀ x, x ∉ box '' T → Z x = 0 := by
    intro x hx
    by_cases hxS : x ∈ box '' S
    · obtain ⟨p, hp, rfl⟩ := hxS
      rw [hZbox p hp, hW0 p fun hpT => hx (mem_image_of_mem _ hpT)]
      exact (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p).map_zero
    · change (if x ∈ box '' S then
        (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (inv x) (W (inv x)) : Fin n → ℝ)
        else 0) = 0
      simp only [hxS, ↓reduceIte]
  have htsupp : tsupport Z ⊆ box '' T := by
    refine closure_minimal (fun x hx => ?_) hBTcl
    by_contra h
    exact hx (hZ0 x h)
  refine ⟨lam, hlam, hlam0, hlam1, Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₀
    by_cases hx₀ : x₀ ∈ box '' S
    · obtain ⟨p₀, hp₀, rfl⟩ := hx₀
      rw [Bundle.Trivialization.contMDiffAt_section_iff
        (e := trivializationAt (Fin n → ℝ) (TangentSpace I) (box p₀))
        (FiberBundle.mem_baseSet_trivializationAt (Fin n → ℝ) (TangentSpace I) (box p₀))]
      set g : (Fin (n - 1) → ℝ) × ℝ → Fin n → ℝ := fun z => extChartAt I (box p₀) (box z)
        with hgdef
      set Ω : Set ((Fin (n - 1) → ℝ) × ℝ) := S ∩ box ⁻¹' (extChartAt I (box p₀)).source
        with hΩdef
      have hΩ : IsOpen Ω :=
        hboxsmooth.continuousOn.isOpen_inter_preimage hSopen (isOpen_extChartAt_source _)
      have hp₀Ω : p₀ ∈ Ω := ⟨hp₀, mem_extChartAt_source _⟩
      have hg : ContDiffOn ℝ ∞ g Ω := by
        have h1 : ContMDiffOn 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ g Ω := by
          refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := box p₀)).comp
            (hboxsmooth.mono inter_subset_left) fun z hz => ?_
          rw [← extChartAt_source I]
          exact hz.2
        exact contMDiffOn_iff_contDiffOn.1 h1
      have hG : ContDiffAt ℝ ∞ (fun z => fderiv ℝ g z (W z)) p₀ := by
        have hfd : ContDiffOn ℝ ∞ (fderiv ℝ g) Ω :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2
        exact (hfd.clm_apply hW.contDiffOn).contDiffAt (hΩ.mem_nhds hp₀Ω)
      have hfib : (fun x => (trivializationAt (Fin n → ℝ) (TangentSpace I) (box p₀)
          ⟨x, Z x⟩).2) =ᶠ[𝓝 (box p₀)] (fun x => (fun z => fderiv ℝ g z (W z)) (inv x)) := by
        have hU : box '' Ω ∈ 𝓝 (box p₀) :=
          (hopen Ω inter_subset_left hΩ).mem_nhds (mem_image_of_mem _ hp₀Ω)
        filter_upwards [hU] with x hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [DifferentialGeometry.Topology.Morse.tangentTrivializationAt_apply I (box p₀) (box p)
          hp.2 _, hZbox p hp.1, hinvl p hp.1]
        have hext : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I (box p₀)) (box p) := by
          refine (contMDiffAt_extChartAt' (I := I) (n := ∞) (x := box p₀) ?_).mdifferentiableAt
            (by simp)
          rw [← extChartAt_source I]
          exact hp.2
        have hmdb : MDifferentiableAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p :=
          (hboxsmooth.contMDiffAt (hSopen.mem_nhds hp.1)).mdifferentiableAt (by simp)
        have hcomp := mfderiv_comp p hext hmdb
        have h1 : mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, Fin n → ℝ)
            (extChartAt I (box p₀) ∘ box) p = fderiv ℝ g p := mfderiv_eq_fderiv
        rw [DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv_apply]
        exact DFunLike.congr_fun (hcomp.symm.trans h1) (W p)
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hfib
      have hGm : ContMDiffAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
          (fun z => fderiv ℝ g z (W z)) (inv (box p₀)) := by
        rw [hinvl p₀ hp₀]
        exact hG.contMDiffAt
      exact ContMDiffAt.comp (I' := 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ)) (box p₀) hGm
        (hinv.contMDiffAt (hBopen.mem_nhds (mem_image_of_mem _ hp₀)))
    · have hx₀' : x₀ ∉ box '' T := fun h => hx₀ (image_mono hTS h)
      refine ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) (IB := I)
        (n := ∞)).contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hBTcl.isOpen_compl.mem_nhds hx₀'] with x hx
      change (⟨x, Z x⟩ : TangentBundle I M) = ⟨x, 0⟩
      rw [hZ0 x hx]
  · exact hBTc.of_isClosed_subset (isClosed_tsupport _) htsupp
  · intro x
    by_cases hxS : x ∈ box '' S
    · obtain ⟨p, hp, rfl⟩ := hxS
      have hfb : (f ∘ box) =ᶠ[𝓝 p] fun q : (Fin (n - 1) → ℝ) × ℝ => c - q.2 := by
        filter_upwards [hSopen.mem_nhds hp] with q hq
        exact hlevel q hq
      have hmdb : MDifferentiableAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p :=
        (hboxsmooth.contMDiffAt (hSopen.mem_nhds hp)).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp p ((hf (box p)).mdifferentiableAt (by simp)) hmdb
      have h1 : mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) 𝓘(ℝ, ℝ) (f ∘ box) p =
          fderiv ℝ (f ∘ box) p := mfderiv_eq_fderiv
      have h2 : fderiv ℝ (f ∘ box) p =
          fderiv ℝ (fun q : (Fin (n - 1) → ℝ) × ℝ => c - q.2) p := hfb.fderiv_eq
      have h3 : fderiv ℝ (fun q : (Fin (n - 1) → ℝ) × ℝ => c - q.2) p (W p) = 0 := by
        rw [(hasFDerivAt_snd.const_sub c).fderiv]
        simp [hWdef]
      have h4 := DFunLike.congr_fun (hcomp.symm.trans (h1.trans h2)) (W p)
      unfold dfV
      rw [hZbox p hp]
      rw [show (mfderiv I 𝓘(ℝ, ℝ) f (box p))
          (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box p (W p)) = 0 from h4.trans h3, map_zero]
    · unfold dfV
      rw [hZ0 x fun h => hxS (image_mono hTS h), map_zero, map_zero]
  · exact htsupp.trans (image_mono hTK)
  · intro y hy s hs
    exact hZbox (y, s) ⟨hy, hs⟩

theorem CollarChart.realizes_of_boxField (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ)
    {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ Ch.U)
    (Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ))
    (hsupp : ∀ t y, y ∉ K → Hs t y = y) (h0 : ∀ t, t ≤ 0 → ∀ y, Hs t y = y)
    (h1 : ∀ t, 1 ≤ t → ∀ y, Hs t y = Hs 1 y)
    (Y : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ))
    (hY : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n - 1) → ℝ) => Y p.1 p.2))
    (hYHs : ∀ t y, HasDerivAt (fun s => Hs s y) (Y t (Hs t y)) t)
    (lam : ℝ → ℝ) (hlam : ContDiff ℝ ∞ lam) (hlam0 : ∀ s, s ≤ -κ / 2 → lam s = 0)
    (hlam1 : ∀ s, κ / 2 ≤ s → lam s = 1) (Z : (x : M) → TangentSpace I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)))
    (hZc : IsCompact (tsupport Z)) (hZf : ∀ x, dfV I f Z x = 0)
    (hZs : tsupport Z ⊆
      (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (K ×ˢ Ioo (-κ) κ))
    (hZbox : ∀ y ∈ Ch.U, ∀ s ∈ Ioo (-κ) κ,
      Z (D.flow s (Ch.φ y)) = mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I
        (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) (y, s)
        (deriv lam s • Y (lam s) y, 0)) :
    Ch.realizes K (Hs 1) Z := by
  have _ := h1
  have _ := hY
  refine ⟨hZ, hZc, hZf, hZs, ?_⟩
  intro E hE y hy
  have hYoff : ∀ t z, z ∉ K → Y t z = 0 := by
    intro t z hz
    have h := hYHs t z
    have hc : (fun s => Hs s z) = fun _ => z := funext fun s => hsupp s z hz
    rw [hc, hsupp t z hz] at h
    exact h.unique (hasDerivAt_const t z)
  have hstay : ∀ y₀ ∈ K, ∀ r, Hs r y₀ ∈ K := by
    intro y₀ hy₀ r₁
    by_contra hr₁
    set γ : ℝ → (Fin (n - 1) → ℝ) := fun r => Hs r y₀ with hγdef
    have hγc : Continuous γ := continuous_iff_continuousAt.2 fun r => (hYHs r y₀).continuousAt
    have hr₁pos : 0 < r₁ := by
      by_contra hle
      exact hr₁ (by rw [h0 r₁ (not_lt.1 hle) y₀]; exact hy₀)
    set S : Set ℝ := Icc 0 r₁ ∩ γ ⁻¹' K with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (hK.isClosed.preimage hγc)
    have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hr₁pos.le⟩, by
      change Hs 0 y₀ ∈ K
      rw [h0 0 le_rfl y₀]; exact hy₀⟩
    have hSbdd : BddAbove S := ⟨r₁, fun r hr => hr.1.2⟩
    have hmem : sSup S ∈ S := hSc.csSup_mem ⟨0, hS0⟩ hSbdd
    set a' := sSup S with ha'
    have ha'r : a' < r₁ := by
      refine lt_of_le_of_ne hmem.1.2 fun h => hr₁ ?_
      have := hmem.2
      rw [h] at this
      exact this
    have hout : ∀ r ∈ Ioc a' r₁, γ r ∉ K := by
      intro r hr hrK
      have : r ≤ a' := le_csSup hSbdd ⟨⟨(hmem.1.1).trans hr.1.le, hr.2⟩, hrK⟩
      linarith [hr.1]
    have hconst : ∀ ε ∈ Ioc a' r₁, γ ε = γ r₁ := by
      intro ε hε
      have := constant_of_has_deriv_right_zero (f := γ) (a := ε) (b := r₁)
        hγc.continuousOn (fun x hx => by
          have hd := hYHs x y₀
          rw [hYoff x _ (hout x ⟨hε.1.trans_le hx.1, hx.2.le⟩)] at hd
          exact hd.hasDerivWithinAt) r₁ ⟨hε.2, le_rfl⟩
      exact this.symm
    have hcl : IsClosed {r | γ r = γ r₁} := isClosed_eq hγc continuous_const
    have hsub : Ioc a' r₁ ⊆ {r | γ r = γ r₁} := fun r hr => hconst r hr
    have ha'mem : a' ∈ closure (Ioc a' r₁) := by
      rw [closure_Ioc ha'r.ne]
      exact ⟨le_rfl, ha'r.le⟩
    have heq : γ a' = γ r₁ := hcl.closure_subset_iff.2 hsub ha'mem
    have h2 : γ a' ∈ K := hmem.2
    rw [heq] at h2
    exact hr₁ h2
  set g : ℝ → (Fin (n - 1) → ℝ) := fun s => Hs (lam s) y with hgdef
  have gU : ∀ s, g s ∈ Ch.U := by
    intro s
    by_cases hyK : y ∈ K
    · exact hKU (hstay y hyK _)
    · change Hs (lam s) y ∈ Ch.U
      rw [hsupp _ y hyK]; exact hy
  have hg : ∀ s, HasDerivAt g (deriv lam s • Y (lam s) (g s)) s := fun s =>
    (hYHs (lam s) y).scomp s ((hlam.differentiable (by simp)) s).hasDerivAt
  set box : (Fin (n - 1) → ℝ) × ℝ → M := fun p => D.flow p.2 (Ch.φ p.1) with hboxdef
  have hbox_smooth : ∀ (y' : Fin (n - 1) → ℝ) (s : ℝ), y' ∈ Ch.U →
      ContMDiffAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I ∞ box (y', s) := by
    intro y' s hy'
    have h1 : ContMDiffAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : (Fin (n - 1) → ℝ) × ℝ => (q.2, Ch.φ q.1)) (y', s) :=
      (contDiff_snd.contMDiff.contMDiffAt).prodMk
        ((Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hy')).comp (y', s)
          contDiff_fst.contMDiff.contMDiffAt)
    exact D.contMDiff_flow_joint.contMDiffAt.comp (y', s) h1
  have hbox_diff : ∀ (y' : Fin (n - 1) → ℝ) (s : ℝ), y' ∈ Ch.U →
      HasMFDerivAt 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y', s)
        (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y', s)) := fun y' s hy' =>
    ((hbox_smooth y' s hy').mdifferentiableAt (by simp)).hasMFDerivAt
  have hV : ∀ (y' : Fin (n - 1) → ℝ) (s : ℝ), y' ∈ Ch.U →
      mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y', s) (0, 1) = D.V (box (y', s)) := by
    intro y' s hy'
    have hc : HasDerivAt (fun u : ℝ => (y', u)) ((0 : Fin (n - 1) → ℝ), (1 : ℝ)) s :=
      (hasDerivAt_const s y').prodMk (hasDerivAt_id s)
    have hc' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) (fun u : ℝ => (y', u)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : Fin (n - 1) → ℝ), (1 : ℝ))) :=
      hasMFDerivAt_iff_hasFDerivAt.2 hc.hasFDerivAt
    have hd1 := (hbox_diff y' s hy').comp s hc'
    have hd2 := D.isMIntegralCurve_flow (Ch.φ y') s
    have h3 := hasMFDerivAt_unique hd1 hd2
    have h4 := DFunLike.congr_fun h3 (1 : ℝ)
    have e1 : ((mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y', s)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : Fin (n - 1) → ℝ), (1 : ℝ)))) (1 : ℝ) =
        mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (y', s) ((0 : Fin (n - 1) → ℝ), (1 : ℝ)) := by
      rw [ContinuousLinearMap.comp_apply]
      exact congrArg _ (one_smul ℝ _)
    have e2 : ((1 : ℝ →L[ℝ] ℝ).smulRight (D.V (D.flow s (Ch.φ y')))) (1 : ℝ) =
        D.V (D.flow s (Ch.φ y')) := by
      exact one_smul ℝ _
    exact e1.symm.trans (h4.trans e2)
  have hκ := Ch.hκ
  have hstrip := Ch.strip
  have hlev : ∀ k ∈ Ch.U, ∀ u ∈ Icc (-κ) κ, f (D.flow u (Ch.φ k)) = c - u := by
    intro k hk u hu
    have hfk : f (Ch.φ k) = c := Ch.level k hk
    have hx : f (Ch.φ k) ∈ Icc a b := by
      rw [hfk]; constructor <;> linarith
    have hxT : f (Ch.φ k) - u ∈ Icc a b := by
      rw [hfk]; constructor <;> linarith [hu.1, hu.2]
    have havoid : ∀ s ∈ uIcc 0 u, ∀ p hp, D.flow s (Ch.φ k) ∉ D.smallBall p hp := by
      intro s hs p hp hmem
      have hsI : s ∈ Icc (-κ) κ := by
        rw [mem_uIcc] at hs
        rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by linarith, by linarith [hu.2]⟩
        · exact ⟨by linarith [hu.1], by linarith⟩
      refine Ch.avoid k hk s hsI p hp ?_
      exact image_mono (fun z (hz : morseNorm n z < (D.chart p hp).r₀) =>
        (show morseNorm n z < D.rm p hp from lt_trans hz (D.r₀_lt_rm p hp))) hmem
    have := f_flow_eq_sub_of_avoid_uIcc (D := D) hf hx hxT havoid u right_mem_uIcc
    rw [this, hfk]
  have hnotsupp : ∀ y₀ ∈ Ch.U, ∀ s, s ∉ Ioo (-κ) κ → D.flow s (Ch.φ y₀) ∉ tsupport Z := by
    intro y₀ hy₀ s hs hmem
    obtain ⟨⟨k, s'⟩, ⟨hk, hs'⟩, heq⟩ := hZs hmem
    simp only [hboxdef] at heq
    have hkU : k ∈ Ch.U := hKU hk
    have hback : Ch.φ y₀ = D.flow (s' + -s) (Ch.φ k) := by
      rw [← D.flow_flow, heq, D.flow_neg_flow]
    have hfy : f (Ch.φ y₀) = c := Ch.level y₀ hy₀
    rw [hback] at hfy
    have hanti := f_flow_antitone (D := D) hf (Ch.φ k)
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · have hu : 0 < s' + -s := by linarith [hs'.1]
      have h1 : f (D.flow (s' + -s) (Ch.φ k)) ≤ f (D.flow (min (s' + -s) κ) (Ch.φ k)) :=
        hanti (min_le_left _ _)
      rw [hlev k hkU _ ⟨by linarith [le_min hu.le hκ.le], min_le_right _ _⟩] at h1
      have : 0 < min (s' + -s) κ := lt_min hu hκ
      linarith
    · have hu : s' + -s < 0 := by linarith [hs'.2]
      have h1 : f (D.flow (max (s' + -s) (-κ)) (Ch.φ k)) ≤ f (D.flow (s' + -s) (Ch.φ k)) :=
        hanti (le_max_left _ _)
      rw [hlev k hkU _ ⟨le_max_right _ _, by linarith [max_le hu.le (by linarith : -κ ≤ 0)]⟩] at h1
      have : max (s' + -s) (-κ) < 0 := max_lt hu (by linarith)
      linarith
  have hdlam : ∀ s, s ∉ Ioo (-κ) κ → deriv lam s = 0 := by
    intro s hs
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · have hev : lam =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show s < -κ / 2 by linarith)] with r hr
        exact hlam0 r hr.le
      rw [hev.deriv_eq]; simp
    · have hev : lam =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show κ / 2 < s by linarith)] with r hr
        exact hlam1 r hr.le
      rw [hev.deriv_eq]; simp
  set γ : ℝ → M := fun t => box (g (t - κ), t - κ) with hγdef
  have hγE : IsMIntegralCurve γ E.V := by
    intro t
    set s := t - κ with hsdef
    set w : Fin (n - 1) → ℝ := deriv lam s • Y (lam s) (g s) with hwdef
    have hc : HasDerivAt (fun t : ℝ => (g (t - κ), t - κ)) (w, (1 : ℝ)) t :=
      (HasDerivAt.comp_sub_const t κ (hg s)).prodMk ((hasDerivAt_id t).sub_const κ)
    have hc' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ)
        (fun t : ℝ => (g (t - κ), t - κ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (w, (1 : ℝ))) :=
      hasMFDerivAt_iff_hasFDerivAt.2 hc.hasFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
        ((mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (w, (1 : ℝ)))) :=
      (hbox_diff (g s) s (gU s)).comp t hc'
    have hL : (1 : ℝ →L[ℝ] ℝ).smulRight (E.V (γ t)) =
        (mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (w, (1 : ℝ))) := by
      refine ContinuousLinearMap.ext_ring (R₁ := ℝ) (M₁ := TangentSpace I (γ t)) ?_
      have e1 : ((mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (w, (1 : ℝ)))) (1 : ℝ) =
          mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s) (w, (1 : ℝ)) := by
        rw [ContinuousLinearMap.comp_apply]
        exact congrArg _ (one_smul ℝ _)
      have e2 : ((1 : ℝ →L[ℝ] ℝ).smulRight (E.V (γ t))) (1 : ℝ) = E.V (γ t) := one_smul ℝ _
      refine e2.trans (Eq.trans ?_ e1.symm)
      have hsplit : mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s) (w, (1 : ℝ)) =
          mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s) (w, 0) +
            mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s) (0, 1) := by
        refine Eq.trans ?_ ((mfderiv 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) I box (g s, s)).map_add (w, 0) (0, 1))
        congr 1
        exact Prod.ext (add_zero w).symm (zero_add (1 : ℝ)).symm
      rw [hsplit, hV (g s) s (gU s), hE]
      have hγt : γ t = box (g s, s) := rfl
      rw [hγt, add_comm]
      congr 1
      by_cases hs : s ∈ Ioo (-κ) κ
      · exact hZbox (g s) (gU s) s hs
      · have hz : Z (box (g s, s)) = 0 := image_eq_zero_of_notMem_tsupport (hnotsupp (g s) (gU s) s hs)
        rw [hz, hwdef, hdlam s hs, zero_smul]
        exact (map_zero _).symm
    rw [hL]
    exact hcomp
  have huniq := DifferentialGeometry.Analysis.ODE.integralCurve_eq_of_agree E.V E.smooth_one
    (E.isMIntegralCurve_flow (γ 0)) hγE (t₀ := 0) (by rw [E.flow_zero])
  have h2 := congrFun huniq (2 * κ)
  have hγ0 : γ 0 = D.flow (-κ) (Ch.φ y) := by
    change D.flow (0 - κ) (Ch.φ (Hs (lam (0 - κ)) y)) = _
    rw [zero_sub, hlam0 (-κ) (by linarith), h0 0 le_rfl]
  have hγ2 : γ (2 * κ) = D.flow κ (Ch.φ (Hs 1 y)) := by
    change D.flow (2 * κ - κ) (Ch.φ (Hs (lam (2 * κ - κ)) y)) = _
    rw [show 2 * κ - κ = κ by ring, hlam1 κ (by linarith)]
  rw [← hγ0, ← hγ2]
  exact h2

theorem CollarChart.exists_realizes (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ)
    {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ Ch.U)
    (Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ))
    (hHs : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n - 1) → ℝ) => Hs p.1 p.2))
    (hbij : ∀ t, Function.Bijective (Hs t))
    (hdiff : ∀ t y, Function.Bijective (fderiv ℝ (Hs t) y))
    (hsupp : ∀ t y, y ∉ K → Hs t y = y) (h0 : ∀ t, t ≤ 0 → ∀ y, Hs t y = y)
    (h1 : ∀ t, 1 ≤ t → ∀ y, Hs t y = Hs 1 y) :
    ∃ Z : (x : M) → TangentSpace I x, Ch.realizes K (Hs 1) Z := by
  obtain ⟨Y, hY, hYK, hY01, hYHs⟩ :=
    exists_isotopy_generator hK Hs hHs hbij hdiff hsupp h0 h1
  obtain ⟨lam, hlam, hlam0, hlam1, Z, hZ, hZc, hZf, hZs, hZbox⟩ :=
    Ch.exists_boxField hf hK hKU Y hY hYK hY01
  exact ⟨Z, Ch.realizes_of_boxField hf hK hKU Hs hsupp h0 h1 Y hY hYHs lam hlam hlam0 hlam1 Z
    hZ hZc hZf hZs hZbox⟩

theorem CollarChart.flow_of_realizes (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c κ : ℝ} (Ch : D.CollarChart c κ)
    {K : Set (Fin (n - 1) → ℝ)} {H₁ : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)}
    {Z : (x : M) → TangentSpace I x} (hZ : Ch.realizes K H₁ Z) (hKU : K ⊆ Ch.U)
    (E : GradientLikeStrip I f a b crit) (hE : ∀ x, E.V x = D.V x + Z x) :
    (∀ x t, (∀ s ∈ Icc (min 0 t) (max 0 t), D.flow s x ∉ tsupport Z) → E.flow t x = D.flow t x) ∧
      ∀ x, f x = c + κ → x ∉ D.flow (-κ) '' (Ch.φ '' K) → E.flow (2 * κ) x = D.flow (2 * κ) x := by
  obtain ⟨-, -, -, hsuppZ, -⟩ := hZ
  have hV : ∀ z ∈ (tsupport Z)ᶜ, D.V z = E.V z := by
    intro z hz
    rw [hE, image_eq_zero_of_notMem_tsupport hz]
    exact (add_zero (D.V z)).symm
  have hopen : IsOpen (tsupport Z)ᶜ := (isClosed_tsupport Z).isOpen_compl
  have clause1 : ∀ x t, (∀ s ∈ Icc (min 0 t) (max 0 t), D.flow s x ∉ tsupport Z) →
      E.flow t x = D.flow t x := by
    intro x t hav
    rcases le_total 0 t with ht | ht
    · rw [min_eq_left ht, max_eq_right ht] at hav
      exact flow_eq_of_agree (D₁ := D) (D₂ := E) hopen hV
        (fun s hs => hav s ⟨hs.1, hs.2.le⟩) t ⟨ht, le_rfl⟩
    · rw [min_eq_right ht, max_eq_left ht] at hav
      have hT : (0 : ℝ) ≤ -t := by linarith
      refine flow_eq_of_agree_neg (D₁ := D) (D₂ := E) hopen hV hT
        (fun s hs => hav s ⟨by linarith [hs.1], hs.2.le⟩) t ⟨by linarith, ht⟩
  refine ⟨clause1, ?_⟩
  intro x hx hxK
  have hκ := Ch.hκ
  refine clause1 x (2 * κ) ?_
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  intro s hs hmem
  obtain ⟨⟨y, s'⟩, ⟨hyK, hs'⟩, hys⟩ := hsuppZ hmem
  simp only at hys
  have hyU := hKU hyK
  have hsmall : ∀ r ∈ Icc (-κ) κ, ∀ p (hp : p ∈ crit),
      D.flow r (Ch.φ y) ∉ D.smallBall p hp := by
    intro r hr p hp hmem'
    refine Ch.avoid y hyU r hr p hp ?_
    obtain ⟨z, hz, hzeq⟩ := hmem'
    exact ⟨z, lt_trans hz (D.r₀_lt_rm p hp), hzeq⟩
  have hφy : f (Ch.φ y) = c := Ch.level y hyU
  have hlev : ∀ r ∈ Icc (-κ) κ, f (D.flow r (Ch.φ y)) = c - r := by
    intro r hr
    rcases le_total 0 r with h0 | h0
    · have := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := κ)
        (by rw [hφy]; exact ⟨by linarith [Ch.strip.1], by linarith [Ch.strip.2]⟩)
        (by rw [hφy]; exact ⟨by linarith [Ch.strip.1], by linarith [Ch.strip.2]⟩)
        (fun u hu => hsmall u (by
          rw [uIcc_of_le hκ.le] at hu; exact ⟨by linarith [hu.1], hu.2⟩))
        r (by rw [uIcc_of_le hκ.le]; exact ⟨h0, hr.2⟩)
      rw [this, hφy]
    · have := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := -κ)
        (by rw [hφy]; exact ⟨by linarith [Ch.strip.1], by linarith [Ch.strip.2]⟩)
        (by rw [hφy]; exact ⟨by linarith [Ch.strip.1], by linarith [Ch.strip.2]⟩)
        (fun u hu => hsmall u (by
          rw [uIcc_of_ge (by linarith : -κ ≤ 0)] at hu; exact ⟨hu.1, by linarith [hu.2]⟩))
        r (by rw [uIcc_of_ge (by linarith : -κ ≤ 0)]; exact ⟨hr.1, h0⟩)
      rw [this, hφy]
  have hxeq : x = D.flow (s' - s) (Ch.φ y) := by
    calc x = D.flow (-s) (D.flow s x) := (D.flow_neg_flow x s).symm
      _ = D.flow (-s) (D.flow s' (Ch.φ y)) := by rw [hys]
      _ = D.flow (s' + -s) (Ch.φ y) := D.flow_flow _ _ _
      _ = D.flow (s' - s) (Ch.φ y) := by rw [sub_eq_add_neg]
  have hu_le : s' - s ≤ -κ := by
    have h1 := sub_le_f_flow (D := D) hf x hs.1
    rw [← hys, hlev s' ⟨hs'.1.le, hs'.2.le⟩, hx] at h1
    linarith
  have hu_ge : -κ ≤ s' - s := by
    by_contra hlt'
    have hlt : s' - s < -κ := lt_of_not_ge hlt'
    set g : ℝ → ℝ := fun r => f (D.flow r (Ch.φ y)) with hg
    have hanti : Antitone g := f_flow_antitone hf (Ch.φ y)
    have hgu : g (s' - s) = c + κ := by
      change f (D.flow (s' - s) (Ch.φ y)) = c + κ
      rw [← hxeq]; exact hx
    have hgk : g (-κ) = c + κ := by
      change f (D.flow (-κ) (Ch.φ y)) = c + κ
      rw [hlev (-κ) ⟨le_rfl, by linarith⟩]; ring
    have hconst : ∀ r ∈ Icc (s' - s) (-κ), g r = c + κ := by
      intro r hr
      have h1 := hanti hr.1
      have h2 := hanti hr.2
      rw [hgu] at h1
      rw [hgk] at h2
      exact le_antisymm h1 h2
    have hdf : dfV I f D.V (D.flow (-κ) (Ch.φ y)) = -1 := by
      refine D.unit _ ?_ (hsmall (-κ) ⟨le_rfl, by linarith⟩)
      change f (D.flow (-κ) (Ch.φ y)) ∈ Icc a b
      rw [hlev (-κ) ⟨le_rfl, by linarith⟩]
      exact ⟨by linarith [Ch.strip.1], by linarith [Ch.strip.2]⟩
    have h1 : HasDerivWithinAt g (-1) (Iic (-κ)) (-κ) := by
      have := (hasDerivAt_f_flow (D := D) hf (Ch.φ y) (-κ)).hasDerivWithinAt (s := Iic (-κ))
      rwa [hdf] at this
    have h2 : HasDerivWithinAt g 0 (Iic (-κ)) (-κ) := by
      refine (hasDerivWithinAt_const (-κ) (Iic (-κ)) (c + κ)).congr_of_eventuallyEq ?_
        (hconst (-κ) ⟨hlt.le, le_rfl⟩)
      filter_upwards [Icc_mem_nhdsLE hlt] with r hr
      exact hconst r hr
    have := (uniqueDiffWithinAt_Iic (-κ)).eq_deriv _ h1 h2
    norm_num at this
  have hu : s' - s = -κ := le_antisymm hu_le hu_ge
  rw [hu] at hxeq
  exact hxK ⟨Ch.φ y, ⟨y, hyK, rfl⟩, hxeq.symm⟩

end GradientLikeStrip

theorem continuousOn_frameVec_tangentBundle {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [IsManifold I 1 M] {X : Type*} [TopologicalSpace X] {s : Set X} {ψ : X → M}
    (hψ : ContinuousOn ψ s) {r : ℕ} {E : X → Fin r → (Fin n → ℝ)}
    (hE : ∀ k, ContinuousOn (fun y => (⟨ψ y, E y k⟩ : TangentBundle I M)) s)
    {c : X → Fin r → ℝ} (hc : ContinuousOn c s) :
    ContinuousOn (fun y => (⟨ψ y, ∑ k, c y k • E y k⟩ : TangentBundle I M)) s := by
  intro y₀ hy₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hψ y₀ hy₀, ?_⟩
  set e := trivializationAt (Fin n → ℝ) (TangentSpace I) (ψ y₀) with he
  have hbase : ∀ᶠ y in nhdsWithin y₀ s, ψ y ∈ e.baseSet :=
    hψ y₀ hy₀ (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  have hk : ∀ k, ContinuousWithinAt (fun y => (e ⟨ψ y, E y k⟩).2) s y₀ := by
    intro k
    have h := ((FiberBundle.continuousWithinAt_totalSpace (Fin n → ℝ) _).1 (hE k y₀ hy₀)).2
    simpa [he] using h
  have hlin : ∀ (b : M) (hb : b ∈ e.baseSet) (v : Fin r → TangentSpace I b) (a : Fin r → ℝ),
      (e ⟨b, ∑ k, a k • v k⟩).2 = ∑ k, a k • (e ⟨b, v k⟩).2 := by
    intro b hb v a
    have hL := e.linear ℝ hb
    let L : TangentSpace I b →ₗ[ℝ] (Fin n → ℝ) := hL.mk' _
    have hL' : ∀ w : TangentSpace I b, (e ⟨b, w⟩).2 = L w := fun w => rfl
    rw [hL', map_sum]
    simp only [map_smul, hL']
  have hcont : ContinuousWithinAt (fun y => ∑ k, c y k • (e ⟨ψ y, E y k⟩).2) s y₀ := by
    refine tendsto_finsetSum _ (fun k _ => ?_)
    exact (((continuous_apply k).continuousAt.comp_continuousWithinAt (hc y₀ hy₀))).smul (hk k)
  refine hcont.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hbase] with y hy
    exact hlin (ψ y) hy (E y) (c y)
  · exact hlin (ψ y₀) (mem_baseSet_trivializationAt _ _ _) (E y₀) (c y₀)

theorem exists_continuousOn_frameCoeff {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [IsManifold I 1 M] {X : Type*} [TopologicalSpace X] {s : Set X} {ψ : X → M}
    (hψ : ContinuousOn ψ s) {r : ℕ} {E : X → Fin r → (Fin n → ℝ)}
    (hE : ∀ k, ContinuousOn (fun y => (⟨ψ y, E y k⟩ : TangentBundle I M)) s)
    (hind : ∀ y ∈ s, LinearIndependent ℝ (E y)) {v : X → Fin n → ℝ}
    (hv : ContinuousOn (fun y => (⟨ψ y, v y⟩ : TangentBundle I M)) s)
    (hspan : ∀ y ∈ s, v y ∈ Submodule.span ℝ (Set.range (E y))) :
    ∃ c : X → Fin r → ℝ, ContinuousOn c s ∧ ∀ y ∈ s, ∑ k, c y k • E y k = v y := by
  classical
  let gram : (Fin r → Fin n → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun A => Matrix.of fun i j => A i ⬝ᵥ A j
  let Φ : (Fin r → Fin n → ℝ) × (Fin n → ℝ) → Fin r → ℝ :=
    fun p => (gram p.1).det⁻¹ • (Matrix.mulVec (gram p.1).adjugate (fun i => p.1 i ⬝ᵥ p.2))
  have hgram : ∀ (A : Fin r → Fin n → ℝ) (g : Fin r → ℝ),
      Matrix.mulVec (gram A) g = fun i => A i ⬝ᵥ ∑ j, g j • A j := by
    intro A g
    funext i
    simp only [gram, Matrix.mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    simp only [dotProduct, Matrix.of_apply, mul_comm]
  have hdet : ∀ A : Fin r → Fin n → ℝ, LinearIndependent ℝ A → (gram A).det ≠ 0 := by
    intro A hA h0
    obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hgram] at hg
    have hS : (∑ j, g j • A j) ⬝ᵥ (∑ j, g j • A j) = 0 := by
      rw [sum_dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_dotProduct, congrFun hg i]
      simp
    rw [dotProduct_self_eq_zero] at hS
    exact hg0 (funext (Fintype.linearIndependent_iff.1 hA g hS))
  have hsolve : ∀ (A : Fin r → Fin n → ℝ) (w : Fin n → ℝ) (g : Fin r → ℝ),
      (gram A).det ≠ 0 → ∑ k, g k • A k = w → g = Φ (A, w) := by
    intro A w g hd hg
    have h1 : Matrix.mulVec (gram A) g = fun i => A i ⬝ᵥ w := by rw [hgram, hg]
    simp only [Φ]
    rw [← h1, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hd, one_smul]
  have hΦ : ∀ A w, (gram A).det ≠ 0 → ContinuousAt Φ (A, w) := by
    intro A w hd
    have hG : Continuous fun p : (Fin r → Fin n → ℝ) × (Fin n → ℝ) => gram p.1 := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [gram, Matrix.of_apply, dotProduct]
      fun_prop
    have hb : Continuous fun p : (Fin r → Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i ⬝ᵥ p.2 := by
      refine continuous_pi fun i => ?_
      simp only [dotProduct]
      fun_prop
    exact ((hG.matrix_det.continuousAt).inv₀ hd).smul
      (hG.matrix_adjugate.matrix_mulVec hb).continuousAt
  have hex : ∀ y ∈ s, ∃ c : Fin r → ℝ, ∑ k, c k • E y k = v y := fun y hy =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan y hy)
  let c : X → Fin r → ℝ := fun y => if h : y ∈ s then (hex y h).choose else 0
  have hc : ∀ y ∈ s, ∑ k, c y k • E y k = v y := by
    intro y hy
    simp only [c, hy, ↓reduceDIte]
    exact (hex y hy).choose_spec
  refine ⟨c, ?_, hc⟩
  intro y₀ hy₀
  set e := trivializationAt (Fin n → ℝ) (TangentSpace I) (ψ y₀) with he
  let A : X → Fin r → Fin n → ℝ := fun y k => (e ⟨ψ y, E y k⟩).2
  let w : X → Fin n → ℝ := fun y => (e ⟨ψ y, v y⟩).2
  have hAc : ContinuousWithinAt A s y₀ := by
    refine continuousWithinAt_pi.2 fun k => ?_
    exact ((FiberBundle.continuousWithinAt_totalSpace (Fin n → ℝ) _).1 (hE k y₀ hy₀)).2
  have hwc : ContinuousWithinAt w s y₀ :=
    ((FiberBundle.continuousWithinAt_totalSpace (Fin n → ℝ) _).1 (hv y₀ hy₀)).2
  have hkey : ∀ y ∈ s, ψ y ∈ e.baseSet → (gram (A y)).det ≠ 0 ∧ c y = Φ (A y, w y) := by
    intro y hy hb
    let L := Bundle.Trivialization.linearEquivAt ℝ e (ψ y) hb
    have hAL : A y = L.toLinearMap ∘ E y := by
      funext k
      exact (Bundle.Trivialization.linearEquivAt_apply e (ψ y) hb (E y k)).symm
    have hwL : w y = L (v y) := (Bundle.Trivialization.linearEquivAt_apply e (ψ y) hb (v y)).symm
    have hind' : LinearIndependent ℝ (A y) := by
      rw [hAL]
      exact (hind y hy).map' _ L.ker
    have hd := hdet _ hind'
    refine ⟨hd, hsolve _ _ _ hd ?_⟩
    rw [hwL, ← hc y hy, hAL]
    refine ((map_sum L.toLinearMap (fun k => c y k • E y k) Finset.univ).trans ?_).symm
    exact Finset.sum_congr rfl fun k _ => map_smul L.toLinearMap (c y k) (E y k)
  have hb₀ : ψ y₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hev : c =ᶠ[𝓝[s] y₀] fun y => Φ (A y, w y) := by
    have hpre : ψ ⁻¹' e.baseSet ∈ 𝓝[s] y₀ :=
      (hψ y₀ hy₀).preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hb₀)
    filter_upwards [hpre, self_mem_nhdsWithin] with y hb hy
    exact (hkey y hy hb).2
  exact ContinuousWithinAt.congr_of_eventuallyEq
    ((hΦ (A y₀) (w y₀) (hkey y₀ hy₀ hb₀).1).comp_continuousWithinAt
      (f := fun y => (A y, w y)) (hAc.prodMk hwc)) hev (hkey y₀ hy₀ hb₀).2

theorem exists_finite_smoothPartition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M]
    {ι : Type*} {K : Set M} (hK : IsCompact K) {U : ι → Set M} (hU : ∀ i, IsOpen (U i))
    (hKU : K ⊆ ⋃ i, U i) :
    ∃ (t : Finset ι) (χ : ι → M → ℝ), (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ i x, 0 ≤ χ i x) ∧ (∀ i, IsCompact (tsupport (χ i))) ∧ (∀ i, tsupport (χ i) ⊆ U i) ∧
      (∀ i, i ∉ t → χ i = 0) ∧ (∀ x, ∑ i ∈ t, χ i x ≤ 1) ∧
      ∀ᶠ x in 𝓝ˢ K, ∑ i ∈ t, χ i x = 1 := by
  classical
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK (isOpen_iUnion hU) hKU
  have hpt : ∀ x : L, ∃ (i : ι) (b : SmoothBumpFunction I (x : M)), tsupport b ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hLU x.2)
    obtain ⟨b, -, hb⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 ((hU i).mem_nhds hi)
    exact ⟨i, b, hb⟩
  choose ix bx hbx using hpt
  obtain ⟨t, ht⟩ := hLc.elim_nhds_subcover'
    (fun x hx => interior {y | bx ⟨x, hx⟩ y = 1})
    (fun x hx => interior_mem_nhds.2 (bx ⟨x, hx⟩).eventuallyEq_one)
  let fs : SmoothBumpCovering (↥t) I M L :=
    { c := fun j => ((j : L) : M)
      toFun := fun j => bx (j : L)
      c_mem' := fun j => (j : L).2
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (ht hx)
        refine ⟨⟨y, hyt⟩, ?_⟩
        exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hy) fun z hz => hz }
  let ρ := fs.toSmoothPartitionOfUnity
  have hρ0 : ∀ (j : ↥t) (x : M), x ∉ tsupport (bx (j : L)) → ρ j x = 0 := fun j x hx =>
    fs.toSmoothPartitionOfUnity_zero_of_zero (image_eq_zero_of_notMem_tsupport hx)
  have hsub : ∀ i, tsupport (fun x => ∑ j ∈ Finset.univ.filter (fun j : ↥t => ix (j : L) = i),
      ρ j x) ⊆ ⋃ j ∈ Finset.univ.filter (fun j : ↥t => ix (j : L) = i), tsupport (bx (j : L)) := by
    intro i
    refine closure_minimal ?_ (isClosed_biUnion_finset fun j _ => isClosed_tsupport _)
    intro x hx
    by_contra hC
    apply hx
    refine Finset.sum_eq_zero fun j hj => hρ0 j x ?_
    intro hxj
    exact hC (mem_iUnion₂.2 ⟨j, hj, hxj⟩)
  have hsum : ∀ x, ∑ i ∈ Finset.univ.image (fun j : ↥t => ix (j : L)),
      ∑ j ∈ Finset.univ.filter (fun j : ↥t => ix (j : L) = i), ρ j x = ∑ᶠ j, ρ j x := by
    intro x
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_fiberwise_of_maps_to (g := fun j : ↥t => ix (j : L))
      (fun j _ => Finset.mem_image_of_mem (fun j : ↥t => ix (j : L)) (Finset.mem_univ j))
      (fun j => ρ j x)
  refine ⟨Finset.univ.image (fun j : ↥t => ix (j : L)),
    fun i x => ∑ j ∈ Finset.univ.filter (fun j : ↥t => ix (j : L) = i), ρ j x,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact contMDiff_finsetSum fun j _ => (ρ j).contMDiff
  · intro i x
    exact Finset.sum_nonneg fun j _ => ρ.nonneg j x
  · intro i
    exact ((Finset.isCompact_biUnion (f := fun j : ↥t => tsupport (bx (j : L))) _
      fun j _ => (bx (j : L)).hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport _) (hsub i))
  · intro i
    refine (hsub i).trans (iUnion₂_subset fun j hj => ?_)
    have hji : ix (j : L) = i := (Finset.mem_filter.1 hj).2
    exact hji ▸ hbx (j : L)
  · intro i hi
    funext x
    refine Finset.sum_eq_zero fun j hj => ?_
    exact absurd ((Finset.mem_filter.1 hj).2 ▸
      Finset.mem_image_of_mem (fun j : ↥t => ix (j : L)) (Finset.mem_univ j)) hi
  · intro x
    rw [hsum x]
    exact ρ.sum_le_one x
  · refine Filter.mem_of_superset (isOpen_interior.mem_nhdsSet.2 hKL) fun y hy => ?_
    change ∑ i ∈ _, _ = _
    rw [hsum y]
    exact ρ.sum_eq_one (interior_subset hy)

theorem continuousOn_mfderiv_apply {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : M → F} {O : Set M} (hO : IsOpen O)
    (hG : ContMDiffOn I 𝓘(ℝ, F) 1 G O) {Y : (x : M) → TangentSpace I x}
    (hY : ContinuousOn (fun x => (⟨x, Y x⟩ : TangentBundle I M)) O) :
    ContinuousOn (fun x => (mfderiv I 𝓘(ℝ, F) G x (Y x) : F)) O := by
  have hT := hG.continuousOn_tangentMapWithin (le_refl _) hO.uniqueMDiffOn
  have hcomp : ContinuousOn (fun x => tangentMapWithin I 𝓘(ℝ, F) G O
      (⟨x, Y x⟩ : TangentBundle I M)) O :=
    hT.comp hY (fun x hx => hx)
  have hsnd : ContinuousOn (fun x => ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F))
      (tangentMapWithin I 𝓘(ℝ, F) G O (⟨x, Y x⟩ : TangentBundle I M))).2) O :=
    continuous_snd.comp_continuousOn
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).continuous.comp_continuousOn hcomp)
  refine hsnd.congr fun x hx => ?_
  simp only [tangentBundleModelSpaceHomeomorph_coe, tangentMapWithin,
    mfderivWithin_of_isOpen hO hx]
  rfl

structure LevelField (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] (f : M → ℝ) where
  Y : (x : M) → TangentSpace I x
  smooth : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M))
  compact : IsCompact (tsupport Y)
  level : ∀ x, dfV I f Y x = 0

namespace LevelField

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ}

def flow (Z : LevelField I f) (t : ℝ) (x : M) : M :=
  DifferentialGeometry.Analysis.ODE.curveAt Z.Y
    (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport Z.Y Z.smooth
      Z.compact) x t

omit [T2Space M] [I.Boundaryless] in
theorem exists_sum_smul {ι : Type*} (t : Finset ι) {χ : ι → M → ℝ}
    (hχ : ∀ i ∈ t, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i)) (Z : ι → LevelField I f) :
    ∃ Y : LevelField I f, ∀ x, Y.Y x = ∑ i ∈ t, χ i x • (Z i).Y x := by
  classical
  refine ⟨⟨fun x => ∑ i ∈ t, χ i x • (Z i).Y x, ?_, ?_, ?_⟩, fun x => rfl⟩
  · refine ContMDiff.sum_section (t := fun i x => χ i x • (Z i).Y x) ?_
    intro i hi
    exact ContMDiff.smul_section (hχ i hi) (Z i).smooth
  · have hK : IsCompact (⋃ i ∈ t, tsupport (Z i).Y) :=
      t.isCompact_biUnion fun i _ => (Z i).compact
    have hKc : IsClosed (⋃ i ∈ t, tsupport (Z i).Y) :=
      isClosed_biUnion_finset fun i _ => isClosed_tsupport _
    refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal ?_ hKc
    intro x hx
    by_contra hxK
    apply hx
    refine Finset.sum_eq_zero fun i hi => ?_
    have hxi : x ∉ tsupport (Z i).Y := fun h => hxK (Set.mem_biUnion hi h)
    rw [image_eq_zero_of_notMem_tsupport hxi]
    exact smul_zero (χ i x)
  · intro x
    unfold dfV
    simp only [map_sum, map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h := (Z i).level x
    unfold dfV at h
    rw [h, smul_zero]

omit [T2Space M] [I.Boundaryless] in
theorem exists_smul_of_contMDiffOn {W : Set M} (hW : IsOpen W) {Y : (x : M) → TangentSpace I x}
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hYf : ∀ x ∈ W, dfV I f Y x = 0) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hχc : IsCompact (tsupport χ)) (hχW : tsupport χ ⊆ W) :
    ∃ Z : LevelField I f, ∀ x, Z.Y x = χ x • Y x := by
  have hsm : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, χ x • Y x⟩ : TangentBundle I M)) :=
    ContMDiffOn.smul_section_of_tsupport (u := W) hχ.contMDiffOn hW hχW hY
  have hts : tsupport (fun x => χ x • Y x) ⊆ tsupport χ :=
    tsupport_smul_subset_left χ Y
  refine ⟨⟨fun x => χ x • Y x, hsm, hχc.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩,
    fun x => rfl⟩
  intro x
  have hlin : dfV I f (fun x => χ x • Y x) x = χ x * dfV I f Y x := by
    unfold dfV
    rw [ContinuousLinearMap.map_smul]
    rfl
  rw [hlin]
  by_cases hx : x ∈ W
  · rw [hYf x hx, mul_zero]
  · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχW h))
    rw [hχx, zero_mul]

end LevelField

section FlowCharts

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

def flowChart {f : M → ℝ} (d r : ℕ) (Ys : Fin r → LevelField I f) (base : (Fin d → ℝ) → M) {m : ℕ}
    (y : Fin m → ℝ) : M :=
  (List.finRange r).foldl (fun x j => (Ys j).flow (coordN y (d + j)) x) (base fun i => coordN y i)

theorem flowChart_spec {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {d r m : ℕ} (hm : m = d + r)
    (Ys : Fin r → LevelField I f) (base : (Fin d → ℝ) → M) {Ω : Set (Fin d → ℝ)}
    (hΩ : IsOpen Ω) (hbase : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I ∞ base Ω) :
    ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ (flowChart d r Ys base (m := m))
        {y | (fun i : Fin d => coordN y i) ∈ Ω} ∧
      (∀ y : Fin m → ℝ, f (flowChart d r Ys base y) = f (base fun i => coordN y i)) ∧
      ∀ y : Fin m → ℝ, (fun i : Fin d => coordN y i) ∈ Ω → (∀ j, d ≤ j → coordN y j = 0) →
        ∀ v : Fin m → ℝ,
          mfderiv 𝓘(ℝ, Fin m → ℝ) I (flowChart d r Ys base (m := m)) y v =
            mfderiv 𝓘(ℝ, Fin d → ℝ) I base (fun i => coordN y i) (fun i => coordN v i) +
              ∑ j : Fin r, coordN v (d + j) • (Ys j).Y (base fun i => coordN y i) := by
  have _ : m = d + r := hm
  classical
  have hc : ∀ k : ℕ, ∃ L : (Fin m → ℝ) →L[ℝ] ℝ, ∀ y, L y = coordN y k := by
    intro k
    by_cases hk : k < m
    · exact ⟨ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) ⟨k, hk⟩,
        fun y => by simp [coordN, hk]⟩
    · exact ⟨0, fun y => by simp [coordN, hk]⟩
  choose c hcy using hc
  let P : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi fun i : Fin d => c i
  have hP : ∀ y, P y = fun i : Fin d => coordN y i := fun y => funext fun i => by
    simp [P, hcy]
  set S : Set (Fin m → ℝ) := {y | (fun i : Fin d => coordN y i) ∈ Ω} with hSdef
  have hSP : S = P ⁻¹' Ω := by ext y; simp [S, hP]
  have hS : IsOpen S := hSP ▸ hΩ.preimage P.continuous
  let Φ : Fin r → ℝ × M → M := fun j p => (Ys j).flow p.1 p.2
  have hΦ : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (Φ j) := fun j =>
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport (Ys j).Y
      (Ys j).smooth (Ys j).compact
  have hΦ0 : ∀ j x, (Ys j).flow 0 x = x := fun j x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hΦcurve : ∀ j x, IsMIntegralCurve (fun t => (Ys j).flow t x) (Ys j).Y := fun j x =>
    DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ x
  have hlev : ∀ j t x, f ((Ys j).flow t x) = f x := by
    intro j t x
    have hd : ∀ s, HasDerivAt (f ∘ fun t => (Ys j).flow t x) 0 s := by
      intro s
      have h1 := DifferentialGeometry.Analysis.ODE.hasDerivAt_df_comp_integralCurve f hf (Ys j).Y
        (hΦcurve j x) s
      have h0 := (Ys j).level ((Ys j).flow s x)
      simp only [dfV] at h0
      exact h1.congr_deriv h0
    have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    simpa [hΦ0] using this
  let D : ∀ {k : ℕ}, ((Fin k → ℝ) → M) → (Fin k → ℝ) → (Fin k → ℝ) → (Fin n → ℝ) :=
    fun {k} g y v => mfderiv 𝓘(ℝ, Fin k → ℝ) I g y v
  let Yv : Fin r → M → (Fin n → ℝ) := fun j x => (Ys j).Y x
  have hmd : ∀ {g : (Fin m → ℝ) → M}, ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ g S → ∀ y ∈ S,
      MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) I g y := fun hg y hy =>
    (hg.contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt (by simp)
  have step : ∀ j : Fin r, ∀ g : (Fin m → ℝ) → M, ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ g S →
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ (fun y => (Ys j).flow (coordN y (d + j)) (g y)) S ∧
      ∀ y ∈ S, coordN y (d + j) = 0 → ∀ v,
        D (fun y => (Ys j).flow (coordN y (d + j)) (g y)) y v =
          D g y v + coordN v (d + j) • Yv j (g y) := by
    intro j g hg
    have heq : (fun y => (Ys j).flow (coordN y (d + j)) (g y)) =
        Φ j ∘ fun y => (c (d + j) y, g y) := by
      funext y; simp [Φ, hcy]
    rw [heq]
    refine ⟨(hΦ j).comp_contMDiffOn ((c (d + j)).contMDiff.contMDiffOn.prodMk hg), ?_⟩
    intro y hy hy0 v
    have hpt : (fun y => (c (d + j) y, g y)) y = ((0 : ℝ), g y) := by simp [hcy, hy0]
    have hpair : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, ℝ).prod I)
        (fun y => (c (d + j) y, g y)) y :=
      (((c (d + j)).contMDiff (n := 1)).mdifferentiable one_ne_zero y).prodMk (hmd hg y hy)
    have hΦd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (Φ j) ((0 : ℝ), g y) :=
      (hΦ j).mdifferentiable (by simp) _
    simp only [D]
    refine (mfderiv_comp_apply_of_eq y hΦd hpair hpt v).trans ?_
    rw [MDifferentiableAt.mfderiv_prod (((c (d + j)).contMDiff (n := 1)).mdifferentiable
      one_ne_zero y) (hmd hg y hy)]
    refine (mfderiv_prod_eq_add_apply hΦd).trans ?_
    have h1 : ∀ a : ℝ, (mfderiv 𝓘(ℝ, ℝ) I (fun z => Φ j (z, g y)) 0 a : Fin n → ℝ) =
        a • Yv j (g y) := by
      intro a
      have := (hΦcurve j (g y) 0).mfderiv
      simp only [Φ]
      rw [this]
      change (1 : ℝ →L[ℝ] ℝ) a • Yv j ((Ys j).flow 0 (g y)) = a • Yv j (g y)
      rw [hΦ0]
      rfl
    have h2 : (fun z => Φ j (0, z)) = id := funext fun z => hΦ0 j z
    have h3 : mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, ℝ) (c (d + j)) y = c (d + j) := by
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      apply ContinuousLinearMap.ext
      intro v
      rfl
    dsimp only
    rw [h2, mfderiv_id, h3]
    change (show Fin n → ℝ from mfderiv 𝓘(ℝ, ℝ) I (fun z => Φ j (z, g y)) 0 (c (d + j) v)) +
        (show Fin n → ℝ from mfderiv 𝓘(ℝ, Fin m → ℝ) I g y v) = _
    rw [h1, hcy, add_comm]
  have key : ∀ l : List (Fin r), ∀ g : (Fin m → ℝ) → M,
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ g S →
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞
        (fun y => l.foldl (fun x (i : Fin r) => (Ys i).flow (coordN y (d + i)) x) (g y)) S ∧
      ∀ y ∈ S, (∀ k, d ≤ k → coordN y k = 0) →
        l.foldl (fun x (i : Fin r) => (Ys i).flow (coordN y (d + i)) x) (g y) = g y ∧
        ∀ v, D (fun y => l.foldl (fun x (i : Fin r) => (Ys i).flow (coordN y (d + i)) x) (g y)) y v =
          D g y v + (l.map fun (i : Fin r) => coordN v (d + i) • Yv i (g y)).sum := by
    intro l
    induction l with
    | nil =>
      intro g hg
      refine ⟨hg, fun y _ _ => ⟨rfl, fun v => ?_⟩⟩
      simp
    | cons j l ih =>
      intro g hg
      obtain ⟨hs, hd⟩ := step j g hg
      obtain ⟨ihs, ihd⟩ := ih _ hs
      refine ⟨ihs, fun y hy hy0 => ?_⟩
      have hj0 : coordN y (d + j) = 0 := hy0 _ (Nat.le_add_right _ _)
      have hgy : (Ys j).flow (coordN y (d + j)) (g y) = g y := by rw [hj0, hΦ0]
      obtain ⟨e1, e2⟩ := ihd y hy hy0
      refine ⟨e1.trans hgy, fun v => ?_⟩
      change D (fun y => l.foldl (fun x (i : Fin r) => (Ys i).flow (coordN y (d + i)) x)
        ((Ys j).flow (coordN y (d + j)) (g y))) y v = _
      rw [e2, hd y hy hj0 v, hgy, List.map_cons, List.sum_cons, add_assoc]
  have hflev : ∀ y : Fin m → ℝ, ∀ l : List (Fin r), ∀ x,
      f (l.foldl (fun x (i : Fin r) => (Ys i).flow (coordN y (d + i)) x) x) = f x := by
    intro y l
    induction l with
    | nil => intro x; rfl
    | cons j l ih => intro x; exact (ih _).trans (hlev _ _ _)
  have hg₀eq : (fun y => base fun i : Fin d => coordN y i) = base ∘ P := by
    funext y; simp [hP]
  have hg₀ : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ (fun y => base fun i : Fin d => coordN y i) S := by
    rw [hg₀eq]
    exact hbase.comp P.contMDiff.contMDiffOn (fun y hy => by simpa [hSP] using hy)
  obtain ⟨K1, K2⟩ := key (List.finRange r) _ hg₀
  refine ⟨K1, fun y => hflev y _ _, fun y hy hy0 v => ?_⟩
  have hbd : D (fun y => base fun i : Fin d => coordN y i) y v =
      mfderiv 𝓘(ℝ, Fin d → ℝ) I base (fun i => coordN y i) (fun i => coordN v i) := by
    simp only [D]
    rw [hg₀eq]
    refine (mfderiv_comp_apply_of_eq y
      ((hbase.contMDiffAt (hΩ.mem_nhds hy)).mdifferentiableAt (by simp))
      ((P.contMDiff (n := 1)).mdifferentiable one_ne_zero y) (hP y) v).trans ?_
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    exact congrArg (mfderiv 𝓘(ℝ, Fin d → ℝ) I base (fun i => coordN y i)) (hP v)
  refine ((K2 y hy hy0).2 v).trans ?_
  rw [hbd, Fin.sum_univ_def]
  rfl

omit [I.Boundaryless] in
theorem exists_injOn_nhds_of_immersion {m : ℕ} {Φ : (Fin m → ℝ) → M} {W K : Set (Fin m → ℝ)}
    (hW : IsOpen W) (hΦ : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I 1 Φ W) (hK : IsCompact K) (hKW : K ⊆ W)
    (himm : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ y)) (hinj : InjOn Φ K) :
    ∃ U : Set (Fin m → ℝ), IsOpen U ∧ K ⊆ U ∧ U ⊆ W ∧ InjOn Φ U ∧
      ∀ y ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ y) := by
  classical
  have hΦc : ContinuousOn Φ W := hΦ.continuousOn
  have hloc : ∀ y ∈ K, ∃ V : Set (Fin m → ℝ), IsOpen V ∧ y ∈ V ∧ V ⊆ W ∧ InjOn Φ V ∧
      ∀ z ∈ V, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ z) := by
    intro y hy
    set e := extChartAt I (Φ y) with he_def
    set W₁ := W ∩ Φ ⁻¹' e.source with hW₁
    have hW₁o : IsOpen W₁ := hΦc.isOpen_inter_preimage hW (isOpen_extChartAt_source _)
    have hyW₁ : y ∈ W₁ := ⟨hKW hy, mem_extChartAt_source _⟩
    have hg : ContDiffOn ℝ 1 (e ∘ Φ) W₁ := by
      have hsrc : e.source = (chartAt H (Φ y)).source := extChartAt_source I (Φ y)
      have h1 : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (e ∘ Φ) W₁ :=
        ((contMDiffOn_extChartAt (I := I) (x := Φ y) (n := ∞)).of_le (by norm_num)).comp
          (hΦ.mono inter_subset_left) (fun z hz => by rw [← hsrc]; exact hz.2)
      exact contMDiffOn_iff_contDiffOn.mp h1
    have hiff : ∀ z ∈ W₁, Function.Injective (fderiv ℝ (e ∘ Φ) z) ↔
        Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ z) := by
      intro z hz
      have hsrc : Φ z ∈ (chartAt H (Φ y)).source := by
        rw [← extChartAt_source I (Φ y)]; exact hz.2
      have hdiff : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) I Φ z :=
        (hΦ.mdifferentiableOn one_ne_zero).mdifferentiableAt (hW.mem_nhds hz.1)
      have hcomp : fderiv ℝ (e ∘ Φ) z =
          (mfderiv I 𝓘(ℝ, Fin n → ℝ) e (Φ z)).comp (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ z) := by
        have hc := mfderiv_comp z (mdifferentiableAt_extChartAt hsrc) hdiff
        rw [mfderiv_eq_fderiv] at hc
        apply ContinuousLinearMap.ext
        intro v
        exact DFunLike.congr_fun hc v
      obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt (I := I) (x := Φ y) hz.2
      rw [hcomp, ← hL]
      constructor
      · intro h a b hab
        apply h
        change L (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ z a) = L (mfderiv 𝓘(ℝ, Fin m → ℝ) I Φ z b)
        rw [hab]
      · intro h a b hab
        exact h (L.injective hab)
    have hinjy : Function.Injective (fderiv ℝ (e ∘ Φ) y) := (hiff y hyW₁).mpr (himm y hy)
    have hcd : ContDiffAt ℝ 1 (e ∘ Φ) y := hg.contDiffAt (hW₁o.mem_nhds hyW₁)
    have hstrict : HasStrictFDerivAt (e ∘ Φ) (fderiv ℝ (e ∘ Φ) y) y :=
      hcd.hasStrictFDerivAt one_ne_zero
    obtain ⟨A, hA0, hA⟩ :=
      ((fderiv ℝ (e ∘ Φ) y : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))).injective_iff_antilipschitz.mp hinjy
    obtain ⟨s, hs, hsapprox⟩ :=
      hstrict.approximates_deriv_on_nhds (c := (2 * A)⁻¹) (Or.inr (by positivity))
    have hopen : (fderiv ℝ (e ∘ Φ)) ⁻¹' {L | Function.Injective L} ∈ 𝓝 y :=
      (hcd.continuousAt_fderiv one_ne_zero).preimage_mem_nhds
        (ContinuousLinearMap.isOpen_injective.mem_nhds hinjy)
    have hmem : s ∩ (fderiv ℝ (e ∘ Φ)) ⁻¹' {L | Function.Injective L} ∩ W₁ ∈ 𝓝 y :=
      inter_mem (inter_mem hs hopen) (hW₁o.mem_nhds hyW₁)
    obtain ⟨V, hVsub, hVo, hyV⟩ := mem_nhds_iff.mp hmem
    refine ⟨V, hVo, hyV, fun z hz => (hVsub hz).2.1, ?_, ?_⟩
    · intro a ha b hb hab
      have ha' := hVsub ha
      have hb' := hVsub hb
      have happ := hsapprox a ha'.1.1 b hb'.1.1
      have hgab : (e ∘ Φ) a = (e ∘ Φ) b := by simp [Function.comp, hab]
      rw [hgab, sub_self, zero_sub, norm_neg] at happ
      have hbd : ‖a - b‖ ≤ (A : ℝ) * ‖fderiv ℝ (e ∘ Φ) y (a - b)‖ :=
        ZeroHomClass.bound_of_antilipschitz _ hA (a - b)
      have hA0' : (0 : ℝ) < A := by exact_mod_cast hA0
      have hc : (((2 * A)⁻¹ : NNReal) : ℝ) = (2 * (A : ℝ))⁻¹ := by push_cast; ring
      rw [hc] at happ
      have h2 : ‖a - b‖ ≤ ‖a - b‖ / 2 := by
        calc ‖a - b‖ ≤ (A : ℝ) * ‖fderiv ℝ (e ∘ Φ) y (a - b)‖ := hbd
          _ ≤ (A : ℝ) * ((2 * (A : ℝ))⁻¹ * ‖a - b‖) := by gcongr
          _ = ‖a - b‖ / 2 := by field_simp
      have h3 : ‖a - b‖ = 0 := le_antisymm (by linarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp h3)
    · intro z hz
      exact (hiff z (hVsub hz).2).mp (hVsub hz).1.2
  choose! V hVo hyV hVW hVinj hVder using hloc
  set N : Set ((Fin m → ℝ) × (Fin m → ℝ)) := (⋃ y ∈ K, V y ×ˢ V y) ∪
    (W ×ˢ W ∩ (fun p : (Fin m → ℝ) × (Fin m → ℝ) => (Φ p.1, Φ p.2)) ⁻¹' (Set.diagonal M)ᶜ)
    with hN
  have hNo : IsOpen N := by
    refine (isOpen_biUnion fun y hy => (hVo y hy).prod (hVo y hy)).union ?_
    refine ContinuousOn.isOpen_inter_preimage ?_ (hW.prod hW) isClosed_diagonal.isOpen_compl
    exact (hΦc.comp continuousOn_fst (fun p hp => hp.1)).prodMk
      (hΦc.comp continuousOn_snd (fun p hp => hp.2))
  have hKN : K ×ˢ K ⊆ N := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    by_cases hab : Φ a = Φ b
    · have : a = b := hinj ha hb hab
      subst this
      exact Or.inl (mem_biUnion ha ⟨hyV a ha, hyV a ha⟩)
    · exact Or.inr ⟨⟨hKW ha, hKW hb⟩, hab⟩
  obtain ⟨u, v, huo, hvo, hKu, hKv, huv⟩ := generalized_tube_lemma hK hK hNo hKN
  refine ⟨u ∩ v ∩ ⋃ y ∈ K, V y, (huo.inter hvo).inter (isOpen_biUnion fun y hy => hVo y hy),
    fun y hy => ⟨⟨hKu hy, hKv hy⟩, mem_biUnion hy (hyV y hy)⟩, ?_, ?_, ?_⟩
  · rintro z ⟨-, hz⟩
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
    exact hVW y hy hzy
  · intro a ha b hb hab
    rcases huv (mk_mem_prod ha.1.1 hb.1.2) with h | h
    · obtain ⟨y, hy, hay, hby⟩ := mem_iUnion₂.mp h
      exact hVinj y hy hay hby hab
    · exact absurd hab h.2
  · rintro z ⟨-, hz⟩
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
    exact hVder y hy z hzy

theorem exists_frame_of_projections {d N r : ℕ} {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) (P : (Fin d → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (hP : ContinuousOn P K)
    (hidem : ∀ y ∈ K, (P y).comp (P y) = P y)
    (hrank : ∀ y ∈ K,
      Module.finrank ℝ (LinearMap.range (P y : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) = r) :
    ∃ F : (Fin d → ℝ) → Fin r → (Fin N → ℝ), ContinuousOn F K ∧
      ∀ y ∈ K, LinearIndependent ℝ (F y) ∧
        ∀ i, F y i ∈ LinearMap.range (P y : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨fun _ _ => 0, continuousOn_empty _, fun y hy => absurd hy (Set.notMem_empty y)⟩
  have huc : UniformContinuousOn P K := hK.uniformContinuousOn_of_continuous hP
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / 2) (by norm_num)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y ∈ K, ‖y - y₀‖ ≤ R :=
    hK.exists_bound_of_continuousOn (continuous_id.sub continuous_const).continuousOn
  obtain ⟨L, hL⟩ := exists_nat_gt (max R 0 / δ)
  have hLpos : (0 : ℝ) < L := lt_of_le_of_lt (div_nonneg (le_max_right _ _) hδ.le) hL
  let pt : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun j y => y₀ + ((j : ℝ) / L) • (y - y₀)
  have hptK : ∀ j ≤ L, ∀ y ∈ K, pt j y ∈ K := by
    intro j hj y hy
    exact hKc.add_smul_sub_mem hy₀ hy
      ⟨div_nonneg (Nat.cast_nonneg _) hLpos.le, (div_le_one hLpos).2 (by exact_mod_cast hj)⟩
  have hpt0 : ∀ y, pt 0 y = y₀ := by intro y; simp [pt]
  have hptL : ∀ y, pt L y = y := by intro y; simp [pt, div_self hLpos.ne']
  have hptd : ∀ j, ∀ y ∈ K, dist (pt (j + 1) y) (pt j y) < δ := by
    intro j y hy
    have hdiff : pt (j + 1) y - pt j y = (1 / (L : ℝ)) • (y - y₀) := by
      simp only [pt]
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      ring
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / (L : ℝ) * ‖y - y₀‖ ≤ 1 / L * max R 0 := by
          gcongr
          exact (hR y hy).trans (le_max_left _ _)
      _ = max R 0 / L := by ring
      _ < δ := by
          rw [div_lt_iff₀ hLpos]
          rw [div_lt_iff₀ hδ] at hL
          linarith
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → (Fin d → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)),
      (∀ y, Q 0 y = P y₀) ∧ ∀ j y, Q (j + 1) y = (P (pt (j + 1) y)).comp (Q j y) :=
    ⟨fun j y => Nat.rec (motive := fun _ => (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (P y₀)
      (fun j q => (P (pt (j + 1) y)).comp q) j, fun _ => rfl, fun _ _ => rfl⟩
  have hQc : ∀ j ≤ L, ContinuousOn (Q j) K := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : Q 0 = fun _ => P y₀ := funext hQ0
      rw [h0]
      exact continuousOn_const
    | succ j ih =>
      intro hj
      have h1 : ContinuousOn (fun y => P (pt (j + 1) y)) K :=
        hP.comp (show Continuous (pt (j + 1)) by simp only [pt]; fun_prop).continuousOn
          (fun y hy => hptK _ hj y hy)
      have h2 : Q (j + 1) = fun y => (P (pt (j + 1) y)).comp (Q j y) := funext (hQs j)
      rw [h2]
      exact h1.clm_comp (ih (by omega))
  let W := LinearMap.range (P y₀ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
  let bW : Module.Basis (Fin r) ℝ W := Module.finBasisOfFinrankEq ℝ W (hrank y₀ hy₀)
  let b : Fin r → (Fin N → ℝ) := fun i => (bW i : Fin N → ℝ)
  have hb : LinearIndependent ℝ b := bW.linearIndependent.map' W.subtype W.ker_subtype
  have hfix : ∀ z x, x ∈ LinearMap.range (P z : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) → z ∈ K →
      P z x = x := by
    rintro z x ⟨w, rfl⟩ hz
    have h := congrArg (fun T => T w) (hidem z hz)
    simpa using h
  have hinv : ∀ j ≤ L, ∀ y ∈ K, LinearIndependent ℝ (fun i => Q j y (b i)) ∧
      ∀ i, Q j y (b i) ∈ LinearMap.range (P (pt j y) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      have hbi : ∀ i, b i ∈ W := fun i => (bW i).2
      have hQb : ∀ i, Q 0 y (b i) = b i := fun i => by
        rw [hQ0]
        exact hfix y₀ _ (hbi i) hy₀
      refine ⟨?_, fun i => ?_⟩
      · simp_rw [hQb]
        exact hb
      · rw [hQb, hpt0]
        exact hbi i
    | succ j ih =>
      intro hj y hy
      obtain ⟨hli, hmem⟩ := ih (by omega) y hy
      have hzK : pt j y ∈ K := hptK j (by omega) y hy
      have hz'K : pt (j + 1) y ∈ K := hptK (j + 1) hj y hy
      have hclose : ‖P (pt (j + 1) y) - P (pt j y)‖ < 1 / 2 := by
        rw [← dist_eq_norm]
        exact hδP _ hz'K _ hzK (hptd j y hy)
      refine ⟨?_, fun i => ?_⟩
      · simp_rw [hQs]
        have hdisj : Disjoint (Submodule.span ℝ (Set.range fun i => Q j y (b i)))
            (LinearMap.ker (P (pt (j + 1) y) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) := by
          rw [Submodule.disjoint_def]
          intro x hx hxk
          have hxW : x ∈ LinearMap.range (P (pt j y) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) :=
            (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hmem i)) hx
          have hPx : P (pt j y) x = x := hfix _ _ hxW hzK
          have hk : P (pt (j + 1) y) x = 0 := hxk
          have h1 : ‖x‖ ≤ 1 / 2 * ‖x‖ := by
            calc ‖x‖ = ‖(P (pt (j + 1) y) - P (pt j y)) x‖ := by
                    rw [sub_apply, hk, hPx, zero_sub, norm_neg]
              _ ≤ ‖P (pt (j + 1) y) - P (pt j y)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 / 2 * ‖x‖ := by gcongr
          have h2 : ‖x‖ = 0 := by linarith [norm_nonneg x]
          exact norm_eq_zero.1 h2
        exact hli.map hdisj
      · rw [hQs]
        exact ⟨_, rfl⟩
  refine ⟨fun y i => Q L y (b i), ?_, fun y hy => ?_⟩
  · exact continuousOn_pi.2 fun i => (hQc L le_rfl).clm_apply continuousOn_const
  · obtain ⟨h1, h2⟩ := hinv L le_rfl y hy
    refine ⟨h1, fun i => ?_⟩
    have h3 := h2 i
    rwa [hptL] at h3

namespace GradientLikeStrip

variable {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_collarChart_of_injOn (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {c κ : ℝ} (hκ : 0 < κ) (hstrip : a ≤ c - κ ∧ c + κ ≤ b)
    (hmodel : ∀ x (hx : x ∈ crit), ∀ z ∈ (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx},
      f z ∉ Icc (c - κ) (c + κ))
    (Φ : (Fin (n - 1) → ℝ) → M) {W : Set (Fin (n - 1) → ℝ)} (hW : IsOpen W)
    (hΦ : ContMDiffOn 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ Φ W) (hlev : ∀ y ∈ W, f (Φ y) = c)
    {K₀ : Set (Fin (n - 1) → ℝ)} (hK₀ : IsCompact K₀) (hK₀W : K₀ ⊆ W)
    (himm : ∀ y ∈ K₀, Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ y))
    (hinj : InjOn Φ K₀) :
    ∃ U₀ : Set (Fin (n - 1) → ℝ), IsOpen U₀ ∧ K₀ ⊆ U₀ ∧ U₀ ⊆ W ∧
      ∀ V ⊆ U₀, IsOpen V → ∃ Ch : D.CollarChart c κ, Ch.U = V ∧ Ch.φ = Φ := by
  classical
  obtain ⟨U₁, hU₁o, hK₀U₁, hU₁W, hU₁inj, hU₁imm⟩ :=
    exists_injOn_nhds_of_immersion hW (hΦ.of_le (by norm_num)) hK₀ hK₀W himm hinj
  have hcab : c ∈ Icc a b := ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  have hnotcrit : ∀ y ∈ W, Φ y ∉ crit := by
    intro y hy hc
    have h0 : (0 : Fin n → ℝ) ∈ {w | morseNorm n w < D.rm (Φ y) hc} := by
      simp only [mem_ofPred_eq, morseNorm_zero]
      exact D.rm_pos _ hc
    have := hmodel (Φ y) hc (Φ y) ⟨0, h0, (D.chart _ hc).hχ0⟩
    exact this ⟨by rw [hlev y hy]; linarith, by rw [hlev y hy]; linarith⟩
  have key : ∀ V ⊆ U₁, IsOpen V → ∀ y₀ ∈ V, Φ '' V ∪ (f ⁻¹' {c})ᶜ ∈ 𝓝 (Φ y₀) := by
    intro V hVU hVo y₀ hy₀
    have hy₀W : y₀ ∈ W := hU₁W (hVU hy₀)
    set x₀ := Φ y₀ with hx₀
    set e := extChartAt I x₀ with he
    have hte : IsOpen e.target := isOpen_extChartAt_target x₀
    have hse : IsOpen e.source := isOpen_extChartAt_source x₀
    have hx₀t : e x₀ ∈ e.target := mem_extChartAt_target x₀
    set F : (Fin n → ℝ) → ℝ := fun u => f (e.symm u) with hFdef
    have hFs : ContDiffOn ℝ ∞ F e.target :=
      contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))
    set O : Set (Fin (n - 1) → ℝ) := V ∩ Φ ⁻¹' e.source with hOdef
    have hOo : IsOpen O :=
      (hΦ.continuousOn.mono (hVU.trans hU₁W)).isOpen_inter_preimage hVo hse
    have hy₀O : y₀ ∈ O := ⟨hy₀, mem_extChartAt_source x₀⟩
    set G : (Fin (n - 1) → ℝ) → (Fin n → ℝ) := fun y => e (Φ y) with hGdef
    have hGs : ContDiffOn ℝ ∞ G O := by
      refine contMDiffOn_iff_contDiffOn.1 ?_
      refine (contMDiffOn_extChartAt (x := x₀)).comp
        (hΦ.mono ((inter_subset_left).trans (hVU.trans hU₁W))) ?_
      intro y hy
      have := hy.2
      rwa [he, extChartAt_source] at this
    have hGstrict : HasStrictFDerivAt G (fderiv ℝ G y₀) y₀ :=
      (hGs.contDiffAt (hOo.mem_nhds hy₀O)).hasStrictFDerivAt (by simp)
    have hFstrict : HasStrictFDerivAt F (fderiv ℝ F (e x₀)) (e x₀) :=
      (hFs.contDiffAt (hte.mem_nhds hx₀t)).hasStrictFDerivAt (by simp)
    have hΦmd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ y₀ :=
      (hΦ.contMDiffAt (hW.mem_nhds hy₀W)).mdifferentiableAt (by simp)
    have hmΦ : ∀ v, (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ y₀ v : Fin n → ℝ) = fderiv ℝ G y₀ v := by
      intro v
      rw [hΦmd.mfderiv_abuse]
      simp [writtenInExtChartAt, hGdef, he, hx₀]
      rfl
    have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x₀ := hf.mdifferentiableAt (by simp)
    have hmf : ∀ v, (mfderiv I 𝓘(ℝ, ℝ) f x₀ v : ℝ) = fderiv ℝ F (e x₀) v := by
      intro v
      rw [hfmd.mfderiv_abuse]
      simp [writtenInExtChartAt, hFdef, he, I.range_eq_univ]
      rfl
    set L₁ := fderiv ℝ F (e x₀) with hL₁
    set D₀ := fderiv ℝ G y₀ with hD₀
    set vV : Fin n → ℝ := D.V x₀ with hvV
    have hneg : L₁ vV < 0 := by
      have := D.neg x₀ (by rw [mem_preimage, hlev y₀ hy₀W]; exact hcab) (hnotcrit y₀ hy₀W)
      rw [hvV, ← hmf]
      exact this
    set w : Fin n → ℝ := (L₁ vV)⁻¹ • vV with hwdef
    have hw : L₁ w = 1 := by
      rw [hwdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hneg.ne]
    have hLD : ∀ v, L₁ (D₀ v) = 0 := by
      have h1 : HasFDerivAt (F ∘ G) (L₁.comp D₀) y₀ :=
        hFstrict.hasFDerivAt.comp y₀ hGstrict.hasFDerivAt
      have h2 : HasFDerivAt (F ∘ G) (0 : (Fin (n - 1) → ℝ) →L[ℝ] ℝ) y₀ := by
        refine (hasFDerivAt_const c y₀).congr_of_eventuallyEq ?_
        filter_upwards [hOo.mem_nhds hy₀O] with y hy
        simp only [Function.comp_apply, hFdef, hGdef]
        rw [e.left_inv hy.2]
        exact hlev y (hU₁W (hVU hy.1))
      intro v
      have := congrArg (fun T => T v) (h1.unique h2)
      simpa using this
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exfalso
        subst hn
        have : w = 0 := Subsingleton.elim _ _
        rw [this, map_zero] at hw
        exact zero_ne_one hw
      · exact hn
    set Ξ : (Fin (n - 1) → ℝ) × ℝ → (Fin n → ℝ) := fun p => G p.1 + p.2 • w with hΞdef
    set L : ((Fin (n - 1) → ℝ) × ℝ) →L[ℝ] (Fin n → ℝ) :=
      D₀.comp (ContinuousLinearMap.fst ℝ _ _) + (ContinuousLinearMap.snd ℝ _ _).smulRight w
      with hLdef
    have hΞstrict : HasStrictFDerivAt Ξ L (y₀, (0 : ℝ)) := by
      have h1 : HasStrictFDerivAt (fun p : (Fin (n - 1) → ℝ) × ℝ => G p.1)
          (D₀.comp (ContinuousLinearMap.fst ℝ _ _)) (y₀, (0 : ℝ)) :=
        hGstrict.comp (y₀, (0 : ℝ)) hasStrictFDerivAt_fst
      have h2 : HasStrictFDerivAt (fun p : (Fin (n - 1) → ℝ) × ℝ => p.2 • w)
          ((ContinuousLinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ).smulRight w) (y₀, (0 : ℝ)) :=
        hasStrictFDerivAt_snd.smul_const w
      exact h1.add h2
    have hLinj : Function.Injective L := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨v, t⟩ hvt
      have hvt' : D₀ v + t • w = 0 := by simpa [hLdef] using hvt
      have ht : t = 0 := by
        have := congrArg L₁ hvt'
        rw [map_add, map_smul, hLD, hw, smul_eq_mul, mul_one, zero_add, map_zero] at this
        exact this
      rw [ht, zero_smul, add_zero] at hvt'
      have hv : v = 0 := by
        apply (hU₁imm y₀ (hVU hy₀))
        have h3 := hmΦ v
        rw [hvt'] at h3
        exact h3.trans (ContinuousLinearMap.map_zero _).symm
      rw [hv, ht]
      rfl
    have hLsurj : Function.Surjective L := by
      have hfin : Module.finrank ℝ ((Fin (n - 1) → ℝ) × ℝ) = Module.finrank ℝ (Fin n → ℝ) := by
        simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
        omega
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
        (f := (L : ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ)))).1 hLinj
    have hmap : map Ξ (𝓝 (y₀, (0 : ℝ))) = 𝓝 (e x₀) := by
      have := hΞstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.2 hLsurj)
      simpa [hΞdef, hGdef] using this
    set S : Set (Fin n → ℝ) := e.target ∩ {u | 0 < fderiv ℝ F u w} with hSdef
    have hS : S ∈ 𝓝 (e x₀) := by
      refine inter_mem (hte.mem_nhds hx₀t) ?_
      have hc : ContinuousAt (fun u => fderiv ℝ F u w) (e x₀) :=
        ((hFs.continuousOn_fderiv_of_isOpen hte (by simp)).continuousAt
          (hte.mem_nhds hx₀t)).clm_apply continuousAt_const
      refine hc.preimage_mem_nhds (Ioi_mem_nhds ?_)
      change 0 < L₁ w
      rw [hw]
      exact one_pos
    have hΞc : ContinuousAt Ξ (y₀, (0 : ℝ)) := hΞstrict.hasFDerivAt.continuousAt
    have hΞ0 : Ξ (y₀, (0 : ℝ)) = e x₀ := by
      change G y₀ + (0 : ℝ) • w = e x₀
      rw [zero_smul, add_zero]
    have hN : Ξ ⁻¹' S ∩ O ×ˢ univ ∈ 𝓝 (y₀, (0 : ℝ)) := by
      refine inter_mem (hΞc.preimage_mem_nhds (hΞ0 ▸ hS)) ?_
      exact prod_mem_nhds (hOo.mem_nhds hy₀O) univ_mem
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
    have hball : ∀ y s, dist y y₀ < r → |s| < r → (y, s) ∈ Metric.ball (y₀, (0 : ℝ)) r := by
      intro y s hy hs
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
      exact ⟨hy, hs⟩
    have himg : Ξ '' Metric.ball (y₀, (0 : ℝ)) r ∈ 𝓝 (e x₀) := by
      rw [← hmap]
      exact image_mem_map (Metric.ball_mem_nhds _ hr)
    have hnhds : e.source ∩ e ⁻¹' (Ξ '' Metric.ball (y₀, (0 : ℝ)) r) ∈ 𝓝 x₀ :=
      inter_mem (extChartAt_source_mem_nhds x₀) ((continuousAt_extChartAt x₀).preimage_mem_nhds himg)
    refine mem_of_superset hnhds ?_
    rintro z ⟨hzs, ⟨⟨y, s⟩, hys, hΞz⟩⟩
    by_cases hzc : f z = c
    swap
    · exact Or.inr hzc
    left
    have hys' : dist y y₀ < r ∧ |s| < r := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero] at hys
      exact hys
    have hyO : y ∈ O := (hrN (hball y 0 hys'.1 (by simpa using hr))).2.1
    set g : ℝ → ℝ := fun σ => F (G y + σ • w) with hgdef
    have hgd : ∀ σ ∈ Metric.ball (0 : ℝ) r, HasDerivAt g (fderiv ℝ F (G y + σ • w) w) σ ∧
        0 < fderiv ℝ F (G y + σ • w) w := by
      intro σ hσ
      have hσ' : |σ| < r := by simpa [Real.dist_eq] using hσ
      have hmemS := (hrN (hball y σ hys'.1 hσ')).1
      have hFd : DifferentiableAt ℝ F (G y + σ • w) :=
        (hFs.contDiffAt (hte.mem_nhds hmemS.1)).differentiableAt (by simp)
      have hline : HasDerivAt (fun τ : ℝ => G y + τ • w) ((1 : ℝ) • w) σ :=
        ((hasDerivAt_id σ).smul_const w).const_add (G y)
      refine ⟨?_, hmemS.2⟩
      have := hFd.hasFDerivAt.comp_hasDerivAt σ hline
      rw [one_smul] at this
      exact this
    have hmono : StrictMonoOn g (Metric.ball (0 : ℝ) r) := by
      refine strictMonoOn_of_deriv_pos (convex_ball 0 r) ?_ ?_
      · intro σ hσ
        exact (hgd σ hσ).1.continuousAt.continuousWithinAt
      · intro σ hσ
        rw [interior_eq_iff_isOpen.2 Metric.isOpen_ball] at hσ
        rw [(hgd σ hσ).1.deriv]
        exact (hgd σ hσ).2
    have hgs : g s = c := by
      have h1 : g s = F (e z) := by
        rw [← hΞz]
      rw [h1, hFdef]
      simp only
      rw [e.left_inv hzs]
      exact hzc
    have hg0 : g 0 = c := by
      simp only [hgdef, zero_smul, add_zero, hFdef, hGdef]
      rw [e.left_inv hyO.2]
      exact hlev y (hU₁W (hVU hyO.1))
    have hs0 : s = 0 := hmono.injOn (by simpa [Real.dist_eq] using hys'.2)
      (Metric.mem_ball_self hr) (hgs.trans hg0.symm)
    have hez : e z = e (Φ y) := by
      rw [← hΞz, hs0]
      simp [hΞdef, hGdef]
    exact ⟨y, hyO.1, e.injOn hyO.2 hzs hez.symm⟩
  refine ⟨U₁, hU₁o, hK₀U₁, hU₁W, fun V hVU hVo => ?_⟩
  refine ⟨{ U := V, isOpen_U := hVo, φ := Φ, smooth := hΦ.mono (hVU.trans hU₁W),
            immersion := fun y hy => hU₁imm y (hVU hy), inj := hU₁inj.mono hVU,
            level := fun y hy => hlev y (hU₁W (hVU hy)),
            open_image := ?_, hκ := hκ, strip := hstrip, avoid := ?_ }, rfl, rfl⟩
  · intro V' hV' hV'o
    refine ⟨interior (Φ '' V' ∪ (f ⁻¹' {c})ᶜ), isOpen_interior, ?_⟩
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_interior_iff_mem_nhds.2 (key V' (hV'.trans hVU) hV'o y hy),
        hlev y (hU₁W (hVU (hV' hy)))⟩
    · rintro ⟨hz1, hz2⟩
      rcases interior_subset hz1 with h | h
      · exact h
      · exact absurd hz2 h
  · intro y hy s hs x hx hmem
    have h1 := f_flow_mem_uIcc (D := D) hf (Φ y) s
    rw [hlev y (hU₁W (hVU hy))] at h1
    apply hmodel x hx _ hmem
    rw [mem_uIcc] at h1
    constructor <;> rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [hs.1, hs.2]

theorem mem_rightSphere_iff_coord (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p : M} (hp : p ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hrm : 2 * ε < D.rm p hp ^ 2)
    (hc : f p + ε ≤ c) (hcb : c ≤ b)
    (hU : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx) {z : M} (hz : f z = c) :
    z ∈ D.rightSphere p hp ε c ↔ D.rightCoord p hp ε z = 0 ∧
      D.flow (c - (f p + ε)) z ∈ (D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp} := by
  have hpstrip : f p ∈ Ioo a b := by
    have := D.inStrip p hp (D.chart p hp).p_mem_image_ball
    exact this
  have hlev := (D.flow_level_transport hf (c' := f p + ε) (c := c) (by linarith [hpstrip.1])
    hc hcb hU).1 z hz
  have hw : f (D.flow (c - (f p + ε)) z) = f p + ε := hlev.1
  have hrmR : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hrm0 : 0 < D.rm p hp := D.rm_pos p hp
  have hcoord : D.rightCoord p hp ε z =
      negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) z)) := by
    unfold rightCoord
    rw [hz]
  rw [D.mem_rightSphere_iff p hp ε c, hcoord]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have hsq := (D.chart p hp).morseNorm_sq_of_mem_rightModelSphere hy
    have hlt : morseNorm n y < D.rm p hp := by
      by_contra hcon
      have h1 : D.rm p hp ^ 2 ≤ morseNorm n y ^ 2 :=
        pow_le_pow_left₀ hrm0.le (not_lt.1 hcon) 2
      linarith
    have hsrc : y ∈ (D.chart p hp).χ.source := (D.chart p hp).hsrc y (hlt.le.trans hrmR)
    refine ⟨?_, ⟨y, hlt, hyw⟩⟩
    rw [← hyw, (D.chart p hp).χ.left_inv hsrc]
    exact hy.1
  · rintro ⟨h0, ⟨y, hlt, hyw⟩⟩
    have hle : morseNorm n y ≤ (D.chart p hp).R := hlt.le.trans hrmR
    have hsrc : y ∈ (D.chart p hp).χ.source := (D.chart p hp).hsrc y hle
    rw [← hyw, (D.chart p hp).χ.left_inv hsrc] at h0
    refine ⟨y, ⟨h0, ?_⟩, hyw⟩
    have hf1 := (D.chart p hp).hnorm y hle
    rw [hyw, hw, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, h0, norm_zero] at hf1
    linarith

theorem mem_leftSphere_iff_coord (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hrm : 2 * ε < D.rm q hq ^ 2)
    (hac : a ≤ c) (hc : c ≤ f q - ε)
    (hU : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx) {z : M} (hz : f z = c) :
    z ∈ D.leftSphere q hq ε c ↔ D.leftCoord q hq ε z = 0 ∧
      D.flow (c - (f q - ε)) z ∈ (D.chart q hq).χ '' {w | morseNorm n w < D.rm q hq} := by
  have hq0 : f q ∈ Ioo a b :=
    D.inStrip q hq ⟨0, (D.chart q hq).zero_mem_ball, (D.chart q hq).hχ0⟩
  have hTlev : f (D.flow (c - (f q - ε)) z) = f q - ε := by
    have h := f_flow_eq_sub_of_levels hf (D := D) (x := z) (T := c - (f q - ε))
      (by rw [hz]; exact ⟨hac, by linarith [hq0.2]⟩)
      (by rw [hz]; constructor <;> linarith [hq0.2])
      (by
        intro y hy
        rw [hz, uIcc_of_le (by linarith)] at hy
        apply hU
        convert hy using 2
        ring)
      _ right_mem_uIcc
    rw [h, hz]
    ring
  rw [D.mem_leftSphere_iff q hq ε c]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have hlt : morseNorm n y < D.rm q hq := by
      apply lt_of_pow_lt_pow_left₀ 2 (D.rm_pos q hq).le
      rw [(D.chart q hq).morseNorm_sq_of_mem_leftModelSphere hy]
      exact hrm
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' :=
      mem_ball_of_morseNorm_lt (hlt.trans (D.rm_lt_R' q hq))
    refine ⟨?_, y, hlt, hyw⟩
    change posPart (D.chart q hq).hk
      ((D.chart q hq).χ.symm (D.flow (f z - (f q - ε)) z)) = 0
    rw [hz, ← hyw, (D.chart q hq).χ.left_inv ((D.chart q hq).hball hyb)]
    exact hy.1
  · rintro ⟨h0, y, hy, hyw⟩
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' :=
      mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' q hq))
    have hsy : (D.chart q hq).χ.symm (D.flow (c - (f q - ε)) z) = y := by
      rw [← hyw, (D.chart q hq).χ.left_inv ((D.chart q hq).hball hyb)]
    have hpos : posPart (D.chart q hq).hk y = 0 := by
      have h0' : posPart (D.chart q hq).hk
          ((D.chart q hq).χ.symm (D.flow (f z - (f q - ε)) z)) = 0 := h0
      rw [hz, hsy] at h0'
      exact h0'
    refine ⟨y, ⟨hpos, ?_⟩, hyw⟩
    have hn := (D.chart q hq).hnorm y ((show morseNorm n y < D.rm q hq from hy).le.trans
      (D.hrm q hq).2)
    rw [hyw, hTlev, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      hpos, norm_zero] at hn
    nlinarith [hn]

end GradientLikeStrip

theorem zero_set_eq_of_fderiv {m s : ℕ} (F : (Fin m → ℝ) → EuclideanSpace ℝ (Fin s))
    (y₀ : Fin m → ℝ) (hF : ContDiffAt ℝ 1 F y₀) (J : Finset (Fin m))
    (hP : ∀ᶠ y in 𝓝 y₀, (∀ j ∈ J, y j = y₀ j) → F y = 0)
    (hinj : ∀ v : Fin m → ℝ, (∀ j, j ∉ J → v j = 0) → fderiv ℝ F y₀ v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 y₀, F y = 0 ↔ ∀ j ∈ J, y j = y₀ j := by
  classical
  set L := fderiv ℝ F y₀ with hL
  let Q : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun j => if j ∈ J then LinearMap.proj j else 0)
  have hQ : ∀ v j, Q v j = if j ∈ J then v j else 0 := by
    intro v j
    by_cases hj : j ∈ J <;> simp [Q, hj]
  let T : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin s) × (Fin m → ℝ) :=
    (L.toLinearMap ∘ₗ Q).prod (LinearMap.id - Q)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : L (Q v) = 0 := congrArg Prod.fst hv
    have h2 : v - Q v = 0 := congrArg Prod.snd hv
    have hQv : Q v = 0 := by
      apply hinj
      · intro j hj
        rw [hQ]
        simp [hj]
      · exact h1
    rw [hQv, sub_zero] at h2
    exact h2
  obtain ⟨K, hKpos, hK⟩ := (LinearMap.injective_iff_antilipschitz T).1 hTinj
  have hbound : ∀ w : Fin m → ℝ, (∀ j, j ∉ J → w j = 0) → ‖w‖ ≤ (K : ℝ) * ‖L w‖ := by
    intro w hw
    have hQw : Q w = w := by
      funext j
      rw [hQ]
      by_cases hj : j ∈ J
      · simp [hj]
      · simp [hj, hw j hj]
    have hTw : T w = (L w, 0) := by
      change (L (Q w), w - Q w) = (L w, 0)
      rw [hQw, sub_self]
    have := hK.le_mul_dist w 0
    rw [map_zero, dist_zero_right, dist_zero_right, hTw, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _)] at this
    exact this
  let π : (Fin m → ℝ) → (Fin m → ℝ) := fun y j => if j ∈ J then y₀ j else y j
  have hπcont : Continuous π := by
    refine continuous_pi fun j => ?_
    by_cases hj : j ∈ J
    · simp only [π, hj, ite_true]; exact continuous_const
    · simp only [π, hj, ite_false]; exact continuous_apply j
  have hπ0 : π y₀ = y₀ := by
    funext j; simp only [π]; split_ifs <;> rfl
  have hπP : ∀ y, ∀ j ∈ J, π y j = y₀ j := by
    intro y j hj; simp only [π, hj, ite_true]
  have hstrict := (hF.hasStrictFDerivAt (by norm_num)).isLittleO
  have hc : (0 : ℝ) < 1 / (2 * (K : ℝ)) := by
    have : (0 : ℝ) < K := hKpos
    positivity
  have hest := hstrict.def hc
  have htend : Tendsto (fun y => (y, π y)) (𝓝 y₀) (𝓝 (y₀, y₀)) := by
    have : Continuous (fun y => (y, π y)) := continuous_id.prodMk hπcont
    have h := this.tendsto y₀
    simpa [hπ0] using h
  have hPπ : ∀ᶠ y in 𝓝 y₀, F (π y) = 0 := by
    have h := (hπcont.tendsto y₀).eventually (hπ0.symm ▸ hP)
    filter_upwards [h] with y hy
    exact hy (fun j hj => by rw [hπ0]; exact hπP y j hj)
  filter_upwards [htend.eventually hest, hPπ, hP] with y hy hFπ hPy
  refine ⟨fun hFy => ?_, hPy⟩
  simp only [hFy, hFπ, sub_zero, zero_sub, norm_neg] at hy
  set w := y - π y with hw
  have hwJ : ∀ j, j ∉ J → w j = 0 := by
    intro j hj
    simp only [hw, Pi.sub_apply, π, hj, ite_false, sub_self]
  have hb := hbound w hwJ
  have hKr : (0 : ℝ) < K := hKpos
  have hw0 : ‖w‖ = 0 := by
    have h1 : ‖w‖ ≤ (K : ℝ) * (1 / (2 * (K : ℝ)) * ‖w‖) :=
      hb.trans (mul_le_mul_of_nonneg_left hy hKr.le)
    have h2 : (K : ℝ) * (1 / (2 * (K : ℝ)) * ‖w‖) = ‖w‖ / 2 := by
      field_simp
    rw [h2] at h1
    linarith [norm_nonneg w]
  have hw00 : w = 0 := norm_eq_zero.1 hw0
  intro j hj
  have := congrFun hw00 j
  simp only [hw, Pi.sub_apply, Pi.zero_apply, π, hj, ite_true, sub_eq_zero] at this
  exact this

theorem exists_adaptedFields {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {s k : ℕ}
    (hsk : k + s + 1 = n) (G : M → EuclideanSpace ℝ (Fin s)) (z₀ : M)
    (hG : ∃ N ∈ 𝓝 z₀, ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G N)
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f z₀ ≠ 0)
    (hsub : ∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I z₀,
      mfderiv I 𝓘(ℝ, ℝ) f z₀ v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z₀ v = w) :
    ∃ Ys : Fin k → LevelField I f, ∃ N ∈ 𝓝 z₀,
      (∀ z ∈ N, ∀ j, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z ((Ys j).Y z) = 0) ∧
      LinearIndependent ℝ (fun j => ((Ys j).Y z₀ : Fin n → ℝ)) := by
  classical
  obtain ⟨N, hN, hGN⟩ := hG
  obtain ⟨N', hN'N, hN'o, hz₀N'⟩ := mem_nhds_iff.mp hN
  set e := extChartAt I z₀ with he_def
  have hz₀s : z₀ ∈ e.source := mem_extChartAt_source z₀
  set y₀ := e z₀ with hy₀_def
  have hy₀t : y₀ ∈ e.target := e.map_source hz₀s
  let g : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
  let Γ : (Fin n → ℝ) → EuclideanSpace ℝ (Fin s) := fun y => G (e.symm y)
  let T₀ : Set (Fin n → ℝ) := e.target ∩ e.symm ⁻¹' N'
  have hT₀o : IsOpen T₀ :=
    (continuousOn_extChartAt_symm z₀).isOpen_inter_preimage (isOpen_extChartAt_target z₀) hN'o
  have hy₀T₀ : y₀ ∈ T₀ := ⟨hy₀t, by
    change e.symm (e z₀) ∈ N'
    rw [e.left_inv hz₀s]; exact hz₀N'⟩
  have hg : ContDiffOn ℝ ∞ g e.target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm z₀))
  have hΓ : ContDiffOn ℝ ∞ Γ T₀ :=
    contMDiffOn_iff_contDiffOn.mp ((hGN.mono hN'N).comp
      ((contMDiffOn_extChartAt_symm z₀).mono inter_subset_left) (fun y hy => hy.2))
  have hgd : ∀ y ∈ e.target, DifferentiableAt ℝ g y := fun y hy =>
    ((hg y hy).contDiffAt ((isOpen_extChartAt_target z₀).mem_nhds hy)).differentiableAt
      (by simp)
  have hΓd : ∀ y ∈ T₀, DifferentiableAt ℝ Γ y := fun y hy =>
    ((hΓ y hy).contDiffAt (hT₀o.mem_nhds hy)).differentiableAt (by simp)
  have key : ∀ {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (h : M → F') (z : M),
      z ∈ e.source → DifferentiableAt ℝ (fun y => h (e.symm y)) (e z) →
      ∀ v : TangentSpace I z, mfderiv I 𝓘(ℝ, F') h z v =
        fderiv ℝ (fun y => h (e.symm y)) (e z) (mfderiv I 𝓘(ℝ, Fin n → ℝ) e z v) := by
    intro F' _ _ h z hz hd v
    have hzc : z ∈ (chartAt H z₀).source := by rwa [extChartAt_source] at hz
    have hme : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) e z := mdifferentiableAt_extChartAt hzc
    have hfe : h =ᶠ[𝓝 z] (fun y => h (e.symm y)) ∘ e := by
      filter_upwards [(isOpen_extChartAt_source z₀).mem_nhds hz] with w hw
      simp [e.left_inv hw]
    rw [hfe.mfderiv_eq, mfderiv_comp z hd.mdifferentiableAt hme, mfderiv_eq_fderiv]
    rfl
  let L₀ : (Fin n → ℝ) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin s) :=
    (fderiv ℝ g y₀).prod (fderiv ℝ Γ y₀)
  have hsurj : Function.Surjective L₀ := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, mfderiv I 𝓘(ℝ, ℝ) f z₀ v ≠ 0 := by
      by_contra! h
      exact hdf (ContinuousLinearMap.ext h)
    rw [key f z₀ hz₀s (hgd y₀ hy₀t)] at hv₀
    set u₀ : Fin n → ℝ := mfderiv I 𝓘(ℝ, Fin n → ℝ) e z₀ v₀ with hu₀
    set c := fderiv ℝ g y₀ u₀ with hc
    rintro ⟨a, w⟩
    obtain ⟨v, hv1, hv2⟩ := hsub (w - (a / c) • fderiv ℝ Γ y₀ u₀)
    rw [key f z₀ hz₀s (hgd y₀ hy₀t)] at hv1
    rw [key G z₀ hz₀s (hΓd y₀ hy₀T₀)] at hv2
    set u : Fin n → ℝ := mfderiv I 𝓘(ℝ, Fin n → ℝ) e z₀ v with hu
    refine ⟨(a / c) • u₀ + u, ?_⟩
    simp only [L₀, ContinuousLinearMap.prod_apply, map_add, map_smul]
    rw [show fderiv ℝ g y₀ u = 0 from hv1, show fderiv ℝ Γ y₀ u = _ from hv2, ← hc]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_zero]
      exact div_mul_cancel₀ a hv₀
    · simp only [Prod.snd_add, Prod.smul_snd]
      abel_nf
  let K₀ : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (L₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin s))
  have hK₀ : Module.finrank ℝ K₀ = k := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (L₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin s))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin, Module.finrank_fin_fun] at h
    change 1 + s + Module.finrank ℝ K₀ = n at h
    omega
  let φ : K₀ ≃ₗ[ℝ] (Fin k → ℝ) := LinearEquiv.ofFinrankEq _ _ (by rw [hK₀, Module.finrank_fin_fun])
  obtain ⟨q, hq⟩ := LinearMap.exists_extend (φ : K₀ →ₗ[ℝ] (Fin k → ℝ))
  let Q : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := LinearMap.toContinuousLinearMap q
  have hQ : ∀ v (hv : v ∈ K₀), Q v = φ ⟨v, hv⟩ := fun v hv => by
    have := LinearMap.congr_fun hq ⟨v, hv⟩
    simpa [Q] using this
  let T₀L : (Fin n → ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ) := L₀.prod Q
  have hinj : Function.Injective T₀L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : L₀ v = 0 := congrArg Prod.fst hv
    have h2 : Q v = 0 := congrArg Prod.snd hv
    have hvK : v ∈ K₀ := h1
    rw [hQ v hvK, LinearEquiv.map_eq_zero_iff] at h2
    exact congrArg Subtype.val h2
  have hdim : Module.finrank ℝ (Fin n → ℝ) =
      Module.finrank ℝ ((ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin, Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  let E₀ : (Fin n → ℝ) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ) :=
    (LinearMap.linearEquivOfInjective
      (T₀L : (Fin n → ℝ) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ)) hinj
      hdim).toContinuousLinearEquiv
  have hE₀ : (E₀ : (Fin n → ℝ) →L[ℝ] _) = T₀L := by
    ext1 v
    rfl
  let Ψ : (Fin n → ℝ) → (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ) :=
    fun y => ((g y, Γ y), Q y)
  let Tm : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ) :=
    fderiv ℝ Ψ
  have hΨ : ContDiffOn ℝ ∞ Ψ T₀ :=
    ((hg.mono inter_subset_left).prodMk hΓ).prodMk Q.contDiff.contDiffOn
  have hTm_eq : ∀ y ∈ T₀, Tm y = ((fderiv ℝ g y).prod (fderiv ℝ Γ y)).prod Q := fun y hy =>
    (((hgd y hy.1).hasFDerivAt.prodMk (hΓd y hy).hasFDerivAt).prodMk Q.hasFDerivAt).fderiv
  have hTm : ContDiffOn ℝ ∞ Tm T₀ := ((contDiffOn_infty_iff_fderiv_of_isOpen hT₀o).mp hΨ).2
  have hTm₀ : Tm y₀ = E₀ := by rw [hTm_eq y₀ hy₀T₀, hE₀]
  let U : Set (Fin n → ℝ) :=
    T₀ ∩ Tm ⁻¹' Set.range (ContinuousLinearEquiv.toContinuousLinearMap :
      ((Fin n → ℝ) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin s)) × (Fin k → ℝ)) → _)
  have hUo : IsOpen U := hTm.continuousOn.isOpen_inter_preimage hT₀o ContinuousLinearEquiv.isOpen
  have hy₀U : y₀ ∈ U := ⟨hy₀T₀, E₀, hTm₀.symm⟩
  let Yt : Fin k → (Fin n → ℝ) → (Fin n → ℝ) := fun i y =>
    (Tm y).inverse ((0 : ℝ × EuclideanSpace ℝ (Fin s)), (Pi.single i (1 : ℝ) : Fin k → ℝ))
  have hYt : ∀ i, ContDiffOn ℝ ∞ (Yt i) U := by
    intro i y hy
    obtain ⟨Ey, hEy⟩ := hy.2
    have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (Tm y) := by
      rw [← hEy]; exact contDiffAt_map_inverse Ey
    exact ((hinv.comp y ((hTm y hy.1).contDiffAt (hT₀o.mem_nhds hy.1))).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hYt_eq : ∀ i, ∀ y ∈ U, fderiv ℝ g y (Yt i y) = 0 ∧ fderiv ℝ Γ y (Yt i y) = 0 ∧
      Q (Yt i y) = Pi.single i (1 : ℝ) := by
    intro i y hy
    obtain ⟨Ey, hEy⟩ := hy.2
    have h : Tm y (Yt i y) =
        ((0 : ℝ × EuclideanSpace ℝ (Fin s)), (Pi.single i (1 : ℝ) : Fin k → ℝ)) := by
      simp only [Yt, ← hEy, ContinuousLinearMap.inverse_equiv]
      simp
    rw [hTm_eq y hy.1] at h
    simp only [ContinuousLinearMap.prod_apply, Prod.mk.injEq, Prod.mk_eq_zero] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hYt_ind : LinearIndependent ℝ (fun i => Yt i y₀) := by
    apply LinearIndependent.of_comp (Q : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    have : (Q : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) ∘ (fun i => Yt i y₀) = Pi.basisFun ℝ (Fin k) := by
      funext i
      simp [Pi.basisFun_apply, (hYt_eq i y₀ hy₀U).2.2]
    rw [this]
    exact (Pi.basisFun ℝ (Fin k)).linearIndependent
  let W : Set M := e.source ∩ e ⁻¹' U
  have hWo : IsOpen W :=
    (continuousOn_extChartAt z₀).isOpen_inter_preimage (isOpen_extChartAt_source z₀) hUo
  have hz₀W : z₀ ∈ W := ⟨hz₀s, hy₀U⟩
  let Yf : Fin k → (x : M) → TangentSpace I x := fun i x =>
    (mfderivWithin 𝓘(ℝ, Fin n → ℝ) I e.symm (range I) (e x) (Yt i (e x)) : Fin n → ℝ)
  have hYe : ∀ i, ∀ x ∈ e.source,
      mfderiv I 𝓘(ℝ, Fin n → ℝ) e x (Yf i x) = Yt i (e x) := by
    intro i x hx
    have h := DFunLike.congr_fun
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := z₀)
        (e.map_source hx)) (Yt i (e x))
    have hx' : e.symm (e x) = x := e.left_inv hx
    rw [hx'] at h
    exact h
  have hYsm : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, Yf i x⟩ : TangentBundle I M)) W := by
    intro i x hx
    have hxc : x ∈ (chartAt H z₀).source := by rw [← extChartAt_source I]; exact hx.1
    apply ContMDiffAt.contMDiffWithinAt
    rw [Bundle.Trivialization.contMDiffAt_section_iff
      (e := trivializationAt (Fin n → ℝ) (TangentSpace I) z₀)
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hxc)]
    have hfib : (fun y : M => (trivializationAt (Fin n → ℝ) (TangentSpace I) z₀
        ⟨y, Yf i y⟩).2) =ᶠ[𝓝 x] (fun y => Yt i (e y)) := by
      filter_upwards [hWo.mem_nhds hx] with y hy
      rw [DifferentialGeometry.Topology.Morse.tangentTrivializationAt_apply I z₀ y hy.1 (Yf i y)]
      exact hYe i y hy.1
    have hc : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (fun y => Yt i (e y)) x := by
      have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (Yt i) (e x) :=
        ((hYt i (e x) hx.2).contDiffAt (hUo.mem_nhds hx.2)).contMDiffAt
      exact h1.comp x (contMDiffAt_extChartAt' hxc)
    exact hc.congr_of_eventuallyEq hfib
  have hYlev : ∀ i, ∀ x ∈ W, dfV I f (Yf i) x = 0 ∧
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G x (Yf i x) = 0 := by
    intro i x hx
    have hxt : e x ∈ e.target := e.map_source hx.1
    have h := hYt_eq i (e x) hx.2
    refine ⟨?_, ?_⟩
    · have h1 := key f x hx.1 (hgd (e x) hxt) (Yf i x)
      rw [hYe i x hx.1] at h1
      have h0 : mfderiv I 𝓘(ℝ, ℝ) f x (Yf i x) = 0 := by rw [h1]; exact h.1
      simp only [dfV, h0, map_zero]
    · have h2 := key G x hx.1 (hΓd (e x) hx.2.1) (Yf i x)
      rw [hYe i x hx.1] at h2
      rw [h2]
      exact h.2.1
  obtain ⟨χ, -, hχW⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) z₀).mem_iff.mp (hWo.mem_nhds hz₀W)
  have hχ1 : χ z₀ = 1 := χ.eventuallyEq_one.eq_of_nhds
  have hex : ∀ i, ∃ Z : LevelField I f, ∀ x, Z.Y x = χ x • Yf i x := fun i =>
    LevelField.exists_smul_of_contMDiffOn hWo (hYsm i) (fun x hx => (hYlev i x hx).1)
      χ.contMDiff χ.hasCompactSupport hχW
  choose Ys hYs using hex
  refine ⟨Ys, W, hWo.mem_nhds hz₀W, ?_, ?_⟩
  · intro z hz j
    rw [hYs j z, map_smul, (hYlev j z hz).2, smul_zero]
  · have hYs₀ : ∀ j, (Ys j).Y z₀ = Yf j z₀ := fun j => by rw [hYs j z₀, hχ1, one_smul]
    let Dm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := by exact mfderiv I 𝓘(ℝ, Fin n → ℝ) e z₀
    apply LinearIndependent.of_comp (Dm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have : (Dm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ (fun j => ((Ys j).Y z₀ : Fin n → ℝ)) =
        fun i => Yt i y₀ := by
      funext j
      change Dm ((Ys j).Y z₀) = Yt j y₀
      rw [hYs₀ j]
      exact hYe j z₀ hz₀s
    rw [this]
    exact hYt_ind

theorem exists_levelFrame_along {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {m : ℕ}
    {K : Set (Fin m → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) {ψ : (Fin m → ℝ) → M}
    (hψ : ContinuousOn ψ K) (hreg : ∀ y ∈ K, mfderiv I 𝓘(ℝ, ℝ) f (ψ y) ≠ 0) :
    ∃ E : (Fin m → ℝ) → Fin (n - 1) → (Fin n → ℝ),
      (∀ j, ContinuousOn (fun y => (⟨ψ y, E y j⟩ : TangentBundle I M)) K) ∧
      ∀ y ∈ K, (∀ j, mfderiv I 𝓘(ℝ, ℝ) f (ψ y) (E y j) = 0) ∧ LinearIndependent ℝ (E y) := by
  classical
  by_cases hn : n = 0
  · have : IsEmpty (Fin (n - 1)) := by rw [hn]; exact Fin.isEmpty'
    exact ⟨fun _ _ => 0, fun j => isEmptyElim j,
      fun y _ => ⟨fun j => isEmptyElim j, linearIndependent_empty_type⟩⟩
  have hk : n - 1 + 0 + 1 = n := by omega
  have hlev : ∀ (Z : LevelField I f) (x : M), mfderiv I 𝓘(ℝ, ℝ) f x (Z.Y x) = 0 := by
    intro Z x
    have h := Z.level x
    unfold dfV at h
    exact (NormedSpace.fromTangentSpace (f x)).map_eq_zero_iff.1 h
  have hloc : ∀ y₀ : K, ∃ X : Fin (n - 1) → LevelField I f, ∃ U : Set (Fin m → ℝ), IsOpen U ∧
      (y₀ : Fin m → ℝ) ∈ U ∧
      ∀ y ∈ U ∩ K, LinearIndependent ℝ (fun j => ((X j).Y (ψ y) : Fin n → ℝ)) := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨X, -, -, -, hXind⟩ := exists_adaptedFields (I := I) hf (s := 0) (k := n - 1) hk
      (fun _ => 0) (ψ y₀) ⟨univ, univ_mem, contMDiffOn_const⟩ (hreg y₀ hy₀)
      (fun w => ⟨0, by simp, by rw [Subsingleton.elim w 0]; exact map_zero _⟩)
    have hev : ∀ᶠ x in 𝓝 (ψ y₀), LinearIndependent ℝ (fun j => ((X j).Y x : Fin n → ℝ)) := by
      set e := trivializationAt (Fin n → ℝ) (TangentSpace I) (ψ y₀) with he
      have hz₀ : ψ y₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
      let w : M → Fin (n - 1) → Fin n → ℝ := fun x j => (e ⟨x, (X j).Y x⟩).2
      have hw : ContinuousAt w (ψ y₀) := by
        refine continuousAt_pi.2 fun j => ?_
        have hs : Continuous (fun x => (⟨x, (X j).Y x⟩ : TangentBundle I M)) :=
          (X j).smooth.continuous
        have he' : ContinuousAt e ⟨ψ y₀, (X j).Y (ψ y₀)⟩ :=
          e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.2 hz₀))
        exact (continuous_snd.continuousAt.comp
          (he'.comp (f := fun x => (⟨x, (X j).Y x⟩ : TangentBundle I M)) hs.continuousAt))
      have hw₀ : LinearIndependent ℝ (w (ψ y₀)) := by
        have := hXind.map' ((e.continuousLinearEquivAt ℝ (ψ y₀) hz₀ :
          TangentSpace I (ψ y₀) →L[ℝ] (Fin n → ℝ)) : TangentSpace I (ψ y₀) →ₗ[ℝ] (Fin n → ℝ))
          (LinearEquiv.ker (e.continuousLinearEquivAt ℝ (ψ y₀) hz₀).toLinearEquiv)
        exact this
      filter_upwards [hw.eventually (hw₀.eventually), e.open_baseSet.mem_nhds hz₀] with x hx hxb
      exact LinearIndependent.of_comp ((e.continuousLinearEquivAt ℝ x hxb :
        TangentSpace I x →L[ℝ] (Fin n → ℝ)) : TangentSpace I x →ₗ[ℝ] (Fin n → ℝ)) hx
    obtain ⟨O, hOsub, hOo, hzO⟩ := mem_nhds_iff.1 hev
    obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 hψ) O hOo
    refine ⟨X, U, hUo, ?_, ?_⟩
    · have h : y₀ ∈ ψ ⁻¹' O ∩ K := ⟨hzO, hy₀⟩
      rw [hU] at h
      exact h.1
    · intro y hy
      have h : y ∈ ψ ⁻¹' O ∩ K := by rw [hU]; exact hy
      exact hOsub h.1
  choose X U hUo hyU hXind using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => U y) (fun y => hUo y)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyU _⟩)
  have hcov : K ⊆ ⋃ i : t, U i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hyi⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed (fun i : t => U i)
    (fun i => hUo i) hcov
  have hρsum : ∀ y ∈ K, ∑ i : t, ρ i y = 1 := fun y hy => by
    rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hy
  let J := t × Fin (n - 1)
  let N := Fintype.card J
  let eJ : J ≃ Fin N := Fintype.equivFin J
  let Xs : Fin N → LevelField I f := fun i => X ((eJ.symm i).1 : K) (eJ.symm i).2
  let v : (Fin m → ℝ) → Fin N → Fin n → ℝ := fun y i => (Xs i).Y (ψ y)
  have hvc : ∀ i, ContinuousOn (fun y => (⟨ψ y, v y i⟩ : TangentBundle I M)) K := fun i =>
    (Xs i).smooth.continuous.comp_continuousOn hψ
  have hfrc : ∀ (a : K) (k : Fin (n - 1)),
      ContinuousOn (fun y => (⟨ψ y, (X a k).Y (ψ y)⟩ : TangentBundle I M)) K := fun a k =>
    (X a k).smooth.continuous.comp_continuousOn hψ
  let fr : K → (Fin m → ℝ) → Fin (n - 1) → Fin n → ℝ := fun a y k => (X a k).Y (ψ y)
  have hfrind : ∀ (a : K), ∀ y ∈ U a ∩ K, LinearIndependent ℝ (fr a y) := fun a y hy =>
    hXind a y hy
  have hvlev : ∀ y i, mfderiv I 𝓘(ℝ, ℝ) f (ψ y) (v y i) = 0 := fun y i => hlev (Xs i) (ψ y)
  let D : (Fin m → ℝ) → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun y => by
    exact ((show (Fin n → ℝ) →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f (ψ y)) : (Fin n → ℝ) →ₗ[ℝ] ℝ)
  have hD : ∀ y w, D y w = mfderiv I 𝓘(ℝ, ℝ) f (ψ y) w := fun _ _ => rfl
  have hkerle : ∀ y ∈ K, Module.finrank ℝ (LinearMap.ker (D y)) ≤ n - 1 := by
    intro y hy
    have hne : LinearMap.ker (D y) ≠ ⊤ := by
      intro htop
      apply hreg y hy
      refine ContinuousLinearMap.ext fun w => ?_
      have hw : (show Fin n → ℝ from w) ∈ LinearMap.ker (D y) := by rw [htop]; exact Submodule.mem_top
      exact LinearMap.mem_ker.1 hw
    have := Submodule.finrank_lt hne
    rw [Module.finrank_fin_fun] at this
    omega
  have hspan : ∀ (a : K), ∀ y ∈ U a ∩ K,
      Submodule.span ℝ (range (fr a y)) = LinearMap.ker (D y) := by
    intro a y hy
    refine Submodule.eq_of_le_of_finrank_le
      (Submodule.span_le.2 (range_subset_iff.2 fun k => LinearMap.mem_ker.2 (hlev _ _))) ?_
    rw [show Module.finrank ℝ (Submodule.span ℝ (range (fr a y))) = n - 1 from
      (finrank_span_eq_card (hfrind a y hy)).trans (Fintype.card_fin _)]
    exact hkerle y hy.2
  have hcoef : ∀ (a : t) (i : Fin N), ∃ c : (Fin m → ℝ) → Fin (n - 1) → ℝ,
      ContinuousOn c (U a ∩ K) ∧ ∀ y ∈ U a ∩ K, ∑ k, c y k • fr a y k = v y i := by
    intro a i
    exact exists_continuousOn_frameCoeff (hψ.mono inter_subset_right)
      (fun k => (hfrc a k).mono inter_subset_right) (hXind a) ((hvc i).mono inter_subset_right)
      (fun y hy => by rw [hspan a y hy]; exact LinearMap.mem_ker.2 (hlev _ _))
  choose c hc hcsum using hcoef
  have hent : ∀ (a : t) (i' : Fin N) (k : Fin (n - 1)),
      ContinuousOn (fun y => ρ a y * c a i' y k) K := by
    intro a i' k y hy
    by_cases hya : y ∈ U a
    · have h1 : ContinuousWithinAt (fun y => ρ a y * c a i' y k) (U a ∩ K) y :=
        (ρ a).continuous.continuousWithinAt.mul
          (((continuous_apply k).comp_continuousOn (hc a i')) y ⟨hya, hy⟩)
      rw [inter_comm] at h1
      exact (continuousWithinAt_inter ((hUo a).mem_nhds hya)).1 h1
    · have hns : y ∉ tsupport (ρ a) := fun h => hya (hρ a h)
      rw [notMem_tsupport_iff_eventuallyEq] at hns
      have h0 : (fun y => ρ a y * c a i' y k) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hns] with z hz
        simp only [Pi.zero_apply] at hz
        rw [hz, zero_mul]
      exact (continuousAt_const.congr h0.symm).continuousWithinAt
  let Qm : (Fin m → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun y i i' =>
    ρ (eJ.symm i).1 y * c (eJ.symm i).1 i' y (eJ.symm i).2
  have hQm : ContinuousOn Qm K :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun i' => hent _ _ _
  let Φ : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toLin'.toLinearMap
  let P : (Fin m → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun y => Φ (Qm y)
  have hP : ContinuousOn P K := (LinearMap.continuous_of_finiteDimensional Φ).comp_continuousOn hQm
  have hPapp : ∀ y c', P y c' = Matrix.mulVec (Qm y) c' := fun y c' => Matrix.toLin'_apply _ _
  let A : (Fin m → ℝ) → (Fin N → ℝ) →ₗ[ℝ] (Fin n → ℝ) := fun y =>
    { toFun := fun c' => ∑ i, c' i • v y i
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hA : ∀ y c', A y c' = ∑ i, c' i • v y i := fun _ _ => rfl
  have hcol : ∀ y ∈ K, ∀ i', ∑ i, Qm y i i' • v y i = v y i' := by
    intro y hy i'
    have h1 : ∑ i, Qm y i i' • v y i =
        ∑ p : J, (ρ p.1 y * c p.1 i' y p.2) • fr p.1 y p.2 :=
      Equiv.sum_comp eJ.symm (fun p : J => (ρ p.1 y * c p.1 i' y p.2) • fr p.1 y p.2)
    rw [h1, Fintype.sum_prod_type]
    calc ∑ a : t, ∑ k, (ρ a y * c a i' y k) • fr a y k = ∑ a : t, ρ a y • v y i' := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [mul_smul, ← Finset.smul_sum]
          by_cases hya : y ∈ U a
          · rw [hcsum a i' y ⟨hya, hy⟩]
          · have : ρ a y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hya (hρ a h))
            rw [this, zero_smul, zero_smul]
      _ = v y i' := by rw [← Finset.sum_smul, hρsum y hy, one_smul]
  have KA : ∀ y ∈ K, ∀ c', A y (P y c') = A y c' := by
    intro y hy c'
    rw [hA, hA, hPapp]
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ i, (∑ i', Qm y i i' * c' i') • v y i = ∑ i', ∑ i, (Qm y i i' * c' i') • v y i := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_smul
      _ = ∑ i', c' i' • v y i' := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hcol y hy i', Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
  have KB : ∀ y ∈ K, ∀ c', A y c' = 0 → P y c' = 0 := by
    intro y hy c' hAc
    rw [hPapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Qm]
    by_cases hya : y ∈ U (eJ.symm i).1
    · have hβ := Fintype.linearIndependent_iff.1 (hXind _ y ⟨hya, hy⟩)
        (fun k => ∑ i', c' i' * c (eJ.symm i).1 i' y k) (by
          calc ∑ k, (∑ i', c' i' * c (eJ.symm i).1 i' y k) • fr (eJ.symm i).1 y k
              = ∑ i', c' i' • ∑ k, c (eJ.symm i).1 i' y k • fr (eJ.symm i).1 y k := by
                simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
                exact Finset.sum_comm
            _ = ∑ i', c' i' • v y i' := by
                refine Finset.sum_congr rfl fun i' _ => ?_
                rw [hcsum _ i' y ⟨hya, hy⟩]
            _ = 0 := hAc) (eJ.symm i).2
      calc ∑ i', ρ (eJ.symm i).1 y * c (eJ.symm i).1 i' y (eJ.symm i).2 * c' i'
          = ρ (eJ.symm i).1 y * ∑ i', c' i' * c (eJ.symm i).1 i' y (eJ.symm i).2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i' _ => by ring
        _ = 0 := by rw [hβ, mul_zero]
    · have : ρ (eJ.symm i).1 y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hya (hρ _ h))
      simp [this]
  have hPP : ∀ y ∈ K, ∀ c', P y (P y c') = P y c' := by
    intro y hy c'
    have h := KB y hy (P y c' - c') (by rw [map_sub, KA y hy, sub_self])
    rw [map_sub, sub_eq_zero] at h
    exact h
  have hidem : ∀ y ∈ K, (P y).comp (P y) = P y := fun y hy =>
    ContinuousLinearMap.ext fun c' => hPP y hy c'
  have hrank : ∀ y ∈ K,
      Module.finrank ℝ (LinearMap.range (P y : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) = n - 1 := by
    intro y hy
    set Pl : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := (P y : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) with hPl
    have hker : LinearMap.ker ((A y).comp Pl) = LinearMap.ker Pl := by
      ext c'
      simp only [LinearMap.mem_ker, LinearMap.comp_apply]
      constructor
      · intro h
        have h' := KB y hy _ h
        rw [hPl, ContinuousLinearMap.coe_coe, hPP y hy] at h'
        exact h'
      · intro h
        rw [h, map_zero]
    have hrng : LinearMap.range ((A y).comp Pl) = LinearMap.range (A y) := by
      have : (A y).comp Pl = A y := LinearMap.ext fun c' => KA y hy c'
      rw [this]
    have h1 := LinearMap.finrank_range_add_finrank_ker Pl
    have h2 := LinearMap.finrank_range_add_finrank_ker ((A y).comp Pl)
    rw [hker, hrng] at h2
    have hRA : Module.finrank ℝ (LinearMap.range (A y)) = n - 1 := by
      obtain ⟨a, hya⟩ : ∃ a : t, y ∈ U a := mem_iUnion.1 (hcov hy)
      apply le_antisymm
      · calc Module.finrank ℝ (LinearMap.range (A y)) ≤ Module.finrank ℝ (LinearMap.ker (D y)) := by
              refine Submodule.finrank_mono ?_
              rintro _ ⟨c', rfl⟩
              rw [LinearMap.mem_ker, hA, map_sum]
              refine Finset.sum_eq_zero fun i _ => ?_
              rw [map_smul, show D y (v y i) = 0 from hvlev y i, smul_zero]
          _ ≤ n - 1 := hkerle y hy
      · calc n - 1 = Module.finrank ℝ
              (Submodule.span ℝ (range (fr a y))) := by
              exact ((finrank_span_eq_card (hfrind a y ⟨hya, hy⟩)).trans
                (Fintype.card_fin _)).symm
          _ ≤ Module.finrank ℝ (LinearMap.range (A y)) := by
              refine Submodule.finrank_mono (Submodule.span_le.2 (range_subset_iff.2 fun k => ?_))
              refine ⟨Pi.single (eJ (a, k)) 1, ?_⟩
              rw [hA, Finset.sum_eq_single (eJ (a, k))]
              · simp only [v, Xs, Pi.single_eq_same, Equiv.symm_apply_apply]
                exact one_smul ℝ _
              · intro b _ hb
                rw [Pi.single_eq_of_ne hb, zero_smul]
              · intro h
                exact absurd (Finset.mem_univ _) h
    omega
  obtain ⟨F, hF, hFind⟩ := exists_frame_of_projections hK hKc P hP hidem hrank
  refine ⟨fun y j => ∑ i, F y j i • v y i, fun j => ?_, fun y hy => ⟨fun j => ?_, ?_⟩⟩
  · exact continuousOn_frameVec_tangentBundle hψ hvc ((continuous_apply j).comp_continuousOn hF)
  · change D y (∑ i, F y j i • v y i) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, show D y (v y i) = 0 from hvlev y i, smul_zero]
  · change LinearIndependent ℝ ((A y) ∘ F y)
    refine (hFind y hy).1.map ?_
    rw [Submodule.disjoint_def]
    intro x hx hxA
    have hxP : x ∈ LinearMap.range (P y : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) :=
      Submodule.span_le.2 (range_subset_iff.2 (hFind y hy).2) hx
    obtain ⟨c', rfl⟩ := hxP
    have h := KB y hy _ (LinearMap.mem_ker.1 hxA)
    rw [ContinuousLinearMap.coe_coe] at h ⊢
    rw [hPP y hy] at h
    exact h

end FlowCharts

end

end DifferentialGeometry.Topology
