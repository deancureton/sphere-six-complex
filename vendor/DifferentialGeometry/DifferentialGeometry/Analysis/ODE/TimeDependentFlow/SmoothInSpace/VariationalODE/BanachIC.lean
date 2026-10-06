module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.UniformExistence
public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.InfiniteOrder

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

section SmoothLocalFlow

open Set Metric Function DifferentialGeometry.Analysis.ODE.Flow
open scoped NNReal

theorem exists_isLocalFlow_contDiffOn_top
    [CompleteSpace E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε)
      (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (ρ : ℝ) (T : ℝ), 0 < ρ ∧ 0 < T ∧ (ρ : ℝ) ≤ r ∧ T ≤ ε ∧
        ContDiffOn ℝ ∞ Φ
          (Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (univ : Set (ℝ × E)) :=
    hf.contDiffOn.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    exists_isLocalFlow_of_contDiffOn_univ f hf_C1 t₀ x₀
  have hrN_pos : (0 : ℝ) < rN := hrN
  have hpartial_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (univ : Set ℝ)) (u := (univ : Set E))
      (by rwa [univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [univ_prod_univ] at h
  have hcomp_cont : ContinuousOn
      (fun q : E × ℝ => (q.2, Φ q))
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    continuousOn_snd.prodMk hΦ.continuousOn
  have hfull_cont : ContinuousOn
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    hpartial_cont.comp hcomp_cont (fun _ _ => mem_univ _)
  have hnorm_cont : ContinuousOn
      (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖)
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    continuous_norm.comp_continuousOn hfull_cont
  have hK : IsCompact (closedBall x₀ (rN : ℝ) ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    (ProperSpace.isCompact_closedBall x₀ rN).prod isCompact_Icc
  have hne : (closedBall x₀ (rN : ℝ) ×ˢ Icc (t₀ - εN) (t₀ + εN)).Nonempty :=
    ⟨⟨x₀, t₀⟩, mem_prod.mpr
      ⟨mem_closedBall_self (by exact_mod_cast le_of_lt hrN),
       mem_Icc.mpr ⟨by linarith, by linarith⟩⟩⟩
  obtain ⟨q₀, hq₀_mem, hq₀_max⟩ := hK.exists_isMaxOn hne hnorm_cont
  set Mglob := ‖fderiv ℝ (f q₀.2) (Φ q₀)‖
  have hMglob_nn : 0 ≤ Mglob := norm_nonneg _
  have hMglob_bound : ∀ x ∈ closedBall x₀ (rN : ℝ),
      ∀ τ ∈ Icc (t₀ - εN) (t₀ + εN), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ Mglob := by
    intro x hx τ hτ
    exact hq₀_max (show (x, τ) ∈ _ from ⟨hx, hτ⟩)
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1)))
  have hTcap_pos : 0 < Tcap := lt_min hεN (by positivity)
  set T_out : ℝ := Tcap / 2
  set T_mid : ℝ := Tcap / 4
  set T : ℝ := Tcap / 8
  have hT_pos : 0 < T := by change 0 < Tcap / 8; linarith
  have hT_lt_mid : T < T_mid := by change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    change Tcap / 2 ≤ εN
    have : Tcap ≤ εN := min_le_left _ _
    linarith
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith
    have hMplus_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) :=
            mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := by
            rw [div_le_div_iff₀ hMplus_pos (by norm_num : (0 : ℝ) < 8)]
            nlinarith [hMglob_nn]
      _ < 1 := by norm_num
  have hsub_T_out : Icc (t₀ - T_out) (t₀ + T_out) ⊆
      Icc (t₀ - εN) (t₀ + εN) :=
    Icc_subset_Icc (by linarith [hT_out_le_eps]) (by linarith [hT_out_le_eps])
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8; linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ); linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ); linarith
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ),
      ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ Mglob := by
    intro x hx τ hτ
    exact hMglob_bound x (closedBall_subset_closedBall hρ_out_le_r hx) τ (hsub_T_out hτ)
  have hSmooth :=
    IsLocalFlow.contDiffOn_top
      hΦ hf hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  refine ⟨rN, εN, hrN, hεN, Φ, hΦ, (ρ : ℝ), T, hρ_pos, hT_pos, ?_, ?_, hSmooth⟩
  · change (rN : ℝ) / 8 ≤ (rN : ℝ); linarith
  · change Tcap / 8 ≤ εN
    have : Tcap ≤ εN := min_le_left _ _
    linarith

end SmoothLocalFlow

section TransferSmoothness

open Set Metric Function DifferentialGeometry.Analysis.ODE.Flow
open scoped NNReal Topology

variable [CompleteSpace E]

omit [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem ChartLocalPicardData.contDiffOn_top
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (hSmoothX_chart : ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E))) :
    ∃ (ρ : ℝ) (T₀ : ℝ), 0 < ρ ∧ 0 < T₀ ∧ ρ ≤ hper.r ∧ T₀ ≤ hper.T ∧
      ContDiffOn ℝ ∞ (Function.uncurry hper.flow)
        (Metric.ball (I ((chartAt H α) α)) ρ ×ˢ Set.Ioo 0 T₀) := by
  set center : E := I ((chartAt H α) α)
  set fChart : ℝ → E → E := fun t y => (X t ((chartAt H α).symm (I.symm y)) : E)
  have hf_top : ContDiff ℝ ∞ (Function.uncurry fChart) := hSmoothX_chart
  obtain ⟨rN, εN, hrN, hεN, Φ_pl, hΦ_pl, ρ_pl, T_pl, hρ_pl_pos, hT_pl_pos,
    hρ_pl_le, hT_pl_le, hΦ_smooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := fChart) (t₀ := 0) (x₀ := center) hf_top
  set ρ₀ : ℝ := min ρ_pl hper.r
  set T₀ : ℝ := min T_pl hper.T
  have hρ₀_pos : 0 < ρ₀ := lt_min hρ_pl_pos hper.r_pos
  have hT₀_pos : 0 < T₀ := lt_min hT_pl_pos hper.T_pos
  have hρ₀_le_ρ_pl : ρ₀ ≤ ρ_pl := min_le_left _ _
  have hρ₀_le_r : ρ₀ ≤ hper.r := min_le_right _ _
  have hT₀_le_T_pl : T₀ ≤ T_pl := min_le_left _ _
  have hT₀_le_T : T₀ ≤ hper.T := min_le_right _ _
  have hΦ_initial : ∀ x ∈ closedBall center rN, Φ_pl ⟨x, 0⟩ = x := by
    intro x hx; exact hΦ_pl.apply_initial x hx
  have hΦ_deriv : ∀ x ∈ closedBall center rN, ∀ t ∈ Icc (0 - εN) (0 + εN),
      HasDerivWithinAt (fun s => Φ_pl ⟨x, s⟩) (fChart t (Φ_pl ⟨x, t⟩))
        (Icc (0 - εN) (0 + εN)) t :=
    hΦ_pl.hasDerivWithinAt
  have hT₀_le_εN : T₀ ≤ εN := hT₀_le_T_pl.trans hT_pl_le
  have hIcc_sub_hartman : Icc 0 T₀ ⊆ Icc (0 - εN) (0 + εN) := by
    intro t ht; simp only [zero_sub, zero_add] at *
    exact ⟨le_trans (neg_nonpos_of_nonneg hεN.le) ht.1, ht.2.trans hT₀_le_εN⟩
  have hρ₀_le_rN : ρ₀ ≤ (rN : ℝ) := hρ₀_le_ρ_pl.trans hρ_pl_le
  have hcb_sub : closedBall center ρ₀ ⊆ closedBall center rN :=
    closedBall_subset_closedBall hρ₀_le_rN
  have hflow_cont : ∀ y ∈ closedBall center ρ₀,
      ContinuousOn (hper.flow y) (Icc 0 T₀) := by
    intro y hy
    have hspec := hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)
    have hcont_full : ContinuousOn (hper.flow y) (Icc 0 hper.T) :=
      fun t ht => (hspec.2 t ht).continuousWithinAt
    exact hcont_full.mono (Icc_subset_Icc le_rfl hT₀_le_T)
  have hΦ_cont : ∀ y ∈ closedBall center ρ₀,
      ContinuousOn (fun t => Φ_pl ⟨y, t⟩) (Icc 0 T₀) := by
    intro y hy
    exact (hΦ_pl.orbit_continuousOn y (hcb_sub hy)).mono hIcc_sub_hartman
  have heq_on : ∀ y ∈ closedBall center ρ₀,
      EqOn (fun t => Φ_pl ⟨y, t⟩) (hper.flow y) (Icc 0 T₀) := by
    intro y hy
    have hΦy_cont := hΦ_cont y hy
    have hflow_y_cont := hflow_cont y hy
    have hΦy_bdd : Bornology.IsBounded ((fun t => Φ_pl ⟨y, t⟩) '' Icc 0 T₀) :=
      (isCompact_Icc.image_of_continuousOn hΦy_cont).isBounded
    have hflow_y_bdd : Bornology.IsBounded ((hper.flow y) '' Icc 0 T₀) :=
      (isCompact_Icc.image_of_continuousOn hflow_y_cont).isBounded
    obtain ⟨R_Φ, hR_Φ⟩ := hΦy_bdd.subset_ball 0
    obtain ⟨R_f, hR_f⟩ := hflow_y_bdd.subset_ball 0
    set R : ℝ := max (max R_Φ R_f) 0 + 1
    have hR_pos : 0 < R := by linarith [le_max_right (max R_Φ R_f) 0]
    have hΦy_in : ∀ t ∈ Ico (0 : ℝ) T₀, Φ_pl ⟨y, t⟩ ∈ closedBall (0 : E) R := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T₀ := Ico_subset_Icc_self ht
      have := hR_Φ (mem_image_of_mem _ ht')
      rw [mem_ball] at this
      rw [mem_closedBall]
      calc dist (Φ_pl ⟨y, t⟩) 0 ≤ R_Φ := le_of_lt this
        _ ≤ max R_Φ R_f := le_max_left _ _
        _ ≤ max (max R_Φ R_f) 0 := le_max_left _ _
        _ ≤ R := by linarith
    have hflow_y_in : ∀ t ∈ Ico (0 : ℝ) T₀, hper.flow y t ∈ closedBall (0 : E) R := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T₀ := Ico_subset_Icc_self ht
      have := hR_f (mem_image_of_mem _ ht')
      rw [mem_ball] at this
      rw [mem_closedBall]
      calc dist (hper.flow y t) 0 ≤ R_f := le_of_lt this
        _ ≤ max R_Φ R_f := le_max_right _ _
        _ ≤ max (max R_Φ R_f) 0 := le_max_left _ _
        _ ≤ R := by linarith
    have hfchart_t_diff : ∀ t : ℝ, Differentiable ℝ (fChart t) := by
      intro t
      have h1 : ContDiff ℝ ∞ (fChart t) := by
        change ContDiff ℝ ∞ (fun y : E => uncurry fChart (t, y))
        exact hf_top.comp (contDiff_const.prodMk contDiff_id)
      exact h1.differentiable (by simp)
    have hfchart_C1 : ContDiffOn ℝ 1 (uncurry fChart) univ :=
      hf_top.contDiffOn.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    have hfderiv_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fChart p.1) p.2) univ := by
      have h := continuousOn_partialFDeriv_uncurry (f := fChart)
        (s := (univ : Set ℝ)) (u := (univ : Set E))
        (by rwa [univ_prod_univ]) isOpen_univ isOpen_univ
      rwa [univ_prod_univ] at h
    have hcompact_domain : IsCompact (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R) :=
      isCompact_Icc.prod (ProperSpace.isCompact_closedBall 0 R)
    have hne_domain : (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R).Nonempty :=
      ⟨(0, 0), mem_prod.mpr ⟨left_mem_Icc.mpr hT₀_pos.le, mem_closedBall_self hR_pos.le⟩⟩
    have hnorm_fderiv_cont : ContinuousOn
        (fun p : ℝ × E => ‖fderiv ℝ (fChart p.1) p.2‖)
        (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R) :=
      (continuous_norm.comp_continuousOn
        (hfderiv_cont.mono (subset_univ _)))
    obtain ⟨p₀, _, hp₀_max⟩ :=
      hcompact_domain.exists_isMaxOn hne_domain hnorm_fderiv_cont
    set Kval : ℝ := ‖fderiv ℝ (fChart p₀.1) p₀.2‖
    have hKval_nn : 0 ≤ Kval := norm_nonneg _
    set K : ℝ≥0 := ⟨Kval, hKval_nn⟩
    have hfchart_lip : ∀ t ∈ Ico (0 : ℝ) T₀,
        LipschitzOnWith K (fChart t) (closedBall (0 : E) R) := by
      intro t ht
      apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun x hx => ((hfchart_t_diff t x).hasFDerivAt).hasFDerivWithinAt)
      · intro x hx
        change ‖fderiv ℝ (fChart t) x‖₊ ≤ K
        rw [← NNReal.coe_le_coe]
        change ‖fderiv ℝ (fChart t) x‖ ≤ Kval
        have : (t, x) ∈ Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R :=
          ⟨Ico_subset_Icc_self ht, hx⟩
        exact hp₀_max this
      · exact convex_closedBall 0 R
    have hΦy_deriv : ∀ t ∈ Ico (0 : ℝ) T₀,
        HasDerivWithinAt (fun s => Φ_pl ⟨y, s⟩)
          (fChart t (Φ_pl ⟨y, t⟩)) (Ici t) t := by
      intro t ht
      have ht_hartman : t ∈ Icc (0 - εN) (0 + εN) :=
        hIcc_sub_hartman (Ico_subset_Icc_self ht)
      have hdw := hΦ_deriv y (hcb_sub hy) t ht_hartman
      have ht_lt_εN : t < εN := lt_of_lt_of_le ht.2 hT₀_le_εN
      have hmem : Icc (0 - εN) (0 + εN) ∈ 𝓝[≥] t := by
        simp only [zero_sub, zero_add]
        exact Icc_mem_nhdsGE_of_mem ⟨le_trans (neg_nonpos_of_nonneg hεN.le) ht.1, ht_lt_εN⟩
      exact hdw.mono_of_mem_nhdsWithin hmem
    have hflow_y_deriv : ∀ t ∈ Ico (0 : ℝ) T₀,
        HasDerivWithinAt (hper.flow y)
          (fChart t (hper.flow y t)) (Ici t) t := by
      intro t ht
      have hspec := hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)
      have ht_Icc : t ∈ Icc (0 : ℝ) hper.T := ⟨ht.1, (Ico_subset_Icc_self ht).2.trans hT₀_le_T⟩
      have hdw := hspec.2 t ht_Icc
      have ht_lt_T : t < hper.T := lt_of_lt_of_le ht.2 hT₀_le_T
      have hmem : Icc (0 : ℝ) hper.T ∈ 𝓝[≥] t :=
        Icc_mem_nhdsGE_of_mem ⟨ht.1, ht_lt_T⟩
      exact hdw.mono_of_mem_nhdsWithin hmem
    have hinit : Φ_pl ⟨y, 0⟩ = hper.flow y 0 := by
      rw [hΦ_initial y (hcb_sub hy)]
      exact (hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)).1.symm
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun t z => fChart t z) (s := fun _ => closedBall 0 R) (K := K)
      hfchart_lip hΦy_cont hΦy_deriv hΦy_in hflow_y_cont hflow_y_deriv hflow_y_in hinit
  have hΦ_smooth_sub : ContDiffOn ℝ ∞ Φ_pl
      (ball center ρ₀ ×ˢ Ioo 0 T₀) := by
    apply hΦ_smooth.mono
    apply prod_mono
    · exact ball_subset_ball hρ₀_le_ρ_pl
    · intro t ht
      simp only [zero_sub, zero_add, mem_Ioo] at *
      exact ⟨by linarith [hT_pl_pos], by linarith [hT₀_le_T_pl]⟩
  have hcongr : ∀ q ∈ ball center ρ₀ ×ˢ Ioo (0 : ℝ) T₀,
      uncurry hper.flow q = Φ_pl q := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    simp only [uncurry]
    have hx_cb : x ∈ closedBall center ρ₀ :=
      mem_closedBall.mpr (le_of_lt (mem_ball.mp hx))
    have ht_Icc : t ∈ Icc (0 : ℝ) T₀ := Ioo_subset_Icc_self ht
    exact (heq_on x hx_cb ht_Icc).symm
  exact ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_r, hT₀_le_T,
    hΦ_smooth_sub.congr hcongr⟩

end TransferSmoothness

end DifferentialGeometry.Analysis.ODE
