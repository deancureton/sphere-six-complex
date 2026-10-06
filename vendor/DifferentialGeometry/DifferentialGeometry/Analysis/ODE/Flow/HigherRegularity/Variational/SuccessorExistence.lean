module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.FirstOrderSmoothness

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] variationalAugmentedEndNormedAddCommGroup

section SuccStepWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_isVariationalFlowProjection_succ_C_step
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (n : ℕ)
    (hf_C : ContDiffOn ℝ ((n : ℕ∞) + 2) (uncurry f) (Set.univ : Set (ℝ × E)))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    (ht₀_a_Ioo : t₀ ∈ Ioo tmin_a tmax_a)
    (hR_aug_pos : (0 : ℝ) < (R_aug : ℝ))
    {T_ih : ℝ} {ρ_ih : ℝ≥0}
    {Y_ih : (E × (E →L[ℝ] E)) × ℝ → ((E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))}
    (_hT_ih_pos : 0 < T_ih) (_hρ_ih_pos : 0 < (ρ_ih : ℝ))
    (hY_ih : IsVariationalFlowProjection haΦ T_ih ρ_ih Y_ih (n : ℕ∞)) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y ((n : ℕ∞) + 1) := by
  classical
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    refine hf_C.of_le ?_
    have h1 : (1 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := by
      have h2 : (1 : WithTop ℕ∞) ≤ 2 := by decide
      have h3 : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := le_add_self
      exact le_trans h2 h3
    exact h1
  have hf_Cn_plus_2_as_succ : ContDiffOn ℝ (((n : ℕ∞) + 1) + 1) (uncurry f)
      (Set.univ : Set (ℝ × E)) := by
    have h_eq_wt :
        ((((n : ℕ∞) : WithTop ℕ∞) + 1) + 1 : WithTop ℕ∞) =
        (((n : ℕ∞) : WithTop ℕ∞) + 2 : WithTop ℕ∞) := by
      have h2 : ((2 : WithTop ℕ∞) = 1 + 1) := by decide
      rw [h2, ← add_assoc]
    rw [h_eq_wt]
    exact hf_C
  have h_augmentedVectorField_Cn_plus_1 : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augmentedVectorField_uncurry_contDiff (k := ((n : ℕ∞) + 1)) hf_Cn_plus_2_as_succ
  have ht₀_minus_tmin_a : 0 < t₀ - tmin_a := by linarith [ht₀_a_Ioo.1]
  have htmax_a_minus_t₀ : 0 < tmax_a - t₀ := by linarith [ht₀_a_Ioo.2]
  set T_a_out : ℝ := min (t₀ - tmin_a) (tmax_a - t₀) / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by
    rw [hT_a_out_def]; refine div_pos (lt_min ht₀_minus_tmin_a htmax_a_minus_t₀) (by norm_num)
  have hT_a_out_le_tmin_a_half : T_a_out ≤ (t₀ - tmin_a) / 2 := by
    rw [hT_a_out_def]
    have : min (t₀ - tmin_a) (tmax_a - t₀) ≤ t₀ - tmin_a := min_le_left _ _
    linarith
  have hT_a_out_le_tmax_a_half : T_a_out ≤ (tmax_a - t₀) / 2 := by
    rw [hT_a_out_def]
    have : min (t₀ - tmin_a) (tmax_a - t₀) ≤ tmax_a - t₀ := min_le_right _ _
    linarith
  have hsub_T_a_out_aug : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc tmin_a tmax_a :=
    Icc_subset_Icc (by linarith) (by linarith)
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := min R_a_mid (ρ_ih : ℝ) / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by
    rw [hR_a_def]; refine div_pos (lt_min hR_a_mid_pos _hρ_ih_pos) (by norm_num)
  have hR_a_lt_mid : R_a < R_a_mid := by
    rw [hR_a_def]
    have : min R_a_mid (ρ_ih : ℝ) ≤ R_a_mid := min_le_left _ _
    linarith
  have hR_a_le_ρ_ih : R_a ≤ (ρ_ih : ℝ) := by
    rw [hR_a_def]
    have : min R_a_mid (ρ_ih : ℝ) ≤ (ρ_ih : ℝ) := min_le_right _ _
    linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    change 0 < (R_aug : ℝ) / 8; linarith
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    change (R_aug : ℝ) / 2 * 3 / 4 + (R_aug : ℝ) / 8 ≤ (R_aug : ℝ)
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  set Slab_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
  have hSlab_a_compact : IsCompact Slab_a :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_a_ne : Slab_a.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have hslab_a_sub_full : Slab_a ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact hsub_T_a_out_aug
  have haΦ_cont : ContinuousOn aΦ Slab_a := haΦ.continuousOn.mono hslab_a_sub_full
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have h_augmentedVectorField_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField f))
        (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
      refine h_augmentedVectorField_Cn_plus_1.of_le ?_
      have h1 : (1 : ℕ∞) ≤ (n : ℕ∞) + 1 := le_add_self
      exact_mod_cast h1
    exact contDiffOn_partial_fderiv_of_succ (f := augmentedVectorField f) (k := (0 : ℕ∞))
      (by simpa using h_augmentedVectorField_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have h_pair_cont_a : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab_a :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_a_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augmentedVectorField f q.2) (aΦ q)) Slab_a := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab_a (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_pair_cont_a hmaps
  have h_norm_cont_a : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖) Slab_a := by
    have hnorm : Continuous
        (fun A : (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)) => ‖A‖) :=
      continuous_norm
    exact hnorm.comp_continuousOn h_fderiv_a_cont
  rcases hSlab_a_compact.exists_isMaxOn hSlab_a_ne h_norm_cont_a with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augmentedVectorField f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := norm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab_a, ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  set T_a_mid : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid_def
  have hT_a_mid_pos : 0 < T_a_mid := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid_lt_out : T_a_mid < T_a_out := by
    have h1 : T_a_mid ≤ T_a_out * 3 / 4 := min_le_left _ _
    linarith
  have hMTa_mid : M_aug * T_a_mid < 1 := by
    have h1 : T_a_mid ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  set T_a : ℝ := min T_a_mid T_ih / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by
    rw [hT_a_def]; refine div_pos (lt_min hT_a_mid_pos _hT_ih_pos) (by norm_num)
  have hT_a_lt_mid : T_a < T_a_mid := by
    rw [hT_a_def]
    have : min T_a_mid T_ih ≤ T_a_mid := min_le_left _ _
    linarith
  have hT_a_le_T_ih : T_a ≤ T_ih := by
    rw [hT_a_def]
    have h1 : min T_a_mid T_ih ≤ T_ih := min_le_right _ _
    linarith
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a := by
      refine ⟨?_, hτ⟩
      rw [hR_a_outN_eq] at hp; exact hp
    have h_pre : ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre :=
      hM_aug_pre_bd ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) hq_in
    rw [hM_aug_def]
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have hR_aN_le_ρ_ih : (R_aN : ℝ) ≤ (ρ_ih : ℝ) := by rw [hR_aN_eq]; exact hR_a_le_ρ_ih
  have h_shrink_sub : (ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)
      ⊆ (ball p₀ (ρ_ih : ℝ)) ×ˢ Ioo (t₀ - T_ih) (t₀ + T_ih) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hR_aN_le_ρ_ih
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  have hY_ih_shrunk : IsVariationalFlowProjection haΦ T_a R_aN Y_ih (n : ℕ∞) := by
    refine
    { contDiffOn := hY_ih.contDiffOn.mono h_shrink_sub,
      fderiv_eq := fun q hq => hY_ih.fderiv_eq q (h_shrink_sub hq) }
  have hk_pos : (1 : ℕ) ≤ n + 1 := by omega
  have hk_minus_one : ((n + 1 - 1 : ℕ) : ℕ∞) = (n : ℕ∞) := by
    have : n + 1 - 1 = n := by omega
    rw [this]
  have hY_ih_at_top : IsVariationalFlowProjection haΦ T_a R_aN Y_ih
      ((n + 1 - 1 : ℕ) : ℕ∞) := by rw [hk_minus_one]; exact hY_ih_shrunk
  have h_aug_Cn_plus_1 : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞) aΦ
      ((ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    refine contDiffOn_flow_of_isVariationalFlowProjection_top
      (f := augmentedVectorField f) (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := tmin_a)
        (tmax := tmax_a)
      (Φ := aΦ) haΦ hT_a_pos hT_a_lt_mid hT_a_mid_lt_out hM_aug_nn hMTa_mid hsub_T_a_out_aug
      (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN) hr'a_pos ?_ ?_ ?_ ?_ hA_bd_a
      (n + 1) hk_pos ?_ hY_ih_at_top
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
    · have h_eq_succ : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
          ((n : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [h_eq_succ]
      exact h_augmentedVectorField_Cn_plus_1
  have h_aug_Cn_plus_1' : ContDiffOn ℝ ((n : ℕ∞) + 1) aΦ
      ((ball p₀ (R_aN : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have h_eq_succ : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
        ((n : ℕ∞) : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [← h_eq_succ]
    exact h_aug_Cn_plus_1
  set U_E : Set (E × ℝ) := ball x₀ (R_aN : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_E_def
  set U_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    ball p₀ (R_aN : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_a_def
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U_E U_a := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    refine ⟨?_, hq_t⟩
    rw [mem_ball] at hq_x ⊢
    have hd : dist ((q.1, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) p₀
        = dist q.1 x₀ := by
      change max (dist q.1 x₀) (dist (ContinuousLinearMap.id ℝ E)
        (ContinuousLinearMap.id ℝ E)) = dist q.1 x₀
      rw [dist_self, max_eq_left dist_nonneg]
    rw [hd]; exact hq_x
  have h_Y_smooth : ContDiffOn ℝ ((n : ℕ∞) + 1) (fromAugmentedFlow aΦ) U_E :=
    contDiffOn_fromAugmentedFlow (k := ((n : ℕ∞) + 1)) (Ω := U_a) (U := U_E)
      h_aug_Cn_plus_1' hmap
  obtain ⟨T_help, ρ_help, hT_help_pos, hρ_help_pos, h_help⟩ :=
    exists_fderiv_eq_fromAugmentedFlow_coprod_timePieceFn
      (Φ := Φ) hΦ hf_C1 ht₀_Ioo hr_pos haΦ ht₀_a_Ioo hR_aug_pos
  set T_effective : ℝ := min T_a T_help with hT_effective_def
  have hT_effective_pos : 0 < T_effective := lt_min hT_a_pos hT_help_pos
  have hT_effective_le_T_a : T_effective ≤ T_a := min_le_left _ _
  have hT_effective_le_T_help : T_effective ≤ T_help := min_le_right _ _
  set ρ_effective : ℝ := min (R_aN : ℝ) (ρ_help : ℝ) with hρ_effective_def
  have hρ_effective_pos : 0 < ρ_effective := lt_min hR_a_pos hρ_help_pos
  set ρ_effectiveN : ℝ≥0 := ⟨ρ_effective, le_of_lt hρ_effective_pos⟩
  have hρ_effectiveN_eq : (ρ_effectiveN : ℝ) = ρ_effective := rfl
  have hρ_effective_le_R_a : ρ_effective ≤ (R_aN : ℝ) := min_le_left _ _
  have hρ_effective_le_help : ρ_effective ≤ (ρ_help : ℝ) := min_le_right _ _
  have hρ_effectiveN_le_R_a : (ρ_effectiveN : ℝ) ≤ (R_aN : ℝ) := by rw [hρ_effectiveN_eq]; exact hρ_effective_le_R_a
  have hρ_effectiveN_le_help : (ρ_effectiveN : ℝ) ≤ (ρ_help : ℝ) := by rw [hρ_effectiveN_eq]; exact hρ_effective_le_help
  have h_effective_sub_smooth : (ball x₀ (ρ_effectiveN : ℝ)) ×ˢ Ioo (t₀ - T_effective) (t₀ + T_effective) ⊆ U_E := by
    rw [hU_E_def]
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effectiveN_le_R_a
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  have h_effective_sub_help : (ball x₀ (ρ_effectiveN : ℝ)) ×ˢ Ioo (t₀ - T_effective) (t₀ + T_effective)
      ⊆ (ball x₀ (ρ_help : ℝ)) ×ˢ Ioo (t₀ - T_help) (t₀ + T_help) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effectiveN_le_help
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  refine ⟨T_effective, ρ_effectiveN, hT_effective_pos, hρ_effective_pos, fromAugmentedFlow aΦ, ?_⟩
  refine { contDiffOn := h_Y_smooth.mono h_effective_sub_smooth, fderiv_eq := ?_ }
  intro q hq
  exact h_help q (h_effective_sub_help hq)

end SuccStepWitness

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
