module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.SuccessorExistence

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

section LevelZeroWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_isVariationalFlowProjection_zero_of_C1
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y (0 : ℕ∞) := by
  classical
  set CE : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) ≃L[ℝ] ((E × ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := E) (F := ℝ) (G := E) ℝ
    with hCE_def
  have ht₀_minus_tmin : 0 < t₀ - tmin := by linarith [ht₀_Ioo.1]
  have htmax_minus_t₀ : 0 < tmax - t₀ := by linarith [ht₀_Ioo.2]
  set T_outer : ℝ := min (t₀ - tmin) (tmax - t₀) / 2 with hT_outer_def
  have hT_outer_pos : 0 < T_outer := by
    rw [hT_outer_def]
    exact div_pos (lt_min ht₀_minus_tmin htmax_minus_t₀) (by norm_num)
  have hT_outer_le_tmin_half : T_outer ≤ (t₀ - tmin) / 2 := by
    rw [hT_outer_def]
    have h1 : min (t₀ - tmin) (tmax - t₀) ≤ t₀ - tmin := min_le_left _ _
    linarith
  have hT_outer_le_tmax_half : T_outer ≤ (tmax - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (t₀ - tmin) (tmax - t₀) ≤ tmax - t₀ := min_le_right _ _
    linarith
  have hsub_outer_orig : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin tmax :=
    Icc_subset_Icc (by linarith) (by linarith)
  set ρ_outer : ℝ := (r : ℝ) / 2 with hρ_outer_def
  have hρ_outer_pos : 0 < ρ_outer := by rw [hρ_outer_def]; linarith
  have hρ_outer_le_r : ρ_outer ≤ (r : ℝ) := by rw [hρ_outer_def]; linarith
  set ρ_outerN : ℝ≥0 := ⟨ρ_outer, le_of_lt hρ_outer_pos⟩ with hρ_outerN_def
  have hρ_outerN_eq : (ρ_outerN : ℝ) = ρ_outer := rfl
  set Slab_Φ_outer : Set (E × ℝ) :=
    closedBall x₀ ρ_outer ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_Φ_outer_def
  have hSlab_Φ_outer_compact : IsCompact Slab_Φ_outer :=
    (isCompact_closedBall x₀ ρ_outer).prod isCompact_Icc
  have hSlab_Φ_outer_ne : Slab_Φ_outer.Nonempty :=
    ⟨(x₀, t₀), Metric.mem_closedBall_self (le_of_lt hρ_outer_pos),
      ⟨by linarith, by linarith⟩⟩
  have hSlab_Φ_outer_sub_orig : Slab_Φ_outer ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    exact Set.prod_mono (closedBall_subset_closedBall hρ_outer_le_r) hsub_outer_orig
  have hΦ_cont_slab : ContinuousOn Φ Slab_Φ_outer :=
    hΦ.continuousOn.mono hSlab_Φ_outer_sub_orig
  have h_Φ_norm_cont : ContinuousOn (fun p : E × ℝ => ‖Φ p - x₀‖) Slab_Φ_outer := by
    have h_sub_cont : ContinuousOn (fun p : E × ℝ => Φ p - x₀) Slab_Φ_outer :=
      hΦ_cont_slab.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_Φ_outer_compact.exists_isMaxOn hSlab_Φ_outer_ne h_Φ_norm_cont
    with ⟨pmax_R, _, hpmax_R⟩
  set R_Φ_image_pre : ℝ := ‖Φ pmax_R - x₀‖ with hR_Φ_image_pre_def
  have hR_Φ_image_pre_nn : 0 ≤ R_Φ_image_pre := norm_nonneg _
  have hR_Φ_image_pre_bd : ∀ p ∈ Slab_Φ_outer, ‖Φ p - x₀‖ ≤ R_Φ_image_pre :=
    fun p hp => hpmax_R hp
  set r₀_lip : ℝ := R_Φ_image_pre + 1 with hr₀_lip_def
  have hr₀_lip_pos : 0 < r₀_lip := by rw [hr₀_lip_def]; linarith
  have hr₀_lip_ge_Φ : R_Φ_image_pre ≤ r₀_lip := by rw [hr₀_lip_def]; linarith
  set Slab_f : Set (ℝ × E) :=
    Icc (t₀ - T_outer) (t₀ + T_outer) ×ˢ closedBall x₀ r₀_lip with hSlab_f_def
  have hSlab_f_compact : IsCompact Slab_f :=
    isCompact_Icc.prod (isCompact_closedBall x₀ r₀_lip)
  have hSlab_f_ne : Slab_f.Nonempty :=
    ⟨(t₀, x₀), ⟨by linarith, by linarith⟩, Metric.mem_closedBall_self (le_of_lt hr₀_lip_pos)⟩
  have hpartial_f : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ (f := f) (k := (0 : ℕ∞))
      (by simpa using hf_C1)
  have hpartial_f_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Slab_f :=
    hpartial_f.continuousOn.mono (subset_univ _)
  have hpartial_f_norm_cont : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖) Slab_f :=
    continuous_norm.comp_continuousOn hpartial_f_cont
  rcases hSlab_f_compact.exists_isMaxOn hSlab_f_ne hpartial_f_norm_cont
    with ⟨pmax_K, _, hpmax_K⟩
  set K_pre : ℝ := ‖fderiv ℝ (f pmax_K.1) pmax_K.2‖ with hK_pre_def
  have hK_pre_nn : 0 ≤ K_pre := norm_nonneg _
  have hK_pre_bd : ∀ p ∈ Slab_f, ‖fderiv ℝ (f p.1) p.2‖ ≤ K_pre := fun p hp => hpmax_K hp
  set K_orig : ℝ := K_pre + 1 with hK_orig_def
  have hK_orig_pos : 0 < K_orig := by rw [hK_orig_def]; linarith
  have hK_orig_nn : 0 ≤ K_orig := le_of_lt hK_orig_pos
  set T_mid : ℝ := min (T_outer * 3 / 4) (1 / (2 * K_orig)) with hT_mid_def
  have hT_mid_pos : 0 < T_mid := by
    have hleft : 0 < T_outer * 3 / 4 := by positivity
    have hright : 0 < 1 / (2 * K_orig) := by positivity
    exact lt_min hleft hright
  have hT_mid_lt_outer : T_mid < T_outer := by
    have h1 : T_mid ≤ T_outer * 3 / 4 := min_le_left _ _
    linarith
  have hKT_mid : K_orig * T_mid < 1 := by
    have h1 : T_mid ≤ 1 / (2 * K_orig) := min_le_right _ _
    have h2 : K_orig * T_mid ≤ K_orig * (1 / (2 * K_orig)) :=
      mul_le_mul_of_nonneg_left h1 hK_orig_nn
    have h3 : K_orig * (1 / (2 * K_orig)) = 1 / 2 := by field_simp
    linarith
  set T_final : ℝ := T_mid / 2 with hT_final_def
  have hT_final_pos : 0 < T_final := by rw [hT_final_def]; linarith
  have hT_final_lt_mid : T_final < T_mid := by rw [hT_final_def]; linarith
  set ρ_mid : ℝ := ρ_outer * 3 / 4 with hρ_mid_def
  have hρ_mid_pos : 0 < ρ_mid := by rw [hρ_mid_def]; positivity
  have hρ_mid_lt_outer : ρ_mid < ρ_outer := by rw [hρ_mid_def]; linarith
  set ρ_inner : ℝ := ρ_outer / 2 with hρ_inner_def
  have hρ_inner_pos : 0 < ρ_inner := by rw [hρ_inner_def]; linarith
  have hρ_inner_lt_mid : ρ_inner < ρ_mid := by
    rw [hρ_inner_def, hρ_mid_def]; linarith
  set ρ_innerN : ℝ≥0 := ⟨ρ_inner, le_of_lt hρ_inner_pos⟩
  set ρ_midN : ℝ≥0 := ⟨ρ_mid, le_of_lt hρ_mid_pos⟩
  have hρ_innerN_eq : (ρ_innerN : ℝ) = ρ_inner := rfl
  have hρ_midN_eq : (ρ_midN : ℝ) = ρ_mid := rfl
  have hρ_outerN_le_r : (ρ_outerN : ℝ) ≤ (r : ℝ) := by
    rw [hρ_outerN_eq]; exact hρ_outer_le_r
  have hρ_innerN_lt_midN : (ρ_innerN : ℝ) < (ρ_midN : ℝ) := by
    rw [hρ_innerN_eq, hρ_midN_eq]; exact hρ_inner_lt_mid
  have hρ_midN_lt_outerN : (ρ_midN : ℝ) < (ρ_outerN : ℝ) := by
    rw [hρ_midN_eq, hρ_outerN_eq]; exact hρ_mid_lt_outer
  set r'_φ : ℝ≥0 := ⟨ρ_outer / 2, by positivity⟩
  have hr'_φ_pos : (0 : ℝ) < (r'_φ : ℝ) := by
    change 0 < ρ_outer / 2
    linarith
  have hρρ'_φ_outer : (ρ_outerN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    rw [hρ_outerN_eq]
    change ρ_outer + ρ_outer / 2 ≤ (r : ℝ)
    have h_eq : ρ_outer + ρ_outer / 2 = ρ_outer * 3 / 2 := by ring
    rw [h_eq, hρ_outer_def]
    linarith
  have hρρ'_φ : (ρ_midN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    have h1 : (ρ_midN : ℝ) + (r'_φ : ℝ) ≤ (ρ_outerN : ℝ) + (r'_φ : ℝ) := by
      linarith [hρ_midN_lt_outerN]
    linarith [hρρ'_φ_outer]
  have hA_bd_outer : ∀ x ∈ closedBall x₀ (ρ_outerN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ K_orig := by
    intro x hx τ hτ
    have hx_closed_ρ_outer : x ∈ closedBall x₀ ρ_outer := by
      change dist x x₀ ≤ ρ_outer
      rw [mem_closedBall] at hx
      exact hx
    have h_pair_in_outer : ((x, τ) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hτ⟩
    have h_orbit_in_r₀ : Φ ⟨x, τ⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (x, τ) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((τ, Φ ⟨x, τ⟩) : ℝ × E) ∈ Slab_f := ⟨hτ, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ K_pre :=
      hK_pre_bd ((τ, Φ ⟨x, τ⟩) : ℝ × E) h_pair_in_f
    linarith
  have h_fderiv_cont : ContinuousOn (fderiv ℝ Φ)
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
    continuousOn_fderiv_flow_of_isLocalFlow hΦ hf_C1
      hT_final_pos hT_final_lt_mid hT_mid_lt_outer hK_orig_nn hKT_mid hsub_outer_orig
      hr'_φ_pos hρ_innerN_lt_midN hρ_midN_lt_outerN hρρ'_φ hρ_outerN_le_r hA_bd_outer
  set Y : E × ℝ → (E →L[ℝ] E) := fun q => (CE.symm (fderiv ℝ Φ q)).1 with hY_def
  have hY_cont : ContinuousOn Y
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) := by
    have h1 : ContinuousOn (fun q => CE.symm (fderiv ℝ Φ q))
        ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
      CE.symm.continuous.comp_continuousOn h_fderiv_cont
    exact continuous_fst.comp_continuousOn h1
  have hY_C0 : ContDiffOn ℝ 0 Y
      ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)) :=
    contDiffOn_zero.mpr hY_cont
  have h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ_innerN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final)),
      fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q) := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    obtain ⟨x, t⟩ := q
    rw [mem_ball] at hq_x
    have hx_cb_inner : x ∈ closedBall x₀ (ρ_innerN : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
    have hx_cb_mid : x ∈ closedBall x₀ (ρ_midN : ℝ) :=
      closedBall_subset_closedBall (le_of_lt hρ_innerN_lt_midN) hx_cb_inner
    have hx_cb_outer : x ∈ closedBall x₀ (ρ_outerN : ℝ) :=
      closedBall_subset_closedBall (le_of_lt hρ_midN_lt_outerN) hx_cb_mid
    have ht_Ioo_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := by
      exact ⟨by linarith [hq_t.1, hT_final_lt_mid],
        by linarith [hq_t.2, hT_final_lt_mid]⟩
    have hsub_mid_orig : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := by
      have hsub_mid_outer : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_outer) (t₀ + T_outer) :=
        Icc_subset_Icc (by linarith) (by linarith)
      exact hsub_mid_outer.trans hsub_outer_orig
    have hA_bd_mid : ∀ y ∈ closedBall x₀ (ρ_outerN : ℝ),
        ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
          ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_orig := by
      intro y hy τ hτ
      have hτ_outer : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := by
        exact ⟨by linarith [hτ.1, hT_mid_lt_outer],
          by linarith [hτ.2, hT_mid_lt_outer]⟩
      exact hA_bd_outer y hy τ hτ_outer
    have h_fd := hasFDerivAt_flow_jointly_at (ρ := ρ_outerN) hΦ hf_C1
      hT_mid_pos hK_orig_nn hKT_mid hsub_mid_orig hr'_φ_pos hρρ'_φ_outer hA_bd_mid
      hx_cb_outer ht_Ioo_mid
    have hfd_eq : fderiv ℝ Φ (x, t) =
        (variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
            hT_mid_pos hK_orig_nn hKT_mid
            (((((hΦ.restrict_center_of_norm_le
                (x₁ := x) (r' := r'_φ) (by
                  rw [mem_closedBall] at hx_cb_outer
                  have hx_le : dist x x₀ ≤ (ρ_outerN : ℝ) := hx_cb_outer
                  linarith))).continuousOn_fderiv_along_orbit hf_C1 x
              (Metric.mem_closedBall_self
                (by exact_mod_cast (le_of_lt hr'_φ_pos))))).mono hsub_mid_orig)
            (fun τ hτ => hA_bd_mid x hx_cb_outer τ hτ)
            (Ioo_subset_Icc_self ht_Ioo_mid)).coprod
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))) := h_fd.fderiv
    have h_timePiece_eq : (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
        = timePieceFn f Φ (x, t) := rfl
    set Lmap : E →L[ℝ] E :=
      variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
        hT_mid_pos hK_orig_nn hKT_mid
        (((((hΦ.restrict_center_of_norm_le
            (x₁ := x) (r' := r'_φ) (by
              rw [mem_closedBall] at hx_cb_outer
              have hx_le : dist x x₀ ≤ (ρ_outerN : ℝ) := hx_cb_outer
              linarith))).continuousOn_fderiv_along_orbit hf_C1 x
          (Metric.mem_closedBall_self
            (by exact_mod_cast (le_of_lt hr'_φ_pos))))).mono hsub_mid_orig)
        (fun τ hτ => hA_bd_mid x hx_cb_outer τ hτ)
        (Ioo_subset_Icc_self ht_Ioo_mid) with hLmap_def
    set Lti : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
      with hLti_def
    have hfd_eq' : fderiv ℝ Φ (x, t) = Lmap.coprod Lti := hfd_eq
    have hCE_apply : CE (Lmap, Lti) = Lmap.coprod Lti := rfl
    have hCE_inv : CE.symm (Lmap.coprod Lti) = (Lmap, Lti) := by
      rw [← hCE_apply]
      exact CE.symm_apply_apply (Lmap, Lti)
    have hY_eq : Y (x, t) = Lmap := by
      change (CE.symm (fderiv ℝ Φ (x, t))).1 = Lmap
      rw [hfd_eq', hCE_inv]
    rw [hfd_eq', hY_eq, ← h_timePiece_eq]
  exact ⟨T_final, ρ_innerN, hT_final_pos, hρ_inner_pos, Y,
    { contDiffOn := hY_C0, fderiv_eq := h_fderiv_eq }⟩

end LevelZeroWitness

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
