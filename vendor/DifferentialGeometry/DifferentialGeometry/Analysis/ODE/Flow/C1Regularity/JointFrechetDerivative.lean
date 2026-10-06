module

public import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.FrechetDerivative

@[expose] public section

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section MainTheorem

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}


theorem hasFDerivAt_flow_jointly_of_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hA_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩)‖ ≤ M)
    (hr : 0 < r)
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasFDerivAt Φ
      (((variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
            hT hM hMT
            ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x₀
              (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr)))).mono hsub)
            hA_bd (Ioo_subset_Icc_self ht))).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x₀, t⟩))))
      (x₀, t) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx₀_in_ball : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self (le_of_lt hr')
  set hA_cont :=
    (hΦ.continuousOn_fderiv_along_orbit hf_C1 x₀ hx₀_in_ball).mono hsub with hA_cont_def
  have ht_Icc : t ∈ Icc (t₀ - T) (t₀ + T) := Ioo_subset_Icc_self ht
  set Lmap := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd ht_Icc with hLmap_def
  have h_space :=
    hasFDerivAt_flow_at_initial_of_isLocalFlow hΦ hf_C1 hT hM hMT hsub hA_bd hr ht_Icc
  set Ltime : ℝ →L[ℝ] E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x₀, t⟩)) with hLtime_def
  set Ljoint : (E × ℝ) →L[ℝ] E := Lmap.coprod Ltime with hLjoint_def
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set c2 : ℝ := c / 2 with hc2_def
  have hc2_pos : 0 < c2 := by positivity
  have hf_cont_pt : ContinuousAt (uncurry f) (t, Φ ⟨x₀, t⟩) :=
    hf_C1.continuousOn.continuousAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
  rcases Metric.continuousAt_iff.mp hf_cont_pt c2 hc2_pos with ⟨η_f, hη_f_pos, hη_f⟩
  have hΦ_cont_pt : ContinuousWithinAt Φ
      (closedBall x₀ r ×ˢ Icc tmin tmax) (x₀, t) := by
    apply hΦ.continuousOn
    exact ⟨hx₀_in_ball, hsub ht_Icc⟩
  rw [Metric.continuousWithinAt_iff] at hΦ_cont_pt
  set η_half : ℝ := η_f / 2 with hη_half_def
  have hη_half_pos : 0 < η_half := by positivity
  have hη_half_lt : η_half < η_f := by linarith
  rcases hΦ_cont_pt η_half hη_half_pos with ⟨ρ₀, hρ₀_pos, hΦ_close⟩
  set ρ_t_raw : ℝ := min ((t - (t₀ - T)) / 2) (((t₀ + T) - t) / 2) with hρ_t_raw_def
  have hρ_t_raw_pos : 0 < ρ_t_raw := by
    refine lt_min ?_ ?_
    · have h : 0 < t - (t₀ - T) := by linarith [ht.1]
      linarith
    · have h : 0 < (t₀ + T) - t := by linarith [ht.2]
      linarith
  have h_t_minus_ρ_t_raw : t₀ - T ≤ t - ρ_t_raw := by
    have h1 : ρ_t_raw ≤ (t - (t₀ - T)) / 2 := min_le_left _ _
    linarith
  have h_t_plus_ρ_t_raw : t + ρ_t_raw ≤ t₀ + T := by
    have h1 : ρ_t_raw ≤ ((t₀ + T) - t) / 2 := min_le_right _ _
    linarith
  have h_space_io := (hasFDerivAt_iff_isLittleO_nhds_zero.mp h_space)
  rw [Asymptotics.isLittleO_iff] at h_space_io
  have h_space_c2 := h_space_io hc2_pos
  rcases Filter.eventually_iff_exists_mem.mp h_space_c2 with ⟨U_space, hU_space_mem, hU_space⟩
  rcases Metric.mem_nhds_iff.mp hU_space_mem with ⟨ρ_s, hρ_s_pos, hρ_s_sub⟩
  set ρ : ℝ := min (min ((r : ℝ)) ρ_s) (min (min ρ_t_raw ρ₀) η_half) with hρ_def
  have hρ_pos : 0 < ρ := by
    refine lt_min (lt_min hr' hρ_s_pos) (lt_min (lt_min hρ_t_raw_pos hρ₀_pos) hη_half_pos)
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : E × ℝ) ρ, Metric.ball_mem_nhds _ hρ_pos, fun p hp => ?_⟩
  rw [mem_ball_zero_iff] at hp
  rcases p with ⟨δ, s⟩
  have hp_norm : ‖(δ, s)‖ < ρ := hp
  rw [Prod.norm_def] at hp_norm
  have hδ_norm : ‖δ‖ < ρ := lt_of_le_of_lt (le_max_left _ _) hp_norm
  have hs_norm_real : ‖s‖ < ρ := lt_of_le_of_lt (le_max_right _ _) hp_norm
  have hs_abs : |s| < ρ := hs_norm_real
  have hδ_lt_r' : ‖δ‖ < (r : ℝ) :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_lt_ρ_s : ‖δ‖ < ρ_s :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hs_lt_ρ_t_raw : |s| < ρ_t_raw :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hδ_lt_ρ₀ : ‖δ‖ < ρ₀ :=
    lt_of_lt_of_le hδ_norm (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hs_lt_ρ₀ : |s| < ρ₀ :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hs_lt_η_half : |s| < η_half :=
    lt_of_lt_of_le hs_abs (le_trans (min_le_right _ _) (min_le_right _ _))
  have hx_in_ball : x₀ + δ ∈ closedBall x₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact le_of_lt hδ_lt_r'
  have h_ab_sub_T : Icc (t - ρ_t_raw) (t + ρ_t_raw) ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro u hu
    exact ⟨h_t_minus_ρ_t_raw.trans hu.1, hu.2.trans h_t_plus_ρ_t_raw⟩
  have h_ab_sub_tmin : Icc (t - ρ_t_raw) (t + ρ_t_raw) ⊆ Icc tmin tmax := h_ab_sub_T.trans hsub
  have hts_in_ab : t + s ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    refine ⟨?_, ?_⟩
    · have hs_ge : -(|s|) ≤ s := neg_abs_le _
      linarith [hs_lt_ρ_t_raw]
    · have hs_le : s ≤ |s| := le_abs_self _
      linarith [hs_lt_ρ_t_raw]
  have ht_in_ab : t ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    refine ⟨?_, ?_⟩ <;> linarith [hρ_t_raw_pos]
  set α : ℝ → E := fun u => Φ ⟨x₀ + δ, u⟩ with hα_def
  have hα_deriv : ∀ u ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw),
      HasDerivWithinAt α (f u (α u)) (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
    intro u hu
    have hu_tmin : u ∈ Icc tmin tmax := h_ab_sub_tmin hu
    exact (hΦ.hasDerivWithinAt (x₀ + δ) hx_in_ball u hu_tmin).mono h_ab_sub_tmin
  set v₀ : E := f t (Φ ⟨x₀, t⟩) with hv₀_def
  set g : ℝ → E := fun u => α u - (u - t) • v₀ with hg_def
  have hg_deriv : ∀ u ∈ Icc (t - ρ_t_raw) (t + ρ_t_raw),
      HasDerivWithinAt g (f u (α u) - v₀) (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
    intro u hu
    have hsubconst :
        HasDerivWithinAt (fun u : ℝ => (u - t) • v₀) v₀
          (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
      have h_lin : HasDerivWithinAt (fun u : ℝ => u - t) (1 : ℝ)
          (Icc (t - ρ_t_raw) (t + ρ_t_raw)) u := by
        have hid : HasDerivAt (fun u : ℝ => u - t) ((1 : ℝ) - 0) u :=
          (hasDerivAt_id' u).sub (hasDerivAt_const u t)
        rw [sub_zero] at hid
        exact hid.hasDerivWithinAt
      have hsmul := h_lin.smul_const v₀
      simpa using hsmul
    exact (hα_deriv u hu).sub hsubconst
  set u_lo : ℝ := min t (t + s) with hu_lo_def
  set u_hi : ℝ := max t (t + s) with hu_hi_def
  have hu_lo_le_t : u_lo ≤ t := min_le_left _ _
  have ht_le_u_hi : t ≤ u_hi := le_max_left _ _
  have hu_lo_le_ts : u_lo ≤ t + s := min_le_right _ _
  have hts_le_u_hi : t + s ≤ u_hi := le_max_right _ _
  have hu_lo_le_u_hi : u_lo ≤ u_hi := hu_lo_le_t.trans ht_le_u_hi
  have h_uloIcc : t - ρ_t_raw ≤ u_lo := by
    rw [hu_lo_def, le_min_iff]
    refine ⟨by linarith [hρ_t_raw_pos], ?_⟩
    have hs_ge : -(|s|) ≤ s := neg_abs_le _
    linarith [hs_lt_ρ_t_raw]
  have h_uhiIcc : u_hi ≤ t + ρ_t_raw := by
    rw [hu_hi_def, max_le_iff]
    refine ⟨by linarith [hρ_t_raw_pos], ?_⟩
    have hs_le : s ≤ |s| := le_abs_self _
    linarith [hs_lt_ρ_t_raw]
  have hseg_sub : Icc u_lo u_hi ⊆ Icc (t - ρ_t_raw) (t + ρ_t_raw) := by
    intro u hu
    exact ⟨h_uloIcc.trans hu.1, hu.2.trans h_uhiIcc⟩
  have h_segment_dist : ∀ u ∈ Icc u_lo u_hi, |u - t| ≤ |s| := by
    intro u hu
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      rw [hlo, hhi] at hu
      have h1 : t ≤ u := hu.1
      have h2 : u ≤ t + s := hu.2
      have h3 : 0 ≤ u - t := by linarith
      have h4 : u - t ≤ s := by linarith
      rw [abs_of_nonneg h3]
      have habs_s : |s| = s := abs_of_nonneg hs_nn
      rw [habs_s]; exact h4
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      rw [hlo, hhi] at hu
      have h1 : t + s ≤ u := hu.1
      have h2 : u ≤ t := hu.2
      have h3 : u - t ≤ 0 := by linarith
      have h4 : -(u - t) ≤ -s := by linarith
      rw [abs_of_nonpos h3]
      have habs_s : |s| = -s := abs_of_neg hs_neg
      rw [habs_s]; exact h4
  have hpair_dist_segment : ∀ u ∈ Icc u_lo u_hi,
      dist ((x₀ + δ, u) : E × ℝ) (x₀, t) < ρ₀ := by
    intro u hu
    rw [Prod.dist_eq]
    have h1 : dist (x₀ + δ) x₀ = ‖δ‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    have h2 : dist u t = |u - t| := Real.dist_eq u t
    rw [h1, h2]
    have h3 : ‖δ‖ < ρ₀ := hδ_lt_ρ₀
    have h4 : |u - t| < ρ₀ := lt_of_le_of_lt (h_segment_dist u hu) hs_lt_ρ₀
    exact max_lt h3 h4
  have hΦ_segment : ∀ u ∈ Icc u_lo u_hi,
      dist (α u) (Φ ⟨x₀, t⟩) < η_half := by
    intro u hu
    have hpair_in : (x₀ + δ, u) ∈ closedBall x₀ r ×ˢ Icc tmin tmax := by
      refine ⟨hx_in_ball, ?_⟩
      exact h_ab_sub_tmin (hseg_sub hu)
    exact hΦ_close hpair_in (hpair_dist_segment u hu)
  have hpair_dist_f : ∀ u ∈ Icc u_lo u_hi,
      dist ((u, α u) : ℝ × E) (t, Φ ⟨x₀, t⟩) < η_f := by
    intro u hu
    rw [Prod.dist_eq]
    have h1 : dist u t = |u - t| := Real.dist_eq u t
    rw [h1]
    have hu_t : |u - t| < η_half := by
      have h_le : |u - t| ≤ |s| := h_segment_dist u hu
      exact lt_of_le_of_lt h_le hs_lt_η_half
    have h2 : dist (α u) (Φ ⟨x₀, t⟩) < η_half := hΦ_segment u hu
    have h3 : max (|u - t|) (dist (α u) (Φ ⟨x₀, t⟩)) < η_half := max_lt hu_t h2
    exact lt_trans h3 hη_half_lt
  have hf_close_segment : ∀ u ∈ Icc u_lo u_hi, ‖f u (α u) - v₀‖ ≤ c2 := by
    intro u hu
    have hd := hpair_dist_f u hu
    have h := hη_f hd
    rw [dist_eq_norm] at h
    change ‖f u (α u) - v₀‖ ≤ c2
    exact le_of_lt h
  have hg_deriv_segment : ∀ u ∈ Icc u_lo u_hi,
      HasDerivWithinAt g (f u (α u) - v₀) (Icc u_lo u_hi) u := fun u hu =>
    (hg_deriv u (hseg_sub hu)).mono hseg_sub
  have hf_segment_bound : ∀ u ∈ Ico u_lo u_hi, ‖f u (α u) - v₀‖ ≤ c2 := fun u hu =>
    hf_close_segment u ⟨hu.1, le_of_lt hu.2⟩
  have h_mvt :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
      (f' := fun u => f u (α u) - v₀) (C := c2) (a := u_lo) (b := u_hi)
      hg_deriv_segment hf_segment_bound u_hi (right_mem_Icc.mpr hu_lo_le_u_hi)
  have h_u_diff : u_hi - u_lo = |s| := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      rw [hlo, hhi]
      rw [abs_of_nonneg hs_nn]; ring
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      rw [hlo, hhi]
      rw [abs_of_neg hs_neg]; ring
  have h_time_residual : ‖α (t + s) - α t - s • v₀‖ ≤ c2 * |s| := by
    rcases le_or_gt 0 s with hs_nn | hs_neg
    · have hlo : u_lo = t := min_eq_left (by linarith)
      have hhi : u_hi = t + s := max_eq_right (by linarith)
      have h_mvt' : ‖g (t + s) - g t‖ ≤ c2 * (t + s - t) := by
        have := h_mvt
        rw [hlo, hhi] at this
        exact this
      have h_diff_eq : g (t + s) - g t = α (t + s) - α t - s • v₀ := by
        change (α (t + s) - (t + s - t) • v₀) - (α t - (t - t) • v₀)
            = α (t + s) - α t - s • v₀
        have h1 : t + s - t = s := by ring
        have h2 : t - t = (0 : ℝ) := by ring
        rw [h1, h2]; simp; abel
      rw [h_diff_eq] at h_mvt'
      have hs_eq : t + s - t = s := by ring
      rw [hs_eq] at h_mvt'
      rw [abs_of_nonneg hs_nn]; exact h_mvt'
    · have hlo : u_lo = t + s := min_eq_right (by linarith)
      have hhi : u_hi = t := max_eq_left (by linarith)
      have h_mvt' : ‖g t - g (t + s)‖ ≤ c2 * (t - (t + s)) := by
        have := h_mvt
        rw [hlo, hhi] at this
        exact this
      have h_diff_eq : g t - g (t + s) = -(α (t + s) - α t - s • v₀) := by
        change (α t - (t - t) • v₀) - (α (t + s) - (t + s - t) • v₀)
            = -(α (t + s) - α t - s • v₀)
        have h1 : t - t = (0 : ℝ) := by ring
        have h2 : t + s - t = s := by ring
        rw [h1, h2]
        simp
        abel
      rw [h_diff_eq, norm_neg] at h_mvt'
      have hs_eq : t - (t + s) = -s := by ring
      rw [hs_eq] at h_mvt'
      rw [abs_of_neg hs_neg]; exact h_mvt'
  have h_space_piece : ‖Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ‖ ≤ c2 * ‖δ‖ := by
    have hδ_in_U : δ ∈ U_space :=
      hρ_s_sub (by rw [mem_ball_zero_iff]; exact hδ_lt_ρ_s)
    have h := hU_space δ hδ_in_U
    exact h
  have h_total :
      ‖Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀‖
        ≤ c2 * ‖δ‖ + c2 * |s| := by
    have h_decomp :
        Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀
          = (α (t + s) - α t - s • v₀) + (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ) := by
      change Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀
          = (Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀ + δ, t⟩ - s • v₀)
            + (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ)
      abel
    rw [h_decomp]
    have hnorm := norm_add_le (α (t + s) - α t - s • v₀)
      (Φ ⟨x₀ + δ, t⟩ - Φ ⟨x₀, t⟩ - Lmap δ)
    have h_sum_le : c2 * |s| + c2 * ‖δ‖ ≤ c2 * ‖δ‖ + c2 * |s| := by linarith
    linarith [hnorm, h_time_residual, h_space_piece]
  have h_norm_pair : ‖(δ, s)‖ = max ‖δ‖ |s| := by
    rw [Prod.norm_def]
    rfl
  have h_δ_le : ‖δ‖ ≤ ‖(δ, s)‖ := by rw [h_norm_pair]; exact le_max_left _ _
  have h_s_le : |s| ≤ ‖(δ, s)‖ := by rw [h_norm_pair]; exact le_max_right _ _
  have h_final : c2 * ‖δ‖ + c2 * |s| ≤ c * ‖(δ, s)‖ := by
    have hsum : c2 * ‖δ‖ + c2 * |s| ≤ c2 * ‖(δ, s)‖ + c2 * ‖(δ, s)‖ := by
      have h1 : c2 * ‖δ‖ ≤ c2 * ‖(δ, s)‖ :=
        mul_le_mul_of_nonneg_left h_δ_le (le_of_lt hc2_pos)
      have h2 : c2 * |s| ≤ c2 * ‖(δ, s)‖ :=
        mul_le_mul_of_nonneg_left h_s_le (le_of_lt hc2_pos)
      linarith
    have hkey : c2 * ‖(δ, s)‖ + c2 * ‖(δ, s)‖ = c * ‖(δ, s)‖ := by
      rw [hc2_def]; ring
    linarith
  have h_Ljoint : Ljoint (δ, s) = Lmap δ + s • v₀ := by
    rw [hLjoint_def, hLtime_def]
    simp [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
  have h_goal_eq :
      Φ ((x₀, t) + (δ, s)) - Φ (x₀, t) - Ljoint (δ, s)
        = Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - Lmap δ - s • v₀ := by
    rw [h_Ljoint]
    change Φ ⟨x₀ + δ, t + s⟩ - Φ ⟨x₀, t⟩ - (Lmap δ + s • v₀) = _
    abel
  rw [h_goal_eq]
  exact le_trans h_total h_final

end MainTheorem

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
