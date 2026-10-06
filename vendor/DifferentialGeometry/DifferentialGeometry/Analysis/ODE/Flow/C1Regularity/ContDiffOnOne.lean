module

public import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.JointFrechetDerivative

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace IsLocalFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
lemma restrict_center
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {x₁ : E} {r' : ℝ≥0}
    (hsub : closedBall x₁ (r' : ℝ) ⊆ closedBall x₀ (r : ℝ)) :
    IsLocalFlow f t₀ x₁ r' tmin tmax Φ where
  minTime_le_initial := hΦ.minTime_le_initial
  initial_le_maxTime := hΦ.initial_le_maxTime
  apply_initial := fun x hx => hΦ.apply_initial x (hsub hx)
  hasDerivWithinAt := fun x hx t ht => hΦ.hasDerivWithinAt x (hsub hx) t ht
  continuousOn := hΦ.continuousOn.mono (fun p hp => ⟨hsub hp.1, hp.2⟩)
  exists_lipschitz := by
    obtain ⟨L, hL⟩ := hΦ.exists_lipschitz
    exact ⟨L, fun t ht => (hL t ht).mono hsub⟩

omit [CompleteSpace E] in
lemma restrict_center_of_norm_le
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {x₁ : E} {r' : ℝ≥0}
    (hd : dist x₁ x₀ + (r' : ℝ) ≤ (r : ℝ)) :
    IsLocalFlow f t₀ x₁ r' tmin tmax Φ := by
  apply hΦ.restrict_center
  intro y hy
  rw [mem_closedBall] at hy ⊢
  have := dist_triangle y x₁ x₀
  linarith

end IsLocalFlow

section JointPointwise

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem hasFDerivAt_flow_jointly_at
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasFDerivAt Φ
      (((variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
            hT hM hMT
            (((((hΦ.restrict_center_of_norm_le
                (x₁ := x) (r' := r') (by
                  rw [mem_closedBall] at hx
                  linarith))).continuousOn_fderiv_along_orbit hf_C1 x
              (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr'))))).mono hsub)
            (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht))).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))))
      (x, t) := by
  have hΦ' := hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
    rw [mem_closedBall] at hx
    have hx_le : dist x x₀ ≤ (ρ : ℝ) := hx
    linarith)
  exact hasFDerivAt_flow_jointly_of_isLocalFlow hΦ' hf_C1 hT hM hMT hsub
    (fun τ hτ => hA_bd x hx τ hτ) hr' ht

end JointPointwise

section GronwallCompare

variable {f : ℝ → E → E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem variationalSolution_compare_norm
    {α₁ α₂ : ℝ → E} {T M ε : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA₂_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₂ τ)‖ ≤ M)
    (hA₁_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₁ τ)‖ ≤ M)
    (hA_diff : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (α₁ τ) - fderiv ℝ (f τ) (α₂ τ)‖ ≤ ε)
    {δ : E} {y₁ y₂ : ℝ → E}
    (h₁ : IsVariationalSolutionOn f α₁ δ t₀ y₁ (Icc (t₀ - T) (t₀ + T)))
    (h₂ : IsVariationalSolutionOn f α₂ δ t₀ y₂ (Icc (t₀ - T) (t₀ + T))) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖y₁ t - y₂ t‖ ≤ ε * ‖δ‖ * exp (M * T) * T * exp (M * T) := by
  intro t ht
  set A₁ : ℝ → E →L[ℝ] E := fun τ => fderiv ℝ (f τ) (α₁ τ)
  set A₂ : ℝ → E →L[ℝ] E := fun τ => fderiv ℝ (f τ) (α₂ τ)
  have hy₁_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖y₁ τ‖ ≤ ‖δ‖ * exp (M * T) :=
    IsVariationalSolutionOn.norm_le_exp_of_mem_Icc (le_of_lt hT) hM h₁ hA₁_bd
  set w : ℝ → E := fun τ => y₁ τ - y₂ τ
  have hbound_aux : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖A₁ τ (y₁ τ) - A₂ τ (y₂ τ)‖ ≤ M * ‖w τ‖ + ε * (‖δ‖ * exp (M * T)) := by
    intro τ hτ
    have hsplit : A₁ τ (y₁ τ) - A₂ τ (y₂ τ)
        = A₂ τ (y₁ τ - y₂ τ) + (A₁ τ - A₂ τ) (y₁ τ) := by
      rw [sub_apply, ContinuousLinearMap.map_sub]
      abel
    rw [hsplit]
    have h_nrm := norm_add_le (A₂ τ (y₁ τ - y₂ τ)) ((A₁ τ - A₂ τ) (y₁ τ))
    have h_A₂ : ‖A₂ τ (y₁ τ - y₂ τ)‖ ≤ M * ‖w τ‖ := by
      calc ‖A₂ τ (y₁ τ - y₂ τ)‖ ≤ ‖A₂ τ‖ * ‖y₁ τ - y₂ τ‖ := (A₂ τ).le_opNorm _
        _ ≤ M * ‖y₁ τ - y₂ τ‖ := by have := hA₂_bd τ hτ; gcongr
        _ = M * ‖w τ‖ := rfl
    have h_diff : ‖(A₁ τ - A₂ τ) (y₁ τ)‖ ≤ ε * (‖δ‖ * exp (M * T)) := by
      calc ‖(A₁ τ - A₂ τ) (y₁ τ)‖ ≤ ‖A₁ τ - A₂ τ‖ * ‖y₁ τ‖ := (A₁ τ - A₂ τ).le_opNorm _
        _ ≤ ε * (‖δ‖ * exp (M * T)) := by
            have h1 := hA_diff τ hτ
            have h2 := hy₁_bd τ hτ
            exact mul_le_mul h1 h2 (norm_nonneg _) hε
    linarith
  have heps_nn : 0 ≤ ε * (‖δ‖ * exp (M * T)) :=
    mul_nonneg hε (mul_nonneg (norm_nonneg _) (le_of_lt (exp_pos _)))
  have hreduce : ∀ {s : ℝ}, 0 ≤ s → s ≤ T → s * exp (M * s) ≤ T * exp (M * T) := by
    intro s hs₀ hsT
    have hexp_le : exp (M * s) ≤ exp (M * T) := by
      apply exp_le_exp.mpr; nlinarith
    calc s * exp (M * s) ≤ T * exp (M * s) := by
          apply mul_le_mul_of_nonneg_right hsT (le_of_lt (exp_pos _))
      _ ≤ T * exp (M * T) := by
          apply mul_le_mul_of_nonneg_left hexp_le (le_of_lt hT)
  have hreduce_full : ∀ {s : ℝ}, 0 ≤ s → s ≤ T →
      gronwallBound 0 M (ε * (‖δ‖ * exp (M * T))) s
        ≤ ε * ‖δ‖ * exp (M * T) * T * exp (M * T) := by
    intro s hs₀ hsT
    rcases lt_or_eq_of_le hM with hM_pos | hM_zero
    · have hgb := gronwallBound_zero_le hM_pos heps_nn hs₀
      have hred := hreduce hs₀ hsT
      have hbase_nn : 0 ≤ ε * (‖δ‖ * exp (M * T)) := heps_nn
      have hbd : ε * (‖δ‖ * exp (M * T)) * s * exp (M * s)
          = ε * (‖δ‖ * exp (M * T)) * (s * exp (M * s)) := by ring
      have hbd2 : ε * (‖δ‖ * exp (M * T)) * (s * exp (M * s))
          ≤ ε * (‖δ‖ * exp (M * T)) * (T * exp (M * T)) :=
        mul_le_mul_of_nonneg_left hred hbase_nn
      have hfinal : ε * (‖δ‖ * exp (M * T)) * (T * exp (M * T))
          = ε * ‖δ‖ * exp (M * T) * T * exp (M * T) := by ring
      linarith
    · have hM_eq : M = 0 := hM_zero.symm
      subst hM_eq
      have hgb : gronwallBound 0 0 (ε * (‖δ‖ * exp (0 * T))) s
          = ε * (‖δ‖ * exp (0 * T)) * s := by
        rw [gronwallBound_K0]; simp
      rw [hgb]
      have hexp0 : exp (0 * T) = 1 := by rw [zero_mul, exp_zero]
      rw [hexp0, mul_one]
      have hgoal : ε * ‖δ‖ * exp (0 * T) * T * exp (0 * T) = ε * ‖δ‖ * T := by
        rw [hexp0]; ring
      have h1 : ε * ‖δ‖ * s ≤ ε * ‖δ‖ * T :=
        mul_le_mul_of_nonneg_left hsT (mul_nonneg hε (norm_nonneg _))
      linarith
  rcases le_or_gt t₀ t with htge | htlt
  · have hsub_R : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_left (by linarith)
    have hw_cont : ContinuousOn w (Icc t₀ (t₀ + T)) :=
      (h₁.continuousOn.sub h₂.continuousOn).mono hsub_R
    have hw_d : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt w (A₁ τ (y₁ τ) - A₂ τ (y₂ τ)) (Ici τ) τ := by
      intro τ hτ
      have hτ_in : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτ.1, le_of_lt hτ.2⟩
      have hτ_Ico : τ ∈ Ico (t₀ - T) (t₀ + T) := ⟨hτ_in.1, hτ.2⟩
      have hd₁ : HasDerivWithinAt y₁ (A₁ τ (y₁ τ)) (Ici τ) τ :=
        hasDerivWithinAt_Ici_of_Icc (h₁.2 τ hτ_in) hτ_Ico
      have hd₂ : HasDerivWithinAt y₂ (A₂ τ (y₂ τ)) (Ici τ) τ :=
        hasDerivWithinAt_Ici_of_Icc (h₂.2 τ hτ_in) hτ_Ico
      exact hd₁.sub hd₂
    have hbound_R : ∀ τ ∈ Ico t₀ (t₀ + T),
        ‖A₁ τ (y₁ τ) - A₂ τ (y₂ τ)‖ ≤ M * ‖w τ‖ + ε * (‖δ‖ * exp (M * T)) :=
      fun τ hτ => hbound_aux τ (hsub_R ⟨hτ.1, le_of_lt hτ.2⟩)
    have hw_initial : ‖w t₀‖ ≤ 0 := by
      simp [w, h₁.1, h₂.1]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := w) (f' := fun τ => A₁ τ (y₁ τ) - A₂ τ (y₂ τ))
      (δ := 0) (K := M) (ε := ε * (‖δ‖ * exp (M * T)))
      hw_cont hw_d hw_initial hbound_R
    have ht_R : t ∈ Icc t₀ (t₀ + T) := ⟨htge, ht.2⟩
    have hgr_t := hgr t ht_R
    have hx_nn : 0 ≤ t - t₀ := by linarith
    have hx_le_T : t - t₀ ≤ T := by linarith [ht.2]
    exact le_trans hgr_t (hreduce_full hx_nn hx_le_T)
  · have hsub_L : Icc (t₀ - T) t₀ ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_right (by linarith)
    set φ : ℝ → ℝ := fun s => 2 * t₀ - s
    set z : ℝ → E := w ∘ φ
    have hφ_cont : Continuous φ := by
      change Continuous (fun s : ℝ => 2 * t₀ - s); fun_prop
    have hφ_map : ∀ s ∈ Icc t₀ (t₀ + T), φ s ∈ Icc (t₀ - T) t₀ := by
      intro s hs
      refine ⟨?_, ?_⟩
      · change t₀ - T ≤ 2 * t₀ - s; linarith [hs.2]
      · change 2 * t₀ - s ≤ t₀; linarith [hs.1]
    have hz_cont : ContinuousOn z (Icc t₀ (t₀ + T)) := by
      apply ((h₁.continuousOn.sub h₂.continuousOn).mono hsub_L).comp hφ_cont.continuousOn
      intro s hs; exact hφ_map s hs
    have hw_dL : ∀ τ ∈ Ioc (t₀ - T) t₀,
        HasDerivWithinAt w (A₁ τ (y₁ τ) - A₂ τ (y₂ τ)) (Iic τ) τ := by
      intro τ hτ
      have hτ_in : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_L ⟨le_of_lt hτ.1, hτ.2⟩
      have hτ_Ioc : τ ∈ Ioc (t₀ - T) (t₀ + T) := ⟨hτ.1, by linarith [hτ.2]⟩
      have hd₁ : HasDerivWithinAt y₁ (A₁ τ (y₁ τ)) (Iic τ) τ :=
        hasDerivWithinAt_Iic_of_Icc (h₁.2 τ hτ_in) hτ_Ioc
      have hd₂ : HasDerivWithinAt y₂ (A₂ τ (y₂ τ)) (Iic τ) τ :=
        hasDerivWithinAt_Iic_of_Icc (h₂.2 τ hτ_in) hτ_Ioc
      exact hd₁.sub hd₂
    have hz_d : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt z (-(A₁ (φ τ) (y₁ (φ τ)) - A₂ (φ τ) (y₂ (φ τ)))) (Ici τ) τ := by
      intro τ hτ
      have hreflect : φ τ ∈ Ioc (t₀ - T) t₀ := by
        refine ⟨?_, ?_⟩
        · change t₀ - T < 2 * t₀ - τ; linarith [hτ.2]
        · change 2 * t₀ - τ ≤ t₀; linarith [hτ.1]
      have hw_d_τ := hw_dL (φ τ) hreflect
      have hφ_d : HasDerivWithinAt φ (-1 : ℝ) (Ici τ) τ := by
        have h1 : HasDerivAt φ (-1 : ℝ) τ := by
          have h2 : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1 : ℝ) τ := by
            exact (((hasDerivAt_const τ (2 * t₀)).sub (hasDerivAt_id τ)).congr_deriv
              (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
          exact h2
        exact h1.hasDerivWithinAt
      have hmaps : MapsTo φ (Ici τ) (Iic (φ τ)) := by
        intro s hs
        have hs_le : τ ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ
        linarith
      have hcomp := HasDerivWithinAt.scomp (g₁ := w) (h := φ) τ hw_d_τ hφ_d hmaps
      convert hcomp using 1
      module
    have hbound_L : ∀ τ ∈ Ico t₀ (t₀ + T),
        ‖-(A₁ (φ τ) (y₁ (φ τ)) - A₂ (φ τ) (y₂ (φ τ)))‖
          ≤ M * ‖z τ‖ + ε * (‖δ‖ * exp (M * T)) := by
      intro τ hτ
      have hreflect : φ τ ∈ Icc (t₀ - T) (t₀ + T) := by
        refine ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      rw [norm_neg]
      have h := hbound_aux (φ τ) hreflect
      change ‖A₁ (φ τ) (y₁ (φ τ)) - A₂ (φ τ) (y₂ (φ τ))‖ ≤ M * ‖z τ‖ + ε * (‖δ‖ * exp (M * T))
      have h_w_z : w (φ τ) = z τ := rfl
      rw [h_w_z] at h
      exact h
    have hz_initial : ‖z t₀‖ ≤ 0 := by
      change ‖w (2 * t₀ - t₀)‖ ≤ 0
      have h0 : 2 * t₀ - t₀ = t₀ := by ring
      simp [w, h0, h₁.1, h₂.1]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := z) (f' := fun τ => -(A₁ (φ τ) (y₁ (φ τ)) - A₂ (φ τ) (y₂ (φ τ))))
      (δ := 0) (K := M) (ε := ε * (‖δ‖ * exp (M * T)))
      hz_cont hz_d hz_initial hbound_L
    set τ' := 2 * t₀ - t
    have hτ'_in : τ' ∈ Icc t₀ (t₀ + T) := ⟨by linarith [htlt.le], by linarith [ht.1]⟩
    have hgr_τ' := hgr τ' hτ'_in
    have hz_τ' : z τ' = y₁ t - y₂ t := by
      change w (2 * t₀ - τ') = y₁ t - y₂ t
      have h0 : 2 * t₀ - τ' = t := by change 2 * t₀ - (2 * t₀ - t) = t; ring
      rw [h0]
    rw [hz_τ'] at hgr_τ'
    have hx_nn : 0 ≤ τ' - t₀ := by linarith [htlt.le]
    have hx_le_T : τ' - t₀ ≤ T := by change 2 * t₀ - t - t₀ ≤ T; linarith [ht.1]
    exact le_trans hgr_τ' (hreduce_full hx_nn hx_le_T)

omit [CompleteSpace E] in
theorem opNorm_sub_le_of_var
    {α₁ α₂ : ℝ → E} {T M ε : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA₂_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₂ τ)‖ ≤ M)
    (hA₁_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₁ τ)‖ ≤ M)
    (hA_diff : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (α₁ τ) - fderiv ℝ (f τ) (α₂ τ)‖ ≤ ε)
    {Y₁ Y₂ : ℝ → E →L[ℝ] E}
    (h₁ : ∀ δ, IsVariationalSolutionOn f α₁ δ t₀ (fun s => Y₁ s δ)
      (Icc (t₀ - T) (t₀ + T)))
    (h₂ : ∀ δ, IsVariationalSolutionOn f α₂ δ t₀ (fun s => Y₂ s δ)
      (Icc (t₀ - T) (t₀ + T))) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖Y₁ t - Y₂ t‖ ≤ ε * exp (M * T) * T * exp (M * T) := by
  intro t ht
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg hε (le_of_lt (exp_pos _))) hT.le)
      (le_of_lt (exp_pos _)))
  intro δ
  rw [sub_apply]
  have hcompare := variationalSolution_compare_norm hT hM hε
    hA₂_bd hA₁_bd hA_diff (h₁ δ) (h₂ δ) t ht
  calc
    ‖Y₁ t δ - Y₂ t δ‖ ≤
        ε * ‖δ‖ * exp (M * T) * T * exp (M * T) := hcompare
    _ = (ε * exp (M * T) * T * exp (M * T)) * ‖δ‖ := by ring

end GronwallCompare

section VariationalCLMContinuity

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

lemma variationalLinearMapAt_opNorm_sub_bound
    {α₁ α₂ : ℝ → E} {T M ε : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hε : 0 ≤ ε)
    (hA₁_cont : ContinuousOn (fun τ => fderiv ℝ (f τ) (α₁ τ)) (Icc (t₀ - T) (t₀ + T)))
    (hA₂_cont : ContinuousOn (fun τ => fderiv ℝ (f τ) (α₂ τ)) (Icc (t₀ - T) (t₀ + T)))
    (hA₁_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₁ τ)‖ ≤ M)
    (hA₂_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α₂ τ)‖ ≤ M)
    (hA_diff : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (α₁ τ) - fderiv ℝ (f τ) (α₂ τ)‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    ‖variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA₁_cont hA₁_bd ht
      - variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA₂_cont hA₂_bd ht‖
      ≤ ε * exp (M * T) * T * exp (M * T) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg hε (le_of_lt (exp_pos _))) (le_of_lt hT))
      (le_of_lt (exp_pos _)))
  intro δ
  set L₁ := variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA₁_cont hA₁_bd ht
  set L₂ := variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA₂_cont hA₂_bd ht
  set y₁ : ℝ → E := variationalSolutionFun (f := f) (α := α₁) hT hM hMT hA₁_cont hA₁_bd δ
  set y₂ : ℝ → E := variationalSolutionFun (f := f) (α := α₂) hT hM hMT hA₂_cont hA₂_bd δ
  have hL₁_eq : L₁ δ = y₁ t :=
    variationalLinearMapAt_apply hT hM hMT hA₁_cont hA₁_bd ht δ
  have hL₂_eq : L₂ δ = y₂ t :=
    variationalLinearMapAt_apply hT hM hMT hA₂_cont hA₂_bd ht δ
  have h_sub : (L₁ - L₂) δ = y₁ t - y₂ t := by
    rw [sub_apply, hL₁_eq, hL₂_eq]
  rw [h_sub]
  have h₁ := variationalSolutionFun_isSolution hT hM hMT hA₁_cont hA₁_bd δ
  have h₂ := variationalSolutionFun_isSolution hT hM hMT hA₂_cont hA₂_bd δ
  have hcompare := variationalSolution_compare_norm hT hM hε
    hA₂_bd hA₁_bd hA_diff h₁ h₂ t ht
  have hgoal :
      ε * ‖δ‖ * exp (M * T) * T * exp (M * T)
        = ε * exp (M * T) * T * exp (M * T) * ‖δ‖ := by ring
  linarith [hcompare, hgoal]

lemma variationalLinearMapAt_opNorm_time_lipschitz
    {α : ℝ → E} {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun τ => fderiv ℝ (f τ) (α τ)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (α τ)‖ ≤ M)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (t₀ - T) (t₀ + T)) (ht₂ : t₂ ∈ Icc (t₀ - T) (t₀ + T)) :
    ‖variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht₁
      - variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht₂‖
      ≤ M * exp (M * T) * |t₁ - t₂| := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hM (le_of_lt (exp_pos _))) (abs_nonneg _))
  intro δ
  set L₁ := variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht₁
  set L₂ := variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht₂
  set y : ℝ → E := variationalSolutionFun (f := f) (α := α) hT hM hMT hA_cont hA_bd δ
  have hL₁_eq : L₁ δ = y t₁ :=
    variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht₁ δ
  have hL₂_eq : L₂ δ = y t₂ :=
    variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht₂ δ
  have h_sub : (L₁ - L₂) δ = y t₁ - y t₂ := by
    rw [sub_apply, hL₁_eq, hL₂_eq]
  rw [h_sub]
  have hy_solution := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have hy_bd := fun τ (hτ : τ ∈ Icc (t₀ - T) (t₀ + T)) =>
    variationalSolutionFun_norm_le hT hM hMT hA_cont hA_bd δ hτ
  have hy_deriv_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖(fderiv ℝ (f τ) (α τ)) (y τ)‖ ≤ M * exp (M * T) * ‖δ‖ := by
    intro τ hτ
    calc ‖(fderiv ℝ (f τ) (α τ)) (y τ)‖
        ≤ ‖fderiv ℝ (f τ) (α τ)‖ * ‖y τ‖ := (fderiv ℝ (f τ) (α τ)).le_opNorm _
      _ ≤ M * (exp (M * T) * ‖δ‖) := by
          apply mul_le_mul (hA_bd τ hτ) (hy_bd τ hτ) (norm_nonneg _) hM
      _ = M * exp (M * T) * ‖δ‖ := by ring
  set tlo : ℝ := min t₁ t₂
  set thi : ℝ := max t₁ t₂
  have htlo_le_thi : tlo ≤ thi := min_le_max
  have htlo_in : tlo ∈ Icc (t₀ - T) (t₀ + T) :=
    ⟨le_min ht₁.1 ht₂.1, (min_le_left _ _).trans ht₁.2⟩
  have hthi_in : thi ∈ Icc (t₀ - T) (t₀ + T) :=
    ⟨ht₁.1.trans (le_max_left _ _), max_le ht₁.2 ht₂.2⟩
  have hseg_sub : Icc tlo thi ⊆ Icc (t₀ - T) (t₀ + T) := fun τ hτ =>
    ⟨htlo_in.1.trans hτ.1, hτ.2.trans hthi_in.2⟩
  have hy_d_segment : ∀ τ ∈ Icc tlo thi,
      HasDerivWithinAt y ((fderiv ℝ (f τ) (α τ)) (y τ)) (Icc tlo thi) τ := fun τ hτ =>
    (hy_solution.2 τ (hseg_sub hτ)).mono hseg_sub
  have hy_d_segment_bd : ∀ τ ∈ Ico tlo thi,
      ‖(fderiv ℝ (f τ) (α τ)) (y τ)‖ ≤ M * exp (M * T) * ‖δ‖ := fun τ hτ =>
    hy_deriv_bd τ (hseg_sub ⟨hτ.1, le_of_lt hτ.2⟩)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := y) (f' := fun τ => (fderiv ℝ (f τ) (α τ)) (y τ))
    (C := M * exp (M * T) * ‖δ‖) (a := tlo) (b := thi)
    hy_d_segment hy_d_segment_bd thi (right_mem_Icc.mpr htlo_le_thi)
  have h_diff_eq : thi - tlo = |t₁ - t₂| := by
    rcases le_or_gt t₁ t₂ with h | h
    · have htlo : tlo = t₁ := min_eq_left h
      have hthi : thi = t₂ := max_eq_right h
      rw [htlo, hthi]
      rw [abs_sub_comm, abs_of_nonneg]; linarith
    · have htlo : tlo = t₂ := min_eq_right (le_of_lt h)
      have hthi : thi = t₁ := max_eq_left (le_of_lt h)
      rw [htlo, hthi, abs_of_nonneg]; linarith
  have h_y_diff_le : ‖y t₁ - y t₂‖ ≤ ‖y thi - y tlo‖ := by
    rcases le_or_gt t₁ t₂ with h | h
    · have htlo : tlo = t₁ := min_eq_left h
      have hthi : thi = t₂ := max_eq_right h
      rw [htlo, hthi]
      rw [show y t₁ - y t₂ = -(y t₂ - y t₁) by abel, norm_neg]
    · have htlo : tlo = t₂ := min_eq_right (le_of_lt h)
      have hthi : thi = t₁ := max_eq_left (le_of_lt h)
      rw [htlo, hthi]
  rw [h_diff_eq] at hmvt
  have hgoal : M * exp (M * T) * ‖δ‖ * |t₁ - t₂|
      = M * exp (M * T) * |t₁ - t₂| * ‖δ‖ := by ring
  linarith [hmvt, h_y_diff_le, hgoal]

end VariationalCLMContinuity

section JointContinuity

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
lemma continuousOn_fderiv_jointly
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ : ℝ} (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun p : E × ℝ => fderiv ℝ (f p.2) (Φ ⟨p.1, p.2⟩))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  set K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  have hK_sub : K ⊆ closedBall x₀ r ×ˢ Icc tmin tmax := by
    intro p hp
    refine ⟨closedBall_subset_closedBall hρ_le hp.1, hsub hp.2⟩
  have hΦ_cont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  have hmap : ContinuousOn (fun p : E × ℝ => ((p.2, Φ ⟨p.1, p.2⟩) : ℝ × E)) K := by
    apply ContinuousOn.prodMk
    · exact continuousOn_snd
    · exact hΦ_cont
  have hmt : MapsTo (fun p : E × ℝ => ((p.2, Φ ⟨p.1, p.2⟩) : ℝ × E)) K
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  exact hpartial.comp hmap hmt

end JointContinuity

section ContDiffOnUpgrade

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

lemma differentiableOn_flow_of_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    DifferentiableOn ℝ Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  intro p hp
  rcases hp with ⟨hp_x, hp_t⟩
  rw [mem_ball] at hp_x
  obtain ⟨x, t⟩ := p
  have hx_cb : x ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hp_x)
  have h := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx_cb hp_t
  exact h.differentiableAt.differentiableWithinAt

omit [CompleteSpace E] in
lemma continuousOn_timePiece
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ : ℝ} (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun q : E × ℝ => f q.2 (Φ ⟨q.1, q.2⟩))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  set K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  have hK_sub : K ⊆ closedBall x₀ r ×ˢ Icc tmin tmax := fun p hp =>
    ⟨closedBall_subset_closedBall hρ_le hp.1, hsub hp.2⟩
  have hΦ_cont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  have hmap : ContinuousOn (fun q : E × ℝ => ((q.2, Φ ⟨q.1, q.2⟩) : ℝ × E)) K :=
    ContinuousOn.prodMk continuousOn_snd hΦ_cont
  have hf_cont : Continuous (uncurry f) :=
    continuousOn_univ.mp hf_C1.continuousOn
  have hmt : MapsTo (fun q : E × ℝ => ((q.2, Φ ⟨q.1, q.2⟩) : ℝ × E)) K
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  exact hf_cont.continuousOn.comp hmap hmt

omit [CompleteSpace E] in
lemma uniformly_close_fderiv_in_x
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T T' : ℝ} (hT'_lt : T' < T)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ ρ' : ℝ} (hρ_le : ρ ≤ (r : ℝ)) (hρ'_lt : ρ' < ρ)
    {x : E} (hx : dist x x₀ < ρ')
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ xq : E, dist xq x < δ →
      ∀ τ ∈ Icc (t₀ - T') (t₀ + T'),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩) - fderiv ℝ (f τ) (Φ ⟨xq, τ⟩)‖ < ε := by
  set Kc : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T) with hKc_def
  set F : E × ℝ → (E →L[ℝ] E) := fun q => fderiv ℝ (f q.2) (Φ ⟨q.1, q.2⟩)
  have hF_cont_slab : ContinuousOn F Kc :=
    continuousOn_fderiv_jointly hΦ hf_C1 hsub hρ_le
  set L : Set (E × ℝ) := {x} ×ˢ Icc (t₀ - T') (t₀ + T')
  have hL_compact : IsCompact L :=
    (isCompact_singleton (x := x)).prod isCompact_Icc
  set Uo : Set (E × ℝ) := ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hUo_open : IsOpen Uo := isOpen_ball.prod isOpen_Ioo
  have hUo_sub_Kc : Uo ⊆ Kc := fun p hp =>
    ⟨(mem_ball.mp hp.1).le |> mem_closedBall.mpr, Ioo_subset_Icc_self hp.2⟩
  have hL_sub_Uo : L ⊆ Uo := by
    intro p hp
    rcases hp with ⟨hp_x, hp_t⟩
    rw [mem_singleton_iff] at hp_x
    refine ⟨?_, ?_⟩
    · rw [hp_x, mem_ball]
      exact lt_of_lt_of_le hx (by linarith)
    · exact ⟨lt_of_lt_of_le (by linarith) hp_t.1,
        lt_of_le_of_lt hp_t.2 (by linarith)⟩
  have hF_at_L : ∀ p ∈ L, ContinuousAt F p := by
    intro p hp
    have hp_Uo : p ∈ Uo := hL_sub_Uo hp
    have hp_Kc : p ∈ Kc := hUo_sub_Kc hp_Uo
    have hUo_nhds : Uo ∈ nhds p := IsOpen.mem_nhds hUo_open hp_Uo
    have hKc_nhds : Kc ∈ nhds p := Filter.mem_of_superset hUo_nhds hUo_sub_Kc
    exact (hF_cont_slab p hp_Kc).continuousAt hKc_nhds
  have hr_uniform : { y : (E →L[ℝ] E) × (E →L[ℝ] E) | dist y.1 y.2 < ε / 2 } ∈
      uniformity (E →L[ℝ] E) := Metric.dist_mem_uniformity (by positivity)
  have hL_uniform := hL_compact.uniformContinuousAt_of_continuousAt F hF_at_L hr_uniform
  rcases Metric.mem_uniformity_dist.mp hL_uniform with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun xq hxq τ hτ => ?_⟩
  set p₁ : E × ℝ := (x, τ)
  set p₂ : E × ℝ := (xq, τ)
  have hp₁_L : p₁ ∈ L := ⟨mem_singleton x, hτ⟩
  have h_dist : dist p₁ p₂ < δ := by
    rw [Prod.dist_eq]
    have h1 : dist τ τ = 0 := dist_self _
    rw [h1]
    have h2 : max (dist x xq) 0 = dist x xq := by
      apply max_eq_left dist_nonneg
    rw [h2, dist_comm]
    exact hxq
  have hpair_d : (F p₁, F p₂) ∈ { y : (E →L[ℝ] E) × (E →L[ℝ] E) | dist y.1 y.2 < ε / 2 } :=
    hδ h_dist hp₁_L
  change dist (F p₁) (F p₂) < ε / 2 at hpair_d
  rw [dist_eq_norm] at hpair_d
  change ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩) - fderiv ℝ (f τ) (Φ ⟨xq, τ⟩)‖ < ε
  linarith

lemma portPrivate_3f231c1a_opNorm_coprod_le {F G H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L₁ : F →L[ℝ] H) (L₂ : G →L[ℝ] H) :
    ‖L₁.coprod L₂‖ ≤ ‖L₁‖ + ‖L₂‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  rw [ContinuousLinearMap.coprod_apply]
  calc ‖L₁ p.1 + L₂ p.2‖ ≤ ‖L₁ p.1‖ + ‖L₂ p.2‖ := norm_add_le _ _
    _ ≤ ‖L₁‖ * ‖p.1‖ + ‖L₂‖ * ‖p.2‖ := by
        gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖L₁‖ * ‖p‖ + ‖L₂‖ * ‖p‖ := by
        have h1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
        have h2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        gcongr
    _ = (‖L₁‖ + ‖L₂‖) * ‖p‖ := by ring


theorem continuousOn_fderiv_flow_of_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContinuousOn (fderiv ℝ Φ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hT_out_pos : 0 < T_out := lt_trans hT_mid_pos hT_mid_lt_out
  have hρ_mid_pos : 0 < (ρ_mid : ℝ) := lt_of_le_of_lt (ρ.coe_nonneg) hρ_lt_mid
  have hρ_out_pos : 0 < (ρ_out : ℝ) := lt_trans hρ_mid_pos hρ_mid_lt_out
  have hρ_mid_le_r : (ρ_mid : ℝ) ≤ (r : ℝ) := le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ), ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ =>
    hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  set ETT : ℝ := exp (M * T_mid) * T_mid * exp (M * T_mid) with hETT_def
  have hETT_nn : 0 ≤ ETT :=
    mul_nonneg (mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt hT_mid_pos)) (le_of_lt (exp_pos _))
  set ETM : ℝ := M * exp (M * T_mid) with hETM_def
  have hETM_nn : 0 ≤ ETM := mul_nonneg hM (le_of_lt (exp_pos _))
  have htp_cont := continuousOn_timePiece hΦ hf_C1 hsub_mid hρ_mid_le_r
  intro p hp
  rcases hp with ⟨hp_x, hp_t⟩
  rw [mem_ball] at hp_x
  obtain ⟨x, t⟩ := p
  have hx_cb_ρ : x ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hp_x)
  have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
    closedBall_subset_closedBall (le_of_lt hρ_lt_mid) hx_cb_ρ
  have hp_t_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨by linarith [hp_t.1], by linarith [hp_t.2]⟩
  have hA_cont_x : ContinuousOn (fun τ => fderiv ℝ (f τ) (Φ ⟨x, τ⟩))
      (Icc (t₀ - T_mid) (t₀ + T_mid)) :=
    (hΦ.continuousOn_fderiv_along_orbit hf_C1 x
      (closedBall_subset_closedBall hρ_mid_le_r hx_cb_mid)).mono hsub_mid
  set Lsp_p : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid hA_cont_x (hA_bd_mid x hx_cb_mid) (Ioo_subset_Icc_self hp_t_mid)
  set Lti_p : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
  have hfd_at_p :=
    hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ' hA_bd_mid
      hx_cb_mid hp_t_mid
  have hfd_p_eq : fderiv ℝ Φ (x, t) = Lsp_p.coprod Lti_p := hfd_at_p.fderiv
  rw [Metric.continuousWithinAt_iff]
  intro c hc
  set ε_spatial : ℝ := c / (4 * (ETT + 1)) with hε_spatial_def
  have hε_spatial_pos : 0 < ε_spatial := by positivity
  set δ_lip_t : ℝ := c / (4 * (ETM + 1)) with hδ_lip_t_def
  have hδ_lip_t_pos : 0 < δ_lip_t := by positivity
  rcases uniformly_close_fderiv_in_x hΦ hf_C1 hT_mid_lt_out hsub
    hρ_out_le_r hρ_mid_lt_out
    (show dist x x₀ < (ρ_mid : ℝ) from lt_trans hp_x hρ_lt_mid) hε_spatial_pos
    with ⟨δ_fd, hδ_fd_pos, hδ_fd⟩
  have hp_Kc_mid : (x, t) ∈ closedBall x₀ (ρ_mid : ℝ) ×ˢ Icc (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨hx_cb_mid, Ioo_subset_Icc_self hp_t_mid⟩
  rcases Metric.continuousOn_iff.mp htp_cont (x, t) hp_Kc_mid (c / 2) (by positivity)
    with ⟨δ_tp, hδ_tp_pos, hδ_tp⟩
  have hρgap_pos : 0 < ((ρ : ℝ) - dist x x₀) / 2 := by linarith
  set δ_p : ℝ := min (min δ_fd δ_tp) (min δ_lip_t (((ρ : ℝ) - dist x x₀) / 2)) with hδ_p_def
  have hδ_p_pos : 0 < δ_p :=
    lt_min (lt_min hδ_fd_pos hδ_tp_pos) (lt_min hδ_lip_t_pos hρgap_pos)
  refine ⟨δ_p, hδ_p_pos, ?_⟩
  intro q hq hqdist
  obtain ⟨xq, tq⟩ := q
  rcases hq with ⟨hq_x, hq_t⟩
  rw [mem_ball] at hq_x
  have hxq_cb_ρ : xq ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
  have hxq_cb_mid : xq ∈ closedBall x₀ (ρ_mid : ℝ) :=
    closedBall_subset_closedBall (le_of_lt hρ_lt_mid) hxq_cb_ρ
  have hq_t_mid : tq ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨by linarith [hq_t.1], by linarith [hq_t.2]⟩
  have hq_Kc_mid : (xq, tq) ∈ closedBall x₀ (ρ_mid : ℝ) ×ˢ Icc (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨hxq_cb_mid, Ioo_subset_Icc_self hq_t_mid⟩
  have hA_cont_xq : ContinuousOn (fun τ => fderiv ℝ (f τ) (Φ ⟨xq, τ⟩))
      (Icc (t₀ - T_mid) (t₀ + T_mid)) :=
    (hΦ.continuousOn_fderiv_along_orbit hf_C1 xq
      (closedBall_subset_closedBall hρ_mid_le_r hxq_cb_mid)).mono hsub_mid
  set Lsp_q : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨xq, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid hA_cont_xq (hA_bd_mid xq hxq_cb_mid) (Ioo_subset_Icc_self hq_t_mid)
  set Lti_q : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f tq (Φ ⟨xq, tq⟩))
  have hfd_at_q :=
    hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ' hA_bd_mid
      hxq_cb_mid hq_t_mid
  have hfd_q_eq : fderiv ℝ Φ (xq, tq) = Lsp_q.coprod Lti_q := hfd_at_q.fderiv
  rw [dist_eq_norm, hfd_q_eq, hfd_p_eq]
  have hcoprod_diff :
      Lsp_q.coprod Lti_q - Lsp_p.coprod Lti_p = (Lsp_q - Lsp_p).coprod (Lti_q - Lti_p) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    simp [sub_apply, ContinuousLinearMap.coprod_apply]
    abel
  rw [hcoprod_diff]
  have hcoprod_norm :
      ‖(Lsp_q - Lsp_p).coprod (Lti_q - Lti_p)‖
        ≤ ‖Lsp_q - Lsp_p‖ + ‖Lti_q - Lti_p‖ :=
    portPrivate_3f231c1a_opNorm_coprod_le _ _
  set Lsp_q_t : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨xq, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid hA_cont_xq (hA_bd_mid xq hxq_cb_mid)
      (Ioo_subset_Icc_self hp_t_mid)
  have hxq_dist : dist xq x < δ_fd := by
    have hd_pair : dist ((x, t) : E × ℝ) (xq, tq) < δ_p := by rw [dist_comm]; exact hqdist
    have hd_x : dist x xq ≤ dist ((x, t) : E × ℝ) (xq, tq) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have hδ_p_le_δ_fd : δ_p ≤ δ_fd := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [dist_comm]; linarith
  have h_sp_bound : ‖Lsp_p - Lsp_q_t‖ ≤ ε_spatial * ETT := by
    have h_A_diff : ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩) - fderiv ℝ (f τ) (Φ ⟨xq, τ⟩)‖ ≤ ε_spatial :=
      fun τ hτ => le_of_lt (hδ_fd xq hxq_dist τ hτ)
    have h := variationalLinearMapAt_opNorm_sub_bound hT_mid_pos hM hMT_mid
      (le_of_lt hε_spatial_pos) hA_cont_x hA_cont_xq (hA_bd_mid x hx_cb_mid)
      (hA_bd_mid xq hxq_cb_mid) h_A_diff (Ioo_subset_Icc_self hp_t_mid)
    change ‖Lsp_p - Lsp_q_t‖ ≤ ε_spatial * (exp (M * T_mid) * T_mid * exp (M * T_mid))
    have : ε_spatial * (exp (M * T_mid) * T_mid * exp (M * T_mid))
        = ε_spatial * exp (M * T_mid) * T_mid * exp (M * T_mid) := by ring
    linarith
  have h_sp_time_bound : ‖Lsp_q_t - Lsp_q‖ ≤ ETM * |t - tq| := by
    exact variationalLinearMapAt_opNorm_time_lipschitz hT_mid_pos hM hMT_mid hA_cont_xq
      (hA_bd_mid xq hxq_cb_mid) (Ioo_subset_Icc_self hp_t_mid)
      (Ioo_subset_Icc_self hq_t_mid)
  have h_sp_total : ‖Lsp_q - Lsp_p‖ ≤ ε_spatial * ETT + ETM * |t - tq| := by
    have h1 : ‖Lsp_q - Lsp_p‖ ≤ ‖Lsp_p - Lsp_q_t‖ + ‖Lsp_q_t - Lsp_q‖ := by
      have heq : Lsp_q - Lsp_p = -(Lsp_p - Lsp_q_t) + -(Lsp_q_t - Lsp_q) := by abel
      rw [heq]
      have := norm_add_le (-(Lsp_p - Lsp_q_t)) (-(Lsp_q_t - Lsp_q))
      rw [norm_neg, norm_neg] at this
      exact this
    linarith
  have h_tdist_bd : |t - tq| < δ_lip_t := by
    have hd_pair : dist ((x, t) : E × ℝ) (xq, tq) < δ_p := by rw [dist_comm]; exact hqdist
    have hd_t : dist t tq ≤ dist ((x, t) : E × ℝ) (xq, tq) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hδ_p_le : δ_p ≤ δ_lip_t := le_trans (min_le_right _ _) (min_le_left _ _)
    have h : dist t tq < δ_lip_t := by linarith
    rwa [Real.dist_eq] at h
  have h_ETM_lip : ETM * |t - tq| < c / 4 := by
    have h1 : ETM * |t - tq| ≤ ETM * δ_lip_t :=
      mul_le_mul_of_nonneg_left (le_of_lt h_tdist_bd) hETM_nn
    have hETM1_pos : 0 < ETM + 1 := by linarith
    have hETMle : ETM * δ_lip_t ≤ (ETM + 1) * δ_lip_t :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hδ_lip_t_pos)
    have key : (ETM + 1) * δ_lip_t = c / 4 := by rw [hδ_lip_t_def]; field_simp
    linarith
  have h_eps_ETT : ε_spatial * ETT < c / 4 := by
    have hETT1_pos : 0 < ETT + 1 := by linarith
    have hETTle : ε_spatial * ETT ≤ ε_spatial * (ETT + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε_spatial_pos)
    have key : ε_spatial * (ETT + 1) = c / 4 := by rw [hε_spatial_def]; field_simp
    linarith
  have h_ti_bound : ‖Lti_q - Lti_p‖ ≤ c / 2 := by
    have hdiff : Lti_q - Lti_p = (ContinuousLinearMap.id ℝ ℝ).smulRight
        (f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)) := by
      apply ContinuousLinearMap.ext
      intro s
      change s • f tq (Φ ⟨xq, tq⟩) - s • f t (Φ ⟨x, t⟩)
        = (ContinuousLinearMap.id ℝ ℝ).smulRight
            (f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)) s
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_sub]
    rw [hdiff]
    have hnorm_eq : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
          (f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩))‖
        = ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)‖ :=
      ContinuousLinearMap.norm_smulRight_apply _ _
    rw [hnorm_eq]
    have hid_norm : ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h_le : ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)‖
        ≤ ‖f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)‖ := by
      have h2 : ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)‖
          ≤ 1 * ‖f tq (Φ ⟨xq, tq⟩) - f t (Φ ⟨x, t⟩)‖ :=
        mul_le_mul_of_nonneg_right hid_norm (norm_nonneg _)
      rw [one_mul] at h2; exact h2
    have h_dist_tp : dist ((xq, tq) : E × ℝ) (x, t) < δ_tp := by
      have hδ_p_le : δ_p ≤ δ_tp := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have h_tp := hδ_tp (xq, tq) hq_Kc_mid h_dist_tp
    rw [dist_eq_norm] at h_tp; linarith
  have hgoal : ‖Lsp_q - Lsp_p‖ + ‖Lti_q - Lti_p‖ < c := by
    have hsum : ε_spatial * ETT + ETM * |t - tq| < c / 2 := by
      have : c / 4 + c / 4 = c / 2 := by ring
      linarith [h_eps_ETT, h_ETM_lip]
    linarith
  linarith [hcoprod_norm, hgoal]

theorem contDiffOn_flow_of_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ), ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ =>
    hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  set U : Set (E × ℝ) := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hU_open : IsOpen U := isOpen_ball.prod isOpen_Ioo
  rw [show (1 : WithTop ℕ∞) = (0 + 1 : WithTop ℕ∞) by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU_open]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hp_x, hp_t⟩
    rw [mem_ball] at hp_x
    obtain ⟨x, t⟩ := p
    have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
      mem_closedBall.mpr (le_of_lt (lt_trans hp_x hρ_lt_mid))
    have hp_t_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
      ⟨by linarith [hp_t.1], by linarith [hp_t.2]⟩
    have h := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ'
      hA_bd_mid hx_cb_mid hp_t_mid
    exact h.differentiableAt.differentiableWithinAt
  · intro h; exact absurd h (by decide)
  · rw [contDiffOn_zero]
    exact continuousOn_fderiv_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM
      hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end ContDiffOnUpgrade

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
