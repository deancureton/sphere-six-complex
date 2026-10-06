module

public import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.GlobalExistence

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section JointContinuity

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
theorem portPrivate_c8c79eec_linearODE_apriori_bound
    {A : ℝ → (G →L[ℝ] G)} {a b α β c M : ℝ}
    (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b)
    (hc_mem : c ∈ Icc α β) (hM_nn : 0 ≤ M)
    (hA_bd : ∀ s ∈ Icc α β, ‖A s‖ ≤ M)
    {Z : ℝ → G} (hZ_deriv : ∀ t ∈ Ioo a b, HasDerivAt Z (A t (Z t)) t)
    (t : ℝ) (ht : t ∈ Icc α β) :
    ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (β - α)) := by
  have hsub : Icc α β ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hZ_cont : ContinuousOn Z (Icc α β) := fun s hs =>
    ((hZ_deriv s (hsub hs)).continuousAt).continuousWithinAt
  have hZ_deriv_within_right : ∀ s ∈ Icc α β, HasDerivWithinAt Z (A s (Z s)) (Ici s) s :=
    fun s hs => ((hZ_deriv s (hsub hs)).hasDerivWithinAt)
  have hZ'_bound : ∀ s ∈ Icc α β, ‖A s (Z s)‖ ≤ M * ‖Z s‖ + 0 := by
    intro s hs
    have h1 : ‖A s (Z s)‖ ≤ ‖A s‖ * ‖Z s‖ := (A s).le_opNorm (Z s)
    have h2 : ‖A s‖ * ‖Z s‖ ≤ M * ‖Z s‖ :=
      mul_le_mul_of_nonneg_right (hA_bd s hs) (norm_nonneg _)
    linarith
  rcases le_total c t with hct | htc
  · have hsub' : Icc c t ⊆ Icc α β := fun s hs =>
      ⟨le_trans hc_mem.1 hs.1, le_trans hs.2 ht.2⟩
    have hZ_cont_ct : ContinuousOn Z (Icc c t) := hZ_cont.mono hsub'
    have hZ_deriv_within_right_ct :
        ∀ s ∈ Ico c t, HasDerivWithinAt Z (A s (Z s)) (Ici s) s :=
      fun s hs => hZ_deriv_within_right s (hsub' (Ico_subset_Icc_self hs))
    have hZ'_bound_ct : ∀ s ∈ Ico c t, ‖A s (Z s)‖ ≤ M * ‖Z s‖ + 0 :=
      fun s hs => hZ'_bound s (hsub' (Ico_subset_Icc_self hs))
    have habs := norm_le_gronwallBound_of_norm_deriv_right_le hZ_cont_ct
      hZ_deriv_within_right_ct (le_refl _) hZ'_bound_ct t (right_mem_Icc.mpr hct)
    rw [gronwallBound_ε0] at habs
    have h_mono : M * (t - c) ≤ M * (β - α) := by
      apply mul_le_mul_of_nonneg_left _ hM_nn
      linarith [ht.2, hc_mem.1]
    have h_exp_mono : Real.exp (M * (t - c)) ≤ Real.exp (M * (β - α)) :=
      Real.exp_le_exp.mpr h_mono
    calc ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (t - c)) := habs
      _ ≤ ‖Z c‖ * Real.exp (M * (β - α)) :=
          mul_le_mul_of_nonneg_left h_exp_mono (norm_nonneg _)
  · set W : ℝ → G := fun s => Z (2 * c - s) with hW_def
    have h_t_le_c : t ≤ c := htc
    have h_2ctmt_ge_c : c ≤ 2 * c - t := by linarith
    have h_dom_sub : ∀ s ∈ Icc c (2 * c - t), 2 * c - s ∈ Icc α β := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have h_eq : 2 * c - (2 * c - t) = t := by ring
        linarith [ht.1, hs.2]
      · have h_eq : 2 * c - c = c := by ring
        linarith [hc_mem.2, hs.1]
    have hW_cont : ContinuousOn W (Icc c (2 * c - t)) := by
      apply ContinuousOn.comp hZ_cont (s := Icc c (2 * c - t))
        (t := Icc α β) (f := fun s => 2 * c - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_sub
    have hW_deriv : ∀ s ∈ Icc c (2 * c - t),
        HasDerivAt W (-(A (2 * c - s) (Z (2 * c - s)))) s := by
      intro s hs
      have hs_mem : (2 * c - s) ∈ Ioo a b := hsub (h_dom_sub s hs)
      have hd : HasDerivAt Z (A (2 * c - s) (Z (2 * c - s))) (2 * c - s) :=
        hZ_deriv (2 * c - s) hs_mem
      have h_chain : HasDerivAt (fun s => 2 * c - s) (-1 : ℝ) s := by
        have h := (hasDerivAt_const s (2 * c)).sub (hasDerivAt_id s)
        have hfun : (fun _ : ℝ => 2 * c) - id = fun r => 2 * c - r := by
          funext r
          rfl
        rw [hfun, zero_sub] at h
        exact h
      have hd' : HasDerivAt (Z ∘ (fun s => 2 * c - s))
          ((-1 : ℝ) • A (2 * c - s) (Z (2 * c - s))) s := hd.scomp s h_chain
      have hZ_eq : (Z ∘ (fun s => 2 * c - s)) = W := rfl
      rw [hZ_eq] at hd'
      have h_smul_eq : ((-1 : ℝ) • A (2 * c - s) (Z (2 * c - s)) : G) =
          -(A (2 * c - s) (Z (2 * c - s))) := by
        rw [neg_one_smul]
      rw [h_smul_eq] at hd'
      exact hd'
    have hW_deriv_within_right :
        ∀ s ∈ Icc c (2 * c - t),
          HasDerivWithinAt W (-(A (2 * c - s) (Z (2 * c - s)))) (Ici s) s :=
      fun s hs => (hW_deriv s hs).hasDerivWithinAt
    have hW'_bound : ∀ s ∈ Ico c (2 * c - t),
        ‖-(A (2 * c - s) (Z (2 * c - s)))‖ ≤ M * ‖W s‖ + 0 := by
      intro s hs
      have h_in : 2 * c - s ∈ Icc α β := h_dom_sub s (Ico_subset_Icc_self hs)
      have h1 : ‖A (2 * c - s) (Z (2 * c - s))‖ ≤ ‖A (2 * c - s)‖ * ‖Z (2 * c - s)‖ :=
        (A _).le_opNorm _
      have h2 : ‖A (2 * c - s)‖ * ‖Z (2 * c - s)‖ ≤ M * ‖Z (2 * c - s)‖ :=
        mul_le_mul_of_nonneg_right (hA_bd _ h_in) (norm_nonneg _)
      have hWs_eq : W s = Z (2 * c - s) := rfl
      rw [hWs_eq, norm_neg]
      linarith
    have hW_initial : ‖W c‖ ≤ ‖Z c‖ := by
      have h_eq : W c = Z c := by
        change Z (2 * c - c) = Z c
        have : 2 * c - c = c := by ring
        rw [this]
      rw [h_eq]
    have habs := norm_le_gronwallBound_of_norm_deriv_right_le hW_cont
      (fun s hs => hW_deriv_within_right s (Ico_subset_Icc_self hs)) hW_initial
      hW'_bound (2 * c - t) (right_mem_Icc.mpr h_2ctmt_ge_c)
    rw [gronwallBound_ε0] at habs
    have hW_eq_Z : W (2 * c - t) = Z t := by
      change Z (2 * c - (2 * c - t)) = Z t
      have : 2 * c - (2 * c - t) = t := by ring
      rw [this]
    rw [hW_eq_Z] at habs
    have h_sub : (2 * c - t) - c = c - t := by ring
    rw [h_sub] at habs
    have h_mono : M * (c - t) ≤ M * (β - α) := by
      apply mul_le_mul_of_nonneg_left _ hM_nn
      linarith [hc_mem.2, ht.1]
    have h_exp_mono : Real.exp (M * (c - t)) ≤ Real.exp (M * (β - α)) :=
      Real.exp_le_exp.mpr h_mono
    calc ‖Z t‖ ≤ ‖Z c‖ * Real.exp (M * (c - t)) := habs
      _ ≤ ‖Z c‖ * Real.exp (M * (β - α)) :=
          mul_le_mul_of_nonneg_left h_exp_mono (norm_nonneg _)

omit [CompleteSpace G] in
theorem linearODE_gronwall_forward
    {A₁ A₂ : ℝ → (G →L[ℝ] G)} {Z₁ Z₂ : ℝ → G} {h₀ β K η : ℝ}
    (hK_nn : 0 ≤ K)
    (hZ₁_cont : ContinuousOn Z₁ (Icc h₀ β))
    (hZ₂_cont : ContinuousOn Z₂ (Icc h₀ β))
    (hZ₁_deriv : ∀ t ∈ Icc h₀ β, HasDerivAt Z₁ (A₁ t (Z₁ t)) t)
    (hZ₂_deriv : ∀ t ∈ Icc h₀ β, HasDerivAt Z₂ (A₂ t (Z₂ t)) t)
    (hA₁_bd : ∀ t ∈ Icc h₀ β, ‖A₁ t‖ ≤ K)
    (hdiff_bd : ∀ t ∈ Icc h₀ β, ‖(A₂ t - A₁ t) (Z₂ t)‖ ≤ η)
    (t : ℝ) (ht : t ∈ Icc h₀ β) :
    ‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ h₀ - Z₂ h₀‖ K η (t - h₀) := by
  let v : ℝ → G → G := fun s y => A₁ s y
  let Knn : ℝ≥0 := ⟨K, hK_nn⟩
  have hv_lip : ∀ s ∈ Ico h₀ β, LipschitzOnWith Knn (v s) (univ : Set G) := by
    intro s hs
    have h_lip : LipschitzWith Knn (A₁ s) :=
      (A₁ s).lipschitzWith_of_opNorm_le (hA₁_bd s (Ico_subset_Icc_self hs))
    exact h_lip.lipschitzOnWith
  have hZ₁_deriv_right : ∀ s ∈ Ico h₀ β, HasDerivWithinAt Z₁ (A₁ s (Z₁ s)) (Ici s) s :=
    fun s hs => (hZ₁_deriv s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hZ₂_deriv_right : ∀ s ∈ Ico h₀ β, HasDerivWithinAt Z₂ (A₂ s (Z₂ s)) (Ici s) s :=
    fun s hs => (hZ₂_deriv s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have f_bound : ∀ s ∈ Ico h₀ β, dist (A₁ s (Z₁ s)) (v s (Z₁ s)) ≤ 0 := by
    intro s _; change dist (A₁ s (Z₁ s)) (A₁ s (Z₁ s)) ≤ 0; rw [dist_self]
  have g_bound : ∀ s ∈ Ico h₀ β, dist (A₂ s (Z₂ s)) (v s (Z₂ s)) ≤ η := by
    intro s hs
    have hsmem : s ∈ Icc h₀ β := Ico_subset_Icc_self hs
    change dist (A₂ s (Z₂ s)) (A₁ s (Z₂ s)) ≤ η
    rw [dist_eq_norm]
    have h_eq : A₂ s (Z₂ s) - A₁ s (Z₂ s) = (A₂ s - A₁ s) (Z₂ s) := by
      simp [sub_apply]
    rw [h_eq]
    exact hdiff_bd s hsmem
  have hres := dist_le_of_approx_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := Knn) (f := Z₁) (g := Z₂) (f' := fun s => A₁ s (Z₁ s))
    (g' := fun s => A₂ s (Z₂ s))
    (a := h₀) (b := β) (εf := 0) (εg := η) (δ := ‖Z₁ h₀ - Z₂ h₀‖)
    hv_lip hZ₁_cont hZ₁_deriv_right f_bound (fun _ _ => mem_univ _)
    hZ₂_cont hZ₂_deriv_right g_bound (fun _ _ => mem_univ _)
    (by rw [dist_eq_norm])
  have := hres t ht
  rw [dist_eq_norm] at this
  rw [zero_add] at this
  exact this

omit [CompleteSpace G] in
theorem linearODE_gronwall_backward
    {A₁ A₂ : ℝ → (G →L[ℝ] G)} {Z₁ Z₂ : ℝ → G} {α h₀ K η : ℝ}
    (hαh₀ : α ≤ h₀) (hK_nn : 0 ≤ K)
    (hZ₁_cont : ContinuousOn Z₁ (Icc α h₀))
    (hZ₂_cont : ContinuousOn Z₂ (Icc α h₀))
    (hZ₁_deriv : ∀ t ∈ Icc α h₀, HasDerivAt Z₁ (A₁ t (Z₁ t)) t)
    (hZ₂_deriv : ∀ t ∈ Icc α h₀, HasDerivAt Z₂ (A₂ t (Z₂ t)) t)
    (hA₁_bd : ∀ t ∈ Icc α h₀, ‖A₁ t‖ ≤ K)
    (hdiff_bd : ∀ t ∈ Icc α h₀, ‖(A₂ t - A₁ t) (Z₂ t)‖ ≤ η)
    (t : ℝ) (ht : t ∈ Icc α h₀) :
    ‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ h₀ - Z₂ h₀‖ K η (h₀ - t) := by
  set W₁ : ℝ → G := fun s => Z₁ (2 * h₀ - s)
  set W₂ : ℝ → G := fun s => Z₂ (2 * h₀ - s)
  set B₁ : ℝ → (G →L[ℝ] G) := fun s => -A₁ (2 * h₀ - s)
  set B₂ : ℝ → (G →L[ℝ] G) := fun s => -A₂ (2 * h₀ - s)
  have h_h₀_le_2h₀mα : h₀ ≤ 2 * h₀ - α := by linarith
  have h_dom_swap : ∀ s ∈ Icc h₀ (2 * h₀ - α), 2 * h₀ - s ∈ Icc α h₀ := by
    intro s hs
    refine ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hW₁_cont : ContinuousOn W₁ (Icc h₀ (2 * h₀ - α)) := by
    apply ContinuousOn.comp hZ₁_cont (s := Icc h₀ (2 * h₀ - α))
      (t := Icc α h₀) (f := fun s => 2 * h₀ - s)
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact h_dom_swap
  have hW₂_cont : ContinuousOn W₂ (Icc h₀ (2 * h₀ - α)) := by
    apply ContinuousOn.comp hZ₂_cont (s := Icc h₀ (2 * h₀ - α))
      (t := Icc α h₀) (f := fun s => 2 * h₀ - s)
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact h_dom_swap
  have hW₁_deriv : ∀ s ∈ Icc h₀ (2 * h₀ - α), HasDerivAt W₁ (B₁ s (W₁ s)) s := by
    intro s hs
    have hd : HasDerivAt Z₁ (A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s))) (2 * h₀ - s) :=
      hZ₁_deriv (2 * h₀ - s) (h_dom_swap s hs)
    have h_chain : HasDerivAt (fun s => 2 * h₀ - s) (-1 : ℝ) s := by
      have h := (hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)
      have hfun : (fun _ : ℝ => 2 * h₀) - id = fun r => 2 * h₀ - r := by
        funext r
        rfl
      rw [hfun, zero_sub] at h
      exact h
    have hd' : HasDerivAt (Z₁ ∘ (fun s => 2 * h₀ - s))
        ((-1 : ℝ) • A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s))) s := hd.scomp s h_chain
    have hZ₁_eq : (Z₁ ∘ (fun s => 2 * h₀ - s)) = W₁ := rfl
    rw [hZ₁_eq] at hd'
    have hW₁s_eq : W₁ s = Z₁ (2 * h₀ - s) := rfl
    have hB₁s_eq : B₁ s = -A₁ (2 * h₀ - s) := rfl
    have h_eq : ((-1 : ℝ) • A₁ (2 * h₀ - s) (Z₁ (2 * h₀ - s)) : G) = B₁ s (W₁ s) := by
      rw [hB₁s_eq, hW₁s_eq, neg_apply, neg_one_smul]
    rw [h_eq] at hd'
    exact hd'
  have hW₂_deriv : ∀ s ∈ Icc h₀ (2 * h₀ - α), HasDerivAt W₂ (B₂ s (W₂ s)) s := by
    intro s hs
    have hd : HasDerivAt Z₂ (A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s))) (2 * h₀ - s) :=
      hZ₂_deriv (2 * h₀ - s) (h_dom_swap s hs)
    have h_chain : HasDerivAt (fun s => 2 * h₀ - s) (-1 : ℝ) s := by
      have h := (hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)
      have hfun : (fun _ : ℝ => 2 * h₀) - id = fun r => 2 * h₀ - r := by
        funext r
        rfl
      rw [hfun, zero_sub] at h
      exact h
    have hd' : HasDerivAt (Z₂ ∘ (fun s => 2 * h₀ - s))
        ((-1 : ℝ) • A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s))) s := hd.scomp s h_chain
    have hZ₂_eq : (Z₂ ∘ (fun s => 2 * h₀ - s)) = W₂ := rfl
    rw [hZ₂_eq] at hd'
    have hW₂s_eq : W₂ s = Z₂ (2 * h₀ - s) := rfl
    have hB₂s_eq : B₂ s = -A₂ (2 * h₀ - s) := rfl
    have h_eq : ((-1 : ℝ) • A₂ (2 * h₀ - s) (Z₂ (2 * h₀ - s)) : G) = B₂ s (W₂ s) := by
      rw [hB₂s_eq, hW₂s_eq, neg_apply, neg_one_smul]
    rw [h_eq] at hd'
    exact hd'
  have hB₁_bd : ∀ s ∈ Icc h₀ (2 * h₀ - α), ‖B₁ s‖ ≤ K := by
    intro s hs
    change ‖-A₁ (2 * h₀ - s)‖ ≤ K
    rw [norm_neg]
    exact hA₁_bd _ (h_dom_swap s hs)
  have hdiff_bd' : ∀ s ∈ Icc h₀ (2 * h₀ - α), ‖(B₂ s - B₁ s) (W₂ s)‖ ≤ η := by
    intro s hs
    have h_in : 2 * h₀ - s ∈ Icc α h₀ := h_dom_swap s hs
    have h_eq : B₂ s - B₁ s = -(A₂ (2 * h₀ - s) - A₁ (2 * h₀ - s)) := by
      change -A₂ (2 * h₀ - s) - (-A₁ (2 * h₀ - s)) =
        -(A₂ (2 * h₀ - s) - A₁ (2 * h₀ - s))
      abel
    rw [h_eq]
    have hW₂s : W₂ s = Z₂ (2 * h₀ - s) := rfl
    rw [hW₂s, neg_apply, norm_neg]
    exact hdiff_bd _ h_in
  have hres := linearODE_gronwall_forward (A₁ := B₁) (A₂ := B₂) (Z₁ := W₁) (Z₂ := W₂)
    (h₀ := h₀) (β := 2 * h₀ - α) (K := K) (η := η) hK_nn
    hW₁_cont hW₂_cont hW₁_deriv hW₂_deriv hB₁_bd hdiff_bd' (2 * h₀ - t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h_W_initial : ‖W₁ h₀ - W₂ h₀‖ = ‖Z₁ h₀ - Z₂ h₀‖ := by
    have hW₁h : W₁ h₀ = Z₁ h₀ := by
      change Z₁ (2 * h₀ - h₀) = Z₁ h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    have hW₂h : W₂ h₀ = Z₂ h₀ := by
      change Z₂ (2 * h₀ - h₀) = Z₂ h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    rw [hW₁h, hW₂h]
  have h_W_t : W₁ (2 * h₀ - t) - W₂ (2 * h₀ - t) = Z₁ t - Z₂ t := by
    change Z₁ (2 * h₀ - (2 * h₀ - t)) - Z₂ (2 * h₀ - (2 * h₀ - t)) = Z₁ t - Z₂ t
    have h_eq : 2 * h₀ - (2 * h₀ - t) = t := by ring
    rw [h_eq]
  have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
  rw [h_time, h_W_initial] at hres
  have h_lhs : ‖W₁ (2 * h₀ - t) - W₂ (2 * h₀ - t)‖ = ‖Z₁ t - Z₂ t‖ := by
    rw [h_W_t]
  rw [h_lhs] at hres
  exact hres

theorem linearODESolution_continuousOn
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (Function.uncurry (linearODESolution A a b h₀ Z₀))
      (U ×ˢ Set.Ioo a b) := by
  set Z : F → ℝ → G := linearODESolution A a b h₀ Z₀ with hZ_def
  have hZ_exists : ∀ x ∈ U, HasLinearODESolution A a b h₀ Z₀ x := fun x hx =>
    hasLinearODESolution_of_continuousOn h₀_mem hA_cont hx
  have hZ_deriv : ∀ x ∈ U, ∀ t ∈ Ioo a b, HasDerivAt (Z x) (A x t (Z x t)) t := by
    intro x hx t ht
    exact linearODESolution_hasDerivAt_of_hasSolution A a b h₀ Z₀ (hZ_exists x hx) ht
  have hZ_cont_t : ∀ x ∈ U, ContinuousOn (Z x) (Ioo a b) := by
    intro x hx t ht
    exact ((hZ_deriv x hx t ht).continuousAt).continuousWithinAt
  have hZ_initial : ∀ x, Z x h₀ = Z₀ x := fun x => linearODESolution_initial A a b h₀ Z₀ x
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b : Set (F × ℝ)) := hU.prod isOpen_Ioo
  refine IsOpen.continuousOn_iff hS_open |>.mpr ?_
  rintro ⟨x₀, t₀⟩ hp
  obtain ⟨hx₀U, ht₀⟩ := hp
  rw [Metric.continuousAt_iff]
  intro ε hε
  set α : ℝ := (a + min t₀ h₀) / 2 with hα_def
  set β : ℝ := (b + max t₀ h₀) / 2 with hβ_def
  have hα_lt_min : α < min t₀ h₀ := by
    rw [hα_def]
    have := lt_min ht₀.1 h₀_mem.1
    linarith
  have hα_lt_a : a < α := by
    rw [hα_def]
    have := lt_min ht₀.1 h₀_mem.1
    linarith
  have hmax_lt_β : max t₀ h₀ < β := by
    rw [hβ_def]
    have := max_lt ht₀.2 h₀_mem.2
    linarith
  have hβ_lt_b : β < b := by
    rw [hβ_def]
    have := max_lt ht₀.2 h₀_mem.2
    linarith
  have hα_le_t₀ : α ≤ t₀ := le_of_lt (lt_of_lt_of_le hα_lt_min (min_le_left _ _))
  have hα_le_h₀ : α ≤ h₀ := le_of_lt (lt_of_lt_of_le hα_lt_min (min_le_right _ _))
  have ht₀_le_β : t₀ ≤ β := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hmax_lt_β)
  have hh₀_le_β : h₀ ≤ β := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax_lt_β)
  have hα_le_β : α ≤ β := le_trans hα_le_h₀ hh₀_le_β
  have hIcc_sub_Ioo : Icc α β ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt_a hs.1, lt_of_le_of_lt hs.2 hβ_lt_b⟩
  have ht₀_mem_Icc : t₀ ∈ Icc α β := ⟨hα_le_t₀, ht₀_le_β⟩
  have hh₀_mem_Icc : h₀ ∈ Icc α β := ⟨hα_le_h₀, hh₀_le_β⟩
  have hIcc_compact : IsCompact (Icc α β) := isCompact_Icc
  obtain ⟨M, hM_nn, hM_x₀_bd⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc α β, ‖A x₀ s‖ ≤ M := by
    have hAx₀_cont : ContinuousOn (A x₀) (Icc α β) := by
      have hAx₀_uncurry : ContinuousOn (A x₀) (Ioo a b) :=
        ContinuousOn.uncurry_left x₀ hx₀U hA_cont
      exact hAx₀_uncurry.mono (fun s hs => hIcc_sub_Ioo hs)
    have hnorm_Ax₀ : ContinuousOn (fun s => ‖A x₀ s‖) (Icc α β) :=
      continuous_norm.comp_continuousOn hAx₀_cont
    have hne : (Icc α β).Nonempty := ⟨h₀, hh₀_mem_Icc⟩
    rcases hIcc_compact.exists_isMaxOn hne hnorm_Ax₀ with ⟨τ, _, hτ_max⟩
    exact ⟨‖A x₀ τ‖, norm_nonneg _, fun s hs => hτ_max hs⟩
  have hS_open' : IsOpen (U ×ˢ Set.Ioo a b : Set (F × ℝ)) := hS_open
  have h_open_set : IsOpen
      {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} := by
    set normA : F × ℝ → ℝ := fun p => ‖A p.1 p.2‖
    have hnormA_cont : ContinuousOn normA (U ×ˢ Set.Ioo a b) :=
      continuous_norm.comp_continuousOn hA_cont
    have hpre_open : IsOpen ((U ×ˢ Set.Ioo a b) ∩ normA ⁻¹' Set.Iio (M + 1)) :=
      hnormA_cont.isOpen_inter_preimage hS_open' isOpen_Iio
    have h_eq : {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} =
        (U ×ˢ Set.Ioo a b) ∩ normA ⁻¹' Set.Iio (M + 1) := by
      ext q
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [h_eq]
    exact hpre_open
  have h_slice_in_open : ({x₀} : Set F) ×ˢ Icc α β ⊆
      {q : F × ℝ | q.1 ∈ U ∧ q.2 ∈ Ioo a b ∧ ‖A q.1 q.2‖ < M + 1} := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Set.mem_singleton_iff] at hq1
    subst hq1
    refine ⟨hx₀U, hIcc_sub_Ioo hq2, ?_⟩
    exact lt_of_le_of_lt (hM_x₀_bd q.2 hq2) (by linarith)
  obtain ⟨W₀, V, hW₀_open, _hV_open, hx₀_W₀, hIcc_V, hWV_sub⟩ :=
    generalized_tube_lemma isCompact_singleton hIcc_compact h_open_set h_slice_in_open
  have hx₀_W₀' : x₀ ∈ W₀ := hx₀_W₀ (Set.mem_singleton x₀)
  set Wopen : Set F := W₀ ∩ U with hWopen_def
  have hWopen_open : IsOpen Wopen := hW₀_open.inter hU
  have hx₀_Wopen : x₀ ∈ Wopen := ⟨hx₀_W₀', hx₀U⟩
  have hWopen_sub_U : Wopen ⊆ U := fun x hx => hx.2
  have hMbd_W : ∀ x ∈ Wopen, ∀ s ∈ Icc α β, ‖A x s‖ ≤ M + 1 := by
    intro x hx s hs
    have hx_W₀ : x ∈ W₀ := hx.1
    have hs_V : s ∈ V := hIcc_V hs
    have hxs_sub : (x, s) ∈ W₀ ×ˢ V := ⟨hx_W₀, hs_V⟩
    have := hWV_sub hxs_sub
    exact le_of_lt this.2.2
  set K : ℝ := M + 1 with hK_def
  have hK_nn : 0 ≤ K := by rw [hK_def]; linarith
  have hZ_apriori : ∀ x ∈ Wopen, ∀ t ∈ Icc α β,
      ‖Z x t‖ ≤ ‖Z₀ x‖ * Real.exp (K * (β - α)) := by
    intro x hx t ht
    have hZxh₀_eq : Z x h₀ = Z₀ x := hZ_initial x
    have hZx_deriv_all : ∀ s ∈ Ioo a b, HasDerivAt (Z x) (A x s (Z x s)) s :=
      hZ_deriv x (hWopen_sub_U hx)
    have habs := portPrivate_c8c79eec_linearODE_apriori_bound (A := A x) (a := a) (b := b) (α := α) (β := β)
      (c := h₀) (M := K) hα_le_β hα_lt_a hβ_lt_b hh₀_mem_Icc hK_nn
      (fun s hs => hMbd_W x hx s hs) hZx_deriv_all t ht
    rw [hZxh₀_eq] at habs
    exact habs
  set T : ℝ := β - α with hT_def
  have hT_nn : 0 ≤ T := by rw [hT_def]; linarith
  have hgb_eq_zero : gronwallBound 0 K 0 T = 0 := by simp [gronwallBound_ε0_δ0]
  have hK_pos : 0 < K := by rw [hK_def]; linarith
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hgb_cont : Continuous (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) := by
    simp only [gronwallBound_of_K_ne_0 hK_ne]
    fun_prop
  have hgb_tendsto : Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T)
      (𝓝 (0, 0)) (𝓝 0) := by
    have := hgb_cont.continuousAt (x := (0, 0))
    rw [ContinuousAt, hgb_eq_zero] at this
    exact this
  rw [Metric.tendsto_nhds] at hgb_tendsto
  obtain ⟨ρ, hρ_pos, hρ_bd⟩ := Metric.mem_nhds_iff.mp (hgb_tendsto (ε / 2) (by linarith))
  set δ_target : ℝ := ρ / 2 with hδ_target_def
  set η_target : ℝ := ρ / 2 with hη_target_def
  have hδ_target_pos : 0 < δ_target := by rw [hδ_target_def]; linarith
  have hη_target_pos : 0 < η_target := by rw [hη_target_def]; linarith
  have hbd_gb : ∀ δ η : ℝ, 0 ≤ δ → 0 ≤ η → δ < δ_target → η < η_target →
      gronwallBound δ K η T < ε / 2 := by
    intro δ η hδ_nn hη_nn hδ_lt hη_lt
    have h_pair_mem : (δ, η) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) ρ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      have h1 : dist δ 0 < ρ := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg hδ_nn]
        exact lt_of_lt_of_le hδ_lt (by rw [hδ_target_def]; linarith)
      have h2 : dist η 0 < ρ := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg hη_nn]
        exact lt_of_lt_of_le hη_lt (by rw [hη_target_def]; linarith)
      exact max_lt h1 h2
    have hd := hρ_bd h_pair_mem
    simp only [Set.mem_ofPred_eq] at hd
    rw [Real.dist_0_eq_abs] at hd
    exact lt_of_le_of_lt (le_abs_self _) hd
  set R' : ℝ := (‖Z₀ x₀‖ + 1) * Real.exp (K * T) with hR'_def
  have hR'_pos : 0 < R' := by
    rw [hR'_def]
    apply mul_pos
    · linarith [norm_nonneg (Z₀ x₀)]
    · exact Real.exp_pos _
  set η_op : ℝ := η_target / (R' + 1) with hη_op_def
  have hη_op_pos : 0 < η_op := div_pos hη_target_pos (by linarith)
  set g : F × ℝ → ℝ := fun p => ‖A p.1 p.2 - A x₀ p.2‖
  have hg_cont : ContinuousOn g (U ×ˢ Set.Ioo a b) := by
    have h_swap : ContinuousOn (fun p : F × ℝ => A x₀ p.2) (U ×ˢ Set.Ioo a b) := by
      have h_A_x₀_cont : ContinuousOn (A x₀) (Ioo a b) :=
        ContinuousOn.uncurry_left x₀ hx₀U hA_cont
      exact h_A_x₀_cont.comp continuousOn_snd (fun _ hp => hp.2)
    have : ContinuousOn (fun p : F × ℝ => A p.1 p.2 - A x₀ p.2) (U ×ˢ Set.Ioo a b) :=
      hA_cont.sub h_swap
    exact continuous_norm.comp_continuousOn this
  have hg_x₀ : ∀ s, g (x₀, s) = 0 := fun s => by
    change ‖A x₀ s - A x₀ s‖ = 0
    rw [sub_self, norm_zero]
  have h_gopen : IsOpen
      {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} := by
    have hpre_open : IsOpen ((U ×ˢ Set.Ioo a b) ∩ g ⁻¹' Set.Iio η_op) :=
      hg_cont.isOpen_inter_preimage hS_open' isOpen_Iio
    have h_eq : {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} =
        (U ×ˢ Set.Ioo a b) ∩ g ⁻¹' Set.Iio η_op := by
      ext p; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [h_eq]
    exact hpre_open
  have h_slice_in_gopen : ({x₀} : Set F) ×ˢ Icc α β ⊆
      {p : F × ℝ | p.1 ∈ U ∧ p.2 ∈ Ioo a b ∧ g p < η_op} := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_singleton_iff] at hp1; subst hp1
    refine ⟨hx₀U, hIcc_sub_Ioo hp2, ?_⟩
    rw [hg_x₀]; exact hη_op_pos
  obtain ⟨W₁, V₁, hW₁_open, _hV₁_open, hx₀_W₁, hIccα_V₁, hW₁V₁_sub⟩ :=
    generalized_tube_lemma isCompact_singleton hIcc_compact h_gopen h_slice_in_gopen
  have hx₀_W₁' : x₀ ∈ W₁ := hx₀_W₁ (Set.mem_singleton x₀)
  have hZ₀_cont_at : ContinuousAt Z₀ x₀ := (hZ₀_cont x₀ hx₀U).continuousAt (hU.mem_nhds hx₀U)
  have hZ₀_diff_eps : ∀ᶠ x in 𝓝 x₀, ‖Z₀ x - Z₀ x₀‖ < δ_target := by
    have h_tendsto_diff : Tendsto (fun x => Z₀ x - Z₀ x₀) (𝓝 x₀) (𝓝 0) := by
      have h_tendsto : Tendsto Z₀ (𝓝 x₀) (𝓝 (Z₀ x₀)) := hZ₀_cont_at
      have := h_tendsto.sub (tendsto_const_nhds (x := Z₀ x₀))
      simpa using this
    rw [Metric.tendsto_nhds] at h_tendsto_diff
    have := h_tendsto_diff δ_target hδ_target_pos
    filter_upwards [this] with x hx
    have h_eq : dist (Z₀ x - Z₀ x₀) 0 = ‖Z₀ x - Z₀ x₀‖ := by
      rw [dist_zero_right]
    rwa [h_eq] at hx
  have hZ₀_norm_eps : ∀ᶠ x in 𝓝 x₀, ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 := by
    have h_norm_cont : ContinuousAt (fun x => ‖Z₀ x‖) x₀ :=
      continuous_norm.continuousAt.comp hZ₀_cont_at
    have h_one_pos : ‖Z₀ x₀‖ < ‖Z₀ x₀‖ + 1 := by linarith
    have h_open : IsOpen {y : ℝ | y < ‖Z₀ x₀‖ + 1} := isOpen_Iio
    have hmem : ‖Z₀ x₀‖ ∈ {y : ℝ | y < ‖Z₀ x₀‖ + 1} := h_one_pos
    exact h_norm_cont.preimage_mem_nhds (h_open.mem_nhds hmem)
  obtain ⟨W_diff, hZ₀_diff_in, hW_diff_open, hx₀_W_diff⟩ := _root_.mem_nhds_iff.mp hZ₀_diff_eps
  obtain ⟨W_norm, hZ₀_norm_in, hW_norm_open, hx₀_W_norm⟩ := _root_.mem_nhds_iff.mp hZ₀_norm_eps
  set Wparam : Set F := Wopen ∩ W₁ ∩ W_diff ∩ W_norm with hWparam_def
  have hWparam_open : IsOpen Wparam :=
    ((hWopen_open.inter hW₁_open).inter hW_diff_open).inter hW_norm_open
  have hx₀_Wparam : x₀ ∈ Wparam :=
    ⟨⟨⟨hx₀_Wopen, hx₀_W₁'⟩, hx₀_W_diff⟩, hx₀_W_norm⟩
  have hWparam_sub_Wopen : Wparam ⊆ Wopen := fun x hx => hx.1.1.1
  have hWparam_sub_U : Wparam ⊆ U := fun x hx => hWopen_sub_U (hWparam_sub_Wopen hx)
  have hWparam_diff_lt : ∀ x ∈ Wparam, ‖Z₀ x - Z₀ x₀‖ < δ_target :=
    fun x hx => hZ₀_diff_in hx.1.2
  have hWparam_norm_lt : ∀ x ∈ Wparam, ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 :=
    fun x hx => hZ₀_norm_in hx.2
  have hWparam_g_lt : ∀ x ∈ Wparam, ∀ s ∈ Icc α β, ‖A x s - A x₀ s‖ < η_op := by
    intro x hx s hs
    have hx_W₁ : x ∈ W₁ := hx.1.1.2
    have hs_V₁ : s ∈ V₁ := hIccα_V₁ hs
    have hxs_sub : (x, s) ∈ W₁ ×ˢ V₁ := ⟨hx_W₁, hs_V₁⟩
    exact (hW₁V₁_sub hxs_sub).2.2
  have hbd_diff : ∀ x ∈ Wparam, ∀ t ∈ Icc α β,
      ‖Z x t - Z x₀ t‖ ≤ gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target |t - h₀| := by
    intro x hx t ht
    have hxU : x ∈ U := hWparam_sub_U hx
    have h_Zxs_bd : ∀ s ∈ Icc α β, ‖Z x s‖ ≤ R' := by
      intro s hs
      have hZx_apr := hZ_apriori x (hWparam_sub_Wopen hx) s hs
      have hZ₀x_lt : ‖Z₀ x‖ < ‖Z₀ x₀‖ + 1 := hWparam_norm_lt x hx
      have hexp_pos : 0 < Real.exp (K * T) := Real.exp_pos _
      have h_bound : ‖Z₀ x‖ * Real.exp (K * T) ≤ (‖Z₀ x₀‖ + 1) * Real.exp (K * T) :=
        mul_le_mul_of_nonneg_right hZ₀x_lt.le hexp_pos.le
      exact le_trans hZx_apr h_bound
    have hAx_bd : ∀ s ∈ Icc α β, ‖A x s‖ ≤ K :=
      fun s hs => hMbd_W x (hWparam_sub_Wopen hx) s hs
    have hAx₀_bd : ∀ s ∈ Icc α β, ‖A x₀ s‖ ≤ K :=
      fun s hs => le_trans (hM_x₀_bd s hs) (by linarith)
    have hZx_cont : ContinuousOn (Z x) (Icc α β) := by
      intro s hs; exact (hZ_cont_t x hxU s (hIcc_sub_Ioo hs)).mono (fun u hu => hIcc_sub_Ioo hu)
    have hZx₀_cont : ContinuousOn (Z x₀) (Icc α β) := by
      intro s hs; exact (hZ_cont_t x₀ hx₀U s (hIcc_sub_Ioo hs)).mono (fun u hu => hIcc_sub_Ioo hu)
    have hZx_deriv_Icc : ∀ s ∈ Icc α β, HasDerivAt (Z x) (A x s (Z x s)) s :=
      fun s hs => hZ_deriv x hxU s (hIcc_sub_Ioo hs)
    have hZx₀_deriv_Icc : ∀ s ∈ Icc α β, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
      fun s hs => hZ_deriv x₀ hx₀U s (hIcc_sub_Ioo hs)
    have hdiff_bd_full : ∀ s ∈ Icc α β, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target := by
      intro s hs
      have h1 : ‖(A x s - A x₀ s) (Z x s)‖ ≤ ‖A x s - A x₀ s‖ * ‖Z x s‖ :=
        (A x s - A x₀ s).le_opNorm _
      have h2 : ‖A x s - A x₀ s‖ * ‖Z x s‖ ≤ η_op * R' := by
        have hop_lt : ‖A x s - A x₀ s‖ < η_op := hWparam_g_lt x hx s hs
        have hZ_lt : ‖Z x s‖ ≤ R' := h_Zxs_bd s hs
        have h_nn_Z : 0 ≤ ‖Z x s‖ := norm_nonneg _
        have h_op_nn : 0 ≤ ‖A x s - A x₀ s‖ := norm_nonneg _
        have h_η_op_nn : 0 ≤ η_op := le_of_lt hη_op_pos
        have h_R'_nn : 0 ≤ R' := le_of_lt hR'_pos
        calc ‖A x s - A x₀ s‖ * ‖Z x s‖
            ≤ η_op * ‖Z x s‖ := mul_le_mul_of_nonneg_right hop_lt.le h_nn_Z
          _ ≤ η_op * R' := mul_le_mul_of_nonneg_left hZ_lt h_η_op_nn
      have h3 : η_op * R' ≤ η_target := by
        rw [hη_op_def]
        rw [div_mul_eq_mul_div, mul_comm]
        rw [div_le_iff₀ (by linarith)]
        have hR'_nn : 0 ≤ R' := le_of_lt hR'_pos
        have h_η_t_nn : 0 ≤ η_target := le_of_lt hη_target_pos
        have h_le : R' ≤ R' + 1 := by linarith
        calc R' * η_target ≤ (R' + 1) * η_target :=
              mul_le_mul_of_nonneg_right h_le h_η_t_nn
          _ = η_target * (R' + 1) := by ring
      linarith
    rcases le_total h₀ t with hht | hth
    · have hh₀_le_t : h₀ ≤ t := hht
      have hZ₁_cont_ht : ContinuousOn (Z x₀) (Icc h₀ β) := by
        intro s hs
        exact (hZx₀_cont s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩).mono
          (fun u hu => ⟨le_trans hα_le_h₀ hu.1, hu.2⟩)
      have hZ₂_cont_ht : ContinuousOn (Z x) (Icc h₀ β) := by
        intro s hs
        exact (hZx_cont s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩).mono
          (fun u hu => ⟨le_trans hα_le_h₀ hu.1, hu.2⟩)
      have hZ₁_deriv_ht : ∀ s ∈ Icc h₀ β, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
        fun s hs => hZx₀_deriv_Icc s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hZ₂_deriv_ht : ∀ s ∈ Icc h₀ β, HasDerivAt (Z x) (A x s (Z x s)) s :=
        fun s hs => hZx_deriv_Icc s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hAx₀_bd_ht : ∀ s ∈ Icc h₀ β, ‖A x₀ s‖ ≤ K :=
        fun s hs => hAx₀_bd s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hdiff_bd_ht : ∀ s ∈ Icc h₀ β, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target :=
        fun s hs => hdiff_bd_full s ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
      have hres := linearODE_gronwall_forward (A₁ := A x₀) (A₂ := A x) (Z₁ := Z x₀) (Z₂ := Z x)
        hK_nn hZ₁_cont_ht hZ₂_cont_ht hZ₁_deriv_ht hZ₂_deriv_ht
        hAx₀_bd_ht hdiff_bd_ht t ⟨hh₀_le_t, ht.2⟩
      have h_initial_eq : ‖Z x₀ h₀ - Z x h₀‖ = ‖Z₀ x - Z₀ x₀‖ := by
        rw [hZ_initial x, hZ_initial x₀]
        rw [← norm_neg]; congr 1; abel
      rw [h_initial_eq] at hres
      have h_lhs_eq : ‖Z x t - Z x₀ t‖ = ‖Z x₀ t - Z x t‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [h_lhs_eq]
      have h_abs : |t - h₀| = t - h₀ := abs_of_nonneg (by linarith)
      rw [h_abs]
      exact hres
    · have ht_le_h₀ : t ≤ h₀ := hth
      have hZ₁_cont_th : ContinuousOn (Z x₀) (Icc α h₀) := by
        intro s hs
        exact (hZx₀_cont s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩).mono
          (fun u hu => ⟨hu.1, le_trans hu.2 hh₀_le_β⟩)
      have hZ₂_cont_th : ContinuousOn (Z x) (Icc α h₀) := by
        intro s hs
        exact (hZx_cont s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩).mono
          (fun u hu => ⟨hu.1, le_trans hu.2 hh₀_le_β⟩)
      have hZ₁_deriv_th : ∀ s ∈ Icc α h₀, HasDerivAt (Z x₀) (A x₀ s (Z x₀ s)) s :=
        fun s hs => hZx₀_deriv_Icc s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hZ₂_deriv_th : ∀ s ∈ Icc α h₀, HasDerivAt (Z x) (A x s (Z x s)) s :=
        fun s hs => hZx_deriv_Icc s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hAx₀_bd_th : ∀ s ∈ Icc α h₀, ‖A x₀ s‖ ≤ K :=
        fun s hs => hAx₀_bd s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hdiff_bd_th : ∀ s ∈ Icc α h₀, ‖(A x s - A x₀ s) (Z x s)‖ ≤ η_target :=
        fun s hs => hdiff_bd_full s ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
      have hres := linearODE_gronwall_backward (A₁ := A x₀) (A₂ := A x) (Z₁ := Z x₀) (Z₂ := Z x)
        hα_le_h₀ hK_nn hZ₁_cont_th hZ₂_cont_th hZ₁_deriv_th hZ₂_deriv_th
        hAx₀_bd_th hdiff_bd_th t ⟨ht.1, ht_le_h₀⟩
      have h_initial_eq : ‖Z x₀ h₀ - Z x h₀‖ = ‖Z₀ x - Z₀ x₀‖ := by
        rw [hZ_initial x, hZ_initial x₀]
        rw [← norm_neg]; congr 1; abel
      rw [h_initial_eq] at hres
      have h_lhs_eq : ‖Z x t - Z x₀ t‖ = ‖Z x₀ t - Z x t‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [h_lhs_eq]
      have h_abs : |t - h₀| = h₀ - t := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [h_abs]
      exact hres
  have hZx₀_cont_Ioo : ContinuousOn (Z x₀) (Ioo a b) := hZ_cont_t x₀ hx₀U
  have hZx₀_cont_at : ContinuousAt (Z x₀) t₀ :=
    (hZx₀_cont_Ioo t₀ ht₀).continuousAt (isOpen_Ioo.mem_nhds ht₀)
  have hZx₀_tendsto : Tendsto (Z x₀) (𝓝 t₀) (𝓝 (Z x₀ t₀)) := hZx₀_cont_at
  rw [Metric.tendsto_nhds] at hZx₀_tendsto
  obtain ⟨δ_t, hδ_t_pos, hδ_t_bd⟩ :=
    Metric.mem_nhds_iff.mp (hZx₀_tendsto (ε / 2) (by linarith))
  obtain ⟨ρ_param, hρ_param_pos, hρ_param_sub⟩ :=
    Metric.isOpen_iff.mp hWparam_open x₀ hx₀_Wparam
  set δ_time : ℝ := min δ_t (min (β - t₀) (t₀ - α)) with hδ_time_def
  have hδ_time_pos : 0 < δ_time := by
    rw [hδ_time_def]
    refine lt_min hδ_t_pos (lt_min ?_ ?_)
    · linarith [lt_of_le_of_lt (le_max_left _ _) hmax_lt_β]
    · linarith [lt_of_lt_of_le hα_lt_min (min_le_left _ _)]
  set δ_final : ℝ := min ρ_param δ_time with hδ_final_def
  have hδ_final_pos : 0 < δ_final :=
    lt_min hρ_param_pos hδ_time_pos
  use δ_final
  refine ⟨hδ_final_pos, ?_⟩
  intro p hp
  obtain ⟨x, t⟩ := p
  rw [Prod.dist_eq] at hp
  have hdx : dist x x₀ < δ_final := lt_of_le_of_lt (le_max_left _ _) hp
  have hdt : dist t t₀ < δ_final := lt_of_le_of_lt (le_max_right _ _) hp
  have hx_param : x ∈ Wparam := hρ_param_sub
    (Metric.mem_ball.mpr (lt_of_lt_of_le hdx (min_le_left _ _)))
  have hdt_t : dist t t₀ < δ_t :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdt_β : dist t t₀ < β - t₀ :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdt_α : dist t t₀ < t₀ - α :=
    lt_of_lt_of_le hdt (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have ht_Icc : t ∈ Icc α β := by
    rw [Real.dist_eq] at hdt_β hdt_α
    refine ⟨?_, ?_⟩
    · have := abs_lt.mp hdt_α
      linarith [this.1]
    · have := abs_lt.mp hdt_β
      linarith [this.2]
  have h_triangle : ‖Z x t - Z x₀ t₀‖ ≤ ‖Z x t - Z x₀ t‖ + ‖Z x₀ t - Z x₀ t₀‖ := by
    have h_eq : Z x t - Z x₀ t₀ = (Z x t - Z x₀ t) + (Z x₀ t - Z x₀ t₀) := by abel
    rw [h_eq]
    exact norm_add_le _ _
  have h_t_piece : ‖Z x₀ t - Z x₀ t₀‖ < ε / 2 := by
    have hd := hδ_t_bd (Metric.mem_ball.mpr hdt_t)
    simp only [Set.mem_ofPred_eq] at hd
    rw [dist_eq_norm] at hd
    exact hd
  have hbd := hbd_diff x hx_param t ht_Icc
  have h_initial_bd : ‖Z₀ x - Z₀ x₀‖ < δ_target := hWparam_diff_lt x hx_param
  have h_t_h0_le_T : |t - h₀| ≤ T := by
    rw [hT_def]
    rcases le_total h₀ t with hht | hth
    · rw [abs_of_nonneg (by linarith)]; linarith [ht_Icc.2, hh₀_mem_Icc.1]
    · rw [abs_of_nonpos (by linarith)]; linarith [ht_Icc.1, hh₀_mem_Icc.2]
  have h_t_h0_nn : 0 ≤ |t - h₀| := abs_nonneg _
  have h_initial_nn : 0 ≤ ‖Z₀ x - Z₀ x₀‖ := norm_nonneg _
  have h_eta_nn : 0 ≤ η_target := le_of_lt hη_target_pos
  have h_gb_mono := gronwallBound_mono h_initial_nn h_eta_nn hK_nn h_t_h0_le_T
  have hbd' : ‖Z x t - Z x₀ t‖ ≤ gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T :=
    le_trans hbd h_gb_mono
  have h_param_piece : ‖Z x t - Z x₀ t‖ < ε / 2 := by
    have h_gb_lt : gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T < ε / 2 := by
      have h_gb_mono_eps : gronwallBound ‖Z₀ x - Z₀ x₀‖ K η_target T ≤
          gronwallBound δ_target K η_target T := by
        simp only [gronwallBound_of_K_ne_0 hK_ne]
        have h_exp_pos : 0 < Real.exp (K * T) := Real.exp_pos _
        have h_initial_le : ‖Z₀ x - Z₀ x₀‖ ≤ δ_target := le_of_lt h_initial_bd
        have h_mul_le : ‖Z₀ x - Z₀ x₀‖ * Real.exp (K * T) ≤ δ_target * Real.exp (K * T) :=
          mul_le_mul_of_nonneg_right h_initial_le h_exp_pos.le
        linarith
      have h_inner_lt : gronwallBound δ_target K η_target T < ε / 2 := by
        have h_pair_in_ball : (δ_target, η_target) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) ρ := by
          rw [Metric.mem_ball, Prod.dist_eq]
          have h1 : dist δ_target 0 < ρ := by
            rw [Real.dist_0_eq_abs, abs_of_nonneg (le_of_lt hδ_target_pos)]
            rw [hδ_target_def]; linarith
          have h2 : dist η_target 0 < ρ := by
            rw [Real.dist_0_eq_abs, abs_of_nonneg (le_of_lt hη_target_pos)]
            rw [hη_target_def]; linarith
          exact max_lt h1 h2
        have hd := hρ_bd h_pair_in_ball
        simp only [Set.mem_ofPred_eq] at hd
        rw [Real.dist_0_eq_abs] at hd
        exact lt_of_le_of_lt (le_abs_self _) hd
      exact lt_of_le_of_lt h_gb_mono_eps h_inner_lt
    exact lt_of_le_of_lt hbd' h_gb_lt
  have h_dist_eq : dist (Z x t) (Z x₀ t₀) = ‖Z x t - Z x₀ t₀‖ := dist_eq_norm _ _
  change dist (Z x t) (Z x₀ t₀) < ε
  rw [h_dist_eq]
  calc ‖Z x t - Z x₀ t₀‖
      ≤ ‖Z x t - Z x₀ t‖ + ‖Z x₀ t - Z x₀ t₀‖ := h_triangle
    _ < ε / 2 + ε / 2 := add_lt_add h_param_piece h_t_piece
    _ = ε := by ring

end JointContinuity

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
