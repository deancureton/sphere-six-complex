module

public import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.VariationalSolutionOperator
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal Uniformity

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section GronwallBoundEstimate

lemma gronwallBound_zero_le {K ε x : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * exp (K * x) := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have h_unfold : gronwallBound 0 K ε x = ε / K * (exp (K * x) - 1) := by
    rw [gronwallBound_of_K_ne_0 hKne]
    change 0 * exp (K * x) + ε / K * (exp (K * x) - 1) = ε / K * (exp (K * x) - 1)
    ring
  rw [h_unfold]
  set y := K * x with hy_def
  have hy_nn : 0 ≤ y := mul_nonneg (le_of_lt hK) hx
  have h_exp_bound : exp y - 1 ≤ y * exp y := by
    rcases eq_or_lt_of_le hy_nn with hy_zero | hy_pos
    · rw [← hy_zero]; simp
    · have h_int : ∫ s in (0 : ℝ)..y, exp s = exp y - 1 := by
        rw [integral_exp, exp_zero]
      have hint_bd : ∫ s in (0 : ℝ)..y, exp s ≤ ∫ _ in (0 : ℝ)..y, exp y := by
        apply intervalIntegral.integral_mono_on hy_nn
        · exact Continuous.intervalIntegrable Real.continuous_exp 0 y
        · exact intervalIntegrable_const
        · intro s hs; exact Real.exp_le_exp.mpr hs.2
      rw [intervalIntegral.integral_const, sub_zero] at hint_bd
      have hsmul : (y : ℝ) • (exp y : ℝ) = y * exp y := rfl
      rw [hsmul] at hint_bd
      linarith [h_int, hint_bd]
  have hεK_nn : 0 ≤ ε / K := div_nonneg hε (le_of_lt hK)
  have h_step : ε / K * (exp y - 1) ≤ ε / K * (y * exp y) :=
    mul_le_mul_of_nonneg_left h_exp_bound hεK_nn
  have h_simplify : ε / K * (y * exp y) = ε * x * exp y := by
    rw [hy_def]; field_simp
  linarith

end GronwallBoundEstimate

section ResidualEstimate

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
lemma norm_residual_le_of_diffOn
    (t : ℝ) (x v : E) {S : Set E} (hS : Convex ℝ S)
    (hf_diff : ∀ z ∈ S, DifferentiableAt ℝ (f t) z)
    (hx : x ∈ S) (hxv : x + v ∈ S)
    {C : ℝ}
    (hC : ∀ z ∈ S, ‖fderiv ℝ (f t) z - fderiv ℝ (f t) x‖ ≤ C) :
    ‖f t (x + v) - f t x - (fderiv ℝ (f t) x) v‖ ≤ C * ‖v‖ := by
  have hCalc :
      ‖f t (x + v) - f t x - (fderiv ℝ (f t) x) ((x + v) - x)‖ ≤ C * ‖(x + v) - x‖ := by
    refine hS.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f t) (f' := fun z => fderiv ℝ (f t) z) (φ := fderiv ℝ (f t) x) ?_ ?_ hx hxv
    · intro z hz
      exact ((hf_diff z hz).hasFDerivAt).hasFDerivWithinAt
    · intro z hz
      exact hC z hz
  simpa using hCalc

end ResidualEstimate

section UniformPartial

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
lemma exists_uniform_partial_fderiv_of_contDiffOn_univ
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {a b : ℝ} (α : ℝ → E) (hα : ContinuousOn α (Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc a b, ∀ z : E, ‖z - α τ‖ < δ →
      ‖fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)‖ < ε := by
  set K_graph : Set (ℝ × E) := (fun τ : ℝ => (τ, α τ)) '' Icc a b with hK_graph_def
  have hK_graph_compact : IsCompact K_graph := by
    apply IsCompact.image_of_continuousOn isCompact_Icc
    exact continuousOn_id.prodMk hα
  set F : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2 with hF_def
  have hF_cont : Continuous F := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rw [Set.univ_prod_univ] at h
    exact continuousOn_univ.mp h
  have hF_contAt : ∀ p ∈ K_graph, ContinuousAt F p :=
    fun p _ => hF_cont.continuousAt
  have hr_uniform : { x : (E →L[ℝ] E) × (E →L[ℝ] E) | dist x.1 x.2 < ε } ∈ 𝓤 (E →L[ℝ] E) :=
    Metric.dist_mem_uniformity hε
  have h := hK_graph_compact.uniformContinuousAt_of_continuousAt F hF_contAt hr_uniform
  rcases Metric.mem_uniformity_dist.mp h with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro τ hτ z hz
  set p₁ : ℝ × E := (τ, α τ)
  set p₂ : ℝ × E := (τ, z)
  have hp₁_K : p₁ ∈ K_graph := ⟨τ, hτ, rfl⟩
  have h_dist : dist p₁ p₂ < δ := by
    rw [Prod.dist_eq]
    have h1 : dist τ τ = 0 := dist_self _
    rw [h1]
    have h2 : max 0 (dist (α τ) z) = dist (α τ) z := by
      apply max_eq_right
      exact dist_nonneg
    rw [h2]
    rw [dist_comm, dist_eq_norm]
    exact hz
  have hdistF := hδ h_dist hp₁_K
  change dist (F p₁) (F p₂) < ε at hdistF
  rw [dist_eq_norm] at hdistF
  change ‖fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)‖ < ε
  have h_neg :
      fderiv ℝ (f τ) z - fderiv ℝ (f τ) (α τ)
        = -(fderiv ℝ (f τ) (α τ) - fderiv ℝ (f τ) z) := by abel
  rw [h_neg, norm_neg]
  exact hdistF

end UniformPartial

section MainTheorem

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}


theorem hasFDerivAt_flow_at_initial_of_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hA_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩)‖ ≤ M)
    (hr : 0 < r)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    HasFDerivAt (fun x => Φ ⟨x, t⟩)
      (variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
        hT hM hMT
        ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x₀
          (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr)))).mono hsub)
        hA_bd ht) x₀ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx₀_in_ball : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self (le_of_lt hr')
  set hA_cont :=
    (hΦ.continuousOn_fderiv_along_orbit hf_C1 x₀ hx₀_in_ball).mono hsub with hA_cont_def
  set A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ (f s) (Φ ⟨x₀, s⟩) with hA_def
  set vSolution := variationalSolutionFun (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd with hvSolution_def
  set Lmap := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x₀, s⟩) (t₀ := t₀)
    hT hM hMT hA_cont hA_bd ht with hLmap_def
  obtain ⟨L, hL_lip⟩ := hΦ.exists_lipschitz
  have hL_nn : (0 : ℝ) ≤ L := L.coe_nonneg
  have hΦ_lip_diff : ∀ s ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r,
      ‖Φ ⟨x, s⟩ - Φ ⟨x₀, s⟩‖ ≤ L * ‖x - x₀‖ := by
    intro s hs x hx
    have := (hL_lip s hs).dist_le_mul x hx x₀ hx₀_in_ball
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this
  have horbit_cont' : ContinuousOn (fun s : ℝ => Φ ⟨x₀, s⟩) (Icc (t₀ - T) (t₀ + T)) :=
    (hΦ.orbit_continuousOn x₀ hx₀_in_ball).mono hsub
  obtain ⟨δ_K, hδ_K_pos, hδ_K⟩ :=
    exists_uniform_partial_fderiv_of_contDiffOn_univ hf_C1
      (α := fun s => Φ ⟨x₀, s⟩) horbit_cont' 1 one_pos
  set δ_K_strict : ℝ := δ_K / 2 with hδ_K_strict_def
  have hδ_K_strict_pos : 0 < δ_K_strict := by positivity
  have hδ_K_strict_lt : δ_K_strict < δ_K := by linarith
  have hK_bd : ∀ τ ∈ Icc (t₀ - T) (t₀ + T), ∀ z : E, ‖z - Φ ⟨x₀, τ⟩‖ ≤ δ_K_strict →
      ‖fderiv ℝ (f τ) z‖ ≤ M + 1 := by
    intro τ hτ z hz
    have h_diff := hδ_K τ hτ z (lt_of_le_of_lt hz hδ_K_strict_lt)
    have hnorm_add := norm_add_le (fderiv ℝ (f τ) z - fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩))
      (fderiv ℝ (f τ) (Φ ⟨x₀, τ⟩))
    simp at hnorm_add
    linarith [hA_bd τ hτ, h_diff]
  set K_lip : ℝ := M + 1 with hK_lip_def
  have hK_lip_pos : 0 < K_lip := by have : (0 : ℝ) ≤ M := hM; linarith
  have hK_lip_nn : 0 ≤ K_lip := le_of_lt hK_lip_pos
  have hf_diff_pt : ∀ τ : ℝ, ∀ z : E, DifferentiableAt ℝ (f τ) z := by
    intro τ z
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (τ, z) :=
      (hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (τ, y)) z :=
      (differentiableAt_const τ).prodMk differentiableAt_id
    have hcomp : DifferentiableAt ℝ ((uncurry f) ∘ (fun y : E => (τ, y))) z :=
      hDiff_joint.comp z hg
    exact hcomp
  have hf_lip_ball : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ)
        (closedBall (Φ ⟨x₀, τ⟩) δ_K_strict) := by
    intro τ hτ
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => hf_diff_pt τ z) ?_
      (convex_closedBall _ _)
    intro z hz
    have h_norm_le : ‖z - Φ ⟨x₀, τ⟩‖ ≤ δ_K_strict := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this; exact this
    change ‖fderiv ℝ (f τ) z‖₊ ≤ (⟨K_lip, hK_lip_nn⟩ : NNReal)
    exact NNReal.coe_le_coe.mp (hK_bd τ hτ z h_norm_le)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set CE := exp (M * T) with hCE_def
  have hCE_pos : 0 < CE := exp_pos _
  have hCE_nn : 0 ≤ CE := le_of_lt hCE_pos
  set GfactorR : ℝ := T * exp (K_lip * T) with hGfactorR_def
  have hGfactorR_pos : 0 < GfactorR := by
    have : 0 < exp (K_lip * T) := exp_pos _
    have hT_pos : 0 < T := hT
    positivity
  set Cmul : ℝ := GfactorR * CE + 1 with hCmul_def
  have hCmul_pos : 0 < Cmul := by
    have : 0 ≤ GfactorR * CE := mul_nonneg (le_of_lt hGfactorR_pos) hCE_nn
    linarith
  set ε_target : ℝ := c / Cmul with hε_target_def
  have hε_target_pos : 0 < ε_target := div_pos hc hCmul_pos
  have hε_target_le_one : ε_target * GfactorR * CE < c := by
    have h1 : ε_target * Cmul = c := by
      rw [hε_target_def]; field_simp
    have h2 : ε_target * GfactorR * CE = ε_target * (GfactorR * CE) := by ring
    have h3 : ε_target * (GfactorR * CE) < ε_target * Cmul := by
      apply mul_lt_mul_of_pos_left _ hε_target_pos
      rw [hCmul_def]; linarith
    linarith
  obtain ⟨δ_uc, hδ_uc_pos, hδ_uc⟩ :=
    exists_uniform_partial_fderiv_of_contDiffOn_univ hf_C1
      (α := fun s => Φ ⟨x₀, s⟩) horbit_cont' ε_target hε_target_pos
  set Lpos : ℝ := L + 1 with hLpos_def
  have hLpos_pos : 0 < Lpos := by linarith
  set CEpos : ℝ := CE + 1 with hCEpos_def
  have hCEpos_pos : 0 < CEpos := by linarith
  set δ_final : ℝ :=
    min (min (r : ℝ) (δ_K_strict / Lpos))
        (min (δ_K_strict / CEpos) (δ_uc / CEpos)) with hδ_final_def
  have hδ_final_pos : 0 < δ_final := by
    refine lt_min (lt_min hr' ?_) (lt_min ?_ ?_)
    · exact div_pos hδ_K_strict_pos hLpos_pos
    · exact div_pos hδ_K_strict_pos hCEpos_pos
    · exact div_pos hδ_uc_pos hCEpos_pos
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : E) δ_final, Metric.ball_mem_nhds _ hδ_final_pos, fun h hh => ?_⟩
  rw [mem_ball_zero_iff] at hh
  have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
  have hh_lt_r : ‖h‖ < (r : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_left _ _)) (min_le_left _ _)
  have hh_le_r : ‖h‖ ≤ (r : ℝ) := le_of_lt hh_lt_r
  have hxh_mem_ball : x₀ + h ∈ closedBall x₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh_le_r
  have mk_bd : ∀ {coef target scale : ℝ}, 0 ≤ coef → coef ≤ scale → 0 < scale →
      ‖h‖ < target / scale → coef * ‖h‖ < target := by
    intros coef target scale hcoef_nn hcoef_le hscale_pos hbd
    have h1 : coef * ‖h‖ ≤ scale * ‖h‖ := mul_le_mul_of_nonneg_right hcoef_le hh_nn
    have h2 : scale * ‖h‖ < scale * (target / scale) := mul_lt_mul_of_pos_left hbd hscale_pos
    have h3 : scale * (target / scale) = target := by
      field_simp
    linarith
  have h_L_le_Lpos : L ≤ Lpos := by rw [hLpos_def]; linarith
  have h_CE_le_CEpos : CE ≤ CEpos := by rw [hCEpos_def]; linarith
  have hh_L_bd : L * ‖h‖ < δ_K_strict :=
    mk_bd hL_nn h_L_le_Lpos hLpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_left _ _)) (min_le_right _ _))
  have hh_L_bd_le : L * ‖h‖ ≤ δ_K_strict := le_of_lt hh_L_bd
  have hh_CE_bd : CE * ‖h‖ < δ_K_strict :=
    mk_bd hCE_nn h_CE_le_CEpos hCEpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_right _ _)) (min_le_left _ _))
  have hh_CE_bd_le : CE * ‖h‖ ≤ δ_K_strict := le_of_lt hh_CE_bd
  have hh_CE_lt_δuc : CE * ‖h‖ < δ_uc :=
    mk_bd hCE_nn h_CE_le_CEpos hCEpos_pos
      (lt_of_lt_of_le (lt_of_lt_of_le hh (min_le_right _ _)) (min_le_right _ _))
  set y_h : ℝ → E := vSolution h with hy_h_def
  have hy_h_solution :
      IsVariationalSolutionOn f (fun s => Φ ⟨x₀, s⟩) h t₀ y_h (Icc (t₀ - T) (t₀ + T)) :=
    variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd h
  have hy_h_initial : y_h t₀ = h := hy_h_solution.1
  have hy_h_bd : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖y_h s‖ ≤ CE * ‖h‖ := by
    intro s hs
    exact variationalSolutionFun_norm_le hT hM hMT hA_cont hA_bd h hs
  have hy_h_cont : ContinuousOn y_h (Icc (t₀ - T) (t₀ + T)) := hy_h_solution.continuousOn
  set α_h : ℝ → E := fun s => Φ ⟨x₀ + h, s⟩ with hα_h_def
  set β_h : ℝ → E := fun s => Φ ⟨x₀, s⟩ + y_h s with hβ_h_def
  have hα_h_initial : α_h t₀ = x₀ + h := hΦ.apply_initial (x₀ + h) hxh_mem_ball
  have hβ_h_initial : β_h t₀ = x₀ + h := by
    change Φ ⟨x₀, t₀⟩ + y_h t₀ = x₀ + h
    rw [hΦ.apply_initial x₀ hx₀_in_ball, hy_h_initial]
  have hα_h_deriv_full : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt α_h (f s (α_h s)) (Icc tmin tmax) s :=
    fun s hs => hΦ.hasDerivWithinAt (x₀ + h) hxh_mem_ball s hs
  have hα_h_cont : ContinuousOn α_h (Icc tmin tmax) :=
    hΦ.orbit_continuousOn (x₀ + h) hxh_mem_ball
  have hα_h_cont' : ContinuousOn α_h (Icc (t₀ - T) (t₀ + T)) := hα_h_cont.mono hsub
  have hΦc_deriv_full : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun s => Φ ⟨x₀, s⟩) (f s (Φ ⟨x₀, s⟩)) (Icc tmin tmax) s :=
    fun s hs => hΦ.hasDerivWithinAt x₀ hx₀_in_ball s hs
  have hα_h_close : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      ‖α_h s - Φ ⟨x₀, s⟩‖ ≤ L * ‖h‖ := by
    intro s hs
    have hs' : s ∈ Icc tmin tmax := hsub hs
    have h1 : ‖α_h s - Φ ⟨x₀, s⟩‖ ≤ L * ‖(x₀ + h) - x₀‖ :=
      hΦ_lip_diff s hs' (x₀ + h) hxh_mem_ball
    have h2 : (x₀ + h) - x₀ = h := by abel
    rw [h2] at h1; exact h1
  have hα_h_mem_ball : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      α_h s ∈ closedBall (Φ ⟨x₀, s⟩) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans (hα_h_close s hs) hh_L_bd_le
  have hβ_h_mem_ball : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      β_h s ∈ closedBall (Φ ⟨x₀, s⟩) δ_K_strict := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    change ‖Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩‖ ≤ δ_K_strict
    have heq : Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩ = y_h s := by abel
    rw [heq]; exact le_trans (hy_h_bd s hs) hh_CE_bd_le
  have hβ_h_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt β_h (f s (Φ ⟨x₀, s⟩) + A s (y_h s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have hs' : s ∈ Icc tmin tmax := hsub hs
    have h1 := (hΦc_deriv_full s hs').mono hsub
    have h2 := hy_h_solution.2 s hs
    exact h1.add h2
  have hβ_h_cont : ContinuousOn β_h (Icc (t₀ - T) (t₀ + T)) := by
    apply ContinuousOn.add (horbit_cont') hy_h_cont
  have h_residual_bound : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      ‖f s (Φ ⟨x₀, s⟩) + A s (y_h s) - f s (β_h s)‖ ≤ ε_target * ‖y_h s‖ := by
    intro s hs
    set ρ_segment : ℝ := CE * ‖h‖ with hρ_segment_def
    have hρ_segment_nn : 0 ≤ ρ_segment := mul_nonneg hCE_nn hh_nn
    set S_segment : Set E := closedBall (Φ ⟨x₀, s⟩) ρ_segment with hS_segment_def
    have hS_segment_convergence : Convex ℝ S_segment := convex_closedBall _ _
    have hf_diff : ∀ z ∈ S_segment, DifferentiableAt ℝ (f s) z := fun z _ => hf_diff_pt s z
    have hx_segment : Φ ⟨x₀, s⟩ ∈ S_segment := Metric.mem_closedBall_self hρ_segment_nn
    have hxv_segment : Φ ⟨x₀, s⟩ + y_h s ∈ S_segment := by
      rw [hS_segment_def, mem_closedBall, dist_eq_norm]
      change ‖Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩‖ ≤ ρ_segment
      have heq : Φ ⟨x₀, s⟩ + y_h s - Φ ⟨x₀, s⟩ = y_h s := by abel
      rw [heq, hρ_segment_def]; exact hy_h_bd s hs
    have hC : ∀ z ∈ S_segment, ‖fderiv ℝ (f s) z - fderiv ℝ (f s) (Φ ⟨x₀, s⟩)‖ ≤ ε_target := by
      intro z hz
      have h_norm_le : ‖z - Φ ⟨x₀, s⟩‖ ≤ ρ_segment := by
        have := Metric.mem_closedBall.mp hz
        rw [dist_eq_norm] at this; exact this
      have h_norm_lt : ‖z - Φ ⟨x₀, s⟩‖ < δ_uc :=
        lt_of_le_of_lt h_norm_le hh_CE_lt_δuc
      exact le_of_lt (hδ_uc s hs z h_norm_lt)
    have h_residual : ‖f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩)
        - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)‖ ≤ ε_target * ‖y_h s‖ :=
      norm_residual_le_of_diffOn s (Φ ⟨x₀, s⟩) (y_h s) hS_segment_convergence hf_diff hx_segment hxv_segment hC
    have h_eq : f s (Φ ⟨x₀, s⟩) + A s (y_h s) - f s (β_h s)
        = -(f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩) - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)) := by
      change f s (Φ ⟨x₀, s⟩) + (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s)
        - f s (Φ ⟨x₀, s⟩ + y_h s)
          = -(f s (Φ ⟨x₀, s⟩ + y_h s) - f s (Φ ⟨x₀, s⟩) - (fderiv ℝ (f s) (Φ ⟨x₀, s⟩)) (y_h s))
      abel
    rw [h_eq, norm_neg]
    exact h_residual
  set s_set : ℝ → Set E := fun τ => closedBall (Φ ⟨x₀, τ⟩) δ_K_strict with hs_set_def
  have h_diff_right : ∀ τ ∈ Icc t₀ (t₀ + T),
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    have hsub_R : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_left (by linarith)
    have hsub_R_full : Icc t₀ (t₀ + T) ⊆ Icc tmin tmax := hsub_R.trans hsub
    have hv_lip : ∀ τ ∈ Ico t₀ (t₀ + T),
        LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (f τ) (s_set τ) := fun τ hτ =>
      hf_lip_ball τ (hsub_R ⟨hτ.1, le_of_lt hτ.2⟩)
    have hα_h_cont_R : ContinuousOn α_h (Icc t₀ (t₀ + T)) := hα_h_cont.mono hsub_R_full
    have hβ_h_cont_R : ContinuousOn β_h (Icc t₀ (t₀ + T)) := hβ_h_cont.mono hsub_R
    have h_tmax_ge : t₀ + T ≤ tmax := by
      have : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax := hsub
      have h_in : (t₀ + T) ∈ Icc (t₀ - T) (t₀ + T) :=
        Set.right_mem_Icc.mpr (by linarith)
      exact (this h_in).2
    have hα_h_deriv_R : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt α_h (f τ (α_h τ)) (Ici τ) τ := by
      intro τ hτR
      have hτ_full : τ ∈ Icc tmin tmax := hsub_R_full ⟨hτR.1, le_of_lt hτR.2⟩
      have hτ_Ico : τ ∈ Ico tmin tmax :=
        ⟨hτ_full.1, lt_of_lt_of_le hτR.2 h_tmax_ge⟩
      exact hasDerivWithinAt_Ici_of_Icc (hα_h_deriv_full τ hτ_full) hτ_Ico
    have hβ_h_deriv_R : ∀ τ ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt β_h (f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ)) (Ici τ) τ := by
      intro τ hτR
      have hτ_sub : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτR.1, le_of_lt hτR.2⟩
      have hτ_Ico_sub : τ ∈ Ico (t₀ - T) (t₀ + T) := ⟨hτ_sub.1, hτR.2⟩
      exact hasDerivWithinAt_Ici_of_Icc (hβ_h_deriv τ hτ_sub) hτ_Ico_sub
    have hf_bound : ∀ τ ∈ Ico t₀ (t₀ + T), dist (f τ (α_h τ)) (f τ (α_h τ)) ≤ 0 := by
      intro _ _; rw [dist_self]
    have hfs : ∀ τ ∈ Ico t₀ (t₀ + T), α_h τ ∈ s_set τ := by
      intro τ hτR
      exact hα_h_mem_ball τ (hsub_R ⟨hτR.1, le_of_lt hτR.2⟩)
    set εg : ℝ := ε_target * CE * ‖h‖ with hεg_def
    have hεg_nn : 0 ≤ εg := by
      have : 0 ≤ ε_target * CE := mul_nonneg (le_of_lt hε_target_pos) hCE_nn
      exact mul_nonneg this hh_nn
    have hg_bound : ∀ τ ∈ Ico t₀ (t₀ + T),
        dist (f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ)) (f τ (β_h τ)) ≤ εg := by
      intro τ hτR
      have hτ_sub : τ ∈ Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτR.1, le_of_lt hτR.2⟩
      have h_res := h_residual_bound τ hτ_sub
      have h_ybd := hy_h_bd τ hτ_sub
      have h_combine : ε_target * ‖y_h τ‖ ≤ εg := by
        rw [hεg_def, mul_assoc]
        exact mul_le_mul_of_nonneg_left h_ybd (le_of_lt hε_target_pos)
      rw [dist_eq_norm]
      exact le_trans h_res h_combine
    have hgs : ∀ τ ∈ Ico t₀ (t₀ + T), β_h τ ∈ s_set τ := by
      intro τ hτR
      exact hβ_h_mem_ball τ (hsub_R ⟨hτR.1, le_of_lt hτR.2⟩)
    have ha_initial : dist (α_h t₀) (β_h t₀) ≤ 0 := by
      rw [hα_h_initial, hβ_h_initial, dist_self]
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (v := f) (s := s_set) (K := ⟨K_lip, hK_lip_nn⟩)
      (f := α_h) (g := β_h) (f' := fun τ => f τ (α_h τ))
      (g' := fun τ => f τ (Φ ⟨x₀, τ⟩) + A τ (y_h τ))
      (εf := 0) (εg := εg) (δ := 0)
      hv_lip hα_h_cont_R hα_h_deriv_R hf_bound hfs
      hβ_h_cont_R hβ_h_deriv_R hg_bound hgs ha_initial τ hτ
    rw [dist_eq_norm] at hG
    have h_zero_add : (0 : ℝ) + εg = εg := zero_add _
    rw [h_zero_add] at hG
    have hτ_sub_t₀_nn : 0 ≤ τ - t₀ := by linarith [hτ.1]
    have hτ_sub_t₀_le : τ - t₀ ≤ T := by linarith [hτ.2]
    have h_GB :=
      gronwallBound_zero_le (K := K_lip) (ε := εg) (x := τ - t₀)
        hK_lip_pos hεg_nn hτ_sub_t₀_nn
    have h_mono : εg * (τ - t₀) * exp (K_lip * (τ - t₀)) ≤ εg * T * exp (K_lip * T) := by
      have h1 : εg * (τ - t₀) ≤ εg * T := mul_le_mul_of_nonneg_left hτ_sub_t₀_le hεg_nn
      have h2 : exp (K_lip * (τ - t₀)) ≤ exp (K_lip * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ_sub_t₀_le hK_lip_nn)
      exact mul_le_mul h1 h2 (le_of_lt (exp_pos _)) (mul_nonneg hεg_nn (le_of_lt hT))
    have h_GB' : gronwallBound 0 K_lip εg (τ - t₀) ≤ εg * T * exp (K_lip * T) :=
      le_trans h_GB h_mono
    have h_eq_factor : εg * T * exp (K_lip * T) = GfactorR * εg := by
      rw [hGfactorR_def]; ring
    rw [h_eq_factor] at h_GB'
    exact le_trans hG h_GB'
  have h_diff_left : ∀ τ ∈ Icc (t₀ - T) t₀,
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    let ψ : ℝ → ℝ := fun s => 2 * t₀ - s
    set αR : ℝ → E := α_h ∘ ψ with hαR_def
    set βR : ℝ → E := β_h ∘ ψ with hβR_def
    set vR : ℝ → E → E := fun τ x => -f (2 * t₀ - τ) x with hvR_def
    set sR : ℝ → Set E := fun τ => closedBall (Φ ⟨x₀, 2 * t₀ - τ⟩) δ_K_strict with hsR_def
    have hsub_full : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc_left (by linarith)
    have hψ_reflect_in_sub : ∀ s ∈ Icc t₀ (t₀ + T), 2 * t₀ - s ∈ Icc (t₀ - T) (t₀ + T) := by
      intro s hs
      refine ⟨by linarith [hs.2], by linarith [hs.1, hT.le]⟩
    have hψ_deriv : ∀ s, HasDerivAt ψ (-1 : ℝ) s := fun s => by
      have h1 : HasDerivAt (fun s => 2 * t₀ - s) (-1 : ℝ) s := by
        have hraw := (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s)
        have hfun : ((fun _ : ℝ => 2 * t₀) - id) = fun r : ℝ => 2 * t₀ - r := by
          funext r
          rfl
        rw [hfun] at hraw
        simpa only [zero_sub] using hraw
      exact h1
    have h_neg_lip_one : LipschitzWith 1 (Neg.neg : E → E) := LipschitzWith.id.neg
    have hvR_lip : ∀ τ' ∈ Ico t₀ (t₀ + T),
        LipschitzOnWith ⟨K_lip, hK_lip_nn⟩ (vR τ') (sR τ') := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have h_lip := hf_lip_ball (2 * t₀ - τ') hτ'_sub
      have h_eq : vR τ' = (Neg.neg : E → E) ∘ f (2 * t₀ - τ') := rfl
      rw [h_eq]
      have h_coe : (⟨K_lip, hK_lip_nn⟩ : ℝ≥0) = 1 * ⟨K_lip, hK_lip_nn⟩ := by
        rw [one_mul]
      rw [h_coe]
      exact h_neg_lip_one.comp_lipschitzOnWith h_lip
    have hψ_cont : Continuous ψ := by
      have h_id : Continuous (id : ℝ → ℝ) := continuous_id
      have h_const : Continuous (fun _ : ℝ => 2 * t₀) := continuous_const
      have : Continuous (fun s : ℝ => 2 * t₀ - s) := h_const.sub h_id
      exact this
    have hψ_cont_R : ContinuousOn ψ (Icc t₀ (t₀ + T)) := hψ_cont.continuousOn
    have hψ_maps_full : MapsTo ψ (Icc t₀ (t₀ + T)) (Icc tmin tmax) := by
      intro s hs
      exact hsub (hψ_reflect_in_sub s hs)
    have hαR_cont_R : ContinuousOn αR (Icc t₀ (t₀ + T)) := hα_h_cont.comp hψ_cont_R hψ_maps_full
    have hψ_maps_sub : MapsTo ψ (Icc t₀ (t₀ + T)) (Icc (t₀ - T) (t₀ + T)) :=
      hψ_reflect_in_sub
    have hβR_cont_R : ContinuousOn βR (Icc t₀ (t₀ + T)) := hβ_h_cont.comp hψ_cont_R hψ_maps_sub
    have hαR_deriv_R : ∀ τ' ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt αR (vR τ' (αR τ')) (Ici τ') τ' := by
      intro τ' hτ'R
      have hτ'_full : 2 * t₀ - τ' ∈ Icc tmin tmax :=
        hsub (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
      have hτ'_Ioc_full : 2 * t₀ - τ' ∈ Ioc tmin tmax := by
        refine ⟨?_, hτ'_full.2⟩
        have hτ'_gt : 2 * t₀ - τ' > t₀ - T := by linarith [hτ'R.2]
        have minTime_le_initial : tmin ≤ t₀ - T :=
          (hsub (Set.left_mem_Icc.mpr (by linarith : t₀ - T ≤ t₀ + T))).1
        linarith
      have h_d := hΦ.hasDerivWithinAt (x₀ + h) hxh_mem_ball (2 * t₀ - τ') hτ'_full
      have h_d_left :
          HasDerivWithinAt α_h (f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))) (Iic (2 * t₀ - τ'))
            (2 * t₀ - τ') :=
        hasDerivWithinAt_Iic_of_Icc h_d hτ'_Ioc_full
      have hψ_dwa : HasDerivWithinAt ψ (-1 : ℝ) (Ici τ') τ' :=
        (hψ_deriv τ').hasDerivWithinAt
      have hψ_maps' : MapsTo ψ (Ici τ') (Iic (2 * t₀ - τ')) := by
        intro s hs
        have hs_ge : τ' ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ'
        linarith
      have h_comp := HasDerivWithinAt.scomp (g₁ := α_h) (h := ψ)
        τ' h_d_left hψ_dwa hψ_maps'
      have h_simplify : (-1 : ℝ) • f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
          = vR τ' (αR τ') := by
        change (-1 : ℝ) • f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
          = -f (2 * t₀ - τ') (α_h (2 * t₀ - τ'))
        rw [neg_one_smul]
      rw [h_simplify] at h_comp
      exact h_comp
    have hβR_deriv_R : ∀ τ' ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt βR (-(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ')
          (y_h (2 * t₀ - τ'))))
          (Ici τ') τ' := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have hτ'_Ioc_sub : 2 * t₀ - τ' ∈ Ioc (t₀ - T) (t₀ + T) := by
        refine ⟨?_, hτ'_sub.2⟩
        linarith [hτ'R.2]
      have h_d := hβ_h_deriv (2 * t₀ - τ') hτ'_sub
      have h_d_left :
          HasDerivWithinAt β_h (f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ')
            (y_h (2 * t₀ - τ')))
            (Iic (2 * t₀ - τ')) (2 * t₀ - τ') :=
        hasDerivWithinAt_Iic_of_Icc h_d hτ'_Ioc_sub
      have hψ_dwa : HasDerivWithinAt ψ (-1 : ℝ) (Ici τ') τ' :=
        (hψ_deriv τ').hasDerivWithinAt
      have hψ_maps' : MapsTo ψ (Ici τ') (Iic (2 * t₀ - τ')) := by
        intro s hs
        have hs_ge : τ' ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ'
        linarith
      have h_comp := HasDerivWithinAt.scomp (g₁ := β_h) (h := ψ)
        τ' h_d_left hψ_dwa hψ_maps'
      have h_simplify :
          (-1 : ℝ) • (f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
              + A (2 * t₀ - τ') (y_h (2 * t₀ - τ')))
            = -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
              + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))) := by
        rw [neg_one_smul]
      rw [h_simplify] at h_comp
      exact h_comp
    have hf_bound : ∀ τ' ∈ Ico t₀ (t₀ + T), dist (vR τ' (αR τ')) (vR τ' (αR τ')) ≤ 0 := by
      intro _ _; rw [dist_self]
    have hfs : ∀ τ' ∈ Ico t₀ (t₀ + T), αR τ' ∈ sR τ' := by
      intro τ' hτ'R
      change α_h (2 * t₀ - τ') ∈ closedBall (Φ ⟨x₀, 2 * t₀ - τ'⟩) δ_K_strict
      exact hα_h_mem_ball (2 * t₀ - τ') (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
    set εg : ℝ := ε_target * CE * ‖h‖ with hεg_def
    have hεg_nn : 0 ≤ εg := by
      have : 0 ≤ ε_target * CE := mul_nonneg (le_of_lt hε_target_pos) hCE_nn
      exact mul_nonneg this hh_nn
    have hg_bound : ∀ τ' ∈ Ico t₀ (t₀ + T),
        dist (-(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))))
            (vR τ' (βR τ')) ≤ εg := by
      intro τ' hτ'R
      have hτ'_sub : 2 * t₀ - τ' ∈ Icc (t₀ - T) (t₀ + T) :=
        hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩
      have h_res := h_residual_bound (2 * t₀ - τ') hτ'_sub
      have h_ybd := hy_h_bd (2 * t₀ - τ') hτ'_sub
      have h_combine : ε_target * ‖y_h (2 * t₀ - τ')‖ ≤ εg := by
        rw [hεg_def, mul_assoc]
        exact mul_le_mul_of_nonneg_left h_ybd (le_of_lt hε_target_pos)
      change dist _ (-f (2 * t₀ - τ') (β_h (2 * t₀ - τ'))) ≤ εg
      rw [dist_eq_norm]
      have h_diff_eq :
          -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ')))
            - (-f (2 * t₀ - τ') (β_h (2 * t₀ - τ')))
            = -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩) + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))
                - f (2 * t₀ - τ') (β_h (2 * t₀ - τ'))) := by abel
      rw [h_diff_eq, norm_neg]
      exact le_trans h_res h_combine
    have hgs : ∀ τ' ∈ Ico t₀ (t₀ + T), βR τ' ∈ sR τ' := by
      intro τ' hτ'R
      change β_h (2 * t₀ - τ') ∈ closedBall (Φ ⟨x₀, 2 * t₀ - τ'⟩) δ_K_strict
      exact hβ_h_mem_ball (2 * t₀ - τ') (hψ_reflect_in_sub τ' ⟨hτ'R.1, le_of_lt hτ'R.2⟩)
    have ha_initial : dist (αR t₀) (βR t₀) ≤ 0 := by
      change dist (α_h (2 * t₀ - t₀)) (β_h (2 * t₀ - t₀)) ≤ 0
      have h_simp : 2 * t₀ - t₀ = t₀ := by ring
      rw [h_simp, hα_h_initial, hβ_h_initial, dist_self]
    set s_eval : ℝ := 2 * t₀ - τ with hs_eval_def
    have hs_eval_mem : s_eval ∈ Icc t₀ (t₀ + T) := by
      refine ⟨?_, ?_⟩
      · rw [hs_eval_def]; linarith [hτ.2]
      · rw [hs_eval_def]; linarith [hτ.1]
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (v := vR) (s := sR) (K := ⟨K_lip, hK_lip_nn⟩)
      (f := αR) (g := βR) (f' := fun τ' => vR τ' (αR τ'))
      (g' := fun τ' => -(f (2 * t₀ - τ') (Φ ⟨x₀, 2 * t₀ - τ'⟩)
        + A (2 * t₀ - τ') (y_h (2 * t₀ - τ'))))
      (εf := 0) (εg := εg) (δ := 0)
      hvR_lip hαR_cont_R hαR_deriv_R hf_bound hfs
      hβR_cont_R hβR_deriv_R hg_bound hgs ha_initial s_eval hs_eval_mem
    rw [dist_eq_norm] at hG
    have h_zero_add : (0 : ℝ) + εg = εg := zero_add _
    rw [h_zero_add] at hG
    have hαR_eval : αR s_eval = α_h τ := by
      change α_h (2 * t₀ - s_eval) = α_h τ
      have : 2 * t₀ - s_eval = τ := by rw [hs_eval_def]; ring
      rw [this]
    have hβR_eval : βR s_eval = β_h τ := by
      change β_h (2 * t₀ - s_eval) = β_h τ
      have : 2 * t₀ - s_eval = τ := by rw [hs_eval_def]; ring
      rw [this]
    rw [hαR_eval, hβR_eval] at hG
    have hs_diff_nn : 0 ≤ s_eval - t₀ := by rw [hs_eval_def]; linarith [hτ.2]
    have hs_diff_le : s_eval - t₀ ≤ T := by rw [hs_eval_def]; linarith [hτ.1]
    have h_GB :=
      gronwallBound_zero_le (K := K_lip) (ε := εg) (x := s_eval - t₀)
        hK_lip_pos hεg_nn hs_diff_nn
    have h_mono : εg * (s_eval - t₀) * exp (K_lip * (s_eval - t₀)) ≤ εg * T * exp (K_lip * T) := by
      have h1 : εg * (s_eval - t₀) ≤ εg * T := mul_le_mul_of_nonneg_left hs_diff_le hεg_nn
      have h2 : exp (K_lip * (s_eval - t₀)) ≤ exp (K_lip * T) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hs_diff_le hK_lip_nn
      exact mul_le_mul h1 h2 (le_of_lt (exp_pos _)) (mul_nonneg hεg_nn (le_of_lt hT))
    have h_GB' : gronwallBound 0 K_lip εg (s_eval - t₀) ≤ εg * T * exp (K_lip * T) :=
      le_trans h_GB h_mono
    have h_eq_factor : εg * T * exp (K_lip * T) = GfactorR * εg := by
      rw [hGfactorR_def]; ring
    rw [h_eq_factor] at h_GB'
    exact le_trans hG h_GB'
  have h_diff_full : ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖α_h τ - β_h τ‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := by
    intro τ hτ
    rcases le_or_gt τ t₀ with hle | hgt
    · exact h_diff_left τ ⟨hτ.1, hle⟩
    · exact h_diff_right τ ⟨le_of_lt hgt, hτ.2⟩
  have h_final_bd : ‖α_h t - β_h t‖ ≤ GfactorR * (ε_target * CE * ‖h‖) := h_diff_full t ht
  have h_lhs : α_h t - β_h t = Φ ⟨x₀ + h, t⟩ - Φ ⟨x₀, t⟩ - Lmap h := by
    change Φ ⟨x₀ + h, t⟩ - (Φ ⟨x₀, t⟩ + y_h t) = _
    have : Lmap h = vSolution h t := rfl
    rw [this]; abel
  rw [h_lhs] at h_final_bd
  have h_bound_le : GfactorR * (ε_target * CE * ‖h‖) ≤ c * ‖h‖ := by
    have h1 : GfactorR * (ε_target * CE * ‖h‖) = (ε_target * GfactorR * CE) * ‖h‖ := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_right (le_of_lt hε_target_le_one) hh_nn
  exact le_trans h_final_bd h_bound_le

end MainTheorem

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
