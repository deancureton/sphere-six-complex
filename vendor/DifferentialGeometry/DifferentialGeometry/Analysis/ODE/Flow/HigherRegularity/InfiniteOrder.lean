module

public import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Parametric
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section

noncomputable section

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set Metric Function
open scoped ContDiff NNReal

theorem contDiffOn_top_of_forall_nat
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {S : Set E}
    (h : ∀ k : ℕ, ContDiffOn 𝕜 (k : ℕ∞) f S) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) f S :=
  contDiffOn_infty.mpr h

section CoefficientRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem portPrivate_8f11500e_contDiffOn_variational_coeff
    {n : ℕ} {T : ℝ} {ρ : ℝ≥0}
    (hf_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) (univ : Set (ℝ × E)))
    (hΦ_Cn : ContDiffOn ℝ (n : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ (n : ℕ∞)
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set pfD : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2
  set iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  suffices h : ContDiffOn ℝ (n : ℕ∞) (pfD ∘ iM) U by exact h.congr (fun _ _ => rfl)
  have hpfd : ContDiffOn ℝ (n : ℕ∞) pfD (univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ hf_succ
  have hiM : ContDiffOn ℝ (n : ℕ∞) iM U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ (n : ℕ∞) Prod.snd U).prodMk hΦ_Cn
  exact hpfd.comp hiM (fun _ _ => mem_univ _)

end CoefficientRegularity

section HartmanTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem IsLocalFlow.contDiffOn_top
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_top : ContDiff ℝ ∞ (uncurry f))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid)
      (hT_mid_lt_out : T_mid < T_out) (hM : 0 ≤ M)
      (hMT_mid : M * T_mid < 1)
      (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
      (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ))
      (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
      (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
      (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ),
       ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
       ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ ∞ Φ
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  apply contDiffOn_top_of_forall_nat
  intro n
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hf_Ck : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞) (uncurry f) (univ : Set (ℝ × E)) :=
    fun k => (hf_top.contDiffOn : ContDiffOn ℝ ∞ (uncurry f) univ).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (univ : Set (ℝ × E)) := by simpa using hf_Ck 1
  have hΦ_C1 : ContDiffOn ℝ 1 Φ U :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M :=
    fun x hx τ hτ =>
      hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  have hab : t₀ - T < t₀ + T := by linarith
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  induction n with
  | zero => exact hΦ_C1.of_le (by decide)
  | succ n ih =>
    have hf_Csucc : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) (univ : Set (ℝ × E)) := by
      simpa using hf_Ck (n + 1)
    have hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q)) U :=
      portPrivate_8f11500e_contDiffOn_variational_coeff hf_Csucc ih
    set A : E → ℝ → (E →L[ℝ] E) := fun x t => fderiv ℝ (f t) (Φ ⟨x, t⟩)
    have hlinear_Cn : ∀ δ : E, ContDiffOn ℝ (n : ℕ∞)
        (uncurry (linearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ)))
        (ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
      fun δ => linearODESolution_contDiffOn ht₀_mem isOpen_ball n
        (hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry A) _)
        (contDiffOn_const : ContDiffOn ℝ (n : ℕ∞) (fun (_ : E) => δ) (ball x₀ (ρ : ℝ)))
    set Lsp : E × ℝ → E →L[ℝ] E :=
      fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hfderiv_coprod : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q) := by
      intro ⟨x, t⟩ ⟨hx, ht⟩
      have hx' : dist x x₀ < ↑ρ := mem_ball.mp hx
      have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
        mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
      have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hfd := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid
        hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
      rw [hfd.fderiv]
      change (variationalLinearMapAt hT_mid_pos hM hMT_mid _ _ _).coprod
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ (x, t))))
        = (Lsp (x, t)).coprod (timePieceFn f Φ (x, t))
      congr 1
      · change _ = (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
        rw [hfd.fderiv]
        exact (ContinuousLinearMap.coprod_comp_inl _ _).symm
    have hLsp_Cn : ContDiffOn ℝ (n : ℕ∞) Lsp U := by
      rw [contDiffOn_clm_apply]
      intro δ
      refine (hlinear_Cn δ).congr (fun q hq => ?_)
      obtain ⟨hx_ball, ht_Ioo⟩ := hq
      have hx' : dist q.1 x₀ < ↑ρ := mem_ball.mp hx_ball
      have hx_cb_mid : q.1 ∈ closedBall x₀ (ρ_mid : ℝ) :=
        mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
      have ht_mid : q.2 ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
        ⟨by linarith [ht_Ioo.1], by linarith [ht_Ioo.2]⟩
      have hΦ_restr := hΦ.restrict_center_of_norm_le (x₁ := q.1) (r' := r') (by
        rw [mem_closedBall] at hx_cb_mid; linarith)
      have hA_cont_x := ((hΦ_restr.continuousOn_fderiv_along_orbit hf_C1 q.1
        (mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub_mid)
      have hA_bd_x := fun τ hτ => hA_bd_mid q.1 hx_cb_mid τ hτ
      have ht_Icc : q.2 ∈ Icc (t₀ - T_mid) (t₀ + T_mid) := Ioo_subset_Icc_self ht_mid
      have hfd := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid
        hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
      have hLsp_eq_vlm : Lsp q =
          variationalLinearMapAt hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x ht_Icc := by
        change (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) = _
        conv_lhs => rw [show q = (q.1, q.2) from Prod.mk.eta.symm]
        rw [hfd.fderiv]
        exact ContinuousLinearMap.coprod_comp_inl _ _
      have hvlm_eq := variationalLinearMapAt_apply hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x
        ht_Icc δ
      have hvsf := variationalSolutionFun_isSolution hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x δ
      have hA_cont_Ioo : ContinuousOn (A q.1) (Ioo (t₀ - T) (t₀ + T)) :=
        hA_cont_x.mono (fun s hs => Ioo_subset_Icc_self
          (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid)))
      have hA_joint_cont : ContinuousOn (uncurry A)
          (ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)) := hcoeff_Cn.continuousOn
      have h_exists : HasLinearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ) q.1 :=
        hasLinearODESolution_of_continuousOn ht₀_mem hA_joint_cont
          (mem_ball.mpr hx')
      have h_uniq := linearODE_unique_on_Ioo (G := E) ht₀_mem hA_cont_Ioo
        (fun s hs => by
          have hs_mid : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
            ⟨by linarith [hs.1], by linarith [hs.2]⟩
          exact (hvsf.2 s (Ioo_subset_Icc_self hs_mid)).hasDerivAt (Icc_mem_nhds_iff.mpr hs_mid))
        (fun s hs => linearODESolution_hasDerivAt_of_hasSolution A (t₀ - T) (t₀ + T) t₀
          (fun _ => δ) h_exists hs)
        (by rw [hvsf.1, linearODESolution_initial])
      simp only [hLsp_eq_vlm, hvlm_eq, uncurry]
      have h_eq := h_uniq ht_Ioo
      dsimp at h_eq
      exact h_eq
    exact contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub
      hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
      (by simpa using hf_Ck (n + 1)) ih hLsp_Cn hfderiv_coprod

end HartmanTheorem

end DifferentialGeometry.Analysis.ODE.Flow

end
