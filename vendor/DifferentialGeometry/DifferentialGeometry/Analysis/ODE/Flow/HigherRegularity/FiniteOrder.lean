module

public import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section TimePieceSmoothness

variable {f : ℝ → E → E} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
lemma contDiffOn_graphMap_of_contDiffOn_flow
    {k : ℕ∞} {U : Set (E × ℝ)} (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ => ((q.2, Φ q) : ℝ × E)) U := by
  refine ContDiffOn.prodMk ?_ hΦ_Ck
  exact contDiff_snd.contDiffOn

omit [CompleteSpace E] in
theorem contDiffOn_orbit_composition
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ => f q.2 (Φ q)) U := by
  set g : E × ℝ → ℝ × E := fun q => (q.2, Φ q) with hg_def
  have hg : ContDiffOn ℝ k g U := contDiffOn_graphMap_of_contDiffOn_flow hΦ_Ck
  have hmaps : MapsTo g U (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hcomp : ContDiffOn ℝ k (uncurry f ∘ g) U := hf_Ck.comp hg hmaps
  exact hcomp.congr (by intro q hq; rfl)

omit [CompleteSpace E] in
theorem contDiffOn_timePiece_CLM
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (fun q : E × ℝ =>
      (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))) U := by
  set h : E × ℝ → E := fun q => f q.2 (Φ q) with hh_def
  have hh : ContDiffOn ℝ k h U := contDiffOn_orbit_composition hf_Ck hΦ_Ck
  set S : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) with hS_def
  have hSeq : (fun v : E => (ContinuousLinearMap.id ℝ ℝ).smulRight v) = fun v => S v := by
    funext v
    simp [S, ContinuousLinearMap.smulRightL]
  have heq : (fun q : E × ℝ => (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q)))
      = S ∘ h := by
    funext q
    change (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))
      = S (f q.2 (Φ q))
    simp [S, ContinuousLinearMap.smulRightL]
  rw [heq]
  exact ContDiffOn.continuousLinearMap_comp S hh

end TimePieceSmoothness

section MainTheorem

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_of_isLocalFlow_of_contDiff
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {k : ℕ∞} (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
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
  have hk' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hk
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h := hf_Ck.of_le hk'
    simpa using h
  exact contDiffOn_flow_of_isLocalFlow (f := f) (t₀ := t₀) (x₀ := x₀) (r := r)
    (tmin := tmin) (tmax := tmax) (Φ := Φ) hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

theorem exists_contDiffOn_flow_of_contDiff
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {k : ℕ∞} (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r') (hρ_pos : 0 < (ρ : ℝ))
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧
      ContDiffOn ℝ 1 Φ U := by
  set U : Set (E × ℝ) := ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T) with hU_def
  refine ⟨U, ?_, ?_, ?_⟩
  · exact isOpen_ball.prod isOpen_Ioo
  · refine ⟨?_, ?_⟩
    · exact mem_ball_self hρ_pos
    · exact ⟨by linarith, by linarith⟩
  · exact contDiffOn_flow_of_isLocalFlow_of_contDiff hΦ hk hf_Ck hT hT_lt_mid hT_mid_lt_out
      hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end MainTheorem

section InductiveStep

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

def timePieceFn (f : ℝ → E → E) (Φ : E × ℝ → E) : E × ℝ → (ℝ →L[ℝ] E) :=
  fun q => (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q))

omit [CompleteSpace E] in
@[simp]
lemma timePieceFn_apply (f : ℝ → E → E) (Φ : E × ℝ → E) (q : E × ℝ) :
    timePieceFn f Φ q = (ContinuousLinearMap.id ℝ ℝ).smulRight (f q.2 (Φ q)) := rfl

omit [CompleteSpace E] in
theorem contDiffOn_timePieceFn
    {k : ℕ∞} {U : Set (E × ℝ)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ U) :
    ContDiffOn ℝ k (timePieceFn f Φ) U :=
  contDiffOn_timePiece_CLM hf_Ck hΦ_Ck

omit [CompleteSpace E] in
theorem contDiffOn_succ_of_contDiffOn_fderiv
    {U : Set (E × ℝ)} (hU_open : IsOpen U) {j : ℕ∞}
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (h_fderiv : ContDiffOn ℝ j (fderiv ℝ Φ) U) :
    ContDiffOn ℝ (j + 1) Φ U := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU_open]
  refine ⟨hΦ_diff, ?_, h_fderiv⟩
  intro h
  exact absurd h (by exact_mod_cast WithTop.coe_ne_top)

omit [CompleteSpace E] in
theorem contDiffOn_succ_of_fderiv_coprod_smooth
    {U : Set (E × ℝ)} (hU_open : IsOpen U) {k : ℕ∞}
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (hLsp_Ck : ContDiffOn ℝ k Lsp U)
    (hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U)
    (h_fderiv_eq : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ U := by
  set coprodCLM : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) →L[ℝ] ((E × ℝ) →L[ℝ] E) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := E) (F := ℝ) (G := E) ℝ
      : ((E →L[ℝ] E) × (ℝ →L[ℝ] E)) ≃L[ℝ] ((E × ℝ) →L[ℝ] E)).toContinuousLinearMap
    with hcoprodCLM_def
  have hcoprod_apply :
      ∀ (a : E →L[ℝ] E) (b : ℝ →L[ℝ] E), coprodCLM (a, b) = a.coprod b := by
    intro a b
    change (ContinuousLinearMap.coprodEquivL ℝ (a, b) : (E × ℝ) →L[ℝ] E) = a.coprod b
    rfl
  have hpair_Ck : ContDiffOn ℝ k (fun q : E × ℝ => (Lsp q, timePieceFn f Φ q)) U :=
    hLsp_Ck.prodMk hLti_Ck
  have hcomp_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => coprodCLM (Lsp q, timePieceFn f Φ q)) U :=
    hpair_Ck.continuousLinearMap_comp coprodCLM
  have heq : ∀ q ∈ U, fderiv ℝ Φ q = coprodCLM (Lsp q, timePieceFn f Φ q) := by
    intro q hq
    rw [hcoprod_apply]
    exact h_fderiv_eq q hq
  have h_fderiv_Ck : ContDiffOn ℝ k (fderiv ℝ Φ) U := hcomp_Ck.congr heq
  exact contDiffOn_succ_of_contDiffOn_fderiv hU_open hΦ_diff h_fderiv_Ck

end InductiveStep

section GeneralHeadline

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_succ_of_spatial_smooth
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_Csucc : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hLsp_Ck : ContDiffOn ℝ k Lsp ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set U : Set (E × ℝ) := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hU_open : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hk_one : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
    have hone_le : (1 : ℕ∞) ≤ k + 1 := by
      calc (1 : ℕ∞) = 0 + 1 := by simp
        _ ≤ k + 1 := by gcongr; exact bot_le
    exact_mod_cast hone_le
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h := hf_Csucc.of_le hk_one
    simpa using h
  have hΦ_C1 : ContDiffOn ℝ 1 Φ U :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hΦ_diff : DifferentiableOn ℝ Φ U :=
    hΦ_C1.differentiableOn (by decide)
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_Csucc.of_le h_le
  have hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U :=
    contDiffOn_timePieceFn hf_Ck hΦ_Ck
  exact contDiffOn_succ_of_fderiv_coprod_smooth hU_open hΦ_diff hLsp_Ck hLti_Ck hLsp_eq

theorem contDiffOn_flow_of_spatial_smooth_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (Lsp_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hLsp_smooth : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (Lsp_seq j)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hLsp_eq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (Lsp_seq j q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  induction k with
  | zero =>
    show ContDiffOn ℝ (((0 : ℕ) : ℕ∞)) Φ _
    have h_ρ_r : (ρ : ℝ) ≤ (r : ℝ) :=
      le_trans (le_of_lt hρ_lt_mid) (le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r)
    have h_T_out : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hsub_U : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
        ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
      intro q hq
      refine ⟨?_, ?_⟩
      · exact closedBall_subset_closedBall h_ρ_r
          (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
      · exact hsub (h_T_out (Ioo_subset_Icc_self hq.2))
    have hcont : ContinuousOn Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
      hΦ.continuousOn.mono hsub_U
    have hzero : ((0 : ℕ) : ℕ∞) = (0 : ℕ∞) := by simp
    rw [hzero]
    exact contDiffOn_zero.mpr hcont
  | succ k ih =>
    have hf_Csucc : ContDiffOn ℝ (((k : ℕ∞)) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have hconv : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
      rw [hconv] at hf_Ck
      exact hf_Ck
    have hf_Ck' : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ∞) + 1 : ℕ∞) : WithTop ℕ∞) := by
        have hk_le : (k : ℕ∞) ≤ (k : ℕ∞) + 1 := le_self_add
        exact_mod_cast hk_le
      exact hf_Csucc.of_le h_le
    have hLsp_smooth' : ∀ j : ℕ, j + 1 ≤ k →
        ContDiffOn ℝ (j : ℕ∞) (Lsp_seq j)
          ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
      intro j hj
      exact hLsp_smooth j (by omega)
    have hLsp_eq' : ∀ j : ℕ, j + 1 ≤ k →
        ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        fderiv ℝ Φ q = (Lsp_seq j q).coprod (timePieceFn f Φ q) := by
      intro j hj q hq
      exact hLsp_eq j (by omega) q hq
    have hΦ_Ck := ih hf_Ck' hLsp_smooth' hLsp_eq'
    have h_at_k_smooth : ContDiffOn ℝ (k : ℕ∞) (Lsp_seq k)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := hLsp_smooth k (le_refl _)
    have h_at_k_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        fderiv ℝ Φ q = (Lsp_seq k q).coprod (timePieceFn f Φ q) :=
      hLsp_eq k (le_refl _)
    have h_succ := contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM
      hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
      (k := (k : ℕ∞)) hf_Csucc hΦ_Ck h_at_k_smooth h_at_k_eq
    have hconv : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
    rw [hconv]; exact h_succ

end GeneralHeadline

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
