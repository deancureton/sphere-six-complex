module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.OrbitComparison

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

section LevelOneSmoothnessClause

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}

theorem exists_isLocalFlow_augmentedVectorField_and_contDiffOn_fromAugmentedFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (R_aug : ℝ≥0) (ε_aug : ℝ) (_hR_aug : 0 < R_aug) (_hε_aug : 0 < ε_aug)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
      (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ)),
      IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
          (t₀ - ε_aug) (t₀ + ε_aug) aΦ ∧
        ContDiffOn ℝ 1 (fromAugmentedFlow aΦ)
          ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
    exists_isLocalFlow_augmentedVectorField_of_C2 hf_C2 t₀ p₀
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_augmentedVectorField_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augmentedVectorField_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  set T_a_out : ℝ := ε_aug / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by rw [hT_a_out_def]; linarith
  have hT_a_out_lt : T_a_out < ε_aug := by rw [hT_a_out_def]; linarith
  have hslab_sub_a : closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug) := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact Icc_subset_Icc (by linarith) (by linarith)
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    contDiffOn_partial_fderiv_of_succ (f := augmentedVectorField f) (k := (0 : ℕ∞))
      (by simpa using h_augmentedVectorField_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug)) :=
    haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ
      (closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)) :=
    haΦ_cont_full.mono hslab_sub_a
  set Slab : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out) with hSlab_def
  have hSlab_compact : IsCompact Slab :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_ne : Slab.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have h_aΦ_pair_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_along_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augmentedVectorField f q.2) (aΦ q))
      Slab := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_aΦ_pair_cont hmaps
  have h_norm_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖)
      Slab := by
    have hnorm : Continuous
        (fun A : (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)) => ‖A‖) :=
      continuous_norm
    exact hnorm.comp_continuousOn h_fderiv_along_cont
  rcases hSlab_compact.exists_isMaxOn hSlab_ne h_norm_cont with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augmentedVectorField f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := norm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab, ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  set T_a_mid' : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid'_def
  have hT_a_mid'_pos : 0 < T_a_mid' := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid'_lt_out : T_a_mid' < T_a_out := by
    have h1 : T_a_mid' ≤ T_a_out * 3 / 4 := min_le_left _ _
    have h2 : T_a_out * 3 / 4 < T_a_out := by linarith
    linarith
  have hMTmid' : M_aug * T_a_mid' < 1 := by
    have h1 : T_a_mid' ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid' ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  set T_a : ℝ := T_a_mid' / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by rw [hT_a_def]; linarith
  have hT_a_lt_mid' : T_a < T_a_mid' := by rw [hT_a_def]; linarith
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := R_a_mid / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by rw [hR_a_def]; linarith
  have hR_a_lt_mid : R_a < R_a_mid := by rw [hR_a_def]; linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩ with hR_aN_def
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩ with hR_a_midN_def
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩ with hR_a_outN_def
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩ with hr'a_def
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    rw [hr'a_def]
    change 0 < (R_aug : ℝ) / 8
    linarith
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    have : (r'a : ℝ) = (R_aug : ℝ) / 8 := rfl
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab := ⟨hp, hτ⟩
    have h_pre : ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre :=
      hM_aug_pre_bd ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) hq_in
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have hsub_a : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc (t₀ - ε_aug) (t₀ + ε_aug) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have h_aug_C1 : ContDiffOn ℝ 1 aΦ ((ball p₀ (R_aN : ℝ))
      ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have hk_aug : (1 : ℕ∞) ≤ 1 := le_refl _
    refine contDiffOn_flow_of_isLocalFlow_of_contDiff (f := augmentedVectorField f)
      (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug)
      (Φ := aΦ) haΦ hk_aug h_augmentedVectorField_C1 hT_a_pos hT_a_lt_mid' hT_a_mid'_lt_out
      hM_aug_nn hMTmid' hsub_a (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN)
      hr'a_pos
      ?_ ?_ ?_ ?_ hA_bd_a
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith [hR_a_lt_mid]
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith [hR_a_mid_lt_out]
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
  set T : ℝ := T_a / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_le_T_a : T ≤ T_a := by rw [hT_def]; linarith
  set ρ : ℝ := R_a / 2 with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
  have hρ_le_R_a : ρ ≤ R_a := by rw [hρ_def]; linarith
  set ρN : ℝ≥0 := ⟨ρ, le_of_lt hρ_pos⟩ with hρN_def
  have hρN_eq : (ρN : ℝ) = ρ := rfl
  have hρN_le_R_aN : (ρN : ℝ) ≤ (R_aN : ℝ) := by rw [hρN_eq, hR_aN_eq]; exact hρ_le_R_a
  refine ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, T, ρN, hT_pos, hρ_pos, haΦ, ?_⟩
  exact contDiffOn_fromAugmentedFlow_inherits (ρ_a := R_aN) (ρ := ρN) (T_a := T_a) (T := T)
    hρN_le_R_aN hT_le_T_a h_aug_C1

theorem exists_contDiffOn_fromAugmentedFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      ContDiffOn ℝ 1 (fromAugmentedFlow aΦ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  obtain ⟨_, _, _, _, aΦ, T, ρ, hT, hρ, _, h_smooth⟩ :=
    exists_isLocalFlow_augmentedVectorField_and_contDiffOn_fromAugmentedFlow_one_of_C2
      hf_C2 t₀ x₀
  exact ⟨T, ρ, hT, hρ, aΦ, h_smooth⟩

end LevelOneSmoothnessClause


section VariationalLinearMapCongr

variable {f : ℝ → E → E} {t₀ : ℝ}

theorem variationalLinearMapAt_congr_of_eqOn
    {α₁ α₂ : ℝ → E} {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont_1 : ContinuousOn (fun t => fderiv ℝ (f t) (α₁ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd_1 : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₁ t)‖ ≤ M)
    (hA_cont_2 : ContinuousOn (fun t => fderiv ℝ (f t) (α₂ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd_2 : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₂ t)‖ ≤ M)
    (h_eq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA_cont_1 hA_bd_1 ht
      = variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA_cont_2 hA_bd_2 ht := by
  apply ContinuousLinearMap.ext
  intro δ
  have h_solution_1 := variationalSolutionFun_isSolution hT hM hMT hA_cont_1 hA_bd_1 δ
  have h_solution_2 := variationalSolutionFun_isSolution hT hM hMT hA_cont_2 hA_bd_2 δ
  set y₂ : ℝ → E := variationalSolutionFun hT hM hMT hA_cont_2 hA_bd_2 δ
  have h_solution_2_as_1 : IsVariationalSolutionOn f α₁ δ t₀ y₂ (Icc (t₀ - T) (t₀ + T)) := by
    refine ⟨h_solution_2.initial, fun s hs => ?_⟩
    have h_dw := h_solution_2.hasDerivWithinAt s hs
    have hα_eq : α₁ s = α₂ s := h_eq hs
    rw [hα_eq]
    exact h_dw
  have h_eq_y := IsVariationalSolutionOn.unique_Icc hT hA_cont_1 h_solution_1 h_solution_2_as_1
  rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
  exact h_eq_y ht

end VariationalLinearMapCongr

section CoproductHelper

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem portPrivate_d6e6b011_fderiv_along_continuousOn
    {f : ℝ → E → E} {γ : ℝ → E} {K : Set ℝ}
    (hf : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Set.univ)
    (hγ : ContinuousOn γ K) :
    ContinuousOn (fun s : ℝ => fderiv ℝ (f s) (γ s)) K := by
  have hpair : ContinuousOn (fun s : ℝ => (s, γ s)) K :=
    continuousOn_id.prodMk hγ
  exact hf.continuousOn.comp hpair (fun _ _ => mem_univ _)

theorem exists_fderiv_eq_fromAugmentedFlow_coprod_timePieceFn
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    (ht₀_a_Ioo : t₀ ∈ Ioo tmin_a tmax_a)
    (hR_aug_pos : (0 : ℝ) < (R_aug : ℝ)) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ)),
      ∀ q ∈ (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T),
        fderiv ℝ Φ q = (fromAugmentedFlow aΦ q).coprod (timePieceFn f Φ q) := by
  classical
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  have ht₀_minus_tmin : 0 < t₀ - tmin := by linarith [ht₀_Ioo.1]
  have htmax_minus_t₀ : 0 < tmax - t₀ := by linarith [ht₀_Ioo.2]
  have ht₀_minus_tmin_a : 0 < t₀ - tmin_a := by linarith [ht₀_a_Ioo.1]
  have htmax_a_minus_t₀ : 0 < tmax_a - t₀ := by linarith [ht₀_a_Ioo.2]
  set T_outer : ℝ := min (min (t₀ - tmin) (tmax - t₀))
      (min (t₀ - tmin_a) (tmax_a - t₀)) / 2 with hT_outer_def
  have hT_outer_pos : 0 < T_outer := by
    rw [hT_outer_def]
    exact div_pos
      (lt_min (lt_min ht₀_minus_tmin htmax_minus_t₀)
        (lt_min ht₀_minus_tmin_a htmax_a_minus_t₀)) (by norm_num)
  have hT_outer_le_tmin_half : T_outer ≤ (t₀ - tmin) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin) (tmax - t₀) := min_le_left _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ t₀ - tmin := min_le_left _ _
    linarith
  have hT_outer_le_tmax_half : T_outer ≤ (tmax - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin) (tmax - t₀) := min_le_left _ _
    have h2 : min (t₀ - tmin) (tmax - t₀) ≤ tmax - t₀ := min_le_right _ _
    linarith
  have hT_outer_le_tmin_a_half : T_outer ≤ (t₀ - tmin_a) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin_a) (tmax_a - t₀) := min_le_right _ _
    have h2 : min (t₀ - tmin_a) (tmax_a - t₀) ≤ t₀ - tmin_a := min_le_left _ _
    linarith
  have hT_outer_le_tmax_a_half : T_outer ≤ (tmax_a - t₀) / 2 := by
    rw [hT_outer_def]
    have h1 : min (min (t₀ - tmin) (tmax - t₀)) (min (t₀ - tmin_a) (tmax_a - t₀))
        ≤ min (t₀ - tmin_a) (tmax_a - t₀) := min_le_right _ _
    have h2 : min (t₀ - tmin_a) (tmax_a - t₀) ≤ tmax_a - t₀ := min_le_right _ _
    linarith
  have hsub_outer_orig : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin tmax :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_outer_aug : Icc (t₀ - T_outer) (t₀ + T_outer) ⊆ Icc tmin_a tmax_a :=
    Icc_subset_Icc (by linarith) (by linarith)
  set ρ_outer : ℝ := (r : ℝ) / 2 with hρ_outer_def
  have hρ_outer_pos : 0 < ρ_outer := by rw [hρ_outer_def]; linarith
  have hρ_outer_le_r : ρ_outer ≤ (r : ℝ) := by rw [hρ_outer_def]; linarith
  set R_aug_out : ℝ := (R_aug : ℝ) / 2 with hR_aug_out_def
  have hR_aug_out_pos : 0 < R_aug_out := by rw [hR_aug_out_def]; linarith
  have hR_aug_out_lt : R_aug_out < (R_aug : ℝ) := by rw [hR_aug_out_def]; linarith
  set Slab_a_outer : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_a_outer_def
  have hSlab_a_outer_compact : IsCompact Slab_a_outer :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_aug_out).prod isCompact_Icc
  have hSlab_a_outer_ne : Slab_a_outer.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_aug_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have hslab_aug_sub : closedBall p₀ R_aug_out ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a := by
    exact Set.prod_mono (closedBall_subset_closedBall (le_of_lt hR_aug_out_lt))
      hsub_outer_aug
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc tmin_a tmax_a) := haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ Slab_a_outer :=
    haΦ_cont_full.mono hslab_aug_sub
  have h_aΦ_norm_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖(aΦ q).1 - x₀‖)
      Slab_a_outer := by
    have h_fst_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1) Slab_a_outer :=
      continuous_fst.continuousOn.comp haΦ_cont (fun _ _ => mem_univ _)
    have h_sub_cont : ContinuousOn (fun q : (E × (E →L[ℝ] E)) × ℝ => (aΦ q).1 - x₀)
        Slab_a_outer := h_fst_cont.sub continuousOn_const
    exact continuous_norm.comp_continuousOn h_sub_cont
  rcases hSlab_a_outer_compact.exists_isMaxOn hSlab_a_outer_ne h_aΦ_norm_cont
    with ⟨qmax_R, _, hqmax_R⟩
  set R_aΦ_image_pre : ℝ := ‖(aΦ qmax_R).1 - x₀‖ with hR_aΦ_image_pre_def
  have hR_aΦ_image_pre_nn : 0 ≤ R_aΦ_image_pre := norm_nonneg _
  have hR_aΦ_image_pre_bd : ∀ q ∈ Slab_a_outer, ‖(aΦ q).1 - x₀‖ ≤ R_aΦ_image_pre :=
    fun q hq => hqmax_R hq
  set Slab_Φ_outer : Set (E × ℝ) :=
    closedBall x₀ ρ_outer ×ˢ Icc (t₀ - T_outer) (t₀ + T_outer) with hSlab_Φ_outer_def
  have hSlab_Φ_outer_compact : IsCompact Slab_Φ_outer :=
    (isCompact_closedBall x₀ ρ_outer).prod isCompact_Icc
  have hSlab_Φ_outer_ne : Slab_Φ_outer.Nonempty :=
    ⟨(x₀, t₀), Metric.mem_closedBall_self (le_of_lt hρ_outer_pos),
      ⟨by linarith, by linarith⟩⟩
  have hSlab_Φ_outer_sub_orig : Slab_Φ_outer ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    exact Set.prod_mono (closedBall_subset_closedBall hρ_outer_le_r) hsub_outer_orig
  have hΦ_cont_slab : ContinuousOn Φ Slab_Φ_outer := hΦ.continuousOn.mono hSlab_Φ_outer_sub_orig
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
  set r₀_lip : ℝ := max R_aΦ_image_pre R_Φ_image_pre + 1 with hr₀_lip_def
  have hr₀_lip_pos : 0 < r₀_lip := by
    rw [hr₀_lip_def]
    have : 0 ≤ max R_aΦ_image_pre R_Φ_image_pre :=
      le_max_of_le_left hR_aΦ_image_pre_nn
    linarith
  have hr₀_lip_ge_aΦ : R_aΦ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_aΦ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_left _ _
    linarith
  have hr₀_lip_ge_Φ : R_Φ_image_pre ≤ r₀_lip := by
    rw [hr₀_lip_def]
    have : R_Φ_image_pre ≤ max R_aΦ_image_pre R_Φ_image_pre := le_max_right _ _
    linarith
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
  set K_origN : ℝ≥0 := ⟨K_orig, hK_orig_nn⟩ with hK_origN_def
  have hK_origN_eq : (K_origN : ℝ) = K_orig := rfl
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
  set ρ_final : ℝ := min ρ_outer R_aug_out / 8 with hρ_final_def
  have hρ_final_pos : 0 < ρ_final := by
    rw [hρ_final_def]
    exact div_pos (lt_min hρ_outer_pos hR_aug_out_pos) (by norm_num)
  have hρ_final_le_outer_8 : ρ_final ≤ ρ_outer / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ ρ_outer := min_le_left _ _
    linarith
  have hρ_final_le_outer : ρ_final ≤ ρ_outer := by linarith
  have hρ_final_le_R_aug_out_8 : ρ_final ≤ R_aug_out / 8 := by
    rw [hρ_final_def]
    have : min ρ_outer R_aug_out ≤ R_aug_out := min_le_right _ _
    linarith
  have hρ_final_le_R_aug_out : ρ_final ≤ R_aug_out := by linarith
  set ρ_finalN : ℝ≥0 := ⟨ρ_final, le_of_lt hρ_final_pos⟩ with hρ_finalN_def
  have hρ_finalN_eq : (ρ_finalN : ℝ) = ρ_final := rfl
  suffices hfinal : ∀ q ∈
      (Metric.ball x₀ (ρ_finalN : ℝ)) ×ˢ Set.Ioo (t₀ - T_final) (t₀ + T_final),
      fderiv ℝ Φ q = (fromAugmentedFlow aΦ q).coprod (timePieceFn f Φ q) by
    exact ⟨T_final, ρ_finalN, hT_final_pos, hρ_final_pos, hfinal⟩
  intro q hq
  rcases hq with ⟨hq_x, hq_t⟩
  obtain ⟨x, t⟩ := q
  rw [mem_ball] at hq_x
  change dist x x₀ < ρ_final at hq_x
  have hx_closed_ρ_final : x ∈ closedBall x₀ ρ_final := mem_closedBall.mpr (le_of_lt hq_x)
  have hx_closed_ρ_outer : x ∈ closedBall x₀ ρ_outer :=
    closedBall_subset_closedBall hρ_final_le_outer hx_closed_ρ_final
  have hx_closed_r : x ∈ closedBall x₀ (r : ℝ) :=
    closedBall_subset_closedBall hρ_outer_le_r hx_closed_ρ_outer
  have hx_id_closed_R_aug_out : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ R_aug_out := by
    rw [mem_closedBall]
    change max (dist x x₀) (dist (ContinuousLinearMap.id ℝ E)
      (ContinuousLinearMap.id ℝ E)) ≤ R_aug_out
    rw [dist_self, max_eq_left dist_nonneg]
    rw [mem_closedBall] at hx_closed_ρ_final
    exact le_trans hx_closed_ρ_final hρ_final_le_R_aug_out
  have hx_id_closed_R_aug : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R_aug : ℝ) :=
    closedBall_subset_closedBall (le_of_lt hR_aug_out_lt) hx_id_closed_R_aug_out
  have ht_Ioo_final : t ∈ Ioo (t₀ - T_final) (t₀ + T_final) := hq_t
  have ht_Icc_final : t ∈ Icc (t₀ - T_final) (t₀ + T_final) := Ioo_subset_Icc_self ht_Ioo_final
  have hsub_final_outer : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc (t₀ - T_outer) (t₀ + T_outer) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_final_orig : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc tmin tmax :=
    hsub_final_outer.trans hsub_outer_orig
  have hsub_final_aug : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc tmin_a tmax_a :=
    hsub_final_outer.trans hsub_outer_aug
  have h_Φ_in_r₀ : ∀ s ∈ Ioo (t₀ - T_final) (t₀ + T_final), Φ ⟨x, s⟩ ∈ closedBall x₀ r₀_lip := by
    intro s hs
    have hs_Icc_outer : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hs)
    have h_pair_in_outer : ((x, s) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hs_Icc_outer⟩
    have h_pre : ‖Φ (x, s) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans h_pre hr₀_lip_ge_Φ
  have h_aΦ_fst_in_r₀ : ∀ s ∈ Ioo (t₀ - T_final) (t₀ + T_final),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ r₀_lip := by
    intro s hs
    have hs_Icc_outer : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hs)
    have h_pair_in_a_outer : (((x, ContinuousLinearMap.id ℝ E), s) :
        (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a_outer :=
      ⟨hx_id_closed_R_aug_out, hs_Icc_outer⟩
    have h_pre : ‖(aΦ ((x, ContinuousLinearMap.id ℝ E), s)).1 - x₀‖ ≤ R_aΦ_image_pre :=
      hR_aΦ_image_pre_bd _ h_pair_in_a_outer
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans h_pre hr₀_lip_ge_aΦ
  have h_lip_on_r₀ : ∀ τ ∈ Ioo (t₀ - T_final) (t₀ + T_final),
      LipschitzOnWith K_origN (f τ) (closedBall x₀ r₀_lip) := by
    intro τ hτ
    have hτ_Icc : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) :=
      hsub_final_outer (Ioo_subset_Icc_self hτ)
    have hf_τ_diff_at : ∀ z, DifferentiableAt ℝ (f τ) z := fun z => by
      have hcd_at : ContDiffAt ℝ 1 (uncurry f) (τ, z) :=
        hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
      exact (hcd_at.differentiableAt one_ne_zero).comp z
        (((differentiableAt_const τ).prodMk differentiableAt_id))
    have hbound : ∀ z ∈ closedBall x₀ r₀_lip, ‖fderiv ℝ (f τ) z‖₊ ≤ K_origN := by
      intro z hz
      have hp_in : ((τ, z) : ℝ × E) ∈ Slab_f := ⟨hτ_Icc, hz⟩
      have h_pre : ‖fderiv ℝ (f τ) z‖ ≤ K_pre :=
        hK_pre_bd ((τ, z) : ℝ × E) hp_in
      have h_le_K_orig : ‖fderiv ℝ (f τ) z‖ ≤ K_orig := by rw [hK_orig_def]; linarith
      rw [← NNReal.coe_le_coe, coe_nnnorm, hK_origN_eq]
      exact h_le_K_orig
    exact (convex_closedBall x₀ r₀_lip).lipschitzOnWith_of_nnnorm_fderiv_le
      (f := f τ) (C := K_origN) (fun z _ => hf_τ_diff_at z) hbound
  have ht₀_Ioo_final : t₀ ∈ Ioo (t₀ - T_final) (t₀ + T_final) :=
    ⟨by linarith, by linarith⟩
  have h_orbit_eqOn : EqOn (fun s => Φ ⟨x, s⟩)
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
      (Icc (t₀ - T_final) (t₀ + T_final)) :=
    orbit_eq_Icc_of_augmentedFlow_isLocalFlow hΦ haΦ hx_closed_r hx_id_closed_R_aug
      hsub_final_orig hsub_final_aug ht₀_Ioo_final
      (r₀ := r₀_lip) (K := K_origN) h_Φ_in_r₀ h_aΦ_fst_in_r₀ h_lip_on_r₀
  have hA_cont_orbit_a : ContinuousOn (fun s : ℝ => fderiv ℝ (f s)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)) (Icc (t₀ - T_final) (t₀ + T_final)) := by
    have h_pair_cont : ContinuousOn (fun s : ℝ => (s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1))
        (Icc (t₀ - T_final) (t₀ + T_final)) := by
      have h_orbit_cont : ContinuousOn
          (fun s : ℝ => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
          (Icc (t₀ - T_final) (t₀ + T_final)) :=
        (haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_id_closed_R_aug).mono
          (by intro s hs; exact hsub_final_aug hs)
      have h_fst_cont : ContinuousOn (fun s : ℝ => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
          (Icc (t₀ - T_final) (t₀ + T_final)) :=
        continuous_fst.continuousOn.comp h_orbit_cont (fun _ _ => mem_univ _)
      exact continuousOn_id.prodMk h_fst_cont
    have hpartial_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (Set.univ : Set (ℝ × E)) := hpartial_f.continuousOn
    have hmaps : MapsTo (fun s : ℝ => (s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1))
        (Icc (t₀ - T_final) (t₀ + T_final)) (Set.univ : Set (ℝ × E)) :=
      fun _ _ => mem_univ _
    exact hpartial_cont.comp h_pair_cont hmaps
  have hA_bd_orbit_a : ∀ s ∈ Icc (t₀ - T_final) (t₀ + T_final),
      ‖fderiv ℝ (f s) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)‖ ≤ K_orig := by
    intro s hs
    have hs_outer_Icc : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := hsub_final_outer hs
    have h_orbit_in_r₀ : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ r₀_lip := by
      have h_pair_in_a_outer : (((x, ContinuousLinearMap.id ℝ E), s) :
          (E × (E →L[ℝ] E)) × ℝ) ∈ Slab_a_outer :=
        ⟨hx_id_closed_R_aug_out, hs_outer_Icc⟩
      have h_pre : ‖(aΦ ((x, ContinuousLinearMap.id ℝ E), s)).1 - x₀‖ ≤ R_aΦ_image_pre :=
        hR_aΦ_image_pre_bd _ h_pair_in_a_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_aΦ
    have h_pair_in_f : ((s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) : ℝ × E) ∈ Slab_f :=
      ⟨hs_outer_Icc, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f s) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)‖ ≤ K_pre :=
      hK_pre_bd ((s, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) : ℝ × E) h_pair_in_f
    rw [hK_orig_def]
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have h_KT_final : K_orig * T_final < 1 := by
    have : K_orig * T_final < K_orig * T_mid :=
      mul_lt_mul_of_pos_left hT_final_lt_mid hK_orig_pos
    linarith
  have h_aΦ_snd_eq : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_a hA_bd_orbit_a ht_Icc_final :=
    augmentedFlow_snd_eq_variationalLinearMapAt (aΦ := aΦ) (R := R_aug) (tmin' := tmin_a)
      (tmax' := tmax_a) (p₀ := p₀) haΦ
      (T := T_final) (M := K_orig) hT_final_pos hK_orig_nn h_KT_final hsub_final_aug
      (x := x) hx_id_closed_R_aug hA_cont_orbit_a hA_bd_orbit_a ht_Icc_final
  have hA_cont_orbit_Φ : ContinuousOn (fun s : ℝ => fderiv ℝ (f s) (Φ ⟨x, s⟩))
      (Icc (t₀ - T_final) (t₀ + T_final)) := by
    have h_orbit_cont : ContinuousOn (fun s : ℝ => Φ ⟨x, s⟩) (Icc tmin tmax) :=
      hΦ.orbit_continuousOn x hx_closed_r
    exact portPrivate_d6e6b011_fderiv_along_continuousOn (E := E) (f := f)
      (γ := fun s : ℝ => Φ ⟨x, s⟩)
      (K := Icc (t₀ - T_final) (t₀ + T_final)) hpartial_f
      (h_orbit_cont.mono hsub_final_orig)
  have hA_bd_orbit_Φ : ∀ s ∈ Icc (t₀ - T_final) (t₀ + T_final),
      ‖fderiv ℝ (f s) (Φ ⟨x, s⟩)‖ ≤ K_orig := by
    intro s hs
    have hs_outer_Icc : s ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := hsub_final_outer hs
    have h_pair_in_outer : ((x, s) : E × ℝ) ∈ Slab_Φ_outer :=
      ⟨hx_closed_ρ_outer, hs_outer_Icc⟩
    have h_orbit_in_r₀ : Φ ⟨x, s⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (x, s) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((s, Φ ⟨x, s⟩) : ℝ × E) ∈ Slab_f := ⟨hs_outer_Icc, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f s) (Φ ⟨x, s⟩)‖ ≤ K_pre :=
      hK_pre_bd ((s, Φ ⟨x, s⟩) : ℝ × E) h_pair_in_f
    rw [hK_orig_def]
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have h_var_congr := variationalLinearMapAt_congr_of_eqOn (f := f)
    (α₁ := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
    (α₂ := fun s => Φ ⟨x, s⟩) (t₀ := t₀) (T := T_final) (M := K_orig)
    hT_final_pos hK_orig_nn h_KT_final
    hA_cont_orbit_a hA_bd_orbit_a hA_cont_orbit_Φ hA_bd_orbit_Φ
    h_orbit_eqOn.symm ht_Icc_final
  have h_aΦ_snd_eq_Φ : (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
          hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_Φ hA_bd_orbit_Φ ht_Icc_final := by
    rw [h_aΦ_snd_eq, h_var_congr]
  set ρ_outerN : ℝ≥0 := ⟨ρ_outer, le_of_lt hρ_outer_pos⟩
  set r'_φ : ℝ≥0 := ⟨ρ_outer / 2, by positivity⟩
  have hr'_φ_pos : (0 : ℝ) < (r'_φ : ℝ) := by change 0 < ρ_outer / 2; linarith
  have hρρ'_φ : (ρ_outerN : ℝ) + (r'_φ : ℝ) ≤ (r : ℝ) := by
    change ρ_outer + ρ_outer / 2 ≤ (r : ℝ)
    have : ρ_outer + ρ_outer / 2 = ρ_outer * 3 / 2 := by ring
    rw [this, hρ_outer_def]
    have : (r : ℝ) / 2 * 3 / 2 ≤ (r : ℝ) := by linarith
    linarith
  have hA_bd_Φ_jointly : ∀ y ∈ closedBall x₀ (ρ_outerN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
        ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_orig := by
    intro y hy τ hτ
    have hy_closed_ρ_outer : y ∈ closedBall x₀ ρ_outer := by
      change dist y x₀ ≤ ρ_outer
      rw [mem_closedBall] at hy
      exact hy
    have hy_closed_r : y ∈ closedBall x₀ (r : ℝ) :=
      closedBall_subset_closedBall hρ_outer_le_r hy_closed_ρ_outer
    have hτ_outer : τ ∈ Icc (t₀ - T_outer) (t₀ + T_outer) := by
      exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have h_pair_in_outer : ((y, τ) : E × ℝ) ∈ Slab_Φ_outer := ⟨hy_closed_ρ_outer, hτ_outer⟩
    have h_orbit_in_r₀ : Φ ⟨y, τ⟩ ∈ closedBall x₀ r₀_lip := by
      have h_pre : ‖Φ (y, τ) - x₀‖ ≤ R_Φ_image_pre := hR_Φ_image_pre_bd _ h_pair_in_outer
      rw [mem_closedBall, dist_eq_norm]
      exact le_trans h_pre hr₀_lip_ge_Φ
    have h_pair_in_f : ((τ, Φ ⟨y, τ⟩) : ℝ × E) ∈ Slab_f := ⟨hτ_outer, h_orbit_in_r₀⟩
    have h_pre : ‖fderiv ℝ (f τ) (Φ ⟨y, τ⟩)‖ ≤ K_pre :=
      hK_pre_bd ((τ, Φ ⟨y, τ⟩) : ℝ × E) h_pair_in_f
    rw [hK_orig_def]
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have hsub_mid_orig : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := by
    exact Icc_subset_Icc (by linarith [hT_mid_lt_outer])
      (by linarith [hT_mid_lt_outer])
  have ht_Ioo_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := by
    exact ⟨by linarith [ht_Ioo_final.1, hT_final_lt_mid],
      by linarith [ht_Ioo_final.2, hT_final_lt_mid]⟩
  have hx_closed_ρ_outerN : x ∈ closedBall x₀ (ρ_outerN : ℝ) := by
    change dist x x₀ ≤ ρ_outer
    rw [mem_closedBall] at hx_closed_ρ_outer
    exact hx_closed_ρ_outer
  have h_jointFD := hasFDerivAt_flow_jointly_at hΦ hf_C1
    hT_mid_pos hK_orig_nn hKT_mid hsub_mid_orig hr'_φ_pos hρρ'_φ hA_bd_Φ_jointly
    hx_closed_ρ_outerN ht_Ioo_mid
  have hfderiv_Φ_eq := h_jointFD.fderiv
  set Lmap_mid := variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
    hT_mid_pos hK_orig_nn hKT_mid
    ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x hx_closed_r).mono hsub_mid_orig)
    (fun τ hτ => hA_bd_Φ_jointly x hx_closed_ρ_outerN τ hτ)
    (Ioo_subset_Icc_self ht_Ioo_mid)
  set Lti : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))
  have hgoal_lhs : fderiv ℝ Φ (x, t) = Lmap_mid.coprod Lti := hfderiv_Φ_eq
  have hLmap_mid_restricted_to_final : Lmap_mid =
      variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
        hT_final_pos hK_orig_nn h_KT_final hA_cont_orbit_Φ hA_bd_orbit_Φ ht_Icc_final := by
    apply ContinuousLinearMap.ext
    intro δ
    have h_solution_mid := variationalSolutionFun_isSolution hT_mid_pos hK_orig_nn hKT_mid
      ((hΦ.continuousOn_fderiv_along_orbit hf_C1 x hx_closed_r).mono hsub_mid_orig)
      (fun τ hτ => hA_bd_Φ_jointly x hx_closed_ρ_outerN τ hτ) δ
    have h_solution_final := variationalSolutionFun_isSolution hT_final_pos hK_orig_nn h_KT_final
      hA_cont_orbit_Φ hA_bd_orbit_Φ δ
    have hsub_final_mid : Icc (t₀ - T_final) (t₀ + T_final) ⊆ Icc (t₀ - T_mid) (t₀ + T_mid) :=
      Icc_subset_Icc
        (sub_le_sub_left (le_of_lt hT_final_lt_mid) t₀)
        (add_le_add_right (le_of_lt hT_final_lt_mid) t₀)
    have h_solution_mid_restricted := h_solution_mid.mono hsub_final_mid
    have h_eq_y := IsVariationalSolutionOn.unique_Icc hT_final_pos hA_cont_orbit_Φ
      h_solution_mid_restricted h_solution_final
    rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
    exact h_eq_y ht_Icc_final
  have hLmap_mid_eq_aΦ_snd : Lmap_mid = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := by
    rw [hLmap_mid_restricted_to_final, ← h_aΦ_snd_eq_Φ]
  rw [hgoal_lhs, hLmap_mid_eq_aΦ_snd]
  rfl

end CoproductHelper


end Flow
end ODE
end Analysis
end DifferentialGeometry

end
