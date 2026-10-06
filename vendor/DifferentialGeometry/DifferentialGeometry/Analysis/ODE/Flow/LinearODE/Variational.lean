module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsVariationalSolutionOn
    (f : ℝ → E → E) (α : ℝ → E) (δ : E) (t₀ : ℝ) (y : ℝ → E) (s : Set ℝ) : Prop :=
  y t₀ = δ ∧
    ∀ t ∈ s, HasDerivWithinAt y ((fderiv ℝ (f t) (α t)) (y t)) s t

def IsVariationalSolution
    (f : ℝ → E → E) (α : ℝ → E) (δ : E) (t₀ : ℝ) (y : ℝ → E) : Prop :=
  y t₀ = δ ∧
    ∀ t : ℝ, HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t

namespace IsVariationalSolutionOn

variable {f : ℝ → E → E} {α : ℝ → E} {δ : E} {t₀ : ℝ} {y : ℝ → E} {s : Set ℝ}

lemma initial (hy : IsVariationalSolutionOn f α δ t₀ y s) : y t₀ = δ := hy.1

lemma hasDerivWithinAt (hy : IsVariationalSolutionOn f α δ t₀ y s) :
    ∀ t ∈ s, HasDerivWithinAt y ((fderiv ℝ (f t) (α t)) (y t)) s t := hy.2

lemma mono {s' : Set ℝ} (hy : IsVariationalSolutionOn f α δ t₀ y s) (hs : s' ⊆ s) :
    IsVariationalSolutionOn f α δ t₀ y s' :=
  ⟨hy.1, fun t ht => (hy.2 t (hs ht)).mono hs⟩

lemma continuousOn (hy : IsVariationalSolutionOn f α δ t₀ y s) : ContinuousOn y s :=
  fun t ht => (hy.2 t ht).continuousWithinAt

lemma hasDerivAt_of_isOpen (hy : IsVariationalSolutionOn f α δ t₀ y s) (hs : IsOpen s)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t :=
  (hy.2 t ht).hasDerivAt (hs.mem_nhds ht)

end IsVariationalSolutionOn

namespace IsVariationalSolution

variable {f : ℝ → E → E} {α : ℝ → E} {δ : E} {t₀ : ℝ} {y : ℝ → E}

lemma initial (hy : IsVariationalSolution f α δ t₀ y) : y t₀ = δ := hy.1

lemma hasDerivAt (hy : IsVariationalSolution f α δ t₀ y) :
    ∀ t : ℝ, HasDerivAt y ((fderiv ℝ (f t) (α t)) (y t)) t := hy.2

lemma toIsVariationalSolutionOn (hy : IsVariationalSolution f α δ t₀ y) (s : Set ℝ) :
    IsVariationalSolutionOn f α δ t₀ y s :=
  ⟨hy.1, fun t _ => (hy.2 t).hasDerivWithinAt⟩

lemma continuous (hy : IsVariationalSolution f α δ t₀ y) : Continuous y :=
  continuous_iff_continuousAt.mpr (fun t => (hy.2 t).continuousAt)

end IsVariationalSolution

section Linearization

variable {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E}

lemma fderiv_eq_comp_inr {f : ℝ → E → E} {p : ℝ × E}
    (hdiff_joint : DifferentiableAt ℝ (uncurry f) p) :
    fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hfd_joint : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p) p :=
    hdiff_joint.hasFDerivAt
  have hg : HasFDerivAt (fun y : E => ((p.1 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
    have h1 : HasFDerivAt (fun _ : E => (p.1 : ℝ)) (0 : E →L[ℝ] ℝ) p.2 :=
      hasFDerivAt_const _ _
    have h2 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) p.2 :=
      hasFDerivAt_id _
    have h3 := h1.prodMk h2
    have : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)
        = ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> simp
    rw [this] at h3
    exact h3
  have hp_eq : ((p.1 : ℝ), p.2) = p := by ext <;> rfl
  have hfd_joint' :
      HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p)
        ((fun y : E => ((p.1 : ℝ), y)) p.2) := by
    change HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) p) ((p.1, p.2))
    rw [hp_eq]
    exact hfd_joint
  have hcomp_raw :
      HasFDerivAt ((uncurry f) ∘ (fun y : E => ((p.1 : ℝ), y)))
        ((fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
    HasFDerivAt.comp p.2 hfd_joint' hg
  have huncurry_eq : (uncurry f) ∘ (fun y : E => ((p.1 : ℝ), y)) = f p.1 := by
    funext y; rfl
  rw [huncurry_eq] at hcomp_raw
  exact hcomp_raw.fderiv

lemma continuousOn_partialFDeriv_uncurry
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (s ×ˢ u) := by
  have hprod_open : IsOpen (s ×ˢ u) := hs.prod hu
  have hf_full :
      ContinuousOn (fun p : ℝ × E => fderiv ℝ (uncurry f) p) (s ×ˢ u) :=
    hf.continuousOn_fderiv_of_isOpen hprod_open le_rfl
  have hpartial_eq :
      EqOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
        (fun p : ℝ × E =>
          (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E))
        (s ×ˢ u) := by
      intro p hp
      have hp_open : (s ×ˢ u) ∈ 𝓝 p := hprod_open.mem_nhds hp
      have hdiff_joint : DifferentiableAt ℝ (uncurry f) p :=
        ((hf.contDiffAt hp_open).differentiableAt one_ne_zero)
      exact fderiv_eq_comp_inr hdiff_joint
  have hcomp_cont :
      ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (s ×ˢ u) := by
    have hpostL : Continuous
        (fun M : (ℝ × E) →L[ℝ] E => M.comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
      exact Continuous.clm_comp_const continuous_id (ContinuousLinearMap.inr ℝ ℝ E)
    exact hpostL.comp_continuousOn hf_full
  exact hcomp_cont.congr hpartial_eq

lemma continuousOn_fderiv_along_curve
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u)
    (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t => fderiv ℝ (f t) (α t)) s := by
  have hpartial := continuousOn_partialFDeriv_uncurry hf hs hu
  have hcont_curve : ContinuousOn (fun t : ℝ => (t, α t)) s :=
    continuousOn_id.prodMk hα
  have hmaps : MapsTo (fun t : ℝ => (t, α t)) s (s ×ˢ u) := fun t ht => ⟨ht, hmem t ht⟩
  exact hpartial.comp hcont_curve hmaps

lemma exists_bound_fderiv_along_curve_Icc {tmin tmax : ℝ}
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u)
    (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u)
    (hsub : Icc tmin tmax ⊆ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc tmin tmax, ‖fderiv ℝ (f t) (α t)‖ ≤ M := by
  rcases le_or_gt tmin tmax with hle | hlt
  · have hcont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) s :=
      continuousOn_fderiv_along_curve hf hs hu hα hmem
    have hcont' : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc tmin tmax) :=
      hcont.mono hsub
    have hcont_norm : ContinuousOn (fun t => ‖fderiv ℝ (f t) (α t)‖) (Icc tmin tmax) :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc tmin tmax) := isCompact_Icc
    have hne : (Icc tmin tmax).Nonempty := ⟨tmin, left_mem_Icc.mpr hle⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨t₁, _, ht₁_max⟩
    exact ⟨‖fderiv ℝ (f t₁) (α t₁)‖, norm_nonneg _, fun t ht => ht₁_max ht⟩
  · refine ⟨0, le_rfl, fun t ht => ?_⟩
    exact absurd (lt_of_le_of_lt ht.1 (lt_of_le_of_lt ht.2 hlt)) (lt_irrefl _)

end Linearization

section Uniqueness

variable {f : ℝ → E → E} {α : ℝ → E} {δ : E} {t₀ : ℝ}

theorem IsVariationalSolutionOn.unique_Ioo {a b : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {y₁ y₂ : ℝ → E}
    (h₁ : IsVariationalSolutionOn f α δ t₀ y₁ (Ioo a b))
    (h₂ : IsVariationalSolutionOn f α δ t₀ y₂ (Ioo a b))
    (hcont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Ioo a b)) :
    EqOn y₁ y₂ (Ioo a b) := by
  intro t ht
  set A : ℝ → E →L[ℝ] E := fun t => fderiv ℝ (f t) (α t) with hA_def
  let v : ℝ → E → E := fun t y => (A t) y
  set a' := (a + min t t₀) / 2 with ha'
  set b' := (b + max t t₀) / 2 with hb'
  have hmin_lt : a < min t t₀ := lt_min ht.1 ht₀.1
  have hmax_lt : max t t₀ < b := max_lt ht.2 ht₀.2
  have hmin_le_t : min t t₀ ≤ t := min_le_left _ _
  have hmin_le_t₀ : min t t₀ ≤ t₀ := min_le_right _ _
  have ht_le_max : t ≤ max t t₀ := le_max_left _ _
  have ht₀_le_max : t₀ ≤ max t t₀ := le_max_right _ _
  have ha'_lt_min : a' < min t t₀ := by rw [ha']; linarith
  have ha_lt_a' : a < a' := by rw [ha']; linarith
  have hmax_lt_b' : max t t₀ < b' := by rw [hb']; linarith
  have hb'_lt_b : b' < b := by rw [hb']; linarith
  have hsub : Ioo a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_trans ha_lt_a' hs.1, lt_trans hs.2 hb'_lt_b⟩
  have ht_mem' : t ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t, lt_of_le_of_lt ht_le_max hmax_lt_b'⟩
  have ht₀_mem' : t₀ ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t₀, lt_of_le_of_lt ht₀_le_max hmax_lt_b'⟩
  have hab_le : a' ≤ b' := le_of_lt (lt_trans ha'_lt_min (lt_of_le_of_lt hmin_le_t
    (lt_of_lt_of_le ht_mem'.2 (le_refl _))))
  have hIcc_sub : Icc a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_a' hs.1, lt_of_le_of_lt hs.2 hb'_lt_b⟩
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc a' b', ‖A τ‖ ≤ M := by
    have hcont' : ContinuousOn A (Icc a' b') := hcont.mono hIcc_sub
    have hcont_norm : ContinuousOn (fun τ => ‖A τ‖) (Icc a' b') :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc a' b') := isCompact_Icc
    have hne : (Icc a' b').Nonempty := ⟨a', left_mem_Icc.mpr hab_le⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖A τ₁‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  obtain ⟨M, hM_nn, hMbd⟩ := hbd
  let K : ℝ≥0 := ⟨M, hM_nn⟩
  have hv_lip : ∀ τ ∈ Ioo a' b', LipschitzOnWith K (v τ) univ := by
    intro τ hτ
    have hlip : LipschitzWith K (A τ) :=
      (A τ).lipschitzWith_of_opNorm_le (hMbd τ (Ioo_subset_Icc_self hτ))
    exact (LipschitzWith.lipschitzOnWith (s := (univ : Set E)) hlip)
  have hy₁_d : ∀ τ ∈ Ioo a' b',
      HasDerivAt y₁ ((A τ) (y₁ τ)) τ := by
    intro τ hτ
    exact (h₁.2 τ (hsub hτ)).hasDerivAt (isOpen_Ioo.mem_nhds (hsub hτ))
  have hy₂_d : ∀ τ ∈ Ioo a' b',
      HasDerivAt y₂ ((A τ) (y₂ τ)) τ := by
    intro τ hτ
    exact (h₂.2 τ (hsub hτ)).hasDerivAt (isOpen_Ioo.mem_nhds (hsub hτ))
  exact (ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => univ) (K := K)
    hv_lip ht₀_mem'
    (fun τ hτ => ⟨hy₁_d τ hτ, mem_univ _⟩)
    (fun τ hτ => ⟨hy₂_d τ hτ, mem_univ _⟩)
    (by rw [h₁.1, h₂.1])) ht_mem'

end Uniqueness

section Existence

variable [CompleteSpace E]

theorem exists_isVariationalSolutionOn_Ioo_local
    {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E}
    (hf : ContDiffOn ℝ 1 (uncurry f) (s ×ˢ u)) (hs : IsOpen s) (hu : IsOpen u)
    (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s) (δ : E) :
    ∃ ε : ℝ, 0 < ε ∧ Ioo (t₀ - ε) (t₀ + ε) ⊆ s ∧
      ∃ y : ℝ → E, IsVariationalSolutionOn f α δ t₀ y (Ioo (t₀ - ε) (t₀ + ε)) := by
  have hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) s :=
    continuousOn_fderiv_along_curve hf hs hu hα hmem
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds ht₀) with ⟨ε₀, hε₀, hball⟩
  set ε := ε₀ / 2 with hε_def
  have hε : 0 < ε := by positivity
  have hε_lt : ε < ε₀ := half_lt_self hε₀
  have hIcc_sub_ball : Icc (t₀ - ε) (t₀ + ε) ⊆ Metric.ball t₀ ε₀ := by
    intro τ hτ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩
    · linarith [hτ.1, hε_lt]
    · linarith [hτ.2, hε_lt]
  have hIcc_sub_s : Icc (t₀ - ε) (t₀ + ε) ⊆ s := hIcc_sub_ball.trans hball
  obtain ⟨M, hM_nn, hMbd⟩ :=
    exists_bound_fderiv_along_curve_Icc hf hs hu hα hmem hIcc_sub_s
  set A : ℝ → E →L[ℝ] E := fun t => fderiv ℝ (f t) (α t) with hA_def
  set v : ℝ → E → E := fun t y => (A t) y with hv_def
  set r : ℝ := ‖δ‖ with hr_def
  have hr_nn : 0 ≤ r := norm_nonneg _
  set a : ℝ := r + 1 with ha_def
  have ha_pos : 0 < a := by linarith
  set ε' : ℝ := min ε (1 / (M * a + 1)) with hε'_def
  have hε' : 0 < ε' := by
    apply lt_min hε
    apply div_pos one_pos
    have : 0 ≤ M * a := mul_nonneg hM_nn (le_of_lt ha_pos)
    linarith
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hMa_eps' : M * a * ε' ≤ 1 := by
    have h1 : ε' ≤ 1 / (M * a + 1) := min_le_right _ _
    have hMa_nn : 0 ≤ M * a := mul_nonneg hM_nn (le_of_lt ha_pos)
    have hMa1_pos : 0 < M * a + 1 := by linarith
    have h2 : M * a * ε' ≤ M * a * (1 / (M * a + 1)) :=
      mul_le_mul_of_nonneg_left h1 hMa_nn
    have h3 : M * a * (1 / (M * a + 1)) = M * a / (M * a + 1) := by ring
    have h4 : M * a / (M * a + 1) ≤ 1 := by
      rw [div_le_one hMa1_pos]; linarith
    linarith
  let tmin : ℝ := t₀ - ε'
  let tmax : ℝ := t₀ + ε'
  have htmin_le_tmax : tmin ≤ tmax := by
    change t₀ - ε' ≤ t₀ + ε'; linarith
  let t₀Icc : Icc tmin tmax := ⟨t₀, by exact ⟨by change t₀ - ε' ≤ t₀; linarith,
    by change t₀ ≤ t₀ + ε'; linarith⟩⟩
  have hIcc_sub_eps : Icc tmin tmax ⊆ Icc (t₀ - ε) (t₀ + ε) := by
    intro τ hτ
    refine ⟨?_, ?_⟩
    · exact le_trans (by change t₀ - ε ≤ t₀ - ε'; linarith) hτ.1
    · exact le_trans hτ.2 (by change t₀ + ε' ≤ t₀ + ε; linarith)
  let aN : ℝ≥0 := ⟨a, le_of_lt ha_pos⟩
  let rN : ℝ≥0 := ⟨r, hr_nn⟩
  let LN : ℝ≥0 := ⟨M * a, mul_nonneg hM_nn (le_of_lt ha_pos)⟩
  let KN : ℝ≥0 := ⟨M, hM_nn⟩
  have hpl : IsPicardLindelof v t₀Icc (0 : E) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro τ hτ
      have hτ_eps : τ ∈ Icc (t₀ - ε) (t₀ + ε) := hIcc_sub_eps hτ
      have hlip : LipschitzWith KN (A τ) :=
        (A τ).lipschitzWith_of_opNorm_le (hMbd τ hτ_eps)
      exact LipschitzWith.lipschitzOnWith (s := closedBall (0 : E) aN) hlip
    · intro y _
      have hsub : Icc tmin tmax ⊆ s := hIcc_sub_eps.trans hIcc_sub_s
      have hA_cont' : ContinuousOn A (Icc tmin tmax) := hA_cont.mono hsub
      have happly : Continuous (fun B : E →L[ℝ] E => B y) :=
        (ContinuousLinearMap.apply ℝ E y).continuous
      exact happly.comp_continuousOn hA_cont'
    · intro τ hτ y hy
      have hτ_eps : τ ∈ Icc (t₀ - ε) (t₀ + ε) := hIcc_sub_eps hτ
      have hA_norm : ‖A τ‖ ≤ M := hMbd τ hτ_eps
      have hy_norm : ‖y‖ ≤ a := by
        rw [mem_closedBall_zero_iff] at hy
        change ‖y‖ ≤ a at hy
        exact hy
      change ‖v τ y‖ ≤ (LN : ℝ)
      calc ‖v τ y‖ = ‖(A τ) y‖ := rfl
        _ ≤ ‖A τ‖ * ‖y‖ := (A τ).le_opNorm y
        _ ≤ M * a := mul_le_mul hA_norm hy_norm (norm_nonneg _) hM_nn
    · change (LN : ℝ) * max (tmax - t₀) (t₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - t₀) (t₀ - tmin) = ε' := by
        have h1 : tmax - t₀ = ε' := by change (t₀ + ε') - t₀ = ε'; ring
        have h2 : t₀ - tmin = ε' := by change t₀ - (t₀ - ε') = ε'; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      have hLrhs : (aN : ℝ) - (rN : ℝ) = 1 := by change a - r = 1; rw [ha_def]; ring
      rw [hLrhs]
      change M * a * ε' ≤ 1
      exact hMa_eps'
  have hδ_mem : δ ∈ closedBall (0 : E) rN := by
    rw [mem_closedBall_zero_iff]
    change ‖δ‖ ≤ r
    rfl
  obtain ⟨y, hy_initial, hy_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hδ_mem
  refine ⟨ε', hε', ?_, y, hy_initial, ?_⟩
  · intro τ hτ
    apply hIcc_sub_s
    refine ⟨le_of_lt ?_, le_of_lt ?_⟩
    · exact lt_of_le_of_lt (by change t₀ - ε ≤ t₀ - ε'; linarith) hτ.1
    · exact lt_of_lt_of_le hτ.2 (by change t₀ + ε' ≤ t₀ + ε; linarith)
  · intro τ hτ
    have hτ_Icc : τ ∈ Icc tmin tmax :=
      ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    have hd := hy_deriv τ hτ_Icc
    have hsub_set : Ioo (t₀ - ε') (t₀ + ε') ⊆ Icc tmin tmax :=
      Ioo_subset_Icc_self
    have hd' := hd.mono hsub_set
    have hτ_open : Ioo (t₀ - ε') (t₀ + ε') ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
    exact (hd'.hasDerivAt hτ_open).hasDerivWithinAt

end Existence

section Linearity

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

theorem IsVariationalSolutionOn.linear_combination
    {δ₁ δ₂ : E} {c₁ c₂ : ℝ} {y₁ y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsVariationalSolutionOn f α δ₁ t₀ y₁ s)
    (h₂ : IsVariationalSolutionOn f α δ₂ t₀ y₂ s) :
    IsVariationalSolutionOn f α (c₁ • δ₁ + c₂ • δ₂) t₀
      (fun t => c₁ • y₁ t + c₂ • y₂ t) s := by
  refine ⟨?_, ?_⟩
  · simp [h₁.1, h₂.1]
  · intro t ht
    have hd₁ := h₁.2 t ht
    have hd₂ := h₂.2 t ht
    have hd_sum : HasDerivWithinAt (fun t => c₁ • y₁ t + c₂ • y₂ t)
        (c₁ • ((fderiv ℝ (f t) (α t)) (y₁ t)) + c₂ • ((fderiv ℝ (f t) (α t)) (y₂ t))) s t :=
      (hd₁.const_smul c₁).add (hd₂.const_smul c₂)
    have hlin :
        (fderiv ℝ (f t) (α t)) (c₁ • y₁ t + c₂ • y₂ t)
          = c₁ • ((fderiv ℝ (f t) (α t)) (y₁ t))
              + c₂ • ((fderiv ℝ (f t) (α t)) (y₂ t)) := by
      simp [map_add]
    rw [hlin]
    exact hd_sum

theorem IsVariationalSolutionOn.const_smul
    {δ : E} {c : ℝ} {y : ℝ → E} {s : Set ℝ}
    (h : IsVariationalSolutionOn f α δ t₀ y s) :
    IsVariationalSolutionOn f α (c • δ) t₀ (fun t => c • y t) s := by
  have h₂ : IsVariationalSolutionOn f α (0 : E) t₀ (fun _ => (0 : E)) s := by
    refine ⟨by simp, ?_⟩
    intro t _
    have hz : ((fderiv ℝ (f t) (α t)) (0 : E)) = 0 := by simp
    rw [hz]
    exact hasDerivWithinAt_const t s (0 : E)
  have hcomb := h.linear_combination (c₁ := c) (c₂ := 0) h₂
  simpa using hcomb

theorem IsVariationalSolutionOn.add
    {δ₁ δ₂ : E} {y₁ y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsVariationalSolutionOn f α δ₁ t₀ y₁ s)
    (h₂ : IsVariationalSolutionOn f α δ₂ t₀ y₂ s) :
    IsVariationalSolutionOn f α (δ₁ + δ₂) t₀ (fun t => y₁ t + y₂ t) s := by
  have hcomb := h₁.linear_combination (c₁ := 1) (c₂ := 1) h₂
  simpa using hcomb

theorem IsVariationalSolutionOn.zero
    {s : Set ℝ} :
    IsVariationalSolutionOn f α (0 : E) t₀ (fun _ => (0 : E)) s := by
  refine ⟨by simp, ?_⟩
  intro t _
  have hz : ((fderiv ℝ (f t) (α t)) (0 : E)) = 0 := by simp
  rw [hz]
  exact hasDerivWithinAt_const t s (0 : E)

end Linearity

end ODE
end Analysis
end DifferentialGeometry

end
