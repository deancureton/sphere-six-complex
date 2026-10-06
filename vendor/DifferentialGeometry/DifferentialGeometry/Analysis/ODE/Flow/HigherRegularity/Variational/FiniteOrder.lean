module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.FiniteOrder

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section AugmentedVectorFieldDefinition

def augmentedVectorField (f : ℝ → E → E) : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E)) :=
  fun t p => (f t p.1, ((fderiv ℝ (f t) p.1).comp p.2))

omit [CompleteSpace E] in
@[simp]
lemma augmentedVectorField_apply (f : ℝ → E → E) (t : ℝ) (x : E) (Z : E →L[ℝ] E) :
    augmentedVectorField f t (x, Z) = (f t x, ((fderiv ℝ (f t) x).comp Z)) := rfl

end AugmentedVectorFieldDefinition

section PartialFDerivSmoothness

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
lemma partial_fderiv_eq_comp_inr_on_univ
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∀ p : ℝ × E, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p := by
    have hp_open : (Set.univ : Set (ℝ × E)) ∈ 𝓝 p := isOpen_univ.mem_nhds (mem_univ _)
    exact (hf.contDiffAt hp_open).differentiableAt one_ne_zero
  exact fderiv_eq_comp_inr hdiff_joint

omit [CompleteSpace E] in
theorem contDiffOn_partial_fderiv_of_succ
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)) := by
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) := by
    have h : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) :=
      hf_succ.fderiv_of_isOpen isOpen_univ le_rfl
    exact h
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    rfl
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) (Set.univ : Set (ℝ × E)) :=
    hfderiv_Ck.continuousLinearMap_comp postL
  have heq : ∀ p ∈ (Set.univ : Set (ℝ × E)),
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p _
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast h1
      have := hf_succ.of_le h1'
      simpa using this
    have h := partial_fderiv_eq_comp_inr_on_univ hf_C1 p
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq


omit [CompleteSpace E] in
lemma partial_fderiv_eq_comp_inr_on_open
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 (uncurry f) Ω) :
    ∀ p ∈ Ω, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p hp
  have hp_open : Ω ∈ 𝓝 p := hΩ.mem_nhds hp
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p :=
    ((hf.contDiffAt hp_open).differentiableAt one_ne_zero)
  exact fderiv_eq_comp_inr hdiff_joint

omit [CompleteSpace E] in
theorem contDiffOn_partial_fderiv_of_succ_local
    {k : ℕ∞} {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) Ω) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Ω := by
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) Ω :=
    hf_succ.fderiv_of_isOpen hΩ le_rfl
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    rfl
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) Ω :=
    hfderiv_Ck.continuousLinearMap_comp postL
  have heq : ∀ p ∈ Ω,
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p hp
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast h1
      exact hf_succ.of_le h1'
    have h := partial_fderiv_eq_comp_inr_on_open hΩ hf_C1 p hp
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

end PartialFDerivSmoothness

section AugmentedVectorFieldSmoothness

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
theorem augmentedVectorField_uncurry_contDiff
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  set proj1 : ℝ × (E × (E →L[ℝ] E)) → ℝ × E := fun q => (q.1, q.2.1) with hproj1_def
  have hproj1_Ck : ContDiffOn ℝ k proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact contDiff_fst.contDiffOn
    · exact (contDiff_fst.comp contDiff_snd).contDiffOn
  have hmaps1 : MapsTo proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_succ.of_le h_le
  have hcomp1 : ContDiffOn ℝ k (uncurry f ∘ proj1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hf_Ck.comp hproj1_Ck hmaps1
  have heq1 : (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1) = uncurry f ∘ proj1 := by
    funext q; rfl
  have hC1 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq1]; exact hcomp1
  have hpartial_Ck := contDiffOn_partial_fderiv_of_succ hf_succ
  have hA_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (f q.1) q.2.1) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have hcomp := hpartial_Ck.comp hproj1_Ck hmaps1
    have heq : (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) ∘ proj1
        = (fun q : ℝ × (E × (E →L[ℝ] E)) => fderiv ℝ (f q.1) q.2.1) := by
      funext q; rfl
    rw [← heq]; exact hcomp
  have hZ_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hpair_Ck : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hA_Ck.prodMk hZ_Ck
  have hbilin_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).contDiff
  have hbilin_Ck : ContDiffOn ℝ k
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2)
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := hbilin_smooth.contDiffOn
  have hmaps_pair : MapsTo (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hC2_pre : ContDiffOn ℝ k
      ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
       (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hbilin_Ck.comp hpair_Ck hmaps_pair
  have heq2 : ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
        (fun q : ℝ × (E × (E →L[ℝ] E)) =>
         ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      = (fun q : ℝ × (E × (E →L[ℝ] E)) =>
          (fderiv ℝ (f q.1) q.2.1).comp q.2.2) := by
    funext q; rfl
  have hC2 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (fderiv ℝ (f q.1) q.2.1).comp q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq2] at hC2_pre; exact hC2_pre
  have hpair_final : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hC1.prodMk hC2
  have heq_final : (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      = uncurry (augmentedVectorField f) := by
    funext q; rfl
  rw [heq_final] at hpair_final
  exact hpair_final

omit [CompleteSpace E] in
theorem augmentedVectorField_uncurry_continuousOn_of_C1
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContinuousOn (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  have hf_succ : ContDiffOn ℝ ((0 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C1
  have h := augmentedVectorField_uncurry_contDiff (k := (0 : ℕ∞)) hf_succ
  exact contDiffOn_zero.mp h

end AugmentedVectorFieldSmoothness

section NestingData

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem continuousOn_fderiv_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun p : E × ℝ => fderiv ℝ (f p.2) (Φ p))
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have hΦcont : ContinuousOn Φ ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    hΦ.continuousOn.mono (Set.prod_mono (closedBall_subset_closedBall hρ) (le_refl _))
  have hmap : ContinuousOn (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    (continuousOn_snd).prodMk hΦcont
  have hmaps : MapsTo (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  exact hpartial.comp hmap hmaps

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem exists_norm_fderiv_le_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ : ρ ≤ (r : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall x₀ ρ, ∀ τ ∈ Icc tmin tmax,
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
  have hcont := continuousOn_fderiv_along_flow_joint hΦ hf hρ
  have hcontN : ContinuousOn (fun p : E × ℝ => ‖fderiv ℝ (f p.2) (Φ p)‖)
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := continuous_norm.comp_continuousOn hcont
  have hcompact : IsCompact ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) :=
    (isCompact_closedBall x₀ ρ).prod isCompact_Icc
  have hne : ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)).Nonempty :=
    ⟨(x₀, t₀), ⟨mem_closedBall_self hρ_nonneg, hΦ.t₀_mem_Icc⟩⟩
  obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
  use ‖fderiv ℝ (f p.2) (Φ p)‖, norm_nonneg _
  intro x hx τ hτ
  have hmem : ((x, τ) : E × ℝ) ∈ (closedBall x₀ ρ) ×ˢ (Icc tmin tmax) := ⟨hx, hτ⟩
  exact hp_max hmem

omit [CompleteSpace E] in
theorem exists_lipschitzOnWith_closedBall_of_C1
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (x₀ : E) (ρ : ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (closedBall x₀ ρ) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have hcontN : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖)
      ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    (continuous_norm.comp_continuousOn (hpartial.mono (subset_univ _)))
  have hcompact : IsCompact ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ ρ)
  have hdiff : ∀ t : ℝ, ∀ x : E, DifferentiableAt ℝ (f t) x := by
    intro t x
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (t, x) :=
      (hf.contDiffAt (isOpen_univ.mem_nhds (mem_univ _))).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (t, y)) x :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact hDiff_joint.comp x hg
  by_cases hball : (closedBall x₀ ρ).Nonempty
  · obtain ⟨x₁, hx₁⟩ := hball
    have hne : ((Icc a b) ×ˢ (closedBall x₀ ρ)).Nonempty := ⟨(a, x₁), ⟨⟨le_rfl, hab⟩, hx₁⟩⟩
    obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
    set C : ℝ := ‖fderiv ℝ (f p.1) p.2‖ with hC_def
    let K : ℝ≥0 := ⟨C, norm_nonneg _⟩
    have hK : ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (closedBall x₀ ρ) := by
      intro t ht
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        (fun x _ => hdiff t x) ?_ (convex_closedBall x₀ ρ)
      intro x hx
      have hmem : ((t, x) : ℝ × E) ∈ (Icc a b) ×ˢ (closedBall x₀ ρ) :=
        Set.mem_prod.mpr ⟨ht, hx⟩
      have : ‖fderiv ℝ (f t) x‖ ≤ C := hp_max hmem
      rw [← NNReal.coe_le_coe]
      change ‖fderiv ℝ (f t) x‖ ≤ C
      exact this
    exact Exists.intro K hK
  · have hK : ∀ t ∈ Icc a b, LipschitzOnWith 0 (f t) (closedBall x₀ ρ) := by
      intro t _
      rw [not_nonempty_iff_eq_empty] at hball
      rw [hball]
      exact lipschitzOnWith_empty 0 (f t)
    exact Exists.intro 0 hK

omit [CompleteSpace E] in
theorem exists_flow_nesting_parameters
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ (T_out T_mid T M : ℝ) (ρ_out ρ_mid ρ r' : ℝ≥0),
      0 < T ∧ T < T_mid ∧ T_mid < T_out ∧ 0 ≤ M ∧ M * T_mid < 1 ∧ 0 < (r' : ℝ) ∧
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < (ρ_mid : ℝ) ∧ (ρ_mid : ℝ) < (ρ_out : ℝ) ∧
      (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) ∧ (ρ_out : ℝ) ≤ (r : ℝ) ∧
      Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax ∧
      (∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) := by
  let ρ_out : ℝ≥0 := r / 2
  let ρ_mid : ℝ≥0 := r / 4
  let ρ : ℝ≥0 := r / 8
  let r' : ℝ≥0 := r / 2
  have hρ_out_coe : (ρ_out : ℝ) = (r : ℝ) / 2 := by simp only [ρ_out]; push_cast; ring
  have hρ_mid_coe : (ρ_mid : ℝ) = (r : ℝ) / 4 := by simp only [ρ_mid]; push_cast; ring
  have hρ_coe : (ρ : ℝ) = (r : ℝ) / 8 := by simp only [ρ]; push_cast; ring
  have hr'_coe : (r' : ℝ) = (r : ℝ) / 2 := by simp only [r']; push_cast; ring
  have hρ_pos : 0 < (ρ : ℝ) := by rw [hρ_coe]; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by rw [hρ_coe, hρ_mid_coe]; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by rw [hρ_mid_coe, hρ_out_coe]; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by rw [hρ_mid_coe, hr'_coe]; linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ) := by rw [hρ_out_coe]; linarith
  have hr'_pos : 0 < (r' : ℝ) := by rw [hr'_coe]; linarith
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_out : ℝ := d / 2 with hT_out_def
  have hT_out_pos : 0 < T_out := by rw [hT_out_def]; linarith
  have hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have : d ≤ t₀ - tmin := min_le_left _ _
      rw [hT_out_def]; linarith
    · have : d ≤ tmax - t₀ := min_le_right _ _
      rw [hT_out_def]; linarith
  obtain ⟨M, hM_nonneg, hM_bd⟩ :=
    exists_norm_fderiv_le_along_flow_joint hΦ hf (ρ := (ρ_out : ℝ))
      (NNReal.coe_nonneg ρ_out) hρ_out_le_r
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    exact hM_bd x hx τ (hsub hτ)
  set T_mid : ℝ := min (T_out / 2) (1 / (2 * (M + 1))) with hT_mid_def
  have hM1_pos : 0 < 2 * (M + 1) := by linarith
  have hT_mid_pos : 0 < T_mid := lt_min (by linarith) (by positivity)
  have hT_mid_lt_out : T_mid < T_out := by
    calc T_mid ≤ T_out / 2 := min_le_left _ _
      _ < T_out := by linarith
  set T : ℝ := T_mid / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_lt_mid : T < T_mid := by rw [hT_def]; linarith
  have hMT_mid : M * T_mid < 1 := by
    have hle : T_mid ≤ 1 / (2 * (M + 1)) := min_le_right _ _
    have hM_T_mid : M * T_mid ≤ M * (1 / (2 * (M + 1))) := by
      apply mul_le_mul_of_nonneg_left hle hM_nonneg
    calc M * T_mid ≤ M * (1 / (2 * (M + 1))) := hM_T_mid
      _ = M / (2 * (M + 1)) := by ring
      _ < 1 := by
          rw [div_lt_one hM1_pos]; linarith
  exact ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT_pos, hT_lt_mid, hT_mid_lt_out,
    hM_nonneg, hMT_mid, hr'_pos, hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r,
    hsub, hA_bd⟩

end NestingData

section ProjectionPredicate

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

structure IsVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) (T : ℝ) (ρ : ℝ≥0)
    (Y : E × ℝ → (E →L[ℝ] E)) (k : ℕ∞) : Prop where
  contDiffOn : ContDiffOn ℝ k Y ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))
  fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
    fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q)

omit [CompleteSpace E] in
lemma IsVariationalFlowProjection.of_le {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T : ℝ} {ρ : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k j : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) (hjk : j ≤ k) :
    IsVariationalFlowProjection hΦ T ρ Y j := by
  refine
  { contDiffOn := ?_,
    fderiv_eq := hY.fderiv_eq }
  have hjk' : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
  exact hY.contDiffOn.of_le hjk'

end ProjectionPredicate

section RecursiveFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_succ_of_isVariationalFlowProjection
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
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
  contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck
    hY.contDiffOn hY.fderiv_eq

theorem contDiffOn_flow_of_isVariationalFlowProjection_seq
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
    (Y_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hY_seq : ∀ j : ℕ, j + 1 ≤ k →
      IsVariationalFlowProjection hΦ T ρ (Y_seq j) (j : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  refine contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_ ?_
  · intro j hj
    exact (hY_seq j hj).contDiffOn
  · intro j hj
    exact (hY_seq j hj).fderiv_eq

theorem contDiffOn_flow_of_isVariationalFlowProjection_top
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
    (k : ℕ) (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y ((k - 1 : ℕ) : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun _ => Y with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  have hj_le : (j : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
    have h : j ≤ k - 1 := by omega
    exact_mod_cast h
  exact hY.of_le hj_le

end RecursiveFlow

section FderivCoprodIdentity

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

def spatialPieceFn (Φ : E × ℝ → E) : E × ℝ → (E →L[ℝ] E) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [CompleteSpace E] in
@[simp]
lemma spatialPieceFn_apply (Φ : E × ℝ → E) (q : E × ℝ) :
    spatialPieceFn Φ q = (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) := rfl

theorem fderiv_flow_eq_coprod_spatialPiece
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) := by
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hρ_mid_pos : 0 < (ρ_mid : ℝ) := lt_of_le_of_lt (ρ.coe_nonneg) hρ_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ), ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ =>
    hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  intro q hq
  rcases hq with ⟨hq_x, hq_t⟩
  rw [mem_ball] at hq_x
  obtain ⟨x, t⟩ := q
  have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
    mem_closedBall.mpr (le_of_lt (lt_trans hq_x hρ_lt_mid))
  have hq_t_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨by linarith [hq_t.1], by linarith [hq_t.2]⟩
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ'
    hA_bd_mid hx_cb_mid hq_t_mid
  have hfd_eq := hfd_at.fderiv
  set Lsp : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid
      (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
          rw [mem_closedBall] at hx_cb_mid; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub_mid)
      (fun τ hτ => hA_bd_mid x hx_cb_mid τ hτ) (Ioo_subset_Icc_self hq_t_mid) with hLsp_def
  set Lti : ℝ →L[ℝ] E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩)) with hLti_def
  have hti_eq : timePieceFn f Φ (x, t) = Lti := rfl
  have hsp_eq : spatialPieceFn Φ (x, t) = Lsp := by
    rw [spatialPieceFn_apply, hfd_eq]
    exact ContinuousLinearMap.coprod_comp_inl Lsp Lti
  rw [hsp_eq, hti_eq, hfd_eq]

end FderivCoprodIdentity

section LevelTwo

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_isLocalFlow_augmentedVectorField_of_C2
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (p₀ : E × (E →L[ℝ] E)) :
    ∃ (R : ℝ≥0) (ε : ℝ) (_ : 0 < R) (_ : 0 < ε)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      IsLocalFlow (augmentedVectorField f) t₀ p₀ R (t₀ - ε) (t₀ + ε) aΦ := by
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_augmentedVectorField_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augmentedVectorField_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  exact exists_isLocalFlow_of_contDiffOn_univ (augmentedVectorField f) h_augmentedVectorField_C1 t₀ p₀

theorem contDiffOn_flow_of_isLocalFlow_C2_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y 1) :
    ContDiffOn ℝ 2 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hΦ_C1 : ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_step := contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid
    hT_mid_lt_out hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
    (k := (1 : ℕ∞)) hf_succ hΦ_C1 hY
  norm_num at h_step
  exact h_step

end LevelTwo

section AugmentedFlowProjection

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

def fromAugmentedFlow (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)) :
    E × ℝ → (E →L[ℝ] E) :=
  fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).2

omit [CompleteSpace E] in
@[simp]
lemma fromAugmentedFlow_apply (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (x : E) (t : ℝ) :
    fromAugmentedFlow aΦ (x, t) = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := rfl

omit [CompleteSpace E] in
theorem contDiffOn_fromAugmentedFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {k : ℕ∞} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} {U : Set (E × ℝ)}
    (haΦ : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U Ω) :
    ContDiffOn ℝ k (fromAugmentedFlow aΦ) U := by
  have h_embed_smooth : ContDiff ℝ (k : ℕ∞)
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) := by
    refine ContDiff.prodMk ?_ contDiff_snd
    refine ContDiff.prodMk contDiff_fst ?_
    exact contDiff_const
  have h_embed_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) U :=
    h_embed_smooth.contDiffOn
  have hcomp : ContDiffOn ℝ k (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U :=
    haΦ.comp h_embed_Ck hmap
  have hsnd_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : E × (E →L[ℝ] E) => p.2) := contDiff_snd
  have hsnd_Ck : ContDiffOn ℝ k (fun p : E × (E →L[ℝ] E) => p.2)
      (Set.univ : Set (E × (E →L[ℝ] E))) := hsnd_smooth.contDiffOn
  have hmaps : MapsTo (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U
      (Set.univ : Set (E × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hfinal : ContDiffOn ℝ k
      ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2)))) U :=
    hsnd_Ck.comp hcomp hmaps
  have heq : ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2))))
      = fromAugmentedFlow aΦ := by
    funext q
    rfl
  rw [heq] at hfinal
  exact hfinal

end AugmentedFlowProjection

section Abstract

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_succ_of_augmentedFlow
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
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugmentedFlow aΦ q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hY_Ck : ContDiffOn ℝ k (fromAugmentedFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugmentedFlow haΦ_Ck hmap
  have hY : IsVariationalFlowProjection hΦ T ρ (fromAugmentedFlow aΦ) k :=
    { contDiffOn := hY_Ck, fderiv_eq := h_fderiv_eq }
  exact contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hY

end Abstract

section AggregatedPublic

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_of_augmentedFlow_seq
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
    (aΦ_seq : ℕ → (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (Ω_seq : ℕ → Set ((E × (E →L[ℝ] E)) × ℝ))
    (haΦ_Ck : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (aΦ_seq j) (Ω_seq j))
    (hmap_seq : ∀ j : ℕ, j + 1 ≤ k →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) (Ω_seq j))
    (h_fderiv_eq_seq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugmentedFlow (aΦ_seq j) q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun j => fromAugmentedFlow (aΦ_seq j) with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  refine
  { contDiffOn := contDiffOn_fromAugmentedFlow (haΦ_Ck j hj) (hmap_seq j hj),
    fderiv_eq := h_fderiv_eq_seq j hj }

end AggregatedPublic

section OperatorVariational

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
lemma hasDerivWithinAt_apply {Z Z' : ℝ → (E →L[ℝ] E)} {s : Set ℝ} {t : ℝ} {δ : E}
    (hZ : HasDerivWithinAt Z (Z' t) s t) :
    HasDerivWithinAt (fun τ => Z τ δ) ((Z' t) δ) s t := by
  set applyδ : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E δ
  have happ : HasFDerivAt applyδ applyδ (Z t) := applyδ.hasFDerivAt
  have hZ_fd : HasFDerivWithinAt Z
      (ContinuousLinearMap.toSpanSingleton ℝ (Z' t)) s t := hZ.hasFDerivWithinAt
  have happ_fd := happ.comp_hasFDerivWithinAt t hZ_fd
  have heq : applyδ.comp (ContinuousLinearMap.toSpanSingleton ℝ (Z' t))
      = ContinuousLinearMap.toSpanSingleton ℝ ((Z' t) δ) := by
    apply ContinuousLinearMap.ext
    intro r
    simp [applyδ, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
  rw [heq] at happ_fd
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact happ_fd

omit [CompleteSpace E] in
theorem isVariationalSolutionOn_apply
    {T : ℝ}
    {Z : ℝ → E →L[ℝ] E}
    (hZ_initial : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    (δ : E) :
    IsVariationalSolutionOn f α δ t₀ (fun s => Z s δ) (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨?_, ?_⟩
  · have : Z t₀ δ = ContinuousLinearMap.id ℝ E δ := by rw [hZ_initial]
    simpa using this
  · intro t ht
    have hZ_d := hZ_deriv t ht
    have happ := hasDerivWithinAt_apply (Z := Z)
      (Z' := fun s => (fderiv ℝ (f s) (α s)).comp (Z s)) (δ := δ) hZ_d
    have hsimp : ((fderiv ℝ (f t) (α t)).comp (Z t)) δ
        = (fderiv ℝ (f t) (α t)) (Z t δ) := by rfl
    rw [hsimp] at happ
    exact happ

theorem Z_eq_variationalLinearMapAt
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {Z : ℝ → E →L[ℝ] E}
    (hZ_initial : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    Z t = variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht := by
  apply ContinuousLinearMap.ext
  intro δ
  have h_Z_solution := isVariationalSolutionOn_apply (T := T) (Z := Z) hZ_initial hZ_deriv δ
  have h_var_solution := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont h_Z_solution h_var_solution
  have hZδ_t : Z t δ
      = variationalSolutionFun (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd δ t :=
    h_eq ht
  rw [hZδ_t]
  exact (variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht δ).symm

end OperatorVariational

section AugmentedFlowVariationalIdentification

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem augmentedFlow_snd_eq_variationalLinearMapAt
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    {p₀ : E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ p₀ R tmin' tmax' aΦ)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    {x : E} (hx : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f t) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT hM hMT hA_cont hA_bd ht := by
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set orbit : ℝ → E × (E →L[ℝ] E) := fun s => aΦ ⟨p, s⟩ with horbit_def
  set Z : ℝ → E →L[ℝ] E := fun s => (orbit s).2 with hZ_def
  set α : ℝ → E := fun s => (orbit s).1 with hα_def
  have hZ_initial : Z t₀ = ContinuousLinearMap.id ℝ E := by
    have h_initial : orbit t₀ = p := haΦ.apply_initial p hx
    change (orbit t₀).2 = ContinuousLinearMap.id ℝ E
    rw [h_initial]
  have h_orbit_deriv : ∀ s ∈ Icc tmin' tmax',
      HasDerivWithinAt orbit (augmentedVectorField f s (orbit s)) (Icc tmin' tmax') s :=
    fun s hs => haΦ.hasDerivWithinAt p hx s hs
  have h_orbit_deriv' : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt orbit (augmentedVectorField f s (orbit s)) (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    exact (h_orbit_deriv s (hsub hs)).mono hsub
  have hZ_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f s) (α s)).comp (Z s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have h := h_orbit_deriv' s hs
    set sndCLM : (E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
      ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)
    have h_fd := h.hasFDerivWithinAt
    have h_snd_at := (sndCLM.hasFDerivAt).comp_hasFDerivWithinAt s h_fd
    have heq : sndCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
      (augmentedVectorField f s (orbit s)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augmentedVectorField f s (orbit s)).2) := by
      apply ContinuousLinearMap.ext
      intro r
      change (sndCLM (r • augmentedVectorField f s (orbit s)))
        = r • (augmentedVectorField f s (orbit s)).2
      change (r • augmentedVectorField f s (orbit s)).2 = r • (augmentedVectorField f s (orbit s)).2
      rfl
    rw [heq] at h_snd_at
    have h_aug_snd : (augmentedVectorField f s (orbit s)).2
        = (fderiv ℝ (f s) (α s)).comp (Z s) := rfl
    rw [h_aug_snd] at h_snd_at
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact h_snd_at
  exact Z_eq_variationalLinearMapAt hT hM hMT hA_cont hA_bd hZ_initial hZ_deriv ht

end AugmentedFlowVariationalIdentification

section UniformContainment

variable [FiniteDimensional ℝ E]
variable {x₀ : E} {t₀ tmin tmax : ℝ}

omit [CompleteSpace E] in
theorem exists_uniform_time_containment
    {ρ₀ : ℝ} (Ψ : E × ℝ → E)
    (hΨ_cont : ContinuousOn Ψ (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax))
    (hΨ_initial : ∀ x ∈ closedBall x₀ ρ₀, Ψ (x, t₀) = x)
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hρ₀_pos : 0 < ρ₀)
    {ρ_b : ℝ} (hρ_b_pos : 0 < ρ_b) :
    ∃ ρ_c > 0, ∃ T_c > 0, ρ_c ≤ ρ₀ ∧ Icc (t₀ - T_c) (t₀ + T_c) ⊆ Icc tmin tmax ∧
      ∀ x ∈ closedBall x₀ ρ_c, ∀ t ∈ Ioo (t₀ - T_c) (t₀ + T_c),
        Ψ (x, t) ∈ closedBall x₀ ρ_b := by
  have hcompact : IsCompact (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax) :=
    (isCompact_closedBall x₀ ρ₀).prod isCompact_Icc
  have huc : UniformContinuousOn Ψ (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax) :=
    hcompact.uniformContinuousOn_of_continuous hΨ_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (ρ_b / 2) (by positivity)
  set ρ_c : ℝ := min ρ₀ (ρ_b / 2) with hρ_c_def
  have hρ_c_pos : 0 < ρ_c := lt_min hρ₀_pos (by positivity)
  have hρ_c_le : ρ_c ≤ ρ₀ := min_le_left _ _
  have hρ_c_le_b : ρ_c ≤ ρ_b / 2 := min_le_right _ _
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_c : ℝ := min (δ / 2) (d / 2) with hT_c_def
  have hT_c_pos : 0 < T_c := lt_min (by linarith) (by linarith)
  have hT_c_lt_δ : T_c < δ := by
    calc T_c ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hsub : Icc (t₀ - T_c) (t₀ + T_c) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have hh : d ≤ t₀ - tmin := min_le_left _ _
      have ht : T_c ≤ d / 2 := min_le_right _ _
      linarith
    · have hh : d ≤ tmax - t₀ := min_le_right _ _
      have ht : T_c ≤ d / 2 := min_le_right _ _
      linarith
  refine ⟨ρ_c, hρ_c_pos, T_c, hT_c_pos, hρ_c_le, hsub, ?_⟩
  intro x hx t ht
  have hx₀ : x ∈ closedBall x₀ ρ₀ := closedBall_subset_closedBall hρ_c_le hx
  have ht_Icc : t ∈ Icc tmin tmax := hsub (Ioo_subset_Icc_self ht)
  have ht₀_Icc : t₀ ∈ Icc tmin tmax := ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩
  have hmem1 : ((x, t) : E × ℝ) ∈ closedBall x₀ ρ₀ ×ˢ Icc tmin tmax := ⟨hx₀, ht_Icc⟩
  have hmem2 : ((x, t₀) : E × ℝ) ∈ closedBall x₀ ρ₀ ×ˢ Icc tmin tmax := ⟨hx₀, ht₀_Icc⟩
  have hdist_xt : dist ((x, t) : E × ℝ) (x, t₀) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, max_eq_right (dist_nonneg)]
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1, hT_c_lt_δ], by linarith [ht.2, hT_c_lt_δ]⟩
  have hclose : dist (Ψ (x, t)) (Ψ (x, t₀)) < ρ_b / 2 := hδ _ hmem1 _ hmem2 hdist_xt
  rw [hΨ_initial x hx₀] at hclose
  rw [mem_closedBall]
  have hx_dist : dist x x₀ ≤ ρ_b / 2 := le_trans (mem_closedBall.mp hx) hρ_c_le_b
  calc dist (Ψ (x, t)) x₀ ≤ dist (Ψ (x, t)) x + dist x x₀ := dist_triangle _ _ _
    _ ≤ ρ_b / 2 + ρ_b / 2 := add_le_add (le_of_lt hclose) hx_dist
    _ = ρ_b := by ring

end UniformContainment

section OrbitUniqueness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem orbit_unique_Ioo
    {a b : ℝ} {y₁ y₂ : ℝ → E} {K : ℝ≥0} {c : E} {ρ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (closedBall c ρ))
    (hy₁ : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t)
    (hy₂ : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t)
    (hy₁_mem : ∀ t ∈ Ioo a b, y₁ t ∈ closedBall c ρ)
    (hy₂_mem : ∀ t ∈ Ioo a b, y₂ t ∈ closedBall c ρ)
    (hinit : y₁ t₀ = y₂ t₀) :
    EqOn y₁ y₂ (Ioo a b) := by
  exact ODE_solution_unique_of_mem_Ioo (v := fun t y => f t y)
    (s := fun _ => closedBall c ρ) (K := K)
    hLip ht₀
    (fun t ht => ⟨hy₁ t ht, hy₁_mem t ht⟩)
    (fun t ht => ⟨hy₂ t ht, hy₂_mem t ht⟩)
    hinit

omit [CompleteSpace E] in
theorem augmentedFlow_fst_eq_flow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {p₀ : E × (E →L[ℝ] E)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ p₀ R tmin' tmax' aΦ)
    {a b : ℝ} {K : ℝ≥0} {c : E} {ρ_b : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ha_sub : Ioo a b ⊆ Icc tmin tmax) (ha_sub' : Ioo a b ⊆ Icc tmin' tmax')
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (closedBall c ρ_b))
    {x : E} (hx : x ∈ closedBall x₀ (r : ℝ))
    (hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hy₁_mem : ∀ t ∈ Ioo a b, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 ∈ closedBall c ρ_b)
    (hy₂_mem : ∀ t ∈ Ioo a b, Φ ⟨x, t⟩ ∈ closedBall c ρ_b) :
    ∀ t ∈ Ioo a b, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 = Φ ⟨x, t⟩ := by
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set y₁ : ℝ → E := fun s => (aΦ ⟨p, s⟩).1 with hy₁_def
  set y₂ : ℝ → E := fun s => Φ ⟨x, s⟩ with hy₂_def
  have hy₁_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t := by
    intro t ht
    have h_orbit := haΦ.hasDerivWithinAt p hxp t (ha_sub' ht)
    set fstCLM : (E × (E →L[ℝ] E)) →L[ℝ] E := ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)
    have h_fd := h_orbit.hasFDerivWithinAt
    have h_fst_at := (fstCLM.hasFDerivAt).comp_hasFDerivWithinAt t h_fd
    have heq : fstCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (augmentedVectorField f t (aΦ ⟨p, t⟩)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augmentedVectorField f t (aΦ ⟨p, t⟩)).1) := by
      apply ContinuousLinearMap.ext
      intro s
      change fstCLM (s • augmentedVectorField f t (aΦ ⟨p, t⟩)) = s •
        (augmentedVectorField f t (aΦ ⟨p, t⟩)).1
      change (s • augmentedVectorField f t (aΦ ⟨p, t⟩)).1 = s •
        (augmentedVectorField f t (aΦ ⟨p, t⟩)).1
      rfl
    rw [heq] at h_fst_at
    have h_aug_fst : (augmentedVectorField f t (aΦ ⟨p, t⟩)).1 = f t (y₁ t) := rfl
    rw [h_aug_fst] at h_fst_at
    have h_within : HasDerivWithinAt y₁ (f t (y₁ t)) (Icc tmin' tmax') t := by
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      exact h_fst_at
    exact (h_within.mono ha_sub').hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hy₂_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t := by
    intro t ht
    have h_within := hΦ.hasDerivWithinAt x hx t (ha_sub ht)
    exact (h_within.mono ha_sub).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hinit : y₁ t₀ = y₂ t₀ := by
    have h1 : y₁ t₀ = x := by
      change (aΦ ⟨p, t₀⟩).1 = x
      rw [haΦ.apply_initial p hxp]
    have h2 : y₂ t₀ = x := by
      change Φ ⟨x, t₀⟩ = x
      exact hΦ.apply_initial x hx
    rw [h1, h2]
  exact orbit_unique_Ioo ht₀ hLip hy₁_deriv hy₂_deriv hy₁_mem hy₂_mem hinit

end OrbitUniqueness

section VariationalLinearMapCongr

variable {f : ℝ → E → E} {α₁ α₂ : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem IsVariationalSolutionOn.congr_central
    {T : ℝ} {δ : E} {y : ℝ → E}
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hy : IsVariationalSolutionOn f α₁ δ t₀ y (Icc (t₀ - T) (t₀ + T))) :
    IsVariationalSolutionOn f α₂ δ t₀ y (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨hy.1, ?_⟩
  intro t ht
  have hd := hy.2 t ht
  rwa [hαeq ht] at hd

theorem variationalLinearMapAt_congr_central
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hA_cont₁ : ContinuousOn (fun t => fderiv ℝ (f t) (α₁ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₁ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₁ t)‖ ≤ M)
    (hA_cont₂ : ContinuousOn (fun t => fderiv ℝ (f t) (α₂ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₂ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₂ t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA_cont₁ hA_bd₁ ht
      = variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA_cont₂ hA_bd₂ ht := by
  apply ContinuousLinearMap.ext
  intro δ
  have h₁ := variationalSolutionFun_isSolution hT hM hMT hA_cont₁ hA_bd₁ δ
  have h₂ := variationalSolutionFun_isSolution hT hM hMT hA_cont₂ hA_bd₂ δ
  have h₁' : IsVariationalSolutionOn f α₂ δ t₀
      (variationalSolutionFun hT hM hMT hA_cont₁ hA_bd₁ δ) (Icc (t₀ - T) (t₀ + T)) :=
    IsVariationalSolutionOn.congr_central hαeq h₁
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont₂ h₁' h₂
  rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
  exact h_eq ht

end VariationalLinearMapCongr

section SpatialPieceVariational

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem spatialPieceFn_eq_variationalLinearMapAt
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
    spatialPieceFn Φ (x, t)
      = variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀) hT hM hMT
          (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
              rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
            (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub)
          (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht) := by
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  have hfd_eq := hfd_at.fderiv
  rw [spatialPieceFn_apply, hfd_eq]
  exact ContinuousLinearMap.coprod_comp_inl _ _

end SpatialPieceVariational

section SpatialPieceAugmentedFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem spatialPieceFn_eq_fromAugmentedFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    (hy₁_mem : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hy₂_mem : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'), Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    spatialPieceFn Φ (x, t) = fromAugmentedFlow aΦ (x, t) := by
  have hx_le : dist x x₀ ≤ (ρ : ℝ) := by rw [mem_closedBall] at hx; exact hx
  have hx_r : x ∈ closedBall x₀ (r : ℝ) :=
    mem_closedBall.mpr (by linarith [r'.coe_nonneg])
  have hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall (x₀, ContinuousLinearMap.id ℝ E)
    (R : ℝ) := by
    rw [mem_closedBall, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist x x₀ ≤ (ρ : ℝ) := hx_le
      _ ≤ (R : ℝ) := hρR
  set α₁ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα₁_def
  set α₂ : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 with hα₂_def
  have ht₀_O : t₀ ∈ Ioo (t₀ - T') (t₀ + T') := ⟨by linarith, by linarith⟩
  have h_orbit_eq : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'), α₂ s = α₁ s :=
    augmentedFlow_fst_eq_flow hΦ haΦ ht₀_O hsubO hsubO' hLip hx_r hxp hy₁_mem hy₂_mem
  have hαeq : EqOn α₂ α₁ (Icc (t₀ - T) (t₀ + T)) := by
    intro s hs
    have hs_O : s ∈ Ioo (t₀ - T') (t₀ + T') :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact h_orbit_eq s hs_O
  have h_sp := spatialPieceFn_eq_variationalLinearMapAt hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  set hA_cont₁ : ContinuousOn (fun s => fderiv ℝ (f s) (α₁ s)) (Icc (t₀ - T) (t₀ + T)) :=
    (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
        rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub) with hA_cont₁_def
  set hA_bd₁ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₁ s)‖ ≤ M :=
    (fun τ hτ => hA_bd x hx τ hτ) with hA_bd₁_def
  have hA_cont₂ : ContinuousOn (fun s => fderiv ℝ (f s) (α₂ s)) (Icc (t₀ - T) (t₀ + T)) := by
    apply hA_cont₁.congr
    intro s hs
    change fderiv ℝ (f s) (α₂ s) = fderiv ℝ (f s) (α₁ s)
    rw [hαeq hs]
  have hA_bd₂ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₂ s)‖ ≤ M := by
    intro s hs
    rw [hαeq hs]
    exact hA_bd₁ s hs
  have h_aug := augmentedFlow_snd_eq_variationalLinearMapAt haΦ hT hM hMT hsub'
    hxp hA_cont₂ hA_bd₂ (Ioo_subset_Icc_self ht)
  have h_congr := variationalLinearMapAt_congr_central hT hM hMT hαeq
    hA_cont₂ hA_bd₂ hA_cont₁ hA_bd₁ (Ioo_subset_Icc_self ht)
  rw [fromAugmentedFlow_apply]
  rw [h_sp]
  rw [h_aug, h_congr]

end SpatialPieceAugmentedFlow

section VariationalLinearMapSmooth

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_variationalLinearMap
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ k (spatialPieceFn Φ) ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have h_fromAug_Ck : ContDiffOn ℝ k (fromAugmentedFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugmentedFlow haΦ_Ck hmap
  have h_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      spatialPieceFn Φ q = fromAugmentedFlow aΦ q := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    rw [mem_ball] at hq_x
    obtain ⟨x, t⟩ := q
    have hx_cb : x ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
    exact spatialPieceFn_eq_fromAugmentedFlow hΦ haΦ hf_C1 hT hM hMT hTT' hsub hsub' hsubO hsubO'
      hLip hr' hρρ' hρR hA_bd hx_cb (hcontain₁ x hx_cb) (hcontain₂ x hx_cb) hq_t
  exact h_fromAug_Ck.congr h_eq

theorem contDiffOn_flow_succ_of_augmented_flow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T T' M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1) (hT_lt' : T < T') (hTT'_out : T' ≤ T_out)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      exact_mod_cast this
    have h := hf_succ.of_le h_le
    simpa using h
  have hT_pos : 0 < T := hT
  have hsub_T : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_T_tmax : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax := hsub_T.trans hsub
  have hsubO_tmax : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax := by
    intro s hs
    exact hsub (Icc_subset_Icc (by linarith [hs.1]) (by linarith [hs.2]) (Ioo_subset_Icc_self hs))
  have hMT : M * T < 1 := lt_of_le_of_lt (by nlinarith [hM, le_of_lt hT_lt_mid]) hMT_mid
  have hA_bd_inner : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    refine hA_bd x ?_ τ (hsub_T hτ)
    exact closedBall_subset_closedBall
      (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hx
  have hρρ'_inner : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by
    have := hρ_lt_mid; linarith
  have hLsp_Ck : ContDiffOn ℝ k (spatialPieceFn Φ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_variationalLinearMap hΦ haΦ hf_C1 haΦ_Ck hT hM hMT hT_lt' hsub_T_tmax hsub'
      hsubO_tmax hsubO' hLip hr' hρρ'_inner hρR hmap hcontain₁ hcontain₂ hA_bd_inner
  have hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) :=
    fderiv_flow_eq_coprod_spatialPiece hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hA_bd
  exact contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hLsp_Ck hLsp_eq

end VariationalLinearMapSmooth

section C1

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_contDiffOn_flow_C1 [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ 1 Φ U := by
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ := exists_flow_nesting_parameters hΦ hf ht₀ hr_pos
  exact exists_contDiffOn_flow_of_contDiff hΦ (le_refl 1) hf hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end C1

section NeighbourhoodReconciliation

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem exists_ball_prod_Ioo_subset_of_mem_open {U : Set (E × ℝ)}
    (hU_open : IsOpen U) (hU_mem : (x₀, t₀) ∈ U) :
    ∃ ρ₁ > 0, ∃ T₁ > 0, ball x₀ ρ₁ ×ˢ Ioo (t₀ - T₁) (t₀ + T₁) ⊆ U := by
  have hU_nhds : U ∈ 𝓝 ((x₀, t₀) : E × ℝ) := hU_open.mem_nhds hU_mem
  rw [nhds_prod_eq] at hU_nhds
  obtain ⟨S, hS, V, hV, hSV⟩ := Filter.mem_prod_iff.mp hU_nhds
  obtain ⟨ρ₁, hρ₁_pos, hρ₁_sub⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨T₁, hT₁_pos, hT₁_sub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ₁, hρ₁_pos, T₁, hT₁_pos, ?_⟩
  intro p hp; apply hSV; rcases hp with ⟨hp1, hp2⟩
  refine ⟨hρ₁_sub hp1, hT₁_sub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩

omit [CompleteSpace E] in
theorem exists_ball_prod_Ioo_mapsTo_insert_id_of_mem_open
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} (hΩ_open : IsOpen Ω)
    (hΩ_mem : ((x₀, ContinuousLinearMap.id ℝ E), t₀) ∈ Ω) :
    ∃ ρ_a > 0, ∃ T_a > 0, ∀ (ρ T : ℝ), ρ ≤ ρ_a → T ≤ T_a →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        (ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω := by
  have hΩ_nhds : Ω ∈ 𝓝 (((x₀, ContinuousLinearMap.id ℝ E), t₀)) := hΩ_open.mem_nhds hΩ_mem
  rw [nhds_prod_eq] at hΩ_nhds
  obtain ⟨S, hS, V, hV, hSV⟩ := Filter.mem_prod_iff.mp hΩ_nhds
  obtain ⟨ρ_a, hρ_a_pos, hρ_a_sub⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨T_a, hT_a_pos, hT_a_sub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ_a, hρ_a_pos, T_a, hT_a_pos, ?_⟩
  intro ρ T hρ hT p hp; apply hSV; rcases hp with ⟨hp1, hp2⟩
  rw [Metric.mem_ball] at hp1
  refine ⟨hρ_a_sub ?_, hT_a_sub ?_⟩
  · rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist p.1 x₀ < ρ := hp1
      _ ≤ ρ_a := hρ
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hp2.1, hT], by linarith [hp2.2, hT]⟩

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem exists_capped_flow_nesting_parameters
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ))
    {ρcap Tcap : ℝ} (hρcap : 0 < ρcap) (hTcap : 0 < Tcap) :
    ∃ (T_out T_mid T M : ℝ) (ρ_out ρ_mid ρ r' : ℝ≥0),
      0 < T ∧ T < T_mid ∧ T_mid < T_out ∧ 0 ≤ M ∧ M * T_mid < 1 ∧ 0 < (r' : ℝ) ∧
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < (ρ_mid : ℝ) ∧ (ρ_mid : ℝ) < (ρ_out : ℝ) ∧
      (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) ∧ (ρ_out : ℝ) ≤ (r : ℝ) ∧
      (ρ_out : ℝ) ≤ ρcap ∧ T_out ≤ Tcap ∧
      Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax ∧
      (∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) := by
  set rb : ℝ := min (r : ℝ) ρcap with hrb_def
  have hrb_pos : 0 < rb := lt_min hr_pos hρcap
  have hrb_le_r : rb ≤ (r : ℝ) := min_le_left _ _
  have hrb_le_cap : rb ≤ ρcap := min_le_right _ _
  set ρ_out : ℝ≥0 := ⟨rb / 2, by positivity⟩ with hρout_def
  set ρ_mid : ℝ≥0 := ⟨rb / 4, by positivity⟩ with hρmid_def
  set ρ : ℝ≥0 := ⟨rb / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨rb / 2, by positivity⟩ with hr'_def
  have hρ_out_coe : (ρ_out : ℝ) = rb / 2 := rfl
  have hρ_mid_coe : (ρ_mid : ℝ) = rb / 4 := rfl
  have hρ_coe : (ρ : ℝ) = rb / 8 := rfl
  have hr'_coe : (r' : ℝ) = rb / 2 := rfl
  have hρ_pos : 0 < (ρ : ℝ) := by rw [hρ_coe]; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by rw [hρ_coe, hρ_mid_coe]; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by rw [hρ_mid_coe, hρ_out_coe]; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by
    rw [hρ_mid_coe, hr'_coe]; nlinarith [hrb_le_r, hrb_pos]
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ) := by rw [hρ_out_coe]; nlinarith [hrb_le_r, hrb_pos]
  have hρ_out_le_cap : (ρ_out : ℝ) ≤ ρcap := by rw [hρ_out_coe]; nlinarith [hrb_le_cap, hrb_pos]
  have hr'_pos : 0 < (r' : ℝ) := by rw [hr'_coe]; linarith
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_out : ℝ := min (d / 2) (Tcap / 2) with hT_out_def
  have hT_out_pos : 0 < T_out := lt_min (by linarith) (by linarith)
  have hT_out_le_cap : T_out ≤ Tcap := by
    calc T_out ≤ Tcap / 2 := min_le_right _ _
      _ ≤ Tcap := by linarith
  have hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have hh : d ≤ t₀ - tmin := min_le_left _ _
      have ht : T_out ≤ d / 2 := min_le_left _ _
      linarith
    · have hh : d ≤ tmax - t₀ := min_le_right _ _
      have ht : T_out ≤ d / 2 := min_le_left _ _
      linarith
  obtain ⟨M, hM_nonneg, hM_bd⟩ :=
    exists_norm_fderiv_le_along_flow_joint hΦ hf (ρ := (ρ_out : ℝ))
      (NNReal.coe_nonneg ρ_out) hρ_out_le_r
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ => hM_bd x hx τ (hsub hτ)
  set T_mid : ℝ := min (T_out / 2) (1 / (2 * (M + 1))) with hT_mid_def
  have hM1_pos : 0 < 2 * (M + 1) := by linarith
  have hT_mid_pos : 0 < T_mid := lt_min (by linarith) (by positivity)
  have hT_mid_lt_out : T_mid < T_out := by
    calc T_mid ≤ T_out / 2 := min_le_left _ _
      _ < T_out := by linarith
  set T : ℝ := T_mid / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_lt_mid : T < T_mid := by rw [hT_def]; linarith
  have hMT_mid : M * T_mid < 1 := by
    have hle : T_mid ≤ 1 / (2 * (M + 1)) := min_le_right _ _
    calc M * T_mid ≤ M * (1 / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hle hM_nonneg
      _ = M / (2 * (M + 1)) := by ring
      _ < 1 := by rw [div_lt_one hM1_pos]; linarith
  exact ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT_pos, hT_lt_mid, hT_mid_lt_out,
    hM_nonneg, hMT_mid, hr'_pos, hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r,
    hρ_out_le_cap, hT_out_le_cap, hsub, hA_bd⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem continuousOn_augmentedFlow_fst
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    {ρ₀ : ℝ} (hρ₀_le : ρ₀ ≤ (R : ℝ)) :
    ContinuousOn (fun q : E × ℝ => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).1)
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax') := by
  have hembed : ContinuousOn (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax') :=
    ((continuousOn_fst).prodMk continuousOn_const).prodMk continuousOn_snd
  have hmaps : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax')
      (closedBall (x₀, ContinuousLinearMap.id ℝ E) (R : ℝ) ×ˢ Icc tmin' tmax') := by
    intro p hp; rcases hp with ⟨hp1, hp2⟩
    refine ⟨?_, hp2⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist p.1 x₀ ≤ ρ₀ := mem_closedBall.mp hp1
      _ ≤ (R : ℝ) := hρ₀_le
  exact continuous_fst.comp_continuousOn (haΦ.continuousOn.comp hembed hmaps)

end NeighbourhoodReconciliation

section CkDriver

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
variable [FiniteDimensional ℝ E]

theorem portPrivate_ff5d016f_exists_contDiffOn_flow_succ_driver
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (ht₀' : t₀ ∈ Ioo tmin' tmax') (hR_pos : 0 < (R : ℝ))
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hΩ_open : IsOpen Ω) (hΩ_mem : ((x₀, ContinuousLinearMap.id ℝ E), t₀) ∈ Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ))
    (hΦ_prev : ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ k Φ U) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (k + 1) Φ U := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      exact_mod_cast this
    simpa using hf_succ.of_le h_le
  obtain ⟨U, hU_open, hU_mem, hU_Ck⟩ := hΦ_prev
  obtain ⟨ρ_p, hρ_p_pos, T_p, hT_p_pos, hbox_p⟩ :=
    exists_ball_prod_Ioo_subset_of_mem_open hU_open hU_mem
  obtain ⟨ρ_a, hρ_a_pos, T_a, hT_a_pos, hembed⟩ :=
    exists_ball_prod_Ioo_mapsTo_insert_id_of_mem_open hΩ_open hΩ_mem
  have hΦ_cont_box : ContinuousOn Φ (closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) := hΦ.continuousOn
  have hΦ_initial : ∀ x ∈ closedBall x₀ (r : ℝ), Φ (x, t₀) = x := hΦ.apply_initial
  obtain ⟨ρ_c2, hρ_c2_pos, T_c2, hT_c2_pos, hρ_c2_le, hsub_c2, hcontain_Φ⟩ :=
    exists_uniform_time_containment (x₀ := x₀) (ρ₀ := (r : ℝ)) (ρ_b := (r : ℝ)) Φ
      hΦ_cont_box hΦ_initial ht₀ hr_pos hr_pos
  set Ψaug : E × ℝ → E := fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).1 with hΨaug_def
  have hΨaug_cont : ContinuousOn Ψaug (closedBall x₀ (R : ℝ) ×ˢ Icc tmin' tmax') :=
    continuousOn_augmentedFlow_fst haΦ (le_refl _)
  have hΨaug_initial : ∀ x ∈ closedBall x₀ (R : ℝ), Ψaug (x, t₀) = x := by
    intro x hx
    have hxp : (x, ContinuousLinearMap.id ℝ E) ∈
        closedBall (x₀, ContinuousLinearMap.id ℝ E) (R : ℝ) := by
      rw [mem_closedBall, Prod.dist_eq]
      simp only [dist_self, max_eq_left (dist_nonneg)]
      exact mem_closedBall.mp hx
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hxp]
  obtain ⟨ρ_c1, hρ_c1_pos, T_c1, hT_c1_pos, hρ_c1_le, hsub_c1, hcontain_aug⟩ :=
    exists_uniform_time_containment (x₀ := x₀) (ρ₀ := (R : ℝ)) (ρ_b := (r : ℝ)) Ψaug
      hΨaug_cont hΨaug_initial ht₀' hR_pos hr_pos
  set ρcap : ℝ := min (min ρ_a ρ_p) (min ρ_c1 ρ_c2) with hρcap_def
  have hρcap_pos : 0 < ρcap := lt_min (lt_min hρ_a_pos hρ_p_pos) (lt_min hρ_c1_pos hρ_c2_pos)
  set Tcap : ℝ := min (min T_a T_p) (min T_c1 T_c2) with hTcap_def
  have hTcap_pos : 0 < Tcap := lt_min (lt_min hT_a_pos hT_p_pos) (lt_min hT_c1_pos hT_c2_pos)
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid,
    hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r, hρ_out_le_cap, hT_out_le_cap,
    hsub_out, hA_bd⟩ := exists_capped_flow_nesting_parameters hΦ hf_C1 ht₀ hr_pos hρcap_pos hTcap_pos
  have hρcap_le_ρa : ρcap ≤ ρ_a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρcap_le_ρp : ρcap ≤ ρ_p := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρcap_le_ρc1 : ρcap ≤ ρ_c1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρcap_le_ρc2 : ρcap ≤ ρ_c2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hTcap_le_Ta : Tcap ≤ T_a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hTcap_le_Tp : Tcap ≤ T_p := le_trans (min_le_left _ _) (min_le_right _ _)
  have hTcap_le_Tc1 : Tcap ≤ T_c1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hTcap_le_Tc2 : Tcap ≤ T_c2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρ_lt_out : (ρ : ℝ) < (ρ_out : ℝ) := lt_trans hρ_lt_mid hρ_mid_lt_out
  have hρ_le_cap : (ρ : ℝ) ≤ ρcap := le_trans (le_of_lt hρ_lt_out) hρ_out_le_cap
  have hT_lt_out : T < T_out := lt_trans hT_lt_mid hT_mid_lt_out
  have hT_le_cap : T ≤ Tcap := le_trans (le_of_lt hT_lt_out) hT_out_le_cap
  have hTmid_le_cap : T_mid ≤ Tcap := le_trans (le_of_lt hT_mid_lt_out) hT_out_le_cap
  have hρR : (ρ : ℝ) ≤ (R : ℝ) := le_trans (le_trans hρ_le_cap hρcap_le_ρc1) hρ_c1_le
  have hT_le_Tc1 : T ≤ T_c1 := le_trans hT_le_cap hTcap_le_Tc1
  have hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax' :=
    (Icc_subset_Icc (by linarith) (by linarith)).trans hsub_c1
  have hTmid_le_Tc1 : T_mid ≤ T_c1 := le_trans hTmid_le_cap hTcap_le_Tc1
  have hsubO' : Ioo (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin' tmax' := by
    intro s hs
    exact hsub_c1 (Icc_subset_Icc (by linarith) (by linarith) (Ioo_subset_Icc_self hs))
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closedBall_of_C1 hf_C1 x₀ (r : ℝ)
    (t₀ - T_out) (t₀ + T_out) (by linarith)
  have hLip : ∀ t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      LipschitzOnWith K (f t) (closedBall x₀ (r : ℝ)) := by
    intro t ht
    exact hK t ⟨by linarith [ht.1, hT_mid_lt_out], by linarith [ht.2, hT_mid_lt_out]⟩
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω := by
    apply hembed (ρ : ℝ) T
    · exact le_trans hρ_le_cap hρcap_le_ρa
    · exact le_trans hT_le_cap hTcap_le_Ta
  have hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ (r : ℝ) := by
    intro x hx s hs
    have hx' : x ∈ closedBall x₀ ρ_c1 :=
      closedBall_subset_closedBall (le_trans hρ_le_cap hρcap_le_ρc1) hx
    have hs' : s ∈ Ioo (t₀ - T_c1) (t₀ + T_c1) :=
      ⟨by linarith [hs.1, hTmid_le_Tc1], by linarith [hs.2, hTmid_le_Tc1]⟩
    exact hcontain_aug x hx' s hs'
  have hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      Φ ⟨x, s⟩ ∈ closedBall x₀ (r : ℝ) := by
    intro x hx s hs
    have hx' : x ∈ closedBall x₀ ρ_c2 :=
      closedBall_subset_closedBall (le_trans hρ_le_cap hρcap_le_ρc2) hx
    have hTmid_le_Tc2 : T_mid ≤ T_c2 := le_trans hTmid_le_cap hTcap_le_Tc2
    have hs' : s ∈ Ioo (t₀ - T_c2) (t₀ + T_c2) :=
      ⟨by linarith [hs.1, hTmid_le_Tc2], by linarith [hs.2, hTmid_le_Tc2]⟩
    exact hcontain_Φ x hx' s hs'
  have hbox_sub : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T) ⊆ U := by
    refine subset_trans ?_ hbox_p
    apply Set.prod_mono
    · exact ball_subset_ball (le_trans hρ_le_cap hρcap_le_ρp)
    · exact Ioo_subset_Ioo (by linarith [hT_le_cap, hTcap_le_Tp])
        (by linarith [hT_le_cap, hTcap_le_Tp])
  have hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    hU_Ck.mono hbox_sub
  have hfinal : ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_succ_of_augmented_flow hΦ haΦ haΦ_Ck hf_succ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
      hT_lt_mid (le_of_lt hT_mid_lt_out) hsub_out hsub' hsubO' hLip hr' hρ_lt_mid hρ_mid_lt_out
      hρρ' hρ_out_le_r hρR hmap hcontain₁ hcontain₂ hA_bd hΦ_Ck
  refine ⟨(ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T), isOpen_ball.prod isOpen_Ioo, ?_, hfinal⟩
  exact ⟨mem_ball_self hρ_pos, by constructor <;> linarith⟩

end CkDriver

section CkInduction

universe u

def portPrivate_ff5d016f_flowCkPred (n : ℕ) : Prop :=
  ∀ {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [FiniteDimensional ℝ E'] {g : ℝ → E' → E'} {t₀ : ℝ} {x₀ : E'} {r : ℝ≥0}
    {tmin tmax : ℝ} {Ψ : E' × ℝ → E'},
    IsLocalFlow g t₀ x₀ r tmin tmax Ψ →
    ContDiffOn ℝ (n : ℕ∞) (uncurry g) (Set.univ : Set (ℝ × E')) →
    t₀ ∈ Ioo tmin tmax → 0 < (r : ℝ) →
    ∃ U : Set (E' × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (n : ℕ∞) Ψ U

theorem portPrivate_ff5d016f_flowCkPred_base : portPrivate_ff5d016f_flowCkPred.{u} 1 := by
  intro E' _ _ _ _ g t₀ x₀ r tmin tmax Ψ hΨ hg ht₀ hr
  have hg1 : ContDiffOn ℝ 1 (uncurry g) (Set.univ : Set (ℝ × E')) := by simpa using hg
  exact exists_contDiffOn_flow_C1 hΨ hg1 ht₀ hr

theorem portPrivate_ff5d016f_flowCkPred_step {n : ℕ} (hn : 1 ≤ n) (IH : portPrivate_ff5d016f_flowCkPred.{u} n) :
    portPrivate_ff5d016f_flowCkPred.{u} (n + 1) := by
  intro E' _ _ _ _ g t₀ x₀ r tmin tmax Ψ hΨ hg ht₀ hr
  have horder : ((((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞)) =
      (((n : ℕ∞) : WithTop ℕ∞) + 1) := by norm_num
  have hg_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry g) (Set.univ : Set (ℝ × E')) := by
    rw [← horder]
    exact hg
  have h_augmentedVectorField_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry (augmentedVectorField g))
      (Set.univ : Set (ℝ × (E' × (E' →L[ℝ] E')))) :=
    augmentedVectorField_uncurry_contDiff (k := (n : ℕ∞)) hg_succ
  have h_augmentedVectorField_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField g))
      (Set.univ : Set (ℝ × (E' × (E' →L[ℝ] E')))) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hn
      exact_mod_cast this
    simpa using h_augmentedVectorField_Cn.of_le h_le
  obtain ⟨R, ε, hR_pos, hε_pos, aΨ, haΨ⟩ :=
    exists_isLocalFlow_of_contDiffOn_univ (augmentedVectorField g) h_augmentedVectorField_C1 t₀
      (x₀, ContinuousLinearMap.id ℝ E')
  have ht₀_aug : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨Ω, hΩ_open, hΩ_mem, haΨ_Cn⟩ := IH haΨ h_augmentedVectorField_Cn ht₀_aug hR_pos
  have hg_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry g) (Set.univ : Set (ℝ × E')) := by
    have h_le : ((n : ℕ∞) : WithTop ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ n
      exact_mod_cast this
    exact hg.of_le h_le
  have hΨ_prev := IH hΨ hg_Cn ht₀ hr
  obtain ⟨U, hU_open, hU_mem, hU_C⟩ := portPrivate_ff5d016f_exists_contDiffOn_flow_succ_driver hΨ haΨ ht₀_aug hR_pos
    haΨ_Cn hΩ_open hΩ_mem hg_succ ht₀ hr hΨ_prev
  refine ⟨U, hU_open, hU_mem, ?_⟩
  rw [horder]
  exact hU_C

theorem portPrivate_ff5d016f_flowCkPred_all (n : ℕ) (hn : 1 ≤ n) : portPrivate_ff5d016f_flowCkPred.{u} n := by
  induction n, hn using Nat.le_induction with
  | base => exact portPrivate_ff5d016f_flowCkPred_base
  | succ m hm IH => exact portPrivate_ff5d016f_flowCkPred_step hm IH

section Headline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_contDiffOn_flow_Cnat
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ (n : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (n : ℕ∞) Φ U :=
  portPrivate_ff5d016f_flowCkPred_all n hn hΦ hf ht₀ hr

theorem exists_contDiffOn_flow_C2
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ 2 Φ U := by
  obtain ⟨U, hU1, hU2, hU3⟩ :=
    exists_contDiffOn_flow_Cnat hΦ (n := 2) (by norm_num) (by exact_mod_cast hf) ht₀ hr
  exact ⟨U, hU1, hU2, by exact_mod_cast hU3⟩

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_flow_infty_of_spatial_smooth_all
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
    (hf_Cinfty : ContDiffOn ℝ ∞ (uncurry f) (Set.univ : Set (ℝ × E)))
    (hLsp_smooth : ∀ j : ℕ,
      ContDiffOn ℝ (j : ℕ∞) (spatialPieceFn Φ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ ∞ Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))
    simpa using hf_Cinfty.of_le h_le
  have hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) :=
    fderiv_flow_eq_coprod_spatialPiece hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hA_bd
  rw [contDiffOn_infty]
  intro k
  have hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hf_Cinfty.of_le h_le
  exact contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck (fun _ => spatialPieceFn Φ)
    (fun j _ => hLsp_smooth j) (fun _ _ => hLsp_eq)

theorem exists_contDiffOn_flow_smooth
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ ∞ (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ))
    (hLsp : ∀ ⦃ρ : ℝ≥0⦄ ⦃T : ℝ⦄, 0 < T →
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T) ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) →
      ∀ j : ℕ, ContDiffOn ℝ (j : ℕ∞) (spatialPieceFn Φ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))
    simpa using hf.of_le h_le
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ := exists_flow_nesting_parameters hΦ hf_C1 ht₀ hr
  have h_ρ_r : (ρ : ℝ) ≤ (r : ℝ) :=
    le_trans (le_of_lt hρ_lt_mid) (le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r)
  have h_T_out : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hbox_sub : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
      ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    refine ⟨?_, ?_⟩
    · exact closedBall_subset_closedBall h_ρ_r
        (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
    · exact hsub (h_T_out (Ioo_subset_Icc_self hq.2))
  refine ⟨(ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T), isOpen_ball.prod isOpen_Ioo,
    ⟨mem_ball_self hρ_pos, ⟨by linarith, by linarith⟩⟩, ?_⟩
  exact contDiffOn_flow_infty_of_spatial_smooth_all hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub
    hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf (hLsp hT hbox_sub)

end Headline

end CkInduction

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
