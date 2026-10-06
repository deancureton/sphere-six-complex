module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}

theorem hasDerivAt_df_comp_integralCurve
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (v (γ t))) t := by
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) :=
    (hf (γ t)).mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hf' : HasMFDerivAt I 𝓘(ℝ, ℝ) f (γ t) (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) :=
    MDifferentiableAt.hasMFDerivAt hfmd
  have hfd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t
      ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) :=
    HasMFDerivAt.comp t (g := f) (f := γ) (hg := hf') (hf := hγ t)
  have hfd'' : HasFDerivAt (f ∘ γ)
      ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp hfd')
  let a : ℝ := NormedSpace.fromTangentSpace (f (γ t))
    ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (v (γ t)))
  have hDlsmul :
      (mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) =
      (ContinuousLinearMap.toSpanSingleton ℝ a : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self,
      ]
    change NormedSpace.fromTangentSpace (f (γ t))
      ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (r • v (γ t))) = r • a
    rw [map_smul]
    rfl
  change HasDerivAt (f ∘ γ) a t
  exact hasDerivAt_iff_hasFDerivAt.mpr (hfd''.congr_fderiv hDlsmul)

theorem hasDerivAt_f_comp_integralCurve (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (-1) t := by
  have h := hasDerivAt_df_comp_integralCurve f hf v hγ t
  have hval : (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (v (γ t)) = (-1 : ℝ) := by
    simpa using! hdf (γ t)
  simpa [hval] using h

theorem f_rate_bounds_of_integralCurve_on_set (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (v : (x : M) → TangentSpace I x)
    (D : Set M)
    (hrate : ∀ x ∈ D, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, γ s ∈ D) :
    f (γ 0) - t ≤ f (γ t) ∧ f (γ t) ≤ f (γ 0) := by
  let g : ℝ → ℝ := f ∘ γ
  have hderiv : ∀ s : ℝ, HasDerivAt g ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) s := by
    intro s
    have hfd : HasFDerivAt g
        ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s)))) s :=
      hasMFDerivAt_iff_hasFDerivAt.mp ((hf (γ s)).hasMFDerivAt.comp s (hγ s))
    apply hasDerivAt_iff_hasFDerivAt.mpr
    apply hfd.congr_fderiv
    apply ContinuousLinearMap.ext
    intro r
    change (mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (r • v (γ s)) =
      r • (mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))
    exact map_smul _ _ _
  have hgdiff : DifferentiableOn ℝ g (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hderiv x).differentiableAt.differentiableWithinAt
  have hderivNonpos : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), deriv g x ≤ 0 := by
    intro x hx
    rw [(hderiv x).deriv]
    have hv : (NormedSpace.fromTangentSpace (f (γ x))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ x)) (v (γ x))) ≤ 0 :=
      (hrate (γ x) (hstay x (interior_subset hx))).2
    simpa using! hv
  have hganti : AntitoneOn g (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hgdiff.continuousOn
      (hgdiff.mono interior_subset) hderivNonpos
  have hle : f (γ t) ≤ f (γ 0) := by
    have hm := hganti (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht
    simpa [g] using hm
  let h : ℝ → ℝ := fun s => g s + s
  have hhderiv : ∀ s : ℝ, HasDerivAt h
      ((NormedSpace.fromTangentSpace (f (γ s))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) + 1) s :=
    fun s => (hderiv s).add (hasDerivAt_id s)
  have hhdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hhderiv x).differentiableAt.differentiableWithinAt
  have hderivNonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), 0 ≤ deriv h x := by
    intro x hx
    rw [(hhderiv x).deriv]
    have hv : -1 ≤ (NormedSpace.fromTangentSpace (f (γ x))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ x)) (v (γ x))) :=
      (hrate (γ x) (hstay x (interior_subset hx))).1
    linarith
  have hhmono : MonotoneOn h (Set.Icc (0 : ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) hderivNonneg
  have hle' : f (γ 0) - t ≤ f (γ t) := by
    have hm : h 0 ≤ h t := hhmono (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht
    dsimp [h, g] at hm
    linarith
  exact ⟨hle', hle⟩

theorem f_rate_bounds_of_integralCurve (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t) :
    f (γ 0) - t ≤ f (γ t) ∧ f (γ t) ≤ f (γ 0) := by
  exact f_rate_bounds_of_integralCurve_on_set f (hf.mdifferentiable (by simp)) v Set.univ
    (fun x _ => hrate x) hγ ht (fun _ _ => Set.mem_univ _)

theorem f_rate_bounds_of_integralCurve_back (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t) :
    f (γ 0) ≤ f (γ (-t)) ∧ f (γ (-t)) ≤ f (γ 0) + t := by
  let g : ℝ → ℝ := fun s => f (γ (-s))
  have hderiv : ∀ s : ℝ, HasDerivAt g
      (-((NormedSpace.fromTangentSpace (f (γ (-s)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-s))) (v (γ (-s)))))) s := by
    intro s
    have hd : HasDerivAt (fun z : ℝ => f (γ z))
        ((NormedSpace.fromTangentSpace (f (γ (-s)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-s))) (v (γ (-s))))) (-s) :=
      hasDerivAt_df_comp_integralCurve f hf v hγ (-s)
    have hneg : HasDerivAt (fun z : ℝ => -z) (-1) s := hasDerivAt_neg s
    simpa [g] using! (hd.comp s hneg)
  have hgdiff : DifferentiableOn ℝ g (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hderiv x).differentiableAt.differentiableWithinAt
  have hderivNonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), 0 ≤ deriv g x := by
    intro x hx
    rw [(hderiv x).deriv]
    have hv : (NormedSpace.fromTangentSpace (f (γ (-x)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-x))) (v (γ (-x)))) ≤ 0 :=
      (hrate (γ (-x))).2
    linarith
  have hgmono : MonotoneOn g (Set.Icc (0 : ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hgdiff.continuousOn
      (hgdiff.mono interior_subset) hderivNonneg
  have hle : f (γ 0) ≤ f (γ (-t)) := by
    have hm := hgmono (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht
    simpa [g] using hm
  let h : ℝ → ℝ := fun s => g s - s
  have hhderiv : ∀ s : ℝ, HasDerivAt h
      (-((NormedSpace.fromTangentSpace (f (γ (-s)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-s))) (v (γ (-s))))) - 1) s := by
    intro s
    exact (hderiv s).sub (hasDerivAt_id s)
  have hhdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hhderiv x).differentiableAt.differentiableWithinAt
  have hderivNonpos : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), deriv h x ≤ 0 := by
    intro x hx
    rw [(hhderiv x).deriv]
    have hv : -1 ≤ (NormedSpace.fromTangentSpace (f (γ (-x)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-x))) (v (γ (-x)))) :=
      (hrate (γ (-x))).1
    linarith
  have hhanti : AntitoneOn h (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) hderivNonpos
  have hle' : f (γ (-t)) ≤ f (γ 0) + t := by
    have hm : h t ≤ h 0 := hhanti (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht
    dsimp [h, g] at hm
    have h0 : γ (-0) = γ 0 := by simp
    have hm' : f (γ (-t)) - t ≤ f (γ 0) := by
      simpa [h0, sub_zero] using hm
    linarith
  exact ⟨hle, hle'⟩

theorem f_eq_sub_of_integralCurve_on_strip (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    {a b : ℝ}
    (hdf : ∀ x ∈ f ⁻¹' Set.Icc a b, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, γ s ∈ f ⁻¹' Set.Icc a b) :
    f (γ t) = f (γ 0) - t := by
  let g : ℝ → ℝ := f ∘ γ
  let h : ℝ → ℝ := fun s => g s + s
  have hderiv : ∀ s : ℝ, HasDerivAt g ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) s :=
    fun s => hasDerivAt_df_comp_integralCurve f hf v hγ s
  have hhderiv : ∀ s : ℝ, HasDerivAt h
      ((NormedSpace.fromTangentSpace (f (γ s))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) + 1) s :=
    fun s => (hderiv s).add (hasDerivAt_id s)
  have hhdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hhderiv x).differentiableAt.differentiableWithinAt
  have hzeroderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), deriv h x = 0 := by
    intro x hx
    have hxcc : x ∈ Set.Icc (0 : ℝ) t := interior_subset hx
    rw [(hhderiv x).deriv]
    have hval : (NormedSpace.fromTangentSpace (f (γ x))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ x)) (v (γ x))) = -1 :=
      hdf (γ x) (hstay x hxcc)
    linarith
  have hmono : MonotoneOn h (Set.Icc (0 : ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact ge_of_eq (hzeroderiv x hx))
  have hanti : AntitoneOn h (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact le_of_eq (hzeroderiv x hx))
  have hc : h 0 = h t := by
    exact le_antisymm
      (hmono (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
      (hanti (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
  dsimp [h, g] at hc
  linarith

theorem f_eq_sub_of_integralCurve_on_set (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (s : Set M)
    (hdf : ∀ x ∈ s, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ u ∈ Set.Icc (0 : ℝ) t, γ u ∈ s) :
    f (γ t) = f (γ 0) - t := by
  let g : ℝ → ℝ := f ∘ γ
  let h : ℝ → ℝ := fun s => g s + s
  have hderiv : ∀ s : ℝ, HasDerivAt g ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) s :=
    fun s => hasDerivAt_df_comp_integralCurve f hf v hγ s
  have hhderiv : ∀ s : ℝ, HasDerivAt h
      ((NormedSpace.fromTangentSpace (f (γ s))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) + 1) s :=
    fun s => (hderiv s).add (hasDerivAt_id s)
  have hhdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hhderiv x).differentiableAt.differentiableWithinAt
  have hzeroderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), deriv h x = 0 := by
    intro x hx
    have hxcc : x ∈ Set.Icc (0 : ℝ) t := interior_subset hx
    rw [(hhderiv x).deriv]
    have hval : (NormedSpace.fromTangentSpace (f (γ x))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ x)) (v (γ x))) = -1 :=
      hdf (γ x) (hstay x hxcc)
    linarith
  have hmono : MonotoneOn h (Set.Icc (0 : ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact ge_of_eq (hzeroderiv x hx))
  have hanti : AntitoneOn h (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact le_of_eq (hzeroderiv x hx))
  have hc : h 0 = h t := by
    exact le_antisymm
      (hmono (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
      (hanti (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
  dsimp [h, g] at hc
  linarith

noncomputable def curveAt (v : (x : M) → TangentSpace I x)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) (x : M) : ℝ → M :=
  Classical.choose (hcomplete x)

theorem curveAt_zero (v : (x : M) → TangentSpace I x)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) (x : M) :
    curveAt v hcomplete x 0 = x :=
  (Classical.choose_spec (hcomplete x)).1

theorem curveAt_integralCurve (v : (x : M) → TangentSpace I x)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) (x : M) :
    IsMIntegralCurve (curveAt v hcomplete x) v :=
  (Classical.choose_spec (hcomplete x)).2

theorem f_eq_sub_of_integralCurve (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    f (γ t) = f (γ 0) - t := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (f ∘ γ) (-1) x := fun x hx =>
    hasDerivAt_f_comp_integralCurve f hf v hdf hγ x
  have hint : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume (0 : ℝ) t :=
    intervalIntegrable_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f ∘ γ)
    (f' := fun _ : ℝ => (-1 : ℝ)) hderiv hint
  have hconst : (∫ x in (0 : ℝ)..t, (-1 : ℝ)) = (0 : ℝ) - t := by
    simp
  rw [hconst] at hftc
  calc
    f (γ t) = f (γ 0) + (f (γ t) - f (γ 0)) := by ring
    _ = f (γ 0) - t := by
      have h2 : f (γ t) - f (γ 0) = (0 : ℝ) - t := hftc.symm
      rw [h2]
      ring

theorem f_add_of_integralCurve_back (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    {a b : ℝ}
    (hdf : ∀ x ∈ f ⁻¹' Set.Icc a b, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, γ (-s) ∈ f ⁻¹' Set.Icc a b) :
    f (γ (-t)) = f (γ 0) + t := by
  let g : ℝ → ℝ := f ∘ γ
  let h : ℝ → ℝ := fun s => g (-s) - s
  have hderiv : ∀ s : ℝ, HasDerivAt g ((mfderiv I 𝓘(ℝ, ℝ) f (γ s)) (v (γ s))) s :=
    fun s => hasDerivAt_df_comp_integralCurve f hf v hγ s
  have hhderiv : ∀ s : ℝ, HasDerivAt h
      (((NormedSpace.fromTangentSpace (f (γ (-s)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-s))) (v (γ (-s))))) * -1 - 1) s := by
    intro s
    have hcomp : HasDerivAt (fun z : ℝ => g (-z))
        (((NormedSpace.fromTangentSpace (f (γ (-s)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-s))) (v (γ (-s))))) * -1) s := by
      have hneg : HasDerivAt (fun z : ℝ => -z) (-1) s := hasDerivAt_neg s
      exact (hderiv (-s)).comp s hneg
    exact hcomp.sub (hasDerivAt_id s)
  have hhdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) t) := by
    intro x hx
    exact (hhderiv x).differentiableAt.differentiableWithinAt
  have hzeroderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) t), deriv h x = 0 := by
    intro x hx
    have hxcc : x ∈ Set.Icc (0 : ℝ) t := interior_subset hx
    rw [(hhderiv x).deriv]
    have hval : (NormedSpace.fromTangentSpace (f (γ (-x)))) ((mfderiv I 𝓘(ℝ, ℝ) f (γ (-x))) (v (γ (-x)))) = -1 :=
      hdf (γ (-x)) (hstay x hxcc)
    linarith
  have hmono : MonotoneOn h (Set.Icc (0 : ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact ge_of_eq (hzeroderiv x hx))
  have hanti : AntitoneOn h (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hhdiff.continuousOn
      (hhdiff.mono interior_subset) (by
      intro x hx
      exact le_of_eq (hzeroderiv x hx))
  have hc : h 0 = h t := by
    exact le_antisymm
      (hmono (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
      (hanti (a := 0) (b := t) (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht)
  dsimp [h, g] at hc
  have hc' : f (γ 0) = f (γ (-t)) - t := by
    have h0 : γ (-0) = γ 0 := by simp
    rw [h0, sub_zero] at hc
    exact hc
  linarith

theorem integralCurve_eq_of_agree [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {γ γ' : ℝ → M} (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v)
    {t₀ : ℝ} (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ hγ' h

theorem integralCurve_eq_of_agree_zero [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {γ γ' : ℝ → M} (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v)
    (h : γ 0 = γ' 0) : γ = γ' :=
  integralCurve_eq_of_agree v hv hγ hγ' h

theorem curveAt_hcomplete_irrel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (h₁ h₂ : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (x : M) (t : ℝ) :
    curveAt v h₁ x t = curveAt v h₂ x t := by
  have hEq := integralCurve_eq_of_agree_zero v hv
    (curveAt_integralCurve v h₁ x) (curveAt_integralCurve v h₂ x) (by
      simp [curveAt_zero v h₁ x])
  exact congrFun hEq t

end DifferentialGeometry.Analysis.ODE
