module

public import DifferentialGeometry.Analysis.Calculus.Derivative.AlmostEverywhereLipschitz
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral

@[expose] public section

namespace DifferentialGeometry
namespace Analysis

open Filter Function MeasureTheory Set
open scoped Interval Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem portPrivate_5734ce2d_hasDerivAt_second (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (fderiv ℝ g (t • x)) x)
      (((fderiv ℝ (fderiv ℝ g) (t • x)) x) x) t := by
  have hsmul : HasFDerivAt (fun t : ℝ => t • x) ((1 : ℝ →L[ℝ] ℝ).smulRight x) t := by
    exact (hasStrictFDerivAt_id (x := t)).hasFDerivAt.smul_const x
  have hfd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (t • x)) (t • x) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hd : DifferentiableAt ℝ (fderiv ℝ g) (t • x) :=
      ((h1 _ (Set.mem_univ _)).differentiableWithinAt
        (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
    exact hd.hasFDerivAt
  have hc : HasFDerivAt (fun t : ℝ => fderiv ℝ g (t • x))
      ((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) t :=
    HasFDerivAt.comp (hg := hfd) (hf := hsmul)
  have hu : HasFDerivAt (fun t : ℝ => x) 0 t :=
    hasFDerivAt_const (𝕜 := ℝ) (c := x) (x := t)
  have hcapp : HasFDerivAt (fun t : ℝ => (fderiv ℝ g (t • x)) x)
      (((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)).flip x) t := by
    simpa using hc.clm_apply hu
  have hdeq : (((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)).flip x) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (((fderiv ℝ (fderiv ℝ g) (t • x)) x) x) := by
    apply ContinuousLinearMap.ext
    intro s
    rw [ContinuousLinearMap.flip_apply]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [map_smul]
    simp
  simpa only [hdeq, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using
    hcapp.hasDerivAt

theorem portPrivate_5734ce2d_hasDerivAt_first (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => g (t • x)) ((fderiv ℝ g (t • x)) x) t := by
  have hsmul : HasFDerivAt (fun t : ℝ => t • x) ((1 : ℝ →L[ℝ] ℝ).smulRight x) t := by
    exact (hasStrictFDerivAt_id (x := t)).hasFDerivAt.smul_const x
  have hg' : HasFDerivAt g (fderiv ℝ g (t • x)) (t • x) := by
    have hda : DifferentiableAt ℝ g (t • x) :=
      (hg.contDiffAt (x := t • x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    exact hda.hasFDerivAt
  have hcomp : HasFDerivAt (fun t : ℝ => g (t • x))
      ((fderiv ℝ g (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) t :=
    HasFDerivAt.comp (hg := hg') (hf := hsmul)
  have hdeq : ((fderiv ℝ g (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((fderiv ℝ g (t • x)) x) := by
    apply ContinuousLinearMap.ext
    intro s
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [map_smul]
    rfl
  simpa only [hdeq, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using
    hcomp.hasDerivAt

theorem second_order_taylor_integral (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    g x - g 0 = (fderiv ℝ g 0) x + ∫ t in (0 : ℝ)..1,
      (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x := by
  let h : ℝ → ℝ := fun t => g (t • x)
  let h' : ℝ → ℝ := fun t => (fderiv ℝ g (t • x)) x
  let h'' : ℝ → ℝ := fun t => ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x
  have hh' : ∀ t : ℝ, HasDerivAt h (h' t) t := by
    intro t
    simpa [h, h'] using portPrivate_5734ce2d_hasDerivAt_first g hg x t
  have hh'' : ∀ t : ℝ, HasDerivAt h' (h'' t) t := by
    intro t
    simpa [h', h''] using portPrivate_5734ce2d_hasDerivAt_second g hg x t
  have hcont' : ContinuousOn h' (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hcont : ContinuousOn (fderiv ℝ g) Set.univ := h1.continuousOn
    have hsmul : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hmain : ContinuousOn (fun t : ℝ => (fderiv ℝ g (t • x)) x) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hcAt : ContinuousAt (fderiv ℝ g) (t • x) :=
        (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
      have hcomp : ContinuousAt (fun t : ℝ => fderiv ℝ g (t • x)) t :=
        ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt
      exact (hcomp.clm_apply (continuousAt_const (x := t) (y := x))).continuousWithinAt
    simpa [h'] using hmain
  have hcont'' : ContinuousOn h'' (Set.Icc (0 : ℝ) 1) := by
    have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ g)) Set.univ := by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
        hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ g)) Set.univ := h0.continuousOn
    have hsmul : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hmain : ContinuousOn (fun t : ℝ => ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x)
        (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
        (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
      have hcomp : ContinuousAt (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x)) t :=
        ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt
      exact ((hcomp.clm_apply (continuousAt_const (x := t) (y := x))).clm_apply
        (continuousAt_const (x := t) (y := x))).continuousWithinAt
    simpa [h''] using hmain
  have hcontH : ContDiffOn ℝ 1 h (Set.Icc (0 : ℝ) 1) := by
    have hsmul : ContDiff ℝ 2 (fun t : ℝ => t • x) := by
      exact ContDiff.smul
        (ContDiff.of_le (contDiff_id : ContDiff ℝ ⊤ (id : ℝ → ℝ))
          (by decide : (2 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
        (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => x))
    have hcomp : ContDiff ℝ 2 (fun t : ℝ => g (t • x)) := hg.comp hsmul
    exact (hcomp.contDiffOn.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))).mono (by
      intro t ht
      exact Set.mem_univ t)
  have hFTC : ∫ t in (0 : ℝ)..1, h' t = h 1 - h 0 := by
    have hFTC' : ∫ t in (0 : ℝ)..1, deriv h t = h 1 - h 0 :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcontH (by norm_num : (0 : ℝ) ≤ 1)
    rw [← hFTC']
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hh' t).deriv.symm
  have hIBP : ∫ t in (0 : ℝ)..1, (1 - t) * h'' t = - h' 0 + ∫ t in (0 : ℝ)..1, h' t := by
    have hu : ∀ x : ℝ, x ∈ [[(0 : ℝ), 1]] → HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      intro x hx
      change HasDerivAt ((fun _ : ℝ => 1) - id) (-1) x
      simpa only [zero_sub] using
        (hasDerivAt_const (c := (1 : ℝ)) (x := x)).sub (hasDerivAt_id x)
    have hv : ∀ x : ℝ, x ∈ [[(0 : ℝ), 1]] → HasDerivAt h' (h'' x) x := by
      intro x hx
      exact hh'' x
    have hu' : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hv' : IntervalIntegrable h'' volume (0 : ℝ) 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont''
    have hIBP' := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    simpa [h''] using hIBP'
  calc
    g x - g 0 = h 1 - h 0 := by
      simp [h]
    _ = ∫ t in (0 : ℝ)..1, h' t := hFTC.symm
    _ = h' 0 + ∫ t in (0 : ℝ)..1, (1 - t) * h'' t := by
      rw [hIBP]
      ring
    _ = (fderiv ℝ g 0) x + ∫ t in (0 : ℝ)..1, (1 - t) * h'' t := by
      simp [h', h'']

theorem second_order_taylor_integral_of_fderiv_eq_zero (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E)
    (hx₀ : fderiv ℝ g 0 = 0) :
    g x - g 0 = ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x := by
  rw [second_order_taylor_integral g hg x, hx₀]
  simp

theorem fderiv_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (c y : E) (hg : DifferentiableAt ℝ g (y + c)) :
    fderiv ℝ (fun z : E => g (z + c)) y = fderiv ℝ g (y + c) := by
  have hc : HasFDerivAt (fun z : E => z + c) (1 : E →L[ℝ] E) y := by
    have h := (hasFDerivAt_id (x := y) (𝕜 := ℝ)).add
      (hasFDerivAt_const (x := y) (c := c) (𝕜 := ℝ))
    change HasFDerivAt (id + fun _ : E => c) (1 : E →L[ℝ] E) y
    have hmap : ContinuousLinearMap.id ℝ E + 0 = (1 : E →L[ℝ] E) := by
      ext z
      simp only [ContinuousLinearMap.id_apply, add_zero, one_apply_eq_self]
    rw [hmap] at h
    exact h
  have hcomp : HasFDerivAt (fun z : E => g (z + c))
      (ContinuousLinearMap.comp (fderiv ℝ g (y + c)) (1 : E →L[ℝ] E)) y := by
    exact HasFDerivAt.comp (x := y) (g := g) (g' := fderiv ℝ g (y + c))
      (f := fun z : E => z + c) (f' := (1 : E →L[ℝ] E)) (hg := hg.hasFDerivAt) (hf := hc)
  have hcomp' : HasFDerivAt (fun z : E => g (z + c)) (fderiv ℝ g (y + c)) y := by
    have hmap : (fderiv ℝ g (y + c)).comp (1 : E →L[ℝ] E) = fderiv ℝ g (y + c) := by
      ext z
      rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
    rw [hmap] at hcomp
    exact hcomp
  exact hcomp'.fderiv

theorem fderiv_fderiv_translate (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c y : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) y = fderiv ℝ (fderiv ℝ g) (y + c) := by
  have hfun : fderiv ℝ (fun z : E => g (z + c)) = fun z : E => fderiv ℝ g (z + c) := by
    funext z
    exact fderiv_translate g c z (by
      exact ((hg.contDiffAt (x := z + c)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)))
  have hd : DifferentiableAt ℝ (fderiv ℝ g) (y + c) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact ((h1 (y + c) (Set.mem_univ _)).differentiableWithinAt
      (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
  calc
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) y
        = fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) y := by rw [hfun]
    _ = fderiv ℝ (fderiv ℝ g) (y + c) := fderiv_translate (fderiv ℝ g) c y hd

theorem second_order_polynomial_derivatives
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : E) (c : F) (p : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F) (hB : B.flip = B) :
    let P := fun y => c + p (y - x) + (1 / 2 : ℝ) • B (y - x) (y - x)
    ContDiff ℝ (⊤ : ℕ∞) P ∧ P x = c ∧
      ∀ y, fderiv ℝ P y = p + B (y - x) ∧ fderiv ℝ (fderiv ℝ P) y = B := by
  intro P
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    (contDiff_const.add (p.contDiff.comp (contDiff_id.sub contDiff_const))).add
      (((B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
        (contDiff_id.sub contDiff_const)).const_smul (1 / 2 : ℝ))
  have hderiv (y : E) : HasFDerivAt P (p + B (y - x)) y := by
    have hs := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
    have hlin : HasFDerivAt (fun z => c + p (z - x)) p y := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
        (p.hasFDerivAt.comp y hs).const_add c
    have hquad : HasFDerivAt (fun z => (1 / 2 : ℝ) • B (z - x) (z - x)) (B (y - x)) y := by
      have h := ((B.hasFDerivAt.comp y hs).clm_apply hs).const_smul (1 / 2 : ℝ)
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq, hB, Pi.smul_def,
        ← two_smul ℝ, smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul] using h
    exact hlin.fun_add hquad
  refine ⟨hP, by simp [P], fun y => ⟨(hderiv y).fderiv, ?_⟩⟩
  have heq : fderiv ℝ P = fun z => p + B (z - x) := funext fun z => (hderiv z).fderiv
  rw [heq]
  have hd := (B.hasFDerivAt.comp y ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x)).const_add p
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using hd.fderiv

theorem second_order_taylor_isLittleO
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hD : HasFDerivAt f' f'' x) :
    (fun y => f y - f x - f' x (y - x) - (1 / 2 : ℝ) • f'' (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  have hsym : f''.flip = f'' := by
    ext v w
    exact (second_derivative_symmetric_of_eventually_of_real hf hD v w).symm
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hf
  let P : E → F := fun y => f y - f x - f' x (y - x) - (1 / 2 : ℝ) • f'' (y - x) (y - x)
  let P' : E → E →L[ℝ] F := fun y => f' y - f' x - f'' (y - x)
  have hP (y : E) (hy : y ∈ Metric.ball x r) : HasFDerivAt P (P' y) y := by
    have hs := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
    have hlin : HasFDerivAt (fun z => f' x (z - x)) (f' x) y := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (f' x).hasFDerivAt.comp y hs
    have hquad : HasFDerivAt (fun z => (1 / 2 : ℝ) • f'' (z - x) (z - x))
        (f'' (y - x)) y := by
      have h := ((f''.hasFDerivAt.comp y hs).clm_apply hs).const_smul (1 / 2 : ℝ)
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, hsym, Pi.smul_def,
        ← two_smul ℝ, smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul] using h
    exact (((hball hy).sub_const (f x)).sub hlin).sub hquad
  have hp : P' =o[𝓝[Metric.ball x r] x] (fun y => ‖y - x‖ ^ 1) := by
    simpa only [P', pow_one] using hD.isLittleO.norm_right.mono nhdsWithin_le_nhds
  have h := (convex_ball x r).isLittleO_pow_succ (Metric.mem_ball_self hr)
    (fun y hy => (hP y hy).hasFDerivWithinAt) hp
  rw [Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hr)] at h
  simpa only [P, sub_self, map_zero, smul_zero, sub_zero] using h

theorem second_order_taylor_isLittleO_of_hasFDerivWithinAt_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {L : NNReal} {f : E → F} {s : Set E} {x : E}
    (hs : s ∈ 𝓝 x) (hf : LipschitzOnWith L f s)
    {B : E →L[ℝ] E →L[ℝ] F}
    (hD : HasFDerivWithinAt (fderiv ℝ f) B {y | DifferentiableAt ℝ f y} x) :
    (fun y => f y - f x - fderiv ℝ f x (y - x) - (1 / 2 : ℝ) • B (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  borelize E
  let μ : Measure E := Measure.addHaar
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hbound := hD.isLittleO.bound (half_pos hc)
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhdsWithin_iff.mp hbound
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp hs
  filter_upwards [Metric.ball_mem_nhds x (half_pos (lt_min hr hR))] with y hy
  by_cases hxy : y = x
  · subst y
    simp
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsmall : 2 * ‖y - x‖ < min r R := by
    have hh : ‖y - x‖ < min r R / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    linarith
  have hbs : Metric.ball x (2 * ‖y - x‖) ⊆ s := by
    intro z hz
    exact hRs (lt_trans hz (hsmall.trans_le (min_le_right r R)))
  have hLip := hf.mono hbs
  have hdiff : ∀ᵐ z ∂μ.restrict (Metric.ball x (2 * ‖y - x‖)), DifferentiableAt ℝ f z := by
    filter_upwards [hLip.ae_differentiableWithinAt Metric.isOpen_ball.measurableSet,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzb
    exact hz.differentiableAt (Metric.isOpen_ball.mem_nhds hzb)
  have hest : ∀ᵐ z ∂μ.restrict (Metric.ball x (2 * ‖y - x‖)),
      ‖fderiv ℝ f z - (fderiv ℝ f x - B x) - B z‖ ≤ c * ‖y - x‖ := by
    filter_upwards [hdiff, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hzd hzb
    have hzr : z ∈ Metric.ball x r := lt_trans hzb (hsmall.trans_le (min_le_left r R))
    have h := hrb ⟨hzr, hzd⟩
    have heq : fderiv ℝ f z - (fderiv ℝ f x - B x) - B z =
        fderiv ℝ f z - fderiv ℝ f x - B (z - x) := by rw [map_sub]; abel
    rw [heq]
    calc
      _ ≤ c / 2 * ‖z - x‖ := h
      _ ≤ c / 2 * (2 * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_ball, dist_eq_norm] using (Metric.mem_ball.mp hzb).le) (by positivity)
      _ = c * ‖y - x‖ := by ring
  have hh := norm_sub_quadratic_le_of_ae_norm_fderiv_sub_le Metric.isOpen_ball (convex_ball _ _)
    hLip (fderiv ℝ f x - B x) B (C := ⟨c * ‖y - x‖, by positivity⟩) hest
    (Metric.mem_ball_self (by positivity : 0 < 2 * ‖y - x‖))
    (show y ∈ Metric.ball x (2 * ‖y - x‖) by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have heq : f y - f x - (fderiv ℝ f x - B x) (y - x) - B x (y - x) =
      f y - f x - fderiv ℝ f x (y - x) := by rw [sub_apply]; abel
  rw [heq] at hh
  change ‖f y - f x - fderiv ℝ f x (y - x) - (1 / 2 : ℝ) • B (y - x) (y - x)‖ ≤
    (c * ‖y - x‖) * ‖y - x‖ at hh
  change ‖f y - f x - fderiv ℝ f x (y - x) - (1 / 2 : ℝ) • B (y - x) (y - x)‖ ≤
    c * ‖‖y - x‖ ^ 2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖y - x‖)]
  nlinarith only [hh]

theorem fderiv_fderiv_comp_affine
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (A : E →L[ℝ] F) (c : F) (y v w : E)
    (hf : ContDiffAt ℝ 2 f (c + A y)) :
    fderiv ℝ (fderiv ℝ (fun z => f (c + A z))) y v w =
      fderiv ℝ (fderiv ℝ f) (c + A y) (A v) (A w) := by
  have hg (z : E) : HasFDerivAt (fun q => c + A q) A z := A.hasFDerivAt.const_add c
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (c + A y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : fderiv ℝ (fun z => f (c + A z)) =ᶠ[𝓝 y]
      (fun z => (fderiv ℝ f (c + A z)).comp A) := by
    filter_upwards [(hg y).continuousAt (hf.eventually (by norm_num))] with z hz
    change ContDiffAt ℝ 2 f (c + A z) at hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z (hg z)).fderiv
  rw [heq.fderiv_eq]
  have hdcomp : DifferentiableAt ℝ (fun z => fderiv ℝ f (c + A z)) y :=
    hdf.comp y (hg y).differentiableAt
  rw [fderiv_clm_comp hdcomp (differentiableAt_const A)]
  have hd : fderiv ℝ (fun z => fderiv ℝ f (c + A z)) y =
      (fderiv ℝ (fderiv ℝ f) (c + A y)).comp A :=
    (hdf.hasFDerivAt.comp y (hg y)).fderiv
  rw [hd]
  simp

namespace Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def hadamardFactor (f : ℝ → F) (a : ℝ) (x : ℝ) : F :=
  ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a))

theorem hadamardFactor_contDiff (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hadamardFactor f a) := by
  have hderiv : ContDiff ℝ (⊤ : ℕ∞) (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  have hH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => deriv f (a + p.2 * (p.1 - a))) Set.univ := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => a + p.2 * (p.1 - a)) := by
      fun_prop
    exact hderiv.comp_contDiffOn hinner.contDiffOn
  have hmain := contDiffOn_paramIntervalIntegral
    (f := fun x : ℝ => fun t : ℝ => deriv f (a + t * (x - a))) hH
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ℝ => ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a)))
  exact contDiffOn_univ.mp hmain

theorem hadamard_factorization (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a x : ℝ) :
    f x - f a = (x - a) • hadamardFactor f a x := by
  let w : ℝ := x - a
  let φ : ℝ → F := fun t => f (a + t * w)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    dsimp [φ]
    have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => a + t * w) := by
      fun_prop
    exact hf.comp hinner
  have hφ₁ : ContDiffOn ℝ 1 φ (Set.Icc (0 : ℝ) 1) :=
    (hφ.contDiffOn.of_le (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mono
      (Set.subset_univ _)
  have hFTC : (∫ t in (0 : ℝ)..1, deriv φ t) = φ 1 - φ 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ₁ (by norm_num)
  have hderivφ : ∀ t : ℝ, deriv φ t = w • deriv f (a + t * w) := by
    intro t
    dsimp [φ]
    have hrewrite : (fun t : ℝ => f (a + t * w)) =
        fun t : ℝ => (fun u : ℝ => f (a + u)) (w * t) := by
      funext t
      rw [mul_comm t w]
    rw [hrewrite]
    rw [deriv_comp_mul_left (c := w) (f := fun u : ℝ => f (a + u)) (x := t)]
    rw [deriv_comp_const_add]
    rw [mul_comm w t]
  calc
    f x - f a = φ 1 - φ 0 := by
      dsimp [φ, w]
      have h1 : a + 1 * (x - a) = x := by ring
      have h0 : a + 0 * (x - a) = a := by ring
      rw [h1, h0]
    _ = ∫ t in (0 : ℝ)..1, deriv φ t := hFTC.symm
    _ = ∫ t in (0 : ℝ)..1, w • deriv f (a + t * w) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hderivφ t
    _ = w • ∫ t in (0 : ℝ)..1, deriv f (a + t * w) := by
      rw [intervalIntegral.integral_smul]
    _ = (x - a) • hadamardFactor f a x := by
      simp [hadamardFactor, w]

theorem exists_contDiff_hadamardFactor (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ∃ g : ℝ → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ x : ℝ, f x - f a = (x - a) • g x :=
  ⟨hadamardFactor f a, hadamardFactor_contDiff f hf a, hadamard_factorization f hf a⟩

end Calculus

end

end Analysis
end DifferentialGeometry
