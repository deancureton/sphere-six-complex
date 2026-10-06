module

public import DifferentialGeometry.Topology.Morse.Defs
public import DifferentialGeometry.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral

@[expose] public section

open scoped Filter Interval Topology


namespace DifferentialGeometry.Topology.Morse

open Filter QuadraticForm
open MeasureTheory
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def morseNormalFormWeights (morseIndex : ℕ) : Fin (Module.finrank ℝ E) → ℝ :=
  fun i => if (i : ℕ) < morseIndex then -1 else 1

theorem chartHessian_weightedSumSquares_normalForm (g : E → ℝ)
    (hnd : (QuadraticMap.associated (R := ℝ) (chartHessian g)).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (chartHessian g) (QuadraticMap.weightedSumSquares ℝ w) ∧
          {i : Fin (Module.finrank ℝ E) | w i < 0}.ncard = sigNeg (chartHessian g) := by
  rcases QuadraticForm.equivalent_one_neg_one_weighted_sum_squared (chartHessian g) hnd with
    ⟨w, hw, hEq⟩
  refine ⟨w, hw, hEq, ?_⟩
  exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hEq).symm

omit [FiniteDimensional ℝ E] in
noncomputable def morseTaylorBilin (g : E → ℝ) (x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)

omit [FiniteDimensional ℝ E] in
theorem portPrivate_846ebadb_continuousOn_morseTaylorIntegrand (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ g)) Set.univ := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ g)) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
      (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt).continuousWithinAt
  exact (continuous_const.sub continuous_id).continuousOn.smul hcomp

omit [FiniteDimensional ℝ E] in
theorem second_order_taylor_bilin (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    g x - g 0 = (fderiv ℝ g 0) x + (morseTaylorBilin g x) x x := by
  rw [second_order_taylor_integral g hg x]
  congr 1
  symm
  change (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x x =
    ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x
  have hBint : IntervalIntegrable (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) volume
      (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg x).mono (by intro t ht; exact Set.mem_univ t))
  have hBvCont : ContinuousOn (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x) Set.univ := by
    have hMain : ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ :=
      portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg x
    have hc : ContinuousOn (fun _ : ℝ => x) Set.univ := continuous_const.continuousOn
    exact ContinuousOn.clm_apply hMain hc
  have hBv : IntervalIntegrable (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x) volume
      (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (hBvCont.mono (by intro t ht; exact Set.mem_univ t))
  rw [ContinuousLinearMap.intervalIntegral_apply hBint x]
  rw [ContinuousLinearMap.intervalIntegral_apply hBv x]
  rfl

omit [FiniteDimensional ℝ E] in
theorem second_order_taylor_bilin_of_fderiv_eq_zero (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E)
    (hx₀ : fderiv ℝ g 0 = 0) :
    g x - g 0 = (morseTaylorBilin g x) x x := by
  rw [second_order_taylor_bilin g hg x, hx₀]
  simp

omit [FiniteDimensional ℝ E] in
theorem morseTaylorBilin_zero (g : E → ℝ) :
    morseTaylorBilin g 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) 0 := by
  dsimp [morseTaylorBilin]
  have hrewrite : (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • (0 : E))) =
      fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) 0 := by
    funext t
    rw [smul_zero]
  rw [hrewrite]
  have hInt : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
    have hMain := intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ => (1 : ℝ)) (g := id)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1)
      (continuous_id.continuousOn.intervalIntegrable : IntervalIntegrable id volume (0 : ℝ) 1)
    calc
      ∫ t in (0 : ℝ)..1, (1 - t) = 1 - 2⁻¹ := by
        simpa [intervalIntegral.integral_const, integral_pow] using hMain
      _ = 1 / 2 := by norm_num
  rw [intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ g) 0), hInt]

noncomputable def morseTaylorBilinAt (g : E → ℝ) (c x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (c + t • (x - c))

omit [FiniteDimensional ℝ E] in
theorem morseTaylorBilin_translate (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c x : E) :
    morseTaylorBilin (fun z : E => g (z + c)) x = morseTaylorBilinAt g c (x + c) := by
  dsimp [morseTaylorBilin, morseTaylorBilinAt]
  apply intervalIntegral.integral_congr
  intro t ht
  have hinner : fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) (t • x) =
      fderiv ℝ (fderiv ℝ g) (c + t • x) := by
    rw [fderiv_fderiv_translate g hg c (t • x)]
    congr 1
    abel
  have harg : c + t • x = c + t • (x + c - c) := by
    congr 1
    have hx : x + c - c = x := by abel
    exact (congrArg (fun y : E => t • y) hx).symm
  have hmain : fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) (t • x) =
      fderiv ℝ (fderiv ℝ g) (c + t • (x + c - c)) := by
    rw [hinner]
    exact congrArg (fderiv ℝ (fderiv ℝ g)) harg
  simpa using congrArg (fun L : E →L[ℝ] (E →L[ℝ] ℝ) => (1 - t) • L) hmain

omit [FiniteDimensional ℝ E] in
theorem second_order_taylor_bilin_at (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c x : E) :
    g x - g c = (fderiv ℝ g c) (x - c) + (morseTaylorBilinAt g c x) (x - c) (x - c) := by
  let h : E → ℝ := fun z => g (z + c)
  have hh : ContDiff ℝ 2 h := by
    dsimp [h]
    exact hg.comp (by
      exact (contDiff_id : ContDiff ℝ 2 (fun z : E => z)).add
        (contDiff_const : ContDiff ℝ 2 fun _ : E => c))
  have ht := second_order_taylor_bilin h hh (x - c)
  have h0 : h (x - c) = g x := by simp [h]
  have h00 : h 0 = g c := by simp [h]
  have hfd : fderiv ℝ h 0 = fderiv ℝ g c := by
    dsimp [h]
    simpa using fderiv_translate g c 0 (by
      simpa using ((hg.contDiffAt (x := c)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)))
  have hmtb : morseTaylorBilin h (x - c) = morseTaylorBilinAt g c x := by
    dsimp [h]
    rw [morseTaylorBilin_translate g hg c (x - c)]
    simp [sub_add_cancel]
  rw [h0, h00, hfd, hmtb] at ht
  simpa using ht

section Completion

variable {n : ℕ}

abbrev MorseModel (n : ℕ) : Type :=
  Fin n → ℝ

def morseTail (x : MorseModel (n + 1)) : MorseModel n :=
  fun i => x i.succ

def morseHead (x : MorseModel (n + 1)) : ℝ :=
  x 0

def morseCons (h : ℝ) (t : MorseModel n) : MorseModel (n + 1) :=
  Fin.cons h t

def morseE0 : MorseModel (n + 1) :=
  Fin.cons (1 : ℝ) 0

def morseZeroTail : MorseModel (n + 1) :=
  Fin.cons (0 : ℝ) 0

theorem morseCons_head (h : ℝ) (t : MorseModel n) :
    morseHead (morseCons h t) = h := by
  simp [morseHead, morseCons]

theorem morseCons_tail (h : ℝ) (t : MorseModel n) :
    morseTail (morseCons h t) = t := by
  funext i
  simp [morseTail, morseCons]

theorem morse_cons_decompose (x : MorseModel (n + 1)) :
    x = morseCons (morseHead x) (morseTail x) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseHead, morseCons]
  | succ j => simp [morseTail, morseCons]

theorem morseCons_eq_smul_add (h : ℝ) (t : MorseModel n) :
    morseCons h t = h • morseE0 + morseCons (0 : ℝ) t := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseE0, morseCons]
  | succ j => simp [morseE0, morseCons]

theorem morseCons_add (h₁ h₂ : ℝ) (t₁ t₂ : MorseModel n) :
    morseCons (h₁ + h₂) (t₁ + t₂) = morseCons h₁ t₁ + morseCons h₂ t₂ := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseCons]
  | succ j => simp [morseCons]

@[simp] theorem morseCons_zero_add (t₁ t₂ : MorseModel n) :
    morseCons (0 : ℝ) (t₁ + t₂) = morseCons (0 : ℝ) t₁ + morseCons (0 : ℝ) t₂ := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseCons]
  | succ j => simp [morseCons]

@[simp] theorem morseCons_zero_smul (c : ℝ) (t : MorseModel n) :
    morseCons (0 : ℝ) (c • t) = c • morseCons (0 : ℝ) t := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseCons]
  | succ j => simp [morseCons]

@[simp] theorem morseCons_smul (c : ℝ) (h : ℝ) (t : MorseModel n) :
    morseCons (c * h) (c • t) = c • morseCons h t := by
  funext i
  cases i using Fin.cases with
  | zero => simp [morseCons]
  | succ j => simp [morseCons]

noncomputable def morsePivot (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : ℝ :=
  a x morseE0 morseE0

noncomputable def morseComplete (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : ℝ :=
  morseHead x + a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x

theorem morse_bilinear_expand
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) (h : ℝ) (t : MorseModel n) :
    a x (h • morseE0 + morseCons (0 : ℝ) t) (h • morseE0 + morseCons (0 : ℝ) t) =
      h ^ 2 * a x morseE0 morseE0 +
        h * a x morseE0 (morseCons (0 : ℝ) t) +
        h * a x (morseCons (0 : ℝ) t) morseE0 +
        a x (morseCons (0 : ℝ) t) (morseCons (0 : ℝ) t) := by
  simp [map_add, map_smul]
  ring

theorem morse_complete_square
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hsym : ∀ x y z, a x y z = a x z y) (x : MorseModel (n + 1))
    (hpiv : morsePivot a x ≠ 0) :
    a x x x =
      morsePivot a x * (morseComplete a x) ^ 2 +
        a x (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail x)) -
          a x (morseCons (0 : ℝ) (morseTail x)) morseE0 *
            a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x := by
  calc
    a x x x = a x (morseCons (morseHead x) (morseTail x)) (morseCons (morseHead x) (morseTail x)) := by
      exact congrArg (fun y => a x y y) (morse_cons_decompose x)
    _ = (morseHead x) ^ 2 * a x morseE0 morseE0 +
          morseHead x * a x morseE0 (morseCons (0 : ℝ) (morseTail x)) +
          morseHead x * a x (morseCons (0 : ℝ) (morseTail x)) morseE0 +
          a x (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail x)) := by
      rw [morseCons_eq_smul_add (morseHead x) (morseTail x)]
      rw [morse_bilinear_expand]
    _ = morsePivot a x * (morseComplete a x) ^ 2 +
          a x (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail x)) -
            a x (morseCons (0 : ℝ) (morseTail x)) morseE0 *
              a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x := by
      dsimp [morsePivot, morseComplete, morseHead]
      have hpiv' : a x morseE0 morseE0 ≠ 0 := by
        simpa [morsePivot] using hpiv
      field_simp [hpiv']
      have hcross : a x (morseCons (0 : ℝ) (morseTail x)) morseE0 =
          a x morseE0 (morseCons (0 : ℝ) (morseTail x)) :=
        hsym x (morseCons (0 : ℝ) (morseTail x)) morseE0
      rw [hcross]
      ring

noncomputable def morseCompletionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : MorseModel (n + 1) :=
  morseCons (Real.sqrt |morsePivot a x| * morseComplete a x) (morseTail x)

theorem morseHead_completionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) :
    morseHead (morseCompletionMap a x) = Real.sqrt |morsePivot a x| * morseComplete a x := by
  simp [morseCompletionMap, morseHead, morseCons]

theorem morseTail_completionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) :
    morseTail (morseCompletionMap a x) = morseTail x := by
  funext i
  simp [morseCompletionMap, morseTail, morseCons]

theorem morse_sqrt_square (p c : ℝ) :
    (Real.sqrt |p| * c) ^ 2 = |p| * c ^ 2 := by
  calc
    (Real.sqrt |p| * c) ^ 2 = (Real.sqrt |p|) ^ 2 * c ^ 2 := by ring
    _ = |p| * c ^ 2 := by simp

theorem morse_sign_sqrt_square (p c : ℝ) :
    SignType.sign p * (Real.sqrt |p| * c) ^ 2 = p * c ^ 2 := by
  rw [morse_sqrt_square, ← mul_assoc, sign_mul_abs p]

theorem morse_complete_square_sqrt
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hsym : ∀ x y z, a x y z = a x z y) (x : MorseModel (n + 1))
    (hpiv : morsePivot a x ≠ 0) :
    a x x x =
      SignType.sign (morsePivot a x) * (morseHead (morseCompletionMap a x)) ^ 2 +
        a x (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail x)) -
          a x (morseCons (0 : ℝ) (morseTail x)) morseE0 *
            a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x := by
  rw [morse_complete_square a hsym x hpiv]
  rw [morseHead_completionMap]
  rw [morse_sign_sqrt_square]

noncomputable def morseReducedInner
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) (v : MorseModel n) : MorseModel n →ₗ[ℝ] ℝ :=
  { toFun := fun w =>
      a x (morseCons (0 : ℝ) v) (morseCons (0 : ℝ) w) -
        a x (morseCons (0 : ℝ) v) morseE0 *
          a x morseE0 (morseCons (0 : ℝ) w) / morsePivot a x
    map_add' := by
      intro w₁ w₂
      simp [map_add]
      ring
    map_smul' := by
      intro c w
      simp [map_smul]
      ring }

noncomputable def morseReducedFamily
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : LinearMap.BilinForm ℝ (MorseModel n) :=
  { toFun := fun v => morseReducedInner a x v
    map_add' := by
      intro v₁ v₂
      apply LinearMap.ext
      intro w
      rw [LinearMap.add_apply]
      simp [morseReducedInner, map_add]
      ring
    map_smul' := by
      intro c v
      apply LinearMap.ext
      intro w
      simp [morseReducedInner, map_smul]
      ring }

theorem morseReducedFamily_apply
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) (v w : MorseModel n) :
    morseReducedFamily a x v w =
      a x (morseCons (0 : ℝ) v) (morseCons (0 : ℝ) w) -
        a x (morseCons (0 : ℝ) v) morseE0 *
          a x morseE0 (morseCons (0 : ℝ) w) / morsePivot a x := by
  rfl

theorem morseReducedFamily_sym (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hsym : ∀ x y z, a x y z = a x z y) (x : MorseModel (n + 1)) (v w : MorseModel n) :
    morseReducedFamily a x v w = morseReducedFamily a x w v := by
  rw [morseReducedFamily_apply, morseReducedFamily_apply]
  rw [hsym x (morseCons (0 : ℝ) v) (morseCons (0 : ℝ) w)]
  rw [hsym x (morseCons (0 : ℝ) v) morseE0]
  rw [hsym x morseE0 (morseCons (0 : ℝ) w)]
  ring

theorem morseHead_add (v w : MorseModel (n + 1)) :
    morseHead (v + w) = morseHead v + morseHead w := by
  simp [morseHead]

theorem morseTail_add (v w : MorseModel (n + 1)) :
    morseTail (v + w) = morseTail v + morseTail w := by
  funext i
  rfl

theorem morseHead_smul (c : ℝ) (v : MorseModel (n + 1)) :
    morseHead (c • v) = c * morseHead v := by
  simp [morseHead]

theorem morseTail_smul (c : ℝ) (v : MorseModel (n + 1)) :
    morseTail (c • v) = c • morseTail v := by
  funext i
  rfl

noncomputable def morseCompletionDerivMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (v : MorseModel (n + 1)) : MorseModel (n + 1) :=
  morseCons (Real.sqrt |morsePivot a 0| * (morseHead v + d' v / morsePivot a 0)) (morseTail v)

noncomputable def morseCompletionDeriv
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) : MorseModel (n + 1) →ₗ[ℝ] MorseModel (n + 1) :=
  { toFun := morseCompletionDerivMap a d'
    map_add' := by
      intro v w
      dsimp [morseCompletionDerivMap]
      rw [morseHead_add, morseTail_add, map_add]
      have hhead :
          Real.sqrt |morsePivot a 0| * (morseHead v + morseHead w + (d' v + d' w) / morsePivot a 0) =
            Real.sqrt |morsePivot a 0| * (morseHead v + d' v / morsePivot a 0) +
              Real.sqrt |morsePivot a 0| * (morseHead w + d' w / morsePivot a 0) := by
        rw [add_div]
        ring
      rw [hhead]
      rw [morseCons_add]
    map_smul' := by
      intro c v
      dsimp [morseCompletionDerivMap]
      rw [morseHead_smul, morseTail_smul, map_smul]
      have hhead : Real.sqrt |morsePivot a 0| * (c * morseHead v + (c • d' v) / morsePivot a 0) =
          c * (Real.sqrt |morsePivot a 0| * (morseHead v + d' v / morsePivot a 0)) := by
        rw [smul_eq_mul]
        ring
      rw [hhead]
      funext i
      cases i using Fin.cases with
      | zero => simp [morseCons]
      | succ j => simp [morseCons]
      }

theorem morseHead_completionDeriv (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (v : MorseModel (n + 1)) :
    morseHead (morseCompletionDeriv a d' v) =
      Real.sqrt |morsePivot a 0| * (morseHead v + d' v / morsePivot a 0) := by
  simp [morseCompletionDeriv, morseCompletionDerivMap, morseHead, morseCons]

theorem morseTail_completionDeriv (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (v : MorseModel (n + 1)) :
    morseTail (morseCompletionDeriv a d' v) = morseTail v := by
  funext i
  simp [morseCompletionDeriv, morseCompletionDerivMap, morseTail, morseCons]

theorem apply_eq_apply_morseCons_tail_of_apply_morseE0_eq_zero (d' : MorseModel (n + 1) →L[ℝ] ℝ) (hd₀ : d' morseE0 = 0)
    (v : MorseModel (n + 1)) :
    d' v = d' (morseCons (0 : ℝ) (morseTail v)) := by
  conv_lhs =>
    rw [morse_cons_decompose v, morseCons_eq_smul_add]
  rw [map_add, map_smul, hd₀, smul_eq_mul, mul_zero, zero_add]

theorem morseCompletionDeriv_injective (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (hpiv : morsePivot a 0 ≠ 0) (hd₀ : d' morseE0 = 0) :
    Function.Injective (morseCompletionDeriv a d') := by
  intro v w h
  have hhead : Real.sqrt |morsePivot a 0| * (morseHead v + d' v / morsePivot a 0) =
      Real.sqrt |morsePivot a 0| * (morseHead w + d' w / morsePivot a 0) := by
    have := congrArg morseHead h
    rw [morseHead_completionDeriv, morseHead_completionDeriv] at this
    exact this
  have htail : morseTail v = morseTail w := by
    have := congrArg morseTail h
    rw [morseTail_completionDeriv, morseTail_completionDeriv] at this
    exact this
  have hsq : Real.sqrt |morsePivot a 0| ≠ 0 := by
    exact (Real.sqrt_pos.2 (abs_pos.mpr hpiv)).ne'
  have hmain : morseHead v + d' v / morsePivot a 0 = morseHead w + d' w / morsePivot a 0 := by
    exact (mul_left_cancel₀ hsq hhead)
  have hdv : d' v = d' (morseCons (0 : ℝ) (morseTail v)) := apply_eq_apply_morseCons_tail_of_apply_morseE0_eq_zero d' hd₀ v
  have hdw : d' w = d' (morseCons (0 : ℝ) (morseTail w)) := apply_eq_apply_morseCons_tail_of_apply_morseE0_eq_zero d' hd₀ w
  have hd'eq : d' v = d' w := by
    rw [hdv, hdw, htail]
  have hh : morseHead v = morseHead w := by
    rw [hd'eq] at hmain
    linarith
  rw [morse_cons_decompose v, morse_cons_decompose w]
  rw [hh, htail]

theorem morseCompletionDeriv_surjective (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (hpiv : morsePivot a 0 ≠ 0) (hd₀ : d' morseE0 = 0) :
    Function.Surjective (morseCompletionDeriv a d') := by
  intro y
  let s : ℝ := Real.sqrt |morsePivot a 0|
  have hsq : s ≠ 0 := by
    exact (Real.sqrt_pos.2 (abs_pos.mpr hpiv)).ne'
  let v : MorseModel (n + 1) :=
    morseCons (morseHead y / s - d' (morseCons (0 : ℝ) (morseTail y)) / morsePivot a 0) (morseTail y)
  refine ⟨v, ?_⟩
  have hd' : d' v = d' (morseCons (0 : ℝ) (morseTail y)) := by
    have hsplit : v =
        (morseHead y / s - d' (morseCons (0 : ℝ) (morseTail y)) / morsePivot a 0) • morseE0 +
          morseCons (0 : ℝ) (morseTail y) := by
      rw [← morseCons_eq_smul_add (morseHead y / s - d' (morseCons (0 : ℝ) (morseTail y)) / morsePivot a 0)
        (morseTail y)]
    rw [hsplit]
    simp [map_add, map_smul, hd₀, smul_eq_mul]
  have hmv : morseHead v =
      morseHead y / s - d' (morseCons (0 : ℝ) (morseTail y)) / morsePivot a 0 := by
    simp [v, morseHead, morseCons]
  funext i
  cases i using Fin.cases with
  | zero =>
      change morseHead (morseCompletionDeriv a d' v) = y (0 : Fin (n + 1))
      rw [morseHead_completionDeriv, hd', hmv]
      field_simp [hsq, hpiv]
      simp [s, morseHead]
      ring_nf
  | succ j =>
      simp [morseCompletionDeriv, morseCompletionDerivMap, v, morseCons, morseTail]

theorem morseComplete_zero (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1))) :
    morseComplete a 0 = 0 := by
  have hz : a 0 morseE0 (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1)))) = 0 := by
    have hz' : morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1))) = 0 := by
      funext i
      cases i using Fin.cases <;> simp [morseCons, morseTail]
    rw [hz']
    exact map_zero (a 0 morseE0)
  simp [morseComplete, morseHead, hz]

noncomputable def morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin (n + 1))).toContinuousLinearMap

theorem hasFDerivAt_morseHead : HasFDerivAt (fun x : MorseModel (n + 1) => morseHead x)
    morseHeadProj 0 := by
  simpa [morseHead, morseHeadProj] using
    (morseHeadProj.hasFDerivAt)

noncomputable def morseSqrtDeriv (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' : MorseModel (n + 1) →L[ℝ] ℝ) : MorseModel (n + 1) →L[ℝ] ℝ :=
  ((1 : ℝ →L[ℝ] ℝ).smulRight (1 / (2 * Real.sqrt |morsePivot a 0|))).comp
    (((1 : ℝ →L[ℝ] ℝ).smulRight (SignType.sign (morsePivot a 0) : ℝ)).comp p')

theorem hasFDerivAt_sqrt_abs_morsePivot
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' : MorseModel (n + 1) →L[ℝ] ℝ) (hs : HasFDerivAt (fun x => morsePivot a x) p' 0)
    (hpiv : morsePivot a 0 ≠ 0) :
    HasFDerivAt (fun x => Real.sqrt |morsePivot a x|) (morseSqrtDeriv a p') 0 := by
  have habs : HasFDerivAt (|·|) ((1 : ℝ →L[ℝ] ℝ).smulRight (SignType.sign (morsePivot a 0)))
      (morsePivot a 0) := by
    exact hasDerivAt_iff_hasFDerivAt.mpr (hasDerivAt_abs hpiv)
  have hsqrt : HasFDerivAt (Real.sqrt)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (1 / (2 * Real.sqrt |morsePivot a 0|))) |morsePivot a 0| := by
    exact hasDerivAt_iff_hasFDerivAt.mpr (Real.hasDerivAt_sqrt (abs_pos.mpr hpiv).ne')
  have hinner : HasFDerivAt (fun x => |morsePivot a x|)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (SignType.sign (morsePivot a 0) : ℝ)).comp p') 0 :=
    HasFDerivAt.comp 0 (hg := habs) (hf := hs)
  have hcomp : HasFDerivAt (fun x => Real.sqrt (|morsePivot a x|))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (1 / (2 * Real.sqrt |morsePivot a 0|))).comp
        (((1 : ℝ →L[ℝ] ℝ).smulRight (SignType.sign (morsePivot a 0) : ℝ)).comp p')) 0 :=
    HasFDerivAt.comp 0 (hg := hsqrt) (hf := hinner)
  simpa [morseSqrtDeriv, Function.comp_def] using hcomp

noncomputable def morseCompleteDeriv
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) : MorseModel (n + 1) →L[ℝ] ℝ :=
  morseHeadProj + (morsePivot a 0)⁻¹ • d'

theorem hasFDerivAt_morseComplete
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' d' : MorseModel (n + 1) →L[ℝ] ℝ)
    (hs : HasFDerivAt (fun x => morsePivot a x) p' 0)
    (hd : HasFDerivAt (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) d' 0)
    (hpiv : morsePivot a 0 ≠ 0) :
    HasFDerivAt (morseComplete a) (morseCompleteDeriv a d') 0 := by
  have hinvDeriv : HasFDerivAt (fun x => (morsePivot a x)⁻¹)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (-(morsePivot a 0 ^ 2)⁻¹)).comp p') 0 := by
    have hinvAt : HasFDerivAt (fun y : ℝ => y⁻¹)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(morsePivot a 0 ^ 2)⁻¹)) (morsePivot a 0) := by
      exact hasDerivAt_iff_hasFDerivAt.mpr (hasDerivAt_inv hpiv)
    exact HasFDerivAt.comp 0 (hg := hinvAt) (hf := hs)
  have hnum0 : a 0 morseE0 (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1)))) = 0 := by
    have hz : morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1))) = 0 := by
      funext i
      cases i using Fin.cases <;> simp [morseCons, morseTail]
    rw [hz]
    exact map_zero (a 0 morseE0)
  have hmul : HasFDerivAt
      (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x)) * (morsePivot a x)⁻¹)
      ((morsePivot a 0)⁻¹ • d') 0 := by
    have hmul' : HasFDerivAt
        (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x)) * (morsePivot a x)⁻¹)
        ((a 0 morseE0 (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1))))) •
            (((1 : ℝ →L[ℝ] ℝ).smulRight (-(morsePivot a 0 ^ 2)⁻¹)).comp p') +
          (morsePivot a 0)⁻¹ • d') 0 :=
      HasFDerivAt.mul hd hinvDeriv
    have hdeq : ((a 0 morseE0 (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1))))) •
            (((1 : ℝ →L[ℝ] ℝ).smulRight (-(morsePivot a 0 ^ 2)⁻¹)).comp p') +
          (morsePivot a 0)⁻¹ • d') = ((morsePivot a 0)⁻¹ • d') := by
      ext v
      simp [hnum0]
    simpa [hdeq] using hmul'
  have hsum : HasFDerivAt
      (fun x => morseHead x + a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x)
      (morseCompleteDeriv a d') 0 := by
    have hdiv : HasFDerivAt
        (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x)
        ((morsePivot a 0)⁻¹ • d') 0 := by
      simpa [div_eq_mul_inv] using hmul
    have hadd : HasFDerivAt
        (fun x => morseHead x + a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x)
        (morseHeadProj + (morsePivot a 0)⁻¹ • d') 0 :=
      HasFDerivAt.add hasFDerivAt_morseHead hdiv
    simpa [morseCompleteDeriv] using hadd
  change HasFDerivAt
    (fun x => morseHead x + a x morseE0 (morseCons (0 : ℝ) (morseTail x)) / morsePivot a x)
    (morseCompleteDeriv a d') 0
  exact hsum

noncomputable def morseConsLinear : (ℝ × MorseModel n) →ₗ[ℝ] MorseModel (n + 1) :=
  { toFun := fun p => morseCons p.1 p.2
    map_add' := by
      intro p q
      exact morseCons_add p.1 q.1 p.2 q.2
    map_smul' := by
      intro c p
      simp [morseCons_smul] }

noncomputable def morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1) :=
  morseConsLinear.toContinuousLinearMap

noncomputable def morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n :=
  ({ toFun := fun v => morseTail v
     map_add' := by intro v w; exact morseTail_add v w
     map_smul' := by intro c v; exact morseTail_smul c v } :
      MorseModel (n + 1) →ₗ[ℝ] MorseModel n).toContinuousLinearMap

theorem hasFDerivAt_morseTailProj :
    HasFDerivAt (fun x : MorseModel (n + 1) => morseTail x) morseTailProj 0 := by
  simpa [morseTailProj] using (morseTailProj.hasFDerivAt)

theorem hasFDerivAt_morseCompletionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' d' : MorseModel (n + 1) →L[ℝ] ℝ)
    (hs : HasFDerivAt (fun x => morsePivot a x) p' 0)
    (hd : HasFDerivAt (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) d' 0)
    (hpiv : morsePivot a 0 ≠ 0) :
    HasFDerivAt (morseCompletionMap a) (morseCompletionDeriv a d').toContinuousLinearMap 0 := by
  have hsqrt := hasFDerivAt_sqrt_abs_morsePivot a p' hs hpiv
  have hcomplete := hasFDerivAt_morseComplete a p' d' hs hd hpiv
  have hprod : HasFDerivAt
      (fun x => Real.sqrt |morsePivot a x| * morseComplete a x)
      (Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d') +
        morseComplete a 0 • morseSqrtDeriv a p') 0 :=
    HasFDerivAt.mul hsqrt hcomplete
  have hprod' : HasFDerivAt
      (fun x => Real.sqrt |morsePivot a x| * morseComplete a x)
      (Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d')) 0 := by
    have hdeq : Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d') +
          morseComplete a 0 • morseSqrtDeriv a p' =
        Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d') := by
      ext v
      simp [morseComplete_zero]
    simpa [hdeq] using hprod
  have hpair : HasFDerivAt
      (fun x => (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x))
      ((Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d')).prod morseTailProj) 0 :=
    HasFDerivAt.prodMk hprod' hasFDerivAt_morseTailProj
  have hcons : HasFDerivAt (fun x : ℝ × MorseModel n => morseCons x.1 x.2)
      morseConsLinearCLM 0 := by
    simpa [morseConsLinearCLM, morseConsLinear] using (morseConsLinearCLM.hasFDerivAt)
  have hcomp : HasFDerivAt (fun x => morseConsLinearCLM (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x))
      (morseConsLinearCLM.comp
        ((Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d')).prod morseTailProj)) 0 :=
    by
      have hcons' : HasFDerivAt (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
          morseConsLinearCLM (Real.sqrt |morsePivot a 0| * morseComplete a 0, morseTail 0) :=
        morseConsLinearCLM.hasFDerivAt
      exact HasFDerivAt.comp 0 (hg := hcons') (hf := hpair)
  have heq : (morseConsLinearCLM.comp
        ((Real.sqrt |morsePivot a 0| • (morseCompleteDeriv a d')).prod morseTailProj)) =
      (morseCompletionDeriv a d').toContinuousLinearMap := by
    ext v i
    dsimp [morseConsLinearCLM, morseConsLinear, morseTailProj, morseCompleteDeriv,
      morseCompletionDeriv, morseCompletionDerivMap, morseHeadProj, morseHead]
    cases i using Fin.cases with
    | zero =>
        simp only [morseCons, Fin.cons_zero, div_eq_mul_inv,
          add_apply, smul_apply]
        have hproj : (LinearMap.toContinuousLinearMap (LinearMap.proj (R := ℝ) 0)) v = v 0 := by
          simpa only [LinearMap.coe_toContinuousLinearMap'] using
            (LinearMap.proj_apply (R := ℝ) 0 v)
        rw [hproj]
        simp only [smul_eq_mul]
        ring
    | succ j =>
        simp only [morseCons, Fin.cons_succ]
  have hfinal : HasFDerivAt (fun x => morseConsLinearCLM (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x))
      (morseCompletionDeriv a d').toContinuousLinearMap 0 := by
    simpa [heq] using hcomp
  have hfun :
      (fun x => morseConsLinearCLM
        (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x)) =
        morseCompletionMap a := by
    funext x i
    rfl
  rw [← hfun]
  exact hfinal

noncomputable def morseCompletionDerivCLE
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (d' : MorseModel (n + 1) →L[ℝ] ℝ) (hpiv : morsePivot a 0 ≠ 0) (hd₀ : d' morseE0 = 0) :
    MorseModel (n + 1) ≃L[ℝ] MorseModel (n + 1) :=
  (LinearEquiv.ofBijective (morseCompletionDeriv a d')
    ⟨morseCompletionDeriv_injective a d' hpiv hd₀,
      morseCompletionDeriv_surjective a d' hpiv hd₀⟩).toContinuousLinearEquiv

theorem hasFDerivAt_morseCompletionMap_CLE
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' d' : MorseModel (n + 1) →L[ℝ] ℝ)
    (hs : HasFDerivAt (fun x => morsePivot a x) p' 0)
    (hd : HasFDerivAt (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) d' 0)
    (hpiv : morsePivot a 0 ≠ 0) (hd₀ : d' morseE0 = 0) :
    HasFDerivAt (morseCompletionMap a)
      (morseCompletionDerivCLE a d' hpiv hd₀ : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 := by
  have heq :
      (morseCompletionDerivCLE a d' hpiv hd₀ : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) =
        (morseCompletionDeriv a d').toContinuousLinearMap := by
    ext v
    rfl
  rw [heq]
  exact hasFDerivAt_morseCompletionMap a p' d' hs hd hpiv

theorem contDiffAt_morsePivotSqrt
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hcontp : ContDiffAt ℝ 1 (fun x => morsePivot a x) 0) (hpiv : morsePivot a 0 ≠ 0) :
    ContDiffAt ℝ 1 (fun x => Real.sqrt |morsePivot a x|) 0 := by
  have habsp : ContDiffAt ℝ 1 (fun x => |morsePivot a x|) 0 := by
    exact ContDiffAt.comp 0 (contDiffAt_abs hpiv) hcontp
  have hsqrt : ContDiffAt ℝ 1 (Real.sqrt) |morsePivot a 0| :=
    Real.contDiffAt_sqrt (abs_pos.mpr hpiv).ne'
  simpa [Function.comp_def] using (ContDiffAt.comp 0 hsqrt habsp)

theorem contDiffAt_morseComplete
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hcontp : ContDiffAt ℝ 1 (fun x => morsePivot a x) 0)
    (hcontd : ContDiffAt ℝ 1 (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) 0)
    (hpiv : morsePivot a 0 ≠ 0) :
    ContDiffAt ℝ 1 (morseComplete a) 0 := by
  have hhead : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseHead x) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseHeadProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hinv : ContDiffAt ℝ 1 (fun x => (morsePivot a x)⁻¹) 0 := hcontp.inv hpiv
  have hquot : ContDiffAt ℝ 1
      (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x)) * (morsePivot a x)⁻¹) 0 :=
    ContDiffAt.mul hcontd hinv
  have hadd : ContDiffAt ℝ 1
      (fun x => morseHead x + a x morseE0 (morseCons (0 : ℝ) (morseTail x)) * (morsePivot a x)⁻¹) 0 :=
    ContDiffAt.add hhead hquot
  change ContDiffAt ℝ 1
    (fun x => morseHead x +
      a x morseE0 (morseCons (0 : ℝ) (morseTail x)) * (morsePivot a x)⁻¹) 0
  exact hadd

theorem contDiffAt_morseCompletionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (hcontp : ContDiffAt ℝ 1 (fun x => morsePivot a x) 0)
    (hcontd : ContDiffAt ℝ 1 (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) 0)
    (hpiv : morsePivot a 0 ≠ 0) :
    ContDiffAt ℝ 1 (morseCompletionMap a) 0 := by
  have hsqrt := contDiffAt_morsePivotSqrt a hcontp hpiv
  have hcomplete := contDiffAt_morseComplete a hcontp hcontd hpiv
  have hprod : ContDiffAt ℝ 1 (fun x => Real.sqrt |morsePivot a x| * morseComplete a x) 0 :=
    ContDiffAt.mul hsqrt hcomplete
  have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hcons : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (Real.sqrt |morsePivot a 0| * morseComplete a 0, morseTail (0 : MorseModel (n + 1))) := by
    exact ((morseConsLinearCLM.contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun p => morseConsLinearCLM p)
          (Real.sqrt |morsePivot a 0| * morseComplete a 0, morseTail (0 : MorseModel (n + 1)))).of_le
      (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hpair : ContDiffAt ℝ 1
      (fun x => (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x)) 0 :=
    ContDiffAt.prodMk hprod htail
  have hcomp : ContDiffAt ℝ 1
      (fun x => morseConsLinearCLM (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x)) 0 :=
    ContDiffAt.comp 0 hcons hpair
  have hfun :
      (fun x => morseConsLinearCLM
        (Real.sqrt |morsePivot a x| * morseComplete a x, morseTail x)) =
        morseCompletionMap a := by
    funext x i
    rfl
  rw [← hfun]
  exact hcomp

theorem isLocalHomeomorphAt_morseCompletionMap
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (p' d' : MorseModel (n + 1) →L[ℝ] ℝ)
    (hs : HasFDerivAt (fun x => morsePivot a x) p' 0)
    (hd : HasFDerivAt (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) d' 0)
    (hpiv : morsePivot a 0 ≠ 0) (hd₀ : d' morseE0 = 0)
    (hcontp : ContDiffAt ℝ 1 (fun x => morsePivot a x) 0)
    (hcontd : ContDiffAt ℝ 1 (fun x => a x morseE0 (morseCons (0 : ℝ) (morseTail x))) 0) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseCompletionMap a ∧ 0 ∈ φ.source := by
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morseCompletionMap a)
      (f' := morseCompletionDerivCLE a d' hpiv hd₀)
      (contDiffAt_morseCompletionMap a hcontp hcontd hpiv)
      (hasFDerivAt_morseCompletionMap_CLE a p' d' hs hd hpiv hd₀)
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  refine ⟨φ, ?_, ?_⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

noncomputable def morsePartial (f : MorseModel (n + 1) → ℝ) : MorseModel (n + 1) → ℝ :=
  fun x => fderiv ℝ f x morseE0

noncomputable def morsePartialMap (f : MorseModel (n + 1) → ℝ) : MorseModel (n + 1) → MorseModel (n + 1) :=
  fun x => morseCons (morsePartial f x) (morseTail x)

noncomputable def morsePartialDeriv (p' : MorseModel (n + 1) →L[ℝ] ℝ) :
    MorseModel (n + 1) →ₗ[ℝ] MorseModel (n + 1) :=
  { toFun := fun v => morseCons (p' v) (morseTail v)
    map_add' := by
      intro v w
      rw [morseTail_add, map_add, morseCons_add]
    map_smul' := by
      intro c v
      rw [morseTail_smul, map_smul, smul_eq_mul]
      rw [morseCons_smul]
      rfl }

theorem morsePartialDeriv_injective (p' : MorseModel (n + 1) →L[ℝ] ℝ)
    (h₀ : p' morseE0 ≠ 0) : Function.Injective (morsePartialDeriv p') := by
  intro v w h
  have hhead : p' v = p' w := by
    have := congrArg morseHead h
    simpa [morsePartialDeriv, morseHead, morseCons] using this
  have htail : morseTail v = morseTail w := by
    have := congrArg morseTail h
    change morseTail (morseCons (p' v) (morseTail v)) =
      morseTail (morseCons (p' w) (morseTail w)) at this
    rw [morseCons_tail, morseCons_tail] at this
    exact this
  have hlin : ∀ u : MorseModel (n + 1),
      p' u = morseHead u * p' morseE0 + p' (morseCons (0 : ℝ) (morseTail u)) := by
    intro u
    conv_lhs =>
      rw [morse_cons_decompose u, morseCons_eq_smul_add (morseHead u) (morseTail u)]
    simp [map_add, map_smul, smul_eq_mul]
  have hmul : morseHead v * p' morseE0 = morseHead w * p' morseE0 := by
    rw [hlin v, hlin w] at hhead
    rw [htail] at hhead
    linarith
  have : morseHead v = morseHead w := mul_right_cancel₀ h₀ hmul
  rw [morse_cons_decompose v, morse_cons_decompose w]
  rw [this, htail]

theorem morsePartialDeriv_surjective (p' : MorseModel (n + 1) →L[ℝ] ℝ)
    (h₀ : p' morseE0 ≠ 0) : Function.Surjective (morsePartialDeriv p') := by
  intro y
  let v : MorseModel (n + 1) :=
    morseCons ((morseHead y - p' (morseCons (0 : ℝ) (morseTail y))) / p' morseE0) (morseTail y)
  refine ⟨v, ?_⟩
  have hlin : p' v = morseHead v * p' morseE0 + p' (morseCons (0 : ℝ) (morseTail v)) := by
    conv_lhs =>
      rw [morse_cons_decompose v, morseCons_eq_smul_add (morseHead v) (morseTail v)]
    simp [map_add, map_smul, smul_eq_mul]
  have hmv : morseHead v = (morseHead y - p' (morseCons (0 : ℝ) (morseTail y))) / p' morseE0 := by
    simp [v, morseHead, morseCons]
  ext i
  cases i using Fin.cases with
  | zero =>
      have hzero : (morsePartialDeriv p' v) (0 : Fin (n + 1)) = p' v := by
        dsimp [morsePartialDeriv, morseCons]
        rfl
      rw [hzero]
      rw [hlin, hmv]
      have htv : morseTail v = morseTail y := by
        funext j
        simp [v, morseTail, morseCons, Fin.cons_succ]
      rw [htv]
      field_simp [h₀]
      simp [morseHead]
  | succ j =>
      simp [v, morseCons, morseTail, morsePartialDeriv, Fin.cons_succ]

noncomputable def morsePartialDerivCLE (p' : MorseModel (n + 1) →L[ℝ] ℝ)
    (h₀ : p' morseE0 ≠ 0) : MorseModel (n + 1) ≃L[ℝ] MorseModel (n + 1) :=
  (LinearEquiv.ofBijective (morsePartialDeriv p')
    (show Function.Bijective (morsePartialDeriv p') from
      ⟨morsePartialDeriv_injective p' h₀, morsePartialDeriv_surjective p' h₀⟩)).toContinuousLinearEquiv

theorem hasFDerivAt_morsePartialMap (f : MorseModel (n + 1) → ℝ)
    (hdf : DifferentiableAt ℝ (morsePartial f) 0)
    (h₀ : fderiv ℝ (morsePartial f) 0 morseE0 ≠ 0) :
    HasFDerivAt (morsePartialMap f)
      (morsePartialDerivCLE (fderiv ℝ (morsePartial f) 0) h₀ :
        MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 := by
  have hcons : HasFDerivAt (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      morseConsLinearCLM (morsePartial f 0, morseTail (0 : MorseModel (n + 1))) :=
    morseConsLinearCLM.hasFDerivAt
  have hhead : HasFDerivAt (fun x : MorseModel (n + 1) => morsePartial f x)
      (fderiv ℝ (morsePartial f) 0) 0 := hdf.hasFDerivAt
  have htail : HasFDerivAt (fun x : MorseModel (n + 1) => morseTail x) morseTailProj 0 :=
    hasFDerivAt_morseTailProj
  have hpair : HasFDerivAt (fun x => (morsePartial f x, morseTail x))
      ((fderiv ℝ (morsePartial f) 0).prod morseTailProj) 0 :=
    HasFDerivAt.prodMk hhead htail
  have hcomp : HasFDerivAt (fun x => morseConsLinearCLM (morsePartial f x, morseTail x))
      (morseConsLinearCLM.comp ((fderiv ℝ (morsePartial f) 0).prod morseTailProj)) 0 :=
    HasFDerivAt.comp 0 (hg := hcons) (hf := hpair)
  have heq : (morseConsLinearCLM.comp ((fderiv ℝ (morsePartial f) 0).prod morseTailProj)) =
      (morsePartialDerivCLE (fderiv ℝ (morsePartial f) 0) h₀ :
        MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) := by
    ext v
    simp [morseConsLinearCLM, morseConsLinear, morseTailProj, morsePartialDerivCLE,
      morsePartialDeriv]
  rw [heq] at hcomp
  have hfun :
      (fun x => morseConsLinearCLM (morsePartial f x, morseTail x)) = morsePartialMap f := by
    funext x i
    rfl
  rw [← hfun]
  exact hcomp

theorem isLocalHomeomorphAt_morsePartialMap (f : MorseModel (n + 1) → ℝ)
    (hdf : DifferentiableAt ℝ (morsePartial f) 0)
    (hcont : ContDiffAt ℝ 1 (morsePartial f) 0)
    (h₀ : fderiv ℝ (morsePartial f) 0 morseE0 ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f ∧ 0 ∈ φ.source := by
  have hcont : ContDiffAt ℝ 1 (morsePartialMap f) 0 := by
    have hhead : ContDiffAt ℝ 1 (morsePartial f) 0 := hcont
    have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
          (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
    have hpair : ContDiffAt ℝ 1 (fun x => (morsePartial f x, morseTail x)) 0 :=
      ContDiffAt.prodMk hhead htail
    have hcons : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morsePartial f 0, morseTail (0 : MorseModel (n + 1))) := by
      exact ((morseConsLinearCLM.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun p => morseConsLinearCLM p)
        (morsePartial f 0, morseTail (0 : MorseModel (n + 1)))).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
    have hcomp : ContDiffAt ℝ 1
        (fun x => morseConsLinearCLM (morsePartial f x, morseTail x)) 0 :=
      ContDiffAt.comp 0 hcons hpair
    have hfun :
        (fun x => morseConsLinearCLM (morsePartial f x, morseTail x)) = morsePartialMap f := by
      funext x i
      rfl
    rw [← hfun]
    exact hcomp
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morsePartialMap f)
      (f' := morsePartialDerivCLE (fderiv ℝ (morsePartial f) 0) h₀)
      hcont (hasFDerivAt_morsePartialMap f hdf h₀) (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  refine ⟨φ, ?_, ?_⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

noncomputable def morseCriticalSection (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (x' : MorseModel n) : ℝ :=
  morseHead (φ.symm (morseCons (0 : ℝ) x'))

theorem morseCriticalSection_eq (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hy : morseCons (0 : ℝ) x' ∈ φ.target) :
    morsePartial f (morseCons (morseCriticalSection φ x') x') = 0 := by
  have hrinv : φ (φ.symm (morseCons (0 : ℝ) x')) = morseCons (0 : ℝ) x' := φ.right_inv hy
  have hmorse : morsePartialMap f (φ.symm (morseCons (0 : ℝ) x')) = morseCons (0 : ℝ) x' := by
    simpa [hφ] using hrinv
  have hhead : morsePartial f (φ.symm (morseCons (0 : ℝ) x')) = 0 := by
    have := congrArg morseHead hmorse
    simpa [morsePartialMap, morseHead, morseCons] using this
  have htail : morseTail (φ.symm (morseCons (0 : ℝ) x')) = x' := by
    have := congrArg morseTail hmorse
    funext j
    simpa [morsePartialMap, morseTail, morseCons] using congrFun this j
  have hdecomp : φ.symm (morseCons (0 : ℝ) x') =
      morseCons (morseHead (φ.symm (morseCons (0 : ℝ) x'))) x' := by
    rw [morse_cons_decompose (φ.symm (morseCons (0 : ℝ) x'))]
    exact congrArg (morseCons (morseHead (φ.symm (morseCons (0 : ℝ) x')))) htail
  rw [morseCriticalSection]
  rw [← hdecomp]
  exact hhead

theorem morseCriticalSection_tail (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hy : morseCons (0 : ℝ) x' ∈ φ.target) :
    morseTail (φ.symm (morseCons (0 : ℝ) x')) = x' := by
  have hφf : φ (φ.symm (morseCons (0 : ℝ) x')) = morsePartialMap f (φ.symm (morseCons (0 : ℝ) x')) := by
    rw [hφ]
  rw [φ.right_inv hy] at hφf
  have := congrArg morseTail hφf
  funext j
  simpa [morsePartialMap, morseTail, morseCons] using (congrFun this j).symm

theorem morseCriticalSection_zero (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hcrit : fderiv ℝ f 0 = 0) (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source) :
    φ.symm (morseCons (0 : ℝ) (0 : MorseModel n)) = 0 := by
  have hφ0 : φ 0 = 0 := by
    have hφm : φ 0 = morsePartialMap f 0 := by rw [hφ]
    rw [hφm]
    funext i
    cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, hcrit, morseCons, morseTail]
  have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
    funext i
    cases i using Fin.cases <;> simp [morseCons]
  rw [hz]
  conv_lhs => rw [← hφ0]
  exact φ.left_inv hsrc

end Completion

omit [FiniteDimensional ℝ E] in
theorem portPrivate_846ebadb_hasFDerivAt_third_morse (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x : E) (t : ℝ) :
    HasFDerivAt (fun x : E => fderiv ℝ (fderiv ℝ g) (t • x))
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))) x := by
  have hsmul : HasFDerivAt (fun x : E => t • x) (t • (1 : E →L[ℝ] E)) x := by
    exact (hasFDerivAt_id x).const_smul t
  have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
    hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
    h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) (t • x) :=
    ((h1 _ (Set.mem_univ _)).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      Filter.univ_mem
  exact HasFDerivAt.comp x (g := fderiv ℝ (fderiv ℝ g))
    (g' := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) (f := fun x : E => t • x)
    (f' := t • (1 : E →L[ℝ] E)) (hg := hd.hasFDerivAt) (hf := hsmul)

omit [FiniteDimensional ℝ E] in
theorem portPrivate_846ebadb_continuousOn_morseTaylorDerivIntegrand (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x : E) :
    ContinuousOn (fun t : ℝ => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E)))) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) (t • x) :=
      (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt).continuousWithinAt
  have hcompCLM : ContinuousOn (fun t : ℝ => (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E))) Set.univ := by
    have hL : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) Set.univ := hcomp
    have hM : ContinuousOn (fun t : ℝ => t • (1 : E →L[ℝ] E)) Set.univ :=
      continuous_id.smul continuous_const |>.continuousOn
    intro t ht
    exact ContinuousOn.clm_comp hL hM t ht
  exact (continuous_const.sub continuous_id).continuousOn.smul hcompCLM

theorem hasFDerivAt_morseTaylorBilin (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x₀ : E) :
    HasFDerivAt (fun x : E => morseTaylorBilin g x)
      (∫ t in (0 : ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x₀)).comp
        (t • (1 : E →L[ℝ] E)))) x₀ := by
  let F : E → ℝ → E →L[ℝ] (E →L[ℝ] ℝ) :=
    fun x t => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)
  let F' : E → ℝ → E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    fun x t => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E)))
  let s : Set E := Metric.ball x₀ 1
  have hs : s ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
  have hFcont : ∀ x : E, Continuous (F x) := by
    intro x
    have hg2 : ContDiff ℝ 2 g :=
      hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))
    exact continuousOn_univ.mp (portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg2 x)
  have hF'_cont : ∀ x : E, Continuous (F' x) := by
    intro x
    exact continuousOn_univ.mp (portPrivate_846ebadb_continuousOn_morseTaylorDerivIntegrand g hg x)
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Ι (0 : ℝ) 1)) := by
    exact Eventually.of_forall fun x => (hFcont x).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hF'_cont x₀).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F x₀) volume (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g (by
        exact hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))) x₀).mono
        (by intro t ht; exact Set.mem_univ t))
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  let R : ℝ := ‖x₀‖ + 2
  have hC : ∃ C : ℝ, ∀ y ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y‖ ≤ C :=
    IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (x := (0 : E)) (r := R))
      (h0.continuousOn.mono (by intro y hy; exact Set.mem_univ y))
  rcases hC with ⟨C, hCbound⟩
  have hbound_aux : ∀ x ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' x t‖ ≤ C := by
    intro x hx t ht
    have htx_mem : t • x ∈ Metric.closedBall (0 : E) R := by
      have hxnorm : ‖x‖ < ‖x₀‖ + 1 := by
        have hdist : dist x x₀ < 1 := (Metric.mem_ball.mp hx)
        calc
          ‖x‖ = dist x 0 := by rw [dist_zero_right]
          _ ≤ dist x x₀ + dist x₀ 0 := dist_triangle x x₀ 0
          _ = ‖x - x₀‖ + ‖x₀‖ := by rw [dist_eq_norm, dist_zero_right]
          _ < ‖x₀‖ + 1 := by
            have hnorm : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hdist
            linarith
      have htxnorm : ‖t • x‖ ≤ ‖x‖ := by
        calc
          ‖t • x‖ = |t| * ‖x‖ := norm_smul _ _
          _ ≤ 1 * ‖x‖ := by
            gcongr
            exact abs_le.mpr ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1, ht.2⟩
          _ = ‖x‖ := by rw [one_mul]
      exact Metric.mem_closedBall.mpr (by
        calc
          dist (t • x) 0 = ‖t • x‖ := by rw [dist_zero_right]
          _ ≤ ‖x‖ := htxnorm
          _ ≤ ‖x₀‖ + 2 := by linarith
          _ = R := rfl)
    have hnormcomp : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| := by
      calc
        ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))‖ ≤
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * ‖t • (1 : E →L[ℝ] E)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * (‖t‖ * ‖(1 : E →L[ℝ] E)‖) := by
          rw [norm_smul]
        _ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * (|t| * ‖(1 : E →L[ℝ] E)‖) := by
          rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| := by
          have hnorm1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          have hinner : |t| * ‖(1 : E →L[ℝ] E)‖ ≤ |t| := by
            calc
              |t| * ‖(1 : E →L[ℝ] E)‖ ≤ |t| * 1 :=
                mul_le_mul_of_nonneg_left hnorm1 (abs_nonneg _)
              _ = |t| := by rw [mul_one]
          exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    calc
      ‖F' x t‖ = ‖(1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E)))‖ := rfl
      _ = ‖(1 - t)‖ * ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E))‖ := norm_smul _ _
      _ = |1 - t| * ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E))‖ := by rw [Real.norm_eq_abs]
      _ ≤ |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t|) := by
        exact mul_le_mul_of_nonneg_left hnormcomp (abs_nonneg _)
      _ ≤ 1 * (C * 1) := by
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCbound (0 : E) (by
          suffices 0 ≤ R from Metric.mem_closedBall.mpr (by simpa using this)
          positivity))
        have hleD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ ≤ C := hCbound (t • x) htx_mem
        have hle1 : |t| ≤ 1 := abs_le.mpr ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1, ht.2⟩
        have hleDmul : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| ≤ C * 1 :=
          mul_le_mul hleD hle1 (abs_nonneg t) hC0
        have hle0 : |1 - t| ≤ 1 := abs_le.mpr
          ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (sub_nonneg.mpr ht.2), sub_le_self 1 ht.1⟩
        calc
          |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t|) ≤
              |1 - t| * (C * 1) :=
            mul_le_mul le_rfl hleDmul (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (abs_nonneg _)
          _ ≤ 1 * (C * 1) := mul_le_mul hle0 le_rfl (by simpa using hC0) (zero_le_one)
      _ = C := by ring
  have h_bound : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, ‖F' x t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro x hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have : t ∈ Ι (0 : ℝ) 1 := ht
      exact ⟨by simpa using (le_of_lt this.1), by simpa using this.2⟩
    exact hbound_aux x hx t htIcc
  have h_diff : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, HasFDerivAt (F · t) (F' x t) x := by
    exact Eventually.of_forall (by
      intro t x hx
      have hderiv : HasFDerivAt (fun x : E => fderiv ℝ (fderiv ℝ g) (t • x))
          ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))) x :=
        portPrivate_846ebadb_hasFDerivAt_third_morse g hg x t
      change HasFDerivAt
        (fun y : E => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • y)) (F' x t) x
      have hscaled := hderiv.const_smul (1 - t)
      change HasFDerivAt
        ((1 - t) • fun y : E => fderiv ℝ (fderiv ℝ g) (t • y)) (F' x t) x at hscaled
      exact hscaled)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (a := (0 : ℝ)) (b := 1)
    (s := s) (x₀ := x₀) (F := F) (F' := F') (bound := fun _ : ℝ => C) hs hF_meas hF_int hF'_meas
    h_bound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) 1) h_diff
  simpa [morseTaylorBilin, F, F'] using hmain

noncomputable def morseTaylorBilinDeriv (g : E → ℝ) (x : E) :
    E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ∫ t in (0 : ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
    (t • (1 : E →L[ℝ] E)))

theorem continuous_morseTaylorBilinDeriv (g : E → ℝ) (hg : ContDiff ℝ 3 g) :
    Continuous (morseTaylorBilinDeriv g) := by
  let F : E → ℝ → E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    fun x t => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E)))
  have hg3 : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ :=
      h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    exact continuousOn_univ.mp h0.continuousOn
  have hpath : Continuous (fun p : E × ℝ => p.2 • p.1) :=
    continuous_snd.smul continuous_fst
  have hhess : Continuous (fun p : E × ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (p.2 • p.1)) :=
    hg3.comp hpath
  have hsmul1 : Continuous (fun p : E × ℝ => p.2 • (1 : E →L[ℝ] E)) :=
    continuous_snd.smul continuous_const
  have hcomp : Continuous (fun p : E × ℝ =>
      (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (p.2 • p.1)).comp (p.2 • (1 : E →L[ℝ] E))) := by
    let C : (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) →L[ℝ] (E →L[ℝ] E) →L[ℝ]
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
      ContinuousLinearMap.compL ℝ E E (E →L[ℝ] (E →L[ℝ] ℝ))
    have hC : Continuous (fun p : (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) × (E →L[ℝ] E) =>
        C p.1 p.2) := by
      exact (ContinuousLinearMap.continuous₂ C)
    exact hC.comp (hhess.prodMk hsmul1)
  have hscalar : Continuous (fun p : E × ℝ => 1 - p.2) :=
    continuous_const.sub continuous_snd
  have hF : Continuous F.uncurry := by
    dsimp [F]
    exact hscalar.smul hcomp
  have hconv : (fun x : E => ∫ t in (0 : ℝ)..1, F x t) =
      fun x : E => ∫ t in Set.Icc (0 : ℝ) 1, F x t := by
    funext x
    calc
      ∫ t in (0 : ℝ)..1, F x t = ∫ t in Set.Ioc (0 : ℝ) 1, F x t :=
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)
      _ = ∫ t in Set.Icc (0 : ℝ) 1, F x t := by
        rw [integral_Icc_eq_integral_Ioc' (by simp)]
  change Continuous (fun x : E => ∫ t in (0 : ℝ)..1, F x t)
  rw [hconv]
  exact continuous_parametric_integral_of_continuous (X := E) (Y := ℝ)
    (E := E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) hF (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))

theorem contDiffOn_morseTaylorBilin (g : E → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiffOn ℝ 1 (fun x : E => morseTaylorBilin g x) Set.univ := by
  have hdiff : DifferentiableOn ℝ (fun x : E => morseTaylorBilin g x) Set.univ := by
    intro x hx
    exact (hasFDerivAt_morseTaylorBilin g hg x).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn (fun y : E => fderiv ℝ (fun x : E => morseTaylorBilin g x) y) Set.univ := by
    have hdeq : ∀ y : E, fderiv ℝ (fun x : E => morseTaylorBilin g x) y = morseTaylorBilinDeriv g y := by
      intro y
      exact (hasFDerivAt_morseTaylorBilin g hg y).fderiv
    intro y hy
    convert (continuous_morseTaylorBilinDeriv g hg).continuousAt.continuousWithinAt using 1
    funext z
    exact hdeq z
  refine contDiffOn_succ_of_fderivWithin (n := 0) (s := Set.univ) hdiff ?_ ?_
  · intro h
    exact False.elim ((by decide : (0 : WithTop ℕ∞) ≠ ⊤) h)
  · rw [contDiffOn_zero]
    intro y hy
    simpa [fderivWithin_univ] using hcont y hy

theorem contDiffAt_morseTaylorBilin (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x₀ : E) :
    ContDiffAt ℝ 1 (fun x : E => morseTaylorBilin g x) x₀ := by
  exact (contDiffOn_morseTaylorBilin g hg).contDiffAt Filter.univ_mem

noncomputable def morseSegmentPath (p : E × E) (t : ℝ) : E :=
  p.1 + t • (p.2 - p.1)

noncomputable def morseSegmentDeriv (t : ℝ) : (E × E) →L[ℝ] E :=
  (1 - t) • ContinuousLinearMap.fst ℝ E E + t • ContinuousLinearMap.snd ℝ E E

omit [FiniteDimensional ℝ E] in
theorem morseSegmentPath_apply_deriv (p : E × E) (t : ℝ) :
    morseSegmentPath p t = morseSegmentDeriv t p := by
  change p.1 + t • (p.2 - p.1) = (1 - t) • p.1 + t • p.2
  rw [smul_sub, sub_smul, one_smul]
  abel

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_morseSegmentPath (p : E × E) (t : ℝ) :
    HasFDerivAt (fun q : E × E => morseSegmentPath q t) (morseSegmentDeriv t) p := by
  have hfun : (fun q : E × E => morseSegmentPath q t) = (morseSegmentDeriv t) := by
    funext q
    exact morseSegmentPath_apply_deriv q t
  have hder : HasFDerivAt (fun q : E × E => morseSegmentDeriv t q) (morseSegmentDeriv t) p := by
    fun_prop
  simpa [hfun] using hder

omit [FiniteDimensional ℝ E] in
theorem norm_morseSegmentDeriv_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(morseSegmentDeriv t : (E × E) →L[ℝ] E)‖ ≤ 2 := by
  have h1 : ‖(1 - t) • (ContinuousLinearMap.fst ℝ E E : (E × E) →L[ℝ] E)‖ ≤ 1 - t := by
    rw [norm_smul]
    have hfst : ‖(ContinuousLinearMap.fst ℝ E E : (E × E) →L[ℝ] E)‖ ≤ 1 :=
      ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := E) (F := E)
    calc
      ‖1 - t‖ * ‖ContinuousLinearMap.fst ℝ E E‖ ≤ ‖1 - t‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hfst (norm_nonneg _)
      _ = 1 - t := by
        rw [mul_one, Real.norm_eq_abs, abs_of_nonneg]
        linarith [ht.2]
  have h2 : ‖t • (ContinuousLinearMap.snd ℝ E E : (E × E) →L[ℝ] E)‖ ≤ t := by
    rw [norm_smul]
    have hsnd : ‖(ContinuousLinearMap.snd ℝ E E : (E × E) →L[ℝ] E)‖ ≤ 1 :=
      ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := E) (F := E)
    calc
      ‖t‖ * ‖ContinuousLinearMap.snd ℝ E E‖ ≤ ‖t‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hsnd (norm_nonneg _)
      _ = t := by
        rw [mul_one, Real.norm_eq_abs, abs_of_nonneg]
        exact ht.1
  calc
    ‖(morseSegmentDeriv t : (E × E) →L[ℝ] E)‖ ≤ ‖(1 - t) • (ContinuousLinearMap.fst ℝ E E : (E × E) →L[ℝ] E)‖ +
        ‖t • (ContinuousLinearMap.snd ℝ E E : (E × E) →L[ℝ] E)‖ := by
      dsimp [morseSegmentDeriv]
      exact norm_add_le _ _
    _ ≤ (1 - t) + t := add_le_add h1 h2
    _ ≤ 2 := by linarith

omit [FiniteDimensional ℝ E] in
theorem norm_morseSegmentPath_le {p₀ : E × E} {p : E × E} (hp : p ∈ Metric.ball p₀ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖morseSegmentPath p t‖ ≤ ‖p₀.1‖ + ‖p₀.2 - p₀.1‖ + 3 := by
  have hdist : ‖p - p₀‖ < 1 := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hp)
  have h₁ : ‖p.1 - p₀.1‖ ≤ ‖p - p₀‖ := by
    calc
      ‖p.1 - p₀.1‖ = ‖ContinuousLinearMap.fst ℝ E E (p - p₀)‖ := by
        simp [ContinuousLinearMap.fst]
      _ ≤ ‖ContinuousLinearMap.fst ℝ E E‖ * ‖p - p₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖p - p₀‖ := by
        calc
          ‖ContinuousLinearMap.fst ℝ E E‖ * ‖p - p₀‖ ≤ 1 * ‖p - p₀‖ := by
            exact mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := E) (F := E)) (norm_nonneg _)
          _ = ‖p - p₀‖ := by rw [one_mul]
  have h₂ : ‖(p.2 - p.1) - (p₀.2 - p₀.1)‖ ≤ ‖p - p₀‖ + ‖p - p₀‖ := by
    calc
      ‖(p.2 - p.1) - (p₀.2 - p₀.1)‖ = ‖(p.2 - p₀.2) - (p.1 - p₀.1)‖ := by
        have hsub : (p.2 - p.1) - (p₀.2 - p₀.1) = (p.2 - p₀.2) - (p.1 - p₀.1) := by abel
        rw [hsub]
      _ ≤ ‖p.2 - p₀.2‖ + ‖p.1 - p₀.1‖ := by
        rw [sub_eq_add_neg]
        calc
          ‖(p.2 - p₀.2) + -(p.1 - p₀.1)‖ ≤ ‖p.2 - p₀.2‖ + ‖-(p.1 - p₀.1)‖ := norm_add_le _ _
          _ = ‖p.2 - p₀.2‖ + ‖p.1 - p₀.1‖ := by
            rw [norm_neg]
      _ ≤ ‖p - p₀‖ + ‖p - p₀‖ := by
        exact add_le_add (by
          calc
            ‖p.2 - p₀.2‖ = ‖ContinuousLinearMap.snd ℝ E E (p - p₀)‖ := by
              simp [ContinuousLinearMap.snd]
            _ ≤ ‖ContinuousLinearMap.snd ℝ E E‖ * ‖p - p₀‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖p - p₀‖ := by
              calc
                ‖ContinuousLinearMap.snd ℝ E E‖ * ‖p - p₀‖ ≤ 1 * ‖p - p₀‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := E) (F := E)) (norm_nonneg _)
                _ = ‖p - p₀‖ := by rw [one_mul]) (by
          calc
            ‖p.1 - p₀.1‖ = ‖ContinuousLinearMap.fst ℝ E E (p - p₀)‖ := by
              simp [ContinuousLinearMap.fst]
            _ ≤ ‖ContinuousLinearMap.fst ℝ E E‖ * ‖p - p₀‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖p - p₀‖ := by
              calc
                ‖ContinuousLinearMap.fst ℝ E E‖ * ‖p - p₀‖ ≤ 1 * ‖p - p₀‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := E) (F := E)) (norm_nonneg _)
                _ = ‖p - p₀‖ := by rw [one_mul])
  have hnorm : ‖morseSegmentPath p t‖ ≤ ‖p.1‖ + ‖p.2 - p.1‖ := by
    calc
      ‖p.1 + t • (p.2 - p.1)‖ ≤ ‖p.1‖ + ‖t • (p.2 - p.1)‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + ‖p.2 - p.1‖ := by
        have ht' : ‖t • (p.2 - p.1)‖ ≤ ‖p.2 - p.1‖ := by
          calc
            ‖t • (p.2 - p.1)‖ = |t| * ‖p.2 - p.1‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ 1 * ‖p.2 - p.1‖ := by
              have ht' : |t| ≤ 1 := by
                rw [abs_of_nonneg ht.1]
                exact ht.2
              exact mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
            _ = ‖p.2 - p.1‖ := by rw [one_mul]
        linarith
  calc
    ‖morseSegmentPath p t‖ ≤ ‖p.1‖ + ‖p.2 - p.1‖ := hnorm
    _ ≤ (‖p₀.1‖ + 1) + (‖p₀.2 - p₀.1‖ + 2) := by
      have hb1 : ‖p.1‖ ≤ ‖p₀.1‖ + 1 := by
        calc
          ‖p.1‖ = ‖p₀.1 + (p.1 - p₀.1)‖ := by rw [add_sub_cancel]
          _ ≤ ‖p₀.1‖ + ‖p.1 - p₀.1‖ := norm_add_le _ _
          _ ≤ ‖p₀.1‖ + 1 := by linarith
      have hb2 : ‖p.2 - p.1‖ ≤ ‖p₀.2 - p₀.1‖ + 2 := by
        calc
          ‖p.2 - p.1‖ = ‖(p₀.2 - p₀.1) + ((p.2 - p.1) - (p₀.2 - p₀.1))‖ := by
            rw [add_sub_cancel]
          _ ≤ ‖p₀.2 - p₀.1‖ + ‖(p.2 - p.1) - (p₀.2 - p₀.1)‖ := norm_add_le _ _
          _ ≤ ‖p₀.2 - p₀.1‖ + 2 := by linarith
      linarith [hb1, hb2]
    _ = ‖p₀.1‖ + ‖p₀.2 - p₀.1‖ + 3 := by ring

omit [FiniteDimensional ℝ E] in
theorem portPrivate_846ebadb_continuousOn_morseTaylorAtIntegrand (g : E → ℝ) (hg : ContDiff ℝ 2 g) (p : E × E) :
    ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath p t)) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ g)) Set.univ := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ g)) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => morseSegmentPath p t) := by
    dsimp [morseSegmentPath]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (morseSegmentPath p t)) Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t) :=
      (hcont (morseSegmentPath p t) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => morseSegmentPath p t) (x := t) hcAt
      hsmul.continuousAt).continuousWithinAt
  exact (continuous_const.sub continuous_id).continuousOn.smul hcomp

omit [FiniteDimensional ℝ E] in
theorem portPrivate_846ebadb_continuousOn_morseTaylorAtDerivIntegrand (g : E → ℝ) (hg : ContDiff ℝ 3 g)
    (p : E × E) :
    ContinuousOn (fun t : ℝ => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
      (morseSegmentDeriv t))) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => morseSegmentPath p t) := by
    dsimp [morseSegmentPath]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t))
      Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) (morseSegmentPath p t) :=
      (hcont (morseSegmentPath p t) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => morseSegmentPath p t) (x := t) hcAt
      hsmul.continuousAt).continuousWithinAt
  have hcompCLM : ContinuousOn (fun t : ℝ => (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
      (morseSegmentDeriv t)) Set.univ := by
    have hL : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)) Set.univ := hcomp
    have hM : Continuous (fun t : ℝ => (morseSegmentDeriv t : (E × E) →L[ℝ] E)) := by
      dsimp [morseSegmentDeriv]
      exact ((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)
    intro t ht
    exact ContinuousOn.clm_comp hL hM.continuousOn t ht
  exact (continuous_const.sub continuous_id).continuousOn.smul hcompCLM

theorem hasFDerivAt_morseTaylorBilinAt (g : E → ℝ) (hg : ContDiff ℝ 3 g) (c₀ x₀ : E) :
    HasFDerivAt (fun p : E × E => morseTaylorBilinAt g p.1 p.2)
      (∫ t in (0 : ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g))
        (c₀ + t • (x₀ - c₀))).comp (morseSegmentDeriv t))) (c₀, x₀) := by
  let F : (E × E) → ℝ → E →L[ℝ] (E →L[ℝ] ℝ) :=
    fun p t => (1 - t) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath p t)
  let F' : (E × E) → ℝ → (E × E) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    fun p t => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
      (morseSegmentDeriv t))
  let p₀ : E × E := (c₀, x₀)
  let s : Set (E × E) := Metric.ball p₀ 1
  have hs : s ∈ nhds p₀ := Metric.ball_mem_nhds p₀ (by norm_num)
  have hFcont : ∀ p : E × E, Continuous (F p) := by
    intro p
    have hg2 : ContDiff ℝ 2 g :=
      hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))
    exact continuousOn_univ.mp (portPrivate_846ebadb_continuousOn_morseTaylorAtIntegrand g hg2 p)
  have hF'_cont : ∀ p : E × E, Continuous (F' p) := by
    intro p
    exact continuousOn_univ.mp (portPrivate_846ebadb_continuousOn_morseTaylorAtDerivIntegrand g hg p)
  have hF_meas : ∀ᶠ p in nhds p₀,
      AEStronglyMeasurable (F p) (volume.restrict (Ι (0 : ℝ) 1)) := by
    exact Eventually.of_forall fun p => (hFcont p).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' p₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hF'_cont p₀).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F p₀) volume (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((portPrivate_846ebadb_continuousOn_morseTaylorAtIntegrand g (by
        exact hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))) p₀).mono
        (by intro t ht; exact Set.mem_univ t))
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  let R : ℝ := ‖c₀‖ + ‖x₀ - c₀‖ + 3
  have hC : ∃ C : ℝ, ∀ y ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y‖ ≤ C :=
    IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (x := (0 : E)) (r := R))
      (h0.continuousOn.mono (by intro y hy; exact Set.mem_univ y))
  rcases hC with ⟨C, hCbound⟩
  have hbound_aux : ∀ p ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' p t‖ ≤ 2 * C := by
    intro p hp t ht
    have htx_mem : morseSegmentPath p t ∈ Metric.closedBall (0 : E) R := by
      have hle := norm_morseSegmentPath_le hp t ht
      exact Metric.mem_closedBall.mpr (by
        calc
          dist (morseSegmentPath p t) 0 = ‖morseSegmentPath p t‖ := by rw [dist_zero_right]
          _ ≤ R := by
            dsimp [R]
            linarith [hle])
    have hnormcomp : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp (morseSegmentDeriv t)‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2 := by
      calc
        ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp (morseSegmentDeriv t)‖ ≤
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * ‖morseSegmentDeriv t‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2 := by
          exact mul_le_mul_of_nonneg_left (norm_morseSegmentDeriv_le t ht) (norm_nonneg _)
    calc
      ‖F' p t‖ = ‖(1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
          (morseSegmentDeriv t))‖ := rfl
      _ = |1 - t| * ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
          (morseSegmentDeriv t)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2) := by
        exact mul_le_mul_of_nonneg_left hnormcomp (abs_nonneg _)
      _ ≤ 1 * (C * 2) := by
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCbound (0 : E) (by
          suffices 0 ≤ R from Metric.mem_closedBall.mpr (by simpa using this)
          positivity))
        have hleD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ ≤ C :=
          hCbound (morseSegmentPath p t) htx_mem
        have hle1 : |1 - t| ≤ 1 := abs_le.mpr
          ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (sub_nonneg.mpr ht.2), sub_le_self 1 ht.1⟩
        have hleDmul : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2 ≤ C * 2 :=
          mul_le_mul hleD le_rfl (by norm_num) hC0
        calc
          |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2) ≤
              1 * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)‖ * 2) :=
            mul_le_mul hle1 le_rfl (mul_nonneg (norm_nonneg _) (by norm_num)) zero_le_one
          _ ≤ 1 * (C * 2) := mul_le_mul le_rfl hleDmul (by norm_num) zero_le_one
      _ = 2 * C := by ring
  have h_bound : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ p ∈ s, ‖F' p t‖ ≤ (fun _ : ℝ => 2 * C) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro p hp
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have : t ∈ Ι (0 : ℝ) 1 := ht
      exact ⟨by simpa using (le_of_lt this.1), by simpa using this.2⟩
    exact hbound_aux p hp t htIcc
  have h_diff : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ p ∈ s, HasFDerivAt (F · t) (F' p t) p := by
    exact Eventually.of_forall (by
      intro t p hp
      have hderiv : HasFDerivAt (fun q : E × E => fderiv ℝ (fderiv ℝ g) (morseSegmentPath q t))
          ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp (morseSegmentDeriv t)) p := by
        have hg' : HasFDerivAt (fderiv ℝ (fderiv ℝ g))
            (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)) (morseSegmentPath p t) := by
          have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
            (by
              have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
                hg.contDiffOn.fderiv_of_isOpen isOpen_univ
                  (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
              exact h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞)))
          have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t) :=
            ((h1 (morseSegmentPath p t) (Set.mem_univ _)).differentiableWithinAt
              (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
          exact hd.hasFDerivAt
        exact HasFDerivAt.comp (x := p) (g := fderiv ℝ (fderiv ℝ g))
          (g' := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t))
          (f := fun q : E × E => morseSegmentPath q t) (f' := morseSegmentDeriv t)
          (hg := hg') (hf := hasFDerivAt_morseSegmentPath p t)
      have hsmul : HasFDerivAt (fun q : E × E => (1 - t) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath q t))
          ((1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp (morseSegmentDeriv t))) p :=
        hderiv.const_smul (1 - t)
      simpa [F, F', Function.comp_def] using hsmul)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (a := (0 : ℝ)) (b := 1)
    (s := s) (x₀ := p₀) (F := F) (F' := F') (bound := fun _ : ℝ => 2 * C) hs hF_meas hF_int hF'_meas
    h_bound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * C) volume (0 : ℝ) 1) h_diff
  simpa [morseTaylorBilinAt, F, F', p₀, morseSegmentPath] using hmain

noncomputable def morseTaylorBilinAtDeriv (g : E → ℝ) (c x : E) :
    (E × E) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ∫ t in (0 : ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g))
    (c + t • (x - c))).comp (morseSegmentDeriv t))

theorem continuous_morseTaylorBilinAtDeriv (g : E → ℝ) (hg : ContDiff ℝ 3 g) :
    Continuous (fun p : E × E => morseTaylorBilinAtDeriv g p.1 p.2) := by
  let G : (E × E) → ℝ → (E × E) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    fun p t => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath p t)).comp
      (morseSegmentDeriv t))
  have hg3 : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ :=
      h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    exact continuousOn_univ.mp h0.continuousOn
  have hpath : Continuous (fun q : (E × E) × ℝ => morseSegmentPath q.1 q.2) := by
    have h1 : Continuous (fun q : (E × E) × ℝ => q.1.1) := by
      exact ((continuous_fst : Continuous (fun r : E × E => r.1)).comp continuous_fst)
    have h2 : Continuous (fun q : (E × E) × ℝ => q.1.2) := by
      exact ((continuous_snd : Continuous (fun r : E × E => r.2)).comp continuous_fst)
    have h3 : Continuous (fun q : (E × E) × ℝ => q.2) := continuous_snd
    dsimp [morseSegmentPath]
    exact h1.add (h3.smul (h2.sub h1))
  have hhess : Continuous (fun q : (E × E) × ℝ =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath q.1 q.2)) :=
    hg3.comp hpath
  have hsegDeriv : Continuous (fun q : (E × E) × ℝ =>
      (morseSegmentDeriv q.2 : (E × E) →L[ℝ] E)) := by
    dsimp [morseSegmentDeriv]
    exact ((continuous_const.sub continuous_snd).smul continuous_const).add
      (continuous_snd.smul continuous_const)
  have hcomp : Continuous (fun q : (E × E) × ℝ =>
      (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath q.1 q.2)).comp
        (morseSegmentDeriv q.2 : (E × E) →L[ℝ] E)) := by
    let C : (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) →L[ℝ] ((E × E) →L[ℝ] E) →L[ℝ]
        ((E × E) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
      ContinuousLinearMap.compL ℝ (E × E) E (E →L[ℝ] (E →L[ℝ] ℝ))
    have hC : Continuous (fun q : (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) × ((E × E) →L[ℝ] E) =>
        C q.1 q.2) := by
      exact (ContinuousLinearMap.continuous₂ C)
    change Continuous (fun q : (E × E) × ℝ =>
      C (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (morseSegmentPath q.1 q.2))
        (morseSegmentDeriv q.2))
    exact hC.comp (hhess.prodMk hsegDeriv)
  have hscalar : Continuous (fun q : (E × E) × ℝ => 1 - q.2) :=
    continuous_const.sub continuous_snd
  have hG : Continuous G.uncurry := by
    dsimp [G]
    exact hscalar.smul hcomp
  have hconv : (fun p : E × E => ∫ t in (0 : ℝ)..1, G p t) =
      fun p : E × E => ∫ t in Set.Icc (0 : ℝ) 1, G p t := by
    funext p
    calc
      ∫ t in (0 : ℝ)..1, G p t = ∫ t in Set.Ioc (0 : ℝ) 1, G p t :=
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)
      _ = ∫ t in Set.Icc (0 : ℝ) 1, G p t := by
        rw [integral_Icc_eq_integral_Ioc' (by simp)]
  have hdef : (fun p : E × E => morseTaylorBilinAtDeriv g p.1 p.2) =
      fun p : E × E => ∫ t in (0 : ℝ)..1, G p t := by
    funext p
    simp [morseTaylorBilinAtDeriv, G, morseSegmentPath]
  rw [hdef]
  rw [hconv]
  exact continuous_parametric_integral_of_continuous (X := E × E) (Y := ℝ)
    (E := (E × E) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) hG (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))

theorem contDiffOn_morseTaylorBilinAt (g : E → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiffOn ℝ 1 (fun p : E × E => morseTaylorBilinAt g p.1 p.2) Set.univ := by
  have hdiff : DifferentiableOn ℝ (fun p : E × E => morseTaylorBilinAt g p.1 p.2) Set.univ := by
    intro p hp
    exact (hasFDerivAt_morseTaylorBilinAt g hg p.1 p.2).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn (fun p : E × E =>
      fderiv ℝ (fun q : E × E => morseTaylorBilinAt g q.1 q.2) p) Set.univ := by
    have hdeq : ∀ p : E × E, fderiv ℝ (fun q : E × E => morseTaylorBilinAt g q.1 q.2) p =
        morseTaylorBilinAtDeriv g p.1 p.2 := by
      intro p
      exact (hasFDerivAt_morseTaylorBilinAt g hg p.1 p.2).fderiv
    intro p hp
    convert (continuous_morseTaylorBilinAtDeriv g hg).continuousAt.continuousWithinAt using 1
    funext q
    exact hdeq q
  refine contDiffOn_succ_of_fderivWithin (n := 0) (s := Set.univ) hdiff ?_ ?_
  · intro h
    exact False.elim ((by decide : (0 : WithTop ℕ∞) ≠ ⊤) h)
  · rw [contDiffOn_zero]
    intro p hp
    simpa [fderivWithin_univ] using hcont p hp

theorem contDiffAt_morseTaylorBilinAt (g : E → ℝ) (hg : ContDiff ℝ 3 g) (c₀ x₀ : E) :
    ContDiffAt ℝ 1 (fun p : E × E => morseTaylorBilinAt g p.1 p.2) (c₀, x₀) := by
  exact (contDiffOn_morseTaylorBilinAt g hg).contDiffAt Filter.univ_mem

theorem contDiffOn_morseTaylorBilinAt_smooth (g : E → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × E => morseTaylorBilinAt g p.1 p.2) Set.univ := by
  have hfd2 : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ g)) Set.univ := by
    have h1 : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)
    exact h1.fderiv_of_isOpen isOpen_univ (by simp)
  have hpath : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (E × E) × ℝ => morseSegmentPath q.1 q.2) Set.univ := by
    unfold morseSegmentPath
    fun_prop
  have hH : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (E × E) × ℝ => (1 - q.2) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath q.1 q.2)) Set.univ := by
    have hcomp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (E × E) × ℝ => fderiv ℝ (fderiv ℝ g) (morseSegmentPath q.1 q.2)) Set.univ :=
      hfd2.comp hpath (by intro q hq; trivial)
    have hscalar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (E × E) × ℝ => 1 - q.2) Set.univ := by
      fun_prop
    exact ContDiffOn.smul hscalar hcomp
  have hmain := DifferentialGeometry.Analysis.Calculus.contDiffOn_paramIntervalIntegral
    (f := fun p : E × E => fun t : ℝ =>
    (1 - t) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath p t)) hH
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : E × E => ∫ t in (0 : ℝ)..1,
      (1 - t) • fderiv ℝ (fderiv ℝ g) (morseSegmentPath p t)) Set.univ
  exact hmain

theorem contDiffAt_morseTaylorBilinAt_smooth (g : E → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) (c₀ x₀ : E) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × E => morseTaylorBilinAt g p.1 p.2) (c₀, x₀) := by
  exact (contDiffOn_morseTaylorBilinAt_smooth g hg).contDiffAt Filter.univ_mem

omit [FiniteDimensional ℝ E] in
theorem morseTaylorBilin_symm (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x u v : E) :
    (morseTaylorBilin g x) u v = (morseTaylorBilin g x) v u := by
  have hsym : ∀ y : E, IsSymmSndFDerivAt ℝ g y := by
    intro y
    exact (hg.contDiffAt (x := y)).isSymmSndFDerivAt
      (by norm_num [minSmoothness] : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  have hinner : ∀ t : ℝ, (fderiv ℝ (fderiv ℝ g) (t • x)) u v = (fderiv ℝ (fderiv ℝ g) (t • x)) v u := by
    intro t
    exact (hsym (t • x)) u v
  have hBint : IntervalIntegrable (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) volume
      (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg x).mono (by intro t ht; exact Set.mem_univ t))
  have hBv1 : IntervalIntegrable (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) u) volume
      (0 : ℝ) 1 := by
    have hc : ContinuousOn (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) u) Set.univ := by
      have hMain : ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ :=
        portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg x
      have hc' : ContinuousOn (fun _ : ℝ => u) Set.univ := continuous_const.continuousOn
      exact ContinuousOn.clm_apply hMain hc'
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (hc.mono (by intro t ht; exact Set.mem_univ t))
  calc
    (morseTaylorBilin g x) u v = (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) u v := by
      rfl
    _ = ∫ t in (0 : ℝ)..1, (((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) u) v := by
      rw [ContinuousLinearMap.intervalIntegral_apply hBint u]
      rw [ContinuousLinearMap.intervalIntegral_apply hBv1 v]
    _ = ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) u v) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [smul_eq_mul]
    _ = ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) v u) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (fun z : ℝ => (1 - t) * z) (hinner t)
    _ = ∫ t in (0 : ℝ)..1, (((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) v) u := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [smul_eq_mul]
    _ = (morseTaylorBilin g x) v u := by
      have hBv1' : IntervalIntegrable (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) v) volume
          (0 : ℝ) 1 := by
        have hc : ContinuousOn (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) v) Set.univ := by
          have hMain : ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ :=
            portPrivate_846ebadb_continuousOn_morseTaylorIntegrand g hg x
          have hc' : ContinuousOn (fun _ : ℝ => v) Set.univ := continuous_const.continuousOn
          exact ContinuousOn.clm_apply hMain hc'
        exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
          (hc.mono (by intro t ht; exact Set.mem_univ t))
      rw [← ContinuousLinearMap.intervalIntegral_apply hBv1' u]
      rw [← ContinuousLinearMap.intervalIntegral_apply hBint v]
      rfl

end DifferentialGeometry.Topology.Morse
