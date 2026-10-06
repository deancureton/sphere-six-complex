module

public import DifferentialGeometry.Topology.Morse.Defs
public import DifferentialGeometry.Topology.Morse.NormalForm.Local
public import DifferentialGeometry.Topology.Attachment.Union
public import DifferentialGeometry.Topology.Handle.Defs
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.ExponentialBounds
public import DifferentialGeometry.Analysis.Calculus.Taylor
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace DifferentialGeometry.Topology.Morse

open Filter
open DifferentialGeometry.Topology.Handle
open scoped _root_.Topology


noncomputable section

namespace CellAttachment

namespace Real

open Set Function Polynomial

theorem smoothTransition_deriv_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    deriv Real.smoothTransition x =
      (expNegInvGlue x * expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
  have hE : ∀ x : ℝ, HasDerivAt expNegInvGlue (expNegInvGlue x * x⁻¹ ^ 2) x := by
    intro y
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (p := (1 : ℝ[X])) y
    simpa [pow_two, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_pow,
      derivative_one, mul_comm, mul_left_comm, mul_assoc] using h
  have hnum : HasDerivAt (fun y : ℝ => expNegInvGlue y) (expNegInvGlue x * x⁻¹ ^ 2) x := hE x
  have h2 : HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y)) (-(expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2)) x := by
    have h3 : HasDerivAt (fun y : ℝ => expNegInvGlue y) (expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2) (1 - x) := hE (1 - x)
    have hneg : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := by
      exact (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (hasDerivAt_id x)).congr_deriv (by ring)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
    exact (((h3.comp x hneg).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl))
  have hden : HasDerivAt (fun y : ℝ => expNegInvGlue y + expNegInvGlue (1 - y))
      (expNegInvGlue x * x⁻¹ ^ 2 - expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2) x := by
    exact (hnum.add h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hden_ne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 := by
    have hpos1 : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
    have hpos2 : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
    nlinarith
  have hτ' : HasDerivAt (fun y : ℝ => expNegInvGlue y / (expNegInvGlue y + expNegInvGlue (1 - y)))
      (((expNegInvGlue x * x⁻¹ ^ 2) * (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x * (expNegInvGlue x * x⁻¹ ^ 2 - expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2)) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
    exact (hnum.div hden hden_ne).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hdef : (fun y : ℝ => expNegInvGlue y / (expNegInvGlue y + expNegInvGlue (1 - y))) = Real.smoothTransition := by
    funext y
    rfl
  rw [← hdef]
  rw [hτ'.deriv]
  have hnum2 : expNegInvGlue x * x⁻¹ ^ 2 * (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x * (expNegInvGlue x * x⁻¹ ^ 2 - expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2) =
      expNegInvGlue x * expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) := by
    ring
  rw [hnum2]

theorem smoothTransition_deriv_zero_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  by_cases hx0 : x < 0
  · have hconst' : Filter.EventuallyEq (nhds x)
        (fun y : ℝ => Real.smoothTransition y) (fun _ => (0 : ℝ)) := by
      rw [Filter.EventuallyEq]
      filter_upwards [Iio_mem_nhds hx0] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    have hd : HasDerivAt Real.smoothTransition 0 x := by
      exact (hasDerivAt_const (x := x) (c := (0 : ℝ))).congr_of_eventuallyEq hconst'
    rw [hd.deriv]
  · have hxeq : x = 0 := le_antisymm hx (le_of_not_gt hx0)
    subst x
    have hτw : HasDerivWithinAt Real.smoothTransition 0 (Set.Iic 0) 0 := by
      have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic 0) 0 :=
        hasDerivWithinAt_const (x := (0 : ℝ)) (s := Set.Iic 0) (c := (0 : ℝ))
      refine hconst.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy
      · simp
    exact HasDerivWithinAt.deriv_eq_zero hτw (uniqueDiffWithinAt_Iic 0)

theorem smoothTransition_deriv_zero_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  by_cases hx0 : 1 < x
  · have hconst' : Filter.EventuallyEq (nhds x)
        (fun y : ℝ => Real.smoothTransition y) (fun _ => (1 : ℝ)) := by
      rw [Filter.EventuallyEq]
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    have hd : HasDerivAt Real.smoothTransition 0 x := by
      exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).congr_of_eventuallyEq hconst'
    rw [hd.deriv]
  · have hxeq : x = 1 := le_antisymm (by linarith) hx
    subst x
    have hτw : HasDerivWithinAt Real.smoothTransition 0 (Set.Ici 1) 1 := by
      have hconst : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ici 1) 1 :=
        hasDerivWithinAt_const (x := (1 : ℝ)) (s := Set.Ici 1) (c := (1 : ℝ))
      refine hconst.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact Real.smoothTransition.one_of_one_le hy
      · simp
    exact HasDerivWithinAt.deriv_eq_zero hτw (uniqueDiffWithinAt_Ici 1)

theorem portPrivate_138057aa_smoothTransition_deriv_le_forty_of_le_quarter (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hxlo : x ≤ 1 / 4) :
    deriv Real.smoothTransition x ≤ 40 := by
  have hExpGlue : ∀ y : ℝ, 0 < y → expNegInvGlue y = Real.exp (-y⁻¹) := by
    intro y hy
    rw [expNegInvGlue, ite_eq_right (not_le.mpr hy)]
  rw [smoothTransition_deriv_eq hx0 hx1]
  have hA : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
  have hB : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
  have hAB : expNegInvGlue x * expNegInvGlue (1 - x) /
      (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ 40 := by
    have hxinv : (4 : ℝ) ≤ x⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hx0).2 (by nlinarith only [hxlo])
    have h1xinv : (1 - x)⁻¹ ≤ 4 / 3 := by
      rw [← one_div]
      exact (div_le_iff₀ (by linarith : 0 < 1 - x)).2 (by nlinarith only [hxlo])
    have h1xsq : (1 - x)⁻¹ ^ 2 ≤ 16 / 9 := by
      have hle : (1 - x)⁻¹ ≤ 4 / 3 := h1xinv
      have hnon : 0 ≤ (1 - x)⁻¹ :=
        inv_nonneg.mpr (le_of_lt (by linarith : 0 < 1 - x))
      calc
        (1 - x)⁻¹ ^ 2 ≤ (4 / 3) ^ 2 := by
          exact sq_le_sq.mpr ((abs_of_nonneg hnon).trans_le (by
            rw [abs_of_nonneg (by norm_num : 0 ≤ (4 / 3 : ℝ))]
            exact hle))
        _ = 16 / 9 := by norm_num
    have hratio : expNegInvGlue x * expNegInvGlue (1 - x) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≤
        expNegInvGlue x / expNegInvGlue (1 - x) := by
      rw [div_le_div_iff₀ (by positivity : 0 < (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) hB]
      rw [mul_assoc]
      have hB2 : expNegInvGlue (1 - x) ^ 2 ≤
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
        have hAB2' : expNegInvGlue (1 - x) ^ 2 < (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
          nlinarith only [sq_nonneg (expNegInvGlue x : ℝ), hA, hB]
        exact le_of_lt hAB2'
      exact mul_le_mul_of_nonneg_left (by simpa [pow_two] using hB2) (le_of_lt hA)
    have hABexp : expNegInvGlue x / expNegInvGlue (1 - x) ≤ Real.exp (4 / 3) * expNegInvGlue x := by
      have hval : expNegInvGlue x / expNegInvGlue (1 - x) = Real.exp (-x⁻¹ + (1 - x)⁻¹) := by
        rw [hExpGlue x hx0, hExpGlue (1 - x) (by linarith : 0 < 1 - x), ← Real.exp_sub]
        have hargs : -x⁻¹ - (-(1 - x)⁻¹) = -x⁻¹ + (1 - x)⁻¹ := by ring
        rw [hargs]
      rw [hval]
      rw [Real.exp_add]
      rw [hExpGlue x hx0]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le h1xinv)
        (Real.exp_pos (-x⁻¹)).le
    have hterm : expNegInvGlue x / expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤
        Real.exp (4 / 3) * (2 + 16 / 9) := by
      have hle1 : expNegInvGlue x / expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤
          Real.exp (4 / 3) * expNegInvGlue x * (x⁻¹ ^ 2 + 16 / 9) := by
        have hsumle : x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 ≤ x⁻¹ ^ 2 + 16 / 9 := by
          nlinarith only [h1xsq]
        have hposb : 0 ≤ Real.exp (4 / 3) * expNegInvGlue x := by positivity
        exact mul_le_mul hABexp hsumle (by positivity) hposb
      have hle2 : Real.exp (4 / 3) * expNegInvGlue x * (x⁻¹ ^ 2 + 16 / 9) ≤
          Real.exp (4 / 3) * (2 + 16 / 9) := by
        have hE : expNegInvGlue x * (x⁻¹ ^ 2 + 16 / 9) ≤ 2 + 16 / 9 := by
          have h1 : expNegInvGlue x * x⁻¹ ^ 2 ≤ 2 := by
            have hquad : 0 ≤ x⁻¹ := by positivity
            have hval : expNegInvGlue x * x⁻¹ ^ 2 = x⁻¹ ^ 2 / Real.exp x⁻¹ := by
              rw [hExpGlue x hx0]
              rw [Real.exp_neg]
              field_simp
            rw [hval]
            rw [div_le_iff₀ (Real.exp_pos x⁻¹)]
            have hm : x⁻¹ ^ 2 ≤ 2 * Real.exp x⁻¹ := by
              have hq2 : 1 + x⁻¹ + x⁻¹ ^ 2 / 2 ≤ Real.exp x⁻¹ := Real.quadratic_le_exp_of_nonneg hquad
              nlinarith only [hquad, hq2]
            exact hm
          have h2 : expNegInvGlue x * (16 / 9) ≤ 16 / 9 := by
            have hle : expNegInvGlue x ≤ 1 := by
              have hval : expNegInvGlue x = Real.exp (-x⁻¹) := hExpGlue x hx0
              rw [hval]
              have hneg : -x⁻¹ ≤ 0 := by nlinarith only [hxinv]
              have h1' : Real.exp (-x⁻¹) ≤ Real.exp 0 :=
                Real.exp_le_exp.mpr (by nlinarith only [hxinv])
              simpa using h1'
            simpa [mul_comm] using
              mul_le_of_le_one_right (by norm_num : 0 ≤ (16 / 9 : ℝ)) hle
          nlinarith only [h1, h2]
        have hpos : 0 ≤ Real.exp (4 / 3) := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hE hpos
      exact le_trans hle1 hle2
    have hfin : Real.exp (4 / 3) * (2 + 16 / 9) ≤ 40 := by
      have h1 : Real.exp (4 / 3) < 9 := by
        have hE1 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have hE13 : Real.exp (1 / 3) ≤ Real.exp 1 := Real.exp_le_exp_of_le (by norm_num)
        have hval : Real.exp (4 / 3) = Real.exp 1 * Real.exp (1 / 3) := by
          rw [← Real.exp_add]
          ring_nf
        rw [hval]
        have hpos13 : 0 ≤ Real.exp (1 / 3) := (Real.exp_pos _).le
        have hpos1 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
        nlinarith only [hE1, hE13, hpos13, hpos1]
      nlinarith only [h1]
    have hmain : expNegInvGlue x * expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 *
        (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ expNegInvGlue x / expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    exact le_trans (le_trans hmain hterm) (by nlinarith only [hfin])
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hAB

theorem portPrivate_138057aa_smoothTransition_deriv_le_forty_of_ge_three_quarters (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hxhi : 3 / 4 ≤ x) :
    deriv Real.smoothTransition x ≤ 40 := by
  have hExpGlue : ∀ y : ℝ, 0 < y → expNegInvGlue y = Real.exp (-y⁻¹) := by
    intro y hy
    rw [expNegInvGlue, ite_eq_right (not_le.mpr hy)]
  rw [smoothTransition_deriv_eq hx0 hx1]
  have hA : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
  have hB : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
  have hAB : expNegInvGlue x * expNegInvGlue (1 - x) /
      (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ 40 := by
    have hABsq : (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≥
        expNegInvGlue x ^ 2 := by
      have hle : expNegInvGlue x + expNegInvGlue (1 - x) ≥ expNegInvGlue x := by linarith
      have hnon : 0 ≤ expNegInvGlue x := le_of_lt hA
      have hnon2 : 0 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by positivity
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg hnon2]
        rw [abs_of_nonneg hnon]
        exact hle)
    have hratio : expNegInvGlue x * expNegInvGlue (1 - x) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≤
        expNegInvGlue (1 - x) / expNegInvGlue x := by
      rw [div_le_div_iff₀ (by positivity : 0 < (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) hA]
      nlinarith only [hA, hB, hABsq]
    have h1x' : (1 - x)⁻¹ ≥ 4 := by
      rw [← one_div]
      exact (le_div_iff₀ (by linarith : 0 < 1 - x)).2 (by nlinarith only [hxhi])
    have hx' : x⁻¹ ≤ 4 / 3 := by
      rw [← one_div]
      exact (div_le_iff₀ hx0).2 (by nlinarith only [hxhi])
    have hxsq : x⁻¹ ^ 2 ≤ 16 / 9 := by
      have hnon : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hx0)
      calc
        x⁻¹ ^ 2 ≤ (4 / 3) ^ 2 := by
          exact sq_le_sq.mpr ((abs_of_nonneg hnon).trans_le (by
            rw [abs_of_nonneg (by norm_num : 0 ≤ (4 / 3 : ℝ))]
            exact hx'))
        _ = 16 / 9 := by norm_num
    have hABexp : expNegInvGlue (1 - x) / expNegInvGlue x ≤ Real.exp (4 / 3) * expNegInvGlue (1 - x) := by
      have hval : expNegInvGlue (1 - x) / expNegInvGlue x = Real.exp (-(1 - x)⁻¹ + x⁻¹) := by
        rw [hExpGlue (1 - x) (by linarith : 0 < 1 - x), hExpGlue x hx0, ← Real.exp_sub]
        have hargs : -(1 - x)⁻¹ - (-x⁻¹) = -(1 - x)⁻¹ + x⁻¹ := by ring
        rw [hargs]
      rw [hval]
      rw [Real.exp_add]
      rw [hExpGlue (1 - x) (by linarith : 0 < 1 - x)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le hx')
        (Real.exp_pos (-(1 - x)⁻¹)).le
    have hterm : expNegInvGlue (1 - x) / expNegInvGlue x * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤
        Real.exp (4 / 3) * (2 + 16 / 9) := by
      have hle1 : expNegInvGlue (1 - x) / expNegInvGlue x * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤
          Real.exp (4 / 3) * expNegInvGlue (1 - x) * (16 / 9 + (1 - x)⁻¹ ^ 2) := by
        have hsumle : x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 ≤ 16 / 9 + (1 - x)⁻¹ ^ 2 := by
          nlinarith only [hxsq]
        have hposb : 0 ≤ Real.exp (4 / 3) * expNegInvGlue (1 - x) := by positivity
        exact mul_le_mul hABexp hsumle (by positivity) hposb
      have hle2 : Real.exp (4 / 3) * expNegInvGlue (1 - x) * (16 / 9 + (1 - x)⁻¹ ^ 2) ≤
          Real.exp (4 / 3) * (2 + 16 / 9) := by
        have hE : expNegInvGlue (1 - x) * (16 / 9 + (1 - x)⁻¹ ^ 2) ≤ 2 + 16 / 9 := by
          have h1 : expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2 ≤ 2 := by
            have hquad : 0 ≤ (1 - x)⁻¹ := by positivity
            have hval : expNegInvGlue (1 - x) * (1 - x)⁻¹ ^ 2 = (1 - x)⁻¹ ^ 2 / Real.exp (1 - x)⁻¹ := by
              rw [hExpGlue (1 - x) (by linarith : 0 < 1 - x)]
              rw [Real.exp_neg]
              field_simp
            rw [hval]
            rw [div_le_iff₀ (Real.exp_pos (1 - x)⁻¹)]
            have hq2 : 1 + (1 - x)⁻¹ + (1 - x)⁻¹ ^ 2 / 2 ≤ Real.exp (1 - x)⁻¹ :=
              Real.quadratic_le_exp_of_nonneg hquad
            nlinarith only [hquad, hq2]
          have h2 : expNegInvGlue (1 - x) * (16 / 9) ≤ 16 / 9 := by
            have hle : expNegInvGlue (1 - x) ≤ 1 := by
              have hval : expNegInvGlue (1 - x) = Real.exp (-(1 - x)⁻¹) :=
                hExpGlue (1 - x) (by linarith : 0 < 1 - x)
              rw [hval]
              have hneg : -(1 - x)⁻¹ ≤ 0 := by nlinarith only [h1x']
              have h1' : Real.exp (-(1 - x)⁻¹) ≤ Real.exp 0 :=
                Real.exp_le_exp.mpr (by nlinarith only [h1x'])
              simpa using h1'
            simpa [mul_comm] using
              mul_le_of_le_one_right (by norm_num : 0 ≤ (16 / 9 : ℝ)) hle
          nlinarith only [h1, h2]
        have hpos : 0 ≤ Real.exp (4 / 3) := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hE hpos
      exact le_trans hle1 hle2
    have hfin : Real.exp (4 / 3) * (2 + 16 / 9) ≤ 40 := by
      have h1 : Real.exp (4 / 3) < 9 := by
        have hE1 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have hE13 : Real.exp (1 / 3) ≤ Real.exp 1 := Real.exp_le_exp_of_le (by norm_num)
        have hval : Real.exp (4 / 3) = Real.exp 1 * Real.exp (1 / 3) := by
          rw [← Real.exp_add]
          ring_nf
        rw [hval]
        have hpos13 : 0 ≤ Real.exp (1 / 3) := (Real.exp_pos _).le
        have hpos1 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
        nlinarith only [hE1, hE13, hpos13, hpos1]
      nlinarith only [h1]
    have hmain : expNegInvGlue x * expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 *
        (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ expNegInvGlue (1 - x) / expNegInvGlue x * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    exact le_trans (le_trans hmain hterm) (by nlinarith only [hfin])
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hAB

theorem portPrivate_138057aa_smoothTransition_deriv_le_forty_middle (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hxq' : 1 / 4 ≤ x ∧ x ≤ 3 / 4) :
    deriv Real.smoothTransition x ≤ 40 := by
  rw [smoothTransition_deriv_eq hx0 hx1]
  have hA : 0 < expNegInvGlue x := expNegInvGlue.pos_of_pos hx0
  have hB : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
  have hAB : expNegInvGlue x * expNegInvGlue (1 - x) /
      (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ 40 := by
    have hx2 : x⁻¹ ^ 2 ≤ 16 := by
      have hle : x⁻¹ ≤ 4 := by
        have hpos : 0 < x := hx0
        rw [← one_div]
        exact (div_le_iff₀ hpos).2 (by nlinarith only [hxq'.1])
      have hnon : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hx0)
      calc
        x⁻¹ ^ 2 ≤ 4 ^ 2 := by
          exact sq_le_sq.mpr ((abs_of_nonneg hnon).trans_le (by simpa using hle))
        _ = 16 := by norm_num
    have h1x2 : (1 - x)⁻¹ ^ 2 ≤ 16 := by
      have hle : (1 - x)⁻¹ ≤ 4 := by
        have hpos : 0 < 1 - x := by linarith
        rw [← one_div]
        exact (div_le_iff₀ hpos).2 (by nlinarith only [hxq'.2])
      have hnon : 0 ≤ (1 - x)⁻¹ :=
        inv_nonneg.mpr (le_of_lt (by linarith : 0 < 1 - x))
      calc
        (1 - x)⁻¹ ^ 2 ≤ 4 ^ 2 := by
          exact sq_le_sq.mpr ((abs_of_nonneg hnon).trans_le (by simpa using hle))
        _ = 16 := by norm_num
    have hsum : x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 ≤ 32 := by nlinarith
    have hmid : expNegInvGlue x * expNegInvGlue (1 - x) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ 40 := by
      have h1 : expNegInvGlue x * expNegInvGlue (1 - x) /
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀
          (pow_pos (add_pos hA hB) 2)
          (by norm_num : (0 : ℝ) < 4)]
        have ham' : 4 * expNegInvGlue x * expNegInvGlue (1 - x) ≤
            (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
          have hsub : 0 ≤ (expNegInvGlue x - expNegInvGlue (1 - x)) ^ 2 := sq_nonneg _
          nlinarith only [hsub]
        nlinarith only [ham']
      have hprod : (expNegInvGlue x * expNegInvGlue (1 - x) /
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) *
          (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤ (1 / 4) * 32 := by
        exact mul_le_mul h1 hsum (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
      exact le_trans hprod (by norm_num)
    exact hmid
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hAB

theorem smoothTransition_deriv_le_forty (x : ℝ) : deriv Real.smoothTransition x ≤ 40 := by
  by_cases hx : x ≤ 0 ∨ 1 ≤ x
  · rcases hx with hxle | hxge
    · rw [smoothTransition_deriv_zero_of_nonpos x hxle]
      norm_num
    · rw [smoothTransition_deriv_zero_of_one_le x hxge]
      norm_num
  · have hx0 : 0 < x := by
      rw [not_or] at hx
      exact lt_of_not_ge hx.1
    have hx1 : x < 1 := by
      rw [not_or] at hx
      exact lt_of_not_ge hx.2
    by_cases hxq : x ≤ 1 / 4 ∨ 3 / 4 ≤ x
    · rcases hxq with hxlo | hxhi
      · exact portPrivate_138057aa_smoothTransition_deriv_le_forty_of_le_quarter x hx0 hx1 hxlo
      · exact portPrivate_138057aa_smoothTransition_deriv_le_forty_of_ge_three_quarters x hx0 hx1 hxhi
    · have hxq' : 1 / 4 ≤ x ∧ x ≤ 3 / 4 := by
        rw [not_or] at hxq
        exact ⟨le_of_lt (lt_of_not_ge hxq.1), le_of_lt (lt_of_not_ge hxq.2)⟩
      exact portPrivate_138057aa_smoothTransition_deriv_le_forty_middle x hx0 hx1 hxq'
end Real

theorem portPrivate_138057aa_one_add_sub_one_mul_mem_Icc {U β : ℝ} (hU : 1 ≤ U)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 1 + (U - 1) * β ∧ 1 + (U - 1) * β ≤ U := by
  constructor
  · exact add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hU) hβ.1)
  · calc
      1 + (U - 1) * β ≤ 1 + (U - 1) * 1 :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hβ.2 (sub_nonneg.mpr hU))
      _ = U := by ring

theorem portPrivate_138057aa_one_add_sub_one_mul_sq_le {U β : ℝ} (hU : 1 ≤ U)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (1 + (U - 1) * β) ^ 2 ≤ U ^ 2 := by
  have hbounds := portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hβ
  exact (sq_le_sq₀ hbounds.1 (le_trans zero_le_one hU)).2 hbounds.2


def negIdx {n k : ℕ} (hk : k ≤ n) (i : Fin k) : Fin n :=
  Fin.castLE hk i

def posIdx {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) : Fin n :=
  ⟨k + j, by omega⟩

def morseNormalForm {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) : ℝ :=
  c + (1 / 2) * (∑ i : Fin k, - (y (negIdx hk i)) ^ 2 +
    ∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)

def cellMap {n k : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    MorseModel n :=
  fun i => if h : i.val < k then r * x ⟨i.val, h⟩ else 0

theorem cellMap_negIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    cellMap ε x (negIdx hk i) = ε * x i := by
  dsimp [cellMap, negIdx]
  simp [i.isLt]

theorem cellMap_posIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin (n - k)) :
    cellMap ε x (posIdx hk j) = 0 := by
  dsimp [cellMap, posIdx]
  rw [dite_eq_right]
  omega

theorem morseNormalForm_cellMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    morseNormalForm hk c (cellMap ε x) = c + (1 / 2) * (-(ε ^ 2) * ‖x‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (cellMap ε x (negIdx hk i)) ^ 2) = -(ε ^ 2) * ‖x‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (cellMap ε x (negIdx hk i)) ^ 2)
          = ∑ i : Fin k, - (ε * x i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [cellMap_negIdx]
      _ = -(ε ^ 2) * ∑ i : Fin k, (x i) ^ 2 := by
        rw [Finset.sum_neg_distrib]
        rw [Finset.mul_sum]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow]
        ring
      _ = -(ε ^ 2) * ‖x‖ ^ 2 := by
        congr 1
        exact (EuclideanSpace.real_norm_sq_eq x).symm
  have hpos : (∑ j : Fin (n - k), (cellMap ε x (posIdx hk j)) ^ 2) = 0 := by
    simp [cellMap_posIdx]
  rw [hneg, hpos]
  ring

def attachMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) (x : CellBoundary k) :
    sublevel (morseNormalForm hk c) (c - ε) :=
  ⟨cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ = 1 := x.2
    have hf : morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) =
        c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
      rw [morseNormalForm_cellMap]
    have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
    have hle : c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) ≤ c - ε := by
      rw [hsq, hnorm]
      ring_nf
      exact le_rfl
    simpa [sublevel] using hf.trans_le hle⟩

theorem cellMap_mem_sublevel_upper {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (x : ClosedCell k) (hε : 0 ≤ ε) :
    cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
      sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c + ε
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := x.2
  have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  rw [hf]
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  have hle : (1 / 2 : ℝ) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) ≤ ε := by
    rw [hsq]
    nlinarith only [hε, sq_nonneg ‖(x : EuclideanSpace ℝ (Fin k))‖]
  linarith

def negPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i : Fin k => y (negIdx hk i))

def posPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : EuclideanSpace ℝ (Fin (n - k)) :=
  WithLp.toLp 2 (fun j : Fin (n - k) => y (posIdx hk j))

theorem negPart_top {n : ℕ} (y : MorseModel n) :
    (negPart (le_rfl : n ≤ n) y : EuclideanSpace ℝ (Fin n)) = y := by
  funext i
  rfl

theorem posPart_top {n : ℕ} (y : MorseModel n) :
    posPart (le_rfl : n ≤ n) y = (0 : EuclideanSpace ℝ (Fin (n - n))) := by
  ext i
  have hn : n - n = 0 := Nat.sub_self n
  have hi : i.1 < 0 := by simpa [hn] using i.isLt
  exact False.elim (Nat.not_lt_zero i.1 hi)

theorem negPart_bot {n : ℕ} (y : MorseModel n) :
    negPart (Nat.zero_le n) y = (0 : EuclideanSpace ℝ (Fin 0)) := by
  ext i
  exact False.elim (Nat.not_lt_zero i.1 i.isLt)

theorem posPart_bot {n : ℕ} (y : MorseModel n) :
    (posPart (Nat.zero_le n) y : EuclideanSpace ℝ (Fin n)) = y := by
  ext i
  change y (posIdx (Nat.zero_le n) i) = y i
  congr 1
  apply Fin.ext
  simp [posIdx]

def recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) : MorseModel n :=
  fun i => if h : i.val < k then a ⟨i.val, h⟩ else b ⟨i.val - k, by
    have hkle : k ≤ i.val := le_of_not_gt h
    have hi : i.val < n := i.isLt
    omega⟩

theorem recombine_negPart {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) (i : Fin k) :
    recombine hk a b (negIdx hk i) = a i := by
  dsimp [recombine, negIdx]
  simp [i.isLt]

theorem recombine_posPart {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) (j : Fin (n - k)) :
    recombine hk a b (posIdx hk j) = b j := by
  dsimp [recombine, posIdx]
  rw [dite_eq_right (by omega : ¬ k + (j : ℕ) < k)]
  apply congrArg b.ofLp
  apply Fin.ext
  simp

theorem recombine_top {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin (n - n))) :
    recombine (le_rfl : n ≤ n) a b = a := by
  funext i
  dsimp [recombine]
  rw [dite_eq_left i.isLt]

theorem recombine_bot {n : ℕ} (a : EuclideanSpace ℝ (Fin 0))
    (b : EuclideanSpace ℝ (Fin n)) :
    recombine (Nat.zero_le n) a b = b := by
  funext i
  dsimp [recombine]

theorem recombine_decompose {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    recombine hk (negPart hk y) (posPart hk y) = y := by
  funext i
  by_cases h : i.val < k
  · have hi : i = negIdx hk ⟨i.val, h⟩ := by
      apply Fin.ext
      rfl
    calc
      recombine hk (negPart hk y) (posPart hk y) i
          = recombine hk (negPart hk y) (posPart hk y) (negIdx hk ⟨i.val, h⟩) := by rw [← hi]
      _ = negPart hk y ⟨i.val, h⟩ := recombine_negPart hk (negPart hk y) (posPart hk y) ⟨i.val, h⟩
      _ = y i := by
        have hi' : negIdx hk ⟨i.val, h⟩ = i := hi.symm
        change y (negIdx hk ⟨i.val, h⟩) = y i
        rw [hi']
  · have hi : i = posIdx hk ⟨i.val - k, by
        have hkle : k ≤ i.val := le_of_not_gt h
        have hi' : i.val < n := i.isLt
        omega⟩ := by
      apply Fin.ext
      have hkle : k ≤ i.val := le_of_not_gt h
      change ↑i = k + (↑i - k)
      rw [Nat.add_sub_of_le hkle]
    calc
      recombine hk (negPart hk y) (posPart hk y) i
          = recombine hk (negPart hk y) (posPart hk y) (posIdx hk ⟨i.val - k, _⟩) := by
            rw [← hi]
      _ = posPart hk y ⟨i.val - k, _⟩ := recombine_posPart hk (negPart hk y) (posPart hk y) ⟨i.val - k, _⟩
      _ = y i := by
        have hi' : posIdx hk ⟨i.val - k, _⟩ = i := hi.symm
        change y (posIdx hk ⟨i.val - k, _⟩) = y i
        rw [hi']

theorem negPart_cellMap_apply {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    negPart hk (cellMap ε u) i = ε * u i := by
  dsimp [negPart, cellMap, negIdx]
  simp [i.isLt]

theorem negPart_cellMap_norm_sq {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    ‖negPart hk (cellMap ε u)‖ ^ 2 = ε ^ 2 * ‖u‖ ^ 2 := by
  calc
    ‖negPart hk (cellMap ε u)‖ ^ 2
        = ∑ i : Fin k, (negPart hk (cellMap ε u) i) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap ε u))]
    _ = ∑ i : Fin k, (ε * u i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [negPart_cellMap_apply]
    _ = ε ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]
    _ = ε ^ 2 * ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq u]

theorem morseNormalForm_recombine {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap ε u)) v) =
      c + (1 / 2) * (-(ε ^ 2) * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (recombine hk (negPart hk (cellMap ε u)) v (negIdx hk i)) ^ 2) =
      -(ε ^ 2) * ‖u‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (recombine hk (negPart hk (cellMap ε u)) v (negIdx hk i)) ^ 2)
          = ∑ i : Fin k, - (negPart hk (cellMap ε u) i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [recombine_negPart]
      _ = -((ε ^ 2) * ‖u‖ ^ 2) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        rw [← EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap ε u))]
        exact negPart_cellMap_norm_sq hk ε u
      _ = -(ε ^ 2) * ‖u‖ ^ 2 := by
        ring
  have hpos : (∑ j : Fin (n - k),
      (recombine hk (negPart hk (cellMap ε u)) v (posIdx hk j)) ^ 2) = ‖v‖ ^ 2 := by
    calc
      (∑ j : Fin (n - k), (recombine hk (negPart hk (cellMap ε u)) v (posIdx hk j)) ^ 2)
          = ∑ j : Fin (n - k), (v j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [recombine_posPart]
      _ = ‖v‖ ^ 2 := by
        exact (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hneg, hpos]

theorem morseNormalForm_recombine_cellMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) v) =
      c + (1 / 2) * (-(2 * ε) * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [morseNormalForm_recombine hk c (Real.sqrt (2 * ε)) u v]
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  rw [hsq]

theorem morseNormalForm_cocoreMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) v) =
      c - ε + (1 / 2) * ‖v‖ ^ 2 := by
  have hval := morseNormalForm_recombine_cellMap hk c ε hε u v
  rw [hval, hu]
  ring

theorem morseNormalForm_recombine_scaled {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) =
      c + (1 / 2) * (-(2 * ε) * ‖u‖ ^ 2 + r ^ 2 * ‖v‖ ^ 2) := by
  rw [morseNormalForm_recombine_cellMap hk c ε hε u (r • v)]
  have hnorm : ‖(r • v : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  rw [hnorm]

theorem morseNormalForm_split {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    morseNormalForm hk c y =
      c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -‖negPart hk y‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -(∑ i : Fin k, (negPart hk y i) ^ 2) := by
        rw [Finset.sum_neg_distrib]
        congr 1
      _ = -‖negPart hk y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
  have hpos : (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) = ‖posPart hk y‖ ^ 2 := by
    calc
      (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)
          = ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = ‖posPart hk y‖ ^ 2 := by
        exact (EuclideanSpace.real_norm_sq_eq (posPart hk y)).symm
  rw [hneg, hpos]
  ring_nf

def spineMap {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) 0

theorem spineMap_split {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    morseNormalForm hk c (spineMap hk y) = c - (1 / 2) * ‖negPart hk y‖ ^ 2 := by
  have hneg : negPart hk (spineMap hk y) = negPart hk y := by
    ext i
    dsimp [spineMap, negPart]
    rw [recombine_negPart]
  have hpos : posPart hk (spineMap hk y) = 0 := by
    ext j
    dsimp [spineMap, posPart]
    rw [recombine_posPart]
    simp
  rw [morseNormalForm_split hk c (spineMap hk y), hpos, hneg]
  simp
  ring_nf

theorem spineMap_mem_lower {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    {y : MorseModel n} (hy : 2 * ε ≤ ‖negPart hk y‖ ^ 2) :
    spineMap hk y ∈ sublevel (morseNormalForm hk c) (c - ε) := by
  change morseNormalForm hk c (spineMap hk y) ≤ c - ε
  rw [spineMap_split]
  nlinarith only [hy, sq_nonneg ‖negPart hk y‖]

theorem spineMap_mem_cell {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε)
    {y : MorseModel n} (hy : ‖negPart hk y‖ ^ 2 ≤ 2 * ε) :
    spineMap hk y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  have hr : 0 < Real.sqrt (2 * ε) := by
    exact Real.sqrt_pos.2 (by positivity : 0 < 2 * ε)
  let x : ClosedCell k :=
    ⟨(Real.sqrt (2 * ε))⁻¹ • negPart hk y, by
      have hnorm : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε) := by
        have hsq : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
          exact hy
        have habs := (sq_le_sq.mp hsq)
        simpa [abs_of_nonneg] using habs
      rw [norm_smul]
      have habs : |(Real.sqrt (2 * ε))⁻¹| = (Real.sqrt (2 * ε))⁻¹ := by
        rw [abs_of_pos]
        positivity
      rw [Real.norm_eq_abs, habs]
      have h1 : (Real.sqrt (2 * ε))⁻¹ * ‖negPart hk y‖ ≤
          (Real.sqrt (2 * ε))⁻¹ * Real.sqrt (2 * ε) := by
        exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (le_of_lt hr))
      have h2 : (Real.sqrt (2 * ε))⁻¹ * Real.sqrt (2 * ε) = 1 := by
        rw [inv_mul_cancel₀ hr.ne']
      rwa [h2] at h1⟩
  refine ⟨x, ?_⟩
  ext i
  by_cases hi : i.val < k
  · have hi' : i = negIdx hk ⟨i.val, hi⟩ := by
      apply Fin.ext
      rfl
    calc
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk ⟨i.val, hi⟩) := by rw [← hi']
      _ = Real.sqrt (2 * ε) * (x : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩ :=
        cellMap_negIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩
      _ = Real.sqrt (2 * ε) * ((Real.sqrt (2 * ε))⁻¹ * negPart hk y ⟨i.val, hi⟩) := by
        dsimp [x]
      _ = negPart hk y ⟨i.val, hi⟩ := by
        field_simp [hr.ne']
      _ = recombine hk (negPart hk y) 0 (negIdx hk ⟨i.val, hi⟩) := by
        rw [recombine_negPart]
      _ = recombine hk (negPart hk y) 0 i := by
        exact congrArg (recombine hk (negPart hk y) 0) hi'.symm
  · have hi' : i = posIdx hk ⟨i.val - k, by
        have hkle : k ≤ i.val := le_of_not_gt hi
        have hii : i.val < n := i.isLt
        omega⟩ := by
      apply Fin.ext
      have hkle : k ≤ i.val := le_of_not_gt hi
      change ↑i = k + (↑i - k)
      rw [Nat.add_sub_of_le hkle]
    calc
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (posIdx hk ⟨i.val - k, _⟩) := by rw [← hi']
      _ = 0 := cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ⟨i.val - k, _⟩
      _ = recombine hk (negPart hk y) 0 (posIdx hk ⟨i.val - k, _⟩) := by
        rw [recombine_posPart]
        rfl
      _ = recombine hk (negPart hk y) 0 i := by
        exact congrArg (recombine hk (negPart hk y) 0) hi'.symm

noncomputable def lowerCellUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Set (MorseModel n) :=
  sublevel (morseNormalForm hk c) (c - ε) ∪
    Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))

abbrev upperSublevel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Type :=
  SublevelSpace (morseNormalForm hk c) (c + ε)

abbrev lowerUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Type :=
  {y : MorseModel n // y ∈ lowerCellUnion hk c ε}

theorem spineMap_mem_union {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (y : MorseModel n) :
    spineMap hk y ∈ lowerCellUnion hk c ε := by
  dsimp [lowerCellUnion]
  by_cases h : 2 * ε ≤ ‖negPart hk y‖ ^ 2
  · exact Or.inl (spineMap_mem_lower hk c ε h)
  · exact Or.inr (spineMap_mem_cell hk ε hε (le_of_not_ge h))

def cellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    upperSublevel hk c ε → lowerUnion hk c ε :=
  fun y =>
    ⟨spineMap hk y.1, spineMap_mem_union hk c ε hε y.1⟩

theorem cellAttachmentInclusion_mem {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (z : lowerUnion hk c ε) :
    z.1 ∈ sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c z.1 ≤ c + ε
  rcases z.2 with hz | ⟨x, hx⟩
  · have hle : morseNormalForm hk c z.1 ≤ c - ε := by simpa [sublevel] using hz
    linarith
  · rw [← hx]
    simpa [sublevel] using (cellMap_mem_sublevel_upper hk c ε (⟨x, x.2⟩ : ClosedCell k) hε)

def cellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    lowerUnion hk c ε → upperSublevel hk c ε :=
  fun z =>
    ⟨z.1, cellAttachmentInclusion_mem hk c ε hε z⟩

def cellRetractionStep {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) (t • posPart hk y)

theorem cellRetractionStep_decompose {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    cellRetractionStep hk 1 y = y := by
  dsimp [cellRetractionStep]
  rw [one_smul]
  exact recombine_decompose hk y

theorem cellRetractionStep_spine {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    cellRetractionStep hk 0 y = spineMap hk y := by
  dsimp [cellRetractionStep, spineMap]
  rw [zero_smul]

theorem cellRetractionStep_level {n k : ℕ} (hk : k ≤ n) (c : ℝ) {t : ℝ} (y : MorseModel n) :
    morseNormalForm hk c (cellRetractionStep hk t y) =
      c + (1 / 2) * (t ^ 2 * ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
  have hneg : negPart hk (cellRetractionStep hk t y) = negPart hk y := by
    ext i
    dsimp [cellRetractionStep, negPart]
    rw [recombine_negPart]
  have hpos : posPart hk (cellRetractionStep hk t y) = t • posPart hk y := by
    ext j
    dsimp [cellRetractionStep, posPart]
    rw [recombine_posPart]
    simp
  rw [morseNormalForm_split hk c (cellRetractionStep hk t y), hpos, hneg]
  rw [norm_smul, mul_pow]
  rw [Real.norm_eq_abs, sq_abs]

theorem cellRetractionStep_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {y : MorseModel n} (hy : y ∈ sublevel (morseNormalForm hk c) (c + ε)) :
    cellRetractionStep hk t y ∈ sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c (cellRetractionStep hk t y) ≤ c + ε
  rw [cellRetractionStep_level hk c y]
  have hle : t ^ 2 ≤ 1 := by nlinarith only [sq_nonneg t, ht0, ht1]
  have hy' : morseNormalForm hk c y ≤ c + ε := by simpa [sublevel] using hy
  have hsplit := morseNormalForm_split hk c y
  rw [hsplit] at hy'
  nlinarith only [hy', hle, sq_nonneg ‖negPart hk y‖, sq_nonneg ‖posPart hk y‖]

def cellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε → upperSublevel hk c ε :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1,
      cellRetractionStep_mem_upper hk c ε (t := p.1.1) (y := p.2.1) p.1.2.1 p.1.2.2 p.2.2⟩

theorem cellRetractionHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (y : upperSublevel hk c ε) :
    cellRetractionHomotopyFun hk c ε (⟨0, by norm_num⟩, y) =
      cellAttachmentInclusion hk c ε (le_of_lt hε) (cellAttachmentMap hk c ε hε y) := by
  apply Subtype.ext
  dsimp [cellRetractionHomotopyFun, cellAttachmentInclusion, cellAttachmentMap]
  exact cellRetractionStep_spine hk y.1

theorem cellRetractionHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (y : upperSublevel hk c ε) :
    cellRetractionHomotopyFun hk c ε (⟨1, by norm_num⟩, y) = y := by
  apply Subtype.ext
  dsimp [cellRetractionHomotopyFun]
  exact cellRetractionStep_decompose hk y.1

def cellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε → lowerUnion hk c ε :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1, by
      rcases p.2.2 with hz | ⟨x, hx⟩
      · left
        change morseNormalForm hk c (cellRetractionStep hk (p.1 : ℝ) p.2.1) ≤ c - ε
        rw [cellRetractionStep_level hk c p.2.1]
        have hz' : morseNormalForm hk c p.2.1 ≤ c - ε := by simpa [sublevel] using hz
        have hsplit := morseNormalForm_split hk c p.2.1
        rw [hsplit] at hz'
        have hle : (p.1 : ℝ) ^ 2 ≤ 1 := by nlinarith only [sq_nonneg (p.1 : ℝ), p.1.2.1, p.1.2.2]
        nlinarith only [hz', hle, sq_nonneg ‖negPart hk p.2.1‖,
          sq_nonneg ‖posPart hk p.2.1‖]
      · right
        have hposz : posPart hk p.2.1 = 0 := by
          ext j
          rw [← hx]
          dsimp [posPart]
          exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
        have hstep : cellRetractionStep hk (p.1 : ℝ) p.2.1 = p.2.1 := by
          calc
            cellRetractionStep hk (p.1 : ℝ) p.2.1
                = recombine hk (negPart hk p.2.1) ((p.1 : ℝ) • posPart hk p.2.1) := rfl
            _ = recombine hk (negPart hk p.2.1) 0 := by rw [hposz, smul_zero]
            _ = recombine hk (negPart hk p.2.1) (posPart hk p.2.1) := by rw [hposz]
            _ = p.2.1 := recombine_decompose hk p.2.1
        rw [hstep]
        exact ⟨x, hx⟩⟩

theorem cellInclusionStep_mem {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (t : Set.Icc (0 : ℝ) 1) (z : lowerUnion hk c ε) :
    cellRetractionStep hk (t : ℝ) z.1 ∈ lowerCellUnion hk c ε := by
  dsimp [lowerCellUnion]
  rcases z.2 with hz | ⟨x, hx⟩
  · left
    change morseNormalForm hk c (cellRetractionStep hk (t : ℝ) z.1) ≤ c - ε
    rw [cellRetractionStep_level hk c z.1]
    have hz' : morseNormalForm hk c z.1 ≤ c - ε := by simpa [sublevel] using hz
    have hsplit := morseNormalForm_split hk c z.1
    rw [hsplit] at hz'
    have hle : (t : ℝ) ^ 2 ≤ 1 := by nlinarith only [sq_nonneg (t : ℝ), t.2.1, t.2.2]
    nlinarith only [hz', hle, sq_nonneg ‖negPart hk z.1‖,
      sq_nonneg ‖posPart hk z.1‖]
  · right
    have hposz : posPart hk z.1 = 0 := by
      ext j
      rw [← hx]
      dsimp [posPart]
      exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
    have hstep : cellRetractionStep hk (t : ℝ) z.1 = z.1 := by
      calc
        cellRetractionStep hk (t : ℝ) z.1
            = recombine hk (negPart hk z.1) ((t : ℝ) • posPart hk z.1) := rfl
        _ = recombine hk (negPart hk z.1) 0 := by rw [hposz, smul_zero]
        _ = recombine hk (negPart hk z.1) (posPart hk z.1) := by rw [hposz]
        _ = z.1 := recombine_decompose hk z.1
    rw [hstep]
    exact ⟨x, hx⟩

theorem cellInclusionStep_zero {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (z : lowerUnion hk c ε) :
    cellInclusionStepFun hk c ε (⟨0, by norm_num⟩, z) =
      cellAttachmentMap hk c ε hε (cellAttachmentInclusion hk c ε (le_of_lt hε) z) := by
  apply Subtype.ext
  dsimp [cellInclusionStepFun, cellAttachmentMap, cellAttachmentInclusion]
  exact cellRetractionStep_spine hk z.1

theorem cellInclusionStep_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (z : lowerUnion hk c ε) :
    cellInclusionStepFun hk c ε (⟨1, by norm_num⟩, z) = z := by
  apply Subtype.ext
  dsimp [cellInclusionStepFun]
  exact cellRetractionStep_decompose hk z.1

theorem continuous_negPart {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => negPart hk y) := by
  dsimp [negPart]
  have hpi : Continuous (fun y : MorseModel n => (fun i : Fin k => y (negIdx hk i))) :=
    continuous_pi (fun i => continuous_apply (negIdx hk i))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)).comp hpi

theorem continuous_posPart {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => posPart hk y) := by
  dsimp [posPart]
  have hpi : Continuous (fun y : MorseModel n => (fun j : Fin (n - k) => y (posIdx hk j))) :=
    continuous_pi (fun j => continuous_apply (posIdx hk j))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (n - k) => ℝ)).comp hpi

theorem continuous_recombine {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [continuousAt_pi]
  intro i
  by_cases hi : i.val < k
  · have hfun : (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk q.1 q.2 i) = fun q => q.1 ⟨i.val, hi⟩ := by
      funext q
      dsimp [recombine]
      rw [dite_eq_left hi]
    rw [hfun]
    exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)
      ⟨i.val, hi⟩).continuousAt.comp continuous_fst.continuousAt
  · have hproof : i.val - k < n - k := by
      have hkle : k ≤ i.val := le_of_not_gt hi
      have hii : i.val < n := i.isLt
      omega
    have hfun : (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk q.1 q.2 i) = fun q => q.2 ⟨i.val - k, hproof⟩ := by
      funext q
      dsimp [recombine]
      rw [dite_eq_right hi]
    rw [hfun]
    exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin (n - k) => ℝ)
      ⟨i.val - k, hproof⟩).continuousAt.comp continuous_snd.continuousAt

theorem continuous_cellRetractionStep {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      cellRetractionStep hk (p.1 : ℝ) p.2) := by
  dsimp [cellRetractionStep]
  have hneg' : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n => negPart hk p.2) :=
    (continuous_negPart hk).comp continuous_snd
  have hpair1 : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      ((p.1 : ℝ), posPart hk p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_posPart hk).comp continuous_snd)
  have hsmul : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin (n - k)) => p.1 • p.2) :=
    continuous_smul
  have hpos' : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (p.1 : ℝ) • posPart hk p.2) := hsmul.comp hpair1
  have hcomp : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (negPart hk p.2, (p.1 : ℝ) • posPart hk p.2)) := by
    exact hneg'.prodMk hpos'
  exact continuous_recombine hk |>.comp hcomp

theorem continuous_spineMap {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => spineMap hk y) := by
  dsimp [spineMap]
  exact continuous_recombine hk |>.comp ((continuous_negPart hk).prodMk continuous_const)

theorem continuous_cellMap {n k : ℕ} (r : ℝ) :
    Continuous (fun x : ClosedCell k => (cellMap r (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_pi]
  intro i
  by_cases hi : i.val < k
  · have hfun : (fun q : ClosedCell k => cellMap r (q : EuclideanSpace ℝ (Fin k)) i) =
        fun q : ClosedCell k => r * (q : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩ := by
      funext q
      dsimp [cellMap]
      rw [dite_eq_left hi]
    rw [hfun]
    exact ((continuous_const.mul (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)
      ⟨i.val, hi⟩)).comp continuous_subtype_val).continuousAt
  · have hfun : (fun q : ClosedCell k => cellMap r (q : EuclideanSpace ℝ (Fin k)) i) =
      fun _ => 0 := by
      funext q
      dsimp [cellMap]
      rw [dite_eq_right hi]
    rw [hfun]
    exact continuous_const.continuousAt

theorem cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (fun x : ClosedCell k =>
      (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) := by
  intro x y hxy
  apply Subtype.ext
  ext i
  have hx : cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk i) =
      cellMap (Real.sqrt (2 * ε)) (y : EuclideanSpace ℝ (Fin k)) (negIdx hk i) := by
    exact congrFun hxy (negIdx hk i)
  rw [cellMap_negIdx, cellMap_negIdx] at hx
  have hr : Real.sqrt (2 * ε) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by positivity : 0 < 2 * ε)).ne'
  exact mul_left_cancel₀ hr hx

theorem cellInterior_disjoint {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    Disjoint ((fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ''
      Set.range (cellInteriorInclusion k))
      (sublevel (morseNormalForm hk c) (c - ε)) := by
  rw [Set.disjoint_left]
  intro y hyA hyB
  rcases hyA with ⟨x, hx, hxy⟩
  rcases hx with ⟨z, hz⟩
  have hxlt : ‖(x : EuclideanSpace ℝ (Fin k))‖ < 1 := by
    have hzval : (x : EuclideanSpace ℝ (Fin k)) = (z : EuclideanSpace ℝ (Fin k)) := by
      simpa [cellInteriorInclusion] using
        (congrArg (fun w : ClosedCell k => (w : EuclideanSpace ℝ (Fin k))) hz).symm
    rw [hzval]
    exact z.2
  have hf : morseNormalForm hk c y = c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
    rw [← hxy]
    exact morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  have hgt : c - ε < morseNormalForm hk c y := by
    rw [hf, hsq]
    have hxlt2 : ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 < 1 := by
      have habs : |‖(x : EuclideanSpace ℝ (Fin k))‖| < |(1 : ℝ)| := by
        simpa [abs_of_nonneg, abs_one] using hxlt
      simpa using (sq_lt_sq.mpr habs)
    nlinarith only [hxlt2, hε]
  have hle : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hyB
  linarith

theorem isClosed_sublevel_normalForm {n k : ℕ} (hk : k ≤ n) (c a : ℝ) :
    IsClosed (sublevel (morseNormalForm hk c) a) := by
  have hcont : Continuous (morseNormalForm hk c) := by
    rw [show morseNormalForm hk c = fun y => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) by
      funext y
      exact morseNormalForm_split hk c y]
    have hposc : Continuous (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) :=
      (continuous_norm.comp (continuous_posPart hk)).pow 2
    have hnegc : Continuous (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) :=
      (continuous_norm.comp (continuous_negPart hk)).pow 2
    exact (continuous_const.add ((continuous_const.mul (hposc.sub hnegc))))
  exact (isClosed_Iic.preimage hcont)

instance closedCellCompactSpace (k : ℕ) : CompactSpace (ClosedCell k) := by
  let f : ClosedCell k → Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    fun x => ⟨(x : EuclideanSpace ℝ (Fin k)), by simpa [Metric.mem_closedBall, dist_eq_norm] using x.2⟩
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 → ClosedCell k :=
    fun y => ⟨(y : EuclideanSpace ℝ (Fin k)), by
      have hy : ‖(y : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
        have hmem : dist (y : EuclideanSpace ℝ (Fin k)) 0 ≤ 1 := y.2
        simpa [dist_eq_norm] using hmem
      exact hy⟩
  let e : ClosedCell k ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      continuous_toFun := by
        have hcomp : (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k))) =
            fun x : ClosedCell k => (x : EuclideanSpace ℝ (Fin k)) := by
          funext x
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val)
      continuous_invFun := by
        have hcomp : (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k))) =
            fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 => (y : EuclideanSpace ℝ (Fin k)) := by
          funext y
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val) }
  exact e.symm.compactSpace

theorem continuous_cellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    Continuous (cellAttachmentMap hk c ε hε) := by
  have h : Continuous (fun y : upperSublevel hk c ε => spineMap hk y.1) :=
    (continuous_spineMap hk).comp continuous_subtype_val
  have hcomp : (fun y : upperSublevel hk c ε =>
      ((cellAttachmentMap hk c ε hε y : lowerUnion hk c ε) : MorseModel n)) =
      fun y => spineMap hk y.1 := by
    funext y
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun y => (congrFun hcomp y).symm)

theorem continuous_cellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    Continuous (cellAttachmentInclusion hk c ε hε) := by
  have hcomp : (fun z : lowerUnion hk c ε =>
      ((cellAttachmentInclusion hk c ε hε z : upperSublevel hk c ε) : MorseModel n)) =
      fun z : lowerUnion hk c ε => (z : MorseModel n) := by
    funext z
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    ((continuous_subtype_val : Continuous (fun z : lowerUnion hk c ε => (z : MorseModel n))).congr
      fun z => (congrFun hcomp z).symm)

theorem continuous_cellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Continuous (cellRetractionHomotopyFun hk c ε) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      ((cellRetractionHomotopyFun hk c ε p : upperSublevel hk c ε) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun p => (congrFun hcomp p).symm)

theorem continuous_cellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Continuous (cellInclusionStepFun hk c ε) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      ((cellInclusionStepFun hk c ε p : lowerUnion hk c ε) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun p => (congrFun hcomp p).symm)

noncomputable def portPrivate_138057aa_cellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    C(upperSublevel hk c ε, lowerUnion hk c ε) :=
  ⟨cellAttachmentMap hk c ε hε, continuous_cellAttachmentMap hk c ε hε⟩

noncomputable def portPrivate_138057aa_cellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    C(lowerUnion hk c ε, upperSublevel hk c ε) :=
  ⟨cellAttachmentInclusion hk c ε hε, continuous_cellAttachmentInclusion hk c ε hε⟩

noncomputable def cellRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.Homotopy
      ((portPrivate_138057aa_cellAttachmentInclusionC hk c ε (le_of_lt hε)).comp (portPrivate_138057aa_cellAttachmentMapC hk c ε hε))
      (ContinuousMap.id (upperSublevel hk c ε)) where
  toFun := ContinuousMap.mk (cellRetractionHomotopyFun hk c ε) (continuous_cellRetractionHomotopyFun hk c ε)
  map_zero_left := by
    intro y
    exact cellRetractionHomotopy_zero hk c ε hε y
  map_one_left := by
    intro y
    exact cellRetractionHomotopy_one hk c ε y

noncomputable def cellInclusionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.Homotopy
      ((portPrivate_138057aa_cellAttachmentMapC hk c ε hε).comp (portPrivate_138057aa_cellAttachmentInclusionC hk c ε (le_of_lt hε)))
      (ContinuousMap.id (lowerUnion hk c ε)) where
  toFun := ContinuousMap.mk (cellInclusionStepFun hk c ε) (continuous_cellInclusionStepFun hk c ε)
  map_zero_left := by
    intro z
    exact cellInclusionStep_zero hk c ε hε z
  map_one_left := by
    intro z
    exact cellInclusionStep_one hk c ε z

noncomputable def cellAttachmentHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyEquiv (upperSublevel hk c ε) (lowerUnion hk c ε) where
  toFun := portPrivate_138057aa_cellAttachmentMapC hk c ε hε
  invFun := portPrivate_138057aa_cellAttachmentInclusionC hk c ε (le_of_lt hε)
  left_inv := ⟨cellRetractionHomotopy hk c ε hε⟩
  right_inv := ⟨cellInclusionHomotopy hk c ε hε⟩

noncomputable def cellAttachmentAdjunctionHomeo {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    CellAdjunctionSpace k (attachMap hk c ε (le_of_lt hε)) ≃ₜ lowerUnion hk c ε := by
  refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := attachMap hk c ε (le_of_lt hε))
    (c := fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap (Real.sqrt (2 * ε))
  · exact cellInterior_disjoint hk c ε hε
  · exact isClosed_sublevel_normalForm hk c (c - ε)

noncomputable def cellAttachmentModel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyEquiv (upperSublevel hk c ε)
      (CellAdjunctionSpace k (attachMap hk c ε (le_of_lt hε))) :=
  (cellAttachmentHomotopyEquiv hk c ε hε).trans
    (cellAttachmentAdjunctionHomeo hk c ε hε).symm.toHomotopyEquiv

abbrev morseNorm (n : ℕ) (y : MorseModel n) : ℝ :=
  ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖

theorem morseNorm_piNorm_le {n : ℕ} (y : MorseModel n) : ‖y‖ ≤ morseNorm n y := by
  exact (pi_norm_le_iff_of_nonneg (ι := Fin n) (x := y) (r := morseNorm n y)
      (norm_nonneg _)).mpr (by
    intro i
    have h := PiLp.norm_apply_le (p := 2) (x := WithLp.toLp 2 y) i
    simpa [morseNorm] using h)

theorem sum_split_fin {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      (∑ i : Fin k, f (negIdx hk i)) + (∑ j : Fin (n - k), f (posIdx hk j)) := by
  let e : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (negIdx hk) (posIdx hk)
      invFun := fun z => if h : z.val < k then Sum.inl ⟨z.val, h⟩ else Sum.inr ⟨z.val - k, by
        have hkle : k ≤ z.val := le_of_not_gt h
        have hz : z.val < n := z.isLt
        omega⟩
      left_inv := by
        intro s
        cases s with
        | inl i =>
            simp [negIdx]
        | inr j =>
            simp [posIdx]
      right_inv := by
        intro z
        by_cases h : z.val < k
        · simp [h, negIdx]
        · apply Fin.ext
          simp [h, posIdx]
          omega }
  calc
    (∑ i : Fin n, f i) = ∑ s : Sum (Fin k) (Fin (n - k)), f (e s) := by
      symm
      exact Fintype.sum_equiv e (fun s : Sum (Fin k) (Fin (n - k)) => f (e s))
        (fun i : Fin n => f i) (by intro s; rfl)
    _ = (∑ i : Fin k, f (e (Sum.inl i))) + (∑ j : Fin (n - k), f (e (Sum.inr j))) := by
      rw [Fintype.sum_sum_type]
    _ = (∑ i : Fin k, f (negIdx hk i)) + (∑ j : Fin (n - k), f (posIdx hk j)) := by
      simp [e]

theorem portPrivate_138057aa_morseNorm_sq_recombine {n k : ℕ} (hk : k ≤ n)
    (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) :
    morseNorm n (recombine hk a b) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : morseNorm n (recombine hk a b) ^ 2 = ∑ i : Fin n, ((recombine hk a b) i) ^ 2 := by
    simpa [morseNorm] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (recombine hk a b)))
  have h2 : ‖a‖ ^ 2 = ∑ i : Fin k, (a i) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq a)
  have h3 : ‖b‖ ^ 2 = ∑ j : Fin (n - k), (b j) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq b)
  rw [h1, h2, h3]
  rw [sum_split_fin hk (fun i : Fin n => ((recombine hk a b) i) ^ 2)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [recombine_negPart]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [recombine_posPart]

theorem portPrivate_138057aa_morseNorm_le_of_sq_le {n : ℕ} {y z : MorseModel n}
    (h : morseNorm n y ^ 2 ≤ morseNorm n z ^ 2) : morseNorm n y ≤ morseNorm n z := by
  have habs := sq_le_sq.mp h
  have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg (norm_nonneg _)
  have h2 : |morseNorm n z| = morseNorm n z := abs_of_nonneg (norm_nonneg _)
  simpa [h1, h2] using habs

theorem norm_spineMap_le {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    morseNorm n (spineMap hk y) ≤ morseNorm n y := by
  apply portPrivate_138057aa_morseNorm_le_of_sq_le
  rw [show spineMap hk y = recombine hk (negPart hk y) 0 by rfl]
  rw [portPrivate_138057aa_morseNorm_sq_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))]
  conv_rhs => rw [← recombine_decompose hk y]
  rw [portPrivate_138057aa_morseNorm_sq_recombine hk (negPart hk y) (posPart hk y)]
  have hz : ‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by simp
  nlinarith only [sq_nonneg ‖posPart hk y‖, hz]

theorem norm_cellRetractionStep_le {n k : ℕ} (hk : k ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : MorseModel n) : morseNorm n (cellRetractionStep hk t y) ≤ morseNorm n y := by
  apply portPrivate_138057aa_morseNorm_le_of_sq_le
  rw [show cellRetractionStep hk t y = recombine hk (negPart hk y) (t • posPart hk y) by rfl]
  rw [portPrivate_138057aa_morseNorm_sq_recombine hk (negPart hk y) (t • posPart hk y)]
  conv_rhs => rw [← recombine_decompose hk y]
  rw [portPrivate_138057aa_morseNorm_sq_recombine hk (negPart hk y) (posPart hk y)]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [sq_nonneg t, ht0, ht1]
  have hts : ‖t • posPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
    calc
      ‖t • posPart hk y‖ ^ 2 = ‖t‖ ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [norm_smul, mul_pow]
      _ = t ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ 1 * ‖posPart hk y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      _ = ‖posPart hk y‖ ^ 2 := by rw [one_mul]
  nlinarith only [hts]

theorem norm_cellMap_le {n k : ℕ} (hk : k ≤ n) (ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R)
    (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ ≤ 1) : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ≤ R := by
  have hsq : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
    have h1 : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ^ 2 =
        ∑ i : Fin n, ((cellMap (Real.sqrt (2 * ε)) x) i) ^ 2 := by
      simpa [morseNorm] using
        (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (cellMap (Real.sqrt (2 * ε)) x)))
    rw [h1]
    rw [sum_split_fin hk (fun i : Fin n => ((cellMap (Real.sqrt (2 * ε)) x) i) ^ 2)]
    have hneg : (∑ i : Fin k, ((cellMap (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2) ≤
        (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 := by
      calc
        (∑ i : Fin k, ((cellMap (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2)
            = (∑ i : Fin k, (Real.sqrt (2 * ε) * x i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [cellMap_negIdx]
        _ ≤ (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq x]
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          exact le_of_eq (mul_pow (Real.sqrt (2 * ε)) (x i) 2)
    have hpos : (∑ j : Fin (n - k), ((cellMap (Real.sqrt (2 * ε)) x) (posIdx hk j)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [cellMap_posIdx]
      norm_num
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by
      rw [pow_two]
      simpa using (mul_le_mul hx hx (norm_nonneg x) (zero_le_one))
    rw [hpos]
    have hx : (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
      simpa using (mul_le_mul_of_nonneg_left hx2 (sq_nonneg (Real.sqrt (2 * ε))))
    nlinarith only [hneg, hx, hx2]
  have hnorm : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ≤ Real.sqrt (2 * ε) := by
    calc
      morseNorm n (cellMap (Real.sqrt (2 * ε)) x)
          = |morseNorm n (cellMap (Real.sqrt (2 * ε)) x)| := by
            rw [abs_of_nonneg (norm_nonneg _)]
      _ ≤ |Real.sqrt (2 * ε)| := sq_le_sq.mp hsq
      _ = Real.sqrt (2 * ε) := abs_of_nonneg (Real.sqrt_nonneg (2 * ε))
  exact le_trans hnorm hR

theorem morseNorm_sq_eq_negPart_add_posPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
  have h1 : morseNorm n y ^ 2 = ∑ i : Fin n, (y i) ^ 2 := by
    dsimp [morseNorm]
    simpa using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)))
  have h2 : ‖negPart hk y‖ ^ 2 = ∑ i : Fin k, (negPart hk y i) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq (negPart hk y))
  have h3 : ‖posPart hk y‖ ^ 2 = ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq (posPart hk y))
  rw [h1, h2, h3]
  rw [sum_split_fin hk (fun i : Fin n => (y i) ^ 2)]
  have hk_eq : (∑ i : Fin k, (y (negIdx hk i)) ^ 2) = ∑ i : Fin k, (negPart hk y i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hp_eq : (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) =
      ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  rw [hk_eq, hp_eq]

theorem norm_negPart_cellMap {n k : ℕ} (hk : k ≤ n) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    ‖negPart hk (cellMap r u)‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by
  have hsum : (∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2) = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
    calc
      (∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2)
          = ∑ i : Fin k, ((cellMap r u) (negIdx hk i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : Fin k, (r * u i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [cellMap_negIdx]
      _ = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_pow]
  calc
    ‖negPart hk (cellMap r u)‖ ^ 2 = ∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2 := by
      simpa using (EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap r u)))
    _ = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := hsum
    _ = r ^ 2 * ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq u]

theorem negPart_recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    negPart hk (recombine hk a b) = a := by
  ext i
  change recombine hk a b (negIdx hk i) = a i
  exact recombine_negPart hk a b i

theorem posPart_recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    posPart hk (recombine hk a b) = b := by
  ext j
  change recombine hk a b (posIdx hk j) = b j
  exact recombine_posPart hk a b j

theorem recombine_contDiff {n k : ℕ} (hk : k ≤ n) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε) * p.1 ⟨i.val, hi⟩ := by
      funext p
      have hrew : recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i =
          (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) ⟨i.val, hi⟩ := by
        dsimp [recombine]
        rw [dite_eq_left hi]
      rw [hrew]
      exact negPart_cellMap_apply hk (Real.sqrt (2 * ε)) p.1 ⟨i.val, hi⟩
    rw [hcomp]
    fun_prop
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          r * p.2 ⟨i.val - k, by
            have hkle : k ≤ i.val := le_of_not_gt hi
            have hi' : i.val < n := i.isLt
            omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dite_eq_right hi]
    rw [hcomp]
    fun_prop

theorem recombine_contDiff_cocore {n k : ℕ} (hk : k ≤ n) (r ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2) * p.1 ⟨i.val, hi⟩ := by
      funext p
      have hrew : recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1))
            (r • p.2) i = (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1))
            ⟨i.val, hi⟩ := by
        dsimp [recombine]
        rw [dite_eq_left hi]
      rw [hrew]
      exact negPart_cellMap_apply hk (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1 ⟨i.val, hi⟩
    rw [hcomp]
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          2 * ε + r ^ 2 * ‖p.2‖ ^ 2) := by
      have hnorm2 : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
            ‖p.2‖ ^ 2) := (contDiff_norm_sq ℝ).comp contDiff_snd
      exact contDiff_const.add (contDiff_const.mul hnorm2)
    have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) :=
      harg.sqrt (by intro p; positivity)
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          p.1 ⟨i.val, hi⟩) := by
      fun_prop
    exact hsqrt.mul hcoord
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          r * p.2 ⟨i.val - k, by
            have hkle : k ≤ i.val := le_of_not_gt hi
            have hi' : i.val < n := i.isLt
            omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dite_eq_right hi]
    rw [hcomp]
    fun_prop

theorem morseNorm_recombine_sq {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    morseNorm n (recombine hk a b) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [morseNorm_sq_eq_negPart_add_posPart hk (recombine hk a b)]
  rw [negPart_recombine, posPart_recombine]

theorem morseNorm_recombine_cellMap_bound {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℝ (Fin (n - k))) (hv : ‖v‖ ≤ 1) :
    morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ≤
      Real.sqrt (2 * ε + r ^ 2) := by
  have hsq : morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ^ 2 ≤
      2 * ε + r ^ 2 := by
    rw [morseNorm_recombine_sq hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)]
    have h1 : ‖negPart hk (cellMap (Real.sqrt (2 * ε)) u)‖ ^ 2 ≤ 2 * ε := by
      have hnorm := norm_negPart_cellMap hk (Real.sqrt (2 * ε)) u
      rw [hnorm, hu]
      have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
      rw [hsq]
      nlinarith only [sq_nonneg ε]
    have h2 : ‖r • v‖ ^ 2 ≤ r ^ 2 := by
      have hnorm : ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [mul_pow]
        rw [sq_abs]
      rw [hnorm]
      have hv2 : ‖v‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖v‖ := by linarith [norm_nonneg v]
        exact (sq_le_sq' hneg hv).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      nlinarith only [hv2, sq_nonneg r]
    nlinarith
  have hnn : 0 ≤ morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) :=
    norm_nonneg _
  have hns : 0 ≤ Real.sqrt (2 * ε + r ^ 2) := Real.sqrt_nonneg _
  have hsq' : morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ^ 2 ≤
      (Real.sqrt (2 * ε + r ^ 2)) ^ 2 := by
    rwa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2)]
  exact le_of_sq_le_sq hsq' hns

theorem negPart_cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (fun u : CellBoundary k =>
      negPart hk (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)))) := by
  intro u v h
  have hneg : ∀ i : Fin k,
      (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)) (negIdx hk i)) =
        cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k)) (negIdx hk i) := by
    intro i
    exact congrArg (fun w : EuclideanSpace ℝ (Fin k) => w i) h
  have hcore : ∀ i : Fin n,
      (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) i =
        (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) i := by
    intro i
    by_cases hi : i.val < k
    · have hni : negIdx hk ⟨i.val, hi⟩ = i := by
        ext
        rfl
      calc
        (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) i
            = (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) (negIdx hk ⟨i.val, hi⟩) := by
              rw [hni]
        _ = (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) (negIdx hk ⟨i.val, hi⟩) :=
              hneg ⟨i.val, hi⟩
        _ = (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) i := by
              rw [hni]
    · have hpos : ∃ j : Fin (n - k), posIdx hk j = i := by
        refine ⟨⟨i.val - k, by omega⟩, ?_⟩
        dsimp [posIdx]
        apply Fin.ext
        simp
        omega
      rcases hpos with ⟨j, rfl⟩
      simp [cellMap_posIdx]
  have hcellmap : (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)) : MorseModel n) =
      (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k)) : MorseModel n) := by
    funext i
    exact hcore i
  have hu : (⟨u, le_of_eq u.2⟩ : ClosedCell k) = ⟨v, le_of_eq v.2⟩ := by
    exact (cellMap_injective hk ε hε) hcellmap
  apply Subtype.ext
  simpa [cellBoundaryInclusion] using congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k))) hu

theorem recombine_injective {n k : ℕ} (hk : k ≤ n) :
    Function.Injective (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · have hneg := congrArg (negPart hk) h
    simpa [negPart_recombine] using hneg
  · have hpos := congrArg (posPart hk) h
    simpa [posPart_recombine] using hpos

theorem recombine_cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0) :
    Function.Injective (fun p : CellBoundary k × ClosedCell (n - k) =>
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
        (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  intro p q h
  have h1 : (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))),
        r • (p.2 : EuclideanSpace ℝ (Fin (n - k)))) =
      (negPart hk (cellMap (Real.sqrt (2 * ε)) (q.1 : EuclideanSpace ℝ (Fin k))),
        r • (q.2 : EuclideanSpace ℝ (Fin (n - k)))) := by
    exact recombine_injective hk h
  apply Prod.ext
  · exact negPart_cellMap_injective hk ε hε (congrArg Prod.fst h1)
  · have hcocore := congrArg Prod.snd h1
    apply Subtype.ext
    exact (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hcocore

theorem recombine_cellMap_cocore_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    Function.Injective (fun p : CellBoundary k × ClosedCell (n - k) =>
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
          (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  intro p q h
  have hneg : negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k))) =
      negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (q.1 : EuclideanSpace ℝ (Fin k))) := by
    have h' := congrArg (negPart hk) h
    simpa [negPart_recombine] using h'
  have hpos : r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) = r • (q.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    have h' := congrArg (posPart hk) h
    simpa [posPart_recombine] using h'
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (q.2 : EuclideanSpace ℝ (Fin (n - k))) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hpos
  have hrad : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
    rw [hw]
  have hinj : Function.Injective (fun u : CellBoundary k =>
      negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (u : EuclideanSpace ℝ (Fin k)))) := by
    intro u v huv
    apply Subtype.ext
    ext i
    have hc := congrArg (fun w : EuclideanSpace ℝ (Fin k) => w i) huv
    have h1 : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          (u : EuclideanSpace ℝ (Fin k)) i =
        Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          (v : EuclideanSpace ℝ (Fin k)) i := by
      simpa [negPart_cellMap_apply] using hc
    exact (mul_left_cancel₀ (by positivity) h1)
  apply Prod.ext
  · exact hinj (by
      rwa [← hrad] at hneg)
  · apply Subtype.ext
    exact hw

noncomputable def modelFlow {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) ((Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) • posPart hk y)

theorem modelFlow_zero {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    modelFlow hk 0 y = y := by
  dsimp [modelFlow]
  have hsq : Real.sqrt (1 - 2 * 0 / ‖posPart hk y‖ ^ 2) = 1 := by norm_num
  rw [hsq, one_smul]
  exact recombine_decompose hk y

theorem modelFlow_f_sub {n k : ℕ} (hk : k ≤ n) (c t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    morseNormalForm hk c (modelFlow hk t y) = morseNormalForm hk c y - t := by
  let a : EuclideanSpace ℝ (Fin k) := negPart hk y
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hsq : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
    have hb2 : 0 ≤ ‖b‖ ^ 2 := sq_nonneg ‖b‖
    have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
      by_cases hb : ‖b‖ = 0
      · have ht' : t = 0 := by
          rw [hb] at ht
          exact le_antisymm (by simpa using ht) ht0
        rw [ht', hb]
        norm_num
      · have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
        have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hbpos
        rw [div_le_one hb2pos]
        nlinarith only [ht, hb2pos, ht0]
    nlinarith only [hdiv, ht0]
  have hnorm : ‖(Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    rw [Real.sq_sqrt hsq]
    by_cases hb2 : ‖b‖ ^ 2 = 0
    · have ht0' : t = 0 := by
        have hle : t ≤ 0 := by
          rw [hb2] at ht
          simpa using ht
        linarith
      have hb0 : b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
      rw [ht0', hb0]
      simp
    · rw [sub_mul, one_mul]
      rw [div_mul_cancel₀ (2 * t) hb2]
  have hnf : morseNormalForm hk c (modelFlow hk t y) =
      c + (1 / 2) * (-‖a‖ ^ 2 + ‖Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b‖ ^ 2) := by
    dsimp [modelFlow, a, b]
    have hcid : negPart hk (cellMap 1 (negPart hk y)) = negPart hk y := by
      ext i
      rw [negPart_cellMap_apply]
      simp
    have hrec := morseNormalForm_recombine hk c 1 (negPart hk y)
      (Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) • posPart hk y)
    rw [hcid] at hrec
    have h1 : (1 : ℝ) ^ 2 * ‖negPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by ring
    simpa [h1] using hrec
  have hnfy : morseNormalForm hk c y = c + (1 / 2) * (-‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    dsimp [morseNormalForm, a, b]
    congr 1
    rw [show (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -(∑ i : Fin k, (y (negIdx hk i)) ^ 2) by
      rw [Finset.sum_neg_distrib]]
    rw [show (∑ i : Fin k, (y (negIdx hk i)) ^ 2) = ‖negPart hk y‖ ^ 2 by
      rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
      apply Finset.sum_congr rfl
      intro i hi
      change (y (negIdx hk i)) ^ 2 = ((negPart hk y).ofLp i) ^ 2
      rfl]
    rw [show (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) = ‖posPart hk y‖ ^ 2 by
      rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      apply Finset.sum_congr rfl
      intro j hj
      change (y (posIdx hk j)) ^ 2 = ((posPart hk y).ofLp j) ^ 2
      rfl]
  rw [hnf, hnfy, hnorm]
  ring

theorem modelFlow_norm_le {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    morseNorm n (modelFlow hk t y) ≤ morseNorm n y := by
  apply le_of_sq_le_sq
  · let a : EuclideanSpace ℝ (Fin k) := negPart hk y
    let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
    have hsq : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
      have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
        by_cases hb : ‖b‖ = 0
        · have ht' : t = 0 := by
            rw [hb] at ht
            exact le_antisymm (by simpa using ht) ht0
          rw [ht', hb]
          norm_num
        · have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
          have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hbpos
          rw [div_le_one hb2pos]
          nlinarith only [ht, hb2pos, ht0]
      nlinarith only [hdiv, ht0, sq_nonneg ‖b‖]
    have hnorm2 : ‖(Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt hsq]
      by_cases hb2 : ‖b‖ ^ 2 = 0
      · have ht0' : t = 0 := by
          have hle : t ≤ 0 := by
            rw [hb2] at ht
            simpa using ht
          linarith
        have hb0 : b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
        rw [ht0', hb0]
        simp
      · rw [sub_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) hb2]
    have hmain : morseNorm n (modelFlow hk t y) ^ 2 ≤ morseNorm n y ^ 2 := by
      rw [morseNorm_sq_eq_negPart_add_posPart hk (modelFlow hk t y)]
      rw [morseNorm_sq_eq_negPart_add_posPart hk y]
      dsimp [modelFlow]
      rw [negPart_recombine]
      rw [posPart_recombine]
      have hnorm2' : ‖(Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) • posPart hk y)‖ ^ 2 =
          ‖posPart hk y‖ ^ 2 - 2 * t := by
        simpa [a, b] using hnorm2
      nlinarith only [hnorm2', ht0]
    exact hmain
  · exact norm_nonneg _

theorem modelFlow_negPart {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) :
    negPart hk (modelFlow hk t y) = negPart hk y := by
  dsimp [modelFlow]
  rw [negPart_recombine]

theorem modelFlow_posPart {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) :
    posPart hk (modelFlow hk t y) =
      (Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) • posPart hk y := by
  dsimp [modelFlow]
  rw [posPart_recombine]

theorem modelFlow_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t := by
  rw [modelFlow_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  have hsq : 0 ≤ 1 - 2 * t / ‖posPart hk y‖ ^ 2 := by
    have hdiv : 2 * t / ‖posPart hk y‖ ^ 2 ≤ 1 := by
      by_cases hb : ‖posPart hk y‖ = 0
      · have ht' : t = 0 := by
          rw [hb] at ht
          exact le_antisymm (by simpa using ht) ht0
        rw [ht', hb]
        norm_num
      · have hbpos : 0 < ‖posPart hk y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
        have hb2pos : 0 < ‖posPart hk y‖ ^ 2 := sq_pos_of_pos hbpos
        rw [div_le_one hb2pos]
        nlinarith only [ht, hb2pos, ht0]
    nlinarith only [hdiv, ht0]
  rw [Real.sq_sqrt hsq]
  by_cases hb2 : ‖posPart hk y‖ ^ 2 = 0
  · have ht0' : t = 0 := by
      have hle : t ≤ 0 := by
        rw [hb2] at ht
        simpa using ht
      linarith
    have hb0 : posPart hk y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
    rw [ht0', hb0]
    simp
  · rw [sub_mul, one_mul]
    rw [div_mul_cancel₀ (2 * t) hb2]

theorem modelFlow_posPart_norm_sq_neg {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : t ≤ 0) (hp : ‖posPart hk y‖ ≠ 0) :
    ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t := by
  rw [modelFlow_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  have hb2pos : 0 < ‖posPart hk y‖ ^ 2 :=
    sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp))
  have hsq : 0 ≤ 1 - 2 * t / ‖posPart hk y‖ ^ 2 := by
    have hnum : 2 * t ≤ 0 := by
      have hm := mul_nonpos_of_nonpos_of_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 2)
      simpa [mul_comm] using hm
    have hterm : 2 * t / ‖posPart hk y‖ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hb2pos)
    nlinarith
  rw [Real.sq_sqrt hsq]
  rw [sub_mul, one_mul]
  rw [div_mul_cancel₀ (2 * t) (ne_of_gt hb2pos)]

theorem modelFlow_norm_le_of_nonneg {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) :
    morseNorm n (modelFlow hk t y) ≤ morseNorm n y := by
  have hneg : ‖negPart hk (modelFlow hk t y)‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by
    rw [modelFlow_negPart]
  have hpos : ‖posPart hk (modelFlow hk t y)‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
    rw [modelFlow_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    have hsc : (Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) ^ 2 ≤ 1 := by
      have hle : 1 - 2 * t / ‖posPart hk y‖ ^ 2 ≤ 1 := by
        have hnum : 0 ≤ 2 * t := by
          have hm := mul_nonneg ht0 (by norm_num : (0 : ℝ) ≤ 2)
          simpa [mul_comm] using hm
        have hnon : 0 ≤ 2 * t / ‖posPart hk y‖ ^ 2 :=
          div_nonneg hnum (sq_nonneg _)
        nlinarith
      have hs : Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hle
      have hsq : 0 ≤ Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) := Real.sqrt_nonneg _
      have hm : |Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)| ≤ |(1 : ℝ)| := by
        rw [abs_of_nonneg hsq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
        exact hs
      simpa using sq_le_sq.mpr hm
    have hp : 0 ≤ ‖posPart hk y‖ ^ 2 := by positivity
    nlinarith only [hsc, hp]
  apply le_of_sq_le_sq
  · rw [morseNorm_sq_eq_negPart_add_posPart hk (modelFlow hk t y),
      morseNorm_sq_eq_negPart_add_posPart hk y]
    nlinarith only [hneg, hpos]
  · dsimp [morseNorm]
    exact norm_nonneg _

theorem modelFlow_up_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (hy : 0 < ‖posPart hk y‖) :
    ‖posPart hk (modelFlow hk (-t) y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * t := by
  rw [modelFlow_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  have hsq : 0 ≤ 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 := by
    have hb2pos : 0 < ‖posPart hk y‖ ^ 2 := sq_pos_of_pos hy
    have h2t : 0 ≤ 2 * t := by positivity
    have hdiv : 0 ≤ 2 * t / ‖posPart hk y‖ ^ 2 := div_nonneg h2t (le_of_lt hb2pos)
    rw [show 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 = 1 + 2 * t / ‖posPart hk y‖ ^ 2 by ring]
    linarith
  rw [Real.sq_sqrt hsq]
  have hb2 : ‖posPart hk y‖ ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos hy)
  rw [show 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 =
      1 + 2 * t / ‖posPart hk y‖ ^ 2 by ring]
  rw [add_mul, one_mul]
  rw [div_mul_cancel₀ (2 * t) hb2]

theorem modelFlow_f_add {n k : ℕ} (hk : k ≤ n) (c t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (hy : 0 < ‖posPart hk y‖) :
    morseNormalForm hk c (modelFlow hk (-t) y) = morseNormalForm hk c y + t := by
  let a : EuclideanSpace ℝ (Fin k) := negPart hk y
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hnorm : ‖(Real.sqrt (1 - 2 * (-t) / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 + 2 * t := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    have hsq : 0 ≤ 1 - 2 * (-t) / ‖b‖ ^ 2 := by
      have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hy
      have h2t : 0 ≤ 2 * t := by positivity
      have hdiv : 0 ≤ 2 * t / ‖b‖ ^ 2 := div_nonneg h2t (le_of_lt hb2pos)
      rw [show 1 - 2 * (-t) / ‖b‖ ^ 2 = 1 + 2 * t / ‖b‖ ^ 2 by ring]
      linarith
    rw [Real.sq_sqrt hsq]
    rw [show 1 - 2 * (-t) / ‖b‖ ^ 2 = 1 + 2 * t / ‖b‖ ^ 2 by ring]
    have hb2 : ‖b‖ ^ 2 ≠ 0 := by
      exact ne_of_gt (sq_pos_of_pos hy)
    rw [add_mul, one_mul]
    rw [div_mul_cancel₀ (2 * t) hb2]
  have hval : morseNormalForm hk c (modelFlow hk (-t) y) =
      c + (1 / 2) * (-‖a‖ ^ 2 + (‖b‖ ^ 2 + 2 * t)) := by
    have hsplit := morseNormalForm_split hk c (modelFlow hk (-t) y)
    rw [hsplit]
    rw [modelFlow_negPart]
    rw [modelFlow_posPart]
    rw [hnorm]
    ring
  have hfy : morseNormalForm hk c y = c + (1 / 2) * (‖b‖ ^ 2 - ‖a‖ ^ 2) := by
    have hsplit := morseNormalForm_split hk c y
    rw [hsplit]
  rw [hval, hfy]
  ring

theorem modelFlow_rev {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : 2 * t < ‖posPart hk y‖ ^ 2) :
    modelFlow hk (-t) (modelFlow hk t y) = y := by
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hBpos : 0 < ‖b‖ ^ 2 := by
    nlinarith only [ht0, ht, sq_nonneg ‖b‖]
  have hBsubPos : 0 < ‖b‖ ^ 2 - 2 * t := by
    nlinarith only [ht]
  have hnonneg : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
    have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
      rw [div_le_one hBpos]
      nlinarith only [ht]
    nlinarith only [hdiv, ht0]
  have hplus : 0 ≤ 1 + 2 * t / (‖b‖ ^ 2 - 2 * t) := by positivity
  have hsq : (Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hplus]
    rw [Real.sq_sqrt hnonneg]
    have h1 : 1 + 2 * t / (‖b‖ ^ 2 - 2 * t) = ‖b‖ ^ 2 / (‖b‖ ^ 2 - 2 * t) := by
      have hmain : (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) * (‖b‖ ^ 2 - 2 * t) = ‖b‖ ^ 2 := by
        rw [add_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) (ne_of_gt hBsubPos)]
        ring
      exact ((div_eq_iff (ne_of_gt hBsubPos)).mpr hmain.symm).symm
    have h2 : 1 - 2 * t / ‖b‖ ^ 2 = (‖b‖ ^ 2 - 2 * t) / ‖b‖ ^ 2 := by
      have hmain : (1 - 2 * t / ‖b‖ ^ 2) * ‖b‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
        rw [sub_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) (ne_of_gt hBpos)]
      exact ((div_eq_iff (ne_of_gt hBpos)).mpr hmain.symm).symm
    rw [h1, h2]
    field_simp [ne_of_gt hBsubPos, ne_of_gt hBpos]
    have hBnorm : 0 < ‖b‖ :=
      lt_of_le_of_ne (norm_nonneg b) (Ne.symm (sq_pos_iff.mp hBpos))
    exact div_self (ne_of_gt hBnorm)
  have hnonneg' : 0 ≤ Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) := by positivity
  have hscalar : Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) = 1 := by
    have hsq' : (Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
        Real.sqrt (1 - 2 * t / ‖b‖ ^ 2)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith only [hnonneg'])
  calc
    modelFlow hk (-t) (modelFlow hk t y) =
        recombine hk (negPart hk (modelFlow hk (-t) (modelFlow hk t y)))
          (posPart hk (modelFlow hk (-t) (modelFlow hk t y))) :=
      (recombine_decompose hk (modelFlow hk (-t) (modelFlow hk t y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelFlow_negPart, modelFlow_negPart]
      · change posPart hk (modelFlow hk (-t) (modelFlow hk t y)) = b
        rw [modelFlow_posPart]
        rw [modelFlow_posPart_norm_sq hk t y ht0 (by nlinarith only [ht])]
        rw [modelFlow_posPart]
        rw [smul_smul]
        have hrew : 1 - 2 * (-t) / (‖b‖ ^ 2 - 2 * t) =
            1 + 2 * t / (‖b‖ ^ 2 - 2 * t) := by ring
        rw [hrew, hscalar, one_smul]
    _ = y := recombine_decompose hk y

noncomputable def modelFlowField {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : MorseModel n :=
  recombine hk 0 (-(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y)

theorem negPart_modelFlowField {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    negPart hk (modelFlowField hk y) = 0 := by
  dsimp [modelFlowField]
  rw [negPart_recombine]

theorem posPart_modelFlowField {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    posPart hk (modelFlowField hk y) = -(‖posPart hk y‖ ^ 2)⁻¹ • posPart hk y := by
  dsimp [modelFlowField]
  rw [posPart_recombine]

lemma portPrivate_138057aa_scalar_aux {x b : ℝ} (hx : 0 < x) (hb : b ≠ 0) (hs : Real.sqrt x ≠ 0) :
    (1 / (2 * Real.sqrt x) * (-(2 / b))) = -(b * x)⁻¹ * Real.sqrt x := by
  calc
    (1 / (2 * Real.sqrt x) * (-(2 / b))) = -(1 / (Real.sqrt x * b)) := by
      field_simp [hb, hs]
    _ = -(b * x)⁻¹ * Real.sqrt x := by
      field_simp [hb, hs, hx.ne']
      try rw [Real.sq_sqrt hx.le]
      try ring

theorem hasDerivAt_modelFlow_posPart_apply {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (j : Fin (n - k)) (hz : posPart hk (modelFlow hk t y) ≠ 0) :
    HasDerivAt (fun s : ℝ => (Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y j)
      ((-(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ • posPart hk (modelFlow hk t y)) j) t := by
  have hzpos : posPart hk y ≠ 0 := by
    intro hp
    apply hz
    rw [modelFlow_posPart, hp]
    simp
  have hsmul : Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) • posPart hk y ≠ 0 := by
    simpa [modelFlow_posPart] using hz
  have hsqrt_ne : Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) ≠ 0 := by
    intro h
    apply hsmul
    rw [h]
    simp
  have hsqrt_pos : 0 < Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsqrt_ne)
  have harg_pos : 0 < 1 - 2 * t / ‖posPart hk y‖ ^ 2 := Real.sqrt_pos.mp hsqrt_pos
  have harg_ne : 1 - 2 * t / ‖posPart hk y‖ ^ 2 ≠ 0 := ne_of_gt harg_pos
  have hpnz : ‖posPart hk y‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hzpos))
  have hlin : HasDerivAt (fun s : ℝ => 2 * s / ‖posPart hk y‖ ^ 2) (2 / ‖posPart hk y‖ ^ 2) t := by
    have hmul : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      exact (((hasDerivAt_const (c := (2 : ℝ)) t).mul
        (hasDerivAt_id t)).congr_deriv (by ring)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
    simpa using (hmul.div_const (‖posPart hk y‖ ^ 2))
  have hinner : HasDerivAt (fun s : ℝ => 1 - 2 * s / ‖posPart hk y‖ ^ 2)
      (-(2 / ‖posPart hk y‖ ^ 2)) t := by
    exact ((((hasDerivAt_const (c := (1 : ℝ)) t).sub hlin).congr_deriv
      (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl))
  have hderiv_sqrt : HasDerivAt (fun s : ℝ => Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2))
      (1 / (2 * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) * (-(2 / ‖posPart hk y‖ ^ 2))) t := by
    exact ((Real.hasDerivAt_sqrt harg_ne).comp t hinner).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hnorm_flow_sq : ‖posPart hk (modelFlow hk t y)‖ ^ 2 =
      ‖posPart hk y‖ ^ 2 * (1 - 2 * t / ‖posPart hk y‖ ^ 2) := by
    rw [modelFlow_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    rw [Real.sq_sqrt harg_pos.le]
    ring
  have hscalar : (1 / (2 * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) *
        (-(2 / ‖posPart hk y‖ ^ 2))) =
      -(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ *
        Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) := by
    rw [hnorm_flow_sq]
    exact portPrivate_138057aa_scalar_aux harg_pos hpnz hsqrt_ne
  have hmain0 : HasDerivAt (fun s : ℝ =>
      (Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y j)
      ((1 / (2 * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) * (-(2 / ‖posPart hk y‖ ^ 2))) •
        posPart hk y j) t := by
    simpa using (hderiv_sqrt.smul_const (posPart hk y j))
  have hder_eq : (1 / (2 * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) *
        (-(2 / ‖posPart hk y‖ ^ 2))) • posPart hk y j =
      (-(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ • posPart hk (modelFlow hk t y)) j := by
    rw [modelFlow_posPart]
    rw [show (1 / (2 * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) * (-(2 / ‖posPart hk y‖ ^ 2))) =
        -(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ * Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) by
          exact hscalar]
    rw [modelFlow_posPart]
    simp
    ring
  exact hmain0.congr_deriv hder_eq

theorem hasDerivAt_modelFlow {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (hz : posPart hk (modelFlow hk t y) ≠ 0) :
    HasDerivAt (fun s : ℝ => modelFlow hk s y) (modelFlowField hk (modelFlow hk t y)) t := by
  rw [hasDerivAt_pi]
  intro i
  by_cases hi : i.val < k
  · let i' : Fin k := ⟨i.val, hi⟩
    have hi' : i = negIdx hk i' := by
      apply Fin.ext
      rfl
    rw [hi']
    have hconst : ∀ s : ℝ, modelFlow hk s y (negIdx hk i') = negPart hk y i' := by
      intro s
      dsimp [modelFlow]
      exact recombine_negPart hk (negPart hk y)
        ((Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y) i'
    have hfield : modelFlowField hk (modelFlow hk t y) (negIdx hk i') = 0 := by
      change negPart hk (modelFlowField hk (modelFlow hk t y)) i' = 0
      rw [negPart_modelFlowField]
      rfl
    simpa [hconst, hfield] using (hasDerivAt_const (c := negPart hk y i') t)
  · have hge : k ≤ i.val := le_of_not_gt hi
    let j : Fin (n - k) := ⟨i.val - k, by omega⟩
    have hji : i = posIdx hk j := by
      apply Fin.ext
      dsimp [posIdx, j]
      omega
    rw [hji]
    have hconst : ∀ s : ℝ, modelFlow hk s y (posIdx hk j) =
        (Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y j := by
      intro s
      dsimp [modelFlow]
      exact recombine_posPart hk (negPart hk y)
        ((Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y) j
    have hfield : modelFlowField hk (modelFlow hk t y) (posIdx hk j) =
        (-(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ • posPart hk (modelFlow hk t y)) j := by
      change posPart hk (modelFlowField hk (modelFlow hk t y)) j = _
      rw [posPart_modelFlowField]
    have hder : HasDerivAt (fun s : ℝ =>
        (Real.sqrt (1 - 2 * s / ‖posPart hk y‖ ^ 2)) • posPart hk y j)
        ((-(‖posPart hk (modelFlow hk t y)‖ ^ 2)⁻¹ • posPart hk (modelFlow hk t y)) j) t :=
      hasDerivAt_modelFlow_posPart_apply hk t y j hz
    simpa [hconst, hfield] using hder

theorem modelFlow_norm_sq_le_add {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 ≤ ε)
    {t : ℝ} (ht : |t| ≤ 2 * ε) (y : MorseModel n) :
    morseNorm n (modelFlow hk t y) ^ 2 ≤ morseNorm n y ^ 2 + 4 * ε := by
  have hnm := morseNorm_sq_eq_negPart_add_posPart hk (modelFlow hk t y)
  have hnm1 := morseNorm_sq_eq_negPart_add_posPart hk y
  have hneg : ‖negPart hk (modelFlow hk t y)‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by
    rw [modelFlow_negPart]
  have hpos : ‖posPart hk (modelFlow hk t y)‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 4 * ε := by
    by_cases ht0 : 0 ≤ t
    · have hposle : ‖posPart hk (modelFlow hk t y)‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
        rw [modelFlow_posPart]
        rw [norm_smul]
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        rw [mul_pow]
        have hsqrt : Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) ^ 2 ≤ 1 := by
          by_cases harg : 0 ≤ 1 - 2 * t / ‖posPart hk y‖ ^ 2
          · rw [Real.sq_sqrt harg]
            have hle : 1 - 2 * t / ‖posPart hk y‖ ^ 2 ≤ 1 := by
              have h2 : 0 ≤ 2 * t / ‖posPart hk y‖ ^ 2 := by positivity
              nlinarith
            exact hle
          · have hsqrt0 : Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) = 0 :=
              Real.sqrt_eq_zero_of_nonpos (lt_of_not_ge harg).le
            rw [hsqrt0]
            simp
        nlinarith only [hsqrt, sq_nonneg (‖posPart hk y‖ : ℝ)]
      nlinarith only [hposle, hε]
    · have htneg : t < 0 := lt_of_not_ge ht0
      have hposle : ‖posPart hk (modelFlow hk t y)‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 4 * ε := by
        by_cases hpos0 : posPart hk y = 0
        · have hpos' : ‖posPart hk (modelFlow hk t y)‖ ^ 2 = 0 := by
            rw [modelFlow_posPart, hpos0]
            simp
          nlinarith only [hpos', hε]
        · have hpospos : 0 < ‖posPart hk y‖ := norm_pos_iff.mpr hpos0
          have hs : 0 ≤ -t := by linarith
          have hsq : ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * (-t) := by
            simpa using (modelFlow_up_posPart_norm_sq hk (-t) y hs hpospos)
          have ht' : -t ≤ 2 * ε := by
            have habs : |t| = -t := abs_of_neg htneg
            rw [← habs]
            exact ht
          nlinarith only [hsq, ht']
      exact hposle
  nlinarith only [hnm, hnm1, hpos, hneg]


def modelHandleMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) : MorseModel n :=
  recombine hk
    ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
      (p.1 : EuclideanSpace ℝ (Fin k)))
    (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))

theorem negPart_cellMap_smul {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    negPart hk (cellMap ε u) = ε • u := by
  ext i
  rw [negPart_cellMap_apply]
  rfl

theorem modelHandleMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) :
    negPart hk (modelHandleMap hk ε r p) =
      (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)) := by
  dsimp [modelHandleMap]
  rw [negPart_recombine]

theorem modelHandleMap_negPart_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    ‖negPart hk (modelHandleMap hk ε r p)‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
  have h1sq : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
      linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
    exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  have h2sq : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
      linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
    exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  calc
    ‖negPart hk (modelHandleMap hk ε r p)‖ ^ 2
        = (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
            ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
          rw [modelHandleMap_negPart]
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [mul_pow]
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
    _ ≤ (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) * 1 := by
      exact mul_le_mul_of_nonneg_left h1sq (by positivity)
    _ ≤ 2 * ε + r ^ 2 := by
      nlinarith only [h2sq, hε, sq_nonneg r]
    _ = 2 * ε + r ^ 2 := rfl

theorem modelHandleMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) :
    posPart hk (modelHandleMap hk ε r p) =
      r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) := by
  dsimp [modelHandleMap]
  rw [posPart_recombine]

theorem modelHandleMap_f_value {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) =
      c + (1 / 2) *
        (-((2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
            ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) +
          r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
  dsimp [modelHandleMap]
  rw [← negPart_cellMap_smul hk]
  have hrec := morseNormalForm_recombine hk c
    (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
    (p.1 : EuclideanSpace ℝ (Fin k)) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))
  rw [hrec]
  have hsq : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) ^ 2 =
      2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
  have hnorm : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
      r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  rw [hsq, hnorm]
  ring

theorem modelHandleMap_f_sub {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) - (c - ε) =
      (1 / 2) * (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        (1 - ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
  have hval := modelHandleMap_f_value hk c ε r hε p
  rw [hval]
  ring

theorem modelHandleMap_f_ge {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    c - ε ≤ morseNormalForm hk c (modelHandleMap hk ε r p) := by
  rw [← sub_nonneg]
  rw [modelHandleMap_f_sub hk c ε r hε]
  have hnonneg : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by positivity
  have hle : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
      linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
    exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  nlinarith only [hnonneg, hle]

theorem modelHandleMap_f_le {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c + r ^ 2 / 2 := by
  rw [modelHandleMap_f_value hk c ε r hε p]
  have hx : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := sq_nonneg _
  have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
      linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
    exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  have hnonneg : 0 ≤ (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by positivity
  have hwle : r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 := by
    simpa using (mul_le_mul_of_nonneg_left hw (sq_nonneg r))
  nlinarith only [hnonneg, hwle]

theorem modelHandleMap_f_eq_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  rw [← sub_eq_zero]
  rw [modelHandleMap_f_sub hk c ε r (le_of_lt hε)]
  constructor
  · intro h
    have hmain : (1 / 2 : ℝ) * (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) ≠ 0 := by
      positivity
    have hzero : 1 - ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hmain
    have hsq : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hsq with h1 | h2
    · exact h1
    · linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
  · intro h
    rw [h]
    ring

theorem modelHandleMap_f_boundary {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 ≤ ε) (u : CellBoundary k) (w : ClosedCell (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r (cellBoundaryInclusion k u, w)) = c - ε := by
  rw [modelHandleMap_f_value hk c ε r hε]
  simp only [cellBoundaryInclusion]
  rw [u.2]
  ring

theorem modelHandleMap_norm_le {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNorm n (modelHandleMap hk ε r p) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) := by
  apply le_of_sq_le_sq
  · change morseNorm n (recombine hk
      ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))
      (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) ^ 2 ≤
      (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2
    rw [morseNorm_recombine_sq hk
      ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))
      (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))]
    have h1 : ‖((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
      have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
          linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
        exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
          linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
        exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hcore : (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
          2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        simpa using mul_le_mul_of_nonneg_left hx
          (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
      have hA : 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
        nlinarith only [hw, sq_nonneg r]
      exact le_trans hcore hA
    have h2 : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
          linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
        exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      nlinarith only [hw]
    have hR2 : 2 * ε + 2 * r ^ 2 ≤ (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)]
    nlinarith only [h1, h2, hR2]
  · exact Real.sqrt_nonneg _

theorem modelHandleMap_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    Function.Injective (modelHandleMap hk ε r) := by
  intro p q h
  have hneg := congrArg (negPart hk) h
  have hpos := congrArg (posPart hk) h
  simp only [modelHandleMap_negPart, modelHandleMap_posPart] at hneg hpos
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (q.2 : EuclideanSpace ℝ (Fin (n - k))) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hpos
  have hscale : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
    rw [hw]
  have hneg' : (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)) =
      (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (q.1 : EuclideanSpace ℝ (Fin k)) := by
    simpa [hscale] using hneg
  have hu : (p.1 : EuclideanSpace ℝ (Fin k)) = (q.1 : EuclideanSpace ℝ (Fin k)) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin k))
      (r := Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) (by positivity))
      hneg'
  apply Prod.ext
  · apply Subtype.ext
    exact hu
  · apply Subtype.ext
    exact hw

theorem modelHandleMap_attachingRegion {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (u : CellBoundary k) (w : ClosedCell (n - k)) :
    modelHandleMap hk ε r (cellBoundaryInclusion k u, w) =
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (u : EuclideanSpace ℝ (Fin k)))) (r • (w : EuclideanSpace ℝ (Fin (n - k)))) := by
  dsimp [modelHandleMap, cellBoundaryInclusion]
  rw [negPart_cellMap_smul]

def modelHandle {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) : Set (MorseModel n) :=
  {y : MorseModel n | ‖posPart hk y‖ ^ 2 ≤ r ^ 2 ∧
    ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 2 * ε}

theorem modelFlow_mem_handle_of_up_le {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {z : MorseModel n} (hz : morseNormalForm hk c z = c - ε)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2)
    (hzpos : 0 < ‖posPart hk z‖) :
    modelFlow hk (-L) z ∈ modelHandle hk ε r := by
  dsimp [modelHandle]
  have hnorm : ‖posPart hk (modelFlow hk (-L) z)‖ ^ 2 = ‖posPart hk z‖ ^ 2 + 2 * L :=
    modelFlow_up_posPart_norm_sq hk L z hL0 hzpos
  have hneg : ‖negPart hk (modelFlow hk (-L) z)‖ ^ 2 = ‖negPart hk z‖ ^ 2 := by
    rw [modelFlow_negPart]
  have hzsplit := morseNormalForm_split hk c z
  have hnegeq : ‖negPart hk z‖ ^ 2 = ‖posPart hk z‖ ^ 2 + 2 * ε := by
    nlinarith only [hzsplit, hz]
  constructor
  · nlinarith only [hnorm, hL]
  · nlinarith only [hneg, hnorm, hnegeq, hL0]


theorem modelHandleMap_mem {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ modelHandle hk ε r := by
  dsimp [modelHandle]
  constructor
  · rw [modelHandleMap_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
    have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
        linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
      exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    nlinarith only [hw]
  · rw [modelHandleMap_posPart, modelHandleMap_negPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
    have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
        linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
      exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
        linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
      exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hcore : (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
        2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hx
        (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
    nlinarith only [hcore]

theorem mem_modelHandle {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0)
    (y : MorseModel n) :
    y ∈ modelHandle hk ε r ↔
      ∃ p : StandardHandle k (n - k), modelHandleMap hk ε r p = y := by
  constructor
  · intro hy
    dsimp [modelHandle] at hy
    rcases hy with ⟨hb, ha⟩
    let a : EuclideanSpace ℝ (Fin k) := negPart hk y
    let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
    have hscale : 0 < Real.sqrt (2 * ε + ‖b‖ ^ 2) := by
      have hpos : 0 < 2 * ε + ‖b‖ ^ 2 := by positivity
      exact Real.sqrt_pos.2 hpos
    let x : EuclideanSpace ℝ (Fin k) := (Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ • a
    have hx' : ‖x‖ ^ 2 ≤ 1 := by
      dsimp [x]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      rw [inv_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + ‖b‖ ^ 2)]
      rw [mul_comm]
      rw [← div_eq_mul_inv]
      rw [div_le_one (by positivity : 0 < 2 * ε + ‖b‖ ^ 2)]
      nlinarith only [ha]
    have hxle : ‖x‖ ≤ 1 := by
      exact le_of_sq_le_sq (by simpa using hx') (by norm_num)
    let w : EuclideanSpace ℝ (Fin (n - k)) := r⁻¹ • b
    have hw' : ‖w‖ ^ 2 ≤ 1 := by
      dsimp [w]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      rw [inv_pow]
      rw [mul_comm]
      rw [← div_eq_mul_inv]
      rw [div_le_one (sq_pos_of_ne_zero hr)]
      exact hb
    have hwle : ‖w‖ ≤ 1 := by
      exact le_of_sq_le_sq (by simpa using hw') (by norm_num)
    have hw2 : r ^ 2 * ‖w‖ ^ 2 = ‖b‖ ^ 2 := by
      dsimp [w]
      calc
        r ^ 2 * ‖(r⁻¹ • b : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
            r ^ 2 * ((r⁻¹) ^ 2 * ‖b‖ ^ 2) := by
              rw [norm_smul]
              rw [Real.norm_eq_abs]
              rw [mul_pow]
              rw [sq_abs]
        _ = (r ^ 2 * (r ^ 2)⁻¹) * ‖b‖ ^ 2 := by
          rw [inv_pow]
          ring
        _ = ‖b‖ ^ 2 := by
          rw [mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
    have hcore_eq : Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) =
        Real.sqrt (2 * ε + ‖b‖ ^ 2) := by
      rw [hw2]
    have hcore_scale : Real.sqrt (2 * ε + ‖b‖ ^ 2) *
        (Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hscale)
    have hsmul1 : (Real.sqrt (2 * ε + ‖b‖ ^ 2)) •
        ((Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ • a) = a := by
      rw [smul_smul]
      rw [hcore_scale, one_smul]
    have hsmul2 : r • (r⁻¹ • b) = b := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ hr, one_smul]
    refine ⟨(⟨x, hxle⟩, ⟨w, hwle⟩), ?_⟩
    dsimp [modelHandleMap, x, w]
    rw [hcore_eq]
    rw [hsmul1, hsmul2]
    change recombine hk (negPart hk y) (posPart hk y) = y
    exact recombine_decompose hk y
  · intro hp
    rcases hp with ⟨p, rfl⟩
    exact modelHandleMap_mem hk ε r (le_of_lt hε) p

noncomputable def modelLowerAttachingChartPoint {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    (Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) • ((‖posPart hk y‖)⁻¹ • posPart hk y))

theorem modelLowerAttachingChartPoint_negPart {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (y : MorseModel n) :
    negPart hk (modelLowerAttachingChartPoint hk ε y) = negPart hk y := by
  dsimp [modelLowerAttachingChartPoint]
  rw [negPart_recombine]

theorem modelLowerAttachingChartPoint_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    {y : MorseModel n} (hpos : posPart hk y ≠ 0)
    (hε : ‖negPart hk y‖ ^ 2 - 2 * ε ≥ 0) :
    ‖posPart hk (modelLowerAttachingChartPoint hk ε y)‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε := by
  dsimp [modelLowerAttachingChartPoint]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt hε]
  have hnorm : ‖((‖posPart hk y‖)⁻¹ • posPart hk y : EuclideanSpace ℝ (Fin (n - k)))‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpos)]
  rw [hnorm]
  ring

theorem modelLowerAttachingChartPoint_fix {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    {y : MorseModel n} (hpos : posPart hk y ≠ 0)
    (hfix : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε) :
    modelLowerAttachingChartPoint hk ε y = y := by
  dsimp [modelLowerAttachingChartPoint]
  rw [← recombine_decompose hk y]
  simp only [negPart_recombine, posPart_recombine]
  have hsqrt : Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) = ‖posPart hk y‖ := by
    rw [← hfix]
    exact Real.sqrt_sq_eq_abs (‖posPart hk y‖) |>.trans (abs_of_nonneg (norm_nonneg _))
  have hsmul' : Real.sqrt (‖negPart hk y‖ ^ 2 - 2 * ε) •
      ((‖posPart hk y‖)⁻¹ • posPart hk y) = posPart hk y := by
    rw [hsqrt]
    rw [smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hpos)]
    rw [one_smul]
  rw [hsmul']


theorem modelLowerAttachingChartPoint_mem_modelHandle_sublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r : ℝ) (hε : 0 ≤ ε) {y : MorseModel n} (hpos : posPart hk y ≠ 0)
    (hneg : ‖negPart hk y‖ ≤ r) (hlo : 2 * ε ≤ ‖negPart hk y‖ ^ 2) :
    modelLowerAttachingChartPoint hk ε y ∈ modelHandle hk ε r ∧
      morseNormalForm hk c (modelLowerAttachingChartPoint hk ε y) ≤ c - ε := by
  let z := modelLowerAttachingChartPoint hk ε y
  have hε' : 0 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by linarith
  have hpnorm : ‖posPart hk z‖ ^ 2 = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [z]
    exact modelLowerAttachingChartPoint_posPart_norm_sq hk ε hpos hε'
  have hn : negPart hk z = negPart hk y := by
    dsimp [z]
    exact modelLowerAttachingChartPoint_negPart hk ε y
  constructor
  · dsimp [modelHandle]
    constructor
    · rw [hpnorm]
      have hle : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 := by
        exact sq_le_sq' (by linarith [norm_nonneg (negPart hk y)]) hneg
      nlinarith only [hε, hle]
    · rw [hn, hpnorm]
      nlinarith
  · rw [morseNormalForm_split hk c z, hn, hpnorm]
    nlinarith


theorem modelHandle_meets_lower_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    modelHandle hk ε r ∩ sublevel (morseNormalForm hk c) (c - ε) =
      Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
        modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyh, hyl⟩
    have hmem := (mem_modelHandle hk ε r hε hr y).1 hyh
    rcases hmem with ⟨p, hp⟩
    have hf : morseNormalForm hk c y = c - ε := by
      apply le_antisymm
      · change y ∈ sublevel (morseNormalForm hk c) (c - ε)
        exact hyl
      · rw [← hp]
        exact modelHandleMap_f_ge hk c ε r (le_of_lt hε) p
    have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      have hpf := modelHandleMap_f_eq_lower_iff hk c ε r hε p
      exact hpf.1 (by simpa [hp] using hf)
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hx⟩, p.2), ?_⟩
    have hpi : (cellBoundaryInclusion k ⟨(p.1 : EuclideanSpace ℝ (Fin k)), hx⟩ : ClosedCell k) = p.1 := by
      apply Subtype.ext
      rfl
    simpa [hpi] using hp
  · intro hy
    rcases hy with ⟨p, hp⟩
    constructor
    · rw [← hp]
      exact modelHandleMap_mem hk ε r (le_of_lt hε) (cellBoundaryInclusion k p.1, p.2)
    · rw [← hp]
      change morseNormalForm hk c (modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) ≤ c - ε
      rw [modelHandleMap_f_boundary hk c ε r (le_of_lt hε) p.1 p.2]

theorem modelFlow_modelHandle_mem_attachingRegion {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 < ε) (hr : r ≠ 0) (y : MorseModel n) (hy : y ∈ modelHandle hk ε r)
    (hflow : morseNormalForm hk c y - (c - ε) ≤ ‖posPart hk y‖ ^ 2 / 2) :
    modelFlow hk (morseNormalForm hk c y - (c - ε)) y ∈
      modelHandle hk ε r ∩ sublevel (morseNormalForm hk c) (c - ε) := by
  let t : ℝ := morseNormalForm hk c y - (c - ε)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rcases (mem_modelHandle hk ε r hε hr y).1 hy with ⟨p, hp⟩
    rw [← hp]
    rw [← sub_nonneg]
    rw [modelHandleMap_f_sub hk c ε r (le_of_lt hε) p]
    have hnonneg : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by positivity
    have hle : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
        linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
      exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    nlinarith only [hnonneg, hle]
  have hf : morseNormalForm hk c (modelFlow hk t y) = c - ε := by
    rw [modelFlow_f_sub hk c t y ht0 hflow]
    dsimp [t]
    ring
  constructor
  · rcases hy with ⟨hb, ha⟩
    dsimp [modelHandle]
    rw [modelFlow_negPart]
    have hpos := modelFlow_posPart_norm_sq hk t y ht0 hflow
    rw [hpos]
    constructor
    · nlinarith only [hb, ht0]
    · have hmain : ‖negPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t + 2 * ε := by
        dsimp [t]
        have hsplit := morseNormalForm_split hk c y
        rw [hsplit]
        ring
      rw [hmain]
  · change morseNormalForm hk c (modelFlow hk t y) ≤ c - ε
    rw [hf]

noncomputable def smoothCap (ε r δ : ℝ) (t : ℝ) : ℝ :=
  r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))

theorem smoothCap_contDiff (ε r δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothCap ε r δ) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
        ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) := by
    fun_prop
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
      ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)))
  exact hcomp

theorem smoothCap_lower {ε r δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ r ^ 2 + 2 * ε - δ) :
    smoothCap ε r δ t = r ^ 2 := by
  dsimp [smoothCap]
  have harg : (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) ≤ 0 := by
    have hden : 0 < 2 * δ := by positivity
    exact (div_le_iff₀ hden).2 (by nlinarith only [ht])
  rw [Real.smoothTransition.zero_of_nonpos harg]
  simp

theorem smoothCap_upper {ε r δ t : ℝ} (hδ : 0 < δ) (ht : r ^ 2 + 2 * ε + δ ≤ t) :
    smoothCap ε r δ t = t - 2 * ε := by
  dsimp [smoothCap]
  have harg : 1 ≤ (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) := by
    have hden : 0 < 2 * δ := by positivity
    exact (le_div_iff₀ hden).2 (by nlinarith only [ht])
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

theorem smoothCap_pos {ε r δ t : ℝ} (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    0 < smoothCap ε r δ t := by
  by_cases ht₁ : t ≤ r ^ 2 + 2 * ε - δ
  · rw [smoothCap_lower hδ0 ht₁]
    nlinarith
  · by_cases ht₂ : r ^ 2 + 2 * ε + δ ≤ t
    · rw [smoothCap_upper hδ0 ht₂]
      nlinarith only [hδ0, hδr, ht₂]
    · have hmid : r ^ 2 + 2 * ε - δ < t ∧ t < r ^ 2 + 2 * ε + δ := by
        constructor <;> linarith
      dsimp [smoothCap]
      have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
        Real.smoothTransition.nonneg _
      have hτle : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
        Real.smoothTransition.le_one _
      have hneg : r ^ 2 + 2 * ε - δ - 2 * ε - r ^ 2 ≤ t - 2 * ε - r ^ 2 := by
        nlinarith only [hmid.1]
      have hlo : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
          ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≥ r ^ 2 - δ := by
        have hdelta : t - 2 * ε - r ^ 2 ≥ -δ := by
          nlinarith only [hmid.1]
        by_cases hsign : t - 2 * ε - r ^ 2 ≤ 0
        · have hprod : (t - 2 * ε - r ^ 2) * Real.smoothTransition
              ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≥
              t - 2 * ε - r ^ 2 := by
            simpa using mul_le_mul_of_nonpos_left hτle hsign
          nlinarith only [hprod, hdelta]
        · have hprod : 0 ≤ (t - 2 * ε - r ^ 2) * Real.smoothTransition
              ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
            mul_nonneg (le_of_lt (lt_of_not_ge hsign)) hτ
          nlinarith only [hδ0, hprod]
      nlinarith only [hlo, hδr]

theorem smoothCap_le_max {ε r δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    smoothCap ε r δ t ≤ max (r ^ 2) t := by
  by_cases ht₁ : t ≤ r ^ 2 + 2 * ε - δ
  · rw [smoothCap_lower hδ ht₁]
    exact le_max_left (r ^ 2) t
  · by_cases ht₂ : r ^ 2 + 2 * ε + δ ≤ t
    · rw [smoothCap_upper hδ ht₂]
      exact le_trans (by nlinarith only [hε]) (le_max_right (r ^ 2) t)
    · have hmid : r ^ 2 + 2 * ε - δ < t ∧ t < r ^ 2 + 2 * ε + δ := by
        constructor <;> linarith
      dsimp [smoothCap]
      have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
        Real.smoothTransition.nonneg _
      have hτle : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
        Real.smoothTransition.le_one _
      by_cases hsign : t - 2 * ε - r ^ 2 ≤ 0
      · have hle : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
            ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ r ^ 2 := by
          nlinarith only [hτ, hsign]
        exact le_trans hle (le_max_left (r ^ 2) t)
      · have hle : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
            ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ t - 2 * ε := by
          nlinarith only [hτle, hsign]
        exact le_trans (le_trans hle (by nlinarith only [hε])) (le_max_right (r ^ 2) t)

theorem portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap {ε r δ t : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδr : δ < r ^ 2) (ht : 0 ≤ t) :
    1 ≤ Real.sqrt ((t + r ^ 2) / smoothCap ε r δ t) := by
  have hsc : 0 < smoothCap ε r δ t := smoothCap_pos hδ hδr
  have hmax : max (r ^ 2) t ≤ t + r ^ 2 := by
    rw [max_le_iff]
    exact ⟨le_add_of_nonneg_left ht, le_add_of_nonneg_right (sq_nonneg r)⟩
  have hle : smoothCap ε r δ t ≤ t + r ^ 2 :=
    le_trans (smoothCap_le_max hε hδ) hmax
  exact (Real.le_sqrt zero_le_one (div_nonneg (add_nonneg ht (sq_nonneg r)) hsc.le)).2 (by
    norm_num
    rw [one_le_div hsc]
    exact hle)

noncomputable def modelAttachedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) (y : MorseModel n) : ℝ :=
  c + (1 / 2) * (‖posPart hk y‖ ^ (2 : ℕ) - smoothCap ε r δ (‖negPart hk y‖ ^ (2 : ℕ)))

noncomputable def modelAttachedRegion {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) : Set (MorseModel n) :=
  {y : MorseModel n | ‖posPart hk y‖ ^ (2 : ℕ) ≤ smoothCap ε r δ (‖negPart hk y‖ ^ (2 : ℕ))}

theorem modelAttachedRegion_eq_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) :
    modelAttachedRegion hk ε r δ = sublevel (modelAttachedFunction hk c ε r δ) c := by
  ext y
  change ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) ↔
    c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) ≤ c
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem modelAttachedRegion_iff_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) (y : MorseModel n) :
    y ∈ modelAttachedRegion hk ε r δ ↔ modelAttachedFunction hk c ε r δ y ≤ c := by
  have heq : (y ∈ modelAttachedRegion hk ε r δ) =
      (y ∈ sublevel (modelAttachedFunction hk c ε r δ) c) :=
    congrArg (fun s : Set (MorseModel n) => y ∈ s)
      (modelAttachedRegion_eq_sublevel hk c ε r δ)
  rw [show (y ∈ sublevel (modelAttachedFunction hk c ε r δ) c) =
      (modelAttachedFunction hk c ε r δ y ≤ c) from rfl] at heq
  exact Iff.of_eq heq

theorem morseNormalForm_le_upper_of_mem_attachedRegion {n k : ℕ} (hk : k ≤ n)
    (c ε r δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNormalForm hk c y ≤ c + r ^ 2 / 2 := by
  have hsc := smoothCap_le_max (ε := ε) (r := r) (δ := δ)
    (t := ‖negPart hk y‖ ^ 2) hε hδ
  have hpos : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    simpa [modelAttachedRegion] using hy
  have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [max_le_iff]
    constructor <;> nlinarith only [sq_nonneg ‖negPart hk y‖]
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    nlinarith only [hpos, hsc, hmax]
  have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
    morseNormalForm_split hk c y
  rw [hf]
  nlinarith only [hle]

theorem contDiff_modelAttachedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedFunction hk c ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hnormPos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hmain : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2))) := by
    exact (contDiff_const.add ((contDiff_const.mul (hnormPos.sub hcap))))
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)))
  exact hmain

theorem smoothCap_nonneg {ε r δ t : ℝ} (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    0 ≤ smoothCap ε r δ t :=
  le_of_lt (smoothCap_pos hδ0 hδr)

noncomputable def modelAttachedStretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2))) •
      posPart hk y)

noncomputable def modelAttachedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) •
      posPart hk y)

theorem modelAttachedStretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelAttachedStretch hk ε r δ y) = negPart hk y := by
  dsimp [modelAttachedStretch]
  rw [negPart_recombine]

theorem modelAttachedStretch_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelAttachedStretch hk ε r δ y) =
      (Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2))) •
        posPart hk y := by
  dsimp [modelAttachedStretch]
  rw [posPart_recombine]

theorem modelAttachedStretch_negPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) := by
  have hne : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ = ‖negPart hk y‖ := by
    exact congrArg (norm : EuclideanSpace ℝ (Fin k) → ℝ)
      (modelAttachedStretch_negPart hk ε r δ y)
  simp [hne]

theorem modelAttachedUnstretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelAttachedUnstretch hk ε r δ y) = negPart hk y := by
  dsimp [modelAttachedUnstretch]
  rw [negPart_recombine]

theorem modelAttachedUnstretch_negPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) := by
  have hne : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ = ‖negPart hk y‖ := by
    exact congrArg (norm : EuclideanSpace ℝ (Fin k) → ℝ)
      (modelAttachedUnstretch_negPart hk ε r δ y)
  simp [hne]

theorem modelAttachedUnstretch_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelAttachedUnstretch hk ε r δ y) =
      (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) •
        posPart hk y := by
  dsimp [modelAttachedUnstretch]
  rw [posPart_recombine]

theorem modelAttachedStretch_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 := by
  rw [modelAttachedStretch_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (div_nonneg (smoothCap_nonneg hδ0 hδr)
    (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2))]

theorem modelAttachedUnstretch_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := by
  rw [modelAttachedUnstretch_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2)
    (smoothCap_nonneg hδ0 hδr))]

theorem modelAttachedStretch_mem {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (y : MorseModel n) (hy : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2) :
    modelAttachedStretch hk ε r δ y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  have hneg' : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) :=
    modelAttachedStretch_negPart_norm_sq hk ε r δ y
  have hden : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact div_nonneg (smoothCap_nonneg hδ0 hδr) (le_of_lt hden)
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hle' : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2 ≤
        (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) :=
      mul_le_mul_of_nonneg_left hy hnonneg
    rwa [div_mul_cancel₀ (smoothCap ε r δ (‖negPart hk y‖ ^ 2)) (ne_of_gt hden)] at hle'
  calc
    ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2
        = (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            ‖posPart hk y‖ ^ 2 :=
      modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y
    _ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hmain
    _ = smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) :=
      congrArg (smoothCap ε r δ) hneg'.symm

theorem modelAttachedUnstretch_mem {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ0 : 0 < δ)
    (hδr : δ < r ^ 2) (y : MorseModel n) (hy : y ∈ modelAttachedRegion hk ε r δ) :
    ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
  dsimp [modelAttachedRegion] at hy
  have hnorm := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  rw [hnorm]
  have hs : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hnonneg : 0 ≤ (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    exact div_nonneg (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2) (le_of_lt hs)
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hle' : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2 ≤
        ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hy hnonneg
    rwa [div_mul_cancel₀ (‖negPart hk y‖ ^ 2 + r ^ 2) (ne_of_gt hs)] at hle'
  exact hmain

theorem modelAttachedUnstretch_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNorm n (modelAttachedUnstretch hk ε r δ y) ^ 2 ≤
      2 * ‖negPart hk y‖ ^ 2 + r ^ 2 := by
  have hneg := modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
  have hmem := modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
  have hnorm := morseNorm_sq_eq_negPart_add_posPart hk (modelAttachedUnstretch hk ε r δ y)
  rw [hnorm, hneg]
  nlinarith only [hmem]

theorem modelAttachedUnstretch_stretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) = y := by
  let s : ℝ := smoothCap ε r δ (‖negPart hk y‖ ^ 2)
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hs : 0 < s := by
    dsimp [s]
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have ht : 0 < t + r ^ 2 := by
    dsimp [t]
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg1 : 0 ≤ s / (t + r ^ 2) := div_nonneg (le_of_lt hs) (le_of_lt ht)
  have hnonneg2 : 0 ≤ (t + r ^ 2) / s := div_nonneg (le_of_lt ht) (le_of_lt hs)
  have hsq : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hnonneg1]
    rw [Real.sq_sqrt hnonneg2]
    field_simp [ne_of_gt hs, ne_of_gt ht]
  have hnonneg' : 0 ≤ Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) := by positivity
  have hscalar : Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) = 1 := by
    have hsq' : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith only [hnonneg'])
  calc
    modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) =
        recombine hk (negPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y)))
          (posPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y))) :=
      (recombine_decompose hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · simp [modelAttachedUnstretch_negPart, modelAttachedStretch_negPart]
      · have hneg : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 = t := by
          dsimp [t]
          exact modelAttachedStretch_negPart_norm_sq hk ε r δ y
        have hpos1 : posPart hk (modelAttachedStretch hk ε r δ y) =
            Real.sqrt (s / (t + r ^ 2)) • posPart hk y := by
          dsimp [s, t]
          exact modelAttachedStretch_posPart hk ε r δ y
        have hpos2 : posPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y)) =
            Real.sqrt ((t + r ^ 2) / s) • posPart hk (modelAttachedStretch hk ε r δ y) := by
          dsimp [s, t]
          rw [modelAttachedUnstretch_posPart]
          rw [hneg]
        rw [hpos2, hpos1, smul_smul, mul_comm, hscalar, one_smul]
    _ = y := recombine_decompose hk y

theorem modelAttachedStretch_unstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) = y := by
  let s : ℝ := smoothCap ε r δ (‖negPart hk y‖ ^ 2)
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hs : 0 < s := by
    dsimp [s]
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have ht : 0 < t + r ^ 2 := by
    dsimp [t]
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg1 : 0 ≤ s / (t + r ^ 2) := div_nonneg (le_of_lt hs) (le_of_lt ht)
  have hnonneg2 : 0 ≤ (t + r ^ 2) / s := div_nonneg (le_of_lt ht) (le_of_lt hs)
  have hsq : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hnonneg1]
    rw [Real.sq_sqrt hnonneg2]
    field_simp [ne_of_gt hs, ne_of_gt ht]
  have hnonneg' : 0 ≤ Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) := by positivity
  have hscalar : Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) = 1 := by
    have hsq' : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith only [hnonneg'])
  calc
    modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) =
        recombine hk (negPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y)))
          (posPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y))) :=
      (recombine_decompose hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · simp [modelAttachedStretch_negPart, modelAttachedUnstretch_negPart]
      · have hneg : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 = t := by
          dsimp [t]
          exact modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
        have hpos1 : posPart hk (modelAttachedUnstretch hk ε r δ y) =
            Real.sqrt ((t + r ^ 2) / s) • posPart hk y := by
          dsimp [s, t]
          exact modelAttachedUnstretch_posPart hk ε r δ y
        have hpos2 : posPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y)) =
            Real.sqrt (s / (t + r ^ 2)) • posPart hk (modelAttachedUnstretch hk ε r δ y) := by
          dsimp [s, t]
          rw [modelAttachedStretch_posPart]
          rw [hneg]
        rw [hpos2, hpos1, smul_smul, hscalar, one_smul]
    _ = y := recombine_decompose hk y

theorem contDiff_modelAttachedStretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedStretch hk ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hden_pos : ∀ y : MorseModel n, 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    intro y
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) :=
    hcap.div hden (by intro y; exact ne_of_gt (hden_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        (‖negPart hk y‖ ^ 2 + r ^ 2))) :=
    harg.sqrt (by
      intro y
      exact ne_of_gt (div_pos (smoothCap_pos (ε := ε) (r := r) (δ := δ)
        (t := ‖negPart hk y‖ ^ 2) hδ0 hδr) (hden_pos y)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelAttachedStretch hk ε r δ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelAttachedStretch]
      rw [recombine, dite_eq_left hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelAttachedStretch hk ε r δ y i) =
        fun y : MorseModel n =>
          Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelAttachedStretch]
      rw [recombine, dite_eq_right hi]
      rfl
    rw [hcomp]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => y (posIdx hk ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩)) := by
      fun_prop
    exact hsqrt.mul hcoord

theorem contDiff_modelAttachedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedUnstretch hk ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hden_pos : ∀ y : MorseModel n, 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    intro y
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by
      intro y
      exact ne_of_gt (div_pos (hden_pos y) (hcap_pos y)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelAttachedUnstretch hk ε r δ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelAttachedUnstretch]
      rw [recombine, dite_eq_left hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelAttachedUnstretch hk ε r δ y i) =
        fun y : MorseModel n =>
          Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelAttachedUnstretch]
      rw [recombine, dite_eq_right hi]
      rfl
    rw [hcomp]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => y (posIdx hk ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩)) := by
      fun_prop
    exact hsqrt.mul hcoord

noncomputable def modelRoundedUnstretchDamped {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
      (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) • posPart hk y)

theorem modelRoundedUnstretchDamped_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ : ℝ)
    (y : MorseModel n) :
    negPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) = negPart hk y := by
  dsimp [modelRoundedUnstretchDamped]
  rw [negPart_recombine]

theorem modelRoundedUnstretchDamped_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ : ℝ)
    (y : MorseModel n) :
    posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) =
      (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) • posPart hk y := by
  dsimp [modelRoundedUnstretchDamped]
  rw [posPart_recombine]

theorem modelRoundedUnstretchDamped_eq_self_of_negPart_large {n k : ℕ} (hk : k ≤ n)
    (ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : R₁ ≤ ‖negPart hk y‖) :
    modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y = y := by
  have harg : 1 ≤ (‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    have hsq : R₁ ^ 2 ≤ ‖negPart hk y‖ ^ 2 := by
      have hnon : 0 ≤ ‖negPart hk y‖ := norm_nonneg _
      exact sq_le_sq' (by nlinarith only [hR, hR0, hnon]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (one_le_div hden).mpr (by nlinarith only [hsq])
  have hβ₁ : 1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) = 0 := by
    rw [Real.smoothTransition.one_of_one_le harg]
    norm_num
  dsimp [modelRoundedUnstretchDamped]
  rw [hβ₁]
  ring_nf
  rw [one_smul]
  exact recombine_decompose hk y

theorem modelRoundedUnstretchDamped_eq_self_of_norm_large {n k : ℕ} (hk : k ≤ n)
    (ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : R₁ ≤ morseNorm n y) :
    modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y = y := by
  have harg : 1 ≤ (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg h0, abs_of_nonneg (norm_nonneg _)]
        exact hy)
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (one_le_div hden).mpr (by nlinarith only [hsq])
  have hβ₂ : 1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) = 0 := by
    rw [Real.smoothTransition.one_of_one_le harg]
    norm_num
  dsimp [modelRoundedUnstretchDamped]
  rw [hβ₂]
  ring_nf
  rw [one_smul]
  exact recombine_decompose hk y

theorem contDiff_modelRoundedUnstretchDamped {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ : ℝ)
    (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundedUnstretchDamped hk ε r δ R₀ R₁) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) :=
    hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ hδr
  have hden_pos : ∀ y : MorseModel n, 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    intro y
    have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
    nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by intro y; exact ne_of_gt (div_pos (hden_pos y) (hcap_pos y)))
  have hβ₁arg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    have hden' : R₁ ^ 2 - R₀ ^ 2 ≠ 0 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (hnormNeg.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const (R₁ ^ 2 - R₀ ^ 2)
  have hβ₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).sub
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hβ₁arg)
  have hnormPosSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    fun_prop
  have hnormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
    rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
        fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 by
      funext y
      exact morseNorm_sq_eq_negPart_add_posPart hk y]
    exact hnormNeg.add hnormPosSq
  have hβ₂arg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    have hden' : R₁ ^ 2 - R₀ ^ 2 ≠ 0 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (hnormSq.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const (R₁ ^ 2 - R₀ ^ 2)
  have hβ₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).sub
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hβ₂arg)
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) := by
    simpa [mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).add
        ((hsqrt.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)))).mul (hβ₁.mul hβ₂)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelRoundedUnstretchDamped]
      rw [recombine, dite_eq_left hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y i) =
        fun y : MorseModel n =>
          (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
            (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelRoundedUnstretchDamped]
      rw [recombine, dite_eq_right hi]
      rfl
    rw [hcomp]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => y (posIdx hk ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩)) := by
      fun_prop
    exact hscale.mul hcoord

theorem modelRoundedUnstretchDamped_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNormalForm hk c (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) ≤ c + r ^ 2 / 2 := by
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ hδr
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap (le_of_lt hε) hδ hδr (sq_nonneg _)
  have hβ₁01 : (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.smoothTransition.le_one ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
    · exact sub_le_self (1 : ℝ) (Real.smoothTransition.nonneg ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hβ₂01 : (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.smoothTransition.le_one ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
    · exact sub_le_self (1 : ℝ) (Real.smoothTransition.nonneg ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hβ01 : (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hβ₁01.1 hβ₂01.1
    · exact (mul_le_of_le_one_left hβ₂01.1 hβ₁01.2).trans hβ₂01.2
  have hS : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
      (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hUsq : (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 =
        (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      exact Real.sq_sqrt (by
        have hnum : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by positivity
        exact div_nonneg hnum (le_of_lt hsc))
    calc
      (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
          (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
            smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 := by
        simpa only [mul_assoc] using portPrivate_138057aa_one_add_sub_one_mul_sq_le hU hβ01
      _ = (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hUsq
  have hposSq : ‖posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [modelRoundedUnstretchDamped_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    have hSnonneg : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
      simpa only [mul_assoc] using (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hβ01).1
    rw [abs_of_nonneg hSnonneg]
    rw [mul_pow]
    have hle : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa [modelAttachedRegion] using hy
    have hmul : ‖posPart hk y‖ ^ 2 *
        (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
          (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
          ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
      exact mul_le_mul hle hS (by positivity) (by positivity)
    have hmain : smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      field_simp [hsc.ne']
    nlinarith only [hmul, hmain]
  have hf : morseNormalForm hk c (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) =
      c + (1 / 2) * (‖posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
    rw [morseNormalForm_split]
    rw [modelRoundedUnstretchDamped_negPart]
  rw [hf]
  nlinarith only [hposSq]



theorem smoothCap_ge_sub {ε r δ t : ℝ} (hδ : 0 < δ) :
    r ^ 2 - δ ≤ smoothCap ε r δ t := by
  by_cases ht₁ : t ≤ r ^ 2 + 2 * ε - δ
  · rw [smoothCap_lower hδ ht₁]
    nlinarith
  · by_cases ht₂ : r ^ 2 + 2 * ε + δ ≤ t
    · rw [smoothCap_upper hδ ht₂]
      nlinarith
    · have hmid : r ^ 2 + 2 * ε - δ < t ∧ t < r ^ 2 + 2 * ε + δ := by
        constructor <;> linarith
      dsimp [smoothCap]
      have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
        Real.smoothTransition.nonneg _
      have hτle : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
        Real.smoothTransition.le_one _
      have hdelta : t - 2 * ε - r ^ 2 ≥ -δ := by
        nlinarith only [hmid.1]
      by_cases hsign : t - 2 * ε - r ^ 2 ≤ 0
      · have hprod : (t - 2 * ε - r ^ 2) * Real.smoothTransition
            ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≥ t - 2 * ε - r ^ 2 := by
          simpa using mul_le_mul_of_nonpos_left hτle hsign
        nlinarith only [hprod, hdelta]
      · have hprod : 0 ≤ (t - 2 * ε - r ^ 2) * Real.smoothTransition
            ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
          mul_nonneg (le_of_lt (lt_of_not_ge hsign)) hτ
        nlinarith only [hδ, hprod]

theorem negPart_norm_le_morseNorm {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    ‖negPart hk y‖ ≤ morseNorm n y := by
  have hsq : ‖negPart hk y‖ ^ 2 ≤ morseNorm n y ^ 2 := by
    rw [morseNorm_sq_eq_negPart_add_posPart hk y]
    nlinarith only [sq_nonneg ‖posPart hk y‖]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem posPart_norm_le_morseNorm {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    ‖posPart hk y‖ ≤ morseNorm n y := by
  have hsq : ‖posPart hk y‖ ^ 2 ≤ morseNorm n y ^ 2 := by
    rw [morseNorm_sq_eq_negPart_add_posPart hk y]
    nlinarith only [sq_nonneg ‖negPart hk y‖]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem modelRoundedUnstretchDamped_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    {y : MorseModel n} (hy : morseNorm n y ≤ R₁) :
    morseNorm n (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) ^ 2 ≤
      R₁ ^ 2 + R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ hδr
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
  have hβ₁01 : (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.smoothTransition.le_one ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
    · exact sub_le_self (1 : ℝ) (Real.smoothTransition.nonneg ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hβ₂01 : (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.smoothTransition.le_one ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
    · exact sub_le_self (1 : ℝ) (Real.smoothTransition.nonneg ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hβ01 : (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hβ₁01.1 hβ₂01.1
    · exact (mul_le_of_le_one_left hβ₂01.1 hβ₁01.2).trans hβ₂01.2
  have hSnonneg : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
      simpa only [mul_assoc] using (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hβ01).1
  have hSsq : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
      (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hUsq : (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 =
        (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      exact Real.sq_sqrt (by
        have hnum : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by positivity
        exact div_nonneg hnum (le_of_lt hsc))
    calc
      (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
          (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
            smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 := by
        simpa only [mul_assoc] using portPrivate_138057aa_one_add_sub_one_mul_sq_le hU hβ01
      _ = (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hUsq
  have hposSq : ‖posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 ≤
      R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
    rw [modelRoundedUnstretchDamped_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg hSnonneg]
    rw [mul_pow]
    have hpos_le : ‖posPart hk y‖ ^ 2 ≤ R₁ ^ 2 := by
      have hle := posPart_norm_le_morseNorm hk y
      have hle' : ‖posPart hk y‖ ≤ R₁ := le_trans hle hy
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (norm_nonneg _)]
        rw [abs_of_nonneg (by nlinarith only [hR0, hR])]
        exact hle')
    have hU2 : (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤
        (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
      have hneg_le : ‖negPart hk y‖ ^ 2 ≤ R₁ ^ 2 := by
        have hle := negPart_norm_le_morseNorm hk y
        have hle' : ‖negPart hk y‖ ≤ R₁ := le_trans hle hy
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (norm_nonneg _)]
          rw [abs_of_nonneg (by nlinarith only [hR0, hR])]
          exact hle')
      have hscge : r ^ 2 - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_ge_sub hδ
      have hden : 0 < r ^ 2 - δ := by nlinarith only [hδ, hδr]
      have hden' : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hsc
      rw [div_le_div_iff₀ hden' hden]
      calc
        (‖negPart hk y‖ ^ 2 + r ^ 2) * (r ^ 2 - δ) ≤
            (R₁ ^ 2 + r ^ 2) * (r ^ 2 - δ) :=
          mul_le_mul_of_nonneg_right (add_le_add hneg_le le_rfl) (le_of_lt hden)
        _ ≤ (R₁ ^ 2 + r ^ 2) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hscge (by positivity)
    have hmul2 : ‖posPart hk y‖ ^ 2 * (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
          (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
        R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
      have hmul3 : ‖posPart hk y‖ ^ 2 *
          (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            (1 - Real.smoothTransition ((‖negPart hk y‖ ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) *
            (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) ^ 2 ≤
          R₁ ^ 2 * ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
        mul_le_mul hpos_le hSsq (by positivity) (by positivity)
      have hU2' : R₁ ^ 2 * ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) ≤
          R₁ ^ 2 * ((R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ)) := by
        exact mul_le_mul_of_nonneg_left hU2 (by nlinarith only [hR0, hR])
      have hmain : R₁ ^ 2 * ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) ≤
          R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
        simpa [mul_div_assoc] using hU2'
      exact le_trans hmul3 hmain
    rw [mul_comm]
    exact hmul2
  have hnormSq : morseNorm n (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) ^ 2 =
      ‖negPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 +
        ‖posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 :=
    morseNorm_sq_eq_negPart_add_posPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)
  have hneg2 : ‖negPart hk (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)‖ ^ 2 ≤ R₁ ^ 2 := by
    rw [modelRoundedUnstretchDamped_negPart]
    have hle := negPart_norm_le_morseNorm hk y
    have hle' : ‖negPart hk y‖ ≤ R₁ := le_trans hle hy
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _)]
      rw [abs_of_nonneg (by nlinarith only [hR0, hR])]
      exact hle')
  rw [hnormSq]
  nlinarith only [hneg2, hposSq]


noncomputable def modelLevelDampedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
      Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) • posPart hk y)

theorem modelLevelDampedUnstretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (y : MorseModel n) :
    negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) = negPart hk y := by
  dsimp [modelLevelDampedUnstretch]
  rw [negPart_recombine]

theorem modelLevelDampedUnstretch_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (y : MorseModel n) :
    posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) =
      (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) • posPart hk y := by
  dsimp [modelLevelDampedUnstretch]
  rw [posPart_recombine]

theorem modelLevelDampedUnstretch_eq_self_of_deep {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε₀ : 0 < ε₀) (y : MorseModel n)
    (hy : morseNormalForm hk c y ≤ c - ε - η) :
    modelLevelDampedUnstretch hk ε r δ c η ε₀ y = y := by
  have hσ : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hε₀)
  calc
    modelLevelDampedUnstretch hk ε r δ c η ε₀ y
        = recombine hk (negPart hk y) (posPart hk y) := by
          dsimp [modelLevelDampedUnstretch]
          rw [hσ]
          simp
    _ = y := recombine_decompose hk y

theorem modelLevelDampedUnstretch_eq_unstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε₀ : 0 < ε₀) (y : MorseModel n)
    (hy : c - ε - η + ε₀ ≤ morseNormalForm hk c y) :
    modelLevelDampedUnstretch hk ε r δ c η ε₀ y = modelAttachedUnstretch hk ε r δ y := by
  have hσ : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div hε₀]
    nlinarith
  calc
    modelLevelDampedUnstretch hk ε r δ c η ε₀ y
        = recombine hk (negPart hk y)
            (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
              smoothCap ε r δ (‖negPart hk y‖ ^ 2)) • posPart hk y) := by
          dsimp [modelLevelDampedUnstretch]
          rw [hσ]
          ring_nf
    _ = modelAttachedUnstretch hk ε r δ y := by
          dsimp [modelAttachedUnstretch]

theorem contDiff_modelLevelDampedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hδ : 0 < δ) (hδr : δ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLevelDampedUnstretch hk ε r δ c η ε₀) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) :=
    hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ hδr
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by
      intro y
      have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
      exact ne_of_gt (div_pos (by positivity) (hcap_pos y)))
  have hnf : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y) :=
    by
      have hsplit : (fun y : MorseModel n => morseNormalForm hk c y) =
          fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        funext y
        exact morseNormalForm_split hk c y
      rw [hsplit]
      have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
        rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
            fun y : MorseModel n => ∑ i : Fin (n - k), (posPart hk y i) ^ 2 by
          funext y
          exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
        fun_prop
      have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
        rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
            fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
          funext y
          exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
        fun_prop
      exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c)).add
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 / 2 : ℝ))).mul
          (hpos.sub hneg))
  have hσarg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (morseNormalForm hk c y - c + ε + η) / ε₀) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => morseNormalForm hk c y - c + ε + η) :=
      by
        have h' : ContDiff ℝ (⊤ : ℕ∞)
            (fun y : MorseModel n => morseNormalForm hk c y - (c - ε - η)) :=
          hnf.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c - ε - η))
        convert h' using 1
        ext y
        ring
    exact hlin.div_const ε₀
  have hσ : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.smoothTransition
        ((morseNormalForm hk c y - c + ε + η) / ε₀)) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hσarg
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) := by
    simpa [mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).add
        ((hsqrt.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)))).mul hσ))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelLevelDampedUnstretch hk ε r δ c η ε₀ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelLevelDampedUnstretch]
      rw [recombine, dite_eq_left hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelLevelDampedUnstretch hk ε r δ c η ε₀ y i) =
        fun y : MorseModel n =>
          (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelLevelDampedUnstretch]
      rw [recombine, dite_eq_right hi]
      rfl
    rw [hcomp]
    fun_prop

theorem modelLevelDampedUnstretch_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (η ε₀ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNormalForm hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) ≤ c + r ^ 2 / 2 := by
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ hδr
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap (le_of_lt hε) hδ hδr (sq_nonneg _)
  have hσ01 : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hfac0 : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) := by
    exact (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hσ01).1
  have hposSq : ‖posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [modelLevelDampedUnstretch_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg hfac0]
    rw [mul_pow]
    have h1 : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa [modelAttachedRegion] using hy
    have h2 : ‖posPart hk y‖ ^ 2 *
        (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2 ≤
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
          ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
      have hsq : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2 ≤
          (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
        have hsqrt : (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
            smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 =
            (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
          Real.sq_sqrt (by
            have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
            exact div_nonneg (by positivity) (le_of_lt hsc))
        exact le_trans (portPrivate_138057aa_one_add_sub_one_mul_sq_le hU hσ01) (le_of_eq hsqrt)
      exact mul_le_mul h1 hsq (by positivity) (by positivity)
    have h3 : smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) =
        ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      field_simp [ne_of_gt hsc]
    nlinarith only [h2, h3]
  have hnegSq : ‖negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := by
    rw [modelLevelDampedUnstretch_negPart]
  have hsplit := morseNormalForm_split hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)
  rw [hsplit]
  rw [hnegSq]
  nlinarith only [hposSq]

theorem modelLevelDampedUnstretch_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (R₁ : ℝ)
    {y : MorseModel n} (hy : morseNorm n y ≤ R₁) :
    morseNorm n (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) ^ 2 ≤
      R₁ ^ 2 + R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ hδr
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
  have hσ01 : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hfac0 : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) := by
    exact (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hσ01).1
  have hR₁0 : 0 ≤ R₁ := by
    have hnon : 0 ≤ morseNorm n y := by dsimp [morseNorm]; exact norm_nonneg _
    linarith
  have hpos_le : ‖posPart hk y‖ ^ 2 ≤ R₁ ^ 2 := by
    have hle := posPart_norm_le_morseNorm hk y
    have hle' : ‖posPart hk y‖ ≤ R₁ := le_trans hle hy
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _)]
      rw [abs_of_nonneg hR₁0]
      exact hle')
  have hneg_le : ‖negPart hk y‖ ^ 2 ≤ R₁ ^ 2 := by
    have hle := negPart_norm_le_morseNorm hk y
    have hle' : ‖negPart hk y‖ ≤ R₁ := le_trans hle hy
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _)]
      rw [abs_of_nonneg hR₁0]
      exact hle')
  have hU2 : (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤
      (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
    have hscge : r ^ 2 - δ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_ge_sub hδ
    have hden : 0 < r ^ 2 - δ := by nlinarith only [hδ, hδr]
    rw [div_le_div_iff₀ hsc hden]
    calc
      (‖negPart hk y‖ ^ 2 + r ^ 2) * (r ^ 2 - δ) ≤
          (R₁ ^ 2 + r ^ 2) * (r ^ 2 - δ) :=
        mul_le_mul_of_nonneg_right (add_le_add hneg_le le_rfl) (le_of_lt hden)
      _ ≤ (R₁ ^ 2 + r ^ 2) * smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hscge (by positivity)
  have hSsq : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) ^ 2 ≤
      (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
    have hsqrt : (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) ^ 2 =
        (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      Real.sq_sqrt (by
        have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
        exact div_nonneg (by positivity) (le_of_lt hsc))
    exact le_trans (portPrivate_138057aa_one_add_sub_one_mul_sq_le hU hσ01) (le_trans (le_of_eq hsqrt) hU2)
  have hposSq : ‖posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 ≤
      R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
    rw [modelLevelDampedUnstretch_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg hfac0]
    rw [mul_pow]
    have hmul := mul_le_mul hpos_le hSsq (by positivity) (by positivity)
    have hrew : R₁ ^ 2 * ((R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ)) =
        R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
      ring
    rw [hrew] at hmul
    simpa [mul_comm] using hmul
  have hnormSq : morseNorm n (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) ^ 2 =
      ‖negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 +
        ‖posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 :=
    morseNorm_sq_eq_negPart_add_posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)
  have hneg2 : ‖negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 ≤ R₁ ^ 2 := by
    rw [modelLevelDampedUnstretch_negPart]
    exact hneg_le
  rw [hnormSq]
  nlinarith only [hneg2, hposSq]

theorem modelLevelDampedUnstretch_radial_strictMono {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hε₀ : 0 < ε₀)
    {y z : MorseModel n} (hneg : negPart hk y = negPart hk z)
    (hlt : ‖posPart hk y‖ < ‖posPart hk z‖) :
    ‖posPart hk y‖ *
        (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) <
      ‖posPart hk z‖ *
        (1 + (Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk z‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c z - c + ε + η) / ε₀)) := by
  let A : ℝ := Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))
  let σy : ℝ := Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)
  let σz : ℝ := Real.smoothTransition ((morseNormalForm hk c z - c + ε + η) / ε₀)
  let Sy : ℝ := 1 + (A - 1) * σy
  let Sz : ℝ := 1 + (A - 1) * σz
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = smoothCap ε r δ (‖negPart hk z‖ ^ 2) := by
    rw [hneg]
  have hnorm : ‖negPart hk y‖ ^ 2 = ‖negPart hk z‖ ^ 2 := by rw [hneg]
  have hU : 1 ≤ A := by
    dsimp [A]
    exact portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
  have hA0 : 0 ≤ A - 1 := by linarith
  have hA0' : 0 ≤ A := by linarith
  have hσy0 : 0 ≤ σy := by dsimp [σy]; exact Real.smoothTransition.nonneg _
  have hσz0 : 0 ≤ σz := by dsimp [σz]; exact Real.smoothTransition.nonneg _
  have hσle : σy ≤ σz := by
    dsimp [σy, σz]
    apply Real.smoothTransition.monotone
    have hfy : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
      morseNormalForm_split hk c y
    have hfz : morseNormalForm hk c z = c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) :=
      morseNormalForm_split hk c z
    have hsq : ‖posPart hk y‖ ^ 2 < ‖posPart hk z‖ ^ 2 := by
      exact sq_lt_sq.mpr (by
        rw [abs_of_nonneg (norm_nonneg _)]
        rw [abs_of_nonneg (norm_nonneg _)]
        exact hlt)
    have hsub : ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2 := by
      rw [hnorm]
      exact sub_le_sub_right (le_of_lt hsq) _
    have hle' : morseNormalForm hk c y - c + ε + η ≤ morseNormalForm hk c z - c + ε + η := by
      rw [hfy, hfz]
      nlinarith only [hsub]
    exact div_le_div_of_nonneg_right hle' (le_of_lt hε₀)
  have hprod_le : (A - 1) * σy ≤ (A - 1) * σz := by
    exact mul_le_mul_of_nonneg_left hσle hA0
  have hSle : Sy ≤ Sz := by
    dsimp [Sy, Sz]
    nlinarith only [hprod_le]
  have hSge1 : 1 ≤ Sy := by
    dsimp [Sy]
    nlinarith only [hU, hσy0]
  have hSge1z : 1 ≤ Sz := by
    dsimp [Sz]
    nlinarith only [hU, hσz0]
  have hmain : ‖posPart hk y‖ * Sy < ‖posPart hk z‖ * Sz := by
    have hSpos : 0 < Sy := lt_of_lt_of_le zero_lt_one hSge1
    have hSposz : 0 < Sz := lt_of_lt_of_le zero_lt_one hSge1z
    have h1 : ‖posPart hk z‖ * Sy ≤ ‖posPart hk z‖ * Sz :=
      mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ ‖posPart hk z‖)
    have h2 : ‖posPart hk z‖ * Sy > ‖posPart hk y‖ * Sy := by
      exact (mul_lt_mul_of_pos_right hlt hSpos)
    exact lt_of_lt_of_le h2 h1
  rw [← hcap, ← hnorm]
  simpa [Sy, Sz, A, σy, σz] using hmain

theorem modelLevelDampedUnstretch_injective {n k : ℕ} (hk : k ≤ n)
    (ε r δ : ℝ) (c η ε₀ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hε₀ : 0 < ε₀)
    {y z : MorseModel n}
    (h : modelLevelDampedUnstretch hk ε r δ c η ε₀ y = modelLevelDampedUnstretch hk ε r δ c η ε₀ z) :
    y = z := by
  let S : MorseModel n → ℝ := fun w =>
    1 + (Real.sqrt ((‖negPart hk w‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk w‖ ^ 2)) - 1) *
      Real.smoothTransition ((morseNormalForm hk c w - c + ε + η) / ε₀)
  have hneg : negPart hk y = negPart hk z := by
    have h' := congrArg (negPart hk) h
    rwa [modelLevelDampedUnstretch_negPart, modelLevelDampedUnstretch_negPart] at h'
  have hSpos : ∀ w : MorseModel n, 0 < S w := by
    intro w
    dsimp [S]
    have hU : 1 ≤ Real.sqrt ((‖negPart hk w‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk w‖ ^ 2)) :=
      portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
    have hσ0 : 0 ≤ Real.smoothTransition ((morseNormalForm hk c w - c + ε + η) / ε₀) :=
      Real.smoothTransition.nonneg _
    nlinarith
  have hSabs : ∀ w : MorseModel n, |S w| = S w := by
    intro w
    exact abs_of_pos (hSpos w)
  have hpos' : S y • posPart hk y = S z • posPart hk z := by
    have h' : posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) =
        posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ z) := congrArg (posPart hk) h
    rw [modelLevelDampedUnstretch_posPart, modelLevelDampedUnstretch_posPart] at h'
    simpa [S] using h'
  have hnorm : ‖posPart hk y‖ * S y = ‖posPart hk z‖ * S z := by
    have hn : ‖S y • posPart hk y‖ = ‖S z • posPart hk z‖ := congrArg norm hpos'
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hSabs y, hSabs z] at hn
    simpa [mul_comm] using hn
  have hnorm_eq : ‖posPart hk y‖ = ‖posPart hk z‖ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmono := modelLevelDampedUnstretch_radial_strictMono hk ε r δ c η ε₀ hε hδ hδr hε₀ hneg hlt
      have hmono' : ‖posPart hk y‖ * S y < ‖posPart hk z‖ * S z := by
        simpa [S] using hmono
      nlinarith only [hnorm, hmono']
    · have hmono := modelLevelDampedUnstretch_radial_strictMono hk ε r δ c η ε₀ hε hδ hδr hε₀ hneg.symm hgt
      have hmono' : ‖posPart hk z‖ * S z < ‖posPart hk y‖ * S y := by
        simpa [S] using hmono
      nlinarith only [hnorm, hmono']
  have hfac : S y = S z := by
    dsimp [S]
    have hnorm' : ‖negPart hk y‖ ^ 2 = ‖negPart hk z‖ ^ 2 := by rw [hneg]
    have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = smoothCap ε r δ (‖negPart hk z‖ ^ 2) := by
      rw [hneg]
    have hsqrt : Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) =
        Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk z‖ ^ 2)) := by
      rw [hcap, hnorm']
    have hσ : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) =
        Real.smoothTransition ((morseNormalForm hk c z - c + ε + η) / ε₀) := by
      have hfy : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
        morseNormalForm_split hk c y
      have hfz : morseNormalForm hk c z = c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) :=
        morseNormalForm_split hk c z
      have harg : (morseNormalForm hk c y - c + ε + η) / ε₀ =
          (morseNormalForm hk c z - c + ε + η) / ε₀ := by
        have hle' : morseNormalForm hk c y - c + ε + η = morseNormalForm hk c z - c + ε + η := by
          rw [hfy, hfz, hnorm_eq, hnorm']
        rw [hle']
      rw [harg]
    rw [hsqrt, hσ]
  have hpos : posPart hk y = posPart hk z := by
    have hsmul : S y • posPart hk y = S y • posPart hk z := by
      rwa [← hfac] at hpos'
    ext i
    exact mul_left_cancel₀ (ne_of_gt (hSpos y)) (by
      have hc := congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => v i) hsmul
      simpa using hc)
  rw [← recombine_decompose hk y, ← recombine_decompose hk z]
  have hpair : (negPart hk y, posPart hk y) = (negPart hk z, posPart hk z) := by
    apply Prod.ext
    · exact hneg
    · exact hpos
  simpa using congrArg (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
    recombine hk p.1 p.2) hpair

theorem modelLevelDampedUnstretch_f_le_unstretch_f {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (η ε₀ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    morseNormalForm hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) ≤
      morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) := by
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
  have hσ01 : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hfac : 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) ≤
      Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by
    have hsub : 0 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1 := by linarith
    have hmul := mul_le_of_le_one_right hsub hσ01.2
    nlinarith
  have hfac0 : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) := by
    nlinarith only [hU, hσ01.1]
  have hSsqrt0 : 0 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := Real.sqrt_nonneg _
  have hposSq : ‖posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 ≤
      ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 := by
    rw [modelLevelDampedUnstretch_posPart, modelAttachedUnstretch_posPart]
    let a : ℝ := 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)
    let b : ℝ := Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))
    change ‖a • posPart hk y‖ ^ 2 ≤ ‖b • posPart hk y‖ ^ 2
    have hle : a ≤ b := by
      dsimp [a, b]
      exact hfac
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact hfac0
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact hSsqrt0
    calc
      ‖a • posPart hk y‖ ^ 2 = (|a| * ‖posPart hk y‖) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = a ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [abs_of_nonneg ha0]
        ring
      _ ≤ b ^ 2 * ‖posPart hk y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by
          exact sq_le_sq.mpr (by
            calc
              |a| = a := abs_of_nonneg ha0
              _ ≤ b := hle
              _ = |b| := (abs_of_nonneg hb0).symm)) (sq_nonneg _)
      _ = (|b| * ‖posPart hk y‖) ^ 2 := by
        rw [abs_of_nonneg hb0]
        ring
      _ = ‖b • posPart hk y‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs]
  have hnegSq₁ : ‖negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := by
    rw [modelLevelDampedUnstretch_negPart]
  have hnegSq₂ : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := by
    rw [modelAttachedUnstretch_negPart]
  rw [morseNormalForm_split hk c (modelLevelDampedUnstretch hk ε r δ c η ε₀ y),
    morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)]
  rw [hnegSq₁, hnegSq₂]
  nlinarith only [hposSq]

noncomputable def modelLevelRadiusDampedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ R₀ R₁ : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
      Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) • posPart hk y)

theorem modelLevelRadiusDampedUnstretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ R₀ R₁ : ℝ) (y : MorseModel n) :
    negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) = negPart hk y := by
  dsimp [modelLevelRadiusDampedUnstretch]
  rw [negPart_recombine]

theorem modelLevelRadiusDampedUnstretch_eq_levelDamped_of_norm_le {n k : ℕ} (hk : k ≤ n)
    (ε r δ : ℝ) (c η ε₀ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n)
    (hy : morseNorm n y ≤ R₀) :
    modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y =
      modelLevelDampedUnstretch hk ε r δ c η ε₀ y := by
  have hβ : 1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) = 1 := by
    have harg : (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) ≤ 0 := by
      have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
        have hlt : |R₀| < |R₁| := by
          rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
          exact hR
        have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
        nlinarith
      have hsq : morseNorm n y ^ 2 ≤ R₀ ^ 2 := by
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (norm_nonneg _)]
          rw [abs_of_nonneg hR0]
          exact hy)
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hsq]) (le_of_lt hden)
    rw [Real.smoothTransition.zero_of_nonpos harg]
    norm_num
  have hneg : negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) =
      negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) := by
    rw [modelLevelRadiusDampedUnstretch_negPart, modelLevelDampedUnstretch_negPart]
  have hpos : posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) =
      posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) := by
    rw [modelLevelRadiusDampedUnstretch, modelLevelDampedUnstretch]
    rw [posPart_recombine, posPart_recombine]
    have hfac : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
            (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) =
        (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)) := by
      rw [hβ]
      ring
    rw [hfac]
  rw [← recombine_decompose hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)]
  rw [← recombine_decompose hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)]
  have hpair : (negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y),
        posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)) =
      (negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y),
        posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)) := by
    apply Prod.ext
    · exact hneg
    · exact hpos
  simpa using congrArg (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
    recombine hk p.1 p.2) hpair

theorem modelLevelRadiusDampedUnstretch_eq_self_of_norm_large {n k : ℕ} (hk : k ≤ n)
    (ε r δ : ℝ) (c η ε₀ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) (y : MorseModel n)
    (hy : R₁ ≤ morseNorm n y) :
    modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y = y := by
  have hβ : 1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) = 0 := by
    have harg : 1 ≤ (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
      have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
        have hlt : |R₀| < |R₁| := by
          rw [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt (lt_of_le_of_lt hR0 hR))]
          exact hR
        have hsq : R₀ ^ 2 < R₁ ^ 2 := sq_lt_sq.mpr hlt
        nlinarith
      have hsq : R₀ ^ 2 ≤ morseNorm n y ^ 2 := by
        have hle : R₀ ≤ morseNorm n y := le_trans (le_of_lt hR) hy
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg (norm_nonneg _)]
          exact hle)
      exact (le_div_iff₀ hden).mpr (by nlinarith)
    rw [Real.smoothTransition.one_of_one_le harg]
    norm_num
  have hneg : negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) = negPart hk y := by
    rw [modelLevelRadiusDampedUnstretch_negPart]
  have hpos : posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) = posPart hk y := by
    rw [modelLevelRadiusDampedUnstretch]
    rw [posPart_recombine]
    have hfac : (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
          smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
            (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) = 1 := by
      rw [hβ]
      ring
    rw [hfac]
    simp
  have hpair : (negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y),
        posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)) =
      (negPart hk y, posPart hk y) := by
    apply Prod.ext
    · exact hneg
    · exact hpos
  calc
    modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y
        = recombine hk (negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y))
            (posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)) := by
          rw [recombine_decompose hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)]
    _ = recombine hk (negPart hk y) (posPart hk y) := by
          simpa using congrArg (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
            recombine hk p.1 p.2) hpair
    _ = y := recombine_decompose hk y

theorem contDiff_modelLevelRadiusDampedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ R₀ R₁ : ℝ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hnormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
    rw [show (fun y : MorseModel n => morseNorm n y ^ 2) =
        fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 by
      funext y
      exact morseNorm_sq_eq_negPart_add_posPart hk y]
    have hnormPosSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
      rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
          fun y : MorseModel n => ∑ i : Fin (n - k), (posPart hk y i) ^ 2 by
        funext y
        exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      fun_prop
    exact hnormNeg.add hnormPosSq
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) :=
    hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ hδr
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by
      intro y
      have hr2 : 0 < r ^ 2 := by nlinarith only [hδ, hδr]
      exact ne_of_gt (div_pos (by positivity) (hcap_pos y)))
  have hnf : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y) := by
    have hsplit : (fun y : MorseModel n => morseNormalForm hk c y) =
        fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      funext y
      exact morseNormalForm_split hk c y
    rw [hsplit]
    have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
      rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
          fun y : MorseModel n => ∑ i : Fin (n - k), (posPart hk y i) ^ 2 by
        funext y
        exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      fun_prop
    have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := hnormNeg
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c)).add
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 / 2 : ℝ))).mul
        (hpos.sub hneg))
  have hσarg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (morseNormalForm hk c y - c + ε + η) / ε₀) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => morseNormalForm hk c y - c + ε + η) := by
      have h' : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : MorseModel n => morseNormalForm hk c y - (c - ε - η)) :=
        hnf.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c - ε - η))
      convert h' using 1
      ext y
      ring
    exact hlin.div_const ε₀
  have hσL : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.smoothTransition
        ((morseNormalForm hk c y - c + ε + η) / ε₀)) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hσarg
  have hβarg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    have hden' : R₁ ^ 2 - R₀ ^ 2 ≠ 0 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith only [hR, hR0]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0]
          rw [abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (hnormSq.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const
      (R₁ ^ 2 - R₀ ^ 2)
  have hβ : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => 1 - Real.smoothTransition
        ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).sub
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hβarg)
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) := by
    simpa [mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ))).add
        ((hsqrt.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 : ℝ)))).mul
          (hσL.mul hβ)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelLevelRadiusDampedUnstretch]
      rw [recombine, dite_eq_left hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y i) =
        fun y : MorseModel n =>
          (1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
            Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
            (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelLevelRadiusDampedUnstretch]
      rw [recombine, dite_eq_right hi]
      rfl
    rw [hcomp]
    fun_prop

theorem modelLevelRadiusDampedUnstretch_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (c η ε₀ R₀ R₁ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : morseNorm n y ≤ R₁) :
    morseNorm n (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) ^ 2 ≤
      R₁ ^ 2 + R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) := by
  have hleL := modelLevelDampedUnstretch_norm_sq_le hk ε r δ c η ε₀ hε hδ hδr R₁ hy
  have hβ01 : (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.smoothTransition.le_one _)
    · exact sub_le_self (1 : ℝ) (Real.smoothTransition.nonneg _)
  have hU : 1 ≤ Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    portPrivate_138057aa_one_le_sqrt_add_sq_div_smoothCap hε hδ hδr (sq_nonneg _)
  have hσ01 : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hfac_le : 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ≤
      1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) := by
    exact add_le_add (le_refl 1)
      (mul_le_of_le_one_right (mul_nonneg (sub_nonneg.mpr hU) hσ01.1) hβ01.2)
  have hσβ01 : Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
      (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) ∈
        Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hσ01.1 hβ01.1
    · exact le_trans (mul_le_of_le_one_right hσ01.1 hβ01.2) hσ01.2
  have hfac0 : 0 ≤ 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
        Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
        (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) := by
    simpa only [mul_assoc] using (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hσβ01).1
  have hposSq : ‖posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)‖ ^ 2 ≤
      ‖posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 := by
    rw [modelLevelRadiusDampedUnstretch, modelLevelDampedUnstretch]
    rw [posPart_recombine, posPart_recombine]
    let a : ℝ := 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀) *
          (1 - Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
    let b : ℝ := 1 + (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) - 1) *
          Real.smoothTransition ((morseNormalForm hk c y - c + ε + η) / ε₀)
    change ‖a • posPart hk y‖ ^ 2 ≤ ‖b • posPart hk y‖ ^ 2
    have hle : a ≤ b := by
      dsimp [a, b]
      exact hfac_le
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact hfac0
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact (portPrivate_138057aa_one_add_sub_one_mul_mem_Icc hU hσ01).1
    calc
      ‖a • posPart hk y‖ ^ 2 = (|a| * ‖posPart hk y‖) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = a ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [abs_of_nonneg ha0]
        ring
      _ ≤ b ^ 2 * ‖posPart hk y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by
          exact sq_le_sq.mpr (by
            calc
              |a| = a := abs_of_nonneg ha0
              _ ≤ b := hle
              _ = |b| := (abs_of_nonneg hb0).symm)) (sq_nonneg _)
      _ = (|b| * ‖posPart hk y‖) ^ 2 := by
        rw [abs_of_nonneg hb0]
        ring
      _ = ‖b • posPart hk y‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs]
  have hnegSq₁ : ‖negPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := by
    rw [modelLevelRadiusDampedUnstretch_negPart]
  have hnegSq₂ : ‖negPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := by
    rw [modelLevelDampedUnstretch_negPart]
  have hnormC : morseNorm n (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y) ^ 2 ≤
      morseNorm n (modelLevelDampedUnstretch hk ε r δ c η ε₀ y) ^ 2 := by
    rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLevelRadiusDampedUnstretch hk ε r δ c η ε₀ R₀ R₁ y)]
    rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLevelDampedUnstretch hk ε r δ c η ε₀ y)]
    rw [hnegSq₁, hnegSq₂]
    nlinarith only [hposSq]
  exact le_trans hnormC hleL

theorem modelRoundedUnstretchDamped_mem_ball {n k : ℕ} (hk : k ≤ n) (ε r δ R₀ R₁ R R' : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hR₁R : R₁ ≤ R) (hRltRp : R < R') (hR'b : R₁ ^ 2 + R₁ ^ 2 * (R₁ ^ 2 + r ^ 2) / (r ^ 2 - δ) < R' ^ 2)
    {y : MorseModel n} (hy : morseNorm n y < R) :
    modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y ∈ Metric.ball (0 : MorseModel n) R' := by
  rw [mem_ball_zero_iff]
  by_cases hy₁ : morseNorm n y ≤ R₁
  · have hb := modelRoundedUnstretchDamped_norm_sq_le hk ε r δ R₀ R₁ hε hδ hδr hR hR0 hy₁
    have hlt : morseNorm n (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) ^ 2 < R' ^ 2 := by
      nlinarith only [hb, hR'b]
    have hnon : 0 ≤ morseNorm n (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) := norm_nonneg _
    have hR'0 : 0 ≤ R' := by
      nlinarith only [hR, hR0, hR₁R, hRltRp]
    have hmain : morseNorm n (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y) < R' := by
      rw [← abs_of_nonneg hnon]
      rw [← abs_of_nonneg hR'0]
      exact sq_lt_sq.mp hlt
    exact lt_of_le_of_lt (morseNorm_piNorm_le (modelRoundedUnstretchDamped hk ε r δ R₀ R₁ y)) hmain
  · have hgt : R₁ < morseNorm n y := lt_of_not_ge hy₁
    have hle : R₁ ≤ morseNorm n y := le_of_lt hgt
    have heq := modelRoundedUnstretchDamped_eq_self_of_norm_large hk ε r δ R₀ R₁ hR hR0 hle
    rw [heq]
    exact lt_of_le_of_lt (morseNorm_piNorm_le y) (lt_trans hy hRltRp)

theorem modelAttachedRegion_contains_handleBelt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (y : MorseModel n)
    (hy₁ : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε - δ)
    (hy₂ : ‖posPart hk y‖ ^ 2 ≤ r ^ 2) :
    y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [smoothCap_lower hδ0 hy₁]
  exact hy₂

theorem modelAttachedRegion_contains_lowerBelt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n)
    (hy₁ : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε)
    (hy₂ : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε) :
    y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  have hs : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≥ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [smoothCap]
    have hτ : Real.smoothTransition
        ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
      Real.smoothTransition.le_one _
    have hcoef : ‖negPart hk y‖ ^ 2 - 2 * ε - r ^ 2 ≤ 0 := by nlinarith only [hy₁]
    have hτsub : Real.smoothTransition
        ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1 ≤ 0 := by
      linarith [hτ]
    have hmul : 0 ≤ (‖negPart hk y‖ ^ 2 - 2 * ε - r ^ 2) *
        (Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hcoef hτsub
    nlinarith only [hmul]
  nlinarith only [hy₂, hs]

theorem modelAttachedRegion_upperBelt_eq_lower {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (y : MorseModel n)
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    y ∈ modelAttachedRegion hk ε r δ ↔ ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
  dsimp [modelAttachedRegion]
  rw [smoothCap_upper hδ0 hy]

theorem modelHandleMap_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ sublevel (morseNormalForm hk c) (c + r ^ 2 / 2) := by
  change morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c + r ^ 2 / 2
  exact modelHandleMap_f_le hk c ε r hε p

theorem modelHandleMap_mem_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ sublevel (morseNormalForm hk c) (c - ε) ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  change morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c - ε ↔
    ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1
  constructor
  · intro hle
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      le_antisymm hle (modelHandleMap_f_ge hk c ε r (le_of_lt hε) p)
    exact (modelHandleMap_f_eq_lower_iff hk c ε r hε p).1 heq
  · intro hx
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      (modelHandleMap_f_eq_lower_iff hk c ε r hε p).2 hx
    exact le_of_eq heq

theorem morseNormalForm_split_ge {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (y : MorseModel n) :
    c - ε ≤ morseNormalForm hk c y ↔
      ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 2 * ε := by
  rw [morseNormalForm_split]
  constructor <;> intro h <;> nlinarith

theorem modelHandle_eq_inter {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hr : 0 ≤ r) :
    modelHandle hk ε r =
      {y : MorseModel n | ‖posPart hk y‖ ≤ r} ∩
        {y : MorseModel n | c - ε ≤ morseNormalForm hk c y} := by
  ext y
  constructor
  · intro hy
    constructor
    · have hy1 := hy.1
      have hsq := (sq_le_sq).1 hy1
      simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hr] using hsq
    · change c - ε ≤ morseNormalForm hk c y
      rw [morseNormalForm_split_ge]
      exact hy.2
  · intro hy
    constructor
    · exact (sq_le_sq).2 (by
        simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hr] using hy.1)
    · have hy2 : c - ε ≤ morseNormalForm hk c y := by
        exact hy.2
      rw [morseNormalForm_split_ge] at hy2
      exact hy2

theorem modelHandleMap_range {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    Set.range (modelHandleMap hk ε r) = modelHandle hk ε r := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp⟩
    rw [← hp]
    exact modelHandleMap_mem hk ε r (le_of_lt hε) p
  · intro hy
    let w : EuclideanSpace ℝ (Fin (n - k)) := (r⁻¹) • (posPart hk y)
    let s : ℝ := Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2)
    let u : EuclideanSpace ℝ (Fin k) := s⁻¹ • (negPart hk y)
    have hwle : ‖w‖ ≤ 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs]
      have hpos : 0 ≤ r⁻¹ := inv_nonneg.mpr (le_of_lt hr)
      rw [abs_of_nonneg hpos]
      have hle : ‖posPart hk y‖ ≤ r := by
        have hsq := (sq_le_sq).1 hy.1
        have hnr : 0 ≤ r := le_of_lt hr
        simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hnr] using hsq
      have hmul : r⁻¹ * ‖posPart hk y‖ ≤ r⁻¹ * r :=
        mul_le_mul_of_nonneg_left hle hpos
      have hc : r⁻¹ * r = 1 := by
        exact inv_mul_cancel₀ (ne_of_gt hr)
      nlinarith
    have hule : ‖u‖ ≤ 1 := by
      dsimp [u, s]
      have hs0 : 0 < Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) := by
        positivity
      rw [norm_smul, Real.norm_eq_abs]
      have hpos : 0 ≤ (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2))⁻¹ :=
        inv_nonneg.mpr (le_of_lt hs0)
      rw [abs_of_nonneg hpos]
      have hw2 : r ^ 2 * ‖w‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by
        have hrw : r • w = posPart hk y := by
          dsimp [w]
          rw [smul_smul]
          have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
          rw [hrr]
          simp
        have hnorm : ‖r • w‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by rw [hrw]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr)] at hnorm
        simpa [mul_pow] using hnorm
      have hneg2 : ‖negPart hk y‖ ^ 2 ≤ 2 * ε + ‖posPart hk y‖ ^ 2 := by
        nlinarith only [hy.2]
      have hsq2 : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖w‖ ^ 2)]
        nlinarith only [hw2, hneg2]
      have hsq3 : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) := by
        simpa [abs_of_nonneg (norm_nonneg (negPart hk y)),
          abs_of_nonneg (Real.sqrt_nonneg (2 * ε + r ^ 2 * ‖w‖ ^ 2))] using (sq_le_sq).1 hsq2
      have hs : (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2))⁻¹ * ‖negPart hk y‖ ≤ 1 := by
        rw [mul_comm]
        rw [← div_eq_mul_inv]
        exact (div_le_one hs0).2 (by simpa using hsq3)
      exact hs
    refine ⟨((⟨u, hule⟩ : ClosedCell k), (⟨w, hwle⟩ : ClosedCell (n - k))), ?_⟩
    dsimp [modelHandleMap]
    rw [← recombine_decompose hk y]
    congr 1
    · dsimp [u, s]
      rw [smul_smul]
      have hsc : Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) ≠ 0 := by
        positivity
      field_simp [hsc]
      simp
    · dsimp [w]
      rw [smul_smul]
      have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
      rw [hrr]
      simp

theorem lowerUnion_modelHandle {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ) (hr : 0 ≤ r) :
    (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪ modelHandle hk ε r =
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪
        {y : MorseModel (m + 1) | ‖posPart hk y‖ ≤ r} := by
  rw [modelHandle_eq_inter hk c ε r hr]
  ext y
  constructor <;> intro hy
  · rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr hy.1
  · rcases hy with hy | hy
    · exact Or.inl hy
    · by_cases hl : y ∈ sublevel (morseNormalForm hk c) (c - ε)
      · exact Or.inl hl
      · right
        constructor
        · exact hy
        · change c - ε ≤ morseNormalForm hk c y
          rw [morseNormalForm_split_ge]
          have hnot : c - ε < morseNormalForm hk c y := lt_of_not_ge hl
          have hineq : ‖negPart hk y‖ ^ 2 < ‖posPart hk y‖ ^ 2 + 2 * ε := by
            rw [morseNormalForm_split] at hnot
            nlinarith
          exact le_of_lt hineq

theorem modelAttachedStretch_equiv {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    (∀ y : MorseModel n,
        morseNormalForm hk c y ≤ c + r ^ 2 / 2 →
          modelAttachedStretch hk ε r δ y ∈ modelAttachedRegion hk ε r δ) ∧
    (∀ y : MorseModel n,
        y ∈ modelAttachedRegion hk ε r δ →
          morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) ≤ c + r ^ 2 / 2) ∧
    (∀ y : MorseModel n,
        morseNormalForm hk c y ≤ c + r ^ 2 / 2 →
          modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) = y) ∧
    (∀ y : MorseModel n,
        y ∈ modelAttachedRegion hk ε r δ →
          modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) = y) ∧
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedStretch hk ε r δ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedUnstretch hk ε r δ) := by
  constructor
  · intro y hy
    have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      nlinarith only [hy, hf]
    exact modelAttachedStretch_mem hk ε r δ hδ0 hδr hr y hle
  constructor
  · intro y hy
    have hnorm : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 :=
      modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
    have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
        c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
          ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
      morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
    have hneg : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 = ‖negPart hk y‖ ^ 2 :=
      modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
    rw [hf, hneg]
    nlinarith only [hnorm]
  constructor
  · intro y hy
    exact modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr y
  constructor
  · intro y hy
    exact modelAttachedStretch_unstretch hk ε r δ hδ0 hδr hr y
  constructor
  · exact contDiff_modelAttachedStretch hk ε r δ hδ0 hδr hr
  · exact contDiff_modelAttachedUnstretch hk ε r δ hδ0 hδr hr

theorem modelAttachedFunction_stretch_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n)
    (hy : morseNormalForm hk c y = c + r ^ 2 / 2) :
    modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ y) = c := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      exact morseNormalForm_split hk c y
    nlinarith only [hy, hf]
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hratio : (‖posPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) = 1 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      have hmain' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        nlinarith only [hy, hf]
      field_simp [ne_of_gt hpos]
      nlinarith only [hmain']
    have hmain'' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      nlinarith only [hy, hf]
    calc
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
              (‖negPart hk y‖ ^ 2 + r ^ 2) := by rw [hmain'']
      _ = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
        field_simp [ne_of_gt hpos]
  have hposSq : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) := by
    rw [modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y]
    rw [modelAttachedStretch_negPart_norm_sq hk ε r δ y]
    exact hmain
  have hnegSq : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedStretch_negPart_norm_sq hk ε r δ y
  dsimp [modelAttachedFunction]
  rw [hposSq]
  rw [hnegSq]
  ring

theorem modelAttachedFunction_unstretch_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hb : modelAttachedFunction hk c ε r δ y = c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) = c + r ^ 2 / 2 := by
  have hmem : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + r ^ 2 := modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
  have hposSq : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  have hnegSq : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) > 0 :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
        (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
    have hle' : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      dsimp [modelAttachedRegion] at hy
      exact hy
    have hmain'' : ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      nlinarith only [hb, hf, hle']
    calc
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
              smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by rw [hmain'']
      _ = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        field_simp [ne_of_gt hcap]
  have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
      c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
        ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
    morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
  rw [hf, hposSq, hnegSq, hmain]
  ring

theorem modelAttachedFunction_stretch_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n)
    (hy : morseNormalForm hk c y < c + r ^ 2 / 2) :
    modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ y) < c := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      exact morseNormalForm_split hk c y
    nlinarith only [hy, hf]
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith only [hr2, sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hcap : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
    have hratio : (‖posPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) < 1 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      have hmain' : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        nlinarith only [hy, hf]
      rw [div_lt_iff₀ hpos]
      nlinarith only [hmain']
    have hmul : smoothCap ε r δ (‖negPart hk y‖ ^ 2) * (‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 + r ^ 2)) <
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa using (mul_lt_mul_of_pos_left hratio hcap)
    calc
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
              (‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 + r ^ 2)) := by
            field_simp [ne_of_gt hpos]
      _ < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hmul
  have hposSq : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 <
      smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) := by
    rw [modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y]
    rw [modelAttachedStretch_negPart_norm_sq hk ε r δ y]
    exact hmain
  have hnegSq : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedStretch_negPart_norm_sq hk ε r δ y
  dsimp [modelAttachedFunction]
  rw [hnegSq]
  have hsub : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 -
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) < 0 := by
    have : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 <
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa [hnegSq] using hposSq
    nlinarith
  nlinarith only [hsub]

theorem modelAttachedFunction_unstretch_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hb : modelAttachedFunction hk c ε r δ y < c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) < c + r ^ 2 / 2 := by
  have hmem : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + r ^ 2 := modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
  have hposSq : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  have hnegSq : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) > 0 :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
        (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
    have hle' : ‖posPart hk y‖ ^ 2 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      nlinarith only [hb, hf]
    have hratio : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) < 1 := by
      rw [div_lt_iff₀ hcap]
      nlinarith only [hle']
    have hden : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith only [hδ0, hδr, sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hmul : (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        (‖negPart hk y‖ ^ 2 + r ^ 2) < 1 * (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_lt_mul_of_pos_right hratio hden
    calc
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
              (‖negPart hk y‖ ^ 2 + r ^ 2) := by
            field_simp [ne_of_gt hcap]
      _ < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        simpa using hmul
  have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
      c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
        ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
    morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
  rw [hf, hposSq, hnegSq]
  nlinarith only [hmain]

noncomputable def coordClm {n : ℕ} (i : Fin n) : MorseModel n →L[ℝ] ℝ :=
  { toFun := fun y => y i
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
    cont := continuous_apply i }

theorem coordClm_apply {n : ℕ} (i : Fin n) (y : MorseModel n) :
    coordClm i y = y i := rfl

theorem fderiv_coord_sq {n : ℕ} (i : Fin n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => (y i) ^ 2) y w =
      2 * (y i) * (w i) := by
  let L : MorseModel n →L[ℝ] ℝ := coordClm i
  have hL : fderiv ℝ (fun y : MorseModel n => L y) y = L := L.fderiv
  have hproj : fderiv ℝ (fun y : MorseModel n => y i) y = L := by
    change fderiv ℝ (fun y : MorseModel n => L y) y = L
    exact hL
  have hpow : fderiv ℝ (fun z : ℝ => z ^ 2) (y i) =
      (2 * y i) • (1 : ℝ →L[ℝ] ℝ) := by
    rw [show (fun z : ℝ => z ^ 2) = (fun z : ℝ => z) ^ 2 by rfl]
    rw [fderiv_pow (𝕜 := ℝ) (f := fun z : ℝ => z) (n := 2) (x := y i)
      differentiableAt_id]
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hfun : (fun y : MorseModel n => (y i) ^ 2) =
      (fun z : ℝ => z ^ 2) ∘ (fun y : MorseModel n => L y) := by
    funext y
    change (y i) ^ 2 = (fun z : ℝ => z ^ 2) (L y)
    rfl
  calc
    fderiv ℝ (fun y : MorseModel n => (y i) ^ 2) y w
        = fderiv ℝ ((fun z : ℝ => z ^ 2) ∘ (fun y : MorseModel n => L y)) y w := by
          rw [hfun]
    _ = (fderiv ℝ (fun z : ℝ => z ^ 2) (L y) ∘ₗ fderiv ℝ (fun y : MorseModel n => L y) y) w := by
          exact congrArg (fun φ : MorseModel n →L[ℝ] ℝ => φ w)
            (fderiv_comp (x := y) (hg := (differentiableAt_id (x := L y)).pow 2)
              (hf := L.differentiableAt))
    _ = 2 * (y i) * (w i) := by
          simp [coordClm, L, hproj]
          ring

theorem fderiv_posPart_normSq {n k : ℕ} (hk : k ≤ n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y w =
      2 * ∑ j : Fin (n - k), (posPart hk y j) * (posPart hk w j) := by
  have hfun : (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
      ∑ j ∈ (Finset.univ : Finset (Fin (n - k))),
        (fun y : MorseModel n => (posPart hk y j) ^ 2) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [fderiv_sum]
  · rw [FunLike.coe_sum]
    rw [Finset.sum_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (by
      intro j hj
      have hcoord := fderiv_coord_sq (posIdx hk j) y w
      simpa [posPart, mul_assoc] using hcoord)
  · intro j hj
    exact ((coordClm (posIdx hk j)).differentiableAt.pow 2)

theorem fderiv_negPart_normSq {n k : ℕ} (hk : k ≤ n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y w =
      2 * ∑ i : Fin k, (negPart hk y i) * (negPart hk w i) := by
  have hfun : (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
        (fun y : MorseModel n => (negPart hk y i) ^ 2) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [fderiv_sum]
  · rw [FunLike.coe_sum]
    rw [Finset.sum_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (by
      intro i hi
      have hcoord : fderiv ℝ (fun y : MorseModel n => (y (negIdx hk i)) ^ 2) y w =
          2 * (y (negIdx hk i)) * (w (negIdx hk i)) := fderiv_coord_sq (negIdx hk i) y w
      simpa [negPart, mul_assoc] using hcoord)
  · intro i hi
    exact ((coordClm (negIdx hk i)).differentiableAt.pow 2)

theorem fderiv_posPart_normSq_self {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 2 * ‖posPart hk y‖ ^ 2 := by
  rw [fderiv_posPart_normSq]
  have hw : posPart hk (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      posPart hk y :=
    posPart_recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  rw [hw]
  have hsum : ∑ j : Fin (n - k), (posPart hk y j) * (posPart hk y j) =
      ‖posPart hk y‖ ^ 2 := by
    have hn := EuclideanSpace.real_norm_sq_eq (posPart hk y)
    rw [hn]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]

theorem fderiv_negPart_normSq_zero_direction {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
  rw [fderiv_negPart_normSq]
  have hw : negPart hk (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      (0 : EuclideanSpace ℝ (Fin k)) :=
    negPart_recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  rw [hw]
  simp

theorem contDiff_negPart_normSq {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
  rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
      fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
    funext y
    exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
  fun_prop

theorem contDiff_posPart_normSq {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
  rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
      fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
    funext y
    exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
  fun_prop

theorem fderiv_negPart_normSq_self {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      2 * ‖negPart hk y‖ ^ 2 := by
  rw [fderiv_negPart_normSq]
  have hw : negPart hk (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      negPart hk y :=
    negPart_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  rw [hw]
  have hsum : ∑ i : Fin k, (negPart hk y i) * (negPart hk y i) =
      ‖negPart hk y‖ ^ 2 := by
    have hn := EuclideanSpace.real_norm_sq_eq (negPart hk y)
    rw [hn]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]

theorem fderiv_posPart_normSq_zero_direction {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 := by
  rw [fderiv_posPart_normSq]
  have hw : posPart hk (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      (0 : EuclideanSpace ℝ (Fin (n - k))) :=
    posPart_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  rw [hw]
  simp

theorem fderiv_morseNormalForm_ne_zero_lower {n k : ℕ} (hk : k ≤ n) (c a : ℝ) (ha : 0 < a)
    (y : MorseModel n) (hy : morseNormalForm hk c y = c - a) :
    fderiv ℝ (morseNormalForm hk c) y ≠ 0 := by
  have hsplit : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
    morseNormalForm_split hk c y
  have hneg : 0 < ‖negPart hk y‖ ^ 2 := by
    have hmain : ‖negPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * a := by
      nlinarith only [hy, hsplit, ha]
    nlinarith only [hmain, ha, sq_nonneg (‖posPart hk y‖ : ℝ)]
  have hdiff : DifferentiableAt ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y := by
    exact (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfderiv : fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
    have hmain : (fun z : MorseModel n =>
        c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) =
        morseNormalForm hk c := by
      funext z
      exact (morseNormalForm_split hk c z).symm
    rw [← hmain]
    rw [fderiv_const_add]
    have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
        ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hdiff.sub hdiffNeg
    have hmul : fderiv ℝ (fun z : MorseModel n =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) y =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : MorseModel n =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y :=
      fderiv_const_mul hsub (1 / 2 : ℝ)
    rw [hmul]
    congr 1
    exact fderiv_sub (f := fun z : MorseModel n => ‖posPart hk z‖ ^ 2)
      (g := fun z : MorseModel n => ‖negPart hk z‖ ^ 2)
      (hf := hdiff) (hg := hdiffNeg)
  intro hzero
  have hw : fderiv ℝ (morseNormalForm hk c) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))) hzero
  rw [hfderiv] at hw
  have hd : (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y)
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 :=
    fderiv_posPart_normSq_zero_direction hk y
  have hdNeg : (fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y)
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      2 * ‖negPart hk y‖ ^ 2 :=
    fderiv_negPart_normSq_self hk y
  rw [smul_apply] at hw
  rw [sub_apply] at hw
  rw [hd, hdNeg] at hw
  have hw' : (1 / 2 : ℝ) * (0 - 2 * ‖negPart hk y‖ ^ 2) = 0 := by
    simpa using hw
  nlinarith only [hneg, hw']

theorem fderiv_morseNormalForm_ne_zero {n k : ℕ} (hk : k ≤ n) (c a : ℝ) (ha : 0 < a)
    (y : MorseModel n) (hy : morseNormalForm hk c y = c + a) :
    fderiv ℝ (morseNormalForm hk c) y ≠ 0 := by
  have hsplit : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
    morseNormalForm_split hk c y
  have hpos : 0 < ‖posPart hk y‖ ^ 2 := by
    have hmain : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * a := by
      nlinarith only [hy, hsplit, ha]
    nlinarith only [hmain, ha, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hdiff : DifferentiableAt ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y := by
    exact (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfderiv : fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
    have hmain : (fun z : MorseModel n =>
        c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) =
        morseNormalForm hk c := by
      funext z
      exact (morseNormalForm_split hk c z).symm
    rw [← hmain]
    rw [fderiv_const_add]
    have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
        ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hdiff.sub hdiffNeg
    have hmul : fderiv ℝ (fun z : MorseModel n =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) y =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : MorseModel n =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y :=
      fderiv_const_mul hsub (1 / 2 : ℝ)
    rw [hmul]
    congr 1
    exact fderiv_sub (f := fun z : MorseModel n => ‖posPart hk z‖ ^ 2)
      (g := fun z : MorseModel n => ‖negPart hk z‖ ^ 2)
      (hf := hdiff) (hg := hdiffNeg)
  intro hzero
  have hw : fderiv ℝ (morseNormalForm hk c) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) hzero
  rw [hfderiv] at hw
  have hd : (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y)
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 2 * ‖posPart hk y‖ ^ 2 :=
    fderiv_posPart_normSq_self hk y
  have hdNeg : (fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y)
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 :=
    fderiv_negPart_normSq_zero_direction hk y
  rw [smul_apply] at hw
  rw [sub_apply] at hw
  rw [hd, hdNeg] at hw
  have hw' : (1 / 2 : ℝ) * (2 * ‖posPart hk y‖ ^ 2) = 0 := by
    simpa using hw
  nlinarith only [hpos, hw']

theorem fderiv_cap_negPart_zero_direction {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
  have hcapDiff : DifferentiableAt ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) :=
    (smoothCap_contDiff ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hinnerDiff : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hcomp : fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y =
      (fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
        (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y) :=
    fderiv_comp (x := y) (f := fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
      (g := smoothCap ε r δ) (hg := hcapDiff) (hf := hinnerDiff)
  calc
    fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))
        = ((fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
            (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y))
            (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
          rw [hcomp]
    _ = 0 := by
          simp [fderiv_negPart_normSq_zero_direction hk y]

theorem fderiv_modelAttachedFunction_direction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (y : MorseModel n) :
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = ‖posPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffCap : DifferentiableAt ℝ (fun y : MorseModel n =>
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y :=
    ((smoothCap_contDiff ε r δ).comp (contDiff_negPart_normSq hk)).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hderiv : fderiv ℝ (modelAttachedFunction hk c ε r δ) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
        fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y) := by
    unfold modelAttachedFunction
    rw [fderiv_const_add]
    rw [fderiv_const_mul]
    · exact congrArg (fun L : MorseModel n →L[ℝ] ℝ => (1 / 2 : ℝ) • L)
        (fderiv_sub (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
          (g := fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2))
          (hf := hdiffPos) (hg := hdiffCap))
    · exact hdiffPos.sub hdiffCap
  calc
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))
        = ((1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
            fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y))
            (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
          rw [hderiv]
    _ = ‖posPart hk y‖ ^ 2 := by
          simp [fderiv_posPart_normSq_self hk y, fderiv_cap_negPart_zero_direction hk ε r δ y]

theorem fderiv_modelAttachedFunction_ne_zero {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : modelAttachedFunction hk c ε r δ y = c) :
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y ≠ 0 := by
  have hpos : 0 < ‖posPart hk y‖ ^ 2 := by
    have hcap : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
    have hmain : ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
          (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
      nlinarith only [hy, hf]
    rw [hmain]
    exact hcap
  intro h
  have hw : fderiv ℝ (modelAttachedFunction hk c ε r δ) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) h
  rw [fderiv_modelAttachedFunction_direction hk c ε r δ y] at hw
  nlinarith only [hw, hpos]

abbrev ballUpperSublevel {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c + ε) ∧ morseNorm n y ≤ R}

abbrev ballLowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n //
    (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
      y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))}

theorem mem_ballLowerUnion_iff {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) (y : MorseModel n) :
    y ∈ lowerCellUnion hk c ε ∧ morseNorm n y ≤ R ↔
      (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
        y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  constructor
  · rintro ⟨h | ⟨x, hx⟩, hb⟩
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨x, hx⟩
  · rintro (h | ⟨x, hx⟩)
    · exact ⟨Or.inl h.1, h.2⟩
    · rw [← hx]
      exact ⟨Or.inr ⟨x, rfl⟩, norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) x.2⟩

theorem norm_le_of_mem_ballLowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) {y : MorseModel n}
    (h : (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
      y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))) :
    morseNorm n y ≤ R := by
  rcases h with h | ⟨x, hx⟩
  · exact h.2
  · rw [← hx]
    exact norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) x.2

def ballCellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (y : ballUpperSublevel hk c ε R) : ballLowerUnion hk c ε R :=
  ⟨spineMap hk y.1, by
    rcases spineMap_mem_union hk c ε hε y.1 with h | ⟨x, hx⟩
    · exact Or.inl ⟨h, le_trans (norm_spineMap_le hk y.1) y.2.2⟩
    · exact Or.inr ⟨x, hx⟩⟩

def ballCellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (z : ballLowerUnion hk c ε R) : ballUpperSublevel hk c ε R :=
  ⟨z.1, by
    constructor
    · exact cellAttachmentInclusion_mem hk c ε hε ⟨z.1, by
        rcases z.2 with h | ⟨x, hx⟩
        · exact Or.inl h.1
        · exact Or.inr ⟨x, hx⟩⟩
    · exact norm_le_of_mem_ballLowerUnion hk c ε R hR z.2⟩

def ballCellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) :
    Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R → ballUpperSublevel hk c ε R :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1,
      ⟨cellRetractionStep_mem_upper hk c ε (t := p.1.1) (y := p.2.1) p.1.2.1 p.1.2.2 p.2.2.1,
        le_trans (norm_cellRetractionStep_le hk p.1.2.1 p.1.2.2 p.2.1) p.2.2.2⟩⟩

def ballCellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R) :
    Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R → ballLowerUnion hk c ε R :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1, by
      have hmem : cellRetractionStep hk (p.1 : ℝ) p.2.1 ∈ lowerCellUnion hk c ε :=
        cellInclusionStep_mem hk c ε p.1 ⟨p.2.1, by
          rcases p.2.2 with h | ⟨x, hx⟩
          · exact Or.inl h.1
          · exact Or.inr ⟨x, hx⟩⟩
      rcases hmem with h | ⟨x, hx⟩
      · exact Or.inl ⟨h, le_trans (norm_cellRetractionStep_le hk p.1.2.1 p.1.2.2 p.2.1)
          (norm_le_of_mem_ballLowerUnion hk c ε R hR p.2.2)⟩
      · exact Or.inr ⟨x, hx⟩⟩

theorem ballCellRetractionHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (y : ballUpperSublevel hk c ε R) :
    ballCellRetractionHomotopyFun hk c ε R (⟨0, by norm_num⟩, y) =
      ballCellAttachmentInclusion hk c ε R (le_of_lt hε) hR (ballCellAttachmentMap hk c ε R hε y) := by
  apply Subtype.ext
  dsimp [ballCellRetractionHomotopyFun, ballCellAttachmentInclusion, ballCellAttachmentMap]
  exact cellRetractionStep_spine hk y.1

theorem ballCellRetractionHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (y : ballUpperSublevel hk c ε R) :
    ballCellRetractionHomotopyFun hk c ε R (⟨1, by norm_num⟩, y) = y := by
  apply Subtype.ext
  dsimp [ballCellRetractionHomotopyFun]
  exact cellRetractionStep_decompose hk y.1

theorem ballCellInclusionStep_zero {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (z : ballLowerUnion hk c ε R) :
    ballCellInclusionStepFun hk c ε R hR (⟨0, by norm_num⟩, z) =
      ballCellAttachmentMap hk c ε R hε (ballCellAttachmentInclusion hk c ε R (le_of_lt hε) hR z) := by
  apply Subtype.ext
  dsimp [ballCellInclusionStepFun, ballCellAttachmentMap, ballCellAttachmentInclusion]
  exact cellRetractionStep_spine hk z.1

theorem ballCellInclusionStep_one {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R)
    (z : ballLowerUnion hk c ε R) :
    ballCellInclusionStepFun hk c ε R hR (⟨1, by norm_num⟩, z) = z := by
  apply Subtype.ext
  dsimp [ballCellInclusionStepFun]
  exact cellRetractionStep_decompose hk z.1

theorem continuous_ballCellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε) :
    Continuous (ballCellAttachmentMap hk c ε R hε) := by
  have h : Continuous (fun y : ballUpperSublevel hk c ε R => spineMap hk y.1) :=
    (continuous_spineMap hk).comp continuous_subtype_val
  have hcomp : (fun y : ballUpperSublevel hk c ε R =>
      ((ballCellAttachmentMap hk c ε R hε y : ballLowerUnion hk c ε R) : MorseModel n)) =
      fun y => spineMap hk y.1 := by
    funext y
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun y => (congrFun hcomp y).symm)

theorem continuous_ballCellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) : Continuous (ballCellAttachmentInclusion hk c ε R hε hR) := by
  have hcomp : (fun z : ballLowerUnion hk c ε R =>
      ((ballCellAttachmentInclusion hk c ε R hε hR z : ballUpperSublevel hk c ε R) : MorseModel n)) =
      fun z : ballLowerUnion hk c ε R => (z : MorseModel n) := by
    funext z
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    ((continuous_subtype_val : Continuous (fun z : ballLowerUnion hk c ε R => (z : MorseModel n))).congr
      fun z => (congrFun hcomp z).symm)

theorem continuous_ballCellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) :
    Continuous (ballCellRetractionHomotopyFun hk c ε R) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      ((ballCellRetractionHomotopyFun hk c ε R p : ballUpperSublevel hk c ε R) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun p => (congrFun hcomp p).symm)

theorem continuous_ballCellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) : Continuous (ballCellInclusionStepFun hk c ε R hR) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      ((ballCellInclusionStepFun hk c ε R hR p : ballLowerUnion hk c ε R) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (h.congr fun p => (congrFun hcomp p).symm)

noncomputable def portPrivate_138057aa_ballCellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε) :
    C(ballUpperSublevel hk c ε R, ballLowerUnion hk c ε R) :=
  ⟨ballCellAttachmentMap hk c ε R hε, continuous_ballCellAttachmentMap hk c ε R hε⟩

noncomputable def portPrivate_138057aa_ballCellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) : C(ballLowerUnion hk c ε R, ballUpperSublevel hk c ε R) :=
  ⟨ballCellAttachmentInclusion hk c ε R hε hR, continuous_ballCellAttachmentInclusion hk c ε R hε hR⟩

noncomputable def ballCellRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.Homotopy
      ((portPrivate_138057aa_ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR).comp
        (portPrivate_138057aa_ballCellAttachmentMapC hk c ε R hε))
      (ContinuousMap.id (ballUpperSublevel hk c ε R)) where
  toFun := ContinuousMap.mk (ballCellRetractionHomotopyFun hk c ε R)
    (continuous_ballCellRetractionHomotopyFun hk c ε R)
  map_zero_left := by
    intro y
    exact ballCellRetractionHomotopy_zero hk c ε R hε hR y
  map_one_left := by
    intro y
    exact ballCellRetractionHomotopy_one hk c ε R y

noncomputable def ballCellInclusionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.Homotopy
      ((portPrivate_138057aa_ballCellAttachmentMapC hk c ε R hε).comp
        (portPrivate_138057aa_ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR))
      (ContinuousMap.id (ballLowerUnion hk c ε R)) where
  toFun := ContinuousMap.mk (ballCellInclusionStepFun hk c ε R hR)
    (continuous_ballCellInclusionStepFun hk c ε R hR)
  map_zero_left := by
    intro z
    exact ballCellInclusionStep_zero hk c ε R hε hR z
  map_one_left := by
    intro z
    exact ballCellInclusionStep_one hk c ε R hR z

noncomputable def ballCellAttachmentHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.HomotopyEquiv (ballUpperSublevel hk c ε R) (ballLowerUnion hk c ε R) where
  toFun := portPrivate_138057aa_ballCellAttachmentMapC hk c ε R hε
  invFun := portPrivate_138057aa_ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR
  left_inv := ⟨ballCellRetractionHomotopy hk c ε R hε hR⟩
  right_inv := ⟨ballCellInclusionHomotopy hk c ε R hε hR⟩

def ballAttachMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε) (hR : Real.sqrt (2 * ε) ≤ R)
    (x : CellBoundary k) : {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} :=
  ⟨cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    constructor
    · change morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c - ε
      have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
      rw [hf]
      have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ = 1 := x.2
      have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
      rw [hsq, hnorm]
      linarith
    · exact norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) (le_of_eq x.2)⟩

noncomputable def ballCellAdjunctionHomeo {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    CellAdjunctionSpace k (ballAttachMap hk c ε R (le_of_lt hε) hR) ≃ₜ ballLowerUnion hk c ε R := by
  refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := ballAttachMap hk c ε R (le_of_lt hε) hR)
    (c := fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap (Real.sqrt (2 * ε))
  · refine Set.disjoint_left.mpr ?_
    intro y hyA hyB
    exact (Set.disjoint_left.mp (cellInterior_disjoint hk c ε hε)) hyA hyB.1
  · have hclosed : IsClosed {y : MorseModel n |
        y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} := by
      have hcont : Continuous (fun y : MorseModel n => morseNorm n y) :=
        continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
      exact (isClosed_sublevel_normalForm hk c (c - ε)).inter (isClosed_Iic.preimage hcont)
    exact hclosed

noncomputable def ballCellAttachmentModel {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.HomotopyEquiv (ballUpperSublevel hk c ε R)
      (CellAdjunctionSpace k (ballAttachMap hk c ε R (le_of_lt hε) hR)) :=
  (ballCellAttachmentHomotopyEquiv hk c ε R hε hR).trans
    (ballCellAdjunctionHomeo hk c ε R hε hR).symm.toHomotopyEquiv

theorem exists_reindexEquiv {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (hcard : {i : Fin n | w i < 0}.ncard = k) :
    ∃ σe : Fin n ≃ Fin n,
      (∀ i : Fin k, w (σe (negIdx hk i)) = -1) ∧
      (∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) := by
  let negs : Finset (Fin n) := Finset.univ.filter (fun i => w i = -1)
  let poss : Finset (Fin n) := Finset.univ.filter (fun i => w i = 1)
  have hneg_card : negs.card = k := by
    have hset : {i : Fin n | w i < 0} = {i : Fin n | w i = -1} := by
      ext i
      constructor
      · intro hi
        rcases hw i with h | h
        · exact h
        · exfalso
          norm_num [h] at hi
      · intro hi
        change w i < 0
        rw [hi]
        norm_num
    have hcard' : ({i : Fin n | w i = -1} : Set (Fin n)).ncard = k := by
      simpa [hset] using hcard
    have hto : ({i : Fin n | w i = -1} : Set (Fin n)).toFinset = negs := by
      ext i
      simp [negs]
    have hncard := Set.ncard_eq_toFinset_card ({i : Fin n | w i = -1} : Set (Fin n)) (Set.toFinite _)
    have hto' : (Set.toFinite ({i : Fin n | w i = -1} : Set (Fin n))).toFinset = negs := by
      ext i
      simp [negs]
    rw [← hto']
    exact hncard.symm.trans hcard'
  have hdisj : Disjoint negs poss := by
    rw [Finset.disjoint_left]
    intro i hi hp
    have h1 : w i = -1 := (Finset.mem_filter.mp hi).2
    have h2 : w i = 1 := (Finset.mem_filter.mp hp).2
    linarith
  have hpos_card : poss.card = n - k := by
    have hunion : negs ∪ poss = Finset.univ := by
      ext i
      rcases hw i with h | h
      · simp [negs, poss, h]
      · simp [negs, poss, h]
    have hcard' : negs.card + poss.card = n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  let e0 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (negIdx hk) (posIdx hk)
      invFun := fun z => if h : z.val < k then Sum.inl ⟨z.val, h⟩ else Sum.inr ⟨z.val - k, by
        have hkle : k ≤ z.val := le_of_not_gt h
        have hz : z.val < n := z.isLt
        omega⟩
      left_inv := by
        intro s
        cases s with
        | inl i => simp [negIdx]
        | inr j => simp [posIdx]
      right_inv := by
        intro z
        by_cases h : z.val < k
        · simp [h, negIdx]
        · apply Fin.ext
          simp [h, posIdx]
          omega }
  let e1 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (fun i : Fin k => ((negs.orderIsoOfFin hneg_card) i : Fin n))
        (fun j : Fin (n - k) => ((poss.orderIsoOfFin hpos_card) j : Fin n))
      invFun := fun z => if h : z ∈ negs then
          Sum.inl ((negs.orderIsoOfFin hneg_card).symm ⟨z, h⟩)
        else
          Sum.inr ((poss.orderIsoOfFin hpos_card).symm ⟨z, by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]⟩)
      left_inv := by
        intro s
        cases s with
        | inl i =>
            have hmem : ((negs.orderIsoOfFin hneg_card) i : Fin n) ∈ negs :=
              ((negs.orderIsoOfFin hneg_card) i).2
            have hmem' : negs.orderEmbOfFin hneg_card i ∈ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hmem
            dsimp
            rw [dite_eq_left hmem']
            apply congrArg Sum.inl
            exact (negs.orderIsoOfFin hneg_card).symm_apply_apply i
        | inr j =>
            have hmem : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∈ poss :=
              ((poss.orderIsoOfFin hpos_card) j).2
            have hnot : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∉ negs := by
              exact (Finset.disjoint_left.mp (Disjoint.symm hdisj)) hmem
            have hnot' : poss.orderEmbOfFin hpos_card j ∉ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hnot
            dsimp
            rw [dite_eq_right hnot']
            apply congrArg Sum.inr
            calc
              (poss.orderIsoOfFin hpos_card).symm ⟨poss.orderEmbOfFin hpos_card j, _⟩ =
                  (poss.orderIsoOfFin hpos_card).symm ((poss.orderIsoOfFin hpos_card) j) := by
                    apply congrArg (poss.orderIsoOfFin hpos_card).symm
                    apply Subtype.ext
                    rfl
              _ = j := (poss.orderIsoOfFin hpos_card).symm_apply_apply j
      right_inv := by
        intro z
        by_cases h : z ∈ negs
        · dsimp
          rw [dite_eq_left h]
          exact congrArg (fun w : negs => (w : Fin n))
            ((negs.orderIsoOfFin hneg_card).apply_symm_apply ⟨z, h⟩)
        · have hposs' : z ∈ poss := by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]
          dsimp
          rw [dite_eq_right h]
          exact congrArg (fun w : poss => (w : Fin n))
            ((poss.orderIsoOfFin hpos_card).apply_symm_apply ⟨z, hposs'⟩) }
  refine ⟨e0.symm.trans e1, ?_, ?_⟩
  · intro i
    have hz : e0.symm (negIdx hk i) = Sum.inl i := by
      dsimp [e0]
      simp [negIdx]
    change w (e1 (e0.symm (negIdx hk i))) = -1
    rw [hz]
    change w ((negs.orderIsoOfFin hneg_card) i : Fin n) = -1
    exact (Finset.mem_filter.mp ((negs.orderIsoOfFin hneg_card) i).2).2
  · intro j
    have hz : e0.symm (posIdx hk j) = Sum.inr j := by
      dsimp [e0]
      simp [posIdx]
    change w (e1 (e0.symm (posIdx hk j))) = 1
    rw [hz]
    change w ((poss.orderIsoOfFin hpos_card) j : Fin n) = 1
    exact (Finset.mem_filter.mp ((poss.orderIsoOfFin hpos_card) j).2).2

theorem w_sum_reindexed {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (σe : Fin n ≃ Fin n) (hwneg : ∀ i : Fin k, w (σe (negIdx hk i)) = -1)
    (hwpos : ∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) (y : MorseModel n) :
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2) =
      (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
  calc
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2)
        = ∑ j : Fin n, w (σe j) * (y j) ^ 2 := by
          symm
          exact Fintype.sum_equiv σe
            (fun j : Fin n => w (σe j) * (y j) ^ 2)
            (fun i : Fin n => w i * (y (σe.symm i)) ^ 2)
            (by intro j; simp)
    _ = (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
      rw [sum_split_fin hk (fun j : Fin n => w (σe j) * (y j) ^ 2)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hwneg i]
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [hwpos j]
        simp

def addHomeo (n : ℕ) (a : MorseModel n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun z => a + z
  invFun := fun z => z - a
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reindexHomeo {n : ℕ} (σe : Fin n ≃ Fin n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun y => y ∘ σe.symm
  invFun := fun y => y ∘ σe
  left_inv := by
    intro y
    funext i
    simp
  right_inv := by
    intro y
    funext i
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem supNorm_le_morseNorm {n : ℕ} (y : MorseModel n) : ‖y‖ ≤ morseNorm n y := by
  rw [Pi.norm_def]
  exact_mod_cast (Finset.sup_le (s := Finset.univ) (f := fun i : Fin n => ‖y i‖₊)
    (a := ⟨morseNorm n y, norm_nonneg _⟩) (by
      intro i hi
      exact PiLp.norm_apply_le (x := (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) i))

noncomputable def modelSharpUnionBound (ε r : ℝ) (t : ℝ) : ℝ :=
  max (r ^ 2) (t - 2 * ε)

noncomputable def modelSharpUnionRound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))) • posPart hk y)

theorem modelSharpUnionRound_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelSharpUnionRound hk ε r δ y) = negPart hk y := by
  dsimp [modelSharpUnionRound]
  rw [negPart_recombine]

theorem morseNorm_lt_of_mem_attached_negPart_lt {n k : ℕ} (hk : k ≤ n) (ε r δ R : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < R / 2)
    (hRpos : 0 < R) {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hneg : ‖negPart hk y‖ < R / 2) :
    morseNorm n y < R := by
  have ht : ‖negPart hk y‖ ^ 2 < (R / 2) ^ 2 := by
    have habs : |‖negPart hk y‖| < |R / 2| := by
      rw [abs_of_nonneg (norm_nonneg (negPart hk y)), abs_of_nonneg (by nlinarith only [hRpos] : 0 ≤ R / 2)]
      exact hneg
    exact sq_lt_sq.mpr habs
  have hle1 : r ^ 2 ≤ (R / 2) ^ 2 := by
    have h1 : 2 * ε + 2 * r ^ 2 < (R / 2) ^ 2 := by
      have hsc : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < (R / 2) ^ 2 := by
        have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |R / 2| := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [abs_of_nonneg (div_nonneg (le_of_lt hRpos) (by norm_num))]
          exact hεr'
        exact sq_lt_sq.mpr habs
      simpa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)] using hsc
    nlinarith only [h1, hε, sq_nonneg r]
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ (R / 2) ^ 2 := by
    exact le_trans (smoothCap_le_max hε hδ0) (max_le hle1 (le_of_lt ht))
  have hpos : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    dsimp [modelAttachedRegion] at hy
    exact hy
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    calc
      morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
        rw [recombine_decompose hk y]
      _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
  have hsq : morseNorm n y ^ 2 < (R / 2) ^ 2 + (R / 2) ^ 2 := by
    nlinarith only [hnorm, hpos, hsc, ht]
  have hsq' : morseNorm n y ^ 2 < R ^ 2 := by nlinarith only [hsq, hRpos]
  have habs := sq_lt_sq.mp hsq'
  rwa [abs_of_nonneg (norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))),
    abs_of_nonneg (le_of_lt hRpos)] at habs

noncomputable def modelSharpUnionUnround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) • posPart hk y)

theorem modelSharpUnionUnround_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelSharpUnionUnround hk ε r δ y) = negPart hk y := by
  dsimp [modelSharpUnionUnround]
  rw [negPart_recombine]

theorem modelSharpUnionBound_pos {ε r t : ℝ} (hr : r ≠ 0) : 0 < modelSharpUnionBound ε r t := by
  dsimp [modelSharpUnionBound]
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hr) (le_max_left (r ^ 2) (t - 2 * ε))

theorem modelSharpUnionRound_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelSharpUnionRound hk ε r δ y)‖ ^ 2 =
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2 := by
  dsimp [modelSharpUnionRound]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) :=
    modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr])
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
    modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))]

theorem modelSharpUnionUnround_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    ‖posPart hk (modelSharpUnionUnround hk ε r δ y)‖ ^ 2 =
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2 := by
  dsimp [modelSharpUnionUnround]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by
    exact div_nonneg (le_of_lt (modelSharpUnionBound_pos (hr := hr)))
      (le_of_lt (smoothCap_pos hδ0 hδr)))]

theorem modelSharpUnionRound_mem_attached {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r) :
    modelSharpUnionRound hk ε r δ y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [modelSharpUnionRound_posPart_norm_sq hk ε r δ hδ0 hδr y]
  dsimp [modelSharpUnionRound]
  rw [negPart_recombine]
  have hB : ‖posPart hk y‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    rcases hy with hl | hh
    · have hf : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hl
      rw [morseNormalForm_split] at hf
      dsimp [modelSharpUnionBound]
      exact le_trans (by nlinarith) (le_max_right (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε))
    · rcases hh with ⟨hp, hn⟩
      dsimp [modelSharpUnionBound]
      exact le_trans hp (le_max_left (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε))
  have hsc_pos : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hB_pos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr])
  have hmain : smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
      ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hle' : ‖posPart hk y‖ ^ 2 / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ 1 :=
      (div_le_one hB_pos).2 hB
    calc
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
          ‖posPart hk y‖ ^ 2
          = smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
            (‖posPart hk y‖ ^ 2 / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) := by ring
      _ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hle' (le_of_lt hsc_pos)
      _ = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by ring
  exact hmain

theorem modelSharpUnionUnround_posPart_le_bound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    ‖posPart hk (modelSharpUnionUnround hk ε r δ y)‖ ^ 2 ≤
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
  rw [modelSharpUnionUnround_posPart_norm_sq hk ε r δ hδ0 hδr
    (by intro h; rw [h] at hδr; nlinarith only [hδ0, hδr]) y]
  dsimp [modelAttachedRegion] at hy
  have hB_pos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr])
  have hsc_pos : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hle' : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ 1 := by
    exact (div_le_one hsc_pos).2 hy
  calc
    modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2
        = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
          (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by ring
    _ ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hle' (le_of_lt hB_pos)
    _ = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by ring

theorem modelSharpUnionUnround_mem_sharpUnion {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    modelSharpUnionUnround hk ε r δ y ∈
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪ modelHandle hk ε r := by
  let z : MorseModel n := modelSharpUnionUnround hk ε r δ y
  have hpos_le : ‖posPart hk z‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    simpa [z] using modelSharpUnionUnround_posPart_le_bound hk ε r δ hδ0 hδr hy
  have hneg_eq : ‖negPart hk z‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by
    dsimp [z, modelSharpUnionUnround]
    rw [negPart_recombine]
  by_cases hl : z ∈ sublevel (morseNormalForm hk c) (c - ε)
  · exact Or.inl hl
  · right
    constructor
    · change ‖posPart hk z‖ ^ 2 ≤ r ^ 2
      have hposgt : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk z‖ ^ 2 := by
        have hmem : ¬ (z ∈ sublevel (morseNormalForm hk c) (c - ε)) := hl
        have hf : ¬ morseNormalForm hk c z ≤ c - ε := by
          intro hh
          exact hmem (by simpa [sublevel] using hh)
        have hnot : c - ε < morseNormalForm hk c z := lt_of_not_ge hf
        rw [morseNormalForm_split] at hnot
        nlinarith
      have hmax : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≠ ‖negPart hk y‖ ^ 2 - 2 * ε := by
        intro hh
        have : ‖posPart hk z‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by simpa [hh] using hpos_le
        nlinarith
      have hnotle : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = r ^ 2 := by
        dsimp [modelSharpUnionBound]
        exact max_eq_left (by
          by_contra hh
          have : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            max_eq_right (le_of_lt (lt_of_not_ge hh))
          exact hmax this)
      exact le_trans (by simpa [hnotle] using hpos_le) (le_of_eq hnotle)
    · change ‖negPart hk z‖ ^ 2 ≤ ‖posPart hk z‖ ^ 2 + 2 * ε
      rw [hneg_eq]
      have hnot : c - ε < morseNormalForm hk c z := by
        have hmem : ¬ (z ∈ sublevel (morseNormalForm hk c) (c - ε)) := hl
        have hf : ¬ morseNormalForm hk c z ≤ c - ε := by
          intro hh
          exact hmem (by simpa [sublevel] using hh)
        exact lt_of_not_ge hf
      rw [morseNormalForm_split] at hnot
      have hineq : ‖negPart hk y‖ ^ 2 < ‖posPart hk z‖ ^ 2 + 2 * ε := by
        nlinarith
      exact le_of_lt hineq

lemma portPrivate_138057aa_sqrt_div_mul_sqrt_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  have h1 : (Real.sqrt (a / b) * Real.sqrt (b / a)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt (div_nonneg (le_of_lt ha) (le_of_lt hb))]
    rw [Real.sq_sqrt (div_nonneg (le_of_lt hb) (le_of_lt ha))]
    field_simp [ne_of_gt ha, ne_of_gt hb]
  rcases (sq_eq_one_iff.mp h1) with h | h
  · exact h
  · have hnon : (0 : ℝ) ≤ Real.sqrt (a / b) * Real.sqrt (b / a) := by positivity
    nlinarith

theorem modelSharpUnionRound_unround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) {z : MorseModel n} :
    modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ z) = z := by
  let t : ℝ := ‖negPart hk z‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  let B : ℝ := modelSharpUnionBound ε r t
  have hsc : 0 < sc := by
    dsimp [sc, t]
    exact smoothCap_pos hδ0 hδr
  have hB : 0 < B := by
    dsimp [B, t]
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr])
  calc
    modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ z)
        = recombine hk (negPart hk z) (posPart hk z) := by
          dsimp [modelSharpUnionRound, modelSharpUnionUnround, sc, B, t]
          rw [negPart_recombine, posPart_recombine]
          congr 1
          rw [smul_smul]
          rw [portPrivate_138057aa_sqrt_div_mul_sqrt_div sc B hsc hB]
          simp
    _ = z := recombine_decompose hk z

theorem modelSharpUnionUnround_round {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n} :
    modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ y) = y := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  let B : ℝ := modelSharpUnionBound ε r t
  have hsc : 0 < sc := by
    dsimp [sc, t]
    exact smoothCap_pos hδ0 hδr
  have hB : 0 < B := by
    dsimp [B, t]
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr])
  calc
    modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ y)
        = recombine hk (negPart hk y) (posPart hk y) := by
          dsimp [modelSharpUnionUnround, modelSharpUnionRound, sc, B, t]
          rw [negPart_recombine, posPart_recombine]
          congr 1
          rw [smul_smul]
          rw [portPrivate_138057aa_sqrt_div_mul_sqrt_div B sc hB hsc]
          simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionRound_eq_self_of_negPart_large {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ)
    {y : MorseModel n} (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelSharpUnionRound hk ε r δ y = y := by
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    exact smoothCap_upper hδ0 ht
  have hB : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [modelSharpUnionBound]
    exact max_eq_right (by nlinarith only [ht, hδ0])
  calc
    modelSharpUnionRound hk ε r δ y = recombine hk (negPart hk y) (posPart hk y) := by
      dsimp [modelSharpUnionRound]
      rw [hsc, hB]
      congr 1
      have hne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith only [ht, hδ0]
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / (‖negPart hk y‖ ^ 2 - 2 * ε) = 1 := by
        field_simp [hne]
      rw [hratio, Real.sqrt_one]
      simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionUnround_eq_self_of_negPart_large {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ)
    {y : MorseModel n} (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelSharpUnionUnround hk ε r δ y = y := by
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    exact smoothCap_upper hδ0 ht
  have hB : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [modelSharpUnionBound]
    exact max_eq_right (by nlinarith only [ht, hδ0])
  calc
    modelSharpUnionUnround hk ε r δ y = recombine hk (negPart hk y) (posPart hk y) := by
      dsimp [modelSharpUnionUnround]
      rw [hsc, hB]
      congr 1
      have hne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith only [ht, hδ0]
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / (‖negPart hk y‖ ^ 2 - 2 * ε) = 1 := by
        field_simp [hne]
      rw [hratio, Real.sqrt_one]
      simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionRound_eq_self_of_deep {n k : ℕ} (hk : k ≤ n) (c ε r δ η : ℝ)
    (hδ0 : 0 < δ)
    {y : MorseModel n} (hη : r ^ 2 + δ ≤ 2 * η)
    (hy : morseNormalForm hk c y ≤ c - ε - η) :
    modelSharpUnionRound hk ε r δ y = y := by
  have ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
    rw [morseNormalForm_split] at hy
    have h : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε - 2 * η := by nlinarith
    nlinarith only [h, hη]
  exact modelSharpUnionRound_eq_self_of_negPart_large hk ε r δ hδ0 ht

theorem modelSharpUnionUnround_eq_self_of_deep {n k : ℕ} (hk : k ≤ n) (c ε r δ η : ℝ)
    (hδ0 : 0 < δ)
    {y : MorseModel n} (hη : r ^ 2 + δ ≤ 2 * η)
    (hy : morseNormalForm hk c y ≤ c - ε - η) :
    modelSharpUnionUnround hk ε r δ y = y := by
  have ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
    rw [morseNormalForm_split] at hy
    have h : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε - 2 * η := by nlinarith
    nlinarith only [h, hη]
  exact modelSharpUnionUnround_eq_self_of_negPart_large hk ε r δ hδ0 ht

theorem modelSharpUnionRound_morseNorm_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    morseNorm n (modelSharpUnionRound hk ε r δ y) ≤ morseNorm n y := by
  have hsq : morseNorm n (modelSharpUnionRound hk ε r δ y) ^ 2 ≤ morseNorm n y ^ 2 := by
    dsimp [modelSharpUnionRound]
    rw [morseNorm_recombine_sq hk (negPart hk y)
      (Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) •
        posPart hk y)]
    have hnorm_y : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      rw [← recombine_decompose hk y]
      rw [morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)]
      simp [negPart_recombine, posPart_recombine]
    rw [hnorm_y]
    have hsc_le : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
      dsimp [modelSharpUnionBound]
      by_cases hle : ‖negPart hk y‖ ^ 2 - 2 * ε ≤ r ^ 2
      · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = r ^ 2 := max_eq_left hle
        rw [hmax]
        dsimp [smoothCap]
        have hst0 : 0 ≤ Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
          Real.smoothTransition.nonneg _
        nlinarith
      · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
          max_eq_right (le_of_not_ge hle)
        rw [hmax]
        dsimp [smoothCap]
        have hst1 : Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
          Real.smoothTransition.le_one _
        nlinarith
    have hsq1 : ‖Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) •
        posPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by
        have hBpos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
          exact modelSharpUnionBound_pos (hr := by
            intro h
            rw [h] at hδr
            nlinarith only [hδ0, hδr])
        exact div_nonneg (le_of_lt (smoothCap_pos hδ0 hδr)) (le_of_lt hBpos))]
      have hle' : smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ 1 := by
        exact (div_le_one (by
          exact modelSharpUnionBound_pos (hr := by
            intro h
            rw [h] at hδr
            nlinarith only [hδ0, hδr]))).2 hsc_le
      nlinarith only [hle', sq_nonneg (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))]
    nlinarith only [hsq1]
  have habs : |morseNorm n (modelSharpUnionRound hk ε r δ y)| ≤ |morseNorm n y| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

theorem modelSharpUnionUnround_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNorm n (modelSharpUnionUnround hk ε r δ y) ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
  dsimp [modelSharpUnionUnround]
  rw [morseNorm_recombine_sq hk (negPart hk y)
    (Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) •
      posPart hk y)]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by
    have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
    have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) :=
      modelSharpUnionBound_pos hr
    exact div_nonneg (le_of_lt hB) (le_of_lt hsc))]
  have hle : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    dsimp [modelAttachedRegion] at hy
    exact hy
  have hmain : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
      ‖posPart hk y‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
    have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := modelSharpUnionBound_pos hr
    have hle' : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ 1 :=
      (div_le_one hsc).2 hle
    calc
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
          ‖posPart hk y‖ ^ 2
          = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
            (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by ring
      _ ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hle' (le_of_lt hB)
      _ = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by ring
  nlinarith

theorem norm_negPart_le_morseNorm {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    ‖negPart hk y‖ ≤ morseNorm n y := by
  have hsq : ‖negPart hk y‖ ^ 2 ≤ morseNorm n y ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    rw [EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))]
    have hinj : Function.Injective (negIdx hk) := Fin.castLE_injective hk
    have hinjOn : Set.InjOn (negIdx hk) (↑(Finset.univ : Finset (Fin k))) := by
      intro a ha b hb hab
      exact hinj hab
    let image : Finset (Fin n) := Finset.image (negIdx hk) (Finset.univ : Finset (Fin k))
    have hsum : (∑ i : Fin k, ((negPart hk y).ofLp i) ^ 2) ≤
        ∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2 := by
      calc
        (∑ i : Fin k, ((negPart hk y).ofLp i) ^ 2) = ∑ i : Fin k, (y (negIdx hk i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [negPart]
        _ = ∑ j ∈ image, (y j) ^ 2 := by
          dsimp [image]
          rw [Finset.sum_image hinjOn]
        _ ≤ ∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2 := by
          have hrew : (∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2) = ∑ j : Fin n, (y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp
          rw [hrew]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro x hx; exact Finset.mem_univ x)
            (by intro x hx hx0; positivity)
    exact hsum
  have habs : |‖negPart hk y‖| ≤ |morseNorm n y| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

theorem continuous_modelSharpUnionRound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    Continuous (modelSharpUnionRound hk ε r δ) := by
  let hlfun : MorseModel n → ℝ := fun y =>
    Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))
  have hl : Continuous hlfun := by
    have hsc : Continuous (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
      (smoothCap_contDiff ε r δ).continuous.comp ((continuous_norm.comp (continuous_negPart hk)).pow 2)
    have hB : Continuous (fun y : MorseModel n => modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) :=
      (continuous_const.max
        (((continuous_norm.comp (continuous_negPart hk)).pow 2).sub continuous_const))
    have hBpos : ∀ y : MorseModel n, 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := fun y =>
      modelSharpUnionBound_pos (hr := by
        intro h
        rw [h] at hδr
        nlinarith only [hδ0, hδr])
    exact (Real.continuous_sqrt.comp (hsc.div hB (fun y => ne_of_gt (hBpos y)))).congr
      (fun _ => rfl)
  have hpair : Continuous (fun y : MorseModel n =>
      (negPart hk y, hlfun y • posPart hk y)) :=
    (continuous_negPart hk).prodMk (hl.smul (continuous_posPart hk))
  have hmain : Continuous (fun y : MorseModel n =>
      recombine hk (negPart hk y) (hlfun y • posPart hk y)) :=
    (continuous_recombine hk).comp hpair
  refine hmain.congr ?_
  intro y
  rfl

theorem continuous_modelSharpUnionUnround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    Continuous (modelSharpUnionUnround hk ε r δ) := by
  let hmfun : MorseModel n → ℝ := fun y =>
    Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2))
  have hm : Continuous hmfun := by
    have hsc : Continuous (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
      (smoothCap_contDiff ε r δ).continuous.comp ((continuous_norm.comp (continuous_negPart hk)).pow 2)
    have hB : Continuous (fun y : MorseModel n => modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) :=
      (continuous_const.max
        (((continuous_norm.comp (continuous_negPart hk)).pow 2).sub continuous_const))
    have hscpos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := fun y =>
      smoothCap_pos hδ0 hδr
    exact (Real.continuous_sqrt.comp (hB.div hsc (fun y => ne_of_gt (hscpos y)))).congr
      (fun _ => rfl)
  have hpair : Continuous (fun y : MorseModel n =>
      (negPart hk y, hmfun y • posPart hk y)) :=
    (continuous_negPart hk).prodMk (hm.smul (continuous_posPart hk))
  have hmain : Continuous (fun y : MorseModel n =>
      recombine hk (negPart hk y) (hmfun y • posPart hk y)) :=
    (continuous_recombine hk).comp hpair
  refine hmain.congr ?_
  intro y
  rfl

noncomputable def modelSharpUnionRoundingHomeo {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    {y : MorseModel n // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel n // y ∈ modelAttachedRegion hk ε r δ} where
  toFun := fun y => ⟨modelSharpUnionRound hk ε r δ y.1,
    modelSharpUnionRound_mem_attached hk c ε r δ hδ0 hδr y.2⟩
  invFun := fun z => ⟨modelSharpUnionUnround hk ε r δ z.1,
    modelSharpUnionUnround_mem_sharpUnion hk c ε r δ hδ0 hδr z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    change modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ z.1) = z.1
    exact modelSharpUnionUnround_round hk ε r δ hδ0 hδr (y := z.1)
  right_inv := by
    intro y
    apply Subtype.ext
    change modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ y.1) = y.1
    exact modelSharpUnionRound_unround hk ε r δ hδ0 hδr (z := y.1)
  continuous_toFun := Continuous.subtype_mk
    ((continuous_modelSharpUnionRound hk ε r δ hδ0 hδr).comp continuous_subtype_val) (by
      intro y
      exact modelSharpUnionRound_mem_attached hk c ε r δ hδ0 hδr y.2)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_modelSharpUnionUnround hk ε r δ hδ0 hδr).comp continuous_subtype_val) (by
      intro z
      exact modelSharpUnionUnround_mem_sharpUnion hk c ε r δ hδ0 hδr z.2)

noncomputable def modelAttachedRegionEquivUpper {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel n // y ∈ modelAttachedRegion hk ε r δ} ≃ₜ
      {y : MorseModel n // morseNormalForm hk c y ≤ c + r ^ 2 / 2} where
  toFun := fun y => ⟨modelAttachedUnstretch hk ε r δ y.1,
    (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y.1 y.2⟩
  invFun := fun z => ⟨modelAttachedStretch hk ε r δ z.1,
    (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 z.1 z.2⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.1 y.1 y.2
  right_inv := by
    intro z
    apply Subtype.ext
    exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.1 z.1 z.2
  continuous_toFun := Continuous.subtype_mk
    ((modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.2.2.continuous.comp
      continuous_subtype_val) (by
        intro y
        exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y.1 y.2)
  continuous_invFun := Continuous.subtype_mk
    ((modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.2.1.continuous.comp
      continuous_subtype_val) (by
        intro z
        exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 z.1 z.2)

noncomputable def modelSharpUnionToUpperHomeo {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    {y : MorseModel n // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel n // morseNormalForm hk c y ≤ c + r ^ 2 / 2} :=
  (modelSharpUnionRoundingHomeo hk c ε r δ hδ0 hδr).trans
    (modelAttachedRegionEquivUpper hk c ε r δ hδ0 hδr (by
      intro h
      rw [h] at hδr
      nlinarith only [hδ0, hδr]))

theorem modelFlow_posPart_ne_zero_of_negTime {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht : t ≤ 0) (hy : 0 < ‖posPart hk y‖) :
    posPart hk (modelFlow hk t y) ≠ 0 := by
  have hup := modelFlow_up_posPart_norm_sq hk (-t) y (by linarith : 0 ≤ -t) hy
  have hmain : ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t := by
    calc
      ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * (-t) := by
        simpa only [neg_neg] using hup
      _ = ‖posPart hk y‖ ^ 2 - 2 * t := by ring
  have hpos : 0 < ‖posPart hk (modelFlow hk t y)‖ ^ 2 := by
    rw [hmain]
    nlinarith only [sq_pos_of_pos hy, ht]
  exact norm_ne_zero_iff.mp (sq_pos_iff.mp hpos)

theorem modelFlow_posPart_ne_zero_of_posTime {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t < ‖posPart hk y‖ ^ 2 / 2) :
    posPart hk (modelFlow hk t y) ≠ 0 := by
  have hsq := modelFlow_posPart_norm_sq hk t y ht0 (le_of_lt ht)
  have hpos : 0 < ‖posPart hk (modelFlow hk t y)‖ ^ 2 := by
    rw [hsq]
    nlinarith only [ht0, ht]
  exact norm_ne_zero_iff.mp (sq_pos_iff.mp hpos)

theorem modelFlow_posPart_ne_zero_on_interval {n k : ℕ} (hk : k ≤ n) (a b : ℝ) (y : MorseModel n)
    (hy : 0 < ‖posPart hk y‖)
    (hbal : b ≤ ‖posPart hk y‖ ^ 2 / 2) :
    ∀ t ∈ Set.Ioo a b, posPart hk (modelFlow hk t y) ≠ 0 := by
  intro t ht
  by_cases ht0 : t ≤ 0
  · exact modelFlow_posPart_ne_zero_of_negTime hk t y ht0 hy
  · have htpos : 0 ≤ t := le_of_not_gt (by intro h; exact ht0 (le_of_lt h))
    have htle : t < ‖posPart hk y‖ ^ 2 / 2 := lt_of_lt_of_le ht.2 hbal
    exact modelFlow_posPart_ne_zero_of_posTime hk t y htpos htle

theorem modelFlow_posPart_norm_sq_ge_half_of_interval {n k : ℕ} (hk : k ≤ n)
    (a b : ℝ) (y : MorseModel n) (hy : 0 < ‖posPart hk y‖)
    (hbal : b ≤ ‖posPart hk y‖ ^ 2 / 4) :
    ∀ t ∈ Set.Ioo a b, ‖posPart hk y‖ ^ 2 / 2 ≤ ‖posPart hk (modelFlow hk t y)‖ ^ 2 := by
  intro t ht
  by_cases ht0 : t ≤ 0
  · have hup := modelFlow_up_posPart_norm_sq hk (-t) y (by linarith : 0 ≤ -t) hy
    have hmain : ‖posPart hk y‖ ^ 2 ≤ ‖posPart hk (modelFlow hk t y)‖ ^ 2 := by
      rw [show ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * (-t) by
        simpa [neg_neg] using hup]
      nlinarith only [ht0]
    nlinarith
  · have htpos : 0 ≤ t := le_of_not_gt (by intro h; exact ht0 (le_of_lt h))
    have htle : t ≤ ‖posPart hk y‖ ^ 2 / 2 := by
      have hbpos : 0 < b := lt_of_le_of_lt htpos ht.2
      have htlt : t < ‖posPart hk y‖ ^ 2 / 4 := lt_of_lt_of_le ht.2 hbal
      nlinarith only [htlt]
    have hsq := modelFlow_posPart_norm_sq hk t y htpos htle
    have hmain : ‖posPart hk y‖ ^ 2 / 2 ≤ ‖posPart hk (modelFlow hk t y)‖ ^ 2 := by
      rw [hsq]
      have htlt : t < ‖posPart hk y‖ ^ 2 / 4 := lt_of_lt_of_le ht.2 hbal
      nlinarith
    exact hmain

theorem modelFlow_posPart_ge_eps_of_interval {n k : ℕ} (hk : k ≤ n) (ε₁ : ℝ)
    (a b : ℝ) (y : MorseModel n) (hy : 0 < ‖posPart hk y‖)
    (hbal : b ≤ ‖posPart hk y‖ ^ 2 / 4)
    (hε : ε₁ ^ 2 ≤ ‖posPart hk y‖ ^ 2 / 2) :
    ∀ t ∈ Set.Ioo a b, ε₁ ≤ ‖posPart hk (modelFlow hk t y)‖ := by
  have hsq := modelFlow_posPart_norm_sq_ge_half_of_interval hk a b y hy hbal
  intro t ht
  have hmain : ε₁ ^ 2 ≤ ‖posPart hk (modelFlow hk t y)‖ ^ 2 :=
    le_trans hε (hsq t ht)
  by_cases hε10 : 0 ≤ ε₁
  · have hnonneg' : 0 ≤ ‖posPart hk (modelFlow hk t y)‖ := norm_nonneg _
    have habs := sq_le_sq.mp hmain
    rwa [abs_of_nonneg hε10, abs_of_nonneg hnonneg'] at habs
  · have hlt : ε₁ < 0 := lt_of_not_ge hε10
    exact le_trans (le_of_lt hlt) (norm_nonneg _)

theorem modelFlow_norm_lt_of_abs_bound {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 ≤ ε)
    {t : ℝ} (ht : |t| ≤ 2 * ε) {y : MorseModel n} {ρ ρ' : ℝ} (hρ' : 0 ≤ ρ')
    (hy : morseNorm n y < ρ) (hρρ' : ρ ^ 2 + 4 * ε < ρ' ^ 2) :
    morseNorm n (modelFlow hk t y) < ρ' := by
  have hsq := modelFlow_norm_sq_le_add hk ε hε ht y
  have hy' : morseNorm n y ^ 2 < ρ ^ 2 := by
    have hle : 0 ≤ morseNorm n y := norm_nonneg _
    nlinarith only [hy, hle, sq_nonneg ρ]
  have hsq' : morseNorm n (modelFlow hk t y) ^ 2 < ρ' ^ 2 := by
    nlinarith only [hsq, hy', hρρ']
  have hle : 0 ≤ morseNorm n (modelFlow hk t y) := norm_nonneg _
  nlinarith only [hsq', hρ', hle, sq_nonneg ρ']

noncomputable def modelRoundGap (ε r δ : ℝ) (t : ℝ) : ℝ :=
  t - 2 * ε - smoothCap ε r δ t

theorem contDiff_modelRoundGap (ε r δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modelRoundGap ε r δ) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε) := by fun_prop
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε - smoothCap ε r δ t)
  exact hlin.sub (smoothCap_contDiff ε r δ)

theorem modelRoundGap_nonpos_of_le {ε r δ t : ℝ} (ht : t ≤ r ^ 2 + 2 * ε) :
    modelRoundGap ε r δ t ≤ 0 := by
  dsimp [modelRoundGap]
  have hcoef : t - 2 * ε - r ^ 2 ≤ 0 := by nlinarith only [ht]
  have hτ0 : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
    Real.smoothTransition.nonneg _
  have hτ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
    Real.smoothTransition.le_one _
  change t - 2 * ε - (r ^ 2 + (t - 2 * ε - r ^ 2) *
    Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) ≤ 0
  have hmul : (t - 2 * ε - r ^ 2) *
      (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) ≤ 0 := by
    nlinarith only [hcoef, hτ0, hτ1]
  nlinarith only [hmul]

noncomputable def modelRoundDip (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) * modelRoundGap ε r δ t

theorem contDiff_modelRoundDip {ε r δ θ : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundDip ε r δ θ) := by
  have htr : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) := by fun_prop
  have hgap : ContDiff ℝ (⊤ : ℕ∞) (modelRoundGap ε r δ) := contDiff_modelRoundGap ε r δ
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) * modelRoundGap ε r δ t)
  exact htr.mul hgap

noncomputable def modelRoundBound (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  t - 2 * ε - modelRoundDip ε r δ θ t

theorem contDiff_modelRoundBound {ε r δ θ : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundBound ε r δ θ) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε) := by fun_prop
  have hdip : ContDiff ℝ (⊤ : ℕ∞) (modelRoundDip ε r δ θ) := contDiff_modelRoundDip
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε - modelRoundDip ε r δ θ t)
  exact hlin.sub hdip

theorem modelRoundBound_eq_self_of_le {ε r δ θ t : ℝ} (hθ : 0 < θ)
    (ht : t ≤ r ^ 2 + 2 * ε - θ) :
    modelRoundBound ε r δ θ t = t - 2 * ε := by
  dsimp [modelRoundBound, modelRoundDip, modelRoundGap]
  have harg : (t - (r ^ 2 + 2 * ε - θ)) / θ ≤ 0 := by
    have hden : 0 < θ := hθ
    exact (div_le_iff₀ hden).2 (by nlinarith only [ht])
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem modelRoundBound_eq_self_of_ge {ε r δ θ t : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (ht : r ^ 2 + 2 * ε + δ ≤ t) :
    modelRoundBound ε r δ θ t = t - 2 * ε := by
  dsimp [modelRoundBound, modelRoundDip, modelRoundGap]
  have harg : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
    have hden : 0 < θ := hθ
    exact (le_div_iff₀ hden).2 (by nlinarith only [hθ, hδ, ht])
  rw [Real.smoothTransition.one_of_one_le harg]
  rw [smoothCap_upper hδ ht]
  ring

theorem modelRoundBound_le_smoothCap {ε r δ θ t : ℝ} (hθ : 0 < θ) :
    modelRoundBound ε r δ θ t ≤ smoothCap ε r δ t := by
  by_cases ht : t ≤ r ^ 2 + 2 * ε
  · have hgap : modelRoundGap ε r δ t ≤ 0 := modelRoundGap_nonpos_of_le ht
    have hτ0 : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) :=
      Real.smoothTransition.nonneg _
    have hτ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) ≤ 1 :=
      Real.smoothTransition.le_one _
    dsimp [modelRoundBound, modelRoundDip, modelRoundGap] at hgap ⊢
    have hmul : (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) *
        (t - 2 * ε - smoothCap ε r δ t) ≤ 0 := by
      nlinarith only [hgap, hτ0, hτ1]
    nlinarith only [hmul]
  · have ht0 : r ^ 2 + 2 * ε ≤ t := le_of_not_ge ht
    have hτ1 : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
      have hden : 0 < θ := hθ
      exact (le_div_iff₀ hden).2 (by nlinarith only [ht0])
    dsimp [modelRoundBound, modelRoundDip, modelRoundGap]
    rw [Real.smoothTransition.one_of_one_le hτ1]
    linarith

noncomputable def modelRoundRatio (ε r δ : ℝ) (t : ℝ) : ℝ :=
  smoothCap ε r δ t / (t - 2 * ε)

theorem contDiffOn_modelRoundRatio {ε r δ : ℝ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelRoundRatio ε r δ) {t : ℝ | 2 * ε < t} := by
  have hsc : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => smoothCap ε r δ t)
      {t : ℝ | 2 * ε < t} := by
    exact (smoothCap_contDiff ε r δ).contDiffOn.mono (Set.subset_univ _)
  have hid : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε)
      {t : ℝ | 2 * ε < t} := by
    fun_prop
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => smoothCap ε r δ t / (t - 2 * ε))
      {t : ℝ | 2 * ε < t} := by
    refine ContDiffOn.div hsc hid (s := {t : ℝ | 2 * ε < t}) ?_
    intro t ht
    change 2 * ε < t at ht
    linarith [ht]
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => smoothCap ε r δ t / (t - 2 * ε))
    {t : ℝ | 2 * ε < t}
  exact hdiv

noncomputable def modelRoundScale (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
    (1 - Real.sqrt (modelRoundRatio ε r δ t))

theorem contDiff_modelRoundScale {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) : ContDiff ℝ (⊤ : ℕ∞) (modelRoundScale ε r δ θ) := by
  have htr : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) := by
    fun_prop
  have hU₁ : ContDiffOn ℝ (⊤ : ℕ∞) (modelRoundScale ε r δ θ)
      {t : ℝ | t < r ^ 2 + 2 * ε - θ} := by
    exact ContDiffOn.congr (f := fun _ : ℝ => (1 : ℝ))
      (s := {t : ℝ | t < r ^ 2 + 2 * ε - θ})
      (by simpa using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ))).contDiffOn)
      (by
        intro t ht
        change t < r ^ 2 + 2 * ε - θ at ht
        dsimp [modelRoundScale]
        have harg : (t - (r ^ 2 + 2 * ε - θ)) / θ ≤ 0 := by
          have hden : 0 < θ := hθ
          exact (div_le_iff₀ hden).2 (by nlinarith only [ht])
        rw [Real.smoothTransition.zero_of_nonpos harg]
        ring)
  have hratio : ContDiffOn ℝ (⊤ : ℕ∞) (modelRoundRatio ε r δ)
      {t : ℝ | 2 * ε < t} :=
    contDiffOn_modelRoundRatio (ε := ε) (r := r) (δ := δ)
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt (modelRoundRatio ε r δ t))
      {t : ℝ | 2 * ε < t} := by
    refine hratio.sqrt ?_
    intro t ht
    change 2 * ε < t at ht
    have hscpos : 0 < smoothCap ε r δ t := smoothCap_pos hδ hδr
    have hdenpos : 0 < t - 2 * ε := by linarith [ht]
    dsimp [modelRoundRatio]
    exact ne_of_gt (div_pos hscpos hdenpos)
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
        (1 - Real.sqrt (modelRoundRatio ε r δ t))) {t : ℝ | 2 * ε < t} := by
    have htr' : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun t : ℝ => Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ))
        {t : ℝ | 2 * ε < t} :=
      htr.contDiffOn.mono (Set.subset_univ _)
    have hsub : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun t : ℝ => 1 - Real.sqrt (modelRoundRatio ε r δ t))
        {t : ℝ | 2 * ε < t} :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ))).contDiffOn.sub hsqrt
    exact htr'.mul hsub
  have hU₂ : ContDiffOn ℝ (⊤ : ℕ∞) (modelRoundScale ε r δ θ)
      {t : ℝ | 2 * ε < t} := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
        (1 - Real.sqrt (modelRoundRatio ε r δ t))) {t : ℝ | 2 * ε < t}
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ))).contDiffOn.sub hmain
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < r ^ 2 + 2 * ε - θ
  · exact hU₁.contDiffAt (by exact (isOpen_Iio.mem_nhds ht))
  · have ht2 : 2 * ε < t := by
      have hle : r ^ 2 + 2 * ε - θ ≤ t := le_of_not_gt ht
      nlinarith only [hθr, hle]
    exact hU₂.contDiffAt (by exact (isOpen_Ioi.mem_nhds ht2))

theorem modelRoundScale_eq_one_of_le {ε r δ θ t : ℝ} (hθ : 0 < θ)
    (ht : t ≤ r ^ 2 + 2 * ε - θ) :
    modelRoundScale ε r δ θ t = 1 := by
  dsimp [modelRoundScale]
  have harg : (t - (r ^ 2 + 2 * ε - θ)) / θ ≤ 0 := by
    have hden : 0 < θ := hθ
    exact (div_le_iff₀ hden).2 (by nlinarith only [ht])
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem modelRoundScale_eq_one_of_ge {ε r δ θ t : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (ht : r ^ 2 + 2 * ε + δ ≤ t) :
    modelRoundScale ε r δ θ t = 1 := by
  dsimp [modelRoundScale]
  have harg : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
    have hden : 0 < θ := hθ
    exact (le_div_iff₀ hden).2 (by nlinarith only [hθ, hδ, ht])
  rw [Real.smoothTransition.one_of_one_le harg]
  have hcap : smoothCap ε r δ t = t - 2 * ε := smoothCap_upper hδ ht
  dsimp [modelRoundRatio]
  rw [hcap]
  have hdiv : (t - 2 * ε) / (t - 2 * ε) = 1 := by
    have hne : t - 2 * ε ≠ 0 := by nlinarith only [ht, hδ]
    exact div_self hne
  rw [hdiv]
  rw [Real.sqrt_one]
  ring

theorem modelRoundScale_nonneg {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (ht : 2 * ε < t) :
    0 ≤ modelRoundScale ε r δ θ t := by
  by_cases ht0 : t ≤ r ^ 2 + 2 * ε
  · have hgap : modelRoundGap ε r δ t ≤ 0 := modelRoundGap_nonpos_of_le ht0
    have hτ0 : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) :=
      Real.smoothTransition.nonneg _
    dsimp [modelRoundScale]
    have hden : 0 < t - 2 * ε := by linarith [ht]
    have hnum : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
    have hratio : 0 ≤ smoothCap ε r δ t / (t - 2 * ε) := div_nonneg hnum (le_of_lt hden)
    have hsqrt : 0 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := Real.sqrt_nonneg _
    have hgap' : t - 2 * ε ≤ smoothCap ε r δ t := by
      dsimp [modelRoundGap] at hgap
      nlinarith
    have hsqrt1 : 1 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := by
      have hsq : 1 ≤ (Real.sqrt (smoothCap ε r δ t / (t - 2 * ε))) ^ 2 := by
        rw [Real.sq_sqrt hratio]
        rw [one_le_div₀ hden]
        exact hgap'
      have hnon : 0 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := Real.sqrt_nonneg _
      nlinarith only [hsq, hnon]
    have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) :=
      Real.smoothTransition.nonneg _
    have hmul : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
        (1 - Real.sqrt (smoothCap ε r δ t / (t - 2 * ε))) ≤ 0 := by
      nlinarith only [hτ, hsqrt1]
    dsimp [modelRoundRatio]
    nlinarith only [hmul]
  · have ht0 : r ^ 2 + 2 * ε ≤ t := le_of_not_ge ht0
    have hτ1 : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
      have hden : 0 < θ := hθ
      exact (le_div_iff₀ hden).2 (by nlinarith only [ht0])
    dsimp [modelRoundScale]
    rw [Real.smoothTransition.one_of_one_le hτ1]
    have hden : 0 < t - 2 * ε := by linarith [ht]
    have hnum : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
    have hratio : 0 ≤ smoothCap ε r δ t / (t - 2 * ε) := div_nonneg hnum (le_of_lt hden)
    have hsqrt : 0 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := Real.sqrt_nonneg _
    dsimp [modelRoundRatio]
    nlinarith only [hsqrt]

theorem modelRoundScale_pos {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    0 < modelRoundScale ε r δ θ t := by
  by_cases ht2 : 2 * ε < t
  · have hratio_pos : 0 < modelRoundRatio ε r δ t := by
      dsimp [modelRoundRatio]
      exact div_pos (smoothCap_pos hδ hδr) (by linarith [ht2])
    have hsqrt : 0 < Real.sqrt (modelRoundRatio ε r δ t) := Real.sqrt_pos.2 hratio_pos
    let τ : ℝ := Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)
    have hτ0 : 0 ≤ τ := Real.smoothTransition.nonneg _
    have hτ1 : τ ≤ 1 := Real.smoothTransition.le_one _
    have hscale : modelRoundScale ε r δ θ t =
        (1 - τ) + τ * Real.sqrt (modelRoundRatio ε r δ t) := by
      dsimp [modelRoundScale, τ]
      ring
    rw [hscale]
    have h1 : 0 ≤ 1 - τ := by linarith [hτ1]
    by_cases hτzero : τ = 0
    · rw [hτzero]
      nlinarith only [h1]
    · have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτzero)
      have hprod : 0 < τ * Real.sqrt (modelRoundRatio ε r δ t) := mul_pos hτpos hsqrt
      nlinarith only [h1, hprod]
  · have ht_le : t ≤ 2 * ε := le_of_not_gt ht2
    have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [ht_le, hθr]
    rw [modelRoundScale_eq_one_of_le hθ hle]
    norm_num

theorem modelRoundScale_le_sqrt_ratio {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : 2 * ε < t) :
    modelRoundScale ε r δ θ t ≤ Real.sqrt (modelRoundRatio ε r δ t) := by
  by_cases ht0 : t ≤ r ^ 2 + 2 * ε
  · have hgap : modelRoundGap ε r δ t ≤ 0 := modelRoundGap_nonpos_of_le ht0
    have hτ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) ≤ 1 :=
      Real.smoothTransition.le_one _
    have hden : 0 < t - 2 * ε := by linarith [ht]
    have hnum : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
    have hratio0 : 0 ≤ smoothCap ε r δ t / (t - 2 * ε) := div_nonneg hnum (le_of_lt hden)
    have hgap' : t - 2 * ε ≤ smoothCap ε r δ t := by
      dsimp [modelRoundGap] at hgap
      nlinarith
    have hratio1 : 1 ≤ smoothCap ε r δ t / (t - 2 * ε) := by
      rw [one_le_div₀ hden]
      exact hgap'
    have hsqrt1 : 1 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := by
      have hsq : 1 ≤ (Real.sqrt (smoothCap ε r δ t / (t - 2 * ε))) ^ 2 := by
        rw [Real.sq_sqrt hratio0]
        exact hratio1
      have hnon : 0 ≤ Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := Real.sqrt_nonneg _
      nlinarith only [hsq, hnon]
    have hmul : (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) *
        (1 - Real.sqrt (smoothCap ε r δ t / (t - 2 * ε))) ≤ 0 := by
      nlinarith only [hτ1, hsqrt1]
    dsimp [modelRoundScale, modelRoundRatio]
    nlinarith only [hmul]
  · have ht0 : r ^ 2 + 2 * ε ≤ t := le_of_not_ge ht0
    have hτ1 : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
      have hden : 0 < θ := hθ
      exact (le_div_iff₀ hden).2 (by nlinarith only [ht0])
    dsimp [modelRoundScale]
    rw [Real.smoothTransition.one_of_one_le hτ1]
    simp

theorem modelRoundScale_sq_le_ratio {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : 2 * ε < t) :
    modelRoundScale ε r δ θ t ^ 2 ≤ modelRoundRatio ε r δ t := by
  have hle := modelRoundScale_le_sqrt_ratio hδ hθ hδr ht
  have hnon : 0 ≤ modelRoundScale ε r δ θ t := modelRoundScale_nonneg hδ hθ hδr ht
  have hsqrt : 0 ≤ Real.sqrt (modelRoundRatio ε r δ t) := Real.sqrt_nonneg _
  have hmul := mul_le_mul hle hle hnon hsqrt
  have hmul' : modelRoundScale ε r δ θ t ^ 2 ≤
      (Real.sqrt (modelRoundRatio ε r δ t)) ^ 2 := by
    simpa [pow_two] using hmul
  have hden : 0 < t - 2 * ε := by linarith [ht]
  have hnum : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
  have hratio0 : 0 ≤ smoothCap ε r δ t / (t - 2 * ε) := div_nonneg hnum (le_of_lt hden)
  dsimp [modelRoundRatio] at hmul'
  rw [Real.sq_sqrt hratio0] at hmul'
  exact hmul'

noncomputable def modelLowerRoundMap {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) • posPart hk y)

theorem modelLowerRoundMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ) (y : MorseModel n) :
    negPart hk (modelLowerRoundMap hk ε r δ θ y) = negPart hk y := by
  dsimp [modelLowerRoundMap]
  rw [negPart_recombine]

theorem modelLowerRoundMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ) (y : MorseModel n) :
    posPart hk (modelLowerRoundMap hk ε r δ θ y) =
      modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) • posPart hk y := by
  dsimp [modelLowerRoundMap]
  rw [posPart_recombine]

theorem modelLowerRoundMap_eq_self_of_le {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ) (hθ : 0 < θ)
    (y : MorseModel n) (ht : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε - θ) :
    modelLowerRoundMap hk ε r δ θ y = y := by
  rw [← recombine_decompose hk y]
  dsimp [modelLowerRoundMap]
  rw [negPart_recombine, posPart_recombine]
  rw [modelRoundScale_eq_one_of_le hθ ht]
  simp

theorem modelLowerRoundMap_eq_self_of_ge {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ) (hθ : 0 < θ)
    (hδ : 0 < δ) (y : MorseModel n) (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelLowerRoundMap hk ε r δ θ y = y := by
  rw [← recombine_decompose hk y]
  dsimp [modelLowerRoundMap]
  rw [negPart_recombine, posPart_recombine]
  rw [modelRoundScale_eq_one_of_ge hθ hδ ht]
  simp

theorem modelLowerRoundMap_mem_attached {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (y : MorseModel n) (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε)) :
    modelLowerRoundMap hk ε r δ θ y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [modelLowerRoundMap_posPart]
  rw [modelLowerRoundMap_negPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [mul_pow]
  rw [sq_abs]
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hsplit := morseNormalForm_split hk c y
    change morseNormalForm hk c y ≤ c - ε at hy
    nlinarith only [hsplit, hy]
  by_cases ht : 2 * ε < ‖negPart hk y‖ ^ 2
  · have hsc := modelRoundScale_sq_le_ratio hδ hθ hδr ht
    have hden : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by linarith [ht]
    have hratio : modelRoundRatio ε r δ (‖negPart hk y‖ ^ 2) *
        (‖negPart hk y‖ ^ 2 - 2 * ε) = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      dsimp [modelRoundRatio]
      field_simp [hden]
    have hmain : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 *
        ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      have hle' : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 *
          ‖posPart hk y‖ ^ 2 ≤
          modelRoundRatio ε r δ (‖negPart hk y‖ ^ 2) * (‖negPart hk y‖ ^ 2 - 2 * ε) := by
        nlinarith only [hsc, hle]
      nlinarith only [hle', hratio]
    exact hmain
  · have ht' : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := le_of_not_gt ht
    have hpos : ‖posPart hk y‖ = 0 := by
      have hsq : ‖posPart hk y‖ ^ 2 = 0 := by nlinarith only [hle, ht']
      exact sq_eq_zero_iff.mp hsq
    rw [hpos]
    norm_num
    exact smoothCap_nonneg hδ hδr

noncomputable def modelLowerRoundBound (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε)

theorem modelLowerRoundBound_eq_self_of_le {ε r δ θ t : ℝ} (hθ : 0 < θ)
    (ht : t ≤ r ^ 2 + 2 * ε - θ) :
    modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
  dsimp [modelLowerRoundBound]
  rw [modelRoundScale_eq_one_of_le hθ ht]
  ring

theorem modelLowerRoundBound_eq_self_of_ge {ε r δ θ t : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (ht : r ^ 2 + 2 * ε + δ ≤ t) :
    modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
  dsimp [modelLowerRoundBound]
  rw [modelRoundScale_eq_one_of_ge hθ hδ ht]
  ring

theorem contDiff_modelLowerRoundBound {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLowerRoundBound ε r δ θ) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (modelRoundScale ε r δ θ) :=
    contDiff_modelRoundScale hθ hδ hδr hθr
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => modelRoundScale ε r δ θ t ^ 2) :=
    hsc.pow 2
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - 2 * ε) := by fun_prop
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε))
  exact hsq.mul hlin

theorem contDiff_modelLowerRoundMap {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLowerRoundMap hk ε r δ θ) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)) :=
    (contDiff_modelRoundScale hθ hδ hδr hθr).comp (contDiff_negPart_normSq hk)
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcoord : (fun y : MorseModel n => modelLowerRoundMap hk ε r δ θ y i) =
        fun y : MorseModel n => (negPart hk y) ⟨i.val, hi⟩ := by
      funext y
      have hneq : i = negIdx hk ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMap hk ε r δ θ y)]
      rw [recombine_negPart hk (negPart hk (modelLowerRoundMap hk ε r δ θ y))
        (posPart hk (modelLowerRoundMap hk ε r δ θ y)) ⟨i.val, hi⟩]
      rw [modelLowerRoundMap_negPart]
    rw [hcoord]
    fun_prop
  · have hi' : i.val - k < n - k := by
      omega
    have hcoord : (fun y : MorseModel n => modelLowerRoundMap hk ε r δ θ y i) =
        fun y : MorseModel n =>
          modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) * (posPart hk y) ⟨i.val - k, hi'⟩ := by
      funext y
      have hneq : i = posIdx hk ⟨i.val - k, hi'⟩ := by
        apply Fin.ext
        dsimp [posIdx]
        omega
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMap hk ε r δ θ y)]
      rw [recombine_posPart hk (negPart hk (modelLowerRoundMap hk ε r δ θ y))
        (posPart hk (modelLowerRoundMap hk ε r δ θ y)) ⟨i.val - k, hi'⟩]
      rw [modelLowerRoundMap_posPart]
      simp
    rw [hcoord]
    fun_prop

theorem contMDiff_modelLowerRoundMap {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContMDiff (modelWithCornersSelf ℝ (MorseModel n)) (modelWithCornersSelf ℝ (MorseModel n)) (⊤ : ℕ∞)
      (modelLowerRoundMap hk ε r δ θ) :=
  contMDiff_iff_contDiff.mpr (contDiff_modelLowerRoundMap hk ε r δ θ hθ hδ hδr hθr)

noncomputable def modelLowerRoundScaleGlobal {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η : ℝ)
    (y : MorseModel n) : ℝ :=
  modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) +
    Real.smoothTransition ((morseNormalForm hk c y - (c - ε)) / η) *
      (1 - modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2))

noncomputable def modelLowerRoundMapGlobal {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) (modelLowerRoundScaleGlobal hk c ε r δ θ η y • posPart hk y)

theorem modelLowerRoundMapGlobal_negPart {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η : ℝ)
    (y : MorseModel n) :
    negPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y) = negPart hk y := by
  dsimp [modelLowerRoundMapGlobal]
  rw [negPart_recombine]

theorem modelLowerRoundMapGlobal_posPart {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η : ℝ)
    (y : MorseModel n) :
    posPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y) =
      modelLowerRoundScaleGlobal hk c ε r δ θ η y • posPart hk y := by
  dsimp [modelLowerRoundMapGlobal]
  rw [posPart_recombine]

theorem contDiff_modelLowerRoundMapGlobal {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLowerRoundMapGlobal hk c ε r δ θ η) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)) :=
    (contDiff_modelRoundScale hθ hδ hδr hθr).comp (contDiff_negPart_normSq hk)
  have hnf : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y) := by
    rw [show (fun y : MorseModel n => morseNormalForm hk c y) =
        fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) by
      funext y
      exact morseNormalForm_split hk c y]
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c)).add
      (((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 / 2 : ℝ))).mul
        ((contDiff_posPart_normSq hk).sub (contDiff_negPart_normSq hk))))
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (morseNormalForm hk c y - (c - ε)) / η) := by
    exact (hnf.sub contDiff_const).div_const η
  have hg : ContDiff ℝ (⊤ : ℕ∞) (modelLowerRoundScaleGlobal hk c ε r δ θ η) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) +
        Real.smoothTransition ((morseNormalForm hk c y - (c - ε)) / η) *
          (1 - modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)))
    have ht : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        Real.smoothTransition ((morseNormalForm hk c y - (c - ε)) / η)) :=
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp harg
    exact hsc.add (ht.mul ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => (1 : ℝ))).sub hsc))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcoord : (fun y : MorseModel n => modelLowerRoundMapGlobal hk c ε r δ θ η y i) =
        fun y : MorseModel n => (negPart hk y) ⟨i.val, hi⟩ := by
      funext y
      have hneq : i = negIdx hk ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMapGlobal hk c ε r δ θ η y)]
      rw [recombine_negPart hk (negPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y))
        (posPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y)) ⟨i.val, hi⟩]
      rw [modelLowerRoundMapGlobal_negPart]
    rw [hcoord]
    fun_prop
  · have hi' : i.val - k < n - k := by
      omega
    have hcoord : (fun y : MorseModel n => modelLowerRoundMapGlobal hk c ε r δ θ η y i) =
        fun y : MorseModel n =>
          modelLowerRoundScaleGlobal hk c ε r δ θ η y * (posPart hk y) ⟨i.val - k, hi'⟩ := by
      funext y
      have hneq : i = posIdx hk ⟨i.val - k, hi'⟩ := by
        apply Fin.ext
        dsimp [posIdx]
        omega
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMapGlobal hk c ε r δ θ η y)]
      rw [recombine_posPart hk (negPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y))
        (posPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y)) ⟨i.val - k, hi'⟩]
      rw [modelLowerRoundMapGlobal_posPart]
      simp
    rw [hcoord]
    fun_prop

theorem modelLowerRoundMapGlobal_eq_modelLowerRoundMap_of_sublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ η : ℝ) (hη : 0 < η) {y : MorseModel n}
    (hy : morseNormalForm hk c y ≤ c - ε) :
    modelLowerRoundMapGlobal hk c ε r δ θ η y = modelLowerRoundMap hk ε r δ θ y := by
  dsimp [modelLowerRoundMapGlobal, modelLowerRoundMap, modelLowerRoundScaleGlobal]
  have harg : (morseNormalForm hk c y - (c - ε)) / η ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hy]) (le_of_lt hη)
  rw [Real.smoothTransition.zero_of_nonpos harg]
  simp only [zero_mul, add_zero]

theorem modelLowerRoundMapGlobal_eq_self_of_above {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ η : ℝ) (hη : 0 < η) {y : MorseModel n}
    (hy : c - ε + η ≤ morseNormalForm hk c y) :
    modelLowerRoundMapGlobal hk c ε r δ θ η y = y := by
  dsimp [modelLowerRoundMapGlobal, modelLowerRoundScaleGlobal]
  have harg : 1 ≤ (morseNormalForm hk c y - (c - ε)) / η := by
    exact (one_le_div hη).mpr (by nlinarith only [hy])
  rw [Real.smoothTransition.one_of_one_le harg]
  simp only [one_mul, add_sub_cancel, one_smul]
  exact recombine_decompose hk y

noncomputable def modelRoundCapInterp (ε r : ℝ) (a b : ℝ) : ℝ :=
  (1 - a) / ((1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)))

theorem contDiffOn_modelRoundCapInterp {ε r : ℝ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapInterp ε r p.1 p.2)
      {p : ℝ × ℝ | p.1 < 1 ∧ 0 < r ^ 2 * p.2 + 2 * ε ∧
        (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) ≠ 0} := by
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < 1 ∧ 0 < r ^ 2 * p.2 + 2 * ε ∧
    (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) ≠ 0}
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => 1 - p.1) U := by
    fun_prop
  have hd₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => 1 - p.2) U := by
    fun_prop
  have hd₂ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => r ^ 2 * p.2 + 2 * ε) U := by
    fun_prop
  have hd₂ne : ∀ p ∈ U, r ^ 2 * p.2 + 2 * ε ≠ 0 := by
    intro p hp
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    exact ne_of_gt hp₂
  have hfrac : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) U := by
    have hr2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun _p : ℝ × ℝ => r ^ 2) U := by
      fun_prop
    exact hr2.div hd₂ hd₂ne
  have hden : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε))) U :=
    hnum.add (hd₁.mul hfrac)
  have hdenne : ∀ p ∈ U, (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) ≠ 0 := by
    intro p hp
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    exact hp₃
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) /
        ((1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)))) U :=
    hnum.div hden hdenne
  have heq : (fun p : ℝ × ℝ => modelRoundCapInterp ε r p.1 p.2) =
      fun p : ℝ × ℝ => (1 - p.1) /
        ((1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε))) := by
    rfl
  rw [heq]
  exact hmain

theorem contDiffOn_modelRoundCapInterp_handle {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapInterp ε r p.1 p.2)
      {p : ℝ × ℝ | p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  refine (contDiffOn_modelRoundCapInterp).mono ?_
  intro p hp
  rcases hp with ⟨hp₁, hp₂₀, hp₂₁⟩
  constructor
  · exact hp₁
  constructor
  · have hmain : 0 ≤ r ^ 2 * p.2 := mul_nonneg (sq_nonneg r) hp₂₀
    nlinarith only [hε, hmain]
  · have hc : 0 < r ^ 2 / (r ^ 2 * p.2 + 2 * ε) := by
      have hden : 0 < r ^ 2 * p.2 + 2 * ε := by
        have hmain : 0 ≤ r ^ 2 * p.2 := mul_nonneg (sq_nonneg r) hp₂₀
        nlinarith only [hε, hmain]
      exact div_pos (sq_pos_of_pos hr) hden
    have h₁ : 0 < 1 - p.1 := by linarith [hp₁]
    have h₂ : 0 ≤ (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) := by
      exact mul_nonneg (by linarith [hp₂₁]) (le_of_lt hc)
    have hsum : 0 < (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) := by
      nlinarith only [h₁, h₂]
    exact ne_of_gt hsum

theorem modelRoundCapInterp_eq_zero_of_eq_one {ε r a b : ℝ} (ha : a = 1) :
    modelRoundCapInterp ε r a b = 0 := by
  dsimp [modelRoundCapInterp]
  rw [ha]
  simp only [sub_self, zero_add, zero_div]

theorem modelRoundCapInterp_eq_one_of_eq_one {ε r a b : ℝ} (hb : b = 1) (ha : a ≠ 1) :
    modelRoundCapInterp ε r a b = 1 := by
  dsimp [modelRoundCapInterp]
  rw [hb]
  simp only [sub_self, zero_mul, add_zero]
  exact div_self (sub_ne_zero.mpr ha.symm)

theorem modelRoundCapInterp_eq_cocore {ε r a b : ℝ} (ha : a = 0) (hε : 0 < ε)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    modelRoundCapInterp ε r a b = (r ^ 2 * b + 2 * ε) / (r ^ 2 + 2 * ε) := by
  dsimp [modelRoundCapInterp]
  rw [ha]
  simp only [sub_zero]
  have hdenpos : 0 < (1 : ℝ) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
    have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
    have h2 : 0 ≤ (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      exact mul_nonneg (by nlinarith only [hb1]) (div_nonneg (sq_nonneg r) (le_of_lt h1))
    nlinarith
  have hden : (1 : ℝ) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) ≠ 0 := ne_of_gt hdenpos
  have hε2 : r ^ 2 + 2 * ε ≠ 0 := by nlinarith only [hε]
  have hbden : r ^ 2 * b + 2 * ε ≠ 0 := by nlinarith only [hε, hb0, sq_nonneg r]
  rw [div_eq_iff hden]
  have hD : (1 : ℝ) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) =
      (r ^ 2 + 2 * ε) / (r ^ 2 * b + 2 * ε) := by
    field_simp [hbden, hε2]
    ring
  rw [hD]
  field_simp [hbden, hε2]

noncomputable def modelRoundCapQ (ε r δ θ : ℝ) (a b : ℝ) : ℝ :=
  (1 - modelRoundCapInterp ε r a b) *
      modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a) +
    modelRoundCapInterp ε r a b * smoothCap ε r δ ((2 * ε + r ^ 2 * b) * a)

theorem contDiffOn_modelRoundCapQ {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapQ ε r δ θ p.1 p.2)
      {p : ℝ × ℝ | p.1 < 1 ∧ 0 < r ^ 2 * p.2 + 2 * ε ∧
        (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) ≠ 0} := by
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < 1 ∧ 0 < r ^ 2 * p.2 + 2 * ε ∧
    (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) ≠ 0}
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapInterp ε r p.1 p.2) U :=
    contDiffOn_modelRoundCapInterp.mono (by intro p hp; exact hp)
  have htU : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (2 * ε + r ^ 2 * p.2) * p.1) U := by
    fun_prop
  have hB : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1)) U :=
    (contDiff_modelLowerRoundBound hθ hδ hδr hθr).contDiffOn.comp
      (s := U) (t := Set.univ)
      htU (by intro p hp; trivial)
  have hS : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => smoothCap ε r δ ((2 * ε + r ^ 2 * p.2) * p.1)) U :=
    (smoothCap_contDiff ε r δ).contDiffOn.comp
      (s := U) (t := Set.univ)
      htU (by intro p hp; trivial)
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (1 - modelRoundCapInterp ε r p.1 p.2) *
          modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1) +
        modelRoundCapInterp ε r p.1 p.2 * smoothCap ε r δ ((2 * ε + r ^ 2 * p.2) * p.1)) U := by
    have h₁ : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (1 - modelRoundCapInterp ε r p.1 p.2) *
          modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1)) U := by
      exact (contDiffOn_const.sub hφ).mul hB
    have h₂ : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => modelRoundCapInterp ε r p.1 p.2 *
          smoothCap ε r δ ((2 * ε + r ^ 2 * p.2) * p.1)) U := by
      exact hφ.mul hS
    exact h₁.add h₂
  have heq : (fun p : ℝ × ℝ => modelRoundCapQ ε r δ θ p.1 p.2) =
      fun p : ℝ × ℝ => (1 - modelRoundCapInterp ε r p.1 p.2) *
          modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1) +
        modelRoundCapInterp ε r p.1 p.2 * smoothCap ε r δ ((2 * ε + r ^ 2 * p.2) * p.1) := by
    rfl
  rw [heq]
  exact hmain

theorem contDiffOn_modelRoundCapQ_handle {ε r δ θ : ℝ} (hε : 0 < ε) (hr : 0 < r) (hθ : 0 < θ)
    (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapQ ε r δ θ p.1 p.2)
      {p : ℝ × ℝ | p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  refine (contDiffOn_modelRoundCapQ hθ hδ hδr hθr).mono ?_
  intro p hp
  rcases hp with ⟨hp₁, hp₂₀, hp₂₁⟩
  constructor
  · exact hp₁
  constructor
  · have hmain : 0 ≤ r ^ 2 * p.2 := mul_nonneg (sq_nonneg r) hp₂₀
    nlinarith only [hε, hmain]
  · have hc : 0 < r ^ 2 / (r ^ 2 * p.2 + 2 * ε) := by
      have hden : 0 < r ^ 2 * p.2 + 2 * ε := by
        have hmain : 0 ≤ r ^ 2 * p.2 := mul_nonneg (sq_nonneg r) hp₂₀
        nlinarith only [hε, hmain]
      exact div_pos (sq_pos_of_pos hr) hden
    have h₁ : 0 < 1 - p.1 := by linarith [hp₁]
    have h₂ : 0 ≤ (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) := by
      exact mul_nonneg (by linarith [hp₂₁]) (le_of_lt hc)
    have hsum : 0 < (1 - p.1) + (1 - p.2) * (r ^ 2 / (r ^ 2 * p.2 + 2 * ε)) := by
      nlinarith only [h₁, h₂]
    exact ne_of_gt hsum

theorem modelRoundCapQ_eq_lowerBound_of_eq_one {ε r δ θ a b : ℝ} (ha : a = 1) :
    modelRoundCapQ ε r δ θ a b = modelLowerRoundBound ε r δ θ (2 * ε + r ^ 2 * b) := by
  dsimp [modelRoundCapQ]
  rw [modelRoundCapInterp_eq_zero_of_eq_one ha, ha]
  simp

theorem modelRoundCapQ_eq_smoothCap_of_eq_one {ε r δ θ a b : ℝ} (hb : b = 1) (ha : a ≠ 1) :
    modelRoundCapQ ε r δ θ a b = smoothCap ε r δ ((2 * ε + r ^ 2) * a) := by
  dsimp [modelRoundCapQ]
  rw [modelRoundCapInterp_eq_one_of_eq_one hb ha, hb]
  simp

theorem portPrivate_138057aa_smoothCap_eq_rSq_of_vertex {ε r δ : ℝ} :
    smoothCap ε r δ (r ^ 2 + 2 * ε) = r ^ 2 := by
  dsimp [smoothCap]
  ring

theorem portPrivate_138057aa_modelRoundScale_eq_one_of_vertex {ε r δ θ : ℝ} (hθ : 0 < θ) (hr : r ≠ 0) :
    modelRoundScale ε r δ θ (r ^ 2 + 2 * ε) = 1 := by
  dsimp [modelRoundScale]
  have harg : (r ^ 2 + 2 * ε - (r ^ 2 + 2 * ε - θ)) / θ = 1 := by
    field_simp [ne_of_gt hθ]
    ring
  rw [harg]
  have hratio : modelRoundRatio ε r δ (r ^ 2 + 2 * ε) = 1 := by
    dsimp [modelRoundRatio]
    rw [portPrivate_138057aa_smoothCap_eq_rSq_of_vertex]
    have hden : (r ^ 2 + 2 * ε) - 2 * ε = r ^ 2 := by ring
    rw [hden]
    rw [div_self (pow_ne_zero 2 hr)]
  rw [hratio]
  rw [Real.sqrt_one]
  rw [Real.smoothTransition.one]
  ring

theorem portPrivate_138057aa_modelLowerRoundBound_eq_rSq_of_vertex {ε r δ θ : ℝ} (hθ : 0 < θ) (hr : r ≠ 0) :
    modelLowerRoundBound ε r δ θ (r ^ 2 + 2 * ε) = r ^ 2 := by
  dsimp [modelLowerRoundBound]
  rw [portPrivate_138057aa_modelRoundScale_eq_one_of_vertex hθ hr]
  have harg : (r ^ 2 + 2 * ε) - 2 * ε = r ^ 2 := by ring
  rw [harg]
  ring

noncomputable def modelRoundCapGap (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t

theorem contDiff_modelRoundCapGap {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundCapGap ε r δ θ) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t)
  exact (smoothCap_contDiff ε r δ).sub (contDiff_modelLowerRoundBound hθ hδ hδr hθr)

noncomputable def modelRoundCapFactor (ε r δ θ : ℝ) (t : ℝ) : ℝ :=
  - DifferentialGeometry.Analysis.Calculus.hadamardFactor (modelRoundCapGap ε r δ θ)
      (r ^ 2 + 2 * ε) t

theorem modelRoundCapGap_eq_factor {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (t : ℝ) :
    modelRoundCapGap ε r δ θ t = (r ^ 2 + 2 * ε - t) * modelRoundCapFactor ε r δ θ t := by
  have hsq : 0 < r ^ 2 := lt_trans hθ hθr
  have hr : r ≠ 0 := by
    intro h
    subst h
    nlinarith
  have hD : ContDiff ℝ (⊤ : ℕ∞) (modelRoundCapGap ε r δ θ) :=
    contDiff_modelRoundCapGap hθ hδ hδr hθr
  have hgap0 : modelRoundCapGap ε r δ θ (r ^ 2 + 2 * ε) = 0 := by
    change smoothCap ε r δ (r ^ 2 + 2 * ε) -
      modelLowerRoundBound ε r δ θ (r ^ 2 + 2 * ε) = 0
    rw [portPrivate_138057aa_smoothCap_eq_rSq_of_vertex, portPrivate_138057aa_modelLowerRoundBound_eq_rSq_of_vertex hθ hr]
    ring
  have hhad := DifferentialGeometry.Analysis.Calculus.hadamard_factorization
    (f := modelRoundCapGap ε r δ θ) hD
    (a := r ^ 2 + 2 * ε) (x := t)
  have hhad' : modelRoundCapGap ε r δ θ t =
      (t - (r ^ 2 + 2 * ε)) * DifferentialGeometry.Analysis.Calculus.hadamardFactor
        (modelRoundCapGap ε r δ θ) (r ^ 2 + 2 * ε) t := by
    simpa [hgap0] using hhad
  dsimp [modelRoundCapFactor]
  rw [hhad']
  ring

theorem contDiff_modelRoundCapFactor {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundCapFactor ε r δ θ) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (modelRoundCapGap ε r δ θ) :=
    contDiff_modelRoundCapGap hθ hδ hδr hθr
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    -DifferentialGeometry.Analysis.Calculus.hadamardFactor
      (modelRoundCapGap ε r δ θ) (r ^ 2 + 2 * ε) t)
  exact (DifferentialGeometry.Analysis.Calculus.hadamardFactor_contDiff
    (modelRoundCapGap ε r δ θ) hD (r ^ 2 + 2 * ε)).neg

noncomputable def modelRoundCapQext (ε r δ θ : ℝ) (a b : ℝ) : ℝ :=
  modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a) +
    ((2 * ε + r ^ 2 * b) - (2 * ε + r ^ 2 * b) * a) *
      modelRoundCapFactor ε r δ θ ((2 * ε + r ^ 2 * b) * a)

theorem contDiff_modelRoundCapQext {ε r δ θ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapQext ε r δ θ p.1 p.2) := by
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (2 * ε + r ^ 2 * p.2) * p.1) := by
    fun_prop
  have hL : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1)) :=
    (contDiff_modelLowerRoundBound hθ hδ hδr hθr).comp hinner
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelRoundCapFactor ε r δ θ ((2 * ε + r ^ 2 * p.2) * p.1)) :=
    (contDiff_modelRoundCapFactor hθ hδ hδr hθr).comp hinner
  have hcoef : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (2 * ε + r ^ 2 * p.2) - (2 * ε + r ^ 2 * p.2) * p.1) := by
    fun_prop
  dsimp [modelRoundCapQext]
  exact hL.add (hcoef.mul hH)

theorem portPrivate_138057aa_modelRoundCapInterp_denom_eq {ε r a b : ℝ} (hB : b * r ^ 2 + 2 * ε ≠ 0) :
    (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) =
      (r ^ 2 + 2 * ε - (r ^ 2 * b + 2 * ε) * a) / (r ^ 2 * b + 2 * ε) := by
  field_simp [hB]
  ring

theorem modelRoundCapQeq_Qext {ε r δ θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) {a b : ℝ}
    (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    modelRoundCapQ ε r δ θ a b = modelRoundCapQext ε r δ θ a b := by
  by_cases ha : a = 1
  · have hq := modelRoundCapQ_eq_lowerBound_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ)
      (a := a) (b := b) ha
    rw [hq]
    dsimp [modelRoundCapQext]
    rw [ha]
    simp
  · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha
    let B : ℝ := 2 * ε + r ^ 2 * b
    let t : ℝ := (2 * ε + r ^ 2 * b) * a
    let T : ℝ := r ^ 2 + 2 * ε
    have hBpos : 0 < B := by
      dsimp [B]
      nlinarith only [hε, hb0, sq_nonneg r]
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hBle : B ≤ T := by
      dsimp [B, T]
      nlinarith only [hb1]
    have ht_lt : t < T := by
      dsimp [t, T]
      nlinarith only [ha_lt, hBpos, hBle]
    have htne : t ≠ T := ne_of_lt ht_lt
    have hTtne : T - t ≠ 0 := by
      intro h
      have h' : t = T := by linarith
      exact htne h'
    have hdenom : (1 - a) + (1 - b) * (r ^ 2 / B) = (T - t) / B := by
      have hB' : b * r ^ 2 + 2 * ε ≠ 0 := by
        intro h
        apply hBne
        dsimp [B]
        nlinarith
      dsimp [B, t, T]
      rw [add_comm (2 * ε) (r ^ 2 * b)]
      exact portPrivate_138057aa_modelRoundCapInterp_denom_eq (ε := ε) (r := r) (a := a) (b := b) hB'
    have hQ : modelRoundCapQ ε r δ θ a b =
        modelLowerRoundBound ε r δ θ t + modelRoundCapInterp ε r a b * modelRoundCapGap ε r δ θ t := by
      dsimp [modelRoundCapQ, modelRoundCapGap, t]
      ring
    have hgap : modelRoundCapGap ε r δ θ t = (T - t) * modelRoundCapFactor ε r δ θ t := by
      dsimp [T]
      exact modelRoundCapGap_eq_factor hθ hδ hδr hθr t
    have hmain : modelRoundCapQ ε r δ θ a b =
        modelLowerRoundBound ε r δ θ t + (B - B * a) * modelRoundCapFactor ε r δ θ t := by
      calc
        modelRoundCapQ ε r δ θ a b
            = modelLowerRoundBound ε r δ θ t +
                modelRoundCapInterp ε r a b * modelRoundCapGap ε r δ θ t := hQ
        _ = modelLowerRoundBound ε r δ θ t +
              modelRoundCapInterp ε r a b * ((T - t) * modelRoundCapFactor ε r δ θ t) := by
                rw [hgap]
        _ = modelLowerRoundBound ε r δ θ t +
              (B - B * a) * modelRoundCapFactor ε r δ θ t := by
                congr 1
                dsimp [modelRoundCapInterp]
                rw [show (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) =
                    (1 - a) + (1 - b) * (r ^ 2 / B) by
                  dsimp [B]
                  ring_nf]
                rw [hdenom]
                field_simp [hBne, hTtne]
    rw [hmain]
    rfl

theorem contDiffOn_modelRoundCapQ_closed {ε r δ θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelRoundCapQ ε r δ θ p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  refine (contDiff_modelRoundCapQext (ε := ε) (r := r) (δ := δ) (θ := θ)
    hθ hδ hδr hθr).contDiffOn.congr ?_
  intro p hp
  exact modelRoundCapQeq_Qext hε hθ hδ hδr hθr hp.2.1 hp.2.2.1 hp.2.2.2

theorem modelLowerRoundBound_le_smoothCap {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : 2 * ε < t) :
    modelLowerRoundBound ε r δ θ t ≤ smoothCap ε r δ t := by
  dsimp [modelLowerRoundBound]
  have hsc := modelRoundScale_sq_le_ratio hδ hθ hδr ht
  have hden : 0 < t - 2 * ε := by linarith [ht]
  have hnum : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
  have hratio : modelRoundRatio ε r δ t * (t - 2 * ε) = smoothCap ε r δ t := by
    dsimp [modelRoundRatio]
    have hne : t - 2 * ε ≠ 0 := ne_of_gt hden
    rw [div_mul_cancel₀ _ hne]
  calc
    modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε) ≤
        modelRoundRatio ε r δ t * (t - 2 * ε) :=
      mul_le_mul_of_nonneg_right hsc (le_of_lt hden)
    _ = smoothCap ε r δ t := hratio

theorem modelLowerRoundMap_mem_attached_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (y : MorseModel n) (hy : morseNormalForm hk c y < c - ε) :
    modelAttachedFunction hk c ε r δ (modelLowerRoundMap hk ε r δ θ y) < c := by
  dsimp [modelAttachedFunction]
  rw [modelLowerRoundMap_posPart, modelLowerRoundMap_negPart]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hstrict : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hsplit := morseNormalForm_split hk c y
    nlinarith only [hsplit, hy]
  have ht : 2 * ε < ‖negPart hk y‖ ^ 2 := by
    have hpos0 : 0 ≤ ‖posPart hk y‖ ^ 2 := sq_nonneg _
    nlinarith only [hstrict, hpos0]
  have hscale_pos : 0 < modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) :=
    modelRoundScale_pos hδ hθ hδr hθr
  have hscale2_pos : 0 < modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 :=
    sq_pos_of_pos hscale_pos
  have hlt : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2 <
      modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 *
        (‖negPart hk y‖ ^ 2 - 2 * ε) := by
    exact mul_lt_mul_of_pos_left hstrict hscale2_pos
  have hbnd : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) ≤
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
    modelLowerRoundBound_le_smoothCap hδ hθ hδr ht
  have hmain : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2 <
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hle' : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 *
        (‖negPart hk y‖ ^ 2 - 2 * ε) ≤
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa [modelLowerRoundBound] using hbnd
    exact lt_of_lt_of_le hlt hle'
  nlinarith

theorem morseNorm_le_of_negPart_le_lower {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ : ℝ)
    (hε : 0 ≤ ε) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    {y : MorseModel n} (hneg : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ)
    (hlow : morseNormalForm hk c y ≤ c - ε) :
    morseNorm n y ≤ R₀ := by
  have hsplit := morseNormalForm_split hk c y
  have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    nlinarith only [hsplit, hlow]
  have hpos_le : ‖posPart hk y‖ ^ 2 ≤ r ^ 2 + δ := by nlinarith only [hpos, hneg]
  have hsum : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≤ R₀ ^ 2 := by
    nlinarith only [hneg, hpos_le, hbig, hε]
  have hsq : morseNorm n y ^ 2 ≤ R₀ ^ 2 := by
    rw [morseNorm_sq_eq_negPart_add_posPart hk y]
    exact hsum
  have hnonneg : 0 ≤ morseNorm n y := by
    dsimp [morseNorm]
    exact norm_nonneg _
  have habs : |morseNorm n y| ≤ |R₀| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hnonneg, abs_of_nonneg hR0] at habs

theorem modelLowerRoundBound_eq_smoothCap_of_ge {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : r ^ 2 + 2 * ε ≤ t) :
    modelLowerRoundBound ε r δ θ t = smoothCap ε r δ t := by
  dsimp [modelLowerRoundBound]
  have hτ : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) = 1 := by
    have harg : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
      have hden : 0 < θ := hθ
      exact (le_div_iff₀ hden).2 (by nlinarith only [ht])
    exact Real.smoothTransition.one_of_one_le harg
  have hsc : modelRoundScale ε r δ θ t = Real.sqrt (modelRoundRatio ε r δ t) := by
    dsimp [modelRoundScale]
    rw [hτ]
    ring
  rw [hsc]
  have hden : 0 < t - 2 * ε := by nlinarith only [ht, hδr, hδ]
  have hratio_nonneg : 0 ≤ modelRoundRatio ε r δ t := by
    dsimp [modelRoundRatio]
    exact div_nonneg (smoothCap_nonneg hδ hδr) (le_of_lt hden)
  rw [Real.sq_sqrt hratio_nonneg]
  dsimp [modelRoundRatio]
  rw [div_mul_cancel₀ _ (ne_of_gt hden)]

theorem modelRoundCapInterp_nonneg {ε r a b : ℝ} (hε : 0 < ε) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ modelRoundCapInterp ε r a b := by
  by_cases ha : a = 1
  · rw [modelRoundCapInterp_eq_zero_of_eq_one ha]
  · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha
    have ha' : 1 - a > 0 := by linarith
    dsimp [modelRoundCapInterp]
    have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
    have h2 : 0 ≤ (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      exact mul_nonneg (by nlinarith only [hb1]) (div_nonneg (sq_nonneg r) (le_of_lt h1))
    have hden : 0 < (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      nlinarith only [ha', h2]
    exact div_nonneg (le_of_lt ha') (le_of_lt hden)

theorem modelRoundCapInterp_le_one {ε r a b : ℝ} (hε : 0 < ε) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    modelRoundCapInterp ε r a b ≤ 1 := by
  by_cases ha : a = 1
  · rw [modelRoundCapInterp_eq_zero_of_eq_one ha]
    norm_num
  · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha
    have ha' : 1 - a > 0 := by linarith
    dsimp [modelRoundCapInterp]
    have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
    have h2 : 0 ≤ (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      exact mul_nonneg (by nlinarith only [hb1]) (div_nonneg (sq_nonneg r) (le_of_lt h1))
    have hden : 0 < (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      nlinarith only [ha', h2]
    rw [div_le_iff₀ hden]
    nlinarith only [ha', h2]

theorem modelRoundCapInverse_params {ε r t φ a b : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (htpos : 0 < t) (htr : t < r ^ 2 + 2 * ε) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hphiD : 2 * ε - t ≤ φ * (r ^ 2 + 2 * ε - t))
    (ha : a = t / (t + φ * (r ^ 2 + 2 * ε - t)))
    (hb : b = (t / a - 2 * ε) / r ^ 2) :
    (2 * ε + r ^ 2 * b) * a = t ∧
      t * (1 - a) / (a * (r ^ 2 + 2 * ε - t)) = φ ∧
      0 < a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 := by
  let _ := hε
  let D : ℝ := r ^ 2 + 2 * ε - t
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith only [htr]
  have hden_pos : 0 < t + φ * D := by nlinarith only [htpos, hφ0, hDpos]
  have hden_ne : t + φ * D ≠ 0 := ne_of_gt hden_pos
  have hane_aux : 0 < a := by
    have ha' : a = t / (t + φ * D) := by
      simpa [D] using ha
    rw [ha']
    exact div_pos htpos hden_pos
  have hane : a ≠ 0 := ne_of_gt hane_aux
  have hrec : t / a = t + φ * D := by
    have ha' : a = t / (t + φ * D) := by
      simpa [D] using ha
    rw [ha']
    field_simp [hden_ne]
  have ha1 : a ≤ 1 := by
    have ha' : a = t / (t + φ * D) := by
      simpa [D] using ha
    rw [ha']
    rw [div_le_iff₀ hden_pos]
    nlinarith only [hφ0, hDpos]
  have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hr
  have hmain : (2 * ε + r ^ 2 * b) * a = t := by
    rw [hb]
    have hr2ne : r ^ 2 ≠ 0 := ne_of_gt hr2pos
    field_simp [hr2ne, hane]
    nlinarith only [hrec]
  have hphi : t * (1 - a) / (a * D) = φ := by
    have ha' : a = t / (t + φ * D) := by
      simpa [D] using ha
    have hDne : D ≠ 0 := ne_of_gt hDpos
    rw [ha']
    field_simp [hden_ne, hane_aux, hDne]
    nlinarith only [hDpos]
  have hbnonneg : 0 ≤ b := by
    rw [hb]
    rw [div_nonneg_iff]
    left
    constructor
    · dsimp [D] at hrec
      nlinarith only [hrec, hphiD]
    · exact le_of_lt hr2pos
  have hb1 : b ≤ 1 := by
    rw [hb]
    rw [div_le_iff₀ hr2pos]
    have hrec' : t / a - 2 * ε = φ * D + t - 2 * ε := by nlinarith only [hrec]
    rw [hrec']
    dsimp [D]
    nlinarith only [hφ1, htr, hε, hr]
  exact ⟨hmain, hphi, hane_aux, ha1, hbnonneg, hb1⟩

theorem modelRoundCapQ_le_smoothCap {ε r δ θ a b t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hφ1 : modelRoundCapInterp ε r a b ≤ 1)
    (ht : t = (2 * ε + r ^ 2 * b) * a) :
    modelRoundCapQ ε r δ θ a b ≤ smoothCap ε r δ t := by
  dsimp [modelRoundCapQ]
  have hsc : modelLowerRoundBound ε r δ θ t ≤ smoothCap ε r δ t := by
    by_cases ht0 : 2 * ε < t
    · exact modelLowerRoundBound_le_smoothCap hδ hθ hδr ht0
    · have ht' : t ≤ 2 * ε := le_of_not_gt ht0
      have hb0' : modelLowerRoundBound ε r δ θ t ≤ 0 := by
        dsimp [modelLowerRoundBound]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith only [ht'])
      exact le_trans hb0' (smoothCap_nonneg hδ hδr)
  have hmul : (1 - modelRoundCapInterp ε r a b) *
      (modelLowerRoundBound ε r δ θ t - smoothCap ε r δ t) ≤ 0 := by
    nlinarith only [hφ1, hsc]
  rw [← ht]
  nlinarith only [hmul]

theorem modelRoundCapQ_le_rSq {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    modelRoundCapQ ε r δ θ a b ≤ r ^ 2 := by
  have hφ1 : modelRoundCapInterp ε r a b ≤ 1 := modelRoundCapInterp_le_one hε ha1 hb0 hb1
  have hq : modelRoundCapQ ε r δ θ a b ≤ smoothCap ε r δ ((2 * ε + r ^ 2 * b) * a) :=
    modelRoundCapQ_le_smoothCap hδ hθ hδr hφ1 rfl
  have hsmooth : smoothCap ε r δ ((2 * ε + r ^ 2 * b) * a) ≤ r ^ 2 := by
    dsimp [smoothCap]
    have hB : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 := by nlinarith only [hb1]
    have hB0 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
    have hmul : (2 * ε + r ^ 2 * b) * a ≤ 2 * ε + r ^ 2 * b :=
      by simpa using (mul_le_mul_of_nonneg_left ha1 hB0 : (2 * ε + r ^ 2 * b) * a ≤
        (2 * ε + r ^ 2 * b) * 1)
    have hcoef : (2 * ε + r ^ 2 * b) * a - 2 * ε - r ^ 2 ≤ 0 := by nlinarith only [hmul, hB]
    have hτ : 0 ≤ Real.smoothTransition (((2 * ε + r ^ 2 * b) * a - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
      Real.smoothTransition.nonneg _
    nlinarith only [hcoef, hτ]
  exact le_trans hq hsmooth

noncomputable def modelHandleRoundMap {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (p : StandardHandle k (n - k)) : MorseModel n :=
  recombine hk
    (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
      (p.1 : EuclideanSpace ℝ (Fin k)))
    ((Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
      (p.2 : EuclideanSpace ℝ (Fin (n - k))))

theorem modelHandleRoundMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (p : StandardHandle k (n - k)) :
    negPart hk (modelHandleRoundMap hk ε r δ θ p) =
      (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p.1 : EuclideanSpace ℝ (Fin k))) := by
  dsimp [modelHandleRoundMap]
  rw [negPart_recombine]

theorem modelHandleRoundMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (p : StandardHandle k (n - k)) :
    posPart hk (modelHandleRoundMap hk ε r δ θ p) =
      ((Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k)))) := by
  dsimp [modelHandleRoundMap]
  rw [posPart_recombine]

theorem norm_smul_div_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ) (w : E) (hw : w ≠ 0) :
    ‖((Real.sqrt q / ‖w‖) • w : E)‖ ^ 2 = (Real.sqrt q) ^ 2 := by
  have hw' : ‖w‖ ≠ 0 := by
    intro h
    exact hw (norm_eq_zero.mp h)
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg q) (norm_nonneg w))]
  rw [mul_pow]
  rw [div_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hw')]

theorem modelHandleRoundMap_mem_attached {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (p : StandardHandle k (n - k)) :
    modelHandleRoundMap hk ε r δ θ p ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [modelHandleRoundMap_posPart]
  rw [modelHandleRoundMap_negPart]
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith only [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k)), p.1.2]
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.2.2
    simpa using hle
  have hφ0 : 0 ≤ modelRoundCapInterp ε r a b := by
    exact modelRoundCapInterp_nonneg hε ha1 hb0 hb1
  have hφ1 : modelRoundCapInterp ε r a b ≤ 1 := by
    exact modelRoundCapInterp_le_one hε ha1 hb0 hb1
  have hq_le : modelRoundCapQ ε r δ θ a b ≤ smoothCap ε r δ t := by
    dsimp [modelRoundCapQ]
    have hsc : modelLowerRoundBound ε r δ θ t ≤ smoothCap ε r δ t := by
      by_cases ht : 2 * ε < t
      · exact modelLowerRoundBound_le_smoothCap hδ hθ hδr ht
      · have ht' : t ≤ 2 * ε := le_of_not_gt ht
        have hb0' : modelLowerRoundBound ε r δ θ t ≤ 0 := by
          dsimp [modelLowerRoundBound]
          exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith only [ht'])
        exact le_trans hb0' (smoothCap_nonneg hδ hδr)
    have hmul : (1 - modelRoundCapInterp ε r a b) *
        (modelLowerRoundBound ε r δ θ t - smoothCap ε r δ t) ≤ 0 := by
      nlinarith only [hφ1, hsc]
    nlinarith only [hmul]
  by_cases hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = 0
  · have hzero : ((Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
      rw [hw]
      simp
    rw [hzero]
    norm_num
    exact smoothCap_nonneg hδ hδr
  · have hnorm' := norm_smul_div_norm_sq (modelRoundCapQ ε r δ θ a b)
      (p.2 : EuclideanSpace ℝ (Fin (n - k))) hw
    have hsq : (Real.sqrt (modelRoundCapQ ε r δ θ a b)) ^ 2 ≤ smoothCap ε r δ t := by
      by_cases hq0 : 0 ≤ modelRoundCapQ ε r δ θ a b
      · rw [Real.sq_sqrt hq0]
        exact hq_le
      · have hsqrt : Real.sqrt (modelRoundCapQ ε r δ θ a b) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq0)
        rw [hsqrt]
        norm_num
        exact smoothCap_nonneg hδ hδr
    have hnorm : ‖((Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤
        smoothCap ε r δ t := by
      rw [hnorm']
      exact hsq
    have hneg : ‖(Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p.1 : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k))‖ ^ 2 = t := by
      dsimp [t, b]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      have harg : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        nlinarith only [hε, sq_nonneg (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ : ℝ)]
      rw [Real.sq_sqrt harg]
    simpa [a, b, t, hneg] using hnorm

theorem modelHandleRoundMap_attaching_eq_lower {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (p : StandardHandle k (n - k)) (hp : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1) :
    modelHandleRoundMap hk ε r δ θ p =
      modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p) := by
  rw [← recombine_decompose hk (modelHandleRoundMap hk ε r δ θ p)]
  rw [← recombine_decompose hk (modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p))]
  have hneg : negPart hk (modelHandleRoundMap hk ε r δ θ p) =
      negPart hk (modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p)) := by
    rw [modelHandleRoundMap_negPart]
    rw [modelLowerRoundMap_negPart]
    rw [modelHandleMap_negPart]
  have hpos : posPart hk (modelHandleRoundMap hk ε r δ θ p) =
      posPart hk (modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p)) := by
    rw [modelHandleRoundMap_posPart]
    rw [modelLowerRoundMap_posPart]
    rw [modelHandleMap_posPart]
    let w : EuclideanSpace ℝ (Fin (n - k)) := p.2
    let t : ℝ := 2 * ε + r ^ 2 * ‖w‖ ^ 2
    have hq0 : modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) (‖w‖ ^ 2) =
        modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε) := by
      have hq' := modelRoundCapQ_eq_lowerBound_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ)
        (a := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) (b := ‖w‖ ^ 2) (by
          have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
          nlinarith only [hp])
      dsimp [modelLowerRoundBound] at hq'
      simpa [t] using hq'
    by_cases hw : w = 0
    · simp [w, hw]
    · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hwn)
      have ht : 2 * ε < t := by
        have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
        have hw2 : 0 < ‖w‖ ^ 2 := sq_pos_of_pos hwpos
        have hprod : 0 < r ^ 2 * ‖w‖ ^ 2 := mul_pos hr2 hw2
        dsimp [t]
        nlinarith only [hprod]
      have hsc_nonneg : 0 ≤ modelRoundScale ε r δ θ t := modelRoundScale_nonneg hδ hθ hδr ht
      have hsc_eq : Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
          (‖w‖ ^ 2)) / ‖w‖ = modelRoundScale ε r δ θ t * r := by
        rw [hq0]
        have hte : t - 2 * ε = r ^ 2 * ‖w‖ ^ 2 := by
          dsimp [t]
          ring
        rw [hte]
        have hprod : modelRoundScale ε r δ θ t ^ 2 * (r ^ 2 * ‖w‖ ^ 2) =
            (modelRoundScale ε r δ θ t * r * ‖w‖) ^ 2 := by
          ring
        rw [hprod]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hsc_nonneg (le_of_lt hr)) (norm_nonneg w))]
        field_simp [hwn]
      rw [hsc_eq]
      rw [smul_smul]
      congr 1
      have harg2 : 0 ≤ 2 * ε + r ^ 2 * ‖w‖ ^ 2 := by
        nlinarith only [hε, sq_nonneg ‖w‖]
      have hneg_norm : ‖negPart hk (modelHandleMap hk ε r p)‖ ^ 2 = t := by
        rw [modelHandleMap_negPart]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        rw [mul_pow]
        rw [Real.sq_sqrt harg2]
        have hu : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 := by
          have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
          nlinarith only [hp, hnon]
        dsimp [t]
        rw [hu, mul_one]
      rw [hneg_norm]
  have hpairs : (negPart hk (modelHandleRoundMap hk ε r δ θ p),
      posPart hk (modelHandleRoundMap hk ε r δ θ p)) =
      (negPart hk (modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p)),
        posPart hk (modelLowerRoundMap hk ε r δ θ (modelHandleMap hk ε r p))) := by
    apply Prod.ext
    · exact hneg
    · exact hpos
  exact congrArg (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
    recombine hk q.1 q.2) hpairs

theorem modelRoundCapQ_ge_lowerBound {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hδr : δ < r ^ 2) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 2 * ε < (2 * ε + r ^ 2 * b) * a) :
    modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a) ≤ modelRoundCapQ ε r δ θ a b := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  have hφ0 : 0 ≤ modelRoundCapInterp ε r a b := modelRoundCapInterp_nonneg hε ha1 hb0 hb1
  have hφ1 : modelRoundCapInterp ε r a b ≤ 1 := modelRoundCapInterp_le_one hε ha1 hb0 hb1
  have hsc : modelLowerRoundBound ε r δ θ t ≤ smoothCap ε r δ t :=
    modelLowerRoundBound_le_smoothCap hδ hθ hδr ht
  dsimp [modelRoundCapQ]
  have hmul : 0 ≤ modelRoundCapInterp ε r a b *
      (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := by
    nlinarith only [hφ0, hsc]
  nlinarith only [hmul]

theorem modelRoundGap_lt_zero_of_lt {ε r δ t : ℝ} (hδ : 0 < δ) (ht : t < r ^ 2 + 2 * ε) :
    modelRoundGap ε r δ t < 0 := by
  dsimp [modelRoundGap]
  have hcoef : t - 2 * ε - r ^ 2 < 0 := by nlinarith only [ht]
  have hτ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) < 1 := by
    have harg : (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) < 1 := by
      have hden : 0 < 2 * δ := by positivity
      exact (div_lt_iff₀ hden).2 (by nlinarith only [hδ, ht])
    exact Real.smoothTransition.lt_one_of_lt_one harg
  have hmul : (t - 2 * ε - r ^ 2) *
      (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) < 0 := by
    nlinarith only [hcoef, hτ1]
  change t - 2 * ε - (r ^ 2 + (t - 2 * ε - r ^ 2) *
    Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) < 0
  nlinarith only [hmul]

theorem modelRoundRatio_gt_one_of_lt {ε r δ t : ℝ} (hδ : 0 < δ) (ht : 2 * ε < t)
    (ht0 : t < r ^ 2 + 2 * ε) :
    1 < modelRoundRatio ε r δ t := by
  have hgap : modelRoundGap ε r δ t < 0 := modelRoundGap_lt_zero_of_lt hδ ht0
  dsimp [modelRoundRatio, modelRoundGap] at hgap ⊢
  have hden : 0 < t - 2 * ε := by linarith [ht]
  rw [one_lt_div₀ hden]
  nlinarith only [hgap]

theorem modelRoundScale_sq_lt_ratio {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : 2 * ε < t) (ht0 : t < r ^ 2 + 2 * ε) :
    modelRoundScale ε r δ θ t ^ 2 < modelRoundRatio ε r δ t := by
  have hratio1 : 1 < Real.sqrt (modelRoundRatio ε r δ t) := by
    have hratio : 1 < modelRoundRatio ε r δ t := modelRoundRatio_gt_one_of_lt hδ ht ht0
    have hratio0 : 0 ≤ modelRoundRatio ε r δ t := by nlinarith only [hratio]
    have hsq : 1 < (Real.sqrt (modelRoundRatio ε r δ t)) ^ 2 := by
      rw [Real.sq_sqrt hratio0]
      exact hratio
    have hnon : 0 ≤ Real.sqrt (modelRoundRatio ε r δ t) := Real.sqrt_nonneg _
    nlinarith only [hsq, hnon]
  have hτ1 : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) < 1 := by
    have harg : (t - (r ^ 2 + 2 * ε - θ)) / θ < 1 := by
      have hden : 0 < θ := hθ
      exact (div_lt_iff₀ hden).2 (by nlinarith only [ht0])
    exact Real.smoothTransition.lt_one_of_lt_one harg
  have hscale : modelRoundScale ε r δ θ t < Real.sqrt (modelRoundRatio ε r δ t) := by
    dsimp [modelRoundScale]
    have hmul : (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) *
        (1 - Real.sqrt (modelRoundRatio ε r δ t)) < 0 := by
      nlinarith only [hτ1, hratio1]
    have hring : 1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
          (1 - Real.sqrt (modelRoundRatio ε r δ t)) -
        Real.sqrt (modelRoundRatio ε r δ t) =
        (1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ)) *
          (1 - Real.sqrt (modelRoundRatio ε r δ t)) := by
      ring
    have hsub : 1 - Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
          (1 - Real.sqrt (modelRoundRatio ε r δ t)) -
        Real.sqrt (modelRoundRatio ε r δ t) < 0 := by
      rw [hring]
      exact hmul
    linarith
  have hnon : 0 ≤ modelRoundScale ε r δ θ t := modelRoundScale_nonneg hδ hθ hδr ht
  have hsqrt : 0 ≤ Real.sqrt (modelRoundRatio ε r δ t) := Real.sqrt_nonneg _
  have habs : |modelRoundScale ε r δ θ t| < |Real.sqrt (modelRoundRatio ε r δ t)| := by
    rw [abs_of_nonneg hnon, abs_of_nonneg hsqrt]
    exact hscale
  have hsq' : modelRoundScale ε r δ θ t ^ 2 < (Real.sqrt (modelRoundRatio ε r δ t)) ^ 2 := by
    exact (sq_lt_sq.mpr habs)
  have hratio0 : 0 ≤ modelRoundRatio ε r δ t := by
    have hratio : 1 < modelRoundRatio ε r δ t := modelRoundRatio_gt_one_of_lt hδ ht ht0
    nlinarith only [hratio]
  rw [Real.sq_sqrt hratio0] at hsq'
  exact hsq'

noncomputable def modelCapRoundedLowerFunctionInner {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (y : MorseModel n) : ℝ :=
  c + (1 / 2) *
    (‖posPart hk y‖ ^ (2 : ℕ) - modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ (2 : ℕ)))

theorem contDiff_modelCapRoundedLowerFunctionInner {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelCapRoundedLowerFunctionInner hk c ε r δ θ) := by
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    fun_prop
  have hbound : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2)) :=
    (contDiff_modelLowerRoundBound hθ hδ hδr hθr).comp hneg
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
    c + (1 / 2) * (‖posPart hk y‖ ^ 2 - modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2)))
  exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => c)).add
    (((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (1 / 2 : ℝ))).mul
      (hpos.sub hbound)))

theorem modelCapRoundedLowerFunctionInner_le_c_iff {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (y : MorseModel n) :
    modelCapRoundedLowerFunctionInner hk c ε r δ θ y ≤ c ↔
      y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hscale_pos : 0 < modelRoundScale ε r δ θ t := by
    exact modelRoundScale_pos hδ hθ hδr hθr
  have hscale_ne : modelRoundScale ε r δ θ t ≠ 0 := ne_of_gt hscale_pos
  constructor
  · intro hy
    let z : MorseModel n := recombine hk (negPart hk y)
      ((modelRoundScale ε r δ θ t)⁻¹ • posPart hk y)
    have hround : modelLowerRoundMap hk ε r δ θ z = y := by
      have hneg : negPart hk (modelLowerRoundMap hk ε r δ θ z) = negPart hk y := by
        dsimp [modelLowerRoundMap, z]
        rw [negPart_recombine, negPart_recombine]
      have hpos : posPart hk (modelLowerRoundMap hk ε r δ θ z) = posPart hk y := by
        dsimp [modelLowerRoundMap, z]
        rw [posPart_recombine, negPart_recombine, posPart_recombine]
        change (modelRoundScale ε r δ θ t) • ((modelRoundScale ε r δ θ t)⁻¹ • posPart hk y) = posPart hk y
        rw [smul_smul]
        rw [mul_inv_cancel₀ hscale_ne]
        simp
      rw [← recombine_decompose hk (modelLowerRoundMap hk ε r δ θ z)]
      rw [hneg, hpos]
      exact recombine_decompose hk y
    refine ⟨z, ?_, hround⟩
    change morseNormalForm hk c z ≤ c - ε
    rw [morseNormalForm_split hk c z]
    dsimp [z]
    rw [negPart_recombine, posPart_recombine]
    have hpos' : ‖(modelRoundScale ε r δ θ t)⁻¹ • posPart hk y‖ ^ 2 =
        ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
    have hinner : ‖posPart hk y‖ ^ 2 ≤ modelLowerRoundBound ε r δ θ t := by
      have hy' : c + (1 / 2) *
          (‖posPart hk y‖ ^ 2 - modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2)) ≤ c := by
        simpa [modelCapRoundedLowerFunctionInner] using hy
      nlinarith
    have hinner' : ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 ≤
        t - 2 * ε := by
      have hsq : ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
        dsimp [modelLowerRoundBound]
        have hden : modelRoundScale ε r δ θ t ^ 2 ≠ 0 := pow_ne_zero 2 hscale_ne
        field_simp [hden]
      nlinarith only [hinner, hsq]
    have hz : c + (1 / 2) * (((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 - t) ≤ c - ε := by
      nlinarith only [hinner']
    simpa [hpos', t] using hz
  · intro hy
    rcases hy with ⟨z, hz, hzr⟩
    rw [← hzr]
    dsimp [modelCapRoundedLowerFunctionInner]
    rw [modelLowerRoundMap_posPart, modelLowerRoundMap_negPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    have hle : ‖posPart hk z‖ ^ 2 ≤ ‖negPart hk z‖ ^ 2 - 2 * ε := by
      have hsplit := morseNormalForm_split hk c z
      change morseNormalForm hk c z ≤ c - ε at hz
      nlinarith only [hsplit, hz]
    have hmain : modelRoundScale ε r δ θ (‖negPart hk z‖ ^ 2) ^ 2 *
        ‖posPart hk z‖ ^ 2 ≤
        modelLowerRoundBound ε r δ θ (‖negPart hk z‖ ^ 2) := by
      dsimp [modelLowerRoundBound]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg (modelRoundScale ε r δ θ (‖negPart hk z‖ ^ 2)))
    nlinarith only [hmain]

theorem modelLowerRoundBound_lt_smoothCap {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht : 2 * ε < t) (ht0 : t < r ^ 2 + 2 * ε) :
    modelLowerRoundBound ε r δ θ t < smoothCap ε r δ t := by
  dsimp [modelLowerRoundBound]
  have hsc := modelRoundScale_sq_lt_ratio hδ hθ hδr ht ht0
  have hden : 0 < t - 2 * ε := by linarith [ht]
  have hratio : modelRoundRatio ε r δ t * (t - 2 * ε) = smoothCap ε r δ t := by
    dsimp [modelRoundRatio]
    have hne : t - 2 * ε ≠ 0 := ne_of_gt hden
    rw [div_mul_cancel₀ _ hne]
  have hmul : modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε) <
      modelRoundRatio ε r δ t * (t - 2 * ε) := by
    exact mul_lt_mul_of_pos_right hsc hden
  nlinarith only [hmul, hratio]

theorem modelLowerRoundBound_lt_smoothCap_of_lt {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (ht0 : t < r ^ 2 + 2 * ε) :
    modelLowerRoundBound ε r δ θ t < smoothCap ε r δ t := by
  by_cases ht2 : 2 * ε < t
  · exact modelLowerRoundBound_lt_smoothCap hδ hθ hδr ht2 ht0
  · have htle : t ≤ 2 * ε := le_of_not_gt ht2
    have hbnd : modelLowerRoundBound ε r δ θ t ≤ 0 := by
      dsimp [modelLowerRoundBound]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith only [htle])
    have hsm : 0 < smoothCap ε r δ t := smoothCap_pos hδ hδr
    nlinarith only [hbnd, hsm]

theorem modelRoundCapQ_eq_lowerBound_imp_eq_one {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hδr : δ < r ^ 2) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 2 * ε < (2 * ε + r ^ 2 * b) * a)
    (hq : modelRoundCapQ ε r δ θ a b =
      modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a)) :
    a = 1 := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  by_cases ht0 : t < r ^ 2 + 2 * ε
  · have hlt : modelLowerRoundBound ε r δ θ t < smoothCap ε r δ t :=
      modelLowerRoundBound_lt_smoothCap hδ hθ hδr ht ht0
    have hφ0 : modelRoundCapInterp ε r a b = 0 := by
      have hq' : (1 - modelRoundCapInterp ε r a b) * modelLowerRoundBound ε r δ θ t +
          modelRoundCapInterp ε r a b * smoothCap ε r δ t =
          modelLowerRoundBound ε r δ θ t := by
        simpa [modelRoundCapQ, t] using hq
      have hmul : modelRoundCapInterp ε r a b *
          (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) = 0 := by
        nlinarith only [hq']
      have hdiff : smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t ≠ 0 := by linarith [hlt]
      exact (mul_eq_zero.mp hmul).resolve_right hdiff
    have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
    have h2 : 0 ≤ (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      exact mul_nonneg (by nlinarith only [hb1]) (div_nonneg (sq_nonneg r) (le_of_lt h1))
    by_cases ha1' : a = 1
    · exact ha1'
    · have ha : 0 < 1 - a := by
        have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha1'
        linarith
      have hden : (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) ≠ 0 := by
        nlinarith only [ha, h2]
      have hnum : 1 - a = 0 := by
        dsimp [modelRoundCapInterp] at hφ0
        exact (div_eq_zero_iff.mp hφ0).resolve_right hden
      nlinarith only [hnum]
  · have ht0' : r ^ 2 + 2 * ε ≤ t := le_of_not_gt ht0
    have h1 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
    have h2 : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 := by nlinarith only [hb1]
    have h3 : (2 * ε + r ^ 2 * b) * a ≤ (2 * ε + r ^ 2) * a :=
      mul_le_mul_of_nonneg_right h2 ha0
    have h5 : 0 ≤ 2 * ε + r ^ 2 := by nlinarith only [hε]
    have h4 : (2 * ε + r ^ 2) * a ≤ 2 * ε + r ^ 2 :=
      mul_le_of_le_one_right h5 ha1
    have hle : t ≤ r ^ 2 + 2 * ε := by
      dsimp [t]
      nlinarith only [h3, h4]
    have heq : t = r ^ 2 + 2 * ε := le_antisymm hle ht0'
    have hden : 2 * ε + r ^ 2 * b ≠ 0 := ne_of_gt (by nlinarith only [hε, hb0, sq_nonneg r])
    have hdiv : (2 * ε + r ^ 2) / (2 * ε + r ^ 2 * b) ≤ a := by
      have hmain : 2 * ε + r ^ 2 ≤ a * (2 * ε + r ^ 2 * b) := by
        dsimp [t] at heq
        nlinarith only [heq]
      exact (div_le_iff₀ (by nlinarith only [hε, hb0, sq_nonneg r])).2 hmain
    have hdiv1 : 1 ≤ (2 * ε + r ^ 2) / (2 * ε + r ^ 2 * b) := by
      rw [one_le_div₀ (by nlinarith only [hε, hb0, sq_nonneg r])]
      exact h2
    have ha_ge : 1 ≤ a := le_trans hdiv1 hdiv
    exact le_antisymm ha1 ha_ge

theorem modelRoundScale_pos_of_ge {ε r δ θ t : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) (ht : 2 * ε ≤ t) :
    0 < modelRoundScale ε r δ θ t := by
  by_cases ht0 : 2 * ε < t
  · by_cases ht1 : t ≤ r ^ 2 + 2 * ε
    · have hratio1 : 1 ≤ Real.sqrt (modelRoundRatio ε r δ t) := by
        by_cases ht2 : t < r ^ 2 + 2 * ε
        · have hgt : 1 < modelRoundRatio ε r δ t := modelRoundRatio_gt_one_of_lt hδ ht0 ht2
          have hratio0 : 0 ≤ modelRoundRatio ε r δ t := by nlinarith only [hgt]
          have hsq : 1 < (Real.sqrt (modelRoundRatio ε r δ t)) ^ 2 := by
            rw [Real.sq_sqrt hratio0]
            exact hgt
          have hnon : 0 ≤ Real.sqrt (modelRoundRatio ε r δ t) := Real.sqrt_nonneg _
          nlinarith only [hsq, hnon]
        · have ht2' : r ^ 2 + 2 * ε ≤ t := le_of_not_gt ht2
          have heq : t = r ^ 2 + 2 * ε := le_antisymm ht1 ht2'
          have hcap : smoothCap ε r δ t = t - 2 * ε := by
            subst t
            dsimp [smoothCap]
            ring
          dsimp [modelRoundRatio]
          rw [hcap]
          have hdiv : (t - 2 * ε) / (t - 2 * ε) = 1 := div_self (by
            have hpos : 0 < t - 2 * ε := by linarith [ht0]
            linarith)
          rw [hdiv]
          rw [Real.sqrt_one]
      have hτ0 : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) :=
        Real.smoothTransition.nonneg _
      have hle : 1 - Real.sqrt (modelRoundRatio ε r δ t) ≤ 0 := by nlinarith only [hratio1]
      have hmul : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - θ)) / θ) *
          (1 - Real.sqrt (modelRoundRatio ε r δ t)) ≤ 0 := by
        nlinarith only [hτ0, hle]
      dsimp [modelRoundScale]
      nlinarith only [hmul]
    · have ht1' : r ^ 2 + 2 * ε < t := lt_of_not_ge ht1
      have hτ1 : 1 ≤ (t - (r ^ 2 + 2 * ε - θ)) / θ := by
        have hden : 0 < θ := hθ
        exact (le_div_iff₀ hden).2 (by nlinarith only [ht1'])
      dsimp [modelRoundScale]
      rw [Real.smoothTransition.one_of_one_le hτ1]
      have hden : 0 < t - 2 * ε := by linarith [ht0]
      have hnum : 0 < smoothCap ε r δ t := smoothCap_pos hδ hδr
      have hratio : 0 < smoothCap ε r δ t / (t - 2 * ε) := div_pos hnum hden
      have hsqrt : 0 < Real.sqrt (smoothCap ε r δ t / (t - 2 * ε)) := Real.sqrt_pos.2 hratio
      dsimp [modelRoundRatio]
      nlinarith only [hsqrt]
  · have ht' : t = 2 * ε := le_antisymm (le_of_not_gt ht0) ht
    have hsc : modelRoundScale ε r δ θ (2 * ε) = 1 := by
      dsimp [modelRoundScale]
      have harg : (2 * ε - (r ^ 2 + 2 * ε - θ)) / θ ≤ 0 := by
        have hden : 0 < θ := hθ
        exact (div_le_iff₀ hden).2 (by nlinarith only [hθr])
      rw [Real.smoothTransition.zero_of_nonpos harg]
      simp [modelRoundRatio]
    rw [ht', hsc]
    norm_num

theorem modelLowerRoundMap_injective {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    {y z : MorseModel n} (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε))
    (h : modelLowerRoundMap hk ε r δ θ y = modelLowerRoundMap hk ε r δ θ z) : y = z := by
  have hneg : negPart hk y = negPart hk z := by
    have hneg' := congrArg (negPart hk) h
    simpa [modelLowerRoundMap_negPart] using hneg'
  have hpos : posPart hk y = posPart hk z := by
    have hpos' := congrArg (posPart hk) h
    rw [modelLowerRoundMap_posPart, modelLowerRoundMap_posPart] at hpos'
    have ht : ‖negPart hk y‖ ^ 2 = ‖negPart hk z‖ ^ 2 := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin k) => ‖v‖ ^ 2) hneg
    have hsc : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) =
        modelRoundScale ε r δ θ (‖negPart hk z‖ ^ 2) := by
      rw [ht]
    have hsc_pos : 0 < modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) := by
      have hle : 2 * ε ≤ ‖negPart hk y‖ ^ 2 := by
        have hsplit := morseNormalForm_split hk c y
        change morseNormalForm hk c y ≤ c - ε at hy
        have hpos0 : 0 ≤ ‖posPart hk y‖ ^ 2 := sq_nonneg _
        nlinarith only [hsplit, hy, hpos0]
      exact modelRoundScale_pos_of_ge hδ hθ hδr hθr hle
    have hsmul : (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) •
        posPart hk y : EuclideanSpace ℝ (Fin (n - k))) =
        modelRoundScale ε r δ θ (‖negPart hk z‖ ^ 2) • posPart hk z := hpos'
    rw [← hsc] at hsmul
    exact (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r :=
      modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)) (ne_of_gt hsc_pos)) hsmul
  rw [← recombine_decompose hk y, ← recombine_decompose hk z]
  have hpairs : (negPart hk y, posPart hk y) = (negPart hk z, posPart hk z) := by
    apply Prod.ext
    · exact hneg
    · exact hpos
  exact congrArg (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
    recombine hk q.1 q.2) hpairs

noncomputable def modelLowerRoundMapUnround {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2))⁻¹ • posPart hk y)

theorem modelLowerRoundMapUnround_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (y : MorseModel n) :
    negPart hk (modelLowerRoundMapUnround hk ε r δ θ y) = negPart hk y := by
  dsimp [modelLowerRoundMapUnround]
  rw [negPart_recombine]

theorem modelLowerRoundMapUnround_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (y : MorseModel n) :
    posPart hk (modelLowerRoundMapUnround hk ε r δ θ y) =
      (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2))⁻¹ • posPart hk y := by
  dsimp [modelLowerRoundMapUnround]
  rw [posPart_recombine]

theorem contDiff_modelLowerRoundMapUnround {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLowerRoundMapUnround hk ε r δ θ) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)) :=
    (contDiff_modelRoundScale hθ hδ hδr hθr).comp (contDiff_negPart_normSq hk)
  have hsc_inv : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2))⁻¹) :=
    hsc.inv (fun y => ne_of_gt (modelRoundScale_pos hδ hθ hδr hθr))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcoord : (fun y : MorseModel n => modelLowerRoundMapUnround hk ε r δ θ y i) =
        fun y : MorseModel n => (negPart hk y) ⟨i.val, hi⟩ := by
      funext y
      have hneq : i = negIdx hk ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMapUnround hk ε r δ θ y)]
      rw [recombine_negPart hk (negPart hk (modelLowerRoundMapUnround hk ε r δ θ y))
        (posPart hk (modelLowerRoundMapUnround hk ε r δ θ y)) ⟨i.val, hi⟩]
      rw [modelLowerRoundMapUnround_negPart]
    rw [hcoord]
    fun_prop
  · have hi' : i.val - k < n - k := by
      omega
    have hcoord : (fun y : MorseModel n => modelLowerRoundMapUnround hk ε r δ θ y i) =
        fun y : MorseModel n =>
          (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2))⁻¹ * (posPart hk y) ⟨i.val - k, hi'⟩ := by
      funext y
      have hneq : i = posIdx hk ⟨i.val - k, hi'⟩ := by
        apply Fin.ext
        dsimp [posIdx]
        omega
      conv_lhs => rw [hneq]
      rw [← recombine_decompose hk (modelLowerRoundMapUnround hk ε r δ θ y)]
      rw [recombine_posPart hk (negPart hk (modelLowerRoundMapUnround hk ε r δ θ y))
        (posPart hk (modelLowerRoundMapUnround hk ε r δ θ y)) ⟨i.val - k, hi'⟩]
      rw [modelLowerRoundMapUnround_posPart]
      simp
    rw [hcoord]
    fun_prop

theorem contMDiff_modelLowerRoundMapUnround {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) :
    ContMDiff (modelWithCornersSelf ℝ (MorseModel n)) (modelWithCornersSelf ℝ (MorseModel n)) (⊤ : ℕ∞)
      (modelLowerRoundMapUnround hk ε r δ θ) :=
  contMDiff_iff_contDiff.mpr (contDiff_modelLowerRoundMapUnround hk ε r δ θ hθ hδ hδr hθr)

theorem modelLowerRoundMapUnround_round {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (z : MorseModel n) :
    modelLowerRoundMapUnround hk ε r δ θ (modelLowerRoundMap hk ε r δ θ z) = z := by
  let t : ℝ := ‖negPart hk z‖ ^ 2
  have hscale_pos : 0 < modelRoundScale ε r δ θ t := modelRoundScale_pos hδ hθ hδr hθr
  have hscale_ne : modelRoundScale ε r δ θ t ≠ 0 := ne_of_gt hscale_pos
  have hneg : negPart hk (modelLowerRoundMapUnround hk ε r δ θ (modelLowerRoundMap hk ε r δ θ z)) =
      negPart hk z := by
    dsimp [modelLowerRoundMapUnround, modelLowerRoundMap]
    rw [negPart_recombine, negPart_recombine]
  have hpos : posPart hk (modelLowerRoundMapUnround hk ε r δ θ (modelLowerRoundMap hk ε r δ θ z)) =
      posPart hk z := by
    dsimp [modelLowerRoundMapUnround, modelLowerRoundMap]
    rw [posPart_recombine, negPart_recombine, posPart_recombine]
    change (modelRoundScale ε r δ θ t)⁻¹ • (modelRoundScale ε r δ θ t • posPart hk z) = posPart hk z
    rw [smul_smul]
    rw [inv_mul_cancel₀ hscale_ne]
    simp
  rw [← recombine_decompose hk (modelLowerRoundMapUnround hk ε r δ θ (modelLowerRoundMap hk ε r δ θ z))]
  rw [hneg, hpos]
  exact recombine_decompose hk z

theorem modelLowerRoundMap_unround {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε))) :
    modelLowerRoundMap hk ε r δ θ (modelLowerRoundMapUnround hk ε r δ θ y) = y := by
  rcases hy with ⟨z, hz, hzr⟩
  rw [← hzr]
  rw [modelLowerRoundMapUnround_round hk ε r δ θ hθ hδ hδr hθr z]

theorem modelLowerRoundMapUnround_mem_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε))) :
    modelLowerRoundMapUnround hk ε r δ θ y ∈ sublevel (morseNormalForm hk c) (c - ε) := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hscale_pos : 0 < modelRoundScale ε r δ θ t := modelRoundScale_pos hδ hθ hδr hθr
  have hscale_ne : modelRoundScale ε r δ θ t ≠ 0 := ne_of_gt hscale_pos
  have hinner : modelCapRoundedLowerFunctionInner hk c ε r δ θ y ≤ c :=
    (modelCapRoundedLowerFunctionInner_le_c_iff hk c ε r δ θ hθ hδ hδr hθr y).mpr hy
  change morseNormalForm hk c (modelLowerRoundMapUnround hk ε r δ θ y) ≤ c - ε
  dsimp [modelLowerRoundMapUnround]
  rw [morseNormalForm_split]
  rw [negPart_recombine, posPart_recombine]
  have hpos' : ‖(modelRoundScale ε r δ θ t)⁻¹ • posPart hk y‖ ^ 2 =
      ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  have hinner_ineq : ‖posPart hk y‖ ^ 2 ≤ modelLowerRoundBound ε r δ θ t := by
    change c + (1 / 2) * (‖posPart hk y‖ ^ 2 - modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2)) ≤ c at hinner
    nlinarith
  have hinner' : ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 ≤
      t - 2 * ε := by
    have hsq : ((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
      dsimp [modelLowerRoundBound]
      have hden : modelRoundScale ε r δ θ t ^ 2 ≠ 0 := pow_ne_zero 2 hscale_ne
      field_simp [hden]
    nlinarith only [hinner_ineq, hsq]
  have hz : c + (1 / 2) * (((modelRoundScale ε r δ θ t)⁻¹) ^ 2 * ‖posPart hk y‖ ^ 2 - t) ≤ c - ε := by
    nlinarith only [hinner']
  simpa [hpos', t] using hz

theorem modelLowerRoundMap_norm_sq_le {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε)) :
    morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
  have hatt : ‖posPart hk (modelLowerRoundMap hk ε r δ θ y)‖ ^ 2 ≤
      smoothCap ε r δ (‖negPart hk (modelLowerRoundMap hk ε r δ θ y)‖ ^ 2) := by
    simpa [modelAttachedRegion] using
      (modelLowerRoundMap_mem_attached hk c ε r δ θ hδ hθ hδr y hy)
  rw [modelLowerRoundMap_negPart] at hatt
  rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLowerRoundMap hk ε r δ θ y)]
  rw [modelLowerRoundMap_negPart]
  nlinarith only [hatt]

theorem modelLowerRoundMapUnround_norm_sq_le {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε))) :
    morseNorm n (modelLowerRoundMapUnround hk ε r δ θ y) ^ 2 ≤
      2 * ‖negPart hk y‖ ^ 2 - 2 * ε := by
  have hsub := modelLowerRoundMapUnround_mem_sublevel hk c ε r δ θ hθ hδ hδr hθr hy
  have hneg : negPart hk (modelLowerRoundMapUnround hk ε r δ θ y) = negPart hk y := by
    dsimp [modelLowerRoundMapUnround]
    rw [negPart_recombine]
  rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLowerRoundMapUnround hk ε r δ θ y)]
  rw [hneg]
  have hle : ‖posPart hk (modelLowerRoundMapUnround hk ε r δ θ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hsplit := morseNormalForm_split hk c (modelLowerRoundMapUnround hk ε r δ θ y)
    rw [hneg] at hsplit
    change morseNormalForm hk c (modelLowerRoundMapUnround hk ε r δ θ y) ≤ c - ε at hsub
    nlinarith only [hsplit, hsub]
  nlinarith only [hle]

theorem modelLowerRoundMap_norm_sq_le_of_negPart_le {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε))
    (ht : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ) :
    morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2 ≤ 2 * (r ^ 2 + 2 * ε + δ) := by
  have hle := modelLowerRoundMap_norm_sq_le hk c ε r δ θ hδ hθ hδr hy
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ r ^ 2 + 2 * ε + δ := by
    have hr : r ^ 2 ≤ r ^ 2 + 2 * ε + δ := by nlinarith only [hε, hδ]
    exact le_trans (smoothCap_le_max hε hδ (t := ‖negPart hk y‖ ^ 2)) (max_le hr ht)
  nlinarith only [hle, hcap, ht]

theorem modelLowerRoundMapUnround_norm_sq_le_of_negPart_le {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 ≤ ε) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)))
    (ht : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ) :
    morseNorm n (modelLowerRoundMapUnround hk ε r δ θ y) ^ 2 ≤ 2 * (r ^ 2 + 2 * ε + δ) := by
  have hle := modelLowerRoundMapUnround_norm_sq_le hk c ε r δ θ hθ hδ hδr hθr hy
  nlinarith only [hε, hle, ht]

theorem modelLowerRoundMapUnround_eq_self_of_ge {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) {y : MorseModel n}
    (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelLowerRoundMapUnround hk ε r δ θ y = y := by
  rw [← recombine_decompose hk y]
  dsimp [modelLowerRoundMapUnround]
  rw [negPart_recombine, posPart_recombine]
  rw [modelRoundScale_eq_one_of_ge hθ hδ ht]
  simp

theorem modelLowerRoundMap_morseNorm_le_max {n k : ℕ} (hk : k ≤ n) (c ε r δ θ R₀ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε)) :
    morseNorm n (modelLowerRoundMap hk ε r δ θ y) ≤ max R₀ (morseNorm n y) := by
  by_cases hle : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ
  · have hnormle := modelLowerRoundMap_norm_sq_le_of_negPart_le hk c ε r δ θ hε hδ hθ hδr hy hle
    have hsq : morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2 ≤ R₀ ^ 2 := by
      nlinarith only [hnormle, hbig]
    have habs := sq_le_sq.mp hsq
    have hnonneg : 0 ≤ morseNorm n (modelLowerRoundMap hk ε r δ θ y) := norm_nonneg _
    rw [abs_of_nonneg hnonneg, abs_of_nonneg hR0] at habs
    exact le_trans habs (le_max_left _ _)
  · have hgt : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := le_of_not_ge hle
    have hself := modelLowerRoundMap_eq_self_of_ge hk ε r δ θ hθ hδ y hgt
    rw [hself]
    exact le_max_right _ _

theorem modelLowerRoundMapGlobal_morseNorm_le_max {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η R₀ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hη : 0 < η) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy : y ∈ sublevel (morseNormalForm hk c) (c - ε)) :
    morseNorm n (modelLowerRoundMapGlobal hk c ε r δ θ η y) ≤ max R₀ (morseNorm n y) := by
  rw [modelLowerRoundMapGlobal_eq_modelLowerRoundMap_of_sublevel hk c ε r δ θ η hη hy]
  exact modelLowerRoundMap_morseNorm_le_max hk c ε r δ θ R₀ hε hδ hθ hδr hR0 hbig hy

theorem modelLowerRoundMap_morseNorm_le_max_two_of_near_sublevel {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ η R₀ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hη : 0 < η) (hηθ : 2 * η ≤ r ^ 2 - θ) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (y : MorseModel n)
    (hy : morseNormalForm hk c y < c - ε + η) :
    morseNorm n (modelLowerRoundMap hk ε r δ θ y) ≤ max (2 * R₀) (morseNorm n y) := by
  by_cases hneg : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2
  · have hself := modelLowerRoundMap_eq_self_of_ge hk ε r δ θ hθ hδ y hneg
    rw [hself]
    exact le_max_right _ _
  · have hneg_lt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hneg
    by_cases hsmall : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε - θ
    · have hscale1 : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) = 1 :=
        modelRoundScale_eq_one_of_le hθ hsmall
      have hself : modelLowerRoundMap hk ε r δ θ y = y := by
        dsimp [modelLowerRoundMap]
        rw [hscale1]
        simp only [one_smul]
        exact recombine_decompose hk y
      rw [hself]
      exact le_max_right _ _
    · have hmid : r ^ 2 + 2 * ε - θ < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hsmall
      have hθr : θ < r ^ 2 := by nlinarith only [hηθ, hη]
      have h2ε : 2 * ε < ‖negPart hk y‖ ^ 2 := by nlinarith only [hmid, hθr]
      have hden_pos : 0 < ‖negPart hk y‖ ^ 2 - 2 * ε := by nlinarith only [h2ε]
      have hden_ge : r ^ 2 - θ ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by nlinarith only [hmid]
      have hpos_lt : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 - 2 * ε + 2 * η := by
        rw [morseNormalForm_split hk c y] at hy
        nlinarith only [hy]
      have hpos_le : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε + 2 * η := le_of_lt hpos_lt
      have hratio2 : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 ≤
          smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 - 2 * ε) :=
        modelRoundScale_sq_le_ratio hδ hθ hδr h2ε
      have hηden : 2 * η ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := le_trans hηθ hden_ge
      have hpos_ratio : ‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ 2 := by
        rw [div_le_iff₀ hden_pos]
        nlinarith only [hpos_le, hηden]
      have hcapmul : smoothCap ε r δ (‖negPart hk y‖ ^ 2) * (‖posPart hk y‖ ^ 2 /
          (‖negPart hk y‖ ^ 2 - 2 * ε)) ≤ R₀ ^ 2 := by
        have hcaple : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ r ^ 2 + 2 * ε + δ := by
          have hmax := smoothCap_le_max (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hε hδ
          have hmax2 : max (r ^ 2) (‖negPart hk y‖ ^ 2) ≤ r ^ 2 + 2 * ε + δ :=
            max_le (by nlinarith only [hε, hδ]) (le_of_lt hneg_lt)
          exact le_trans hmax hmax2
        have hcapnonneg : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_nonneg hδ hδr
        have hpos_ratio_nonneg : 0 ≤ ‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 - 2 * ε) :=
          div_nonneg (sq_nonneg _) (le_of_lt hden_pos)
        have hle1 := mul_le_mul_of_nonneg_left hpos_ratio hcapnonneg
        have hle2 := mul_le_mul_of_nonneg_right hcaple hpos_ratio_nonneg
        nlinarith only [hle1, hle2, hbig]
      have hround_pos : ‖modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) • posPart hk y‖ ^ 2 ≤ R₀ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        have hle := mul_le_mul_of_nonneg_right hratio2 (sq_nonneg ‖posPart hk y‖)
        have hrew : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 - 2 * ε)) *
            ‖posPart hk y‖ ^ 2 =
            smoothCap ε r δ (‖negPart hk y‖ ^ 2) * (‖posPart hk y‖ ^ 2 /
              (‖negPart hk y‖ ^ 2 - 2 * ε)) := by
          field_simp [ne_of_gt hden_pos]
        nlinarith only [hle, hrew, hcapmul]
      have hround_norm_sq : morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2 ≤ (2 * R₀) ^ 2 := by
        rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLowerRoundMap hk ε r δ θ y)]
        rw [modelLowerRoundMap_negPart, modelLowerRoundMap_posPart]
        nlinarith only [hround_pos, hneg_lt, hbig]
      have hnon : 0 ≤ morseNorm n (modelLowerRoundMap hk ε r δ θ y) := norm_nonneg _
      have hmaxnon : 0 ≤ 2 * R₀ := by nlinarith only [hR0]
      have habs := sq_le_sq.mp hround_norm_sq
      rw [abs_of_nonneg hnon, abs_of_nonneg hmaxnon] at habs
      exact le_trans habs (le_max_left _ _)

theorem modelLowerRoundMapGlobal_morseNorm_le_max_two {n k : ℕ} (hk : k ≤ n) (c ε r δ θ η R₀ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hη : 0 < η)
    (hηθ : 2 * η ≤ r ^ 2 - θ) (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (y : MorseModel n) :
    morseNorm n (modelLowerRoundMapGlobal hk c ε r δ θ η y) ≤ max (2 * R₀) (morseNorm n y) := by
  by_cases habove : c - ε + η ≤ morseNormalForm hk c y
  · rw [modelLowerRoundMapGlobal_eq_self_of_above hk c ε r δ θ η hη habove]
    exact le_max_right _ _
  · have hbelow : morseNormalForm hk c y < c - ε + η := lt_of_not_ge habove
    have hscale_le : modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 ≤
        max (modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2) (1 : ℝ) := by
      let a : ℝ := modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2)
      let s : ℝ := Real.smoothTransition ((morseNormalForm hk c y - (c - ε)) / η)
      dsimp [modelLowerRoundScaleGlobal, a, s]
      have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
      have hs1 : s ≤ 1 := Real.smoothTransition.le_one _
      have hs10 : 0 ≤ 1 - s := by nlinarith only [hs1]
      have hjensen : (a + s * (1 - a)) ^ 2 ≤ (1 - s) * a ^ 2 + s * (1 : ℝ) ^ 2 := by
        have h : 0 ≤ s * (1 - s) * (a - 1) ^ 2 := by positivity
        nlinarith only [h]
      have hweighted : (1 - s) * a ^ 2 + s * (1 : ℝ) ^ 2 ≤ max (a ^ 2) (1 : ℝ) := by
        rw [one_pow, mul_one]
        have h1 : (1 - s) * a ^ 2 ≤ (1 - s) * max (a ^ 2) (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_max_left (a ^ 2) (1 : ℝ)) hs10
        have h2 : s * 1 ≤ s * max (a ^ 2) (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_max_right (a ^ 2) (1 : ℝ)) hs0
        nlinarith only [h1, h2]
      exact le_trans hjensen hweighted
    have hround_bound := modelLowerRoundMap_morseNorm_le_max_two_of_near_sublevel hk c ε r δ θ η R₀
      hε hδ hθ hδr hη hηθ hR0 hbig y hbelow
    have hnorm : morseNorm n (modelLowerRoundMapGlobal hk c ε r δ θ η y) ^ 2 ≤
        max (morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2) (morseNorm n y ^ 2) := by
      have hsmul_global : ‖modelLowerRoundScaleGlobal hk c ε r δ θ η y • posPart hk y‖ ^ 2 =
          modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsmul_round : ‖modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) • posPart hk y‖ ^ 2 =
          modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLowerRoundMapGlobal hk c ε r δ θ η y)]
      rw [modelLowerRoundMapGlobal_negPart, modelLowerRoundMapGlobal_posPart]
      rw [hsmul_global]
      rw [morseNorm_sq_eq_negPart_add_posPart hk (modelLowerRoundMap hk ε r δ θ y)]
      rw [modelLowerRoundMap_negPart, modelLowerRoundMap_posPart]
      rw [hsmul_round]
      rw [morseNorm_sq_eq_negPart_add_posPart hk y]
      have hpos : 0 ≤ ‖posPart hk y‖ ^ 2 := sq_nonneg _
      by_cases hle : modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 ≤ 1
      · have hσ_le : modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 ≤ 1 := by
          simpa [hle] using hscale_le
        have hmul : modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 * ‖posPart hk y‖ ^ 2 ≤
            ‖posPart hk y‖ ^ 2 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hσ_le hpos
        have hmax : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≤
            max (‖negPart hk y‖ ^ 2 + modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2)
              (‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2) :=
          le_max_right _ _
        nlinarith only [hmul, hmax]
      · have hge : 1 ≤ modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 := le_of_not_ge hle
        have hσ_le : modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 ≤
            modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 := by
          simpa [hge] using hscale_le
        have hmul : modelLowerRoundScaleGlobal hk c ε r δ θ η y ^ 2 * ‖posPart hk y‖ ^ 2 ≤
            modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hσ_le hpos
        have hmax : ‖negPart hk y‖ ^ 2 + modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2 ≤
            max (‖negPart hk y‖ ^ 2 + modelRoundScale ε r δ θ (‖negPart hk y‖ ^ 2) ^ 2 * ‖posPart hk y‖ ^ 2)
              (‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2) :=
          le_max_left _ _
        nlinarith only [hmul, hmax]
    have hmax_le : max (morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2) (morseNorm n y ^ 2) ≤
        max (2 * R₀) (morseNorm n y) ^ 2 := by
      have h1 : morseNorm n (modelLowerRoundMap hk ε r δ θ y) ^ 2 ≤ max (2 * R₀) (morseNorm n y) ^ 2 := by
        have hnon : 0 ≤ morseNorm n (modelLowerRoundMap hk ε r δ θ y) := norm_nonneg _
        have hmaxnon : 0 ≤ max (2 * R₀) (morseNorm n y) := by
          exact le_trans (by nlinarith only [hR0]) (le_max_left _ _)
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg hnon, abs_of_nonneg hmaxnon]
          exact hround_bound)
      have h2 : morseNorm n y ^ 2 ≤ max (2 * R₀) (morseNorm n y) ^ 2 := by
        have hnon : 0 ≤ morseNorm n y := norm_nonneg _
        have hmaxnon : 0 ≤ max (2 * R₀) (morseNorm n y) := by
          exact le_trans (by nlinarith only [hR0]) (le_max_left _ _)
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg hnon, abs_of_nonneg hmaxnon]
          exact le_max_right _ _)
      exact max_le h1 h2
    have hsq := le_trans hnorm hmax_le
    have habs := sq_le_sq.mp hsq
    have hnon : 0 ≤ morseNorm n (modelLowerRoundMapGlobal hk c ε r δ θ η y) := norm_nonneg _
    have hmaxnon : 0 ≤ max (2 * R₀) (morseNorm n y) := by
      exact le_trans (by nlinarith only [hR0]) (le_max_left _ _)
    rw [abs_of_nonneg hnon, abs_of_nonneg hmaxnon] at habs
    exact habs

theorem modelLowerRoundMapUnround_morseNorm_le_max {n k : ℕ} (hk : k ≤ n) (c ε r δ θ R₀ : ℝ)
    (hε : 0 ≤ ε) (hθ : 0 < θ) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (hR0 : 0 ≤ R₀) (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε))) :
    morseNorm n (modelLowerRoundMapUnround hk ε r δ θ y) ≤ max R₀ (morseNorm n y) := by
  by_cases hle : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ
  · have hnormle := modelLowerRoundMapUnround_norm_sq_le_of_negPart_le hk c ε r δ θ hε hθ hδ hδr hθr hy hle
    have hsq : morseNorm n (modelLowerRoundMapUnround hk ε r δ θ y) ^ 2 ≤ R₀ ^ 2 := by
      nlinarith only [hnormle, hbig]
    have habs := sq_le_sq.mp hsq
    have hnonneg : 0 ≤ morseNorm n (modelLowerRoundMapUnround hk ε r δ θ y) := norm_nonneg _
    rw [abs_of_nonneg hnonneg, abs_of_nonneg hR0] at habs
    exact le_trans habs (le_max_left _ _)
  · have hgt : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := le_of_not_ge hle
    have hself := modelLowerRoundMapUnround_eq_self_of_ge hk ε r δ θ hθ hδ hgt
    rw [hself]
    exact le_max_right _ _

theorem modelLowerRoundMap_image_norm_sq_le {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε))) :
    morseNorm n y ^ 2 ≤ ‖negPart hk y‖ ^ 2 + smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
  rcases hy with ⟨z, hz, hzy⟩
  have hle := modelLowerRoundMap_norm_sq_le hk c ε r δ θ hδ hθ hδr hz
  have hneg : negPart hk y = negPart hk z := by
    rw [← hzy]
    exact modelLowerRoundMap_negPart hk ε r δ θ z
  rw [hzy] at hle
  rw [hneg.symm] at hle
  exact hle

theorem modelLowerRoundMap_image_norm_sq_le_of_negPart_le {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) {y : MorseModel n}
    (hy : y ∈ modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)))
    (ht : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε + δ) :
    morseNorm n y ^ 2 ≤ 2 * (r ^ 2 + 2 * ε + δ) := by
  have hle := modelLowerRoundMap_image_norm_sq_le hk c ε r δ θ hδ hθ hδr hy
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ r ^ 2 + 2 * ε + δ := by
    have hr : r ^ 2 ≤ r ^ 2 + 2 * ε + δ := by nlinarith only [hε, hδ]
    exact le_trans (smoothCap_le_max hε hδ (t := ‖negPart hk y‖ ^ 2)) (max_le hr ht)
  nlinarith only [hle, hcap, ht]

theorem modelRoundCapInterp_eq {ε r a b t : ℝ} (hε : 0 < ε) (hr : 0 < r) (ha0 : 0 < a)
    (hb0 : 0 ≤ b) (ht0 : t < r ^ 2 + 2 * ε) (htpos : 0 < t)
    (ht : t = (2 * ε + r ^ 2 * b) * a) :
    modelRoundCapInterp ε r a b = t * (1 - a) / (a * (r ^ 2 + 2 * ε - t)) := by
  have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
  have hta : t / a = 2 * ε + r ^ 2 * b := by
    field_simp [ne_of_gt ha0]
    nlinarith only [ht]
  have h1mb : 1 - b = ((r ^ 2 + 2 * ε) * a - t) / (r ^ 2 * a) := by
    have hrb : r ^ 2 * a * b = t - 2 * ε * a := by
      have hmain : t = 2 * ε * a + r ^ 2 * a * b := by nlinarith only [ht]
      nlinarith only [hmain]
    have hden : r ^ 2 * a ≠ 0 := by
      have hr2 : r ^ 2 ≠ 0 := by
        intro h
        have hsq : r ^ 2 = 0 := h
        nlinarith only [sq_pos_of_pos hr, hsq]
      exact mul_ne_zero hr2 (ne_of_gt ha0)
    rw [eq_div_iff hden]
    ring_nf
    nlinarith only [hrb]
  have hden : (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) =
      a * (r ^ 2 + 2 * ε - t) / t := by
    rw [h1mb]
    have h2 : r ^ 2 * b + 2 * ε = t / a := by nlinarith only [hta]
    rw [h2]
    field_simp [ne_of_gt ha0, ne_of_gt htpos,
      (mul_ne_zero (by
        intro h
        have hsq : r ^ 2 = 0 := h
        nlinarith only [sq_pos_of_pos hr, hsq]) (ne_of_gt ha0))]
    ring
  dsimp [modelRoundCapInterp]
  rw [hden]
  have h8 : a * (r ^ 2 + 2 * ε - t) / t ≠ 0 := by
    have h9 : 0 < a * (r ^ 2 + 2 * ε - t) := by
      have h10 : 0 < r ^ 2 + 2 * ε - t := by nlinarith only [ht0]
      nlinarith only [ha0, h10]
    exact ne_of_gt (div_pos h9 htpos)
  field_simp [ne_of_gt ha0, ne_of_gt htpos, h8]

theorem modelRoundCapInterp_injective_fixed_t {ε r a₁ a₂ b₁ b₂ t : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (ha1₀ : 0 < a₁) (ha2₀ : 0 < a₂) (hb1₀ : 0 ≤ b₁) (hb2₀ : 0 ≤ b₂)
    (ht0 : t < r ^ 2 + 2 * ε) (htpos : 0 < t)
    (ht₁ : t = (2 * ε + r ^ 2 * b₁) * a₁) (ht₂ : t = (2 * ε + r ^ 2 * b₂) * a₂)
    (hφ : modelRoundCapInterp ε r a₁ b₁ = modelRoundCapInterp ε r a₂ b₂) :
    a₁ = a₂ := by
  have hφ1 := modelRoundCapInterp_eq hε hr ha1₀ hb1₀ ht0 htpos ht₁
  have hφ2 := modelRoundCapInterp_eq hε hr ha2₀ hb2₀ ht0 htpos ht₂
  have hD : r ^ 2 + 2 * ε - t ≠ 0 := by
    have hDpos : 0 < r ^ 2 + 2 * ε - t := by nlinarith only [ht0]
    linarith
  have hq : t / (r ^ 2 + 2 * ε - t) ≠ 0 := div_ne_zero (ne_of_gt htpos) hD
  have hmul : t * (1 - a₁) / (a₁ * (r ^ 2 + 2 * ε - t)) =
      t * (1 - a₂) / (a₂ * (r ^ 2 + 2 * ε - t)) := by
    rw [← hφ1, ← hφ2]
    exact hφ
  have hsplit₁ : t * (1 - a₁) / (a₁ * (r ^ 2 + 2 * ε - t)) =
      (1 - a₁) / a₁ * (t / (r ^ 2 + 2 * ε - t)) := by
    field_simp [ne_of_gt ha1₀, hD, ne_of_gt htpos]
  have hsplit₂ : t * (1 - a₂) / (a₂ * (r ^ 2 + 2 * ε - t)) =
      (1 - a₂) / a₂ * (t / (r ^ 2 + 2 * ε - t)) := by
    field_simp [ne_of_gt ha2₀, hD, ne_of_gt htpos]
  have hmul' : (1 - a₁) / a₁ * (t / (r ^ 2 + 2 * ε - t)) =
      (1 - a₂) / a₂ * (t / (r ^ 2 + 2 * ε - t)) := by
    rw [← hsplit₁, ← hsplit₂]
    exact hmul
  have hmain : (1 - a₁) / a₁ = (1 - a₂) / a₂ := by
    exact mul_right_cancel₀ hq hmul'
  have h1 : (1 - a₁) / a₁ = a₁⁻¹ - 1 := by
    field_simp [ne_of_gt ha1₀]
  have h2 : (1 - a₂) / a₂ = a₂⁻¹ - 1 := by
    field_simp [ne_of_gt ha2₀]
  have hrecip : a₁⁻¹ = a₂⁻¹ := by
    have hm : a₁⁻¹ - 1 = a₂⁻¹ - 1 := by
      rw [← h1, ← h2]
      exact hmain
    linarith
  have hinv : (a₁⁻¹)⁻¹ = (a₂⁻¹)⁻¹ := congrArg Inv.inv hrecip
  simpa using hinv

theorem modelRoundCapQ_eq_zero_of_b_eq_zero {ε r δ θ a : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (ha : a ≤ 1) :
    modelRoundCapQ ε r δ θ a 0 = 0 := by
  by_cases ha1 : a = 1
  · have hq' := modelRoundCapQ_eq_lowerBound_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ)
      (a := a) (b := 0) ha1
    rw [hq']
    dsimp [modelLowerRoundBound]
    have hsc : modelRoundScale ε r δ θ (2 * ε + r ^ 2 * 0) = 1 := by
      have hle : 2 * ε + r ^ 2 * 0 ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [hθr]
      exact modelRoundScale_eq_one_of_le hθ hle
    rw [hsc]
    ring_nf
  · have hsc : modelRoundScale ε r δ θ (2 * ε * a) = 1 := by
      have hle : 2 * ε * a ≤ r ^ 2 + 2 * ε - θ := by
        nlinarith only [hε, hθr, ha]
      exact modelRoundScale_eq_one_of_le hθ hle
    have hcap : smoothCap ε r δ (2 * ε * a) = r ^ 2 := by
      have hle : 2 * ε * a ≤ r ^ 2 + 2 * ε - δ := by
        nlinarith only [hε, hδr, ha]
      exact smoothCap_lower hδ hle
    have hlt : a < 1 := lt_of_le_of_ne ha ha1
    have h1 : 0 < 1 - a := by linarith [hlt]
    have h2 : 0 < r ^ 2 / (2 * ε) := div_pos (sq_pos_of_pos hr) (by positivity)
    have hsum : 0 < (1 - a) + r ^ 2 / (2 * ε) := by nlinarith only [h1, h2]
    dsimp [modelRoundCapQ, modelLowerRoundBound, modelRoundCapInterp]
    simp only [sub_zero, add_zero, mul_zero, zero_add, one_mul]
    rw [hsc, hcap]
    have hden2 : (1 - a) * (2 * ε) + r ^ 2 ≠ 0 := by
      have hmul : 2 * ε * ((1 - a) + r ^ 2 / (2 * ε)) = (1 - a) * (2 * ε) + r ^ 2 := by
        field_simp [hε.ne']
      have hprod : 0 < 2 * ε * ((1 - a) + r ^ 2 / (2 * ε)) := mul_pos (by positivity) hsum
      have hpos : 0 < (1 - a) * (2 * ε) + r ^ 2 := by
        rwa [hmul] at hprod
      exact ne_of_gt hpos
    field_simp [hden2]
    ring

theorem modelRoundCapQ_eq_cocore {ε r δ θ b : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    modelRoundCapQ ε r δ θ 0 b = r ^ 2 * b := by
  have hsc : modelRoundScale ε r δ θ 0 = 1 := by
    have hle : 0 ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [hε, hθr]
    exact modelRoundScale_eq_one_of_le hθ hle
  have hcap : smoothCap ε r δ 0 = r ^ 2 := by
    have hle : 0 ≤ r ^ 2 + 2 * ε - δ := by nlinarith only [hε, hδr]
    exact smoothCap_lower hδ hle
  have hφ : modelRoundCapInterp ε r 0 b = (r ^ 2 * b + 2 * ε) / (r ^ 2 + 2 * ε) :=
    modelRoundCapInterp_eq_cocore rfl hε hb0 hb1
  dsimp [modelRoundCapQ, modelLowerRoundBound]
  simp only [mul_zero]
  rw [hφ, hsc, hcap]
  field_simp [hε.ne']
  ring

theorem modelRoundCapQ_algebra_low {ε r a b t : ℝ} (hapos : 0 < a)
    (ht0 : t < r ^ 2 + 2 * ε) (ht : t = (2 * ε + r ^ 2 * b) * a) :
    (1 - t * (1 - a) / (a * (r ^ 2 + 2 * ε - t))) * (t - 2 * ε) +
        t * (1 - a) / (a * (r ^ 2 + 2 * ε - t)) * r ^ 2 = r ^ 2 * b := by
  have hden : a * (r ^ 2 + 2 * ε - t) ≠ 0 := by
    have hd1 : 0 < r ^ 2 + 2 * ε - t := by nlinarith only [ht0]
    have hd : 0 < a * (r ^ 2 + 2 * ε - t) := by nlinarith only [hapos, hd1]
    exact ne_of_gt hd
  have hden2 : a * (r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a) ≠ 0 := by
    rw [ht] at hden
    exact hden
  rw [ht]
  have hD : r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a ≠ 0 := by
    have hd : 0 < r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a := by nlinarith only [ht0, ht]
    exact ne_of_gt hd
  field_simp [hden2, hD]
  ring

theorem modelRoundCapQ_nonneg {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ modelRoundCapQ ε r δ θ a b := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  by_cases ht : 2 * ε ≤ t
  · have hb0' : 0 ≤ modelLowerRoundBound ε r δ θ t := by
      dsimp [modelLowerRoundBound]
      exact mul_nonneg (sq_nonneg _) (by nlinarith only [ht])
    have hφ0 : 0 ≤ modelRoundCapInterp ε r a b := modelRoundCapInterp_nonneg hε ha1 hb0 hb1
    have hφ1 : modelRoundCapInterp ε r a b ≤ 1 := modelRoundCapInterp_le_one hε ha1 hb0 hb1
    have hsc : 0 ≤ smoothCap ε r δ t := smoothCap_nonneg hδ hδr
    have hmul : modelRoundCapInterp ε r a b * smoothCap ε r δ t ≥ 0 := by nlinarith only [hφ0, hsc]
    have hq' : 0 ≤ (1 - modelRoundCapInterp ε r a b) * modelLowerRoundBound ε r δ θ t +
        modelRoundCapInterp ε r a b * smoothCap ε r δ t := by
      nlinarith only [hb0', hφ1, hmul]
    dsimp [modelRoundCapQ]
    simpa [t] using hq'
  · have ht' : t < 2 * ε := lt_of_not_ge ht
    by_cases ha : a = 0
    · have hq0 := modelRoundCapQ_eq_cocore hε hδ hθ hδr hθr hb0 hb1
      rw [ha, hq0]
      exact mul_nonneg (sq_nonneg r) hb0
    · have hapos : 0 < a := by
        by_contra h
        have hle : a ≤ 0 := le_of_not_gt h
        exact ha (le_antisymm hle ha0)
      have h1 : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
      have htpos : 0 < t := by
        dsimp [t]
        exact mul_pos h1 hapos
      have ht0 : t < r ^ 2 + 2 * ε := by
        dsimp [t]
        nlinarith only [ht']
      have hφ := modelRoundCapInterp_eq hε hr hapos hb0 ht0 htpos (by dsimp [t])
      have hbound : modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
        have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [ht', hθr]
        exact modelLowerRoundBound_eq_self_of_le hθ hle
      have hsm : smoothCap ε r δ t = r ^ 2 := by
        have hle : t ≤ r ^ 2 + 2 * ε - δ := by nlinarith only [ht', hδr]
        exact smoothCap_lower hδ hle
      have hq : modelRoundCapQ ε r δ θ a b = r ^ 2 * b := by
        dsimp [modelRoundCapQ]
        rw [hφ, hbound, hsm]
        exact modelRoundCapQ_algebra_low hapos ht0 (by dsimp [t])
      rw [hq]
      exact mul_nonneg (sq_nonneg r) hb0

theorem modelHandleRoundMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p : StandardHandle k (n - k)) :
    ‖posPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
      modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
  rw [modelHandleRoundMap_posPart]
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  have ha0 : 0 ≤ a := by dsimp [a]; exact sq_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith only [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k)), p.1.2]
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.2.2
    simpa using hle
  have hq0 : 0 ≤ modelRoundCapQ ε r δ θ a b :=
    modelRoundCapQ_nonneg hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1
  by_cases hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = 0
  · have hzero : ((Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
      rw [hw]
      simp
    rw [hzero]
    have hq0' : modelRoundCapQ ε r δ θ a b = 0 := by
      have hqz := modelRoundCapQ_eq_zero_of_b_eq_zero hε hδ hθ hδr hθr hr ha1
      simpa [a, b, hw] using hqz
    rw [hq0']
    norm_num
  · have hnorm' := norm_smul_div_norm_sq (modelRoundCapQ ε r δ θ a b)
      (p.2 : EuclideanSpace ℝ (Fin (n - k))) hw
    have hsq : (Real.sqrt (modelRoundCapQ ε r δ θ a b)) ^ 2 = modelRoundCapQ ε r δ θ a b :=
      Real.sq_sqrt hq0
    rw [hnorm', hsq]

theorem modelHandleRoundMap_negPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 ≤ ε) (p : StandardHandle k (n - k)) :
    ‖negPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
      (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
  rw [modelHandleRoundMap_negPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by nlinarith only [hε, sq_nonneg (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ : ℝ)])]

theorem modelHandleRoundMap_norm_le {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p : StandardHandle k (n - k)) :
    morseNorm n (modelHandleRoundMap hk ε r δ θ p) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) := by
  apply le_of_sq_le_sq
  · rw [morseNorm_sq_eq_negPart_add_posPart hk]
    rw [modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p]
    rw [modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p]
    have hsqrt : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 = 2 * ε + 2 * r ^ 2 :=
      Real.sq_sqrt (by nlinarith only [hε, sq_nonneg r])
    have ha1 : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
      have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
      have hle : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := p.1.2
      simpa using sq_le_sq' (by linarith [hnon]) hle
    have hb1 : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
      have hle : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ≤ 1 := p.2.2
      simpa using sq_le_sq' (by linarith [hnon]) hle
    have hneg : (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
      have hb : r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 :=
        by simpa using (mul_le_mul_of_nonneg_left hb1 (sq_nonneg r) :
          r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 * 1)
      have hB : 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
        nlinarith only [hb]
      have hB0 : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        nlinarith only [hε, sq_nonneg (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ : ℝ)]
      calc
        (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
            ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
            ≤ (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left ha1 hB0
        _ = 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by ring
        _ ≤ 2 * ε + r ^ 2 := hB
    have hpos : modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) ≤ r ^ 2 :=
      modelRoundCapQ_le_rSq hε hδ hθ hδr ha1 (sq_nonneg _) hb1
    nlinarith only [hneg, hpos, hsqrt]
  · positivity

theorem modelHandleRoundMap_f_sub {n k : ℕ} (hk : k ≤ n) (c ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleRoundMap hk ε r δ θ p) - (c - ε) =
      (1 / 2) * (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
          (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) -
        (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 + 2 * ε) := by
  rw [morseNormalForm_split hk c (modelHandleRoundMap hk ε r δ θ p)]
  rw [modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p]
  rw [modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p]
  ring

theorem modelHandleRoundMap_attachedFunction_eq_c_of_cocore_eq_one {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) (hr : 0 < r) (p : StandardHandle k (n - k))
    (hp : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ = 1) :
    modelAttachedFunction hk c ε r δ (modelHandleRoundMap hk ε r δ θ p) = c := by
  dsimp [modelAttachedFunction]
  rw [modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p]
  rw [modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p]
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  have hb : b = 1 := by
    dsimp [b]
    rw [hp]
    simp
  have hq : modelRoundCapQ ε r δ θ a b = smoothCap ε r δ ((2 * ε + r ^ 2 * b) * a) := by
    by_cases ha : a = 1
    · rw [modelRoundCapQ_eq_lowerBound_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ) (a := a) (b := b) ha]
      rw [ha]
      have hlb : modelLowerRoundBound ε r δ θ (2 * ε + r ^ 2) = r ^ 2 := by
        simpa [add_comm] using (portPrivate_138057aa_modelLowerRoundBound_eq_rSq_of_vertex (ε := ε) (r := r) (δ := δ)
          (θ := θ) hθ (ne_of_gt hr) : modelLowerRoundBound ε r δ θ (r ^ 2 + 2 * ε) = r ^ 2)
      have hsm : smoothCap ε r δ (2 * ε + r ^ 2) = r ^ 2 := by
        simpa [add_comm] using (portPrivate_138057aa_smoothCap_eq_rSq_of_vertex (ε := ε) (r := r) (δ := δ) :
          smoothCap ε r δ (r ^ 2 + 2 * ε) = r ^ 2)
      simpa [hb, mul_one] using (hlb.trans hsm.symm)
    · have hq' : modelRoundCapQ ε r δ θ a b = smoothCap ε r δ ((2 * ε + r ^ 2) * a) :=
        modelRoundCapQ_eq_smoothCap_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ) (a := a) (b := b)
          hb ha
      simpa [hb] using hq'
  rw [hq]
  ring

theorem modelHandleRoundMap_attachedFunction_lt_c_of_cocore_lt_one {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) (hr : 0 < r) (p : StandardHandle k (n - k))
    (hp : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ < 1) :
    modelAttachedFunction hk c ε r δ (modelHandleRoundMap hk ε r δ θ p) < c := by
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  have ha0 : 0 ≤ a := by dsimp [a]; exact sq_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.1.2
    simpa using hle
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb_lt : b < 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hsq := sq_lt_sq' (by linarith [hnon]) hp
    simpa using hsq
  have ht_le : t ≤ 2 * ε + r ^ 2 * b := by
    dsimp [t]
    have hnonneg : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
    nlinarith only [ha1, hnonneg]
  have ht_lt : t < r ^ 2 + 2 * ε := by
    have hr2b : r ^ 2 * b < r ^ 2 := by
      simpa [mul_one] using mul_lt_mul_of_pos_left hb_lt (sq_pos_of_pos hr)
    nlinarith only [ht_le, hr2b]
  have hφ_lt : modelRoundCapInterp ε r a b < 1 := by
    by_cases ha : a = 1
    · rw [modelRoundCapInterp_eq_zero_of_eq_one ha]
      norm_num
    · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha
      have h1a : 0 < 1 - a := by linarith
      have h1b : 0 < 1 - b := by linarith [hb_lt]
      have hc : 0 < r ^ 2 / (r ^ 2 * b + 2 * ε) :=
        div_pos (sq_pos_of_pos hr) (by nlinarith only [hε, hb0, sq_nonneg r])
      dsimp [modelRoundCapInterp]
      have hden : 0 < (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) :=
        add_pos h1a (mul_pos h1b hc)
      rw [div_lt_one hden]
      nlinarith only [h1b, hc]
  have hgap : modelLowerRoundBound ε r δ θ t < smoothCap ε r δ t :=
    modelLowerRoundBound_lt_smoothCap_of_lt hδ hθ hδr ht_lt
  have hq : modelRoundCapQ ε r δ θ a b < smoothCap ε r δ t := by
    dsimp [modelRoundCapQ]
    have h1φ : 0 < 1 - modelRoundCapInterp ε r a b := by linarith [hφ_lt]
    have hgap' : 0 < smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t := by linarith [hgap]
    have hprod : 0 < (1 - modelRoundCapInterp ε r a b) *
        (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := mul_pos h1φ hgap'
    nlinarith
  dsimp [modelAttachedFunction]
  rw [modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p]
  rw [modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p]
  change c + (1 / 2) * (modelRoundCapQ ε r δ θ a b - smoothCap ε r δ t) < c
  nlinarith only [hq]

theorem modelRoundCapQ_eq_r2b_of_t_lt {ε r δ θ a b t : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (hapos : 0 < a)
    (hb0 : 0 ≤ b) (ht0 : t < r ^ 2 + 2 * ε) (htpos : 0 < t)
    (ht : t ≤ 2 * ε) (hteq : t = (2 * ε + r ^ 2 * b) * a) :
    modelRoundCapQ ε r δ θ a b = r ^ 2 * b := by
  have hφ := modelRoundCapInterp_eq hε hr hapos hb0 ht0 htpos hteq
  have hbound : modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
    have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [ht, hθr]
    exact modelLowerRoundBound_eq_self_of_le hθ hle
  have hsm : smoothCap ε r δ t = r ^ 2 := by
    have hle : t ≤ r ^ 2 + 2 * ε - δ := by nlinarith only [ht, hδr]
    exact smoothCap_lower hδ hle
  dsimp [modelRoundCapQ]
  rw [hteq] at hbound hsm
  rw [hφ, hbound, hsm]
  rw [hteq]
  have hden2 : a * (r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a) ≠ 0 := by
    have hd1 : 0 < r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a := by nlinarith only [ht0, hteq]
    have hd : 0 < a * (r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a) := by nlinarith only [hapos, hd1]
    exact ne_of_gt hd
  have hD : r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a ≠ 0 := by
    have hd : 0 < r ^ 2 + 2 * ε - (2 * ε + r ^ 2 * b) * a := by nlinarith only [ht0, hteq]
    exact ne_of_gt hd
  field_simp [hden2, hD]
  ring

theorem modelRoundCapQ_eq_r2b_of_flat {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hr : 0 < r) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1 - δ / r ^ 2) (hb2 : b < 1 - θ / r ^ 2) :
    modelRoundCapQ ε r δ θ a b = r ^ 2 * b := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  have htδ : t ≤ r ^ 2 + 2 * ε - δ := by
    have h1 : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 - δ := by
      have hdiv : b * r ^ 2 < (1 - δ / r ^ 2) * r ^ 2 :=
        mul_lt_mul_of_pos_right hb1 (sq_pos_of_pos hr)
      have hmain : r ^ 2 * b < r ^ 2 - δ := by
        calc
          r ^ 2 * b = b * r ^ 2 := by ring
          _ < (1 - δ / r ^ 2) * r ^ 2 := hdiv
          _ = r ^ 2 - δ := by
            have hr2ne : r ^ 2 ≠ 0 := by
              intro hz
              nlinarith only [sq_pos_of_pos hr, hz]
            field_simp [hr2ne]
      nlinarith only [hmain]
    have h2 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
    nlinarith only [mul_le_of_le_one_right h2 ha1, h1]
  have htθ : t ≤ r ^ 2 + 2 * ε - θ := by
    have h1 : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 - θ := by
      have hdiv : b * r ^ 2 < (1 - θ / r ^ 2) * r ^ 2 :=
        mul_lt_mul_of_pos_right hb2 (sq_pos_of_pos hr)
      have hmain : r ^ 2 * b < r ^ 2 - θ := by
        calc
          r ^ 2 * b = b * r ^ 2 := by ring
          _ < (1 - θ / r ^ 2) * r ^ 2 := hdiv
          _ = r ^ 2 - θ := by
            have hr2ne : r ^ 2 ≠ 0 := by
              intro hz
              nlinarith only [sq_pos_of_pos hr, hz]
            field_simp [hr2ne]
      nlinarith only [hmain]
    have h2 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
    nlinarith only [mul_le_of_le_one_right h2 ha1, h1]
  have hbound : modelLowerRoundBound ε r δ θ t = t - 2 * ε :=
    modelLowerRoundBound_eq_self_of_le hθ htθ
  have hsm : smoothCap ε r δ t = r ^ 2 := smoothCap_lower hδ htδ
  have hbden : r ^ 2 * b + 2 * ε ≠ 0 := by
    have hpos : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
    exact ne_of_gt hpos
  have hb1' : b < 1 := lt_of_lt_of_le hb1 (by
    have hd : 0 ≤ δ / r ^ 2 := div_nonneg (le_of_lt hδ) (le_of_lt (sq_pos_of_pos hr))
    nlinarith)
  have hD : (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) ≠ 0 := by
    have h₁ : 0 ≤ 1 - a := by linarith [ha1]
    have h₂ : 0 < 1 - b := by linarith [hb1']
    have h₃ : 0 < r ^ 2 / (r ^ 2 * b + 2 * ε) :=
      div_pos (sq_pos_of_pos hr) (by nlinarith only [hε, hb0, sq_nonneg r])
    have hpos : 0 < (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
      nlinarith only [h₁, h₂, h₃]
    exact ne_of_gt hpos
  have hDcl : (1 - a) * (r ^ 2 * b + 2 * ε) + (1 - b) * r ^ 2 ≠ 0 := by
    by_contra hz
    apply hD
    have hmain : (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) =
        ((1 - a) * (r ^ 2 * b + 2 * ε) + (1 - b) * r ^ 2) / (r ^ 2 * b + 2 * ε) := by
      field_simp [hbden]
    rw [hmain, hz]
    simp
  have hDcl' : -(a * r ^ 2 * b) - a * ε * 2 + r ^ 2 + ε * 2 ≠ 0 := by
    have hmain : (1 - a) * (r ^ 2 * b + 2 * ε) + (1 - b) * r ^ 2 =
        -(a * r ^ 2 * b) - a * ε * 2 + r ^ 2 + ε * 2 := by
      ring
    rwa [hmain] at hDcl
  have hφ : modelRoundCapInterp ε r a b =
      (1 - a) * (r ^ 2 * b + 2 * ε) /
        ((1 - a) * (r ^ 2 * b + 2 * ε) + (1 - b) * r ^ 2) := by
    dsimp [modelRoundCapInterp]
    field_simp [hbden, hD]
  let N : ℝ := (1 - a) * (r ^ 2 * b + 2 * ε)
  let Dcl : ℝ := N + (1 - b) * r ^ 2
  have hφ' : modelRoundCapInterp ε r a b = N / Dcl := by
    dsimp [N, Dcl]
    exact hφ
  have hDcl'' : Dcl ≠ 0 := by
    dsimp [Dcl]
    exact hDcl
  have hφD : modelRoundCapInterp ε r a b * Dcl = N := by
    rw [hφ']
    exact div_mul_cancel₀ (b := Dcl) N hDcl''
  have hq : (1 - modelRoundCapInterp ε r a b) * (t - 2 * ε) +
        modelRoundCapInterp ε r a b * r ^ 2 = r ^ 2 * b := by
    apply (mul_right_cancel₀ hDcl'')
    have hmain : ((1 - modelRoundCapInterp ε r a b) * (t - 2 * ε) +
          modelRoundCapInterp ε r a b * r ^ 2) * Dcl = r ^ 2 * b * Dcl := by
      calc
        ((1 - modelRoundCapInterp ε r a b) * (t - 2 * ε) +
            modelRoundCapInterp ε r a b * r ^ 2) * Dcl =
            (t - 2 * ε) * Dcl -
              (t - 2 * ε) * (modelRoundCapInterp ε r a b * Dcl) +
                r ^ 2 * (modelRoundCapInterp ε r a b * Dcl) := by
          ring
        _ = (t - 2 * ε) * Dcl - (t - 2 * ε) * N + r ^ 2 * N := by rw [hφD]
        _ = r ^ 2 * b * Dcl := by
          dsimp [t, N, Dcl]
          ring
    exact hmain
  dsimp [modelRoundCapQ]
  rw [hbound, hsm]
  change (1 - modelRoundCapInterp ε r a b) * (t - 2 * ε) +
      modelRoundCapInterp ε r a b * r ^ 2 = r ^ 2 * b
  exact hq

theorem modelRoundCapQ_pos_of_b_pos {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hb : 0 < b) :
    0 < modelRoundCapQ ε r δ θ a b := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  by_cases ht : 2 * ε ≤ t
  · by_cases ht' : t = 2 * ε
    · have ha_lt : a < 1 := by
        have hmain : (2 * ε + r ^ 2 * b) * a = 2 * ε := by simpa [t] using ht'
        have h1 : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
        have h2 : a = 2 * ε / (2 * ε + r ^ 2 * b) := by
          have h3 : (2 * ε + r ^ 2 * b) * (2 * ε / (2 * ε + r ^ 2 * b)) = 2 * ε :=
            mul_div_cancel₀ _ (ne_of_gt h1)
          nlinarith only [h1, hmain, h3]
        have hden : 2 * ε < 2 * ε + r ^ 2 * b := by
          nlinarith only [mul_pos (sq_pos_of_pos hr) hb]
        have h4 : 2 * ε / (2 * ε + r ^ 2 * b) < 1 := by
          rw [div_lt_one₀ (by nlinarith only [hε, hb0, sq_nonneg r] : 0 < 2 * ε + r ^ 2 * b)]
          exact hden
        rw [h2]
        exact h4
      have hφ_pos : 0 < modelRoundCapInterp ε r a b := by
        have hpos : 0 < 1 - a := by nlinarith only [ha_lt]
        dsimp [modelRoundCapInterp]
        have h1 : 0 < r ^ 2 * b + 2 * ε := by nlinarith only [hε, hb0, sq_nonneg r]
        have h2 : 0 ≤ (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
          exact mul_nonneg (by nlinarith only [hb1]) (div_nonneg (sq_nonneg r) (le_of_lt h1))
        have hden : 0 < (1 - a) + (1 - b) * (r ^ 2 / (r ^ 2 * b + 2 * ε)) := by
          nlinarith only [hpos, h2]
        exact div_pos hpos hden
      have hsc : 0 < smoothCap ε r δ t := smoothCap_pos hδ hδr
      have hbnd : modelLowerRoundBound ε r δ θ t = 0 := by
        have hsc_eq : modelRoundScale ε r δ θ t = 1 := by
          have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [ht', hθr]
          exact modelRoundScale_eq_one_of_le hθ hle
        dsimp [modelLowerRoundBound]
        rw [hsc_eq, ht']
        ring
      dsimp [modelRoundCapQ]
      rw [hbnd]
      have hφ0 : 0 ≤ modelRoundCapInterp ε r a b := le_of_lt hφ_pos
      nlinarith only [mul_pos hφ_pos hsc]
    · have ht2 : 2 * ε < t := lt_of_le_of_ne ht (by
        intro h
        exact ht' h.symm)
      have hbnd_pos : 0 < modelLowerRoundBound ε r δ θ t := by
        have hsc_pos : 0 < modelRoundScale ε r δ θ t := modelRoundScale_pos_of_ge hδ hθ hδr hθr ht
        dsimp [modelLowerRoundBound]
        exact mul_pos (sq_pos_of_pos hsc_pos) (by nlinarith only [ht2])
      have hge : modelLowerRoundBound ε r δ θ t ≤ modelRoundCapQ ε r δ θ a b :=
        modelRoundCapQ_ge_lowerBound hε hδ hθ hδr ha1 hb0 hb1 ht2
      exact lt_of_lt_of_le hbnd_pos hge
  · have ht_lt : t < 2 * ε := lt_of_not_ge ht
    by_cases ha0' : a = 0
    · have hq0 := modelRoundCapQ_eq_cocore hε hδ hθ hδr hθr hb0 hb1
      rw [ha0', hq0]
      exact mul_pos (sq_pos_of_pos hr) hb
    · have ha_pos : 0 < a := by
        by_contra hzero
        have hle : a ≤ 0 := le_of_not_gt hzero
        have : a = 0 := le_antisymm hle ha0
        exact ha0' this
      have ht0 : t < r ^ 2 + 2 * ε := by
        nlinarith only [ht_lt, hr]
      have htpos : 0 < t := by
        have h1 : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
        dsimp [t]
        exact mul_pos h1 ha_pos
      have hq := modelRoundCapQ_eq_r2b_of_t_lt hε hδ hθ hδr hθr hr ha_pos hb0 ht0 htpos
        (le_of_lt ht_lt) (by dsimp [t])
      rw [hq]
      exact mul_pos (sq_pos_of_pos hr) hb

theorem modelRoundCapQ_ge_lowerBound_of_ge {ε r δ θ a b : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 2 * ε ≤ (2 * ε + r ^ 2 * b) * a) :
    modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a) ≤ modelRoundCapQ ε r δ θ a b := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  by_cases ht2 : 2 * ε < t
  · exact modelRoundCapQ_ge_lowerBound hε hδ hθ hδr ha1 hb0 hb1 ht2
  · have hteq : t = 2 * ε := le_antisymm (le_of_not_gt ht2) ht
    have hL : modelLowerRoundBound ε r δ θ t = 0 := by
      have hsc : modelRoundScale ε r δ θ t = 1 := by
        have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [hteq, hθr]
        exact modelRoundScale_eq_one_of_le hθ hle
      dsimp [modelLowerRoundBound]
      rw [hsc, hteq]
      ring
    have hq : 0 ≤ modelRoundCapQ ε r δ θ a b :=
      modelRoundCapQ_nonneg hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1
    rwa [hL]

theorem modelRoundCapQ_eq_lowerBound_imp_eq_one_of_ge {ε r δ θ a b : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 2 * ε ≤ (2 * ε + r ^ 2 * b) * a)
    (hq : modelRoundCapQ ε r δ θ a b =
      modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a)) :
    a = 1 := by
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  by_cases ht2 : 2 * ε < t
  · exact modelRoundCapQ_eq_lowerBound_imp_eq_one hε hδ hθ hδr ha0 ha1 hb0 hb1 ht2 hq
  · have hteq : t = 2 * ε := le_antisymm (le_of_not_gt ht2) ht
    have hL : modelLowerRoundBound ε r δ θ t = 0 := by
      have hsc : modelRoundScale ε r δ θ t = 1 := by
        have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [hteq, hθr]
        exact modelRoundScale_eq_one_of_le hθ hle
      dsimp [modelLowerRoundBound]
      rw [hsc, hteq]
      ring
    have hq0 : modelRoundCapQ ε r δ θ a b = 0 := by
      rw [hq, hL]
    by_cases ha : a = 1
    · exact ha
    · have ha_lt : a < 1 := lt_of_le_of_ne ha1 ha
      by_cases hb0' : b = 0
      · have ht' : t = 2 * ε * a := by
          dsimp [t]
          rw [hb0']
          ring
        have hmain : 2 * ε * a = 2 * ε := by
          have h1 : (2 * ε + r ^ 2 * b) * a = 2 * ε := by
            simpa [t] using hteq
          rw [hb0'] at h1
          simpa using h1
        nlinarith only [hε, ha_lt, hmain]
      · have hb_pos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb0')
        have hqpos : 0 < modelRoundCapQ ε r δ θ a b :=
          modelRoundCapQ_pos_of_b_pos hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1 hb_pos
        nlinarith only [hq0, hqpos]

theorem modelHandleRoundMap_mem_lowerRound_iff {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (p : StandardHandle k (n - k)) :
    modelHandleRoundMap hk ε r δ θ p ∈
        modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  have ha0 : 0 ≤ a := by dsimp [a]; exact sq_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.1.2
    simpa using hle
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.2.2
    simpa using hle
  constructor
  · intro hy
    have hinner : modelCapRoundedLowerFunctionInner hk c ε r δ θ
        (modelHandleRoundMap hk ε r δ θ p) ≤ c :=
      (modelCapRoundedLowerFunctionInner_le_c_iff hk c ε r δ θ hθ hδ hδr hθr
        (modelHandleRoundMap hk ε r δ θ p)).mpr hy
    have hinner' : c + (1 / 2) *
        (modelRoundCapQ ε r δ θ a b - modelLowerRoundBound ε r δ θ t) ≤ c := by
      have hpos := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p
      have hneg := modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p
      simpa [modelCapRoundedLowerFunctionInner, a, b, t, hpos, hneg] using hinner
    have hq_le : modelRoundCapQ ε r δ θ a b ≤ modelLowerRoundBound ε r δ θ t := by
      nlinarith
    have ht : 2 * ε ≤ t := by
      have hq_nonneg : 0 ≤ modelRoundCapQ ε r δ θ a b :=
        modelRoundCapQ_nonneg hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1
      have hL_nonneg : 0 ≤ modelLowerRoundBound ε r δ θ t := by nlinarith only [hq_le, hq_nonneg]
      have hsc_pos : 0 < modelRoundScale ε r δ θ t := modelRoundScale_pos hδ hθ hδr hθr
      have hsc_sq_pos : 0 < modelRoundScale ε r δ θ t ^ 2 := sq_pos_of_pos hsc_pos
      have hLprod : 0 ≤ modelRoundScale ε r δ θ t ^ 2 * (t - 2 * ε) := by
        simpa [modelLowerRoundBound] using hL_nonneg
      have hsub_nonneg : 0 ≤ t - 2 * ε := nonneg_of_mul_nonneg_right hLprod hsc_sq_pos
      nlinarith
    have hq_ge : modelLowerRoundBound ε r δ θ t ≤ modelRoundCapQ ε r δ θ a b :=
      modelRoundCapQ_ge_lowerBound_of_ge hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1 ht
    have hq_eq : modelRoundCapQ ε r δ θ a b = modelLowerRoundBound ε r δ θ t :=
      le_antisymm hq_le hq_ge
    have haeq : a = 1 :=
      modelRoundCapQ_eq_lowerBound_imp_eq_one_of_ge hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1 ht hq_eq
    have hsq : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 := by simpa [a] using haeq
    have hsqor : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∨
        ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = -1 := sq_eq_one_iff.mp hsq
    rcases hsqor with h | h
    · exact h
    · linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
  · intro hp
    rw [modelHandleRoundMap_attaching_eq_lower hk ε r δ θ hε hδ hθ hδr hr p hp]
    refine ⟨modelHandleMap hk ε r p, ?_, rfl⟩
    exact le_of_eq ((modelHandleMap_f_eq_lower_iff hk c ε r hε p).2 hp)

theorem lowerRound_union_handleRound_subset_modelAttachedRegion {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) :
    modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) ∪
        Set.range (modelHandleRoundMap hk ε r δ θ) ⊆ modelAttachedRegion hk ε r δ := by
  intro y hy
  rcases hy with hy | hy
  · rcases hy with ⟨z, hz, hzy⟩
    rw [← hzy]
    exact modelLowerRoundMap_mem_attached hk c ε r δ θ hδ hθ hδr z hz
  · rcases hy with ⟨p, hpy⟩
    rw [← hpy]
    exact modelHandleRoundMap_mem_attached hk ε r δ θ hε hδ hθ hδr p

theorem modelAttachedRegion_mem_handleRound_of_negPart_gt {n k : ℕ} (hk : k ≤ n)
    (ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hr : 0 < r) {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hq_gt : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) < ‖posPart hk y‖ ^ 2)
    (ht2 : 2 * ε < ‖negPart hk y‖ ^ 2) :
    y ∈ Set.range (modelHandleRoundMap hk ε r δ θ) := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let q : ℝ := ‖posPart hk y‖ ^ 2
  let D : ℝ := r ^ 2 + 2 * ε - t
  have hq_le : q ≤ smoothCap ε r δ t := by
    simpa [modelAttachedRegion, t, q] using hy
  have ht_lt : t < r ^ 2 + 2 * ε := by
    by_contra h
    have hge : r ^ 2 + 2 * ε ≤ t := le_of_not_gt h
    have hB : modelLowerRoundBound ε r δ θ t = smoothCap ε r δ t :=
      modelLowerRoundBound_eq_smoothCap_of_ge hδ hθ hδr hge
    have hbad : q ≤ modelLowerRoundBound ε r δ θ t := by
      rw [hB]
      exact hq_le
    nlinarith only [hq_gt, hbad]
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith only [ht_lt]
  have hgap_pos : 0 < smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t := by
    nlinarith only [hq_gt, hq_le]
  let φ : ℝ := (q - modelLowerRoundBound ε r δ θ t) / (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t)
  have hφ0 : 0 ≤ φ := by
    dsimp [φ]
    exact div_nonneg (by nlinarith only [hq_gt]) (le_of_lt hgap_pos)
  have hφ1 : φ ≤ 1 := by
    dsimp [φ]
    rw [div_le_iff₀ hgap_pos]
    nlinarith only [hq_le]
  have hφ_pos : 0 < φ := by
    dsimp [φ]
    exact div_pos (by nlinarith only [hq_gt]) hgap_pos
  have htpos : 0 < t := by nlinarith only [ht2, hε]
  let a : ℝ := t / (t + φ * D)
  let b : ℝ := (t / a - 2 * ε) / r ^ 2
  have hparams := modelRoundCapInverse_params (hε := hε) (hr := hr) (htpos := htpos) (htr := ht_lt)
    (hφ0 := hφ0) (hφ1 := hφ1) (hphiD := by nlinarith only [ht2, hφ0, hDpos]) (ha := by
      rfl) (hb := by
      rfl)
  have ht_eq : (2 * ε + r ^ 2 * b) * a = t := hparams.1
  have ha0 : 0 < a := hparams.2.2.1
  have ha1 : a ≤ 1 := hparams.2.2.2.1
  have hb0 : 0 ≤ b := hparams.2.2.2.2.1
  have hb1 : b ≤ 1 := hparams.2.2.2.2.2
  have hrec : t / a = t + φ * D := by
    have ha' : a = t / (t + φ * D) := by
      rfl
    rw [ha']
    rw [div_div_eq_mul_div]
    rw [mul_div_right_comm]
    rw [div_self (ne_of_gt htpos)]
    rw [one_mul]
  have hb_pos : 0 < b := by
    dsimp [b]
    have hnum : 0 < t / a - 2 * ε := by
      nlinarith only [hrec, hφ_pos, hDpos, ht2]
    exact div_pos hnum (sq_pos_of_pos hr)
  have hqpos : 0 < q := by
    have hB_nonneg : 0 ≤ modelLowerRoundBound ε r δ θ t := by
      dsimp [modelLowerRoundBound]
      exact mul_nonneg (sq_nonneg _) (by nlinarith only [ht2])
    nlinarith only [hq_gt, hB_nonneg]
  have hcpos : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
  have hinterp : modelRoundCapInterp ε r a b = φ := by
    have hieq := modelRoundCapInterp_eq hε hr ha0 hb0 ht_lt htpos ht_eq.symm
    rw [hieq]
    simpa [D] using hparams.2.1
  have hq_eq : modelRoundCapQ ε r δ θ a b = q := by
    dsimp [modelRoundCapQ]
    rw [show modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b) * a) =
        modelLowerRoundBound ε r δ θ t by rw [ht_eq]]
    rw [show smoothCap ε r δ ((2 * ε + r ^ 2 * b) * a) = smoothCap ε r δ t by rw [ht_eq]]
    rw [hinterp]
    dsimp [φ]
    field_simp [ne_of_gt hgap_pos]
    ring
  let sx : ℝ := Real.sqrt (2 * ε + r ^ 2 * b)
  let sq : ℝ := Real.sqrt q
  let sb : ℝ := Real.sqrt b
  have hsx_pos : 0 < sx := by dsimp [sx]; exact Real.sqrt_pos.2 hcpos
  have hsq_pos : 0 < sq := by dsimp [sq]; exact Real.sqrt_pos.2 hqpos
  have hsb_pos : 0 < sb := by dsimp [sb]; exact Real.sqrt_pos.2 hb_pos
  let u : EuclideanSpace ℝ (Fin k) := sx⁻¹ • negPart hk y
  let w : EuclideanSpace ℝ (Fin (n - k)) := (sb / sq) • posPart hk y
  have hsq_u : ‖u‖ ^ 2 = a := by
    dsimp [u, sx]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [show ‖negPart hk y‖ ^ 2 = t by dsimp [t]]
    rw [← ht_eq]
    rw [show (Real.sqrt (2 * ε + r ^ 2 * b))⁻¹ ^ 2 = (2 * ε + r ^ 2 * b)⁻¹ by
      rw [inv_pow]
      rw [Real.sq_sqrt (le_of_lt hcpos)]]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
  have hunorm_le : ‖u‖ ≤ 1 := by
    have hs : ‖u‖ ^ 2 ≤ 1 ^ 2 := by
      rw [hsq_u]
      rw [one_pow]
      exact ha1
    have habs := sq_le_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg u), abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))] at habs
  have hwnorm_sq : ‖w‖ ^ 2 = b := by
    dsimp [w, sb, sq]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [show ‖posPart hk y‖ ^ 2 = q by dsimp [q]]
    rw [div_pow]
    rw [show Real.sqrt b ^ 2 = b by exact Real.sq_sqrt hb0]
    rw [show Real.sqrt q ^ 2 = q by exact Real.sq_sqrt (le_of_lt hqpos)]
    field_simp [ne_of_gt hqpos]
  have hwnorm_eq : ‖w‖ = sb := by
    calc
      ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ = Real.sqrt b := by rw [hwnorm_sq]
      _ = sb := rfl
  have hwnorm_le : ‖w‖ ≤ 1 := by
    rw [hwnorm_eq]
    dsimp [sb]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hb1
  let p : StandardHandle k (n - k) := (⟨u, hunorm_le⟩, ⟨w, hwnorm_le⟩)
  refine ⟨p, ?_⟩
  have hneg : negPart hk (modelHandleRoundMap hk ε r δ θ p) = negPart hk y := by
    rw [modelHandleRoundMap_negPart]
    dsimp [p]
    rw [hwnorm_sq]
    dsimp [u, sx]
    rw [smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hsx_pos)]
    rw [one_smul]
  have hpos : posPart hk (modelHandleRoundMap hk ε r δ θ p) = posPart hk y := by
    rw [modelHandleRoundMap_posPart]
    dsimp [p]
    rw [hwnorm_eq]
    rw [show modelRoundCapQ ε r δ θ (‖u‖ ^ 2) (sb ^ 2) = q by
      rw [hsq_u]
      rw [show sb ^ 2 = b by
        dsimp [sb]
        exact Real.sq_sqrt hb0]
      exact hq_eq]
    dsimp [w, sb, sq]
    rw [smul_smul]
    have hmain : (Real.sqrt q / Real.sqrt b) * (Real.sqrt b / Real.sqrt q) = 1 := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 hqpos), ne_of_gt (Real.sqrt_pos.2 hb_pos)]
    rw [hmain]
    rw [one_smul]
  rw [← recombine_decompose hk y]
  rw [← recombine_decompose hk (modelHandleRoundMap hk ε r δ θ p)]
  rw [hneg, hpos]

theorem modelAttachedRegion_mem_handleRound_of_negPart_le {n k : ℕ} (hk : k ≤ n)
    (ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (hr : 0 < r) {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hq_gt : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) < ‖posPart hk y‖ ^ 2)
    (ht_le : ‖negPart hk y‖ ^ 2 ≤ 2 * ε) :
    y ∈ Set.range (modelHandleRoundMap hk ε r δ θ) := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let q : ℝ := ‖posPart hk y‖ ^ 2
  have hq_le : q ≤ smoothCap ε r δ t := by
    simpa [modelAttachedRegion, t, q] using hy
  have hB : modelLowerRoundBound ε r δ θ t = t - 2 * ε := by
    have hle : t ≤ r ^ 2 + 2 * ε - θ := by nlinarith only [ht_le, hθr]
    exact modelLowerRoundBound_eq_self_of_le hθ hle
  have hS : smoothCap ε r δ t = r ^ 2 := by
    have hle : t ≤ r ^ 2 + 2 * ε - δ := by nlinarith only [ht_le, hδr]
    exact smoothCap_lower hδ hle
  have hq_gt' : t - 2 * ε < q := by
    rwa [hB] at hq_gt
  have hq_le_r2 : q ≤ r ^ 2 := by
    rwa [hS] at hq_le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact sq_nonneg _
  let b : ℝ := q / r ^ 2
  let a : ℝ := t / (2 * ε + r ^ 2 * b)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg hq_nonneg (sq_nonneg r)
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ (sq_pos_of_pos hr)]
    nlinarith only [hq_le_r2]
  have hcpos : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
  have hteq : t = (2 * ε + r ^ 2 * b) * a := by
    dsimp [a]
    field_simp [ne_of_gt hcpos]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (by nlinarith only [ht_le, hε]) (le_of_lt hcpos)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_iff₀ hcpos]
    nlinarith only [ht_le, hb0, sq_nonneg r]
  have hq_eq : modelRoundCapQ ε r δ θ a b = q := by
    by_cases ht0 : t = 0
    · have ha0' : a = 0 := by
        dsimp [a]
        rw [ht0]
        norm_num
      rw [ha0']
      have hcq := modelRoundCapQ_eq_cocore hε hδ hθ hδr hθr hb0 hb1
      dsimp [b] at hcq ⊢
      rw [hcq]
      dsimp [q]
      field_simp [ne_of_gt (sq_pos_of_pos hr)]
    · have htpos : 0 < t := lt_of_le_of_ne (by
        dsimp [t]
        exact sq_nonneg _) (Ne.symm ht0)
      have hapos : 0 < a := by
        dsimp [a]
        exact div_pos htpos hcpos
      have hcq := modelRoundCapQ_eq_r2b_of_t_lt hε hδ hθ hδr hθr hr hapos hb0
        (by nlinarith only [ht_le, sq_pos_of_pos hr]) htpos ht_le hteq
      dsimp [b] at hcq ⊢
      rw [hcq]
      dsimp [q]
      field_simp [ne_of_gt (sq_pos_of_pos hr)]
  let sx : ℝ := Real.sqrt (2 * ε + r ^ 2 * b)
  let sb : ℝ := Real.sqrt b
  have hsx_pos : 0 < sx := by dsimp [sx]; exact Real.sqrt_pos.2 hcpos
  let u : EuclideanSpace ℝ (Fin k) := sx⁻¹ • negPart hk y
  let w : EuclideanSpace ℝ (Fin (n - k)) := (r⁻¹ : ℝ) • posPart hk y
  have hsq_u : ‖u‖ ^ 2 = a := by
    dsimp [u, sx]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [show ‖negPart hk y‖ ^ 2 = t by rfl]
    rw [hteq]
    rw [show (Real.sqrt (2 * ε + r ^ 2 * b))⁻¹ ^ 2 = (2 * ε + r ^ 2 * b)⁻¹ by
      rw [inv_pow]
      rw [Real.sq_sqrt (le_of_lt hcpos)]]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
  have hunorm_le : ‖u‖ ≤ 1 := by
    have hs : ‖u‖ ^ 2 ≤ 1 ^ 2 := by
      rw [hsq_u]
      rw [one_pow]
      exact ha1
    have habs := sq_le_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg u), abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))] at habs
  have hwnorm_sq : ‖w‖ ^ 2 = b := by
    dsimp [w, b, q]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [ne_of_gt (sq_pos_of_pos hr)]
  have hwnorm_eq : ‖w‖ = sb := by
    calc
      ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ = Real.sqrt b := by rw [hwnorm_sq]
      _ = sb := rfl
  have hwnorm_le : ‖w‖ ≤ 1 := by
    rw [hwnorm_eq]
    dsimp [sb]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hb1
  let p : StandardHandle k (n - k) := (⟨u, hunorm_le⟩, ⟨w, hwnorm_le⟩)
  refine ⟨p, ?_⟩
  have hneg : negPart hk (modelHandleRoundMap hk ε r δ θ p) = negPart hk y := by
    rw [modelHandleRoundMap_negPart]
    dsimp [p]
    rw [hwnorm_sq]
    dsimp [u, sx]
    rw [smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hsx_pos)]
    rw [one_smul]
  have hpos : posPart hk (modelHandleRoundMap hk ε r δ θ p) = posPart hk y := by
    by_cases hb0' : b = 0
    · have hq0 : q = 0 := by
        dsimp [b] at hb0'
        rcases (div_eq_zero_iff.mp hb0') with hq | hr2
        · exact hq
        · exact False.elim (ne_of_gt (sq_pos_of_pos hr) hr2)
      have hposy : posPart hk y = 0 := by
        have hsq0 : ‖posPart hk y‖ ^ 2 = 0 := by
          dsimp [q] at hq0
          exact hq0
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
      rw [modelHandleRoundMap_posPart]
      dsimp [p]
      rw [hwnorm_eq]
      dsimp [sb]
      have hsb0 : Real.sqrt b = 0 := by
        rw [hb0']
        rw [Real.sqrt_zero]
      rw [hsb0]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
      rw [show modelRoundCapQ ε r δ θ (‖u‖ ^ 2) 0 = 0 by
        exact modelRoundCapQ_eq_zero_of_b_eq_zero hε hδ hθ hδr hθr hr
          (by rw [hsq_u]; exact ha1)]
      dsimp [w]
      rw [hposy]
      simp
    · have hb_pos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb0')
      rw [modelHandleRoundMap_posPart]
      dsimp [p]
      rw [hwnorm_eq]
      dsimp [w]
      rw [show modelRoundCapQ ε r δ θ (‖u‖ ^ 2) (sb ^ 2) = q by
        rw [hsq_u]
        rw [show sb ^ 2 = b by
          dsimp [sb]
          exact Real.sq_sqrt hb0]
        exact hq_eq]
      dsimp [sb]
      rw [show Real.sqrt q / Real.sqrt b = r by
        have hsqrt_q : Real.sqrt q = r * Real.sqrt b := by
          rw [show q = r ^ 2 * b by
            dsimp [b]
            field_simp [ne_of_gt (sq_pos_of_pos hr)]]
          rw [Real.sqrt_mul (sq_nonneg r) b]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hr)]
        rw [hsqrt_q]
        field_simp [ne_of_gt (Real.sqrt_pos.2 hb_pos)]]
      rw [smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt hr)]
      rw [one_smul]
  rw [← recombine_decompose hk y]
  rw [← recombine_decompose hk (modelHandleRoundMap hk ε r δ θ p)]
  rw [hneg, hpos]

theorem modelAttachedRegion_subset_lowerRound_union_handleRound {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (hr : 0 < r) :
    modelAttachedRegion hk ε r δ ⊆
      modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) ∪
        Set.range (modelHandleRoundMap hk ε r δ θ) := by
  intro y hy
  by_cases hlower : modelCapRoundedLowerFunctionInner hk c ε r δ θ y ≤ c
  · left
    exact (modelCapRoundedLowerFunctionInner_le_c_iff hk c ε r δ θ hθ hδ hδr hθr y).mp hlower
  · right
    have hq_gt : modelLowerRoundBound ε r δ θ (‖negPart hk y‖ ^ 2) < ‖posPart hk y‖ ^ 2 := by
      have hinner_gt : c < modelCapRoundedLowerFunctionInner hk c ε r δ θ y := lt_of_not_ge hlower
      dsimp [modelCapRoundedLowerFunctionInner] at hinner_gt
      nlinarith
    by_cases ht2 : 2 * ε < ‖negPart hk y‖ ^ 2
    · exact modelAttachedRegion_mem_handleRound_of_negPart_gt hk ε r δ θ hε hδ hθ hδr hr hy hq_gt ht2
    · exact modelAttachedRegion_mem_handleRound_of_negPart_le hk ε r δ θ hε hδ hθ hδr hθr hr hy hq_gt (le_of_not_gt ht2)

theorem modelAttachedRegion_eq_lowerRound_union_handleRound {n k : ℕ} (hk : k ≤ n)
    (c ε r δ θ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2)
    (hr : 0 < r) :
    modelAttachedRegion hk ε r δ =
      modelLowerRoundMap hk ε r δ θ '' (sublevel (morseNormalForm hk c) (c - ε)) ∪
        Set.range (modelHandleRoundMap hk ε r δ θ) := by
  ext y
  constructor
  · intro hy
    exact modelAttachedRegion_subset_lowerRound_union_handleRound hk c ε r δ θ hε hδ hθ hδr hθr hr hy
  · intro hy
    exact lowerRound_union_handleRound_subset_modelAttachedRegion hk c ε r δ θ hε hδ hθ hδr hy

theorem modelHandleRoundMap_posPart_eq_of_scalar {n k : ℕ} (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p p' : StandardHandle k (n - k))
    (hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) ≠ 0)
    (hbb : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
      ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
    (hqq : modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
    (hpos : ((Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
          (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
        (Real.sqrt (modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
          (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
            (p'.2 : EuclideanSpace ℝ (Fin (n - k)))) :
    (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let a' : ℝ := ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let b' : ℝ := ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.2.2
    simpa using hle
  have hb0' : 0 ≤ b' := by dsimp [b']; exact sq_nonneg _
  have hb1' : b' ≤ 1 := by
    dsimp [b']
    have hnon : 0 ≤ ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p'.2.2
    simpa using hle
  have hb : 0 < b := by
    have hwpos : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hw))
    dsimp [b]
    exact sq_pos_of_pos hwpos
  have hqpos : 0 < modelRoundCapQ ε r δ θ a b := by
    exact modelRoundCapQ_pos_of_b_pos hε hδ hθ hδr hθr hr (by dsimp [a]; exact sq_nonneg _)
      (by
        dsimp [a]
        have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
        have hle := sq_le_sq' (by linarith [hnon]) p.1.2
        simpa using hle) hb0 hb1 hb
  have hnorm : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ = ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hnon' : 0 ≤ ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hsqrt : Real.sqrt (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
        Real.sqrt (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
      rw [hbb]
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hsqrt
    rw [abs_of_nonneg hnon, abs_of_nonneg hnon'] at hsqrt
    exact hsqrt
  have hscalar : Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ =
      Real.sqrt (modelRoundCapQ ε r δ θ a' b') / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
    have hqeq : modelRoundCapQ ε r δ θ a b = modelRoundCapQ ε r δ θ a' b' := by
      simpa [a, a', b, b'] using hqq
    rw [hqeq, hnorm]
  have hscalar_ne : Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ≠ 0 := by
    have hsqrt_pos : 0 < Real.sqrt (modelRoundCapQ ε r δ θ a b) := Real.sqrt_pos.2 hqpos
    have hw_pos : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hw))
    exact ne_of_gt (div_pos hsqrt_pos hw_pos)
  have hs_inj : (Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
      (p.2 : EuclideanSpace ℝ (Fin (n - k))) =
      (Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    have hpos' : ((Real.sqrt (modelRoundCapQ ε r δ θ a' b') / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
        (Real.sqrt (modelRoundCapQ ε r δ θ a' b') / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
          (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
      have hpos'' : ((Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
          (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
          (Real.sqrt (modelRoundCapQ ε r δ θ a' b') / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
            (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
        simpa [a, a', b, b'] using hpos
      rw [hscalar] at hpos''
      exact hpos''
    rw [hscalar]
    exact hpos'
  exact (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r :=
    Real.sqrt (modelRoundCapQ ε r δ θ a b) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖)
    hscalar_ne) hs_inj

theorem modelHandleRoundMap_negPart_eq_of_scalar {n k : ℕ} (ε r : ℝ)
    (hε : 0 < ε) (p p' : StandardHandle k (n - k))
    (hbb : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
      ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
    (hneg : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p.1 : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k)) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p'.1 : EuclideanSpace ℝ (Fin k))) :
    (p.1 : EuclideanSpace ℝ (Fin k)) = (p'.1 : EuclideanSpace ℝ (Fin k)) := by
  have hsqrt_ne : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) ≠ 0 := by
    have hpos : 0 < 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
      nlinarith only [hε, sq_nonneg (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ : ℝ)]
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  have hs_inj : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
      (p.1 : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k)) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p'.1 : EuclideanSpace ℝ (Fin k)) := by
    rw [hbb]
    rw [hbb] at hneg
    exact hneg
  exact (smul_right_injective (EuclideanSpace ℝ (Fin k)) (r :=
    Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
    hsqrt_ne) hs_inj

theorem modelHandleRoundMap_injective_cocore {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p p' : StandardHandle k (n - k))
    (h : modelHandleRoundMap hk ε r δ θ p = modelHandleRoundMap hk ε r δ θ p')
    (ht0 : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 0) (ht0' : ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ = 0) :
    p = p' := by
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let b' : ℝ := ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    have hnon : 0 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.2.2
    simpa using hle
  have hb0' : 0 ≤ b' := by dsimp [b']; exact sq_nonneg _
  have hb1' : b' ≤ 1 := by
    dsimp [b']
    have hnon : 0 ≤ ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p'.2.2
    simpa using hle
  have hq : modelRoundCapQ ε r δ θ 0 b = modelRoundCapQ ε r δ θ 0 b' := by
    have hnorms : ‖posPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
        ‖posPart hk (modelHandleRoundMap hk ε r δ θ p')‖ ^ 2 := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => ‖v‖ ^ 2) (congrArg (posPart hk) h)
    have hqn : ‖posPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 = modelRoundCapQ ε r δ θ 0 b := by
      have hqn0 := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p
      have hu : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 := by
        have hz : (p.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0
        simp [hz]
      simpa [b, hu] using hqn0
    have hqn' : ‖posPart hk (modelHandleRoundMap hk ε r δ θ p')‖ ^ 2 =
        modelRoundCapQ ε r δ θ 0 b' := by
      have hqn0 := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p'
      have hu : ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 := by
        have hz : (p'.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0'
        simp [hz]
      simpa [b', hu] using hqn0
    rw [hqn, hqn'] at hnorms
    exact hnorms
  have hb_eq : b = b' := by
    have hq0 := modelRoundCapQ_eq_cocore hε hδ hθ hδr hθr hb0 hb1
    have hq0' := modelRoundCapQ_eq_cocore hε hδ hθ hδr hθr hb0' hb1'
    have hmain : r ^ 2 * b = r ^ 2 * b' := by
      rw [← hq0, ← hq0']
      exact hq
    have hr2 : r ^ 2 ≠ 0 := by
      intro hz
      nlinarith only [sq_pos_of_pos hr, hz]
    exact (mul_left_cancel₀ hr2) hmain
  have hu : (p.1 : EuclideanSpace ℝ (Fin k)) = (p'.1 : EuclideanSpace ℝ (Fin k)) := by
    have hz : (p.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0
    rw [hz]
    have hz' : (p'.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0'
    rw [hz']
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    by_cases hb0z : b = 0
    · have hw0 : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
        have hsq : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by simpa [b] using hb0z
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      rw [hw0]
      have hw0' : (p'.2 : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
        have hsq : ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by
          have : b' = 0 := by simpa [hb_eq] using hb0z
          simpa [b'] using this
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      rw [hw0']
    · have hbneq : (p.2 : EuclideanSpace ℝ (Fin (n - k))) ≠ 0 := by
        intro hz
        have hsq : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by
          have hsq1 : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
              ‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 :=
            congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => ‖v‖ ^ 2) hz
          norm_num at hsq1
          simpa using hsq1
        have hb0sq : b = 0 := by
          change ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0
          exact hsq
        exact hb0z hb0sq
      have hbb' : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
          ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        simp [b, b', hb_eq]
      have hqq' : modelRoundCapQ ε r δ θ 0 (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
          modelRoundCapQ ε r δ θ 0 (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
        simpa [b, b'] using hq
      have hqq'' : modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
            (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
          modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
            (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
        have hu0 : (p.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0
        have hu0' : (p'.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0'
        simpa [hu0, hu0', b, b'] using hq
      have hpos' : ((Real.sqrt (modelRoundCapQ ε r δ θ 0 (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) /
            ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
              (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
          (Real.sqrt (modelRoundCapQ ε r δ θ 0 (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) /
            ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
              (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
        have hpos0 := congrArg (posPart hk) h
        rw [modelHandleRoundMap_posPart, modelHandleRoundMap_posPart] at hpos0
        have hu0 : (p.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0
        have hu0' : (p'.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0'
        simpa [hu0, hu0'] using hpos0
      have hpos'' : ((Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
              (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
                (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
            (Real.sqrt (modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
                (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
                  (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
        have hu0 : (p.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0
        have hu0' : (p'.1 : EuclideanSpace ℝ (Fin k)) = 0 := norm_eq_zero.mp ht0'
        simpa [hu0, hu0'] using hpos'
      exact modelHandleRoundMap_posPart_eq_of_scalar ε r δ θ hε hδ hθ hδr hθr hr p p'
        hbneq hbb' hqq'' hpos''
  apply Prod.ext
  · apply Subtype.ext
    exact hu
  · apply Subtype.ext
    exact hw

theorem modelRoundCapInterp_eq_of_modelRoundCapQ_eq {ε r δ θ a₁ a₂ b₁ b₂ t : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (ht0 : t < r ^ 2 + 2 * ε)
    (ht₁ : t = (2 * ε + r ^ 2 * b₁) * a₁)
    (ht₂ : t = (2 * ε + r ^ 2 * b₂) * a₂)
    (hq : modelRoundCapQ ε r δ θ a₁ b₁ = modelRoundCapQ ε r δ θ a₂ b₂) :
    modelRoundCapInterp ε r a₁ b₁ = modelRoundCapInterp ε r a₂ b₂ := by
  have hB₁ : modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b₁) * a₁) =
      modelLowerRoundBound ε r δ θ t := by
    rw [← ht₁]
  have hB₂ : modelLowerRoundBound ε r δ θ ((2 * ε + r ^ 2 * b₂) * a₂) =
      modelLowerRoundBound ε r δ θ t := by
    rw [← ht₂]
  have hS₁ : smoothCap ε r δ ((2 * ε + r ^ 2 * b₁) * a₁) = smoothCap ε r δ t := by
    rw [← ht₁]
  have hS₂ : smoothCap ε r δ ((2 * ε + r ^ 2 * b₂) * a₂) = smoothCap ε r δ t := by
    rw [← ht₂]
  have hq₁ : modelRoundCapQ ε r δ θ a₁ b₁ =
      modelLowerRoundBound ε r δ θ t +
        modelRoundCapInterp ε r a₁ b₁ *
          (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := by
    dsimp [modelRoundCapQ]
    rw [hB₁, hS₁]
    ring
  have hq₂ : modelRoundCapQ ε r δ θ a₂ b₂ =
      modelLowerRoundBound ε r δ θ t +
        modelRoundCapInterp ε r a₂ b₂ *
          (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := by
    dsimp [modelRoundCapQ]
    rw [hB₂, hS₂]
    ring
  have hlt : modelLowerRoundBound ε r δ θ t < smoothCap ε r δ t :=
    modelLowerRoundBound_lt_smoothCap_of_lt hδ hθ hδr ht0
  have hdiff : smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t ≠ 0 := by linarith
  have hmul : modelRoundCapInterp ε r a₁ b₁ *
        (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) =
      modelRoundCapInterp ε r a₂ b₂ *
        (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := by
    calc
      modelRoundCapInterp ε r a₁ b₁ *
          (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) =
          modelRoundCapQ ε r δ θ a₁ b₁ - modelLowerRoundBound ε r δ θ t := by
        rw [hq₁]
        ring
      _ = modelRoundCapQ ε r δ θ a₂ b₂ - modelLowerRoundBound ε r δ θ t := by rw [hq]
      _ = modelRoundCapInterp ε r a₂ b₂ *
          (smoothCap ε r δ t - modelLowerRoundBound ε r δ θ t) := by
        rw [hq₂]
        ring
  exact (mul_right_cancel₀ hdiff) hmul

theorem modelHandleRoundMap_injective_of_eq {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p p' : StandardHandle k (n - k))
    (h : modelHandleRoundMap hk ε r δ θ p = modelHandleRoundMap hk ε r δ θ p')
    (hb : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
      ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) :
    p = p' := by
  have hneg : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
      (p.1 : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k)) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) •
        (p'.1 : EuclideanSpace ℝ (Fin k)) := by
    have hneg' := congrArg (negPart hk) h
    rw [modelHandleRoundMap_negPart, modelHandleRoundMap_negPart] at hneg'
    exact hneg'
  have hpos : ((Real.sqrt (modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
      (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
        (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k))) =
      (Real.sqrt (modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) / ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖) •
          (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    have hpos' := congrArg (posPart hk) h
    rw [modelHandleRoundMap_posPart, modelHandleRoundMap_posPart] at hpos'
    exact hpos'
  have hq : modelRoundCapQ ε r δ θ (‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      modelRoundCapQ ε r δ θ (‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2)
        (‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
    have hnorms : ‖posPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
        ‖posPart hk (modelHandleRoundMap hk ε r δ θ p')‖ ^ 2 := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => ‖v‖ ^ 2) (congrArg (posPart hk) h)
    have hqn := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p
    have hqn' := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p'
    rw [hqn, hqn'] at hnorms
    exact hnorms
  have hu : (p.1 : EuclideanSpace ℝ (Fin k)) = (p'.1 : EuclideanSpace ℝ (Fin k)) := by
    exact modelHandleRoundMap_negPart_eq_of_scalar ε r hε p p' hb hneg
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (p'.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    by_cases hw0 : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = 0
    · have hb0 : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by
        rw [hw0]
        norm_num
      have hb0' : ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by
        rw [← hb]
        exact hb0
      have hw0' : (p'.2 : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb0')
      rw [hw0, hw0']
    · exact modelHandleRoundMap_posPart_eq_of_scalar ε r δ θ hε hδ hθ hδr hθr hr p p' hw0 hb hq hpos
  apply Prod.ext
  · apply Subtype.ext
    exact hu
  · apply Subtype.ext
    exact hw

theorem modelHandleRoundMap_injective_top {ε r a b : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (ht : (2 * ε + r ^ 2 * b) * a = r ^ 2 + 2 * ε) :
    a = 1 ∧ b = 1 := by
  have hge : 2 * ε + r ^ 2 ≤ (2 * ε + r ^ 2) * a := by
    have hm : (2 * ε + r ^ 2 * b) * a = 2 * ε + r ^ 2 := by
      rw [ht]
      ring
    have hcoef_le : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 := by nlinarith only [hb1]
    have hprod_le : (2 * ε + r ^ 2 * b) * a ≤ (2 * ε + r ^ 2) * a :=
      mul_le_mul_of_nonneg_right hcoef_le ha0
    nlinarith only [hm, hprod_le]
  have hle : (2 * ε + r ^ 2) * a ≤ 2 * ε + r ^ 2 := by
    exact mul_le_of_le_one_right (by nlinarith only [hε]) ha1
  have heq : (2 * ε + r ^ 2) * a = 2 * ε + r ^ 2 := le_antisymm hle hge
  have haeq : a = 1 := by
    have hmain : (2 * ε + r ^ 2) * a = (2 * ε + r ^ 2) * 1 := by
      rw [heq]
      ring
    exact (mul_left_cancel₀ (by nlinarith only [hε])) hmain
  have hbeq : b = 1 := by
    have hm : (2 * ε + r ^ 2 * b) * a = 2 * ε + r ^ 2 := by
      rw [ht]
      ring
    rw [haeq] at hm
    have hcoef : 2 * ε + r ^ 2 * b = 2 * ε + r ^ 2 := by
      simpa using hm
    have hrb : r ^ 2 * b = r ^ 2 := by nlinarith
    have hmain2 : r ^ 2 * b = r ^ 2 * 1 := by
      rw [hrb]
      ring
    exact (mul_left_cancel₀ (by
      intro hz
      nlinarith only [sq_pos_of_pos hr, hz])) hmain2
  exact ⟨haeq, hbeq⟩

theorem modelHandleRoundMap_injective {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r)
    (p p' : StandardHandle k (n - k))
    (h : modelHandleRoundMap hk ε r δ θ p = modelHandleRoundMap hk ε r δ θ p') : p = p' := by
  let a : ℝ := ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let a' : ℝ := ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2
  let b : ℝ := ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let b' : ℝ := ‖(p'.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2
  let t : ℝ := (2 * ε + r ^ 2 * b) * a
  let t' : ℝ := (2 * ε + r ^ 2 * b') * a'
  have ha0 : 0 ≤ a := by dsimp [a]; exact sq_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have hnon : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := norm_nonneg _
    have hle := sq_le_sq' (by linarith [hnon]) p.1.2
    simpa using hle
  have ha0' : 0 ≤ a' := by dsimp [a']; exact sq_nonneg _
  have ha1' : a' ≤ 1 := by
    dsimp [a']
    nlinarith only [norm_nonneg (p'.1 : EuclideanSpace ℝ (Fin k)), p'.1.2]
  have hb0 : 0 ≤ b := by dsimp [b]; exact sq_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    nlinarith only [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k))), p.2.2]
  have hb0' : 0 ≤ b' := by dsimp [b']; exact sq_nonneg _
  have hb1' : b' ≤ 1 := by
    dsimp [b']
    nlinarith only [norm_nonneg (p'.2 : EuclideanSpace ℝ (Fin (n - k))), p'.2.2]
  have hc0 : 0 < 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0, sq_nonneg r]
  have hc0' : 0 < 2 * ε + r ^ 2 * b' := by nlinarith only [hε, hb0', sq_nonneg r]
  have ht : t = t' := by
    have hnorm : ‖negPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
        ‖negPart hk (modelHandleRoundMap hk ε r δ θ p')‖ ^ 2 := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin k) => ‖v‖ ^ 2) (congrArg (negPart hk) h)
    have hnp := modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p
    have hnp' := modelHandleRoundMap_negPart_norm_sq hk ε r δ θ (le_of_lt hε) p'
    rw [hnp, hnp'] at hnorm
    dsimp [t, t', a, a', b, b']
    exact hnorm
  have hq : modelRoundCapQ ε r δ θ a b = modelRoundCapQ ε r δ θ a' b' := by
    have hnorms : ‖posPart hk (modelHandleRoundMap hk ε r δ θ p)‖ ^ 2 =
        ‖posPart hk (modelHandleRoundMap hk ε r δ θ p')‖ ^ 2 := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (n - k)) => ‖v‖ ^ 2) (congrArg (posPart hk) h)
    have hqn := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p
    have hqn' := modelHandleRoundMap_posPart_norm_sq hk ε r δ θ hε hδ hθ hδr hθr hr p'
    rw [hqn, hqn'] at hnorms
    dsimp [a, a', b, b']
    exact hnorms
  have ht_le : t ≤ r ^ 2 + 2 * ε := by
    have h1 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0]
    have h2 : 2 * ε + r ^ 2 * b ≤ 2 * ε + r ^ 2 := by nlinarith only [hb1]
    have h3 : (2 * ε + r ^ 2 * b) * a ≤ (2 * ε + r ^ 2) * a :=
      mul_le_mul_of_nonneg_right h2 ha0
    have h4 : (2 * ε + r ^ 2) * a ≤ 2 * ε + r ^ 2 := by
      have h5 : 0 ≤ 2 * ε + r ^ 2 := by nlinarith only [hε]
      exact mul_le_of_le_one_right h5 ha1
    dsimp [t]
    nlinarith only [h3, h4]
  by_cases ht0 : t = 0
  · have ha_eq0 : a = 0 := by
      have hmain : (2 * ε + r ^ 2 * b) * a = 0 := by
        simpa [t] using ht0
      exact (mul_eq_zero.mp hmain).resolve_left (ne_of_gt hc0)
    have ha_eq0' : a' = 0 := by
      have ht'0 : t' = 0 := by
        rw [← ht]
        exact ht0
      have hmain : (2 * ε + r ^ 2 * b') * a' = 0 := by
        simpa [t'] using ht'0
      exact (mul_eq_zero.mp hmain).resolve_left (ne_of_gt hc0')
    have hu0 : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 0 := by
      have hsq : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 := by
        simpa [a] using ha_eq0
      exact sq_eq_zero_iff.mp hsq
    have hu0' : ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ = 0 := by
      have hsq : ‖(p'.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 := by
        simpa [a'] using ha_eq0'
      exact sq_eq_zero_iff.mp hsq
    exact modelHandleRoundMap_injective_cocore hk ε r δ θ hε hδ hθ hδr hθr hr p p' h hu0 hu0'
  · have htpos : 0 < t := by
      have hle : 0 ≤ t := by
        have h1 : 0 ≤ 2 * ε + r ^ 2 * b := by nlinarith only [hε, hb0]
        simpa [t] using mul_nonneg h1 ha0
      exact lt_of_le_of_ne hle (Ne.symm ht0)
    by_cases htop : t = r ^ 2 + 2 * ε
    · have htop_unp : (2 * ε + r ^ 2 * b) * a = r ^ 2 + 2 * ε := by
        dsimp [t] at htop
        exact htop
      have htop_pr : (2 * ε + r ^ 2 * b') * a' = r ^ 2 + 2 * ε := by
        have hteq : t = (2 * ε + r ^ 2 * b') * a' := by
          simpa [t'] using ht
        rw [← hteq]
        exact htop
      have hpair := modelHandleRoundMap_injective_top (hε := hε) (hr := hr)
        (a := a) (b := b) (ha0 := ha0) (ha1 := ha1) (hb1 := hb1) (ht := htop_unp)
      have hpair' := modelHandleRoundMap_injective_top (hε := hε) (hr := hr)
        (a := a') (b := b') (ha0 := ha0') (ha1 := ha1') (hb1 := hb1') (ht := htop_pr)
      have ha_eq : a = a' := by
        rw [hpair.1, hpair'.1]
      have hb_eq : b = b' := by
        rw [hpair.2, hpair'.2]
      exact modelHandleRoundMap_injective_of_eq hk ε r δ θ hε hδ hθ hδr hθr hr p p' h
        (by simpa [b, b'] using hb_eq)
    · have ht_lt : t < r ^ 2 + 2 * ε := lt_of_le_of_ne ht_le htop
      have ha_pos : 0 < a := by
        have ht_eq : (2 * ε + r ^ 2 * b) * a = t := by
          dsimp [t]
        by_contra hz
        have hle : a ≤ 0 := le_of_not_gt hz
        have hnonpos : (2 * ε + r ^ 2 * b) * a ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc0) hle
        have hpos : 0 < (2 * ε + r ^ 2 * b) * a := by
          rw [ht_eq]
          exact htpos
        exact (not_lt_of_ge hnonpos) hpos
      have ha'_pos : 0 < a' := by
        have ht_eq : (2 * ε + r ^ 2 * b') * a' = t := by
          simpa [t'] using ht.symm
        by_contra hz
        have hle : a' ≤ 0 := le_of_not_gt hz
        have hnonpos : (2 * ε + r ^ 2 * b') * a' ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc0') hle
        have hpos : 0 < (2 * ε + r ^ 2 * b') * a' := by
          rw [ht_eq]
          exact htpos
        exact (not_lt_of_ge hnonpos) hpos
      by_cases hlow : t < 2 * ε
      · have hq1 : modelRoundCapQ ε r δ θ a b = r ^ 2 * b := by
          exact modelRoundCapQ_eq_r2b_of_t_lt hε hδ hθ hδr hθr hr ha_pos hb0 ht_lt htpos
            (le_of_lt hlow) (by dsimp [t])
        have hq1' : modelRoundCapQ ε r δ θ a' b' = r ^ 2 * b' := by
          exact modelRoundCapQ_eq_r2b_of_t_lt hε hδ hθ hδr hθr hr ha'_pos hb0' ht_lt htpos
            (le_of_lt hlow) (by simpa [t'] using ht)
        have hrb : r ^ 2 * b = r ^ 2 * b' := by
          rw [← hq1, ← hq1']
          exact hq
        have hb_eq : b = b' := by
          exact (mul_left_cancel₀ (by
            intro hz
            nlinarith only [sq_pos_of_pos hr, hz])) hrb
        have ha_eq : a = a' := by
          have hmain : (2 * ε + r ^ 2 * b) * a = (2 * ε + r ^ 2 * b') * a' := by
            dsimp [t, t'] at ht
            exact ht
          rw [hb_eq] at hmain
          exact (mul_left_cancel₀ (ne_of_gt hc0')) hmain
        exact modelHandleRoundMap_injective_of_eq hk ε r δ θ hε hδ hθ hδr hθr hr p p' h
          (by simpa [b, b'] using hb_eq)
      · have hφ : modelRoundCapInterp ε r a b = modelRoundCapInterp ε r a' b' := by
          exact modelRoundCapInterp_eq_of_modelRoundCapQ_eq (hδ := hδ) (hθ := hθ) (hδr := hδr)
            (a₁ := a) (a₂ := a') (b₁ := b) (b₂ := b') (t := t) (ht0 := ht_lt)
            (ht₁ := by dsimp [t]) (ht₂ := by simpa [t'] using ht) (hq := hq)
        have ha_eq : a = a' := by
          exact modelRoundCapInterp_injective_fixed_t (hε := hε) (hr := hr)
            (a₁ := a) (a₂ := a') (b₁ := b) (b₂ := b') (t := t)
            (ha1₀ := ha_pos) (ha2₀ := ha'_pos) (hb1₀ := hb0) (hb2₀ := hb0')
            (ht0 := ht_lt) (htpos := htpos) (ht₁ := by dsimp [t])
            (ht₂ := by simpa [t'] using ht) (hφ := hφ)
        have hb_eq : b = b' := by
          have hmain : (2 * ε + r ^ 2 * b) * a = (2 * ε + r ^ 2 * b') * a' := by
            dsimp [t, t'] at ht
            exact ht
          rw [ha_eq] at hmain
          have hcoef : 2 * ε + r ^ 2 * b = 2 * ε + r ^ 2 * b' :=
            (mul_right_cancel₀ (ne_of_gt ha'_pos)) hmain
          have hrb : r ^ 2 * b = r ^ 2 * b' := add_left_cancel hcoef
          exact (mul_left_cancel₀ (by
            intro hz
            nlinarith only [sq_pos_of_pos hr, hz])) hrb
        exact modelHandleRoundMap_injective_of_eq hk ε r δ θ hε hδ hθ hδr hθr hr p p' h
          (by simpa [b, b'] using hb_eq)

theorem modelRoundCapQ_pos_at_handle {ε r δ θ a b : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hb : 0 < b) :
    0 < modelRoundCapQ ε r δ θ a b := by
  by_cases hb' : b < 1
  · exact modelRoundCapQ_pos_of_b_pos hε hδ hθ hδr hθr hr ha0 (le_of_lt ha1) hb0 hb1 hb
  · have hbeq : b = 1 := le_antisymm hb1 (le_of_not_gt hb')
    have hane : a ≠ 1 := by linarith [ha1]
    have hq := modelRoundCapQ_eq_smoothCap_of_eq_one (ε := ε) (r := r) (δ := δ) (θ := θ)
      (a := a) (b := b) hbeq hane
    rw [hq]
    exact smoothCap_pos hδ hδr

noncomputable def modelHandleRoundMapAmbient {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) : MorseModel n :=
  recombine hk
    (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2) • p.1)
    ((Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) / ‖p.2‖) • p.2)

theorem modelHandleRoundMap_eq_ambient {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (p : StandardHandle k (n - k)) :
    modelHandleRoundMap hk ε r δ θ p =
      modelHandleRoundMapAmbient hk ε r δ θ
        (⟨(p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k)))⟩) := by
  rfl

theorem portPrivate_138057aa_contDiffOn_recombine_handle {n k : ℕ} (hk : k ≤ n)
    (s : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))))
    (f g : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g s) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (f p • p.1) (g p • p.2)) s := by
  rw [contDiffOn_pi]
  intro i
  by_cases hi : i.val < k
  · have hcoord : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (f p • p.1) (g p • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => f p * p.1 ⟨i.val, hi⟩ := by
      funext p
      have hneq : i = negIdx hk ⟨i.val, hi⟩ := by
        apply Fin.ext
        rfl
      conv_lhs => rw [hneq]
      rw [recombine_negPart hk (f p • p.1) (g p • p.2) ⟨i.val, hi⟩]
      rfl
    rw [hcoord]
    exact hf.mul (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => p.1 ⟨i.val, hi⟩) s)
  · have hi' : i.val - k < n - k := by omega
    have hcoord : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (f p • p.1) (g p • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => g p * p.2 ⟨i.val - k, hi'⟩ := by
      funext p
      have hneq : i = posIdx hk ⟨i.val - k, hi'⟩ := by
        apply Fin.ext
        dsimp [posIdx]
        omega
      conv_lhs => rw [hneq]
      rw [recombine_posPart hk (f p • p.1) (g p • p.2) ⟨i.val - k, hi'⟩]
      rfl
    rw [hcoord]
    exact hg.mul (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => p.2 ⟨i.val - k, hi'⟩) s)

theorem contDiffOn_modelHandleRoundMap_ambient_closed {n k : ℕ} (hk : k ≤ n) (ε r δ θ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2) (hθr : θ < r ^ 2) (hr : 0 < r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelHandleRoundMapAmbient hk ε r δ θ)
      {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) |
        ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} := by
  let S : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) :=
    {p | ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1}
  let S_pos : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) :=
    {p | 0 < ‖p.2‖}
  let S_flat : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) :=
    {p | ‖p.2‖ ^ 2 < 1 - δ / r ^ 2 ∧ ‖p.2‖ ^ 2 < 1 - θ / r ^ 2}
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) := by
    rw [show (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) = fun x => ∑ i : Fin k, (x i) ^ 2 by
      funext x
      exact EuclideanSpace.real_norm_sq_eq x]
    fun_prop
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (n - k)) => ‖y‖ ^ 2) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin (n - k)) => ‖y‖ ^ 2) = fun y => ∑ j : Fin (n - k), (y j) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq y]
    fun_prop
  have hAOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => ‖p.1‖ ^ 2) Set.univ :=
    hA.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => p.1)) |>.contDiffOn
  have hBOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => ‖p.2‖ ^ 2) Set.univ :=
    hB.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => p.2)) |>.contDiffOn
  have hpairOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (Prod.map (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2)
        (fun y : EuclideanSpace ℝ (Fin (n - k)) => ‖y‖ ^ 2)) Set.univ :=
    ContDiff.prodMap hA hB |>.contDiffOn
  have hpair_pos : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      (S ∩ S_pos) := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (Prod.map (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2)
        (fun y : EuclideanSpace ℝ (Fin (n - k)) => ‖y‖ ^ 2)) (S ∩ S_pos)
    exact hpairOn.mono (by intro p hp; trivial)
  have hsq₁ : ∀ p ∈ S ∩ S_pos, ‖p.1‖ ^ 2 ≤ 1 := by
    intro p hp
    have hnon : 0 ≤ ‖p.1‖ := norm_nonneg _
    have hneg : (-1 : ℝ) ≤ ‖p.1‖ := by linarith [hnon]
    simpa using sq_le_sq' hneg hp.1.1
  have hsq₂ : ∀ p ∈ S ∩ S_pos, ‖p.2‖ ^ 2 ≤ 1 := by
    intro p hp
    have hnon : 0 ≤ ‖p.2‖ := norm_nonneg _
    have hneg : (-1 : ℝ) ≤ ‖p.2‖ := by linarith [hnon]
    simpa using sq_le_sq' hneg hp.1.2
  have hmaps : Set.MapsTo
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      (S ∩ S_pos) {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} := by
    intro p hp
    exact ⟨sq_nonneg _, hsq₁ p hp, sq_nonneg _, hsq₂ p hp⟩
  have hq : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) (S ∩ S_pos) :=
    (contDiffOn_modelRoundCapQ_closed hε hθ hδ hδr hθr).comp hpair_pos hmaps
  have hqpos : ∀ p ∈ S ∩ S_pos, modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2) ≠ 0 := by
    intro p hp
    have ha0 : 0 ≤ ‖p.1‖ ^ 2 := sq_nonneg _
    have ha1 : ‖p.1‖ ^ 2 ≤ 1 := hsq₁ p hp
    have hb0 : 0 ≤ ‖p.2‖ ^ 2 := sq_nonneg _
    have hb1 : ‖p.2‖ ^ 2 ≤ 1 := hsq₂ p hp
    have hb : 0 < ‖p.2‖ ^ 2 := sq_pos_of_pos hp.2
    exact ne_of_gt (modelRoundCapQ_pos_of_b_pos hε hδ hθ hδr hθr hr ha0 ha1 hb0 hb1 hb)
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2))) (S ∩ S_pos) :=
    hq.sqrt hqpos
  have hnorm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => ‖p.2‖) (S ∩ S_pos) := by
    have hcont : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => p.2) (S ∩ S_pos) := by
      fun_prop
    refine ContDiffOn.norm ℝ hcont ?_
    intro p hp
    exact (norm_ne_zero_iff.mp (ne_of_gt hp.2))
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) / ‖p.2‖) (S ∩ S_pos) :=
    hsqrt.div hnorm (by
      intro p hp
      exact ne_of_gt hp.2)
  have hsqrtArg_pos : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) (S ∩ S_pos) := by
    have harg : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          2 * ε + r ^ 2 * ‖p.2‖ ^ 2) (S ∩ S_pos) :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => 2 * ε)).contDiffOn.add
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => r ^ 2)).contDiffOn.mul
          (hBOn.mono (by intro p hp; trivial)))
    exact harg.sqrt (by
      intro p hp
      have hpos : 0 < 2 * ε + r ^ 2 * ‖p.2‖ ^ 2 := by nlinarith only [hε, sq_nonneg (‖p.2‖ : ℝ)]
      exact ne_of_gt hpos)
  have hSpos : ContDiffOn ℝ (⊤ : ℕ∞) (modelHandleRoundMapAmbient hk ε r δ θ) (S ∩ S_pos) := by
    have hraw := portPrivate_138057aa_contDiffOn_recombine_handle hk (S ∩ S_pos)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2))
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) / ‖p.2‖)
      hsqrtArg_pos hdiv
    exact hraw.congr fun _ _ => rfl
  have hsqrtArg_flat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) (S ∩ S_flat) := by
    have harg : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          2 * ε + r ^ 2 * ‖p.2‖ ^ 2) (S ∩ S_flat) :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => 2 * ε)).contDiffOn.add
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => r ^ 2)).contDiffOn.mul
          (hBOn.mono (by intro p hp; trivial)))
    exact harg.sqrt (by
      intro p hp
      have hpos : 0 < 2 * ε + r ^ 2 * ‖p.2‖ ^ 2 := by nlinarith only [hε, sq_nonneg (‖p.2‖ : ℝ)]
      exact ne_of_gt hpos)
  have hconst_flat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => r) (S ∩ S_flat) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => r)).contDiffOn
  have hSflat : ContDiffOn ℝ (⊤ : ℕ∞) (modelHandleRoundMapAmbient hk ε r δ θ) (S ∩ S_flat) := by
    have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          recombine hk (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2) • p.1) (r • p.2)) (S ∩ S_flat) :=
      portPrivate_138057aa_contDiffOn_recombine_handle hk (S ∩ S_flat)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2))
        (fun _p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => r)
        hsqrtArg_flat hconst_flat
    refine ContDiffOn.congr (s := S ∩ S_flat) hmain ?_
    intro p hp
    dsimp [modelHandleRoundMapAmbient]
    have hqflat : modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2) = r ^ 2 * ‖p.2‖ ^ 2 := by
      refine modelRoundCapQ_eq_r2b_of_flat hε hδ hθ hr ?_ ?_ hp.2.1 hp.2.2
      · have hnon : 0 ≤ ‖p.1‖ := norm_nonneg _
        have hneg : (-1 : ℝ) ≤ ‖p.1‖ := by linarith [hnon]
        simpa using sq_le_sq' hneg hp.1.1
      · exact sq_nonneg (‖p.2‖ : ℝ)
    have hposEq : (Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) / ‖p.2‖) • p.2 = r • p.2 := by
      by_cases hv : p.2 = 0
      · simp [hv]
      · have hnorm_ne : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        have hsqrt : Real.sqrt (r ^ 2 * ‖p.2‖ ^ 2) = r * ‖p.2‖ := by
          have hrew : (r * ‖p.2‖) ^ 2 = r ^ 2 * ‖p.2‖ ^ 2 := by ring
          have hsq : Real.sqrt ((r * ‖p.2‖) ^ 2) = |r * ‖p.2‖| := Real.sqrt_sq_eq_abs _
          rw [← hrew]
          rw [hsq]
          rw [abs_of_nonneg (mul_nonneg (le_of_lt hr) (norm_nonneg _))]
        have hmain : Real.sqrt (modelRoundCapQ ε r δ θ (‖p.1‖ ^ 2) (‖p.2‖ ^ 2)) / ‖p.2‖ = r := by
          rw [hqflat, hsqrt]
          field_simp [hnorm_ne]
        rw [hmain]
    rw [hposEq]
  have hSpos_open : IsOpen S_pos := by
    dsimp [S_pos]
    exact IsOpen.preimage (continuous_norm.comp continuous_snd) isOpen_Ioi
  have hSflat_open : IsOpen S_flat := by
    dsimp [S_flat]
    exact (IsOpen.preimage (continuous_norm.comp continuous_snd |>.pow 2) isOpen_Iio).inter
      (IsOpen.preimage (continuous_norm.comp continuous_snd |>.pow 2) isOpen_Iio)
  intro p hp
  by_cases hv : p.2 = 0
  · have hpflat : p ∈ S ∩ S_flat := by
      constructor
      · exact hp
      constructor
      · have hpos : 0 < 1 - δ / r ^ 2 := by
          have hdiv : δ / r ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hr)).mpr hδr
          linarith
        rw [hv]
        norm_num
        linarith [hpos]
      · have hpos : 0 < 1 - θ / r ^ 2 := by
          have hdiv : θ / r ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hr)).mpr hθr
          linarith
        rw [hv]
        norm_num
        linarith [hpos]
    have hmem : S ∩ S_flat ∈ nhdsWithin p S := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨S_flat, hSflat_open.mem_nhds hpflat.2, ?_⟩
      intro x hx
      exact ⟨hx.2, hx.1⟩
    exact (hSflat.contDiffWithinAt hpflat).mono_of_mem_nhdsWithin hmem
  · have hp2ne : ‖p.2‖ ≠ 0 := by
      intro h
      exact hv (norm_eq_zero.mp h)
    have hp2pos : 0 < ‖p.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp2ne)
    have hppos : p ∈ S ∩ S_pos := by
      exact ⟨hp, hp2pos⟩
    have hmem : S ∩ S_pos ∈ nhdsWithin p S := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨S_pos, hSpos_open.mem_nhds hp2pos, ?_⟩
      intro x hx
      exact ⟨hx.2, hx.1⟩
    exact (hSpos.contDiffWithinAt hppos).mono_of_mem_nhdsWithin hmem

end CellAttachment

end
end DifferentialGeometry.Topology.Morse
