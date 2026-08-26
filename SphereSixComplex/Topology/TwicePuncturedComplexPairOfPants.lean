module

public import SphereSixComplex.Topology.TwicePuncturedComplexMarkedMeridians
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The marked pair-of-pants relation in the twice-punctured plane

This module compares the two literal clockwise tangent meridians based at `1/2` with a
clockwise circle enclosing both punctures.  The comparison is an explicit homotopy through
`ℂ \ {0, 1}`; it does not use a presentation or universal-cover marking.
-/

@[expose] public section

open Set Metric

noncomputable section

namespace SphereSixComplex

open SphereSixComplex.Topology
open CategoryTheory

/-- The exterior comparison is first based at the real point `2`. -/
public abbrev paperStandardExteriorBasepoint : TwicePuncturedComplex :=
  ⟨(2 : ℂ), by
    rw [Set.mem_compl_iff]
    norm_num⟩

/-- The literal clockwise radius-two circle enclosing both finite punctures. -/
public def paperStandardClockwiseExteriorPoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨2 * Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
    · intro h
      have hn := congrArg norm h
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I] at hn
      norm_num at hn⟩

@[simp]
public theorem paperStandardClockwiseExteriorPoint_zero :
    paperStandardClockwiseExteriorPoint 0 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  norm_num [paperStandardClockwiseExteriorPoint]

@[simp]
public theorem paperStandardClockwiseExteriorPoint_one :
    paperStandardClockwiseExteriorPoint 1 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  norm_num [paperStandardClockwiseExteriorPoint, Complex.exp_neg,
    Complex.exp_two_pi_mul_I]

public def paperStandardClockwiseExteriorMeridian :
    Path paperStandardExteriorBasepoint paperStandardExteriorBasepoint where
  toFun := paperStandardClockwiseExteriorPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := paperStandardClockwiseExteriorPoint_zero
  target' := paperStandardClockwiseExteriorPoint_one

/-! Rebase the exterior comparison at the common finite-meridian point `1/2`. -/

public def paperStandardExteriorBridgeArcPoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 1 (-(2 : ℝ)⁻¹) (Real.pi * (t : ℝ)), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hzero
      have hs := circleMap_mem_sphere' 1 (-(2 : ℝ)⁻¹) (Real.pi * (t : ℝ))
      rw [Metric.mem_sphere, hzero] at hs
      norm_num [Complex.dist_eq] at hs
    · exact circleMap_ne_center (by norm_num)⟩

public theorem paperStandardExteriorBridgeArcPoint_zero :
    paperStandardExteriorBridgeArcPoint 0 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [paperStandardExteriorBridgeArcPoint, circleMap,
    twicePuncturedComplexBasepoint]

public theorem paperStandardExteriorBridgeArcPoint_one :
    paperStandardExteriorBridgeArcPoint 1 =
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) := by
  apply Subtype.ext
  norm_num [paperStandardExteriorBridgeArcPoint, circleMap,
    Complex.exp_pi_mul_I]

public def paperStandardExteriorBridgeArc :
    Path twicePuncturedComplexBasepoint
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) where
  toFun := paperStandardExteriorBridgeArcPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := paperStandardExteriorBridgeArcPoint_zero
  target' := paperStandardExteriorBridgeArcPoint_one

public def paperStandardExteriorBridgeLinePoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨(3 / 2 : ℂ) + ((t : ℝ) / 2 : ℝ), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> intro h
    · have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [t.2.1]
    · have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [t.2.1]⟩

public theorem paperStandardExteriorBridgeLinePoint_zero :
    paperStandardExteriorBridgeLinePoint 0 =
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) := by
  apply Subtype.ext
  norm_num [paperStandardExteriorBridgeLinePoint]

public theorem paperStandardExteriorBridgeLinePoint_one :
    paperStandardExteriorBridgeLinePoint 1 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  norm_num [paperStandardExteriorBridgeLinePoint]

public def paperStandardExteriorBridgeLine :
    Path
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex)
      paperStandardExteriorBasepoint where
  toFun := paperStandardExteriorBridgeLinePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := paperStandardExteriorBridgeLinePoint_zero
  target' := paperStandardExteriorBridgeLinePoint_one

/-- An explicit lower-half-plane bridge from `1/2` to the exterior point `2`. -/
public def paperStandardExteriorBridge :
    Path twicePuncturedComplexBasepoint paperStandardExteriorBasepoint :=
  paperStandardExteriorBridgeArc.trans paperStandardExteriorBridgeLine

public def paperStandardClockwiseExteriorMeridianAtCommonBasepoint :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint :=
  paperStandardExteriorBridge.trans
    (paperStandardClockwiseExteriorMeridian.trans paperStandardExteriorBridge.symm)

def paperPairOfPantsAngle (t : unitInterval) : ℝ :=
  -Real.pi / 2 - 2 * Real.pi * (t : ℝ)

def paperPairOfPantsValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + |Real.cos (paperPairOfPantsAngle t)| *
    Complex.exp ((paperPairOfPantsAngle t : ℂ) * Complex.I)

theorem paperPairOfPants_cos_angle (t : unitInterval) :
    Real.cos (paperPairOfPantsAngle t) = -Real.sin (2 * Real.pi * (t : ℝ)) := by
  rw [show paperPairOfPantsAngle t = -(2 * Real.pi * (t : ℝ) + Real.pi / 2) by
    simp [paperPairOfPantsAngle]; ring]
  rw [Real.cos_neg, Real.cos_add_pi_div_two]

theorem paperPairOfPants_sin_angle (t : unitInterval) :
    Real.sin (paperPairOfPantsAngle t) = -Real.cos (2 * Real.pi * (t : ℝ)) := by
  rw [show paperPairOfPantsAngle t = -(2 * Real.pi * (t : ℝ) + Real.pi / 2) by
    simp [paperPairOfPantsAngle]; ring]
  rw [Real.sin_neg, Real.sin_add_pi_div_two]

theorem paperPairOfPantsValue_eq_zero_first (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    paperPairOfPantsValue t =
      (twicePuncturedClockwiseZeroMeridian
        ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1]⟩).1 := by
  have hsin : 0 ≤ Real.sin (2 * Real.pi * (t : ℝ)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) t.2.1
    · nlinarith [Real.pi_pos]
  have htarget :
      (twicePuncturedClockwiseZeroMeridian
        ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1]⟩).1 =
      (1 / 2 : ℂ) * Complex.exp (((-4 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
    change circleMap 0 (2 : ℝ)⁻¹ (-((2 : ℝ) * Real.pi * (2 * (t : ℝ)))) = _
    rw [circleMap_zero]
    congr 2
    norm_num
    push_cast
    ring
  rw [htarget]
  rw [paperPairOfPantsValue]
  rw [paperPairOfPants_cos_angle, abs_neg, abs_of_nonneg hsin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    rw [paperPairOfPants_cos_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (t : ℝ))]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    rw [paperPairOfPants_sin_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.sin_two_mul]
    ring

theorem paperPairOfPantsValue_eq_one_second (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    paperPairOfPantsValue t =
      (twicePuncturedClockwiseOneMeridian
        ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.2.2]⟩).1 := by
  have hsin : Real.sin (2 * Real.pi * (t : ℝ)) ≤ 0 := by
    rw [← Real.sin_sub_two_pi]
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
    · have h := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
          (sub_nonpos.mpr t.2.2)
      nlinarith
    · have h := mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
          (sub_nonneg.mpr ht)
      nlinarith
  have htarget :
      (twicePuncturedClockwiseOneMeridian
        ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.2.2]⟩).1 =
      1 - (1 / 2 : ℂ) * Complex.exp (((-4 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
    change circleMap 1 (-(2 : ℝ)⁻¹)
      (-((2 : ℝ) * Real.pi * (2 * (t : ℝ) - 1))) = _
    rw [circleMap]
    have hexp : Complex.exp
        (((-((2 : ℝ) * Real.pi * (2 * (t : ℝ) - 1)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-4 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
      have harg :
          (((-((2 : ℝ) * Real.pi * (2 * (t : ℝ) - 1)) : ℝ) : ℂ) * Complex.I) =
          (((-4 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) +
            2 * Real.pi * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexp]
    norm_num
    ring
  rw [htarget]
  rw [paperPairOfPantsValue]
  rw [paperPairOfPants_cos_angle, abs_neg, abs_of_nonpos hsin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    rw [paperPairOfPants_cos_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (t : ℝ))]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.sub_im, Complex.one_im,
      Complex.exp_ofReal_mul_I_im]
    rw [paperPairOfPants_sin_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.sin_two_mul]
    ring

theorem paperPairOfPants_sin_angle_eq_zero_iff (t : unitInterval) :
    Real.sin (paperPairOfPantsAngle t) = 0 ↔
      (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 3 / 4 := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hangleUpper : paperPairOfPantsAngle t < 0 := by
      unfold paperPairOfPantsAngle
      have hnonneg := mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) t.2.1
      nlinarith [Real.pi_pos]
    have hangleLower : -3 * Real.pi < paperPairOfPantsAngle t := by
      unfold paperPairOfPantsAngle
      have hnonneg := mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
        (sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.2.2))
      nlinarith [Real.pi_pos]
    have hnUpper : (n : ℝ) < 0 := by
      rw [← hn] at hangleUpper
      nlinarith [Real.pi_pos]
    have hnLower : (-3 : ℝ) < n := by
      rw [← hn] at hangleLower
      nlinarith [Real.pi_pos]
    have hnUpperZ : n < 0 := by exact_mod_cast hnUpper
    have hnLowerZ : (-3 : ℤ) < n := by exact_mod_cast hnLower
    have hnCases : n = -1 ∨ n = -2 := by omega
    rcases hnCases with rfl | rfl
    · left
      unfold paperPairOfPantsAngle at hn
      norm_num at hn ⊢
      nlinarith [Real.pi_pos]
    · right
      unfold paperPairOfPantsAngle at hn
      norm_num at hn ⊢
      nlinarith [Real.pi_pos]
  · rintro (ht | ht)
    · refine ⟨-1, ?_⟩
      unfold paperPairOfPantsAngle
      rw [ht]
      norm_num
      ring
    · refine ⟨-2, ?_⟩
      unfold paperPairOfPantsAngle
      rw [ht]
      norm_num
      ring

def paperPairOfPantsLollipopRadius (t : unitInterval) : ℝ :=
  min (3 * (t : ℝ)) (min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))))

def paperPairOfPantsLollipopAngle (t : unitInterval) : ℝ :=
  -Real.pi / 2 - 8 * Real.pi * max 0 (min ((t : ℝ) - 1 / 2) (1 / 4))

theorem paperPairOfPantsLollipopRadius_nonneg (t : unitInterval) :
    0 ≤ paperPairOfPantsLollipopRadius t := by
  unfold paperPairOfPantsLollipopRadius
  apply le_min
  · exact mul_nonneg (by norm_num) t.2.1
  · apply le_min
    · norm_num
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr t.2.2)

theorem continuous_paperPairOfPantsLollipopRadius : Continuous paperPairOfPantsLollipopRadius := by
  unfold paperPairOfPantsLollipopRadius
  fun_prop

theorem continuous_paperPairOfPantsLollipopAngle : Continuous paperPairOfPantsLollipopAngle := by
  unfold paperPairOfPantsLollipopAngle
  fun_prop

theorem paperPairOfPantsLollipopRadius_zero : paperPairOfPantsLollipopRadius 0 = 0 := by
  norm_num [paperPairOfPantsLollipopRadius]

theorem paperPairOfPantsLollipopRadius_one : paperPairOfPantsLollipopRadius 1 = 0 := by
  norm_num [paperPairOfPantsLollipopRadius]

theorem paperPairOfPantsLollipopRadius_quarter :
    paperPairOfPantsLollipopRadius ⟨(1 / 4 : ℝ), by norm_num⟩ = 3 / 4 := by
  norm_num [paperPairOfPantsLollipopRadius]

theorem paperPairOfPantsLollipopRadius_threeQuarter :
    paperPairOfPantsLollipopRadius ⟨(3 / 4 : ℝ), by norm_num⟩ = 3 / 2 := by
  norm_num [paperPairOfPantsLollipopRadius]

theorem paperPairOfPantsLollipopAngle_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    paperPairOfPantsLollipopAngle t = -Real.pi / 2 := by
  unfold paperPairOfPantsLollipopAngle
  rw [min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_left (show (t : ℝ) - 1 / 2 ≤ 0 by linarith)]
  ring

theorem paperPairOfPantsLollipopAngle_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    paperPairOfPantsLollipopAngle t = 7 * Real.pi / 2 - 8 * Real.pi * (t : ℝ) := by
  unfold paperPairOfPantsLollipopAngle
  rw [min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_right (show 0 ≤ (t : ℝ) - 1 / 2 by linarith)]
  ring

theorem paperPairOfPantsLollipopAngle_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    paperPairOfPantsLollipopAngle t = -5 * Real.pi / 2 := by
  unfold paperPairOfPantsLollipopAngle
  rw [min_eq_right (show 1 / 4 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  ring

theorem paperPairOfPantsLollipopRadius_eq_half_iff (t : unitInterval) :
    paperPairOfPantsLollipopRadius t = 1 / 2 ↔
      (t : ℝ) = 1 / 6 ∨ (t : ℝ) = 11 / 12 := by
  constructor
  · intro h
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · left
      have hfirst : paperPairOfPantsLollipopRadius t = 3 * (t : ℝ) := by
        unfold paperPairOfPantsLollipopRadius
        rw [min_eq_left]
        apply le_min
        · nlinarith
        · nlinarith [t.2.1]
      rw [hfirst] at h
      linarith
    · right
      have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
      by_cases htq : (t : ℝ) ≤ 3 / 4
      · have hconst : paperPairOfPantsLollipopRadius t = 3 / 2 := by
          unfold paperPairOfPantsLollipopRadius
          have houter : min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))) ≤ 3 * (t : ℝ) :=
            (min_le_left _ _).trans (by nlinarith)
          have hinner : (3 / 2 : ℝ) ≤ 6 * (1 - (t : ℝ)) := by nlinarith
          rw [min_eq_right houter, min_eq_left hinner]
        rw [hconst] at h
        norm_num at h
      · have hlast : paperPairOfPantsLollipopRadius t = 6 * (1 - (t : ℝ)) := by
          unfold paperPairOfPantsLollipopRadius
          have hinner : 6 * (1 - (t : ℝ)) ≤ (3 / 2 : ℝ) := by nlinarith
          have houter : 6 * (1 - (t : ℝ)) ≤ 3 * (t : ℝ) := by nlinarith
          rw [min_eq_right hinner, min_eq_right houter]
        rw [hlast] at h
        linarith
  · rintro (ht | ht)
    · rw [show t = ⟨(1 / 6 : ℝ), by norm_num⟩ by ext; exact ht]
      norm_num [paperPairOfPantsLollipopRadius]
    · rw [show t = ⟨(11 / 12 : ℝ), by norm_num⟩ by ext; exact ht]
      norm_num [paperPairOfPantsLollipopRadius]

def paperPairOfPantsRadialHomotopyRadius (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * |Real.cos (paperPairOfPantsAngle t)| +
    (s : ℝ) * paperPairOfPantsLollipopRadius t

theorem paperPairOfPantsRadialHomotopyRadius_nonneg (s t : unitInterval) :
    0 ≤ paperPairOfPantsRadialHomotopyRadius s t := by
  unfold paperPairOfPantsRadialHomotopyRadius
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr s.2.2) (abs_nonneg _))
    (mul_nonneg s.2.1 (paperPairOfPantsLollipopRadius_nonneg t))

def paperPairOfPantsRadialHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + paperPairOfPantsRadialHomotopyRadius s t *
    Complex.exp ((paperPairOfPantsAngle t : ℂ) * Complex.I)

theorem paperPairOfPantsRadialHomotopyValue_ne_zero (s t : unitInterval) :
    paperPairOfPantsRadialHomotopyValue s t ≠ 0 := by
  intro hzero
  have hv : (paperPairOfPantsRadialHomotopyRadius s t : ℂ) *
      Complex.exp ((paperPairOfPantsAngle t : ℂ) * Complex.I) = -(1 / 2 : ℂ) := by
    unfold paperPairOfPantsRadialHomotopyValue at hzero
    linear_combination hzero
  have hr : paperPairOfPantsRadialHomotopyRadius s t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (paperPairOfPantsRadialHomotopyRadius_nonneg s t), Complex.norm_exp_ofReal_mul_I] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im, Complex.neg_im] at him
  have hsin : Real.sin (paperPairOfPantsAngle t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (paperPairOfPants_sin_angle_eq_zero_iff t).mp hsin with ht | ht
  · have htSubtype : t = ⟨(1 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold paperPairOfPantsRadialHomotopyRadius at hr
    have hc : |Real.cos (paperPairOfPantsAngle ⟨(1 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show paperPairOfPantsAngle ⟨(1 / 4 : ℝ), by norm_num⟩ = -Real.pi by
        unfold paperPairOfPantsAngle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [paperPairOfPantsLollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]
  · have htSubtype : t = ⟨(3 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold paperPairOfPantsRadialHomotopyRadius at hr
    have hc : |Real.cos (paperPairOfPantsAngle ⟨(3 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show paperPairOfPantsAngle ⟨(3 / 4 : ℝ), by norm_num⟩ = -(2 * Real.pi) by
        unfold paperPairOfPantsAngle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [paperPairOfPantsLollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]

theorem paperPairOfPantsRadialHomotopyValue_ne_one (s t : unitInterval) :
    paperPairOfPantsRadialHomotopyValue s t ≠ 1 := by
  intro hone
  have hv : (paperPairOfPantsRadialHomotopyRadius s t : ℂ) *
      Complex.exp ((paperPairOfPantsAngle t : ℂ) * Complex.I) = (1 / 2 : ℂ) := by
    unfold paperPairOfPantsRadialHomotopyValue at hone
    linear_combination hone
  have hr : paperPairOfPantsRadialHomotopyRadius s t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (paperPairOfPantsRadialHomotopyRadius_nonneg s t), Complex.norm_exp_ofReal_mul_I] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im] at him
  have hsin : Real.sin (paperPairOfPantsAngle t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (paperPairOfPants_sin_angle_eq_zero_iff t).mp hsin with ht | ht
  · have htSubtype : t = ⟨(1 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold paperPairOfPantsRadialHomotopyRadius at hr
    have hc : |Real.cos (paperPairOfPantsAngle ⟨(1 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show paperPairOfPantsAngle ⟨(1 / 4 : ℝ), by norm_num⟩ = -Real.pi by
        unfold paperPairOfPantsAngle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [paperPairOfPantsLollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]
  · have htSubtype : t = ⟨(3 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold paperPairOfPantsRadialHomotopyRadius at hr
    have hc : |Real.cos (paperPairOfPantsAngle ⟨(3 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show paperPairOfPantsAngle ⟨(3 / 4 : ℝ), by norm_num⟩ = -(2 * Real.pi) by
        unfold paperPairOfPantsAngle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [paperPairOfPantsLollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]

def paperPairOfPantsRadialHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsRadialHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsRadialHomotopyValue_ne_zero p.1 p.2,
      paperPairOfPantsRadialHomotopyValue_ne_one p.1 p.2⟩⟩

theorem continuous_paperPairOfPantsRadialHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsRadialHomotopyValue p.1 p.2) := by
  have hr : Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsLollipopRadius p.2) :=
    continuous_paperPairOfPantsLollipopRadius.comp continuous_snd
  unfold paperPairOfPantsRadialHomotopyValue paperPairOfPantsRadialHomotopyRadius paperPairOfPantsAngle
  fun_prop

theorem paperPairOfPantsRadialHomotopyValue_zero_left (t : unitInterval) :
    paperPairOfPantsRadialHomotopyValue 0 t = paperPairOfPantsValue t := by
  simp [paperPairOfPantsRadialHomotopyValue, paperPairOfPantsRadialHomotopyRadius, paperPairOfPantsValue]

def paperPairOfPantsLollipopLinearAngleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + paperPairOfPantsLollipopRadius t *
    Complex.exp ((paperPairOfPantsAngle t : ℂ) * Complex.I)

theorem paperPairOfPantsRadialHomotopyValue_one_left (t : unitInterval) :
    paperPairOfPantsRadialHomotopyValue 1 t = paperPairOfPantsLollipopLinearAngleValue t := by
  simp [paperPairOfPantsRadialHomotopyValue, paperPairOfPantsRadialHomotopyRadius,
    paperPairOfPantsLollipopLinearAngleValue]

theorem paperPairOfPantsRadialHomotopyValue_zero_right (s : unitInterval) :
    paperPairOfPantsRadialHomotopyValue s 0 = (1 / 2 : ℂ) := by
  have hr : paperPairOfPantsRadialHomotopyRadius s 0 = 0 := by
    unfold paperPairOfPantsRadialHomotopyRadius
    rw [paperPairOfPantsLollipopRadius_zero]
    rw [show paperPairOfPantsAngle 0 = -Real.pi / 2 by simp [paperPairOfPantsAngle]]
    have hc : Real.cos (-Real.pi / 2) = 0 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.cos_neg, Real.cos_pi_div_two]
    rw [hc]
    simp
  simp [paperPairOfPantsRadialHomotopyValue, hr]

theorem paperPairOfPantsRadialHomotopyValue_one_right (s : unitInterval) :
    paperPairOfPantsRadialHomotopyValue s 1 = (1 / 2 : ℂ) := by
  have hangle : paperPairOfPantsAngle 1 = -Real.pi / 2 - 2 * Real.pi := by
    unfold paperPairOfPantsAngle
    norm_num
  have hr : paperPairOfPantsRadialHomotopyRadius s 1 = 0 := by
    unfold paperPairOfPantsRadialHomotopyRadius
    rw [paperPairOfPantsLollipopRadius_one, hangle, Real.cos_sub_two_pi]
    have hc : Real.cos (-Real.pi / 2) = 0 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.cos_neg, Real.cos_pi_div_two]
    rw [hc]
    simp
  simp [paperPairOfPantsRadialHomotopyValue, hr]

def paperPairOfPantsAngleHomotopyAngle (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * paperPairOfPantsAngle t + (s : ℝ) * paperPairOfPantsLollipopAngle t

def paperPairOfPantsAngleHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + paperPairOfPantsLollipopRadius t *
    Complex.exp ((paperPairOfPantsAngleHomotopyAngle s t : ℂ) * Complex.I)

theorem paperPairOfPantsAngleHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) :
    paperPairOfPantsAngleHomotopyValue s t ≠ a := by
  intro hpuncture
  have hdist : ‖a - (1 / 2 : ℂ)‖ = 1 / 2 := by rcases ha with rfl | rfl <;> norm_num
  have hv : (paperPairOfPantsLollipopRadius t : ℂ) *
      Complex.exp ((paperPairOfPantsAngleHomotopyAngle s t : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold paperPairOfPantsAngleHomotopyValue at hpuncture
    linear_combination hpuncture
  have hr : paperPairOfPantsLollipopRadius t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperPairOfPantsLollipopRadius_nonneg t),
      Complex.norm_exp_ofReal_mul_I, hdist] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  have haim : (a - (1 / 2 : ℂ)).im = 0 := by rcases ha with rfl | rfl <;> norm_num
  rw [haim] at him
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im] at him
  have hsin : Real.sin (paperPairOfPantsAngleHomotopyAngle s t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (paperPairOfPantsLollipopRadius_eq_half_iff t).mp hr with ht | ht
  · have htSubtype : t = ⟨(1 / 6 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    have hangle : paperPairOfPantsAngleHomotopyAngle s ⟨(1 / 6 : ℝ), by norm_num⟩ =
        -5 * Real.pi / 6 + (s : ℝ) * Real.pi / 3 := by
      unfold paperPairOfPantsAngleHomotopyAngle
      rw [paperPairOfPantsLollipopAngle_eq_left _ (by norm_num)]
      unfold paperPairOfPantsAngle
      norm_num
      ring
    have hsPiNonneg : 0 ≤ (s : ℝ) * Real.pi :=
      mul_nonneg s.2.1 Real.pi_pos.le
    have hsOnePiNonneg : 0 ≤ (1 - (s : ℝ)) * Real.pi :=
      mul_nonneg (sub_nonneg.mpr s.2.2) Real.pi_pos.le
    have hlower : -Real.pi < paperPairOfPantsAngleHomotopyAngle s
        ⟨(1 / 6 : ℝ), by norm_num⟩ := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hupper : paperPairOfPantsAngleHomotopyAngle s
        ⟨(1 / 6 : ℝ), by norm_num⟩ < 0 := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hupper hlower).ne hsin
  · have htSubtype : t = ⟨(11 / 12 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    have hangle : paperPairOfPantsAngleHomotopyAngle s ⟨(11 / 12 : ℝ), by norm_num⟩ +
          2 * Real.pi = -Real.pi / 3 - (s : ℝ) * Real.pi / 6 := by
      unfold paperPairOfPantsAngleHomotopyAngle
      rw [paperPairOfPantsLollipopAngle_eq_right _ (by norm_num)]
      unfold paperPairOfPantsAngle
      norm_num
      ring
    have hsPiNonneg : 0 ≤ (s : ℝ) * Real.pi :=
      mul_nonneg s.2.1 Real.pi_pos.le
    have hsOnePiNonneg : 0 ≤ (1 - (s : ℝ)) * Real.pi :=
      mul_nonneg (sub_nonneg.mpr s.2.2) Real.pi_pos.le
    have hlower : -Real.pi < paperPairOfPantsAngleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hupper : paperPairOfPantsAngleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi < 0 := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hsin' : Real.sin (paperPairOfPantsAngleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi) = 0 := by
      rw [Real.sin_add_two_pi, hsin]
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hupper hlower).ne hsin'

theorem paperPairOfPantsAngleHomotopyValue_ne_zero (s t : unitInterval) :
    paperPairOfPantsAngleHomotopyValue s t ≠ 0 :=
  paperPairOfPantsAngleHomotopyValue_ne_puncture s t 0 (Or.inl rfl)

theorem paperPairOfPantsAngleHomotopyValue_ne_one (s t : unitInterval) :
    paperPairOfPantsAngleHomotopyValue s t ≠ 1 :=
  paperPairOfPantsAngleHomotopyValue_ne_puncture s t 1 (Or.inr rfl)

def paperPairOfPantsAngleHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsAngleHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsAngleHomotopyValue_ne_zero p.1 p.2,
      paperPairOfPantsAngleHomotopyValue_ne_one p.1 p.2⟩⟩

theorem continuous_paperPairOfPantsAngleHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsAngleHomotopyValue p.1 p.2) := by
  have hr : Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsLollipopRadius p.2) :=
    continuous_paperPairOfPantsLollipopRadius.comp continuous_snd
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsLollipopAngle p.2) :=
    continuous_paperPairOfPantsLollipopAngle.comp continuous_snd
  unfold paperPairOfPantsAngleHomotopyValue paperPairOfPantsAngleHomotopyAngle paperPairOfPantsAngle
  fun_prop

def paperPairOfPantsLollipopValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + paperPairOfPantsLollipopRadius t *
    Complex.exp ((paperPairOfPantsLollipopAngle t : ℂ) * Complex.I)

theorem paperPairOfPantsAngleHomotopyValue_zero_left (t : unitInterval) :
    paperPairOfPantsAngleHomotopyValue 0 t = paperPairOfPantsLollipopLinearAngleValue t := by
  simp [paperPairOfPantsAngleHomotopyValue, paperPairOfPantsAngleHomotopyAngle,
    paperPairOfPantsLollipopLinearAngleValue]

theorem paperPairOfPantsAngleHomotopyValue_one_left (t : unitInterval) :
    paperPairOfPantsAngleHomotopyValue 1 t = paperPairOfPantsLollipopValue t := by
  simp [paperPairOfPantsAngleHomotopyValue, paperPairOfPantsAngleHomotopyAngle, paperPairOfPantsLollipopValue]

theorem paperPairOfPantsAngleHomotopyValue_zero_right (s : unitInterval) :
    paperPairOfPantsAngleHomotopyValue s 0 = (1 / 2 : ℂ) := by
  simp [paperPairOfPantsAngleHomotopyValue, paperPairOfPantsLollipopRadius_zero]

theorem paperPairOfPantsAngleHomotopyValue_one_right (s : unitInterval) :
    paperPairOfPantsAngleHomotopyValue s 1 = (1 / 2 : ℂ) := by
  simp [paperPairOfPantsAngleHomotopyValue, paperPairOfPantsLollipopRadius_one]

abbrev paperPairOfPantsCommonBasepoint : ↥(({0, 1} : Set ℂ)ᶜ) :=
  twicePuncturedComplexBasepoint

def paperPairOfPantsPeanutPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  paperPairOfPantsRadialHomotopyPoint (0, t)

def paperPairOfPantsLinearAnglePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  paperPairOfPantsRadialHomotopyPoint (1, t)

def paperPairOfPantsLollipopPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  paperPairOfPantsAngleHomotopyPoint (1, t)

theorem paperPairOfPantsPeanutPoint_zero : paperPairOfPantsPeanutPoint 0 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsPeanutPoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsRadialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsRadialHomotopyValue_zero_right 0

theorem paperPairOfPantsPeanutPoint_one : paperPairOfPantsPeanutPoint 1 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsPeanutPoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsRadialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsRadialHomotopyValue_one_right 0

theorem paperPairOfPantsLinearAnglePoint_zero : paperPairOfPantsLinearAnglePoint 0 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsLinearAnglePoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsRadialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsRadialHomotopyValue_zero_right 1

theorem paperPairOfPantsLinearAnglePoint_one : paperPairOfPantsLinearAnglePoint 1 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsLinearAnglePoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsRadialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsRadialHomotopyValue_one_right 1

theorem paperPairOfPantsLollipopPoint_zero : paperPairOfPantsLollipopPoint 0 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsLollipopPoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsAngleHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsAngleHomotopyValue_zero_right 1

theorem paperPairOfPantsLollipopPoint_one : paperPairOfPantsLollipopPoint 1 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  simpa [paperPairOfPantsLollipopPoint, paperPairOfPantsCommonBasepoint, paperPairOfPantsAngleHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      paperPairOfPantsAngleHomotopyValue_one_right 1

def paperPairOfPantsPeanutLoop : Path paperPairOfPantsCommonBasepoint paperPairOfPantsCommonBasepoint where
  toFun := paperPairOfPantsPeanutPoint
  continuous_toFun := by
    exact (continuous_paperPairOfPantsRadialHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := paperPairOfPantsPeanutPoint_zero
  target' := paperPairOfPantsPeanutPoint_one

def paperPairOfPantsLinearAngleLoop : Path paperPairOfPantsCommonBasepoint paperPairOfPantsCommonBasepoint where
  toFun := paperPairOfPantsLinearAnglePoint
  continuous_toFun := by
    exact (continuous_paperPairOfPantsRadialHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := paperPairOfPantsLinearAnglePoint_zero
  target' := paperPairOfPantsLinearAnglePoint_one

def paperPairOfPantsLollipopLoop : Path paperPairOfPantsCommonBasepoint paperPairOfPantsCommonBasepoint where
  toFun := paperPairOfPantsLollipopPoint
  continuous_toFun := by
    exact (continuous_paperPairOfPantsAngleHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := paperPairOfPantsLollipopPoint_zero
  target' := paperPairOfPantsLollipopPoint_one

def paperPairOfPantsRadialHomotopy : Path.Homotopy paperPairOfPantsPeanutLoop paperPairOfPantsLinearAngleLoop where
  toFun := paperPairOfPantsRadialHomotopyPoint
  continuous_toFun := continuous_paperPairOfPantsRadialHomotopyValue.subtype_mk _
  map_zero_left t := rfl
  map_one_left t := rfl
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      have hbase : (paperPairOfPantsCommonBasepoint).1 = (1 / 2 : ℂ) := by
        norm_num [paperPairOfPantsCommonBasepoint,
          twicePuncturedComplexBasepoint]
      exact (paperPairOfPantsRadialHomotopyValue_zero_right s).trans
        (hbase.symm.trans (congrArg Subtype.val paperPairOfPantsPeanutLoop.source).symm)
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      have hbase : (paperPairOfPantsCommonBasepoint).1 = (1 / 2 : ℂ) := by
        norm_num [paperPairOfPantsCommonBasepoint,
          twicePuncturedComplexBasepoint]
      exact (paperPairOfPantsRadialHomotopyValue_one_right s).trans
        (hbase.symm.trans (congrArg Subtype.val paperPairOfPantsPeanutLoop.target).symm)

def paperPairOfPantsAngleHomotopy : Path.Homotopy paperPairOfPantsLinearAngleLoop paperPairOfPantsLollipopLoop where
  toFun := paperPairOfPantsAngleHomotopyPoint
  continuous_toFun := continuous_paperPairOfPantsAngleHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact (paperPairOfPantsAngleHomotopyValue_zero_left t).trans
      (paperPairOfPantsRadialHomotopyValue_one_left t).symm
  map_one_left t := by
    apply Subtype.ext
    rfl
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      have hbase : (paperPairOfPantsCommonBasepoint).1 = (1 / 2 : ℂ) := by
        norm_num [paperPairOfPantsCommonBasepoint,
          twicePuncturedComplexBasepoint]
      exact (paperPairOfPantsAngleHomotopyValue_zero_right s).trans
        (hbase.symm.trans (congrArg Subtype.val paperPairOfPantsLinearAngleLoop.source).symm)
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      have hbase : (paperPairOfPantsCommonBasepoint).1 = (1 / 2 : ℂ) := by
        norm_num [paperPairOfPantsCommonBasepoint,
          twicePuncturedComplexBasepoint]
      exact (paperPairOfPantsAngleHomotopyValue_one_right s).trans
        (hbase.symm.trans (congrArg Subtype.val paperPairOfPantsLinearAngleLoop.target).symm)

theorem paperPairOfPantsPeanutLoop_eq_finiteComposite :
    paperPairOfPantsPeanutLoop =
      twicePuncturedClockwiseZeroMeridian.trans
        twicePuncturedClockwiseOneMeridian := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change paperPairOfPantsRadialHomotopyValue 0 t = _
  rw [paperPairOfPantsRadialHomotopyValue_zero_left]
  simp only [Path.trans_apply]
  split_ifs with ht
  · exact paperPairOfPantsValue_eq_zero_first t ht
  · exact paperPairOfPantsValue_eq_one_second t (le_of_not_ge ht)

theorem paperPairOfPantsFiniteComposite_class_eq_lollipop :
    Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) =
      Path.Homotopic.Quotient.mk paperPairOfPantsLollipopLoop := by
  rw [← paperPairOfPantsPeanutLoop_eq_finiteComposite, Path.Homotopic.Quotient.eq]
  exact ⟨paperPairOfPantsRadialHomotopy.trans paperPairOfPantsAngleHomotopy⟩

theorem paperPairOfPantsLollipopRadius_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    paperPairOfPantsLollipopRadius t = 3 * (t : ℝ) := by
  unfold paperPairOfPantsLollipopRadius
  rw [min_eq_left]
  apply le_min
  · linarith
  · nlinarith [t.2.1]

theorem paperPairOfPantsLollipopRadius_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    paperPairOfPantsLollipopRadius t = 3 / 2 := by
  unfold paperPairOfPantsLollipopRadius
  have houter : min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))) ≤ 3 * (t : ℝ) :=
    (min_le_left _ _).trans (by nlinarith)
  have hinner : (3 / 2 : ℝ) ≤ 6 * (1 - (t : ℝ)) := by nlinarith
  rw [min_eq_right houter, min_eq_left hinner]

theorem paperPairOfPantsLollipopRadius_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    paperPairOfPantsLollipopRadius t = 6 * (1 - (t : ℝ)) := by
  unfold paperPairOfPantsLollipopRadius
  have hinner : 6 * (1 - (t : ℝ)) ≤ (3 / 2 : ℝ) := by nlinarith
  have houter : 6 * (1 - (t : ℝ)) ≤ 3 * (t : ℝ) := by nlinarith
  rw [min_eq_right hinner, min_eq_right houter]

abbrev paperPairOfPantsLowerCircleBasepoint : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨(1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> intro h
    · have hi := congrArg Complex.im h
      norm_num at hi
    · have hi := congrArg Complex.im h
      norm_num at hi⟩

def paperPairOfPantsLowerWhiskerValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) - ((3 / 2 : ℝ) * (t : ℝ)) * Complex.I

theorem paperPairOfPantsLowerWhiskerValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsLowerWhiskerValue t ≠ a := by
  intro h
  have hi := congrArg Complex.im h
  have haim : a.im = 0 := by rcases ha with rfl | rfl <;> norm_num
  rw [haim] at hi
  simp [paperPairOfPantsLowerWhiskerValue] at hi
  have ht : t = 0 := hi
  subst t
  rcases ha with rfl | rfl <;> norm_num [paperPairOfPantsLowerWhiskerValue] at h

def paperPairOfPantsLowerWhiskerPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsLowerWhiskerValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsLowerWhiskerValue_ne_puncture t 0 (Or.inl rfl),
      paperPairOfPantsLowerWhiskerValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem paperPairOfPantsLowerWhiskerPoint_zero :
    paperPairOfPantsLowerWhiskerPoint 0 = paperPairOfPantsCommonBasepoint := by
  apply Subtype.ext
  norm_num [paperPairOfPantsLowerWhiskerPoint, paperPairOfPantsLowerWhiskerValue, paperPairOfPantsCommonBasepoint,
    twicePuncturedComplexBasepoint]

theorem paperPairOfPantsLowerWhiskerPoint_one :
    paperPairOfPantsLowerWhiskerPoint 1 = paperPairOfPantsLowerCircleBasepoint := by
  apply Subtype.ext
  norm_num [paperPairOfPantsLowerWhiskerPoint, paperPairOfPantsLowerWhiskerValue]

def paperPairOfPantsLowerWhisker : Path paperPairOfPantsCommonBasepoint paperPairOfPantsLowerCircleBasepoint where
  toFun := paperPairOfPantsLowerWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperPairOfPantsLowerWhiskerValue
    fun_prop
  source' := paperPairOfPantsLowerWhiskerPoint_zero
  target' := paperPairOfPantsLowerWhiskerPoint_one

def paperPairOfPantsLowerCircleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((-Real.pi / 2 - 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem paperPairOfPantsLowerCircleValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsLowerCircleValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((-Real.pi / 2 - 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold paperPairOfPantsLowerCircleValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def paperPairOfPantsLowerCirclePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsLowerCircleValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsLowerCircleValue_ne_puncture t 0 (Or.inl rfl),
      paperPairOfPantsLowerCircleValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem paperPairOfPantsLowerCirclePoint_zero :
    paperPairOfPantsLowerCirclePoint 0 = paperPairOfPantsLowerCircleBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsLowerCircleValue 0 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold paperPairOfPantsLowerCircleValue
  have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    all_goals push_cast
    all_goals ring
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl,
    show -Real.pi / 2 - 2 * Real.pi * (0 : ℝ) = -Real.pi / 2 by norm_num,
    hexp]
  norm_num
  ring

theorem paperPairOfPantsLowerCirclePoint_one :
    paperPairOfPantsLowerCirclePoint 1 = paperPairOfPantsLowerCircleBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsLowerCircleValue 1 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold paperPairOfPantsLowerCircleValue
  have hexp : Complex.exp (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [show (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
        (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) - 2 * Real.pi * Complex.I by
      push_cast; ring,
      Complex.exp_sub]
    convert congrArg (fun z : ℂ => z / Complex.exp (2 * Real.pi * Complex.I))
      Complex.exp_neg_pi_div_two_mul_I using 1 <;>
      rw [Complex.exp_two_pi_mul_I] <;> norm_num
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl,
    show -Real.pi / 2 - 2 * Real.pi * (1 : ℝ) = -5 * Real.pi / 2 by
      norm_num; ring,
    hexp]
  norm_num
  ring

def paperPairOfPantsLowerCircle : Path paperPairOfPantsLowerCircleBasepoint paperPairOfPantsLowerCircleBasepoint where
  toFun := paperPairOfPantsLowerCirclePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperPairOfPantsLowerCircleValue
    fun_prop
  source' := paperPairOfPantsLowerCirclePoint_zero
  target' := paperPairOfPantsLowerCirclePoint_one

theorem paperPairOfPantsLollipopLoop_eq_whiskeredLowerCircle :
    paperPairOfPantsLollipopLoop =
      paperPairOfPantsLowerWhisker.trans (paperPairOfPantsLowerCircle.trans paperPairOfPantsLowerWhisker.symm) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change paperPairOfPantsAngleHomotopyValue 1 t = _
  rw [paperPairOfPantsAngleHomotopyValue_one_left]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs with hfirst hsecond
  · change paperPairOfPantsLollipopValue t = paperPairOfPantsLowerWhiskerValue
      ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1]⟩
    rw [paperPairOfPantsLollipopValue, paperPairOfPantsLollipopRadius_eq_left t hfirst,
      paperPairOfPantsLollipopAngle_eq_left t hfirst]
    unfold paperPairOfPantsLowerWhiskerValue
    have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      convert Complex.exp_neg_pi_div_two_mul_I using 1
      all_goals push_cast
      all_goals ring
    rw [hexp]
    norm_num
    ring
  · have hleft : 1 / 2 ≤ (t : ℝ) := by nlinarith
    have hright : (t : ℝ) ≤ 3 / 4 := by nlinarith
    change paperPairOfPantsLollipopValue t = paperPairOfPantsLowerCircleValue
      ⟨2 * (2 * (t : ℝ) - 1), by constructor <;> nlinarith⟩
    rw [paperPairOfPantsLollipopValue, paperPairOfPantsLollipopRadius_eq_middle t hleft hright,
      paperPairOfPantsLollipopAngle_eq_middle t hleft hright]
    unfold paperPairOfPantsLowerCircleValue
    norm_num
    congr 1
    ring
  · have hright : 3 / 4 ≤ (t : ℝ) := by nlinarith
    change paperPairOfPantsLollipopValue t = paperPairOfPantsLowerWhiskerValue
      (unitInterval.symm ⟨2 * (2 * (t : ℝ) - 1) - 1, by
        constructor <;> nlinarith [t.2.2]⟩)
    rw [paperPairOfPantsLollipopValue, paperPairOfPantsLollipopRadius_eq_right t hright,
      paperPairOfPantsLollipopAngle_eq_right t hright]
    unfold paperPairOfPantsLowerWhiskerValue
    have hexp : Complex.exp (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      rw [show (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
          (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) - 2 * Real.pi * Complex.I by
        push_cast; ring,
        Complex.exp_sub]
      convert congrArg (fun z : ℂ => z / Complex.exp (2 * Real.pi * Complex.I))
        Complex.exp_neg_pi_div_two_mul_I using 1 <;>
        rw [Complex.exp_two_pi_mul_I] <;> norm_num
    rw [hexp]
    norm_num
    ring

def paperPairOfPantsLowerToExteriorArcValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) * Complex.exp
    (((-Real.pi / 2 + Real.pi / 2 * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem paperPairOfPantsLowerToExteriorArcValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsLowerToExteriorArcValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) * Complex.exp
      (((-Real.pi / 2 + Real.pi / 2 * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold paperPairOfPantsLowerToExteriorArcValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def paperPairOfPantsLowerToExteriorArcPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsLowerToExteriorArcValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsLowerToExteriorArcValue_ne_puncture t 0 (Or.inl rfl),
      paperPairOfPantsLowerToExteriorArcValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem paperPairOfPantsLowerToExteriorArcPoint_zero :
    paperPairOfPantsLowerToExteriorArcPoint 0 = paperPairOfPantsLowerCircleBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsLowerToExteriorArcValue 0 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold paperPairOfPantsLowerToExteriorArcValue
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    all_goals push_cast
    all_goals ring
  rw [show -Real.pi / 2 + Real.pi / 2 * (0 : ℝ) = -Real.pi / 2 by norm_num,
    hexp]
  norm_num
  ring

theorem paperPairOfPantsLowerToExteriorArcPoint_one :
    paperPairOfPantsLowerToExteriorArcPoint 1 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsLowerToExteriorArcValue 1 = (2 : ℂ)
  unfold paperPairOfPantsLowerToExteriorArcValue
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl,
    show -Real.pi / 2 + Real.pi / 2 * (1 : ℝ) = 0 by ring]
  norm_num

def paperPairOfPantsLowerToExteriorArc :
    Path paperPairOfPantsLowerCircleBasepoint paperStandardExteriorBasepoint where
  toFun := paperPairOfPantsLowerToExteriorArcPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperPairOfPantsLowerToExteriorArcValue
    fun_prop
  source' := paperPairOfPantsLowerToExteriorArcPoint_zero
  target' := paperPairOfPantsLowerToExteriorArcPoint_one

theorem paperPairOfPantsLowerToExteriorArc_coe (t : unitInterval) :
    (paperPairOfPantsLowerToExteriorArc t).1 = paperPairOfPantsLowerToExteriorArcValue t := rfl

def paperPairOfPantsCenteredExteriorCircleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem paperPairOfPantsCenteredExteriorCircleValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsCenteredExteriorCircleValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold paperPairOfPantsCenteredExteriorCircleValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def paperPairOfPantsCenteredExteriorCirclePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsCenteredExteriorCircleValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsCenteredExteriorCircleValue_ne_puncture t 0 (Or.inl rfl),
      paperPairOfPantsCenteredExteriorCircleValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem paperPairOfPantsCenteredExteriorCirclePoint_zero :
    paperPairOfPantsCenteredExteriorCirclePoint 0 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsCenteredExteriorCircleValue 0 = (2 : ℂ)
  unfold paperPairOfPantsCenteredExteriorCircleValue
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  norm_num

theorem paperPairOfPantsCenteredExteriorCirclePoint_one :
    paperPairOfPantsCenteredExteriorCirclePoint 1 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  change paperPairOfPantsCenteredExteriorCircleValue 1 = (2 : ℂ)
  unfold paperPairOfPantsCenteredExteriorCircleValue
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]

def paperPairOfPantsCenteredExteriorCircle :
    Path paperStandardExteriorBasepoint paperStandardExteriorBasepoint where
  toFun := paperPairOfPantsCenteredExteriorCirclePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperPairOfPantsCenteredExteriorCircleValue
    fun_prop
  source' := paperPairOfPantsCenteredExteriorCirclePoint_zero
  target' := paperPairOfPantsCenteredExteriorCirclePoint_one

def paperPairOfPantsRebasedCircleAngle (t : unitInterval) : ℝ :=
  -Real.pi / 2 + Real.pi * min (t : ℝ) (1 / 2) -
    8 * Real.pi * max 0 (min ((t : ℝ) - 1 / 2) (1 / 4)) -
      2 * Real.pi * max 0 ((t : ℝ) - 3 / 4)

theorem continuous_paperPairOfPantsRebasedCircleAngle : Continuous paperPairOfPantsRebasedCircleAngle := by
  unfold paperPairOfPantsRebasedCircleAngle
  fun_prop

theorem paperPairOfPantsRebasedCircleAngle_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    paperPairOfPantsRebasedCircleAngle t = -Real.pi / 2 + Real.pi * (t : ℝ) := by
  unfold paperPairOfPantsRebasedCircleAngle
  rw [min_eq_left ht,
    min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_left (show (t : ℝ) - 1 / 2 ≤ 0 by linarith),
    max_eq_left (show (t : ℝ) - 3 / 4 ≤ 0 by linarith)]
  ring

theorem paperPairOfPantsRebasedCircleAngle_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    paperPairOfPantsRebasedCircleAngle t = 4 * Real.pi - 8 * Real.pi * (t : ℝ) := by
  unfold paperPairOfPantsRebasedCircleAngle
  rw [min_eq_right hleft,
    min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_right (show 0 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_left (show (t : ℝ) - 3 / 4 ≤ 0 by linarith)]
  ring

theorem paperPairOfPantsRebasedCircleAngle_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    paperPairOfPantsRebasedCircleAngle t = -Real.pi / 2 - 2 * Real.pi * (t : ℝ) := by
  unfold paperPairOfPantsRebasedCircleAngle
  rw [min_eq_right (show 1 / 2 ≤ (t : ℝ) by linarith),
    min_eq_right (show 1 / 4 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4),
    max_eq_right (show 0 ≤ (t : ℝ) - 3 / 4 by linarith)]
  ring

def paperPairOfPantsCircleRebaseHomotopyAngle (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * (-Real.pi / 2 - 2 * Real.pi * (t : ℝ)) +
    (s : ℝ) * paperPairOfPantsRebasedCircleAngle t

def paperPairOfPantsCircleRebaseHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((paperPairOfPantsCircleRebaseHomotopyAngle s t : ℝ) : ℂ) * Complex.I)

theorem paperPairOfPantsCircleRebaseHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsCircleRebaseHomotopyValue s t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((paperPairOfPantsCircleRebaseHomotopyAngle s t : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold paperPairOfPantsCircleRebaseHomotopyValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def paperPairOfPantsCircleRebaseHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsCircleRebaseHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsCircleRebaseHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      paperPairOfPantsCircleRebaseHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_paperPairOfPantsCircleRebaseHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsCircleRebaseHomotopyValue p.1 p.2) := by
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsRebasedCircleAngle p.2) :=
    continuous_paperPairOfPantsRebasedCircleAngle.comp continuous_snd
  unfold paperPairOfPantsCircleRebaseHomotopyValue paperPairOfPantsCircleRebaseHomotopyAngle
  fun_prop

def paperPairOfPantsRebasedCenteredCircle : Path paperPairOfPantsLowerCircleBasepoint paperPairOfPantsLowerCircleBasepoint :=
  paperPairOfPantsLowerToExteriorArc.trans
    (paperPairOfPantsCenteredExteriorCircle.trans paperPairOfPantsLowerToExteriorArc.symm)

theorem paperPairOfPantsCircleRebaseHomotopyValue_zero_left (t : unitInterval) :
    paperPairOfPantsCircleRebaseHomotopyValue 0 t = paperPairOfPantsLowerCircleValue t := by
  simp [paperPairOfPantsCircleRebaseHomotopyValue, paperPairOfPantsCircleRebaseHomotopyAngle,
    paperPairOfPantsLowerCircleValue]

theorem paperPairOfPantsCircleRebaseHomotopyValue_one_left (t : unitInterval) :
    paperPairOfPantsCircleRebaseHomotopyValue 1 t = (paperPairOfPantsRebasedCenteredCircle t).1 := by
  simp [paperPairOfPantsCircleRebaseHomotopyValue, paperPairOfPantsCircleRebaseHomotopyAngle,
    paperPairOfPantsRebasedCenteredCircle]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs with hfirst hsecond
  · rw [paperPairOfPantsRebasedCircleAngle_eq_left t hfirst]
    unfold paperPairOfPantsLowerToExteriorArc paperPairOfPantsLowerToExteriorArcPoint
      paperPairOfPantsLowerToExteriorArcValue
    norm_num
    congr 1
    ring
  · have hleft : 1 / 2 ≤ (t : ℝ) := by nlinarith
    have hright : (t : ℝ) ≤ 3 / 4 := by nlinarith
    rw [paperPairOfPantsRebasedCircleAngle_eq_middle t hleft hright]
    unfold paperPairOfPantsCenteredExteriorCircle paperPairOfPantsCenteredExteriorCirclePoint
      paperPairOfPantsCenteredExteriorCircleValue
    norm_num
    congr 1
    ring
  · have hright : 3 / 4 ≤ (t : ℝ) := by nlinarith
    rw [paperPairOfPantsRebasedCircleAngle_eq_right t hright]
    simp only [Function.comp_apply, paperPairOfPantsLowerToExteriorArc_coe]
    unfold paperPairOfPantsLowerToExteriorArcValue
    have hexp (x : ℝ) : Complex.exp (((x - 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((x : ℂ) * Complex.I) := by
      rw [show (((x - 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          (x : ℂ) * Complex.I - 2 * Real.pi * Complex.I by push_cast; ring,
        Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    rw [show -Real.pi / 2 - 2 * Real.pi * (t : ℝ) =
        (3 * Real.pi / 2 - 2 * Real.pi * (t : ℝ)) - 2 * Real.pi by ring,
      hexp]
    simp only [unitInterval.symm]
    norm_num
    congr 1
    ring

theorem paperPairOfPantsCircleRebaseHomotopyValue_zero_right (s : unitInterval) :
    paperPairOfPantsCircleRebaseHomotopyValue s 0 =
      (paperPairOfPantsLowerCircleBasepoint).1 := by
  have hsource : -Real.pi / 2 - 2 * Real.pi * ((0 : unitInterval) : ℝ) =
      -Real.pi / 2 := by norm_num
  have htarget : paperPairOfPantsRebasedCircleAngle 0 = -Real.pi / 2 := by
    rw [paperPairOfPantsRebasedCircleAngle_eq_left 0 (by norm_num)]
    norm_num
  unfold paperPairOfPantsCircleRebaseHomotopyValue paperPairOfPantsCircleRebaseHomotopyAngle
  rw [hsource, htarget]
  have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    all_goals push_cast
    all_goals ring
  rw [show (1 - (s : ℝ)) * (-Real.pi / 2) + (s : ℝ) * (-Real.pi / 2) =
      -Real.pi / 2 by ring,
    hexp]
  norm_num
  ring

theorem paperPairOfPantsCircleRebaseHomotopyValue_one_right (s : unitInterval) :
    paperPairOfPantsCircleRebaseHomotopyValue s 1 =
      (paperPairOfPantsLowerCircleBasepoint).1 := by
  have hsource : -Real.pi / 2 - 2 * Real.pi * ((1 : unitInterval) : ℝ) =
      -5 * Real.pi / 2 := by norm_num; ring
  have htarget : paperPairOfPantsRebasedCircleAngle 1 = -5 * Real.pi / 2 := by
    rw [paperPairOfPantsRebasedCircleAngle_eq_right 1 (by norm_num)]
    norm_num
    ring
  unfold paperPairOfPantsCircleRebaseHomotopyValue paperPairOfPantsCircleRebaseHomotopyAngle
  rw [hsource, htarget]
  have hexp : Complex.exp (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [show (((-5 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
        (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) - 2 * Real.pi * Complex.I by
      push_cast; ring,
      Complex.exp_sub]
    convert congrArg (fun z : ℂ => z / Complex.exp (2 * Real.pi * Complex.I))
      Complex.exp_neg_pi_div_two_mul_I using 1 <;>
      rw [Complex.exp_two_pi_mul_I] <;> norm_num
  rw [show (1 - (s : ℝ)) * (-5 * Real.pi / 2) + (s : ℝ) * (-5 * Real.pi / 2) =
      -5 * Real.pi / 2 by ring,
    hexp]
  norm_num
  ring

def paperPairOfPantsCircleRebaseHomotopy :
    Path.Homotopy paperPairOfPantsLowerCircle paperPairOfPantsRebasedCenteredCircle where
  toFun := paperPairOfPantsCircleRebaseHomotopyPoint
  continuous_toFun := continuous_paperPairOfPantsCircleRebaseHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact paperPairOfPantsCircleRebaseHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact paperPairOfPantsCircleRebaseHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (paperPairOfPantsCircleRebaseHomotopyValue_zero_right s).trans
        (congrArg Subtype.val paperPairOfPantsLowerCircle.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (paperPairOfPantsCircleRebaseHomotopyValue_one_right s).trans
        (congrArg Subtype.val paperPairOfPantsLowerCircle.target).symm

def paperPairOfPantsCircleExpansionCenter (s : unitInterval) : ℝ :=
  (1 - (s : ℝ)) / 2

def paperPairOfPantsCircleExpansionRadius (s : unitInterval) : ℝ :=
  (3 + (s : ℝ)) / 2

def paperPairOfPantsCircleExpansionHomotopyValue (s t : unitInterval) : ℂ :=
  (paperPairOfPantsCircleExpansionCenter s : ℂ) + paperPairOfPantsCircleExpansionRadius s *
    Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem paperPairOfPantsCircleExpansionRadius_pos (s : unitInterval) :
    0 < paperPairOfPantsCircleExpansionRadius s := by
  unfold paperPairOfPantsCircleExpansionRadius
  nlinarith [s.2.1]

theorem paperPairOfPantsCircleExpansionHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsCircleExpansionHomotopyValue s t ≠ a := by
  intro h
  have hv : (paperPairOfPantsCircleExpansionRadius s : ℂ) *
      Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - paperPairOfPantsCircleExpansionCenter s := by
    unfold paperPairOfPantsCircleExpansionHomotopyValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (paperPairOfPantsCircleExpansionRadius_pos s),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl
  · have hcNonneg : 0 ≤ paperPairOfPantsCircleExpansionCenter s := by
      unfold paperPairOfPantsCircleExpansionCenter
      nlinarith [s.2.2]
    rw [show (0 : ℂ) - paperPairOfPantsCircleExpansionCenter s =
        (-(paperPairOfPantsCircleExpansionCenter s) : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hcNonneg] at hn
    unfold paperPairOfPantsCircleExpansionRadius paperPairOfPantsCircleExpansionCenter at hn
    nlinarith [s.2.1]
  · have hcOneNonneg : 0 ≤ 1 - paperPairOfPantsCircleExpansionCenter s := by
      unfold paperPairOfPantsCircleExpansionCenter
      nlinarith [s.2.1]
    rw [show (1 : ℂ) - paperPairOfPantsCircleExpansionCenter s =
        ((1 - paperPairOfPantsCircleExpansionCenter s : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcOneNonneg] at hn
    unfold paperPairOfPantsCircleExpansionRadius paperPairOfPantsCircleExpansionCenter at hn
    nlinarith [s.2.2]

def paperPairOfPantsCircleExpansionHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsCircleExpansionHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsCircleExpansionHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      paperPairOfPantsCircleExpansionHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_paperPairOfPantsCircleExpansionHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsCircleExpansionHomotopyValue p.1 p.2) := by
  unfold paperPairOfPantsCircleExpansionHomotopyValue paperPairOfPantsCircleExpansionCenter
    paperPairOfPantsCircleExpansionRadius
  fun_prop

theorem paperStandardClockwiseExteriorMeridian_coe (t : unitInterval) :
    (paperStandardClockwiseExteriorMeridian t).1 =
      2 * Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rfl

theorem paperPairOfPantsCircleExpansionHomotopyValue_zero_left (t : unitInterval) :
    paperPairOfPantsCircleExpansionHomotopyValue 0 t = paperPairOfPantsCenteredExteriorCircleValue t := by
  simp [paperPairOfPantsCircleExpansionHomotopyValue, paperPairOfPantsCircleExpansionCenter,
    paperPairOfPantsCircleExpansionRadius, paperPairOfPantsCenteredExteriorCircleValue]

theorem paperPairOfPantsCircleExpansionHomotopyValue_one_left (t : unitInterval) :
    paperPairOfPantsCircleExpansionHomotopyValue 1 t =
      (paperStandardClockwiseExteriorMeridian t).1 := by
  rw [paperStandardClockwiseExteriorMeridian_coe]
  simp [paperPairOfPantsCircleExpansionHomotopyValue, paperPairOfPantsCircleExpansionCenter,
    paperPairOfPantsCircleExpansionRadius]
  norm_num

theorem paperPairOfPantsCircleExpansionHomotopyValue_zero_right (s : unitInterval) :
    paperPairOfPantsCircleExpansionHomotopyValue s 0 = (paperStandardExteriorBasepoint).1 := by
  unfold paperPairOfPantsCircleExpansionHomotopyValue paperPairOfPantsCircleExpansionCenter
    paperPairOfPantsCircleExpansionRadius
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  norm_num
  ring

theorem paperPairOfPantsCircleExpansionHomotopyValue_one_right (s : unitInterval) :
    paperPairOfPantsCircleExpansionHomotopyValue s 1 = (paperStandardExteriorBasepoint).1 := by
  unfold paperPairOfPantsCircleExpansionHomotopyValue paperPairOfPantsCircleExpansionCenter
    paperPairOfPantsCircleExpansionRadius
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]
  ring

def paperPairOfPantsCircleExpansionHomotopy :
    Path.Homotopy paperPairOfPantsCenteredExteriorCircle paperStandardClockwiseExteriorMeridian where
  toFun := paperPairOfPantsCircleExpansionHomotopyPoint
  continuous_toFun := continuous_paperPairOfPantsCircleExpansionHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact paperPairOfPantsCircleExpansionHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact paperPairOfPantsCircleExpansionHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (paperPairOfPantsCircleExpansionHomotopyValue_zero_right s).trans
        (congrArg Subtype.val paperPairOfPantsCenteredExteriorCircle.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (paperPairOfPantsCircleExpansionHomotopyValue_one_right s).trans
        (congrArg Subtype.val paperPairOfPantsCenteredExteriorCircle.target).symm

def paperPairOfPantsAlternativeExteriorBridge :
    Path paperPairOfPantsCommonBasepoint paperStandardExteriorBasepoint :=
  paperPairOfPantsLowerWhisker.trans paperPairOfPantsLowerToExteriorArc

theorem paperStandardExteriorBridgeArc_coe (t : unitInterval) :
    (paperStandardExteriorBridgeArc t).1 =
      circleMap 1 (-(2 : ℝ)⁻¹) (Real.pi * (t : ℝ)) := rfl

theorem paperStandardExteriorBridgeLine_coe (t : unitInterval) :
    (paperStandardExteriorBridgeLine t).1 =
      (3 / 2 : ℂ) + ((t : ℝ) / 2 : ℝ) := rfl

theorem paperPairOfPantsLowerWhisker_coe (t : unitInterval) :
    (paperPairOfPantsLowerWhisker t).1 = paperPairOfPantsLowerWhiskerValue t := rfl

theorem paperStandardExteriorBridge_im_nonpos (t : unitInterval) :
    (paperStandardExteriorBridge t).1.im ≤ 0 := by
  unfold paperStandardExteriorBridge
  simp only [Path.trans_apply]
  split_ifs with ht
  · rw [paperStandardExteriorBridgeArc_coe]
    unfold circleMap
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    have hsin : 0 ≤ Real.sin (Real.pi * (2 * (t : ℝ))) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact mul_nonneg Real.pi_pos.le (by nlinarith [t.2.1])
      · nlinarith [Real.pi_pos]
    norm_num
    nlinarith
  · rw [paperStandardExteriorBridgeLine_coe]
    norm_num

theorem paperPairOfPantsAlternativeExteriorBridge_im_neg (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (paperPairOfPantsAlternativeExteriorBridge t).1.im < 0 := by
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (by
    intro h
    apply ht0
    ext
    exact h.symm)
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (by
    intro h
    apply ht1
    ext
    exact h)
  unfold paperPairOfPantsAlternativeExteriorBridge
  simp only [Path.trans_apply]
  split_ifs with ht
  · let u : unitInterval := ⟨2 * (t : ℝ), by
      constructor
      · exact mul_nonneg (by norm_num) t.2.1
      · nlinarith⟩
    change (paperPairOfPantsLowerWhisker u).1.im < 0
    rw [paperPairOfPantsLowerWhisker_coe]
    have himval : (paperPairOfPantsLowerWhiskerValue u).im = -(3 / 2 * (u : ℝ)) := by
      unfold paperPairOfPantsLowerWhiskerValue
      norm_num
    rw [himval]
    change -(3 / 2 * (2 * (t : ℝ))) < 0
    nlinarith
  · rw [paperPairOfPantsLowerToExteriorArc_coe]
    unfold paperPairOfPantsLowerToExteriorArcValue
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    have hangleLower : -Real.pi <
        -Real.pi / 2 + Real.pi / 2 * (2 * (t : ℝ) - 1) := by
      have hprod := mul_pos Real.pi_pos htpos
      nlinarith [Real.pi_pos]
    have hangleUpper :
        -Real.pi / 2 + Real.pi / 2 * (2 * (t : ℝ) - 1) < 0 := by
      have hprod := mul_pos Real.pi_pos (sub_pos.mpr htlt)
      nlinarith [Real.pi_pos]
    have hsin := Real.sin_neg_of_neg_of_neg_pi_lt hangleUpper hangleLower
    norm_num
    nlinarith

def paperPairOfPantsBridgeHomotopyValue (s t : unitInterval) : ℂ :=
  (1 - (s : ℝ)) * (paperStandardExteriorBridge t).1 +
    (s : ℝ) * (paperPairOfPantsAlternativeExteriorBridge t).1

theorem paperPairOfPantsBridgeHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : paperPairOfPantsBridgeHomotopyValue s t ≠ a := by
  intro h
  by_cases ht0 : t = 0
  · subst t
    have hpaper := congrArg Subtype.val paperStandardExteriorBridge.source
    have halt := congrArg Subtype.val paperPairOfPantsAlternativeExteriorBridge.source
    unfold paperPairOfPantsBridgeHomotopyValue at h
    rw [hpaper, halt] at h
    rcases ha with rfl | rfl
    · have hr := congrArg Complex.re h
      norm_num [paperPairOfPantsCommonBasepoint,
        twicePuncturedComplexBasepoint] at hr
      nlinarith
    · have hr := congrArg Complex.re h
      norm_num [paperPairOfPantsCommonBasepoint,
        twicePuncturedComplexBasepoint] at hr
      nlinarith
  · by_cases ht1 : t = 1
    · subst t
      have hpaper := congrArg Subtype.val paperStandardExteriorBridge.target
      have halt := congrArg Subtype.val paperPairOfPantsAlternativeExteriorBridge.target
      unfold paperPairOfPantsBridgeHomotopyValue at h
      rw [hpaper, halt] at h
      rcases ha with rfl | rfl
      · have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith
      · have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith
    · have hpaperIm := paperStandardExteriorBridge_im_nonpos t
      have haltIm := paperPairOfPantsAlternativeExteriorBridge_im_neg t ht0 ht1
      have haim : a.im = 0 := by rcases ha with rfl | rfl <;> norm_num
      have him := congrArg Complex.im h
      unfold paperPairOfPantsBridgeHomotopyValue at him
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] at him
      rw [haim] at him
      norm_num at him
      have hsZero : (s : ℝ) = 0 := by
        by_contra hs
        have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs)
        have hfirst : (1 - (s : ℝ)) * (paperStandardExteriorBridge t).1.im ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr s.2.2) hpaperIm
        have hsecond : (s : ℝ) * (paperPairOfPantsAlternativeExteriorBridge t).1.im < 0 :=
          mul_neg_of_pos_of_neg hspos haltIm
        nlinarith
      have hsSubtype : s = 0 := by ext; exact hsZero
      subst s
      simp [paperPairOfPantsBridgeHomotopyValue] at h
      exact (show (paperStandardExteriorBridge t).1 ≠ a from by
        rcases (paperStandardExteriorBridge t).2 with hmem
        rw [Set.mem_compl_iff] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
        rcases ha with rfl | rfl
        · exact hmem.1
        · exact hmem.2) h

def paperPairOfPantsBridgeHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨paperPairOfPantsBridgeHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨paperPairOfPantsBridgeHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      paperPairOfPantsBridgeHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_paperPairOfPantsBridgeHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      paperPairOfPantsBridgeHomotopyValue p.1 p.2) := by
  unfold paperPairOfPantsBridgeHomotopyValue
  have hp : Continuous (fun p : unitInterval × unitInterval =>
      (paperStandardExteriorBridge p.2).1) :=
    continuous_subtype_val.comp (paperStandardExteriorBridge.continuous.comp continuous_snd)
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      (paperPairOfPantsAlternativeExteriorBridge p.2).1) :=
    continuous_subtype_val.comp
      (paperPairOfPantsAlternativeExteriorBridge.continuous.comp continuous_snd)
  fun_prop

theorem paperPairOfPantsBridgeHomotopyValue_zero_left (t : unitInterval) :
    paperPairOfPantsBridgeHomotopyValue 0 t = (paperStandardExteriorBridge t).1 := by
  simp [paperPairOfPantsBridgeHomotopyValue]

theorem paperPairOfPantsBridgeHomotopyValue_one_left (t : unitInterval) :
    paperPairOfPantsBridgeHomotopyValue 1 t = (paperPairOfPantsAlternativeExteriorBridge t).1 := by
  simp [paperPairOfPantsBridgeHomotopyValue]

theorem paperPairOfPantsBridgeHomotopyValue_zero_right (s : unitInterval) :
    paperPairOfPantsBridgeHomotopyValue s 0 = (paperPairOfPantsCommonBasepoint).1 := by
  unfold paperPairOfPantsBridgeHomotopyValue
  rw [congrArg Subtype.val paperStandardExteriorBridge.source,
    congrArg Subtype.val paperPairOfPantsAlternativeExteriorBridge.source]
  ring

theorem paperPairOfPantsBridgeHomotopyValue_one_right (s : unitInterval) :
    paperPairOfPantsBridgeHomotopyValue s 1 = (paperStandardExteriorBasepoint).1 := by
  unfold paperPairOfPantsBridgeHomotopyValue
  rw [congrArg Subtype.val paperStandardExteriorBridge.target,
    congrArg Subtype.val paperPairOfPantsAlternativeExteriorBridge.target]
  push_cast
  ring

def paperPairOfPantsBridgeHomotopy :
    Path.Homotopy paperStandardExteriorBridge paperPairOfPantsAlternativeExteriorBridge where
  toFun := paperPairOfPantsBridgeHomotopyPoint
  continuous_toFun := continuous_paperPairOfPantsBridgeHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact paperPairOfPantsBridgeHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact paperPairOfPantsBridgeHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (paperPairOfPantsBridgeHomotopyValue_zero_right s).trans
        (congrArg Subtype.val paperStandardExteriorBridge.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (paperPairOfPantsBridgeHomotopyValue_one_right s).trans
        (congrArg Subtype.val paperStandardExteriorBridge.target).symm

theorem paperPairOfPantsAlternativeExteriorBridge_symm_class :
    Path.Homotopic.Quotient.mk paperPairOfPantsAlternativeExteriorBridge.symm =
      Path.Homotopic.Quotient.mk
        (paperPairOfPantsLowerToExteriorArc.symm.trans paperPairOfPantsLowerWhisker.symm) := by
  unfold paperPairOfPantsAlternativeExteriorBridge
  simp only [Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_trans]
  let p := Path.Homotopic.Quotient.mk paperPairOfPantsLowerWhisker
  let q := Path.Homotopic.Quotient.mk paperPairOfPantsLowerToExteriorArc
  have hrightInverse : Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.trans p q)
      (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm q) (Path.Homotopic.Quotient.symm p)) =
      Path.Homotopic.Quotient.refl paperPairOfPantsCommonBasepoint := by
    calc
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.trans p q)
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm q) (Path.Homotopic.Quotient.symm p)) =
          Path.Homotopic.Quotient.trans p
            (Path.Homotopic.Quotient.trans q
              (Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.symm q)
                (Path.Homotopic.Quotient.symm p))) :=
        Path.Homotopic.Quotient.trans_assoc _ _ _
      _ = Path.Homotopic.Quotient.trans p
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans q (Path.Homotopic.Quotient.symm q))
            (Path.Homotopic.Quotient.symm p)) := by
        rw [Path.Homotopic.Quotient.trans_assoc]
      _ = Path.Homotopic.Quotient.trans p (Path.Homotopic.Quotient.symm p) := by
        rw [Path.Homotopic.Quotient.trans_symm,
          Path.Homotopic.Quotient.refl_trans]
      _ = Path.Homotopic.Quotient.refl paperPairOfPantsCommonBasepoint :=
        Path.Homotopic.Quotient.trans_symm p
  symm
  calc
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm q)
        (Path.Homotopic.Quotient.symm p) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.refl paperStandardExteriorBasepoint)
          (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm q)
            (Path.Homotopic.Quotient.symm p)) :=
      (Path.Homotopic.Quotient.refl_trans _).symm
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.symm
            (Path.Homotopic.Quotient.trans p q))
          (Path.Homotopic.Quotient.trans p q))
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm q)
          (Path.Homotopic.Quotient.symm p)) := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ = Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.trans p q))
        (Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans p q)
          (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm q)
            (Path.Homotopic.Quotient.symm p))) :=
      Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.trans p q) := by
      rw [hrightInverse, Path.Homotopic.Quotient.trans_refl]

def paperPairOfPantsAlternativeCenteredOuterLoop :
    Path paperPairOfPantsCommonBasepoint paperPairOfPantsCommonBasepoint :=
  paperPairOfPantsAlternativeExteriorBridge.trans
    (paperPairOfPantsCenteredExteriorCircle.trans paperPairOfPantsAlternativeExteriorBridge.symm)

def paperPairOfPantsPaperCenteredOuterLoop :
    Path paperPairOfPantsCommonBasepoint paperPairOfPantsCommonBasepoint :=
  paperStandardExteriorBridge.trans
    (paperPairOfPantsCenteredExteriorCircle.trans paperStandardExteriorBridge.symm)

def paperPairOfPantsBridgeWhiskeredCenteredHomotopy :
    Path.Homotopy paperPairOfPantsPaperCenteredOuterLoop paperPairOfPantsAlternativeCenteredOuterLoop :=
  paperPairOfPantsBridgeHomotopy.hcomp
    ((Path.Homotopy.refl paperPairOfPantsCenteredExteriorCircle).hcomp
      paperPairOfPantsBridgeHomotopy.symm₂)

def paperPairOfPantsPaperCircleExpansionHomotopy :
    Path.Homotopy paperPairOfPantsPaperCenteredOuterLoop
      paperStandardClockwiseExteriorMeridianAtCommonBasepoint :=
  (Path.Homotopy.refl paperStandardExteriorBridge).hcomp
    (paperPairOfPantsCircleExpansionHomotopy.hcomp
      (Path.Homotopy.refl paperStandardExteriorBridge.symm))

theorem paperPairOfPantsWhiskeredLowerCircle_class_eq_alternativeCentered :
    Path.Homotopic.Quotient.mk
        (paperPairOfPantsLowerWhisker.trans (paperPairOfPantsLowerCircle.trans paperPairOfPantsLowerWhisker.symm)) =
      Path.Homotopic.Quotient.mk paperPairOfPantsAlternativeCenteredOuterLoop := by
  have hcircle : Path.Homotopic.Quotient.mk paperPairOfPantsLowerCircle =
      Path.Homotopic.Quotient.mk paperPairOfPantsRebasedCenteredCircle := by
    rw [Path.Homotopic.Quotient.eq]
    exact ⟨paperPairOfPantsCircleRebaseHomotopy⟩
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [hcircle]
  unfold paperPairOfPantsAlternativeCenteredOuterLoop
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [paperPairOfPantsAlternativeExteriorBridge_symm_class]
  unfold paperPairOfPantsRebasedCenteredCircle paperPairOfPantsAlternativeExteriorBridge
  simp only [Path.Homotopic.Quotient.mk_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem paperPairOfPantsAlternativeCentered_class_eq_standardCommonExterior :
    Path.Homotopic.Quotient.mk paperPairOfPantsAlternativeCenteredOuterLoop =
      Path.Homotopic.Quotient.mk
        paperStandardClockwiseExteriorMeridianAtCommonBasepoint := by
  calc
    Path.Homotopic.Quotient.mk paperPairOfPantsAlternativeCenteredOuterLoop =
        Path.Homotopic.Quotient.mk paperPairOfPantsPaperCenteredOuterLoop := by
      rw [Path.Homotopic.Quotient.eq]
      exact ⟨paperPairOfPantsBridgeWhiskeredCenteredHomotopy.symm⟩
    _ = Path.Homotopic.Quotient.mk
        paperStandardClockwiseExteriorMeridianAtCommonBasepoint := by
      rw [Path.Homotopic.Quotient.eq]
      exact ⟨paperPairOfPantsPaperCircleExpansionHomotopy⟩

theorem paperPairOfPantsExterior_class_eq_finiteComposite :
    Path.Homotopic.Quotient.mk
        paperStandardClockwiseExteriorMeridianAtCommonBasepoint =
      Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) := by
  calc
    Path.Homotopic.Quotient.mk
        paperStandardClockwiseExteriorMeridianAtCommonBasepoint =
        Path.Homotopic.Quotient.mk paperPairOfPantsAlternativeCenteredOuterLoop :=
      paperPairOfPantsAlternativeCentered_class_eq_standardCommonExterior.symm
    _ = Path.Homotopic.Quotient.mk
        (paperPairOfPantsLowerWhisker.trans (paperPairOfPantsLowerCircle.trans paperPairOfPantsLowerWhisker.symm)) :=
      paperPairOfPantsWhiskeredLowerCircle_class_eq_alternativeCentered.symm
    _ = Path.Homotopic.Quotient.mk paperPairOfPantsLollipopLoop := by
      rw [paperPairOfPantsLollipopLoop_eq_whiskeredLowerCircle]
    _ = Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) :=
      paperPairOfPantsFiniteComposite_class_eq_lollipop.symm


end SphereSixComplex

end
