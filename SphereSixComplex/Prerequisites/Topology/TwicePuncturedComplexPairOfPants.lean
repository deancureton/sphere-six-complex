module

public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedComplexMarkedMeridians

/-!
# The marked pair-of-pants relation in the twice-punctured plane

This module compares the two literal clockwise tangent meridians based at `1/2` with a
clockwise circle enclosing both punctures.  The comparison is an explicit homotopy through
`ℂ \ {0, 1}`; it does not use a presentation or universal-cover marking.
-/

@[expose] public section

open Set Metric

noncomputable section

namespace SphereSixComplex.Topology.TwicePuncturedComplex.PairOfPants

open SphereSixComplex.Topology
open CategoryTheory

/-- The exterior comparison is first based at the real point `2`. -/
public abbrev exteriorBasepoint : TwicePuncturedComplex :=
  ⟨(2 : ℂ), by
    rw [Set.mem_compl_iff]
    norm_num⟩

/-- The literal clockwise radius-two circle enclosing both finite punctures. -/
public def clockwiseExteriorPoint (t : unitInterval) :
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
public theorem clockwiseExteriorPoint_zero :
    clockwiseExteriorPoint 0 = exteriorBasepoint := by
  apply Subtype.ext
  norm_num [clockwiseExteriorPoint]

@[simp]
public theorem clockwiseExteriorPoint_one :
    clockwiseExteriorPoint 1 = exteriorBasepoint := by
  apply Subtype.ext
  norm_num [clockwiseExteriorPoint, Complex.exp_neg,
    Complex.exp_two_pi_mul_I]

public def clockwiseExteriorMeridian :
    Path exteriorBasepoint exteriorBasepoint where
  toFun := clockwiseExteriorPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := clockwiseExteriorPoint_zero
  target' := clockwiseExteriorPoint_one

/-! Rebase the exterior comparison at the common finite-meridian point `1/2`. -/

public def exteriorBridgeArcPoint (t : unitInterval) :
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

public theorem exteriorBridgeArcPoint_zero :
    exteriorBridgeArcPoint 0 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [exteriorBridgeArcPoint, circleMap,
    twicePuncturedComplexBasepoint]

public theorem exteriorBridgeArcPoint_one :
    exteriorBridgeArcPoint 1 =
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) := by
  apply Subtype.ext
  norm_num [exteriorBridgeArcPoint, circleMap,
    Complex.exp_pi_mul_I]

public def exteriorBridgeArc :
    Path twicePuncturedComplexBasepoint
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) where
  toFun := exteriorBridgeArcPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := exteriorBridgeArcPoint_zero
  target' := exteriorBridgeArcPoint_one

public def exteriorBridgeLinePoint (t : unitInterval) :
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

public theorem exteriorBridgeLinePoint_zero :
    exteriorBridgeLinePoint 0 =
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex) := by
  apply Subtype.ext
  norm_num [exteriorBridgeLinePoint]

public theorem exteriorBridgeLinePoint_one :
    exteriorBridgeLinePoint 1 = exteriorBasepoint := by
  apply Subtype.ext
  norm_num [exteriorBridgeLinePoint]

public def exteriorBridgeLine :
    Path
      (⟨(3 / 2 : ℂ), by
        rw [Set.mem_compl_iff]
        norm_num⟩ : TwicePuncturedComplex)
      exteriorBasepoint where
  toFun := exteriorBridgeLinePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := exteriorBridgeLinePoint_zero
  target' := exteriorBridgeLinePoint_one

/-- An explicit lower-half-plane bridge from `1/2` to the exterior point `2`. -/
public def exteriorBridge :
    Path twicePuncturedComplexBasepoint exteriorBasepoint :=
  exteriorBridgeArc.trans exteriorBridgeLine

public def clockwiseExteriorMeridianAtBasepoint :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint :=
  exteriorBridge.trans
    (clockwiseExteriorMeridian.trans exteriorBridge.symm)

def angle (t : unitInterval) : ℝ :=
  -Real.pi / 2 - 2 * Real.pi * (t : ℝ)

def value (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + |Real.cos (angle t)| *
    Complex.exp ((angle t : ℂ) * Complex.I)

theorem cos_angle (t : unitInterval) :
    Real.cos (angle t) = -Real.sin (2 * Real.pi * (t : ℝ)) := by
  rw [show angle t = -(2 * Real.pi * (t : ℝ) + Real.pi / 2) by
    simp [angle]; ring]
  rw [Real.cos_neg, Real.cos_add_pi_div_two]

theorem sin_angle (t : unitInterval) :
    Real.sin (angle t) = -Real.cos (2 * Real.pi * (t : ℝ)) := by
  rw [show angle t = -(2 * Real.pi * (t : ℝ) + Real.pi / 2) by
    simp [angle]; ring]
  rw [Real.sin_neg, Real.sin_add_pi_div_two]

theorem value_eq_zero_first (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    value t =
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
  rw [value]
  rw [cos_angle, abs_neg, abs_of_nonneg hsin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    rw [cos_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (t : ℝ))]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    rw [sin_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.sin_two_mul]
    ring

theorem value_eq_one_second (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    value t =
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
  rw [value]
  rw [cos_angle, abs_neg, abs_of_nonpos hsin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    rw [cos_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (t : ℝ))]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.sub_im, Complex.one_im,
      Complex.exp_ofReal_mul_I_im]
    rw [sin_angle]
    norm_num
    rw [show 4 * Real.pi * (t : ℝ) = 2 * (2 * Real.pi * (t : ℝ)) by ring,
      Real.sin_two_mul]
    ring

theorem sin_angle_eq_zero_iff (t : unitInterval) :
    Real.sin (angle t) = 0 ↔
      (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 3 / 4 := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hangleUpper : angle t < 0 := by
      unfold angle
      have hnonneg := mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) t.2.1
      nlinarith [Real.pi_pos]
    have hangleLower : -3 * Real.pi < angle t := by
      unfold angle
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
      unfold angle at hn
      norm_num at hn ⊢
      nlinarith [Real.pi_pos]
    · right
      unfold angle at hn
      norm_num at hn ⊢
      nlinarith [Real.pi_pos]
  · rintro (ht | ht)
    · refine ⟨-1, ?_⟩
      unfold angle
      rw [ht]
      norm_num
      ring
    · refine ⟨-2, ?_⟩
      unfold angle
      rw [ht]
      norm_num
      ring

def lollipopRadius (t : unitInterval) : ℝ :=
  min (3 * (t : ℝ)) (min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))))

def lollipopAngle (t : unitInterval) : ℝ :=
  -Real.pi / 2 - 8 * Real.pi * max 0 (min ((t : ℝ) - 1 / 2) (1 / 4))

theorem lollipopRadius_nonneg (t : unitInterval) :
    0 ≤ lollipopRadius t := by
  unfold lollipopRadius
  apply le_min
  · exact mul_nonneg (by norm_num) t.2.1
  · apply le_min
    · norm_num
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr t.2.2)

theorem continuous_lollipopRadius : Continuous lollipopRadius := by
  unfold lollipopRadius
  fun_prop

theorem continuous_lollipopAngle : Continuous lollipopAngle := by
  unfold lollipopAngle
  fun_prop

theorem lollipopRadius_zero : lollipopRadius 0 = 0 := by
  norm_num [lollipopRadius]

theorem lollipopRadius_one : lollipopRadius 1 = 0 := by
  norm_num [lollipopRadius]



theorem lollipopAngle_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    lollipopAngle t = -Real.pi / 2 := by
  unfold lollipopAngle
  rw [min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_left (show (t : ℝ) - 1 / 2 ≤ 0 by linarith)]
  ring

theorem lollipopAngle_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    lollipopAngle t = 7 * Real.pi / 2 - 8 * Real.pi * (t : ℝ) := by
  unfold lollipopAngle
  rw [min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_right (show 0 ≤ (t : ℝ) - 1 / 2 by linarith)]
  ring

theorem lollipopAngle_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    lollipopAngle t = -5 * Real.pi / 2 := by
  unfold lollipopAngle
  rw [min_eq_right (show 1 / 4 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  ring

theorem lollipopRadius_eq_half_iff (t : unitInterval) :
    lollipopRadius t = 1 / 2 ↔
      (t : ℝ) = 1 / 6 ∨ (t : ℝ) = 11 / 12 := by
  constructor
  · intro h
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · left
      have hfirst : lollipopRadius t = 3 * (t : ℝ) := by
        unfold lollipopRadius
        rw [min_eq_left]
        apply le_min
        · nlinarith
        · nlinarith [t.2.1]
      rw [hfirst] at h
      linarith
    · right
      have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
      by_cases htq : (t : ℝ) ≤ 3 / 4
      · have hconst : lollipopRadius t = 3 / 2 := by
          unfold lollipopRadius
          have houter : min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))) ≤ 3 * (t : ℝ) :=
            (min_le_left _ _).trans (by nlinarith)
          have hinner : (3 / 2 : ℝ) ≤ 6 * (1 - (t : ℝ)) := by nlinarith
          rw [min_eq_right houter, min_eq_left hinner]
        rw [hconst] at h
        norm_num at h
      · have hlast : lollipopRadius t = 6 * (1 - (t : ℝ)) := by
          unfold lollipopRadius
          have hinner : 6 * (1 - (t : ℝ)) ≤ (3 / 2 : ℝ) := by nlinarith
          have houter : 6 * (1 - (t : ℝ)) ≤ 3 * (t : ℝ) := by nlinarith
          rw [min_eq_right hinner, min_eq_right houter]
        rw [hlast] at h
        linarith
  · rintro (ht | ht)
    · rw [show t = ⟨(1 / 6 : ℝ), by norm_num⟩ by ext; exact ht]
      norm_num [lollipopRadius]
    · rw [show t = ⟨(11 / 12 : ℝ), by norm_num⟩ by ext; exact ht]
      norm_num [lollipopRadius]

def radialHomotopyRadius (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * |Real.cos (angle t)| +
    (s : ℝ) * lollipopRadius t

theorem radialHomotopyRadius_nonneg (s t : unitInterval) :
    0 ≤ radialHomotopyRadius s t := by
  unfold radialHomotopyRadius
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr s.2.2) (abs_nonneg _))
    (mul_nonneg s.2.1 (lollipopRadius_nonneg t))

def radialHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + radialHomotopyRadius s t *
    Complex.exp ((angle t : ℂ) * Complex.I)

theorem radialHomotopyValue_ne_zero (s t : unitInterval) :
    radialHomotopyValue s t ≠ 0 := by
  intro hzero
  have hv : (radialHomotopyRadius s t : ℂ) *
      Complex.exp ((angle t : ℂ) * Complex.I) = -(1 / 2 : ℂ) := by
    unfold radialHomotopyValue at hzero
    linear_combination hzero
  have hr : radialHomotopyRadius s t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (radialHomotopyRadius_nonneg s t), Complex.norm_exp_ofReal_mul_I] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im, Complex.neg_im] at him
  have hsin : Real.sin (angle t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (sin_angle_eq_zero_iff t).mp hsin with ht | ht
  · have htSubtype : t = ⟨(1 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold radialHomotopyRadius at hr
    have hc : |Real.cos (angle ⟨(1 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show angle ⟨(1 / 4 : ℝ), by norm_num⟩ = -Real.pi by
        unfold angle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [lollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]
  · have htSubtype : t = ⟨(3 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold radialHomotopyRadius at hr
    have hc : |Real.cos (angle ⟨(3 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show angle ⟨(3 / 4 : ℝ), by norm_num⟩ = -(2 * Real.pi) by
        unfold angle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [lollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]

theorem radialHomotopyValue_ne_one (s t : unitInterval) :
    radialHomotopyValue s t ≠ 1 := by
  intro hone
  have hv : (radialHomotopyRadius s t : ℂ) *
      Complex.exp ((angle t : ℂ) * Complex.I) = (1 / 2 : ℂ) := by
    unfold radialHomotopyValue at hone
    linear_combination hone
  have hr : radialHomotopyRadius s t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (radialHomotopyRadius_nonneg s t), Complex.norm_exp_ofReal_mul_I] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im] at him
  have hsin : Real.sin (angle t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (sin_angle_eq_zero_iff t).mp hsin with ht | ht
  · have htSubtype : t = ⟨(1 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold radialHomotopyRadius at hr
    have hc : |Real.cos (angle ⟨(1 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show angle ⟨(1 / 4 : ℝ), by norm_num⟩ = -Real.pi by
        unfold angle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [lollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]
  · have htSubtype : t = ⟨(3 / 4 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    unfold radialHomotopyRadius at hr
    have hc : |Real.cos (angle ⟨(3 / 4 : ℝ), by norm_num⟩)| = 1 := by
      rw [show angle ⟨(3 / 4 : ℝ), by norm_num⟩ = -(2 * Real.pi) by
        unfold angle
        norm_num
        ring]
      simp
    rw [hc] at hr
    norm_num [lollipopRadius] at hr
    nlinarith [s.2.1, s.2.2]

def radialHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨radialHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨radialHomotopyValue_ne_zero p.1 p.2,
      radialHomotopyValue_ne_one p.1 p.2⟩⟩

theorem continuous_radialHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      radialHomotopyValue p.1 p.2) := by
  have hr : Continuous (fun p : unitInterval × unitInterval =>
      lollipopRadius p.2) :=
    continuous_lollipopRadius.comp continuous_snd
  unfold radialHomotopyValue radialHomotopyRadius angle
  fun_prop

theorem radialHomotopyValue_zero_left (t : unitInterval) :
    radialHomotopyValue 0 t = value t := by
  simp [radialHomotopyValue, radialHomotopyRadius, value]

def lollipopLinearAngleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + lollipopRadius t *
    Complex.exp ((angle t : ℂ) * Complex.I)

theorem radialHomotopyValue_one_left (t : unitInterval) :
    radialHomotopyValue 1 t = lollipopLinearAngleValue t := by
  simp [radialHomotopyValue, radialHomotopyRadius,
    lollipopLinearAngleValue]

theorem radialHomotopyValue_zero_right (s : unitInterval) :
    radialHomotopyValue s 0 = (1 / 2 : ℂ) := by
  have hr : radialHomotopyRadius s 0 = 0 := by
    unfold radialHomotopyRadius
    rw [lollipopRadius_zero]
    rw [show angle 0 = -Real.pi / 2 by simp [angle]]
    have hc : Real.cos (-Real.pi / 2) = 0 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.cos_neg, Real.cos_pi_div_two]
    rw [hc]
    simp
  simp [radialHomotopyValue, hr]

theorem radialHomotopyValue_one_right (s : unitInterval) :
    radialHomotopyValue s 1 = (1 / 2 : ℂ) := by
  have hangle : angle 1 = -Real.pi / 2 - 2 * Real.pi := by
    unfold angle
    norm_num
  have hr : radialHomotopyRadius s 1 = 0 := by
    unfold radialHomotopyRadius
    rw [lollipopRadius_one, hangle, Real.cos_sub_two_pi]
    have hc : Real.cos (-Real.pi / 2) = 0 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.cos_neg, Real.cos_pi_div_two]
    rw [hc]
    simp
  simp [radialHomotopyValue, hr]

def angleHomotopyAngle (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * angle t + (s : ℝ) * lollipopAngle t

def angleHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + lollipopRadius t *
    Complex.exp ((angleHomotopyAngle s t : ℂ) * Complex.I)

theorem angleHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) :
    angleHomotopyValue s t ≠ a := by
  intro hpuncture
  have hdist : ‖a - (1 / 2 : ℂ)‖ = 1 / 2 := by rcases ha with rfl | rfl <;> norm_num
  have hv : (lollipopRadius t : ℂ) *
      Complex.exp ((angleHomotopyAngle s t : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold angleHomotopyValue at hpuncture
    linear_combination hpuncture
  have hr : lollipopRadius t = 1 / 2 := by
    have hn := congrArg norm hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lollipopRadius_nonneg t),
      Complex.norm_exp_ofReal_mul_I, hdist] at hn
    norm_num at hn
    exact hn
  have him := congrArg Complex.im hv
  have haim : (a - (1 / 2 : ℂ)).im = 0 := by rcases ha with rfl | rfl <;> norm_num
  rw [haim] at him
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im] at him
  have hsin : Real.sin (angleHomotopyAngle s t) = 0 := by
    rw [hr] at him
    norm_num at him
    exact him
  rcases (lollipopRadius_eq_half_iff t).mp hr with ht | ht
  · have htSubtype : t = ⟨(1 / 6 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    have hangle : angleHomotopyAngle s ⟨(1 / 6 : ℝ), by norm_num⟩ =
        -5 * Real.pi / 6 + (s : ℝ) * Real.pi / 3 := by
      unfold angleHomotopyAngle
      rw [lollipopAngle_eq_left _ (by norm_num)]
      unfold angle
      norm_num
      ring
    have hsPiNonneg : 0 ≤ (s : ℝ) * Real.pi :=
      mul_nonneg s.2.1 Real.pi_pos.le
    have hsOnePiNonneg : 0 ≤ (1 - (s : ℝ)) * Real.pi :=
      mul_nonneg (sub_nonneg.mpr s.2.2) Real.pi_pos.le
    have hlower : -Real.pi < angleHomotopyAngle s
        ⟨(1 / 6 : ℝ), by norm_num⟩ := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hupper : angleHomotopyAngle s
        ⟨(1 / 6 : ℝ), by norm_num⟩ < 0 := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hupper hlower).ne hsin
  · have htSubtype : t = ⟨(11 / 12 : ℝ), by norm_num⟩ := by ext; exact ht
    subst t
    have hangle : angleHomotopyAngle s ⟨(11 / 12 : ℝ), by norm_num⟩ +
          2 * Real.pi = -Real.pi / 3 - (s : ℝ) * Real.pi / 6 := by
      unfold angleHomotopyAngle
      rw [lollipopAngle_eq_right _ (by norm_num)]
      unfold angle
      norm_num
      ring
    have hsPiNonneg : 0 ≤ (s : ℝ) * Real.pi :=
      mul_nonneg s.2.1 Real.pi_pos.le
    have hsOnePiNonneg : 0 ≤ (1 - (s : ℝ)) * Real.pi :=
      mul_nonneg (sub_nonneg.mpr s.2.2) Real.pi_pos.le
    have hlower : -Real.pi < angleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hupper : angleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi < 0 := by
      rw [hangle]
      nlinarith [Real.pi_pos]
    have hsin' : Real.sin (angleHomotopyAngle s
        ⟨(11 / 12 : ℝ), by norm_num⟩ + 2 * Real.pi) = 0 := by
      rw [Real.sin_add_two_pi, hsin]
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hupper hlower).ne hsin'

theorem angleHomotopyValue_ne_zero (s t : unitInterval) :
    angleHomotopyValue s t ≠ 0 :=
  angleHomotopyValue_ne_puncture s t 0 (Or.inl rfl)

theorem angleHomotopyValue_ne_one (s t : unitInterval) :
    angleHomotopyValue s t ≠ 1 :=
  angleHomotopyValue_ne_puncture s t 1 (Or.inr rfl)

def angleHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨angleHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨angleHomotopyValue_ne_zero p.1 p.2,
      angleHomotopyValue_ne_one p.1 p.2⟩⟩

theorem continuous_angleHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      angleHomotopyValue p.1 p.2) := by
  have hr : Continuous (fun p : unitInterval × unitInterval =>
      lollipopRadius p.2) :=
    continuous_lollipopRadius.comp continuous_snd
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      lollipopAngle p.2) :=
    continuous_lollipopAngle.comp continuous_snd
  unfold angleHomotopyValue angleHomotopyAngle angle
  fun_prop

def lollipopValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + lollipopRadius t *
    Complex.exp ((lollipopAngle t : ℂ) * Complex.I)

theorem angleHomotopyValue_zero_left (t : unitInterval) :
    angleHomotopyValue 0 t = lollipopLinearAngleValue t := by
  simp [angleHomotopyValue, angleHomotopyAngle,
    lollipopLinearAngleValue]

theorem angleHomotopyValue_one_left (t : unitInterval) :
    angleHomotopyValue 1 t = lollipopValue t := by
  simp [angleHomotopyValue, angleHomotopyAngle, lollipopValue]

theorem angleHomotopyValue_zero_right (s : unitInterval) :
    angleHomotopyValue s 0 = (1 / 2 : ℂ) := by
  simp [angleHomotopyValue, lollipopRadius_zero]

theorem angleHomotopyValue_one_right (s : unitInterval) :
    angleHomotopyValue s 1 = (1 / 2 : ℂ) := by
  simp [angleHomotopyValue, lollipopRadius_one]

abbrev basepoint : ↥(({0, 1} : Set ℂ)ᶜ) :=
  twicePuncturedComplexBasepoint

def peanutPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  radialHomotopyPoint (0, t)

def linearAnglePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  radialHomotopyPoint (1, t)

def lollipopPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  angleHomotopyPoint (1, t)

theorem peanutPoint_zero : peanutPoint 0 = basepoint := by
  apply Subtype.ext
  simpa [peanutPoint, basepoint, radialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      radialHomotopyValue_zero_right 0

theorem peanutPoint_one : peanutPoint 1 = basepoint := by
  apply Subtype.ext
  simpa [peanutPoint, basepoint, radialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      radialHomotopyValue_one_right 0

theorem linearAnglePoint_zero : linearAnglePoint 0 = basepoint := by
  apply Subtype.ext
  simpa [linearAnglePoint, basepoint, radialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      radialHomotopyValue_zero_right 1

theorem linearAnglePoint_one : linearAnglePoint 1 = basepoint := by
  apply Subtype.ext
  simpa [linearAnglePoint, basepoint, radialHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      radialHomotopyValue_one_right 1

theorem lollipopPoint_zero : lollipopPoint 0 = basepoint := by
  apply Subtype.ext
  simpa [lollipopPoint, basepoint, angleHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      angleHomotopyValue_zero_right 1

theorem lollipopPoint_one : lollipopPoint 1 = basepoint := by
  apply Subtype.ext
  simpa [lollipopPoint, basepoint, angleHomotopyPoint,
    twicePuncturedComplexBasepoint] using
      angleHomotopyValue_one_right 1

def peanutLoop : Path basepoint basepoint where
  toFun := peanutPoint
  continuous_toFun := by
    exact (continuous_radialHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := peanutPoint_zero
  target' := peanutPoint_one

def linearAngleLoop : Path basepoint basepoint where
  toFun := linearAnglePoint
  continuous_toFun := by
    exact (continuous_radialHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := linearAnglePoint_zero
  target' := linearAnglePoint_one

def lollipopLoop : Path basepoint basepoint where
  toFun := lollipopPoint
  continuous_toFun := by
    exact (continuous_angleHomotopyValue.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
  source' := lollipopPoint_zero
  target' := lollipopPoint_one

def radialHomotopy : Path.Homotopy peanutLoop linearAngleLoop where
  toFun := radialHomotopyPoint
  continuous_toFun := continuous_radialHomotopyValue.subtype_mk _
  map_zero_left t := rfl
  map_one_left t := rfl
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      have hbase : (basepoint).1 = (1 / 2 : ℂ) := by
        norm_num [basepoint,
          twicePuncturedComplexBasepoint]
      exact (radialHomotopyValue_zero_right s).trans
        (hbase.symm.trans (congrArg Subtype.val peanutLoop.source).symm)
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      have hbase : (basepoint).1 = (1 / 2 : ℂ) := by
        norm_num [basepoint,
          twicePuncturedComplexBasepoint]
      exact (radialHomotopyValue_one_right s).trans
        (hbase.symm.trans (congrArg Subtype.val peanutLoop.target).symm)

def angleHomotopy : Path.Homotopy linearAngleLoop lollipopLoop where
  toFun := angleHomotopyPoint
  continuous_toFun := continuous_angleHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact (angleHomotopyValue_zero_left t).trans
      (radialHomotopyValue_one_left t).symm
  map_one_left t := by
    apply Subtype.ext
    rfl
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      have hbase : (basepoint).1 = (1 / 2 : ℂ) := by
        norm_num [basepoint,
          twicePuncturedComplexBasepoint]
      exact (angleHomotopyValue_zero_right s).trans
        (hbase.symm.trans (congrArg Subtype.val linearAngleLoop.source).symm)
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      have hbase : (basepoint).1 = (1 / 2 : ℂ) := by
        norm_num [basepoint,
          twicePuncturedComplexBasepoint]
      exact (angleHomotopyValue_one_right s).trans
        (hbase.symm.trans (congrArg Subtype.val linearAngleLoop.target).symm)

theorem peanutLoop_eq_finiteComposite :
    peanutLoop =
      twicePuncturedClockwiseZeroMeridian.trans
        twicePuncturedClockwiseOneMeridian := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change radialHomotopyValue 0 t = _
  rw [radialHomotopyValue_zero_left]
  simp only [Path.trans_apply]
  split_ifs with ht
  · exact value_eq_zero_first t ht
  · exact value_eq_one_second t (le_of_not_ge ht)

theorem finiteComposite_class_eq_lollipop :
    Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) =
      Path.Homotopic.Quotient.mk lollipopLoop := by
  rw [← peanutLoop_eq_finiteComposite, Path.Homotopic.Quotient.eq]
  exact ⟨radialHomotopy.trans angleHomotopy⟩

theorem lollipopRadius_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    lollipopRadius t = 3 * (t : ℝ) := by
  unfold lollipopRadius
  rw [min_eq_left]
  apply le_min
  · linarith
  · nlinarith [t.2.1]

theorem lollipopRadius_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    lollipopRadius t = 3 / 2 := by
  unfold lollipopRadius
  have houter : min (3 / 2 : ℝ) (6 * (1 - (t : ℝ))) ≤ 3 * (t : ℝ) :=
    (min_le_left _ _).trans (by nlinarith)
  have hinner : (3 / 2 : ℝ) ≤ 6 * (1 - (t : ℝ)) := by nlinarith
  rw [min_eq_right houter, min_eq_left hinner]

theorem lollipopRadius_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    lollipopRadius t = 6 * (1 - (t : ℝ)) := by
  unfold lollipopRadius
  have hinner : 6 * (1 - (t : ℝ)) ≤ (3 / 2 : ℝ) := by nlinarith
  have houter : 6 * (1 - (t : ℝ)) ≤ 3 * (t : ℝ) := by nlinarith
  rw [min_eq_right hinner, min_eq_right houter]

abbrev lowerCircleBasepoint : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨(1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> intro h
    · have hi := congrArg Complex.im h
      norm_num at hi
    · have hi := congrArg Complex.im h
      norm_num at hi⟩

def lowerWhiskerValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) - ((3 / 2 : ℝ) * (t : ℝ)) * Complex.I

theorem lowerWhiskerValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : lowerWhiskerValue t ≠ a := by
  intro h
  have hi := congrArg Complex.im h
  have haim : a.im = 0 := by rcases ha with rfl | rfl <;> norm_num
  rw [haim] at hi
  simp [lowerWhiskerValue] at hi
  have ht : t = 0 := hi
  subst t
  rcases ha with rfl | rfl <;> norm_num [lowerWhiskerValue] at h

def lowerWhiskerPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨lowerWhiskerValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨lowerWhiskerValue_ne_puncture t 0 (Or.inl rfl),
      lowerWhiskerValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem lowerWhiskerPoint_zero :
    lowerWhiskerPoint 0 = basepoint := by
  apply Subtype.ext
  norm_num [lowerWhiskerPoint, lowerWhiskerValue, basepoint,
    twicePuncturedComplexBasepoint]

theorem lowerWhiskerPoint_one :
    lowerWhiskerPoint 1 = lowerCircleBasepoint := by
  apply Subtype.ext
  norm_num [lowerWhiskerPoint, lowerWhiskerValue]

def lowerWhisker : Path basepoint lowerCircleBasepoint where
  toFun := lowerWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold lowerWhiskerValue
    fun_prop
  source' := lowerWhiskerPoint_zero
  target' := lowerWhiskerPoint_one

def lowerCircleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((-Real.pi / 2 - 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem lowerCircleValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : lowerCircleValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((-Real.pi / 2 - 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold lowerCircleValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def lowerCirclePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨lowerCircleValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨lowerCircleValue_ne_puncture t 0 (Or.inl rfl),
      lowerCircleValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem lowerCirclePoint_zero :
    lowerCirclePoint 0 = lowerCircleBasepoint := by
  apply Subtype.ext
  change lowerCircleValue 0 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold lowerCircleValue
  have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    all_goals push_cast
    all_goals ring
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl,
    show -Real.pi / 2 - 2 * Real.pi * (0 : ℝ) = -Real.pi / 2 by norm_num,
    hexp]
  norm_num
  ring

theorem lowerCirclePoint_one :
    lowerCirclePoint 1 = lowerCircleBasepoint := by
  apply Subtype.ext
  change lowerCircleValue 1 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold lowerCircleValue
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

def lowerCircle : Path lowerCircleBasepoint lowerCircleBasepoint where
  toFun := lowerCirclePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold lowerCircleValue
    fun_prop
  source' := lowerCirclePoint_zero
  target' := lowerCirclePoint_one

theorem lollipopLoop_eq_whiskeredLowerCircle :
    lollipopLoop =
      lowerWhisker.trans (lowerCircle.trans lowerWhisker.symm) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change angleHomotopyValue 1 t = _
  rw [angleHomotopyValue_one_left]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs with hfirst hsecond
  · change lollipopValue t = lowerWhiskerValue
      ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1]⟩
    rw [lollipopValue, lollipopRadius_eq_left t hfirst,
      lollipopAngle_eq_left t hfirst]
    unfold lowerWhiskerValue
    have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      convert Complex.exp_neg_pi_div_two_mul_I using 1
      all_goals push_cast
      all_goals ring
    rw [hexp]
    norm_num
    ring
  · have hleft : 1 / 2 ≤ (t : ℝ) := by nlinarith
    have hright : (t : ℝ) ≤ 3 / 4 := by nlinarith
    change lollipopValue t = lowerCircleValue
      ⟨2 * (2 * (t : ℝ) - 1), by constructor <;> nlinarith⟩
    rw [lollipopValue, lollipopRadius_eq_middle t hleft hright,
      lollipopAngle_eq_middle t hleft hright]
    unfold lowerCircleValue
    norm_num
    congr 1
    ring
  · have hright : 3 / 4 ≤ (t : ℝ) := by nlinarith
    change lollipopValue t = lowerWhiskerValue
      (unitInterval.symm ⟨2 * (2 * (t : ℝ) - 1) - 1, by
        constructor <;> nlinarith [t.2.2]⟩)
    rw [lollipopValue, lollipopRadius_eq_right t hright,
      lollipopAngle_eq_right t hright]
    unfold lowerWhiskerValue
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

def lowerToExteriorArcValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) * Complex.exp
    (((-Real.pi / 2 + Real.pi / 2 * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem lowerToExteriorArcValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : lowerToExteriorArcValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) * Complex.exp
      (((-Real.pi / 2 + Real.pi / 2 * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold lowerToExteriorArcValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def lowerToExteriorArcPoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨lowerToExteriorArcValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨lowerToExteriorArcValue_ne_puncture t 0 (Or.inl rfl),
      lowerToExteriorArcValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem lowerToExteriorArcPoint_zero :
    lowerToExteriorArcPoint 0 = lowerCircleBasepoint := by
  apply Subtype.ext
  change lowerToExteriorArcValue 0 =
    (1 / 2 : ℂ) - (3 / 2 : ℝ) * Complex.I
  unfold lowerToExteriorArcValue
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  have hexp : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    all_goals push_cast
    all_goals ring
  rw [show -Real.pi / 2 + Real.pi / 2 * (0 : ℝ) = -Real.pi / 2 by norm_num,
    hexp]
  norm_num
  ring

theorem lowerToExteriorArcPoint_one :
    lowerToExteriorArcPoint 1 = exteriorBasepoint := by
  apply Subtype.ext
  change lowerToExteriorArcValue 1 = (2 : ℂ)
  unfold lowerToExteriorArcValue
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl,
    show -Real.pi / 2 + Real.pi / 2 * (1 : ℝ) = 0 by ring]
  norm_num

def lowerToExteriorArc :
    Path lowerCircleBasepoint exteriorBasepoint where
  toFun := lowerToExteriorArcPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold lowerToExteriorArcValue
    fun_prop
  source' := lowerToExteriorArcPoint_zero
  target' := lowerToExteriorArcPoint_one

theorem lowerToExteriorArc_coe (t : unitInterval) :
    (lowerToExteriorArc t).1 = lowerToExteriorArcValue t := rfl

def centeredExteriorCircleValue (t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem centeredExteriorCircleValue_ne_puncture (t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : centeredExteriorCircleValue t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold centeredExteriorCircleValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def centeredExteriorCirclePoint (t : unitInterval) : ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨centeredExteriorCircleValue t, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨centeredExteriorCircleValue_ne_puncture t 0 (Or.inl rfl),
      centeredExteriorCircleValue_ne_puncture t 1 (Or.inr rfl)⟩⟩

theorem centeredExteriorCirclePoint_zero :
    centeredExteriorCirclePoint 0 = exteriorBasepoint := by
  apply Subtype.ext
  change centeredExteriorCircleValue 0 = (2 : ℂ)
  unfold centeredExteriorCircleValue
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  norm_num

theorem centeredExteriorCirclePoint_one :
    centeredExteriorCirclePoint 1 = exteriorBasepoint := by
  apply Subtype.ext
  change centeredExteriorCircleValue 1 = (2 : ℂ)
  unfold centeredExteriorCircleValue
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]

def centeredExteriorCircle :
    Path exteriorBasepoint exteriorBasepoint where
  toFun := centeredExteriorCirclePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold centeredExteriorCircleValue
    fun_prop
  source' := centeredExteriorCirclePoint_zero
  target' := centeredExteriorCirclePoint_one

def rebasedCircleAngle (t : unitInterval) : ℝ :=
  -Real.pi / 2 + Real.pi * min (t : ℝ) (1 / 2) -
    8 * Real.pi * max 0 (min ((t : ℝ) - 1 / 2) (1 / 4)) -
      2 * Real.pi * max 0 ((t : ℝ) - 3 / 4)

theorem continuous_rebasedCircleAngle : Continuous rebasedCircleAngle := by
  unfold rebasedCircleAngle
  fun_prop

theorem rebasedCircleAngle_eq_left (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    rebasedCircleAngle t = -Real.pi / 2 + Real.pi * (t : ℝ) := by
  unfold rebasedCircleAngle
  rw [min_eq_left ht,
    min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_left (show (t : ℝ) - 1 / 2 ≤ 0 by linarith),
    max_eq_left (show (t : ℝ) - 3 / 4 ≤ 0 by linarith)]
  ring

theorem rebasedCircleAngle_eq_middle (t : unitInterval)
    (hleft : 1 / 2 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    rebasedCircleAngle t = 4 * Real.pi - 8 * Real.pi * (t : ℝ) := by
  unfold rebasedCircleAngle
  rw [min_eq_right hleft,
    min_eq_left (show (t : ℝ) - 1 / 2 ≤ 1 / 4 by linarith),
    max_eq_right (show 0 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_left (show (t : ℝ) - 3 / 4 ≤ 0 by linarith)]
  ring

theorem rebasedCircleAngle_eq_right (t : unitInterval) (ht : 3 / 4 ≤ (t : ℝ)) :
    rebasedCircleAngle t = -Real.pi / 2 - 2 * Real.pi * (t : ℝ) := by
  unfold rebasedCircleAngle
  rw [min_eq_right (show 1 / 2 ≤ (t : ℝ) by linarith),
    min_eq_right (show 1 / 4 ≤ (t : ℝ) - 1 / 2 by linarith),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4),
    max_eq_right (show 0 ≤ (t : ℝ) - 3 / 4 by linarith)]
  ring

def circleRebaseHomotopyAngle (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * (-Real.pi / 2 - 2 * Real.pi * (t : ℝ)) +
    (s : ℝ) * rebasedCircleAngle t

def circleRebaseHomotopyValue (s t : unitInterval) : ℂ :=
  (1 / 2 : ℂ) + (3 / 2 : ℝ) *
    Complex.exp (((circleRebaseHomotopyAngle s t : ℝ) : ℂ) * Complex.I)

theorem circleRebaseHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : circleRebaseHomotopyValue s t ≠ a := by
  intro h
  have hv : ((3 / 2 : ℝ) : ℂ) *
      Complex.exp (((circleRebaseHomotopyAngle s t : ℝ) : ℂ) * Complex.I) =
      a - (1 / 2 : ℂ) := by
    unfold circleRebaseHomotopyValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl <;> norm_num at hn

def circleRebaseHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨circleRebaseHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨circleRebaseHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      circleRebaseHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_circleRebaseHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      circleRebaseHomotopyValue p.1 p.2) := by
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      rebasedCircleAngle p.2) :=
    continuous_rebasedCircleAngle.comp continuous_snd
  unfold circleRebaseHomotopyValue circleRebaseHomotopyAngle
  fun_prop

def rebasedCenteredCircle : Path lowerCircleBasepoint lowerCircleBasepoint :=
  lowerToExteriorArc.trans
    (centeredExteriorCircle.trans lowerToExteriorArc.symm)

theorem circleRebaseHomotopyValue_zero_left (t : unitInterval) :
    circleRebaseHomotopyValue 0 t = lowerCircleValue t := by
  simp [circleRebaseHomotopyValue, circleRebaseHomotopyAngle,
    lowerCircleValue]

theorem circleRebaseHomotopyValue_one_left (t : unitInterval) :
    circleRebaseHomotopyValue 1 t = (rebasedCenteredCircle t).1 := by
  simp [circleRebaseHomotopyValue, circleRebaseHomotopyAngle,
    rebasedCenteredCircle]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs with hfirst hsecond
  · rw [rebasedCircleAngle_eq_left t hfirst]
    unfold lowerToExteriorArc lowerToExteriorArcPoint
      lowerToExteriorArcValue
    norm_num
    congr 1
    ring
  · have hleft : 1 / 2 ≤ (t : ℝ) := by nlinarith
    have hright : (t : ℝ) ≤ 3 / 4 := by nlinarith
    rw [rebasedCircleAngle_eq_middle t hleft hright]
    unfold centeredExteriorCircle centeredExteriorCirclePoint
      centeredExteriorCircleValue
    norm_num
    congr 1
    ring
  · have hright : 3 / 4 ≤ (t : ℝ) := by nlinarith
    rw [rebasedCircleAngle_eq_right t hright]
    simp only [Function.comp_apply, lowerToExteriorArc_coe]
    unfold lowerToExteriorArcValue
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

theorem circleRebaseHomotopyValue_zero_right (s : unitInterval) :
    circleRebaseHomotopyValue s 0 =
      (lowerCircleBasepoint).1 := by
  have hsource : -Real.pi / 2 - 2 * Real.pi * ((0 : unitInterval) : ℝ) =
      -Real.pi / 2 := by norm_num
  have htarget : rebasedCircleAngle 0 = -Real.pi / 2 := by
    rw [rebasedCircleAngle_eq_left 0 (by norm_num)]
    norm_num
  unfold circleRebaseHomotopyValue circleRebaseHomotopyAngle
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

theorem circleRebaseHomotopyValue_one_right (s : unitInterval) :
    circleRebaseHomotopyValue s 1 =
      (lowerCircleBasepoint).1 := by
  have hsource : -Real.pi / 2 - 2 * Real.pi * ((1 : unitInterval) : ℝ) =
      -5 * Real.pi / 2 := by norm_num; ring
  have htarget : rebasedCircleAngle 1 = -5 * Real.pi / 2 := by
    rw [rebasedCircleAngle_eq_right 1 (by norm_num)]
    norm_num
    ring
  unfold circleRebaseHomotopyValue circleRebaseHomotopyAngle
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

def circleRebaseHomotopy :
    Path.Homotopy lowerCircle rebasedCenteredCircle where
  toFun := circleRebaseHomotopyPoint
  continuous_toFun := continuous_circleRebaseHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact circleRebaseHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact circleRebaseHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (circleRebaseHomotopyValue_zero_right s).trans
        (congrArg Subtype.val lowerCircle.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (circleRebaseHomotopyValue_one_right s).trans
        (congrArg Subtype.val lowerCircle.target).symm

def circleExpansionCenter (s : unitInterval) : ℝ :=
  (1 - (s : ℝ)) / 2

def circleExpansionRadius (s : unitInterval) : ℝ :=
  (3 + (s : ℝ)) / 2

def circleExpansionHomotopyValue (s t : unitInterval) : ℂ :=
  (circleExpansionCenter s : ℂ) + circleExpansionRadius s *
    Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem circleExpansionRadius_pos (s : unitInterval) :
    0 < circleExpansionRadius s := by
  unfold circleExpansionRadius
  nlinarith [s.2.1]

theorem circleExpansionHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : circleExpansionHomotopyValue s t ≠ a := by
  intro h
  have hv : (circleExpansionRadius s : ℂ) *
      Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
      a - circleExpansionCenter s := by
    unfold circleExpansionHomotopyValue at h
    linear_combination h
  have hn := congrArg norm hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (circleExpansionRadius_pos s),
    Complex.norm_exp_ofReal_mul_I] at hn
  rcases ha with rfl | rfl
  · have hcNonneg : 0 ≤ circleExpansionCenter s := by
      unfold circleExpansionCenter
      nlinarith [s.2.2]
    rw [show (0 : ℂ) - circleExpansionCenter s =
        (-(circleExpansionCenter s) : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hcNonneg] at hn
    unfold circleExpansionRadius circleExpansionCenter at hn
    nlinarith [s.2.1]
  · have hcOneNonneg : 0 ≤ 1 - circleExpansionCenter s := by
      unfold circleExpansionCenter
      nlinarith [s.2.1]
    rw [show (1 : ℂ) - circleExpansionCenter s =
        ((1 - circleExpansionCenter s : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcOneNonneg] at hn
    unfold circleExpansionRadius circleExpansionCenter at hn
    nlinarith [s.2.2]

def circleExpansionHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨circleExpansionHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨circleExpansionHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      circleExpansionHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_circleExpansionHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      circleExpansionHomotopyValue p.1 p.2) := by
  unfold circleExpansionHomotopyValue circleExpansionCenter
    circleExpansionRadius
  fun_prop

theorem clockwiseExteriorMeridian_coe (t : unitInterval) :
    (clockwiseExteriorMeridian t).1 =
      2 * Complex.exp (((-2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rfl

theorem circleExpansionHomotopyValue_zero_left (t : unitInterval) :
    circleExpansionHomotopyValue 0 t = centeredExteriorCircleValue t := by
  simp [circleExpansionHomotopyValue, circleExpansionCenter,
    circleExpansionRadius, centeredExteriorCircleValue]

theorem circleExpansionHomotopyValue_one_left (t : unitInterval) :
    circleExpansionHomotopyValue 1 t =
      (clockwiseExteriorMeridian t).1 := by
  rw [clockwiseExteriorMeridian_coe]
  simp [circleExpansionHomotopyValue, circleExpansionCenter,
    circleExpansionRadius]
  norm_num

theorem circleExpansionHomotopyValue_zero_right (s : unitInterval) :
    circleExpansionHomotopyValue s 0 = (exteriorBasepoint).1 := by
  unfold circleExpansionHomotopyValue circleExpansionCenter
    circleExpansionRadius
  rw [show (((0 : unitInterval) : ℝ)) = 0 by rfl]
  norm_num
  ring

theorem circleExpansionHomotopyValue_one_right (s : unitInterval) :
    circleExpansionHomotopyValue s 1 = (exteriorBasepoint).1 := by
  unfold circleExpansionHomotopyValue circleExpansionCenter
    circleExpansionRadius
  rw [show (((1 : unitInterval) : ℝ)) = 1 by rfl]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]
  ring

def circleExpansionHomotopy :
    Path.Homotopy centeredExteriorCircle clockwiseExteriorMeridian where
  toFun := circleExpansionHomotopyPoint
  continuous_toFun := continuous_circleExpansionHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact circleExpansionHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact circleExpansionHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (circleExpansionHomotopyValue_zero_right s).trans
        (congrArg Subtype.val centeredExteriorCircle.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (circleExpansionHomotopyValue_one_right s).trans
        (congrArg Subtype.val centeredExteriorCircle.target).symm

def lowerExteriorBridge :
    Path basepoint exteriorBasepoint :=
  lowerWhisker.trans lowerToExteriorArc

theorem exteriorBridgeArc_coe (t : unitInterval) :
    (exteriorBridgeArc t).1 =
      circleMap 1 (-(2 : ℝ)⁻¹) (Real.pi * (t : ℝ)) := rfl

theorem exteriorBridgeLine_coe (t : unitInterval) :
    (exteriorBridgeLine t).1 =
      (3 / 2 : ℂ) + ((t : ℝ) / 2 : ℝ) := rfl

theorem lowerWhisker_coe (t : unitInterval) :
    (lowerWhisker t).1 = lowerWhiskerValue t := rfl

theorem exteriorBridge_im_nonpos (t : unitInterval) :
    (exteriorBridge t).1.im ≤ 0 := by
  unfold exteriorBridge
  simp only [Path.trans_apply]
  split_ifs with ht
  · rw [exteriorBridgeArc_coe]
    unfold circleMap
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    have hsin : 0 ≤ Real.sin (Real.pi * (2 * (t : ℝ))) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact mul_nonneg Real.pi_pos.le (by nlinarith [t.2.1])
      · nlinarith [Real.pi_pos]
    norm_num
    nlinarith
  · rw [exteriorBridgeLine_coe]
    norm_num

theorem alternativeExteriorBridge_im_neg (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (lowerExteriorBridge t).1.im < 0 := by
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
  unfold lowerExteriorBridge
  simp only [Path.trans_apply]
  split_ifs with ht
  · let u : unitInterval := ⟨2 * (t : ℝ), by
      constructor
      · exact mul_nonneg (by norm_num) t.2.1
      · nlinarith⟩
    change (lowerWhisker u).1.im < 0
    rw [lowerWhisker_coe]
    have himval : (lowerWhiskerValue u).im = -(3 / 2 * (u : ℝ)) := by
      unfold lowerWhiskerValue
      norm_num
    rw [himval]
    change -(3 / 2 * (2 * (t : ℝ))) < 0
    nlinarith
  · rw [lowerToExteriorArc_coe]
    unfold lowerToExteriorArcValue
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

def bridgeHomotopyValue (s t : unitInterval) : ℂ :=
  (1 - (s : ℝ)) * (exteriorBridge t).1 +
    (s : ℝ) * (lowerExteriorBridge t).1

theorem bridgeHomotopyValue_ne_puncture (s t : unitInterval) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : bridgeHomotopyValue s t ≠ a := by
  intro h
  by_cases ht0 : t = 0
  · subst t
    have hpaper := congrArg Subtype.val exteriorBridge.source
    have halt := congrArg Subtype.val lowerExteriorBridge.source
    unfold bridgeHomotopyValue at h
    rw [hpaper, halt] at h
    rcases ha with rfl | rfl
    · have hr := congrArg Complex.re h
      norm_num [basepoint,
        twicePuncturedComplexBasepoint] at hr
      nlinarith
    · have hr := congrArg Complex.re h
      norm_num [basepoint,
        twicePuncturedComplexBasepoint] at hr
      nlinarith
  · by_cases ht1 : t = 1
    · subst t
      have hpaper := congrArg Subtype.val exteriorBridge.target
      have halt := congrArg Subtype.val lowerExteriorBridge.target
      unfold bridgeHomotopyValue at h
      rw [hpaper, halt] at h
      rcases ha with rfl | rfl
      · have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith
      · have hr := congrArg Complex.re h
        norm_num at hr
        nlinarith
    · have hpaperIm := exteriorBridge_im_nonpos t
      have haltIm := alternativeExteriorBridge_im_neg t ht0 ht1
      have haim : a.im = 0 := by rcases ha with rfl | rfl <;> norm_num
      have him := congrArg Complex.im h
      unfold bridgeHomotopyValue at him
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] at him
      rw [haim] at him
      norm_num at him
      have hsZero : (s : ℝ) = 0 := by
        by_contra hs
        have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs)
        have hfirst : (1 - (s : ℝ)) * (exteriorBridge t).1.im ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr s.2.2) hpaperIm
        have hsecond : (s : ℝ) * (lowerExteriorBridge t).1.im < 0 :=
          mul_neg_of_pos_of_neg hspos haltIm
        nlinarith
      have hsSubtype : s = 0 := by ext; exact hsZero
      subst s
      simp [bridgeHomotopyValue] at h
      exact (show (exteriorBridge t).1 ≠ a from by
        rcases (exteriorBridge t).2 with hmem
        rw [Set.mem_compl_iff] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
        rcases ha with rfl | rfl
        · exact hmem.1
        · exact hmem.2) h

def bridgeHomotopyPoint (p : unitInterval × unitInterval) :
    ↥(({0, 1} : Set ℂ)ᶜ) :=
  ⟨bridgeHomotopyValue p.1 p.2, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨bridgeHomotopyValue_ne_puncture p.1 p.2 0 (Or.inl rfl),
      bridgeHomotopyValue_ne_puncture p.1 p.2 1 (Or.inr rfl)⟩⟩

theorem continuous_bridgeHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      bridgeHomotopyValue p.1 p.2) := by
  unfold bridgeHomotopyValue
  have hp : Continuous (fun p : unitInterval × unitInterval =>
      (exteriorBridge p.2).1) :=
    continuous_subtype_val.comp (exteriorBridge.continuous.comp continuous_snd)
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      (lowerExteriorBridge p.2).1) :=
    continuous_subtype_val.comp
      (lowerExteriorBridge.continuous.comp continuous_snd)
  fun_prop

theorem bridgeHomotopyValue_zero_left (t : unitInterval) :
    bridgeHomotopyValue 0 t = (exteriorBridge t).1 := by
  simp [bridgeHomotopyValue]

theorem bridgeHomotopyValue_one_left (t : unitInterval) :
    bridgeHomotopyValue 1 t = (lowerExteriorBridge t).1 := by
  simp [bridgeHomotopyValue]

theorem bridgeHomotopyValue_zero_right (s : unitInterval) :
    bridgeHomotopyValue s 0 = (basepoint).1 := by
  unfold bridgeHomotopyValue
  rw [congrArg Subtype.val exteriorBridge.source,
    congrArg Subtype.val lowerExteriorBridge.source]
  ring

theorem bridgeHomotopyValue_one_right (s : unitInterval) :
    bridgeHomotopyValue s 1 = (exteriorBasepoint).1 := by
  unfold bridgeHomotopyValue
  rw [congrArg Subtype.val exteriorBridge.target,
    congrArg Subtype.val lowerExteriorBridge.target]
  push_cast
  ring

def bridgeHomotopy :
    Path.Homotopy exteriorBridge lowerExteriorBridge where
  toFun := bridgeHomotopyPoint
  continuous_toFun := continuous_bridgeHomotopyValue.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact bridgeHomotopyValue_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact bridgeHomotopyValue_one_left t
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Subtype.ext
      exact (bridgeHomotopyValue_zero_right s).trans
        (congrArg Subtype.val exteriorBridge.source).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Subtype.ext
      exact (bridgeHomotopyValue_one_right s).trans
        (congrArg Subtype.val exteriorBridge.target).symm

theorem alternativeExteriorBridge_symm_class :
    Path.Homotopic.Quotient.mk lowerExteriorBridge.symm =
      Path.Homotopic.Quotient.mk
        (lowerToExteriorArc.symm.trans lowerWhisker.symm) := by
  unfold lowerExteriorBridge
  simp only [Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_trans]
  let p := Path.Homotopic.Quotient.mk lowerWhisker
  let q := Path.Homotopic.Quotient.mk lowerToExteriorArc
  have hrightInverse : Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.trans p q)
      (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm q) (Path.Homotopic.Quotient.symm p)) =
      Path.Homotopic.Quotient.refl basepoint := by
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
      _ = Path.Homotopic.Quotient.refl basepoint :=
        Path.Homotopic.Quotient.trans_symm p
  symm
  calc
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm q)
        (Path.Homotopic.Quotient.symm p) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.refl exteriorBasepoint)
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

def centeredOuterLoopViaLowerBridge :
    Path basepoint basepoint :=
  lowerExteriorBridge.trans
    (centeredExteriorCircle.trans lowerExteriorBridge.symm)

def centeredOuterLoopViaExteriorBridge :
    Path basepoint basepoint :=
  exteriorBridge.trans
    (centeredExteriorCircle.trans exteriorBridge.symm)

def bridgeWhiskeredCenteredHomotopy :
    Path.Homotopy centeredOuterLoopViaExteriorBridge centeredOuterLoopViaLowerBridge :=
  bridgeHomotopy.hcomp
    ((Path.Homotopy.refl centeredExteriorCircle).hcomp
      bridgeHomotopy.symm₂)

def circleExpansionViaExteriorBridge :
    Path.Homotopy centeredOuterLoopViaExteriorBridge
      clockwiseExteriorMeridianAtBasepoint :=
  (Path.Homotopy.refl exteriorBridge).hcomp
    (circleExpansionHomotopy.hcomp
      (Path.Homotopy.refl exteriorBridge.symm))

theorem whiskeredLowerCircle_class_eq_alternativeCentered :
    Path.Homotopic.Quotient.mk
        (lowerWhisker.trans (lowerCircle.trans lowerWhisker.symm)) =
      Path.Homotopic.Quotient.mk centeredOuterLoopViaLowerBridge := by
  have hcircle : Path.Homotopic.Quotient.mk lowerCircle =
      Path.Homotopic.Quotient.mk rebasedCenteredCircle := by
    rw [Path.Homotopic.Quotient.eq]
    exact ⟨circleRebaseHomotopy⟩
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [hcircle]
  unfold centeredOuterLoopViaLowerBridge
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [alternativeExteriorBridge_symm_class]
  unfold rebasedCenteredCircle lowerExteriorBridge
  simp only [Path.Homotopic.Quotient.mk_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem alternativeCentered_class_eq_standardCommonExterior :
    Path.Homotopic.Quotient.mk centeredOuterLoopViaLowerBridge =
      Path.Homotopic.Quotient.mk
        clockwiseExteriorMeridianAtBasepoint := by
  calc
    Path.Homotopic.Quotient.mk centeredOuterLoopViaLowerBridge =
        Path.Homotopic.Quotient.mk centeredOuterLoopViaExteriorBridge := by
      rw [Path.Homotopic.Quotient.eq]
      exact ⟨bridgeWhiskeredCenteredHomotopy.symm⟩
    _ = Path.Homotopic.Quotient.mk
        clockwiseExteriorMeridianAtBasepoint := by
      rw [Path.Homotopic.Quotient.eq]
      exact ⟨circleExpansionViaExteriorBridge⟩

theorem exterior_class_eq_finiteComposite :
    Path.Homotopic.Quotient.mk
        clockwiseExteriorMeridianAtBasepoint =
      Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) := by
  calc
    Path.Homotopic.Quotient.mk
        clockwiseExteriorMeridianAtBasepoint =
        Path.Homotopic.Quotient.mk centeredOuterLoopViaLowerBridge :=
      alternativeCentered_class_eq_standardCommonExterior.symm
    _ = Path.Homotopic.Quotient.mk
        (lowerWhisker.trans (lowerCircle.trans lowerWhisker.symm)) :=
      whiskeredLowerCircle_class_eq_alternativeCentered.symm
    _ = Path.Homotopic.Quotient.mk lollipopLoop := by
      rw [lollipopLoop_eq_whiskeredLowerCircle]
    _ = Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridian.trans
          twicePuncturedClockwiseOneMeridian) :=
      finiteComposite_class_eq_lollipop.symm


end SphereSixComplex.Topology.TwicePuncturedComplex.PairOfPants

end
