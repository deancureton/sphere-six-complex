module

public import SphereSixComplex.Topology.PaperActualCuspCentralLoopRelation
public import SphereSixComplex.Topology.PaperActualCuspCoordinateWinding
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandTrivialization

/-!
# The affine-strip lift pinned by the actual cusp meridian

The actual cusp coordinate crosses the middle of the Section 7 affine strip.  Its explicit
regular-base representative at the selected crossing pins a unique lift of the whole strip through
the regular-coordinate covering.
-/

@[expose] public section

noncomputable section

open Set Metric Topology
open SphereSixComplex.Geometry.GlobalTorusFamily
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

/-- A loop with a logarithmic lift gaining `2πi` has a point on the imaginary axis. -/
public theorem exists_exp_re_eq_zero_of_log_turn
    (γ : C(unitInterval, ℂ))
    (hturn : γ 1 = γ 0 + 2 * Real.pi * Complex.I) :
    ∃ t : unitInterval, (Complex.exp (γ t)).re = 0 := by
  let a : ℝ := (γ 0).im
  let k : ℤ := ⌊(a - Real.pi / 2) / Real.pi⌋ + 1
  let target : ℝ := Real.pi / 2 + (k : ℝ) * Real.pi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hkLower : (a - Real.pi / 2) / Real.pi < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact Int.lt_floor_add_one (R := ℝ) _
  have hkUpper : (k : ℝ) ≤ (a - Real.pi / 2) / Real.pi + 1 := by
    dsimp [k]
    have hfloor := Int.floor_le (α := ℝ) ((a - Real.pi / 2) / Real.pi)
    push_cast
    linarith
  have hmulLower := mul_lt_mul_of_pos_right hkLower hpi
  have hmulUpper := mul_le_mul_of_nonneg_right hkUpper hpi.le
  have htargetLower : a ≤ target := by
    dsimp [target]
    rw [div_mul_cancel₀ _ hpi.ne'] at hmulLower
    linarith
  have htargetUpper : target ≤ a + 2 * Real.pi := by
    dsimp [target]
    rw [add_mul, div_mul_cancel₀ _ hpi.ne'] at hmulUpper
    linarith
  have himOne : (γ 1).im = a + 2 * Real.pi := by
    rw [hturn]
    simp [a]
  have hcont : Continuous (fun t : unitInterval ↦ (γ t).im) :=
    Complex.continuous_im.comp γ.continuous
  have hmem : target ∈ Set.Icc ((γ 0).im) ((γ 1).im) := by
    change a ≤ target ∧ target ≤ (γ 1).im
    rw [himOne]
    exact ⟨htargetLower, htargetUpper⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hcont hmem
  change (γ t).im = target at ht
  refine ⟨t, ?_⟩
  rw [Complex.exp_re, ht]
  have hcos : Real.cos target = 0 := by
    dsimp [target]
    rw [Real.cos_add_int_mul_pi]
    simp
  rw [hcos, mul_zero]

/-- During one positive logarithmic turn the exponential reaches the positive real axis. -/
public theorem exists_exp_re_eq_norm_of_log_turn
    (γ : C(unitInterval, ℂ))
    (hturn : γ 1 = γ 0 + 2 * Real.pi * Complex.I) :
    ∃ t : unitInterval, (Complex.exp (γ t)).re = ‖Complex.exp (γ t)‖ := by
  let a : ℝ := (γ 0).im
  let k : ℤ := ⌊a / (2 * Real.pi)⌋ + 1
  let target : ℝ := (k : ℝ) * (2 * Real.pi)
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hkLower : a / (2 * Real.pi) < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact Int.lt_floor_add_one (R := ℝ) _
  have hkUpper : (k : ℝ) ≤ a / (2 * Real.pi) + 1 := by
    dsimp [k]
    have hfloor := Int.floor_le (α := ℝ) (a / (2 * Real.pi))
    push_cast
    linarith
  have hmulLower := mul_lt_mul_of_pos_right hkLower htwoPi
  have hmulUpper := mul_le_mul_of_nonneg_right hkUpper htwoPi.le
  have htargetLower : a ≤ target := by
    dsimp [target]
    rw [div_mul_cancel₀ _ htwoPi.ne'] at hmulLower
    exact hmulLower.le
  have htargetUpper : target ≤ a + 2 * Real.pi := by
    dsimp [target]
    rw [add_mul, div_mul_cancel₀ _ htwoPi.ne'] at hmulUpper
    linarith
  have himOne : (γ 1).im = a + 2 * Real.pi := by
    rw [hturn]
    simp [a]
  have hcont : Continuous (fun t : unitInterval ↦ (γ t).im) :=
    Complex.continuous_im.comp γ.continuous
  have hmem : target ∈ Set.Icc ((γ 0).im) ((γ 1).im) := by
    change a ≤ target ∧ target ≤ (γ 1).im
    rw [himOne]
    exact ⟨htargetLower, htargetUpper⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hcont hmem
  change (γ t).im = target at ht
  refine ⟨t, ?_⟩
  rw [Complex.exp_re, Complex.norm_exp, ht]
  have hcos : Real.cos target = 1 := by
    dsimp [target]
    exact Real.cos_int_mul_two_pi k
  rw [hcos, mul_one]

variable (A : PaperAnalyticData)

/-- The actual marked cusp meridian reaches the middle height of the affine strip. -/
public theorem exists_actualCuspAngularCoordinateLoop_re_eq_half :
    ∃ t : unitInterval, ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2 := by
  let γ : C(unitInterval, ℂ) :=
    ⟨A.actualCuspAngularZeroRawLog, A.continuous_actualCuspAngularZeroRawLog⟩
  obtain ⟨tzero, hzero⟩ :=
    exists_exp_re_eq_zero_of_log_turn γ A.actualCuspAngularZeroRawLog_one
  obtain ⟨tpositive, hpositive⟩ :=
    exists_exp_re_eq_norm_of_log_turn γ A.actualCuspAngularZeroRawLog_one
  have hgt : 2 < (Complex.exp (γ tpositive)).re := by
    rw [hpositive]
    change 2 < ‖Complex.exp (A.actualCuspAngularZeroRawLog tpositive)‖
    rw [A.actualCuspAngularZeroRawLog_exp]
    exact A.actualCuspAngularCoordinateLoop_norm_gt_two tpositive
  have hcont : Continuous (fun t : unitInterval ↦ (Complex.exp (γ t)).re) :=
    Complex.continuous_re.comp (Complex.continuous_exp.comp γ.continuous)
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc
      ((Complex.exp (γ tzero)).re) ((Complex.exp (γ tpositive)).re) := by
    rw [hzero]
    constructor <;> linarith
  obtain ⟨t, ht⟩ := intermediate_value_univ tzero tpositive hcont hmem
  refine ⟨t, ?_⟩
  rw [← A.actualCuspAngularZeroRawLog_exp]
  exact ht

/-- The selected middle-strip crossing of the actual cusp meridian. -/
public noncomputable def sectionSevenAffineActualCuspCrossingTime : unitInterval :=
  Classical.choose A.exists_actualCuspAngularCoordinateLoop_re_eq_half

public theorem sectionSevenAffineActualCuspCrossingTime_re_eq_half :
    ((A.actualCuspAngularCoordinateLoop A.sectionSevenAffineActualCuspCrossingTime).1).re =
      1 / 2 :=
  Classical.choose_spec A.exists_actualCuspAngularCoordinateLoop_re_eq_half

/-- The selected actual cusp-coordinate crossing, regarded as a point of the affine strip. -/
public noncomputable def sectionSevenAffineActualCuspCrossingPoint :
    sectionSevenAffineVerticalStrip :=
  ⟨(A.actualCuspAngularCoordinateLoop A.sectionSevenAffineActualCuspCrossingTime).1, by
    rw [sectionSevenAffineVerticalStrip]
    change (1 / 3 : ℝ) <
        ((A.actualCuspAngularCoordinateLoop A.sectionSevenAffineActualCuspCrossingTime).1).re ∧
      ((A.actualCuspAngularCoordinateLoop A.sectionSevenAffineActualCuspCrossingTime).1).re < 2 / 3
    rw [A.sectionSevenAffineActualCuspCrossingTime_re_eq_half]
    norm_num⟩

/-- The explicit regular cusp point lies above the selected affine-strip crossing. -/
public theorem regularCoordinate_actualCuspAngularRegularBasePoint_crossing :
    A.regularCoordinate
        (A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime) =
      stripInclusion A.sectionSevenAffineActualCuspCrossingPoint := by
  apply Subtype.ext
  simp only [regularCoordinate, actualCuspAngularRegularBasePoint, stripInclusion,
    sectionSevenAffineActualCuspCrossingPoint, actualCuspAngularLiftPoint]
  exact (A.actualCuspAngularCoordinateLoop_apply _).symm

/-- The unique continuous affine-strip lift through the selected actual cusp point. -/
public noncomputable def sectionSevenAffineActualCuspContinuousLift :
    C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  Classical.choose (A.existsUnique_sectionSevenAffineStripContinuousLift
    A.sectionSevenAffineActualCuspCrossingPoint
    (A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime)
    A.regularCoordinate_actualCuspAngularRegularBasePoint_crossing)

public theorem sectionSevenAffineActualCuspContinuousLift_apply_crossing :
    A.sectionSevenAffineActualCuspContinuousLift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime :=
  (Classical.choose_spec (A.existsUnique_sectionSevenAffineStripContinuousLift
    A.sectionSevenAffineActualCuspCrossingPoint
    (A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime)
    A.regularCoordinate_actualCuspAngularRegularBasePoint_crossing)).1.1

public theorem sectionSevenAffineActualCuspContinuousLift_coordinate :
    A.regularCoordinate ∘ A.sectionSevenAffineActualCuspContinuousLift = stripInclusion :=
  (Classical.choose_spec (A.existsUnique_sectionSevenAffineStripContinuousLift
    A.sectionSevenAffineActualCuspCrossingPoint
    (A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime)
    A.regularCoordinate_actualCuspAngularRegularBasePoint_crossing)).1.2

/-- The affine-strip lift uniquely pinned by the selected actual cusp crossing. -/
public noncomputable def sectionSevenAffineActualCuspStripLift : A.SectionSevenAffineStripLift where
  lift := A.sectionSevenAffineActualCuspContinuousLift
  lift_coordinate z := congrArg Subtype.val
    (congrFun A.sectionSevenAffineActualCuspContinuousLift_coordinate z)

public theorem sectionSevenAffineActualCuspStripLift_apply_crossing :
    A.sectionSevenAffineActualCuspStripLift.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime :=
  A.sectionSevenAffineActualCuspContinuousLift_apply_crossing

end SphereSixComplex.Geometry.PaperAnalyticData
