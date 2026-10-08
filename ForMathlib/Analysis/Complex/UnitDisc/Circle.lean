module

public import ForMathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
open scoped ContinuousMap

namespace ComplexUnitDisc

public def circle (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    C(AddCircle (1 : ℝ), ComplexUnitDisc) where
  toFun z := ⟨(r : ℂ) * (AddCircle.toCircle z : ℂ), by
    simpa [norm_mul, Circle.norm_coe, abs_of_nonneg hr] using hr1⟩
  continuous_toFun := (continuous_const.mul
    (continuous_subtype_val.comp AddCircle.continuous_toCircle)).subtype_mk _

public theorem circle_coe (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    (circle r hr hr1 (t : AddCircle (1 : ℝ)) : ℂ) =
      (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  change (r : ℂ) * (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  push_cast
  ring

public def circleLog (r t : ℝ) : ℂ :=
  (Real.log r : ℂ) + 2 * Real.pi * Complex.I * (t : ℂ)


public theorem exp_circleLog (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (t : ℝ) :
    Complex.exp (circleLog r t) = (circle r hr.le hr1 (t : AddCircle (1 : ℝ)) : ℂ) := by
  rw [circle_coe, circleLog, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]


def circlePath (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Path (circle r hr hr1 0) (circle r hr hr1 0) where
  toFun t := circle r hr hr1 ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (circle r hr hr1).continuous.comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
  source' := by simp
  target' := by simp [AddCircle.coe_period]

theorem circlePath_ne_zero (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    (circlePath r hr.le hr1 t : ℂ) ≠ 0 := by
  change (circle r hr.le hr1 ((t : ℝ) : AddCircle (1 : ℝ)) : ℂ) ≠ 0
  rw [circle_coe]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)

def circleLogScalar (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t ↦ (Real.log r : ℂ) / (2 * Real.pi * Complex.I) + (t : ℂ), by fun_prop⟩

theorem circleLogScalar_one (r : ℝ) :
    circleLogScalar r 1 = circleLogScalar r 0 + 1 := by
  simp [circleLogScalar]

theorem exp_circleLogScalar (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    Complex.exp ((2 * Real.pi * Complex.I) * circleLogScalar r t) =
      (circle r hr.le hr1 ((t : ℝ) : AddCircle (1 : ℝ)) : ℂ) := by
  have hk : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have he : (2 * Real.pi * Complex.I) * circleLogScalar r t = circleLog r t := by
    simp only [circleLogScalar, ContinuousMap.coe_mk, circleLog]
    field_simp
  rw [he]
  exact exp_circleLog r hr hr1 t

end ComplexUnitDisc
