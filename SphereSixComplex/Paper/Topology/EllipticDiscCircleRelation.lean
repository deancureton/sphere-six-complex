module

public import SphereSixComplex.Paper.Topology.EllipticDiscCircleSplitting
public import SphereSixComplex.Prerequisites.Geometry.ComplexDiscCircle

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.EllipticDiscCircle
open ComplexUnitDisc

public def smallDiscCircle {R : ℝ} (hR : 0 < R) (r : ℝ) (hr : 0 < r) (hrR : r < R) :=
  circlePath (r / R) (div_pos hr hR).le ((div_lt_one hR).mpr hrR)

public theorem smallDiscCircle_ne_zero {R : ℝ} (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : unitInterval) :
    (smallDiscCircle hR r hr hrR t : ℂ) ≠ 0 :=
  circlePath_ne_zero (r / R) (div_pos hr hR) ((div_lt_one hR).mpr hrR) t

public theorem smallDiscCircle_scaled {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : unitInterval) :
    (discBallScale hR hR1 (smallDiscCircle hR r hr hrR t)).val.val =
      (circle r hr.le (hrR.trans hR1) ((t : ℝ) : AddCircle (1 : ℝ)) : ℂ) := by
  change (R : ℂ) *
    (circle (r / R) (div_pos hr hR).le ((div_lt_one hR).mpr hrR)
      ((t : ℝ) : AddCircle (1 : ℝ)) : ℂ) = _
  rw [circle_coe, circle_coe]
  push_cast
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  field_simp

public theorem smallDiscCircle_log {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : unitInterval) :
    Complex.exp ((2 * Real.pi * Complex.I) * circleLogScalar r t) =
      (discBallScale hR hR1 (smallDiscCircle hR r hr hrR t)).val.val := by
  rw [smallDiscCircle_scaled]
  exact exp_circleLogScalar r hr (hrR.trans hR1) t

end SphereSixComplex.Geometry.EllipticDiscCircle
