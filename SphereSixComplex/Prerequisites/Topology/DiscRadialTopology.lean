module

public import SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc
public import Mathlib.Topology.UnitInterval

open Set
open scoped ContinuousMap
namespace SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
noncomputable section

/-- Linear contraction of the complex unit disc to its centre. -/
@[expose] public def discRadialHomotopy
    (p : unitInterval × ComplexUnitDisc) : ComplexUnitDisc :=
  ⟨((1 - (p.1 : ℝ) : ℝ) : ℂ) * p.2.1, by
    have hs0 : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
    have hs1 : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    have hnorm : ‖((1 - (p.1 : ℝ) : ℝ) : ℂ)‖ = 1 - (p.1 : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hs0]
    calc
      ‖(((1 - (p.1 : ℝ) : ℝ) : ℂ) * p.2.1)‖ =
          (1 - (p.1 : ℝ)) * ‖p.2.1‖ := by rw [norm_mul, hnorm]
      _ ≤ 1 * ‖p.2.1‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < 1 := by simpa using p.2.2⟩

public theorem discRadialHomotopy_continuous : Continuous discRadialHomotopy := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub
    (continuous_subtype_val.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd))

@[simp]
public theorem discRadialHomotopy_zero (w : ComplexUnitDisc) :
    discRadialHomotopy (0, w) = w := by
  apply Subtype.ext
  simp [discRadialHomotopy]

@[simp]
public theorem discRadialHomotopy_one (w : ComplexUnitDisc) :
    discRadialHomotopy (1, w) = ComplexUnitDisc.center := by
  apply Subtype.ext
  simp [discRadialHomotopy, ComplexUnitDisc.center]

@[simp]
public theorem discRadialHomotopy_center (s : unitInterval) :
    discRadialHomotopy (s, ComplexUnitDisc.center) = ComplexUnitDisc.center := by
  apply Subtype.ext
  simp [discRadialHomotopy, ComplexUnitDisc.center]

public theorem discRadialHomotopy_discScalarEquiv_pow
    (lambda : ℂ) (hlambda : ‖lambda‖ = 1) (k : ℕ)
    (s : unitInterval) (w : ComplexUnitDisc) :
    discRadialHomotopy (s, (ComplexUnitDisc.rotation lambda hlambda ^ k) w) =
      (ComplexUnitDisc.rotation lambda hlambda ^ k) (discRadialHomotopy (s, w)) := by
  apply Subtype.ext
  change (((1 - (s : ℝ) : ℝ) : ℂ) *
      ((ComplexUnitDisc.rotation lambda hlambda ^ k) w).1) =
    ((ComplexUnitDisc.rotation lambda hlambda ^ k) (discRadialHomotopy (s, w))).1
  rw [ComplexUnitDisc.coe_rotation_pow_apply, ComplexUnitDisc.coe_rotation_pow_apply]
  change (((1 - (s : ℝ) : ℝ) : ℂ) * (lambda ^ k * w.1)) =
    lambda ^ k * (((1 - (s : ℝ) : ℝ) : ℂ) * w.1)
  ring

/-- Radius-`r` ball in a fixed disc--torus product. -/
public abbrev RadialProductBall (r : ℝ) (T : Type) [TopologicalSpace T] :=
  {p : ComplexUnitDisc × T // ‖(p.1 : ℂ)‖ < r}

/-- Positive radial rescaling identifies a radius-`r` product ball with the full unit-disc
product. -/
@[expose] public def radialProductBallHomeomorph
    {T : Type} [TopologicalSpace T] {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    RadialProductBall r T ≃ₜ ComplexUnitDisc × T where
  toFun p :=
    (⟨p.1.1.1 / (r : ℂ), by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact (div_lt_one hr).mpr p.2⟩, p.1.2)
  invFun p :=
    ⟨(⟨(r : ℂ) * p.1.1, by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      have h := mul_lt_mul_of_pos_left p.1.2 hr
      have h' : r * ‖p.1.1‖ < r := by simpa using h
      exact h'.trans hr1⟩, p.2), by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      simpa using mul_lt_mul_of_pos_left p.1.2 hr⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    · rfl
  continuous_toFun :=
    (Continuous.subtype_mk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).div_const _)
      _).prodMk (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := Continuous.subtype_mk
    ((Continuous.subtype_mk
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst)) _).prodMk
        continuous_snd) _

end
end SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
