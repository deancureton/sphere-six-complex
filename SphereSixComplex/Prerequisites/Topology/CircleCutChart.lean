module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
open Set Complex
namespace SphereSixComplex

public theorem circle_arg_lt_pi_of_ne_neg_one (c : Circle) (hc : c ≠ -1) :
    Complex.arg (c : ℂ) < Real.pi := by
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro h
  apply hc
  apply Circle.injective_arg
  simpa using h

public theorem circle_neg_mem_slitPlane (c : Circle) (hc : c ≠ 1) :
    ((-c : Circle) : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨(circle_arg_lt_pi_of_ne_neg_one (-c) ?_).ne, (-c).coe_ne_zero⟩
  intro h
  exact hc (neg_injective h)

public def circleCutParameter (y : ℝ) : Circle := -Circle.exp (Real.pi * y)

public theorem circleCutParameter_ne_one {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    circleCutParameter y ≠ 1 := by
  intro h
  have he : Circle.exp (Real.pi * y) = -1 := by
    have := congrArg Neg.neg h
    simpa [circleCutParameter] using this
  have ha := congrArg (fun c : Circle ↦ Complex.arg (c : ℂ)) he
  have hlo : -Real.pi < Real.pi * y := by nlinarith [Real.pi_pos, hy.1]
  have hhi : Real.pi * y < Real.pi := by nlinarith [Real.pi_pos, hy.2]
  rw [Circle.arg_exp hlo hhi.le] at ha
  have : Real.pi * y = Real.pi := by simpa using ha
  linarith

public def circleCutArgument (c : Circle) : ℝ := Complex.arg ((-c : Circle) : ℂ) / Real.pi

public theorem circleCutArgument_mem_Ioo (c : Circle) (hc : c ≠ 1) :
    circleCutArgument c ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · rw [circleCutArgument, lt_div_iff₀ Real.pi_pos]
    simpa using Complex.neg_pi_lt_arg ((-c : Circle) : ℂ)
  · rw [circleCutArgument, div_lt_iff₀ Real.pi_pos, one_mul]
    apply circle_arg_lt_pi_of_ne_neg_one
    intro h
    exact hc (neg_injective h)

public theorem circleCutArgument_parameter {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    circleCutArgument (circleCutParameter y) = y := by
  have hlo : -Real.pi < Real.pi * y := by nlinarith [Real.pi_pos, hy.1]
  have hhi : Real.pi * y ≤ Real.pi := by nlinarith [Real.pi_pos, hy.2]
  simp only [circleCutArgument, circleCutParameter, neg_neg]
  rw [Circle.arg_exp hlo hhi]
  exact mul_div_cancel_left₀ y Real.pi_ne_zero

public theorem circleCutParameter_argument (c : Circle) :
    circleCutParameter (circleCutArgument c) = c := by
  unfold circleCutParameter circleCutArgument
  rw [mul_div_cancel₀ _ Real.pi_ne_zero, Circle.exp_arg, neg_neg]

public def circleCutHomeomorph : Ioo (-1 : ℝ) 1 ≃ₜ {c : Circle // c ≠ 1} where
  toFun y := ⟨circleCutParameter y.1, circleCutParameter_ne_one y.2⟩
  invFun c := ⟨circleCutArgument c.1, circleCutArgument_mem_Ioo c.1 c.2⟩
  left_inv y := Subtype.ext (circleCutArgument_parameter y.2)
  right_inv c := Subtype.ext (circleCutParameter_argument c.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val) |>.neg
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div_const
    apply continuous_iff_continuousAt.mpr
    intro c
    have hc : Continuous (fun x : {c : Circle // c ≠ 1} ↦ ((-x.1 : Circle) : ℂ)) :=
      by fun_prop
    exact (Complex.continuousAt_arg (circle_neg_mem_slitPlane c.1 c.2)).comp
      (f := fun x : {c : Circle // c ≠ 1} ↦ ((-x.1 : Circle) : ℂ)) (x := c) hc.continuousAt

public theorem circleCutParameter_injOn :
    Set.InjOn circleCutParameter (Ioo (-1 : ℝ) 1) := by
  intro x hx y hy h
  have he := congrArg circleCutArgument h
  simpa only [circleCutArgument_parameter hx, circleCutArgument_parameter hy] using he

public theorem circleCutParameter_surjOn :
    Set.SurjOn circleCutParameter (Ioo (-1 : ℝ) 1) {c : Circle | c ≠ 1} := by
  intro c hc
  exact ⟨circleCutArgument c, circleCutArgument_mem_Ioo c hc, circleCutParameter_argument c⟩

public theorem circleCutParameter_continuous : Continuous circleCutParameter :=
  (Circle.exp.continuous.comp (continuous_const.mul continuous_id)).neg

public theorem circleCutParameter_eq_turn (t : ℝ) :
    circleCutParameter (2 * t - 1) = Circle.exp (2 * Real.pi * t) := by
  have hp : Circle.exp Real.pi = -1 := by
    apply Subtype.ext
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]
  rw [show 2 * Real.pi * t = Real.pi + Real.pi * (2 * t - 1) by ring,
    Circle.exp_add, hp]
  simp [circleCutParameter]

end SphereSixComplex
