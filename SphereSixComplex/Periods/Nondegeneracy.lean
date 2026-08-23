module

public import SphereSixComplex.Periods.Matrix
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import all SphereSixComplex.Periods.Matrix

/-!
# Nondegeneracy of the period lattice

The two inequalities in the Setup imply that the four columns of the period matrix are
real-linearly independent.
-/

open Matrix

namespace SphereSixComplex.Periods

public structure SetupInequalities (x : Parameters) : Prop where
  tau_im_pos : 0 < x.tau.im
  schur_im_neg : x.beta.im - 6 * x.mu.im ^ 2 / x.tau.im < 0

@[expose] public noncomputable def periodRealLinear (x : Parameters) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun a := ![
    a 0 • (6 * x.mu) + a 1 • x.tau + a 2 • (1 : ℂ),
    a 0 • x.beta + a 1 • x.mu + a 3 • (1 : ℂ)]
  map_add' a b := by
    funext i
    fin_cases i <;> simp [add_smul] <;> abel
  map_smul' r a := by
    funext i
    fin_cases i <;> simp [smul_add, mul_smul]

@[simp]
public theorem periodRealLinear_apply_zero (x : Parameters) (a : Fin 4 → ℝ) :
    periodRealLinear x a 0 =
      a 0 • (6 * x.mu) + a 1 • x.tau + a 2 • (1 : ℂ) := rfl

@[simp]
public theorem periodRealLinear_apply_one (x : Parameters) (a : Fin 4 → ℝ) :
    periodRealLinear x a 1 =
      a 0 • x.beta + a 1 • x.mu + a 3 • (1 : ℂ) := rfl

public theorem periodRealLinear_eq_mulVec (x : Parameters) (a : Fin 4 → ℝ) :
    periodRealLinear x a = periodMatrix x *ᵥ (fun j ↦ (a j : ℂ)) := by
  funext i
  fin_cases i <;>
    simp [periodRealLinear, SphereSixComplex.Periods.periodMatrix.eq_def, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;>
    ring

public theorem periodRealLinear_injective (x : Parameters) (h : SetupInequalities x) :
    Function.Injective (periodRealLinear x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hfirst := congrFun ha (0 : Fin 2)
  have hsecond := congrFun ha (1 : Fin 2)
  change a 0 • (6 * x.mu) + a 1 • x.tau + a 2 • (1 : ℂ) = 0 at hfirst
  change a 0 • x.beta + a 1 • x.mu + a 3 • (1 : ℂ) = 0 at hsecond
  have himFirst := congrArg Complex.im hfirst
  have himSecond := congrArg Complex.im hsecond
  norm_num [Complex.add_im, Complex.smul_im, Complex.mul_im] at himFirst himSecond
  have htau : x.tau.im ≠ 0 := ne_of_gt h.tau_im_pos
  have ha0 : a 0 = 0 := by
    have hfactor : a 0 * (x.beta.im - 6 * x.mu.im ^ 2 / x.tau.im) = 0 := by
      field_simp [htau]
      linear_combination x.tau.im * himSecond - x.mu.im * himFirst
    exact (mul_eq_zero.mp hfactor).resolve_right (ne_of_lt h.schur_im_neg)
  have ha1 : a 1 = 0 := by
    rw [ha0, zero_mul, zero_add] at himFirst
    exact (mul_eq_zero.mp himFirst).resolve_right htau
  have ha2 : a 2 = 0 := by
    rw [ha0, ha1] at hfirst
    simpa using hfirst
  have ha3 : a 3 = 0 := by
    rw [ha0, ha1] at hsecond
    simpa using hsecond
  funext i
  fin_cases i <;> simp [ha0, ha1, ha2, ha3]

public theorem periodRealLinear_finrank_eq :
    Module.finrank ℝ (Fin 4 → ℝ) = Module.finrank ℝ (Fin 2 → ℂ) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

public theorem periodRealLinear_surjective (x : Parameters) (h : SetupInequalities x) :
    Function.Surjective (periodRealLinear x) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank periodRealLinear_finrank_eq).mp
    (periodRealLinear_injective x h)

@[expose] public noncomputable def periodRealLinearEquiv (x : Parameters) (h : SetupInequalities x) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℂ) :=
  (periodRealLinear x).linearEquivOfInjective (periodRealLinear_injective x h)
    periodRealLinear_finrank_eq

@[simp]
public theorem periodRealLinearEquiv_apply (x : Parameters) (h : SetupInequalities x)
    (a : Fin 4 → ℝ) :
    periodRealLinearEquiv x h a = periodRealLinear x a := rfl

end SphereSixComplex.Periods
