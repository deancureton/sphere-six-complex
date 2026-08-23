module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic
public import Mathlib.Tactic.NormDet

/-!
# Lattice and monodromy data

The explicit rank-four integral matrices from Section 2 of the source paper.
-/

open Matrix

namespace SphereSixComplex.LatticeData

public abbrev Lattice := Fin 4 → ℤ

public def T₁ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, -6, 2;
     0, -1, 1, 1;
     0, -1, 0, 1;
     0, 0, 0, 1]

public def T₂ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 6, 0, -3;
     0, 0, -1, 1;
     0, 1, 0, 0;
     0, 0, 0, 1]

public def T₀ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 1;
     0, 1, -1, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

public def N : Matrix (Fin 4) (Fin 4) ℤ := T₀ - 1

public theorem T₁_det : T₁.det = 1 := by
  rw [T₁]
  eval_det

public theorem T₂_det : T₂.det = 1 := by
  rw [T₂]
  eval_det

public theorem T₁_pow_three : T₁ ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₁, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem T₂_pow_four : T₂ ^ 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₂, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem T₁_ne_one : T₁ ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 2
  change (-6 : ℤ) = 0 at this
  omega

public theorem T₂_sq_ne_one : T₂ ^ 2 ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 1
  change (6 : ℤ) = 0 at this
  omega

public theorem T₁_mul_T₂_mul_T₀ : T₁ * T₂ * T₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₁, T₂, T₀, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem T₁_mul_T₂ : T₁ * T₂ = 1 - N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₁, T₂, T₀, N, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem T₀_eq_one_add_N : T₀ = 1 + N := by
  simp [N]

public theorem N_eq : N = !![0, 0, 0, 1; 0, 0, -1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [N, T₀, Matrix.one_apply]

public theorem N_sq : N ^ 2 = 0 := by
  rw [N_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public def A₁ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     6, 0, 1, 0;
     -6, -1, -1, 0;
     -2, 1, 0, 1]

public def A₂ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 0, -1, 0;
     -6, 1, 0, 0;
     3, 0, 1, 1]

public def M₀ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 1, 1, 0;
     -1, 0, 0, 1]

public theorem A₁_eq_transpose_T₁_sq : A₁ = (T₁ ^ 2)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A₁, T₁, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem A₂_eq_transpose_T₂_cube : A₂ = (T₂ ^ 3)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A₂, T₂, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem M₀_eq_one_sub_transpose_N : M₀ = 1 - Nᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [M₀, N, T₀]

public theorem A₁_mul_A₂_mul_M₀ : A₁ * A₂ * M₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A₁, A₂, M₀, Matrix.mul_apply, Fin.sum_univ_succ]

public def gamma : Lattice →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem gamma_A₁ (x : Lattice) : gamma (A₁ *ᵥ x) = gamma x := by
  simp [gamma, A₁, dotProduct, Fin.sum_univ_succ]

public theorem gamma_A₂ (x : Lattice) : gamma (A₂ *ᵥ x) = gamma x := by
  simp [gamma, A₂, dotProduct, Fin.sum_univ_succ]

public theorem gamma_M₀ (x : Lattice) : gamma (M₀ *ᵥ x) = gamma x := by
  simp [gamma, M₀, dotProduct, Fin.sum_univ_succ]

public def epsilon : Lattice := ![1, 2, -4, 0]

public def epsilon' : Lattice := ![1, 3, -3, 0]

public def deltaHat : Lattice := ![0, 0, 0, 1]

public theorem A₁_epsilon : A₁ *ᵥ epsilon = epsilon := by
  funext i
  fin_cases i <;> norm_num [A₁, epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem A₂_epsilon' : A₂ *ᵥ epsilon' = epsilon' := by
  funext i
  fin_cases i <;> norm_num [A₂, epsilon', Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem A₁_deltaHat : A₁ *ᵥ deltaHat = deltaHat := by
  funext i
  fin_cases i <;> norm_num [A₁, deltaHat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem A₂_deltaHat : A₂ *ᵥ deltaHat = deltaHat := by
  funext i
  fin_cases i <;> norm_num [A₂, deltaHat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem gamma_epsilon : gamma epsilon = 1 := by
  rfl

public theorem gamma_neg_epsilon' : gamma (-epsilon') = -1 := by
  rfl

end SphereSixComplex.LatticeData
