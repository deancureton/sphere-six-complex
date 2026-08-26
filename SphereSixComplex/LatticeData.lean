module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
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

@[expose] public def gamma : Lattice →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem gamma_apply (x : Lattice) : gamma x = x 0 := rfl

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

@[expose] public def gammaVec : Lattice := ![1, 0, 0, 0]

@[expose] public def uVec : Lattice := ![0, 1, 0, 0]

@[expose] public def wVec : Lattice := ![0, 0, 1, 0]

public def deltaVec : Lattice := ![0, 0, 0, 1]

@[simp]
public theorem gammaVec_zero : gammaVec 0 = 1 := rfl

@[simp]
public theorem gammaVec_one : gammaVec 1 = 0 := rfl

@[simp]
public theorem uVec_zero : uVec 0 = 0 := rfl

@[simp]
public theorem uVec_one : uVec 1 = 1 := rfl

@[simp]
public theorem wVec_zero : wVec 0 = 0 := rfl

@[simp]
public theorem wVec_one : wVec 1 = 0 := rfl

/-- The first elliptic monodromy carries the toric `w` direction to `u-w`. -/
public theorem A₁_mulVec_wVec : A₁ *ᵥ wVec = uVec - wVec := by
  funext i
  fin_cases i <;>
    norm_num [A₁, uVec, wVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem N_mulVec (x : Lattice) : N *ᵥ x = ![x 3, -x 2, 0, 0] := by
  funext i
  fin_cases i <;> simp [N_eq, dotProduct, Fin.sum_univ_succ]

public theorem N_mul_gammaVec : N *ᵥ gammaVec = 0 := by
  simp [N_mulVec, gammaVec]

public theorem N_mul_uVec : N *ᵥ uVec = 0 := by
  simp [N_mulVec, uVec]

public theorem N_mul_wVec : N *ᵥ wVec = -uVec := by
  funext i
  fin_cases i <;> simp [N_mulVec, wVec, uVec]

public theorem N_mul_deltaVec : N *ᵥ deltaVec = gammaVec := by
  funext i
  fin_cases i <;> simp [N_mulVec, deltaVec, gammaVec]

public theorem N_mulVec_eq_zero_iff (x : Lattice) :
    N *ᵥ x = 0 ↔ x 2 = 0 ∧ x 3 = 0 := by
  rw [N_mulVec]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    simp at h0 h1
    omega
  · rintro ⟨h2, h3⟩
    funext i
    fin_cases i <;> simp [h2, h3]

public theorem range_N_mulVec :
    Set.range (fun x : Lattice => N *ᵥ x) = {x | x 2 = 0 ∧ x 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [N_mulVec]
  · rintro ⟨h2, h3⟩
    refine ⟨![0, 0, -x 1, x 0], ?_⟩
    change N *ᵥ ![0, 0, -x 1, x 0] = x
    rw [N_mulVec]
    funext i
    fin_cases i <;> simp [h2, h3]

public theorem T₁_fixed_iff (x : Lattice) :
    T₁ *ᵥ x = x ↔ x 1 = 2 * x 2 ∧ x 3 = 3 * x 2 := by
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    simp [T₁, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    omega
  · rintro ⟨h1, h3⟩
    funext i
    fin_cases i <;> simp [T₁, dotProduct, Fin.sum_univ_succ] <;> omega

public theorem T₂_fixed_iff (x : Lattice) :
    T₂ *ᵥ x = x ↔ x 2 = x 1 ∧ x 3 = 2 * x 1 := by
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    simp [T₂, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    omega
  · rintro ⟨h2, h3⟩
    funext i
    fin_cases i <;> simp [T₂, dotProduct, Fin.sum_univ_succ] <;> omega

public theorem common_T_fixed_iff (x : Lattice) :
    (T₁ *ᵥ x = x ∧ T₂ *ᵥ x = x) ↔ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := by
  rw [T₁_fixed_iff, T₂_fixed_iff]
  omega

public theorem A₁_fixed_iff (x : Lattice) :
    A₁ *ᵥ x = x ↔ x 1 = 2 * x 0 ∧ x 2 = -4 * x 0 := by
  constructor
  · intro h
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    simp [A₁, dotProduct, Fin.sum_univ_succ] at h1 h2
    omega
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [A₁, dotProduct, Fin.sum_univ_succ] <;> omega

public theorem A₂_fixed_iff (x : Lattice) :
    A₂ *ᵥ x = x ↔ x 1 = 3 * x 0 ∧ x 2 = -3 * x 0 := by
  constructor
  · intro h
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    simp [A₂, dotProduct, Fin.sum_univ_succ] at h1 h2
    omega
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [A₂, dotProduct, Fin.sum_univ_succ] <;> omega

public theorem common_A_fixed_iff (x : Lattice) :
    (A₁ *ᵥ x = x ∧ A₂ *ᵥ x = x) ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  rw [A₁_fixed_iff, A₂_fixed_iff]
  omega

public theorem M₀_sub_mulVec (x : Lattice) : M₀ *ᵥ x - x = ![0, 0, x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [M₀, dotProduct, Fin.sum_univ_succ]

public theorem M₀_sub_mulVec_eq_zero_iff (x : Lattice) :
    M₀ *ᵥ x - x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [M₀_sub_mulVec]
  constructor
  · intro h
    have h2 := congrFun h (2 : Fin 4)
    have h3 := congrFun h (3 : Fin 4)
    simp at h2 h3
    omega
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]

public theorem range_M₀_sub_mulVec :
    Set.range (fun x : Lattice => M₀ *ᵥ x - x) = {x | x 0 = 0 ∧ x 1 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [M₀_sub_mulVec]
  · rintro ⟨h0, h1⟩
    refine ⟨![-x 3, x 2, 0, 0], ?_⟩
    change M₀ *ᵥ ![-x 3, x 2, 0, 0] - ![-x 3, x 2, 0, 0] = x
    rw [M₀_sub_mulVec]
    funext i
    fin_cases i <;> simp [h0, h1]

public def B₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

public def B₀Inv : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

public theorem B₀_det : B₀.det = 1 := by
  rw [B₀]
  eval_det

public theorem B₀_mul_inv : B₀ * B₀Inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B₀, B₀Inv, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem B₀_inv_mul : B₀Inv * B₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B₀, B₀Inv, Matrix.mul_apply, Fin.sum_univ_succ]

public def B₀Equiv : (Fin 2 → ℤ) ≃ₗ[ℤ] Fin 2 → ℤ :=
  Matrix.toLinearEquivRight'OfInv B₀_mul_inv B₀_inv_mul

public def Q₀Matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 6, 0;
     0, -6, 0, 0;
     -1, 0, 0, 0]

public theorem Q₀Matrix_alternating : Q₀Matrixᵀ = -Q₀Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q₀Matrix]

public theorem Q₀Matrix_T₁_invariant : T₁ᵀ * Q₀Matrix * T₁ = Q₀Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₁, Q₀Matrix, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem Q₀Matrix_T₂_invariant : T₂ᵀ * Q₀Matrix * T₂ = Q₀Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T₂, Q₀Matrix, Matrix.mul_apply, Fin.sum_univ_succ]

public def Q₀ (x y : Lattice) : ℤ := dotProduct x (Q₀Matrix *ᵥ y)

public theorem Q₀_apply (x y : Lattice) :
    Q₀ x y = x 0 * y 3 + 6 * x 1 * y 2 - 6 * x 2 * y 1 - x 3 * y 0 := by
  simp [Q₀, Q₀Matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

public theorem Q₀_self (x : Lattice) : Q₀ x x = 0 := by
  rw [Q₀_apply]
  ring

public theorem invariant_alternating_matrix_classification
    (Q : Matrix (Fin 4) (Fin 4) ℤ) (ha : Qᵀ = -Q)
    (h1 : T₁ᵀ * Q * T₁ = Q) (h2 : T₂ᵀ * Q * T₂ = Q) :
    ∃ c : ℤ, Q = c • Q₀Matrix := by
  have a00 := congrFun (congrFun ha (0 : Fin 4)) (0 : Fin 4)
  have a01 := congrFun (congrFun ha (0 : Fin 4)) (1 : Fin 4)
  have a02 := congrFun (congrFun ha (0 : Fin 4)) (2 : Fin 4)
  have a03 := congrFun (congrFun ha (0 : Fin 4)) (3 : Fin 4)
  have a11 := congrFun (congrFun ha (1 : Fin 4)) (1 : Fin 4)
  have a12 := congrFun (congrFun ha (1 : Fin 4)) (2 : Fin 4)
  have a13 := congrFun (congrFun ha (1 : Fin 4)) (3 : Fin 4)
  have a22 := congrFun (congrFun ha (2 : Fin 4)) (2 : Fin 4)
  have a23 := congrFun (congrFun ha (2 : Fin 4)) (3 : Fin 4)
  have a33 := congrFun (congrFun ha (3 : Fin 4)) (3 : Fin 4)
  simp at a00 a01 a02 a03 a11 a12 a13 a22 a23 a33
  have e101 := congrFun (congrFun h1 (0 : Fin 4)) (1 : Fin 4)
  have e102 := congrFun (congrFun h1 (0 : Fin 4)) (2 : Fin 4)
  have e113 := congrFun (congrFun h1 (1 : Fin 4)) (3 : Fin 4)
  have e123 := congrFun (congrFun h1 (2 : Fin 4)) (3 : Fin 4)
  have e201 := congrFun (congrFun h2 (0 : Fin 4)) (1 : Fin 4)
  have e202 := congrFun (congrFun h2 (0 : Fin 4)) (2 : Fin 4)
  have e213 := congrFun (congrFun h2 (1 : Fin 4)) (3 : Fin 4)
  have e223 := congrFun (congrFun h2 (2 : Fin 4)) (3 : Fin 4)
  simp [T₁, T₂, Matrix.mul_apply, Fin.sum_univ_succ] at e101 e102 e113 e123 e201 e202 e213 e223
  refine ⟨Q 0 3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q₀Matrix] <;> omega

public def cuspForm (x y : Lattice) : ℤ := Q₀ x (N *ᵥ y)

public theorem cuspForm_apply (x y : Lattice) :
    cuspForm x y = 6 * x 2 * y 2 - x 3 * y 3 := by
  change Q₀ x (N *ᵥ y) = _
  rw [N_mulVec]
  simp [Q₀, Q₀Matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

public theorem cuspForm_symmetric (x y : Lattice) : cuspForm x y = cuspForm y x := by
  rw [cuspForm_apply, cuspForm_apply]
  ring

public theorem cuspForm_w_w : cuspForm wVec wVec = 6 := by
  rw [cuspForm_apply]
  change 6 * 1 * 1 - 0 * 0 = 6
  norm_num

public theorem cuspForm_delta_delta : cuspForm deltaVec deltaVec = -1 := by
  rw [cuspForm_apply]
  change 6 * 0 * 0 - 1 * 1 = -1
  norm_num

public theorem cuspForm_w_delta : cuspForm wVec deltaVec = 0 := by
  rw [cuspForm_apply]
  change 6 * 1 * 0 - 0 * 1 = 0
  norm_num

public def cuspFormGram : Matrix (Fin 2) (Fin 2) ℤ := !![6, 0; 0, -1]

public theorem cuspFormGram_det : cuspFormGram.det = -6 := by
  rw [cuspFormGram]
  eval_det

public theorem A₁_wVec_sub : A₁ *ᵥ wVec - wVec = uVec - (2 : ℤ) • wVec := by
  funext i
  fin_cases i <;> simp [A₁, wVec, uVec]

public theorem A₂_uVec_sub : A₂ *ᵥ uVec - uVec = -uVec + wVec := by
  funext i
  fin_cases i <;> simp [A₂, wVec, uVec]

public theorem A₁_uVec_sub : A₁ *ᵥ uVec - uVec = -uVec - wVec + deltaVec := by
  funext i
  fin_cases i <;> simp [A₁, wVec, uVec, deltaVec]

/-- Images of the two finite-monodromy differences. -/
public def dualMonodromyDifferences : Set Lattice :=
  Set.range (fun x => A₁ *ᵥ x - x) ∪ Set.range (fun x => A₂ *ᵥ x - x)

/-- The subgroup of the dual lattice generated by finite-monodromy differences. -/
public def dualCoinvariantRelations : Submodule ℤ Lattice :=
  Submodule.span ℤ dualMonodromyDifferences

public theorem dualCoinvariantRelations_eq_ker_gamma :
    dualCoinvariantRelations = LinearMap.ker gamma := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change gamma (A₁ *ᵥ x - x) = 0
      rw [map_sub, gamma_A₁, sub_self]
    · change gamma (A₂ *ᵥ x - x) = 0
      rw [map_sub, gamma_A₂, sub_self]
  · intro x hx
    have hx0 : x 0 = 0 := by
      change gamma x = 0 at hx
      rwa [gamma_apply] at hx
    have hA1w : A₁ *ᵥ wVec - wVec ∈ dualCoinvariantRelations :=
      Submodule.subset_span (Or.inl ⟨wVec, rfl⟩)
    have hA2u : A₂ *ᵥ uVec - uVec ∈ dualCoinvariantRelations :=
      Submodule.subset_span (Or.inr ⟨uVec, rfl⟩)
    have hwneg : -wVec ∈ dualCoinvariantRelations := by
      have h := dualCoinvariantRelations.add_mem hA1w hA2u
      rw [A₁_wVec_sub, A₂_uVec_sub] at h
      have heq : (uVec - (2 : ℤ) • wVec) + (-uVec + wVec) = -wVec := by
        module
      rw [← heq]
      exact h
    have hw : wVec ∈ dualCoinvariantRelations := by
      simpa using dualCoinvariantRelations.neg_mem hwneg
    have hu : uVec ∈ dualCoinvariantRelations := by
      have h := dualCoinvariantRelations.add_mem hA1w
        (dualCoinvariantRelations.smul_mem (2 : ℤ) hw)
      rw [A₁_wVec_sub] at h
      have heq : (uVec - (2 : ℤ) • wVec) + (2 : ℤ) • wVec = uVec := by
        module
      rw [← heq]
      exact h
    have hA1u : A₁ *ᵥ uVec - uVec ∈ dualCoinvariantRelations :=
      Submodule.subset_span (Or.inl ⟨uVec, rfl⟩)
    have hd : deltaVec ∈ dualCoinvariantRelations := by
      have h := dualCoinvariantRelations.add_mem
        (dualCoinvariantRelations.add_mem hA1u hu) hw
      rw [A₁_uVec_sub] at h
      have heq : (-uVec - wVec + deltaVec) + uVec + wVec = deltaVec := by
        module
      rw [← heq]
      exact h
    have hdecomp :
        x = (x 1) • uVec + (x 2) • wVec + (x 3) • deltaVec := by
      funext i
      fin_cases i <;> simp [uVec, wVec, deltaVec, hx0]
    rw [hdecomp]
    exact dualCoinvariantRelations.add_mem
      (dualCoinvariantRelations.add_mem (dualCoinvariantRelations.smul_mem (x 1) hu)
        (dualCoinvariantRelations.smul_mem (x 2) hw))
      (dualCoinvariantRelations.smul_mem (x 3) hd)

public theorem gamma_surjective : Function.Surjective gamma := by
  intro z
  refine ⟨![z, 0, 0, 0], ?_⟩
  rfl

/-- The dual-lattice coinvariants are freely generated by the first coordinate. -/
public noncomputable def dualCoinvariantsEquivInt :
    (Lattice ⧸ dualCoinvariantRelations) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq dualCoinvariantRelations (LinearMap.ker gamma)
    dualCoinvariantRelations_eq_ker_gamma).trans
    (gamma.quotKerEquivOfSurjective gamma_surjective)

end SphereSixComplex.LatticeData
