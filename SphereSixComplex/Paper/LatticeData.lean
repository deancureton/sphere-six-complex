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








@[expose] public def A₁ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     6, 0, 1, 0;
     -6, -1, -1, 0;
     -2, 1, 0, 1]

@[expose] public def A₂ : Matrix (Fin 4) (Fin 4) ℤ :=
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


public theorem A₁_mul_A₂_mul_M₀ : A₁ * A₂ * M₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A₁, A₂, M₀, Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] public def gamma : Lattice →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem gamma_A₁ (x : Lattice) : gamma (A₁ *ᵥ x) = gamma x := by
  simp [gamma, A₁, dotProduct, Fin.sum_univ_succ]

public theorem gamma_A₂ (x : Lattice) : gamma (A₂ *ᵥ x) = gamma x := by
  simp [gamma, A₂, dotProduct, Fin.sum_univ_succ]


@[expose] public def epsilon : Lattice := ![1, 2, -4, 0]

@[expose] public def epsilon' : Lattice := ![1, 3, -3, 0]


public theorem A₁_epsilon : A₁ *ᵥ epsilon = epsilon := by
  funext i
  fin_cases i <;> norm_num [A₁, epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem A₂_epsilon' : A₂ *ᵥ epsilon' = epsilon' := by
  funext i
  fin_cases i <;> norm_num [A₂, epsilon', Matrix.mulVec, dotProduct, Fin.sum_univ_succ]



public theorem gamma_epsilon : gamma epsilon = 1 := by
  rfl

public theorem gamma_neg_epsilon' : gamma (-epsilon') = -1 := by
  rfl


@[expose] public def uVec : Lattice := ![0, 1, 0, 0]

@[expose] public def wVec : Lattice := ![0, 0, 1, 0]

@[expose] public def deltaVec : Lattice := ![0, 0, 0, 1]














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


public theorem B₀_mul_inv : B₀ * B₀Inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B₀, B₀Inv, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem B₀_inv_mul : B₀Inv * B₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B₀, B₀Inv, Matrix.mul_apply, Fin.sum_univ_succ]


















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
    · simp [LinearMap.mem_ker, gamma_A₁]
    · simp [LinearMap.mem_ker, gamma_A₂]
  · intro x hx
    have hx0 : x 0 = 0 := by
      simpa [LinearMap.mem_ker, gamma] using hx
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



end SphereSixComplex.LatticeData
