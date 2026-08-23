module

public import SphereSixComplex.TriangleGroup.Representation
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The modular-parameter representation

The integral two-dimensional representation whose induced Möbius action gives the
transformations of the period parameter `tau`.
-/

open Matrix
open scoped MatrixGroups

namespace SphereSixComplex.TriangleGroup

public abbrev ModularMatrix := Matrix.SpecialLinearGroup (Fin 2) ℤ

@[expose] public def modularOne : ModularMatrix :=
  ⟨!![-1, 1; -1, 0], by norm_num [Matrix.det_fin_two]⟩

@[expose] public def modularTwo : ModularMatrix :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

@[expose] public def modularCusp : ModularMatrix :=
  ⟨!![1, -1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

public theorem modularOne_pow_three : modularOne ^ 3 = 1 := by
  apply Subtype.ext
  change (modularOne : Matrix (Fin 2) (Fin 2) ℤ) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularOne, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem modularTwo_pow_four : modularTwo ^ 4 = 1 := by
  apply Subtype.ext
  change (modularTwo : Matrix (Fin 2) (Fin 2) ℤ) ^ 4 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularTwo, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem modularOne_mul_modularTwo_mul_modularCusp :
    modularOne * modularTwo * modularCusp = 1 := by
  apply Subtype.ext
  change (modularOne : Matrix (Fin 2) (Fin 2) ℤ) * modularTwo * modularCusp = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularOne, modularTwo, modularCusp, Matrix.mul_apply, Fin.sum_univ_succ]

public noncomputable def rhoTau : Delta →* ModularMatrix :=
  Monoid.Coprod.lift (cyclicRepresentation 3 modularOne modularOne_pow_three)
    (cyclicRepresentation 4 modularTwo modularTwo_pow_four)

@[simp]
public theorem rhoTau_g₁ : rhoTau g₁ = modularOne := by
  simp [rhoTau, SphereSixComplex.TriangleGroup.g₁.eq_def]

@[simp]
public theorem rhoTau_g₂ : rhoTau g₂ = modularTwo := by
  simp [rhoTau, SphereSixComplex.TriangleGroup.g₂.eq_def]

@[simp]
public theorem rhoTau_g₀ : rhoTau g₀ = modularCusp := by
  rw [SphereSixComplex.TriangleGroup.g₀.eq_def, map_inv, map_mul, rhoTau_g₁, rhoTau_g₂]
  exact inv_eq_of_mul_eq_one_right modularOne_mul_modularTwo_mul_modularCusp

public noncomputable def modularToReal : ModularMatrix →* GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ

public noncomputable def rhoTauReal : Delta →* GL (Fin 2) ℝ :=
  modularToReal.comp rhoTau

public theorem modularOne_real_matrix :
    ((modularToReal modularOne : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1, 1; -1, 0] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) modularOne : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [modularOne]

public theorem modularTwo_real_matrix :
    ((modularToReal modularTwo : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; 1, 0] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) modularTwo : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [modularTwo]

public theorem modularCusp_real_matrix :
    ((modularToReal modularCusp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, -1; 0, 1] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) modularCusp : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [modularCusp]

@[simp]
public theorem rhoTauReal_g₁ : rhoTauReal g₁ = modularToReal modularOne := by
  simp [rhoTauReal]

@[simp]
public theorem rhoTauReal_g₂ : rhoTauReal g₂ = modularToReal modularTwo := by
  simp [rhoTauReal]

@[simp]
public theorem rhoTauReal_g₀ : rhoTauReal g₀ = modularToReal modularCusp := by
  simp [rhoTauReal]

public theorem rhoTauReal_g₁_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₁ • z : UpperHalfPlane) : ℂ) = (z - 1) / z := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, rhoTauReal_g₁,
      modularOne_real_matrix]
    field_simp [z.ne_zero]
    ring
  · simp [rhoTauReal_g₁, modularToReal]

public theorem rhoTauReal_g₂_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₂ • z : UpperHalfPlane) : ℂ) = -1 / z := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, rhoTauReal_g₂,
      modularTwo_real_matrix]
  · simp [rhoTauReal_g₂, modularToReal]

public theorem rhoTauReal_g₀_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₀ • z : UpperHalfPlane) : ℂ) = z - 1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, rhoTauReal_g₀,
      modularCusp_real_matrix]
    ring
  · simp [rhoTauReal_g₀, modularToReal]

public theorem rhoTau_relation : rhoTau (g₁ * g₂ * g₀) = 1 := by
  rw [g₁_mul_g₂_mul_g₀, map_one]

public theorem rhoTau_g1 : rhoTau g₁ = modularOne := rhoTau_g₁

public theorem rhoTau_g2 : rhoTau g₂ = modularTwo := rhoTau_g₂

public theorem rhoTau_g0 : rhoTau g₀ = modularCusp := rhoTau_g₀

public theorem rhoTauReal_g1_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₁ • z : UpperHalfPlane) : ℂ) = (z - 1) / z :=
  rhoTauReal_g₁_smul z

public theorem rhoTauReal_g2_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₂ • z : UpperHalfPlane) : ℂ) = -1 / z :=
  rhoTauReal_g₂_smul z

public theorem rhoTauReal_g0_smul (z : UpperHalfPlane) :
    ((rhoTauReal g₀ • z : UpperHalfPlane) : ℂ) = z - 1 :=
  rhoTauReal_g₀_smul z

end SphereSixComplex.TriangleGroup
