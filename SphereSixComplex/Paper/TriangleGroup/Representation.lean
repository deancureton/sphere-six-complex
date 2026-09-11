module

public import SphereSixComplex.Paper.LatticeData
public import SphereSixComplex.Prerequisites.TriangleGroup.SourceGroup
import all SphereSixComplex.Prerequisites.TriangleGroup.SourceGroup
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The abstract triangle-group representation

The algebraic part of Definition 2.15: the coproduct of cyclic groups of orders three and
four acts on the rank-four lattice through the monodromy matrices.
-/

open Matrix

namespace SphereSixComplex.TriangleGroup

open LatticeData





















public abbrev DualLattice := LatticeData.Lattice

public theorem A₁_det : A₁.det = 1 := by
  rw [A₁_eq_transpose_T₁_sq, Matrix.det_transpose, Matrix.det_pow, T₁_det]
  norm_num

public theorem A₂_det : A₂.det = 1 := by
  rw [A₂_eq_transpose_T₂_cube, Matrix.det_transpose, Matrix.det_pow, T₂_det]
  norm_num

public theorem A₁_pow_three : A₁ ^ 3 = 1 := by
  rw [A₁_eq_transpose_T₁_sq, ← Matrix.transpose_pow]
  rw [← pow_mul]
  norm_num only
  rw [show T₁ ^ 6 = (T₁ ^ 3) ^ 2 by rw [← pow_mul']]
  rw [T₁_pow_three]
  simp

public theorem A₂_pow_four : A₂ ^ 4 = 1 := by
  rw [A₂_eq_transpose_T₂_cube, ← Matrix.transpose_pow]
  rw [← pow_mul]
  norm_num only
  rw [show T₂ ^ 12 = (T₂ ^ 4) ^ 3 by rw [← pow_mul']]
  rw [T₂_pow_four]
  simp

public noncomputable def a₁ : DualLattice ≃ₗ[ℤ] DualLattice :=
  A₁.toLinearEquiv' (Matrix.invertibleOfIsUnitDet A₁ (by simp [A₁_det]))

public noncomputable def a₂ : DualLattice ≃ₗ[ℤ] DualLattice :=
  A₂.toLinearEquiv' (Matrix.invertibleOfIsUnitDet A₂ (by simp [A₂_det]))

public noncomputable def m₀ : DualLattice ≃ₗ[ℤ] DualLattice :=
  (a₁ * a₂)⁻¹

@[simp]
public theorem a₁_apply (x : DualLattice) : a₁ x = A₁ *ᵥ x := by
  change Matrix.toLin' A₁ x = _
  rfl

@[simp]
public theorem a₂_apply (x : DualLattice) : a₂ x = A₂ *ᵥ x := by
  change Matrix.toLin' A₂ x = _
  rfl

@[simp]
public theorem m₀_apply (x : DualLattice) : m₀ x = M₀ *ᵥ x := by
  apply (a₁ * a₂).injective
  have hleft : (a₁ * a₂) (m₀ x) = x := by simp [m₀]
  rw [hleft]
  rw [LinearEquiv.mul_apply, a₁_apply, a₂_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) A₁_mul_A₂_mul_M₀
  simpa using h.symm

public theorem a₁_pow_three : a₁ ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  change A₁ *ᵥ (A₁ *ᵥ (A₁ *ᵥ x)) = x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) A₁_pow_three
  simpa [pow_succ] using h

public theorem a₂_pow_four : a₂ ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  change A₂ *ᵥ (A₂ *ᵥ (A₂ *ᵥ (A₂ *ᵥ x))) = x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) A₂_pow_four
  simpa [pow_succ] using h

public theorem a₁_mul_a₂_mul_m₀ : a₁ * a₂ * m₀ = 1 := by
  simp [m₀]

public noncomputable def rhoLambda : Delta →* (DualLattice ≃ₗ[ℤ] DualLattice) :=
  Monoid.Coprod.lift (cyclicRepresentation 3 a₁ a₁_pow_three)
    (cyclicRepresentation 4 a₂ a₂_pow_four)

@[simp]
public theorem rhoLambda_g₁ : rhoLambda g₁ = a₁ := by
  simp [rhoLambda, g₁]

@[simp]
public theorem rhoLambda_g₂ : rhoLambda g₂ = a₂ := by
  simp [rhoLambda, g₂]

@[simp]
public theorem rhoLambda_g₀ : rhoLambda g₀ = m₀ := by
  rw [g₀, map_inv, map_mul, rhoLambda_g₁, rhoLambda_g₂]
  exact inv_eq_of_mul_eq_one_right a₁_mul_a₂_mul_m₀

@[simp]
public theorem rhoLambda_g₁_apply (x : DualLattice) : rhoLambda g₁ x = A₁ *ᵥ x := by
  simp

@[simp]
public theorem rhoLambda_g₂_apply (x : DualLattice) : rhoLambda g₂ x = A₂ *ᵥ x := by
  simp

@[simp]
public theorem rhoLambda_g₀_apply (x : DualLattice) : rhoLambda g₀ x = M₀ *ᵥ x := by
  simp




public theorem rhoLambda_g0 : rhoLambda g₀ = m₀ := rhoLambda_g₀


end SphereSixComplex.TriangleGroup
