module

public import SphereSixComplex.LatticeData
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The abstract triangle-group representation

The algebraic part of Definition 2.15: the coproduct of cyclic groups of orders three and
four acts on the rank-four lattice through the monodromy matrices.
-/

open Matrix

namespace SphereSixComplex.TriangleGroup

open LatticeData

public abbrev CyclicThree := Multiplicative (ZMod 3)

public abbrev CyclicFour := Multiplicative (ZMod 4)

public abbrev Delta := Monoid.Coprod CyclicThree CyclicFour

public def g₁ : Delta := Monoid.Coprod.inl (Multiplicative.ofAdd 1)

public def g₂ : Delta := Monoid.Coprod.inr (Multiplicative.ofAdd 1)

public def g₀ : Delta := (g₁ * g₂)⁻¹

public theorem g₁_pow_three : g₁ ^ 3 = 1 := by
  let a := Multiplicative.ofAdd (1 : ZMod 3)
  calc
    g₁ ^ 3 = Monoid.Coprod.inl (a ^ 3) :=
      (map_pow (Monoid.Coprod.inl : CyclicThree →* Delta) a 3).symm
    _ = Monoid.Coprod.inl 1 := congrArg (Monoid.Coprod.inl : CyclicThree → Delta) (by decide)
    _ = 1 := map_one (Monoid.Coprod.inl : CyclicThree →* Delta)

public theorem g₂_pow_four : g₂ ^ 4 = 1 := by
  let a := Multiplicative.ofAdd (1 : ZMod 4)
  calc
    g₂ ^ 4 = Monoid.Coprod.inr (a ^ 4) :=
      (map_pow (Monoid.Coprod.inr : CyclicFour →* Delta) a 4).symm
    _ = Monoid.Coprod.inr 1 := congrArg (Monoid.Coprod.inr : CyclicFour → Delta) (by decide)
    _ = 1 := map_one (Monoid.Coprod.inr : CyclicFour →* Delta)

public theorem g₁_mul_g₂_mul_g₀ : g₁ * g₂ * g₀ = 1 := by
  simp [g₀]

public noncomputable def t₁ : Lattice ≃ₗ[ℤ] Lattice :=
  T₁.toLinearEquiv' (Matrix.invertibleOfIsUnitDet T₁ (by simp [T₁_det]))

public noncomputable def t₂ : Lattice ≃ₗ[ℤ] Lattice :=
  T₂.toLinearEquiv' (Matrix.invertibleOfIsUnitDet T₂ (by simp [T₂_det]))

public noncomputable def t₀ : Lattice ≃ₗ[ℤ] Lattice :=
  (t₁ * t₂)⁻¹

@[simp]
public theorem t₁_apply (x : Lattice) : t₁ x = T₁ *ᵥ x := by
  change Matrix.toLin' T₁ x = _
  rfl

@[simp]
public theorem t₂_apply (x : Lattice) : t₂ x = T₂ *ᵥ x := by
  change Matrix.toLin' T₂ x = _
  rfl

@[simp]
public theorem t₀_apply (x : Lattice) : t₀ x = T₀ *ᵥ x := by
  apply (t₁ * t₂).injective
  have hleft : (t₁ * t₂) (t₀ x) = x := by simp [t₀]
  rw [hleft]
  rw [LinearEquiv.mul_apply, t₁_apply, t₂_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) T₁_mul_T₂_mul_T₀
  simpa using h.symm

public theorem t₁_pow_three : t₁ ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  change T₁ *ᵥ (T₁ *ᵥ (T₁ *ᵥ x)) = x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) T₁_pow_three
  simpa [pow_succ] using h

public theorem t₂_pow_four : t₂ ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  change T₂ *ᵥ (T₂ *ᵥ (T₂ *ᵥ (T₂ *ᵥ x))) = x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ ↦ M *ᵥ x) T₂_pow_four
  simpa [pow_succ] using h

public theorem t₁_mul_t₂_mul_t₀ : t₁ * t₂ * t₀ = 1 := by
  simp [t₀]

public noncomputable def cyclicRepresentation {G : Type*} [Group G] (n : ℕ) (g : G)
    (h : g ^ n = 1) : Multiplicative (ZMod n) →* G := by
  let powers : ℤ →+ Additive G :=
    { toFun := fun k ↦ Additive.ofMul (g ^ k)
      map_zero' := by simp
      map_add' := by
        intro a b
        apply Additive.toMul.injective
        exact zpow_add g a b }
  have powers_n : powers (n : ℤ) = 0 := by
    apply Additive.toMul.injective
    simpa [powers] using h
  let descended : ZMod n →+ Additive G := ZMod.lift n ⟨powers, powers_n⟩
  exact
    { toFun := fun x ↦ Additive.toMul (descended (Multiplicative.toAdd x))
      map_one' := by simp [descended]
      map_mul' := by
        intro x y
        apply Additive.ofMul.injective
        simp [descended] }

@[simp]
public theorem cyclicRepresentation_generator {G : Type*} [Group G] (n : ℕ) (g : G)
    (h : g ^ n = 1) : cyclicRepresentation n g h (Multiplicative.ofAdd 1) = g := by
  unfold cyclicRepresentation
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  have hto : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod n)) = 1 := by rfl
  rw [hto]
  have hone : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := by simp
  rw [hone, ZMod.lift_coe]
  simp

public noncomputable def rhoV : Delta →* (Lattice ≃ₗ[ℤ] Lattice) :=
  Monoid.Coprod.lift (cyclicRepresentation 3 t₁ t₁_pow_three)
    (cyclicRepresentation 4 t₂ t₂_pow_four)

@[simp]
public theorem rhoV_g₁ : rhoV g₁ = t₁ := by
  simp [rhoV, g₁]

@[simp]
public theorem rhoV_g₂ : rhoV g₂ = t₂ := by
  simp [rhoV, g₂]

@[simp]
public theorem rhoV_g₀ : rhoV g₀ = t₀ := by
  rw [g₀, map_inv, map_mul, rhoV_g₁, rhoV_g₂]
  exact inv_eq_of_mul_eq_one_right t₁_mul_t₂_mul_t₀

@[simp]
public theorem rhoV_g₁_apply (x : Lattice) : rhoV g₁ x = T₁ *ᵥ x := by
  simp

@[simp]
public theorem rhoV_g₂_apply (x : Lattice) : rhoV g₂ x = T₂ *ᵥ x := by
  simp

@[simp]
public theorem rhoV_g₀_apply (x : Lattice) : rhoV g₀ x = T₀ *ᵥ x := by
  simp

public theorem rhoV_g1 : rhoV g₁ = t₁ := rhoV_g₁

public theorem rhoV_g2 : rhoV g₂ = t₂ := rhoV_g₂

public theorem rhoV_g0 : rhoV g₀ = t₀ := rhoV_g₀

public theorem rhoV_g0_apply (x : Lattice) : rhoV g₀ x = T₀ *ᵥ x := rhoV_g₀_apply x

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

public theorem rhoLambda_relation : rhoLambda (g₁ * g₂ * g₀) = 1 := by
  rw [g₁_mul_g₂_mul_g₀, map_one]

public theorem rhoLambda_g1 : rhoLambda g₁ = a₁ := rhoLambda_g₁

public theorem rhoLambda_g2 : rhoLambda g₂ = a₂ := rhoLambda_g₂

public theorem rhoLambda_g0 : rhoLambda g₀ = m₀ := rhoLambda_g₀

public theorem rhoLambda_g0_apply (x : DualLattice) : rhoLambda g₀ x = M₀ *ᵥ x :=
  rhoLambda_g₀_apply x

end SphereSixComplex.TriangleGroup
