module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section
noncomputable section
namespace SphereSixComplex.CyclicCoinvariants

/-- The relation map imposing `m * meridian = [v]` after taking coinvariants. -/
public def relationMap {Λ : Type*} [AddCommGroup Λ]
    (D : Λ →ₗ[ℤ] Λ) (v : Λ) (m : ℤ) :
    ℤ →ₗ[ℤ] ((Λ ⧸ LinearMap.range D) × ℤ) where
  toFun k := k • (-Submodule.Quotient.mk v, m)
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

/-- The abelian multiple-fibre presentation: coinvariants plus a meridian, modulo
`m * meridian = [v]`. -/
public abbrev Presentation {Λ : Type*} [AddCommGroup Λ]
    (D : Λ →ₗ[ℤ] Λ) (v : Λ) (m : ℤ) :=
  ((Λ ⧸ LinearMap.range D) × ℤ) ⧸
    LinearMap.range (relationMap D v m)

/-- Maps out of the multiple-fibre presentation are exactly pairs: a map killing the difference,
together with a meridian image whose `m`-th multiple is the image of the twist.

This is the universal property that an identification of `H₁` of a free affine cyclic quotient with
this presentation has to go through, in either direction; see issue #148. -/
public noncomputable def lift {Λ : Type*} [AddCommGroup Λ]
    {B : Type*} [AddCommGroup B]
    (D : Λ →ₗ[ℤ] Λ) (v : Λ) (m : ℤ)
    (φ : Λ →ₗ[ℤ] B) (hφ : ∀ x, φ (D x) = 0) (b : B) (hb : m • b = φ v) :
    Presentation D v m →ₗ[ℤ] B := by
  refine Submodule.liftQ _ ((Submodule.liftQ _ φ ?_).coprod
    (LinearMap.toSpanSingleton ℤ B b)) ?_
  · rintro x ⟨y, rfl⟩; exact hφ y
  · rintro x ⟨k, rfl⟩
    simp [relationMap, LinearMap.toSpanSingleton, hb.symm, mul_comm]
    rw [smul_smul, mul_comm k m]
    exact neg_add_cancel _

/-- The lift sends the class of `(x, k)` to `φ x + k • b`. -/
public theorem lift_mk {Λ : Type*} [AddCommGroup Λ]
    {B : Type*} [AddCommGroup B]
    (D : Λ →ₗ[ℤ] Λ) (v : Λ) (m : ℤ)
    (φ : Λ →ₗ[ℤ] B) (hφ : ∀ x, φ (D x) = 0) (b : B) (hb : m • b = φ v)
    (x : Λ) (k : ℤ) :
    lift D v m φ hφ b hb
        (Submodule.Quotient.mk (Submodule.Quotient.mk x, k)) = φ x + k • b := by
  simp [lift, LinearMap.toSpanSingleton]

end SphereSixComplex.CyclicCoinvariants
