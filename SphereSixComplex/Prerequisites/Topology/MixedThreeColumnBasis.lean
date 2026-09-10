module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel

@[expose] public section
namespace SphereSixComplex

public def mixedThreeColumnEquiv : (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) where
  toFun x := ![x 0, x 1 - x 2 + x 3, x 2, -x 1]
  invFun x := ![x 0, -x 3, x 2, x 1 + x 2 + x 3]
  left_inv x := by ext i; fin_cases i <;> simp; abel
  right_inv x := by ext i; fin_cases i <;> simp; abel
  map_add' x y := by ext i; fin_cases i <;> simp <;> abel

public def integerUnitDiagonalEquiv {ι : Type*} (u : ι → ℤˣ) :
    (ι → ℤ) ≃+ (ι → ℤ) where
  toFun x i := ↑(u i) * x i
  invFun x i := ↑((u i)⁻¹) * x i
  left_inv x := by ext i; simp [← mul_assoc]
  right_inv x := by ext i; simp [← mul_assoc]
  map_add' x y := by ext i; exact mul_add _ _ _

public def signedMixedThreeColumnEquiv (a b c : ℤˣ) :
    (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) :=
  mixedThreeColumnEquiv.trans (integerUnitDiagonalEquiv ![1, a, b, c])

public theorem signedMixedThreeColumnEquiv_apply (a b c : ℤˣ) (x : Fin 4 → ℤ) :
    signedMixedThreeColumnEquiv a b c x =
      ![x 0, ↑a * (x 1 - x 2 + x 3), ↑b * x 2, -(↑c * x 1)] := by
  ext i
  fin_cases i <;>
    simp [signedMixedThreeColumnEquiv, integerUnitDiagonalEquiv, mixedThreeColumnEquiv]

public theorem signedMixedThreeColumnEquiv_first (a b c : ℤˣ) :
    signedMixedThreeColumnEquiv a b c (Pi.single 0 1) = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [signedMixedThreeColumnEquiv_apply]

public theorem signedMixedThreeColumnEquiv_one (a b c : ℤˣ) :
    signedMixedThreeColumnEquiv a b c (Pi.single 1 1) = ![0, ↑a, 0, -↑c] := by
  ext i
  fin_cases i <;> simp [signedMixedThreeColumnEquiv_apply]

public theorem signedMixedThreeColumnEquiv_two (a b c : ℤˣ) :
    signedMixedThreeColumnEquiv a b c (Pi.single 2 1) = ![0, -↑a, ↑b, 0] := by
  ext i
  fin_cases i <;> simp [signedMixedThreeColumnEquiv_apply]

public theorem signedMixedThreeColumnEquiv_three (a b c : ℤˣ) :
    signedMixedThreeColumnEquiv a b c (Pi.single 3 1) = ![0, ↑a, 0, 0] := by
  ext i
  fin_cases i <;> simp [signedMixedThreeColumnEquiv_apply]

end SphereSixComplex
