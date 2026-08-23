module

public import SphereSixComplex.Periods.Matrix
import all SphereSixComplex.Periods.Matrix

/-!
# Period-parameter transformations

The rational transformations of the three period parameters satisfy the triangle-group relations.
-/

namespace SphereSixComplex.Periods

/-- The order-three parameter transformation closes after three applications. -/
public theorem transformOne_order_three (x : Parameters) (hτ : x.tau ≠ 0)
    (hτ1 : x.tau ≠ 1) :
    transformOne (transformOne (transformOne x)) = x := by
  rcases x with ⟨τ, μ, β⟩
  rw [Parameters.mk.injEq]
  constructor
  · dsimp [transformOne] at *
    field_simp
    ring
  constructor
  · dsimp [transformOne] at *
    field_simp
    ring
  · dsimp [transformOne] at *
    field_simp
    ring

/-- The order-four parameter transformation closes after four applications. -/
public theorem transformTwo_order_four (x : Parameters) (hτ : x.tau ≠ 0) :
    transformTwo (transformTwo (transformTwo (transformTwo x))) = x := by
  rcases x with ⟨τ, μ, β⟩
  rw [Parameters.mk.injEq]
  constructor
  · dsimp [transformTwo] at *
    field_simp
  constructor
  · dsimp [transformTwo] at *
    field_simp
    ring
  · dsimp [transformTwo] at *
    field_simp
    ring

/-- The cusp transformation is the inverse of the product of the elliptic transformations. -/
public theorem transformOne_transformTwo_transformCusp (x : Parameters)
    (hτ1 : x.tau ≠ 1) :
    transformOne (transformTwo (transformCusp x)) = x := by
  rcases x with ⟨τ, μ, β⟩
  rw [Parameters.mk.injEq]
  constructor
  · dsimp [transformOne, transformTwo, transformCusp] at *
    field_simp
    ring
  constructor
  · dsimp [transformOne, transformTwo, transformCusp] at *
    field_simp
    ring
  · dsimp [transformOne, transformTwo, transformCusp] at *
    field_simp
    ring

end SphereSixComplex.Periods
