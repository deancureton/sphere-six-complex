module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences with the unit cylinder

The two endpoint inclusions into `X × [0, 1]` are homotopy equivalences. The homotopies below
linearly interpolate the interval coordinate from the chosen endpoint to its original value.
-/

@[expose] public section

open ContinuousMap
open scoped unitInterval

namespace SphereSixComplex

variable (X : Type*) [TopologicalSpace X]

/-- Inclusion of `X` as the zero end of its unit cylinder, as a homotopy equivalence. -/
public def cylinderZeroHomotopyEquiv : X ≃ₕ X × Set.Icc (0 : ℝ) 1 where
  toFun :=
    { toFun := fun x ↦ (x, 0)
      continuous_toFun := continuous_id.prodMk continuous_const }
  invFun :=
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }
  left_inv := by
    convert Homotopic.refl (ContinuousMap.id X) using 1
    ext x
    rfl
  right_inv :=
    ⟨{ toFun := fun p ↦ (p.2.1, Set.Icc.convexComb 0 p.2.2 p.1)
       continuous_toFun := by fun_prop
       map_zero_left := by intro p; ext <;> simp
       map_one_left := by intro p; ext <;> simp }⟩

/-- Inclusion of `X` as the one end of its unit cylinder, as a homotopy equivalence. -/
public def cylinderOneHomotopyEquiv : X ≃ₕ X × Set.Icc (0 : ℝ) 1 where
  toFun :=
    { toFun := fun x ↦ (x, 1)
      continuous_toFun := continuous_id.prodMk continuous_const }
  invFun :=
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }
  left_inv := by
    convert Homotopic.refl (ContinuousMap.id X) using 1
    ext x
    rfl
  right_inv :=
    ⟨{ toFun := fun p ↦ (p.2.1, Set.Icc.convexComb 1 p.2.2 p.1)
       continuous_toFun := by fun_prop
       map_zero_left := by intro p; ext <;> simp
       map_one_left := by intro p; ext <;> simp }⟩

@[simp]
public theorem cylinderZeroHomotopyEquiv_toFun (x : X) :
    (cylinderZeroHomotopyEquiv X).toFun x = (x, 0) :=
  rfl

@[simp]
public theorem cylinderOneHomotopyEquiv_toFun (x : X) :
    (cylinderOneHomotopyEquiv X).toFun x = (x, 1) :=
  rfl

/-- The forward function of `cylinderZeroHomotopyEquiv` is exactly the zero-section inclusion. -/
public theorem coe_cylinderZeroHomotopyEquiv :
    (cylinderZeroHomotopyEquiv X : X → X × Set.Icc (0 : ℝ) 1) = fun x ↦ (x, 0) :=
  rfl

/-- The forward function of `cylinderOneHomotopyEquiv` is exactly the one-section inclusion. -/
public theorem coe_cylinderOneHomotopyEquiv :
    (cylinderOneHomotopyEquiv X : X → X × Set.Icc (0 : ℝ) 1) = fun x ↦ (x, 1) :=
  rfl

end SphereSixComplex
