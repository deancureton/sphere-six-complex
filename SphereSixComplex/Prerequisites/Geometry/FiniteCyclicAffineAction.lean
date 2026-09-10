module

public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

noncomputable section

namespace SphereSixComplex.Geometry

public abbrev FiniteCyclic (m : ℕ) := Multiplicative (ZMod m)

@[expose] public def cyclicGenerator (m : ℕ) : FiniteCyclic m :=
  Multiplicative.ofAdd 1

@[expose] public def affineEquiv {T : Type*} [AddCommGroup T]
    (A : T ≃+ T) (b : T) : Equiv.Perm T where
  toFun x := A x + b
  invFun x := A.symm (x - b)
  left_inv x := by simp
  right_inv x := by simp

@[simp]
public theorem affineEquiv_apply {T : Type*} [AddCommGroup T]
    (A : T ≃+ T) (b x : T) :
    affineEquiv A b x = A x + b := rfl

public theorem affineEquiv_pow_apply {T : Type*} [AddCommGroup T]
    (A : T ≃+ T) (b : T) (hb : A b = b) (k : ℕ) (x : T) :
    (affineEquiv A b ^ k) x = (A.toEquiv ^ k) x + k • b := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, affineEquiv_apply, ih]
      rw [pow_succ', Equiv.Perm.mul_apply]
      simp [hb, add_assoc, add_nsmul]

public theorem affineEquiv_pow_eq_one {T : Type*} [AddCommGroup T]
    (A : T ≃+ T) (b : T) (hb : A b = b) (m : ℕ)
    (hA : A.toEquiv ^ m = 1) (hmb : m • b = 0) :
    affineEquiv A b ^ m = 1 := by
  apply Equiv.ext
  intro x
  rw [affineEquiv_pow_apply A b hb, hA, hmb]
  simp

public theorem cyclic_eq_generator_pow {m : ℕ} [NeZero m]
    (g : FiniteCyclic m) :
    g = cyclicGenerator m ^ (Multiplicative.toAdd g).val := by
  apply Multiplicative.toAdd.injective
  rw [show Multiplicative.toAdd g =
    ((Multiplicative.toAdd g).val : ZMod m) from
      (ZMod.natCast_zmod_val (Multiplicative.toAdd g)).symm]
  simp [cyclicGenerator]

public theorem cyclicGenerator_pow_ne_one {m k : ℕ}
    (hk : 0 < k) (hkm : k < m) :
    cyclicGenerator m ^ k ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  have hk0 : (k : ZMod m) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hkm] at hv
    simp at hv
    omega
  apply hk0
  simpa [cyclicGenerator] using h'

public theorem finiteCyclic_card (m : ℕ) [NeZero m] :
    Nat.card (FiniteCyclic m) = m := by
  simp [FiniteCyclic]

end SphereSixComplex.Geometry
