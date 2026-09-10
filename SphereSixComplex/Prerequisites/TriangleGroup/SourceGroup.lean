module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic

namespace SphereSixComplex.TriangleGroup

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

end SphereSixComplex.TriangleGroup
