module

public import SphereSixComplex.Periods.ExactFuchsianInvariantContinuousDescent
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Descent from the two finite Fuchsian generators

The source group is the free product of its order-three and order-four factors.  Consequently,
invariance under the two distinguished generators is enough for continuous descent through the
exact quotient coordinate.
-/

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Invariance of a source function under one deck transformation. -/
@[expose] public def SourceFunctionInvariant
    (f : UpperHalfPlane → ℂ) (g : Delta) : Prop :=
  ∀ z, f (fuchsianSourceAction g • z) = f z

public theorem SourceFunctionInvariant.one (f : UpperHalfPlane → ℂ) :
    SourceFunctionInvariant f 1 := by
  intro z
  simp

public theorem SourceFunctionInvariant.mul
    {f : UpperHalfPlane → ℂ} {g h : Delta}
    (hg : SourceFunctionInvariant f g) (hh : SourceFunctionInvariant f h) :
    SourceFunctionInvariant f (g * h) := by
  intro z
  rw [map_mul, mul_smul]
  exact (hg (fuchsianSourceAction h • z)).trans (hh z)

public theorem SourceFunctionInvariant.pow
    {f : UpperHalfPlane → ℂ} {g : Delta}
    (hg : SourceFunctionInvariant f g) (n : ℕ) :
    SourceFunctionInvariant f (g ^ n) := by
  induction n with
  | zero => simpa using SourceFunctionInvariant.one f
  | succ n ih => simpa [pow_succ] using ih.mul hg

private theorem multiplicativeZMod_eq_generator_pow {k : ℕ} [NeZero k]
    (x : Multiplicative (ZMod k)) :
    x = Multiplicative.ofAdd (1 : ZMod k) ^ x.toAdd.val := by
  apply Multiplicative.toAdd.injective
  simp

/-- Invariance under the two standard generators implies invariance under the entire free
product. -/
public theorem sourceFunctionInvariant_all
    (f : UpperHalfPlane → ℂ)
    (h₁ : SourceFunctionInvariant f g₁)
    (h₂ : SourceFunctionInvariant f g₂) :
    ∀ g : Delta, SourceFunctionInvariant f g := by
  intro g
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      rw [multiplicativeZMod_eq_generator_pow a, map_pow]
      rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁ by
        exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm]
      exact h₁.pow _
  | inr a =>
      rw [multiplicativeZMod_eq_generator_pow a, map_pow]
      rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂ by
        exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm]
      exact h₂.pow _
  | mul g h hg hh => exact hg.mul hh

/-- A continuous function invariant under the two finite generators descends continuously
through the exact Fuchsian quotient. -/
@[expose] public noncomputable def
    ExactFuchsianOrbifoldCoordinate.descendGeneratorInvariantContinuous
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (h₁ : SourceFunctionInvariant f g₁)
    (h₂ : SourceFunctionInvariant f g₂) :
    C(ℂ, ℂ) :=
  C.descendInvariantContinuous f hf (sourceFunctionInvariant_all f h₁ h₂)

/-- Pullback of the generator-invariant descent recovers the source function. -/
public theorem ExactFuchsianOrbifoldCoordinate.descendGeneratorInvariantContinuous_comp
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (h₁ : SourceFunctionInvariant f g₁)
    (h₂ : SourceFunctionInvariant f g₂) (z : UpperHalfPlane) :
    C.descendGeneratorInvariantContinuous f hf h₁ h₂ (C.coordinate z) = f z :=
  C.descendInvariantContinuous_comp f hf (sourceFunctionInvariant_all f h₁ h₂) z

end SphereSixComplex.Periods
