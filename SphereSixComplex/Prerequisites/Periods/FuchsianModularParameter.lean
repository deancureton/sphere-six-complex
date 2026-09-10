module

public import SphereSixComplex.Prerequisites.Periods.ModularUniformization
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.Prerequisites.TriangleGroup.SourceGroup

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Equivariance of a candidate modular parameter at one triangle-group element. -/
@[expose] public def FuchsianTauEquivariant
    (tau : UpperHalfPlane → UpperHalfPlane) (g : Delta) : Prop :=
  ∀ z, tau (fuchsianSourceAction g • z) = rhoTauReal g • tau z

public theorem fuchsianTauEquivariant_one (tau : UpperHalfPlane → UpperHalfPlane) :
    FuchsianTauEquivariant tau 1 := by
  intro z
  simp

public theorem FuchsianTauEquivariant.mul {tau : UpperHalfPlane → UpperHalfPlane} {g h : Delta}
    (hg : FuchsianTauEquivariant tau g) (hh : FuchsianTauEquivariant tau h) :
    FuchsianTauEquivariant tau (g * h) := by
  intro z
  rw [map_mul, map_mul, mul_smul, mul_smul, hg, hh]

public theorem FuchsianTauEquivariant.pow {tau : UpperHalfPlane → UpperHalfPlane} {g : Delta}
    (hg : FuchsianTauEquivariant tau g) (n : ℕ) :
    FuchsianTauEquivariant tau (g ^ n) := by
  induction n with
  | zero => simpa using fuchsianTauEquivariant_one tau
  | succ n ih => simpa [pow_succ] using ih.mul hg

private theorem multiplicativeZMod_eq_generator_pow {k : ℕ} [NeZero k]
    (x : Multiplicative (ZMod k)) :
    x = Multiplicative.ofAdd (1 : ZMod k) ^ x.toAdd.val := by
  apply Multiplicative.toAdd.injective
  simp

/-- A holomorphic modular parameter on the explicit Fuchsian source, specified only on the two
cyclic generators. -/
public structure FuchsianModularParameter where
  tau : UpperHalfPlane → UpperHalfPlane
  tau_holomorphic : MDiff tau
  transform_one : FuchsianTauEquivariant tau g₁
  transform_two : FuchsianTauEquivariant tau g₂

namespace FuchsianModularParameter

variable (P : FuchsianModularParameter)

private theorem equivariant_inl (a : CyclicThree) :
    FuchsianTauEquivariant P.tau (Monoid.Coprod.inl a) := by
  rw [multiplicativeZMod_eq_generator_pow a, map_pow]
  rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁ by
    exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm]
  exact P.transform_one.pow _

private theorem equivariant_inr (a : CyclicFour) :
    FuchsianTauEquivariant P.tau (Monoid.Coprod.inr a) := by
  rw [multiplicativeZMod_eq_generator_pow a, map_pow]
  rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂ by
    exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm]
  exact P.transform_two.pow _

/-- The two generator identities imply equivariance for every element of the free product. -/
public theorem equivariant (g : Delta) : FuchsianTauEquivariant P.tau g := by
  induction g using Monoid.Coprod.induction_on with
  | inl a => exact P.equivariant_inl a
  | inr a => exact P.equivariant_inr a
  | mul g h hg hh => exact hg.mul hh

/-- The invariant coordinate induced by the normalized modular function. -/
@[expose] public noncomputable def coordinate (z : UpperHalfPlane) : ℂ :=
  normalizedJ (P.tau z) / 1728

public theorem coordinate_holomorphic : MDiff P.coordinate := by
  exact (normalizedJ_mdifferentiable.comp P.tau_holomorphic).div mdifferentiable_const
    (by norm_num)

public theorem coordinate_invariant (g : Delta) (z : UpperHalfPlane) :
    P.coordinate (fuchsianSourceAction g • z) = P.coordinate z := by
  rw [coordinate, coordinate, P.equivariant g z]
  change normalizedJ (Matrix.SpecialLinearGroup.mapGL ℝ (rhoTau g) • P.tau z) / 1728 =
    normalizedJ (P.tau z) / 1728
  rw [normalizedJ_modular_invariant]

/-- A holomorphic equivariant modular parameter completes the explicit smooth Fuchsian source to
the triangle-uniformization interface used by the period construction. -/
@[expose] public noncomputable def toTriangleUniformization : TriangleUniformization where
  sourceAction := fuchsianSourceAction
  sourceAction_contMDiff := fuchsianSourceAction_contMDiff
  coordinate := P.coordinate
  coordinate_holomorphic := P.coordinate_holomorphic
  coordinate_invariant := P.coordinate_invariant
  zOne := fuchsianOneFixedPoint
  zTwo := fuchsianTwoFixedPoint
  zOne_fixed := fuchsianOneFixedPoint_fixed
  zTwo_fixed := fuchsianTwoFixedPoint_fixed
  cuspRegion := fuchsianCuspRegion
  cuspRegion_nonempty := fuchsianCuspRegion_nonempty
  cuspRegion_invariant := fuchsianCuspRegion_invariant

@[simp]
public theorem toTriangleUniformization_sourceAction :
    P.toTriangleUniformization.sourceAction = fuchsianSourceAction :=
  rfl

@[simp]
public theorem toTriangleUniformization_coordinate (z : UpperHalfPlane) :
    P.toTriangleUniformization.coordinate z = normalizedJ (P.tau z) / 1728 :=
  rfl

end FuchsianModularParameter

end SphereSixComplex.Periods
