module

public import SphereSixComplex.Periods.SchurCompactness
public import SphereSixComplex.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.Matrix
import all SphereSixComplex.TriangleGroup.Representation

/-!
# From an equivariant modular parameter to the triangle uniformization

The source action and its special points are explicit.  This file shows that it is enough to
construct a holomorphic modular parameter satisfying the two generator laws: the laws extend to
the full free product, and the normalized modular invariant then supplies the quotient coordinate
required by `TriangleUniformization`.
-/

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

/-- The remaining additive period data on a holomorphic Fuchsian modular parameter, before the
global imaginary shift imposing nondegeneracy. -/
public structure FuchsianPrePeriodData extends FuchsianModularParameter where
  tau_at_zOne : tau fuchsianOneFixedPoint = ellipticThreeParameter
  tau_at_zTwo : tau fuchsianTwoFixedPoint = UpperHalfPlane.I
  mu : UpperHalfPlane → ℂ
  beta : UpperHalfPlane → ℂ
  mu_holomorphic : MDiff mu
  beta_holomorphic : MDiff beta
  mu_transform_one : ∀ z,
    mu (fuchsianSourceAction g₁ • z) = (1 - mu z) / tau z
  mu_transform_two : ∀ z,
    mu (fuchsianSourceAction g₂ • z) = 1 + mu z / tau z
  beta_transform_one : ∀ z,
    beta (fuchsianSourceAction g₁ • z) =
      beta z + 2 - 6 * (1 - mu z) ^ 2 / tau z
  beta_transform_two : ∀ z,
    beta (fuchsianSourceAction g₂ • z) = beta z - 3 - 6 * mu z ^ 2 / tau z
  mu_transform_cusp : ∀ z, mu (fuchsianSourceAction g₀ • z) = mu z
  beta_transform_cusp : ∀ z, beta (fuchsianSourceAction g₀ • z) = beta z + 1
  mu_cusp_bounded : BoundedOn mu fuchsianCuspRegion
  beta_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ beta z + (tau z : ℂ)) fuchsianCuspRegion

namespace FuchsianPrePeriodData

variable (D : FuchsianPrePeriodData)

/-- The explicit Fuchsian analytic data satisfies the generic pre-period interface. -/
@[expose] public noncomputable def toPrePeriodFunctions :
    PrePeriodFunctions D.toFuchsianModularParameter.toTriangleUniformization where
  tau := D.tau
  mu := D.mu
  beta := D.beta
  tau_holomorphic := D.tau_holomorphic
  mu_holomorphic := D.mu_holomorphic
  beta_holomorphic := D.beta_holomorphic
  modular_equation z := by
    change normalizedJ (D.tau z) = 1728 * (normalizedJ (D.tau z) / 1728)
    ring
  tau_at_zOne := D.tau_at_zOne
  tau_at_zTwo := D.tau_at_zTwo
  transform_one z := by
    apply Parameters.ext
    · simpa only [periodValues, transformOne.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using
        (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) (D.transform_one z)
          |>.trans (rhoTauReal_g1_smul (D.tau z)))
    · simpa only [periodValues, transformOne.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.mu_transform_one z
    · simpa only [periodValues, transformOne.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.beta_transform_one z
  transform_two z := by
    apply Parameters.ext
    · simpa only [periodValues, transformTwo.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using
        (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) (D.transform_two z)
          |>.trans (rhoTauReal_g2_smul (D.tau z)))
    · simpa only [periodValues, transformTwo.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.mu_transform_two z
    · simpa only [periodValues, transformTwo.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.beta_transform_two z
  transform_cusp z := by
    apply Parameters.ext
    · simpa only [periodValues, transformCusp.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using
        (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
          (D.toFuchsianModularParameter.equivariant g₀ z)
          |>.trans (rhoTauReal_g0_smul (D.tau z)))
    · simpa only [periodValues, transformCusp.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.mu_transform_cusp z
    · simpa only [periodValues, transformCusp.eq_def,
        FuchsianModularParameter.toTriangleUniformization] using D.beta_transform_cusp z
  mu_cusp_bounded := D.mu_cusp_bounded
  beta_add_tau_cusp_bounded := D.beta_add_tau_cusp_bounded

/-- The analytic period-function theorem is reduced to explicit equivariant `tau`, `mu`, `beta`
data and a compact core for the concrete Fuchsian quotient. -/
public theorem theorem3_4Existence (K : QuotientCompactCore
    D.toFuchsianModularParameter.toTriangleUniformization) :
    Theorem3_4Existence D.toFuchsianModularParameter.toTriangleUniformization :=
  show Nonempty (PeriodFunctions D.toFuchsianModularParameter.toTriangleUniformization) from
    D.toPrePeriodFunctions.exists_shiftedPeriodFunctions K

end FuchsianPrePeriodData

end SphereSixComplex.Periods
