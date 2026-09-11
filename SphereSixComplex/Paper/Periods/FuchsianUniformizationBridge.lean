module

public import SphereSixComplex.Paper.Periods.SchurCompactness
public import SphereSixComplex.Prerequisites.Periods.FuchsianModularParameter
import all SphereSixComplex.Prerequisites.Periods.FuchsianModularParameter
import all SphereSixComplex.Paper.Periods.Functions
import all SphereSixComplex.Paper.Periods.Matrix
import all SphereSixComplex.Paper.TriangleGroup.Representation

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
    Nonempty (PeriodFunctions D.toFuchsianModularParameter.toTriangleUniformization) :=
  show Nonempty (PeriodFunctions D.toFuchsianModularParameter.toTriangleUniformization) from
    D.toPrePeriodFunctions.exists_shiftedPeriodFunctions K

end FuchsianPrePeriodData

end SphereSixComplex.Periods
