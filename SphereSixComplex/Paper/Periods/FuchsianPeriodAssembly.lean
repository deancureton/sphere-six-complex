module

public import SphereSixComplex.Paper.Periods.FuchsianModularLift
public import SphereSixComplex.Paper.Periods.SchurCompactness
public import SphereSixComplex.Paper.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.Paper.TriangleGroup.FuchsianTriangleCover
import all SphereSixComplex.Paper.Periods.Functions
import all SphereSixComplex.Paper.Periods.FuchsianUniformizationBridge

/-!
# Assembly of global Fuchsian period functions

Global holomorphic additive coordinates with their affine transformation laws and cusp bounds
combine with the fixed modular lift. The doubled fundamental region supplies the compact core
for the final Schur shift imposing nondegeneracy.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : FuchsianModularLift)

/-- Global additive period coordinates for the fixed modular lift. -/
public structure FuchsianPeriodData where
  mu : UpperHalfPlane → ℂ
  beta : UpperHalfPlane → ℂ
  mu_holomorphic : MDiff mu
  beta_holomorphic : MDiff beta
  mu_transform_one : ∀ z, mu (fuchsianSourceAction g₁ • z) =
    (1 - mu z) / E.modularParameter.tau z
  mu_transform_two : ∀ z, mu (fuchsianSourceAction g₂ • z) =
    1 + mu z / E.modularParameter.tau z
  beta_transform_one : ∀ z, beta (fuchsianSourceAction g₁ • z) =
    beta z + 2 - 6 * (1 - mu z) ^ 2 / E.modularParameter.tau z
  beta_transform_two : ∀ z, beta (fuchsianSourceAction g₂ • z) =
    beta z - 3 - 6 * mu z ^ 2 / E.modularParameter.tau z
  mu_cusp_bounded : BoundedOn mu fuchsianCuspRegion
  beta_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ beta z + E.modularParameter.tau z) fuchsianCuspRegion

variable (D : FuchsianPeriodData E)

private theorem tau_transform_two_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
      -1 / E.modularParameter.tau z := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₂ z)).trans (rhoTauReal_g₂_smul _)

/-- The two elliptic affine laws make `mu` invariant under the parabolic product. -/
public theorem FuchsianPeriodData.mu_transform_product (z : UpperHalfPlane) :
    D.mu
        (fuchsianSourceAction (g₁ * g₂) • z) =
      D.mu z := by
  have hOne := D.mu_transform_one
  have hTwo := D.mu_transform_two
  rw [map_mul, mul_smul, hOne, hTwo, tau_transform_two_coe E]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- Invariance under the parabolic product gives invariance under its inverse `g₀`. -/
public theorem FuchsianPeriodData.mu_transform_cusp (z : UpperHalfPlane) :
    D.mu (fuchsianSourceAction g₀ • z) =
      D.mu z := by
  have h := FuchsianPeriodData.mu_transform_product E D
    (fuchsianSourceAction g₀ • z)
  rw [← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀, map_one, one_smul] at h
  exact h.symm

/-- The two elliptic affine laws make `beta` decrease by one under the parabolic product. -/
public theorem FuchsianPeriodData.beta_transform_product (z : UpperHalfPlane) :
    D.beta (fuchsianSourceAction (g₁ * g₂) • z) =
      D.beta z - 1 := by
  have hBetaOne := D.beta_transform_one
  have hBetaTwo := D.beta_transform_two
  have hMuTwo := D.mu_transform_two
  rw [map_mul, mul_smul, hBetaOne, hBetaTwo, hMuTwo, tau_transform_two_coe E]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The inverse parabolic generator increases `beta` by one. -/
public theorem FuchsianPeriodData.beta_transform_cusp (z : UpperHalfPlane) :
    D.beta (fuchsianSourceAction g₀ • z) =
      D.beta z + 1 := by
  have h := FuchsianPeriodData.beta_transform_product E D
    (fuchsianSourceAction g₀ • z)
  rw [← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀, map_one, one_smul] at h
  linear_combination -h

/-- The global additive coordinates assemble into the Fuchsian pre-period data. -/
@[expose] public noncomputable def assembledFuchsianPrePeriodData : FuchsianPrePeriodData where
  toFuchsianModularParameter := E.modularParameter
  tau_at_zOne := E.tau_at_one
  tau_at_zTwo := E.tau_at_two
  mu := D.mu
  beta := D.beta
  mu_holomorphic := D.mu_holomorphic
  beta_holomorphic := D.beta_holomorphic
  mu_transform_one := D.mu_transform_one
  mu_transform_two := D.mu_transform_two
  beta_transform_one := D.beta_transform_one
  beta_transform_two := D.beta_transform_two
  mu_transform_cusp := FuchsianPeriodData.mu_transform_cusp E D
  beta_transform_cusp := FuchsianPeriodData.beta_transform_cusp E D
  mu_cusp_bounded := D.mu_cusp_bounded
  beta_add_tau_cusp_bounded := D.beta_add_tau_cusp_bounded


/-- The global additive period data produces nondegenerate period functions for the explicit
Fuchsian uniformization. -/
public theorem exists_assembledFuchsianPeriodFunctions :
    (D : FuchsianPeriodData E) →
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) :=
  fun D ↦ (assembledFuchsianPrePeriodData E D).toPrePeriodFunctions.exists_shiftedPeriodFunctions
    (orientedFuchsianQuotientCompactCore E.modularParameter)

/-- A selected nondegenerate period family produced by the compact-core Schur shift. -/
@[expose] public noncomputable def assembledFuchsianPeriodFunctions
    (D : FuchsianPeriodData E) :
    PeriodFunctions E.modularParameter.toTriangleUniformization := by
  exact Classical.choice (exists_assembledFuchsianPeriodFunctions E D)


end SphereSixComplex.Periods
