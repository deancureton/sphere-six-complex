module

public import SphereSixComplex.Periods.FuchsianBetaTorsor
public import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# Assembly of the explicit Fuchsian period functions

This file combines the established modular parameter with exact local Cech data for the `mu` and
`beta` torsors.  The two descent theorems produce global pre-period data.  The doubled Fuchsian
fundamental region then supplies the compact core needed for the final Schur shift.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : EstablishedFuchsianModularParameter)

/-- The global `mu` selected from exact local `O(-1)` torsor data. -/
@[expose] public noncomputable def descendedFuchsianMu
    (D : MuTorsorCechLocalData E) : UpperHalfPlane → ℂ :=
  Classical.choose (exists_globalFuchsianMu E D)

public theorem descendedFuchsianMu_spec (D : MuTorsorCechLocalData E) :
    MDiff (descendedFuchsianMu E D) ∧
      (∀ z, descendedFuchsianMu E D (fuchsianSourceAction g₁ • z) =
        (1 - descendedFuchsianMu E D z) / E.modularParameter.tau z) ∧
      (∀ z, descendedFuchsianMu E D (fuchsianSourceAction g₂ • z) =
        1 + descendedFuchsianMu E D z / E.modularParameter.tau z) ∧
      BoundedOn (descendedFuchsianMu E D) fuchsianCuspRegion :=
  Classical.choose_spec (exists_globalFuchsianMu E D)

/-- The exact remaining local analytic input for both additive period coordinates. -/
public structure FuchsianPeriodLocalData where
  /-- Exact local descent data for the `O(-1)` affine `mu` torsor. -/
  muLocal : MuTorsorCechLocalData E
  /-- Exact local descent data for the `O` affine `beta` torsor, after the descended `mu` has
  been selected. -/
  betaLocal : BetaTorsorCechLocalData E (descendedFuchsianMu E muLocal)

variable (D : FuchsianPeriodLocalData E)

/-- The global `beta` selected from exact local structure-sheaf torsor data. -/
@[expose] public noncomputable def descendedFuchsianBeta : UpperHalfPlane → ℂ :=
  Classical.choose (exists_globalFuchsianBeta E D.betaLocal)

public theorem descendedFuchsianBeta_spec :
    MDiff (descendedFuchsianBeta E D) ∧
      (∀ z, descendedFuchsianBeta E D (fuchsianSourceAction g₁ • z) =
        descendedFuchsianBeta E D z + 2 -
          6 * (1 - descendedFuchsianMu E D.muLocal z) ^ 2 /
            E.modularParameter.tau z) ∧
      (∀ z, descendedFuchsianBeta E D (fuchsianSourceAction g₂ • z) =
        descendedFuchsianBeta E D z - 3 -
          6 * descendedFuchsianMu E D.muLocal z ^ 2 / E.modularParameter.tau z) ∧
      BoundedOn
        (fun z ↦ descendedFuchsianBeta E D z + E.modularParameter.tau z)
        fuchsianCuspRegion :=
  Classical.choose_spec (exists_globalFuchsianBeta E D.betaLocal)

private theorem tau_transform_two_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
      -1 / E.modularParameter.tau z := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₂ z)).trans (rhoTauReal_g₂_smul _)

/-- The two elliptic affine laws make `mu` invariant under the parabolic product. -/
public theorem descendedFuchsianMu_transform_product (z : UpperHalfPlane) :
    descendedFuchsianMu E D.muLocal
        (fuchsianSourceAction (g₁ * g₂) • z) =
      descendedFuchsianMu E D.muLocal z := by
  have hOne := (descendedFuchsianMu_spec E D.muLocal).2.1
  have hTwo := (descendedFuchsianMu_spec E D.muLocal).2.2.1
  rw [map_mul, mul_smul, hOne, hTwo, tau_transform_two_coe E]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- Invariance under the parabolic product gives invariance under its inverse `g₀`. -/
public theorem descendedFuchsianMu_transform_cusp (z : UpperHalfPlane) :
    descendedFuchsianMu E D.muLocal (fuchsianSourceAction g₀ • z) =
      descendedFuchsianMu E D.muLocal z := by
  have h := descendedFuchsianMu_transform_product E D
    (fuchsianSourceAction g₀ • z)
  rw [← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀, map_one, one_smul] at h
  exact h.symm

/-- The two elliptic affine laws make `beta` decrease by one under the parabolic product. -/
public theorem descendedFuchsianBeta_transform_product (z : UpperHalfPlane) :
    descendedFuchsianBeta E D (fuchsianSourceAction (g₁ * g₂) • z) =
      descendedFuchsianBeta E D z - 1 := by
  have hBetaOne := (descendedFuchsianBeta_spec E D).2.1
  have hBetaTwo := (descendedFuchsianBeta_spec E D).2.2.1
  have hMuTwo := (descendedFuchsianMu_spec E D.muLocal).2.2.1
  rw [map_mul, mul_smul, hBetaOne, hBetaTwo, hMuTwo, tau_transform_two_coe E]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The inverse parabolic generator increases `beta` by one. -/
public theorem descendedFuchsianBeta_transform_cusp (z : UpperHalfPlane) :
    descendedFuchsianBeta E D (fuchsianSourceAction g₀ • z) =
      descendedFuchsianBeta E D z + 1 := by
  have h := descendedFuchsianBeta_transform_product E D
    (fuchsianSourceAction g₀ • z)
  rw [← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀, map_one, one_smul] at h
  linear_combination -h

/-- The two exact local torsor descents assemble into the paper's full Fuchsian pre-period data. -/
@[expose] public noncomputable def assembledFuchsianPrePeriodData : FuchsianPrePeriodData where
  toFuchsianModularParameter := E.modularParameter
  tau_at_zOne := E.tau_at_one
  tau_at_zTwo := E.tau_at_two
  mu := descendedFuchsianMu E D.muLocal
  beta := descendedFuchsianBeta E D
  mu_holomorphic := (descendedFuchsianMu_spec E D.muLocal).1
  beta_holomorphic := (descendedFuchsianBeta_spec E D).1
  mu_transform_one := (descendedFuchsianMu_spec E D.muLocal).2.1
  mu_transform_two := (descendedFuchsianMu_spec E D.muLocal).2.2.1
  beta_transform_one := (descendedFuchsianBeta_spec E D).2.1
  beta_transform_two := (descendedFuchsianBeta_spec E D).2.2.1
  mu_transform_cusp := descendedFuchsianMu_transform_cusp E D
  beta_transform_cusp := descendedFuchsianBeta_transform_cusp E D
  mu_cusp_bounded := (descendedFuchsianMu_spec E D.muLocal).2.2.2
  beta_add_tau_cusp_bounded := (descendedFuchsianBeta_spec E D).2.2.2

@[simp]
public theorem assembledFuchsianPrePeriodData_tau (z : UpperHalfPlane) :
    (assembledFuchsianPrePeriodData E D).tau z = E.modularParameter.tau z :=
  rfl

@[simp]
public theorem assembledFuchsianPrePeriodData_mu (z : UpperHalfPlane) :
    (assembledFuchsianPrePeriodData E D).mu z = descendedFuchsianMu E D.muLocal z :=
  rfl

@[simp]
public theorem assembledFuchsianPrePeriodData_beta (z : UpperHalfPlane) :
    (assembledFuchsianPrePeriodData E D).beta z = descendedFuchsianBeta E D z :=
  rfl

public theorem assembledFuchsianPrePeriodData_mu_cusp_bounded :
    BoundedOn (assembledFuchsianPrePeriodData E D).mu fuchsianCuspRegion :=
  (assembledFuchsianPrePeriodData E D).mu_cusp_bounded

public theorem assembledFuchsianPrePeriodData_beta_add_tau_cusp_bounded :
    BoundedOn
      (fun z ↦ (assembledFuchsianPrePeriodData E D).beta z +
        (assembledFuchsianPrePeriodData E D).tau z)
      fuchsianCuspRegion :=
  (assembledFuchsianPrePeriodData E D).beta_add_tau_cusp_bounded

/-- The exact local torsor data produces actual nondegenerate period functions for the explicit
Fuchsian uniformization. -/
public theorem exists_assembledFuchsianPeriodFunctions :
    (D : FuchsianPeriodLocalData E) →
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) :=
  fun D ↦ (assembledFuchsianPrePeriodData E D).toPrePeriodFunctions.exists_shiftedPeriodFunctions
    (orientedFuchsianQuotientCompactCore E.modularParameter)

/-- A selected nondegenerate period family produced by the compact-core Schur shift. -/
@[expose] public noncomputable def assembledFuchsianPeriodFunctions
    (D : FuchsianPeriodLocalData E) :
    PeriodFunctions E.modularParameter.toTriangleUniformization := by
  exact Classical.choice (exists_assembledFuchsianPeriodFunctions E D)

public theorem assembledFuchsianPeriodFunctions_fields :
    MDiff (assembledFuchsianPeriodFunctions E D).tau ∧
      MDiff (assembledFuchsianPeriodFunctions E D).mu ∧
      MDiff (assembledFuchsianPeriodFunctions E D).beta ∧
      BoundedOn (assembledFuchsianPeriodFunctions E D).mu fuchsianCuspRegion ∧
      BoundedOn
        (fun z ↦ (assembledFuchsianPeriodFunctions E D).beta z +
          (assembledFuchsianPeriodFunctions E D).tau z)
        fuchsianCuspRegion :=
  ⟨(assembledFuchsianPeriodFunctions E D).tau_holomorphic,
    (assembledFuchsianPeriodFunctions E D).mu_holomorphic,
    (assembledFuchsianPeriodFunctions E D).beta_holomorphic,
    (assembledFuchsianPeriodFunctions E D).mu_cusp_bounded,
    (assembledFuchsianPeriodFunctions E D).beta_add_tau_cusp_bounded⟩

end SphereSixComplex.Periods
