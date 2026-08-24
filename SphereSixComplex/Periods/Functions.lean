module

public import SphereSixComplex.Periods.Invariant
public import SphereSixComplex.TriangleGroup.ModularParameter
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.Discriminant
import all SphereSixComplex.Periods.Matrix
import Mathlib.Geometry.Manifold.Notation

/-!
# Analytic period functions

An interface for Definition 3.1 and the existence assertion of Theorem 3.4.  The normalized
modular function is constructed from the level-one Eisenstein series and discriminant already in
Mathlib.  The paper-specific uniformization and the two additive torsor problems are retained as
explicit data rather than assumed globally.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

@[expose] public noncomputable def normalizedJ (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

public theorem discriminant_mdifferentiable :
    MDiff (ModularForm.discriminant : UpperHalfPlane → ℂ) := by
  change MDiff (fun z : UpperHalfPlane ↦ ModularForm.eta z ^ 24)
  exact (show MDiff (fun z : UpperHalfPlane ↦ ModularForm.eta z) by
    intro z
    exact MDifferentiableAt.comp z
      (DifferentiableAt.mdifferentiableAt
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos))
      z.mdifferentiable_coe).pow 24

public theorem normalizedJ_mdifferentiable : MDiff normalizedJ := by
  exact ((ModularFormClass.holo ModularForm.E₄).pow 3).div discriminant_mdifferentiable
    ModularForm.discriminant_ne_zero

public theorem normalizedJ_modular_invariant (g : ModularMatrix) (z : UpperHalfPlane) :
    normalizedJ (Matrix.SpecialLinearGroup.mapGL ℝ g • z) = normalizedJ z := by
  have hE := congrFun (ModularForm.E₄.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ g) ⟨g, rfl⟩) z
  have hD := congrFun (CuspForm.discriminant.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ g) ⟨g, rfl⟩) z
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE hD
  have hd := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  field_simp [hd] at hE hD
  simp only [normalizedJ]
  rw [hE, hD]
  field_simp [ModularForm.discriminant_ne_zero z, hd]

@[expose] public def ellipticThreeParameter : UpperHalfPlane :=
  ⟨(UpperHalfPlane.ρ : ℂ) + 1, by simpa using UpperHalfPlane.ρ.im_pos⟩

public structure TriangleUniformization where
  sourceAction : Delta →* GL (Fin 2) ℝ
  source_det_pos : ∀ g, 0 < (sourceAction g).det.val
  coordinate : UpperHalfPlane → ℂ
  coordinate_holomorphic : MDiff coordinate
  coordinate_invariant : ∀ g z, coordinate (sourceAction g • z) = coordinate z
  zOne : UpperHalfPlane
  zTwo : UpperHalfPlane
  zOne_fixed : sourceAction g₁ • zOne = zOne
  zTwo_fixed : sourceAction g₂ • zTwo = zTwo
  cuspRegion : Set UpperHalfPlane
  cuspRegion_nonempty : cuspRegion.Nonempty
  cuspRegion_invariant : ∀ z, sourceAction g₀ • z ∈ cuspRegion ↔ z ∈ cuspRegion

/-- The explicit modular action and normalized modular coordinate provide the algebraic and local
fixed-point data required by `TriangleUniformization`.  Its cusp region is initially taken to be the
whole upper half-plane; later analytic estimates may replace it by a smaller invariant region. -/
public noncomputable def canonicalTriangleUniformization : TriangleUniformization where
  sourceAction := rhoTauReal
  source_det_pos g := by
    rw [show (rhoTauReal g).det = 1 by
      exact Matrix.SpecialLinearGroup.det_mapGL (S := ℝ) (rhoTau g)]
    norm_num
  coordinate z := normalizedJ z / 1728
  coordinate_holomorphic :=
    normalizedJ_mdifferentiable.div mdifferentiable_const (by norm_num)
  coordinate_invariant g z := by
    rw [show rhoTauReal g = Matrix.SpecialLinearGroup.mapGL ℝ (rhoTau g) by
      simp [rhoTauReal, modularToReal]]
    rw [normalizedJ_modular_invariant]
  zOne := ellipticThreeParameter
  zTwo := UpperHalfPlane.I
  zOne_fixed := by
    apply UpperHalfPlane.coe_injective
    rw [rhoTauReal_g1_smul]
    have hz : (ellipticThreeParameter : ℂ) ≠ 0 := ellipticThreeParameter.ne_zero
    field_simp [hz]
    rw [show (ellipticThreeParameter : ℂ) = UpperHalfPlane.ρ + 1 by rfl]
    rw [show ((UpperHalfPlane.ρ : ℂ) + 1) ^ 2 =
        (UpperHalfPlane.ρ : ℂ) ^ 2 + 2 * UpperHalfPlane.ρ + 1 by ring]
    rw [UpperHalfPlane.ρ_sq]
    ring
  zTwo_fixed := by
    apply UpperHalfPlane.coe_injective
    rw [rhoTauReal_g2_smul]
    norm_num [UpperHalfPlane.I]
  cuspRegion := Set.univ
  cuspRegion_nonempty := Set.univ_nonempty
  cuspRegion_invariant _ := by simp

@[expose] public def periodValues (tau : UpperHalfPlane → UpperHalfPlane)
    (mu beta : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : Parameters where
  tau := tau z
  mu := mu z
  beta := beta z

public def BoundedOn (f : UpperHalfPlane → ℂ) (s : Set UpperHalfPlane) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ s, ‖f z‖ ≤ C

public structure PeriodFunctions (U : TriangleUniformization) where
  tau : UpperHalfPlane → UpperHalfPlane
  mu : UpperHalfPlane → ℂ
  beta : UpperHalfPlane → ℂ
  tau_holomorphic : MDiff tau
  mu_holomorphic : MDiff mu
  beta_holomorphic : MDiff beta
  modular_equation : ∀ z, normalizedJ (tau z) = 1728 * U.coordinate z
  tau_at_zOne : tau U.zOne = ellipticThreeParameter
  tau_at_zTwo : tau U.zTwo = UpperHalfPlane.I
  transform_one : ∀ z,
    periodValues tau mu beta (U.sourceAction g₁ • z) =
      transformOne (periodValues tau mu beta z)
  transform_two : ∀ z,
    periodValues tau mu beta (U.sourceAction g₂ • z) =
      transformTwo (periodValues tau mu beta z)
  transform_cusp : ∀ z,
    periodValues tau mu beta (U.sourceAction g₀ • z) =
      transformCusp (periodValues tau mu beta z)
  mu_cusp_bounded : BoundedOn mu U.cuspRegion
  beta_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ beta z + (tau z : ℂ)) U.cuspRegion
  setup_inequalities : ∀ z, SetupInequalities (periodValues tau mu beta z)

namespace PeriodFunctions

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem tau_transform_one (z : UpperHalfPlane) :
    ((F.tau (U.sourceAction g₁ • z) : UpperHalfPlane) : ℂ) =
      ((F.tau z : ℂ) - 1) / F.tau z := by
  simpa only [periodValues, transformOne.eq_def] using
    congrArg Parameters.tau (F.transform_one z)

public theorem tau_transform_two (z : UpperHalfPlane) :
    ((F.tau (U.sourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
      -1 / F.tau z := by
  simpa only [periodValues, transformTwo.eq_def] using
    congrArg Parameters.tau (F.transform_two z)

public theorem mu_transform_one (z : UpperHalfPlane) :
    F.mu (U.sourceAction g₁ • z) = (1 - F.mu z) / F.tau z := by
  simpa only [periodValues, transformOne.eq_def] using
    congrArg Parameters.mu (F.transform_one z)

public theorem mu_transform_two (z : UpperHalfPlane) :
    F.mu (U.sourceAction g₂ • z) = 1 + F.mu z / F.tau z := by
  simpa only [periodValues, transformTwo.eq_def] using
    congrArg Parameters.mu (F.transform_two z)

public theorem beta_transform_one (z : UpperHalfPlane) :
    F.beta (U.sourceAction g₁ • z) =
      F.beta z + 2 - 6 * (1 - F.mu z) ^ 2 / F.tau z := by
  simpa only [periodValues, transformOne.eq_def] using
    congrArg Parameters.beta (F.transform_one z)

public theorem beta_transform_two (z : UpperHalfPlane) :
    F.beta (U.sourceAction g₂ • z) =
      F.beta z - 3 - 6 * F.mu z ^ 2 / F.tau z := by
  simpa only [periodValues, transformTwo.eq_def] using
    congrArg Parameters.beta (F.transform_two z)

public theorem tau_transform_cusp (z : UpperHalfPlane) :
    ((F.tau (U.sourceAction g₀ • z) : UpperHalfPlane) : ℂ) = F.tau z - 1 := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.tau (F.transform_cusp z)

public theorem tau_equivariant_g1 (z : UpperHalfPlane) :
    F.tau (U.sourceAction g₁ • z) = rhoTauReal g₁ • F.tau z := by
  apply UpperHalfPlane.ext
  rw [tau_transform_one, rhoTauReal_g1_smul]

public theorem tau_equivariant_g2 (z : UpperHalfPlane) :
    F.tau (U.sourceAction g₂ • z) = rhoTauReal g₂ • F.tau z := by
  apply UpperHalfPlane.ext
  rw [tau_transform_two, rhoTauReal_g2_smul]

public theorem tau_equivariant_g0 (z : UpperHalfPlane) :
    F.tau (U.sourceAction g₀ • z) = rhoTauReal g₀ • F.tau z := by
  apply UpperHalfPlane.ext
  rw [tau_transform_cusp, rhoTauReal_g0_smul]

public theorem mu_transform_cusp (z : UpperHalfPlane) :
    F.mu (U.sourceAction g₀ • z) = F.mu z := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.mu (F.transform_cusp z)

public theorem beta_transform_cusp (z : UpperHalfPlane) :
    F.beta (U.sourceAction g₀ • z) = F.beta z + 1 := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.beta (F.transform_cusp z)

public theorem qParam_transform_cusp (z : UpperHalfPlane) :
    Function.Periodic.qParam 1 (F.tau (U.sourceAction g₀ • z)) =
      Function.Periodic.qParam 1 (F.tau z) := by
  rw [tau_transform_cusp]
  simpa [Function.Periodic.qParam, mul_sub] using
    Complex.exp_periodic.sub_eq (2 * Real.pi * Complex.I * (F.tau z : ℂ))

public theorem periodRealLinear_injective (z : UpperHalfPlane) :
    Function.Injective (Periods.periodRealLinear (periodValues F.tau F.mu F.beta z)) :=
  Periods.periodRealLinear_injective _ (F.setup_inequalities z)

end PeriodFunctions

/-- The exact analytic existence assertion remaining from Theorem 3.4 for a fixed
triangle-orbifold uniformization. -/
public def Theorem3_4Existence (U : TriangleUniformization) : Prop :=
  Nonempty (PeriodFunctions U)

end SphereSixComplex.Periods
