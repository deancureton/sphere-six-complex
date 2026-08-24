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

/-- The explicit modular action, normalized modular coordinate, fixed points, and invariant
horodisc provide the data required by `TriangleUniformization`. -/
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
  cuspRegion := {z | 1 ≤ z.im}
  cuspRegion_nonempty := by
    refine ⟨UpperHalfPlane.I, ?_⟩
    norm_num [UpperHalfPlane.I]
  cuspRegion_invariant z := by
    change 1 ≤ (rhoTauReal g₀ • z).im ↔ 1 ≤ z.im
    rw [rhoTauReal_g₀]
    have h := congrArg Complex.im (rhoTauReal_g0_smul z)
    norm_num at h
    rw [h]

@[expose] public def periodValues (tau : UpperHalfPlane → UpperHalfPlane)
    (mu beta : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : Parameters where
  tau := tau z
  mu := mu z
  beta := beta z

public def BoundedOn (f : UpperHalfPlane → ℂ) (s : Set UpperHalfPlane) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ s, ‖f z‖ ≤ C

/-- Subtracting a constant preserves boundedness on a set. -/
public theorem BoundedOn.sub_const {f : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (h : BoundedOn f s) (c : ℂ) : BoundedOn (fun z ↦ f z - c) s := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C + ‖c‖, add_nonneg hC (norm_nonneg c), ?_⟩
  intro z hz
  exact (norm_sub_le (f z) c).trans (add_le_add (hbound z hz) le_rfl)

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

/-- The order-three fixed point forces the corresponding affine period value. -/
public theorem mu_at_zOne (F : PeriodFunctions U) :
    F.mu U.zOne = 1 / (1 + (F.tau U.zOne : ℂ)) := by
  have h := F.mu_transform_one U.zOne
  rw [U.zOne_fixed] at h
  have ht : (F.tau U.zOne : ℂ) ≠ 0 := (F.tau U.zOne).ne_zero
  have hden : 1 + (F.tau U.zOne : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    rw [Complex.add_im] at him
    norm_num at him
    exact (F.tau U.zOne).im_pos.ne' him
  rw [eq_div_iff hden]
  field_simp [ht] at h
  linear_combination h

/-- The order-four fixed point forces the corresponding affine period value. -/
public theorem mu_at_zTwo (F : PeriodFunctions U) :
    F.mu U.zTwo = (F.tau U.zTwo : ℂ) / ((F.tau U.zTwo : ℂ) - 1) := by
  have h := F.mu_transform_two U.zTwo
  rw [U.zTwo_fixed] at h
  have ht : (F.tau U.zTwo : ℂ) ≠ 0 := (F.tau U.zTwo).ne_zero
  have ht1 : (F.tau U.zTwo : ℂ) - 1 ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.sub_im] at him
    norm_num at him
    exact (F.tau U.zTwo).im_pos.ne' him
  rw [eq_div_iff ht1]
  field_simp [ht] at h
  linear_combination h

/-- At the order-three fixed point the additive term in the `β` law vanishes. -/
public theorem beta_cocycle_at_zOne (F : PeriodFunctions U) :
    2 - 6 * (1 - F.mu U.zOne) ^ 2 / F.tau U.zOne = 0 := by
  have h := F.beta_transform_one U.zOne
  rw [U.zOne_fixed] at h
  linear_combination -h

/-- At the order-four fixed point the additive term in the `β` law vanishes. -/
public theorem beta_cocycle_at_zTwo (F : PeriodFunctions U) :
    -3 - 6 * F.mu U.zTwo ^ 2 / F.tau U.zTwo = 0 := by
  have h := F.beta_transform_two U.zTwo
  rw [U.zTwo_fixed] at h
  linear_combination -h

end PeriodFunctions

/-- The exact analytic existence assertion remaining from Theorem 3.4 for a fixed
triangle-orbifold uniformization. -/
public def Theorem3_4Existence (U : TriangleUniformization) : Prop :=
  Nonempty (PeriodFunctions U)

@[ext]
public theorem Parameters.ext {x y : Parameters} (htau : x.tau = y.tau)
    (hmu : x.mu = y.mu) (hbeta : x.beta = y.beta) : x = y := by
  cases x
  cases y
  simp_all

/-- Holomorphic and equivariant `μ, β` data before imposing period-lattice nondegeneracy. -/
public structure CanonicalMuBetaEquivariantData where
  /-- The additive period function `μ`. -/
  mu : UpperHalfPlane → ℂ
  /-- The additive period function `β`. -/
  beta : UpperHalfPlane → ℂ
  /-- Holomorphy of `μ`. -/
  mu_holomorphic : MDiff mu
  /-- Holomorphy of `β`. -/
  beta_holomorphic : MDiff beta
  /-- The order-three transformation law for `μ`. -/
  mu_transform_one : ∀ z,
    mu (rhoTauReal g₁ • z) = (1 - mu z) / z
  /-- The order-four transformation law for `μ`. -/
  mu_transform_two : ∀ z,
    mu (rhoTauReal g₂ • z) = 1 + mu z / z
  /-- The order-three transformation law for `β`. -/
  beta_transform_one : ∀ z,
    beta (rhoTauReal g₁ • z) = beta z + 2 - 6 * (1 - mu z) ^ 2 / z
  /-- The order-four transformation law for `β`. -/
  beta_transform_two : ∀ z,
    beta (rhoTauReal g₂ • z) = beta z - 3 - 6 * mu z ^ 2 / z
  /-- Cusp invariance of `μ`. -/
  mu_transform_cusp : ∀ z, mu (rhoTauReal g₀ • z) = mu z
  /-- Affine cusp transformation of `β`. -/
  beta_transform_cusp : ∀ z, beta (rhoTauReal g₀ • z) = beta z + 1
  /-- Boundedness of `μ` on the distinguished horodisc. -/
  mu_cusp_bounded : BoundedOn mu canonicalTriangleUniformization.cuspRegion
  /-- Boundedness of `β + τ` on the distinguished horodisc. -/
  beta_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ beta z + (z : ℂ)) canonicalTriangleUniformization.cuspRegion

/-- After fixing the explicit modular uniformization, the remaining analytic problem consists only
of the two additive period functions `μ` and `β`. -/
public structure CanonicalMuBetaData extends CanonicalMuBetaEquivariantData where
  /-- Pointwise nondegeneracy of the resulting period lattice. -/
  setup_inequalities : ∀ z, SetupInequalities (periodValues id mu beta z)

/-- The equivariant `μ, β` laws assemble into the order-three parameter transformation. -/
public theorem CanonicalMuBetaEquivariantData.periodValues_transform_one
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    periodValues id D.mu D.beta (rhoTauReal g₁ • z) =
      transformOne (periodValues id D.mu D.beta z) := by
  ext
  · exact rhoTauReal_g1_smul z
  · exact D.mu_transform_one z
  · exact D.beta_transform_one z

/-- The equivariant `μ, β` laws assemble into the order-four parameter transformation. -/
public theorem CanonicalMuBetaEquivariantData.periodValues_transform_two
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    periodValues id D.mu D.beta (rhoTauReal g₂ • z) =
      transformTwo (periodValues id D.mu D.beta z) := by
  ext
  · exact rhoTauReal_g2_smul z
  · exact D.mu_transform_two z
  · exact D.beta_transform_two z

/-- The equivariant `μ, β` laws assemble into the cusp parameter transformation. -/
public theorem CanonicalMuBetaEquivariantData.periodValues_transform_cusp
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    periodValues id D.mu D.beta (rhoTauReal g₀ • z) =
      transformCusp (periodValues id D.mu D.beta z) := by
  ext
  · exact rhoTauReal_g0_smul z
  · exact D.mu_transform_cusp z
  · exact D.beta_transform_cusp z

/-- The Schur quantity is invariant under the order-three generator. -/
public theorem CanonicalMuBetaEquivariantData.schurQuantity_transform_one
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    schurQuantity (periodValues id D.mu D.beta (rhoTauReal g₁ • z)) =
      schurQuantity (periodValues id D.mu D.beta z) := by
  rw [D.periodValues_transform_one]
  apply schurQuantity_transformOne
  simpa [periodValues] using z.im_pos.ne'

/-- The Schur quantity is invariant under the order-four generator. -/
public theorem CanonicalMuBetaEquivariantData.schurQuantity_transform_two
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    schurQuantity (periodValues id D.mu D.beta (rhoTauReal g₂ • z)) =
      schurQuantity (periodValues id D.mu D.beta z) := by
  rw [D.periodValues_transform_two]
  apply schurQuantity_transformTwo
  simpa [periodValues] using z.im_pos.ne'

/-- The Schur quantity is invariant under the cusp generator. -/
public theorem CanonicalMuBetaEquivariantData.schurQuantity_transform_cusp
    (D : CanonicalMuBetaEquivariantData) (z : UpperHalfPlane) :
    schurQuantity (periodValues id D.mu D.beta (rhoTauReal g₀ • z)) =
      schurQuantity (periodValues id D.mu D.beta z) := by
  rw [D.periodValues_transform_cusp, schurQuantity_transformCusp]

/-- The analytic data before shifting `β` by a sufficiently negative imaginary constant. -/
public structure CanonicalMuBetaPreData extends CanonicalMuBetaEquivariantData where
  /-- The invariant Schur quantity is bounded above on the quotient curve. -/
  schur_bounded_above :
    ∃ M : ℝ, ∀ z, schurQuantity (periodValues id mu beta z) ≤ M

/-- Shift `β` by the negative imaginary constant `-c i`; all analytic and equivariance laws are
unchanged. -/
public noncomputable def CanonicalMuBetaEquivariantData.shiftBeta
    (D : CanonicalMuBetaEquivariantData) (c : ℝ) : CanonicalMuBetaEquivariantData where
  mu := D.mu
  beta z := D.beta z - c * Complex.I
  mu_holomorphic := D.mu_holomorphic
  beta_holomorphic := D.beta_holomorphic.sub mdifferentiable_const
  mu_transform_one := D.mu_transform_one
  mu_transform_two := D.mu_transform_two
  beta_transform_one z := by rw [D.beta_transform_one]; ring
  beta_transform_two z := by rw [D.beta_transform_two]; ring
  mu_transform_cusp := D.mu_transform_cusp
  beta_transform_cusp z := by rw [D.beta_transform_cusp]; ring
  mu_cusp_bounded := D.mu_cusp_bounded
  beta_add_tau_cusp_bounded := by
    convert D.beta_add_tau_cusp_bounded.sub_const (c * Complex.I) using 1
    funext z
    ring

/-- A global upper bound for the invariant Schur quantity can always be converted into strict
period-lattice nondegeneracy by shifting `β` downward by a constant. -/
public theorem CanonicalMuBetaPreData.exists_shiftedData (D : CanonicalMuBetaPreData) :
    Nonempty CanonicalMuBetaData := by
  obtain ⟨M, hM⟩ := D.schur_bounded_above
  let c : ℝ := max M 0 + 1
  let E := D.toCanonicalMuBetaEquivariantData.shiftBeta c
  refine ⟨{
    toCanonicalMuBetaEquivariantData := E
    setup_inequalities := ?_
  }⟩
  intro z
  constructor
  · exact z.im_pos
  · change schurQuantity (periodValues id E.mu E.beta z) < 0
    have hshift : schurQuantity (periodValues id E.mu E.beta z) =
        schurQuantity (periodValues id D.mu D.beta z) - c := by
      simp [E, CanonicalMuBetaEquivariantData.shiftBeta, schurQuantity, periodValues,
        Complex.mul_im]
      ring
    rw [hshift]
    have hc : M - c < 0 := by
      dsimp [c]
      have := le_max_left M 0
      linarith
    exact lt_of_le_of_lt (sub_le_sub_right (hM z) c) hc

/-- The identity upper-half-plane map supplies the `τ` component of Theorem 3.4 for the canonical
uniformization. -/
public noncomputable def CanonicalMuBetaData.toPeriodFunctions
    (D : CanonicalMuBetaData) : PeriodFunctions canonicalTriangleUniformization where
  tau := id
  mu := D.mu
  beta := D.beta
  tau_holomorphic := mdifferentiable_id
  mu_holomorphic := D.mu_holomorphic
  beta_holomorphic := D.beta_holomorphic
  modular_equation z := by
    change normalizedJ z = 1728 * (normalizedJ z / 1728)
    field_simp
  tau_at_zOne := rfl
  tau_at_zTwo := rfl
  transform_one z := by
    ext
    · exact rhoTauReal_g1_smul z
    · exact D.mu_transform_one z
    · exact D.beta_transform_one z
  transform_two z := by
    ext
    · exact rhoTauReal_g2_smul z
    · exact D.mu_transform_two z
    · exact D.beta_transform_two z
  transform_cusp z := by
    ext
    · exact rhoTauReal_g0_smul z
    · exact D.mu_transform_cusp z
    · exact D.beta_transform_cusp z
  mu_cusp_bounded := D.mu_cusp_bounded
  beta_add_tau_cusp_bounded := D.beta_add_tau_cusp_bounded
  setup_inequalities := D.setup_inequalities

/-- Solving the two remaining additive functional equations proves the canonical case of Theorem
3.4. -/
public theorem theorem3_4Existence_canonical_of_muBeta (D : CanonicalMuBetaData) :
    Theorem3_4Existence canonicalTriangleUniformization :=
  ⟨D.toPeriodFunctions⟩

/-- The pre-data form of the paper's torsor argument implies the canonical Theorem 3.4 existence
statement after the final imaginary shift. -/
public theorem theorem3_4Existence_canonical_of_preData (D : CanonicalMuBetaPreData) :
    Theorem3_4Existence canonicalTriangleUniformization := by
  obtain ⟨E⟩ := D.exists_shiftedData
  exact theorem3_4Existence_canonical_of_muBeta E

end SphereSixComplex.Periods
