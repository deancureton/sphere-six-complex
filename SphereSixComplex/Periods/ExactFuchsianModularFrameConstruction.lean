module

public import SphereSixComplex.Periods.ExactFuchsianModularFrameData
import SphereSixComplex.Periods.FuchsianCuspNormalization
import SphereSixComplex.Periods.ExactFuchsianCuspFrameGerm
import SphereSixComplex.Periods.ExactFuchsianEisensteinSixRoot
import SphereSixComplex.Periods.ExactFuchsianRamification
import all SphereSixComplex.Periods.FuchsianUniformizationBridge
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : EstablishedFuchsianModularParameter)

/-!
# Construction of the exact lifted modular frame

This module constructs the genuine lifted modular frame from the established Fuchsian
uniformization.  The global square root has forced elliptic generator signs; their product gives
the parabolic invariance needed by the completed-cusp germ.
-/

private lemma sourceCoordinate_analyticOrderAt_one :
    analyticOrderAt
        (E.sourceCoordinate.coordinate ∘ UpperHalfPlane.ofComplex)
        fuchsianOneFixedPoint = (3 : ℕ∞) := by
  simpa only [Function.comp_def, sub_zero, Nat.cast_ofNat] using
    E.sourceCoordinate.branch_one.analyticOrderAt
      E.sourceCoordinate.coordinate_holomorphic

private lemma sourceCoordinate_analyticOrderAt_two :
    analyticOrderAt
        (fun w : ℂ ↦ E.sourceCoordinate.coordinate
          (UpperHalfPlane.ofComplex w) - 1)
        fuchsianTwoFixedPoint = (4 : ℕ∞) := by
  exact E.sourceCoordinate.branch_two.analyticOrderAt
    E.sourceCoordinate.coordinate_holomorphic

private lemma sourceCoordinate_eq_liftedEisensteinFour_cube_div (z : UpperHalfPlane) :
    E.sourceCoordinate.coordinate z =
      liftedEisensteinFour E z ^ 3 /
        (1728 * liftedModularDiscriminant E z) := by
  rw [← E.induced_coordinate z]
  simp only [FuchsianModularParameter.coordinate, normalizedJ,
    liftedEisensteinFour, liftedModularDiscriminant]
  field_simp [ModularForm.discriminant_ne_zero]

private lemma liftedEisensteinSix_sq_eq (z : UpperHalfPlane) :
    liftedEisensteinSix E z ^ 2 =
      1728 * liftedModularDiscriminant E z *
        (E.sourceCoordinate.coordinate z - 1) := by
  have hdisc := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq
    (E.modularParameter.tau z)
  have hcoord := sourceCoordinate_eq_liftedEisensteinFour_cube_div E z
  simp only [liftedEisensteinFour, liftedEisensteinSix,
    liftedModularDiscriminant] at hcoord ⊢
  field_simp [ModularForm.discriminant_ne_zero] at hcoord
  have hdisc' :
      1728 * ModularForm.discriminant (E.modularParameter.tau z) =
        ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          ModularForm.E₆ (E.modularParameter.tau z) ^ 2 := by
    calc
      _ = 1728 * ((ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          ModularForm.E₆ (E.modularParameter.tau z) ^ 2) / 1728) := by rw [hdisc]
      _ = _ := by field_simp
  calc
    ModularForm.E₆ (E.modularParameter.tau z) ^ 2 =
        ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          1728 * ModularForm.discriminant (E.modularParameter.tau z) := by
      linear_combination hdisc'
    _ = 1728 * ModularForm.discriminant (E.modularParameter.tau z) *
        (E.sourceCoordinate.coordinate z - 1) := by
      rw [← hcoord]
      ring

private lemma liftedEisensteinFour_zero_iff (z : UpperHalfPlane) :
    liftedEisensteinFour E z = 0 ↔ E.sourceCoordinate.coordinate z = 0 := by
  have hdisc : liftedModularDiscriminant E z ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  rw [sourceCoordinate_eq_liftedEisensteinFour_cube_div E z]
  simp [hdisc]

private lemma liftedEisensteinSix_zero_iff (z : UpperHalfPlane) :
    liftedEisensteinSix E z = 0 ↔ E.sourceCoordinate.coordinate z = 1 := by
  have hdisc : liftedModularDiscriminant E z ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  rw [← sq_eq_zero_iff, liftedEisensteinSix_sq_eq E z]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, hdisc, false_or, sub_eq_zero]

private lemma liftedEisensteinFour_analyticOrderAt_one :
    analyticOrderAt
        (liftedEisensteinFour E ∘ UpperHalfPlane.ofComplex)
        fuchsianOneFixedPoint = (1 : ℕ∞) := by
  let C : ℂ → ℂ := E.sourceCoordinate.coordinate ∘ UpperHalfPlane.ofComplex
  let F4 : ℂ → ℂ := liftedEisensteinFour E ∘ UpperHalfPlane.ofComplex
  let Δ : ℂ → ℂ := liftedModularDiscriminant E ∘ UpperHalfPlane.ofComplex
  have hC : AnalyticAt ℂ C fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      E.sourceCoordinate.coordinate_holomorphic _
  have hF4 : AnalyticAt ℂ F4 fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      ((ModularFormClass.holo ModularForm.E₄).comp
        E.modularParameter.tau_holomorphic) _
  have hΔ : AnalyticAt ℂ Δ fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      (discriminant_mdifferentiable.comp
        E.modularParameter.tau_holomorphic) _
  have hΔne : Δ fuchsianOneFixedPoint ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  have heq : C * (fun w ↦ 1728 * Δ w) = F4 ^ 3 := by
    funext w
    apply (eq_div_iff
      (mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero _))).mp
    simpa only [C, F4, Δ, Function.comp_apply, Pi.mul_apply, Pi.pow_apply,
      liftedModularDiscriminant] using
      sourceCoordinate_eq_liftedEisensteinFour_cube_div E
        (UpperHalfPlane.ofComplex w)
  have hord : analyticOrderAt (C * (fun w ↦ 1728 * Δ w))
        (fuchsianOneFixedPoint : ℂ) =
      analyticOrderAt (F4 ^ 3) (fuchsianOneFixedPoint : ℂ) :=
    analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq))
  have hconstΔ : AnalyticAt ℂ (fun w ↦ 1728 * Δ w) fuchsianOneFixedPoint :=
    analyticAt_const.mul hΔ
  have hconstΔorder :
      analyticOrderAt (fun w ↦ 1728 * Δ w) fuchsianOneFixedPoint = 0 := by
    apply hconstΔ.analyticOrderAt_eq_zero.mpr
    exact mul_ne_zero (by norm_num) hΔne
  rw [analyticOrderAt_mul hC hconstΔ, analyticOrderAt_pow hF4,
    show analyticOrderAt C fuchsianOneFixedPoint = (3 : ℕ∞) by
      simpa only [C] using sourceCoordinate_analyticOrderAt_one E,
    hconstΔorder] at hord
  have horder : analyticOrderAt F4 fuchsianOneFixedPoint = (1 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (3 : ℕ∞)) (by norm_num) (by simp)).injective
    simpa using hord.symm
  change analyticOrderAt F4 fuchsianOneFixedPoint = (1 : ℕ∞)
  exact horder

private lemma liftedEisensteinSix_analyticOrderAt_two :
    analyticOrderAt
        (liftedEisensteinSix E ∘ UpperHalfPlane.ofComplex)
        fuchsianTwoFixedPoint = (2 : ℕ∞) := by
  let C1 : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1
  let F6 : ℂ → ℂ := liftedEisensteinSix E ∘ UpperHalfPlane.ofComplex
  let Δ : ℂ → ℂ := liftedModularDiscriminant E ∘ UpperHalfPlane.ofComplex
  have hC1 : AnalyticAt ℂ C1 fuchsianTwoFixedPoint :=
    (MDifferentiable.analyticAt_comp_ofComplex
      E.sourceCoordinate.coordinate_holomorphic _).sub analyticAt_const
  have hF6 : AnalyticAt ℂ F6 fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      ((ModularFormClass.holo ModularForm.E₆).comp
        E.modularParameter.tau_holomorphic) _
  have hΔ : AnalyticAt ℂ Δ fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      (discriminant_mdifferentiable.comp
        E.modularParameter.tau_holomorphic) _
  have hΔne : Δ fuchsianTwoFixedPoint ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  have heq : F6 ^ 2 = (fun w ↦ 1728 * Δ w) * C1 := by
    funext w
    simpa only [F6, Δ, C1, Function.comp_apply, Pi.mul_apply, Pi.pow_apply] using
      liftedEisensteinSix_sq_eq E (UpperHalfPlane.ofComplex w)
  have hord : analyticOrderAt (F6 ^ 2) (fuchsianTwoFixedPoint : ℂ) =
      analyticOrderAt ((fun w ↦ 1728 * Δ w) * C1)
        (fuchsianTwoFixedPoint : ℂ) :=
    analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq))
  have hconstΔ : AnalyticAt ℂ (fun w ↦ 1728 * Δ w) fuchsianTwoFixedPoint :=
    analyticAt_const.mul hΔ
  have hconstΔorder :
      analyticOrderAt (fun w ↦ 1728 * Δ w) fuchsianTwoFixedPoint = 0 := by
    apply hconstΔ.analyticOrderAt_eq_zero.mpr
    exact mul_ne_zero (by norm_num) hΔne
  rw [analyticOrderAt_pow hF6, analyticOrderAt_mul hconstΔ hC1,
    hconstΔorder,
    show analyticOrderAt C1 fuchsianTwoFixedPoint = (4 : ℕ∞) by
      simpa only [C1] using sourceCoordinate_analyticOrderAt_two E] at hord
  have horder : analyticOrderAt F6 fuchsianTwoFixedPoint = (2 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
    convert hord using 1 <;> norm_num
  change analyticOrderAt F6 fuchsianTwoFixedPoint = (2 : ℕ∞)
  exact horder

/-- The sole global analytic input: a holomorphic square root of the pulled-back `E₆`. -/
structure BareEisensteinSixSqrt where
  root : UpperHalfPlane → ℂ
  root_holomorphic : MDiff root
  root_sq : ∀ z, root z ^ 2 = liftedEisensteinSix E z

/-- A bare root together with the generator signs which will be proved below, rather than assumed
by the final constructor. -/
structure GenuineEisensteinSixSqrt extends BareEisensteinSixSqrt E where
  root_one : ∀ z, root (fuchsianSourceAction g₁ • z) =
    -(E.modularParameter.tau z : ℂ) ^ 3 * root z
  root_two : ∀ z, root (fuchsianSourceAction g₂ • z) =
    (E.modularParameter.tau z : ℂ) ^ 3 * root z

variable (S : GenuineEisensteinSixSqrt E)

private lemma sqrt_zero_iff (z : UpperHalfPlane) :
    S.root z = 0 ↔ E.sourceCoordinate.coordinate z = 1 := by
  rw [← liftedEisensteinSix_zero_iff E z, ← S.root_sq z]
  simp

def genuineModularFrame (z : UpperHalfPlane) : ℂ :=
  liftedEisensteinFour E z ^ 2 * S.root z / liftedModularDiscriminant E z

private lemma genuineModularFrame_holomorphic : MDiff (genuineModularFrame E S) := by
  exact (((ModularFormClass.holo ModularForm.E₄).comp
      E.modularParameter.tau_holomorphic).pow 2).mul S.root_holomorphic |>.div
    (discriminant_mdifferentiable.comp E.modularParameter.tau_holomorphic)
      (fun z ↦ ModularForm.discriminant_ne_zero _)

private lemma genuineModularFrame_zero_iff (z : UpperHalfPlane) :
    genuineModularFrame E S z = 0 ↔
      (∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z) ∨
        ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z := by
  have hΔ : liftedModularDiscriminant E z ≠ 0 := ModularForm.discriminant_ne_zero _
  have hzero : genuineModularFrame E S z = 0 ↔
      E.sourceCoordinate.coordinate z = 0 ∨
        E.sourceCoordinate.coordinate z = 1 := by
    simp [genuineModularFrame, hΔ, liftedEisensteinFour_zero_iff E z,
      sqrt_zero_iff E S z]
  rw [hzero]
  constructor
  · rintro (hz | hz)
    · left
      exact (E.sourceCoordinate.coordinate_eq_iff_orbit fuchsianOneFixedPoint z).mp
        (E.sourceCoordinate.coordinate_at_one.trans hz.symm)
    · right
      exact (E.sourceCoordinate.coordinate_eq_iff_orbit fuchsianTwoFixedPoint z).mp
        (E.sourceCoordinate.coordinate_at_two.trans hz.symm)
  · rintro (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · left
      rw [E.sourceCoordinate.coordinate_invariant, E.sourceCoordinate.coordinate_at_one]
    · right
      rw [E.sourceCoordinate.coordinate_invariant, E.sourceCoordinate.coordinate_at_two]

private lemma sqrt_analyticOrderAt_one :
    analyticOrderAt (S.root ∘ UpperHalfPlane.ofComplex)
      fuchsianOneFixedPoint = (0 : ℕ∞) := by
  have hS : AnalyticAt ℂ (S.root ∘ UpperHalfPlane.ofComplex) fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex S.root_holomorphic _
  apply hS.analyticOrderAt_eq_zero.mpr
  intro hzero
  have := (sqrt_zero_iff E S fuchsianOneFixedPoint).mp (by simpa using hzero)
  rw [E.sourceCoordinate.coordinate_at_one] at this
  norm_num at this

private lemma sqrt_analyticOrderAt_two :
    analyticOrderAt (S.root ∘ UpperHalfPlane.ofComplex)
      fuchsianTwoFixedPoint = (1 : ℕ∞) := by
  let R : ℂ → ℂ := S.root ∘ UpperHalfPlane.ofComplex
  let F6 : ℂ → ℂ := liftedEisensteinSix E ∘ UpperHalfPlane.ofComplex
  have hR : AnalyticAt ℂ R fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex S.root_holomorphic _
  have heq : R ^ 2 = F6 := by
    funext w
    simpa only [R, F6, Function.comp_apply, Pi.pow_apply] using
      S.root_sq (UpperHalfPlane.ofComplex w)
  have hord : analyticOrderAt (R ^ 2) (fuchsianTwoFixedPoint : ℂ) =
      analyticOrderAt F6 (fuchsianTwoFixedPoint : ℂ) :=
    analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq))
  rw [analyticOrderAt_pow hR,
    show analyticOrderAt F6 fuchsianTwoFixedPoint = (2 : ℕ∞) by
      simpa only [F6] using liftedEisensteinSix_analyticOrderAt_two E] at hord
  have horder : analyticOrderAt R fuchsianTwoFixedPoint = (1 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
    simpa using hord
  change analyticOrderAt R fuchsianTwoFixedPoint = (1 : ℕ∞)
  exact horder

private lemma genuineModularFrame_analyticOrderAt_one :
    analyticOrderAt
        (genuineModularFrame E S ∘ UpperHalfPlane.ofComplex)
        fuchsianOneFixedPoint = (2 : ℕ∞) := by
  let F4 : ℂ → ℂ := liftedEisensteinFour E ∘ UpperHalfPlane.ofComplex
  let R : ℂ → ℂ := S.root ∘ UpperHalfPlane.ofComplex
  let Δ : ℂ → ℂ := liftedModularDiscriminant E ∘ UpperHalfPlane.ofComplex
  have hF4 : AnalyticAt ℂ F4 fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      ((ModularFormClass.holo ModularForm.E₄).comp E.modularParameter.tau_holomorphic) _
  have hR : AnalyticAt ℂ R fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex S.root_holomorphic _
  have hΔ : AnalyticAt ℂ Δ fuchsianOneFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      (discriminant_mdifferentiable.comp E.modularParameter.tau_holomorphic) _
  have hΔne : Δ fuchsianOneFixedPoint ≠ 0 := ModularForm.discriminant_ne_zero _
  have hΔinv : AnalyticAt ℂ (fun w ↦ (Δ w)⁻¹) fuchsianOneFixedPoint := hΔ.inv hΔne
  have hΔinvOrder : analyticOrderAt (fun w ↦ (Δ w)⁻¹)
      fuchsianOneFixedPoint = 0 :=
    hΔinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hΔne)
  have heq : genuineModularFrame E S ∘ UpperHalfPlane.ofComplex =
      (F4 ^ 2 * R) * fun w ↦ (Δ w)⁻¹ := by
    funext w
    simp [genuineModularFrame, F4, R, Δ, div_eq_mul_inv]
  rw [analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq)),
    analyticOrderAt_mul ((hF4.pow 2).mul hR) hΔinv,
    analyticOrderAt_mul (hF4.pow 2) hR, analyticOrderAt_pow hF4,
    show analyticOrderAt F4 fuchsianOneFixedPoint = (1 : ℕ∞) by
      simpa only [F4] using liftedEisensteinFour_analyticOrderAt_one E,
    show analyticOrderAt R fuchsianOneFixedPoint = (0 : ℕ∞) by
      simpa only [R] using sqrt_analyticOrderAt_one E S,
    hΔinvOrder]
  norm_num

private lemma genuineModularFrame_analyticOrderAt_two :
    analyticOrderAt
        (genuineModularFrame E S ∘ UpperHalfPlane.ofComplex)
        fuchsianTwoFixedPoint = (1 : ℕ∞) := by
  let F4 : ℂ → ℂ := liftedEisensteinFour E ∘ UpperHalfPlane.ofComplex
  let R : ℂ → ℂ := S.root ∘ UpperHalfPlane.ofComplex
  let Δ : ℂ → ℂ := liftedModularDiscriminant E ∘ UpperHalfPlane.ofComplex
  have hF4 : AnalyticAt ℂ F4 fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      ((ModularFormClass.holo ModularForm.E₄).comp E.modularParameter.tau_holomorphic) _
  have hR : AnalyticAt ℂ R fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex S.root_holomorphic _
  have hΔ : AnalyticAt ℂ Δ fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex
      (discriminant_mdifferentiable.comp E.modularParameter.tau_holomorphic) _
  have hF4ne : F4 fuchsianTwoFixedPoint ≠ 0 := by
    intro hzero
    have hz : liftedEisensteinFour E fuchsianTwoFixedPoint = 0 := by
      simpa [F4, UpperHalfPlane.ofComplex_apply] using hzero
    have := (liftedEisensteinFour_zero_iff E fuchsianTwoFixedPoint).mp hz
    rw [E.sourceCoordinate.coordinate_at_two] at this
    norm_num at this
  have hF4order : analyticOrderAt F4 fuchsianTwoFixedPoint = 0 :=
    hF4.analyticOrderAt_eq_zero.mpr hF4ne
  have hΔne : Δ fuchsianTwoFixedPoint ≠ 0 := ModularForm.discriminant_ne_zero _
  have hΔinv : AnalyticAt ℂ (fun w ↦ (Δ w)⁻¹) fuchsianTwoFixedPoint := hΔ.inv hΔne
  have hΔinvOrder : analyticOrderAt (fun w ↦ (Δ w)⁻¹)
      fuchsianTwoFixedPoint = 0 :=
    hΔinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hΔne)
  have heq : genuineModularFrame E S ∘ UpperHalfPlane.ofComplex =
      (F4 ^ 2 * R) * fun w ↦ (Δ w)⁻¹ := by
    funext w
    simp [genuineModularFrame, F4, R, Δ, div_eq_mul_inv]
  rw [analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq)),
    analyticOrderAt_mul ((hF4.pow 2).mul hR) hΔinv,
    analyticOrderAt_mul (hF4.pow 2) hR, analyticOrderAt_pow hF4,
    hF4order,
    show analyticOrderAt R fuchsianTwoFixedPoint = (1 : ℕ∞) by
      simpa only [R] using sqrt_analyticOrderAt_two E S,
    hΔinvOrder]
  norm_num

noncomputable def genuineModularFrame_branch_one :
    HasExactHolomorphicBranchAt (genuineModularFrame E S)
      fuchsianOneFixedPoint 0 2 := by
  apply hasExactHolomorphicBranchAt_of_analyticOrderAt
    (genuineModularFrame_holomorphic E S) (by
      simp [genuineModularFrame, liftedEisensteinFour_zero_iff E,
        E.sourceCoordinate.coordinate_at_one]) (by norm_num)
  simpa only [sub_zero, Function.comp_def, Nat.cast_ofNat] using
    genuineModularFrame_analyticOrderAt_one E S

noncomputable def genuineModularFrame_branch_two :
    HasExactHolomorphicBranchAt (genuineModularFrame E S)
      fuchsianTwoFixedPoint 0 1 := by
  apply hasExactHolomorphicBranchAt_of_analyticOrderAt
    (genuineModularFrame_holomorphic E S) (by
      simp [genuineModularFrame, sqrt_zero_iff E S,
        E.sourceCoordinate.coordinate_at_two]) (by norm_num)
  simpa only [sub_zero, Function.comp_def, Nat.cast_one] using
    genuineModularFrame_analyticOrderAt_two E S

private lemma liftedEisensteinFour_one (z : UpperHalfPlane) :
    liftedEisensteinFour E (fuchsianSourceAction g₁ • z) =
      (E.modularParameter.tau z : ℂ) ^ 4 * liftedEisensteinFour E z := by
  have htau := E.modularParameter.transform_one z
  have hE := congrFun (ModularForm.E₄.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) ⟨modularOne, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedEisensteinFour, liftedEisensteinFour, htau, rhoTauReal_g₁]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) (E.modularParameter.tau z)
  field_simp [hd] at hE
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularOne)
      (E.modularParameter.tau z) = -(E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularOne]
  rw [hdenom] at hE
  rw [show (-(E.modularParameter.tau z : ℂ)) ^ 4 =
      (E.modularParameter.tau z : ℂ) ^ 4 by ring] at hE
  simpa [modularToReal] using hE

private lemma liftedEisensteinFour_two (z : UpperHalfPlane) :
    liftedEisensteinFour E (fuchsianSourceAction g₂ • z) =
      (E.modularParameter.tau z : ℂ) ^ 4 * liftedEisensteinFour E z := by
  have htau := E.modularParameter.transform_two z
  have hE := congrFun (ModularForm.E₄.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) ⟨modularTwo, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedEisensteinFour, liftedEisensteinFour, htau, rhoTauReal_g₂]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) (E.modularParameter.tau z)
  field_simp [hd] at hE
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo)
      (E.modularParameter.tau z) = (E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularTwo]
  rw [hdenom] at hE
  simpa [modularToReal] using hE

lemma liftedEisensteinSix_one (z : UpperHalfPlane) :
    liftedEisensteinSix E (fuchsianSourceAction g₁ • z) =
      (E.modularParameter.tau z : ℂ) ^ 6 * liftedEisensteinSix E z := by
  have htau := E.modularParameter.transform_one z
  have hE := congrFun (ModularForm.E₆.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) ⟨modularOne, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedEisensteinSix, liftedEisensteinSix, htau, rhoTauReal_g₁]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) (E.modularParameter.tau z)
  field_simp [hd] at hE
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularOne)
      (E.modularParameter.tau z) = -(E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularOne]
  rw [hdenom] at hE
  rw [show (-(E.modularParameter.tau z : ℂ)) ^ 6 =
      (E.modularParameter.tau z : ℂ) ^ 6 by ring] at hE
  simpa [modularToReal] using hE

lemma liftedEisensteinSix_two (z : UpperHalfPlane) :
    liftedEisensteinSix E (fuchsianSourceAction g₂ • z) =
      (E.modularParameter.tau z : ℂ) ^ 6 * liftedEisensteinSix E z := by
  have htau := E.modularParameter.transform_two z
  have hE := congrFun (ModularForm.E₆.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) ⟨modularTwo, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedEisensteinSix, liftedEisensteinSix, htau, rhoTauReal_g₂]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) (E.modularParameter.tau z)
  field_simp [hd] at hE
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo)
      (E.modularParameter.tau z) = (E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularTwo]
  rw [hdenom] at hE
  simpa [modularToReal] using hE

private lemma liftedModularDiscriminant_one (z : UpperHalfPlane) :
    liftedModularDiscriminant E (fuchsianSourceAction g₁ • z) =
      (E.modularParameter.tau z : ℂ) ^ 12 * liftedModularDiscriminant E z := by
  have htau := E.modularParameter.transform_one z
  have hΔ := congrFun (CuspForm.discriminant.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) ⟨modularOne, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedModularDiscriminant, liftedModularDiscriminant, htau, rhoTauReal_g₁]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hΔ
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularOne) (E.modularParameter.tau z)
  field_simp [hd] at hΔ
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularOne)
      (E.modularParameter.tau z) = -(E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularOne]
  rw [hdenom] at hΔ
  rw [show (-(E.modularParameter.tau z : ℂ)) ^ 12 =
      (E.modularParameter.tau z : ℂ) ^ 12 by ring] at hΔ
  simpa [modularToReal] using hΔ

private lemma liftedModularDiscriminant_two (z : UpperHalfPlane) :
    liftedModularDiscriminant E (fuchsianSourceAction g₂ • z) =
      (E.modularParameter.tau z : ℂ) ^ 12 * liftedModularDiscriminant E z := by
  have htau := E.modularParameter.transform_two z
  have hΔ := congrFun (CuspForm.discriminant.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) ⟨modularTwo, rfl⟩)
      (E.modularParameter.tau z)
  rw [liftedModularDiscriminant, liftedModularDiscriminant, htau, rhoTauReal_g₂]
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hΔ
  have hd := UpperHalfPlane.denom_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo) (E.modularParameter.tau z)
  field_simp [hd] at hΔ
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ modularTwo)
      (E.modularParameter.tau z) = (E.modularParameter.tau z : ℂ) := by
    rw [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    norm_num [modularTwo]
  rw [hdenom] at hΔ
  simpa [modularToReal] using hΔ

private lemma genuineModularFrame_one (z : UpperHalfPlane) :
    genuineModularFrame E S (fuchsianSourceAction g₁ • z) =
      -genuineModularFrame E S z / E.modularParameter.tau z := by
  rw [genuineModularFrame, liftedEisensteinFour_one E,
    S.root_one, liftedModularDiscriminant_one E]
  have htau : (E.modularParameter.tau z : ℂ) ≠ 0 :=
    (E.modularParameter.tau z).ne_zero
  field_simp [htau]
  simp [genuineModularFrame, div_eq_mul_inv]

private lemma genuineModularFrame_two (z : UpperHalfPlane) :
    genuineModularFrame E S (fuchsianSourceAction g₂ • z) =
      genuineModularFrame E S z / E.modularParameter.tau z := by
  rw [genuineModularFrame, liftedEisensteinFour_two E,
    S.root_two, liftedModularDiscriminant_two E]
  have htau : (E.modularParameter.tau z : ℂ) ≠ 0 :=
    (E.modularParameter.tau z).ne_zero
  field_simp [htau]
  simp [genuineModularFrame, div_eq_mul_inv]

lemma BareEisensteinSixSqrt.root_zero_iff (R : BareEisensteinSixSqrt E)
    (z : UpperHalfPlane) :
    R.root z = 0 ↔ E.sourceCoordinate.coordinate z = 1 := by
  rw [← liftedEisensteinSix_zero_iff E z, ← R.root_sq z]
  simp

lemma BareEisensteinSixSqrt.root_analyticOrderAt_two (R : BareEisensteinSixSqrt E) :
    analyticOrderAt (R.root ∘ UpperHalfPlane.ofComplex)
      fuchsianTwoFixedPoint = (1 : ℕ∞) := by
  let r : ℂ → ℂ := R.root ∘ UpperHalfPlane.ofComplex
  let F6 : ℂ → ℂ := liftedEisensteinSix E ∘ UpperHalfPlane.ofComplex
  have hr : AnalyticAt ℂ r fuchsianTwoFixedPoint :=
    MDifferentiable.analyticAt_comp_ofComplex R.root_holomorphic _
  have heq : r ^ 2 = F6 := by
    funext w
    simpa only [r, F6, Function.comp_apply, Pi.pow_apply] using
      R.root_sq (UpperHalfPlane.ofComplex w)
  have hord : analyticOrderAt (r ^ 2) (fuchsianTwoFixedPoint : ℂ) =
      analyticOrderAt F6 (fuchsianTwoFixedPoint : ℂ) :=
    analyticOrderAt_congr (Filter.Eventually.of_forall (congrFun heq))
  rw [analyticOrderAt_pow hr,
    show analyticOrderAt F6 fuchsianTwoFixedPoint = (2 : ℕ∞) by
      simpa only [F6] using liftedEisensteinSix_analyticOrderAt_two E] at hord
  apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
  simpa using hord

lemma BareEisensteinSixSqrt.root_one (R : BareEisensteinSixSqrt E) (z : UpperHalfPlane) :
    R.root (fuchsianSourceAction g₁ • z) =
      -(E.modularParameter.tau z : ℂ) ^ 3 * R.root z := by
  let a : UpperHalfPlane → ℂ := fun w ↦ R.root (fuchsianSourceAction g₁ • w)
  let b : UpperHalfPlane → ℂ := fun w ↦
    -(E.modularParameter.tau w : ℂ) ^ 3 * R.root w
  have haction : MDiff (fun w : UpperHalfPlane ↦ fuchsianSourceAction g₁ • w) :=
    (fuchsianSourceAction_contMDiff g₁ ⊤).mdifferentiable (by simp)
  have ha : MDiff a := R.root_holomorphic.comp haction
  have htau : MDiff (fun w ↦ (E.modularParameter.tau w : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp E.modularParameter.tau_holomorphic
  have hb : MDiff b := ((htau.pow 3).neg.mul R.root_holomorphic)
  have hsquares (w : UpperHalfPlane) : a w ^ 2 = b w ^ 2 := by
    calc
      a w ^ 2 = liftedEisensteinSix E (fuchsianSourceAction g₁ • w) :=
        R.root_sq _
      _ = (E.modularParameter.tau w : ℂ) ^ 6 * liftedEisensteinSix E w :=
        liftedEisensteinSix_one E w
      _ = b w ^ 2 := by
        rw [← R.root_sq w]
        dsimp only [b]
        ring
  have hprod : (a - b) * (a + b) = 0 := by
    funext w
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    calc
      (a w - b w) * (a w + b w) = a w ^ 2 - b w ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr (hsquares w)
  rcases (UpperHalfPlane.mul_eq_zero_iff (ha.sub hb) (ha.add hb)).mp hprod with
      hdiff | hsum
  · exact sub_eq_zero.mp (congrFun hdiff z)
  · have hrootne : R.root fuchsianOneFixedPoint ≠ 0 := by
      intro hzero
      have hcoord := (R.root_zero_iff E fuchsianOneFixedPoint).mp hzero
      rw [E.sourceCoordinate.coordinate_at_one] at hcoord
      norm_num at hcoord
    have hcoeff :
        -((ellipticThreeParameter : UpperHalfPlane) : ℂ) ^ 3 = 1 := by
      rw [← fuchsianOneFixedPoint_eq_ellipticThreeParameter]
      change -(⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1
      apply Complex.ext <;>
        norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
      all_goals
        ring_nf
        try rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num <;> ring
    have ha_fixed : a fuchsianOneFixedPoint = R.root fuchsianOneFixedPoint := by
      dsimp only [a]
      rw [fuchsianOneFixedPoint_fixed]
    have hb_fixed : b fuchsianOneFixedPoint = R.root fuchsianOneFixedPoint := by
      simp only [b, E.tau_at_one, hcoeff, one_mul]
    have hzero := congrFun hsum fuchsianOneFixedPoint
    rw [Pi.zero_apply] at hzero
    change a fuchsianOneFixedPoint + b fuchsianOneFixedPoint = 0 at hzero
    rw [ha_fixed, hb_fixed, ← two_mul] at hzero
    exfalso
    exact hrootne ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

lemma BareEisensteinSixSqrt.root_two (R : BareEisensteinSixSqrt E) (z : UpperHalfPlane) :
    R.root (fuchsianSourceAction g₂ • z) =
      (E.modularParameter.tau z : ℂ) ^ 3 * R.root z := by
  let a : UpperHalfPlane → ℂ := fun w ↦ R.root (fuchsianSourceAction g₂ • w)
  let b : UpperHalfPlane → ℂ := fun w ↦
    (E.modularParameter.tau w : ℂ) ^ 3 * R.root w
  have haction : MDiff (fun w : UpperHalfPlane ↦ fuchsianSourceAction g₂ • w) :=
    (fuchsianSourceAction_contMDiff g₂ ⊤).mdifferentiable (by simp)
  have ha : MDiff a := R.root_holomorphic.comp haction
  have htau : MDiff (fun w ↦ (E.modularParameter.tau w : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp E.modularParameter.tau_holomorphic
  have hb : MDiff b := (htau.pow 3).mul R.root_holomorphic
  have hsquares (w : UpperHalfPlane) : a w ^ 2 = b w ^ 2 := by
    calc
      a w ^ 2 = liftedEisensteinSix E (fuchsianSourceAction g₂ • w) :=
        R.root_sq _
      _ = (E.modularParameter.tau w : ℂ) ^ 6 * liftedEisensteinSix E w :=
        liftedEisensteinSix_two E w
      _ = b w ^ 2 := by
        rw [← R.root_sq w]
        dsimp only [b]
        ring
  have hprod : (a - b) * (a + b) = 0 := by
    funext w
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    calc
      (a w - b w) * (a w + b w) = a w ^ 2 - b w ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr (hsquares w)
  rcases (UpperHalfPlane.mul_eq_zero_iff (ha.sub hb) (ha.add hb)).mp hprod with
      hdiff | hsum
  · exact sub_eq_zero.mp (congrFun hdiff z)
  · let r : ℂ → ℂ := R.root ∘ UpperHalfPlane.ofComplex
    have hr : AnalyticAt ℂ r fuchsianTwoFixedPoint :=
      MDifferentiable.analyticAt_comp_ofComplex R.root_holomorphic _
    have hrorder : analyticOrderAt r fuchsianTwoFixedPoint = (1 : ℕ∞) := by
      simpa only [r] using R.root_analyticOrderAt_two E
    have hrderiv : deriv r fuchsianTwoFixedPoint ≠ 0 := by
      have hnonzero :=
        (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hr).mp hrorder |>.2
      simpa [iteratedDeriv_one] using hnonzero
    have hrzero : r fuchsianTwoFixedPoint = 0 := by
      simp only [r, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
      exact (R.root_zero_iff E fuchsianTwoFixedPoint).mpr
        E.sourceCoordinate.coordinate_at_two
    let gamma : ℂ → ℂ := fun w ↦
      ((fuchsianSourceAction g₂ • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)
    have hgamma_eq : gamma =ᶠ[nhds (fuchsianTwoFixedPoint : ℂ)]
        fun w : ℂ ↦ -(1 : ℂ) / (w + Real.sqrt 2) := by
      have him : ∀ᶠ w in nhds (fuchsianTwoFixedPoint : ℂ), 0 < w.im :=
        UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds fuchsianTwoFixedPoint.im_pos
      filter_upwards [him] with w hw
      dsimp only [gamma]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      change ((((fuchsianSourceAction g₂) (⟨w, hw⟩ : UpperHalfPlane) :
        UpperHalfPlane) : ℂ)) = _
      rw [fuchsianSourceAction_g₂_apply]
    have hden : (fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num [fuchsianTwoFixedPoint] at him
    have hrat : HasDerivAt (fun w : ℂ ↦ -(1 : ℂ) / (w + Real.sqrt 2))
        (1 / ((fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2) ^ 2)
        fuchsianTwoFixedPoint := by
      have hnum : HasDerivAt (fun _ : ℂ ↦ -(1 : ℂ)) 0 fuchsianTwoFixedPoint :=
        hasDerivAt_const _ _
      have hdenom : HasDerivAt (fun w : ℂ ↦ w + Real.sqrt 2) 1
          fuchsianTwoFixedPoint := (hasDerivAt_id _).add_const _
      have hquot := hnum.div hdenom hden
      have heq : (fun w : ℂ ↦ -(1 : ℂ) / (w + Real.sqrt 2)) =ᶠ[nhds
          (fuchsianTwoFixedPoint : ℂ)]
          ((fun _ : ℂ ↦ -(1 : ℂ)) / (fun w : ℂ ↦ w + Real.sqrt 2)) := by
        filter_upwards [] with w
        rfl
      simpa only [zero_mul, mul_one, zero_sub, neg_neg, one_div] using
        hquot.congr_of_eventuallyEq heq
    have hdensq : ((fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2) ^ 2 = Complex.I := by
      change ((⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ : ℂ) + Real.sqrt 2) ^ 2 =
        Complex.I
      apply Complex.ext <;>
        norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      ring_nf
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hgamma_deriv : deriv gamma fuchsianTwoFixedPoint = -Complex.I := by
      calc
        deriv gamma fuchsianTwoFixedPoint =
            deriv (fun w : ℂ ↦ -(1 : ℂ) / (w + Real.sqrt 2))
              fuchsianTwoFixedPoint := hgamma_eq.deriv_eq
        _ = 1 / ((fuchsianTwoFixedPoint : ℂ) + Real.sqrt 2) ^ 2 := hrat.deriv
        _ = -Complex.I := by rw [hdensq]; norm_num
    have hgamma_zero : gamma fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
      simp only [gamma, UpperHalfPlane.ofComplex_apply, fuchsianTwoFixedPoint_fixed]
    have hgamma_diff : DifferentiableAt ℂ gamma fuchsianTwoFixedPoint :=
      hgamma_eq.differentiableAt_iff.mpr hrat.differentiableAt
    let A : ℂ → ℂ := a ∘ UpperHalfPlane.ofComplex
    let B : ℂ → ℂ := b ∘ UpperHalfPlane.ofComplex
    have hAeq : A = r ∘ gamma := by
      funext w
      simp only [A, a, r, gamma, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    have hAdiff : DifferentiableAt ℂ A fuchsianTwoFixedPoint := by
      rw [hAeq]
      have hr_at : DifferentiableAt ℂ r (gamma fuchsianTwoFixedPoint) := by
        rw [hgamma_zero]
        exact hr.differentiableAt
      exact hr_at.comp (fuchsianTwoFixedPoint : ℂ) hgamma_diff
    have hAderiv : deriv A fuchsianTwoFixedPoint =
        deriv r fuchsianTwoFixedPoint * (-Complex.I) := by
      rw [hAeq]
      have hr_at : DifferentiableAt ℂ r (gamma fuchsianTwoFixedPoint) := by
        rw [hgamma_zero]
        exact hr.differentiableAt
      have hchain := hr_at.hasDerivAt.comp (fuchsianTwoFixedPoint : ℂ)
        hgamma_diff.hasDerivAt
      simpa [hgamma_zero, hgamma_deriv] using hchain.deriv
    let t : ℂ → ℂ := fun w ↦
      (E.modularParameter.tau (UpperHalfPlane.ofComplex w) : ℂ)
    have ht : AnalyticAt ℂ t fuchsianTwoFixedPoint :=
      MDifferentiable.analyticAt_comp_ofComplex htau _
    have htzero : t fuchsianTwoFixedPoint = Complex.I := by
      simp [t, E.tau_at_two, UpperHalfPlane.I]
    have hBeq : B = (t ^ 3) * r := by
      funext w
      rfl
    have hBdiff : DifferentiableAt ℂ B fuchsianTwoFixedPoint := by
      rw [hBeq]
      exact (ht.pow 3).mul hr |>.differentiableAt
    have hBderiv : deriv B fuchsianTwoFixedPoint =
        (-Complex.I) * deriv r fuchsianTwoFixedPoint := by
      rw [hBeq]
      have hder := ((ht.differentiableAt.hasDerivAt.pow 3).mul
        hr.differentiableAt.hasDerivAt).deriv
      simpa [htzero, hrzero, pow_succ] using hder
    have hsumAB : A + B = 0 := by
      funext w
      simpa only [A, B, Pi.add_apply, Pi.zero_apply, Function.comp_apply] using
        congrFun hsum (UpperHalfPlane.ofComplex w)
    have hderzero : deriv (A + B) fuchsianTwoFixedPoint = 0 := by
      rw [hsumAB]
      simp
    have hadd : deriv (A + B) fuchsianTwoFixedPoint =
        deriv A fuchsianTwoFixedPoint + deriv B fuchsianTwoFixedPoint :=
      (hAdiff.hasDerivAt.add hBdiff.hasDerivAt).deriv
    rw [hadd, hAderiv, hBderiv] at hderzero
    have hmul : (-2 * Complex.I) * deriv r fuchsianTwoFixedPoint = 0 := by
      calc
        (-2 * Complex.I) * deriv r fuchsianTwoFixedPoint =
            deriv r fuchsianTwoFixedPoint * (-Complex.I) +
              (-Complex.I) * deriv r fuchsianTwoFixedPoint := by ring
        _ = 0 := hderzero
    exfalso
    exact hrderiv ((mul_eq_zero.mp hmul).resolve_left (by norm_num))

/-- The generator signs of a holomorphic square root are forced by its square identity and the
normalizations at the two elliptic fixed points. -/
def BareEisensteinSixSqrt.toGenuine (R : BareEisensteinSixSqrt E) :
    GenuineEisensteinSixSqrt E where
  toBareEisensteinSixSqrt := R
  root_one := R.root_one E
  root_two := R.root_two E

/-- The two forced elliptic signs cancel along the parabolic product. -/
lemma GenuineEisensteinSixSqrt.root_product (S : GenuineEisensteinSixSqrt E)
    (z : UpperHalfPlane) :
    S.root (fuchsianSourceAction (g₁ * g₂) • z) = S.root z := by
  have htau :
      ((E.modularParameter.tau (fuchsianSourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
        -1 / E.modularParameter.tau z := by
    exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
      (E.modularParameter.equivariant g₂ z)).trans
        (rhoTauReal_g₂_smul (E.modularParameter.tau z))
  rw [map_mul, mul_smul, S.root_one, S.root_two, htau]
  field_simp [(E.modularParameter.tau z).ne_zero]

/-- The forced elliptic signs imply invariance under the inverse parabolic generator. -/
lemma GenuineEisensteinSixSqrt.root_cusp (S : GenuineEisensteinSixSqrt E)
    (z : UpperHalfPlane) :
    S.root (fuchsianSourceAction g₀ • z) = S.root z := by
  have h := S.root_product E (fuchsianSourceAction g₀ • z)
  rw [← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀, map_one, one_smul] at h
  exact h.symm

/-- Forget the implementation of the production global root, retaining exactly the data used by
the sign and frame construction. -/
def ExactFuchsianEisensteinSixRoot.toBare
    (R : ExactFuchsianEisensteinSixRoot E) : BareEisensteinSixSqrt E where
  root := R.root
  root_holomorphic := R.root_holomorphic
  root_sq := R.root_sq

/-- A bare holomorphic square root determines the complete exact lifted modular frame. -/
theorem exists_exactLiftedModularNegOneFrame_of_bareRoot
    (R : BareEisensteinSixSqrt E) :
    Nonempty (ExactLiftedModularNegOneFrame E) := by
  let S : GenuineEisensteinSixSqrt E := R.toGenuine E
  obtain ⟨C⟩ := exists_exactFuchsianCuspFrameGerm E S.root
    S.root_holomorphic (by
      intro z
      simpa only [liftedEisensteinSix] using S.root_sq z) (S.root_cusp E)
  refine ⟨{
    sqrtEisensteinSix := S.root
    sqrtEisensteinSix_holomorphic := S.root_holomorphic
    sqrtEisensteinSix_sq := S.root_sq
    frame := genuineModularFrame E S
    frame_eq := fun _ ↦ rfl
    frame_holomorphic := genuineModularFrame_holomorphic E S
    frame_branch_one := genuineModularFrame_branch_one E S
    frame_branch_two := genuineModularFrame_branch_two E S
    frame_zero_iff := genuineModularFrame_zero_iff E S
    frame_one := genuineModularFrame_one E S
    frame_two := genuineModularFrame_two E S
    cuspUnit := C.cuspUnit
    cuspRadius := C.cuspRadius
    cuspRadius_pos := C.cuspRadius_pos
    cuspUnit_holomorphic := C.cuspUnit_holomorphic
    cuspUnit_zero_ne := C.cuspUnit_zero_ne
    inverse_coordinate_eventually_mem_closedBall :=
      C.inverse_coordinate_eventually_mem_closedBall
    cusp_factorization_eventually := ?_ }⟩
  simpa only [genuineModularFrame, liftedEisensteinFour,
    liftedModularDiscriminant] using C.cusp_factorization_eventually

/-- The established uniformization carries a fully genuine exact lifted modular frame. -/
public theorem establishedExactLiftedModularNegOneFrame
    (E : EstablishedFuchsianModularParameter) :
    Nonempty (ExactLiftedModularNegOneFrame E) := by
  obtain ⟨R⟩ := exists_exactFuchsianEisensteinSixRoot E
  exact exists_exactLiftedModularNegOneFrame_of_bareRoot E R.toBare

end SphereSixComplex.Periods
