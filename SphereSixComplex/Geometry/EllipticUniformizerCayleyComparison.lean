module

public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import Mathlib.Analysis.Complex.RemovableSingularity
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Comparing an analytic elliptic uniformizer with the Cayley coordinate

An arbitrary exact elliptic branch is expressed using a holomorphic local uniformizer.  This file
compares that uniformizer with the explicit Cayley coordinate used by the filling collars.  Their
ratio is implemented as a divided slope, so it extends continuously and nonvanishingly across the
elliptic center.  This is the analytic input needed to compute the winding of the actual collar
paths without assuming that the chosen branch uniformizer literally is the Cayley coordinate.
-/

@[expose] public section

open scoped ComplexConjugate Manifold

noncomputable section

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods
open EllipticLocalCoordinates EllipticCayleyHomeomorph

def cayleyInverseExtension (a : UpperHalfPlane) (w : ℂ) : ℂ :=
  ((a : ℂ) - w * conj (a : ℂ)) / (1 - w)

theorem cayleyInverseExtension_zero (a : UpperHalfPlane) :
    cayleyInverseExtension a 0 = (a : ℂ) := by
  simp [cayleyInverseExtension]

theorem cayleyInverseExtension_eq (a : UpperHalfPlane) (w : ComplexUnitDisc) :
    cayleyInverseExtension a w.1 = cayleyInverse a w := by
  rfl

theorem cayleyInverseExtension_im_pos (a : UpperHalfPlane) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayleyInverseExtension a w).im := by
  change 0 < (cayleyInverse a (⟨w, hw⟩ : ComplexUnitDisc)).im
  exact cayleyInverse_im_pos a (⟨w, hw⟩ : ComplexUnitDisc)

theorem differentiableAt_cayleyInverseExtension (a : UpperHalfPlane) {w : ℂ}
    (hw : w ≠ 1) : DifferentiableAt ℂ (cayleyInverseExtension a) w := by
  unfold cayleyInverseExtension
  have hnum : DifferentiableAt ℂ (fun w : ℂ ↦ (a : ℂ) - w * conj (a : ℂ)) w := by
    fun_prop
  have hden : DifferentiableAt ℂ (fun w : ℂ ↦ 1 - w) w := by
    fun_prop
  exact hnum.div hden (sub_ne_zero.mpr hw.symm)

theorem uniformizerExtension_deriv_ne_zero
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu0 : u a = 0)
    (hu : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ u a) :
    deriv (u ∘ UpperHalfPlane.ofComplex) (a : ℂ) ≠ 0 := by
  have hGdiff : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hu.mdifferentiableAt (by simp))
  let H : ℂ → ℂ := fun y ↦ (hu.localInverse y : ℂ)
  have hHmdiff : MDiffAt H 0 := by
    change MDiffAt (((↑) : UpperHalfPlane → ℂ) ∘ hu.localInverse) 0
    exact UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.comp 0
      (by simpa [hu0] using hu.localInverse_mdifferentiableAt (by simp))
  have hHdiff : DifferentiableAt ℂ H 0 :=
    mdifferentiableAt_iff_differentiableAt.mp hHmdiff
  have hH0 : H 0 = (a : ℂ) := by
    change (hu.localInverse 0 : ℂ) = (a : ℂ)
    rw [← hu0]
    exact congrArg ((↑) : UpperHalfPlane → ℂ)
      (hu.localInverse_left_inv hu.localInverse_mem_target)
  have hright : (u ∘ UpperHalfPlane.ofComplex) ∘ H =ᶠ[nhds 0] id := by
    have hright' := hu.localInverse_eventuallyEq_right
    rw [hu0] at hright'
    filter_upwards [hright'] with y hy
    change u (UpperHalfPlane.ofComplex (hu.localInverse y : ℂ)) = y
    rw [UpperHalfPlane.ofComplex_apply]
    exact hy
  intro hzero
  have hGdiff' : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) (H 0) := by
    rw [hH0]
    exact hGdiff
  have hcomp := deriv_comp (x := (0 : ℂ)) hGdiff' hHdiff
  rw [hright.deriv_eq] at hcomp
  rw [hH0, hzero] at hcomp
  simp at hcomp

def uniformizerCayleyExtension (a : UpperHalfPlane) (u : UpperHalfPlane → ℂ)
    (w : ℂ) : ℂ :=
  u (UpperHalfPlane.ofComplex (cayleyInverseExtension a w))

theorem differentiableAt_uniformizerCayleyExtension_zero
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu : MDiffAt u a) :
    DifferentiableAt ℂ (uniformizerCayleyExtension a u) 0 := by
  have houter : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp hu
  have hinner : DifferentiableAt ℂ (cayleyInverseExtension a) 0 :=
    differentiableAt_cayleyInverseExtension a (by norm_num)
  have houter' : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex)
      (cayleyInverseExtension a 0) := by
    rw [cayleyInverseExtension_zero]
    exact houter
  have hcomp := houter'.comp (0 : ℂ) hinner
  change DifferentiableAt ℂ
    (fun w ↦ u (UpperHalfPlane.ofComplex (cayleyInverseExtension a w))) 0
  exact hcomp

theorem uniformizerCayleyExtension_zero
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ} (hu0 : u a = 0) :
    uniformizerCayleyExtension a u 0 = 0 := by
  simp [uniformizerCayleyExtension, cayleyInverseExtension_zero,
    UpperHalfPlane.ofComplex_apply, hu0]

/-- Inside the open unit disc, the total extension evaluates the uniformizer at the genuine
inverse Cayley point. -/
theorem uniformizerCayleyExtension_eq_cayleyInverseUpper
    (a : UpperHalfPlane) (u : UpperHalfPlane → ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    uniformizerCayleyExtension a u w =
      u (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc)) := by
  unfold uniformizerCayleyExtension
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos
    (cayleyInverseExtension_im_pos a hw)]
  congr 1

theorem uniformizerCayleyExtension_deriv_ne_zero
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu0 : u a = 0)
    (hu : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ u a) :
    deriv (uniformizerCayleyExtension a u) 0 ≠ 0 := by
  have houter : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hu.mdifferentiableAt (by simp))
  have hinner : DifferentiableAt ℂ (cayleyInverseExtension a) 0 :=
    differentiableAt_cayleyInverseExtension a (by norm_num)
  have houter' : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex)
      (cayleyInverseExtension a 0) := by
    rw [cayleyInverseExtension_zero]
    exact houter
  have hcomp := deriv_comp (x := (0 : ℂ)) houter' hinner
  have houter_ne := uniformizerExtension_deriv_ne_zero hu0 hu
  have houter_ne' : deriv (u ∘ UpperHalfPlane.ofComplex)
      (cayleyInverseExtension a 0) ≠ 0 := by
    rw [cayleyInverseExtension_zero]
    exact houter_ne
  have hinner_ne : deriv (cayleyInverseExtension a) 0 ≠ 0 := by
    change deriv (fun w : ℂ ↦
      ((a : ℂ) - w * conj (a : ℂ)) / (1 - w)) 0 ≠ 0
    rw [deriv_fun_div]
    · simp
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith [a.im_pos]
    · fun_prop
    · fun_prop
    · norm_num
  rw [show uniformizerCayleyExtension a u =
      (u ∘ UpperHalfPlane.ofComplex) ∘ cayleyInverseExtension a by rfl]
  rw [hcomp]
  exact mul_ne_zero houter_ne' hinner_ne

def uniformizerCayleyFactor (a : UpperHalfPlane) (u : UpperHalfPlane → ℂ) : ℂ → ℂ :=
  dslope (uniformizerCayleyExtension a u) 0

theorem uniformizerCayleyExtension_eq_mul_factor
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ} (hu0 : u a = 0) (w : ℂ) :
    uniformizerCayleyExtension a u w = w * uniformizerCayleyFactor a u w := by
  by_cases hw : w = 0
  · simp [hw, uniformizerCayleyExtension_zero hu0]
  · rw [uniformizerCayleyFactor, dslope_of_ne _ hw, slope]
    simp [uniformizerCayleyExtension_zero hu0, hw, smul_eq_mul]

/-- Exact comparison of the genuine inverse-Cayley uniformizer with the Cayley coordinate. -/
theorem uniformizer_cayleyInverseUpper_eq_mul_factor
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ} (hu0 : u a = 0)
    {w : ℂ} (hw : ‖w‖ < 1) :
    u (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc)) =
      w * uniformizerCayleyFactor a u w := by
  rw [← uniformizerCayleyExtension_eq_cayleyInverseUpper a u hw]
  exact uniformizerCayleyExtension_eq_mul_factor hu0 w

theorem continuousAt_uniformizerCayleyFactor
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu : MDiffAt u a) :
    ContinuousAt (uniformizerCayleyFactor a u) 0 := by
  unfold uniformizerCayleyFactor
  exact continuousAt_dslope_same.mpr
    (differentiableAt_uniformizerCayleyExtension_zero hu)

theorem uniformizerCayleyFactor_zero_ne
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu0 : u a = 0)
    (hu : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ u a) :
    uniformizerCayleyFactor a u 0 ≠ 0 := by
  rw [uniformizerCayleyFactor, dslope_same]
  exact uniformizerCayleyExtension_deriv_ne_zero hu0 hu

/-- The residual leading unit obtained after replacing an arbitrary branch uniformizer by the
explicit Cayley coordinate. -/
def ellipticCayleyLeadingUnit (a : UpperHalfPlane) (order : ℕ)
    (uniformizer unit : UpperHalfPlane → ℂ) (w : ℂ) : ℂ :=
  uniformizerCayleyFactor a uniformizer w ^ order *
    uniformizerCayleyExtension a unit w

theorem continuousAt_ellipticCayleyLeadingUnit_zero
    {a : UpperHalfPlane} {order : ℕ} {uniformizer unit : UpperHalfPlane → ℂ}
    (huniformizer : MDiffAt uniformizer a) (hunit : MDiffAt unit a) :
    ContinuousAt (ellipticCayleyLeadingUnit a order uniformizer unit) 0 := by
  unfold ellipticCayleyLeadingUnit
  exact (continuousAt_uniformizerCayleyFactor huniformizer).pow order |>.mul
    (differentiableAt_uniformizerCayleyExtension_zero hunit).continuousAt

theorem ellipticCayleyLeadingUnit_zero
    {a : UpperHalfPlane} {order : ℕ} {uniformizer unit : UpperHalfPlane → ℂ} :
    ellipticCayleyLeadingUnit a order uniformizer unit 0 =
      deriv (uniformizerCayleyExtension a uniformizer) 0 ^ order * unit a := by
  simp [ellipticCayleyLeadingUnit, uniformizerCayleyFactor, dslope_same,
    uniformizerCayleyExtension, cayleyInverseExtension_zero,
    UpperHalfPlane.ofComplex_apply]

theorem ellipticCayleyLeadingUnit_zero_ne
    {a : UpperHalfPlane} {order : ℕ} {uniformizer unit : UpperHalfPlane → ℂ}
    (huniformizer0 : uniformizer a = 0)
    (huniformizer : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ uniformizer a)
    (hunit : unit a ≠ 0) :
    ellipticCayleyLeadingUnit a order uniformizer unit 0 ≠ 0 := by
  rw [ellipticCayleyLeadingUnit_zero]
  exact mul_ne_zero (pow_ne_zero order
    (uniformizerCayleyExtension_deriv_ne_zero huniformizer0 huniformizer)) hunit

/-- Rewriting an exact branch factorization in inverse-Cayley coordinates extracts the explicit
power of the Cayley variable and leaves the completed leading unit. -/
theorem branchFactorization_cayley_eq_pow_mul_leadingUnit
    {a : UpperHalfPlane} {order : ℕ} {f uniformizer unit : UpperHalfPlane → ℂ}
    {value w : ℂ} (hw : ‖w‖ < 1) (huniformizer0 : uniformizer a = 0)
    (hfactor : f (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc)) - value =
      uniformizer (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc)) ^ order *
        unit (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc))) :
    f (cayleyInverseUpper a (⟨w, hw⟩ : ComplexUnitDisc)) - value =
      w ^ order * ellipticCayleyLeadingUnit a order uniformizer unit w := by
  rw [hfactor, uniformizer_cayleyInverseUpper_eq_mul_factor huniformizer0 hw,
    ← uniformizerCayleyExtension_eq_cayleyInverseUpper a unit hw]
  unfold ellipticCayleyLeadingUnit
  rw [mul_pow]
  ring

theorem eventually_uniformizerCayleyFactor_continuousAt_ne_zero
    {a : UpperHalfPlane} {u : UpperHalfPlane → ℂ}
    (hu0 : u a = 0)
    (hu : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ u a) :
    ∀ᶠ w in nhds (0 : ℂ),
      ContinuousAt (uniformizerCayleyFactor a u) w ∧
        uniformizerCayleyFactor a u w ≠ 0 := by
  have huDiff : MDiffAt u a := hu.mdifferentiableAt (by simp)
  have hfactorCont0 : ContinuousAt (uniformizerCayleyFactor a u) 0 :=
    continuousAt_uniformizerCayleyFactor huDiff
  have hfactorNe : ∀ᶠ w in nhds (0 : ℂ), uniformizerCayleyFactor a u w ≠ 0 :=
    hfactorCont0.eventually_ne (uniformizerCayleyFactor_zero_ne hu0 hu)
  have huContEventually : ∀ᶠ z in nhds a, ContinuousAt u z := by
    have hsource : hu.choose.source ∈ nhds a :=
      hu.choose.open_source.mem_nhds hu.choose_spec.1
    filter_upwards [hsource] with z hz
    have hphi : ContinuousAt hu.choose z :=
      (hu.choose.contMDiffOn_toFun.contMDiffAt
        (hu.choose.open_source.mem_nhds hz)).continuousAt
    have heq : u =ᶠ[nhds z] hu.choose :=
      Filter.eventuallyEq_of_mem (hu.choose.open_source.mem_nhds hz) hu.choose_spec.2
    exact hphi.congr_of_eventuallyEq heq
  let Z : ℂ → UpperHalfPlane := fun w ↦
    UpperHalfPlane.ofComplex (cayleyInverseExtension a w)
  have hZ0 : Z 0 = a := by
    apply UpperHalfPlane.ext
    simp [Z, cayleyInverseExtension_zero, UpperHalfPlane.ofComplex_apply]
  have hZCont0 : ContinuousAt Z 0 := by
    have hinner := differentiableAt_cayleyInverseExtension a
      (show (0 : ℂ) ≠ 1 by norm_num)
    have hof : MDiffAt UpperHalfPlane.ofComplex (a : ℂ) :=
      UpperHalfPlane.mdifferentiableAt_ofComplex a.im_pos
    have hof' : ContinuousAt UpperHalfPlane.ofComplex
        (cayleyInverseExtension a 0) := by
      rw [cayleyInverseExtension_zero]
      exact hof.continuousAt
    exact hof'.comp hinner.continuousAt
  have hZCont : ∀ᶠ w in nhds (0 : ℂ), ContinuousAt Z w := by
    have hball : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ nhds 0 :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with w hw
    have hwnorm : ‖w‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    have hwne : w ≠ 1 := by
      intro h
      rw [h, norm_one] at hwnorm
      linarith
    have hinner := differentiableAt_cayleyInverseExtension a hwne
    have him := cayleyInverseExtension_im_pos a hwnorm
    have hof : ContinuousAt UpperHalfPlane.ofComplex (cayleyInverseExtension a w) :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex him).continuousAt
    exact hof.comp hinner.continuousAt
  have huContAlong : ∀ᶠ w in nhds (0 : ℂ), ContinuousAt u (Z w) := by
    rw [← hZ0] at huContEventually
    exact hZCont0.eventually huContEventually
  filter_upwards [hfactorNe, hZCont, huContAlong] with w hne hZ hU
  refine ⟨?_, hne⟩
  by_cases hw : w = 0
  · simpa [hw] using hfactorCont0
  · apply (continuousAt_dslope_of_ne hw).mpr
    exact hU.comp hZ

end SphereSixComplex.Geometry
