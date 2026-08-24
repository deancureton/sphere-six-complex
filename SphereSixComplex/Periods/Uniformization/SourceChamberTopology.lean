module

public import SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
import all SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import all Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Convex
import all Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CoveringMap
import all Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.Periodic
import all Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Convex.Contractible
import all Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import all Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import all TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

@[expose] public section

open Complex Set

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-- A vertical shear of the complex plane. -/
def verticalShear (phi : ℝ → ℝ) (hphi : Continuous phi) : ℂ ≃ₜ ℂ where
  toFun z := (z.re : ℂ) + (z.im - phi z.re) * Complex.I
  invFun z := (z.re : ℂ) + (z.im + phi z.re) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv z := by
    apply Complex.ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem verticalShear_re (phi : ℝ → ℝ) (hphi : Continuous phi) (z : ℂ) :
    (verticalShear phi hphi z).re = z.re := by simp [verticalShear]

@[simp] theorem verticalShear_im (phi : ℝ → ℝ) (hphi : Continuous phi) (z : ℂ) :
    (verticalShear phi hphi z).im = z.im - phi z.re := by simp [verticalShear]

def semicircleHeight (x : ℝ) : ℝ := Real.sqrt (max 0 (1 - x ^ 2))

theorem continuous_semicircleHeight : Continuous semicircleHeight := by
  unfold semicircleHeight
  fun_prop

def sourceOpenChamber : Set ℂ :=
  {z | -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧ 0 < z.im ∧ 1 < normSq z}

def flatOpenChamber : Set ℂ :=
  {z | -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧ 0 < z.im}

theorem re_sq_lt_one_of_source_bounds {x : ℝ}
    (hl : -Real.sqrt 2 / 2 < x) (hr : x < 1 / 2) : x ^ 2 < 1 := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hs2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hxlo : -1 < x := by
    have hs2lt : Real.sqrt 2 < 2 := by nlinarith
    nlinarith
  have hxhi : x < 1 := by linarith
  nlinarith

theorem semicircleHeight_sq_of_source_bounds {x : ℝ}
    (hl : -Real.sqrt 2 / 2 < x) (hr : x < 1 / 2) :
    semicircleHeight x ^ 2 = 1 - x ^ 2 := by
  have hx := re_sq_lt_one_of_source_bounds hl hr
  rw [semicircleHeight, max_eq_right (by linarith), Real.sq_sqrt (by linarith)]

theorem source_normSq_iff_height {z : ℂ}
    (hl : -Real.sqrt 2 / 2 < z.re) (hr : z.re < 1 / 2) (hi : 0 < z.im) :
    1 < normSq z ↔ semicircleHeight z.re < z.im := by
  have hs0 : 0 ≤ semicircleHeight z.re := by
    unfold semicircleHeight
    positivity
  have hs := semicircleHeight_sq_of_source_bounds hl hr
  rw [normSq_apply]
  constructor <;> intro h <;> nlinarith

theorem verticalShear_image_sourceOpenChamber :
    verticalShear semicircleHeight continuous_semicircleHeight '' sourceOpenChamber =
      flatOpenChamber := by
  ext w
  constructor
  · rintro ⟨z, ⟨hl, hr, hi, hn⟩, rfl⟩
    simp only [flatOpenChamber, mem_setOf_eq, verticalShear_re, verticalShear_im]
    exact ⟨hl, hr, sub_pos.mpr ((source_normSq_iff_height hl hr hi).mp hn)⟩
  · rintro ⟨hl, hr, hi⟩
    let z : ℂ := (verticalShear semicircleHeight continuous_semicircleHeight).symm w
    refine ⟨z, ?_, (verticalShear semicircleHeight continuous_semicircleHeight).apply_symm_apply w⟩
    have hzre : z.re = w.re := by simp [z, verticalShear]
    have hzim : z.im = w.im + semicircleHeight w.re := by simp [z, verticalShear]
    have hs0 : 0 ≤ semicircleHeight w.re := by
      unfold semicircleHeight
      positivity
    have hzpos : 0 < z.im := by rw [hzim]; positivity
    refine ⟨by simpa [hzre] using hl, by simpa [hzre] using hr, hzpos, ?_⟩
    apply (source_normSq_iff_height (by simpa [hzre] using hl)
      (by simpa [hzre] using hr) hzpos).mpr
    rw [hzim, hzre]
    linarith

theorem flatOpenChamber_convex : Convex ℝ flatOpenChamber := by
  rw [show flatOpenChamber =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩ {z : ℂ | 0 < z.im}) by
    ext z
    simp [flatOpenChamber]]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

theorem flatOpenChamber_nonempty : flatOpenChamber.Nonempty := by
  refine ⟨Complex.I, ?_⟩
  change -Real.sqrt 2 / 2 < 0 ∧ (0 : ℝ) < 1 / 2 ∧ (0 : ℝ) < 1
  constructor
  · have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  norm_num

theorem flatOpenChamber_isSimplyConnected : IsSimplyConnected flatOpenChamber := by
  letI : ContractibleSpace flatOpenChamber :=
    flatOpenChamber_convex.contractibleSpace flatOpenChamber_nonempty
  show SimplyConnectedSpace flatOpenChamber
  infer_instance

theorem sourceOpenChamber_isSimplyConnected : IsSimplyConnected sourceOpenChamber := by
  rw [← (verticalShear semicircleHeight continuous_semicircleHeight).isSimplyConnected_image,
    verticalShear_image_sourceOpenChamber]
  exact flatOpenChamber_isSimplyConnected

/-- The corresponding open reflection chamber for the level-one modular group. -/
def targetOpenChamber : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 / 2 ∧ 0 < z.im ∧ 1 < normSq z}

def targetFlatOpenChamber : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 / 2 ∧ 0 < z.im}

theorem target_re_sq_lt_one {x : ℝ} (hl : 0 < x) (hr : x < 1 / 2) : x ^ 2 < 1 := by
  nlinarith

theorem target_semicircleHeight_sq {x : ℝ} (hl : 0 < x) (hr : x < 1 / 2) :
    semicircleHeight x ^ 2 = 1 - x ^ 2 := by
  have hx := target_re_sq_lt_one hl hr
  rw [semicircleHeight, max_eq_right (by linarith), Real.sq_sqrt (by linarith)]

theorem target_normSq_iff_height {z : ℂ} (hl : 0 < z.re) (hr : z.re < 1 / 2)
    (hi : 0 < z.im) : 1 < normSq z ↔ semicircleHeight z.re < z.im := by
  have hs0 : 0 ≤ semicircleHeight z.re := by
    unfold semicircleHeight
    positivity
  have hs := target_semicircleHeight_sq hl hr
  rw [normSq_apply]
  constructor <;> intro h <;> nlinarith

theorem verticalShear_image_targetOpenChamber :
    verticalShear semicircleHeight continuous_semicircleHeight '' targetOpenChamber =
      targetFlatOpenChamber := by
  ext w
  constructor
  · rintro ⟨z, ⟨hl, hr, hi, hn⟩, rfl⟩
    simp only [targetFlatOpenChamber, Set.mem_ofPred_eq, verticalShear_re, verticalShear_im]
    exact ⟨hl, hr, sub_pos.mpr ((target_normSq_iff_height hl hr hi).mp hn)⟩
  · rintro ⟨hl, hr, hi⟩
    let z : ℂ := (verticalShear semicircleHeight continuous_semicircleHeight).symm w
    refine ⟨z, ?_, (verticalShear semicircleHeight continuous_semicircleHeight).apply_symm_apply w⟩
    have hzre : z.re = w.re := by simp [z, verticalShear]
    have hzim : z.im = w.im + semicircleHeight w.re := by simp [z, verticalShear]
    have hzpos : 0 < z.im := by
      rw [hzim]
      have : 0 ≤ semicircleHeight w.re := by unfold semicircleHeight; positivity
      linarith
    refine ⟨by simpa [hzre] using hl, by simpa [hzre] using hr, hzpos, ?_⟩
    apply (target_normSq_iff_height (by simpa [hzre] using hl)
      (by simpa [hzre] using hr) hzpos).mpr
    rw [hzim, hzre]
    linarith

theorem targetFlatOpenChamber_convex : Convex ℝ targetFlatOpenChamber := by
  rw [show targetFlatOpenChamber =
      {z : ℂ | 0 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩ {z : ℂ | 0 < z.im}) by
    ext z
    simp [targetFlatOpenChamber]]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _))

theorem targetFlatOpenChamber_nonempty : targetFlatOpenChamber.Nonempty := by
  refine ⟨⟨1 / 4, 1⟩, ?_⟩
  norm_num [targetFlatOpenChamber]

theorem targetOpenChamber_isSimplyConnected : IsSimplyConnected targetOpenChamber := by
  have hcontractible : ContractibleSpace targetFlatOpenChamber :=
    targetFlatOpenChamber_convex.contractibleSpace targetFlatOpenChamber_nonempty
  have hsimple : IsSimplyConnected targetFlatOpenChamber := by
    letI := hcontractible
    show SimplyConnectedSpace targetFlatOpenChamber
    infer_instance
  rw [← (verticalShear semicircleHeight continuous_semicircleHeight).isSimplyConnected_image,
    verticalShear_image_targetOpenChamber]
  exact hsimple

/-! ## The bounded cusp-exponential model -/

def cuspExponential (width : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * z / width)

theorem cuspExponential_ne_zero (width : ℝ) (z : ℂ) :
    cuspExponential width z ≠ 0 := Complex.exp_ne_zero _

theorem cuspExponential_continuous (width : ℝ) : Continuous (cuspExponential width) := by
  unfold cuspExponential
  fun_prop

theorem cuspExponential_differentiable (width : ℝ) (hwidth : width ≠ 0) :
    Differentiable ℂ (cuspExponential width) := by
  unfold cuspExponential
  fun_prop

theorem cuspExponential_isOpenMap (width : ℝ) (hwidth : width ≠ 0) :
    IsOpenMap (cuspExponential width) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero
    (2 * Real.pi * Complex.I / width)
    (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) (by exact_mod_cast hwidth))
  have heq : cuspExponential width = Complex.exp ∘ e := by
    funext z
    simp only [cuspExponential, Function.comp_apply, e, Homeomorph.smulOfNeZero_apply]
    ring
  rw [heq]
  exact Complex.isOpenMap_exp.comp e.isOpenMap

theorem cuspExponential_eq_iff_exists_int {width : ℝ} (hwidth : width ≠ 0)
    (z w : ℂ) :
    cuspExponential width z = cuspExponential width w ↔
      ∃ n : ℤ, z = w + n * width := by
  rw [cuspExponential, cuspExponential, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (mul_ne_zero hpi Complex.I_ne_zero)))
    field_simp [show (width : ℂ) ≠ 0 by exact_mod_cast hwidth] at hn ⊢
    linear_combination hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hw : (width : ℂ) ≠ 0 := by exact_mod_cast hwidth
    field_simp [hw]

theorem cuspExponential_injOn_re_interval {width l r : ℝ} (hwidth : 0 < width)
    (hspan : r - l < width) :
    Set.InjOn (cuspExponential width) {z : ℂ | l ≤ z.re ∧ z.re ≤ r} := by
  intro z hz w hw hzw
  obtain ⟨n, hn⟩ := (cuspExponential_eq_iff_exists_int hwidth.ne' z w).mp hzw
  have hre := congrArg Complex.re hn
  push_cast at hre
  norm_num [Complex.mul_re] at hre
  have hnlt : (n : ℝ) < 1 := by
    apply (mul_lt_mul_iff_of_pos_right hwidth).mp
    nlinarith [hz.1, hz.2, hw.1, hw.2]
  have hnneglt : -(n : ℝ) < 1 := by
    apply (mul_lt_mul_iff_of_pos_right hwidth).mp
    nlinarith [hz.1, hz.2, hw.1, hw.2]
  have hnzero : n = 0 := by
    have hnlt' : n < 1 := by exact_mod_cast hnlt
    have hnneglt' : -n < 1 := by exact_mod_cast hnneglt
    omega
  simpa [hnzero] using hn

theorem source_cuspExponential_injOn_closedStrip :
    Set.InjOn (cuspExponential (1 + Real.sqrt 2))
      {z : ℂ | -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2} := by
  apply cuspExponential_injOn_re_interval
  · positivity
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem target_cuspExponential_injOn_closedStrip :
    Set.InjOn (cuspExponential 1) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} := by
  apply cuspExponential_injOn_re_interval <;> norm_num

theorem sourceOpenChamber_isOpen : IsOpen sourceOpenChamber := by
  rw [show sourceOpenChamber =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩
          ({z : ℂ | 0 < z.im} ∩ {z : ℂ | 1 < normSq z})) by
    ext z
    simp [sourceOpenChamber]]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const Complex.continuous_normSq)))

theorem targetOpenChamber_isOpen : IsOpen targetOpenChamber := by
  rw [show targetOpenChamber =
      {z : ℂ | 0 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩
          ({z : ℂ | 0 < z.im} ∩ {z : ℂ | 1 < normSq z})) by
    ext z
    simp [targetOpenChamber]]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const Complex.continuous_normSq)))

def sourceBoundedChamber : Set ℂ :=
  cuspExponential (1 + Real.sqrt 2) '' sourceOpenChamber

def targetBoundedChamber : Set ℂ :=
  cuspExponential 1 '' targetOpenChamber

theorem sourceBoundedChamber_isOpen : IsOpen sourceBoundedChamber := by
  exact (cuspExponential_isOpenMap _ (by positivity)) _ sourceOpenChamber_isOpen

theorem targetBoundedChamber_isOpen : IsOpen targetBoundedChamber := by
  exact (cuspExponential_isOpenMap _ one_ne_zero) _ targetOpenChamber_isOpen

theorem source_cuspExponential_injOn :
    Set.InjOn (cuspExponential (1 + Real.sqrt 2)) sourceOpenChamber := by
  apply source_cuspExponential_injOn_closedStrip.mono
  rintro z ⟨hl, hr, -⟩
  exact ⟨hl.le, hr.le⟩

theorem target_cuspExponential_injOn :
    Set.InjOn (cuspExponential 1) targetOpenChamber := by
  apply target_cuspExponential_injOn_closedStrip.mono
  rintro z ⟨hl, hr, -⟩
  exact ⟨hl.le, hr.le⟩

theorem sourceBoundedChamber_isSimplyConnected :
    IsSimplyConnected sourceBoundedChamber := by
  exact TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn
    sourceOpenChamber_isOpen sourceOpenChamber_isSimplyConnected
    (cuspExponential_differentiable _ (by positivity)).differentiableOn
    source_cuspExponential_injOn

theorem targetBoundedChamber_isSimplyConnected :
    IsSimplyConnected targetBoundedChamber := by
  exact TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn
    targetOpenChamber_isOpen targetOpenChamber_isSimplyConnected
    (cuspExponential_differentiable _ one_ne_zero).differentiableOn
    target_cuspExponential_injOn

theorem norm_cuspExponential (width : ℝ) (hwidth : width ≠ 0) (z : ℂ) :
    ‖cuspExponential width z‖ = Real.exp (-2 * Real.pi * z.im / width) := by
  simpa only [cuspExponential, Function.Periodic.qParam] using
    Function.Periodic.norm_qParam width z

theorem sourceBoundedChamber_subset_ball : sourceBoundedChamber ⊆ Metric.ball 0 1 := by
  rintro w ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hwidth : 0 < 1 + Real.sqrt 2 := by positivity
  simpa only [cuspExponential, Function.Periodic.qParam] using
    Function.Periodic.norm_qParam_lt_one hwidth hz.2.2.1

theorem targetBoundedChamber_subset_ball : targetBoundedChamber ⊆ Metric.ball 0 1 := by
  rintro w ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  simpa only [cuspExponential, Function.Periodic.qParam] using
    Function.Periodic.norm_qParam_lt_one one_pos hz.2.2.1

theorem sourceBoundedChamber_isBounded : Bornology.IsBounded sourceBoundedChamber :=
  Metric.isBounded_ball.subset sourceBoundedChamber_subset_ball

theorem targetBoundedChamber_isBounded : Bornology.IsBounded targetBoundedChamber :=
  Metric.isBounded_ball.subset targetBoundedChamber_subset_ball


end SphereSixComplex.Periods.SourceChamberTopology
