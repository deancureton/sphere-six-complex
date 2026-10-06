module

public import DifferentialGeometry.Topology.Morse.Attachment.ModelCell
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

open scoped ContDiff _root_.Topology RealInnerProductSpace
open Set DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.ModelField

noncomputable section

variable {n k : ℕ} (hk : k ≤ n)

def negPartL : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i : Fin k => ContinuousLinearMap.proj (negIdx hk i))

def posPartL : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n - k)) :=
  (EuclideanSpace.equiv (Fin (n - k)) ℝ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun j : Fin (n - k) => ContinuousLinearMap.proj (posIdx hk j))

@[simp] theorem negPartL_apply (y : Fin n → ℝ) : negPartL hk y = negPart hk y := rfl
@[simp] theorem posPartL_apply (y : Fin n → ℝ) : posPartL hk y = posPart hk y := rfl

theorem negPart_apply (y : Fin n → ℝ) (i : Fin k) : negPart hk y i = y (negIdx hk i) := rfl
theorem posPart_apply (y : Fin n → ℝ) (j : Fin (n - k)) : posPart hk y j = y (posIdx hk j) := rfl

theorem negPart_smul (a : ℝ) (y : Fin n → ℝ) : negPart hk (a • y) = a • negPart hk y :=
  (negPartL hk).map_smul a y
theorem posPart_smul (a : ℝ) (y : Fin n → ℝ) : posPart hk (a • y) = a • posPart hk y :=
  (posPartL hk).map_smul a y
theorem negPart_add (y z : Fin n → ℝ) : negPart hk (y + z) = negPart hk y + negPart hk z :=
  (negPartL hk).map_add y z
theorem posPart_add (y z : Fin n → ℝ) : posPart hk (y + z) = posPart hk y + posPart hk z :=
  (posPartL hk).map_add y z
theorem negPart_neg (y : Fin n → ℝ) : negPart hk (-y) = -negPart hk y :=
  (negPartL hk).map_neg y
theorem posPart_neg (y : Fin n → ℝ) : posPart hk (-y) = -posPart hk y :=
  (posPartL hk).map_neg y

theorem negPart_recombine (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) :
    negPart hk (recombine hk a b) = a := by
  ext i; exact recombine_negPart hk a b i
theorem posPart_recombine (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) :
    posPart hk (recombine hk a b) = b := by
  ext j; exact recombine_posPart hk a b j

theorem morseNorm_sq_eq (y : Fin n → ℝ) :
    morseNorm n y ^ 2 = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ ^ 2 := rfl

theorem contDiff_morseNorm_sq : ContDiff ℝ ∞ (fun y : Fin n → ℝ => morseNorm n y ^ 2) := by
  have : (fun y : Fin n → ℝ => morseNorm n y ^ 2) =
      (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (ContinuousLinearMap.contDiff _)

def nfDeriv (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (posPart hk y)).comp (posPartL hk) - (innerSL ℝ (negPart hk y)).comp (negPartL hk)

theorem nfDeriv_apply (y w : Fin n → ℝ) :
    nfDeriv hk y w = ⟪posPart hk y, posPart hk w⟫ - ⟪negPart hk y, negPart hk w⟫ := rfl

theorem hasFDerivAt_nf (c : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (morseNormalForm hk c) (nfDeriv hk y) y := by
  have h : morseNormalForm hk c = fun y =>
      c + (1 / 2) * (‖posPartL hk y‖ ^ 2 - ‖negPartL hk y‖ ^ 2) := by
    funext y; exact morseNormalForm_split hk c y
  rw [h]
  have h1 := (posPartL hk).hasFDerivAt (x := y) |>.norm_sq
  have h2 := (negPartL hk).hasFDerivAt (x := y) |>.norm_sq
  have := ((h1.sub h2).const_mul (1 / 2)).const_add c
  convert this using 1
  ext w
  simp [nfDeriv, two_smul]
  ring

theorem fderiv_nf_apply (c : ℝ) (y w : Fin n → ℝ) :
    fderiv ℝ (morseNormalForm hk c) y w =
      ⟪posPart hk y, posPart hk w⟫ - ⟪negPart hk y, negPart hk w⟫ := by
  rw [(hasFDerivAt_nf hk c y).fderiv]; rfl

theorem contDiff_nf (c : ℝ) : ContDiff ℝ ∞ (morseNormalForm hk c) := by
  have h : morseNormalForm hk c = fun y =>
      c + (1 / 2) * (‖posPartL hk y‖ ^ 2 - ‖negPartL hk y‖ ^ 2) := by
    funext y; exact morseNormalForm_split hk c y
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun y : Fin n → ℝ => ‖posPartL hk y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (posPartL hk).contDiff
  have h2 : ContDiff ℝ ∞ (fun y : Fin n → ℝ => ‖negPartL hk y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (negPartL hk).contDiff
  exact contDiff_const.add (contDiff_const.mul (h1.sub h2))

def bump (r₀ : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.smoothTransition (1 - 4 * morseNorm n y ^ 2 / r₀ ^ 2)

theorem contDiff_bump (r₀ : ℝ) : ContDiff ℝ ∞ (bump (n := n) r₀) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_morseNorm_sq).div_const _))

theorem bump_nonneg (r₀ : ℝ) (y : Fin n → ℝ) : 0 ≤ bump r₀ y :=
  Real.smoothTransition.nonneg _

theorem bump_le_one (r₀ : ℝ) (y : Fin n → ℝ) : bump r₀ y ≤ 1 :=
  Real.smoothTransition.le_one _

theorem morseNorm_eq_zero_iff (y : Fin n → ℝ) : morseNorm n y = 0 ↔ y = 0 := by
  simp [morseNorm]

theorem morseNorm_nonneg (y : Fin n → ℝ) : 0 ≤ morseNorm n y := norm_nonneg _

theorem bump_eq_one_of_eq_zero (r₀ : ℝ) {y : Fin n → ℝ} (hy : morseNorm n y = 0) :
    bump r₀ y = 1 := by
  simp [bump, hy]

theorem bump_eq_zero {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ} (hy : r₀ / 2 ≤ morseNorm n y) :
    bump r₀ y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : r₀ ^ 2 / 4 ≤ morseNorm n y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy 2
    linarith [this]
  have h2 : 1 ≤ 4 * morseNorm n y ^ 2 / r₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

def thetaDen (r₀ : ℝ) (y : Fin n → ℝ) : ℝ := morseNorm n y ^ 2 + r₀ ^ 2 * bump r₀ y

theorem thetaDen_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) : 0 < thetaDen r₀ y := by
  unfold thetaDen
  by_cases hy : morseNorm n y = 0
  · rw [bump_eq_one_of_eq_zero r₀ hy, hy]; positivity
  · have : 0 < morseNorm n y ^ 2 := by positivity
    have := bump_nonneg r₀ y
    positivity

theorem contDiff_thetaDen (r₀ : ℝ) : ContDiff ℝ ∞ (thetaDen (n := n) r₀) :=
  contDiff_morseNorm_sq.add (contDiff_const.mul (contDiff_bump r₀))

def theta (r₀ : ℝ) (y : Fin n → ℝ) : ℝ := (thetaDen r₀ y)⁻¹

theorem theta_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) : 0 < theta r₀ y :=
  inv_pos.2 (thetaDen_pos hr₀ y)

theorem contDiff_theta {r₀ : ℝ} (hr₀ : 0 < r₀) : ContDiff ℝ ∞ (theta (n := n) r₀) :=
  (contDiff_thetaDen r₀).inv fun y => (thetaDen_pos hr₀ y).ne'

theorem theta_eq {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ} (hy : r₀ / 2 ≤ morseNorm n y) :
    theta r₀ y = (morseNorm n y ^ 2)⁻¹ := by
  simp [theta, thetaDen, bump_eq_zero hr₀ hy]

theorem theta_mul_sq {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ} (hy : r₀ / 2 ≤ morseNorm n y) :
    theta r₀ y * morseNorm n y ^ 2 = 1 := by
  rw [theta_eq hr₀ hy]
  have : 0 < morseNorm n y := by linarith
  field_simp

theorem continuous_theta {r₀ : ℝ} (hr₀ : 0 < r₀) : Continuous (theta (n := n) r₀) :=
  (contDiff_theta hr₀).continuous

theorem thetaDen_le (r₀ : ℝ) (y : Fin n → ℝ) : thetaDen r₀ y ≤ morseNorm n y ^ 2 + r₀ ^ 2 := by
  unfold thetaDen
  have := bump_le_one r₀ y
  have := sq_nonneg r₀
  nlinarith

theorem theta_ge_of_le {r₀ R : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ} (hy : morseNorm n y ≤ R) :
    (R ^ 2 + r₀ ^ 2)⁻¹ ≤ theta r₀ y := by
  have h1 := thetaDen_pos hr₀ y
  have h2 := thetaDen_le r₀ y
  have h3 : morseNorm n y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (morseNorm_nonneg y) hy 2
  exact inv_anti₀ h1 (by linarith)

def modelDesc (k : ℕ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i.val < k then y i else -(y i)

theorem negPart_modelDesc (y : Fin n → ℝ) : negPart hk (modelDesc k y) = negPart hk y := by
  ext i
  have : (negIdx hk i).val < k := by simp [negIdx]
  simp [negPart_apply, modelDesc, this]

theorem posPart_modelDesc (y : Fin n → ℝ) : posPart hk (modelDesc k y) = -posPart hk y := by
  ext j
  have : ¬ (posIdx hk j).val < k := by simp [posIdx]
  simp [posPart_apply, modelDesc, this]

theorem contDiff_modelDesc : ContDiff ℝ ∞ (modelDesc (n := n) k) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i.val < k
  · simp only [modelDesc, h, ite_true]; exact contDiff_apply ℝ ℝ i
  · simp only [modelDesc, h, ite_false]; exact (contDiff_apply ℝ ℝ i).neg

theorem modelDesc_zero : modelDesc k (0 : Fin n → ℝ) = 0 := by
  ext i; simp [modelDesc]

def modelField (k : ℕ) (r₀ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  theta r₀ y • modelDesc k y

theorem contDiff_modelField {r₀ : ℝ} (hr₀ : 0 < r₀) : ContDiff ℝ ∞ (modelField (n := n) k r₀) :=
  (contDiff_theta hr₀).smul contDiff_modelDesc

theorem modelField_zero (r₀ : ℝ) : modelField k r₀ (0 : Fin n → ℝ) = 0 := by
  simp [modelField, modelDesc_zero]

theorem negPart_modelField (r₀ : ℝ) (y : Fin n → ℝ) :
    negPart hk (modelField k r₀ y) = theta r₀ y • negPart hk y := by
  rw [modelField, negPart_smul, negPart_modelDesc]

theorem posPart_modelField (r₀ : ℝ) (y : Fin n → ℝ) :
    posPart hk (modelField k r₀ y) = -(theta r₀ y • posPart hk y) := by
  rw [modelField, posPart_smul, posPart_modelDesc, smul_neg]

theorem fderiv_nf_modelField (c r₀ : ℝ) (y : Fin n → ℝ) :
    fderiv ℝ (morseNormalForm hk c) y (modelField k r₀ y) =
      -(theta r₀ y * morseNorm n y ^ 2) := by
  rw [fderiv_nf_apply, negPart_modelField, posPart_modelField, inner_neg_right,
    inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    morseNorm_sq_eq_negPart_add_posPart hk]
  ring

theorem fderiv_nf_modelField_eq_neg_one (c : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ}
    (hy : r₀ / 2 ≤ morseNorm n y) :
    fderiv ℝ (morseNormalForm hk c) y (modelField k r₀ y) = -1 := by
  rw [fderiv_nf_modelField, theta_mul_sq hr₀ hy]

theorem fderiv_nf_modelField_nonpos (c : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) :
    fderiv ℝ (morseNormalForm hk c) y (modelField k r₀ y) ≤ 0 := by
  rw [fderiv_nf_modelField]
  have := theta_pos hr₀ y
  have := sq_nonneg (morseNorm n y)
  nlinarith

theorem fderiv_nf_modelField_neg (c : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ} (hy : y ≠ 0) :
    fderiv ℝ (morseNormalForm hk c) y (modelField k r₀ y) < 0 := by
  rw [fderiv_nf_modelField]
  have h1 := theta_pos hr₀ y
  have h2 : 0 < morseNorm n y := by
    rcases (morseNorm_nonneg y).lt_or_eq with h | h
    · exact h
    · exact absurd ((morseNorm_eq_zero_iff y).1 h.symm) hy
  have : 0 < theta r₀ y * morseNorm n y ^ 2 := by positivity
  linarith

section Curve

variable {r₀ : ℝ} {γ : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}

theorem hasDerivAt_negPart_curve
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => negPart hk (γ s)) (theta r₀ (γ t) • negPart hk (γ t)) t := by
  have := (negPartL hk).hasFDerivAt.comp_hasDerivAt t (hγ t ht)
  rw [negPartL_apply, negPart_modelField] at this
  exact this

theorem hasDerivAt_posPart_curve
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => posPart hk (γ s)) (-(theta r₀ (γ t) • posPart hk (γ t))) t := by
  have := (posPartL hk).hasFDerivAt.comp_hasDerivAt t (hγ t ht)
  rw [posPartL_apply, posPart_modelField] at this
  exact this

theorem hasDerivAt_normSq_negPart_curve
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => ‖negPart hk (γ s)‖ ^ 2)
      (2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2) t := by
  have := (hasDerivAt_negPart_curve hk hγ ht).norm_sq
  convert this using 1
  rw [inner_smul_right, real_inner_self_eq_norm_sq]; ring

theorem hasDerivAt_normSq_posPart_curve
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => ‖posPart hk (γ s)‖ ^ 2)
      (-(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2)) t := by
  have := (hasDerivAt_posPart_curve hk hγ ht).norm_sq
  convert this using 1
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]; ring

theorem hasDerivAt_nf_curve (c : ℝ)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => morseNormalForm hk c (γ s))
      (-(theta r₀ (γ t) * morseNorm n (γ t) ^ 2)) t := by
  have := (hasFDerivAt_nf hk c (γ t)).comp_hasDerivAt t (hγ t ht)
  rw [← fderiv_nf_modelField hk c r₀ (γ t), (hasFDerivAt_nf hk c (γ t)).fderiv]
  exact this

theorem continuousOn_curve (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    ContinuousOn γ (Icc t₀ t₁) :=
  HasDerivAt.continuousOn hγ

theorem normSq_negPart_mul_posPart_const
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    ∀ t ∈ Icc t₀ t₁, ‖negPart hk (γ t)‖ ^ 2 * ‖posPart hk (γ t)‖ ^ 2 =
      ‖negPart hk (γ t₀)‖ ^ 2 * ‖posPart hk (γ t₀)‖ ^ 2 := by
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => ‖negPart hk (γ s)‖ ^ 2 * ‖posPart hk (γ s)‖ ^ 2) 0 t := by
    intro t ht
    have := (hasDerivAt_normSq_negPart_curve hk hγ ht).mul
      (hasDerivAt_normSq_posPart_curve hk hγ ht)
    convert this using 1; ring
  refine constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd) fun t ht => ?_
  exact (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt

theorem normSq_negPart_monotoneOn {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    MonotoneOn (fun t => ‖negPart hk (γ t)‖ ^ 2) (Icc t₀ t₁) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ t₁)
    (f' := fun t => 2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_normSq_negPart_curve hk hγ ht)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_normSq_negPart_curve hk hγ (Ioo_subset_Icc_self ht)).hasDerivWithinAt
  · have := theta_pos hr₀ (γ t)
    positivity

theorem normSq_posPart_antitoneOn {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    AntitoneOn (fun t => ‖posPart hk (γ t)‖ ^ 2) (Icc t₀ t₁) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
    (f' := fun t => -(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2))
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_normSq_posPart_curve hk hγ ht)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_normSq_posPart_curve hk hγ (Ioo_subset_Icc_self ht)).hasDerivWithinAt
  · have := theta_pos hr₀ (γ t)
    have := sq_nonneg ‖posPart hk (γ t)‖
    nlinarith

theorem nf_antitoneOn (c : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    AntitoneOn (fun t => morseNormalForm hk c (γ t)) (Icc t₀ t₁) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
    (f' := fun t => -(theta r₀ (γ t) * morseNorm n (γ t) ^ 2))
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_nf_curve hk c hγ ht)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_nf_curve hk c hγ (Ioo_subset_Icc_self ht)).hasDerivWithinAt
  · have := theta_pos hr₀ (γ t)
    have := sq_nonneg (morseNorm n (γ t))
    nlinarith

theorem nf_curve_eq_sub (c : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hunit : ∀ t ∈ Icc t₀ t₁, r₀ / 2 ≤ morseNorm n (γ t)) :
    ∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) = morseNormalForm hk c (γ t₀) - (t - t₀) := by
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => morseNormalForm hk c (γ s) + s) 0 t := by
    intro t ht
    have h2 := (hasDerivAt_nf_curve hk c hγ ht).add (hasDerivAt_id' (x := t))
    rw [theta_mul_sq hr₀ (hunit t ht), show (-1 : ℝ) + 1 = 0 by norm_num] at h2
    exact h2
  have := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  intro t ht
  have h := this t ht
  linarith

theorem negPart_eq_zero_of_right {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (h1 : negPart hk (γ t₁) = 0) (ht₀₁ : t₀ ≤ t₁) :
    ∀ t ∈ Icc t₀ t₁, negPart hk (γ t) = 0 := by
  intro t ht
  have hm := normSq_negPart_monotoneOn hk hr₀ hγ ht (right_mem_Icc.2 ht₀₁) ht.2
  simp only [h1, norm_zero] at hm
  have := sq_nonneg ‖negPart hk (γ t)‖
  have : ‖negPart hk (γ t)‖ ^ 2 = 0 := by linarith
  simpa using this

theorem posPart_eq_zero_of_left {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (h0 : posPart hk (γ t₀) = 0) (ht₀₁ : t₀ ≤ t₁) :
    ∀ t ∈ Icc t₀ t₁, posPart hk (γ t) = 0 := by
  intro t ht
  have hm := normSq_posPart_antitoneOn hk hr₀ hγ (left_mem_Icc.2 ht₀₁) ht ht.1
  simp only [h0, norm_zero] at hm
  have := sq_nonneg ‖posPart hk (γ t)‖
  have : ‖posPart hk (γ t)‖ ^ 2 = 0 := by linarith
  simpa using this

theorem exists_theta_bound {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc t₀ t₁, theta r₀ (γ t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_theta hr₀).comp_continuousOn (continuousOn_curve hγ))
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  exact le_trans (le_abs_self _) (le_trans (hC t ht) (le_max_left _ _))

theorem negPart_eq_zero_of_left {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (h0 : negPart hk (γ t₀) = 0) (ht₀₁ : t₀ ≤ t₁) :
    ∀ t ∈ Icc t₀ t₁, negPart hk (γ t) = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound hr₀ hγ
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => ‖negPart hk (γ s)‖ ^ 2 * Real.exp (-(2 * C) * s))
      ((2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2) * Real.exp (-(2 * C) * t) +
        ‖negPart hk (γ t)‖ ^ 2 * (Real.exp (-(2 * C) * t) * (-(2 * C)))) t := by
    intro t ht
    have he : HasDerivAt (fun s => Real.exp (-(2 * C) * s))
        (Real.exp (-(2 * C) * t) * (-(2 * C))) t := by
      convert ((hasDerivAt_id' (x := t)).const_mul (-(2 * C))).exp using 1
      ring
    exact (hasDerivAt_normSq_negPart_curve hk hγ ht).mul he
  have hanti : AntitoneOn (fun s => ‖negPart hk (γ s)‖ ^ 2 * Real.exp (-(2 * C) * s))
      (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
      (f' := fun t => (2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2) * Real.exp (-(2 * C) * t) +
        ‖negPart hk (γ t)‖ ^ 2 * (Real.exp (-(2 * C) * t) * (-(2 * C))))
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have h1 := hC t (Ioo_subset_Icc_self ht)
      have h2 := Real.exp_pos (-(2 * C) * t)
      have h3 := sq_nonneg ‖negPart hk (γ t)‖
      have : (2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2) * Real.exp (-(2 * C) * t) +
          ‖negPart hk (γ t)‖ ^ 2 * (Real.exp (-(2 * C) * t) * (-(2 * C))) =
          2 * (theta r₀ (γ t) - C) * (‖negPart hk (γ t)‖ ^ 2 * Real.exp (-(2 * C) * t)) := by
        ring
      rw [this]
      have : theta r₀ (γ t) - C ≤ 0 := by linarith
      have : 0 ≤ ‖negPart hk (γ t)‖ ^ 2 * Real.exp (-(2 * C) * t) := by positivity
      nlinarith
  intro t ht
  have hm := hanti (left_mem_Icc.2 ht₀₁) ht ht.1
  simp only [h0, norm_zero] at hm
  have h2 := Real.exp_pos (-(2 * C) * t)
  have h3 := sq_nonneg ‖negPart hk (γ t)‖
  have : ‖negPart hk (γ t)‖ ^ 2 * Real.exp (-(2 * C) * t) = 0 := by
    have : 0 ≤ ‖negPart hk (γ t)‖ ^ 2 * Real.exp (-(2 * C) * t) := by positivity
    have h4 : (0 : ℝ) ^ 2 * Real.exp (-(2 * C) * t₀) = 0 := by simp
    linarith
  rcases mul_eq_zero.1 this with h | h
  · simpa using h
  · exact absurd h h2.ne'

theorem posPart_eq_zero_of_right {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (h1 : posPart hk (γ t₁) = 0) (ht₀₁ : t₀ ≤ t₁) :
    ∀ t ∈ Icc t₀ t₁, posPart hk (γ t) = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound hr₀ hγ
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => ‖posPart hk (γ s)‖ ^ 2 * Real.exp ((2 * C) * s))
      ((-(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2)) * Real.exp ((2 * C) * t) +
        ‖posPart hk (γ t)‖ ^ 2 * (Real.exp ((2 * C) * t) * (2 * C))) t := by
    intro t ht
    have he : HasDerivAt (fun s => Real.exp ((2 * C) * s))
        (Real.exp ((2 * C) * t) * (2 * C)) t := by
      convert ((hasDerivAt_id' (x := t)).const_mul (2 * C)).exp using 1
      ring
    exact (hasDerivAt_normSq_posPart_curve hk hγ ht).mul he
  have hmono : MonotoneOn (fun s => ‖posPart hk (γ s)‖ ^ 2 * Real.exp ((2 * C) * s))
      (Icc t₀ t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ t₁)
      (f' := fun t => (-(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2)) * Real.exp ((2 * C) * t) +
        ‖posPart hk (γ t)‖ ^ 2 * (Real.exp ((2 * C) * t) * (2 * C)))
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have h1 := hC t (Ioo_subset_Icc_self ht)
      have h2 := Real.exp_pos ((2 * C) * t)
      have h3 := sq_nonneg ‖posPart hk (γ t)‖
      have : (-(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2)) * Real.exp ((2 * C) * t) +
          ‖posPart hk (γ t)‖ ^ 2 * (Real.exp ((2 * C) * t) * (2 * C)) =
          2 * (C - theta r₀ (γ t)) * (‖posPart hk (γ t)‖ ^ 2 * Real.exp ((2 * C) * t)) := by
        ring
      rw [this]
      have : 0 ≤ C - theta r₀ (γ t) := by linarith
      have : 0 ≤ ‖posPart hk (γ t)‖ ^ 2 * Real.exp ((2 * C) * t) := by positivity
      positivity
  intro t ht
  have hm := hmono ht (right_mem_Icc.2 ht₀₁) ht.2
  simp only [h1, norm_zero] at hm
  have h2 := Real.exp_pos ((2 * C) * t)
  have h3 := sq_nonneg ‖posPart hk (γ t)‖
  have : ‖posPart hk (γ t)‖ ^ 2 * Real.exp ((2 * C) * t) = 0 := by
    have : 0 ≤ ‖posPart hk (γ t)‖ ^ 2 * Real.exp ((2 * C) * t) := by positivity
    have h4 : (0 : ℝ) ^ 2 * Real.exp ((2 * C) * t₁) = 0 := by simp
    linarith
  rcases mul_eq_zero.1 this with h | h
  · simpa using h
  · exact absurd h h2.ne'

theorem normSq_negPart_ge_linear {r₀ θ₀ : ℝ} (hr₀ : 0 < r₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hθ : ∀ t ∈ Icc t₀ t₁, θ₀ ≤ theta r₀ (γ t)) :
    ∀ t ∈ Icc t₀ t₁, ‖negPart hk (γ t₀)‖ ^ 2 + 2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * (t - t₀) ≤
      ‖negPart hk (γ t)‖ ^ 2 := by
  have hmono := normSq_negPart_monotoneOn hk hr₀ hγ
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => ‖negPart hk (γ s)‖ ^ 2 - 2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * s)
      (2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2 - 2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2) t := by
    intro t ht
    have := (hasDerivAt_normSq_negPart_curve hk hγ ht).sub
      ((hasDerivAt_id' (x := t)).const_mul (2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2))
    rw [mul_one] at this
    exact this
  have hm : MonotoneOn
      (fun s => ‖negPart hk (γ s)‖ ^ 2 - 2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * s) (Icc t₀ t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ t₁)
      (f' := fun t => 2 * theta r₀ (γ t) * ‖negPart hk (γ t)‖ ^ 2 -
        2 * θ₀ * ‖negPart hk (γ t₀)‖ ^ 2)
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have ht' := Ioo_subset_Icc_self ht
      have h1 := hθ t ht'
      have h2 := hmono (left_mem_Icc.2 (ht'.1.trans ht'.2)) ht' ht'.1
      simp only at h2
      have h3 := sq_nonneg ‖negPart hk (γ t₀)‖
      have h4 : 0 ≤ theta r₀ (γ t) := (theta_pos hr₀ _).le
      nlinarith [mul_le_mul h1 h2 h3 h4]
  intro t ht
  have := hm (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
  simp only at this
  linarith

theorem nf_le_linear (c : ℝ) {r₀ θ₀ : ℝ} (hr₀ : 0 < r₀) (hθ₀ : 0 ≤ θ₀)
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hθ : ∀ t ∈ Icc t₀ t₁, θ₀ ≤ theta r₀ (γ t)) :
    ∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) ≤
      morseNormalForm hk c (γ t₀) - θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * (t - t₀) := by
  have hmono := normSq_negPart_monotoneOn hk hr₀ hγ
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => morseNormalForm hk c (γ s) + θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * s)
      (-(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + θ₀ * ‖negPart hk (γ t₀)‖ ^ 2) t := by
    intro t ht
    have := (hasDerivAt_nf_curve hk c hγ ht).add
      ((hasDerivAt_id' (x := t)).const_mul (θ₀ * ‖negPart hk (γ t₀)‖ ^ 2))
    rw [mul_one] at this
    exact this
  have hm : AntitoneOn
      (fun s => morseNormalForm hk c (γ s) + θ₀ * ‖negPart hk (γ t₀)‖ ^ 2 * s) (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
      (f' := fun t => -(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + θ₀ * ‖negPart hk (γ t₀)‖ ^ 2)
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have ht' := Ioo_subset_Icc_self ht
      have h1 := hθ t ht'
      have h2 := hmono (left_mem_Icc.2 (ht'.1.trans ht'.2)) ht' ht'.1
      simp only at h2
      have h3 := sq_nonneg ‖negPart hk (γ t₀)‖
      have h4 : 0 ≤ theta r₀ (γ t) := (theta_pos hr₀ _).le
      have h5 := morseNorm_sq_eq_negPart_add_posPart hk (γ t)
      have h6 := sq_nonneg ‖posPart hk (γ t)‖
      nlinarith [mul_le_mul h1 h2 h3 h4]
  intro t ht
  have := hm (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
  simp only at this
  linarith

theorem hasDerivAt_comp_neg {F : (Fin n → ℝ) → Fin n → ℝ} {γ : ℝ → Fin n → ℝ} {s : ℝ}
    (h : HasDerivAt γ (-(F (γ (-s)))) (-s)) :
    HasDerivAt (fun s => γ (-s)) (F (γ (-s))) s := by
  have := h.scomp s (hasDerivAt_neg s)
  rw [neg_one_smul, neg_neg] at this
  exact this

theorem hasDerivAt_comp_neg' {F : (Fin n → ℝ) → Fin n → ℝ} {γ : ℝ → Fin n → ℝ} {s : ℝ}
    (h : HasDerivAt γ (F (γ (-s))) (-s)) :
    HasDerivAt (fun s => γ (-s)) (-(F (γ (-s)))) s := by
  have := h.scomp s (hasDerivAt_neg s)
  rw [neg_one_smul] at this
  exact this

end Curve

theorem exit_bound {ε r' a b : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlevel : a ^ 2 - b ^ 2 = 2 * ε) (hprod : a * b ≤ r' ^ 2) : b ^ 2 ≤ r' ^ 4 / (2 * ε) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : 2 * ε ≤ a ^ 2 := by nlinarith [sq_nonneg b]
  have h2 : (a * b) ^ 2 ≤ (r' ^ 2) ^ 2 := by
    have := mul_nonneg ha hb
    exact pow_le_pow_left₀ this hprod 2
  nlinarith [sq_nonneg b]

def recombineL : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k))) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    if h : i.val < k then
      (EuclideanSpace.proj (⟨i.val, h⟩ : Fin k)).comp (ContinuousLinearMap.fst ℝ _ _)
    else
      (EuclideanSpace.proj (⟨i.val - k, by have := i.isLt; omega⟩ : Fin (n - k))).comp
        (ContinuousLinearMap.snd ℝ _ _)

theorem recombineL_apply (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) :
    recombineL hk (a, b) = recombine hk a b := by
  ext i
  by_cases h : i.val < k
  · simp [recombineL, recombine, h]
  · simp [recombineL, recombine, h]

def scaledNegativePart (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin k) := ‖posPart hk y‖ • negPart hk y

theorem continuous_scaledNegativePart : Continuous (scaledNegativePart hk) :=
  ((posPartL hk).continuous.norm).smul (negPartL hk).continuous

theorem contDiffOn_scaledNegativePart : ContDiffOn ℝ ∞ (scaledNegativePart hk) {y | posPart hk y ≠ 0} :=
  ((posPartL hk).contDiff.contDiffOn.norm ℝ fun _ hy => hy).smul
    (negPartL hk).contDiff.contDiffOn

theorem contDiffAt_scaledNegativePart {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) : ContDiffAt ℝ ∞ (scaledNegativePart hk) y :=
  (contDiffOn_scaledNegativePart hk).contDiffAt
    (((posPartL hk).continuous.isOpen_preimage _ isOpen_compl_singleton).mem_nhds hy)

theorem scaledNegativePart_eq_zero_iff {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    scaledNegativePart hk y = 0 ↔ negPart hk y = 0 := by
  simp [scaledNegativePart, norm_eq_zero, hy]

theorem norm_scaledNegativePart (y : Fin n → ℝ) : ‖scaledNegativePart hk y‖ = ‖posPart hk y‖ * ‖negPart hk y‖ := by
  simp [scaledNegativePart, norm_smul]

theorem negPart_eq_of_scaledNegativePart_eq (c : ℝ) {y₁ y₂ : Fin n → ℝ}
    (hlevel : morseNormalForm hk c y₁ = morseNormalForm hk c y₂)
    (hv₁ : posPart hk y₁ ≠ 0) (hv₂ : posPart hk y₂ ≠ 0) (hJ : scaledNegativePart hk y₁ = scaledNegativePart hk y₂) :
    negPart hk y₁ = negPart hk y₂ := by
  rw [morseNormalForm_split, morseNormalForm_split] at hlevel
  have hn : ‖scaledNegativePart hk y₁‖ = ‖scaledNegativePart hk y₂‖ := by rw [hJ]
  rw [norm_scaledNegativePart, norm_scaledNegativePart] at hn
  have hv₁' : 0 < ‖posPart hk y₁‖ := norm_pos_iff.2 hv₁
  have hv₂' : 0 < ‖posPart hk y₂‖ := norm_pos_iff.2 hv₂
  have hu₁ := norm_nonneg (negPart hk y₁)
  have hu₂ := norm_nonneg (negPart hk y₂)
  have hueq : ‖negPart hk y₁‖ = ‖negPart hk y₂‖ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hvlt : ‖posPart hk y₁‖ < ‖posPart hk y₂‖ := by
        have : ‖posPart hk y₁‖ ^ 2 < ‖posPart hk y₂‖ ^ 2 := by
          have := pow_lt_pow_left₀ h hu₁ two_ne_zero
          linarith
        exact (pow_lt_pow_iff_left₀ hv₁'.le hv₂'.le two_ne_zero).1 this
      have : ‖posPart hk y₁‖ * ‖negPart hk y₁‖ < ‖posPart hk y₂‖ * ‖negPart hk y₂‖ := by
        calc ‖posPart hk y₁‖ * ‖negPart hk y₁‖ ≤ ‖posPart hk y₂‖ * ‖negPart hk y₁‖ :=
              mul_le_mul_of_nonneg_right hvlt.le hu₁
          _ < ‖posPart hk y₂‖ * ‖negPart hk y₂‖ := mul_lt_mul_of_pos_left h hv₂'
      linarith
    · have hvlt : ‖posPart hk y₂‖ < ‖posPart hk y₁‖ := by
        have : ‖posPart hk y₂‖ ^ 2 < ‖posPart hk y₁‖ ^ 2 := by
          have := pow_lt_pow_left₀ h hu₂ two_ne_zero
          linarith
        exact (pow_lt_pow_iff_left₀ hv₂'.le hv₁'.le two_ne_zero).1 this
      have : ‖posPart hk y₂‖ * ‖negPart hk y₂‖ < ‖posPart hk y₁‖ * ‖negPart hk y₁‖ := by
        calc ‖posPart hk y₂‖ * ‖negPart hk y₂‖ ≤ ‖posPart hk y₁‖ * ‖negPart hk y₂‖ :=
              mul_le_mul_of_nonneg_right hvlt.le hu₂
          _ < ‖posPart hk y₁‖ * ‖negPart hk y₁‖ := mul_lt_mul_of_pos_left h hv₁'
      linarith
  have hveq : ‖posPart hk y₁‖ = ‖posPart hk y₂‖ := by
    have : ‖posPart hk y₁‖ ^ 2 = ‖posPart hk y₂‖ ^ 2 := by rw [hueq] at hlevel; linarith
    exact (pow_left_inj₀ hv₁'.le hv₂'.le two_ne_zero).1 this
  simp only [scaledNegativePart] at hJ
  rw [hveq] at hJ
  exact smul_right_injective _ hv₂'.ne' hJ

def scaledNegativePartDeriv (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ((‖posPart hk y‖⁻¹) • ((innerSL ℝ (posPart hk y)).comp (posPartL hk))).smulRight
    (negPart hk y) + ‖posPart hk y‖ • negPartL hk

theorem scaledNegativePartDeriv_apply (y w : Fin n → ℝ) :
    scaledNegativePartDeriv hk y w = (‖posPart hk y‖⁻¹ * ⟪posPart hk y, posPart hk w⟫) • negPart hk y +
      ‖posPart hk y‖ • negPart hk w := rfl

theorem hasFDerivAt_norm_posPart {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    HasFDerivAt (fun y => ‖posPart hk y‖)
      ((‖posPart hk y‖⁻¹) • ((innerSL ℝ (posPart hk y)).comp (posPartL hk))) y := by
  have h1 := ((posPartL hk).hasFDerivAt (x := y)).norm_sq
  have h2 : ‖posPartL hk y‖ ^ 2 ≠ 0 := by
    rw [posPartL_apply]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have h3 := h1.sqrt h2
  have h4 : (fun y => √(‖posPartL hk y‖ ^ 2)) = fun y => ‖posPart hk y‖ := by
    funext y; rw [Real.sqrt_sq (norm_nonneg _)]; rfl
  rw [h4] at h3
  have h5 : (1 / (2 * √(‖posPartL hk y‖ ^ 2))) •
      (2 • (innerSL ℝ (posPartL hk y)).comp (posPartL hk)) =
      (‖posPart hk y‖⁻¹) • ((innerSL ℝ (posPart hk y)).comp (posPartL hk)) := by
    rw [Real.sqrt_sq (norm_nonneg _), posPartL_apply]
    ext w
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    have : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    field_simp
  rw [h5] at h3
  exact h3

theorem hasFDerivAt_scaledNegativePart {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    HasFDerivAt (scaledNegativePart hk) (scaledNegativePartDeriv hk y) y := by
  have := (hasFDerivAt_norm_posPart hk hy).smul ((negPartL hk).hasFDerivAt (x := y))
  convert this using 1
  all_goals first | rfl | (unfold scaledNegativePartDeriv; exact add_comm _ _)

theorem fderiv_scaledNegativePart_apply {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) (w : Fin n → ℝ) :
    fderiv ℝ (scaledNegativePart hk) y w = (‖posPart hk y‖⁻¹ * ⟪posPart hk y, posPart hk w⟫) • negPart hk y +
      ‖posPart hk y‖ • negPart hk w := by
  rw [(hasFDerivAt_scaledNegativePart hk hy).fderiv]; rfl

theorem fderiv_scaledNegativePart_modelField (r₀ : ℝ) {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    fderiv ℝ (scaledNegativePart hk) y (modelField k r₀ y) = 0 := by
  rw [fderiv_scaledNegativePart_apply hk hy, negPart_modelField, posPart_modelField, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [smul_smul, ← add_smul]
  convert zero_smul ℝ (negPart hk y) using 2
  field_simp
  ring

def lam (z : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) : ℝ :=
  ⟪negPart hk y, z⟫ / (‖posPart hk y‖ * (‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2))

theorem contDiffOn_lam (z : EuclideanSpace ℝ (Fin k)) :
    ContDiffOn ℝ ∞ (lam hk z) {y | posPart hk y ≠ 0} := by
  have hnum : ContDiffOn ℝ ∞ (fun y : Fin n → ℝ => ⟪negPart hk y, z⟫) {y | posPart hk y ≠ 0} :=
    ((negPartL hk).contDiff.contDiffOn.inner ℝ contDiffOn_const)
  have hden : ContDiffOn ℝ ∞ (fun y : Fin n → ℝ =>
      ‖posPart hk y‖ * (‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2)) {y | posPart hk y ≠ 0} :=
    ((posPartL hk).contDiff.contDiffOn.norm ℝ fun _ hy => hy).mul
      ((negPartL hk).contDiff.contDiffOn.norm_sq ℝ |>.add
        ((posPartL hk).contDiff.contDiffOn.norm_sq ℝ))
  refine hnum.div hden fun y hy => ?_
  have h1 : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h2 : 0 < ‖posPart hk y‖ ^ 2 := by positivity
  have h3 : 0 < ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by positivity
  exact mul_ne_zero h1 h3.ne'

def levelTangentLift (z : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) : Fin n → ℝ :=
  recombineL hk ((‖posPart hk y‖⁻¹) • (z - (lam hk z y * ‖posPart hk y‖) • negPart hk y),
    lam hk z y • posPart hk y)

theorem negPart_levelTangentLift (z : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) :
    negPart hk (levelTangentLift hk z y) =
      (‖posPart hk y‖⁻¹) • (z - (lam hk z y * ‖posPart hk y‖) • negPart hk y) := by
  rw [levelTangentLift, recombineL_apply, negPart_recombine]

theorem posPart_levelTangentLift (z : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) :
    posPart hk (levelTangentLift hk z y) = lam hk z y • posPart hk y := by
  rw [levelTangentLift, recombineL_apply, posPart_recombine]

theorem contDiffOn_levelTangentLift (z : EuclideanSpace ℝ (Fin k)) :
    ContDiffOn ℝ ∞ (levelTangentLift hk z) {y | posPart hk y ≠ 0} := by
  have hnorm : ContDiffOn ℝ ∞ (fun y : Fin n → ℝ => ‖posPart hk y‖) {y | posPart hk y ≠ 0} :=
    (posPartL hk).contDiff.contDiffOn.norm ℝ fun _ hy => hy
  have h1 : ContDiffOn ℝ ∞ (fun y : Fin n → ℝ =>
      (‖posPart hk y‖⁻¹) • (z - (lam hk z y * ‖posPart hk y‖) • negPart hk y))
      {y | posPart hk y ≠ 0} :=
    (hnorm.inv fun y hy => norm_ne_zero_iff.2 hy).smul
      (contDiffOn_const.sub (((contDiffOn_lam hk z).mul hnorm).smul
        (negPartL hk).contDiff.contDiffOn))
  have h2 : ContDiffOn ℝ ∞ (fun y : Fin n → ℝ => lam hk z y • posPart hk y)
      {y | posPart hk y ≠ 0} :=
    (contDiffOn_lam hk z).smul (posPartL hk).contDiff.contDiffOn
  exact (recombineL hk).contDiff.comp_contDiffOn (h1.prodMk h2)

theorem lam_mul {z : EuclideanSpace ℝ (Fin k)} {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    lam hk z y * (‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2) =
      ‖posPart hk y‖⁻¹ * ⟪negPart hk y, z⟫ := by
  have h1 : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h3 : 0 < ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by positivity
  rw [lam]
  field_simp

theorem fderiv_nf_levelTangentLift (c : ℝ) (z : EuclideanSpace ℝ (Fin k)) {y : Fin n → ℝ}
    (hy : posPart hk y ≠ 0) :
    fderiv ℝ (morseNormalForm hk c) y (levelTangentLift hk z y) = 0 := by
  rw [fderiv_nf_apply, negPart_levelTangentLift, posPart_levelTangentLift, inner_smul_right, inner_smul_right,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h2 := lam_mul hk (z := z) hy
  have e2 : ‖posPart hk y‖⁻¹ * ‖posPart hk y‖ = 1 := inv_mul_cancel₀ h1
  linear_combination h2 + lam hk z y * ‖negPart hk y‖ ^ 2 * e2

theorem fderiv_scaledNegativePart_levelTangentLift (z : EuclideanSpace ℝ (Fin k)) {y : Fin n → ℝ} (hy : posPart hk y ≠ 0) :
    fderiv ℝ (scaledNegativePart hk) y (levelTangentLift hk z y) = z := by
  rw [fderiv_scaledNegativePart_apply hk hy, negPart_levelTangentLift, posPart_levelTangentLift, inner_smul_right, real_inner_self_eq_norm_sq]
  have h1 : ‖posPart hk y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have e2 : ‖posPart hk y‖ * ‖posPart hk y‖⁻¹ = 1 := mul_inv_cancel₀ h1
  simp only [smul_smul, smul_sub]
  linear_combination (norm := module) e2 • z

def levelCutoff (c ε : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t - (c + ε / 2)) / (ε / 2))

theorem contDiff_levelCutoff (c ε : ℝ) : ContDiff ℝ ∞ (levelCutoff c ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem levelCutoff_nonneg (c ε t : ℝ) : 0 ≤ levelCutoff c ε t := Real.smoothTransition.nonneg _

theorem levelCutoff_le_one (c ε t : ℝ) : levelCutoff c ε t ≤ 1 := Real.smoothTransition.le_one _

theorem levelCutoff_eq_zero {c ε t : ℝ} (hε : 0 < ε) (ht : t ≤ c + ε / 2) : levelCutoff c ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem levelCutoff_eq_one {c ε t : ℝ} (hε : 0 < ε) (ht : c + ε ≤ t) : levelCutoff c ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]; linarith

theorem monotone_levelCutoff {c ε : ℝ} (hε : 0 < ε) : Monotone (levelCutoff c ε) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

def β (c ε : ℝ) (t : ℝ) : ℝ := deriv (levelCutoff c ε) t

theorem contDiff_β (c ε : ℝ) : ContDiff ℝ ∞ (β c ε) :=
  (contDiff_infty_iff_deriv.1 (contDiff_levelCutoff c ε)).2

theorem continuous_β (c ε : ℝ) : Continuous (β c ε) := (contDiff_β c ε).continuous

theorem hasDerivAt_levelCutoff (c ε t : ℝ) : HasDerivAt (levelCutoff c ε) (β c ε t) t :=
  ((contDiff_levelCutoff c ε).differentiable (by simp) t).hasDerivAt

theorem β_nonneg {c ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ β c ε t :=
  (monotone_levelCutoff hε).deriv_nonneg

theorem hasDerivAt_B' (c ε t : ℝ) :
    HasDerivAt (levelCutoff c ε) (deriv Real.smoothTransition ((t - (c + ε / 2)) / (ε / 2)) * (1 / (ε / 2)))
      t := by
  have h1 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t - (c + ε / 2)) / (ε / 2))) ((t - (c + ε / 2)) / (ε / 2)) :=
    (Real.smoothTransition.contDiff.differentiable (n := 1) (by simp) _).hasDerivAt
  have h2 : HasDerivAt (fun t => (t - (c + ε / 2)) / (ε / 2)) (1 / (ε / 2)) t := by
    simpa using ((hasDerivAt_id' (x := t)).sub_const (c + ε / 2)).div_const (ε / 2)
  exact h1.comp t h2

theorem β_eq_zero_of_le {c ε t : ℝ} (hε : 0 < ε) (ht : t ≤ c + ε / 2) : β c ε t = 0 := by
  rw [β, (hasDerivAt_B' c ε t).deriv, Real.smoothTransition_deriv_zero_of_nonpos _
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), zero_mul]

theorem β_eq_zero_of_ge {c ε t : ℝ} (hε : 0 < ε) (ht : c + ε ≤ t) : β c ε t = 0 := by
  rw [β, (hasDerivAt_B' c ε t).deriv, Real.smoothTransition_deriv_zero_of_one_le _
    (by rw [le_div_iff₀ (by positivity)]; linarith), zero_mul]

def α (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.smoothTransition ((9 * ρ ^ 2 - ‖w‖ ^ 2) / (5 * ρ ^ 2))

theorem contDiff_α (ρ : ℝ) : ContDiff ℝ ∞ (α (k := k) ρ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)

theorem α_nonneg (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) : 0 ≤ α ρ w :=
  Real.smoothTransition.nonneg _

theorem α_le_one (ρ : ℝ) (w : EuclideanSpace ℝ (Fin k)) : α ρ w ≤ 1 :=
  Real.smoothTransition.le_one _

theorem α_eq_one {ρ : ℝ} (hρ : 0 < ρ) {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ ≤ 2 * ρ) :
    α ρ w = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  have := pow_le_pow_left₀ (norm_nonneg w) hw 2
  linarith

theorem α_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {w : EuclideanSpace ℝ (Fin k)} (hw : 3 * ρ ≤ ‖w‖) :
    α ρ w = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have := pow_le_pow_left₀ (by positivity) hw 2
  linarith

def twist (c ε ρ : ℝ) (z : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) : Fin n → ℝ :=
  (-(β c ε (morseNormalForm hk c y) * α ρ (scaledNegativePart hk y))) • levelTangentLift hk z y

theorem nf_le_of_posPart_eq_zero (c : ℝ) {y : Fin n → ℝ} (hy : posPart hk y = 0) :
    morseNormalForm hk c y ≤ c := by
  rw [morseNormalForm_split, hy, norm_zero]
  have := sq_nonneg ‖negPart hk y‖
  linarith

theorem posPart_ne_zero_of_lt_nf {c : ℝ} {y : Fin n → ℝ} (hy : c < morseNormalForm hk c y) :
    posPart hk y ≠ 0 := fun h => absurd (nf_le_of_posPart_eq_zero hk c h) (not_le.2 hy)

theorem normSq_posPart_ge_of_nf_ge {c ε : ℝ} {y : Fin n → ℝ}
    (hy : c + ε ≤ morseNormalForm hk c y) : 2 * ε + ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
  rw [morseNormalForm_split] at hy; linarith

theorem normSq_posPart_le_of_nf_le {c ε : ℝ} {y : Fin n → ℝ}
    (hy : morseNormalForm hk c y ≤ c + ε) : ‖posPart hk y‖ ^ 2 ≤ 2 * ε + ‖negPart hk y‖ ^ 2 := by
  rw [morseNormalForm_split] at hy; linarith

theorem twist_eq_zero_of_nf_le {c ε ρ : ℝ} (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin k))
    {y : Fin n → ℝ} (hy : morseNormalForm hk c y ≤ c + ε / 2) : twist hk c ε ρ z y = 0 := by
  simp [twist, β_eq_zero_of_le hε hy]

theorem twist_eq_zero_of_nf_ge {c ε ρ : ℝ} (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin k))
    {y : Fin n → ℝ} (hy : c + ε ≤ morseNormalForm hk c y) : twist hk c ε ρ z y = 0 := by
  simp [twist, β_eq_zero_of_ge hε hy]

theorem twist_eq_zero_of_norm_scaledNegativePart {c ε ρ : ℝ} (hρ : 0 < ρ) (z : EuclideanSpace ℝ (Fin k))
    {y : Fin n → ℝ} (hy : 3 * ρ ≤ ‖scaledNegativePart hk y‖) : twist hk c ε ρ z y = 0 := by
  simp [twist, α_eq_zero hρ hy]

theorem isOpen_posPart_ne_zero : IsOpen {y : Fin n → ℝ | posPart hk y ≠ 0} :=
  (posPartL hk).continuous.isOpen_preimage _ isOpen_compl_singleton

theorem contDiffOn_twist (c ε ρ : ℝ) (z : EuclideanSpace ℝ (Fin k)) :
    ContDiffOn ℝ ∞ (twist hk c ε ρ z) {y | posPart hk y ≠ 0} := by
  refine ContDiffOn.smul (𝕜' := ℝ) ?_ (contDiffOn_levelTangentLift hk z)
  refine ContDiffOn.neg (ContDiffOn.mul ?_ ?_)
  · exact (contDiff_β c ε).comp_contDiffOn (contDiff_nf hk c).contDiffOn
  · exact (contDiff_α ρ).comp_contDiffOn (contDiffOn_scaledNegativePart hk)

theorem contDiff_twist {c ε : ℝ} (hε : 0 < ε) (ρ : ℝ) (z : EuclideanSpace ℝ (Fin k)) :
    ContDiff ℝ ∞ (twist hk c ε ρ z) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hv : posPart hk y ≠ 0
  · exact (contDiffOn_twist hk c ε ρ z).contDiffAt ((isOpen_posPart_ne_zero hk).mem_nhds hv)
  · have hv : posPart hk y = 0 := not_not.1 hv
    have hU : IsOpen {y : Fin n → ℝ | morseNormalForm hk c y < c + ε / 2} :=
      isOpen_lt (contDiff_nf hk c).continuous continuous_const
    have hmem : y ∈ {y : Fin n → ℝ | morseNormalForm hk c y < c + ε / 2} := by
      change morseNormalForm hk c y < c + ε / 2
      have := nf_le_of_posPart_eq_zero hk c hv
      linarith
    refine (ContDiffOn.congr (contDiffOn_const (c := (0 : Fin n → ℝ))) ?_).contDiffAt
      (hU.mem_nhds hmem)
    intro y hy
    exact twist_eq_zero_of_nf_le hk hε z (le_of_lt hy)

def twistSupp (c ε ρ : ℝ) : Set (Fin n → ℝ) :=
  {y | c + ε / 2 ≤ morseNormalForm hk c y ∧ morseNormalForm hk c y ≤ c + ε ∧ ‖scaledNegativePart hk y‖ ≤ 3 * ρ}

theorem isClosed_twistSupp (c ε ρ : ℝ) : IsClosed (twistSupp hk c ε ρ) := by
  have hc := (contDiff_nf hk c).continuous
  exact (isClosed_le continuous_const hc).inter
    ((isClosed_le hc continuous_const).inter
      (isClosed_le (continuous_scaledNegativePart hk).norm continuous_const))

theorem support_twist_subset {c ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin k)) :
    Function.support (twist hk c ε ρ z) ⊆ twistSupp hk c ε ρ := by
  intro y hy
  rw [Function.mem_support] at hy
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hy (twist_eq_zero_of_nf_le hk hε z (le_of_lt (not_le.1 h)))
  · by_contra h
    exact hy (twist_eq_zero_of_nf_ge hk hε z (le_of_lt (not_le.1 h)))
  · by_contra h
    exact hy (twist_eq_zero_of_norm_scaledNegativePart hk hρ z (le_of_lt (not_le.1 h)))

theorem tsupport_twist_subset {c ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin k)) :
    tsupport (twist hk c ε ρ z) ⊆ twistSupp hk c ε ρ :=
  closure_minimal (support_twist_subset hk hε hρ z) (isClosed_twistSupp hk c ε ρ)

theorem morseNorm_sq_le_of_mem_twistSupp {c ε ρ : ℝ} (hε : 0 < ε) {y : Fin n → ℝ}
    (hy : y ∈ twistSupp hk c ε ρ) : morseNorm n y ^ 2 ≤ 2 * ε + 18 * ρ ^ 2 / ε := by
  obtain ⟨h1, h2, h3⟩ := hy
  rw [morseNormalForm_split] at h1 h2
  rw [norm_scaledNegativePart] at h3
  rw [morseNorm_sq_eq_negPart_add_posPart hk]
  set a := ‖negPart hk y‖ with ha
  set b := ‖posPart hk y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hab : (b * a) ^ 2 ≤ (3 * ρ) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  have hbε : ε ≤ b ^ 2 := by nlinarith [sq_nonneg a]
  have haε : a ^ 2 * ε ≤ 9 * ρ ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha' : a ^ 2 ≤ 9 * ρ ^ 2 / ε := by rw [le_div_iff₀ hε]; exact haε
  have : 18 * ρ ^ 2 / ε = 2 * (9 * ρ ^ 2 / ε) := by ring
  rw [this]
  nlinarith

theorem morseNorm_le_of_mem_twistSupp {c ε ρ R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hR' : 2 * ε + 18 * ρ ^ 2 / ε ≤ R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ twistSupp hk c ε ρ) : morseNorm n y ≤ R := by
  have := (morseNorm_sq_le_of_mem_twistSupp hk hε hy).trans hR'
  exact (pow_le_pow_iff_left₀ (morseNorm_nonneg y) hR two_ne_zero).1 this

theorem tsupport_twist_subset_ball {c ε ρ R : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hR' : 2 * ε + 18 * ρ ^ 2 / ε ≤ R ^ 2) (z : EuclideanSpace ℝ (Fin k)) :
    tsupport (twist hk c ε ρ z) ⊆ {y | morseNorm n y ≤ R} := fun _ hy =>
  morseNorm_le_of_mem_twistSupp hk hε hR hR' (tsupport_twist_subset hk hε hρ z hy)

theorem hasCompactSupport_twist {c ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin k)) : HasCompactSupport (twist hk c ε ρ z) := by
  set R := Real.sqrt (2 * ε + 18 * ρ ^ 2 / ε) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR' : 2 * ε + 18 * ρ ^ 2 / ε ≤ R ^ 2 := by
    rw [hR, Real.sq_sqrt (by positivity)]
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℝ) R)
    fun y hy => ?_
  have h1 := morseNorm_le_of_mem_twistSupp hk hε hR0 hR' (support_twist_subset hk hε hρ z hy)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (morseNorm_piNorm_le y).trans h1

theorem fderiv_nf_twist {c ε : ℝ} (hε : 0 < ε) (ρ : ℝ) (z : EuclideanSpace ℝ (Fin k))
    (y : Fin n → ℝ) : fderiv ℝ (morseNormalForm hk c) y (twist hk c ε ρ z y) = 0 := by
  by_cases hv : posPart hk y ≠ 0
  · rw [twist, ContinuousLinearMap.map_smul, fderiv_nf_levelTangentLift hk c z hv, smul_zero]
  · have hv : posPart hk y = 0 := not_not.1 hv
    have := nf_le_of_posPart_eq_zero hk c hv
    rw [twist_eq_zero_of_nf_le hk hε z (by linarith), map_zero]

theorem fderiv_scaledNegativePart_twist {c ε ρ : ℝ} (hρ : 0 < ρ) (z : EuclideanSpace ℝ (Fin k))
    {y : Fin n → ℝ} (hv : posPart hk y ≠ 0) (hJ : ‖scaledNegativePart hk y‖ ≤ 2 * ρ) :
    fderiv ℝ (scaledNegativePart hk) y (twist hk c ε ρ z y) = (-(β c ε (morseNormalForm hk c y))) • z := by
  rw [twist, ContinuousLinearMap.map_smul, fderiv_scaledNegativePart_levelTangentLift hk z hv, α_eq_one hρ hJ, mul_one]

section Twisted

variable {c ε ρ r₀ : ℝ} {z : EuclideanSpace ℝ (Fin k)} {γ : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}

theorem hasDerivAt_invariant (hr₀ : 0 < r₀) (hε : 0 < ε) (hρ : 0 < ρ) {σ t : ℝ}
    (hγt : HasDerivAt γ (σ • (modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t)
    (hunit : r₀ / 2 ≤ morseNorm n (γ t)) (hpos : posPart hk (γ t) ≠ 0)
    (hα : ‖scaledNegativePart hk (γ t)‖ ≤ 2 * ρ) :
    HasDerivAt (fun s => scaledNegativePart hk (γ s) - levelCutoff c ε (morseNormalForm hk c (γ s)) • z) 0 t := by
  have hJ := (hasFDerivAt_scaledNegativePart hk hpos).comp_hasDerivAt t hγt
  have hJ' : scaledNegativePartDeriv hk (γ t) (σ • (modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) =
      σ • ((-(β c ε (morseNormalForm hk c (γ t)))) • z) := by
    rw [ContinuousLinearMap.map_smul, map_add, ← (hasFDerivAt_scaledNegativePart hk hpos).fderiv,
      fderiv_scaledNegativePart_modelField hk r₀ hpos, fderiv_scaledNegativePart_twist hk hρ z hpos hα, zero_add]
  have hnf := (hasFDerivAt_nf hk c (γ t)).comp_hasDerivAt t hγt
  have hnf' : nfDeriv hk (γ t) (σ • (modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) =
      σ * (-1) := by
    rw [ContinuousLinearMap.map_smul, map_add, ← (hasFDerivAt_nf hk c (γ t)).fderiv,
      fderiv_nf_modelField_eq_neg_one hk c hr₀ hunit, fderiv_nf_twist hk hε ρ z, add_zero,
      smul_eq_mul]
  rw [hJ'] at hJ
  rw [hnf'] at hnf
  have hB := (hasDerivAt_levelCutoff c ε (morseNormalForm hk c (γ t))).comp t hnf
  have := hJ.sub (hB.smul_const z)
  convert this using 1
  · funext s; rfl
  · rw [smul_smul, ← sub_smul]
    convert (zero_smul ℝ z).symm using 2
    ring

theorem invariant_twisted_curve (hr₀ : 0 < r₀) (hε : 0 < ε) (hρ : 0 < ρ)
    (hγ : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt γ (modelField k r₀ (γ t) + twist hk c ε ρ z (γ t)) t)
    (hunit : ∀ t ∈ Icc t₀ t₁, r₀ / 2 ≤ morseNorm n (γ t))
    (hpos : ∀ t ∈ Icc t₀ t₁, posPart hk (γ t) ≠ 0)
    (hα : ∀ t ∈ Icc t₀ t₁, ‖scaledNegativePart hk (γ t)‖ ≤ 2 * ρ) :
    ∀ t ∈ Icc t₀ t₁, scaledNegativePart hk (γ t) - levelCutoff c ε (morseNormalForm hk c (γ t)) • z =
      scaledNegativePart hk (γ t₀) - levelCutoff c ε (morseNormalForm hk c (γ t₀)) • z := by
  have hd : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt (fun s => scaledNegativePart hk (γ s) - levelCutoff c ε (morseNormalForm hk c (γ s)) • z) 0 t := by
    intro t ht
    refine hasDerivAt_invariant hk hr₀ hε hρ (σ := 1) ?_ (hunit t ht) (hpos t ht) (hα t ht)
    rw [one_smul]; exact hγ t ht
  exact constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd)
    fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt

theorem hasDerivAt_nf_ascending (hε : 0 < ε) {t : ℝ}
    (hγt : HasDerivAt γ (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t) :
    HasDerivAt (fun s => morseNormalForm hk c (γ s))
      (theta r₀ (γ t) * morseNorm n (γ t) ^ 2) t := by
  have hnf := (hasFDerivAt_nf hk c (γ t)).comp_hasDerivAt t hγt
  have hnf' : nfDeriv hk (γ t) (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) =
      theta r₀ (γ t) * morseNorm n (γ t) ^ 2 := by
    rw [map_neg, map_add, ← (hasFDerivAt_nf hk c (γ t)).fderiv, fderiv_nf_modelField,
      fderiv_nf_twist hk hε ρ z, add_zero, neg_neg]
  rw [hnf'] at hnf
  exact hnf

theorem nf_monotoneOn_ascending (hr₀ : 0 < r₀) (hε : 0 < ε)
    (hγ : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt γ (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t) :
    MonotoneOn (fun t => morseNormalForm hk c (γ t)) (Icc t₀ t₁) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ t₁)
    (f' := fun t => theta r₀ (γ t) * morseNorm n (γ t) ^ 2)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_nf_ascending hk hε (hγ t ht))
    (fun t ht => ?_) (fun t _ => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_nf_ascending hk hε (hγ t (Ioo_subset_Icc_self ht))).hasDerivWithinAt
  · have := theta_pos hr₀ (γ t)
    positivity

theorem morseNorm_ge_of_nf_ge (hr₀ : 0 < r₀) (hr₀ε : r₀ ^ 2 ≤ 4 * ε) {y : Fin n → ℝ}
    (hy : c + ε / 2 ≤ morseNormalForm hk c y) : r₀ / 2 ≤ morseNorm n y := by
  have h1 := normSq_posPart_ge_of_nf_ge hk hy
  have h2 := morseNorm_sq_eq_negPart_add_posPart hk y
  have h3 : (r₀ / 2) ^ 2 ≤ morseNorm n y ^ 2 := by nlinarith [sq_nonneg ‖negPart hk y‖]
  exact (pow_le_pow_iff_left₀ (by positivity) (morseNorm_nonneg y) two_ne_zero).1 h3

theorem morseNorm_sq_le_of_collar (hε : 0 < ε) {y : Fin n → ℝ}
    (h1 : c + ε / 2 ≤ morseNormalForm hk c y) (h2 : morseNormalForm hk c y ≤ c + ε) {K : ℝ}
    (hJ : ‖scaledNegativePart hk y‖ ≤ K) : morseNorm n y ^ 2 ≤ 2 * ε + 2 * K ^ 2 / ε := by
  rw [morseNormalForm_split] at h1 h2
  rw [norm_scaledNegativePart] at hJ
  rw [morseNorm_sq_eq_negPart_add_posPart hk]
  set a := ‖negPart hk y‖ with ha
  set b := ‖posPart hk y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hab : (b * a) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) hJ 2
  have hbε : ε ≤ b ^ 2 := by nlinarith [sq_nonneg a]
  have haε : a ^ 2 * ε ≤ K ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha' : a ^ 2 ≤ K ^ 2 / ε := by rw [le_div_iff₀ hε]; exact haε
  have : 2 * K ^ 2 / ε = 2 * (K ^ 2 / ε) := by ring
  rw [this]
  nlinarith

theorem ascending_twisted_curve (hr₀ : 0 < r₀) (hε : 0 < ε) (hρ : 0 < ρ)
    (hr₀ε : r₀ ^ 2 ≤ 4 * ε) (hz : ‖z‖ ≤ ρ) (ht₀₁ : t₀ ≤ t₁)
    (hγ : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt γ (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t)
    (hJ0 : scaledNegativePart hk (γ t₀) = 0) (hnf0 : morseNormalForm hk c (γ t₀) = c + ε / 2) :
    (∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) = c + ε / 2 + (t - t₀)) ∧
    (∀ t ∈ Icc t₀ t₁, scaledNegativePart hk (γ t) = levelCutoff c ε (morseNormalForm hk c (γ t)) • z) ∧
    (∀ t ∈ Icc t₀ t₁, ‖scaledNegativePart hk (γ t)‖ ≤ ‖z‖) := by
  have hmono := nf_monotoneOn_ascending hk hr₀ hε hγ
  have hge : ∀ t ∈ Icc t₀ t₁, c + ε / 2 ≤ morseNormalForm hk c (γ t) := by
    intro t ht
    have := hmono (left_mem_Icc.2 ht₀₁) ht ht.1
    simp only at this
    linarith
  have hunit : ∀ t ∈ Icc t₀ t₁, r₀ / 2 ≤ morseNorm n (γ t) := fun t ht =>
    morseNorm_ge_of_nf_ge hk hr₀ hr₀ε (hge t ht)
  have hpos : ∀ t ∈ Icc t₀ t₁, posPart hk (γ t) ≠ 0 := fun t ht =>
    posPart_ne_zero_of_lt_nf hk (by linarith [hge t ht])
  have hlevel : ∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) = c + ε / 2 + (t - t₀) := by
    have hd : ∀ t ∈ Icc t₀ t₁,
        HasDerivAt (fun s => morseNormalForm hk c (γ s) - s) 0 t := by
      intro t ht
      have h2 := (hasDerivAt_nf_ascending hk hε (hγ t ht)).sub (hasDerivAt_id' (x := t))
      rw [theta_mul_sq hr₀ (hunit t ht), sub_self] at h2
      exact h2
    have := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    intro t ht
    have h := this t ht
    linarith
  refine ⟨hlevel, ?_⟩
  set g : ℝ → EuclideanSpace ℝ (Fin k) :=
    fun s => scaledNegativePart hk (γ s) - levelCutoff c ε (morseNormalForm hk c (γ s)) • z with hg
  have hγc : ContinuousOn γ (Icc t₀ t₁) := HasDerivAt.continuousOn hγ
  have hJcont : ContinuousOn (fun s => scaledNegativePart hk (γ s)) (Icc t₀ t₁) :=
    (continuous_scaledNegativePart hk).comp_continuousOn hγc
  have hBcont : ContinuousOn (fun s => levelCutoff c ε (morseNormalForm hk c (γ s))) (Icc t₀ t₁) :=
    ((contDiff_levelCutoff c ε).continuous.comp (contDiff_nf hk c).continuous).comp_continuousOn hγc
  have hgcont : ContinuousOn g (Icc t₀ t₁) := fun x hx =>
    (hJcont x hx).sub ((hBcont x hx).smul continuousWithinAt_const)
  have hSclosed : IsClosed ({s | g s = 0} ∩ Icc t₀ t₁) := by
    rw [inter_comm]
    exact hgcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hnormJ : ∀ s, g s = 0 → ‖scaledNegativePart hk (γ s)‖ ≤ ‖z‖ := by
    intro s hs
    have : scaledNegativePart hk (γ s) = levelCutoff c ε (morseNormalForm hk c (γ s)) • z := sub_eq_zero.1 hs
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (levelCutoff_nonneg _ _ _)]
    have := levelCutoff_le_one c ε (morseNormalForm hk c (γ s))
    have := norm_nonneg z
    nlinarith
  have hsubset : Icc t₀ t₁ ⊆ {s | g s = 0} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hSclosed ?_ ?_
    · change g t₀ = 0
      simp only [hg, hJ0, hnf0, levelCutoff_eq_zero hε (le_refl _), zero_smul, sub_zero]
    · rintro x ⟨hx, hxI⟩
      have hx0 : g x = 0 := hx
      have hxIcc : x ∈ Icc t₀ t₁ := ⟨hxI.1, hxI.2.le⟩
      have hxlt : ‖scaledNegativePart hk (γ x)‖ < 2 * ρ := by linarith [hnormJ x hx0]
      have hIcc : Icc t₀ t₁ ∈ 𝓝[>] x :=
        Filter.mem_of_superset (Icc_mem_nhdsGT hxI.2) (Icc_subset_Icc hxI.1 le_rfl)
      have hev1 : ∀ᶠ s in 𝓝[>] x, ‖scaledNegativePart hk (γ s)‖ < 2 * ρ := by
        have h := ((hJcont.continuousWithinAt hxIcc).norm.tendsto).eventually
          (eventually_lt_nhds hxlt)
        exact h.filter_mono (nhdsWithin_le_of_mem hIcc)
      have hev2 : ∀ᶠ s in 𝓝[>] x, s ∈ Icc t₀ t₁ := hIcc
      obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev1.and hev2)
      refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨u, hu, fun s hs => ?_⟩
      have hs' := hIoo hs
      change g s = 0
      have hxs : x ≤ s := hs.1.le
      have hd : ∀ r ∈ Ico x s, HasDerivWithinAt g 0 (Ici r) r := by
        intro r hr
        have hrI : r ∈ Icc t₀ t₁ := ⟨hxI.1.trans hr.1, hr.2.le.trans hs'.2.2⟩
        have hαr : ‖scaledNegativePart hk (γ r)‖ ≤ 2 * ρ := by
          rcases hr.1.lt_or_eq with h | h
          · exact (hIoo ⟨h, hr.2.trans hs.2⟩).1.le
          · rw [← h]; exact hxlt.le
        refine (hasDerivAt_invariant hk hr₀ hε hρ (σ := -1) ?_ (hunit r hrI) (hpos r hrI)
          hαr).hasDerivWithinAt
        rw [neg_one_smul]; exact hγ r hrI
      have := constant_of_has_deriv_right_zero
        (hgcont.mono (Icc_subset_Icc hxIcc.1 hs'.2.2)) hd s (right_mem_Icc.2 hxs)
      rw [this, hx0]
  refine ⟨fun t ht => sub_eq_zero.1 (hsubset ht), fun t ht => hnormJ t (hsubset ht)⟩

theorem ascending_twisted_curve_end (hr₀ : 0 < r₀) (hε : 0 < ε) (hρ : 0 < ρ)
    (hr₀ε : r₀ ^ 2 ≤ 4 * ε) (hz : ‖z‖ ≤ ρ)
    (hγ : ∀ t ∈ Icc t₀ (t₀ + ε / 2),
      HasDerivAt γ (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t)
    (hJ0 : scaledNegativePart hk (γ t₀) = 0) (hnf0 : morseNormalForm hk c (γ t₀) = c + ε / 2) :
    scaledNegativePart hk (γ (t₀ + ε / 2)) = z ∧ morseNormalForm hk c (γ (t₀ + ε / 2)) = c + ε := by
  obtain ⟨h1, h2, -⟩ := ascending_twisted_curve hk hr₀ hε hρ hr₀ε hz (by linarith) hγ hJ0 hnf0
  have ht : t₀ + ε / 2 ∈ Icc t₀ (t₀ + ε / 2) := right_mem_Icc.2 (by linarith)
  have hl : morseNormalForm hk c (γ (t₀ + ε / 2)) = c + ε := by rw [h1 _ ht]; ring
  refine ⟨?_, hl⟩
  rw [h2 _ ht, hl, levelCutoff_eq_one hε le_rfl, one_smul]

end Twisted

theorem exists_avoid_image {k l : ℕ} (hlt : k < l) {O : Set (Fin k → ℝ)}
    {F : (Fin k → ℝ) → (Fin l → ℝ)} (hF : DifferentiableOn ℝ F O) (z₀ : Fin l → ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ z, ‖z - z₀‖ < ρ ∧ z ∉ F '' O := by
  have hdim : dimH (F '' O) < Module.finrank ℝ (Fin l → ℝ) := by
    calc dimH (F '' O) ≤ dimH O := hF.dimH_image_le
      _ ≤ dimH (univ : Set (Fin k → ℝ)) := dimH_mono (subset_univ _)
      _ = Module.finrank ℝ (Fin k → ℝ) := Real.dimH_univ_eq_finrank _
      _ < Module.finrank ℝ (Fin l → ℝ) := by simp [hlt]
  have hdense := dense_compl_of_dimH_lt_finrank hdim
  obtain ⟨z, hz, hzmem⟩ := hdense.exists_mem_open Metric.isOpen_ball ⟨z₀, Metric.mem_ball_self hρ⟩
  exact ⟨z, by simpa [dist_eq_norm] using hzmem, hz⟩

theorem exists_avoid_image_euclidean {k l : ℕ} (hlt : k < l) {O : Set (Fin k → ℝ)}
    {F : (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)} (hF : DifferentiableOn ℝ F O)
    (z₀ : EuclideanSpace ℝ (Fin l)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z, ‖z - z₀‖ < ρ ∧ z ∉ F '' O := by
  have hdim : dimH (F '' O) < Module.finrank ℝ (EuclideanSpace ℝ (Fin l)) := by
    calc dimH (F '' O) ≤ dimH O := hF.dimH_image_le
      _ ≤ dimH (univ : Set (Fin k → ℝ)) := dimH_mono (subset_univ _)
      _ = Module.finrank ℝ (Fin k → ℝ) := Real.dimH_univ_eq_finrank _
      _ < Module.finrank ℝ (EuclideanSpace ℝ (Fin l)) := by
        simp [hlt]
  have hdense := dense_compl_of_dimH_lt_finrank hdim
  obtain ⟨z, hz, hzmem⟩ := hdense.exists_mem_open Metric.isOpen_ball ⟨z₀, Metric.mem_ball_self hρ⟩
  exact ⟨z, by simpa [dist_eq_norm] using hzmem, hz⟩

end

end DifferentialGeometry.Topology.ModelField
