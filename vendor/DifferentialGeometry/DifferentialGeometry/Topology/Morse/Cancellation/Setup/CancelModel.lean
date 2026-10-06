module

public import DifferentialGeometry.Topology.Morse.Strip.Substrip

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology.CancelModel

open scoped ContDiff _root_.Topology RealInnerProductSpace
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_piNorm_le morseNorm_sq_eq_negPart_add_posPart)
open DifferentialGeometry.Topology.ModelField

noncomputable section

def decreasingTransition (t : ℝ) : ℝ := Real.smoothTransition (1 - t)

theorem contDiff_decreasingTransition : ContDiff ℝ ∞ decreasingTransition :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem continuous_decreasingTransition : Continuous decreasingTransition := contDiff_decreasingTransition.continuous

theorem decreasingTransition_nonneg (t : ℝ) : 0 ≤ decreasingTransition t := Real.smoothTransition.nonneg _

theorem decreasingTransition_le_one (t : ℝ) : decreasingTransition t ≤ 1 := Real.smoothTransition.le_one _

theorem decreasingTransition_eq_one {t : ℝ} (ht : t ≤ 0) : decreasingTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem decreasingTransition_eq_zero {t : ℝ} (ht : 1 ≤ t) : decreasingTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem decreasingTransition_eq_one_iff {t : ℝ} : decreasingTransition t = 1 ↔ t ≤ 0 := by
  rw [decreasingTransition, Real.smoothTransition.eq_one_iff_one_le]; constructor <;> intro h <;> linarith

theorem decreasingTransition_eq_zero_iff {t : ℝ} : decreasingTransition t = 0 ↔ 1 ≤ t := by
  rw [decreasingTransition, Real.smoothTransition.zero_iff_nonpos]; constructor <;> intro h <;> linarith

theorem decreasingTransition_pos_of_lt_one {t : ℝ} (ht : t < 1) : 0 < decreasingTransition t :=
  Real.smoothTransition.pos_of_pos (by linarith)

theorem decreasingTransition_lt_one_of_pos {t : ℝ} (ht : 0 < t) : decreasingTransition t < 1 :=
  Real.smoothTransition.lt_one_of_lt_one (by linarith)

theorem decreasingTransition_antitone : Antitone decreasingTransition := fun s t hst =>
  Real.smoothTransition.monotone (by linarith)

theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have h := Real.smoothTransition.pos_denom x
  simp only [Real.smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x)), ← add_div, div_self h.ne']

theorem decreasingTransition_add_decreasingTransition_one_sub (t : ℝ) : decreasingTransition t + decreasingTransition (1 - t) = 1 := by
  have := smoothTransition_add_one_sub (1 - t)
  simp only [decreasingTransition, sub_sub_cancel] at this ⊢
  linarith

theorem smoothTransition_ge_half {x : ℝ} (hx : 1 / 2 ≤ x) :
    1 / 2 ≤ Real.smoothTransition x := by
  have h1 := smoothTransition_add_one_sub x
  have h2 : Real.smoothTransition (1 - x) ≤ Real.smoothTransition x :=
    Real.smoothTransition.monotone (by linarith)
  linarith

def cut (lo hi t : ℝ) : ℝ := decreasingTransition ((t - lo) / (hi - lo))

theorem contDiff_cut (lo hi : ℝ) : ContDiff ℝ ∞ (cut lo hi) :=
  contDiff_decreasingTransition.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem cut_nonneg (lo hi t : ℝ) : 0 ≤ cut lo hi t := decreasingTransition_nonneg _

theorem cut_le_one (lo hi t : ℝ) : cut lo hi t ≤ 1 := decreasingTransition_le_one _

theorem cut_eq_one {lo hi t : ℝ} (h : lo < hi) (ht : t ≤ lo) : cut lo hi t = 1 :=
  decreasingTransition_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cut_eq_zero {lo hi t : ℝ} (h : lo < hi) (ht : hi ≤ t) : cut lo hi t = 0 :=
  decreasingTransition_eq_zero (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem cut_eq_one_iff {lo hi t : ℝ} (h : lo < hi) : cut lo hi t = 1 ↔ t ≤ lo := by
  rw [cut, decreasingTransition_eq_one_iff, div_nonpos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · intro ht; exact Or.inr ⟨by linarith, by linarith⟩

theorem cut_eq_zero_iff {lo hi t : ℝ} (h : lo < hi) : cut lo hi t = 0 ↔ hi ≤ t := by
  rw [cut, decreasingTransition_eq_zero_iff, le_div_iff₀ (by linarith)]
  constructor <;> intro h' <;> linarith

theorem cut_pos_of_lt {lo hi t : ℝ} (h : lo < hi) (ht : t < hi) : 0 < cut lo hi t :=
  decreasingTransition_pos_of_lt_one (by rw [div_lt_iff₀ (by linarith)]; linarith)

theorem lt_of_cut_ne_zero {lo hi t : ℝ} (h : lo < hi) (ht : cut lo hi t ≠ 0) : t < hi := by
  by_contra h'
  exact ht (cut_eq_zero h (not_lt.1 h'))

theorem cut_antitone {lo hi : ℝ} (h : lo < hi) : Antitone (cut lo hi) := fun s t hst =>
  decreasingTransition_antitone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem one_sub_cut {lo hi : ℝ} (h : lo ≠ hi) (t : ℝ) : 1 - cut lo hi t = cut hi lo t := by
  have hne : hi - lo ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have key : (t - hi) / (lo - hi) = 1 - (t - lo) / (hi - lo) := by
    field_simp
    ring
  have := decreasingTransition_add_decreasingTransition_one_sub ((t - lo) / (hi - lo))
  rw [cut, cut, key]
  linarith

theorem cut_affine {s : ℝ} (hs : s ≠ 0) (a lo hi t : ℝ) :
    cut (a + s * lo) (a + s * hi) (a + s * t) = cut lo hi t := by
  unfold cut
  congr 1
  by_cases h : hi = lo
  · subst h; simp
  · have h1 : hi - lo ≠ 0 := sub_ne_zero.2 h
    have h2 : a + s * hi - (a + s * lo) ≠ 0 := by
      intro h'; apply h1; apply mul_left_cancel₀ hs; linarith
    field_simp
    ring

def dot {n : ℕ} (y z : Fin n → ℝ) : ℝ :=
  ⟪(EuclideanSpace.equiv (Fin n) ℝ).symm y, (EuclideanSpace.equiv (Fin n) ℝ).symm z⟫

variable {n : ℕ}

theorem dot_comm (y z : Fin n → ℝ) : dot y z = dot z y := real_inner_comm _ _

theorem dot_self (y : Fin n → ℝ) : dot y y = morseNorm n y ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem dot_add_left (x y z : Fin n → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, map_add, inner_add_left]

theorem dot_sub_left (x y z : Fin n → ℝ) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot, map_sub, inner_sub_left]

theorem dot_smul_left (a : ℝ) (y z : Fin n → ℝ) : dot (a • y) z = a * dot y z := by
  simp only [dot, map_smul, real_inner_smul_left]

theorem dot_neg_left (y z : Fin n → ℝ) : dot (-y) z = -dot y z := by
  simp only [dot, map_neg, inner_neg_left]

theorem dot_zero_left (z : Fin n → ℝ) : dot (0 : Fin n → ℝ) z = 0 := by
  simp only [dot, map_zero, inner_zero_left]

theorem dot_add_right (x y z : Fin n → ℝ) : dot x (y + z) = dot x y + dot x z := by
  rw [dot_comm, dot_add_left, dot_comm y, dot_comm z]

theorem dot_sub_right (x y z : Fin n → ℝ) : dot x (y - z) = dot x y - dot x z := by
  rw [dot_comm, dot_sub_left, dot_comm y, dot_comm z]

theorem dot_smul_right (a : ℝ) (y z : Fin n → ℝ) : dot y (a • z) = a * dot y z := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem dot_neg_right (y z : Fin n → ℝ) : dot y (-z) = -dot y z := by
  rw [dot_comm, dot_neg_left, dot_comm]

theorem dot_zero_right (y : Fin n → ℝ) : dot y (0 : Fin n → ℝ) = 0 := by
  rw [dot_comm, dot_zero_left]

theorem contDiff_dot_left (z : Fin n → ℝ) : ContDiff ℝ ∞ (fun y : Fin n → ℝ => dot y z) := by
  have : (fun y : Fin n → ℝ => dot y z) =
      (innerSL ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm z)) ∘L
        (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap := by
    ext y; simp [dot, real_inner_comm]
  rw [this]
  exact ContinuousLinearMap.contDiff _

theorem continuous_dot_left (z : Fin n → ℝ) : Continuous (fun y : Fin n → ℝ => dot y z) :=
  (contDiff_dot_left z).continuous

theorem abs_dot_le (y z : Fin n → ℝ) : |dot y z| ≤ morseNorm n y * morseNorm n z :=
  abs_real_inner_le_norm _ _

def axial (e₁ y : Fin n → ℝ) : ℝ := dot y e₁

def perp (e₁ y : Fin n → ℝ) : Fin n → ℝ := y - axial e₁ y • e₁

def perpSq (e₁ y : Fin n → ℝ) : ℝ := morseNorm n y ^ 2 - axial e₁ y ^ 2

theorem contDiff_axial (e₁ : Fin n → ℝ) : ContDiff ℝ ∞ (axial e₁) := contDiff_dot_left e₁

theorem contDiff_perpSq (e₁ : Fin n → ℝ) : ContDiff ℝ ∞ (perpSq e₁) :=
  contDiff_morseNorm_sq.sub ((contDiff_axial e₁).pow 2)

theorem continuous_axial (e₁ : Fin n → ℝ) : Continuous (axial e₁) := (contDiff_axial e₁).continuous

theorem continuous_perpSq (e₁ : Fin n → ℝ) : Continuous (perpSq e₁) :=
  (contDiff_perpSq e₁).continuous

theorem axial_add (e₁ y z : Fin n → ℝ) : axial e₁ (y + z) = axial e₁ y + axial e₁ z :=
  dot_add_left _ _ _

theorem axial_smul (e₁ : Fin n → ℝ) (a : ℝ) (y : Fin n → ℝ) : axial e₁ (a • y) = a * axial e₁ y :=
  dot_smul_left _ _ _

theorem axial_neg (e₁ y : Fin n → ℝ) : axial e₁ (-y) = -axial e₁ y := dot_neg_left _ _

theorem axial_zero (e₁ : Fin n → ℝ) : axial e₁ (0 : Fin n → ℝ) = 0 := dot_zero_left _

section Unit

variable {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1)
include he₁

theorem axial_smul_self (a : ℝ) : axial e₁ (a • e₁) = a := by
  rw [axial, dot_smul_left, dot_self, he₁]; ring

theorem perp_smul_self (a : ℝ) : perp e₁ (a • e₁) = 0 := by
  rw [perp, axial_smul_self he₁, sub_self]

theorem perpSq_smul_self (a : ℝ) : perpSq e₁ (a • e₁) = 0 := by
  rw [perpSq, axial_smul_self he₁]
  have : morseNorm n (a • e₁) = |a| := by
    change ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (a • e₁)‖ = _
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    change |a| * morseNorm n e₁ = |a|
    rw [he₁, mul_one]
  rw [this, sq_abs, sub_self]

theorem morseNorm_smul_self (a : ℝ) : morseNorm n (a • e₁) = |a| := by
  change ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (a • e₁)‖ = _
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  change |a| * morseNorm n e₁ = |a|
  rw [he₁, mul_one]

theorem morseNorm_sq_perp (y : Fin n → ℝ) : morseNorm n (perp e₁ y) ^ 2 = perpSq e₁ y := by
  rw [← dot_self, perp, perpSq, dot_sub_left, dot_sub_right, dot_sub_right, dot_smul_left,
    dot_smul_right, dot_smul_right, dot_smul_left, dot_self, dot_self, he₁]
  simp only [axial, dot_comm y e₁]
  ring

theorem perpSq_nonneg (y : Fin n → ℝ) : 0 ≤ perpSq e₁ y := by
  rw [← morseNorm_sq_perp he₁]; positivity

theorem axial_sq_le (y : Fin n → ℝ) : axial e₁ y ^ 2 ≤ morseNorm n y ^ 2 := by
  have := perpSq_nonneg he₁ y
  rw [perpSq] at this
  linarith

omit he₁ in
theorem perp_eq_zero_iff (y : Fin n → ℝ) : perp e₁ y = 0 ↔ y = axial e₁ y • e₁ := by
  rw [perp, sub_eq_zero]

theorem perpSq_eq_zero_iff (y : Fin n → ℝ) : perpSq e₁ y = 0 ↔ y = axial e₁ y • e₁ := by
  constructor
  · intro h
    have h2 : morseNorm n (perp e₁ y) = 0 := by
      rw [← pow_eq_zero_iff two_ne_zero, morseNorm_sq_perp he₁, h]
    exact (perp_eq_zero_iff y).1 ((morseNorm_eq_zero_iff _).1 h2)
  · intro h
    have h2 : perp e₁ y = 0 := (perp_eq_zero_iff y).2 h
    rw [← morseNorm_sq_perp he₁, h2, morseNorm_zero]; ring

theorem eq_smul_of_perpSq_eq_zero {y : Fin n → ℝ} (h : perpSq e₁ y = 0) : y = axial e₁ y • e₁ :=
  (perpSq_eq_zero_iff he₁ y).1 h

theorem morseNorm_eq_axial_of_perpSq_eq_zero {y : Fin n → ℝ} (h : perpSq e₁ y = 0)
    (ha : 0 ≤ axial e₁ y) : morseNorm n y = axial e₁ y := by
  have hy := eq_smul_of_perpSq_eq_zero he₁ h
  calc morseNorm n y = morseNorm n (axial e₁ y • e₁) := by rw [← hy]
    _ = axial e₁ y := by rw [morseNorm_smul_self he₁, abs_of_nonneg ha]

omit he₁ in
theorem perp_add (y z : Fin n → ℝ) : perp e₁ (y + z) = perp e₁ y + perp e₁ z := by
  simp only [perp, axial_add, add_smul]; abel

omit he₁ in
theorem perp_smul (a : ℝ) (y : Fin n → ℝ) : perp e₁ (a • y) = a • perp e₁ y := by
  simp only [perp, axial_smul, smul_sub, mul_smul]

end Unit

theorem theta_mul_morseNorm_le {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) :
    theta r₀ y * morseNorm n y ≤ 3 / r₀ := by
  have hden := thetaDen_pos hr₀ y
  have hb0 := bump_nonneg r₀ y
  have hy0 := morseNorm_nonneg y
  rw [theta, ← div_eq_inv_mul, div_le_div_iff₀ hden hr₀]
  unfold thetaDen
  rcases le_or_gt (morseNorm n y ^ 2) (r₀ ^ 2 / 8) with h | h
  · have hb : 1 / 2 ≤ bump r₀ y := by
      apply smoothTransition_ge_half
      have : 4 * morseNorm n y ^ 2 / r₀ ^ 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hle : morseNorm n y ≤ r₀ / 2 := by nlinarith
    nlinarith
  · have : r₀ ≤ 3 * morseNorm n y := by nlinarith
    nlinarith

theorem theta_mul_morseNorm_lt {r₀ m : ℝ} (hr₀ : 0 < r₀) (hm : 3 / r₀ < m) (y : Fin n → ℝ) :
    theta r₀ y * morseNorm n y < m :=
  (theta_mul_morseNorm_le hr₀ y).trans_lt hm

theorem modelField_index_zero (r₀ : ℝ) (y : Fin n → ℝ) :
    modelField 0 r₀ y = -(theta r₀ y • y) := by
  ext i
  simp [modelField, modelDesc]

theorem axis_ineq_p {θρ m s : ℝ} (h0 : 0 < θρ) (hm : θρ < m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < θρ * (2 * s - 1) + m * (1 - s) := by
  have e : θρ * (2 * s - 1) + m * (1 - s) = (1 - s) * (m - θρ) + s * θρ := by ring
  rw [e]
  rcases hs1.lt_or_eq with h | h
  · have := mul_pos (sub_pos.2 h) (sub_pos.2 hm)
    nlinarith [mul_nonneg hs0 h0.le]
  · subst h; nlinarith

theorem axis_ineq_q {θu m s : ℝ} (h0 : 0 < θu) (hm : θu < m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    θu * (2 * s - 1) - m * s < 0 := by
  have e : θu * (2 * s - 1) - m * s = -((1 - s) * θu + s * (m - θu)) := by ring
  rw [e]
  rcases hs1.lt_or_eq with h | h
  · have := mul_pos (sub_pos.2 h) h0
    nlinarith [mul_nonneg hs0 (sub_pos.2 hm).le]
  · subst h; nlinarith

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_pos_le_quadratic (L : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < L v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ L v v := by
  by_cases hE : ∃ v : E, v ≠ 0
  · obtain ⟨v₀, hv₀⟩ := hE
    have hcont : Continuous fun v : E => L v v := by fun_prop
    have hsph : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      ⟨‖v₀‖⁻¹ • v₀, by simp [norm_smul, norm_ne_zero_iff.2 hv₀]⟩
    obtain ⟨w, hw, hmin⟩ := hsph.exists_isMinOn hne hcont.continuousOn
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hwne : w ≠ 0 := by rintro rfl; simp at hw1
    refine ⟨L w w, hpos w hwne, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, hnv.ne']
      have h1 : L w w ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * L v v) := by
        have := hmin hmem
        simpa [map_smul, smul_eq_mul] using this
      have h2 : L w w * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * L v v) * ‖v‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : ‖v‖⁻¹ * (‖v‖⁻¹ * L v v) * ‖v‖ ^ 2 = L v v := by
        field_simp
      linarith
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by_contra fun h => hE ⟨v, h⟩
    rw [hv]; simp

theorem taylor_second_order_pos' {h : E → ℝ} (hh : ContDiff ℝ 2 h)
    (hd : fderiv ℝ h 0 = 0)
    (hpos : ∀ v, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ h) 0 v v) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ v, v ≠ 0 → ‖v‖ < δ₀ → 0 < fderiv ℝ h v v := by
  set A : E → E →L[ℝ] ℝ := fderiv ℝ h with hA
  set L : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ A 0 with hL
  obtain ⟨c, hc, hcL⟩ := exists_pos_le_quadratic L hpos
  have hA1 : ContDiff ℝ 1 A := hh.fderiv_right (m := 1) (by norm_num)
  have hder : HasFDerivAt A L 0 := (hA1.differentiable one_ne_zero 0).hasFDerivAt
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hder)
  have hbound := Asymptotics.isLittleO_iff.1 hlo (half_pos hc)
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ₀, hδ₀, hδ⟩ := hbound
  refine ⟨δ₀, hδ₀, fun v hv hvδ => ?_⟩
  have h1 := hδ (show dist v 0 < δ₀ by simpa using hvδ)
  simp only [zero_add, hd, sub_zero] at h1
  have h2 : |(A v - L v) v| ≤ ‖A v - L v‖ * ‖v‖ := by
    have := (A v - L v).le_opNorm v
    simpa [Real.norm_eq_abs] using this
  have h3 : (A v - L v) v = A v v - L v v := by simp
  have h4 := hcL v
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h5 : |A v v - L v v| ≤ c / 2 * ‖v‖ ^ 2 := by
    rw [← h3]
    calc |(A v - L v) v| ≤ ‖A v - L v‖ * ‖v‖ := h2
      _ ≤ c / 2 * ‖v‖ * ‖v‖ := by gcongr
      _ = c / 2 * ‖v‖ ^ 2 := by ring
  have h6 := (abs_le.1 h5).1
  have h7 : 0 < c / 2 * ‖v‖ ^ 2 := by positivity
  change 0 < A v v
  linarith

theorem taylor_second_order_pos {h : E → ℝ} (hh : ContDiff ℝ 2 h)
    (hd : fderiv ℝ h 0 = 0)
    (hpos : ∀ v, v ≠ 0 → 0 < iteratedFDeriv ℝ 2 h 0 ![v, v]) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ v, v ≠ 0 → ‖v‖ < δ₀ → 0 < fderiv ℝ h v v := by
  refine taylor_second_order_pos' hh hd fun v hv => ?_
  have := hpos v hv
  rwa [iteratedFDeriv_two_apply] at this

end Taylor

section PSide

variable (δ τ : ℝ) (e₁ : Fin n → ℝ)

def βp (y : Fin n → ℝ) : ℝ :=
  decreasingTransition ((perpSq e₁ y - τ ^ 2 * axial e₁ y ^ 2 - δ ^ 2) / δ ^ 2) *
    decreasingTransition ((-axial e₁ y - δ / 2) / (δ / 2))

theorem contDiff_βp : ContDiff ℝ ∞ (βp δ τ e₁) :=
  (contDiff_decreasingTransition.comp ((((contDiff_perpSq e₁).sub
      (contDiff_const.mul ((contDiff_axial e₁).pow 2))).sub contDiff_const).div_const _)).mul
    (contDiff_decreasingTransition.comp (((contDiff_axial e₁).neg.sub contDiff_const).div_const _))

def ψp (ρa ρb : ℝ) (y : Fin n → ℝ) : ℝ := cut (ρa ^ 2) (ρb ^ 2) (morseNorm n y ^ 2)

theorem contDiff_ψp (ρa ρb : ℝ) : ContDiff ℝ ∞ (ψp (n := n) ρa ρb) :=
  (contDiff_cut _ _).comp contDiff_morseNorm_sq

def pPerturbationField (m δ τ ρa ρb : ℝ) (e₁ : Fin n → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  (m * (βp δ τ e₁ y * ψp ρa ρb y)) • e₁

theorem contDiff_pPerturbationField (m δ τ ρa ρb : ℝ) : ContDiff ℝ ∞ (pPerturbationField m δ τ ρa ρb e₁) :=
  (contDiff_const.mul ((contDiff_βp δ τ e₁).mul (contDiff_ψp ρa ρb))).smul contDiff_const

def pSupportRegion (ρb : ℝ) : Set (Fin n → ℝ) :=
  {y | morseNorm n y ≤ ρb ∧ perpSq e₁ y ≤ τ ^ 2 * axial e₁ y ^ 2 + 2 * δ ^ 2 ∧
    -δ ≤ axial e₁ y}

variable {δ τ e₁}

theorem βp_nonneg (y : Fin n → ℝ) : 0 ≤ βp δ τ e₁ y := mul_nonneg (decreasingTransition_nonneg _) (decreasingTransition_nonneg _)

theorem βp_le_one (y : Fin n → ℝ) : βp δ τ e₁ y ≤ 1 :=
  (mul_le_mul (decreasingTransition_le_one _) (decreasingTransition_le_one _) (decreasingTransition_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem βp_eq_one (hδ : 0 < δ) {y : Fin n → ℝ}
    (h1 : perpSq e₁ y ≤ τ ^ 2 * axial e₁ y ^ 2 + δ ^ 2) (h2 : -(δ / 2) ≤ axial e₁ y) :
    βp δ τ e₁ y = 1 := by
  rw [βp, decreasingTransition_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
    decreasingTransition_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), mul_one]

theorem βp_eq_zero_of_perpSq (hδ : 0 < δ) {y : Fin n → ℝ}
    (h : τ ^ 2 * axial e₁ y ^ 2 + 2 * δ ^ 2 ≤ perpSq e₁ y) : βp δ τ e₁ y = 0 := by
  rw [βp, decreasingTransition_eq_zero (by rw [le_div_iff₀ (by positivity)]; linarith), zero_mul]

theorem βp_eq_zero_of_axial (hδ : 0 < δ) {y : Fin n → ℝ} (h : axial e₁ y ≤ -δ) :
    βp δ τ e₁ y = 0 := by
  rw [βp, decreasingTransition_eq_zero (t := (-axial e₁ y - δ / 2) / (δ / 2))
    (by rw [le_div_iff₀ (by positivity)]; linarith), mul_zero]

theorem lt_of_βp_ne_zero (hδ : 0 < δ) {y : Fin n → ℝ} (h : βp δ τ e₁ y ≠ 0) :
    perpSq e₁ y < τ ^ 2 * axial e₁ y ^ 2 + 2 * δ ^ 2 ∧ -δ < axial e₁ y := by
  constructor
  · by_contra h'; exact h (βp_eq_zero_of_perpSq hδ (not_lt.1 h'))
  · by_contra h'; exact h (βp_eq_zero_of_axial hδ (not_lt.1 h'))

theorem βp_zero (hδ : 0 < δ) : βp δ τ e₁ (0 : Fin n → ℝ) = 1 :=
  βp_eq_one hδ (by rw [perpSq, axial_zero, morseNorm_zero]; nlinarith [sq_nonneg δ, sq_nonneg τ])
    (by rw [axial_zero]; linarith)

theorem βp_smul_self (he₁ : morseNorm n e₁ = 1) (hδ : 0 < δ) {a : ℝ} (ha : -(δ / 2) ≤ a) :
    βp δ τ e₁ (a • e₁) = 1 :=
  βp_eq_one hδ (by rw [perpSq_smul_self he₁]; positivity) (by rwa [axial_smul_self he₁])

theorem continuous_βp : Continuous (βp δ τ e₁) := (contDiff_βp δ τ e₁).continuous

variable {ρa ρb : ℝ}

theorem ψp_nonneg (y : Fin n → ℝ) : 0 ≤ ψp ρa ρb y := cut_nonneg _ _ _

theorem ψp_le_one (y : Fin n → ℝ) : ψp ρa ρb y ≤ 1 := cut_le_one _ _ _

theorem ψp_eq_one (hρ : 0 ≤ ρa) (hab : ρa < ρb) {y : Fin n → ℝ} (hy : morseNorm n y ≤ ρa) :
    ψp ρa ρb y = 1 :=
  cut_eq_one (pow_lt_pow_left₀ hab hρ two_ne_zero) (pow_le_pow_left₀ (morseNorm_nonneg y) hy 2)

theorem ψp_eq_zero (hρ : 0 ≤ ρa) (hab : ρa < ρb) {y : Fin n → ℝ} (hy : ρb ≤ morseNorm n y) :
    ψp ρa ρb y = 0 :=
  cut_eq_zero (pow_lt_pow_left₀ hab hρ two_ne_zero) (pow_le_pow_left₀ (by linarith) hy 2)

theorem morseNorm_lt_of_ψp_ne_zero (hρ : 0 ≤ ρa) (hab : ρa < ρb) {y : Fin n → ℝ}
    (hy : ψp ρa ρb y ≠ 0) : morseNorm n y < ρb := by
  by_contra h
  exact hy (ψp_eq_zero hρ hab (not_lt.1 h))

theorem ψp_zero (hρ : 0 ≤ ρa) (hab : ρa < ρb) : ψp ρa ρb (0 : Fin n → ℝ) = 1 :=
  ψp_eq_one hρ hab (by rw [morseNorm_zero]; exact hρ)

theorem ψp_smul_self (he₁ : morseNorm n e₁ = 1) (a : ℝ) :
    ψp ρa ρb (a • e₁) = cut (ρa ^ 2) (ρb ^ 2) (a ^ 2) := by
  rw [ψp, morseNorm_smul_self he₁, sq_abs]

theorem continuous_ψp : Continuous (ψp (n := n) ρa ρb) := (contDiff_ψp ρa ρb).continuous

variable {m : ℝ}

theorem pPerturbationField_smul_self (he₁ : morseNorm n e₁ = 1) (hδ : 0 < δ) {a : ℝ} (ha : -(δ / 2) ≤ a) :
    pPerturbationField m δ τ ρa ρb e₁ (a • e₁) = (m * cut (ρa ^ 2) (ρb ^ 2) (a ^ 2)) • e₁ := by
  rw [pPerturbationField, βp_smul_self he₁ hδ ha, ψp_smul_self he₁, one_mul]

theorem axial_pPerturbationField (he₁ : morseNorm n e₁ = 1) (y : Fin n → ℝ) :
    axial e₁ (pPerturbationField m δ τ ρa ρb e₁ y) = m * (βp δ τ e₁ y * ψp ρa ρb y) := by
  rw [pPerturbationField, axial_smul_self he₁]

theorem perp_pPerturbationField (he₁ : morseNorm n e₁ = 1) (y : Fin n → ℝ) :
    perp e₁ (pPerturbationField m δ τ ρa ρb e₁ y) = 0 := by
  rw [pPerturbationField, perp_smul_self he₁]

theorem isClosed_pSupportRegion : IsClosed (pSupportRegion δ τ e₁ ρb) :=
  (isClosed_le continuous_morseNorm continuous_const).inter
    ((isClosed_le (continuous_perpSq e₁)
      ((continuous_const.mul ((continuous_axial e₁).pow 2)).add continuous_const)).inter
      (isClosed_le continuous_const (continuous_axial e₁)))

theorem isCompact_pSupportRegion : IsCompact (pSupportRegion δ τ e₁ ρb) :=
  (isCompact_morseNorm_le ρb).of_isClosed_subset isClosed_pSupportRegion fun _ hy => hy.1

theorem pSupportRegion_subset_ball {R : ℝ} (h : ρb < R) : pSupportRegion δ τ e₁ ρb ⊆ Metric.ball 0 R := fun _ hy =>
  mem_ball_of_morseNorm_lt (hy.1.trans_lt h)

theorem morseNorm_le_of_mem_pSupportRegion {y : Fin n → ℝ} (hy : y ∈ pSupportRegion δ τ e₁ ρb) : morseNorm n y ≤ ρb :=
  hy.1

theorem pPerturbationField_eq_zero_of_notMem (hδ : 0 < δ) (hρ : 0 ≤ ρa) (hab : ρa < ρb) {y : Fin n → ℝ}
    (hy : y ∉ pSupportRegion δ τ e₁ ρb) : pPerturbationField m δ τ ρa ρb e₁ y = 0 := by
  by_contra h
  apply hy
  have h1 : βp δ τ e₁ y ≠ 0 := fun h' => h (by simp [pPerturbationField, h'])
  have h2 : ψp ρa ρb y ≠ 0 := fun h' => h (by simp [pPerturbationField, h'])
  obtain ⟨h3, h4⟩ := lt_of_βp_ne_zero hδ h1
  exact ⟨(morseNorm_lt_of_ψp_ne_zero hρ hab h2).le, h3.le, h4.le⟩

theorem support_pPerturbationField_subset (hδ : 0 < δ) (hρ : 0 ≤ ρa) (hab : ρa < ρb) :
    Function.support (pPerturbationField m δ τ ρa ρb e₁) ⊆ pSupportRegion δ τ e₁ ρb := fun _ hy => by
  by_contra h
  exact hy (pPerturbationField_eq_zero_of_notMem hδ hρ hab h)

theorem tsupport_pPerturbationField_subset (hδ : 0 < δ) (hρ : 0 ≤ ρa) (hab : ρa < ρb) :
    tsupport (pPerturbationField m δ τ ρa ρb e₁) ⊆ pSupportRegion δ τ e₁ ρb :=
  closure_minimal (support_pPerturbationField_subset hδ hρ hab) isClosed_pSupportRegion

theorem hasCompactSupport_pPerturbationField (hδ : 0 < δ) (hρ : 0 ≤ ρa) (hab : ρa < ρb) :
    HasCompactSupport (pPerturbationField m δ τ ρa ρb e₁) :=
  isCompact_pSupportRegion.of_isClosed_subset (isClosed_tsupport _) (tsupport_pPerturbationField_subset hδ hρ hab)

theorem perp_modelField_add_pPerturbationField (he₁ : morseNorm n e₁ = 1) (r₀ : ℝ) (y : Fin n → ℝ) :
    perp e₁ (modelField 0 r₀ y + pPerturbationField m δ τ ρa ρb e₁ y) = -(theta r₀ y • perp e₁ y) := by
  rw [perp_add, perp_pPerturbationField he₁, add_zero, modelField_index_zero, ← neg_one_smul ℝ (theta r₀ y • y),
    perp_smul, perp_smul, neg_one_smul]

theorem axial_modelField_add_pPerturbationField (he₁ : morseNorm n e₁ = 1) (r₀ : ℝ) (y : Fin n → ℝ) :
    axial e₁ (modelField 0 r₀ y + pPerturbationField m δ τ ρa ρb e₁ y) =
      -(theta r₀ y * axial e₁ y) + m * (βp δ τ e₁ y * ψp ρa ρb y) := by
  rw [axial_add, axial_pPerturbationField he₁, modelField_index_zero, axial_neg, axial_smul]

theorem pPerturbationField_add_model_ne_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (he₁ : morseNorm n e₁ = 1) (hδ : 0 < δ)
    (hm : ∀ y : Fin n → ℝ, theta r₀ y * morseNorm n y < m) {y : Fin n → ℝ}
    (hψ : ψp ρa ρb y = 1) : modelField 0 r₀ y + pPerturbationField m δ τ ρa ρb e₁ y ≠ 0 := by
  intro h0
  rw [modelField_index_zero, pPerturbationField, hψ, mul_one, neg_add_eq_zero] at h0
  have hm0 : 0 < m := by have := hm 0; rwa [morseNorm_zero, mul_zero] at this
  set c := m * βp δ τ e₁ y with hc_def
  have hc : 0 ≤ c := mul_nonneg hm0.le (βp_nonneg _)
  have hθ := theta_pos hr₀ y
  have hy : y = (c / theta r₀ y) • e₁ := by
    rw [div_eq_inv_mul, mul_smul, ← h0, smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]
  have ha : 0 ≤ c / theta r₀ y := div_nonneg hc hθ.le
  have hβ : βp δ τ e₁ y = 1 := by
    calc βp δ τ e₁ y = βp δ τ e₁ ((c / theta r₀ y) • e₁) := by rw [← hy]
      _ = 1 := βp_smul_self he₁ hδ (by linarith)
  have hc' : c = m := by rw [hc_def, hβ, mul_one]
  have hnorm : morseNorm n y = c / theta r₀ y := by
    calc morseNorm n y = morseNorm n ((c / theta r₀ y) • e₁) := by rw [← hy]
      _ = c / theta r₀ y := by rw [morseNorm_smul_self he₁, abs_of_nonneg ha]
  have hlt := hm y
  rw [hnorm, hc'] at hlt
  have : theta r₀ y * (m / theta r₀ y) = m := by field_simp
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem pPerturbationField_add_model_ne_zero_of_le {r₀ : ℝ} (hr₀ : 0 < r₀) (he₁ : morseNorm n e₁ = 1)
    (hδ : 0 < δ) (hρ : 0 ≤ ρa) (hab : ρa < ρb)
    (hm : ∀ y : Fin n → ℝ, theta r₀ y * morseNorm n y < m) {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ ρa) : modelField 0 r₀ y + pPerturbationField m δ τ ρa ρb e₁ y ≠ 0 :=
  pPerturbationField_add_model_ne_zero hr₀ he₁ hδ hm (ψp_eq_one hρ hab hy)

theorem pPerturbationField_add_model_ne_zero_of_three_div_lt {r₀ : ℝ} (hr₀ : 0 < r₀) (he₁ : morseNorm n e₁ = 1)
    (hδ : 0 < δ) (hm : 3 / r₀ < m) {y : Fin n → ℝ} (hψ : ψp ρa ρb y = 1) :
    modelField 0 r₀ y + pPerturbationField m δ τ ρa ρb e₁ y ≠ 0 :=
  pPerturbationField_add_model_ne_zero hr₀ he₁ hδ (theta_mul_morseNorm_lt hr₀ hm) hψ

end PSide

section QSide

variable {k : ℕ} (hk : k ≤ n) (hk1 : k = 1)

def uq (y : Fin n → ℝ) : ℝ := negPart hk y ⟨0, by omega⟩

def e₀ : Fin n → ℝ := recombine hk (EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ)) 0

theorem uq_apply (y : Fin n → ℝ) : uq hk hk1 y = negPart hk y ⟨0, by omega⟩ := rfl

theorem uq_add (y z : Fin n → ℝ) : uq hk hk1 (y + z) = uq hk hk1 y + uq hk hk1 z := by
  simp only [uq, negPart_add]; rfl

theorem uq_smul (a : ℝ) (y : Fin n → ℝ) : uq hk hk1 (a • y) = a * uq hk hk1 y := by
  simp only [uq, negPart_smul]; rfl

theorem uq_neg (y : Fin n → ℝ) : uq hk hk1 (-y) = -uq hk hk1 y := by
  simp only [uq, negPart_neg]; rfl

theorem uq_zero : uq hk hk1 (0 : Fin n → ℝ) = 0 := rfl

theorem contDiff_uq : ContDiff ℝ ∞ (uq hk hk1) := by
  have : uq hk hk1 = fun y => (EuclideanSpace.proj (⟨0, by omega⟩ : Fin k) ∘L negPartL hk) y :=
    rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _

theorem continuous_uq : Continuous (uq hk hk1) := (contDiff_uq hk hk1).continuous

theorem contDiff_normSq_posPart : ContDiff ℝ ∞ (fun y : Fin n → ℝ => ‖posPart hk y‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (posPartL hk).contDiff

theorem continuous_normSq_posPart : Continuous (fun y : Fin n → ℝ => ‖posPart hk y‖ ^ 2) :=
  (contDiff_normSq_posPart hk).continuous

theorem norm_negPart_sq (y : Fin n → ℝ) : ‖negPart hk y‖ ^ 2 = uq hk hk1 y ^ 2 := by
  subst hk1
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]
  rfl

theorem morseNorm_sq_eq_uq (y : Fin n → ℝ) :
    morseNorm n y ^ 2 = uq hk hk1 y ^ 2 + ‖posPart hk y‖ ^ 2 := by
  rw [morseNorm_sq_eq_negPart_add_posPart hk, norm_negPart_sq hk hk1]

theorem eq_zero_of_uq_eq_zero {y : Fin n → ℝ} (hu : uq hk hk1 y = 0) (hv : posPart hk y = 0) :
    y = 0 := by
  rw [← morseNorm_eq_zero_iff, ← pow_eq_zero_iff two_ne_zero, morseNorm_sq_eq_uq hk hk1, hu, hv]
  simp

theorem morseNorm_eq_abs_uq {y : Fin n → ℝ} (hv : posPart hk y = 0) :
    morseNorm n y = |uq hk hk1 y| := by
  rw [← sq_eq_sq₀ (morseNorm_nonneg y) (abs_nonneg _), sq_abs, morseNorm_sq_eq_uq hk hk1, hv]
  simp

theorem negPart_e₀ : negPart hk (e₀ hk hk1) = EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) :=
  negPart_recombine hk _ _

theorem posPart_e₀ : posPart hk (e₀ hk hk1) = 0 := posPart_recombine hk _ _

theorem uq_e₀ : uq hk hk1 (e₀ hk hk1) = 1 := by
  rw [uq_apply, negPart_e₀]
  simp

theorem posPart_smul_e₀ (a : ℝ) : posPart hk (a • e₀ hk hk1) = 0 := by
  rw [posPart_smul, posPart_e₀, smul_zero]

theorem uq_smul_e₀ (a : ℝ) : uq hk hk1 (a • e₀ hk hk1) = a := by
  rw [uq_smul, uq_e₀, mul_one]

omit hk1 in
theorem posPart_zero : posPart hk (0 : Fin n → ℝ) = 0 := by ext j; rfl

variable (δ τ σ : ℝ)

def βq (y : Fin n → ℝ) : ℝ :=
  decreasingTransition ((‖posPart hk y‖ ^ 2 - τ ^ 2 * uq hk hk1 y ^ 2 - δ ^ 2) / δ ^ 2) *
    decreasingTransition ((-(σ * uq hk hk1 y) - δ / 2) / (δ / 2))

theorem contDiff_βq : ContDiff ℝ ∞ (βq hk hk1 δ τ σ) :=
  (contDiff_decreasingTransition.comp ((((contDiff_normSq_posPart hk).sub
      (contDiff_const.mul ((contDiff_uq hk hk1).pow 2))).sub contDiff_const).div_const _)).mul
    (contDiff_decreasingTransition.comp (((contDiff_const.mul (contDiff_uq hk hk1)).neg.sub
      contDiff_const).div_const _))

def ψq (ua ub : ℝ) (y : Fin n → ℝ) : ℝ := cut (ua ^ 2) (ub ^ 2) (uq hk hk1 y ^ 2)

theorem contDiff_ψq (ua ub : ℝ) : ContDiff ℝ ∞ (ψq hk hk1 ua ub) :=
  (contDiff_cut _ _).comp ((contDiff_uq hk hk1).pow 2)

def qPerturbationField (m ua ub : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  -(σ * m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y)) • e₀ hk hk1

theorem contDiff_qPerturbationField (m ua ub : ℝ) : ContDiff ℝ ∞ (qPerturbationField hk hk1 δ τ σ m ua ub) :=
  ((contDiff_const.mul ((contDiff_βq hk hk1 δ τ σ).mul (contDiff_ψq hk hk1 ua ub))).neg).smul
    contDiff_const

def qSupportRegion (ub : ℝ) : Set (Fin n → ℝ) :=
  {y | uq hk hk1 y ^ 2 ≤ ub ^ 2 ∧ ‖posPart hk y‖ ^ 2 ≤ τ ^ 2 * uq hk hk1 y ^ 2 + 2 * δ ^ 2 ∧
    -δ ≤ σ * uq hk hk1 y}

variable {δ τ σ}

theorem βq_nonneg (y : Fin n → ℝ) : 0 ≤ βq hk hk1 δ τ σ y := mul_nonneg (decreasingTransition_nonneg _) (decreasingTransition_nonneg _)

theorem βq_le_one (y : Fin n → ℝ) : βq hk hk1 δ τ σ y ≤ 1 :=
  (mul_le_mul (decreasingTransition_le_one _) (decreasingTransition_le_one _) (decreasingTransition_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem βq_eq_one (hδ : 0 < δ) {y : Fin n → ℝ}
    (h1 : ‖posPart hk y‖ ^ 2 ≤ τ ^ 2 * uq hk hk1 y ^ 2 + δ ^ 2)
    (h2 : -(δ / 2) ≤ σ * uq hk hk1 y) : βq hk hk1 δ τ σ y = 1 := by
  rw [βq, decreasingTransition_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
    decreasingTransition_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), mul_one]

theorem βq_eq_zero_of_posPart (hδ : 0 < δ) {y : Fin n → ℝ}
    (h : τ ^ 2 * uq hk hk1 y ^ 2 + 2 * δ ^ 2 ≤ ‖posPart hk y‖ ^ 2) : βq hk hk1 δ τ σ y = 0 := by
  rw [βq, decreasingTransition_eq_zero (by rw [le_div_iff₀ (by positivity)]; linarith), zero_mul]

theorem βq_eq_zero_of_uq (hδ : 0 < δ) {y : Fin n → ℝ} (h : σ * uq hk hk1 y ≤ -δ) :
    βq hk hk1 δ τ σ y = 0 := by
  rw [βq, decreasingTransition_eq_zero (t := (-(σ * uq hk hk1 y) - δ / 2) / (δ / 2))
    (by rw [le_div_iff₀ (by positivity)]; linarith), mul_zero]

theorem lt_of_βq_ne_zero (hδ : 0 < δ) {y : Fin n → ℝ} (h : βq hk hk1 δ τ σ y ≠ 0) :
    ‖posPart hk y‖ ^ 2 < τ ^ 2 * uq hk hk1 y ^ 2 + 2 * δ ^ 2 ∧ -δ < σ * uq hk hk1 y := by
  constructor
  · by_contra h'; exact h (βq_eq_zero_of_posPart hk hk1 hδ (not_lt.1 h'))
  · by_contra h'; exact h (βq_eq_zero_of_uq hk hk1 hδ (not_lt.1 h'))

theorem βq_zero (hδ : 0 < δ) : βq hk hk1 δ τ σ (0 : Fin n → ℝ) = 1 :=
  βq_eq_one hk hk1 hδ
    (by rw [uq_zero, posPart_zero, norm_zero]; nlinarith [sq_nonneg δ, sq_nonneg τ])
    (by rw [uq_zero, mul_zero]; linarith)

theorem βq_axis (hδ : 0 < δ) {y : Fin n → ℝ} (hv : posPart hk y = 0)
    (hu : -(δ / 2) ≤ σ * uq hk hk1 y) : βq hk hk1 δ τ σ y = 1 :=
  βq_eq_one hk hk1 hδ
    (by rw [hv, norm_zero]; nlinarith [sq_nonneg δ, sq_nonneg τ, sq_nonneg (uq hk hk1 y)]) hu

variable {ua ub : ℝ}

theorem ψq_nonneg (y : Fin n → ℝ) : 0 ≤ ψq hk hk1 ua ub y := cut_nonneg _ _ _

theorem ψq_le_one (y : Fin n → ℝ) : ψq hk hk1 ua ub y ≤ 1 := cut_le_one _ _ _

theorem ψq_eq_one (hua : 0 ≤ ua) (hab : ua < ub) {y : Fin n → ℝ}
    (hy : uq hk hk1 y ^ 2 ≤ ua ^ 2) : ψq hk hk1 ua ub y = 1 :=
  cut_eq_one (pow_lt_pow_left₀ hab hua two_ne_zero) hy

theorem ψq_eq_zero (hua : 0 ≤ ua) (hab : ua < ub) {y : Fin n → ℝ}
    (hy : ub ^ 2 ≤ uq hk hk1 y ^ 2) : ψq hk hk1 ua ub y = 0 :=
  cut_eq_zero (pow_lt_pow_left₀ hab hua two_ne_zero) hy

theorem sq_lt_of_ψq_ne_zero (hua : 0 ≤ ua) (hab : ua < ub) {y : Fin n → ℝ}
    (hy : ψq hk hk1 ua ub y ≠ 0) : uq hk hk1 y ^ 2 < ub ^ 2 := by
  by_contra h
  exact hy (ψq_eq_zero hk hk1 hua hab (not_lt.1 h))

theorem ψq_zero (hua : 0 ≤ ua) (hab : ua < ub) : ψq hk hk1 ua ub (0 : Fin n → ℝ) = 1 :=
  ψq_eq_one hk hk1 hua hab (by rw [uq_zero]; nlinarith [sq_nonneg ua])

variable {m : ℝ}

theorem posPart_qPerturbationField (y : Fin n → ℝ) : posPart hk (qPerturbationField hk hk1 δ τ σ m ua ub y) = 0 :=
  posPart_smul_e₀ hk hk1 _

theorem uq_qPerturbationField (y : Fin n → ℝ) :
    uq hk hk1 (qPerturbationField hk hk1 δ τ σ m ua ub y) =
      -(σ * m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y)) :=
  uq_smul_e₀ hk hk1 _

theorem isClosed_qSupportRegion : IsClosed (qSupportRegion hk hk1 δ τ σ ub) :=
  (isClosed_le ((continuous_uq hk hk1).pow 2) continuous_const).inter
    ((isClosed_le (continuous_normSq_posPart hk)
      ((continuous_const.mul ((continuous_uq hk hk1).pow 2)).add continuous_const)).inter
      (isClosed_le continuous_const (continuous_const.mul (continuous_uq hk hk1))))

theorem morseNorm_sq_le_of_mem_qSupportRegion {y : Fin n → ℝ} (hy : y ∈ qSupportRegion hk hk1 δ τ σ ub) :
    morseNorm n y ^ 2 ≤ ub ^ 2 + τ ^ 2 * ub ^ 2 + 2 * δ ^ 2 := by
  obtain ⟨h1, h2, _⟩ := hy
  rw [morseNorm_sq_eq_uq hk hk1]
  have : τ ^ 2 * uq hk hk1 y ^ 2 ≤ τ ^ 2 * ub ^ 2 := by gcongr
  linarith

theorem isCompact_qSupportRegion : IsCompact (qSupportRegion hk hk1 δ τ σ ub) :=
  (isCompact_morseNorm_le (Real.sqrt (ub ^ 2 + τ ^ 2 * ub ^ 2 + 2 * δ ^ 2))).of_isClosed_subset
    (isClosed_qSupportRegion hk hk1) fun y hy => by
      have h := morseNorm_sq_le_of_mem_qSupportRegion hk hk1 hy
      exact (Real.le_sqrt (morseNorm_nonneg y) ((sq_nonneg _).trans h)).2 h

theorem qSupportRegion_subset_ball {R : ℝ} (hR : 0 ≤ R) (h : ub ^ 2 + τ ^ 2 * ub ^ 2 + 2 * δ ^ 2 < R ^ 2) :
    qSupportRegion hk hk1 δ τ σ ub ⊆ Metric.ball 0 R := fun y hy => by
  apply mem_ball_of_morseNorm_lt
  have h1 := morseNorm_sq_le_of_mem_qSupportRegion hk hk1 hy
  exact (pow_lt_pow_iff_left₀ (morseNorm_nonneg y) hR two_ne_zero).1 (h1.trans_lt h)

theorem qPerturbationField_eq_zero_of_notMem (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub) {y : Fin n → ℝ}
    (hy : y ∉ qSupportRegion hk hk1 δ τ σ ub) : qPerturbationField hk hk1 δ τ σ m ua ub y = 0 := by
  by_contra h
  apply hy
  have h1 : βq hk hk1 δ τ σ y ≠ 0 := fun h' => h (by simp [qPerturbationField, h'])
  have h2 : ψq hk hk1 ua ub y ≠ 0 := fun h' => h (by simp [qPerturbationField, h'])
  obtain ⟨h3, h4⟩ := lt_of_βq_ne_zero hk hk1 hδ h1
  exact ⟨(sq_lt_of_ψq_ne_zero hk hk1 hua hab h2).le, h3.le, h4.le⟩

theorem support_qPerturbationField_subset (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub) :
    Function.support (qPerturbationField hk hk1 δ τ σ m ua ub) ⊆ qSupportRegion hk hk1 δ τ σ ub := fun _ hy => by
  by_contra h
  exact hy (qPerturbationField_eq_zero_of_notMem hk hk1 hδ hua hab h)

theorem tsupport_qPerturbationField_subset (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub) :
    tsupport (qPerturbationField hk hk1 δ τ σ m ua ub) ⊆ qSupportRegion hk hk1 δ τ σ ub :=
  closure_minimal (support_qPerturbationField_subset hk hk1 hδ hua hab) (isClosed_qSupportRegion hk hk1)

theorem hasCompactSupport_qPerturbationField (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub) :
    HasCompactSupport (qPerturbationField hk hk1 δ τ σ m ua ub) :=
  (isCompact_qSupportRegion hk hk1).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_qPerturbationField_subset hk hk1 hδ hua hab)

theorem uq_modelField (r₀ : ℝ) (y : Fin n → ℝ) :
    uq hk hk1 (modelField k r₀ y) = theta r₀ y * uq hk hk1 y := by
  simp only [uq, negPart_modelField]; rfl

theorem posPart_modelField_add_qPerturbationField (r₀ : ℝ) (y : Fin n → ℝ) :
    posPart hk (modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y) =
      -(theta r₀ y • posPart hk y) := by
  rw [posPart_add, posPart_qPerturbationField, add_zero, posPart_modelField]

theorem uq_modelField_add_qPerturbationField (r₀ : ℝ) (y : Fin n → ℝ) :
    uq hk hk1 (modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y) =
      theta r₀ y * uq hk hk1 y - σ * m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y) := by
  rw [uq_add, uq_qPerturbationField, uq_modelField, sub_eq_add_neg]

theorem qPerturbationField_add_model_ne_zero_of_posPart_ne_zero {r₀ : ℝ} (hr₀ : 0 < r₀) {y : Fin n → ℝ}
    (hv : posPart hk y ≠ 0) : modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y ≠ 0 := by
  intro h
  have h1 := congrArg (posPart hk) h
  rw [posPart_modelField_add_qPerturbationField, posPart_zero, neg_eq_zero, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (theta_pos hr₀ y).ne' h1
  · exact hv h1

theorem σ_mul_uq_modelField_add_qPerturbationField_neg {r₀ : ℝ} (hr₀ : 0 < r₀) (hσ : σ = 1 ∨ σ = -1)
    (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub)
    (hm : ∀ y : Fin n → ℝ, theta r₀ y * morseNorm n y < m) {y : Fin n → ℝ}
    (hv : posPart hk y = 0) (h : σ * uq hk hk1 y ≤ 0 ∨ ψq hk hk1 ua ub y = 1) :
    σ * uq hk hk1 (modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y) < 0 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hm0 : 0 < m := by have := hm 0; rwa [morseNorm_zero, mul_zero] at this
  have hθ := theta_pos hr₀ y
  have hβ := βq_nonneg hk hk1 (δ := δ) (τ := τ) (σ := σ) y
  have hψ := ψq_nonneg hk hk1 (ua := ua) (ub := ub) y
  rw [uq_modelField_add_qPerturbationField]
  have e : σ * (theta r₀ y * uq hk hk1 y - σ * m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y)) =
      theta r₀ y * (σ * uq hk hk1 y) -
        m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y) := by
    linear_combination (-(m * (βq hk hk1 δ τ σ y * ψq hk hk1 ua ub y))) * hσ2
  rw [e]
  rcases lt_or_ge 0 (σ * uq hk hk1 y) with hpos | hnp
  · have hψ1 : ψq hk hk1 ua ub y = 1 := by
      rcases h with h | h
      · exact absurd hpos (not_lt.2 h)
      · exact h
    have hβ1 : βq hk hk1 δ τ σ y = 1 := βq_axis hk hk1 hδ hv (by linarith)
    rw [hψ1, hβ1, mul_one, mul_one]
    have habs : σ * uq hk hk1 y = morseNorm n y := by
      rw [morseNorm_eq_abs_uq hk hk1 hv]
      rcases hσ with h | h
      · rw [h, one_mul]; rw [h, one_mul] at hpos; exact (abs_of_pos hpos).symm
      · rw [h, neg_one_mul]; rw [h, neg_one_mul] at hpos
        exact (abs_of_neg (by linarith)).symm
    rw [habs]
    linarith [hm y]
  · rcases hnp.lt_or_eq with hneg | hzero
    · have : theta r₀ y * (σ * uq hk hk1 y) < 0 := mul_neg_of_pos_of_neg hθ hneg
      nlinarith [mul_nonneg hβ hψ]
    · have hu : uq hk hk1 y = 0 := by
        rcases mul_eq_zero.1 hzero with h | h
        · exact absurd h hσ0
        · exact h
      have hy0 : y = 0 := eq_zero_of_uq_eq_zero hk hk1 hu hv
      rw [hzero, hy0, βq_zero hk hk1 hδ, ψq_zero hk hk1 hua hab]
      linarith

theorem qPerturbationField_add_model_ne_zero_axis {r₀ : ℝ} (hr₀ : 0 < r₀) (hσ : σ = 1 ∨ σ = -1)
    (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub)
    (hm : ∀ y : Fin n → ℝ, theta r₀ y * morseNorm n y < m) {y : Fin n → ℝ}
    (hv : posPart hk y = 0) (h : σ * uq hk hk1 y ≤ 0 ∨ ψq hk hk1 ua ub y = 1) :
    modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y ≠ 0 := by
  intro h0
  have := σ_mul_uq_modelField_add_qPerturbationField_neg hk hk1 (τ := τ) hr₀ hσ hδ hua hab hm hv h
  rw [h0, uq_zero, mul_zero] at this
  exact lt_irrefl _ this

theorem qPerturbationField_add_model_ne_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (hσ : σ = 1 ∨ σ = -1)
    (hδ : 0 < δ) (hua : 0 ≤ ua) (hab : ua < ub)
    (hm : ∀ y : Fin n → ℝ, theta r₀ y * morseNorm n y < m) {y : Fin n → ℝ}
    (h : posPart hk y ≠ 0 ∨ σ * uq hk hk1 y ≤ 0 ∨ ψq hk hk1 ua ub y = 1) :
    modelField k r₀ y + qPerturbationField hk hk1 δ τ σ m ua ub y ≠ 0 := by
  by_cases hv : posPart hk y = 0
  · rcases h with h | h
    · exact absurd hv h
    · exact qPerturbationField_add_model_ne_zero_axis hk hk1 hr₀ hσ hδ hua hab hm hv h
  · exact qPerturbationField_add_model_ne_zero_of_posPart_ne_zero hk hk1 hr₀ hv

end QSide

theorem cut_le_cut_of_le {lo lo' w : ℝ} (hw : 0 < w) (h : lo ≤ lo') (t : ℝ) :
    cut lo (lo + w) t ≤ cut lo' (lo' + w) t := by
  unfold cut
  simp only [add_sub_cancel_left]
  exact decreasingTransition_antitone (div_le_div_of_nonneg_right (by linarith) hw.le)

def plateau (lo₁ lo₂ hi₁ hi₂ t : ℝ) : ℝ := cut lo₂ lo₁ t * cut hi₁ hi₂ t

theorem contDiff_plateau (lo₁ lo₂ hi₁ hi₂ : ℝ) : ContDiff ℝ ∞ (plateau lo₁ lo₂ hi₁ hi₂) :=
  (contDiff_cut _ _).mul (contDiff_cut _ _)

theorem plateau_nonneg (lo₁ lo₂ hi₁ hi₂ t : ℝ) : 0 ≤ plateau lo₁ lo₂ hi₁ hi₂ t :=
  mul_nonneg (cut_nonneg _ _ _) (cut_nonneg _ _ _)

theorem plateau_le_one (lo₁ lo₂ hi₁ hi₂ t : ℝ) : plateau lo₁ lo₂ hi₁ hi₂ t ≤ 1 :=
  (mul_le_mul (cut_le_one _ _ _) (cut_le_one _ _ _) (cut_nonneg _ _ _) zero_le_one).trans_eq
    (one_mul 1)

theorem plateau_eq_one {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hlo : lo₁ < lo₂) (hhi : hi₁ < hi₂)
    (h1 : lo₂ ≤ t) (h2 : t ≤ hi₁) : plateau lo₁ lo₂ hi₁ hi₂ t = 1 := by
  rw [plateau, ← one_sub_cut hlo.ne, cut_eq_zero hlo h1, cut_eq_one hhi h2]; ring

theorem plateau_eq_zero_of_le {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hlo : lo₁ < lo₂) (h : t ≤ lo₁) :
    plateau lo₁ lo₂ hi₁ hi₂ t = 0 := by
  rw [plateau, ← one_sub_cut hlo.ne, cut_eq_one hlo h]; ring

theorem plateau_eq_zero_of_ge {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hhi : hi₁ < hi₂) (h : hi₂ ≤ t) :
    plateau lo₁ lo₂ hi₁ hi₂ t = 0 := by
  rw [plateau, cut_eq_zero hhi h, mul_zero]

theorem plateau_eq_cut_low {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hhi : hi₁ < hi₂) (h : t ≤ hi₁) :
    plateau lo₁ lo₂ hi₁ hi₂ t = cut lo₂ lo₁ t := by
  rw [plateau, cut_eq_one hhi h, mul_one]

theorem plateau_eq_cut_high {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hlo : lo₁ < lo₂) (h : lo₂ ≤ t) :
    plateau lo₁ lo₂ hi₁ hi₂ t = cut hi₁ hi₂ t := by
  rw [plateau, ← one_sub_cut hlo.ne, cut_eq_zero hlo h, sub_zero, one_mul]

theorem plateau_lt_of_ne_zero {lo₁ lo₂ hi₁ hi₂ t : ℝ} (hlo : lo₁ < lo₂) (hhi : hi₁ < hi₂)
    (h : plateau lo₁ lo₂ hi₁ hi₂ t ≠ 0) : lo₁ < t ∧ t < hi₂ := by
  constructor
  · by_contra h'; exact h (plateau_eq_zero_of_le hlo (not_lt.1 h'))
  · by_contra h'; exact h (plateau_eq_zero_of_ge hhi (not_lt.1 h'))

theorem ψp_add_plateau {fp lo₁ lo₂ hi₁ hi₂ ρa ρb : ℝ} (hlo : lo₁ < lo₂) (hhi : hi₁ < hi₂)
    (ha : ρa ^ 2 = 2 * (lo₁ - fp)) (hb : ρb ^ 2 = 2 * (lo₂ - fp)) {y : Fin n → ℝ}
    (hy : fp + morseNorm n y ^ 2 / 2 ≤ hi₁) :
    ψp ρa ρb y + plateau lo₁ lo₂ hi₁ hi₂ (fp + morseNorm n y ^ 2 / 2) = 1 := by
  rw [plateau_eq_cut_low hhi hy, ← one_sub_cut hlo.ne, ψp]
  have e1 : lo₁ = fp + (1 / 2) * ρa ^ 2 := by rw [ha]; ring
  have e2 : lo₂ = fp + (1 / 2) * ρb ^ 2 := by rw [hb]; ring
  have e3 : fp + morseNorm n y ^ 2 / 2 = fp + (1 / 2) * morseNorm n y ^ 2 := by ring
  rw [e1, e2, e3, cut_affine (by norm_num)]
  ring

theorem ψq_add_plateau {k : ℕ} (hk : k ≤ n) (hk1 : k = 1) {fq lo₁ lo₂ hi₁ hi₂ ua ub : ℝ}
    (hlo : lo₁ < lo₂) (hhi : hi₁ < hi₂) (ha : ua ^ 2 = 2 * (fq - hi₂))
    (hb : ub ^ 2 = 2 * (fq - hi₁)) {y : Fin n → ℝ}
    (hy : lo₂ ≤ fq - uq hk hk1 y ^ 2 / 2) :
    ψq hk hk1 ua ub y + plateau lo₁ lo₂ hi₁ hi₂ (fq - uq hk hk1 y ^ 2 / 2) = 1 := by
  rw [plateau_eq_cut_high hlo hy, ψq]
  have e1 : hi₂ = fq + (-1 / 2) * ua ^ 2 := by rw [ha]; ring
  have e2 : hi₁ = fq + (-1 / 2) * ub ^ 2 := by rw [hb]; ring
  have e3 : fq - uq hk hk1 y ^ 2 / 2 = fq + (-1 / 2) * uq hk hk1 y ^ 2 := by ring
  rw [e1, e2, e3, cut_affine (by norm_num), ← one_sub_cut]
  · ring
  · intro h
    rw [ha, hb] at h
    linarith

theorem perpSq_lt_of_βp_ne_zero {δ τ ρa : ℝ} {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1)
    (hδ : 0 < δ) (hρa : 0 < ρa) {y : Fin n → ℝ} (h : βp δ τ e₁ y ≠ 0) (hy : ρa ≤ morseNorm n y) :
    perpSq e₁ y < (τ ^ 2 + 2 * δ ^ 2 / ρa ^ 2) * morseNorm n y ^ 2 := by
  obtain ⟨h1, _⟩ := lt_of_βp_ne_zero hδ h
  have h2 : axial e₁ y ^ 2 ≤ morseNorm n y ^ 2 := by
    have := perpSq_nonneg he₁ y; rw [perpSq] at this; linarith
  have h3 : ρa ^ 2 ≤ morseNorm n y ^ 2 := pow_le_pow_left₀ hρa.le hy 2
  have h4 : 2 * δ ^ 2 ≤ 2 * δ ^ 2 / ρa ^ 2 * morseNorm n y ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : τ ^ 2 * axial e₁ y ^ 2 ≤ τ ^ 2 * morseNorm n y ^ 2 := by gcongr
  nlinarith

def dotL (z : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm z)) ∘L
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap

theorem dotL_apply (z w : Fin n → ℝ) : dotL z w = dot z w := rfl

theorem morseNorm_smul (a : ℝ) (y : Fin n → ℝ) : morseNorm n (a • y) = |a| * morseNorm n y := by
  change ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (a • y)‖ = _
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  rfl

theorem morseNorm_pos {y : Fin n → ℝ} (hy : y ≠ 0) : 0 < morseNorm n y :=
  lt_of_le_of_ne (morseNorm_nonneg y) (Ne.symm (mt (morseNorm_eq_zero_iff y).1 hy))

def axialDefect (e₁ y : Fin n → ℝ) : ℝ := 1 - axial e₁ y / morseNorm n y

def axialDefectDeriv (e₁ y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (axial e₁ y / morseNorm n y ^ 3) • dotL y - (morseNorm n y)⁻¹ • dotL e₁

theorem axialDefectDeriv_apply (e₁ y w : Fin n → ℝ) :
    axialDefectDeriv e₁ y w = axial e₁ y / morseNorm n y ^ 3 * dot y w - (morseNorm n y)⁻¹ * dot e₁ w := by
  simp [axialDefectDeriv, dotL_apply]

theorem axialDefect_smul (e₁ : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (y : Fin n → ℝ) :
    axialDefect e₁ (t • y) = axialDefect e₁ y := by
  rw [axialDefect, axialDefect, axial_smul, morseNorm_smul, abs_of_pos ht]
  by_cases hy : morseNorm n y = 0
  · rw [hy]; simp
  · rw [mul_div_mul_left _ _ ht.ne']

theorem hasFDerivAt_morseNorm_sq (y : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => morseNorm n y ^ 2) (2 • dotL y) y := by
  have := (hasStrictFDerivAt_norm_sq ((EuclideanSpace.equiv (Fin n) ℝ).symm y)).hasFDerivAt.comp y
    (EuclideanSpace.equiv (Fin n) ℝ).symm.hasFDerivAt
  refine this.congr_fderiv ?_
  ext w
  simp [dotL]

theorem hasFDerivAt_morseNorm {y : Fin n → ℝ} (hy : y ≠ 0) :
    HasFDerivAt (morseNorm n) ((morseNorm n y)⁻¹ • dotL y) y := by
  have hρ := morseNorm_pos hy
  have h1 := (Real.hasDerivAt_sqrt (by positivity : morseNorm n y ^ 2 ≠ 0)).comp_hasFDerivAt y
    (hasFDerivAt_morseNorm_sq y)
  have e : ((√·) ∘ fun y : Fin n → ℝ => morseNorm n y ^ 2) = morseNorm n :=
    funext fun y => Real.sqrt_sq (morseNorm_nonneg y)
  rw [e] at h1
  refine h1.congr_fderiv ?_
  rw [Real.sqrt_sq hρ.le]
  ext w
  simp
  field_simp

theorem hasFDerivAt_axial (e₁ y : Fin n → ℝ) : HasFDerivAt (axial e₁) (dotL e₁) y := by
  have := (dotL e₁).hasFDerivAt (x := y)
  convert this using 1
  ext w
  rw [dotL_apply, axial, dot_comm]

theorem hasFDerivAt_axialDefect (e₁ : Fin n → ℝ) {y : Fin n → ℝ} (hy : y ≠ 0) :
    HasFDerivAt (axialDefect e₁) (axialDefectDeriv e₁ y) y := by
  have hρ := morseNorm_pos hy
  have h3 := (hasDerivAt_inv hρ.ne').comp_hasFDerivAt y (hasFDerivAt_morseNorm hy)
  have h5 := (hasFDerivAt_axial e₁ y).mul h3
  have h6 := (hasFDerivAt_const (1 : ℝ) y).sub h5
  have e : axialDefect e₁ = fun y => 1 - axial e₁ y * (fun y => (morseNorm n y)⁻¹) y := by
    funext y; simp [axialDefect, div_eq_mul_inv]
  rw [e]
  refine h6.congr_fderiv ?_
  ext w
  simp [axialDefectDeriv, dotL_apply]
  field_simp
  ring

theorem contDiffAt_morseNorm {y : Fin n → ℝ} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (morseNorm n) y := by
  have h0 : (EuclideanSpace.equiv (Fin n) ℝ).symm y ≠ 0 := by
    intro h; apply hy; simpa using h
  exact (contDiffAt_norm ℝ (n := ∞) h0).comp y
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt

theorem contDiffAt_axialDefect (e₁ : Fin n → ℝ) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ (axialDefect e₁) y :=
  contDiffAt_const.sub ((contDiff_axial e₁).contDiffAt.div (contDiffAt_morseNorm hy)
    (morseNorm_pos hy).ne')

theorem fderiv_axialDefect (e₁ : Fin n → ℝ) {y : Fin n → ℝ} (hy : y ≠ 0) :
    fderiv ℝ (axialDefect e₁) y = axialDefectDeriv e₁ y := (hasFDerivAt_axialDefect e₁ hy).fderiv

theorem axialDefectDeriv_self (e₁ : Fin n → ℝ) {y : Fin n → ℝ} (hy : y ≠ 0) : axialDefectDeriv e₁ y y = 0 := by
  have hρ := morseNorm_pos hy
  rw [axialDefectDeriv_apply, dot_self, axial, dot_comm]
  field_simp
  ring

theorem axialDefectDeriv_e₁ {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) {y : Fin n → ℝ} (hy : y ≠ 0) :
    axialDefectDeriv e₁ y e₁ = -(perpSq e₁ y / morseNorm n y ^ 3) := by
  have hρ := morseNorm_pos hy
  rw [axialDefectDeriv_apply, dot_self, he₁, perpSq, axial]
  field_simp
  ring

theorem axialDefectDeriv_e₁_neg {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) {y : Fin n → ℝ} (hy : y ≠ 0)
    (h : 0 < perpSq e₁ y) : axialDefectDeriv e₁ y e₁ < 0 := by
  rw [axialDefectDeriv_e₁ he₁ hy]
  have := morseNorm_pos hy
  have : 0 < perpSq e₁ y / morseNorm n y ^ 3 := by positivity
  linarith

theorem axialDefect_nonneg {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) (y : Fin n → ℝ) : 0 ≤ axialDefect e₁ y := by
  rw [axialDefect, sub_nonneg]
  by_cases hy : y = 0
  · subst hy; simp [axial_zero]
  · have hρ := morseNorm_pos hy
    rw [div_le_one hρ]
    have := axial_sq_le he₁ y
    nlinarith [abs_le_of_sq_le_sq' this hρ.le]

theorem axialDefect_smul_self {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) {a : ℝ} (ha : 0 < a) :
    axialDefect e₁ (a • e₁) = 0 := by
  rw [axialDefect, axial_smul_self he₁, morseNorm_smul_self he₁, abs_of_pos ha, div_self ha.ne', sub_self]

theorem axialDefect_pos_of_perpSq_pos (e₁ : Fin n → ℝ) {y : Fin n → ℝ}
    (h : 0 < perpSq e₁ y) : 0 < axialDefect e₁ y := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [perpSq, axial_zero, morseNorm_zero] at h; norm_num at h
  have hρ := morseNorm_pos hy
  rw [axialDefect, sub_pos, div_lt_one hρ]
  rw [perpSq] at h
  nlinarith [abs_le_of_sq_le_sq' (le_of_lt (by linarith : axial e₁ y ^ 2 < morseNorm n y ^ 2))
    hρ.le]

theorem axialDefect_eq_zero_iff {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) {y : Fin n → ℝ} (hy : y ≠ 0) :
    axialDefect e₁ y = 0 ↔ y = morseNorm n y • e₁ := by
  have hρ := morseNorm_pos hy
  constructor
  · intro h
    rw [axialDefect, sub_eq_zero, eq_comm, div_eq_one_iff_eq hρ.ne'] at h
    have hp : perpSq e₁ y = 0 := by rw [perpSq, h]; ring
    rw [← h]; exact eq_smul_of_perpSq_eq_zero he₁ hp
  · intro h
    rw [h, axialDefect_smul_self he₁ hρ]

end

end DifferentialGeometry.Topology.CancelModel
