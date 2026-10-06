module

public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.CancelTransverse
public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.CancelModel

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose)
open CancelModel

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace CancelModel

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_pos_norm_le_of_injective (L : E →L[ℝ] F) (hinj : Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
  by_cases hE : ∃ v : E, v ≠ 0
  · obtain ⟨v₀, hv₀⟩ := hE
    have hcont : Continuous fun v : E => ‖L v‖ := L.continuous.norm
    have hsph : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      ⟨‖v₀‖⁻¹ • v₀, by simp [norm_smul, norm_ne_zero_iff.2 hv₀]⟩
    obtain ⟨w, hw, hmin⟩ := hsph.exists_isMinOn hne hcont.continuousOn
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hwne : w ≠ 0 := by rintro rfl; simp at hw1
    have hLw : 0 < ‖L w‖ := norm_pos_iff.2 fun h => hwne (hinj (by rw [h, map_zero]))
    refine ⟨‖L w‖, hLw, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, hnv.ne']
      have h1 : ‖L w‖ ≤ ‖v‖⁻¹ * ‖L v‖ := by
        have := hmin hmem
        simpa [map_smul, norm_smul, abs_of_pos (inv_pos.2 hnv)] using this
      have h2 : ‖L w‖ * ‖v‖ ≤ ‖v‖⁻¹ * ‖L v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right h1 hnv.le
      have h3 : ‖v‖⁻¹ * ‖L v‖ * ‖v‖ = ‖L v‖ := by field_simp
      linarith
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by_contra fun h => hE ⟨v, h⟩
    rw [hv]; simp

theorem exists_pos_inner_of_injective {P : E → F} {r : ℝ} (hr : 0 < r)
    (hP : ContDiffOn ℝ 1 P (Metric.ball 0 r)) (h0 : P 0 = 0)
    (hinj : Function.Injective (fderiv ℝ P 0)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ v, v ≠ 0 → ‖v‖ < δ₀ →
      0 < ⟪P v, fderiv ℝ P v v⟫ := by
  set L := fderiv ℝ P 0 with hL
  obtain ⟨c, hc, hcL⟩ := exists_pos_norm_le_of_injective L hinj
  have hball : Metric.ball (0 : E) r ∈ 𝓝 0 :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  have hder : HasFDerivAt P L 0 :=
    ((hP.differentiableOn one_ne_zero).differentiableAt hball).hasFDerivAt
  have hcontD : ContinuousAt (fderiv ℝ P) 0 :=
    (hP.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).continuousAt hball
  set ε := min (c / 2) (c ^ 2 / (8 * (‖L‖ + 1))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεc : ε ≤ c / 2 := min_le_left _ _
  have hεL : 2 * ε * ‖L‖ ≤ c ^ 2 / 4 := by
    have h1 : ε ≤ c ^ 2 / (8 * (‖L‖ + 1)) := min_le_right _ _
    have h2 : 0 ≤ ‖L‖ := norm_nonneg _
    have h3 : c ^ 2 / (8 * (‖L‖ + 1)) * ‖L‖ ≤ c ^ 2 / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg c]
    nlinarith
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hder)
  have hbound := Asymptotics.isLittleO_iff.1 hlo hε0
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hbound
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 hcontD ε hε0
  refine ⟨min (min δ₁ δ₂) r, by positivity, fun v hv hvδ => ?_⟩
  have hv1 : ‖v‖ < δ₁ := lt_of_lt_of_le hvδ ((min_le_left _ _).trans (min_le_left _ _))
  have hv2 : ‖v‖ < δ₂ := lt_of_lt_of_le hvδ ((min_le_left _ _).trans (min_le_right _ _))
  have ha := hδ₁' (show dist v 0 < δ₁ by simpa using hv1)
  simp only [zero_add, h0, sub_zero] at ha
  have hb' := hδ₂' (show dist v 0 < δ₂ by simpa using hv2)
  rw [dist_eq_norm] at hb'
  set a := P v - L v with ha_def
  set b := fderiv ℝ P v v - L v with hb_def
  have hbb : ‖b‖ ≤ ε * ‖v‖ := by
    have : b = (fderiv ℝ P v - L) v := by simp [hb_def]
    rw [this]
    calc ‖(fderiv ℝ P v - L) v‖ ≤ ‖fderiv ℝ P v - L‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hb'.le (norm_nonneg _)
  have hPv : P v = L v + a := by simp [ha_def]
  have hDv : fderiv ℝ P v v = L v + b := by simp [hb_def]
  rw [hPv, hDv, inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq]
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hLv : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
  have hcv := hcL v
  have i1 := abs_real_inner_le_norm (L v) b
  have i2 := abs_real_inner_le_norm a (L v)
  have i3 := abs_real_inner_le_norm a b
  have e1 : -(‖L v‖ * ‖b‖) ≤ ⟪L v, b⟫ := (abs_le.1 i1).1
  have e2 : -(‖a‖ * ‖L v‖) ≤ ⟪a, L v⟫ := (abs_le.1 i2).1
  have e3 : -(‖a‖ * ‖b‖) ≤ ⟪a, b⟫ := (abs_le.1 i3).1
  have hLb : ‖L v‖ * ‖b‖ ≤ ‖L‖ * ‖v‖ * (ε * ‖v‖) :=
    mul_le_mul hLv hbb (norm_nonneg _) (by positivity)
  have haL : ‖a‖ * ‖L v‖ ≤ ε * ‖v‖ * (‖L‖ * ‖v‖) :=
    mul_le_mul ha hLv (norm_nonneg _) (by positivity)
  have hab : ‖a‖ * ‖b‖ ≤ ε * ‖v‖ * (ε * ‖v‖) :=
    mul_le_mul ha hbb (norm_nonneg _) (by positivity)
  have hc2 : c ^ 2 * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2 := by
    have := mul_le_mul hcv hcv (by positivity) (norm_nonneg _)
    nlinarith
  have hεε : ε * ε ≤ c ^ 2 / 4 := by nlinarith
  have hv2' : 0 < ‖v‖ ^ 2 := by positivity
  have key : ‖L v‖ ^ 2 -
      (‖L‖ * ‖v‖ * (ε * ‖v‖) + ε * ‖v‖ * (‖L‖ * ‖v‖) + ε * ‖v‖ * (ε * ‖v‖)) ≤
      ‖L v‖ ^ 2 + ⟪L v, b⟫ + (⟪a, L v⟫ + ⟪a, b⟫) := by
    linarith [e1, e2, e3, hLb, haL, hab]
  have hsum : ‖L‖ * ‖v‖ * (ε * ‖v‖) + ε * ‖v‖ * (‖L‖ * ‖v‖) +
      ε * ‖v‖ * (ε * ‖v‖) = (2 * ε * ‖L‖ + ε * ε) * ‖v‖ ^ 2 := by ring
  have hsum' : (2 * ε * ‖L‖ + ε * ε) * ‖v‖ ^ 2 ≤
      (c ^ 2 / 4 + c ^ 2 / 4) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (add_le_add hεL hεε) hv2'.le
  have hpos := mul_pos (pow_pos hc 2) hv2'
  linarith [key, hc2, hsum, hsum', hpos]

end CancelModel

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

def m' : ℝ := 3 / c.e.r₀ + 3 / c.d.r₀ + 1

theorem three_div_r₀p_lt_m' : 3 / c.e.r₀ < c.m' := by
  unfold m'
  have := c.d.hr₀
  have : 0 < 3 / c.d.r₀ := by positivity
  linarith

theorem three_div_r₀q_lt_m' : 3 / c.d.r₀ < c.m' := by
  unfold m'
  have := c.e.hr₀
  have : 0 < 3 / c.e.r₀ := by positivity
  linarith

theorem m'_pos : 0 < c.m' := by
  have := c.three_div_r₀p_lt_m'
  have := c.e.hr₀
  have : 0 < 3 / c.e.r₀ := by positivity
  linarith

theorem hm_p (y : Fin n → ℝ) : ModelField.theta c.e.r₀ y * morseNorm n y < c.m' :=
  theta_mul_morseNorm_lt c.e.hr₀ c.three_div_r₀p_lt_m' y

theorem hm_q (y : Fin n → ℝ) : ModelField.theta c.d.r₀ y * morseNorm n y < c.m' :=
  theta_mul_morseNorm_lt c.d.hr₀ c.three_div_r₀q_lt_m' y

def lo₁ : ℝ := c.c₁ - c.η / 4
def lo₂ : ℝ := c.c₁ + c.η / 4
def hi₁ : ℝ := c.c₂ - c.η / 4
def hi₂ : ℝ := c.c₂ + c.η / 4

theorem lo₁_lt_lo₂ : c.lo₁ < c.lo₂ := by unfold lo₁ lo₂; linarith [c.η_pos]
theorem hi₁_lt_hi₂ : c.hi₁ < c.hi₂ := by unfold hi₁ hi₂; linarith [c.η_pos]

theorem η_lt_ε : c.η < c.ε := by
  have := c.η_lt_left; have := c.ε₁_lt_ε; nlinarith [sq_nonneg c.e.r₀]

theorem η_lt_c₂_sub_c₁ : c.η < c.c₂ - c.c₁ := by
  have h1 := c.η_lt_left
  unfold c₂ c₁ ε₁ ε₂ at *
  have := c.hlt; have := c.hr₀p; have := c.hr₀q
  linarith

theorem lo₂_lt_hi₁ : c.lo₂ < c.hi₁ := by
  unfold lo₂ hi₁; linarith [c.η_lt_c₂_sub_c₁, c.η_pos]

def ρA : ℝ := Real.sqrt (2 * c.ε₁ - c.η / 2)
def ρB : ℝ := Real.sqrt (2 * c.ε₁ + c.η / 2)

def uA : ℝ := Real.sqrt (2 * c.ε₂ - c.η / 2)
def uB : ℝ := Real.sqrt (2 * c.ε₂ + c.η / 2)

theorem two_ε₁_sub_pos : 0 < 2 * c.ε₁ - c.η / 2 := by
  have := c.η_lt_left; have := c.ε₁_pos; nlinarith [sq_nonneg c.e.r₀]

theorem two_ε₂_sub_pos : 0 < 2 * c.ε₂ - c.η / 2 := by
  have := c.η_lt_right; have := c.ε₂_pos; nlinarith [sq_nonneg c.d.r₀]

theorem ρA_sq : c.ρA ^ 2 = 2 * c.ε₁ - c.η / 2 := Real.sq_sqrt c.two_ε₁_sub_pos.le
theorem ρB_sq : c.ρB ^ 2 = 2 * c.ε₁ + c.η / 2 :=
  Real.sq_sqrt (by linarith [c.two_ε₁_sub_pos, c.η_pos])
theorem uA_sq : c.uA ^ 2 = 2 * c.ε₂ - c.η / 2 := Real.sq_sqrt c.two_ε₂_sub_pos.le
theorem uB_sq : c.uB ^ 2 = 2 * c.ε₂ + c.η / 2 :=
  Real.sq_sqrt (by linarith [c.two_ε₂_sub_pos, c.η_pos])

theorem ρA_pos : 0 < c.ρA := Real.sqrt_pos.2 c.two_ε₁_sub_pos
theorem uA_pos : 0 < c.uA := Real.sqrt_pos.2 c.two_ε₂_sub_pos
theorem ρA_lt_ρB : c.ρA < c.ρB :=
  Real.sqrt_lt_sqrt c.two_ε₁_sub_pos.le (by linarith [c.η_pos])
theorem uA_lt_uB : c.uA < c.uB :=
  Real.sqrt_lt_sqrt c.two_ε₂_sub_pos.le (by linarith [c.η_pos])
theorem ρB_pos : 0 < c.ρB := c.ρA_pos.trans c.ρA_lt_ρB
theorem uB_pos : 0 < c.uB := c.uA_pos.trans c.uA_lt_uB

theorem r₀p_lt_ρA : c.e.r₀ < c.ρA := by
  rw [ρA, Real.lt_sqrt c.e.hr₀.le]
  have := c.η_lt_left; have := c.η_pos; nlinarith
theorem r₀q_lt_uA : c.d.r₀ < c.uA := by
  rw [uA, Real.lt_sqrt c.d.hr₀.le]
  have := c.η_lt_right; have := c.η_pos; nlinarith

theorem ρB_sq_lt : c.ρB ^ 2 < 2 * c.ε := by
  rw [c.ρB_sq]
  have := c.η_lt_left; have := c.ε₁_lt_ε
  unfold ε₁ at *; nlinarith [sq_nonneg c.e.r₀]
theorem uB_sq_lt : c.uB ^ 2 < 2 * c.ε := by
  rw [c.uB_sq]
  have := c.η_lt_right; have := c.ε₂_lt_ε
  unfold ε₂ at *; nlinarith [sq_nonneg c.d.r₀]

theorem ρA_sq_eq : c.ρA ^ 2 = 2 * (c.lo₁ - f p) := by rw [c.ρA_sq]; unfold lo₁ c₁; ring
theorem ρB_sq_eq : c.ρB ^ 2 = 2 * (c.lo₂ - f p) := by rw [c.ρB_sq]; unfold lo₂ c₁; ring
theorem uA_sq_eq : c.uA ^ 2 = 2 * (f q - c.hi₂) := by rw [c.uA_sq]; unfold hi₂ c₂; ring
theorem uB_sq_eq : c.uB ^ 2 = 2 * (f q - c.hi₁) := by rw [c.uB_sq]; unfold hi₁ c₂; ring

def e₁ : Fin n → ℝ := (Real.sqrt (2 * c.ε))⁻¹ • c.y₀

theorem sqrt_two_ε_pos : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith [c.hε])

theorem morseNorm_y₀ : morseNorm n c.y₀ = Real.sqrt (2 * c.ε) := by
  rw [← c.morseNorm_y₀_sq, Real.sqrt_sq (ModelField.morseNorm_nonneg _)]

theorem morseNorm_e₁ : morseNorm n c.e₁ = 1 := by
  rw [e₁, ModelField.morseNorm_smul, c.morseNorm_y₀, abs_of_pos (inv_pos.2 c.sqrt_two_ε_pos),
    inv_mul_cancel₀ c.sqrt_two_ε_pos.ne']

theorem y₀_eq : c.y₀ = Real.sqrt (2 * c.ε) • c.e₁ := by
  rw [e₁, smul_smul, mul_inv_cancel₀ c.sqrt_two_ε_pos.ne', one_smul]

def σ : ℝ := if c.i = 0 then 1 else -1

theorem σ_eq : c.σ = 1 ∨ c.σ = -1 := by
  unfold σ; split_ifs <;> simp

theorem σ_sq : c.σ * c.σ = 1 := by rcases c.σ_eq with h | h <;> rw [h] <;> norm_num

theorem σ_ne_zero : c.σ ≠ 0 := by rcases c.σ_eq with h | h <;> rw [h] <;> norm_num

theorem abs_σ : |c.σ| = 1 := by rcases c.σ_eq with h | h <;> rw [h] <;> norm_num

def e₀' : Fin n → ℝ := e₀ c.d.hk c.hkq

theorem armPt_eq : c.d.armPt c.hkq c.ε c.i = (c.σ * Real.sqrt (2 * c.ε)) • c.e₀' := by
  unfold MorseNormalChart.armPt e₀' e₀ σ
  rw [← ModelField.recombineL_apply, ← ModelField.recombineL_apply, ← map_smul]
  congr 1
  split_ifs <;> simp

theorem uq_e₀' : uq c.d.hk c.hkq c.e₀' = 1 := uq_e₀ _ _

theorem posPart_e₀' : posPart c.d.hk c.e₀' = 0 := posPart_e₀ _ _

theorem morseNorm_e₀' : morseNorm n c.e₀' = 1 := by
  rw [morseNorm_eq_abs_uq c.d.hk c.hkq c.posPart_e₀', c.uq_e₀', abs_one]

theorem z₀_eq : c.z₀ = c.d.χ ((c.σ * Real.sqrt (2 * c.ε)) • c.e₀') := by
  unfold z₀; rw [c.armPt_eq]

def pBall' : Set M := c.e.χ '' {y | morseNorm n y ^ 2 < 3 * c.ε}

def qBall' : Set M := c.d.χ '' {y | morseNorm n y ^ 2 < 3 * c.ε}

theorem three_ε_lt_rmp_sq : 3 * c.ε < c.D.rm p c.hp ^ 2 := by linarith [c.hrmp, c.hε]
theorem three_ε_lt_rmq_sq : 3 * c.ε < c.D.rm q c.hq ^ 2 := by linarith [c.hrmq, c.hε]

theorem morseNorm_lt_rmp_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    morseNorm n y < c.D.rm p c.hp :=
  (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg y) c.rmp_pos.le two_ne_zero).1
    (hy.trans c.three_ε_lt_rmp_sq)

theorem morseNorm_lt_rmq_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    morseNorm n y < c.D.rm q c.hq :=
  (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg y) c.rmq_pos.le two_ne_zero).1
    (hy.trans c.three_ε_lt_rmq_sq)

theorem pBall'_subset_pBall : c.pBall' ⊆ c.pBall :=
  image_mono fun _ hy => c.morseNorm_lt_rmp_of_sq_lt hy

theorem qBall'_subset_qBall : c.qBall' ⊆ c.qBall :=
  image_mono fun _ hy => c.morseNorm_lt_rmq_of_sq_lt hy

theorem pBall'_subset_image_ball : c.pBall' ⊆ c.e.χ '' Metric.ball 0 c.e.R' :=
  c.pBall'_subset_pBall.trans c.pBall_subset_image_ball

theorem qBall'_subset_image_ball : c.qBall' ⊆ c.d.χ '' Metric.ball 0 c.d.R' :=
  c.qBall'_subset_qBall.trans c.qBall_subset_image_ball

theorem disjoint_pBall'_qBall' : Disjoint c.pBall' c.qBall' :=
  (c.D.disjoint p c.hp q c.hq c.p_ne_q).mono c.pBall'_subset_image_ball c.qBall'_subset_image_ball

theorem pBall'_eq : c.pBall' = c.e.χ '' {y | morseNorm n y < Real.sqrt (3 * c.ε)} := by
  unfold pBall'
  congr 1
  ext y
  simp only [mem_ofPred_eq]
  rw [Real.lt_sqrt (ModelField.morseNorm_nonneg y)]

theorem qBall'_eq : c.qBall' = c.d.χ '' {y | morseNorm n y < Real.sqrt (3 * c.ε)} := by
  unfold qBall'
  congr 1
  ext y
  simp only [mem_ofPred_eq]
  rw [Real.lt_sqrt (ModelField.morseNorm_nonneg y)]

theorem sqrt_three_ε_lt_rmp : Real.sqrt (3 * c.ε) < c.D.rm p c.hp := by
  rw [Real.sqrt_lt' c.rmp_pos]; exact c.three_ε_lt_rmp_sq

theorem sqrt_three_ε_lt_rmq : Real.sqrt (3 * c.ε) < c.D.rm q c.hq := by
  rw [Real.sqrt_lt' c.rmq_pos]; exact c.three_ε_lt_rmq_sq

theorem isOpen_pBall' : IsOpen c.pBall' := by
  rw [c.pBall'_eq]
  exact c.e.isOpen_image_of_lt (by linarith [c.sqrt_three_ε_lt_rmp, c.D.rm_lt_R' p c.hp])

theorem isOpen_qBall' : IsOpen c.qBall' := by
  rw [c.qBall'_eq]
  exact c.d.isOpen_image_of_lt (by linarith [c.sqrt_three_ε_lt_rmq, c.D.rm_lt_R' q c.hq])

theorem chart_p_symm_eq' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    c.e.χ.symm (c.e.χ y) = y :=
  c.chart_p_symm_eq (c.morseNorm_lt_rmp_of_sq_lt hy)

theorem chart_q_symm_eq' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    c.d.χ.symm (c.d.χ y) = y :=
  c.d.χ.left_inv (c.d.hsrc y ((c.morseNorm_lt_rmq_of_sq_lt hy).le.trans (c.D.hrm q c.hq).2))

theorem f_chart_q {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.d.R) :
    f (c.d.χ y) = f q + (‖posPart c.d.hk y‖ ^ 2 - uq c.d.hk c.hkq y ^ 2) / 2 := by
  rw [c.d.hnorm y hy, morseNormalForm_split, norm_negPart_sq c.d.hk c.hkq]; ring

def orientedChartTube : Set M := c.openChartTube ∩ {x | 0 < c.σ * uq c.d.hk c.hkq (c.w x)}

theorem orientedChartTube_subset : c.orientedChartTube ⊆ c.openChartTube := inter_subset_left

theorem isOpen_orientedChartTube : IsOpen c.orientedChartTube := by
  have hc : ContinuousOn (fun x => c.σ * uq c.d.hk c.hkq (c.w x)) c.openChartTube :=
    continuousOn_const.mul
      ((continuous_uq c.d.hk c.hkq).comp_continuousOn c.contMDiffOn_w.continuousOn)
  exact hc.isOpen_inter_preimage c.isOpen_openChartTube isOpen_Ioi

theorem f_lt_f_q_of_mem_tube {x : M} (hx : f x ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)) :
    f x < f q := by
  have := c.c₂_add_η_lt_f_q_sub; have := hx.2; nlinarith [sq_nonneg c.d.r₀]

theorem uq_ne_zero_of_f_lt {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.d.R)
    (hf : f (c.d.χ y) < f q) : uq c.d.hk c.hkq y ≠ 0 := by
  intro h
  rw [c.f_chart_q hy, h] at hf
  nlinarith [sq_nonneg ‖posPart c.d.hk y‖]

theorem morseNorm_le_R_of_mem_qBall {x : M} (hx : x ∈ c.qBall) :
    morseNorm n (c.d.χ.symm x) ≤ c.d.R := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : morseNorm n y < c.D.rm q c.hq := hy
  rw [c.d.χ.left_inv (c.d.hsrc y (hy'.le.trans (c.D.hrm q c.hq).2))]
  exact hy'.le.trans (c.D.hrm q c.hq).2

theorem uq_sign_const {x : M} {T : ℝ} (hstay : ∀ s ∈ uIcc 0 T, c.D.flow s x ∈ c.qBall)
    (hne : ∀ s ∈ uIcc 0 T, uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s x)) ≠ 0) :
    0 < uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow T x)) * uq c.d.hk c.hkq (c.d.χ.symm x) := by
  have hγ := hasDerivAt_symm_flow_Icc (D := c.D) c.hq (x := x) (t₀ := min 0 T) (t₁ := max 0 T)
    hstay
  set h : ℝ → ℝ := fun s => uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s x)) with hh
  have hcont : ContinuousOn h (uIcc 0 T) :=
    (continuous_uq c.d.hk c.hkq).comp_continuousOn (HasDerivAt.continuousOn hγ)
  have h0 : h 0 = uq c.d.hk c.hkq (c.d.χ.symm x) := by simp only [hh]; rw [c.D.flow_zero]
  rw [← h0]
  change 0 < h T * h 0
  rcases lt_trichotomy (h T * h 0) 0 with hlt | heq | hgt
  · exfalso
    have hmem : (0 : ℝ) ∈ uIcc (h 0) (h T) := by
      rcases mul_neg_iff.1 hlt with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨by rw [min_le_iff]; left; exact hb.le, by rw [le_max_iff]; right; exact ha.le⟩
      · exact ⟨by rw [min_le_iff]; right; exact ha.le, by rw [le_max_iff]; left; exact hb.le⟩
    obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcont hmem
    exact hne s hs hs0
  · exfalso
    rcases mul_eq_zero.1 heq with h' | h'
    · exact hne T right_mem_uIcc h'
    · exact hne 0 left_mem_uIcc h'
  · exact hgt

theorem flow_mem_qBall_of_nonneg {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : morseNorm n y ^ 2 + 2 * t < c.D.rm q c.hq ^ 2) :
    ∀ s ∈ Icc 0 t, c.D.flow s (c.d.χ y) ∈
      c.d.χ '' {z | morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 + 2 * t} := by
  set x := c.d.χ y with hx
  set B := morseNorm n y ^ 2 + 2 * t with hB
  set S : Set (Fin n → ℝ) := {z | morseNorm n z ^ 2 ≤ B} with hS
  have hrm := c.rmq_pos
  have hR := (c.D.hrm q c.hq).2
  have hSsub : S ⊆ {z | morseNorm n z < c.D.rm q c.hq} := fun z hz =>
    (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg z) hrm.le two_ne_zero).1
      (lt_of_le_of_lt hz ht)
  have hSK : IsCompact (c.d.χ '' S) :=
    c.d.isCompact_image_of_subset ((isCompact_morseNorm_le (Real.sqrt B)).of_isClosed_subset
      (isClosed_le (continuous_morseNorm.pow 2) continuous_const) fun z hz =>
        Real.le_sqrt_of_sq_le hz) (c.D.rm_lt_R' q c.hq)
      fun z hz => show morseNorm n z ≤ _ from le_of_lt (hSsub hz)
  have hQc : IsClosed {s : ℝ | c.D.flow s x ∈ c.d.χ '' S} :=
    hSK.isClosed.preimage (c.D.continuous_flow_curve x)
  have hyR : morseNorm n y ≤ c.d.R := hy.le.trans hR
  have hfx : f x = f q + (1 / 2) * (‖posPart c.d.hk y‖ ^ 2 - ‖negPart c.d.hk y‖ ^ 2) := by
    rw [hx, c.d.hnorm y hyR, morseNormalForm_split]
  refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
  · change c.D.flow 0 x ∈ c.d.χ '' S
    rw [flow_zero]
    exact ⟨y, by change morseNorm n y ^ 2 ≤ B; linarith, rfl⟩
  · intro s hs hIcc
    have hsO : c.D.flow s x ∈ c.qBall := image_mono hSsub (hIcc (right_mem_Icc.2 hs.1))
    obtain ⟨δ, hδ, hδO⟩ := c.D.exists_Icc_flow_mem_open c.isOpen_qBall hsO
    refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + δ) t,
      by simp only [mem_Ioi, lt_min_iff]; exact ⟨by linarith, hs.2⟩, fun s' hs' => ?_⟩
    have hs'δ : s' ≤ s + δ := hs'.2.trans (min_le_left _ _)
    have hs't : s' ≤ t := hs'.2.trans (min_le_right _ _)
    change c.D.flow s' x ∈ c.d.χ '' S
    have hODE : ∀ u ∈ Icc 0 s', c.D.flow u x ∈ c.qBall := by
      intro u hu
      rcases le_or_gt u s with hus | hus
      · exact image_mono hSsub (hIcc ⟨hu.1, hus⟩)
      · exact hδO u ⟨by linarith [hus], hu.2.trans hs'δ⟩
    have hγ := hasDerivAt_symm_flow_Icc (D := c.D) c.hq hODE
    have hss' : 0 ≤ s' := hs.1.trans hs'.1.le
    have hγ0 : c.d.χ.symm (c.D.flow 0 x) = y := by
      rw [flow_zero, hx, c.d.χ.left_inv (c.d.hsrc y hyR)]
    have hanti : ‖posPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (c.D.flow 0 x))‖ ^ 2 :=
      ModelField.normSq_posPart_antitoneOn c.d.hk c.d.hr₀ hγ (left_mem_Icc.2 hss')
        (right_mem_Icc.2 hss') hss'
    rw [hγ0] at hanti
    have hmem' : c.D.flow s' x ∈ c.d.χ '' Metric.ball 0 c.d.R' :=
      c.qBall_subset_image_ball (hODE s' (right_mem_Icc.2 hss'))
    have hlev : f (c.D.flow s' x) = f q + (1 / 2) *
        (‖posPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2 -
          ‖negPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2) := by
      rw [← morseNormalForm_split, ← c.d.hnorm _ (c.morseNorm_le_R_of_mem_qBall
        (hODE s' (right_mem_Icc.2 hss'))), c.d.symm_image_eq hmem']
    have hf1 := sub_le_f_flow c.hfs (D := c.D) x hss'
    refine c.d.mem_image_of_symm_mem hmem' ?_
    change morseNorm n (c.d.χ.symm (c.D.flow s' x)) ^ 2 ≤ B
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk]
    have h2 := morseNorm_sq_eq_negPart_add_posPart c.d.hk y
    nlinarith

theorem flow_mem_qBall_of_nonpos {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq) {t : ℝ}
    (ht0 : t ≤ 0) (ht : morseNorm n y ^ 2 - 2 * t < c.D.rm q c.hq ^ 2) :
    ∀ s ∈ Icc t 0, c.D.flow s (c.d.χ y) ∈
      c.d.χ '' {z | morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 - 2 * t} := by
  set x := c.d.χ y with hx
  set B := morseNorm n y ^ 2 - 2 * t with hB
  set S : Set (Fin n → ℝ) := {z | morseNorm n z ^ 2 ≤ B} with hS
  have hrm := c.rmq_pos
  have hR := (c.D.hrm q c.hq).2
  have hSsub : S ⊆ {z | morseNorm n z < c.D.rm q c.hq} := fun z hz =>
    (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg z) hrm.le two_ne_zero).1
      (lt_of_le_of_lt hz ht)
  have hSK : IsCompact (c.d.χ '' S) :=
    c.d.isCompact_image_of_subset ((isCompact_morseNorm_le (Real.sqrt B)).of_isClosed_subset
      (isClosed_le (continuous_morseNorm.pow 2) continuous_const) fun z hz =>
        Real.le_sqrt_of_sq_le hz) (c.D.rm_lt_R' q c.hq)
      fun z hz => show morseNorm n z ≤ _ from le_of_lt (hSsub hz)
  have hQc : IsClosed {s : ℝ | c.D.flow s x ∈ c.d.χ '' S} :=
    hSK.isClosed.preimage (c.D.continuous_flow_curve x)
  have hyR : morseNorm n y ≤ c.d.R := hy.le.trans hR
  have hfx : f x = f q + (1 / 2) * (‖posPart c.d.hk y‖ ^ 2 - ‖negPart c.d.hk y‖ ^ 2) := by
    rw [hx, c.d.hnorm y hyR, morseNormalForm_split]
  have hmain := Icc_neg_subset_of_isClosed_of_step hQc (T := -t) ?_ ?_
  · rwa [neg_neg] at hmain
  · change c.D.flow 0 x ∈ c.d.χ '' S
    rw [flow_zero]
    exact ⟨y, by change morseNorm n y ^ 2 ≤ B; linarith, rfl⟩
  · intro s hs hIcc
    have hsO : c.D.flow s x ∈ c.qBall := image_mono hSsub (hIcc (left_mem_Icc.2 hs.2))
    obtain ⟨δ, hδ, hδO⟩ := c.D.exists_Icc_flow_mem_open c.isOpen_qBall hsO
    have hts : t < s := by have := hs.1; rwa [neg_neg] at this
    refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨max (s - δ) t,
      by simp only [mem_Iio, max_lt_iff]; exact ⟨by linarith, hts⟩, fun s' hs' => ?_⟩
    have hs'δ : s - δ ≤ s' := (le_max_left _ _).trans hs'.1
    have hs't : t ≤ s' := (le_max_right _ _).trans hs'.1
    change c.D.flow s' x ∈ c.d.χ '' S
    have hODE : ∀ u ∈ Icc s' 0, c.D.flow u x ∈ c.qBall := by
      intro u hu
      rcases le_or_gt s u with hus | hus
      · exact image_mono hSsub (hIcc ⟨hus, hu.2⟩)
      · exact hδO u ⟨hs'δ.trans hu.1, by linarith [hus]⟩
    have hγ := hasDerivAt_symm_flow_Icc (D := c.D) c.hq hODE
    have hss' : s' ≤ 0 := hs'.2.le.trans hs.2
    have hγ0 : c.d.χ.symm (c.D.flow 0 x) = y := by
      rw [flow_zero, hx, c.d.χ.left_inv (c.d.hsrc y hyR)]
    have hmono : ‖negPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2 ≤
        ‖negPart c.d.hk (c.d.χ.symm (c.D.flow 0 x))‖ ^ 2 :=
      ModelField.normSq_negPart_monotoneOn c.d.hk c.d.hr₀ hγ (left_mem_Icc.2 hss')
        (right_mem_Icc.2 hss') hss'
    rw [hγ0] at hmono
    have hmem' : c.D.flow s' x ∈ c.d.χ '' Metric.ball 0 c.d.R' :=
      c.qBall_subset_image_ball (hODE s' (left_mem_Icc.2 hss'))
    have hlev : f (c.D.flow s' x) = f q + (1 / 2) *
        (‖posPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2 -
          ‖negPart c.d.hk (c.d.χ.symm (c.D.flow s' x))‖ ^ 2) := by
      rw [← morseNormalForm_split, ← c.d.hnorm _ (c.morseNorm_le_R_of_mem_qBall
        (hODE s' (left_mem_Icc.2 hss'))), c.d.symm_image_eq hmem']
    have hf1 := f_flow_le_sub_of_nonpos c.hfs (D := c.D) x hss'
    refine c.d.mem_image_of_symm_mem hmem' ?_
    change morseNorm n (c.d.χ.symm (c.D.flow s' x)) ^ 2 ≤ B
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk]
    have h2 := morseNorm_sq_eq_negPart_add_posPart c.d.hk y
    nlinarith

theorem flow_mem_qBall_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq) {t : ℝ}
    (ht : morseNorm n y ^ 2 + 2 * |t| < c.D.rm q c.hq ^ 2) :
    ∀ s ∈ uIcc 0 t, c.D.flow s (c.d.χ y) ∈ c.qBall := by
  intro s hs
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [uIcc_of_le ht0] at hs
    exact image_mono (fun z hz => (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg z)
      c.rmq_pos.le two_ne_zero).1 (lt_of_le_of_lt hz ht))
      (c.flow_mem_qBall_of_nonneg hy ht0 ht s hs)
  · rw [abs_of_neg ht0] at ht
    rw [uIcc_of_ge ht0.le] at hs
    have ht' : morseNorm n y ^ 2 - 2 * t < c.D.rm q c.hq ^ 2 := by linarith
    exact image_mono (fun z hz => (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg z)
      c.rmq_pos.le two_ne_zero).1 (lt_of_le_of_lt hz ht'))
      (c.flow_mem_qBall_of_nonpos hy ht0.le ht' s hs)

theorem hstay_of_f_mem {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : f (c.d.χ y) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall := by
  apply c.flow_mem_qBall_of_sq_lt (c.morseNorm_lt_rmq_of_sq_lt hy)
  have hf := c.f_chart_q ((c.morseNorm_lt_rmq_of_sq_lt hy).le.trans (c.D.hrm q c.hq).2)
  have h1 := hx.1
  have h2 := hx.2
  have hη := c.η_lt_ε
  have hε₂ := c.ε₂_pos
  have hsq := morseNorm_sq_eq_uq c.d.hk c.hkq y
  have hrm := c.hrmq
  have hv := sq_nonneg ‖posPart c.d.hk y‖
  have hu := sq_nonneg (uq c.d.hk c.hkq y)
  have hb : |f (c.d.χ y) - c.c₂| < 3 * c.ε / 2 := by
    rw [abs_lt]
    constructor
    · unfold c₂; nlinarith
    · linarith
  nlinarith

theorem hstay_of_mem_qBall' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : c.d.χ y ∈ c.openChartTube) :
    ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall :=
  c.hstay_of_f_mem hy hx.1

theorem uq_mul_uq_w_pos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : f (c.d.χ y) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    0 < uq c.d.hk c.hkq (c.w (c.d.χ y)) * uq c.d.hk c.hkq y := by
  have hstay := c.hstay_of_f_mem hy hx
  have hne : ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂),
      uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s (c.d.χ y))) ≠ 0 := by
    intro s hs
    apply c.uq_ne_zero_of_f_lt (c.morseNorm_le_R_of_mem_qBall (hstay s hs))
    rw [c.d.symm_image_eq (c.qBall_subset_image_ball (hstay s hs))]
    apply c.f_lt_f_q_of_mem_tube
    have hmem := f_flow_mem_uIcc c.hfs (D := c.D) (c.d.χ y) s
    rw [mem_uIcc] at hmem hs
    have hc := c.c₂_mem_tube
    rcases hmem with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hs with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
  have h := c.uq_sign_const hstay hne
  rw [c.chart_q_symm_eq' hy] at h
  exact h

theorem π_z₀ : c.D.π c.c₂ c.z₀ = c.D.flow (c.ε₂ - c.ε) c.z₀ := by
  unfold GradientLikeStrip.π
  rw [c.f_z₀]
  congr 1
  unfold c₂; ring

theorem flow_π_eq {x : M} : c.D.flow (c.c₂ - f x) (c.D.π c.c₂ x) = x := by
  unfold GradientLikeStrip.π
  rw [flow_flow, show f x - c.c₂ + (c.c₂ - f x) = 0 by ring, flow_zero]

theorem eq_uq_smul_e₀' {y : Fin n → ℝ} (hv : posPart c.d.hk y = 0) :
    y = uq c.d.hk c.hkq y • c.e₀' := by
  have hk1 : c.d.k = 1 := c.hkq
  set i₀ : Fin c.d.k := ⟨0, by omega⟩ with hi₀
  have hi : ∀ i : Fin c.d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
  have hneg : negPart c.d.hk y = uq c.d.hk c.hkq y • EuclideanSpace.single i₀ 1 := by
    ext j
    rw [hi j]
    simp [uq, hi₀]
  conv_lhs => rw [← recombine_decompose c.d.hk y, hv, hneg]
  unfold e₀' e₀
  rw [← ModelField.recombineL_apply, ← ModelField.recombineL_apply, ← map_smul]
  congr 1
  ext <;> simp [hi₀]

theorem z₀_mem_openChartTube : c.z₀ ∈ c.openChartTube := by
  have := c.flow_z₀_mem_openChartTube (s := 0) ⟨le_rfl, c.transitTime_pos.le⟩
  rwa [flow_zero] at this

theorem uq_w_z₀_sq : uq c.d.hk c.hkq (c.w c.z₀) ^ 2 = 2 * c.ε₂ := by
  have h := c.normSq_negPart_w c.z₀_mem_openChartTube
  have hζ : c.ζ c.z₀ = 0 := by
    have := c.ζ_flow_z₀ (s := 0) ⟨le_rfl, c.transitTime_pos.le⟩
    rwa [flow_zero] at this
  rw [c.ζ_def] at hζ
  rw [hζ, norm_zero, norm_negPart_sq c.d.hk c.hkq] at h
  linarith

theorem σ_uq_w_z₀_pos : 0 < c.σ * uq c.d.hk c.hkq (c.w c.z₀) := by
  have harm := c.morseNorm_armPt_lt c.i
  have hv := (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i).1
  have hT : c.ε₂ - c.ε ≤ 0 := by linarith [c.ε₂_lt_ε]
  have hstay : ∀ s ∈ uIcc 0 (c.ε₂ - c.ε), c.D.flow s c.z₀ ∈ c.qBall := by
    intro s hs
    rw [uIcc_of_ge hT] at hs
    exact image_mono (fun z hz => hz.1.trans_lt harm)
      (flow_mem_of_posPart_eq_zero (D := c.D) c.hq harm hv hs.2)
  have hne : ∀ s ∈ uIcc 0 (c.ε₂ - c.ε),
      uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s c.z₀)) ≠ 0 := by
    intro s hs
    rw [uIcc_of_ge hT] at hs
    have hmem : c.D.flow s c.z₀ ∈ c.d.χ ''
        {z | morseNorm n z ≤ morseNorm n (c.d.armPt c.hkq c.ε c.i) ∧ posPart c.d.hk z = 0} :=
      flow_mem_of_posPart_eq_zero (D := c.D) c.hq harm hv hs.2
    obtain ⟨z, hz, hzx⟩ := hmem
    have hzR : morseNorm n z ≤ c.d.R := hz.1.trans (harm.le.trans (c.D.hrm q c.hq).2)
    have hz' : c.d.χ.symm (c.D.flow s c.z₀) = z := by
      rw [← hzx, c.d.χ.left_inv (c.d.hsrc z hzR)]
    rw [hz']
    apply c.uq_ne_zero_of_f_lt hzR
    have hfle : f (c.D.flow s c.z₀) ≤ f q :=
      f_flow_le_f_p_of_posPart_eq_zero (D := c.D) c.hq harm hv hs.2
    rw [hzx]
    refine lt_of_le_of_ne hfle ?_
    intro hfeq
    have hu : uq c.d.hk c.hkq z = 0 := by
      rw [← hzx, c.f_chart_q hzR, hz.2] at hfeq
      simp only [norm_zero] at hfeq
      nlinarith [sq_nonneg (uq c.d.hk c.hkq z)]
    have hz0 : z = 0 := eq_zero_of_uq_eq_zero c.d.hk c.hkq hu hz.2
    have hq' : c.D.flow s c.z₀ = q := by rw [← hzx, hz0, c.d.hχ0]
    have := congrArg (c.D.flow (-s)) hq'
    rw [flow_neg_flow, c.D.flow_crit c.hq] at this
    have hf := c.f_z₀
    rw [this] at hf
    linarith [c.hε]
  have h := c.uq_sign_const hstay hne
  rw [← c.π_z₀] at h
  have hz₀ : c.d.χ.symm c.z₀ = c.d.armPt c.hkq c.ε c.i := by
    unfold z₀
    exact c.d.χ.left_inv (c.d.hsrc _ (harm.le.trans (c.D.hrm q c.hq).2))
  rw [hz₀, c.armPt_eq, uq_smul, c.uq_e₀', mul_one] at h
  have hσ := c.σ_sq
  have hs := c.sqrt_two_ε_pos
  change 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (c.D.π c.c₂ c.z₀))
  nlinarith [mul_pos hs hs]

theorem w_z₀ : c.w c.z₀ = (c.σ * Real.sqrt (2 * c.ε₂)) • c.e₀' := by
  have hζ : c.ζ c.z₀ = 0 := by
    have := c.ζ_flow_z₀ (s := 0) ⟨le_rfl, c.transitTime_pos.le⟩
    rwa [flow_zero] at this
  rw [c.ζ_def] at hζ
  rw [c.eq_uq_smul_e₀' hζ]
  congr 1
  have h1 := c.uq_w_z₀_sq
  have h2 := c.σ_uq_w_z₀_pos
  have h3 : Real.sqrt (2 * c.ε₂) ^ 2 = 2 * c.ε₂ := Real.sq_sqrt (by linarith [c.ε₂_pos])
  have hσ := c.σ_sq
  have h4 : (uq c.d.hk c.hkq (c.w c.z₀) - c.σ * Real.sqrt (2 * c.ε₂)) *
      (uq c.d.hk c.hkq (c.w c.z₀) + c.σ * Real.sqrt (2 * c.ε₂)) = 0 := by
    have e : ∀ u s σ : ℝ, (u - σ * s) * (u + σ * s) = u ^ 2 - (σ * σ) * s ^ 2 :=
      fun _ _ _ => by ring
    rw [e, hσ, one_mul, h3, h1]; ring
  rcases mul_eq_zero.1 h4 with h | h
  · linarith
  · exfalso
    have : c.σ * uq c.d.hk c.hkq (c.w c.z₀) = -Real.sqrt (2 * c.ε₂) := by
      linear_combination c.σ * h - (Real.sqrt (2 * c.ε₂)) * hσ
    linarith [c.sqrt_two_ε_pos, Real.sqrt_pos.2 (by linarith [c.ε₂_pos] : 0 < 2 * c.ε₂)]

theorem flow_z₀_mem_orientedChartTube {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) :
    c.D.flow s c.z₀ ∈ c.orientedChartTube := by
  refine ⟨c.flow_z₀_mem_openChartTube hs, ?_⟩
  change 0 < c.σ * uq c.d.hk c.hkq (c.w (c.D.flow s c.z₀))
  unfold w
  rw [c.π_flow_z₀ hs, ← c.π_z₀]
  exact c.σ_uq_w_z₀_pos

theorem eq_flow_z₀_of_ζ_eq_zero {x : M} (hx : x ∈ c.orientedChartTube) (hζ : c.ζ x = 0) :
    x = c.D.flow (f q - c.ε - f x) c.z₀ := by
  have hw : c.w x = c.w c.z₀ := by
    rw [c.w_z₀]
    rw [c.ζ_def] at hζ
    rw [c.eq_uq_smul_e₀' hζ]
    congr 1
    have h := c.normSq_negPart_w hx.1
    rw [hζ, norm_zero, norm_negPart_sq c.d.hk c.hkq] at h
    have h2 : 0 < c.σ * uq c.d.hk c.hkq (c.w x) := hx.2
    have h3 : Real.sqrt (2 * c.ε₂) ^ 2 = 2 * c.ε₂ := Real.sq_sqrt (by linarith [c.ε₂_pos])
    have hσ := c.σ_sq
    have h4 : (uq c.d.hk c.hkq (c.w x) - c.σ * Real.sqrt (2 * c.ε₂)) *
        (uq c.d.hk c.hkq (c.w x) + c.σ * Real.sqrt (2 * c.ε₂)) = 0 := by
      have e : ∀ u s σ : ℝ, (u - σ * s) * (u + σ * s) = u ^ 2 - (σ * σ) * s ^ 2 :=
        fun _ _ _ => by ring
      rw [e, hσ, one_mul, h3, h]; ring
    rcases mul_eq_zero.1 h4 with h | h
    · linarith
    · exfalso
      have : c.σ * uq c.d.hk c.hkq (c.w x) = -Real.sqrt (2 * c.ε₂) := by
        linear_combination c.σ * h - (Real.sqrt (2 * c.ε₂)) * hσ
      linarith [Real.sqrt_pos.2 (by linarith [c.ε₂_pos] : 0 < 2 * c.ε₂)]
  have hπ : c.D.π c.c₂ x = c.D.π c.c₂ c.z₀ := by
    rw [← c.chart_w hx.1, ← c.chart_w c.z₀_mem_openChartTube, hw]
  calc x = c.D.flow (c.c₂ - f x) (c.D.π c.c₂ x) := c.flow_π_eq.symm
    _ = c.D.flow (c.c₂ - f x) (c.D.flow (c.ε₂ - c.ε) c.z₀) := by rw [hπ, c.π_z₀]
    _ = c.D.flow (f q - c.ε - f x) c.z₀ := by
        rw [flow_flow]; congr 1; unfold c₂; ring

theorem mem_orientedChartTube_of_eq_flow_z₀ {s : ℝ} (hx : c.D.flow s c.z₀ ∈ c.openChartTube) :
    c.D.flow s c.z₀ ∈ c.orientedChartTube ∧ c.ζ (c.D.flow s c.z₀) = 0 := by
  have hπ : c.D.π c.c₂ (c.D.flow s c.z₀) = c.D.π c.c₂ c.z₀ :=
    c.π_flow_eq (c.openChartTube_subset_regularFlowDomain c.z₀_mem_openChartTube) (c.openChartTube_subset_regularFlowDomain hx)
  have hw : c.w (c.D.flow s c.z₀) = c.w c.z₀ := by unfold w; rw [hπ]
  refine ⟨⟨hx, ?_⟩, ?_⟩
  · change 0 < c.σ * uq c.d.hk c.hkq (c.w (c.D.flow s c.z₀))
    rw [hw]; exact c.σ_uq_w_z₀_pos
  · rw [c.ζ_def, hw, c.w_z₀, ModelField.posPart_smul, c.posPart_e₀', smul_zero]

theorem flow_z₀_mem_pBall' {s : ℝ} (hs : c.transitTime ≤ s) : c.D.flow s c.z₀ ∈ c.pBall' := by
  obtain ⟨l, hl0, hl1, hl⟩ := c.flow_z₀_ray_general hs
  rw [hl]
  refine ⟨l • c.y₀, ?_, rfl⟩
  change morseNorm n (l • c.y₀) ^ 2 < 3 * c.ε
  rw [ModelField.morseNorm_smul, abs_of_pos hl0, mul_pow, c.morseNorm_y₀_sq]
  have := c.hε
  have hl2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0.le hl1
  nlinarith

theorem flow_z₀_mem_qBall' {s : ℝ} (hs : s ≤ 0) : c.D.flow s c.z₀ ∈ c.qBall' := by
  have harm := c.morseNorm_armPt_lt c.i
  have hv := (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i).1
  have hmem := flow_mem_of_posPart_eq_zero (D := c.D) c.hq harm hv hs
  refine image_mono (fun z hz => ?_) hmem
  change morseNorm n z ^ 2 < 3 * c.ε
  have h1 := c.d.morseNorm_sq_of_mem_leftModelSphere
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i)
  have h2 : morseNorm n z ^ 2 ≤ morseNorm n (c.d.armPt c.hkq c.ε c.i) ^ 2 :=
    pow_le_pow_left₀ (ModelField.morseNorm_nonneg z) hz.1 2
  linarith [c.hε]

theorem eq_norm_smul_e₁_of_eq_flow_z₀ {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    {s : ℝ} (hx : c.e.χ y = c.D.flow s c.z₀) : y = morseNorm n y • c.e₁ := by
  have hyR' : y ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' :=
    mem_ball_of_morseNorm_lt ((c.morseNorm_lt_rmp_of_sq_lt hy).trans (c.D.rm_lt_R' p c.hp))
  have hy₀R' : c.y₀ ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' :=
    mem_ball_of_morseNorm_lt (c.morseNorm_y₀_lt.trans (c.D.rm_lt_R' p c.hp))
  have hs2 := c.sqrt_two_ε_pos
  rcases le_or_gt c.transitTime s with hsT | hsT
  · obtain ⟨l, hl0, hl1, hl⟩ := c.flow_z₀_ray_general hsT
    rw [hl] at hx
    have hly : l • c.y₀ ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' := by
      apply mem_ball_of_morseNorm_lt
      rw [ModelField.morseNorm_smul, abs_of_pos hl0]
      have := c.morseNorm_y₀_lt; have := c.D.rm_lt_R' p c.hp
      have := ModelField.morseNorm_nonneg c.y₀
      nlinarith
    have hyl : y = l • c.y₀ := c.e.χ.injOn (c.e.hball hyR') (c.e.hball hly) hx
    rw [hyl, c.y₀_eq, smul_smul]
    congr 1
    rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos (by positivity)]
  · set t := c.transitTime - s with ht
    have ht0 : 0 ≤ t := by linarith
    obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp
      (c.morseNorm_lt_rmp_of_sq_lt hy) ht0
    have h1 : c.D.flow t (c.e.χ y) = c.e.χ c.y₀ := by
      rw [hx, flow_flow, c.chart_y₀]; congr 1; rw [ht]; ring
    rw [hl] at h1
    have hly : l • y ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' := by
      apply mem_ball_of_morseNorm_lt
      rw [ModelField.morseNorm_smul, abs_of_pos hl0]
      have := c.morseNorm_lt_rmp_of_sq_lt hy; have := c.D.rm_lt_R' p c.hp
      have := ModelField.morseNorm_nonneg y
      nlinarith
    have hyl : l • y = c.y₀ := c.e.χ.injOn (c.e.hball hly) (c.e.hball hy₀R') h1
    have hy' : y = l⁻¹ • c.y₀ := by
      rw [← hyl, smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
    rw [hy', c.y₀_eq, smul_smul]
    congr 1
    rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos (by positivity)]

theorem axis_of_ζ_eq_zero_p {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : c.e.χ y ∈ c.orientedChartTube) (hζ : c.ζ (c.e.χ y) = 0) :
    y = morseNorm n y • c.e₁ ∧ f (c.e.χ y) ≤ f q - c.ε := by
  have h := c.eq_flow_z₀_of_ζ_eq_zero hx hζ
  have hs : 0 < f q - c.ε - f (c.e.χ y) := by
    by_contra hle
    push Not at hle
    have hmem : c.e.χ y ∈ c.qBall' := by rw [h]; exact c.flow_z₀_mem_qBall' hle
    exact c.disjoint_pBall'_qBall'.notMem_of_mem_left ⟨y, hy, rfl⟩ hmem
  exact ⟨c.eq_norm_smul_e₁_of_eq_flow_z₀ hy h, by linarith⟩

theorem σ_uq_pos_of_mem_orientedChartTube {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : c.d.χ y ∈ c.orientedChartTube) : 0 < c.σ * uq c.d.hk c.hkq y := by
  have h := c.uq_mul_uq_w_pos hy hx.1.1
  have h3 : 0 < c.σ * uq c.d.hk c.hkq (c.w (c.d.χ y)) := hx.2
  set A := uq c.d.hk c.hkq (c.w (c.d.χ y)) with hA
  set B := uq c.d.hk c.hkq y with hB
  by_contra hle
  push Not at hle
  have e : (c.σ * A) * (A * B) = A ^ 2 * (c.σ * B) := by ring
  have := mul_pos h3 h
  rw [e] at this
  nlinarith [sq_nonneg A]

theorem mem_orientedChartTube_of_σ_uq_pos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hf : f (c.d.χ y) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η))
    (hu : 0 < c.σ * uq c.d.hk c.hkq y) : c.d.χ y ∈ c.orientedChartTube := by
  have hstay := c.hstay_of_f_mem hy hf
  have hT : c.d.χ y ∈ c.openChartTube := ⟨hf, hstay _ right_mem_uIcc⟩
  refine ⟨hT, ?_⟩
  change 0 < c.σ * uq c.d.hk c.hkq (c.w (c.d.χ y))
  have h := c.uq_mul_uq_w_pos hy hf
  set A := uq c.d.hk c.hkq (c.w (c.d.χ y)) with hA
  set B := uq c.d.hk c.hkq y with hB
  by_contra hle
  push Not at hle
  have e : (c.σ * B) * (A * B) = B ^ 2 * (c.σ * A) := by ring
  have := mul_pos hu h
  rw [e] at this
  nlinarith [sq_nonneg B]

theorem ray_eq_flow_z₀ {a : ℝ} (ha₀ : c.e.r₀ < a) (ha : a ^ 2 < 3 * c.ε) :
    c.e.χ (a • c.e₁) = c.D.flow (f q - c.ε - (f p + a ^ 2 / 2)) c.z₀ := by
  have hapos : 0 < a := c.e.hr₀.trans ha₀
  have hnorm : morseNorm n (a • c.e₁) = a := by
    rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos hapos]
  have hsq : morseNorm n (a • c.e₁) ^ 2 < 3 * c.ε := by rw [hnorm]; exact ha
  have hR : morseNorm n (a • c.e₁) ≤ c.e.R :=
    (c.morseNorm_lt_rmp_of_sq_lt hsq).le.trans (c.D.hrm p c.hp).2
  have hfx : f (c.e.χ (a • c.e₁)) = f p + a ^ 2 / 2 := by rw [c.f_chart_p hR, hnorm]
  have hs2 := c.sqrt_two_ε_pos
  have h2ε : Real.sqrt (2 * c.ε) ^ 2 = 2 * c.ε := Real.sq_sqrt (by linarith [c.hε])
  rcases le_or_gt a (Real.sqrt (2 * c.ε)) with hle | hgt
  · set s := c.transitTime + c.ε - a ^ 2 / 2 with hs
    have hs₁ : c.transitTime ≤ s := by
      rw [hs]; nlinarith [pow_le_pow_left₀ hapos.le hle 2]
    have hs₂ : s < c.transitTime + (c.ε - c.e.r₀ ^ 2 / 2) := by
      rw [hs]; nlinarith [pow_lt_pow_left₀ ha₀ c.e.hr₀.le two_ne_zero]
    have h := c.flow_z₀_ray hs₁ hs₂
    have hT : c.transitTime = f q - f p - 2 * c.ε := rfl
    have hs' : s = f q - c.ε - (f p + a ^ 2 / 2) := by rw [hs, hT]; ring
    rw [← hs', h, c.y₀_eq, smul_smul]
    congr 2
    have : 2 * c.ε - 2 * (s - c.transitTime) = a ^ 2 := by rw [hs]; ring
    rw [this, Real.sqrt_sq hapos.le]
    field_simp
  · set t := a ^ 2 / 2 - c.ε with ht
    have ht0 : 0 ≤ t := by rw [ht]; nlinarith [pow_le_pow_left₀ hs2.le hgt.le 2]
    set x := c.e.χ (a • c.e₁) with hx
    obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp
      (c.morseNorm_lt_rmp_of_sq_lt hsq) ht0
    have havoid : ∀ u ∈ uIcc 0 t, ∀ p' hp', c.D.flow u x ∉ c.D.smallBall p' hp' := by
      intro u hu p' hp' hmem
      rw [uIcc_of_le ht0] at hu
      have hmemp : c.D.flow u x ∈ c.e.χ '' {z | morseNorm n z ≤ morseNorm n (a • c.e₁)} :=
        modelBall_forward_invariant_of_index_zero c.hkp (c.morseNorm_lt_rmp_of_sq_lt hsq) hu.1
      obtain ⟨z, hz, hzx⟩ := hmemp
      have hzR : morseNorm n z ≤ c.e.R := hz.trans hR
      have h2 := abs_f_sub_lt_of_mem_smallBall (D := c.D) hp' hmem
      have hsub := c.D.smallBall_subset_image_ball p' hp' hmem
      rcases mem_pair_iff.1 hp' with h | h
      · obtain rfl := h.symm
        have hf1 := sub_le_f_flow c.hfs (D := c.D) x hu.1
        rw [← hzx, c.f_chart_p hzR] at hf1
        rw [hfx] at hf1
        rw [← hzx, c.f_chart_p hzR, abs_lt] at h2
        have h3 := c.hr₀p
        nlinarith [hu.2, h2.2, hf1]
      · obtain rfl := h.symm
        have hzb : z ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' := c.e.mem_ball_of_le hzR
        exact (c.D.disjoint p c.hp q hp' c.p_ne_q).notMem_of_mem_left
          (show c.D.flow u x ∈ c.e.χ '' Metric.ball 0 c.e.R' by
            rw [← hzx]; exact mem_image_of_mem _ hzb) hsub
    have hfa : f x - t ∈ Icc a' b' := by
      rw [hfx, ht]
      have h1 := c.f_p_mem; have h2 := c.f_q_mem; have := c.hlt; have := c.hε
      constructor <;> linarith [h1.1, h2.2]
    have hfx' : f x ∈ Icc a' b' := by
      rw [hfx]
      have h1 := c.f_p_mem; have h2 := c.f_q_mem; have := c.hlt; have := c.hε
      constructor <;> nlinarith [h1.1, h2.2, sq_nonneg a]
    have hft := f_flow_eq_sub_of_avoid_uIcc c.hfs (D := c.D) hfx' hfa havoid t right_mem_uIcc
    rw [hl, hfx, ht] at hft
    have hlaR : morseNorm n (l • (a • c.e₁)) ≤ c.e.R := by
      rw [ModelField.morseNorm_smul, abs_of_pos hl0]
      nlinarith [ModelField.morseNorm_nonneg (a • c.e₁)]
    rw [c.f_chart_p hlaR, ModelField.morseNorm_smul, abs_of_pos hl0, hnorm] at hft
    have hla : l * a = Real.sqrt (2 * c.ε) := by
      have h1 : (l * a) ^ 2 = 2 * c.ε := by nlinarith
      rw [← h1, Real.sqrt_sq (by positivity)]
    have hy₀ : l • (a • c.e₁) = c.y₀ := by rw [smul_smul, hla, c.y₀_eq]
    rw [hy₀, c.chart_y₀] at hl
    have hT : c.transitTime = f q - f p - 2 * c.ε := rfl
    have : f q - c.ε - (f p + a ^ 2 / 2) = c.transitTime - t := by rw [hT, ht]; ring
    rw [this]
    have := congrArg (c.D.flow (-t)) hl
    rw [flow_neg_flow, flow_flow] at this
    rw [hx, this, sub_eq_add_neg]

theorem flow_z₀_mem_openChartTube_of_eq {s : ℝ} (hs : f (c.D.flow s c.z₀) = f q - c.ε - s)
    (hf : f (c.D.flow s c.z₀) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    c.D.flow s c.z₀ ∈ c.openChartTube := by
  refine ⟨hf, ?_⟩
  change c.D.π c.c₂ (c.D.flow s c.z₀) ∈ c.qBall
  unfold GradientLikeStrip.π
  rw [flow_flow, hs, show s + (f q - c.ε - s - c.c₂) = c.ε₂ - c.ε by unfold c₂; ring]
  have hmem := flow_mem_of_posPart_eq_zero (D := c.D) c.hq (c.morseNorm_armPt_lt c.i)
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i).1 (t := c.ε₂ - c.ε)
    (by linarith [c.ε₂_lt_ε])
  exact image_mono (fun z hz => hz.1.trans_lt (c.morseNorm_armPt_lt c.i)) hmem

theorem axis_p_mem_orientedChartTube {a : ℝ} (ha₀ : c.e.r₀ < a) (ha : a ^ 2 < 3 * c.ε)
    (hf : f (c.e.χ (a • c.e₁)) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    c.e.χ (a • c.e₁) ∈ c.orientedChartTube ∧ c.ζ (c.e.χ (a • c.e₁)) = 0 := by
  have h := c.ray_eq_flow_z₀ ha₀ ha
  have hapos : 0 < a := c.e.hr₀.trans ha₀
  have hnorm : morseNorm n (a • c.e₁) = a := by
    rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos hapos]
  have hsq : morseNorm n (a • c.e₁) ^ 2 < 3 * c.ε := by rw [hnorm]; exact ha
  have hR : morseNorm n (a • c.e₁) ≤ c.e.R :=
    (c.morseNorm_lt_rmp_of_sq_lt hsq).le.trans (c.D.hrm p c.hp).2
  have hfx : f (c.e.χ (a • c.e₁)) = f p + a ^ 2 / 2 := by rw [c.f_chart_p hR, hnorm]
  rw [h] at hf ⊢
  exact c.mem_orientedChartTube_of_eq_flow_z₀
    (c.flow_z₀_mem_openChartTube_of_eq (by rw [← h, hfx]; ring) hf)

theorem f_le_of_axis_p {a : ℝ} (ha₀ : c.e.r₀ < a) (ha : a ^ 2 < 3 * c.ε) :
    f p + a ^ 2 / 2 ≤ f q - c.ε := by
  by_contra hlt
  push Not at hlt
  have h := c.ray_eq_flow_z₀ ha₀ ha
  have hapos : 0 < a := c.e.hr₀.trans ha₀
  have hnorm : morseNorm n (a • c.e₁) = a := by
    rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos hapos]
  have hmem : c.e.χ (a • c.e₁) ∈ c.qBall' := by
    rw [h]; exact c.flow_z₀_mem_qBall' (by linarith)
  exact c.disjoint_pBall'_qBall'.notMem_of_mem_left
    ⟨a • c.e₁, by change morseNorm n (a • c.e₁) ^ 2 < 3 * c.ε; rw [hnorm]; exact ha, rfl⟩
    hmem

def ψm (x : M) : ℝ := plateau c.lo₁ c.lo₂ c.hi₁ c.hi₂ (f x)

def ψm' (x : M) : ℝ := plateau (c.c₁ - c.η / 2) c.lo₁ c.hi₂ (c.c₂ + c.η / 2) (f x)

theorem ψm_nonneg (x : M) : 0 ≤ c.ψm x := plateau_nonneg _ _ _ _ _
theorem ψm_le_one (x : M) : c.ψm x ≤ 1 := plateau_le_one _ _ _ _ _
theorem ψm'_nonneg (x : M) : 0 ≤ c.ψm' x := plateau_nonneg _ _ _ _ _
theorem ψm'_le_one (x : M) : c.ψm' x ≤ 1 := plateau_le_one _ _ _ _ _

theorem c₁_sub_half_lt_lo₁ : c.c₁ - c.η / 2 < c.lo₁ := by unfold lo₁; linarith [c.η_pos]
theorem hi₂_lt_c₂_add_half : c.hi₂ < c.c₂ + c.η / 2 := by unfold hi₂; linarith [c.η_pos]

theorem f_mem_of_ψm_ne_zero {x : M} (h : c.ψm x ≠ 0) : c.lo₁ < f x ∧ f x < c.hi₂ :=
  plateau_lt_of_ne_zero c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ h

theorem f_mem_of_ψm'_ne_zero {x : M} (h : c.ψm' x ≠ 0) :
    c.c₁ - c.η / 2 < f x ∧ f x < c.c₂ + c.η / 2 :=
  plateau_lt_of_ne_zero c.c₁_sub_half_lt_lo₁ c.hi₂_lt_c₂_add_half h

theorem ψm'_eq_one_of_ψm_ne_zero {x : M} (h : c.ψm x ≠ 0) : c.ψm' x = 1 := by
  obtain ⟨h1, h2⟩ := c.f_mem_of_ψm_ne_zero h
  exact plateau_eq_one c.c₁_sub_half_lt_lo₁ c.hi₂_lt_c₂_add_half h1.le h2.le

theorem ψm_eq_one {x : M} (h1 : c.lo₂ ≤ f x) (h2 : f x ≤ c.hi₁) : c.ψm x = 1 :=
  plateau_eq_one c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ h1 h2

theorem ψm'_eq_one {x : M} (h1 : c.lo₁ ≤ f x) (h2 : f x ≤ c.hi₂) : c.ψm' x = 1 :=
  plateau_eq_one c.c₁_sub_half_lt_lo₁ c.hi₂_lt_c₂_add_half h1 h2

theorem ψm_eq_zero_of_le {x : M} (h : f x ≤ c.lo₁) : c.ψm x = 0 :=
  plateau_eq_zero_of_le c.lo₁_lt_lo₂ h

theorem ψm_eq_zero_of_ge {x : M} (h : c.hi₂ ≤ f x) : c.ψm x = 0 :=
  plateau_eq_zero_of_ge c.hi₁_lt_hi₂ h

theorem contMDiff_ψm : ContMDiff I 𝓘(ℝ, ℝ) ∞ c.ψm :=
  (contDiff_plateau _ _ _ _).comp_contMDiff c.hfs

theorem contMDiff_ψm' : ContMDiff I 𝓘(ℝ, ℝ) ∞ c.ψm' :=
  (contDiff_plateau _ _ _ _).comp_contMDiff c.hfs

theorem ρB_lt_R' : c.ρB < c.e.R' := by
  have h1 : c.ρB < Real.sqrt (2 * c.ε) := by
    rw [ρB]; exact Real.sqrt_lt_sqrt (by linarith [c.two_ε₁_sub_pos, c.η_pos])
      (by rw [← c.ρB_sq]; exact c.ρB_sq_lt)
  linarith [c.sqrt_two_ε_lt_rmp, c.D.rm_lt_R' p c.hp, c.rmp_pos]

theorem ρB_le_R : c.ρB ≤ c.e.R := by
  have h1 : c.ρB < Real.sqrt (2 * c.ε) := by
    rw [ρB]; exact Real.sqrt_lt_sqrt (by linarith [c.two_ε₁_sub_pos, c.η_pos])
      (by rw [← c.ρB_sq]; exact c.ρB_sq_lt)
  linarith [c.sqrt_two_ε_lt_rmp, (c.D.hrm p c.hp).2, c.rmp_pos]

def pTransverseField (y : Fin n → ℝ) : Fin n → ℝ :=
  mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (c.transverseField (c.e.χ y))

def qTransverseField (y : Fin n → ℝ) : Fin n → ℝ :=
  mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (c.transverseField (c.d.χ y))

theorem mem_ball_p_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    y ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' :=
  mem_ball_of_morseNorm_lt ((c.morseNorm_lt_rmp_of_sq_lt hy).trans (c.D.rm_lt_R' p c.hp))

theorem mem_ball_q_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    y ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' :=
  mem_ball_of_morseNorm_lt ((c.morseNorm_lt_rmq_of_sq_lt hy).trans (c.D.rm_lt_R' q c.hq))

theorem transverseField_eq_zero_of_pTransverseField_eq_zero {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (h : c.pTransverseField y = 0) : c.transverseField (c.e.χ y) = 0 := by
  have := MorseNormalChart.mfderiv_chart_symm_apply (c.mem_ball_p_of_sq_lt hy) (c.transverseField (c.e.χ y))
  unfold pTransverseField at h
  rw [h] at this
  exact this.symm.trans ((mfderiv 𝓘(ℝ, Fin n → ℝ) I c.e.χ y).map_zero)

theorem transverseField_eq_zero_of_qTransverseField_eq_zero {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (h : c.qTransverseField y = 0) : c.transverseField (c.d.χ y) = 0 := by
  have := MorseNormalChart.mfderiv_chart_symm_apply (c.mem_ball_q_of_sq_lt hy) (c.transverseField (c.d.χ y))
  unfold qTransverseField at h
  rw [h] at this
  exact this.symm.trans ((mfderiv 𝓘(ℝ, Fin n → ℝ) I c.d.χ y).map_zero)

def lam : ℝ := 1 / (c.ε₂ - c.η) + 1

theorem ε₂_sub_η_pos : 0 < c.ε₂ - c.η := by
  have := c.η_lt_right; nlinarith [sq_nonneg c.d.r₀]

theorem lam_pos : 0 < c.lam := by
  unfold lam; have := c.ε₂_sub_η_pos; positivity

theorem one_le_lam : 1 ≤ c.lam := by
  unfold lam; have := c.ε₂_sub_η_pos
  have : 0 ≤ 1 / (c.ε₂ - c.η) := by positivity
  linarith

theorem lam_mul : 4 < 2 * c.lam * (2 * (c.ε₂ - c.η)) := by
  unfold lam; have h := c.ε₂_sub_η_pos
  have : 1 / (c.ε₂ - c.η) * (c.ε₂ - c.η) = 1 := by field_simp
  nlinarith

structure CancelConsts where
  δ : ℝ
  δ' : ℝ
  τ : ℝ
  hδ : 0 < δ
  hδδ' : 2 * δ < δ'
  hδ'ε : δ' ^ 2 < c.ε
  hτ : 0 < τ
  hτ1 : τ ^ 2 ≤ 1 / 4
  hdB : ∀ y : Fin n → ℝ, morseNorm n y ^ 2 < 3 * c.ε → c.e.χ y ∈ c.orientedChartTube →
    0 < ‖c.ζ (c.e.χ y)‖ → ‖c.ζ (c.e.χ y)‖ < δ' →
    axialDefectDeriv c.e₁ y (c.pTransverseField y) < 0
  hcone : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
    perpSq c.e₁ y < (τ ^ 2 + 2 * δ ^ 2 / c.ρA ^ 2) * morseNorm n y ^ 2 →
    0 < axial c.e₁ y →
    c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < δ'

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem δ'_pos : 0 < k.δ' := by linarith [k.hδ, k.hδδ']

theorem δ_lt_δ' : k.δ < k.δ' := by linarith [k.hδ, k.hδδ']

theorem δ_sq_lt : 4 * k.δ ^ 2 < c.ε := by
  have := k.hδ; have := k.hδδ'; have := k.hδ'ε; nlinarith

def βm (x : M) : ℝ := cut (k.δ ^ 2) ((2 * k.δ) ^ 2) (‖c.ζ x‖ ^ 2)

def βm' (x : M) : ℝ := cut ((2 * k.δ) ^ 2) (k.δ' ^ 2) (‖c.ζ x‖ ^ 2)

def pPerturbationField : (Fin n → ℝ) → Fin n → ℝ := CancelModel.pPerturbationField c.m' k.δ k.τ c.ρA c.ρB c.e₁

def qPerturbationField : (Fin n → ℝ) → Fin n → ℝ := CancelModel.qPerturbationField c.d.hk c.hkq k.δ k.τ c.σ c.m' c.uA c.uB

def middlePerturbation (x : M) : TangentSpace I x :=
  (2 * (k.βm x * c.ψm x)) • (-c.D.V x) + (2 * (c.lam * (k.βm' x * c.ψm' x))) • c.transverseField x

def localizedMiddlePerturbation : (x : M) → TangentSpace I x :=
  fun x =>
    (Set.indicator (M := Fin n → ℝ) c.orientedChartTube (fun x => (k.middlePerturbation x : Fin n → ℝ)) x :
      Fin n → ℝ)

theorem localizedMiddlePerturbation_of_mem {x : M} (hx : x ∈ c.orientedChartTube) : k.localizedMiddlePerturbation x = k.middlePerturbation x :=
  Set.indicator_of_mem hx _

theorem localizedMiddlePerturbation_of_notMem {x : M} (hx : x ∉ c.orientedChartTube) : k.localizedMiddlePerturbation x = 0 :=
  Set.indicator_of_notMem hx _

def cancellationField : (x : M) → TangentSpace I x :=
  fun x => c.D.V x + c.e.push k.pPerturbationField x + c.d.push k.qPerturbationField x + k.localizedMiddlePerturbation x

theorem cancellationField_apply (x : M) : k.cancellationField x = c.D.V x + c.e.push k.pPerturbationField x + c.d.push k.qPerturbationField x + k.localizedMiddlePerturbation x := rfl

theorem βm_nonneg (x : M) : 0 ≤ k.βm x := cut_nonneg _ _ _
theorem βm_le_one (x : M) : k.βm x ≤ 1 := cut_le_one _ _ _
theorem βm'_nonneg (x : M) : 0 ≤ k.βm' x := cut_nonneg _ _ _
theorem βm'_le_one (x : M) : k.βm' x ≤ 1 := cut_le_one _ _ _

theorem δ_sq_lt_two_δ_sq : k.δ ^ 2 < (2 * k.δ) ^ 2 := by have := k.hδ; nlinarith
theorem two_δ_sq_lt_δ'_sq : (2 * k.δ) ^ 2 < k.δ' ^ 2 := by
  have := k.hδ; have := k.hδδ'; nlinarith

theorem βm_eq_one {x : M} (h : ‖c.ζ x‖ ≤ k.δ) : k.βm x = 1 :=
  cut_eq_one k.δ_sq_lt_two_δ_sq (pow_le_pow_left₀ (norm_nonneg _) h 2)

theorem βm_eq_one_of_ζ_eq_zero {x : M} (h : c.ζ x = 0) : k.βm x = 1 :=
  k.βm_eq_one (by rw [h, norm_zero]; exact k.hδ.le)

theorem norm_ζ_lt_of_βm_ne_zero {x : M} (h : k.βm x ≠ 0) : ‖c.ζ x‖ < 2 * k.δ := by
  have := lt_of_cut_ne_zero k.δ_sq_lt_two_δ_sq h
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by linarith [k.hδ]) two_ne_zero).1 this

theorem norm_ζ_lt_of_βm'_ne_zero {x : M} (h : k.βm' x ≠ 0) : ‖c.ζ x‖ < k.δ' := by
  have := lt_of_cut_ne_zero k.two_δ_sq_lt_δ'_sq h
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 this

theorem βm'_eq_one_of_βm_ne_zero {x : M} (h : k.βm x ≠ 0) : k.βm' x = 1 :=
  cut_eq_one k.two_δ_sq_lt_δ'_sq
    (pow_le_pow_left₀ (norm_nonneg _) (k.norm_ζ_lt_of_βm_ne_zero h).le 2)

theorem middlePerturbation_eq_zero_of {x : M} (hβ : k.βm' x * c.ψm' x = 0) : k.middlePerturbation x = 0 := by
  have hβm : k.βm x * c.ψm x = 0 := by
    by_contra h
    rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    rw [k.βm'_eq_one_of_βm_ne_zero h1, c.ψm'_eq_one_of_ψm_ne_zero h2, one_mul] at hβ
    exact one_ne_zero hβ
  unfold middlePerturbation
  rw [hβm, hβ]
  simp

def qTubeCoordinates : Set (Fin n → ℝ) :=
  {y | morseNorm n y ^ 2 ≤ 2 * k.δ' ^ 2 + 2 * c.ε₂ ∧ 0 ≤ c.σ * uq c.d.hk c.hkq y}

theorem qTubeCoordinates_radius_lt : 2 * k.δ' ^ 2 + 2 * c.ε₂ < c.D.rm q c.hq ^ 2 := by
  have := k.hδ'ε; have := c.ε₂_lt_ε; have := c.hrmq; have := c.hε; linarith

theorem isCompact_qTubeCoordinates : IsCompact k.qTubeCoordinates :=
  (isCompact_morseNorm_le (Real.sqrt (2 * k.δ' ^ 2 + 2 * c.ε₂))).of_isClosed_subset
    ((isClosed_le (continuous_morseNorm.pow 2) continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))))
    fun _ hy => Real.le_sqrt_of_sq_le hy.1

theorem morseNorm_lt_rm_of_mem_qTubeCoordinates {y : Fin n → ℝ} (hy : y ∈ k.qTubeCoordinates) :
    morseNorm n y < c.D.rm q c.hq :=
  (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg y) c.rmq_pos.le two_ne_zero).1
    (hy.1.trans_lt k.qTubeCoordinates_radius_lt)

theorem isCompact_image_qTubeCoordinates : IsCompact (c.d.χ '' k.qTubeCoordinates) :=
  c.d.isCompact_image_of_subset k.isCompact_qTubeCoordinates (c.D.rm_lt_R' q c.hq)
    fun _ hy => (k.morseNorm_lt_rm_of_mem_qTubeCoordinates hy).le

def closedFlowTube : Set M :=
  {x | f x ∈ Icc (c.c₁ - c.η / 2) (c.c₂ + c.η / 2)} ∩
    c.D.π c.c₂ ⁻¹' (c.d.χ '' k.qTubeCoordinates)

theorem isClosed_closedFlowTube : IsClosed k.closedFlowTube :=
  (isClosed_Icc.preimage c.hfs.continuous).inter
    (k.isCompact_image_qTubeCoordinates.isClosed.preimage (c.D.continuous_π c.hfs c.c₂))

theorem closedFlowTube_subset_strip : k.closedFlowTube ⊆ f ⁻¹' Icc a' b' := fun x hx => by
  have h := hx.1
  have := c.a'_lt_c₁_sub_η; have := c.c₂_add_η_lt_b'; have := c.η_pos
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem isCompact_closedFlowTube : IsCompact k.closedFlowTube :=
  c.hf.compact.of_isClosed_subset k.isClosed_closedFlowTube k.closedFlowTube_subset_strip

theorem closedFlowTube_subset_orientedChartTube : k.closedFlowTube ⊆ c.orientedChartTube := by
  rintro x ⟨hx1, hx2⟩
  have hf : f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
    have := c.η_pos; exact ⟨by linarith [hx1.1], by linarith [hx1.2]⟩
  obtain ⟨y, hy, hyx⟩ := hx2
  have hyrm := k.morseNorm_lt_rm_of_mem_qTubeCoordinates hy
  have hxT : x ∈ c.openChartTube := ⟨hf, ⟨y, hyrm, hyx⟩⟩
  refine ⟨hxT, ?_⟩
  change 0 < c.σ * uq c.d.hk c.hkq (c.w x)
  have hw : c.w x = y := by
    unfold w
    rw [← hyx, c.d.χ.left_inv (c.d.hsrc y (hyrm.le.trans (c.D.hrm q c.hq).2))]
  rw [hw]
  have hne : uq c.d.hk c.hkq y ≠ 0 := by
    apply c.uq_ne_zero_of_f_lt (hyrm.le.trans (c.D.hrm q c.hq).2)
    rw [hyx, c.f_π_eq hxT]
    unfold c₂; linarith [c.ε₂_pos]
  exact lt_of_le_of_ne hy.2 fun h => hne (by
    rcases mul_eq_zero.1 h.symm with h' | h'
    · exact absurd h' c.σ_ne_zero
    · exact h')

theorem localizedMiddlePerturbation_eq_zero_of_notMem_closedFlowTube {x : M} (hx : x ∉ k.closedFlowTube) : k.localizedMiddlePerturbation x = 0 := by
  by_cases hxT : x ∈ c.orientedChartTube
  · rw [k.localizedMiddlePerturbation_of_mem hxT]
    apply k.middlePerturbation_eq_zero_of
    by_contra h
    rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    apply hx
    obtain ⟨hf1, hf2⟩ := c.f_mem_of_ψm'_ne_zero h2
    have hζ := k.norm_ζ_lt_of_βm'_ne_zero h1
    refine ⟨⟨hf1.le, hf2.le⟩, ?_⟩
    change c.D.π c.c₂ x ∈ c.d.χ '' k.qTubeCoordinates
    refine ⟨c.w x, ⟨?_, ?_⟩, c.chart_w hxT.1⟩
    · have h := c.normSq_negPart_w hxT.1
      rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk, h, ← c.ζ_def]
      have := pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero
      linarith
    · exact hxT.2.le
  · exact k.localizedMiddlePerturbation_of_notMem hxT

theorem support_localizedMiddlePerturbation_subset : Function.support k.localizedMiddlePerturbation ⊆ k.closedFlowTube := fun x hx => by
  by_contra h
  exact hx (k.localizedMiddlePerturbation_eq_zero_of_notMem_closedFlowTube h)

theorem contMDiffAt_βm {x₀ : M} (hx₀ : x₀ ∈ c.openChartTube) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ k.βm x₀ := by
  have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) ∞ c.ζ x₀ :=
    c.contMDiffOn_ζ.contMDiffAt (c.isOpen_openChartTube.mem_nhds hx₀)
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => ‖c.ζ x‖ ^ 2) x₀ :=
    (contDiff_norm_sq ℝ).comp_contMDiffAt h1
  exact (contDiff_cut _ _).comp_contMDiffAt h2

theorem contMDiffAt_βm' {x₀ : M} (hx₀ : x₀ ∈ c.openChartTube) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ k.βm' x₀ := by
  have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) ∞ c.ζ x₀ :=
    c.contMDiffOn_ζ.contMDiffAt (c.isOpen_openChartTube.mem_nhds hx₀)
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => ‖c.ζ x‖ ^ 2) x₀ :=
    (contDiff_norm_sq ℝ).comp_contMDiffAt h1
  exact (contDiff_cut _ _).comp_contMDiffAt h2

theorem contMDiffAt_middlePerturbation {x₀ : M} (hx₀ : x₀ ∈ c.openChartTube) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, k.middlePerturbation x⟩ : TangentBundle I M)) x₀ := by
  have hV : ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, -c.D.V x⟩ : TangentBundle I M)) x₀ :=
    (c.D.smooth x₀).neg_section
  have hZ : ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, c.transverseField x⟩ : TangentBundle I M)) x₀ :=
    c.contMDiffOn_transverseField.contMDiffAt (c.isOpen_openChartTube.mem_nhds hx₀)
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => 2 * (k.βm x * c.ψm x)) x₀ :=
    contMDiffAt_const.mul ((k.contMDiffAt_βm hx₀).mul (c.contMDiff_ψm x₀))
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => 2 * (c.lam * (k.βm' x * c.ψm' x))) x₀ :=
    contMDiffAt_const.mul (contMDiffAt_const.mul
      ((k.contMDiffAt_βm' hx₀).mul (c.contMDiff_ψm' x₀)))
  exact (h1.smul_section hV).add_section (h2.smul_section hZ)

theorem contMDiff_localizedMiddlePerturbation :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, k.localizedMiddlePerturbation x⟩ : TangentBundle I M)) := by
  intro x₀
  by_cases hx₀ : x₀ ∈ c.orientedChartTube
  · refine (k.contMDiffAt_middlePerturbation hx₀.1).congr_of_eventuallyEq ?_
    filter_upwards [c.isOpen_orientedChartTube.mem_nhds hx₀] with x hx
    show (⟨x, k.localizedMiddlePerturbation x⟩ : TangentBundle I M) = ⟨x, k.middlePerturbation x⟩
    rw [k.localizedMiddlePerturbation_of_mem hx]
  · have hx₀' : x₀ ∉ k.closedFlowTube := fun h => hx₀ (k.closedFlowTube_subset_orientedChartTube h)
    refine ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) (IB := I)
      (n := ∞)).contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [k.isClosed_closedFlowTube.isOpen_compl.mem_nhds hx₀'] with x hx
    change (⟨x, k.localizedMiddlePerturbation x⟩ : TangentBundle I M) = ⟨x, 0⟩
    rw [k.localizedMiddlePerturbation_eq_zero_of_notMem_closedFlowTube hx]

theorem Kq_radius_lt : c.uB ^ 2 + k.τ ^ 2 * c.uB ^ 2 + 2 * k.δ ^ 2 < 3 * c.ε := by
  have h1 := c.uB_sq_lt; have h2 := k.hτ1; have h3 := k.δ_sq_lt; have h4 := c.hε
  have h5 : 0 ≤ c.uB ^ 2 := sq_nonneg _
  have h6 : k.τ ^ 2 * c.uB ^ 2 ≤ 1 / 4 * c.uB ^ 2 := by gcongr
  nlinarith

theorem pSupportRegion_subset_pBall' : c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB ⊆ c.pBall' :=
  image_mono fun y hy => by
  change morseNorm n y ^ 2 < 3 * c.ε
  have := hy.1
  have h2 := c.ρB_sq_lt; have := c.hε
  nlinarith [ModelField.morseNorm_nonneg y, c.ρB_pos]

theorem qSupportRegion_subset_qBall' : c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB ⊆ c.qBall' :=
  image_mono fun y hy => by
    change morseNorm n y ^ 2 < 3 * c.ε
    exact (morseNorm_sq_le_of_mem_qSupportRegion c.d.hk c.hkq hy).trans_lt k.Kq_radius_lt

theorem pSupportRegion_subset_ball : pSupportRegion k.δ k.τ c.e₁ c.ρB ⊆ Metric.ball 0 c.e.R' :=
  CancelModel.pSupportRegion_subset_ball c.ρB_lt_R'

theorem qSupportRegion_subset_ball : qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB ⊆ Metric.ball 0 c.d.R' := by
  refine CancelModel.qSupportRegion_subset_ball c.d.hk c.hkq c.d.R'_pos.le ?_
  have h1 := k.Kq_radius_lt
  have h2 := c.three_ε_lt_rmq_sq
  have h3 := c.D.rm_lt_R' q c.hq
  have h4 := c.rmq_pos
  nlinarith

theorem pPerturbationField_eq_zero_of_notMem {y : Fin n → ℝ} (hy : y ∉ pSupportRegion k.δ k.τ c.e₁ c.ρB) :
    k.pPerturbationField y = 0 :=
  CancelModel.pPerturbationField_eq_zero_of_notMem k.hδ c.ρA_pos.le c.ρA_lt_ρB hy

theorem qPerturbationField_eq_zero_of_notMem {y : Fin n → ℝ} (hy : y ∉ qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB) :
    k.qPerturbationField y = 0 :=
  CancelModel.qPerturbationField_eq_zero_of_notMem c.d.hk c.hkq k.hδ c.uA_pos.le c.uA_lt_uB hy

theorem contDiff_pPerturbationField : ContDiff ℝ ∞ k.pPerturbationField := CancelModel.contDiff_pPerturbationField _ _ _ _ _ _

theorem contDiff_qPerturbationField : ContDiff ℝ ∞ k.qPerturbationField := CancelModel.contDiff_qPerturbationField _ _ _ _ _ _ _ _

theorem contMDiff_push_pPerturbationField :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, c.e.push k.pPerturbationField x⟩ : TangentBundle I M)) :=
  c.e.contMDiff_push k.contDiff_pPerturbationField isCompact_pSupportRegion k.pSupportRegion_subset_ball fun _ hy =>
    k.pPerturbationField_eq_zero_of_notMem hy

theorem contMDiff_push_qPerturbationField :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, c.d.push k.qPerturbationField x⟩ : TangentBundle I M)) :=
  c.d.contMDiff_push k.contDiff_qPerturbationField (isCompact_qSupportRegion c.d.hk c.hkq) k.qSupportRegion_subset_ball fun _ hy =>
    k.qPerturbationField_eq_zero_of_notMem hy

theorem contMDiff_cancellationField :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, k.cancellationField x⟩ : TangentBundle I M)) :=
  ((c.D.smooth.add_section k.contMDiff_push_pPerturbationField).add_section k.contMDiff_push_qPerturbationField).add_section
    k.contMDiff_localizedMiddlePerturbation

def perturbationSupportRegion : Set M :=
  c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB ∪ c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB ∪ k.closedFlowTube

theorem isCompact_image_pSupportRegion : IsCompact (c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB) :=
  c.e.isCompact_image_of_subset isCompact_pSupportRegion c.ρB_lt_R' fun _ hy => hy.1

theorem isCompact_image_qSupportRegion : IsCompact (c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB) := by
  refine c.d.isCompact_image_of_subset (isCompact_qSupportRegion c.d.hk c.hkq)
    (r := Real.sqrt (3 * c.ε)) (by linarith [c.sqrt_three_ε_lt_rmq, c.D.rm_lt_R' q c.hq])
    fun y hy => ?_
  change morseNorm n y ≤ Real.sqrt (3 * c.ε)
  exact Real.le_sqrt_of_sq_le
    ((morseNorm_sq_le_of_mem_qSupportRegion c.d.hk c.hkq hy).trans k.Kq_radius_lt.le)

theorem isCompact_perturbationSupportRegion : IsCompact k.perturbationSupportRegion :=
  (k.isCompact_image_pSupportRegion.union k.isCompact_image_qSupportRegion).union k.isCompact_closedFlowTube

theorem isClosed_perturbationSupportRegion : IsClosed k.perturbationSupportRegion := k.isCompact_perturbationSupportRegion.isClosed

theorem push_pPerturbationField_eq_zero_of_notMem {x : M} (hx : x ∉ c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB) :
    c.e.push k.pPerturbationField x = 0 :=
  MorseNormalChart.push_eq_zero_of_notMem_image (fun _ hy => k.pPerturbationField_eq_zero_of_notMem hy) hx

theorem push_qPerturbationField_eq_zero_of_notMem {x : M}
    (hx : x ∉ c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB) : c.d.push k.qPerturbationField x = 0 :=
  MorseNormalChart.push_eq_zero_of_notMem_image (fun _ hy => k.qPerturbationField_eq_zero_of_notMem hy) hx

theorem cancellationField_eq_V_of_notMem {x : M} (hx : x ∉ k.perturbationSupportRegion) : k.cancellationField x = c.D.V x := by
  simp only [perturbationSupportRegion, mem_union, not_or] at hx
  rw [cancellationField_apply, k.push_pPerturbationField_eq_zero_of_notMem hx.1.1, k.push_qPerturbationField_eq_zero_of_notMem hx.1.2,
    k.localizedMiddlePerturbation_eq_zero_of_notMem_closedFlowTube hx.2, add_zero, add_zero, add_zero]

theorem support_cancellationField_subset : Function.support k.cancellationField ⊆ tsupport c.D.V ∪ k.perturbationSupportRegion := fun x hx => by
  by_contra h
  rw [mem_union, not_or] at h
  apply hx
  rw [k.cancellationField_eq_V_of_notMem h.2]
  exact image_eq_zero_of_notMem_tsupport h.1

theorem isCompact_tsupport_cancellationField : IsCompact (tsupport k.cancellationField) :=
  (c.D.compact.union k.isCompact_perturbationSupportRegion).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal k.support_cancellationField_subset (c.D.compact.union k.isCompact_perturbationSupportRegion).isClosed)

theorem image_pSupportRegion_subset_strip :
    c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB ⊆ f ⁻¹' Icc (a' + c.η₀) (b' - c.η₀) := by
  rintro x ⟨y, hy, rfl⟩
  have h := c.η₀_spec p c.hp (c.e.χ y) ⟨y, hy.1.trans c.ρB_le_R, rfl⟩
  exact ⟨h.1.le, h.2.le⟩

theorem image_qSupportRegion_subset_strip :
    c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB ⊆
      f ⁻¹' Icc (a' + c.η₀) (b' - c.η₀) := by
  rintro x ⟨y, hy, rfl⟩
  have hyR : morseNorm n y ≤ c.d.R := by
    have := (morseNorm_sq_le_of_mem_qSupportRegion c.d.hk c.hkq hy).trans k.Kq_radius_lt.le
    exact ((Real.le_sqrt (ModelField.morseNorm_nonneg y) (by linarith [c.hε])).2 this).trans
      (by linarith [c.sqrt_three_ε_lt_rmq, (c.D.hrm q c.hq).2])
  have h := c.η₀_spec q c.hq (c.d.χ y) ⟨y, hyR, rfl⟩
  exact ⟨h.1.le, h.2.le⟩

theorem perturbationSupportRegion_subset_strip : k.perturbationSupportRegion ⊆ f ⁻¹' Icc (a' + c.η₀) (b' - c.η₀) := by
  refine union_subset (union_subset k.image_pSupportRegion_subset_strip k.image_qSupportRegion_subset_strip) ?_
  intro x hx
  have h := hx.1
  have h1 := c.a'_add_η₀_lt_f_p
  have h2 := c.f_p_add_lt_c₁_sub_η
  have h3 := c.c₂_add_η_lt_f_q_sub
  have h4 := c.f_q_add_η₀_lt_b'
  have h5 := c.η_pos
  exact ⟨by nlinarith [sq_nonneg c.e.r₀, h.1], by nlinarith [sq_nonneg c.d.r₀, h.2]⟩

theorem perturbationSupportRegion_subset_strip' : k.perturbationSupportRegion ⊆ f ⁻¹' Icc a' b' := fun x hx => by
  have h := k.perturbationSupportRegion_subset_strip hx
  have := c.η₀_pos
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

open scoped Classical in
theorem pullback_cancellationField_p {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (k.cancellationField (c.e.χ y)) : Fin n → ℝ) =
      ModelField.modelField 0 c.e.r₀ y + k.pPerturbationField y +
        (if c.e.χ y ∈ c.orientedChartTube then
          (2 * (k.βm (c.e.χ y) * c.ψm (c.e.χ y))) • (-ModelField.modelField 0 c.e.r₀ y) +
            (2 * (c.lam * (k.βm' (c.e.χ y) * c.ψm' (c.e.χ y)))) • c.pTransverseField y
        else 0) := by
  have hyb := c.mem_ball_p_of_sq_lt hy
  have hk0 : c.e.k = 0 := c.hkp
  have hmodel : mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (c.D.V (c.e.χ y)) =
      ModelField.modelField 0 c.e.r₀ y := by
    rw [← hk0]; exact c.D.model p c.hp y (c.morseNorm_lt_rmp_of_sq_lt hy)
  have hq0 : c.d.push k.qPerturbationField (c.e.χ y) = 0 :=
    MorseNormalChart.push_apply_of_notMem _ fun h =>
      (c.D.disjoint p c.hp q c.hq c.p_ne_q).notMem_of_mem_left (mem_image_of_mem _ hyb) h
  rw [cancellationField_apply, map_add, map_add, map_add, hq0, map_zero, add_zero, hmodel,
    MorseNormalChart.pullback_push _ hyb]
  congr 1
  split_ifs with hT
  · rw [k.localizedMiddlePerturbation_of_mem hT]
    unfold middlePerturbation
    rw [map_add, map_smul, map_smul, map_neg, hmodel]
    rfl
  · rw [k.localizedMiddlePerturbation_of_notMem hT, map_zero]
    rfl

open scoped Classical in
theorem pullback_cancellationField_q {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (k.cancellationField (c.d.χ y)) : Fin n → ℝ) =
      ModelField.modelField c.d.k c.d.r₀ y + k.qPerturbationField y +
        (if c.d.χ y ∈ c.orientedChartTube then
          (2 * (k.βm (c.d.χ y) * c.ψm (c.d.χ y))) •
              (-ModelField.modelField c.d.k c.d.r₀ y) +
            (2 * (c.lam * (k.βm' (c.d.χ y) * c.ψm' (c.d.χ y)))) • c.qTransverseField y
        else 0) := by
  have hyb := c.mem_ball_q_of_sq_lt hy
  have hmodel : mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (c.D.V (c.d.χ y)) =
      ModelField.modelField c.d.k c.d.r₀ y :=
    c.D.model q c.hq y (c.morseNorm_lt_rmq_of_sq_lt hy)
  have hp0 : c.e.push k.pPerturbationField (c.d.χ y) = 0 :=
    MorseNormalChart.push_apply_of_notMem _ fun h =>
      (c.D.disjoint q c.hq p c.hp c.p_ne_q.symm).notMem_of_mem_left (mem_image_of_mem _ hyb) h
  rw [cancellationField_apply, map_add, map_add, map_add, hp0, map_zero, add_zero, hmodel,
    MorseNormalChart.pullback_push _ hyb]
  congr 1
  split_ifs with hT
  · rw [k.localizedMiddlePerturbation_of_mem hT]
    unfold middlePerturbation
    rw [map_add, map_smul, map_smul, map_neg, hmodel]
    rfl
  · rw [k.localizedMiddlePerturbation_of_notMem hT, map_zero]
    rfl

theorem cancellationField_ne_zero_of_pullback_p {y : Fin n → ℝ}
    (h : mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (k.cancellationField (c.e.χ y)) ≠
      (0 : Fin n → ℝ)) :
    k.cancellationField (c.e.χ y) ≠ 0 := fun h0 => h (by rw [h0]; exact map_zero _)

theorem cancellationField_ne_zero_of_pullback_q {y : Fin n → ℝ}
    (h : mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (k.cancellationField (c.d.χ y)) ≠
      (0 : Fin n → ℝ)) :
    k.cancellationField (c.d.χ y) ≠ 0 := fun h0 => h (by rw [h0]; exact map_zero _)

end CancelConsts

theorem dot_eq_sum (y z : Fin n → ℝ) : dot y z = ∑ i, y i * z i := by
  simp [dot, PiLp.inner_apply, mul_comm]

theorem theta_mul_sq_le {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) :
    ModelField.theta r₀ y * morseNorm n y ^ 2 ≤ 1 := by
  have hden := ModelField.thetaDen_pos hr₀ y
  have hb := ModelField.bump_nonneg r₀ y
  have h1 : morseNorm n y ^ 2 ≤ ModelField.thetaDen r₀ y := by
    unfold ModelField.thetaDen; nlinarith [sq_nonneg r₀]
  rw [ModelField.theta, inv_mul_le_iff₀ hden, mul_one]
  exact h1

theorem modelField_ne_zero {k : ℕ} (hk : k ≤ n) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {y : Fin n → ℝ} (hy : y ≠ 0) : ModelField.modelField k r₀ y ≠ 0 := by
  intro h
  have hθ := ModelField.theta_pos hr₀ y
  have h1 := congrArg (negPart hk) h
  have h2 := congrArg (posPart hk) h
  rw [ModelField.negPart_modelField,
    show negPart hk (0 : Fin n → ℝ) = 0 from (ModelField.negPartL hk).map_zero] at h1
  rw [ModelField.posPart_modelField, posPart_zero, neg_eq_zero] at h2
  have h1' : negPart hk y = 0 := (smul_eq_zero.1 h1).resolve_left hθ.ne'
  have h2' : posPart hk y = 0 := (smul_eq_zero.1 h2).resolve_left hθ.ne'
  apply hy
  rw [← recombine_decompose hk y, h1', h2']
  ext i
  simp [recombine]

theorem perp_neg (e₁ y : Fin n → ℝ) : perp e₁ (-y) = -perp e₁ y := by
  rw [← neg_one_smul ℝ y, perp_smul, neg_one_smul]

theorem perp_zero (e₁ : Fin n → ℝ) : perp e₁ (0 : Fin n → ℝ) = 0 := by
  rw [perp, axial_zero, zero_smul, sub_zero]

theorem eq_norm_smul_e₁_of_eq_smul {b : ℝ} (hb : 0 ≤ b) {y : Fin n → ℝ}
    (hy : y = b • c.e₁) : y = morseNorm n y • c.e₁ := by
  rw [hy, ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_nonneg hb]

theorem e₁_ne_zero : c.e₁ ≠ 0 := by
  intro h
  have := c.morseNorm_e₁
  rw [h, morseNorm_zero] at this
  exact zero_ne_one this

theorem lo₂_le : c.lo₂ ≤ f p + c.ε := by
  unfold lo₂ c₁
  have := c.η_lt_left; have := c.ε₁_lt_ε
  unfold ε₁ at *; nlinarith [sq_nonneg c.e.r₀]

theorem uB_sq_lt_of_le {t : ℝ} (ht : t ≤ c.c₁ - c.η) : c.uB ^ 2 < 2 * (f q - t) := by
  rw [c.uB_sq]
  unfold c₁ at ht
  have := c.hlt; have := c.ε₁_lt_ε; have := c.ε₂_lt_ε; have := c.η_pos
  linarith

theorem lo₂_lt_f_p_add_ε : c.lo₂ < f p + c.ε := by
  unfold lo₂ c₁
  have := c.η_lt_left; have := c.ε₁_lt_ε
  unfold ε₁ at *; nlinarith [sq_nonneg c.e.r₀]

theorem f_q_sub_ε_lt_hi₁ : f q - c.ε < c.hi₁ := by
  unfold hi₁ c₂
  have := c.η_lt_right; have := c.ε₂_lt_ε
  unfold ε₂ at *; nlinarith [sq_nonneg c.d.r₀]

theorem p_mem_pBall' : p ∈ c.pBall' :=
  ⟨0, by
    change morseNorm n (0 : Fin n → ℝ) ^ 2 < 3 * c.ε
    rw [morseNorm_zero]; nlinarith [c.hε], c.e.hχ0⟩

theorem q_mem_qBall' : q ∈ c.qBall' :=
  ⟨0, by
    change morseNorm n (0 : Fin n → ℝ) ^ 2 < 3 * c.ε
    rw [morseNorm_zero]; nlinarith [c.hε], c.d.hχ0⟩

theorem V_ne_zero_of_notMem {x : M} (hx : f x ∈ Icc a' b') (hp : x ∉ c.pBall')
    (hq : x ∉ c.qBall') : c.D.V x ≠ 0 := by
  intro h0
  have hcrit : x ∉ ({p, q} : Finset M) := by
    rw [mem_pair_iff]
    rintro (rfl | rfl)
    · exact hp c.p_mem_pBall'
    · exact hq c.q_mem_qBall'
  have := c.D.neg x hx hcrit
  rw [h0, map_zero, map_zero] at this
  exact lt_irrefl _ this

theorem dfV_V_eq_neg_one_of_mem_tube {x : M} (hx : f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    dfV I f c.D.V x = -1 := by
  have h1 := c.a'_lt_c₁_sub_η; have h2 := c.c₂_add_η_lt_b'
  exact c.D.unit x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    (c.levels_avoid_smallBall (Ioo_subset_Icc_self hx))

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem βm_mul_ψm_eq_zero {x : M} (h : k.βm' x * c.ψm' x = 0) : k.βm x * c.ψm x = 0 := by
  by_contra h'
  rcases mul_ne_zero_iff.1 h' with ⟨h1, h2⟩
  rw [k.βm'_eq_one_of_βm_ne_zero h1, c.ψm'_eq_one_of_ψm_ne_zero h2, one_mul] at h
  exact one_ne_zero h

theorem βm'_mul_ψm'_eq_one {x : M} (h : k.βm x * c.ψm x ≠ 0) : k.βm' x * c.ψm' x = 1 := by
  rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
  rw [k.βm'_eq_one_of_βm_ne_zero h1, c.ψm'_eq_one_of_ψm_ne_zero h2, one_mul]

theorem cancellationField_ne_zero_p {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    k.cancellationField (c.e.χ y) ≠ 0 := by
  classical
  apply k.cancellationField_ne_zero_of_pullback_p
  rw [k.pullback_cancellationField_p hy]
  change _ ≠ (0 : Fin n → ℝ)
  have he₁ := c.morseNorm_e₁
  have he₁0 := c.e₁_ne_zero
  have hδ := k.hδ
  have hθ := ModelField.theta_pos c.e.hr₀ y
  have hm := c.hm_p
  have hyrm := c.morseNorm_lt_rmp_of_sq_lt hy
  have hyR : morseNorm n y ≤ c.e.R := hyrm.le.trans (c.D.hrm p c.hp).2
  have hfx : f (c.e.χ y) = f p + morseNorm n y ^ 2 / 2 := c.f_chart_p hyR
  have hmf : ModelField.modelField 0 c.e.r₀ y = -(ModelField.theta c.e.r₀ y • y) :=
    modelField_index_zero _ _
  have hYp : k.pPerturbationField y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  have hlam := c.lam_pos
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [ite_eq_left hT]
    have hy0 : y ≠ 0 := by
      rintro rfl
      have h1 := hT.1.1.1
      rw [hfx, morseNorm_zero] at h1
      have := c.f_p_add_lt_c₁_sub_η
      nlinarith [sq_nonneg c.e.r₀]
    have hr₀y : c.e.r₀ < morseNorm n y := by
      have h1 := hT.1.1.1
      rw [hfx] at h1
      have := c.f_p_add_lt_c₁_sub_η
      nlinarith [ModelField.morseNorm_nonneg y, c.e.hr₀]
    by_cases hζ : c.ζ (c.e.χ y) = 0
    · obtain ⟨hyax, hfle⟩ := c.axis_of_ζ_eq_zero_p hy hT hζ
      have hZ : c.pTransverseField y = 0 := by
        unfold pTransverseField; rw [(c.transverseField_eq_zero_iff hT.1).2 hζ, map_zero]; rfl
      have hβm := k.βm_eq_one_of_ζ_eq_zero hζ
      have hψ := ψp_add_plateau (n := n) c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ c.ρA_sq_eq c.ρB_sq_eq
        (y := y) (by rw [← hfx]; exact hfle.trans c.f_q_sub_ε_lt_hi₁.le)
      have hψm : c.ψm (c.e.χ y) =
          plateau c.lo₁ c.lo₂ c.hi₁ c.hi₂ (f p + morseNorm n y ^ 2 / 2) := by
        unfold IndexZeroCancellingPair.ψm; rw [hfx]
      set a := morseNorm n y with ha
      have hapos : 0 < a := morseNorm_pos hy0
      have hβp : βp k.δ k.τ c.e₁ y = 1 := by
        rw [hyax]; exact βp_smul_self he₁ hδ (by linarith)
      have hθa : 0 < ModelField.theta c.e.r₀ y * a := mul_pos hθ hapos
      have hθm : ModelField.theta c.e.r₀ y * a < c.m' := hm y
      have hs0 := c.ψm_nonneg (c.e.χ y)
      have hs1 := c.ψm_le_one (c.e.χ y)
      have hpos := axis_ineq_p hθa hθm hs0 hs1
      have hψp : ψp c.ρA c.ρB y = 1 - c.ψm (c.e.χ y) := by rw [hψm]; linarith
      rw [hYp, hβp, hmf, hZ, hβm, smul_zero, add_zero, hψp]
      clear_value a
      refine ne_of_eq_of_ne ?_ (smul_ne_zero hpos.ne' he₁0)
      rw [hyax]
      simp only [smul_smul, neg_neg, ← neg_smul, ← add_smul]
      congr 1
      ring
    · have hZp : c.pTransverseField y ≠ 0 := fun h =>
        hζ ((c.transverseField_eq_zero_iff hT.1).1 (c.transverseField_eq_zero_of_pTransverseField_eq_zero hy h))
      have horth : dot y (c.pTransverseField y) = 0 := by
        rw [dot_eq_sum]; exact c.transverseField_chart_p_orth hyrm hT.1
      set C := k.βm (c.e.χ y) * c.ψm (c.e.χ y) with hC
      set Bc := k.βm' (c.e.χ y) * c.ψm' (c.e.χ y) with hBc
      set A := βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y with hA
      have hA0 : 0 ≤ A := mul_nonneg (βp_nonneg _) (ψp_nonneg _)
      have hBc0 : 0 ≤ Bc := mul_nonneg (k.βm'_nonneg _) (c.ψm'_nonneg _)
      have hBcC : Bc = 0 → C = 0 := fun h => k.βm_mul_ψm_eq_zero h
      intro h0
      rw [hYp, hmf] at h0
      by_cases hperp : perpSq c.e₁ y = 0
      · have hyax := eq_smul_of_perpSq_eq_zero he₁ hperp
        set a := axial c.e₁ y with ha
        have ha0 : a ≠ 0 := by
          intro h; apply hy0; rw [hyax, h, zero_smul]
        rcases lt_or_gt_of_ne ha0 with haneg | hapos
        · have hZe : axial c.e₁ (c.pTransverseField y) = 0 := by
            have h1 : dot y (c.pTransverseField y) = a * dot c.e₁ (c.pTransverseField y) := by
              calc dot y (c.pTransverseField y) = dot (a • c.e₁) (c.pTransverseField y) := by rw [← hyax]
                _ = a * dot c.e₁ (c.pTransverseField y) := dot_smul_left _ _ _
            rw [h1] at horth
            rw [axial, dot_comm]
            exact (mul_eq_zero.1 horth).resolve_left ha0
          have hperpZ : perp c.e₁ (c.pTransverseField y) = c.pTransverseField y := by
            rw [perp, hZe, zero_smul, sub_zero]
          generalize hZv : c.pTransverseField y = Zv at hZp hperpZ h0 hZe
          clear_value a
          subst hyax
          have hperpP := congrArg (perp c.e₁) h0
          simp only [perp_zero, perp_add, perp_smul, perp_neg, perp_smul_self he₁, hperpZ,
            smul_zero, neg_zero, zero_add] at hperpP
          have hBcz : Bc = 0 := by
            rcases smul_eq_zero.1 hperpP with h | h
            · rcases mul_eq_zero.1 h with h | h
              · norm_num at h
              · rcases mul_eq_zero.1 h with h | h
                · exact absurd h hlam.ne'
                · exact h
            · exact absurd h hZp
          have hCz : C = 0 := hBcC hBcz
          rw [hBcz, hCz] at h0
          have haxP := congrArg (axial c.e₁) h0
          simp only [axial_add, axial_smul, axial_neg, axial_smul_self he₁, axial_zero, hZe,
            mul_zero, zero_mul, add_zero] at haxP
          have : 0 < -(ModelField.theta c.e.r₀ (a • c.e₁) * a) + c.m' * A := by
            have := c.m'_pos
            nlinarith [mul_pos hθ (neg_pos.2 haneg)]
          linarith
        · have hya' : y = a • c.e₁ := hyax
          have hnorm : morseNorm n y = a := by
            rw [hya', ModelField.morseNorm_smul, he₁, mul_one, abs_of_pos hapos]
          have h := c.axis_p_mem_orientedChartTube (a := a) (by rw [← hnorm]; exact hr₀y)
            (by rw [← hnorm]; exact hy) (by rw [← hya']; exact hT.1.1)
          rw [← hya'] at h
          exact hζ h.2
      · have hperp' : 0 < perpSq c.e₁ y := lt_of_le_of_ne (perpSq_nonneg he₁ y) (Ne.symm hperp)
        have hL := congrArg (axialDefectDeriv c.e₁ y) h0
        rw [map_add, map_add, map_add, map_zero, map_neg, map_smul, map_smul, map_smul, map_smul,
          map_neg, map_neg, map_smul, axialDefectDeriv_self c.e₁ hy0] at hL
        simp only [smul_eq_mul, mul_zero, neg_zero, zero_add] at hL
        have hLe := axialDefectDeriv_e₁_neg he₁ hy0 hperp'
        have hLZ : Bc ≠ 0 → axialDefectDeriv c.e₁ y (c.pTransverseField y) < 0 := by
          intro hne
          obtain ⟨h1, -⟩ := mul_ne_zero_iff.1 hne
          have hζn : 0 < ‖c.ζ (c.e.χ y)‖ := norm_pos_iff.2 hζ
          exact k.hdB y hy hT hζn (k.norm_ζ_lt_of_βm'_ne_zero h1)
        have hA_ : c.m' * A * axialDefectDeriv c.e₁ y c.e₁ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg c.m'_pos.le hA0) hLe.le
        have hB_ : 2 * (c.lam * Bc) * axialDefectDeriv c.e₁ y (c.pTransverseField y) ≤ 0 := by
          by_cases hne : Bc = 0
          · rw [hne]; simp
          · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hLZ hne).le
        have hAz : A = 0 := by
          by_contra hne
          have : c.m' * A * axialDefectDeriv c.e₁ y c.e₁ < 0 :=
            mul_neg_of_pos_of_neg (mul_pos c.m'_pos (lt_of_le_of_ne hA0 (Ne.symm hne))) hLe
          linarith
        have hBz : Bc = 0 := by
          by_contra hne
          have : 2 * (c.lam * Bc) * axialDefectDeriv c.e₁ y (c.pTransverseField y) < 0 :=
            mul_neg_of_pos_of_neg (by have := lt_of_le_of_ne hBc0 (Ne.symm hne); positivity)
              (hLZ hne)
          linarith
        have hCz : C = 0 := hBcC hBz
        rw [hAz, hBz, hCz] at h0
        simp only [mul_zero, zero_smul, add_zero] at h0
        exact hy0 ((smul_eq_zero.1 (neg_eq_zero.1 h0)).resolve_left hθ.ne')
  · rw [ite_eq_right hT, add_zero]
    by_cases hψ : ψp c.ρA c.ρB y = 1
    · exact pPerturbationField_add_model_ne_zero c.e.hr₀ he₁ hδ hm hψ
    have hρA : c.ρA < morseNorm n y := by
      by_contra h; push Not at h
      exact hψ (ψp_eq_one c.ρA_pos.le c.ρA_lt_ρB h)
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [morseNorm_zero] at hρA; linarith [c.ρA_pos]
    rcases le_or_gt c.ρB (morseNorm n y) with hρB | hρB
    · have hψ0 : ψp c.ρA c.ρB y = 0 := ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hρB
      rw [hYp, hψ0, mul_zero, mul_zero, zero_smul, add_zero]
      exact modelField_ne_zero (Nat.zero_le n) c.e.hr₀ hy0
    · intro h0
      rw [hYp, hmf] at h0
      have hyax : y = morseNorm n y • c.e₁ := by
        apply c.eq_norm_smul_e₁_of_eq_smul (b := (ModelField.theta c.e.r₀ y)⁻¹ *
          (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)))
        · have := c.m'_pos
          exact mul_nonneg (inv_pos.2 hθ).le
            (mul_nonneg this.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _)))
        · have h1 : ModelField.theta c.e.r₀ y • y =
              (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := by
            rw [neg_add_eq_zero] at h0; exact h0
          rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]
      have hr₀y : c.e.r₀ < morseNorm n y := c.r₀p_lt_ρA.trans hρA
      have hlev : f (c.e.χ (morseNorm n y • c.e₁)) ∈
          Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
        rw [← hyax, hfx]
        have h1 := c.ρA_sq_eq; have h2 := c.ρB_sq_eq
        have h3 : c.ρA ^ 2 < morseNorm n y ^ 2 := pow_lt_pow_left₀ hρA c.ρA_pos.le two_ne_zero
        have h4 : morseNorm n y ^ 2 < c.ρB ^ 2 :=
          pow_lt_pow_left₀ hρB (ModelField.morseNorm_nonneg y) two_ne_zero
        have := c.η_pos; have := c.lo₂_lt_hi₁
        unfold lo₁ lo₂ hi₁ at *
        constructor <;> linarith
      have h := c.axis_p_mem_orientedChartTube hr₀y (by rw [← hyax] at *; exact hy) hlev
      rw [← hyax] at h
      exact hT h.1

theorem cancellationField_ne_zero_q {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    k.cancellationField (c.d.χ y) ≠ 0 := by
  classical
  apply k.cancellationField_ne_zero_of_pullback_q
  rw [k.pullback_cancellationField_q hy]
  change _ ≠ (0 : Fin n → ℝ)
  have hδ := k.hδ
  have hθ := ModelField.theta_pos c.d.hr₀ y
  have hm := c.hm_q
  have hσ := c.σ_eq
  have hσ2 := c.σ_sq
  have hyrm := c.morseNorm_lt_rmq_of_sq_lt hy
  have hyR : morseNorm n y ≤ c.d.R := hyrm.le.trans (c.D.hrm q c.hq).2
  have hfx := c.f_chart_q hyR
  have hYq : k.qPerturbationField y =
      -(c.σ * c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) •
        c.e₀' := rfl
  have hlam := c.lam_pos
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [ite_eq_left hT]
    have hstay := c.hstay_of_mem_qBall' hy hT.1
    have hstayπ := c.hstay_π_of_hstay hstay
    have hσu := c.σ_uq_pos_of_mem_orientedChartTube hy hT
    by_cases hv : posPart c.d.hk y = 0
    · have hζ : c.ζ (c.d.χ y) = 0 :=
        c.ζ_eq_zero_of_posPart_eq_zero hT.1 hstayπ (by rw [c.chart_q_symm_eq' hy]; exact hv)
      have hZ : c.qTransverseField y = 0 := by
        unfold qTransverseField; rw [(c.transverseField_eq_zero_iff hT.1).2 hζ, map_zero]; rfl
      have hβm := k.βm_eq_one_of_ζ_eq_zero hζ
      have hβq : βq c.d.hk c.hkq k.δ k.τ c.σ y = 1 :=
        βq_axis c.d.hk c.hkq hδ hv (by linarith)
      have hlo : c.lo₂ ≤ f (c.d.χ y) := by
        by_contra hlt
        push Not at hlt
        have h := c.eq_flow_z₀_of_ζ_eq_zero hT hζ
        have hs : c.transitTime ≤ f q - c.ε - f (c.d.χ y) := by
          have := c.lo₂_lt_f_p_add_ε; unfold transitTime; linarith
        have := c.flow_z₀_mem_pBall' hs
        rw [← h] at this
        exact c.disjoint_pBall'_qBall'.notMem_of_mem_left this ⟨y, hy, rfl⟩
      have hfx' : f (c.d.χ y) = f q - uq c.d.hk c.hkq y ^ 2 / 2 := by
        rw [hfx, hv, norm_zero]; ring
      have hψ := ψq_add_plateau c.d.hk c.hkq c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ c.uA_sq_eq
        c.uB_sq_eq (y := y) (by rw [← hfx']; exact hlo)
      have hψm : c.ψm (c.d.χ y) =
          plateau c.lo₁ c.lo₂ c.hi₁ c.hi₂ (f q - uq c.d.hk c.hkq y ^ 2 / 2) := by
        unfold IndexZeroCancellingPair.ψm; rw [hfx']
      have hψq : ψq c.d.hk c.hkq c.uA c.uB y = 1 - c.ψm (c.d.χ y) := by rw [hψm]; linarith
      intro h0
      have hu := congrArg (uq c.d.hk c.hkq) h0
      rw [hZ, hβm, hYq, hβq] at hu
      simp only [uq_add, uq_smul, uq_neg, uq_modelField, c.uq_e₀', uq_zero, mul_one,
        add_zero, smul_zero] at hu
      have habs : c.σ * uq c.d.hk c.hkq y = morseNorm n y := by
        rw [morseNorm_eq_abs_uq c.d.hk c.hkq hv]
        rcases hσ with h | h
        · rw [h, one_mul]; rw [h, one_mul] at hσu; exact (abs_of_pos hσu).symm
        · rw [h, neg_one_mul]; rw [h, neg_one_mul] at hσu
          exact (abs_of_neg (by linarith)).symm
      have hpos : 0 < ModelField.theta c.d.r₀ y * morseNorm n y := by
        have : 0 < morseNorm n y := by
          rw [← habs]; exact hσu
        positivity
      have hlt := axis_ineq_q hpos (hm y) (ψq_nonneg c.d.hk c.hkq (ua := c.uA) (ub := c.uB) y)
        (ψq_le_one c.d.hk c.hkq (ua := c.uA) (ub := c.uB) y)
      rw [hψq] at hlt
      have : ModelField.theta c.d.r₀ y * morseNorm n y * (2 * (1 - c.ψm (c.d.χ y)) - 1) -
            c.m' * (1 - c.ψm (c.d.χ y)) = 0 := by
        rw [hψq] at hu
        linear_combination c.σ * hu -
          ModelField.theta c.d.r₀ y * (1 - 2 * c.ψm (c.d.χ y)) * habs +
          c.m' * (1 - c.ψm (c.d.χ y)) * hσ2
      linarith
    · set C := k.βm (c.d.χ y) * c.ψm (c.d.χ y) with hC
      set Bc := k.βm' (c.d.χ y) * c.ψm' (c.d.χ y) with hBc
      have hBc0 : 0 ≤ Bc := mul_nonneg (k.βm'_nonneg _) (c.ψm'_nonneg _)
      have hC0 : 0 ≤ C := mul_nonneg (k.βm_nonneg _) (c.ψm_nonneg _)
      have hC1 : C ≤ 1 :=
        (mul_le_mul (k.βm_le_one _) (c.ψm_le_one _) (c.ψm_nonneg _) zero_le_one).trans_eq
          (one_mul 1)
      have hpv := posPart_transverseField_chart_q (c := c) hyrm hT.1 hstay
      have hcoef := posPart_transverseField_chart_q_coeff_neg (c := c) hyR hT.1
      set b := ‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2)
        with hb
      intro h0
      have hp := congrArg (posPart c.d.hk) h0
      have hZq : posPart c.d.hk (c.qTransverseField y) = (-c.κ (c.d.χ y) * b) • posPart c.d.hk y := hpv
      rw [hYq] at hp
      simp only [ModelField.posPart_add, ModelField.posPart_smul, ModelField.posPart_neg,
        ModelField.posPart_modelField, c.posPart_e₀', hZq, posPart_zero, smul_zero,
        add_zero] at hp
      have hp' : (-(ModelField.theta c.d.r₀ y) + -(2 * C * -ModelField.theta c.d.r₀ y) +
          2 * (c.lam * Bc) * (-c.κ (c.d.χ y) * b)) • posPart c.d.hk y = 0 := by
        rw [← hp]; module
      have hK : -(ModelField.theta c.d.r₀ y) + -(2 * C * -ModelField.theta c.d.r₀ y) +
          2 * (c.lam * Bc) * (-c.κ (c.d.χ y) * b) ≠ 0 := by
        have hκ := c.one_le_κ (c.d.χ y)
        have hu2 := (c.normSq_negPart_of_mem hyR hT.1).1
        have hsum := morseNorm_sq_eq_negPart_add_posPart c.d.hk y
        have hb' : b * morseNorm n y ^ 2 = ‖negPart c.d.hk y‖ ^ 2 := by
          rw [hb, hsum]; field_simp
        have hθy := theta_mul_sq_le c.d.hr₀ y
        have hy2 : 0 < morseNorm n y ^ 2 := by
          have := (c.normSq_negPart_of_mem hyR hT.1).2
          rw [hsum]; positivity
        have hlm := c.lam_mul
        rcases le_or_gt C (1 / 2) with hCle | hCgt
        · intro hK0
          have h1 : 0 ≤ (1 - 2 * C) * ModelField.theta c.d.r₀ y := by
            apply mul_nonneg _ hθ.le; linarith
          have hb0 : 0 ≤ b := by rw [hb]; positivity
          have hκ0 := c.κ_pos (c.d.χ y)
          have h2 : 0 ≤ 2 * (c.lam * Bc) * (c.κ (c.d.χ y) * b) := by positivity
          have h3 : (1 - 2 * C) * ModelField.theta c.d.r₀ y = 0 := by linarith
          have h4 : C = 1 / 2 := by
            rcases mul_eq_zero.1 h3 with h | h
            · linarith
            · exact absurd h hθ.ne'
          have hBc1 : Bc = 1 := k.βm'_mul_ψm'_eq_one (by rw [← hC, h4]; norm_num)
          rw [hBc1, h4] at hK0
          have hbpos : 0 < b := by
            rw [hb]
            exact div_pos (c.normSq_negPart_of_mem hyR hT.1).2 (by rw [← hsum]; exact hy2)
          have := mul_pos hlam (mul_pos hκ0 hbpos)
          linarith
        · have hBc1 : Bc = 1 :=
            k.βm'_mul_ψm'_eq_one (by rw [← hC]; intro h; rw [h] at hCgt; linarith)
          rw [hBc1]
          intro hK0
          have e1 : (2 * C - 1) * (ModelField.theta c.d.r₀ y * morseNorm n y ^ 2) =
              2 * c.lam * c.κ (c.d.χ y) * (b * morseNorm n y ^ 2) := by
            linear_combination (morseNorm n y ^ 2) * hK0
          rw [hb'] at e1
          have h6 : (2 * C - 1) * (ModelField.theta c.d.r₀ y * morseNorm n y ^ 2) ≤ 1 * 1 :=
            mul_le_mul (by linarith) hθy (by positivity) (by norm_num)
          have hκ0 := c.κ_pos (c.d.χ y)
          have h7 : 2 * c.lam * 1 * (2 * (c.ε₂ - c.η)) ≤
              2 * c.lam * c.κ (c.d.χ y) * ‖negPart c.d.hk y‖ ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hκ (by positivity)) hu2
              (by linarith [c.ε₂_sub_η_pos]) (by positivity)
          have hlm := c.lam_mul
          linarith
      exact hv ((smul_eq_zero.1 hp').resolve_left hK)
  · rw [ite_eq_right hT, add_zero]
    by_cases hcase : posPart c.d.hk y ≠ 0 ∨ c.σ * uq c.d.hk c.hkq y ≤ 0 ∨
        ψq c.d.hk c.hkq c.uA c.uB y = 1
    · exact qPerturbationField_add_model_ne_zero c.d.hk c.hkq c.d.hr₀ hσ hδ c.uA_pos.le c.uA_lt_uB hm hcase
    push Not at hcase
    obtain ⟨hv, hσu, hψ⟩ := hcase
    have hfx' : f (c.d.χ y) = f q - uq c.d.hk c.hkq y ^ 2 / 2 := by
      rw [hfx, hv, norm_zero]; ring
    have huA : c.uA ^ 2 < uq c.d.hk c.hkq y ^ 2 := by
      by_contra h; push Not at h
      exact hψ (ψq_eq_one c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB h)
    have hfhi : f (c.d.χ y) < c.c₂ + c.η := by
      rw [hfx']
      have := c.uA_sq_eq; have := c.hi₁_lt_hi₂; have := c.η_pos
      unfold hi₂ at *; linarith
    by_cases hf : c.c₁ - c.η < f (c.d.χ y)
    · exact absurd (c.mem_orientedChartTube_of_σ_uq_pos hy ⟨hf, hfhi⟩ hσu) hT
    · push Not at hf
      have huB : c.uB ^ 2 ≤ uq c.d.hk c.hkq y ^ 2 := by
        have := c.uB_sq_lt_of_le hf
        rw [hfx'] at this; linarith
      have hψ0 : ψq c.d.hk c.hkq c.uA c.uB y = 0 :=
        ψq_eq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB huB
      rw [hYq, hψ0, mul_zero, mul_zero, neg_zero, zero_smul, add_zero]
      apply modelField_ne_zero c.d.hk c.d.hr₀
      intro h
      rw [h, uq_zero, mul_zero] at hσu
      exact lt_irrefl _ hσu

theorem cancellationField_ne_zero_outside {x : M} (hx : f x ∈ Icc a' b') (hp : x ∉ c.pBall')
    (hq : x ∉ c.qBall') : k.cancellationField x ≠ 0 := by
  have hYp : c.e.push k.pPerturbationField x = 0 :=
    k.push_pPerturbationField_eq_zero_of_notMem fun h => hp (k.pSupportRegion_subset_pBall' h)
  have hYq : c.d.push k.qPerturbationField x = 0 :=
    k.push_qPerturbationField_eq_zero_of_notMem fun h => hq (k.qSupportRegion_subset_qBall' h)
  by_cases hT : x ∈ c.orientedChartTube
  · rw [cancellationField_apply, hYp, hYq, add_zero, add_zero, k.localizedMiddlePerturbation_of_mem hT]
    unfold middlePerturbation
    set C := k.βm x * c.ψm x with hC
    set Bc := k.βm' x * c.ψm' x with hBc
    intro h0
    have hdf := congrArg (dfL I f x) h0
    rw [map_add, map_add, map_smul, map_smul, map_neg, map_zero, dfL_apply, dfL_apply,
      c.dfV_V_eq_neg_one_of_mem_tube hT.1.1, c.df_transverseField hT.1] at hdf
    simp only [smul_eq_mul, mul_zero, add_zero, mul_neg, mul_one] at hdf
    have hC12 : C = 1 / 2 := by linarith
    have hBc1 : Bc = 1 := k.βm'_mul_ψm'_eq_one (by rw [← hC, hC12]; norm_num)
    rw [hC12, hBc1] at h0
    have hZ : c.transverseField x = 0 := by
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, mul_one, add_neg_cancel_left] at h0
      have := c.lam_pos
      exact (smul_eq_zero.1 h0).resolve_left (by positivity)
    have hζ : c.ζ x = 0 := (c.transverseField_eq_zero_iff hT.1).1 hZ
    have hβm := k.βm_eq_one_of_ζ_eq_zero hζ
    have hψm : c.ψm x = 1 / 2 := by rw [hC, hβm, one_mul] at hC12; exact hC12
    have h := c.eq_flow_z₀_of_ζ_eq_zero hT hζ
    have hfade : f x < c.lo₂ ∨ c.hi₁ < f x := by
      by_contra hcon
      push Not at hcon
      have := c.ψm_eq_one hcon.1 hcon.2
      rw [hψm] at this; norm_num at this
    rcases hfade with hlt | hgt
    · apply hp
      rw [h]
      apply c.flow_z₀_mem_pBall'
      have := c.lo₂_lt_f_p_add_ε; unfold transitTime; linarith
    · apply hq
      rw [h]
      apply c.flow_z₀_mem_qBall'
      have := c.f_q_sub_ε_lt_hi₁; linarith
  · rw [cancellationField_apply, hYp, hYq, k.localizedMiddlePerturbation_of_notMem hT, add_zero, add_zero, add_zero]
    exact c.V_ne_zero_of_notMem hx hp hq

theorem cancellationField_ne_zero {x : M} (hx : f x ∈ Icc a' b') : k.cancellationField x ≠ 0 := by
  by_cases hp : x ∈ c.pBall'
  · obtain ⟨y, hy, rfl⟩ := hp
    exact k.cancellationField_ne_zero_p hy
  by_cases hq : x ∈ c.qBall'
  · obtain ⟨y, hy, rfl⟩ := hq
    exact k.cancellationField_ne_zero_q hy
  exact k.cancellationField_ne_zero_outside hx hp hq

end CancelConsts

section Holonomy

open scoped RealInnerProductSpace

def sheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : Fin n → ℝ :=
  (c.σ * Real.sqrt (2 * c.ε₂ + ‖v‖ ^ 2)) • c.e₀' + recombine c.d.hk 0 v

theorem posPart_sheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    posPart c.d.hk (c.sheet v) = v := by
  unfold sheet
  rw [ModelField.posPart_add, ModelField.posPart_smul, c.posPart_e₀', smul_zero, zero_add,
    ModelField.posPart_recombine]

theorem negPart_sheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    negPart c.d.hk (c.sheet v) =
      (c.σ * Real.sqrt (2 * c.ε₂ + ‖v‖ ^ 2)) • negPart c.d.hk c.e₀' := by
  unfold sheet
  rw [ModelField.negPart_add, ModelField.negPart_smul, ModelField.negPart_recombine, add_zero]

theorem uq_sheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    uq c.d.hk c.hkq (c.sheet v) = c.σ * Real.sqrt (2 * c.ε₂ + ‖v‖ ^ 2) := by
  have h := c.uq_e₀'
  rw [uq_apply] at h ⊢
  rw [c.negPart_sheet, PiLp.smul_apply, smul_eq_mul, h, mul_one]

theorem uq_sheet_sq (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    uq c.d.hk c.hkq (c.sheet v) ^ 2 = 2 * c.ε₂ + ‖v‖ ^ 2 := by
  have hε := c.ε₂_pos
  rw [c.uq_sheet, mul_pow, Real.sq_sqrt (by positivity), sq, c.σ_sq, one_mul]

theorem σ_uq_sheet_pos (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    0 < c.σ * uq c.d.hk c.hkq (c.sheet v) := by
  rw [c.uq_sheet, ← mul_assoc, c.σ_sq, one_mul]
  exact Real.sqrt_pos.2 (by have := c.ε₂_pos; positivity)

theorem morseNorm_sheet_sq (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    morseNorm n (c.sheet v) ^ 2 = 2 * c.ε₂ + 2 * ‖v‖ ^ 2 := by
  rw [morseNorm_sq_eq_uq c.d.hk c.hkq, c.uq_sheet_sq, c.posPart_sheet]; ring

theorem nf_sheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    morseNormalForm c.d.hk (f q) (c.sheet v) = c.c₂ := by
  rw [morseNormalForm_split, norm_negPart_sq c.d.hk c.hkq, c.uq_sheet_sq, c.posPart_sheet]
  unfold c₂; ring

theorem eq_of_parts {y z : Fin n → ℝ} (h1 : negPart c.d.hk y = negPart c.d.hk z)
    (h2 : posPart c.d.hk y = posPart c.d.hk z) : y = z := by
  rw [← recombine_decompose c.d.hk y, ← recombine_decompose c.d.hk z, h1, h2]

theorem sheet_zero : c.sheet 0 = c.w c.z₀ := by
  rw [c.w_z₀]
  apply c.eq_of_parts
  · rw [c.negPart_sheet, ModelField.negPart_smul, norm_zero]; simp
  · rw [c.posPart_sheet, ModelField.posPart_smul, c.posPart_e₀', smul_zero]

theorem lev_sheet (r : ℝ) (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    c.lev r (c.sheet v) = c.sheet (Real.exp (-r) • v) := by
  apply c.eq_of_parts
  · rw [c.negPart_lev, c.negPart_sheet, c.negPart_sheet, c.posPart_sheet, smul_smul]
    congr 1
    have hε := c.ε₂_pos
    have hE : ‖Real.exp (-r) • v‖ ^ 2 = Real.exp (-2 * r) * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [hE, add_comm (2 * c.ε₂) (‖v‖ ^ 2),
      add_comm (2 * c.ε₂) (Real.exp (-2 * r) * ‖v‖ ^ 2)]
    have h1 : 0 < ‖v‖ ^ 2 + 2 * c.ε₂ := by positivity
    have h2 : Real.sqrt (‖v‖ ^ 2 + 2 * c.ε₂) ≠ 0 := Real.sqrt_ne_zero'.2 h1
    field_simp
  · rw [c.posPart_lev, c.posPart_sheet, c.posPart_sheet]

theorem contDiff_sheet : ContDiff ℝ ∞ c.sheet := by
  have hε := c.ε₂_pos
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) =>
      c.σ * Real.sqrt (2 * c.ε₂ + ‖v‖ ^ 2)) :=
    contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun v => by positivity)
  have h2 : ContDiff ℝ ∞
      (fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) => recombine c.d.hk 0 v) := by
    have : (fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) => recombine c.d.hk 0 v) =
        fun v => ModelField.recombineL c.d.hk (0, v) := by
      funext v; rw [ModelField.recombineL_apply]
    rw [this]
    exact (ModelField.recombineL c.d.hk).contDiff.comp (contDiff_const.prodMk contDiff_id)
  exact (h1.smul contDiff_const).add h2

theorem continuous_sheet : Continuous c.sheet := c.contDiff_sheet.continuous

theorem w_eq_sheet_ζ {x : M} (hx : x ∈ c.orientedChartTube) : c.w x = c.sheet (c.ζ x) := by
  apply c.eq_of_parts
  · rw [c.negPart_sheet]
    have hk1 : c.d.k = 1 := c.hkq
    set i₀ : Fin c.d.k := ⟨0, by omega⟩ with hi₀
    have hi : ∀ i : Fin c.d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
    have hu : uq c.d.hk c.hkq (c.w x) = c.σ * Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2) := by
      have h := c.normSq_negPart_w hx.1
      rw [norm_negPart_sq c.d.hk c.hkq, ← c.ζ_def] at h
      have h2 : 0 < c.σ * uq c.d.hk c.hkq (c.w x) := hx.2
      have h3 : Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2) ^ 2 = 2 * c.ε₂ + ‖c.ζ x‖ ^ 2 :=
        Real.sq_sqrt (by have := c.ε₂_pos; positivity)
      have hσ := c.σ_sq
      have h4 : (uq c.d.hk c.hkq (c.w x) - c.σ * Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2)) *
          (uq c.d.hk c.hkq (c.w x) + c.σ * Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2)) = 0 := by
        have e : ∀ u s σ : ℝ, (u - σ * s) * (u + σ * s) = u ^ 2 - (σ * σ) * s ^ 2 :=
          fun _ _ _ => by ring
        rw [e, hσ, one_mul, h3, h]; ring
      rcases mul_eq_zero.1 h4 with h5 | h5
      · linarith
      · exfalso
        have : c.σ * uq c.d.hk c.hkq (c.w x) = -Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2) := by
          linear_combination c.σ * h5 - (Real.sqrt (2 * c.ε₂ + ‖c.ζ x‖ ^ 2)) * hσ
        linarith [Real.sqrt_pos.2 (by have := c.ε₂_pos; positivity :
          0 < 2 * c.ε₂ + ‖c.ζ x‖ ^ 2)]
    ext j
    rw [hi j]
    have e1 : negPart c.d.hk (c.w x) i₀ = uq c.d.hk c.hkq (c.w x) := rfl
    have e2 : negPart c.d.hk c.e₀' i₀ = uq c.d.hk c.hkq c.e₀' := rfl
    rw [PiLp.smul_apply, smul_eq_mul, e1, e2, c.uq_e₀', hu, mul_one]
  · rw [c.posPart_sheet, c.ζ_def]

def flowedSheet (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : M :=
  c.D.flow (c.c₂ - c.c₁) (c.d.χ (c.sheet v))

def pSheetCoordinates (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : Fin n → ℝ := c.e.χ.symm (c.flowedSheet v)

theorem morseNorm_sheet_lt {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    morseNorm n (c.sheet v) < c.D.rm q c.hq := by
  rw [← Real.sqrt_sq (ModelField.morseNorm_nonneg _), Real.sqrt_lt' c.rmq_pos,
    c.morseNorm_sheet_sq]
  have := c.ε₂_lt_ε; have := c.hrmq; have := c.hε
  linarith

theorem sheet_mem_ball {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.sheet v ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' :=
  mem_ball_of_morseNorm_lt ((c.morseNorm_sheet_lt hv).trans (c.D.rm_lt_R' q c.hq))

theorem f_chart_sheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    f (c.d.χ (c.sheet v)) = c.c₂ := by
  rw [c.d.hnorm _ ((c.morseNorm_sheet_lt hv).le.trans (c.D.hrm q c.hq).2), c.nf_sheet]

theorem c₁_mem_tube : c.c₁ ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η) :=
  ⟨by linarith [c.η_pos], by linarith [c.c₁_lt_c₂, c.η_pos]⟩

theorem f_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    f (c.flowedSheet v) = c.c₁ := by
  have h := c.f_flow_eq_sub_tube (x := c.d.χ (c.sheet v)) (T := c.c₂ - c.c₁)
    (by rw [c.f_chart_sheet hv]; exact Ioo_subset_Icc_self c.c₂_mem_tube)
    (by rw [c.f_chart_sheet hv, sub_sub_cancel]; exact c.c₁_mem_tube) _ right_mem_uIcc
  unfold flowedSheet
  rw [h, c.f_chart_sheet hv]; ring

theorem π_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.D.π c.c₂ (c.flowedSheet v) = c.d.χ (c.sheet v) := by
  unfold GradientLikeStrip.π
  rw [c.f_flowedSheet hv]
  unfold flowedSheet
  rw [flow_flow, show c.c₂ - c.c₁ + (c.c₁ - c.c₂) = 0 by ring, flow_zero]

theorem flowedSheet_mem_openChartTube {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.flowedSheet v ∈ c.openChartTube := by
  refine ⟨?_, ?_⟩
  · change f (c.flowedSheet v) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)
    rw [c.f_flowedSheet hv]
    exact ⟨by linarith [c.η_pos], by linarith [c.c₁_lt_c₂, c.η_pos]⟩
  · change c.D.π c.c₂ (c.flowedSheet v) ∈ c.qBall
    rw [c.π_flowedSheet hv]
    exact ⟨_, c.morseNorm_sheet_lt hv, rfl⟩

theorem w_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.w (c.flowedSheet v) = c.sheet v := by
  unfold w
  rw [c.π_flowedSheet hv, c.d.χ.left_inv (c.d.hball (c.sheet_mem_ball hv))]

theorem flowedSheet_mem_orientedChartTube {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.flowedSheet v ∈ c.orientedChartTube := by
  refine ⟨c.flowedSheet_mem_openChartTube hv, ?_⟩
  change 0 < c.σ * uq c.d.hk c.hkq (c.w (c.flowedSheet v))
  rw [c.w_flowedSheet hv]
  exact c.σ_uq_sheet_pos v

theorem ζ_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    c.ζ (c.flowedSheet v) = v := by
  rw [c.ζ_def, c.w_flowedSheet hv, c.posPart_sheet]

theorem levelDeformation_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) (r : ℝ) :
    c.levelDeformation r (c.flowedSheet v) = c.flowedSheet (Real.exp (-r) • v) := by
  unfold levelDeformation
  rw [c.f_flowedSheet hv, c.w_flowedSheet hv, c.lev_sheet]
  rfl

theorem flowedSheet_zero : c.flowedSheet 0 = c.D.flow (f q - c.ε - c.c₁) c.z₀ := by
  unfold flowedSheet
  rw [c.sheet_zero, c.chart_w c.z₀_mem_openChartTube, c.π_z₀, flow_flow]
  congr 1
  unfold c₂; ring

theorem s₀_ge : c.transitTime ≤ f q - c.ε - c.c₁ := by
  unfold transitTime c₁; linarith [c.ε₁_lt_ε]

theorem s₀_lt : f q - c.ε - c.c₁ < c.transitTime + (c.ε - c.e.r₀ ^ 2 / 2) := by
  unfold transitTime c₁; linarith [c.r₀p_sq_half_lt_ε₁]

theorem flowedSheet_zero_mem_pBall' : c.flowedSheet 0 ∈ c.pBall' := by
  rw [c.flowedSheet_zero]; exact c.flow_z₀_mem_pBall' c.s₀_ge

theorem two_ε₁_lt : 2 * c.ε₁ < 3 * c.ε := by linarith [c.ε₁_lt_ε, c.hε]

theorem flowedSheet_zero_eq : c.flowedSheet 0 = c.e.χ (Real.sqrt (2 * c.ε₁) • c.e₁) := by
  rw [c.flowedSheet_zero, c.flow_z₀_ray c.s₀_ge c.s₀_lt, c.y₀_eq, smul_smul]
  congr 2
  have h1 : 2 * c.ε - 2 * (f q - c.ε - c.c₁ - c.transitTime) = 2 * c.ε₁ := by unfold transitTime c₁; ring
  rw [h1, div_mul_cancel₀ _ c.sqrt_two_ε_pos.ne']

theorem pSheetCoordinates_zero : c.pSheetCoordinates 0 = Real.sqrt (2 * c.ε₁) • c.e₁ := by
  unfold pSheetCoordinates
  rw [c.flowedSheet_zero_eq]
  apply c.chart_p_symm_eq'
  rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, sq_abs,
    Real.sq_sqrt (by linarith [c.ε₁_pos])]
  exact c.two_ε₁_lt

theorem contMDiffAt_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) I ∞ c.flowedSheet v :=
  (c.D.contMDiff_flow (c.c₂ - c.c₁)).contMDiffAt.comp v
    ((c.d.contMDiffAt_chart (c.sheet_mem_ball hv)).comp v c.contDiff_sheet.contMDiff.contMDiffAt)

theorem continuousAt_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε) :
    ContinuousAt c.flowedSheet v :=
  (c.contMDiffAt_flowedSheet hv).continuousAt

theorem contDiffAt_pSheetCoordinates {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.e.χ '' Metric.ball 0 c.e.R') : ContDiffAt ℝ ∞ c.pSheetCoordinates v :=
  ((c.e.contMDiffAt_symm hH).comp v (c.contMDiffAt_flowedSheet hv)).contDiffAt

theorem chart_pSheetCoordinates {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hH : c.flowedSheet v ∈ c.pBall') :
    c.e.χ (c.pSheetCoordinates v) = c.flowedSheet v :=
  c.e.symm_image_eq (c.pBall'_subset_image_ball hH)

theorem pSheetCoordinates_sq_lt {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hH : c.flowedSheet v ∈ c.pBall') :
    morseNorm n (c.pSheetCoordinates v) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, hyx⟩ := hH
  have : c.pSheetCoordinates v = y := by unfold pSheetCoordinates; rw [← hyx, c.chart_p_symm_eq' hy]
  rw [this]; exact hy

theorem morseNorm_pSheetCoordinates_sq {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.pBall') : morseNorm n (c.pSheetCoordinates v) ^ 2 = 2 * c.ε₁ := by
  have h := c.f_chart_p ((c.morseNorm_lt_rmp_of_sq_lt (c.pSheetCoordinates_sq_lt hH)).le.trans (c.D.hrm p c.hp).2)
  rw [c.chart_pSheetCoordinates hH, c.f_flowedSheet hv] at h
  unfold c₁ at h; linarith

theorem pSheetCoordinates_ne_zero {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.pBall') : c.pSheetCoordinates v ≠ 0 := by
  intro h
  have := c.morseNorm_pSheetCoordinates_sq hv hH
  rw [h, morseNorm_zero] at this
  linarith [c.ε₁_pos]

theorem hasDerivAt_exp_smul (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    HasDerivAt (fun r : ℝ => Real.exp (-r) • v) (-v) 0 := by
  have := ((Real.hasDerivAt_exp (-0)).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).smul_const v
  refine this.congr_deriv ?_
  simp

theorem eventually_exp_smul_sq_lt {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hv : ‖v‖ ^ 2 < c.ε) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ‖Real.exp (-r) • v‖ ^ 2 < c.ε := by
  have hc : Continuous (fun r : ℝ => ‖Real.exp (-r) • v‖ ^ 2) :=
    ((Real.continuous_exp.comp continuous_neg).smul continuous_const).norm.pow 2
  have h0 : ‖Real.exp (-(0 : ℝ)) • v‖ ^ 2 < c.ε := by
    rw [neg_zero, Real.exp_zero, one_smul]; exact hv
  have := hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0)
  filter_upwards [this] with r hr
  exact hr

theorem pTransverseField_pSheetCoordinates {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.pBall') (hdiff : DifferentiableAt ℝ c.pSheetCoordinates v) :
    c.pTransverseField (c.pSheetCoordinates v) = -(fderiv ℝ c.pSheetCoordinates v v) := by
  have h1 : HasDerivAt (fun r => c.e.χ.symm (c.levelDeformation r (c.e.χ (c.pSheetCoordinates v)))) (c.pTransverseField (c.pSheetCoordinates v)) 0 :=
    c.hasDerivAt_symm_levelDeformation_p (c.morseNorm_lt_rmp_of_sq_lt (c.pSheetCoordinates_sq_lt hH))
      (by rw [c.chart_pSheetCoordinates hH]; exact c.flowedSheet_mem_openChartTube hv)
  have h2 : (fun r => c.pSheetCoordinates (Real.exp (-r) • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => c.e.χ.symm (c.levelDeformation r (c.e.χ (c.pSheetCoordinates v)))) := by
    filter_upwards [c.eventually_exp_smul_sq_lt hv] with r hr
    rw [c.chart_pSheetCoordinates hH, c.levelDeformation_flowedSheet hv]
    rfl
  have h3 : HasDerivAt (fun r => c.pSheetCoordinates (Real.exp (-r) • v)) (c.pTransverseField (c.pSheetCoordinates v)) 0 :=
    h1.congr_of_eventuallyEq h2
  have hf' : HasFDerivAt c.pSheetCoordinates (fderiv ℝ c.pSheetCoordinates v) (Real.exp (-0) • v) := by
    rw [neg_zero, Real.exp_zero, one_smul]; exact hdiff.hasFDerivAt
  have h4 : HasDerivAt (c.pSheetCoordinates ∘ fun r => Real.exp (-r) • v) (fderiv ℝ c.pSheetCoordinates v (-v)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) hf' (c.hasDerivAt_exp_smul v)
  rw [h3.unique h4, map_neg]

def sheetProjection (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n - c.d.k)) :=
  posPart c.d.hk (c.d.χ.symm (c.D.flow (c.c₁ - c.c₂) (c.e.χ y)))

theorem flow_flowedSheet {v : EuclideanSpace ℝ (Fin (n - c.d.k))} :
    c.D.flow (c.c₁ - c.c₂) (c.flowedSheet v) = c.d.χ (c.sheet v) := by
  unfold flowedSheet
  rw [flow_flow, show c.c₂ - c.c₁ + (c.c₁ - c.c₂) = 0 by ring, flow_zero]

theorem sheetProjection_pSheetCoordinates {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.pBall') : c.sheetProjection (c.pSheetCoordinates v) = v := by
  unfold sheetProjection
  rw [c.chart_pSheetCoordinates hH, c.flow_flowedSheet, c.d.χ.left_inv (c.d.hball (c.sheet_mem_ball hv)),
    c.posPart_sheet]

theorem contDiffAt_sheetProjection {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε)
    (hH : c.flowedSheet v ∈ c.pBall') : ContDiffAt ℝ ∞ c.sheetProjection (c.pSheetCoordinates v) := by
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ c.e.χ (c.pSheetCoordinates v) :=
    c.e.contMDiffAt_chart (c.mem_ball_p_of_sq_lt (c.pSheetCoordinates_sq_lt hH))
  have h2 : ContMDiffAt I I ∞ (c.D.flow (c.c₁ - c.c₂)) (c.e.χ (c.pSheetCoordinates v)) :=
    (c.D.contMDiff_flow _).contMDiffAt
  have h3 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.d.χ.symm
      (c.D.flow (c.c₁ - c.c₂) (c.e.χ (c.pSheetCoordinates v))) := by
    apply c.d.contMDiffAt_symm
    rw [c.chart_pSheetCoordinates hH, c.flow_flowedSheet]
    exact mem_image_of_mem _ (c.sheet_mem_ball hv)
  have h4 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) ∞
      (posPart c.d.hk) (c.d.χ.symm (c.D.flow (c.c₁ - c.c₂) (c.e.χ (c.pSheetCoordinates v)))) :=
    (ModelField.posPartL c.d.hk).contDiff.contMDiff.contMDiffAt
  have : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) ∞
      (posPart c.d.hk ∘ (c.d.χ.symm ∘ (c.D.flow (c.c₁ - c.c₂) ∘ c.e.χ))) (c.pSheetCoordinates v) :=
    h4.comp (c.pSheetCoordinates v) (h3.comp (c.pSheetCoordinates v) (h2.comp (c.pSheetCoordinates v) h1))
  exact this.contDiffAt

theorem exists_r₁ : ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)),
    ‖v‖ < r₁ →
    ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall' ∧ 0 < axial c.e₁ (c.pSheetCoordinates v) := by
  have hv0 : ‖(0 : EuclideanSpace ℝ (Fin (n - c.d.k)))‖ ^ 2 < c.ε := by simpa using c.hε
  have hH0 := c.flowedSheet_zero_mem_pBall'
  have h1 : {v : EuclideanSpace ℝ (Fin (n - c.d.k)) | c.flowedSheet v ∈ c.pBall'} ∈ 𝓝 0 :=
    (c.continuousAt_flowedSheet hv0).preimage_mem_nhds (c.isOpen_pBall'.mem_nhds hH0)
  have hG : ContinuousAt c.pSheetCoordinates 0 :=
    (c.contDiffAt_pSheetCoordinates hv0 (c.pBall'_subset_image_ball hH0)).continuousAt
  have hax0 : 0 < axial c.e₁ (c.pSheetCoordinates 0) := by
    rw [c.pSheetCoordinates_zero, axial_smul_self c.morseNorm_e₁]
    exact Real.sqrt_pos.2 (by linarith [c.ε₁_pos])
  have h2 : {v : EuclideanSpace ℝ (Fin (n - c.d.k)) | 0 < axial c.e₁ (c.pSheetCoordinates v)} ∈ 𝓝 0 :=
    ((continuous_axial c.e₁).continuousAt.comp hG).preimage_mem_nhds (isOpen_Ioi.mem_nhds hax0)
  have h3 : {v : EuclideanSpace ℝ (Fin (n - c.d.k)) | ‖v‖ ^ 2 < c.ε} ∈ 𝓝 0 :=
    (continuous_norm.pow 2).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hv0)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem h3 h1) h2)
  refine ⟨r₁, hr₁, fun v hv => ?_⟩
  have := hball (show v ∈ Metric.ball 0 r₁ by simpa using hv)
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem axial_fderiv_pSheetCoordinates_zero {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hgood : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ < r₁ →
      ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall' ∧ 0 < axial c.e₁ (c.pSheetCoordinates v))
    (w : EuclideanSpace ℝ (Fin (n - c.d.k))) : axial c.e₁ (fderiv ℝ c.pSheetCoordinates 0 w) = 0 := by
  have h0 := hgood 0 (by simpa using hr₁)
  have hdiff : DifferentiableAt ℝ c.pSheetCoordinates 0 :=
    (c.contDiffAt_pSheetCoordinates h0.1 (c.pBall'_subset_image_ball h0.2.1)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => c.pSheetCoordinates (t • w)) (fderiv ℝ c.pSheetCoordinates 0 w) 0 := by
    have hf' : HasFDerivAt c.pSheetCoordinates (fderiv ℝ c.pSheetCoordinates 0) ((0 : ℝ) • w) := by
      rw [zero_smul]; exact hdiff.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      have := (hasDerivAt_id (0 : ℝ)).smul_const w
      simpa using this
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hf' hl
  have h1 := ModelField.hasDerivAt_morseNorm_sq_half hcurve
  rw [zero_smul] at h1
  have h2 : HasDerivAt (fun t : ℝ => morseNorm n (c.pSheetCoordinates (t • w)) ^ 2 / 2) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) c.ε₁).congr_of_eventuallyEq ?_
    have hc : Continuous (fun t : ℝ => t • w) := by fun_prop
    have hmem : {t : ℝ | ‖t • w‖ < r₁} ∈ 𝓝 (0 : ℝ) :=
      (hc.norm.continuousAt).preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa using hr₁))
    filter_upwards [hmem] with t ht
    have := hgood (t • w) ht
    rw [c.morseNorm_pSheetCoordinates_sq this.1 this.2.1]; ring
  have h := h1.unique h2
  rw [← dot_eq_sum, c.pSheetCoordinates_zero, dot_smul_left] at h
  have hs : Real.sqrt (2 * c.ε₁) ≠ 0 := Real.sqrt_ne_zero'.2 (by linarith [c.ε₁_pos])
  rw [axial, dot_comm]
  exact (mul_eq_zero.1 h).resolve_left hs

theorem fderiv_pSheetCoordinates_zero_injective {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hgood : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ < r₁ →
      ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall' ∧ 0 < axial c.e₁ (c.pSheetCoordinates v)) :
    Function.Injective (fderiv ℝ c.pSheetCoordinates 0) := by
  have h0 := hgood 0 (by simpa using hr₁)
  have hdiff : DifferentiableAt ℝ c.pSheetCoordinates 0 :=
    (c.contDiffAt_pSheetCoordinates h0.1 (c.pBall'_subset_image_ball h0.2.1)).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ c.sheetProjection (c.pSheetCoordinates 0) :=
    (c.contDiffAt_sheetProjection h0.1 h0.2.1).differentiableAt (by simp)
  have hcomp : HasFDerivAt (c.sheetProjection ∘ c.pSheetCoordinates)
      ((fderiv ℝ c.sheetProjection (c.pSheetCoordinates 0)).comp (fderiv ℝ c.pSheetCoordinates 0)) 0 :=
    hQ.hasFDerivAt.comp 0 hdiff.hasFDerivAt
  have hid : HasFDerivAt (c.sheetProjection ∘ c.pSheetCoordinates) (ContinuousLinearMap.id ℝ _) 0 := by
    refine (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin (n - c.d.k)))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin (n - c.d.k))) hr₁] with v hv
    have := hgood v (by simpa using hv)
    exact c.sheetProjection_pSheetCoordinates this.1 this.2.1
  have heq := hcomp.unique hid
  intro a b hab
  have ha := DFunLike.congr_fun heq a
  have hb := DFunLike.congr_fun heq b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
  rw [← ha, ← hb, hab]

def perpL (e₁ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.id ℝ _ - (dotL e₁).smulRight e₁

theorem perpL_apply (e₁ w : Fin n → ℝ) : perpL e₁ w = perp e₁ w := by
  simp [perpL, perp, axial, dotL_apply, dot_comm]

theorem hasFDerivAt_perp (e₁ y : Fin n → ℝ) : HasFDerivAt (perp e₁) (perpL e₁) y := by
  have := (hasFDerivAt_id y).sub ((hasFDerivAt_axial e₁ y).smul_const e₁)
  exact this

theorem contDiff_perp (e₁ : Fin n → ℝ) : ContDiff ℝ ∞ (perp e₁) :=
  contDiff_id.sub ((contDiff_axial e₁).smul contDiff_const)

def transverseSheetMap (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (perp c.e₁ (c.pSheetCoordinates v))

theorem transverseSheetMap_zero : c.transverseSheetMap 0 = 0 := by
  unfold transverseSheetMap
  rw [c.pSheetCoordinates_zero, perp_smul_self c.morseNorm_e₁, map_zero]

theorem hasFDerivAt_transverseSheetMap {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hdiff : DifferentiableAt ℝ c.pSheetCoordinates v) :
    HasFDerivAt c.transverseSheetMap ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
      ((perpL c.e₁).comp (fderiv ℝ c.pSheetCoordinates v))) v :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm.hasFDerivAt.comp v
    ((hasFDerivAt_perp c.e₁ (c.pSheetCoordinates v)).comp v hdiff.hasFDerivAt))

theorem fderiv_transverseSheetMap_apply {v : EuclideanSpace ℝ (Fin (n - c.d.k))}
    (hdiff : DifferentiableAt ℝ c.pSheetCoordinates v) (w : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    fderiv ℝ c.transverseSheetMap v w =
      (EuclideanSpace.equiv (Fin n) ℝ).symm (perp c.e₁ (fderiv ℝ c.pSheetCoordinates v w)) := by
  rw [(c.hasFDerivAt_transverseSheetMap hdiff).fderiv]
  simp [perpL_apply]

theorem inner_transverseSheetMap {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hdiff : DifferentiableAt ℝ c.pSheetCoordinates v)
    (w : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    ⟪c.transverseSheetMap v, fderiv ℝ c.transverseSheetMap v w⟫ =
      dot (perp c.e₁ (c.pSheetCoordinates v)) (perp c.e₁ (fderiv ℝ c.pSheetCoordinates v w)) := by
  rw [c.fderiv_transverseSheetMap_apply hdiff]
  rfl

theorem dot_decomp {e₁ : Fin n → ℝ} (he₁ : morseNorm n e₁ = 1) (y z : Fin n → ℝ) :
    dot y z = dot (perp e₁ y) (perp e₁ z) + axial e₁ y * axial e₁ z := by
  simp only [perp, dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right, dot_self, he₁]
  simp only [axial, dot_comm y e₁, dot_comm z e₁]
  ring

theorem axialDefectDeriv_smul {e₁ : Fin n → ℝ} {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ} (hy : y ≠ 0)
    (w : Fin n → ℝ) : axialDefectDeriv e₁ (t • y) (t • w) = axialDefectDeriv e₁ y w := by
  have hρ := morseNorm_pos hy
  rw [axialDefectDeriv_apply, axialDefectDeriv_apply, axial_smul, dot_smul_left, dot_smul_right, dot_smul_right,
    morseNorm_smul, abs_of_pos ht]
  field_simp

theorem exists_dB_neg_level : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)),
    v ≠ 0 → ‖v‖ < δ₀ → ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall' ∧
      axialDefectDeriv c.e₁ (c.pSheetCoordinates v) (c.pTransverseField (c.pSheetCoordinates v)) < 0 := by
  obtain ⟨r₁, hr₁, hgood⟩ := c.exists_r₁
  have he₁ := c.morseNorm_e₁
  have hdiffAt : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ < r₁ →
      DifferentiableAt ℝ c.pSheetCoordinates v := fun v hv =>
    (c.contDiffAt_pSheetCoordinates (hgood v hv).1
      (c.pBall'_subset_image_ball (hgood v hv).2.1)).differentiableAt (by simp)
  have hP : ContDiffOn ℝ 1 c.transverseSheetMap (Metric.ball 0 r₁) := by
    intro v hv
    have hv' : ‖v‖ < r₁ := by simpa using hv
    have hG : ContDiffAt ℝ ∞ c.pSheetCoordinates v :=
      c.contDiffAt_pSheetCoordinates (hgood v hv').1 (c.pBall'_subset_image_ball (hgood v hv').2.1)
    have : ContDiffAt ℝ ∞ c.transverseSheetMap v :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt.comp v
        ((contDiff_perp c.e₁).contDiffAt.comp v hG)
    exact (this.of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hinj : Function.Injective (fderiv ℝ c.transverseSheetMap 0) := by
    intro a b hab
    rw [c.fderiv_transverseSheetMap_apply (hdiffAt 0 (by simpa using hr₁)),
      c.fderiv_transverseSheetMap_apply (hdiffAt 0 (by simpa using hr₁))] at hab
    have h1 := (EuclideanSpace.equiv (Fin n) ℝ).symm.injective hab
    have hperp : ∀ w, perp c.e₁ (fderiv ℝ c.pSheetCoordinates 0 w) = fderiv ℝ c.pSheetCoordinates 0 w := fun w => by
      rw [perp, c.axial_fderiv_pSheetCoordinates_zero hr₁ hgood, zero_smul, sub_zero]
    rw [hperp, hperp] at h1
    exact c.fderiv_pSheetCoordinates_zero_injective hr₁ hgood h1
  obtain ⟨δ₀, hδ₀, hpos⟩ :=
    CancelModel.exists_pos_inner_of_injective hr₁ hP c.transverseSheetMap_zero hinj
  refine ⟨min δ₀ r₁, lt_min hδ₀ hr₁, fun v hv hvδ => ?_⟩
  have hv1 : ‖v‖ < δ₀ := hvδ.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < r₁ := hvδ.trans_le (min_le_right _ _)
  obtain ⟨hvε, hH, hax⟩ := hgood v hv2
  refine ⟨hvε, hH, ?_⟩
  have hdiff := hdiffAt v hv2
  have hin := hpos v hv hv1
  rw [c.inner_transverseSheetMap hdiff] at hin
  set y := c.pSheetCoordinates v with hy
  have hy0 : y ≠ 0 := c.pSheetCoordinates_ne_zero hvε hH
  have hZ : c.pTransverseField y = -(fderiv ℝ c.pSheetCoordinates v v) := c.pTransverseField_pSheetCoordinates hvε hH hdiff
  have horth : dot y (c.pTransverseField y) = 0 := by
    rw [dot_eq_sum]
    exact c.transverseField_chart_p_orth (c.morseNorm_lt_rmp_of_sq_lt (c.pSheetCoordinates_sq_lt hH))
      (by rw [hy, c.chart_pSheetCoordinates hH]; exact c.flowedSheet_mem_openChartTube hvε)
  have hdec := dot_decomp he₁ y (c.pTransverseField y)
  have hperpZ : dot (perp c.e₁ y) (perp c.e₁ (c.pTransverseField y)) =
      -dot (perp c.e₁ y) (perp c.e₁ (fderiv ℝ c.pSheetCoordinates v v)) := by
    rw [hZ, perp_neg, dot_neg_right]
  have haxZ : 0 < axial c.e₁ (c.pTransverseField y) := by
    have : axial c.e₁ y * axial c.e₁ (c.pTransverseField y) =
        dot (perp c.e₁ y) (perp c.e₁ (fderiv ℝ c.pSheetCoordinates v v)) := by linarith
    have hprod : 0 < axial c.e₁ y * axial c.e₁ (c.pTransverseField y) := by rw [this]; exact hin
    exact pos_of_mul_pos_right hprod hax.le
  have hρ := morseNorm_pos hy0
  rw [axialDefectDeriv_apply, horth, mul_zero, zero_sub, neg_lt_zero]
  have : dot c.e₁ (c.pTransverseField y) = axial c.e₁ (c.pTransverseField y) := by rw [axial, dot_comm]
  rw [this]
  exact mul_pos (inv_pos.2 hρ) haxZ

theorem flowedSheet_ζ {x : M} (hx : x ∈ c.orientedChartTube) (hv : ‖c.ζ x‖ ^ 2 < c.ε) :
    c.flowedSheet (c.ζ x) = c.D.flow (f x - c.c₁) x := by
  have _ := hv
  unfold flowedSheet
  rw [← c.w_eq_sheet_ζ hx, c.chart_w hx.1]
  unfold GradientLikeStrip.π
  rw [flow_flow]
  congr 1; ring

theorem ne_zero_of_mem_openChartTube {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hx : c.e.χ y ∈ c.openChartTube) : y ≠ 0 := by
  rintro rfl
  have h1 := hx.1.1
  rw [c.f_chart_p ((c.morseNorm_lt_rmp_of_sq_lt hy).le.trans (c.D.hrm p c.hp).2),
    morseNorm_zero] at h1
  have := c.f_p_add_lt_c₁_sub_η
  nlinarith [sq_nonneg c.e.r₀]

theorem exists_dB_neg : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ y : Fin n → ℝ, morseNorm n y ^ 2 < 3 * c.ε →
    c.e.χ y ∈ c.orientedChartTube → 0 < ‖c.ζ (c.e.χ y)‖ → ‖c.ζ (c.e.χ y)‖ < δ₀ →
    axialDefectDeriv c.e₁ y (c.pTransverseField y) < 0 := by
  obtain ⟨δ₀, hδ₀, hmain⟩ := c.exists_dB_neg_level
  refine ⟨δ₀, hδ₀, fun y hy hx hζ0 hζδ => ?_⟩
  set v := c.ζ (c.e.χ y) with hvdef
  have hv0 : v ≠ 0 := norm_pos_iff.1 hζ0
  obtain ⟨hvε, hH, hB⟩ := hmain v hv0 hζδ
  have hHx : c.flowedSheet v = c.D.flow (f (c.e.χ y) - c.c₁) (c.e.χ y) := c.flowedSheet_ζ hx hvε
  set y' := c.pSheetCoordinates v with hy'def
  have hy' : c.e.χ y' = c.flowedSheet v := c.chart_pSheetCoordinates hH
  have hy'sq : morseNorm n y' ^ 2 < 3 * c.ε := c.pSheetCoordinates_sq_lt hH
  have hy'rm := c.morseNorm_lt_rmp_of_sq_lt hy'sq
  have hyrm := c.morseNorm_lt_rmp_of_sq_lt hy
  have hxT : c.e.χ y ∈ c.openChartTube := hx.1
  have hx'T : c.e.χ y' ∈ c.openChartTube := by rw [hy']; exact c.flowedSheet_mem_openChartTube hvε
  have hy0 : y ≠ 0 := c.ne_zero_of_mem_openChartTube hy hxT
  have hy'0 : y' ≠ 0 := c.pSheetCoordinates_ne_zero hvε hH
  have hyb := c.mem_ball_p_of_sq_lt hy
  have hy'b := c.mem_ball_p_of_sq_lt hy'sq
  rcases le_or_gt c.c₁ (f (c.e.χ y)) with hle | hlt
  · obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hyrm
      (t := f (c.e.χ y) - c.c₁) (by linarith)
    have hly : y' = l • y := by
      apply c.e.χ.injOn (c.e.hball hy'b) (c.e.hball (mem_ball_of_morseNorm_lt (by
        rw [ModelField.morseNorm_smul, abs_of_pos hl0]
        have := ModelField.morseNorm_nonneg y; have := c.D.rm_lt_R' p c.hp; nlinarith)))
      rw [hy', hHx, hl]
    have hZ : c.pTransverseField (l • y) = l • c.pTransverseField y :=
      c.transverseField_chart_p_smul hyrm hxT hl0 hl1 (by rw [← hly]; exact hx'T)
    rw [← axialDefectDeriv_smul hl0 hy0 (c.pTransverseField y), ← hZ, ← hly]
    exact hB
  · obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hy'rm
      (t := c.c₁ - f (c.e.χ y)) (by linarith)
    have hflow : c.D.flow (c.c₁ - f (c.e.χ y)) (c.e.χ y') = c.e.χ y := by
      rw [hy', hHx, flow_flow, show f (c.e.χ y) - c.c₁ + (c.c₁ - f (c.e.χ y)) = 0 by ring,
        flow_zero]
    have hly : y = l • y' := by
      apply c.e.χ.injOn (c.e.hball hyb) (c.e.hball (mem_ball_of_morseNorm_lt (by
        rw [ModelField.morseNorm_smul, abs_of_pos hl0]
        have := ModelField.morseNorm_nonneg y'; have := c.D.rm_lt_R' p c.hp; nlinarith)))
      rw [← hflow, hl]
    have hZ : c.pTransverseField (l • y') = l • c.pTransverseField y' :=
      c.transverseField_chart_p_smul hy'rm hx'T hl0 hl1 (by rw [← hly]; exact hxT)
    rw [hly, hZ, axialDefectDeriv_smul hl0 hy'0]
    exact hB

theorem mem_orientedChartTube_of_flow {x : M} (hx : f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) {s : ℝ}
    (hs : c.D.flow s x ∈ c.orientedChartTube) : x ∈ c.orientedChartTube ∧ c.ζ x = c.ζ (c.D.flow s x) := by
  have hπ : c.D.π c.c₂ (c.D.flow s x) = c.D.π c.c₂ x :=
    c.π_flow_eq (c.mem_regularFlowDomain_of_f_mem hx) (c.openChartTube_subset_regularFlowDomain hs.1)
  have hw : c.w (c.D.flow s x) = c.w x := by unfold w; rw [hπ]
  refine ⟨⟨⟨hx, ?_⟩, ?_⟩, ?_⟩
  · change c.D.π c.c₂ x ∈ c.qBall
    rw [← hπ]; exact hs.1.2
  · change 0 < c.σ * uq c.d.hk c.hkq (c.w x)
    rw [← hw]; exact hs.2
  · rw [c.ζ_def, c.ζ_def, hw]

theorem ρA_sq_lt : c.ρA ^ 2 < 3 * c.ε := by
  have := c.ρA_lt_ρB; have := c.ρB_sq_lt; have := c.ρA_pos; have := c.hε
  nlinarith

theorem exists_cone_ball {δ' : ℝ} (hδ' : 0 < δ') : ∃ r : ℝ, 0 < r ∧ ∀ y : Fin n → ℝ,
    morseNorm n (y - c.ρA • c.e₁) < r →
      c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < δ' := by
  set U : Set (Fin n → ℝ) := Metric.ball 0 c.e.R' ∩ c.e.χ ⁻¹' c.orientedChartTube with hU
  have hUo : IsOpen U :=
    (c.e.χ.continuousOn.mono c.e.hball).isOpen_inter_preimage Metric.isOpen_ball
      c.isOpen_orientedChartTube
  have hζc : ContinuousOn (fun y => ‖c.ζ (c.e.χ y)‖) U :=
    (c.continuousOn_ζ.comp (c.e.χ.continuousOn.mono (inter_subset_left.trans c.e.hball))
      fun y hy => hy.2.1).norm
  set U' := U ∩ (fun y => ‖c.ζ (c.e.χ y)‖) ⁻¹' Iio δ' with hU'
  have hU'o : IsOpen U' := hζc.isOpen_inter_preimage hUo isOpen_Iio
  have hmem : c.ρA • c.e₁ ∈ U' := by
    have hρ := c.ρA_pos
    have hnorm : morseNorm n (c.ρA • c.e₁) = c.ρA := by
      rw [ModelField.morseNorm_smul, c.morseNorm_e₁, mul_one, abs_of_pos hρ]
    have hsq : morseNorm n (c.ρA • c.e₁) ^ 2 < 3 * c.ε := by rw [hnorm]; exact c.ρA_sq_lt
    have hax := c.axis_p_mem_orientedChartTube c.r₀p_lt_ρA c.ρA_sq_lt (by
      rw [c.f_chart_p ((c.morseNorm_lt_rmp_of_sq_lt hsq).le.trans (c.D.hrm p c.hp).2), hnorm]
      have e1 := c.ρA_sq_eq
      have := c.lo₁_lt_lo₂; have := c.lo₂_lt_hi₁; have := c.hi₁_lt_hi₂; have := c.η_pos
      unfold lo₁ hi₂ at *
      constructor <;> linarith)
    refine ⟨⟨c.mem_ball_p_of_sq_lt hsq, hax.1⟩, ?_⟩
    change ‖c.ζ (c.e.χ (c.ρA • c.e₁))‖ < δ'
    rw [hax.2, norm_zero]; exact hδ'
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU'o _ hmem
  refine ⟨r, hr, fun y hy => ?_⟩
  have hyU : y ∈ U' := hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact (DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_piNorm_le _).trans_lt hy)
  exact ⟨hyU.1.2, hyU.2⟩

theorem cone_of_ball {δ' r τ δ : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin n → ℝ, morseNorm n (y - c.ρA • c.e₁) < r →
      c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < δ')
    (hsmall : 2 * c.ρA ^ 2 * τ ^ 2 + 4 * δ ^ 2 < r ^ 2) (y : Fin n → ℝ)
    (h1 : c.ρA ≤ morseNorm n y) (h2 : morseNorm n y ≤ c.ρB)
    (h3 : perpSq c.e₁ y < (τ ^ 2 + 2 * δ ^ 2 / c.ρA ^ 2) * morseNorm n y ^ 2)
    (h4 : 0 < axial c.e₁ y) : c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < δ' := by
  have he₁ := c.morseNorm_e₁
  have hρ := c.ρA_pos
  set N := morseNorm n y with hN
  have hN0 : 0 < N := hρ.trans_le h1
  set a := axial c.e₁ y with ha
  set y' := (c.ρA / N) • y with hy'
  have hy'ball : morseNorm n (y' - c.ρA • c.e₁) < r := by
    have hsq : morseNorm n (y' - c.ρA • c.e₁) ^ 2 = 2 * c.ρA ^ 2 * (1 - a / N) := by
      rw [← dot_self, dot_sub_left, dot_sub_right, dot_sub_right, hy', dot_smul_left,
        dot_smul_left, dot_smul_right, dot_smul_right, dot_smul_right, dot_smul_left, dot_self,
        dot_self, ModelField.morseNorm_smul, abs_of_pos hρ, he₁, ← hN, ha, axial,
        dot_comm y c.e₁]
      field_simp
      ring
    have hperp : perpSq c.e₁ y = N ^ 2 - a ^ 2 := by rw [perpSq, ← hN, ← ha]
    have haN : a ≤ N :=
      (pow_le_pow_iff_left₀ h4.le hN0.le two_ne_zero).1 (axial_sq_le he₁ y)
    have hle : 1 - a / N ≤ perpSq c.e₁ y / N ^ 2 := by
      rw [hperp, le_div_iff₀ (by positivity)]
      have e : (1 - a / N) * N ^ 2 = N ^ 2 - a * N := by field_simp
      rw [e]
      nlinarith
    have hlt : perpSq c.e₁ y / N ^ 2 < τ ^ 2 + 2 * δ ^ 2 / c.ρA ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]; exact h3
    have h5 : morseNorm n (y' - c.ρA • c.e₁) ^ 2 < r ^ 2 := by
      rw [hsq]
      have : 2 * c.ρA ^ 2 * (τ ^ 2 + 2 * δ ^ 2 / c.ρA ^ 2) =
          2 * c.ρA ^ 2 * τ ^ 2 + 4 * δ ^ 2 := by
        field_simp; ring
      nlinarith [mul_lt_mul_of_pos_left (hle.trans_lt hlt)
        (by positivity : (0:ℝ) < 2 * c.ρA ^ 2)]
    exact (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg _) hr.le two_ne_zero).1 h5
  obtain ⟨hT', hζ'⟩ := hball y' hy'ball
  have hysq : morseNorm n y ^ 2 < 3 * c.ε := by
    have := c.ρB_sq_lt; have := c.hε
    nlinarith [pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) h2 2]
  have hyrm := c.morseNorm_lt_rmp_of_sq_lt hysq
  have hyR : morseNorm n y ≤ c.e.R := hyrm.le.trans (c.D.hrm p c.hp).2
  have hfx : f (c.e.χ y) = f p + N ^ 2 / 2 := by rw [c.f_chart_p hyR]
  have hlev : f (c.e.χ y) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
    rw [hfx]
    have e1 := c.ρA_sq_eq; have e2 := c.ρB_sq_eq
    have h5 : c.ρA ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hρ.le h1 2
    have h6 : N ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ hN0.le h2 2
    have := c.η_pos; have := c.lo₂_lt_hi₁
    unfold lo₁ lo₂ hi₁ at *
    constructor <;> linarith
  set s := f (c.e.χ y) - c.lo₁ with hs
  have hs0 : 0 ≤ s := by
    rw [hs, hfx]
    have := c.ρA_sq_eq
    have h5 : c.ρA ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hρ.le h1 2
    linarith
  obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hyrm hs0
  have hflev : f (c.D.flow s (c.e.χ y)) = c.lo₁ := by
    have := c.f_flow_eq_sub_tube (x := c.e.χ y) (Ioo_subset_Icc_self hlev) (T := s)
      (by rw [hs, sub_sub_cancel]; have := c.η_pos; unfold lo₁
          exact ⟨by linarith, by linarith [c.c₁_lt_c₂]⟩) s right_mem_uIcc
    rw [this, hs]; ring
  have hly : l • y = y' := by
    rw [hl] at hflev
    have hlyR : morseNorm n (l • y) ≤ c.e.R := by
      rw [ModelField.morseNorm_smul, abs_of_pos hl0]
      nlinarith [ModelField.morseNorm_nonneg y]
    rw [c.f_chart_p hlyR, ModelField.morseNorm_smul, abs_of_pos hl0, ← hN] at hflev
    have hlN : l * N = c.ρA := by
      have h5 : (l * N) ^ 2 = c.ρA ^ 2 := by have := c.ρA_sq_eq; linarith
      exact (sq_eq_sq₀ (by positivity) hρ.le).1 h5
    rw [hy']
    congr 1
    rw [← hlN]; field_simp
  have hflow : c.D.flow s (c.e.χ y) = c.e.χ y' := by rw [hl, hly]
  have key := c.mem_orientedChartTube_of_flow hlev (s := s) (by rw [hflow]; exact hT')
  refine ⟨key.1, ?_⟩
  rw [key.2, hflow]; exact hζ'

theorem exists_cancelConsts : Nonempty c.CancelConsts := by
  obtain ⟨δ₀, hδ₀, hdB⟩ := c.exists_dB_neg
  have hε := c.hε
  set δ' := min (δ₀ / 2) (Real.sqrt c.ε / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'δ₀ : δ' < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hδ'ε : δ' ^ 2 < c.ε := by
    have h1 : δ' ≤ Real.sqrt c.ε / 2 := min_le_right _ _
    have h2 : Real.sqrt c.ε ^ 2 = c.ε := Real.sq_sqrt hε.le
    nlinarith [Real.sqrt_nonneg c.ε]
  obtain ⟨r, hr, hball⟩ := c.exists_cone_ball hδ'
  have hρ := c.ρA_pos
  set τ := min (1 / 2) (r / (4 * c.ρA)) with hτdef
  set δ := min (δ' / 3) (r / 8) with hδdef
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hτ1 : τ ^ 2 ≤ 1 / 4 := by
    have : τ ≤ 1 / 2 := min_le_left _ _
    nlinarith
  have hδδ' : 2 * δ < δ' := by
    have : δ ≤ δ' / 3 := min_le_left _ _
    linarith
  have hsmall : 2 * c.ρA ^ 2 * τ ^ 2 + 4 * δ ^ 2 < r ^ 2 := by
    have h1 : τ ≤ r / (4 * c.ρA) := min_le_right _ _
    have h2 : δ ≤ r / 8 := min_le_right _ _
    have h3 : τ ^ 2 ≤ (r / (4 * c.ρA)) ^ 2 := pow_le_pow_left₀ hτ.le h1 2
    have h4 : δ ^ 2 ≤ (r / 8) ^ 2 := pow_le_pow_left₀ hδ.le h2 2
    have h5 : 2 * c.ρA ^ 2 * (r / (4 * c.ρA)) ^ 2 = r ^ 2 / 8 := by field_simp; ring
    have h6 : 2 * c.ρA ^ 2 * τ ^ 2 ≤ r ^ 2 / 8 := by
      rw [← h5]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  exact ⟨⟨δ, δ', τ, hδ, hδδ', hδ'ε, hτ, hτ1,
    fun y hy hx hζ0 hζδ => hdB y hy hx hζ0 (hζδ.trans hδ'δ₀),
    fun y h1 h2 h3 h4 => c.cone_of_ball hr hball hsmall y h1 h2 h3 h4⟩⟩

end Holonomy

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
