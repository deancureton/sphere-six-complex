module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelFlowP

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

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

def qNormProductSq (y : Fin n → ℝ) : ℝ := ‖negPart c.d.hk y‖ ^ 2 * ‖posPart c.d.hk y‖ ^ 2

theorem qNormProductSq_nonneg (y : Fin n → ℝ) : 0 ≤ c.qNormProductSq y := by unfold qNormProductSq; positivity

theorem qNormProductSq_eq_uq (y : Fin n → ℝ) : c.qNormProductSq y = uq c.d.hk c.hkq y ^ 2 * ‖posPart c.d.hk y‖ ^ 2 := by
  unfold qNormProductSq; rw [norm_negPart_sq c.d.hk c.hkq]

theorem continuous_qNormProductSq : Continuous c.qNormProductSq :=
  ((ModelField.negPartL c.d.hk).continuous.norm.pow 2).mul
    ((ModelField.posPartL c.d.hk).continuous.norm.pow 2)

def rζ (y : Fin n → ℝ) : ℝ := -c.ε₂ + Real.sqrt (c.ε₂ ^ 2 + c.qNormProductSq y)

theorem rζ_nonneg (y : Fin n → ℝ) : 0 ≤ c.rζ y := by
  unfold rζ
  have h1 : c.ε₂ ≤ Real.sqrt (c.ε₂ ^ 2 + c.qNormProductSq y) := by
    rw [Real.le_sqrt c.ε₂_pos.le (add_nonneg (sq_nonneg _) (c.qNormProductSq_nonneg y))]
    linarith [c.qNormProductSq_nonneg y]
  linarith

theorem rζ_mul (y : Fin n → ℝ) : c.rζ y * (2 * c.ε₂ + c.rζ y) = c.qNormProductSq y := by
  unfold rζ
  have h := Real.sq_sqrt (add_nonneg (sq_nonneg c.ε₂) (c.qNormProductSq_nonneg y))
  nlinarith [h]

theorem rζ_eq_of {y : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : r * (2 * c.ε₂ + r) = c.qNormProductSq y) :
    r = c.rζ y := by
  have h1 := c.rζ_mul y
  have h2 := c.rζ_nonneg y
  have h3 := c.ε₂_pos
  nlinarith

theorem continuous_rζ : Continuous c.rζ :=
  continuous_const.add ((continuous_const.add c.continuous_qNormProductSq).sqrt)

theorem rζ_le_of_qNormProductSq_le {y z : Fin n → ℝ} (h : c.qNormProductSq y ≤ c.qNormProductSq z) : c.rζ y ≤ c.rζ z := by
  unfold rζ
  have := Real.sqrt_le_sqrt (show c.ε₂ ^ 2 + c.qNormProductSq y ≤ c.ε₂ ^ 2 + c.qNormProductSq z by linarith)
  linarith

theorem rζ_lt_of_qNormProductSq_lt {y z : Fin n → ℝ} (h : c.qNormProductSq y < c.qNormProductSq z) : c.rζ y < c.rζ z := by
  unfold rζ
  have := Real.sqrt_lt_sqrt (add_nonneg (sq_nonneg c.ε₂) (c.qNormProductSq_nonneg y))
    (show c.ε₂ ^ 2 + c.qNormProductSq y < c.ε₂ ^ 2 + c.qNormProductSq z by linarith)
  linarith

theorem rζ_eq_zero_of_qNormProductSq_eq_zero {y : Fin n → ℝ} (h : c.qNormProductSq y = 0) : c.rζ y = 0 := by
  unfold rζ; rw [h, add_zero, Real.sqrt_sq c.ε₂_pos.le]; ring

def ζhat (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n - c.d.k)) :=
  (Real.sqrt (c.rζ y) * ‖posPart c.d.hk y‖⁻¹) • posPart c.d.hk y

theorem ζhat_of_posPart_eq_zero {y : Fin n → ℝ} (h : posPart c.d.hk y = 0) : c.ζhat y = 0 := by
  unfold ζhat; rw [h, smul_zero]

theorem norm_ζhat_of_ne {y : Fin n → ℝ} (h : posPart c.d.hk y ≠ 0) :
    ‖c.ζhat y‖ = Real.sqrt (c.rζ y) := by
  unfold ζhat
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 h), mul_one]

theorem norm_ζhat_le (y : Fin n → ℝ) : ‖c.ζhat y‖ ≤ Real.sqrt (c.rζ y) := by
  by_cases h : posPart c.d.hk y = 0
  · rw [c.ζhat_of_posPart_eq_zero h, norm_zero]; exact Real.sqrt_nonneg _
  · rw [c.norm_ζhat_of_ne h]

theorem norm_ζhat_sq_le (y : Fin n → ℝ) : ‖c.ζhat y‖ ^ 2 ≤ c.rζ y := by
  have := c.norm_ζhat_le y
  have h2 := pow_le_pow_left₀ (norm_nonneg _) this 2
  rwa [Real.sq_sqrt (c.rζ_nonneg y)] at h2

theorem ζhat_eq_zero_iff (y : Fin n → ℝ) : c.ζhat y = 0 ↔ c.qNormProductSq y = 0 := by
  constructor
  · intro h
    by_cases hv : posPart c.d.hk y = 0
    · unfold qNormProductSq; rw [hv, norm_zero]; ring
    · have h1 := c.norm_ζhat_of_ne hv
      rw [h, norm_zero] at h1
      have h2 : c.rζ y = 0 := by
        have := Real.sqrt_eq_zero'.1 h1.symm
        exact le_antisymm this (c.rζ_nonneg y)
      have := c.rζ_mul y
      rw [h2] at this; linarith
  · intro h
    by_cases hv : posPart c.d.hk y = 0
    · exact c.ζhat_of_posPart_eq_zero hv
    · unfold ζhat
      rw [c.rζ_eq_zero_of_qNormProductSq_eq_zero h, Real.sqrt_zero, zero_mul, zero_smul]

theorem continuousAt_ζhat (y : Fin n → ℝ) : ContinuousAt c.ζhat y := by
  by_cases hv : posPart c.d.hk y = 0
  · have hQ : c.qNormProductSq y = 0 := by unfold qNormProductSq; rw [hv, norm_zero]; ring
    rw [ContinuousAt, c.ζhat_of_posPart_eq_zero hv]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun z => c.norm_ζhat_le z) ?_
    have : Tendsto (fun z => Real.sqrt (c.rζ z)) (𝓝 y) (𝓝 (Real.sqrt (c.rζ y))) :=
      (c.continuous_rζ.sqrt).continuousAt
    rwa [c.rζ_eq_zero_of_qNormProductSq_eq_zero hQ, Real.sqrt_zero] at this
  · have hcont : Continuous (posPart c.d.hk) := (ModelField.posPartL c.d.hk).continuous
    have h1 : ContinuousAt (fun z => Real.sqrt (c.rζ z) * ‖posPart c.d.hk z‖⁻¹) y :=
      (c.continuous_rζ.sqrt).continuousAt.mul
        ((hcont.norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hv))
    exact h1.smul hcont.continuousAt

theorem continuous_ζhat : Continuous c.ζhat :=
  continuous_iff_continuousAt.2 c.continuousAt_ζhat

theorem ζhat_eq_smul {y : Fin n → ℝ} (hv : posPart c.d.hk y ≠ 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ c.ζhat y = μ • posPart c.d.hk y :=
  ⟨Real.sqrt (c.rζ y) * ‖posPart c.d.hk y‖⁻¹, by positivity, rfl⟩

theorem qNormProductSq_eq_ζ {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hT : c.d.χ y ∈ c.openChartTube) :
    ‖c.ζ (c.d.χ y)‖ ^ 2 * (2 * c.ε₂ + ‖c.ζ (c.d.χ y)‖ ^ 2) = c.qNormProductSq y := by
  have hyrm := c.morseNorm_lt_rmq_of_sq_lt hy
  have hyR : morseNorm n y ≤ c.d.R := hyrm.le.trans (c.D.hrm q c.hq).2
  have hsymm : c.d.χ.symm (c.d.χ y) = y := c.chart_q_symm_eq' hy
  have hstay := c.hstay_π_of_hstay (c.hstay_of_mem_qBall' hy hT)
  have hk1 : c.d.k = 1 := c.hkq
  set i₀ : Fin c.d.k := ⟨0, by omega⟩ with hi₀
  have hprod : ∀ j, negPart c.d.hk y i₀ * posPart c.d.hk y j =
      negPart c.d.hk (c.w (c.d.χ y)) i₀ * posPart c.d.hk (c.w (c.d.χ y)) j := fun j => by
    have := c.prod_w_eq hT hstay i₀ j
    rwa [hsymm] at this
  have hw := c.normSq_negPart_w hT
  rw [← c.ζ_def] at hw
  have hnu : ∀ z : Fin n → ℝ, ‖negPart c.d.hk z‖ ^ 2 = negPart c.d.hk z i₀ ^ 2 := by
    intro z
    rw [EuclideanSpace.real_norm_sq_eq]
    have : ∀ i : Fin c.d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
    rw [Finset.sum_eq_single i₀ (fun i _ hi => absurd (this i) hi)
      (fun h => absurd (Finset.mem_univ _) h)]
  have hnv : ∀ z : Fin n → ℝ, ‖posPart c.d.hk z‖ ^ 2 = ∑ j, posPart c.d.hk z j ^ 2 := fun z =>
    EuclideanSpace.real_norm_sq_eq _
  have hQ' : ‖negPart c.d.hk y‖ ^ 2 * ‖posPart c.d.hk y‖ ^ 2 =
      ‖negPart c.d.hk (c.w (c.d.χ y))‖ ^ 2 * ‖posPart c.d.hk (c.w (c.d.χ y))‖ ^ 2 := by
    rw [hnu y, hnv y, hnu (c.w _), hnv (c.w _), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_pow, ← mul_pow, hprod j]
  unfold qNormProductSq
  rw [hQ', hw, c.ζ_def]
  ring

theorem ζ_eq_ζhat {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hT : c.d.χ y ∈ c.openChartTube) :
    c.ζ (c.d.χ y) = c.ζhat y := by
  have hyrm := c.morseNorm_lt_rmq_of_sq_lt hy
  obtain ⟨μ, hμ, hζ⟩ := c.exists_ζ_eq_smul_posPart hyrm hT (c.hstay_of_mem_qBall' hy hT)
  have hQ := c.qNormProductSq_eq_ζ hy hT
  have hr : ‖c.ζ (c.d.χ y)‖ ^ 2 = c.rζ y := c.rζ_eq_of (by positivity) hQ
  by_cases hv : posPart c.d.hk y = 0
  · rw [c.ζhat_of_posPart_eq_zero hv, hζ, hv, smul_zero]
  · unfold ζhat
    rw [hζ, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, mul_pow] at hr
    rw [hζ]
    congr 1
    have hvn : 0 < ‖posPart c.d.hk y‖ := norm_pos_iff.2 hv
    have : Real.sqrt (c.rζ y) = μ * ‖posPart c.d.hk y‖ := by
      rw [← hr, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]; ring
    rw [this]; field_simp

theorem norm_ζ_le_iff_qNormProductSq_le (k : c.CancelConsts) {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.d.χ y ∈ c.openChartTube) : ‖c.ζ (c.d.χ y)‖ ≤ k.δ' ↔ c.qNormProductSq y ≤ k.qNormProductBound := by
  have hQ := c.qNormProductSq_eq_ζ hy hT
  have hδ := k.δ'_pos
  have hε₂ := c.ε₂_pos
  have hn := norm_nonneg (c.ζ (c.d.χ y))
  unfold CancelConsts.qNormProductBound
  constructor
  · intro h
    rw [← hQ]
    have h2 : ‖c.ζ (c.d.χ y)‖ ^ 2 ≤ k.δ' ^ 2 := pow_le_pow_left₀ hn h 2
    nlinarith
  · intro h
    by_contra hlt
    push Not at hlt
    have h2 : k.δ' ^ 2 < ‖c.ζ (c.d.χ y)‖ ^ 2 := pow_lt_pow_left₀ hlt hδ.le two_ne_zero
    nlinarith

theorem norm_ζ_lt_iff_qNormProductSq_lt (k : c.CancelConsts) {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.d.χ y ∈ c.openChartTube) : ‖c.ζ (c.d.χ y)‖ < k.δ' ↔ c.qNormProductSq y < k.qNormProductBound := by
  have hQ := c.qNormProductSq_eq_ζ hy hT
  have hδ := k.δ'_pos
  have hε₂ := c.ε₂_pos
  have hn := norm_nonneg (c.ζ (c.d.χ y))
  unfold CancelConsts.qNormProductBound
  constructor
  · intro h
    rw [← hQ]
    have h2 : ‖c.ζ (c.d.χ y)‖ ^ 2 < k.δ' ^ 2 := pow_lt_pow_left₀ h hn two_ne_zero
    nlinarith
  · intro h
    by_contra hle
    push Not at hle
    have h2 : k.δ' ^ 2 ≤ ‖c.ζ (c.d.χ y)‖ ^ 2 := pow_le_pow_left₀ hδ.le hle 2
    nlinarith

open scoped Classical in
def qRestrictedTransverseField (y : Fin n → ℝ) : Fin n → ℝ := if c.d.χ y ∈ c.orientedChartTube then c.qTransverseField y else 0

theorem qRestrictedTransverseField_of_mem {y : Fin n → ℝ} (h : c.d.χ y ∈ c.orientedChartTube) : c.qRestrictedTransverseField y = c.qTransverseField y := by
  classical simp [qRestrictedTransverseField, h]

theorem qRestrictedTransverseField_of_notMem {y : Fin n → ℝ} (h : c.d.χ y ∉ c.orientedChartTube) : c.qRestrictedTransverseField y = 0 := by
  classical simp [qRestrictedTransverseField, h]

def bq (y : Fin n → ℝ) : ℝ :=
  ‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2)

def bq' (y : Fin n → ℝ) : ℝ :=
  ‖posPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2)

theorem bq_nonneg (y : Fin n → ℝ) : 0 ≤ c.bq y := by unfold bq; positivity

theorem bq'_nonneg (y : Fin n → ℝ) : 0 ≤ c.bq' y := by unfold bq'; positivity

theorem bq_le_one (y : Fin n → ℝ) : c.bq y ≤ 1 := by
  unfold bq
  by_cases h : ‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2 = 0
  · rw [h, div_zero]; exact zero_le_one
  · rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm h))]
    linarith [sq_nonneg ‖posPart c.d.hk y‖]

theorem bq_add_bq' {y : Fin n → ℝ} (h : y ≠ 0) : c.bq y + c.bq' y = 1 := by
  unfold bq bq'
  have hne : ‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2 ≠ 0 := by
    rw [← morseNorm_sq_eq_negPart_add_posPart c.d.hk]
    exact pow_ne_zero 2 (morseNorm_pos h).ne'
  rw [← add_div, div_self hne]

theorem bq_pos_of_negPart_ne_zero {y : Fin n → ℝ} (h : negPart c.d.hk y ≠ 0) : 0 < c.bq y := by
  unfold bq
  have : 0 < ‖negPart c.d.hk y‖ ^ 2 := by positivity
  positivity

theorem posPart_qRestrictedTransverseField_of_mem {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.d.χ y ∈ c.orientedChartTube) :
    posPart c.d.hk (c.qRestrictedTransverseField y) = (-(c.κ (c.d.χ y) * c.bq y)) • posPart c.d.hk y := by
  rw [c.qRestrictedTransverseField_of_mem hT]
  have := c.posPart_transverseField_chart_q (c.morseNorm_lt_rmq_of_sq_lt hy) hT.1 (c.hstay_of_mem_qBall' hy hT.1)
  unfold qTransverseField bq
  rw [← neg_mul]
  exact this

theorem uq_qRestrictedTransverseField_of_mem {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.d.χ y ∈ c.orientedChartTube) :
    uq c.d.hk c.hkq (c.qRestrictedTransverseField y) = (-(c.κ (c.d.χ y) * c.bq' y)) * uq c.d.hk c.hkq y := by
  rw [c.qRestrictedTransverseField_of_mem hT]
  have := c.negPart_transverseField_chart_q (c.morseNorm_lt_rmq_of_sq_lt hy) hT.1 (c.hstay_of_mem_qBall' hy hT.1)
  have hk1 : c.d.k = 1 := c.hkq
  have h2 := congrArg (fun z => z ⟨0, by omega⟩) this
  simp only [PiLp.smul_apply, smul_eq_mul] at h2
  have h3 : negPart c.d.hk (c.qTransverseField y) ⟨0, by omega⟩ =
      -c.κ (c.d.χ y) * (‖posPart c.d.hk y‖ ^ 2 /
        (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2)) * negPart c.d.hk y ⟨0, by omega⟩ := h2
  change negPart c.d.hk (c.qTransverseField y) ⟨0, by omega⟩ = _ * negPart c.d.hk y ⟨0, by omega⟩
  rw [h3]
  unfold bq'
  ring

namespace CancelConsts

variable {c} (k : c.CancelConsts)

open scoped Classical in
def qReversalWeight (y : Fin n → ℝ) : ℝ :=
  if c.d.χ y ∈ c.orientedChartTube then k.βm (c.d.χ y) * c.ψm (c.d.χ y) else 0

open scoped Classical in
def qTransverseWeight (y : Fin n → ℝ) : ℝ :=
  if c.d.χ y ∈ c.orientedChartTube then k.βm' (c.d.χ y) * c.ψm' (c.d.χ y) else 0

theorem qReversalWeight_of_mem {y : Fin n → ℝ} (h : c.d.χ y ∈ c.orientedChartTube) :
    k.qReversalWeight y = k.βm (c.d.χ y) * c.ψm (c.d.χ y) := by classical simp [qReversalWeight, h]

theorem qReversalWeight_of_notMem {y : Fin n → ℝ} (h : c.d.χ y ∉ c.orientedChartTube) : k.qReversalWeight y = 0 := by
  classical simp [qReversalWeight, h]

theorem qTransverseWeight_of_mem {y : Fin n → ℝ} (h : c.d.χ y ∈ c.orientedChartTube) :
    k.qTransverseWeight y = k.βm' (c.d.χ y) * c.ψm' (c.d.χ y) := by classical simp [qTransverseWeight, h]

theorem qTransverseWeight_of_notMem {y : Fin n → ℝ} (h : c.d.χ y ∉ c.orientedChartTube) : k.qTransverseWeight y = 0 := by
  classical simp [qTransverseWeight, h]

theorem qReversalWeight_nonneg (y : Fin n → ℝ) : 0 ≤ k.qReversalWeight y := by
  classical
  unfold qReversalWeight; split_ifs
  · exact mul_nonneg (k.βm_nonneg _) (c.ψm_nonneg _)
  · exact le_rfl

theorem qReversalWeight_le_one (y : Fin n → ℝ) : k.qReversalWeight y ≤ 1 := by
  classical
  unfold qReversalWeight; split_ifs
  · exact (mul_le_mul (k.βm_le_one _) (c.ψm_le_one _) (c.ψm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem qTransverseWeight_nonneg (y : Fin n → ℝ) : 0 ≤ k.qTransverseWeight y := by
  classical
  unfold qTransverseWeight; split_ifs
  · exact mul_nonneg (k.βm'_nonneg _) (c.ψm'_nonneg _)
  · exact le_rfl

theorem qTransverseWeight_le_one (y : Fin n → ℝ) : k.qTransverseWeight y ≤ 1 := by
  classical
  unfold qTransverseWeight; split_ifs
  · exact (mul_le_mul (k.βm'_le_one _) (c.ψm'_le_one _) (c.ψm'_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem qTransverseWeight_eq_one_of_qReversalWeight_ne_zero {y : Fin n → ℝ} (h : k.qReversalWeight y ≠ 0) : k.qTransverseWeight y = 1 := by
  classical
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [k.qReversalWeight_of_mem hT] at h
    rw [k.qTransverseWeight_of_mem hT]
    exact k.βm'_mul_ψm'_eq_one h
  · exact absurd (k.qReversalWeight_of_notMem hT) h

theorem qReversalWeight_eq_zero_of_qTransverseWeight_eq_zero {y : Fin n → ℝ} (h : k.qTransverseWeight y = 0) : k.qReversalWeight y = 0 := by
  classical
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [k.qTransverseWeight_of_mem hT] at h
    rw [k.qReversalWeight_of_mem hT]
    exact k.βm_mul_ψm_eq_zero h
  · exact k.qReversalWeight_of_notMem hT

theorem qReversalWeight_eq_zero_of_σ_uq_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (h : c.σ * uq c.d.hk c.hkq y ≤ 0) : k.qReversalWeight y = 0 :=
  k.qReversalWeight_of_notMem fun hT => absurd (c.σ_uq_pos_of_mem_orientedChartTube hy hT) (not_lt.2 h)

theorem qTransverseWeight_eq_zero_of_σ_uq_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (h : c.σ * uq c.d.hk c.hkq y ≤ 0) : k.qTransverseWeight y = 0 :=
  k.qTransverseWeight_of_notMem fun hT => absurd (c.σ_uq_pos_of_mem_orientedChartTube hy hT) (not_lt.2 h)

theorem qCancellationField_eq (y : Fin n → ℝ) :
    k.qCancellationField y = (1 - 2 * k.qReversalWeight y) • ModelField.modelField c.d.k c.d.r₀ y + k.qPerturbationField y +
      (2 * (c.lam * k.qTransverseWeight y)) • c.qRestrictedTransverseField y := by
  classical
  unfold qCancellationField
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [k.qReversalWeight_of_mem hT, k.qTransverseWeight_of_mem hT, c.qRestrictedTransverseField_of_mem hT]
    simp only [hT, ite_true]
    module
  · rw [k.qReversalWeight_of_notMem hT, k.qTransverseWeight_of_notMem hT, c.qRestrictedTransverseField_of_notMem hT]
    simp only [hT, ite_false]
    module

def qDampingCoefficient (y : Fin n → ℝ) : ℝ :=
  ModelField.theta c.d.r₀ y * (1 - 2 * k.qReversalWeight y) +
    2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * c.bq y)

theorem qPerturbationField_eq (y : Fin n → ℝ) : k.qPerturbationField y =
    -(c.σ * c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) • c.e₀' := rfl

theorem posPart_qCancellationField {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    posPart c.d.hk (k.qCancellationField y) = (-k.qDampingCoefficient y) • posPart c.d.hk y := by
  classical
  rw [k.qCancellationField_eq, ModelField.posPart_add, ModelField.posPart_add, ModelField.posPart_smul,
    ModelField.posPart_smul, ModelField.posPart_modelField, k.qPerturbationField_eq, ModelField.posPart_smul,
    c.posPart_e₀', smul_zero, add_zero]
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [c.posPart_qRestrictedTransverseField_of_mem hy hT]
    simp only [qDampingCoefficient]
    module
  · rw [c.qRestrictedTransverseField_of_notMem hT, posPart_zero, smul_zero]
    simp only [qDampingCoefficient, k.qTransverseWeight_of_notMem hT]
    module

theorem uq_qCancellationField {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    uq c.d.hk c.hkq (k.qCancellationField y) =
      ModelField.theta c.d.r₀ y * uq c.d.hk c.hkq y * (1 - 2 * k.qReversalWeight y) -
        c.σ * c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y) +
        2 * (c.lam * k.qTransverseWeight y) * ((-(c.κ (c.d.χ y) * c.bq' y)) * uq c.d.hk c.hkq y) := by
  classical
  rw [k.qCancellationField_eq, uq_add, uq_add, uq_smul, uq_smul, uq_modelField, k.qPerturbationField_eq, uq_smul, c.uq_e₀',
    mul_one]
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · rw [c.uq_qRestrictedTransverseField_of_mem hy hT]; ring
  · rw [c.qRestrictedTransverseField_of_notMem hT, uq_zero, k.qTransverseWeight_of_notMem hT]; ring

theorem qDampingCoefficient_pos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) : 0 < k.qDampingCoefficient y := by
  classical
  have hθ := ModelField.theta_pos c.d.hr₀ y
  have hlam := c.lam_pos
  unfold qDampingCoefficient
  by_cases hT : c.d.χ y ∈ c.orientedChartTube
  · have hyR : morseNorm n y ≤ c.d.R :=
      (c.morseNorm_lt_rmq_of_sq_lt hy).le.trans (c.D.hrm q c.hq).2
    have hκ := c.one_le_κ (c.d.χ y)
    have hκ0 := c.κ_pos (c.d.χ y)
    have hu2 := (c.normSq_negPart_of_mem hyR hT.1).1
    have hu0 := (c.normSq_negPart_of_mem hyR hT.1).2
    have hsum := morseNorm_sq_eq_negPart_add_posPart c.d.hk y
    have hb0 : 0 < c.bq y := by
      unfold bq; exact div_pos hu0 (by linarith [sq_nonneg ‖posPart c.d.hk y‖])
    have hb' : c.bq y * morseNorm n y ^ 2 = ‖negPart c.d.hk y‖ ^ 2 := by
      unfold bq; rw [hsum]; field_simp
    have hθy := theta_mul_sq_le c.d.hr₀ y
    have hy2 : 0 < morseNorm n y ^ 2 := by rw [hsum]; positivity
    have hC0 := k.qReversalWeight_nonneg y
    have hC1 := k.qReversalWeight_le_one y
    have hB0 := k.qTransverseWeight_nonneg y
    have hlm := c.lam_mul
    rcases le_or_gt (k.qReversalWeight y) (1 / 2) with hCle | hCgt
    · have h1 : 0 ≤ (1 - 2 * k.qReversalWeight y) * ModelField.theta c.d.r₀ y := by
        apply mul_nonneg _ hθ.le; linarith
      have h2 : 0 ≤ 2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * c.bq y) := by positivity
      rcases lt_or_eq_of_le h1 with h1 | h1
      · nlinarith
      · have h4 : k.qReversalWeight y = 1 / 2 := by
          rcases mul_eq_zero.1 h1.symm with h | h
          · linarith
          · exact absurd h hθ.ne'
        have hBc1 : k.qTransverseWeight y = 1 := k.qTransverseWeight_eq_one_of_qReversalWeight_ne_zero (by rw [h4]; norm_num)
        rw [hBc1, h4]
        have := mul_pos hlam (mul_pos hκ0 hb0)
        nlinarith
    · have hBc1 : k.qTransverseWeight y = 1 :=
        k.qTransverseWeight_eq_one_of_qReversalWeight_ne_zero (by intro h; rw [h] at hCgt; linarith)
      rw [hBc1]
      have h6 : (2 * k.qReversalWeight y - 1) * (ModelField.theta c.d.r₀ y * morseNorm n y ^ 2) ≤ 1 * 1 :=
        mul_le_mul (by linarith) hθy (by positivity) (by norm_num)
      have h7 : 2 * c.lam * 1 * (2 * (c.ε₂ - c.η)) ≤
          2 * c.lam * c.κ (c.d.χ y) * ‖negPart c.d.hk y‖ ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hκ (by positivity)) hu2
          (by linarith [c.ε₂_sub_η_pos]) (by positivity)
      have key : 0 < (ModelField.theta c.d.r₀ y * (1 - 2 * k.qReversalWeight y) +
          2 * (c.lam * 1) * (c.κ (c.d.χ y) * c.bq y)) * morseNorm n y ^ 2 := by
        have e : (ModelField.theta c.d.r₀ y * (1 - 2 * k.qReversalWeight y) +
            2 * (c.lam * 1) * (c.κ (c.d.χ y) * c.bq y)) * morseNorm n y ^ 2 =
            -((2 * k.qReversalWeight y - 1) * (ModelField.theta c.d.r₀ y * morseNorm n y ^ 2)) +
              2 * c.lam * c.κ (c.d.χ y) * (c.bq y * morseNorm n y ^ 2) := by ring
        rw [e, hb']
        linarith
      exact pos_of_mul_pos_left key hy2.le
  · rw [k.qReversalWeight_of_notMem hT, k.qTransverseWeight_of_notMem hT]
    simp only [mul_zero, zero_mul, sub_zero, mul_one, add_zero]
    exact hθ

theorem qDampingCoefficient_le {Kθ : ℝ} {y : Fin n → ℝ} (hθ : ModelField.theta c.d.r₀ y ≤ Kθ) :
    k.qDampingCoefficient y ≤ Kθ + 4 * c.lam := by
  unfold qDampingCoefficient
  have h1 := ModelField.theta_pos c.d.hr₀ y
  have hC0 := k.qReversalWeight_nonneg y
  have hB0 := k.qTransverseWeight_nonneg y
  have hB1 := k.qTransverseWeight_le_one y
  have hκ := c.κ_lt_two (c.d.χ y)
  have hκ0 := c.κ_pos (c.d.χ y)
  have hb0 := c.bq_nonneg y
  have hb1 := c.bq_le_one y
  have hlam := c.lam_pos
  have e1 : ModelField.theta c.d.r₀ y * (1 - 2 * k.qReversalWeight y) ≤ Kθ := by nlinarith
  have e2 : c.κ (c.d.χ y) * c.bq y ≤ 2 := by nlinarith
  have e3 : 2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * c.bq y) ≤ 2 * c.lam * 2 := by
    have : 2 * (c.lam * k.qTransverseWeight y) ≤ 2 * c.lam := by nlinarith
    have : 0 ≤ 2 * (c.lam * k.qTransverseWeight y) := by positivity
    nlinarith
  linarith

def qNormProductRate (y : Fin n → ℝ) : ℝ :=
  -(2 * ‖posPart c.d.hk y‖ ^ 2) *
    (c.σ * uq c.d.hk c.hkq y *
        (c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) +
      2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2))

theorem qNormProductRate_nonpos {y : Fin n → ℝ} (h : 0 ≤ c.σ * uq c.d.hk c.hkq y) : k.qNormProductRate y ≤ 0 := by
  unfold qNormProductRate
  have h1 : 0 ≤ c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y) :=
    mul_nonneg c.m'_pos.le (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _))
  have h2 : 0 ≤ 2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2) :=
    mul_nonneg (by have := c.lam_pos; have := k.qTransverseWeight_nonneg y; positivity)
      (mul_nonneg (c.κ_pos _).le (sq_nonneg _))
  have h3 : 0 ≤ 2 * ‖posPart c.d.hk y‖ ^ 2 := by positivity
  nlinarith [mul_nonneg h h1]

theorem qNormProductRate_eq {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    k.qNormProductRate y = 2 * uq c.d.hk c.hkq y * uq c.d.hk c.hkq (k.qCancellationField y) * ‖posPart c.d.hk y‖ ^ 2 +
      uq c.d.hk c.hkq y ^ 2 * (-(2 * k.qDampingCoefficient y) * ‖posPart c.d.hk y‖ ^ 2) := by
  rw [k.uq_qCancellationField hy]
  unfold qNormProductRate qDampingCoefficient
  by_cases hy0 : y = 0
  · subst hy0
    simp [uq_zero]
  · have hb := c.bq_add_bq' hy0
    have e : c.bq' y = 1 - c.bq y := by linarith
    rw [e]
    ring

end CancelConsts

def qAxialDefect (y : Fin n → ℝ) : ℝ := c.sheetAxialDefect (c.ζhat y)

theorem qAxialDefect_nonneg (y : Fin n → ℝ) : 0 ≤ c.qAxialDefect y := c.sheetAxialDefect_nonneg _

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem qAxialDefect_eq_sheetAxialDefect_ζ {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.d.χ y ∈ c.openChartTube) : c.qAxialDefect y = c.sheetAxialDefect (c.ζ (c.d.χ y)) := by
  unfold qAxialDefect; rw [c.ζ_eq_ζhat hy hT]

theorem rζ_of_qNormProductSq_eq_qNormProductBound {y : Fin n → ℝ} (h : c.qNormProductSq y = k.qNormProductBound) : c.rζ y = k.δ' ^ 2 :=
  (c.rζ_eq_of (sq_nonneg _) (by rw [h]; unfold qNormProductBound; ring)).symm

theorem rζ_le_of_qNormProductSq_le_qNormProductBound {y : Fin n → ℝ} (h : c.qNormProductSq y ≤ k.qNormProductBound) : c.rζ y ≤ k.δ' ^ 2 := by
  have h1 := c.rζ_mul y
  have h2 := c.rζ_nonneg y
  have h3 := c.ε₂_pos
  have h4 := k.δ'_pos
  unfold qNormProductBound at h
  by_contra hlt
  push Not at hlt
  nlinarith

theorem norm_ζhat_le_δ'_of_qNormProductSq_le {y : Fin n → ℝ} (h : c.qNormProductSq y ≤ k.qNormProductBound) : ‖c.ζhat y‖ ≤ k.δ' := by
  have h1 := c.norm_ζhat_sq_le y
  have h2 := k.rζ_le_of_qNormProductSq_le_qNormProductBound h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 (h1.trans h2)

theorem norm_ζhat_lt_δ''_of_qNormProductSq_le (hk : k.Good) {y : Fin n → ℝ} (h : c.qNormProductSq y ≤ k.qNormProductBound) :
    ‖c.ζhat y‖ < hk.δ'' :=
  (k.norm_ζhat_le_δ'_of_qNormProductSq_le h).trans_lt hk.hδ'δ''

theorem sheetAxialDefect_pos (hk : k.Good) {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv0 : v ≠ 0)
    (hv : ‖v‖ < hk.δ'') : 0 < c.sheetAxialDefect v := by
  have := hk.sheetAxialDefect_smul_lt hv0 hv (a := 1 / 2) (by norm_num) (by norm_num)
  linarith [c.sheetAxialDefect_nonneg ((1 / 2 : ℝ) • v)]

section Curve

variable {y : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
  (hy : ∀ s ∈ Icc t₀ t₁, HasDerivAt y (k.qCancellationField (y s)) s)
  (hb : ∀ s ∈ Icc t₀ t₁, morseNorm n (y s) ^ 2 < 3 * c.ε)
include hy hb

theorem hasDerivAt_posPart_qCancellationField {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => posPart c.d.hk (y s)) ((-k.qDampingCoefficient (y t)) • posPart c.d.hk (y t)) t := by
  have := (ModelField.posPartL c.d.hk).hasFDerivAt.comp_hasDerivAt t (hy t ht)
  rw [ModelField.posPartL_apply, k.posPart_qCancellationField (hb t ht)] at this
  exact this

theorem hasDerivAt_normSq_posPart_qCancellationField {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => ‖posPart c.d.hk (y s)‖ ^ 2)
      (-(2 * k.qDampingCoefficient (y t)) * ‖posPart c.d.hk (y t)‖ ^ 2) t := by
  have := (k.hasDerivAt_posPart_qCancellationField hy hb ht).norm_sq
  rw [inner_smul_right, real_inner_self_eq_norm_sq] at this
  convert this using 1; ring

omit hb in
theorem hasDerivAt_uq_qCancellationField {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => uq c.d.hk c.hkq (y s)) (uq c.d.hk c.hkq (k.qCancellationField (y t))) t := by
  have hk1 : c.d.k = 1 := c.hkq
  exact hasDerivAt_pi.1 (hy t ht)
    (DifferentialGeometry.Topology.Morse.CellAttachment.negIdx c.d.hk ⟨0, by omega⟩)

theorem hasDerivAt_qNormProductSq_qCancellationField {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt (fun s => c.qNormProductSq (y s)) (k.qNormProductRate (y t)) t := by
  have h1 := (k.hasDerivAt_uq_qCancellationField hy ht).fun_pow 2
  have h3 := h1.mul (k.hasDerivAt_normSq_posPart_qCancellationField hy hb ht)
  rw [k.qNormProductRate_eq (hb t ht)]
  convert h3 using 1
  · funext s; exact c.qNormProductSq_eq_uq (y s)
  · push_cast; ring

theorem antitoneOn_normSq_posPart_qCancellationField :
    AntitoneOn (fun s => ‖posPart c.d.hk (y s)‖ ^ 2) (Icc t₀ t₁) :=
  antitoneOn_Icc_of_hasDerivAt_nonpos (fun _ ht => k.hasDerivAt_normSq_posPart_qCancellationField hy hb ht)
    fun t ht => by
      have := k.qDampingCoefficient_pos (hb t ht)
      nlinarith [sq_nonneg ‖posPart c.d.hk (y t)‖]

theorem antitoneOn_qNormProductSq_qCancellationField (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (y s)) :
    AntitoneOn (fun s => c.qNormProductSq (y s)) (Icc t₀ t₁) :=
  antitoneOn_Icc_of_hasDerivAt_nonpos (fun _ ht => k.hasDerivAt_qNormProductSq_qCancellationField hy hb ht)
    fun t ht => k.qNormProductRate_nonpos (hσ t ht)

theorem σ_uq_nonpos_qCancellationField {Kθ : ℝ} (hθ : ∀ s ∈ Icc t₀ t₁, ModelField.theta c.d.r₀ (y s) ≤ Kθ)
    (h0 : c.σ * uq c.d.hk c.hkq (y t₀) ≤ 0) :
    ∀ s ∈ Icc t₀ t₁, c.σ * uq c.d.hk c.hkq (y s) ≤ 0 := by
  refine nonpos_of_deriv_le_mul (h := fun s => c.σ * uq c.d.hk c.hkq (y s))
    (h' := fun s => c.σ * uq c.d.hk c.hkq (k.qCancellationField (y s))) (K := Kθ)
    (fun t ht => (k.hasDerivAt_uq_qCancellationField hy ht).const_mul c.σ) h0 (fun t ht hpos => ?_)
  rw [k.uq_qCancellationField (hb t ht)]
  have hσ2 := c.σ_sq
  set u := uq c.d.hk c.hkq (y t) with hu
  set θ := ModelField.theta c.d.r₀ (y t) with hθdef
  set βψ := βq c.d.hk c.hkq k.δ k.τ c.σ (y t) * ψq c.d.hk c.hkq c.uA c.uB (y t) with hβψ
  set B := k.qTransverseWeight (y t)
  set C := k.qReversalWeight (y t)
  set κb := c.κ (c.d.χ (y t)) * c.bq' (y t)
  have e : c.σ * (θ * u * (1 - 2 * C) - c.σ * c.m' * βψ + 2 * (c.lam * B) * (-κb * u)) =
      θ * (c.σ * u) * (1 - 2 * C) - c.m' * βψ - 2 * (c.lam * B) * κb * (c.σ * u) := by
    linear_combination (-(c.m' * βψ)) * hσ2
  rw [e]
  have hθ0 : 0 < θ := ModelField.theta_pos c.d.hr₀ _
  have hC0 := k.qReversalWeight_nonneg (y t)
  have h1 : θ * (c.σ * u) * (1 - 2 * C) ≤ θ * (c.σ * u) :=
    mul_le_of_le_one_right (mul_nonneg hθ0.le hpos) (by linarith)
  have h2 : θ * (c.σ * u) ≤ Kθ * (c.σ * u) := mul_le_mul_of_nonneg_right (hθ t ht) hpos
  have h3 : 0 ≤ c.m' * βψ :=
    mul_nonneg c.m'_pos.le (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _))
  have h4 : 0 ≤ 2 * (c.lam * B) * κb * (c.σ * u) := by
    have := c.lam_pos; have := k.qTransverseWeight_nonneg (y t); have := c.κ_pos (c.d.χ (y t))
    have := c.bq'_nonneg (y t)
    positivity
  linarith

theorem exists_smul_posPart_qCancellationField {Kθ : ℝ}
    (hθ : ∀ s ∈ Icc t₀ t₁, ModelField.theta c.d.r₀ (y s) ≤ Kθ) :
    ∀ s ∈ Icc t₀ t₁, ∃ m : ℝ, 0 < m ∧ posPart c.d.hk (y s) = m • posPart c.d.hk (y t₀) := by
  intro s hs
  have ht₀ : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.2 (hs.1.trans hs.2)
  set v₀ := posPart c.d.hk (y t₀) with hv₀def
  by_cases hv₀ : v₀ = 0
  · refine ⟨1, one_pos, ?_⟩
    have h1 : ‖posPart c.d.hk (y s)‖ ^ 2 ≤ ‖posPart c.d.hk (y t₀)‖ ^ 2 :=
      k.antitoneOn_normSq_posPart_qCancellationField hy hb ht₀ hs hs.1
    rw [← hv₀def, hv₀, norm_zero] at h1
    have h2 : ‖posPart c.d.hk (y s)‖ ^ 2 = 0 := le_antisymm (by simpa using h1) (by positivity)
    rw [norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2), hv₀, smul_zero]
  · have hv₀n : 0 < ‖v₀‖ ^ 2 := by positivity
    set m : ℝ → ℝ := fun s => inner ℝ (posPart c.d.hk (y s)) v₀ / ‖v₀‖ ^ 2 with hm
    have hmd : ∀ t ∈ Icc t₀ t₁, HasDerivAt m (-k.qDampingCoefficient (y t) * m t) t := by
      intro t ht
      have h := ((k.hasDerivAt_posPart_qCancellationField hy hb ht).inner ℝ (hasDerivAt_const t v₀)).div_const
        (‖v₀‖ ^ 2)
      convert h using 1
      simp only [hm, inner_zero_right, zero_add, inner_smul_left, conj_trivial]
      ring
    have hm0 : m t₀ = 1 := by
      simp only [hm, ← hv₀def, real_inner_self_eq_norm_sq]
      exact div_self hv₀n.ne'
    have hmpos : ∀ t ∈ Icc t₀ t₁, 0 < m t := by
      refine pos_of_deriv_ge_neg_mul (K := Kθ + 4 * c.lam) hmd (by rw [hm0]; exact one_pos)
        fun t ht hnn => ?_
      have := k.qDampingCoefficient_le (hθ t ht)
      nlinarith
    set w : ℝ → EuclideanSpace ℝ (Fin (n - c.d.k)) := fun s => posPart c.d.hk (y s) - m s • v₀
      with hw
    have hwd : ∀ t ∈ Icc t₀ t₁, HasDerivAt w ((-k.qDampingCoefficient (y t)) • w t) t := by
      intro t ht
      have := (k.hasDerivAt_posPart_qCancellationField hy hb ht).sub ((hmd t ht).smul_const v₀)
      convert this using 1
      simp only [hw]
      module
    have hwn : ∀ t ∈ Icc t₀ t₁,
        HasDerivAt (fun s => ‖w s‖ ^ 2) (-(2 * k.qDampingCoefficient (y t)) * ‖w t‖ ^ 2) t := by
      intro t ht
      have := (hwd t ht).norm_sq
      rw [inner_smul_right, real_inner_self_eq_norm_sq] at this
      convert this using 1; ring
    have hanti : AntitoneOn (fun s => ‖w s‖ ^ 2) (Icc t₀ t₁) :=
      antitoneOn_Icc_of_hasDerivAt_nonpos hwn fun t ht => by
        have := k.qDampingCoefficient_pos (hb t ht)
        nlinarith [sq_nonneg ‖w t‖]
    have hw0 : w t₀ = 0 := by
      change posPart c.d.hk (y t₀) - m t₀ • v₀ = 0
      rw [hm0, one_smul, hv₀def, sub_self]
    have h1 : ‖w s‖ ^ 2 ≤ ‖w t₀‖ ^ 2 := hanti ht₀ hs hs.1
    rw [hw0, norm_zero] at h1
    have h2 : ‖w s‖ ^ 2 = 0 := le_antisymm (by simpa using h1) (by positivity)
    have h3 : w s = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    refine ⟨m s, hmpos s hs, ?_⟩
    have : posPart c.d.hk (y s) - m s • v₀ = 0 := h3
    exact sub_eq_zero.1 this

theorem exists_smul_ζhat_qCancellationField {Kθ : ℝ}
    (hθ : ∀ s ∈ Icc t₀ t₁, ModelField.theta c.d.r₀ (y s) ≤ Kθ)
    (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (y s)) :
    ∀ s ∈ Icc t₀ t₁, ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ c.ζhat (y s) = a • c.ζhat (y t₀) ∧
      (c.qNormProductSq (y s) < c.qNormProductSq (y t₀) → 0 < c.qNormProductSq (y t₀) → a < 1) := by
  intro s hs
  have ht₀ : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.2 (hs.1.trans hs.2)
  obtain ⟨m, hm, hv⟩ := k.exists_smul_posPart_qCancellationField hy hb hθ s hs
  have hQ : c.qNormProductSq (y s) ≤ c.qNormProductSq (y t₀) := k.antitoneOn_qNormProductSq_qCancellationField hy hb hσ ht₀ hs hs.1
  have hr : c.rζ (y s) ≤ c.rζ (y t₀) := c.rζ_le_of_qNormProductSq_le hQ
  have hr0 := c.rζ_nonneg (y s)
  have hr0' := c.rζ_nonneg (y t₀)
  set v₀ := posPart c.d.hk (y t₀) with hv₀def
  by_cases hv₀ : v₀ = 0
  · refine ⟨1, zero_le_one, le_rfl, ?_, fun _ _ => ?_⟩
    · rw [c.ζhat_of_posPart_eq_zero (by rw [hv, hv₀, smul_zero]),
        c.ζhat_of_posPart_eq_zero hv₀, smul_zero]
    · exfalso
      have : c.qNormProductSq (y t₀) = 0 := by unfold qNormProductSq; rw [← hv₀def, hv₀, norm_zero]; ring
      linarith
  · by_cases hr₀ : c.rζ (y t₀) = 0
    · have hrs : c.rζ (y s) = 0 := le_antisymm (hr.trans_eq hr₀) hr0
      refine ⟨1, zero_le_one, le_rfl, ?_, fun _ hQ0 => ?_⟩
      · unfold ζhat
        simp [hrs, hr₀]
      · exfalso
        have := c.rζ_mul (y t₀)
        rw [hr₀] at this
        linarith
    · have hr₀pos : 0 < c.rζ (y t₀) := lt_of_le_of_ne hr0' (Ne.symm hr₀)
      refine ⟨Real.sqrt (c.rζ (y s)) / Real.sqrt (c.rζ (y t₀)), by positivity, ?_, ?_, ?_⟩
      · rw [div_le_one (Real.sqrt_pos.2 hr₀pos)]
        exact Real.sqrt_le_sqrt hr
      · unfold ζhat
        rw [hv, ← hv₀def, norm_smul, Real.norm_eq_abs, abs_of_pos hm, smul_smul, smul_smul]
        congr 1
        have hvn : ‖v₀‖ ≠ 0 := norm_ne_zero_iff.2 hv₀
        field_simp
      · intro hlt hQ0
        rw [div_lt_one (Real.sqrt_pos.2 hr₀pos)]
        exact Real.sqrt_lt_sqrt hr0 (c.rζ_lt_of_qNormProductSq_lt hlt)

theorem qAxialDefect_le_qCancellationField (hk : k.Good) {Kθ : ℝ}
    (hθ : ∀ s ∈ Icc t₀ t₁, ModelField.theta c.d.r₀ (y s) ≤ Kθ)
    (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (y s)) (hQ : c.qNormProductSq (y t₀) ≤ k.qNormProductBound) :
    ∀ s ∈ Icc t₀ t₁, c.qAxialDefect (y s) ≤ c.qAxialDefect (y t₀) := by
  intro s hs
  obtain ⟨a, ha0, ha1, hζ, -⟩ := k.exists_smul_ζhat_qCancellationField hy hb hθ hσ s hs
  unfold qAxialDefect
  rw [hζ]
  rcases ha0.eq_or_lt with h | h
  · rw [← h, zero_smul, c.sheetAxialDefect_zero]; exact c.sheetAxialDefect_nonneg _
  · exact hk.sheetAxialDefect_smul_le (k.norm_ζhat_lt_δ''_of_qNormProductSq_le hk hQ) h ha1

theorem qAxialDefect_lt_qCancellationField (hk : k.Good) {Kθ : ℝ}
    (hθ : ∀ s ∈ Icc t₀ t₁, ModelField.theta c.d.r₀ (y s) ≤ Kθ)
    (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (y s)) (hQ : c.qNormProductSq (y t₀) ≤ k.qNormProductBound)
    (hQ0 : 0 < c.qNormProductSq (y t₀)) {s : ℝ} (hs : s ∈ Icc t₀ t₁) (hlt : c.qNormProductSq (y s) < c.qNormProductSq (y t₀)) :
    c.qAxialDefect (y s) < c.qAxialDefect (y t₀) := by
  obtain ⟨a, ha0, -, hζ, hstrict⟩ := k.exists_smul_ζhat_qCancellationField hy hb hθ hσ s hs
  have ha1 := hstrict hlt hQ0
  have hζ0 : c.ζhat (y t₀) ≠ 0 := fun h => by
    rw [c.ζhat_eq_zero_iff] at h; linarith
  have hδ := k.norm_ζhat_lt_δ''_of_qNormProductSq_le hk hQ
  unfold qAxialDefect
  rw [hζ]
  rcases ha0.eq_or_lt with h | h
  · rw [← h, zero_smul, c.sheetAxialDefect_zero]; exact k.sheetAxialDefect_pos hk hζ0 hδ
  · exact hk.sheetAxialDefect_smul_lt hζ0 hδ h ha1

end Curve

end CancelConsts

theorem sqrt_three_ε_lt_R'q : Real.sqrt (3 * c.ε) < c.d.R' :=
  c.sqrt_three_ε_lt_rmq.trans (c.D.rm_lt_R' q c.hq)

theorem hi₁_le_iff {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.d.R) :
    c.hi₁ ≤ f (c.d.χ y) ↔ uq c.d.hk c.hkq y ^ 2 ≤ c.uB ^ 2 + ‖posPart c.d.hk y‖ ^ 2 := by
  rw [c.f_chart_q hy, c.uB_sq_eq]
  constructor <;> intro h <;> linarith

theorem hi₁_lt_iff {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.d.R) :
    c.hi₁ < f (c.d.χ y) ↔ uq c.d.hk c.hkq y ^ 2 < c.uB ^ 2 + ‖posPart c.d.hk y‖ ^ 2 := by
  rw [c.f_chart_q hy, c.uB_sq_eq]
  constructor <;> intro h <;> linarith

theorem morseNorm_le_R_of_sq_lt {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    morseNorm n y ≤ c.d.R :=
  (c.morseNorm_lt_rmq_of_sq_lt hy).le.trans (c.D.hrm q c.hq).2

theorem continuousOn_symm_qBall' : ContinuousOn c.d.χ.symm c.qBall' :=
  c.d.hχsymm.continuousOn.mono c.qBall'_subset_image_ball

theorem symm_sq_lt_of_mem_qBall' {x : M} (hx : x ∈ c.qBall') :
    morseNorm n (c.d.χ.symm x) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_q_symm_eq' hy]; exact hy

namespace CancelConsts

variable {c} (k : c.CancelConsts)

section Flow

variable {x : M} {t₀ t₁ : ℝ} (hq : ∀ s ∈ Icc t₀ t₁, k.cancellationFlow s x ∈ c.qBall')
include hq

theorem hasDerivAt_symm_cancellationFlow_q_Icc' :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => c.d.χ.symm (k.cancellationFlow s x)) (k.qCancellationField (c.d.χ.symm (k.cancellationFlow s x))) s :=
  k.hasDerivAt_symm_cancellationFlow_q_Icc hq

theorem symm_cancellationFlow_q_sq_lt_Icc : ∀ s ∈ Icc t₀ t₁, morseNorm n (c.d.χ.symm (k.cancellationFlow s x)) ^ 2 < 3 * c.ε :=
  fun s hs => k.symm_cancellationFlow_q_sq_lt (hq s hs)

theorem antitoneOn_normSq_posPart_cancellationFlow :
    AntitoneOn (fun s => ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow s x))‖ ^ 2) (Icc t₀ t₁) :=
  k.antitoneOn_normSq_posPart_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hq) (k.symm_cancellationFlow_q_sq_lt_Icc hq)

theorem antitoneOn_qNormProductSq_cancellationFlow (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x))) :
    AntitoneOn (fun s => c.qNormProductSq (c.d.χ.symm (k.cancellationFlow s x))) (Icc t₀ t₁) :=
  k.antitoneOn_qNormProductSq_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hq) (k.symm_cancellationFlow_q_sq_lt_Icc hq) hσ

theorem σ_uq_nonpos_cancellationFlow (h0 : c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow t₀ x)) ≤ 0) :
    ∀ s ∈ Icc t₀ t₁, c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x)) ≤ 0 := by
  obtain ⟨Kθ, -, hKθ⟩ := c.exists_theta_le_q
  exact k.σ_uq_nonpos_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hq) (k.symm_cancellationFlow_q_sq_lt_Icc hq)
    (fun s hs => hKθ _ (k.symm_cancellationFlow_q_sq_lt (hq s hs)).le) h0

theorem σ_uq_pos_of_pos_end (hpos : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow t₁ x))) :
    ∀ s ∈ Icc t₀ t₁, 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x)) := by
  intro s hs
  by_contra hle
  push Not at hle
  have := k.σ_uq_nonpos_cancellationFlow (t₀ := s) (t₁ := t₁) (fun u hu => hq u ⟨hs.1.trans hu.1, hu.2⟩) hle t₁
    (right_mem_Icc.2 hs.2)
  linarith

theorem qAxialDefect_le_cancellationFlow (hk : k.Good)
    (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x)))
    (hQ : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow t₀ x)) ≤ k.qNormProductBound) :
    ∀ s ∈ Icc t₀ t₁, c.qAxialDefect (c.d.χ.symm (k.cancellationFlow s x)) ≤ c.qAxialDefect (c.d.χ.symm (k.cancellationFlow t₀ x)) := by
  obtain ⟨Kθ, -, hKθ⟩ := c.exists_theta_le_q
  exact k.qAxialDefect_le_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hq) (k.symm_cancellationFlow_q_sq_lt_Icc hq) hk
    (fun s hs => hKθ _ (k.symm_cancellationFlow_q_sq_lt (hq s hs)).le) hσ hQ

theorem qAxialDefect_lt_cancellationFlow (hk : k.Good)
    (hσ : ∀ s ∈ Icc t₀ t₁, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x)))
    (hQ : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow t₀ x)) ≤ k.qNormProductBound) (hQ0 : 0 < c.qNormProductSq (c.d.χ.symm (k.cancellationFlow t₀ x)))
    {s : ℝ} (hs : s ∈ Icc t₀ t₁)
    (hlt : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow s x)) < c.qNormProductSq (c.d.χ.symm (k.cancellationFlow t₀ x))) :
    c.qAxialDefect (c.d.χ.symm (k.cancellationFlow s x)) < c.qAxialDefect (c.d.χ.symm (k.cancellationFlow t₀ x)) := by
  obtain ⟨Kθ, -, hKθ⟩ := c.exists_theta_le_q
  exact k.qAxialDefect_lt_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hq) (k.symm_cancellationFlow_q_sq_lt_Icc hq) hk
    (fun s hs => hKθ _ (k.symm_cancellationFlow_q_sq_lt (hq s hs)).le) hσ hQ hQ0 hs hlt

end Flow

theorem hasDerivAt_qNormProductSq_cancellationFlow {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.qBall') :
    HasDerivAt (fun s => c.qNormProductSq (c.d.χ.symm (k.cancellationFlow s x))) (k.qNormProductRate (c.d.χ.symm (k.cancellationFlow s x))) s := by
  obtain ⟨ε, hε, hO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_qBall' hs
  exact k.hasDerivAt_qNormProductSq_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hO) (k.symm_cancellationFlow_q_sq_lt_Icc hO)
    ⟨by linarith, by linarith⟩

theorem hasDerivAt_normSq_posPart_cancellationFlow {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.qBall') :
    HasDerivAt (fun s => ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow s x))‖ ^ 2)
      (-(2 * k.qDampingCoefficient (c.d.χ.symm (k.cancellationFlow s x))) * ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow s x))‖ ^ 2) s := by
  obtain ⟨ε, hε, hO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_qBall' hs
  exact k.hasDerivAt_normSq_posPart_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hO)
    (k.symm_cancellationFlow_q_sq_lt_Icc hO) ⟨by linarith, by linarith⟩

theorem hasDerivAt_uq_cancellationFlow {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.qBall') :
    HasDerivAt (fun s => uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow s x)))
      (uq c.d.hk c.hkq (k.qCancellationField (c.d.χ.symm (k.cancellationFlow s x)))) s := by
  obtain ⟨ε, hε, hO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_qBall' hs
  exact k.hasDerivAt_uq_qCancellationField (k.hasDerivAt_symm_cancellationFlow_q_Icc' hO) ⟨by linarith, by linarith⟩

def qCoordinateRegion : Set (Fin n → ℝ) :=
  {y | -(2 * k.δ) ≤ c.σ * uq c.d.hk c.hkq y ∧
    uq c.d.hk c.hkq y ^ 2 ≤ c.uB ^ 2 + ‖posPart c.d.hk y‖ ^ 2 ∧ ‖posPart c.d.hk y‖ ≤ k.ν}

def qPositiveCoordinateRegion : Set (Fin n → ℝ) :=
  {y | 0 ≤ c.σ * uq c.d.hk c.hkq y ∧
    uq c.d.hk c.hkq y ^ 2 ≤ c.uB ^ 2 + ‖posPart c.d.hk y‖ ^ 2 ∧ ‖posPart c.d.hk y‖ ≤ k.ν ∧
    c.qNormProductSq y ≤ k.qNormProductBound}

def qNegativeCoordinateRegion : Set (Fin n → ℝ) :=
  {y | -(2 * k.δ) ≤ c.σ * uq c.d.hk c.hkq y ∧ c.σ * uq c.d.hk c.hkq y ≤ 0 ∧
    ‖posPart c.d.hk y‖ ≤ k.ν}

def qRegion : Set M := c.d.χ '' k.qCoordinateRegion

def qPositiveRegion : Set M := c.d.χ '' k.qPositiveCoordinateRegion

def qNegativeRegion : Set M := c.d.χ '' k.qNegativeCoordinateRegion

theorem qPositiveCoordinateRegion_subset : k.qPositiveCoordinateRegion ⊆ k.qCoordinateRegion := fun _ hy =>
  ⟨by linarith [hy.1, k.hδ], hy.2.1, hy.2.2.1⟩

theorem four_δ_sq_le_uB_sq : 4 * k.δ ^ 2 ≤ c.uB ^ 2 := by
  have h1 := k.δ_sq_lt
  have h2 := c.uB_sq
  have h3 : c.ε / 2 ≤ c.ε₂ := by unfold ε₂; nlinarith [sq_nonneg c.d.r₀]
  have h4 := c.η_pos
  nlinarith

theorem qNegativeCoordinateRegion_subset : k.qNegativeCoordinateRegion ⊆ k.qCoordinateRegion := fun y hy => by
  refine ⟨hy.1, ?_, hy.2.2⟩
  have h1 := hy.1
  have h2 := hy.2.1
  have hσ := c.σ_sq
  have : uq c.d.hk c.hkq y ^ 2 ≤ 4 * k.δ ^ 2 := by
    have e : uq c.d.hk c.hkq y ^ 2 = (c.σ * uq c.d.hk c.hkq y) ^ 2 := by
      rw [mul_pow]; nlinarith [hσ]
    rw [e]; nlinarith
  nlinarith [k.four_δ_sq_le_uB_sq, sq_nonneg ‖posPart c.d.hk y‖]

theorem qPositiveRegion_subset_qRegion : k.qPositiveRegion ⊆ k.qRegion := image_mono k.qPositiveCoordinateRegion_subset

theorem qNegativeRegion_subset_qRegion : k.qNegativeRegion ⊆ k.qRegion := image_mono k.qNegativeCoordinateRegion_subset

theorem sq_lt_of_mem_qCoordinateRegion (hk : k.Good) {y : Fin n → ℝ} (hy : y ∈ k.qCoordinateRegion) :
    morseNorm n y ^ 2 < 3 * c.ε := by
  have h1 := morseNorm_sq_eq_uq c.d.hk c.hkq y
  have h2 := hy.2.1
  have h3 : ‖posPart c.d.hk y‖ ^ 2 ≤ k.ν ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy.2.2 2
  have h4 := hk.uB_sq_add_two_ν_sq_lt
  nlinarith

theorem qCoordinateRegion_subset_le (hk : k.Good) : k.qCoordinateRegion ⊆ {y | morseNorm n y ≤ Real.sqrt (3 * c.ε)} :=
  fun _ hy => Real.le_sqrt_of_sq_le (k.sq_lt_of_mem_qCoordinateRegion hk hy).le

theorem isClosed_qCoordinateRegion : IsClosed k.qCoordinateRegion :=
  (isClosed_le continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))).inter
    ((isClosed_le ((continuous_uq c.d.hk c.hkq).pow 2)
      (continuous_const.add (continuous_normSq_posPart c.d.hk))).inter
      (isClosed_le (c.d.continuous_posPart.norm) continuous_const))

theorem isClosed_qPositiveCoordinateRegion : IsClosed k.qPositiveCoordinateRegion :=
  (isClosed_le continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))).inter
    ((isClosed_le ((continuous_uq c.d.hk c.hkq).pow 2)
      (continuous_const.add (continuous_normSq_posPart c.d.hk))).inter
      ((isClosed_le (c.d.continuous_posPart.norm) continuous_const).inter
        (isClosed_le c.continuous_qNormProductSq continuous_const)))

theorem isClosed_qNegativeCoordinateRegion : IsClosed k.qNegativeCoordinateRegion :=
  (isClosed_le continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))).inter
    ((isClosed_le (continuous_const.mul (continuous_uq c.d.hk c.hkq)) continuous_const).inter
      (isClosed_le (c.d.continuous_posPart.norm) continuous_const))

theorem isCompact_qCoordinateRegion (hk : k.Good) : IsCompact k.qCoordinateRegion :=
  (isCompact_morseNorm_le (Real.sqrt (3 * c.ε))).of_isClosed_subset k.isClosed_qCoordinateRegion
    (k.qCoordinateRegion_subset_le hk)

theorem isCompact_qRegion (hk : k.Good) : IsCompact k.qRegion :=
  c.d.isCompact_image_of_subset (k.isCompact_qCoordinateRegion hk) c.sqrt_three_ε_lt_R'q
    (k.qCoordinateRegion_subset_le hk)

theorem isCompact_qPositiveRegion (hk : k.Good) : IsCompact k.qPositiveRegion :=
  c.d.isCompact_image_of_subset
    ((k.isCompact_qCoordinateRegion hk).of_isClosed_subset k.isClosed_qPositiveCoordinateRegion k.qPositiveCoordinateRegion_subset)
    c.sqrt_three_ε_lt_R'q (k.qPositiveCoordinateRegion_subset.trans (k.qCoordinateRegion_subset_le hk))

theorem isCompact_qNegativeRegion (hk : k.Good) : IsCompact k.qNegativeRegion :=
  c.d.isCompact_image_of_subset
    ((k.isCompact_qCoordinateRegion hk).of_isClosed_subset k.isClosed_qNegativeCoordinateRegion k.qNegativeCoordinateRegion_subset)
    c.sqrt_three_ε_lt_R'q (k.qNegativeCoordinateRegion_subset.trans (k.qCoordinateRegion_subset_le hk))

theorem qRegion_subset_qBall' (hk : k.Good) : k.qRegion ⊆ c.qBall' :=
  image_mono fun _ hy => k.sq_lt_of_mem_qCoordinateRegion hk hy

theorem symm_mem_qCoordinateRegion_of_mem_qRegion (hk : k.Good) {x : M} (hx : x ∈ k.qRegion) :
    c.d.χ.symm x ∈ k.qCoordinateRegion := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_q_symm_eq' (k.sq_lt_of_mem_qCoordinateRegion hk hy)]

theorem symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion (hk : k.Good) {x : M} (hx : x ∈ k.qPositiveRegion) :
    c.d.χ.symm x ∈ k.qPositiveCoordinateRegion := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_q_symm_eq' (k.sq_lt_of_mem_qCoordinateRegion hk (k.qPositiveCoordinateRegion_subset hy))]

theorem symm_mem_qNegativeCoordinateRegion_of_mem_qNegativeRegion (hk : k.Good) {x : M} (hx : x ∈ k.qNegativeRegion) :
    c.d.χ.symm x ∈ k.qNegativeCoordinateRegion := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_q_symm_eq' (k.sq_lt_of_mem_qCoordinateRegion hk (k.qNegativeCoordinateRegion_subset hy))]

theorem mem_qRegion_of_symm {x : M} (hx : x ∈ c.qBall') (h : c.d.χ.symm x ∈ k.qCoordinateRegion) : x ∈ k.qRegion :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx) h

theorem mem_qPositiveRegion_of_symm {x : M} (hx : x ∈ c.qBall') (h : c.d.χ.symm x ∈ k.qPositiveCoordinateRegion) :
    x ∈ k.qPositiveRegion :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx) h

theorem mem_qNegativeRegion_of_symm {x : M} (hx : x ∈ c.qBall') (h : c.d.χ.symm x ∈ k.qNegativeCoordinateRegion) :
    x ∈ k.qNegativeRegion :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx) h

theorem hi₁_le_f_of_mem_qRegion (hk : k.Good) {x : M} (hx : x ∈ k.qRegion) : c.hi₁ ≤ f x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact (c.hi₁_le_iff (c.morseNorm_le_R_of_sq_lt (k.sq_lt_of_mem_qCoordinateRegion hk hy))).2 hy.2.1

theorem σ_uq_qCancellationField_neg_axis {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hv : posPart c.d.hk y = 0) (hlo : c.lo₂ ≤ f (c.d.χ y)) :
    c.σ * uq c.d.hk c.hkq (k.qCancellationField y) < 0 := by
  rw [k.uq_qCancellationField hy]
  have hb' : c.bq' y = 0 := by unfold bq'; rw [hv, norm_zero]; simp
  rw [hb', mul_zero, neg_zero, zero_mul, mul_zero, add_zero]
  have hσ2 := c.σ_sq
  have hθ := ModelField.theta_pos c.d.hr₀ y
  have hm := c.hm_q y
  have hm0 := c.m'_pos
  set u := uq c.d.hk c.hkq y with hu
  set θ := ModelField.theta c.d.r₀ y with hθdef
  set βψ := βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y with hβψ
  have e : c.σ * (θ * u * (1 - 2 * k.qReversalWeight y) - c.σ * c.m' * βψ) =
      θ * (c.σ * u) * (1 - 2 * k.qReversalWeight y) - c.m' * βψ := by
    linear_combination (-(c.m' * βψ)) * hσ2
  rw [e]
  have hβψ0 : 0 ≤ βψ := mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)
  rcases lt_trichotomy (c.σ * u) 0 with hneg | hzero | hpos
  · have hC : k.qReversalWeight y = 0 := k.qReversalWeight_eq_zero_of_σ_uq_nonpos hy hneg.le
    rw [hC]
    nlinarith [mul_pos hθ (neg_pos.2 hneg)]
  · have hu0 : u = 0 := by
      rcases mul_eq_zero.1 hzero with h | h
      · exact absurd h c.σ_ne_zero
      · exact h
    have hy0 : y = 0 := eq_zero_of_uq_eq_zero c.d.hk c.hkq hu0 hv
    rw [hzero, hβψ, hy0, βq_zero c.d.hk c.hkq k.hδ, ψq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB]
    simp only [mul_zero, zero_mul, mul_one, zero_sub]
    linarith
  · have hβ1 : βq c.d.hk c.hkq k.δ k.τ c.σ y = 1 :=
      βq_axis c.d.hk c.hkq k.hδ hv (by linarith [k.hδ])
    have hyR := c.morseNorm_le_R_of_sq_lt hy
    have hfx : f (c.d.χ y) = f q - u ^ 2 / 2 := by
      rw [c.f_chart_q hyR, hv, norm_zero]; ring
    have hψ := ψq_add_plateau c.d.hk c.hkq c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ c.uA_sq_eq c.uB_sq_eq
      (y := y) (by rw [← hu, ← hfx]; exact hlo)
    have hψm : c.ψm (c.d.χ y) = plateau c.lo₁ c.lo₂ c.hi₁ c.hi₂ (f q - u ^ 2 / 2) := by
      unfold IndexZeroCancellingPair.ψm; rw [hfx]
    have hψq : ψq c.d.hk c.hkq c.uA c.uB y = 1 - c.ψm (c.d.χ y) := by
      rw [hψm]; rw [← hu] at hψ; linarith
    have hC : k.qReversalWeight y = c.ψm (c.d.χ y) := by
      by_cases hT : c.d.χ y ∈ c.orientedChartTube
      · rw [k.qReversalWeight_of_mem hT]
        have hζ : c.ζ (c.d.χ y) = 0 := by
          rw [c.ζ_eq_ζhat hy hT.1]; exact c.ζhat_of_posPart_eq_zero hv
        rw [k.βm_eq_one_of_ζ_eq_zero hζ, one_mul]
      · rw [k.qReversalWeight_of_notMem hT]
        have hf : f (c.d.χ y) ∉ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := fun hf =>
          hT (c.mem_orientedChartTube_of_σ_uq_pos hy hf hpos)
        have hlo' : c.c₁ - c.η < f (c.d.χ y) := by
          have := c.lo₂_lt_hi₁; have := c.η_pos; unfold lo₂ at hlo; linarith
        have hhi : c.c₂ + c.η ≤ f (c.d.χ y) := by
          by_contra h; push Not at h; exact hf ⟨hlo', h⟩
        rw [c.ψm_eq_zero_of_ge (by unfold hi₂; linarith [c.η_pos])]
    have habs : c.σ * u = morseNorm n y := by
      rw [morseNorm_eq_abs_uq c.d.hk c.hkq hv]
      rcases c.σ_eq with h | h
      · rw [h, one_mul]; rw [h, one_mul] at hpos; exact (abs_of_pos hpos).symm
      · rw [h, neg_one_mul]; rw [h, neg_one_mul] at hpos
        exact (abs_of_neg (by linarith)).symm
    have hθu : 0 < θ * (c.σ * u) := mul_pos hθ hpos
    have hlt := axis_ineq_q (θu := θ * (c.σ * u)) (m := c.m') hθu (by rw [habs]; exact hm)
      (ψq_nonneg c.d.hk c.hkq (ua := c.uA) (ub := c.uB) y)
      (ψq_le_one c.d.hk c.hkq (ua := c.uA) (ub := c.uB) y)
    rw [hβψ, hβ1, one_mul, hC, hψq]
    rw [hψq] at hlt
    linarith

theorem exists_exit_qRegion (hk : k.Good) : ∀ x ∈ k.qRegion, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ k.qRegion := by
  refine k.exists_exit_of_lyapunov_pair (k.isCompact_qRegion hk)
    (L₁ := fun y => ‖posPart c.d.hk (c.d.χ.symm y)‖ ^ 2)
    (L₂ := fun y => -(c.σ * uq c.d.hk c.hkq (c.d.χ.symm y)))
    ((c.d.continuous_posPart.norm.pow 2).comp_continuousOn
      (c.continuousOn_symm_qBall'.mono (k.qRegion_subset_qBall' hk)))
    ((continuous_const.mul (continuous_uq c.d.hk c.hkq)).neg.comp_continuousOn
      (c.continuousOn_symm_qBall'.mono (k.qRegion_subset_qBall' hk)))
    (Z := {y | posPart c.d.hk (c.d.χ.symm y) = 0}) ?_ ?_
  · intro x hx
    have hxq : k.cancellationFlow 0 x ∈ c.qBall' := by rw [k.cancellationFlow_zero]; exact k.qRegion_subset_qBall' hk hx
    have hd := k.hasDerivAt_normSq_posPart_cancellationFlow hxq
    rw [k.cancellationFlow_zero] at hd
    refine ⟨_, ?_, hd, fun h0 => ?_⟩
    · have := k.qDampingCoefficient_pos (k.symm_cancellationFlow_q_sq_lt hxq)
      rw [k.cancellationFlow_zero] at this
      nlinarith [sq_nonneg ‖posPart c.d.hk (c.d.χ.symm x)‖]
    · have hA := k.qDampingCoefficient_pos (k.symm_cancellationFlow_q_sq_lt hxq)
      rw [k.cancellationFlow_zero] at hA
      have : ‖posPart c.d.hk (c.d.χ.symm x)‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exfalso; linarith
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · rintro x ⟨hx, hv⟩
    have hv' : posPart c.d.hk (c.d.χ.symm x) = 0 := hv
    have hxq : k.cancellationFlow 0 x ∈ c.qBall' := by rw [k.cancellationFlow_zero]; exact k.qRegion_subset_qBall' hk hx
    have hd := (k.hasDerivAt_uq_cancellationFlow hxq).const_mul c.σ |>.neg
    rw [k.cancellationFlow_zero] at hd
    refine ⟨_, ?_, hd⟩
    have hy := k.symm_mem_qCoordinateRegion_of_mem_qRegion hk hx
    have hsq := k.sq_lt_of_mem_qCoordinateRegion hk hy
    have hlo : c.lo₂ ≤ f (c.d.χ (c.d.χ.symm x)) := by
      rw [c.d.symm_image_eq (c.qBall'_subset_image_ball (k.qRegion_subset_qBall' hk hx))]
      exact c.lo₂_lt_hi₁.le.trans (k.hi₁_le_f_of_mem_qRegion hk hx)
    have := k.σ_uq_qCancellationField_neg_axis hsq hv' hlo
    linarith

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
