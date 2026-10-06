module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldLift
public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.TransverseAscent

@[expose] public section

set_option autoImplicit false

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace
open DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace CrossField

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  {f : M → ℝ} {a' b' : ℝ} {p q : M}

namespace TransverseCancellingPair

variable [DecidableEq M] (c : TransverseCancellingPair I f a' b' p q)

theorem band_setup : ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ c.βmax ∧ ∃ W : Set (Fin n → ℝ), IsOpen W ∧
    (∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), c.pRayAt s ∈ W) ∧
    (∃ rW : ℝ, 0 < rW ∧ ∀ y : Fin n → ℝ,
      |morseNormalForm c.dp.hk (f p) y - c.fb| ≤ 3 * β₀ →
        ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ rW → y ∈ W) ∧
    (∀ y ∈ W, c.dp.r₀ < morseNorm n y ∧ morseNorm n y < c.D.rm p (mem_pair_left p q) ∧
      c.dp.χ y ∈ c.qTube ∧ 0 < c.qArc (c.qExtendedChart (c.dp.χ y)) ∧
      c.qArc (c.qExtendedChart (c.dp.χ y)) ^ 2 < c.sqSum) ∧
    ContDiffOn ℝ ∞ (fun y => c.qExtendedChart (c.dp.χ y)) W ∧
    ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 → negPart c.dp.hk w = 0 →
        fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (c.pRayAt s) w = 0 → w = 0 := by
  have hfc : Continuous f := c.hf.smooth.continuous
  have hpq := mem_pair_left p q
  have hε := c.hε
  have hr₀p : c.dp.r₀ ^ 2 < 2 * c.ε := c.hr₀p
  have hrmp : 8 * c.ε < c.D.rm p hpq ^ 2 := c.hrmp
  have hrmq : 8 * c.ε < c.D.rm q (mem_pair_right p q) ^ 2 := c.hrmq
  have hr₀pos : 0 < c.dp.r₀ := c.dp.hr₀
  have hgap : 2 * c.ε < f q - f p := by linarith [c.hc₁, c.hc₂]
  have hβ1 : c.βmax ≤ c.ε / 16 := by
    unfold TransverseCancellingPair.βmax; exact (min_le_left _ _).trans (min_le_left _ _)
  have hβ2 : c.βmax ≤ (f q - f p - 2 * c.ε) / 16 := by
    unfold TransverseCancellingPair.βmax; exact (min_le_left _ _).trans (min_le_right _ _)
  have hβ3 : c.βmax ≤ (2 * c.ε - c.dp.r₀ ^ 2) / 16 := by
    unfold TransverseCancellingPair.βmax; exact min_le_right _ _
  have hβpos : 0 < c.βmax := by
    unfold TransverseCancellingPair.βmax
    refine lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hfb : c.fb = f p + c.ε := rfl
  have hsq : c.sqSum = 2 * (f q - f p) := by
    unfold TransverseCancellingPair.sqSum TransverseCancellingPair.cq TransverseCancellingPair.fb; ring
  have hunit := c.unit_dirs
  have hseg : ∀ s ∈ Icc (c.fb - 3 * c.βmax) (c.fb + 3 * c.βmax),
      c.dp.r₀ < morseNorm n (c.pRayAt s) ∧ morseNorm n (c.pRayAt s) < c.D.rm p hpq ∧
        c.dp.χ (c.pRayAt s) ∈ c.qTube ∧ 0 < c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s))) ∧
        c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s))) ^ 2 < c.sqSum := by
    intro s hs
    rw [hfb] at hs
    obtain ⟨hs₁, hs₂⟩ := hs
    have hpos : 0 < 2 * (s - f p) := by linarith
    set t := Real.sqrt (2 * (s - f p)) with ht
    have ht0 : 0 < t := Real.sqrt_pos.2 hpos
    have ht2 : t ^ 2 = 2 * (s - f p) := Real.sq_sqrt hpos.le
    have ht' : |t ^ 2 - 2 * c.ε| ≤ 6 * c.βmax := by
      rw [abs_le]; constructor <;> linarith
    obtain ⟨hT, hΨ⟩ := c.qExtendedChart_p_ray ht0 ht'
    have hray : c.pRayAt s = recombine c.dp.hk 0 (t • c.e₁) := rfl
    have hmn : morseNorm n (c.pRayAt s) ^ 2 = t ^ 2 := by
      rw [hray, DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq, norm_smul, hunit.1]
      simp [Real.norm_eq_abs, abs_of_pos ht0]
    have hmn0 := ModelField.morseNorm_nonneg (c.pRayAt s)
    have hrm0 := c.D.rm_pos p hpq
    have hU : 0 < c.sqSum - t ^ 2 := by rw [hsq, ht2]; linarith
    have hqa : c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s))) = Real.sqrt (c.sqSum - t ^ 2) := by
      rw [hray, hΨ]
      unfold TransverseCancellingPair.qArc
      rw [ModelField.negPart_recombine, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hunit.2.1]
      ring
    refine ⟨?_, ?_, hray ▸ hT, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · rw [hqa]; exact Real.sqrt_pos.2 hU
    · rw [hqa, Real.sq_sqrt hU.le]; linarith
  have hρq : c.ρq < c.D.rm q (mem_pair_right p q) := by
    unfold TransverseCancellingPair.ρq
    rw [Real.sqrt_lt' (c.D.rm_pos q _)]; linarith
  have hqTo : IsOpen c.qTube := by
    have h1 : IsOpen {x : M | f x < c.cq} := isOpen_lt hfc continuous_const
    have h2 := c.D.isOpen_regularFlowDomain hfc c.cq
    have h3 : IsOpen (c.dq.χ '' {y | morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0}) := by
      refine (c.dq.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 ?_
      · exact c.dq.hsrc y (hy.1.le.trans ((hρq.le).trans (c.D.hrm q _).2))
      · exact (isOpen_morseNorm_lt _).inter
          (isOpen_compl_singleton.preimage (ModelField.negPartL c.dq.hk).continuous)
    exact h1.inter (h2.inter (h3.preimage (c.D.continuous_π c.hf.smooth c.cq)))
  have hΨc : ContinuousOn c.qExtendedChart c.qTube :=
    (c.contMDiffOn_qExtendedChart.2.mono subset_union_right).continuousOn
  have hqArcc : Continuous c.qArc :=
    (ModelField.negPartL c.dq.hk).continuous.inner continuous_const
  set S : Set M := c.qTube ∩ c.qExtendedChart ⁻¹' {z | 0 < c.qArc z ∧ c.qArc z ^ 2 < c.sqSum} with hS
  have hSo : IsOpen S :=
    hΨc.isOpen_inter_preimage hqTo
      ((isOpen_lt continuous_const hqArcc).inter
        (isOpen_lt (hqArcc.pow 2) continuous_const))
  set A : Set (Fin n → ℝ) := {y | c.dp.r₀ < morseNorm n y ∧ morseNorm n y < c.D.rm p hpq}
    with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_morseNorm).inter (isOpen_morseNorm_lt _)
  have hAball : A ⊆ Metric.ball 0 c.dp.R' := fun y hy =>
    mem_ball_of_morseNorm_lt (hy.2.trans (c.D.rm_lt_R' p hpq))
  set W : Set (Fin n → ℝ) := A ∩ c.dp.χ ⁻¹' S with hW
  have hWo : IsOpen W :=
    (c.dp.χ.continuousOn.mono fun y hy => c.dp.hball (hAball hy)).isOpen_inter_preimage hAo hSo
  have hWprop : ∀ y ∈ W, c.dp.r₀ < morseNorm n y ∧ morseNorm n y < c.D.rm p (mem_pair_left p q) ∧
      c.dp.χ y ∈ c.qTube ∧ 0 < c.qArc (c.qExtendedChart (c.dp.χ y)) ∧
      c.qArc (c.qExtendedChart (c.dp.χ y)) ^ 2 < c.sqSum := fun y hy =>
    ⟨hy.1.1, hy.1.2, hy.2.1, hy.2.2.1, hy.2.2.2⟩
  have hWC : ContDiffOn ℝ ∞ (fun y => c.qExtendedChart (c.dp.χ y)) W :=
    contMDiffOn_iff_contDiffOn.1 ((c.contMDiffOn_qExtendedChart.2).comp
      (c.dp.hχ.mono fun y hy => hAball hy.1) fun y hy => Or.inr hy.2.1)
  have hsegW : ∀ s ∈ Icc (c.fb - 3 * c.βmax) (c.fb + 3 * c.βmax), c.pRayAt s ∈ W := by
    intro s hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := hseg s hs
    exact ⟨⟨h1, h2⟩, h3, h4, h5⟩
  have hfbmem : c.fb ∈ Icc (c.fb - 3 * c.βmax) (c.fb + 3 * c.βmax) :=
    ⟨by linarith, by linarith⟩
  have hy₀ : c.pRayAt c.fb = c.y₀ := by
    rw [hunit.2.2, hfb]
    unfold TransverseCancellingPair.pRayAt
    congr 3
    ring
  have hy₀W : c.y₀ ∈ W := hy₀ ▸ hsegW c.fb hfbmem
  have hbC : ContDiffOn ℝ ∞ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) W :=
    (ModelField.posPartL c.dq.hk).contDiff.comp_contDiffOn hWC
  have hdb : ContinuousAt (fun y => fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) y)
      c.y₀ :=
    (hbC.continuousOn_fderiv_of_isOpen hWo (by simp)).continuousAt (hWo.mem_nhds hy₀W)
  have hdN : ContinuousAt (fun y => fderiv ℝ (morseNormalForm c.dp.hk (f p)) y) c.y₀ :=
    ((ModelField.contDiff_nf c.dp.hk (f p)).continuous_fderiv (by simp)).continuousAt
  set Lm : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ]
      ℝ × EuclideanSpace ℝ (Fin c.dp.k) × EuclideanSpace ℝ (Fin (n - c.dq.k))) :=
    fun y => (fderiv ℝ (morseNormalForm c.dp.hk (f p)) y).prod
      ((ModelField.negPartL c.dp.hk).prod
        (fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) y)) with hLm
  have hLc : ContinuousAt Lm c.y₀ := by
    have h1 : ContinuousAt (fun y => ContinuousLinearMap.prodₗᵢ ℝ
        (ModelField.negPartL c.dp.hk,
          fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) y)) c.y₀ :=
      (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp
        (continuousAt_const.prodMk hdb)
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp (hdN.prodMk h1)
  have hL₀ : Function.Injective (Lm c.y₀) := by
    intro w₁ w₂ h
    exact c.transversal_y₀.2 h
  have hev : ∀ᶠ y in 𝓝 c.y₀, Function.Injective (Lm y) :=
    hLc.eventually_mem (ContinuousLinearMap.isOpen_injective.mem_nhds hL₀)
  obtain ⟨δ, hδ, hδinj⟩ := Metric.eventually_nhds_iff.1 hev
  have hpc : Continuous c.pRayAt := by
    have : c.pRayAt = fun s => ModelField.recombineL c.dp.hk (0, Real.sqrt (2 * (s - f p)) • c.e₁) := by
      funext s; rw [ModelField.recombineL_apply]; rfl
    rw [this]; fun_prop
  obtain ⟨β₁, hβ₁, hβ₁δ⟩ := Metric.continuousAt_iff.1 (hpc.continuousAt (x := c.fb)) δ hδ
  refine ⟨min c.βmax (β₁ / 4), lt_min hβpos (by linarith), min_le_left _ _, W, hWo, ?_, ?_,
    hWprop, hWC, ?_⟩
  · intro s hs
    exact hsegW s ⟨by linarith [hs.1, min_le_left c.βmax (β₁ / 4)],
      by linarith [hs.2, min_le_left c.βmax (β₁ / 4)]⟩
  · have hK : IsCompact (c.pRayAt '' Icc (c.fb - 3 * min c.βmax (β₁ / 4))
        (c.fb + 3 * min c.βmax (β₁ / 4))) := isCompact_Icc.image hpc
    have hKW : c.pRayAt '' Icc (c.fb - 3 * min c.βmax (β₁ / 4))
        (c.fb + 3 * min c.βmax (β₁ / 4)) ⊆ W := by
      rintro _ ⟨s, hs, rfl⟩
      exact hsegW s ⟨by linarith [hs.1, min_le_left c.βmax (β₁ / 4)],
        by linarith [hs.2, min_le_left c.βmax (β₁ / 4)]⟩
    obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hWo hKW
    refine ⟨r, hr, fun y hy hyr => hrW ?_⟩
    rw [abs_le] at hy
    refine Metric.mem_cthickening_of_dist_le y
      (c.pRayAt (morseNormalForm c.dp.hk (f p) y)) r _
      (mem_image_of_mem c.pRayAt (x := morseNormalForm c.dp.hk (f p) y) ⟨by linarith [hy.1], by linarith [hy.2]⟩) ?_
    rw [dist_eq_norm]; exact hyr
  · intro s hs w h1 h2 h3
    have hds : dist s c.fb < β₁ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2, min_le_right c.βmax (β₁ / 4)]
    have hinj : Function.Injective (Lm (c.pRayAt s)) := hδinj (hy₀ ▸ hβ₁δ hds)
    apply hinj
    rw [map_zero]
    simp only [hLm, ContinuousLinearMap.prod_apply, ModelField.negPartL_apply, h1, h2, h3]
    rfl

theorem band_quad_le : ∃ η₀ β₀ r₀ : ℝ, 0 < η₀ ∧ 0 < β₀ ∧ β₀ ≤ c.βmax ∧ 0 < r₀ ∧
    ∀ η ∈ Ioc 0 η₀, ∀ y : Fin n → ℝ, |morseNormalForm c.dp.hk (f p) y - c.fb| ≤ 3 * β₀ →
      ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ r₀ →
        c.dp.χ y ∈ c.qTube ∧ c.qQuad η (c.qExtendedChart (c.dp.χ y)) ≤ c.pQuad η y := by
  classical
  obtain ⟨β₀, hβ₀, hβm, W, hWo, hσW, -, hWp, hsm, hinj⟩ := c.band_setup
  have hε : 0 < c.ε := c.hε
  have hβε : c.βmax ≤ c.ε / 16 := by
    unfold TransverseCancellingPair.βmax
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hu₀ : ‖c.u₀‖ = 1 := c.unit_dirs.2.1
  have he₁ : ‖c.e₁‖ = 1 := c.unit_dirs.1
  have hray : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀),
      morseNormalForm c.dp.hk (f p) (c.pRayAt s) = s ∧ negPart c.dp.hk (c.pRayAt s) = 0 ∧
        posPart c.dq.hk (c.qExtendedChart (c.dp.χ (c.pRayAt s))) = 0 ∧
        c.qPerp (c.qExtendedChart (c.dp.χ (c.pRayAt s))) = 0 ∧ c.pPerp (c.pRayAt s) = 0 := by
    intro s hs
    have hfb : c.fb = f p + c.ε := rfl
    have h2 : 0 < 2 * (s - f p) := by
      have := hs.1
      linarith
    set t := Real.sqrt (2 * (s - f p)) with ht
    have htp : 0 < t := Real.sqrt_pos.mpr h2
    have ht2 : t ^ 2 = 2 * (s - f p) := Real.sq_sqrt h2.le
    have ht' : |t ^ 2 - 2 * c.ε| ≤ 6 * c.βmax := by
      rw [ht2, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    obtain ⟨-, hΨ⟩ := c.qExtendedChart_p_ray htp ht'
    have hR : c.pRayAt s = recombine c.dp.hk 0 (t • c.e₁) := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hR, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        ModelField.posPart_recombine, ModelField.negPart_recombine, norm_smul, he₁,
        Real.norm_eq_abs, abs_of_pos htp]
      simp only [norm_zero]
      rw [mul_one, ht2]
      ring
    · rw [hR, ModelField.negPart_recombine]
    · rw [hR, hΨ, ModelField.posPart_recombine]
    · rw [hR, hΨ]
      unfold TransverseCancellingPair.qPerp TransverseCancellingPair.qArc
      rw [ModelField.negPart_recombine, real_inner_smul_left, real_inner_self_eq_norm_sq, hu₀]
      simp
    · rw [hR]
      unfold TransverseCancellingPair.pPerp TransverseCancellingPair.pArc
      rw [ModelField.posPart_recombine, real_inner_smul_left, real_inner_self_eq_norm_sq, he₁]
      simp
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hσc : ContinuousOn c.pRayAt (Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀)) := by
    have : c.pRayAt = fun s => ModelField.recombineL c.dp.hk
        ((0 : EuclideanSpace ℝ (Fin c.dp.k)), Real.sqrt (2 * (s - f p)) • c.e₁) := by
      funext s
      rw [ModelField.recombineL_apply]
      rfl
    rw [this]
    exact ((ModelField.recombineL c.dp.hk).continuous.comp (by fun_prop)).continuousOn
  have hN : ContDiffOn ℝ 2 (morseNormalForm c.dp.hk (f p)) W :=
    ((ModelField.contDiff_nf c.dp.hk (f p)).of_le h2le).contDiffOn
  have ha : ContDiffOn ℝ 2 (negPart c.dp.hk) W :=
    (ModelField.negPartL c.dp.hk).contDiff.contDiffOn
  have hT : ContDiffOn ℝ 2 (fun y => c.qExtendedChart (c.dp.χ y)) W := hsm.of_le h2le
  have hb : ContDiffOn ℝ 2 (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) W :=
    (ModelField.posPartL c.dq.hk).contDiff.comp_contDiffOn hT
  have hpP : ContDiffOn ℝ 2 c.pPerp W := by
    have h1 : ContDiff ℝ 2 (posPart c.dp.hk) := (ModelField.posPartL c.dp.hk).contDiff
    have : ContDiff ℝ 2 (fun y => posPart c.dp.hk y - ⟪posPart c.dp.hk y, c.e₁⟫ • c.e₁) :=
      h1.sub ((h1.inner ℝ contDiff_const).smul contDiff_const)
    exact this.contDiffOn
  have hqP : ContDiffOn ℝ 2 (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) W := by
    have h1 : ContDiff ℝ 2 (negPart c.dq.hk) := (ModelField.negPartL c.dq.hk).contDiff
    have : ContDiff ℝ 2 (fun y => negPart c.dq.hk y - ⟪negPart c.dq.hk y, c.u₀⟫ • c.u₀) :=
      h1.sub ((h1.inner ℝ contDiff_const).smul contDiff_const)
    exact this.comp_contDiffOn hT
  have hΦ : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
      fderiv ℝ (negPart c.dp.hk) (c.pRayAt s) w = 0 →
      fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (c.pRayAt s) w = 0 → w = 0 := by
    intro s hs w h1 h2 h3
    have hfd : fderiv ℝ (negPart c.dp.hk) (c.pRayAt s) = ModelField.negPartL c.dp.hk :=
      (ModelField.negPartL c.dp.hk).fderiv
    rw [hfd] at h2
    exact hinj s hs w h1 h2 h3
  obtain ⟨r, C, hr, hC, hbd⟩ := exists_transverse_bound hWo hσc hσW hN ha hb
    (fun s hs => ⟨(hray s hs).1, (hray s hs).2.1, (hray s hs).2.2.1⟩) hΦ
  have hK : IsCompact (c.pRayAt '' Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀)) :=
    isCompact_Icc.image_of_continuousOn hσc
  have hKW : c.pRayAt '' Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀) ⊆ W := by
    rintro _ ⟨s, hs, rfl⟩
    exact hσW s hs
  have lip : ∀ {m : ℕ} (φ : (Fin n → ℝ) → EuclideanSpace ℝ (Fin m)), ContDiffOn ℝ 2 φ W →
      (∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), φ (c.pRayAt s) = 0) →
      ∃ r' L : ℝ, 0 < r' ∧ 0 ≤ L ∧ ∀ y : Fin n → ℝ,
        morseNormalForm c.dp.hk (f p) y ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀) →
        ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ r' →
          ‖φ y‖ ≤ L * ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ := by
    intro m φ hφ hφ0
    obtain ⟨r₁, C₁, hr₁, hC₁, htay⟩ := exists_uniform_taylor hWo hφ hK hKW
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((hφ.continuousOn_fderiv_of_isOpen hWo (by exact_mod_cast (by norm_num : (1 : ℕ∞) ≤ 2))).mono hKW)
    refine ⟨r₁, max B 0 + C₁ * r₁, hr₁, by positivity, ?_⟩
    intro y hy hyr
    set y' := c.pRayAt (morseNormalForm c.dp.hk (f p) y) with hy'
    have hy'K : y' ∈ c.pRayAt '' Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀) := ⟨_, hy, rfl⟩
    obtain ⟨-, h1, -⟩ := htay y' hy'K y hyr
    rw [hφ0 _ hy, sub_zero] at h1
    have h2 : ‖fderiv ℝ φ y' (y - y')‖ ≤ max B 0 * ‖y - y'‖ :=
      ((fderiv ℝ φ y').le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((hB y' hy'K).trans (le_max_left _ _)) (norm_nonneg _))
    have h3 : ‖φ y‖ ≤ ‖φ y - fderiv ℝ φ y' (y - y')‖ + ‖fderiv ℝ φ y' (y - y')‖ := by
      simpa using norm_add_le (φ y - fderiv ℝ φ y' (y - y')) (fderiv ℝ φ y' (y - y'))
    have h4 : C₁ * ‖y - y'‖ ^ 2 ≤ C₁ * r₁ * ‖y - y'‖ := by
      calc C₁ * ‖y - y'‖ ^ 2 = (C₁ * ‖y - y'‖) * ‖y - y'‖ := by ring
        _ ≤ (C₁ * ‖y - y'‖) * r₁ := mul_le_mul_of_nonneg_left hyr (by positivity)
        _ = C₁ * r₁ * ‖y - y'‖ := by ring
    have h5 : (max B 0 + C₁ * r₁) * ‖y - y'‖ = max B 0 * ‖y - y'‖ + C₁ * r₁ * ‖y - y'‖ := by
      ring
    linarith
  obtain ⟨r₁, L₁, hr₁, hL₁, hlip₁⟩ := lip c.pPerp hpP (fun s hs => (hray s hs).2.2.2.2)
  obtain ⟨r₂, L₂, hr₂, hL₂, hlip₂⟩ := lip (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) hqP
    (fun s hs => (hray s hs).2.2.2.1)
  set K : ℝ := 2 * C ^ 2 * (L₁ ^ 2 + L₂ ^ 2) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨1 / (K + 1), β₀, min r (min r₁ r₂), by positivity, hβ₀, hβm,
    lt_min hr (lt_min hr₁ hr₂), ?_⟩
  intro η hη y hlev hdist
  have hyI : morseNormalForm c.dp.hk (f p) y ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hlev
    constructor <;> linarith
  obtain ⟨hyW, hyd⟩ := hbd y hyI (hdist.trans (min_le_left _ _))
  refine ⟨(hWp y hyW).2.2.1, ?_⟩
  have hp := hlip₁ y hyI (hdist.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq := hlip₂ y hyI (hdist.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set d := ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ with hd
  set A := ‖negPart c.dp.hk y‖ with hA
  set B := ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ with hB
  set P := ‖c.pPerp y‖ with hP
  set Q := ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ with hQ
  have hd0 : 0 ≤ d := norm_nonneg _
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hP0 : 0 ≤ P := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  have hP2 : P ^ 2 ≤ L₁ ^ 2 * d ^ 2 := by
    have := pow_le_pow_left₀ hP0 hp 2
    rwa [mul_pow] at this
  have hQ2 : Q ^ 2 ≤ L₂ ^ 2 * d ^ 2 := by
    have := pow_le_pow_left₀ hQ0 hq 2
    rwa [mul_pow] at this
  have hd2 : d ^ 2 ≤ 2 * C ^ 2 * (A ^ 2 + B ^ 2) := by
    have h1 := pow_le_pow_left₀ hd0 hyd 2
    have h2 : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by nlinarith only [sq_nonneg (A - B)]
    calc d ^ 2 ≤ (C * (A + B)) ^ 2 := h1
      _ = C ^ 2 * (A + B) ^ 2 := by ring
      _ ≤ C ^ 2 * (2 * (A ^ 2 + B ^ 2)) := mul_le_mul_of_nonneg_left h2 (sq_nonneg C)
      _ = 2 * C ^ 2 * (A ^ 2 + B ^ 2) := by ring
  have hsum : P ^ 2 + Q ^ 2 ≤ K * (A ^ 2 + B ^ 2) := by
    calc P ^ 2 + Q ^ 2 ≤ L₁ ^ 2 * d ^ 2 + L₂ ^ 2 * d ^ 2 := add_le_add hP2 hQ2
      _ = (L₁ ^ 2 + L₂ ^ 2) * d ^ 2 := by ring
      _ ≤ (L₁ ^ 2 + L₂ ^ 2) * (2 * C ^ 2 * (A ^ 2 + B ^ 2)) :=
          mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ = K * (A ^ 2 + B ^ 2) := by rw [hKdef]; ring
  have hη0 : 0 < η := hη.1
  have hηK : η * K ≤ 1 := by
    have h1 : η ≤ 1 / (K + 1) := hη.2
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : η * (K + 1) = η * K + η := by ring
    linarith
  have hfin : η * (P ^ 2 + Q ^ 2) ≤ A ^ 2 + B ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsum hη0.le
    have h2 : η * K * (A ^ 2 + B ^ 2) ≤ A ^ 2 + B ^ 2 := by
      have := mul_le_mul_of_nonneg_right hηK (by positivity : (0 : ℝ) ≤ A ^ 2 + B ^ 2)
      linarith
    have h3 : η * (K * (A ^ 2 + B ^ 2)) = η * K * (A ^ 2 + B ^ 2) := by ring
    linarith
  unfold TransverseCancellingPair.qQuad TransverseCancellingPair.pQuad
  rw [← hP, ← hQ, ← hA, ← hB]
  have h4 : η * (P ^ 2 + Q ^ 2) = η * P ^ 2 + η * Q ^ 2 := by ring
  linarith

theorem band_common_ascent :
    ∃ η₀ β₀ : ℝ, 0 < η₀ ∧ 0 < β₀ ∧ β₀ ≤ c.βmax ∧ ∀ η ∈ Ioc 0 η₀, ∃ r₀ μ₀ : ℝ, 0 < r₀ ∧ 0 < μ₀ ∧
      ∀ μ ∈ Ioc 0 μ₀, ∀ y : Fin n → ℝ, |morseNormalForm c.dp.hk (f p) y - c.fb| ≤ 3 * β₀ →
        ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ r₀ →
        y ≠ c.pRayAt (morseNormalForm c.dp.hk (f p) y) →
          ∃ w : Fin n → ℝ, fderiv ℝ (morseNormalForm c.dp.hk (f p)) y w = 0 ∧
            0 < fderiv ℝ (fun y => c.pQuad η y + μ * c.pArc y) y w ∧
            0 < fderiv ℝ (fun y => c.qQuad η (c.qExtendedChart (c.dp.χ y)) +
              μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) y w := by
  classical
  have hε := c.hε
  obtain ⟨he₁, hu₀, -⟩ := c.unit_dirs
  have hβm1 : c.βmax ≤ c.ε / 16 := (min_le_left _ _).trans (min_le_left _ _)
  have hβm2 : c.βmax ≤ (f q - f p - 2 * c.ε) / 16 := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨β₀, hβ₀, hβ₀m, W, hWo, hσW, -, hWprop, hTW, hΦW⟩ := c.band_setup
  have hdqk : c.dq.k = c.dp.k + 1 := by
    have h1 := c.dq.hkidx
    have h2 := c.dp.hkidx
    have h3 := c.hidx
    omega
  let pArcL : (Fin n → ℝ) →L[ℝ] ℝ := (innerSL ℝ c.e₁).comp (ModelField.posPartL c.dp.hk)
  have hpArcL : ∀ y, c.pArc y = pArcL y := fun y => by
    simp only [pArcL, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ModelField.posPartL_apply, TransverseCancellingPair.pArc]
    exact real_inner_comm _ _
  let pPerpL : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n - c.dp.k)) :=
    ModelField.posPartL c.dp.hk - pArcL.smulRight c.e₁
  have hpPerpL : ∀ y, c.pPerp y = pPerpL y := fun y => by
    simp only [pPerpL, sub_apply, ContinuousLinearMap.smulRight_apply,
      ModelField.posPartL_apply, TransverseCancellingPair.pPerp, ← hpArcL]
  let qArcL : (Fin n → ℝ) →L[ℝ] ℝ := (innerSL ℝ c.u₀).comp (ModelField.negPartL c.dq.hk)
  have hqArcL : ∀ y, c.qArc y = qArcL y := fun y => by
    simp only [qArcL, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ModelField.negPartL_apply, TransverseCancellingPair.qArc]
    exact real_inner_comm _ _
  let qPerpL : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin c.dq.k) :=
    ModelField.negPartL c.dq.hk - qArcL.smulRight c.u₀
  have hqPerpL : ∀ y, c.qPerp y = qPerpL y := fun y => by
    simp only [qPerpL, sub_apply, ContinuousLinearMap.smulRight_apply,
      ModelField.negPartL_apply, TransverseCancellingPair.qPerp, ← hqArcL]
  have hpArcF : c.pArc = ⇑pArcL := funext hpArcL
  have hpPerpF : c.pPerp = ⇑pPerpL := funext hpPerpL
  have hqArcF : c.qArc = ⇑qArcL := funext hqArcL
  have hqPerpF : c.qPerp = ⇑qPerpL := funext hqPerpL
  have hnegF : ∀ y, fderiv ℝ (negPart c.dp.hk) y = ModelField.negPartL c.dp.hk := fun y =>
    (ModelField.negPartL c.dp.hk).fderiv
  have hrec0 : ∀ {k : ℕ} (hk : k ≤ n), recombine hk 0 0 = 0 := fun hk => by
    rw [← ModelField.recombineL_apply, Prod.mk_zero_zero, map_zero]
  have hWnf : ∀ y ∈ W, morseNormalForm c.dp.hk (f p) y =
      morseNormalForm c.dq.hk (f q) (c.qExtendedChart (c.dp.χ y)) := by
    intro y hy
    obtain ⟨-, hy1, hy2, -, -⟩ := hWprop y hy
    rw [c.nf_qExtendedChart (Or.inr hy2), c.dp.hnorm y (hy1.le.trans (c.D.hrm p (mem_pair_left p q)).2)]
  have hTd : ∀ y ∈ W, DifferentiableAt ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y := fun y hy =>
    (hTW.differentiableOn (by simp)).differentiableAt (hWo.mem_nhds hy)
  have hTinj : ∀ y ∈ W, Function.Injective (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y) := by
    intro y hy
    obtain ⟨-, hy1, hy2, -, -⟩ := hWprop y hy
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' :=
      mem_ball_of_morseNorm_lt (hy1.trans (c.D.rm_lt_R' p (mem_pair_left p q)))
    have hdom : c.dp.χ y ∈ c.qDom := Or.inr hy2
    have hχd := c.dp.mdifferentiableAt_chart hyb
    have hΨd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ y) :=
      ((c.contMDiffOn_qExtendedChart.2).contMDiffAt (c.contMDiffOn_qExtendedChart.1.mem_nhds hdom)).mdifferentiableAt
        (by simp)
    have hcomp := mfderiv_comp y hΨd hχd
    have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (c.qExtendedChart ∘ c.dp.χ) y =
        fderiv ℝ (c.qExtendedChart ∘ c.dp.χ) y := mfderiv_eq_fderiv
    have hsurj : Function.Surjective (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y) := by
      intro v
      obtain ⟨v1, hv1⟩ := c.surjective_mfderiv_qExtendedChart hdom v
      refine ⟨(mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y) v1 : Fin n → ℝ), ?_⟩
      have h2 := MorseNormalChart.mfderiv_chart_symm_apply (d := c.dp) hyb v1
      change fderiv ℝ (c.qExtendedChart ∘ c.dp.χ) y _ = v
      rw [← h1, hcomp]
      change mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ y) (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y) v1)) = v
      rw [h2, hv1]
    exact (LinearMap.injective_iff_surjective
      (f := (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))).2 hsurj
  have hNq : ∀ y ∈ W, ∀ w, fderiv ℝ (morseNormalForm c.dp.hk (f p)) y w =
      ⟪posPart c.dq.hk (c.qExtendedChart (c.dp.χ y)),
          posPart c.dq.hk (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y w)⟫ -
        ⟪negPart c.dq.hk (c.qExtendedChart (c.dp.χ y)),
          negPart c.dq.hk (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y w)⟫ := by
    intro y hy w
    have hev : morseNormalForm c.dp.hk (f p) =ᶠ[𝓝 y]
        (fun z => morseNormalForm c.dq.hk (f q) (c.qExtendedChart (c.dp.χ z))) :=
      Filter.eventuallyEq_of_mem (hWo.mem_nhds hy) hWnf
    rw [hev.fderiv_eq]
    have hd : HasFDerivAt (fun z => morseNormalForm c.dq.hk (f q) (c.qExtendedChart (c.dp.χ z)))
        ((ModelField.nfDeriv c.dq.hk (c.qExtendedChart (c.dp.χ y))).comp
          (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y)) y :=
      by
        have h := (ModelField.hasFDerivAt_nf c.dq.hk (f q) (c.qExtendedChart (c.dp.χ y))).comp y
          (hTd y hy).hasFDerivAt
        exact h
    rw [hd.fderiv]
    rfl
  have hbd : ∀ y ∈ W, ∀ w, fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) y w =
      posPart c.dq.hk (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y w) := by
    intro y hy w
    have hd : HasFDerivAt (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y)))
        ((ModelField.posPartL c.dq.hk).comp (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y)) y :=
      (ModelField.posPartL c.dq.hk).hasFDerivAt.comp y (hTd y hy).hasFDerivAt
    rw [hd.fderiv]
    rfl
  have hhd : ∀ y ∈ W, ∀ w, fderiv ℝ (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) y w =
      qPerpL (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y w) := by
    intro y hy w
    have hd : HasFDerivAt (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y)))
        (qPerpL.comp (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) y)) y := by
      rw [hqPerpF]
      exact qPerpL.hasFDerivAt.comp y (hTd y hy).hasFDerivAt
    rw [hd.fderiv]
    rfl
  have hsq : c.sqSum = 2 * (f q - f p) := by
    simp only [TransverseCancellingPair.sqSum, TransverseCancellingPair.cq, TransverseCancellingPair.fb]; ring
  have hray : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀),
      0 < Real.sqrt (2 * (s - f p)) ∧
      |Real.sqrt (2 * (s - f p)) ^ 2 - 2 * c.ε| ≤ 6 * c.βmax ∧
      Real.sqrt (2 * (s - f p)) ^ 2 = 2 * (s - f p) ∧
      0 < c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2 := by
    intro s hs
    have hfb : c.fb = f p + c.ε := rfl
    have hs1 := hs.1
    have hs2 := hs.2
    rw [hfb] at hs1 hs2
    have h2 : Real.sqrt (2 * (s - f p)) ^ 2 = 2 * (s - f p) := Real.sq_sqrt (by linarith)
    refine ⟨Real.sqrt_pos.2 (by linarith), ?_, h2, ?_⟩
    · rw [h2, abs_le]; constructor <;> linarith
    · rw [h2, hsq]; linarith
  have hσneg : ∀ s, negPart c.dp.hk (c.pRayAt s) = 0 := fun s =>
    ModelField.negPart_recombine c.dp.hk _ _
  have hσpos : ∀ s, posPart c.dp.hk (c.pRayAt s) = Real.sqrt (2 * (s - f p)) • c.e₁ := fun s =>
    ModelField.posPart_recombine c.dp.hk _ _
  have hTσ : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀),
      c.qExtendedChart (c.dp.χ (c.pRayAt s)) =
        recombine c.dq.hk (Real.sqrt (c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2) • c.u₀) 0 :=
    fun s hs => (c.qExtendedChart_p_ray (hray s hs).1 (hray s hs).2.1).2
  have hNσ : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w =
        Real.sqrt (2 * (s - f p)) * pArcL w := by
    intro s hs w
    rw [ModelField.fderiv_nf_apply, hσpos, hσneg, inner_zero_left, sub_zero,
      real_inner_smul_left]
    rfl
  have hNσq : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w =
        -(Real.sqrt (c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2) *
          qArcL (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w)) := by
    intro s hs w
    rw [hNq _ (hσW s hs), hTσ s hs, ModelField.posPart_recombine, ModelField.negPart_recombine,
      inner_zero_left, zero_sub, real_inner_smul_left]
    rfl
  have hσc : ContinuousOn c.pRayAt (Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀)) := by
    have h : c.pRayAt = fun s =>
        ModelField.recombineL c.dp.hk (0, Real.sqrt (2 * (s - f p)) • c.e₁) := by
      funext s
      rw [ModelField.recombineL_apply]
      rfl
    rw [h]
    exact ((ModelField.recombineL c.dp.hk).continuous.comp (continuous_const.prodMk
      ((Real.continuous_sqrt.comp (continuous_const.mul (continuous_id.sub continuous_const))).smul
        continuous_const))).continuousOn
  have hdim : Module.finrank ℝ (Fin n → ℝ) =
      1 + Module.finrank ℝ (EuclideanSpace ℝ (Fin c.dp.k)) +
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - c.dq.k))) := by
    rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    have := c.dq.hk
    omega
  have hN : ContDiffOn ℝ 2 (morseNormalForm c.dp.hk (f p)) W :=
    ((ModelField.contDiff_nf c.dp.hk (f p)).of_le (by decide)).contDiffOn
  have ha : ContDiffOn ℝ 2 (negPart c.dp.hk) W :=
    (ModelField.negPartL c.dp.hk).contDiff.contDiffOn
  have hT2 : ContDiffOn ℝ 2 (fun y => c.qExtendedChart (c.dp.χ y)) W := hTW.of_le (by decide)
  have hb : ContDiffOn ℝ 2 (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) W :=
    (ModelField.posPartL c.dq.hk).contDiff.comp_contDiffOn hT2
  have hg : ContDiffOn ℝ 2 c.pPerp W := by
    rw [hpPerpF]; exact pPerpL.contDiff.contDiffOn
  have hh : ContDiffOn ℝ 2 (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) W := by
    rw [hqPerpF]; exact qPerpL.contDiff.comp_contDiffOn hT2
  have hA₁ : ContDiffOn ℝ 2 c.pArc W := by
    rw [hpArcF]; exact pArcL.contDiff.contDiffOn
  have hρq : 0 ≤ c.ρq := Real.sqrt_nonneg _
  have hA₂ : ContDiffOn ℝ 2 (fun y => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) W := by
    intro y hy
    obtain ⟨-, -, -, h0, hsq'⟩ := hWprop y hy
    have hHc : ContDiffAt ℝ 2 c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) :=
      (c.qHeightProfile_spec.1 _ (by linarith) hsq').1.of_le (by decide)
    have hqc : ContDiffOn ℝ 2 (fun y => c.qArc (c.qExtendedChart (c.dp.χ y))) W := by
      rw [hqArcF]; exact qArcL.contDiff.comp_contDiffOn hT2
    exact hHc.comp_contDiffWithinAt y (hqc y hy)
  have hσs : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀),
      morseNormalForm c.dp.hk (f p) (c.pRayAt s) = s ∧ negPart c.dp.hk (c.pRayAt s) = 0 ∧
        posPart c.dq.hk (c.qExtendedChart (c.dp.χ (c.pRayAt s))) = 0 ∧ c.pPerp (c.pRayAt s) = 0 ∧
        c.qPerp (c.qExtendedChart (c.dp.χ (c.pRayAt s))) = 0 := by
    intro s hs
    have hpa : c.pArc (c.pRayAt s) = Real.sqrt (2 * (s - f p)) := by
      rw [TransverseCancellingPair.pArc, hσpos, real_inner_smul_left, real_inner_self_eq_norm_sq, he₁]
      ring
    have hqa : c.qArc (recombine c.dq.hk (Real.sqrt (c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2) •
        c.u₀) 0) = Real.sqrt (c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2) := by
      rw [TransverseCancellingPair.qArc, ModelField.negPart_recombine, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hu₀]
      ring
    refine ⟨?_, hσneg s, ?_, ?_, ?_⟩
    · rw [Topology.Morse.CellAttachment.morseNormalForm_split, hσneg, hσpos, norm_smul, mul_pow, he₁, norm_zero,
        Real.norm_eq_abs, sq_abs, (hray s hs).2.2.1]
      ring
    · rw [hTσ s hs, ModelField.posPart_recombine]
    · rw [TransverseCancellingPair.pPerp, hpa, hσpos, sub_self]
    · rw [hTσ s hs, TransverseCancellingPair.qPerp, hqa, ModelField.negPart_recombine, sub_self]
  have hΦ : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
        fderiv ℝ (negPart c.dp.hk) (c.pRayAt s) w = 0 →
        fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (c.pRayAt s) w = 0 → w = 0 := by
    intro s hs w h1 h2 h3
    rw [hnegF] at h2
    exact hΦW s hs w h1 h2 h3
  have hlev : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
        pArcL w = 0 ∧ qArcL (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w) = 0 := by
    intro s hs w h1
    have h1' := h1
    rw [hNσ s hs] at h1
    rw [hNσq s hs, neg_eq_zero] at h1'
    have hS : 0 < Real.sqrt (c.sqSum - Real.sqrt (2 * (s - f p)) ^ 2) :=
      Real.sqrt_pos.2 (hray s hs).2.2.2
    exact ⟨(mul_eq_zero.1 h1).resolve_left (hray s hs).1.ne',
      (mul_eq_zero.1 h1').resolve_left hS.ne'⟩
  have hgi : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
        fderiv ℝ (negPart c.dp.hk) (c.pRayAt s) w = 0 →
        fderiv ℝ c.pPerp (c.pRayAt s) w = 0 → w = 0 := by
    intro s hs w h1 h2 h3
    have hp := (hlev s hs w h1).1
    rw [hnegF] at h2
    rw [hpPerpF, pPerpL.fderiv] at h3
    have h2' : negPart c.dp.hk w = 0 := h2
    have h3' : posPart c.dp.hk w - pArcL w • c.e₁ = 0 := h3
    rw [hp, zero_smul, sub_zero] at h3'
    rw [← Topology.Morse.CellAttachment.recombine_decompose c.dp.hk w, h2', h3', hrec0]
  have hhi : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
        fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (c.pRayAt s) w = 0 →
        fderiv ℝ (fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) (c.pRayAt s) w = 0 → w = 0 := by
    intro s hs w h1 h2 h3
    have hq := (hlev s hs w h1).2
    rw [hbd _ (hσW s hs)] at h2
    rw [hhd _ (hσW s hs)] at h3
    have h3' : negPart c.dq.hk (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w) -
        qArcL (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w) • c.u₀ = 0 := h3
    rw [hq, zero_smul, sub_zero] at h3'
    have hv : fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w = 0 := by
      rw [← Topology.Morse.CellAttachment.recombine_decompose c.dq.hk (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s) w), h2,
        h3', hrec0]
    exact hTinj _ (hσW s hs) (hv.trans (map_zero _).symm)
  have hA : ∀ s ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀), ∀ w : Fin n → ℝ,
      fderiv ℝ (morseNormalForm c.dp.hk (f p)) (c.pRayAt s) w = 0 →
        fderiv ℝ c.pArc (c.pRayAt s) w = 0 ∧
          fderiv ℝ (fun y => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) (c.pRayAt s) w = 0 := by
    intro s hs w h1
    obtain ⟨hp, hq⟩ := hlev s hs w h1
    refine ⟨?_, ?_⟩
    · rw [hpArcF, pArcL.fderiv]; exact hp
    · obtain ⟨-, -, -, h0, hsq'⟩ := hWprop _ (hσW s hs)
      have hHd : HasDerivAt c.qHeightProfile (deriv c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s)))))
          (c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s)))) :=
        ((c.qHeightProfile_spec.1 _ (by linarith) hsq').1.differentiableAt (by simp)).hasDerivAt
      have hqa : HasFDerivAt (fun z => c.qArc (c.qExtendedChart (c.dp.χ z)))
          (qArcL.comp (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s))) (c.pRayAt s) := by
        rw [hqArcF]
        have h := qArcL.hasFDerivAt.comp (c.pRayAt s) (hTd _ (hσW s hs)).hasFDerivAt
        exact h
      have hd := hHd.comp_hasFDerivAt (c.pRayAt s) hqa
      have hd' : HasFDerivAt (fun y => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))))
          (deriv c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ (c.pRayAt s)))) •
            qArcL.comp (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) (c.pRayAt s))) (c.pRayAt s) := hd
      rw [hd'.fderiv, smul_apply, ContinuousLinearMap.comp_apply, hq,
        smul_zero]
  obtain ⟨η₀, hη₀, hasc⟩ := exists_reflection_ascent (N := morseNormalForm c.dp.hk (f p))
    (a := negPart c.dp.hk) (b := fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (g := c.pPerp)
    (h := fun y => c.qPerp (c.qExtendedChart (c.dp.χ y))) (A₁ := c.pArc)
    (A₂ := fun y => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) (σ := c.pRayAt) hWo hσc hσW hdim hN ha hb
    hg hh hA₁ hA₂ hσs hΦ hgi hhi hA
  obtain ⟨r', C, hr', -, htb⟩ := exists_transverse_bound (N := morseNormalForm c.dp.hk (f p))
    (a := negPart c.dp.hk) (b := fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (σ := c.pRayAt)
    hWo hσc hσW hN ha hb (fun s hs => ⟨(hσs s hs).1, (hσs s hs).2.1, (hσs s hs).2.2.1⟩) hΦ
  refine ⟨η₀, β₀, hη₀, hβ₀, hβ₀m, fun η hη => ?_⟩
  obtain ⟨r, μ₀, hr, hμ₀, hmain⟩ := hasc η hη
  refine ⟨min r r', μ₀, lt_min hr hr', hμ₀, fun μ hμ y hy1 hy2 hy3 => ?_⟩
  have hyI : morseNormalForm c.dp.hk (f p) y ∈ Icc (c.fb - 3 * β₀) (c.fb + 3 * β₀) := by
    rw [abs_le] at hy1
    constructor <;> linarith [hy1.1, hy1.2]
  have hab : negPart c.dp.hk y ≠ 0 ∨ posPart c.dq.hk (c.qExtendedChart (c.dp.χ y)) ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨-, hle⟩ := htb y hyI (hy2.trans (min_le_right _ _))
    rw [hcon.1, hcon.2, norm_zero, norm_zero, add_zero, mul_zero] at hle
    exact hy3 (sub_eq_zero.1 (norm_le_zero_iff.1 hle))
  obtain ⟨w, hw1, hw2, hw3⟩ := hmain μ hμ y hyI (hy2.trans (min_le_left _ _)) hab
  exact ⟨w, hw1, hw2, hw3⟩

theorem band_glue_deriv {η β μ : ℝ} (hβ : 0 < β) {y : Fin n → ℝ} (hyR : morseNorm n y < c.dp.R)
    (hyT : c.dp.χ y ∈ c.qTube) (hq : c.qArc (c.qExtendedChart (c.dp.χ y)) ^ 2 < c.sqSum)
    (w : Fin n → ℝ) :
    mfderiv I 𝓘(ℝ, ℝ) (fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x) (c.dp.χ y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y w) =
      (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) *
          fderiv ℝ (fun z => c.pQuad η z + μ * c.pArc z) y w +
        c.κ β (morseNormalForm c.dp.hk (f p) y) *
          fderiv ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z)) +
            μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y w +
        deriv (c.κ β) (morseNormalForm c.dp.hk (f p) y) *
          fderiv ℝ (morseNormalForm c.dp.hk (f p)) y w *
          ((c.qQuad η (c.qExtendedChart (c.dp.χ y)) + μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) -
            (c.pQuad η y + μ * c.pArc y)) := by
  classical
  have _hβ : 0 < β := hβ
  set nf : (Fin n → ℝ) → ℝ := morseNormalForm c.dp.hk (f p) with hnf_def
  set Gp : (Fin n → ℝ) → ℝ := fun z => c.pQuad η z + μ * c.pArc z with hGp_def
  set Gq : (Fin n → ℝ) → ℝ := fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z)) +
    μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z))) with hGq_def
  set G : (Fin n → ℝ) → ℝ := fun z =>
    (1 - c.κ β (nf z)) * Gp z + c.κ β (nf z) * Gq z with hG_def
  set F : M → ℝ := fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x with hF_def
  have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' := c.dp.mem_ball_of_le hyR.le
  have hysrc : y ∈ c.dp.χ.source := c.dp.hsrc y hyR.le
  have hopenR : IsOpen {z : Fin n → ℝ | morseNorm n z < c.dp.R} := isOpen_morseNorm_lt _
  have hFG : ∀ z : Fin n → ℝ, morseNorm n z < c.dp.R → F (c.dp.χ z) = G z := by
    intro z hz
    have hzs : c.dp.χ.symm (c.dp.χ z) = z := c.dp.χ.left_inv (c.dp.hsrc z hz.le)
    have hfz : f (c.dp.χ z) = nf z := c.dp.hnorm z hz.le
    simp only [hF_def, hG_def, hGp_def, hGq_def, TransverseCancellingPair.blendedQuadraticFunction, TransverseCancellingPair.blendedArcCoordinate, hzs, hfz]
    ring
  have hFGev : (F ∘ c.dp.χ) =ᶠ[𝓝 y] G :=
    Filter.eventually_of_mem (hopenR.mem_nhds hyR) fun z hz => hFG z hz
  have hnegL : Differentiable ℝ (fun z : Fin n → ℝ => negPart c.dp.hk z) :=
    (ModelField.negPartL c.dp.hk).differentiable
  have hposL : Differentiable ℝ (fun z : Fin n → ℝ => posPart c.dp.hk z) :=
    (ModelField.posPartL c.dp.hk).differentiable
  have hnegLq : Differentiable ℝ (fun z : Fin n → ℝ => negPart c.dq.hk z) :=
    (ModelField.negPartL c.dq.hk).differentiable
  have hposLq : Differentiable ℝ (fun z : Fin n → ℝ => posPart c.dq.hk z) :=
    (ModelField.posPartL c.dq.hk).differentiable
  have hpArc : Differentiable ℝ c.pArc := by
    intro z
    unfold TransverseCancellingPair.pArc
    exact (hposL z).inner ℝ (differentiableAt_const _)
  have hpQuad : Differentiable ℝ (c.pQuad η) := by
    intro z
    unfold TransverseCancellingPair.pQuad TransverseCancellingPair.pPerp
    exact ((hnegL z).norm_sq ℝ).sub
      ((((hposL z).sub ((hpArc z).smul_const c.e₁)).norm_sq ℝ).const_mul η)
  have hqArc : Differentiable ℝ c.qArc := by
    intro z
    unfold TransverseCancellingPair.qArc
    exact (hnegLq z).inner ℝ (differentiableAt_const _)
  have hqQuad : Differentiable ℝ (c.qQuad η) := by
    intro z
    unfold TransverseCancellingPair.qQuad TransverseCancellingPair.qPerp
    exact ((((hnegLq z).sub ((hqArc z).smul_const c.u₀)).norm_sq ℝ).const_mul η).sub
      ((hposLq z).norm_sq ℝ)
  have hκ : Differentiable ℝ (c.κ β) := by
    intro s
    unfold TransverseCancellingPair.κ
    exact (differentiableAt_const _).sub
      ((CancelModel.contDiff_cut _ _).differentiable (by simp) s)
  have hHq : DifferentiableAt ℝ c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) := by
    unfold TransverseCancellingPair.qHeightProfile
    have hne : c.sqSum - c.qArc (c.qExtendedChart (c.dp.χ y)) ^ 2 ≠ 0 := by
      have := hq; intro h; linarith
    have h1 : DifferentiableAt ℝ (fun σ : ℝ => Real.sqrt (c.sqSum - σ ^ 2))
        (c.qArc (c.qExtendedChart (c.dp.χ y))) :=
      (by fun_prop : DifferentiableAt ℝ (fun σ : ℝ => c.sqSum - σ ^ 2) _).sqrt hne
    have h2 : DifferentiableAt ℝ (CancelModel.cut (Real.sqrt (2 * c.ε) / 2) (Real.sqrt (2 * c.ε)))
        (c.qArc (c.qExtendedChart (c.dp.χ y))) :=
      (CancelModel.contDiff_cut _ _).differentiable (by simp) _
    have h3 : DifferentiableAt ℝ (fun σ : ℝ => c.kH * (Real.sqrt (2 * c.ε) - σ))
        (c.qArc (c.qExtendedChart (c.dp.χ y))) := by fun_prop
    exact h1.add (h3.mul h2)
  have hχc : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ c.dp.χ y :=
    c.dp.hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds hyball)
  have hχm : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y := hχc.mdifferentiableAt (by simp)
  have hΨc : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.qExtendedChart (c.dp.χ y) :=
    c.contMDiffOn_qExtendedChart.2.contMDiffAt (c.contMDiffOn_qExtendedChart.1.mem_nhds (Set.mem_union_right _ hyT))
  have hΨχ : DifferentiableAt ℝ (fun z => c.qExtendedChart (c.dp.χ z)) y :=
    mdifferentiableAt_iff_differentiableAt.1 ((hΨc.comp y hχc).mdifferentiableAt (by simp))
  have hsymmc : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.dp.χ.symm (c.dp.χ y) :=
    c.dp.hχsymm.contMDiffAt (c.dp.isOpen_image_ball.mem_nhds ⟨y, hyball, rfl⟩)
  have hsymmm : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y) :=
    hsymmc.mdifferentiableAt (by simp)
  have hGpd : DifferentiableAt ℝ Gp y := (hpQuad y).add ((hpArc y).const_mul μ)
  have hGqd : DifferentiableAt ℝ Gq y := by
    have h1 : DifferentiableAt ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z))) y :=
      (hqQuad _).comp y hΨχ
    have h2 : DifferentiableAt ℝ (fun z => c.qArc (c.qExtendedChart (c.dp.χ z))) y :=
      (hqArc _).comp y hΨχ
    have h3 : DifferentiableAt ℝ (fun z => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y :=
      DifferentiableAt.comp (g := c.qHeightProfile) y hHq h2
    exact h1.add (h3.const_mul μ)
  have hnfd : HasFDerivAt nf (fderiv ℝ nf y) y :=
    ((ModelField.contDiff_nf c.dp.hk (f p)).differentiable (by simp) y).hasFDerivAt
  have hK : HasFDerivAt (fun z => c.κ β (nf z)) (deriv (c.κ β) (nf y) • fderiv ℝ nf y) y :=
    (hκ (nf y)).hasDerivAt.comp_hasFDerivAt y hnfd
  have hGfd : HasFDerivAt G
      (((1 - c.κ β (nf y)) • fderiv ℝ Gp y + Gp y • (-(deriv (c.κ β) (nf y) • fderiv ℝ nf y))) +
        (c.κ β (nf y) • fderiv ℝ Gq y + Gq y • (deriv (c.κ β) (nf y) • fderiv ℝ nf y))) y := by
    have hA := ((hasFDerivAt_const (1 : ℝ) y).sub hK).mul hGpd.hasFDerivAt
    have hB := hK.mul hGqd.hasFDerivAt
    convert hA.add hB using 1
    simp
  have hχy : c.dp.χ y ∈ c.dp.χ.target := c.dp.χ.map_source hysrc
  have hFev : F =ᶠ[𝓝 (c.dp.χ y)] G ∘ c.dp.χ.symm := by
    have h1 : c.dp.χ.target ∈ 𝓝 (c.dp.χ y) := c.dp.χ.open_target.mem_nhds hχy
    have h2 : c.dp.χ.symm ⁻¹' {z : Fin n → ℝ | morseNorm n z < c.dp.R} ∈ 𝓝 (c.dp.χ y) := by
      apply c.dp.χ.continuousAt_symm hχy
      rw [c.dp.χ.left_inv hysrc]
      exact hopenR.mem_nhds hyR
    filter_upwards [h1, h2] with x hx1 hx2
    have := hFG (c.dp.χ.symm x) hx2
    rw [c.dp.χ.right_inv hx1] at this
    exact this
  have hGm : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) G (c.dp.χ.symm (c.dp.χ y)) := by
    rw [c.dp.χ.left_inv hysrc]
    exact hGfd.differentiableAt.mdifferentiableAt
  have hFm : MDifferentiableAt I 𝓘(ℝ, ℝ) F (c.dp.χ y) :=
    (hGm.comp (c.dp.χ y) hsymmm).congr_of_eventuallyEq hFev
  have hchain : mfderiv I 𝓘(ℝ, ℝ) F (c.dp.χ y) (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y w) =
      fderiv ℝ G y w := by
    refine (mfderiv_comp_apply y hFm hχm w).symm.trans ?_
    rw [hFGev.mfderiv_eq, mfderiv_eq_fderiv]
    rfl
  change @Eq ℝ _ _
  rw [hchain, hGfd.fderiv]
  have hGpy : Gp y = c.pQuad η y + μ * c.pArc y := rfl
  have hGqy : Gq y = c.qQuad η (c.qExtendedChart (c.dp.χ y)) + μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) := rfl
  simp only [add_apply, smul_apply, smul_eq_mul,
    neg_apply]
  rw [hGpy, hGqy]
  ring

theorem band_dfV {η β : ℝ} (hβ : 0 < β) {y : Fin n → ℝ} (hy₀ : c.dp.r₀ < morseNorm n y)
    (hy₁ : morseNorm n y < c.D.rm p (mem_pair_left p q))
    (hlev : |morseNormalForm c.dp.hk (f p) y - c.fb| ≤ 3 * c.βmax) (hyT : c.dp.χ y ∈ c.qTube)
    (hq₀ : 0 < c.qArc (c.qExtendedChart (c.dp.χ y))) (hq : c.qArc (c.qExtendedChart (c.dp.χ y)) ^ 2 < c.sqSum) :
    dfV I (c.blendedQuadraticFunction η β) c.D.V (c.dp.χ y) =
        (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) * (ModelField.theta c.dp.r₀ y *
            (2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2)) +
          c.κ β (morseNormalForm c.dp.hk (f p) y) *
            (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
              (2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
                2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2)) +
          deriv (c.κ β) (morseNormalForm c.dp.hk (f p) y) *
            (c.pQuad η y - c.qQuad η (c.qExtendedChart (c.dp.χ y))) ∧
      dfV I (c.blendedArcCoordinate β) c.D.V (c.dp.χ y) =
        (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) *
            (-(ModelField.theta c.dp.r₀ y * c.pArc y)) +
          c.κ β (morseNormalForm c.dp.hk (f p) y) *
            (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
              (deriv c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) * c.qArc (c.qExtendedChart (c.dp.χ y)))) +
          deriv (c.κ β) (morseNormalForm c.dp.hk (f p) y) *
            (c.pArc y - c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y)))) := by
  have _hlev := hlev
  have hyR : morseNorm n y < c.dp.R := hy₁.trans_le (c.D.hrm p (mem_pair_left p q)).2
  have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' :=
    mem_ball_of_morseNorm_lt (hy₁.trans (c.D.rm_lt_R' p (mem_pair_left p q)))
  have hxImg : c.dp.χ y ∈ c.dp.χ '' Metric.ball 0 c.dp.R' := ⟨y, hyball, rfl⟩
  have hxDom : c.dp.χ y ∈ c.qDom := Or.inr hyT
  have hV : c.D.V (c.dp.χ y) = mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y
      (ModelField.modelField c.dp.k c.dp.r₀ y) :=
    GradientLikeStrip.V_chart_eq (D := c.D) p (mem_pair_left p q) hy₁
  have hr₀ : 0 < c.dp.r₀ := c.dp.hr₀
  have hnf : fderiv ℝ (morseNormalForm c.dp.hk (f p)) y
      (ModelField.modelField c.dp.k c.dp.r₀ y) = -1 :=
    ModelField.fderiv_nf_modelField_eq_neg_one c.dp.hk (f p) hr₀ (by linarith)
  have hnegD : ∀ {k : ℕ} (hk : k ≤ n), Differentiable ℝ (fun z : Fin n → ℝ => negPart hk z) :=
    fun hk => (ModelField.negPartL hk).differentiable
  have hposD : ∀ {k : ℕ} (hk : k ≤ n), Differentiable ℝ (fun z : Fin n → ℝ => posPart hk z) :=
    fun hk => (ModelField.posPartL hk).differentiable
  have hpArc : Differentiable ℝ c.pArc := fun z =>
    (hposD c.dp.hk z).inner ℝ (differentiableAt_const c.e₁)
  have hpPerp : Differentiable ℝ c.pPerp := fun z =>
    (hposD c.dp.hk z).sub ((hpArc z).smul_const c.e₁)
  have hpQ : Differentiable ℝ (c.pQuad η) := fun z =>
    ((hnegD c.dp.hk z).norm_sq ℝ).sub (((hpPerp z).norm_sq ℝ).const_mul η)
  have hqArc : Differentiable ℝ c.qArc := fun z =>
    (hnegD c.dq.hk z).inner ℝ (differentiableAt_const c.u₀)
  have hqPerp : Differentiable ℝ c.qPerp := fun z =>
    (hnegD c.dq.hk z).sub ((hqArc z).smul_const c.u₀)
  have hqQ : Differentiable ℝ (c.qQuad η) := fun z =>
    (((hqPerp z).norm_sq ℝ).const_mul η).sub ((hposD c.dq.hk z).norm_sq ℝ)
  have hρ : -c.ρq ≤ c.qArc (c.qExtendedChart (c.dp.χ y)) := by
    have : 0 ≤ c.ρq := Real.sqrt_nonneg _
    linarith
  have hHq : DifferentiableAt ℝ (fun w => c.qHeightProfile (c.qArc w)) (c.qExtendedChart (c.dp.χ y)) :=
    (((c.qHeightProfile_spec.1 _ hρ hq).1.differentiableAt (by simp))).comp _ (hqArc _)
  have hΨm : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ y) :=
    (c.contMDiffOn_qExtendedChart.2.contMDiffAt (c.contMDiffOn_qExtendedChart.1.mem_nhds hxDom)).mdifferentiableAt
      (by simp)
  have hχm := c.dp.mdifferentiableAt_chart hyball
  have hGm : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (c.qExtendedChart ∘ c.dp.χ) y :=
    hΨm.comp y hχm
  have hGd : DifferentiableAt ℝ (fun z => c.qExtendedChart (c.dp.χ z)) y :=
    mdifferentiableAt_iff_differentiableAt.1 hGm
  have hGfd : fderiv ℝ (fun z => c.qExtendedChart (c.dp.χ z)) y (ModelField.modelField c.dp.k c.dp.r₀ y) =
      ModelField.modelField c.dq.k c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) := by
    have hcomp := mfderiv_comp y hΨm hχm
    rw [mfderiv_eq_fderiv] at hcomp
    calc
      _ = (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ y))
          ((mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y)
            (ModelField.modelField c.dp.k c.dp.r₀ y)) := DFunLike.congr_fun hcomp _
      _ = _ := by rw [← hV, c.mfderiv_qExtendedChart_V hxDom]
  have hfq1 : fderiv ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z))) y
      (ModelField.modelField c.dp.k c.dp.r₀ y) =
      ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
        (2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
          2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2) := by
    change fderiv ℝ (c.qQuad η ∘ fun z => c.qExtendedChart (c.dp.χ z)) y _ = _
    rw [fderiv_comp y (hqQ _) hGd, ContinuousLinearMap.comp_apply, hGfd,
      c.fderiv_qQuad_modelField]
  have hfq2 : fderiv ℝ (fun z => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y
      (ModelField.modelField c.dp.k c.dp.r₀ y) =
      ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
        (deriv c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) * c.qArc (c.qExtendedChart (c.dp.χ y))) := by
    change fderiv ℝ ((fun w => c.qHeightProfile (c.qArc w)) ∘ fun z => c.qExtendedChart (c.dp.χ z)) y _ = _
    rw [fderiv_comp y hHq hGd, ContinuousLinearMap.comp_apply, hGfd,
      c.fderiv_qHeightProfile_qArc_modelField hρ hq]
  have hfp1 := c.fderiv_pQuad_modelField η y
  have hfp2 := c.fderiv_pArc_modelField y
  have h0 := c.band_glue_deriv (η := η) (μ := 0) hβ hyR hyT hq
    (ModelField.modelField c.dp.k c.dp.r₀ y)
  simp only [zero_mul, add_zero] at h0
  have hL0eq : (fun x => c.blendedQuadraticFunction η β x + 0 * c.blendedArcCoordinate β x) = c.blendedQuadraticFunction η β := funext fun x => by ring
  rw [hL0eq] at h0
  rw [hnf, hfp1, hfq1] at h0
  have hfm : MDifferentiableAt I 𝓘(ℝ, ℝ) f (c.dp.χ y) :=
    c.hf.smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hκ : Differentiable ℝ (c.κ β) :=
    (differentiable_const _).sub ((CancelModel.contDiff_cut _ _).differentiable (by simp))
  have hκm : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c.κ β (f x)) (c.dp.χ y) :=
    (hκ _).comp_mdifferentiableAt hfm
  have hχsm := c.dp.mdifferentiableAt_symm hxImg
  have hL : MDifferentiableAt I 𝓘(ℝ, ℝ) (c.blendedQuadraticFunction η β) (c.dp.χ y) := by
    have e1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c.pQuad η (c.dp.χ.symm x)) (c.dp.χ y) :=
      (hpQ _).comp_mdifferentiableAt hχsm
    have e2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c.qQuad η (c.qExtendedChart x)) (c.dp.χ y) :=
      (hqQ _).comp_mdifferentiableAt hΨm
    exact ((mdifferentiableAt_const.sub hκm).mul e1).add (hκm.mul e2)
  have hA : MDifferentiableAt I 𝓘(ℝ, ℝ) (c.blendedArcCoordinate β) (c.dp.χ y) := by
    have e1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c.pArc (c.dp.χ.symm x)) (c.dp.χ y) :=
      (hpArc _).comp_mdifferentiableAt hχsm
    have e2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c.qHeightProfile (c.qArc (c.qExtendedChart x))) (c.dp.χ y) :=
      hHq.comp_mdifferentiableAt hΨm
    exact ((mdifferentiableAt_const.sub hκm).mul e1).add (hκm.mul e2)
  have h1 := c.band_glue_deriv (η := η) (μ := 1) hβ hyR hyT hq
    (ModelField.modelField c.dp.k c.dp.r₀ y)
  simp only [one_mul] at h1
  have hadd : mfderiv I 𝓘(ℝ, ℝ) (fun x => c.blendedQuadraticFunction η β x + 1 * c.blendedArcCoordinate β x) (c.dp.χ y)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y (ModelField.modelField c.dp.k c.dp.r₀ y)) =
      @HAdd.hAdd ℝ ℝ ℝ _ (mfderiv I 𝓘(ℝ, ℝ) (c.blendedQuadraticFunction η β) (c.dp.χ y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y (ModelField.modelField c.dp.k c.dp.r₀ y)))
      (mfderiv I 𝓘(ℝ, ℝ) (c.blendedArcCoordinate β) (c.dp.χ y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y (ModelField.modelField c.dp.k c.dp.r₀ y))) := by
    rw [show (fun x => c.blendedQuadraticFunction η β x + 1 * c.blendedArcCoordinate β x) = c.blendedQuadraticFunction η β + c.blendedArcCoordinate β from
      funext fun x => by simp, mfderiv_add hL hA]
    rfl
  have hpadd : fderiv ℝ (fun z => c.pQuad η z + c.pArc z) y =
      fderiv ℝ (c.pQuad η) y + fderiv ℝ c.pArc y :=
    ((hpQ y).hasFDerivAt.add (hpArc y).hasFDerivAt).fderiv
  have hqd1 : DifferentiableAt ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z))) y := (hqQ _).comp y hGd
  have hqd2 : DifferentiableAt ℝ (fun z => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y :=
    DifferentiableAt.comp (g := fun w => c.qHeightProfile (c.qArc w)) y hHq hGd
  have hqadd : fderiv ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z)) + c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z))))
      y = fderiv ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z))) y +
        fderiv ℝ (fun z => c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y :=
    (hqd1.hasFDerivAt.add hqd2.hasFDerivAt).fderiv
  rw [hadd, hpadd, hqadd, _root_.add_apply, _root_.add_apply, hnf, hfp1, hfp2, hfq1, hfq2] at h1
  have h0' : dfV I (c.blendedQuadraticFunction η β) c.D.V (c.dp.χ y) =
      (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) * (ModelField.theta c.dp.r₀ y *
          (2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2)) +
        c.κ β (morseNormalForm c.dp.hk (f p) y) *
          (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
            (2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
              2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2)) +
        deriv (c.κ β) (morseNormalForm c.dp.hk (f p) y) * -1 *
          (c.qQuad η (c.qExtendedChart (c.dp.χ y)) - c.pQuad η y) := by
    change mfderiv I 𝓘(ℝ, ℝ) (c.blendedQuadraticFunction η β) (c.dp.χ y) (c.D.V (c.dp.χ y)) = _
    rw [hV]
    exact h0
  have h1' : dfV I (c.blendedQuadraticFunction η β) c.D.V (c.dp.χ y) + dfV I (c.blendedArcCoordinate β) c.D.V (c.dp.χ y) =
      (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) * (ModelField.theta c.dp.r₀ y *
          (2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2) +
            -(ModelField.theta c.dp.r₀ y * c.pArc y)) +
        c.κ β (morseNormalForm c.dp.hk (f p) y) *
          (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
            (2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
              2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2) +
            ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) *
              (deriv c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) * c.qArc (c.qExtendedChart (c.dp.χ y)))) +
        deriv (c.κ β) (morseNormalForm c.dp.hk (f p) y) * -1 *
          (c.qQuad η (c.qExtendedChart (c.dp.χ y)) + c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ y))) -
            (c.pQuad η y + c.pArc y)) := by
    change @HAdd.hAdd ℝ ℝ ℝ _ (mfderiv I 𝓘(ℝ, ℝ) (c.blendedQuadraticFunction η β) (c.dp.χ y) (c.D.V (c.dp.χ y)))
      (mfderiv I 𝓘(ℝ, ℝ) (c.blendedArcCoordinate β) (c.dp.χ y) (c.D.V (c.dp.χ y))) = _
    rw [hV]
    exact h1
  refine ⟨?_, ?_⟩
  · linear_combination h0'
  · linear_combination h1' - h0'

theorem exists_p_piece {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) (hβm : β ≤ c.βmax) :
    ∃ K : Set M, isLyapunovOn c.D c.arc K (c.blendedQuadraticFunction η β) (c.blendedArcCoordinate β) ∧
      c.arc ∩ f ⁻¹' Iic (c.fb - 2 * β) ⊆ interior K := by
  classical
  have hp : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hε := c.hε
  have hfc : Continuous f := c.hf.smooth.continuous
  have hrm0 : 0 < c.D.rm p hp := c.D.rm_pos p hp
  have hrmR : c.D.rm p hp ≤ c.dp.R := (c.D.hrm p hp).2
  have hrmR' : c.D.rm p hp < c.dp.R' := c.D.rm_lt_R' p hp
  have hr0 : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
  have hrrm : Real.sqrt (2 * c.ε) < c.D.rm p hp :=
    (Real.sqrt_lt' hrm0).2 (by have := c.hrmp; linarith)
  have hball : ∀ y : Fin n → ℝ, morseNorm n y < c.D.rm p hp →
      y ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' :=
    fun y hy => mem_ball_of_morseNorm_lt (hy.trans hrmR')
  have hsrc : ∀ y : Fin n → ℝ, morseNorm n y < c.D.rm p hp → y ∈ c.dp.χ.source :=
    fun y hy => c.dp.hball (hball y hy)
  have hnf : ∀ y : Fin n → ℝ, morseNorm n y < c.D.rm p hp →
      f (c.dp.χ y) = morseNormalForm c.dp.hk (f p) y :=
    fun y hy => c.dp.hnorm y (hy.le.trans hrmR)
  set W : Set M := c.dp.χ '' {y | morseNorm n y < c.D.rm p hp} ∩ f ⁻¹' Iio (c.fb - β) with hW_def
  have hWo : IsOpen W := (c.dp.isOpen_image_of_lt hrmR'.le).inter (isOpen_Iio.preimage hfc)
  have hκW : ∀ x ∈ W, c.κ β (f x) = 0 := by
    intro x hx
    have h1 : f x ≤ c.fb - β := le_of_lt hx.2
    simp only [TransverseCancellingPair.κ]
    rw [CancelModel.cut_eq_one (by linarith) h1]
    ring
  have hL₀W : ∀ x ∈ W, c.blendedQuadraticFunction η β x = c.pQuad η (c.dp.χ.symm x) := by
    intro x hx
    simp only [TransverseCancellingPair.blendedQuadraticFunction, hκW x hx]
    ring
  have hAW : ∀ x ∈ W, c.blendedArcCoordinate β x = c.pArc (c.dp.χ.symm x) := by
    intro x hx
    simp only [TransverseCancellingPair.blendedArcCoordinate, hκW x hx]
    ring
  have hneg : ContDiff ℝ ∞ (fun y : Fin n → ℝ => negPart c.dp.hk y) :=
    (ModelField.negPartL c.dp.hk).contDiff
  have hpos : ContDiff ℝ ∞ (fun y : Fin n → ℝ => posPart c.dp.hk y) :=
    (ModelField.posPartL c.dp.hk).contDiff
  have hpA : ContDiff ℝ ∞ c.pArc := by
    change ContDiff ℝ ∞ (fun y => ⟪posPart c.dp.hk y, c.e₁⟫)
    exact hpos.inner ℝ contDiff_const
  have hpQ : ContDiff ℝ ∞ (c.pQuad η) := by
    change ContDiff ℝ ∞ (fun y => ‖negPart c.dp.hk y‖ ^ 2 -
      η * ‖posPart c.dp.hk y - c.pArc y • c.e₁‖ ^ 2)
    exact (hneg.norm_sq ℝ).sub
      (contDiff_const.mul ((hpos.sub (hpA.smul contDiff_const)).norm_sq ℝ))
  have hgen : ∀ (G : M → ℝ) (g : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ g →
      (∀ x ∈ W, G x = g (c.dp.χ.symm x)) →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ G W ∧ ∀ y : Fin n → ℝ, c.dp.χ y ∈ W →
        morseNorm n y < c.D.rm p hp →
        dfV I G c.D.V (c.dp.χ y) = fderiv ℝ g y (ModelField.modelField c.dp.k c.dp.r₀ y) ∧
        (mfderiv I 𝓘(ℝ, ℝ) G (c.dp.χ y) = 0 → fderiv ℝ g y = 0) := by
    intro G g hg hGW
    have hsm : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ G W := by
      have h1 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (g ∘ c.dp.χ.symm) (c.dp.χ '' Metric.ball 0 c.dp.R') :=
        hg.contMDiff.comp_contMDiffOn c.dp.hχsymm
      refine (h1.mono ?_).congr hGW
      exact inter_subset_left.trans (c.dp.image_lt_subset_image_ball hrmR'.le)
    refine ⟨hsm, fun y hxW hy => ?_⟩
    have hGd : MDifferentiableAt I 𝓘(ℝ, ℝ) G (c.dp.χ y) :=
      (hsm.contMDiffAt (hWo.mem_nhds hxW)).mdifferentiableAt (by simp)
    have hev : G ∘ c.dp.χ =ᶠ[𝓝 y] g := by
      have hO : IsOpen (c.dp.χ.source ∩ c.dp.χ ⁻¹' W) :=
        c.dp.χ.continuousOn.isOpen_inter_preimage c.dp.χ.open_source hWo
      filter_upwards [hO.mem_nhds ⟨hsrc y hy, hxW⟩] with z hz
      simp only [Function.comp]
      rw [hGW _ hz.2, c.dp.χ.left_inv hz.1]
    have hcomp := mfderiv_comp y hGd (c.dp.mdifferentiableAt_chart (hball y hy))
    have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (G ∘ c.dp.χ) y = fderiv ℝ g y := by
      rw [mfderiv_eq_fderiv, hev.fderiv_eq]
      ext1 v
      rfl
    refine ⟨?_, fun h0 => ?_⟩
    · have h2 := DFunLike.congr_fun (hcomp.symm.trans h1)
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y) (c.D.V (c.dp.χ y)))
      have h3 : mfderiv I 𝓘(ℝ, ℝ) G (c.dp.χ y) (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ y
          (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y) (c.D.V (c.dp.χ y)))) =
          fderiv ℝ g y (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ y)
            (c.D.V (c.dp.χ y))) := h2
      rw [MorseNormalChart.mfderiv_chart_symm_apply (hball y hy), c.D.model p hp y hy] at h3
      exact h3
    · rw [h0, ContinuousLinearMap.zero_comp] at hcomp
      exact h1.symm.trans hcomp
  obtain ⟨hL₀sm, hL₀d⟩ := hgen (c.blendedQuadraticFunction η β) (c.pQuad η) hpQ hL₀W
  obtain ⟨hAsm, hAd⟩ := hgen (c.blendedArcCoordinate β) c.pArc hpA hAW
  set S : Set (Fin n → ℝ) := {y | morseNorm n y ≤ Real.sqrt (2 * c.ε) ∧
    morseNormalForm c.dp.hk (f p) y ≤ c.fb - 3 * β / 2} with hS_def
  have hSmem : ∀ y ∈ S, morseNorm n y < c.D.rm p hp ∧ c.dp.χ y ∈ W := by
    intro y hy
    have hyr : morseNorm n y < c.D.rm p hp := hy.1.trans_lt hrrm
    refine ⟨hyr, ⟨y, hyr, rfl⟩, ?_⟩
    change f (c.dp.χ y) < c.fb - β
    rw [hnf y hyr]
    linarith [hy.2]
  have hSc : IsCompact S :=
    (isCompact_morseNorm_le (Real.sqrt (2 * c.ε))).inter_right
      (isClosed_le (ModelField.contDiff_nf c.dp.hk (f p)).continuous continuous_const)
  refine ⟨c.dp.χ '' S, ?_, ?_⟩
  · refine ⟨hSc.image_of_continuousOn
      (c.dp.χ.continuousOn.mono fun y hy => hsrc y (hSmem y hy).1), ?_,
      ⟨W, hWo, ?_, hL₀sm, hAsm⟩, ?_, ?_, 1, one_pos, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact c.D.inStrip p hp (mem_image_of_mem _ (hball y (hSmem y hy).1))
    · rintro _ ⟨y, hy, rfl⟩
      exact (hSmem y hy).2
    · rintro _ ⟨y, hy, rfl⟩
      rw [(hL₀d y (hSmem y hy).2 (hSmem y hy).1).1, c.fderiv_pQuad_modelField]
      exact mul_nonneg (ModelField.theta_pos c.dp.hr₀ y).le (by positivity)
    · rintro _ ⟨y, hy, rfl⟩ hxΓ
      obtain ⟨hyrm, hyW⟩ := hSmem y hy
      rw [(hL₀d y hyW hyrm).1, (hAd y hyW hyrm).1, c.fderiv_pQuad_modelField,
        c.fderiv_pArc_modelField]
      have hθ := ModelField.theta_pos c.dp.hr₀ y
      have hnn : (0 : ℝ) ≤ 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 := by positivity
      rcases (mul_nonneg hθ.le hnn).lt_or_eq with hlt | heq
      · exact Or.inl hlt
      right
      have h0 : 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 heq.symm with h | h
        · linarith
        · exact h
      have hu2 : ‖negPart c.dp.hk y‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖negPart c.dp.hk y‖, mul_nonneg hη.le (sq_nonneg ‖c.pPerp y‖)]
      have hv2 : ‖c.pPerp y‖ ^ 2 = 0 := by
        have : η * ‖c.pPerp y‖ ^ 2 = 0 := by
          nlinarith [sq_nonneg ‖negPart c.dp.hk y‖, mul_nonneg hη.le (sq_nonneg ‖c.pPerp y‖)]
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      have hu : negPart c.dp.hk y = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hu2)
      have hv : c.pPerp y = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hv2)
      have hposy : posPart c.dp.hk y = c.pArc y • c.e₁ := sub_eq_zero.1 hv
      have hy_eq : y = recombine c.dp.hk 0 (c.pArc y • c.e₁) := by
        conv_lhs => rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dp.hk y]
        rw [hu, hposy]
      rcases lt_trichotomy (c.pArc y) 0 with ht | ht | ht
      · exact ⟨heq.symm, neg_pos.2 (mul_neg_of_pos_of_neg hθ ht)⟩
      · exfalso
        apply hxΓ
        have hy0 : y = 0 := by
          rw [hy_eq, ht, zero_smul]
          funext i
          simp [recombine]
        rw [hy0, c.dp.hχ0]
        exact c.p_mem_arc
      · exfalso
        apply hxΓ
        rw [hy_eq]
        apply c.p_ray_mem_arc ht
        have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
          c.dp.hk 0 (c.pArc y • c.e₁)
        rw [← hy_eq, norm_zero, norm_smul, c.unit_dirs.1, Real.norm_eq_abs, mul_one, sq_abs] at hsq
        have h1 : morseNorm n y ^ 2 ≤ Real.sqrt (2 * c.ε) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hy.1 2
        rw [Real.sq_sqrt (by linarith)] at h1
        nlinarith
    · intro μ hμ _ x hx _
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨hyrm, hyW⟩ := hSmem y hy
      have hGW : ∀ x ∈ W, c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x =
          c.pQuad η (c.dp.χ.symm x) + μ * c.pArc (c.dp.χ.symm x) := fun x hx => by
        rw [hL₀W x hx, hAW x hx]
      obtain ⟨-, hd⟩ := hgen (fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x)
        (fun z => c.pQuad η z + μ * c.pArc z) (hpQ.add (contDiff_const.mul hpA)) hGW
      intro h0
      have h1 := (hd y hyW hyrm).2 h0
      have h2 := (c.fderiv_ascent η μ y).1
      rw [h1] at h2
      have h3 : μ = 0 := h2.symm.trans rfl
      linarith
  · rintro x ⟨hxΓ, hxf⟩
    have hxf' : f x ≤ c.fb - 2 * β := hxf
    have hfb : c.fb = f p + c.ε := rfl
    set O : Set (Fin n → ℝ) := {y | morseNorm n y < Real.sqrt (2 * c.ε) ∧
        morseNormalForm c.dp.hk (f p) y < c.fb - 3 * β / 2} with hO_def
    have hOo : IsOpen (c.dp.χ '' O) := by
      rw [c.dp.χ.isOpen_image_iff_of_subset_source (fun y hy => hsrc y (hy.1.trans hrrm))]
      exact (isOpen_morseNorm_lt _).inter
        (isOpen_lt (ModelField.contDiff_nf c.dp.hk (f p)).continuous continuous_const)
    have hmem : ∀ y : Fin n → ℝ, morseNorm n y < Real.sqrt (2 * c.ε) → x = c.dp.χ y →
        x ∈ interior (c.dp.χ '' S) := by
      intro y hy hxy
      have hxO : x ∈ c.dp.χ '' O := by
        refine ⟨y, ⟨hy, ?_⟩, hxy.symm⟩
        rw [← hnf y (hy.trans hrrm), ← hxy]
        linarith
      have hOS : O ⊆ S := fun z hz => ⟨hz.1.le, hz.2.le⟩
      exact interior_maximal (image_mono hOS) hOo hxO
    have hc₁ := c.hc₁
    have hc₂ := c.hc₂
    rcases c.arc_cases hxΓ with rfl | rfl | ⟨t, ht, ht2, rfl⟩ | ⟨t, ht, ht2, rfl⟩ | ⟨s, hs, _, hfs⟩
    · exact hmem 0 (by rw [morseNorm_zero]; exact hr0) c.dp.hχ0.symm
    · exfalso
      linarith
    · refine hmem _ ?_ rfl
      rw [Real.lt_sqrt (norm_nonneg _),
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq, norm_zero,
        norm_smul, c.unit_dirs.1, Real.norm_eq_abs, mul_one, sq_abs]
      linarith
    · exfalso
      have hq : q ∈ ({p, q} : Finset M) := mem_pair_right p q
      have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
        c.dq.hk (t • c.u₀) 0
      rw [norm_zero, norm_smul, c.unit_dirs.2.1, Real.norm_eq_abs, mul_one, sq_abs] at hsq
      have hrq := c.hrmq
      have hrq0 : 0 < c.D.rm q hq := c.D.rm_pos q hq
      have hlt : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) < c.D.rm q hq := by
        refine lt_of_pow_lt_pow_left₀ 2 hrq0.le ?_
        rw [hsq]
        linarith
      have hfx := c.dq.hnorm _ (hlt.le.trans (c.D.hrm q hq).2)
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul, c.unit_dirs.2.1,
        Real.norm_eq_abs, mul_one, sq_abs] at hfx
      rw [hfx] at hxf'
      linarith
    · exfalso
      linarith [hs.1, hs.2]

theorem lyapunovOn_q {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) (hβm : β ≤ c.βmax) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ f ⁻¹' Ioo a' b') (hKdom : K ⊆ c.qDom)
    (hKlev : ∀ x ∈ K, c.fb + β < f x)
    (hKarc : ∀ x ∈ K, -c.ρq ≤ c.qArc (c.qExtendedChart x) ∧ c.qArc (c.qExtendedChart x) ^ 2 < c.sqSum) :
    isLyapunovOn c.D c.arc K (c.blendedQuadraticFunction η β) (c.blendedArcCoordinate β) := by
  classical
  have _ := hβm
  obtain ⟨hopen, hΨ⟩ := c.contMDiffOn_qExtendedChart
  have hfc : Continuous f := c.hf.smooth.continuous
  have hκ : ∀ x : M, c.fb + β < f x → c.κ β (f x) = 1 := fun x hx => by
    unfold TransverseCancellingPair.κ
    rw [CancelModel.cut_eq_zero (by linarith) hx.le]
    ring
  have hqArc : Continuous c.qArc := by
    unfold TransverseCancellingPair.qArc
    exact (ModelField.negPartL c.dq.hk).continuous.inner continuous_const
  have hqArcD : ContDiff ℝ ∞ c.qArc := by
    have : c.qArc = fun y => ⟪ModelField.negPartL c.dq.hk y, c.u₀⟫ := rfl
    rw [this]
    exact (ModelField.negPartL c.dq.hk).contDiff.inner ℝ contDiff_const
  have hgQ : ContDiff ℝ ∞ (c.qQuad η) := by
    have : c.qQuad η = fun y => η * ‖ModelField.negPartL c.dq.hk y -
        c.qArc y • c.u₀‖ ^ 2 - ‖ModelField.posPartL c.dq.hk y‖ ^ 2 := rfl
    rw [this]
    exact (contDiff_const.mul ((contDiff_norm_sq ℝ).comp
      ((ModelField.negPartL c.dq.hk).contDiff.sub (hqArcD.smul contDiff_const)))).sub
      ((contDiff_norm_sq ℝ).comp (ModelField.posPartL c.dq.hk).contDiff)
  set UH : Set ℝ := {σ | σ ^ 2 < c.sqSum} with hUHdef
  have hUH : IsOpen UH := isOpen_lt (continuous_pow 2) continuous_const
  have hHqs : ∀ σ ∈ UH, ContDiffAt ℝ ∞ c.qHeightProfile σ := fun σ hσ => by
    have hσ' : σ ^ 2 < c.sqSum := hσ
    have : c.qHeightProfile = fun σ => Real.sqrt (c.sqSum - σ ^ 2) +
        c.kH * (Real.sqrt (2 * c.ε) - σ) * CancelModel.cut (Real.sqrt (2 * c.ε) / 2)
          (Real.sqrt (2 * c.ε)) σ := rfl
    rw [this]
    refine ContDiffAt.add ?_ ?_
    · exact (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt (by simp only [id]; linarith)
    · exact (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).mul
        (CancelModel.contDiff_cut _ _).contDiffAt
  set W : Set M := c.qDom ∩ (f ⁻¹' Ioi (c.fb + β) ∩ c.qExtendedChart ⁻¹' (c.qArc ⁻¹' UH)) with hWdef
  have hWo : IsOpen W := by
    have h1 := hΨ.continuousOn.isOpen_inter_preimage hopen (hUH.preimage hqArc)
    have h2 : W = (c.qDom ∩ c.qExtendedChart ⁻¹' (c.qArc ⁻¹' UH)) ∩ f ⁻¹' Ioi (c.fb + β) := by
      rw [hWdef]; ext x; simp only [mem_inter_iff, mem_preimage]; tauto
    rw [h2]
    exact h1.inter (isOpen_Ioi.preimage hfc)
  have hKW : K ⊆ W := fun x hx =>
    ⟨hKdom hx, hKlev x hx, (hKarc x hx).2⟩
  set gA : (Fin n → ℝ) → ℝ := fun y => c.qHeightProfile (c.qArc y) with hgAdef
  have hgA : ∀ x ∈ W, ContDiffAt ℝ ∞ gA (c.qExtendedChart x) := fun x hx =>
    (hHqs _ hx.2.2).comp (c.qExtendedChart x) hqArcD.contDiffAt
  have hL₀W : ∀ x ∈ W, c.blendedQuadraticFunction η β x = c.qQuad η (c.qExtendedChart x) := fun x hx => by
    unfold TransverseCancellingPair.blendedQuadraticFunction; rw [hκ x hx.2.1]; ring
  have hAW : ∀ x ∈ W, c.blendedArcCoordinate β x = gA (c.qExtendedChart x) := fun x hx => by
    unfold TransverseCancellingPair.blendedArcCoordinate; rw [hκ x hx.2.1]; ring
  have hΨmd : ∀ x ∈ W, MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x := fun x hx =>
    (hΨ.contMDiffAt (hopen.mem_nhds hx.1)).mdifferentiableAt (by simp)
  have hchain : ∀ x ∈ W, ∀ (F : M → ℝ) (g : (Fin n → ℝ) → ℝ),
      DifferentiableAt ℝ g (c.qExtendedChart x) → (∀ z ∈ W, F z = g (c.qExtendedChart z)) →
        ∀ v : TangentSpace I x, mfderiv I 𝓘(ℝ, ℝ) F x v =
          fderiv ℝ g (c.qExtendedChart x) (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x v) := by
    intro x hx F g hg hFg v
    have hev : F =ᶠ[𝓝 x] g ∘ c.qExtendedChart :=
      eventuallyEq_of_mem (hWo.mem_nhds hx) fun z hz => hFg z hz
    have h1 := hev.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
    have h2 := mfderiv_comp x hg.mdifferentiableAt (hΨmd x hx)
    have h3 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) g (c.qExtendedChart x) = fderiv ℝ g (c.qExtendedChart x) :=
      mfderiv_eq_fderiv
    rw [h1, h2, h3]
    rfl
  have hdfV : ∀ x ∈ W, ∀ (F : M → ℝ) (g : (Fin n → ℝ) → ℝ),
      DifferentiableAt ℝ g (c.qExtendedChart x) → (∀ z ∈ W, F z = g (c.qExtendedChart z)) →
        dfV I F c.D.V x = fderiv ℝ g (c.qExtendedChart x)
          (ModelField.modelField c.dq.k c.dq.r₀ (c.qExtendedChart x)) := by
    intro x hx F g hg hFg
    have h := hchain x hx F g hg hFg (c.D.V x)
    change mfderiv I 𝓘(ℝ, ℝ) F x (c.D.V x) = _
    rw [h, c.mfderiv_qExtendedChart_V hx.1]
  have hθ : ∀ x : M, 0 < ModelField.theta c.dq.r₀ (c.qExtendedChart x) := fun x =>
    ModelField.theta_pos c.dq.hr₀ _
  have hdL : ∀ x ∈ K, dfV I (c.blendedQuadraticFunction η β) c.D.V x = ModelField.theta c.dq.r₀ (c.qExtendedChart x) *
      (2 * η * ‖c.qPerp (c.qExtendedChart x)‖ ^ 2 + 2 * ‖posPart c.dq.hk (c.qExtendedChart x)‖ ^ 2) := fun x hx => by
    rw [hdfV x (hKW hx) (c.blendedQuadraticFunction η β) (c.qQuad η) (hgQ.differentiable (by simp) _) hL₀W]
    exact c.fderiv_qQuad_modelField η _
  have hdA : ∀ x ∈ K, dfV I (c.blendedArcCoordinate β) c.D.V x = ModelField.theta c.dq.r₀ (c.qExtendedChart x) *
      (deriv c.qHeightProfile (c.qArc (c.qExtendedChart x)) * c.qArc (c.qExtendedChart x)) := fun x hx => by
    rw [hdfV x (hKW hx) (c.blendedArcCoordinate β) gA ((hgA x (hKW hx)).differentiableAt (by simp)) hAW]
    exact c.fderiv_qHeightProfile_qArc_modelField (hKarc x hx).1 (hKarc x hx).2
  refine ⟨hK, hKs, ⟨W, hWo, hKW, ?_, ?_⟩, ?_, ?_, 1, one_pos, ?_⟩
  · intro x hx
    refine ContMDiffAt.contMDiffWithinAt ?_
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (c.qQuad η ∘ c.qExtendedChart) x :=
      (contMDiffAt_iff_contDiffAt.2 hgQ.contDiffAt).comp x
        (hΨ.contMDiffAt (hopen.mem_nhds hx.1))
    exact h1.congr_of_eventuallyEq
      (eventuallyEq_of_mem (hWo.mem_nhds hx) fun z hz => hL₀W z hz)
  · intro x hx
    refine ContMDiffAt.contMDiffWithinAt ?_
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (gA ∘ c.qExtendedChart) x :=
      (contMDiffAt_iff_contDiffAt.2 (hgA x hx)).comp x
        (hΨ.contMDiffAt (hopen.mem_nhds hx.1))
    exact h1.congr_of_eventuallyEq
      (eventuallyEq_of_mem (hWo.mem_nhds hx) fun z hz => hAW z hz)
  · intro x hx
    rw [hdL x hx]
    have := hθ x
    positivity
  · intro x hx hxΓ
    by_cases hpos : 0 < dfV I (c.blendedQuadraticFunction η β) c.D.V x
    · exact Or.inl hpos
    right
    have h0 : dfV I (c.blendedQuadraticFunction η β) c.D.V x = 0 := by
      refine le_antisymm (not_lt.1 hpos) ?_
      rw [hdL x hx]
      have := hθ x
      positivity
    refine ⟨h0, ?_⟩
    rw [hdL x hx] at h0
    have h2 : 2 * η * ‖c.qPerp (c.qExtendedChart x)‖ ^ 2 + 2 * ‖posPart c.dq.hk (c.qExtendedChart x)‖ ^ 2 = 0 :=
      (mul_eq_zero.1 h0).resolve_left (hθ x).ne'
    have ha : ‖c.qPerp (c.qExtendedChart x)‖ ^ 2 = 0 := by
      have := sq_nonneg ‖c.qPerp (c.qExtendedChart x)‖
      have := sq_nonneg ‖posPart c.dq.hk (c.qExtendedChart x)‖
      nlinarith
    have hb : ‖posPart c.dq.hk (c.qExtendedChart x)‖ ^ 2 = 0 := by
      have := sq_nonneg ‖c.qPerp (c.qExtendedChart x)‖
      have := sq_nonneg ‖posPart c.dq.hk (c.qExtendedChart x)‖
      nlinarith
    have ha' : c.qPerp (c.qExtendedChart x) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ha)
    have hb' : posPart c.dq.hk (c.qExtendedChart x) = 0 :=
      norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hb)
    have hneg : c.qArc (c.qExtendedChart x) < 0 := by
      by_contra hnn
      exact hxΓ (c.mem_arc_of_qExtendedChart (hKdom hx) ha' hb' (not_lt.1 hnn))
    rw [hdA x hx]
    have hd := (c.qHeightProfile_spec.1 _ (hKarc x hx).1 (hKarc x hx).2).2
    exact mul_pos (hθ x) (mul_pos_of_neg_of_neg hd hneg)
  · intro μ hμ _ x hx _ hzero
    have hxW := hKW hx
    have hg : DifferentiableAt ℝ (fun y => c.qQuad η y + μ * gA y) (c.qExtendedChart x) :=
      (hgQ.differentiable (by simp) _).add
        ((differentiableAt_const _).mul ((hgA x hxW).differentiableAt (by simp)))
    have h := hchain x hxW (fun y => c.blendedQuadraticFunction η β y + μ * c.blendedArcCoordinate β y)
      (fun y => c.qQuad η y + μ * gA y) hg (fun z hz => by rw [hL₀W z hz, hAW z hz])
    obtain ⟨v, hv⟩ := c.surjective_mfderiv_qExtendedChart (hKdom hx) (recombine c.dq.hk c.u₀ 0)
    have h1 := h v
    rw [hzero, hv] at h1
    have h2 := (c.fderiv_ascent η μ (c.qExtendedChart x)).2 (hKarc x hx).1 (hKarc x hx).2
    have h3 : μ * deriv c.qHeightProfile (c.qArc (c.qExtendedChart x)) = 0 := h2.symm.trans (h1.symm.trans rfl)
    have hd := (c.qHeightProfile_spec.1 _ (hKarc x hx).1 (hKarc x hx).2).2
    exact (mul_ne_zero hμ.ne' hd.ne) h3

theorem exists_q_tube {β : ℝ} (hβ : 0 < β) (hβm : β ≤ c.βmax) :
    ∃ T : Set M, IsCompact T ∧ T ⊆ c.qTube ∧
      (∀ x ∈ T, c.fb + 3 * β / 2 ≤ f x ∧ 0 < c.qArc (c.qExtendedChart x) ∧
        c.qArc (c.qExtendedChart x) ^ 2 < c.sqSum) ∧
      c.arc ∩ f ⁻¹' Icc (c.fb + 2 * β) (f q - 17 * c.ε / 16) ⊆ interior T := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hε := c.hε
  have hpI := c.D.f_mem_Ioo p (mem_pair_left p q)
  have hqI := c.D.f_mem_Ioo q (mem_pair_right p q)
  have hcq : c.cq = f q - c.ε := rfl
  have hfb : c.fb = f p + c.ε := rfl
  have hsq : c.sqSum = 2 * (f q - f p) := by
    simp only [TransverseCancellingPair.sqSum, hcq, hfb]; ring
  have hc12 : f p + c.ε < f q - c.ε := c.hc₁.trans c.hc₂
  have hcsb : ∀ y : M, f y ∈ Icc (f p + c.ε) (f q - c.ε) →
      ∀ p' (hp' : p' ∈ ({p, q} : Finset M)), y ∉ c.D.closedSmallBall p' hp' := by
    intro y hy p' hp' hmem
    have h := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hmem
    rcases mem_pair_iff.1 hp' with h' | h'
    · subst h'
      have h1 : (c.D.chart p' hp').r₀ ^ 2 < 2 * c.ε := c.hr₀p
      have h2 := (abs_le.1 h).2
      linarith [hy.1]
    · subst h'
      have h1 : (c.D.chart p' hp').r₀ ^ 2 < 2 * c.ε := c.hr₀q
      have h2 := (abs_le.1 h).1
      linarith [hy.2]
  have hflow : ∀ z : M, f z = c.cq → ∀ t ∈ Icc 0 (c.cq - c.fb),
      c.D.flow t z ∈ c.D.regularFlowDomain c.cq ∧ f (c.D.flow t z) = c.cq - t ∧
        c.D.π c.cq (c.D.flow t z) = z := by
    intro z hz t ht
    have ht1 := ht.1
    have ht2 : t ≤ f q - c.ε - (f p + c.ε) := ht.2
    have hlev := GradientLikeStrip.f_flow_eq_sub_of_levels (D := c.D) hfs (x := z) (T := t)
      (by rw [hz, hcq]; constructor <;> linarith [hpI.1, hqI.2])
      (by rw [hz, hcq]; constructor <;> linarith [hpI.1, hqI.2])
      (by
        intro y hy
        rw [hz, uIcc_of_ge (by linarith), hcq] at hy
        exact c.hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have hmem : ∀ s ∈ Icc 0 t, f (c.D.flow s z) = c.cq - s := fun s hs => by
      rw [hlev s (by rw [uIcc_of_le ht1]; exact hs), hz]
    have hft : f (c.D.flow t z) = c.cq - t := hmem t ⟨ht1, le_rfl⟩
    refine ⟨⟨?_, ?_⟩, hft, ?_⟩
    · rw [hft, hcq]; constructor <;> linarith [hpI.1, hqI.2]
    · intro s hs p' hp'
      rw [hft, show c.cq - t - c.cq = -t by ring] at hs
      rw [c.D.flow_flow]
      have hs' : t + s ∈ Icc 0 t := by
        rw [mem_uIcc] at hs
        rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
      apply hcsb _ _ p' hp'
      rw [hmem _ hs', hcq]
      constructor <;> linarith [hs'.1, hs'.2]
    · change c.D.flow (f (c.D.flow t z) - c.cq) (c.D.flow t z) = z
      rw [hft, show c.cq - t - c.cq = -t by ring, c.D.flow_neg_flow]
  have hw₀ : c.w₀ ≠ 0 := c.hw₀.1
  have hu₀ : ‖c.u₀‖ = 1 := c.unit_dirs.2.1
  have hrmR := (c.D.hrm q (mem_pair_right p q)).2
  have hrm0 := c.D.rm_pos q (mem_pair_right p q)
  have hR2 : c.D.rm q (mem_pair_right p q) ^ 2 ≤ c.dq.R ^ 2 := pow_le_pow_left₀ hrm0.le hrmR 2
  have hrmq := c.hrmq
  have hρ2 : c.ρq ^ 2 = 5 * c.ε / 2 := Real.sq_sqrt (by linarith)
  have hρ0 : 0 < c.ρq := Real.sqrt_pos.2 (by linarith)
  have hρR : c.ρq < c.dq.R := by
    change Real.sqrt (5 * c.ε / 2) < c.dq.R
    rw [Real.sqrt_lt' c.dq.R_pos]; linarith
  have hycS := c.dq.sphereParam_mem_leftModelSphere hε.le hw₀
  have hycR : morseNorm n (c.dq.sphereParam c.ε c.w₀) ≤ c.dq.R :=
    c.dq.morseNorm_sphereParam_le hε.le (by linarith) hw₀
  have hz₀lev : f c.z₀ = c.cq :=
    (c.dq.hnorm _ hycR).trans (c.dq.nf_of_mem_leftModelSphere hycS)
  set G : Set (Fin n → ℝ) := {y | morseNorm n y < c.ρq} ∩
      {y | 0 < ⟪negPart c.dq.hk y, c.u₀⟫} ∩
      {y | ‖negPart c.dq.hk y‖ * ‖posPart c.dq.hk y‖ < c.ε} with hG
  have hGo : IsOpen G :=
    ((isOpen_morseNorm_lt _).inter (isOpen_lt continuous_const
      (c.dq.continuous_negPart.inner continuous_const))).inter
      (isOpen_lt ((c.dq.continuous_negPart.norm).mul c.dq.continuous_posPart.norm)
        continuous_const)
  have hycG : c.dq.sphereParam c.ε c.w₀ ∈ G := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change morseNorm n _ < c.ρq
      refine lt_of_pow_lt_pow_left₀ 2 hρ0.le ?_
      rw [c.dq.morseNorm_sq_of_mem_leftModelSphere hycS, hρ2]; linarith
    · change 0 < ⟪negPart c.dq.hk (c.dq.sphereParam c.ε c.w₀), c.u₀⟫
      have he : 0 < ‖c.dq.toE c.w₀‖ := norm_pos_iff.2 (c.dq.toE_ne_zero hw₀)
      rw [c.dq.negPart_sphereParam]
      change 0 < ⟪(Real.sqrt (2 * c.ε) / ‖c.dq.toE c.w₀‖) • c.dq.toE c.w₀,
        ‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀⟫
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      exact mul_pos (div_pos (Real.sqrt_pos.2 (by linarith)) he)
        (mul_pos (inv_pos.2 he) (pow_pos he 2))
    · change ‖negPart c.dq.hk _‖ * ‖posPart c.dq.hk _‖ < c.ε
      rw [c.dq.posPart_sphereParam, norm_zero, mul_zero]; exact hε
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hGo _ hycG
  have hcb : Metric.closedBall (c.dq.sphereParam c.ε c.w₀) (r₁ / 2) ⊆ G :=
    (Metric.closedBall_subset_ball (half_lt_self hr₁)).trans hball
  have hGsrc : ∀ y ∈ G, morseNorm n y ≤ c.dq.R := fun y hy => (hy.1.1.trans hρR).le
  have hGs : ∀ y ∈ G, y ∈ c.dq.χ.source := fun y hy => c.dq.hsrc y (hGsrc y hy)
  set N : Set (Fin n → ℝ) := Metric.closedBall (c.dq.sphereParam c.ε c.w₀) (r₁ / 2) ∩
    {y | morseNormalForm c.dq.hk (f q) y = c.cq} with hN
  have hNc : IsCompact N := (isCompact_closedBall _ _).inter_right
    (isClosed_eq (ModelField.contDiff_nf c.dq.hk (f q)).continuous continuous_const)
  have hKc : IsCompact (c.dq.χ '' N) :=
    hNc.image_of_continuousOn (c.dq.χ.continuousOn.mono fun y hy => hGs y (hcb hy.1))
  have hKlev : ∀ y ∈ N, f (c.dq.χ y) = c.cq := fun y hy =>
    (c.dq.hnorm y (hGsrc y (hcb hy.1))).trans hy.2
  have hlift : ∀ y ∈ G, ∀ s : ℝ, c.fb + 3 * β / 2 ≤ s → s < f q →
      0 < c.qArc (modelLift c.dq.hk (f q) s y) ∧
        c.qArc (modelLift c.dq.hk (f q) s y) ^ 2 < c.sqSum := by
    intro y hy s hs1 hs2
    have hin : 0 < ⟪negPart c.dq.hk y, c.u₀⟫ := hy.1.2
    have hP : ‖negPart c.dq.hk y‖ * ‖posPart c.dq.hk y‖ < c.ε := hy.2
    have hu : 0 < ‖negPart c.dq.hk y‖ := by
      rcases (norm_nonneg (negPart c.dq.hk y)).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [eq_comm, norm_eq_zero] at h
        rw [h, inner_zero_left] at hin
        exact lt_irrefl _ hin
    have hA : 0 < f q - s := by linarith
    have hPn : 0 ≤ ‖negPart c.dq.hk y‖ * ‖posPart c.dq.hk y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    obtain ⟨L, hL⟩ : ∃ L, L = liftScale (f q) s
        (‖negPart c.dq.hk y‖ ^ 2 * ‖posPart c.dq.hk y‖ ^ 2) := ⟨_, rfl⟩
    have hL2 : L ^ 2 = (f q - s) + Real.sqrt ((f q - s) ^ 2 +
        ‖negPart c.dq.hk y‖ ^ 2 * ‖posPart c.dq.hk y‖ ^ 2) := by
      rw [hL, liftScale, Real.sq_sqrt (add_nonneg hA.le (Real.sqrt_nonneg _))]
    have hLpos : 0 < L := by
      rw [hL, liftScale]; exact Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hA (Real.sqrt_nonneg _))
    have hq : c.qArc (modelLift c.dq.hk (f q) s y) =
        L / ‖negPart c.dq.hk y‖ * ⟪negPart c.dq.hk y, c.u₀⟫ := by
      rw [TransverseCancellingPair.qArc, modelLift, ModelField.negPart_recombine, real_inner_smul_left, hL]
    have hle : c.qArc (modelLift c.dq.hk (f q) s y) ≤ L := by
      rw [hq]
      have h1 := real_inner_le_norm (negPart c.dq.hk y) c.u₀
      rw [hu₀, mul_one] at h1
      calc L / ‖negPart c.dq.hk y‖ * ⟪negPart c.dq.hk y, c.u₀⟫
          ≤ L / ‖negPart c.dq.hk y‖ * ‖negPart c.dq.hk y‖ :=
            mul_le_mul_of_nonneg_left h1 (div_pos hLpos hu).le
        _ = L := div_mul_cancel₀ L hu.ne'
    have hpos : 0 < c.qArc (modelLift c.dq.hk (f q) s y) := by
      rw [hq]; exact mul_pos (div_pos hLpos hu) hin
    have hsqrt : Real.sqrt ((f q - s) ^ 2 +
        ‖negPart c.dq.hk y‖ ^ 2 * ‖posPart c.dq.hk y‖ ^ 2) ≤
          (f q - s) + ‖negPart c.dq.hk y‖ * ‖posPart c.dq.hk y‖ := by
      rw [← Real.sqrt_sq (add_nonneg hA.le hPn)]
      apply Real.sqrt_le_sqrt
      have := mul_nonneg hA.le hPn
      nlinarith
    refine ⟨hpos, ?_⟩
    calc c.qArc (modelLift c.dq.hk (f q) s y) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      _ < c.sqSum := by rw [hL2, hsq]; linarith
  have hT : ∀ x ∈ (fun z : ℝ × M => c.D.flow z.1 z.2) ''
      (Icc (c.ε / 32) (c.cq - c.fb - 3 * β / 2) ×ˢ (c.dq.χ '' N)),
      x ∈ c.qTube ∧ c.fb + 3 * β / 2 ≤ f x ∧ 0 < c.qArc (c.qExtendedChart x) ∧
        c.qArc (c.qExtendedChart x) ^ 2 < c.sqSum := by
    rintro x ⟨⟨t, z⟩, ⟨ht, y, hyN, rfl⟩, rfl⟩
    dsimp only
    have hyG : y ∈ G := hcb hyN.1
    have ht' : t ∈ Icc 0 (c.cq - c.fb) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hΩ, hft, hπ⟩ := hflow (c.dq.χ y) (hKlev y hyN) t ht'
    have hmemT : c.D.flow t (c.dq.χ y) ∈ c.qTube := by
      refine ⟨by rw [hft]; linarith [ht.1], hΩ, ?_⟩
      rw [hπ]
      refine ⟨y, ⟨hyG.1.1, ?_⟩, rfl⟩
      intro h0
      have h1 : 0 < ⟪negPart c.dq.hk y, c.u₀⟫ := hyG.1.2
      rw [h0, inner_zero_left] at h1
      exact lt_irrefl _ h1
    refine ⟨hmemT, by rw [hft]; linarith [ht.2], ?_⟩
    rw [c.qExtendedChart_eq_of_mem_qTube hmemT, hπ, c.dq.χ.left_inv (hGs y hyG), hft]
    exact hlift y hyG _ (by linarith [ht.2]) (by rw [hcq]; linarith [ht.1])
  refine ⟨_, (isCompact_Icc.prod hKc).image c.D.continuous_flow_joint,
    fun x hx => (hT x hx).1, fun x hx => (hT x hx).2, ?_⟩
  rintro x ⟨hxΓ, hxl⟩
  have hxl1 : c.fb + 2 * β ≤ f x := hxl.1
  have hxl2 : f x ≤ f q - 17 * c.ε / 16 := hxl.2
  have he₁ : ‖c.e₁‖ = 1 := c.unit_dirs.1
  rcases c.arc_cases hxΓ with rfl | rfl | ⟨t, ht0, ht2, rfl⟩ | ⟨t, ht0, ht2, rfl⟩ |
      ⟨s, hs, rfl, hfx⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso
    have hrmR' := (c.D.hrm p (mem_pair_left p q)).2
    have hrm0' := c.D.rm_pos p (mem_pair_left p q)
    have hR2' : c.D.rm p (mem_pair_left p q) ^ 2 ≤ c.dp.R ^ 2 :=
      pow_le_pow_left₀ hrm0'.le hrmR' 2
    have hrmp := c.hrmp
    have hn : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ^ 2 = t ^ 2 := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        c.dp.hk, ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul,
        he₁, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    have hRp : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ≤ c.dp.R := by
      refine (lt_of_pow_lt_pow_left₀ 2 c.dp.R_pos.le ?_).le
      rw [hn]; linarith
    have hfx := c.dp.hnorm _ hRp
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul, he₁,
      mul_one, Real.norm_eq_abs, sq_abs] at hfx
    rw [hfx] at hxl1
    linarith
  · exfalso
    have hn : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) ^ 2 = t ^ 2 := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        c.dq.hk, ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul,
        hu₀, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    have hRq : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) ≤ c.dq.R := by
      refine (lt_of_pow_lt_pow_left₀ 2 c.dq.R_pos.le ?_).le
      rw [hn]; linarith
    have hfx := c.dq.hnorm _ hRq
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul, hu₀,
      mul_one, Real.norm_eq_abs, sq_abs] at hfx
    rw [hfx] at hxl2
    linarith
  · have hs' : s ∈ Icc 0 (c.cq - c.fb) := ⟨hs.1, by rw [hfx] at hxl1; linarith⟩
    obtain ⟨hΩ, hft, hπ⟩ := hflow c.z₀ hz₀lev s hs'
    have hbsrc : Metric.ball (c.dq.sphereParam c.ε c.w₀) (r₁ / 2) ⊆ c.dq.χ.source :=
      fun y hy => hGs y (hcb (Metric.ball_subset_closedBall hy))
    have hOo : IsOpen (f ⁻¹' Ioo (c.fb + 3 * β / 2) (c.cq - c.ε / 32) ∩ c.D.regularFlowDomain c.cq ∩
        c.D.π c.cq ⁻¹' (c.dq.χ '' Metric.ball (c.dq.sphereParam c.ε c.w₀) (r₁ / 2))) :=
      ((isOpen_Ioo.preimage hfc).inter (c.D.isOpen_regularFlowDomain hfc c.cq)).inter
        (((c.dq.χ.isOpen_image_iff_of_subset_source hbsrc).2 Metric.isOpen_ball).preimage
          (c.D.continuous_π hfs c.cq))
    have hxO : c.D.flow s c.z₀ ∈ f ⁻¹' Ioo (c.fb + 3 * β / 2) (c.cq - c.ε / 32) ∩
        c.D.regularFlowDomain c.cq ∩
        c.D.π c.cq ⁻¹' (c.dq.χ '' Metric.ball (c.dq.sphereParam c.ε c.w₀) (r₁ / 2)) := by
      refine ⟨⟨?_, hΩ⟩, ?_⟩
      · change f _ ∈ Ioo _ _
        rw [hft]
        rw [hfx] at hxl1 hxl2
        constructor <;> linarith
      · change c.D.π c.cq (c.D.flow s c.z₀) ∈
          c.dq.χ '' Metric.ball (c.dq.sphereParam c.ε c.w₀) (r₁ / 2)
        rw [hπ]
        exact ⟨_, Metric.mem_ball_self (half_pos hr₁), rfl⟩
    refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (hOo.mem_nhds hxO) ?_)
    rintro x' ⟨⟨hx'l, hx'Ω⟩, y', hy', hπ'⟩
    have hx'l' : f x' ∈ Ioo (c.fb + 3 * β / 2) (c.cq - c.ε / 32) := hx'l
    have hy'G : y' ∈ G := hcb (Metric.ball_subset_closedBall hy')
    have hlev' : f (c.dq.χ y') = c.cq := by
      rw [hπ']
      exact GradientLikeStrip.f_π hfs ⟨by rw [hcq]; linarith [hpI.1], by rw [hcq]; linarith [hqI.2]⟩
        hx'Ω
    have hy'N : y' ∈ N :=
      ⟨Metric.ball_subset_closedBall hy', (c.dq.hnorm y' (hGsrc y' hy'G)).symm.trans hlev'⟩
    refine ⟨(c.cq - f x', c.dq.χ y'), ⟨⟨by linarith [hx'l'.2], by linarith [hx'l'.1]⟩,
      y', hy'N, rfl⟩, ?_⟩
    change c.D.flow (c.cq - f x') (c.dq.χ y') = x'
    rw [hπ']
    change c.D.flow (c.cq - f x') (c.D.flow (f x' - c.cq) x') = x'
    rw [c.D.flow_flow, show f x' - c.cq + (c.cq - f x') = 0 by ring,
      GradientLikeStrip.flow_zero]

theorem exists_q_piece {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) (hβm : β ≤ c.βmax) :
    ∃ K : Set M, isLyapunovOn c.D c.arc K (c.blendedQuadraticFunction η β) (c.blendedArcCoordinate β) ∧
      c.arc ∩ f ⁻¹' Ici (c.fb + 2 * β) ⊆ interior K := by
  classical
  obtain ⟨T, hTc, hTsub, hTprop, hTcov⟩ := c.exists_q_tube hβ hβm
  have hε := c.hε
  have hfc : Continuous f := c.hf.smooth.continuous
  have hpq : 2 * c.ε < f q - f p := by linarith [c.hc₁, c.hc₂]
  have hβ16 : β ≤ (f q - f p - 2 * c.ε) / 16 :=
    hβm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hfb : c.fb = f p + c.ε := rfl
  have hcq : c.cq = f q - c.ε := rfl
  have hsqS : c.sqSum = 2 * (f q - f p) := by
    simp only [TransverseCancellingPair.sqSum, TransverseCancellingPair.cq, TransverseCancellingPair.fb]; ring
  have hρq0 : 0 ≤ c.ρq := Real.sqrt_nonneg _
  have hq_mem : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hp_mem : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hfq : f q ∈ Ioo a' b' := ((c.hcrit q).1 hq_mem).1
  have hfp : f p ∈ Ioo a' b' := ((c.hcrit p).1 hp_mem).1
  set r : ℝ := Real.sqrt (9 * c.ε / 4) with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 9 * c.ε / 4 := Real.sq_sqrt (by positivity)
  have hrρ : r < c.ρq := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hrmq : 8 * c.ε < c.D.rm q hq_mem ^ 2 := c.hrmq
  have hrmp : 8 * c.ε < c.D.rm p hp_mem ^ 2 := c.hrmp
  have hrmRq : c.D.rm q hq_mem ≤ c.dq.R := (c.D.hrm q hq_mem).2
  have hrmRp : c.D.rm p hp_mem ≤ c.dp.R := (c.D.hrm p hp_mem).2
  have hRR' : c.dq.R < c.dq.R' := c.dq.hRR'
  have hrm0 : 0 < c.D.rm q hq_mem := c.D.rm_pos q hq_mem
  have hrmp0 : 0 < c.D.rm p hp_mem := c.D.rm_pos p hp_mem
  have hr_rm : r < c.D.rm q hq_mem :=
    (le_abs_self r).trans_lt (abs_lt_of_sq_lt_sq (by linarith) hrm0.le)
  have hrR' : r < c.dq.R' := by linarith
  have hrR : r < c.dq.R := by linarith
  have hu₀ : ‖c.u₀‖ = 1 := c.unit_dirs.2.1
  have he₁ : ‖c.e₁‖ = 1 := c.unit_dirs.1
  have hball_facts : ∀ y : Fin n → ℝ, morseNorm n y ≤ r →
      c.dq.χ y ∈ c.qBall ∧ c.qExtendedChart (c.dq.χ y) = y ∧ f (c.dq.χ y) ∈ Ioo a' b' := by
    intro y hy
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.dq.R' :=
      mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy hrR')
    have hqb : c.dq.χ y ∈ c.qBall := ⟨y, lt_of_le_of_lt hy hrρ, rfl⟩
    refine ⟨hqb, ?_, c.D.inStrip q hq_mem ⟨y, hyb, rfl⟩⟩
    simp only [TransverseCancellingPair.qExtendedChart, hqb, ↓reduceIte]
    exact c.dq.χ.left_inv (c.dq.hball hyb)
  set B : Set M := c.dq.χ '' {y | morseNorm n y ≤ r} ∩ f ⁻¹' Ici (c.fb + 3 * β / 2) with hB
  have hK : isLyapunovOn c.D c.arc (B ∪ T) (c.blendedQuadraticFunction η β) (c.blendedArcCoordinate β) := by
    refine c.lyapunovOn_q hη hβ hβm
      (((c.dq.isCompact_image_le hrR').inter_right (isClosed_Ici.preimage hfc)).union hTc)
      ?_ ?_ ?_ ?_
    · rintro x (⟨⟨y, hy, rfl⟩, -⟩ | hx)
      · exact (hball_facts y hy).2.2
      · have h1 := (hTprop x hx).1
        have h2 : f x < c.cq := (hTsub hx).1
        constructor <;> linarith [hfp.1, hfq.2]
    · rintro x (⟨⟨y, hy, rfl⟩, -⟩ | hx)
      · exact Or.inl (hball_facts y hy).1
      · exact Or.inr (hTsub hx)
    · rintro x (⟨-, hx⟩ | hx)
      · have : c.fb + 3 * β / 2 ≤ f x := hx
        linarith
      · linarith [(hTprop x hx).1]
    · rintro x (⟨⟨y, hy, rfl⟩, -⟩ | hx)
      · rw [(hball_facts y hy).2.1]
        have habs : |c.qArc y| ≤ r := by
          have h1 : |c.qArc y| ≤ ‖negPart c.dq.hk y‖ * ‖c.u₀‖ :=
            abs_real_inner_le_norm _ _
          rw [hu₀, mul_one] at h1
          exact h1.trans ((DifferentialGeometry.Topology.Morse.CellAttachment.negPart_norm_le_morseNorm c.dq.hk y).trans hy)
        have hsq : c.qArc y ^ 2 ≤ r ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        refine ⟨by linarith [neg_abs_le (c.qArc y)], by linarith⟩
      · obtain ⟨-, h1, h2⟩ := hTprop x hx
        exact ⟨by linarith, h2⟩
  refine ⟨B ∪ T, hK, ?_⟩
  rintro x ⟨hx, hxf⟩
  have hxf' : c.fb + 2 * β ≤ f x := hxf
  have hOpen : IsOpen (c.dq.χ '' {y | morseNorm n y < r} ∩ f ⁻¹' Ioi (c.fb + 3 * β / 2)) :=
    (c.dq.isOpen_image_of_lt hrR'.le).inter (isOpen_Ioi.preimage hfc)
  have hOB : c.dq.χ '' {y | morseNorm n y < r} ∩ f ⁻¹' Ioi (c.fb + 3 * β / 2) ⊆
      interior (B ∪ T) :=
    interior_maximal (fun z ⟨⟨y, hy, hyz⟩, hz⟩ => Or.inl ⟨⟨y, show morseNorm n y ≤ r from le_of_lt hy, hyz⟩,
      show c.fb + 3 * β / 2 ≤ f z from le_of_lt hz⟩) hOpen
  have hin : ∀ y : Fin n → ℝ, morseNorm n y < r → c.dq.χ y = x → x ∈ interior (B ∪ T) :=
    fun y hy hyx => hOB ⟨⟨y, hy, hyx⟩, show c.fb + 3 * β / 2 < f x by linarith⟩
  have hqray : ∀ t : ℝ, 0 < t → t ^ 2 < 9 * c.ε / 4 →
      morseNorm n (recombine c.dq.hk (t • c.u₀) 0) < r ∧
        f (c.dq.χ (recombine c.dq.hk (t • c.u₀) 0)) = f q - t ^ 2 / 2 := by
    intro t ht ht2
    have hn2 : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) ^ 2 = t ^ 2 := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq, norm_smul, hu₀, norm_zero, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hlt : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) < r :=
      (le_abs_self _).trans_lt (abs_lt_of_sq_lt_sq (by rw [hn2, hr2]; exact ht2) hr0.le)
    refine ⟨hlt, ?_⟩
    rw [c.dq.hnorm _ (by linarith), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine, DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine,
      norm_smul, hu₀, norm_zero, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  rcases c.arc_cases hx with rfl | rfl | ⟨t, ht, ht2, rfl⟩ | ⟨t, ht, ht2, rfl⟩ | ⟨s, hs, rfl, hfs⟩
  · linarith
  · exact hin 0 (by rw [morseNorm_zero]; exact hr0) c.dq.hχ0
  · exfalso
    have hn2 : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ^ 2 = t ^ 2 := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq, norm_smul, he₁, norm_zero, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hle : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ≤ c.dp.R :=
      (le_abs_self _).trans ((abs_lt_of_sq_lt_sq (by rw [hn2]; linarith) hrmp0.le).le.trans hrmRp)
    have hfx : f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) = f p + t ^ 2 / 2 := by
      rw [c.dp.hnorm _ hle, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine, DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine,
        norm_smul, he₁, norm_zero, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    rw [hfx] at hxf'
    linarith
  · exact hin _ (hqray t ht (by linarith)).1 rfl
  · by_cases h : c.D.flow s c.z₀ ∈ f ⁻¹' Iic (f q - 17 * c.ε / 16)
    · exact interior_mono subset_union_right (hTcov ⟨hx, hxf', h⟩)
    · have h' : f q - 17 * c.ε / 16 < f (c.D.flow s c.z₀) := lt_of_not_ge h
      set t : ℝ := Real.sqrt (2 * (f q - f (c.D.flow s c.z₀))) with ht_def
      have hs0 := hs.1
      have ht2 : t ^ 2 = 2 * (f q - f (c.D.flow s c.z₀)) := Real.sq_sqrt (by linarith)
      have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
      obtain ⟨hlt, hfx'⟩ := hqray t ht (by linarith)
      have hx'arc := c.q_ray_mem_arc ht (by linarith)
      have hfeq : f (c.dq.χ (recombine c.dq.hk (t • c.u₀) 0)) = f (c.D.flow s c.z₀) := by
        rw [hfx', ht2]; ring
      rcases hx'arc with (hp' | hq') | hr'
      · exfalso
        rw [hp'] at hfeq
        linarith
      · exfalso
        have hq'' : c.dq.χ (recombine c.dq.hk (t • c.u₀) 0) = q := hq'
        rw [hq''] at hfeq
        linarith
      · have := c.arc_level_inj ⟨s, rfl⟩ hr' hfeq.symm
        exact hin _ hlt this.symm

theorem exists_band_piece :
    ∃ η₀ β₀ : ℝ, 0 < η₀ ∧ 0 < β₀ ∧ β₀ ≤ c.βmax ∧ ∀ η ∈ Ioc 0 η₀, ∀ β ∈ Ioc 0 β₀,
      ∃ K : Set M, isLyapunovOn c.D c.arc K (c.blendedQuadraticFunction η β) (c.blendedArcCoordinate β) ∧
        c.arc ∩ f ⁻¹' Icc (c.fb - 2 * β) (c.fb + 2 * β) ⊆ interior K := by
  classical
  obtain ⟨β₁, hβ₁, hβ₁m, W, hWo, hWray, ⟨rW, hrW, hWtube⟩, hWprop, -, -⟩ := c.band_setup
  obtain ⟨η₂, β₂, r₂, hη₂, hβ₂, -, hr₂, hquad⟩ := c.band_quad_le
  obtain ⟨η₃, β₃, hη₃, hβ₃, -, hasc⟩ := c.band_common_ascent
  obtain ⟨he₁, hu₀, -⟩ := c.unit_dirs
  have hε : 0 < c.ε := c.hε
  have hrmR : c.D.rm p (mem_pair_left p q) ≤ c.dp.R := (c.D.hrm p (mem_pair_left p q)).2
  have hrmR' : c.D.rm p (mem_pair_left p q) < c.dp.R' := c.D.rm_lt_R' p (mem_pair_left p q)
  have hβmax : c.βmax ≤ c.ε / 16 ∧ c.βmax ≤ (f q - f p - 2 * c.ε) / 16 := by
    unfold TransverseCancellingPair.βmax
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _)⟩
  have hfb : c.fb = f p + c.ε := rfl
  have hWsrc : ∀ y ∈ W, y ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' ∧ y ∈ c.dp.χ.source ∧
      f (c.dp.χ y) = morseNormalForm c.dp.hk (f p) y := by
    intro y hy
    have h1 := (hWprop y hy).2.1
    exact ⟨mem_ball_of_morseNorm_lt (h1.trans hrmR'), c.dp.hsrc y (h1.trans_le hrmR).le,
      c.dp.hnorm y (h1.trans_le hrmR).le⟩
  have hsplit : ∀ y : Fin n → ℝ, morseNormalForm c.dp.hk (f p) y =
      f p + (1 / 2) * (‖posPart c.dp.hk y‖ ^ 2 - ‖negPart c.dp.hk y‖ ^ 2) :=
    DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split c.dp.hk (f p)
  have hrecsmul : ∀ a : ℝ, recombine c.dp.hk 0 (a • c.e₁) = a • recombine c.dp.hk 0 c.e₁ := by
    intro a
    rw [← ModelField.recombineL_apply, ← ModelField.recombineL_apply, ← map_smul]
    congr 1
    simp
  have hray : ∀ s : ℝ, c.pRayAt s = Real.sqrt (2 * (s - f p)) • recombine c.dp.hk 0 c.e₁ :=
    fun s => hrecsmul _
  have hnfrec : ∀ t : ℝ, morseNormalForm c.dp.hk (f p) (recombine c.dp.hk 0 (t • c.e₁)) =
      f p + t ^ 2 / 2 := by
    intro t
    rw [hsplit, ModelField.negPart_recombine, ModelField.posPart_recombine, norm_smul, he₁,
      norm_zero, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hnfray : ∀ s : ℝ, f p ≤ s → morseNormalForm c.dp.hk (f p) (c.pRayAt s) = s := by
    intro s hs
    unfold TransverseCancellingPair.pRayAt
    rw [hnfrec, Real.sq_sqrt (by linarith)]
    ring
  have hcontRay : Continuous c.pRayAt := by
    rw [show c.pRayAt = fun s => Real.sqrt (2 * (s - f p)) • recombine c.dp.hk 0 c.e₁ from
      funext hray]
    exact (Real.continuous_sqrt.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).smul continuous_const
  have hcontN : Continuous (morseNormalForm c.dp.hk (f p)) :=
    (ModelField.contDiff_nf c.dp.hk (f p)).continuous
  have hfsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hneg : ContDiff ℝ ∞ (negPart c.dp.hk) := (ModelField.negPartL c.dp.hk).contDiff
  have hpos : ContDiff ℝ ∞ (posPart c.dp.hk) := (ModelField.posPartL c.dp.hk).contDiff
  have hnegq : ContDiff ℝ ∞ (negPart c.dq.hk) := (ModelField.negPartL c.dq.hk).contDiff
  have hposq : ContDiff ℝ ∞ (posPart c.dq.hk) := (ModelField.posPartL c.dq.hk).contDiff
  have hpArc : ContDiff ℝ ∞ c.pArc := by
    change ContDiff ℝ ∞ (fun y => ⟪posPart c.dp.hk y, c.e₁⟫)
    exact hpos.inner ℝ contDiff_const
  have hqArc : ContDiff ℝ ∞ c.qArc := by
    change ContDiff ℝ ∞ (fun y => ⟪negPart c.dq.hk y, c.u₀⟫)
    exact hnegq.inner ℝ contDiff_const
  have hpQ : ∀ η : ℝ, ContDiff ℝ ∞ (c.pQuad η) := by
    intro η
    change ContDiff ℝ ∞ (fun y => ‖negPart c.dp.hk y‖ ^ 2 -
      η * ‖posPart c.dp.hk y - c.pArc y • c.e₁‖ ^ 2)
    exact (hneg.norm_sq ℝ).sub (contDiff_const.mul ((hpos.sub (hpArc.smul contDiff_const)).norm_sq ℝ))
  have hqQ : ∀ η : ℝ, ContDiff ℝ ∞ (c.qQuad η) := by
    intro η
    change ContDiff ℝ ∞ (fun y => η * ‖negPart c.dq.hk y - c.qArc y • c.u₀‖ ^ 2 -
      ‖posPart c.dq.hk y‖ ^ 2)
    exact (contDiff_const.mul ((hnegq.sub (hqArc.smul contDiff_const)).norm_sq ℝ)).sub
      (hposq.norm_sq ℝ)
  have hκcd : ∀ β : ℝ, ContDiff ℝ ∞ (c.κ β) := by
    intro β
    change ContDiff ℝ ∞ (fun s => 1 - CancelModel.cut (c.fb - β) (c.fb + β) s)
    exact contDiff_const.sub (CancelModel.contDiff_cut _ _)
  have hΨsm : ∀ y ∈ W, ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.qExtendedChart (c.dp.χ y) := by
    intro y hy
    have hT : c.dp.χ y ∈ c.qDom := by
      unfold TransverseCancellingPair.qDom
      exact Or.inr (hWprop y hy).2.2.1
    exact c.contMDiffOn_qExtendedChart.2.contMDiffAt (c.contMDiffOn_qExtendedChart.1.mem_nhds hT)
  have hL₀sm : ∀ η β : ℝ, ∀ y ∈ W, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (c.blendedQuadraticFunction η β) (c.dp.χ y) := by
    intro η β y hy
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.κ β (f x)) (c.dp.χ y) :=
      (hκcd β).contDiffAt.comp_contMDiffAt (hfsm _)
    have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.pQuad η (c.dp.χ.symm x)) (c.dp.χ y) :=
      (hpQ η).contDiffAt.comp_contMDiffAt (c.dp.contMDiffAt_symm ⟨y, (hWsrc y hy).1, rfl⟩)
    have h3 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.qQuad η (c.qExtendedChart x)) (c.dp.χ y) :=
      (hqQ η).contDiffAt.comp_contMDiffAt (hΨsm y hy)
    exact ((contMDiffAt_const.sub h1).mul h2).add (h1.mul h3)
  have hAsm : ∀ β : ℝ, ∀ y ∈ W, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (c.blendedArcCoordinate β) (c.dp.χ y) := by
    intro β y hy
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.κ β (f x)) (c.dp.χ y) :=
      (hκcd β).contDiffAt.comp_contMDiffAt (hfsm _)
    have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.pArc (c.dp.χ.symm x)) (c.dp.χ y) :=
      hpArc.contDiffAt.comp_contMDiffAt (c.dp.contMDiffAt_symm ⟨y, (hWsrc y hy).1, rfl⟩)
    have hρ : 0 ≤ c.ρq := Real.sqrt_nonneg _
    have hH := (c.qHeightProfile_spec.1 (c.qArc (c.qExtendedChart (c.dp.χ y)))
      (by linarith [(hWprop y hy).2.2.2.1]) (hWprop y hy).2.2.2.2).1
    have h4 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.qArc (c.qExtendedChart x)) (c.dp.χ y) :=
      hqArc.contDiffAt.comp_contMDiffAt (hΨsm y hy)
    have h3 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c.qHeightProfile (c.qArc (c.qExtendedChart x))) (c.dp.χ y) :=
      ContDiffAt.comp_contMDiffAt (f := fun x => c.qArc (c.qExtendedChart x)) (x := c.dp.χ y) hH h4
    exact ((contMDiffAt_const.sub h1).mul h2).add (h1.mul h3)
  have hR0 : recombine c.dp.hk 0 c.e₁ ≠ 0 := by
    intro h
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq c.dp.hk
      (0 : EuclideanSpace ℝ (Fin c.dp.k)) c.e₁
    rw [h, he₁, norm_zero] at h1
    simp [morseNorm_zero] at h1
  have hδpos : 0 < ‖recombine c.dp.hk 0 c.e₁‖ := norm_pos_iff.2 hR0
  refine ⟨min η₂ η₃, min β₁ (min β₂ β₃), lt_min hη₂ hη₃, lt_min hβ₁ (lt_min hβ₂ hβ₃),
    (min_le_left _ _).trans hβ₁m, ?_⟩
  rintro η ⟨hη, hηle⟩ β ⟨hβ, hβle⟩
  have hηle₂ : η ≤ η₂ := hηle.trans (min_le_left _ _)
  have hηle₃ : η ≤ η₃ := hηle.trans (min_le_right _ _)
  have hβle₁ : β ≤ β₁ := hβle.trans (min_le_left _ _)
  have hβle₂ : β ≤ β₂ := hβle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hβle₃ : β ≤ β₃ := hβle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hβm : β ≤ c.βmax := hβle₁.trans hβ₁m
  have hκ01 : ∀ s, 0 ≤ c.κ β s ∧ c.κ β s ≤ 1 := by
    intro s
    unfold TransverseCancellingPair.κ
    exact ⟨by linarith [CancelModel.cut_le_one (c.fb - β) (c.fb + β) s],
      by linarith [CancelModel.cut_nonneg (c.fb - β) (c.fb + β) s]⟩
  have hκmono : Monotone (c.κ β) := by
    intro s t hst
    unfold TransverseCancellingPair.κ
    linarith [CancelModel.cut_antitone (show c.fb - β < c.fb + β by linarith) hst]
  have hκ' : ∀ s, 0 ≤ deriv (c.κ β) s := fun s => hκmono.deriv_nonneg
  obtain ⟨r₃, μ₀, hr₃, hμ₀, hasc'⟩ := hasc η ⟨hη, hηle₃⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min (min rW r₂) (min r₃
      (Real.sqrt c.ε * ‖recombine c.dp.hk 0 c.e₁‖)) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min hrW hr₂) (lt_min hr₃ (mul_pos (Real.sqrt_pos.2 hε) hδpos))
  have hrW' : r ≤ rW := hrdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hr₂' : r ≤ r₂ := hrdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hr₃' : r ≤ r₃ := hrdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ Real.sqrt c.ε * ‖recombine c.dp.hk 0 c.e₁‖ :=
    hrdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin n → ℝ), S = {y | |morseNormalForm c.dp.hk (f p) y - c.fb| ≤
      3 * β ∧ ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ r} := ⟨_, rfl⟩
  have hSW : ∀ y ∈ S, y ∈ W ∧ |morseNormalForm c.dp.hk (f p) y - c.fb| ≤ 3 * β ∧
      ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ ≤ r := by
    intro y hy
    rw [hSdef] at hy
    exact ⟨hWtube y (hy.1.trans (by linarith)) (hy.2.trans hrW'), hy.1, hy.2⟩
  refine ⟨c.dp.χ '' S, ⟨?_, ?_, ?_, ?_, ?_, μ₀, hμ₀, ?_⟩, ?_⟩
  · have hScl : IsClosed S := by
      rw [hSdef]
      exact (isClosed_le (continuous_abs.comp (hcontN.sub continuous_const)) continuous_const).inter
        (isClosed_le ((continuous_id.sub (hcontRay.comp hcontN)).norm) continuous_const)
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := c.fb - 3 * β) (b := c.fb + 3 * β)).exists_bound_of_continuousOn
      hcontRay.continuousOn
    have hSb : S ⊆ Metric.closedBall 0 (C + r) := by
      intro y hy
      obtain ⟨-, h1, h2⟩ := hSW y hy
      have h3 := hC (morseNormalForm c.dp.hk (f p) y) ⟨by linarith [(abs_le.1 h1).1], by linarith [(abs_le.1 h1).2]⟩
      rw [mem_closedBall_zero_iff]
      calc ‖y‖ = ‖(y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)) +
            c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ r + C := add_le_add h2 h3
        _ = C + r := add_comm _ _
    have hScpt : IsCompact S := (isCompact_closedBall 0 (C + r)).of_isClosed_subset hScl hSb
    exact hScpt.image_of_continuousOn
      (c.dp.χ.continuousOn.mono fun y hy => (hWsrc y (hSW y hy).1).2.1)
  · rintro x ⟨y, hy, rfl⟩
    exact c.D.inStrip p (mem_pair_left p q) ⟨y, (hWsrc y (hSW y hy).1).1, rfl⟩
  · refine ⟨c.dp.χ '' W, (c.dp.χ.isOpen_image_iff_of_subset_source
      fun y hy => (hWsrc y hy).2.1).2 hWo, image_mono fun y hy => (hSW y hy).1, ?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact (hL₀sm η β y hy).contMDiffWithinAt
    · rintro x ⟨y, hy, rfl⟩
      exact (hAsm β y hy).contMDiffWithinAt
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨hyW, hlev, hdist⟩ := hSW y hy
    obtain ⟨hy₀, hy₁, hT, hq₀, hq⟩ := hWprop y hyW
    rw [(c.band_dfV (η := η) hβ hy₀ hy₁ (hlev.trans (by linarith)) hT hq₀ hq).1]
    have hQ := (hquad η ⟨hη, hηle₂⟩ y (hlev.trans (by linarith)) (hdist.trans hr₂')).2
    have hθp := ModelField.theta_pos c.dp.hr₀ y
    have hθq := ModelField.theta_pos c.dq.hr₀ (c.qExtendedChart (c.dp.χ y))
    obtain ⟨hk0, hk1⟩ := hκ01 (morseNormalForm c.dp.hk (f p) y)
    have hd := hκ' (morseNormalForm c.dp.hk (f p) y)
    have hP0 : 0 ≤ 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 :=
      add_nonneg (by positivity) (mul_nonneg (by linarith) (sq_nonneg _))
    have hQ0 : 0 ≤ 2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
        2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2 :=
      add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith) (mul_nonneg hθp.le hP0))
      (mul_nonneg hk0 (mul_nonneg hθq.le hQ0))) (mul_nonneg hd (by linarith))
  · rintro x ⟨y, hy, rfl⟩ hxΓ
    left
    obtain ⟨hyW, hlev, hdist⟩ := hSW y hy
    obtain ⟨hy₀, hy₁, hT, hq₀, hq⟩ := hWprop y hyW
    rw [(c.band_dfV (η := η) hβ hy₀ hy₁ (hlev.trans (by linarith)) hT hq₀ hq).1]
    have hQ := (hquad η ⟨hη, hηle₂⟩ y (hlev.trans (by linarith)) (hdist.trans hr₂')).2
    have hθp := ModelField.theta_pos c.dp.hr₀ y
    have hθq := ModelField.theta_pos c.dq.hr₀ (c.qExtendedChart (c.dp.χ y))
    obtain ⟨hk0, hk1⟩ := hκ01 (morseNormalForm c.dp.hk (f p) y)
    have hd := hκ' (morseNormalForm c.dp.hk (f p) y)
    have hP0 : 0 ≤ 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 :=
      add_nonneg (by positivity) (mul_nonneg (by linarith) (sq_nonneg _))
    have hQ0 : 0 ≤ 2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
        2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2 :=
      add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
    have hT1 := mul_nonneg (sub_nonneg.2 hk1) (mul_nonneg hθp.le hP0)
    have hT2 := mul_nonneg hk0 (mul_nonneg hθq.le hQ0)
    have hT3 := mul_nonneg hd (sub_nonneg.2 hQ)
    by_contra hle
    push Not at hle
    rcases hk1.lt_or_eq with hk1' | hk1'
    · have hP : 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 = 0 := by
        by_contra hPne
        have h1 : 0 < 2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2 :=
          lt_of_le_of_ne hP0 (Ne.symm hPne)
        have h2 := mul_pos (sub_pos.2 hk1') (mul_pos hθp h1)
        linarith
      have hu : negPart c.dp.hk y = 0 := by
        have h1 : ‖negPart c.dp.hk y‖ ^ 2 = 0 := by
          linarith only [hP, sq_nonneg ‖negPart c.dp.hk y‖, mul_nonneg hη.le (sq_nonneg ‖c.pPerp y‖)]
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
      have hv : c.pPerp y = 0 := by
        have h1 : η * ‖c.pPerp y‖ ^ 2 = 0 := by
          linarith only [hP, sq_nonneg ‖negPart c.dp.hk y‖, mul_nonneg hη.le (sq_nonneg ‖c.pPerp y‖)]
        have h2 : ‖c.pPerp y‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hη.ne'
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      obtain ⟨t, ht⟩ : ∃ t, t = c.pArc y := ⟨_, rfl⟩
      have hyeq : y = recombine c.dp.hk 0 (t • c.e₁) := by
        have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dp.hk y
        have h2 : posPart c.dp.hk y = t • c.e₁ := by
          rw [ht]
          exact sub_eq_zero.1 hv
        rw [hu, h2] at h1
        exact h1.symm
      have hnfy : morseNormalForm c.dp.hk (f p) y = f p + t ^ 2 / 2 := by
        rw [hyeq]
        exact hnfrec t
      rw [hnfy, hfb] at hlev
      have hlev' := abs_le.1 hlev
      rcases le_or_gt t 0 with ht0 | ht0
      · have hst : Real.sqrt c.ε < -t := by
          rw [show -t = Real.sqrt ((-t) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
          exact Real.sqrt_lt_sqrt hε.le (by linarith only [hlev'.1, hβm, hβmax.1, hε])
        have hray' : c.pRayAt (morseNormalForm c.dp.hk (f p) y) =
            (-t) • recombine c.dp.hk 0 c.e₁ := by
          rw [hray, hnfy]
          congr 1
          rw [show 2 * (f p + t ^ 2 / 2 - f p) = (-t) ^ 2 by ring]
          exact Real.sqrt_sq (by linarith)
        have hdiff : y - c.pRayAt (morseNormalForm c.dp.hk (f p) y) =
            (2 * t) • recombine c.dp.hk 0 c.e₁ := by
          rw [hray']
          conv_lhs => rw [hyeq]
          rw [hrecsmul, ← sub_smul]
          congr 1
          ring
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : 2 * t ≤ 0)] at hdist
        linarith only [hdist, hrδ, mul_lt_mul_of_pos_right hst hδpos,
          mul_nonpos_of_nonpos_of_nonneg ht0 hδpos.le]
      · apply hxΓ
        rw [hyeq]
        exact c.p_ray_mem_arc ht0 (by linarith only [hlev'.2, hβm, hβmax.1, hε])
    · rw [hk1'] at hle
      have hQz : 2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
          2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2 = 0 := by
        by_contra hQne
        have h1 : 0 < 2 * η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 +
            2 * ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2 := lt_of_le_of_ne hQ0 (Ne.symm hQne)
        have h2 := mul_pos hθq h1
        rw [hk1'] at hT2 hT1
        linarith
      have hqp : c.qPerp (c.qExtendedChart (c.dp.χ y)) = 0 := by
        have h1 : η * ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 = 0 := by
          linarith only [hQz, sq_nonneg ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖,
            mul_nonneg hη.le (sq_nonneg ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖)]
        have h2 : ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hη.ne'
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      have hvp : posPart c.dq.hk (c.qExtendedChart (c.dp.χ y)) = 0 := by
        have h1 : ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖ ^ 2 = 0 := by
          linarith only [hQz, sq_nonneg ‖posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))‖,
            mul_nonneg hη.le (sq_nonneg ‖c.qPerp (c.qExtendedChart (c.dp.χ y))‖)]
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
      have hdom : c.dp.χ y ∈ c.qDom := by
        unfold TransverseCancellingPair.qDom
        exact Or.inr hT
      exact hxΓ (c.mem_arc_of_qExtendedChart hdom hqp hvp hq₀.le)
  · rintro μ hμ hμle x ⟨y, hy, rfl⟩ - hzero
    obtain ⟨hyW, hlev, hdist⟩ := hSW y hy
    obtain ⟨hy₀, hy₁, hT, hq₀, hq⟩ := hWprop y hyW
    obtain ⟨hk0, hk1⟩ := hκ01 (morseNormalForm c.dp.hk (f p) y)
    have hθp := ModelField.theta_pos c.dp.hr₀ y
    have hθq := ModelField.theta_pos c.dq.hr₀ (c.qExtendedChart (c.dp.χ y))
    by_cases hray0 : y = c.pRayAt (morseNormalForm c.dp.hk (f p) y)
    · have hlin : dfV I (fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x) c.D.V (c.dp.χ y) =
          dfV I (c.blendedQuadraticFunction η β) c.D.V (c.dp.χ y) + μ * dfV I (c.blendedArcCoordinate β) c.D.V (c.dp.χ y) := by
        have h1 := ((hL₀sm η β y hyW).mdifferentiableAt (by simp)).hasMFDerivAt
        have h2 := (((hAsm β y hyW).mdifferentiableAt (by simp)).hasMFDerivAt).const_smul μ
        have h3 := (h1.add h2).mfderiv
        have hfun : (c.blendedQuadraticFunction η β + μ • c.blendedArcCoordinate β) = fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x := by
          funext x
          simp [smul_eq_mul]
        rw [hfun] at h3
        unfold dfV
        rw [h3]
        rfl
      have h0 : dfV I (fun x => c.blendedQuadraticFunction η β x + μ * c.blendedArcCoordinate β x) c.D.V (c.dp.χ y) = 0 := by
        unfold dfV
        rw [hzero]
        simp
      obtain ⟨hL, hA⟩ := c.band_dfV (η := η) hβ hy₀ hy₁ (hlev.trans (by linarith)) hT hq₀ hq
      have hlev' := abs_le.1 hlev
      rw [hfb] at hlev'
      obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt (2 * (morseNormalForm c.dp.hk (f p) y - f p)) :=
        ⟨_, rfl⟩
      have ht : 0 < t := by
        rw [htdef]
        exact Real.sqrt_pos.2 (by linarith only [hlev'.1, hβm, hβmax.1, hε])
      have ht2 : t ^ 2 = 2 * (morseNormalForm c.dp.hk (f p) y - f p) := by
        rw [htdef]
        exact Real.sq_sqrt (by linarith only [hlev'.1, hβm, hβmax.1, hε])
      have hyr : y = recombine c.dp.hk 0 (t • c.e₁) := by
        rw [htdef]
        exact hray0
      have hu : negPart c.dp.hk y = 0 := by
        rw [hyr, ModelField.negPart_recombine]
      have hpA : c.pArc y = t := by
        unfold TransverseCancellingPair.pArc
        rw [hyr, ModelField.posPart_recombine, inner_smul_left, real_inner_self_eq_norm_sq, he₁]
        simp
      have hpP : c.pPerp y = 0 := by
        unfold TransverseCancellingPair.pPerp
        rw [hpA, sub_eq_zero, hyr, ModelField.posPart_recombine]
      have hpQ0 : c.pQuad η y = 0 := by
        unfold TransverseCancellingPair.pQuad
        rw [hu, hpP]
        simp
      have hΨ := (c.qExtendedChart_p_ray ht (by
        rw [ht2, abs_le]
        constructor <;> linarith only [hlev'.1, hlev'.2, hβm])).2
      rw [← hyr] at hΨ
      obtain ⟨U, hUdef⟩ : ∃ U, U = Real.sqrt (c.sqSum - t ^ 2) := ⟨_, rfl⟩
      rw [← hUdef] at hΨ
      have hqA : c.qArc (c.qExtendedChart (c.dp.χ y)) = U := by
        unfold TransverseCancellingPair.qArc
        rw [hΨ, ModelField.negPart_recombine, inner_smul_left, real_inner_self_eq_norm_sq, hu₀]
        simp
      have hqP : c.qPerp (c.qExtendedChart (c.dp.χ y)) = 0 := by
        unfold TransverseCancellingPair.qPerp
        rw [hqA, sub_eq_zero, hΨ, ModelField.negPart_recombine]
      have hqv : posPart c.dq.hk (c.qExtendedChart (c.dp.χ y)) = 0 := by
        rw [hΨ, ModelField.posPart_recombine]
      have hqQ0 : c.qQuad η (c.qExtendedChart (c.dp.χ y)) = 0 := by
        unfold TransverseCancellingPair.qQuad
        rw [hqP, hqv]
        simp
      have hHq : c.qHeightProfile U = t := by
        have hmem : morseNormalForm c.dp.hk (f p) y ∈
            Icc (c.fb - 3 * c.βmax) (c.fb + 3 * c.βmax) := by
          rw [hfb]
          constructor <;> linarith only [hlev'.1, hlev'.2, hβm]
        have h1 := c.qHeightProfile_spec.2 _ hmem
        have h2 : U = Real.sqrt (2 * (f q - morseNormalForm c.dp.hk (f p) y)) := by
          rw [hUdef, ht2]
          congr 1
          unfold TransverseCancellingPair.sqSum TransverseCancellingPair.cq TransverseCancellingPair.fb
          ring
        rw [h2, h1, htdef]
      have hU : 0 < U := hqA ▸ hq₀
      have hHd : deriv c.qHeightProfile U < 0 := by
        have hρ : 0 ≤ c.ρq := Real.sqrt_nonneg _
        have h1 := (c.qHeightProfile_spec.1 (c.qArc (c.qExtendedChart (c.dp.χ y))) (by linarith only [hρ, hq₀]) hq).2
        rwa [hqA] at h1
      have e1 : dfV I (c.blendedQuadraticFunction η β) c.D.V (c.dp.χ y) = 0 := by
        rw [hL, hu, hpP, hqP, hqv, hpQ0, hqQ0]
        simp
      have e2 : dfV I (c.blendedArcCoordinate β) c.D.V (c.dp.χ y) =
          (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) * (-(ModelField.theta c.dp.r₀ y * t)) +
            c.κ β (morseNormalForm c.dp.hk (f p) y) *
              (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) * (deriv c.qHeightProfile U * U)) := by
        rw [hA, hpA, hqA, hHq]
        ring
      have hneg : (1 - c.κ β (morseNormalForm c.dp.hk (f p) y)) *
            (-(ModelField.theta c.dp.r₀ y * t)) +
            c.κ β (morseNormalForm c.dp.hk (f p) y) *
              (ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) * (deriv c.qHeightProfile U * U)) < 0 := by
        have hqneg : ModelField.theta c.dq.r₀ (c.qExtendedChart (c.dp.χ y)) * (deriv c.qHeightProfile U * U) < 0 :=
          mul_neg_of_pos_of_neg hθq (mul_neg_of_neg_of_pos hHd hU)
        have hpneg : -(ModelField.theta c.dp.r₀ y * t) < 0 := neg_neg_of_pos (mul_pos hθp ht)
        rcases hk1.lt_or_eq with hk1' | hk1'
        · have h1 := mul_neg_of_pos_of_neg (sub_pos.2 hk1') hpneg
          have h2 := mul_nonpos_of_nonneg_of_nonpos hk0 hqneg.le
          linarith only [h1, h2]
        · rw [hk1', sub_self, zero_mul, zero_add, one_mul]
          exact hqneg
      rw [hlin, e1, e2] at h0
      have := mul_neg_of_pos_of_neg hμ hneg
      linarith only [this, h0]
    · obtain ⟨w, hw0, hwp, hwq⟩ := hasc' μ ⟨hμ, hμle⟩ y (hlev.trans (by linarith))
        (hdist.trans hr₃') hray0
      have hg := c.band_glue_deriv (η := η) (μ := μ) hβ (hy₁.trans_le hrmR) hT hq w
      rw [hzero, hw0] at hg
      simp only [zero_apply, mul_zero, zero_mul, add_zero] at hg
      change (0 : ℝ) = _ at hg
      have hwp' : 0 < (fderiv ℝ (fun z => c.pQuad η z + μ * c.pArc z) y) w := hwp
      have hwq' : 0 < (fderiv ℝ (fun z => c.qQuad η (c.qExtendedChart (c.dp.χ z)) +
          μ * c.qHeightProfile (c.qArc (c.qExtendedChart (c.dp.χ z)))) y) w := hwq
      rcases hk1.lt_or_eq with hk1' | hk1'
      · have h1 := mul_pos (sub_pos.2 hk1') hwp'
        have h2 := mul_nonneg hk0 hwq'.le
        linarith only [h1, h2, hg]
      · rw [hk1', sub_self, zero_mul, zero_add, one_mul] at hg
        linarith only [hg, hwq']
  · rintro x ⟨hxΓ, hxlev⟩
    have hxlev' : c.fb - 2 * β ≤ f x ∧ f x ≤ c.fb + 2 * β := hxlev
    rw [hfb] at hxlev'
    have hfxp : f p < f x := by linarith only [hxlev'.1, hβm, hβmax.1, hε]
    have hfxq : f x < f q := by linarith only [hxlev'.2, hβm, hβmax.2, hβ, hε]
    have hxr : x ∈ range (fun t : ℝ => c.D.flow t c.z₀) := by
      rcases hxΓ with (h | h) | h
      · rw [h] at hfxp
        exact absurd hfxp (lt_irrefl _)
      · rw [h] at hfxq
        exact absurd hfxq (lt_irrefl _)
      · exact h
    obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt (2 * (f x - f p)) := ⟨_, rfl⟩
    have ht : 0 < t := by
      rw [htdef]
      exact Real.sqrt_pos.2 (by linarith only [hfxp])
    have ht2 : t ^ 2 = 2 * (f x - f p) := by
      rw [htdef]
      exact Real.sq_sqrt (by linarith only [hfxp])
    have hmemI : f x ∈ Icc (c.fb - 3 * β₁) (c.fb + 3 * β₁) := by
      rw [hfb]
      constructor <;> linarith only [hxlev'.1, hxlev'.2, hβle₁, hβ]
    have hrayW := hWray (f x) hmemI
    have hnfx : morseNormalForm c.dp.hk (f p) (c.pRayAt (f x)) = f x := hnfray (f x) hfxp.le
    have hz'lev : f (c.dp.χ (c.pRayAt (f x))) = f x := by
      rw [(hWsrc _ hrayW).2.2, hnfx]
    have hz'arc : c.dp.χ (c.pRayAt (f x)) ∈ c.arc := by
      have h1 := c.p_ray_mem_arc ht (by
        rw [ht2]
        linarith only [hxlev'.2, hβm, hβmax.1, hε])
      rw [htdef] at h1
      exact h1
    have hz'r : c.dp.χ (c.pRayAt (f x)) ∈ range (fun t : ℝ => c.D.flow t c.z₀) := by
      rcases hz'arc with (h | h) | h
      · rw [h] at hz'lev
        linarith only [hz'lev, hfxp]
      · rw [h] at hz'lev
        linarith only [hz'lev, hfxq]
      · exact h
    have hxz : x = c.dp.χ (c.pRayAt (f x)) := c.arc_level_inj hxr hz'r hz'lev.symm
    obtain ⟨S', hS'def⟩ : ∃ S' : Set (Fin n → ℝ), S' = {y | |morseNormalForm c.dp.hk (f p) y -
        c.fb| < 3 * β ∧ ‖y - c.pRayAt (morseNormalForm c.dp.hk (f p) y)‖ < r} := ⟨_, rfl⟩
    have hS'o : IsOpen S' := by
      rw [hS'def]
      exact (isOpen_lt (continuous_abs.comp (hcontN.sub continuous_const)) continuous_const).inter
        (isOpen_lt ((continuous_id.sub (hcontRay.comp hcontN)).norm) continuous_const)
    have hS'S : S' ⊆ S := by
      rw [hS'def, hSdef]
      exact fun y hy => ⟨hy.1.le, hy.2.le⟩
    have hopen : IsOpen (c.dp.χ '' S') :=
      (c.dp.χ.isOpen_image_iff_of_subset_source
        fun y hy => (hWsrc y (hSW y (hS'S hy)).1).2.1).2 hS'o
    have hmem : c.pRayAt (f x) ∈ S' := by
      rw [hS'def]
      refine ⟨?_, ?_⟩
      · rw [hnfx, abs_lt, hfb]
        constructor <;> linarith only [hxlev'.1, hxlev'.2, hβ]
      · rw [hnfx, sub_self, norm_zero]
        exact hr
    rw [hxz]
    exact interior_maximal (image_mono hS'S) hopen ⟨_, hmem, rfl⟩

theorem exists_lyapunovNbhd [SigmaCompactSpace M] : ∃ U : Set M, isLyapunovNbhd c.D c.arc U := by
  obtain ⟨η₀, β₀, hη₀, hβ₀, hβm, hband⟩ := c.exists_band_piece
  obtain ⟨Kb, hKb, hcovb⟩ := hband η₀ ⟨hη₀, le_rfl⟩ β₀ ⟨hβ₀, le_rfl⟩
  obtain ⟨Kp, hKp, hcovp⟩ := c.exists_p_piece hη₀ hβ₀ hβm
  obtain ⟨Kq, hKq, hcovq⟩ := c.exists_q_piece hη₀ hβ₀ hβm
  refine ⟨_, isLyapunovNbhd_of_isLyapunovOn ((hKp.union hKb).union hKq) ?_⟩
  intro x hx
  have hsub₁ : interior Kp ⊆ interior (Kp ∪ Kb ∪ Kq) :=
    interior_mono (subset_union_left.trans subset_union_left)
  have hsub₂ : interior Kb ⊆ interior (Kp ∪ Kb ∪ Kq) :=
    interior_mono (subset_union_right.trans subset_union_left)
  have hsub₃ : interior Kq ⊆ interior (Kp ∪ Kb ∪ Kq) := interior_mono subset_union_right
  rcases le_or_gt (f x) (c.fb - 2 * β₀) with h₁ | h₁
  · exact hsub₁ (hcovp ⟨hx, h₁⟩)
  rcases le_or_gt (f x) (c.fb + 2 * β₀) with h₂ | h₂
  · exact hsub₂ (hcovb ⟨hx, h₁.le, h₂⟩)
  · exact hsub₃ (hcovq ⟨hx, h₂.le⟩)

end TransverseCancellingPair

theorem crossfield_target [SigmaCompactSpace M] [DecidableEq M] (h : isCancellingPair I f a' b' p q) :
    ∃ V' : (x : M) → TangentSpace I x, isCrossingField I f a' b' V' := by
  obtain ⟨c⟩ := nonempty_transverseCancellingPair h
  obtain ⟨U, hUc, hΓU, hUs, hL⟩ := c.exists_lyapunovNbhd
  obtain ⟨hΓc, -⟩ := c.isCompact_arc
  obtain ⟨U', hU'o, hΓU', hU'U, hnr⟩ := exists_noReturn c.D c.hf.smooth c.hf.compact hΓc
    (fun t x hx => c.flow_mem_arc t hx) (fun x hx hxΓ => c.dichotomy x hx hxΓ) isOpen_interior
    hΓU (interior_subset.trans (hUs.trans (preimage_mono Ioo_subset_Icc_self)))
  obtain ⟨L, hLs, hLE⟩ := hL U' hU'o hΓU'
  have hεr : ∀ r (hr : r ∈ ({p, q} : Finset M)),
      (c.D.chart r hr).r₀ ^ 2 < 2 * c.ε ∧ 8 * c.ε < c.D.rm r hr ^ 2 := by
    intro r hr
    rcases mem_pair_iff.1 hr with rfl | rfl
    · exact ⟨c.hr₀p, c.hrmp⟩
    · exact ⟨c.hr₀q, c.hrmq⟩
  have hcritU : ∀ r ∈ ({p, q} : Finset M), r ∈ U := by
    intro r hr
    rcases mem_pair_iff.1 hr with rfl | rfl
    · exact interior_subset (hΓU c.p_mem_arc)
    · exact interior_subset (hΓU c.q_mem_arc)
  have hnr' : noReturn c.D U U' := fun x hx s t hs hst hout =>
    hnr x hx s t hs hst (fun hin => hout (interior_subset hin))
  exact exists_crossingField_of_lyapunov c.hf c.D c.hε hεr hUc hUs hU'o
    (hU'U.trans interior_subset) hcritU hnr' hLs hLE

end CrossField

end

end DifferentialGeometry.Topology
