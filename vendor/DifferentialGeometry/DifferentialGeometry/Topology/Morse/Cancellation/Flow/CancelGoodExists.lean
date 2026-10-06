module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelGood

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

theorem armPt_succ_eq :
    c.d.armPt c.hkq c.ε (c.i + 1) = (-(c.σ * Real.sqrt (2 * c.ε))) • c.e₀' := by
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  unfold MorseNormalChart.armPt e₀' e₀ σ
  rw [← ModelField.recombineL_apply, ← ModelField.recombineL_apply, ← map_smul]
  congr 1
  rcases hcases c.i with h | h <;> rw [h] <;> simp

def sheetNeg (v : EuclideanSpace ℝ (Fin (n - c.d.k))) : Fin n → ℝ :=
  (-(c.σ * Real.sqrt (2 * c.ε + ‖v‖ ^ 2))) • c.e₀' + recombine c.d.hk 0 v

theorem sheetNeg_zero : c.sheetNeg 0 = c.d.armPt c.hkq c.ε (c.i + 1) := by
  rw [c.armPt_succ_eq]
  unfold sheetNeg
  rw [norm_zero, zero_pow two_ne_zero, add_zero]
  have : recombine c.d.hk (0 : EuclideanSpace ℝ (Fin c.d.k))
      (0 : EuclideanSpace ℝ (Fin (n - c.d.k))) = 0 := by
    rw [← ModelField.recombineL_apply]; exact map_zero _
  rw [this, add_zero]

theorem posPart_sheetNeg (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    posPart c.d.hk (c.sheetNeg v) = v := by
  unfold sheetNeg
  rw [ModelField.posPart_add, ModelField.posPart_smul, c.posPart_e₀', smul_zero, zero_add,
    ModelField.posPart_recombine]

theorem negPart_sheetNeg (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    negPart c.d.hk (c.sheetNeg v) =
      (-(c.σ * Real.sqrt (2 * c.ε + ‖v‖ ^ 2))) • negPart c.d.hk c.e₀' := by
  unfold sheetNeg
  rw [ModelField.negPart_add, ModelField.negPart_smul, ModelField.negPart_recombine, add_zero]

theorem uq_sheetNeg (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    uq c.d.hk c.hkq (c.sheetNeg v) = -(c.σ * Real.sqrt (2 * c.ε + ‖v‖ ^ 2)) := by
  have h := c.uq_e₀'
  rw [uq_apply] at h ⊢
  rw [c.negPart_sheetNeg, PiLp.smul_apply, smul_eq_mul, h, mul_one]

theorem morseNorm_sheetNeg_sq (v : EuclideanSpace ℝ (Fin (n - c.d.k))) :
    morseNorm n (c.sheetNeg v) ^ 2 = 2 * c.ε + 2 * ‖v‖ ^ 2 := by
  have hε := c.hε
  rw [morseNorm_sq_eq_uq c.d.hk c.hkq, c.uq_sheetNeg, c.posPart_sheetNeg, neg_sq, mul_pow,
    Real.sq_sqrt (by positivity), sq, c.σ_sq, one_mul]
  ring

theorem continuous_sheetNeg : Continuous c.sheetNeg := by
  have h1 : Continuous fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) =>
      -(c.σ * Real.sqrt (2 * c.ε + ‖v‖ ^ 2)) :=
    (continuous_const.mul ((continuous_const.add (continuous_norm.pow 2)).sqrt)).neg
  have h2 : Continuous fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) =>
      recombine c.d.hk (0 : EuclideanSpace ℝ (Fin c.d.k)) v := by
    have := (ModelField.recombineL c.d.hk).continuous.comp
      (continuous_const.prodMk continuous_id :
        Continuous fun v : EuclideanSpace ℝ (Fin (n - c.d.k)) =>
          ((0 : EuclideanSpace ℝ (Fin c.d.k)), v))
    refine this.congr fun v => ?_
    exact ModelField.recombineL_apply c.d.hk 0 v
  exact (h1.smul continuous_const).add h2

theorem eq_sheetNeg {y : Fin n → ℝ} (hnf : morseNormalForm c.d.hk (f q) y = f q - c.ε)
    (hu : c.σ * uq c.d.hk c.hkq y < 0) : y = c.sheetNeg (posPart c.d.hk y) := by
  have hε := c.hε
  have hσ2 := c.σ_sq
  have hk1 : c.d.k = 1 := c.hkq
  have hu2 : uq c.d.hk c.hkq y ^ 2 = 2 * c.ε + ‖posPart c.d.hk y‖ ^ 2 := by
    rw [morseNormalForm_split, norm_negPart_sq c.d.hk c.hkq] at hnf
    linarith
  have hσu2 : (c.σ * uq c.d.hk c.hkq y) ^ 2 = 2 * c.ε + ‖posPart c.d.hk y‖ ^ 2 := by
    rw [mul_pow, hu2]; nlinarith
  have hσu : c.σ * uq c.d.hk c.hkq y = -Real.sqrt (2 * c.ε + ‖posPart c.d.hk y‖ ^ 2) := by
    have h1 : Real.sqrt (2 * c.ε + ‖posPart c.d.hk y‖ ^ 2) = |c.σ * uq c.d.hk c.hkq y| := by
      rw [← hσu2, Real.sqrt_sq_eq_abs]
    rw [h1, abs_of_neg hu, neg_neg]
  have huq : uq c.d.hk c.hkq y = -(c.σ * Real.sqrt (2 * c.ε + ‖posPart c.d.hk y‖ ^ 2)) := by
    linear_combination c.σ * hσu - uq c.d.hk c.hkq y * hσ2
  apply c.eq_of_parts
  · rw [c.negPart_sheetNeg]
    ext i
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
    rw [hi, PiLp.smul_apply, smul_eq_mul]
    have h := c.uq_e₀'
    rw [uq_apply] at h
    rw [h, mul_one]
    exact huq
  · rw [c.posPart_sheetNeg]

theorem sheetNeg_sq_lt {v : EuclideanSpace ℝ (Fin (n - c.d.k))} (hv : ‖v‖ ^ 2 < c.ε / 2) :
    morseNorm n (c.sheetNeg v) ^ 2 < 3 * c.ε := by
  rw [c.morseNorm_sheetNeg_sq]; linarith

theorem hi₁_le_of_mem_qSupportRegion (k : c.CancelConsts) {y : Fin n → ℝ}
    (hy : y ∈ qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB) : c.hi₁ ≤ f (c.d.χ y) := by
  have hyR : morseNorm n y ≤ c.d.R := by
    have := (morseNorm_sq_le_of_mem_qSupportRegion c.d.hk c.hkq hy).trans k.Kq_radius_lt.le
    exact ((Real.le_sqrt (ModelField.morseNorm_nonneg y) (by linarith [c.hε])).2 this).trans
      (by linarith [c.sqrt_three_ε_lt_rmq, (c.D.hrm q c.hq).2])
  rw [c.f_chart_q hyR]
  have := hy.1
  have := c.uB_sq_eq
  nlinarith [sq_nonneg ‖posPart c.d.hk y‖]

theorem image_pSupportRegion_subset_modelBall (k : c.CancelConsts) :
    c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB ⊆ c.e.χ '' {y | morseNorm n y < c.D.rm p c.hp} :=
  image_mono fun _ hy => hy.1.trans_lt (by
    have := c.ρB_sq_lt_three_ε; have := c.three_ε_lt_rmp_sq; have := c.rmp_pos
    have := c.ρB_pos
    nlinarith)

theorem exists_T₂ (k : c.CancelConsts) (hSb : k.closedFlowTube ⊆ c.D.basin p c.hp) :
    ∃ T₂, 0 ≤ T₂ ∧ (∀ s ∈ Icc 0 T₂, c.D.flow s c.z₁ ∉ k.perturbationSupportRegion) ∧ f (c.D.flow T₂ c.z₁) < a' := by
  obtain ⟨T₁, hT₁, hfT₁, hgt⟩ := c.exists_other_arm_exit
  have havoid : ∀ s, 0 ≤ s → c.D.flow s c.z₁ ∉ k.perturbationSupportRegion := by
    intro s hs hK
    rcases hK with (hKp | hKq) | hS
    · exact c.z₁_notMem_basin ⟨s, hs, c.image_pSupportRegion_subset_modelBall k hKp⟩
    · obtain ⟨y, hy, hyz⟩ := hKq
      have h1 := c.hi₁_le_of_mem_qSupportRegion k hy
      rw [hyz] at h1
      have h2 := f_flow_le c.hfs (D := c.D) c.z₁ hs
      rw [c.f_z₁] at h2
      linarith [c.f_q_sub_ε_lt_hi₁]
    · have := hSb hS
      rw [flow_mem_basin_iff (D := c.D) c.hkp] at this
      exact c.z₁_notMem_basin this
  have hunit : dfV I f c.D.V (c.D.flow T₁ c.z₁) = -1 := by
    refine c.D.unit _ ⟨hfT₁.ge, by rw [hfT₁]; exact c.hf.lt.le⟩ fun p' hp' hmem => ?_
    have := c.f_mem_of_mem_smallBall (hp' := hp') hmem
    rw [hfT₁] at this
    linarith [this.1, c.η₀_pos]
  obtain ⟨s₀, hlt, hs₀⟩ :=
    ((eventually_f_flow_lt (D := c.D) c.hfs hunit).and self_mem_nhdsWithin).exists
  have hs₀' : (0 : ℝ) < s₀ := hs₀
  rw [flow_flow, hfT₁] at hlt
  exact ⟨T₁ + s₀, by linarith, fun s hs => havoid s hs.1, hlt⟩

theorem negPart_sq_of_nf {y : Fin n → ℝ} (hnf : morseNormalForm c.d.hk (f q) y = f q - c.ε) :
    ‖negPart c.d.hk y‖ ^ 2 = 2 * c.ε + ‖posPart c.d.hk y‖ ^ 2 := by
  rw [morseNormalForm_split] at hnf; linarith

theorem exists_ρ₁ (k : c.CancelConsts) (hSb : k.closedFlowTube ⊆ c.D.basin p c.hp) :
    ∃ ρ₁ T₂ : ℝ, 0 < ρ₁ ∧ 0 ≤ T₂ ∧ ρ₁ ^ 2 ≤ c.ε ∧
      ∀ y : Fin n → ℝ, morseNormalForm c.d.hk (f q) y = f q - c.ε →
        c.σ * uq c.d.hk c.hkq y < 0 →
        4 * (‖negPart c.d.hk y‖ ^ 2 * ‖posPart c.d.hk y‖ ^ 2) ≤ ρ₁ ^ 4 →
        (∀ s ∈ Icc 0 T₂, c.D.flow s (c.d.χ y) ∉ k.perturbationSupportRegion) ∧ f (c.D.flow T₂ (c.d.χ y)) < a' := by
  obtain ⟨T₂, hT₂, havoid, hfT₂⟩ := c.exists_T₂ k hSb
  have hε := c.hε
  set N : Set M := {x | (∀ s ∈ Icc 0 T₂, c.D.flow s x ∉ k.perturbationSupportRegion) ∧ f (c.D.flow T₂ x) < a'} with hN
  have hN₁ : {x | ∀ s ∈ Icc 0 T₂, c.D.flow s x ∉ k.perturbationSupportRegion} ∈ 𝓝 c.z₁ := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := c.z₁)
      (P := fun x s => c.D.flow s x ∉ k.perturbationSupportRegion) fun s hs => ?_
    have hopen : IsOpen {z : M × ℝ | c.D.flow z.2 z.1 ∉ k.perturbationSupportRegion} :=
      k.isClosed_perturbationSupportRegion.isOpen_compl.preimage
        (c.D.continuous_flow_joint.comp (continuous_snd.prodMk continuous_fst))
    exact hopen.mem_nhds (havoid s hs)
  have hN₂ : {x | f (c.D.flow T₂ x) < a'} ∈ 𝓝 c.z₁ :=
    (isOpen_lt (c.hfs.continuous.comp (c.D.continuous_flow T₂)) continuous_const).mem_nhds hfT₂
  have hNz : N ∈ 𝓝 c.z₁ := inter_mem hN₁ hN₂
  have h0ball : c.sheetNeg 0 ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' := by
    refine mem_ball_of_morseNorm_lt ?_
    have h1 : morseNorm n (c.sheetNeg 0) ^ 2 < 3 * c.ε := c.sheetNeg_sq_lt (by
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.ofNat_pos,
        div_pos_iff_of_pos_right]
      positivity)
    exact (c.morseNorm_lt_rmq_of_sq_lt h1).trans (c.D.rm_lt_R' q c.hq)
  have hg : ContinuousAt (fun v => c.d.χ (c.sheetNeg v)) 0 := by
    refine ContinuousAt.comp ?_ c.continuous_sheetNeg.continuousAt
    exact c.d.χ.continuousOn.continuousAt
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds h0ball) c.d.hball)
  have hg0 : c.d.χ (c.sheetNeg 0) = c.z₁ := by rw [c.sheetNeg_zero]; rfl
  have hpre : (fun v => c.d.χ (c.sheetNeg v)) ⁻¹' N ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin (n - c.d.k))) :=
    hg.preimage_mem_nhds (by rw [hg0]; exact hNz)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨min r (Real.sqrt c.ε), T₂, lt_min hr (Real.sqrt_pos.2 hε), hT₂, ?_, ?_⟩
  · have : min r (Real.sqrt c.ε) ≤ Real.sqrt c.ε := min_le_right _ _
    have h2 := Real.sq_sqrt hε.le
    nlinarith [Real.sqrt_nonneg c.ε, lt_min hr (Real.sqrt_pos.2 hε)]
  intro y hnf hu hprod
  set ρ₁ := min r (Real.sqrt c.ε) with hρ₁
  have hρ₁r : ρ₁ ≤ r := min_le_left _ _
  have hρ₁ε : ρ₁ ^ 2 ≤ c.ε := by
    have : ρ₁ ≤ Real.sqrt c.ε := min_le_right _ _
    have h2 := Real.sq_sqrt hε.le
    nlinarith [Real.sqrt_nonneg c.ε, lt_min hr (Real.sqrt_pos.2 hε)]
  have hρ₁0 : 0 < ρ₁ := lt_min hr (Real.sqrt_pos.2 hε)
  have hv : ‖posPart c.d.hk y‖ ^ 2 ≤ ρ₁ ^ 2 / 8 := by
    rw [c.negPart_sq_of_nf hnf] at hprod
    have h1 : ρ₁ ^ 4 = ρ₁ ^ 2 * ρ₁ ^ 2 := by ring
    rw [h1] at hprod
    have h2 : ρ₁ ^ 2 * ρ₁ ^ 2 ≤ ρ₁ ^ 2 * c.ε := mul_le_mul_of_nonneg_left hρ₁ε (sq_nonneg _)
    nlinarith [sq_nonneg ‖posPart c.d.hk y‖]
  have hvr : posPart c.d.hk y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - c.d.k))) r := by
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖posPart c.d.hk y‖ ^ 2 < ρ₁ ^ 2 := by nlinarith
    have h2 : ‖posPart c.d.hk y‖ < ρ₁ :=
      (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ₁0.le two_ne_zero).1 h1
    exact h2.trans_le hρ₁r
  have hyN := hrN hvr
  rw [mem_preimage, ← c.eq_sheetNeg hnf hu] at hyN
  exact hyN

theorem closedFlowTube_subset_basin_of (k : c.CancelConsts)
    (hH : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ ≤ k.δ' →
      ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall') : k.closedFlowTube ⊆ c.D.basin p c.hp := by
  intro x hx
  have hT := k.mem_orientedChartTube_of_mem_closedFlowTube hx
  obtain ⟨hv2, hHm⟩ := hH _ (k.norm_ζ_le_of_mem_closedFlowTube hx)
  have hHσ := c.flowedSheet_ζ hT hv2
  rw [← flow_mem_basin_iff (D := c.D) c.hkp (f x - c.c₁), ← hHσ]
  exact ⟨0, le_rfl, by rw [c.D.flow_zero]; exact c.pBall'_subset_pBall hHm⟩

theorem exists_mζ (k : c.CancelConsts) : ∃ m : ℝ, 0 < m ∧ ∀ y : Fin n → ℝ,
    c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB → k.b₀ ≤ axialDefect c.e₁ y →
    c.e.χ y ∈ c.orientedChartTube → ‖c.ζ (c.e.χ y)‖ ≤ k.δ' → m ≤ ‖c.ζ (c.e.χ y)‖ := by
  set B : Set (Fin n → ℝ) := {y | c.ρA ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧
    k.b₀ ≤ axialDefect c.e₁ y ∧ c.e.χ y ∈ k.closedFlowTube} with hB
  have hρA := c.ρA_pos
  have hBc : IsCompact B := by
    have h1 : IsClosed ({y : Fin n → ℝ | c.ρA ≤ morseNorm n y} ∩ (axialDefect c.e₁) ⁻¹' Ici k.b₀) := by
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_
        (isClosed_le continuous_const continuous_morseNorm) isClosed_Ici
      intro y hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        have : c.ρA ≤ morseNorm n (0 : Fin n → ℝ) := hy
        rw [morseNorm_zero] at this; linarith
      exact (contDiffAt_axialDefect c.e₁ hy0).continuousAt.continuousWithinAt
    have h2 : IsClosed ({y : Fin n → ℝ | morseNorm n y ≤ c.ρB} ∩ c.e.χ ⁻¹' k.closedFlowTube) := by
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_
        (isClosed_le continuous_morseNorm continuous_const) k.isClosed_closedFlowTube
      exact c.e.χ.continuousOn.mono fun y hy =>
        c.e.hball (mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy c.ρB_lt_R'))
    have hBeq : B = ({y : Fin n → ℝ | c.ρA ≤ morseNorm n y} ∩ (axialDefect c.e₁) ⁻¹' Ici k.b₀) ∩
        ({y : Fin n → ℝ | morseNorm n y ≤ c.ρB} ∩ c.e.χ ⁻¹' k.closedFlowTube) := by
      ext y
      simp only [hB, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici]
      tauto
    rw [hBeq]
    exact (isCompact_morseNorm_le c.ρB).of_isClosed_subset (h1.inter h2)
      fun _ hy => hy.2.1
  have hcont : ContinuousOn (fun y => ‖c.ζ (c.e.χ y)‖) B := by
    refine ContinuousOn.norm (c.continuousOn_ζ.comp ?_ ?_)
    · exact c.e.χ.continuousOn.mono fun y hy =>
        c.e.hball (mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy.2.1 c.ρB_lt_R'))
    · intro y hy
      exact (k.mem_orientedChartTube_of_mem_closedFlowTube hy.2.2.2).1
  have hpos : ∀ y ∈ B, 0 < ‖c.ζ (c.e.χ y)‖ := by
    intro y hy
    rw [norm_pos_iff]
    intro hζ
    have hT := k.mem_orientedChartTube_of_mem_closedFlowTube hy.2.2.2
    have hsq : morseNorm n y ^ 2 < 3 * c.ε := c.sq_lt_three_ε_of_le_ρB hy.2.1
    have hax := (c.axis_of_ζ_eq_zero_p hsq hT hζ).1
    have hB0 : axialDefect c.e₁ y = 0 := by
      have hpos' : 0 < morseNorm n y := hρA.trans_le hy.1
      rw [hax, axialDefect_smul_self c.morseNorm_e₁ hpos']
    have := hy.2.2.1
    rw [hB0] at this
    linarith [k.b₀_pos]
  have hmem : ∀ y, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB → k.b₀ ≤ axialDefect c.e₁ y →
      c.e.χ y ∈ c.orientedChartTube → ‖c.ζ (c.e.χ y)‖ ≤ k.δ' → y ∈ B := by
    intro y h1 h2 h3 hT hζ
    refine ⟨h1, h2, h3, k.mem_closedFlowTube_iff.2 ⟨hT, ?_, hζ⟩⟩
    rw [c.f_chart_p (h2.trans c.ρB_le_R)]
    have hA := c.ρA_sq_eq
    have hB' := c.ρB_sq_eq
    have hl := pow_le_pow_left₀ hρA.le h1 2
    have hu := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) h2 2
    have := c.c₁_sub_half_lt_lo₁
    have := c.lo₂_lt_hi₁
    have := c.hi₁_mem_levels
    constructor <;> linarith
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨1, one_pos, fun y h1 h2 h3 hT hζ => ?_⟩
    have := hmem y h1 h2 h3 hT hζ
    rw [hBe] at this
    exact absurd this (notMem_empty y)
  · obtain ⟨y₀, hy₀, hmin⟩ := hBc.exists_isMinOn hBne hcont
    refine ⟨‖c.ζ (c.e.χ y₀)‖, hpos y₀ hy₀, fun y h1 h2 h3 hT hζ => ?_⟩
    exact hmin (hmem y h1 h2 h3 hT hζ)

theorem perturbationSupportRegion_antitone {k k' : c.CancelConsts} (hδ : k.δ ≤ k'.δ) (hδ' : k.δ' = k'.δ')
    (hτ : k.τ = k'.τ) : k.perturbationSupportRegion ⊆ k'.perturbationSupportRegion := by
  have hδ0 := k.hδ
  rintro x ((hKp | hKq) | hS)
  · left; left
    obtain ⟨y, hy, rfl⟩ := hKp
    refine ⟨y, ⟨hy.1, ?_, ?_⟩, rfl⟩
    · rw [← hτ]; nlinarith [hy.2.1]
    · linarith [hy.2.2]
  · left; right
    obtain ⟨y, hy, rfl⟩ := hKq
    refine ⟨y, ⟨hy.1, ?_, ?_⟩, rfl⟩
    · rw [← hτ]; nlinarith [hy.2.1]
    · linarith [hy.2.2]
  · right
    have : k.closedFlowTube = k'.closedFlowTube := by unfold CancelConsts.closedFlowTube CancelConsts.qTubeCoordinates; rw [hδ']
    rw [← this]; exact hS

theorem G6_arith {ε r₀ ε₂ η δ' τ δ uB νm : ℝ} (hε : 0 < ε)
    (hε₂ : ε₂ = (r₀ ^ 2 / 2 + ε) / 2) (hη0 : 0 < η) (hη : η ≤ (2 * ε - r₀ ^ 2) / 8)
    (huB : uB ^ 2 = 2 * ε₂ + η / 2) (hτ : τ ^ 2 ≤ 1 / 4)
    (hν : νm ^ 2 = δ' ^ 2 * (2 * ε₂ + δ' ^ 2) / (2 * ε₂ - η))
    (hδ'1 : δ' ^ 2 ≤ ε / 16)
    (hδ'2 : δ' ^ 2 ≤ 21 * (2 * ε - r₀ ^ 2) * (2 * ε₂ - η) / (384 * ε))
    (hδ : 4 * δ ^ 2 < 21 * (2 * ε - r₀ ^ 2) / 64) :
    4 * δ ^ 2 < 3 * ε - (1 + 2 * τ ^ 2) * uB ^ 2 - 2 * νm ^ 2 := by
  have hr0 : 0 ≤ r₀ ^ 2 := sq_nonneg _
  have hpos : 0 < 2 * ε₂ - η := by rw [hε₂]; linarith
  have h3 : δ' ^ 2 * (2 * ε₂ + δ' ^ 2) ≤ δ' ^ 2 * (3 * ε) :=
    mul_le_mul_of_nonneg_left (by rw [hε₂]; linarith) (sq_nonneg _)
  have h4 : δ' ^ 2 * (384 * ε) ≤ 21 * (2 * ε - r₀ ^ 2) * (2 * ε₂ - η) :=
    (le_div_iff₀ (by positivity)).1 hδ'2
  have h1 : νm ^ 2 ≤ 21 * (2 * ε - r₀ ^ 2) / 128 := by
    rw [hν, div_le_iff₀ hpos]; nlinarith
  have huB0 : 0 ≤ uB ^ 2 := sq_nonneg _
  have h2 : (1 + 2 * τ ^ 2) * uB ^ 2 ≤ (3 / 2) * uB ^ 2 := by nlinarith
  subst hε₂
  linarith [h1, h2, hδ, hη, huB]

theorem exists_good : ∃ k : c.CancelConsts, Nonempty k.Good := by
  have hε := c.hε
  have hr₀q := c.hr₀q
  have hρ := c.ρA_pos
  have hε₂η := c.two_ε₂_sub_η_pos
  have hη0 := c.η_pos
  obtain ⟨r₁, hr₁, hr₁H⟩ := c.exists_r₁
  obtain ⟨δ₀, hδ₀, hδ₀L⟩ := c.exists_dB_neg_level
  obtain ⟨δ₀', hδ₀', hdB⟩ := c.exists_dB_neg
  set δ'' := min (min r₁ δ₀) (min δ₀' (Real.sqrt c.ε / 2)) with hδ''def
  have hsε : 0 < Real.sqrt c.ε := Real.sqrt_pos.2 hε
  have hsε2 := Real.sq_sqrt hε.le
  have hδ''0 : 0 < δ'' := lt_min (lt_min hr₁ hδ₀) (lt_min hδ₀' (by positivity))
  have hδ''r₁ : δ'' ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ''δ₀ : δ'' ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ''δ₀' : δ'' ≤ δ₀' := (min_le_right _ _).trans (min_le_left _ _)
  have hδ''s : δ'' ≤ Real.sqrt c.ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδ''ε : δ'' ^ 2 < c.ε := by nlinarith
  set cG6 := 21 * (2 * c.ε - c.d.r₀ ^ 2) * (2 * c.ε₂ - c.η) / (384 * c.ε) with hcG6def
  have hcG6 : 0 < cG6 := by
    have : 0 < 2 * c.ε - c.d.r₀ ^ 2 := by linarith
    positivity
  set δ' := min (δ'' / 2) (Real.sqrt cG6 / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'δ'' : δ' < δ'' := (min_le_left _ _).trans_lt (by linarith)
  have hδ'ε : δ' ^ 2 < c.ε := by nlinarith
  have hδ'16 : δ' ^ 2 ≤ c.ε / 16 := by
    have : δ' ≤ Real.sqrt c.ε / 4 := (min_le_left _ _).trans (by linarith)
    nlinarith
  have hδ'8 : 8 * δ' ^ 2 ≤ c.ε := by linarith
  have hδ'G6 : δ' ^ 2 ≤ cG6 := by
    have h1 : δ' ≤ Real.sqrt cG6 / 2 := min_le_right _ _
    have h2 := Real.sq_sqrt hcG6.le
    nlinarith [Real.sqrt_nonneg cG6]
  have hδ'δ₀' : δ' < δ₀' := hδ'δ''.trans_le hδ''δ₀'
  obtain ⟨r, hr, hball⟩ := c.exists_cone_ball hδ'0
  set τ := min (1 / 2) (r / (4 * c.ρA)) with hτdef
  set δa := min (δ' / 3) (r / 8) with hδadef
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hδa : 0 < δa := lt_min (by positivity) (by positivity)
  have hτ1 : τ ^ 2 ≤ 1 / 4 := by
    have : τ ≤ 1 / 2 := min_le_left _ _
    nlinarith
  have hδaδ' : 2 * δa < δ' := by
    have : δa ≤ δ' / 3 := min_le_left _ _
    linarith
  have hsmall : 2 * c.ρA ^ 2 * τ ^ 2 + 4 * δa ^ 2 < r ^ 2 := by
    have h1 : τ ≤ r / (4 * c.ρA) := min_le_right _ _
    have h2 : δa ≤ r / 8 := min_le_right _ _
    have h3 : τ ^ 2 ≤ (r / (4 * c.ρA)) ^ 2 := pow_le_pow_left₀ hτ.le h1 2
    have h4 : δa ^ 2 ≤ (r / 8) ^ 2 := pow_le_pow_left₀ hδa.le h2 2
    have h5 : 2 * c.ρA ^ 2 * (r / (4 * c.ρA)) ^ 2 = r ^ 2 / 8 := by field_simp; ring
    have h6 : 2 * c.ρA ^ 2 * τ ^ 2 ≤ r ^ 2 / 8 := by
      rw [← h5]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have hdB' : ∀ y : Fin n → ℝ, morseNorm n y ^ 2 < 3 * c.ε → c.e.χ y ∈ c.orientedChartTube →
      0 < ‖c.ζ (c.e.χ y)‖ → ‖c.ζ (c.e.χ y)‖ < δ' → axialDefectDeriv c.e₁ y (c.pTransverseField y) < 0 :=
    fun y hy hx hζ0 hζδ => hdB y hy hx hζ0 (hζδ.trans hδ'δ₀')
  let k₁ : c.CancelConsts := ⟨δa, δ', τ, hδa, hδaδ', hδ'ε, hτ, hτ1, hdB',
    fun y h1 h2 h3 h4 => c.cone_of_ball hr hball hsmall y h1 h2 h3 h4⟩
  obtain ⟨mζ, hmζ, hζmin₁⟩ := c.exists_mζ k₁
  have hH : ∀ v : EuclideanSpace ℝ (Fin (n - c.d.k)), ‖v‖ ≤ k₁.δ' →
      ‖v‖ ^ 2 < c.ε ∧ c.flowedSheet v ∈ c.pBall' := fun v hv => by
    have := hr₁H v (lt_of_le_of_lt hv (hδ'δ''.trans_le hδ''r₁))
    exact ⟨this.1, this.2.1⟩
  obtain ⟨ρ₁, T₂, hρ₁, hT₂, -, harm₁⟩ := c.exists_ρ₁ k₁ (c.closedFlowTube_subset_basin_of k₁ hH)
  set νmax := Real.sqrt (k₁.νm ^ 2 + τ ^ 2 * c.uB ^ 2 + 2 * δa ^ 2) with hνmaxdef
  have hνmax : 0 < νmax := Real.sqrt_pos.2 (by positivity)
  have hνmax2 : νmax ^ 2 = k₁.νm ^ 2 + τ ^ 2 * c.uB ^ 2 + 2 * δa ^ 2 :=
    Real.sq_sqrt (by positivity)
  set R6 := 21 * (2 * c.ε - c.d.r₀ ^ 2) / 64 with hR6def
  have hR6 : 0 < R6 := by
    have : 0 < 2 * c.ε - c.d.r₀ ^ 2 := by linarith
    positivity
  set δ := min (min δa (mζ / 2)) (min (Real.sqrt R6 / 4) (ρ₁ ^ 2 / (4 * νmax))) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδa (by positivity))
    (lt_min (by positivity) (by positivity))
  have hδδa : δ ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
  have hδm : δ ≤ mζ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδR6 : δ ≤ Real.sqrt R6 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδρ : δ ≤ ρ₁ ^ 2 / (4 * νmax) := (min_le_right _ _).trans (min_le_right _ _)
  have hδδ' : 2 * δ < δ' := by linarith
  have hsmall' : 2 * c.ρA ^ 2 * τ ^ 2 + 4 * δ ^ 2 < r ^ 2 := by
    have : δ ^ 2 ≤ δa ^ 2 := pow_le_pow_left₀ hδ0.le hδδa 2
    linarith
  let k : c.CancelConsts := ⟨δ, δ', τ, hδ0, hδδ', hδ'ε, hτ, hτ1, hdB',
    fun y h1 h2 h3 h4 => c.cone_of_ball hr hball hsmall' y h1 h2 h3 h4⟩
  have hKsub : k.perturbationSupportRegion ⊆ k₁.perturbationSupportRegion := c.perturbationSupportRegion_antitone (k := k) (k' := k₁) hδδa rfl rfl
  refine ⟨k, ⟨⟨δ'', hδ'δ'', hδ''ε, ?_, ?_, hδ'8, ?_, ?_, ρ₁, T₂, hρ₁, hT₂, ?_, ?_⟩⟩⟩
  · intro v hv
    exact hr₁H v (hv.trans_le hδ''r₁)
  · intro v hv0 hv
    exact (hδ₀L v hv0 (hv.trans_le hδ''δ₀)).2.2
  · intro y h1 h2 h3 hT
    by_cases hζ : ‖c.ζ (c.e.χ y)‖ ≤ δ'
    · have := hζmin₁ y h1 h2 h3 hT hζ
      linarith
    · push Not at hζ
      linarith
  · change 4 * δ ^ 2 < 3 * c.ε - (1 + 2 * τ ^ 2) * c.uB ^ 2 - 2 * k.νm ^ 2
    have hδ4 : 4 * δ ^ 2 < R6 := by
      have h1 : δ ^ 2 ≤ (Real.sqrt R6 / 4) ^ 2 := pow_le_pow_left₀ hδ0.le hδR6 2
      have h2 := Real.sq_sqrt hR6.le
      have h3 : (Real.sqrt R6 / 4) ^ 2 = R6 / 16 := by rw [div_pow, h2]; ring
      linarith only [h1, h3, hR6]
    refine G6_arith (ε := c.ε) (r₀ := c.d.r₀) (ε₂ := c.ε₂) (η := c.η) (δ' := δ') (τ := τ)
      (δ := δ) (uB := c.uB) (νm := k.νm) hε (by unfold IndexZeroCancellingPair.ε₂; ring) hη0 ?_ c.uB_sq
      hτ1 ?_ hδ'16 hδ'G6 hδ4
    · have h1 : c.η ≤ (c.ε₂ - c.d.r₀ ^ 2 / 2) / 2 := by
        unfold η; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have h2 : c.ε₂ - c.d.r₀ ^ 2 / 2 = (2 * c.ε - c.d.r₀ ^ 2) / 4 := by unfold ε₂; ring
      linarith
    · rw [k.νm_sq]
      change δ' ^ 2 * (2 * c.ε₂ + δ' ^ 2) / (2 * c.ε₂ - c.η) = _
      rfl
  · intro y hnf hu hprod
    obtain ⟨havoid, hf⟩ := harm₁ y hnf hu hprod
    exact ⟨fun s hs hK => havoid s hs (hKsub hK), hf⟩
  · change 16 * δ ^ 2 * k.ν ^ 2 ≤ ρ₁ ^ 4
    have hν2 : k.ν ^ 2 ≤ νmax ^ 2 := by
      rw [k.ν_sq, hνmax2]
      have : δ ^ 2 ≤ δa ^ 2 := pow_le_pow_left₀ hδ0.le hδδa 2
      change k₁.νm ^ 2 + τ ^ 2 * c.uB ^ 2 + 2 * δ ^ 2 ≤ k₁.νm ^ 2 + τ ^ 2 * c.uB ^ 2 + 2 * δa ^ 2
      linarith
    have h1 : δ ^ 2 ≤ (ρ₁ ^ 2 / (4 * νmax)) ^ 2 := pow_le_pow_left₀ hδ0.le hδρ 2
    have h2 : (ρ₁ ^ 2 / (4 * νmax)) ^ 2 * νmax ^ 2 = ρ₁ ^ 4 / 16 := by
      field_simp; ring
    have h3 : 16 * δ ^ 2 * k.ν ^ 2 ≤ 16 * ((ρ₁ ^ 2 / (4 * νmax)) ^ 2 * νmax ^ 2) := by
      have := mul_le_mul h1 hν2 (sq_nonneg _) (sq_nonneg _)
      linarith
    rw [h2] at h3
    linarith

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
