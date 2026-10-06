module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerDefs

@[expose] public section

set_option autoImplicit false

open Set Filter Function

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart)

namespace IndexOnePartner

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

section Sard

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem sardMap_circ (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hk : (D.chart q hq).k = 2) (ε c t : ℝ) :
    D.sardMap p hq ε c ε hp (fun i => circ2 t (Fin.cast hk i)) =
      rightFun D p hp ε c (leftLoop D q hq hk ε c t) := rfl

theorem exists_angle_of_mem_leftModelSphere (D : GradientLikeStrip I f a b crit) {q : M}
    (hq : q ∈ crit) (hk : (D.chart q hq).k = 2) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ}
    (hy : y ∈ (D.chart q hq).leftModelSphere ε) :
    ∃ t : ℝ, y = (D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)) := by
  have _hT2 : T2Space M := inferInstance
  have _hBl : I.Boundaryless := inferInstance
  set e := D.chart q hq with he
  obtain ⟨hw0, hwy⟩ := e.sphereParam_of_mem hε hy
  set w : Fin e.k → ℝ := (EuclideanSpace.equiv (Fin e.k) ℝ) (negPart e.hk y) with hw
  set z : ℂ := ⟨w (Fin.cast hk.symm 0), w (Fin.cast hk.symm 1)⟩ with hz
  have hall : ∀ i : Fin e.k, i = Fin.cast hk.symm 0 ∨ i = Fin.cast hk.symm 1 := by
    intro i
    have hi := i.isLt
    rcases Nat.lt_or_ge i.val 1 with h | h
    · left; exact Fin.ext (by simp; omega)
    · right; exact Fin.ext (by simp; omega)
  have hz0 : z ≠ 0 := by
    intro h0
    apply hw0
    funext i
    have h1 : w (Fin.cast hk.symm 0) = 0 := by
      have := congrArg Complex.re h0; simpa [hz] using this
    have h2 : w (Fin.cast hk.symm 1) = 0 := by
      have := congrArg Complex.im h0; simpa [hz] using this
    rcases hall i with h | h
    · rw [h]; exact h1
    · rw [h]; exact h2
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  refine ⟨Complex.arg z / (2 * Real.pi), ?_⟩
  have hang : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
    field_simp
  have hwr : w = ‖z‖ • fun i => circ2 (Complex.arg z / (2 * Real.pi)) (Fin.cast hk i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, circ2, hang]
    rcases hall i with h | h
    · subst h
      simp only [Fin.cast_cast, Fin.cast_eq_self, Matrix.cons_val_zero]
      rw [Complex.cos_arg hz0, mul_div_cancel₀ _ hzn.ne']
    · subst h
      simp only [Fin.cast_cast, Fin.cast_eq_self, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Complex.sin_arg, mul_div_cancel₀ _ hzn.ne']
  have hne : (fun i => circ2 (Complex.arg z / (2 * Real.pi)) (Fin.cast hk i)) ≠ 0 := by
    intro h0
    apply hw0
    rw [hwr, h0, smul_zero]
  rw [← hwy, hwr, e.sphereParam_smul ε hzn hne]

theorem flow_eq_of_agree_along {g : M → ℝ} {a' b' : ℝ} {crit' : Finset M}
    (D : GradientLikeStrip I f a b crit) (D' : GradientLikeStrip I g a' b' crit') {x : M} {T : ℝ}
    (h : ∀ s ∈ uIcc 0 T, D'.V (D.flow s x) = D.V (D.flow s x)) : D'.flow T x = D.flow T x := by
  rcases eq_or_ne T 0 with hT | hT
  · subst hT
    simp
  set y := D.flow (T / 2) x with hy
  set c : ℝ → M := (fun t => D'.flow t y) ∘ (· + (-(T / 2))) with hc
  have hcI : IsMIntegralCurve c D'.V := (D'.isMIntegralCurve_flow y).comp_add _
  have hlt : min 0 T < max 0 T := min_lt_max.mpr hT.symm
  have hγ : IsMIntegralCurveOn (fun t => D.flow t x) D'.V (Ioo (min 0 T) (max 0 T)) := by
    intro t ht
    have h1 := ((D.isMIntegralCurve_flow x).isMIntegralCurveOn (Ioo (min 0 T) (max 0 T))) t ht
    have h2 := h t (Ioo_subset_Icc_self ht)
    simp only at h1 ⊢
    rw [h2]
    exact h1
  have ht₀ : T / 2 ∈ Ioo (min 0 T) (max 0 T) := by
    rcases lt_or_gt_of_ne hT with h' | h'
    · rw [min_eq_right h'.le, max_eq_left h'.le]
      constructor <;> linarith
    · rw [min_eq_left h'.le, max_eq_right h'.le]
      constructor <;> linarith
  have hcT : c (T / 2) = D.flow (T / 2) x := by
    simp [hc, hy]
  have heq : EqOn (fun t => D.flow t x) c (Ioo (min 0 T) (max 0 T)) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ D'.smooth_one hγ
      (hcI.isMIntegralCurveOn _) hcT.symm
  have hcont1 : Continuous (fun t => D.flow t x) := (D.isMIntegralCurve_flow x).continuous
  have hcont2 : Continuous c := hcI.continuous
  have heqc : EqOn (fun t => D.flow t x) c (closure (Ioo (min 0 T) (max 0 T))) :=
    heq.closure hcont1 hcont2
  rw [closure_Ioo hlt.ne] at heqc
  have h0 : D.flow 0 x = c 0 := heqc ⟨min_le_left _ _, le_max_left _ _⟩
  have hTe : D.flow T x = c T := heqc ⟨min_le_right _ _, le_max_right _ _⟩
  rw [D.flow_zero] at h0
  have hc0 : c 0 = D'.flow (-(T / 2)) y := by
    simp only [hc, Function.comp_apply, zero_add]
  have hcT' : c T = D'.flow (-(T / 2) + T) y := by
    simp only [hc, Function.comp_apply]
    ring_nf
  rw [hTe, h0, hc0, ← D'.flow_add, hcT']

theorem leftLoop_eq_of_le (D : GradientLikeStrip I f a b crit) {q : M} (hq : q ∈ crit)
    (hk : (D.chart q hq).k = 2) {ε ε' c : ℝ} (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hr₀ : (D.chart q hq).r₀ ^ 2 < 2 * ε') (hR' : 2 * ε < (D.chart q hq).R' ^ 2)
    (hmodel : ∀ y, morseNorm n y ^ 2 ≤ 2 * ε → posPart (D.chart q hq).hk y = 0 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart q hq).χ.symm ((D.chart q hq).χ y)
        (D.V ((D.chart q hq).χ y)) = ModelField.modelField (D.chart q hq).k (D.chart q hq).r₀ y) :
    leftLoop D q hq hk ε' c = leftLoop D q hq hk ε c ∧
      (∀ y ∈ (D.chart q hq).leftModelSphere ε',
        D.flow (ε - ε') ((D.chart q hq).χ y) ∈
          (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε) ∧
      ∀ y ∈ (D.chart q hq).leftModelSphere ε', ∀ s ∈ Icc 0 (ε - ε'), ∀ x (hx : x ∈ crit),
        D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx := by
  have hr₀pos := (D.chart q hq).hr₀
  have hR'pos : 0 < (D.chart q hq).R' := by
    linarith [(D.chart q hq).hRR', (D.chart q hq).hr₀R]
  have hmsq : ∀ y ∈ (D.chart q hq).leftModelSphere ε', ∀ c : ℝ,
      morseNorm n (c • y) ^ 2 = c ^ 2 * (2 * ε') := by
    intro y hy c
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart q hq).hk, ModelField.negPart_smul, ModelField.posPart_smul, hy.1, smul_zero,
      norm_zero, norm_smul, mul_pow, hy.2, Real.norm_eq_abs, sq_abs]
    ring
  have hpos0 : ∀ y ∈ (D.chart q hq).leftModelSphere ε', ∀ c : ℝ,
      posPart (D.chart q hq).hk (c • y) = 0 := by
    intro y hy c
    rw [ModelField.posPart_smul, hy.1, smul_zero]
  have hball : ∀ y ∈ (D.chart q hq).leftModelSphere ε', ∀ s ∈ Icc 0 (ε - ε'),
      Real.sqrt (1 + s / ε') • y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' ∧
        (D.chart q hq).r₀ ^ 2 < morseNorm n (Real.sqrt (1 + s / ε') • y) ^ 2 := by
    intro y hy s hs
    have h1 : 0 ≤ 1 + s / ε' := by have := div_nonneg hs.1 hε'.le; linarith
    have h2 : morseNorm n (Real.sqrt (1 + s / ε') • y) ^ 2 = 2 * ε' + 2 * s := by
      rw [hmsq y hy, Real.sq_sqrt h1]
      field_simp
    refine ⟨mem_ball_of_morseNorm_lt ?_, by rw [h2]; linarith [hs.1]⟩
    apply lt_of_pow_lt_pow_left₀ 2 hR'pos.le
    rw [h2]
    linarith [hs.2]
  have hmain : ∀ y ∈ (D.chart q hq).leftModelSphere ε', ∀ s ∈ Icc 0 (ε - ε'),
      D.flow s ((D.chart q hq).χ y) = (D.chart q hq).χ (Real.sqrt (1 + s / ε') • y) := by
    intro y hy
    rcases hε'ε.lt_or_eq with hlt | heq
    swap
    · intro s hs
      have hs0 : s = 0 := by rw [heq, sub_self] at hs; exact le_antisymm hs.2 hs.1
      subst hs0
      simp
    have hT : 0 < ε - ε' := sub_pos.2 hlt
    set δ := (2 * ε' - (D.chart q hq).r₀ ^ 2) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδε' : δ < ε' := by rw [hδ]; nlinarith
    set γ : ℝ → M := fun τ => (D.chart q hq).χ (Real.sqrt (1 + τ / ε') • y) with hγ
    have hint : IsMIntegralCurveOn γ D.V (Ioo (-δ) (ε - ε')) := by
      intro τ hτ
      apply HasMFDerivAt.hasMFDerivWithinAt
      have hτ1 : 0 < 1 + τ / ε' := by
        have : -1 < τ / ε' := by rw [lt_div_iff₀ hε']; linarith [hτ.1]
        linarith
      set g := Real.sqrt (1 + τ / ε') with hg
      have hgpos : 0 < g := Real.sqrt_pos.2 hτ1
      have hg2 : g ^ 2 = 1 + τ / ε' := Real.sq_sqrt hτ1.le
      have hms : morseNorm n (g • y) ^ 2 = 2 * ε' + 2 * τ := by
        rw [hmsq y hy, hg2]; field_simp
      have hζb : g • y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' := by
        apply mem_ball_of_morseNorm_lt
        apply lt_of_pow_lt_pow_left₀ 2 hR'pos.le
        rw [hms]; linarith [hτ.2]
      have hr : (D.chart q hq).r₀ / 2 ≤ morseNorm n (g • y) := by
        have h1 : (D.chart q hq).r₀ < morseNorm n (g • y) := by
          apply lt_of_pow_lt_pow_left₀ 2 (ModelField.morseNorm_nonneg _)
          rw [hms]; linarith [hτ.1]
        linarith
      have hdesc : ModelField.modelDesc (D.chart q hq).k (g • y) = g • y := by
        have hz := hpos0 y hy g
        have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose
          (D.chart q hq).hk (ModelField.modelDesc (D.chart q hq).k (g • y))
        rw [ModelField.negPart_modelDesc, ModelField.posPart_modelDesc, hz, neg_zero] at h1
        have h2 := DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose
          (D.chart q hq).hk (g • y)
        rw [hz] at h2
        exact h1.symm.trans h2
      have hfield : ModelField.modelField (D.chart q hq).k (D.chart q hq).r₀ (g • y) =
          (2 * ε' + 2 * τ)⁻¹ • (g • y) := by
        rw [ModelField.modelField, hdesc, ModelField.theta_eq hr₀pos hr, hms]
      have hmod := hmodel (g • y) (by rw [hms]; linarith [hτ.2]) (hpos0 y hy g)
      have hder : HasDerivAt (fun τ => Real.sqrt (1 + τ / ε') • y)
          ((2 * ε' + 2 * τ)⁻¹ • (g • y)) τ := by
        have h1 : HasDerivAt (fun τ => 1 + τ / ε') (1 / ε') τ := by
          simpa using ((hasDerivAt_id τ).div_const ε').const_add 1
        have h2 := (h1.sqrt hτ1.ne').smul_const y
        convert h2 using 1
        rw [smul_smul]
        congr 1
        rw [← hg]
        field_simp
        have hετ : 0 < ε' + τ := by
          have := mul_pos hε' hτ1
          rw [mul_add, mul_one, mul_div_cancel₀ _ hε'.ne'] at this
          exact this
        rw [div_eq_one_iff_eq hετ.ne', hg2]
        field_simp
      have hx : (D.chart q hq).χ (g • y) ∈ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' :=
        mem_image_of_mem _ hζb
      have hleft : (D.chart q hq).χ.symm ((D.chart q hq).χ (g • y)) = g • y :=
        (D.chart q hq).χ.left_inv ((D.chart q hq).hball hζb)
      have hBA : mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart q hq).χ (g • y)
          (mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart q hq).χ.symm ((D.chart q hq).χ (g • y))
            (D.V ((D.chart q hq).χ (g • y)))) = D.V ((D.chart q hq).χ (g • y)) := by
        have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) ((D.chart q hq).χ (g • y))
          ((D.chart q hq).mdifferentiableAt_chart ((D.chart q hq).symm_mem_ball hx))
          ((D.chart q hq).mdifferentiableAt_symm hx)
        have hev : ((D.chart q hq).χ ∘ (D.chart q hq).χ.symm) =ᶠ[𝓝 ((D.chart q hq).χ (g • y))]
            id :=
          eventuallyEq_of_mem ((D.chart q hq).isOpen_image_ball.mem_nhds hx)
            fun x hx => (D.chart q hq).symm_image_eq hx
        have h1 := hev.mfderiv_eq (I := I) (I' := I)
        rw [mfderiv_id] at h1
        have h2 := DFunLike.congr_fun (hcomp.symm.trans h1) (D.V ((D.chart q hq).χ (g • y)))
        rw [hleft] at h2
        exact h2
      have hχd : HasMFDerivAt 𝓘(ℝ, Fin n → ℝ) I (D.chart q hq).χ (g • y)
          (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart q hq).χ (g • y)) :=
        ((D.chart q hq).mdifferentiableAt_chart hζb).hasMFDerivAt
      have hζd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun τ => Real.sqrt (1 + τ / ε') • y) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight ((2 * ε' + 2 * τ)⁻¹ • (g • y))) :=
        hasMFDerivAt_iff_hasFDerivAt.2 hder.hasFDerivAt
      have hc := hχd.comp τ hζd
      refine hc.congr_mfderiv ?_
      apply ContinuousLinearMap.ext_ring
      change mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart q hq).χ (g • y)
          ((1 : ℝ) • ((2 * ε' + 2 * τ)⁻¹ • (g • y))) = (1 : ℝ) • D.V (γ τ)
      rw [one_smul, one_smul, ← hfield, ← hmod, hBA]
    have hint' : IsMIntegralCurveOn (fun t => D.flow t ((D.chart q hq).χ y)) D.V
        (Ioo (-δ) (ε - ε')) := fun t _ => (D.isMIntegralCurve_flow _ t).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      ⟨by linarith, hT⟩ D.smooth_one hint' hint (by simp [γ])
    have hcont : ContinuousOn γ (Icc 0 (ε - ε')) :=
      (D.chart q hq).χ.continuousOn.comp
        (((Real.continuous_sqrt.comp (continuous_const.add
          (continuous_id.div_const ε'))).smul continuous_const).continuousOn)
        (fun s hs => (D.chart q hq).hball (hball y hy s hs).1)
    have hEq : EqOn (fun t => D.flow t ((D.chart q hq).χ y)) γ (Icc 0 (ε - ε')) :=
      EqOn.of_subset_closure (s := Ico 0 (ε - ε')) (fun t ht => heq ⟨by linarith [ht.1], ht.2⟩)
        (D.continuous_flow_curve _).continuousOn hcont Ico_subset_Icc_self
        (by rw [closure_Ico hT.ne])
    exact fun s hs => hEq hs
  refine ⟨?_, ?_, ?_⟩
  · funext t
    set w : Fin (D.chart q hq).k → ℝ := fun i => circ2 t (Fin.cast hk i) with hw
    have hscale : (D.chart q hq).sphereParam ε w =
        Real.sqrt (1 + (ε - ε') / ε') • (D.chart q hq).sphereParam ε' w := by
      have h1 : 1 + (ε - ε') / ε' = ε / ε' := by field_simp; ring
      have h2 : Real.sqrt (2 * ε) = Real.sqrt (ε / ε') * Real.sqrt (2 * ε') := by
        rw [← Real.sqrt_mul (div_nonneg (by linarith) hε'.le)]
        congr 1
        field_simp
      rw [h1, MorseNormalChart.sphereParam, MorseNormalChart.sphereParam,
        ← ModelField.recombineL_apply, ← ModelField.recombineL_apply, ← map_smul, Prod.smul_mk,
        smul_zero, smul_smul, h2, mul_div_assoc]
    have hflow : D.flow (ε - ε') ((D.chart q hq).χ ((D.chart q hq).sphereParam ε' w)) =
        (D.chart q hq).χ ((D.chart q hq).sphereParam ε w) := by
      by_cases hw0 : w = 0
      · have hz : ∀ e, (D.chart q hq).sphereParam e w = 0 := by
          intro e
          rw [hw0, MorseNormalChart.sphereParam, MorseNormalChart.toE, map_zero, smul_zero,
            ← ModelField.recombineL_apply, Prod.mk_zero_zero, map_zero]
        rw [hz, hz, (D.chart q hq).hχ0, D.flow_crit hq]
      · rw [hmain _ ((D.chart q hq).sphereParam_mem_leftModelSphere hε'.le hw0) _
          ⟨sub_nonneg.2 hε'ε, le_rfl⟩, hscale]
    change D.flow (f q - ε' - c) (leftPt D q hq hk ε' t) = D.flow (f q - ε - c) (leftPt D q hq hk ε t)
    unfold leftPt
    rw [show f q - ε' - c = (ε - ε') + (f q - ε - c) by ring, D.flow_add, hflow]
  · intro y hy
    refine ⟨Real.sqrt (1 + (ε - ε') / ε') • y, ⟨hpos0 y hy _, ?_⟩,
      (hmain y hy _ ⟨sub_nonneg.2 hε'ε, le_rfl⟩).symm⟩
    rw [ModelField.negPart_smul, norm_smul, mul_pow, hy.2, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by have := div_nonneg (sub_nonneg.2 hε'ε) hε'.le; linarith)]
    field_simp
    ring
  · intro y hy s hs x hx hmem
    rw [hmain y hy s hs] at hmem
    obtain ⟨hzb, hzr⟩ := hball y hy s hs
    by_cases hxq : x = q
    · subst hxq
      obtain ⟨z', hz', hzz'⟩ := hmem
      have hz'b : z' ∈ Metric.ball (0 : Fin n → ℝ) (D.chart x hq).R' :=
        mem_ball_of_morseNorm_lt (lt_of_le_of_lt hz' (D.r₀_lt_R' x hx))
      have heq := (D.chart x hq).χ.injOn ((D.chart x hq).hball hz'b) ((D.chart x hq).hball hzb)
        hzz'
      rw [← heq] at hzr
      have : morseNorm n z' ^ 2 ≤ (D.chart x hq).r₀ ^ 2 :=
        pow_le_pow_left₀ (ModelField.morseNorm_nonneg _) hz' 2
      linarith
    · exact (D.disjoint x hx q hq hxq).notMem_of_mem_left
        (D.closedSmallBall_subset_image_ball x hx hmem) (mem_image_of_mem _ hzb)

theorem meetsRightOnce_of_le (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) {ε ε' c : ℝ} (hε' : 0 < ε')
    (hε'ε : ε' ≤ ε) (hr₀ : (D.chart p hp).r₀ ^ 2 < 2 * ε') (hrm : 8 * ε < D.rm p hp ^ 2)
    (hpc : f p + ε ≤ c) (hcb : c ≤ b)
    (hballs : ∀ x (hx : x ∈ crit), x ≠ p → ∀ y ∈ D.closedSmallBall x hx,
      f y ∉ Icc (f p + ε') (f p + ε))
    {γ : ℝ → M} (hγ : Continuous γ) (hlev : ∀ t, f (γ t) = c)
    (hfree : ∀ t, descendsFreely D (c - (f p + ε)) (γ t))
    (h : meetsRightOnce D p hp ε c γ) :
    (∀ t, descendsFreely D (c - (f p + ε')) (γ t)) ∧ meetsRightOnce D p hp ε' c γ := by
  have hε : 0 < ε := lt_of_lt_of_le hε' hε'ε
  have hδ0 : 0 ≤ ε - ε' := sub_nonneg.2 hε'ε
  have hTnn : 0 ≤ c - (f p + ε) := by linarith
  have hfpI : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hrmpos := D.rm_pos p hp
  have hrmR : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hflowT' : ∀ x, D.flow (c - (f p + ε')) x =
      D.flow (ε - ε') (D.flow (c - (f p + ε)) x) := by
    intro x
    rw [show c - (f p + ε') = (c - (f p + ε)) + (ε - ε') by ring, D.flow_add]
  have hpball : ∀ y ∈ D.closedSmallBall p hp, f y < f p + ε' := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : morseNorm n y ≤ (D.chart p hp).r₀ := hy
    have hyR : morseNorm n y ≤ (D.chart p hp).R := hy'.trans (D.r₀_lt_R p hp).le
    rw [(D.chart p hp).hnorm y hyR,
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart p hp).hk y
    have h2 : morseNorm n y ^ 2 ≤ (D.chart p hp).r₀ ^ 2 :=
      pow_le_pow_left₀ (ModelField.morseNorm_nonneg _) hy' 2
    nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk y‖]
  have hlevT : ∀ t, f (D.flow (c - (f p + ε)) (γ t)) = f p + ε := by
    intro t
    have hx : f (γ t) ∈ Icc a b := by rw [hlev]; exact ⟨by linarith [hfpI.1], hcb⟩
    have hxT : f (γ t) - (c - (f p + ε)) ∈ Icc a b := by
      rw [hlev]; exact ⟨by linarith [hfpI.1], by linarith⟩
    have hav : ∀ s ∈ uIcc 0 (c - (f p + ε)), ∀ x hx, D.flow s (γ t) ∉ D.smallBall x hx := by
      intro s hs x hx hmem
      rw [uIcc_of_le hTnn] at hs
      exact hfree t s hs x hx (D.smallBall_subset_closedSmallBall x hx hmem)
    have := D.f_flow_eq_sub_of_avoid_uIcc hf hx hxT hav _ right_mem_uIcc
    rw [this, hlev]; ring
  have hband : ∀ t, ∀ u ∈ Icc 0 (ε - ε'),
      f p + ε' ≤ f (D.flow u (D.flow (c - (f p + ε)) (γ t))) ∧
        f (D.flow u (D.flow (c - (f p + ε)) (γ t))) ≤ f p + ε := by
    intro t u hu
    have h1 := D.sub_le_f_flow hf (D.flow (c - (f p + ε)) (γ t)) hu.1
    have h2 := D.f_flow_le hf (D.flow (c - (f p + ε)) (γ t)) hu.1
    rw [hlevT t] at h1 h2
    constructor <;> linarith [hu.2]
  have hfree' : ∀ t, descendsFreely D (c - (f p + ε')) (γ t) := by
    intro t s hs x hx hmem
    rcases le_or_gt s (c - (f p + ε)) with hsT | hsT
    · exact hfree t s ⟨hs.1, hsT⟩ x hx hmem
    · have hs' : s = (c - (f p + ε)) + (s - (c - (f p + ε))) := by ring
      rw [hs', D.flow_add] at hmem
      obtain ⟨hl1, hl2⟩ := hband t (s - (c - (f p + ε))) ⟨by linarith, by linarith [hs.2]⟩
      by_cases hxp : x = p
      · subst hxp
        linarith [hpball _ hmem]
      · exact hballs x hx hxp _ hmem ⟨hl1, hl2⟩
  refine ⟨hfree', ?_⟩
  have hlevJ : ∀ y : Fin n → ℝ, morseNorm n y ≤ (D.chart p hp).R → ∀ L, f p < L →
      f ((D.chart p hp).χ y) = L → ModelField.scaledNegativePart (D.chart p hp).hk y = 0 →
      posPart (D.chart p hp).hk y ≠ 0 ∧ negPart (D.chart p hp).hk y = 0 ∧
        morseNorm n y ^ 2 = 2 * (L - f p) := by
    intro y hyR L hL hfy hJ
    rw [(D.chart p hp).hnorm y hyR,
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hfy
    have hv : posPart (D.chart p hp).hk y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hfy
      nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk y‖]
    have hu := (ModelField.scaledNegativePart_eq_zero_iff (D.chart p hp).hk hv).1 hJ
    refine ⟨hv, hu, ?_⟩
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart p hp).hk, hu]
    rw [hu, norm_zero] at hfy
    rw [norm_zero]
    linarith
  obtain ⟨t₀, hdom₀, hzero₀, huniq, v, hv, hv0⟩ := h
  obtain ⟨y₀, hy₀R, hy₀eq⟩ := hdom₀
  have hy₀R' : morseNorm n y₀ ≤ (D.chart p hp).R := le_of_lt hy₀R
  have hJ₀ : ModelField.scaledNegativePart (D.chart p hp).hk y₀ = 0 := by
    have h0 : ModelField.scaledNegativePart (D.chart p hp).hk
        ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) (γ t₀))) = 0 := hzero₀
    rw [← hy₀eq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₀ hy₀R')] at h0
    exact h0
  have hfy₀ : f ((D.chart p hp).χ y₀) = f p + ε := by rw [hy₀eq]; exact hlevT t₀
  obtain ⟨_, hu₀, hn₀⟩ := hlevJ y₀ hy₀R' (f p + ε) (by linarith) hfy₀ hJ₀
  have hy₀rm : morseNorm n y₀ < D.rm p hp := by
    apply lt_of_pow_lt_pow_left₀ 2 hrmpos.le
    rw [hn₀]; linarith
  have hO₀ : ∀ s ∈ Icc 0 (ε - ε'), D.flow s (D.flow (c - (f p + ε)) (γ t₀)) ∈
      (D.chart p hp).χ '' {z | morseNorm n z ≤ morseNorm n y₀ ∧
        negPart (D.chart p hp).hk z = 0} := by
    intro s hs
    rw [← hy₀eq]
    exact D.flow_mem_of_negPart_eq_zero hp hy₀rm hu₀ hs.1
  obtain ⟨y₁, ⟨hy₁a, hy₁b⟩, hy₁eq⟩ := hO₀ (ε - ε') ⟨hδ0, le_rfl⟩
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := lt_of_le_of_lt hy₁a (hy₀rm.trans_le hrmR)
  refine ⟨t₀, ?_, ?_, ?_, ?_⟩
  · change D.flow (c - (f p + ε')) (γ t₀) ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hflowT', ← hy₁eq]
    exact ⟨y₁, hy₁R, rfl⟩
  · change ModelField.scaledNegativePart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow (c - (f p + ε')) (γ t₀))) = 0
    rw [hflowT', ← hy₁eq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R.le)]
    simp [ModelField.scaledNegativePart, hy₁b]
  · intro t hdom hzero
    have hdom' : D.flow (ε - ε') (D.flow (c - (f p + ε)) (γ t)) ∈
        (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R} := by
      rw [← hflowT']; exact hdom
    have hzero' : ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm
        (D.flow (ε - ε') (D.flow (c - (f p + ε)) (γ t)))) = 0 := by
      rw [← hflowT']; exact hzero
    set w := D.flow (ε - ε') (D.flow (c - (f p + ε)) (γ t)) with hw
    obtain ⟨y₂, hy₂R, hy₂eq⟩ := hdom'
    have hy₂R' : morseNorm n y₂ ≤ (D.chart p hp).R := le_of_lt hy₂R
    rw [← hy₂eq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₂ hy₂R')] at hzero'
    obtain ⟨hbl1, hbl2⟩ := hband t (ε - ε') ⟨hδ0, le_rfl⟩
    rw [← hw] at hbl1 hbl2
    obtain ⟨hv₂, hu₂, _⟩ := hlevJ y₂ hy₂R' (f w) (by linarith) (by rw [hy₂eq]) hzero'
    have hball2 : 2 * ε + 2 * ‖negPart (D.chart p hp).hk y₂‖ ^ 2 < D.rm p hp ^ 2 := by
      rw [hu₂, norm_zero]; nlinarith
    have hlevel2 : morseNormalForm (D.chart p hp).hk (f p) y₂ ≤ f p + ε := by
      rw [← (D.chart p hp).hnorm y₂ hy₂R', hy₂eq]; exact hbl2
    obtain ⟨τ, _, hτlev, htraj, hprod⟩ := D.exists_exit_asc hf hp hε hball2 hv₂ hlevel2
    rw [hy₂eq] at hτlev htraj hprod
    have hcU : ∀ y, f y = f p + ε → dfV I f D.V y = -1 := by
      intro y hy
      refine D.dfV_eq_neg_one_of_level ⟨by linarith [hfpI.1], by linarith⟩ ?_ hy
      intro x hx z hz hfz
      by_cases hxp : x = p
      · subst hxp
        have := hpball z (D.smallBall_subset_closedSmallBall x hx hz)
        linarith
      · exact hballs x hx hxp z (D.smallBall_subset_closedSmallBall x hx hz)
          ⟨by linarith, by linarith⟩
    have hback : D.flow (-(ε - ε')) w = D.flow (c - (f p + ε)) (γ t) := by
      rw [hw, D.flow_neg_flow]
    have hτδ : -τ = -(ε - ε') :=
      GradientLikeStrip.flow_level_unique (D := D) hf hcU hτlev (by rw [hback]; exact hlevT t)
    rw [hτδ] at htraj
    rw [hτδ, hback] at hprod
    have htraj' := htraj (-(ε - ε')) ⟨le_rfl, by linarith⟩
    rw [hback] at htraj'
    obtain ⟨y₃, hy₃, hy₃eq⟩ := htraj'
    have hy₃' : morseNorm n y₃ ^ 2 ≤ 2 * ε := by
      have : morseNorm n y₃ ^ 2 ≤ 2 * ε + 2 * ‖negPart (D.chart p hp).hk y₂‖ ^ 2 := hy₃
      rw [hu₂, norm_zero] at this; linarith
    have hy₃R : morseNorm n y₃ < (D.chart p hp).R := by
      apply lt_of_pow_lt_pow_left₀ 2 (D.chart p hp).R_pos.le
      have : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := pow_le_pow_left₀ hrmpos.le hrmR 2
      linarith
    rw [← hy₃eq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₃ hy₃R.le), hu₂,
      norm_zero] at hprod
    have hu₃ : negPart (D.chart p hp).hk y₃ = 0 := by
      have h0 : (0 : ℝ) ^ 2 * ‖posPart (D.chart p hp).hk y₂‖ ^ 2 = 0 := by ring
      have h4 := hprod.trans h0.le
      have h1 : ‖negPart (D.chart p hp).hk y₃‖ ^ 2 ≤ 0 := by
        by_contra hc
        push Not at hc
        have := mul_pos (show (0 : ℝ) < 2 * ε by linarith) hc
        linarith
      have h3 : ‖negPart (D.chart p hp).hk y₃‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    apply huniq t
    · change D.flow (c - (f p + ε)) (γ t) ∈
        (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
      exact ⟨y₃, hy₃R, hy₃eq⟩
    · change ModelField.scaledNegativePart (D.chart p hp).hk
        ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) (γ t))) = 0
      rw [← hy₃eq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₃ hy₃R.le)]
      simp [ModelField.scaledNegativePart, hu₃]
  · refine ⟨v, hv.congr_of_eventuallyEq ?_, hv0⟩
    set O := (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} with hO
    have hOopen : IsOpen O := D.isOpen_modelBall p hp
    have hcontF : Continuous (fun q : ℝ × ℝ => D.flow q.2 (D.flow (c - (f p + ε)) (γ q.1))) :=
      D.continuous_flow_joint.comp
        (continuous_snd.prodMk ((D.continuous_flow _).comp (hγ.comp continuous_fst)))
    have htube : ∀ᶠ t in 𝓝 t₀, ∀ s ∈ Icc 0 (ε - ε'),
        D.flow s (D.flow (c - (f p + ε)) (γ t)) ∈ O := by
      refine isCompact_Icc.eventually_forall_of_forall_eventually fun s hs => ?_
      have hmem : D.flow s (D.flow (c - (f p + ε)) (γ t₀)) ∈ O := by
        obtain ⟨z, hz, hzeq⟩ := hO₀ s hs
        exact ⟨z, lt_of_le_of_lt hz.1 hy₀rm, hzeq⟩
      exact hcontF.continuousAt.eventually_mem (hOopen.mem_nhds hmem)
    filter_upwards [htube] with t ht
    change ModelField.scaledNegativePart (D.chart p hp).hk
        ((D.chart p hp).χ.symm (D.flow (c - (f p + ε')) (γ t))) =
      ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) (γ t)))
    rw [hflowT']
    set z := D.flow (c - (f p + ε)) (γ t) with hz
    have hd : ∀ s ∈ Icc 0 (ε - ε'),
        HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s z)))
          0 s := by
      intro s hs
      have hY := GradientLikeStrip.hasDerivAt_symm_flow (D := D) hp (ht s hs)
      have hsymm : morseNorm n ((D.chart p hp).χ.symm (D.flow s z)) < D.rm p hp :=
        (D.chart p hp).symm_mem ((D.chart p hp).lt_subset_ball (D.rm_lt_R' p hp).le) (ht s hs)
      have hnf := (D.chart p hp).f_eq_nf_symm (D.modelBall_subset_image_le p hp (ht s hs))
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hnf
      have hlo := (hband t s hs).1
      rw [← hz] at hlo
      have hvs : posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s z)) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hnf
        nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s z))‖]
      have hJd : HasFDerivAt (ModelField.scaledNegativePart (D.chart p hp).hk)
          (fderiv ℝ (ModelField.scaledNegativePart (D.chart p hp).hk) ((D.chart p hp).χ.symm (D.flow s z)))
          ((D.chart p hp).χ.symm (D.flow s z)) :=
        ((ModelField.contDiffAt_scaledNegativePart (D.chart p hp).hk hvs).differentiableAt (by simp)).hasFDerivAt
      have := hJd.comp_hasDerivAt s hY
      rw [ModelField.fderiv_scaledNegativePart_modelField (D.chart p hp).hk _ hvs] at this
      exact this
    have hconst := constant_of_has_deriv_right_zero
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (ε - ε') ⟨hδ0, le_rfl⟩
    simp only [D.flow_zero] at hconst
    exact hconst

theorem meetsRightOnce_transfer {f₁ : M → ℝ} {a₁ b₁ : ℝ} {crit₁ : Finset M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) (D₁ : GradientLikeStrip I f₁ a₁ b₁ crit₁) {p : M}
    (hp : p ∈ crit) (hp₁ : p ∈ crit₁) (hχ : (D₁.chart p hp₁).χ = (D.chart p hp).χ)
    (hk : (D₁.chart p hp₁).k = (D.chart p hp).k)
    (hR : (D₁.chart p hp₁).R ≤ (D.chart p hp).R) (hfp : f₁ p = f p) {ε c : ℝ} (hε : 0 < ε)
    (hRε : 2 * ε < (D₁.chart p hp₁).R ^ 2) (hpc : f p + ε ≤ c) (hcb : c ≤ b)
    {γ : ℝ → M} (hlev : ∀ t, f (γ t) = c) (hfree : ∀ t, descendsFreely D (c - (f p + ε)) (γ t))
    (hflow : ∀ t, D₁.flow (c - (f p + ε)) (γ t) = D.flow (c - (f p + ε)) (γ t))
    (h : meetsRightOnce D p hp ε c γ) : meetsRightOnce D₁ p hp₁ ε c γ := by
  classical
  set T : ℝ := c - (f p + ε) with hTdef
  have hT1 : c - (f₁ p + ε) = T := by rw [hfp]
  have hJiso : ∀ (k₁ k : ℕ) (_ : k₁ = k) (h₁ : k₁ ≤ n) (h : k ≤ n),
      ∃ e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k₁),
        ∀ y, ModelField.scaledNegativePart h₁ y = e (ModelField.scaledNegativePart h y) := by
    intro k₁ k hkk h₁ h
    subst hkk
    exact ⟨ContinuousLinearEquiv.refl ℝ _, fun y => rfl⟩
  obtain ⟨e, he⟩ := hJiso _ _ hk (D₁.chart p hp₁).hk (D.chart p hp).hk
  have hfun : ∀ t, rightFun D₁ p hp₁ ε c (γ t) = e (rightFun D p hp ε c (γ t)) := by
    intro t
    simp only [rightFun]
    rw [hT1, hflow, hχ, he]
  have hdom : ∀ t, γ t ∈ rightDom D₁ p hp₁ ε c → γ t ∈ rightDom D p hp ε c := by
    intro t ht
    simp only [rightDom, Set.mem_ofPred_eq] at ht ⊢
    rw [hT1, hflow, hχ] at ht
    obtain ⟨y, hy, hyeq⟩ := ht
    exact ⟨y, lt_of_lt_of_le hy hR, hyeq⟩
  obtain ⟨t₀, hdom₀, hzero₀, huniq, v, hv, hv0⟩ := h
  refine ⟨t₀, ?_, ?_, ?_, ?_⟩
  · have hfpI : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
    have hlevel : f (D.flow T (γ t₀)) = f p + ε := by
      have hx : f (γ t₀) ∈ Icc a b := by
        rw [hlev]; exact ⟨by linarith [hfpI.1], hcb⟩
      have hxT : f (γ t₀) - T ∈ Icc a b := by
        rw [hlev, hTdef]; exact ⟨by linarith [hfpI.1], by linarith⟩
      have hTnn : 0 ≤ T := by rw [hTdef]; linarith
      have hav : ∀ s ∈ uIcc 0 T, ∀ x hx, D.flow s (γ t₀) ∉ D.smallBall x hx := by
        intro s hs x hx hmem
        rw [uIcc_of_le hTnn] at hs
        exact hfree t₀ s hs x hx (D.smallBall_subset_closedSmallBall x hx hmem)
      have := D.f_flow_eq_sub_of_avoid_uIcc hf hx hxT hav T right_mem_uIcc
      rw [this, hlev, hTdef]; ring
    simp only [rightDom, Set.mem_ofPred_eq] at hdom₀ ⊢
    rw [hT1, hflow, hχ]
    obtain ⟨y, hy, hyeq⟩ := hdom₀
    refine ⟨y, ?_, hyeq⟩
    have hyR : morseNorm n y ≤ (D.chart p hp).R := le_of_lt hy
    have hfy := (D.chart p hp).hnorm y hyR
    rw [hyeq, hlevel, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hfy
    have hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk y = 0 := by
      have h0 := hzero₀
      simp only [rightFun] at h0
      rw [← hyeq, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y hyR)] at h0
      exact h0
    have hpos : posPart (D.chart p hp).hk y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hfy
      nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk y‖]
    have hneg : negPart (D.chart p hp).hk y = 0 :=
      (ModelField.scaledNegativePart_eq_zero_iff (D.chart p hp).hk hpos).1 hJ0
    rw [hneg, norm_zero] at hfy
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk y
    rw [hneg, norm_zero] at hsq
    have hR1pos : 0 ≤ (D₁.chart p hp₁).R := (D₁.chart p hp₁).R_pos.le
    refine lt_of_pow_lt_pow_left₀ 2 hR1pos ?_
    rw [hsq]
    nlinarith
  · rw [hfun, hzero₀, map_zero]
  · intro t ht hzt
    refine huniq t (hdom t ht) ?_
    rw [hfun] at hzt
    exact (map_eq_zero_iff e e.injective).1 hzt
  · refine ⟨e v, ?_, ?_⟩
    · have hcomp := (e.hasFDerivAt (x := rightFun D p hp ε c (γ t₀))).comp_hasDerivAt t₀ hv
      have heq : (fun t => rightFun D₁ p hp₁ ε c (γ t)) =
          (⇑e ∘ fun t => rightFun D p hp ε c (γ t)) := by
        funext t; exact hfun t
      rw [heq]
      simpa using hcomp
    · intro h0
      exact hv0 ((map_eq_zero_iff e e.injective).1 h0)

theorem leftLoop_congr {f₁ : M → ℝ} {a₁ b₁ : ℝ} {crit₁ : Finset M}
    (D : GradientLikeStrip I f a b crit) (D₁ : GradientLikeStrip I f₁ a₁ b₁ crit₁) {q : M}
    (hq : q ∈ crit) (hq₁ : q ∈ crit₁) (hk : (D.chart q hq).k = 2)
    (hk₁ : (D₁.chart q hq₁).k = 2) (hχ : (D₁.chart q hq₁).χ = (D.chart q hq).χ)
    (hfq : f₁ q = f q) {ε c : ℝ}
    (hflow : ∀ t, D₁.flow (f q - ε - c) (leftPt D q hq hk ε t) =
      D.flow (f q - ε - c) (leftPt D q hq hk ε t)) :
    leftPt D₁ q hq₁ hk₁ ε = leftPt D q hq hk ε ∧
      leftLoop D₁ q hq₁ hk₁ ε c = leftLoop D q hq hk ε c := by
  have key : ∀ (e : MorseNormalChart I f q) (e' : MorseNormalChart I f₁ q) (he : e.k = 2)
      (he' : e'.k = 2), e'.χ = e.χ → ∀ t : ℝ,
      e'.χ (e'.sphereParam ε (fun i => circ2 t (Fin.cast he' i))) =
        e.χ (e.sphereParam ε (fun i => circ2 t (Fin.cast he i))) := by
    intro e e' he he' hee t
    cases e
    cases e'
    simp only at he he' hee ⊢
    subst he
    subst he'
    subst hee
    rfl
  have hpt : leftPt D₁ q hq₁ hk₁ ε = leftPt D q hq hk ε := by
    funext t
    exact key (D.chart q hq) (D₁.chart q hq₁) hk hk₁ hχ t
  refine ⟨hpt, ?_⟩
  funext t
  simp only [leftLoop]
  rw [hfq, hpt]
  exact hflow t

theorem sard_of_meetsRightOnce (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit)
    (hkp : (D.chart p hp).k = 1) (hkq : (D.chart q hq).k = 2) {ε c : ℝ} (hε : 0 < ε)
    (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) (hc : f p + ε ≤ c) (hcq : c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    (h : meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)) :
    ∃ w₀ ∈ D.sardDom p hq ε c ε hp, D.sardMap p hq ε c ε hp w₀ = 0 ∧
      (∀ w ∈ D.sardDom p hq ε c ε hp, D.sardMap p hq ε c ε hp w = 0 →
        ∃ t : ℝ, 0 < t ∧ w = t • w₀) ∧
      Function.Surjective (fderiv ℝ (D.sardMap p hq ε c ε hp) w₀) := by
  classical
  obtain ⟨t₀, hdom₀, hzero₀, huniq, v, hv, hv0⟩ := h
  let g : ℝ → (Fin (D.chart q hq).k → ℝ) := fun t i => circ2 t (Fin.cast hkq i)
  have hcast : ∀ i : Fin (D.chart q hq).k, i = Fin.cast hkq.symm (Fin.cast hkq i) :=
    fun i => Fin.ext rfl
  have hg_ne : ∀ t, g t ≠ 0 := by
    intro t hzero
    have h0 := congrFun hzero (Fin.cast hkq.symm 0)
    have h1 := congrFun hzero (Fin.cast hkq.symm 1)
    simp only [g, circ2, Fin.cast_cast, Fin.cast_eq_self, Pi.zero_apply] at h0 h1
    simp only [Matrix.cons_val_zero] at h0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    have := Real.cos_sq_add_sin_sq (2 * Real.pi * t)
    rw [h0, h1] at this
    norm_num at this
  have hdomiff : ∀ t, g t ∈ D.sardDom p hq ε c ε hp ↔
      leftLoop D q hq hkq ε c t ∈ rightDom D p hp ε c :=
    fun t => ⟨fun h => h.2, fun h => ⟨hg_ne t, h⟩⟩
  have hpolar : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, w = r • g t := by
    intro w hw
    let z : ℂ := ⟨w (Fin.cast hkq.symm 0), w (Fin.cast hkq.symm 1)⟩
    have hz : z ≠ 0 := by
      intro hz0
      apply hw
      have h0 : w (Fin.cast hkq.symm 0) = 0 := congrArg Complex.re hz0
      have h1 : w (Fin.cast hkq.symm 1) = 0 := congrArg Complex.im hz0
      have key : ∀ j : Fin 2, w (Fin.cast hkq.symm j) = 0 := by
        rw [Fin.forall_fin_two]; exact ⟨h0, h1⟩
      funext i
      rw [hcast i]
      exact key _
    refine ⟨‖z‖, norm_pos_iff.2 hz, Complex.arg z / (2 * Real.pi), ?_⟩
    have hpi : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
      field_simp
    have key : ∀ j : Fin 2, w (Fin.cast hkq.symm j) =
        ‖z‖ * circ2 (Complex.arg z / (2 * Real.pi)) j := by
      rw [Fin.forall_fin_two]
      simp only [circ2, hpi, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_mul_cos_arg,
        Complex.norm_mul_sin_arg]
      exact ⟨rfl, rfl⟩
    funext i
    rw [hcast i, key]
    rfl
  have hgt : ∀ t (m : ℤ), g (t + m) = g t := by
    intro t m
    funext i
    have h2 : 2 * Real.pi * (t + m) = 2 * Real.pi * t + m * (2 * Real.pi) := by ring
    simp only [g, circ2, h2, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  have hdom₀' : g t₀ ∈ D.sardDom p hq ε c ε hp := (hdomiff t₀).2 hdom₀
  refine ⟨g t₀, hdom₀', hzero₀, ?_, ?_⟩
  · intro w hw hw0
    obtain ⟨r, hr, t, rfl⟩ := hpolar w hw.1
    have hsp : (D.chart q hq).sphereParam ε (r • g t) = (D.chart q hq).sphereParam ε (g t) :=
      (D.chart q hq).sphereParam_smul ε hr (hg_ne t)
    have hland : D.landing p hq ε c ε (r • g t) = D.landing p hq ε c ε (g t) := by
      unfold GradientLikeStrip.landing
      rw [hsp]
    have hmap : D.sardMap p hq ε c ε hp (r • g t) = D.sardMap p hq ε c ε hp (g t) := by
      unfold GradientLikeStrip.sardMap
      rw [hland]
    have hdom : g t ∈ D.sardDom p hq ε c ε hp := by
      refine ⟨hg_ne t, ?_⟩
      have h2 := hw.2
      simp only [Set.mem_preimage] at h2 ⊢
      rwa [hland] at h2
    obtain ⟨m, hm⟩ := huniq t ((hdomiff t).1 hdom) (by
      change D.sardMap p hq ε c ε hp (g t) = 0
      rw [← hmap]; exact hw0)
    refine ⟨r, hr, ?_⟩
    rw [hm, hgt]
  · have hdiff : DifferentiableAt ℝ (D.sardMap p hq ε c ε hp) (g t₀) :=
      (GradientLikeStrip.differentiableOn_sardMap hf hε hε hεR hc hcq hlev).differentiableAt
        ((GradientLikeStrip.isOpen_sardDom hε.le hεR).mem_nhds hdom₀')
    have hgdiff : DifferentiableAt ℝ g t₀ := by
      refine differentiableAt_pi.2 fun i => ?_
      change DifferentiableAt ℝ (fun t => circ2 t (Fin.cast hkq i)) t₀
      generalize Fin.cast hkq i = j
      fin_cases j
      · change DifferentiableAt ℝ (fun t => Real.cos (2 * Real.pi * t)) t₀
        fun_prop
      · change DifferentiableAt ℝ (fun t => Real.sin (2 * Real.pi * t)) t₀
        fun_prop
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t₀ hgdiff.hasDerivAt
    have hv' : HasDerivAt (D.sardMap p hq ε c ε hp ∘ g) v t₀ := hv
    have heq := hv'.unique hcomp
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (D.chart p hp).k)) = 1 := by
      rw [finrank_euclideanSpace_fin, hkp]
    intro y
    obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).1 hfin y
    exact ⟨s • deriv g t₀, by rw [map_smul, ← heq, hs]⟩

theorem isCancellingPair_of_fine [DecidableEq M] (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hkp : (D.chart p hp).k = 1)
    (hkq : (D.chart q hq).k = 2) {a' b' : ℝ} (ha' : a < a') (hb' : b' < b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hpq : f p < f q) (honly : ∀ x, f x ∈ Ioo a' b' → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x = p ∨ x = q)
    (himp : (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' ⊆ f ⁻¹' Ioo a' b')
    (himq : (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' ⊆ f ⁻¹' Ioo a' b')
    (hother : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D.smallBall x hx, f y ∉ Icc a' b')
    {ε c : ℝ} (hε : 0 < ε)
    (hcst : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2 ∧
      (D.chart q hq).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm q hq ^ 2)
    (hc : f p + ε < c) (hcq : c < f q - ε)
    (h : meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)) :
    isCancellingPair I f a' b' p q := by
  have hff : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  obtain ⟨hr₀p, hrmp, hr₀q, hrmq⟩ := hcst
  have hpI : f p ∈ Ioo a' b' := by
    have h0 := himp ⟨0, Metric.mem_ball_self (D.chart p hp).R'_pos, (D.chart p hp).hχ0⟩
    exact h0
  have hqI : f q ∈ Ioo a' b' := by
    have h0 := himq ⟨0, Metric.mem_ball_self (D.chart q hq).R'_pos, (D.chart q hq).hχ0⟩
    exact h0
  have hab' : a' < b' := hpI.1.trans hpI.2
  have hRp : 2 * ε < (D.chart p hp).R ^ 2 := by
    have h1 := (D.hrm p hp).2
    have h2 := D.rm_pos p hp
    nlinarith
  have hRq : 2 * ε < (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    nlinarith
  have hpball : ∀ y ∈ D.closedSmallBall p hp, f y < f p + ε := by
    intro y hy
    have h1 := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hy
    have h2 := (abs_le.1 h1).2
    linarith
  have hqball : ∀ y ∈ D.closedSmallBall q hq, f q - ε < f y := by
    intro y hy
    have h1 := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hy
    have h2 := (abs_le.1 h1).1
    linarith
  have hotherC : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D.closedSmallBall x hx,
      f y ∉ Ioo a' b' := by
    intro x hx hxp hxq y hy hyI
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : morseNorm n z ≤ (D.chart x hx).r₀ := hz
    have hzball : z ∈ Metric.ball (0 : Fin n → ℝ) (D.chart x hx).R' :=
      mem_ball_of_morseNorm_lt (hz'.trans_lt (D.r₀_lt_R' x hx))
    have hcont : ContinuousAt (fun t : ℝ => f ((D.chart x hx).χ (t • z))) 1 := by
      have h1 : ContinuousAt (D.chart x hx).χ ((1 : ℝ) • z) := by
        rw [one_smul]
        exact (D.chart x hx).χ.continuousAt ((D.chart x hx).hball hzball)
      have h2 : ContinuousAt (fun t : ℝ => t • z) 1 :=
        (continuous_id.smul continuous_const).continuousAt
      exact hff.continuous.continuousAt.comp (ContinuousAt.comp (f := fun t : ℝ => t • z) h1 h2)
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), f ((D.chart x hx).χ (t • z)) ∈ Ioo a' b' := by
      have h1 := hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hyI))
      exact nhdsWithin_le_nhds h1
    have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
    obtain ⟨t, ht, ht01⟩ := (hev.and hev2).exists
    refine hother x hx hxp hxq _ ⟨t • z, ?_, rfl⟩ (Ioo_subset_Icc_self ht)
    change morseNorm n (t • z) < (D.chart x hx).r₀
    have hsm : morseNorm n (t • z) = t * morseNorm n z := by
      simp [morseNorm, WithLp.toLp_smul, norm_smul, abs_of_pos ht01.1]
    rw [hsm]
    have := (D.chart x hx).hr₀
    have := ModelField.morseNorm_nonneg z
    nlinarith [ht01.1, ht01.2]
  have hlevC : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ x (hx : x ∈ crit),
      y ∉ D.closedSmallBall x hx := by
    intro y hy x hx hyx
    by_cases hxp : x = p
    · subst hxp
      have := hpball y hyx
      linarith [hy.1]
    by_cases hxq : x = q
    · subst hxq
      have := hqball y hyx
      linarith [hy.2]
    refine hotherC x hx hxp hxq y hyx ⟨?_, ?_⟩
    · linarith [hy.1, hpI.1]
    · linarith [hy.2, hqI.2]
  have hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ x (hx : x ∈ crit),
      y ∉ D.smallBall x hx := fun y hy x hx hmem =>
    hlevC y hy x hx (D.smallBall_subset_closedSmallBall x hx hmem)
  have hw : ∀ t : ℝ, (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
    intro t h0
    have h1 : Real.cos (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 0)
    have h2 : Real.sin (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 1)
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h1, h2] at this
    norm_num at this
  have hleftPt : ∀ t, f (leftPt D q hq hkq ε t) = f q - ε := by
    intro t
    exact (D.chart q hq).f_chart_of_mem_leftModelSphere hRq.le
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le (hw t))
  have hγlev : ∀ t, f (leftLoop D q hq hkq ε c t) = c := by
    intro t
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hff
      (x := leftPt D q hq hkq ε t) (T := f q - ε - c)
      (by rw [hleftPt]; constructor <;> linarith [hqI.2, hpI.1])
      (by rw [hleftPt]; constructor <;> linarith [hqI.2, hpI.1])
      (by
        intro y hy
        apply hlev
        rw [hleftPt, show f q - ε - (f q - ε - c) = c by ring, uIcc_of_ge hcq.le] at hy
        exact ⟨by linarith [hy.1], hy.2⟩)
      (f q - ε - c) right_mem_uIcc
    change f (D.flow (f q - ε - c) (leftPt D q hq hkq ε t)) = c
    rw [h, hleftPt]
    ring
  have hfree : ∀ t, descendsFreely D (c - (f p + ε)) (leftLoop D q hq hkq ε c t) := by
    intro t s hs x hx
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hff
      (x := leftLoop D q hq hkq ε c t) (T := c - (f p + ε))
      (by rw [hγlev]; constructor <;> linarith [hqI.2, hpI.1])
      (by rw [hγlev]; constructor <;> linarith [hqI.2, hpI.1])
      (by
        intro y hy
        apply hlev
        rw [hγlev, show c - (c - (f p + ε)) = f p + ε by ring, uIcc_of_ge (by linarith)] at hy
        exact ⟨hy.1, by linarith [hy.2]⟩)
      s (by rw [uIcc_of_le (by linarith)]; exact hs)
    apply hlevC
    rw [h, hγlev]
    constructor <;> linarith [hs.1, hs.2]
  have hsub : ∀ r ∈ ({p, q} : Finset M), r ∈ crit := by
    intro r hr
    rcases mem_pair_iff.1 hr with h | h
    · rw [h]; exact hp
    · rw [h]; exact hq
  have hother' : ∀ r hr, r ∉ ({p, q} : Finset M) → ∀ y ∈ D.smallBall r hr, f y ∉ Icc a' b' := by
    intro r hr hn
    have hrp : r ≠ p := fun h => hn (mem_pair_iff.2 (Or.inl h))
    have hrq : r ≠ q := fun h => hn (mem_pair_iff.2 (Or.inr h))
    exact hother r hr hrp hrq
  have hinStrip : ∀ r (hr : r ∈ ({p, q} : Finset M)),
      (D.chart r (hsub r hr)).χ '' Metric.ball 0 (D.chart r (hsub r hr)).R' ⊆ f ⁻¹' Ioo a' b' := by
    intro r hr
    rcases mem_pair_iff.1 hr with h | h
    · subst h; exact himp
    · subst h; exact himq
  have hnotcrit : ∀ x, f x ∈ Icc a' b' → x ∉ ({p, q} : Finset M) → x ∉ crit := by
    intro x hx hn hc
    have hxc := ((hcrit x).1 hc).2
    have hxI : f x ∈ Ioo a' b' := by
      refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
      · intro h; exact hreg x (Or.inl h.symm) hxc
      · intro h; exact hreg x (Or.inr h) hxc
    exact hn (mem_pair_iff.2 (honly x hxI hxc))
  obtain ⟨D', hch, hrm', hV⟩ := GradientLikeStrip.exists_restrict D ha'.le hb'.le
    ({p, q} : Finset M) hsub hother'
    (fun r hr => (D.chart r (hsub r hr)).R) (fun r hr => (D.chart r (hsub r hr)).R')
    (fun r hr => D.rm r (hsub r hr))
    (fun r hr => ⟨(D.chart r (hsub r hr)).hr₀R, le_rfl⟩)
    (fun r hr => ⟨(D.chart r (hsub r hr)).hRR', le_rfl⟩)
    (fun r hr => ⟨(D.hrm r (hsub r hr)).1, le_rfl, (D.hrm r (hsub r hr)).2⟩)
    hinStrip hnotcrit
  have hp' : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hq' : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  obtain ⟨hχp, hkp', hr₀p', hRp', -⟩ := hch p hp'
  obtain ⟨hχq, hkq', hr₀q', hRq', -⟩ := hch q hq'
  have hrmp' : D'.rm p hp' = D.rm p hp := hrm' p hp'
  have hrmq' : D'.rm q hq' = D.rm q hq := hrm' q hq'
  have hkp₁ : (D'.chart p hp').k = 1 := hkp'.trans hkp
  have hkq₁ : (D'.chart q hq').k = 2 := hkq'.trans hkq
  have hflow : ∀ t x, D'.flow t x = D.flow t x :=
    GradientLikeStrip.flow_eq_of_V_eq D D' hV
  have hS5 := leftLoop_congr D D' hq hq' hkq hkq₁ hχq rfl (ε := ε) (c := c)
    (fun t => hflow _ _)
  have hS4 : meetsRightOnce D' p hp' ε c (leftLoop D q hq hkq ε c) :=
    meetsRightOnce_transfer hff D D' hp hp' hχp hkp' hRp'.le rfl hε
      (by rw [hRp']; exact hRp) (by linarith) (by linarith [hqI.2])
      hγlev hfree (fun t => hflow _ _) h
  rw [← hS5.2] at hS4
  have hlev' : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp'', y ∉ D'.smallBall p' hp'' := by
    intro y hy x hx
    have hx' := hch x hx
    unfold GradientLikeStrip.smallBall
    rw [hx'.1, hx'.2.2.1]
    exact hlev y hy x (hsub x hx)
  have hS6 := sard_of_meetsRightOnce hff D' hp' hq' hkp₁ hkq₁ hε
    (by rw [hRq']; exact hRq.le) hc.le hcq.le hlev' hS4
  have hidx : morseIndex I f q = morseIndex I f p + 1 := by
    rw [(D.chart q hq).hkidx, (D.chart p hp).hkidx, hkp, hkq]
  refine ⟨hf.substrip ha'.le hab' hb'.le hreg, ?_, hpq, hidx, D', ε, c, hε, ?_, ?_, ?_, ?_,
    hc, hcq, hlev', hS6⟩
  · intro x
    constructor
    · intro hx
      rcases mem_pair_iff.1 hx with h | h
      · subst h; exact ⟨hpI, ((hcrit x).1 hp).2⟩
      · subst h; exact ⟨hqI, ((hcrit x).1 hq).2⟩
    · rintro ⟨hxI, hxc⟩
      exact mem_pair_iff.2 (honly x hxI hxc)
  · rw [hr₀p']; exact hr₀p
  · rw [hr₀q']; exact hr₀q
  · rw [hrmp']; exact hrmp
  · rw [hrmq']; exact hrmq

theorem exists_small_eps_partner (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hkp : (D.chart p hp).k = 1)
    (hkq : (D.chart q hq).k = 2) {a' b' : ℝ}
    (hother : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D.smallBall x hx, f y ∉ Icc a' b')
    {ε c : ℝ} (hε : 0 < ε)
    (hcst : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2 ∧
      (D.chart q hq).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm q hq ^ 2)
    (ha'p : a' < f p) (hc : f p + ε < c) (hcq : c < f q - ε) (hqb' : f q < b')
    (h : meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)) {ρ β : ℝ} (hρ : 0 < ρ)
    (hβ : 0 < β) :
    ∃ (D₁ : GradientLikeStrip I f a b crit) (hkq₁ : (D₁.chart q hq).k = 2) (ε₁ : ℝ),
      0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ < β ∧
      (∀ x hx, (D₁.chart x hx).χ = (D.chart x hx).χ ∧ (D₁.chart x hx).k = (D.chart x hx).k ∧
        (D₁.chart x hx).R = (D.chart x hx).R ∧ (D₁.chart x hx).R' = (D.chart x hx).R' ∧
        (D₁.chart x hx).r₀ ≤ (D.chart x hx).r₀ ∧ (D₁.chart x hx).r₀ ≤ ρ) ∧
      (∀ x hx, D₁.rm x hx = D.rm x hx) ∧
      (D₁.chart p hp).r₀ ^ 2 < 2 * ε₁ ∧ (D₁.chart q hq).r₀ ^ 2 < 2 * ε₁ ∧
      meetsRightOnce D₁ p hp ε₁ c (leftLoop D₁ q hq hkq₁ ε₁ c) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  obtain ⟨hr₀p, hrmp, hr₀q, hrmq⟩ := hcst
  have hpab : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hqab : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hcb : c ≤ b := by linarith [hqab.2]
  have hrmRp : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
    pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
  have hrmRq : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 :=
    pow_le_pow_left₀ (D.rm_pos q hq).le (D.hrm q hq).2 2
  have hRεp : 2 * ε < (D.chart p hp).R ^ 2 := by linarith
  have hRεq : 2 * ε < (D.chart q hq).R ^ 2 := by linarith
  have hRR'q : (D.chart q hq).R ^ 2 < (D.chart q hq).R' ^ 2 :=
    pow_lt_pow_left₀ (D.chart q hq).hRR' (D.chart q hq).R_pos.le two_ne_zero
  have hcl : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ x (hx : x ∈ crit),
      y ∉ D.closedSmallBall x hx := by
    intro y hy x hx hmem
    by_cases hxp : x = p
    · subst hxp
      have h := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hmem
      rw [abs_le] at h
      linarith [hy.1, h.2]
    by_cases hxq : x = q
    · subst hxq
      have h := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hmem
      rw [abs_le] at h
      linarith [hy.2, h.1]
    obtain ⟨z, hz, rfl⟩ := hmem
    have hz' : morseNorm n z ≤ (D.chart x hx).r₀ := hz
    have hsrc : z ∈ (D.chart x hx).χ.source :=
      (D.chart x hx).hsrc z (hz'.trans (D.r₀_lt_R x hx).le)
    have hχc : ContinuousAt (D.chart x hx).χ ((1 : ℝ) • z) := by
      rw [one_smul]
      exact (D.chart x hx).χ.continuousAt hsrc
    have hcont : ContinuousAt (fun t : ℝ => f ((D.chart x hx).χ (t • z))) 1 :=
      hfs.continuous.continuousAt.comp (f := fun t : ℝ => (D.chart x hx).χ (t • z))
        (hχc.comp (f := fun t : ℝ => t • z) (continuous_id.smul continuous_const).continuousAt)
    have hIoo : f ((D.chart x hx).χ ((1 : ℝ) • z)) ∈ Ioo a' b' := by
      rw [one_smul]
      constructor <;> linarith [hy.1, hy.2]
    have hev := hcont.eventually_mem (isOpen_Ioo.mem_nhds hIoo)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set t : ℝ := 1 - min (δ / 2) (1 / 2) with ht
    have hmin1 : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hmin2 : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
    have hmin3 : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have ht0 : 0 < t := by linarith
    have ht1 : t < 1 := by linarith
    have hdist : dist t 1 < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hmemI := hball hdist
    apply hother x hx hxp hxq ((D.chart x hx).χ (t • z)) ⟨t • z, ?_, rfl⟩
      (Ioo_subset_Icc_self hmemI)
    change morseNorm n (t • z) < (D.chart x hx).r₀
    rw [ModelField.morseNorm_smul, abs_of_pos ht0]
    nlinarith [(D.chart x hx).hr₀, ModelField.morseNorm_nonneg z]
  have hw : ∀ t : ℝ, (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
    intro t h
    have h0 : Real.cos (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h (Fin.cast hkq.symm 0)
    have h1 : Real.sin (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h (Fin.cast hkq.symm 1)
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h0, h1] at this
    norm_num at this
  have hlp : ∀ t, f (leftPt D q hq hkq ε t) = f q - ε := fun t =>
    (D.chart q hq).f_chart_of_mem_leftModelSphere hRεq.le
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le (hw t))
  have htraj : ∀ t, ∀ s ∈ Icc 0 (f q - ε - (f p + ε)),
      f (D.flow s (leftPt D q hq hkq ε t)) = f q - ε - s := by
    intro t s hs
    have hsub : Icc 0 (f q - ε - (f p + ε)) ⊆ uIcc 0 (f q - ε - (f p + ε)) := Icc_subset_uIcc
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels hfs (D := D)
      (x := leftPt D q hq hkq ε t) (T := f q - ε - (f p + ε)) ?_ ?_ ?_ s (hsub hs)
    · rw [h, hlp]
    · rw [hlp]; constructor <;> linarith [hqab.1, hqab.2, hpab.1]
    · rw [hlp]; constructor <;> linarith [hpab.1, hpab.2]
    · intro y hy x hx hmem
      rw [hlp, uIcc_of_ge (by linarith)] at hy
      exact hcl y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x hx
        (D.smallBall_subset_closedSmallBall x hx hmem)
  have hfree : ∀ t, ∀ s ∈ Icc 0 (f q - ε - (f p + ε)), ∀ x (hx : x ∈ crit),
      D.flow s (leftPt D q hq hkq ε t) ∉ D.closedSmallBall x hx := by
    intro t s hs
    apply hcl
    rw [htraj t s hs]
    constructor <;> linarith [hs.1, hs.2]
  set ε₁ : ℝ := min ε β / 2 with hε₁
  have hε₁pos : 0 < ε₁ := by have := lt_min hε hβ; linarith
  have hε₁ε : ε₁ ≤ ε := by have := min_le_left ε β; linarith
  have hε₁β : ε₁ < β := by have := min_le_right ε β; linarith
  obtain ⟨m, hmpos, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x (hx : x ∈ crit), m ≤ (D.chart x hx).r₀ := by
    let S : Finset ℝ := insert 1 (crit.attach.image fun x => (D.chart x.1 x.2).r₀)
    have hne : S.Nonempty := Finset.insert_nonempty _ _
    refine ⟨S.min' hne, ?_, fun x hx => S.min'_le _ ?_⟩
    · rcases Finset.mem_insert.1 (S.min'_mem hne) with h | h
      · rw [h]; norm_num
      · obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
        rw [← hy]; exact (D.chart y.1 y.2).hr₀
    · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
  set ρ' : ℝ := min (min ρ m) (min 1 ε₁) with hρ'
  have hρ'pos : 0 < ρ' := lt_min (lt_min hρ hmpos) (lt_min one_pos hε₁pos)
  have hρ'ρ : ρ' ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ'm : ρ' ≤ m := (min_le_left _ _).trans (min_le_right _ _)
  have hρ'1 : ρ' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ'ε₁ : ρ' ≤ ε₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hsq : (ρ' / 2) ^ 2 < 2 * ε₁ := by nlinarith
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ :=
    GradientLikeStrip.exists_shrinkAll hfs D hρ'pos fun x hx => hρ'm.trans (hm x hx)
  have hkq₁ : (E.chart q hq).k = 2 := (hE1 q hq).2.1.trans hkq
  have hr₀le : ∀ x (hx : x ∈ crit), (E.chart x hx).r₀ ≤ (D.chart x hx).r₀ := fun x hx => by
    rw [hE2 x hx]; linarith [hm x hx]
  have hr₀lt : ∀ x (hx : x ∈ crit), (E.chart x hx).r₀ < (D.chart x hx).r₀ := fun x hx => by
    rw [hE2 x hx]; linarith [hm x hx]
  have hVeq : ∀ y, (∀ x (hx : x ∈ crit), y ∉ D.closedSmallBall x hx) → E.V y = D.V y := by
    intro y hy
    refine hE4 y fun x hx hmem => hy x hx ?_
    obtain ⟨z, hz, rfl⟩ := hmem
    exact ⟨z, (show morseNorm n z ≤ (D.chart x hx).r₀ / 2 from hz).trans
      (by linarith [(D.chart x hx).hr₀]), rfl⟩
  have hEflow : ∀ t, ∀ s ∈ Icc 0 (f q - ε - (f p + ε)),
      E.flow s (leftPt D q hq hkq ε t) = D.flow s (leftPt D q hq hkq ε t) := by
    intro t s hs
    apply flow_eq_of_agree_along D E
    intro u hu
    rw [uIcc_of_le hs.1] at hu
    exact hVeq _ (hfree t u ⟨hu.1, hu.2.trans hs.2⟩)
  have hT₁ : f q - ε - c ∈ Icc 0 (f q - ε - (f p + ε)) := ⟨by linarith, by linarith⟩
  have hloopD : ∀ t, leftLoop D q hq hkq ε c t =
      D.flow (f q - ε - c) (leftPt D q hq hkq ε t) := fun t => rfl
  have hlevD : ∀ t, f (leftLoop D q hq hkq ε c t) = c := by
    intro t
    rw [hloopD, htraj t _ hT₁]; ring
  have hmemT : ∀ u ∈ Icc 0 (c - (f p + ε)),
      f q - ε - c + u ∈ Icc 0 (f q - ε - (f p + ε)) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hdescD : ∀ t, ∀ u ∈ Icc 0 (c - (f p + ε)),
      D.flow u (leftLoop D q hq hkq ε c t) =
        D.flow (f q - ε - c + u) (leftPt D q hq hkq ε t) := by
    intro t u _
    rw [hloopD, D.flow_flow]
  have hfreeD : ∀ t, descendsFreely D (c - (f p + ε)) (leftLoop D q hq hkq ε c t) := by
    intro t u hu x hx
    rw [hdescD t u hu]
    exact hfree t _ (hmemT u hu) x hx
  have hflowLoop : ∀ t, ∀ u ∈ Icc 0 (c - (f p + ε)),
      E.flow u (leftLoop D q hq hkq ε c t) = D.flow u (leftLoop D q hq hkq ε c t) := by
    intro t u hu
    rw [hdescD t u hu, hloopD, ← hEflow t _ hT₁, E.flow_flow, hEflow t _ (hmemT u hu)]
  obtain ⟨-, hloop⟩ := leftLoop_congr D E hq hq hkq hkq₁ (hE1 q hq).1 rfl (ε := ε) (c := c)
    fun t => hEflow t _ hT₁
  have hRεpE : 2 * ε < (E.chart p hp).R ^ 2 := by rw [(hE1 p hp).2.2.1]; exact hRεp
  have hM₀ : meetsRightOnce E p hp ε c (leftLoop D q hq hkq ε c) :=
    meetsRightOnce_transfer hfs D E hp hp (hE1 p hp).1 (hE1 p hp).2.1
      (hE1 p hp).2.2.1.le rfl hε hRεpE hc.le hcb hlevD hfreeD
      (fun t => hflowLoop t _ ⟨by linarith, le_rfl⟩) h
  have hr₀qE : (E.chart q hq).r₀ ^ 2 < 2 * ε₁ := by rw [hE2 q hq]; exact hsq
  have hr₀pE : (E.chart p hp).r₀ ^ 2 < 2 * ε₁ := by rw [hE2 p hp]; exact hsq
  have hR'qE : 2 * ε < (E.chart q hq).R' ^ 2 := by
    rw [(hE1 q hq).2.2.2]; linarith
  obtain ⟨hLL, -, -⟩ := leftLoop_eq_of_le E hq hkq₁ (c := c) hε₁pos hε₁ε hr₀qE hR'qE
    (fun y hy _ => E.model q hq y (by
      rw [hE3 q hq]
      exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos q hq).le (by linarith)))
  have hrmpE : 8 * ε < E.rm p hp ^ 2 := by rw [hE3 p hp]; exact hrmp
  have hballs : ∀ x (hx : x ∈ crit), x ≠ p → ∀ y ∈ E.closedSmallBall x hx,
      f y ∉ Icc (f p + ε₁) (f p + ε) := by
    intro x hx hxp y hy hyI
    by_cases hxq : x = q
    · subst hxq
      have h := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hy
      rw [abs_le] at h
      linarith [hyI.2, h.1]
    · obtain ⟨z, hz, rfl⟩ := hy
      have hz' : morseNorm n z ≤ (E.chart x hx).r₀ := hz
      refine hother x hx hxp hxq ((E.chart x hx).χ z) ?_
        ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
      rw [(hE1 x hx).1]
      exact ⟨z, hz'.trans_lt (hr₀lt x hx), rfl⟩
  have hlevE : ∀ t, f (leftLoop E q hq hkq₁ ε c t) = c := by
    rw [hloop]; exact hlevD
  have hfreeE : ∀ t, descendsFreely E (c - (f p + ε)) (leftLoop E q hq hkq₁ ε c t) := by
    rw [hloop]
    intro t u hu x hx hmem
    rw [hflowLoop t u hu] at hmem
    apply hfreeD t u hu x hx
    obtain ⟨z, hz, hzeq⟩ := hmem
    refine ⟨z, (show morseNorm n z ≤ (E.chart x hx).r₀ from hz).trans (hr₀le x hx), ?_⟩
    rw [← hzeq, (hE1 x hx).1]
  have hcirc : ∀ j : Fin 2, Continuous fun t : ℝ => circ2 t j := by
    intro j
    fin_cases j <;> dsimp [circ2] <;> fun_prop
  have hwc : Continuous fun t : ℝ => (fun i => circ2 t (Fin.cast hkq i)) :=
    continuous_pi fun i => hcirc _
  have hγD : Continuous (leftLoop D q hq hkq ε c) := by
    refine (D.continuous_flow (f q - ε - c)).comp ?_
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hsrc : (D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hkq i)) ∈
        (D.chart q hq).χ.source :=
      (D.chart q hq).hsrc _ ((D.chart q hq).morseNorm_sphereParam_le hε.le hRεq.le (hw t))
    have h1 : ContinuousAt (fun s : ℝ =>
        (D.chart q hq).sphereParam ε (fun i => circ2 s (Fin.cast hkq i))) t :=
      ContinuousAt.comp (x := t) (g := (D.chart q hq).sphereParam ε)
        (f := fun s : ℝ => (fun i => circ2 s (Fin.cast hkq i)))
        ((D.chart q hq).contDiffAt_sphereParam ε (hw t)).continuousAt hwc.continuousAt
    exact ContinuousAt.comp (x := t) ((D.chart q hq).χ.continuousAt hsrc) h1
  have hγE : Continuous (leftLoop E q hq hkq₁ ε c) := by rw [hloop]; exact hγD
  obtain ⟨-, hM⟩ := meetsRightOnce_of_le hfs E hp hε₁pos hε₁ε hr₀pE hrmpE hc.le hcb hballs
    hγE hlevE hfreeE (by rw [hloop]; exact hM₀)
  refine ⟨E, hkq₁, ε₁, hε₁pos, hε₁ε, hε₁β, fun x hx => ⟨(hE1 x hx).1, (hE1 x hx).2.1,
    (hE1 x hx).2.2.1, (hE1 x hx).2.2.2, hr₀le x hx, ?_⟩, hE3, hr₀pE, hr₀qE, ?_⟩
  · rw [hE2 x hx]; linarith
  · rw [hLL]; exact hM

theorem isCancellingPair_of_ambient [DecidableEq M]
    (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hkp : (D.chart p hp).k = 1)
    (hkq : (D.chart q hq).k = 2) {a' b' : ℝ} (ha' : a < a') (hb' : b' < b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hpI : f p ∈ Ioo a' b') (hqI : f q ∈ Ioo a' b') (hpq : f p < f q)
    (honly : ∀ x, f x ∈ Ioo a' b' → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x = p ∨ x = q)
    (hother : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D.smallBall x hx, f y ∉ Icc a' b')
    {ε c : ℝ} (hε : 0 < ε)
    (hcst : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2 ∧
      (D.chart q hq).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm q hq ^ 2)
    (hc : f p + ε < c) (hcq : c < f q - ε)
    (h : meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)) :
    isCancellingPair I f a' b' p q := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hδx : ∀ x (hx : x ∈ crit), f x ∈ Ioo a' b' → ∃ δ > 0,
      (D.chart x hx).χ '' Metric.ball 0 δ ⊆ f ⁻¹' Ioo a' b' := by
    intro x hx hxI
    have hcont : ContinuousAt (fun y => f ((D.chart x hx).χ y)) 0 :=
      hfc.continuousAt.comp ((D.chart x hx).χ.continuousAt
        ((D.chart x hx).hball (D.chart x hx).zero_mem_ball))
    have hmem : (fun y => f ((D.chart x hx).χ y)) ⁻¹' Ioo a' b' ∈ 𝓝 (0 : Fin n → ℝ) := by
      refine hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      simp only [(D.chart x hx).hχ0]
      exact hxI
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hsub hy
  obtain ⟨δp, hδp, hδpsub⟩ := hδx p hp hpI
  obtain ⟨δq, hδq, hδqsub⟩ := hδx q hq hqI
  set δ := min δp δq with hδdef
  have hδ : 0 < δ := lt_min hδp hδq
  have hm : ∃ m > 0, ∀ x (hx : x ∈ crit), m ≤ (D.chart x hx).r₀ := by
    have hne : (crit.attach.image fun x => (D.chart x.1 x.2).r₀).Nonempty :=
      (Finset.attach_nonempty_iff.2 ⟨p, hp⟩).image _
    refine ⟨(crit.attach.image fun x => (D.chart x.1 x.2).r₀).min' hne, ?_,
      fun x hx => Finset.min'_le _ _ (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)⟩
    obtain ⟨⟨x, hx⟩, -, hxe⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
    rw [← hxe]
    exact (D.chart x hx).hr₀
  obtain ⟨m, hm0, hmle⟩ := hm
  set ρ := min (δ / 16) (m / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  set Rpq := min (min (D.chart p hp).R (D.chart q hq).R) (δ / 2) with hRpqdef
  have hRpq : 0 < Rpq := lt_min (lt_min (D.chart p hp).R_pos (D.chart q hq).R_pos) (by positivity)
  set β := Rpq ^ 2 / 8 with hβdef
  have hβ : 0 < β := by positivity
  obtain ⟨D₁, hkq₁, ε₁, hε₁, hε₁ε, hε₁β, hch, hrm₁, hr₀p, hr₀q, h₁⟩ :=
    exists_small_eps_partner hf D hp hq hkp hkq hother hε hcst hpI.1 hc hcq hqI.2 h hρ hβ
  have hr₀₁ : ∀ x (hx : x ∈ crit), (D₁.chart x hx).r₀ < (D.chart x hx).r₀ := by
    intro x hx
    have h1 := (hch x hx).2.2.2.2.2
    have h2 := hmle x hx
    have h3 : ρ ≤ m / 2 := min_le_right _ _
    linarith
  have hr₀ρ : ∀ x (hx : x ∈ crit), 4 * (D₁.chart x hx).r₀ < min (D₁.chart x hx).R (δ / 2) := by
    intro x hx
    have h1 := (hch x hx).2.2.2.2.2
    have h3 : ρ ≤ δ / 16 := min_le_left _ _
    have h4 := (D₁.chart x hx).hr₀R
    refine lt_min h4 ?_
    linarith
  obtain ⟨D₂, hch₂, hrm₂, hV₂⟩ := D₁.exists_restrict le_rfl le_rfl crit (fun r hr => hr)
    (fun r hr hr' => absurd hr hr')
    (fun x hx => min (D₁.chart x hx).R (δ / 2)) (fun x hx => min (D₁.chart x hx).R' δ)
    (fun x hx => min (D₁.rm x hx) (min (D₁.chart x hx).R (δ / 2)))
    (fun x hx => ⟨hr₀ρ x hx, min_le_left _ _⟩)
    (fun x hx => ⟨lt_min (lt_of_le_of_lt (min_le_left _ _) (D₁.chart x hx).hRR')
        (lt_of_le_of_lt (min_le_right _ _) (by linarith)), min_le_left _ _⟩)
    (fun x hx => ⟨lt_min (D₁.hrm x hx).1 (by linarith [hr₀ρ x hx, (D₁.chart x hx).hr₀]),
        min_le_left _ _, min_le_right _ _⟩)
    (fun x hx => (image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans (D₁.inStrip x hx))
    (fun x _ hx => hx)
  have hlevfree : ∀ y, f y ∈ Icc (f p + ε₁) (f q - ε₁) → ∀ x (hx : x ∈ crit),
      y ∉ D₁.closedSmallBall x hx := by
    intro y hy x hx hyx
    have habs := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hyx
    by_cases hxp : x = p
    · subst hxp
      rw [abs_le] at habs
      linarith [hy.1, habs.2]
    by_cases hxq : x = q
    · subst hxq
      rw [abs_le] at habs
      linarith [hy.2, habs.1]
    obtain ⟨z, hz, rfl⟩ := hyx
    have hzs : (D₁.chart x hx).χ z ∈ D.smallBall x hx :=
      ⟨z, lt_of_le_of_lt hz (hr₀₁ x hx), by rw [(hch x hx).1]⟩
    exact hother x hx hxp hxq _ hzs ⟨by linarith [hy.1, hpI.1], by linarith [hy.2, hqI.2]⟩
  have hw : ∀ t, (fun i => circ2 t (Fin.cast hkq₁ i)) ≠ 0 := by
    intro t hw0
    have h0 : Real.cos (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun hw0 (Fin.cast hkq₁.symm 0)
    have h1 : Real.sin (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun hw0 (Fin.cast hkq₁.symm 1)
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h0, h1] at this
    norm_num at this
  have hRq : 2 * ε₁ ≤ (D₁.chart q hq).R ^ 2 := by
    rw [(hch q hq).2.2.1]
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    have h3 : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 := pow_le_pow_left₀ h2.le h1 2
    nlinarith [hcst.2.2.2]
  have hleftPt : ∀ t, f (leftPt D₁ q hq hkq₁ ε₁ t) = f q - ε₁ := fun t =>
    (D₁.chart q hq).f_chart_of_mem_leftModelSphere hRq
      ((D₁.chart q hq).sphereParam_mem_leftModelSphere hε₁.le (hw t))
  have hdesc : ∀ t, ∀ u ∈ Icc 0 (f q - f p - 2 * ε₁), ∀ x (hx : x ∈ crit),
      D₁.flow u (leftPt D₁ q hq hkq₁ ε₁ t) ∉ D₁.closedSmallBall x hx := by
    intro t u hu
    have h1 := GradientLikeStrip.f_flow_le (D := D₁) hfs (leftPt D₁ q hq hkq₁ ε₁ t) hu.1
    have h2 := GradientLikeStrip.sub_le_f_flow (D := D₁) hfs (leftPt D₁ q hq hkq₁ ε₁ t) hu.1
    rw [hleftPt t] at h1 h2
    exact hlevfree _ ⟨by linarith [hu.2], h1⟩
  have hT : 0 ≤ f q - ε₁ - c := by linarith
  have hfree : ∀ t, descendsFreely D₁ (c - (f p + ε₁)) (leftLoop D₁ q hq hkq₁ ε₁ c t) := by
    intro t s hs x hx
    simp only [leftLoop]
    rw [D₁.flow_flow]
    exact hdesc t _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ x hx
  have hlev : ∀ t, f (leftLoop D₁ q hq hkq₁ ε₁ c t) = c := by
    intro t
    have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D₁) hfs
      (x := leftPt D₁ q hq hkq₁ ε₁ t) (T := f q - ε₁ - c)
      (by rw [hleftPt t]; constructor <;> linarith [hqI.2, hpI.1])
      (by rw [hleftPt t]; constructor <;> linarith [hqI.2, hpI.1])
      (fun s hs x hx hsx => by
        rw [uIcc_of_le hT] at hs
        exact hdesc t s ⟨hs.1, by linarith [hs.2]⟩ x hx
          (D₁.smallBall_subset_closedSmallBall x hx hsx))
      (f q - ε₁ - c) right_mem_uIcc
    simp only [leftLoop]
    rw [h, hleftPt t]
    ring
  have hflow₂ : ∀ t x, D₂.flow t x = D₁.flow t x :=
    GradientLikeStrip.flow_eq_of_V_eq D₁ D₂ hV₂
  have hkq₂ : (D₂.chart q hq).k = 2 := ((hch₂ q hq).2.1).trans hkq₁
  have hloop : leftLoop D₂ q hq hkq₂ ε₁ c = leftLoop D₁ q hq hkq₁ ε₁ c :=
    (leftLoop_congr D₁ D₂ hq hq hkq₁ hkq₂ (hch₂ q hq).1 rfl
      (fun t => hflow₂ _ _)).2
  have hR₂p : (D₂.chart p hp).R = min (D₁.chart p hp).R (δ / 2) := (hch₂ p hp).2.2.2.1
  have hR₂q : (D₂.chart q hq).R = min (D₁.chart q hq).R (δ / 2) := (hch₂ q hq).2.2.2.1
  have hRpqp : Rpq ≤ (D₂.chart p hp).R := by
    rw [hR₂p, (hch p hp).2.2.1]
    exact min_le_min_right _ (min_le_left _ _)
  have hRpqq : Rpq ≤ (D₂.chart q hq).R := by
    rw [hR₂q, (hch q hq).2.2.1]
    exact min_le_min_right _ (min_le_right _ _)
  have hsqp : Rpq ^ 2 ≤ (D₂.chart p hp).R ^ 2 := pow_le_pow_left₀ hRpq.le hRpqp 2
  have hsqq : Rpq ^ 2 ≤ (D₂.chart q hq).R ^ 2 := pow_le_pow_left₀ hRpq.le hRpqq 2
  have hmeet₂ : meetsRightOnce D₂ p hp ε₁ c (leftLoop D₁ q hq hkq₁ ε₁ c) :=
    meetsRightOnce_transfer hfs D₁ D₂ hp hp (hch₂ p hp).1 (hch₂ p hp).2.1
      (by rw [hR₂p]; exact min_le_left _ _) rfl hε₁ (by nlinarith) (by linarith)
      (by linarith [hqI.2]) hlev hfree (fun t => hflow₂ _ _) h₁
  rw [← hloop] at hmeet₂
  have hkp₂ : (D₂.chart p hp).k = 1 := (hch₂ p hp).2.1.trans ((hch p hp).2.1.trans hkp)
  have himg : ∀ x (hx : x ∈ crit), (D₂.chart x hx).χ '' Metric.ball 0 (D₂.chart x hx).R' ⊆
      (D.chart x hx).χ '' Metric.ball 0 δ := by
    intro x hx
    rw [(hch₂ x hx).1, (hch₂ x hx).2.2.2.2, (hch x hx).1]
    exact image_mono (Metric.ball_subset_ball (min_le_right _ _))
  have himp : (D₂.chart p hp).χ '' Metric.ball 0 (D₂.chart p hp).R' ⊆ f ⁻¹' Ioo a' b' :=
    (himg p hp).trans ((image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hδpsub)
  have himq : (D₂.chart q hq).χ '' Metric.ball 0 (D₂.chart q hq).R' ⊆ f ⁻¹' Ioo a' b' :=
    (himg q hq).trans ((image_mono (Metric.ball_subset_ball (min_le_right _ _))).trans hδqsub)
  have hother₂ : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D₂.smallBall x hx,
      f y ∉ Icc a' b' := by
    intro x hx hxp hxq y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : morseNorm n z < (D₂.chart x hx).r₀ := hz
    rw [(hch₂ x hx).2.2.1] at hz'
    refine hother x hx hxp hxq _ ⟨z, lt_trans hz' (hr₀₁ x hx), ?_⟩
    rw [(hch₂ x hx).1, (hch x hx).1]
  have hrm8 : ∀ x (hx : x ∈ crit), Rpq ≤ min (D₁.chart x hx).R (δ / 2) →
      8 * ε₁ < D.rm x hx ^ 2 → 8 * ε₁ < D₂.rm x hx ^ 2 := by
    intro x hx hle hA
    rw [hrm₂ x hx, hrm₁ x hx]
    have hB : 8 * ε₁ < min (D₁.chart x hx).R (δ / 2) ^ 2 := by
      have := pow_le_pow_left₀ hRpq.le hle 2
      have h8 : 8 * β = Rpq ^ 2 := by rw [hβdef]; ring
      linarith
    rcases min_cases (D.rm x hx) (min (D₁.chart x hx).R (δ / 2)) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rw [h] <;> assumption
  have hRpqp' : Rpq ≤ min (D₁.chart p hp).R (δ / 2) := hR₂p ▸ hRpqp
  have hRpqq' : Rpq ≤ min (D₁.chart q hq).R (δ / 2) := hR₂q ▸ hRpqq
  have hcst₂ : (D₂.chart p hp).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < D₂.rm p hp ^ 2 ∧
      (D₂.chart q hq).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < D₂.rm q hq ^ 2 := by
    refine ⟨?_, hrm8 p hp hRpqp' (by linarith [hcst.2.1]), ?_,
      hrm8 q hq hRpqq' (by linarith [hcst.2.2.2])⟩
    · rw [(hch₂ p hp).2.2.1]; exact hr₀p
    · rw [(hch₂ q hq).2.2.1]; exact hr₀q
  exact isCancellingPair_of_fine hf D₂ hcrit hp hq hkp₂ hkq₂ ha' hb' hreg hpq honly himp himq
    hother₂ hε₁ hcst₂ (by linarith) (by linarith) hmeet₂

end Sard

end

end IndexOnePartner

end DifferentialGeometry.Topology
