module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Configuration.MiddleSard

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {a b : ℝ} {crit : Finset M}

omit [I.Boundaryless] in
theorem exists_addLevelField {f : M → ℝ} (D : GradientLikeStrip I f a b crit)
    (Z : (x : M) → TangentSpace I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)))
    (hZc : IsCompact (tsupport Z)) (hdf : ∀ x, dfV I f Z x = 0)
    (hZmodel : ∀ p hp, ∀ y, morseNorm n y < D.rm p hp → Z ((D.chart p hp).χ y) = 0) :
    ∃ D' : GradientLikeStrip I f a b crit, (∀ x, D'.V x = D.V x + Z x) ∧
      (∀ p hp, D'.chart p hp = D.chart p hp) ∧ ∀ p hp, D'.rm p hp = D.rm p hp := by
  have hadd : ∀ x, dfV I f (fun x => D.V x + Z x) x = dfV I f D.V x := by
    intro x
    rw [dfV_add, hdf x, add_zero]
  refine ⟨{ V := fun x => D.V x + Z x
            smooth := D.smooth.add_section hZ
            compact := ?_
            rate := fun x => by
              have h := hadd x
              unfold dfV at h
              rw [h]
              exact D.rate x
            chart := D.chart
            disjoint := D.disjoint
            inStrip := D.inStrip
            unit := fun x hx hno => by
              have h := hadd x
              unfold dfV at h
              rw [h]
              exact D.unit x hx hno
            neg := fun x hx hnc => by
              have h := hadd x
              unfold dfV at h
              rw [h]
              exact D.neg x hx hnc
            rm := D.rm
            hrm := D.hrm
            model := fun p hp y hy => by
              have hz := hZmodel p hp y hy
              rw [hz, add_zero]
              exact D.model p hp y hy }, fun x => rfl, fun p hp => rfl, fun p hp => rfl⟩
  refine (D.compact.union hZc).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun x hx => ?_) (D.compact.union hZc).isClosed)
  by_contra h
  rw [mem_union, not_or] at h
  apply hx
  simp only
  rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2]
  exact add_zero (0 : Fin n → ℝ)

theorem sardAgree_of_rescale {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {ε ε' : ℝ} (hεε' : ε' ≤ ε) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit)
    (hv : D.sardValid ε p hq hp) (hv' : D'.sardValid ε' p hq hp) (c c' : ℝ) :
    D.sardAgree D' ε ε' c c' p hq hp := by
  classical
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hV⟩ := hresc
  obtain ⟨hε, -, -, hrmp, hrmq, hfpq, hlev⟩ := hv
  obtain ⟨hε', -, -, hrmp', hrmq', hgpq, hlev'⟩ := hv'
  have hkq : (D'.chart q hq).k = (D.chart q hq).k := (hχ q hq).2
  have hkp : (D'.chart p hp).k = (D.chart p hp).k := (hχ p hp).2
  have hχq : (D'.chart q hq).χ = (D.chart q hq).χ := (hχ q hq).1
  have hχp : (D'.chart p hp).χ = (D.chart p hp).χ := (hχ p hp).1
  have Gpart : ∀ (k₁ k₂ : ℕ) (h : k₁ = k₂) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n) (y : Fin n → ℝ),
      ‖negPart h₁ y‖ = ‖negPart h₂ y‖ ∧ ‖posPart h₁ y‖ = ‖posPart h₂ y‖ ∧
      (negPart h₁ y = 0 ↔ negPart h₂ y = 0) ∧ (posPart h₁ y = 0 ↔ posPart h₂ y = 0) ∧
      ∀ j, (ModelField.scaledNegativePart h₁ y).ofLp j = (ModelField.scaledNegativePart h₂ y).ofLp (Fin.cast h j) := by
    intro k₁ k₂ h h₁ h₂ y
    subst h
    exact ⟨rfl, rfl, Iff.rfl, Iff.rfl, fun j => rfl⟩
  have Gsph : ∀ (k₁ k₂ : ℕ) (h : k₁ = k₂) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n) (r : ℝ) (w : Fin k₂ → ℝ),
      recombine h₁ ((r / ‖(EuclideanSpace.equiv (Fin k₁) ℝ).symm (w ∘ Fin.cast h)‖) •
        (EuclideanSpace.equiv (Fin k₁) ℝ).symm (w ∘ Fin.cast h)) 0 =
      recombine h₂ ((r / ‖(EuclideanSpace.equiv (Fin k₂) ℝ).symm w‖) •
        (EuclideanSpace.equiv (Fin k₂) ℝ).symm w) 0 := by
    intro k₁ k₂ h h₁ h₂ r w
    subst h
    rfl
  have hrmp0 := D.rm_pos p hp
  have hrmq0 := D.rm_pos q hq
  have hrmp0' := D'.rm_pos p hp
  have hrmq0' := D'.rm_pos q hq
  have hRp : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hRq : D.rm q hq ≤ (D.chart q hq).R := (D.hrm q hq).2
  have hRp' : D'.rm p hp ≤ (D'.chart p hp).R := (D'.hrm p hp).2
  have hRq' : D'.rm q hq ≤ (D'.chart q hq).R := (D'.hrm q hq).2
  have hRq2 : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    nlinarith only [mul_le_mul hRq hRq hrmq0.le (hrmq0.le.trans hRq), hrmq, hε]
  have hRq2' : 2 * ε' ≤ (D'.chart q hq).R ^ 2 := by
    nlinarith only [mul_le_mul hRq' hRq' hrmq0'.le (hrmq0'.le.trans hRq'), hrmq', hε']
  have hRp2 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := by
    nlinarith only [mul_le_mul hRp hRp hrmp0.le (hrmp0.le.trans hRp)]
  have hRp2' : D'.rm p hp ^ 2 ≤ (D'.chart p hp).R ^ 2 := by
    nlinarith only [mul_le_mul hRp' hRp' hrmp0'.le (hrmp0'.le.trans hRp')]
  have hfpa : a < f p := (D.f_mem_Ioo p hp).1
  have hfqb : f q < b := (D.f_mem_Ioo q hq).2
  have hgpa : a < g p := (D'.f_mem_Ioo p hp).1
  have hgqb : g q < b := (D'.f_mem_Ioo q hq).2
  have hunitD : ∀ y, f y = f p + ε → dfV I f D.V y = -1 := fun y hy =>
    D.dfV_eq_neg_one_of_mem_unitRegion (show y ∈ D.unitRegion from
      ⟨by rw [hy]; constructor <;> linarith only [hfpa, hε, hfpq, hfqb],
        hlev y (by rw [hy]; constructor <;> linarith only [hfpq])⟩)
  have hunitD' : ∀ y, g y = g p + ε' → dfV I g D'.V y = -1 := fun y hy =>
    D'.dfV_eq_neg_one_of_mem_unitRegion (show y ∈ D'.unitRegion from
      ⟨by rw [hy]; constructor <;> linarith only [hgpa, hε', hgpq, hgqb],
        hlev' y (by rw [hy]; constructor <;> linarith only [hgpq])⟩)
  have hL : ∀ w, D.landing p hq ε c ε w = D.flow (f q - ε - (f p + ε))
      ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := by
    intro w
    simp only [landing, flow_flow]
    congr 1
    ring
  have hL' : ∀ w : Fin (D.chart q hq).k → ℝ, D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq) =
      D'.flow (g q - ε' - (g p + ε')) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε' w)) := by
    intro w
    have hsp : (D'.chart q hq).sphereParam ε' (w ∘ Fin.cast hkq) =
        (D.chart q hq).sphereParam ε' w := by
      simp only [MorseNormalChart.sphereParam, MorseNormalChart.toE]
      exact Gsph _ _ hkq _ _ _ w
    simp only [landing, flow_flow, hsp, hχq]
    congr 1
    ring
  have hLf : ∀ w, w ≠ 0 → f (D.landing p hq ε c ε w) = f p + ε := by
    intro w hw
    have := f_landing (D := D) (c := f p + ε) hp hf hε hε hRq2 le_rfl hfpq.le hlev hw
    have h2 : D.landing p hq ε c ε w = D.landing p hq ε (f p + ε) ε w := by
      simp only [landing, flow_flow]
      congr 1
      ring
    rw [h2]
    exact this
  have hLg : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      g (D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq)) = g p + ε' := by
    intro w hw
    have hw' : w ∘ Fin.cast hkq ≠ 0 := by
      intro h0
      apply hw
      funext i
      have := congrFun h0 (Fin.cast hkq.symm i)
      simpa using this
    have := f_landing (D := D') (c := g p + ε') hp hg hε' hε' hRq2' le_rfl hgpq.le hlev' hw'
    have h2 : D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq) =
        D'.landing p hq ε' (g p + ε') ε' (w ∘ Fin.cast hkq) := by
      simp only [landing, flow_flow]
      congr 1
      ring
    rw [h2]
    exact this
  have hrep : ∀ x, ∃ σ : ℝ → ℝ, Function.Surjective σ ∧ ∀ s, D.flow s x = D'.flow (σ s) x := by
    intro x
    obtain ⟨σ, -, -, hσ, hfl⟩ := exists_reparam D' D hφc hm hφb hV x
    exact ⟨σ, hσ, hfl⟩
  have hQ1 : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → ∃ s₁, 0 ≤ s₁ ∧
      D.flow (-s₁) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) =
        (D.chart q hq).χ ((D.chart q hq).sphereParam ε' w) := by
    intro w hw
    have hE : (D.chart q hq).toE w ≠ 0 := (D.chart q hq).toE_ne_zero hw
    set ê := (‖(D.chart q hq).toE w‖)⁻¹ • (D.chart q hq).toE w with hê
    have hê1 : ‖ê‖ = 1 := norm_smul_inv_norm hE
    have hsp : ∀ r, (D.chart q hq).sphereParam r w =
        recombine (D.chart q hq).hk (Real.sqrt (2 * r) • ê) 0 := by
      intro r
      simp only [MorseNormalChart.sphereParam, hê, smul_smul, div_eq_mul_inv]
    have hlt : Real.sqrt (2 * ε) < D.rm q hq := (Real.sqrt_lt' hrmq0).2 (by linarith only [hrmq, hε])
    obtain ⟨s, hs, hfl⟩ := (CrossField.flow_ray_unstable D hf hq hê1
      (Real.sqrt_pos.2 (by linarith only [hε])) hlt).2 (Real.sqrt (2 * ε'))
      ⟨Real.sqrt_pos.2 (by linarith only [hε']), Real.sqrt_le_sqrt (by linarith only [hεε'])⟩
    refine ⟨s, hs, ?_⟩
    rw [hsp, hsp]
    exact hfl
  have hOR : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → ∀ s, ∃ s₂,
      D'.flow s₂ ((D.chart q hq).χ ((D.chart q hq).sphereParam ε' w)) =
        D.flow s (D.landing p hq ε c ε w) := by
    intro w hw s
    obtain ⟨s₁, -, hs₁⟩ := hQ1 w hw
    obtain ⟨σ, -, hσ⟩ := hrep ((D.chart q hq).χ ((D.chart q hq).sphereParam ε' w))
    refine ⟨σ (s₁ + (f q - ε - (f p + ε)) + s), ?_⟩
    rw [← hσ, hL, flow_flow, ← hs₁, flow_flow]
    congr 1
    ring
  have hOR' : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → ∃ τ,
      D.flow τ (D.landing p hq ε c ε w) = D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq) := by
    intro w hw
    obtain ⟨s₁, -, hs₁⟩ := hQ1 w hw
    obtain ⟨σ, hσs, hσ⟩ := hrep ((D.chart q hq).χ ((D.chart q hq).sphereParam ε' w))
    obtain ⟨u, hu⟩ := hσs (g q - ε' - (g p + ε'))
    refine ⟨-(f q - ε - (f p + ε)) - s₁ + u, ?_⟩
    rw [hL', ← hu, ← hσ, hL, flow_flow, ← hs₁, flow_flow]
    congr 1
    ring
  have hCORE : ∀ (y' : Fin n → ℝ) (x₀ : M) (τ : ℝ),
      2 * ε + 2 * ‖negPart (D.chart p hp).hk y'‖ ^ 2 < D.rm p hp ^ 2 →
      posPart (D.chart p hp).hk y' ≠ 0 →
      morseNormalForm (D.chart p hp).hk (f p) y' ≤ f p + ε →
      f x₀ = f p + ε → D.flow τ x₀ = (D.chart p hp).χ y' →
      x₀ ∈ (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} ∧
        ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm x₀) =
          ModelField.scaledNegativePart (D.chart p hp).hk y' := by
    intro y' x₀ τ hB hv hlevel hfx₀ hτ
    obtain ⟨t, ht0, hft, hball, -⟩ := exists_exit_asc (D := D) hf hp hε hB hv hlevel
    have hx₀ : x₀ = D.flow (-τ) ((D.chart p hp).χ y') := by rw [← hτ, flow_neg_flow]
    have hτt : -τ = -t := flow_level_unique hf hunitD (x := (D.chart p hp).χ y')
      (by rw [← hx₀]; exact hfx₀) hft
    rw [hτt] at hx₀
    have hsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤
        2 * ε + 2 * ‖negPart (D.chart p hp).hk y'‖ ^ 2} ⊆ {z | morseNorm n z < D.rm p hp} :=
      fun z hz => lt_of_pow_lt_pow_left₀ 2 hrmp0.le (lt_of_le_of_lt hz hB)
    have hmem : ∀ s ∈ uIcc 0 (-t), D.flow s ((D.chart p hp).χ y') ∈
        (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} := by
      intro s hs
      rw [uIcc_of_ge (by linarith only [ht0])] at hs
      exact image_mono hsub (hball s hs)
    have hy'rm : morseNorm n y' < D.rm p hp := by
      have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (D.chart p hp).hk y'
      have h2 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split
        (D.chart p hp).hk (f p) y'
      refine lt_of_pow_lt_pow_left₀ 2 hrmp0.le ?_
      linarith only [h1, h2, hlevel, hB]
    obtain ⟨l, hl0, -, -, hscale⟩ := CrossField.model_flow_scaling D hp hy'rm hmem
    refine ⟨hx₀ ▸ hmem (-t) right_mem_uIcc, ?_⟩
    rw [hx₀, hscale]
    simp only [ModelField.scaledNegativePart, ModelField.negPart_recombine, ModelField.posPart_recombine, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hl0, smul_smul]
    congr 1
    field_simp
  have hcast0 : ∀ w : Fin (D.chart q hq).k → ℝ, w ∘ Fin.cast hkq ≠ 0 ↔ w ≠ 0 := by
    intro w
    constructor
    · intro h h0
      apply h
      rw [h0]
      rfl
    · intro hw h0
      apply hw
      funext i
      have := congrFun h0 (Fin.cast hkq.symm i)
      simpa using this
  have hFWD : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      D.landing p hq ε c ε w ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R} →
      ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w)) = 0 →
      ∃ z', D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq) = (D.chart p hp).χ z' ∧
        negPart (D.chart p hp).hk z' = 0 ∧ ‖posPart (D.chart p hp).hk z'‖ ^ 2 = 2 * ε' := by
    intro w hw hwL hJ
    obtain ⟨y₀, hy₀R, hy₀L⟩ := hwL
    have hsy : (D.chart p hp).χ.symm (D.landing p hq ε c ε w) = y₀ := by
      rw [← hy₀L, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc _ hy₀R.le)]
    have hfy := (D.chart p hp).hnorm y₀ hy₀R.le
    rw [hy₀L, hLf w hw,
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hfy
    have hv0 : posPart (D.chart p hp).hk y₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hfy
      nlinarith only [hfy, hε, sq_nonneg ‖negPart (D.chart p hp).hk y₀‖]
    have hu0 : negPart (D.chart p hp).hk y₀ = 0 :=
      (ModelField.scaledNegativePart_eq_zero_iff _ hv0).1 (by rw [← hsy]; exact hJ)
    rw [hu0, norm_zero] at hfy
    have hvn2 : ‖posPart (D.chart p hp).hk y₀‖ ^ 2 = 2 * ε := by nlinarith only [hfy]
    have hvn : ‖posPart (D.chart p hp).hk y₀‖ = Real.sqrt (2 * ε) := by
      rw [← hvn2, Real.sqrt_sq (norm_nonneg _)]
    set ê := (‖posPart (D.chart p hp).hk y₀‖)⁻¹ • posPart (D.chart p hp).hk y₀ with hê
    have hê1 : ‖ê‖ = 1 := norm_smul_inv_norm hv0
    have hsê : Real.sqrt (2 * ε) • ê = posPart (D.chart p hp).hk y₀ := by
      rw [hê, smul_smul, ← hvn, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), one_smul]
    have hy₀eq : y₀ = recombine (D.chart p hp).hk 0 (Real.sqrt (2 * ε) • ê) := by
      conv_lhs => rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose
        (D.chart p hp).hk y₀]
      rw [hu0, hsê]
    have hlt : Real.sqrt (2 * ε) < D.rm p hp := (Real.sqrt_lt' hrmp0).2 (by linarith only [hrmp, hε])
    obtain ⟨s, -, hs⟩ := (CrossField.flow_ray_stable D hf hp hê1
      (Real.sqrt_pos.2 (by linarith only [hε])) hlt).2 (Real.sqrt (2 * ε'))
      ⟨Real.sqrt_pos.2 (by linarith only [hε']), Real.sqrt_le_sqrt (by linarith only [hεε'])⟩
    set z' := recombine (D.chart p hp).hk 0 (Real.sqrt (2 * ε') • ê) with hz'
    have hflow : D.flow s (D.landing p hq ε c ε w) = (D.chart p hp).χ z' := by
      rw [← hy₀L, hy₀eq]
      exact hs
    obtain ⟨s₂, hs₂⟩ := hOR w hw s
    have hz'u : negPart (D.chart p hp).hk z' = 0 := ModelField.negPart_recombine _ _ _
    have hz'v : ‖posPart (D.chart p hp).hk z'‖ ^ 2 = 2 * ε' := by
      rw [hz', ModelField.posPart_recombine, norm_smul, hê1, mul_one, Real.norm_eq_abs,
        sq_abs, Real.sq_sqrt (by linarith only [hε'])]
    have hz'n : morseNorm n z' ^ 2 = 2 * ε' := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (D.chart p hp).hk, hz'u, hz'v, norm_zero]
      ring
    have hz'R : morseNorm n z' < (D'.chart p hp).R :=
      lt_of_pow_lt_pow_left₀ 2 (D'.chart p hp).R_pos.le (by rw [hz'n]; linarith only [hrmp', hRp2', hε'])
    obtain ⟨hn1, hn2, -, -, -⟩ := Gpart _ _ hkp (D'.chart p hp).hk (D.chart p hp).hk z'
    have hgz : g ((D.chart p hp).χ z') = g p + ε' := by
      have := (D'.chart p hp).hnorm z' hz'R.le
      rw [hχp, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hn1, hn2,
        hz'u, hz'v, norm_zero] at this
      rw [this]
      ring
    have hTs : s₂ = g q - ε' - (g p + ε') := flow_level_unique hg hunitD'
      (x := (D.chart q hq).χ ((D.chart q hq).sphereParam ε' w))
      (by rw [hs₂, hflow]; exact hgz) (by rw [← hL']; exact hLg w hw)
    refine ⟨z', ?_, hz'u, hz'v⟩
    rw [hL', ← hTs, hs₂, hflow]
  have hU : IsOpen (D.sardDom p hq ε c ε hp) := isOpen_sardDom hε.le hRq2
  have hzero : ∀ w : Fin (D.chart q hq).k → ℝ,
      (w ∈ D.sardDom p hq ε c ε hp ∧ D.sardMap p hq ε c ε hp w = 0) ↔
        (w ∘ Fin.cast hkq ∈ D'.sardDom p hq ε' c' ε' hp ∧
          D'.sardMap p hq ε' c' ε' hp (w ∘ Fin.cast hkq) = 0) := by
    intro w
    simp only [sardDom, sardMap, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hw0, hwL⟩, hJ⟩
      obtain ⟨z', hz'L, hz'u, hz'v⟩ := hFWD w hw0 hwL hJ
      have hz'n : morseNorm n z' ^ 2 = 2 * ε' := by
        rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
          (D.chart p hp).hk, hz'u, hz'v, norm_zero]
        ring
      have hz'R : morseNorm n z' < (D'.chart p hp).R :=
        lt_of_pow_lt_pow_left₀ 2 (D'.chart p hp).R_pos.le (by rw [hz'n]; linarith only [hrmp', hRp2', hε'])
      refine ⟨⟨(hcast0 w).2 hw0, ?_⟩, ?_⟩
      · rw [hz'L, hχp]
        exact ⟨z', hz'R, rfl⟩
      · rw [hz'L, hχp, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc z'
          (lt_of_pow_lt_pow_left₀ 2 (D.chart p hp).R_pos.le (by rw [hz'n]; linarith only [hεε', hrmp, hRp2, hε'])).le)]
        have := (Gpart _ _ hkp (D'.chart p hp).hk (D.chart p hp).hk z').2.2.1.2 hz'u
        simp [ModelField.scaledNegativePart, this]
    · rintro ⟨⟨hw'0, hL'mem⟩, hJ'⟩
      have hw0 : w ≠ 0 := (hcast0 w).1 hw'0
      obtain ⟨y', hy'R, hy'L⟩ := hL'mem
      have hsy' : (D'.chart p hp).χ.symm (D'.landing p hq ε' c' ε' (w ∘ Fin.cast hkq)) = y' := by
        rw [← hy'L, (D'.chart p hp).χ.left_inv ((D'.chart p hp).hsrc _ hy'R.le)]
      have hgy := (D'.chart p hp).hnorm y' hy'R.le
      obtain ⟨hn1, hn2, hn3, hn4, -⟩ := Gpart _ _ hkp (D'.chart p hp).hk (D.chart p hp).hk y'
      rw [hy'L, hLg w hw0,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hn1, hn2] at hgy
      have hv : posPart (D.chart p hp).hk y' ≠ 0 := by
        intro h
        rw [h, norm_zero] at hgy
        nlinarith only [hgy, hε', sq_nonneg ‖negPart (D.chart p hp).hk y'‖]
      have hv' : posPart (D'.chart p hp).hk y' ≠ 0 := fun h => hv (hn4.1 h)
      have hu' : negPart (D'.chart p hp).hk y' = 0 :=
        (ModelField.scaledNegativePart_eq_zero_iff _ hv').1 (by rw [← hsy']; exact hJ')
      have hu : negPart (D.chart p hp).hk y' = 0 := hn3.1 hu'
      rw [hu, norm_zero] at hgy
      obtain ⟨τ, hτ⟩ := hOR' w hw0
      have hτ' : D.flow τ (D.landing p hq ε c ε w) = (D.chart p hp).χ y' := by
        rw [hτ, ← hy'L, hχp]
      obtain ⟨hmemL, hJeq⟩ := hCORE y' _ τ (by rw [hu, norm_zero]; nlinarith only [hrmp, hε]) hv
        (by rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hu,
          norm_zero]; nlinarith only [hgy, hεε']) (hLf w hw0) hτ'
      refine ⟨⟨hw0, image_mono (fun z (hz : morseNorm n z < D.rm p hp) => lt_of_lt_of_le hz hRp)
        hmemL⟩, ?_⟩
      rw [hJeq]
      simp [ModelField.scaledNegativePart, hu]
  have hloc : ∀ w ∈ D.sardDom p hq ε c ε hp, D.sardMap p hq ε c ε hp w = 0 →
      ∀ᶠ v in 𝓝 w, v ∘ Fin.cast hkq ∈ D'.sardDom p hq ε' c' ε' hp ∧
        ∀ j, (D'.sardMap p hq ε' c' ε' hp (v ∘ Fin.cast hkq)).ofLp j =
          (D.sardMap p hq ε c ε hp v).ofLp (Fin.cast hkp j) := by
    intro w hwU hS
    obtain ⟨hw0, hwL⟩ := hwU
    obtain ⟨z', hz'L, hz'u, hz'v⟩ := hFWD w hw0 hwL hS
    set ρ := min (D.chart p hp).R (D'.chart p hp).R with hρ
    set W₀ : Set (Fin n → ℝ) := {y | morseNorm n y < ρ ∧
      2 * ε + 2 * ‖negPart (D.chart p hp).hk y‖ ^ 2 < D.rm p hp ^ 2 ∧
        posPart (D.chart p hp).hk y ≠ 0} with hW₀
    have hW₀o : IsOpen W₀ := by
      have hc : Continuous fun y : Fin n → ℝ => 2 * ε + 2 * ‖negPart (D.chart p hp).hk y‖ ^ 2 :=
        continuous_const.add (continuous_const.mul ((D.chart p hp).continuous_negPart.norm.pow 2))
      have h := (isOpen_morseNorm_lt ρ).inter ((isOpen_lt hc
        (continuous_const : Continuous fun _ : Fin n → ℝ => D.rm p hp ^ 2)).inter
        (isOpen_ne_fun (D.chart p hp).continuous_posPart (continuous_const :
          Continuous fun _ : Fin n → ℝ => (0 : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k))))))
      exact h
    have hW₀s : W₀ ⊆ (D.chart p hp).χ.source := fun y hy =>
      (D.chart p hp).hsrc y (hy.1.le.trans (min_le_left _ _))
    have hWo : IsOpen ((D.chart p hp).χ '' W₀) :=
      ((D.chart p hp).χ.isOpen_image_iff_of_subset_source hW₀s).2 hW₀o
    have hz'n : morseNorm n z' ^ 2 = 2 * ε' := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (D.chart p hp).hk, hz'u, hz'v, norm_zero]
      ring
    have hz'W : z' ∈ W₀ := by
      refine ⟨lt_min ?_ ?_, ?_, ?_⟩
      · exact lt_of_pow_lt_pow_left₀ 2 (D.chart p hp).R_pos.le (by rw [hz'n]; linarith only [hεε', hrmp, hRp2, hε'])
      · exact lt_of_pow_lt_pow_left₀ 2 (D'.chart p hp).R_pos.le (by rw [hz'n]; linarith only [hrmp', hRp2', hε'])
      · rw [hz'u, norm_zero]; nlinarith only [hrmp, hε]
      · intro h
        rw [h, norm_zero] at hz'v
        nlinarith only [hz'v, hε']
    have hw'0 : w ∘ Fin.cast hkq ≠ 0 := (hcast0 w).2 hw0
    have hFc : ContinuousAt (fun v : Fin (D.chart q hq).k → ℝ =>
        D'.landing p hq ε' c' ε' (v ∘ Fin.cast hkq)) w := by
      have h1 : ContinuousAt (D'.landing p hq ε' c' ε') (w ∘ Fin.cast hkq) :=
        (continuousOn_landing (D := D') hε'.le hRq2').continuousAt (isOpen_ne.mem_nhds hw'0)
      have h2 : Continuous (fun v : Fin (D.chart q hq).k → ℝ => v ∘ Fin.cast hkq) :=
        continuous_pi fun i => continuous_apply (Fin.cast hkq i)
      exact h1.comp (f := fun v : Fin (D.chart q hq).k → ℝ => v ∘ Fin.cast hkq) h2.continuousAt
    filter_upwards [hFc.preimage_mem_nhds (hWo.mem_nhds ⟨z', hz'W, hz'L.symm⟩),
      isOpen_ne.mem_nhds hw0] with v hvW hv0
    obtain ⟨y', hy'W, hy'L⟩ := hvW
    have hy'L' : D'.landing p hq ε' c' ε' (v ∘ Fin.cast hkq) = (D.chart p hp).χ y' := hy'L.symm
    have hv'0 : v ∘ Fin.cast hkq ≠ 0 := (hcast0 v).2 hv0
    refine ⟨⟨hv'0, ?_⟩, ?_⟩
    · change D'.landing p hq ε' c' ε' (v ∘ Fin.cast hkq) ∈
        (D'.chart p hp).χ '' {y | morseNorm n y < (D'.chart p hp).R}
      rw [hy'L', hχp]
      exact ⟨y', lt_of_lt_of_le hy'W.1 (min_le_right _ _), rfl⟩
    · intro j
      obtain ⟨hn1, hn2, -, -, hJc⟩ := Gpart _ _ hkp (D'.chart p hp).hk (D.chart p hp).hk y'
      have hgy := (D'.chart p hp).hnorm y' (hy'W.1.le.trans (min_le_right _ _))
      rw [hχp, ← hy'L', hLg v hv0,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hn1, hn2] at hgy
      obtain ⟨τ, hτ⟩ := hOR' v hv0
      rw [hy'L'] at hτ
      obtain ⟨-, hJeq⟩ := hCORE y' _ τ hy'W.2.1 hy'W.2.2
        (by rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
            linarith only [hgy, hεε'])
        (hLf v hv0) hτ
      change (ModelField.scaledNegativePart (D'.chart p hp).hk ((D'.chart p hp).χ.symm
          (D'.landing p hq ε' c' ε' (v ∘ Fin.cast hkq)))).ofLp j =
        (ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm
          (D.landing p hq ε c ε v))).ofLp (Fin.cast hkp j)
      rw [hy'L', hχp, (D.chart p hp).χ.left_inv (hW₀s hy'W), hJc j, hJeq]
  exact SardData.congr_data hkq hkp hU hzero hloc

theorem sardAgree_of_flow_agree {f : M → ℝ} (D D' : GradientLikeStrip I f a b crit)
    (hchart : ∀ x hx, D'.chart x hx = D.chart x hx) {ε : ℝ} {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hε : 0 < ε) (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (hagree : ∀ y ∈ (D.chart q hq).leftModelSphere ε,
      (D.flow (f q - f p - 2 * ε) ((D.chart q hq).χ y) ∈
          (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R} ∨
        D'.flow (f q - f p - 2 * ε) ((D.chart q hq).χ y) ∈
          (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R}) →
      D'.flow (f q - f p - 2 * ε) ((D.chart q hq).χ y) =
        D.flow (f q - f p - 2 * ε) ((D.chart q hq).χ y))
    (c c' : ℝ) : D.sardAgree D' ε ε c c' p hq hp := by
  have hgenq : ∀ (d d' : MorseNormalChart I f q) (_ : d' = d) (hk : d'.k = d.k)
      (w : Fin d.k → ℝ), d'.χ (d'.sphereParam ε (w ∘ Fin.cast hk)) = d.χ (d.sphereParam ε w) ∧
        (w ∘ Fin.cast hk = 0 ↔ w = 0) := by
    intro d d' h hk w
    subst h
    exact ⟨rfl, Iff.rfl⟩
  have hgenp : ∀ (d d' : MorseNormalChart I f p) (_ : d' = d) (hl : d'.k = d.k) (z : M)
      (j : Fin d'.k), ModelField.scaledNegativePart d'.hk (d'.χ.symm z) j =
        ModelField.scaledNegativePart d.hk (d.χ.symm z) (Fin.cast hl j) := by
    intro d d' h hl z j
    subst h
    rfl
  have hk : (D'.chart q hq).k = (D.chart q hq).k := by rw [hchart]
  have hl : (D'.chart p hp).k = (D.chart p hp).k := by rw [hchart]
  have hland : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → ∀ c₀ c₀' : ℝ,
      (D.landing p hq ε c₀ ε w ∈ (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R} ↔
        D'.landing p hq ε c₀' ε (w ∘ Fin.cast hk) ∈
          (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R}) ∧
      (D.landing p hq ε c₀ ε w ∈ (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R} →
        D'.landing p hq ε c₀' ε (w ∘ Fin.cast hk) = D.landing p hq ε c₀ ε w) := by
    intro w hw c₀ c₀'
    have hx := (hgenq (D.chart q hq) (D'.chart q hq) (hchart q hq) hk w).1
    have hL : D.landing p hq ε c₀ ε w =
        D.flow (f q - f p - 2 * ε) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := by
      unfold landing
      rw [D.flow_flow]
      congr 1
      ring
    have hL' : D'.landing p hq ε c₀' ε (w ∘ Fin.cast hk) =
        D'.flow (f q - f p - 2 * ε) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := by
      unfold landing
      rw [D'.flow_flow, hx]
      congr 1
      ring
    have hy := (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw
    have hag := hagree _ hy
    rw [hL, hL']
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => hag (Or.inl h)⟩
    · rw [hag (Or.inl h)]; exact h
    · rw [← hag (Or.inr h)]; exact h
  have hdom : ∀ w : Fin (D.chart q hq).k → ℝ,
      (w ∈ D.sardDom p hq ε c ε hp ↔ w ∘ Fin.cast hk ∈ D'.sardDom p hq ε c' ε hp) ∧
      (w ∈ D.sardDom p hq ε c ε hp → ∀ j, D'.sardMap p hq ε c' ε hp (w ∘ Fin.cast hk) j =
        D.sardMap p hq ε c ε hp w (Fin.cast hl j)) := by
    intro w
    have hz := (hgenq (D.chart q hq) (D'.chart q hq) (hchart q hq) hk w).2
    have hpc : (D'.chart p hp).χ '' {z | morseNorm n z < (D'.chart p hp).R} =
        (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R} := by rw [hchart]
    by_cases hw : w = 0
    · refine ⟨?_, fun h => absurd hw h.1⟩
      constructor
      · intro h; exact absurd hw h.1
      · intro h; exact absurd (hz.2 hw) h.1
    · obtain ⟨h1, h2⟩ := hland w hw c c'
      have hw' : w ∘ Fin.cast hk ≠ 0 := fun h => hw (hz.1 h)
      refine ⟨?_, ?_⟩
      · change (w ≠ 0 ∧ _) ↔ (w ∘ Fin.cast hk ≠ 0 ∧ _)
        simp only [mem_preimage]
        rw [hpc]
        exact ⟨fun h => ⟨hw', h1.1 h.2⟩, fun h => ⟨hw, h1.2 h.2⟩⟩
      · intro hmem j
        have hmem' : D.landing p hq ε c ε w ∈
            (D.chart p hp).χ '' {z | morseNorm n z < (D.chart p hp).R} := hmem.2
        unfold sardMap
        rw [h2 hmem']
        exact hgenp (D.chart p hp) (D'.chart p hp) (hchart p hp) hl _ j
  have hU : IsOpen (D.sardDom p hq ε c ε hp) := isOpen_sardDom hε.le hεR
  have hSzero : ∀ w ∈ D.sardDom p hq ε c ε hp,
      (D'.sardMap p hq ε c' ε hp (w ∘ Fin.cast hk) = 0 ↔ D.sardMap p hq ε c ε hp w = 0) := by
    intro w hw
    have h := (hdom w).2 hw
    constructor
    · intro h0
      ext i
      have := h (Fin.cast hl.symm i)
      rw [h0] at this
      simpa using this.symm
    · intro h0
      ext j
      rw [h j, h0]
      rfl
  exact SardData.congr_data hk hl hU
    (fun w => ⟨fun h => ⟨(hdom w).1.1 h.1, (hSzero w h.1).2 h.2⟩,
      fun h => ⟨(hdom w).1.2 h.1, (hSzero w ((hdom w).1.2 h.1)).1 h.2⟩⟩)
    (fun w hw _ => Filter.mem_of_superset (hU.mem_nhds hw)
      (fun v hv => ⟨(hdom v).1.1 hv, (hdom v).2 hv⟩))

omit [I.Boundaryless] in
theorem exists_shrink_field {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {ε₁ ρ : ℝ} (hε₁ : 0 < ε₁) (hρ0 : 0 < ρ)
    (hρ : 8 * ε₁ < ρ ^ 2) (hrm : ∀ x hx, 8 * ε₁ < D.rm x hx ^ 2) :
    ∃ D' : GradientLikeStrip I f a b crit, D'.isRescaleOf D ∧
      (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
        (D'.chart x hx).R = (D.chart x hx).R ∧ (D'.chart x hx).R' = (D.chart x hx).R' ∧
        (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
      (∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ D'.rm x hx = min ρ (D.rm x hx)) ∧
      ∀ x, (∀ y hy, x ∉ (D.chart y hy).χ '' {z | morseNorm n z < (D.chart y hy).r₀}) →
        D'.V x = D.V x := by
  classical
  have _ := hrm
  have key : ∀ S : Finset M, S ⊆ crit → ∃ D₁ : GradientLikeStrip I f a b crit,
      D₁.isRescaleOf D ∧
      (∀ x hx, (D₁.chart x hx).χ = (D.chart x hx).χ ∧ (D₁.chart x hx).k = (D.chart x hx).k ∧
        (D₁.chart x hx).R = (D.chart x hx).R ∧ (D₁.chart x hx).R' = (D.chart x hx).R' ∧
        (D₁.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
      (∀ x hx, x ∈ S → (D₁.chart x hx).r₀ ^ 2 < 2 * ε₁) ∧
      (∀ x hx, D₁.rm x hx = D.rm x hx) ∧
      ∀ x, (∀ y hy, x ∉ (D.chart y hy).χ '' {z | morseNorm n z < (D.chart y hy).r₀}) →
        D₁.V x = D.V x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨D, ⟨fun _ => 1, continuous_const, ⟨1, 1, one_pos, fun _ => ⟨le_rfl, le_rfl⟩⟩,
        fun x => (one_smul ℝ _).symm⟩, fun x hx => ⟨rfl, rfl, rfl, rfl, le_rfl⟩,
        fun x hx h => absurd h (Finset.notMem_empty x), fun _ _ => rfl, fun _ _ => rfl⟩
    | insert p S hpS ih =>
      intro hsub
      have hp : p ∈ crit := hsub (Finset.mem_insert_self p S)
      obtain ⟨D₁, ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩, hch, hS, hrm₁, hV₁⟩ :=
        ih ((Finset.subset_insert p S).trans hsub)
      have hr₀ : 0 < (D₁.chart p hp).r₀ := (D₁.chart p hp).hr₀
      have hr : 0 < min (D₁.chart p hp).r₀ (Real.sqrt ε₁) := lt_min hr₀ (Real.sqrt_pos.2 hε₁)
      have hle : min (D₁.chart p hp).r₀ (Real.sqrt ε₁) ≤ (D₁.chart p hp).r₀ := min_le_left _ _
      have hr2 : min (D₁.chart p hp).r₀ (Real.sqrt ε₁) ^ 2 < 2 * ε₁ := by
        have h1 : min (D₁.chart p hp).r₀ (Real.sqrt ε₁) ≤ Real.sqrt ε₁ := min_le_right _ _
        have h2 := pow_le_pow_left₀ hr.le h1 2
        rw [Real.sq_sqrt hε₁.le] at h2
        linarith
      let g : (Fin n → ℝ) → ℝ := fun y =>
        ModelField.theta (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y /
          ModelField.theta (D₁.chart p hp).r₀ y
      let h : (Fin n → ℝ) → ℝ := fun y => g y - 1
      have hgc : ContDiff ℝ ∞ g :=
        (ModelField.contDiff_theta hr).div (ModelField.contDiff_theta hr₀)
          fun y => (ModelField.theta_pos hr₀ y).ne'
      have hhc : ContDiff ℝ ∞ h := hgc.sub contDiff_const
      have hgpos : ∀ y, 0 < g y := fun y =>
        div_pos (ModelField.theta_pos hr y) (ModelField.theta_pos hr₀ y)
      have hh0 : ∀ y, (D₁.chart p hp).r₀ / 2 ≤ morseNorm n y → h y = 0 := by
        intro y hy
        have ht : ModelField.theta (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y =
            ModelField.theta (D₁.chart p hp).r₀ y := by
          rw [ModelField.theta_eq hr (by linarith), ModelField.theta_eq hr₀ hy]
        change g y - 1 = 0
        simp only [g]
        rw [ht, div_self (ModelField.theta_pos hr₀ y).ne', sub_self]
      set K : Set (Fin n → ℝ) := {y | morseNorm n y ≤ (D₁.chart p hp).r₀ / 2} with hKdef
      have hKc : IsCompact K := isCompact_morseNorm_le _
      have hKb : K ⊆ Metric.ball 0 (D₁.chart p hp).R' := half_r₀_ball_subset (D := D₁)
      have hhK : ∀ y ∉ K, h y = 0 := fun y hy => hh0 y (le_of_lt (not_le.1 hy))
      have h0K : (0 : Fin n → ℝ) ∈ K := by
        change morseNorm n 0 ≤ _
        rw [morseNorm_zero]; linarith
      obtain ⟨y₁, -, hy₁⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hgc.continuous.continuousOn
      obtain ⟨y₂, -, hy₂⟩ := hKc.exists_isMaxOn ⟨0, h0K⟩ hgc.continuous.continuousOn
      let ψ : M → ℝ := fun x => 1 + (D₁.chart p hp).pushFun h x
      have hψc : Continuous ψ :=
        continuous_const.add (MorseNormalChart.contMDiff_pushFun hhc hKc hKb hhK).continuous
      have hψb : ∀ x, min 1 (g y₁) ≤ ψ x ∧ ψ x ≤ max 1 (g y₂) := by
        intro x
        by_cases hx : x ∈ (D₁.chart p hp).χ '' K
        · obtain ⟨y, hyK, rfl⟩ := hx
          have hψy : ψ ((D₁.chart p hp).χ y) = g y := by
            change 1 + (D₁.chart p hp).pushFun h ((D₁.chart p hp).χ y) = g y
            rw [MorseNormalChart.pushFun_apply_chart h (hKb hyK)]
            change 1 + (g y - 1) = g y
            ring
          rw [hψy]
          exact ⟨(min_le_right _ _).trans (hy₁ hyK), (hy₂ hyK).trans (le_max_right _ _)⟩
        · have hψx : ψ x = 1 := by
            change 1 + (D₁.chart p hp).pushFun h x = 1
            rw [MorseNormalChart.pushFun_eq_zero_of_notMem_image hhK hx, add_zero]
          rw [hψx]
          exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hψV : ∀ x, shrunkV (D := D₁) p hp (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) x =
          ψ x • D₁.V x := by
        intro x
        by_cases hx : x ∈ (D₁.chart p hp).χ '' K
        · obtain ⟨y, hyK, rfl⟩ := hx
          have hyB : y ∈ Metric.ball (0 : Fin n → ℝ) (D₁.chart p hp).R' := hKb hyK
          have hxB : (D₁.chart p hp).χ y ∈
              (D₁.chart p hp).χ '' Metric.ball 0 (D₁.chart p hp).R' := mem_image_of_mem _ hyB
          have hyrm : morseNorm n y < D₁.rm p hp :=
            lt_of_le_of_lt (show morseNorm n y ≤ _ from hyK) (half_r₀_lt_rm (D := D₁))
          have hmod := D₁.model p hp y hyrm
          have hshr : shrinkY (D := D₁) p hp (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y =
              h y • ModelField.modelField (D₁.chart p hp).k (D₁.chart p hp).r₀ y := by
            have := (ModelField.theta_pos hr₀ y).ne'
            have e : (g y - 1) * ModelField.theta (D₁.chart p hp).r₀ y =
                ModelField.theta (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y -
                  ModelField.theta (D₁.chart p hp).r₀ y := by
              simp only [g]
              field_simp
            change ModelField.theta (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y •
                ModelField.modelDesc (D₁.chart p hp).k y -
              ModelField.theta (D₁.chart p hp).r₀ y • ModelField.modelDesc (D₁.chart p hp).k y =
              (g y - 1) • (ModelField.theta (D₁.chart p hp).r₀ y •
                ModelField.modelDesc (D₁.chart p hp).k y)
            rw [smul_smul, e, sub_smul]
          have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) ((D₁.chart p hp).χ y)
            ((D₁.chart p hp).mdifferentiableAt_chart ((D₁.chart p hp).symm_mem_ball hxB))
            ((D₁.chart p hp).mdifferentiableAt_symm hxB)
          have hev : ((D₁.chart p hp).χ ∘ (D₁.chart p hp).χ.symm) =ᶠ[𝓝 ((D₁.chart p hp).χ y)]
              id :=
            eventuallyEq_of_mem ((D₁.chart p hp).isOpen_image_ball.mem_nhds hxB)
              fun x hx => (D₁.chart p hp).symm_image_eq hx
          have h1 := hev.mfderiv_eq (I := I) (I' := I)
          rw [mfderiv_id] at h1
          have h2 := DFunLike.congr_fun (hcomp.symm.trans h1) (D₁.V ((D₁.chart p hp).χ y))
          have hleft : (D₁.chart p hp).χ.symm ((D₁.chart p hp).χ y) = y :=
            (D₁.chart p hp).χ.left_inv ((D₁.chart p hp).hball hyB)
          have key2 : ∀ z, z = y →
              (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D₁.chart p hp).χ z)
                ((mfderiv I 𝓘(ℝ, Fin n → ℝ) (D₁.chart p hp).χ.symm ((D₁.chart p hp).χ y))
                  (D₁.V ((D₁.chart p hp).χ y))) =
              (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D₁.chart p hp).χ y)
                ((mfderiv I 𝓘(ℝ, Fin n → ℝ) (D₁.chart p hp).χ.symm ((D₁.chart p hp).χ y))
                  (D₁.V ((D₁.chart p hp).χ y))) := by
            rintro z rfl; rfl
          have h3 := (key2 _ hleft).symm.trans h2
          have hpush : (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D₁.chart p hp).χ y)
              (shrinkY (D := D₁) p hp (min (D₁.chart p hp).r₀ (Real.sqrt ε₁)) y) =
              h y • D₁.V ((D₁.chart p hp).χ y) := by
            rw [hshr]
            calc (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D₁.chart p hp).χ y)
                  (h y • ModelField.modelField (D₁.chart p hp).k (D₁.chart p hp).r₀ y)
                = h y • (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D₁.chart p hp).χ y)
                    (ModelField.modelField (D₁.chart p hp).k (D₁.chart p hp).r₀ y) :=
                  ContinuousLinearMap.map_smul _ _ _
              _ = h y • D₁.V ((D₁.chart p hp).χ y) := by rw [← hmod, h3]; rfl
          rw [shrunkV, addPush_apply, MorseNormalChart.push_apply_chart _ hyB, hpush]
          change D₁.V ((D₁.chart p hp).χ y) + h y • D₁.V ((D₁.chart p hp).χ y) =
            (1 + (D₁.chart p hp).pushFun h ((D₁.chart p hp).χ y)) • D₁.V ((D₁.chart p hp).χ y)
          rw [MorseNormalChart.pushFun_apply_chart h hyB, add_smul, one_smul]
        · rw [shrunkV_of_notMem_image hr hle hx]
          have hψx : ψ x = 1 := by
            change 1 + (D₁.chart p hp).pushFun h x = 1
            rw [MorseNormalChart.pushFun_eq_zero_of_notMem_image hhK hx, add_zero]
          rw [hψx, one_smul]
      have hm₂ : 0 < min 1 (g y₁) := lt_min one_pos (hgpos y₁)
      have hM₂ : 0 < max 1 (g y₂) := one_pos.trans_le (le_max_left _ _)
      have hψpos : ∀ x, 0 < ψ x := fun x => hm₂.trans_le (hψb x).1
      refine ⟨shrinkAt (D := D₁) hf hr hle, ⟨fun x => φ x / ψ x,
        hφc.div hψc fun x => (hψpos x).ne',
        ⟨m / max 1 (g y₂), M₀ / min 1 (g y₁), div_pos hm hM₂, fun x => ⟨?_, ?_⟩⟩, fun x => ?_⟩,
        fun x hx => ?_, fun x hx hxS => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact div_le_div₀ (hm.le.trans (hφb x).1) (hφb x).1 (hψpos x) (hψb x).2
      · exact div_le_div₀ (hm.le.trans ((hφb x).1.trans (hφb x).2)) (hφb x).2 hm₂ (hψb x).1
      · rw [hφV x, shrinkAt_V, hψV x, smul_smul, div_mul_cancel₀ _ (hψpos x).ne']
      · obtain ⟨e1, e2, e3, e4, e5⟩ := hch x hx
        refine ⟨by rw [shrinkAt_chart_χ]; exact e1, by rw [shrinkAt_chart_k]; exact e2,
          by rw [shrinkAt_chart_R]; exact e3, by rw [shrinkAt_chart_R']; exact e4, ?_⟩
        by_cases hxp : x = p
        · subst hxp
          rw [shrinkAt_chart_r₀_self hf hr hle]
          exact hle.trans e5
        · rw [shrinkAt_chart_r₀_of_ne hf hr hle hx hxp]
          exact e5
      · by_cases hxp : x = p
        · subst hxp
          rw [shrinkAt_chart_r₀_self hf hr hle]
          exact hr2
        · rw [shrinkAt_chart_r₀_of_ne hf hr hle hx hxp]
          exact hS x hx (Finset.mem_of_mem_insert_of_ne hxS hxp)
      · rw [shrinkAt_rm]; exact hrm₁ x hx
      · have hx' : x ∉ (D₁.chart p hp).χ '' K := by
          rintro ⟨y, hy, rfl⟩
          refine hx p hp ⟨y, ?_, by rw [(hch p hp).1]⟩
          change morseNorm n y < (D.chart p hp).r₀
          have hy' : morseNorm n y ≤ (D₁.chart p hp).r₀ / 2 := hy
          linarith [(hch p hp).2.2.2.2]
        rw [shrinkAt_V, shrunkV_of_notMem_image hr hle hx']
        exact hV₁ x hx
  obtain ⟨D₁, hresc, hch, hS, hrm₁, hV₁⟩ := key crit le_rfl
  have hr₀ρ : ∀ x hx, 2 * (D₁.chart x hx).r₀ < ρ := by
    intro x hx
    have h1 := hS x hx hx
    have h2 := (D₁.chart x hx).hr₀
    nlinarith
  refine ⟨{ D₁ with
      rm := fun x hx => min ρ (D.rm x hx)
      hrm := fun x hx => ⟨lt_min (hr₀ρ x hx) (by rw [← hrm₁ x hx]; exact (D₁.hrm x hx).1),
        (min_le_right _ _).trans (by rw [← hrm₁ x hx]; exact (D₁.hrm x hx).2)⟩
      model := fun x hx y hy => D₁.model x hx y
        (lt_of_lt_of_le hy (by rw [hrm₁ x hx]; exact min_le_right _ _)) },
    hresc, hch, fun x hx => ⟨hS x hx hx, rfl⟩, hV₁⟩

theorem noCommon.of_rescale {f g : M → ℝ} {D : GradientLikeStrip I f a b crit}
    {D' : GradientLikeStrip I g a b crit} (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ) {x : M} {hx : x ∈ crit} {y : M}
    {hy : y ∈ crit} {rx ry : ℝ} (h : D.noCommon x hx y hy rx ry) : D'.noCommon x hx y hy rx ry := by
  obtain ⟨φ, hφ, ⟨m, M₀, hm, hφb⟩, hV⟩ := hresc
  intro z hz s hs
  rw [hχ x hx] at hz
  rw [hχ y hy] at hs
  obtain ⟨t, ht⟩ := (exists_flow_mem_iff D' D hφ hm hφb hV z
    ((D.chart y hy).χ '' {w | morseNorm n w < ry})).2 ⟨s, hs⟩
  exact h z hz t ht

theorem leftSphereMap_eq_of_rescale {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {q : M} (hq : q ∈ crit) {μ : ℕ} (hμ : (D.chart q hq).k = μ) {ε ε' t : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hrm : 2 * ε < D.rm q hq ^ 2) (hrm' : 2 * ε' < D'.rm q hq ^ 2) (hat : a ≤ t)
    (ht : t < f q - ε) (ht' : t < g q - ε')
    (hU : ∀ y, f y ∈ Icc t (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hU' : ∀ y, g y ∈ Icc t (g q - ε') → ∀ x hx, y ∉ D'.smallBall x hx)
    (hlev : ∀ y, f y = t ↔ g y = t) :
    ∀ y : EuclideanSpace ℝ (Fin μ), y ≠ 0 →
      D'.leftSphereMap q μ ε' t y = D.leftSphereMap q μ ε t y := by
  intro y hy
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hV⟩ := hresc
  have hA : ∀ k₁ : ℕ, k₁ = μ → (Handle.reidx y : Fin k₁ → ℝ) ≠ 0 := by
    rintro k₁ rfl h
    apply hy
    ext j
    have := congrFun h j
    simpa [Handle.reidx] using this
  have hB : ∀ (F : M → ℝ) (c : MorseNormalChart I F q) (w : Fin c.k → ℝ) (δ : ℝ),
      c.sphereParam δ w =
        recombine c.hk (Real.sqrt (2 * δ) • (‖c.toE w‖⁻¹ • c.toE w)) 0 := by
    intro F c w δ
    unfold MorseNormalChart.sphereParam
    rw [smul_smul, div_eq_mul_inv]
  have hnorm1 : ∀ (F : M → ℝ) (c : MorseNormalChart I F q) (w : Fin c.k → ℝ), w ≠ 0 →
      ‖‖c.toE w‖⁻¹ • c.toE w‖ = 1 := by
    intro F c w hw
    have h : ‖c.toE w‖ ≠ 0 := norm_ne_zero_iff.2 (c.toE_ne_zero hw)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
  have hG : ∀ (k₁ k₂ : ℕ) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ → ∀ δ : ℝ,
      recombine h₁ ((Real.sqrt (2 * δ) /
          ‖(EuclideanSpace.equiv (Fin k₁) ℝ).symm (Handle.reidx y)‖) •
          (EuclideanSpace.equiv (Fin k₁) ℝ).symm (Handle.reidx y)) 0 =
        recombine h₂ ((Real.sqrt (2 * δ) /
          ‖(EuclideanSpace.equiv (Fin k₂) ℝ).symm (Handle.reidx y)‖) •
          (EuclideanSpace.equiv (Fin k₂) ℝ).symm (Handle.reidx y)) 0 := by
    rintro k₁ k₂ h₁ h₂ rfl δ
    rfl
  set d := D.chart q hq with hd
  set d' := D'.chart q hq with hd'
  have hχq := (hχ q hq).1
  have hkq := (hχ q hq).2
  have hC : ∀ δ : ℝ, d'.sphereParam δ (Handle.reidx y) = d.sphereParam δ (Handle.reidx y) :=
    fun δ => hG _ _ _ _ hkq δ
  have hw : (Handle.reidx y : Fin d.k → ℝ) ≠ 0 := hA _ hμ
  have hw' : (Handle.reidx y : Fin d'.k → ℝ) ≠ 0 := hA _ (hkq.trans hμ)
  set x₀ := d.χ (d.sphereParam ε (Handle.reidx y)) with hx₀
  set x₀' := d.χ (d.sphereParam ε' (Handle.reidx y)) with hx₀'
  have hx₀'' : d'.χ (d'.sphereParam ε' (Handle.reidx y)) = x₀' := by
    rw [hC, hχq]
  have hfq : f q ∈ Ioo a b := D.inStrip q hq d.p_mem_image_ball
  have hgq : g q ∈ Ioo a b := D'.inStrip q hq d'.p_mem_image_ball
  have hrmpos := D.rm_pos q hq
  have hrmpos' := D'.rm_pos q hq
  have hεR : 2 * ε ≤ d.R ^ 2 := by
    have := (D.hrm q hq).2
    nlinarith
  have hεR' : 2 * ε' ≤ d'.R ^ 2 := by
    have := (D'.hrm q hq).2
    nlinarith
  have hsq : Real.sqrt (2 * ε) < D.rm q hq := by
    rw [Real.sqrt_lt' hrmpos]; exact hrm
  have hsq' : Real.sqrt (2 * ε') < D'.rm q hq := by
    rw [Real.sqrt_lt' hrmpos']; exact hrm'
  have hsqpos : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
  have hsqpos' : 0 < Real.sqrt (2 * ε') := Real.sqrt_pos.2 (by linarith)
  have horbit : ∃ τ : ℝ, x₀' = D.flow τ x₀ := by
    rcases le_total ε' ε with hle | hle
    · obtain ⟨s, -, hs⟩ := (CrossField.flow_ray_unstable D hf hq (hnorm1 f d _ hw) hsqpos
        hsq).2 (Real.sqrt (2 * ε')) ⟨hsqpos', Real.sqrt_le_sqrt (by linarith)⟩
      refine ⟨-s, ?_⟩
      rw [hx₀, hx₀', hB f d, hB f d, hs]
    · obtain ⟨s, -, hs⟩ := (CrossField.flow_ray_unstable D' hg hq (hnorm1 g d' _ hw')
        hsqpos' hsq').2 (Real.sqrt (2 * ε)) ⟨hsqpos, Real.sqrt_le_sqrt (by linarith)⟩
      rw [← hB g d', ← hB g d', hx₀'', hC, hχq] at hs
      obtain ⟨σ, -, -, hσs, hσ⟩ := exists_reparam D' D hφc hm hφb hV x₀'
      obtain ⟨u, hu⟩ := hσs (-s)
      rw [← hu, ← hσ] at hs
      refine ⟨-u, ?_⟩
      have h2 := congrArg (D.flow (-u)) hs
      rw [flow_neg_flow] at h2
      exact h2
  obtain ⟨τ, hτ⟩ := horbit
  have htab : t ∈ Icc a b := ⟨hat, by linarith [hfq.2]⟩
  have htab' : t ∈ Icc a b := ⟨hat, by linarith [hgq.2]⟩
  have hlevD : f (D.flow (f q - ε - t) x₀) = t := by
    have := D.leftSphere_subset_level hf q hq hεR htab (by
      intro z hz
      rw [uIcc_of_ge (by linarith)] at hz
      exact hU z hz) ⟨x₀, ⟨_, d.sphereParam_mem_leftModelSphere hε.le hw, rfl⟩, rfl⟩
    exact this
  have hlevD' : g (D'.flow (g q - ε' - t) x₀') = t := by
    have := D'.leftSphere_subset_level hg q hq hεR' htab' (by
      intro z hz
      rw [uIcc_of_ge (by linarith)] at hz
      exact hU' z hz) ⟨x₀', ⟨_, d'.sphereParam_mem_leftModelSphere hε'.le hw', hx₀''⟩, rfl⟩
    exact this
  obtain ⟨σ, -, -, hσs, hσ⟩ := exists_reparam D' D hφc hm hφb hV x₀'
  obtain ⟨u, hu⟩ := hσs (g q - ε' - t)
  have hcU : ∀ z, f z = t → dfV I f D.V z = -1 := by
    intro z hz
    exact D.dfV_eq_neg_one_of_mem_unitRegion
      ⟨hz ▸ htab, fun p hp => hU z (by rw [hz]; exact ⟨le_rfl, ht.le⟩) p hp⟩
  have hl2 : f (D.flow (τ + u) x₀) = t := by
    rw [← flow_flow, ← hτ, hσ, hu]
    exact (hlev _).2 hlevD'
  have heq := flow_level_unique hf hcU hl2 hlevD
  change D'.leftSphereMap q μ ε' t y = D.leftSphereMap q μ ε t y
  rw [leftSphereMap, leftSphereMap]
  simp only [hq, ↓reduceDIte]
  rw [← hd, ← hd', hx₀'', ← hx₀, ← hu, ← hσ,
    ← heq, ← flow_flow, ← hτ]

theorem leftSphere_eq_of_rescale {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {q : M} (hq : q ∈ crit) {ε ε' t : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (hrm : 2 * ε < D.rm q hq ^ 2) (hrm' : 2 * ε' < D'.rm q hq ^ 2) (hat : a ≤ t)
    (ht : t < f q - ε) (ht' : t < g q - ε')
    (hU : ∀ y, f y ∈ Icc t (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hU' : ∀ y, g y ∈ Icc t (g q - ε') → ∀ x hx, y ∉ D'.smallBall x hx)
    (hlev : ∀ y, f y = t ↔ g y = t) :
    D'.leftSphere q hq ε' t = D.leftSphere q hq ε t := by
  have key : ∀ {f₀ : M → ℝ} (D₀ : GradientLikeStrip I f₀ a b crit) {ε₀ : ℝ}, 0 < ε₀ →
      (D₀.chart q hq).k = (D.chart q hq).k →
      D₀.leftSphere q hq ε₀ t =
        (fun y => D₀.leftSphereMap q (D.chart q hq).k ε₀ t y) '' {y | y ≠ 0} := by
    intro f₀ D₀ ε₀ hε₀ hk
    ext x
    simp only [leftSphere, leftSphereMap, hq, ↓reduceDIte, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z', ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨hw, hzw⟩ := (D₀.chart q hq).sphereParam_of_mem hε₀ hz
      set w : Fin (D₀.chart q hq).k → ℝ :=
        (EuclideanSpace.equiv (Fin (D₀.chart q hq).k) ℝ) (negPart (D₀.chart q hq).hk z) with hwdef
      let y : EuclideanSpace ℝ (Fin (D.chart q hq).k) :=
        (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).symm
          (fun j => if h : (j : ℕ) < (D₀.chart q hq).k then w ⟨j, h⟩ else 0)
      have hry : (Handle.reidx y : Fin (D₀.chart q hq).k → ℝ) = w := by
        funext i
        have hi : (i : ℕ) < (D.chart q hq).k := hk ▸ i.isLt
        simp [Handle.reidx, y, hi]
      refine ⟨y, ?_, ?_⟩
      · intro hy0
        apply hw
        rw [← hry, hy0]
        funext i
        simp [Handle.reidx]
      · rw [hry, hzw]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨_, ⟨_, (D₀.chart q hq).sphereParam_mem_leftModelSphere hε₀.le ?_, rfl⟩, rfl⟩
      intro h0
      apply hy
      ext j
      have hj : (j : ℕ) < (D₀.chart q hq).k := hk.symm ▸ j.isLt
      have := congrFun h0 ⟨j, hj⟩
      simpa [Handle.reidx] using this
  rw [key D' hε' ((hχ q hq).2), key D hε rfl]
  refine Set.image_congr ?_
  intro y hy
  exact leftSphereMap_eq_of_rescale hf hg D D' hresc hχ hq rfl hε hε' hrm hrm' hat ht ht' hU hU'
    hlev y hy

theorem rightSphere_eq_of_rescale {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {p : M} (hp : p ∈ crit) {ε ε' t : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (hrm : 2 * ε < D.rm p hp ^ 2) (hrm' : 2 * ε' < D'.rm p hp ^ 2) (htb : t ≤ b)
    (ht : f p + ε < t) (ht' : g p + ε' < t)
    (hU : ∀ y, f y ∈ Icc (f p + ε) t → ∀ x hx, y ∉ D.smallBall x hx)
    (hU' : ∀ y, g y ∈ Icc (g p + ε') t → ∀ x hx, y ∉ D'.smallBall x hx)
    (hlev : ∀ y, f y = t ↔ g y = t) :
    D'.rightSphere p hp ε' t = D.rightSphere p hp ε t := by
  have charac : ∀ (h : M → ℝ) (E : GradientLikeStrip I h a b crit) (δ : ℝ),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ h → 0 < δ → 2 * δ < E.rm p hp ^ 2 → h p + δ < t →
      (∀ y, h y ∈ Icc (h p + δ) t → ∀ x hx, y ∉ E.smallBall x hx) →
      ∀ x, (x ∈ E.rightSphere p hp δ t ↔ h x = t ∧ x ∈ E.captured p hp) := by
    intro h E δ hh hδ hδrm hδt hUE x
    have hR : 2 * δ ≤ (E.chart p hp).R ^ 2 := by
      have h1 := (E.hrm p hp).2
      have h2 := E.rm_pos p hp
      nlinarith
    have hpS : h p ∈ Ioo a b :=
      E.inStrip p hp ⟨0, (E.chart p hp).zero_mem_ball, (E.chart p hp).hχ0⟩
    have htab : t ∈ Icc a b := ⟨by linarith [hpS.1], htb⟩
    have hsqrt : Real.sqrt (2 * δ) < E.rm p hp := by
      rw [Real.sqrt_lt' (E.rm_pos p hp)]; exact hδrm
    constructor
    · intro hx
      refine ⟨E.rightSphere_subset_level hh p hp hR htab (by
        intro y hy; rw [uIcc_of_le hδt.le] at hy; exact hUE y hy) hx, ?_⟩
      rw [E.mem_rightSphere_iff p hp δ t] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨t - (h p + δ), y, ⟨?_, hy.1⟩, hyx⟩
      have h1 := (E.chart p hp).morseNorm_sq_of_mem_rightModelSphere hy
      have h2 := ModelField.morseNorm_nonneg y
      have h3 := E.rm_pos p hp
      nlinarith
    · rintro ⟨hxt, hxc⟩
      rw [E.mem_rightSphere_iff p hp δ t]
      set z := E.flow (t - (h p + δ)) x with hz
      have hzlev : h z = h p + δ := by
        have := f_flow_eq_sub_of_levels (D := E) hh (x := x) (T := t - (h p + δ))
          (by rw [hxt]; exact htab)
          (by rw [hxt, sub_sub_cancel]; exact ⟨by linarith [hpS.1], by linarith⟩)
          (by
            intro y hy
            rw [hxt, sub_sub_cancel, uIcc_of_ge hδt.le] at hy
            exact hUE y hy) _ right_mem_uIcc
        rw [hz, this, hxt]; ring
      have hzc : z ∈ E.captured p hp := (E.flow_mem_captured_iff _).2 hxc
      obtain ⟨T₀, hT₀⟩ := (mem_captured_iff_eventually (D := E)).1 hzc
      set T := max T₀ 0 with hT
      have hT0 : 0 ≤ T := le_max_right _ _
      set w := E.flow T z with hw
      set d := E.chart p hp with hd
      set K : Set (Fin n → ℝ) :=
        {y | morseNorm n y ≤ Real.sqrt (2 * δ) ∧ negPart d.hk y = 0} with hK
      set O := d.χ '' {y | morseNorm n y < E.rm p hp} with hO
      have hbound : ∀ s, -T ≤ s → E.flow s w ∈ O →
          negPart d.hk (d.χ.symm (E.flow s w)) = 0 → E.flow s w ∈ d.χ '' K := by
        intro s hs hsO hneg
        obtain ⟨y, hy, hyx⟩ := hsO
        have hy' : morseNorm n y < E.rm p hp := hy
        have hsy : d.χ.symm (E.flow s w) = y := by
          rw [← hyx, d.χ.left_inv (d.hsrc y (hy'.le.trans (E.hrm p hp).2))]
        rw [hsy] at hneg
        refine ⟨y, ⟨?_, hneg⟩, hyx⟩
        have hlev : h (E.flow s w) ≤ h (E.flow (-T) w) := f_flow_antitone (D := E) hh w hs
        rw [hw, E.flow_neg_flow, hzlev, ← hw, ← hyx, d.hnorm y (hy'.le.trans (E.hrm p hp).2),
          DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hneg, norm_zero] at hlev
        have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart d.hk y
        rw [hneg, norm_zero] at h1
        refine MorseNormalChart.morseNorm_le_sqrt_of_sq_le ?_
        nlinarith
      have hw0 : w ∈ d.χ '' K := by
        obtain ⟨y₀, ⟨hy₀1, hy₀2⟩, hy₀x⟩ := hT₀ T (le_max_left _ _)
        have hwO : E.flow 0 w ∈ O := by rw [E.flow_zero]; exact ⟨y₀, hy₀1, hy₀x⟩
        have := hbound 0 (by linarith) hwO (by
          rw [E.flow_zero, hw, ← hy₀x, d.χ.left_inv (d.hsrc y₀ (hy₀1.le.trans (E.hrm p hp).2))]
          exact hy₀2)
        rwa [E.flow_zero] at this
      have hKc : IsCompact (d.χ '' K) :=
        d.isCompact_image_of_subset ((isCompact_morseNorm_le _).of_isClosed_subset
          ((isClosed_morseNorm_le _).inter (isClosed_eq d.continuous_negPart continuous_const))
          fun y hy => hy.1) (hsqrt.trans (E.rm_lt_R' p hp)) fun y hy => hy.1
      have hQc : IsClosed {s : ℝ | E.flow s w ∈ d.χ '' K} :=
        hKc.isClosed.preimage (E.continuous_flow_curve w)
      have hKO : d.χ '' K ⊆ O := image_mono fun y hy => lt_of_le_of_lt hy.1 hsqrt
      have hall : Icc (-T) 0 ⊆ {s : ℝ | E.flow s w ∈ d.χ '' K} := by
        refine Icc_neg_subset_of_isClosed_of_step hQc
          (by change E.flow 0 w ∈ d.χ '' K; rw [E.flow_zero]; exact hw0) ?_
        intro s hs hIcc
        have hsK : E.flow s w ∈ d.χ '' K := hIcc (left_mem_Icc.2 hs.2)
        obtain ⟨δ', hδ', hδO⟩ := E.exists_Icc_flow_mem_open (E.isOpen_modelBall p hp) (hKO hsK)
        refine mem_nhdsLT_iff_exists_Ico_subset.2
          ⟨max (s - δ') (-T), max_lt (by linarith) hs.1, fun s' hs' => ?_⟩
        change E.flow s' w ∈ d.χ '' K
        have hss' : s' ≤ s := hs'.2.le
        have hODE : ∀ u ∈ Icc s' s, E.flow u w ∈ O := fun u hu =>
          hδO u ⟨by linarith [le_max_left (s - δ') (-T), hs'.1, hu.1], by linarith [hu.2]⟩
        have hγ := hasDerivAt_symm_flow_Icc hp hODE
        obtain ⟨y, hy, hyx⟩ := hsK
        have hγs : d.χ.symm (E.flow s w) = y := by
          rw [← hyx, d.χ.left_inv (d.hsrc y (hy.1.trans (hsqrt.le.trans (E.hrm p hp).2)))]
        have hneg := ModelField.negPart_eq_zero_of_right d.hk d.hr₀ hγ
          (by rw [hγs]; exact hy.2) hss' s' (left_mem_Icc.2 hss')
        exact hbound s' ((le_max_right _ _).trans hs'.1) (hODE s' (left_mem_Icc.2 hss')) hneg
      have hzK : z ∈ d.χ '' K := by
        have := hall (left_mem_Icc.2 (by linarith))
        simp only [mem_ofPred_eq] at this
        rwa [hw, E.flow_neg_flow] at this
      obtain ⟨y, hy, hyz⟩ := hzK
      refine ⟨y, ⟨hy.2, ?_⟩, hyz⟩
      have := hzlev
      rw [← hyz, d.hnorm y (hy.1.trans (hsqrt.le.trans (E.hrm p hp).2)), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        hy.2, norm_zero] at this
      norm_num at this
      linarith
  have hkeq : ∀ (k₁ k₂ : ℕ) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ → ∀ y : Fin n → ℝ,
      (negPart h₁ y = 0 ↔ negPart h₂ y = 0) := by
    rintro k₁ k₂ h₁ h₂ rfl y
    exact Iff.rfl
  have hset : ∀ r : ℝ,
      (D'.chart p hp).χ '' {y | morseNorm n y < r ∧ negPart (D'.chart p hp).hk y = 0} =
        (D.chart p hp).χ '' {y | morseNorm n y < r ∧ negPart (D.chart p hp).hk y = 0} := by
    intro r
    rw [(hχ p hp).1]
    congr 1
    ext y
    simp only [mem_ofPred_eq]
    rw [hkeq _ _ (D'.chart p hp).hk (D.chart p hp).hk (hχ p hp).2 y]
  obtain ⟨φ, hφ, ⟨m, M₀, hm, hφb⟩, hV⟩ := hresc
  have hcap : ∀ x, x ∈ D'.captured p hp ↔ x ∈ D.captured p hp := by
    intro x
    constructor
    · intro hx
      obtain ⟨T, hT⟩ := captured_eventually_small hx (D.rm_pos p hp)
      have h1 : ∃ s, D'.flow s x ∈ (D.chart p hp).χ ''
          {y | morseNorm n y < D.rm p hp ∧ negPart (D.chart p hp).hk y = 0} :=
        ⟨T, by rw [← hset]; exact hT T le_rfl⟩
      exact (exists_flow_mem_iff D' D hφ hm hφb hV x _).2 h1
    · intro hx
      obtain ⟨T, hT⟩ := captured_eventually_small hx (D'.rm_pos p hp)
      have h1 : ∃ s, D.flow s x ∈ (D'.chart p hp).χ ''
          {y | morseNorm n y < D'.rm p hp ∧ negPart (D'.chart p hp).hk y = 0} :=
        ⟨T, by rw [hset]; exact hT T le_rfl⟩
      exact (exists_flow_mem_iff D' D hφ hm hφb hV x _).1 h1
  ext x
  rw [charac g D' ε' hg hε' hrm' ht' hU' x, charac f D ε hf hε hrm ht hU x, hcap x, hlev x]

theorem leftSphereHit_eq_of_rescale {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) (hresc : D'.isRescaleOf D)
    (hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k)
    {q : M} (hq : q ∈ crit) {μ : ℕ} (hμ : (D.chart q hq).k = μ) {ε ε' t : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hrm : 2 * ε < D.rm q hq ^ 2) (hrm' : 2 * ε' < D'.rm q hq ^ 2)
    (ht : t < f q - ε) (ht' : t < g q - ε') (hsub : ∀ z, g z ≤ t ↔ f z ≤ t)
    (hreach : ∀ y : EuclideanSpace ℝ (Fin μ), y ≠ 0 → ∃ s, 0 ≤ s ∧
      f (D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y)))) ≤ t) :
    ∀ y : EuclideanSpace ℝ (Fin μ), y ≠ 0 →
      D'.leftSphereHit q μ ε' t y = D.leftSphereHit q μ ε t y := by
  intro y hy
  have hspEq : ∀ δ : ℝ, (D'.chart q hq).sphereParam δ (Handle.reidx y) =
      (D.chart q hq).sphereParam δ (Handle.reidx y) := by
    intro δ
    have key : ∀ (k₁ k₂ : ℕ) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ →
        recombine h₁ ((Real.sqrt (2 * δ) /
            ‖(EuclideanSpace.equiv (Fin k₁) ℝ).symm (Handle.reidx y)‖) •
          (EuclideanSpace.equiv (Fin k₁) ℝ).symm (Handle.reidx y)) 0 =
        recombine h₂ ((Real.sqrt (2 * δ) /
            ‖(EuclideanSpace.equiv (Fin k₂) ℝ).symm (Handle.reidx y)‖) •
          (EuclideanSpace.equiv (Fin k₂) ℝ).symm (Handle.reidx y)) 0 := by
      rintro k₁ k₂ h₁ h₂ rfl
      rfl
    exact key _ _ _ _ (hχ q hq).2
  have hstart : ∀ δ : ℝ, (D'.chart q hq).χ ((D'.chart q hq).sphereParam δ (Handle.reidx y)) =
      (D.chart q hq).χ ((D.chart q hq).sphereParam δ (Handle.reidx y)) := by
    intro δ
    rw [hspEq δ, (hχ q hq).1]
  unfold leftSphereHit
  simp only [hq, ↓reduceDIte]
  rw [hstart ε']
  set x₀ := (D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y)) with hx₀
  set x₁ := (D.chart q hq).χ ((D.chart q hq).sphereParam ε' (Handle.reidx y)) with hx₁
  have hwne : ∀ (k : ℕ), k = μ → (Handle.reidx y : Fin k → ℝ) ≠ 0 := by
    rintro k rfl h0
    apply hy
    ext j
    have h := congrFun h0 j
    simpa [Handle.reidx, j.isLt] using h
  have hw : (Handle.reidx y : Fin (D.chart q hq).k → ℝ) ≠ 0 := hwne _ hμ
  have hw' : (Handle.reidx y : Fin (D'.chart q hq).k → ℝ) ≠ 0 :=
    hwne _ ((hχ q hq).2.trans hμ)
  have hrmpos : 0 < D.rm q hq := D.rm_pos q hq
  have hrmpos' : 0 < D'.rm q hq := D'.rm_pos q hq
  have hεR : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 :=
      pow_le_pow_left₀ hrmpos.le (D.hrm q hq).2 2
    linarith
  have hεR' : 2 * ε' ≤ (D'.chart q hq).R ^ 2 := by
    have h1 : D'.rm q hq ^ 2 ≤ (D'.chart q hq).R ^ 2 :=
      pow_le_pow_left₀ hrmpos'.le (D'.hrm q hq).2 2
    linarith
  have hfx₀ : f x₀ = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hεR
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw)
  have hgx₁ : g x₁ = g q - ε' := by
    rw [hx₁, ← hstart ε']
    exact (D'.chart q hq).f_chart_of_mem_leftModelSphere hεR'
      ((D'.chart q hq).sphereParam_mem_leftModelSphere hε'.le hw')
  have htfx₀ : t < f x₀ := by rw [hfx₀]; exact ht
  obtain ⟨φ₀, hφ₀, ⟨m₀, M₁, hm₀, hφ₀b⟩, hV₀⟩ := hresc
  have hφ₀pos : ∀ x, 0 < φ₀ x := fun x => hm₀.trans_le (hφ₀b x).1
  have hM₁ : 0 < M₁ := (hφ₀pos q).trans_le (hφ₀b q).2
  set φ : M → ℝ := fun x => (φ₀ x)⁻¹ with hφdef
  have hφ : Continuous φ := hφ₀.inv₀ fun x => (hφ₀pos x).ne'
  have hm : (0 : ℝ) < M₁⁻¹ := inv_pos.2 hM₁
  have hφb : ∀ x, M₁⁻¹ ≤ φ x ∧ φ x ≤ m₀⁻¹ := fun x =>
    ⟨inv_anti₀ (hφ₀pos x) (hφ₀b x).2, inv_anti₀ hm₀ (hφ₀b x).1⟩
  have hV : ∀ x, D'.V x = φ x • D.V x := by
    intro x
    rw [hV₀ x, smul_smul, hφdef]
    simp only
    rw [inv_mul_cancel₀ (hφ₀pos x).ne', one_smul]
  have hdesc : ∀ (h : M → ℝ) (E : GradientLikeStrip I h a b crit) (x : M) (s : ℝ), 0 ≤ s →
      h (E.flow s x) ≤ t → (∀ r, 0 ≤ r → r < s → t < h (E.flow r x)) →
      E.descend t x = E.flow s x := by
    intro h E x s hs0 hst hlt
    have hT : E.hitTime t x = s := by
      unfold hitTime
      apply le_antisymm
      · have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ h (E.flow r x) ≤ t} := ⟨0, fun r hr => hr.1⟩
        exact csInf_le hbdd ⟨hs0, hst⟩
      · refine le_csInf ⟨s, hs0, hst⟩ ?_
        rintro r ⟨hr0, hrt⟩
        by_contra hlt'
        exact absurd hrt (not_le.2 (hlt r hr0 (not_le.1 hlt')))
    unfold descend
    rw [hT]
  set A : Set ℝ := {s | 0 ≤ s ∧ f (D.flow s x₀) ≤ t} with hA
  have hAne : A.Nonempty := by
    obtain ⟨s, hs0, hst⟩ := hreach y hy
    exact ⟨s, hs0, hst⟩
  have hAc : IsClosed A :=
    isClosed_Ici.inter (isClosed_le (hf.continuous.comp (D.continuous_flow_curve x₀))
      continuous_const)
  have hAbdd : BddBelow A := ⟨0, fun r hr => hr.1⟩
  set s₁ := sInf A with hs₁
  have hs₁A : s₁ ∈ A := hAc.csInf_mem hAne hAbdd
  have hbefore : ∀ r, 0 ≤ r → r < s₁ → t < f (D.flow r x₀) := by
    intro r hr0 hrs
    by_contra hle
    exact absurd (csInf_le hAbdd ⟨hr0, not_lt.1 hle⟩) (not_le.2 hrs)
  have hDdesc : D.descend t x₀ = D.flow s₁ x₀ := hdesc f D x₀ s₁ hs₁A.1 hs₁A.2 hbefore
  set ŵ := (D.chart q hq).toE (Handle.reidx y) with hŵ
  have hŵne : ‖ŵ‖ ≠ 0 := norm_ne_zero_iff.2 ((D.chart q hq).toE_ne_zero hw)
  set u := ‖ŵ‖⁻¹ • ŵ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hŵne]
  have hsp : ∀ δ : ℝ, (D.chart q hq).sphereParam δ (Handle.reidx y) =
      recombine (D.chart q hq).hk (Real.sqrt (2 * δ) • u) 0 := by
    intro δ
    simp only [MorseNormalChart.sphereParam, hu, smul_smul, div_eq_mul_inv, hŵ]
  set ŵ' := (D'.chart q hq).toE (Handle.reidx y) with hŵ'
  have hŵne' : ‖ŵ'‖ ≠ 0 := norm_ne_zero_iff.2 ((D'.chart q hq).toE_ne_zero hw')
  set u' := ‖ŵ'‖⁻¹ • ŵ' with hu'
  have hu1' : ‖u'‖ = 1 := by
    rw [hu', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hŵne']
  have hsp' : ∀ δ : ℝ, (D'.chart q hq).sphereParam δ (Handle.reidx y) =
      recombine (D'.chart q hq).hk (Real.sqrt (2 * δ) • u') 0 := by
    intro δ
    simp only [MorseNormalChart.sphereParam, hu', smul_smul, div_eq_mul_inv, hŵ']
  have horbit : ∃ c : ℝ, x₁ = D.flow c x₀ ∧ t < f x₁ := by
    rcases lt_or_ge ε' ε with hlt | hle
    · have hsq : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
      have hsqrm : Real.sqrt (2 * ε) < D.rm q hq := (Real.sqrt_lt' hrmpos).2 hrm
      obtain ⟨-, h2⟩ := CrossField.flow_ray_unstable D hf hq hu1 hsq hsqrm
      obtain ⟨s, hs0, hflow⟩ := h2 (Real.sqrt (2 * ε'))
        ⟨Real.sqrt_pos.2 (by linarith), Real.sqrt_le_sqrt (by linarith)⟩
      rw [← hsp, ← hsp, ← hx₀, ← hx₁] at hflow
      refine ⟨-s, hflow.symm, ?_⟩
      rw [← hflow]
      have h3 := le_f_flow_of_nonpos (D := D) hf x₀ (t := -s) (by linarith)
      linarith
    · have hsq : 0 < Real.sqrt (2 * ε') := Real.sqrt_pos.2 (by linarith)
      have hsqrm : Real.sqrt (2 * ε') < D'.rm q hq := (Real.sqrt_lt' hrmpos').2 hrm'
      obtain ⟨-, h2⟩ := CrossField.flow_ray_unstable D' hg hq hu1' hsq hsqrm
      obtain ⟨s, hs0, hflow⟩ := h2 (Real.sqrt (2 * ε))
        ⟨Real.sqrt_pos.2 (by linarith), Real.sqrt_le_sqrt (by linarith)⟩
      rw [← hsp', ← hsp', hstart, hstart, ← hx₀, ← hx₁] at hflow
      have hx₁eq : x₁ = D'.flow s x₀ := by
        rw [← hflow, flow_flow_neg]
      obtain ⟨σ₀, -, -, -, hσ₀⟩ := exists_reparam D D' hφ hm hφb hV x₀
      refine ⟨σ₀ s, by rw [hx₁eq, hσ₀], ?_⟩
      by_contra hle'
      have := (hsub x₁).2 (not_lt.1 hle')
      linarith
  obtain ⟨c, hx₁c, htfx₁⟩ := horbit
  have hcs₁ : c < s₁ := by
    by_contra hle
    have h1 := f_flow_antitone (D := D) hf x₀ (not_lt.1 hle)
    simp only at h1
    rw [← hx₁c] at h1
    linarith [hs₁A.2]
  obtain ⟨σ, hσmono, hσ0, hσsurj, hσ⟩ := exists_reparam D D' hφ hm hφb hV x₁
  obtain ⟨s', hs'⟩ := hσsurj (s₁ - c)
  have hs'pos : 0 < s' := by
    have h1 : σ 0 < σ s' := by rw [hσ0, hs']; linarith
    exact hσmono.lt_iff_lt.1 h1
  have hflowr : ∀ r, D'.flow r x₁ = D.flow (c + σ r) x₀ := by
    intro r
    rw [hσ r, hx₁c, flow_flow]
  have hend : D'.flow s' x₁ = D.flow s₁ x₀ := by
    rw [hflowr, hs']
    congr 1
    ring
  rw [hDdesc, ← hend]
  refine hdesc g D' x₁ s' hs'pos.le ?_ ?_
  · rw [hend]
    exact (hsub _).2 hs₁A.2
  · intro r hr0 hrs
    have hlt : c + σ r < s₁ := by
      have := hσmono hrs
      rw [hs'] at this
      linarith
    have hfr : t < f (D.flow (c + σ r) x₀) := by
      rcases le_or_gt 0 (c + σ r) with h0 | h0
      · exact hbefore _ h0 hlt
      · have := le_f_flow_of_nonpos (D := D) hf x₀ h0.le
        linarith
    rw [hflowr]
    by_contra hle
    exact absurd ((hsub _).1 (not_lt.1 hle)) (not_le.2 hfr)

end GradientLikeStrip

namespace BlockConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ}

theorem exists_shrink (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {ε₁ ρ : ℝ}
    (hε₁ : 0 < ε₁) (hε₁ε : ε₁ ≤ B.ε) (hρ0 : 0 < ρ) (hρ : 8 * ε₁ < ρ ^ 2) :
    ∃ B' : BlockConfig I f a b ℓ, ∃ hcrit : B'.crit = B.crit, B'.α = B.α ∧ B'.β = B.β ∧
      B'.c = B.c ∧ B'.ε = ε₁ ∧
      (∀ x (hx : x ∈ B.crit), (B'.D.chart x (hcrit ▸ hx)).χ = (B.D.chart x hx).χ ∧
        (B'.D.chart x (hcrit ▸ hx)).k = (B.D.chart x hx).k ∧
        (B'.D.chart x (hcrit ▸ hx)).R = (B.D.chart x hx).R ∧
        (B'.D.chart x (hcrit ▸ hx)).r₀ ≤ (B.D.chart x hx).r₀ ∧
        B'.D.rm x (hcrit ▸ hx) = min ρ (B.D.rm x hx)) ∧
      (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ z, B'.D.V z = φ z • B.D.V z) ∧
      (∀ z, (∀ y (hy : y ∈ B.crit),
          z ∉ (B.D.chart y hy).χ '' {w | morseNorm n w < (B.D.chart y hy).r₀}) →
        B'.D.V z = B.D.V z) ∧
      (∀ q ∈ B.upperIndexCriticalPoints, B'.leftSphere q = B.leftSphere q) ∧
      (∀ p ∈ B.lowerIndexCriticalPoints, B'.rightSphere p = B.rightSphere p) ∧
      (∀ q ∈ B.upperIndexCriticalPoints, ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c y = B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) ∧
      ∀ p ∈ B.lowerIndexCriticalPoints, ∀ q ∈ B.upperIndexCriticalPoints, (B'.pairTransverse p q ↔ B.pairTransverse p q) ∧
        B'.count p q = B.count p q ∧ B'.zerosCard p q = B.zerosCard p q := by
  classical
  have hff : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hrmB : ∀ x hx, 8 * ε₁ < B.D.rm x hx ^ 2 := fun x hx => by
    linarith [B.hrm x hx]
  obtain ⟨D', hresc, hch, hsm, hV⟩ :=
    GradientLikeStrip.exists_shrink_field hff B.D hε₁ hρ0 hρ hrmB
  have hrm' : ∀ x hx, 8 * ε₁ < D'.rm x hx ^ 2 := by
    intro x hx
    rw [(hsm x hx).2]
    rcases min_choice ρ (B.D.rm x hx) with h | h
    · rw [h]; exact hρ
    · rw [h]; exact hrmB x hx
  have hr₀' : ∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε₁ := fun x hx => (hsm x hx).1
  have hlev' : ∀ y, f y ∈ Icc (B.α + ε₁) (B.β - ε₁) → ∀ x hx, y ∉ D'.smallBall x hx := by
    intro y hy x hx hyx
    have habs := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hyx
    have hr := hr₀' x hx
    rw [abs_lt] at habs
    have hmin := B.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h1 | h1
    · have := B.hhigh x hx h1
      linarith [hy.2]
    · rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h2 | h2
      · have := B.hQ x hx (by omega)
        linarith [hy.2]
      · have := B.hP x hx (by omega)
        linarith [hy.1]
  let B' : BlockConfig I f a b ℓ :=
    { crit := B.crit
      hcrit := B.hcrit
      D := D'
      α := B.α
      β := B.β
      ε := ε₁
      c := B.c
      hε := hε₁
      hr₀ := hr₀'
      hrm := hrm'
      haα := B.haα
      hαc := by linarith [B.hαc]
      hcβ := by linarith [B.hcβ]
      hβb := B.hβb
      hmin := B.hmin
      hP := B.hP
      hQ := B.hQ
      hhigh := B.hhigh
      hlev := hlev' }
  have hχ : ∀ x hx, (D'.chart x hx).χ = (B.D.chart x hx).χ ∧
      (D'.chart x hx).k = (B.D.chart x hx).k := fun x hx => ⟨(hch x hx).1, (hch x hx).2.1⟩
  have hac : a ≤ B.c := by linarith [B.haα, B.hαc, B.hε]
  have hcb : B.c ≤ b := by linarith [B.hβb, B.hcβ, B.hε]
  have hPB : B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints := BlockConfig.lowerIndexCriticalPoints_eq_of_crit_eq B rfl
  have hQB : B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints := BlockConfig.upperIndexCriticalPoints_eq_of_crit_eq B rfl
  have hresc' : ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
      ∀ z, D'.V z = φ z • B.D.V z := by
    obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ := hresc
    have hφpos : ∀ x, 0 < φ x := fun x => hm.trans_le (hφb x).1
    have hM₀ : 0 < max M₀ m := hm.trans_le (le_max_right _ _)
    refine ⟨fun x => (φ x)⁻¹, hφc.inv₀ fun x => (hφpos x).ne', ⟨(max M₀ m)⁻¹, m⁻¹, inv_pos.2 hM₀,
      fun x => ⟨inv_anti₀ (hφpos x) ((hφb x).2.trans (le_max_left _ _)), inv_anti₀ hm (hφb x).1⟩⟩, fun z => ?_⟩
    rw [hφV z, smul_smul, inv_mul_cancel₀ (hφpos z).ne', one_smul]
  refine ⟨B', rfl, rfl, rfl, rfl, rfl, ?_, hresc', hV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hch x hx).1, (hch x hx).2.1, (hch x hx).2.2.1, (hch x hx).2.2.2.2, (hsm x hx).2⟩
  · intro q hq
    have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
    have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
    have hqc' : q ∈ B'.crit := hqc
    unfold BlockConfig.leftSphere
    rw [dite_eq_left_of_eq_true (eq_true hqc'), dite_eq_left_of_eq_true (eq_true hqc)]
    refine GradientLikeStrip.leftSphere_eq_of_rescale hff hff B.D D' hresc hχ hqc B.hε hε₁
      (by linarith [B.hrm q hqc, B.hε]) (by linarith [hrm' q hqc]) hac
      (by rw [hqβ]; linarith [B.hcβ]) (by rw [hqβ]; linarith [B.hcβ, hε₁ε]) ?_ ?_
      (fun _ => Iff.rfl)
    · intro y hy x hx
      rw [hqβ] at hy
      exact B.hlev y ⟨by linarith [hy.1, B.hαc], hy.2⟩ x hx
    · intro y hy x hx
      rw [hqβ] at hy
      exact hlev' y ⟨by linarith [hy.1, B.hαc, hε₁ε], hy.2⟩ x hx
  · intro p hp
    have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
    have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
    have hpc' : p ∈ B'.crit := hpc
    unfold BlockConfig.rightSphere
    rw [dite_eq_left_of_eq_true (eq_true hpc'), dite_eq_left_of_eq_true (eq_true hpc)]
    refine GradientLikeStrip.rightSphere_eq_of_rescale hff hff B.D D' hresc hχ hpc B.hε hε₁
      (by linarith [B.hrm p hpc, B.hε]) (by linarith [hrm' p hpc]) hcb
      (by rw [hpα]; linarith [B.hαc]) (by rw [hpα]; linarith [B.hαc, hε₁ε]) ?_ ?_
      (fun _ => Iff.rfl)
    · intro y hy x hx
      rw [hpα] at hy
      exact B.hlev y ⟨hy.1, by linarith [hy.2, B.hcβ]⟩ x hx
    · intro y hy x hx
      rw [hpα] at hy
      exact hlev' y ⟨hy.1, by linarith [hy.2, B.hcβ, hε₁ε]⟩ x hx
  · intro q hq y hy
    have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
    have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
    have hμ : (B.D.chart q hqc).k = ℓ + 1 := by
      rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
    refine GradientLikeStrip.leftSphereMap_eq_of_rescale hff hff B.D D' hresc hχ hqc hμ B.hε hε₁
      (by linarith [B.hrm q hqc, B.hε]) (by linarith [hrm' q hqc]) hac
      (by rw [hqβ]; linarith [B.hcβ]) (by rw [hqβ]; linarith [B.hcβ, hε₁ε]) ?_ ?_
      (fun _ => Iff.rfl) y hy
    · intro y hy x hx
      rw [hqβ] at hy
      exact B.hlev y ⟨by linarith [hy.1, B.hαc], hy.2⟩ x hx
    · intro y hy x hx
      rw [hqβ] at hy
      exact hlev' y ⟨by linarith [hy.1, B.hαc, hε₁ε], hy.2⟩ x hx
  · intro p hp q hq
    have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
    have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
    have hpc' : p ∈ B'.crit := hpc
    have hqc' : q ∈ B'.crit := hqc
    have hv := B.sardValid hp hq
    have hv' := B'.sardValid (hPB.symm ▸ hp) (hQB.symm ▸ hq)
    have hS := GradientLikeStrip.sardAgree_of_rescale hff hff B.D D' hresc hχ hε₁ε hpc hqc hv hv'
      B.c B.c
    refine ⟨⟨fun ⟨_, _, h⟩ => ⟨hpc, hqc, hS.1.1 h⟩, fun ⟨_, _, h⟩ => ⟨hpc', hqc', hS.1.2 h⟩⟩,
      ?_, ?_⟩
    · unfold BlockConfig.count
      rw [dite_eq_left_of_eq_true (eq_true hpc'), dite_eq_left_of_eq_true (eq_true hqc'), dite_eq_left_of_eq_true (eq_true hpc), dite_eq_left_of_eq_true (eq_true hqc)]
      exact hS.2.1
    · unfold BlockConfig.zerosCard
      rw [dite_eq_left_of_eq_true (eq_true hpc'), dite_eq_left_of_eq_true (eq_true hqc'), dite_eq_left_of_eq_true (eq_true hpc), dite_eq_left_of_eq_true (eq_true hqc)]
      exact hS.2.2

end BlockConfig

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem noCommon_sameLevel (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {x y : M}
    (hx : x ∈ crit) (hy : y ∈ crit) (hxy : x ≠ y) (hlev : f x = f y) {rx ry : ℝ}
    (hrx : rx ^ 2 < 2 * ε) (hry : ry ^ 2 < 2 * ε) : D.noCommon x hx y hy rx ry := by
  have key : ∀ (p : M) (hp : p ∈ crit) (q : M) (hq : q ∈ crit), p ≠ q → f p = f q →
      ∀ (w w' : Fin n → ℝ), morseNorm n w ^ 2 < 2 * ε → morseNorm n w' ^ 2 < 2 * ε →
      ∀ s : ℝ, 0 ≤ s → D.flow s ((D.chart p hp).χ w) ≠ (D.chart q hq).χ w' := by
    intro p hp q hq hpq hfpq w w' hw hw' s hs heq
    have hrmp := (hεr p hp).2
    have hrmq := (hεr q hq).2
    have hrmp0 := D.rm_pos p hp
    have hrmq0 := D.rm_pos q hq
    have hw'lt : morseNorm n w' < D.rm q hq := by
      apply lt_of_pow_lt_pow_left₀ 2 hrmq0.le
      linarith
    have hwlt : morseNorm n w < D.rm p hp := by
      apply lt_of_pow_lt_pow_left₀ 2 hrmp0.le
      linarith
    have hmemq : D.flow s ((D.chart p hp).χ w) ∈
        (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' := by
      rw [heq]
      exact ⟨w', mem_ball_of_morseNorm_lt (hw'lt.trans (D.rm_lt_R' q hq)), rfl⟩
    have hfz' : f q - ε < f (D.flow s ((D.chart p hp).χ w)) := by
      rw [heq, (D.chart q hq).hnorm w' (hw'lt.le.trans (D.hrm q hq).2), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
      have := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk w'
      nlinarith [sq_nonneg ‖posPart (D.chart q hq).hk w'‖]
    by_cases hu : negPart (D.chart p hp).hk w = 0
    · obtain ⟨z, hz, hzx⟩ := flow_mem_of_negPart_eq_zero (D := D) hp hwlt hu hs
      have hmemp : D.flow s ((D.chart p hp).χ w) ∈
          (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
        ⟨z, mem_ball_of_morseNorm_lt (hz.1.trans_lt (hwlt.trans (D.rm_lt_R' p hp))), hzx⟩
      exact Set.disjoint_left.1 (D.disjoint p hp q hq hpq) hmemp hmemq
    · have hsplit := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk w
      have hball : 2 * ε + 2 * ‖posPart (D.chart p hp).hk w‖ ^ 2 < D.rm p hp ^ 2 := by
        nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk w‖]
      have hlevel : f p - ε ≤ morseNormalForm (D.chart p hp).hk (f p) w := by
        rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
        nlinarith [sq_nonneg ‖posPart (D.chart p hp).hk w‖]
      obtain ⟨t, ht0, hft, hin, -⟩ := exists_exit_desc (D := D) hf hp hε hball hu hlevel
      rcases le_or_gt s t with hst | hts
      · obtain ⟨z, hz, hzx⟩ := hin s ⟨hs, hst⟩
        have hzlt : morseNorm n z < (D.chart p hp).R' := by
          have hz' : morseNorm n z < D.rm p hp :=
            lt_of_pow_lt_pow_left₀ 2 hrmp0.le (lt_of_le_of_lt hz hball)
          exact hz'.trans (D.rm_lt_R' p hp)
        exact Set.disjoint_left.1 (D.disjoint p hp q hq hpq)
          ⟨z, mem_ball_of_morseNorm_lt hzlt, hzx⟩ hmemq
      · have hanti := D.f_flow_antitone hf ((D.chart p hp).χ w) hts.le
        simp only at hanti
        linarith
  rintro z ⟨w, hw, rfl⟩ s ⟨w', hw', heq⟩
  have hw0 : morseNorm n w < rx := hw
  have hw'0 : morseNorm n w' < ry := hw'
  have hw2 : morseNorm n w ^ 2 < 2 * ε := by
    have h0 := ModelField.morseNorm_nonneg w
    nlinarith
  have hw'2 : morseNorm n w' ^ 2 < 2 * ε := by
    have h0 := ModelField.morseNorm_nonneg w'
    nlinarith
  rcases le_or_gt 0 s with hs | hs
  · exact key x hx y hy hxy hlev w w' hw2 hw'2 s hs heq.symm
  · apply key y hy x hx hxy.symm hlev.symm w' w hw'2 hw2 (-s) (by linarith)
    rw [heq, flow_neg_flow]

theorem exists_noCommon_of_disjoint (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {x y : M} (hx : x ∈ crit) (hy : y ∈ crit) {ε c : ℝ}
    (hε : 0 < ε) (hεr : ∀ z hz, (D.chart z hz).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm z hz ^ 2)
    (hxc : f x + ε < c) (hcy : c < f y - ε)
    (hlev : ∀ z, f z ∈ Icc (f x + ε) (f y - ε) → ∀ w hw, z ∉ D.smallBall w hw)
    (hdisj : Disjoint (D.rightSphere x hx ε c) (D.leftSphere y hy ε c)) :
    ∃ ρ > 0, ∀ rx ry, rx < ρ → ry < ρ → D.noCommon x hx y hy rx ry := by
  have hxy : y ≠ x := by
    rintro rfl
    linarith
  have hrmx := D.rm_pos x hx
  have hrmy := D.rm_pos y hy
  have hRx : 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    have h1 := (D.hrm x hx).2
    have h2 : D.rm x hx ^ 2 ≤ (D.chart x hx).R ^ 2 := pow_le_pow_left₀ hrmx.le h1 2
    linarith [(hεr x hx).2]
  have hRy : 2 * ε ≤ (D.chart y hy).R ^ 2 := by
    have h1 := (D.hrm y hy).2
    have h2 : D.rm y hy ^ 2 ≤ (D.chart y hy).R ^ 2 := pow_le_pow_left₀ hrmy.le h1 2
    linarith [(hεr y hy).2]
  obtain ⟨δ, hδ, htube⟩ := exists_tube_disjoint D x hx y hy hε hRx hRy hdisj
  set ρ : ℝ := min 1 (min (ε / 2) (ε * δ)) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (lt_min (by linarith) (mul_pos hε hδ))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : ρ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ ε * δ := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < ε := by nlinarith
  have hρ4 : ρ ^ 4 ≤ 2 * ε * δ := by
    have h2 : ρ ^ 2 ≤ ρ := by nlinarith
    have h4 : ρ ^ 4 ≤ ρ ^ 2 := by nlinarith
    nlinarith
  have hmain := nocommon_of_agree (D := D) (D' := D) hf hx hy hxy (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => subset_rfl) hε hρ0 hρsq hρ4 (by linarith [(hεr x hx).2])
    (by linarith [(hεr y hy).2]) (fun _ _ _ => rfl) hxc hcy hlev htube
  refine ⟨ρ, hρ0, fun rx ry hrx hry => ?_⟩
  rintro _ ⟨w, hw, rfl⟩ s ⟨w', hw', hs⟩
  have hw1 : morseNorm n w < ρ := lt_trans hw hrx
  have hw2 : morseNorm n w' < ρ := lt_trans hw' hry
  exact hmain _ ⟨w, hw1, rfl⟩ s ⟨w', hw2, hs⟩

end GradientLikeStrip

section Moves

variable (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem exists_move_core {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) {crit : Finset M}
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2)
    (S : Finset M) (hS : ∀ x ∈ S, x ∈ crit) {s₀ u v t : ℝ} (hSlev : ∀ x ∈ S, f x = s₀)
    (hau : a < u) (hvb : v < b) (hin : u + 2 * ε < min s₀ t ∧ max s₀ t < v - 2 * ε)
    (hsep : ∀ x ∈ crit, f x ∉ Ioo u v → f x + 2 * ε ≤ u ∨ v ≤ f x - 2 * ε)
    (hwin : ∀ x ∈ crit, f x ∈ Icc u v → f x = s₀ ∨ f x = t)
    (r' : ∀ x ∈ crit, ℝ) (hr' : ∀ x hx, (D.chart x hx).r₀ < r' x hx ∧ r' x hx ^ 2 < 2 * ε)
    (hnoc : ∀ x (hx : x ∈ crit) y (hy : y ∈ crit), x ∈ S → y ∉ S → f y ∈ Icc u v →
      D.noCommon x hx y hy (r' x hx) (r' y hy)) :
    ∃ g : M → ℝ, ModifiedWithin f u v g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      (∀ x ∈ S, g x = t) ∧ (∀ x ∈ crit, x ∉ S → g x = f x) ∧
      ∃ D' : GradientLikeStrip I g a b crit, D'.isRescaleOf D ∧
        (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
          (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
        ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
          ∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm x hx ^ 2 := by
  classical
  have hfs := hf.smooth
  obtain ⟨hin1, hin2⟩ := hin
  have hs₀u : u + 2 * ε < s₀ := lt_of_lt_of_le hin1 (min_le_left _ _)
  have htu : u + 2 * ε < t := lt_of_lt_of_le hin1 (min_le_right _ _)
  have hs₀v : s₀ < v - 2 * ε := lt_of_le_of_lt (le_max_left _ _) hin2
  have htv : t < v - 2 * ε := lt_of_le_of_lt (le_max_right _ _) hin2
  have huv : u < v := by linarith
  have hreg : ∀ x, f x = u ∨ f x = v → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hc
    have hxab : f x ∈ Ioo a b := by
      rcases hx with h | h
      · rw [h]; exact ⟨hau, by linarith⟩
      · rw [h]; exact ⟨by linarith, hvb⟩
    have hxc : x ∈ crit := (hcrit x).2 ⟨hxab, hc⟩
    have hxn : f x ∉ Ioo u v := by
      rcases hx with h | h
      · rw [h]; exact fun h' => lt_irrefl _ h'.1
      · rw [h]; exact fun h' => lt_irrefl _ h'.2
    rcases hsep x hxc hxn with h | h <;> rcases hx with h' | h' <;> linarith
  have hwinI : ∀ x ∈ crit, f x ∈ Ioo u v → u + 2 * ε < f x := by
    intro x hx hxI
    rcases hwin x hx (Ioo_subset_Icc_self hxI) with h | h <;> rw [h] <;> assumption
  have hnocommon : ∀ p hp q hq, p ∈ {x : M | x ∉ S} → q ∈ (↑S : Set M) →
      f p ∈ Ioo u v → f q ∈ Ioo u v →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp}, ∀ s,
        D.flow s x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq} := by
    intro p hp q hq hpS hqS hpI _ x hx s hmem
    refine hnoc q hq p hp hqS hpS (Ioo_subset_Icc_self hpI) _ hmem (-s) ?_
    rw [GradientLikeStrip.flow_neg_flow]
    exact hx
  obtain ⟨μ, ρ, hρ, hμ, hμ01, hμV, hμ0, hμ1⟩ := exists_trajectoryCutoff' hfs D hau.le hvb.le
    {x | x ∉ S} (↑S) (fun p _ _ => by by_cases h : p ∈ S <;> simp [h])
    (fun p h1 h2 => h1 h2) (c := u + ε) ⟨by linarith, by linarith⟩ hε hεr
    (fun p hp hpI => by
      rcases hsep p hp hpI with h | h
      · left; linarith
      · right; linarith)
    (fun p hp hpI => ⟨fun h => by linarith [hwinI p hp hpI], fun _ => by
      linarith [hwinI p hp hpI]⟩)
    (fun p hp hpI => by linarith [hwinI p hp hpI]) r' (fun p hp => (hr' p hp).1) hnocommon
  have hρpos : ∀ x hx, 0 < ρ x hx := fun x hx => (D.chart x hx).hr₀.trans (hρ x hx).1
  have hr'rm : ∀ x hx, r' x hx < D.rm x hx := fun x hx => by
    apply lt_of_pow_lt_pow_left₀ 2 (D.rm_pos x hx).le
    linarith [(hr' x hx).2, (hεr x hx).2]
  have hρrm : ∀ x hx, ρ x hx < D.rm x hx := fun x hx => (hρ x hx).2.1.trans_lt (hr'rm x hx)
  have hρR : ∀ x hx, ρ x hx ≤ (D.chart x hx).R := fun x hx =>
    (hρrm x hx).le.trans (D.hrm x hx).2
  have hρR' : ∀ x hx, ρ x hx ≤ (D.chart x hx).R' := fun x hx =>
    (hρrm x hx).le.trans (D.rm_lt_R' x hx).le
  have hρsq : ∀ x hx, ρ x hx ≤ Real.sqrt (2 * ε) := fun x hx =>
    Real.le_sqrt_of_sq_le (hρ x hx).2.2
  obtain ⟨ρm, hρm, hρmle⟩ := exists_pos_le_forall_finset crit.attach (fun x => ρ x.1 x.2)
    (fun x _ => hρpos x.1 x.2)
  have hρmle' : ∀ x hx, ρm ≤ ρ x hx := fun x hx => hρmle ⟨x, hx⟩ (Finset.mem_attach _ _)
  set ε₁ : ℝ := min (ρm ^ 2 / 128) (ε / 8) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by linarith)
  have hε₁m : ε₁ ≤ ρm ^ 2 / 128 := min_le_left _ _
  have hε₁8 : ε₁ ≤ ε / 8 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := by linarith
  have hρmsq : ∀ x hx, ρm ^ 2 ≤ ρ x hx ^ 2 := fun x hx =>
    pow_le_pow_left₀ hρm.le (hρmle' x hx) 2
  have h2ε : 0 < 2 * ε := by linarith
  obtain ⟨E, ⟨φ₁, hφ₁c, ⟨m₁, M₁, hm₁, hφ₁b⟩, hφ₁V⟩, hEc, hEr, -⟩ :=
    GradientLikeStrip.exists_shrink_field hfs D (ε₁ := ε₁) (ρ := Real.sqrt (2 * ε)) hε₁
      (Real.sqrt_pos.2 h2ε) (by rw [Real.sq_sqrt h2ε.le]; linarith)
      (fun x hx => by linarith [(hεr x hx).2])
  have hEχ : ∀ x hx, (E.chart x hx).χ = (D.chart x hx).χ := fun x hx => (hEc x hx).1
  have hER : ∀ x hx, (E.chart x hx).R = (D.chart x hx).R := fun x hx => (hEc x hx).2.2.1
  have hEr₀ : ∀ x hx, (E.chart x hx).r₀ < ρ x hx / 8 := fun x hx => by
    have h1 : (E.chart x hx).r₀ ^ 2 < (ρm / 8) ^ 2 := by
      have := (hEr x hx).1
      have e : (ρm / 8) ^ 2 = ρm ^ 2 / 64 := by ring
      rw [e]; linarith
    have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
    linarith [hρmle' x hx]
  have hφ₁pos : ∀ x, 0 < φ₁ x := fun x => hm₁.trans_le (hφ₁b x).1
  have hμVE : ∀ x ∈ f ⁻¹' Ioo u v, (mfderiv I 𝓘(ℝ, ℝ) μ x) (E.V x) = 0 := by
    intro x hx
    have e : E.V x = (φ₁ x)⁻¹ • D.V x := by
      rw [hφ₁V x, smul_smul, inv_mul_cancel₀ (hφ₁pos x).ne', one_smul]
    rw [e, map_smul, hμV x hx, smul_zero]
  obtain ⟨ρ₂, hρ₂, hρ₂', -, hρ₂id, hρ₂maps₃, hρ₂tr⟩ :=
    MonotoneShift.exists_translationShift (c₀ := u + ε) (c₁ := v - ε) (lo := s₀ - ε)
      (hi := s₀ + ε) (d := t - s₀) (lt_min (by linarith) (by linarith))
      (max_lt (by linarith) (by linarith)) (by linarith)
  have h₃ : u < u + ε ∧ v - ε < v := ⟨by linarith, by linarith⟩
  have hρ₂maps : MapsTo ρ₂ (Ioo u v) (Ioo u v) := by
    intro s hs
    by_cases hs' : s ∈ Ioo (u + ε) (v - ε)
    · have := hρ₂maps₃ hs'
      exact ⟨h₃.1.trans this.1, this.2.trans h₃.2⟩
    · rw [hρ₂id s hs']
      exact hs
  have hμconst : ∀ x hx, f x ∈ Ioo u v →
      ∀ y ∈ (D.chart x hx).χ '' {z | morseNorm n z < ρ x hx}, μ y = if x ∈ S then 1 else 0 := by
    intro x hx hxI y hy
    by_cases hxS : x ∈ S
    · rw [ite_eq_left hxS]
      exact hμ1 x hx hxS hxI y hy
    · rw [ite_eq_right hxS]
      exact hμ0 x hx hxS hxI y hy
  have hμcrit : ∀ p ∈ crit, f p ∈ Ioo u v → ∀ᶠ x in 𝓝 p, μ x = μ p := by
    intro p hp hpI
    have hO : IsOpen ((D.chart p hp).χ '' {z | morseNorm n z < ρ p hp}) :=
      (D.chart p hp).isOpen_image_of_lt (hρR' p hp)
    filter_upwards [hO.mem_nhds ((D.chart p hp).p_mem_image_lt (hρpos p hp))] with y hy
    rw [hμconst p hp hpI y hy, hμconst p hp hpI p ((D.chart p hp).p_mem_image_lt (hρpos p hp))]
  obtain ⟨hmodW, -, -, hstrip, hcritIff, hidxEq, hval, -⟩ :=
    rearrange' hf hau.le huv hvb.le hreg E hcrit μ hμ hμ01 hμVE hμcrit ρ₂ hρ₂ hρ₂' hρ₂id h₃
      hρ₂maps
  have hRn : ∀ x hx, 4 * (E.chart x hx).r₀ < ρ x hx / 2 ∧ ρ x hx / 2 ≤ (E.chart x hx).R := by
    intro x hx
    rw [hER x hx]
    exact ⟨by linarith [hEr₀ x hx], by linarith [hρR x hx, hρpos x hx]⟩
  have hrmn : ∀ x hx, 2 * (E.chart x hx).r₀ < ρ x hx / 2 ∧ ρ x hx / 2 ≤ E.rm x hx ∧
      ρ x hx / 2 ≤ ρ x hx / 2 := by
    intro x hx
    rw [(hEr x hx).2]
    exact ⟨by linarith [hEr₀ x hx, (E.chart x hx).hr₀],
      le_min (by linarith [hρsq x hx, hρpos x hx]) (by linarith [hρrm x hx, hρpos x hx]), le_rfl⟩
  have hconst : ∀ p hp, ∀ y, morseNorm n y ≤ ρ p hp / 2 →
      μ ((E.chart p hp).χ y) * (ρ₂ (f ((E.chart p hp).χ y)) - f ((E.chart p hp).χ y)) =
        μ p * (ρ₂ (f p) - f p) ∧
      μ ((E.chart p hp).χ y) * (deriv ρ₂ (f ((E.chart p hp).χ y)) - 1) = 0 := by
    intro p hp y hy
    rw [hEχ p hp]
    have hlev := (D.chart p hp).f_mem_Icc_of_morseNorm_le
      (by linarith [hρR p hp, hρpos p hp] : ρ p hp / 2 ≤ (D.chart p hp).R) hy
    have hq : (ρ p hp / 2) ^ 2 / 2 < ε := by
      have e : (ρ p hp / 2) ^ 2 / 2 = ρ p hp ^ 2 / 8 := by ring
      rw [e]; linarith [(hρ p hp).2.2]
    have hlev' : f ((D.chart p hp).χ y) ∈ Ioo (f p - ε) (f p + ε) :=
      ⟨by linarith [hlev.1], by linarith [hlev.2]⟩
    by_cases hpI : f p ∈ Ioo u v
    · have hyρ : (D.chart p hp).χ y ∈ (D.chart p hp).χ '' {z | morseNorm n z < ρ p hp} :=
        ⟨y, by change morseNorm n y < ρ p hp; linarith [hρpos p hp], rfl⟩
      have hpρ : p ∈ (D.chart p hp).χ '' {z | morseNorm n z < ρ p hp} :=
        (D.chart p hp).p_mem_image_lt (hρpos p hp)
      rw [hμconst p hp hpI _ hyρ, hμconst p hp hpI p hpρ]
      by_cases hpS : p ∈ S
      · rw [ite_eq_left hpS]
        have hps : f p = s₀ := hSlev p hpS
        rw [hps] at hlev'
        have e1 := hρ₂tr (f ((D.chart p hp).χ y)) (Ioo_subset_Icc_self hlev')
        have e2 := hρ₂tr (f p) ⟨by linarith, by linarith⟩
        have e3 := deriv_eq_one_of_translation hρ₂tr hlev'
        rw [e1, e2, e3]
        constructor <;> ring
      · rw [ite_eq_right hpS]
        exact ⟨by ring, by ring⟩
    · have hout : f ((D.chart p hp).χ y) < u + ε ∨ v - ε < f ((D.chart p hp).χ y) := by
        rcases hsep p hp hpI with h | h
        · left; linarith [hlev'.2]
        · right; linarith [hlev'.1]
      have hpout : f p ∉ Ioo (u + ε) (v - ε) := fun h' =>
        hpI ⟨by linarith [h'.1], by linarith [h'.2]⟩
      have e1 : ρ₂ (f ((D.chart p hp).χ y)) = f ((D.chart p hp).χ y) := hρ₂id _ (by
        rcases hout with h | h
        · exact fun h' => absurd h'.1 (not_lt.2 h.le)
        · exact fun h' => absurd h'.2 (not_lt.2 h.le))
      have e2 : ρ₂ (f p) = f p := hρ₂id _ hpout
      have e3 := deriv_eq_one_of_notMem hρ₂id hout
      rw [e1, e2, e3]
      exact ⟨by ring, by ring⟩
  obtain ⟨D', hD'c, hD'rm, φ₂, hφ₂c, ⟨m₂, M₂, hm₂, hφ₂b⟩, hφ₂V⟩ :=
    exists_rescaled hf hau.le huv hvb.le hreg E hcrit μ hμ hμ01 hμVE hμcrit ρ₂ hρ₂ hρ₂' hρ₂id h₃
      hρ₂maps (fun x hx => ρ x hx / 2) (fun x hx => ρ x hx / 2) hRn hrmn hconst
  have hφ₂pos : ∀ x, 0 < φ₂ x := fun x => hm₂.trans_le (hφ₂b x).1
  refine ⟨Rearrange.rearranged f μ ρ₂, hmodW, hstrip,
    ⟨fun x _ => hcritIff x, fun x _ hc => hidxEq x hc⟩, ?_, ?_, D', ?_, ?_, ε₁, hε₁, hε₁ε, ?_⟩
  · intro x hxS
    have hxc := hS x hxS
    have hxs : f x = s₀ := hSlev x hxS
    have hxI : f x ∈ Ioo u v := by rw [hxs]; exact ⟨by linarith, by linarith⟩
    rw [hval x, hμ1 x hxc hxS hxI x ((D.chart x hxc).p_mem_image_lt (hρpos x hxc)),
      hρ₂tr (f x) ⟨by linarith, by linarith⟩, hxs]
    ring
  · intro x hxc hxS
    rw [hval x]
    by_cases hxI : f x ∈ Ioo u v
    · rw [hμ0 x hxc hxS hxI x ((D.chart x hxc).p_mem_image_lt (hρpos x hxc))]; ring
    · have hout : f x ∉ Ioo (u + ε) (v - ε) := fun h' =>
        hxI ⟨by linarith [h'.1], by linarith [h'.2]⟩
      rw [hρ₂id _ hout]; ring
  · refine ⟨fun x => φ₁ x / φ₂ x, hφ₁c.div hφ₂c (fun x => (hφ₂pos x).ne'),
      ⟨m₁ / max M₂ 1, M₁ / m₂, div_pos hm₁ (lt_max_of_lt_right one_pos), fun x => ⟨?_, ?_⟩⟩, fun x => ?_⟩
    · exact div_le_div₀ (hφ₁pos x).le (hφ₁b x).1 (hφ₂pos x)
        ((hφ₂b x).2.trans (le_max_left _ _))
    · exact div_le_div₀ ((hφ₁pos x).le.trans (hφ₁b x).2) (hφ₁b x).2 hm₂ (hφ₂b x).1
    · rw [hφ₁V x, hφ₂V x, smul_smul, div_mul_cancel₀ _ (hφ₂pos x).ne']
  · intro x hx
    refine ⟨(hD'c x hx).1.trans (hEc x hx).1, (hD'c x hx).2.1.trans (hEc x hx).2.1, ?_⟩
    rw [(hD'c x hx).2.2.1]
    exact (hEc x hx).2.2.2.2
  · intro x hx
    rw [(hD'c x hx).2.2.1, hD'rm x hx]
    refine ⟨(hEr x hx).1, ?_⟩
    have e : (ρ x hx / 2) ^ 2 = ρ x hx ^ 2 / 4 := by ring
    rw [e]
    have := hρmsq x hx
    have := pow_pos hρm 2
    linarith

theorem exists_vertical_move {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) {crit : Finset M}
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2)
    (S : Finset M) (hS : ∀ x ∈ S, x ∈ crit) {s₀ u v t : ℝ} (hSlev : ∀ x ∈ S, f x = s₀)
    (hau : a < u) (hvb : v < b) (hs₀ : s₀ ∈ Ioo u v) (ht : t ∈ Ioo u v)
    (hwin : ∀ x ∈ crit, f x ∈ Icc u v → f x = s₀ ∨ f x = t)
    (r' : ∀ x ∈ crit, ℝ) (hr'pos : ∀ x hx, 0 < r' x hx)
    (hnoc : ∀ x (hx : x ∈ crit) y (hy : y ∈ crit), x ∈ S → y ∉ S → f y = t →
      D.noCommon x hx y hy (r' x hx) (r' y hy)) :
    ∃ g : M → ℝ, ModifiedWithin f u v g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      (∀ x ∈ S, g x = t) ∧ (∀ x ∈ crit, x ∉ S → g x = f x) ∧
      ∃ D' : GradientLikeStrip I g a b crit, D'.isRescaleOf D ∧
        (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
          (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
        ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
          (∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm x hx ^ 2) ∧
          ∀ p (hp : p ∈ crit) q (hq : q ∈ crit), D.sardValid ε p hq hp →
            D'.sardValid ε' p hq hp → ∀ c c', D.sardAgree D' ε ε' c c' p hq hp := by
  classical
  let d : M → ℝ := fun x => if f x < u then u - f x else if v < f x then f x - v else 1
  have hdpos : ∀ x, 0 < d x := by
    intro x
    simp only [d]
    split_ifs with h1 h2
    · linarith
    · linarith
    · exact one_pos
  obtain ⟨m, hm0, hm1, hm⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ x (hx : x ∈ crit), m ≤ r' x hx ∧ m ≤ d x := by
    let e : {x // x ∈ crit} → ℝ := fun x => min (r' x.1 x.2) (d x.1)
    let T : Finset ℝ := insert 1 (crit.attach.image e)
    have hT : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
    refine ⟨T.min' hT, ?_, ?_, ?_⟩
    · have hmem := Finset.min'_mem T hT
      rcases Finset.mem_insert.1 hmem with h | h
      · rw [h]; exact one_pos
      · obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
        rw [← hx]
        exact lt_min (hr'pos x.1 x.2) (hdpos x.1)
    · exact Finset.min'_le T 1 (Finset.mem_insert_self _ _)
    · intro x hx
      have hle : T.min' hT ≤ e ⟨x, hx⟩ :=
        Finset.min'_le T _ (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem e (Finset.mem_attach _ _)))
      exact ⟨hle.trans (min_le_left _ _), hle.trans (min_le_right _ _)⟩
  obtain ⟨hs₀u, hs₀v⟩ := hs₀
  obtain ⟨htu, htv⟩ := ht
  set w : ℝ := min (min (s₀ - u) (t - u)) (min (v - s₀) (v - t)) with hw_def
  have hw0 : 0 < w := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) (by linarith))
  have hw1 : w ≤ s₀ - u := (min_le_left _ _).trans (min_le_left _ _)
  have hw2 : w ≤ t - u := (min_le_left _ _).trans (min_le_right _ _)
  have hw3 : w ≤ v - s₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hw4 : w ≤ v - t := (min_le_right _ _).trans (min_le_right _ _)
  set δ : ℝ := min (min m ε) w / 4 with hδ_def
  have hδ0 : 0 < δ := by
    have : 0 < min (min m ε) w := lt_min (lt_min hm0 hε) hw0
    positivity
  have hδm : δ ≤ m / 4 := by
    have : min (min m ε) w ≤ m := (min_le_left _ _).trans (min_le_left _ _)
    rw [hδ_def]; linarith
  have hδε : δ ≤ ε / 4 := by
    have : min (min m ε) w ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
    rw [hδ_def]; linarith
  have hδw : δ ≤ w / 4 := by
    have : min (min m ε) w ≤ w := min_le_right _ _
    rw [hδ_def]; linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  set ε₂ : ℝ := δ ^ 2 with hε₂_def
  have hε₂0 : 0 < ε₂ := by positivity
  have hε₂ε : ε₂ ≤ ε := by linarith
  set ρ : ℝ := 8 * ε + 1 with hρ_def
  have hρ0 : 0 < ρ := by positivity
  have hρ8 : 8 * ε < ρ ^ 2 := by nlinarith
  obtain ⟨D₁, hresc₁, hchart₁, hr₀₁, -⟩ := GradientLikeStrip.exists_shrink_field hf.smooth D
    (ε₁ := ε₂ / 2) (ρ := ρ) (by positivity) hρ0 (by linarith)
    (fun x hx => by have := (hεr x hx).2; linarith)
  have hεr₁ : ∀ x hx, (D₁.chart x hx).r₀ ^ 2 < 2 * ε₂ ∧ 8 * ε₂ < D₁.rm x hx ^ 2 := by
    intro x hx
    refine ⟨by have := (hr₀₁ x hx).1; linarith, ?_⟩
    rw [(hr₀₁ x hx).2]
    rcases min_choice ρ (D.rm x hx) with h | h
    · rw [h]; linarith
    · rw [h]; have := (hεr x hx).2; linarith
  have hr₀δ : ∀ x hx, (D₁.chart x hx).r₀ < δ := by
    intro x hx
    have h1 : (D₁.chart x hx).r₀ ^ 2 < δ ^ 2 := by have := (hr₀₁ x hx).1; linarith
    exact lt_of_abs_lt (abs_lt_of_sq_lt_sq h1 hδ0.le)
  have hnoc₁ : ∀ x (hx : x ∈ crit) y (hy : y ∈ crit), x ∈ S → y ∉ S → f y ∈ Icc u v →
      D₁.noCommon x hx y hy ((fun _ _ => δ : ∀ x ∈ crit, ℝ) x hx)
        ((fun _ _ => δ : ∀ x ∈ crit, ℝ) y hy) := by
    intro x hx y hy hxS hyS hyw
    rcases hwin y hy hyw with hys | hyt
    · have hxy : x ≠ y := fun h => hyS (h ▸ hxS)
      exact GradientLikeStrip.noCommon_sameLevel hf.smooth D₁ hε₂0 hεr₁ hx hy hxy
        ((hSlev x hxS).trans hys.symm) (by nlinarith) (by nlinarith)
    · have h₀ := GradientLikeStrip.noCommon.of_rescale hresc₁ (fun z hz => (hchart₁ z hz).1)
        (hnoc x hx y hy hxS hyS hyt)
      intro z hz s hs
      apply h₀ z _ s _
      · obtain ⟨w', hw', rfl⟩ := hz
        exact ⟨w', lt_of_lt_of_le hw' (by have := (hm x hx).1; change δ ≤ r' x hx; linarith), rfl⟩
      · obtain ⟨w', hw', hw''⟩ := hs
        exact ⟨w', lt_of_lt_of_le hw' (by have := (hm y hy).1; change δ ≤ r' y hy; linarith),
          hw''⟩
  have hin : u + 2 * ε₂ < min s₀ t ∧ max s₀ t < v - 2 * ε₂ := by
    refine ⟨lt_min (by linarith) (by linarith), max_lt (by linarith) (by linarith)⟩
  have hsep : ∀ x ∈ crit, f x ∉ Ioo u v → f x + 2 * ε₂ ≤ u ∨ v ≤ f x - 2 * ε₂ := by
    intro x hx hxw
    have hdx := (hm x hx).2
    by_cases h1 : f x < u
    · left
      have : d x = u - f x := by simp [d, h1]
      linarith
    · have h2 : v < f x := by
        by_contra h2
        rcases hwin x hx ⟨not_lt.mp h1, not_lt.mp h2⟩ with h | h
        · exact hxw (h ▸ ⟨hs₀u, hs₀v⟩)
        · exact hxw (h ▸ ⟨htu, htv⟩)
      right
      have : d x = f x - v := by simp [d, h1, h2]
      linarith
  obtain ⟨g, hmod, hg, hsame, hgS, hgn, D', hresc', hchart', ε', hε'0, hε'ε₂, hεr'⟩ :=
    exists_move_core I hf hcrit D₁ hε₂0 hεr₁ S hS hSlev hau hvb hin hsep hwin
      (fun _ _ => δ) (fun x hx => ⟨hr₀δ x hx, by nlinarith⟩) hnoc₁
  have hresc : D'.isRescaleOf D := by
    obtain ⟨φ₁, hφ₁c, ⟨m₁, M₁, hm₁, hφ₁b⟩, hφ₁⟩ := hresc₁
    obtain ⟨φ₂, hφ₂c, ⟨m₂, M₂, hm₂, hφ₂b⟩, hφ₂⟩ := hresc'
    refine ⟨fun x => φ₁ x * φ₂ x, hφ₁c.mul hφ₂c, ⟨m₁ * m₂, M₁ * M₂, mul_pos hm₁ hm₂,
      fun x => ?_⟩, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := hφ₁b x
      obtain ⟨h3, h4⟩ := hφ₂b x
      exact ⟨mul_le_mul h1 h3 hm₂.le (hm₁.le.trans h1),
        mul_le_mul h2 h4 (hm₂.le.trans h3) ((hm₁.le.trans h1).trans h2)⟩
    · rw [hφ₁ x, hφ₂ x, smul_smul]
  have hχ : ∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧
      (D'.chart x hx).k = (D.chart x hx).k ∧ (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀ := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hchart' x hx
    obtain ⟨h4, h5, -, -, h6⟩ := hchart₁ x hx
    exact ⟨h1.trans h4, h2.trans h5, h3.trans h6⟩
  refine ⟨g, hmod, hg, hsame, hgS, hgn, D', hresc, hχ, ε', hε'0, hε'ε₂.trans hε₂ε, hεr', ?_⟩
  intro p hp q hq hv hv' c c'
  exact GradientLikeStrip.sardAgree_of_rescale hf.smooth hg.smooth D D' hresc
    (fun x hx => ⟨(hχ x hx).1, (hχ x hx).2.1⟩) (hε'ε₂.trans hε₂ε) hp hq hv hv' c c'

end Moves

end

end DifferentialGeometry.Topology
