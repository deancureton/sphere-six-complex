module

public import DifferentialGeometry.Topology.Morse.Strip.TrajectoryCutoff

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le negPart posPart morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace ModelField

variable {k : ℕ} (hk : k ≤ n)

theorem normSq_posPart_mul_le {r₀ θ₀ : ℝ} (hr₀ : 0 < r₀) {γ : ℝ → Fin n → ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ t ∈ Icc 0 T, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hθ : ∀ t ∈ Icc 0 T, θ₀ ≤ theta r₀ (γ t)) :
    ‖posPart hk (γ T)‖ ^ 2 * (1 + 2 * θ₀ * T) ≤ ‖posPart hk (γ 0)‖ ^ 2 := by
  have hanti := normSq_posPart_antitoneOn hk hr₀ hγ
  have hc0 : 0 ≤ ‖posPart hk (γ T)‖ ^ 2 := sq_nonneg _
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt
      (fun s => ‖posPart hk (γ s)‖ ^ 2 + 2 * θ₀ * ‖posPart hk (γ T)‖ ^ 2 * s)
      (-(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2) + 2 * θ₀ * ‖posPart hk (γ T)‖ ^ 2) t := by
    intro t ht
    have := (hasDerivAt_normSq_posPart_curve hk hγ ht).add
      ((hasDerivAt_id' (x := t)).const_mul (2 * θ₀ * ‖posPart hk (γ T)‖ ^ 2))
    rw [mul_one] at this
    exact this
  have hm : AntitoneOn
      (fun s => ‖posPart hk (γ s)‖ ^ 2 + 2 * θ₀ * ‖posPart hk (γ T)‖ ^ 2 * s) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun t => -(2 * theta r₀ (γ t) * ‖posPart hk (γ t)‖ ^ 2) +
        2 * θ₀ * ‖posPart hk (γ T)‖ ^ 2)
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have ht' := Ioo_subset_Icc_self ht
      have h1 := hθ t ht'
      have h2 : ‖posPart hk (γ T)‖ ^ 2 ≤ ‖posPart hk (γ t)‖ ^ 2 :=
        hanti ht' (right_mem_Icc.2 hT) ht'.2
      have h4 : 0 ≤ theta r₀ (γ t) := (theta_pos hr₀ _).le
      nlinarith [mul_le_mul h1 h2 hc0 h4]
  have := hm (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
  simp only [mul_zero, add_zero] at this
  linarith

end ModelField

namespace GradientLikeStrip

variable (D : GradientLikeStrip I f a b crit) [T2Space M] [I.Boundaryless]

def bottom : Set M := {x | ∃ t, 0 ≤ t ∧ f (D.flow t x) < a}

def basin (p : M) (hp : p ∈ crit) : Set M :=
  {x | ∃ t, 0 ≤ t ∧ D.flow t x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}}

def captured (r : M) (hr : r ∈ crit) : Set M :=
  {x | ∃ T, D.flow T x ∈ (D.chart r hr).χ ''
    {y | morseNorm n y < D.rm r hr ∧ negPart (D.chart r hr).hk y = 0}}

omit [T2Space M] [I.Boundaryless] in
theorem modelBall_subset_strip (p : M) (hp : p ∈ crit) :
    (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} ⊆ f ⁻¹' Ioo a b :=
  (D.modelBall_subset_image_ball p hp).trans (D.inStrip p hp)

theorem isOpen_bottom (hf : Continuous f) : IsOpen D.bottom := by
  have : D.bottom = ⋃ t ∈ Ici (0 : ℝ), D.flow t ⁻¹' (f ⁻¹' Iio a) := by
    ext x
    simp only [bottom, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_Iio, mem_Ici, exists_prop]
  rw [this]
  exact isOpen_biUnion fun t _ => (isOpen_Iio.preimage hf).preimage (D.continuous_flow t)

theorem isOpen_basin (p : M) (hp : p ∈ crit) : IsOpen (D.basin p hp) := by
  have : D.basin p hp = ⋃ t ∈ Ici (0 : ℝ),
      D.flow t ⁻¹' ((D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) := by
    ext x
    simp only [basin, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_Ici, exists_prop]
  rw [this]
  exact isOpen_biUnion fun t _ => (D.isOpen_modelBall p hp).preimage (D.continuous_flow t)

variable {D}

theorem mem_bottom_of_lt {x : M} (hx : f x < a) : x ∈ D.bottom :=
  ⟨0, le_rfl, by rwa [flow_zero]⟩

theorem mem_bottom_of_flow_mem {x : M} {t : ℝ} (ht : 0 ≤ t) (h : D.flow t x ∈ D.bottom) :
    x ∈ D.bottom := by
  obtain ⟨s, hs, hlt⟩ := h
  exact ⟨t + s, add_nonneg ht hs, by rwa [flow_flow] at hlt⟩

theorem flow_mem_bottom_of_mem (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (h : x ∈ D.bottom)
    (t : ℝ) : D.flow t x ∈ D.bottom := by
  obtain ⟨s, hs, hlt⟩ := h
  rcases le_or_gt t s with hts | hts
  · refine ⟨s - t, sub_nonneg.2 hts, ?_⟩
    rwa [flow_flow, add_sub_cancel]
  · refine ⟨0, le_rfl, ?_⟩
    rw [flow_zero]
    exact lt_of_le_of_lt (f_flow_antitone hf x hts.le) hlt

theorem flow_mem_bottom_iff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (t : ℝ) :
    D.flow t x ∈ D.bottom ↔ x ∈ D.bottom := by
  refine ⟨fun h => ?_, fun h => flow_mem_bottom_of_mem hf h t⟩
  have := flow_mem_bottom_of_mem hf h (-t)
  rwa [flow_neg_flow] at this

theorem mem_basin_of_flow_mem {p : M} {hp : p ∈ crit} {x : M} {t : ℝ} (ht : 0 ≤ t)
    (h : D.flow t x ∈ D.basin p hp) : x ∈ D.basin p hp := by
  obtain ⟨s, hs, hmem⟩ := h
  exact ⟨t + s, add_nonneg ht hs, by rwa [flow_flow] at hmem⟩

theorem modelBall_subset_basin (p : M) (hp : p ∈ crit) :
    (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} ⊆ D.basin p hp :=
  fun x hx => ⟨0, le_rfl, by rwa [flow_zero]⟩

theorem crit_mem_basin (p : M) (hp : p ∈ crit) : p ∈ D.basin p hp :=
  modelBall_subset_basin p hp ((D.chart p hp).p_mem_image_lt (D.rm_pos p hp))

theorem flow_mem_captured_iff {r : M} {hr : r ∈ crit} {x : M} (t : ℝ) :
    D.flow t x ∈ D.captured r hr ↔ x ∈ D.captured r hr := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨t + T, by rwa [flow_flow] at hT⟩
  · rintro ⟨T, hT⟩
    refine ⟨T - t, ?_⟩
    rwa [flow_flow, add_sub_cancel]

theorem mem_captured_of_mem_stable {r : M} {hr : r ∈ crit} {x : M}
    (hx : x ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < D.rm r hr ∧ negPart (D.chart r hr).hk y = 0}) :
    x ∈ D.captured r hr :=
  ⟨0, by rwa [flow_zero]⟩

theorem crit_mem_captured (r : M) (hr : r ∈ crit) : r ∈ D.captured r hr :=
  mem_captured_of_mem_stable ⟨0, ⟨by rw [morseNorm_zero]; exact D.rm_pos r hr,
    (ModelField.negPartL (D.chart r hr).hk).map_zero⟩, (D.chart r hr).hχ0⟩

theorem mem_captured_iff_eventually {r : M} {hr : r ∈ crit} {x : M} :
    x ∈ D.captured r hr ↔ ∃ T, ∀ t, T ≤ t → D.flow t x ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < D.rm r hr ∧ negPart (D.chart r hr).hk y = 0} := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨y, ⟨hy1, hy2⟩, hyx⟩ := hT
    refine ⟨T, fun t ht => ?_⟩
    have := flow_mem_of_negPart_eq_zero hr hy1 hy2 (t := t - T) (by linarith)
    rw [hyx, flow_flow, add_sub_cancel] at this
    refine image_mono ?_ this
    rintro z ⟨hz1, hz2⟩
    exact ⟨lt_of_le_of_lt hz1 hy1, hz2⟩
  · rintro ⟨T, hT⟩
    exact ⟨T, hT T le_rfl⟩

theorem modelBall_forward_invariant_of_index_zero {p : M} {hp : p ∈ crit}
    (hk : (D.chart p hp).k = 0) {y : Fin n → ℝ} (hy : morseNorm n y < D.rm p hp) {t : ℝ}
    (ht : 0 ≤ t) :
    D.flow t ((D.chart p hp).χ y) ∈ (D.chart p hp).χ '' {z | morseNorm n z ≤ morseNorm n y} := by
  have hu : negPart (D.chart p hp).hk y = 0 := by
    ext i
    have := i.isLt
    omega
  exact image_mono (fun z hz => hz.1) (flow_mem_of_negPart_eq_zero hp hy hu ht)

theorem flow_mem_modelBall_of_index_zero {p : M} {hp : p ∈ crit}
    (hk : (D.chart p hp).k = 0) {x : M}
    (hx : x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) {t : ℝ} (ht : 0 ≤ t) :
    D.flow t x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact image_mono (fun z (hz : morseNorm n z ≤ morseNorm n y) => lt_of_le_of_lt hz hy)
    (modelBall_forward_invariant_of_index_zero hk hy ht)

theorem flow_mem_basin_of_mem {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0) {x : M}
    (h : x ∈ D.basin p hp) (t : ℝ) : D.flow t x ∈ D.basin p hp := by
  obtain ⟨s, hs, hmem⟩ := h
  rcases le_or_gt t s with hts | hts
  · refine ⟨s - t, sub_nonneg.2 hts, ?_⟩
    rwa [flow_flow, add_sub_cancel]
  · refine ⟨0, le_rfl, ?_⟩
    rw [flow_zero]
    have := flow_mem_modelBall_of_index_zero hk hmem (t := t - s) (by linarith)
    rwa [flow_flow, add_sub_cancel] at this

theorem flow_mem_basin_iff {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0) {x : M}
    (t : ℝ) : D.flow t x ∈ D.basin p hp ↔ x ∈ D.basin p hp := by
  refine ⟨fun h => ?_, fun h => flow_mem_basin_of_mem hk h t⟩
  have := flow_mem_basin_of_mem hk h (-t)
  rwa [flow_neg_flow] at this

theorem captured_index_zero_eq_basin {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0) :
    D.captured p hp = D.basin p hp := by
  ext x
  constructor
  · rintro ⟨T, hT⟩
    have hT' : D.flow T x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} :=
      image_mono (fun z hz => hz.1) hT
    rcases le_or_gt 0 T with h | h
    · exact ⟨T, h, hT'⟩
    · refine ⟨0, le_rfl, ?_⟩
      have := flow_mem_modelBall_of_index_zero hk hT' (t := -T) (by linarith)
      rwa [flow_neg_flow, ← flow_zero (D := D) x] at this
  · rintro ⟨t, -, y, hy, hyx⟩
    refine ⟨t, y, ⟨hy, ?_⟩, hyx⟩
    ext i
    have := i.isLt
    omega

theorem disjoint_bottom_basin (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} {hp : p ∈ crit}
    (hk : (D.chart p hp).k = 0) : Disjoint D.bottom (D.basin p hp) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs, hlt⟩ hxb
  have hmem := flow_mem_basin_of_mem hk hxb s
  obtain ⟨t, ht, hmem⟩ := hmem
  have h1 : f (D.flow t (D.flow s x)) ∈ Ioo a b := D.modelBall_subset_strip p hp hmem
  have h2 : f (D.flow t (D.flow s x)) ≤ f (D.flow s x) := f_flow_le hf _ ht
  linarith [h1.1]

theorem disjoint_basin_basin {p q : M} {hp : p ∈ crit} {hq : q ∈ crit}
    (hk : (D.chart p hp).k = 0) (hk' : (D.chart q hq).k = 0) (hpq : p ≠ q) :
    Disjoint (D.basin p hp) (D.basin q hq) := by
  rw [Set.disjoint_left]
  rintro x hxp hxq
  obtain ⟨s, hs, hmem⟩ := hxp
  have hxq' := flow_mem_basin_of_mem hk' hxq s
  obtain ⟨t, ht, hmemq⟩ := hxq'
  have hmemp := flow_mem_modelBall_of_index_zero hk hmem ht
  exact Set.disjoint_left.1 (D.disjoint p hp q hq hpq) (D.modelBall_subset_image_ball p hp hmemp)
    (D.modelBall_subset_image_ball q hq hmemq)

theorem eventually_f_flow_lt (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : dfV I f D.V x = -1) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (D.flow t x) < f x := by
  have hd : HasDerivAt (fun s => f (D.flow s x)) (-1) 0 := by
    have := hasDerivAt_f_flow (D := D) hf x 0
    rwa [flow_zero, hx] at this
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope (fun s => f (D.flow s x)) 0 t < 0 :=
    (tendsto_order.1 hd).2 0 (by norm_num)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (fun s => f (D.flow s x)) 0 t < 0 :=
    h1.filter_mono (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
  filter_upwards [h2, self_mem_nhdsWithin] with t ht ht0
  have ht0' : (0 : ℝ) < t := ht0
  rw [slope_def_field, sub_zero, flow_zero] at ht
  have := (div_lt_iff₀ ht0').1 ht
  linarith

theorem mem_bottom_of_le (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a ≤ b) {x : M} (hx : f x ≤ a) :
    x ∈ D.bottom := by
  rcases hx.lt_or_eq with h | h
  · exact mem_bottom_of_lt h
  have hunit : dfV I f D.V x = -1 :=
    D.unit x ⟨h.ge, h.le.trans hab⟩ fun p hp hmem =>
      (D.inStrip p hp (D.smallBall_subset_image_ball p hp hmem)).1.ne' h
  obtain ⟨t, ht, ht0⟩ := ((eventually_f_flow_lt hf hunit).and self_mem_nhdsWithin).exists
  exact ⟨t, le_of_lt ht0, ht.trans_eq h⟩

theorem exists_exit_mem_leftTube (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hq : q ∈ crit)
    {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ}
    (hball : 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 < D.rm q hq ^ 2)
    (hu : negPart (D.chart q hq).hk y ≠ 0)
    (hlevel : f q - ε ≤ morseNormalForm (D.chart q hq).hk (f q) y) {ρ : ℝ}
    (hρ : 4 * (‖negPart (D.chart q hq).hk y‖ ^ 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2) ≤
      ρ ^ 4) :
    ∃ t, 0 ≤ t ∧ f (D.flow t ((D.chart q hq).χ y)) = f q - ε ∧
      (∀ s ∈ Icc 0 t, D.flow s ((D.chart q hq).χ y) ∈ (D.chart q hq).χ ''
        {z | morseNorm n z ^ 2 ≤ 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2}) ∧
      D.flow t ((D.chart q hq).χ y) ∈ (D.chart q hq).χ '' (D.chart q hq).leftTube ε ρ := by
  set d := D.chart q hq with hd
  obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hq hε hball hu hlevel
  refine ⟨t, ht0, hft, hstay, ?_⟩
  have hrm0 := D.rm_pos q hq
  set B := 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 with hB
  have hSsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤ B} ⊆ {z | morseNorm n z < D.rm q hq} :=
    fun z hz => lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hz hball)
  have hODE : ∀ u ∈ Icc 0 t, D.flow u (d.χ y) ∈ d.χ '' {z | morseNorm n z < D.rm q hq} :=
    fun u hu => image_mono hSsub (hstay u hu)
  have hγ := hasDerivAt_symm_flow_Icc hq hODE
  have hyS : morseNorm n y ^ 2 ≤ B := by
    rw [morseNormalForm_split] at hlevel
    rw [morseNorm_sq_eq_negPart_add_posPart d.hk]
    linarith
  have hyrm : morseNorm n y < D.rm q hq := hSsub hyS
  have hyR : morseNorm n y ≤ d.R := hyrm.le.trans (D.hrm q hq).2
  have hγ0 : d.χ.symm (D.flow 0 (d.χ y)) = y := by
    rw [flow_zero, d.χ.left_inv (d.hsrc y hyR)]
  have hprod := ModelField.normSq_negPart_mul_posPart_const d.hk hγ t (right_mem_Icc.2 ht0)
  rw [hγ0] at hprod
  have heO : D.flow t (d.χ y) ∈ d.χ '' {z | morseNorm n z < D.rm q hq} :=
    hODE t (right_mem_Icc.2 ht0)
  have heball := D.modelBall_subset_image_ball q hq heO
  have hez := D.modelBall_subset_image_le q hq heO
  have hfe : f (D.flow t (d.χ y)) = morseNormalForm d.hk (f q) (d.χ.symm (D.flow t (d.χ y))) :=
    d.f_eq_nf_symm hez
  refine d.mem_image_of_symm_mem heball ⟨by rw [← hfe]; exact hft, ?_⟩
  rw [hprod]
  exact hρ

theorem exists_exit_mem_leftTube_of_le (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hq : q ∈ crit)
    {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ}
    (hball : 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 < D.rm q hq ^ 2)
    (hu : negPart (D.chart q hq).hk y ≠ 0)
    (hlevel : f q - ε ≤ morseNormalForm (D.chart q hq).hk (f q) y) {ρ : ℝ}
    (hρ : morseNorm n y ≤ ρ) :
    ∃ t, 0 ≤ t ∧ f (D.flow t ((D.chart q hq).χ y)) = f q - ε ∧
      (∀ s ∈ Icc 0 t, D.flow s ((D.chart q hq).χ y) ∈ (D.chart q hq).χ ''
        {z | morseNorm n z ^ 2 ≤ 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2}) ∧
      D.flow t ((D.chart q hq).χ y) ∈ (D.chart q hq).χ '' (D.chart q hq).leftTube ε ρ := by
  refine exists_exit_mem_leftTube hf hq hε hball hu hlevel ?_
  have h2 := prod_le_morseNorm_pow_four (D.chart q hq) y
  have h3 : morseNorm n y ^ 4 ≤ ρ ^ 4 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hρ 4
  linarith

theorem trichotomy (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) {x : M}
    (hx : f x ∈ Icc a b) : x ∈ D.bottom ∨ ∃ r hr, x ∈ D.captured r hr := by
  classical
  have hab : a ≤ b := hx.1.trans hx.2
  have key : ∀ N : ℕ, ∀ x, f x ∈ Ioo a b → (crit.filter (fun r => f r - ε < f x)).card = N →
      x ∈ D.bottom ∨ ∃ r hr, x ∈ D.captured r hr := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro x hx hN
    have hr'gt : ∀ p (hp : p ∈ crit), (D.chart p hp).r₀ < Real.sqrt (2 * ε) := fun p hp =>
      (Real.lt_sqrt (D.chart p hp).hr₀.le).2 (hεr p hp).1
    rcases D.mem_regularFlowDomain_or_exists_throughBall (c := a) (fun _ _ => Real.sqrt (2 * ε)) hr'gt hx with
      hΩ | ⟨r, hr, hthr⟩
    · left
      have h1 := f_flow_eq_sub_of_mem_regularFlowDomain hf (left_mem_Icc.2 hab) hΩ _ right_mem_uIcc
      refine mem_bottom_of_flow_mem (t := f x - a) (by linarith [hx.1])
        (mem_bottom_of_le hf hab ?_)
      rw [h1]
      linarith
    · obtain ⟨-, s, hs, hmem⟩ := hthr
      rw [uIcc_of_le (by linarith [hx.1])] at hs
      obtain ⟨y, hy, hyx⟩ := hmem
      set d := D.chart r hr with hd
      have hy' : morseNorm n y < Real.sqrt (2 * ε) := hy
      have hysq : morseNorm n y ^ 2 < 2 * ε :=
        (Real.lt_sqrt (ModelField.morseNorm_nonneg y)).1 hy'
      have hsq := morseNorm_sq_eq_negPart_add_posPart d.hk y
      have hrm0 := D.rm_pos r hr
      have hrm8 := (hεr r hr).2
      have hyrm : morseNorm n y < D.rm r hr := by
        apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
        linarith
      have hyR : morseNorm n y ≤ d.R := hyrm.le.trans (D.hrm r hr).2
      by_cases hu0 : negPart d.hk y = 0
      · right
        exact ⟨r, hr, (flow_mem_captured_iff s).1 (mem_captured_of_mem_stable
          ⟨y, ⟨hyrm, hu0⟩, hyx⟩)⟩
      · have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm r hr ^ 2 := by
          nlinarith [sq_nonneg ‖negPart d.hk y‖]
        have hnfy : f r - ε < morseNormalForm d.hk (f r) y := by
          rw [morseNormalForm_split]
          nlinarith [sq_nonneg ‖posPart d.hk y‖]
        obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hr hε hball hu0 hnfy.le
        rw [hyx] at hft hstay
        have hfxs : f (D.flow s x) = morseNormalForm d.hk (f r) y := by
          rw [← hyx]; exact d.hnorm y hyR
        have hfx_gt : f r - ε < f x :=
          hnfy.trans_le (hfxs ▸ f_flow_le hf x hs.1)
        have hst : 0 ≤ s + t := add_nonneg hs.1 ht0
        have hflow : D.flow t (D.flow s x) = D.flow (s + t) x := D.flow_flow x s t
        rw [hflow] at hft
        have hx' : f (D.flow (s + t) x) ∈ Ioo a b := by
          have := hstay t (right_mem_Icc.2 ht0)
          rw [hflow] at this
          refine D.modelBall_subset_strip r hr (image_mono ?_ this)
          intro z hz
          exact lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hz hball)
        have hsub : crit.filter (fun r => f r - ε < f (D.flow (s + t) x)) ⊆
            crit.filter (fun r => f r - ε < f x) := by
          intro q
          simp only [Finset.mem_filter]
          rintro ⟨hq, hlt⟩
          exact ⟨hq, hlt.trans_le (f_flow_le hf x hst)⟩
        have hss : crit.filter (fun r => f r - ε < f (D.flow (s + t) x)) ⊂
            crit.filter (fun r => f r - ε < f x) := by
          rw [Finset.ssubset_iff_of_subset hsub]
          refine ⟨r, ?_, ?_⟩
          · simp only [Finset.mem_filter]
            exact ⟨hr, hfx_gt⟩
          · simp only [Finset.mem_filter, not_and, not_lt]
            intro _
            rw [hft]
        have hlt := Finset.card_lt_card hss
        rw [hN] at hlt
        rcases ih _ hlt _ hx' rfl with hb | ⟨r'', hr'', hc⟩
        · exact Or.inl (mem_bottom_of_flow_mem hst hb)
        · exact Or.inr ⟨r'', hr'', (flow_mem_captured_iff (s + t)).1 hc⟩
  rcases hx.1.lt_or_eq with hlt | heq
  · rcases hx.2.lt_or_eq with hlt' | heq'
    · exact key _ x ⟨hlt, hlt'⟩ rfl
    · have hunit : dfV I f D.V x = -1 :=
        D.unit x hx fun p hp hmem =>
          (D.inStrip p hp (D.smallBall_subset_image_ball p hp hmem)).2.ne heq'
      obtain ⟨t, ht, ht0⟩ :=
        ((eventually_f_flow_lt hf hunit).and (Ioo_mem_nhdsGT (sub_pos.2 hlt))).exists
      have hx' : f (D.flow t x) ∈ Ioo a b :=
        ⟨by linarith [sub_le_f_flow (D := D) hf x ht0.1.le, ht0.2], ht.trans_eq heq'⟩
      rcases key _ _ hx' rfl with hb | ⟨r, hr, hc⟩
      · exact Or.inl (mem_bottom_of_flow_mem ht0.1.le hb)
      · exact Or.inr ⟨r, hr, (flow_mem_captured_iff t).1 hc⟩
  · exact Or.inl (mem_bottom_of_le hf hab heq.ge)

theorem leftSphere_self_level (r : M) (hr : r ∈ crit) (ε : ℝ) :
    D.leftSphere r hr ε (f r - ε) = (D.chart r hr).χ '' (D.chart r hr).leftModelSphere ε := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [sub_self, flow_zero]
  · intro hx
    exact ⟨x, hx, by rw [sub_self, flow_zero]⟩

theorem leftThick_self_level (r : M) (hr : r ∈ crit) (ε ρ : ℝ) :
    D.leftThick r hr ε (f r - ε) ρ = (D.chart r hr).χ '' (D.chart r hr).leftTube ε ρ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [sub_self, flow_zero]
  · intro hx
    exact ⟨x, hx, by rw [sub_self, flow_zero]⟩

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem leftTube_zero_subset {q : M} (d : MorseNormalChart I f q) {ε : ℝ} (hε : 0 < ε) :
    d.leftTube ε 0 ⊆ d.leftModelSphere ε := by
  rintro z ⟨hz1, hz2⟩
  have h1 := d.normSq_negPart_of_mem_leftTube ⟨hz1, hz2⟩
  have hv : ‖posPart d.hk z‖ ^ 2 = 0 := by
    have h0 : (0 : ℝ) ^ 4 = 0 := by norm_num
    rw [h0] at hz2
    nlinarith [sq_nonneg ‖posPart d.hk z‖, sq_nonneg ‖negPart d.hk z‖,
      mul_nonneg (sq_nonneg ‖negPart d.hk z‖) (sq_nonneg ‖posPart d.hk z‖)]
  refine ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hv), ?_⟩
  rw [h1, hv, add_zero]

theorem exists_uniform_exit_of_small_negPart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (r : M)
    (hr : r ∈ crit) {ε : ℝ} (hε : 0 < ε) (hrm : 8 * ε < D.rm r hr ^ 2) {U : Set M}
    (hU : IsOpen U) (hUS : D.leftSphere r hr ε (f r - ε) ⊆ U) :
    ∃ δ > 0, ∀ y, morseNorm n y ^ 2 < 2 * ε → ‖negPart (D.chart r hr).hk y‖ < δ →
      negPart (D.chart r hr).hk y ≠ 0 →
      ∃ t, 0 ≤ t ∧ D.flow t ((D.chart r hr).χ y) ∈ U ∧
        f (D.flow t ((D.chart r hr).χ y)) = f r - ε := by
  set d := D.chart r hr with hd
  have hrm0 := D.rm_pos r hr
  have hR : 3 * ε ≤ d.R ^ 2 := by
    have h2 : D.rm r hr ^ 2 ≤ d.R ^ 2 := pow_le_pow_left₀ hrm0.le (D.hrm r hr).2 2
    linarith
  have hsub : D.leftThick r hr ε (f r - ε) 0 ⊆ U := by
    rw [leftThick_self_level]
    refine (image_mono (leftTube_zero_subset d hε)).trans ?_
    rwa [← leftSphere_self_level]
  have hsqrt : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by positivity)
  have hsqrt2 : Real.sqrt (2 * ε) ^ 2 ≤ 2 * ε := by
    rw [Real.sq_sqrt (by positivity)]
  obtain ⟨ρ, ⟨hρ0, -⟩, hρU⟩ := D.exists_leftThick_subset r hr hε le_rfl hsqrt hsqrt2 hR
    (f r - ε) hU hsub
  refine ⟨ρ ^ 2 / Real.sqrt (8 * ε), by positivity, fun y hysq hu hu0 => ?_⟩
  have hsq := morseNorm_sq_eq_negPart_add_posPart d.hk y
  have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm r hr ^ 2 := by
    nlinarith [sq_nonneg ‖negPart d.hk y‖]
  have hnfy : f r - ε < morseNormalForm d.hk (f r) y := by
    rw [morseNormalForm_split]
    nlinarith [sq_nonneg ‖posPart d.hk y‖]
  have hprod : 4 * (‖negPart d.hk y‖ ^ 2 * ‖posPart d.hk y‖ ^ 2) ≤ ρ ^ 4 := by
    have h8 : 0 < Real.sqrt (8 * ε) := Real.sqrt_pos.2 (by positivity)
    have hu' : ‖negPart d.hk y‖ * Real.sqrt (8 * ε) < ρ ^ 2 := by
      rwa [lt_div_iff₀ h8] at hu
    have hu2 : (‖negPart d.hk y‖ * Real.sqrt (8 * ε)) ^ 2 < (ρ ^ 2) ^ 2 :=
      pow_lt_pow_left₀ hu' (by positivity) two_ne_zero
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hu2
    have hv : ‖posPart d.hk y‖ ^ 2 ≤ 2 * ε := by nlinarith [sq_nonneg ‖negPart d.hk y‖]
    have hu0' : 0 ≤ ‖negPart d.hk y‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hv hu0']
  obtain ⟨t, ht0, hft, -, hmem⟩ := exists_exit_mem_leftTube hf hr hε hball hu0 hnfy.le hprod
  refine ⟨t, ht0, hρU ?_, hft⟩
  rw [leftThick_self_level]
  exact hmem

theorem exists_uniform_exit (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (r : M) (hr : r ∈ crit) {ε : ℝ}
    (hε : 0 < ε) (hrm : 8 * ε < D.rm r hr ^ 2) {U : Set M} (hU : IsOpen U)
    (hUS : D.leftSphere r hr ε (f r - ε) ⊆ U) :
    ∃ ρ > 0, ∀ y, morseNorm n y < ρ → negPart (D.chart r hr).hk y ≠ 0 →
      ∃ t, 0 ≤ t ∧ D.flow t ((D.chart r hr).χ y) ∈ U ∧
        f (D.flow t ((D.chart r hr).χ y)) = f r - ε := by
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_exit_of_small_negPart hf r hr hε hrm hU hUS
  have hsqrt : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by positivity)
  refine ⟨min δ (Real.sqrt (2 * ε)), lt_min hδ hsqrt, fun y hy hu => ?_⟩
  have hy1 : morseNorm n y < δ := hy.trans_le (min_le_left _ _)
  have hy2 : morseNorm n y < Real.sqrt (2 * ε) := hy.trans_le (min_le_right _ _)
  have hysq : morseNorm n y ^ 2 < 2 * ε :=
    (Real.lt_sqrt (ModelField.morseNorm_nonneg y)).1 hy2
  refine hδU y hysq ?_ hu
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart r hr).hk y
  have h1 : ‖negPart (D.chart r hr).hk y‖ ≤ morseNorm n y :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (ModelField.morseNorm_nonneg y) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖posPart (D.chart r hr).hk y‖])
  exact h1.trans_lt hy1

theorem captured_eventually_small {r : M} {hr : r ∈ crit} {x : M} (hx : x ∈ D.captured r hr)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ T, ∀ t, T ≤ t → D.flow t x ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < ρ ∧ negPart (D.chart r hr).hk y = 0} := by
  set d := D.chart r hr with hd
  obtain ⟨T₀, hT₀⟩ := hx
  obtain ⟨y₀, ⟨hy₀, hu₀⟩, hyx⟩ := hT₀
  have hr₀ := d.hr₀
  have hy₀R : morseNorm n y₀ ≤ d.R := hy₀.le.trans (D.hrm r hr).2
  have hstay : ∀ s, 0 ≤ s → D.flow s (D.flow T₀ x) ∈ d.χ ''
      {z | morseNorm n z ≤ morseNorm n y₀ ∧ negPart d.hk z = 0} := fun s hs => by
    have := flow_mem_of_negPart_eq_zero hr hy₀ hu₀ hs
    rwa [hyx] at this
  have hsub : {z : Fin n → ℝ | morseNorm n z ≤ morseNorm n y₀ ∧ negPart d.hk z = 0} ⊆
      {z | morseNorm n z < D.rm r hr} := fun z hz => lt_of_le_of_lt hz.1 hy₀
  have hODE : ∀ T, ∀ s ∈ Icc 0 T, D.flow s (D.flow T₀ x) ∈ d.χ '' {z | morseNorm n z < D.rm r hr} :=
    fun T s hs => image_mono hsub (hstay s hs.1)
  set θ₀ : ℝ := (morseNorm n y₀ ^ 2 + d.r₀ ^ 2)⁻¹ with hθ₀def
  have hθ₀ : 0 < θ₀ := by positivity
  obtain ⟨T, hT0, hT⟩ : ∃ T, 0 ≤ T ∧ morseNorm n y₀ ^ 2 < ρ ^ 2 * (1 + 2 * θ₀ * T) := by
    have hpos : 0 < 2 * θ₀ * ρ ^ 2 := by positivity
    refine ⟨morseNorm n y₀ ^ 2 / (2 * θ₀ * ρ ^ 2), by positivity, ?_⟩
    have h := mul_div_cancel₀ (morseNorm n y₀ ^ 2) hpos.ne'
    nlinarith [sq_nonneg ρ]
  refine ⟨T₀ + T, fun t ht => ?_⟩
  have hs : 0 ≤ t - T₀ := by linarith
  have heq : D.flow t x = D.flow (t - T₀) (D.flow T₀ x) := by
    rw [flow_flow, add_sub_cancel]
  rw [heq]
  obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hstay (t - T₀) hs
  refine ⟨z, ⟨?_, hz2⟩, hzx⟩
  have hγ := hasDerivAt_symm_flow_Icc hr (hODE (t - T₀))
  have hθ : ∀ s ∈ Icc 0 (t - T₀),
      θ₀ ≤ ModelField.theta d.r₀ (d.χ.symm (D.flow s (D.flow T₀ x))) := fun s hs' => by
    have hmem := d.symm_mem (hsub.trans (d.lt_subset_ball (D.rm_lt_R' r hr).le)) (hstay s hs'.1)
    exact ModelField.theta_ge_of_le hr₀ hmem.1
  have hdecay := ModelField.normSq_posPart_mul_le d.hk hr₀ hs hγ hθ
  have hγ0 : d.χ.symm (D.flow 0 (D.flow T₀ x)) = y₀ := by
    rw [flow_zero, ← hyx, d.χ.left_inv (d.hsrc y₀ hy₀R)]
  have hγt : d.χ.symm (D.flow (t - T₀) (D.flow T₀ x)) = z := by
    rw [← hzx, d.χ.left_inv (d.hsrc z (hz1.trans hy₀R))]
  rw [hγ0, hγt] at hdecay
  have hz' := morseNorm_sq_eq_negPart_add_posPart d.hk z
  have hy' := morseNorm_sq_eq_negPart_add_posPart d.hk y₀
  rw [hz2, norm_zero] at hz'
  rw [hu₀, norm_zero] at hy'
  have hpos : 0 < 1 + 2 * θ₀ * (t - T₀) := by positivity
  have hlt : morseNorm n z ^ 2 * (1 + 2 * θ₀ * (t - T₀)) <
      ρ ^ 2 * (1 + 2 * θ₀ * (t - T₀)) := by
    have hTt : 1 + 2 * θ₀ * T ≤ 1 + 2 * θ₀ * (t - T₀) := by nlinarith
    have := mul_le_mul_of_nonneg_left hTt (sq_nonneg ρ)
    nlinarith
  have hlt' : morseNorm n z ^ 2 < ρ ^ 2 := lt_of_mul_lt_mul_right hlt hpos.le
  exact lt_of_pow_lt_pow_left₀ 2 hρ.le hlt'

end GradientLikeStrip

end

end DifferentialGeometry.Topology
