module

public import DifferentialGeometry.Topology.Morse.Strip.StripFlow

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le negPart posPart morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_mem_uIcc_zero_iff {T : ℝ} {P : ℝ → Prop} :
    (∃ s ∈ uIcc 0 T, P s) ↔ ∃ l ∈ Icc (0 : ℝ) 1, P (l * T) := by
  have := forall_mem_uIcc_zero_iff (T := T) (P := fun s => ¬ P s)
  constructor
  · rintro ⟨s, hs, hP⟩
    by_contra hcon
    push Not at hcon
    exact this.2 hcon s hs hP
  · rintro ⟨l, hl, hP⟩
    by_contra hcon
    push Not at hcon
    exact this.1 hcon l hl hP

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} (d : MorseNormalChart I f p)

def rightTube (ε r : ℝ) : Set (Fin n → ℝ) :=
  {z | morseNormalForm d.hk (f p) z = f p + ε ∧
    4 * (‖negPart d.hk z‖ ^ 2 * ‖posPart d.hk z‖ ^ 2) ≤ r ^ 4}

def leftTube (ε r : ℝ) : Set (Fin n → ℝ) :=
  {z | morseNormalForm d.hk (f p) z = f p - ε ∧
    4 * (‖negPart d.hk z‖ ^ 2 * ‖posPart d.hk z‖ ^ 2) ≤ r ^ 4}

theorem rightTube_mono {ε r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) :
    d.rightTube ε r ⊆ d.rightTube ε r' := fun _ hz =>
  ⟨hz.1, hz.2.trans (pow_le_pow_left₀ hr h 4)⟩

theorem leftTube_mono {ε r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) :
    d.leftTube ε r ⊆ d.leftTube ε r' := fun _ hz =>
  ⟨hz.1, hz.2.trans (pow_le_pow_left₀ hr h 4)⟩

theorem normSq_posPart_of_mem_rightTube {ε r : ℝ} {z : Fin n → ℝ} (hz : z ∈ d.rightTube ε r) :
    ‖posPart d.hk z‖ ^ 2 = 2 * ε + ‖negPart d.hk z‖ ^ 2 := by
  have := hz.1
  rw [morseNormalForm_split] at this
  linarith

theorem normSq_negPart_of_mem_leftTube {ε r : ℝ} {z : Fin n → ℝ} (hz : z ∈ d.leftTube ε r) :
    ‖negPart d.hk z‖ ^ 2 = 2 * ε + ‖posPart d.hk z‖ ^ 2 := by
  have := hz.1
  rw [morseNormalForm_split] at this
  linarith

theorem normSq_negPart_le_of_mem_rightTube {ε r : ℝ} (hε : 0 < ε) {z : Fin n → ℝ}
    (hz : z ∈ d.rightTube ε r) : ‖negPart d.hk z‖ ^ 2 ≤ r ^ 4 / (8 * ε) := by
  have h1 := d.normSq_posPart_of_mem_rightTube hz
  have h2 := hz.2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖negPart d.hk z‖, sq_nonneg (‖negPart d.hk z‖ ^ 2)]

theorem normSq_posPart_le_of_mem_leftTube {ε r : ℝ} (hε : 0 < ε) {z : Fin n → ℝ}
    (hz : z ∈ d.leftTube ε r) : ‖posPart d.hk z‖ ^ 2 ≤ r ^ 4 / (8 * ε) := by
  have h1 := d.normSq_negPart_of_mem_leftTube hz
  have h2 := hz.2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖posPart d.hk z‖, sq_nonneg (‖posPart d.hk z‖ ^ 2)]

theorem morseNorm_sq_of_mem_rightTube {ε r : ℝ} (hε : 0 < ε) {z : Fin n → ℝ}
    (hz : z ∈ d.rightTube ε r) : morseNorm n z ^ 2 ≤ 2 * ε + 2 * (r ^ 4 / (8 * ε)) := by
  rw [morseNorm_sq_eq_negPart_add_posPart d.hk, d.normSq_posPart_of_mem_rightTube hz]
  linarith [d.normSq_negPart_le_of_mem_rightTube hε hz]

theorem morseNorm_sq_of_mem_leftTube {ε r : ℝ} (hε : 0 < ε) {z : Fin n → ℝ}
    (hz : z ∈ d.leftTube ε r) : morseNorm n z ^ 2 ≤ 2 * ε + 2 * (r ^ 4 / (8 * ε)) := by
  rw [morseNorm_sq_eq_negPart_add_posPart d.hk, d.normSq_negPart_of_mem_leftTube hz]
  linarith [d.normSq_posPart_le_of_mem_leftTube hε hz]

theorem isClosed_rightTube (ε r : ℝ) : IsClosed (d.rightTube ε r) :=
  (isClosed_eq (ModelField.contDiff_nf d.hk (f p)).continuous continuous_const).inter
    (isClosed_le (continuous_const.mul
      ((d.continuous_negPart.norm.pow 2).mul (d.continuous_posPart.norm.pow 2)))
      continuous_const)

theorem isClosed_leftTube (ε r : ℝ) : IsClosed (d.leftTube ε r) :=
  (isClosed_eq (ModelField.contDiff_nf d.hk (f p)).continuous continuous_const).inter
    (isClosed_le (continuous_const.mul
      ((d.continuous_negPart.norm.pow 2).mul (d.continuous_posPart.norm.pow 2)))
      continuous_const)

theorem rightTube_subset {ε r : ℝ} (hε : 0 < ε) :
    d.rightTube ε r ⊆ {z | morseNorm n z ≤ Real.sqrt (2 * ε + 2 * (r ^ 4 / (8 * ε)))} :=
  fun _ hz => morseNorm_le_sqrt_of_sq_le (d.morseNorm_sq_of_mem_rightTube hε hz)

theorem leftTube_subset {ε r : ℝ} (hε : 0 < ε) :
    d.leftTube ε r ⊆ {z | morseNorm n z ≤ Real.sqrt (2 * ε + 2 * (r ^ 4 / (8 * ε)))} :=
  fun _ hz => morseNorm_le_sqrt_of_sq_le (d.morseNorm_sq_of_mem_leftTube hε hz)

theorem isCompact_rightTube {ε : ℝ} (hε : 0 < ε) (r : ℝ) : IsCompact (d.rightTube ε r) :=
  (isCompact_morseNorm_le _).of_isClosed_subset (d.isClosed_rightTube ε r)
    (d.rightTube_subset hε)

theorem isCompact_leftTube {ε : ℝ} (hε : 0 < ε) (r : ℝ) : IsCompact (d.leftTube ε r) :=
  (isCompact_morseNorm_le _).of_isClosed_subset (d.isClosed_leftTube ε r)
    (d.leftTube_subset hε)

theorem morseNorm_sq_le_of_mem_rightTube {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    {z : Fin n → ℝ} (hz : z ∈ d.rightTube ε r) : morseNorm n z ^ 2 ≤ 3 * ε := by
  have h := d.morseNorm_sq_of_mem_rightTube hε hz
  have h4 : r ^ 4 ≤ 4 * ε ^ 2 := by
    have : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg r]
  have : r ^ 4 / (8 * ε) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem morseNorm_sq_le_of_mem_leftTube {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    {z : Fin n → ℝ} (hz : z ∈ d.leftTube ε r) : morseNorm n z ^ 2 ≤ 3 * ε := by
  have h := d.morseNorm_sq_of_mem_leftTube hε hz
  have h4 : r ^ 4 ≤ 4 * ε ^ 2 := by
    have : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg r]
  have : r ^ 4 / (8 * ε) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem iInter_rightTube {ε r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ < r₁) :
    ⋂ r : Ioc r₀ r₁, d.rightTube ε r.1 = d.rightTube ε r₀ := by
  ext z
  simp only [mem_iInter, Subtype.forall, mem_Ioc]
  constructor
  · intro h
    refine ⟨(h r₁ ⟨hr₀₁, le_rfl⟩).1, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : ∀ᶠ r in 𝓝[>] r₀, r ^ 4 < 4 * (‖negPart d.hk z‖ ^ 2 * ‖posPart d.hk z‖ ^ 2) :=
      ((continuous_pow 4).continuousAt.eventually_lt continuousAt_const hcon).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨r, hr, hrr⟩ := (h1.and (Ioo_mem_nhdsGT hr₀₁)).exists
    exact absurd (h r ⟨hrr.1, hrr.2.le⟩).2 (not_le.2 hr)
  · intro h r hr
    exact d.rightTube_mono hr.1.le hr₀ h

theorem iInter_leftTube {ε r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ < r₁) :
    ⋂ r : Ioc r₀ r₁, d.leftTube ε r.1 = d.leftTube ε r₀ := by
  ext z
  simp only [mem_iInter, Subtype.forall, mem_Ioc]
  constructor
  · intro h
    refine ⟨(h r₁ ⟨hr₀₁, le_rfl⟩).1, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : ∀ᶠ r in 𝓝[>] r₀, r ^ 4 < 4 * (‖negPart d.hk z‖ ^ 2 * ‖posPart d.hk z‖ ^ 2) :=
      ((continuous_pow 4).continuousAt.eventually_lt continuousAt_const hcon).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨r, hr, hrr⟩ := (h1.and (Ioo_mem_nhdsGT hr₀₁)).exists
    exact absurd (h r ⟨hrr.1, hrr.2.le⟩).2 (not_le.2 hr)
  · intro h r hr
    exact d.leftTube_mono hr.1.le hr₀ h

theorem rightTube_subset_le {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε) (hR : 3 * ε ≤ d.R ^ 2) :
    d.rightTube ε r ⊆ {z | morseNorm n z ≤ d.R} := fun _ hz =>
  morseNorm_le_of_sq_le d.R_pos.le ((d.morseNorm_sq_le_of_mem_rightTube hε hr hz).trans hR)

theorem leftTube_subset_le {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε) (hR : 3 * ε ≤ d.R ^ 2) :
    d.leftTube ε r ⊆ {z | morseNorm n z ≤ d.R} := fun _ hz =>
  morseNorm_le_of_sq_le d.R_pos.le ((d.morseNorm_sq_le_of_mem_leftTube hε hr hz).trans hR)

theorem isCompact_image_rightTube {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ d.R ^ 2) : IsCompact (d.χ '' d.rightTube ε r) :=
  d.isCompact_image_of_subset (d.isCompact_rightTube hε r) d.hRR' (d.rightTube_subset_le hε hr hR)

theorem isCompact_image_leftTube {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ d.R ^ 2) : IsCompact (d.χ '' d.leftTube ε r) :=
  d.isCompact_image_of_subset (d.isCompact_leftTube hε r) d.hRR' (d.leftTube_subset_le hε hr hR)

theorem image_rightTube_subset_image_ball {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ d.R ^ 2) : d.χ '' d.rightTube ε r ⊆ d.χ '' Metric.ball 0 d.R' :=
  image_mono ((d.rightTube_subset_le hε hr hR).trans (d.le_subset_ball d.hRR'))

theorem image_leftTube_subset_image_ball {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ d.R ^ 2) : d.χ '' d.leftTube ε r ⊆ d.χ '' Metric.ball 0 d.R' :=
  image_mono ((d.leftTube_subset_le hε hr hR).trans (d.le_subset_ball d.hRR'))

end MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace GradientLikeStrip

variable (D : GradientLikeStrip I f a b crit) [T2Space M] [I.Boundaryless]

def rightThick (p : M) (hp : p ∈ crit) (ε c r : ℝ) : Set M :=
  D.flow (f p + ε - c) '' ((D.chart p hp).χ '' (D.chart p hp).rightTube ε r)

def leftThick (q : M) (hq : q ∈ crit) (ε c r : ℝ) : Set M :=
  D.flow (f q - ε - c) '' ((D.chart q hq).χ '' (D.chart q hq).leftTube ε r)

def thick (p : M) (hp : p ∈ crit) (ε c r : ℝ) : Set M :=
  if f p < c then D.rightThick p hp ε c r else D.leftThick p hp ε c r

theorem isCompact_rightThick (p : M) (hp : p ∈ crit) {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ (D.chart p hp).R ^ 2) (c : ℝ) : IsCompact (D.rightThick p hp ε c r) :=
  ((D.chart p hp).isCompact_image_rightTube hε hr hR).image (D.continuous_flow _)

theorem isCompact_leftThick (p : M) (hp : p ∈ crit) {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ (D.chart p hp).R ^ 2) (c : ℝ) : IsCompact (D.leftThick p hp ε c r) :=
  ((D.chart p hp).isCompact_image_leftTube hε hr hR).image (D.continuous_flow _)

theorem isCompact_thick (p : M) (hp : p ∈ crit) {ε r : ℝ} (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε)
    (hR : 3 * ε ≤ (D.chart p hp).R ^ 2) (c : ℝ) : IsCompact (D.thick p hp ε c r) := by
  unfold thick
  split_ifs
  · exact D.isCompact_rightThick p hp hε hr hR c
  · exact D.isCompact_leftThick p hp hε hr hR c

theorem rightThick_mono (p : M) (hp : p ∈ crit) (ε c : ℝ) {r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) :
    D.rightThick p hp ε c r ⊆ D.rightThick p hp ε c r' :=
  image_mono (image_mono ((D.chart p hp).rightTube_mono h hr))

theorem leftThick_mono (p : M) (hp : p ∈ crit) (ε c : ℝ) {r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) :
    D.leftThick p hp ε c r ⊆ D.leftThick p hp ε c r' :=
  image_mono (image_mono ((D.chart p hp).leftTube_mono h hr))

theorem thick_mono (p : M) (hp : p ∈ crit) (ε c : ℝ) {r r' : ℝ} (h : r ≤ r') (hr : 0 ≤ r) :
    D.thick p hp ε c r ⊆ D.thick p hp ε c r' := by
  unfold thick
  split_ifs
  · exact D.rightThick_mono p hp ε c h hr
  · exact D.leftThick_mono p hp ε c h hr

theorem mem_rightThick_iff (p : M) (hp : p ∈ crit) (ε c r : ℝ) {x : M} :
    x ∈ D.rightThick p hp ε c r ↔
      D.flow (c - (f p + ε)) x ∈ (D.chart p hp).χ '' (D.chart p hp).rightTube ε r := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    rwa [flow_flow, show f p + ε - c + (c - (f p + ε)) = 0 by ring, flow_zero]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [flow_flow, show c - (f p + ε) + (f p + ε - c) = 0 by ring, flow_zero]

theorem mem_leftThick_iff (q : M) (hq : q ∈ crit) (ε c r : ℝ) {x : M} :
    x ∈ D.leftThick q hq ε c r ↔
      D.flow (c - (f q - ε)) x ∈ (D.chart q hq).χ '' (D.chart q hq).leftTube ε r := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    rwa [flow_flow, show f q - ε - c + (c - (f q - ε)) = 0 by ring, flow_zero]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [flow_flow, show c - (f q - ε) + (f q - ε - c) = 0 by ring, flow_zero]

theorem exists_rightThick_subset (p : M) (hp : p ∈ crit) {ε r₀ r₁ : ℝ} (hε : 0 < ε)
    (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ < r₁) (hr₁ : r₁ ^ 2 ≤ 2 * ε) (hR : 3 * ε ≤ (D.chart p hp).R ^ 2)
    (c : ℝ) {U : Set M} (hU : IsOpen U) (hsub : D.rightThick p hp ε c r₀ ⊆ U) :
    ∃ r ∈ Ioc r₀ r₁, D.rightThick p hp ε c r ⊆ U := by
  set d := D.chart p hp with hd
  have hne : Nonempty (Ioc r₀ r₁) := ⟨⟨r₁, hr₀₁, le_rfl⟩⟩
  have hbound : ∀ r : Ioc r₀ r₁, r.1 ^ 2 ≤ 2 * ε := fun r =>
    (pow_le_pow_left₀ (hr₀.trans r.2.1.le) r.2.2 2).trans hr₁
  have hdir : Directed (· ⊇ ·) (fun r : Ioc r₀ r₁ => D.rightThick p hp ε c r.1) := by
    intro r r'
    refine ⟨⟨min r.1 r'.1, lt_min r.2.1 r'.2.1, (min_le_left _ _).trans r.2.2⟩, ?_, ?_⟩
    · exact D.rightThick_mono p hp ε c (min_le_left _ _) (hr₀.trans (lt_min r.2.1 r'.2.1).le)
    · exact D.rightThick_mono p hp ε c (min_le_right _ _) (hr₀.trans (lt_min r.2.1 r'.2.1).le)
  have hcpt : ∀ r : Ioc r₀ r₁, IsCompact (D.rightThick p hp ε c r.1) := fun r =>
    D.isCompact_rightThick p hp hε (hbound r) hR c
  have hinter : ⋂ r : Ioc r₀ r₁, D.rightThick p hp ε c r.1 ⊆ D.rightThick p hp ε c r₀ := by
    intro x hx
    rw [mem_iInter] at hx
    rw [mem_rightThick_iff]
    have h1 := hx ⟨r₁, hr₀₁, le_rfl⟩
    rw [mem_rightThick_iff] at h1
    have hball : D.flow (c - (f p + ε)) x ∈ d.χ '' Metric.ball 0 d.R' :=
      d.image_rightTube_subset_image_ball hε hr₁ hR h1
    refine d.mem_image_of_symm_mem hball ?_
    rw [← d.iInter_rightTube hr₀ hr₀₁, mem_iInter]
    intro r
    have := hx r
    rw [mem_rightThick_iff] at this
    exact d.symm_mem ((d.rightTube_subset_le hε (hbound r) hR).trans (d.le_subset_ball d.hRR'))
      this
  obtain ⟨r, hr⟩ := exists_subset_nhds_of_isCompact' hdir hcpt (fun r => (hcpt r).isClosed)
    (hU.mem_nhdsSet.2 (hinter.trans hsub))
  exact ⟨r.1, r.2, hr⟩

theorem exists_leftThick_subset (p : M) (hp : p ∈ crit) {ε r₀ r₁ : ℝ} (hε : 0 < ε)
    (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ < r₁) (hr₁ : r₁ ^ 2 ≤ 2 * ε) (hR : 3 * ε ≤ (D.chart p hp).R ^ 2)
    (c : ℝ) {U : Set M} (hU : IsOpen U) (hsub : D.leftThick p hp ε c r₀ ⊆ U) :
    ∃ r ∈ Ioc r₀ r₁, D.leftThick p hp ε c r ⊆ U := by
  set d := D.chart p hp with hd
  have hne : Nonempty (Ioc r₀ r₁) := ⟨⟨r₁, hr₀₁, le_rfl⟩⟩
  have hbound : ∀ r : Ioc r₀ r₁, r.1 ^ 2 ≤ 2 * ε := fun r =>
    (pow_le_pow_left₀ (hr₀.trans r.2.1.le) r.2.2 2).trans hr₁
  have hdir : Directed (· ⊇ ·) (fun r : Ioc r₀ r₁ => D.leftThick p hp ε c r.1) := by
    intro r r'
    refine ⟨⟨min r.1 r'.1, lt_min r.2.1 r'.2.1, (min_le_left _ _).trans r.2.2⟩, ?_, ?_⟩
    · exact D.leftThick_mono p hp ε c (min_le_left _ _) (hr₀.trans (lt_min r.2.1 r'.2.1).le)
    · exact D.leftThick_mono p hp ε c (min_le_right _ _) (hr₀.trans (lt_min r.2.1 r'.2.1).le)
  have hcpt : ∀ r : Ioc r₀ r₁, IsCompact (D.leftThick p hp ε c r.1) := fun r =>
    D.isCompact_leftThick p hp hε (hbound r) hR c
  have hinter : ⋂ r : Ioc r₀ r₁, D.leftThick p hp ε c r.1 ⊆ D.leftThick p hp ε c r₀ := by
    intro x hx
    rw [mem_iInter] at hx
    rw [mem_leftThick_iff]
    have h1 := hx ⟨r₁, hr₀₁, le_rfl⟩
    rw [mem_leftThick_iff] at h1
    have hball : D.flow (c - (f p - ε)) x ∈ d.χ '' Metric.ball 0 d.R' :=
      d.image_leftTube_subset_image_ball hε hr₁ hR h1
    refine d.mem_image_of_symm_mem hball ?_
    rw [← d.iInter_leftTube hr₀ hr₀₁, mem_iInter]
    intro r
    have := hx r
    rw [mem_leftThick_iff] at this
    exact d.symm_mem ((d.leftTube_subset_le hε (hbound r) hR).trans (d.le_subset_ball d.hRR'))
      this
  obtain ⟨r, hr⟩ := exists_subset_nhds_of_isCompact' hdir hcpt (fun r => (hcpt r).isClosed)
    (hU.mem_nhdsSet.2 (hinter.trans hsub))
  exact ⟨r.1, r.2, hr⟩

theorem exists_thick_subset (p : M) (hp : p ∈ crit) {ε r₀ r₁ : ℝ} (hε : 0 < ε)
    (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ < r₁) (hr₁ : r₁ ^ 2 ≤ 2 * ε) (hR : 3 * ε ≤ (D.chart p hp).R ^ 2)
    (c : ℝ) {U : Set M} (hU : IsOpen U) (hsub : D.thick p hp ε c r₀ ⊆ U) :
    ∃ r ∈ Ioc r₀ r₁, D.thick p hp ε c r ⊆ U := by
  unfold thick at hsub ⊢
  split_ifs at hsub ⊢
  · exact D.exists_rightThick_subset p hp hε hr₀ hr₀₁ hr₁ hR c hU hsub
  · exact D.exists_leftThick_subset p hp hε hr₀ hr₀₁ hr₁ hR c hU hsub

def throughBall (p : M) (hp : p ∈ crit) (r c : ℝ) : Set M :=
  {x | f x ∈ Ioo a b ∧ ∃ s ∈ uIcc 0 (f x - c),
    D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r}}

theorem isOpen_throughBall (hf : Continuous f) (p : M) (hp : p ∈ crit) {r : ℝ}
    (hr : r ≤ (D.chart p hp).R') (c : ℝ) : IsOpen (D.throughBall p hp r c) := by
  have hB : IsOpen ((D.chart p hp).χ '' {y | morseNorm n y < r}) :=
    (D.chart p hp).isOpen_image_of_lt hr
  have heq : D.throughBall p hp r c = {x | f x ∈ Ioo a b} ∩
      ⋃ l ∈ Icc (0 : ℝ) 1,
        {x | D.flow (l * (f x - c)) x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r}} := by
    ext x
    simp only [throughBall, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    exact and_congr_right fun _ => exists_mem_uIcc_zero_iff
  rw [heq]
  refine (isOpen_Ioo.preimage hf).inter (isOpen_biUnion fun l _ => ?_)
  have hc : Continuous fun x => D.flow (l * (f x - c)) x :=
    D.continuous_flow_joint.comp ((continuous_const.mul (hf.sub continuous_const)).prodMk
      continuous_id)
  exact hB.preimage hc

theorem throughBall_mono (p : M) (hp : p ∈ crit) {r r' : ℝ} (h : r ≤ r') (c : ℝ) :
    D.throughBall p hp r c ⊆ D.throughBall p hp r' c := by
  rintro x ⟨hx, s, hs, hmem⟩
  exact ⟨hx, s, hs, image_mono (fun y (hy : morseNorm n y < r) => lt_of_lt_of_le hy h) hmem⟩

theorem mem_throughBall_of_mem_ball (p : M) (hp : p ∈ crit) {r c : ℝ}
    (hr : r ≤ (D.chart p hp).R') {x : M}
    (hx : x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r}) : x ∈ D.throughBall p hp r c :=
  ⟨D.inStrip p hp ((D.chart p hp).image_lt_subset_image_ball hr hx), 0, left_mem_uIcc,
    by rw [flow_zero]; exact hx⟩

theorem throughBall_subset_strip (p : M) (hp : p ∈ crit) (r c : ℝ) :
    D.throughBall p hp r c ⊆ f ⁻¹' Ioo a b := fun _ hx => hx.1

theorem mem_regularFlowDomain_or_exists_throughBall {c : ℝ} (r : ∀ p ∈ crit, ℝ)
    (hr : ∀ p hp, (D.chart p hp).r₀ < r p hp) {x : M} (hx : f x ∈ Ioo a b) :
    x ∈ D.regularFlowDomain c ∨ ∃ p hp, x ∈ D.throughBall p hp (r p hp) c := by
  by_cases h : x ∈ D.regularFlowDomain c
  · exact Or.inl h
  · right
    simp only [regularFlowDomain, mem_ofPred_eq, not_and, not_forall, not_not] at h
    obtain ⟨s, hs, p, hp, hmem⟩ := h hx
    refine ⟨p, hp, hx, s, hs, ?_⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    exact ⟨y, lt_of_le_of_lt hy (hr p hp), hyx⟩

end GradientLikeStrip

namespace ModelField

variable {k : ℕ} (hk : k ≤ n)

theorem nf_le_linear_of_rate (c : ℝ) {r₀ m : ℝ} {γ : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hm : ∀ t ∈ Icc t₀ t₁, m ≤ theta r₀ (γ t) * morseNorm n (γ t) ^ 2) :
    ∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) ≤ morseNormalForm hk c (γ t₀) - m * (t - t₀) := by
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => morseNormalForm hk c (γ s) + m * s)
      (-(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + m) t := by
    intro t ht
    have := (hasDerivAt_nf_curve hk c hγ ht).add ((hasDerivAt_id' (x := t)).const_mul m)
    rw [mul_one] at this
    exact this
  have hanti : AntitoneOn (fun s => morseNormalForm hk c (γ s) + m * s) (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
      (f' := fun t => -(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + m)
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      linarith [hm t (Ioo_subset_Icc_self ht)]
  intro t ht
  have := hanti (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
  simp only at this
  linarith

end ModelField

namespace GradientLikeStrip

variable {D : GradientLikeStrip I f a b crit} [T2Space M] [I.Boundaryless]

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem prod_le_morseNorm_pow_four {p : M} (d : MorseNormalChart I f p) (y : Fin n → ℝ) :
    4 * (‖negPart d.hk y‖ ^ 2 * ‖posPart d.hk y‖ ^ 2) ≤ morseNorm n y ^ 4 := by
  have h := morseNorm_sq_eq_negPart_add_posPart d.hk y
  have : morseNorm n y ^ 4 = (morseNorm n y ^ 2) ^ 2 := by ring
  rw [this, h]
  nlinarith [sq_nonneg (‖negPart d.hk y‖ ^ 2 - ‖posPart d.hk y‖ ^ 2)]

theorem π_mem_rightThick (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} (hp : p ∈ crit) {ε c r : ℝ}
    (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε) (hrm : 6 * ε < D.rm p hp ^ 2) (hc : c ∈ Icc a b)
    (hpc : f p + ε < c) {x : M} (hx : x ∈ D.regularFlowDomain c) {s : ℝ} (hs : s ∈ uIcc 0 (f x - c))
    (hmem : D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r}) :
    D.π c x ∈ D.rightThick p hp ε c r := by
  set d := D.chart p hp with hd
  obtain ⟨y, hy, hyw⟩ := hmem
  have hy' : morseNorm n y < r := hy
  have hrm0 := D.rm_pos p hp
  have hr0 : 0 ≤ r := (ModelField.morseNorm_nonneg y).trans hy'.le
  have hrrm : r < D.rm p hp := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm0.le; linarith
  have hyrm : morseNorm n y < D.rm p hp := hy'.trans hrrm
  have hyR : morseNorm n y ≤ d.R := hyrm.le.trans (D.hrm p hp).2
  have hsq := morseNorm_sq_eq_negPart_add_posPart d.hk y
  have hysq : morseNorm n y ^ 2 < r ^ 2 := by
    exact pow_lt_pow_left₀ hy' (ModelField.morseNorm_nonneg y) two_ne_zero
  have hfw : f (D.flow s x) = morseNormalForm d.hk (f p) y := by rw [← hyw]; exact d.hnorm y hyR
  have hnfy : morseNormalForm d.hk (f p) y < f p + ε := by
    rw [morseNormalForm_split]
    nlinarith [sq_nonneg ‖negPart d.hk y‖]
  have hunit := f_flow_eq_sub_of_mem_regularFlowDomain hf hc hx
  have hfws : f (D.flow s x) = f x - s := hunit s hs
  have hfx : f x < c := by
    by_contra hcon
    push Not at hcon
    rw [uIcc_of_le (by linarith)] at hs
    linarith [hs.2]
  rw [uIcc_of_ge (by linarith)] at hs hunit
  have hπ : f (D.π c x) = c := f_π hf hc hx
  have hv : posPart d.hk y ≠ 0 := by
    intro hv0
    have := f_flow_le_f_p_of_posPart_eq_zero hp hyrm hv0 (t := f x - c - s) (by linarith [hs.1])
    rw [hyw, flow_flow, show s + (f x - c - s) = f x - c by ring] at this
    change f (D.π c x) ≤ f p at this
    linarith
  have hball : 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 < D.rm p hp ^ 2 := by
    nlinarith [sq_nonneg ‖posPart d.hk y‖]
  obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_asc hf hp hε hball hv hnfy.le
  rw [hyw] at hft hstay
  set B := 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 with hB
  have hSsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤ B} ⊆ {z | morseNorm n z < D.rm p hp} :=
    fun z hz => lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hz hball)
  have hODE : ∀ u ∈ Icc (-t) 0, D.flow u (D.flow s x) ∈ d.χ '' {z | morseNorm n z < D.rm p hp} :=
    fun u hu => image_mono hSsub (hstay u hu)
  have hγ := hasDerivAt_symm_flow_Icc hp hODE
  have hγ0 : d.χ.symm (D.flow 0 (D.flow s x)) = y := by
    rw [flow_zero, ← hyw, d.χ.left_inv (d.hsrc y hyR)]
  have hprod := ModelField.normSq_negPart_mul_posPart_const d.hk hγ 0
    (right_mem_Icc.2 (by linarith))
  rw [hγ0] at hprod
  set e := D.flow (-t) (D.flow s x) with he
  have heO : e ∈ d.χ '' {z | morseNorm n z < D.rm p hp} := hODE (-t) (left_mem_Icc.2 (by linarith))
  have heball : e ∈ d.χ '' Metric.ball 0 d.R' := D.modelBall_subset_image_ball p hp heO
  have hez : e ∈ d.χ '' {z | morseNorm n z ≤ d.R} := D.modelBall_subset_image_le p hp heO
  have hfe : f e = morseNormalForm d.hk (f p) (d.χ.symm e) := d.f_eq_nf_symm hez
  have hzT : d.χ.symm e ∈ d.rightTube ε r := by
    refine ⟨by rw [← hfe]; exact hft, ?_⟩
    have h1 : ‖negPart d.hk (d.χ.symm e)‖ ^ 2 * ‖posPart d.hk (d.χ.symm e)‖ ^ 2 =
        ‖negPart d.hk y‖ ^ 2 * ‖posPart d.hk y‖ ^ 2 := hprod.symm
    have h2 := prod_le_morseNorm_pow_four d y
    have h3 : morseNorm n y ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy'.le 4
    rw [h1]; linarith
  have hes : e = D.flow (s - t) x := by rw [he, flow_flow]; ring_nf
  have hst : s - t ∈ Icc (f x - c) 0 := by
    refine ⟨?_, by linarith [hs.2]⟩
    by_contra hcon
    push Not at hcon
    have hanti : f (D.flow (f x - c) x) ≤ f (D.flow (s - t) x) :=
      f_flow_antitone (D := D) hf x hcon.le
    have hπ' : f (D.flow (f x - c) x) = c := hπ
    rw [hes] at hft
    linarith
  have hfe' : f e = f x - (s - t) := by rw [hes]; exact hunit _ hst
  rw [mem_rightThick_iff]
  have : D.flow (c - (f p + ε)) (D.π c x) = e := by
    rw [π, flow_flow, hes]
    congr 1
    linarith
  rw [this]
  exact d.mem_image_of_symm_mem heball hzT

theorem π_mem_leftThick (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hq : q ∈ crit) {ε c r : ℝ}
    (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε) (hrm : 6 * ε < D.rm q hq ^ 2) (hc : c ∈ Icc a b)
    (hqc : c < f q - ε) {x : M} (hx : x ∈ D.regularFlowDomain c) {s : ℝ} (hs : s ∈ uIcc 0 (f x - c))
    (hmem : D.flow s x ∈ (D.chart q hq).χ '' {y | morseNorm n y < r}) :
    D.π c x ∈ D.leftThick q hq ε c r := by
  set d := D.chart q hq with hd
  obtain ⟨y, hy, hyw⟩ := hmem
  have hy' : morseNorm n y < r := hy
  have hrm0 := D.rm_pos q hq
  have hr0 : 0 ≤ r := (ModelField.morseNorm_nonneg y).trans hy'.le
  have hrrm : r < D.rm q hq := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm0.le; linarith
  have hyrm : morseNorm n y < D.rm q hq := hy'.trans hrrm
  have hyR : morseNorm n y ≤ d.R := hyrm.le.trans (D.hrm q hq).2
  have hsq := morseNorm_sq_eq_negPart_add_posPart d.hk y
  have hysq : morseNorm n y ^ 2 < r ^ 2 := by
    exact pow_lt_pow_left₀ hy' (ModelField.morseNorm_nonneg y) two_ne_zero
  have hfw : f (D.flow s x) = morseNormalForm d.hk (f q) y := by rw [← hyw]; exact d.hnorm y hyR
  have hnfy : f q - ε < morseNormalForm d.hk (f q) y := by
    rw [morseNormalForm_split]
    nlinarith [sq_nonneg ‖posPart d.hk y‖]
  have hunit := f_flow_eq_sub_of_mem_regularFlowDomain hf hc hx
  have hfws : f (D.flow s x) = f x - s := hunit s hs
  have hfx : c < f x := by
    by_contra hcon
    push Not at hcon
    rw [uIcc_of_ge (by linarith)] at hs
    linarith [hs.1]
  rw [uIcc_of_le (by linarith)] at hs hunit
  have hπ : f (D.π c x) = c := f_π hf hc hx
  have hu : negPart d.hk y ≠ 0 := by
    intro hu0
    have := f_p_le_f_flow_of_negPart_eq_zero hq hyrm hu0 (t := f x - c - s) (by linarith [hs.2])
    rw [hyw, flow_flow, show s + (f x - c - s) = f x - c by ring] at this
    change f q ≤ f (D.π c x) at this
    linarith
  have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm q hq ^ 2 := by
    nlinarith [sq_nonneg ‖negPart d.hk y‖]
  obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hq hε hball hu hnfy.le
  rw [hyw] at hft hstay
  set B := 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 with hB
  have hSsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤ B} ⊆ {z | morseNorm n z < D.rm q hq} :=
    fun z hz => lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hz hball)
  have hODE : ∀ u ∈ Icc 0 t, D.flow u (D.flow s x) ∈ d.χ '' {z | morseNorm n z < D.rm q hq} :=
    fun u hu => image_mono hSsub (hstay u hu)
  have hγ := hasDerivAt_symm_flow_Icc hq hODE
  have hγ0 : d.χ.symm (D.flow 0 (D.flow s x)) = y := by
    rw [flow_zero, ← hyw, d.χ.left_inv (d.hsrc y hyR)]
  have hprod := ModelField.normSq_negPart_mul_posPart_const d.hk hγ t (right_mem_Icc.2 ht0)
  rw [hγ0] at hprod
  set e := D.flow t (D.flow s x) with he
  have heO : e ∈ d.χ '' {z | morseNorm n z < D.rm q hq} := hODE t (right_mem_Icc.2 ht0)
  have heball : e ∈ d.χ '' Metric.ball 0 d.R' := D.modelBall_subset_image_ball q hq heO
  have hez : e ∈ d.χ '' {z | morseNorm n z ≤ d.R} := D.modelBall_subset_image_le q hq heO
  have hfe : f e = morseNormalForm d.hk (f q) (d.χ.symm e) := d.f_eq_nf_symm hez
  have hzT : d.χ.symm e ∈ d.leftTube ε r := by
    refine ⟨by rw [← hfe]; exact hft, ?_⟩
    have h1 : ‖negPart d.hk (d.χ.symm e)‖ ^ 2 * ‖posPart d.hk (d.χ.symm e)‖ ^ 2 =
        ‖negPart d.hk y‖ ^ 2 * ‖posPart d.hk y‖ ^ 2 := hprod
    have h2 := prod_le_morseNorm_pow_four d y
    have h3 : morseNorm n y ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy'.le 4
    rw [h1]; linarith
  have hes : e = D.flow (s + t) x := by rw [he, flow_flow]
  have hst : s + t ∈ Icc 0 (f x - c) := by
    refine ⟨by linarith [hs.1], ?_⟩
    by_contra hcon
    push Not at hcon
    have hanti : f (D.flow (s + t) x) ≤ f (D.flow (f x - c) x) :=
      f_flow_antitone (D := D) hf x hcon.le
    have hπ' : f (D.flow (f x - c) x) = c := hπ
    rw [hes] at hft
    linarith
  have hfe' : f e = f x - (s + t) := by rw [hes]; exact hunit _ hst
  rw [mem_leftThick_iff]
  have : D.flow (c - (f q - ε)) (D.π c x) = e := by
    rw [π, flow_flow, hes]
    congr 1
    linarith
  rw [this]
  exact d.mem_image_of_symm_mem heball hzT

end GradientLikeStrip

namespace GradientLikeStrip

variable {D : GradientLikeStrip I f a b crit} [T2Space M] [I.Boundaryless]

theorem exists_flow_mem_closedSmallBall_of_mem_rightTube (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hp : p ∈ crit) {ε : ℝ} (hε : 0 < ε) (hr₀ : (D.chart p hp).r₀ ^ 2 < 2 * ε)
    (hrm : 8 * ε < D.rm p hp ^ 2) {z : Fin n → ℝ}
    (hz : z ∈ (D.chart p hp).rightTube ε (D.chart p hp).r₀) :
    ∃ t, 0 ≤ t ∧ D.flow t ((D.chart p hp).χ z) ∈ D.closedSmallBall p hp := by
  set d := D.chart p hp with hd
  set x := d.χ z with hx
  have hr₀pos := d.hr₀
  have hrm0 := D.rm_pos p hp
  have hu2 := d.normSq_negPart_le_of_mem_rightTube hε hz
  have hv2 := d.normSq_posPart_of_mem_rightTube hz
  have hu2' : ‖negPart d.hk z‖ ^ 2 < ε / 2 := by
    have : d.r₀ ^ 4 / (8 * ε) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : d.r₀ ^ 4 = d.r₀ ^ 2 * d.r₀ ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg d.r₀]
    linarith
  have hzsq : morseNorm n z ^ 2 < 3 * ε := by
    rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hv2]; linarith
  have hzrm : morseNorm n z < D.rm p hp := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm0.le; linarith
  have hzR : morseNorm n z ≤ d.R := hzrm.le.trans (D.hrm p hp).2
  have hfx : f x = f p + ε := by rw [hx, d.hnorm z hzR]; exact hz.1
  have hOball := D.modelBall_subset_image_ball p hp
  have hOle := D.modelBall_subset_image_le p hp
  by_cases hu0 : negPart d.hk z = 0
  · have hstay : ∀ t, 0 ≤ t → D.flow t x ∈ d.χ ''
        {w | morseNorm n w ≤ morseNorm n z ∧ negPart d.hk w = 0} :=
      fun t ht => flow_mem_of_negPart_eq_zero hp hzrm hu0 ht
    have hsubrm : {w | morseNorm n w ≤ morseNorm n z ∧ negPart d.hk w = 0} ⊆
        {w | morseNorm n w < D.rm p hp} := fun w hw => hw.1.trans_lt hzrm
    have hsubR' := hsubrm.trans (d.lt_subset_ball (D.rm_lt_R' p hp).le)
    set θ₀ : ℝ := (D.rm p hp ^ 2 + d.r₀ ^ 2)⁻¹ with hθ₀
    have hθ₀pos : 0 < θ₀ := by positivity
    set m := θ₀ * d.r₀ ^ 2 with hm
    have hmpos : 0 < m := by positivity
    set T := ε / m + 1 with hT
    have hTpos : 0 < T := by have := div_pos hε hmpos; linarith
    by_contra hcon
    push Not at hcon
    have hODE : ∀ t ∈ Icc 0 T, D.flow t x ∈ d.χ '' {w | morseNorm n w < D.rm p hp} :=
      fun t ht => image_mono (fun w hw => lt_of_le_of_lt hw.1 hzrm) (hstay t ht.1)
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hrate : ∀ t ∈ Icc 0 T, m ≤ ModelField.theta d.r₀ (d.χ.symm (D.flow t x)) *
        morseNorm n (d.χ.symm (D.flow t x)) ^ 2 := by
      intro t ht
      have hmem := hstay t ht.1
      have hw : d.χ.symm (D.flow t x) ∈ {w | morseNorm n w ≤ morseNorm n z ∧ negPart d.hk w = 0} :=
        d.symm_mem hsubR' hmem
      have hθ : θ₀ ≤ ModelField.theta d.r₀ (d.χ.symm (D.flow t x)) :=
        ModelField.theta_ge_of_le d.hr₀ (hw.1.trans hzrm.le)
      have hnorm : d.r₀ < morseNorm n (d.χ.symm (D.flow t x)) := by
        by_contra hle
        push Not at hle
        exact hcon t ht.1 (d.mem_image_of_symm_mem (hOball (hODE t ht)) hle)
      have h1 : d.r₀ ^ 2 ≤ morseNorm n (d.χ.symm (D.flow t x)) ^ 2 :=
        pow_le_pow_left₀ d.hr₀.le hnorm.le 2
      exact mul_le_mul hθ h1 (sq_nonneg _) (ModelField.theta_pos d.hr₀ _).le
    have hlin := ModelField.nf_le_linear_of_rate d.hk (f p) hγ hrate T (right_mem_Icc.2 hTpos.le)
    have hγ0 : d.χ.symm (D.flow 0 x) = z := by
      rw [flow_zero, hx, d.χ.left_inv (d.hsrc z hzR)]
    rw [hγ0, hz.1] at hlin
    have hwT : d.χ.symm (D.flow T x) ∈ {w | morseNorm n w ≤ morseNorm n z ∧ negPart d.hk w = 0} :=
      d.symm_mem hsubR' (hstay T hTpos.le)
    have hge : f p ≤ morseNormalForm d.hk (f p) (d.χ.symm (D.flow T x)) := by
      rw [morseNormalForm_split, hwT.2, norm_zero]
      nlinarith [sq_nonneg ‖posPart d.hk (d.χ.symm (D.flow T x))‖]
    have hTm : m * T = ε + m := by rw [hT]; field_simp
    nlinarith
  · have hball : 2 * ε + 2 * ‖posPart d.hk z‖ ^ 2 < D.rm p hp ^ 2 := by rw [hv2]; linarith
    have hlevel : f p - ε ≤ morseNormalForm d.hk (f p) z := by rw [hz.1]; linarith
    obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hp hε hball hu0 hlevel
    set B := 2 * ε + 2 * ‖posPart d.hk z‖ ^ 2 with hB
    have hSsub : {w : Fin n → ℝ | morseNorm n w ^ 2 ≤ B} ⊆ {w | morseNorm n w < D.rm p hp} :=
      fun w hw => lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hw hball)
    have hODE : ∀ u ∈ Icc 0 t, D.flow u x ∈ d.χ '' {w | morseNorm n w < D.rm p hp} :=
      fun u hu => image_mono hSsub (hstay u hu)
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hγ0 : d.χ.symm (D.flow 0 x) = z := by
      rw [flow_zero, hx, d.χ.left_inv (d.hsrc z hzR)]
    set g : ℝ → ℝ := fun u => f (D.flow u x) with hg
    have hgc : Continuous g := hf.continuous.comp (D.continuous_flow_curve x)
    have hg0 : g 0 = f p + ε := by simp [hg, hfx]
    have hgt : g t = f p - ε := hft
    obtain ⟨t', ht', hgt'⟩ : ∃ t' ∈ Icc 0 t, g t' = f p :=
      intermediate_value_Icc' ht0 hgc.continuousOn ⟨by rw [hgt]; linarith, by rw [hg0]; linarith⟩
    refine ⟨t', ht'.1, ?_⟩
    have hprod := ModelField.normSq_negPart_mul_posPart_const d.hk hγ t' ht'
    rw [hγ0] at hprod
    have heO := hODE t' ht'
    have hfe : f (D.flow t' x) = morseNormalForm d.hk (f p) (d.χ.symm (D.flow t' x)) :=
      d.f_eq_nf_symm (hOle heO)
    have hbal : ‖negPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 =
        ‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 := by
      have := hgt'
      rw [hg] at this
      simp only at this
      rw [hfe, morseNormalForm_split] at this
      linarith
    have h4 := hz.2
    rw [hbal] at hprod
    have hle : ‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 ≤ d.r₀ ^ 2 / 2 := by
      have h1 : (‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2) ^ 2 ≤ (d.r₀ ^ 2 / 2) ^ 2 := by
        rw [← hprod] at h4
        nlinarith
      exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) two_ne_zero).1 h1
    have hmn : morseNorm n (d.χ.symm (D.flow t' x)) ≤ d.r₀ := by
      refine MorseNormalChart.morseNorm_le_of_sq_le d.hr₀.le ?_
      rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hbal]
      linarith
    exact d.mem_image_of_symm_mem (hOball heO) hmn

theorem exists_flow_mem_closedSmallBall_of_mem_leftTube (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hp : p ∈ crit) {ε : ℝ} (hε : 0 < ε) (hr₀ : (D.chart p hp).r₀ ^ 2 < 2 * ε)
    (hrm : 8 * ε < D.rm p hp ^ 2) {z : Fin n → ℝ}
    (hz : z ∈ (D.chart p hp).leftTube ε (D.chart p hp).r₀) :
    ∃ t, t ≤ 0 ∧ D.flow t ((D.chart p hp).χ z) ∈ D.closedSmallBall p hp := by
  set d := D.chart p hp with hd
  set x := d.χ z with hx
  have hr₀pos := d.hr₀
  have hrm0 := D.rm_pos p hp
  have hv2 := d.normSq_posPart_le_of_mem_leftTube hε hz
  have hu2 := d.normSq_negPart_of_mem_leftTube hz
  have hv2' : ‖posPart d.hk z‖ ^ 2 < ε / 2 := by
    have : d.r₀ ^ 4 / (8 * ε) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : d.r₀ ^ 4 = d.r₀ ^ 2 * d.r₀ ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg d.r₀]
    linarith
  have hzsq : morseNorm n z ^ 2 < 3 * ε := by
    rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hu2]; linarith
  have hzrm : morseNorm n z < D.rm p hp := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm0.le; linarith
  have hzR : morseNorm n z ≤ d.R := hzrm.le.trans (D.hrm p hp).2
  have hfx : f x = f p - ε := by rw [hx, d.hnorm z hzR]; exact hz.1
  have hOball := D.modelBall_subset_image_ball p hp
  have hOle := D.modelBall_subset_image_le p hp
  by_cases hv0 : posPart d.hk z = 0
  · have hstay : ∀ t, t ≤ 0 → D.flow t x ∈ d.χ ''
        {w | morseNorm n w ≤ morseNorm n z ∧ posPart d.hk w = 0} :=
      fun t ht => flow_mem_of_posPart_eq_zero hp hzrm hv0 ht
    have hsubrm : {w | morseNorm n w ≤ morseNorm n z ∧ posPart d.hk w = 0} ⊆
        {w | morseNorm n w < D.rm p hp} := fun w hw => hw.1.trans_lt hzrm
    have hsubR' := hsubrm.trans (d.lt_subset_ball (D.rm_lt_R' p hp).le)
    set θ₀ : ℝ := (D.rm p hp ^ 2 + d.r₀ ^ 2)⁻¹ with hθ₀
    have hθ₀pos : 0 < θ₀ := by positivity
    set m := θ₀ * d.r₀ ^ 2 with hm
    have hmpos : 0 < m := by positivity
    set T := ε / m + 1 with hT
    have hTpos : 0 < T := by have := div_pos hε hmpos; linarith
    by_contra hcon
    push Not at hcon
    have hODE : ∀ t ∈ Icc (-T) 0, D.flow t x ∈ d.χ '' {w | morseNorm n w < D.rm p hp} :=
      fun t ht => image_mono (fun w hw => lt_of_le_of_lt hw.1 hzrm) (hstay t ht.2)
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hrate : ∀ t ∈ Icc (-T) 0, m ≤ ModelField.theta d.r₀ (d.χ.symm (D.flow t x)) *
        morseNorm n (d.χ.symm (D.flow t x)) ^ 2 := by
      intro t ht
      have hmem := hstay t ht.2
      have hw : d.χ.symm (D.flow t x) ∈ {w | morseNorm n w ≤ morseNorm n z ∧ posPart d.hk w = 0} :=
        d.symm_mem hsubR' hmem
      have hθ : θ₀ ≤ ModelField.theta d.r₀ (d.χ.symm (D.flow t x)) :=
        ModelField.theta_ge_of_le d.hr₀ (hw.1.trans hzrm.le)
      have hnorm : d.r₀ < morseNorm n (d.χ.symm (D.flow t x)) := by
        by_contra hle
        push Not at hle
        exact hcon t ht.2 (d.mem_image_of_symm_mem (hOball (hODE t ht)) hle)
      have h1 : d.r₀ ^ 2 ≤ morseNorm n (d.χ.symm (D.flow t x)) ^ 2 :=
        pow_le_pow_left₀ d.hr₀.le hnorm.le 2
      exact mul_le_mul hθ h1 (sq_nonneg _) (ModelField.theta_pos d.hr₀ _).le
    have hlin := ModelField.nf_le_linear_of_rate d.hk (f p) hγ hrate 0
      (right_mem_Icc.2 (by linarith))
    have hγ0 : d.χ.symm (D.flow 0 x) = z := by
      rw [flow_zero, hx, d.χ.left_inv (d.hsrc z hzR)]
    rw [hγ0, hz.1] at hlin
    have hwT : d.χ.symm (D.flow (-T) x) ∈
        {w | morseNorm n w ≤ morseNorm n z ∧ posPart d.hk w = 0} :=
      d.symm_mem hsubR' (hstay (-T) (by linarith))
    have hle : morseNormalForm d.hk (f p) (d.χ.symm (D.flow (-T) x)) ≤ f p := by
      rw [morseNormalForm_split, hwT.2, norm_zero]
      nlinarith [sq_nonneg ‖negPart d.hk (d.χ.symm (D.flow (-T) x))‖]
    have hTm : m * T = ε + m := by rw [hT]; field_simp
    nlinarith
  · have hball : 2 * ε + 2 * ‖negPart d.hk z‖ ^ 2 < D.rm p hp ^ 2 := by rw [hu2]; linarith
    have hlevel : morseNormalForm d.hk (f p) z ≤ f p + ε := by rw [hz.1]; linarith
    obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_asc hf hp hε hball hv0 hlevel
    set B := 2 * ε + 2 * ‖negPart d.hk z‖ ^ 2 with hB
    have hSsub : {w : Fin n → ℝ | morseNorm n w ^ 2 ≤ B} ⊆ {w | morseNorm n w < D.rm p hp} :=
      fun w hw => lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hw hball)
    have hODE : ∀ u ∈ Icc (-t) 0, D.flow u x ∈ d.χ '' {w | morseNorm n w < D.rm p hp} :=
      fun u hu => image_mono hSsub (hstay u hu)
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hγ0 : d.χ.symm (D.flow 0 x) = z := by
      rw [flow_zero, hx, d.χ.left_inv (d.hsrc z hzR)]
    set g : ℝ → ℝ := fun u => f (D.flow u x) with hg
    have hgc : Continuous g := hf.continuous.comp (D.continuous_flow_curve x)
    have hg0 : g 0 = f p - ε := by simp [hg, hfx]
    have hgt : g (-t) = f p + ε := hft
    obtain ⟨t', ht', hgt'⟩ : ∃ t' ∈ Icc (-t) 0, g t' = f p :=
      intermediate_value_Icc' (by linarith) hgc.continuousOn
        ⟨by rw [hg0]; linarith, by rw [hgt]; linarith⟩
    refine ⟨t', ht'.2, ?_⟩
    have hprod := ModelField.normSq_negPart_mul_posPart_const d.hk hγ
    have hprod0 := hprod 0 (right_mem_Icc.2 (by linarith))
    have hprodt := hprod t' ht'
    rw [hγ0] at hprod0
    rw [← hprod0] at hprodt
    have heO := hODE t' ht'
    have hfe : f (D.flow t' x) = morseNormalForm d.hk (f p) (d.χ.symm (D.flow t' x)) :=
      d.f_eq_nf_symm (hOle heO)
    have hbal : ‖negPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 =
        ‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 := by
      have := hgt'
      rw [hg] at this
      simp only at this
      rw [hfe, morseNormalForm_split] at this
      linarith
    have h4 := hz.2
    rw [hbal] at hprodt
    have hle : ‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2 ≤ d.r₀ ^ 2 / 2 := by
      have h1 : (‖posPart d.hk (d.χ.symm (D.flow t' x))‖ ^ 2) ^ 2 ≤ (d.r₀ ^ 2 / 2) ^ 2 := by
        rw [← hprodt] at h4
        nlinarith
      exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) two_ne_zero).1 h1
    have hmn : morseNorm n (d.χ.symm (D.flow t' x)) ≤ d.r₀ := by
      refine MorseNormalChart.morseNorm_le_of_sq_le d.hr₀.le ?_
      rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hbal]
      linarith
    exact d.mem_image_of_symm_mem (hOball heO) hmn

theorem mfderiv_V_eq_zero_of_eventually_const {g : M → ℝ} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) (h : ∀ᶠ s in 𝓝 (0 : ℝ), g (D.flow s x) = g x) :
    (mfderiv I 𝓘(ℝ, ℝ) g x) (D.V x) = 0 := by
  have hγ := D.isMIntegralCurve_flow x
  have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g (D.flow 0 x) := by rw [flow_zero]; exact hg
  have hcomp := HasMFDerivAt.comp (0 : ℝ) hg'.hasMFDerivAt (hγ 0)
  have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  set a : ℝ := (mfderiv I 𝓘(ℝ, ℝ) g (D.flow 0 x)) (D.V (D.flow 0 x)) with ha
  have hDl : (mfderiv I 𝓘(ℝ, ℝ) g (D.flow 0 x)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (D.V (D.flow 0 x))) = ContinuousLinearMap.toSpanSingleton ℝ a := by
    apply ContinuousLinearMap.ext
    intro r
    change (mfderiv I 𝓘(ℝ, ℝ) g (D.flow 0 x)) (((1 : ℝ →L[ℝ] ℝ) r) • D.V (D.flow 0 x)) = r • a
    rw [map_smul]
    rfl
  have hfd' : HasDerivAt (g ∘ fun s => D.flow s x) a 0 :=
    hasDerivAt_iff_hasFDerivAt.mpr (hfd.congr_fderiv hDl)
  have hconst : HasDerivAt (g ∘ fun s => D.flow s x) 0 0 := by
    refine HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (g x)) ?_
    filter_upwards [h] with s hs
    simp [Function.comp, hs]
  have key : (mfderiv I 𝓘(ℝ, ℝ) g (D.flow 0 x)) (D.V (D.flow 0 x)) = 0 := hfd'.unique hconst
  rw [flow_zero] at key
  exact key

end GradientLikeStrip

namespace GradientLikeStrip

variable {D : GradientLikeStrip I f a b crit} [T2Space M] [I.Boundaryless]

theorem exists_flow_mem_closedSmallBall_of_mem_thick (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hp : p ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hr₀ : (D.chart p hp).r₀ ^ 2 < 2 * ε)
    (hrm : 8 * ε < D.rm p hp ^ 2) {x : M} (hx : x ∈ D.thick p hp ε c (D.chart p hp).r₀) :
    ∃ t, D.flow t x ∈ D.closedSmallBall p hp := by
  unfold thick at hx
  split_ifs at hx
  · obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    obtain ⟨t, -, ht⟩ := exists_flow_mem_closedSmallBall_of_mem_rightTube hf hp hε hr₀ hrm hz
    refine ⟨t - (f p + ε - c), ?_⟩
    rw [flow_flow, add_sub_cancel]
    exact ht
  · obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    obtain ⟨t, -, ht⟩ := exists_flow_mem_closedSmallBall_of_mem_leftTube hf hp hε hr₀ hrm hz
    refine ⟨t - (f p - ε - c), ?_⟩
    rw [flow_flow, add_sub_cancel]
    exact ht

theorem π_mem_thick (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} (hp : p ∈ crit) {ε c r : ℝ}
    (hε : 0 < ε) (hr : r ^ 2 ≤ 2 * ε) (hrm : 6 * ε < D.rm p hp ^ 2) (hc : c ∈ Icc a b)
    (hcU : ∀ y ∈ D.smallBall p hp, f y ≠ c)
    (hcε : (f p < c → f p + ε < c) ∧ (c < f p → c < f p - ε))
    {x : M} (hx : x ∈ D.regularFlowDomain c) (hmem : x ∈ D.throughBall p hp r c) :
    D.π c x ∈ D.thick p hp ε c r := by
  obtain ⟨-, s, hs, hmem⟩ := hmem
  unfold thick
  split_ifs with hlt
  · exact π_mem_rightThick hf hp hε hr hrm hc (hcε.1 hlt) hx hs hmem
  · have hne : f p ≠ c := hcU p (D.p_mem_smallBall p hp)
    have hgt : c < f p := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    exact π_mem_leftThick hf hp hε hr hrm hc (hcε.2 hgt) hx hs hmem

end GradientLikeStrip

theorem exists_trajectoryCutoff [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit) (P₀ P₁ : Set M)
    (hP : ∀ p ∈ crit, p ∈ P₀ ∨ p ∈ P₁) (hdisj : ∀ p, p ∈ P₀ → p ∈ P₁ → False) {c ε : ℝ}
    (hc : c ∈ Ioo a b) (hcU : ∀ p hp, ∀ y ∈ D.smallBall p hp, f y ≠ c) (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hcε : ∀ p (_ : p ∈ crit), (f p < c → f p + ε < c) ∧ (c < f p → c < f p - ε))
    (r' : ∀ p ∈ crit, ℝ) (hr' : ∀ p hp, (D.chart p hp).r₀ < r' p hp)
    (hnocommon : ∀ p hp q hq, p ∈ P₀ → q ∈ P₁ →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp}, ∀ t,
        D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq}) :
    ∃ μ : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a b) ∧ (∀ x, μ x ∈ Icc 0 1) ∧
      (∀ x ∈ f ⁻¹' Ioo a b, (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0) ∧
      (∀ p hp, p ∈ P₀ → ∀ x ∈ D.smallBall p hp, μ x = 0) ∧
      (∀ p hp, p ∈ P₁ → ∀ x ∈ D.smallBall p hp, μ x = 1) := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : NormalSpace M := inferInstance
  have hfc : Continuous f := hf.continuous
  have hcI : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  have hr₀ε : ∀ p hp, (D.chart p hp).r₀ ^ 2 ≤ 2 * ε := fun p hp => (hεr p hp).1.le
  have h3R : ∀ p hp, 3 * ε ≤ (D.chart p hp).R ^ 2 := fun p hp => by
    have h1 := (hεr p hp).2
    have h2 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
    linarith
  have h6 : ∀ p hp, 6 * ε < D.rm p hp ^ 2 := fun p hp => by linarith [(hεr p hp).2]
  set K₀ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₀),
    D.thick q.1 q.2 ε c (D.chart q.1 q.2).r₀ with hK₀
  set K₁ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₁),
    D.thick q.1 q.2 ε c (D.chart q.1 q.2).r₀ with hK₁
  have hK₀c : IsCompact K₀ := isCompact_iUnion fun q => isCompact_iUnion fun _ =>
    D.isCompact_thick q.1 q.2 hε (hr₀ε q.1 q.2) (h3R q.1 q.2) c
  have hK₁c : IsCompact K₁ := isCompact_iUnion fun q => isCompact_iUnion fun _ =>
    D.isCompact_thick q.1 q.2 hε (hr₀ε q.1 q.2) (h3R q.1 q.2) c
  have hKdisj : Disjoint K₀ K₁ := by
    rw [Set.disjoint_left]
    intro x hx₀ hx₁
    simp only [hK₀, hK₁, mem_iUnion, Subtype.exists, exists_prop] at hx₀ hx₁
    obtain ⟨p, hp, hpP, hxp⟩ := hx₀
    obtain ⟨q, hq, hqP, hxq⟩ := hx₁
    obtain ⟨t, ht⟩ := GradientLikeStrip.exists_flow_mem_closedSmallBall_of_mem_thick hf hp hε
      (hεr p hp).1 (hεr p hp).2 hxp
    obtain ⟨t', ht'⟩ := GradientLikeStrip.exists_flow_mem_closedSmallBall_of_mem_thick hf hq hε
      (hεr q hq).1 (hεr q hq).2 hxq
    have hmemp : D.flow t x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp} :=
      image_mono (fun y (hy : morseNorm n y ≤ _) => lt_of_le_of_lt hy (hr' p hp)) ht
    have hmemq : D.flow t' x ∈ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq} :=
      image_mono (fun y (hy : morseNorm n y ≤ _) => lt_of_le_of_lt hy (hr' q hq)) ht'
    refine hnocommon p hp q hq hpP hqP _ hmemp (t' - t) ?_
    rw [GradientLikeStrip.flow_flow, add_sub_cancel]
    exact hmemq
  obtain ⟨ν, hν0, hν1, hν01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hK₀c.isClosed hK₁c.isClosed hKdisj
  obtain ⟨N₀, hN₀, hKN₀, hνN₀⟩ := eventually_nhdsSet_iff_exists.1 hν0
  obtain ⟨N₁, hN₁, hKN₁, hνN₁⟩ := eventually_nhdsSet_iff_exists.1 hν1
  have hρ : ∀ p hp, ∃ ρ : ℝ, (D.chart p hp).r₀ < ρ ∧ ρ ≤ r' p hp ∧ ρ ^ 2 ≤ 2 * ε ∧
      (p ∈ P₀ → D.thick p hp ε c ρ ⊆ N₀) ∧ (p ∈ P₁ → D.thick p hp ε c ρ ⊆ N₁) := by
    intro p hp
    set r₁ := min (r' p hp) (Real.sqrt (2 * ε)) with hr₁
    have hr₀r₁ : (D.chart p hp).r₀ < r₁ := by
      refine lt_min (hr' p hp) ?_
      exact (Real.lt_sqrt (D.chart p hp).hr₀.le).2 (hεr p hp).1
    have hr₁sq : r₁ ^ 2 ≤ 2 * ε := by
      have h1 : r₁ ≤ Real.sqrt (2 * ε) := min_le_right _ _
      have h2 : 0 ≤ r₁ := (D.chart p hp).hr₀.le.trans hr₀r₁.le
      calc r₁ ^ 2 ≤ Real.sqrt (2 * ε) ^ 2 := pow_le_pow_left₀ h2 h1 2
        _ = 2 * ε := Real.sq_sqrt (by positivity)
    set U : Set M := if p ∈ P₀ then N₀ else N₁ with hU
    have hUopen : IsOpen U := by
      rw [hU]; split_ifs
      · exact hN₀
      · exact hN₁
    have hsub : D.thick p hp ε c (D.chart p hp).r₀ ⊆ U := by
      rw [hU]
      split_ifs with hpP
      · refine subset_trans ?_ hKN₀
        exact subset_iUnion₂_of_subset (⟨p, hp⟩ : {q // q ∈ crit}) hpP subset_rfl
      · have hpP' : p ∈ P₁ := (hP p hp).resolve_left hpP
        refine subset_trans ?_ hKN₁
        exact subset_iUnion₂_of_subset (⟨p, hp⟩ : {q // q ∈ crit}) hpP' subset_rfl
    obtain ⟨ρ, hρ, hρU⟩ := D.exists_thick_subset p hp hε (D.chart p hp).hr₀.le hr₀r₁ hr₁sq
      (h3R p hp) c hUopen hsub
    have hρ0 : 0 ≤ ρ := (D.chart p hp).hr₀.le.trans hρ.1.le
    refine ⟨ρ, hρ.1, hρ.2.trans (min_le_left _ _), (pow_le_pow_left₀ hρ0 hρ.2 2).trans hr₁sq,
      fun hpP => ?_, fun hpP => ?_⟩
    · rw [hU, ite_eq_left hpP] at hρU; exact hρU
    · have hpP' : p ∉ P₀ := fun h => hdisj p h hpP
      rw [hU, ite_eq_right hpP'] at hρU; exact hρU
  choose ρ hρ₀ hρr' hρε hρN₀ hρN₁ using hρ
  have hρR' : ∀ p hp, ρ p hp ≤ (D.chart p hp).R' := fun p hp => by
    have h1 : ρ p hp ^ 2 < D.rm p hp ^ 2 := by linarith [hρε p hp, (hεr p hp).2]
    have h2 : ρ p hp < D.rm p hp :=
      lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le h1
    exact (h2.trans (D.rm_lt_R' p hp)).le
  set A₀ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₀),
    D.throughBall q.1 q.2 (ρ q.1 q.2) c with hA₀
  set A₁ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₁),
    D.throughBall q.1 q.2 (ρ q.1 q.2) c with hA₁
  have hA₀open : IsOpen A₀ := isOpen_iUnion fun q => isOpen_iUnion fun _ =>
    D.isOpen_throughBall hfc q.1 q.2 (hρR' q.1 q.2) c
  have hA₁open : IsOpen A₁ := isOpen_iUnion fun q => isOpen_iUnion fun _ =>
    D.isOpen_throughBall hfc q.1 q.2 (hρR' q.1 q.2) c
  have hΩopen : IsOpen (D.regularFlowDomain c) := D.isOpen_regularFlowDomain hfc c
  have hmemA₀ : ∀ x, x ∈ A₀ ↔ ∃ p hp, p ∈ P₀ ∧ x ∈ D.throughBall p hp (ρ p hp) c := fun x => by
    simp only [hA₀, mem_iUnion, Subtype.exists, exists_prop]
  have hmemA₁ : ∀ x, x ∈ A₁ ↔ ∃ p hp, p ∈ P₁ ∧ x ∈ D.throughBall p hp (ρ p hp) c := fun x => by
    simp only [hA₁, mem_iUnion, Subtype.exists, exists_prop]
  have hA01 : ∀ x, x ∈ A₀ → x ∈ A₁ → False := by
    intro x hx₀ hx₁
    obtain ⟨p, hp, hpP, -, s, -, hs⟩ := (hmemA₀ x).1 hx₀
    obtain ⟨q, hq, hqP, -, s', -, hs'⟩ := (hmemA₁ x).1 hx₁
    have hmemp : D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp} :=
      image_mono (fun y (hy : morseNorm n y < _) => lt_of_lt_of_le hy (hρr' p hp)) hs
    have hmemq : D.flow s' x ∈ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq} :=
      image_mono (fun y (hy : morseNorm n y < _) => lt_of_lt_of_le hy (hρr' q hq)) hs'
    refine hnocommon p hp q hq hpP hqP _ hmemp (s' - s) ?_
    rw [GradientLikeStrip.flow_flow, add_sub_cancel]
    exact hmemq
  have hΩA₀ : ∀ x, x ∈ D.regularFlowDomain c → x ∈ A₀ → ν (D.π c x) = 0 := by
    intro x hx hx₀
    obtain ⟨p, hp, hpP, hmem⟩ := (hmemA₀ x).1 hx₀
    exact hνN₀ _ (hρN₀ p hp hpP (GradientLikeStrip.π_mem_thick hf hp hε (hρε p hp) (h6 p hp) hcI
      (hcU p hp) (hcε p hp) hx hmem))
  have hΩA₁ : ∀ x, x ∈ D.regularFlowDomain c → x ∈ A₁ → ν (D.π c x) = 1 := by
    intro x hx hx₁
    obtain ⟨p, hp, hpP, hmem⟩ := (hmemA₁ x).1 hx₁
    exact hνN₁ _ (hρN₁ p hp hpP (GradientLikeStrip.π_mem_thick hf hp hε (hρε p hp) (h6 p hp) hcI
      (hcU p hp) (hcε p hp) hx hmem))
  set μ : M → ℝ := fun x => if x ∈ A₀ then 0 else if x ∈ A₁ then 1 else
    if x ∈ D.regularFlowDomain c then ν (D.π c x) else 0 with hμ
  have hμA₀ : ∀ x ∈ A₀, μ x = 0 := fun x hx => by simp only [hμ, ite_eq_left hx]
  have hμA₁ : ∀ x ∈ A₁, μ x = 1 := fun x hx => by
    have hx₀ : x ∉ A₀ := fun h => hA01 x h hx
    simp only [hμ, ite_eq_right hx₀, ite_eq_left hx]
  have hμΩ : ∀ x ∈ D.regularFlowDomain c, μ x = ν (D.π c x) := fun x hx => by
    by_cases hx₀ : x ∈ A₀
    · rw [hμA₀ x hx₀, hΩA₀ x hx hx₀]
    by_cases hx₁ : x ∈ A₁
    · rw [hμA₁ x hx₁, hΩA₁ x hx hx₁]
    simp only [hμ, ite_eq_right hx₀, ite_eq_right hx₁, ite_eq_left hx]
  have hcover : ∀ x ∈ f ⁻¹' Ioo a b, x ∈ A₀ ∨ x ∈ A₁ ∨ x ∈ D.regularFlowDomain c := by
    intro x hx
    rcases D.mem_regularFlowDomain_or_exists_throughBall ρ hρ₀ hx with h | ⟨p, hp, hmem⟩
    · exact Or.inr (Or.inr h)
    · rcases hP p hp with hpP | hpP
      · exact Or.inl ((hmemA₀ x).2 ⟨p, hp, hpP, hmem⟩)
      · exact Or.inr (Or.inl ((hmemA₁ x).2 ⟨p, hp, hpP, hmem⟩))
  have hνπ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ν (D.π c x)) :=
    ν.contMDiff.comp (D.contMDiff_π hf c)
  have hsmooth : ∀ x ∈ f ⁻¹' Ioo a b, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ μ x := by
    intro x hx
    rcases hcover x hx with hx₀ | hx₁ | hxΩ
    · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hA₀open.mem_nhds hx₀] with y hy
      exact hμA₀ y hy
    · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hA₁open.mem_nhds hx₁] with y hy
      exact hμA₁ y hy
    · refine (hνπ x).congr_of_eventuallyEq ?_
      filter_upwards [hΩopen.mem_nhds hxΩ] with y hy
      exact hμΩ y hy
  refine ⟨μ, fun x hx => (hsmooth x hx).contMDiffWithinAt, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hμ]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hν01 _
    · exact ⟨le_rfl, zero_le_one⟩
  · intro x hx
    refine GradientLikeStrip.mfderiv_V_eq_zero_of_eventually_const
      ((hsmooth x hx).mdifferentiableAt (by simp)) ?_
    have hflow0 : ∀ O : Set M, IsOpen O → x ∈ O → ∀ᶠ s in 𝓝 (0 : ℝ), D.flow s x ∈ O := by
      intro O hO hxO
      have : {s : ℝ | D.flow s x ∈ O} ∈ 𝓝 (0 : ℝ) :=
        (D.continuous_flow_curve x).continuousAt.preimage_mem_nhds
          (by rw [GradientLikeStrip.flow_zero]; exact hO.mem_nhds hxO)
      exact this
    rcases hcover x hx with hx₀ | hx₁ | hxΩ
    · filter_upwards [hflow0 A₀ hA₀open hx₀] with s hs
      rw [hμA₀ _ hs, hμA₀ x hx₀]
    · filter_upwards [hflow0 A₁ hA₁open hx₁] with s hs
      rw [hμA₁ _ hs, hμA₁ x hx₁]
    · filter_upwards [hflow0 (D.regularFlowDomain c) hΩopen hxΩ] with s hs
      rw [hμΩ _ hs, hμΩ x hxΩ, GradientLikeStrip.π_flow hf hcI hcU hxΩ hs]
  · intro p hp hpP x hx
    refine hμA₀ x ((hmemA₀ x).2 ⟨p, hp, hpP, ?_⟩)
    refine D.mem_throughBall_of_mem_ball p hp (hρR' p hp) ?_
    exact image_mono (fun y (hy : morseNorm n y < _) => hy.trans (hρ₀ p hp)) hx
  · intro p hp hpP x hx
    refine hμA₁ x ((hmemA₁ x).2 ⟨p, hp, hpP, ?_⟩)
    refine D.mem_throughBall_of_mem_ball p hp (hρR' p hp) ?_
    exact image_mono (fun y (hy : morseNorm n y < _) => hy.trans (hρ₀ p hp)) hx

end

end DifferentialGeometry.Topology
