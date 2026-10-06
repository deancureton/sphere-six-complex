module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerBirth

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

def isPartnerConfig (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] (f : M → ℝ) (a b : ℝ) (p q : M) : Prop :=
  MorseStrip I f a b ∧ ∃ crit : Finset M, (∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
  ∃ (hp : p ∈ crit) (hq : q ∈ crit) (D : GradientLikeStrip I f a b crit)
    (hkq : (D.chart q hq).k = 2), (D.chart p hp).k = 1 ∧
  ∃ εp εq : ℝ, 0 < εp ∧ 0 < εq ∧
    (D.chart p hp).r₀ ^ 2 < 2 * εp ∧ 8 * εp < D.rm p hp ^ 2 ∧
    (D.chart q hq).r₀ ^ 2 < 2 * εq ∧ 8 * εq < D.rm q hq ^ 2 ∧ f p + εp < f q - εq ∧
    (∀ x ∈ crit, x ≠ p → x ≠ q → 2 * εp < |f x - f p| ∧ 2 * εq < |f x - f q|) ∧
    (∀ x (hx : x ∈ crit), x ≠ p → ∀ y ∈ D.closedSmallBall x hx, f y ∉ Icc (f p) (f p + εp)) ∧
    (∀ y ∈ (D.chart q hq).leftModelSphere εq, ∀ s ∈ Icc 0 (f q - εq - (f p + εp)),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx) ∧
    ∃ c : ℝ, f p + εp ≤ c ∧ c ≤ f q - εq ∧
      meetsRightOnce D p hp εp c (leftLoop D q hq hkq εq c)

def isPartnerConfigBelow (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] (f : M → ℝ) (a b : ℝ) (p q : M) (ρ : ℝ) : Prop :=
  MorseStrip I f a b ∧ ∃ crit : Finset M, (∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
  ∃ (hp : p ∈ crit) (hq : q ∈ crit) (D : GradientLikeStrip I f a b crit)
    (hkq : (D.chart q hq).k = 2), (D.chart p hp).k = 1 ∧
  ∃ εp εq : ℝ, 0 < εp ∧ 0 < εq ∧
    (∀ x hx, (D.chart x hx).r₀ ≤ ρ ∧ 16 * (D.chart x hx).r₀ < D.rm x hx ∧
      (D.chart x hx).r₀ ^ 2 < εp ∧ (D.chart x hx).r₀ ^ 2 < εq) ∧
    (D.chart p hp).r₀ ^ 2 < 2 * εp ∧ 8 * εp < D.rm p hp ^ 2 ∧
    (D.chart q hq).r₀ ^ 2 < 2 * εq ∧ 8 * εq < D.rm q hq ^ 2 ∧ f p + εp < f q - εq ∧
    (∀ x ∈ crit, x ≠ p → x ≠ q → 2 * εp < |f x - f p| ∧ 2 * εq < |f x - f q|) ∧
    (∀ x (hx : x ∈ crit), x ≠ p → ∀ y ∈ D.closedSmallBall x hx, f y ∉ Icc (f p) (f p + εp)) ∧
    (∀ y ∈ (D.chart q hq).leftModelSphere εq, ∀ s ∈ Icc 0 (f q - εq - (f p + εp)),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx) ∧
    ∃ c : ℝ, f p + εp ≤ c ∧ c ≤ f q - εq ∧
      meetsRightOnce D p hp εp c (leftLoop D q hq hkq εq c)

def isSmallPartnerConfig (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] (f : M → ℝ) (a b : ℝ) (p q : M) : Prop :=
  MorseStrip I f a b ∧ ∃ crit : Finset M, (∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
  ∃ (hp : p ∈ crit) (hq : q ∈ crit) (D : GradientLikeStrip I f a b crit)
    (hkq : (D.chart q hq).k = 2), (D.chart p hp).k = 1 ∧
  ∃ ε δ : ℝ, 0 < ε ∧ ε < δ ∧
    (∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm x hx ^ 2) ∧
    (∀ x hx, (D.chart x hx).R ^ 2 < 2 * δ) ∧
    a < f p - 8 * δ ∧ f p + 8 * δ < f q ∧ f q + 8 * δ < b ∧
    (∀ x ∈ crit, x ≠ p → x ≠ q → 8 * δ < |f x - f p| ∧ 8 * δ < |f x - f q|) ∧
    (∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 (f q - f p - 2 * ε),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx) ∧
    ∃ c : ℝ, f p + ε ≤ c ∧ c ≤ f q - ε ∧ meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)

def isFinePartnerConfig (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] (f : M → ℝ) (a b : ℝ) (p q : M) : Prop :=
  MorseStrip I f a b ∧ ∃ crit : Finset M, (∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
  ∃ (hp : p ∈ crit) (hq : q ∈ crit) (D : GradientLikeStrip I f a b crit)
    (hkq : (D.chart q hq).k = 2), (D.chart p hp).k = 1 ∧
  ∃ ε δ r' : ℝ, 0 < ε ∧ ε < δ ∧ 0 < r' ∧ r' ^ 2 < ε ∧
    (∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm x hx ^ 2 ∧
      (D.chart x hx).r₀ < r') ∧
    (∀ x hx, (D.chart x hx).R ^ 2 < 2 * δ) ∧
    a < f p - 8 * δ ∧ f p + 8 * δ < f q ∧ f q + 8 * δ < b ∧
    (∀ x ∈ crit, x ≠ p → x ≠ q → 8 * δ < |f x - f p| ∧ 8 * δ < |f x - f q|) ∧
    (∀ x (hx : x ∈ crit), f p < f x → f x < f q →
      ∀ z ∈ (D.chart q hq).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t z ∉ (D.chart x hx).χ '' {y | morseNorm n y < r'}) ∧
    (∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 (f q - f p - 2 * ε),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx) ∧
    ∃ c : ℝ, f p + ε ≤ c ∧ c ≤ f q - ε ∧ meetsRightOnce D p hp ε c (leftLoop D q hq hkq ε c)

section Isolation

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_nocommon_radius (hf : MorseStrip I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε)
    (hcst : (D.chart q hq).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm q hq ^ 2)
    (hca : a ≤ c) (hc : c < f q - ε)
    (hdesc : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 (f q - ε - c),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx)
    {η : ℝ} (hη : 0 < η) :
    ∃ (D' : GradientLikeStrip I f a b crit) (r' : ℝ), 0 < r' ∧ r' < η ∧ r' ^ 2 < ε ∧
      (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
        (D'.chart x hx).R = (D.chart x hx).R ∧ (D'.chart x hx).R' = (D.chart x hx).R' ∧
        (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀ ∧ (D'.chart x hx).r₀ < r') ∧
      (∀ x hx, D'.rm x hx = D.rm x hx) ∧
      (∀ z, (∀ x hx, z ∉ D.closedSmallBall x hx) → D'.V z = D.V z) ∧
      ∀ x (hx : x ∈ crit), c + ε ≤ f x → f x ≤ f q - ε →
        ∀ z ∈ (D'.chart q hq).χ '' {y | morseNorm n y < r'}, ∀ t,
          D'.flow t z ∉ (D'.chart x hx).χ '' {y | morseNorm n y < r'} := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  set d := D.chart q hq with hd
  have hqb : f q ∈ Ioo a b := ((hcrit q).1 hq).1
  have hrmq := D.hrm q hq
  have hrm0 := D.rm_pos q hq
  have hR2 : 2 * ε ≤ d.R ^ 2 := by
    have h1 : D.rm q hq ^ 2 ≤ d.R ^ 2 := pow_le_pow_left₀ hrm0.le hrmq.2 2
    linarith [hcst.2]
  set T := f q - ε - c with hT
  have hT0 : 0 ≤ T := by linarith
  set W : Set (Fin n → ℝ) := {y | y ∈ Metric.ball (0 : Fin n → ℝ) d.R' ∧
    ∀ s ∈ Icc 0 T, D.flow s (d.χ y) ∉ D.closedSmallBalls} with hW
  have hK := D.isClosed_closedSmallBalls
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro y₀ ⟨hy₀b, hy₀⟩
    have hχc : ContinuousAt d.χ y₀ :=
      d.χ.continuousOn.continuousAt (d.χ.open_source.mem_nhds (d.hball hy₀b))
    have hG : ∀ s, ContinuousAt (fun z : (Fin n → ℝ) × ℝ => D.flow z.2 (d.χ z.1)) (y₀, s) :=
      fun s => D.continuous_flow_joint.continuousAt.comp
        (continuousAt_snd.prodMk (hχc.comp continuousAt_fst))
    have hev : ∀ s ∈ Icc (0 : ℝ) T, ∀ᶠ z : (Fin n → ℝ) × ℝ in 𝓝 (y₀, s),
        D.flow z.2 (d.χ z.1) ∉ D.closedSmallBalls := fun s hs =>
      (hG s).eventually_mem (hK.isOpen_compl.mem_nhds (hy₀ s hs))
    have h1 := isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun (y : Fin n → ℝ) (s : ℝ) => D.flow s (d.χ y) ∉ D.closedSmallBalls) hev
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds hy₀b] with y hy hyb
    exact ⟨hyb, hy⟩
  have hSW : d.leftModelSphere ε ⊆ W := by
    intro y hy
    refine ⟨d.mem_ball_of_le (d.morseNorm_le_R_of_mem_leftModelSphere hR2 hy), fun s hs => ?_⟩
    rw [GradientLikeStrip.notMem_closedSmallBalls_iff]
    exact fun x hx => hdesc y hy s hs x hx
  obtain ⟨δW, hδW, hδWsub⟩ := D.exists_leftTube_subset_open q hq hε hWo hSW
  obtain ⟨δr, hδr, hδrP⟩ := exists_pos_forall_small_finset crit
    (fun x δ => ∀ hx : x ∈ crit, δ ≤ (D.chart x hx).r₀) (fun x hx =>
      ⟨(D.chart x hx).r₀, (D.chart x hx).hr₀, fun δ _ hδ _ => hδ⟩)
  set r' := min (min (η / 2) δr) (min 1 (min (ε / 4) (8 * ε * δW))) with hr'def
  have hr'0 : 0 < r' :=
    lt_min (lt_min (by linarith) hδr) (lt_min one_pos (lt_min (by linarith) (by positivity)))
  have hr'η : r' < η := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hr'δr : r' ≤ δr := (min_le_left _ _).trans (min_le_right _ _)
  have hr'1 : r' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hr'ε4 : r' ≤ ε / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr'δW : r' ≤ 8 * ε * δW :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr'r₀ : ∀ x (hx : x ∈ crit), r' ≤ (D.chart x hx).r₀ := fun x hx =>
    hδrP x hx r' hr'0 hr'δr hx
  have hr'sq : r' ^ 2 ≤ r' := pow_le_of_le_one hr'0.le hr'1 two_ne_zero
  have hr'sqε : r' ^ 2 < ε / 2 := by linarith
  obtain ⟨D', hD'ch, hD'r₀, hD'rm, hD'V, φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ :=
    exists_shrinkAll_factor hfs D hr'0 hr'r₀
  have hmain : ∀ x (hx : x ∈ crit), c + ε ≤ f x → f x ≤ f q - ε → ∀ y, morseNorm n y < r' →
      ∀ t, D.flow t (d.χ y) ∉ (D.chart x hx).χ '' {y | morseNorm n y < r'} := by
    intro x hx hx1 hx2 y hy t hmem
    obtain ⟨y', hy'0, hy'eq⟩ := hmem
    have hy' : morseNorm n y' < r' := hy'0
    set dx := D.chart x hx with hdx
    set w := D.flow t (d.χ y) with hw
    have hxq : x ≠ q := by rintro rfl; linarith
    have hr'x := hr'r₀ x hx
    have hr₀Rx : dx.r₀ < dx.R := D.r₀_lt_R x hx
    have hr₀R'x : dx.r₀ < dx.R' := D.r₀_lt_R' x hx
    have hy'R : morseNorm n y' ≤ dx.R := by linarith
    have hfw : f w = morseNormalForm dx.hk (f x) y' := by rw [← hy'eq]; exact dx.hnorm y' hy'R
    have hsq' := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      dx.hk y'
    have hsplit' := DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split
      dx.hk (f x) y'
    have hy'sq : morseNorm n y' ^ 2 < r' ^ 2 :=
      pow_lt_pow_left₀ hy' (ModelField.morseNorm_nonneg y') two_ne_zero
    have hfw_up : f w < f x + r' ^ 2 := by
      rw [hfw, hsplit']
      linarith [sq_nonneg ‖negPart dx.hk y'‖, sq_nonneg ‖posPart dx.hk y'‖]
    have hfw_low : c < f w := by
      rw [hfw, hsplit']
      linarith [sq_nonneg ‖negPart dx.hk y'‖, sq_nonneg ‖posPart dx.hk y'‖]
    have hw_ball : w ∈ dx.χ '' Metric.ball 0 dx.R' :=
      ⟨y', dx.lt_subset_ball (r := r') (by linarith) hy', hy'eq⟩
    have hw_closed : w ∈ D.closedSmallBalls :=
      mem_iUnion.2 ⟨⟨x, hx⟩, ⟨y', show morseNorm n y' ≤ dx.r₀ by linarith, hy'eq⟩⟩
    have hnotq : ∀ S : Set (Fin n → ℝ), S ⊆ Metric.ball 0 d.R' → w ∉ d.χ '' S :=
      fun S hS hwS => Set.disjoint_left.1 (D.disjoint x hx q hq hxq) hw_ball (image_mono hS hwS)
    have hr'q := hr'r₀ q hq
    have hr₀Rq : d.r₀ < d.R := D.r₀_lt_R q hq
    have hr₀rmq : d.r₀ < D.rm q hq := D.r₀_lt_rm q hq
    have hrmR'q : D.rm q hq < d.R' := D.rm_lt_R' q hq
    have hyR : morseNorm n y ≤ d.R := by linarith
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      d.hk y
    have hsplit := DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split
      d.hk (f q) y
    have hysq : morseNorm n y ^ 2 < r' ^ 2 :=
      pow_lt_pow_left₀ hy (ModelField.morseNorm_nonneg y) two_ne_zero
    have hfz : f (d.χ y) = morseNormalForm d.hk (f q) y := d.hnorm y hyR
    rcases le_or_gt t 0 with ht | ht
    · have h1 := GradientLikeStrip.le_f_flow_of_nonpos (D := D) hfs (d.χ y) ht
      rw [← hw, hfz, hsplit] at h1
      linarith [sq_nonneg ‖negPart d.hk y‖, sq_nonneg ‖posPart d.hk y‖]
    · by_cases hu : negPart d.hk y = 0
      · have h1 := GradientLikeStrip.flow_mem_of_negPart_eq_zero (D := D) hq (by linarith) hu
          ht.le
        exact hnotq _ (fun z hz => mem_ball_of_morseNorm_lt (lt_of_le_of_lt hz.1 (by linarith)))
          h1
      · have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm q hq ^ 2 := by
          linarith [sq_nonneg ‖negPart d.hk y‖, sq_nonneg ‖posPart d.hk y‖, hcst.2]
        have hlevel : f q - ε ≤ morseNormalForm d.hk (f q) y := by
          rw [hsplit]
          linarith [sq_nonneg ‖negPart d.hk y‖, sq_nonneg ‖posPart d.hk y‖]
        obtain ⟨t₁, ht₁0, hft₁, hstay, htube⟩ :=
          GradientLikeStrip.exists_exit_mem_leftTube_of_le (D := D) hfs hq hε hball hu hlevel
            (ρ := r') hy.le
        rcases le_or_gt t t₁ with htt | htt
        · refine hnotq _ (fun z hz => mem_ball_of_morseNorm_lt ?_) (hstay t ⟨ht.le, htt⟩)
          have h2 : morseNorm n z < D.rm q hq :=
            lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hz hball)
          linarith
        · obtain ⟨ye, hye, hyeq⟩ := htube
          have hyeW : ye ∈ W := by
            refine hδWsub ⟨hye.1, ?_⟩
            have h3 := d.normSq_posPart_le_of_mem_leftTube hε hye
            have h4 : r' ^ 4 ≤ r' := pow_le_of_le_one hr'0.le hr'1 (by norm_num)
            have h5 : r' ^ 4 / (8 * ε) ≤ δW := by
              have h6 : δW * (8 * ε) = 8 * ε * δW := by ring
              rw [div_le_iff₀ (by positivity), h6]; linarith
            linarith
          set e := D.flow t₁ (d.χ y) with he
          have hwe : w = D.flow (t - t₁) e := by
            rw [hw, he, GradientLikeStrip.flow_flow]; congr 1; ring
          have hfree : ∀ s ∈ Icc 0 T, D.flow s e ∉ D.closedSmallBalls := by
            intro s hs
            have := hyeW.2 s hs
            rwa [hyeq] at this
          rcases le_or_gt (t - t₁) T with htT | htT
          · exact hfree (t - t₁) ⟨by linarith, htT⟩ (hwe ▸ hw_closed)
          · have havoid : ∀ s ∈ uIcc 0 T, ∀ p (hp : p ∈ crit), D.flow s e ∉ D.smallBall p hp := by
              intro s hs p hp hmem'
              rw [uIcc_of_le hT0] at hs
              exact hfree s hs (mem_iUnion.2 ⟨⟨p, hp⟩, D.smallBall_subset_closedSmallBall p hp hmem'⟩)
            have hunit := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs (x := e) (T := T)
              ⟨by rw [hft₁]; linarith, by rw [hft₁]; linarith [hqb.2]⟩
              ⟨by rw [hft₁]; linarith, by rw [hft₁]; linarith [hqb.2]⟩ havoid T right_mem_uIcc
            have hanti := GradientLikeStrip.f_flow_antitone (D := D) hfs e htT.le
            simp only at hanti
            rw [← hwe, hunit, hft₁] at hanti
            linarith
  refine ⟨D', r', hr'0, hr'η, by linarith, fun x hx => ?_, hD'rm, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hD'ch x hx
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩
    · rw [hD'r₀ x hx]; linarith [hr'r₀ x hx]
    · rw [hD'r₀ x hx]; linarith
  · intro z hz
    refine hD'V z fun p hp hmem => hz p hp ?_
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy2 : morseNorm n y ≤ (D.chart p hp).r₀ / 2 := hy
    have h0 := (D.chart p hp).hr₀
    exact ⟨y, show morseNorm n y ≤ (D.chart p hp).r₀ by linarith, rfl⟩
  · intro x hx hx1 hx2 z hz t
    rw [(hD'ch q hq).1] at hz
    rw [(hD'ch x hx).1]
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨σ, -, -, -, hσ⟩ := GradientLikeStrip.exists_reparam D D' hφc hm hφb hφV (d.χ y)
    rw [hσ t]
    exact hmain x hx hx1 hx2 y hy (σ t)

theorem exists_partner_below {p q : M} (h : isPartnerConfig I f a b p q) {ρ : ℝ}
    (hρ : 0 < ρ) : isPartnerConfigBelow I f a b p q ρ := by
  classical
  obtain ⟨hf, crit, hcrit, hp, hq, D, hkq, hkp, εp, εq, hεp, hεq, hp1, hp2, hq1, hq2, hpq,
    hsep, hballs, hdesc, c, hc1, hc2, hmeet⟩ := h
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  let g : M → ℝ := fun x => if hx : x ∈ crit then min (D.chart x hx).r₀ (D.rm x hx / 16) else 1
  let S : Finset ℝ := insert (min (min ρ 1) (min εp εq)) (crit.image g)
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  have hSpos : ∀ y ∈ S, 0 < y := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact lt_min (lt_min hρ one_pos) (lt_min hεp hεq)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      simp only [g, hx, ↓reduceDIte]
      exact lt_min (D.chart x hx).hr₀ (by linarith [D.rm_pos x hx])
  have hρ'pos : 0 < S.min' hSne := hSpos _ (Finset.min'_mem S hSne)
  have hρ'1 : S.min' hSne ≤ min (min ρ 1) (min εp εq) :=
    Finset.min'_le S _ (Finset.mem_insert_self _ _)
  have hρ'g : ∀ x (hx : x ∈ crit), S.min' hSne ≤ (D.chart x hx).r₀ ∧
      S.min' hSne ≤ D.rm x hx / 16 := by
    intro x hx
    have := Finset.min'_le S (g x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hx))
    simp only [g, hx, ↓reduceDIte] at this
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
  obtain ⟨⟨hρ'ρ, hρ'one⟩, hρ'εp, hρ'εq⟩ : (S.min' hSne ≤ ρ ∧ S.min' hSne ≤ 1) ∧
      S.min' hSne ≤ εp ∧ S.min' hSne ≤ εq := by
    simpa only [le_min_iff] using hρ'1
  set ρ' := S.min' hSne with hρ'def
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ :=
    GradientLikeStrip.exists_shrinkAll hfs D hρ'pos (fun x hx => (hρ'g x hx).1)
  have hkq' : (E.chart q hq).k = 2 := (hE1 q hq).2.1.trans hkq
  have hkp' : (E.chart p hp).k = 1 := (hE1 p hp).2.1.trans hkp
  have hball_sub : ∀ x (hx : x ∈ crit), E.closedSmallBall x hx ⊆ D.closedSmallBall x hx := by
    intro x hx y hy
    simp only [GradientLikeStrip.closedSmallBall, (hE1 x hx).1, hE2 x hx] at hy ⊢
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, ?_, rfl⟩
    have hz' : morseNorm n z ≤ ρ' / 2 := hz
    change morseNorm n z ≤ (D.chart x hx).r₀
    linarith [(hρ'g x hx).1]
  have hV : ∀ z, (∀ x (hx : x ∈ crit), z ∉ D.closedSmallBall x hx) → E.V z = D.V z := by
    intro z hz
    apply hE4
    intro x hx hmem
    apply hz x hx
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy' : morseNorm n y ≤ (D.chart x hx).r₀ / 2 := hy
    change (D.chart x hx).χ y ∈ (D.chart x hx).χ '' {y | morseNorm n y ≤ (D.chart x hx).r₀}
    exact ⟨y, show morseNorm n y ≤ (D.chart x hx).r₀ by linarith [(D.chart x hx).hr₀], rfl⟩
  have hflowEq : ∀ x T, 0 ≤ T →
      (∀ s ∈ Icc 0 T, ∀ y (hy : y ∈ crit), D.flow s x ∉ D.closedSmallBall y hy) →
      E.flow T x = D.flow T x := by
    intro x T hT hfree
    apply flow_eq_of_agree_along D E
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact hV _ (hfree s hs)
  have hLS : (E.chart q hq).leftModelSphere εq = (D.chart q hq).leftModelSphere εq :=
    GradientLikeStrip.leftModelSphere_eq (hE1 q hq).2.1 εq
  have hdesc' : ∀ y ∈ (E.chart q hq).leftModelSphere εq, ∀ s ∈ Icc 0 (f q - εq - (f p + εp)),
      ∀ x (hx : x ∈ crit), E.flow s ((E.chart q hq).χ y) ∉ E.closedSmallBall x hx := by
    intro y hy s hs x hx
    rw [hLS] at hy
    rw [(hE1 q hq).1, hflowEq _ s hs.1
      (fun s' hs' x' hx' => hdesc y hy s' ⟨hs'.1, hs'.2.trans hs.2⟩ x' hx')]
    exact fun hm => hdesc y hy s hs x hx (hball_sub x hx hm)
  have hT : f q - εq - c ∈ Icc 0 (f q - εq - (f p + εp)) :=
    ⟨by linarith, by linarith⟩
  have hleftPt : ∀ t, ∃ y ∈ (D.chart q hq).leftModelSphere εq,
      leftPt D q hq hkq εq t = (D.chart q hq).χ y := by
    intro t
    refine ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hεq.le ?_, rfl⟩
    intro h0
    have h0' := congrFun h0 (Fin.cast hkq.symm 0)
    have h1' := congrFun h0 (Fin.cast hkq.symm 1)
    simp [circ2] at h0' h1'
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
  have hloop := leftLoop_congr D E hq hq hkq hkq' (hE1 q hq).1 rfl (ε := εq) (c := c)
    (fun t => by
      obtain ⟨y, hy, hyeq⟩ := hleftPt t
      rw [hyeq]
      exact hflowEq _ _ hT.1 (fun s hs => hdesc y hy s ⟨hs.1, hs.2.trans hT.2⟩))
  have hRsq : ∀ x (hx : x ∈ crit), D.rm x hx ^ 2 ≤ (D.chart x hx).R ^ 2 := fun x hx =>
    pow_le_pow_left₀ (D.rm_pos x hx).le (D.hrm x hx).2 2
  have hqI := ((hcrit q).1 hq).1
  have hpI := ((hcrit p).1 hp).1
  have hfree : ∀ t, descendsFreely D (c - (f p + εp)) (leftLoop D q hq hkq εq c t) := by
    intro t s hs x hx
    obtain ⟨y, hy, hyeq⟩ := hleftPt t
    change D.flow s (D.flow (f q - εq - c) (leftPt D q hq hkq εq t)) ∉ _
    rw [hyeq, D.flow_flow]
    exact hdesc y hy _ ⟨by linarith [hs.1, hT.1], by linarith [hs.2]⟩ x hx
  have hlev : ∀ t, f (leftLoop D q hq hkq εq c t) = c := by
    intro t
    obtain ⟨y, hy, hyeq⟩ := hleftPt t
    have hfy : f ((D.chart q hq).χ y) = f q - εq :=
      (D.chart q hq).f_chart_of_mem_leftModelSphere (by linarith [hRsq q hq]) hy
    change f (D.flow (f q - εq - c) (leftPt D q hq hkq εq t)) = c
    rw [hyeq]
    have := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs (x := (D.chart q hq).χ y)
      (T := f q - εq - c) (by rw [hfy]; constructor <;> linarith [hpI.1, hqI.2])
      (by rw [hfy]; constructor <;> linarith [hpI.1, hqI.2])
      (fun s hs x hx hm => by
        rw [uIcc_of_le hT.1] at hs
        exact hdesc y hy s ⟨hs.1, hs.2.trans hT.2⟩ x hx
          (D.smallBall_subset_closedSmallBall x hx hm))
      _ right_mem_uIcc
    rw [this, hfy]
    ring
  have hmeet' : meetsRightOnce E p hp εp c (leftLoop E q hq hkq' εq c) := by
    rw [hloop.2]
    refine meetsRightOnce_transfer hfs D E hp hp (hE1 p hp).1 (hE1 p hp).2.1
      (hE1 p hp).2.2.1.le rfl hεp ?_ hc1 (by linarith [hqI.2]) hlev hfree
      (fun t => hflowEq _ _ (by linarith) (hfree t)) hmeet
    rw [(hE1 p hp).2.2.1]
    linarith [hRsq p hp]
  have hrad : ∀ x hx, (E.chart x hx).r₀ ≤ ρ ∧ 16 * (E.chart x hx).r₀ < E.rm x hx ∧
      (E.chart x hx).r₀ ^ 2 < εp ∧ (E.chart x hx).r₀ ^ 2 < εq := by
    intro x hx
    rw [hE2 x hx, hE3 x hx]
    have hsq : ρ' * ρ' ≤ ρ' * 1 := mul_le_mul_of_nonneg_left hρ'one hρ'pos.le
    refine ⟨by linarith, by linarith [(hρ'g x hx).2, D.rm_pos x hx], by nlinarith, by nlinarith⟩
  exact ⟨hf, crit, hcrit, hp, hq, E, hkq', hkp', εp, εq, hεp, hεq, hrad,
    by linarith [(hrad p hp).2.2.1], by rw [hE3]; exact hp2,
    by linarith [(hrad q hq).2.2.2], by rw [hE3]; exact hq2, hpq, hsep,
    fun x hx hxp y hy => hballs x hx hxp y (hball_sub x hx hy), hdesc', c, hc1, hc2, hmeet'⟩

theorem exists_small_partner {p q : M}
    (h : isPartnerConfig I f a b p q) : isSmallPartnerConfig I f a b p q := by
  obtain ⟨hf, C, hC, hp, hq, D, hkq, hkp, εp, εq, hεp, hεq, hr₀p, hrmp, hr₀q, hrmq, hpq, hsep,
    hballs, hdesc, c, hc1, hc2, hmeet⟩ := h
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfp : f p ∈ Ioo a b := ((hC p).1 hp).1
  have hfq : f q ∈ Ioo a b := ((hC q).1 hq).1
  have hLMS : ∀ {z : M} (d₁ d₂ : MorseNormalChart I f z), d₁.k = d₂.k → ∀ e : ℝ,
      d₁.leftModelSphere e = d₂.leftModelSphere e := by
    intro z d₁ d₂ hk e
    cases d₁
    cases d₂
    simp only at hk
    subst hk
    rfl
  have hcirc : ∀ (k : ℕ) (hk : k = 2) (t : ℝ),
      (fun i : Fin k => circ2 t (Fin.cast hk i)) ≠ 0 := by
    intro k hk t
    subst hk
    intro h0
    have e0 : Real.cos (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 0
    have e1 : Real.sin (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 1
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [e0, e1] at this
    norm_num at this
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_min_image C.attach (fun y => D.rm y.1 y.2)
    ⟨⟨p, hp⟩, Finset.mem_attach _ _⟩
  have hm0 : 0 < D.rm y₀.1 y₀.2 := D.rm_pos _ _
  have hmle : ∀ x (hx : x ∈ C), D.rm y₀.1 y₀.2 ≤ D.rm x hx := fun x hx =>
    hy₀ ⟨x, hx⟩ (Finset.mem_attach _ _)
  have hmin1 : min εp εq ≤ εp := min_le_left _ _
  have hmin2 : min εp εq ≤ εq := min_le_right _ _
  have hmin0 : 0 < min εp εq := lt_min hεp hεq
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ min εp εq / 4 ∧ δ ≤ (f p - a) / 9 ∧
      δ ≤ (b - f q) / 9 :=
    ⟨min (min εp εq / 4) (min ((f p - a) / 9) ((b - f q) / 9)),
      lt_min (by positivity) (lt_min (by linarith [hfp.1]) (by linarith [hfq.2])),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨s, hs0, hsm, hsδ, hs1, hsp, hsq⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ D.rm y₀.1 y₀.2 ∧ s ≤ δ ∧
      s ≤ 1 ∧ s ≤ εp ∧ s ≤ εq :=
    ⟨min (min (D.rm y₀.1 y₀.2) δ) (min 1 (min εp εq)),
      lt_min (lt_min hm0 hδ0) (lt_min one_pos hmin0),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      ((min_le_right _ _).trans (min_le_right _ _)).trans hmin1,
      ((min_le_right _ _).trans (min_le_right _ _)).trans hmin2⟩
  have hs2 : s ^ 2 ≤ s := by rw [sq]; exact mul_le_of_le_one_right hs0.le hs1
  have hsq0 : 0 < s ^ 2 := by positivity
  set ε : ℝ := s ^ 2 / 48 with hεdef
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := by rw [hεdef]; linarith
  have hεp' : ε ≤ εp := by rw [hεdef]; linarith
  have hεq' : ε ≤ εq := by rw [hεdef]; linarith
  have hcb : c ≤ b := by linarith [hfq.2]
  obtain ⟨D₂, r', -, hr'η, -, hch, hrm2, hV2, -⟩ :=
    exists_nocommon_radius (c := f p + εp) hf hC D hq hεq ⟨hr₀q, hrmq⟩ (by linarith [hfp.1]) hpq
      hdesc (η := s / 5) (by positivity)
  have hr₀2 : ∀ x (hx : x ∈ C), (D₂.chart x hx).r₀ < s / 5 := fun x hx =>
    (hch x hx).2.2.2.2.2.trans hr'η
  have hr₀2sq : ∀ x (hx : x ∈ C), (D₂.chart x hx).r₀ ^ 2 < 2 * ε := by
    intro x hx
    have h1 := hr₀2 x hx
    have h2 := (D₂.chart x hx).hr₀
    have h3 := pow_lt_pow_left₀ h1 h2.le two_ne_zero
    have h4 : (s / 5) ^ 2 = s ^ 2 / 25 := by ring
    rw [hεdef]
    linarith
  have hsrm2 : ∀ x (hx : x ∈ C), s ≤ D₂.rm x hx := fun x hx => by
    rw [hrm2 x hx]; exact hsm.trans (hmle x hx)
  have hsR2 : ∀ x (hx : x ∈ C), s ≤ (D₂.chart x hx).R := fun x hx =>
    (hsrm2 x hx).trans (D₂.hrm x hx).2
  have hcSB : ∀ x (hx : x ∈ C), D₂.closedSmallBall x hx ⊆ D.closedSmallBall x hx := by
    intro x hx
    unfold GradientLikeStrip.closedSmallBall
    rw [(hch x hx).1]
    exact image_mono fun y (hy : morseNorm n y ≤ _) => hy.trans (hch x hx).2.2.2.2.1
  have hkq₂ : (D₂.chart q hq).k = 2 := (hch q hq).2.1.trans hkq
  have hLMS2 : ∀ e, (D₂.chart q hq).leftModelSphere e = (D.chart q hq).leftModelSphere e :=
    hLMS _ _ (hch q hq).2.1
  have hRq : 2 * εq ≤ (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    have h3 := pow_le_pow_left₀ h2.le h1 2
    linarith
  have hleftPt : ∀ e t : ℝ, 0 ≤ e →
      (D.chart q hq).sphereParam e (fun i => circ2 t (Fin.cast hkq i)) ∈
        (D.chart q hq).leftModelSphere e := fun e t he =>
    (D.chart q hq).sphereParam_mem_leftModelSphere he (hcirc _ hkq t)
  have hagree : ∀ (z : M) (T : ℝ), 0 ≤ T →
      (∀ u ∈ Icc 0 T, ∀ x (hx : x ∈ C), D.flow u z ∉ D.closedSmallBall x hx) →
      D₂.flow T z = D.flow T z := by
    intro z T hT hfree
    apply flow_eq_of_agree_along D D₂
    intro u hu
    rw [uIcc_of_le hT] at hu
    exact hV2 _ fun x hx => hfree u hu x hx
  set γ := leftLoop D q hq hkq εq c with hγdef
  have hγ2 : leftLoop D₂ q hq hkq₂ εq c = γ :=
    (leftLoop_congr D D₂ hq hq hkq hkq₂ (hch q hq).1 rfl (fun t =>
      hagree _ _ (by linarith) fun u hu x hx => hdesc _ (hleftPt εq t hεq.le) u
        ⟨hu.1, by linarith [hu.2]⟩ x hx)).2
  have hlevγ : ∀ t, f (γ t) = c := by
    intro t
    have hy := hleftPt εq t hεq.le
    have hfx : f ((D.chart q hq).χ ((D.chart q hq).sphereParam εq
        (fun i => circ2 t (Fin.cast hkq i)))) = f q - εq :=
      (D.chart q hq).f_chart_of_mem_leftModelSphere hRq hy
    have key := D.f_flow_eq_sub_of_avoid_uIcc hfs (T := f q - εq - c)
      (by rw [hfx]; constructor <;> linarith [hfp.1, hfq.2])
      (by rw [hfx]; constructor <;> linarith [hfp.1, hfq.2])
      (fun u hu x hx hmem => by
        rw [uIcc_of_le (by linarith)] at hu
        exact hdesc _ hy u ⟨hu.1, by linarith [hu.2]⟩ x hx
          (D.smallBall_subset_closedSmallBall x hx hmem))
      (f q - εq - c) right_mem_uIcc
    change f (D.flow (f q - εq - c) (leftPt D q hq hkq εq t)) = c
    unfold leftPt
    rw [key, hfx]
    ring
  have hfreeD : ∀ t, descendsFreely D (c - (f p + εp)) (γ t) := by
    intro t u hu x hx
    change D.flow u (D.flow (f q - εq - c) (leftPt D q hq hkq εq t)) ∉ D.closedSmallBall x hx
    rw [D.flow_flow]
    exact hdesc _ (hleftPt εq t hεq.le) _ ⟨by linarith [hu.1], by linarith [hu.2]⟩ x hx
  have hmeet2 : meetsRightOnce D₂ p hp εp c γ := by
    refine meetsRightOnce_transfer hfs D D₂ hp hp (hch p hp).1 (hch p hp).2.1
      (le_of_eq (hch p hp).2.2.1) rfl hεp ?_ hc1 hcb hlevγ hfreeD
      (fun t => hagree _ _ (by linarith) (hfreeD t)) hmeet
    rw [(hch p hp).2.2.1]
    have h1 := (D.hrm p hp).2
    have h2 := D.rm_pos p hp
    have h3 := pow_le_pow_left₀ h2.le h1 2
    linarith
  have hfree₂ : ∀ t, descendsFreely D₂ (c - (f p + εp)) (γ t) := by
    intro t u hu x hx hmem
    have heq := hagree (γ t) u hu.1 fun u' hu' => hfreeD t u' ⟨hu'.1, hu'.2.trans hu.2⟩
    rw [heq] at hmem
    exact hfreeD t u hu x hx (hcSB x hx hmem)
  have hdesc2 : ∀ y ∈ (D₂.chart q hq).leftModelSphere εq,
      ∀ t ∈ Icc 0 (f q - εq - (f p + εp)), ∀ x (hx : x ∈ C),
        D₂.flow t ((D₂.chart q hq).χ y) ∉ D₂.closedSmallBall x hx := by
    intro y hy t ht x hx hmem
    rw [hLMS2] at hy
    rw [(hch q hq).1, hagree _ _ ht.1 fun u hu x' hx' =>
      hdesc y hy u ⟨hu.1, hu.2.trans ht.2⟩ x' hx'] at hmem
    exact hdesc y hy t ht x hx (hcSB x hx hmem)
  have hmodel2 : ∀ y, morseNorm n y ^ 2 ≤ 2 * εq → posPart (D₂.chart q hq).hk y = 0 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (D₂.chart q hq).χ.symm ((D₂.chart q hq).χ y)
        (D₂.V ((D₂.chart q hq).χ y)) =
          ModelField.modelField (D₂.chart q hq).k (D₂.chart q hq).r₀ y := by
    intro y hy _
    refine D₂.model q hq y ?_
    rw [hrm2 q hq]
    have h2 := D.rm_pos q hq
    exact lt_of_pow_lt_pow_left₀ 2 h2.le (by linarith)
  have hR'2q : 2 * εq < (D₂.chart q hq).R' ^ 2 := by
    rw [(hch q hq).2.2.2.1]
    have h1 := D.rm_lt_R' q hq
    have h2 := D.rm_pos q hq
    have h3 := pow_lt_pow_left₀ h1 h2.le two_ne_zero
    linarith
  obtain ⟨hL1, hL2, hL3⟩ := leftLoop_eq_of_le D₂ hq hkq₂ (c := c) hε0 hεq' (hr₀2sq q hq) hR'2q
    hmodel2
  have hballs2 : ∀ x (hx : x ∈ C), x ≠ p → ∀ y ∈ D₂.closedSmallBall x hx,
      f y ∉ Icc (f p + ε) (f p + εp) := fun x hx hxp y hy hmem =>
    hballs x hx hxp y (hcSB x hx hy) ⟨by linarith [hmem.1], hmem.2⟩
  have hγc : Continuous γ :=
    (isLevelLoop_leftLoop hfs D hq hkq hεq hRq (by linarith [hfp.1]) hc2
      (fun y hy u hu x hx => hdesc y hy u ⟨hu.1, by linarith [hu.2]⟩ x hx)).2.1.continuous
  obtain ⟨hfree₂ε, hmeetε⟩ := meetsRightOnce_of_le hfs D₂ hp hε0 hεp' (hr₀2sq p hp)
    (by rw [hrm2 p hp]; exact hrmp) hc1 hcb hballs2 hγc hlevγ hfree₂ hmeet2
  have hdescε : ∀ y ∈ (D₂.chart q hq).leftModelSphere ε, ∀ t ∈ Icc 0 (f q - f p - 2 * ε),
      ∀ x (hx : x ∈ C), D₂.flow t ((D₂.chart q hq).χ y) ∉ D₂.closedSmallBall x hx := by
    intro y hy t ht x hx
    by_cases h1 : t ≤ εq - ε
    · exact hL3 y hy t ⟨ht.1, h1⟩ x hx
    rw [not_le] at h1
    obtain ⟨y', hy', hy'eq⟩ := hL2 y hy
    have ht' : D₂.flow t ((D₂.chart q hq).χ y) =
        D₂.flow (t - (εq - ε)) ((D₂.chart q hq).χ y') := by
      rw [hy'eq, D₂.flow_flow]
      congr 1
      ring
    rw [ht']
    by_cases h2 : t - (εq - ε) ≤ f q - εq - c
    · exact hdesc2 y' hy' _ ⟨by linarith, by linarith [ht.2]⟩ x hx
    rw [not_le] at h2
    obtain ⟨θ, hθ⟩ := exists_angle_of_mem_leftModelSphere D₂ hq hkq₂ hεq hy'
    have h3 : D₂.flow (t - (εq - ε)) ((D₂.chart q hq).χ y') =
        D₂.flow (t - (εq - ε) - (f q - εq - c)) (leftLoop D₂ q hq hkq₂ εq c θ) := by
      rw [hθ]
      unfold leftLoop leftPt
      rw [D₂.flow_flow]
      congr 1
      ring
    rw [h3, hγ2]
    exact hfree₂ε θ _ ⟨by linarith, by linarith [ht.2]⟩ x hx
  obtain ⟨D₃, hch3, hrm3, hV3⟩ := D₂.exists_restrict (le_refl a) (le_refl b) C
    (fun r hr => hr) (fun r hr hr' => absurd hr hr') (fun _ _ => s)
    (fun r hr => (D₂.chart r hr).R') (fun _ _ => s)
    (fun r hr => ⟨by linarith [hr₀2 r hr], hsR2 r hr⟩)
    (fun r hr => ⟨(hsR2 r hr).trans_lt (D₂.chart r hr).hRR', le_refl _⟩)
    (fun r hr => ⟨by linarith [hr₀2 r hr], hsrm2 r hr, le_refl _⟩)
    (fun r hr => D₂.inStrip r hr) (fun x _ hx => hx)
  have hflow3 : ∀ t z, D₃.flow t z = D₂.flow t z :=
    GradientLikeStrip.flow_eq_of_V_eq D₂ D₃ hV3
  have hcSB3 : ∀ x (hx : x ∈ C), D₃.closedSmallBall x hx = D₂.closedSmallBall x hx := by
    intro x hx
    unfold GradientLikeStrip.closedSmallBall
    rw [(hch3 x hx).1, (hch3 x hx).2.2.1]
  have hkq₃ : (D₃.chart q hq).k = 2 := (hch3 q hq).2.1.trans hkq₂
  have hkp₃ : (D₃.chart p hp).k = 1 := (hch3 p hp).2.1.trans ((hch p hp).2.1.trans hkp)
  refine ⟨hf, C, hC, hp, hq, D₃, hkq₃, hkp₃, ε, δ, hε0, hεδ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c,
    by linarith, by linarith, ?_⟩
  · intro x hx
    rw [(hch3 x hx).2.2.1, hrm3 x hx]
    refine ⟨hr₀2sq x hx, ?_⟩
    change 24 * ε < s ^ 2
    rw [hεdef]
    linarith
  · intro x hx
    rw [(hch3 x hx).2.2.2.1]
    change s ^ 2 < 2 * δ
    linarith
  · linarith
  · linarith
  · linarith
  · intro x hx hxp hxq
    have := hsep x hx hxp hxq
    constructor <;> linarith [this.1, this.2]
  · intro y hy t ht x hx
    rw [hcSB3 x hx, hflow3, (hch3 q hq).1]
    rw [hLMS _ _ (hch3 q hq).2.1] at hy
    exact hdescε y hy t ht x hx
  · have hL3eq : leftLoop D₃ q hq hkq₃ ε c = leftLoop D₂ q hq hkq₂ ε c :=
      (leftLoop_congr D₂ D₃ hq hq hkq₂ hkq₃ (hch3 q hq).1 rfl (fun t => hflow3 _ _)).2
    rw [hL3eq, hL1, hγ2]
    refine meetsRightOnce_transfer hfs D₂ D₃ hp hp (hch3 p hp).1 (hch3 p hp).2.1 ?_ rfl hε0 ?_
      (by linarith) hcb hlevγ hfree₂ε (fun t => hflow3 _ _) hmeetε
    · rw [(hch3 p hp).2.2.2.1]; exact hsR2 p hp
    · rw [(hch3 p hp).2.2.2.1]
      show 2 * ε < s ^ 2
      rw [hεdef]
      linarith

theorem exists_fine_partner {p q : M}
    (h : isSmallPartnerConfig I f a b p q) : isFinePartnerConfig I f a b p q := by
  obtain ⟨hf, crit, hcrit, hp, hq, D, hkq, hkp, ε, δ, hε, hεδ, hD, hR, hgap1, hgap2, hgap3,
    hsep, hdesc, c, hc1, hc2, hmeet⟩ := h
  have hT : f q - ε - (f p + ε) = f q - f p - 2 * ε := by ring
  obtain ⟨D', r', hr'0, -, hr'ε, hch, hrm, hV, hnc⟩ :=
    exists_nocommon_radius (c := f p + ε) hf hcrit D hq hε
      ⟨(hD q hq).1, by linarith [(hD q hq).2]⟩ (by linarith) (by linarith)
      (by rw [hT]; exact hdesc) (η := 1) one_pos
  have hkq' : (D'.chart q hq).k = 2 := (hch q hq).2.1.trans hkq
  have hball : ∀ x (hx : x ∈ crit), D'.closedSmallBall x hx ⊆ D.closedSmallBall x hx := by
    intro x hx
    change (D'.chart x hx).χ '' {y | morseNorm n y ≤ (D'.chart x hx).r₀} ⊆
      (D.chart x hx).χ '' {y | morseNorm n y ≤ (D.chart x hx).r₀}
    rw [(hch x hx).1]
    exact image_mono fun y hy => le_trans hy (hch x hx).2.2.2.2.1
  have hlmsgen : ∀ (k₁ k₂ : ℕ) (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ → ∀ y : Fin n → ℝ,
      (posPart h₁ y = 0 ∧ ‖negPart h₁ y‖ ^ 2 = 2 * ε) ↔
        (posPart h₂ y = 0 ∧ ‖negPart h₂ y‖ ^ 2 = 2 * ε) := by
    rintro k₁ k₂ h₁ h₂ rfl y
    exact Iff.rfl
  have hlms : (D'.chart q hq).leftModelSphere ε = (D.chart q hq).leftModelSphere ε := by
    ext y
    exact hlmsgen _ _ (D'.chart q hq).hk (D.chart q hq).hk (hch q hq).2.1 y
  have hflowEq : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 (f q - f p - 2 * ε),
      D'.flow s ((D.chart q hq).χ y) = D.flow s ((D.chart q hq).χ y) := by
    intro y hy s hs
    refine flow_eq_of_agree_along D D' ?_
    intro u hu
    rw [uIcc_of_le hs.1] at hu
    exact hV _ fun x hx => hdesc y hy u ⟨hu.1, hu.2.trans hs.2⟩ x hx
  have hleftPt : ∀ t, ∃ y ∈ (D.chart q hq).leftModelSphere ε,
      leftPt D q hq hkq ε t = (D.chart q hq).χ y := by
    intro t
    have hw : (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
      intro h0
      have h1 : Real.cos (2 * Real.pi * t) = 0 := by
        simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 0)
      have h2 : Real.sin (2 * Real.pi * t) = 0 := by
        simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 1)
      have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
      rw [h1, h2] at this
      norm_num at this
    exact ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw, rfl⟩
  have hcT : f q - ε - c ∈ Icc 0 (f q - f p - 2 * ε) := ⟨by linarith, by linarith⟩
  have hloop : leftLoop D' q hq hkq' ε c = leftLoop D q hq hkq ε c := by
    refine (leftLoop_congr D D' hq hq hkq hkq' (hch q hq).1 rfl ?_).2
    intro t
    obtain ⟨y, hy, hyt⟩ := hleftPt t
    rw [hyt]
    exact hflowEq y hy _ hcT
  have hfree : ∀ t, descendsFreely D (c - (f p + ε)) (leftLoop D q hq hkq ε c t) := by
    intro t s hs x hx
    obtain ⟨y, hy, hyt⟩ := hleftPt t
    change D.flow s (D.flow (f q - ε - c) (leftPt D q hq hkq ε t)) ∉ D.closedSmallBall x hx
    rw [hyt, D.flow_flow]
    exact hdesc y hy _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ x hx
  have hRp : 2 * ε < (D'.chart p hp).R ^ 2 := by
    rw [(hch p hp).2.2.1]
    have h1 := (D.hrm p hp).2
    have h2 := D.rm_pos p hp
    have h3 := (hD p hp).2
    nlinarith
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    have h3 := (hD q hq).2
    nlinarith
  have hlev : ∀ t, f (leftLoop D q hq hkq ε c t) = c :=
    (isLevelLoop_leftLoop hf.smooth D hq hkq hε hRq (by linarith) hc2
      (fun y hy s hs x hx => hdesc y hy s ⟨hs.1, by linarith [hs.2]⟩ x hx)).2.2.2.2
  have hflow' : ∀ t, D'.flow (c - (f p + ε)) (leftLoop D q hq hkq ε c t) =
      D.flow (c - (f p + ε)) (leftLoop D q hq hkq ε c t) := by
    intro t
    refine flow_eq_of_agree_along D D' ?_
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    exact hV _ fun x hx => hfree t u hu x hx
  refine ⟨hf, crit, hcrit, hp, hq, D', hkq', (hch p hp).2.1.trans hkp, ε, δ, r', hε, hεδ, hr'0,
    hr'ε, ?_, ?_, hgap1, hgap2, hgap3, hsep, ?_, ?_, c, hc1, hc2, ?_⟩
  · intro x hx
    have h0 := (D'.chart x hx).hr₀
    have h1 := (hch x hx).2.2.2.2.1
    refine ⟨?_, ?_, (hch x hx).2.2.2.2.2⟩
    · have := (hD x hx).1
      nlinarith
    · rw [hrm x hx]; exact (hD x hx).2
  · intro x hx
    rw [(hch x hx).2.2.1]
    exact hR x hx
  · intro x hx h1 h2
    have hxp : x ≠ p := by rintro rfl; exact lt_irrefl _ h1
    have hxq : x ≠ q := by rintro rfl; exact lt_irrefl _ h2
    obtain ⟨s1, s2⟩ := hsep x hx hxp hxq
    rw [abs_of_pos (by linarith)] at s1
    rw [abs_of_neg (by linarith)] at s2
    exact hnc x hx (by linarith) (by linarith)
  · intro y hy s hs x hx
    rw [hlms] at hy
    rw [(hch q hq).1, hflowEq y hy s hs]
    exact fun hmem => hdesc y hy s hs x hx (hball x hx hmem)
  · rw [hloop]
    exact meetsRightOnce_transfer hf.smooth D D' hp hp (hch p hp).1 (hch p hp).2.1
      (hch p hp).2.2.1.le rfl hε hRp hc1 (by linarith) hlev hfree hflow' hmeet

theorem exists_raise_between [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit)
    {ε δ r' : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hr' : 0 < r') (hr'ε : r' ^ 2 < ε)
    (hD : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm x hx ^ 2 ∧
      (D.chart x hx).r₀ < r')
    (hR : ∀ x hx, (D.chart x hx).R ^ 2 < 2 * δ)
    (hgap : a < f p - 8 * δ ∧ f p + 8 * δ < f q ∧ f q + 8 * δ < b)
    (hsep : ∀ x ∈ crit, x ≠ p → x ≠ q → 8 * δ < |f x - f p| ∧ 8 * δ < |f x - f q|)
    (hnocommon : ∀ x (hx : x ∈ crit), f p < f x → f x < f q →
      ∀ z ∈ (D.chart q hq).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t z ∉ (D.chart x hx).χ '' {y | morseNorm n y < r'}) :
    ∃ g : M → ℝ, ∃ D' : GradientLikeStrip I g a b crit, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      (∀ x ∈ crit, f p < f x → f x < f q → f q + 2 * δ < g x ∧ g x < f q + 3 * δ) ∧
      (∀ x ∈ crit, ¬ (f p < f x ∧ f x < f q) → g x = f x) ∧
      (∀ r hr, (D'.chart r hr).χ = (D.chart r hr).χ ∧ (D'.chart r hr).k = (D.chart r hr).k ∧
        (D'.chart r hr).r₀ ≤ (D.chart r hr).r₀ ∧ (D'.chart r hr).R ≤ (D.chart r hr).R ∧
        (D'.chart r hr).R' = (D.chart r hr).R' ∧
        (D'.chart r hr).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm r hr ^ 2) ∧
      (∀ r hr, f r ∉ Ioo (f p + 4 * δ) (f q + 4 * δ) →
        (D'.chart r hr).R = (D.chart r hr).R ∧ D'.rm r hr = D.rm r hr) ∧
      (∀ r hr, (¬ (f p < f r ∧ f r < f q)) → ∀ y, morseNorm n y < D.rm r hr →
        (negPart (D.chart r hr).hk y = 0 ∨ posPart (D.chart r hr).hk y = 0) →
        mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart r hr).χ.symm ((D.chart r hr).χ y)
          (D'.V ((D.chart r hr).χ y)) =
            ModelField.modelField (D.chart r hr).k (D'.chart r hr).r₀ y) ∧
      ∀ x, x ∉ D.closedSmallBalls → f x ∈ Icc a b →
        (f x ∉ Ioo (f p + 5 * δ) (f q + 7 * δ / 2) ∨
          ∃ t, (∀ s ∈ uIcc 0 t, f (D.flow s x) ∈ Ioo (f p + 4 * δ) (f q + 4 * δ)) ∧
            D.flow t x ∈ D.smallBall q hq) →
        g x = f x ∧ D'.V x = D.V x := by
  classical
  have _ : 0 < r' := hr'
  have hδ : 0 < δ := hε.trans hεδ
  obtain ⟨hga, hgpq, hgb⟩ := hgap
  have hRd : ∀ x hx, (D.chart x hx).R ^ 2 / 2 < δ := fun x hx => by
    have := hR x hx; linarith
  have hRnn : ∀ x hx, 0 ≤ (D.chart x hx).R ^ 2 / 2 := fun x hx => by positivity
  have hP₁val : ∀ x ∈ crit, f p < f x → f x < f q → f p + 8 * δ < f x := by
    intro x hx h1 h2
    have hxp : x ≠ p := by rintro rfl; exact lt_irrefl _ h1
    have hxq : x ≠ q := by rintro rfl; exact lt_irrefl _ h2
    have h8 := (hsep x hx hxp hxq).1
    rw [abs_of_pos (sub_pos.2 h1)] at h8
    linarith
  set T : Finset ℝ := (crit.filter (fun x => f p < f x ∧ f x < f q)).image f with hT
  set m := T.card with hm
  set t : Fin m ↪o ℝ := T.orderEmbOfFin rfl with ht
  set sv : Fin m → ℝ := fun i => f q + 2 * δ + δ * (((i : ℕ) : ℝ) + 1) / ((m : ℝ) + 1)
    with hsvdef
  have hsv : ∀ i : Fin m, f q + 2 * δ < sv i ∧ sv i < f q + 3 * δ := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    constructor
    · have : 0 < δ * (((i : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) := by positivity
      simp only [sv]; linarith
    · have : δ * (((i : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) < δ := by
        rw [div_lt_iff₀ hm0]; nlinarith
      simp only [sv]; linarith
  have hsvmono : StrictMono sv := by
    intro i j hij
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have : δ * (((i : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) <
        δ * (((j : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) := by
      apply div_lt_div_of_pos_right _ hm0
      nlinarith
    simp only [sv]; linarith
  have hTmem : ∀ v ∈ T, ∃ x ∈ crit, f p < f x ∧ f x < f q ∧ f x = v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hxc, hx1, hx2⟩ := Finset.mem_filter.1 hx
    exact ⟨x, hxc, hx1, hx2, rfl⟩
  have hts : ∀ i, t i ∈ Ioo (f p + 5 * δ) (f q + 7 * δ / 2) ∧
      sv i ∈ Ioo (f p + 5 * δ) (f q + 7 * δ / 2) := by
    intro i
    obtain ⟨x, hxc, hx1, hx2, hxv⟩ := hTmem (t i) (T.orderEmbOfFin_mem rfl i)
    have h8 := hP₁val x hxc hx1 hx2
    obtain ⟨hs1, hs2⟩ := hsv i
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  obtain ⟨σ, hσ, ρ, hρ, hρ', hρid, hρtr⟩ := exists_multiShift t.strictMono hsvmono hts
  have hreg : ∀ x, f x = f p + 4 * δ ∨ f x = f q + 4 * δ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hc
    have hxab : f x ∈ Ioo a b := by
      rcases hx with hx | hx <;> rw [hx] <;> constructor <;> linarith
    have hxc : x ∈ crit := (hcrit x).2 ⟨hxab, hc⟩
    rcases hx with hx | hx
    · have hxp : x ≠ p := by rintro rfl; linarith
      have hxq : x ≠ q := by rintro rfl; linarith
      have h8 := (hsep x hxc hxp hxq).1
      rw [hx, show f p + 4 * δ - f p = 4 * δ by ring, abs_of_pos (by linarith)] at h8
      linarith
    · have hxp : x ≠ p := by rintro rfl; linarith
      have hxq : x ≠ q := by rintro rfl; linarith
      have h8 := (hsep x hxc hxp hxq).2
      rw [hx, show f q + 4 * δ - f q = 4 * δ by ring, abs_of_pos (by linarith)] at h8
      linarith
  have hsep' : ∀ r hr, f r ∉ Ioo (f p + 4 * δ) (f q + 4 * δ) →
      f r + (D.chart r hr).R ^ 2 / 2 + ε < f p + 4 * δ ∨
        f q + 4 * δ + ε < f r - (D.chart r hr).R ^ 2 / 2 := by
    intro r hr hrb
    have h1 := hRd r hr
    by_cases hrp : r = p
    · subst hrp; left; linarith
    by_cases hrq : r = q
    · subst hrq; exact absurd ⟨by linarith, by linarith⟩ hrb
    obtain ⟨h8p, h8q⟩ := hsep r hr hrp hrq
    rcases le_or_gt (f r) (f p + 4 * δ) with hle | hlt
    · left
      rcases le_or_gt (f r) (f p) with hle' | hlt'
      · rw [abs_of_nonpos (by linarith)] at h8p; linarith
      · rw [abs_of_pos (by linarith)] at h8p; linarith
    · right
      have hge : f q + 4 * δ ≤ f r := by
        by_contra hcon; exact hrb ⟨hlt, lt_of_not_ge hcon⟩
      rw [abs_of_pos (by linarith)] at h8q; linarith
  have hin : ∀ r hr, f r ∈ Ioo (f p + 4 * δ) (f q + 4 * δ) →
      f p + 4 * δ + ε < f r - (D.chart r hr).R ^ 2 / 2 ∧
        f r + (D.chart r hr).R ^ 2 / 2 + ε < f q + 4 * δ := by
    intro r hr hrb
    obtain ⟨hrb1, hrb2⟩ := hrb
    have h1 := hRd r hr
    by_cases hrq : r = q
    · subst hrq; constructor <;> linarith
    have hrp : r ≠ p := by rintro rfl; linarith
    obtain ⟨h8p, h8q⟩ := hsep r hr hrp hrq
    rw [abs_of_pos (by linarith)] at h8p
    rcases le_or_gt (f r) (f q) with hle | hlt
    · rw [abs_of_nonpos (by linarith)] at h8q; constructor <;> linarith
    · rw [abs_of_pos (by linarith)] at h8q; linarith
  have hnoc : ∀ r hr s hs, r ∉ {x | f p < f x ∧ f x < f q} → s ∈ {x | f p < f x ∧ f x < f q} →
      f r ∈ Ioo (f p + 4 * δ) (f q + 4 * δ) → f s ∈ Ioo (f p + 4 * δ) (f q + 4 * δ) →
      ∀ x ∈ (D.chart r hr).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart s hs).χ '' {y | morseNorm n y < r'} := by
    intro r hr s hs hrP hsP hrb _
    by_cases hrq : r = q
    · subst hrq
      exact hnocommon s hs hsP.1 hsP.2
    exfalso
    obtain ⟨hrb1, hrb2⟩ := hrb
    have hrp : r ≠ p := by rintro rfl; linarith
    obtain ⟨-, h8q⟩ := hsep r hr hrp hrq
    have hge : f q ≤ f r := by
      by_contra hcon; exact hrP ⟨by linarith, lt_of_not_ge hcon⟩
    rw [abs_of_nonneg (by linarith)] at h8q; linarith
  have hρtr' : ∀ s ∈ crit, s ∈ {x | f p < f x ∧ f x < f q} →
      f s ∈ Ioo (f p + 4 * δ) (f q + 4 * δ) →
      ∀ τ ∈ Icc (f s - σ) (f s + σ), ρ τ = τ + (ρ (f s) - f s) := by
    intro s hs hsP _ τ hτ
    have hsT : f s ∈ T := Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨hs, hsP⟩, rfl⟩
    have hsr : f s ∈ Set.range t := by
      rw [ht, Finset.range_orderEmbOfFin]; exact hsT
    obtain ⟨i, hi⟩ := hsr
    have h1 := hρtr i τ (by rw [hi]; exact hτ)
    have h2 := hρtr i (f s) (by rw [hi]; constructor <;> linarith)
    rw [h1, h2, hi]; ring
  have hmoved : ∀ s ∈ crit, s ∈ {x | f p < f x ∧ f x < f q} →
      f q + 2 * δ < ρ (f s) ∧ ρ (f s) < f q + 3 * δ := by
    intro s hs hsP
    have hsT : f s ∈ T := Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨hs, hsP⟩, rfl⟩
    have hsr : f s ∈ Set.range t := by
      rw [ht, Finset.range_orderEmbOfFin]; exact hsT
    obtain ⟨i, hi⟩ := hsr
    have h2 := hρtr i (f s) (by rw [hi]; constructor <;> linarith)
    rw [hi] at h2
    rw [h2]
    have := hsv i
    constructor <;> linarith
  obtain ⟨g, D', ε', hε', hε'ε, hmod, hg, hcritg, hidx, hmv, hfix, hch, hout, hmodel, hlast⟩ :=
    exists_move hf hcrit D hε hr'ε hD (a₂ := f p + 4 * δ) (b₂ := f q + 4 * δ)
      (a₃ := f p + 5 * δ) (b₃ := f q + 7 * δ / 2) (by linarith) (by linarith)
      ⟨by linarith, by linarith, by linarith⟩ hreg hsep' hin {x | f p < f x ∧ f x < f q} hnoc
      ρ hρ hρ' hρid hσ hρtr'
  refine ⟨g, D', ε', hε', hε'ε, hmod, hg, hcritg, hidx, ?_, ?_, hch, hout, ?_, ?_⟩
  · intro x hx h1 h2
    have h8 := hP₁val x hx h1 h2
    rw [hmv x hx ⟨h1, h2⟩ ⟨by linarith, by linarith⟩]
    exact hmoved x hx ⟨h1, h2⟩
  · intro x hx hxP
    exact hfix x hx (Or.inl hxP)
  · intro r hr hrP
    exact hmodel r hr (Or.inl hrP)
  · intro x hx hxab hcase
    refine hlast x hx hxab ?_
    rcases hcase with hc | ⟨τ, hτ, hτq⟩
    · exact Or.inl hc
    · exact Or.inr ⟨τ, hτ, q, hq, fun h => lt_irrefl _ h.2, ⟨by linarith, by linarith⟩, hτq⟩

theorem exists_isolate_of_fine [SigmaCompactSpace M] [DecidableEq M] {p q : M}
    (h : isFinePartnerConfig I f a b p q) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      ∃ a' b' : ℝ, a < a' ∧ b' < b ∧ (∀ x, g x = a' ∨ g x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) ∧
        isCancellingPair I g a' b' p q := by
  obtain ⟨hf, crit, hcrit, hp, hq, D, hkq, hkp, ε, δ, r', hε, hεδ, hr', hr'ε, hD, hR, hgap1,
    hgap2, hgap3, hsep, hnocommon, hdesc, c, hc1, hc2, hmeet⟩ := h
  have hδ : 0 < δ := hε.trans hεδ
  obtain ⟨g, D', ε', hε', hε'ε, hmod, hg, hcritg, hidxg, hraise, hfix, hchart, hfar, hmodel',
    hsame⟩ := exists_raise_between hf hcrit D hp hq hε hεδ hr' hr'ε hD hR ⟨hgap1, hgap2, hgap3⟩
      hsep hnocommon
  have hfs := hf.smooth
  have hgs := hg.smooth
  have hgp : g p = f p := hfix p hp (fun h => lt_irrefl _ h.1)
  have hgq : g q = f q := hfix q hq (fun h => lt_irrefl _ h.2)
  have hpre : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x => Set.ext_iff.1 hmod.preimage_Ioo x
  have hcritg' : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro x
    rw [hcrit x, hpre x, hcritg x]
  have hval : ∀ x ∈ crit, x ≠ p → x ≠ q → g x < f p - 8 * δ ∨ f q + 2 * δ < g x := by
    intro x hx hxp hxq
    by_cases hb : f p < f x ∧ f x < f q
    · exact Or.inr (hraise x hx hb.1 hb.2).1
    · rw [hfix x hx hb]
      obtain ⟨h1, h2⟩ := hsep x hx hxp hxq
      rcases le_or_gt (f x) (f p) with hle | hlt
      · left
        rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h1
        linarith
      · right
        have hge : f q ≤ f x := by
          by_contra hcon
          exact hb ⟨hlt, lt_of_not_ge hcon⟩
        rw [abs_of_nonneg (by linarith)] at h2
        linarith
  have hballg : ∀ x (hx : x ∈ crit), ∀ y ∈ D'.closedSmallBall x hx, |g y - g x| < δ := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : morseNorm n z ≤ (D'.chart x hx).r₀ := hz
    have hr₀R := D'.r₀_lt_R x hx
    have hRle := (hchart x hx).2.2.2.1
    have hRδ := hR x hx
    have hr₀pos := (D'.chart x hx).hr₀
    rw [(D'.chart x hx).hnorm z (hz'.trans hr₀R.le),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      add_sub_cancel_left]
    have hsq :=
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (D'.chart x hx).hk z
    have hmn := ModelField.morseNorm_nonneg (n := n) z
    have h1 : morseNorm n z ^ 2 < 2 * δ := by
      have : morseNorm n z < (D.chart x hx).R := (hz'.trans_lt hr₀R).trans_le hRle
      exact (pow_lt_pow_left₀ this hmn two_ne_zero).trans hRδ
    rw [abs_lt]
    constructor <;> linarith [sq_nonneg ‖posPart (D'.chart x hx).hk z‖,
      sq_nonneg ‖negPart (D'.chart x hx).hk z‖]
  have hfpq : f p + 8 * δ < f q := hgap2
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = f q - f p - 2 * ε := ⟨_, rfl⟩
  rw [← hT] at hdesc
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have hrmq := hD q hq
  have hrmpos := D.rm_pos q hq
  have hrmR := (D.hrm q hq).2
  have hrmRsq : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 := pow_le_pow_left₀ hrmpos.le hrmR 2
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by linarith [hrmq.2.1]
  have hA : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 T,
      f (D.flow s ((D.chart q hq).χ y)) = f q - ε - s := by
    intro y hy s hs
    have hfy := (D.chart q hq).f_chart_of_mem_leftModelSphere hRq hy
    have := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs (x := (D.chart q hq).χ y)
      (T := T) (by rw [hfy]; constructor <;> linarith)
      (by rw [hfy, hT]; constructor <;> linarith) (by
        intro s' hs' x hx hmem
        rw [uIcc_of_le hT0] at hs'
        exact hdesc y hy s' hs' x hx (D.smallBall_subset_closedSmallBall x hx hmem))
      s (by rw [uIcc_of_le hT0]; exact hs)
    rw [this, hfy]
  have hyrm : ∀ y ∈ (D.chart q hq).leftModelSphere ε, morseNorm n y < D.rm q hq := by
    intro y hy
    have h1 := (D.chart q hq).morseNorm_sq_of_mem_leftModelSphere hy
    exact lt_of_pow_lt_pow_left₀ 2 hrmpos.le (by rw [h1]; linarith [hrmq.2.1])
  have hback : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∃ s₁ ∈ Icc (-(ε + δ)) 0,
      D.flow s₁ ((D.chart q hq).χ y) ∈ D.smallBall q hq := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hfy := (D.chart q hq).f_chart_of_mem_leftModelSphere hRq hy
    have hav : ∀ s ∈ uIcc 0 (-(ε + δ)), ∀ x (hx : x ∈ crit),
        D.flow s ((D.chart q hq).χ y) ∉ D.smallBall x hx := by
      intro s hs x hx hmem
      rw [uIcc_of_ge (by linarith)] at hs
      by_cases hxq : x = q
      · subst hxq
        exact hcon s hs hmem
      · obtain ⟨z, hz, hzx⟩ := GradientLikeStrip.flow_mem_of_posPart_eq_zero (D := D) hq
          (hyrm y hy) hy.1 hs.2
        have hin : D.flow s ((D.chart q hq).χ y) ∈
            (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' := by
          rw [← hzx]
          exact ⟨z, mem_ball_of_morseNorm_lt ((hz.1.trans_lt (hyrm y hy)).trans
            (D.rm_lt_R' q hq)), rfl⟩
        exact Set.disjoint_left.1 (D.disjoint x hx q hq hxq)
          (D.smallBall_subset_image_ball x hx hmem) hin
    have h1 := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs
      (x := (D.chart q hq).χ y) (T := -(ε + δ)) (by rw [hfy]; constructor <;> linarith)
      (by rw [hfy]; constructor <;> linarith) hav (-(ε + δ)) right_mem_uIcc
    have h2 := GradientLikeStrip.f_flow_le_f_p_of_posPart_eq_zero (D := D) hq (hyrm y hy) hy.1
      (t := -(ε + δ)) (by linarith)
    rw [h1, hfy] at h2
    linarith
  have hB : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 T,
      g (D.flow s ((D.chart q hq).χ y)) = f (D.flow s ((D.chart q hq).χ y)) ∧
        D'.V (D.flow s ((D.chart q hq).χ y)) = D.V (D.flow s ((D.chart q hq).χ y)) := by
    intro y hy s hs
    have hfz := hA y hy s hs
    have hfy := (D.chart q hq).f_chart_of_mem_leftModelSphere hRq hy
    refine hsame _ ((D.notMem_closedSmallBalls_iff).2 fun x hx =>
      hdesc y hy s hs x hx) (by rw [hfz]; rw [hT] at hs; constructor <;> linarith [hs.1, hs.2]) ?_
    by_cases h5 : f (D.flow s ((D.chart q hq).χ y)) ≤ f p + 5 * δ
    · left
      intro hmem
      linarith [hmem.1]
    · right
      push Not at h5
      obtain ⟨s₁, hs₁, hs₁b⟩ := hback y hy
      refine ⟨-s + s₁, ?_, ?_⟩
      · intro s' hs'
        rw [D.flow_flow]
        rw [uIcc_of_ge (by linarith [hs₁.2, hs.1])] at hs'
        by_cases hss : 0 ≤ s + s'
        · rw [hA y hy (s + s') ⟨hss, by linarith [hs'.2, hs.2]⟩]
          rw [hfz] at h5
          constructor <;> linarith [hs'.2]
        · push Not at hss
          have h1 := GradientLikeStrip.f_flow_le_f_p_of_posPart_eq_zero (D := D) hq (hyrm y hy)
            hy.1 hss.le
          have h2 := GradientLikeStrip.le_f_flow_of_nonpos (D := D) hfs ((D.chart q hq).χ y)
            hss.le
          rw [hfy] at h2
          constructor <;> linarith
      · rw [D.flow_flow, show s + (-s + s₁) = s₁ by ring]
        exact hs₁b
  have hC : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 T,
      D'.flow s ((D.chart q hq).χ y) = D.flow s ((D.chart q hq).χ y) := by
    intro y hy s hs
    refine flow_eq_of_agree_along D D' fun s' hs' => (hB y hy s' ?_).2
    rw [uIcc_of_le hs.1] at hs'
    exact ⟨hs'.1, hs'.2.trans hs.2⟩
  have hw : ∀ t : ℝ, (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
    intro t h0
    have h1 : Real.cos (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 0)
    have h2 : Real.sin (2 * Real.pi * t) = 0 := by
      simpa [circ2] using congrFun h0 (Fin.cast hkq.symm 1)
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h1, h2] at this
    norm_num at this
  have hleftPt : ∀ t, ∃ y ∈ (D.chart q hq).leftModelSphere ε,
      leftPt D q hq hkq ε t = (D.chart q hq).χ y := fun t =>
    ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hε.le (hw t), rfl⟩
  have hcT : f q - ε - c ∈ Icc 0 T := ⟨by linarith, by rw [hT]; linarith⟩
  have hkq' : (D'.chart q hq).k = 2 := (hchart q hq).2.1.trans hkq
  have hχq : (D'.chart q hq).χ = (D.chart q hq).χ := (hchart q hq).1
  have hloop := (leftLoop_congr D D' hq hq hkq hkq' hχq hgq (ε := ε) (c := c) (fun t => by
    obtain ⟨y, hy, hyt⟩ := hleftPt t
    rw [hyt]
    exact hC y hy _ hcT)).2
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = leftLoop D q hq hkq ε c := ⟨_, rfl⟩
  rw [← hγ] at hloop hmeet
  have hγt : ∀ t, ∃ y ∈ (D.chart q hq).leftModelSphere ε,
      γ t = D.flow (f q - ε - c) ((D.chart q hq).χ y) := fun t => by
    obtain ⟨y, hy, hyt⟩ := hleftPt t
    exact ⟨y, hy, by rw [hγ, leftLoop, hyt]⟩
  have hflowγ : ∀ t, ∀ s ∈ Icc 0 (c - (f p + ε)),
      D'.flow s (γ t) = D.flow s (γ t) ∧ ∀ x (hx : x ∈ crit),
        D.flow s (γ t) ∉ D.closedSmallBall x hx := by
    intro t s hs
    obtain ⟨y, hy, hyt⟩ := hγt t
    have hsT : f q - ε - c + s ∈ Icc 0 T := ⟨by linarith [hs.1], by rw [hT]; linarith [hs.2]⟩
    rw [hyt, D.flow_flow]
    refine ⟨?_, hdesc y hy _ hsT⟩
    rw [← hC y hy _ hcT, D'.flow_flow, hC y hy _ hsT]
  have hlevγ : ∀ t, f (γ t) = c ∧ g (γ t) = c := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hγt t
    have h1 := hA y hy _ hcT
    have h2 := (hB y hy _ hcT).1
    rw [hyt]
    constructor <;> linarith
  have hγcont : Continuous γ := by
    rw [hγ]
    exact (isLevelLoop_leftLoop hfs D hq hkq hε hRq (by linarith) hc2
      (fun y hy s hs x hx => hdesc y hy s ⟨hs.1, by rw [hT]; linarith [hs.2]⟩ x hx)).2.1.continuous
  have hfarp := hfar p hp (fun hm => by linarith [hm.1])
  have hrmp := hD p hp
  have hrmpR := (D.hrm p hp).2
  have hrmppos := D.rm_pos p hp
  have hkp' : (D'.chart p hp).k = 1 := (hchart p hp).2.1.trans hkp
  have hmeet' : meetsRightOnce D' p hp ε c γ := by
    refine meetsRightOnce_transfer hfs D D' hp hp (hchart p hp).1 (hchart p hp).2.1
      (hchart p hp).2.2.2.1 hgp hε ?_ hc1 (by linarith) (fun t => (hlevγ t).1)
      (fun t s hs x hx => (hflowγ t s hs).2 x hx)
      (fun t => (hflowγ t _ ⟨by linarith, le_rfl⟩).1) hmeet
    rw [hfarp.1]
    have := pow_le_pow_left₀ hrmppos.le hrmpR 2
    linarith [hrmp.2.1]
  have hcp := (hchart p hp).2.2.2.2.2
  have hcq := (hchart q hq).2.2.2.2.2
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ((D'.chart p hp).r₀ ^ 2) ((D'.chart q hq).r₀ ^ 2) :=
    ⟨_, rfl⟩
  have hmp : (D'.chart p hp).r₀ ^ 2 ≤ m := hm ▸ le_max_left _ _
  have hmq : (D'.chart q hq).r₀ ^ 2 ≤ m := hm ▸ le_max_right _ _
  have hm2 : m < 2 * ε' := hm ▸ max_lt hcp.1 hcq.1
  have hm0 : 0 < m := lt_of_lt_of_le (pow_pos (D'.chart p hp).hr₀ 2) hmp
  obtain ⟨ε'', hε''⟩ : ∃ ε'' : ℝ, ε'' = (m / 2 + ε') / 2 := ⟨_, rfl⟩
  have hε''pos : 0 < ε'' := by rw [hε'']; linarith
  have hε''lt : ε'' < ε' := by rw [hε'']; linarith
  have hmε'' : m < 2 * ε'' := by rw [hε'']; linarith
  have hS3 : (∀ t, descendsFreely D' (c - (g p + ε'')) (γ t)) ∧
      meetsRightOnce D' p hp ε'' c γ :=
    meetsRightOnce_of_le hgs D' hp (ε := ε) (ε' := ε'') (c := c) hε''pos (by linarith)
    (by linarith) (by rw [hfarp.2]; linarith [hrmp.2.1]) (by rw [hgp]; exact hc1) (by linarith)
    (by
      intro x hx hxp y hy hmem
      have hb := hballg x hx y hy
      rw [abs_lt] at hb
      rw [hgp] at hmem
      by_cases hxq : x = q
      · subst hxq
        rw [hgq] at hb
        linarith [hmem.2, hb.1]
      · rcases hval x hx hxp hxq with h | h
        · linarith [hmem.1, hb.2]
        · linarith [hmem.2, hb.1])
    (γ := γ) hγcont (fun t => (hlevγ t).2)
    (by
      intro t s hs x hx hmem
      rw [hgp] at hs
      rw [(hflowγ t s hs).1] at hmem
      obtain ⟨z, hz, hzx⟩ := hmem
      refine (hflowγ t s hs).2 x hx ⟨z, ?_, by rw [← hzx, (hchart x hx).1]⟩
      exact (show morseNorm n z ≤ (D'.chart x hx).r₀ from hz).trans (hchart x hx).2.2.1)
    hmeet'
  have hε''ε : ε'' ≤ ε := by linarith
  have hr₀q'' : (D'.chart q hq).r₀ ^ 2 < 2 * ε'' := by linarith
  have hR'q : 2 * ε < (D'.chart q hq).R' ^ 2 := by
    rw [(hchart q hq).2.2.2.2.1]
    have := pow_lt_pow_left₀ (D.chart q hq).hRR' (D.chart q hq).R_pos.le two_ne_zero
    linarith
  have hS2 := leftLoop_eq_of_le D' hq hkq' (ε := ε) (ε' := ε'') (c := c) hε''pos hε''ε
    hr₀q'' hR'q
    (by
      intro y hy hpos
      have hkk : (D'.chart q hq).k = (D.chart q hq).k := (hchart q hq).2.1
      have hpos' : posPart (D.chart q hq).hk y = 0 := by
        have key : ∀ {k₁ k₂ : ℕ} (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ →
            posPart h₁ y = 0 → posPart h₂ y = 0 := by
          rintro k₁ k₂ h₁ h₂ rfl h
          exact h
        exact key _ _ hkk hpos
      have hyn : morseNorm n y < D.rm q hq :=
        lt_of_pow_lt_pow_left₀ 2 hrmpos.le (by linarith [hrmq.2.1])
      have := hmodel' q hq (fun h => lt_irrefl _ h.2) y hyn (Or.inr hpos')
      rw [hχq, hkk]
      exact this)
  have hmeetF : meetsRightOnce D' p hp ε'' c (leftLoop D' q hq hkq' ε'' c) := by
    rw [hS2.1, hloop]
    exact hS3.2
  have hcritIoo : ∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x → x ∈ crit := fun x hx hc =>
    (hcritg' x).2 ⟨hx, hc⟩
  have hreg : ∀ x, g x = f p - 2 * δ ∨ g x = f q + δ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro x hx hc
    have hxab : g x ∈ Ioo a b := by
      rcases hx with h | h <;> rw [h] <;> constructor <;> linarith
    have hxc := hcritIoo x hxab hc
    by_cases hxp : x = p
    · subst hxp
      rw [hgp] at hx
      rcases hx with h | h <;> linarith
    by_cases hxq : x = q
    · subst hxq
      rw [hgq] at hx
      rcases hx with h | h <;> linarith
    rcases hval x hxc hxp hxq with h | h <;> rcases hx with h' | h' <;> linarith
  have honly : ∀ x, g x ∈ Ioo (f p - 2 * δ) (f q + δ) → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x → x = p ∨ x = q := by
    intro x hx hc
    have hxab : g x ∈ Ioo a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxc := hcritIoo x hxab hc
    by_contra hcon
    push Not at hcon
    rcases hval x hxc hcon.1 hcon.2 with h | h
    · linarith [hx.1]
    · linarith [hx.2]
  have hother : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D'.smallBall x hx,
      g y ∉ Icc (f p - 2 * δ) (f q + δ) := by
    intro x hx hxp hxq y hy hmem
    have hb := hballg x hx y (D'.smallBall_subset_closedSmallBall x hx hy)
    rw [abs_lt] at hb
    rcases hval x hx hxp hxq with h | h
    · linarith [hmem.1, hb.2]
    · linarith [hmem.2, hb.1]
  have hpair := isCancellingPair_of_ambient hg D' hcritg' hp hq hkp' hkq'
    (a' := f p - 2 * δ) (b' := f q + δ) (by linarith) (by linarith) hreg
    (by rw [hgp]; constructor <;> linarith) (by rw [hgq]; constructor <;> linarith)
    (by rw [hgp, hgq]; linarith) honly hother hε''pos
    ⟨by linarith, by linarith [hcp.2], by linarith, by linarith [hcq.2]⟩
    (by rw [hgp]; linarith) (by rw [hgq]; linarith) hmeetF
  exact ⟨g, hmod, hg, hcritg, hidxg, f p - 2 * δ, f q + δ, by linarith, by linarith, hreg, hpair⟩

theorem exists_isolate_partner [SigmaCompactSpace M] [DecidableEq M] {p q : M}
    (h : isPartnerConfig I f a b p q) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      ∃ a' b' : ℝ, a < a' ∧ b' < b ∧ (∀ x, g x = a' ∨ g x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) ∧
        isCancellingPair I g a' b' p q :=
  exists_isolate_of_fine (exists_fine_partner (exists_small_partner h))

theorem exists_partner_of_loop [SigmaCompactSpace M] (h5 : 5 ≤ n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) {p : M} (h : isLoopConfig I f a b p) :
    ∃ f₂ : M → ℝ, ∃ q r : M, ModifiedWithin f a b f₂ ∧ isPartnerConfig I f₂ a b p q ∧
      (∀ x, f₂ x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₂ x →
        (f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∨ x = q ∨ x = r) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₂ x ∧ morseIndex I f₂ x = morseIndex I f x) ∧
      morseIndex I f₂ r = 3 := by
  classical
  obtain ⟨hf, crit, hcrit, hp, D, hkp, ε, δ, c₂, c₃, hε, hεδ, hac₂, hc₂₃, hc₃b, hpc₂, hfine,
    hconst, hgap, hsepp, hdn, hup, γ, hγ, hfree, hmeet⟩ := h
  have hfc : Continuous f := hf.smooth.continuous
  have hδ : 0 < δ := hε.trans hεδ
  have hγlev : ∀ θ, f (γ θ) = c₂ := hγ.2.2.2.2
  have hnear : ∀ x (hx : x ∈ crit), ∀ y ∈ (D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R',
      f y ∈ Ioo (f x - δ) (f x + δ) := fun x hx y hy => hfine x hx hy
  have hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂ := by
    intro x hx y hy hyc
    have h1 := hnear x hx y (D.closedSmallBall_subset_image_ball x hx hy)
    rcases hgap x hx with h2 | h2
    · linarith [h1.2]
    · linarith [h1.1]
  obtain ⟨Hm, hH⟩ :=
    exists_level_nullhomotopy h5 hf D hcrit hW ⟨hac₂, hc₂₃.trans hc₃b⟩ hcU hdn hup hγ
  have hband : ∀ y, f y ∈ Icc c₂ c₃ → ∀ x (hx : x ∈ crit),
      y ∉ closure ((D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R') := by
    intro y hy x hx hcl
    have hsub : closure ((D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R') ⊆
        f ⁻¹' Icc (f x - δ) (f x + δ) :=
      closure_minimal (fun z hz => Ioo_subset_Icc_self (hnear x hx z hz))
        (isClosed_Icc.preimage hfc)
    have h1 := hsub hcl
    rcases hgap x hx with h2 | h2
    · linarith [h1.2, hy.1]
    · linarith [h1.1, hy.2]
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁c⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ (c₃ - c₂) / 128 :=
    ⟨min ε ((c₃ - c₂) / 128), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨f₁, q, r, D₁, K, -, hKsub, hoff, hmod, hf₁, hcrit₁, -, -, hq_lo, hqr, hr_hi,
    -, hidxr, hidx, hch, hnew, hkq, ε', hε', hε'ε₁, hε'gap, hr₀q, hrmq, hloop, hdesc⟩ :=
    exists_birth_along_loop h5 hf D hcrit ⟨hac₂, hc₂₃, hc₃b⟩ hband hγ hH hε₁ (by linarith)
  have hmodab : ModifiedWithin f a b f₁ := hmod.mono hac₂.le hc₃b.le
  have hpre : ∀ x, f₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmodab.preimage_Ioo x
  have hoffK : ∀ x, f x ∉ Ioo c₂ c₃ → f₁ x = f x ∧ D₁.V x = D.V x :=
    fun x hx => hoff x (fun hxK => hx (hKsub hxK))
  have hfp : f₁ p = f p := (hoffK p fun h' => by linarith [h'.1]).1
  have hcritmem : ∀ x ∈ crit, f x ∉ Ioo c₂ c₃ := by
    intro x hx h'
    rcases hgap x hx with h2 | h2
    · linarith [h'.1]
    · linarith [h'.2]
  have hp₁ : p ∈ insert q (insert r crit) := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
  have hq₁ : q ∈ insert q (insert r crit) := Finset.mem_insert_self q _
  obtain ⟨hχp, hkp₁, hRp, -, hr₀p, hrmp⟩ := hch p hp
  have hflowγ : ∀ θ, ∀ u : ℝ, 0 ≤ u → D₁.flow u (γ θ) = D.flow u (γ θ) := by
    intro θ u hu
    refine flow_eq_of_agree_along D D₁ fun s hs => ?_
    rw [uIcc_of_le hu] at hs
    refine (hoffK _ fun h' => ?_).2
    have := GradientLikeStrip.f_flow_le (D := D) hf.smooth (γ θ) hs.1
    rw [hγlev θ] at this
    linarith [h'.1]
  have hball_eq : ∀ x (hx : x ∈ crit),
      D₁.closedSmallBall x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) =
        D.closedSmallBall x hx := by
    intro x hx
    obtain ⟨h1, -, -, -, h5', -⟩ := hch x hx
    change (D₁.chart x _).χ '' {y | morseNorm n y ≤ (D₁.chart x _).r₀} =
      (D.chart x hx).χ '' {y | morseNorm n y ≤ (D.chart x hx).r₀}
    rw [h1, h5']
  have hnewball : ∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
      ∀ y ∈ D₁.closedSmallBall x hx, y ∈ K ∧ c₂ + (c₃ - c₂) / 8 - ε₁ < f₁ y := by
    intro x hx hxqr y hy
    have hy' := D₁.closedSmallBall_subset_image_ball x hx hy
    obtain ⟨hK', hlev'⟩ := hnew x hx hxqr
    refine ⟨hK' hy', ?_⟩
    have h1 := hlev' y hy'
    have h2 : c₂ + (c₃ - c₂) / 8 < f₁ x := by
      rcases hxqr with h3 | h3 <;> rw [h3] <;> linarith
    linarith [(abs_lt.1 h1).1]
  have hmem₁ : ∀ x, x ∈ insert q (insert r crit) ↔ f₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x := by
    intro x
    simp only [Finset.mem_insert]
    constructor
    · rintro (h1 | h1 | hx)
      · rw [h1]
        exact ⟨⟨by linarith, by linarith⟩, (hcrit₁ _).2 (Or.inr (Or.inl rfl))⟩
      · rw [h1]
        exact ⟨⟨by linarith, by linarith⟩, (hcrit₁ _).2 (Or.inr (Or.inr rfl))⟩
      · obtain ⟨h1, h2⟩ := (hcrit x).1 hx
        exact ⟨(hpre x).2 h1, (hcrit₁ x).2 (Or.inl h2)⟩
    · rintro ⟨h1, h2⟩
      rcases (hcrit₁ x).1 h2 with h3 | h3 | h3
      · exact Or.inr (Or.inr ((hcrit x).2 ⟨(hpre x).1 h1, h3⟩))
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
  refine ⟨f₁, q, r, hmodab, ⟨hf₁, insert q (insert r crit), hmem₁, hp₁, hq₁, D₁, hkq, ?_, ε, ε',
    hε, hε', ?_, ?_, hr₀q, hrmq, ?_, ?_, ?_, ?_, c₂, ?_, ?_, ?_⟩, ?_, ?_, hidxr⟩
  · exact hkp₁.trans hkp
  · rw [hr₀p]; exact (hconst p hp).1
  · rw [hrmp]; exact (hconst p hp).2
  · rw [hfp]; linarith
  · intro x hx hxp hxq
    rw [Finset.mem_insert, Finset.mem_insert] at hx
    rw [hfp]
    rcases hx with hx | hx | hx
    · exact absurd hx hxq
    · rw [hx]
      constructor
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · rw [(hoffK x (hcritmem x hx)).1]
      refine ⟨by linarith [hsepp x hx hxp], ?_⟩
      rcases hgap x hx with h2 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  · intro x hx hxp y hy
    rw [hfp]
    have hx' := hx
    rw [Finset.mem_insert, Finset.mem_insert] at hx'
    rcases hx' with hx' | hx' | hx'
    · have h1 := (hnewball x hx (Or.inl hx') y hy).2
      intro h2; linarith [h2.2]
    · have h1 := (hnewball x hx (Or.inr hx') y hy).2
      intro h2; linarith [h2.2]
    · have hy' : y ∈ D.closedSmallBall x hx' := by rw [← hball_eq x hx']; exact hy
      have h1 := hnear x hx' y (D.closedSmallBall_subset_image_ball x hx' hy')
      have hyK : f y ∉ Ioo c₂ c₃ := by
        intro h'
        rcases hgap x hx' with h2 | h2
        · linarith [h'.1, h1.2]
        · linarith [h'.2, h1.1]
      rw [(hoffK y hyK).1]
      intro h2
      have h3 := hsepp x hx' hxp
      rcases le_or_gt 0 (f x - f p) with h4 | h4
      · rw [abs_of_nonneg h4] at h3; linarith [h1.1, h2.2]
      · rw [abs_of_neg h4] at h3; linarith [h1.2, h2.1]
  · intro y hy s hs x hx
    obtain ⟨t, rfl⟩ := exists_angle_of_mem_leftModelSphere D₁ hq₁ hkq hε' hy
    rw [hfp] at hs
    rcases le_or_gt s (f₁ q - ε' - c₂) with hsT | hsT
    · exact hdesc _ hy s ⟨hs.1, hsT⟩ x hx
    · have hsplit : D₁.flow s (leftPt D₁ q hq₁ hkq ε' t) =
          D₁.flow (s - (f₁ q - ε' - c₂)) (γ t) := by
        rw [← hloop]
        change _ = D₁.flow (s - (f₁ q - ε' - c₂))
          (D₁.flow (f₁ q - ε' - c₂) (leftPt D₁ q hq₁ hkq ε' t))
        rw [← GradientLikeStrip.flow_add]
        congr 1
        ring
      change D₁.flow s (leftPt D₁ q hq₁ hkq ε' t) ∉ _
      rw [hsplit, hflowγ t _ (by linarith)]
      have hx' := hx
      rw [Finset.mem_insert, Finset.mem_insert] at hx'
      have hlow : f (D.flow (s - (f₁ q - ε' - c₂)) (γ t)) ≤ c₂ := by
        have := GradientLikeStrip.f_flow_le (D := D) hf.smooth (γ t)
          (t := s - (f₁ q - ε' - c₂)) (by linarith)
        rw [hγlev t] at this
        exact this
      rcases hx' with hx' | hx' | hx'
      · intro hmem
        have := hKsub (hnewball x hx (Or.inl hx') _ hmem).1
        linarith [this.1]
      · intro hmem
        have := hKsub (hnewball x hx (Or.inr hx') _ hmem).1
        linarith [this.1]
      · have heq : D₁.closedSmallBall x hx = D.closedSmallBall x hx' := hball_eq x hx'
        rw [heq]
        exact hfree t _ ⟨by linarith, by linarith [hs.2]⟩ x hx'
  · rw [hfp]; linarith
  · linarith
  · rw [hloop]
    have hRε : 2 * ε < (D₁.chart p hp₁).R ^ 2 := by
      rw [hRp]
      have h1 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
        pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
      linarith [(hconst p hp).2]
    exact meetsRightOnce_transfer hf.smooth D D₁ hp hp₁ hχp hkp₁ hRp.le hfp hε hRε
      (by linarith) (by linarith) hγlev hfree (fun θ => hflowγ θ _ (by linarith)) hmeet
  · intro x hx hc
    rcases (hcrit₁ x).1 hc with h1 | h1 | h1
    · exact Or.inl ⟨(hpre x).1 hx, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · exact fun x hx => ⟨(hcrit₁ x).2 (Or.inl hx), hidx x hx⟩

theorem exists_partner_config [SigmaCompactSpace M] (h5 : 5 ≤ n)
    (hf : MorseStrip I f a b) (hsi : isSelfIndexing I f a b)
    (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) (hV₀ : ConnectedSpace (f ⁻¹' {a})) {p : M}
    (hp : f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ morseIndex I f p = 1)
    (htop : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f x = 1 → x ≠ p →
      f x < f p) :
    ∃ f₂ : M → ℝ, ∃ q r : M, ModifiedWithin f a b f₂ ∧ isPartnerConfig I f₂ a b p q ∧
      (∀ x, f₂ x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₂ x →
        (f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∨ x = q ∨ x = r) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₂ x ∧ morseIndex I f₂ x = morseIndex I f x) ∧
      morseIndex I f₂ r = 3 := by
  classical
  exact exists_partner_of_loop h5 hW (exists_loop_config h5 hf hsi hinj hidx hV₀ hp htop)

end Isolation

theorem partner_target (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : isSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) (hV₀ : ConnectedSpace (f ⁻¹' {a}))
    {p : M} (hp : f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ morseIndex I f p = 1) :
    ∃ f₁ : M → ℝ, ModifiedWithin f a b f₁ ∧ MorseStrip I f₁ a b ∧
      ∃ q : M, ∃ a' b' : ℝ, a < a' ∧ b' < b ∧
        (∀ x, f₁ x = a' ∨ f₁ x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x) ∧
        isCancellingPair I f₁ a' b' p q ∧
        ∀ x, f₁ x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x →
          (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∧ morseIndex I f₁ x = morseIndex I f x) ∨ x = q ∨
            morseIndex I f₁ x = 3 := by
  obtain ⟨g₁, hmod₁, hg₁, hsi₁, hinj₁, hcrit₁, hidx₁, htop₁⟩ := exists_top_index_one hf hsi hp
  have hpre₁ : ∀ x, g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hidx' : ∀ x, g₁ x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x →
      0 < morseIndex I g₁ x ∧ morseIndex I g₁ x < n := by
    intro x hx hc
    have hcf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcrit₁ x).1 hc
    rw [hidx₁ x hcf]
    exact hidx x ((hpre₁ x).1 hx) hcf
  have hW₁ : SimplyConnectedSpace (g₁ ⁻¹' Icc a b) := by
    rw [hmod₁.preimage_Icc]; exact hW
  have hV₁ : ConnectedSpace (g₁ ⁻¹' {a}) := by
    rw [hmod₁.preimage_singleton_left]; exact hV₀
  have hp₁ : g₁ p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ p ∧ morseIndex I g₁ p = 1 :=
    ⟨(hpre₁ p).2 hp.1, (hcrit₁ p).2 hp.2.1, (hidx₁ p hp.2.1).trans hp.2.2⟩
  obtain ⟨g₂, q, r, hmod₂, hconf, hcrit₂, hold₂, hidxr⟩ :=
    exists_partner_config h5 hg₁ hsi₁ hinj₁ hidx' hW₁ hV₁ hp₁ htop₁
  obtain ⟨g₃, hmod₃, hg₃, hcrit₃, hidx₃, a', b', ha', hb', hreg', hpair⟩ :=
    exists_isolate_partner hconf
  have hpre₃ : ∀ x, g₃ x ∈ Ioo a b ↔ g₂ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₃.preimage_Ioo x
  refine ⟨g₃, hmod₁.trans (hmod₂.trans hmod₃), hg₃, q, a', b', ha', hb', hreg', hpair, ?_⟩
  intro x hx hc
  have hx₂ : g₂ x ∈ Ioo a b := (hpre₃ x).1 hx
  have hc₂ : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := (hcrit₃ x).1 hc
  rcases hcrit₂ x hx₂ hc₂ with ⟨-, hc₁⟩ | hxq | hxr
  · left
    refine ⟨(hcrit₁ x).1 hc₁, ?_⟩
    rw [hidx₃ x hc₂, (hold₂ x hc₁).2, hidx₁ x ((hcrit₁ x).1 hc₁)]
  · exact Or.inr (Or.inl hxq)
  · right; right
    rw [hidx₃ x hc₂, hxr, hidxr]

end

end IndexOnePartner

end DifferentialGeometry.Topology
