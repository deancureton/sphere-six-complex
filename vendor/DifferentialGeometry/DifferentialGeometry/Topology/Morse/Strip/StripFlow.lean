module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.GradientLike
public import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le negPart posPart morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split)

noncomputable section

theorem forall_mem_uIcc_zero_iff {T : ℝ} {P : ℝ → Prop} :
    (∀ s ∈ uIcc 0 T, P s) ↔ ∀ l ∈ Icc (0 : ℝ) 1, P (l * T) := by
  constructor
  · intro h l hl
    refine h _ ?_
    rw [mem_uIcc]
    rcases le_or_gt 0 T with hT | hT
    · left; constructor <;> nlinarith [hl.1, hl.2]
    · right; constructor <;> nlinarith [hl.1, hl.2]
  · intro h s hs
    rcases eq_or_ne T 0 with hT | hT
    · subst hT
      rw [uIcc_self, mem_singleton_iff] at hs
      subst hs
      simpa using h 0 ⟨le_rfl, zero_le_one⟩
    · have := h (s / T) ?_
      · rwa [div_mul_cancel₀ s hT] at this
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hT' : 0 < T := lt_of_le_of_ne (h1.trans h2) (Ne.symm hT)
        exact ⟨div_nonneg h1 hT'.le, (div_le_one hT').2 h2⟩
      · have hT' : T < 0 := lt_of_le_of_ne (h1.trans h2) hT
        exact ⟨div_nonneg_of_nonpos h2 hT'.le, (div_le_one_of_neg hT').2 h1⟩

theorem Icc_subset_of_isClosed_of_step {Q : Set ℝ} (hQ : IsClosed Q) {T : ℝ} (h0 : (0 : ℝ) ∈ Q)
    (hstep : ∀ t ∈ Ico (0 : ℝ) T, Icc 0 t ⊆ Q → Q ∈ 𝓝[>] t) : Icc 0 T ⊆ Q := by
  set S : Set ℝ := {t | Icc 0 t ⊆ Q} with hS
  have hsub : Icc 0 T ⊆ S := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · have : S ∩ Icc 0 T = Icc 0 T ∩ ⋂ l ∈ Icc (0 : ℝ) 1, (fun t => l * t) ⁻¹' Q := by
        ext t
        simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, fun l hl => h1 ⟨by nlinarith [hl.1, h2.1], by nlinarith [hl.2, h2.1]⟩⟩
        · rintro ⟨h2, h1⟩
          refine ⟨fun u hu => ?_, h2⟩
          rcases eq_or_lt_of_le h2.1 with ht | ht
          · have hu0 : u = 0 := by rw [← ht] at hu; exact le_antisymm hu.2 hu.1
            rw [hu0]; exact h0
          · have := h1 (u / t) ⟨div_nonneg hu.1 ht.le, (div_le_one ht).2 hu.2⟩
            rwa [div_mul_cancel₀ u ht.ne'] at this
      rw [this]
      exact isClosed_Icc.inter
        (isClosed_biInter fun l _ => hQ.preimage (continuous_const.mul continuous_id))
    · change Icc (0 : ℝ) 0 ⊆ Q
      rw [Icc_self]; exact singleton_subset_iff.2 h0
    · rintro t ⟨htS, htI⟩
      have hQt := hstep t htI htS
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hQt
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨u, hu, fun t' ht' => ?_⟩
      change Icc 0 t' ⊆ Q
      intro s hs
      rcases le_or_gt s t with hst | hst
      · exact htS ⟨hs.1, hst⟩
      · exact hsub ⟨hst, hs.2.trans ht'.2⟩
  exact fun t ht => hsub ht ⟨ht.1, le_rfl⟩

theorem Icc_neg_subset_of_isClosed_of_step {Q : Set ℝ} (hQ : IsClosed Q) {T : ℝ}
    (h0 : (0 : ℝ) ∈ Q)
    (hstep : ∀ t ∈ Ioc (-T) (0 : ℝ), Icc t 0 ⊆ Q → Q ∈ 𝓝[<] t) : Icc (-T) 0 ⊆ Q := by
  have hQ' : IsClosed ((fun t : ℝ => -t) ⁻¹' Q) := hQ.preimage continuous_neg
  have h0' : (0 : ℝ) ∈ (fun t : ℝ => -t) ⁻¹' Q := by simpa using h0
  have hmain : Icc 0 T ⊆ (fun t : ℝ => -t) ⁻¹' Q := by
    refine Icc_subset_of_isClosed_of_step hQ' h0' fun t ht hIcc => ?_
    have h1 : Icc (-t) 0 ⊆ Q := fun s hs => by
      have := hIcc (show -s ∈ Icc 0 t from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      simpa using this
    have h2 := hstep (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ h1
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ico_subset.1 h2
    refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨-l, by simp only [mem_Iio] at hl; simp; linarith,
      fun s hs => ?_⟩
    change -s ∈ Q
    exact hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
  intro s hs
  have := hmain (show -s ∈ Icc 0 T from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  simpa using this

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} (d : MorseNormalChart I f p)

theorem symm_mem {S : Set (Fin n → ℝ)} (hS : S ⊆ Metric.ball 0 d.R') {w : M}
    (hw : w ∈ d.χ '' S) : d.χ.symm w ∈ S := by
  obtain ⟨y, hy, rfl⟩ := hw
  rw [d.χ.left_inv (d.hball (hS hy))]
  exact hy

theorem mem_image_of_symm_mem {S : Set (Fin n → ℝ)} {w : M} (hw : w ∈ d.χ '' Metric.ball 0 d.R')
    (hS : d.χ.symm w ∈ S) : w ∈ d.χ '' S :=
  ⟨_, hS, d.symm_image_eq hw⟩

theorem lt_subset_ball {r : ℝ} (hr : r ≤ d.R') :
    {y : Fin n → ℝ | morseNorm n y < r} ⊆ Metric.ball 0 d.R' :=
  fun _ hy => mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy hr)

theorem le_subset_ball {r : ℝ} (hr : r < d.R') :
    {y : Fin n → ℝ | morseNorm n y ≤ r} ⊆ Metric.ball 0 d.R' :=
  fun _ hy => mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy hr)

theorem f_eq_nf_symm {w : M} (hw : w ∈ d.χ '' {y | morseNorm n y ≤ d.R}) :
    f w = morseNormalForm d.hk (f p) (d.χ.symm w) := by
  obtain ⟨y, hy, rfl⟩ := hw
  rw [d.χ.left_inv (d.hsrc y hy)]
  exact d.hnorm y hy

theorem isCompact_image_of_subset {K : Set (Fin n → ℝ)} (hK : IsCompact K) {r : ℝ}
    (hr : r < d.R') (hKr : K ⊆ {y | morseNorm n y ≤ r}) : IsCompact (d.χ '' K) :=
  hK.image_of_continuousOn (d.χ.continuousOn.mono ((hKr.trans (d.le_subset_ball hr)).trans d.hball))

def leftModelSphere (ε : ℝ) : Set (Fin n → ℝ) :=
  {y | posPart d.hk y = 0 ∧ ‖negPart d.hk y‖ ^ 2 = 2 * ε}

def rightModelSphere (ε : ℝ) : Set (Fin n → ℝ) :=
  {y | negPart d.hk y = 0 ∧ ‖posPart d.hk y‖ ^ 2 = 2 * ε}

theorem morseNorm_sq_of_mem_leftModelSphere {ε : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ d.leftModelSphere ε) : morseNorm n y ^ 2 = 2 * ε := by
  rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hy.1, hy.2]; simp

theorem morseNorm_sq_of_mem_rightModelSphere {ε : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ d.rightModelSphere ε) : morseNorm n y ^ 2 = 2 * ε := by
  rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hy.1, hy.2]; simp

theorem nf_of_mem_leftModelSphere {ε : ℝ} {y : Fin n → ℝ} (hy : y ∈ d.leftModelSphere ε) :
    morseNormalForm d.hk (f p) y = f p - ε := by
  rw [morseNormalForm_split, hy.1, hy.2, norm_zero]; ring

theorem nf_of_mem_rightModelSphere {ε : ℝ} {y : Fin n → ℝ} (hy : y ∈ d.rightModelSphere ε) :
    morseNormalForm d.hk (f p) y = f p + ε := by
  rw [morseNormalForm_split, hy.1, hy.2, norm_zero]; ring

theorem continuous_negPart : Continuous (negPart d.hk) := (ModelField.negPartL d.hk).continuous

theorem continuous_posPart : Continuous (posPart d.hk) := (ModelField.posPartL d.hk).continuous

theorem isClosed_leftModelSphere (ε : ℝ) : IsClosed (d.leftModelSphere ε) :=
  (isClosed_eq d.continuous_posPart continuous_const).inter
    (isClosed_eq (d.continuous_negPart.norm.pow 2) continuous_const)

theorem isClosed_rightModelSphere (ε : ℝ) : IsClosed (d.rightModelSphere ε) :=
  (isClosed_eq d.continuous_negPart continuous_const).inter
    (isClosed_eq (d.continuous_posPart.norm.pow 2) continuous_const)

theorem morseNorm_le_of_sq_le {y : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : morseNorm n y ^ 2 ≤ r ^ 2) :
    morseNorm n y ≤ r :=
  (pow_le_pow_iff_left₀ (ModelField.morseNorm_nonneg y) hr two_ne_zero).1 h

theorem morseNorm_le_sqrt_of_sq_le {y : Fin n → ℝ} {B : ℝ} (h : morseNorm n y ^ 2 ≤ B) :
    morseNorm n y ≤ Real.sqrt B := by
  have hB : 0 ≤ B := (sq_nonneg _).trans h
  exact (Real.le_sqrt (ModelField.morseNorm_nonneg y) hB).2 h

theorem leftModelSphere_subset (ε : ℝ) :
    d.leftModelSphere ε ⊆ {y | morseNorm n y ≤ Real.sqrt (2 * ε)} := fun _ hy =>
  morseNorm_le_sqrt_of_sq_le (d.morseNorm_sq_of_mem_leftModelSphere hy).le

theorem rightModelSphere_subset (ε : ℝ) :
    d.rightModelSphere ε ⊆ {y | morseNorm n y ≤ Real.sqrt (2 * ε)} := fun _ hy =>
  morseNorm_le_sqrt_of_sq_le (d.morseNorm_sq_of_mem_rightModelSphere hy).le

theorem isCompact_leftModelSphere (ε : ℝ) : IsCompact (d.leftModelSphere ε) :=
  (isCompact_morseNorm_le _).of_isClosed_subset (d.isClosed_leftModelSphere ε)
    (d.leftModelSphere_subset ε)

theorem isCompact_rightModelSphere (ε : ℝ) : IsCompact (d.rightModelSphere ε) :=
  (isCompact_morseNorm_le _).of_isClosed_subset (d.isClosed_rightModelSphere ε)
    (d.rightModelSphere_subset ε)

theorem morseNorm_le_R_of_mem_leftModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ d.leftModelSphere ε) : morseNorm n y ≤ d.R :=
  morseNorm_le_of_sq_le d.R_pos.le ((d.morseNorm_sq_of_mem_leftModelSphere hy).le.trans hε)

theorem morseNorm_le_R_of_mem_rightModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ d.rightModelSphere ε) : morseNorm n y ≤ d.R :=
  morseNorm_le_of_sq_le d.R_pos.le ((d.morseNorm_sq_of_mem_rightModelSphere hy).le.trans hε)

theorem f_chart_of_mem_leftModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ d.leftModelSphere ε) : f (d.χ y) = f p - ε := by
  rw [d.hnorm y (d.morseNorm_le_R_of_mem_leftModelSphere hε hy), d.nf_of_mem_leftModelSphere hy]

theorem f_chart_of_mem_rightModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ d.rightModelSphere ε) : f (d.χ y) = f p + ε := by
  rw [d.hnorm y (d.morseNorm_le_R_of_mem_rightModelSphere hε hy),
    d.nf_of_mem_rightModelSphere hy]

theorem isCompact_image_leftModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) :
    IsCompact (d.χ '' d.leftModelSphere ε) :=
  d.isCompact_image_of_subset (d.isCompact_leftModelSphere ε) d.hRR'
    fun _ hy => d.morseNorm_le_R_of_mem_leftModelSphere hε hy

theorem isCompact_image_rightModelSphere {ε : ℝ} (hε : 2 * ε ≤ d.R ^ 2) :
    IsCompact (d.χ '' d.rightModelSphere ε) :=
  d.isCompact_image_of_subset (d.isCompact_rightModelSphere ε) d.hRR'
    fun _ hy => d.morseNorm_le_R_of_mem_rightModelSphere hε hy

end MorseNormalChart

namespace ModelField

variable {k : ℕ} (hk : k ≤ n)

theorem nf_ge_linear (c : ℝ) {r₀ θ₀ : ℝ} (hr₀ : 0 < r₀) (hθ₀ : 0 ≤ θ₀) {γ : ℝ → Fin n → ℝ}
    {t₀ t₁ : ℝ} (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t)
    (hθ : ∀ t ∈ Icc t₀ t₁, θ₀ ≤ theta r₀ (γ t)) (ht₀₁ : t₀ ≤ t₁) :
    morseNormalForm hk c (γ t₁) + θ₀ * ‖posPart hk (γ t₁)‖ ^ 2 * (t₁ - t₀) ≤
      morseNormalForm hk c (γ t₀) := by
  have hanti := normSq_posPart_antitoneOn hk hr₀ hγ
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun s => morseNormalForm hk c (γ s) + θ₀ * ‖posPart hk (γ t₁)‖ ^ 2 * s)
      (-(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + θ₀ * ‖posPart hk (γ t₁)‖ ^ 2) t := by
    intro t ht
    have := (hasDerivAt_nf_curve hk c hγ ht).add
      ((hasDerivAt_id' (x := t)).const_mul (θ₀ * ‖posPart hk (γ t₁)‖ ^ 2))
    rw [mul_one] at this
    exact this
  have hm : AntitoneOn
      (fun s => morseNormalForm hk c (γ s) + θ₀ * ‖posPart hk (γ t₁)‖ ^ 2 * s) (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁)
      (f' := fun t => -(theta r₀ (γ t) * morseNorm n (γ t) ^ 2) + θ₀ * ‖posPart hk (γ t₁)‖ ^ 2)
      (HasDerivAt.continuousOn hd) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have ht' := Ioo_subset_Icc_self ht
      have h1 := hθ t ht'
      have h2 := hanti ht' (right_mem_Icc.2 ht₀₁) ht'.2
      simp only at h2
      have h3 := sq_nonneg ‖posPart hk (γ t₁)‖
      have h4 : 0 ≤ theta r₀ (γ t) := (theta_pos hr₀ _).le
      have h5 := morseNorm_sq_eq_negPart_add_posPart hk (γ t)
      have h6 := sq_nonneg ‖negPart hk (γ t)‖
      nlinarith [mul_le_mul h1 h2 h3 h4]
  have := hm (left_mem_Icc.2 ht₀₁) (right_mem_Icc.2 ht₀₁) ht₀₁
  simp only at this
  linarith

end ModelField

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace GradientLikeStrip

variable (D : GradientLikeStrip I f a b crit)

theorem smooth_one :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, D.V x⟩ : TangentBundle I M)) :=
  D.smooth.of_le (by norm_num)

def smallBall (p : M) (hp : p ∈ crit) : Set M :=
  (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).r₀}

def closedSmallBall (p : M) (hp : p ∈ crit) : Set M :=
  (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀}

theorem r₀_lt_R (p : M) (hp : p ∈ crit) : (D.chart p hp).r₀ < (D.chart p hp).R := by
  linarith [(D.chart p hp).hr₀R, (D.chart p hp).hr₀]

theorem r₀_lt_R' (p : M) (hp : p ∈ crit) : (D.chart p hp).r₀ < (D.chart p hp).R' :=
  (D.r₀_lt_R p hp).trans (D.chart p hp).hRR'

theorem isOpen_smallBall (p : M) (hp : p ∈ crit) : IsOpen (D.smallBall p hp) :=
  (D.chart p hp).isOpen_image_of_lt (D.r₀_lt_R' p hp).le

theorem isCompact_closedSmallBall (p : M) (hp : p ∈ crit) :
    IsCompact (D.closedSmallBall p hp) :=
  (D.chart p hp).isCompact_image_le (D.r₀_lt_R' p hp)

theorem smallBall_subset_closedSmallBall (p : M) (hp : p ∈ crit) :
    D.smallBall p hp ⊆ D.closedSmallBall p hp :=
  image_mono fun y (hy : morseNorm n y < _) => le_of_lt hy

theorem smallBall_subset_image_ball (p : M) (hp : p ∈ crit) :
    D.smallBall p hp ⊆ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
  (D.chart p hp).image_lt_subset_image_ball (D.r₀_lt_R' p hp).le

theorem closedSmallBall_subset_image_ball (p : M) (hp : p ∈ crit) :
    D.closedSmallBall p hp ⊆ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
  image_mono ((D.chart p hp).le_subset_ball (D.r₀_lt_R' p hp))

theorem p_mem_smallBall (p : M) (hp : p ∈ crit) : p ∈ D.smallBall p hp :=
  (D.chart p hp).p_mem_image_lt (D.chart p hp).hr₀

def unitRegion : Set M := {x | f x ∈ Icc a b ∧ ∀ p hp, x ∉ D.smallBall p hp}

theorem dfV_eq_neg_one_of_mem_unitRegion {x : M} (hx : x ∈ D.unitRegion) :
    dfV I f D.V x = -1 :=
  D.unit x hx.1 hx.2

theorem unitRegion_eq : D.unitRegion =
    f ⁻¹' Icc a b ∩ ⋂ q : {q // q ∈ crit}, (D.smallBall q.1 q.2)ᶜ := by
  ext x
  simp only [unitRegion, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, mem_compl_iff]
  exact and_congr_right fun _ => ⟨fun h q => h q.1 q.2, fun h p hp => h ⟨p, hp⟩⟩

theorem isClosed_unitRegion (hf : Continuous f) : IsClosed D.unitRegion := by
  rw [D.unitRegion_eq]
  exact (isClosed_Icc.preimage hf).inter
    (isClosed_iInter fun q => (D.isOpen_smallBall q.1 q.2).isClosed_compl)

def closedSmallBalls : Set M := ⋃ q : {q // q ∈ crit}, D.closedSmallBall q.1 q.2

theorem notMem_closedSmallBalls_iff {x : M} :
    x ∉ D.closedSmallBalls ↔ ∀ p hp, x ∉ D.closedSmallBall p hp := by
  simp only [closedSmallBalls, mem_iUnion, not_exists]
  exact ⟨fun h p hp => h ⟨p, hp⟩, fun h q => h q.1 q.2⟩

theorem dfV_eq_neg_one_of_level {c : ℝ} (hc : c ∈ Icc a b)
    (hcU : ∀ p hp, ∀ y ∈ D.smallBall p hp, f y ≠ c) {y : M} (hy : f y = c) :
    dfV I f D.V y = -1 :=
  D.dfV_eq_neg_one_of_mem_unitRegion ⟨hy ▸ hc, fun p hp hmem => hcU p hp y hmem hy⟩

theorem isOpen_modelBall (p : M) (hp : p ∈ crit) :
    IsOpen ((D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) :=
  (D.chart p hp).isOpen_image_of_lt (D.rm_lt_R' p hp).le

theorem modelBall_subset_image_ball (p : M) (hp : p ∈ crit) :
    (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} ⊆
      (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
  image_mono ((D.chart p hp).lt_subset_ball (D.rm_lt_R' p hp).le)

theorem modelBall_subset_image_le (p : M) (hp : p ∈ crit) :
    (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} ⊆
      (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).R} :=
  image_mono fun _ hy => (le_of_lt hy).trans (D.hrm p hp).2

variable [T2Space M]

theorem isClosed_closedSmallBall (p : M) (hp : p ∈ crit) : IsClosed (D.closedSmallBall p hp) :=
  (D.isCompact_closedSmallBall p hp).isClosed

theorem isClosed_closedSmallBalls : IsClosed D.closedSmallBalls :=
  isClosed_iUnion_of_finite fun q => D.isClosed_closedSmallBall q.1 q.2

variable [I.Boundaryless]

theorem hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ D.V :=
  exists_globalIntegralCurve_of_compactSupport D.V D.smooth D.compact

def flow (t : ℝ) (x : M) : M := curveAt D.V D.hcomplete x t

theorem isMIntegralCurve_flow (x : M) : IsMIntegralCurve (fun t => D.flow t x) D.V :=
  curveAt_integralCurve D.V D.hcomplete x

@[simp] theorem flow_zero (x : M) : D.flow 0 x = x := curveAt_zero D.V D.hcomplete x

theorem flow_add (x : M) (s t : ℝ) : D.flow (s + t) x = D.flow t (D.flow s x) :=
  curveAt_add D.V D.smooth_one D.hcomplete x s t

theorem flow_flow (x : M) (s t : ℝ) : D.flow t (D.flow s x) = D.flow (s + t) x :=
  (D.flow_add x s t).symm

theorem flow_neg_flow (x : M) (t : ℝ) : D.flow (-t) (D.flow t x) = x := by
  rw [flow_flow, add_neg_cancel, flow_zero]

theorem flow_flow_neg (x : M) (t : ℝ) : D.flow t (D.flow (-t) x) = x := by
  rw [flow_flow, neg_add_cancel, flow_zero]

theorem flow_injective (t : ℝ) : Function.Injective (D.flow t) :=
  curveAt_injective D.V D.smooth_one D.hcomplete t

theorem flow_eq_self_of_not_mem_tsupport {x : M} (hx : x ∉ tsupport D.V) (t : ℝ) :
    D.flow t x = x :=
  curveAt_eq_self_of_not_mem_tsupport D.V D.smooth D.hcomplete hx t

theorem contMDiff_flow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => D.flow q.1 q.2) :=
  contMDiff_globalFlow_joint_of_compactSupport D.V D.smooth D.compact

theorem continuous_flow_joint : Continuous (fun q : ℝ × M => D.flow q.1 q.2) :=
  D.contMDiff_flow_joint.continuous

theorem contMDiff_flow (t : ℝ) : ContMDiff I I ∞ (D.flow t) := fun x =>
  contMDiffAt_globalFlow_of_compactSupport D.V D.smooth D.compact t x

theorem continuous_flow (t : ℝ) : Continuous (D.flow t) := (D.contMDiff_flow t).continuous

theorem continuous_flow_curve (x : M) : Continuous (fun t => D.flow t x) :=
  (D.isMIntegralCurve_flow x).continuous

theorem flow_crit {p : M} (hp : p ∈ crit) (t : ℝ) : D.flow t p = p := by
  have hV : D.V p = 0 := D.V_crit p hp
  have hEq := integralCurve_eq_of_agree D.V D.smooth_one (D.isMIntegralCurve_flow p)
    (isMIntegralCurve_const hV) (t₀ := 0) (by simp)
  exact congrFun hEq t

theorem exists_Icc_flow_mem_open {O : Set M} (hO : IsOpen O) {x : M} {t : ℝ}
    (ht : D.flow t x ∈ O) : ∃ δ > 0, ∀ s ∈ Icc (t - δ) (t + δ), D.flow s x ∈ O := by
  have hmem : {s | D.flow s x ∈ O} ∈ 𝓝 t :=
    (D.continuous_flow_curve x).continuousAt.preimage_mem_nhds (hO.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε / 2, by positivity, fun s hs => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

variable {D}

theorem hasDerivAt_f_flow (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (D.flow s x)) (dfV I f D.V (D.flow t x)) t :=
  hasDerivAt_df_comp_integralCurve f hf D.V (D.isMIntegralCurve_flow x) t

theorem f_flow_le (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {t : ℝ} (ht : 0 ≤ t) :
    f (D.flow t x) ≤ f x := by
  have := (f_rate_bounds_of_integralCurve f hf D.V D.rate (D.isMIntegralCurve_flow x) ht).2
  simpa using this

theorem sub_le_f_flow (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {t : ℝ} (ht : 0 ≤ t) :
    f x - t ≤ f (D.flow t x) := by
  have := (f_rate_bounds_of_integralCurve f hf D.V D.rate (D.isMIntegralCurve_flow x) ht).1
  simpa using this

theorem f_flow_antitone (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Antitone (fun t => f (D.flow t x)) := by
  intro s t hst
  have := f_flow_le (D := D) hf (D.flow s x) (sub_nonneg.2 hst)
  rwa [flow_flow, add_sub_cancel] at this

theorem le_f_flow_of_nonpos (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {t : ℝ} (ht : t ≤ 0) :
    f x ≤ f (D.flow t x) := by
  have := f_flow_antitone (D := D) hf x ht
  simpa using this

theorem f_flow_le_sub_of_nonpos (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {t : ℝ} (ht : t ≤ 0) :
    f (D.flow t x) ≤ f x - t := by
  have := sub_le_f_flow (D := D) hf (D.flow t x) (neg_nonneg.2 ht)
  rw [flow_neg_flow] at this
  linarith

theorem f_flow_mem_uIcc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (s : ℝ) :
    f (D.flow s x) ∈ uIcc (f x) (f x - s) := by
  rw [mem_uIcc]
  rcases le_or_gt 0 s with hs | hs
  · right; exact ⟨sub_le_f_flow hf x hs, f_flow_le hf x hs⟩
  · left; exact ⟨le_f_flow_of_nonpos hf x hs.le, f_flow_le_sub_of_nonpos hf x hs.le⟩

theorem f_flow_mem_uIcc_of_mem_uIcc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {s u : ℝ}
    (hu : u ∈ uIcc 0 s) : f (D.flow u x) ∈ uIcc (f x) (f (D.flow s x)) := by
  have hanti := f_flow_antitone (D := D) hf x
  rw [mem_uIcc] at hu ⊢
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    refine ⟨hanti h2, ?_⟩
    have := hanti h1
    simpa using this
  · left
    refine ⟨?_, hanti h1⟩
    have := hanti h2
    simpa using this

theorem f_flow_eq_sub (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ} (hT : 0 ≤ T)
    (hstay : ∀ s ∈ Icc 0 T, D.flow s x ∈ D.unitRegion) :
    ∀ s ∈ Icc 0 T, f (D.flow s x) = f x - s := by
  have _ := hT
  intro s hs
  have := f_eq_sub_of_integralCurve_on_set f hf D.V D.unitRegion
    (fun y hy => D.dfV_eq_neg_one_of_mem_unitRegion hy) (D.isMIntegralCurve_flow x) hs.1
    (fun u hu => hstay u ⟨hu.1, hu.2.trans hs.2⟩)
  simpa using this

theorem f_flow_eq_sub_neg (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ} (hT : 0 ≤ T)
    (hstay : ∀ s ∈ Icc (-T) 0, D.flow s x ∈ D.unitRegion) :
    ∀ s ∈ Icc (-T) 0, f (D.flow s x) = f x - s := by
  set y := D.flow (-T) x with hy
  have hstay' : ∀ u ∈ Icc 0 T, D.flow u y ∈ D.unitRegion := by
    intro u hu
    rw [hy, flow_flow]
    exact hstay _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h := f_flow_eq_sub hf hT hstay'
  have hT' := h T (right_mem_Icc.2 hT)
  rw [hy, flow_flow, neg_add_cancel, flow_zero] at hT'
  intro s hs
  have hs' := h (s + T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [hy, flow_flow, show -T + (s + T) = s by ring] at hs'
  rw [hs']
  linarith

theorem f_flow_eq_sub_of_avoid_uIcc' (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {s : ℝ}
    (hx : f x ∈ Icc a b) (hs : f (D.flow s x) ∈ Icc a b)
    (havoid : ∀ u ∈ uIcc 0 s, ∀ p hp, D.flow u x ∉ D.smallBall p hp) :
    ∀ u ∈ uIcc 0 s, f (D.flow u x) = f x - u := by
  have hstay : ∀ u ∈ uIcc 0 s, D.flow u x ∈ D.unitRegion := fun u hu =>
    ⟨uIcc_subset_Icc hx hs (f_flow_mem_uIcc_of_mem_uIcc hf x hu), havoid u hu⟩
  rcases le_or_gt 0 s with h0 | h0
  · rw [uIcc_of_le h0] at hstay ⊢
    exact f_flow_eq_sub hf h0 hstay
  · rw [uIcc_of_ge h0.le] at hstay ⊢
    have := f_flow_eq_sub_neg hf (T := -s) (by linarith) (by rwa [neg_neg])
    rwa [neg_neg] at this

theorem f_flow_eq_sub_of_avoid_uIcc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ}
    (hx : f x ∈ Icc a b) (hxT : f x - T ∈ Icc a b)
    (havoid : ∀ s ∈ uIcc 0 T, ∀ p hp, D.flow s x ∉ D.smallBall p hp) :
    ∀ s ∈ uIcc 0 T, f (D.flow s x) = f x - s := by
  have hstay : ∀ u ∈ uIcc 0 T, D.flow u x ∈ D.unitRegion := fun u hu =>
    ⟨uIcc_subset_Icc hx hxT (uIcc_subset_uIcc left_mem_uIcc (by
      rw [mem_uIcc] at hu ⊢
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith) (f_flow_mem_uIcc hf x u)), havoid u hu⟩
  rcases le_or_gt 0 T with h0 | h0
  · rw [uIcc_of_le h0] at hstay ⊢
    exact f_flow_eq_sub hf h0 hstay
  · rw [uIcc_of_ge h0.le] at hstay ⊢
    have := f_flow_eq_sub_neg hf (T := -T) (by linarith) (by rwa [neg_neg])
    rwa [neg_neg] at this

theorem f_flow_eq_sub_of_levels (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {T : ℝ}
    (hx : f x ∈ Icc a b) (hxT : f x - T ∈ Icc a b)
    (hU : ∀ y, f y ∈ uIcc (f x) (f x - T) → ∀ p hp, y ∉ D.smallBall p hp) :
    ∀ s ∈ uIcc 0 T, f (D.flow s x) = f x - s := by
  refine f_flow_eq_sub_of_avoid_uIcc hf hx hxT fun s hs => hU _ ?_
  refine uIcc_subset_uIcc left_mem_uIcc ?_ (f_flow_mem_uIcc hf x s)
  rw [mem_uIcc] at hs ⊢
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

theorem flow_level_transport (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c' c : ℝ} (hc' : a ≤ c')
    (hcc' : c' ≤ c) (hc : c ≤ b) (hU : ∀ y, f y ∈ Icc c' c → ∀ p hp, y ∉ D.smallBall p hp) :
    (∀ x, f x = c → f (D.flow (c - c') x) = c' ∧ ∀ s ∈ Icc 0 (c - c'), f (D.flow s x) = c - s) ∧
    (∀ y, f y = c' → f (D.flow (c' - c) y) = c ∧
      ∀ s ∈ Icc (c' - c) 0, f (D.flow s y) = c' - s) := by
  constructor
  · intro x hx
    have h := f_flow_eq_sub_of_levels hf (x := x) (T := c - c')
      (by rw [hx]; exact ⟨hc'.trans hcc', hc⟩)
      (by rw [hx, sub_sub_cancel]; exact ⟨hc', hcc'.trans hc⟩) (by
        intro y hy
        rw [hx, sub_sub_cancel, uIcc_of_ge hcc'] at hy
        exact hU y hy)
    rw [uIcc_of_le (sub_nonneg.2 hcc'), hx] at h
    exact ⟨by rw [h _ (right_mem_Icc.2 (sub_nonneg.2 hcc'))]; ring, h⟩
  · intro y hy
    have h := f_flow_eq_sub_of_levels hf (x := y) (T := c' - c)
      (by rw [hy]; exact ⟨hc', hcc'.trans hc⟩)
      (by rw [hy, sub_sub_cancel]; exact ⟨hc'.trans hcc', hc⟩) (by
        intro z hz
        rw [hy, sub_sub_cancel, uIcc_of_le hcc'] at hz
        exact hU z hz)
    rw [uIcc_of_ge (sub_nonpos.2 hcc'), hy] at h
    exact ⟨by rw [h _ (left_mem_Icc.2 (sub_nonpos.2 hcc'))]; ring, h⟩

theorem flow_image_levelSet (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c' c : ℝ} (hc' : a ≤ c')
    (hcc' : c' ≤ c) (hc : c ≤ b) (hU : ∀ y, f y ∈ Icc c' c → ∀ p hp, y ∉ D.smallBall p hp) :
    D.flow (c - c') '' (f ⁻¹' {c}) = f ⁻¹' {c'} := by
  obtain ⟨h1, h2⟩ := flow_level_transport hf hc' hcc' hc hU
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h1 x hx).1
  · intro hz
    refine ⟨D.flow (c' - c) z, (h2 z hz).1, ?_⟩
    rw [flow_flow, sub_add_sub_cancel, sub_self, flow_zero]

theorem flow_level_unique (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hcU : ∀ y, f y = c → dfV I f D.V y = -1) {x : M} {t t' : ℝ} (ht : f (D.flow t x) = c)
    (ht' : f (D.flow t' x) = c) : t = t' := by
  have key : ∀ t t' : ℝ, t < t' → f (D.flow t x) = c → f (D.flow t' x) = c → False := by
    intro t t' htt' ht ht'
    set g : ℝ → ℝ := fun s => f (D.flow s x) with hg
    have hanti : Antitone g := f_flow_antitone hf x
    have hconst : ∀ s ∈ Icc t t', g s = c := fun s hs =>
      le_antisymm (ht ▸ hanti hs.1) (ht' ▸ hanti hs.2)
    have h1 : HasDerivWithinAt g (-1) (Ici t) t := by
      have := (hasDerivAt_f_flow (D := D) hf x t).hasDerivWithinAt (s := Ici t)
      rwa [hcU _ ht] at this
    have h2 : HasDerivWithinAt g 0 (Ici t) t := by
      refine (hasDerivWithinAt_const t (Ici t) c).congr_of_eventuallyEq ?_
        (hconst t ⟨le_rfl, htt'.le⟩)
      filter_upwards [Icc_mem_nhdsGE htt'] with s hs
      exact hconst s hs
    have := (uniqueDiffWithinAt_Ici t).eq_deriv _ h1 h2
    norm_num at this
  rcases lt_trichotomy t t' with h | h | h
  · exact absurd (key t t' h ht ht') id
  · exact h
  · exact absurd (key t' t h ht' ht) id

variable (D)

def regularFlowDomain (c : ℝ) : Set M :=
  {x | f x ∈ Ioo a b ∧ ∀ s ∈ uIcc 0 (f x - c), ∀ p hp, D.flow s x ∉ D.closedSmallBall p hp}

def π (c : ℝ) (x : M) : M := D.flow (f x - c) x

theorem isOpen_regularFlowDomain (hf : Continuous f) (c : ℝ) : IsOpen (D.regularFlowDomain c) := by
  have hC : IsClosed D.closedSmallBalls := D.isClosed_closedSmallBalls
  set G : ℝ × M → M := fun q => D.flow (q.1 * (f q.2 - c)) q.2 with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun q : ℝ × M => (q.1 * (f q.2 - c), q.2)) :=
      (continuous_fst.mul ((hf.comp continuous_snd).sub continuous_const)).prodMk continuous_snd
    exact D.continuous_flow_joint.comp h1
  have hΩ : D.regularFlowDomain c = {x | f x ∈ Ioo a b} ∩
      {x | ∀ l ∈ Icc (0 : ℝ) 1, G (l, x) ∉ D.closedSmallBalls} := by
    ext x
    simp only [regularFlowDomain, mem_inter_iff, mem_ofPred_eq, D.notMem_closedSmallBalls_iff]
    exact and_congr_right fun _ =>
      forall_mem_uIcc_zero_iff (P := fun s => ∀ p hp, D.flow s x ∉ D.closedSmallBall p hp)
  rw [hΩ]
  refine (isOpen_Ioo.preimage hf).inter ?_
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hsub : Icc (0 : ℝ) 1 ×ˢ {x} ⊆ G ⁻¹' D.closedSmallBallsᶜ := by
    rintro ⟨l, x'⟩ ⟨hl, hx'⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hx l hl
  obtain ⟨u, v, -, hv, hsu, hxv, huv⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    (hC.isOpen_compl.preimage hGc) hsub
  exact ⟨v, fun x' hx' l hl => huv ⟨hsu hl, hx'⟩, hv, hxv rfl⟩

theorem contMDiff_π (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) : ContMDiff I I ∞ (D.π c) := by
  have h1 : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x => (f x - c, x)) :=
    (hf.sub contMDiff_const).prodMk contMDiff_id
  exact D.contMDiff_flow_joint.comp h1

theorem continuous_π (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) : Continuous (D.π c) :=
  (D.contMDiff_π hf c).continuous

variable {D}

theorem f_flow_eq_sub_of_mem_regularFlowDomain (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} (hc : c ∈ Icc a b) {x : M}
    (hx : x ∈ D.regularFlowDomain c) : ∀ s ∈ uIcc 0 (f x - c), f (D.flow s x) = f x - s :=
  f_flow_eq_sub_of_avoid_uIcc hf ⟨hx.1.1.le, hx.1.2.le⟩ (by rwa [sub_sub_cancel])
    fun s hs p hp hmem => hx.2 s hs p hp (D.smallBall_subset_closedSmallBall p hp hmem)

theorem f_π (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} (hc : c ∈ Icc a b) {x : M} (hx : x ∈ D.regularFlowDomain c) :
    f (D.π c x) = c := by
  have := f_flow_eq_sub_of_mem_regularFlowDomain hf hc hx _ right_mem_uIcc
  rw [π, this]; ring

theorem π_notMem_closedSmallBall {c : ℝ} {x : M} (hx : x ∈ D.regularFlowDomain c) (p : M) (hp : p ∈ crit) :
    D.π c x ∉ D.closedSmallBall p hp :=
  hx.2 _ right_mem_uIcc p hp

theorem π_mem_regularFlowDomain (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} (hc : c ∈ Ioo a b) {x : M}
    (hx : x ∈ D.regularFlowDomain c) : D.π c x ∈ D.regularFlowDomain c := by
  have hπ : f (D.π c x) = c := f_π hf ⟨hc.1.le, hc.2.le⟩ hx
  refine ⟨by rw [hπ]; exact hc, fun s hs p hp => ?_⟩
  rw [hπ, sub_self, uIcc_self, mem_singleton_iff] at hs
  rw [hs, flow_zero]
  exact π_notMem_closedSmallBall hx p hp

theorem π_eq_self_of_level {c : ℝ} {x : M} (hx : f x = c) : D.π c x = x := by
  rw [π, hx, sub_self, flow_zero]

theorem π_flow (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} (hc : c ∈ Icc a b)
    (hcU : ∀ p hp, ∀ y ∈ D.smallBall p hp, f y ≠ c) {x : M} {s : ℝ} (hx : x ∈ D.regularFlowDomain c)
    (hs : D.flow s x ∈ D.regularFlowDomain c) : D.π c (D.flow s x) = D.π c x := by
  have h1 : f (D.π c x) = c := f_π hf hc hx
  have h2 : f (D.π c (D.flow s x)) = c := f_π hf hc hs
  have hcU' : ∀ y, f y = c → dfV I f D.V y = -1 := fun y hy => D.dfV_eq_neg_one_of_level hc hcU hy
  unfold π at h1 h2 ⊢
  rw [flow_flow] at h2 ⊢
  rw [flow_level_unique hf hcU' h2 h1]

theorem flow_mem_regularFlowDomain (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} {x : M} {s : ℝ}
    (hx : x ∈ D.regularFlowDomain c) (hs : f (D.flow s x) ∈ Ioo a b)
    (havoid : ∀ u ∈ uIcc 0 s, ∀ p hp, D.flow u x ∉ D.closedSmallBall p hp) :
    D.flow s x ∈ D.regularFlowDomain c := by
  have hfs : ∀ u ∈ uIcc 0 s, f (D.flow u x) = f x - u :=
    f_flow_eq_sub_of_avoid_uIcc' hf ⟨hx.1.1.le, hx.1.2.le⟩ ⟨hs.1.le, hs.2.le⟩
      fun u hu p hp hm => havoid u hu p hp (D.smallBall_subset_closedSmallBall p hp hm)
  have hfs' := hfs s right_mem_uIcc
  refine ⟨hs, fun u hu p hp => ?_⟩
  rw [flow_flow]
  rw [hfs'] at hu
  have hmem : s + u ∈ uIcc s (f x - c) := by
    rw [mem_uIcc] at hu ⊢
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  rcases uIcc_subset_uIcc_union_uIcc (b := 0) hmem with h | h
  · rw [uIcc_comm] at h
    exact havoid _ h p hp
  · exact hx.2 _ h p hp

variable (D)

def leftSphere (q : M) (hq : q ∈ crit) (ε c : ℝ) : Set M :=
  D.flow (f q - ε - c) '' ((D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε)

def rightSphere (p : M) (hp : p ∈ crit) (ε c : ℝ) : Set M :=
  D.flow (f p + ε - c) '' ((D.chart p hp).χ '' (D.chart p hp).rightModelSphere ε)

theorem isCompact_leftSphere (q : M) (hq : q ∈ crit) {ε : ℝ} (hε : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (c : ℝ) : IsCompact (D.leftSphere q hq ε c) :=
  ((D.chart q hq).isCompact_image_leftModelSphere hε).image (D.continuous_flow _)

theorem isCompact_rightSphere (p : M) (hp : p ∈ crit) {ε : ℝ}
    (hε : 2 * ε ≤ (D.chart p hp).R ^ 2) (c : ℝ) : IsCompact (D.rightSphere p hp ε c) :=
  ((D.chart p hp).isCompact_image_rightModelSphere hε).image (D.continuous_flow _)

theorem mem_leftSphere_iff (q : M) (hq : q ∈ crit) (ε c : ℝ) {x : M} :
    x ∈ D.leftSphere q hq ε c ↔
      D.flow (c - (f q - ε)) x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    rwa [flow_flow, show f q - ε - c + (c - (f q - ε)) = 0 by ring, flow_zero]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [flow_flow, show c - (f q - ε) + (f q - ε - c) = 0 by ring, flow_zero]

theorem mem_rightSphere_iff (p : M) (hp : p ∈ crit) (ε c : ℝ) {x : M} :
    x ∈ D.rightSphere p hp ε c ↔
      D.flow (c - (f p + ε)) x ∈ (D.chart p hp).χ '' (D.chart p hp).rightModelSphere ε := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    rwa [flow_flow, show f p + ε - c + (c - (f p + ε)) = 0 by ring, flow_zero]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [flow_flow, show c - (f p + ε) + (f p + ε - c) = 0 by ring, flow_zero]

theorem leftSphere_subset_level (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (q : M) (hq : q ∈ crit) {ε c : ℝ}
    (hε : 2 * ε ≤ (D.chart q hq).R ^ 2) (hc : c ∈ Icc a b)
    (hU : ∀ y, f y ∈ uIcc (f q - ε) c → ∀ p hp, y ∉ D.smallBall p hp) :
    D.leftSphere q hq ε c ⊆ f ⁻¹' {c} := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hfy : f ((D.chart q hq).χ y) = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hε hy
  have hstrip : f ((D.chart q hq).χ y) ∈ Ioo a b := D.inStrip q hq ⟨y,
    (D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hε hy),
    rfl⟩
  have := f_flow_eq_sub_of_levels hf (x := (D.chart q hq).χ y) (T := f q - ε - c)
    ⟨hstrip.1.le, hstrip.2.le⟩ (by rw [hfy, sub_sub_cancel]; exact hc)
    (by rw [hfy, sub_sub_cancel]; exact hU) _ right_mem_uIcc
  rw [mem_preimage, mem_singleton_iff, this, hfy]
  ring

theorem rightSphere_subset_level (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (hp : p ∈ crit)
    {ε c : ℝ} (hε : 2 * ε ≤ (D.chart p hp).R ^ 2) (hc : c ∈ Icc a b)
    (hU : ∀ y, f y ∈ uIcc (f p + ε) c → ∀ p' hp', y ∉ D.smallBall p' hp') :
    D.rightSphere p hp ε c ⊆ f ⁻¹' {c} := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hfy : f ((D.chart p hp).χ y) = f p + ε :=
    (D.chart p hp).f_chart_of_mem_rightModelSphere hε hy
  have hstrip : f ((D.chart p hp).χ y) ∈ Ioo a b := D.inStrip p hp ⟨y,
    (D.chart p hp).mem_ball_of_le ((D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere hε hy),
    rfl⟩
  have := f_flow_eq_sub_of_levels hf (x := (D.chart p hp).χ y) (T := f p + ε - c)
    ⟨hstrip.1.le, hstrip.2.le⟩ (by rw [hfy, sub_sub_cancel]; exact hc)
    (by rw [hfy, sub_sub_cancel]; exact hU) _ right_mem_uIcc
  rw [mem_preimage, mem_singleton_iff, this, hfy]
  ring

variable {D}

theorem hasDerivAt_symm_flow_of_pullback {p : M} (d : MorseNormalChart I f p)
    {Y : (Fin n → ℝ) → Fin n → ℝ} {x : M} {s : ℝ} (hs : D.flow s x ∈ d.χ '' Metric.ball 0 d.R')
    (hY : mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (D.flow s x) (D.V (D.flow s x)) =
      Y (d.χ.symm (D.flow s x))) :
    HasDerivAt (fun s => d.χ.symm (D.flow s x)) (Y (d.χ.symm (D.flow s x))) s := by
  have hγ := D.isMIntegralCurve_flow x
  have hsymm : HasMFDerivAt I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (D.flow s x)
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (D.flow s x)) :=
    (d.mdifferentiableAt_symm hs).hasMFDerivAt
  have hcomp := HasMFDerivAt.comp s hsymm (hγ s)
  have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  rw [hasDerivAt_iff_hasFDerivAt]
  refine (hfd.congr_fderiv ?_)
  apply ContinuousLinearMap.ext
  intro r
  change (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (D.flow s x)) ((id r : ℝ) • D.V (D.flow s x)) =
    (id r : ℝ) • Y (d.χ.symm (D.flow s x))
  rw [map_smul, hY]
  rfl

theorem hasDerivAt_symm_flow {p : M} (hp : p ∈ crit) {x : M} {s : ℝ}
    (hs : D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) :
    HasDerivAt (fun s => (D.chart p hp).χ.symm (D.flow s x))
      (ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀
        ((D.chart p hp).χ.symm (D.flow s x))) s := by
  obtain ⟨y, hy, hxy⟩ := hs
  have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' :=
    mem_ball_of_morseNorm_lt ((show morseNorm n y < D.rm p hp from hy).trans (D.rm_lt_R' p hp))
  refine hasDerivAt_symm_flow_of_pullback (D.chart p hp) ⟨y, hyb, hxy⟩ ?_
  rw [← hxy, (D.chart p hp).χ.left_inv ((D.chart p hp).hball hyb)]
  exact D.model p hp y hy

theorem hasDerivAt_symm_flow_Icc {p : M} (hp : p ∈ crit) {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => (D.chart p hp).χ.symm (D.flow s x))
      (ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀
        ((D.chart p hp).χ.symm (D.flow s x))) s :=
  fun s hs => hasDerivAt_symm_flow hp (h s hs)

theorem flow_mem_of_negPart_eq_zero {p : M} (hp : p ∈ crit) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) (hu : negPart (D.chart p hp).hk y = 0) {t : ℝ} (ht : 0 ≤ t) :
    D.flow t ((D.chart p hp).χ y) ∈ (D.chart p hp).χ ''
      {z | morseNorm n z ≤ morseNorm n y ∧ negPart (D.chart p hp).hk z = 0} := by
  set x := (D.chart p hp).χ y with hx
  set S : Set (Fin n → ℝ) :=
    {z | morseNorm n z ≤ morseNorm n y ∧ negPart (D.chart p hp).hk z = 0} with hS
  set O := (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hSsub : S ⊆ {z | morseNorm n z < D.rm p hp} := fun z hz => lt_of_le_of_lt hz.1 hy
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset ((isCompact_morseNorm_le _).of_isClosed_subset
      ((isClosed_morseNorm_le _).inter
        (isClosed_eq (D.chart p hp).continuous_negPart continuous_const))
      fun z hz => hz.1) (hy.trans (D.rm_lt_R' p hp)) fun z hz => hz.1
  have hQc : IsClosed {s : ℝ | D.flow s x ∈ (D.chart p hp).χ '' S} :=
    hSK.isClosed.preimage (D.continuous_flow_curve x)
  refine Icc_subset_of_isClosed_of_step hQc ?_ ?_ ⟨ht, le_rfl⟩
  · change D.flow 0 x ∈ (D.chart p hp).χ '' S
    rw [flow_zero]; exact ⟨y, ⟨le_rfl, hu⟩, rfl⟩
  · intro s hs hIcc
    have hsO : D.flow s x ∈ O := image_mono hSsub (hIcc (right_mem_Icc.2 hs.1))
    obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open hOopen hsO
    refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + δ, by simp [hδ], fun s' hs' => ?_⟩
    change D.flow s' x ∈ (D.chart p hp).χ '' S
    have hODE : ∀ u ∈ Icc s s', D.flow u x ∈ O := fun u hu =>
      hδO u ⟨by linarith [hu.1], hu.2.trans hs'.2⟩
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hss' : s ≤ s' := hs'.1.le
    obtain ⟨z, hz, hzx⟩ := hIcc (right_mem_Icc.2 hs.1)
    have hγs : (D.chart p hp).χ.symm (D.flow s x) = z := by
      rw [← hzx, (D.chart p hp).χ.left_inv
        ((D.chart p hp).hsrc z (hz.1.trans (hy.le.trans (D.hrm p hp).2)))]
    have hu0 : negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s x)) = 0 := by
      rw [hγs]; exact hz.2
    have hneg : negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s' x)) = 0 :=
      ModelField.negPart_eq_zero_of_left (D.chart p hp).hk (D.chart p hp).hr₀ hγ hu0 hss' s'
        (right_mem_Icc.2 hss')
    have hanti : ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s' x))‖ ^ 2 ≤
        ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s x))‖ ^ 2 :=
      ModelField.normSq_posPart_antitoneOn (D.chart p hp).hk (D.chart p hp).hr₀ hγ
        (left_mem_Icc.2 hss') (right_mem_Icc.2 hss') hss'
    refine (D.chart p hp).mem_image_of_symm_mem (D.modelBall_subset_image_ball p hp
      (hODE s' (right_mem_Icc.2 hss'))) ⟨?_, hneg⟩
    have h1 := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow s' x))
    have h2 := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow s x))
    rw [hneg, norm_zero] at h1
    rw [hu0, norm_zero] at h2
    rw [hγs] at h2 hanti
    refine MorseNormalChart.morseNorm_le_of_sq_le (ModelField.morseNorm_nonneg y) ?_
    have hz1 : morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 :=
      pow_le_pow_left₀ (ModelField.morseNorm_nonneg z) hz.1 2
    nlinarith

theorem flow_mem_of_posPart_eq_zero {p : M} (hp : p ∈ crit) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) (hv : posPart (D.chart p hp).hk y = 0) {t : ℝ} (ht : t ≤ 0) :
    D.flow t ((D.chart p hp).χ y) ∈ (D.chart p hp).χ ''
      {z | morseNorm n z ≤ morseNorm n y ∧ posPart (D.chart p hp).hk z = 0} := by
  set x := (D.chart p hp).χ y with hx
  set S : Set (Fin n → ℝ) :=
    {z | morseNorm n z ≤ morseNorm n y ∧ posPart (D.chart p hp).hk z = 0} with hS
  set O := (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hSsub : S ⊆ {z | morseNorm n z < D.rm p hp} := fun z hz => lt_of_le_of_lt hz.1 hy
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset ((isCompact_morseNorm_le _).of_isClosed_subset
      ((isClosed_morseNorm_le _).inter
        (isClosed_eq (D.chart p hp).continuous_posPart continuous_const))
      fun z hz => hz.1) (hy.trans (D.rm_lt_R' p hp)) fun z hz => hz.1
  have hQc : IsClosed {s : ℝ | D.flow s x ∈ (D.chart p hp).χ '' S} :=
    hSK.isClosed.preimage (D.continuous_flow_curve x)
  refine Icc_neg_subset_of_isClosed_of_step hQc ?_ ?_ (T := -t) ⟨by rw [neg_neg], ht⟩
  · change D.flow 0 x ∈ (D.chart p hp).χ '' S
    rw [flow_zero]; exact ⟨y, ⟨le_rfl, hv⟩, rfl⟩
  · intro s hs hIcc
    have hsO : D.flow s x ∈ O := image_mono hSsub (hIcc (left_mem_Icc.2 hs.2))
    obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open hOopen hsO
    refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨s - δ, by simp [hδ], fun s' hs' => ?_⟩
    change D.flow s' x ∈ (D.chart p hp).χ '' S
    have hODE : ∀ u ∈ Icc s' s, D.flow u x ∈ O := fun u hu =>
      hδO u ⟨hs'.1.trans hu.1, by linarith [hu.2]⟩
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hss' : s' ≤ s := hs'.2.le
    obtain ⟨z, hz, hzx⟩ := hIcc (left_mem_Icc.2 hs.2)
    have hγs : (D.chart p hp).χ.symm (D.flow s x) = z := by
      rw [← hzx, (D.chart p hp).χ.left_inv
        ((D.chart p hp).hsrc z (hz.1.trans (hy.le.trans (D.hrm p hp).2)))]
    have hv0 : posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s x)) = 0 := by
      rw [hγs]; exact hz.2
    have hpos : posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s' x)) = 0 :=
      ModelField.posPart_eq_zero_of_right (D.chart p hp).hk (D.chart p hp).hr₀ hγ hv0 hss' s'
        (left_mem_Icc.2 hss')
    have hmono : ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s' x))‖ ^ 2 ≤
        ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s x))‖ ^ 2 :=
      ModelField.normSq_negPart_monotoneOn (D.chart p hp).hk (D.chart p hp).hr₀ hγ
        (left_mem_Icc.2 hss') (right_mem_Icc.2 hss') hss'
    refine (D.chart p hp).mem_image_of_symm_mem (D.modelBall_subset_image_ball p hp
      (hODE s' (left_mem_Icc.2 hss'))) ⟨?_, hpos⟩
    have h1 := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow s' x))
    have h2 := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow s x))
    rw [hpos, norm_zero] at h1
    rw [hv0, norm_zero] at h2
    rw [hγs] at h2 hmono
    refine MorseNormalChart.morseNorm_le_of_sq_le (ModelField.morseNorm_nonneg y) ?_
    have hz1 : morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 :=
      pow_le_pow_left₀ (ModelField.morseNorm_nonneg z) hz.1 2
    nlinarith

theorem f_p_le_f_flow_of_negPart_eq_zero {p : M} (hp : p ∈ crit) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) (hu : negPart (D.chart p hp).hk y = 0) {t : ℝ}
    (ht : 0 ≤ t) : f p ≤ f (D.flow t ((D.chart p hp).χ y)) := by
  obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := flow_mem_of_negPart_eq_zero hp hy hu ht
  rw [← hzx, (D.chart p hp).hnorm z (hz1.trans (hy.le.trans (D.hrm p hp).2)),
    morseNormalForm_split, hz2]
  simp only [norm_zero]
  nlinarith [sq_nonneg ‖posPart (D.chart p hp).hk z‖]

theorem f_flow_le_f_p_of_posPart_eq_zero {p : M} (hp : p ∈ crit) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) (hv : posPart (D.chart p hp).hk y = 0) {t : ℝ}
    (ht : t ≤ 0) : f (D.flow t ((D.chart p hp).χ y)) ≤ f p := by
  obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := flow_mem_of_posPart_eq_zero hp hy hv ht
  rw [← hzx, (D.chart p hp).hnorm z (hz1.trans (hy.le.trans (D.hrm p hp).2)),
    morseNormalForm_split, hz2]
  simp only [norm_zero]
  nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk z‖]

theorem exists_exit_desc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M} (hq : q ∈ crit) {ε : ℝ}
    (hε : 0 < ε) {y : Fin n → ℝ}
    (hball : 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 < D.rm q hq ^ 2)
    (hu : negPart (D.chart q hq).hk y ≠ 0)
    (hlevel : f q - ε ≤ morseNormalForm (D.chart q hq).hk (f q) y) :
    ∃ t, 0 ≤ t ∧ f (D.flow t ((D.chart q hq).χ y)) = f q - ε ∧
      (∀ s ∈ Icc 0 t, D.flow s ((D.chart q hq).χ y) ∈ (D.chart q hq).χ ''
        {z | morseNorm n z ^ 2 ≤ 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2}) ∧
      2 * ε * ‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm
        (D.flow t ((D.chart q hq).χ y)))‖ ^ 2 ≤
        ‖negPart (D.chart q hq).hk y‖ ^ 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 := by
  set x := (D.chart q hq).χ y with hx
  set B := 2 * ε + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set S : Set (Fin n → ℝ) := {z | morseNorm n z ^ 2 ≤ B} with hS
  set O := (D.chart q hq).χ '' {z | morseNorm n z < D.rm q hq} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall q hq
  have hrm := D.rm_pos q hq
  have hrmR' := D.rm_lt_R' q hq
  have hSsub : S ⊆ {z | morseNorm n z < D.rm q hq} := fun z hz =>
    lt_of_pow_lt_pow_left₀ 2 hrm.le (lt_of_le_of_lt hz hball)
  have hSsub' : S ⊆ {z | morseNorm n z ≤ Real.sqrt B} := fun z hz =>
    MorseNormalChart.morseNorm_le_sqrt_of_sq_le hz
  have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
  have hSK : IsCompact ((D.chart q hq).χ '' S) :=
    (D.chart q hq).isCompact_image_of_subset
      ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
      (((Real.sqrt_lt' hrm).2 hball).trans hrmR') hSsub'
  have hKO : (D.chart q hq).χ '' S ⊆ O := image_mono hSsub
  have hOball := D.modelBall_subset_image_ball q hq
  have hOle := D.modelBall_subset_image_le q hq
  set g : ℝ → ℝ := fun s => f (D.flow s x) with hg
  have hgc : Continuous g := hf.continuous.comp (D.continuous_flow_curve x)
  have hganti : Antitone g := f_flow_antitone (D := D) hf x
  have hnf : ∀ s, D.flow s x ∈ O →
      g s = morseNormalForm (D.chart q hq).hk (f q) ((D.chart q hq).χ.symm (D.flow s x)) :=
    fun s hs => (D.chart q hq).f_eq_nf_symm (hOle hs)
  have hyS : y ∈ S := by
    change morseNorm n y ^ 2 ≤ B
    rw [morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk]
    rw [morseNormalForm_split] at hlevel
    linarith
  have hγ0 : (D.chart q hq).χ.symm (D.flow 0 x) = y := by
    rw [flow_zero, hx, (D.chart q hq).χ.left_inv
      ((D.chart q hq).hball (mem_ball_of_morseNorm_lt ((hSsub hyS).trans hrmR')))]
  have hsymmS : ∀ s, D.flow s x ∈ (D.chart q hq).χ '' S →
      morseNorm n ((D.chart q hq).χ.symm (D.flow s x)) ^ 2 ≤ B :=
    fun s hs => (D.chart q hq).symm_mem (hSsub.trans ((D.chart q hq).lt_subset_ball hrmR'.le)) hs
  have claim1 : ∀ T, 0 ≤ T → (∀ s ∈ Icc 0 T, f q - ε ≤ g s) →
      ∀ s ∈ Icc 0 T, D.flow s x ∈ (D.chart q hq).χ '' S := by
    intro T hT hlev
    have hQc : IsClosed {s : ℝ | D.flow s x ∈ (D.chart q hq).χ '' S} :=
      hSK.isClosed.preimage (D.continuous_flow_curve x)
    have _ := hT
    refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
    · change D.flow 0 x ∈ (D.chart q hq).χ '' S
      rw [flow_zero]; exact ⟨y, hyS, rfl⟩
    · intro t ht hIcc
      have htO : D.flow t x ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
      obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open hOopen htO
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + δ) T, ?_, fun s hs => ?_⟩
      · change t < min (t + δ) T
        exact lt_min (by linarith) ht.2
      change D.flow s x ∈ (D.chart q hq).χ '' S
      have hs0 : 0 ≤ s := ht.1.trans hs.1.le
      have hsT : s ≤ T := hs.2.trans (min_le_right _ _)
      have hODE : ∀ u ∈ Icc 0 s, D.flow u x ∈ O := fun u hu => by
        rcases le_or_gt u t with h | h
        · exact hKO (hIcc ⟨hu.1, h⟩)
        · exact hδO u ⟨by linarith, hu.2.trans (hs.2.trans (min_le_left _ _))⟩
      have hγ := hasDerivAt_symm_flow_Icc hq hODE
      have hv : ‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow s x))‖ ^ 2 ≤
          ‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow 0 x))‖ ^ 2 :=
        ModelField.normSq_posPart_antitoneOn (D.chart q hq).hk (D.chart q hq).hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
      rw [hγ0] at hv
      have hlev_s := hlev s ⟨hs0, hsT⟩
      rw [hnf s (hODE s (right_mem_Icc.2 hs0)), morseNormalForm_split] at hlev_s
      refine (D.chart q hq).mem_image_of_symm_mem (hOball (hODE s (right_mem_Icc.2 hs0))) ?_
      change morseNorm n ((D.chart q hq).χ.symm (D.flow s x)) ^ 2 ≤ B
      rw [morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk]
      linarith
  set θ₀ : ℝ := (B + (D.chart q hq).r₀ ^ 2)⁻¹ with hθ₀
  have hr₀ := (D.chart q hq).hr₀
  have hθ₀pos : 0 < θ₀ := by positivity
  have hθ : ∀ z : Fin n → ℝ, morseNorm n z ^ 2 ≤ B → θ₀ ≤ ModelField.theta (D.chart q hq).r₀ z := by
    intro z hz
    have := ModelField.theta_ge_of_le (D.chart q hq).hr₀
      (MorseNormalChart.morseNorm_le_sqrt_of_sq_le hz)
    rwa [Real.sq_sqrt hB0] at this
  have hU₀pos : 0 < ‖negPart (D.chart q hq).hk y‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  have hθU : 0 < θ₀ * ‖negPart (D.chart q hq).hk y‖ ^ 2 := mul_pos hθ₀pos hU₀pos
  set T := (morseNormalForm (D.chart q hq).hk (f q) y - (f q - ε)) /
    (θ₀ * ‖negPart (D.chart q hq).hk y‖ ^ 2) + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ (morseNormalForm (D.chart q hq).hk (f q) y - (f q - ε)) /
        (θ₀ * ‖negPart (D.chart q hq).hk y‖ ^ 2) :=
      div_nonneg (by linarith) hθU.le
    linarith
  have hdrop : ∃ u₁ ∈ Icc 0 T, g u₁ < f q - ε := by
    by_contra hcon
    push Not at hcon
    have hK' := claim1 T hTpos.le hcon
    have hODE : ∀ u ∈ Icc 0 T, D.flow u x ∈ O := fun u hu => hKO (hK' u hu)
    have hγ := hasDerivAt_symm_flow_Icc hq hODE
    have hθ' : ∀ u ∈ Icc 0 T,
        θ₀ ≤ ModelField.theta (D.chart q hq).r₀ ((D.chart q hq).χ.symm (D.flow u x)) :=
      fun u hu => hθ _ (hsymmS u (hK' u hu))
    have hlin := ModelField.nf_le_linear (D.chart q hq).hk (f q) (D.chart q hq).hr₀ hθ₀pos.le
      hγ hθ' T (right_mem_Icc.2 hTpos.le)
    simp only [hγ0, sub_zero] at hlin
    have hcT := hcon T (right_mem_Icc.2 hTpos.le)
    rw [hnf T (hODE T (right_mem_Icc.2 hTpos.le))] at hcT
    have hTeq : θ₀ * ‖negPart (D.chart q hq).hk y‖ ^ 2 * T =
        morseNormalForm (D.chart q hq).hk (f q) y - (f q - ε) +
          θ₀ * ‖negPart (D.chart q hq).hk y‖ ^ 2 := by
      rw [hT]; field_simp
    nlinarith
  obtain ⟨u₁, hu₁, hu₁lt⟩ := hdrop
  have hg0 : f q - ε ≤ g 0 := by
    rw [hnf 0 (hKO ⟨y, hyS, by rw [flow_zero]⟩), hγ0]; exact hlevel
  obtain ⟨t, ht, hgt⟩ : ∃ t ∈ Icc 0 u₁, g t = f q - ε :=
    intermediate_value_Icc' hu₁.1 hgc.continuousOn ⟨hu₁lt.le, hg0⟩
  have hlev : ∀ s ∈ Icc 0 t, f q - ε ≤ g s := fun s hs => by
    rw [← hgt]; exact hganti hs.2
  have hK' := claim1 t ht.1 hlev
  refine ⟨t, ht.1, hgt, hK', ?_⟩
  have hODE : ∀ u ∈ Icc 0 t, D.flow u x ∈ O := fun u hu => hKO (hK' u hu)
  have hγ := hasDerivAt_symm_flow_Icc hq hODE
  have hprod := ModelField.normSq_negPart_mul_posPart_const (D.chart q hq).hk hγ t
    (right_mem_Icc.2 ht.1)
  simp only [hγ0] at hprod
  have hgt' := hgt
  rw [hnf t (hODE t (right_mem_Icc.2 ht.1)), morseNormalForm_split] at hgt'
  have hut : ‖negPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow t x))‖ ^ 2 =
      2 * ε + ‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow t x))‖ ^ 2 := by linarith
  rw [hut] at hprod
  nlinarith [sq_nonneg (‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow t x))‖ ^ 2)]

theorem exists_exit_asc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} (hp : p ∈ crit) {ε : ℝ}
    (hε : 0 < ε) {y : Fin n → ℝ}
    (hball : 2 * ε + 2 * ‖negPart (D.chart p hp).hk y‖ ^ 2 < D.rm p hp ^ 2)
    (hv : posPart (D.chart p hp).hk y ≠ 0)
    (hlevel : morseNormalForm (D.chart p hp).hk (f p) y ≤ f p + ε) :
    ∃ t, 0 ≤ t ∧ f (D.flow (-t) ((D.chart p hp).χ y)) = f p + ε ∧
      (∀ s ∈ Icc (-t) 0, D.flow s ((D.chart p hp).χ y) ∈ (D.chart p hp).χ ''
        {z | morseNorm n z ^ 2 ≤ 2 * ε + 2 * ‖negPart (D.chart p hp).hk y‖ ^ 2}) ∧
      2 * ε * ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm
        (D.flow (-t) ((D.chart p hp).χ y)))‖ ^ 2 ≤
        ‖negPart (D.chart p hp).hk y‖ ^ 2 * ‖posPart (D.chart p hp).hk y‖ ^ 2 := by
  set x := (D.chart p hp).χ y with hx
  set B := 2 * ε + 2 * ‖negPart (D.chart p hp).hk y‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set S : Set (Fin n → ℝ) := {z | morseNorm n z ^ 2 ≤ B} with hS
  set O := (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hrm := D.rm_pos p hp
  have hrmR' := D.rm_lt_R' p hp
  have hSsub : S ⊆ {z | morseNorm n z < D.rm p hp} := fun z hz =>
    lt_of_pow_lt_pow_left₀ 2 hrm.le (lt_of_le_of_lt hz hball)
  have hSsub' : S ⊆ {z | morseNorm n z ≤ Real.sqrt B} := fun z hz =>
    MorseNormalChart.morseNorm_le_sqrt_of_sq_le hz
  have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset
      ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
      (((Real.sqrt_lt' hrm).2 hball).trans hrmR') hSsub'
  have hKO : (D.chart p hp).χ '' S ⊆ O := image_mono hSsub
  have hOball := D.modelBall_subset_image_ball p hp
  have hOle := D.modelBall_subset_image_le p hp
  set g : ℝ → ℝ := fun s => f (D.flow s x) with hg
  have hgc : Continuous g := hf.continuous.comp (D.continuous_flow_curve x)
  have hganti : Antitone g := f_flow_antitone (D := D) hf x
  have hnf : ∀ s, D.flow s x ∈ O →
      g s = morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm (D.flow s x)) :=
    fun s hs => (D.chart p hp).f_eq_nf_symm (hOle hs)
  have hyS : y ∈ S := by
    change morseNorm n y ^ 2 ≤ B
    rw [morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk]
    rw [morseNormalForm_split] at hlevel
    linarith
  have hγ0 : (D.chart p hp).χ.symm (D.flow 0 x) = y := by
    rw [flow_zero, hx, (D.chart p hp).χ.left_inv
      ((D.chart p hp).hball (mem_ball_of_morseNorm_lt ((hSsub hyS).trans hrmR')))]
  have hsymmS : ∀ s, D.flow s x ∈ (D.chart p hp).χ '' S →
      morseNorm n ((D.chart p hp).χ.symm (D.flow s x)) ^ 2 ≤ B :=
    fun s hs => (D.chart p hp).symm_mem (hSsub.trans ((D.chart p hp).lt_subset_ball hrmR'.le)) hs
  have claim1 : ∀ T, 0 ≤ T → (∀ s ∈ Icc (-T) 0, g s ≤ f p + ε) →
      ∀ s ∈ Icc (-T) 0, D.flow s x ∈ (D.chart p hp).χ '' S := by
    intro T hT hlev
    have hQc : IsClosed {s : ℝ | D.flow s x ∈ (D.chart p hp).χ '' S} :=
      hSK.isClosed.preimage (D.continuous_flow_curve x)
    have _ := hT
    refine Icc_neg_subset_of_isClosed_of_step hQc ?_ ?_
    · change D.flow 0 x ∈ (D.chart p hp).χ '' S
      rw [flow_zero]; exact ⟨y, hyS, rfl⟩
    · intro t ht hIcc
      have htO : D.flow t x ∈ O := hKO (hIcc (left_mem_Icc.2 ht.2))
      obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open hOopen htO
      refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨max (t - δ) (-T), ?_, fun s hs => ?_⟩
      · change max (t - δ) (-T) < t
        exact max_lt (by linarith) ht.1
      change D.flow s x ∈ (D.chart p hp).χ '' S
      have hs0 : s ≤ 0 := hs.2.le.trans ht.2
      have hsT : -T ≤ s := (le_max_right _ _).trans hs.1
      have hODE : ∀ u ∈ Icc s 0, D.flow u x ∈ O := fun u hu => by
        rcases le_or_gt t u with h | h
        · exact hKO (hIcc ⟨h, hu.2⟩)
        · exact hδO u ⟨(le_max_left _ _).trans (hs.1.trans hu.1), by linarith⟩
      have hγ := hasDerivAt_symm_flow_Icc hp hODE
      have hu' : ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow s x))‖ ^ 2 ≤
          ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow 0 x))‖ ^ 2 :=
        ModelField.normSq_negPart_monotoneOn (D.chart p hp).hk (D.chart p hp).hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
      rw [hγ0] at hu'
      have hlev_s := hlev s ⟨hsT, hs0⟩
      rw [hnf s (hODE s (left_mem_Icc.2 hs0)), morseNormalForm_split] at hlev_s
      refine (D.chart p hp).mem_image_of_symm_mem (hOball (hODE s (left_mem_Icc.2 hs0))) ?_
      change morseNorm n ((D.chart p hp).χ.symm (D.flow s x)) ^ 2 ≤ B
      rw [morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk]
      linarith
  set θ₀ : ℝ := (B + (D.chart p hp).r₀ ^ 2)⁻¹ with hθ₀
  have hr₀ := (D.chart p hp).hr₀
  have hθ₀pos : 0 < θ₀ := by positivity
  have hθ : ∀ z : Fin n → ℝ, morseNorm n z ^ 2 ≤ B → θ₀ ≤ ModelField.theta (D.chart p hp).r₀ z := by
    intro z hz
    have := ModelField.theta_ge_of_le (D.chart p hp).hr₀
      (MorseNormalChart.morseNorm_le_sqrt_of_sq_le hz)
    rwa [Real.sq_sqrt hB0] at this
  have hV₀pos : 0 < ‖posPart (D.chart p hp).hk y‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hθV : 0 < θ₀ * ‖posPart (D.chart p hp).hk y‖ ^ 2 := mul_pos hθ₀pos hV₀pos
  set T := (f p + ε - morseNormalForm (D.chart p hp).hk (f p) y) /
    (θ₀ * ‖posPart (D.chart p hp).hk y‖ ^ 2) + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ (f p + ε - morseNormalForm (D.chart p hp).hk (f p) y) /
        (θ₀ * ‖posPart (D.chart p hp).hk y‖ ^ 2) :=
      div_nonneg (by linarith) hθV.le
    linarith
  have hdrop : ∃ u₁ ∈ Icc (-T) 0, f p + ε < g u₁ := by
    by_contra hcon
    push Not at hcon
    have hK' := claim1 T hTpos.le hcon
    have hODE : ∀ u ∈ Icc (-T) 0, D.flow u x ∈ O := fun u hu => hKO (hK' u hu)
    have hγ := hasDerivAt_symm_flow_Icc hp hODE
    have hθ' : ∀ u ∈ Icc (-T) 0,
        θ₀ ≤ ModelField.theta (D.chart p hp).r₀ ((D.chart p hp).χ.symm (D.flow u x)) :=
      fun u hu => hθ _ (hsymmS u (hK' u hu))
    have hlin := ModelField.nf_ge_linear (D.chart p hp).hk (f p) (D.chart p hp).hr₀ hθ₀pos.le
      hγ hθ' (by linarith)
    simp only [hγ0, sub_neg_eq_add, zero_add] at hlin
    have hcT := hcon (-T) (left_mem_Icc.2 (by linarith))
    rw [hnf (-T) (hODE (-T) (left_mem_Icc.2 (by linarith)))] at hcT
    have hTeq : θ₀ * ‖posPart (D.chart p hp).hk y‖ ^ 2 * T =
        f p + ε - morseNormalForm (D.chart p hp).hk (f p) y +
          θ₀ * ‖posPart (D.chart p hp).hk y‖ ^ 2 := by
      rw [hT]; field_simp
    nlinarith
  obtain ⟨u₁, hu₁, hu₁lt⟩ := hdrop
  have hg0 : g 0 ≤ f p + ε := by
    rw [hnf 0 (hKO ⟨y, hyS, by rw [flow_zero]⟩), hγ0]; exact hlevel
  obtain ⟨t', ht', hgt⟩ : ∃ t' ∈ Icc u₁ 0, g t' = f p + ε :=
    intermediate_value_Icc' hu₁.2 hgc.continuousOn ⟨hg0, hu₁lt.le⟩
  have hlev : ∀ s ∈ Icc (-(-t')) 0, g s ≤ f p + ε := fun s hs => by
    rw [← hgt]; exact hganti (by rw [neg_neg] at hs; exact hs.1)
  have hK' := claim1 (-t') (by linarith [ht'.2]) hlev
  refine ⟨-t', by linarith [ht'.2], by rw [neg_neg]; exact hgt, hK', ?_⟩
  have hODE : ∀ u ∈ Icc (-(-t')) 0, D.flow u x ∈ O := fun u hu => hKO (hK' u hu)
  have hγ := hasDerivAt_symm_flow_Icc hp hODE
  have hprod := ModelField.normSq_negPart_mul_posPart_const (D.chart p hp).hk hγ 0
    (right_mem_Icc.2 (by linarith [ht'.2]))
  simp only [hγ0, neg_neg] at hprod
  have hgt' := hgt
  rw [hnf t' (hODE t' (by rw [neg_neg]; exact left_mem_Icc.2 ht'.2)), morseNormalForm_split]
    at hgt'
  have hvt : ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow t' x))‖ ^ 2 =
      2 * ε + ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow t' x))‖ ^ 2 := by linarith
  rw [hvt] at hprod
  rw [neg_neg]
  nlinarith [sq_nonneg (‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow t' x))‖ ^ 2)]

end GradientLikeStrip

end

end DifferentialGeometry.Topology
