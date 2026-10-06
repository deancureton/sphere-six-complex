module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldDynamics

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

structure TransverseCancellingPair (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [DecidableEq M] (f : M → ℝ) (a' b' : ℝ) (p q : M) where
  hf : MorseStrip I f a' b'
  hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x
  hlt : f p < f q
  hidx : morseIndex I f q = morseIndex I f p + 1
  D : GradientLikeStrip I f a' b' {p, q}
  ε : ℝ
  c : ℝ
  hε : 0 < ε
  hr₀p : (D.chart p (mem_pair_left p q)).r₀ ^ 2 < 2 * ε
  hr₀q : (D.chart q (mem_pair_right p q)).r₀ ^ 2 < 2 * ε
  hrmp : 8 * ε < D.rm p (mem_pair_left p q) ^ 2
  hrmq : 8 * ε < D.rm q (mem_pair_right p q) ^ 2
  hc₁ : f p + ε < c
  hc₂ : c < f q - ε
  hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp'
  w₀ : Fin (D.chart q (mem_pair_right p q)).k → ℝ
  hw₀ : w₀ ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q)
  hzero : D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w₀ = 0
  huniq : ∀ w ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q),
    D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w = 0 → ∃ t : ℝ, 0 < t ∧ w = t • w₀
  hsurj : Function.Surjective
    (fderiv ℝ (D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q)) w₀)

theorem nonempty_transverseCancellingPair [DecidableEq M] (h : isCancellingPair I f a' b' p q) :
    Nonempty (TransverseCancellingPair I f a' b' p q) := by
  obtain ⟨hf, hcrit, hlt, hidx, D, ε, c, hε, h1, h2, h3, h4, h5, h6, hlev, w₀, hw₀, hz, hu, hs⟩ := h
  exact ⟨⟨hf, hcrit, hlt, hidx, D, ε, c, hε, h1, h2, h3, h4, h5, h6, hlev, w₀, hw₀, hz, hu, hs⟩⟩

namespace TransverseCancellingPair

variable [DecidableEq M] (c : TransverseCancellingPair I f a' b' p q)

abbrev dp : MorseNormalChart I f p := c.D.chart p (mem_pair_left p q)

abbrev dq : MorseNormalChart I f q := c.D.chart q (mem_pair_right p q)

def z₀ : M := c.dq.χ (c.dq.sphereParam c.ε c.w₀)

def arc : Set M := {p, q} ∪ range (fun t : ℝ => c.D.flow t c.z₀)

def y₀ : Fin n → ℝ := c.dp.χ.symm (c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀)

def e₁ : EuclideanSpace ℝ (Fin (n - c.dp.k)) := (Real.sqrt (2 * c.ε))⁻¹ • posPart c.dp.hk c.y₀

def u₀ : EuclideanSpace ℝ (Fin c.dq.k) := ‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀

end TransverseCancellingPair

namespace TransverseCancellingPair

variable [DecidableEq M] (c : TransverseCancellingPair I f a' b' p q)

theorem p_mem_arc : p ∈ c.arc := Or.inl (Or.inl rfl)

theorem q_mem_arc : q ∈ c.arc := Or.inl (Or.inr rfl)

theorem flow_mem_arc (t : ℝ) {x : M} (hx : x ∈ c.arc) : c.D.flow t x ∈ c.arc := by
  rcases hx with (rfl | rfl) | ⟨s, rfl⟩
  · rw [c.D.flow_crit (mem_pair_left x q)]; exact c.p_mem_arc
  · rw [c.D.flow_crit (mem_pair_right p x)]; exact c.q_mem_arc
  · exact Or.inr ⟨s + t, (c.D.flow_flow c.z₀ s t).symm⟩

def transitTime : ℝ := f q - f p - 2 * c.ε

theorem arc_eq : c.arc =
    (fun t : ℝ => c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) '' Icc 0 (Real.sqrt (2 * c.ε)) ∪
      (fun s : ℝ => c.D.flow s c.z₀) '' Icc 0 c.transitTime ∪
      (fun t : ℝ => c.dq.χ (recombine c.dq.hk (t • c.u₀) 0)) '' Icc 0 (Real.sqrt (2 * c.ε)) := by
  have hε := c.hε
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hpC : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hqC : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hrmp_pos := c.D.rm_pos p hpC
  have hrmq_pos := c.D.rm_pos q hqC
  have hsq_pos : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
  have hsqp : Real.sqrt (2 * c.ε) < c.D.rm p hpC := by
    rw [Real.sqrt_lt' hrmp_pos]; linarith [c.hrmp]
  have hsqq : Real.sqrt (2 * c.ε) < c.D.rm q hqC := by
    rw [Real.sqrt_lt' hrmq_pos]; linarith [c.hrmq]
  have hrec0 : ∀ {k : ℕ} (hk : k ≤ n), recombine hk (0 : EuclideanSpace ℝ (Fin k))
      (0 : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
    intro k hk
    funext i
    unfold recombine
    split_ifs <;> rfl
  have hw0 : c.w₀ ≠ 0 := c.hw₀.1
  have htoE : c.dq.toE c.w₀ ≠ 0 := c.dq.toE_ne_zero hw0
  have hu₀ : ‖c.u₀‖ = 1 := by
    change ‖‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 htoE)]
  have hz₀ : c.z₀ = c.dq.χ (recombine c.dq.hk (Real.sqrt (2 * c.ε) • c.u₀) 0) := by
    change c.dq.χ (c.dq.sphereParam c.ε c.w₀) = _
    unfold MorseNormalChart.sphereParam
    rw [div_eq_mul_inv]
    change _ = c.dq.χ (recombine c.dq.hk (Real.sqrt (2 * c.ε) • ‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀) 0)
    rw [smul_smul]
  have hland : c.D.landing p hqC c.ε c.c c.ε c.w₀ = c.D.flow c.transitTime c.z₀ := by
    change c.D.flow (c.c - (f p + c.ε)) (c.D.flow (f q - c.ε - c.c) c.z₀) = _
    rw [c.D.flow_flow]
    change _ = c.D.flow (f q - f p - 2 * c.ε) c.z₀
    congr 1
    ring
  have hlandR := c.hw₀.2
  have hlandB : c.D.landing p hqC c.ε c.c c.ε c.w₀ ∈ c.dp.χ '' Metric.ball 0 c.dp.R' :=
    c.dp.image_lt_subset_image_ball c.dp.hRR'.le hlandR
  have hlandLe : c.D.landing p hqC c.ε c.c c.ε c.w₀ ∈ c.dp.χ '' {y | morseNorm n y ≤ c.dp.R} :=
    image_mono (fun y (hy : morseNorm n y < c.dp.R) => le_of_lt hy) hlandR
  have hχy₀ : c.dp.χ c.y₀ = c.D.landing p hqC c.ε c.c c.ε c.w₀ := c.dp.symm_image_eq hlandB
  have hεR : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have h1 := (c.D.hrm q hqC).2
    have h2 : c.D.rm q hqC ^ 2 ≤ c.dq.R ^ 2 := pow_le_pow_left₀ hrmq_pos.le h1 2
    linarith [c.hrmq]
  have hfland : f (c.D.landing p hqC c.ε c.c c.ε c.w₀) = f p + c.ε :=
    GradientLikeStrip.f_landing hpC hfs hε hε hεR c.hc₁.le c.hc₂.le c.hlev hw0
  have hnf : morseNormalForm c.dp.hk (f p) c.y₀ = f p + c.ε := by
    rw [← hfland, c.dp.f_eq_nf_symm hlandLe]
    rfl
  have hpos0 : posPart c.dp.hk c.y₀ ≠ 0 :=
    ModelField.posPart_ne_zero_of_lt_nf c.dp.hk (c := f p) (by rw [hnf]; linarith)
  have hJ : ModelField.scaledNegativePart c.dp.hk c.y₀ = 0 := c.hzero
  have hneg0 : negPart c.dp.hk c.y₀ = 0 := by
    unfold ModelField.scaledNegativePart at hJ
    rcases smul_eq_zero.1 hJ with h | h
    · exact absurd (norm_eq_zero.1 h) hpos0
    · exact h
  have hnormpos : ‖posPart c.dp.hk c.y₀‖ = Real.sqrt (2 * c.ε) := by
    have h := hnf
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hneg0, norm_zero] at h
    have h2 : ‖posPart c.dp.hk c.y₀‖ ^ 2 = 2 * c.ε := by linarith
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have hse₁ : Real.sqrt (2 * c.ε) • c.e₁ = posPart c.dp.hk c.y₀ := by
    change Real.sqrt (2 * c.ε) • (Real.sqrt (2 * c.ε))⁻¹ • posPart c.dp.hk c.y₀ = _
    rw [smul_smul, mul_inv_cancel₀ hsq_pos.ne', one_smul]
  have he₁ : ‖c.e₁‖ = 1 := by
    change ‖(Real.sqrt (2 * c.ε))⁻¹ • posPart c.dp.hk c.y₀‖ = 1
    rw [norm_smul, norm_inv, hnormpos, Real.norm_eq_abs, abs_of_pos hsq_pos,
      inv_mul_cancel₀ hsq_pos.ne']
  have hy₀eq : c.y₀ = recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • c.e₁) := by
    calc c.y₀ = recombine c.dp.hk (negPart c.dp.hk c.y₀) (posPart c.dp.hk c.y₀) :=
          (DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose _ _).symm
      _ = _ := by rw [hneg0, hse₁]
  have hT₀pt : c.D.flow c.transitTime c.z₀ = c.dp.χ (recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • c.e₁)) := by
    rw [← hy₀eq, hχy₀, hland]
  have hpc : c.dp.χ (recombine c.dp.hk 0 ((0 : ℝ) • c.e₁)) = p := by
    rw [zero_smul, hrec0, c.dp.hχ0]
  have hqc : c.dq.χ (recombine c.dq.hk ((0 : ℝ) • c.u₀) 0) = q := by
    rw [zero_smul, hrec0, c.dq.hχ0]
  have hstab := flow_ray_stable c.D hfs hpC he₁ hsq_pos hsqp
  have hunst := flow_ray_unstable c.D hfs hqC hu₀ hsq_pos hsqq
  have hsqI : (0 : ℝ) ≤ Real.sqrt (2 * c.ε) := hsq_pos.le
  ext x
  constructor
  · rintro (hx | ⟨s, rfl⟩)
    · rcases hx with hx' | hx'
      · rw [mem_singleton_iff.1 hx']
        exact Or.inl (Or.inl ⟨0, left_mem_Icc.2 hsqI, hpc⟩)
      · rw [mem_singleton_iff.1 hx']
        exact Or.inr ⟨0, left_mem_Icc.2 hsqI, hqc⟩
    · rcases lt_or_ge s 0 with hs | hs
      · obtain ⟨t', ht', heq⟩ := hunst.1 (-s) (by linarith)
        refine Or.inr ⟨t', ⟨ht'.1.le, ht'.2⟩, ?_⟩
        exact heq.symm.trans (by rw [neg_neg, hz₀])
      · rcases le_or_gt s c.transitTime with hsT | hsT
        · exact Or.inl (Or.inr ⟨s, ⟨hs, hsT⟩, rfl⟩)
        · obtain ⟨t', ht', heq⟩ := hstab.1 (s - c.transitTime) (by linarith)
          refine Or.inl (Or.inl ⟨t', ⟨ht'.1.le, ht'.2⟩, ?_⟩)
          refine heq.symm.trans ?_
          rw [hT₀pt.symm, c.D.flow_flow]
          congr 1
          ring
  · rintro ((⟨t, ht, rfl⟩ | ⟨s, -, rfl⟩) | ⟨t, ht, rfl⟩)
    · rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        change c.dp.χ (recombine c.dp.hk 0 ((0 : ℝ) • c.e₁)) ∈ c.arc
        rw [hpc]
        exact c.p_mem_arc
      · obtain ⟨s, -, heq⟩ := hstab.2 t ⟨h0, ht.2⟩
        refine Or.inr ⟨c.transitTime + s, ?_⟩
        refine Eq.trans ?_ heq
        rw [hT₀pt.symm, c.D.flow_flow]
    · exact Or.inr ⟨s, rfl⟩
    · rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        change c.dq.χ (recombine c.dq.hk ((0 : ℝ) • c.u₀) 0) ∈ c.arc
        rw [hqc]
        exact c.q_mem_arc
      · obtain ⟨s, -, heq⟩ := hunst.2 t ⟨h0, ht.2⟩
        refine Or.inr ⟨-s, ?_⟩
        refine Eq.trans ?_ heq
        rw [hz₀]

theorem isCompact_arc : IsCompact c.arc ∧ c.arc ⊆ f ⁻¹' Ioo a' b' := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hε2 : 0 < 2 * c.ε := by linarith [c.hε]
  have hsqpos : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 hε2
  have hmn : ∀ {k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
      (b : EuclideanSpace ℝ (Fin (n - k))), a = 0 ∨ b = 0 →
      morseNorm n (recombine hk a b) = ‖a‖ + ‖b‖ := by
    intro k hk a b hab
    have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq hk a b
    have h0 : 0 ≤ morseNorm n (recombine hk a b) := ModelField.morseNorm_nonneg _
    rcases hab with rfl | rfl
    · rw [norm_zero, zero_add]
      rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
      exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h
    · rw [norm_zero, add_zero]
      rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
      exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h
  obtain ⟨y, hy, hyeq⟩ := c.hw₀.2
  have hy₀ : c.y₀ = y := by
    change c.dp.χ.symm (c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀) = y
    rw [← hyeq]
    exact c.dp.χ.left_inv (c.dp.hsrc y (le_of_lt hy))
  have hpos : ‖posPart c.dp.hk c.y₀‖ < c.dp.R := by
    rw [hy₀]
    have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      c.dp.hk y
    have h1 : ‖posPart c.dp.hk y‖ ^ 2 ≤ morseNorm n y ^ 2 := by
      rw [h]; nlinarith [norm_nonneg (negPart c.dp.hk y)]
    have h2 : ‖posPart c.dp.hk y‖ ≤ morseNorm n y :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (ModelField.morseNorm_nonneg _) two_ne_zero).1 h1
    exact lt_of_le_of_lt h2 hy
  have hpseg : ∀ t ∈ Icc 0 (Real.sqrt (2 * c.ε)),
      morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ≤ c.dp.R := by
    intro t ht
    rw [hmn c.dp.hk 0 (t • c.e₁) (Or.inl rfl), norm_zero, zero_add]
    have hte : ‖t • c.e₁‖ ≤ ‖posPart c.dp.hk c.y₀‖ := by
      rw [TransverseCancellingPair.e₁, smul_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ht.1 (inv_nonneg.2 hsqpos.le))]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [← div_eq_mul_inv]
      exact div_le_one_of_le₀ ht.2 hsqpos.le
    exact le_of_lt (lt_of_le_of_lt hte hpos)
  have hRq : Real.sqrt (2 * c.ε) < c.dq.R := by
    have hrm := c.D.hrm q (mem_pair_right p q)
    have hrmpos := c.D.rm_pos q (mem_pair_right p q)
    have h1 : 2 * c.ε < c.dq.R ^ 2 := by
      have : c.D.rm q (mem_pair_right p q) ^ 2 ≤ c.dq.R ^ 2 :=
        pow_le_pow_left₀ hrmpos.le hrm.2 2
      linarith [c.hrmq, c.hε]
    exact (Real.sqrt_lt' (by linarith [c.dq.R_pos])).2 h1
  have hu₀ : ‖c.u₀‖ ≤ 1 := by
    rw [TransverseCancellingPair.u₀, norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hqseg : ∀ t ∈ Icc 0 (Real.sqrt (2 * c.ε)),
      morseNorm n (recombine c.dq.hk (t • c.u₀) 0) ≤ c.dq.R := by
    intro t ht
    rw [hmn c.dq.hk (t • c.u₀) 0 (Or.inr rfl), norm_zero, add_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    have : t * ‖c.u₀‖ ≤ t := mul_le_of_le_one_right ht.1 hu₀
    linarith [ht.2]
  have hw0 : c.w₀ ≠ 0 := c.hw₀.1
  have hεRq : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have := pow_lt_pow_left₀ hRq hsqpos.le two_ne_zero
    rw [Real.sq_sqrt hε2.le] at this
    exact this.le
  have hz₀ : f c.z₀ ∈ Ioo a' b' := by
    have hm := c.dq.morseNorm_sphereParam_le c.hε.le hεRq hw0
    exact c.D.inStrip q (mem_pair_right p q) ⟨_, c.dq.mem_ball_of_le hm, rfl⟩
  have hland : c.D.flow c.transitTime c.z₀ = c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀ := by
    change c.D.flow c.transitTime c.z₀ = c.D.flow (c.c - (f p + c.ε)) (c.D.flow (f q - c.ε - c.c) c.z₀)
    rw [c.D.flow_flow]
    congr 1
    unfold TransverseCancellingPair.transitTime
    ring
  have hT₀ : f (c.D.flow c.transitTime c.z₀) ∈ Ioo a' b' := by
    rw [hland, ← hyeq]
    exact c.D.inStrip p (mem_pair_left p q) ⟨y, c.dp.mem_ball_of_le (le_of_lt hy), rfl⟩
  refine ⟨?_, ?_⟩
  · rw [c.arc_eq]
    refine ((IsCompact.image_of_continuousOn isCompact_Icc ?_).union
      (isCompact_Icc.image (c.D.continuous_flow_curve c.z₀))).union
      (IsCompact.image_of_continuousOn isCompact_Icc ?_)
    · refine c.dp.χ.continuousOn.comp ?_ (fun t ht => c.dp.hsrc _ (hpseg t ht))
      exact ((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
        c.dp.hk).comp (continuous_const.prodMk (continuous_id.smul continuous_const))).continuousOn
    · refine c.dq.χ.continuousOn.comp ?_ (fun t ht => c.dq.hsrc _ (hqseg t ht))
      exact ((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
        c.dq.hk).comp ((continuous_id.smul continuous_const).prodMk continuous_const)).continuousOn
  · rw [c.arc_eq]
    rintro x ((⟨t, ht, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact c.D.inStrip p (mem_pair_left p q) ⟨_, c.dp.mem_ball_of_le (hpseg t ht), rfl⟩
    · have h1 : f (c.D.flow s c.z₀) ≤ f c.z₀ := GradientLikeStrip.f_flow_le hfs c.z₀ hs.1
      have h2 : f (c.D.flow c.transitTime c.z₀) ≤ f (c.D.flow s c.z₀) :=
        GradientLikeStrip.f_flow_antitone hfs c.z₀ hs.2
      exact ⟨lt_of_lt_of_le hT₀.1 h2, lt_of_le_of_lt h1 hz₀.2⟩
    · exact c.D.inStrip q (mem_pair_right p q) ⟨_, c.dq.mem_ball_of_le (hqseg t ht), rfl⟩

theorem arc_cases {x : M} (hx : x ∈ c.arc) :
    x = p ∨ x = q ∨
      (∃ t : ℝ, 0 < t ∧ t ^ 2 < 2 * c.ε ∧ x = c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) ∨
      (∃ t : ℝ, 0 < t ∧ t ^ 2 < 2 * c.ε ∧ x = c.dq.χ (recombine c.dq.hk (t • c.u₀) 0)) ∨
      ∃ s ∈ Icc 0 (f q - f p - 2 * c.ε), x = c.D.flow s c.z₀ ∧ f x = f q - c.ε - s := by
  have hq : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hp : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hε : 0 < c.ε := c.hε
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hRq : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have h1 := (c.D.hrm q hq).2
    have h2 := c.D.rm_pos q hq
    have h3 := c.hrmq
    nlinarith
  have hw0ne : c.w₀ ≠ 0 := c.hw₀.1
  obtain ⟨hpa, hpb⟩ := c.D.f_mem_Ioo p hp
  obtain ⟨hqa, hqb⟩ := c.D.f_mem_Ioo q hq
  have hc₁ := c.hc₁
  have hc₂ := c.hc₂
  have hT₀ : c.transitTime = f q - f p - 2 * c.ε := rfl
  have hT₀nn : 0 ≤ c.transitTime := by rw [hT₀]; linarith
  have hsq : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
  have hrec0 : ∀ {k : ℕ} (hk : k ≤ n), recombine hk 0 0 = (0 : Fin n → ℝ) := by
    intro k hk
    funext i
    unfold recombine
    split_ifs <;> rfl
  have hfz₀ : f c.z₀ = f q - c.ε :=
    c.dq.f_chart_of_mem_leftModelSphere hRq (c.dq.sphereParam_mem_leftModelSphere hε.le hw0ne)
  have hz₀ : c.dq.χ (recombine c.dq.hk (Real.sqrt (2 * c.ε) • c.u₀) 0) = c.z₀ := by
    change _ = c.dq.χ (c.dq.sphereParam c.ε c.w₀)
    unfold MorseNormalChart.sphereParam TransverseCancellingPair.u₀
    rw [smul_smul, div_eq_mul_inv]
  have hmid : ∀ s ∈ Icc 0 c.transitTime, f (c.D.flow s c.z₀) = f q - c.ε - s := by
    intro s hs
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels (D := c.D) hfs (x := c.z₀) (T := c.transitTime)
      (by rw [hfz₀]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfz₀, hT₀]; exact ⟨by linarith, by linarith⟩) (by
        intro y hy
        rw [hfz₀, hT₀, uIcc_of_ge (by linarith)] at hy
        exact c.hlev y ⟨by linarith [hy.1], hy.2⟩) s (by rw [uIcc_of_le hT₀nn]; exact hs)
    rw [h, hfz₀]
  have hland : c.D.landing p hq c.ε c.c c.ε c.w₀ = c.D.flow c.transitTime c.z₀ := by
    unfold GradientLikeStrip.landing
    rw [c.D.flow_flow]
    congr 1
    rw [hT₀]; ring
  have hpend : c.dp.χ (recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • c.e₁)) =
      c.D.flow c.transitTime c.z₀ := by
    obtain ⟨y', hy', hy'eq⟩ := c.hw₀.2
    have hy₀ : c.y₀ = y' := by
      change c.dp.χ.symm (c.D.landing p hq c.ε c.c c.ε c.w₀) = y'
      rw [← hy'eq]
      exact c.dp.χ.left_inv (c.dp.hsrc y' (le_of_lt hy'))
    have hfl : f (c.D.landing p hq c.ε c.c c.ε c.w₀) = f p + c.ε :=
      GradientLikeStrip.f_landing hp hfs hε hε hRq hc₁.le hc₂.le c.hlev hw0ne
    have hnf : morseNormalForm c.dp.hk (f p) y' = f p + c.ε := by
      rw [← c.dp.hnorm y' (le_of_lt hy'), ← hfl, ← hy'eq]
    have hpos : posPart c.dp.hk y' ≠ 0 :=
      ModelField.posPart_ne_zero_of_lt_nf c.dp.hk (by rw [hnf]; linarith)
    have hJ : ModelField.scaledNegativePart c.dp.hk c.y₀ = 0 := c.hzero
    rw [hy₀] at hJ
    unfold ModelField.scaledNegativePart at hJ
    have hneg : negPart c.dp.hk y' = 0 := by
      rcases smul_eq_zero.1 hJ with h | h
      · exact absurd (norm_eq_zero.1 h) hpos
      · exact h
    have he : Real.sqrt (2 * c.ε) • c.e₁ = posPart c.dp.hk y' := by
      unfold TransverseCancellingPair.e₁
      rw [smul_smul, mul_inv_cancel₀ hsq.ne', one_smul, hy₀]
    rw [he, ← hneg, DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose, hy'eq, hland]
  have hmidT : f (c.D.flow c.transitTime c.z₀) = f q - c.ε - c.transitTime :=
    hmid c.transitTime ⟨hT₀nn, le_rfl⟩
  rw [c.arc_eq] at hx
  rcases hx with (⟨t, ht, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨t, ht, rfl⟩
  · beta_reduce
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · left
      rw [← h0, zero_smul, hrec0, c.dp.hχ0]
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · right; right; right; right
        refine ⟨c.transitTime, ⟨hT₀nn, le_of_eq hT₀⟩, ?_, ?_⟩
        · rw [h1, hpend]
        · rw [h1, hpend, hmidT]
      · right; right; left
        exact ⟨t, h0, (Real.lt_sqrt ht.1).1 h1, rfl⟩
  · beta_reduce
    right; right; right; right
    exact ⟨s, ⟨hs.1, hT₀ ▸ hs.2⟩, rfl, hmid s hs⟩
  · beta_reduce
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · right; left
      rw [← h0, zero_smul, hrec0, c.dq.hχ0]
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · right; right; right; right
        refine ⟨0, ⟨le_rfl, hT₀ ▸ hT₀nn⟩, ?_, ?_⟩
        · rw [h1, hz₀, c.D.flow_zero]
        · rw [h1, hz₀, hfz₀, sub_zero]
      · right; right; right; left
        exact ⟨t, h0, (Real.lt_sqrt ht.1).1 h1, rfl⟩

theorem arc_level_inj {x y : M} (hx : x ∈ range (fun t : ℝ => c.D.flow t c.z₀))
    (hy : y ∈ range (fun t : ℝ => c.D.flow t c.z₀)) (hxy : f x = f y) : x = y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  by_cases hz : c.z₀ ∈ ({p, q} : Finset M)
  · simp only [c.D.flow_crit hz]
  have hnc : ∀ u, c.D.flow u c.z₀ ∉ ({p, q} : Finset M) := by
    intro u hu
    apply hz
    have h1 := c.D.flow_crit hu (-u)
    rw [c.D.flow_neg_flow] at h1
    rwa [← h1] at hu
  have key : ∀ s t : ℝ, s < t → f (c.D.flow s c.z₀) = f (c.D.flow t c.z₀) → False := by
    intro s t hst hfst
    have hanti := GradientLikeStrip.f_flow_antitone (D := c.D) hfs c.z₀
    have hconst : ∀ u ∈ Icc s t, f (c.D.flow u c.z₀) = f (c.D.flow s c.z₀) := by
      intro u hu
      have h1 : f (c.D.flow u c.z₀) ≤ f (c.D.flow s c.z₀) := hanti hu.1
      have h2 : f (c.D.flow t c.z₀) ≤ f (c.D.flow u c.z₀) := hanti hu.2
      linarith
    have hm : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
    have hev : (fun u => f (c.D.flow u c.z₀)) =ᶠ[𝓝 ((s + t) / 2)]
        fun _ => f (c.D.flow s c.z₀) :=
      Filter.eventually_of_mem (Icc_mem_nhds hm.1 hm.2) hconst
    have hd1 := GradientLikeStrip.hasDerivAt_f_flow (D := c.D) hfs c.z₀ ((s + t) / 2)
    have hd2 : HasDerivAt (fun u => f (c.D.flow u c.z₀)) 0 ((s + t) / 2) :=
      (hasDerivAt_const ((s + t) / 2) (f (c.D.flow s c.z₀))).congr_of_eventuallyEq hev
    have h0 := hd1.unique hd2
    have hmem : c.D.flow ((s + t) / 2) c.z₀ ∈ f ⁻¹' Icc a' b' :=
      Ioo_subset_Icc_self (c.isCompact_arc.2 (Or.inr ⟨(s + t) / 2, rfl⟩))
    have hneg := c.D.neg _ hmem (hnc ((s + t) / 2))
    change dfV I f c.D.V (c.D.flow ((s + t) / 2) c.z₀) < 0 at hneg
    linarith
  rcases lt_trichotomy s t with hst | rfl | hst
  · exact (key s t hst hxy).elim
  · rfl
  · exact (key t s hst hxy.symm).elim

theorem p_ray_mem_arc {t : ℝ} (ht : 0 < t) (ht' : t ^ 2 ≤ 3 * c.ε) :
    c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈ c.arc := by
  have hε := c.hε
  have hS0 : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
  have hSsq : Real.sqrt (2 * c.ε) ^ 2 = 2 * c.ε := Real.sq_sqrt (by linarith)
  have hseg : ∀ τ ∈ Icc 0 (Real.sqrt (2 * c.ε)),
      c.dp.χ (recombine c.dp.hk 0 (τ • c.e₁)) ∈ c.arc := by
    intro τ hτ
    rw [c.arc_eq]
    exact Or.inl (Or.inl ⟨τ, hτ, rfl⟩)
  by_cases htS : t ≤ Real.sqrt (2 * c.ε)
  · exact hseg t ⟨ht.le, htS⟩
  rw [not_le] at htS
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  obtain ⟨hw0, hland⟩ := c.hw₀
  have hw0' : c.w₀ ≠ 0 := hw0
  have hRq : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have h1 := c.D.rm_pos q (mem_pair_right p q)
    have h2 := pow_le_pow_left₀ h1.le (c.D.hrm q (mem_pair_right p q)).2 2
    have h3 := c.hrmq
    linarith
  have hfL : f (c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀) = f p + c.ε :=
    GradientLikeStrip.f_landing (D := c.D) (mem_pair_left p q) hsmooth hε hε hRq c.hc₁.le c.hc₂.le c.hlev hw0'
  have hland2 : c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀ ∈
      c.dp.χ '' {y | morseNorm n y ≤ c.dp.R} :=
    image_mono (fun y (hy : morseNorm n y < c.dp.R) => le_of_lt hy) hland
  have hnf : morseNormalForm c.dp.hk (f p) c.y₀ = f p + c.ε := by
    rw [← hfL, c.dp.f_eq_nf_symm hland2]
    rfl
  have hv0 : posPart c.dp.hk c.y₀ ≠ 0 :=
    ModelField.posPart_ne_zero_of_lt_nf c.dp.hk (by rw [hnf]; linarith)
  have hu0 : negPart c.dp.hk c.y₀ = 0 := by
    have hz := c.hzero
    have hz' : ‖posPart c.dp.hk c.y₀‖ • negPart c.dp.hk c.y₀ = 0 := hz
    rcases smul_eq_zero.1 hz' with h | h
    · exact absurd (norm_eq_zero.1 h) hv0
    · exact h
  have hvsq : ‖posPart c.dp.hk c.y₀‖ ^ 2 = 2 * c.ε := by
    have := hnf
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hu0, norm_zero] at this
    linarith
  have hvn : ‖posPart c.dp.hk c.y₀‖ = Real.sqrt (2 * c.ε) := by
    rw [← hvsq, Real.sqrt_sq (norm_nonneg _)]
  have he : ‖c.e₁‖ = 1 := by
    rw [TransverseCancellingPair.e₁, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hS0, hvn,
      inv_mul_cancel₀ hS0.ne']
  have htr : t < c.D.rm p (mem_pair_left p q) := by
    have h1 := c.D.rm_pos p (mem_pair_left p q)
    have h2 := c.hrmp
    nlinarith
  obtain ⟨s, -, hs⟩ := (flow_ray_stable c.D hsmooth (mem_pair_left p q) he ht htr).2
    (Real.sqrt (2 * c.ε)) ⟨hS0, htS.le⟩
  have hmem := c.flow_mem_arc (-s) (hseg _ ⟨hS0.le, le_rfl⟩)
  rw [← hs, GradientLikeStrip.flow_flow, add_neg_cancel, GradientLikeStrip.flow_zero] at hmem
  exact hmem

theorem q_ray_mem_arc {t : ℝ} (ht : 0 < t) (ht' : t ^ 2 ≤ 3 * c.ε) :
    c.dq.χ (recombine c.dq.hk (t • c.u₀) 0) ∈ c.arc := by
  have hw₀ne : c.w₀ ≠ 0 := c.hw₀.1
  have hE : c.dq.toE c.w₀ ≠ 0 := c.dq.toE_ne_zero hw₀ne
  have hu₀ : ‖c.u₀‖ = 1 := by
    change ‖‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀‖ = 1
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hE)
  have hε := c.hε
  have hrm := c.hrmq
  have hrm0 := c.D.rm_pos q (mem_pair_right p q)
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ Real.sqrt (2 * c.ε) →
      c.dq.χ (recombine c.dq.hk (s • c.u₀) 0) ∈ c.arc := by
    intro s hs0 hs1
    rw [c.arc_eq]
    exact Or.inr ⟨s, ⟨hs0, hs1⟩, rfl⟩
  by_cases hle : t ≤ Real.sqrt (2 * c.ε)
  · exact hseg t ht.le hle
  · push Not at hle
    have htr : t < c.D.rm q (mem_pair_right p q) := by
      have h1 : t ^ 2 < c.D.rm q (mem_pair_right p q) ^ 2 := by linarith
      exact (pow_lt_pow_iff_left₀ ht.le hrm0.le two_ne_zero).1 h1
    have hsq : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
    obtain ⟨s, -, hs⟩ := (flow_ray_unstable c.D c.hf.smooth (mem_pair_right p q) hu₀ ht htr).2
      (Real.sqrt (2 * c.ε)) ⟨hsq, hle.le⟩
    have hmem := c.flow_mem_arc s (hseg _ hsq.le le_rfl)
    rw [← hs, c.D.flow_flow_neg] at hmem
    exact hmem

theorem mem_arc_of_unstable {x : M} (hcap : x ∈ c.D.captured p (mem_pair_left p q))
    {y : Fin n → ℝ} (hy : 2 * morseNorm n y ^ 2 < c.D.rm q (mem_pair_right p q) ^ 2)
    (hv : posPart c.dq.hk y = 0) (hu : negPart c.dq.hk y ≠ 0) {T : ℝ}
    (hT : x = c.D.flow T (c.dq.χ y)) : x ∈ c.arc := by
  have hp : p ∈ ({p, q} : Finset M) := mem_pair_left p q
  have hq : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hε := c.hε
  have hpI := c.D.f_mem_Ioo p hp
  have hqI := c.D.f_mem_Ioo q hq
  have hc₁ := c.hc₁
  have hc₂ := c.hc₂
  have hrmq := c.hrmq
  have hrmp := c.hrmp
  have hrmqpos := c.D.rm_pos q hq
  have hrmppos := c.D.rm_pos p hp
  have hRq := (c.D.hrm q hq).2
  have hRp := (c.D.hrm p hp).2
  have hs2pos : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith)
  have hs2sq : Real.sqrt (2 * c.ε) ^ 2 = 2 * c.ε := Real.sq_sqrt (by linarith)
  have hs2q : Real.sqrt (2 * c.ε) < c.D.rm q hq := (Real.sqrt_lt' hrmqpos).2 (by linarith)
  have hs2p : Real.sqrt (2 * c.ε) < c.D.rm p hp := (Real.sqrt_lt' hrmppos).2 (by linarith)
  set u := negPart c.dq.hk y with hudef
  have hyu : y = recombine c.dq.hk u 0 := by
    rw [← hv]; exact (DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dq.hk y).symm
  have hmn0 : 0 ≤ morseNorm n y := le_trans (norm_nonneg _) (DifferentialGeometry.Topology.Morse.CellAttachment.norm_negPart_le_morseNorm c.dq.hk y)
  have hmn : morseNorm n y < c.D.rm q hq := by nlinarith
  have hurm : ‖u‖ < c.D.rm q hq := lt_of_le_of_lt (DifferentialGeometry.Topology.Morse.CellAttachment.norm_negPart_le_morseNorm c.dq.hk y) hmn
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  set e := ‖u‖⁻¹ • u with hedef
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hupos.ne']
  have hue : ‖u‖ • e = u := by
    rw [hedef, smul_smul, mul_inv_cancel₀ hupos.ne', one_smul]
  set w := (EuclideanSpace.equiv (Fin c.dq.k) ℝ) u with hwdef
  have htoE : c.dq.toE w = u := (EuclideanSpace.equiv (Fin c.dq.k) ℝ).symm_apply_apply _
  have hw0 : w ≠ 0 := fun h => hu ((EuclideanSpace.equiv (Fin c.dq.k) ℝ).map_eq_zero_iff.1 h)
  have hsp : c.dq.sphereParam c.ε w = recombine c.dq.hk (Real.sqrt (2 * c.ε) • e) 0 := by
    rw [MorseNormalChart.sphereParam, htoE, hedef, smul_smul, div_eq_mul_inv]
  set z := c.dq.χ (c.dq.sphereParam c.ε w) with hzdef
  obtain ⟨σ, hσ⟩ : ∃ σ, x = c.D.flow σ z := by
    rcases le_or_gt ‖u‖ (Real.sqrt (2 * c.ε)) with h | h
    · obtain ⟨s, -, hs⟩ := (flow_ray_unstable c.D hfs hq he hs2pos hs2q).2 ‖u‖ ⟨hupos, h⟩
      refine ⟨-s + T, ?_⟩
      rw [hT, hyu, ← hue, ← hs, hzdef, hsp, c.D.flow_flow]
    · obtain ⟨s, -, hs⟩ := (flow_ray_unstable c.D hfs hq he hupos hurm).2 (Real.sqrt (2 * c.ε))
        ⟨hs2pos, h.le⟩
      refine ⟨s + T, ?_⟩
      have hs' : c.dq.χ y = c.D.flow s z := by
        rw [hzdef, hsp, ← hs, c.D.flow_flow_neg, hue, ← hyu]
      rw [hT, hs', c.D.flow_flow]
  have hzcap : z ∈ c.D.captured p hp := (c.D.flow_mem_captured_iff σ).1 (hσ ▸ hcap)
  have hfz : f z = f q - c.ε :=
    c.dq.f_chart_of_mem_leftModelSphere (by nlinarith)
      (c.dq.sphereParam_mem_leftModelSphere hε.le hw0)
  obtain ⟨T1, hT1⟩ := GradientLikeStrip.mem_captured_iff_eventually.1 hzcap
  obtain ⟨y1, ⟨hy1n, hy1u⟩, hy1⟩ := hT1 T1 le_rfl
  set v1 := posPart c.dp.hk y1 with hv1def
  have hy1eq : y1 = recombine c.dp.hk 0 v1 := by
    rw [← hy1u]; exact (DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dp.hk y1).symm
  have hv1 : v1 ≠ 0 := by
    intro h0
    have hy10 : y1 = 0 := by
      rw [hy1eq, h0, ← ModelField.recombineL_apply]; exact map_zero _
    have hpz : c.D.flow T1 z = p := by rw [← hy1, hy10]; exact c.dp.hχ0
    have hz' : z = p := by
      rw [← c.D.flow_neg_flow z T1, hpz, c.D.flow_crit hp]
    rw [hz'] at hfz
    linarith
  have hv1pos : 0 < ‖v1‖ := norm_pos_iff.2 hv1
  have hv1rm : ‖v1‖ < c.D.rm p hp :=
    lt_of_le_of_lt (DifferentialGeometry.Topology.Morse.CellAttachment.posPart_norm_le_morseNorm c.dp.hk y1) hy1n
  set e' := ‖v1‖⁻¹ • v1 with he'def
  have he' : ‖e'‖ = 1 := by
    rw [he'def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv1pos.ne']
  have hve : ‖v1‖ • e' = v1 := by
    rw [he'def, smul_smul, mul_inv_cancel₀ hv1pos.ne', one_smul]
  set L' := c.dp.χ (recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • e')) with hL'def
  obtain ⟨σ', hσ'⟩ : ∃ σ', c.D.flow σ' z = L' := by
    rcases le_or_gt (Real.sqrt (2 * c.ε)) ‖v1‖ with h | h
    · obtain ⟨s, -, hs⟩ := (flow_ray_stable c.D hfs hp he' hv1pos hv1rm).2 (Real.sqrt (2 * c.ε))
        ⟨hs2pos, h⟩
      refine ⟨T1 + s, ?_⟩
      rw [← c.D.flow_flow, ← hy1, hy1eq, ← hve, hs]
    · obtain ⟨s, -, hs⟩ := (flow_ray_stable c.D hfs hp he' hs2pos hs2p).2 ‖v1‖ ⟨hv1pos, h.le⟩
      refine ⟨T1 + -s, ?_⟩
      rw [← c.D.flow_flow, ← hy1, hy1eq, ← hve, ← hs, c.D.flow_neg_flow]
  have hL'mem : recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • e') ∈ c.dp.rightModelSphere c.ε := by
    refine ⟨DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine _ _ _, ?_⟩
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine, norm_smul, he',
      mul_one, Real.norm_of_nonneg hs2pos.le, hs2sq]
  have hfL' : f L' = f p + c.ε := c.dp.f_chart_of_mem_rightModelSphere (by nlinarith) hL'mem
  have hinj : ∀ s₁ s₂ : ℝ, s₁ < s₂ → f (c.D.flow s₁ z) = f p + c.ε →
      f (c.D.flow s₂ z) = f p + c.ε → False := by
    intro s₁ s₂ h12 h1 h2
    have hunit : dfV I f c.D.V (c.D.flow s₁ z) = -1 :=
      c.D.dfV_eq_neg_one_of_mem_unitRegion
        ⟨by rw [h1]; exact ⟨by linarith [hpI.1], by linarith [hqI.2]⟩,
          fun p' hp' => c.hlev _ (by rw [h1]; exact ⟨le_rfl, by linarith⟩) p' hp'⟩
    obtain ⟨t, ht, ht0⟩ :=
      ((GradientLikeStrip.eventually_f_flow_lt hfs hunit).and
        (Ioo_mem_nhdsGT (sub_pos.2 h12))).exists
    have hanti := GradientLikeStrip.f_flow_antitone (D := c.D) hfs z
      (show s₁ + t ≤ s₂ by linarith [ht0.2])
    rw [c.D.flow_flow] at ht
    simp only at hanti
    linarith
  set TL := (f q - c.ε - c.c) + (c.c - (f p + c.ε)) with hTL
  have hland : c.D.landing p hq c.ε c.c c.ε w = c.D.flow TL z := by
    rw [GradientLikeStrip.landing, c.D.flow_flow]
  have hfland : f (c.D.flow TL z) = f p + c.ε := by
    rw [← hland]
    exact GradientLikeStrip.f_landing hp hfs hε hε (by nlinarith) hc₁.le hc₂.le c.hlev hw0
  have hLL : c.D.landing p hq c.ε c.c c.ε w = L' := by
    rw [hland]
    rcases lt_trichotomy TL σ' with h | h | h
    · exact (hinj _ _ h hfland (hσ' ▸ hfL')).elim
    · rw [h, hσ']
    · exact (hinj _ _ h (hσ' ▸ hfL') hfland).elim
  have hnL' : morseNorm n (recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • e')) < c.dp.R := by
    have h := c.dp.morseNorm_sq_of_mem_rightModelSphere hL'mem
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) (by rw [h]; nlinarith)
  have hdom : w ∈ c.D.sardDom p hq c.ε c.c c.ε hp := ⟨hw0, by rw [mem_preimage, hLL]; exact ⟨_, hnL', rfl⟩⟩
  have hzero : c.D.sardMap p hq c.ε c.c c.ε hp w = 0 := by
    rw [GradientLikeStrip.sardMap, hLL, hL'def, c.dp.χ.left_inv (c.dp.hsrc _ hnL'.le),
      ModelField.scaledNegativePart, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine, smul_zero]
  obtain ⟨t, ht, hwt⟩ := c.huniq w hdom hzero
  have hsp0 : c.dq.sphereParam c.ε (t • c.w₀) = c.dq.sphereParam c.ε c.w₀ := by
    have hlin : c.dq.toE (t • c.w₀) = t • c.dq.toE c.w₀ := by
      exact (EuclideanSpace.equiv (Fin c.dq.k) ℝ).symm.map_smul t c.w₀
    have hcoef : (Real.sqrt (2 * c.ε) / ‖c.dq.toE (t • c.w₀)‖) • c.dq.toE (t • c.w₀) =
        (Real.sqrt (2 * c.ε) / ‖c.dq.toE c.w₀‖) • c.dq.toE c.w₀ := by
      rw [hlin, norm_smul, Real.norm_of_nonneg ht.le, smul_smul]
      have hsc : Real.sqrt (2 * c.ε) / (t * ‖c.dq.toE c.w₀‖) * t =
          Real.sqrt (2 * c.ε) / ‖c.dq.toE c.w₀‖ := by
        rw [mul_comm t, ← div_div, div_mul_cancel₀ _ ht.ne']
      rw [hsc]
    rw [MorseNormalChart.sphereParam, MorseNormalChart.sphereParam, hcoef]
  have hzz : z = c.z₀ := by
    rw [hzdef, TransverseCancellingPair.z₀, hwt, hsp0]
  rw [hσ, hzz]
  exact Or.inr ⟨σ, rfl⟩

theorem dichotomy (x : M) (hx : f x ∈ Icc a' b') (hxΓ : x ∉ c.arc) :
    x ∈ c.D.bottom ∨ ∃ t ≤ 0, b' < f (c.D.flow t x) := by
  classical
  have hfs := c.hf.smooth
  have hpq : p ≠ q := fun h => (lt_irrefl (f p)) (h ▸ c.hlt)
  have hxc : x ∉ ({p, q} : Finset M) := by
    intro hmem
    rcases Finset.mem_insert.1 hmem with h | h
    · exact hxΓ (h ▸ c.p_mem_arc)
    · exact hxΓ ((Finset.mem_singleton.1 h) ▸ c.q_mem_arc)
  have hεr : ∀ r (hr : r ∈ ({p, q} : Finset M)),
      (c.D.chart r hr).r₀ ^ 2 < 2 * c.ε ∧ 8 * c.ε < c.D.rm r hr ^ 2 := by
    intro r hr
    rcases Finset.mem_insert.1 hr with h | h
    · subst h; exact ⟨c.hr₀p, c.hrmp⟩
    · rw [Finset.mem_singleton] at h; subst h; exact ⟨c.hr₀q, c.hrmq⟩
  by_contra hcon
  rw [not_or, not_exists] at hcon
  obtain ⟨hbot, hnt'⟩ := hcon
  have hnt : ∀ t ≤ 0, f (c.D.flow t x) ≤ b' := fun t ht => not_lt.1 fun h => hnt' t ⟨ht, h⟩
  rcases GradientLikeStrip.trichotomy hfs c.hε hεr hx with hb | ⟨r, hr, hcap⟩
  · exact hbot hb
  have hge : f r ≤ f x := by
    obtain ⟨T, hT⟩ := GradientLikeStrip.mem_captured_iff_eventually.1 hcap
    obtain ⟨y, ⟨hy1, hy2⟩, hyx⟩ := hT (max T 0) (le_max_left _ _)
    have hle : f (c.D.flow (max T 0) x) ≤ f x := by
      have := GradientLikeStrip.f_flow_antitone (D := c.D) hfs x (le_max_right T 0)
      simpa using this
    have hlev : f ((c.D.chart r hr).χ y) = f r + (1 / 2) *
        (‖posPart (c.D.chart r hr).hk y‖ ^ 2 - ‖negPart (c.D.chart r hr).hk y‖ ^ 2) := by
      rw [(c.D.chart r hr).hnorm y (hy1.le.trans (c.D.hrm r hr).2), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
    rw [hy2, hyx] at hlev
    have : f r ≤ f (c.D.flow (max T 0) x) := by
      rw [hlev, norm_zero]; nlinarith [sq_nonneg ‖posPart (c.D.chart r hr).hk y‖]
    linarith
  obtain ⟨r', hr', hxr', hcl, hback⟩ :=
    CrossField.exists_backward_clusterPt c.hf c.D hx hxc hnt
  have hrp : r = p := by
    rcases Finset.mem_insert.1 hr with h | h
    · exact h
    · rw [Finset.mem_singleton] at h
      subst h
      exfalso
      rcases Finset.mem_insert.1 hr' with h' | h'
      · subst h'; linarith [c.hlt]
      · rw [Finset.mem_singleton] at h'; subst h'; linarith
  have hr'q : r' = q := by
    rcases Finset.mem_insert.1 hr' with h' | h'
    · subst h'; subst hrp; exact absurd hxr' (not_lt.2 hge)
    · exact Finset.mem_singleton.1 h'
  subst hrp
  subst hr'q
  have hq := mem_pair_right r r'
  have hrm := c.D.rm_pos r' hq
  have hU : (c.D.chart r' hq).χ '' {y | morseNorm n y < c.D.rm r' hq / 2} ∈ 𝓝 r' :=
    ((c.D.chart r' hq).isOpen_image_of_lt (by
      linarith [c.D.rm_lt_R' r' hq])).mem_nhds ((c.D.chart r' hq).p_mem_image_lt (by linarith))
  obtain ⟨t, ⟨y, hy, hyx⟩, ht⟩ :=
    ((hcl.frequently hU).and_eventually (eventually_ge_atTop 0)).exists
  have hy' : 2 * morseNorm n y ^ 2 < c.D.rm r' hq ^ 2 := by
    have h0 := ModelField.morseNorm_nonneg y
    simp only [mem_ofPred_eq] at hy
    nlinarith
  have hlevb : ∀ s, 0 ≤ s → f (c.D.flow (-s) ((c.D.chart r' hq).χ y)) < f r' := by
    intro s hs
    rw [hyx, GradientLikeStrip.flow_flow]
    have := hback (t + s) (by linarith)
    rwa [show -t + -s = -(t + s) by ring]
  have hv := CrossField.posPart_eq_zero_of_backward c.D hfs hq hy' hlevb
  have hu : negPart (c.D.chart r' hq).hk y ≠ 0 := by
    intro hu0
    have h0 := hlevb 0 le_rfl
    rw [neg_zero, GradientLikeStrip.flow_zero,
      (c.D.chart r' hq).hnorm y (by
        have := ModelField.morseNorm_nonneg y
        simp only [mem_ofPred_eq] at hy
        linarith [(c.D.hrm r' hq).2]),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hv, hu0] at h0
    simp at h0
  have hxT : x = c.D.flow t ((c.D.chart r' hq).χ y) := by
    rw [hyx, GradientLikeStrip.flow_flow_neg]
  exact hxΓ (c.mem_arc_of_unstable hcap hy' hv hu hxT)

end TransverseCancellingPair

end CrossField

end

end DifferentialGeometry.Topology
