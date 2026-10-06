module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerSard

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

section Moves

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_multiShift {m : ℕ} {t s : Fin m → ℝ} (ht : StrictMono t) (hs : StrictMono s)
    {a₃ b₃ : ℝ} (hts : ∀ i, t i ∈ Ioo a₃ b₃ ∧ s i ∈ Ioo a₃ b₃) :
    ∃ σ > 0, ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ x, 0 < deriv ρ x) ∧
      (∀ x, x ∉ Ioo a₃ b₃ → ρ x = x) ∧
      ∀ i, ∀ x ∈ Icc (t i - σ) (t i + σ), ρ x = x + (s i - t i) := by
  have gap : ∀ a b A B : ℝ, a < b → A < B → ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧
      (∀ x, 0 < deriv G x) ∧ (∀ x, x ≤ a → G x = x + (A - a)) ∧
      (∀ x, b ≤ x → G x = x + (B - b)) := by
    intro a b A B hab hAB
    set e : ℝ := (B - b) - (A - a) with he
    set M : ℝ := max 0 (-e) with hM
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMe : -e ≤ M := le_max_right _ _
    have hMlt : M < b - a := max_lt (by linarith) (by rw [he]; linarith)
    set δ : ℝ := (b - a - M) / 4 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set φ : ℝ → ℝ := fun u =>
      Real.smoothTransition ((u - a) / δ) * Real.smoothTransition ((b - u) / δ) with hφ
    have hφc : ContDiff ℝ ∞ φ := by
      apply ContDiff.mul
      · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)
      · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ)
    have hφcont : Continuous φ := hφc.continuous
    have hφ0 : ∀ u, 0 ≤ φ u := fun u =>
      mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have hφ1 : ∀ u, φ u ≤ 1 := fun u =>
      (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one).trans (by norm_num)
    have hφa : ∀ u, u ≤ a → φ u = 0 := fun u hu => by
      simp only [hφ]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le), zero_mul]
    have hφb : ∀ u, b ≤ u → φ u = 0 := fun u hu => by
      simp only [hφ]
      rw [Real.smoothTransition.zero_of_nonpos (x := (b - u) / δ)
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le), mul_zero]
    have hφmid : ∀ u, a + δ ≤ u → u ≤ b - δ → φ u = 1 := fun u h1 h2 => by
      simp only [hφ]
      rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
      · rw [le_div_iff₀ hδpos]; linarith
      · rw [le_div_iff₀ hδpos]; linarith
    have hII : ∀ x y, IntervalIntegrable φ MeasureTheory.volume x y := fun x y =>
      hφcont.intervalIntegrable x y
    set I : ℝ := ∫ u in a..b, φ u with hI
    have hIge : b - a - 2 * δ ≤ I := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals (hII a (a + δ)) (hII (a + δ) b)
      have h2 := intervalIntegral.integral_add_adjacent_intervals (hII (a + δ) (b - δ))
        (hII (b - δ) b)
      have h3 : 0 ≤ ∫ u in a..(a + δ), φ u :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => hφ0 u)
      have h4 : 0 ≤ ∫ u in (b - δ)..b, φ u :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => hφ0 u)
      have h5 : ∫ u in (a + δ)..(b - δ), φ u = (b - δ) - (a + δ) := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
        · simp
        · intro u hu
          rw [uIcc_of_le (by linarith)] at hu
          exact hφmid u hu.1 hu.2
      linarith
    have hIM : M < I := by linarith
    have hIpos : 0 < I := by linarith
    have hc : -1 < e / I := by rw [lt_div_iff₀ hIpos]; linarith
    have hF : ContDiff ℝ ∞ (fun x => ∫ u in a..x, φ u) := by
      refine contDiff_infty_iff_deriv.2 ⟨fun x =>
        (hφcont.integral_hasStrictDerivAt a x).hasDerivAt.differentiableAt, ?_⟩
      rw [show deriv (fun x => ∫ u in a..x, φ u) = φ from funext (Continuous.deriv_integral φ hφcont a)]
      exact hφc
    have hFa : ∀ x, x ≤ a → ∫ u in a..x, φ u = 0 := fun x hx => by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro u hu
        rw [uIcc_of_ge hx] at hu
        exact hφa u hu.2
    have hFb : ∀ x, b ≤ x → ∫ u in a..x, φ u = I := fun x hx => by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hII a b) (hII b x)]
      rw [intervalIntegral.integral_congr (a := b) (b := x) (g := fun _ => (0 : ℝ)) ?_]
      · simp [hI]
      · intro u hu
        rw [uIcc_of_le hx] at hu
        exact hφb u hu.1
    refine ⟨fun x => x + (A - a) + e / I * ∫ u in a..x, φ u, ?_, ?_, ?_, ?_⟩
    · exact (contDiff_id.add contDiff_const).add (contDiff_const.mul hF)
    · intro x
      have hd : HasDerivAt (fun x => x + (A - a) + e / I * ∫ u in a..x, φ u)
          (1 + e / I * φ x) x :=
        ((hasDerivAt_id' x).add_const (A - a)).add
          ((hφcont.integral_hasStrictDerivAt a x).hasDerivAt.const_mul (e / I))
      rw [hd.deriv]
      by_cases hc0 : 0 ≤ e / I
      · nlinarith [mul_nonneg hc0 (hφ0 x)]
      · have : e / I * 1 ≤ e / I * φ x := mul_le_mul_of_nonpos_left (hφ1 x) (by linarith)
        linarith
    · intro x hx
      simp only
      rw [hFa x hx]; ring
    · intro x hx
      simp only
      rw [hFb x hx, div_mul_cancel₀ e hIpos.ne', he]; ring
  have main : ∀ m : ℕ, ∀ (t s : Fin m → ℝ), StrictMono t → StrictMono s →
      ∀ a b A B : ℝ, a < b → A < B → (∀ i, t i ∈ Ioo a b ∧ s i ∈ Ioo A B) →
      ∃ σ > 0, ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ x, 0 < deriv ρ x) ∧
        (∀ x, x ≤ a → ρ x = x + (A - a)) ∧ (∀ x, b ≤ x → ρ x = x + (B - b)) ∧
        ∀ i, ∀ x ∈ Icc (t i - σ) (t i + σ), ρ x = x + (s i - t i) := by
    intro m
    induction m with
    | zero =>
      intro t s _ _ a b A B hab hAB _
      obtain ⟨G, hG, hG', hGa, hGb⟩ := gap a b A B hab hAB
      exact ⟨1, one_pos, G, hG, hG', hGa, hGb, fun i => i.elim0⟩
    | succ m ih =>
      intro t s ht hs a b A B hab hAB hts
      have htt : ∀ j : Fin m, t 0 < t j.succ := fun j => ht (Fin.succ_pos j)
      have hss : ∀ j : Fin m, s 0 < s j.succ := fun j => hs (Fin.succ_pos j)
      obtain ⟨⟨ha0, hb0⟩, ⟨hA0, hB0⟩⟩ := hts 0
      have hev : ∀ᶠ σ₁ in 𝓝 (0 : ℝ), σ₁ < t 0 - a ∧ σ₁ < s 0 - A ∧ σ₁ < b - t 0 ∧
          σ₁ < B - s 0 ∧ ∀ j : Fin m, σ₁ < t j.succ - t 0 ∧ σ₁ < s j.succ - s 0 :=
        (eventually_lt_nhds (by linarith)).and ((eventually_lt_nhds (by linarith)).and
          ((eventually_lt_nhds (by linarith)).and ((eventually_lt_nhds (by linarith)).and
          (Filter.eventually_all.2 fun j => (eventually_lt_nhds (by linarith [htt j])).and
            (eventually_lt_nhds (by linarith [hss j]))))))
      obtain ⟨σ₁, ⟨h1, h2, h3, h4, h5⟩, hσ₁⟩ :=
        ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
      have hσ₁' : (0 : ℝ) < σ₁ := hσ₁
      obtain ⟨G, hG, hG', hGa, hGb⟩ := gap a (t 0 - σ₁) A (s 0 - σ₁) (by linarith) (by linarith)
      obtain ⟨σ', hσ', ρ', hρ', hρ'', hρ'a, hρ'b, hρ'w⟩ := ih (fun j => t j.succ)
        (fun j => s j.succ) (ht.comp Fin.strictMono_succ) (hs.comp Fin.strictMono_succ)
        (t 0 + σ₁) b (s 0 + σ₁) B (by linarith) (by linarith)
        (fun j => ⟨⟨by linarith [(h5 j).1], (hts j.succ).1.2⟩,
          ⟨by linarith [(h5 j).2], (hts j.succ).2.2⟩⟩)
      have hGr : ∀ x, t 0 - σ₁ ≤ x → G x = x + (s 0 - t 0) := fun x hx => by
        rw [hGb x hx]; ring
      have hρ'l : ∀ x, x ≤ t 0 + σ₁ → ρ' x = x + (s 0 - t 0) := fun x hx => by
        rw [hρ'a x hx]; ring
      refine ⟨min σ₁ σ', lt_min hσ₁' hσ', fun x => G x + ρ' x - x - (s 0 - t 0),
        ?_, ?_, ?_, ?_, ?_⟩
      · exact ((hG.add hρ').sub contDiff_id).sub contDiff_const
      · intro x
        have hd : HasDerivAt (fun x => G x + ρ' x - x - (s 0 - t 0))
            (deriv G x + deriv ρ' x - 1) x :=
          ((((hG.differentiable (by simp)) x).hasDerivAt.add
            ((hρ'.differentiable (by simp)) x).hasDerivAt).sub (hasDerivAt_id' x)).sub_const _
        rw [hd.deriv]
        rcases lt_or_ge x (t 0 + σ₁) with hx | hx
        · have : deriv ρ' x = 1 := by
            rw [Filter.EventuallyEq.deriv_eq (f := fun y => y + (s 0 - t 0))]
            · simp
            · filter_upwards [eventually_lt_nhds hx] with y hy using hρ'l y hy.le
          linarith [hG' x]
        · have : deriv G x = 1 := by
            rw [Filter.EventuallyEq.deriv_eq (f := fun y => y + (s 0 - t 0))]
            · simp
            · filter_upwards [eventually_gt_nhds (show t 0 - σ₁ < x by linarith)] with y hy
                using hGr y hy.le
          linarith [hρ'' x]
      · intro x hx
        simp only
        rw [hGa x hx, hρ'l x (by linarith)]; ring
      · intro x hx
        simp only
        rw [hGr x (by linarith), hρ'b x hx]; ring
      · intro i
        have hm1 := min_le_left σ₁ σ'
        have hm2 := min_le_right σ₁ σ'
        refine Fin.cases ?_ (fun j => ?_) i
        · intro x hx
          simp only
          rw [hGr x (by linarith [hx.1]), hρ'l x (by linarith [hx.2])]; ring
        · intro x hx
          simp only
          rw [hGr x (by linarith [hx.1, (h5 j).1]),
            hρ'w j x ⟨by linarith [hx.1], by linarith [hx.2]⟩]; ring
  by_cases hab : a₃ < b₃
  · obtain ⟨σ, hσ, ρ, h1, h2, h3, h4, h5⟩ := main m t s ht hs a₃ b₃ a₃ b₃ hab hab hts
    refine ⟨σ, hσ, ρ, h1, h2, fun x hx => ?_, h5⟩
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hx | hx
    · rw [h3 x hx]; ring
    · rw [h4 x hx]; ring
  · have hm : ∀ i : Fin m, False := fun i => hab ((hts i).1.1.trans (hts i).1.2)
    exact ⟨1, one_pos, id, contDiff_id, fun x => by simp, fun x _ => rfl,
      fun i => (hm i).elim⟩

theorem eq_of_unit_of_mfderiv_eq {g : M → ℝ} {crit' : Finset M}
    (D : GradientLikeStrip I f a b crit) (D' : GradientLikeStrip I g a b crit') {φ : M → ℝ}
    (hφ : ∀ x, D'.V x = φ x • D.V x) {x : M} (hx : f x ∈ Icc a b) (hgx : g x ∈ Icc a b)
    (hd : mfderiv I 𝓘(ℝ, ℝ) g x = mfderiv I 𝓘(ℝ, ℝ) f x)
    (hD : ∀ p hp, x ∉ D.smallBall p hp) (hD' : ∀ p hp, x ∉ D'.smallBall p hp) :
    D'.V x = D.V x := by
  have _ : T2Space M := ‹_›
  have _ : I.Boundaryless := ‹_›
  have h1 := D.unit x hx hD
  have h2 := D'.unit x hgx hD'
  have e : (mfderiv I 𝓘(ℝ, ℝ) g x) (D.V x) = (mfderiv I 𝓘(ℝ, ℝ) f x) (D.V x) :=
    DFunLike.congr_fun hd (D.V x)
  have h3 : (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (D'.V x)) =
      φ x * (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (D.V x)) := by
    rw [hφ x, map_smul]
    change φ x * @id ℝ ((mfderiv I 𝓘(ℝ, ℝ) g x) (D.V x)) =
      φ x * @id ℝ ((mfderiv I 𝓘(ℝ, ℝ) f x) (D.V x))
    rw [e]
  rw [h3, h1] at h2
  have hφ1 : φ x = 1 := by linarith
  rw [hφ x, hφ1, one_smul]

theorem exists_cutoff_shrunk [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {ε r' : ℝ} (hε : 0 < ε)
    (hD : ∀ r hr, (D.chart r hr).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm r hr ^ 2 ∧
      (D.chart r hr).r₀ < r')
    {a₂ b₂ : ℝ} (ha₂ : a ≤ a₂) (hb₂ : b₂ ≤ b) (hab₂ : a₂ < b₂)
    (hsep : ∀ r hr, f r ∉ Ioo a₂ b₂ →
      f r + (D.chart r hr).R ^ 2 / 2 + ε < a₂ ∨ b₂ + ε < f r - (D.chart r hr).R ^ 2 / 2)
    (hin : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      a₂ + ε < f r - (D.chart r hr).R ^ 2 / 2 ∧ f r + (D.chart r hr).R ^ 2 / 2 + ε < b₂)
    (P₁ : Set M)
    (hnocommon : ∀ r hr s hs, r ∉ P₁ → s ∈ P₁ → f r ∈ Ioo a₂ b₂ → f s ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart s hs).χ '' {y | morseNorm n y < r'})
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ (μ : M → ℝ) (ρr : ∀ p ∈ crit, ℝ) (Ds : GradientLikeStrip I f a b crit),
      (∀ p hp, (D.chart p hp).r₀ < ρr p hp ∧ ρr p hp ≤ r' ∧ ρr p hp ^ 2 ≤ 2 * ε) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a₂ b₂) ∧ (∀ x, μ x ∈ Icc 0 1) ∧
      (∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0) ∧
      (∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (Ds.V x) = 0) ∧
      (∀ p hp, p ∉ P₁ → f p ∈ Ioo a₂ b₂ →
        ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < ρr p hp}, μ x = 0) ∧
      (∀ p hp, p ∈ P₁ → f p ∈ Ioo a₂ b₂ →
        ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < ρr p hp}, μ x = 1) ∧
      (∀ p hp, (Ds.chart p hp).χ = (D.chart p hp).χ ∧ (Ds.chart p hp).k = (D.chart p hp).k ∧
        (Ds.chart p hp).R = (D.chart p hp).R ∧ (Ds.chart p hp).R' = (D.chart p hp).R' ∧
        (Ds.chart p hp).r₀ ≤ (D.chart p hp).r₀ ∧ (Ds.chart p hp).r₀ ≤ ρ₀ ∧
        4 * (Ds.chart p hp).r₀ < ρr p hp) ∧
      (∀ p hp, Ds.rm p hp = D.rm p hp) ∧
      (∀ x, x ∉ D.closedSmallBalls → Ds.V x = D.V x) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ x, Ds.V x = φ x • D.V x := by
  classical
  obtain ⟨c, hc, hcε, hcne⟩ : ∃ c ∈ Ioo a₂ b₂,
      (∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → (f p < c → f p + ε < c) ∧ (c < f p → c < f p - ε)) ∧
      (∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → f p ≠ c) := by
    by_cases hex : ∃ p ∈ crit, f p ∈ Ioo a₂ b₂
    · obtain ⟨q, hq, hqb⟩ := hex
      have hRq := (hin q hq hqb)
      have hRq2 : 0 ≤ (D.chart q hq).R ^ 2 := sq_nonneg _
      refine ⟨a₂ + ε / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
      · intro p hp hpb
        have hRp := hin p hp hpb
        have hRp2 : 0 < (D.chart p hp).R ^ 2 := pow_pos (D.chart p hp).R_pos 2
        have hRp3 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
          pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
        have hRp4 := (hD p hp).2.1
        exact ⟨fun h => absurd h (by linarith), fun _ => by linarith⟩
      · intro p hp hpb
        have hRp := hin p hp hpb
        have hRp2 : 0 < (D.chart p hp).R ^ 2 := pow_pos (D.chart p hp).R_pos 2
        intro h; linarith
    · have hex : ∀ p ∈ crit, f p ∉ Ioo a₂ b₂ := fun p hp hpb => hex ⟨p, hp, hpb⟩
      refine ⟨(a₂ + b₂) / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
      · intro p hp hpb; exact absurd hpb (hex p hp)
      · intro p hp hpb; exact absurd hpb (hex p hp)
  obtain ⟨μ, ρr, hρr, hμs, hμI, hμV, hμ0, hμ1⟩ :=
    exists_trajectoryCutoff' hf.smooth D ha₂ hb₂ P₁ᶜ P₁
      (fun p _ _ => by by_cases h : p ∈ P₁; exacts [Or.inr h, Or.inl h])
      (fun p h0 h1 => h0 h1) hc hε
      (fun p hp => ⟨(hD p hp).1, by linarith [(hD p hp).2.1]⟩)
      (fun p hp hpb => by
        have hR2 : 0 ≤ (D.chart p hp).R ^ 2 := sq_nonneg _
        rcases hsep p hp hpb with h | h
        · left; linarith
        · right; linarith)
      hcε hcne (fun _ _ => r') (fun p hp => (hD p hp).2.2)
      (fun p hp q hq h0 h1 hpb hqb => hnocommon p hp q hq h0 h1 hpb hqb)
  let gmin : M → ℝ := fun p =>
    if hp : p ∈ crit then min (D.chart p hp).r₀ (ρr p hp / 2) else 1
  have hgpos : ∀ p, 0 < gmin p := by
    intro p
    by_cases hp : p ∈ crit
    · simp only [gmin, hp, dite_true]
      exact lt_min (D.chart p hp).hr₀ (by linarith [(hρr p hp).1, (D.chart p hp).hr₀])
    · simp only [gmin, hp, dite_false]; norm_num
  let S₀ : Finset ℝ := insert ρ₀ (crit.image gmin)
  have hSne : S₀.Nonempty := ⟨ρ₀, Finset.mem_insert_self _ _⟩
  set m := S₀.min' hSne with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact hρ₀
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 h; exact hgpos p
  have hmρ₀ : m ≤ ρ₀ := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hmg : ∀ p hp, m ≤ min (D.chart p hp).r₀ (ρr p hp / 2) := by
    intro p hp
    have := Finset.min'_le S₀ (gmin p) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem gmin hp))
    simpa only [gmin, hp, dite_true] using this
  have hρpos : 0 < m / 2 := by linarith
  have hr : 0 < m / 2 / 2 := by linarith
  have hleD : ∀ p hp, m / 2 ≤ (D.chart p hp).r₀ := fun p hp => by
    linarith [hmg p hp, min_le_left (D.chart p hp).r₀ (ρr p hp / 2)]
  have key : ∀ S : Finset M, S ⊆ crit → ∃ E : GradientLikeStrip I f a b crit,
      (∀ p hp, (E.chart p hp).χ = (D.chart p hp).χ ∧ (E.chart p hp).k = (D.chart p hp).k ∧
        (E.chart p hp).R = (D.chart p hp).R ∧ (E.chart p hp).R' = (D.chart p hp).R') ∧
      (∀ p hp, p ∈ S → (E.chart p hp).r₀ = m / 2 / 2) ∧
      (∀ p hp, p ∉ S → (E.chart p hp).r₀ = (D.chart p hp).r₀) ∧
      (∀ p hp, E.rm p hp = D.rm p hp) ∧
      (∀ x, (∀ p hp, p ∈ S →
        x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) →
        E.V x = D.V x) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ x, E.V x = φ x • D.V x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨D, fun p hp => ⟨rfl, rfl, rfl, rfl⟩, fun p hp h => absurd h (Finset.notMem_empty p),
        fun p hp _ => rfl, fun p hp => rfl, fun x _ => rfl,
        ⟨fun _ => 1, continuous_const, ⟨1, 1, one_pos, fun _ => ⟨le_rfl, le_rfl⟩⟩,
          fun x => (one_smul ℝ _).symm⟩⟩
    | insert q S hqS ih =>
      intro hsub
      have hq : q ∈ crit := hsub (Finset.mem_insert_self q S)
      obtain ⟨E, hE1, hE2, hE3, hE4, hE5, φ, hφc, ⟨m₁, M₁, hm₁, hφb⟩, hφV⟩ :=
        ih ((Finset.subset_insert q S).trans hsub)
      have hleq : m / 2 / 2 ≤ (E.chart q hq).r₀ := by
        rw [hE3 q hq hqS]; linarith [hleD q hq]
      have hr₀ : 0 < (E.chart q hq).r₀ := (E.chart q hq).hr₀
      let g : (Fin n → ℝ) → ℝ := fun y =>
        ModelField.theta (m / 2 / 2) y / ModelField.theta (E.chart q hq).r₀ y
      let h : (Fin n → ℝ) → ℝ := fun y => g y - 1
      have hgc : ContDiff ℝ ∞ g :=
        (ModelField.contDiff_theta hr).div (ModelField.contDiff_theta hr₀)
          fun y => (ModelField.theta_pos hr₀ y).ne'
      have hhc : ContDiff ℝ ∞ h := hgc.sub contDiff_const
      have hgpos' : ∀ y, 0 < g y := fun y =>
        div_pos (ModelField.theta_pos hr y) (ModelField.theta_pos hr₀ y)
      have hh0 : ∀ y, (E.chart q hq).r₀ / 2 ≤ morseNorm n y → h y = 0 := by
        intro y hy
        have ht : ModelField.theta (m / 2 / 2) y = ModelField.theta (E.chart q hq).r₀ y := by
          rw [ModelField.theta_eq hr (by linarith), ModelField.theta_eq hr₀ hy]
        change g y - 1 = 0
        simp only [g]
        rw [ht, div_self (ModelField.theta_pos hr₀ y).ne', sub_self]
      set K : Set (Fin n → ℝ) := {y | morseNorm n y ≤ (E.chart q hq).r₀ / 2} with hKdef
      have hKc : IsCompact K := isCompact_morseNorm_le _
      have hKb : K ⊆ Metric.ball 0 (E.chart q hq).R' :=
        GradientLikeStrip.half_r₀_ball_subset (D := E) (p := q) (hp := hq)
      have hhK : ∀ y ∉ K, h y = 0 := fun y hy => hh0 y (le_of_lt (not_le.1 hy))
      have h0K : (0 : Fin n → ℝ) ∈ K := by
        change morseNorm n 0 ≤ _
        rw [morseNorm_zero]; linarith
      obtain ⟨y₁, -, hy₁⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hgc.continuous.continuousOn
      obtain ⟨y₂, -, hy₂⟩ := hKc.exists_isMaxOn ⟨0, h0K⟩ hgc.continuous.continuousOn
      let ψ : M → ℝ := fun x => 1 + (E.chart q hq).pushFun h x
      have hψc : Continuous ψ :=
        continuous_const.add (MorseNormalChart.contMDiff_pushFun hhc hKc hKb hhK).continuous
      have hψb : ∀ x, min 1 (g y₁) ≤ ψ x ∧ ψ x ≤ max 1 (g y₂) := by
        intro x
        by_cases hx : x ∈ (E.chart q hq).χ '' K
        · obtain ⟨y, hyK, rfl⟩ := hx
          have hψy : ψ ((E.chart q hq).χ y) = g y := by
            change 1 + (E.chart q hq).pushFun h ((E.chart q hq).χ y) = g y
            rw [MorseNormalChart.pushFun_apply_chart h (hKb hyK)]
            change 1 + (g y - 1) = g y
            ring
          rw [hψy]
          exact ⟨(min_le_right _ _).trans (hy₁ hyK), (hy₂ hyK).trans (le_max_right _ _)⟩
        · have hψx : ψ x = 1 := by
            change 1 + (E.chart q hq).pushFun h x = 1
            rw [MorseNormalChart.pushFun_eq_zero_of_notMem_image hhK hx, add_zero]
          rw [hψx]
          exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hψV : ∀ x, GradientLikeStrip.shrunkV (D := E) q hq (m / 2 / 2) x = ψ x • E.V x := by
        intro x
        by_cases hx : x ∈ (E.chart q hq).χ '' K
        · obtain ⟨y, hyK, rfl⟩ := hx
          have hyB : y ∈ Metric.ball (0 : Fin n → ℝ) (E.chart q hq).R' := hKb hyK
          have hyrm : morseNorm n y < E.rm q hq :=
            lt_of_le_of_lt (show morseNorm n y ≤ _ from hyK)
              (GradientLikeStrip.half_r₀_lt_rm (D := E) (p := q) (hp := hq))
          have hshr : GradientLikeStrip.shrinkY (D := E) q hq (m / 2 / 2) y =
              h y • ModelField.modelField (E.chart q hq).k (E.chart q hq).r₀ y := by
            have := (ModelField.theta_pos hr₀ y).ne'
            have e : (g y - 1) * ModelField.theta (E.chart q hq).r₀ y =
                ModelField.theta (m / 2 / 2) y - ModelField.theta (E.chart q hq).r₀ y := by
              simp only [g]
              field_simp
            change ModelField.theta (m / 2 / 2) y • ModelField.modelDesc (E.chart q hq).k y -
              ModelField.theta (E.chart q hq).r₀ y • ModelField.modelDesc (E.chart q hq).k y =
              (g y - 1) • (ModelField.theta (E.chart q hq).r₀ y •
                ModelField.modelDesc (E.chart q hq).k y)
            rw [smul_smul, e, sub_smul]
          have hVy := GradientLikeStrip.V_chart_eq (D := E) q hq hyrm
          have hpush : (mfderiv 𝓘(ℝ, Fin n → ℝ) I (E.chart q hq).χ y)
              (GradientLikeStrip.shrinkY (D := E) q hq (m / 2 / 2) y) =
              h y • E.V ((E.chart q hq).χ y) := by
            rw [hshr, hVy]
            exact ContinuousLinearMap.map_smul _ _ _
          rw [GradientLikeStrip.shrunkV, GradientLikeStrip.addPush_apply,
            MorseNormalChart.push_apply_chart _ hyB, hpush]
          change E.V ((E.chart q hq).χ y) + h y • E.V ((E.chart q hq).χ y) =
            (1 + (E.chart q hq).pushFun h ((E.chart q hq).χ y)) • E.V ((E.chart q hq).χ y)
          rw [MorseNormalChart.pushFun_apply_chart h hyB, add_smul, one_smul]
        · rw [GradientLikeStrip.shrunkV_of_notMem_image hr hleq hx]
          have hψx : ψ x = 1 := by
            change 1 + (E.chart q hq).pushFun h x = 1
            rw [MorseNormalChart.pushFun_eq_zero_of_notMem_image hhK hx, add_zero]
          rw [hψx, one_smul]
      have hm₂ : 0 < min 1 (g y₁) := lt_min one_pos (hgpos' y₁)
      have hψpos : ∀ x, 0 < ψ x := fun x => hm₂.trans_le (hψb x).1
      have hφpos : ∀ x, 0 < φ x := fun x => hm₁.trans_le (hφb x).1
      refine ⟨GradientLikeStrip.shrinkAt (D := E) hf.smooth hr hleq, fun p hp => ?_,
        fun p hp hpS => ?_, fun p hp hpS => ?_, fun p hp => ?_, fun x hx => ?_,
        ⟨fun x => ψ x * φ x, hψc.mul hφc,
          ⟨min 1 (g y₁) * m₁, max 1 (g y₂) * M₁, mul_pos hm₂ hm₁, fun x => ⟨?_, ?_⟩⟩,
          fun x => ?_⟩⟩
      · rw [GradientLikeStrip.shrinkAt_chart_χ, GradientLikeStrip.shrinkAt_chart_k,
          GradientLikeStrip.shrinkAt_chart_R, GradientLikeStrip.shrinkAt_chart_R']
        exact hE1 p hp
      · by_cases hpq : p = q
        · subst hpq; exact GradientLikeStrip.shrinkAt_chart_r₀_self hf.smooth hr hleq
        · rw [GradientLikeStrip.shrinkAt_chart_r₀_of_ne hf.smooth hr hleq hp hpq]
          exact hE2 p hp (Finset.mem_of_mem_insert_of_ne hpS hpq)
      · have hpq : p ≠ q := fun h' => hpS (h' ▸ Finset.mem_insert_self q S)
        rw [GradientLikeStrip.shrinkAt_chart_r₀_of_ne hf.smooth hr hleq hp hpq]
        exact hE3 p hp fun h' => hpS (Finset.mem_insert_of_mem h')
      · rw [GradientLikeStrip.shrinkAt_rm]; exact hE4 p hp
      · rw [GradientLikeStrip.shrinkAt_V,
          GradientLikeStrip.shrunkV_of_notMem_image hr hleq ?_]
        · exact hE5 x fun p hp hpS => hx p hp (Finset.mem_insert_of_mem hpS)
        · rw [(hE1 q hq).1, hE3 q hq hqS]
          exact hx q hq (Finset.mem_insert_self q S)
      · exact mul_le_mul (hψb x).1 (hφb x).1 hm₁.le (hψpos x).le
      · exact mul_le_mul (hψb x).2 (hφb x).2 (hφpos x).le
          (one_pos.le.trans (le_max_left _ _))
      · rw [GradientLikeStrip.shrinkAt_V, hψV x, hφV x, smul_smul]
  obtain ⟨Ds, hDs, hDsr₀, -, hDsrm, hDsV, φ, hφc, hφb, hφ⟩ := key crit le_rfl
  refine ⟨μ, ρr, Ds, hρr, hμs, hμI, hμV, ?_, hμ0, hμ1, ?_, hDsrm, ?_, φ, hφc, hφb, hφ⟩
  · intro x hx
    rw [hφ x, map_smul, hμV x hx, smul_zero]
  · intro p hp
    have h1 := hmg p hp
    have h2 := min_le_left (D.chart p hp).r₀ (ρr p hp / 2)
    have h3 := min_le_right (D.chart p hp).r₀ (ρr p hp / 2)
    obtain ⟨e1, e2, e3, e4⟩ := hDs p hp
    refine ⟨e1, e2, e3, e4, ?_, ?_, ?_⟩ <;> rw [hDsr₀ p hp hp] <;> linarith
  · intro x hx
    apply hDsV
    intro p hp _ hmem
    apply (D.notMem_closedSmallBalls_iff.1 hx) p hp
    obtain ⟨y, hy, rfl⟩ := hmem
    refine ⟨y, ?_, rfl⟩
    have hy' : morseNorm n y ≤ (D.chart p hp).r₀ / 2 := hy
    change morseNorm n y ≤ (D.chart p hp).r₀
    linarith [(D.chart p hp).hr₀]
theorem exists_move [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε r' : ℝ} (hε : 0 < ε) (hr'ε : r' ^ 2 < ε)
    (hD : ∀ r hr, (D.chart r hr).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm r hr ^ 2 ∧
      (D.chart r hr).r₀ < r')
    {a₂ b₂ a₃ b₃ : ℝ} (ha₂ : a ≤ a₂) (hb₂ : b₂ ≤ b) (h₃ : a₂ < a₃ ∧ a₃ < b₃ ∧ b₃ < b₂)
    (hreg : ∀ x, f x = a₂ ∨ f x = b₂ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hsep : ∀ r hr, f r ∉ Ioo a₂ b₂ →
      f r + (D.chart r hr).R ^ 2 / 2 + ε < a₂ ∨ b₂ + ε < f r - (D.chart r hr).R ^ 2 / 2)
    (hin : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      a₂ + ε < f r - (D.chart r hr).R ^ 2 / 2 ∧ f r + (D.chart r hr).R ^ 2 / 2 + ε < b₂)
    (P₁ : Set M)
    (hnocommon : ∀ r hr s hs, r ∉ P₁ → s ∈ P₁ → f r ∈ Ioo a₂ b₂ → f s ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart s hs).χ '' {y | morseNorm n y < r'})
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρ' : ∀ t, 0 < deriv ρ t)
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) {σ : ℝ} (hσ : 0 < σ)
    (hρtr : ∀ s ∈ crit, s ∈ P₁ → f s ∈ Ioo a₂ b₂ →
      ∀ t ∈ Icc (f s - σ) (f s + σ), ρ t = t + (ρ (f s) - f s)) :
    ∃ g : M → ℝ, ∃ D' : GradientLikeStrip I g a b crit, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      (∀ s ∈ crit, s ∈ P₁ → f s ∈ Ioo a₂ b₂ → g s = ρ (f s)) ∧
      (∀ r ∈ crit, (r ∉ P₁ ∨ f r ∉ Ioo a₂ b₂) → g r = f r) ∧
      (∀ r hr, (D'.chart r hr).χ = (D.chart r hr).χ ∧ (D'.chart r hr).k = (D.chart r hr).k ∧
        (D'.chart r hr).r₀ ≤ (D.chart r hr).r₀ ∧ (D'.chart r hr).R ≤ (D.chart r hr).R ∧
        (D'.chart r hr).R' = (D.chart r hr).R' ∧
        (D'.chart r hr).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm r hr ^ 2) ∧
      (∀ r hr, f r ∉ Ioo a₂ b₂ →
        (D'.chart r hr).R = (D.chart r hr).R ∧ D'.rm r hr = D.rm r hr) ∧
      (∀ r hr, (r ∉ P₁ ∨ f r ∉ Ioo a₂ b₂) → ∀ y, morseNorm n y < D.rm r hr →
        (negPart (D.chart r hr).hk y = 0 ∨ posPart (D.chart r hr).hk y = 0) →
        mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart r hr).χ.symm ((D.chart r hr).χ y)
          (D'.V ((D.chart r hr).χ y)) =
            ModelField.modelField (D.chart r hr).k (D'.chart r hr).r₀ y) ∧
      ∀ x, x ∉ D.closedSmallBalls → f x ∈ Icc a b →
        (f x ∉ Ioo a₃ b₃ ∨ ∃ t, (∀ s ∈ uIcc 0 t, f (D.flow s x) ∈ Ioo a₂ b₂) ∧
          ∃ r hr, r ∉ P₁ ∧ f r ∈ Ioo a₂ b₂ ∧ D.flow t x ∈ D.smallBall r hr) →
        g x = f x ∧ D'.V x = D.V x := by
  classical
  have hfs := hf.smooth
  have hfc : Continuous f := hfs.continuous
  obtain ⟨ha₃, hab₃, hb₃⟩ := h₃
  have hab₂ : a₂ < b₂ := by linarith
  have hBo : IsOpen (f ⁻¹' Ioo a₂ b₂) := isOpen_Ioo.preimage hfc
  have hr'rm : ∀ r hr, r' < D.rm r hr := fun r hr => by
    have hr'0 : 0 < r' := (D.chart r hr).hr₀.trans (hD r hr).2.2
    apply lt_of_pow_lt_pow_left₀ 2 (D.rm_pos r hr).le
    linarith [(hD r hr).2.1]
  obtain ⟨τ, hτ, hτle⟩ := exists_pos_le_forall_finset crit.attach
    (fun r => (D.chart r.1 r.2).r₀) (fun r _ => (D.chart r.1 r.2).hr₀)
  have hs2σ : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.2 (by linarith)
  set ρ₀ : ℝ := min (min (τ / 8) (Real.sqrt (2 * σ) / 16)) (Real.sqrt ε) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (lt_min (by linarith) (by linarith)) (Real.sqrt_pos.2 hε)
  have hρ₀τ : ρ₀ ≤ τ / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀σ : ρ₀ ≤ Real.sqrt (2 * σ) / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀ε : ρ₀ ^ 2 ≤ ε := by
    have h1 : ρ₀ ≤ Real.sqrt ε := min_le_right _ _
    calc ρ₀ ^ 2 ≤ Real.sqrt ε ^ 2 := pow_le_pow_left₀ hρ₀.le h1 2
      _ = ε := Real.sq_sqrt hε.le
  have hρ₀r₀ : ∀ r hr, 8 * ρ₀ ≤ (D.chart r hr).r₀ := fun r hr => by
    have := hτle ⟨r, hr⟩ (Finset.mem_attach _ _)
    simp only at this
    linarith
  obtain ⟨μ, ρr, Ds, hρr, hμ, hμ01, hμV, hμVs, hμ0, hμ1, hDsc, hDsrm, hDsV, φs, -, -, hφs⟩ :=
    exists_cutoff_shrunk hf D hε hD ha₂ hb₂ hab₂ hsep hin P₁ hnocommon hρ₀
  have hDsχ : ∀ r hr, (Ds.chart r hr).χ = (D.chart r hr).χ := fun r hr => (hDsc r hr).1
  have hDsk : ∀ r hr, (Ds.chart r hr).k = (D.chart r hr).k := fun r hr => (hDsc r hr).2.1
  have hDsR : ∀ r hr, (Ds.chart r hr).R = (D.chart r hr).R := fun r hr => (hDsc r hr).2.2.1
  have hDsR' : ∀ r hr, (Ds.chart r hr).R' = (D.chart r hr).R' := fun r hr =>
    (hDsc r hr).2.2.2.1
  have hDsr₀ : ∀ r hr, (Ds.chart r hr).r₀ ≤ (D.chart r hr).r₀ := fun r hr =>
    (hDsc r hr).2.2.2.2.1
  have hDsρ₀ : ∀ r hr, (Ds.chart r hr).r₀ ≤ ρ₀ := fun r hr => (hDsc r hr).2.2.2.2.2.1
  have hρrpos : ∀ r hr, 0 < ρr r hr := fun r hr => (D.chart r hr).hr₀.trans (hρr r hr).1
  have hρrrm : ∀ r hr, ρr r hr < D.rm r hr := fun r hr => (hρr r hr).2.1.trans_lt (hr'rm r hr)
  have hρrR : ∀ r hr, ρr r hr ≤ (D.chart r hr).R := fun r hr =>
    (hρrrm r hr).le.trans (D.hrm r hr).2
  have hρrR' : ∀ r hr, ρr r hr ≤ (D.chart r hr).R' := fun r hr =>
    (hρrrm r hr).le.trans (D.rm_lt_R' r hr).le
  have hball_open : ∀ r hr, IsOpen ((D.chart r hr).χ '' {z | morseNorm n z < ρr r hr}) :=
    fun r hr => (D.chart r hr).isOpen_image_of_lt (hρrR' r hr)
  have hρmono : StrictMono ρ := strictMono_of_deriv_pos hρ'
  have hρa₂ : ρ a₂ = a₂ := hρid a₂ (fun h => by linarith [h.1])
  have hρb₂ : ρ b₂ = b₂ := hρid b₂ (fun h => by linarith [h.2])
  have hρmaps : MapsTo ρ (Ioo a₂ b₂) (Ioo a₂ b₂) := fun t ht =>
    ⟨hρa₂ ▸ hρmono ht.1, hρb₂ ▸ hρmono ht.2⟩
  have hμcrit : ∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → ∀ᶠ x in 𝓝 p, μ x = μ p := by
    intro p hp hpI
    have hpm := (D.chart p hp).p_mem_image_lt (hρrpos p hp)
    filter_upwards [(hball_open p hp).mem_nhds hpm] with x hx
    by_cases hP : p ∈ P₁
    · rw [hμ1 p hp hP hpI x hx, hμ1 p hp hP hpI p hpm]
    · rw [hμ0 p hp hP hpI x hx, hμ0 p hp hP hpI p hpm]
  obtain ⟨-, -, hmod, hstrip, hcritIff, hidxEq, hval, -⟩ :=
    rearrange' hf ha₂ hab₂ hb₂ hreg Ds hcrit μ hμ hμ01 hμVs hμcrit ρ hρ hρ' hρid ⟨ha₃, hb₃⟩
      hρmaps
  set Rn : ∀ r ∈ crit, ℝ := fun r hr => if f r ∈ Ioo a₂ b₂ then
    min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) else (D.chart r hr).R with hRndef
  set rmn : ∀ r ∈ crit, ℝ := fun r hr => if f r ∈ Ioo a₂ b₂ then
    min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) else D.rm r hr with hrmndef
  have hRnI : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      Rn r hr = min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) := fun r hr h => by
    simp only [hRndef, ite_eq_left h]
  have hRnO : ∀ r hr, f r ∉ Ioo a₂ b₂ → Rn r hr = (D.chart r hr).R := fun r hr h => by
    simp only [hRndef, ite_eq_right h]
  have hrmnI : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      rmn r hr = min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) := fun r hr h => by
    simp only [hrmndef, ite_eq_left h]
  have hrmnO : ∀ r hr, f r ∉ Ioo a₂ b₂ → rmn r hr = D.rm r hr := fun r hr h => by
    simp only [hrmndef, ite_eq_right h]
  have hmin4 : ∀ r hr, 4 * ρ₀ < min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) := fun r hr =>
    lt_min (by linarith [hρ₀r₀ r hr, (hρr r hr).1]) (by linarith)
  have hminρ : ∀ r hr, min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) < ρr r hr := fun r hr =>
    (min_le_left _ _).trans_lt (by linarith [hρrpos r hr])
  have hrmn4 : ∀ r hr, 4 * ρ₀ < rmn r hr := by
    intro r hr
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hrmnI r hr hrI]; exact hmin4 r hr
    · rw [hrmnO r hr hrI]; linarith [hρ₀r₀ r hr, (D.hrm r hr).1, hρ₀]
  have hRn : ∀ r hr, 4 * (Ds.chart r hr).r₀ < Rn r hr ∧ Rn r hr ≤ (Ds.chart r hr).R := by
    intro r hr
    rw [hDsR r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hRnI r hr hrI]
      exact ⟨by linarith [hmin4 r hr, hDsρ₀ r hr], by linarith [hminρ r hr, hρrR r hr]⟩
    · rw [hRnO r hr hrI]
      exact ⟨by linarith [hDsr₀ r hr, (D.chart r hr).hr₀R], le_rfl⟩
  have hrmn : ∀ r hr, 2 * (Ds.chart r hr).r₀ < rmn r hr ∧ rmn r hr ≤ Ds.rm r hr ∧
      rmn r hr ≤ Rn r hr := by
    intro r hr
    rw [hDsrm r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hrmnI r hr hrI, hRnI r hr hrI]
      exact ⟨by linarith [hmin4 r hr, hDsρ₀ r hr, hρ₀], by linarith [hminρ r hr, hρrrm r hr],
        le_rfl⟩
    · rw [hrmnO r hr hrI, hRnO r hr hrI]
      exact ⟨by linarith [hDsr₀ r hr, (D.hrm r hr).1], le_rfl, (D.hrm r hr).2⟩
  have hconst : ∀ r hr, ∀ y, morseNorm n y ≤ Rn r hr →
      μ ((Ds.chart r hr).χ y) * (ρ (f ((Ds.chart r hr).χ y)) - f ((Ds.chart r hr).χ y)) =
        μ r * (ρ (f r) - f r) ∧
      μ ((Ds.chart r hr).χ y) * (deriv ρ (f ((Ds.chart r hr).χ y)) - 1) = 0 := by
    intro r hr y hy
    rw [hDsχ r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hRnI r hr hrI] at hy
      have hyρ : (D.chart r hr).χ y ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρr r hr} :=
        ⟨y, hy.trans_lt (hminρ r hr), rfl⟩
      have hrρ : r ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρr r hr} :=
        (D.chart r hr).p_mem_image_lt (hρrpos r hr)
      by_cases hP : r ∈ P₁
      · rw [hμ1 r hr hP hrI _ hyρ, hμ1 r hr hP hrI r hrρ]
        have hRle : min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) ≤ (D.chart r hr).R :=
          (hminρ r hr).le.trans (hρrR r hr)
        have hlev := (D.chart r hr).f_mem_Icc_of_morseNorm_le hRle hy
        have hsq : min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) ^ 2 ≤ σ / 2 := by
          have h1 : min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) ≤ Real.sqrt (2 * σ) / 2 :=
            min_le_right _ _
          have h0 : 0 ≤ min (ρr r hr / 2) (Real.sqrt (2 * σ) / 2) :=
            le_min (by linarith [hρrpos r hr]) (by linarith)
          have h2 := pow_le_pow_left₀ h0 h1 2
          have h3 : (Real.sqrt (2 * σ) / 2) ^ 2 = σ / 2 := by
            rw [div_pow, Real.sq_sqrt (by linarith)]; ring
          linarith
        have hlev' : f ((D.chart r hr).χ y) ∈ Ioo (f r - σ) (f r + σ) :=
          ⟨by linarith [hlev.1], by linarith [hlev.2]⟩
        have e1 := hρtr r hr hP hrI _ (Ioo_subset_Icc_self hlev')
        have e3 := deriv_eq_one_of_translation (hρtr r hr hP hrI) hlev'
        rw [e1, e3]
        constructor <;> ring
      · rw [hμ0 r hr hP hrI _ hyρ, hμ0 r hr hP hrI r hrρ]
        exact ⟨by ring, by ring⟩
    · rw [hRnO r hr hrI] at hy
      have hlev := (D.chart r hr).f_mem_Icc_of_morseNorm_le le_rfl hy
      have hout : f ((D.chart r hr).χ y) < a₃ ∨ b₃ < f ((D.chart r hr).χ y) := by
        rcases hsep r hr hrI with h | h
        · left; linarith only [hlev.2, h, ha₃, hε]
        · right; linarith only [hlev.1, h, hb₃, hε]
      have hrout : f r ∉ Ioo a₃ b₃ := by
        rcases hsep r hr hrI with h | h
        · exact fun h' => by linarith only [h'.1, h, ha₃, hε, sq_nonneg (D.chart r hr).R]
        · exact fun h' => by linarith only [h'.2, h, hb₃, hε, sq_nonneg (D.chart r hr).R]
      have e1 : ρ (f ((D.chart r hr).χ y)) = f ((D.chart r hr).χ y) := hρid _ (by
        rcases hout with h | h
        · exact fun h' => absurd h'.1 (not_lt.2 h.le)
        · exact fun h' => absurd h'.2 (not_lt.2 h.le))
      have e2 : ρ (f r) = f r := hρid _ hrout
      have e3 := deriv_eq_one_of_notMem hρid hout
      rw [e1, e2, e3]
      exact ⟨by ring, by ring⟩
  obtain ⟨D', hD'c, hD'rm, φ, -, -, hφ⟩ :=
    exists_rescaled hf ha₂ hab₂ hb₂ hreg Ds hcrit μ hμ hμ01 hμVs hμcrit ρ hρ hρ' hρid
      ⟨ha₃, hb₃⟩ hρmaps Rn rmn hRn hrmn hconst
  have hflowconst : ∀ x t, (∀ s ∈ uIcc 0 t, f (D.flow s x) ∈ Ioo a₂ b₂) →
      μ (D.flow t x) = μ x := by
    intro x t hseg
    have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun u => μ (D.flow u x)) 0 s := by
      intro s hs
      have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) μ (D.flow s x) :=
        (hμ.contMDiffAt (hBo.mem_nhds (hseg s hs))).mdifferentiableAt (by simp)
      have := hasDerivAt_comp_integralCurve (D.isMIntegralCurve_flow x) hmd
      rwa [hμV _ (hseg s hs), map_zero] at this
    rcases le_total 0 t with ht | ht
    · rw [uIcc_of_le ht] at hd
      have := constant_of_has_deriv_right_zero (f := fun u => μ (D.flow u x)) (a := 0) (b := t)
        (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ⟨ht, le_rfl⟩
      simpa using this
    · rw [uIcc_of_ge ht] at hd
      have := constant_of_has_deriv_right_zero (f := fun u => μ (D.flow u x)) (a := t) (b := 0)
        (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
        (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) 0 ⟨ht, le_rfl⟩
      simpa using this.symm
  have hμzero : ∀ r hr, r ∉ P₁ → f r ∈ Ioo a₂ b₂ → ∀ x t,
      (∀ s ∈ uIcc 0 t, f (D.flow s x) ∈ Ioo a₂ b₂) →
      D.flow t x ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρr r hr} →
      ∀ᶠ x' in 𝓝 x, μ x' = 0 := by
    intro r hr hP hrI x t hseg ht
    have h1 : ∀ᶠ x' in 𝓝 x, ∀ s ∈ uIcc 0 t, f (D.flow s x') ∈ Ioo a₂ b₂ := by
      refine isCompact_uIcc.eventually_forall_of_forall_eventually fun s hs => ?_
      have hc : Continuous (fun z : M × ℝ => f (D.flow z.2 z.1)) :=
        hfc.comp (D.continuous_flow_joint.comp continuous_swap)
      exact hc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hseg s hs))
    have h2 : ∀ᶠ x' in 𝓝 x, D.flow t x' ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρr r hr} :=
      (D.continuous_flow t).continuousAt.preimage_mem_nhds ((hball_open r hr).mem_nhds ht)
    filter_upwards [h1, h2] with x' h1' h2'
    rw [← hflowconst x' t h1']
    exact hμ0 r hr hP hrI _ h2'
  have hgf : ∀ x, (∀ᶠ x' in 𝓝 x, μ x' = 0) → (Rearrange.rearranged f μ ρ) =ᶠ[𝓝 x] f :=
    fun x h => by
      filter_upwards [h] with x' hx'
      rw [Rearrange.rearranged_apply, hx', zero_mul, add_zero]
  have hevd : ∀ x, (Rearrange.rearranged f μ ρ) =ᶠ[𝓝 x] f →
      mfderiv I 𝓘(ℝ, ℝ) (Rearrange.rearranged f μ ρ) x = mfderiv I 𝓘(ℝ, ℝ) f x :=
    fun x hev => by rw [hev.mfderiv_eq]; rfl
  have hnot : ∀ r hr (y : Fin n → ℝ), morseNorm n y < (D.chart r hr).R' → ∀ p hp (ρ' : ℝ),
      ρ' ≤ (D.chart p hp).R' → (p = r → ρ' ≤ morseNorm n y) →
      (D.chart r hr).χ y ∉ (D.chart p hp).χ '' {z | morseNorm n z < ρ'} := by
    intro r hr y hy p hp ρ' hρ' hpr ⟨z, hz, hzy⟩
    have hz' : morseNorm n z < (D.chart p hp).R' := lt_of_lt_of_le hz hρ'
    by_cases hpr' : p = r
    · subst hpr'
      have hzy' : z = y := (D.chart p hp).χ.injOn
        ((D.chart p hp).hball (mem_ball_of_morseNorm_lt hz'))
        ((D.chart p hp).hball (mem_ball_of_morseNorm_lt hy)) hzy
      subst hzy'
      exact absurd (hpr rfl) (not_le.2 hz)
    · exact Set.disjoint_left.1 (D.disjoint p hp r hr hpr') ⟨z, mem_ball_of_morseNorm_lt hz', hzy⟩
        ⟨y, mem_ball_of_morseNorm_lt hy, rfl⟩
  have hDsball : ∀ p hp, Ds.smallBall p hp =
      (D.chart p hp).χ '' {z | morseNorm n z < (Ds.chart p hp).r₀} := fun p hp => by
    rw [GradientLikeStrip.smallBall, hDsχ p hp]
  have hD'ball : ∀ p hp, D'.smallBall p hp =
      (D.chart p hp).χ '' {z | morseNorm n z < (Ds.chart p hp).r₀} := fun p hp => by
    rw [GradientLikeStrip.smallBall, (hD'c p hp).1, (hD'c p hp).2.2.1, hDsχ p hp]
  have hM1u : ∀ x, f x ∈ Icc a b → (Rearrange.rearranged f μ ρ) x = f x →
      mfderiv I 𝓘(ℝ, ℝ) (Rearrange.rearranged f μ ρ) x = mfderiv I 𝓘(ℝ, ℝ) f x →
      (∀ p hp, x ∉ (D.chart p hp).χ '' {z | morseNorm n z < (Ds.chart p hp).r₀}) →
      D'.V x = Ds.V x := by
    intro x hx hgx hd hball
    exact eq_of_unit_of_mfderiv_eq Ds D' hφ hx (hgx ▸ hx) hd
      (fun p hp => by rw [hDsball p hp]; exact hball p hp)
      (fun p hp => by rw [hD'ball p hp]; exact hball p hp)
  have hreach : ∀ r hr, r ∉ P₁ → f r ∈ Ioo a₂ b₂ → ∀ y, morseNorm n y < D.rm r hr →
      (negPart (D.chart r hr).hk y = 0 ∨ posPart (D.chart r hr).hk y = 0) →
      ∀ᶠ x' in 𝓝 ((D.chart r hr).χ y), μ x' = 0 := by
    intro r hr hP hrI y hy hdisc
    have hyR : morseNorm n y ≤ (D.chart r hr).R := hy.le.trans (D.hrm r hr).2
    have hband : ∀ z, morseNorm n z ≤ morseNorm n y → f ((D.chart r hr).χ z) ∈ Ioo a₂ b₂ := by
      intro z hz
      have h1 := (D.chart r hr).f_mem_Icc_of_morseNorm_le le_rfl (hz.trans hyR)
      have h2 := hin r hr hrI
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hxI : f ((D.chart r hr).χ y) ∈ Icc a b := by
      have := hband y le_rfl
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have havoid : ∀ z, morseNorm n z ≤ morseNorm n y →
        (D.chart r hr).χ z ∉ (D.chart r hr).χ '' {w | morseNorm n w < ρr r hr} →
        ∀ p hp, (D.chart r hr).χ z ∉ D.smallBall p hp := by
      intro z hz hzρ p hp
      have hzR' : morseNorm n z < (D.chart r hr).R' := hz.trans_lt (hy.trans (D.rm_lt_R' r hr))
      have hzρ' : ρr r hr ≤ morseNorm n z := not_lt.1 fun h => hzρ ⟨z, h, rfl⟩
      exact hnot r hr z hzR' p hp _ (D.r₀_lt_R' p hp).le
        (fun hpr => by subst hpr; linarith [(hρr p hr).1])
    rcases hdisc with hu | hv
    · have hfr : f r ≤ f ((D.chart r hr).χ y) := by
        have := GradientLikeStrip.f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hy hu le_rfl
        rwa [GradientLikeStrip.flow_zero] at this
      have hT0 : 0 ≤ f ((D.chart r hr).χ y) - (f r + a₂) / 2 := by linarith [hrI.1]
      have hmem : ∀ s, 0 ≤ s → ∃ z, morseNorm n z ≤ morseNorm n y ∧
          (D.chart r hr).χ z = D.flow s ((D.chart r hr).χ y) := fun s hs => by
        obtain ⟨z, ⟨hz1, -⟩, hzx⟩ :=
          GradientLikeStrip.flow_mem_of_negPart_eq_zero (D := D) hr hy hu hs
        exact ⟨z, hz1, hzx⟩
      have hex : ∃ s ∈ Icc 0 (f ((D.chart r hr).χ y) - (f r + a₂) / 2),
          D.flow s ((D.chart r hr).χ y) ∈ (D.chart r hr).χ '' {w | morseNorm n w < ρr r hr} := by
        by_contra hcon
        push Not at hcon
        have hav : ∀ s ∈ uIcc 0 (f ((D.chart r hr).χ y) - (f r + a₂) / 2), ∀ p hp,
            D.flow s ((D.chart r hr).χ y) ∉ D.smallBall p hp := by
          intro s hs p hp
          rw [uIcc_of_le hT0] at hs
          obtain ⟨z, hz, hzx⟩ := hmem s hs.1
          rw [← hzx]
          exact havoid z hz (hzx ▸ hcon s hs) p hp
        have hlev := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs hxI
          (by constructor <;> linarith [hrI.1, hrI.2]) hav _ right_mem_uIcc
        have := GradientLikeStrip.f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hy hu hT0
        linarith [hrI.1]
      obtain ⟨s, hs, hsρ⟩ := hex
      refine hμzero r hr hP hrI _ s (fun u hu => ?_) hsρ
      rw [uIcc_of_le hs.1] at hu
      obtain ⟨z, hz, hzx⟩ := hmem u hu.1
      rw [← hzx]
      exact hband z hz
    · have hfr : f ((D.chart r hr).χ y) ≤ f r := by
        have := GradientLikeStrip.f_flow_le_f_p_of_posPart_eq_zero (D := D) hr hy hv le_rfl
        rwa [GradientLikeStrip.flow_zero] at this
      have hT0 : f ((D.chart r hr).χ y) - (f r + b₂) / 2 ≤ 0 := by linarith [hrI.2]
      have hmem : ∀ s, s ≤ 0 → ∃ z, morseNorm n z ≤ morseNorm n y ∧
          (D.chart r hr).χ z = D.flow s ((D.chart r hr).χ y) := fun s hs => by
        obtain ⟨z, ⟨hz1, -⟩, hzx⟩ :=
          GradientLikeStrip.flow_mem_of_posPart_eq_zero (D := D) hr hy hv hs
        exact ⟨z, hz1, hzx⟩
      have hex : ∃ s ∈ Icc (f ((D.chart r hr).χ y) - (f r + b₂) / 2) 0,
          D.flow s ((D.chart r hr).χ y) ∈ (D.chart r hr).χ '' {w | morseNorm n w < ρr r hr} := by
        by_contra hcon
        push Not at hcon
        have hav : ∀ s ∈ uIcc 0 (f ((D.chart r hr).χ y) - (f r + b₂) / 2), ∀ p hp,
            D.flow s ((D.chart r hr).χ y) ∉ D.smallBall p hp := by
          intro s hs p hp
          rw [uIcc_of_ge hT0] at hs
          obtain ⟨z, hz, hzx⟩ := hmem s hs.2
          rw [← hzx]
          exact havoid z hz (hzx ▸ hcon s hs) p hp
        have hlev := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs hxI
          (by constructor <;> linarith [hrI.1, hrI.2]) hav _ right_mem_uIcc
        have := GradientLikeStrip.f_flow_le_f_p_of_posPart_eq_zero (D := D) hr hy hv hT0
        linarith [hrI.2]
      obtain ⟨s, hs, hsρ⟩ := hex
      refine hμzero r hr hP hrI _ s (fun u hu => ?_) hsρ
      rw [uIcc_of_ge hs.2] at hu
      obtain ⟨z, hz, hzx⟩ := hmem u hu.2
      rw [← hzx]
      exact hband z hz
  have hderiv1 : ∀ t, t ∉ Ioo a₃ b₃ → deriv ρ t = 1 := by
    have hcont : Continuous (deriv ρ) := hρ.continuous_deriv (by simp)
    have hclosed : IsClosed {t | deriv ρ t = 1} := isClosed_eq hcont continuous_const
    intro t ht
    simp only [mem_Ioo, not_and_or, not_lt] at ht
    rcases ht with h | h
    · have hsub : Iio a₃ ⊆ {t | deriv ρ t = 1} := fun s hs =>
        deriv_eq_one_of_notMem hρid (Or.inl hs)
      have := hclosed.closure_subset_iff.2 hsub
      rw [closure_Iio] at this
      exact this h
    · have hsub : Ioi b₃ ⊆ {t | deriv ρ t = 1} := fun s hs =>
        deriv_eq_one_of_notMem hρid (Or.inr hs)
      have := hclosed.closure_subset_iff.2 hsub
      rw [closure_Ioi] at this
      exact this h
  have hdnot : ∀ x, f x ∉ Ioo a₃ b₃ →
      mfderiv I 𝓘(ℝ, ℝ) (Rearrange.rearranged f μ ρ) x = mfderiv I 𝓘(ℝ, ℝ) f x := by
    intro x hx
    by_cases hxI : f x ∈ Ioo a₂ b₂
    · have hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x :=
        (hμ.contMDiffAt (hBo.mem_nhds hxI)).mdifferentiableAt (by simp)
      ext v
      have := Rearrange.mfderiv_rearranged_apply hfs hμx hρ v
      rw [hρid _ hx, hderiv1 _ hx, sub_self, sub_self, mul_zero, zero_mul, add_zero,
        add_zero, one_mul] at this
      exact this
    · have hev := Rearrange.rearranged_eventuallyEq_of_notMem (μ := μ) hfc hρid ⟨ha₃, hb₃⟩ hxI
      exact hevd x hev
  refine ⟨Rearrange.rearranged f μ ρ, D', ρ₀ ^ 2, by positivity, hρ₀ε, hmod, hstrip, hcritIff,
    hidxEq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hP hsI
    rw [hval s, hμ1 s hs hP hsI s ((D.chart s hs).p_mem_image_lt (hρrpos s hs))]
    ring
  · intro r hr hor
    rw [hval r]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · have hP : r ∉ P₁ := by
        rcases hor with h | h
        · exact h
        · exact absurd hrI h
      rw [hμ0 r hr hP hrI r ((D.chart r hr).p_mem_image_lt (hρrpos r hr))]
      ring
    · rw [hρid _ (fun h => hrI ⟨ha₃.trans h.1, h.2.trans hb₃⟩)]
      ring
  · intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hD'c r hr
    refine ⟨h1.trans (hDsχ r hr), h2.trans (hDsk r hr), by rw [h3]; exact hDsr₀ r hr, ?_,
      h5.trans (hDsR' r hr), ?_, ?_⟩
    · rw [h4]
      have := (hRn r hr).2
      rwa [hDsR r hr] at this
    · rw [h3]
      have := hDsρ₀ r hr
      have h0 := (Ds.chart r hr).hr₀
      nlinarith
    · rw [hD'rm r hr]
      have := hrmn4 r hr
      nlinarith
  · intro r hr hrI
    exact ⟨(hD'c r hr).2.2.2.1.trans (hRnO r hr hrI), (hD'rm r hr).trans (hrmnO r hr hrI)⟩
  · intro r hr hor y hy hdisc
    have hχ' : (D'.chart r hr).χ = (D.chart r hr).χ := (hD'c r hr).1.trans (hDsχ r hr)
    have hk' : (D'.chart r hr).k = (D.chart r hr).k := (hD'c r hr).2.1.trans (hDsk r hr)
    by_cases hyr : morseNorm n y < rmn r hr
    · have := D'.model r hr y (by rw [hD'rm r hr]; exact hyr)
      rw [hχ', hk'] at this
      exact this
    · have hrI : f r ∈ Ioo a₂ b₂ := by
        by_contra hrI
        rw [hrmnO r hr hrI] at hyr
        exact hyr hy
      have hP : r ∉ P₁ := by
        rcases hor with h | h
        · exact h
        · exact absurd hrI h
      have hev := hgf _ (hreach r hr hP hrI y hy hdisc)
      have hyR' : morseNorm n y < (D.chart r hr).R' := hy.trans (D.rm_lt_R' r hr)
      have hxI : f ((D.chart r hr).χ y) ∈ Icc a b := by
        have h1 := (D.chart r hr).f_mem_Icc_of_morseNorm_le le_rfl (hy.le.trans (D.hrm r hr).2)
        have h2 := hin r hr hrI
        exact ⟨by linarith [h1.1, hrI.1], by linarith [h1.2, hrI.2]⟩
      have hVeq : D'.V ((D.chart r hr).χ y) = Ds.V ((D.chart r hr).χ y) := by
        refine hM1u _ hxI hev.self_of_nhds (hevd _ hev) fun p hp => ?_
        refine hnot r hr y hyR' p hp _ ((hDsr₀ p hp).trans (D.r₀_lt_R' p hp).le)
          (fun hpr => ?_)
        subst hpr
        have := (hrmn p hr).1
        linarith [not_lt.1 hyr, (Ds.chart p hr).hr₀]
      rw [hVeq]
      have := Ds.model r hr y (by rw [hDsrm r hr]; exact hy)
      rw [hDsχ r hr, hDsk r hr] at this
      rw [this, (hD'c r hr).2.2.1]
  · intro x hx hxI hor
    have hxDs : ∀ p hp, x ∉ (D.chart p hp).χ '' {z | morseNorm n z < (Ds.chart p hp).r₀} := by
      rintro p hp ⟨z, hz, hzx⟩
      exact (D.notMem_closedSmallBalls_iff.1 hx) p hp
        ⟨z, (le_of_lt hz).trans (hDsr₀ p hp), hzx⟩
    have hkey : Rearrange.rearranged f μ ρ x = f x ∧
        mfderiv I 𝓘(ℝ, ℝ) (Rearrange.rearranged f μ ρ) x = mfderiv I 𝓘(ℝ, ℝ) f x := by
      rcases hor with h | ⟨t, hseg, r, hr, hP, hrI, ht⟩
      · exact ⟨Rearrange.rearranged_eq_of_notMem hρid h, hdnot x h⟩
      · have hev := hgf x (hμzero r hr hP hrI x t hseg
          (image_mono (fun z (hz : morseNorm n z < (D.chart r hr).r₀) =>
            show morseNorm n z < ρr r hr from hz.trans (hρr r hr).1) ht))
        exact ⟨hev.self_of_nhds, hevd x hev⟩
    refine ⟨hkey.1, ?_⟩
    rw [hM1u x hxI hkey.1 hkey.2 hxDs]
    exact hDsV x hx

theorem exists_top_index_one [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) {p : M}
    (hp : f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ morseIndex I f p = 1) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
      InjOn g {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      ∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x → morseIndex I g x = 1 → x ≠ p → g x < g p := by
  classical
  obtain ⟨f₁, hmod₁, hf₁, hsi₁, hcrit₁, hidx₁, hinj₁⟩ := exists_distinct_selfIndexing I hf hsi
  have hIoo₁ : ∀ x, f₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hglob : ∀ x, (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f₁ x = morseIndex I f x) := by
    intro x
    by_cases hx : f x ∈ Ioo a b
    · exact ⟨hcrit₁ x hx, hidx₁ x hx⟩
    have hfx : f₁ x = f x := hmod₁.eqOn hx
    by_cases hxI : f x ∈ Icc a b
    · have hab : f x = a ∨ f x = b := by
        rcases eq_or_lt_of_le hxI.1 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le hxI.2 with h' | h'
        · exact Or.inr h'
        exact absurd ⟨h, h'⟩ hx
      have h1 := hf.regular x hab
      have h2 := hf₁.regular x (by rw [hfx]; exact hab)
      exact ⟨⟨fun h => absurd h h2, fun h => absurd h h1⟩, fun h => absurd h h1⟩
    · have hop : IsOpen (f ⁻¹' (Icc a b)ᶜ) :=
        isClosed_Icc.isOpen_compl.preimage hf.smooth.continuous
      have hev : f₁ =ᶠ[𝓝 x] f := by
        filter_upwards [hop.mem_nhds hxI] with y hy
        exact hmod₁.eqOn (fun h => hy (Ioo_subset_Icc_self h))
      exact ⟨MonotoneShift.isCriticalPointAt_congr_nhds hev,
        fun _ => MonotoneShift.morseIndex_congr_nhds hev⟩
  set crit : Finset M := (hf₁.finite_critical.subset fun x hx =>
    ⟨Ioo_subset_Icc_self hx.1, hx.2⟩ :
      {x | f₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x}.Finite).toFinset with hcritdef
  have hcrit : ∀ x, x ∈ crit ↔ f₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x := fun x => by
    rw [hcritdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hp₁ : f₁ p ∈ Ioo a b := (hIoo₁ p).2 hp.1
  have hpc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ p := (hcrit₁ p hp.1).2 hp.2.1
  have hpi : morseIndex I f₁ p = 1 := by rw [hidx₁ p hp.1 hp.2.1]; exact hp.2.2
  have hpcrit : p ∈ crit := (hcrit p).2 ⟨hp₁, hpc⟩
  set crit₁ : Finset M := crit.filter fun q => morseIndex I f₁ q = 1 with hcrit₁def
  have hmem₁ : ∀ q, q ∈ crit₁ ↔ q ∈ crit ∧ morseIndex I f₁ q = 1 := fun q =>
    Finset.mem_filter
  have hne : crit₁.Nonempty := ⟨p, (hmem₁ p).2 ⟨hpcrit, hpi⟩⟩
  obtain ⟨pm, hpm, hpmmin⟩ := crit₁.exists_min_image f₁ hne
  obtain ⟨pM, hpM, hpMmax⟩ := crit₁.exists_max_image f₁ hne
  obtain ⟨hpmc, hpmi⟩ := (hmem₁ pm).1 hpm
  obtain ⟨hpMc, hpMi⟩ := (hmem₁ pM).1 hpM
  have hmM : f₁ pm ≤ f₁ pM := hpMmax pm hpm
  have hpmp : f₁ pm ≤ f₁ p := hpmmin p ((hmem₁ p).2 ⟨hpcrit, hpi⟩)
  obtain ⟨δ, hδ, hgap⟩ := DistinctSelfIndexing.exists_index_gap hf₁ hsi₁
  have hpmab := ((hcrit pm).1 hpmc).1
  have hpMab := ((hcrit pM).1 hpMc).1
  obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = min δ (min (f₁ pm - a) (b - f₁ pM)) := ⟨_, rfl⟩
  have hδ'pos : 0 < δ' := by
    rw [hδ'def]
    exact lt_min hδ (lt_min (sub_pos.2 hpmab.1) (sub_pos.2 hpMab.2))
  have hδ'δ : δ' ≤ δ := by rw [hδ'def]; exact min_le_left _ _
  have hδ'a : δ' ≤ f₁ pm - a := by
    rw [hδ'def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ'b : δ' ≤ b - f₁ pM := by
    rw [hδ'def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hclass : ∀ x ∈ crit,
      (morseIndex I f₁ x = 1 ∧ f₁ pm ≤ f₁ x ∧ f₁ x ≤ f₁ pM) ∨
      (morseIndex I f₁ x < 1 ∧ f₁ x ≤ f₁ pm - δ') ∨
      (1 < morseIndex I f₁ x ∧ f₁ pM + δ' ≤ f₁ x) := by
    intro x hx
    have hx' := (hcrit x).1 hx
    rcases lt_trichotomy (morseIndex I f₁ x) 1 with h | h | h
    · refine Or.inr (Or.inl ⟨h, ?_⟩)
      have := hgap x pm hx'.1 hpmab hx'.2 ((hcrit pm).1 hpmc).2 (by rw [hpmi]; exact h)
      linarith
    · exact Or.inl ⟨h, hpmmin x ((hmem₁ x).2 ⟨hx, h⟩), hpMmax x ((hmem₁ x).2 ⟨hx, h⟩)⟩
    · refine Or.inr (Or.inr ⟨h, ?_⟩)
      have := hgap pM x hpMab hx'.1 ((hcrit pM).1 hpMc).2 hx'.2 (by rw [hpMi]; exact h)
      linarith
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = min 1 (δ' / 4) := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by rw [hR₀def]; exact lt_min one_pos (by linarith)
  obtain ⟨D, ε, hε, r', -, hr'ε, hD, hE2, -⟩ :=
    GradientLikeStrip.exists_gradientLike_allPairs hf₁ hsi₁ hinj₁ crit hcrit hR₀
  have hsmall : ∀ r hr, (D.chart r hr).R ^ 2 / 2 + ε < δ' / 4 := by
    intro r hr
    have hRpos := (D.chart r hr).R_pos
    have hR1 : (D.chart r hr).R ≤ 1 := (hD r hr).1.trans (by rw [hR₀def]; exact min_le_left _ _)
    have hRδ : (D.chart r hr).R ≤ δ' / 4 :=
      (hD r hr).1.trans (by rw [hR₀def]; exact min_le_right _ _)
    have hR2 : (D.chart r hr).R ^ 2 ≤ δ' / 4 := by
      calc (D.chart r hr).R ^ 2 = (D.chart r hr).R * (D.chart r hr).R := by ring
        _ ≤ 1 * (δ' / 4) := mul_le_mul hR1 hRδ hRpos.le zero_le_one
        _ = δ' / 4 := one_mul _
    have hrm2 : D.rm r hr ^ 2 ≤ (D.chart r hr).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos r hr).le (D.hrm r hr).2 2
    have := (hD r hr).2.2.1
    nlinarith
  have hband : ∀ r ∈ crit, (f₁ r ∈ Ioo (f₁ pm - δ' / 2) (f₁ pM + δ' / 2) ↔
      morseIndex I f₁ r = 1) := by
    intro r hr
    rcases hclass r hr with h | h | h
    · exact ⟨fun _ => h.1, fun _ => ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩
    · exact ⟨fun hb => absurd hb.1 (by linarith [h.2]), fun he => by omega⟩
    · exact ⟨fun hb => absurd hb.2 (by linarith [h.2]), fun he => by omega⟩
  obtain ⟨P₁, hP₁def⟩ : ∃ P₁ : Set M,
      P₁ = {x | x ∈ crit ∧ morseIndex I f₁ x = 1 ∧ f₁ p < f₁ x} := ⟨_, rfl⟩
  have hP₁ : ∀ x, x ∈ P₁ ↔ x ∈ crit ∧ morseIndex I f₁ x = 1 ∧ f₁ p < f₁ x := by
    intro x; rw [hP₁def]; exact Iff.rfl
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℝ,
      T = (crit.filter fun x => morseIndex I f₁ x = 1 ∧ f₁ p < f₁ x).image f₁ := ⟨_, rfl⟩
  have hT : ∀ v, v ∈ T ↔ ∃ x ∈ P₁, f₁ x = v := by
    intro v
    rw [hTdef, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxv⟩
      exact ⟨x, (hP₁ x).2 (Finset.mem_filter.1 hx), hxv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨x, Finset.mem_filter.2 ((hP₁ x).1 hx), hxv⟩
  obtain ⟨k, hk⟩ : ∃ k, T.card = k := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : Fin k → ℝ, t = fun i => T.orderEmbOfFin hk i := ⟨_, rfl⟩
  have ht : StrictMono t := by rw [htdef]; exact (T.orderEmbOfFin hk).strictMono
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = δ' / (4 * ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hck : c * ((k : ℝ) + 1) = δ' / 4 := by
    rw [hcdef, div_mul_eq_mul_div, mul_div_mul_right _ _ hk1.ne']
  obtain ⟨s, hsdef⟩ : ∃ s : Fin k → ℝ,
      s = fun i : Fin k => (f₁ pm - δ' / 4) + c * (((i : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hs : StrictMono s := by
    intro i j hij
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    rw [hsdef]
    change (f₁ pm - δ' / 4) + c * (((i : ℕ) : ℝ) + 1) < (f₁ pm - δ' / 4) + c * (((j : ℕ) : ℝ) + 1)
    have := mul_lt_mul_of_pos_left (show ((i : ℕ) : ℝ) + 1 < ((j : ℕ) : ℝ) + 1 by linarith) hcpos
    linarith
  have hsbd : ∀ i, f₁ pm - δ' / 4 < s i ∧ s i < f₁ pm := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hsdef]
    change f₁ pm - δ' / 4 < (f₁ pm - δ' / 4) + c * (((i : ℕ) : ℝ) + 1) ∧
      (f₁ pm - δ' / 4) + c * (((i : ℕ) : ℝ) + 1) < f₁ pm
    have h1 : 0 < c * (((i : ℕ) : ℝ) + 1) := mul_pos hcpos (by linarith)
    have h2 : c * (((i : ℕ) : ℝ) + 1) < c * ((k : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hcpos
    constructor <;> linarith
  have htmem : ∀ i, t i ∈ T := fun i => by rw [htdef]; exact T.orderEmbOfFin_mem hk i
  have htbd : ∀ i, f₁ pm ≤ t i ∧ t i ≤ f₁ pM := by
    intro i
    obtain ⟨x, hx, hxv⟩ := (hT (t i)).1 (htmem i)
    obtain ⟨hxc, hxi, -⟩ := (hP₁ x).1 hx
    rw [← hxv]
    exact ⟨hpmmin x ((hmem₁ x).2 ⟨hxc, hxi⟩), hpMmax x ((hmem₁ x).2 ⟨hxc, hxi⟩)⟩
  obtain ⟨σ, hσ, ρ, hρ, hρ', hρid, hρtr⟩ := exists_multiShift ht hs
    (a₃ := f₁ pm - δ' / 4) (b₃ := f₁ pM + δ' / 4) fun i =>
      ⟨⟨by linarith [htbd i], by linarith [htbd i]⟩,
        ⟨(hsbd i).1, by linarith [(hsbd i).2]⟩⟩
  have hρmono : StrictMono ρ := strictMono_of_deriv_pos hρ'
  have hPt : ∀ x ∈ P₁, ∃ i, t i = f₁ x := by
    intro x hx
    have hmemT : f₁ x ∈ (T : Set ℝ) := (hT (f₁ x)).2 ⟨x, hx, rfl⟩
    rw [← Finset.range_orderEmbOfFin T hk] at hmemT
    obtain ⟨i, hi⟩ := hmemT
    exact ⟨i, by rw [htdef]; exact hi⟩
  have hρval : ∀ x ∈ P₁, f₁ pm - δ' / 4 < ρ (f₁ x) ∧ ρ (f₁ x) < f₁ pm := by
    intro x hx
    obtain ⟨i, hi⟩ := hPt x hx
    have h := hρtr i (t i) ⟨by linarith, by linarith⟩
    rw [← hi, h]
    have := hsbd i
    constructor <;> linarith
  obtain ⟨g, D', ε', -, -, hmod₂, hg, hcrit₂, hidx₂, hmv, hfx, -⟩ :=
    exists_move hf₁ hcrit D hε hr'ε (fun r hr => (hD r hr).2)
      (a₂ := f₁ pm - δ' / 2) (b₂ := f₁ pM + δ' / 2)
      (a₃ := f₁ pm - δ' / 4) (b₃ := f₁ pM + δ' / 4)
      (by linarith) (by linarith)
      ⟨by linarith, by linarith, by linarith⟩
      (by
        intro x hx hcx
        have hxab : f₁ x ∈ Ioo a b := by
          rcases hx with h | h <;> rw [h] <;> constructor <;> linarith
        rcases hclass x ((hcrit x).2 ⟨hxab, hcx⟩) with h | h | h <;>
          rcases hx with h' | h' <;> linarith [h.2])
      (by
        intro r hr hrb
        rcases hclass r hr with h | h | h
        · exact absurd ((hband r hr).2 h.1) hrb
        · left; linarith [h.2, hsmall r hr]
        · right; linarith [h.2, hsmall r hr])
      (by
        intro r hr hrb
        rcases hclass r hr with h | h | h
        · constructor <;> linarith [h.2.1, h.2.2, hsmall r hr]
        · exact absurd hrb.1 (by linarith [h.2])
        · exact absurd hrb.2 (by linarith [h.2]))
      P₁
      (by
        intro r hr q hq hrP hqP hrb hqb x hx τ
        have hri : morseIndex I f₁ r = 1 := (hband r hr).1 hrb
        obtain ⟨-, hqi, hpq⟩ := (hP₁ q).1 hqP
        have hrp : f₁ r ≤ f₁ p := by
          by_contra hlt
          exact hrP ((hP₁ r).2 ⟨hr, hri, lt_of_not_ge hlt⟩)
        have hkr : (D.chart r hr).k = 1 := by rw [← (D.chart r hr).hkidx]; exact hri
        have hkq : (D.chart q hq).k = 1 := by rw [← (D.chart q hq).hkidx]; exact hqi
        exact hE2 r hr q hq hkr hkq (lt_of_le_of_lt hrp hpq) x hx τ)
      ρ hρ hρ' hρid hσ
      (by
        intro q hq hqP _ τ hτ
        obtain ⟨i, hi⟩ := hPt q hqP
        rw [← hi] at hτ ⊢
        rw [hρtr i τ hτ, hρtr i (t i) ⟨by linarith, by linarith⟩]
        ring)
  have hIoo₂ : ∀ x, g x ∈ Ioo a b ↔ f₁ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₂.preimage_Ioo x
  have hgv : ∀ z ∈ crit, (z ∈ P₁ ∧ morseIndex I f₁ z = 1 ∧ g z = ρ (f₁ z) ∧
      f₁ pm - δ' / 4 < g z ∧ g z < f₁ pm) ∨ (z ∉ P₁ ∧ g z = f₁ z) := by
    intro z hz
    by_cases hzP : z ∈ P₁
    · have hzi := ((hP₁ z).1 hzP).2.1
      have hgz := hmv z hz hzP ((hband z hz).2 hzi)
      rw [hgz]
      exact Or.inl ⟨hzP, hzi, rfl, hρval z hzP⟩
    · exact Or.inr ⟨hzP, hfx z hz (Or.inl hzP)⟩
  have hcritg : ∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x →
      x ∈ crit ∧ morseIndex I g x = morseIndex I f₁ x := by
    intro x hx hcx
    have hc₁ := (hcrit₂ x).1 hcx
    exact ⟨(hcrit x).2 ⟨(hIoo₂ x).1 hx, hc₁⟩, hidx₂ x hc₁⟩
  have hpP : p ∉ P₁ := fun h => lt_irrefl _ ((hP₁ p).1 h).2.2
  have hgp : g p = f₁ p := hfx p hpcrit (Or.inl hpP)
  refine ⟨g, hmod₁.trans hmod₂, hg, ?_, ?_, fun x => (hcrit₂ x).trans (hglob x).1,
    fun x hx => by rw [hidx₂ x ((hglob x).1.2 hx), (hglob x).2 hx], ?_⟩
  · intro x y hx hy hcx hcy hlt
    obtain ⟨hxc, hxi⟩ := hcritg x hx hcx
    obtain ⟨hyc, hyi⟩ := hcritg y hy hcy
    rw [hxi, hyi] at hlt
    rcases hgv x hxc with hX | hX <;> rcases hgv y hyc with hY | hY
    · omega
    · rcases hclass y hyc with h | h | h
      · omega
      · omega
      · rw [hY.2]; linarith [h.2, hX.2.2.2.2]
    · rcases hclass x hxc with h | h | h
      · omega
      · rw [hX.2]; linarith [h.2, hY.2.2.2.1]
      · omega
    · rw [hX.2, hY.2]
      exact hsi₁ x y ((hcrit x).1 hxc).1 ((hcrit y).1 hyc).1 ((hcrit x).1 hxc).2
        ((hcrit y).1 hyc).2 hlt
  · intro x hx y hy hxy
    obtain ⟨hxc, -⟩ := hcritg x hx.1 hx.2
    obtain ⟨hyc, -⟩ := hcritg y hy.1 hy.2
    have hinj' : f₁ x = f₁ y → x = y := fun h =>
      hinj₁ ((hcrit x).1 hxc) ((hcrit y).1 hyc) h
    rcases hgv x hxc with hX | hX <;> rcases hgv y hyc with hY | hY
    · rw [hX.2.2.1, hY.2.2.1] at hxy
      exact hinj' (hρmono.injective hxy)
    · exfalso
      rw [hY.2] at hxy
      rcases hclass y hyc with h | h | h <;> linarith [h.2, hX.2.2.2.1, hX.2.2.2.2]
    · exfalso
      rw [hX.2] at hxy
      rcases hclass x hxc with h | h | h <;> linarith [h.2, hY.2.2.2.1, hY.2.2.2.2]
    · rw [hX.2, hY.2] at hxy
      exact hinj' hxy
  · intro x hx hcx hix hxp
    obtain ⟨hxc, hxi⟩ := hcritg x hx hcx
    rw [hxi] at hix
    rw [hgp]
    rcases hgv x hxc with hX | hX
    · linarith [hX.2.2.2.2]
    · rw [hX.2]
      have hle : f₁ x ≤ f₁ p := by
        by_contra hlt
        exact hX.1 ((hP₁ x).2 ⟨hxc, hix, lt_of_not_ge hlt⟩)
      refine lt_of_le_of_ne hle fun h => hxp ?_
      exact hinj₁ ((hcrit x).1 hxc) ((hcrit p).1 hpcrit) h

end Moves

end

end IndexOnePartner

end DifferentialGeometry.Topology
