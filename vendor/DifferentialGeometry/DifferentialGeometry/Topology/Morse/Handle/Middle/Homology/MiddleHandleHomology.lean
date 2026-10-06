module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Homology.MiddleHomology

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
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem descend_spec (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {t : ℝ} {x : M} (hx : t ≤ f x) (hreach : ∃ s, 0 ≤ s ∧ f (D.flow s x) ≤ t) :
    f (D.descend t x) = t ∧ 0 ≤ D.hitTime t x ∧
      ∀ s, 0 ≤ s → s < D.hitTime t x → t < f (D.flow s x) := by
  have hg : Continuous (fun s => f (D.flow s x)) := hf.continuous.comp (D.continuous_flow_curve x)
  set S : Set ℝ := {s : ℝ | 0 ≤ s ∧ f (D.flow s x) ≤ t} with hS
  have hSne : S.Nonempty := hreach
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  have hSclosed : IsClosed S :=
    isClosed_le continuous_const continuous_id |>.inter (isClosed_le hg continuous_const)
  have hmem : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hht : D.hitTime t x = sInf S := rfl
  have hlow : ∀ s, 0 ≤ s → s < D.hitTime t x → t < f (D.flow s x) := by
    intro s hs0 hsh
    by_contra hcon
    have hsS : s ∈ S := ⟨hs0, not_lt.1 hcon⟩
    have := csInf_le hSbdd hsS
    rw [hht] at hsh
    linarith
  refine ⟨?_, hht ▸ hmem.1, hlow⟩
  have hivt := intermediate_value_Icc' hmem.1 hg.continuousOn
  have ht0 : f (D.flow 0 x) = f x := by rw [D.flow_zero]
  obtain ⟨c, hc, hct⟩ := hivt ⟨hmem.2, ht0 ▸ hx⟩
  have hcS : c ∈ S := ⟨hc.1, hct.le⟩
  have hle := csInf_le hSbdd hcS
  have hceq : c = sInf S := le_antisymm hc.2 hle
  change f (D.flow (D.hitTime t x) x) = t
  rw [hht, ← hceq]
  exact hct

theorem continuousOn_hitTime (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) (hreg : ∀ x ∈ crit, f x ≠ t) :
    ContinuousOn (D.hitTime t) {x | ∃ s, 0 ≤ s ∧ f (D.flow s x) < t} ∧
      ContinuousOn (D.descend t) {x | ∃ s, 0 ≤ s ∧ f (D.flow s x) < t} := by
  classical
  set W : Set M := {x | ∃ s, 0 ≤ s ∧ f (D.flow s x) < t} with hW
  have hfc : Continuous f := hf.continuous
  have hbdd : ∀ y : M, BddBelow {s : ℝ | 0 ≤ s ∧ f (D.flow s y) ≤ t} :=
    fun y => ⟨0, fun s hs => hs.1⟩
  have hnonneg : ∀ y : M, 0 ≤ D.hitTime t y := fun y =>
    Real.sInf_nonneg (fun s hs => hs.1)
  have hclosed : ∀ y : M, IsClosed {s : ℝ | 0 ≤ s ∧ f (D.flow s y) ≤ t} := fun y =>
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le (hfc.comp (D.continuous_flow_curve y)) continuous_const)
  have hmem : ∀ y ∈ W, 0 ≤ D.hitTime t y ∧ f (D.flow (D.hitTime t y) y) ≤ t := by
    intro y hy
    obtain ⟨s, hs0, hs⟩ := hy
    exact (hclosed y).csInf_mem ⟨s, hs0, hs.le⟩ (hbdd y)
  have hcont : ContinuousOn (D.hitTime t) W := by
    intro x hx
    obtain ⟨hT0, hTt⟩ := hmem x hx
    set T := D.hitTime t x with hTdef
    refine tendsto_order.2 ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
    · rcases lt_or_ge a' 0 with ha0 | ha0
      · exact Filter.Eventually.of_forall fun y => ha0.trans_le (hnonneg y)
      · set u := (a' + T) / 2 with hu
        have hu0 : 0 ≤ u := by rw [hu]; linarith
        have huT : u < T := by rw [hu]; linarith
        have hgu : t < f (D.flow u x) := by
          by_contra hcon
          exact (notMem_of_lt_csInf huT (hbdd x)) ⟨hu0, not_lt.1 hcon⟩
        have hev : ∀ᶠ y in 𝓝 x, t < f (D.flow u y) :=
          ((hfc.comp (D.continuous_flow u)).continuousAt).eventually
            (lt_mem_nhds hgu)
        filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hy hyW
        obtain ⟨s, hs0, hs⟩ := hyW
        have hle : u ≤ D.hitTime t y := by
          refine le_csInf ⟨s, hs0, hs.le⟩ ?_
          intro s' hs'
          by_contra hcon
          have h1 := f_flow_antitone (D := D) hf y (not_le.1 hcon).le
          simp only at h1
          linarith [hs'.2]
        have : a' < u := by rw [hu]; linarith
        linarith
    · have hex : ∃ s', 0 ≤ s' ∧ s' < b' ∧ f (D.flow s' x) < t := by
        rcases lt_or_eq_of_le hTt with hlt | heq
        · exact ⟨T, hT0, hb', hlt⟩
        · have hd := hasDerivAt_f_flow (D := D) hf x T
          have hab : f (D.flow T x) ∈ Icc a b := by rw [heq]; exact ⟨hat, htb⟩
          have hnc : D.flow T x ∉ crit := fun hc => hreg _ hc heq
          have hneg : dfV I f D.V (D.flow T x) < 0 := D.neg _ hab hnc
          have hsl := (hd.hasDerivWithinAt (s := Ioi T)).limsup_slope_le'
            (lt_irrefl T) hneg
          obtain ⟨z, hz1, hz2⟩ := (hsl.and (Ioo_mem_nhdsGT hb')).exists
          refine ⟨z, hT0.trans hz2.1.le, hz2.2, ?_⟩
          rw [slope_def_field] at hz1
          have hzT : 0 < z - T := sub_pos.2 hz2.1
          have := (div_neg_iff.1 hz1)
          rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
          · linarith
          · linarith
      obtain ⟨s', hs'0, hs'b, hs'⟩ := hex
      have hev : ∀ᶠ y in 𝓝 x, f (D.flow s' y) < t :=
        ((hfc.comp (D.continuous_flow s')).continuousAt).eventually (gt_mem_nhds hs')
      filter_upwards [nhdsWithin_le_nhds hev] with y hy
      exact (csInf_le (hbdd y) ⟨hs'0, hy.le⟩).trans_lt hs'b
  refine ⟨hcont, ?_⟩
  intro x hx
  have hj : ContinuousAt (fun q : ℝ × M => D.flow q.1 q.2) (D.hitTime t x, x) :=
    D.continuous_flow_joint.continuousAt
  have hp : ContinuousWithinAt (fun y => (D.hitTime t y, y)) W x :=
    (hcont x hx).prodMk continuousWithinAt_id
  exact hj.comp_continuousWithinAt (f := fun y => (D.hitTime t y, y)) hp

theorem nonempty_homeomorph_levels (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {c₁ c₂ : ℝ} (h₁ : a ≤ c₁) (h₁₂ : c₁ ≤ c₂) (h₂ : c₂ ≤ b)
    (hU : ∀ y, f y ∈ Icc c₁ c₂ → ∀ x hx, y ∉ D.smallBall x hx) :
    Nonempty (↥(f ⁻¹' {c₂}) ≃ₜ ↥(f ⁻¹' {c₁})) := by
  obtain ⟨h1, h2⟩ := D.flow_level_transport hf h₁ h₁₂ h₂ hU
  refine ⟨{
    toFun := fun x => ⟨D.flow (c₂ - c₁) x.1, (h1 x.1 x.2).1⟩
    invFun := fun y => ⟨D.flow (c₁ - c₂) y.1, (h2 y.1 y.2).1⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · intro x
    apply Subtype.ext
    simp only
    rw [flow_flow, show c₂ - c₁ + (c₁ - c₂) = 0 by ring, flow_zero]
  · intro y
    apply Subtype.ext
    simp only
    rw [flow_flow, show c₁ - c₂ + (c₂ - c₁) = 0 by ring, flow_zero]
  · exact ((D.continuous_flow _).comp continuous_subtype_val).subtype_mk _
  · exact ((D.continuous_flow _).comp continuous_subtype_val).subtype_mk _

theorem nonempty_homeomorph_level_diff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {c₁ τ c₂ : ℝ}
    (h₁ : a ≤ c₁) (h₁τ : c₁ < τ - ε) (hτ₂ : τ + ε < c₂) (h₂ : c₂ ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc c₁ c₂ → f x = τ)
    (hU : ∀ y, f y ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ → ∀ x hx, y ∉ D.smallBall x hx) :
    Nonempty (↥(f ⁻¹' {c₂} \ ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.rightSphere x hx ε c₂) ≃ₜ
      ↥(f ⁻¹' {c₁} \ ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.leftSphere x hx ε c₁)) := by
  classical
  have _ := hcrit
  have hfc : Continuous f := hf.continuous
  have hunit : ∀ c, c ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ → ∀ y, f y = c →
      dfV I f D.V y = -1 := by
    intro c hc y hy
    refine D.dfV_eq_neg_one_of_level ?_ (fun p hp y' hy' hfy' =>
      hU y' (by rw [hfy']; exact hc) p hp hy') hy
    rcases hc with hc | hc
    · exact ⟨h₁.trans hc.1, by linarith [hc.2]⟩
    · exact ⟨by linarith [hc.1], hc.2.trans h₂⟩
  have huniq : ∀ c, c ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ → ∀ x t t',
      f (D.flow t x) = c → f (D.flow t' x) = c → t = t' :=
    fun c hc x t t' ht ht' => flow_level_unique hf (hunit c hc) ht ht'
  have hc₁m : c₁ ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ := Or.inl ⟨le_rfl, h₁τ.le⟩
  have hc₂m : c₂ ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ := Or.inr ⟨hτ₂.le, le_rfl⟩
  have hτlm : τ - ε ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ := Or.inl ⟨h₁τ.le, le_rfl⟩
  have hτum : τ + ε ∈ Icc c₁ (τ - ε) ∪ Icc (τ + ε) c₂ := Or.inr ⟨le_rfl, hτ₂.le⟩
  have htrU := flow_level_transport (D := D) hf (c' := τ + ε) (c := c₂) (by linarith) hτ₂.le h₂
    (fun y hy p hp => hU y (Or.inr hy) p hp)
  have htrL := flow_level_transport (D := D) hf (c' := c₁) (c := τ - ε) h₁ h₁τ.le (by linarith)
    (fun y hy p hp => hU y (Or.inl hy) p hp)
  have hcls : ∀ p (hp : p ∈ crit) w, w ∈ D.closedSmallBall p hp →
      f w ∈ Icc (τ - ε) (τ + ε) → f p = τ := by
    intro p hp w hw hfw
    obtain ⟨y, hy, rfl⟩ := hw
    have hy' : morseNorm n y ≤ (D.chart p hp).r₀ := hy
    have hyR : morseNorm n y ≤ (D.chart p hp).R := hy'.trans (D.r₀_lt_R p hp).le
    have hnf := (D.chart p hp).hnorm y hyR
    have hscale : ∀ l : ℝ, 0 ≤ l → l < 1 → (D.chart p hp).χ (l • y) ∈ D.smallBall p hp ∧
        f ((D.chart p hp).χ (l • y)) = f p + l ^ 2 * (f ((D.chart p hp).χ y) - f p) := by
      intro l hl0 hl1
      have hr₀ := (D.chart p hp).hr₀
      have hm : morseNorm n (l • y) < (D.chart p hp).r₀ := by
        rw [ModelField.morseNorm_smul, abs_of_nonneg hl0]
        nlinarith [ModelField.morseNorm_nonneg y]
      refine ⟨⟨l • y, hm, rfl⟩, ?_⟩
      rw [(D.chart p hp).hnorm _ (hm.le.trans (D.r₀_lt_R p hp).le), hnf,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        ModelField.negPart_smul, ModelField.posPart_smul, norm_smul, norm_smul,
        Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
      ring
    by_contra hne
    have hout : f p < c₁ ∨ c₂ < f p := by
      by_contra hin
      push Not at hin
      exact hne (hslab p hp hin)
    rcases hout with hlt | hgt
    · have hden : 0 < f ((D.chart p hp).χ y) - f p := by linarith [hfw.1]
      set q := (c₁ - f p) / (f ((D.chart p hp).χ y) - f p) with hq
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hden.le
      have hq1 : q < 1 := (div_lt_one hden).2 (by linarith [hfw.1])
      obtain ⟨hmem, hfl⟩ := hscale (Real.sqrt q) (Real.sqrt_nonneg q)
        ((Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hq1))
      rw [Real.sq_sqrt hq0, hq, div_mul_cancel₀ _ hden.ne'] at hfl
      exact hU _ (by rw [hfl]; exact Or.inl ⟨by linarith, by linarith⟩) p hp hmem
    · have hden : 0 < f p - f ((D.chart p hp).χ y) := by linarith [hfw.2]
      set q := (f p - c₂) / (f p - f ((D.chart p hp).χ y)) with hq
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hden.le
      have hq1 : q < 1 := (div_lt_one hden).2 (by linarith [hfw.2])
      obtain ⟨hmem, hfl⟩ := hscale (Real.sqrt q) (Real.sqrt_nonneg q)
        ((Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hq1))
      rw [Real.sq_sqrt hq0, hq] at hfl
      have hfl' : f ((D.chart p hp).χ (Real.sqrt q • y)) = c₂ := by
        rw [hfl]; field_simp; ring
      exact hU _ (by rw [hfl']; exact Or.inr ⟨by linarith, le_rfl⟩) p hp hmem
  have hE1' : ∀ z, f z = τ + ε → (∀ r (hr : r ∈ crit), f r = τ →
      z ∉ (D.chart r hr).χ '' (D.chart r hr).rightModelSphere ε) →
      ∃ t, f (D.flow t z) = τ - ε := by
    intro z hfz hz
    have hzab : f z ∈ Ioo a b := ⟨by linarith, by linarith⟩
    by_cases hΩ : z ∈ D.regularFlowDomain (τ - ε)
    · exact ⟨f z - (τ - ε), f_π hf ⟨by linarith, by linarith⟩ hΩ⟩
    simp only [regularFlowDomain, mem_ofPred_eq, not_and, not_forall, not_not] at hΩ
    obtain ⟨s, hs, p, hp, hmem⟩ := hΩ hzab
    rw [hfz, show τ + ε - (τ - ε) = 2 * ε by ring, uIcc_of_le (by linarith)] at hs
    have hfs : f (D.flow s z) ∈ Icc (τ - ε) (τ + ε) :=
      ⟨by linarith [sub_le_f_flow (D := D) hf z hs.1, hs.2],
        by linarith [f_flow_le (D := D) hf z hs.1]⟩
    have hfp : f p = τ := hcls p hp _ hmem hfs
    obtain ⟨y, hy, hyz⟩ := hmem
    set d := D.chart p hp with hd
    have hy' : morseNorm n y ≤ d.r₀ := hy
    have hr0 := (hεr p hp).1
    have hrm := (hεr p hp).2
    have hrmR := (D.hrm p hp).2
    have hrm0 := D.rm_pos p hp
    have hyrm : morseNorm n y < D.rm p hp := hy'.trans_lt (D.r₀_lt_rm p hp)
    have hyR : morseNorm n y ≤ d.R := hyrm.le.trans hrmR
    have hnfy : f (d.χ y) = morseNormalForm d.hk (f p) y := d.hnorm y hyR
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      d.hk y
    have hm2 : morseNorm n y ^ 2 ≤ d.r₀ ^ 2 :=
      pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy' 2
    by_cases hu : negPart d.hk y = 0
    · exfalso
      by_cases hv : posPart d.hk y = 0
      · have := f_flow_le_f_p_of_posPart_eq_zero (D := D) hp hyrm hv (t := -s) (by linarith [hs.1])
        rw [hyz, flow_neg_flow, hfz, hfp] at this
        linarith
      · have hball : 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 < D.rm p hp ^ 2 := by
          rw [hu, norm_zero]; norm_num; linarith
        have hlevel : morseNormalForm d.hk (f p) y ≤ f p + ε := by
          rw [← hnfy, hyz, hfp]; exact hfs.2
        obtain ⟨t, ht0, hft, hstay, hprod⟩ := exists_exit_asc (D := D) hf hp hε hball hv hlevel
        rw [hu, norm_zero] at hprod
        have he : D.flow (-t) (d.χ y) = D.flow (s + -t) z := by rw [hyz, flow_flow]
        have hts : s + -t = 0 := huniq (τ + ε) hτum z _ _ (by rw [← he, hft, hfp])
          (by rw [flow_zero, hfz])
        have hez : D.flow (-t) (d.χ y) = z := by rw [he, hts, flow_zero]
        obtain ⟨y', hy'1, hy'e⟩ := hstay (-t) ⟨le_rfl, by linarith⟩
        have hy'1' : morseNorm n y' ^ 2 ≤ 2 * ε := by
          have : morseNorm n y' ^ 2 ≤ 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 := hy'1
          rw [hu, norm_zero] at this; linarith
        have hy'rm : morseNorm n y' < D.rm p hp :=
          lt_of_pow_lt_pow_left₀ 2 hrm0.le (by linarith)
        have hy'R : morseNorm n y' ≤ d.R := hy'rm.le.trans hrmR
        have hsymm : d.χ.symm (D.flow (-t) (d.χ y)) = y' := by
          rw [← hy'e, d.χ.left_inv (d.hsrc y' hy'R)]
        rw [hsymm] at hprod
        have hu' : negPart d.hk y' = 0 := by
          have h0 : 2 * ε * ‖negPart d.hk y'‖ ^ 2 ≤ 0 := by simpa using hprod
          have h1 : ‖negPart d.hk y'‖ ^ 2 ≤ 0 := by
            by_contra hc
            have := mul_pos (by linarith : (0 : ℝ) < 2 * ε) (not_le.1 hc)
            linarith
          have h2 : ‖negPart d.hk y'‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
          exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
        have hnf' : f (d.χ y') = morseNormalForm d.hk (f p) y' := d.hnorm y' hy'R
        rw [hy'e, hft, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
          hu', norm_zero] at hnf'
        apply hz p hp hfp
        rw [← hez, ← hy'e]
        exact ⟨y', ⟨hu', by linarith⟩, rfl⟩
    · have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm p hp ^ 2 := by
        linarith [sq_nonneg ‖negPart d.hk y‖]
      have hlevel : f p - ε ≤ morseNormalForm d.hk (f p) y := by
        rw [← hnfy, hyz, hfp]; exact hfs.1
      obtain ⟨t, ht0, hft, -⟩ := exists_exit_desc (D := D) hf hp hε hball hu hlevel
      refine ⟨s + t, ?_⟩
      rw [← flow_flow, ← hyz, hft, hfp]
  have hE2' : ∀ z, f z = τ - ε → (∀ r (hr : r ∈ crit), f r = τ →
      z ∉ (D.chart r hr).χ '' (D.chart r hr).leftModelSphere ε) →
      ∃ t, f (D.flow t z) = τ + ε := by
    intro z hfz hz
    have hzab : f z ∈ Ioo a b := ⟨by linarith, by linarith⟩
    by_cases hΩ : z ∈ D.regularFlowDomain (τ + ε)
    · exact ⟨f z - (τ + ε), f_π hf ⟨by linarith, by linarith⟩ hΩ⟩
    simp only [regularFlowDomain, mem_ofPred_eq, not_and, not_forall, not_not] at hΩ
    obtain ⟨s, hs, p, hp, hmem⟩ := hΩ hzab
    rw [hfz, show τ - ε - (τ + ε) = -(2 * ε) by ring, uIcc_of_ge (by linarith)] at hs
    have hfs : f (D.flow s z) ∈ Icc (τ - ε) (τ + ε) :=
      ⟨by linarith [le_f_flow_of_nonpos (D := D) hf z hs.2],
        by linarith [f_flow_le_sub_of_nonpos (D := D) hf z hs.2, hs.1]⟩
    have hfp : f p = τ := hcls p hp _ hmem hfs
    obtain ⟨y, hy, hyz⟩ := hmem
    set d := D.chart p hp with hd
    have hy' : morseNorm n y ≤ d.r₀ := hy
    have hr0 := (hεr p hp).1
    have hrm := (hεr p hp).2
    have hrmR := (D.hrm p hp).2
    have hrm0 := D.rm_pos p hp
    have hyrm : morseNorm n y < D.rm p hp := hy'.trans_lt (D.r₀_lt_rm p hp)
    have hyR : morseNorm n y ≤ d.R := hyrm.le.trans hrmR
    have hnfy : f (d.χ y) = morseNormalForm d.hk (f p) y := d.hnorm y hyR
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      d.hk y
    have hm2 : morseNorm n y ^ 2 ≤ d.r₀ ^ 2 :=
      pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy' 2
    by_cases hv : posPart d.hk y = 0
    · exfalso
      by_cases hu : negPart d.hk y = 0
      · have := f_p_le_f_flow_of_negPart_eq_zero (D := D) hp hyrm hu (t := -s) (by linarith [hs.2])
        rw [hyz, flow_neg_flow, hfz, hfp] at this
        linarith
      · have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm p hp ^ 2 := by
          rw [hv, norm_zero]; norm_num; linarith
        have hlevel : f p - ε ≤ morseNormalForm d.hk (f p) y := by
          rw [← hnfy, hyz, hfp]; exact hfs.1
        obtain ⟨t, ht0, hft, hstay, hprod⟩ := exists_exit_desc (D := D) hf hp hε hball hu hlevel
        rw [hv, norm_zero] at hprod
        have he : D.flow t (d.χ y) = D.flow (s + t) z := by rw [hyz, flow_flow]
        have hts : s + t = 0 := huniq (τ - ε) hτlm z _ _ (by rw [← he, hft, hfp])
          (by rw [flow_zero, hfz])
        have hez : D.flow t (d.χ y) = z := by rw [he, hts, flow_zero]
        obtain ⟨y', hy'1, hy'e⟩ := hstay t ⟨ht0, le_rfl⟩
        have hy'1' : morseNorm n y' ^ 2 ≤ 2 * ε := by
          have : morseNorm n y' ^ 2 ≤ 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 := hy'1
          rw [hv, norm_zero] at this; linarith
        have hy'rm : morseNorm n y' < D.rm p hp :=
          lt_of_pow_lt_pow_left₀ 2 hrm0.le (by linarith)
        have hy'R : morseNorm n y' ≤ d.R := hy'rm.le.trans hrmR
        have hsymm : d.χ.symm (D.flow t (d.χ y)) = y' := by
          rw [← hy'e, d.χ.left_inv (d.hsrc y' hy'R)]
        rw [hsymm] at hprod
        have hv' : posPart d.hk y' = 0 := by
          have h0 : 2 * ε * ‖posPart d.hk y'‖ ^ 2 ≤ 0 := by simpa using hprod
          have h1 : ‖posPart d.hk y'‖ ^ 2 ≤ 0 := by
            by_contra hc
            have := mul_pos (by linarith : (0 : ℝ) < 2 * ε) (not_le.1 hc)
            linarith
          have h2 : ‖posPart d.hk y'‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
          exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
        have hnf' : f (d.χ y') = morseNormalForm d.hk (f p) y' := d.hnorm y' hy'R
        rw [hy'e, hft, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
          hv', norm_zero] at hnf'
        apply hz p hp hfp
        rw [← hez, ← hy'e]
        exact ⟨y', ⟨hv', by linarith⟩, rfl⟩
    · have hball : 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 < D.rm p hp ^ 2 := by
        linarith [sq_nonneg ‖posPart d.hk y‖]
      have hlevel : morseNormalForm d.hk (f p) y ≤ f p + ε := by
        rw [← hnfy, hyz, hfp]; exact hfs.2
      obtain ⟨t, ht0, hft, -⟩ := exists_exit_asc (D := D) hf hp hε hball hv hlevel
      refine ⟨s + -t, ?_⟩
      rw [← flow_flow, ← hyz, hft, hfp]
  set A : Set M := f ⁻¹' {c₂} \ ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ),
    D.rightSphere x hx ε c₂ with hAdef
  set B : Set M := f ⁻¹' {c₁} \ ⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ),
    D.leftSphere x hx ε c₁ with hBdef
  have hmemA : ∀ x, x ∈ A ↔ f x = c₂ ∧ ∀ r (hr : r ∈ crit), f r = τ →
      x ∉ D.rightSphere r hr ε c₂ := by
    intro x
    simp only [hAdef, Set.mem_sdiff, mem_preimage, mem_singleton_iff, mem_iUnion, not_exists]
  have hmemB : ∀ y, y ∈ B ↔ f y = c₁ ∧ ∀ r (hr : r ∈ crit), f r = τ →
      y ∉ D.leftSphere r hr ε c₁ := by
    intro y
    simp only [hBdef, Set.mem_sdiff, mem_preimage, mem_singleton_iff, mem_iUnion, not_exists]
  have hE1 : ∀ x, f x = c₂ → (∀ r (hr : r ∈ crit), f r = τ → x ∉ D.rightSphere r hr ε c₂) →
      ∃ t, f (D.flow t x) = c₁ := by
    intro x hx hxS
    obtain ⟨hz, -⟩ := htrU.1 x hx
    obtain ⟨t, ht⟩ := hE1' _ hz (fun r hr hfr hmem => hxS r hr hfr
      ((D.mem_rightSphere_iff r hr ε c₂).2 (by rw [hfr]; exact hmem)))
    obtain ⟨hw, -⟩ := htrL.1 _ ht
    refine ⟨(c₂ - (τ + ε)) + t + (τ - ε - c₁), ?_⟩
    rw [← flow_flow, ← flow_flow]
    exact hw
  have hE2 : ∀ y, f y = c₁ → (∀ r (hr : r ∈ crit), f r = τ → y ∉ D.leftSphere r hr ε c₁) →
      ∃ t, f (D.flow t y) = c₂ := by
    intro y hy hyS
    obtain ⟨hz, -⟩ := htrL.2 y hy
    obtain ⟨t, ht⟩ := hE2' _ hz (fun r hr hfr hmem => hyS r hr hfr
      ((D.mem_leftSphere_iff r hr ε c₁).2 (by rw [hfr]; exact hmem)))
    obtain ⟨hw, -⟩ := htrU.2 _ ht
    refine ⟨(c₁ - (τ - ε)) + t + (τ + ε - c₂), ?_⟩
    rw [← flow_flow, ← flow_flow]
    exact hw
  obtain ⟨F, hF⟩ : ∃ F : M → M, ∀ x t, f (D.flow t x) = c₁ → F x = D.flow t x := by
    refine ⟨fun x => if h : ∃ t, f (D.flow t x) = c₁ then D.flow h.choose x else x, ?_⟩
    intro x t ht
    beta_reduce
    split_ifs with h
    · rw [huniq c₁ hc₁m x _ _ h.choose_spec ht]
    · exact absurd ⟨t, ht⟩ h
  obtain ⟨G, hG⟩ : ∃ G : M → M, ∀ y t, f (D.flow t y) = c₂ → G y = D.flow t y := by
    refine ⟨fun y => if h : ∃ t, f (D.flow t y) = c₂ then D.flow h.choose y else y, ?_⟩
    intro y t ht
    beta_reduce
    split_ifs with h
    · rw [huniq c₂ hc₂m y _ _ h.choose_spec ht]
    · exact absurd ⟨t, ht⟩ h
  have hFB : ∀ x ∈ A, F x ∈ B := by
    intro x hx
    obtain ⟨hx, hxS⟩ := (hmemA x).1 hx
    obtain ⟨t, ht⟩ := hE1 x hx hxS
    rw [hmemB, hF x t ht]
    refine ⟨ht, fun r hr hfr hmem => ?_⟩
    rw [D.mem_leftSphere_iff, hfr, D.flow_flow x t] at hmem
    have hw := (htrL.2 _ ht).1
    rw [D.flow_flow x t] at hw
    obtain ⟨y, ⟨hv, hu2⟩, hyw⟩ := hmem
    have hyrm : morseNorm n y < D.rm r hr := by
      have h1 := (D.chart r hr).morseNorm_sq_of_mem_leftModelSphere ⟨hv, hu2⟩
      exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos r hr).le (by linarith [(hεr r hr).2])
    set u := t + (c₁ - (τ - ε)) with hu
    rcases le_or_gt 0 u with h0 | h0
    · have := f_flow_le_f_p_of_posPart_eq_zero (D := D) hr hyrm hv (t := -u) (by linarith)
      rw [hyw, flow_neg_flow, hx, hfr] at this
      linarith
    · have := f_flow_le (D := D) hf (D.flow u x) (t := -u) (by linarith)
      rw [flow_neg_flow, hx, hw] at this
      linarith
  have hGA : ∀ y ∈ B, G y ∈ A := by
    intro y hy
    obtain ⟨hy, hyS⟩ := (hmemB y).1 hy
    obtain ⟨t, ht⟩ := hE2 y hy hyS
    rw [hmemA, hG y t ht]
    refine ⟨ht, fun r hr hfr hmem => ?_⟩
    rw [D.mem_rightSphere_iff, hfr, D.flow_flow y t] at hmem
    have hw := (htrU.1 _ ht).1
    rw [D.flow_flow y t] at hw
    obtain ⟨y', ⟨hu', hv2⟩, hyw⟩ := hmem
    have hyrm : morseNorm n y' < D.rm r hr := by
      have h1 := (D.chart r hr).morseNorm_sq_of_mem_rightModelSphere ⟨hu', hv2⟩
      exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos r hr).le (by linarith [(hεr r hr).2])
    set u := t + (c₂ - (τ + ε)) with hu
    rcases le_or_gt u 0 with h0 | h0
    · have := f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hyrm hu' (t := -u) (by linarith)
      rw [hyw, flow_neg_flow, hy, hfr] at this
      linarith
    · have := le_f_flow_of_nonpos (D := D) hf (D.flow u y) (t := -u) (by linarith)
      rw [flow_neg_flow, hy, hw] at this
      linarith
  have hGF : ∀ x ∈ A, G (F x) = x := by
    intro x hx
    obtain ⟨hx, hxS⟩ := (hmemA x).1 hx
    obtain ⟨t, ht⟩ := hE1 x hx hxS
    rw [hF x t ht, hG _ (-t) (by rw [flow_neg_flow]; exact hx), flow_neg_flow]
  have hFG : ∀ y ∈ B, F (G y) = y := by
    intro y hy
    obtain ⟨hy, hyS⟩ := (hmemB y).1 hy
    obtain ⟨t, ht⟩ := hE2 y hy hyS
    rw [hG y t ht, hF _ (-t) (by rw [flow_neg_flow]; exact hy), flow_neg_flow]
  have hreg₁ : ∀ x ∈ crit, f x ≠ c₁ := fun x hx hfx => by
    have := hslab x hx ⟨hfx.ge, by linarith⟩
    linarith
  have hreg₂ : ∀ x ∈ crit, f x ≠ c₂ := fun x hx hfx => by
    have := hslab x hx ⟨by linarith, hfx.le⟩
    linarith
  have hS₁ := (continuousOn_hitTime hf D h₁ (by linarith) hreg₁).2
  have hS₂ := (continuousOn_hitTime hf D (by linarith) h₂ hreg₂).2
  have hFc : ContinuousOn F A := by
    refine (hS₁.mono ?_).congr ?_
    · intro x hx
      obtain ⟨hx, hxS⟩ := (hmemA x).1 hx
      obtain ⟨t, ht⟩ := hE1 x hx hxS
      have ht0 : 0 ≤ t := by
        by_contra hneg
        have := le_f_flow_of_nonpos (D := D) hf x (t := t) (by linarith)
        rw [hx, ht] at this
        linarith
      refine ⟨t + 1, by linarith, ?_⟩
      have hle := f_flow_antitone (D := D) hf x (show t ≤ t + 1 by linarith)
      simp only at hle
      refine lt_of_le_of_ne (hle.trans_eq ht) fun heq => ?_
      have := huniq c₁ hc₁m x _ _ heq ht
      linarith
    · intro x hx
      obtain ⟨hx, hxS⟩ := (hmemA x).1 hx
      obtain ⟨t, ht⟩ := hE1 x hx hxS
      have ht0 : 0 ≤ t := by
        by_contra hneg
        have := le_f_flow_of_nonpos (D := D) hf x (t := t) (by linarith)
        rw [hx, ht] at this
        linarith
      have hd := (descend_spec hf D (t := c₁) (x := x) (by linarith) ⟨t, ht0, ht.le⟩).1
      exact hF x (D.hitTime c₁ x) hd
  have hGc : ContinuousOn G B := by
    intro y₀ hy₀
    obtain ⟨hy₀1, hy₀S⟩ := (hmemB y₀).1 hy₀
    obtain ⟨T, hT⟩ := hE2 y₀ hy₀1 hy₀S
    have hT0 : T ≤ 0 := by
      by_contra hpos
      have := f_flow_le (D := D) hf y₀ (t := T) (by linarith)
      rw [hy₀1, hT] at this
      linarith
    have hmaps : MapsTo (D.flow (T - 1)) B {x | ∃ s, 0 ≤ s ∧ f (D.flow s x) < c₂} := by
      intro y hy
      refine ⟨1 - T, by linarith, ?_⟩
      rw [D.flow_flow, show T - 1 + (1 - T) = 0 by ring, flow_zero, ((hmemB y).1 hy).1]
      linarith
    have hgc : ContinuousWithinAt (fun y => D.descend c₂ (D.flow (T - 1) y)) B y₀ :=
      (hS₂ _ (hmaps hy₀)).comp (D.continuous_flow (T - 1)).continuousWithinAt hmaps
    have hlt : c₂ < f (D.flow (T - 1) y₀) := by
      have hle := f_flow_antitone (D := D) hf y₀ (show T - 1 ≤ T by linarith)
      simp only at hle
      refine lt_of_le_of_ne (hT.symm.trans_le hle) fun heq => ?_
      have := huniq c₂ hc₂m y₀ _ _ heq.symm hT
      linarith
    have hN : ∀ᶠ y in 𝓝[B] y₀, c₂ < f (D.flow (T - 1) y) :=
      nhdsWithin_le_nhds ((hfc.comp (D.continuous_flow (T - 1))).continuousAt.eventually
        (lt_mem_nhds hlt))
    have heq : G =ᶠ[𝓝[B] y₀] fun y => D.descend c₂ (D.flow (T - 1) y) := by
      filter_upwards [hN, self_mem_nhdsWithin] with y hy hyB
      have hyc : f y = c₁ := ((hmemB y).1 hyB).1
      have hd := (descend_spec hf D (t := c₂) (x := D.flow (T - 1) y) hy.le
        ⟨1 - T, by linarith, by
          rw [D.flow_flow, show T - 1 + (1 - T) = 0 by ring, flow_zero, hyc]
          linarith⟩).1
      have hd' : f (D.flow ((T - 1) + D.hitTime c₂ (D.flow (T - 1) y)) y) = c₂ := by
        rw [← D.flow_flow]; exact hd
      rw [hG y _ hd', ← D.flow_flow]
      rfl
    exact hgc.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hy₀)
  exact ⟨{
    toFun := fun x => ⟨F x, hFB x x.2⟩
    invFun := fun y => ⟨G y, hGA y y.2⟩
    left_inv := fun x => Subtype.ext (hGF x x.2)
    right_inv := fun y => Subtype.ext (hFG y y.2)
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.1 hFc).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.1 hGc).subtype_mk _ }⟩

end GradientLikeStrip

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem isHomotopyEquivInclusion_slab (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ) :
    isHomotopyEquivInclusion (f ⁻¹' Icc a t) (f ⁻¹' Icc a t' \ D.slabCap τ) := by
  classical
  have _hcrit := hcrit
  clear _hcrit hcrit
  have hcap_ge : ∀ (r : M) (hr : r ∈ crit) (y : M), y ∈ D.captured r hr → f r ≤ f y := by
    intro r hr y hy
    obtain ⟨T, z, ⟨hz1, hz2⟩, hzx⟩ := hy
    have h1 := f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hz1 hz2 (t := max T 0 - T)
      (by linarith [le_max_left T 0])
    rw [hzx, flow_flow, add_sub_cancel] at h1
    exact h1.trans (f_flow_le (D := D) hf y (le_max_right T 0))
  have hcap_below : ∀ (r : M) (hr : r ∈ crit) (y : M), y ∈ D.captured r hr → f r < t →
      ∃ s, 0 ≤ s ∧ f (D.flow s y) < t := by
    intro r hr y hy hlt
    have hρ : 0 < min (D.rm r hr) (Real.sqrt (t - f r)) :=
      lt_min (D.rm_pos r hr) (Real.sqrt_pos.2 (by linarith))
    obtain ⟨T, hT⟩ := captured_eventually_small (D := D) hy hρ
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hT (max T 0) (le_max_left _ _)
    refine ⟨max T 0, le_max_right _ _, ?_⟩
    have hzR : morseNorm n z ≤ (D.chart r hr).R :=
      hz1.le.trans ((min_le_left _ _).trans (D.hrm r hr).2)
    rw [← hzx, (D.chart r hr).hnorm z hzR,
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hz2, norm_zero]
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart r hr).hk z
    rw [hz2, norm_zero] at hsq
    have hm : morseNorm n z < Real.sqrt (t - f r) := hz1.trans_le (min_le_right _ _)
    have hm2 : morseNorm n z ^ 2 < t - f r :=
      (Real.lt_sqrt (ModelField.morseNorm_nonneg z)).1 hm
    nlinarith
  have hAB : f ⁻¹' Icc a t ⊆ f ⁻¹' Icc a t' \ D.slabCap τ := by
    intro y hy
    refine ⟨⟨hy.1, hy.2.trans (by linarith)⟩, fun hcap => ?_⟩
    simp only [slabCap, mem_iUnion] at hcap
    obtain ⟨x, hx, hfx, hyx⟩ := hcap
    have := hcap_ge x hx y hyx
    have h2 : f y ≤ t := hy.2
    linarith
  have hW : ∀ y ∈ f ⁻¹' Icc a t' \ D.slabCap τ, ∃ s, 0 ≤ s ∧ f (D.flow s y) < t := by
    rintro y ⟨hy, hyc⟩
    rcases trichotomy (D := D) hf hε hεr ⟨hy.1, hy.2.trans ht'⟩ with ⟨s, hs, hlt⟩ | ⟨r, hr, hyr⟩
    · exact ⟨s, hs, hlt.trans_le ht⟩
    · rcases lt_or_ge (f r) t with hlt | hge
      · exact hcap_below r hr y hyr hlt
      · exfalso
        have hfr : f r = τ := hslab r hr ⟨hge, (hcap_ge r hr y hyr).trans hy.2⟩
        exact hyc (mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hr, mem_iUnion.2 ⟨hfr, hyr⟩⟩⟩)
  have hT0 : ∀ y, f y ≤ t → D.hitTime t y = 0 := by
    intro y hy
    unfold hitTime
    refine IsLeast.csInf_eq ⟨⟨le_rfl, ?_⟩, fun s hs => hs.1⟩
    rwa [flow_zero]
  have hreg : ∀ x ∈ crit, f x ≠ t := by
    intro x hx hxt
    have := hslab x hx ⟨hxt.ge, by linarith⟩
    linarith
  have hcont := (D.continuousOn_hitTime hf ht (by linarith) hreg).1
  set B : Set M := f ⁻¹' Icc a t' \ D.slabCap τ with hBdef
  set Hd : unitInterval × M → M := fun p => D.flow ((p.1 : ℝ) * D.hitTime t p.2) p.2 with hHd
  have hc : ContinuousOn Hd (univ ×ˢ B) := by
    have hin : ContinuousOn (fun p : unitInterval × M => ((p.1 : ℝ) * D.hitTime t p.2, p.2))
        (univ ×ˢ B) := by
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      refine (continuous_subtype_val.comp continuous_fst).continuousOn.mul ?_
      exact hcont.comp continuousOn_snd (fun p hp => hW p.2 hp.2)
    exact D.continuous_flow_joint.comp_continuousOn hin
  have h0 : ∀ y ∈ B, Hd (0, y) = y := by
    intro y _
    simp [hHd, flow_zero]
  have h1 : ∀ y ∈ B, Hd (1, y) ∈ f ⁻¹' Icc a t := by
    intro y hy
    change f (D.flow (((1 : unitInterval) : ℝ) * D.hitTime t y) y) ∈ Icc a t
    rw [Set.Icc.coe_one, one_mul]
    rcases le_or_gt (f y) t with hle | hgt
    · rw [hT0 y hle, flow_zero]
      exact ⟨hy.1.1, hle⟩
    · obtain ⟨s, hs, hlt⟩ := hW y hy
      have hd := D.descend_spec hf hgt.le ⟨s, hs, hlt.le⟩
      have hd1 : f (D.flow (D.hitTime t y) y) = t := hd.1
      rw [hd1]
      exact ⟨ht, le_rfl⟩
  have hB : ∀ s, ∀ y ∈ B, Hd (s, y) ∈ B := by
    intro s y hy
    change D.flow ((s : ℝ) * D.hitTime t y) y ∈ f ⁻¹' Icc a t' \ D.slabCap τ
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    rcases le_or_gt (f y) t with hle | hgt
    · rw [hT0 y hle, mul_zero, flow_zero]
      exact hy
    · obtain ⟨s', hs', hlt'⟩ := hW y hy
      obtain ⟨hdf, hd0, hdlt⟩ := D.descend_spec hf hgt.le ⟨s', hs', hlt'.le⟩
      have hst : 0 ≤ (s : ℝ) * D.hitTime t y := mul_nonneg hs0 hd0
      refine ⟨⟨?_, (f_flow_le (D := D) hf y hst).trans hy.1.2⟩, fun hc => ?_⟩
      · rcases (mul_le_of_le_one_left hd0 hs1).lt_or_eq with hlt | heq
        · exact ht.trans (hdlt _ hst hlt).le
        · rw [heq]
          have hd1 : f (D.flow (D.hitTime t y) y) = t := hdf
          rw [hd1]
          exact ht
      · apply hy.2
        simp only [slabCap, mem_iUnion] at hc ⊢
        obtain ⟨x, hx, hfx, hxc⟩ := hc
        exact ⟨x, hx, hfx, (flow_mem_captured_iff _).1 hxc⟩
  have hA : ∀ s, ∀ y ∈ f ⁻¹' Icc a t, Hd (s, y) = y := by
    intro s y hy
    change D.flow ((s : ℝ) * D.hitTime t y) y = y
    rw [hT0 y hy.2, mul_zero, flow_zero]
  have hcont' : Continuous fun p : unitInterval × B => Hd (p.1, (p.2 : M)) :=
    hc.comp_continuous (by fun_prop) fun p => ⟨mem_univ _, p.2.2⟩
  let r : C(B, f ⁻¹' Icc a t) :=
    ⟨fun x => ⟨Hd (1, x), h1 x x.2⟩,
      (hcont'.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let i : C(f ⁻¹' Icc a t, B) := ⟨fun a => ⟨a, hAB a.2⟩, by fun_prop⟩
  refine ⟨⟨i, r, ?_, ?_⟩, fun _ => rfl⟩
  · have : r.comp i = ContinuousMap.id (f ⁻¹' Icc a t) := by
      ext a
      exact hA 1 a a.2
    rw [this]
  · refine ContinuousMap.Homotopic.symm ⟨?_⟩
    exact
      { toFun := fun p => ⟨Hd (p.1, p.2), hB p.1 p.2 p.2.2⟩
        continuous_toFun := hcont'.subtype_mk _
        map_zero_left := fun x => Subtype.ext (h0 x x.2)
        map_one_left := fun _ => rfl }

theorem isIso_inclPair_slab (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ) :
    ∃ h : f ⁻¹' Icc a t ⊆ f ⁻¹' Icc a t' \ D.slabCap τ, ∀ j,
      CategoryTheory.IsIso (Handle.inclPair (subset_refl (f ⁻¹' Icc a t')) h j) := by
  have h : f ⁻¹' Icc a t ⊆ f ⁻¹' Icc a t' \ D.slabCap τ := by
    intro y hy
    refine ⟨⟨hy.1, hy.2.trans (by linarith)⟩, ?_⟩
    intro hyc
    simp only [slabCap, mem_iUnion] at hyc
    obtain ⟨x, hx, hxτ, hyx⟩ := hyc
    have h1 := f_le_of_mem_captured hf hyx 0
    rw [flow_zero] at h1
    have h2 : f y ≤ t := hy.2
    linarith
  refine ⟨h, fun j => ?_⟩
  have hB : isHomotopyEquivInclusion (f ⁻¹' Icc a t') (f ⁻¹' Icc a t') :=
    ⟨ContinuousMap.HomotopyEquiv.refl _, fun _ => rfl⟩
  have hA := isHomotopyEquivInclusion_slab hf D hcrit hε hεr ht htτ hτt' ht' hslab
  exact SingularPair.isIso_relativeHomologyMap_inclOfLE_of_homotopyEquiv SingularPair.integerCoefficients
    (fun y hy => (h hy).1) sdiff_subset (subset_refl _) h hB hA j

theorem isOpen_tube (D : GradientLikeStrip I f a b crit) {x : M} (hx : x ∈ crit) (δ : ℝ) :
    IsOpen (D.tube x hx δ) := by
  have hO : IsOpen ((D.chart x hx).χ ''
      {z | morseNorm n z < D.rm x hx ∧ ‖negPart (D.chart x hx).hk z‖ < δ}) := by
    refine ((D.chart x hx).χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2
      ((isOpen_morseNorm_lt (D.rm x hx)).inter
        (isOpen_lt (continuous_norm.comp
          (DifferentialGeometry.Topology.Morse.CellAttachment.continuous_negPart
            (D.chart x hx).hk)) continuous_const))
    exact (D.chart x hx).hball
      (mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy.1 (D.rm_lt_R' x hx).le))
  have : D.tube x hx δ = ⋃ s ∈ Ici (0 : ℝ), D.flow s ⁻¹' ((D.chart x hx).χ ''
      {z | morseNorm n z < D.rm x hx ∧ ‖negPart (D.chart x hx).hk z‖ < δ}) := by
    ext y
    simp only [tube, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_Ici, exists_prop]
  rw [this]
  exact isOpen_biUnion fun s _ => hO.preimage (D.continuous_flow s)

theorem isIso_excise_tubes (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    CategoryTheory.IsIso (Handle.inclPair
      (inter_subset_left : f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ),
        D.tube x hx δ) ⊆ f ⁻¹' Icc a t')
      (sdiff_subset_sdiff_left inter_subset_left :
        (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
          D.slabCap τ ⊆ f ⁻¹' Icc a t' \ D.slabCap τ) j) := by
  classical
  have _unused := And.intro hcrit (And.intro ht hτt')
  clear _unused
  have hBB : f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) ⊆
      f ⁻¹' Icc a t' := inter_subset_left
  have hTopen : IsOpen (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx => isOpen_iUnion fun _ => isOpen_tube D hx δ
  have hkey : ∀ p ∈ f ⁻¹' Icc a t',
      p ∉ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) →
      ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ Disjoint N (D.slabCap τ) := by
    intro p hp hpT
    have hpab : f p ∈ Icc a b := ⟨hp.1, hp.2.trans ht'⟩
    rcases trichotomy hf hε hεr hpab with hbot | ⟨r, hr, hpr⟩
    · refine ⟨D.bottom, D.isOpen_bottom hf.continuous, hbot, ?_⟩
      refine Set.disjoint_left.2 fun y hyN hyC => ?_
      simp only [slabCap, mem_iUnion] at hyC
      obtain ⟨x, hx, -, hyx⟩ := hyC
      exact Set.disjoint_left.1 (disjoint_bottom_captured hf x hx) hyN hyx
    · have hfr : f r ≤ f p := by simpa using f_le_of_mem_captured hf hpr 0
      have hrτ : f r < τ := by
        by_contra hcon
        replace hcon : τ ≤ f r := not_lt.1 hcon
        have hrcrit : f r ∈ Icc t t' := ⟨by linarith, hfr.trans hp.2⟩
        have hr_eq := hslab r hr hrcrit
        apply hpT
        obtain ⟨T0, hT0⟩ := mem_captured_iff_eventually.1 hpr
        refine mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hr, mem_iUnion.2 ⟨hr_eq, ?_⟩⟩⟩
        refine ⟨max T0 0, le_max_right _ _, ?_⟩
        refine image_mono ?_ (hT0 _ (le_max_left _ _))
        rintro z ⟨hz1, hz2⟩
        refine ⟨hz1, ?_⟩
        rw [hz2, norm_zero]
        exact hδ
      obtain ⟨ρ, hρ, hρexit⟩ :=
        exists_uniform_exit hf r hr hε (hεr r hr).2 isOpen_univ (subset_univ _)
      have hρ' : 0 < min ρ (D.rm r hr) := lt_min hρ (D.rm_pos r hr)
      obtain ⟨T0, hT0⟩ := captured_eventually_small hpr hρ'
      refine ⟨D.flow T0 ⁻¹' ((D.chart r hr).χ '' {z | morseNorm n z < min ρ (D.rm r hr)}),
        ((D.chart r hr).isOpen_image_of_lt
          ((min_le_right _ _).trans (D.rm_lt_R' r hr).le)).preimage (D.continuous_flow T0),
        image_mono (fun z hz => hz.1) (hT0 T0 le_rfl), ?_⟩
      refine Set.disjoint_left.2 fun y hyN hyC => ?_
      simp only [slabCap, mem_iUnion] at hyC
      obtain ⟨x, hx, hxτ, hyx⟩ := hyC
      obtain ⟨z, hz, hzy⟩ := hyN
      have hz' : morseNorm n z < min ρ (D.rm r hr) := hz
      have hlow : ∃ s, f (D.flow s y) < τ := by
        by_cases hu : negPart (D.chart r hr).hk z = 0
        · have hyr : y ∈ D.captured r hr :=
            ⟨T0, z, ⟨hz'.trans_le (min_le_right _ _), hu⟩, hzy⟩
          obtain ⟨s, hs⟩ := exists_f_flow_lt_of_mem_captured hyr (η := τ - f r) (by linarith)
          exact ⟨s, by linarith⟩
        · obtain ⟨s, -, -, hs⟩ := hρexit z (hz'.trans_le (min_le_left _ _)) hu
          rw [hzy, flow_flow] at hs
          exact ⟨T0 + s, by rw [hs]; linarith⟩
      obtain ⟨s, hs⟩ := hlow
      have := f_le_of_mem_captured hf hyx s
      linarith
  let X : TopCat := TopCat.of ↥(f ⁻¹' Icc a t')
  let U : Set X := Subtype.val ⁻¹'
    (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ))
  let V : Set X := Subtype.val ⁻¹' (f ⁻¹' Icc a t' \ D.slabCap τ)
  have hcov : interior U ∪ interior V = Set.univ := by
    refine eq_univ_of_forall fun q => ?_
    by_cases hq : q.1 ∈ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)
    · left
      refine interior_maximal ?_ (hTopen.preimage continuous_subtype_val) hq
      intro y hy
      exact ⟨y.2, hy⟩
    · right
      obtain ⟨N, hN, hpN, hdisj⟩ := hkey q.1 q.2 hq
      refine interior_maximal ?_ (hN.preimage continuous_subtype_val) hpN
      intro y hy
      exact ⟨y.2, fun hc => Set.disjoint_left.1 hdisj hy hc⟩
  have hexc := SingularPair.excision SingularPair.integerCoefficients hcov j
  let e := (homeomorphPreimageVal hBB).symm
  have himg : e '' (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩
      (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \ D.slabCap τ)) =
      Subtype.val ⁻¹' V :=
    SingularPair.homeomorph_image_eq_of_mem_iff e
      fun x => ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨x.2, h.2⟩⟩
  have hiso1 := SingularPair.isIso_relativeHomologyMap_homeoHom SingularPair.integerCoefficients e himg
    (SingularPair.mapsTo_homeoHom e himg) j
  have hcomp : SingularPair.inclOfLE (X := TopCat.of M) hBB =
      CategoryTheory.CategoryStruct.comp (SingularPair.homeoHom e) (SingularPair.incl X U) := rfl
  unfold Handle.inclPair
  rw [SingularPair.relativeHomologyMap_eq_of_eq SingularPair.integerCoefficients hcomp,
    SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients _ _ (SingularPair.mapsTo_homeoHom e himg)
      (SingularPair.mapsTo_incl U V)]
  infer_instance

theorem tube_disjoint (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {ε : ℝ} (hε : 0 < ε) (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2)
    {τ : ℝ} : ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ x (hx : x ∈ crit) y (hy : y ∈ crit), f x = τ → f y = τ → x ≠ y →
        Disjoint (D.tube x hx δ) (D.tube y hy δ) := by
  have hsplit := @DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split
  have hnsq := @DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
  refine ⟨Real.sqrt ε, Real.sqrt_pos.2 hε, fun δ hδ hδε x hx y hy hfx hfy hxy => ?_⟩
  have hδ2 : δ ^ 2 < ε := by
    have h1 := Real.sq_sqrt hε.le
    have h2 : δ ^ 2 < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ hδε hδ.le two_ne_zero
    linarith
  have alg : ∀ (a b a₁ b₁ r : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ a₁ → 0 ≤ b₁ → 0 < r → a ≤ a₁ →
      b * a = b₁ * a₁ → b ≤ 2 * ε + a → b₁ ≤ δ ^ 2 → b₁ + a₁ < r ^ 2 →
      b + a ≤ max (b₁ + a₁) (2 * ε + 2 * (r * δ)) := by
    intro a b a₁ b₁ r ha0 hb0 ha₁0 hb₁0 hr hv hprod hba hu2 hw
    rcases le_or_gt b a with hab | hab
    · refine le_max_of_le_left ?_
      rcases eq_or_lt_of_le ha₁0 with h0 | h0
      · have : a = 0 := le_antisymm (h0 ▸ hv) ha0
        linarith
      · have hm : 0 ≤ (a₁ - a) * (a₁ - b) := mul_nonneg (by linarith) (by linarith)
        have : a₁ * (b + a) ≤ a₁ * (b₁ + a₁) := by nlinarith
        exact le_of_mul_le_mul_left this h0
    · refine le_max_of_le_right ?_
      have h2 : b₁ * a₁ ≤ δ ^ 2 * r ^ 2 := by
        have : a₁ < r ^ 2 := by linarith
        exact mul_le_mul hu2 this.le ha₁0 (sq_nonneg _)
      have h1 : a * a ≤ b * a := mul_le_mul_of_nonneg_right hab.le ha0
      have hsq : a ^ 2 ≤ (r * δ) ^ 2 := by
        have : (r * δ) ^ 2 = δ ^ 2 * r ^ 2 := by ring
        rw [this, sq]
        linarith
      have : a ≤ r * δ := (pow_le_pow_iff_left₀ ha0 (by positivity) two_ne_zero).1 hsq
      linarith
  have key : ∀ (x : M) (hx : x ∈ crit) (y : M) (hy : y ∈ crit), f x = τ → f y = τ → x ≠ y →
      ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx → ‖negPart (D.chart x hx).hk w‖ < δ →
      ∀ T : ℝ, 0 ≤ T → D.flow T ((D.chart x hx).χ w) ∈ (D.chart y hy).χ ''
        {z | morseNorm n z < D.rm y hy ∧ ‖negPart (D.chart y hy).hk z‖ < δ} → False := by
    intro x hx y hy hfx hfy hxy w hw hu T hT hq
    have hrm := D.rm_pos x hx
    have hrm8 := (hεr x hx).2
    have hrmR' := D.rm_lt_R' x hx
    obtain ⟨w₂, ⟨hw₂, hu₂⟩, hqw₂⟩ := hq
    have hfq : τ - ε ≤ f (D.flow T ((D.chart x hx).χ w)) := by
      have hle : (D.chart y hy).χ w₂ ∈ (D.chart y hy).χ ''
          {z | morseNorm n z ≤ (D.chart y hy).R} :=
        D.modelBall_subset_image_le y hy ⟨w₂, hw₂, rfl⟩
      rw [← hqw₂, (D.chart y hy).f_eq_nf_symm hle,
        (D.chart y hy).χ.left_inv ((D.chart y hy).hsrc w₂ (hw₂.le.trans (D.hrm y hy).2)),
        hsplit, hfy]
      have : ‖negPart (D.chart y hy).hk w₂‖ ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hu₂.le 2
      nlinarith [sq_nonneg ‖posPart (D.chart y hy).hk w₂‖]
    set B := max (morseNorm n w ^ 2) (2 * ε + 2 * (D.rm x hx * δ)) with hB
    have hBrm : B < D.rm x hx ^ 2 := by
      apply max_lt
      · exact pow_lt_pow_left₀ hw (ModelField.morseNorm_nonneg w) two_ne_zero
      · by_contra hcon
        push Not at hcon
        have h0 : 0 ≤ D.rm x hx ^ 2 - 2 * ε := by nlinarith
        have h3 : (D.rm x hx ^ 2 - 2 * ε) ^ 2 ≤ (2 * (D.rm x hx * δ)) ^ 2 :=
          pow_le_pow_left₀ h0 (by linarith) 2
        have h4 : (2 * (D.rm x hx * δ)) ^ 2 = 4 * D.rm x hx ^ 2 * δ ^ 2 := by ring
        have h5 : D.rm x hx ^ 2 * δ ^ 2 ≤ D.rm x hx ^ 2 * ε :=
          mul_le_mul_of_nonneg_left hδ2.le (sq_nonneg _)
        nlinarith [sq_nonneg (D.rm x hx ^ 2), mul_pos hε (pow_pos hrm 2)]
    have hB0 : 0 ≤ B := le_max_of_le_left (sq_nonneg _)
    set S : Set (Fin n → ℝ) := {z | morseNorm n z ^ 2 ≤ B} with hS
    set O := (D.chart x hx).χ '' {z | morseNorm n z < D.rm x hx} with hO
    have hOopen : IsOpen O := D.isOpen_modelBall x hx
    have hSsub : S ⊆ {z | morseNorm n z < D.rm x hx} := fun z hz =>
      lt_of_pow_lt_pow_left₀ 2 hrm.le (lt_of_le_of_lt hz hBrm)
    have hSsub' : S ⊆ {z | morseNorm n z ≤ Real.sqrt B} := fun z hz =>
      MorseNormalChart.morseNorm_le_sqrt_of_sq_le hz
    have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
    have hSK : IsCompact ((D.chart x hx).χ '' S) :=
      (D.chart x hx).isCompact_image_of_subset
        ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
        (((Real.sqrt_lt' hrm).2 hBrm).trans hrmR') hSsub'
    have hKO : (D.chart x hx).χ '' S ⊆ O := image_mono hSsub
    have hOball := D.modelBall_subset_image_ball x hx
    have hOle := D.modelBall_subset_image_le x hx
    have hwS : w ∈ S := by
      change morseNorm n w ^ 2 ≤ B
      exact le_max_left _ _
    have hγ0 : (D.chart x hx).χ.symm (D.flow 0 ((D.chart x hx).χ w)) = w := by
      rw [D.flow_zero, (D.chart x hx).χ.left_inv
        ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hw.trans hrmR')))]
    have hnf : ∀ s, D.flow s ((D.chart x hx).χ w) ∈ O →
        f (D.flow s ((D.chart x hx).χ w)) = morseNormalForm (D.chart x hx).hk (f x)
          ((D.chart x hx).χ.symm (D.flow s ((D.chart x hx).χ w))) :=
      fun s hs => (D.chart x hx).f_eq_nf_symm (hOle hs)
    have hu2 : ‖negPart (D.chart x hx).hk w‖ ^ 2 ≤ δ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hu.le 2
    have hw2 : morseNorm n w ^ 2 < D.rm x hx ^ 2 :=
      pow_lt_pow_left₀ hw (ModelField.morseNorm_nonneg w) two_ne_zero
    have hw2' := hnsq (D.chart x hx).hk w
    have claim : ∀ s ∈ Icc 0 T, D.flow s ((D.chart x hx).χ w) ∈ (D.chart x hx).χ '' S := by
      have hQc : IsClosed {s : ℝ | D.flow s ((D.chart x hx).χ w) ∈ (D.chart x hx).χ '' S} :=
        hSK.isClosed.preimage (D.continuous_flow_curve _)
      refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
      · change D.flow 0 ((D.chart x hx).χ w) ∈ (D.chart x hx).χ '' S
        rw [D.flow_zero]; exact ⟨w, hwS, rfl⟩
      · intro t ht hIcc
        have htO : D.flow t ((D.chart x hx).χ w) ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
        obtain ⟨δ', hδ', hδO⟩ := D.exists_Icc_flow_mem_open hOopen htO
        refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + δ') T, ?_, fun s hs => ?_⟩
        · change t < min (t + δ') T
          exact lt_min (by linarith) ht.2
        change D.flow s ((D.chart x hx).χ w) ∈ (D.chart x hx).χ '' S
        have hs0 : 0 ≤ s := ht.1.trans hs.1.le
        have hsT : s ≤ T := hs.2.trans (min_le_right _ _)
        have hODE : ∀ u ∈ Icc 0 s, D.flow u ((D.chart x hx).χ w) ∈ O := fun u hu => by
          rcases le_or_gt u t with h | h
          · exact hKO (hIcc ⟨hu.1, h⟩)
          · exact hδO u ⟨by linarith, hu.2.trans (hs.2.trans (min_le_left _ _))⟩
        have hγ := hasDerivAt_symm_flow_Icc hx hODE
        have hv := ModelField.normSq_posPart_antitoneOn (D.chart x hx).hk (D.chart x hx).hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
        have hprod := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ s
          (right_mem_Icc.2 hs0)
        simp only [hγ0] at hv hprod
        have hlev : τ - ε ≤ f (D.flow s ((D.chart x hx).χ w)) :=
          hfq.trans (f_flow_antitone hf _ hsT)
        rw [hnf s (hODE s (right_mem_Icc.2 hs0)), hsplit, hfx] at hlev
        refine (D.chart x hx).mem_image_of_symm_mem (hOball (hODE s (right_mem_Icc.2 hs0))) ?_
        change morseNorm n ((D.chart x hx).χ.symm (D.flow s ((D.chart x hx).χ w))) ^ 2 ≤ B
        rw [hnsq (D.chart x hx).hk, hB, hw2']
        exact alg _ _ _ _ (D.rm x hx) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
          hrm hv hprod (by linarith) hu2 (by linarith)
    have hqS := claim T (right_mem_Icc.2 hT)
    have h1 : D.flow T ((D.chart x hx).χ w) ∈
        (D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R' := hOball (hKO hqS)
    have h2 : D.flow T ((D.chart x hx).χ w) ∈
        (D.chart y hy).χ '' Metric.ball 0 (D.chart y hy).R' :=
      hqw₂ ▸ D.modelBall_subset_image_ball y hy ⟨w₂, hw₂, rfl⟩
    exact Set.disjoint_left.1 (D.disjoint x hx y hy hxy) h1 h2
  rw [Set.disjoint_left]
  rintro z ⟨s₁, hs₁, w₁, ⟨hw₁, hu₁⟩, hzw₁⟩ ⟨s₂, hs₂, hz₂⟩
  rcases le_total s₁ s₂ with h | h
  · refine key x hx y hy hfx hfy hxy w₁ hw₁ hu₁ (s₂ - s₁) (sub_nonneg.2 h) ?_
    rw [hzw₁, D.flow_flow]
    have he : s₁ + (s₂ - s₁) = s₂ := by ring
    rw [he]
    exact hz₂
  · obtain ⟨w₂, ⟨hw₂, hu₂⟩, hzw₂⟩ := hz₂
    refine key y hy x hx hfy hfx hxy.symm w₂ hw₂ hu₂ (s₁ - s₂) (sub_nonneg.2 h) ?_
    rw [hzw₂, D.flow_flow]
    have he : s₂ + (s₁ - s₂) = s₁ := by ring
    rw [he]
    exact ⟨w₁, ⟨hw₁, hu₁⟩, hzw₁⟩

theorem tubeCoord_spec (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw)
    {x : M} (hx : x ∈ crit) (hxτ : f x = τ) {μ : ℕ} (hμ : (D.chart x hx).k = μ) :
    ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ContinuousOn (D.tubeCoordE x hx ε μ) (f ⁻¹' Icc a t' ∩ D.tube x hx δ) ∧
      ∀ z ∈ f ⁻¹' Icc a t' ∩ D.tube x hx δ, (D.tubeCoordE x hx ε μ z = 0 ↔ z ∈ D.slabCap τ) := by
  have _ := hcrit
  subst hxτ
  subst hμ
  obtain ⟨δ₁, hδ₁, hdisj⟩ := tube_disjoint hf D hε hεr (τ := f x)
  have hrm : 0 < D.rm x hx := D.rm_pos x hx
  have hrmR : D.rm x hx ≤ (D.chart x hx).R := (D.hrm x hx).2
  have hrmR' : D.rm x hx < (D.chart x hx).R' := D.rm_lt_R' x hx
  have h8 : 8 * ε < D.rm x hx ^ 2 := (hεr x hx).2
  have hr₀ := (D.chart x hx).hr₀
  refine ⟨min (Real.sqrt ε) (min (ε / D.rm x hx) δ₁),
    lt_min (Real.sqrt_pos.2 hε) (lt_min (div_pos hε hrm) hδ₁), ?_⟩
  intro δ hδ hδlt
  have hδs : δ < Real.sqrt ε := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδr : δ < ε / D.rm x hx :=
    lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < δ₁ := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))
  have hδε : δ ^ 2 < ε := (Real.lt_sqrt hδ.le).1 hδs
  have hδrm : δ ^ 2 * D.rm x hx ^ 2 < ε ^ 2 := by
    have h1 : δ * D.rm x hx < ε := (lt_div_iff₀ hrm).1 hδr
    have h2 : 0 ≤ δ * D.rm x hx := by positivity
    nlinarith
  set c := f x + ε with hc
  have hcab : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hcU : ∀ y, f y = c → dfV I f D.V y = -1 := fun y hy =>
    D.dfV_eq_neg_one_of_level hcab
      (fun p hp w hw hwc => hU w (by rw [hwc]; exact ⟨le_rfl, hτt'.le⟩) p hp hw) hy
  have hsplit : ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx →
      f ((D.chart x hx).χ w) = f x + (1 / 2) *
        (‖posPart (D.chart x hx).hk w‖ ^ 2 - ‖negPart (D.chart x hx).hk w‖ ^ 2) := by
    intro w hw
    rw [(D.chart x hx).hnorm w (hw.le.trans hrmR),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
  have hsq : ∀ w : Fin n → ℝ, morseNorm n w ^ 2 =
      ‖negPart (D.chart x hx).hk w‖ ^ 2 + ‖posPart (D.chart x hx).hk w‖ ^ 2 := fun w =>
    DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart x hx).hk w
  have hleft : ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx →
      (D.chart x hx).χ.symm ((D.chart x hx).χ w) = w := fun w hw =>
    (D.chart x hx).χ.left_inv ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hw.trans hrmR')))
  have htc : ∀ z, D.tubeCoord x hx ε z =
      negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z)) := by
    intro z
    unfold GradientLikeStrip.tubeCoord GradientLikeStrip.rightCoord
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith), flow_zero]
  have hE : ∀ z, D.tubeCoordE x hx ε (D.chart x hx).k z = D.tubeCoord x hx ε z := by
    intro z
    ext i
    simp [GradientLikeStrip.tubeCoordE]
  have key : ∀ z, z ∈ D.tube x hx δ → f z ∈ Icc a t' →
      ∃ w, morseNorm n w < D.rm x hx ∧ ‖negPart (D.chart x hx).hk w‖ ^ 2 < ε ∧
        f (D.flow (max (f z - c) 0) z) ≤ c ∧
        (D.chart x hx).χ w = D.flow (max (f z - c) 0) z := by
    intro z hzT hzI
    obtain ⟨s₀, hs₀, w₀, ⟨hw₀rm, hw₀u⟩, hQ⟩ := hzT
    have hu₀ : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hw₀u (norm_nonneg _) two_ne_zero
    have hsq₀ := hsq w₀
    have hw₀sq : morseNorm n w₀ ^ 2 < D.rm x hx ^ 2 :=
      pow_lt_pow_left₀ hw₀rm (ModelField.morseNorm_nonneg w₀) two_ne_zero
    have hprod₀ : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 <
        ε ^ 2 := by
      have hb₀ : ‖posPart (D.chart x hx).hk w₀‖ ^ 2 ≤ D.rm x hx ^ 2 := by
        linarith [sq_nonneg ‖negPart (D.chart x hx).hk w₀‖]
      have := mul_le_mul hu₀.le hb₀ (sq_nonneg _) (sq_nonneg δ)
      linarith
    have hball₀ : 2 * ε + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < D.rm x hx ^ 2 := by
      linarith
    have hγ0 : (D.chart x hx).χ.symm (D.flow 0 ((D.chart x hx).χ w₀)) = w₀ := by
      rw [flow_zero, hleft w₀ hw₀rm]
    rcases le_or_gt c (f z) with hcz | hcz
    · rw [max_eq_left (sub_nonneg.2 hcz)]
      have hunit := f_flow_eq_sub_of_levels hf (D := D) (x := z) (T := f z - c)
        ⟨hzI.1, hzI.2.trans ht'⟩ (by rw [sub_sub_cancel]; exact hcab) (by
          intro y hy p hp
          rw [sub_sub_cancel, uIcc_of_ge hcz] at hy
          exact hU y ⟨hy.1, hy.2.trans hzI.2⟩ p hp)
      have hL : f (D.flow (f z - c) z) = c := by
        rw [hunit _ right_mem_uIcc]; ring
      rcases le_or_gt s₀ (f z - c) with h1a | h1b
      · set r := f z - c - s₀ with hr
        have hr0 : 0 ≤ r := by rw [hr]; linarith
        have hLr : D.flow (f z - c) z = D.flow r ((D.chart x hx).χ w₀) := by
          rw [hQ, flow_flow]; congr 1; rw [hr]; ring
        have hlevs : ∀ s ∈ Icc 0 r, c ≤ f (D.flow s ((D.chart x hx).χ w₀)) := by
          intro s hs
          have := f_flow_antitone (D := D) hf ((D.chart x hx).χ w₀) hs.2
          simp only at this
          rw [← hLr, hL] at this
          exact this
        set K : Set (Fin n → ℝ) := {w | morseNorm n w ≤ morseNorm n w₀} with hK
        have hKsub : K ⊆ {w | morseNorm n w < D.rm x hx} := fun w hw => lt_of_le_of_lt hw hw₀rm
        have hKc : IsCompact ((D.chart x hx).χ '' K) :=
          (D.chart x hx).isCompact_image_of_subset (isCompact_morseNorm_le _)
            (hw₀rm.trans hrmR') (fun w hw => hw)
        have hQc : IsClosed {s : ℝ | D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K} :=
          hKc.isClosed.preimage (D.continuous_flow_curve _)
        set O := (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx} with hO
        have hOopen : IsOpen O := D.isOpen_modelBall x hx
        have hKO : (D.chart x hx).χ '' K ⊆ O := image_mono hKsub
        have claimA : ∀ s ∈ Icc 0 r, D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K := by
          refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
          · change D.flow 0 ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K
            rw [flow_zero]; exact ⟨w₀, (le_rfl : morseNorm n w₀ ≤ morseNorm n w₀), rfl⟩
          · intro t ht hIcc
            have htO : D.flow t ((D.chart x hx).χ w₀) ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
            obtain ⟨η, hη, hηO⟩ := D.exists_Icc_flow_mem_open hOopen htO
            refine mem_nhdsGT_iff_exists_Ioc_subset.2
              ⟨min (t + η) r, lt_min (by linarith) ht.2, fun s hs => ?_⟩
            change D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K
            have hs0 : 0 ≤ s := ht.1.trans hs.1.le
            have hsr : s ≤ r := hs.2.trans (min_le_right _ _)
            have hODE : ∀ u ∈ Icc 0 s, D.flow u ((D.chart x hx).χ w₀) ∈ O := fun u hu => by
              rcases le_or_gt u t with h | h
              · exact hKO (hIcc ⟨hu.1, h⟩)
              · exact hηO u ⟨by linarith, hu.2.trans (hs.2.trans (min_le_left _ _))⟩
            have hγ := hasDerivAt_symm_flow_Icc hx hODE
            have hcons := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ s
              (right_mem_Icc.2 hs0)
            have hmono := ModelField.normSq_negPart_monotoneOn (D.chart x hx).hk hr₀ hγ
              (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
            have hanti := ModelField.normSq_posPart_antitoneOn (D.chart x hx).hk hr₀ hγ
              (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
            simp only [hγ0] at hcons hmono hanti
            obtain ⟨ws, hws, hwsx⟩ := hODE s (right_mem_Icc.2 hs0)
            rw [← hwsx, hleft ws hws] at hcons hmono hanti
            have hlev := hlevs s ⟨hs0, hsr⟩
            rw [← hwsx, hsplit ws hws] at hlev
            refine ⟨ws, ?_, hwsx⟩
            change morseNorm n ws ≤ morseNorm n w₀
            refine MorseNormalChart.morseNorm_le_of_sq_le (ModelField.morseNorm_nonneg w₀) ?_
            rw [hsq ws, hsq w₀]
            have hAb0 : ‖negPart (D.chart x hx).hk ws‖ ^ 2 ≤
                ‖posPart (D.chart x hx).hk w₀‖ ^ 2 := by linarith
            have key1 : ‖negPart (D.chart x hx).hk ws‖ ^ 2 *
                (‖negPart (D.chart x hx).hk ws‖ ^ 2 + ‖posPart (D.chart x hx).hk ws‖ ^ 2) ≤
                ‖negPart (D.chart x hx).hk ws‖ ^ 2 *
                (‖negPart (D.chart x hx).hk w₀‖ ^ 2 + ‖posPart (D.chart x hx).hk w₀‖ ^ 2) := by
              nlinarith only [mul_nonneg (sub_nonneg.2 hmono) (sub_nonneg.2 hAb0), hcons]
            rcases eq_or_lt_of_le (sq_nonneg ‖negPart (D.chart x hx).hk ws‖) with h0 | hpos
            · rw [← h0] at hmono ⊢
              linarith [sq_nonneg ‖negPart (D.chart x hx).hk w₀‖]
            · exact le_of_mul_le_mul_left key1 hpos
        have hODEr : ∀ u ∈ Icc 0 r, D.flow u ((D.chart x hx).χ w₀) ∈ O := fun u hu =>
          hKO (claimA u hu)
        have hγ := hasDerivAt_symm_flow_Icc hx hODEr
        have hcons := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ r
          (right_mem_Icc.2 hr0)
        simp only [hγ0] at hcons
        obtain ⟨wL, hwL, hwLx⟩ := claimA r (right_mem_Icc.2 hr0)
        have hwLrm : morseNorm n wL < D.rm x hx := lt_of_le_of_lt hwL hw₀rm
        rw [← hwLx, hleft wL hwLrm] at hcons
        have hlevL : f ((D.chart x hx).χ wL) = c := by rw [hwLx, ← hLr, hL]
        rw [hsplit wL hwLrm] at hlevL
        refine ⟨wL, hwLrm, ?_, le_of_eq hL, by rw [hwLx, hLr]⟩
        have hA := sq_nonneg ‖negPart (D.chart x hx).hk wL‖
        have hB : ‖posPart (D.chart x hx).hk wL‖ ^ 2 =
            2 * ε + ‖negPart (D.chart x hx).hk wL‖ ^ 2 := by linarith
        rw [hB] at hcons
        nlinarith only [hcons, hprod₀, hA, hε]
      · set r := s₀ - (f z - c) with hr
        have hr0 : 0 < r := by rw [hr]; linarith
        have hLr : D.flow (f z - c) z = D.flow (-r) ((D.chart x hx).χ w₀) := by
          rw [hQ, flow_flow]; congr 1; rw [hr]; ring
        have hQc' : f ((D.chart x hx).χ w₀) ≤ c := by
          rw [hQ, ← hL]; exact f_flow_antitone (D := D) hf z h1b.le
        by_cases hv₀ : posPart (D.chart x hx).hk w₀ = 0
        · exfalso
          have := f_flow_le_f_p_of_posPart_eq_zero (D := D) hx hw₀rm hv₀ (t := -r) (by linarith)
          rw [← hLr, hL] at this
          linarith
        · have hlevel : morseNormalForm (D.chart x hx).hk (f x) w₀ ≤ f x + ε := by
            rw [← (D.chart x hx).hnorm w₀ (hw₀rm.le.trans hrmR)]; exact hQc'
          obtain ⟨t₁, ht₁, hft₁, hin, hprod⟩ :=
            exists_exit_asc hf hx hε (y := w₀) hball₀ hv₀ hlevel
          have htt : -t₁ = -r := flow_level_unique hf hcU hft₁ (by rw [← hLr, hL])
          have hmemL := hin (-t₁) (left_mem_Icc.2 (by linarith))
          rw [htt, ← hLr] at hmemL hprod
          obtain ⟨wL, hwL, hwLx⟩ := hmemL
          have hwLrm : morseNorm n wL < D.rm x hx := by
            have : morseNorm n wL ^ 2 < D.rm x hx ^ 2 := by
              have : morseNorm n wL ^ 2 ≤ 2 * ε + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := hwL
              linarith
            exact lt_of_pow_lt_pow_left₀ 2 hrm.le this
          rw [← hwLx, hleft wL hwLrm] at hprod
          refine ⟨wL, hwLrm, ?_, le_of_eq hL, hwLx⟩
          have hA := sq_nonneg ‖negPart (D.chart x hx).hk wL‖
          nlinarith only [hprod, hprod₀, hA, hε]
    · rw [max_eq_right (by linarith), flow_zero]
      have hzQ : z = D.flow (-s₀) ((D.chart x hx).χ w₀) := by rw [hQ, flow_neg_flow]
      by_cases hv₀ : posPart (D.chart x hx).hk w₀ = 0
      · obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ :=
          flow_mem_of_posPart_eq_zero (D := D) hx hw₀rm hv₀ (t := -s₀) (by linarith)
        rw [← hzQ] at hwz
        refine ⟨w, lt_of_le_of_lt hw1 hw₀rm, ?_, hcz.le, hwz⟩
        have h1 : morseNorm n w ^ 2 = ‖negPart (D.chart x hx).hk w‖ ^ 2 := by
          rw [hsq w, hw2, norm_zero]; ring
        have h2 : morseNorm n w₀ ^ 2 = ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := by
          rw [hsq w₀, hv₀, norm_zero]; ring
        have h3 : morseNorm n w ^ 2 ≤ morseNorm n w₀ ^ 2 :=
          pow_le_pow_left₀ (ModelField.morseNorm_nonneg w) hw1 2
        linarith
      · have hlevel : morseNormalForm (D.chart x hx).hk (f x) w₀ ≤ f x + ε := by
          rw [← (D.chart x hx).hnorm w₀ (hw₀rm.le.trans hrmR), hQ]
          exact (f_flow_le hf z hs₀).trans hcz.le
        obtain ⟨t₁, ht₁, hft₁, hin, -⟩ := exists_exit_asc hf hx hε (y := w₀) hball₀ hv₀ hlevel
        have hst : s₀ ≤ t₁ := by
          by_contra hlt
          push Not at hlt
          have := f_flow_antitone (D := D) hf ((D.chart x hx).χ w₀) (show -s₀ ≤ -t₁ by linarith)
          simp only at this
          rw [← hzQ, hft₁] at this
          linarith
        have hinO : ∀ s ∈ Icc (-s₀) 0, D.flow s ((D.chart x hx).χ w₀) ∈
            (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx} := by
          intro s hs
          obtain ⟨w, hw, hwx⟩ := hin s ⟨by linarith [hs.1], hs.2⟩
          refine ⟨w, ?_, hwx⟩
          change morseNorm n w < D.rm x hx
          have : morseNorm n w ^ 2 < D.rm x hx ^ 2 := by
            have : morseNorm n w ^ 2 ≤ 2 * ε + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := hw
            linarith
          exact lt_of_pow_lt_pow_left₀ 2 hrm.le this
        have hγ := hasDerivAt_symm_flow_Icc hx hinO
        have hs0 : -s₀ ≤ 0 := by linarith
        have hmono := ModelField.normSq_negPart_monotoneOn (D.chart x hx).hk hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
        simp only [hγ0] at hmono
        obtain ⟨w, hw, hwx⟩ := hinO (-s₀) (left_mem_Icc.2 hs0)
        rw [← hwx, hleft w hw] at hmono
        rw [← hzQ] at hwx
        exact ⟨w, hw, by linarith, hcz.le, hwx⟩
  refine ⟨?_, ?_⟩
  · have hfun : D.tubeCoordE x hx ε (D.chart x hx).k = fun z =>
        negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z)) :=
      funext fun z => (hE z).trans (htc z)
    rw [hfun]
    intro z hz
    obtain ⟨w, hw, -, -, hwz⟩ := key z hz.2 hz.1
    refine ContinuousAt.continuousWithinAt ?_
    have hP : ContinuousAt (fun q => D.flow (max (f q - c) 0) q) z :=
      (D.continuous_flow_joint.comp
        (((hf.continuous.sub continuous_const).max continuous_const).prodMk
          continuous_id)).continuousAt
    have hsymm : ContinuousAt (D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z) := by
      refine (D.chart x hx).χ.continuousAt_symm ?_
      rw [← hwz]
      exact (D.chart x hx).χ.map_source
        ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hw.trans hrmR')))
    have h2 : ContinuousAt (fun q => (D.chart x hx).χ.symm (D.flow (max (f q - c) 0) q)) z :=
      ContinuousAt.comp (g := (D.chart x hx).χ.symm) hsymm hP
    exact (D.chart x hx).continuous_negPart.continuousAt.comp h2
  · intro z hz
    rw [hE z, htc z]
    obtain ⟨w, hw, hwu, hwf, hwz⟩ := key z hz.2 hz.1
    rw [← hwz, hleft w hw]
    have hcapP : z ∈ D.captured x hx ↔ (D.chart x hx).χ w ∈ D.captured x hx := by
      rw [hwz, flow_mem_captured_iff]
    constructor
    · intro hu
      exact mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hx, mem_iUnion.2 ⟨rfl,
        hcapP.2 (mem_captured_of_mem_stable ⟨w, ⟨hw, hu⟩, rfl⟩)⟩⟩⟩
    · intro hcap
      obtain ⟨y, hy, hyτ, hzy⟩ : ∃ y, ∃ hy : y ∈ crit, f y = f x ∧ z ∈ D.captured y hy := by
        simp only [GradientLikeStrip.slabCap, mem_iUnion] at hcap
        obtain ⟨y, hy, hyτ, hzy⟩ := hcap
        exact ⟨y, hy, hyτ, hzy⟩
      have hzx : z ∈ D.captured x hx := by
        by_cases hyx : y = x
        · have : D.captured y hy = D.captured x hx := by subst hyx; rfl
          rw [← this]; exact hzy
        · exfalso
          obtain ⟨T, hT⟩ := mem_captured_iff_eventually.1 hzy
          have hzty : z ∈ D.tube y hy δ := by
            obtain ⟨v, ⟨hv1, hv2⟩, hvz⟩ := hT (max T 0) (le_max_left _ _)
            exact ⟨max T 0, le_max_right _ _, v, ⟨hv1, by rw [hv2, norm_zero]; exact hδ⟩, hvz⟩
          exact Set.disjoint_left.1 (hdisj δ hδ hδ1 x hx y hy rfl hyτ (Ne.symm hyx)) hz.2 hzty
      have hPcap := hcapP.1 hzx
      by_contra hu
      have hfw := hsplit w hw
      have hge : f x ≤ f ((D.chart x hx).χ w) := by
        have := f_le_of_mem_captured hf hPcap 0
        rwa [flow_zero] at this
      have hwc : f ((D.chart x hx).χ w) ≤ c := by rw [hwz]; exact hwf
      have hv2 : 2 * ‖posPart (D.chart x hx).hk w‖ ^ 2 < D.rm x hx ^ 2 := by
        linarith
      set ε' := (D.rm x hx ^ 2 - 2 * ‖posPart (D.chart x hx).hk w‖ ^ 2) / 4 with hε'
      have hε'pos : 0 < ε' := by rw [hε']; linarith
      obtain ⟨t₂, -, ht₂, -, -⟩ := exists_exit_desc hf hx hε'pos (y := w) (by rw [hε']; linarith)
        hu (by
          rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
          linarith)
      have := f_le_of_mem_captured hf hPcap t₂
      linarith

theorem isIso_tubeCoord (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw)
    {x : M} (hx : x ∈ crit) (hxτ : f x = τ) {μ : ℕ} (hμ : (D.chart x hx).k = μ) (hμ1 : 1 ≤ μ) :
    ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IsOpen (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) :
        Set ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)) ∧
      ∃ (Φ : TopCat.of ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ) ⟶ TopCat.of (SingularPair.EU μ))
        (hΦ : MapsTo Φ (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ))
          {ULift.up 0}ᶜ),
        (∀ z, (Φ z).down = D.tubeCoordE x hx ε μ z.1) ∧
          ∀ j, CategoryTheory.IsIso (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ j) := by
  have _ := hμ1
  obtain ⟨δs, hδs, hspec⟩ := tubeCoord_spec hf D hcrit hε hεr ht htτ hτt' ht' hslab hU hx hxτ hμ
  subst hxτ
  subst hμ
  have hrm : 0 < D.rm x hx := D.rm_pos x hx
  have hrmR : D.rm x hx ≤ (D.chart x hx).R := (D.hrm x hx).2
  have hrmR' : D.rm x hx < (D.chart x hx).R' := D.rm_lt_R' x hx
  have h8 : 8 * ε < D.rm x hx ^ 2 := (hεr x hx).2
  have hr₀ := (D.chart x hx).hr₀
  refine ⟨min δs (Real.sqrt ε), lt_min hδs (Real.sqrt_pos.2 hε), ?_⟩
  intro δ hδ hδlt
  have hδ1 : δ < δs := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδs' : δ < Real.sqrt ε := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hδε : δ ^ 2 < ε := (Real.lt_sqrt hδ.le).1 hδs'
  have hδ2 : 0 < δ ^ 2 := by positivity
  obtain ⟨hcont, hzero⟩ := hspec δ hδ hδ1
  set c := f x + ε with hc
  have hsplit : ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx →
      f ((D.chart x hx).χ w) = f x + (1 / 2) *
        (‖posPart (D.chart x hx).hk w‖ ^ 2 - ‖negPart (D.chart x hx).hk w‖ ^ 2) := by
    intro w hw
    rw [(D.chart x hx).hnorm w (hw.le.trans hrmR),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
  have hsq : ∀ w : Fin n → ℝ, morseNorm n w ^ 2 =
      ‖negPart (D.chart x hx).hk w‖ ^ 2 + ‖posPart (D.chart x hx).hk w‖ ^ 2 := fun w =>
    DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart x hx).hk w
  have hleft : ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx →
      (D.chart x hx).χ.symm ((D.chart x hx).χ w) = w := fun w hw =>
    (D.chart x hx).χ.left_inv ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hw.trans hrmR')))
  have hlt_of_sq : ∀ w : Fin n → ℝ, morseNorm n w ^ 2 < D.rm x hx ^ 2 →
      morseNorm n w < D.rm x hx := fun w h => lt_of_pow_lt_pow_left₀ 2 hrm.le h
  have FWD : ∀ w₀ : Fin n → ℝ, morseNorm n w₀ < D.rm x hx → ∀ r : ℝ, 0 ≤ r →
      c ≤ f (D.flow r ((D.chart x hx).χ w₀)) →
      ∃ w, morseNorm n w < D.rm x hx ∧
        (D.chart x hx).χ w = D.flow r ((D.chart x hx).χ w₀) ∧
        ‖negPart (D.chart x hx).hk w‖ ^ 2 * ‖posPart (D.chart x hx).hk w‖ ^ 2 =
          ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 ∧
        ‖negPart (D.chart x hx).hk w₀‖ ^ 2 ≤ ‖negPart (D.chart x hx).hk w‖ ^ 2 := by
    intro w₀ hw₀rm r hr0 hcr
    have hγ0 : (D.chart x hx).χ.symm (D.flow 0 ((D.chart x hx).χ w₀)) = w₀ := by
      rw [flow_zero, hleft w₀ hw₀rm]
    have hlevs : ∀ s ∈ Icc 0 r, c ≤ f (D.flow s ((D.chart x hx).χ w₀)) := fun s hs =>
      hcr.trans (f_flow_antitone (D := D) hf ((D.chart x hx).χ w₀) hs.2)
    set K : Set (Fin n → ℝ) := {w | morseNorm n w ≤ morseNorm n w₀} with hK
    have hKsub : K ⊆ {w | morseNorm n w < D.rm x hx} := fun w hw => lt_of_le_of_lt hw hw₀rm
    have hKc : IsCompact ((D.chart x hx).χ '' K) :=
      (D.chart x hx).isCompact_image_of_subset (isCompact_morseNorm_le _)
        (hw₀rm.trans hrmR') (fun w hw => hw)
    have hQc : IsClosed {s : ℝ | D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K} :=
      hKc.isClosed.preimage (D.continuous_flow_curve _)
    set O := (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx} with hO
    have hOopen : IsOpen O := D.isOpen_modelBall x hx
    have hKO : (D.chart x hx).χ '' K ⊆ O := image_mono hKsub
    have claimA : ∀ s ∈ Icc 0 r, D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K := by
      refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
      · change D.flow 0 ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K
        rw [flow_zero]; exact ⟨w₀, (le_rfl : morseNorm n w₀ ≤ morseNorm n w₀), rfl⟩
      · intro t ht hIcc
        have htO : D.flow t ((D.chart x hx).χ w₀) ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
        obtain ⟨η, hη, hηO⟩ := D.exists_Icc_flow_mem_open hOopen htO
        refine mem_nhdsGT_iff_exists_Ioc_subset.2
          ⟨min (t + η) r, lt_min (by linarith only [hη]) ht.2, fun s hs => ?_⟩
        change D.flow s ((D.chart x hx).χ w₀) ∈ (D.chart x hx).χ '' K
        have hs0 : 0 ≤ s := ht.1.trans hs.1.le
        have hsr : s ≤ r := hs.2.trans (min_le_right _ _)
        have hODE : ∀ u ∈ Icc 0 s, D.flow u ((D.chart x hx).χ w₀) ∈ O := fun u hu => by
          rcases le_or_gt u t with h | h
          · exact hKO (hIcc ⟨hu.1, h⟩)
          · exact hηO u ⟨by linarith only [h, hη], hu.2.trans (hs.2.trans (min_le_left _ _))⟩
        have hγ := hasDerivAt_symm_flow_Icc hx hODE
        have hcons := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ s
          (right_mem_Icc.2 hs0)
        have hmono := ModelField.normSq_negPart_monotoneOn (D.chart x hx).hk hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
        have hanti := ModelField.normSq_posPart_antitoneOn (D.chart x hx).hk hr₀ hγ
          (left_mem_Icc.2 hs0) (right_mem_Icc.2 hs0) hs0
        simp only [hγ0] at hcons hmono hanti
        obtain ⟨ws, hws, hwsx⟩ := hODE s (right_mem_Icc.2 hs0)
        rw [← hwsx, hleft ws hws] at hcons hmono hanti
        have hlev := hlevs s ⟨hs0, hsr⟩
        rw [← hwsx, hsplit ws hws] at hlev
        refine ⟨ws, ?_, hwsx⟩
        change morseNorm n ws ≤ morseNorm n w₀
        refine MorseNormalChart.morseNorm_le_of_sq_le (ModelField.morseNorm_nonneg w₀) ?_
        rw [hsq ws, hsq w₀]
        have hAb0 : ‖negPart (D.chart x hx).hk ws‖ ^ 2 ≤
            ‖posPart (D.chart x hx).hk w₀‖ ^ 2 := by linarith only [hlev, hanti, hc, hε]
        have key1 : ‖negPart (D.chart x hx).hk ws‖ ^ 2 *
            (‖negPart (D.chart x hx).hk ws‖ ^ 2 + ‖posPart (D.chart x hx).hk ws‖ ^ 2) ≤
            ‖negPart (D.chart x hx).hk ws‖ ^ 2 *
            (‖negPart (D.chart x hx).hk w₀‖ ^ 2 + ‖posPart (D.chart x hx).hk w₀‖ ^ 2) := by
          nlinarith only [mul_nonneg (sub_nonneg.2 hmono) (sub_nonneg.2 hAb0), hcons]
        rcases eq_or_lt_of_le (sq_nonneg ‖negPart (D.chart x hx).hk ws‖) with h0 | hpos
        · rw [← h0] at hmono ⊢
          linarith only [hanti, sq_nonneg ‖negPart (D.chart x hx).hk w₀‖]
        · exact le_of_mul_le_mul_left key1 hpos
    have hODEr : ∀ u ∈ Icc 0 r, D.flow u ((D.chart x hx).χ w₀) ∈ O := fun u hu =>
      hKO (claimA u hu)
    have hγ := hasDerivAt_symm_flow_Icc hx hODEr
    have hcons := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ r
      (right_mem_Icc.2 hr0)
    have hmono := ModelField.normSq_negPart_monotoneOn (D.chart x hx).hk hr₀ hγ
      (left_mem_Icc.2 hr0) (right_mem_Icc.2 hr0) hr0
    simp only [hγ0] at hcons hmono
    obtain ⟨wL, hwL, hwLx⟩ := claimA r (right_mem_Icc.2 hr0)
    have hwLrm : morseNorm n wL < D.rm x hx := lt_of_le_of_lt hwL hw₀rm
    rw [← hwLx, hleft wL hwLrm] at hcons hmono
    exact ⟨wL, hwLrm, hwLx, hcons, hmono⟩
  have BWD : ∀ w₀ : Fin n → ℝ, morseNorm n w₀ < D.rm x hx →
      ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < δ ^ 2 → ∀ r : ℝ, 0 ≤ r →
      2 * (f (D.flow (-r) ((D.chart x hx).χ w₀)) - f x) +
        2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < D.rm x hx ^ 2 →
      ∃ w, morseNorm n w < D.rm x hx ∧
        (D.chart x hx).χ w = D.flow (-r) ((D.chart x hx).χ w₀) ∧
        ‖negPart (D.chart x hx).hk w‖ ^ 2 * ‖posPart (D.chart x hx).hk w‖ ^ 2 =
          ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 ∧
        ‖negPart (D.chart x hx).hk w‖ ^ 2 ≤ ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := by
    intro w₀ hw₀rm hb₀ r hr0 hℓ
    by_cases hv₀ : posPart (D.chart x hx).hk w₀ = 0
    · obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ :=
        flow_mem_of_posPart_eq_zero (D := D) hx hw₀rm hv₀ (t := -r) (by linarith only [hr0])
      refine ⟨w, lt_of_le_of_lt hw1 hw₀rm, hwz, by rw [hw2, hv₀]; simp, ?_⟩
      have h1 : morseNorm n w ^ 2 = ‖negPart (D.chart x hx).hk w‖ ^ 2 := by
        rw [hsq w, hw2, norm_zero]; ring
      have h2 : morseNorm n w₀ ^ 2 = ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := by
        rw [hsq w₀, hv₀, norm_zero]; ring
      have h3 : morseNorm n w ^ 2 ≤ morseNorm n w₀ ^ 2 :=
        pow_le_pow_left₀ (ModelField.morseNorm_nonneg w) hw1 2
      linarith only [h1, h2, h3]
    · set ℓ := f (D.flow (-r) ((D.chart x hx).χ w₀)) with hℓdef
      set η := (D.rm x hx ^ 2 - 2 * (ℓ - f x) - 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2) / 4
        with hη
      have hηpos : 0 < η := by rw [hη]; linarith only [hℓ]
      set ε' := max ε (ℓ - f x + η) with hε'
      have hε'pos : 0 < ε' := lt_of_lt_of_le hε (le_max_left _ _)
      have hball' : 2 * ε' + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < D.rm x hx ^ 2 := by
        rcases le_total ε (ℓ - f x + η) with h | h
        · rw [hε', max_eq_right h, hη]; linarith only [hℓ]
        · rw [hε', max_eq_left h]; linarith only [hb₀, hδε, h8, hε]
      have hf₀ : f ((D.chart x hx).χ w₀) ≤ ℓ := by
        have := f_flow_antitone (D := D) hf ((D.chart x hx).χ w₀)
          (show -r ≤ 0 by linarith only [hr0])
        simp only [flow_zero] at this
        exact this
      have hlevel : morseNormalForm (D.chart x hx).hk (f x) w₀ ≤ f x + ε' := by
        rw [← (D.chart x hx).hnorm w₀ (hw₀rm.le.trans hrmR)]
        have hmx : ℓ - f x + η ≤ ε' := le_max_right _ _
        linarith only [hmx, hf₀, hηpos]
      obtain ⟨t₁, ht₁, hft₁, hin, -⟩ := exists_exit_asc hf hx hε'pos (y := w₀) hball' hv₀ hlevel
      have hrt : r ≤ t₁ := by
        by_contra h
        push Not at h
        have hmn := f_flow_antitone (D := D) hf ((D.chart x hx).χ w₀)
          (show -r ≤ -t₁ by linarith only [h])
        simp only at hmn
        rw [hft₁] at hmn
        have hmx : ℓ - f x + η ≤ ε' := le_max_right _ _
        linarith only [hmn, hmx, hηpos]
      have hinO : ∀ s ∈ Icc (-r) 0, D.flow s ((D.chart x hx).χ w₀) ∈
          (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx} := by
        intro s hs
        obtain ⟨w, hw, hwx⟩ := hin s ⟨by linarith only [hs.1, hrt], hs.2⟩
        refine ⟨w, hlt_of_sq w ?_, hwx⟩
        have hw' : morseNorm n w ^ 2 ≤ 2 * ε' + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := hw
        linarith only [hw', hball']
      have hγ := hasDerivAt_symm_flow_Icc hx hinO
      have hr0' : -r ≤ 0 := by linarith only [hr0]
      have hcons := ModelField.normSq_negPart_mul_posPart_const (D.chart x hx).hk hγ 0
        (right_mem_Icc.2 hr0')
      have hmono := ModelField.normSq_negPart_monotoneOn (D.chart x hx).hk hr₀ hγ
        (left_mem_Icc.2 hr0') (right_mem_Icc.2 hr0') hr0'
      have hγ0 : (D.chart x hx).χ.symm (D.flow 0 ((D.chart x hx).χ w₀)) = w₀ := by
        rw [flow_zero, hleft w₀ hw₀rm]
      simp only [hγ0] at hcons hmono
      obtain ⟨w, hw, hwx⟩ := hinO (-r) (left_mem_Icc.2 hr0')
      rw [← hwx, hleft w hw] at hcons hmono
      exact ⟨w, hw, hwx, hcons.symm, hmono⟩
  have hat : a ≤ f x - ε := by linarith only [ht, htτ]
  have hct' : c ≤ t' := hτt'.le
  have hlevc : ∀ y, c ≤ f y → f y ≤ t' → ∀ s, 0 ≤ s → s ≤ f y - c →
      f (D.flow s y) = f y - s := by
    intro y hy1 hy2 s hs0 hs1
    have h := f_flow_eq_sub_of_levels hf (D := D) (x := y) (T := f y - c)
      ⟨by linarith only [hy1, hc, hat, hε], hy2.trans ht'⟩
      (by rw [sub_sub_cancel]; exact ⟨by linarith only [hc, hat, hε], by linarith only [hct', ht']⟩)
      (by
        intro y' hy' p hp
        rw [sub_sub_cancel, uIcc_of_ge hy1] at hy'
        exact hU y' ⟨hy'.1, hy'.2.trans hy2⟩ p hp)
    exact h s (by rw [uIcc_of_le (by linarith only [hy1])]; exact ⟨hs0, hs1⟩)
  set Xs := f ⁻¹' Icc a t' ∩ D.tube x hx δ with hXs
  have U1 : ∀ z ∈ Xs, ∀ s₀ : ℝ, 0 ≤ s₀ → ∀ w₀ : Fin n → ℝ, morseNorm n w₀ < D.rm x hx →
      ‖negPart (D.chart x hx).hk w₀‖ < δ → D.flow s₀ z = (D.chart x hx).χ w₀ →
      ∃ wL, morseNorm n wL < D.rm x hx ∧
        (D.chart x hx).χ wL = D.flow (max (f z - c) 0) z ∧
        ‖negPart (D.chart x hx).hk wL‖ ^ 2 * ‖posPart (D.chart x hx).hk wL‖ ^ 2 =
          ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 ∧
        (f z < c → ‖negPart (D.chart x hx).hk wL‖ ^ 2 ≤ ‖negPart (D.chart x hx).hk w₀‖ ^ 2) := by
    intro z hz s₀ hs₀ w₀ hw₀rm hw₀u hQ
    have hb₀ : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hw₀u (norm_nonneg _) two_ne_zero
    rcases le_or_gt c (f z) with hcz | hcz
    · rw [max_eq_left (sub_nonneg.2 hcz)]
      have hL : f (D.flow (f z - c) z) = c := by
        rw [hlevc z hcz hz.1.2 (f z - c) (sub_nonneg.2 hcz) le_rfl]; ring
      rcases le_or_gt s₀ (f z - c) with h1 | h1
      · have heq : D.flow (f z - c - s₀) ((D.chart x hx).χ w₀) = D.flow (f z - c) z := by
          rw [← hQ, flow_flow]; congr 1; ring
        obtain ⟨w, hw, hwx, hcons, -⟩ := FWD w₀ hw₀rm (f z - c - s₀) (by linarith only [h1])
          (by rw [heq, hL])
        exact ⟨w, hw, hwx.trans heq, hcons, fun h => absurd h (not_lt.2 hcz)⟩
      · have heq : D.flow (-(s₀ - (f z - c))) ((D.chart x hx).χ w₀) = D.flow (f z - c) z := by
          rw [← hQ, flow_flow]; congr 1; ring
        obtain ⟨w, hw, hwx, hcons, -⟩ := BWD w₀ hw₀rm hb₀ (s₀ - (f z - c)) (by linarith only [h1])
          (by rw [heq, hL, hc]; linarith only [hb₀, hδε, h8, hε])
        exact ⟨w, hw, hwx.trans heq, hcons, fun h => absurd h (not_lt.2 hcz)⟩
    · rw [max_eq_right (by linarith only [hcz]), flow_zero]
      have heq : D.flow (-s₀) ((D.chart x hx).χ w₀) = z := by rw [← hQ, flow_neg_flow]
      obtain ⟨w, hw, hwx, hcons, hmono⟩ := BWD w₀ hw₀rm hb₀ s₀ hs₀
        (by rw [heq]; rw [hc] at hcz; linarith only [hcz, hb₀, hδε, h8, hε])
      exact ⟨w, hw, hwx.trans heq, hcons, fun _ => hmono⟩
  have hPcont : Continuous (fun q : M => D.flow (max (f q - c) 0) q) :=
    D.continuous_flow_joint.comp
      (((hf.continuous.sub continuous_const).max continuous_const).prodMk continuous_id)
  have hwLcont : ContinuousOn
      (fun z => (D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z)) Xs := by
    intro z hz
    obtain ⟨s₀, hs₀, w₀, ⟨hw₀rm, hw₀u⟩, hQ⟩ := hz.2
    obtain ⟨wL, hwL, hwLx, -, -⟩ := U1 z hz s₀ hs₀ w₀ hw₀rm hw₀u hQ.symm
    refine ContinuousAt.continuousWithinAt ?_
    have hsymm : ContinuousAt (D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z) := by
      refine (D.chart x hx).χ.continuousAt_symm ?_
      rw [← hwLx]
      exact (D.chart x hx).χ.map_source
        ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hwL.trans hrmR')))
    exact ContinuousAt.comp (g := (D.chart x hx).χ.symm) hsymm hPcont.continuousAt
  obtain ⟨κ, hκ⟩ : ∃ κ : M → ℝ, κ = fun z =>
      ‖negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z))‖ ^ 2 *
        ‖posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z))‖ ^ 2 :=
    ⟨_, rfl⟩
  have hκcont : ContinuousOn κ Xs := by
    rw [hκ]
    exact (((D.chart x hx).continuous_negPart.norm.pow 2).comp_continuousOn hwLcont).mul
      (((D.chart x hx).continuous_posPart.norm.pow 2).comp_continuousOn hwLcont)
  have U2 : ∀ z ∈ Xs, 0 ≤ κ z ∧ κ z < δ ^ 2 * (D.rm x hx ^ 2 - δ ^ 2) := by
    intro z hz
    obtain ⟨s₀, hs₀, w₀, ⟨hw₀rm, hw₀u⟩, hQ⟩ := hz.2
    obtain ⟨wL, hwL, hwLx, hcons, -⟩ := U1 z hz s₀ hs₀ w₀ hw₀rm hw₀u hQ.symm
    have hκz : κ z = ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 := by
      rw [hκ]; simp only; rw [← hwLx, hleft wL hwL, hcons]
    rw [hκz]
    have hb₀ : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hw₀u (norm_nonneg _) two_ne_zero
    have hsq₀ := hsq w₀
    have hw₀sq : morseNorm n w₀ ^ 2 < D.rm x hx ^ 2 :=
      pow_lt_pow_left₀ hw₀rm (ModelField.morseNorm_nonneg w₀) two_ne_zero
    have hA := sq_nonneg ‖negPart (D.chart x hx).hk w₀‖
    have hB := sq_nonneg ‖posPart (D.chart x hx).hk w₀‖
    refine ⟨mul_nonneg hA hB, ?_⟩
    have h1 : ‖posPart (D.chart x hx).hk w₀‖ ^ 2 <
        D.rm x hx ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2 := by linarith only [hsq₀, hw₀sq]
    have h2 : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 * ‖posPart (D.chart x hx).hk w₀‖ ^ 2 ≤
        ‖negPart (D.chart x hx).hk w₀‖ ^ 2 *
          (D.rm x hx ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1.le hA
    have h4 : 0 < (δ ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) *
        (D.rm x hx ^ 2 - δ ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) :=
      mul_pos (by linarith only [hb₀]) (by linarith only [hb₀, hδε, h8, hA])
    have e : δ ^ 2 * (D.rm x hx ^ 2 - δ ^ 2) - ‖negPart (D.chart x hx).hk w₀‖ ^ 2 *
          (D.rm x hx ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) =
        (δ ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) *
          (D.rm x hx ^ 2 - δ ^ 2 - ‖negPart (D.chart x hx).hk w₀‖ ^ 2) := by ring
    linarith only [h2, h4, e]
  obtain ⟨Df, hDf⟩ : ∃ Df : M → ℝ, Df = fun z =>
      ((κ z / δ ^ 2 - δ ^ 2) / 2 + (D.rm x hx ^ 2 / 2 - δ ^ 2)) / 2 := ⟨_, rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : M → ℝ, Lf = fun z => max c (f x + Df z) := ⟨_, rfl⟩
  obtain ⟨σf, hσf⟩ : ∃ σf : M → ℝ, σf = fun z => max (f z - Lf z) 0 := ⟨_, rfl⟩
  obtain ⟨qf, hqf⟩ : ∃ qf : M → M, qf = fun z => D.flow (σf z) z := ⟨_, rfl⟩
  have hσcont : ContinuousOn σf Xs := by
    have hDcont : ContinuousOn Df Xs := by
      rw [hDf]; fun_prop
    have hLcont : ContinuousOn Lf Xs := by
      rw [hLf]; exact ContinuousOn.sup continuousOn_const (continuousOn_const.add hDcont)
    rw [hσf]
    exact ContinuousOn.sup (hf.continuous.continuousOn.sub hLcont) continuousOn_const
  have hqcont : ContinuousOn qf Xs := by
    rw [hqf]
    exact D.continuous_flow_joint.comp_continuousOn (hσcont.prodMk continuousOn_id)
  have hDlt : ∀ z ∈ Xs, Df z < D.rm x hx ^ 2 / 2 - δ ^ 2 := by
    intro z hz
    obtain ⟨-, h2⟩ := U2 z hz
    have : κ z / δ ^ 2 < D.rm x hx ^ 2 - δ ^ 2 := by
      rw [div_lt_iff₀ hδ2]; linarith only [h2]
    rw [hDf]; simp only; linarith only [this]
  have hDbig : ∀ z ∈ Xs, ∀ bb aa d : ℝ, 0 ≤ bb → bb * aa = κ z → aa - bb = 2 * d →
      Df z ≤ d → bb < δ ^ 2 := by
    intro z hz bb aa d hbb hprod hd hDd
    obtain ⟨h1, h2⟩ := U2 z hz
    set K' := κ z / δ ^ 2 with hK'
    have hK'1 : K' < D.rm x hx ^ 2 - δ ^ 2 := by
      rw [hK', div_lt_iff₀ hδ2]; linarith only [h2]
    have hK'0 : 0 ≤ K' := div_nonneg h1 hδ2.le
    have hκK : κ z = δ ^ 2 * K' := by rw [hK']; exact (mul_div_cancel₀ _ hδ2.ne').symm
    have hDv : Df z = ((K' - δ ^ 2) / 2 + (D.rm x hx ^ 2 / 2 - δ ^ 2)) / 2 := by
      rw [hDf]
    by_contra hbig
    push Not at hbig
    have haa : K' < aa := by rw [hDv] at hDd; linarith only [hDd, hd, hbig, hK'1]
    have hK1 : δ ^ 2 * K' < δ ^ 2 * aa := mul_lt_mul_of_pos_left haa hδ2
    have hK2 : δ ^ 2 * aa ≤ bb * aa :=
      mul_le_mul_of_nonneg_right hbig (by linarith only [haa, hK'0])
    linarith only [hK1, hK2, hκK, hprod]
  have hσ0 : ∀ z, 0 ≤ σf z := by intro z; rw [hσf]; exact le_max_right _ _
  have hLc : ∀ z, c ≤ Lf z := by intro z; rw [hLf]; exact le_max_left _ _
  have hDL : ∀ z, f x + Df z ≤ Lf z := by intro z; rw [hLf]; exact le_max_right _ _
  have hσge : ∀ z, f z - Lf z ≤ σf z := by intro z; rw [hσf]; exact le_max_left _ _
  have hσle : ∀ z, c ≤ f z → σf z ≤ f z - c := by
    intro z hcz; rw [hσf]; exact max_le (by linarith only [hLc z]) (by linarith only [hcz])
  have hσlow : ∀ z, f z < c → σf z = 0 := by
    intro z hcz; rw [hσf]; exact max_eq_right (by linarith only [hLc z, hcz])
  have hσpos : ∀ z, 0 < σf z → σf z = f z - Lf z := by
    intro z h
    rw [hσf] at h ⊢
    simp only at h ⊢
    rcases le_total (f z - Lf z) 0 with h' | h'
    · rw [max_eq_right h'] at h; exact absurd h (lt_irrefl _)
    · exact max_eq_left h'
  have hqlev : ∀ z ∈ Xs, c ≤ f z → f (qf z) = f z - σf z := by
    intro z hz hcz; rw [hqf]; exact hlevc z hcz hz.1.2 _ (hσ0 z) (hσle z hcz)
  have hqlow : ∀ z, f z < c → qf z = z := by
    intro z hcz; rw [hqf]; simp only; rw [hσlow z hcz, flow_zero]
  have hqa : ∀ z ∈ Xs, a ≤ f (qf z) := by
    intro z hz
    rcases le_or_gt c (f z) with hcz | hcz
    · rw [hqlev z hz hcz]; linarith only [hσle z hcz, hc, hat, hε]
    · rw [hqlow z hcz]; exact hz.1.1
  have hqle : ∀ z, f (qf z) ≤ f z := by
    intro z; rw [hqf]; exact f_flow_le hf z (hσ0 z)
  have U3 : ∀ z ∈ Xs, ∃ w, morseNorm n w < D.rm x hx ∧
      ‖negPart (D.chart x hx).hk w‖ ^ 2 < δ ^ 2 ∧ (D.chart x hx).χ w = qf z := by
    intro z hz
    obtain ⟨s₀, hs₀, w₀, ⟨hw₀rm, hw₀u⟩, hQ⟩ := hz.2
    have hQ' : D.flow s₀ z = (D.chart x hx).χ w₀ := hQ.symm
    have hb₀ : ‖negPart (D.chart x hx).hk w₀‖ ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ hw₀u (norm_nonneg _) two_ne_zero
    obtain ⟨wL, hwL, hwLx, hconsL, hmonoL⟩ := U1 z hz s₀ hs₀ w₀ hw₀rm hw₀u hQ'
    have hκz : κ z = ‖negPart (D.chart x hx).hk w₀‖ ^ 2 *
        ‖posPart (D.chart x hx).hk w₀‖ ^ 2 := by
      rw [hκ]; simp only; rw [← hwLx, hleft wL hwL, hconsL]
    have hqz : qf z = D.flow (σf z) z := by rw [hqf]
    rcases le_or_gt c (f z) with hcz | hcz
    · have hlevq := hqlev z hz hcz
      rcases le_or_gt s₀ (σf z) with h1 | h1
      · rcases eq_or_lt_of_le (hσ0 z) with h0 | h0
        · have hs0 : s₀ = 0 := le_antisymm (h0 ▸ h1) hs₀
          refine ⟨w₀, hw₀rm, hb₀, ?_⟩
          rw [hqz, ← h0, flow_zero, ← hQ', hs0, flow_zero]
        · have hσeq := hσpos z h0
          have hlevL : f (qf z) = Lf z := by rw [hlevq, hσeq]; ring
          have heq : D.flow (σf z - s₀) ((D.chart x hx).χ w₀) = qf z := by
            rw [← hQ', flow_flow, hqz]; congr 1; ring
          obtain ⟨w, hw, hwx, hcons, -⟩ := FWD w₀ hw₀rm (σf z - s₀) (by linarith only [h1])
            (by rw [heq, hlevL]; exact hLc z)
          refine ⟨w, hw, ?_, hwx.trans heq⟩
          have hlw := hsplit w hw
          rw [hwx, heq, hlevL] at hlw
          exact hDbig z hz _ _ (Lf z - f x) (sq_nonneg _) (by rw [hcons, hκz])
            (by linarith only [hlw]) (by linarith only [hDL z])
      · have heq : D.flow (-(s₀ - σf z)) ((D.chart x hx).χ w₀) = qf z := by
          rw [← hQ', flow_flow, hqz]; congr 1; ring
        have hbound : 2 * (Lf z - f x) + 2 * ‖negPart (D.chart x hx).hk w₀‖ ^ 2 <
            D.rm x hx ^ 2 := by
          rw [hLf]; simp only
          rcases le_total c (f x + Df z) with h | h
          · rw [max_eq_right h]; linarith only [hDlt z hz, hb₀]
          · rw [max_eq_left h, hc]; linarith only [hb₀, hδε, h8, hε]
        obtain ⟨w, hw, hwx, -, hmono⟩ := BWD w₀ hw₀rm hb₀ (s₀ - σf z) (by linarith only [h1])
          (by rw [heq, hlevq]; linarith only [hσge z, hbound])
        exact ⟨w, hw, lt_of_le_of_lt hmono hb₀, hwx.trans heq⟩
    · refine ⟨wL, hwL, lt_of_le_of_lt (hmonoL hcz) hb₀, ?_⟩
      rw [hwLx, hqlow z hcz, max_eq_right (by linarith only [hcz]), flow_zero]
  have htc : ∀ z, D.tubeCoord x hx ε z =
      negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z)) := by
    intro z
    unfold GradientLikeStrip.tubeCoord GradientLikeStrip.rightCoord
    split_ifs with h
    · rw [max_eq_left (by linarith only [h, hc])]
    · rw [max_eq_right (by linarith only [h, hc]), flow_zero]
  have hE : ∀ z, D.tubeCoordE x hx ε (D.chart x hx).k z = D.tubeCoord x hx ε z := by
    intro z
    ext i
    simp [GradientLikeStrip.tubeCoordE]
  have hΦf : ∀ z, D.tubeCoordE x hx ε (D.chart x hx).k z =
      negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (D.flow (max (f z - c) 0) z)) :=
    fun z => (hE z).trans (htc z)
  have hΦlow : ∀ w, morseNorm n w < D.rm x hx → f ((D.chart x hx).χ w) ≤ c →
      D.tubeCoordE x hx ε (D.chart x hx).k ((D.chart x hx).χ w) = negPart (D.chart x hx).hk w := by
    intro w hw hwc
    rw [hΦf, max_eq_right (by linarith only [hwc]), flow_zero, hleft w hw]
  have U4 : ∀ z ∈ Xs, D.tubeCoordE x hx ε (D.chart x hx).k (qf z) =
      D.tubeCoordE x hx ε (D.chart x hx).k z := by
    intro z hz
    rcases le_or_gt c (f z) with hcz | hcz
    · have hlevq := hqlev z hz hcz
      have hσc := hσle z hcz
      rw [hΦf, hΦf, hlevq, max_eq_left (by linarith only [hσc]), max_eq_left (by linarith only [hcz]), hqf]
      simp only
      rw [flow_flow]
      congr 3
      ring
    · rw [hqlow z hcz]
  have hcapflow : ∀ (s : ℝ) (y : M), D.flow s y ∈ D.slabCap (f x) ↔ y ∈ D.slabCap (f x) := by
    intro s y
    simp only [GradientLikeStrip.slabCap, mem_iUnion]
    constructor
    · rintro ⟨p, hp, hpτ, hmem⟩
      exact ⟨p, hp, hpτ, (flow_mem_captured_iff s).1 hmem⟩
    · rintro ⟨p, hp, hpτ, hmem⟩
      exact ⟨p, hp, hpτ, (flow_mem_captured_iff s).2 hmem⟩
  have U5 : ∀ p ∈ Xs, ∀ w, morseNorm n w < D.rm x hx → (D.chart x hx).χ w = p →
      (D.tubeCoordE x hx ε (D.chart x hx).k p = 0 ↔ negPart (D.chart x hx).hk w = 0) := by
    intro p hp w hw hwp
    constructor
    · intro h0
      rcases le_or_gt (f p) c with hpc | hpc
      · rw [← hwp, hΦlow w hw (hwp ▸ hpc)] at h0; exact h0
      · have hlev : f (D.flow (f p - c) ((D.chart x hx).χ w)) = c := by
          rw [hwp, hlevc p hpc.le hp.1.2 (f p - c) (by linarith only [hpc]) le_rfl]; ring
        obtain ⟨w', hw', hw'x, -, hmono⟩ := FWD w hw (f p - c) (by linarith only [hpc]) hlev.ge
        have hw'p : (D.chart x hx).χ w' = D.flow (f p - c) p := by rw [hw'x, hwp]
        rw [hΦf, max_eq_left (by linarith only [hpc]), ← hw'p, hleft w' hw'] at h0
        rw [h0, norm_zero] at hmono
        have : ‖negPart (D.chart x hx).hk w‖ ^ 2 = 0 :=
          le_antisymm (by simpa using hmono) (sq_nonneg _)
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    · intro hu
      refine (hzero p hp).2 ?_
      simp only [GradientLikeStrip.slabCap, mem_iUnion]
      exact ⟨x, hx, rfl, mem_captured_of_mem_stable ⟨w, ⟨hw, hu⟩, hwp⟩⟩
  have hχon : ContinuousOn (D.chart x hx).χ {w | morseNorm n w < D.rm x hx} :=
    (D.chart x hx).χ.continuousOn.mono fun w hw =>
      (D.chart x hx).hball (mem_ball_of_morseNorm_lt (lt_trans hw hrmR'))
  have hrec : ∀ (u : EuclideanSpace ℝ (Fin (D.chart x hx).k))
      (v : EuclideanSpace ℝ (Fin (n - (D.chart x hx).k))),
      morseNorm n (recombine (D.chart x hx).hk u v) ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
    DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq (D.chart x hx).hk
  have hnegrec : ∀ (u : EuclideanSpace ℝ (Fin (D.chart x hx).k))
      (v : EuclideanSpace ℝ (Fin (n - (D.chart x hx).k))),
      negPart (D.chart x hx).hk (recombine (D.chart x hx).hk u v) = u :=
    DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine (D.chart x hx).hk
  have hposrec : ∀ (u : EuclideanSpace ℝ (Fin (D.chart x hx).k))
      (v : EuclideanSpace ℝ (Fin (n - (D.chart x hx).k))),
      posPart (D.chart x hx).hk (recombine (D.chart x hx).hk u v) = v :=
    DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine (D.chart x hx).hk
  have hδrm : δ < D.rm x hx := by
    have : δ ^ 2 < D.rm x hx ^ 2 := by linarith only [hδε, h8, hε]
    exact lt_of_pow_lt_pow_left₀ 2 hrm.le this
  have hpt : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ < δ →
      morseNorm n (recombine (D.chart x hx).hk u 0) < D.rm x hx ∧
      (D.chart x hx).χ (recombine (D.chart x hx).hk u 0) ∈ Xs ∧
      D.tubeCoordE x hx ε (D.chart x hx).k
        ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) = u := by
    intro u hu
    have hm : morseNorm n (recombine (D.chart x hx).hk u 0) < D.rm x hx := by
      refine hlt_of_sq _ ?_
      rw [hrec, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
      have : ‖u‖ ^ 2 < δ ^ 2 := pow_lt_pow_left₀ hu (norm_nonneg _) two_ne_zero
      linarith only [this, hδε, h8, hε]
    have hlev := hsplit _ hm
    rw [hnegrec, hposrec, norm_zero] at hlev
    have hu2 : ‖u‖ ^ 2 < δ ^ 2 := pow_lt_pow_left₀ hu (norm_nonneg _) two_ne_zero
    have hu0 := sq_nonneg ‖u‖
    have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h00] at hlev
    have hlev1 : a ≤ f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) := by
      rw [hlev]; linarith only [hat, hu2, hδε, hu0]
    have hlev2 : f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) ≤ f x := by
      rw [hlev]; linarith only [hu0]
    have hX : (D.chart x hx).χ (recombine (D.chart x hx).hk u 0) ∈ Xs := by
      refine ⟨⟨hlev1, by linarith only [hlev2, hct', hc, hε]⟩, ?_⟩
      exact ⟨0, le_rfl, recombine (D.chart x hx).hk u 0, ⟨hm, by rw [hnegrec]; exact hu⟩,
        by rw [flow_zero]⟩
    refine ⟨hm, hX, ?_⟩
    rw [hΦlow _ hm (by linarith only [hlev2, hc, hε]), hnegrec]
  have hψq : ∀ z ∈ Xs, morseNorm n ((D.chart x hx).χ.symm (qf z)) < D.rm x hx ∧
      ‖negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z))‖ ^ 2 < δ ^ 2 ∧
      (D.chart x hx).χ ((D.chart x hx).χ.symm (qf z)) = qf z := by
    intro z hz
    obtain ⟨w, hw, hwb, hwq⟩ := U3 z hz
    rw [← hwq, hleft w hw]
    exact ⟨hw, hwb, rfl⟩
  have hqmem : ∀ z ∈ Xs, qf z ∈ Xs := by
    intro z hz
    obtain ⟨w, hw, hwb, hwq⟩ := U3 z hz
    refine ⟨⟨hqa z hz, (hqle z).trans hz.1.2⟩, 0, le_rfl, w,
      ⟨hw, lt_of_pow_lt_pow_left₀ 2 hδ.le hwb⟩, by rw [flow_zero, hwq]⟩
  have hψqcont : ContinuousOn (fun z => (D.chart x hx).χ.symm (qf z)) Xs := by
    intro z hz
    obtain ⟨w, hw, -, hwq⟩ := U3 z hz
    have hsymm : ContinuousAt (D.chart x hx).χ.symm (qf z) := by
      refine (D.chart x hx).χ.continuousAt_symm ?_
      rw [← hwq]
      exact (D.chart x hx).χ.map_source
        ((D.chart x hx).hball (mem_ball_of_morseNorm_lt (hw.trans hrmR')))
    exact hsymm.comp_continuousWithinAt (hqcont z hz)
  have hAout : ∀ w, morseNorm n w < D.rm x hx → (D.chart x hx).χ w ∈ Xs →
      negPart (D.chart x hx).hk w ≠ 0 → (D.chart x hx).χ w ∉ D.slabCap (f x) := by
    intro w hw hwX hu hcap
    exact hu ((U5 _ hwX w hw rfl).1 ((hzero _ hwX).2 hcap))
  have hAin : ∀ z ∈ Xs, z ∉ D.slabCap (f x) →
      negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z)) ≠ 0 := by
    intro z hz hzc hu
    obtain ⟨hw, -, hwq⟩ := hψq z hz
    have h0 := (U5 (qf z) (hqmem z hz) _ hw hwq).2 hu
    have hcap := (hzero _ (hqmem z hz)).1 h0
    rw [hqf] at hcap
    exact hzc ((hcapflow _ z).1 hcap)
  have hΦcont : Continuous (fun z : ↥Xs => D.tubeCoordE x hx ε (D.chart x hx).k z.1) :=
    hcont.comp_continuous continuous_subtype_val (fun z => z.2)
  have hmemA : ∀ z : ↥Xs, z.1 ∈ Xs \ D.slabCap (f x) ↔
      D.tubeCoordE x hx ε (D.chart x hx).k z.1 ≠ 0 := by
    intro z
    rw [Set.mem_sdiff, ne_eq, hzero z.1 z.2]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  refine ⟨?_, ?_⟩
  · have hset : (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) =
        (fun z : ↥Xs => D.tubeCoordE x hx ε (D.chart x hx).k z.1) ⁻¹' {0}ᶜ := by
      ext z
      exact hmemA z
    rw [hset]
    exact isOpen_compl_singleton.preimage hΦcont
  let Φ : TopCat.of ↥Xs ⟶ TopCat.of (SingularPair.EU (D.chart x hx).k) :=
    TopCat.ofHom ⟨fun z => ULift.up (D.tubeCoordE x hx ε (D.chart x hx).k z.1),
      continuous_uliftUp.comp hΦcont⟩
  have hΦ : MapsTo Φ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x))) {ULift.up 0}ᶜ := by
    intro z hz h
    exact (hmemA z).1 hz (congrArg ULift.down h)
  refine ⟨Φ, hΦ, fun z => rfl, fun j => ?_⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : EuclideanSpace ℝ (Fin (D.chart x hx).k) → ℝ,
      θ = fun y => (δ / 2) / (1 + ‖y‖) := ⟨_, rfl⟩
  have hθcont : Continuous θ := by
    rw [hθ]
    exact continuous_const.div (continuous_const.add continuous_norm)
      (fun y => by positivity)
  have hθpos : ∀ y, 0 < θ y := by intro y; rw [hθ]; positivity
  have hθn : ∀ y, θ y * ‖y‖ < δ / 2 := by
    intro y
    rw [hθ]
    simp only
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith only [hδ]
  have hρ : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖θ y • y‖ < δ := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hθpos y)]
    linarith only [hθn y, hδ]
  have instE : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (D.chart x hx).k)) :=
    IsBoundedSMul.continuousSMul
  have instF : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (n - (D.chart x hx).k))) :=
    IsBoundedSMul.continuousSMul
  have hsmE : Continuous
      (fun q : ℝ × EuclideanSpace ℝ (Fin (D.chart x hx).k) => q.1 • q.2) := continuous_smul
  have hsmF : Continuous
      (fun q : ℝ × EuclideanSpace ℝ (Fin (n - (D.chart x hx).k)) => q.1 • q.2) := continuous_smul
  have hrecC : Continuous (fun q : EuclideanSpace ℝ (Fin (D.chart x hx).k) ×
      EuclideanSpace ℝ (Fin (n - (D.chart x hx).k)) => recombine (D.chart x hx).hk q.1 q.2) :=
    DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine (D.chart x hx).hk
  have hρC : Continuous (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => θ y • y) :=
    hsmE.comp (hθcont.prodMk continuous_id)
  have hptC : Continuous (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) =>
      (D.chart x hx).χ (recombine (D.chart x hx).hk (θ y • y) 0)) :=
    hχon.comp_continuous (hrecC.comp (hρC.prodMk continuous_const))
      (fun y => (hpt _ (hρ y)).1)
  have hdnE : Continuous (fun y : SingularPair.EU.{u_2} (D.chart x hx).k => y.down) :=
    continuous_uliftDown
  let g : TopCat.of (SingularPair.EU (D.chart x hx).k) ⟶ TopCat.of ↥Xs :=
    TopCat.ofHom ⟨fun y => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk (θ y.down • y.down) 0),
      (hpt _ (hρ y.down)).2.1⟩, (hptC.comp hdnE).subtype_mk _⟩
  have hg : MapsTo g {ULift.up 0}ᶜ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x))) := by
    intro y hy
    have hy0 : y.down ≠ 0 := fun h => hy (by rw [mem_singleton_iff]; exact ULift.ext h)
    refine ⟨(hpt _ (hρ y.down)).2.1, hAout _ (hpt _ (hρ y.down)).1 (hpt _ (hρ y.down)).2.1 ?_⟩
    rw [hnegrec]
    exact smul_ne_zero (hθpos _).ne' hy0
  have hdn : Continuous (fun p : unitInterval × SingularPair.EU.{u_2} (D.chart x hx).k =>
      p.2.down) := continuous_uliftDown.comp continuous_snd
  have hs1 : Continuous (fun p : unitInterval × SingularPair.EU.{u_2} (D.chart x hx).k =>
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hcoef : Continuous (fun p : unitInterval × SingularPair.EU.{u_2} (D.chart x hx).k =>
      (1 - (p.1 : ℝ)) * θ p.2.down + p.1) :=
    ((continuous_const.sub hs1).mul (hθcont.comp hdn)).add hs1
  have hGc : Continuous (fun p : unitInterval × SingularPair.EU.{u_2} (D.chart x hx).k =>
      ULift.up.{u_2} (((1 - (p.1 : ℝ)) * θ p.2.down + p.1) • p.2.down)) :=
    continuous_uliftUp.comp (hsmE.comp (hcoef.prodMk hdn))
  let G : ContinuousMap.Homotopy (CategoryTheory.CategoryStruct.comp g Φ).hom
      (ContinuousMap.id (TopCat.of (SingularPair.EU (D.chart x hx).k))) :=
    { toFun := fun p => ULift.up (((1 - (p.1 : ℝ)) * θ p.2.down + p.1) • p.2.down)
      continuous_toFun := hGc
      map_zero_left := by
        intro y
        apply ULift.ext
        change ((1 - ((0 : unitInterval) : ℝ)) * θ y.down + ((0 : unitInterval) : ℝ)) • y.down =
          D.tubeCoordE x hx ε (D.chart x hx).k
            ((D.chart x hx).χ (recombine (D.chart x hx).hk (θ y.down • y.down) 0))
        rw [(hpt _ (hρ y.down)).2.2, Set.Icc.coe_zero, sub_zero, one_mul, add_zero]
      map_one_left := by
        intro y
        apply ULift.ext
        change ((1 - ((1 : unitInterval) : ℝ)) * θ y.down + ((1 : unitInterval) : ℝ)) • y.down =
          y.down
        rw [Set.Icc.coe_one, sub_self, zero_mul, zero_add, one_smul] }
  have hG : ∀ t, ∀ y ∈ ({ULift.up 0}ᶜ : Set (SingularPair.EU (D.chart x hx).k)),
      G (t, y) ∈ ({ULift.up 0}ᶜ : Set (SingularPair.EU (D.chart x hx).k)) := by
    intro t y hy h
    have hy0 : y.down ≠ 0 := fun h' => hy (by rw [mem_singleton_iff]; exact ULift.ext h')
    have hcoef : 0 < (1 - (t : ℝ)) * θ y.down + t := by
      have h1 : 0 ≤ (1 - (t : ℝ)) * θ y.down := mul_nonneg (sub_nonneg.2 t.2.2) (hθpos _).le
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [← h0, sub_zero, one_mul, add_zero]; exact hθpos _
      · linarith only [h1, h0]
    exact smul_ne_zero hcoef.ne' hy0 (congrArg ULift.down h)
  have hσX : Continuous (fun z : ↥Xs => σf z.1) :=
    hσcont.comp_continuous continuous_subtype_val (fun z => z.2)
  have hqX : Continuous (fun z : ↥Xs => qf z.1) :=
    hqcont.comp_continuous continuous_subtype_val (fun z => z.2)
  have hψqX : Continuous (fun z : ↥Xs => (D.chart x hx).χ.symm (qf z.1)) :=
    hψqcont.comp_continuous continuous_subtype_val (fun z => z.2)
  have hUX : Continuous (fun z : ↥Xs =>
      negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) :=
    (D.chart x hx).continuous_negPart.comp hψqX
  have hVX : Continuous (fun z : ↥Xs =>
      posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) :=
    (D.chart x hx).continuous_posPart.comp hψqX
  have hsX : Continuous (fun p : unitInterval × ↥Xs => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hpX : Continuous (fun p : unitInterval × ↥Xs => p.2) := continuous_snd
  have hUδ : ∀ z ∈ Xs, ‖negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z))‖ < δ :=
    fun z hz => lt_of_pow_lt_pow_left₀ 2 hδ.le (hψq z hz).2.1
  let Q : C(↥Xs, ↥Xs) := ⟨fun z => ⟨qf z.1, hqmem z.1 z.2⟩, hqX.subtype_mk _⟩
  have hmem1 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ z ∈ Xs, D.flow (s * σf z) z ∈ Xs := by
    intro s hs0 hs1 z hz
    have hle : f (D.flow (s * σf z) z) ≤ f z := f_flow_le hf z (mul_nonneg hs0 (hσ0 z))
    have hge : f (qf z) ≤ f (D.flow (s * σf z) z) := by
      rw [hqf]; exact f_flow_antitone hf z (mul_le_of_le_one_left (hσ0 z) hs1)
    obtain ⟨w, hw, hwb, hwq⟩ := U3 z hz
    refine ⟨⟨(hqa z hz).trans hge, hle.trans hz.1.2⟩, (1 - s) * σf z,
      mul_nonneg (by linarith only [hs1]) (hσ0 z), w, ⟨hw, lt_of_pow_lt_pow_left₀ 2 hδ.le hwb⟩,
      ?_⟩
    rw [hwq, flow_flow, show s * σf z + (1 - s) * σf z = σf z by ring, hqf]
  have hF1c : Continuous (fun p : unitInterval × ↥Xs => D.flow ((p.1 : ℝ) * σf p.2.1) p.2.1) :=
    D.continuous_flow_joint.comp ((hsX.mul (hσX.comp hpX)).prodMk (continuous_subtype_val.comp hpX))
  let F1 : ContinuousMap.Homotopy (ContinuousMap.id ↥Xs) Q :=
    { toFun := fun p => ⟨D.flow ((p.1 : ℝ) * σf p.2.1) p.2.1, hmem1 _ p.1.2.1 p.1.2.2 _ p.2.2⟩
      continuous_toFun := hF1c.subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        change D.flow (((0 : unitInterval) : ℝ) * σf z.1) z.1 = z.1
        rw [Set.Icc.coe_zero, zero_mul, flow_zero]
      map_one_left := by
        intro z
        apply Subtype.ext
        change D.flow (((1 : unitInterval) : ℝ) * σf z.1) z.1 = qf z.1
        rw [Set.Icc.coe_one, one_mul, hqf] }
  have hF1 : ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
      F1 (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro t z hz
    refine ⟨(F1 (t, z)).2, ?_⟩
    change D.flow ((t : ℝ) * σf z.1) z.1 ∉ D.slabCap (f x)
    rw [hcapflow]
    exact hz.2
  have hmem2 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ w : Fin n → ℝ, morseNorm n w < D.rm x hx →
      ‖negPart (D.chart x hx).hk w‖ ^ 2 < δ ^ 2 → f ((D.chart x hx).χ w) ≤ t' →
      morseNorm n (recombine (D.chart x hx).hk (negPart (D.chart x hx).hk w)
        ((1 - s) • posPart (D.chart x hx).hk w)) < D.rm x hx ∧
      (D.chart x hx).χ (recombine (D.chart x hx).hk (negPart (D.chart x hx).hk w)
        ((1 - s) • posPart (D.chart x hx).hk w)) ∈ Xs := by
    intro s hs0 hs1 w hw hwb hwt
    have h1s : (1 - s) ^ 2 ≤ 1 := pow_le_one₀ (by linarith only [hs1]) (by linarith only [hs0])
    have hn : ‖(1 - s) • posPart (D.chart x hx).hk w‖ ^ 2 ≤ ‖posPart (D.chart x hx).hk w‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_of_le_one_left (sq_nonneg _) h1s
    have hwsq : morseNorm n w ^ 2 < D.rm x hx ^ 2 :=
      pow_lt_pow_left₀ hw (ModelField.morseNorm_nonneg w) two_ne_zero
    have hsqw := hsq w
    have hm : morseNorm n (recombine (D.chart x hx).hk (negPart (D.chart x hx).hk w)
        ((1 - s) • posPart (D.chart x hx).hk w)) < D.rm x hx := by
      refine hlt_of_sq _ ?_
      rw [hrec]
      linarith only [hn, hwsq, hsqw]
    have hlev := hsplit _ hm
    rw [hnegrec, hposrec] at hlev
    have hlw := hsplit w hw
    have hn0 := sq_nonneg ‖(1 - s) • posPart (D.chart x hx).hk w‖
    refine ⟨hm, ⟨⟨?_, ?_⟩, 0, le_rfl, _, ⟨hm, by
      rw [hnegrec]; exact lt_of_pow_lt_pow_left₀ 2 hδ.le hwb⟩, by rw [flow_zero]⟩⟩
    · rw [hlev]; linarith only [hn0, hwb, hδε, hat, hε]
    · rw [hlev]; linarith only [hn, hlw, hwt]
  have hW2c : Continuous (fun p : unitInterval × ↥Xs => recombine (D.chart x hx).hk
      (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))
      ((1 - (p.1 : ℝ)) • posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) :=
    hrecC.comp ((hUX.comp hpX).prodMk (hsmF.comp ((continuous_const.sub hsX).prodMk
      (hVX.comp hpX))))
  have hmem2' : ∀ p : unitInterval × ↥Xs, morseNorm n (recombine (D.chart x hx).hk
      (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))
      ((1 - (p.1 : ℝ)) • posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) <
        D.rm x hx ∧ (D.chart x hx).χ (recombine (D.chart x hx).hk
      (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))
      ((1 - (p.1 : ℝ)) • posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) ∈ Xs :=
    fun p => hmem2 _ p.1.2.1 p.1.2.2 _ (hψq _ p.2.2).1 (hψq _ p.2.2).2.1
      (by rw [(hψq _ p.2.2).2.2]; exact (hqle _).trans p.2.2.1.2)
  have hQ'c : Continuous (fun z : ↥Xs => (D.chart x hx).χ (recombine (D.chart x hx).hk
      (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0)) :=
    hχon.comp_continuous (hrecC.comp (hUX.prodMk continuous_const))
      (fun z => (hpt _ (hUδ _ z.2)).1)
  let Q' : C(↥Xs, ↥Xs) := ⟨fun z => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk
      (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0),
      (hpt _ (hUδ _ z.2)).2.1⟩, hQ'c.subtype_mk _⟩
  let F2 : ContinuousMap.Homotopy Q Q' :=
    { toFun := fun p => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk
          (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))
          ((1 - (p.1 : ℝ)) • posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))),
        (hmem2' p).2⟩
      continuous_toFun := (hχon.comp_continuous hW2c (fun p => (hmem2' p).1)).subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        change (D.chart x hx).χ (recombine (D.chart x hx).hk
          (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))
          ((1 - ((0 : unitInterval) : ℝ)) •
            posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))) = qf z.1
        rw [Set.Icc.coe_zero, sub_zero, one_smul,
          DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]
        exact (hψq z.1 z.2).2.2
      map_one_left := by
        intro z
        apply Subtype.ext
        change (D.chart x hx).χ (recombine (D.chart x hx).hk
          (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))
          ((1 - ((1 : unitInterval) : ℝ)) •
            posPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))) =
          (D.chart x hx).χ (recombine (D.chart x hx).hk
          (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0)
        rw [Set.Icc.coe_one, sub_self, zero_smul] }
  have hF2 : ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
      F2 (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro t z hz
    refine ⟨(F2 (t, z)).2, ?_⟩
    exact hAout _ (hmem2' (t, z)).1 (hmem2' (t, z)).2
      (by rw [hnegrec]; exact hAin z.1 z.2 hz.2)
  have hc3pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ u, 0 < (1 - s) + s * θ u := by
    intro s hs0 hs1 u
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; norm_num
    · have := mul_pos h (hθpos u); linarith only [this, hs1]
  have hc3n : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k),
      ‖u‖ < δ → ‖((1 - s) + s * θ u) • u‖ < δ := by
    intro s hs0 hs1 u hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hc3pos s hs0 hs1 u)]
    have hm : max ‖u‖ (θ u * ‖u‖) < δ := max_lt hu (by linarith only [hθn u, hδ])
    have h1 : (1 - s) * ‖u‖ ≤ (1 - s) * max ‖u‖ (θ u * ‖u‖) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith only [hs1])
    have h2 : s * (θ u * ‖u‖) ≤ s * max ‖u‖ (θ u * ‖u‖) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hs0
    have e : ((1 - s) + s * θ u) * ‖u‖ = (1 - s) * ‖u‖ + s * (θ u * ‖u‖) := by ring
    have e2 : (1 - s) * max ‖u‖ (θ u * ‖u‖) + s * max ‖u‖ (θ u * ‖u‖) =
        max ‖u‖ (θ u * ‖u‖) := by ring
    linarith only [e, e2, h1, h2, hm]
  have hW3c : Continuous (fun p : unitInterval × ↥Xs =>
      ((1 - (p.1 : ℝ)) + p.1 * θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) •
        negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1))) :=
    hsmE.comp ((((continuous_const.sub hsX).add (hsX.mul (hθcont.comp (hUX.comp hpX))))).prodMk
      (hUX.comp hpX))
  have hmem3 : ∀ p : unitInterval × ↥Xs, ‖((1 - (p.1 : ℝ)) +
      p.1 * θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) •
        negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1))‖ < δ :=
    fun p => hc3n _ p.1.2.1 p.1.2.2 _ (hUδ _ p.2.2)
  have hptC' : Continuous (fun u : EuclideanSpace ℝ (Fin (D.chart x hx).k) =>
      recombine (D.chart x hx).hk u 0) := hrecC.comp (continuous_id.prodMk continuous_const)
  let Q'' : C(↥Xs, ↥Xs) := ⟨fun z => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk
      (θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) •
        negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0),
      (hpt _ (hρ _)).2.1⟩, (hptC.comp hUX).subtype_mk _⟩
  let F3 : ContinuousMap.Homotopy Q' Q'' :=
    { toFun := fun p => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk (((1 - (p.1 : ℝ)) +
          p.1 * θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1)))) •
            negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf p.2.1))) 0),
        (hpt _ (hmem3 p)).2.1⟩
      continuous_toFun := (hχon.comp_continuous (hptC'.comp hW3c)
        (fun p => (hpt _ (hmem3 p)).1)).subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        change (D.chart x hx).χ (recombine (D.chart x hx).hk (((1 - ((0 : unitInterval) : ℝ)) +
          ((0 : unitInterval) : ℝ) *
            θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))) •
              negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0) =
          (D.chart x hx).χ (recombine (D.chart x hx).hk
            (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0)
        rw [Set.Icc.coe_zero, sub_zero, zero_mul, add_zero, one_smul]
      map_one_left := by
        intro z
        apply Subtype.ext
        change (D.chart x hx).χ (recombine (D.chart x hx).hk (((1 - ((1 : unitInterval) : ℝ)) +
          ((1 : unitInterval) : ℝ) *
            θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)))) •
              negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0) =
          (D.chart x hx).χ (recombine (D.chart x hx).hk
            (θ (negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) •
              negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1))) 0)
        rw [Set.Icc.coe_one, sub_self, one_mul, zero_add] }
  have hF3 : ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
      F3 (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro t z hz
    refine ⟨(F3 (t, z)).2, ?_⟩
    exact hAout _ (hpt _ (hmem3 (t, z))).1 (hpt _ (hmem3 (t, z))).2.1
      (by rw [hnegrec]; exact smul_ne_zero (hc3pos _ t.2.1 t.2.2 _).ne' (hAin z.1 z.2 hz.2))
  have hvc : Continuous (fun p : unitInterval × ↥Xs =>
      D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm p.1, p.2)).1) :=
    hΦcont.comp (F2.continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  let F4 : ContinuousMap.Homotopy Q'' (CategoryTheory.CategoryStruct.comp Φ g).hom :=
    { toFun := fun p => ⟨(D.chart x hx).χ (recombine (D.chart x hx).hk
          (θ (D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm p.1, p.2)).1) •
            D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm p.1, p.2)).1) 0),
        (hpt _ (hρ _)).2.1⟩
      continuous_toFun := (hptC.comp hvc).subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        have hv0 : D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 0, z)).1 =
            negPart (D.chart x hx).hk ((D.chart x hx).χ.symm (qf z.1)) := by
          rw [unitInterval.symm_zero, F2.apply_one]
          exact (hpt _ (hUδ _ z.2)).2.2
        change (D.chart x hx).χ (recombine (D.chart x hx).hk
          (θ (D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 0, z)).1) •
            D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 0, z)).1) 0) = _
        rw [hv0]
        rfl
      map_one_left := by
        intro z
        apply Subtype.ext
        have hv1 : D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 1, z)).1 =
            D.tubeCoordE x hx ε (D.chart x hx).k z.1 := by
          rw [unitInterval.symm_one, F2.apply_zero]
          exact U4 z.1 z.2
        change (D.chart x hx).χ (recombine (D.chart x hx).hk
          (θ (D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 1, z)).1) •
            D.tubeCoordE x hx ε (D.chart x hx).k (F2 (unitInterval.symm 1, z)).1) 0) =
          (D.chart x hx).χ (recombine (D.chart x hx).hk
          (θ (D.tubeCoordE x hx ε (D.chart x hx).k z.1) •
            D.tubeCoordE x hx ε (D.chart x hx).k z.1) 0)
        rw [hv1] }
  have hF4 : ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
      F4 (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro t z hz
    refine ⟨(F4 (t, z)).2, ?_⟩
    have hne := (hmemA _).1 (hF2 (unitInterval.symm t) z hz)
    exact hAout _ (hpt _ (hρ _)).1 (hpt _ (hρ _)).2.1
      (by rw [hnegrec]; exact smul_ne_zero (hθpos _).ne' hne)
  have htrans : ∀ {f₀ f₁ f₂ : C(↥Xs, ↥Xs)} (P : ContinuousMap.Homotopy f₀ f₁)
      (R : ContinuousMap.Homotopy f₁ f₂),
      (∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
        P (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs)) →
      (∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
        R (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs)) →
      ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
        (P.trans R) (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro f₀ f₁ f₂ P R hP hR t z hz
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hP _ z hz
    · exact hR _ z hz
  let F := ((F1.trans F2).trans (F3.trans F4)).symm
  have hF : ∀ t, ∀ z ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs),
      F (t, z) ∈ (Subtype.val ⁻¹' (Xs \ D.slabCap (f x)) : Set ↥Xs) := by
    intro t z hz
    rw [ContinuousMap.Homotopy.symm_apply]
    exact htrans _ _ (htrans _ _ hF1 hF2) (htrans _ _ hF3 hF4) _ z hz
  exact Handle.isIso_relativeHomologyMap_of_pairHomotopyEquiv Φ g hΦ hg F hF G hG j

theorem tubeCoord_smallDisc (D : GradientLikeStrip I f a b crit) {x : M} (hx : x ∈ crit)
    {μ : ℕ} (hμ : (D.chart x hx).k = μ) {ε ρ₁ : ℝ} (hε : 0 < ε) (hρ₁ : 0 < ρ₁)
    (hρ₁R : ρ₁ < (D.chart x hx).R) :
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin μ)) 1,
      D.tubeCoordE x hx ε μ (D.smallDiscMap x μ ρ₁ y) = ρ₁ • y := by
  intro y hy
  have hyn : ‖y‖ ≤ 1 := by simpa using hy
  have hnormE : ‖(D.chart x hx).toE (Handle.reidx y)‖ = ‖y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Fintype.sum_equiv (finCongr hμ) _ _ (fun i => ?_)
    have hi : (i : ℕ) < μ := hμ ▸ i.isLt
    simp [MorseNormalChart.toE, Handle.reidx, hi]
    rfl
  set u : EuclideanSpace ℝ (Fin (D.chart x hx).k) := ρ₁ • (D.chart x hx).toE (Handle.reidx y)
    with hu
  set w : Fin n → ℝ := recombine (D.chart x hx).hk u 0 with hw
  have hun : ‖u‖ ≤ ρ₁ := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hρ₁, hnormE]
    nlinarith
  have hwR : morseNorm n w ≤ (D.chart x hx).R := by
    have h2 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
      (D.chart x hx).hk u 0
    rw [norm_zero] at h2
    have h0 : 0 ≤ morseNorm n w := norm_nonneg _
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    nlinarith
  have hsrc := (D.chart x hx).hsrc w hwR
  have hf : f ((D.chart x hx).χ w) < f x + ε := by
    rw [(D.chart x hx).hnorm w hwR,
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine,
      DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine, norm_zero]
    nlinarith [norm_nonneg u]
  have hsd : D.smallDiscMap x μ ρ₁ y = (D.chart x hx).χ w := by
    unfold smallDiscMap
    simp only [hx, ↓reduceDIte]
    rfl
  have htc : D.tubeCoord x hx ε ((D.chart x hx).χ w) = u := by
    have hnle : ¬ (f x + ε ≤ f ((D.chart x hx).χ w)) := not_le.2 hf
    unfold tubeCoord
    simp only [hnle, ↓reduceIte]
    rw [(D.chart x hx).χ.left_inv hsrc,
      DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine]
  rw [hsd, tubeCoordE, htc]
  ext i
  have hi : (i : ℕ) < (D.chart x hx).k := hμ ▸ i.isLt
  simp [hu, hi, MorseNormalChart.toE, Handle.reidx]

theorem discClass_tube_local (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw)
    {x : M} (hx : x ∈ crit) (hxτ : f x = τ) {μ : ℕ} (hμ : (D.chart x hx).k = μ) (hμ1 : 1 ≤ μ)
    (F : EuclideanSpace ℝ (Fin μ) → M) (z₀ : EuclideanSpace ℝ (Fin μ)) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hFc : ContinuousOn F (Metric.closedBall z₀ r₁))
    (hFX : MapsTo F (Metric.closedBall z₀ r₁) (f ⁻¹' Icc a t'))
    (hF0 : F z₀ ∈ D.captured x hx)
    (hFcap : ∀ y ∈ Metric.closedBall z₀ r₁, F y ∈ D.slabCap τ → y = z₀)
    (hG : ContDiffAt ℝ 1 (D.tubeCoordE x hx ε μ ∘ F) z₀)
    (hdet : LinearMap.det (fderiv ℝ (D.tubeCoordE x hx ε μ ∘ F) z₀ : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin μ)) ≠ 0)
    (g : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk μ)))
      (ULift.down ⁻¹' diskSphere μ) μ) :
    ∃ r₀ > (0 : ℝ), ∀ r : ℝ, 0 < r → r < r₀ → ∀ ρ₁, 0 < ρ₁ → ρ₁ < D.rm x hx →
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ) (fun y => F (z₀ + r • y)) g =
        ((SignType.sign (LinearMap.det (fderiv ℝ (D.tubeCoordE x hx ε μ ∘ F) z₀ :
            EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ))) : SignType) : ℤ) •
          Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
            (D.smallDiscMap x μ ρ₁) g := by
  classical
  subst hμ
  have hk1x : 1 ≤ (D.chart x hx).k := hμ1
  obtain ⟨d1, hd1, H1⟩ := isIso_tubeCoord hf D hcrit hε hεr ht htτ hτt' ht' hslab hU hx hxτ rfl
    hk1x
  obtain ⟨d2, hd2, H2⟩ := tubeCoord_spec hf D hcrit hε hεr ht htτ hτt' ht' hslab hU hx hxτ rfl
  have hrm0 : 0 < D.rm x hx := D.rm_pos x hx
  have hrmR : D.rm x hx ≤ (D.chart x hx).R := (D.hrm x hx).2
  have hm0 : 0 < min (min d1 d2) (2 * D.rm x hx) := lt_min (lt_min hd1 hd2) (by linarith)
  set δ : ℝ := min (min d1 d2) (2 * D.rm x hx) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδm : δ < min (min d1 d2) (2 * D.rm x hx) := by rw [hδdef]; linarith
  have hδ1 : δ < d1 := lt_of_lt_of_le hδm ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ < d2 := lt_of_lt_of_le hδm ((min_le_left _ _).trans (min_le_right _ _))
  have hρrm : δ / 2 < D.rm x hx := by
    have := lt_of_lt_of_le hδm (min_le_right _ _)
    linarith
  obtain ⟨hopen, Φ, hΦ, hΦeq, hiso⟩ := H1 δ hδ hδ1
  obtain ⟨hcontT, hzero⟩ := H2 δ hδ hδ2
  clear H1 H2
  have hre : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k),
      (D.chart x hx).toE (Handle.reidx y) = y := by
    intro y
    ext i
    simp [MorseNormalChart.toE, Handle.reidx]
  have hLnorm : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k),
      morseNorm n (recombine (D.chart x hx).hk u 0) = ‖u‖ := by
    intro u
    have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
      (D.chart x hx).hk u 0
    rw [norm_zero] at h
    exact (pow_left_inj₀ (ModelField.morseNorm_nonneg _) (norm_nonneg u) two_ne_zero).1
      (by rw [h]; ring)
  have hfL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) = τ - ‖u‖ ^ 2 / 2 := by
    intro u hu
    rw [(D.chart x hx).hnorm _ (by rw [hLnorm]; exact hu),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, hxτ]
    ring
  have hsrcL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      recombine (D.chart x hx).hk u 0 ∈ (D.chart x hx).χ.source := by
    intro u hu
    exact (D.chart x hx).hsrc _ (by rw [hLnorm]; exact hu)
  have hstripL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      a < f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) := by
    intro u hu
    exact (D.inStrip x hx ⟨_, (D.chart x hx).mem_ball_of_le (by rw [hLnorm]; exact hu), rfl⟩).1
  have hnotcap : ∀ z : M, f z < τ → z ∉ D.slabCap τ := by
    intro z hz hmem
    simp only [GradientLikeStrip.slabCap, Set.mem_iUnion] at hmem
    obtain ⟨w, hw, hwτ, hzw⟩ := hmem
    exact GradientLikeStrip.notMem_captured_of_f_flow_lt (D := D) hf (t := 0)
      (by rw [D.flow_zero]; linarith) hzw
  have hSeq : ∀ (ρ : ℝ) (y : EuclideanSpace ℝ (Fin (D.chart x hx).k)),
      D.smallDiscMap x (D.chart x hx).k ρ y =
        (D.chart x hx).χ (recombine (D.chart x hx).hk (ρ • y) 0) := by
    intro ρ y
    simp only [GradientLikeStrip.smallDiscMap, hx, ↓reduceDIte, hre]
  have hrad : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < D.rm x hx → 0 < ρ' → ρ' < D.rm x hx →
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k ρ) g =
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k ρ') g := by
    intro ρ ρ' hρ hρr hρ' hρ'r
    let δs : ℝ → ℝ := fun s => (1 - s) * ρ + s * ρ'
    have hδs : ∀ s ∈ Icc (0 : ℝ) 1, 0 < δs s ∧ δs s < D.rm x hx := by
      intro s hs
      rcases lt_or_eq_of_le hs.2 with h | h
      · have h1 : 0 < (1 - s) * ρ := mul_pos (sub_pos.2 h) hρ
        have h2 : 0 ≤ s * ρ' := mul_nonneg hs.1 hρ'.le
        have h3 : 0 < (1 - s) * (D.rm x hx - ρ) := mul_pos (sub_pos.2 h) (sub_pos.2 hρr)
        have h4 : 0 ≤ s * (D.rm x hx - ρ') := mul_nonneg hs.1 (sub_pos.2 hρ'r).le
        constructor
        · change 0 < (1 - s) * ρ + s * ρ'
          linarith
        · change (1 - s) * ρ + s * ρ' < D.rm x hx
          nlinarith
      · subst h
        constructor
        · change 0 < (1 - 1) * ρ + 1 * ρ'
          linarith
        · change (1 - 1) * ρ + 1 * ρ' < D.rm x hx
          linarith
    have hnδ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ
        (Fin (D.chart x hx).k)) 1, ‖δs s • y‖ ≤ (D.chart x hx).R := by
      intro s hs y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hδs s hs).1]
      nlinarith [(hδs s hs).1, (hδs s hs).2, norm_nonneg y]
    refine Handle.discClass_eq_of_homotopy _ _ _ _
      (fun s y => (D.chart x hx).χ (recombine (D.chart x hx).hk (δs s • y) 0)) ?_ ?_ ?_ ?_ ?_ g
    · refine (D.chart x hx).χ.continuousOn.comp
        (((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
          (D.chart x hx).hk).comp
          ((((continuous_const.sub continuous_fst).mul continuous_const).add
            (continuous_fst.mul continuous_const)).smul continuous_snd |>.prodMk
            continuous_const)).continuousOn) ?_
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact hsrcL _ (hnδ s hs y hy)
    · intro y _
      rw [hSeq]
      congr 3
      simp [δs]
    · intro y _
      rw [hSeq]
      congr 3
      simp [δs]
    · intro s hs y hy
      have h1 := hfL _ (hnδ s hs y hy)
      refine ⟨(hstripL _ (hnδ s hs y hy)).le, ?_⟩
      change f ((D.chart x hx).χ (recombine (D.chart x hx).hk (δs s • y) 0)) ≤ t'
      rw [h1]
      nlinarith [sq_nonneg ‖δs s • y‖]
    · intro s hs y hy
      have hy' : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
        Metric.sphere_subset_closedBall hy
      rw [mem_sphere_zero_iff_norm] at hy
      have h1 := hfL _ (hnδ s hs y hy')
      have hne : δs s • y ≠ 0 := smul_ne_zero (hδs s hs).1.ne' (by rintro rfl; simp at hy)
      have hpos : 0 < ‖δs s • y‖ := norm_pos_iff.2 hne
      refine ⟨⟨(hstripL _ (hnδ s hs y hy')).le, ?_⟩, hnotcap _ ?_⟩
      · change f ((D.chart x hx).χ (recombine (D.chart x hx).hk (δs s • y) 0)) ≤ t'
        rw [h1]
        nlinarith [sq_nonneg ‖δs s • y‖]
      · rw [h1]
        nlinarith [sq_nonneg ‖δs s • y‖]
  have hρ : 0 < δ / 2 := by linarith
  have hnormz : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
      morseNorm n (recombine (D.chart x hx).hk ((δ / 2) • y) 0) ≤ δ / 2 := by
    intro y hy
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
      (D.chart x hx).hk ((δ / 2) • y) 0
    have h2 := ModelField.morseNorm_nonneg (recombine (D.chart x hx).hk ((δ / 2) • y) 0)
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    rw [norm_zero, norm_smul, Real.norm_of_nonneg hρ.le] at h1
    have h3 : δ / 2 * ‖y‖ ≤ δ / 2 := mul_le_of_le_one_right hρ.le hy1
    have h4 : 0 ≤ δ / 2 * ‖y‖ := by positivity
    nlinarith
  have hRle : δ / 2 ≤ (D.chart x hx).R := hρrm.le.trans hrmR
  have hcontR : Continuous (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) =>
      recombine (D.chart x hx).hk ((δ / 2) • y) 0) :=
    (DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
      (D.chart x hx).hk).comp ((continuous_const_smul (δ / 2)).prodMk continuous_const)
  have hcontD : ContinuousOn (D.smallDiscMap x (D.chart x hx).k (δ / 2))
      (Metric.closedBall 0 1) := by
    have : D.smallDiscMap x (D.chart x hx).k (δ / 2) =
        fun y => (D.chart x hx).χ (recombine (D.chart x hx).hk ((δ / 2) • y) 0) :=
      funext (hSeq (δ / 2))
    rw [this]
    exact (D.chart x hx).χ.continuousOn.comp hcontR.continuousOn
      (fun y hy => (D.chart x hx).hsrc _ ((hnormz y hy).trans hRle))
  have hmapsB : MapsTo (D.smallDiscMap x (D.chart x hx).k (δ / 2)) (Metric.closedBall 0 1)
      (f ⁻¹' Icc a t' ∩ D.tube x hx δ) := by
    intro y hy
    rw [hSeq]
    have hnz := hnormz y hy
    have hneg : ‖negPart (D.chart x hx).hk (recombine (D.chart x hx).hk ((δ / 2) • y) 0)‖ ≤
        δ / 2 := by
      rw [ModelField.negPart_recombine, norm_smul, Real.norm_of_nonneg hρ.le]
      have : ‖y‖ ≤ 1 := by simpa using hy
      exact mul_le_of_le_one_right hρ.le this
    refine ⟨⟨?_, ?_⟩, 0, le_rfl, ?_⟩
    · exact (D.inStrip x hx ⟨_, (D.chart x hx).mem_ball_of_le (hnz.trans hRle), rfl⟩).1.le
    · rw [(D.chart x hx).hnorm _ (hnz.trans hRle),
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
        ModelField.posPart_recombine, hxτ, norm_zero]
      nlinarith [sq_nonneg ‖negPart (D.chart x hx).hk
        (recombine (D.chart x hx).hk ((δ / 2) • y) 0)‖]
    · rw [D.flow_zero]
      exact ⟨_, ⟨lt_of_le_of_lt hnz hρrm, lt_of_le_of_lt hneg (by linarith)⟩, rfl⟩
  have htc : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
      D.tubeCoordE x hx ε (D.chart x hx).k (D.smallDiscMap x (D.chart x hx).k (δ / 2) y) =
        (δ / 2) • y :=
    tubeCoord_smallDisc D hx rfl hε hρ (hρrm.trans_le hrmR)
  have hmapsA : MapsTo (D.smallDiscMap x (D.chart x hx).k (δ / 2)) (Metric.sphere 0 1)
      ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) := by
    intro y hy
    have hyb : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
      Metric.sphere_subset_closedBall hy
    refine ⟨hmapsB hyb, fun hcap => ?_⟩
    have h0 := (hzero _ (hmapsB hyb)).2 hcap
    rw [htc y hyb] at h0
    have hy1 : ‖y‖ = 1 := by simpa using hy
    rcases smul_eq_zero.1 h0 with h | h
    · linarith
    · rw [h, norm_zero] at hy1
      exact zero_ne_one hy1
  let A : EuclideanSpace ℝ (Fin (D.chart x hx).k) ≃L[ℝ] EuclideanSpace ℝ (Fin (D.chart x hx).k) :=
    (LinearEquiv.smulOfNeZero ℝ _ (δ / 2) hρ.ne').toContinuousLinearEquiv
  have hAdet : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (D.chart x hx).k)) := by
    have hAeq : (A : EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (D.chart x hx).k)) = (δ / 2) • LinearMap.id :=
      LinearMap.ext fun v => rfl
    rw [hAeq, LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin, mul_one]
    exact pow_pos hρ _
  let ψ : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
      TopCat.of ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ) :=
    TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) =>
        (⟨D.smallDiscMap x (D.chart x hx).k (δ / 2) z.down.1, hmapsB z.down.2⟩ :
          ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)),
      (hcontD.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun z => z.down.2)).subtype_mk _⟩
  have hψ : MapsTo ψ (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
      (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)) :=
    fun z hz => hmapsA hz
  let ι : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
      TopCat.of (SingularPair.EU.{u_2} (D.chart x hx).k) :=
    TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) => ULift.up z.down.1,
      continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩
  have hι : MapsTo ι (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
      ({ULift.up 0}ᶜ : Set (SingularPair.EU.{u_2} (D.chart x hx).k)) := by
    intro z hz h0
    have hz1 : ‖z.down.1‖ = 1 := by simpa [diskSphere] using hz
    have h0' : z.down.1 = 0 := congrArg ULift.down h0
    rw [h0', norm_zero] at hz1
    exact zero_ne_one hz1
  have e1 : Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
      ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
      (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g =
        SingularPair.relativeHomologyMap SingularPair.integerCoefficients ψ hψ (D.chart x hx).k g := by
    unfold Handle.discClass
    rw [dite_eq_left ⟨hcontD, hmapsB, hmapsA⟩]
    rfl
  have e2 : Handle.euDiscClass (fun y => y) g =
      SingularPair.relativeHomologyMap SingularPair.integerCoefficients ι hι (D.chart x hx).k g := by
    unfold Handle.euDiscClass
    rw [dite_eq_left ⟨continuous_id.continuousOn, fun y hy h0 => by
      have hy1 : ‖y‖ = 1 := by simpa using hy
      simp only at h0
      rw [h0, norm_zero] at hy1
      exact zero_ne_one hy1⟩]
  have hmor : CategoryTheory.CategoryStruct.comp ψ Φ =
      CategoryTheory.CategoryStruct.comp ι (Handle.euMap A) := by
    ext z i
    have h1 : (Φ (ψ z)).down = A z.down.1 := by
      rw [hΦeq]
      exact htc z.down.1 z.down.2
    exact congrArg (fun v : EuclideanSpace ℝ (Fin (D.chart x hx).k) => v.ofLp i) h1
  have key : SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k
      (Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
        ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g) = Handle.euDiscClass (fun y => y) g := by
    rw [← Handle.hrelMap_euMap_of_det_pos hk1x A hAdet (Handle.euDiscClass (fun y => y) g), e1, e2,
      ← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
      ← SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients ψ Φ hψ hΦ (SingularPair.mapsTo_comp hψ hΦ),
      ← SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients ι (Handle.euMap A) hι (Handle.euMap_mapsTo A)
        (SingularPair.mapsTo_comp hι (Handle.euMap_mapsTo A)),
      SingularPair.relativeHomologyMap_eq_of_eq SingularPair.integerCoefficients hmor]
  have := hiso (D.chart x hx).k
  have hinj : Function.Injective (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r₁ := Metric.mem_closedBall_self hr₁.le
  have hFz0T : F z₀ ∈ D.tube x hx δ := by
    obtain ⟨T0, hT0⟩ := (GradientLikeStrip.mem_captured_iff_eventually (D := D)).1 hF0
    refine ⟨max T0 0, le_max_right _ _, ?_⟩
    obtain ⟨w, ⟨hw1, hw2⟩, hw⟩ := hT0 (max T0 0) (le_max_left _ _)
    exact ⟨w, ⟨hw1, by rw [hw2, norm_zero]; exact hδ⟩, hw⟩
  have hFz0cap : F z₀ ∈ D.slabCap τ := by
    simp only [GradientLikeStrip.slabCap, Set.mem_iUnion]
    exact ⟨x, hx, hxτ, hF0⟩
  obtain ⟨e, he, hesub⟩ : ∃ e > (0 : ℝ), ∀ y ∈ Metric.closedBall z₀ r₁, dist y z₀ < e →
      F y ∈ D.tube x hx δ := by
    have h1 : F ⁻¹' D.tube x hx δ ∈ 𝓝[Metric.closedBall z₀ r₁] z₀ :=
      hFc z₀ hz₀mem ((isOpen_tube D hx δ).mem_nhds hFz0T)
    rcases Metric.mem_nhdsWithin_iff.1 h1 with ⟨e, he, hsub⟩
    exact ⟨e, he, fun y hy hye => hsub ⟨hye, hy⟩⟩
  let Gt : EuclideanSpace ℝ (Fin (D.chart x hx).k) → EuclideanSpace ℝ (Fin (D.chart x hx).k) :=
    fun w => D.tubeCoordE x hx ε (D.chart x hx).k (F (z₀ + w))
  have hGt0 : Gt 0 = 0 := by
    change D.tubeCoordE x hx ε _ (F (z₀ + 0)) = 0
    rw [add_zero]
    exact (hzero _ ⟨hFX hz₀mem, hFz0T⟩).2 hFz0cap
  have hGteq : Gt = (D.tubeCoordE x hx ε (D.chart x hx).k ∘ F) ∘ (fun w => z₀ + w) := rfl
  have hGtC : ContDiffAt ℝ 1 Gt 0 := by
    rw [hGteq]
    refine ContDiffAt.comp (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) ?_ ?_
    · simpa using hG
    · exact contDiffAt_const.add contDiffAt_id
  have hGtD : fderiv ℝ Gt 0 = fderiv ℝ (D.tubeCoordE x hx ε (D.chart x hx).k ∘ F) z₀ := by
    have h := fderiv_comp_add_left (𝕜 := ℝ) (f := D.tubeCoordE x hx ε (D.chart x hx).k ∘ F)
      (x := (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k))) z₀
    rw [add_zero] at h
    exact h
  have hdet' : LinearMap.det (fderiv ℝ Gt 0 : EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (D.chart x hx).k)) ≠ 0 := by
    rw [hGtD]
    exact hdet
  obtain ⟨r₂, hr₂, Hlin⟩ := Handle.euDiscClass_linearize hk1x hGt0 hGtC hdet' g
  refine ⟨min (min r₁ e) r₂, lt_min (lt_min hr₁ he) hr₂, fun r hr0 hr ρ₁ hρ₁ hρ₁r => ?_⟩
  have hrr₁ : r < r₁ := lt_of_lt_of_le hr ((min_le_left _ _).trans (min_le_left _ _))
  have hre' : r < e := lt_of_lt_of_le hr ((min_le_left _ _).trans (min_le_right _ _))
  have hrr₂ : r < r₂ := lt_of_lt_of_le hr (min_le_right _ _)
  have hmem : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
      z₀ + r • y ∈ Metric.closedBall z₀ r₁ ∧ dist (z₀ + r • y) z₀ < e := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    have hd : dist (z₀ + r • y) z₀ = r * ‖y‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
    have hle : r * ‖y‖ ≤ r := mul_le_of_le_one_right hr0.le hy1
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, hd]
      linarith
    · rw [hd]
      linarith
  have hFrc : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => F (z₀ + r • y))
      (Metric.closedBall 0 1) := by
    have hcaff : Continuous (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => z₀ + r • y) :=
      continuous_const.add (continuous_id.const_smul r)
    have h := hFc.comp hcaff.continuousOn (fun y hy => (hmem y hy).1)
    exact h
  have hFrB : MapsTo (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => F (z₀ + r • y))
      (Metric.closedBall 0 1) (f ⁻¹' Icc a t' ∩ D.tube x hx δ) :=
    fun y hy => ⟨hFX (hmem y hy).1, hesub _ (hmem y hy).1 (hmem y hy).2⟩
  have hFrA : MapsTo (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => F (z₀ + r • y))
      (Metric.sphere 0 1) ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) := by
    intro y hy
    have hyb : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
      Metric.sphere_subset_closedBall hy
    refine ⟨hFrB hyb, fun hcap => ?_⟩
    have h1 := hFcap _ (hmem y hyb).1 hcap
    have h2 : r • y = 0 := by
      have := congrArg (fun v => v - z₀) h1
      simpa using this
    have hy1 : ‖y‖ = 1 := by simpa using hy
    rcases smul_eq_zero.1 h2 with h | h
    · linarith
    · rw [h, norm_zero] at hy1
      exact zero_ne_one hy1
  let ψF : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
      TopCat.of ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ) :=
    TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) =>
        (⟨F (z₀ + r • z.down.1), hFrB z.down.2⟩ : ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)),
      (hFrc.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun z => z.down.2)).subtype_mk _⟩
  have hψF : MapsTo ψF (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
      (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)) :=
    fun z hz => hFrA hz
  have hGrc : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => Gt (r • y))
      (Metric.closedBall 0 1) :=
    hcontT.comp hFrc hFrB
  have hGr0 : ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
      Gt (r • y) ≠ 0 := by
    intro y hy h0
    have hyb : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
      Metric.sphere_subset_closedBall hy
    exact (hFrA hy).2 ((hzero _ (hFrB hyb)).1 h0)
  let ιF : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
      TopCat.of (SingularPair.EU.{u_2} (D.chart x hx).k) :=
    TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) => ULift.up (Gt (r • z.down.1)),
      continuous_uliftUp.comp (hGrc.comp_continuous
        (continuous_subtype_val.comp continuous_uliftDown) (fun z => z.down.2))⟩
  have hιF : MapsTo ιF (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
      ({ULift.up 0}ᶜ : Set (SingularPair.EU.{u_2} (D.chart x hx).k)) := by
    intro z hz h0
    exact hGr0 z.down.1 hz (congrArg ULift.down h0)
  have e1F : Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
      ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
      (fun y => F (z₀ + r • y)) g =
        SingularPair.relativeHomologyMap SingularPair.integerCoefficients ψF hψF (D.chart x hx).k g := by
    unfold Handle.discClass
    rw [dite_eq_left ⟨hFrc, hFrB, hFrA⟩]
    rfl
  have e2F : Handle.euDiscClass (fun y => Gt (r • y)) g =
      SingularPair.relativeHomologyMap SingularPair.integerCoefficients ιF hιF (D.chart x hx).k g := by
    unfold Handle.euDiscClass
    rw [dite_eq_left ⟨hGrc, hGr0⟩]
  have hmorF : CategoryTheory.CategoryStruct.comp ψF Φ = ιF := by
    ext z i
    have h1 : (Φ (ψF z)).down = Gt (r • z.down.1) := by
      rw [hΦeq]
      rfl
    exact congrArg (fun v : EuclideanSpace ℝ (Fin (D.chart x hx).k) => v.ofLp i) h1
  have keyF : SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k
      (Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
        ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
        (fun y => F (z₀ + r • y)) g) = Handle.euDiscClass (fun y => Gt (r • y)) g := by
    rw [e1F, e2F, ← CategoryTheory.ConcreteCategory.comp_apply,
      ← SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients ψF Φ hψF hΦ (SingularPair.mapsTo_comp hψF hΦ),
      SingularPair.relativeHomologyMap_eq_of_eq SingularPair.integerCoefficients hmorF]
  have hloc : Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
      ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) (fun y => F (z₀ + r • y)) g =
      ((SignType.sign (LinearMap.det (fderiv ℝ (D.tubeCoordE x hx ε (D.chart x hx).k ∘ F) z₀ :
          EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (D.chart x hx).k))) : SignType) : ℤ) •
        Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
          ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
          (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g := by
    apply hinj
    rw [keyF, map_zsmul, key, Hlin r hr0 hrr₂, hGtD]
  have hB : f ⁻¹' Icc a t' ∩ D.tube x hx δ ⊆ f ⁻¹' Icc a t' := inter_subset_left
  have hA : (f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ ⊆ f ⁻¹' Icc a t' \ D.slabCap τ :=
    sdiff_subset_sdiff_left inter_subset_left
  have i1 := Handle.inclPair_discClass hB hA (fun y => F (z₀ + r • y)) hFrc hFrB hFrA g
  have i2 := Handle.inclPair_discClass hB hA (D.smallDiscMap x (D.chart x hx).k (δ / 2))
    hcontD hmapsB hmapsA g
  rw [← i1, hloc, map_zsmul, i2, hrad (δ / 2) ρ₁ hρ hρrm hρ₁ hρ₁r]

theorem discClass_leftDisc_eq_smallDisc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc t (τ - ε) → ∀ w hw, y ∉ D.smallBall w hw)
    {x : M} (hx : x ∈ crit) (hxτ : f x = τ) {μ : ℕ} (hμ : (D.chart x hx).k = μ) {ρ₁ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < D.rm x hx)
    (g : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk μ)))
      (ULift.down ⁻¹' diskSphere μ) μ) :
    Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ) (D.leftDiscMap x μ ε t) g =
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ) (D.smallDiscMap x μ ρ₁) g := by
  classical
  have _unused := And.intro hcrit (And.intro ht' (And.intro hslab hU))
  clear _unused hcrit ht' hslab hU
  subst hμ
  have hk := (D.chart x hx).hk
  have hre : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k),
      (D.chart x hx).toE (Handle.reidx y) = y := by
    intro y
    ext i
    simp [MorseNormalChart.toE, Handle.reidx]
  have hrm0 : 0 < D.rm x hx := D.rm_pos x hx
  have hrmR : D.rm x hx ≤ (D.chart x hx).R := (D.hrm x hx).2
  have hs0 : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
  have hsq2 : Real.sqrt (2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
  have hsrm : Real.sqrt (2 * ε) < D.rm x hx := by
    rw [Real.sqrt_lt' hrm0]
    nlinarith [(hεr x hx).2]
  have htτ' : 0 < τ - ε - t := by linarith
  have hLnorm : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k),
      morseNorm n (recombine (D.chart x hx).hk u 0) = ‖u‖ := by
    intro u
    have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
      (D.chart x hx).hk u 0
    rw [norm_zero] at h
    exact (pow_left_inj₀ (ModelField.morseNorm_nonneg _) (norm_nonneg u) two_ne_zero).1
      (by rw [h]; ring)
  have hfL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) = τ - ‖u‖ ^ 2 / 2 := by
    intro u hu
    rw [(D.chart x hx).hnorm _ (by rw [hLnorm]; exact hu),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, hxτ]
    ring
  have hsrcL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      recombine (D.chart x hx).hk u 0 ∈ (D.chart x hx).χ.source := by
    intro u hu
    exact (D.chart x hx).hsrc _ (by rw [hLnorm]; exact hu)
  have hstripL : ∀ u : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖u‖ ≤ (D.chart x hx).R →
      a < f ((D.chart x hx).χ (recombine (D.chart x hx).hk u 0)) := by
    intro u hu
    exact (D.inStrip x hx ⟨_, (D.chart x hx).mem_ball_of_le (by rw [hLnorm]; exact hu), rfl⟩).1
  have hnotcap : ∀ z : M, f z < τ → z ∉ D.slabCap τ := by
    intro z hz hmem
    simp only [GradientLikeStrip.slabCap, Set.mem_iUnion] at hmem
    obtain ⟨w, hw, hwτ, hzw⟩ := hmem
    exact GradientLikeStrip.notMem_captured_of_f_flow_lt (D := D) hf (t := 0)
      (by rw [D.flow_zero]; linarith) hzw
  let c : EuclideanSpace ℝ (Fin (D.chart x hx).k) → ℝ := fun y =>
    Real.sqrt (2 * ε) / max ‖y‖ (1 / 2)
  let T : EuclideanSpace ℝ (Fin (D.chart x hx).k) → ℝ := fun y =>
    max 0 (2 * ‖y‖ - 1) * (τ - ε - t)
  let G : EuclideanSpace ℝ (Fin (D.chart x hx).k) → M := fun y =>
    D.flow (T y) ((D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0))
  have hmax : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), 0 < max ‖y‖ (1 / 2) :=
    fun y => lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hcy : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖c y • y‖ ≤ Real.sqrt (2 * ε) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs0.le (hmax y).le), div_mul_eq_mul_div,
      div_le_iff₀ (hmax y)]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hs0.le
  have hcyR : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖c y • y‖ ≤ (D.chart x hx).R :=
    fun y => ((hcy y).trans hsrm.le).trans hrmR
  have hcy0 : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), y ≠ 0 → c y • y ≠ 0 :=
    fun y hy => smul_ne_zero (div_pos hs0 (hmax y)).ne' hy
  have hGeq : ∀ y, D.leftDiscMap x (D.chart x hx).k ε t y = G y := by
    intro y
    simp only [GradientLikeStrip.leftDiscMap, hx, ↓reduceDIte, G, T, c]
    split_ifs with h
    · rw [max_eq_left (by linarith), zero_mul, D.flow_zero, max_eq_right h, hre]
      congr 2
      congr 1
      ring
    · rw [not_le] at h
      rw [max_eq_right (by linarith), max_eq_left h.le, hxτ]
      congr 2
      rw [MorseNormalChart.sphereParam, hre]
  have hGc : Continuous G := by
    have h1 : Continuous fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) => c y • y :=
      (continuous_const.div (continuous_norm.max continuous_const)
        (fun y => (hmax y).ne')).smul continuous_id
    have h2 : Continuous fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) =>
        (D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0) :=
      (D.chart x hx).χ.continuousOn.comp_continuous
        ((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
          (D.chart x hx).hk).comp (h1.prodMk continuous_const))
        (fun y => hsrcL _ (hcyR y))
    have h3 : Continuous T :=
      (continuous_const.max ((continuous_const.mul continuous_norm).sub continuous_const)).mul
        continuous_const
    exact D.continuous_flow_joint.comp (h3.prodMk h2)
  have hGB : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), ‖y‖ ≤ 1 →
      G y ∈ f ⁻¹' Icc a t' := by
    intro y hy
    have hT0 : 0 ≤ T y := mul_nonneg (le_max_left _ _) htτ'.le
    have hT1 : T y ≤ τ - ε - t := by
      have : max 0 (2 * ‖y‖ - 1) ≤ 1 := max_le (by norm_num) (by linarith)
      calc T y ≤ 1 * (τ - ε - t) := mul_le_mul_of_nonneg_right this htτ'.le
        _ = τ - ε - t := one_mul _
    have hfz := hfL _ (hcyR y)
    have hsq : ‖c y • y‖ ^ 2 ≤ 2 * ε := by
      rw [← hsq2]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcy y) 2
    have hlo := GradientLikeStrip.sub_le_f_flow (D := D) hf
      ((D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0)) hT0
    have hhi := GradientLikeStrip.f_flow_le (D := D) hf
      ((D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0)) hT0
    refine ⟨?_, ?_⟩
    · change a ≤ f (G y)
      nlinarith [sq_nonneg ‖c y • y‖]
    · change f (G y) ≤ t'
      nlinarith [sq_nonneg ‖c y • y‖]
  have hGA : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k), y ≠ 0 → f (G y) < τ := by
    intro y hy
    have hT0 : 0 ≤ T y := mul_nonneg (le_max_left _ _) htτ'.le
    have hfz := hfL _ (hcyR y)
    have hpos : 0 < ‖c y • y‖ := norm_pos_iff.2 (hcy0 y hy)
    have hhi := GradientLikeStrip.f_flow_le (D := D) hf
      ((D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0)) hT0
    change f (D.flow (T y) ((D.chart x hx).χ (recombine (D.chart x hx).hk (c y • y) 0))) < τ
    nlinarith [sq_nonneg ‖c y • y‖]
  have hSeq : ∀ (δ : ℝ) (y : EuclideanSpace ℝ (Fin (D.chart x hx).k)),
      D.smallDiscMap x (D.chart x hx).k δ y =
        (D.chart x hx).χ (recombine (D.chart x hx).hk (δ • y) 0) := by
    intro δ y
    simp only [GradientLikeStrip.smallDiscMap, hx, ↓reduceDIte, hre]
  have step1 : Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
      (D.leftDiscMap x (D.chart x hx).k ε t) g =
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k (Real.sqrt (2 * ε) / 2)) g := by
    refine Handle.discClass_eq_of_homotopy _ _ _ _ (fun s y => G ((1 - 3 / 4 * s) • y)) ?_ ?_ ?_ ?_ ?_ g
    · exact (hGc.comp ((continuous_const.sub (continuous_const.mul continuous_fst)).smul
        continuous_snd)).continuousOn
    · intro y _
      simp only [mul_zero, sub_zero, one_smul]
      exact (hGeq y).symm
    · intro y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [hSeq]
      have hy' : ‖(1 - 3 / 4 * (1 : ℝ)) • y‖ ≤ 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
        nlinarith [norm_nonneg y]
      change D.flow (T _) ((D.chart x hx).χ (recombine (D.chart x hx).hk (c _ • _) 0)) = _
      simp only [T, c]
      rw [max_eq_left (by linarith), zero_mul, D.flow_zero, max_eq_right hy', smul_smul]
      congr 3
      ring
    · intro s hs y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      apply hGB
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
      nlinarith [norm_nonneg y, hs.1, hs.2]
    · intro s hs y hy
      rw [mem_sphere_zero_iff_norm] at hy
      have hne : (1 - 3 / 4 * s) • y ≠ 0 :=
        smul_ne_zero (by linarith [hs.2]) (by rintro rfl; simp at hy)
      refine ⟨hGB _ ?_, hnotcap _ (hGA _ hne)⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2]), hy]
      linarith [hs.1]
  have step2 : Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
      (D.smallDiscMap x (D.chart x hx).k (Real.sqrt (2 * ε) / 2)) g =
      Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k ρ₁) g := by
    let δ : ℝ → ℝ := fun s => (1 - s) * (Real.sqrt (2 * ε) / 2) + s * ρ₁
    have hδ : ∀ s ∈ Icc (0 : ℝ) 1, 0 < δ s ∧ δ s < D.rm x hx := by
      intro s hs
      constructor
      · change 0 < (1 - s) * (Real.sqrt (2 * ε) / 2) + s * ρ₁
        rcases lt_or_eq_of_le hs.2 with h | h
        · nlinarith [mul_pos (sub_pos.2 h) hs0, mul_nonneg hs.1 hρ₁.le]
        · rw [h]
          linarith
      · change (1 - s) * (Real.sqrt (2 * ε) / 2) + s * ρ₁ < D.rm x hx
        nlinarith [hs.1, hs.2]
    have hnδ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ
        (Fin (D.chart x hx).k)) 1, ‖δ s • y‖ ≤ (D.chart x hx).R := by
      intro s hs y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hδ s hs).1]
      nlinarith [(hδ s hs).1, (hδ s hs).2, norm_nonneg y]
    refine Handle.discClass_eq_of_homotopy _ _ _ _
      (fun s y => (D.chart x hx).χ (recombine (D.chart x hx).hk (δ s • y) 0)) ?_ ?_ ?_ ?_ ?_ g
    · refine (D.chart x hx).χ.continuousOn.comp
        (((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
          (D.chart x hx).hk).comp
          ((((continuous_const.sub continuous_fst).mul continuous_const).add
            (continuous_fst.mul continuous_const)).smul continuous_snd |>.prodMk
            continuous_const)).continuousOn) ?_
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact hsrcL _ (hnδ s hs y hy)
    · intro y _
      rw [hSeq]
      congr 3
      simp [δ]
    · intro y _
      rw [hSeq]
      congr 3
      simp [δ]
    · intro s hs y hy
      have h1 := hfL _ (hnδ s hs y hy)
      refine ⟨(hstripL _ (hnδ s hs y hy)).le, ?_⟩
      change f ((D.chart x hx).χ (recombine (D.chart x hx).hk (δ s • y) 0)) ≤ t'
      rw [h1]
      nlinarith [sq_nonneg ‖δ s • y‖]
    · intro s hs y hy
      have hy' : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
        Metric.sphere_subset_closedBall hy
      rw [mem_sphere_zero_iff_norm] at hy
      have h1 := hfL _ (hnδ s hs y hy')
      have hne : δ s • y ≠ 0 := smul_ne_zero (hδ s hs).1.ne' (by rintro rfl; simp at hy)
      have hpos : 0 < ‖δ s • y‖ := norm_pos_iff.2 hne
      refine ⟨⟨(hstripL _ (hnδ s hs y hy')).le, ?_⟩, hnotcap _ ?_⟩
      · change f ((D.chart x hx).χ (recombine (D.chart x hx).hk (δ s • y) 0)) ≤ t'
        rw [h1]
        nlinarith [sq_nonneg ‖δ s • y‖]
      · rw [h1]
        nlinarith [sq_nonneg ‖δ s • y‖]
  exact step1.trans step2

theorem tube_hpair (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw)
    (hk1 : ∀ x (hx : x ∈ crit), f x = τ → 1 ≤ (D.chart x hx).k) :
    ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (∀ x (hx : x ∈ crit) y (hy : y ∈ crit), f x = τ → f y = τ → x ≠ y →
        Disjoint (D.tube x hx δ) (D.tube y hy δ)) ∧
      ∀ x (hx : x ∈ crit), f x = τ →
        IsOpen (D.tube x hx δ) ∧
        IsOpen (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) :
          Set ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)) ∧
        (∀ j, j ≠ (D.chart x hx).k → CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair
          (f ⁻¹' Icc a t' ∩ D.tube x hx δ) ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) j)) ∧
        ∀ g : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk (D.chart x hx).k)))
            (ULift.down ⁻¹' diskSphere (D.chart x hx).k) (D.chart x hx).k, Handle.isGen g →
          (∀ y : Handle.relativeHomologyPair (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) (D.chart x hx).k, ∃ m : ℤ,
            y = m • Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
              (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g) ∧
          ∀ m : ℤ, m • Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
              (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g = 0 → m = 0 := by
  classical
  obtain ⟨δd, hδd, hdisj⟩ := tube_disjoint hf D hε hεr (τ := τ)
  have hex : ∀ x (hx : x ∈ crit), f x = τ → ∃ d > 0, ∀ δ, 0 < δ → δ < d →
      (IsOpen (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) :
        Set ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)) ∧
      ∃ (Φ : TopCat.of ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ) ⟶
          TopCat.of (SingularPair.EU (D.chart x hx).k))
        (hΦ : MapsTo Φ (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ))
          {ULift.up 0}ᶜ),
        (∀ z, (Φ z).down = D.tubeCoordE x hx ε (D.chart x hx).k z.1) ∧
          ∀ j, CategoryTheory.IsIso (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ j)) ∧
      (∀ z ∈ f ⁻¹' Icc a t' ∩ D.tube x hx δ,
        (D.tubeCoordE x hx ε (D.chart x hx).k z = 0 ↔ z ∈ D.slabCap τ)) ∧
      δ / 2 < D.rm x hx := by
    intro x hx hxτ
    obtain ⟨d1, hd1, H1⟩ := isIso_tubeCoord hf D hcrit hε hεr ht htτ hτt' ht' hslab hU hx hxτ rfl
      (hk1 x hx hxτ)
    obtain ⟨d2, hd2, H2⟩ := tubeCoord_spec hf D hcrit hε hεr ht htτ hτt' ht' hslab hU hx hxτ rfl
    refine ⟨min (min d1 d2) (2 * D.rm x hx),
      lt_min (lt_min hd1 hd2) (by linarith [D.rm_pos x hx]), fun δ hδ hδd => ?_⟩
    have h1 : δ < d1 := lt_of_lt_of_le hδd ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : δ < d2 := lt_of_lt_of_le hδd ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : δ < 2 * D.rm x hx := lt_of_lt_of_le hδd (min_le_right _ _)
    exact ⟨H1 δ hδ h1, (H2 δ hδ h2).2, by linarith⟩
  choose d hdpos hd using hex
  let d' : M → ℝ := fun x => if h : x ∈ crit ∧ f x = τ then d x h.1 h.2 else 1
  have hd'pos : ∀ x, 0 < d' x := by
    intro x
    simp only [d']
    split_ifs with h
    · exact hdpos x h.1 h.2
    · exact one_pos
  have hsne : (insert (1 : ℝ) (crit.image d')).Nonempty := Finset.insert_nonempty _ _
  have hmpos : 0 < (insert (1 : ℝ) (crit.image d')).min' hsne := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
      exact hd'pos x
  have hmle : ∀ x (hx : x ∈ crit) (hxτ : f x = τ),
      (insert (1 : ℝ) (crit.image d')).min' hsne ≤ d x hx hxτ := by
    intro x hx hxτ
    have := Finset.min'_le (insert (1 : ℝ) (crit.image d')) (d' x)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem d' hx))
    simpa [d', hx, hxτ] using this
  refine ⟨min δd ((insert (1 : ℝ) (crit.image d')).min' hsne), lt_min hδd hmpos,
    fun δ hδ hδ₀ => ⟨fun x hx y hy hxτ hyτ hxy =>
      hdisj δ hδ (lt_of_lt_of_le hδ₀ (min_le_left _ _)) x hx y hy hxτ hyτ hxy,
      fun x hx hxτ => ?_⟩⟩
  have hδx : δ < d x hx hxτ := lt_of_lt_of_le hδ₀ ((min_le_right _ _).trans (hmle x hx hxτ))
  obtain ⟨⟨hopen, Φ, hΦ, hΦeq, hiso⟩, hzero, hρrm⟩ := hd x hx hxτ δ hδ hδx
  have hk1x := hk1 x hx hxτ
  refine ⟨isOpen_tube D hx δ, hopen, fun j hj => ?_, fun g hg => ?_⟩
  · have := hiso j
    exact (SingularPair.isZero_relativeHomology_EU_compl_singleton SingularPair.integerCoefficients hk1x (ULift.up 0) hj).of_iso
      (CategoryTheory.asIso (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ j))
  · have hρ : 0 < δ / 2 := by linarith
    have hdisc : ∀ y : EuclideanSpace ℝ (Fin (D.chart x hx).k),
        D.smallDiscMap x (D.chart x hx).k (δ / 2) y =
          (D.chart x hx).χ (recombine (D.chart x hx).hk ((δ / 2) • y) 0) := by
      intro y
      have hy : (D.chart x hx).toE (Handle.reidx y) = y := by
        ext i
        simp [MorseNormalChart.toE, Handle.reidx]
      rw [smallDiscMap, dite_eq_left hx, hy]
    have hnormz : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
        morseNorm n (recombine (D.chart x hx).hk ((δ / 2) • y) 0) ≤ δ / 2 := by
      intro y hy
      have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
        (D.chart x hx).hk ((δ / 2) • y) 0
      have h2 := ModelField.morseNorm_nonneg (recombine (D.chart x hx).hk ((δ / 2) • y) 0)
      have hy1 : ‖y‖ ≤ 1 := by simpa using hy
      rw [norm_zero, norm_smul, Real.norm_of_nonneg hρ.le] at h1
      have h3 : δ / 2 * ‖y‖ ≤ δ / 2 := mul_le_of_le_one_right hρ.le hy1
      have h4 : 0 ≤ δ / 2 * ‖y‖ := by positivity
      nlinarith
    have hRle : δ / 2 ≤ (D.chart x hx).R := hρrm.le.trans (D.hrm x hx).2
    have hcontR : Continuous (fun y : EuclideanSpace ℝ (Fin (D.chart x hx).k) =>
        recombine (D.chart x hx).hk ((δ / 2) • y) 0) :=
      (DifferentialGeometry.Topology.Morse.CellAttachment.continuous_recombine
        (D.chart x hx).hk).comp ((continuous_const_smul (δ / 2)).prodMk continuous_const)
    have hcontD : ContinuousOn (D.smallDiscMap x (D.chart x hx).k (δ / 2))
        (Metric.closedBall 0 1) := by
      have : D.smallDiscMap x (D.chart x hx).k (δ / 2) =
          fun y => (D.chart x hx).χ (recombine (D.chart x hx).hk ((δ / 2) • y) 0) := funext hdisc
      rw [this]
      exact (D.chart x hx).χ.continuousOn.comp hcontR.continuousOn
        (fun y hy => (D.chart x hx).hsrc _ ((hnormz y hy).trans hRle))
    have hmapsB : MapsTo (D.smallDiscMap x (D.chart x hx).k (δ / 2)) (Metric.closedBall 0 1)
        (f ⁻¹' Icc a t' ∩ D.tube x hx δ) := by
      intro y hy
      rw [hdisc]
      have hnz := hnormz y hy
      have hneg : ‖negPart (D.chart x hx).hk (recombine (D.chart x hx).hk ((δ / 2) • y) 0)‖ ≤
          δ / 2 := by
        rw [ModelField.negPart_recombine, norm_smul, Real.norm_of_nonneg hρ.le]
        have : ‖y‖ ≤ 1 := by simpa using hy
        exact mul_le_of_le_one_right hρ.le this
      refine ⟨⟨?_, ?_⟩, 0, le_rfl, ?_⟩
      · exact (D.inStrip x hx ⟨_, (D.chart x hx).mem_ball_of_le (hnz.trans hRle), rfl⟩).1.le
      · rw [(D.chart x hx).hnorm _ (hnz.trans hRle),
          DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
          ModelField.posPart_recombine, hxτ, norm_zero]
        nlinarith [sq_nonneg ‖negPart (D.chart x hx).hk
          (recombine (D.chart x hx).hk ((δ / 2) • y) 0)‖]
      · rw [D.flow_zero]
        exact ⟨_, ⟨lt_of_le_of_lt hnz hρrm, lt_of_le_of_lt hneg (by linarith)⟩, rfl⟩
    have htc : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1,
        D.tubeCoordE x hx ε (D.chart x hx).k (D.smallDiscMap x (D.chart x hx).k (δ / 2) y) =
          (δ / 2) • y :=
      tubeCoord_smallDisc D hx rfl hε hρ (hρrm.trans_le (D.hrm x hx).2)
    have hmapsA : MapsTo (D.smallDiscMap x (D.chart x hx).k (δ / 2)) (Metric.sphere 0 1)
        ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) := by
      intro y hy
      have hyb : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (D.chart x hx).k)) 1 :=
        Metric.sphere_subset_closedBall hy
      refine ⟨hmapsB hyb, fun hcap => ?_⟩
      have h0 := (hzero _ (hmapsB hyb)).2 hcap
      rw [htc y hyb] at h0
      have hy1 : ‖y‖ = 1 := by simpa using hy
      rcases smul_eq_zero.1 h0 with h | h
      · linarith
      · rw [h, norm_zero] at hy1
        exact zero_ne_one hy1
    let A : EuclideanSpace ℝ (Fin (D.chart x hx).k) ≃L[ℝ] EuclideanSpace ℝ (Fin (D.chart x hx).k) :=
      (LinearEquiv.smulOfNeZero ℝ _ (δ / 2) hρ.ne').toContinuousLinearEquiv
    have hAdet : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (D.chart x hx).k)) := by
      have hAeq : (A : EuclideanSpace ℝ (Fin (D.chart x hx).k) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (D.chart x hx).k)) = (δ / 2) • LinearMap.id :=
        LinearMap.ext fun v => rfl
      rw [hAeq, LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin, mul_one]
      exact pow_pos hρ _
    let ψ : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
        TopCat.of ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ) :=
      TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) =>
          (⟨D.smallDiscMap x (D.chart x hx).k (δ / 2) z.down.1, hmapsB z.down.2⟩ :
            ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)),
        (hcontD.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun z => z.down.2)).subtype_mk _⟩
    have hψ : MapsTo ψ (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
        (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)) :=
      fun z hz => hmapsA hz
    let ι : TopCat.of (ULift.{u_2} (Disk (D.chart x hx).k)) ⟶
        TopCat.of (SingularPair.EU.{u_2} (D.chart x hx).k) :=
      TopCat.ofHom ⟨fun z : ULift.{u_2} (Disk (D.chart x hx).k) => ULift.up z.down.1,
        continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩
    have hι : MapsTo ι (ULift.down ⁻¹' diskSphere (D.chart x hx).k)
        ({ULift.up 0}ᶜ : Set (SingularPair.EU.{u_2} (D.chart x hx).k)) := by
      intro z hz h0
      have hz1 : ‖z.down.1‖ = 1 := by simpa [diskSphere] using hz
      have h0' : z.down.1 = 0 := congrArg ULift.down h0
      rw [h0', norm_zero] at hz1
      exact zero_ne_one hz1
    have e1 : Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
        ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
        (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g =
          SingularPair.relativeHomologyMap SingularPair.integerCoefficients ψ hψ (D.chart x hx).k g := by
      unfold Handle.discClass
      rw [dite_eq_left ⟨hcontD, hmapsB, hmapsA⟩]
      rfl
    have e2 : Handle.euDiscClass (fun y => y) g =
        SingularPair.relativeHomologyMap SingularPair.integerCoefficients ι hι (D.chart x hx).k g := by
      unfold Handle.euDiscClass
      rw [dite_eq_left ⟨continuous_id.continuousOn, fun y hy h0 => by
        have hy1 : ‖y‖ = 1 := by simpa using hy
        simp only at h0
        rw [h0, norm_zero] at hy1
        exact zero_ne_one hy1⟩]
    have hmor : CategoryTheory.CategoryStruct.comp ψ Φ =
        CategoryTheory.CategoryStruct.comp ι (Handle.euMap A) := by
      ext z i
      have h1 : (Φ (ψ z)).down = A z.down.1 := by
        rw [hΦeq]
        exact htc z.down.1 z.down.2
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (D.chart x hx).k) => v.ofLp i) h1
    have key : SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k
        (Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
          ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
          (D.smallDiscMap x (D.chart x hx).k (δ / 2)) g) = Handle.euDiscClass (fun y => y) g := by
      rw [← Handle.hrelMap_euMap_of_det_pos hk1x A hAdet (Handle.euDiscClass (fun y => y) g), e1, e2,
        ← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
        ← SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients ψ Φ hψ hΦ (SingularPair.mapsTo_comp hψ hΦ),
        ← SingularPair.relativeHomologyMap_comp SingularPair.integerCoefficients ι (Handle.euMap A) hι (Handle.euMap_mapsTo A)
          (SingularPair.mapsTo_comp hι (Handle.euMap_mapsTo A)),
        SingularPair.relativeHomologyMap_eq_of_eq SingularPair.integerCoefficients hmor]
    obtain ⟨hgen, hind⟩ := Handle.euDiscClass_isGen hk1x g hg
    have := hiso (D.chart x hx).k
    have hinj : Function.Injective (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine ⟨fun y => ?_, fun m hm => ?_⟩
    · obtain ⟨m, hm⟩ := hgen (SingularPair.relativeHomologyMap SingularPair.integerCoefficients Φ hΦ (D.chart x hx).k y)
      refine ⟨m, hinj ?_⟩
      rw [hm, map_zsmul, key]
    · apply hind m
      rw [← key, ← map_zsmul, hm, map_zero]

theorem slab_hpair_vanishes (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc t (τ - ε) ∪ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw)
    (hk1 : ∀ x (hx : x ∈ crit), f x = τ → 1 ≤ (D.chart x hx).k) (j : ℕ)
    (hj : ∀ x (hx : x ∈ crit), f x = τ → (D.chart x hx).k ≠ j) :
    CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) j) := by
  classical
  obtain ⟨hsub, hiso⟩ := isIso_inclPair_slab hf D hcrit hε hεr ht htτ hτt' ht' hslab
  have := hiso j
  refine CategoryTheory.Limits.IsZero.of_iso ?_
    (CategoryTheory.asIso (Handle.inclPair (subset_refl (f ⁻¹' Icc a t')) hsub j))
  obtain ⟨δ₀, hδ₀, hT⟩ := tube_hpair hf D hcrit hε hεr ht htτ hτt' ht' hslab
    (fun y hy w hw => hU y (Or.inr hy) w hw) hk1
  have hδ : 0 < δ₀ / 2 := half_pos hδ₀
  obtain ⟨hdisj, hloc⟩ := hT (δ₀ / 2) hδ (half_lt_self hδ₀)
  have := isIso_excise_tubes hf D hcrit hε hεr ht htτ hτt' ht' hslab hδ j
  refine CategoryTheory.Limits.IsZero.of_iso ?_ (CategoryTheory.asIso (Handle.inclPair
      (inter_subset_left : f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ),
        D.tube x hx (δ₀ / 2)) ⊆ f ⁻¹' Icc a t')
      (sdiff_subset_sdiff_left inter_subset_left :
        (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx (δ₀ / 2))) \
          D.slabCap τ ⊆ f ⁻¹' Icc a t' \ D.slabCap τ) j)).symm
  set s : Finset {x // x ∈ crit} := crit.attach.filter (fun i => f i.1 = τ) with hs
  set U : {x // x ∈ crit} → Set M := fun i => f ⁻¹' Icc a t' ∩ D.tube i.1 i.2 (δ₀ / 2) with hUdef
  have hEq : (⋃ i ∈ s, U i) = f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ),
      D.tube x hx (δ₀ / 2)) := by
    ext z
    simp only [hs, hUdef, mem_iUnion, Finset.mem_filter, Finset.mem_attach, true_and, mem_inter_iff,
      exists_prop, Subtype.exists]
    constructor
    · rintro ⟨x, hx, hxτ, hz1, hz2⟩
      exact ⟨hz1, x, hx, hxτ, hz2⟩
    · rintro ⟨hz1, x, hx, hxτ, hz2⟩
      exact ⟨x, hx, hxτ, hz1, hz2⟩
  rw [← hEq]
  refine Handle.relativeHomologyPair_iUnion_vanishes s U (D.slabCap τ) ?_ ?_ ?_ j ?_
  · intro i hi
    have hi' : f i.1 = τ := (Finset.mem_filter.mp hi).2
    have hO : IsOpen (D.tube i.1 i.2 (δ₀ / 2)) := (hloc i.1 i.2 hi').1
    have hset : (Subtype.val ⁻¹' U i : Set ↥(⋃ i ∈ s, U i)) =
        Subtype.val ⁻¹' D.tube i.1 i.2 (δ₀ / 2) := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        refine ⟨?_, hz⟩
        obtain ⟨k, hk⟩ := mem_iUnion₂.mp z.2
        exact hk.2.1
    rw [hset]
    exact hO.preimage continuous_subtype_val
  · intro i hi
    exact (hloc i.1 i.2 (Finset.mem_filter.mp hi).2).2.1
  · intro i hi i' hi' hne
    exact hdisj i.1 i.2 i'.1 i'.2 (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
      (fun h => hne (Subtype.ext h)) |>.mono inter_subset_right inter_subset_right
  · intro i hi
    have hi' : f i.1 = τ := (Finset.mem_filter.mp hi).2
    exact (hloc i.1 i.2 hi').2.2.1 j (hj i.1 i.2 hi').symm

theorem slab_discClass_basis (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {t τ t' : ℝ}
    (ht : a ≤ t) (htτ : t < τ - ε) (hτt' : τ + ε < t') (ht' : t' ≤ b)
    (hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ)
    (hU : ∀ y, f y ∈ Icc t (τ - ε) ∪ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw) {μ : ℕ}
    (hμ : ∀ x (hx : x ∈ crit), f x = τ → (D.chart x hx).k = μ) (hμ1 : 1 ≤ μ)
    (g : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk μ)))
      (ULift.down ⁻¹' diskSphere μ) μ) (hg : Handle.isGen g) :
    (∀ y : Handle.relativeHomologyPair (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) μ, ∃ v : M → ℤ,
      y = ∑ x ∈ crit.filter (fun x => f x = τ),
        v x • Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) (D.leftDiscMap x μ ε t) g) ∧
    ∀ v : M → ℤ, ∑ x ∈ crit.filter (fun x => f x = τ),
        v x • Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) (D.leftDiscMap x μ ε t) g = 0 →
      ∀ x ∈ crit.filter (fun x => f x = τ), v x = 0 := by
  classical
  have hUup : ∀ y, f y ∈ Icc (τ + ε) t' → ∀ w hw, y ∉ D.smallBall w hw :=
    fun y hy => hU y (Or.inr hy)
  have hUlo : ∀ y, f y ∈ Icc t (τ - ε) → ∀ w hw, y ∉ D.smallBall w hw :=
    fun y hy => hU y (Or.inl hy)
  have hk1 : ∀ x (hx : x ∈ crit), f x = τ → 1 ≤ (D.chart x hx).k :=
    fun x hx hxτ => (hμ x hx hxτ) ▸ hμ1
  obtain ⟨hsub, hφ⟩ := D.isIso_inclPair_slab hf hcrit hε hεr ht htτ hτt' ht' hslab
  have := hφ μ
  have hφbij := CategoryTheory.ConcreteCategory.bijective_of_isIso
    (Handle.inclPair (subset_refl (f ⁻¹' Icc a t')) hsub μ)
  obtain ⟨ρ, hρ, hρrm⟩ : ∃ ρ > 0, ∀ x (hx : x ∈ crit), ρ ≤ D.rm x hx := by
    rcases isEmpty_or_nonempty {p // p ∈ crit} with hE | hE
    · exact ⟨1, one_pos, fun x hx => (hE.false ⟨x, hx⟩).elim⟩
    · obtain ⟨p₀, hp₀⟩ := Finite.exists_min (fun p : {p // p ∈ crit} => D.rm p.1 p.2)
      exact ⟨D.rm p₀.1 p₀.2, D.rm_pos _ _, fun x hx => hp₀ ⟨x, hx⟩⟩
  obtain ⟨δ₀, hδ₀, htube⟩ := D.tube_hpair hf hcrit hε hεr ht htτ hτt' ht' hslab hUup hk1
  obtain ⟨δ, hδ, hδδ₀, hδρ⟩ : ∃ δ, 0 < δ ∧ δ < δ₀ ∧ δ / 2 < ρ := by
    refine ⟨min (δ₀ / 2) ρ, lt_min (by linarith) hρ, (min_le_left _ _).trans_lt (by linarith), ?_⟩
    have := min_le_right (δ₀ / 2) ρ
    linarith
  obtain ⟨hdisj, hloc⟩ := htube δ hδ hδδ₀
  have hloc' : ∀ x (hx : x ∈ crit), f x = τ →
      IsOpen (D.tube x hx δ) ∧
      IsOpen (Subtype.val ⁻¹' ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) :
          Set ↥(f ⁻¹' Icc a t' ∩ D.tube x hx δ)) ∧
      (∀ y : Handle.relativeHomologyPair (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ) μ, ∃ m : ℤ,
            y = m • Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
              (D.smallDiscMap x μ (δ / 2)) g) ∧
      ∀ m : ℤ, m • Handle.discClass (f ⁻¹' Icc a t' ∩ D.tube x hx δ)
              ((f ⁻¹' Icc a t' ∩ D.tube x hx δ) \ D.slabCap τ)
              (D.smallDiscMap x μ (δ / 2)) g = 0 → m = 0 := by
    intro x hx hxτ
    obtain ⟨h1, h2, -, h4⟩ := hloc x hx hxτ
    have hk := hμ x hx hxτ
    rw [hk] at h4
    exact ⟨h1, h2, h4 g hg⟩
  let U : M → Set M := fun x => if hx : x ∈ crit then f ⁻¹' Icc a t' ∩ D.tube x hx δ else ∅
  have hUx : ∀ x (hx : x ∈ crit), U x = f ⁻¹' Icc a t' ∩ D.tube x hx δ := fun x hx => dite_eq_left hx
  have hUnion : (⋃ i ∈ crit.filter (fun x => f x = τ), U i) =
      f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨i, ⟨hi, hiτ⟩, hz⟩
      rw [hUx i hi] at hz
      exact ⟨hz.1, i, hi, hiτ, hz.2⟩
    · rintro ⟨hzW, i, hi, hiτ, hz⟩
      exact ⟨i, ⟨hi, hiτ⟩, by rw [hUx i hi]; exact ⟨hzW, hz⟩⟩
  have hUopen : ∀ i ∈ crit.filter (fun x => f x = τ),
      IsOpen (Subtype.val ⁻¹' U i : Set ↥(⋃ i ∈ crit.filter (fun x => f x = τ), U i)) := by
    intro i hi
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    have heq : (Subtype.val ⁻¹' U i : Set ↥(⋃ i ∈ crit.filter (fun x => f x = τ), U i)) =
        Subtype.val ⁻¹' D.tube i hic δ := by
      ext z
      simp only [mem_preimage, hUx i hic, mem_inter_iff, and_iff_right_iff_imp]
      intro _
      exact (hUnion.subset z.2).1
    rw [heq]
    exact (hloc' i hic hiτ).1.preimage continuous_subtype_val
  have hK : ∀ i ∈ crit.filter (fun x => f x = τ),
      IsOpen (Subtype.val ⁻¹' (U i \ D.slabCap τ) : Set ↥(U i)) := by
    intro i hi
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    rw [hUx i hic]
    exact (hloc' i hic hiτ).2.1
  have hdisjU : ∀ i ∈ crit.filter (fun x => f x = τ), ∀ i' ∈ crit.filter (fun x => f x = τ),
      i ≠ i' → Disjoint (U i) (U i') := by
    intro i hi i' hi' hne
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    obtain ⟨hic', hiτ'⟩ := Finset.mem_filter.1 hi'
    rw [hUx i hic, hUx i' hic']
    exact (hdisj i hic i' hic' hiτ hiτ' hne).mono inter_subset_right inter_subset_right
  have hspanU : ∀ i ∈ crit.filter (fun x => f x = τ),
      ∀ y : Handle.relativeHomologyPair (U i) (U i \ D.slabCap τ) μ, ∃ m : ℤ,
        y = m • Handle.discClass (U i) (U i \ D.slabCap τ) (D.smallDiscMap i μ (δ / 2)) g := by
    intro i hi
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    rw [hUx i hic]
    exact (hloc' i hic hiτ).2.2.1
  have hindU : ∀ i ∈ crit.filter (fun x => f x = τ), ∀ m : ℤ,
      m • Handle.discClass (U i) (U i \ D.slabCap τ) (D.smallDiscMap i μ (δ / 2)) g = 0 →
        m = 0 := by
    intro i hi
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    rw [hUx i hic]
    exact (hloc' i hic hiτ).2.2.2
  obtain ⟨hspanT, hindT⟩ := Handle.relativeHomologyPair_iUnion_basis (crit.filter (fun x => f x = τ)) U
    (D.slabCap τ) hUopen hK hdisjU (fun i => D.smallDiscMap i μ (δ / 2)) g hspanU hindU
  rw [hUnion] at hspanT hindT
  have hEW : f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) ⊆
      f ⁻¹' Icc a t' := inter_subset_left
  have hEWc : (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
      D.slabCap τ ⊆ f ⁻¹' Icc a t' \ D.slabCap τ := sdiff_subset_sdiff_left inter_subset_left
  have hψ : CategoryTheory.IsIso (Handle.inclPair hEW hEWc μ) :=
    D.isIso_excise_tubes hf hcrit hε hεr ht htτ hτt' ht' hslab hδ μ
  have hψbij := CategoryTheory.ConcreteCategory.bijective_of_isIso (Handle.inclPair hEW hEWc μ)
  have hsmall : ∀ i (hic : i ∈ crit), f i = τ →
      ContinuousOn (D.smallDiscMap i μ (δ / 2)) (Metric.closedBall 0 1) ∧
      MapsTo (D.smallDiscMap i μ (δ / 2)) (Metric.closedBall 0 1)
        (f ⁻¹' Icc a t' ∩ D.tube i hic δ) ∧
      MapsTo (D.smallDiscMap i μ (δ / 2)) (Metric.sphere 0 1)
        ((f ⁻¹' Icc a t' ∩ D.tube i hic δ) \ D.slabCap τ) := by
    intro i hic hiτ
    by_contra hcon
    have h1 := (hloc' i hic hiτ).2.2.2 1
    rw [one_smul] at h1
    unfold Handle.discClass at h1
    rw [dite_eq_right hcon] at h1
    exact one_ne_zero (h1 rfl)
  have hkey : ∀ i ∈ crit.filter (fun x => f x = τ),
      Handle.inclPair (subset_refl (f ⁻¹' Icc a t')) hsub μ
        (Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) (D.leftDiscMap i μ ε t) g) =
      Handle.inclPair hEW hEWc μ
        (Handle.discClass
          (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ))
          ((f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
            D.slabCap τ) (D.smallDiscMap i μ (δ / 2)) g) := by
    intro i hi
    obtain ⟨hic, hiτ⟩ := Finset.mem_filter.1 hi
    obtain ⟨hsc, hsB, hsA⟩ := hsmall i hic hiτ
    have hmemU : ∀ z ∈ D.tube i hic δ,
        z ∈ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ) := fun z hz =>
      mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hic, mem_iUnion.2 ⟨hiτ, hz⟩⟩⟩
    have hsE : MapsTo (D.smallDiscMap i μ (δ / 2)) (Metric.closedBall 0 1)
        (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) :=
      fun z hz => ⟨(hsB hz).1, hmemU _ (hsB hz).2⟩
    have hsEA : MapsTo (D.smallDiscMap i μ (δ / 2)) (Metric.sphere 0 1)
        ((f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
          D.slabCap τ) :=
      fun z hz => ⟨⟨(hsA hz).1.1, hmemU _ (hsA hz).1.2⟩, (hsA hz).2⟩
    have hψe := Handle.inclPair_discClass hEW hEWc _ hsc hsE hsEA g
    have hsmallW := (D.discClass_leftDisc_eq_smallDisc hf hcrit hε hεr ht htτ hτt' ht' hslab
      hUlo hic hiτ (hμ i hic hiτ) (half_pos hδ) (lt_of_lt_of_le hδρ (hρrm i hic)) g).symm
    have heT : Handle.discClass
        (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ))
        ((f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
          D.slabCap τ) (D.smallDiscMap i μ (δ / 2)) g ≠ 0 := by
      intro h0
      have := hindT (fun j => if j = i then 1 else 0) (by
        rw [Finset.sum_eq_single i]
        · simp [h0]
        · intro j _ hji
          simp [hji]
        · intro hni
          exact absurd hi hni) i hi
      simp at this
    have hd : Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t' \ D.slabCap τ)
        (D.leftDiscMap i μ ε t) g ≠ 0 := by
      rw [← hsmallW, ← hψe]
      intro h0
      exact heT (hψbij.1 (h0.trans (map_zero _).symm))
    obtain ⟨hlc, hlB, -⟩ : ContinuousOn (D.leftDiscMap i μ ε t) (Metric.closedBall 0 1) ∧
        MapsTo (D.leftDiscMap i μ ε t) (Metric.closedBall 0 1) (f ⁻¹' Icc a t') ∧
        MapsTo (D.leftDiscMap i μ ε t) (Metric.sphere 0 1) (f ⁻¹' Icc a t' \ D.slabCap τ) := by
      by_contra hcon
      apply hd
      unfold Handle.discClass
      rw [dite_eq_right hcon]
    have hlt : MapsTo (D.leftDiscMap i μ ε t) (Metric.sphere 0 1) (f ⁻¹' Icc a t) := by
      intro y hy
      have hy1 : ‖y‖ = 1 := by simpa using hy
      have hk := hμ i hic hiτ
      have hw : (Handle.reidx y : Fin (D.chart i hic).k → ℝ) ≠ 0 := by
        intro h0
        have hy0 : y = 0 := by
          ext j
          have := congrFun h0 ⟨j.1, by rw [hk]; exact j.2⟩
          simp only [Handle.reidx, dite_eq_left j.2, Pi.zero_apply] at this
          simpa using this
        rw [hy0, norm_zero] at hy1
        exact zero_ne_one hy1
      have hε2 : 2 * ε ≤ (D.chart i hic).R ^ 2 := by
        have h1 := (hεr i hic).2
        have h2 := (D.hrm i hic).2
        have h3 := D.rm_pos i hic
        nlinarith
      have hmem := (D.chart i hic).sphereParam_mem_leftModelSphere hε.le hw
      have hf0 := (D.chart i hic).f_chart_of_mem_leftModelSphere hε2 hmem
      have hval : D.leftDiscMap i μ ε t y = D.flow (τ - ε - t)
          ((D.chart i hic).χ ((D.chart i hic).sphereParam ε (Handle.reidx y))) := by
        unfold leftDiscMap
        rw [dite_eq_left hic, ite_eq_right (by rw [hy1]; norm_num), hy1, hiτ]
        congr 1
        ring
      have hlev := f_flow_eq_sub_of_levels hf (D := D)
        (x := (D.chart i hic).χ ((D.chart i hic).sphereParam ε (Handle.reidx y)))
        (T := τ - ε - t)
        (by rw [hf0, hiτ]; constructor <;> linarith)
        (by rw [hf0, hiτ]; constructor <;> linarith)
        (fun z hz p hp => by
          rw [hf0, hiτ] at hz
          have he : τ - ε - (τ - ε - t) = t := by ring
          rw [he, uIcc_of_ge (by linarith)] at hz
          exact hUlo z hz p hp)
        (τ - ε - t) (by rw [uIcc_of_le (by linarith)]; exact right_mem_Icc.2 (by linarith))
      rw [mem_preimage, hval, hlev, hf0, hiτ]
      constructor <;> linarith
    rw [Handle.inclPair_discClass (subset_refl _) hsub _ hlc hlB hlt g, hψe, hsmallW]
  generalize Handle.inclPair (subset_refl (f ⁻¹' Icc a t')) hsub μ = φ at hφbij hkey
  generalize Handle.inclPair hEW hEWc μ = ψ at hψbij hkey
  refine ⟨fun y => ?_, fun v hv i hi => ?_⟩
  · obtain ⟨z, hz⟩ := hψbij.2 (CategoryTheory.ConcreteCategory.hom φ y)
    obtain ⟨v, hv⟩ := hspanT z
    refine ⟨v, hφbij.1 ?_⟩
    rw [← hz, hv, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_zsmul, map_zsmul, hkey j hj]
  · have h1 : CategoryTheory.ConcreteCategory.hom ψ (∑ j ∈ crit.filter (fun x => f x = τ), v j •
        Handle.discClass
          (f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ))
          ((f ⁻¹' Icc a t' ∩ (⋃ (x : M) (hx : x ∈ crit) (_ : f x = τ), D.tube x hx δ)) \
            D.slabCap τ) (D.smallDiscMap j μ (δ / 2)) g) = CategoryTheory.ConcreteCategory.hom ψ 0 := by
      rw [map_zero, map_sum, ← map_zero (CategoryTheory.ConcreteCategory.hom φ), ← hv, map_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_zsmul, map_zsmul, hkey j hj]
    exact hindT v (hψbij.1 h1) i hi

theorem hpair_vanishes_above (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {c' : ℝ}
    (hc' : a ≤ c') (hc'b : c' ≤ b) (hreg : ∀ x ∈ crit, f x ≠ c') {j : ℕ}
    (hidx : ∀ x ∈ crit, c' < f x → j < morseIndex I f x) :
    CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair (f ⁻¹' Icc a b) (f ⁻¹' Icc a c') j) := by
  classical
  have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have glue : ∀ {T S Y : Set M} (hTS : T ⊆ S) (hSY : S ⊆ Y),
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair S T j) →
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair Y S j) →
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair Y T j) := by
    intro T S Y hTS hSY h1 h2
    rw [ModuleCat.isZero_iff_subsingleton] at h1 h2 ⊢
    have key : ∀ z : Handle.relativeHomologyPair Y T j, z = 0 := by
      intro z
      obtain ⟨y, hy⟩ := Handle.triple_exact_mid hTS hSY j z (Subsingleton.elim _ _)
      rw [← hy, Subsingleton.elim y 0, map_zero]
    exact ⟨fun x x' => by rw [key x, key x']⟩
  have hslabZ : ∀ t τ t' : ℝ, a ≤ t → t < τ → τ < t' → t' ≤ b →
      (∀ x ∈ crit, f x < t ∨ f x = τ ∨ t' < f x) →
      (∀ x ∈ crit, f x = τ → j < morseIndex I f x) →
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) j) := by
    intro t τ t' ht htτ hτt' ht' hsep hidx'
    obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ x ∈ crit,
        (f x < t → f x + δ ≤ t) ∧ (t' < f x → t' + δ ≤ f x) := by
      by_cases hne : crit.Nonempty
      · obtain ⟨x₀, hx₀, hmin⟩ :=
          crit.exists_min_image (fun x => min |f x - t| |f x - t'|) hne
        have hne₁ : f x₀ - t ≠ 0 := by
          intro h0
          rcases hsep x₀ hx₀ with h | h | h <;> linarith
        have hne₂ : f x₀ - t' ≠ 0 := by
          intro h0
          rcases hsep x₀ hx₀ with h | h | h <;> linarith
        refine ⟨min |f x₀ - t| |f x₀ - t'|,
          lt_min (abs_pos.mpr hne₁) (abs_pos.mpr hne₂), fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
        · have h1 := (hmin x hx).trans (min_le_left _ _)
          rw [abs_of_neg (show f x - t < 0 by linarith)] at h1
          linarith
        · have h1 := (hmin x hx).trans (min_le_right _ _)
          rw [abs_of_pos (show 0 < f x - t' by linarith)] at h1
          linarith
      · refine ⟨1, one_pos, fun x hx => ?_⟩
        exact absurd ⟨x, hx⟩ hne
    set ε₁ := min ε (min ((τ - t) / 2) (min ((t' - τ) / 2) δ)) with hε₁def
    have hε₁ : 0 < ε₁ := lt_min hε (lt_min (by linarith) (lt_min (by linarith) hδ))
    have hε₁ε : ε₁ ≤ ε := min_le_left _ _
    have hε₁t : ε₁ ≤ (τ - t) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hε₁t' : ε₁ ≤ (t' - τ) / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hε₁δ : ε₁ ≤ δ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨D', -, hch, hr, -⟩ := GradientLikeStrip.exists_shrink_field hsm D hε₁
      (ρ := 8 * ε₁ + 1) (by linarith) (by nlinarith)
      (fun x hx => by have := (hεr x hx).2; linarith)
    have hεr' : ∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < D'.rm x hx ^ 2 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hr x hx
      refine ⟨h1, ?_⟩
      rw [h2]
      rcases min_choice (8 * ε₁ + 1) (D.rm x hx) with h | h <;> rw [h]
      · nlinarith
      · have := (hεr x hx).2
        linarith
    have hslab : ∀ x ∈ crit, f x ∈ Icc t t' → f x = τ := by
      intro x hx hmem
      rcases hsep x hx with h | h | h
      · linarith [hmem.1]
      · exact h
      · linarith [hmem.2]
    have hU : ∀ y, f y ∈ Icc t (τ - ε₁) ∪ Icc (τ + ε₁) t' →
        ∀ w hw, y ∉ D'.smallBall w hw := by
      intro y hy w hw hyw
      have habs := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hw hyw
      have hr0 := (hr w hw).1
      rw [abs_lt] at habs
      obtain ⟨hl, hu⟩ := hδle w hw
      rcases hsep w hw with h | h | h
      · have := hl h
        rcases hy with hy | hy <;> linarith [hy.1, hy.2]
      · rw [h] at habs
        rcases hy with hy | hy <;> linarith [hy.1, hy.2]
      · have := hu h
        rcases hy with hy | hy <;> linarith [hy.1, hy.2]
    have hk1 : ∀ x (hx : x ∈ crit), f x = τ → 1 ≤ (D'.chart x hx).k := by
      intro x hx h
      rw [(hch x hx).2.1, ← (D.chart x hx).hkidx]
      have := hidx' x hx h
      omega
    have hj : ∀ x (hx : x ∈ crit), f x = τ → (D'.chart x hx).k ≠ j := by
      intro x hx h
      rw [(hch x hx).2.1, ← (D.chart x hx).hkidx]
      have := hidx' x hx h
      omega
    exact slab_hpair_vanishes hsm D' hcrit hε₁ hεr' ht (by linarith) (by linarith) ht' hslab hU
      hk1 j hj
  have hbase : ∀ s : ℝ, c' < s → s ≤ b → (∀ x ∈ crit, f x ≠ s) →
      (∀ x ∈ crit, ¬ (c' < f x ∧ f x < s)) →
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair (f ⁻¹' Icc a s) (f ⁻¹' Icc a c') j) := by
    intro s hs hsb hsreg hnone
    refine hslabZ c' ((c' + s) / 2) s hc' (by linarith) (by linarith) hsb ?_ ?_
    · intro x hx
      rcases lt_or_gt_of_ne (hreg x hx) with h | h
      · exact Or.inl h
      rcases lt_or_gt_of_ne (hsreg x hx) with h' | h'
      · exact absurd ⟨h, h'⟩ (hnone x hx)
      · exact Or.inr (Or.inr h')
    · intro x hx h
      exact hidx x hx (by rw [h]; linarith)
  have claim : ∀ N : ℕ, ∀ s : ℝ, c' < s → s ≤ b → (∀ x ∈ crit, f x ≠ s) →
      ((crit.image f).filter (fun v => c' < v ∧ v < s)).card ≤ N →
      CategoryTheory.Limits.IsZero (Handle.relativeHomologyPair (f ⁻¹' Icc a s) (f ⁻¹' Icc a c') j) := by
    intro N
    induction N with
    | zero =>
      intro s hs hsb hsreg hcard
      have hW := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      refine hbase s hs hsb hsreg fun x hx hmem => ?_
      have : f x ∈ (crit.image f).filter (fun v => c' < v ∧ v < s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f hx, hmem⟩
      rw [hW] at this
      exact Finset.notMem_empty _ this
    | succ N ih =>
      intro s hs hsb hsreg hcard
      set W := (crit.image f).filter (fun v => c' < v ∧ v < s) with hWdef
      by_cases hne : W.Nonempty
      swap
      · refine hbase s hs hsb hsreg fun x hx hmem => hne ⟨f x, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f hx, hmem⟩
      set τ := W.max' hne with hτdef
      have hτW : τ ∈ W := W.max'_mem hne
      obtain ⟨-, hτc', hτs⟩ := Finset.mem_filter.mp hτW
      have hτmax : ∀ x ∈ crit, c' < f x → f x < s → f x ≤ τ := fun x hx h1 h2 =>
        W.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f hx, h1, h2⟩)
      set L := insert c' ((crit.image f).filter (fun v => v < τ)) with hLdef
      have hLne : L.Nonempty := Finset.insert_nonempty _ _
      set m := L.max' hLne with hmdef
      have hm1 : c' ≤ m := L.le_max' c' (Finset.mem_insert_self _ _)
      have hm2 : m < τ := by
        refine (L.max'_lt_iff hLne).mpr fun y hy => ?_
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hτc'
        · exact (Finset.mem_filter.mp hy).2
      have hlow : ∀ x ∈ crit, f x < τ → f x ≤ m := fun x hx h =>
        L.le_max' _ (Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f hx, h⟩))
      set s₀ := (m + τ) / 2 with hs₀def
      have hs₀c' : c' < s₀ := by linarith
      have hs₀τ : s₀ < τ := by linarith
      have hs₀reg : ∀ x ∈ crit, f x ≠ s₀ := by
        intro x hx h
        rcases lt_or_ge (f x) τ with h' | h'
        · have := hlow x hx h'
          linarith
        · linarith
      have hsub : (crit.image f).filter (fun v => c' < v ∧ v < s₀) ⊆ W.erase τ := by
        intro v hv
        obtain ⟨hvim, hv1, hv2⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_erase.mpr ⟨by linarith,
          Finset.mem_filter.mpr ⟨hvim, hv1, by linarith⟩⟩
      have hcard₀ : ((crit.image f).filter (fun v => c' < v ∧ v < s₀)).card ≤ N := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hτW] at h1
        omega
      have hlowZ := ih s₀ hs₀c' (by linarith) hs₀reg hcard₀
      have hslabZ' := hslabZ s₀ τ s (hc'.trans hs₀c'.le) hs₀τ hτs hsb
        (by
          intro x hx
          rcases lt_trichotomy (f x) τ with h | h | h
          · have := hlow x hx h
            exact Or.inl (by linarith)
          · exact Or.inr (Or.inl h)
          · refine Or.inr (Or.inr ?_)
            rcases lt_or_gt_of_ne (hsreg x hx) with h' | h'
            · have := hτmax x hx (by linarith) h'
              linarith
            · exact h')
        (fun x hx h => hidx x hx (by rw [h]; exact hτc'))
      exact glue (preimage_mono (Icc_subset_Icc_right hs₀c'.le))
        (preimage_mono (Icc_subset_Icc_right (hs₀τ.trans hτs).le)) hlowZ hslabZ'
  rcases hc'b.lt_or_eq with hlt | heq
  · exact claim _ b hlt le_rfl (fun x hx => ne_of_lt ((hcrit x).1 hx).1.2) le_rfl
  · subst heq
    exact (isHomotopyEquivInclusion_refl _).relHomologyVanishes j

theorem tripleBoundary_leftDisc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {x : M} (hx : x ∈ crit) {μ : ℕ} (hμ : (D.chart x hx).k = μ + 1) {ε t t' : ℝ} (hε : 0 < ε)
    (hrm : 8 * ε < D.rm x hx ^ 2) (hat : a ≤ t) (ht : t < f x - ε) (hxt' : f x ≤ t')
    (ht'b : t' ≤ b) (hU : ∀ y, f y ∈ Icc t (f x - ε) → ∀ w hw, y ∉ D.smallBall w hw)
    (gD' : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk (μ + 1))))
      (ULift.down ⁻¹' diskSphere (μ + 1)) (μ + 1)) :
    Handle.tripleBoundary (f ⁻¹' {a}) (f ⁻¹' Icc a t) (f ⁻¹' Icc a t') μ
        (Handle.discClass (f ⁻¹' Icc a t') (f ⁻¹' Icc a t) (D.leftDiscMap x (μ + 1) ε t) gD') =
      Handle.sphereClass (f ⁻¹' Icc a t) (f ⁻¹' {a}) (D.leftSphereMap x (μ + 1) ε t)
        (Handle.boundaryGen gD') := by
  classical
  set F := D.leftDiscMap x (μ + 1) ε t with hFdef
  set G := D.leftSphereMap x (μ + 1) ε t with hGdef
  set d := D.chart x hx with hd
  have hRpos : 0 < d.R := d.R_pos
  have hrmpos : 0 < D.rm x hx := D.rm_pos x hx
  have hrmR : D.rm x hx ≤ d.R := (D.hrm x hx).2
  have hR2 : 2 * ε ≤ d.R ^ 2 := by nlinarith
  have hsq : Real.sqrt (2 * ε) ≤ d.R := by
    rw [show d.R = Real.sqrt (d.R ^ 2) from (Real.sqrt_sq hRpos.le).symm]
    exact Real.sqrt_le_sqrt hR2
  have hsqnn : 0 ≤ Real.sqrt (2 * ε) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
  have hnormE : ∀ (k : ℕ) (_ : k = μ + 1) (y : EuclideanSpace ℝ (Fin (μ + 1))),
      ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (Handle.reidx y : Fin k → ℝ)‖ = ‖y‖ := by
    intro k hk y
    subst hk
    congr 1
    ext i
    have hi := i.2
    simp [Handle.reidx, hi]
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), ‖d.toE (Handle.reidx y)‖ = ‖y‖ :=
    fun y => hnormE d.k hμ y
  have hreidx_cont : Continuous (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
      (Handle.reidx y : Fin d.k → ℝ)) := by
    refine continuous_pi fun i => ?_
    by_cases h : (i : ℕ) < μ + 1
    · simp only [Handle.reidx, h, ↓reduceDIte]
      exact (EuclideanSpace.proj (⟨i, h⟩ : Fin (μ + 1))).continuous
    · simp only [Handle.reidx, h, ↓reduceDIte]
      exact continuous_const
  have hu_cont : Continuous (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
      d.toE (Handle.reidx y)) := d.contDiff_toE.continuous.comp hreidx_cont
  have hw0 : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), 1 / 2 ≤ ‖y‖ →
      (Handle.reidx y : Fin d.k → ℝ) ≠ 0 := by
    intro y hy h0
    have h1 := hnorm y
    rw [h0, show d.toE 0 = 0 from map_zero _, norm_zero] at h1
    linarith
  have hdisc_nm : ∀ v : EuclideanSpace ℝ (Fin d.k), ‖v‖ ≤ Real.sqrt (2 * ε) →
      morseNorm n (recombine d.hk v 0) ≤ d.R := by
    intro v hv
    refine MorseNormalChart.morseNorm_le_of_sq_le hRpos.le ?_
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart d.hk, ModelField.negPart_recombine,
      ModelField.posPart_recombine, norm_zero]
    nlinarith [norm_nonneg v]
  have hdisc_f : ∀ v : EuclideanSpace ℝ (Fin d.k), ‖v‖ ≤ Real.sqrt (2 * ε) →
      f (d.χ (recombine d.hk v 0)) = f x - ‖v‖ ^ 2 / 2 := by
    intro v hv
    rw [d.hnorm _ (hdisc_nm v hv), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, ModelField.negPart_recombine,
      ModelField.posPart_recombine, norm_zero]
    ring
  have hsp : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), 1 / 2 ≤ ‖y‖ →
      d.sphereParam ε (Handle.reidx y) ∈ d.χ.source ∧
        f (d.χ (d.sphereParam ε (Handle.reidx y))) = f x - ε := by
    intro y hy
    refine ⟨d.hsrc _ (d.morseNorm_sphereParam_le hε.le hR2 (hw0 y hy)), ?_⟩
    exact d.f_chart_of_mem_leftModelSphere hR2 (d.sphereParam_mem_leftModelSphere hε.le (hw0 y hy))
  have hsp_ab : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), 1 / 2 ≤ ‖y‖ →
      f (d.χ (d.sphereParam ε (Handle.reidx y))) ∈ Icc a b := by
    intro y hy
    have hmem : d.χ (d.sphereParam ε (Handle.reidx y)) ∈ d.χ '' Metric.ball 0 d.R' :=
      ⟨_, d.mem_ball_of_le (d.morseNorm_sphereParam_le hε.le hR2 (hw0 y hy)), rfl⟩
    exact Ioo_subset_Icc_self (D.inStrip x hx hmem)
  have hpt_cont : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), 1 / 2 ≤ ‖y‖ →
      ContinuousAt (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        d.χ (d.sphereParam ε (Handle.reidx y))) y := by
    intro y hy
    have h1 : ContinuousAt d.χ (d.sphereParam ε (Handle.reidx y)) :=
      d.χ.continuousAt (hsp y hy).1
    have h2 : ContinuousAt (d.sphereParam ε) (Handle.reidx y) :=
      (d.contDiffAt_sphereParam ε (hw0 y hy)).continuousAt
    exact h1.comp (f := fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
      d.sphereParam ε (Handle.reidx y)) (h2.comp hreidx_cont.continuousAt)
  have hTt : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), 1 / 2 ≤ ‖y‖ →
      f (D.flow (f x - ε - t) (d.χ (d.sphereParam ε (Handle.reidx y)))) = t := by
    intro y hy
    have hf0 := (hsp y hy).2
    have hl := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hf
      (x := d.χ (d.sphereParam ε (Handle.reidx y))) (T := f x - ε - t) (hsp_ab y hy)
      (by rw [hf0]; exact ⟨by linarith, by linarith [(hsp_ab y hy).2]⟩)
      (by
        intro z hz w hw
        refine hU z ?_ w hw
        rw [hf0, show f x - ε - (f x - ε - t) = t by ring, uIcc_of_ge (by linarith)] at hz
        exact hz)
      (f x - ε - t) right_mem_uIcc
    rw [hl, hf0]
    ring
  have hFeq : ∀ y, F y = if ‖y‖ ≤ 1 / 2 then
      d.χ (recombine d.hk ((2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)) 0)
      else D.flow ((2 * ‖y‖ - 1) * (f x - ε - t)) (d.χ (d.sphereParam ε (Handle.reidx y))) := by
    intro y
    simp only [hFdef, GradientLikeStrip.leftDiscMap, hx, ↓reduceDIte, hd]
    rfl
  have hGeq : ∀ y, G y = D.flow (f x - ε - t) (d.χ (d.sphereParam ε (Handle.reidx y))) := by
    intro y
    simp only [hGdef, GradientLikeStrip.leftSphereMap, hx, ↓reduceDIte, hd]
    rfl
  have hsmall : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), ‖y‖ ≤ 1 / 2 →
      ‖(2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)‖ ≤ Real.sqrt (2 * ε) := by
    intro y hy
    rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg y]
  have hFc : ContinuousOn F (Metric.closedBall 0 1) := by
    rw [show F = _ from funext hFeq]
    refine ContinuousOn.if ?_ ?_ ?_
    · intro y hy
      have hy2 : ‖y‖ = 1 / 2 := frontier_le_subset_eq continuous_norm continuous_const hy.2
      rw [hy2, show (2 * (1 / 2 : ℝ) - 1) * (f x - ε - t) = 0 by ring, D.flow_zero,
        MorseNormalChart.sphereParam, hnorm, hy2]
      congr 3
      ring
    · intro y hy
      have hy2 : ‖y‖ ≤ 1 / 2 := by
        have := hy.2
        rwa [(isClosed_le continuous_norm continuous_const).closure_eq] at this
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt d.χ
          (recombine d.hk ((2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)) 0) :=
        d.χ.continuousAt (d.hsrc _ (hdisc_nm _ (hsmall y hy2)))
      have h2 : Continuous (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
          recombine d.hk ((2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)) 0) := by
        have := (ModelField.recombineL d.hk).continuous.comp
          ((hu_cont.const_smul (2 * Real.sqrt (2 * ε))).prodMk
            (continuous_const (y := (0 : EuclideanSpace ℝ (Fin (n - d.k))))))
        simpa only [Function.comp_def, ModelField.recombineL_apply, Pi.smul_apply] using this
      exact h1.comp (f := fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        recombine d.hk ((2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)) 0) h2.continuousAt
    · intro y hy
      have hy2 : 1 / 2 ≤ ‖y‖ := by
        have hsub : closure {a : EuclideanSpace ℝ (Fin (μ + 1)) | ¬‖a‖ ≤ 1 / 2} ⊆
            {a | 1 / 2 ≤ ‖a‖} := by
          simp only [not_le]
          exact closure_lt_subset_le continuous_const continuous_norm
        exact hsub hy.2
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
          ((2 * ‖y‖ - 1) * (f x - ε - t), d.χ (d.sphereParam ε (Handle.reidx y)))) y :=
        ContinuousAt.prodMk (by fun_prop) (hpt_cont y hy2)
      exact D.continuous_flow_joint.continuousAt.comp h1
  have hFB : MapsTo F (Metric.closedBall 0 1) (f ⁻¹' Icc a t') := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
    rw [mem_preimage, hFeq]
    split_ifs with h
    · rw [hdisc_f _ (hsmall y h)]
      have := hsmall y h
      have h0 : 0 ≤ ‖(2 * Real.sqrt (2 * ε)) • d.toE (Handle.reidx y)‖ := norm_nonneg _
      constructor <;> nlinarith
    · have hs0 : 0 ≤ (2 * ‖y‖ - 1) * (f x - ε - t) :=
        mul_nonneg (by linarith [not_le.1 h]) (by linarith)
      have hsT : (2 * ‖y‖ - 1) * (f x - ε - t) ≤ f x - ε - t := by
        nlinarith
      have hy' : 1 / 2 ≤ ‖y‖ := (not_le.1 h).le
      have h1 := GradientLikeStrip.f_flow_le (D := D) hf
        (d.χ (d.sphereParam ε (Handle.reidx y))) hs0
      have h2 := GradientLikeStrip.sub_le_f_flow (D := D) hf
        (d.χ (d.sphereParam ε (Handle.reidx y))) hs0
      rw [(hsp y hy').2] at h1 h2
      constructor <;> linarith
  have hFA : MapsTo F (Metric.sphere 0 1) (f ⁻¹' Icc a t) := by
    intro y hy
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.1 hy
    have hn : ¬‖y‖ ≤ 1 / 2 := by rw [hy1]; norm_num
    rw [mem_preimage, hFeq]
    simp only [hn, ↓reduceIte]
    rw [hy1,
      show (2 * (1 : ℝ) - 1) * (f x - ε - t) = f x - ε - t by ring, hTt y (by rw [hy1]; norm_num)]
    exact ⟨hat, le_rfl⟩
  have hGc : ContinuousOn G (SingularPair.unitSphere μ) := by
    rw [show G = _ from funext hGeq]
    intro y hy
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.1 hy
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        (f x - ε - t, d.χ (d.sphereParam ε (Handle.reidx y)))) y :=
      ContinuousAt.prodMk continuousAt_const (hpt_cont y (by rw [hy1]; norm_num))
    exact D.continuous_flow_joint.continuousAt.comp h1
  have hGA : MapsTo G (SingularPair.unitSphere μ) (f ⁻¹' Icc a t) := by
    intro y hy
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.1 hy
    rw [mem_preimage, hGeq, hTt y (by rw [hy1]; norm_num)]
    exact ⟨hat, le_rfl⟩
  have hFG : ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (μ + 1))) 1, F y = G y := by
    intro y hy
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.1 hy
    have hn : ¬‖y‖ ≤ 1 / 2 := by rw [hy1]; norm_num
    rw [hFeq, hGeq]
    simp only [hn, ↓reduceIte]
    rw [hy1,
      show (2 * (1 : ℝ) - 1) * (f x - ε - t) = f x - ε - t by ring]
  unfold Handle.discClass Handle.sphereClass
  rw [dite_eq_left_of_eq_true (eq_true ⟨hFc, hFB, hFA⟩), dite_eq_left_of_eq_true (eq_true ⟨hGc, hGA⟩)]
  unfold Handle.tripleBoundary Handle.boundaryGen
  refine (CategoryTheory.ConcreteCategory.comp_apply _ _ gD').symm.trans
    ((CategoryTheory.ConcreteCategory.congr_hom ?_ gD').trans
      (CategoryTheory.ConcreteCategory.comp_apply _ _ gD'))
  simp only [CategoryTheory.Category.assoc]
  erw [← CategoryTheory.Category.assoc, ← SingularPair.δ_natural]
  erw [CategoryTheory.Category.assoc, ← SingularPair.singularHomologyMap_comp_assoc, ← SingularPair.singularHomologyMap_comp_assoc]
  congr 3
  ext z
  exact hFG _ z.2

theorem sign_det_sphereSard (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c)
    (hc₂ : c < f q - ε)
    (R : EuclideanSpace ℝ (Fin (ℓ + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))
    (hR : 0 < LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1)))) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {y : EuclideanSpace ℝ (Fin ℓ)} (hy : ‖y‖ < 1)
    (hdom : Handle.reidx (R (Handle.bigDisc ℓ ρ y)) ∈ D.sardDom p hq ε c ε hp)
    (hzero : D.sardMap p hq ε c ε hp (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) = 0) :
    ((SignType.sign (LinearMap.det (fderiv ℝ (D.tubeCoordE p hp ε ℓ ∘
        D.leftSphereMap q (ℓ + 1) ε c ∘ R ∘ Handle.bigDisc ℓ ρ) y :
          EuclideanSpace ℝ (Fin ℓ) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ))) : SignType) : ℤ) =
      D.sardSign p hq ε c hp (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) := by
  obtain ⟨B, hB, hBorth, hBdet⟩ : ∃ B : EuclideanSpace ℝ (Fin ℓ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
      HasFDerivAt (Handle.bigDisc ℓ ρ) B y ∧
      (∀ h, inner ℝ (Handle.bigDisc ℓ ρ y) (B h) = 0) ∧
      0 < (Matrix.of fun i j : Fin (ℓ + 1) => if (j : ℕ) = 0 then Handle.bigDisc ℓ ρ y i else
        if hj : (j : ℕ) - 1 < ℓ then B (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i else 0).det := by
    clear * - hρ hρ1 hy
    have instCS1 : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin ℓ)) := IsBoundedSMul.continuousSMul
    have instCS2 : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (ℓ + 1))) := IsBoundedSMul.continuousSMul
    set κ := ρ * Real.pi with ha
    have ha0 : 0 < κ := mul_pos hρ Real.pi_pos
    set e0 : EuclideanSpace ℝ (Fin (ℓ + 1)) := EuclideanSpace.single 0 1 with he0
    obtain ⟨ι, hι⟩ : ∃ ι : EuclideanSpace ℝ (Fin ℓ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
        ∀ v i, ι v i = if h : (i : ℕ) = 0 then 0 else v ⟨(i : ℕ) - 1, by have := i.2; omega⟩ := by
      refine ⟨LinearMap.toContinuousLinearMap
        { toFun := fun v => WithLp.toLp 2 fun i =>
            if h : (i : ℕ) = 0 then 0 else v ⟨(i : ℕ) - 1, by have := i.2; omega⟩
          map_add' := ?_
          map_smul' := ?_ }, ?_⟩
      · intro v w; ext i; by_cases h : i = 0 <;> simp [h]
      · intro c v; ext i; by_cases h : i = 0 <;> simp [h]
      · intro v i; rfl
    have hι0 : ∀ v, ι v 0 = 0 := fun v => by rw [hι]; simp
    have hιs : ∀ v (k : Fin ℓ), ι v k.succ = v k := fun v k => by rw [hι]; simp
    have hinnι : ∀ v w, (inner ℝ (ι v) (ι w)) = (inner ℝ (v) (w)) := by
      intro v w
      rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
      simp [hι0, hιs]
    have hinn0ι : ∀ v, (inner ℝ (e0) (ι v)) = 0 := by
      intro v
      rw [PiLp.inner_apply, Fin.sum_univ_succ]
      simp [he0, hι0, hιs]
    have hnorm0 : ‖e0‖ = 1 := by simp [he0]
    have hB1 : ∀ z, Handle.bigDisc ℓ ρ z = Real.cos (κ * ‖z‖) • e0 + (Real.sin (κ * ‖z‖) * ‖z‖⁻¹) • ι z := by
      intro z; ext i
      rw [Handle.bigDisc, PiLp.toLp_apply]
      by_cases h : (i : ℕ) = 0
      · have hi : i = 0 := Fin.ext h
        subst hi; simp [he0, hι0, ha]
      · have hi : i ≠ 0 := fun h' => h (by rw [h']; rfl)
        simp [h, he0, hi, hι, ha]
        ring
    set r := ‖y‖ with hr
    set e : EuclideanSpace ℝ (Fin ℓ) := r⁻¹ • y with he
    obtain ⟨P, hP⟩ : ∃ P : ℝ → (EuclideanSpace ℝ (Fin ℓ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))),
        ∀ u h, P u h = (-(κ * Real.sin (κ * u)) * (inner ℝ (e) (h))) • e0 +
          ((κ * Real.cos (κ * u) - κ * Real.sinc (κ * u)) * (inner ℝ (e) (h))) • ι e +
          (κ * Real.sinc (κ * u)) • ι h := by
      refine ⟨fun u => ((-(κ * Real.sin (κ * u))) • innerSL ℝ e).smulRight e0 +
        ((κ * Real.cos (κ * u) - κ * Real.sinc (κ * u)) • innerSL ℝ e).smulRight (ι e) +
        (κ * Real.sinc (κ * u)) • ι, fun u h => ?_⟩
      simp [smul_eq_mul]
    have hF1a : y ≠ 0 → HasFDerivAt (Handle.bigDisc ℓ ρ) (P r) y := by
      intro hy0
      have hr0 : r ≠ 0 := by rw [hr]; exact norm_ne_zero_iff.2 hy0
      have hn : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin ℓ) => ‖z‖) (r⁻¹ • innerSL ℝ y) y := by
        have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
        have h2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr0
        have h3 := h1.sqrt h2
        have h4 : (fun z : EuclideanSpace ℝ (Fin ℓ) => √(‖z‖ ^ 2)) = fun z => ‖z‖ := by
          funext z; rw [Real.sqrt_sq (norm_nonneg _)]
        rw [h4] at h3
        convert h3 using 1
        ext h
        simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
          Nat.cast_ofNat]
        rw [Real.sqrt_sq (norm_nonneg _)]
        field_simp
        rw [hr]; ring
      have hc := ((hn.const_mul κ).cos).smul_const e0
      have hs := (hn.const_mul κ).sin
      have hi := (hasDerivAt_inv hr0).comp_hasFDerivAt y hn
      have hφ := hs.mul hi
      have hd := hc.add (hφ.smul ι.hasFDerivAt)
      have hfun : Handle.bigDisc ℓ ρ = (fun z => Real.cos (κ * ‖z‖) • e0) +
          ((fun z : EuclideanSpace ℝ (Fin ℓ) => Real.sin (κ * ‖z‖)) *
            ((fun t : ℝ => t⁻¹) ∘ fun z : EuclideanSpace ℝ (Fin ℓ) => ‖z‖)) • ⇑ι := by
        funext z; rw [hB1 z]; rfl
      rw [← hfun] at hd
      refine hd.congr_fderiv ?_
      ext1 h
      rw [hP]
      have hsinc : Real.sinc (κ * r) = Real.sin (κ * r) / (κ * r) :=
        Real.sinc_of_ne_zero (mul_ne_zero ha0.ne' hr0)
      have hιe : ι e = r⁻¹ • ι y := by rw [he, map_smul]
      have hie : (inner ℝ (e) (h)) = r⁻¹ * (inner ℝ (y) (h)) := by rw [he, real_inner_smul_left]
      rw [hsinc, hιe, hie]
      ext i
      simp only [add_apply, ContinuousLinearMap.smulRight_apply,
        smul_apply, innerSL_apply_apply, smul_eq_mul, PiLp.add_apply,
        PiLp.smul_apply, Pi.mul_apply, Function.comp_apply, ← hr]
      field_simp
      ring
    have hnormι : ∀ v, ‖ι v‖ = ‖v‖ := by
      intro v
      rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinnι]
    have hP0 : P 0 = κ • ι := by
      ext1 h
      rw [hP]
      simp
    have hF1b : HasFDerivAt (Handle.bigDisc ℓ ρ) (κ • ι) 0 := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      have hb0 : Handle.bigDisc ℓ ρ 0 = e0 := by rw [hB1]; simp
      refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : EuclideanSpace ℝ (Fin ℓ) => ‖h‖ ^ 2)
        ?_ (Asymptotics.isLittleO_norm_pow_id (by norm_num))
      refine Asymptotics.IsBigO.of_bound (κ ^ 2 / 2 + κ ^ 3 / 6) ?_
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin ℓ)) one_pos] with h hh
      rw [mem_ball_zero_iff] at hh
      set x := ‖h‖ with hx
      have hx0 : 0 ≤ x := norm_nonneg _
      have hax : 0 ≤ κ * x := mul_nonneg ha0.le hx0
      rw [zero_add, hb0, hB1, ← hx]
      have heq : Real.cos (κ * x) • e0 + (Real.sin (κ * x) * x⁻¹) • ι h - e0 - (κ • ι) h =
          (Real.cos (κ * x) - 1) • e0 + (Real.sin (κ * x) - κ * x) • (x⁻¹ • ι h) := by
        rcases eq_or_ne x 0 with h0 | h0
        · have : h = 0 := by rw [hx] at h0; exact norm_eq_zero.1 h0
          subst this
          simp [sub_smul]
        · rw [smul_apply, smul_smul, sub_mul, mul_assoc κ x, mul_inv_cancel₀ h0]
          module
      rw [heq]
      have hc1 : |Real.cos (κ * x) - 1| ≤ (κ * x) ^ 2 / 2 := by
        rw [abs_of_nonpos (by linarith [Real.cos_le_one (κ * x)])]
        linarith [Real.one_sub_sq_div_two_le_cos (x := κ * x)]
      have hs1 : |Real.sin (κ * x) - κ * x| ≤ (κ * x) ^ 3 / 6 := by
        rw [abs_of_nonpos (by linarith [Real.sin_le hax])]
        rcases eq_or_lt_of_le hax with h0 | h0
        · rw [← h0]; simp
        · linarith [Real.sin_gt_sub_cube h0]
      have hιx : ‖x⁻¹ • ι h‖ ≤ 1 := by
        rw [norm_smul, hnormι, ← hx, norm_inv, Real.norm_eq_abs, abs_of_nonneg hx0]
        rcases eq_or_ne x 0 with h0 | h0
        · rw [h0]; simp
        · rw [inv_mul_cancel₀ h0]
      calc ‖(Real.cos (κ * x) - 1) • e0 + (Real.sin (κ * x) - κ * x) • (x⁻¹ • ι h)‖
          ≤ ‖(Real.cos (κ * x) - 1) • e0‖ + ‖(Real.sin (κ * x) - κ * x) • (x⁻¹ • ι h)‖ :=
            norm_add_le _ _
        _ ≤ (κ * x) ^ 2 / 2 + (κ * x) ^ 3 / 6 := by
            rw [norm_smul, norm_smul, hnorm0, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
            gcongr
            calc |Real.sin (κ * x) - κ * x| * ‖x⁻¹ • ι h‖ ≤ |Real.sin (κ * x) - κ * x| * 1 := by
                  gcongr
              _ ≤ _ := by rw [mul_one]; exact hs1
        _ ≤ (κ ^ 2 / 2 + κ ^ 3 / 6) * ‖‖h‖ ^ 2‖ := by
            rw [norm_pow, norm_norm, ← hx]
            have hx1 : x ≤ 1 := hh.le
            have : κ ^ 3 * x ^ 3 ≤ κ ^ 3 * x ^ 2 := by
              exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (by norm_num)) (by positivity)
            have e1 : (κ * x) ^ 2 / 2 + (κ * x) ^ 3 / 6 = κ ^ 2 * x ^ 2 / 2 + κ ^ 3 * x ^ 3 / 6 := by ring
            have e2 : (κ ^ 2 / 2 + κ ^ 3 / 6) * x ^ 2 = κ ^ 2 * x ^ 2 / 2 + κ ^ 3 * x ^ 2 / 6 := by ring
            rw [e1, e2]
            linarith
    have hF1 : HasFDerivAt (Handle.bigDisc ℓ ρ) (P r) y := by
      rcases eq_or_ne y 0 with hy0 | hy0
      · have hr0 : r = 0 := by rw [hr, hy0, norm_zero]
        rw [hr0, hP0, hy0]; exact hF1b
      · exact hF1a hy0
    set bv : ℝ → EuclideanSpace ℝ (Fin (ℓ + 1)) := fun u => Real.cos (κ * u) • e0 + Real.sin (κ * u) • ι e
      with hbv
    have hF2 : Handle.bigDisc ℓ ρ y = bv r := by
      rw [hB1, hbv, he, map_smul]
      simp only [smul_smul, ← hr]
    have he1 : (inner ℝ (e) (e)) = 1 ∨ e = 0 := by
      rcases eq_or_ne y 0 with hy0 | hy0
      · right; rw [he, hy0, smul_zero]
      · left
        have hr0 : r ≠ 0 := by rw [hr]; exact norm_ne_zero_iff.2 hy0
        rw [he, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hr]
        field_simp
    have hinn00 : (inner ℝ (e0) (e0)) = 1 := by rw [real_inner_self_eq_norm_sq, hnorm0]; norm_num
    have hinnι0 : ∀ v, (inner ℝ (ι v) (e0)) = 0 := fun v => by rw [real_inner_comm]; exact hinn0ι v
    have hF4 : ∀ u h, (inner ℝ (bv u) (P u h)) = 0 := by
      intro u h
      rw [hbv, hP]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hinn00, hinn0ι, hinnι0, hinnι]
      rcases he1 with h1 | h1
      · rw [h1]; ring
      · rw [h1]; simp
    set Mt : ℝ → Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ := fun u => Matrix.of fun i j =>
      if (j : ℕ) = 0 then bv u i else if hj : (j : ℕ) - 1 < ℓ then
        P u (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i else 0 with hMt
    have hMs : ∀ u i (k : Fin ℓ), Mt u i k.succ = P u (EuclideanSpace.single k 1) i := by
      intro u i k
      simp [hMt]
    have hM0 : ∀ u i, Mt u i 0 = bv u i := by
      intro u i
      simp [hMt]
    have hdet0 : (Mt 0).det = κ ^ ℓ := by
      have hdiag : Mt 0 = Matrix.diagonal (fun i : Fin (ℓ + 1) => if i = 0 then 1 else κ) := by
        ext i j
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
        · rw [hM0]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
          · simp [hbv, he0]
          · simp [hbv, he0]
        · rw [hMs, hP0]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
          · rw [Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero k).symm]; simp [hι0]
          · simp [hιs, Matrix.diagonal_apply]
      rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ]
      simp
    have hexp : ∀ {m : ℕ} (x : EuclideanSpace ℝ (Fin m)),
        ∑ k, x k • EuclideanSpace.single k (1 : ℝ) = x := by
      intro m x
      simpa using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x
    have hmul : ∀ u (v : Fin (ℓ + 1) → ℝ), (Mt u).mulVec v =
        fun i => (v 0 • bv u + P u (WithLp.toLp 2 fun k => v k.succ)) i := by
      intro u v
      funext i
      simp only [Matrix.mulVec, dotProduct]
      rw [Fin.sum_univ_succ, hM0]
      simp_rw [hMs]
      conv_rhs => rw [← hexp (WithLp.toLp 2 fun k => v k.succ)]
      simp [map_sum, map_smul, mul_comm]
    have hnz : (inner ℝ (e) (e)) = 1 → ∀ u, 0 ≤ u → κ * u < Real.pi → (Mt u).det ≠ 0 := by
      intro hee u hu hau hdet
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      rw [hmul] at hv
      set h : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 fun k => v k.succ with hh
      have hvec : v 0 • bv u + P u h = 0 := by
        ext i; exact congrFun hv i
      have hbb : (inner ℝ (bv u) (bv u)) = 1 := by
        rw [hbv]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          hinn00, hinn0ι, hinnι0, hinnι, hee]
        linear_combination Real.sin_sq_add_cos_sq (κ * u)
      have hv00 : v 0 = 0 := by
        have := congrArg (fun z => (inner ℝ (bv u) (z))) hvec
        simp only [inner_add_right, real_inner_smul_right, hbb, hF4, inner_zero_right] at this
        linarith
      rw [hv00, zero_smul, zero_add] at hvec
      have h1 : κ * Real.sin (κ * u) * (inner ℝ (e) (h)) = 0 := by
        have := congrArg (fun z => (inner ℝ (e0) (z))) hvec
        simp only [hP, inner_add_right, real_inner_smul_right, hinn00, hinn0ι, inner_zero_right] at this
        linarith
      have h2 : κ * Real.cos (κ * u) * (inner ℝ (e) (h)) = 0 := by
        have := congrArg (fun z => (inner ℝ (ι e) (z))) hvec
        simp only [hP, inner_add_right, real_inner_smul_right, hinnι0, hinnι, hee,
          inner_zero_right] at this
        linarith
      have heh : (inner ℝ (e) (h)) = 0 := by
        have h3 : Real.sin (κ * u) * (inner ℝ (e) (h)) = 0 := by
          rcases mul_eq_zero.1 (show κ * (Real.sin (κ * u) * (inner ℝ (e) (h))) = 0 by linarith) with h' | h'
          · exact absurd h' ha0.ne'
          · exact h'
        have h4 : Real.cos (κ * u) * (inner ℝ (e) (h)) = 0 := by
          rcases mul_eq_zero.1 (show κ * (Real.cos (κ * u) * (inner ℝ (e) (h))) = 0 by linarith) with h' | h'
          · exact absurd h' ha0.ne'
          · exact h'
        have h5 : (inner ℝ (e) (h)) ^ 2 = (Real.sin (κ * u) * (inner ℝ (e) (h))) ^ 2 + (Real.cos (κ * u) * (inner ℝ (e) (h))) ^ 2 := by
          linear_combination (-((inner ℝ (e) (h)) ^ 2)) * Real.sin_sq_add_cos_sq (κ * u)
        rw [h3, h4] at h5
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
      have hsinc : 0 < Real.sinc (κ * u) := by
        rcases eq_or_lt_of_le (mul_nonneg ha0.le hu) with h0 | h0
        · rw [← h0, Real.sinc_zero]; norm_num
        · rw [Real.sinc_of_ne_zero h0.ne']
          exact div_pos (Real.sin_pos_of_pos_of_lt_pi h0 hau) h0
      rw [hP, heh] at hvec
      simp only [mul_zero, zero_smul, zero_add] at hvec
      have hιh : ι h = 0 := by
        rcases smul_eq_zero.1 hvec with h' | h'
        · exact absurd h' (mul_pos ha0 hsinc).ne'
        · exact h'
      have hh0 : h = 0 := by
        rw [← norm_eq_zero, ← hnormι, hιh, norm_zero]
      apply hv0
      funext i
      refine Fin.cases hv00 (fun k => ?_) i
      have := congrArg (fun z : EuclideanSpace ℝ (Fin ℓ) => z k) hh0
      simpa [hh] using this
    have hcont : Continuous fun u => (Mt u).det := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      refine Fin.cases ?_ (fun k => ?_) j
      · have : (fun u => Mt u i 0) = fun u => Real.cos (κ * u) * e0 i + Real.sin (κ * u) * ι e i := by
          funext u; rw [hM0]; simp [hbv]
        rw [this]; fun_prop
      · have : (fun u => Mt u i k.succ) = fun u =>
            (-(κ * Real.sin (κ * u)) * (inner ℝ (e) (EuclideanSpace.single k 1))) * e0 i +
            ((κ * Real.cos (κ * u) - κ * Real.sinc (κ * u)) * (inner ℝ (e) (EuclideanSpace.single k 1))) * ι e i +
            (κ * Real.sinc (κ * u)) * ι (EuclideanSpace.single k 1) i := by
          funext u; rw [hMs, hP]; simp
        rw [this]
        have := Real.continuous_sinc
        fun_prop
    have hF3 : 0 < (Mt r).det := by
      rcases eq_or_ne y 0 with hy0 | hy0
      · have hr0 : r = 0 := by rw [hr, hy0, norm_zero]
        rw [hr0, hdet0]; positivity
      · have hee : (inner ℝ (e) (e)) = 1 := by
          rcases he1 with h1 | h1
          · exact h1
          · exfalso; apply hy0
            have hr0 : r ≠ 0 := by rw [hr]; exact norm_ne_zero_iff.2 hy0
            rw [he] at h1
            rcases smul_eq_zero.1 h1 with h' | h'
            · exact absurd h' (inv_ne_zero hr0)
            · exact h'
        have hr0 : 0 ≤ r := norm_nonneg _
        by_contra hneg
        replace hneg := not_lt.1 hneg
        have hsub := intermediate_value_Icc' hr0 hcont.continuousOn
        rw [hdet0] at hsub
        obtain ⟨u, hu, hu0⟩ := hsub ⟨hneg, by positivity⟩
        refine hnz hee u hu.1 ?_ hu0
        have : ρ * u < 1 := by
          calc ρ * u ≤ ρ * r := by gcongr; exact hu.2
            _ < 1 * 1 := by gcongr
            _ = 1 := one_mul 1
        rw [ha]
        calc ρ * Real.pi * u = (ρ * u) * Real.pi := by ring
          _ < 1 * Real.pi := by gcongr
          _ = Real.pi := one_mul _
    refine ⟨P r, hF1, fun h => ?_, ?_⟩
    · rw [hF2]; exact hF4 r h
    · have hMr : (Matrix.of fun i j : Fin (ℓ + 1) => if (j : ℕ) = 0 then Handle.bigDisc ℓ ρ y i else
          if hj : (j : ℕ) - 1 < ℓ then P r (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i else 0) = Mt r := by
        rw [hF2]
      rw [hMr]; exact hF3
  obtain ⟨hε, -, -, -, hrmq, hpq, hlev⟩ := hv
  have instCSp : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (D.chart p hp).k)) :=
    IsBoundedSMul.continuousSMul
  have instCSl : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin ℓ)) := IsBoundedSMul.continuousSMul
  have instCSl1 : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (ℓ + 1))) :=
    IsBoundedSMul.continuousSMul
  have hεR : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos q hq).le (D.hrm q hq).2 2
    linarith
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hk := (D.chart p hp).hk
  have hfl : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      f (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) = c := by
    intro w hw
    have hfx₁ : f ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) = f q - ε :=
      (D.chart q hq).f_chart_of_mem_leftModelSphere hεR
        ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw)
    have := GradientLikeStrip.f_flow_eq_sub_of_levels hf (D := D)
      (x := (D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) (T := f q - ε - c)
      (by rw [hfx₁]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfx₁, sub_sub_cancel]; exact ⟨by linarith, by linarith⟩) (by
        intro z hz
        rw [hfx₁, sub_sub_cancel, uIcc_of_ge hc₂.le] at hz
        exact hlev z ⟨by linarith [hz.1], hz.2⟩) _ right_mem_uIcc
    rw [this, hfx₁]; ring
  obtain ⟨EL, hEL⟩ : ∃ EL : EuclideanSpace ℝ (Fin (D.chart p hp).k) →L[ℝ] EuclideanSpace ℝ (Fin ℓ),
      ∀ u i, EL u i = if h : (i : ℕ) < (D.chart p hp).k then u ⟨i, h⟩ else 0 := by
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun u => WithLp.toLp 2 fun i =>
          if h : (i : ℕ) < (D.chart p hp).k then u ⟨i, h⟩ else 0
        map_add' := ?_
        map_smul' := ?_ }, fun u i => rfl⟩
    · intro u v; ext i; by_cases h : (i : ℕ) < (D.chart p hp).k <;> simp [h]
    · intro t u; ext i; by_cases h : (i : ℕ) < (D.chart p hp).k <;> simp [h]
  obtain ⟨rL, hrL⟩ : ∃ rL : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] (Fin (D.chart q hq).k → ℝ),
      ∀ z, rL z = Handle.reidx z := by
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun z => Handle.reidx z
        map_add' := ?_
        map_smul' := ?_ }, fun z => rfl⟩
    · intro u v; funext i; by_cases h : (i : ℕ) < ℓ + 1 <;> simp [Handle.reidx, h]
    · intro t u; funext i; by_cases h : (i : ℕ) < ℓ + 1 <;> simp [Handle.reidx, h]
  have hreidx0 : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)),
      (Handle.reidx z : Fin (D.chart q hq).k → ℝ) = 0 → z = 0 := by
    intro z hz
    ext j
    have h1 := congrFun hz ⟨j, by rw [hkq]; exact j.2⟩
    simp only [Handle.reidx, Pi.zero_apply] at h1
    rw [dite_eq_left (Nat.lt_succ_iff.2 (Nat.lt_succ_iff.1 j.2))] at h1
    exact h1
  have htube : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)),
      (Handle.reidx z : Fin (D.chart q hq).k → ℝ) ≠ 0 →
      D.tubeCoordE p hp ε ℓ (D.leftSphereMap q (ℓ + 1) ε c z) =
        EL (DifferentialGeometry.Topology.Morse.CellAttachment.negPart hk
          ((D.chart p hp).χ.symm (D.landing p hq ε c ε (Handle.reidx z)))) := by
    intro z hz
    have hZ : D.leftSphereMap q (ℓ + 1) ε c z = D.flow (f q - ε - c)
        ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx z))) := by
      simp only [GradientLikeStrip.leftSphereMap, dite_eq_left hq]
    have hfZ : f (D.leftSphereMap q (ℓ + 1) ε c z) = c := by rw [hZ]; exact hfl _ hz
    have htc : D.tubeCoord p hp ε (D.leftSphereMap q (ℓ + 1) ε c z) =
        DifferentialGeometry.Topology.Morse.CellAttachment.negPart hk
          ((D.chart p hp).χ.symm (D.landing p hq ε c ε (Handle.reidx z))) := by
      rw [GradientLikeStrip.tubeCoord, ite_eq_left (by rw [hfZ]; linarith), GradientLikeStrip.rightCoord,
        hfZ, hZ]
      rfl
    ext i
    rw [hEL, GradientLikeStrip.tubeCoordE, PiLp.toLp_apply, htc]
  set w₀ : Fin (D.chart q hq).k → ℝ := Handle.reidx (R (Handle.bigDisc ℓ ρ y)) with hw₀
  obtain ⟨hw0, hland⟩ := hdom
  have hw0' : w₀ ≠ 0 := hw0
  have hland' : D.landing p hq ε c ε w₀ ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
    (D.chart p hp).image_lt_subset_image_ball (D.chart p hp).hRR'.le hland
  set X : (Fin (D.chart q hq).k → ℝ) → (Fin n → ℝ) :=
    fun w => (D.chart p hp).χ.symm (D.landing p hq ε c ε w) with hX
  have hXd : DifferentiableAt ℝ X w₀ := by
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((D.chart q hq).sphereParam ε) w₀ :=
      contMDiffAt_iff_contDiffAt.2 ((D.chart q hq).contDiffAt_sphereParam ε hw0')
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart q hq).χ
        ((D.chart q hq).sphereParam ε w₀) :=
      (D.chart q hq).contMDiffAt_chart
        ((D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hεR hw0'))
    have c1 := hχq.comp w₀ hsp
    have c2 := ((D.contMDiff_flow (f q - ε - c)).contMDiffAt).comp w₀ c1
    have c3 := ((D.contMDiff_flow (c - (f p + ε))).contMDiffAt).comp w₀ c2
    have c4 := ((D.chart p hp).contMDiffAt_symm hland').comp w₀ c3
    exact (contMDiffAt_iff_contDiffAt.1 c4).differentiableAt (by simp)
  have hv0 : DifferentialGeometry.Topology.Morse.CellAttachment.posPart hk (X w₀) ≠ 0 := by
    apply ModelField.posPart_ne_zero_of_lt_nf hk (c := f p)
    have hland2 : D.landing p hq ε c ε w₀ ∈
        (D.chart p hp).χ '' {y | DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm n y ≤
          (D.chart p hp).R} :=
      image_mono (fun y (hy : DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm n y <
        (D.chart p hp).R) => le_of_lt hy) hland
    rw [← (D.chart p hp).f_eq_nf_symm hland2,
      GradientLikeStrip.f_landing hp hf hε hε hεR hc₁.le hc₂.le hlev hw0']
    linarith
  have hn0 : DifferentialGeometry.Topology.Morse.CellAttachment.negPart hk (X w₀) = 0 :=
    (ModelField.scaledNegativePart_eq_zero_iff hk hv0).1 hzero
  have hS : HasFDerivAt (D.sardMap p hq ε c ε hp)
      (‖DifferentialGeometry.Topology.Morse.CellAttachment.posPart hk (X w₀)‖ •
        ((ModelField.negPartL hk).comp (fderiv ℝ X w₀))) w₀ := by
    have h1 := (ModelField.hasFDerivAt_scaledNegativePart hk hv0).comp w₀ hXd.hasFDerivAt
    refine h1.congr_fderiv ?_
    ext1 v
    simp [ModelField.scaledNegativePartDeriv_apply, hn0]
  have hSray : fderiv ℝ (D.sardMap p hq ε c ε hp) w₀ w₀ = 0 := by
    have h1 : HasDerivAt (fun t : ℝ => D.sardMap p hq ε c ε hp (t • w₀))
        (fderiv ℝ (D.sardMap p hq ε c ε hp) w₀ w₀) 1 := by
      have h2 : HasDerivAt (fun t : ℝ => t • w₀) w₀ 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).smul_const w₀
      have h3 : HasFDerivAt (D.sardMap p hq ε c ε hp) (fderiv ℝ (D.sardMap p hq ε c ε hp) w₀)
          ((1 : ℝ) • w₀) := by
        rw [one_smul]; exact hS.differentiableAt.hasFDerivAt
      exact h3.comp_hasDerivAt (1 : ℝ) h2
    have h4 : HasDerivAt (fun t : ℝ => D.sardMap p hq ε c ε hp (t • w₀)) 0 1 := by
      refine (hasDerivAt_const (1 : ℝ) (D.sardMap p hq ε c ε hp w₀)).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      change ModelField.scaledNegativePart hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε (t • w₀))) =
        ModelField.scaledNegativePart hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w₀))
      rw [D.landing_smul p hq ε c ε ht hw0']
    exact h1.unique h4
  have hBnorm : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin ℓ)) 1,
      R (Handle.bigDisc ℓ ρ z) ≠ 0 := by
    intro z hz h0
    have h1 := (Handle.bigDisc_spec ℓ hρ hρ1).1 (Metric.ball_subset_closedBall hz)
    rw [SingularPair.unitSphere, mem_sphere_zero_iff_norm, ← R.norm_map, h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨RL, hRL⟩ : ∃ RL : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
      ∀ z, RL z = R z :=
    ⟨(R.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1))), fun z => rfl⟩
  set G' := EL.comp ((ModelField.negPartL hk).comp ((fderiv ℝ X w₀).comp (rL.comp (RL.comp B))))
    with hG'
  have hG : HasFDerivAt (D.tubeCoordE p hp ε ℓ ∘ D.leftSphereMap q (ℓ + 1) ε c ∘ ⇑R ∘
      Handle.bigDisc ℓ ρ) G' y := by
    have hXd' : HasFDerivAt X (fderiv ℝ X w₀) (rL (RL (Handle.bigDisc ℓ ρ y))) := by
      rw [hrL, hRL]; exact hXd.hasFDerivAt
    have hc := EL.hasFDerivAt.comp y ((ModelField.negPartL hk).hasFDerivAt.comp y
      (hXd'.comp y (rL.hasFDerivAt.comp y (RL.hasFDerivAt.comp y hB))))
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with z hz
    simp only [Function.comp_apply]
    rw [htube _ (fun h0 => hBnorm z hz (hreidx0 _ h0)), hrL, hRL]
    rfl
  set L := EL.comp ((fderiv ℝ (D.sardMap p hq ε c ε hp) w₀).comp rL) with hL
  set Φ := RL.comp B with hΦ
  have hw : R (Handle.bigDisc ℓ ρ y) ≠ 0 := hBnorm y (mem_ball_zero_iff.2 hy)
  have hLw : L (R (Handle.bigDisc ℓ ρ y)) = 0 := by
    simp only [hL, ContinuousLinearMap.comp_apply]
    rw [hrL, ← hw₀, hSray, map_zero]
  have hΦw : ∀ v, inner ℝ (R (Handle.bigDisc ℓ ρ y)) (Φ v) = 0 := by
    intro v
    rw [hΦ, ContinuousLinearMap.comp_apply, hRL, LinearIsometryEquiv.inner_map_map]
    exact hBorth v
  have hexp : ∀ (x : EuclideanSpace ℝ (Fin (ℓ + 1))),
      ∑ k, x k • EuclideanSpace.single k (1 : ℝ) = x := by
    intro x
    simpa using (EuclideanSpace.basisFun (Fin (ℓ + 1)) ℝ).sum_repr x
  have hRcol : ∀ (v : EuclideanSpace ℝ (Fin (ℓ + 1))) i,
      ∑ k, R (EuclideanSpace.single k 1) i * v k = R v i := by
    intro v i
    conv_rhs => rw [← hexp v]
    simp [map_sum, map_smul, mul_comm]
  have hor : 0 < (Matrix.of fun i j : Fin (ℓ + 1) => if (j : ℕ) = 0 then R (Handle.bigDisc ℓ ρ y) i
      else if hj : (j : ℕ) - 1 < ℓ then Φ (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i
        else 0).det := by
    set A : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
      Matrix.of fun i k => R (EuclideanSpace.single k 1) i with hA
    have hAdet : A.det = LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (ℓ + 1))) := by
      rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (ℓ + 1)) ℝ).toBasis]
      congr 1
    have hmat : (Matrix.of fun i j : Fin (ℓ + 1) => if (j : ℕ) = 0 then R (Handle.bigDisc ℓ ρ y) i
        else if hj : (j : ℕ) - 1 < ℓ then Φ (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i
          else 0) = A * (Matrix.of fun i j : Fin (ℓ + 1) =>
        if (j : ℕ) = 0 then Handle.bigDisc ℓ ρ y i else
          if hj : (j : ℕ) - 1 < ℓ then B (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i else 0) := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply, hA]
      by_cases hj0 : (j : ℕ) = 0
      · simp only [hj0, ite_true]
        exact (hRcol _ i).symm
      · simp only [hj0, ite_false]
        by_cases hj : (j : ℕ) - 1 < ℓ
        · simp only [hj, dite_true]
          rw [hΦ, ContinuousLinearMap.comp_apply, hRL]
          exact (hRcol _ i).symm
        · simp [hj]
    rw [hmat, Matrix.det_mul, hAdet]
    exact mul_pos hR hBdet
  have key := Handle.sign_det_comp_frame (R (Handle.bigDisc ℓ ρ y)) L Φ hw hLw hΦw hor
  have hLΦ : L.comp Φ =
      ‖DifferentialGeometry.Topology.Morse.CellAttachment.posPart hk (X w₀)‖ • G' := by
    ext1 v
    simp only [hL, hΦ, hG', ContinuousLinearMap.comp_apply, hS.fderiv,
      smul_apply, map_smul]
  have hpos : 0 < ‖DifferentialGeometry.Topology.Morse.CellAttachment.posPart hk (X w₀)‖ :=
    norm_pos_iff.2 hv0
  have hdet : LinearMap.det ((L.comp Φ : EuclideanSpace ℝ (Fin ℓ) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) :
      EuclideanSpace ℝ (Fin ℓ) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)) =
      ‖DifferentialGeometry.Topology.Morse.CellAttachment.posPart hk (X w₀)‖ ^ ℓ *
        LinearMap.det (G' : EuclideanSpace ℝ (Fin ℓ) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)) := by
    rw [hLΦ, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, finrank_euclideanSpace_fin]
  have hsub : (Matrix.of fun i j : Fin (ℓ + 1) => if (i : ℕ) = 0 then R (Handle.bigDisc ℓ ρ y) j
      else if hi : (i : ℕ) - 1 < ℓ then L (EuclideanSpace.single j 1) ⟨(i : ℕ) - 1, hi⟩ else 0) =
      (SardData.matrix (D.sardMap p hq ε c ε hp) w₀).submatrix (finCongr hkq.symm)
        (finCongr hkq.symm) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, SardData.matrix, finCongr_apply,
      Fin.val_cast]
    by_cases hi0 : (i : ℕ) = 0
    · simp only [hi0, ite_true, hw₀, Handle.reidx, Fin.val_cast]
      rw [dite_eq_left j.2]
    · have hi1 : (i : ℕ) - 1 < ℓ := by have := i.2; omega
      have hi2 : (i : ℕ) - 1 < (D.chart p hp).k := by rw [hkp]; exact hi1
      have hsingle : rL (EuclideanSpace.single j 1) = Pi.single (Fin.cast hkq.symm j) 1 := by
        funext m
        rw [hrL]
        have hm : (m : ℕ) < ℓ + 1 := by rw [← hkq]; exact m.2
        simp only [Handle.reidx, Pi.single_apply, dite_eq_left hm, PiLp.single_apply, Fin.ext_iff,
          Fin.val_cast]
      simp only [hi0, ite_false, dite_eq_left hi1, dite_eq_left hi2, hL,
        ContinuousLinearMap.comp_apply, hEL, hsingle]
  rw [hG.fderiv]
  change _ = ((SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w₀).det : SignType) : ℤ)
  congr 1
  rw [← Matrix.det_submatrix_equiv_self (finCongr hkq.symm), ← hsub, ← key, hdet, sign_mul,
    sign_pos (pow_pos hpos ℓ), one_mul]

end GradientLikeStrip

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem leftSphereHit_eq_leftSphereMap (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {q : M} (hq : q ∈ crit) {μ : ℕ}
    (hμ : (D.chart q hq).k = μ) {ε t : ℝ} (hε : 0 < ε) (hrm : 2 * ε < D.rm q hq ^ 2)
    (hat : a ≤ t) (ht : t < f q - ε)
    (hU : ∀ y, f y ∈ Icc t (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx) :
    ∀ y : EuclideanSpace ℝ (Fin μ), y ≠ 0 → D.leftSphereHit q μ ε t y = D.leftSphereMap q μ ε t y := by
  intro y hy
  subst hμ
  have hw : (Handle.reidx y : Fin (D.chart q hq).k → ℝ) ≠ 0 := by
    intro h
    apply hy
    ext i
    have := congrFun h i
    simpa [Handle.reidx, i.isLt] using this
  have hR : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    nlinarith
  have hmem := (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw
  have hfz : f ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y))) = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hR hmem
  have hstrip : f ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y))) ∈ Ioo a b :=
    D.inStrip q hq ⟨(D.chart q hq).sphereParam ε (Handle.reidx y),
      (D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hR hmem),
      rfl⟩
  have hunit := f_flow_eq_sub_of_levels (D := D) hf
    (x := (D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y))) (T := f q - ε - t)
    ⟨hstrip.1.le, hstrip.2.le⟩ (by rw [hfz, sub_sub_cancel]; exact ⟨hat, by linarith [hstrip.2]⟩)
    (by
      rw [hfz, sub_sub_cancel, uIcc_of_ge (by linarith)]
      exact hU)
  have hT : 0 ≤ f q - ε - t := by linarith
  have hhit : D.hitTime t ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (Handle.reidx y))) =
      f q - ε - t := by
    refine IsLeast.csInf_eq ⟨⟨hT, ?_⟩, ?_⟩
    · rw [hunit _ right_mem_uIcc, hfz]
      linarith
    · rintro s ⟨hs0, hs⟩
      by_contra hlt
      have hlt' : s < f q - ε - t := lt_of_not_ge hlt
      rw [hunit s (by rw [uIcc_of_le hT]; exact ⟨hs0, hlt'.le⟩), hfz] at hs
      linarith
  simp only [leftSphereHit, leftSphereMap, hq, dite_true]
  rw [descend, hhit]

end GradientLikeStrip

namespace BlockConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ}

theorem mem_slabCap_iff (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {q : M}
    (hq : q ∈ B.upperIndexCriticalPoints) {y : EuclideanSpace ℝ (Fin (ℓ + 1))} (hy : y ≠ 0) :
    (∀ p (hp : p ∈ B.lowerIndexCriticalPoints),
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c y ∈ B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1 ↔
        Handle.reidx y ∈ B.D.sardDom p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c B.ε (B.mem_lowerIndexCriticalPoints.1 hp).1 ∧
          B.D.sardMap p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c B.ε (B.mem_lowerIndexCriticalPoints.1 hp).1 (Handle.reidx y) = 0) ∧
      (B.D.leftSphereMap q (ℓ + 1) B.ε B.c y ∈ B.D.slabCap B.α ↔
        ∃ p, ∃ hp : p ∈ B.lowerIndexCriticalPoints, B.D.leftSphereMap q (ℓ + 1) B.ε B.c y ∈ B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hqidx : morseIndex I f q = ℓ + 1 := (B.mem_upperIndexCriticalPoints.1 hq).2
  have hqβ : f q = B.β := B.hQ q hqc hqidx
  have hε := B.hε
  have hαc := B.hαc
  have hcβ := B.hcβ
  have haα := B.haα
  have hβb := B.hβb
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by rw [← (B.D.chart q hqc).hkidx]; exact hqidx
  have hw : (Handle.reidx y : Fin (B.D.chart q hqc).k → ℝ) ≠ 0 := by
    intro h0
    apply hy
    ext j
    have hj : (j : ℕ) < (B.D.chart q hqc).k := by rw [hkq]; exact j.isLt
    have h1 := congrFun h0 ⟨j, hj⟩
    simp only [Handle.reidx, Pi.zero_apply, j.isLt, ↓reduceDIte] at h1
    simpa using h1
  have hσ : B.D.leftSphereMap q (ℓ + 1) B.ε B.c y = B.D.flow (f q - B.ε - B.c)
      ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε (Handle.reidx y))) := by
    simp only [GradientLikeStrip.leftSphereMap, hqc, ↓reduceDIte]
  have hεR : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have h1 := B.hrm q hqc
    have h2 : B.D.rm q hqc ^ 2 ≤ (B.D.chart q hqc).R ^ 2 :=
      pow_le_pow_left₀ (B.D.rm_pos q hqc).le (B.D.hrm q hqc).2 2
    linarith
  refine ⟨fun p hp => ?_, ?_⟩
  · have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
    have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
    set d := B.D.chart p hpc with hd
    set L := B.D.landing p hqc B.ε B.c B.ε (Handle.reidx y) with hL
    have hLσ : L = B.D.flow (B.c - (f p + B.ε)) (B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) := by
      rw [hσ]; rfl
    have hlev' : ∀ z, f z ∈ Icc (f p + B.ε) (f q - B.ε) → ∀ (p' : M) (hp' : p' ∈ B.crit),
        z ∉ B.D.smallBall p' hp' := by
      intro z hz
      rw [hpα, hqβ] at hz
      exact B.hlev z hz
    have hfL : f L = f p + B.ε :=
      GradientLikeStrip.f_landing hpc hfs hε hε hεR (by linarith) (by linarith) hlev' hw
    have hrmp := B.hrm p hpc
    have hrmR := (B.D.hrm p hpc).2
    have hrm0 := B.D.rm_pos p hpc
    have hstab : L ∈ B.D.captured p hpc ↔
        L ∈ d.χ '' {z | morseNorm n z < B.D.rm p hpc ∧ negPart d.hk z = 0} := by
      constructor
      · rintro ⟨T, z, ⟨hz1, hz2⟩, hzT⟩
        rcases le_or_gt T 0 with hT | hT
        · have h1 := GradientLikeStrip.flow_mem_of_negPart_eq_zero (D := B.D) hpc hz1 hz2
            (t := -T) (by linarith)
          rw [hzT, GradientLikeStrip.flow_flow, add_neg_cancel, GradientLikeStrip.flow_zero]
            at h1
          obtain ⟨w, hw, hwL⟩ := h1
          exact ⟨w, ⟨lt_of_le_of_lt hw.1 hz1, hw.2⟩, hwL⟩
        · have hzR : morseNorm n z ≤ d.R := hz1.le.trans hrmR
          have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
            d.hk z
          rw [hz2, norm_zero] at hsq
          set v := posPart d.hk z with hv
          have hfz : f (d.χ z) = f p + 1 / 2 * ‖v‖ ^ 2 := by
            rw [d.hnorm z hzR,
              DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hz2,
              norm_zero]
            ring
          have hfle : f (d.χ z) ≤ f L := by
            rw [hzT]
            have := GradientLikeStrip.f_flow_antitone (D := B.D) hfs L hT.le
            simpa [GradientLikeStrip.flow_zero] using this
          have hv0 : v ≠ 0 := by
            intro hv0
            rw [hv0, norm_zero] at hsq
            have hz0 : z = 0 := (ModelField.morseNorm_eq_zero_iff z).1 (by
              have : morseNorm n z ^ 2 = 0 := by rw [hsq]; ring
              exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
            rw [hz0, d.hχ0] at hzT
            have h1 : p = L := by
              have := congrArg (B.D.flow (-T)) hzT
              rwa [GradientLikeStrip.flow_flow, add_neg_cancel, GradientLikeStrip.flow_zero,
                GradientLikeStrip.flow_crit B.D hpc] at this
            rw [← h1] at hfL
            linarith
          have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
          set e := ‖v‖⁻¹ • v with he
          have hne : ‖e‖ = 1 := by
            rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
          set t0 := Real.sqrt (2 * B.ε) with ht0
          have ht0pos : 0 < t0 := Real.sqrt_pos.2 (by linarith)
          have ht0sq : t0 ^ 2 = 2 * B.ε := Real.sq_sqrt (by linarith)
          have ht0rm : t0 < B.D.rm p hpc := by
            refine lt_of_pow_lt_pow_left₀ 2 hrm0.le ?_
            rw [ht0sq]; linarith
          have hvt0 : ‖v‖ ≤ t0 := by
            refine Real.le_sqrt_of_sq_le ?_
            linarith
          obtain ⟨s, hs0, hsW⟩ := (CrossField.flow_ray_stable B.D hfs hpc hne ht0pos ht0rm).2
            ‖v‖ ⟨hvpos, hvt0⟩
          have hve : ‖v‖ • e = v := by
            rw [he, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
          have hzrec : recombine d.hk 0 v = z := by
            have := DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk z
            rwa [hz2] at this
          rw [hve, hzrec, hzT] at hsW
          set W := d.χ (recombine d.hk 0 (t0 • e)) with hW
          have hWrec_sq : morseNorm n (recombine d.hk 0 (t0 • e)) ^ 2 = 2 * B.ε := by
            rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq,
              norm_zero, norm_smul, hne, Real.norm_eq_abs, abs_of_pos ht0pos]
            rw [← ht0sq]; ring
          have hWn : morseNorm n (recombine d.hk 0 (t0 • e)) = t0 := by
            rw [← Real.sqrt_sq (ModelField.morseNorm_nonneg _), hWrec_sq]
          have hfW : f W = f p + B.ε := by
            rw [hW, d.hnorm _ (by rw [hWn]; exact ht0rm.le.trans hrmR),
              DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
              DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine,
              DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine,
              norm_zero, norm_smul, hne, Real.norm_eq_abs, abs_of_pos ht0pos]
            nlinarith
          have hWL : W = B.D.flow (T - s) L := by
            have := congrArg (B.D.flow (-s)) hsW
            rw [GradientLikeStrip.flow_flow, add_neg_cancel, GradientLikeStrip.flow_zero,
              GradientLikeStrip.flow_flow] at this
            rw [sub_eq_add_neg]; exact this
          have hcU : ∀ w, f w = f p + B.ε → dfV I f B.D.V w = -1 := by
            intro w hw
            refine B.D.dfV_eq_neg_one_of_level (c := f p + B.ε) ⟨by linarith, by linarith⟩
              (fun p' hp' w' hw' hfw' => ?_) hw
            refine B.hlev w' ?_ p' hp' hw'
            rw [hfw', hpα]
            constructor <;> linarith
          have hts : T - s = 0 :=
            GradientLikeStrip.flow_level_unique hfs (c := f p + B.ε) hcU (x := L)
              (by rw [← hWL]; exact hfW) (by rw [GradientLikeStrip.flow_zero]; exact hfL)
          rw [hts, GradientLikeStrip.flow_zero] at hWL
          refine ⟨recombine d.hk 0 (t0 • e), ⟨by rw [hWn]; exact ht0rm, ?_⟩, hWL ▸ hW.symm⟩
          exact DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine _ _ _
      · exact fun h => GradientLikeStrip.mem_captured_of_mem_stable h
    change B.D.leftSphereMap q (ℓ + 1) B.ε B.c y ∈ B.D.captured p hpc ↔
      Handle.reidx y ∈ B.D.sardDom p hqc B.ε B.c B.ε hpc ∧
        B.D.sardMap p hqc B.ε B.c B.ε hpc (Handle.reidx y) = 0
    rw [← GradientLikeStrip.flow_mem_captured_iff (B.c - (f p + B.ε)), ← hLσ, hstab]
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, hzL⟩
      have hzL' : d.χ z = L := hzL
      have hzR : morseNorm n z ≤ d.R := hz1.le.trans hrmR
      refine ⟨⟨hw, z, lt_of_lt_of_le hz1 hrmR, hzL⟩, ?_⟩
      change ModelField.scaledNegativePart d.hk (d.χ.symm L) = 0
      rw [← hzL', d.χ.left_inv (d.hsrc z hzR), ModelField.scaledNegativePart, hz2, smul_zero]
    · rintro ⟨hdom, hzero⟩
      obtain ⟨z, hzR, hzL⟩ := hdom.2
      have hzL' : d.χ z = L := hzL
      have hzR' : morseNorm n z ≤ d.R := le_of_lt hzR
      have hJ : ModelField.scaledNegativePart d.hk z = 0 := by
        have h1 : ModelField.scaledNegativePart d.hk (d.χ.symm L) = 0 := hzero
        rwa [← hzL', d.χ.left_inv (d.hsrc z hzR')] at h1
      have hfz : f (d.χ z) = f p + 1 / 2 * (‖posPart d.hk z‖ ^ 2 - ‖negPart d.hk z‖ ^ 2) := by
        rw [d.hnorm z hzR',
          DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
      rw [hzL', hfL] at hfz
      have hvne : ‖posPart d.hk z‖ ≠ 0 := by
        intro h0
        rw [h0] at hfz
        nlinarith [sq_nonneg ‖negPart d.hk z‖]
      have hu : negPart d.hk z = 0 := by
        rw [ModelField.scaledNegativePart, smul_eq_zero] at hJ
        rcases hJ with h | h
        · exact absurd h hvne
        · exact h
      have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        d.hk z
      rw [hu, norm_zero] at hsq hfz
      refine ⟨z, ⟨?_, hu⟩, hzL⟩
      refine lt_of_pow_lt_pow_left₀ 2 hrm0.le ?_
      nlinarith
  · constructor
    · rintro hmem
      simp only [GradientLikeStrip.slabCap, mem_iUnion] at hmem
      obtain ⟨x, hx, hfx, hcap⟩ := hmem
      have hxidx : morseIndex I f x = ℓ := by
        have h1 := B.hmin x hx
        rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h2 | h2
        · have := B.hhigh x hx h2
          linarith
        · rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h3 | h3
          · have h4 : morseIndex I f x = ℓ + 1 := by omega
            have := B.hQ x hx h4
            linarith
          · omega
      exact ⟨x, B.mem_lowerIndexCriticalPoints.2 ⟨hx, hxidx⟩, hcap⟩
    · rintro ⟨p, hp, hcap⟩
      simp only [GradientLikeStrip.slabCap, mem_iUnion]
      exact ⟨p, (B.mem_lowerIndexCriticalPoints.1 hp).1, B.hP p (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_lowerIndexCriticalPoints.1 hp).2, hcap⟩

theorem sardZeros_finite (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {p q : M}
    (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) (htr : B.pairTransverse p q) :
    (B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1).Finite := by
  classical
  obtain ⟨hpc, hqc, htr⟩ := htr
  change (B.D.sardZeros p hqc B.ε B.c hpc).Finite
  have hpm := B.mem_lowerIndexCriticalPoints.1 hp
  have hqm := B.mem_upperIndexCriticalPoints.1 hq
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by rw [← (B.D.chart q hqc).hkidx]; exact hqm.2
  have hkp : (B.D.chart p hpc).k = ℓ := by rw [← (B.D.chart p hpc).hkidx]; exact hpm.2
  have hfp : f p = B.α := B.hP p hpc hpm.2
  have hfq : f q = B.β := B.hQ q hqc hqm.2
  have hlev' : ∀ y, f y ∈ Icc (f p + B.ε) (f q - B.ε) → ∀ p' hp', y ∉ B.D.smallBall p' hp' := by
    rw [hfp, hfq]; exact B.hlev
  have hηc : f p + B.ε ≤ B.c := by rw [hfp]; exact B.hαc.le
  have hcq : B.c ≤ f q - B.ε := by rw [hfq]; linarith [B.hcβ]
  have hεR : ∀ x (hx : x ∈ B.crit), 2 * B.ε < (B.D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (B.D.hrm x hx).2
    have h2 := B.D.rm_pos x hx
    have h3 := B.hrm x hx
    have h4 : B.D.rm x hx ^ 2 ≤ (B.D.chart x hx).R ^ 2 := pow_le_pow_left₀ h2.le h1 2
    linarith [B.hε]
  have hεRq : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := (hεR q hqc).le
  have hεRp : 2 * B.ε ≤ (B.D.chart p hpc).R ^ 2 := (hεR p hpc).le
  set S := B.D.sardMap p hqc B.ε B.c B.ε hpc with hS
  set U := B.D.sardDom p hqc B.ε B.c B.ε hpc with hU
  change (SardData.zeros S U).Finite
  have hUopen : IsOpen U := GradientLikeStrip.isOpen_sardDom B.hε.le hεRq
  have hSdiff : DifferentiableOn ℝ S U :=
    GradientLikeStrip.differentiableOn_sardMap hf.smooth B.hε B.hε hεRq hηc hcq hlev'
  have hray : ∀ v : Fin (B.D.chart q hqc).k → ℝ, v ≠ 0 → ∀ t : ℝ, 0 < t → S (t • v) = S v := by
    intro v hv t ht
    simp only [hS, GradientLikeStrip.sardMap]
    rw [B.D.landing_smul p hqc B.ε B.c B.ε ht hv]
  have hiso : ∀ w ∈ SardData.zeros S U, ∀ᶠ v in 𝓝 w, v ∈ SardData.zeros S U → v = w := by
    rintro w ⟨hwU, hw1, hw0⟩
    have hwne : w ≠ 0 := by rintro rfl; simp at hw1
    have hL : HasFDerivAt S (fderiv ℝ S w) w :=
      ((hSdiff w hwU).differentiableAt (hUopen.mem_nhds hwU)).hasFDerivAt
    set L := fderiv ℝ S w with hLdef
    have hsurj : Function.Surjective L := htr w hwU hw0
    have hLw : L w = 0 := by
      have hg : HasDerivAt (fun t : ℝ => t • w) ((1 : ℝ) • w) 1 := (hasDerivAt_id (1 : ℝ)).smul_const w
      have hL1 : HasFDerivAt S L ((fun t : ℝ => t • w) 1) := by simpa using hL
      have h1 := hL1.comp_hasDerivAt (1 : ℝ) hg
      have h2 : HasDerivAt (S ∘ fun t : ℝ => t • w) 0 1 := by
        refine (hasDerivAt_const (1 : ℝ) (S w)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
        simp [hray w hwne t ht]
      simpa using h1.unique h2
    have hfin : Module.finrank ℝ (LinearMap.ker (L : (Fin (B.D.chart q hqc).k → ℝ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (B.D.chart p hpc).k))) = 1 := by
      have h := LinearMap.finrank_range_add_finrank_ker (L : (Fin (B.D.chart q hqc).k → ℝ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (B.D.chart p hpc).k))
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_euclideanSpace_fin,
        Module.finrank_fin_fun] at h
      omega
    have hker : ∀ h, L h = 0 → ∃ c : ℝ, c • w = h := by
      intro h hh
      have hw' : (⟨w, LinearMap.mem_ker.2 hLw⟩ : LinearMap.ker (L : (Fin (B.D.chart q hqc).k → ℝ) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (B.D.chart p hpc).k))) ≠ 0 := by
        intro h0; apply hwne; simpa using congrArg Subtype.val h0
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw').1 hfin ⟨h, LinearMap.mem_ker.2 hh⟩
      exact ⟨c, by simpa using congrArg Subtype.val hc⟩
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push Not at h; exact hwne (funext h)
    set φ : (Fin (B.D.chart q hqc).k → ℝ) →L[ℝ] ℝ := (w i)⁻¹ • ContinuousLinearMap.proj i with hφ
    have hφapp : ∀ v, φ v = (w i)⁻¹ * v i := fun v => rfl
    have hφw : φ w = 1 := by rw [hφapp]; exact inv_mul_cancel₀ hi
    set T := L.prod φ with hT
    have hTinj : LinearMap.ker (T : (Fin (B.D.chart q hqc).k → ℝ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (B.D.chart p hpc).k) × ℝ) = ⊥ := by
      refine LinearMap.ker_eq_bot'.2 fun h hh => ?_
      have hh' : L h = 0 ∧ φ h = 0 := by
        have := Prod.ext_iff.1 hh
        exact ⟨this.1, this.2⟩
      obtain ⟨c, rfl⟩ := hker h hh'.1
      have := hh'.2
      rw [map_smul, hφw, smul_eq_mul, mul_one] at this
      rw [this, zero_smul]
    obtain ⟨K, hK0, hK⟩ := LinearMap.exists_antilipschitzWith _ hTinj
    have hKpos : (0 : ℝ) < K := NNReal.coe_pos.2 hK0
    have hKle : ∀ h, ‖h‖ ≤ K * ‖T h‖ := fun h => by simpa using hK.le_mul_dist h 0
    have hLo := hL.isLittleO.def (c := 1 / (2 * K)) (by positivity)
    have hrc : ContinuousAt (fun v => (φ v)⁻¹ • v) w :=
      ((φ.continuous.continuousAt).inv₀ (by rw [hφw]; exact one_ne_zero)).smul continuousAt_id
    have hrt : Tendsto (fun v => (φ v)⁻¹ • v) (𝓝 w) (𝓝 w) := by
      simpa [hφw] using hrc.tendsto
    filter_upwards [hrt.eventually hLo, (φ.continuous.tendsto w).eventually
      (lt_mem_nhds (by rw [hφw]; exact zero_lt_one : (0 : ℝ) < φ w))] with v hv1 hv2 hvZ
    obtain ⟨_, hvn, hv0⟩ := hvZ
    have hvne : v ≠ 0 := by rintro rfl; simp at hvn
    have hSr : S ((φ v)⁻¹ • v) = 0 := by rw [hray v hvne _ (inv_pos.2 hv2)]; exact hv0
    set x := (φ v)⁻¹ • v - w with hx
    have hφx : φ x = 0 := by
      rw [hx, map_sub, map_smul, smul_eq_mul, inv_mul_cancel₀ hv2.ne', hφw, sub_self]
    have hLx : ‖L x‖ ≤ 1 / (2 * K) * ‖x‖ := by
      rw [hSr, hw0] at hv1; simpa using hv1
    have hTx : ‖T x‖ = ‖L x‖ := by
      rw [hT, ContinuousLinearMap.prod_apply, Prod.norm_def, hφx, norm_zero]
      exact max_eq_left (norm_nonneg _)
    have hx0 : x = 0 := by
      have h1 := hKle x
      rw [hTx] at h1
      have h2 : (K : ℝ) * ‖L x‖ ≤ K * (1 / (2 * K) * ‖x‖) := mul_le_mul_of_nonneg_left hLx hKpos.le
      have h3 : (K : ℝ) * (1 / (2 * K) * ‖x‖) = ‖x‖ / 2 := by field_simp
      have h4 : ‖x‖ ≤ 0 := by linarith [norm_nonneg x]
      exact norm_le_zero_iff.1 h4
    have hvw : v = φ v • w := by
      rw [hx, sub_eq_zero] at hx0
      rw [← hx0, smul_smul, mul_inv_cancel₀ hv2.ne', one_smul]
    have hφv : φ v = 1 := by
      have := congrArg norm hvw
      rw [norm_smul, hw1, hvn, mul_one, Real.norm_eq_abs, abs_of_pos hv2] at this
      exact this.symm
    rw [hvw, hφv, one_smul]
  have hsub : B.D.landing p hqc B.ε B.c B.ε '' SardData.zeros S U ⊆
      (B.D.chart p hpc).χ '' (B.D.chart p hpc).rightModelSphere B.ε := by
    rintro _ ⟨z, ⟨⟨hzne, y, hyR, hyeq⟩, _, hz0⟩, rfl⟩
    have hyR' : morseNorm n y < (B.D.chart p hpc).R := hyR
    have hJ : ModelField.scaledNegativePart (B.D.chart p hpc).hk y = 0 := by
      have h := hz0
      simp only [hS, GradientLikeStrip.sardMap] at h
      rw [← hyeq, (B.D.chart p hpc).χ.left_inv ((B.D.chart p hpc).hsrc y hyR'.le)] at h
      exact h
    have hfl := GradientLikeStrip.f_landing hpc hf.smooth B.hε B.hε hεRq hηc hcq hlev' hzne
    rw [← hyeq, (B.D.chart p hpc).hnorm y hyR'.le] at hfl
    have hv : posPart (B.D.chart p hpc).hk y ≠ 0 :=
      ModelField.posPart_ne_zero_of_lt_nf _ (c := f p) (by rw [hfl]; linarith [B.hε])
    have hu : negPart (B.D.chart p hpc).hk y = 0 := (ModelField.scaledNegativePart_eq_zero_iff _ hv).1 hJ
    have hn := ModelField.nf_sub_eq (B.D.chart p hpc).hk (f p) y
    rw [hfl, hu, norm_zero] at hn
    refine ⟨y, ⟨hu, ?_⟩, hyeq⟩
    linarith
  have hclosed : IsClosed (SardData.zeros S U) := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have hw1 : ‖w‖ = 1 := by
      have : w ∈ Metric.sphere (0 : Fin (B.D.chart q hqc).k → ℝ) 1 :=
        closure_minimal (fun z hz => by simpa using hz.2.1) Metric.isClosed_sphere hw
      simpa using this
    have hwne : w ≠ 0 := by rintro rfl; simp at hw1
    have hKc : IsClosed ((B.D.chart p hpc).χ '' (B.D.chart p hpc).rightModelSphere B.ε) :=
      ((B.D.chart p hpc).isCompact_image_rightModelSphere hεRp).isClosed
    have hcont : ContinuousAt (B.D.landing p hqc B.ε B.c B.ε) w :=
      (GradientLikeStrip.continuousOn_landing B.hε.le hεRq).continuousAt (isOpen_ne.mem_nhds hwne)
    obtain ⟨y, hy, hyeq⟩ := closure_minimal hsub hKc (hcont.continuousWithinAt.mem_closure_image hw)
    have hyR : morseNorm n y < (B.D.chart p hpc).R := by
      refine lt_of_pow_lt_pow_left₀ 2 (B.D.chart p hpc).R_pos.le ?_
      rw [(B.D.chart p hpc).morseNorm_sq_of_mem_rightModelSphere hy]
      exact hεR p hpc
    have hwU : w ∈ U := ⟨hwne, y, hyR, hyeq⟩
    have hScont : ContinuousAt S w := hSdiff.continuousOn.continuousAt (hUopen.mem_nhds hwU)
    have hsub0 : S '' SardData.zeros S U ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩; exact hz.2.2
    exact ⟨hwU, hw1, closure_minimal hsub0 isClosed_singleton
      (hScont.continuousWithinAt.mem_closure_image hw)⟩
  have hcomp : IsCompact (SardData.zeros S U) :=
    (isCompact_sphere (0 : Fin (B.D.chart q hqc).k → ℝ) 1).of_isClosed_subset hclosed
      (fun z hz => by simpa using hz.2.1)
  obtain ⟨t, -, ht⟩ := hcomp.elim_nhds_subcover
    (fun w => {v | v ∈ SardData.zeros S U → v = w}) hiso
  refine t.finite_toSet.subset fun z hz => ?_
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (ht hz)
  rw [hzx hz]
  exact hx

theorem finite_sphereCap (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (htr : B.transverse) {q : M} (hq : q ∈ B.upperIndexCriticalPoints) :
    {z | z ∈ SingularPair.unitSphere ℓ ∧ B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.slabCap B.α}.Finite := by
  classical
  have hq' : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hK : (B.D.chart q hq').k = ℓ + 1 := by
    rw [← (B.D.chart q hq').hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hre : ∀ (z : EuclideanSpace ℝ (Fin (ℓ + 1))) (i : Fin (ℓ + 1)),
      (Handle.reidx z : Fin (B.D.chart q hq').k → ℝ) ⟨i, by rw [hK]; exact i.isLt⟩ = z i := by
    intro z i
    simp [Handle.reidx, i.isLt]
  have hne : ∀ z ∈ SingularPair.unitSphere ℓ,
      (Handle.reidx z : Fin (B.D.chart q hq').k → ℝ) ≠ 0 := by
    intro z hz h0
    apply (show z ≠ 0 from by
      intro h; rw [h] at hz; simp at hz)
    ext i
    have := hre z i
    rw [h0] at this
    simpa using this.symm
  let g : EuclideanSpace ℝ (Fin (ℓ + 1)) → (Fin (B.D.chart q hq').k → ℝ) := fun z =>
    ‖(Handle.reidx z : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ • Handle.reidx z
  let T : Set (Fin (B.D.chart q hq').k → ℝ) :=
    ⋃ (p : M) (hp : p ∈ (B.lowerIndexCriticalPoints : Set M)), B.D.sardZeros p hq' B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hT : T.Finite :=
    Set.Finite.biUnion' B.lowerIndexCriticalPoints.finite_toSet (fun p hp => sardZeros_finite hf B hp hq (htr p hp q hq))
  have hinj : Set.InjOn g
      {z | z ∈ SingularPair.unitSphere ℓ ∧ B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.slabCap B.α} := by
    intro z hz z' hz' hzz
    have hn : 0 < ‖(Handle.reidx z : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 (hne z hz.1))
    have hn' : 0 < ‖(Handle.reidx z' : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 (hne z' hz'.1))
    have hvec : ‖(Handle.reidx z : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ • z =
        ‖(Handle.reidx z' : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ • z' := by
      ext i
      have := congrFun hzz ⟨i, by rw [hK]; exact i.isLt⟩
      simp only [g, Pi.smul_apply, smul_eq_mul, hre] at this
      simpa using this
    have hz1 : ‖z‖ = 1 := by simpa using hz.1
    have hz1' : ‖z'‖ = 1 := by simpa using hz'.1
    have hnorm := congrArg norm hvec
    rw [norm_smul, norm_smul, hz1, hz1', Real.norm_of_nonneg hn.le,
      Real.norm_of_nonneg hn'.le, mul_one, mul_one] at hnorm
    rw [hnorm] at hvec
    exact smul_right_injective _ hn'.ne' hvec
  have hmaps : Set.MapsTo g
      {z | z ∈ SingularPair.unitSphere ℓ ∧ B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.slabCap B.α} T := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; have := hz.1; rw [h] at this; simp at this
    obtain ⟨hcapiff, hslab⟩ := mem_slabCap_iff hf B hq hz0
    obtain ⟨p, hp, hcap⟩ := hslab.1 hz.2
    obtain ⟨hdom, hzero⟩ := (hcapiff p hp).1 hcap
    have hw := hne z hz.1
    have ht : 0 < ‖(Handle.reidx z : Fin (B.D.chart q hq').k → ℝ)‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 hw)
    have hland := GradientLikeStrip.landing_smul (D := B.D) p hq' B.ε B.c B.ε ht hw
    refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨Finset.mem_coe.2 hp, ?_⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact smul_ne_zero ht.ne' hw
    · simp only [g, Set.mem_preimage]
      rw [hland]
      exact hdom.2
    · simp only [g]
      rw [norm_smul, Real.norm_of_nonneg ht.le, inv_mul_cancel₀ (norm_pos_iff.2 hw).ne']
    · change ModelField.scaledNegativePart _ ((B.D.chart p _).χ.symm (B.D.landing p hq' B.ε B.c B.ε (g z))) = 0
      simp only [g]
      rw [hland]
      exact hzero
  exact Set.Finite.of_finite_image (hT.subset (Set.mapsTo_iff_image_subset.1 hmaps)) hinj

theorem discClass_zero_eq_sign (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 1 ≤ ℓ) (haα : a < B.α - B.ε) {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q)
    (R : EuclideanSpace ℝ (Fin (ℓ + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))
    (hR : 0 < LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1)))) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {y : EuclideanSpace ℝ (Fin ℓ)} (hy : ‖y‖ < 1) (hy0 : y ≠ 0)
    (hzero : B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈
      B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1)
    {r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁y : r₁ < ‖y‖)
    (hiso : ∀ y' ∈ Metric.closedBall y r₁,
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y')) ∈ B.D.slabCap B.α → y' = y)
    (gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk ℓ)))
      (ULift.down ⁻¹' diskSphere ℓ) ℓ) :
    ∃ r₀ > (0 : ℝ), ∀ r : ℝ, 0 < r → r < r₀ →
      Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
          (fun y' => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ (y + r • y')))) gD =
        B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1
            (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) •
          Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
            (B.D.leftDiscMap p ℓ B.ε a) gD := by
  have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hkp : (B.D.chart p hpc).k = ℓ := by
    rw [← (B.D.chart p hpc).hkidx]; exact (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by
    rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
  have hεr : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  have hαc := B.hαc
  have hcβ := B.hcβ
  have hβb := B.hβb
  have hε := B.hε
  have hcb : B.c ≤ b := by linarith
  have hfge : ∀ x ∈ B.crit, B.α ≤ f x := by
    intro x hx
    have h1 := B.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h2 | h2
    · have := B.hhigh x hx h2; linarith
    · rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h3 | h3
      · have := B.hQ x hx (by omega); linarith
      · have := B.hP x hx (by omega); linarith
  have hslab : ∀ x ∈ B.crit, f x ∈ Icc a B.c → f x = B.α := by
    intro x hx hxc
    have h1 := B.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h2 | h2
    · have := B.hhigh x hx h2; linarith [hxc.2]
    · rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h3 | h3
      · have := B.hQ x hx (by omega); linarith [hxc.2]
      · exact B.hP x hx (by omega)
  have hUup : ∀ y, f y ∈ Icc (B.α + B.ε) B.c → ∀ w hw, y ∉ B.D.smallBall w hw :=
    fun y hy w hw => B.hlev y ⟨hy.1, by linarith [hy.2]⟩ w hw
  have hUlow : ∀ y, f y ∈ Icc a (B.α - B.ε) → ∀ w hw, y ∉ B.D.smallBall w hw := by
    intro y hy w hw hyw
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hw hyw
    have h2 := hfge w hw
    have h3 := B.hr₀ w hw
    rw [abs_lt] at h1
    linarith [hy.2]
  have hRq : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have h1 := B.hrm q hqc
    have h2 := (B.D.hrm q hqc).2
    have h3 := B.D.rm_pos q hqc
    nlinarith
  have hreidx_ne : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      (Handle.reidx u : Fin (B.D.chart q hqc).k → ℝ) ≠ 0 := by
    intro u hu h
    apply hu
    ext i
    have := congrFun h ⟨i, by omega⟩
    have h2 : (i : ℕ) ≤ ℓ → u i = 0 := by simpa [Handle.reidx] using this
    exact h2 (Nat.lt_succ_iff.1 i.2)
  have hLS : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), B.D.leftSphereMap q (ℓ + 1) B.ε B.c u =
      B.D.flow (f q - B.ε - B.c) ((B.D.chart q hqc).χ
        ((B.D.chart q hqc).sphereParam B.ε (Handle.reidx u))) := by
    intro u
    unfold GradientLikeStrip.leftSphereMap
    simp only [hqc, ↓reduceDIte]
  have hlevel : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      f (B.D.leftSphereMap q (ℓ + 1) B.ε B.c u) = B.c := by
    intro u hu
    have hmem : B.D.leftSphereMap q (ℓ + 1) B.ε B.c u ∈ B.D.leftSphere q hqc B.ε B.c := by
      rw [hLS]
      exact ⟨_, ⟨_, (B.D.chart q hqc).sphereParam_mem_leftModelSphere hε.le (hreidx_ne u hu),
        rfl⟩, rfl⟩
    have := B.D.leftSphere_subset_level hsm q hqc hRq ⟨by linarith [B.haα], hcb⟩
      (fun y hy w hw => by
        rw [uIcc_of_ge (by rw [hqβ]; linarith)] at hy
        exact B.hlev y ⟨by linarith [hy.1], by rw [hqβ] at hy; linarith [hy.2]⟩ w hw) hmem
    simpa using this
  have hLsm : ∀ w : Fin (B.D.chart q hqc).k → ℝ, w ≠ 0 →
      ContMDiffAt 𝓘(ℝ, Fin (B.D.chart q hqc).k → ℝ) I ∞
        (fun w => B.D.flow (f q - B.ε - B.c)
          ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε w))) w := by
    intro w hw
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (B.D.chart q hqc).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((B.D.chart q hqc).sphereParam B.ε) w :=
      contMDiffAt_iff_contDiffAt.2 ((B.D.chart q hqc).contDiffAt_sphereParam B.ε hw)
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (B.D.chart q hqc).χ
        ((B.D.chart q hqc).sphereParam B.ε w) :=
      (B.D.chart q hqc).contMDiffAt_chart
        ((B.D.chart q hqc).mem_ball_of_le ((B.D.chart q hqc).morseNorm_sphereParam_le hε.le hRq hw))
    exact (B.D.contMDiff_flow _).contMDiffAt.comp w (hχq.comp w hsp)
  have hland_sm : ∀ w : Fin (B.D.chart q hqc).k → ℝ, w ∈ B.D.sardDom p hqc B.ε B.c B.ε hpc →
      ContDiffAt ℝ ∞ (fun w => (B.D.chart p hpc).χ.symm (B.D.landing p hqc B.ε B.c B.ε w)) w := by
    rintro w ⟨hw0, hland⟩
    have hland' := (B.D.chart p hpc).image_lt_subset_image_ball (B.D.chart p hpc).hRR'.le hland
    have hsymm : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (B.D.chart p hpc).χ.symm
        (B.D.landing p hqc B.ε B.c B.ε w) :=
      (B.D.chart p hpc).contMDiffAt_symm hland'
    have := hsymm.comp w ((B.D.contMDiff_flow _).contMDiffAt.comp w (hLsm w hw0))
    exact contMDiffAt_iff_contDiffAt.1 this
  have hreidx_cd : ContDiff ℝ ∞
      (Handle.reidx : EuclideanSpace ℝ (Fin (ℓ + 1)) → Fin (B.D.chart q hqc).k → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    unfold Handle.reidx
    by_cases h : (i : ℕ) < ℓ + 1
    · simp only [h, ↓reduceDIte]
      exact (EuclideanSpace.proj (⟨i, h⟩ : Fin (ℓ + 1)) : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] ℝ).contDiff
    · simp only [h, ↓reduceDIte]
      exact contDiff_const
  have hbig := Handle.bigDisc_spec ℓ hρ hρ1
  set r₁' : ℝ := min r₁ ((1 - ‖y‖) / 2) with hr₁'def
  have hr₁'pos : 0 < r₁' := lt_min hr₁ (by linarith)
  have hr₁'le : r₁' ≤ r₁ := min_le_left _ _
  have hr₁'le2 : r₁' ≤ (1 - ‖y‖) / 2 := min_le_right _ _
  have hball1 : ∀ y' ∈ Metric.closedBall y r₁', y' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1 := by
    intro y' hy'
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_insert' y' y
    have h3 : ‖y'‖ ≤ ‖y‖ + ‖y' - y‖ := by
      calc ‖y'‖ = ‖y + (y' - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖y' - y‖ := norm_add_le _ _
    linarith
  have hball0 : ∀ y' ∈ Metric.closedBall y r₁', y' ≠ 0 := by
    intro y' hy' h0
    rw [h0, Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hy'
    linarith
  have hbig_ne : ∀ y' ∈ Metric.closedBall y r₁', R (Handle.bigDisc ℓ ρ y') ≠ 0 := by
    intro y' hy' h0
    have h1 := hbig.1 (hball1 y' hy')
    rw [mem_sphere_zero_iff_norm] at h1
    have h2 : ‖R (Handle.bigDisc ℓ ρ y')‖ = 1 := by rw [R.norm_map]; exact h1
    rw [h0, norm_zero] at h2
    exact zero_ne_one h2
  set F : EuclideanSpace ℝ (Fin ℓ) → M :=
    fun y' => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y')) with hFdef
  have hFc : ContinuousOn F (Metric.closedBall y r₁') := by
    intro y' hy'
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun y' => Handle.reidx (R (Handle.bigDisc ℓ ρ y')) :
        EuclideanSpace ℝ (Fin ℓ) → Fin (B.D.chart q hqc).k → ℝ) y' :=
      hreidx_cd.continuous.continuousAt.comp (R.continuous.continuousAt.comp hbig.2.2.2.2.2.1.continuousAt)
    have h2 := ContinuousAt.comp (f := fun y' => Handle.reidx (R (Handle.bigDisc ℓ ρ y')))
      (x := y') (hLsm _ (hreidx_ne _ (hbig_ne y' hy'))).continuousAt h1
    have h3 : F = (fun w => B.D.flow (f q - B.ε - B.c)
          ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε w))) ∘
        (fun y' => Handle.reidx (R (Handle.bigDisc ℓ ρ y'))) := by
      funext y''; simp only [hFdef, Function.comp, hLS]
    rw [h3]; exact h2
  have hFX : MapsTo F (Metric.closedBall y r₁') (f ⁻¹' Icc a B.c) := by
    intro y' hy'
    rw [mem_preimage, hFdef, hlevel _ (hbig_ne y' hy')]
    exact ⟨by linarith [B.haα], le_rfl⟩
  have hFcap : ∀ y' ∈ Metric.closedBall y r₁', F y' ∈ B.D.slabCap B.α → y' = y :=
    fun y' hy' h => hiso y' (Metric.closedBall_subset_closedBall hr₁'le hy') h
  have hy1 : R (Handle.bigDisc ℓ ρ y) ≠ 0 := hbig_ne y (Metric.mem_closedBall_self hr₁'pos.le)
  obtain ⟨hdom, hS0⟩ := ((mem_slabCap_iff hf B hq hy1).1 p hp).1 hzero
  have hc₁ : f p + B.ε < B.c := by rw [hpα]; linarith
  have hc₂ : B.c < f q - B.ε := by rw [hqβ]; linarith
  have hsign := GradientLikeStrip.sign_det_sphereSard hsm B.D hpc hqc hkp hkq (B.sardValid hp hq)
    hc₁ hc₂ R hR hρ hρ1 hy hdom hS0
  have hFeq : (B.D.tubeCoordE p hpc B.ε ℓ ∘ F) = B.D.tubeCoordE p hpc B.ε ℓ ∘
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c ∘ R ∘ Handle.bigDisc ℓ ρ := rfl
  have hpm : B.D.sardSign p hqc B.ε B.c hpc (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) = 1 ∨
      B.D.sardSign p hqc B.ε B.c hpc (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) = -1 := by
    obtain ⟨_, _, htr'⟩ := htr
    refine SardData.sign_eq_one_or_neg_one (by rw [hkq, hkp])
      (GradientLikeStrip.isOpen_sardDom hε.le hRq) ⟨fun w hw => hw.1, fun w hw t ht => ?_⟩
      hdom hS0 (htr' _ hdom hS0)
    have hl := B.D.landing_smul p hqc B.ε B.c B.ε ht hw.1
    refine ⟨⟨smul_ne_zero ht.ne' hw.1, ?_⟩, ?_⟩
    · rw [mem_preimage, hl]; exact hw.2
    · unfold GradientLikeStrip.sardMap
      rw [hl]
  have hdet : LinearMap.det (fderiv ℝ (B.D.tubeCoordE p hpc B.ε ℓ ∘ F) y :
      EuclideanSpace ℝ (Fin ℓ) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)) ≠ 0 := by
    intro h0
    rw [hFeq] at h0
    rw [h0, sign_zero, SignType.coe_zero] at hsign
    rcases hpm with h | h <;> rw [h] at hsign <;> norm_num at hsign
  have hG : ContDiffAt ℝ 1 (B.D.tubeCoordE p hpc B.ε ℓ ∘ F) y := by
    have hbigCD : ContDiffAt ℝ ∞ (Handle.bigDisc ℓ ρ) y :=
      hbig.2.2.2.2.2.2.contDiffAt (isOpen_ne.mem_nhds hy0)
    have hcore : ContDiffAt ℝ ∞ (fun y' => negPart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm
        (B.D.landing p hqc B.ε B.c B.ε (Handle.reidx (R (Handle.bigDisc ℓ ρ y')))))) y := by
      have h1 : ContDiffAt ℝ ∞ (fun y' => (Handle.reidx (R (Handle.bigDisc ℓ ρ y')) :
          Fin (B.D.chart q hqc).k → ℝ)) y :=
        hreidx_cd.contDiffAt.comp y (R.contDiff.contDiffAt.comp y hbigCD)
      have h2 := (hland_sm _ hdom).comp y h1
      exact (ModelField.negPartL (B.D.chart p hpc).hk).contDiff.contDiffAt.comp y h2
    have hg : ContDiffAt ℝ ∞ (fun y' => fun i : Fin ℓ =>
        if h : (i : ℕ) < (B.D.chart p hpc).k then negPart (B.D.chart p hpc).hk
          ((B.D.chart p hpc).χ.symm (B.D.landing p hqc B.ε B.c B.ε
            (Handle.reidx (R (Handle.bigDisc ℓ ρ y'))))) ⟨i, h⟩ else 0) y := by
      refine contDiffAt_pi.2 fun i => ?_
      by_cases h : (i : ℕ) < (B.D.chart p hpc).k
      · simp only [h, ↓reduceDIte]
        exact (EuclideanSpace.proj (⟨i, h⟩ : Fin (B.D.chart p hpc).k) :
          EuclideanSpace ℝ (Fin (B.D.chart p hpc).k) →L[ℝ] ℝ).contDiff.contDiffAt.comp y hcore
      · simp only [h, ↓reduceDIte]
        exact contDiffAt_const
    have hGsm := (PiLp.contDiff_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin ℓ => ℝ)
      (n := ∞)).contDiffAt.comp y hg
    have hev : (B.D.tubeCoordE p hpc B.ε ℓ ∘ F) =ᶠ[𝓝 y] (WithLp.toLp 2 ∘ fun y' => fun i : Fin ℓ =>
        if h : (i : ℕ) < (B.D.chart p hpc).k then negPart (B.D.chart p hpc).hk
          ((B.D.chart p hpc).χ.symm (B.D.landing p hqc B.ε B.c B.ε
            (Handle.reidx (R (Handle.bigDisc ℓ ρ y'))))) ⟨i, h⟩ else 0) := by
      filter_upwards [Metric.closedBall_mem_nhds y hr₁'pos] with y' hy'
      have hfF : f (F y') = B.c := hlevel _ (hbig_ne y' hy')
      have hFy : F y' = B.D.flow (f q - B.ε - B.c) ((B.D.chart q hqc).χ
          ((B.D.chart q hqc).sphereParam B.ε (Handle.reidx (R (Handle.bigDisc ℓ ρ y'))))) := hLS _
      have hkey : B.D.tubeCoord p hpc B.ε (F y') = negPart (B.D.chart p hpc).hk
          ((B.D.chart p hpc).χ.symm (B.D.landing p hqc B.ε B.c B.ε
            (Handle.reidx (R (Handle.bigDisc ℓ ρ y'))))) := by
        have hle : f p + B.ε ≤ f (F y') := by rw [hfF]; linarith
        unfold GradientLikeStrip.tubeCoord
        simp only [hle, ↓reduceIte]
        rw [GradientLikeStrip.rightCoord, hfF, hFy]
        rfl
      simp only [Function.comp, GradientLikeStrip.tubeCoordE]
      rw [hkey]
    exact (hGsm.congr_of_eventuallyEq hev).of_le (by exact_mod_cast le_top)
  obtain ⟨r₀, hr₀, hloc⟩ := GradientLikeStrip.discClass_tube_local hsm B.D B.hcrit hε hεr
    (le_refl a) haα hαc hcb hslab hUup hpc hpα hkp hℓ F y hr₁'pos hFc hFX hzero hFcap hG hdet gD
  refine ⟨r₀, hr₀, fun r hr hrr => ?_⟩
  have hρ₁ : 0 < B.D.rm p hpc / 2 := half_pos (B.D.rm_pos p hpc)
  have hρ₁R : B.D.rm p hpc / 2 < B.D.rm p hpc := half_lt_self (B.D.rm_pos p hpc)
  have h1 := hloc r hr hrr _ hρ₁ hρ₁R
  rw [hFeq, hsign] at h1
  rw [GradientLikeStrip.discClass_leftDisc_eq_smallDisc hsm B.D B.hcrit hε hεr (le_refl a) haα hαc
    hcb hslab hUlow hpc hpα hkp hρ₁ hρ₁R gD]
  exact h1

theorem count_eq_sum_bigDisc (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {p q : M}
    (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (R : EuclideanSpace ℝ (Fin (ℓ + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (Zs : Finset (EuclideanSpace ℝ (Fin ℓ)))
    (hZs : ∀ y, y ∈ Zs ↔ y ∈ Metric.closedBall 0 1 ∧
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈
        B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hcap : ∀ z ∈ SingularPair.unitSphere ℓ, z 0 ≤ Real.cos (ρ * Real.pi) →
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R z) ∉ B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1) :
    B.count p q = ∑ y ∈ Zs, B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1
      (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) := by
  classical
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hk : (B.D.chart q hqc).k = ℓ + 1 := by
    rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hspec := Handle.bigDisc_spec ℓ hρ hρ1
  have hray : SardData.rayInvariant (B.D.sardMap p hqc B.ε B.c B.ε hpc)
      (B.D.sardDom p hqc B.ε B.c B.ε hpc) := by
    refine ⟨fun w hw => hw.1, fun w hw t ht => ?_⟩
    have hL := B.D.landing_smul p hqc B.ε B.c B.ε ht hw.1
    refine ⟨⟨smul_ne_zero ht.ne' hw.1, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, hL]; exact hw.2
    · change ModelField.scaledNegativePart _ ((B.D.chart p hpc).χ.symm (B.D.landing p hqc B.ε B.c B.ε (t • w))) = _
      rw [hL]; rfl
  have hU : IsOpen (B.D.sardDom p hqc B.ε B.c B.ε hpc) := by
    refine GradientLikeStrip.isOpen_sardDom B.hε.le ?_
    have h1 := B.hrm q hqc
    have h2 := (B.D.hrm q hqc).2
    have h3 := B.D.rm_pos q hqc
    nlinarith
  have hsph : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1,
      ‖R (Handle.bigDisc ℓ ρ y)‖ = 1 := by
    intro y hy
    rw [LinearIsometryEquiv.norm_map]
    simpa using hspec.1 hy
  have hsmul_reidx : ∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin (ℓ + 1))),
      (Handle.reidx (k := (B.D.chart q hqc).k) (c • x)) = c • Handle.reidx x := by
    intro c x
    funext i
    simp only [Handle.reidx, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hzero : ∀ y ∈ Zs, Handle.reidx (R (Handle.bigDisc ℓ ρ y)) ∈
      B.D.sardDom p hqc B.ε B.c B.ε hpc ∧
      B.D.sardMap p hqc B.ε B.c B.ε hpc (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) = 0 := by
    intro y hy
    obtain ⟨hyb, hyc⟩ := (hZs y).1 hy
    have hne : R (Handle.bigDisc ℓ ρ y) ≠ 0 := by
      intro h
      have := hsph y hyb
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact ((mem_slabCap_iff hf B hq hne).1 p hp).1 hyc
  let v : EuclideanSpace ℝ (Fin ℓ) → (Fin (B.D.chart q hqc).k → ℝ) := fun y =>
    Handle.reidx (R (Handle.bigDisc ℓ ρ y))
  let e : EuclideanSpace ℝ (Fin ℓ) → (Fin (B.D.chart q hqc).k → ℝ) := fun y => ‖v y‖⁻¹ • v y
  have hbij : Set.BijOn e ↑Zs (B.D.sardZeros p hqc B.ε B.c hpc) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨hU', hS'⟩ := hzero y hy
      have hpos : 0 < ‖v y‖ := norm_pos_iff.2 hU'.1
      obtain ⟨h1, h2⟩ := hray.2 _ hU' _ (inv_pos.2 hpos)
      refine ⟨h1, ?_, ?_⟩
      · change ‖‖v y‖⁻¹ • v y‖ = 1
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      · change B.D.sardMap p hqc B.ε B.c B.ε hpc (‖v y‖⁻¹ • v y) = 0
        rw [h2]; exact hS'
    · intro y₁ hy₁ y₂ hy₂ heq
      have hb₁ := ((hZs y₁).1 hy₁).1
      have hb₂ := ((hZs y₂).1 hy₂).1
      have hp₁ : 0 < ‖v y₁‖ := norm_pos_iff.2 (hzero y₁ hy₁).1.1
      have hp₂ : 0 < ‖v y₂‖ := norm_pos_iff.2 (hzero y₂ hy₂).1.1
      have hv : v y₁ = (‖v y₁‖ * ‖v y₂‖⁻¹) • v y₂ := by
        have : ‖v y₁‖ • e y₁ = ‖v y₁‖ • e y₂ := by rw [heq]
        simp only [e, smul_smul, mul_inv_cancel₀ hp₁.ne', one_smul] at this
        exact this
      obtain ⟨t, htdef⟩ : ∃ t, t = ‖v y₁‖ * ‖v y₂‖⁻¹ := ⟨_, rfl⟩
      rw [← htdef] at hv
      have htpos : 0 < t := htdef ▸ mul_pos hp₁ (inv_pos.2 hp₂)
      have hz : R (Handle.bigDisc ℓ ρ y₁) = t • R (Handle.bigDisc ℓ ρ y₂) := by
        ext j
        have := congrFun hv ⟨j, by rw [hk]; exact j.2⟩
        have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.2
        simpa [v, Handle.reidx, hj] using this
      have ht1 : t = 1 := by
        have := congrArg norm hz
        rw [norm_smul, hsph y₁ hb₁, hsph y₂ hb₂, Real.norm_eq_abs, abs_of_pos htpos] at this
        linarith
      rw [ht1, one_smul] at hz
      exact hspec.2.1 hb₁ hb₂ (R.injective hz)
    · intro w hw
      obtain ⟨hwU, hw1, hwS⟩ := hw
      let E : EuclideanSpace ℝ (Fin (ℓ + 1)) := WithLp.toLp 2
        (fun i => if h : (i : ℕ) < (B.D.chart q hqc).k then w ⟨i, h⟩ else 0)
      have hE : Handle.reidx (k := (B.D.chart q hqc).k) E = w := by
        funext i
        have hi : (i : ℕ) < ℓ + 1 := hk ▸ i.2
        simp [Handle.reidx, E, hi]
      have hEne : E ≠ 0 := by
        intro h
        apply hwU.1
        rw [← hE, h]
        funext i
        simp [Handle.reidx]
      have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hEne
      obtain ⟨z, hzdef⟩ : ∃ z, z = ‖E‖⁻¹ • E := ⟨_, rfl⟩
      have hznorm : ‖z‖ = 1 := by
        rw [hzdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hEpos.ne']
      have hzr : Handle.reidx (k := (B.D.chart q hqc).k) z = ‖E‖⁻¹ • w := by
        rw [hzdef, hsmul_reidx, hE]
      obtain ⟨hzU, hzS⟩ := hray.2 w hwU _ (inv_pos.2 hEpos)
      have hzne : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hznorm
        exact zero_ne_one hznorm
      have hcapz : B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.captured p hpc :=
        ((mem_slabCap_iff hf B hq hzne).1 p hp).2 ⟨hzr ▸ hzU, by rw [hzr, hzS]; exact hwS⟩
      have hz' : R.symm z ∈ SingularPair.unitSphere ℓ := by
        simp [hznorm]
      have hcos : Real.cos (ρ * Real.pi) ≤ R.symm z 0 := by
        by_contra hlt
        exact hcap _ hz' (le_of_lt (not_le.1 hlt)) (by rw [R.apply_symm_apply]; exact hcapz)
      obtain ⟨y, hyb, hyz⟩ := hspec.2.2.1 _ hz' hcos
      have hRy : R (Handle.bigDisc ℓ ρ y) = z := by rw [hyz, R.apply_symm_apply]
      refine ⟨y, (hZs y).2 ⟨hyb, by rw [hRy]; exact hcapz⟩, ?_⟩
      have hvy : v y = ‖E‖⁻¹ • w := by
        change Handle.reidx (R (Handle.bigDisc ℓ ρ y)) = _
        rw [hRy, hzr]
      change ‖v y‖⁻¹ • v y = w
      rw [hvy, norm_smul, norm_inv, norm_norm, hw1, mul_one, inv_inv, smul_smul,
        mul_inv_cancel₀ hEpos.ne', one_smul]
  have hcount : B.count p q = SardData.count (B.D.sardMap p hqc B.ε B.c B.ε hpc)
      (B.D.sardDom p hqc B.ε B.c B.ε hpc) := by
    simp only [count, hpc, hqc, ↓reduceDIte]
    rfl
  rw [hcount, SardData.count, ← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn e hbij ?_
  intro y hy
  have hvU := (hzero y hy).1
  exact (SardData.sign_smul hU hray hvU (inv_pos.2 (norm_pos_iff.2 hvU.1))).symm

theorem sphereClass_cap_eq_sum (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (htr : B.transverse) (hℓ : 1 ≤ ℓ) (haα : a < B.α - B.ε)
    (gS : SingularPair.singularHomology SingularPair.integerCoefficients (SingularPair.Sphere.liftedSphere ℓ) ℓ)
    (gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk ℓ)))
      (ULift.down ⁻¹' diskSphere ℓ) ℓ) {s : ℤ}
    (hs : ∀ (Bs As : Set M) (F : EuclideanSpace ℝ (Fin (ℓ + 1)) → M) (ρ : ℝ), 0 < ρ → ρ < 1 →
      ContinuousOn F (SingularPair.unitSphere ℓ) → MapsTo F (SingularPair.unitSphere ℓ) Bs →
      (∀ z ∈ SingularPair.unitSphere ℓ, z 0 ≤ Real.cos (ρ * Real.pi) → F z ∈ As) →
      Handle.sphereClass Bs As F gS = s • Handle.discClass Bs As (F ∘ Handle.bigDisc ℓ ρ) gD)
    {q : M} (hq : q ∈ B.upperIndexCriticalPoints) :
    Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
        (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) gS =
      ∑ p ∈ B.lowerIndexCriticalPoints, (s * B.count p q) •
        Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
          (B.D.leftDiscMap p ℓ B.ε a) gD := by
  classical
  have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
  have hαc := B.hαc
  have hcβ := B.hcβ
  have hβb := B.hβb
  have hε := B.hε
  have hcb : B.c ≤ b := by linarith
  have hac : a ≤ B.c := by linarith [B.haα]
  have hRq : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have h1 := B.hrm q hqc
    have h2 := (B.D.hrm q hqc).2
    have h3 := B.D.rm_pos q hqc
    nlinarith
  have hreidx_ne : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      (Handle.reidx u : Fin (B.D.chart q hqc).k → ℝ) ≠ 0 := by
    have hkq : (B.D.chart q hqc).k = ℓ + 1 := by
      rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
    intro u hu h
    apply hu
    ext i
    have := congrFun h ⟨i, by omega⟩
    have h2 : (i : ℕ) ≤ ℓ → u i = 0 := by simpa [Handle.reidx] using this
    exact h2 (Nat.lt_succ_iff.1 i.2)
  have hLS : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), B.D.leftSphereMap q (ℓ + 1) B.ε B.c u =
      B.D.flow (f q - B.ε - B.c) ((B.D.chart q hqc).χ
        ((B.D.chart q hqc).sphereParam B.ε (Handle.reidx u))) := by
    intro u
    unfold GradientLikeStrip.leftSphereMap
    simp only [hqc, ↓reduceDIte]
  have hlevel : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      f (B.D.leftSphereMap q (ℓ + 1) B.ε B.c u) = B.c := by
    intro u hu
    have hmem : B.D.leftSphereMap q (ℓ + 1) B.ε B.c u ∈ B.D.leftSphere q hqc B.ε B.c := by
      rw [hLS]
      exact ⟨_, ⟨_, (B.D.chart q hqc).sphereParam_mem_leftModelSphere hε.le (hreidx_ne u hu),
        rfl⟩, rfl⟩
    have := B.D.leftSphere_subset_level hsm q hqc hRq ⟨by linarith [B.haα], hcb⟩
      (fun y hy w hw => by
        rw [uIcc_of_ge (by rw [hqβ]; linarith)] at hy
        exact B.hlev y ⟨by linarith [hy.1], by rw [hqβ] at hy; linarith [hy.2]⟩ w hw) hmem
    simpa using this
  have hLsm : ∀ w : Fin (B.D.chart q hqc).k → ℝ, w ≠ 0 →
      ContMDiffAt 𝓘(ℝ, Fin (B.D.chart q hqc).k → ℝ) I ∞
        (fun w => B.D.flow (f q - B.ε - B.c)
          ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε w))) w := by
    intro w hw
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (B.D.chart q hqc).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((B.D.chart q hqc).sphereParam B.ε) w :=
      contMDiffAt_iff_contDiffAt.2 ((B.D.chart q hqc).contDiffAt_sphereParam B.ε hw)
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (B.D.chart q hqc).χ
        ((B.D.chart q hqc).sphereParam B.ε w) :=
      (B.D.chart q hqc).contMDiffAt_chart
        ((B.D.chart q hqc).mem_ball_of_le ((B.D.chart q hqc).morseNorm_sphereParam_le hε.le hRq hw))
    exact (B.D.contMDiff_flow _).contMDiffAt.comp w (hχq.comp w hsp)
  have hreidx_cd : ContDiff ℝ ∞
      (Handle.reidx : EuclideanSpace ℝ (Fin (ℓ + 1)) → Fin (B.D.chart q hqc).k → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    unfold Handle.reidx
    by_cases h : (i : ℕ) < ℓ + 1
    · simp only [h, ↓reduceDIte]
      exact (EuclideanSpace.proj (⟨i, h⟩ : Fin (ℓ + 1)) : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] ℝ).contDiff
    · simp only [h, ↓reduceDIte]
      exact contDiff_const
  have hσc : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      ContinuousAt (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) u := by
    intro u hu
    have h1 : ContinuousAt (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) =>
        (Handle.reidx u : Fin (B.D.chart q hqc).k → ℝ)) u := hreidx_cd.continuous.continuousAt
    have h2 := ContinuousAt.comp (f := fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) =>
        (Handle.reidx u : Fin (B.D.chart q hqc).k → ℝ)) (x := u)
      (hLsm _ (hreidx_ne u hu)).continuousAt h1
    have h3 : B.D.leftSphereMap q (ℓ + 1) B.ε B.c = (fun w => B.D.flow (f q - B.ε - B.c)
          ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε w))) ∘
        (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) => (Handle.reidx u : Fin (B.D.chart q hqc).k → ℝ)) := by
      funext u'; simp only [Function.comp, hLS]
    rw [h3]; exact h2
  have hsph_ne : ∀ z ∈ SingularPair.unitSphere ℓ, z ≠ 0 := by
    intro z hz h0
    rw [h0] at hz
    simp at hz
  have hσcont : ContinuousOn (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) (SingularPair.unitSphere ℓ) :=
    fun z hz => (hσc z (hsph_ne z hz)).continuousWithinAt
  have hσX : MapsTo (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) (SingularPair.unitSphere ℓ)
      (f ⁻¹' Icc a B.c) := by
    intro z hz
    rw [mem_preimage, hlevel z (hsph_ne z hz)]
    exact ⟨hac, le_rfl⟩
  have hcapdisj : ∀ (p p' : M) (hp : p ∈ B.crit) (hp' : p' ∈ B.crit) (x : M),
      x ∈ B.D.captured p hp → x ∈ B.D.captured p' hp' → p = p' := by
    intro p p' hp hp' x hx hx'
    by_contra hne
    obtain ⟨T, hT⟩ := GradientLikeStrip.mem_captured_iff_eventually.1 hx
    obtain ⟨T', hT'⟩ := GradientLikeStrip.mem_captured_iff_eventually.1 hx'
    have h1 := hT (max T T') (le_max_left _ _)
    have h2 := hT' (max T T') (le_max_right _ _)
    exact Set.disjoint_left.1 (B.D.disjoint p hp p' hp' hne)
      (B.D.modelBall_subset_image_ball p hp (image_mono (fun z hz => hz.1) h1))
      (B.D.modelBall_subset_image_ball p' hp' (image_mono (fun z hz => hz.1) h2))
  have hcapsub : ∀ (p : M) (hp : p ∈ B.lowerIndexCriticalPoints) (x : M), x ∈ B.D.captured p (B.mem_lowerIndexCriticalPoints.1 hp).1 →
      x ∈ B.D.slabCap B.α := by
    intro p hp x hx
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨(B.mem_lowerIndexCriticalPoints.1 hp).1, Set.mem_iUnion.2
      ⟨B.hP p (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_lowerIndexCriticalPoints.1 hp).2, hx⟩⟩⟩
  have hZc := finite_sphereCap hf B htr hq
  have hsphInf : (SingularPair.unitSphere ℓ).Infinite := by
    have hball : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1).Infinite := by
      have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
      exact infinite_of_mem_nhds (0 : EuclideanSpace ℝ (Fin ℓ)) (Metric.closedBall_mem_nhds 0 one_pos)
    have hb := Handle.bigDisc_spec ℓ (ρ := 1 / 2) (by norm_num) (by norm_num)
    exact (hball.image hb.2.1).mono (Set.image_subset_iff.2 hb.1)
  obtain ⟨u, hu, huZ⟩ := (hsphInf.sdiff (hZc.union (hZc.image (fun z => -z)))).nonempty
  have hu1 : ‖u‖ = 1 := by simpa using hu
  have huC : B.D.leftSphereMap q (ℓ + 1) B.ε B.c u ∉ B.D.slabCap B.α :=
    fun h => huZ (Or.inl ⟨hu, h⟩)
  have hnuC : B.D.leftSphereMap q (ℓ + 1) B.ε B.c (-u) ∉ B.D.slabCap B.α := by
    intro h
    refine huZ (Or.inr ⟨-u, ⟨?_, h⟩, neg_neg u⟩)
    simpa using hu
  obtain ⟨R, hRe, hRdet, hRcl⟩ := Handle.exists_rotation_sphereClass ℓ hℓ u hu1
  have hrot := hRcl (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
    (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) gS hσcont hσX
  have hRsph : MapsTo R (SingularPair.unitSphere ℓ) (SingularPair.unitSphere ℓ) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz ⊢
    rw [R.norm_map]; exact hz
  have hgt : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖z‖ = 1 →
      z ≠ -EuclideanSpace.single 0 1 → -1 < z 0 := by
    intro z hz hne
    have h := norm_add_sq_real z (EuclideanSpace.single 0 1)
    rw [EuclideanSpace.inner_single_right, hz, PiLp.norm_single, norm_one] at h
    have hpos : 0 < ‖z + EuclideanSpace.single 0 1‖ :=
      norm_pos_iff.2 (fun h0 => hne (eq_neg_of_add_eq_zero_left h0))
    simp at h
    nlinarith
  have hgt' : ∀ w ∈ {z | z ∈ SingularPair.unitSphere ℓ ∧
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.slabCap B.α}, -1 < (R.symm w) 0 := by
    intro w hw
    refine hgt _ ?_ ?_
    · rw [R.symm.norm_map]; simpa using hw.1
    · intro h
      apply hnuC
      have : w = -u := by
        rw [← hRe, ← map_neg, ← h, R.apply_symm_apply]
      rw [← this]; exact hw.2
  have hevρ : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Ioo 0 1 ∧ ∀ w ∈ {z | z ∈ SingularPair.unitSphere ℓ ∧
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c z ∈ B.D.slabCap B.α},
        Real.cos (ρ * Real.pi) < (R.symm w) 0 := by
    have ht : Tendsto (fun ρ : ℝ => Real.cos (ρ * Real.pi)) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := by
      have hc : Continuous fun ρ : ℝ => Real.cos (ρ * Real.pi) := by fun_prop
      have := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa [Real.cos_pi] using this
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num),
      (eventually_all_finite hZc).2 (fun w hw => ht.eventually_lt_const (hgt' w hw))] with ρ h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hρw⟩ := hevρ.exists
  have hcapρ : ∀ z ∈ SingularPair.unitSphere ℓ, z 0 ≤ Real.cos (ρ * Real.pi) →
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R z) ∉ B.D.slabCap B.α := by
    intro z hz hz0 hC
    have := hρw (R z) ⟨hRsph hz, hC⟩
    rw [R.symm_apply_apply] at this
    linarith
  have hcontR : ContinuousOn (B.D.leftSphereMap q (ℓ + 1) B.ε B.c ∘ R) (SingularPair.unitSphere ℓ) :=
    hσcont.comp R.continuous.continuousOn hRsph
  have hmapsR : MapsTo (B.D.leftSphereMap q (ℓ + 1) B.ε B.c ∘ R) (SingularPair.unitSphere ℓ)
      (f ⁻¹' Icc a B.c) := hσX.comp hRsph
  have hS := hs (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
    (B.D.leftSphereMap q (ℓ + 1) B.ε B.c ∘ R) ρ hρ0 hρ1 hcontR hmapsR
    (fun z hz hz0 => ⟨hmapsR hz, hcapρ z hz hz0⟩)
  have hb := Handle.bigDisc_spec ℓ hρ0 hρ1
  have hYfin : {y : EuclideanSpace ℝ (Fin ℓ) | y ∈ Metric.closedBall 0 1 ∧
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈ B.D.slabCap B.α}.Finite := by
    refine Set.Finite.of_finite_image (f := fun y => R (Handle.bigDisc ℓ ρ y)) (hZc.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨hRsph (hb.1 hy.1), hy.2⟩
    · intro y hy y' hy' h
      exact hb.2.1 hy.1 hy'.1 (R.injective h)
  obtain ⟨Zs, hZsdef⟩ : ∃ Zs : Finset (EuclideanSpace ℝ (Fin ℓ)), Zs = hYfin.toFinset := ⟨_, rfl⟩
  have hmemZs : ∀ y, y ∈ Zs ↔ y ∈ Metric.closedBall 0 1 ∧
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈ B.D.slabCap B.α := by
    intro y
    rw [hZsdef, Set.Finite.mem_toFinset]
    rfl
  have hRb_ne : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1,
      R (Handle.bigDisc ℓ ρ y) ≠ 0 := fun y hy => hsph_ne _ (hRsph (hb.1 hy))
  have hZs0 : ∀ y ∈ Zs, y ≠ 0 := by
    intro y hy h0
    obtain ⟨-, hC⟩ := (hmemZs y).1 hy
    rw [h0, hb.2.2.2.2.1, hRe] at hC
    exact huC hC
  have hZs1 : ∀ y ∈ Zs, ‖y‖ < 1 := by
    intro y hy
    obtain ⟨hyB, hC⟩ := (hmemZs y).1 hy
    have hle : ‖y‖ ≤ 1 := by simpa using hyB
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      refine hcapρ _ (hb.1 hyB) ?_ hC
      rw [hb.2.2.2.1, h, mul_one]
  have hevδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∀ y ∈ Zs, δ < ‖y‖ ∧ δ < 1 - ‖y‖) ∧
      ∀ y ∈ Zs, ∀ y' ∈ Zs, y ≠ y' → 2 * δ < dist y y' := by
    have ht : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have ht2 : Tendsto (fun δ : ℝ => 2 * δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ht.const_mul 2
    refine ((eventually_all_finset Zs).2 (fun y hy => ?_)).and
      ((eventually_all_finset Zs).2 fun y hy => (eventually_all_finset Zs).2 fun y' hy' => ?_)
    · exact (ht.eventually_lt_const (norm_pos_iff.2 (hZs0 y hy))).and
        (ht.eventually_lt_const (by linarith [hZs1 y hy]))
    · by_cases hyy : y = y'
      · exact Eventually.of_forall fun δ h => absurd hyy h
      · exact (ht2.eventually_lt_const (dist_pos.2 hyy)).mono fun δ h _ => h
  obtain ⟨δ, ⟨hδZ, hδd⟩, hδ0⟩ := (hevδ.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  replace hδ0 : 0 < δ := hδ0.1
  have hiso : ∀ y ∈ Zs, ∀ y' ∈ Metric.closedBall y δ,
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y')) ∈ B.D.slabCap B.α →
        y' = y := by
    intro y hy y' hy' hC
    have hd : dist y' y ≤ δ := hy'
    have hy'B : y' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have := norm_le_norm_add_norm_sub' y' y
      have h2 : ‖y' - y‖ = dist y' y := (dist_eq_norm y' y).symm
      linarith [(hδZ y hy).2]
    by_contra hne
    have := hδd y' ((hmemZs y').2 ⟨hy'B, hC⟩) y hy hne
    linarith
  have hloc : ∀ y ∈ Zs, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
          (fun y' => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ (y + r • y')))) gD =
        ∑ p ∈ B.lowerIndexCriticalPoints.attach, if B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈
            B.D.captured p.1 (B.mem_lowerIndexCriticalPoints.1 p.2).1 then
          B.D.sardSign p.1 hqc B.ε B.c (B.mem_lowerIndexCriticalPoints.1 p.2).1 (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) •
            Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
              (B.D.leftDiscMap p.1 ℓ B.ε a) gD
        else 0 := by
    intro y hy
    obtain ⟨hyB, hyC⟩ := (hmemZs y).1 hy
    obtain ⟨p, hp, hcap⟩ := (mem_slabCap_iff hf B hq (hRb_ne y hyB)).2.1 hyC
    obtain ⟨r₀, hr₀, hr⟩ := discClass_zero_eq_sign hf B hℓ haα hp hq (htr p hp q hq) R hRdet hρ0 hρ1
      (hZs1 y hy) (hZs0 y hy) hcap hδ0 (hδZ y hy).1 (hiso y hy) gD
    have hsum : (∑ p' ∈ B.lowerIndexCriticalPoints.attach,
        if B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈
            B.D.captured p'.1 (B.mem_lowerIndexCriticalPoints.1 p'.2).1 then
          B.D.sardSign p'.1 hqc B.ε B.c (B.mem_lowerIndexCriticalPoints.1 p'.2).1 (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) •
            Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
              (B.D.leftDiscMap p'.1 ℓ B.ε a) gD
        else 0) =
        B.D.sardSign p hqc B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 (Handle.reidx (R (Handle.bigDisc ℓ ρ y))) •
          Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
            (B.D.leftDiscMap p ℓ B.ε a) gD := by
      rw [Finset.sum_eq_single ⟨p, hp⟩]
      · exact ite_eq_left_of_eq_true _ _ (eq_true hcap)
      · intro p' _ hp'
        have hn : B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∉
            B.D.captured p'.1 (B.mem_lowerIndexCriticalPoints.1 p'.2).1 := fun hcap' =>
          hp' (Subtype.ext (hcapdisj _ _ _ _ _ hcap' hcap))
        exact ite_eq_right_of_eq_false _ _ (eq_false hn)
      · intro h
        exact absurd (Finset.mem_attach _ _) h
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr'
    rw [hsum]
    exact hr r hr'.1 hr'.2
  obtain ⟨r, hrZ, hr0, hrδ⟩ :=
    (((eventually_all_finset Zs).2 hloc).and (Ioo_mem_nhdsGT hδ0)).exists
  have hFc : ContinuousOn (fun y => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)))
      (Metric.closedBall 0 1) := by
    intro y hy
    exact (ContinuousAt.comp (f := fun y => R (Handle.bigDisc ℓ ρ y)) (x := y) (hσc _ (hRb_ne y hy))
      (R.continuous.comp hb.2.2.2.2.2.1).continuousAt).continuousWithinAt
  have hFB : MapsTo (fun y => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)))
      (Metric.closedBall 0 1) (f ⁻¹' Icc a B.c) := fun y hy => hσX (hRsph (hb.1 hy))
  have hZ : ∀ z ∈ Zs, Metric.closedBall z r ⊆ Metric.ball 0 1 := by
    intro z hz y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hd : dist y z ≤ r := hy
    have := norm_le_norm_add_norm_sub' y z
    have h2 : ‖y - z‖ = dist y z := (dist_eq_norm y z).symm
    linarith [(hδZ z hz).2]
  have hdisj : ∀ z ∈ Zs, ∀ z' ∈ Zs, z ≠ z' →
      Disjoint (Metric.closedBall z r) (Metric.closedBall z' r) := by
    intro z hz z' hz' hne
    refine Metric.closedBall_disjoint_closedBall ?_
    linarith [hδd z hz z' hz' hne]
  have hC : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1,
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈ B.D.slabCap B.α → y ∈ Zs :=
    fun y hy h => (hmemZs y).2 ⟨hy, h⟩
  have hL := Handle.discClass_localize (f ⁻¹' Icc a B.c) (B.D.slabCap B.α) _ hFc hFB Zs hr0 hZ
    hdisj hC gD
  rw [← hrot, hS]
  change s • Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
      (fun y => B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y))) gD = _
  rw [hL, Finset.sum_congr rfl hrZ, Finset.sum_comm]
  conv_rhs => rw [← Finset.sum_attach]
  refine (Finset.sum_zsmul _ _ s).symm.trans (Finset.sum_congr rfl (fun p _ => ?_))
  rw [count_eq_sum_bigDisc hf B p.2 hq R hρ0 hρ1 (Zs.filter (fun y =>
      B.D.leftSphereMap q (ℓ + 1) B.ε B.c (R (Handle.bigDisc ℓ ρ y)) ∈
        B.D.captured p.1 (B.mem_lowerIndexCriticalPoints.1 p.2).1)) ?_ ?_]
  · rw [mul_zsmul]
    congr 1
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl (fun y _ => ?_))
      (@Finset.sum_smul _ ℤ _ _ _ (AddCommGroup.toIntModule _) _ _ _).symm
    split_ifs <;> simp
  · intro y
    rw [Finset.mem_filter, hmemZs]
    constructor
    · rintro ⟨⟨hy, -⟩, h⟩
      exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨hy, hcapsub p.1 p.2 _ h⟩, h⟩
  · intro z hz hz0 h
    exact hcapρ z hz hz0 (hcapsub p.1 p.2 _ h)

theorem sphereClass_eq_sum (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (htr : B.transverse) (hℓ : 1 ≤ ℓ) (haα : a < B.α - B.ε)
    (gS : SingularPair.singularHomology SingularPair.integerCoefficients (SingularPair.Sphere.liftedSphere ℓ) ℓ) (hgS : Handle.isGen gS)
    (gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk ℓ)))
      (ULift.down ⁻¹' diskSphere ℓ) ℓ) (hgD : Handle.isGen gD) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ q ∈ B.upperIndexCriticalPoints,
      Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) gS =
        ∑ p ∈ B.lowerIndexCriticalPoints, (s * B.count p q) •
          Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) (B.D.leftDiscMap p ℓ B.ε a) gD := by
  classical
  obtain ⟨s, hs1, hs⟩ := Handle.exists_sphere_bigDisc_sign ℓ hℓ gS hgS gD hgD
  refine ⟨s, hs1, fun q hq => ?_⟩
  have hcap := sphereClass_cap_eq_sum hf B htr hℓ haα gS gD
    (fun Bs As F ρ h1 h2 h3 h4 h5 => hs Bs As F ρ h1 h2 h3 h4 h5) hq
  have hεr : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  have hαβ : B.α < B.β := by linarith [B.hαc, B.hcβ, B.hε]
  have hlevel : ∀ x ∈ B.crit, f x = B.α ∨ B.β ≤ f x := by
    intro x hx
    rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h | h
    · rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h' | h'
      · exact Or.inr (B.hhigh x hx h').le
      · exact Or.inr (B.hQ x hx (by omega)).ge
    · exact Or.inl (B.hP x hx (le_antisymm h (B.hmin x hx)))
  have hcb : B.c ≤ b := by linarith [B.hcβ, B.hβb, B.hε]
  have hslab : ∀ x ∈ B.crit, f x ∈ Icc a B.c → f x = B.α := by
    intro x hx hxc
    rcases hlevel x hx with h | h
    · exact h
    · exfalso; linarith [hxc.2, B.hcβ, B.hε]
  have hU : ∀ y, f y ∈ Icc a (B.α - B.ε) ∪ Icc (B.α + B.ε) B.c →
      ∀ w hw, y ∉ B.D.smallBall w hw := by
    intro y hy w hw hyw
    have habs := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall (D := B.D) hw hyw
    have hr := B.hr₀ w hw
    rw [abs_lt] at habs
    rcases hlevel w hw with h | h
    · rcases hy with hy | hy
      · linarith [hy.2]
      · linarith [hy.1]
    · rcases hy with hy | hy
      · linarith [hy.2]
      · linarith [hy.2, B.hcβ]
  have hμ : ∀ x (hx : x ∈ B.crit), f x = B.α → (B.D.chart x hx).k = ℓ := by
    intro x hx hxα
    rw [← (B.D.chart x hx).hkidx]
    rcases Nat.lt_or_ge ℓ (morseIndex I f x) with h | h
    · exfalso
      rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h' | h'
      · linarith [B.hhigh x hx h']
      · linarith [B.hQ x hx (by omega)]
    · exact le_antisymm h (B.hmin x hx)
  have hex := GradientLikeStrip.isIso_inclPair_slab hf.smooth B.D B.hcrit B.hε hεr le_rfl haα
    B.hαc hcb hslab
  rw [Set.Icc_self] at hex
  obtain ⟨hsub, hiso⟩ := hex
  have hbas := GradientLikeStrip.slab_discClass_basis hf.smooth B.D B.hcrit B.hε hεr le_rfl haα
    B.hαc hcb hslab hU hμ hℓ gD hgD
  rw [Set.Icc_self] at hbas
  have hinj := (ModuleCat.mono_iff_injective
    (Handle.inclPair (subset_refl (f ⁻¹' Icc a B.c)) hsub ℓ)).1 inferInstance
  have hdisc : ∀ p ∈ B.lowerIndexCriticalPoints, ContinuousOn (B.D.leftDiscMap p ℓ B.ε a) (Metric.closedBall 0 1) ∧
      MapsTo (B.D.leftDiscMap p ℓ B.ε a) (Metric.closedBall 0 1) (f ⁻¹' Icc a B.c) ∧
      MapsTo (B.D.leftDiscMap p ℓ B.ε a) (Metric.sphere 0 1) (f ⁻¹' {a}) := by
    intro p hp
    by_contra hcon
    have hzero : Handle.discClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) (B.D.leftDiscMap p ℓ B.ε a) gD =
        0 := by
      unfold Handle.discClass
      exact dite_eq_right hcon
    have hpf : p ∈ B.crit.filter (fun x => f x = B.α) :=
      Finset.mem_filter.2 ⟨(B.mem_lowerIndexCriticalPoints.1 hp).1, B.hP p (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_lowerIndexCriticalPoints.1 hp).2⟩
    have h1 := hbas.2 (fun x => if x = p then 1 else 0) (by
      rw [Finset.sum_eq_single_of_mem p hpf (fun x _ hxp => by simp [hxp])]
      simp [hzero]) p hpf
    simp at h1
  have hsph : Handle.inclPair (subset_refl (f ⁻¹' Icc a B.c)) hsub ℓ
      (Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) gS) =
      Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' Icc a B.c \ B.D.slabCap B.α)
        (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) gS := by
    by_cases hF : ContinuousOn (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) (SingularPair.unitSphere ℓ) ∧
        MapsTo (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) (SingularPair.unitSphere ℓ) (f ⁻¹' Icc a B.c)
    · exact Handle.inclPair_sphereClass _ _ _ hF.1 hF.2 gS
    · unfold Handle.sphereClass
      rw [dite_eq_right hF, dite_eq_right hF, map_zero]
  apply hinj
  rw [hsph, hcap, map_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [map_zsmul]
  obtain ⟨h1, h2, h3⟩ := hdisc p hp
  rw [Handle.inclPair_discClass _ _ _ h1 h2 h3 gD]

theorem count_surjective (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (htr : B.transverse) (hℓ : 2 ≤ ℓ)
    (hH : relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∀ u : M → ℤ, ∃ v : M → ℤ, ∀ p ∈ B.lowerIndexCriticalPoints, ∑ q ∈ B.upperIndexCriticalPoints, B.count p q * v q = u p := by
  intro u
  have hℓ1 : 1 ≤ ℓ := by omega
  obtain ⟨m, hβm, hmb, hm⟩ : ∃ m : ℝ, B.β < m ∧ m ≤ b ∧
      ∀ x ∈ B.crit, B.β < f x → m ≤ f x := by
    have hSne : (insert b ((B.crit.filter (fun x => B.β < f x)).image f)).Nonempty :=
      ⟨b, Finset.mem_insert_self _ _⟩
    refine ⟨(insert b ((B.crit.filter (fun x => B.β < f x)).image f)).min' hSne, ?_,
      Finset.min'_le _ b (Finset.mem_insert_self _ _), fun x hx hxβ => Finset.min'_le _ (f x)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hx, hxβ⟩)))⟩
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact B.hβb
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 hx).2
  obtain ⟨ε₁, hε₁pos, hε₁ε, hε₁α, hε₁m⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ B.ε ∧
      ε₁ ≤ (B.α - a) / 2 ∧ ε₁ ≤ (m - B.β) / 4 :=
    ⟨min B.ε (min ((B.α - a) / 2) ((m - B.β) / 4)),
      lt_min B.hε (lt_min (by linarith [B.haα]) (by linarith)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨B', hcrit, hα, hβ, hc, hε', -, -, -, -, -, -, hPQ⟩ :=
    exists_shrink hf B hε₁pos hε₁ε (ρ := 8 * ε₁ + 1) (by linarith) (by nlinarith)
  have hP' : B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints := B.lowerIndexCriticalPoints_eq_of_crit_eq hcrit
  have hQ' : B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints := B.upperIndexCriticalPoints_eq_of_crit_eq hcrit
  suffices hmain : ∃ v : M → ℤ, ∀ p ∈ B'.lowerIndexCriticalPoints, ∑ q ∈ B'.upperIndexCriticalPoints, B'.count p q * v q = u p by
    obtain ⟨v, hv⟩ := hmain
    refine ⟨v, fun p hp => ?_⟩
    have hp' : p ∈ B'.lowerIndexCriticalPoints := by rw [hP']; exact hp
    rw [← hv p hp', hQ']
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(hPQ p hp q hq).2.1]
  have htr' : B'.transverse := by
    intro p hp q hq
    rw [hP'] at hp
    rw [hQ'] at hq
    exact (hPQ p hp q hq).1.2 (htr p hp q hq)
  have hm' : ∀ x ∈ B'.crit, B'.β < f x → m ≤ f x := by
    intro x hx h
    rw [hcrit] at hx
    rw [hβ] at h
    exact hm x hx h
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = (B.β + m) / 2 := ⟨_, rfl⟩
  have hε'1 := B'.hε
  have hαc := B'.hαc
  have hcβ := B'.hcβ
  have hβb := B'.hβb
  have haα := B'.haα
  have hc'b : c' ≤ b := by rw [hc'def]; linarith
  have hβc' : B'.β + B'.ε < c' := by rw [hc'def, hβ, hε']; linarith
  have hc'm : c' < m - B'.ε := by rw [hc'def, hε']; linarith
  have haα' : a < B'.α - B'.ε := by rw [hα, hε']; linarith [B.haα]
  have hac : a ≤ B'.c := by linarith
  have hcb : B'.c ≤ b := by linarith
  have hcc'le : B'.c ≤ c' := by linarith
  have hac' : a ≤ c' := by linarith
  have hεr : ∀ x hx, (B'.D.chart x hx).r₀ ^ 2 < 2 * B'.ε ∧ 8 * B'.ε < B'.D.rm x hx ^ 2 :=
    fun x hx => ⟨B'.hr₀ x hx, B'.hrm x hx⟩
  have hkidx : ∀ x (hx : x ∈ B'.crit), (B'.D.chart x hx).k = morseIndex I f x :=
    fun x hx => (B'.D.chart x hx).hkidx.symm
  have hval : ∀ x ∈ B'.crit, (morseIndex I f x = ℓ ∧ f x = B'.α) ∨
      (morseIndex I f x = ℓ + 1 ∧ f x = B'.β) ∨ (ℓ + 1 < morseIndex I f x ∧ B'.β < f x) := by
    intro x hx
    have h1 := B'.hmin x hx
    by_cases h2 : morseIndex I f x = ℓ
    · exact Or.inl ⟨h2, B'.hP x hx h2⟩
    by_cases h3 : morseIndex I f x = ℓ + 1
    · exact Or.inr (Or.inl ⟨h3, B'.hQ x hx h3⟩)
    have h4 : ℓ + 1 < morseIndex I f x := by omega
    exact Or.inr (Or.inr ⟨h4, B'.hhigh x hx h4⟩)
  have hsb : ∀ y x (hx : x ∈ B'.crit), y ∈ B'.D.smallBall x hx → |f y - f x| < B'.ε := by
    intro y x hx hy
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall (D := B'.D) hx hy
    have h2 := B'.hr₀ x hx
    linarith
  have hge : ∀ x ∈ B'.crit, B'.α ≤ f x := by
    intro x hx
    rcases hval x hx with h | h | h <;> linarith [h.2]
  have hfilP : B'.crit.filter (fun x => f x = B'.α) = B'.lowerIndexCriticalPoints := by
    ext x
    rw [Finset.mem_filter, B'.mem_lowerIndexCriticalPoints]
    constructor
    · rintro ⟨hx, hfx⟩
      refine ⟨hx, ?_⟩
      rcases hval x hx with h | h | h
      · exact h.1
      · exfalso; linarith [h.2]
      · exfalso; linarith [h.2]
    · rintro ⟨hx, hi⟩
      exact ⟨hx, B'.hP x hx hi⟩
  have hfilQ : B'.crit.filter (fun x => f x = B'.β) = B'.upperIndexCriticalPoints := by
    ext x
    rw [Finset.mem_filter, B'.mem_upperIndexCriticalPoints]
    constructor
    · rintro ⟨hx, hfx⟩
      refine ⟨hx, ?_⟩
      rcases hval x hx with h | h | h
      · exfalso; linarith [h.2]
      · exact h.1
      · exfalso; linarith [h.2]
    · rintro ⟨hx, hi⟩
      exact ⟨hx, B'.hQ x hx hi⟩
  obtain ⟨gD', hgD', hgS⟩ := Handle.exists_disc_generator.{u_2} ℓ hℓ1
  have hgenD : ∃ gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift.{u_2} (Disk ℓ)))
      (ULift.down ⁻¹' diskSphere ℓ) ℓ, Handle.isGen gD := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨g, hg, -⟩ := Handle.exists_disc_generator.{u_2} k (by omega)
    exact ⟨g, hg⟩
  obtain ⟨gD, hgD⟩ := hgenD
  have hPslab := GradientLikeStrip.slab_discClass_basis hf.smooth B'.D B'.hcrit B'.hε hεr
    (t := a) (τ := B'.α) (t' := B'.c) le_rfl haα' hαc hcb
    (by
      intro x hx hfx
      rcases hval x hx with h | h | h
      · exact h.2
      · exfalso; linarith [h.2, hfx.2]
      · exfalso; linarith [h.2, hfx.2])
    (by
      intro y hy w hw hmem
      rcases hy with hy | hy
      · have h1 := hsb y w hw hmem
        have h2 := hge w hw
        rw [abs_lt] at h1
        linarith [hy.2, h1.1]
      · exact B'.hlev y ⟨hy.1, hy.2.trans (by linarith)⟩ w hw hmem)
    (μ := ℓ)
    (by
      intro x hx hfx
      rw [hkidx]
      rcases hval x hx with h | h | h
      · exact h.1
      · exfalso; linarith [h.2]
      · exfalso; linarith [h.2])
    hℓ1 gD hgD
  rw [Set.Icc_self a, hfilP] at hPslab
  have hQslab := GradientLikeStrip.slab_discClass_basis hf.smooth B'.D B'.hcrit B'.hε hεr
    (t := B'.c) (τ := B'.β) (t' := c') hac hcβ hβc' hc'b
    (by
      intro x hx hfx
      rcases hval x hx with h | h | h
      · exfalso; linarith [h.2, hfx.1]
      · exact h.2
      · exfalso; linarith [hm' x hx h.2, hfx.2])
    (by
      intro y hy w hw hmem
      have h1 := hsb y w hw hmem
      rw [abs_lt] at h1
      rcases hy with hy | hy
      · exact B'.hlev y ⟨le_trans (by linarith) hy.1, hy.2⟩ w hw hmem
      · rcases hval w hw with h | h | h
        · linarith [h.2, hy.1, h1.2]
        · linarith [h.2, hy.1, h1.2]
        · linarith [hm' w hw h.2, hy.2, h1.1])
    (μ := ℓ + 1)
    (by
      intro x hx hfx
      rw [hkidx]
      rcases hval x hx with h | h | h
      · exfalso; linarith [h.2]
      · exact h.1
      · exfalso; linarith [h.2])
    (by omega) gD' hgD'
  rw [hfilQ] at hQslab
  have hVc' : f ⁻¹' {a} ⊆ f ⁻¹' Icc a c' := by
    intro x hx
    rw [mem_preimage, mem_singleton_iff] at hx
    exact ⟨hx.ge, by rw [hx]; exact hac'⟩
  have hc'W : f ⁻¹' Icc a c' ⊆ f ⁻¹' Icc a b := fun x hx => ⟨hx.1, hx.2.trans hc'b⟩
  have hvan := GradientLikeStrip.hpair_vanishes_above hf B'.D B'.hcrit B'.hε hεr hac' hc'b
    (by
      intro x hx hfx
      rcases hval x hx with h | h | h
      · linarith [h.2]
      · linarith [h.2]
      · linarith [hm' x hx h.2])
    (j := ℓ + 1)
    (by
      intro x hx hfx
      rcases hval x hx with h | h | h
      · exfalso; linarith [h.2]
      · exfalso; linarith [h.2]
      · exact h.1)
  have hzero' : ∀ x : Handle.relativeHomologyPair (f ⁻¹' Icc a c') (f ⁻¹' {a}) ℓ, x = 0 := by
    intro x
    have h0 : Handle.inclPair hc'W (subset_refl (f ⁻¹' {a})) ℓ x = 0 :=
      (ModuleCat.subsingleton_of_isZero (hH ℓ)).elim _ _
    obtain ⟨z, hz⟩ := Handle.tripleBoundary_exact hVc' hc'W ℓ x h0
    have hz0 : z = 0 := (ModuleCat.subsingleton_of_isZero hvan).elim _ _
    rw [← hz, hz0, map_zero]
  obtain ⟨s, -, hs⟩ := sphereClass_eq_sum hf B' htr' hℓ1 haα' (Handle.boundaryGen gD') hgS gD hgD
  have hbd : ∀ q ∈ B'.upperIndexCriticalPoints, Handle.tripleBoundary (f ⁻¹' {a}) (f ⁻¹' Icc a B'.c) (f ⁻¹' Icc a c') ℓ
      (Handle.discClass (f ⁻¹' Icc a c') (f ⁻¹' Icc a B'.c)
        (B'.D.leftDiscMap q (ℓ + 1) B'.ε B'.c) gD') =
      ∑ p ∈ B'.lowerIndexCriticalPoints, (s * B'.count p q) • Handle.discClass (f ⁻¹' Icc a B'.c) (f ⁻¹' {a})
        (B'.D.leftDiscMap p ℓ B'.ε a) gD := by
    intro q hq
    have hqc := (B'.mem_upperIndexCriticalPoints.1 hq).1
    have hfq : f q = B'.β := B'.hQ q hqc (B'.mem_upperIndexCriticalPoints.1 hq).2
    rw [GradientLikeStrip.tripleBoundary_leftDisc hf.smooth B'.D hqc (μ := ℓ)
      (by rw [hkidx]; exact (B'.mem_upperIndexCriticalPoints.1 hq).2) B'.hε (B'.hrm q hqc) hac
      (by rw [hfq]; exact hcβ) (by rw [hfq]; linarith) hc'b
      (fun y hy => B'.hlev y ⟨le_trans (by linarith) hy.1, by rw [hfq] at hy; exact hy.2⟩) gD']
    exact hs q hq
  have hVc : f ⁻¹' {a} ⊆ f ⁻¹' Icc a B'.c := by
    intro x hx
    rw [mem_preimage, mem_singleton_iff] at hx
    exact ⟨hx.ge, by rw [hx]; exact hac⟩
  have hcc' : f ⁻¹' Icc a B'.c ⊆ f ⁻¹' Icc a c' := fun x hx => ⟨hx.1, hx.2.trans hcc'le⟩
  obtain ⟨z, hz⟩ := Handle.tripleBoundary_exact hVc hcc' ℓ
    (∑ p ∈ B'.lowerIndexCriticalPoints, u p • Handle.discClass (f ⁻¹' Icc a B'.c) (f ⁻¹' {a})
      (B'.D.leftDiscMap p ℓ B'.ε a) gD) (hzero' _)
  obtain ⟨v, hv⟩ := hQslab.1 z
  have hy : ∑ p ∈ B'.lowerIndexCriticalPoints, u p • Handle.discClass (f ⁻¹' Icc a B'.c) (f ⁻¹' {a})
      (B'.D.leftDiscMap p ℓ B'.ε a) gD =
      ∑ p ∈ B'.lowerIndexCriticalPoints, (∑ q ∈ B'.upperIndexCriticalPoints, v q * (s * B'.count p q)) • Handle.discClass
        (f ⁻¹' Icc a B'.c) (f ⁻¹' {a}) (B'.D.leftDiscMap p ℓ B'.ε a) gD := by
    rw [← hz, hv, map_sum]
    rw [Finset.sum_congr rfl fun q hq => by rw [map_zsmul, hbd q hq]]
    have hsz : ∀ (G : Type u_2) [AddCommGroup G] (t : Finset M) (g : M → ℤ) (x : G),
        (∑ i ∈ t, g i) • x = ∑ i ∈ t, g i • x := fun G _ t g x => Finset.sum_smul
    rw [Finset.sum_congr rfl fun q _ => (Finset.sum_zsmul _ _ _).symm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ =>
      ((hsz _ _ _ _).trans (Finset.sum_congr rfl fun q _ => mul_zsmul _ _ _)).symm
  refine ⟨fun q => s * v q, fun p hp => ?_⟩
  have hind : u p - ∑ q ∈ B'.upperIndexCriticalPoints, v q * (s * B'.count p q) = 0 :=
    hPslab.2 (fun p => u p - ∑ q ∈ B'.upperIndexCriticalPoints, v q * (s * B'.count p q)) (by
      simp only [sub_zsmul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [hy, add_neg_cancel]) p hp
  have hsum : ∑ q ∈ B'.upperIndexCriticalPoints, B'.count p q * (s * v q) =
      ∑ q ∈ B'.upperIndexCriticalPoints, v q * (s * B'.count p q) := Finset.sum_congr rfl fun q _ => by ring
  rw [hsum]
  linarith

end BlockConfig

end

end DifferentialGeometry.Topology
