module

public import Mathlib.Topology.Algebra.Order.Floor
public import DifferentialGeometry.Topology.Morse.Handle.Partners.GeneralPosition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

section Circle

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_good_gradientLike [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hidx : ∀ x ∈ crit, 1 ≤ morseIndex I f x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : GradientLikeStrip I f a b crit, isFineAt D δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      (∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) ∧
      ∀ x hx, (D.chart x hx).k = 1 →
        (D.chart x hx).χ '' (D.chart x hx).leftModelSphere ε ⊆ D.bottom := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hab : a < b := hf.lt
  obtain ⟨D, ε, hε, r', hr', hr'ε, hsz, -, hA3⟩ :=
    GradientLikeStrip.exists_gradientLike_allPairs hf hsi hinj crit hcrit one_pos
  have hkidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q := by
    intro p hp q hq hlt
    have hp' := (hcrit p).1 hp
    have hq' := (hcrit q).1 hq
    exact hsi p q hp'.1 hq'.1 hp'.2 hq'.2
      (by rw [(D.chart p hp).hkidx, (D.chart q hq).hkidx]; exact hlt)
  have hk1 : ∀ p hp, 1 ≤ (D.chart p hp).k := fun p hp => by
    rw [← (D.chart p hp).hkidx]; exact hidx p hp
  have hDarms : ∀ q hq, (D.chart q hq).k = 1 → ∀ y ∈ (D.chart q hq).leftModelSphere ε,
      (D.chart q hq).χ y ∈ D.bottom := by
    intro q hq hkq y hy
    have h8 : 8 * ε < D.rm q hq ^ 2 := by linarith [(hsz q hq).2.2.1]
    have hfw : f ((D.chart q hq).χ y) = f q - ε :=
      GradientLikeStrip.f_chart_of_mem_leftModelSphere' hq h8 hy
    have hyrm := GradientLikeStrip.morseNorm_lt_rm_of_mem_leftModelSphere hq h8 hy
    have hwS : f ((D.chart q hq).χ y) ∈ Ioo a b :=
      D.inStrip q hq ⟨y, mem_ball_of_morseNorm_lt (hyrm.trans (D.rm_lt_R' q hq)), rfl⟩
    have havoid : ∀ t, 0 ≤ t → ∀ p hp, D.flow t ((D.chart q hq).χ y) ∉ D.smallBall p hp := by
      intro t ht p hp hmem
      have hlev := D.f_mem_Icc_of_mem_smallBall hmem
      have hft : f (D.flow t ((D.chart q hq).χ y)) ≤ f ((D.chart q hq).χ y) :=
        GradientLikeStrip.f_flow_le hfs _ ht
      have hr₀ := (hsz p hp).2.1
      have hfp : f p < f q := by linarith [hlev.1]
      rcases Nat.lt_or_ge (D.chart p hp).k 2 with hk | hk
      · have hkp : (D.chart p hp).k = 1 := by have := hk1 p hp; omega
        exact hA3 p hp q hq hkp hkq hfp _ ⟨y, hy, rfl⟩ t ht
          (image_mono (fun z (hz : morseNorm n z < _) => hz.trans (hsz p hp).2.2.2) hmem)
      · have := hkidx q hq p hp (by omega)
        linarith
    have hT : 0 ≤ f ((D.chart q hq).χ y) - a := by linarith [hwS.1]
    have hlev := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc hfs (D := D)
      (x := (D.chart q hq).χ y) (T := f ((D.chart q hq).χ y) - a) ⟨hwS.1.le, hwS.2.le⟩
      ⟨le_of_eq (by ring), by linarith [hwS.1]⟩
      (fun s hs p hp => havoid s (by rw [uIcc_of_le hT] at hs; exact hs.1) p hp)
      (f ((D.chart q hq).χ y) - a) (by rw [uIcc_of_le hT]; exact right_mem_Icc.2 hT)
    refine GradientLikeStrip.mem_bottom_of_flow_mem hT
      (GradientLikeStrip.mem_bottom_of_le hfs hab.le ?_)
    rw [hlev]; linarith
  have hcont : ∀ x (hx : x ∈ crit), ∃ η, 0 < η ∧ η ≤ (D.chart x hx).R' ∧
      (D.chart x hx).χ '' Metric.ball 0 η ⊆ f ⁻¹' Ioo (f x - δ) (f x + δ) := by
    intro x hx
    have hc : ContinuousAt (fun y => f ((D.chart x hx).χ y)) 0 :=
      hfs.continuous.continuousAt.comp ((D.chart x hx).χ.continuousOn.continuousAt
        ((D.chart x hx).χ.open_source.mem_nhds ((D.chart x hx).hball (D.chart x hx).zero_mem_ball)))
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hc δ hδ
    refine ⟨min η (D.chart x hx).R', lt_min hη (D.chart x hx).R'_pos, min_le_right _ _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : dist y 0 < η := lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _)
    have := hηc hy'
    simp only [(D.chart x hx).hχ0, Real.dist_eq, abs_lt] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  choose η hηpos hηR' hηfine using hcont
  set Rn : ∀ x ∈ crit, ℝ := fun x hx => min (η x hx / 2) (D.chart x hx).R with hRndef
  set rmn : ∀ x ∈ crit, ℝ := fun x hx => min (Rn x hx) (D.rm x hx) with hrmndef
  have hrmnpos : ∀ x hx, 0 < rmn x hx := fun x hx =>
    lt_min (lt_min (by linarith [hηpos x hx]) (D.chart x hx).R_pos) (D.rm_pos x hx)
  obtain ⟨m, hm, hmT⟩ := exists_pos_le_forall_finset crit.attach
    (fun x => rmn x.1 x.2) fun x _ => hrmnpos x.1 x.2
  have hmle : ∀ x hx, m ≤ rmn x hx := fun x hx => hmT ⟨x, hx⟩ (Finset.mem_attach _ _)
  obtain ⟨ρ₀, hρ₀, hρ₀T⟩ := exists_pos_le_forall_finset crit.attach
    (fun x => (D.chart x.1 x.2).r₀) fun x _ => (D.chart x.1 x.2).hr₀
  set ε' : ℝ := min (min ε (δ / 2)) (m ^ 2 / 16) with hε'def
  have hε'pos : 0 < ε' := lt_min (lt_min hε (by linarith)) (by positivity)
  have hε'ε : ε' ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε'δ : ε' < δ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hε'm : ε' ≤ m ^ 2 / 16 := min_le_right _ _
  set ρ : ℝ := min (min ρ₀ (m / 4)) (min 1 ε') with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hρ₀ (by linarith)) (lt_min one_pos hε'pos)
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρm : ρ ≤ m / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρε' : ρ ≤ ε' := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < 8 * ε' := by nlinarith
  have hle : ∀ p hp, ρ ≤ (D.chart p hp).r₀ := fun p hp =>
    hρρ₀.trans (hρ₀T ⟨p, hp⟩ (Finset.mem_attach _ _))
  obtain ⟨E, hE1, hE2, hE3, -, φ, hφc, ⟨mφ, Mφ, hmφ, hφb⟩, hEV⟩ :=
    exists_shrinkAll_factor hfs D hρpos hle
  have hbotDE : ∀ x ∈ D.bottom, x ∈ E.bottom := by
    rintro x ⟨t, ht, hlt⟩
    obtain ⟨σ, hσ, hσ0, hσs, hσf⟩ :=
      GradientLikeStrip.exists_reparam D E hφc hmφ hφb hEV x
    obtain ⟨s, rfl⟩ := hσs t
    refine ⟨s, ?_, by rw [hσf]; exact hlt⟩
    rw [← hσ.le_iff_le, hσ0]; exact ht
  have hEarms : ∀ q hq, (E.chart q hq).k = 1 → ∀ y ∈ (E.chart q hq).leftModelSphere ε',
      (E.chart q hq).χ y ∈ E.bottom := by
    intro q hq hkq y hy
    have hkqD : (D.chart q hq).k = 1 := by rw [← (hE1 q hq).2.1]; exact hkq
    have hrmE : 2 * ε < E.rm q hq ^ 2 := by rw [hE3]; linarith [(hsz q hq).2.2.1]
    obtain ⟨i, rfl⟩ : ∃ i, y = (E.chart q hq).armPt hkq ε' i := by
      rcases (E.chart q hq).eq_armPt_of_mem_leftModelSphere hkq hε'pos hy with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨t, ht, hteq⟩ :=
      GradientLikeStrip.exists_flow_armPt_eq hfs hq hkq hε'pos hε'ε hrmE i
    refine GradientLikeStrip.mem_bottom_of_flow_mem ht ?_
    rw [hteq]
    have hmem : (E.chart q hq).armPt hkq ε i ∈ (D.chart q hq).leftModelSphere ε := by
      rw [← GradientLikeStrip.leftModelSphere_eq (hE1 q hq).2.1]
      exact (E.chart q hq).armPt_mem_leftModelSphere hkq hε.le i
    rw [(hE1 q hq).1]
    exact hbotDE _ (hDarms q hq hkqD _ hmem)
  obtain ⟨D', hD'1, hD'2, hD'3⟩ := GradientLikeStrip.exists_restrict E le_rfl le_rfl crit
    (fun r hr => hr) (fun r hr hr' => absurd hr hr') Rn η rmn
    (fun r hr => by
      rw [hE2, (hE1 r hr).2.2.1]
      refine ⟨?_, min_le_right _ _⟩
      have h1 := hmle r hr
      have h2 : rmn r hr ≤ Rn r hr := min_le_left _ _
      linarith)
    (fun r hr => by
      rw [(hE1 r hr).2.2.2]
      exact ⟨lt_of_le_of_lt (min_le_left _ _) (by linarith [hηpos r hr]), hηR' r hr⟩)
    (fun r hr => by
      rw [hE2, hE3]
      exact ⟨by linarith [hmle r hr], min_le_right _ _, min_le_left _ _⟩)
    (fun r hr => by
      rw [(hE1 r hr).1]
      exact (image_mono (Metric.ball_subset_ball (hηR' r hr))).trans (D.inStrip r hr))
    (fun x _ hx => hx)
  have hbotED : ∀ x ∈ E.bottom, x ∈ D'.bottom := by
    rintro x ⟨t, ht, hlt⟩
    exact ⟨t, ht, by rw [GradientLikeStrip.flow_eq_of_V_eq E D' hD'3]; exact hlt⟩
  refine ⟨D', ?_, ε', hε'pos, hε'δ, ?_, ?_⟩
  · intro x hx
    rw [(hD'1 x hx).2.2.2.2, (hD'1 x hx).1, (hE1 x hx).1]
    exact hηfine x hx
  · intro x hx
    rw [(hD'1 x hx).2.2.1, hE2, hD'2]
    refine ⟨by nlinarith, ?_⟩
    have h1 := hmle x hx
    have h2 : m ^ 2 ≤ rmn x hx ^ 2 := pow_le_pow_left₀ hm.le h1 2
    nlinarith
  · intro x hx hk
    rintro _ ⟨y, hy, rfl⟩
    rw [GradientLikeStrip.leftModelSphere_eq (hD'1 x hx).2.1] at hy
    rw [(hD'1 x hx).1]
    exact hbotED _ (hEarms x hx (by rw [← (hD'1 x hx).2.1]; exact hk) y hy)

theorem exists_ascending_rightPt (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = 1) {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    (hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2) :
    ∃ y₀ ∈ (D.chart p hp).rightModelSphere ε,
      ∃ t, t ≤ 0 ∧ c₂ < f (D.flow t ((D.chart p hp).χ y₀)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hpab : f p ∈ Ioo a b := ((hcrit p).1 hp).1
  have hc : c₂ ∈ Ioo a b := ⟨by linarith [hpab.1], hc₂⟩
  have hrmpos := D.rm_pos p hp
  have hrmR := (D.hrm p hp).2
  have h2εR : 2 * ε ≤ (D.chart p hp).R ^ 2 := by nlinarith [hεp.2]
  obtain ⟨ι, hι, U, g, hU, hg, hTsub⟩ :=
    isThin_nonReaching_below hf D hcrit hc hcU (kdn := 2) hdn
  by_contra hne
  push Not at hne
  have hsub : ∀ y₀ ∈ (D.chart p hp).rightModelSphere ε,
      (D.chart p hp).χ y₀ ∈ {x | f x ∈ Icc a c₂ ∧ ∀ t, f (D.flow t x) ≠ c₂} := by
    intro y₀ hy₀
    have hfx : f ((D.chart p hp).χ y₀) = f p + ε :=
      (D.chart p hp).f_chart_of_mem_rightModelSphere h2εR hy₀
    refine ⟨⟨by rw [hfx]; linarith [hpab.1], by rw [hfx]; exact hpc.le⟩, ?_⟩
    intro t ht
    rcases le_or_gt t 0 with htn | htp
    · have hconst : ∀ s ∈ Iic t, f (D.flow s ((D.chart p hp).χ y₀)) = c₂ := fun s hs =>
        le_antisymm (hne y₀ hy₀ s (le_trans hs htn))
          (ht ▸ GradientLikeStrip.f_flow_antitone (D := D) hfs _ hs)
      have hd1 : HasDerivWithinAt (fun s => f (D.flow s ((D.chart p hp).χ y₀))) (-1) (Iic t) t := by
        have h := (GradientLikeStrip.hasDerivAt_f_flow (D := D) hfs
          ((D.chart p hp).χ y₀) t).hasDerivWithinAt (s := Iic t)
        rwa [D.dfV_eq_neg_one_of_level ⟨hc.1.le, hc.2.le⟩
          (fun q hq z hz => hcU q hq z (D.smallBall_subset_closedSmallBall q hq hz)) ht] at h
      have hd2 : HasDerivWithinAt (fun s => f (D.flow s ((D.chart p hp).χ y₀))) 0 (Iic t) t :=
        (hasDerivWithinAt_const t (Iic t) c₂).congr_of_mem (fun s hs => hconst s hs) (mem_Iic.2 le_rfl)
      have := (uniqueDiffWithinAt_Iic t).eq_deriv _ hd1 hd2
      norm_num at this
    · have := GradientLikeStrip.f_flow_le (D := D) hfs ((D.chart p hp).χ y₀) htp.le
      rw [ht, hfx] at this
      linarith
  let π : (Fin (m + 2) → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi fun j : Fin m =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 2) => ℝ) j.succ.succ
  let V : ι → Set (Fin 2 → ℝ) := fun i =>
    U i ∩ g i ⁻¹' ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')
  let F : ι → (Fin 2 → ℝ) → (Fin m → ℝ) := fun i u => π ((D.chart p hp).χ.symm (g i u))
  have hF : ∀ i, ∀ u ∈ V i, ContDiffAt ℝ 1 (F i) u := by
    intro i u hu
    have h1 : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) I 1 (g i) u :=
      (hg i).contMDiffAt ((hU i).mem_nhds hu.1)
    have h2 : ContMDiffAt I 𝓘(ℝ, Fin (m + 2) → ℝ) 1 (D.chart p hp).χ.symm (g i u) :=
      ((D.chart p hp).contMDiffAt_symm hu.2).of_le (by norm_num)
    have h3 := contMDiffAt_iff_contDiffAt.1 (h2.comp u h1)
    exact π.contDiff.contDiffAt.comp u h3
  have hdimF : ∀ i, dimH (F i '' V i) ≤ 2 := by
    intro i
    refine (dimH_image_le_of_locally_lipschitzOn fun u hu => ?_).trans ?_
    · obtain ⟨K, t, ht, hK⟩ := (hF i u hu).exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
    · refine (dimH_mono (subset_univ _)).trans ?_
      rw [Real.dimH_univ_eq_finrank, Module.finrank_fin_fun]
      norm_num
  have hcover : π '' (D.chart p hp).rightModelSphere ε ⊆ ⋃ i, F i '' V i := by
    rintro _ ⟨y₀, hy₀, rfl⟩
    have hyball : y₀ ∈ Metric.ball (0 : Fin (m + 2) → ℝ) (D.chart p hp).R' :=
      (D.chart p hp).mem_ball_of_le
        ((D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere h2εR hy₀)
    obtain ⟨i, u, hu, hgu⟩ := mem_iUnion.1 (hTsub (hsub y₀ hy₀))
    refine mem_iUnion.2 ⟨i, u, ⟨hu, ?_⟩, ?_⟩
    · change g i u ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'
      rw [hgu]
      exact ⟨y₀, hyball, rfl⟩
    · change π ((D.chart p hp).χ.symm (g i u)) = π y₀
      rw [hgu, (D.chart p hp).χ.left_inv ((D.chart p hp).hball hyball)]
  have hup : dimH (π '' (D.chart p hp).rightModelSphere ε) ≤ 2 :=
    (dimH_mono hcover).trans ((dimH_iUnion _).le.trans (iSup_le hdimF))
  have hneg : ∀ (k : ℕ) (hk : k ≤ m + 2), k = 1 → ∀ y : Fin (m + 2) → ℝ, y 0 = 0 →
      negPart hk y = 0 := by
    rintro k hk rfl y hy
    ext i
    fin_cases i
    simpa [DifferentialGeometry.Topology.Morse.CellAttachment.negPart, DifferentialGeometry.Topology.Morse.CellAttachment.negIdx] using hy
  have hopen : IsOpen {w : Fin m → ℝ | ∑ j, w j ^ 2 < 2 * ε} :=
    isOpen_lt (by fun_prop) continuous_const
  have hin : {w : Fin m → ℝ | ∑ j, w j ^ 2 < 2 * ε} ⊆ π '' (D.chart p hp).rightModelSphere ε := by
    intro w hw
    have hw' : (0 : ℝ) ≤ 2 * ε - ∑ j, w j ^ 2 := by
      have : ∑ j, w j ^ 2 < 2 * ε := hw
      linarith
    refine ⟨Fin.cons 0 (Fin.cons (Real.sqrt (2 * ε - ∑ j, w j ^ 2)) w), ⟨?_, ?_⟩, ?_⟩
    · exact hneg _ _ hkp _ (by simp)
    · have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk
        (Fin.cons 0 (Fin.cons (Real.sqrt (2 * ε - ∑ j, w j ^ 2)) w) : Fin (m + 2) → ℝ)
      rw [hneg _ _ hkp _ (by simp), norm_zero] at h1
      have h2 : morseNorm (m + 2)
          (Fin.cons 0 (Fin.cons (Real.sqrt (2 * ε - ∑ j, w j ^ 2)) w) : Fin (m + 2) → ℝ) ^ 2 =
          ∑ i, (Fin.cons 0 (Fin.cons (Real.sqrt (2 * ε - ∑ j, w j ^ 2)) w) :
            Fin (m + 2) → ℝ) i ^ 2 := by
        dsimp [morseNorm]
        simpa using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2
          (Fin.cons 0 (Fin.cons (Real.sqrt (2 * ε - ∑ j, w j ^ 2)) w) : Fin (m + 2) → ℝ)))
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h2
      simp only [Fin.cons_zero, Fin.cons_succ, Real.sq_sqrt hw'] at h2
      linarith
    · ext j
      simp [π]
  have hint : (interior (π '' (D.chart p hp).rightModelSphere ε)).Nonempty :=
    ⟨0, interior_mono hin (mem_interior_iff_mem_nhds.2 (hopen.mem_nhds (by
      simp only [mem_ofPred_eq, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact hε)))⟩
  rw [Real.dimH_of_nonempty_interior hint, Module.finrank_fin_fun] at hup
  have hm : (m : ENNReal) ≤ ((2 : ℕ) : ENNReal) := by exact_mod_cast hup
  have hm' : m ≤ 2 := by exact_mod_cast hm
  omega

theorem exists_arc_of_rightPt (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = 1) {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (harms : (D.chart p hp).χ '' (D.chart p hp).leftModelSphere ε ⊆ D.bottom)
    {y₀ : Fin n → ℝ} (hy₀ : y₀ ∈ (D.chart p hp).rightModelSphere ε)
    (hasc : ∃ t, t ≤ 0 ∧ c₂ < f (D.flow t ((D.chart p hp).χ y₀))) :
    ∃ y : ℝ → (Fin n → ℝ), ContDiff ℝ ∞ y ∧ InjOn y (Icc (-1) 1) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, deriv y s ≠ 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y s) < D.rm p hp ∧
        morseNormalForm (D.chart p hp).hk (f p) (y s) = f p + ε) ∧
      negPart (D.chart p hp).hk (y 0) = 0 ∧
      (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk (y s)) v 0 ∧ v ≠ 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, t ≤ 0 ∧ c₂ < f (D.flow t ((D.chart p hp).χ (y s)))) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D.chart p hp).χ (y s) ∈ D.bottom := by
  have _ := hcrit
  have _ := hpc
  have _ := hc₂
  have hfs := hf.smooth
  set d := D.chart p hp with hd
  have hk0 : 0 < d.k := by rw [hkp]; exact Nat.one_pos
  set e : EuclideanSpace ℝ (Fin d.k) := EuclideanSpace.single (⟨0, hk0⟩ : Fin d.k) (1 : ℝ)
    with he
  have he1 : ‖e‖ = 1 := by simp [he]
  have he0 : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he1
    exact zero_ne_one he1
  set E : Fin n → ℝ := DifferentialGeometry.Topology.Morse.CellAttachment.recombine d.hk e 0
    with hE
  have hnE : negPart d.hk E = e := ModelField.negPart_recombine d.hk e 0
  have hpE : posPart d.hk E = 0 := ModelField.posPart_recombine d.hk e 0
  set r := Real.sqrt (2 * ε) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
  have hv₀ : ‖posPart d.hk y₀‖ = r := by
    rw [hr, ← hy₀.2, Real.sqrt_sq (norm_nonneg _)]
  set Y : ℝ → Fin n → ℝ := fun x => Real.cosh x • y₀ + (r * Real.sinh x) • E with hY
  have hnY : ∀ x, negPart d.hk (Y x) = (r * Real.sinh x) • e := by
    intro x
    simp only [hY, ModelField.negPart_add, ModelField.negPart_smul, hy₀.1, hnE, smul_zero,
      zero_add]
  have hpY : ∀ x, posPart d.hk (Y x) = Real.cosh x • posPart d.hk y₀ := by
    intro x
    simp only [hY, ModelField.posPart_add, ModelField.posPart_smul, hpE, smul_zero, add_zero]
  have hnY2 : ∀ x, ‖negPart d.hk (Y x)‖ ^ 2 = 2 * ε * Real.sinh x ^ 2 := by
    intro x
    rw [hnY, norm_smul, he1, mul_one, Real.norm_eq_abs, sq_abs, mul_pow, hr2]
  have hpY2 : ∀ x, ‖posPart d.hk (Y x)‖ ^ 2 = 2 * ε * Real.cosh x ^ 2 := by
    intro x
    rw [hpY, norm_smul, hv₀, Real.norm_eq_abs, mul_pow, sq_abs, hr2, mul_comm]
  have hY0 : Y 0 = y₀ := by simp [hY]
  have hlevel : ∀ x, morseNormalForm d.hk (f p) (Y x) = f p + ε := by
    intro x
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hnY2, hpY2]
    have := Real.cosh_sq_sub_sinh_sq x
    linear_combination ε * this
  have hmn : ∀ x, morseNorm n (Y x) ^ 2 = 2 * ε * Real.sinh x ^ 2 + 2 * ε * Real.cosh x ^ 2 := by
    intro x
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      d.hk, hnY2, hpY2]
  have hrm0 := D.rm_pos p hp
  have hR : 3 * ε ≤ d.R ^ 2 := by
    have h2 : D.rm p hp ^ 2 ≤ d.R ^ 2 := pow_le_pow_left₀ hrm0.le (D.hrm p hp).2 2
    linarith [hεp.2]
  have hsub : D.leftThick p hp ε (f p - ε) 0 ⊆ D.bottom := by
    rw [GradientLikeStrip.leftThick_self_level]
    exact (image_mono (GradientLikeStrip.leftTube_zero_subset d hε)).trans harms
  obtain ⟨ρ, ⟨hρ0, -⟩, hρU⟩ := D.exists_leftThick_subset p hp hε le_rfl hr0 hr2.le hR
    (f p - ε) (D.isOpen_bottom hfs.continuous) hsub
  obtain ⟨t₀, ht₀, hc₂t⟩ := hasc
  have hy₀R : morseNorm n y₀ ≤ d.R := by
    have h1 := d.morseNorm_sq_of_mem_rightModelSphere hy₀
    have h2 : D.rm p hp ^ 2 ≤ d.R ^ 2 := pow_le_pow_left₀ hrm0.le (D.hrm p hp).2 2
    exact (pow_le_pow_iff_left₀ (ModelField.morseNorm_nonneg y₀) d.R_pos.le two_ne_zero).1
      (by linarith [hεp.2])
  have hYc : Continuous Y :=
    (Real.continuous_cosh.smul continuous_const).add
      ((continuous_const.mul Real.continuous_sinh).smul continuous_const)
  have hcontA : ContinuousAt (fun x => f (D.flow t₀ (d.χ (Y x)))) 0 := by
    have h1 : ContinuousAt d.χ (Y 0) := by
      rw [hY0]
      exact d.χ.continuousAt (d.hsrc y₀ hy₀R)
    exact hfs.continuous.continuousAt.comp
      ((D.continuous_flow t₀).continuousAt.comp (h1.comp hYc.continuousAt))
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), c₂ < f (D.flow t₀ (d.χ (Y x))) ∧
      2 * ε * Real.sinh x ^ 2 + 2 * ε * Real.cosh x ^ 2 < D.rm p hp ^ 2 ∧
      2 * ε + 2 * (2 * ε * Real.cosh x ^ 2) < D.rm p hp ^ 2 ∧
      4 * (2 * ε * Real.sinh x ^ 2 * (2 * ε * Real.cosh x ^ 2)) < ρ ^ 4 := by
    refine (continuousAt_const.eventually_lt hcontA ?_).and
      ((ContinuousAt.eventually_lt (by fun_prop) continuousAt_const ?_).and
        ((ContinuousAt.eventually_lt (by fun_prop) continuousAt_const ?_).and
          (ContinuousAt.eventually_lt (by fun_prop) continuousAt_const ?_)))
    · simpa [hY0] using hc₂t
    · simp only [Real.sinh_zero, Real.cosh_zero]
      linarith [hεp.2]
    · simp only [Real.cosh_zero]
      linarith [hεp.2]
    · have : (0 : ℝ) < ρ ^ 4 := by positivity
      simpa using this
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  set s₀ := δ / 2 with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  have hP : ∀ s ∈ Icc (-1 : ℝ) 1, c₂ < f (D.flow t₀ (d.χ (Y (s * s₀)))) ∧
      2 * ε * Real.sinh (s * s₀) ^ 2 + 2 * ε * Real.cosh (s * s₀) ^ 2 < D.rm p hp ^ 2 ∧
      2 * ε + 2 * (2 * ε * Real.cosh (s * s₀) ^ 2) < D.rm p hp ^ 2 ∧
      4 * (2 * ε * Real.sinh (s * s₀) ^ 2 * (2 * ε * Real.cosh (s * s₀) ^ 2)) < ρ ^ 4 := by
    intro s hs
    apply hδP
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hs₀0]
    have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    have : |s| * s₀ ≤ s₀ := by nlinarith
    linarith
  have hm : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s * s₀) s₀ s := fun s => by
    simpa using (hasDerivAt_id s).mul_const s₀
  refine ⟨fun s => Y (s * s₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun s : ℝ => s * s₀) := contDiff_id.mul contDiff_const
    exact ((Real.contDiff_cosh.comp h1).smul contDiff_const).add
      ((contDiff_const.mul (Real.contDiff_sinh.comp h1)).smul contDiff_const)
  · intro s _ s' _ h
    have h1 := congrArg (negPart d.hk) h
    simp only [hnY] at h1
    have h2 := smul_left_injective ℝ he0 h1
    have h3 := mul_left_cancel₀ hr0.ne' h2
    exact mul_right_cancel₀ hs₀0.ne' (Real.sinh_injective h3)
  · intro s _
    have hd' : HasDerivAt (fun s => Y (s * s₀))
        ((Real.sinh (s * s₀) * s₀) • y₀ + (r * (Real.cosh (s * s₀) * s₀)) • E) s := by
      have h1 := ((Real.hasDerivAt_cosh (s * s₀)).comp s (hm s)).smul_const y₀
      have h2 := (((Real.hasDerivAt_sinh (s * s₀)).comp s (hm s)).const_mul r).smul_const E
      exact h1.add h2
    rw [hd'.deriv]
    intro h0
    have h1 := congrArg (negPart d.hk) h0
    have hz : negPart d.hk (0 : Fin n → ℝ) = 0 := (ModelField.negPartL d.hk).map_zero
    rw [ModelField.negPart_add, ModelField.negPart_smul, ModelField.negPart_smul, hy₀.1, hnE,
      smul_zero, zero_add, hz] at h1
    exact smul_ne_zero (mul_ne_zero hr0.ne' (mul_ne_zero (Real.cosh_pos _).ne' hs₀0.ne')) he0 h1
  · intro s hs
    refine ⟨?_, hlevel _⟩
    have h1 := (hP s hs).2.1
    rw [← hmn] at h1
    exact lt_of_pow_lt_pow_left₀ 2 hrm0.le h1
  · simp only [zero_mul]
    rw [hY0]
    exact hy₀.1
  · have hJ : (fun s => ModelField.scaledNegativePart d.hk (Y (s * s₀))) =
        fun s => (2 * ε * (Real.cosh (s * s₀) * Real.sinh (s * s₀))) • e := by
      funext s
      rw [ModelField.scaledNegativePart, hnY, hpY, norm_smul, hv₀, Real.norm_eq_abs,
        abs_of_pos (Real.cosh_pos _), smul_smul, ← hr2]
      congr 1
      ring
    have hg := ((((Real.hasDerivAt_cosh (0 * s₀)).comp 0 (hm 0)).mul
      ((Real.hasDerivAt_sinh (0 * s₀)).comp 0 (hm 0))).const_mul (2 * ε)).smul_const e
    simp only [zero_mul, Real.sinh_zero, Real.cosh_zero] at hg
    refine ⟨(2 * ε * s₀) • e, ?_, ?_⟩
    · rw [hJ]
      convert hg using 1
      · congr 1
      · simp
    · exact smul_ne_zero (by positivity) he0
  · intro s hs
    exact ⟨t₀, ht₀, (hP s hs).1⟩
  · intro s hs hs0
    have hx0 : s * s₀ ≠ 0 := mul_ne_zero hs0 hs₀0.ne'
    have hu : negPart d.hk (Y (s * s₀)) ≠ 0 := by
      rw [hnY]
      exact smul_ne_zero (mul_ne_zero hr0.ne' (Real.sinh_eq_zero.not.2 hx0)) he0
    have hball : 2 * ε + 2 * ‖posPart d.hk (Y (s * s₀))‖ ^ 2 < D.rm p hp ^ 2 := by
      rw [hpY2]; exact (hP s hs).2.2.1
    have hlev : f p - ε ≤ morseNormalForm d.hk (f p) (Y (s * s₀)) := by
      rw [hlevel]; linarith
    have hprod : 4 * (‖negPart d.hk (Y (s * s₀))‖ ^ 2 * ‖posPart d.hk (Y (s * s₀))‖ ^ 2) ≤
        ρ ^ 4 := by
      rw [hnY2, hpY2]; exact (hP s hs).2.2.2.le
    obtain ⟨t, ht0, -, -, hmem⟩ :=
      GradientLikeStrip.exists_exit_mem_leftTube hfs hp hε hball hu hlev hprod
    refine GradientLikeStrip.mem_bottom_of_flow_mem ht0 (hρU ?_)
    rw [GradientLikeStrip.leftThick_self_level]
    exact hmem

theorem exists_arc (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = 1) {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    (hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2)
    (harms : (D.chart p hp).χ '' (D.chart p hp).leftModelSphere ε ⊆ D.bottom) :
    ∃ y : ℝ → (Fin n → ℝ), ContDiff ℝ ∞ y ∧ InjOn y (Icc (-1) 1) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, deriv y s ≠ 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y s) < D.rm p hp ∧
        morseNormalForm (D.chart p hp).hk (f p) (y s) = f p + ε) ∧
      negPart (D.chart p hp).hk (y 0) = 0 ∧
      (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk (y s)) v 0 ∧ v ≠ 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, t ≤ 0 ∧ c₂ < f (D.flow t ((D.chart p hp).χ (y s)))) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D.chart p hp).χ (y s) ∈ D.bottom := by
  obtain ⟨y₀, hy₀, hasc⟩ :=
    exists_ascending_rightPt h5 hf D hcrit hp hkp hε hεp hpc hc₂ hcU hdn
  exact exists_arc_of_rightPt hf D hcrit hp hkp hε hεp hpc hc₂ harms hy₀ hasc

theorem exists_loop_through_arc (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c₂ : ℝ} (hc : c₂ ∈ Ioo a b)
    (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    (hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2) (hV₀ : ConnectedSpace (f ⁻¹' {a}))
    {A : ℝ → M} (hA : ContinuousOn A (Icc (-1) 1)) (hAc : ∀ s ∈ Icc (-1 : ℝ) 1, f (A s) = c₂)
    (hA₁ : A 1 ∈ D.bottom) (hA₂ : A (-1) ∈ D.bottom) :
    ∃ γ₀ : ℝ → M, Continuous γ₀ ∧ Periodic γ₀ 1 ∧ (∀ t, f (γ₀ t) = c₂) ∧
      (∀ t ∈ Icc (-(1 / 8) : ℝ) (1 / 8), γ₀ t = A (8 * t)) ∧
      ∀ t ∈ Icc (1 / 8 : ℝ) (7 / 8), γ₀ t ∈ D.bottom := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hab : a < b := hf.lt
  obtain ⟨⟨U, hUo, hUeq⟩, r, hrc, hrprop, -⟩ := exists_levelRetraction hf D hc hcU
  set R : Set M := {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c₂} with hR
  set Z : Set M := f ⁻¹' {a} \ U with hZ
  have hZc : IsClosed Z := (isClosed_singleton.preimage hfc).inter hUo.isClosed_compl
  have hZsub : Z ⊆ {x | f x ∈ Icc a c₂ ∧ ∀ t, f (D.flow t x) ≠ c₂} := by
    rintro x ⟨hxa, hxU⟩
    rw [mem_preimage, mem_singleton_iff] at hxa
    refine ⟨⟨hxa.ge, hxa.le.trans hc.1.le⟩, fun t ht => hxU ?_⟩
    have hxR : x ∈ R := ⟨⟨hxa.ge, hxa.le.trans hab.le⟩, t, ht⟩
    rw [hUeq] at hxR
    exact hxR.1
  have hthin : isThin I 2 Z := by
    obtain ⟨ι, hι, U', g, h1, h2, h3⟩ := isThin_nonReaching_below hf D hcrit hc hcU hdn
    exact ⟨ι, hι, U', g, h1, h2, hZsub.trans h3⟩
  have hpc : IsPathConnected (f ⁻¹' {a} \ Z) :=
    isPathConnected_level_diff_thin hfs (fun x hx => hf.regular x (Or.inl hx))
      (isConnected_iff_connectedSpace.2 hV₀) hZc hthin (by omega)
  have hcU' : ∀ y, f y = c₂ → dfV I f D.V y = -1 := fun y hy =>
    D.dfV_eq_neg_one_of_level ⟨hc.1.le, hc.2.le⟩
      (fun p hp z hz => hcU p hp z (D.smallBall_subset_closedSmallBall p hp hz)) hy
  have hdesc : ∀ x, f x = c₂ → x ∈ D.bottom →
      ∃ s, f (D.flow s x) = a ∧ D.flow s x ∈ f ⁻¹' {a} \ Z ∧ r (D.flow s x) = x := by
    intro x hx hxb
    obtain ⟨t, ht, hlt⟩ := hxb
    have hcont : ContinuousOn (fun s => f (D.flow s x)) (Icc 0 t) :=
      (hfc.comp (D.continuous_flow_curve x)).continuousOn
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc' ht hcont
      ⟨hlt.le, by simp only [GradientLikeStrip.flow_zero, hx]; exact hc.1.le⟩
    simp only at hs
    have hreach : ∃ t, f (D.flow t (D.flow s x)) = c₂ :=
      ⟨-s, by rw [GradientLikeStrip.flow_neg_flow, hx]⟩
    have hmemR : D.flow s x ∈ R := ⟨⟨hs.ge, hs.le.trans hab.le⟩, hreach⟩
    refine ⟨s, hs, ⟨hs, fun hZ' => hZ'.2 ?_⟩, ?_⟩
    · rw [hUeq] at hmemR
      exact hmemR.1
    · obtain ⟨hr1, t', ht'⟩ := hrprop _ hmemR.1 hmemR.2
      have h1 : f (D.flow t' (D.flow s x)) = c₂ := ht' ▸ hr1
      have h2 : f (D.flow (-s) (D.flow s x)) = c₂ := by
        rw [GradientLikeStrip.flow_neg_flow, hx]
      have := GradientLikeStrip.flow_level_unique hfs hcU' h1 h2
      rw [ht', this, GradientLikeStrip.flow_neg_flow]
  obtain ⟨s₁, -, hy₁, hr₁⟩ := hdesc (A 1) (hAc 1 ⟨by norm_num, le_rfl⟩) hA₁
  obtain ⟨s₂, -, hy₂, hr₂⟩ := hdesc (A (-1)) (hAc (-1) ⟨le_rfl, by norm_num⟩) hA₂
  have hjoin := hpc.joinedIn _ hy₁ _ hy₂
  set P := hjoin.somePath with hP
  have hPmem : ∀ v, P.extend v ∈ f ⁻¹' {a} \ Z := by
    intro v
    have : P.extend v ∈ range P := by rw [← Path.extend_range]; exact mem_range_self v
    obtain ⟨u, hu⟩ := this
    rw [← hu]
    exact hjoin.somePath_mem u
  have hPR : ∀ v, P.extend v ∈ R := by
    intro v
    obtain ⟨hva, hvZ⟩ := hPmem v
    rw [mem_preimage, mem_singleton_iff] at hva
    have hvU : P.extend v ∈ U := by
      by_contra hcon
      exact hvZ ⟨hva, hcon⟩
    have : P.extend v ∈ U ∩ f ⁻¹' Icc a b := ⟨hvU, ⟨hva.ge, hva.le.trans hab.le⟩⟩
    rw [← hUeq] at this
    exact this
  set Q : ℝ → M := fun v => r (P.extend v) with hQ
  have hQc : Continuous Q := hrc.comp_continuous P.continuous_extend hPR
  have hQlev : ∀ v, f (Q v) = c₂ := fun v => (hrprop _ (hPR v).1 (hPR v).2).1
  have hQbot : ∀ v, Q v ∈ D.bottom := by
    intro v
    obtain ⟨t, ht⟩ := (hrprop _ (hPR v).1 (hPR v).2).2
    simp only [hQ]
    rw [ht, GradientLikeStrip.flow_mem_bottom_iff hfs]
    have hva := (hPmem v).1
    rw [mem_preimage, mem_singleton_iff] at hva
    exact GradientLikeStrip.mem_bottom_of_le hfs hab.le hva.le
  have hQ0 : Q 0 = A 1 := by simp only [hQ, Path.extend_zero]; exact hr₁
  have hQ1 : Q 1 = A (-1) := by simp only [hQ, Path.extend_one]; exact hr₂
  set L : ℝ → M := fun u => if u ≤ 1 / 4 then A (8 * u - 1) else Q ((4 * u - 1) / 3) with hL
  have hLc : ContinuousOn L (Icc 0 1) := by
    have hsplit : Icc (0 : ℝ) 1 = Icc 0 (1 / 4) ∪ Icc (1 / 4) 1 := by
      rw [Icc_union_Icc_eq_Icc] <;> norm_num
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · have h1 : ContinuousOn (fun u : ℝ => A (8 * u - 1)) (Icc 0 (1 / 4)) := by
        refine hA.comp (Continuous.continuousOn (by fun_prop)) ?_
        intro u hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      refine h1.congr fun u hu => ?_
      simp only [hL, hu.2, ↓reduceIte]
    · have h1 : ContinuousOn (fun u : ℝ => Q ((4 * u - 1) / 3)) (Icc (1 / 4) 1) :=
        (hQc.comp (by fun_prop)).continuousOn
      refine h1.congr fun u hu => ?_
      simp only [hL]
      split_ifs with h
      · have : u = 1 / 4 := le_antisymm h hu.1
        subst this
        norm_num
        rw [hQ0]
      · rfl
  have hL01 : L 0 = L 1 := by
    simp only [hL]
    norm_num
    rw [hQ1]
  refine ⟨fun t => L (Int.fract (t + 1 / 8)), ?_, ?_, ?_, ?_, ?_⟩
  · have := ContinuousOn.comp_fract (f := fun (_ : ℝ) u => L u) (s := fun t : ℝ => t + 1 / 8)
      (hLc.comp continuous_snd.continuousOn (fun z hz => hz.2)) (by fun_prop) (fun _ => hL01)
    exact this
  · intro t
    simp only
    rw [show t + 1 + 1 / 8 = (t + 1 / 8) + 1 by ring, Int.fract_add_one]
  · intro t
    have h0 := Int.fract_nonneg (t + 1 / 8)
    have h1 := Int.fract_lt_one (t + 1 / 8)
    simp only [hL]
    split_ifs with h
    · exact hAc _ ⟨by linarith, by linarith⟩
    · exact hQlev _
  · intro t ht
    have hfr : Int.fract (t + 1 / 8) = t + 1 / 8 :=
      Int.fract_eq_self.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [hL, hfr]
    have hle : t + 1 / 8 ≤ 1 / 4 := by linarith [ht.2]
    simp only [hle, ↓reduceIte]
    congr 1
    ring
  · intro t ht
    simp only [hL]
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      have hfr : Int.fract ((7 / 8 : ℝ) + 1 / 8) = 0 := by norm_num
      rw [hfr]
      norm_num
      exact hA₂
    · have hfr : Int.fract (t + 1 / 8) = t + 1 / 8 :=
        Int.fract_eq_self.2 ⟨by linarith [ht.1], by linarith⟩
      rw [hfr]
      split_ifs with h'
      · have : t = 1 / 8 := by linarith [ht.1]
        subst this
        norm_num
        exact hA₁
      · exact hQbot _

theorem meetsRightOnce_of_arc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) {ε c : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε ≤ c)
    (hcb : c ≤ b) {γ : ℝ → M} (hper : Periodic γ 1) (hlev : ∀ t, f (γ t) = c)
    (hfree : ∀ t, descendsFreely D (c - (f p + ε)) (γ t)) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    {y : ℝ → (Fin n → ℝ)} (hy : ∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y s) < D.rm p hp)
    (hy0 : negPart (D.chart p hp).hk (y 0) = 0)
    (hJ : ∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk (y s)) v 0 ∧ v ≠ 0)
    (harc : ∀ t ∈ Icc (-δ) δ, D.flow (c - (f p + ε)) (γ t) = (D.chart p hp).χ (y (t / δ)))
    (hbot : ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D.chart p hp).χ (y s) ∈ D.bottom)
    (hrest : ∀ t ∈ Icc δ (1 - δ), γ t ∈ D.bottom) :
    meetsRightOnce D p hp ε c γ := by
  have _ := hδ'
  have hT : 0 ≤ c - (f p + ε) := by linarith
  have hfp := D.f_mem_Ioo p hp
  have hrmR := (D.hrm p hp).2
  have hinv : ∀ z : Fin n → ℝ, morseNorm n z ≤ (D.chart p hp).R →
      (D.chart p hp).χ.symm ((D.chart p hp).χ z) = z :=
    fun z hz => (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc z hz)
  have hγ0 : D.flow (c - (f p + ε)) (γ 0) = (D.chart p hp).χ (y 0) := by
    have := harc 0 ⟨by linarith, by linarith⟩
    rwa [zero_div] at this
  have hy0R : morseNorm n (y 0) ≤ (D.chart p hp).R :=
    (hy 0 ⟨by norm_num, by norm_num⟩).le.trans hrmR
  have hkey : ∀ t, γ t ∈ rightDom D p hp ε c → rightFun D p hp ε c (γ t) = 0 →
      γ t ∉ D.bottom := by
    intro t hdom hzero hbt
    obtain ⟨z, hz, hzx⟩ := hdom
    have hzR : morseNorm n z ≤ (D.chart p hp).R := le_of_lt hz
    have hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk z = 0 := by
      have h := hzero
      unfold rightFun at h
      rwa [← hzx, hinv z hzR] at h
    have hlevT : f (D.flow (c - (f p + ε)) (γ t)) = f p + ε := by
      have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := γ t)
        (T := c - (f p + ε)) ⟨by rw [hlev t]; linarith [hfp.1], by rw [hlev t]; exact hcb⟩
        ⟨by rw [hlev t]; linarith [hfp.1], by rw [hlev t]; linarith⟩
        (fun s hs q hq hmem => by
          rw [uIcc_of_le hT] at hs
          obtain ⟨w, hw, hwx⟩ := hmem
          exact hfree t s hs q hq ⟨w, show morseNorm n w ≤ _ from le_of_lt hw, hwx⟩)
        (c - (f p + ε)) right_mem_uIcc
      rw [h, hlev t]
      ring
    have hnf : f p + ε = f p + (1 / 2) * (‖posPart (D.chart p hp).hk z‖ ^ 2 -
        ‖negPart (D.chart p hp).hk z‖ ^ 2) := by
      rw [← hlevT, ← hzx, (D.chart p hp).hnorm z hzR,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
    unfold ModelField.scaledNegativePart at hJ0
    rcases smul_eq_zero.1 hJ0 with h | h
    · rw [h] at hnf
      nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk z‖]
    · have hsq :=
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
          (D.chart p hp).hk z
      rw [h, norm_zero] at hnf hsq
      have hzrm : morseNorm n z < D.rm p hp :=
        lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le (by nlinarith [hεp.2])
      have hcap : γ t ∈ D.captured p hp :=
        (GradientLikeStrip.flow_mem_captured_iff (c - (f p + ε))).1
          (GradientLikeStrip.mem_captured_of_mem_stable ⟨z, ⟨hzrm, h⟩, hzx⟩)
      exact Set.disjoint_left.1 (GradientLikeStrip.disjoint_bottom_captured hf p hp) hbt hcap
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · rw [rightDom, mem_ofPred_eq, hγ0]
    exact ⟨y 0, lt_of_lt_of_le (hy 0 ⟨by norm_num, by norm_num⟩) hrmR, rfl⟩
  · change ModelField.scaledNegativePart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) (γ 0))) = 0
    rw [hγ0, hinv _ hy0R]
    unfold ModelField.scaledNegativePart
    rw [hy0, smul_zero]
  · intro t hdom hzero
    refine ⟨⌊t + δ⌋, ?_⟩
    have hm1 : ((⌊t + δ⌋ : ℤ) : ℝ) ≤ t + δ := Int.floor_le _
    have hm2 : t + δ < ((⌊t + δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hγt : γ (t - ((⌊t + δ⌋ : ℤ) : ℝ)) = γ t := by
      have := hper.sub_int_mul_eq (x := t) ⌊t + δ⌋
      rwa [mul_one] at this
    by_contra hne
    have hne' : t - ((⌊t + δ⌋ : ℤ) : ℝ) ≠ 0 := fun h0 => hne (by linarith)
    apply hkey t hdom hzero
    rw [← hγt]
    rcases le_or_gt (t - ((⌊t + δ⌋ : ℤ) : ℝ)) δ with h | h
    · have hs : (t - ((⌊t + δ⌋ : ℤ) : ℝ)) / δ ∈ Icc (-1 : ℝ) 1 :=
        ⟨by rw [le_div_iff₀ hδ]; linarith, by rw [div_le_iff₀ hδ]; linarith⟩
      have hs0 : (t - ((⌊t + δ⌋ : ℤ) : ℝ)) / δ ≠ 0 := div_ne_zero hne' hδ.ne'
      have hb := hbot _ hs hs0
      rw [← harc _ ⟨by linarith, h⟩] at hb
      exact (GradientLikeStrip.flow_mem_bottom_iff hf _).1 hb
    · exact hrest _ ⟨h.le, by linarith⟩
  · obtain ⟨v, hv, hv0⟩ := hJ
    refine ⟨δ⁻¹ • v, ?_, smul_ne_zero (inv_ne_zero hδ.ne') hv0⟩
    have hlin : HasDerivAt (fun t : ℝ => t / δ) δ⁻¹ 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℝ)).div_const δ
    have hv' : HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk (y s)) v ((0 : ℝ) / δ) := by
      rwa [zero_div]
    have hcomp := hv'.scomp (0 : ℝ) hlin
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hδ) hδ] with t ht
    have hs : t / δ ∈ Icc (-1 : ℝ) 1 :=
      ⟨by rw [le_div_iff₀ hδ]; linarith [ht.1], by rw [div_le_iff₀ hδ]; linarith [ht.2]⟩
    change ModelField.scaledNegativePart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) (γ t))) = _
    rw [harc t (Ioo_subset_Icc_self ht), hinv _ ((hy _ hs).le.trans hrmR)]
    rfl

theorem exists_level_arc_loop (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = 1) {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    (hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2)
    (harms : (D.chart p hp).χ '' (D.chart p hp).leftModelSphere ε ⊆ D.bottom)
    (hV₀ : ConnectedSpace (f ⁻¹' {a})) :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
        (D'.chart x hx).R = (D.chart x hx).R ∧ (D'.chart x hx).R' = (D.chart x hx).R' ∧
        (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
      (∀ x hx, D'.rm x hx = D.rm x hx) ∧
      (∀ x hx, D'.closedSmallBall x hx ⊆ D.closedSmallBall x hx) ∧
      ∃ (y : ℝ → (Fin n → ℝ)) (γ₀ : ℝ → M),
        ContDiff ℝ ∞ y ∧ InjOn y (Icc (-1) 1) ∧ (∀ s ∈ Icc (-1 : ℝ) 1, deriv y s ≠ 0) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y s) < D'.rm p hp ∧
          morseNormalForm (D'.chart p hp).hk (f p) (y s) = f p + ε) ∧
        negPart (D'.chart p hp).hk (y 0) = 0 ∧
        (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D'.chart p hp).hk (y s)) v 0 ∧ v ≠ 0) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D'.chart p hp).χ (y s) ∈ D'.bottom) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1,
          ascendsFreely D' (c₂ - (f p + ε)) ((D'.chart p hp).χ (y s))) ∧
        Continuous γ₀ ∧ Periodic γ₀ 1 ∧ (∀ t, f (γ₀ t) = c₂) ∧
        (∀ t ∈ Icc (-(1 / 8) : ℝ) (1 / 8),
          γ₀ t = D'.flow (-(c₂ - (f p + ε))) ((D'.chart p hp).χ (y (8 * t)))) ∧
        ∀ t ∈ Icc (1 / 8 : ℝ) (7 / 8), γ₀ t ∈ D'.bottom := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfp : f p ∈ Ioo a b := ((hcrit p).1 hp).1
  set T : ℝ := c₂ - (f p + ε) with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  obtain ⟨y, hy, hyinj, hy', hyball, hy0, hJ, hyasc, hybot⟩ :=
    exists_arc h5 hf D hcrit hp hkp hε hεp hpc hc₂ hcU hdn harms
  have hysrc : ∀ s ∈ Icc (-1 : ℝ) 1, y s ∈ (D.chart p hp).χ.source := fun s hs =>
    (D.chart p hp).hsrc _ ((hyball s hs).1.le.trans (D.hrm p hp).2)
  have hfy : ∀ s ∈ Icc (-1 : ℝ) 1, f ((D.chart p hp).χ (y s)) = f p + ε := fun s hs => by
    rw [(D.chart p hp).hnorm _ ((hyball s hs).1.le.trans (D.hrm p hp).2)]
    exact (hyball s hs).2
  have hKc : ContinuousOn (fun s => (D.chart p hp).χ (y s)) (Icc (-1 : ℝ) 1) :=
    (D.chart p hp).χ.continuousOn.comp hy.continuous.continuousOn fun s hs => hysrc s hs
  obtain ⟨D', hch, hrm, -, ⟨φ, hφ, ⟨m, M₀, hm, hφb⟩, hV⟩, -, hup⟩ :=
    exists_shrink_free hfs D (Kdn := ∅)
      (Kup := (fun s => (D.chart p hp).χ (y s)) '' Icc (-1 : ℝ) 1) isCompact_empty
      (isCompact_Icc.image_of_continuousOn hKc) le_rfl hT0 (fun x hx => absurd hx (by simp))
      (by
        rintro x ⟨s, hs, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hfy s hs]; linarith [hfp.1]
        · rw [hfy s hs, hT]; linarith
        · obtain ⟨t, ht, hlt⟩ := hyasc s hs
          exact ⟨t, ht, by rw [hfy s hs, hT]; linarith⟩)
      one_pos
  have hbot_iff : ∀ x, x ∈ D'.bottom ↔ x ∈ D.bottom := fun x =>
    GradientLikeStrip.exists_nonneg_flow_mem_iff D D' hφ hm hφb hV x (f ⁻¹' Iio a)
  have hball' : ∀ x hx, D'.closedSmallBall x hx ⊆ D.closedSmallBall x hx := by
    intro x hx z hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, ?_, by rw [(hch x hx).1]⟩
    exact le_trans hw (hch x hx).2.2.2.2.1
  have hχ : (D'.chart p hp).χ = (D.chart p hp).χ := (hch p hp).1
  have hkk : (D.chart p hp).k = (D'.chart p hp).k := ((hch p hp).2.1).symm
  have hneg : ∀ (k k' : ℕ) (hk : k ≤ n) (hk' : k' ≤ n), k = k' →
      negPart hk (y 0) = 0 → negPart hk' (y 0) = 0 := by
    intro k k' hk hk' h
    subst h
    exact id
  have hJt : ∀ (k k' : ℕ) (hk : k ≤ n) (hk' : k' ≤ n), k = k' →
      (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart hk (y s)) v 0 ∧ v ≠ 0) →
      (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart hk' (y s)) v 0 ∧ v ≠ 0) := by
    intro k k' hk hk' h
    subst h
    exact id
  have hasc' : ∀ s ∈ Icc (-1 : ℝ) 1, ascendsFreely D' T ((D'.chart p hp).χ (y s)) := by
    intro s hs
    rw [hχ]
    exact hup _ ⟨s, hs, rfl⟩
  have hfy' : ∀ s ∈ Icc (-1 : ℝ) 1, f ((D'.chart p hp).χ (y s)) = f p + ε := fun s hs => by
    rw [hχ]; exact hfy s hs
  have hAc : ∀ s ∈ Icc (-1 : ℝ) 1, f (D'.flow (-T) ((D'.chart p hp).χ (y s))) = c₂ := by
    intro s hs
    have h := D'.f_flow_eq_sub_of_avoid_uIcc hfs (x := (D'.chart p hp).χ (y s)) (T := -T)
      (by rw [hfy' s hs]; exact ⟨by linarith [hfp.1], by linarith [hfp.2]⟩)
      (by rw [hfy' s hs, hT]; exact ⟨by linarith [hfp.1], by linarith⟩)
      (by
        intro u hu q hq hmem
        rw [uIcc_of_ge (by linarith)] at hu
        exact hasc' s hs u hu q hq (D'.smallBall_subset_closedSmallBall q hq hmem))
    rw [h (-T) right_mem_uIcc, hfy' s hs, hT]
    ring
  have hbotflow : ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 →
      D'.flow (-T) ((D'.chart p hp).χ (y s)) ∈ D'.bottom := by
    intro s hs hs0
    have hmem : (D'.chart p hp).χ (y s) ∈ D'.bottom := by
      rw [hbot_iff, hχ]; exact hybot s hs hs0
    obtain ⟨t, ht, hlt⟩ := hmem
    refine ⟨t + T, by linarith, ?_⟩
    rw [D'.flow_flow, show -T + (t + T) = t by ring]
    exact hlt
  have hc : c₂ ∈ Ioo a b := ⟨by linarith [hfp.1], hc₂⟩
  have hcU' : ∀ x hx, ∀ z ∈ D'.closedSmallBall x hx, f z ≠ c₂ := fun x hx z hz =>
    hcU x hx z (hball' x hx hz)
  have hdn' : ∀ x hx, f x < c₂ → (D'.chart x hx).k ≤ 2 := fun x hx h => by
    rw [(hch x hx).2.1]; exact hdn x hx h
  have hA : ContinuousOn (fun s => D'.flow (-T) ((D'.chart p hp).χ (y s))) (Icc (-1 : ℝ) 1) := by
    have : ContinuousOn (fun s => (D'.chart p hp).χ (y s)) (Icc (-1 : ℝ) 1) := by
      rw [hχ]; exact hKc
    exact (D'.continuous_flow (-T)).comp_continuousOn this
  obtain ⟨γ₀, hγ₀, hper, hlev, harc, hbot⟩ :=
    exists_loop_through_arc h5 hf D' hcrit hc hcU' hdn' hV₀ hA hAc
      (hbotflow 1 (right_mem_Icc.2 (by norm_num)) one_ne_zero)
      (hbotflow (-1) (left_mem_Icc.2 (by norm_num)) (by norm_num))
  refine ⟨D', fun x hx => ⟨(hch x hx).1, (hch x hx).2.1, (hch x hx).2.2.1, (hch x hx).2.2.2.1,
    (hch x hx).2.2.2.2.1⟩, hrm, hball', y, γ₀, hy, hyinj, hy', ?_, ?_, ?_, ?_, hasc', hγ₀, hper,
    hlev, harc, hbot⟩
  · intro s hs
    refine ⟨by rw [hrm]; exact (hyball s hs).1, ?_⟩
    rw [← (D'.chart p hp).hnorm _ ((hyball s hs).1.le.trans ((hrm p hp).symm ▸ (D'.hrm p hp).2))]
    exact hfy' s hs
  · exact hneg _ _ (D.chart p hp).hk (D'.chart p hp).hk hkk hy0
  · exact hJt _ _ (D.chart p hp).hk (D'.chart p hp).hk hkk hJ
  · intro s hs hs0
    rw [hbot_iff, hχ]
    exact hybot s hs hs0

theorem exists_loop_of_level_arc (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    {y : ℝ → (Fin n → ℝ)} (hy : ContDiff ℝ ∞ y) (hyinj : InjOn y (Icc (-1) 1))
    (hy' : ∀ s ∈ Icc (-1 : ℝ) 1, deriv y s ≠ 0)
    (hyball : ∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y s) < D.rm p hp ∧
      morseNormalForm (D.chart p hp).hk (f p) (y s) = f p + ε)
    (hy0 : negPart (D.chart p hp).hk (y 0) = 0)
    (hJ : ∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D.chart p hp).hk (y s)) v 0 ∧ v ≠ 0)
    (hybot : ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D.chart p hp).χ (y s) ∈ D.bottom)
    (hyasc : ∀ s ∈ Icc (-1 : ℝ) 1, ascendsFreely D (c₂ - (f p + ε)) ((D.chart p hp).χ (y s)))
    {γ₀ : ℝ → M} (hγ₀ : Continuous γ₀) (hper : Periodic γ₀ 1) (hlev : ∀ t, f (γ₀ t) = c₂)
    (harc : ∀ t ∈ Icc (-(1 / 8) : ℝ) (1 / 8),
      γ₀ t = D.flow (-(c₂ - (f p + ε))) ((D.chart p hp).χ (y (8 * t))))
    (hbot : ∀ t ∈ Icc (1 / 8 : ℝ) (7 / 8), γ₀ t ∈ D.bottom) :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
        (D'.chart x hx).R = (D.chart x hx).R ∧ (D'.chart x hx).R' = (D.chart x hx).R' ∧
        (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
      (∀ x hx, D'.rm x hx = D.rm x hx) ∧
      ∃ γ : ℝ → M, isLevelLoop I f c₂ γ ∧ (∀ θ, descendsFreely D' (c₂ - (f p + ε)) (γ θ)) ∧
        meetsRightOnce D' p hp ε c₂ γ := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hpab : f p ∈ Ioo a b := ((hcrit p).1 hp).1
  have hc : c₂ ∈ Ioo a b := ⟨by linarith [hpab.1], hc₂⟩
  set T : ℝ := c₂ - (f p + ε) with hTdef
  have hT : 0 < T := sub_pos.2 hpc
  have hopen : ∀ r : ℝ, IsOpen {t : ℝ | ∃ k : ℤ, t - k ∈ Ioo (-r) r} := by
    intro r
    have hset : {t : ℝ | ∃ k : ℤ, t - k ∈ Ioo (-r) r} =
        ⋃ k : ℤ, (fun t : ℝ => t - k) ⁻¹' Ioo (-r) r := by
      ext t; simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
    rw [hset]
    exact isOpen_iUnion fun k => isOpen_Ioo.preimage (continuous_id.sub continuous_const)
  have hclosed : ∀ r : ℝ, IsClosed {t : ℝ | ∃ k : ℤ, t - k ∈ Icc (-r) r} := by
    intro r
    open scoped Pointwise in
    have key : IsClosed (Icc (-r) r + range (Int.cast : ℤ → ℝ)) :=
      Int.isClosedEmbedding_coe_real.isClosed_range.add_left_of_isCompact isCompact_Icc
    open scoped Pointwise in
    have hset : {t : ℝ | ∃ k : ℤ, t - k ∈ Icc (-r) r} =
        Icc (-r) r + range (Int.cast : ℤ → ℝ) := by
      ext t
      simp only [mem_ofPred_eq, Set.mem_add, mem_range]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨t - k, hk, k, ⟨k, rfl⟩, by ring⟩
      · rintro ⟨u, hu, _, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, by simpa using hu⟩
    rw [hset]
    exact key
  have hpermem : ∀ (A : Set ℝ) (t : ℝ), (∃ k : ℤ, t - k ∈ A) ↔ (∃ k : ℤ, t + 1 - k ∈ A) := by
    intro A t
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by push_cast; convert hk using 1; ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k - 1, by push_cast; convert hk using 1; ring⟩
  have hyR : ∀ s ∈ Icc (-1 : ℝ) 1, y s ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' :=
    fun s hs => (D.chart p hp).mem_ball_of_le ((hyball s hs).1.le.trans (D.hrm p hp).2)
  have hγ₀loc : ∀ θ : ℝ, ∀ k : ℤ, θ - k ∈ Icc (-(1 / 8) : ℝ) (1 / 8) →
      γ₀ θ = D.flow (-T) ((D.chart p hp).χ (y (8 * (θ - k)))) := by
    intro θ k hk
    rw [← harc _ hk]
    have := hper.sub_int_mul_eq (x := θ) k
    rw [mul_one] at this
    exact this.symm
  have hwsm : ∀ k : ℤ, ContDiff ℝ ∞ (fun θ : ℝ => y (8 * (θ - k))) := fun k =>
    hy.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hsmAt : ∀ θ : ℝ, ∀ k : ℤ, θ - k ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) →
      ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ₀ θ := by
    intro θ k hk
    have hev : γ₀ =ᶠ[𝓝 θ] fun θ' => D.flow (-T) ((D.chart p hp).χ (y (8 * (θ' - k)))) := by
      have : ∀ᶠ θ' : ℝ in 𝓝 θ, θ' - (k : ℝ) ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) :=
        (isOpen_Ioo.preimage (continuous_id.sub continuous_const)).mem_nhds hk
      filter_upwards [this] with θ' hθ'
      exact hγ₀loc θ' k (Ioo_subset_Icc_self hθ')
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    have h8 : 8 * (θ - k) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact ((D.contMDiff_flow (-T)).contMDiffAt).comp θ
      (((D.chart p hp).contMDiffAt_chart (hyR _ h8)).comp θ ((hwsm k).contMDiff.contMDiffAt))
  have hγ₀arcbot : ∀ t ∈ Icc (-(1 / 8) : ℝ) (1 / 8), t ≠ 0 → γ₀ t ∈ D.bottom := by
    intro t ht ht0
    rw [harc t ht, GradientLikeStrip.flow_mem_bottom_iff hfs]
    exact hybot _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by intro h; apply ht0; linarith)
  have hγ₀bot : ∀ t ∈ Icc (1 / 32 : ℝ) (31 / 32), γ₀ t ∈ D.bottom := by
    intro t ht
    rcases le_or_gt t (1 / 8) with h1 | h1
    · exact hγ₀arcbot t ⟨by linarith [ht.1], h1⟩ (by linarith [ht.1])
    rcases le_or_gt (7 / 8) t with h2 | h2
    · have := hper (t - 1)
      rw [sub_add_cancel] at this
      rw [this]
      exact hγ₀arcbot (t - 1) ⟨by linarith, by linarith [ht.2]⟩ (by linarith [ht.2])
    · exact hbot t ⟨h1.le, h2.le⟩
  have hU₀ : IsOpen {t : ℝ | ∃ k : ℤ, t - k ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)} := hopen (1 / 8)
  have hP₁ : IsClosed {t : ℝ | ∃ k : ℤ, t - k ∈ Icc (-(1 / 16) : ℝ) (1 / 16)} := hclosed (1 / 16)
  have hsm₀ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ₀ {t : ℝ | ∃ k : ℤ, t - k ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)} :=
    fun θ ⟨k, hk⟩ => (hsmAt θ k hk).contMDiffWithinAt
  have hP₁U₀ : {t : ℝ | ∃ k : ℤ, t - k ∈ Icc (-(1 / 16) : ℝ) (1 / 16)} ⊆
      {t : ℝ | ∃ k : ℤ, t - k ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)} := by
    rintro t ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  have hKb : IsCompact (γ₀ '' Icc (1 / 32 : ℝ) (31 / 32)) := isCompact_Icc.image hγ₀
  have hKbbot : γ₀ '' Icc (1 / 32 : ℝ) (31 / 32) ⊆ D.bottom := by
    rintro _ ⟨t, ht, rfl⟩
    exact hγ₀bot t ht
  have hO₁ : IsOpen (((γ₀ '' Icc (1 / 32 : ℝ) (31 / 32))ᶜ ×ˢ (univ : Set M)) ∪
      ((univ : Set M) ×ˢ D.bottom)) :=
    (hKb.isClosed.isOpen_compl.prod isOpen_univ).union (isOpen_univ.prod (D.isOpen_bottom hfc))
  have hdiag₁ : ∀ x, (x, x) ∈ ((γ₀ '' Icc (1 / 32 : ℝ) (31 / 32))ᶜ ×ˢ (univ : Set M)) ∪
      ((univ : Set M) ×ˢ D.bottom) := by
    intro x
    by_cases hx : x ∈ γ₀ '' Icc (1 / 32 : ℝ) (31 / 32)
    · exact Or.inr ⟨mem_univ _, hKbbot hx⟩
    · exact Or.inl ⟨hx, mem_univ _⟩
  obtain ⟨γ₁, hγ₁sm, hγ₁per, hγ₁lev, hγ₁P, hγ₁O⟩ :=
    exists_smooth_level_loop hf D hc hcU hγ₀ hper hlev hU₀
      (fun t => hpermem (Ioo (-(1 / 8) : ℝ) (1 / 8)) t) hsm₀ hP₁
      (fun t => hpermem (Icc (-(1 / 16) : ℝ) (1 / 16)) t) hP₁U₀ hO₁ hdiag₁
  have hγ₁bot : ∀ t ∈ Icc (1 / 32 : ℝ) (31 / 32), γ₁ t ∈ D.bottom := by
    intro t ht
    rcases hγ₁O t with h | h
    · exact absurd (mem_image_of_mem γ₀ ht) h.1
    · exact h.2
  have hγ₁eq : ∀ θ : ℝ, ∀ k : ℤ, θ - k ∈ Icc (-(1 / 16) : ℝ) (1 / 16) → γ₁ θ = γ₀ θ :=
    fun θ k hk => hγ₁P θ ⟨k, hk⟩
  have hreg : ∀ x, f x = c₂ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hcx
    have hxc : x ∈ crit := (hcrit x).2 ⟨hx ▸ hc, hcx⟩
    exact hcU x hxc x (D.smallBall_subset_closedSmallBall x hxc (D.p_mem_smallBall x hxc)) hx
  have himm : ∀ θ : ℝ, ∀ k : ℤ, θ - k ∈ Ioo (-(1 / 16) : ℝ) (1 / 16) →
      mfderiv 𝓘(ℝ, ℝ) I γ₁ θ (1 : ℝ) ≠ 0 := by
    intro θ k hk
    have hk8 : θ - k ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have h8 : 8 * (θ - k) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have hev1 : γ₁ =ᶠ[𝓝 θ] γ₀ := by
      have : ∀ᶠ θ' : ℝ in 𝓝 θ, θ' - (k : ℝ) ∈ Ioo (-(1 / 16) : ℝ) (1 / 16) :=
        (isOpen_Ioo.preimage (continuous_id.sub continuous_const)).mem_nhds hk
      filter_upwards [this] with θ' hθ'
      exact hγ₁eq θ' k (Ioo_subset_Icc_self hθ')
    intro h0
    have e1 := DFunLike.congr_fun (hev1.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)) (show TangentSpace 𝓘(ℝ, ℝ) θ from (1 : ℝ))
    replace h0 : mfderiv 𝓘(ℝ, ℝ) I γ₀ θ (1 : ℝ) = 0 := e1.symm.trans h0
    have hγ₀d : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₀ θ := (hsmAt θ k hk8).mdifferentiableAt (by simp)
    have hmem : D.flow T (γ₀ θ) ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' := by
      rw [hγ₀loc θ k (Ioo_subset_Icc_self hk8), GradientLikeStrip.flow_flow_neg]
      exact mem_image_of_mem _ (hyR _ h8)
    have hGd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ)
        (fun x => (D.chart p hp).χ.symm (D.flow T x)) (γ₀ θ) :=
      (((D.chart p hp).contMDiffAt_symm hmem).comp (γ₀ θ)
        ((D.contMDiff_flow T).contMDiffAt)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp θ hGd hγ₀d
    have hev2 : ((fun x => (D.chart p hp).χ.symm (D.flow T x)) ∘ γ₀) =ᶠ[𝓝 θ]
        fun θ' => y (8 * (θ' - k)) := by
      have : ∀ᶠ θ' : ℝ in 𝓝 θ, θ' - (k : ℝ) ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) :=
        (isOpen_Ioo.preimage (continuous_id.sub continuous_const)).mem_nhds hk8
      filter_upwards [this] with θ' hθ'
      have h8' : 8 * (θ' - k) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩
      simp only [Function.comp_apply]
      rw [hγ₀loc θ' k (Ioo_subset_Icc_self hθ'), GradientLikeStrip.flow_flow_neg,
        (D.chart p hp).χ.left_inv ((D.chart p hp).hball (hyR _ h8'))]
    have h3 := DFunLike.congr_fun
      (hev2.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))) (show TangentSpace 𝓘(ℝ, ℝ) θ from (1 : ℝ))
    rw [hcomp, ContinuousLinearMap.comp_apply, h0, map_zero, mfderiv_eq_fderiv] at h3
    have hin : HasDerivAt (fun θ' : ℝ => 8 * (θ' - k)) 8 θ := by
      simpa using ((hasDerivAt_id θ).sub_const (k : ℝ)).const_mul 8
    have hyd : HasDerivAt y (deriv y (8 * (θ - k))) (8 * (θ - k)) :=
      ((hy.differentiable (by simp)) _).hasDerivAt
    have hw := hyd.scomp θ hin
    have h4 : deriv (fun θ' => y (8 * (θ' - k))) θ = 0 := h3.symm
    rw [show (fun θ' => y (8 * (θ' - k))) = y ∘ (fun θ' : ℝ => 8 * (θ' - k)) from rfl,
      hw.deriv] at h4
    exact smul_ne_zero (by norm_num) (hy' _ h8) h4
  have hinj : ∀ θ θ' : ℝ, ∀ k₁ k₂ : ℤ, θ - k₁ ∈ Ioo (-(1 / 16) : ℝ) (1 / 16) →
      θ' - k₂ ∈ Ioo (-(1 / 16) : ℝ) (1 / 16) → γ₁ θ = γ₁ θ' → ∃ k : ℤ, θ' = θ + k := by
    intro θ θ' k₁ k₂ h₁ h₂ heq
    have h₁' : θ - k₁ ∈ Icc (-(1 / 8) : ℝ) (1 / 8) := ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
    have h₂' : θ' - k₂ ∈ Icc (-(1 / 8) : ℝ) (1 / 8) := ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
    have e₁ : 8 * (θ - k₁) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
    have e₂ : 8 * (θ' - k₂) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
    rw [hγ₁eq θ k₁ (Ioo_subset_Icc_self h₁), hγ₁eq θ' k₂ (Ioo_subset_Icc_self h₂),
      hγ₀loc θ k₁ h₁', hγ₀loc θ' k₂ h₂'] at heq
    have heq2 := (D.chart p hp).χ.injOn ((D.chart p hp).hball (hyR _ e₁))
      ((D.chart p hp).hball (hyR _ e₂)) (D.flow_injective (-T) heq)
    have heq3 := hyinj e₁ e₂ heq2
    exact ⟨k₂ - k₁, by push_cast; linarith⟩
  have hK₁ : IsCompact (γ₁ '' Icc (1 / 32 : ℝ) (31 / 32)) :=
    isCompact_Icc.image hγ₁sm.continuous
  have hK₁bot : γ₁ '' Icc (1 / 32 : ℝ) (31 / 32) ⊆ D.bottom := by
    rintro _ ⟨t, ht, rfl⟩
    exact hγ₁bot t ht
  have hO₂ : IsOpen (((γ₁ '' Icc (1 / 32 : ℝ) (31 / 32))ᶜ ×ˢ (univ : Set M)) ∪
      ((univ : Set M) ×ˢ D.bottom)) :=
    (hK₁.isClosed.isOpen_compl.prod isOpen_univ).union (isOpen_univ.prod (D.isOpen_bottom hfc))
  have hdiag₂ : ∀ x, (x, x) ∈ ((γ₁ '' Icc (1 / 32 : ℝ) (31 / 32))ᶜ ×ˢ (univ : Set M)) ∪
      ((univ : Set M) ×ˢ D.bottom) := by
    intro x
    by_cases hx : x ∈ γ₁ '' Icc (1 / 32 : ℝ) (31 / 32)
    · exact Or.inr ⟨mem_univ _, hK₁bot hx⟩
    · exact Or.inl ⟨hx, mem_univ _⟩
  have hsm₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry fun θ (_ : ℝ) => γ₁ θ) :=
    hγ₁sm.comp contDiff_fst.contMDiff
  have hU₂ : IsOpen {z : ℝ × ℝ | ∃ k : ℤ, z.1 - k ∈ Ioo (-(1 / 16) : ℝ) (1 / 16)} :=
    (hopen (1 / 16)).preimage continuous_fst
  have hP₂ : IsClosed {z : ℝ × ℝ | ∃ k : ℤ, z.1 - k ∈ Icc (-(1 / 32) : ℝ) (1 / 32)} :=
    (hclosed (1 / 32)).preimage continuous_fst
  have hP₂U₂ : {z : ℝ × ℝ | ∃ k : ℤ, z.1 - k ∈ Icc (-(1 / 32) : ℝ) (1 / 32)} ⊆
      {z : ℝ × ℝ | ∃ k : ℤ, z.1 - k ∈ Ioo (-(1 / 16) : ℝ) (1 / 16)} := by
    rintro z ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  obtain ⟨h', hh'sm, hh'per, hh'lev, hh'P, hh'O, hemb⟩ :=
    exists_embedded_slices h5 hfs hreg hsm₁ (fun θ _ => hγ₁per θ) (fun θ _ => hγ₁lev θ) hU₂
      (fun θ _ => hpermem (Ioo (-(1 / 16) : ℝ) (1 / 16)) θ) hP₂
      (fun θ _ => hpermem (Icc (-(1 / 32) : ℝ) (1 / 32)) θ) hP₂U₂
      (fun z ⟨k, hk⟩ => himm z.1 k hk)
      (fun θ θ' _ ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ heq => hinj θ θ' k₁ k₂ h₁ h₂ heq) hO₂ hdiag₂
  have hγper : Periodic (fun θ => h' θ 0) 1 := fun θ => hh'per θ 0
  have hγsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun θ => h' θ 0) :=
    hh'sm.comp (contDiff_id.prodMk contDiff_const).contMDiff
  have hγlev : ∀ θ, f ((fun θ => h' θ 0) θ) = c₂ := fun θ => hh'lev θ 0
  have hemb0 := hemb 0 ⟨le_rfl, zero_le_one⟩
  have hloop : isLevelLoop I f c₂ (fun θ => h' θ 0) :=
    ⟨hγper, hγsm, hemb0.1, hemb0.2, hγlev⟩
  have hγeq : ∀ θ ∈ Icc (-(1 / 32) : ℝ) (1 / 32), h' θ 0 = γ₀ θ := by
    intro θ hθ
    have e1 := hh'P θ 0 ⟨0, by simpa using hθ⟩
    rw [e1]
    exact hγ₁eq θ 0 ⟨by simp; linarith [hθ.1], by simp; linarith [hθ.2]⟩
  have hγbot : ∀ θ ∈ Icc (1 / 32 : ℝ) (31 / 32), h' θ 0 ∈ D.bottom := by
    intro θ hθ
    rcases hh'O θ 0 with h | h
    · exact absurd (mem_image_of_mem γ₁ hθ) h.1
    · exact h.2
  have hz0 : ∃ s, 0 ≤ s ∧ f (D.flow s ((D.chart p hp).χ (y 0))) < f p + ε := by
    have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hfz : f ((D.chart p hp).χ (y 0)) = f p + ε := by
      rw [(D.chart p hp).hnorm (y 0) ((hyball 0 h0mem).1.le.trans (D.hrm p hp).2)]
      exact (hyball 0 h0mem).2
    have hzc : (D.chart p hp).χ (y 0) ∉ crit := by
      intro hzc
      by_cases hzp : (D.chart p hp).χ (y 0) = p
      · rw [hzp] at hfz
        linarith
      · exact Set.disjoint_left.1 (D.disjoint p hp _ hzc (fun h => hzp h.symm))
          ⟨y 0, hyR 0 h0mem, rfl⟩ (D.chart _ hzc).p_mem_image_ball
    have hzab : (D.chart p hp).χ (y 0) ∈ f ⁻¹' Icc a b := by
      rw [mem_preimage, hfz]
      exact ⟨by linarith [hpab.1], by linarith⟩
    have hneg := D.neg _ hzab hzc
    have hd := GradientLikeStrip.hasDerivAt_f_flow (D := D) hfs ((D.chart p hp).χ (y 0)) 0
    rw [GradientLikeStrip.flow_zero] at hd
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        slope (fun s => f (D.flow s ((D.chart p hp).χ (y 0)))) 0 t < 0 :=
      (tendsto_order.1 hd).2 0 hneg
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        slope (fun s => f (D.flow s ((D.chart p hp).χ (y 0)))) 0 t < 0 :=
      h1.filter_mono (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
    obtain ⟨s, hs, hs0⟩ := (h2.and self_mem_nhdsWithin).exists
    have hs0' : (0 : ℝ) < s := hs0
    rw [slope_def_field, sub_zero, GradientLikeStrip.flow_zero] at hs
    have := (div_lt_iff₀ hs0').1 hs
    exact ⟨s, hs0'.le, by linarith⟩
  have hKdn : IsCompact (range fun θ => h' θ 0) :=
    hγper.compact_of_continuous one_ne_zero hγsm.continuous
  have hdn : ∀ x ∈ range (fun θ => h' θ 0), a ≤ f x - T ∧ f x ≤ b ∧
      ∃ t, 0 ≤ t ∧ f (D.flow t x) < f x - T := by
    rintro _ ⟨θ, rfl⟩
    rw [hγlev θ]
    refine ⟨by rw [hTdef]; linarith [hpab.1], hc₂.le, ?_⟩
    have hfT : c₂ - T = f p + ε := by rw [hTdef]; ring
    rw [hfT]
    set k : ℤ := ⌊θ + 1 / 32⌋ with hkdef
    have hk1 : (k : ℝ) ≤ θ + 1 / 32 := Int.floor_le _
    have hk2 : θ + 1 / 32 < k + 1 := Int.lt_floor_add_one _
    have hθk : h' θ 0 = h' (θ - k) 0 := by
      have := hγper.sub_int_mul_eq (x := θ) k
      rw [mul_one] at this
      exact this.symm
    change ∃ t, 0 ≤ t ∧ f (D.flow t (h' θ 0)) < f p + ε
    rw [hθk]
    rcases le_or_gt (1 / 32 : ℝ) (θ - k) with hu | hu
    · obtain ⟨t, ht, hlt⟩ := hγbot (θ - k) ⟨hu, by linarith⟩
      exact ⟨t, ht, by linarith [hpab.1]⟩
    · have hu' : θ - k ∈ Icc (-(1 / 32) : ℝ) (1 / 32) := ⟨by linarith, hu.le⟩
      have hu8 : θ - k ∈ Icc (-(1 / 8) : ℝ) (1 / 8) := ⟨by linarith, by linarith⟩
      rw [hγeq _ hu', harc _ hu8]
      suffices hz : ∃ s, 0 ≤ s ∧ f (D.flow s ((D.chart p hp).χ (y (8 * (θ - k))))) < f p + ε by
        obtain ⟨s, hs, hlt⟩ := hz
        refine ⟨T + s, by linarith, ?_⟩
        rw [GradientLikeStrip.flow_add, GradientLikeStrip.flow_flow_neg]
        exact hlt
      by_cases h0 : θ - k = 0
      · rw [h0, mul_zero]
        exact hz0
      · obtain ⟨s, hs, hlt⟩ := hybot (8 * (θ - k)) ⟨by linarith, by linarith⟩
          (mul_ne_zero (by norm_num) h0)
        exact ⟨s, hs, by linarith [hpab.1]⟩
  obtain ⟨D₂, hch₂, hrm₂, hVeq₂, ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩, hfree₂, -⟩ :=
    exists_shrink_free hfs D (Kdn := range fun θ => h' θ 0) (Kup := ∅) hKdn isCompact_empty
      (Tdn := T) (Tup := 0) hT.le le_rfl hdn (fun x hx => absurd hx (Set.notMem_empty x)) one_pos
  have hbotiff : ∀ x, x ∈ D₂.bottom ↔ x ∈ D.bottom := fun x =>
    GradientLikeStrip.exists_nonneg_flow_mem_iff D D₂ hφc hm hφb hφV x (f ⁻¹' Iio a)
  have hfree : ∀ θ, descendsFreely D₂ T (h' θ 0) := fun θ => hfree₂ _ ⟨θ, rfl⟩
  have hεp₂ : (D₂.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D₂.rm p hp ^ 2 := by
    refine ⟨lt_of_le_of_lt ?_ hεp.1, by rw [hrm₂]; exact hεp.2⟩
    exact pow_le_pow_left₀ (D₂.chart p hp).hr₀.le (hch₂ p hp).2.2.2.2.1 2
  have hkeq : (D₂.chart p hp).k = (D.chart p hp).k := (hch₂ p hp).2.1
  have hnegT : ∀ {k₁ k₂ : ℕ} (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ → ∀ z : Fin n → ℝ,
      negPart h₂ z = 0 → negPart h₁ z = 0 := by
    rintro k₁ k₂ h₁ h₂ rfl z h
    exact h
  have hJT : ∀ {k₁ k₂ : ℕ} (h₁ : k₁ ≤ n) (h₂ : k₂ ≤ n), k₁ = k₂ →
      (∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart h₂ (y (s / 4))) v 0 ∧ v ≠ 0) →
      ∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart h₁ (y (s / 4))) v 0 ∧ v ≠ 0 := by
    rintro k₁ k₂ h₁ h₂ rfl h
    exact h
  have hy0₂ : negPart (D₂.chart p hp).hk (y (0 / 4)) = 0 :=
    hnegT (D₂.chart p hp).hk (D.chart p hp).hk hkeq _ (by rw [zero_div]; exact hy0)
  have hJ₂ : ∃ v, HasDerivAt (fun s => ModelField.scaledNegativePart (D₂.chart p hp).hk (y (s / 4))) v 0 ∧
      v ≠ 0 := by
    refine hJT (D₂.chart p hp).hk (D.chart p hp).hk hkeq ?_
    obtain ⟨v, hv, hv0⟩ := hJ
    have hin : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) 0 := (hasDerivAt_id 0).div_const 4
    exact ⟨(1 / 4 : ℝ) • v, hv.scomp_of_eq 0 hin (by norm_num),
      smul_ne_zero (by norm_num) hv0⟩
  have hy₂ : ∀ s ∈ Icc (-1 : ℝ) 1, morseNorm n (y (s / 4)) < D₂.rm p hp := by
    intro s hs
    rw [hrm₂]
    exact (hyball _ ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have harc₂ : ∀ t ∈ Icc (-(1 / 32) : ℝ) (1 / 32),
      D₂.flow T (h' t 0) = (D₂.chart p hp).χ (y (t / (1 / 32) / 4)) := by
    intro t ht
    have hte : t / (1 / 32) / 4 = 8 * t := by ring
    have ht8 : t ∈ Icc (-(1 / 8) : ℝ) (1 / 8) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h8 : 8 * t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [(hch₂ p hp).1, hte, hγeq t ht, harc t ht8]
    rw [flow_eq_of_agree_along D D₂ ?_]
    · exact D.flow_flow_neg _ _
    intro s hs
    rw [uIcc_of_le hT.le] at hs
    apply hVeq₂
    intro q hq
    rw [GradientLikeStrip.flow_flow]
    exact hyasc (8 * t) h8 (-T + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ q hq
  have hbot₂ : ∀ s ∈ Icc (-1 : ℝ) 1, s ≠ 0 → (D₂.chart p hp).χ (y (s / 4)) ∈ D₂.bottom := by
    intro s hs hs0
    rw [(hch₂ p hp).1, hbotiff]
    exact hybot _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ (div_ne_zero hs0 four_ne_zero)
  have hrest₂ : ∀ t ∈ Icc (1 / 32 : ℝ) (1 - 1 / 32), h' t 0 ∈ D₂.bottom := fun t ht =>
    (hbotiff _).2 (hγbot t ⟨ht.1, by linarith [ht.2]⟩)
  have hmeet : meetsRightOnce D₂ p hp ε c₂ (fun θ => h' θ 0) :=
    meetsRightOnce_of_arc hfs D₂ hp hε hεp₂ hpc.le hc₂.le hγper hγlev hfree
      (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num) hy₂ hy0₂ hJ₂ harc₂ hbot₂ hrest₂
  refine ⟨D₂, fun x hx => ⟨(hch₂ x hx).1, (hch₂ x hx).2.1, (hch₂ x hx).2.2.1,
    (hch₂ x hx).2.2.2.1, (hch₂ x hx).2.2.2.2.1⟩, hrm₂, fun θ => h' θ 0, hloop, hfree, hmeet⟩

theorem exists_level_loop (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = 1) {ε c₂ : ℝ} (hε : 0 < ε)
    (hεp : (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) (hpc : f p + ε < c₂)
    (hc₂ : c₂ < b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂)
    (hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2)
    (harms : (D.chart p hp).χ '' (D.chart p hp).leftModelSphere ε ⊆ D.bottom)
    (hV₀ : ConnectedSpace (f ⁻¹' {a})) :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ x hx, (D'.chart x hx).χ = (D.chart x hx).χ ∧ (D'.chart x hx).k = (D.chart x hx).k ∧
        (D'.chart x hx).R = (D.chart x hx).R ∧ (D'.chart x hx).R' = (D.chart x hx).R' ∧
        (D'.chart x hx).r₀ ≤ (D.chart x hx).r₀) ∧
      (∀ x hx, D'.rm x hx = D.rm x hx) ∧
      ∃ γ : ℝ → M, isLevelLoop I f c₂ γ ∧ (∀ θ, descendsFreely D' (c₂ - (f p + ε)) (γ θ)) ∧
        meetsRightOnce D' p hp ε c₂ γ := by
  obtain ⟨D₁, hch₁, hrm₁, hball₁, y, γ₀, hy, hyinj, hy', hyball, hy0, hJ, hybot, hyasc, hγ₀,
    hper, hlev, harc, hbot⟩ :=
    exists_level_arc_loop h5 hf D hcrit hp hkp hε hεp hpc hc₂ hcU hdn harms hV₀
  have hcU₁ : ∀ x hx, ∀ y ∈ D₁.closedSmallBall x hx, f y ≠ c₂ :=
    fun x hx y hy => hcU x hx y (hball₁ x hx hy)
  have hεp₁ : (D₁.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D₁.rm p hp ^ 2 := by
    refine ⟨lt_of_le_of_lt ?_ hεp.1, by rw [hrm₁]; exact hεp.2⟩
    exact pow_le_pow_left₀ (D₁.chart p hp).hr₀.le (hch₁ p hp).2.2.2.2 2
  obtain ⟨D₂, hch₂, hrm₂, γ, hγ, hfree, hmeet⟩ :=
    exists_loop_of_level_arc h5 hf D₁ hcrit hp hε hεp₁ hpc hc₂ hcU₁ hy hyinj hy' hyball hy0 hJ
      hybot hyasc hγ₀ hper hlev harc hbot
  refine ⟨D₂, fun x hx => ?_, fun x hx => (hrm₂ x hx).trans (hrm₁ x hx), γ, hγ, hfree, hmeet⟩
  obtain ⟨h1, h2, h3, h4, h5'⟩ := hch₂ x hx
  obtain ⟨g1, g2, g3, g4, g5⟩ := hch₁ x hx
  exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4, h5'.trans g5⟩

end Circle

def isLoopConfig (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] (f : M → ℝ) (a b : ℝ) (p : M) : Prop :=
  MorseStrip I f a b ∧ ∃ crit : Finset M, (∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
  ∃ (hp : p ∈ crit) (D : GradientLikeStrip I f a b crit), (D.chart p hp).k = 1 ∧
  ∃ ε δ c₂ c₃ : ℝ, 0 < ε ∧ ε < δ ∧ a < c₂ ∧ c₂ < c₃ ∧ c₃ < b ∧ f p + 4 * δ < c₂ ∧
    isFineAt D δ ∧ (∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) ∧
    (∀ x ∈ crit, f x + 4 * δ < c₂ ∨ c₃ + 4 * δ < f x) ∧
    (∀ x ∈ crit, x ≠ p → 4 * δ < |f x - f p|) ∧
    (∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2) ∧ (∀ x hx, c₂ < f x → 3 ≤ (D.chart x hx).k) ∧
    ∃ γ : ℝ → M, isLevelLoop I f c₂ γ ∧ (∀ θ, descendsFreely D (c₂ - (f p + ε)) (γ θ)) ∧
      meetsRightOnce D p hp ε c₂ γ

section CircleConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ}

theorem exists_loop_config [SigmaCompactSpace M] (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hV₀ : ConnectedSpace (f ⁻¹' {a})) {p : M}
    (hp : f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ morseIndex I f p = 1)
    (htop : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f x = 1 → x ≠ p →
      f x < f p) :
    isLoopConfig I f a b p := by
  classical
  have _ := htop
  set crit : Finset M := (hf.finite_critical.subset fun x hx =>
    ⟨Ioo_subset_Icc_self hx.1, hx.2⟩ :
      {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}.Finite).toFinset with hcritdef
  have hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := fun x => by
    rw [hcritdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hpc : p ∈ crit := (hcrit p).2 ⟨hp.1, hp.2.1⟩
  obtain ⟨x₁, hx₁, hx₁max⟩ := Finset.exists_max_image
    (crit.filter fun x => morseIndex I f x ≤ 2) f
    ⟨p, Finset.mem_filter.2 ⟨hpc, by rw [hp.2.2]; norm_num⟩⟩
  obtain ⟨hx₁c, hx₁i⟩ := Finset.mem_filter.1 hx₁
  have hlow : ∀ x ∈ crit, morseIndex I f x ≤ 2 → f x ≤ f x₁ := fun x hx hxi =>
    hx₁max x (Finset.mem_filter.2 ⟨hx, hxi⟩)
  have hfpx₁ : f p ≤ f x₁ := hlow p hpc (by rw [hp.2.2]; norm_num)
  have hx₁b : f x₁ < b := ((hcrit x₁).1 hx₁c).1.2
  obtain ⟨δ₀, hδ₀, hgap⟩ := DistinctSelfIndexing.exists_index_gap hf hsi
  have hhigh : ∀ x ∈ crit, ¬ morseIndex I f x ≤ 2 → f x₁ + δ₀ ≤ f x := fun x hx hxi => by
    have hx' := (hcrit x).1 hx
    have hx₁' := (hcrit x₁).1 hx₁c
    have := hgap x₁ x hx₁'.1 hx'.1 hx₁'.2 hx'.2 (by omega)
    linarith
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_forall_finset (crit.erase p) (fun x => |f x - f p|)
    (fun x hx => by
      obtain ⟨hxp, hx⟩ := Finset.mem_erase.1 hx
      refine abs_pos.2 (sub_ne_zero.2 fun h => hxp ?_)
      exact hinj ((hcrit x).1 hx) ((hcrit p).1 hpc) h)
  set δ : ℝ := min (min δ₀ ρ) (b - f x₁) / 16 with hδdef
  have hδ : 0 < δ := by
    have : 0 < min (min δ₀ ρ) (b - f x₁) := lt_min (lt_min hδ₀ hρ) (by linarith)
    positivity
  have hδ₁ : 16 * δ ≤ δ₀ := by
    rw [hδdef]; linarith [min_le_left (min δ₀ ρ) (b - f x₁), min_le_left δ₀ ρ]
  have hδ₂ : 16 * δ ≤ ρ := by
    rw [hδdef]; linarith [min_le_left (min δ₀ ρ) (b - f x₁), min_le_right δ₀ ρ]
  have hδ₃ : 16 * δ ≤ b - f x₁ := by
    rw [hδdef]; linarith [min_le_right (min δ₀ ρ) (b - f x₁)]
  obtain ⟨D, hfine, ε, hε, hεδ, hεp, harms⟩ := exists_good_gradientLike hf hsi hinj hcrit
    (fun x hx => by
      have hx' := (hcrit x).1 hx
      exact (hidx x hx'.1 hx'.2).1) hδ
  have hkp : (D.chart p hpc).k = 1 := by
    rw [← (D.chart p hpc).hkidx]; exact hp.2.2
  set c₂ : ℝ := f x₁ + 5 * δ with hc₂def
  set c₃ : ℝ := f x₁ + 6 * δ with hc₃def
  have hkidx : ∀ x (hx : x ∈ crit), (D.chart x hx).k = morseIndex I f x := fun x hx =>
    (D.chart x hx).hkidx.symm
  have hdn : ∀ x hx, f x < c₂ → (D.chart x hx).k ≤ 2 := fun x hx hfx => by
    rw [hkidx x hx]
    by_contra h
    have := hhigh x hx h
    linarith
  have hup : ∀ x hx, c₂ < f x → 3 ≤ (D.chart x hx).k := fun x hx hfx => by
    rw [hkidx x hx]
    by_contra h
    have := hlow x hx (by omega)
    linarith
  have hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c₂ := fun x hx y hy => by
    have hy' := hfine x hx (D.closedSmallBall_subset_image_ball x hx hy)
    obtain ⟨hy1, hy2⟩ := hy'
    by_cases hxi : morseIndex I f x ≤ 2
    · have := hlow x hx hxi
      intro h; linarith
    · have := hhigh x hx hxi
      intro h; linarith
  obtain ⟨D', hch, hrm, γ, hγ, hfree, hmeet⟩ :=
    exists_level_loop h5 hf D hcrit hpc hkp hε (hεp p hpc) (by linarith) (by linarith) hcU hdn
      (harms p hpc hkp) hV₀
  refine ⟨hf, crit, hcrit, hpc, D', (hch p hpc).2.1.trans hkp, ε, δ, c₂, c₃, hε, hεδ,
    by linarith [((hcrit p).1 hpc).1.1], by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_,
    ?_, ?_, γ, hγ, hfree, hmeet⟩
  · intro x hx
    rw [(hch x hx).1, (hch x hx).2.2.2.1]
    exact hfine x hx
  · intro x hx
    refine ⟨lt_of_le_of_lt ?_ (hεp x hx).1, by rw [hrm x hx]; exact (hεp x hx).2⟩
    exact pow_le_pow_left₀ (D'.chart x hx).hr₀.le (hch x hx).2.2.2.2 2
  · intro x hx
    by_cases hxi : morseIndex I f x ≤ 2
    · left; have := hlow x hx hxi; linarith
    · right; have := hhigh x hx hxi; linarith
  · intro x hx hxp
    have := hρle x (Finset.mem_erase.2 ⟨hxp, hx⟩)
    linarith
  · intro x hx hfx
    rw [(hch x hx).2.1]; exact hdn x hx hfx
  · intro x hx hfx
    rw [(hch x hx).2.1]; exact hup x hx hfx

end CircleConfig

end

end IndexOnePartner

end DifferentialGeometry.Topology
