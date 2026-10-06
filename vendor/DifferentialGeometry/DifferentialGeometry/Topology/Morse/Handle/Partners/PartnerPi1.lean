module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerCircle

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

section Pi1

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_strip_nullhomotopy (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) {c : ℝ} (hc : c ∈ Ioo a b) {γ : ℝ → M}
    (hγ : Continuous γ) (hper : Periodic γ 1) (hlev : ∀ θ, f (γ θ) = c) :
    ∃ (F : ℝ → ℝ → M) (δ : ℝ), 0 < δ ∧ Continuous (uncurry F) ∧
      (∀ θ s, F (θ + 1) s = F θ s) ∧ (∀ θ s, f (F θ s) ∈ Icc (a + δ) (b - δ)) ∧
      (∀ θ s, s ≤ 1 / 4 → F θ s = γ θ) ∧ ∀ θ s, 3 / 4 ≤ s → F θ s = γ 0 := by
  classical
  have hfc : Continuous f := hf.smooth.continuous
  obtain ⟨hca, hcb⟩ := hc
  set C : Set M := D.closedSmallBalls with hC
  have hCc : IsCompact C := isCompact_iUnion fun q => D.isCompact_closedSmallBall q.1 q.2
  have hCs : C ⊆ f ⁻¹' Ioo a b :=
    iUnion_subset fun q => (D.closedSmallBall_subset_image_ball q.1 q.2).trans (D.inStrip q.1 q.2)
  obtain ⟨η, hη, hηC⟩ : ∃ η : ℝ, 0 < η ∧ ∀ x ∈ C, η ≤ f x - a ∧ η ≤ b - f x := by
    rcases C.eq_empty_or_nonempty with hne | hne
    · exact ⟨1, one_pos, fun x hx => by simp [hne] at hx⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hCc.exists_isMinOn hne hfc.continuousOn
      obtain ⟨x₁, hx₁, hmax⟩ := hCc.exists_isMaxOn hne hfc.continuousOn
      have h0 := hCs hx₀
      have h1 := hCs hx₁
      refine ⟨min (f x₀ - a) (b - f x₁), lt_min (by linarith [h0.1]) (by linarith [h1.2]),
        fun x hx => ⟨?_, ?_⟩⟩
      · have := isMinOn_iff.1 hmin x hx
        linarith [min_le_left (f x₀ - a) (b - f x₁)]
      · have := isMaxOn_iff.1 hmax x hx
        linarith [min_le_right (f x₀ - a) (b - f x₁)]
  set δ₀ : ℝ := min (η / 2) (min ((c - a) / 2) ((b - c) / 2)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ₀η : δ₀ ≤ η / 2 := min_le_left _ _
  have hδ₀a : δ₀ ≤ (c - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀b : δ₀ ≤ (b - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have havoid : ∀ y, f y ∈ Icc a (a + δ₀) ∪ Icc (b - δ₀) b → ∀ p hp, y ∉ D.smallBall p hp := by
    intro y hy p hp hmem
    have hyC : y ∈ C := mem_iUnion.2 ⟨⟨p, hp⟩, D.smallBall_subset_closedSmallBall p hp hmem⟩
    obtain ⟨h1, h2⟩ := hηC y hyC
    rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith
  let lam : ℝ → ℝ := fun v => max 0 (a + δ₀ - v) - max 0 (v - (b - δ₀))
  have hlamc : Continuous lam := by fun_prop
  have hP : ∀ x, f x ∈ Icc a b → f (D.flow (-lam (f x)) x) ∈ Icc (a + δ₀) (b - δ₀) := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    by_cases h1 : f x ≤ a + δ₀
    · have hl : lam (f x) = a + δ₀ - f x := by
        simp only [lam]
        rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      have key := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hf.smooth (x := x)
        (T := -lam (f x)) ⟨hxa, hxb⟩ (by rw [hl]; constructor <;> linarith) (by
          intro y hy
          rw [hl, mem_uIcc] at hy
          refine havoid y (Or.inl ?_)
          rcases hy with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> constructor <;> linarith)
        (-lam (f x)) right_mem_uIcc
      rw [key, hl]
      constructor <;> linarith
    by_cases h2 : b - δ₀ ≤ f x
    · have hl : lam (f x) = -(f x - (b - δ₀)) := by
        simp only [lam]
        rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
      have key := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D) hf.smooth (x := x)
        (T := -lam (f x)) ⟨hxa, hxb⟩ (by rw [hl]; constructor <;> linarith) (by
          intro y hy
          rw [hl, mem_uIcc] at hy
          refine havoid y (Or.inr ?_)
          rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith)
        (-lam (f x)) right_mem_uIcc
      rw [key, hl]
      constructor <;> linarith
    · push Not at h1 h2
      have hl : lam (f x) = 0 := by
        simp only [lam]
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        ring
      rw [hl, neg_zero, D.flow_zero]
      exact ⟨h1.le, h2.le⟩
  have hPid : ∀ x, f x = c → D.flow (-lam (f x)) x = x := by
    intro x hx
    have hl : lam (f x) = 0 := by
      simp only [lam]
      rw [hx, max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    rw [hl, neg_zero, D.flow_zero]
  have hmem : ∀ θ, γ θ ∈ f ⁻¹' Icc a b := fun θ => by
    change f (γ θ) ∈ Icc a b
    rw [hlev]
    exact ⟨hca.le, hcb.le⟩
  let x₀ : f ⁻¹' Icc a b := ⟨γ 0, hmem 0⟩
  let p : Path x₀ x₀ :=
    { toFun := fun t => ⟨γ t, hmem t⟩
      continuous_toFun := (hγ.comp continuous_subtype_val).subtype_mk _
      source' := rfl
      target' := Subtype.ext (by simpa using hper 0) }
  obtain ⟨Hh⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x₀)
  let G : ℝ → ℝ → M := fun s t =>
    ((Hh ((projIcc 0 1 zero_le_one (2 * s - 1 / 2) : unitInterval),
      (projIcc 0 1 zero_le_one t : unitInterval)) : f ⁻¹' Icc a b) : M)
  have hGc : Continuous (uncurry G) := by
    refine continuous_subtype_val.comp (Hh.continuous.comp ?_)
    exact (continuous_projIcc.comp ((continuous_const.mul continuous_fst).sub continuous_const)).prodMk
      (continuous_projIcc.comp continuous_snd)
  have hG01 : ∀ s, G s 0 = G s 1 := by
    intro s
    simp only [G, projIcc_left, projIcc_right]
    have e0 := Hh.source (projIcc 0 1 zero_le_one (2 * s - 1 / 2))
    have e1 := Hh.target (projIcc 0 1 zero_le_one (2 * s - 1 / 2))
    exact congrArg Subtype.val (e0.trans e1.symm)
  let F₀ : ℝ → ℝ → M := fun θ s => G s (Int.fract θ)
  have hF₀c : Continuous (uncurry F₀) :=
    (ContinuousOn.comp_fract' hGc.continuousOn hG01).comp continuous_swap
  have hF₀mem : ∀ θ s, f (F₀ θ s) ∈ Icc a b := fun θ s => (Hh _).2
  refine ⟨fun θ s => D.flow (-lam (f (F₀ θ s))) (F₀ θ s), δ₀, hδ₀pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.continuous_flow_joint.comp
      (((hlamc.comp (hfc.comp hF₀c)).neg).prodMk hF₀c)
  · intro θ s
    simp only [F₀, Int.fract_add_one]
  · intro θ s
    exact hP _ (hF₀mem θ s)
  · intro θ s hs
    have hF : F₀ θ s = γ θ := by
      simp only [F₀, G]
      rw [projIcc_of_le_left zero_le_one (by linarith),
        projIcc_of_mem zero_le_one ⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩]
      have e := Hh.apply_zero (⟨Int.fract θ, Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩ : unitInterval)
      have e' := congrArg Subtype.val e
      refine e'.trans ?_
      change γ (Int.fract θ) = γ θ
      rw [← Int.self_sub_floor]
      simpa using hper.sub_int_mul_eq (x := θ) ⌊θ⌋
    simp only
    rw [hF]
    exact hPid _ (hlev θ)
  · intro θ s hs
    have hF : F₀ θ s = γ 0 := by
      simp only [F₀, G]
      rw [projIcc_of_right_le zero_le_one (by linarith)]
      have e := Hh.apply_one (projIcc 0 1 zero_le_one (Int.fract θ))
      exact congrArg Subtype.val e
    simp only
    rw [hF]
    exact hPid _ (hlev 0)

theorem exists_level_nullhomotopy (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) {c : ℝ} (hc : c ∈ Ioo a b)
    (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c)
    (hdn : ∀ x hx, f x < c → (D.chart x hx).k ≤ 2) (hup : ∀ x hx, c < f x → 3 ≤ (D.chart x hx).k)
    {γ : ℝ → M} (hγ : isLevelLoop I f c γ) :
    ∃ Hm : ℝ → ℝ → M, isLevelHomotopy f c Hm γ (fun _ => γ 0) := by
  obtain ⟨hγper, hγsm, -, -, hγlev⟩ := hγ
  have hγc : Continuous γ := hγsm.continuous
  have hfc : Continuous f := hf.smooth.continuous
  obtain ⟨F, δ, hδ, hFc, hFper, hFstrip, hF0, hF1⟩ :=
    exists_strip_nullhomotopy hf D hW hc hγc hγper hγlev
  set U : Set (ℝ × ℝ) := {z | z.2 < 1 / 4} ∪ {z | 3 / 4 < z.2} with hUdef
  set P : Set (ℝ × ℝ) := {z | z.2 ≤ 1 / 8} ∪ {z | 7 / 8 ≤ z.2} with hPdef
  set O : Set (M × M) := {p | |f p.1 - f p.2| < δ / 2} with hOdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd)
  have hUper : ∀ θ s, (θ, s) ∈ U ↔ (θ + 1, s) ∈ U := fun θ s => Iff.rfl
  have hFU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry F) U := by
    intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    rcases hz with hz | hz
    · have hev : (fun w : ℝ × ℝ => γ w.1) =ᶠ[𝓝 z] uncurry F := by
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds
          (show z ∈ {w : ℝ × ℝ | w.2 < 1 / 4} from hz)] with w hw
        exact (hF0 w.1 w.2 (le_of_lt hw)).symm
      have hsm : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun w : ℝ × ℝ => γ w.1) z :=
        (hγsm.comp (contDiff_fst.contMDiff (n := ∞))).contMDiffAt
      exact hsm.congr_of_eventuallyEq hev.symm
    · have hev : (fun _ : ℝ × ℝ => γ 0) =ᶠ[𝓝 z] uncurry F := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds
          (show z ∈ {w : ℝ × ℝ | 3 / 4 < w.2} from hz)] with w hw
        exact (hF1 w.1 w.2 (le_of_lt hw)).symm
      exact contMDiffAt_const.congr_of_eventuallyEq hev.symm
  have hPc : IsClosed P :=
    (isClosed_le continuous_snd continuous_const).union (isClosed_le continuous_const continuous_snd)
  have hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P := fun θ s => Iff.rfl
  have hPU : P ⊆ U := by
    rintro z (hz | hz)
    · left; change z.2 < 1 / 4; have : z.2 ≤ 1 / 8 := hz; linarith
    · right; change 3 / 4 < z.2; have : 7 / 8 ≤ z.2 := hz; linarith
  have hPs : ∀ θ s, s ∉ Ioo (0 : ℝ) 1 → (θ, s) ∈ P := by
    intro θ s hs
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · left; change s ≤ 1 / 8; linarith
    · right; change 7 / 8 ≤ s; linarith
  have hOo : IsOpen O :=
    isOpen_lt ((hfc.comp continuous_fst).sub (hfc.comp continuous_snd)).abs continuous_const
  have hdiag : ∀ x, (x, x) ∈ O := by
    intro x
    change |f x - f x| < δ / 2
    rw [sub_self, abs_zero]; linarith
  obtain ⟨G, hGsm, hGper, hGP, hGO⟩ :=
    exists_smooth_approx hFc hFper hUo hUper hFU hPc hPper hPU hPs hOo hdiag
  have hFPlev : ∀ θ s, (θ, s) ∈ P → f (F θ s) = c := by
    rintro θ s (hs | hs)
    · have : s ≤ 1 / 8 := hs
      rw [hF0 θ s (by linarith)]; exact hγlev θ
    · have : 7 / 8 ≤ s := hs
      rw [hF1 θ s (by linarith)]; exact hγlev 0
  obtain ⟨⟨V, hVo, hVeq⟩, r, hrc, hrlev, hrid⟩ := exists_levelRetraction hf D hc hcU
  set T : Set M := {x | f x ∈ Icc a b ∧ ∀ t, f (D.flow t x) ≠ c} with hTdef
  have hTc : IsClosed T := by
    have hcl : IsClosed (f ⁻¹' Icc a b ∩ Vᶜ) :=
      (isClosed_Icc.preimage hfc).inter hVo.isClosed_compl
    convert hcl using 1
    ext x
    simp only [hTdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hx, hnt⟩
      refine ⟨hx, fun hxV => ?_⟩
      have : x ∈ {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c} := by
        rw [hVeq]; exact ⟨hxV, hx⟩
      obtain ⟨t, ht⟩ := this.2
      exact hnt t ht
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, fun t ht => hxV ?_⟩
      have : x ∈ {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c} := ⟨hx, t, ht⟩
      rw [hVeq] at this
      exact this.1
  have hT₁ := isThin_nonReaching_below hf D hcrit hc hcU (kdn := 2) hdn
  have hT₂ := isThin_nonReaching_above hf D hcrit hc hcU (kup := 3) hup
  have hT₁₂ := isThin_union_of_le (d := n - 3) (by omega) le_rfl hT₁ hT₂
  have hTthin : isThin I (n - 3) T := by
    obtain ⟨ι, hι, Us, g, hUs, hg, hcov⟩ := hT₁₂
    refine ⟨ι, hι, Us, g, hUs, hg, fun x hx => hcov ?_⟩
    obtain ⟨⟨hxa, hxb⟩, hnt⟩ := hx
    rcases le_total (f x) c with hxc | hxc
    · exact Or.inl ⟨⟨hxa, hxc⟩, hnt⟩
    · exact Or.inr ⟨⟨hxc, hxb⟩, hnt⟩
  have hd : n - 3 + 2 < n := by omega
  have hPT : ∀ θ s, (θ, s) ∈ P → G θ s ∉ T := by
    intro θ s hz hGT
    rw [hGP θ s hz] at hGT
    exact hGT.2 0 (by rw [D.flow_zero]; exact hFPlev θ s hz)
  obtain ⟨G', hG'sm, hG'per, hG'P, hG'T, hG'O⟩ :=
    exists_avoid_thin hGsm hGper hTc hTthin hd hPc hPper hPs hPT hOo hdiag
  have hG'strip : ∀ θ s, f (G' θ s) ∈ Icc a b := by
    intro θ s
    have h1 := hFstrip θ s
    have h2 : |f (F θ s) - f (G θ s)| < δ / 2 := hGO θ s
    have h3 : |f (G θ s) - f (G' θ s)| < δ / 2 := hG'O θ s
    rw [abs_lt] at h2 h3
    obtain ⟨h1a, h1b⟩ := h1
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  have hG'reach : ∀ θ s, G' θ s ∈ {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c} := by
    intro θ s
    refine ⟨hG'strip θ s, ?_⟩
    by_contra hne
    exact hG'T θ s ⟨hG'strip θ s, fun t ht => hne ⟨t, ht⟩⟩
  refine ⟨fun θ s => r (G' θ s), ?_, ?_, ?_, ?_, ?_⟩
  · exact hrc.comp_continuous hG'sm.continuous (fun z => hG'reach z.1 z.2)
  · intro θ s
    change r (G' (θ + 1) s) = r (G' θ s)
    rw [hG'per]
  · intro θ s
    exact (hrlev _ (hG'reach θ s).1 (hG'reach θ s).2).1
  · intro θ
    have hz : (θ, (0 : ℝ)) ∈ P := Or.inl (show (0 : ℝ) ≤ 1 / 8 by norm_num)
    change r (G' θ 0) = γ θ
    rw [hG'P θ 0 hz, hGP θ 0 hz, hF0 θ 0 (by norm_num)]
    exact hrid _ (hγlev θ)
  · intro θ
    have hz : (θ, (1 : ℝ)) ∈ P := Or.inr (show (7 / 8 : ℝ) ≤ 1 by norm_num)
    change r (G' θ 1) = γ 0
    rw [hG'P θ 1 hz, hGP θ 1 hz, hF1 θ 1 (by norm_num)]
    exact hrid _ (hγlev 0)

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem isLevelHomotopy.trans {c : ℝ} {H₁ H₂ : ℝ → ℝ → M} {γ β δ : ℝ → M}
    (h₁ : isLevelHomotopy f c H₁ γ β) (h₂ : isLevelHomotopy f c H₂ β δ) :
    ∃ H : ℝ → ℝ → M, isLevelHomotopy f c H γ δ := by
  obtain ⟨hc₁, hper₁, hlev₁, h0₁, h1₁⟩ := h₁
  obtain ⟨hc₂, hper₂, hlev₂, h0₂, h1₂⟩ := h₂
  refine ⟨fun θ s => if s ≤ 1 / 2 then H₁ θ (2 * s) else H₂ θ (2 * s - 1), ?_, ?_, ?_, ?_, ?_⟩
  · have hA : Continuous fun p : ℝ × ℝ => H₁ p.1 (2 * p.2) :=
      hc₁.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))
    have hB : Continuous fun p : ℝ × ℝ => H₂ p.1 (2 * p.2 - 1) :=
      hc₂.comp (continuous_fst.prodMk ((continuous_const.mul continuous_snd).sub continuous_const))
    have hC : Continuous fun p : ℝ × ℝ =>
        if p.2 ≤ 1 / 2 then H₁ p.1 (2 * p.2) else H₂ p.1 (2 * p.2 - 1) :=
      Continuous.if_le hA hB continuous_snd continuous_const (fun p hp => by
        rw [hp]
        norm_num
        rw [h1₁, h0₂])
    exact hC
  · intro θ s
    simp only [hper₁, hper₂]
  · intro θ s
    dsimp only
    split_ifs
    · exact hlev₁ _ _
    · exact hlev₂ _ _
  · intro θ
    simp [h0₁]
  · intro θ
    norm_num [h1₂]

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem isLevelHomotopy.symm {c : ℝ} {H : ℝ → ℝ → M} {γ β : ℝ → M}
    (h : isLevelHomotopy f c H γ β) : isLevelHomotopy f c (fun θ s => H θ (1 - s)) β γ := by
  obtain ⟨hc, hper, hlev, h0, h1⟩ := h
  refine ⟨?_, fun θ s => hper θ (1 - s), fun θ s => hlev θ (1 - s), fun θ => ?_, fun θ => ?_⟩
  · exact hc.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))
  · simpa using h1 θ
  · simpa using h0 θ

end Pi1

end

end IndexOnePartner

end DifferentialGeometry.Topology
