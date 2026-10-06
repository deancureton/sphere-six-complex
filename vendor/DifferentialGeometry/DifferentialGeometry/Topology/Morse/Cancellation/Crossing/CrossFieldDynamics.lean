module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldDefs

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

section Generic

variable {a b : ℝ} {crit : Finset M}

omit [I.Boundaryless] [T2Space M] in
theorem continuousOn_dfV {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {L : M → ℝ} {W : Set M} (hW : IsOpen W) (hL : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ L W) :
    ContinuousOn (dfV I L V) W := by
  have hcont : ContinuousOn (tangentMapWithin I 𝓘(ℝ, ℝ) L W)
      (Bundle.TotalSpace.proj ⁻¹' W) :=
    hL.continuousOn_tangentMapWithin (by simp) hW.uniqueMDiffOn
  have hσ : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I M)) W :=
    hV.continuous.continuousOn
  have h1 : ContinuousOn (fun x => ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ))
      (tangentMapWithin I 𝓘(ℝ, ℝ) L W (⟨x, V x⟩ : TangentBundle I M))).2) W :=
    continuous_snd.comp_continuousOn
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp_continuousOn
        (hcont.comp hσ (fun x hx => hx)))
  refine h1.congr fun x hx => ?_
  change dfV I L V x = mfderivWithin I 𝓘(ℝ, ℝ) L W x (V x)
  rw [mfderivWithin_of_isOpen hW hx]
  rfl

theorem isOpen_mfderiv_ne_zero {L : M → ℝ} {W : Set M} (hW : IsOpen W)
    (hL : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ L W) :
    IsOpen {x | x ∈ W ∧ mfderiv I 𝓘(ℝ, ℝ) L x ≠ 0} := by
  have _hB : I.Boundaryless := inferInstance
  have _hT : T2Space M := inferInstance
  rw [isOpen_iff_forall_mem_open]
  rintro x₀ ⟨hx₀W, hx₀⟩
  obtain ⟨v', hv'⟩ : ∃ v' : TangentSpace I x₀, mfderiv I 𝓘(ℝ, ℝ) L x₀ v' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀ (ContinuousLinearMap.ext fun v => by simpa using hcon v)
  set e := trivializationAt (Fin n → ℝ) (TangentSpace I : M → Type _) x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x₀
  set w : Fin n → ℝ := (e (⟨x₀, v'⟩ : TangentBundle I M)).2 with hw
  have hσ : ContinuousOn (fun x : M => (⟨x, e.symm x w⟩ : TangentBundle I M)) e.baseSet :=
    e.continuousOn_symm.comp
      ((continuous_id.prodMk (continuous_const (y := w))).continuousOn)
      (fun x hx => ⟨hx, mem_univ _⟩)
  have hcont : ContinuousOn (tangentMapWithin I 𝓘(ℝ, ℝ) L W)
      (Bundle.TotalSpace.proj ⁻¹' W) :=
    hL.continuousOn_tangentMapWithin (by simp) hW.uniqueMDiffOn
  set g : M → ℝ := fun x => ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ))
      (tangentMapWithin I 𝓘(ℝ, ℝ) L W (⟨x, e.symm x w⟩ : TangentBundle I M))).2 with hg
  have hgc : ContinuousOn g (W ∩ e.baseSet) :=
    continuous_snd.comp_continuousOn
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp_continuousOn
        (hcont.comp (hσ.mono inter_subset_right) (fun x hx => hx.1)))
  have hgx : ∀ x ∈ W, g x = mfderiv I 𝓘(ℝ, ℝ) L x (e.symm x w) := by
    intro x hx
    change mfderivWithin I 𝓘(ℝ, ℝ) L W x (e.symm x w) = _
    rw [mfderivWithin_of_isOpen hW hx]
  refine ⟨(W ∩ e.baseSet) ∩ g ⁻¹' {0}ᶜ, ?_, ?_, ?_⟩
  · rintro x ⟨⟨hxW, _⟩, hgx0⟩
    refine ⟨hxW, fun h0 => hgx0 ?_⟩
    rw [mem_singleton_iff, hgx x hxW, h0]
    rfl
  · exact hgc.isOpen_inter_preimage (hW.inter e.open_baseSet) isOpen_compl_singleton
  · refine ⟨⟨hx₀W, hx₀e⟩, ?_⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    rw [hgx x₀ hx₀W, hw, e.symm_apply_apply_mk hx₀e]
    exact hv'

theorem eq_flow_of_avoid (D : GradientLikeStrip I f a b crit) {V' : (x : M) → TangentSpace I x}
    {K : Set M} (hK : IsClosed K) (hagree : ∀ x ∉ K, V' x = D.V x) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V') {s T : ℝ} (hsT : s ≤ T) (havoid : ∀ t ∈ Ico s T, γ t ∉ K) :
    ∀ t ∈ Icc s T, γ t = D.flow (t - s) (γ s) := by
  have hT0 : (0 : ℝ) ≤ T - s := sub_nonneg.2 hsT
  set δ : ℝ → M := fun u => γ (u + s) with hδdef
  have hδ : IsMIntegralCurve δ V' := hγ.comp_add s
  have hQ : IsClosed {u : ℝ | δ u = D.flow u (γ s)} :=
    isClosed_eq hδ.continuous (D.isMIntegralCurve_flow (γ s)).continuous
  have hsub : Icc 0 (T - s) ⊆ {u : ℝ | δ u = D.flow u (γ s)} := by
    refine Icc_subset_of_isClosed_of_step hQ (by simp [hδdef]) fun u hu hIcc => ?_
    have hxt : δ u = D.flow u (γ s) := hIcc (right_mem_Icc.2 hu.1)
    have hnot : δ u ∉ K := havoid (u + s) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hc₁ : IsMIntegralCurveAt (fun v => D.flow v (γ s)) D.V u :=
      (D.isMIntegralCurve_flow (γ s)).isMIntegralCurveAt u
    have hc₂ : IsMIntegralCurveAt δ D.V u := by
      have hev : ∀ᶠ v in 𝓝 u, δ v ∉ K :=
        hδ.continuous.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hnot)
      filter_upwards [hev] with v hv
      have := hδ v
      rwa [hagree _ hv] at this
    have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      D.smooth_one.contMDiffAt hc₁ hc₂ hxt.symm
    exact nhdsWithin_le_nhds (heq.mono fun v hv => hv.symm)
  intro t ht
  have := hsub (a := t - s) ⟨sub_nonneg.2 ht.1, sub_le_sub_right ht.2 s⟩
  simpa [hδdef] using this

omit [I.Boundaryless] [T2Space M] in
theorem exists_exit_of_lyapunov {V' : (x : M) → TangentSpace I x}
    (hV' : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsCompact U) {L : M → ℝ} (hL : ContMDiff I 𝓘(ℝ, ℝ) ∞ L)
    (hLpos : ∀ x ∈ U, 0 < dfV I L V' x) {γ : ℝ → M} (hγ : IsMIntegralCurve γ V') (t₀ : ℝ) :
    ∃ t, t₀ < t ∧ γ t ∉ U := by
  by_contra hcon
  push Not at hcon
  set t₁ : ℝ := t₀ + 1 with ht₁
  have ht₀₁ : t₀ < t₁ := by rw [ht₁]; linarith
  have hne : U.Nonempty := ⟨γ t₁, hcon t₁ ht₀₁⟩
  have hcont : ContinuousOn (dfV I L V') U :=
    (continuousOn_dfV hV' isOpen_univ hL.contMDiffOn).mono (subset_univ U)
  obtain ⟨xm, hxm, hmin⟩ := hU.exists_isMinOn hne hcont
  set m : ℝ := dfV I L V' xm with hm
  have hm0 : 0 < m := hLpos xm hxm
  obtain ⟨xM, hxM, hmax⟩ := hU.exists_isMaxOn hne hL.continuous.continuousOn
  set B : ℝ := L xM with hB
  have hderiv : ∀ t, HasDerivAt (fun r => L (γ r)) (dfV I L V' (γ t)) t := fun t =>
    hasDerivAt_comp_integralCurve hγ (hL.mdifferentiableAt (by simp))
  have hcontOn : ContinuousOn (fun r => L (γ r)) (Ici t₁) := fun t _ =>
    (hderiv t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun r => L (γ r)) (interior (Ici t₁)) := fun t _ =>
    (hderiv t).differentiableAt.differentiableWithinAt
  have hge : ∀ t ∈ interior (Ici t₁), m ≤ deriv (fun r => L (γ r)) t := by
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hderiv t).deriv]
    exact hmin (hcon t (by linarith))
  have key := (convex_Ici t₁).mul_sub_le_image_sub_of_le_deriv hcontOn hdiff hge
  set y : ℝ := t₁ + (B - L (γ t₁) + 1) / m with hy
  have hBt₁ : L (γ t₁) ≤ B := hmax (hcon t₁ ht₀₁)
  have ht₁y : t₁ ≤ y := by
    have : 0 ≤ (B - L (γ t₁) + 1) / m := div_nonneg (by linarith) hm0.le
    rw [hy]; linarith
  have h1 := key t₁ (mem_Ici.2 le_rfl) y ht₁y ht₁y
  have h2 : m * (y - t₁) = B - L (γ t₁) + 1 := by
    rw [hy]; field_simp; ring
  have hyU : L (γ y) ≤ B := hmax (hcon y (by linarith))
  linarith

omit [I.Boundaryless] [T2Space M] in
theorem exists_unit_collar (D : GradientLikeStrip I f a b crit) (hf : MorseStrip I f a b)
    {U : Set M} (hU : IsCompact U) (hUs : U ⊆ f ⁻¹' Ioo a b) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ 2 * η₀ < b - a ∧
      ∀ x, f x ∈ Icc a (a + η₀) ∪ Icc (b - η₀) b → dfV I f D.V x = -1 ∧ x ∉ U := by
  have hab : a < b := hf.lt
  set C : Set M := U ∪ D.closedSmallBalls with hC
  have hCc : IsCompact C :=
    hU.union (isCompact_iUnion fun q => D.isCompact_closedSmallBall q.1 q.2)
  have hCs : C ⊆ f ⁻¹' Ioo a b := by
    refine union_subset hUs (iUnion_subset fun q => ?_)
    exact (D.closedSmallBall_subset_image_ball q.1 q.2).trans (D.inStrip q.1 q.2)
  set g : M → ℝ := fun x => min (f x - a) (b - f x) with hg
  have hgc : Continuous g := by
    have := hf.smooth.continuous
    fun_prop
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, δ ≤ g x := by
    rcases C.eq_empty_or_nonempty with hne | hne
    · exact ⟨1, one_pos, fun x hx => by simp [hne] at hx⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hCc.exists_isMinOn hne hgc.continuousOn
      have hx₀s := hCs hx₀
      exact ⟨g x₀, lt_min (by linarith [hx₀s.1]) (by linarith [hx₀s.2]),
        fun x hx => isMinOn_iff.1 hmin x hx⟩
  refine ⟨min (δ / 2) ((b - a) / 4), lt_min (by positivity) (by linarith), ?_, ?_⟩
  · have := min_le_right (δ / 2) ((b - a) / 4)
    linarith
  · intro x hx
    have hη₁ : min (δ / 2) ((b - a) / 4) ≤ δ / 2 := min_le_left _ _
    have hη₂ : min (δ / 2) ((b - a) / 4) ≤ (b - a) / 4 := min_le_right _ _
    have hxC : x ∉ C := by
      intro hxC
      have h1 := hδC x hxC
      have h2 : δ ≤ f x - a := h1.trans (min_le_left _ _)
      have h3 : δ ≤ b - f x := h1.trans (min_le_right _ _)
      rcases hx with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> linarith
    have hxab : f x ∈ Icc a b := by
      rcases hx with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> constructor <;> linarith
    refine ⟨?_, fun hxU => hxC (Or.inl hxU)⟩
    have hxB : x ∉ D.closedSmallBalls := fun h => hxC (Or.inr h)
    exact D.unit x hxab fun p hp hmem =>
      (D.notMem_closedSmallBalls_iff.1 hxB) p hp (D.smallBall_subset_closedSmallBall p hp hmem)

def noReturn (D : GradientLikeStrip I f a b crit) (U U' : Set M) : Prop :=
  ∀ x ∈ U', ∀ s t : ℝ, 0 ≤ s → s ≤ t → D.flow s x ∉ U → D.flow t x ∉ U'

theorem exists_noReturn (D : GradientLikeStrip I f a b crit) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) {Γ : Set M} (hΓ : IsCompact Γ)
    (hinv : ∀ t : ℝ, ∀ x ∈ Γ, D.flow t x ∈ Γ)
    (hdich : ∀ x, f x ∈ Icc a b → x ∉ Γ → x ∈ D.bottom ∨ ∃ t ≤ 0, b < f (D.flow t x))
    {U : Set M} (hU : IsOpen U) (hΓU : Γ ⊆ U) (hUs : U ⊆ f ⁻¹' Icc a b) :
    ∃ U' : Set M, IsOpen U' ∧ Γ ⊆ U' ∧ U' ⊆ U ∧ noReturn D U U' := by
  classical
  have hfc : Continuous f := hf.continuous
  set C : Set M := f ⁻¹' Icc a b \ U with hC
  have hCc : IsCompact C := hcomp.diff hU
  have key : ∀ z ∈ C, ∀ T : ℝ, ∃ O N : Set M, IsOpen O ∧ Γ ⊆ O ∧ N ∈ 𝓝 z ∧
      ∀ y ∈ N, ∀ τ ∈ uIcc 0 T, D.flow τ y ∉ O := by
    intro z hz T
    have hzΓ : z ∉ Γ := fun h => hz.2 (hΓU h)
    have hA : IsCompact ((fun τ => D.flow τ z) '' uIcc 0 T) :=
      isCompact_uIcc.image (D.continuous_flow_curve z)
    have hdisj : Disjoint Γ ((fun τ => D.flow τ z) '' uIcc 0 T) := by
      rw [Set.disjoint_left]
      rintro w hw ⟨τ, _, rfl⟩
      apply hzΓ
      have := hinv (-τ) _ hw
      rwa [D.flow_neg_flow] at this
    obtain ⟨O, N', hO, hN', hΓO, hAN', hON'⟩ :=
      SeparatedNhds.of_isCompact_isCompact hΓ hA hdisj
    have hev : ∀ᶠ y in 𝓝 z, ∀ τ ∈ uIcc 0 T, D.flow τ y ∈ N' := by
      refine isCompact_uIcc.eventually_forall_of_forall_eventually (x₀ := z)
        (P := fun y τ => D.flow τ y ∈ N') ?_
      intro τ hτ
      have hc : ContinuousAt (fun p : M × ℝ => D.flow p.2 p.1) (z, τ) :=
        (D.continuous_flow_joint.comp continuous_swap).continuousAt
      exact hc.preimage_mem_nhds (hN'.mem_nhds (hAN' ⟨τ, hτ, rfl⟩))
    refine ⟨O, _, hO, hΓO, hev, fun y hy τ hτ hmem => ?_⟩
    exact Set.disjoint_left.1 hON' hmem (hy τ hτ)
  have hpt : ∀ z ∈ C, ∃ O N : Set M, IsOpen O ∧ Γ ⊆ O ∧ N ∈ 𝓝 z ∧
      ((∀ y ∈ N, ∀ τ, 0 ≤ τ → f (D.flow τ y) ∈ Icc a b → D.flow τ y ∉ O) ∨
        (∀ y ∈ N, ∀ τ, τ ≤ 0 → f (D.flow τ y) ∈ Icc a b → D.flow τ y ∉ O)) := by
    intro z hz
    have hzΓ : z ∉ Γ := fun h => hz.2 (hΓU h)
    rcases hdich z hz.1 hzΓ with ⟨T, hT, hTa⟩ | ⟨T, hT, hTb⟩
    · obtain ⟨O, N, hO, hΓO, hN, hON⟩ := key z hz T
      have hN₂ : {y | f (D.flow T y) < a} ∈ 𝓝 z :=
        (hfc.comp (D.continuous_flow T)).continuousAt.preimage_mem_nhds
          (isOpen_Iio.mem_nhds hTa)
      refine ⟨O, N ∩ {y | f (D.flow T y) < a}, hO, hΓO, inter_mem hN hN₂, Or.inl ?_⟩
      intro y hy τ hτ hτab hmem
      rcases le_or_gt τ T with hτT | hτT
      · exact hON y hy.1 τ (by rw [uIcc_of_le hT]; exact ⟨hτ, hτT⟩) hmem
      · have h1 : f (D.flow τ y) ≤ f (D.flow T y) := GradientLikeStrip.f_flow_antitone hf y hτT.le
        have h2 : f (D.flow T y) < a := hy.2
        linarith [hτab.1]
    · obtain ⟨O, N, hO, hΓO, hN, hON⟩ := key z hz T
      have hN₂ : {y | b < f (D.flow T y)} ∈ 𝓝 z :=
        (hfc.comp (D.continuous_flow T)).continuousAt.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds hTb)
      refine ⟨O, N ∩ {y | b < f (D.flow T y)}, hO, hΓO, inter_mem hN hN₂, Or.inr ?_⟩
      intro y hy τ hτ hτab hmem
      rcases le_or_gt T τ with hτT | hτT
      · exact hON y hy.1 τ (by rw [uIcc_of_ge hT]; exact ⟨hτT, hτ⟩) hmem
      · have h1 : f (D.flow T y) ≤ f (D.flow τ y) := GradientLikeStrip.f_flow_antitone hf y hτT.le
        have h2 : b < f (D.flow T y) := hy.2
        linarith [hτab.2]
  choose! O N hO hΓO hN hcase using hpt
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover N fun z hz => hN z hz
  refine ⟨U ∩ ⋂ z ∈ t, O z,
    hU.inter (isOpen_biInter_finset fun z hz => hO z (htC z hz)), ?_, inter_subset_left, ?_⟩
  · intro w hw
    exact ⟨hΓU hw, mem_iInter₂.2 fun z hz => hΓO z (htC z hz) hw⟩
  · intro x hx s t' hs hst hsU htU'
    have hxab : f x ∈ Icc a b := hUs hx.1
    have htab : f (D.flow t' x) ∈ Icc a b := hUs htU'.1
    have hsab : f (D.flow s x) ∈ Icc a b :=
      ⟨htab.1.trans (GradientLikeStrip.f_flow_antitone hf x hst), (GradientLikeStrip.f_flow_le hf x hs).trans hxab.2⟩
    have hsC : D.flow s x ∈ C := ⟨hsab, hsU⟩
    obtain ⟨z, hz, hmem⟩ := mem_iUnion₂.1 (hcov hsC)
    have hzC := htC z hz
    rcases hcase z hzC with h | h
    · have := h _ hmem (t' - s) (sub_nonneg.2 hst)
      rw [D.flow_flow, add_sub_cancel] at this
      exact this htab (mem_iInter₂.1 htU'.2 z hz)
    · have := h _ hmem (-s) (neg_nonpos.2 hs)
      rw [D.flow_neg_flow] at this
      exact this hxab (mem_iInter₂.1 hx.2 z hz)

theorem reaches_bottom_of_lyapunov (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ r hr, (D.chart r hr).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm r hr ^ 2)
    {U U' K : Set M} (hU : IsCompact U) (hU'o : IsOpen U') (hU'U : U' ⊆ U)
    (hnr : noReturn D U U') (hK : IsCompact K) (hKU' : K ⊆ U') (hKs : K ⊆ f ⁻¹' Ioo a b)
    (hcritK : ∀ r ∈ crit, r ∈ interior K) {V' : (x : M) → TangentSpace I x}
    (hV' : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle I M)))
    (hV'K : ∀ x ∉ K, V' x = D.V x) {L : M → ℝ} (hL : ContMDiff I 𝓘(ℝ, ℝ) ∞ L)
    (hLpos : ∀ x ∈ U, 0 < dfV I L V' x) :
    ∀ x, f x ∈ Icc a b → ∀ γ : ℝ → M, γ 0 = x → IsMIntegralCurve γ V' →
      ∃ t, 0 ≤ t ∧ f (γ t) ≤ a := by
  intro x hx γ hγ0 hγ
  have hKc : IsClosed K := hK.isClosed
  have hγc : Continuous γ := hγ.continuous
  obtain ⟨s', hs'0, hs'ab, hav⟩ : ∃ s', 0 ≤ s' ∧ f (γ s') ∈ Icc a b ∧ ∀ t, s' ≤ t → γ t ∉ K := by
    by_cases hmeet : ∃ t₀, 0 ≤ t₀ ∧ γ t₀ ∈ K
    · obtain ⟨t₀, ht₀0, ht₀K⟩ := hmeet
      obtain ⟨t₁, ht₀₁, ht₁U⟩ := exists_exit_of_lyapunov hV' hU hL hLpos hγ t₀
      have ht₁K : γ t₁ ∉ K := fun h => ht₁U (hU'U (hKU' h))
      set S : Set ℝ := Icc t₀ t₁ ∩ γ ⁻¹' K with hS
      have hSc : IsClosed S := isClosed_Icc.inter (hKc.preimage hγc)
      have hSne : S.Nonempty := ⟨t₀, ⟨le_rfl, ht₀₁.le⟩, ht₀K⟩
      have hSbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
      set s₀ : ℝ := sSup S with hs₀
      have hs₀S : s₀ ∈ S := hSc.csSup_mem hSne hSbdd
      have hs₀t₁ : s₀ < t₁ := by
        rcases lt_or_eq_of_le hs₀S.1.2 with h | h
        · exact h
        · exact absurd (h ▸ hs₀S.2) ht₁K
      have hav1 : ∀ t, s₀ < t → t ≤ t₁ → γ t ∉ K := by
        intro t ht1 ht2 htK
        have : t ≤ s₀ := le_csSup hSbdd ⟨⟨by linarith [hs₀S.1.1], ht2⟩, htK⟩
        linarith
      set W : Set ℝ := γ ⁻¹' (U' ∩ f ⁻¹' Ioo a b) with hW
      have hWo : IsOpen W := (hU'o.inter (isOpen_Ioo.preimage hf.smooth.continuous)).preimage hγc
      have hs₀W : s₀ ∈ W := ⟨hKU' hs₀S.2, hKs hs₀S.2⟩
      have h1 : W ∈ 𝓝[>] s₀ := nhdsWithin_le_nhds (hWo.mem_nhds hs₀W)
      have h2 : Ioo s₀ t₁ ∈ 𝓝[>] s₀ := Ioo_mem_nhdsGT hs₀t₁
      obtain ⟨s', hs'W, hs'I⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
      refine ⟨s', by linarith [hs₀S.1.1, hs'I.1], ⟨hs'W.2.1.le, hs'W.2.2.le⟩, ?_⟩
      intro t₂ hs't₂ ht₂K
      have ht₁t₂ : t₁ < t₂ := by
        by_contra hle
        push Not at hle
        exact hav1 t₂ (by linarith [hs'I.1]) hle ht₂K
      set S2 : Set ℝ := Icc t₁ t₂ ∩ γ ⁻¹' K with hS2
      have hS2c : IsClosed S2 := isClosed_Icc.inter (hKc.preimage hγc)
      have hS2ne : S2.Nonempty := ⟨t₂, ⟨ht₁t₂.le, le_rfl⟩, ht₂K⟩
      have hS2bdd : BddBelow S2 := ⟨t₁, fun t ht => ht.1.1⟩
      set t₃ : ℝ := sInf S2 with ht₃
      have ht₃S : t₃ ∈ S2 := hS2c.csInf_mem hS2ne hS2bdd
      have hs't₃ : s' ≤ t₃ := by linarith [hs'I.2, ht₃S.1.1]
      have havoid : ∀ t ∈ Ico s' t₃, γ t ∉ K := by
        intro t ht htK
        rcases le_or_gt t t₁ with h | h
        · exact hav1 t (by linarith [hs'I.1, ht.1]) h htK
        · have : t₃ ≤ t := csInf_le hS2bdd ⟨⟨h.le, by linarith [ht.2, ht₃S.1.2]⟩, htK⟩
          linarith [ht.2]
      have heq := eq_flow_of_avoid D hKc hV'K hγ hs't₃ havoid
      have heq₁ := heq t₁ ⟨hs'I.2.le, ht₃S.1.1⟩
      have heq₃ := heq t₃ ⟨hs't₃, le_rfl⟩
      have := hnr (γ s') hs'W.1 (t₁ - s') (t₃ - s') (by linarith [hs'I.2])
        (by linarith [ht₃S.1.1]) (by rw [← heq₁]; exact ht₁U)
      rw [← heq₃] at this
      exact this (hKU' ht₃S.2)
    · push Not at hmeet
      exact ⟨0, le_rfl, by rw [hγ0]; exact hx, fun t ht => hmeet t ht⟩
  have hflow : ∀ τ, 0 ≤ τ → γ (s' + τ) = D.flow τ (γ s') := by
    intro τ hτ
    have := eq_flow_of_avoid D hKc hV'K hγ (s := s') (T := s' + τ) (by linarith)
      (fun t ht => hav t ht.1) (s' + τ) ⟨by linarith, le_rfl⟩
    rwa [add_sub_cancel_left] at this
  rcases D.trichotomy hf.smooth hε hεr hs'ab with hb | ⟨r, hr, hcap⟩
  · obtain ⟨τ, hτ, hτa⟩ := hb
    refine ⟨s' + τ, by linarith, ?_⟩
    rw [hflow τ hτ]
    exact hτa.le
  · exfalso
    set d := D.chart r hr with hd
    have h0src : (0 : Fin n → ℝ) ∈ d.χ.source := d.hball d.zero_mem_ball
    have hnhds : d.χ ⁻¹' interior K ∈ 𝓝 (0 : Fin n → ℝ) := by
      refine (d.χ.continuousAt h0src).preimage_mem_nhds (isOpen_interior.mem_nhds ?_)
      rw [d.hχ0]
      exact hcritK r hr
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.1 hnhds
    obtain ⟨T, hT⟩ := GradientLikeStrip.captured_eventually_small hcap hρ
    obtain ⟨z, ⟨hz1, _⟩, hzT⟩ := hT (max T 0) (le_max_left _ _)
    have hzK : D.flow (max T 0) (γ s') ∈ K := by
      rw [← hzT]
      exact interior_subset (hρsub (mem_ball_of_morseNorm_lt hz1))
    rw [← hflow (max T 0) (le_max_right _ _)] at hzK
    exact hav _ (by linarith [le_max_right T 0]) hzK

theorem exists_crossingField_of_lyapunov [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ r hr, (D.chart r hr).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm r hr ^ 2)
    {U U' : Set M} (hU : IsCompact U) (hUs : U ⊆ f ⁻¹' Ioo a b) (hU'o : IsOpen U')
    (hU'U : U' ⊆ U) (hcritU : ∀ r ∈ crit, r ∈ U) (hnr : noReturn D U U') {L : M → ℝ}
    (hL : ContMDiff I 𝓘(ℝ, ℝ) ∞ L)
    (hE : ∀ x ∈ U, dfV I L D.V x ≤ 0 → x ∈ U' ∧ mfderiv I 𝓘(ℝ, ℝ) L x ≠ 0) :
    ∃ V' : (x : M) → TangentSpace I x, isCrossingField I f a b V' := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : NormalSpace M := inferInstance
  have hgc : Continuous (dfV I L D.V) :=
    continuousOn_univ.1 (continuousOn_dfV D.smooth isOpen_univ hL.contMDiffOn)
  set E : Set M := U ∩ {x | dfV I L D.V x ≤ 0} with hEdef
  have hEc : IsCompact E := hU.inter_right (isClosed_le hgc continuous_const)
  set O : Set M := U' ∩ {x | x ∈ (univ : Set M) ∧ mfderiv I 𝓘(ℝ, ℝ) L x ≠ 0} with hOdef
  have hOo : IsOpen O := hU'o.inter (isOpen_mfderiv_ne_zero isOpen_univ hL.contMDiffOn)
  have hEO : E ⊆ O := by
    rintro x ⟨hxU, hxE⟩
    obtain ⟨h1, h2⟩ := hE x hxU hxE
    exact ⟨h1, mem_univ x, h2⟩
  obtain ⟨Ep, hEpc, hEEp, hEpO⟩ := exists_compact_between hEc hOo hEO
  have hEpU' : Ep ⊆ U' := fun x hx => (hEpO hx).1
  have hEps : Ep ⊆ f ⁻¹' Ioo a b := fun x hx => hUs (hU'U (hEpU' hx))
  have hEpU : Ep ⊆ U := fun x hx => hU'U (hEpU' hx)
  obtain ⟨W, hWs, hWc, hWK, hWb⟩ :=
    DifferentialGeometry.Topology.Morse.exists_unitSpeedVectorField_on_compact I L hL Ep hEpc
      (fun x hx => (hEpO hx).2.2)
  obtain ⟨κ, hκ1, hκ0, hκ01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤) hEc.isClosed hEEp
  obtain ⟨B, hB⟩ := hU.exists_bound_of_continuousOn hgc.continuousOn
  set c : ℝ := 1 + B with hc
  set V' : (x : M) → TangentSpace I x := fun x => D.V x + (-(c * κ x)) • W x with hV'def
  have hV's : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, V' x⟩ : TangentBundle I M)) :=
    D.smooth.add_section ((contMDiff_const.mul κ.contMDiff).neg.smul_section hWs)
  have hV'K : ∀ x ∉ Ep, V' x = D.V x := by
    intro x hx
    simp [hV'def, hκ0 x hx]
  have hdfV' : ∀ (g : M → ℝ) (x : M),
      dfV I g V' x = dfV I g D.V x + (-(c * κ x)) * dfV I g W x := by
    intro g x
    simp only [hV'def, dfV, map_add, map_smul, smul_eq_mul]
  have hLpos : ∀ x ∈ U, 0 < dfV I L V' x := by
    intro x hxU
    rw [hdfV']
    have hBx : ‖dfV I L D.V x‖ ≤ B := hB x hxU
    have hBx' : -B ≤ dfV I L D.V x := by
      rw [Real.norm_eq_abs] at hBx
      linarith [neg_abs_le (dfV I L D.V x)]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hBx
    by_cases hxE : dfV I L D.V x ≤ 0
    · have hxE' : x ∈ E := ⟨hxU, hxE⟩
      have hk : κ x = 1 := hκ1.self_of_nhdsSet x hxE'
      have hw : dfV I L W x = -1 := hWK x (interior_subset (hEEp hxE'))
      rw [hk, hw]
      linarith
    · push Not at hxE
      have hk := hκ01 x
      have hw : -1 ≤ dfV I L W x ∧ dfV I L W x ≤ 0 := hWb x
      have h1 : 0 ≤ (-(c * κ x)) * dfV I L W x := by
        have : 0 ≤ c * κ x := mul_nonneg (by linarith) hk.1
        have : -(c * κ x) * dfV I L W x = (c * κ x) * (-dfV I L W x) := by ring
        rw [this]
        exact mul_nonneg ‹_› (by linarith [hw.2])
      linarith
  have hcritK : ∀ r ∈ crit, r ∈ interior Ep := by
    intro r hr
    refine hEEp ⟨hcritU r hr, ?_⟩
    change dfV I L D.V r ≤ 0
    simp [dfV, D.V_crit r hr]
  obtain ⟨η₀, hη₀, hη₀ab, hcoll⟩ := exists_unit_collar D hf hU hUs
  refine ⟨V', hV's, ?_, η₀, hη₀, hη₀ab, ?_, ?_⟩
  · refine (D.compact.union hWc).of_isClosed_subset isClosed_closure ?_
    have hsub : Function.support V' ⊆ Function.support D.V ∪ Function.support W := by
      intro x hx
      by_contra hcon
      have h1 : D.V x = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h2 : W x = 0 := by
        by_contra h
        exact hcon (Or.inr h)
      apply hx
      change D.V x + -(c * κ x) • W x = 0
      rw [h1, h2, smul_zero, add_zero]
    have h := closure_mono hsub
    rw [closure_union] at h
    exact h
  · intro x hx
    obtain ⟨h1, h2⟩ := hcoll x hx
    have hxK : x ∉ Ep := fun h => h2 (hEpU h)
    have : dfV I f V' x = dfV I f D.V x := by
      simp only [dfV, hV'K x hxK]
    rw [this, h1]
  · exact reaches_bottom_of_lyapunov hf D hε hεr hU hU'o hU'U hnr hEpc hEpU' hEps hcritK hV's
      hV'K hL hLpos

def isLyapunovOn (D : GradientLikeStrip I f a b crit) (Γ K : Set M) (L₀ A : M → ℝ) : Prop :=
  IsCompact K ∧ K ⊆ f ⁻¹' Ioo a b ∧
    (∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ L₀ W ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ A W) ∧
    (∀ x ∈ K, 0 ≤ dfV I L₀ D.V x) ∧
    (∀ x ∈ K, x ∉ Γ → 0 < dfV I L₀ D.V x ∨ (dfV I L₀ D.V x = 0 ∧ 0 < dfV I A D.V x)) ∧
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∀ x ∈ K,
      dfV I (fun y => L₀ y + μ * A y) D.V x ≤ 0 →
        mfderiv I 𝓘(ℝ, ℝ) (fun y => L₀ y + μ * A y) x ≠ 0

def isLyapunovNbhd (D : GradientLikeStrip I f a b crit) (Γ U : Set M) : Prop :=
  IsCompact U ∧ Γ ⊆ interior U ∧ U ⊆ f ⁻¹' Ioo a b ∧
    ∀ O : Set M, IsOpen O → Γ ⊆ O → ∃ L : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ L ∧
      ∀ x ∈ U, dfV I L D.V x ≤ 0 → x ∈ O ∧ mfderiv I 𝓘(ℝ, ℝ) L x ≠ 0

omit [I.Boundaryless] [T2Space M] in
theorem isLyapunovOn.union {D : GradientLikeStrip I f a b crit} {Γ K₁ K₂ : Set M}
    {L₀ A : M → ℝ} (h₁ : isLyapunovOn D Γ K₁ L₀ A) (h₂ : isLyapunovOn D Γ K₂ L₀ A) :
    isLyapunovOn D Γ (K₁ ∪ K₂) L₀ A := by
  obtain ⟨hc₁, hs₁, ⟨W₁, hW₁, hKW₁, hL₁, hA₁⟩, hpos₁, hoff₁, μ₁, hμ₁, hnc₁⟩ := h₁
  obtain ⟨hc₂, hs₂, ⟨W₂, hW₂, hKW₂, hL₂, hA₂⟩, hpos₂, hoff₂, μ₂, hμ₂, hnc₂⟩ := h₂
  have hsm : ∀ {g : M → ℝ}, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g W₁ → ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g W₂ →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g (W₁ ∪ W₂) := fun {g} h₁ h₂ => by
    intro x hx
    rcases hx with hx | hx
    · exact (h₁.contMDiffAt (hW₁.mem_nhds hx)).contMDiffWithinAt
    · exact (h₂.contMDiffAt (hW₂.mem_nhds hx)).contMDiffWithinAt
  refine ⟨hc₁.union hc₂, union_subset hs₁ hs₂, ⟨W₁ ∪ W₂, hW₁.union hW₂,
    union_subset_union hKW₁ hKW₂, hsm hL₁ hL₂, hsm hA₁ hA₂⟩, ?_, ?_, min μ₁ μ₂,
    lt_min hμ₁ hμ₂, ?_⟩
  · rintro x (hx | hx)
    exacts [hpos₁ x hx, hpos₂ x hx]
  · rintro x (hx | hx)
    exacts [hoff₁ x hx, hoff₂ x hx]
  · rintro μ hμ hμle x (hx | hx)
    exacts [hnc₁ μ hμ (hμle.trans (min_le_left _ _)) x hx,
      hnc₂ μ hμ (hμle.trans (min_le_right _ _)) x hx]

theorem isLyapunovNbhd_of_isLyapunovOn [SigmaCompactSpace M] {D : GradientLikeStrip I f a b crit}
    {Γ K : Set M} {L₀ A : M → ℝ} (h : isLyapunovOn D Γ K L₀ A) (hΓ : Γ ⊆ interior K) :
    isLyapunovNbhd D Γ K := by
  classical
  have _hbd : I.Boundaryless := inferInstance
  obtain ⟨hKc, hKs, ⟨W, hWo, hKW, hL₀W, hAW⟩, hpos, hoff, μ₀, hμ₀, hnc⟩ := h
  refine ⟨hKc, hΓ, hKs, ?_⟩
  intro O hO hΓO
  have hg₀ : ContinuousOn (dfV I L₀ D.V) W := continuousOn_dfV D.smooth hWo hL₀W
  have hg₁ : ContinuousOn (dfV I A D.V) W := continuousOn_dfV D.smooth hWo hAW
  obtain ⟨μ, hμ, hμle, hμpos⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ μ₀ ∧
      ∀ x ∈ K, x ∉ O → 0 < dfV I L₀ D.V x + μ * dfV I A D.V x := by
    have hKOc : IsCompact (K \ O) := hKc.diff hO
    set C : Set M := (K \ O) ∩ dfV I A D.V ⁻¹' Iic 0 with hC
    have hCcl : IsClosed C :=
      (hg₁.mono (sdiff_subset.trans hKW)).preimage_isClosed_of_isClosed hKOc.isClosed isClosed_Iic
    have hCc : IsCompact C := hKOc.of_isClosed_subset hCcl inter_subset_left
    have hoff' : ∀ x ∈ K, x ∉ O →
        0 < dfV I L₀ D.V x ∨ (dfV I L₀ D.V x = 0 ∧ 0 < dfV I A D.V x) :=
      fun x hx hxO => hoff x hx fun hxΓ => hxO (hΓO hxΓ)
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨μ₀, hμ₀, le_rfl, fun x hx hxO => ?_⟩
      have h1 : 0 < dfV I A D.V x := by
        by_contra hle
        push Not at hle
        have : x ∈ C := ⟨⟨hx, hxO⟩, hle⟩
        rw [hCe] at this
        exact this
      have h2 := hpos x hx
      have h3 : 0 < μ₀ * dfV I A D.V x := mul_pos hμ₀ h1
      linarith
    · have hCK : C ⊆ W := fun x hx => hKW hx.1.1
      obtain ⟨xm, hxm, hmin⟩ := hCc.exists_isMinOn hCne (hg₀.mono hCK)
      obtain ⟨xM, hxM, hmax⟩ := hCc.exists_isMinOn hCne (hg₁.mono hCK)
      set m : ℝ := dfV I L₀ D.V xm with hm
      set B : ℝ := -dfV I A D.V xM with hB
      have hm0 : 0 < m := by
        rcases hoff' xm hxm.1.1 hxm.1.2 with h | h
        · exact h
        · exact absurd hxm.2 (not_le.2 h.2)
      have hB0 : 0 ≤ B := by
        have : dfV I A D.V xM ≤ 0 := hxM.2
        rw [hB]; linarith
      refine ⟨min μ₀ (m / (B + 1)), lt_min hμ₀ (by positivity), min_le_left _ _,
        fun x hx hxO => ?_⟩
      set μ := min μ₀ (m / (B + 1)) with hμdef
      have hμ : 0 < μ := lt_min hμ₀ (by positivity)
      rcases lt_or_ge 0 (dfV I A D.V x) with h1 | h1
      · have h2 := hpos x hx
        have h3 : 0 < μ * dfV I A D.V x := mul_pos hμ h1
        linarith
      · have hxC : x ∈ C := ⟨⟨hx, hxO⟩, h1⟩
        have h2 : m ≤ dfV I L₀ D.V x := isMinOn_iff.1 hmin x hxC
        have h3 : -dfV I A D.V x ≤ B := by
          have := isMinOn_iff.1 hmax x hxC
          rw [hB]; linarith
        have h4 : μ * (-dfV I A D.V x) ≤ μ * B := mul_le_mul_of_nonneg_left h3 hμ.le
        have h5 : μ * B ≤ m / (B + 1) * B :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hB0
        have h6 : m / (B + 1) * B < m := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        nlinarith
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : NormalSpace M := inferInstance
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := (⊤ : ℕ∞))
    hWo.isClosed_compl hKc.isClosed (disjoint_compl_left_iff_subset.2 hKW)
  set g : M → ℝ := fun y => L₀ y + μ * A y with hg
  set L : M → ℝ := fun y => χ y * g y with hL
  have hgW : ∀ x ∈ W, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ g x := fun x hx =>
    ((hL₀W.contMDiffAt (hWo.mem_nhds hx)).add
      (contMDiffAt_const.mul (hAW.contMDiffAt (hWo.mem_nhds hx))))
  have hLs : ContMDiff I 𝓘(ℝ, ℝ) ∞ L := by
    intro x
    by_cases hx : x ∈ W
    · exact χ.contMDiff.contMDiffAt.mul (hgW x hx)
    · have hev : ∀ᶠ y in 𝓝 x, χ y = 0 :=
        (hχ0.filter_mono (nhds_le_nhdsSet (mem_compl hx)))
      refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [hL, hy]
  refine ⟨L, hLs, fun x hx hLx => ?_⟩
  have hLg : L =ᶠ[𝓝 x] g := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [hL, hy]
  have hLgx : L x = g x := hLg.eq_of_nhds
  have hmf : mfderiv I 𝓘(ℝ, ℝ) L x = mfderiv I 𝓘(ℝ, ℝ) g x := by
    rw [hLg.mfderiv_eq, hLgx]
    rfl
  have hdfV : dfV I L D.V x = dfV I g D.V x := by
    unfold dfV
    rw [hmf, hLgx]
  have hadd : dfV I g D.V x = dfV I L₀ D.V x + μ * dfV I A D.V x := by
    have hxW := hKW hx
    have h0 : MDifferentiableAt I 𝓘(ℝ, ℝ) L₀ x :=
      (hL₀W.contMDiffAt (hWo.mem_nhds hxW)).mdifferentiableAt (by simp)
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) A x :=
      (hAW.contMDiffAt (hWo.mem_nhds hxW)).mdifferentiableAt (by simp)
    have hd := h0.hasMFDerivAt.add (h1.hasMFDerivAt.const_smul μ)
    have hgeq : g = L₀ + μ • A := rfl
    unfold dfV
    rw [hgeq, hd.mfderiv]
    rfl
  rw [hdfV] at hLx
  refine ⟨?_, ?_⟩
  · by_contra hxO
    have := hμpos x hx hxO
    rw [← hadd] at this
    linarith
  · rw [hmf]
    exact hnc μ hμ hμle x hx hLx

end Generic

section Backward

variable {a b : ℝ} {crit : Finset M}

theorem exists_backward_clusterPt (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {x : M} (hx : f x ∈ Icc a b) (hxc : x ∉ crit) (hnt : ∀ t ≤ 0, f (D.flow t x) ≤ b) :
    ∃ r ∈ crit, f x < f r ∧ MapClusterPt r atTop (fun t => D.flow (-t) x) ∧
      ∀ t, 0 ≤ t → f (D.flow (-t) x) < f r := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hSc : IsCompact (f ⁻¹' Icc a b) := hf.compact
  let φ : Flow ℝ M :=
    { toFun := D.flow
      cont' := D.continuous_flow_joint
      map_add' := fun t₁ t₂ y => by rw [add_comm, D.flow_add]
      map_zero' := D.flow_zero }
  set ψ : Flow ℝ M := φ.reverse with hψ
  have hψ' : ∀ t y, ψ t y = D.flow (-t) y := fun t y => rfl
  set Ω := omegaLimit atTop (⇑ψ) {x} with hΩ
  have hmono : ∀ s t : ℝ, s ≤ t → f (D.flow (-s) x) ≤ f (D.flow (-t) x) := fun s t hst =>
    GradientLikeStrip.f_flow_antitone (D := D) hfs x (neg_le_neg hst)
  have hcon : ∀ t, 0 ≤ t → D.flow (-t) x ∈ f ⁻¹' Icc a b := fun t ht =>
    ⟨hx.1.trans (by simpa using hmono 0 t ht), hnt (-t) (by linarith)⟩
  have himg : ∀ (C : Set M), IsClosed C → ∀ T : ℝ, (∀ t, T ≤ t → D.flow (-t) x ∈ C) →
      closure (image2 (⇑ψ) (Ici T) {x}) ⊆ C := by
    intro C hC T hT
    refine closure_minimal ?_ hC
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    rw [hψ']
    exact hT t ht
  have hclos : ∀ (C : Set M), IsClosed C → ∀ T : ℝ, (∀ t, T ≤ t → D.flow (-t) x ∈ C) →
      Ω ⊆ C := fun C hC T hT =>
    (omegaLimit_subset_closure_image2 atTop (⇑ψ) {x} (Ici_mem_atTop T)).trans (himg C hC T hT)
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑ψ) {x} hSc
      ⟨Ici 0, Ici_mem_atTop 0, himg _ hSc.isClosed 0 hcon⟩ (singleton_nonempty x)
  have hinv : ∀ t, MapsTo (ψ t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop ψ {x} fun t =>
      tendsto_atTop_atTop.2 fun b => ⟨b - t, fun s hs => by linarith⟩
  have hlow : ∀ z ∈ Ω, ∀ t, 0 ≤ t → f (D.flow (-t) x) ≤ f z := by
    intro z hz t _
    exact hclos {y | f (D.flow (-t) x) ≤ f y} (isClosed_le continuous_const hfc) t
      (fun s hs => hmono t s hs) hz
  have hup : ∀ z ∈ Ω, ∀ w ∈ Ω, f z ≤ f w := by
    intro z hz w hw
    exact hclos {y | f y ≤ f w} (isClosed_le hfc continuous_const) 0
      (fun s hs => hlow w hw s hs) hz
  obtain ⟨r, hr⟩ := hΩne
  have hrS : r ∈ f ⁻¹' Icc a b := hclos _ hSc.isClosed 0 hcon hr
  have hconst : ∀ s, f (D.flow s r) = f r := by
    intro s
    have hm : D.flow s r ∈ Ω := by
      have := hinv (-s) hr
      rwa [hψ', neg_neg] at this
    exact le_antisymm (hup _ hm r hr) (hup r hr _ hm)
  have hrc : r ∈ crit := by
    by_contra hrc
    have hneg := D.neg r hrS hrc
    have hd := GradientLikeStrip.hasDerivAt_f_flow (D := D) hfs r 0
    rw [D.flow_zero] at hd
    have hmax : IsLocalMax (fun s => f (D.flow s r)) 0 :=
      Filter.Eventually.of_forall fun s => by
        change f (D.flow s r) ≤ f (D.flow 0 r)
        rw [hconst s, hconst 0]
    exact (ne_of_lt hneg) (hmax.hasDerivAt_eq_zero hd)
  have hstrict : ∀ t, 0 ≤ t → f (D.flow (-t) x) < f r := by
    intro t ht
    refine lt_of_le_of_ne (hlow r hr t ht) fun heq => ?_
    have hyS : D.flow (-t) x ∈ f ⁻¹' Icc a b := hcon t ht
    have hyc : D.flow (-t) x ∉ crit := fun hyc => hxc (by
      have := D.flow_crit hyc t
      rw [D.flow_flow, neg_add_cancel, D.flow_zero] at this
      rw [this]; exact hyc)
    have hneg := D.neg _ hyS hyc
    have hd := GradientLikeStrip.hasDerivAt_f_flow (D := D) hfs (D.flow (-t) x) 0
    rw [D.flow_zero] at hd
    have hmax : IsLocalMax (fun s => f (D.flow s (D.flow (-t) x))) 0 := by
      refine Filter.Eventually.of_forall fun s => ?_
      change f (D.flow s (D.flow (-t) x)) ≤ f (D.flow 0 (D.flow (-t) x))
      rw [D.flow_zero]
      rcases le_total 0 s with hs | hs
      · exact GradientLikeStrip.f_flow_le hfs _ hs
      · rw [heq, D.flow_flow, show -t + s = -(t - s) by ring]
        exact hlow r hr (t - s) (by linarith)
    exact (ne_of_lt hneg) (hmax.hasDerivAt_eq_zero hd)
  refine ⟨r, hrc, by simpa using hstrict 0 le_rfl, ?_, hstrict⟩
  exact (mem_omegaLimit_singleton_iff_mapClusterPt atTop (⇑ψ) x r).1 hr

theorem posPart_eq_zero_of_backward (D : GradientLikeStrip I f a b crit)
    (hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {r : M} (hr : r ∈ crit) {y : Fin n → ℝ}
    (hy : 2 * morseNorm n y ^ 2 < D.rm r hr ^ 2)
    (hlev : ∀ t, 0 ≤ t → f (D.flow (-t) ((D.chart r hr).χ y)) < f r) :
    posPart (D.chart r hr).hk y = 0 := by
  have _hf : Continuous f := hfs.continuous
  set d := D.chart r hr with hd
  set x := d.χ y with hx
  set R := D.rm r hr with hR
  set u₀ := negPart d.hk y with hu₀
  set v₀ := posPart d.hk y with hv₀
  set O : Set M := d.χ '' {z | morseNorm n z < R} with hO
  have hRpos : 0 < R := D.rm_pos r hr
  have hRle : R ≤ d.R := (D.hrm r hr).2
  have hmn : 0 ≤ morseNorm n y := ModelField.morseNorm_nonneg y
  have hyR : morseNorm n y < R := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hsplit : morseNorm n y ^ 2 = ‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 :=
    DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart d.hk y
  set ρ := Real.sqrt (2 * morseNorm n y ^ 2) with hρ
  have hρR : ρ < R := (Real.sqrt_lt' hRpos).2 hy
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set K : Set M := d.χ '' {z | morseNorm n z ≤ ρ} with hK
  have hKc : IsClosed K := (d.isCompact_image_le (hρR.trans (D.rm_lt_R' r hr))).isClosed
  have hKO : K ⊆ O := image_mono fun z hz => lt_of_le_of_lt hz hρR
  have hOo : IsOpen O := D.isOpen_modelBall r hr
  have hsymm : ∀ z, morseNorm n z < R → d.χ.symm (d.χ z) = z := fun z hz =>
    d.χ.left_inv (d.hsrc z (hz.le.trans hRle))
  have hlevel : ∀ s ≤ 0, f (D.flow s x) < f r := by
    intro s hs
    have := hlev (-s) (by linarith)
    rwa [neg_neg] at this
  have hsc : ∀ s ≤ 0, (∀ s' ∈ Icc s 0, D.flow s' x ∈ O) → ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧
      d.χ.symm (D.flow s x) = recombine d.hk (l • u₀) (l⁻¹ • v₀) := by
    intro t ht0 hball
    set γ' : ℝ → Fin n → ℝ := fun s => d.χ.symm (D.flow s x) with hγ'def
    have h0 : (0 : ℝ) ∈ Icc t 0 := ⟨ht0, le_rfl⟩
    have ht : t ∈ Icc t 0 := ⟨le_rfl, ht0⟩
    have hγ : ∀ s ∈ Icc t 0, HasDerivAt γ' (ModelField.modelField d.k d.r₀ (γ' s)) s :=
      GradientLikeStrip.hasDerivAt_symm_flow_Icc hr (fun s hs => hball s hs)
    have hγ0 : γ' 0 = y := by
      simp only [hγ'def, GradientLikeStrip.flow_zero]
      exact hsymm y hyR
    have hΘ : ContinuousOn (fun s => ModelField.theta d.r₀ (γ' s)) (Icc t 0) :=
      (ModelField.continuous_theta d.hr₀).comp_continuousOn (ModelField.continuousOn_curve hγ)
    set Θ' : ℝ → ℝ := fun s => ModelField.theta d.r₀ (γ' ((projIcc t 0 ht0 s : Icc t 0) : ℝ))
      with hΘ'def
    have hΘ'c : Continuous Θ' :=
      hΘ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => Subtype.mem _
    have hΘ'eq : ∀ s ∈ Icc t 0, Θ' s = ModelField.theta d.r₀ (γ' s) := by
      intro s hs
      simp only [hΘ'def, projIcc_of_mem ht0 hs]
    have hΘ'nn : ∀ s, 0 ≤ Θ' s := fun s => (ModelField.theta_pos d.hr₀ _).le
    set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, Θ' u with hFdef
    have hF : ∀ s, HasDerivAt F (Θ' s) s := fun s =>
      (hΘ'c.integral_hasStrictDerivAt 0 s).hasDerivAt
    have hF0 : F 0 = 0 := intervalIntegral.integral_same
    have hu : ∀ s ∈ Icc t 0,
        HasDerivAt (fun s => Real.exp (-F s) • negPart d.hk (γ' s)) 0 s := by
      intro s hs
      have h1 := ((hF s).neg.exp).smul (ModelField.hasDerivAt_negPart_curve d.hk hγ hs)
      convert h1 using 1
      rw [hΘ'eq s hs]
      module
    have hu_const := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hu)
      (fun s hs => (hu s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    have hu_t : Real.exp (-F t) • negPart d.hk (γ' t) = negPart d.hk y := by
      have := (hu_const t ht).trans (hu_const 0 h0).symm
      simpa [hF0, hγ0] using this
    have hv : ∀ s ∈ Icc t 0,
        HasDerivAt (fun s => Real.exp (F s) • posPart d.hk (γ' s)) 0 s := by
      intro s hs
      have h1 := ((hF s).exp).smul (ModelField.hasDerivAt_posPart_curve d.hk hγ hs)
      convert h1 using 1
      rw [hΘ'eq s hs]
      module
    have hv_const := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hv)
      (fun s hs => (hv s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    have hv_t : Real.exp (F t) • posPart d.hk (γ' t) = posPart d.hk y := by
      have := (hv_const t ht).trans (hv_const 0 h0).symm
      simpa [hF0, hγ0] using this
    refine ⟨Real.exp (F t), Real.exp_pos _, ?_, ?_⟩
    · rw [Real.exp_le_one_iff, hFdef]
      simp only
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.2 (intervalIntegral.integral_nonneg ht0 fun u _ => hΘ'nn u)
    · have hneg : negPart d.hk (γ' t) = Real.exp (F t) • negPart d.hk y := by
        rw [← hu_t, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
      have hpos : posPart d.hk (γ' t) = (Real.exp (F t))⁻¹ • posPart d.hk y := by
        rw [← hv_t, smul_smul, ← Real.exp_neg, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          one_smul]
      change γ' t = _
      rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk (γ' t),
        hneg, hpos]
  have hlevl : ∀ s ≤ 0, ∀ l : ℝ, 0 < l → D.flow s x ∈ O →
      d.χ.symm (D.flow s x) = recombine d.hk (l • u₀) (l⁻¹ • v₀) →
      ‖l⁻¹ • v₀‖ ^ 2 < ‖l • u₀‖ ^ 2 ∧ morseNorm n (d.χ.symm (D.flow s x)) < R := by
    intro s hs l hl hmem heq
    obtain ⟨z, hz, hzx⟩ := hmem
    have hzs : d.χ.symm (D.flow s x) = z := by rw [← hzx]; exact hsymm z hz
    have hf := hlevel s hs
    rw [← hzx, d.hnorm z (le_of_lt (lt_of_lt_of_le hz hRle)),
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hf
    rw [hzs] at heq
    rw [heq, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine,
      DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine] at hf
    refine ⟨by linarith, ?_⟩
    rw [hzs]
    exact hz
  have hmemK : ∀ s ≤ 0, (∀ s' ∈ Icc s 0, D.flow s' x ∈ O) → D.flow s x ∈ K := by
    intro s hs hball
    obtain ⟨l, hl0, hl1, heq⟩ := hsc s hs hball
    have hmem := hball s ⟨le_rfl, hs⟩
    obtain ⟨hlt, -⟩ := hlevl s hs l hl0 hmem heq
    obtain ⟨z, hz, hzx⟩ := hmem
    have hzs : d.χ.symm (D.flow s x) = z := by rw [← hzx]; exact hsymm z hz
    rw [hzs] at heq
    refine ⟨z, ?_, hzx⟩
    change morseNorm n z ≤ ρ
    have hz2 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      d.hk z
    rw [heq, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine,
      DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine] at hz2
    rw [← heq] at hz2
    have hnu : ‖l • u₀‖ ^ 2 = l ^ 2 * ‖u₀‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hl2 : l ^ 2 ≤ 1 := by nlinarith
    have hu2 : l ^ 2 * ‖u₀‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
      nlinarith [sq_nonneg ‖u₀‖]
    rw [Real.le_sqrt (ModelField.morseNorm_nonneg z) (by positivity)]
    nlinarith [sq_nonneg ‖v₀‖]
  have hconf : ∀ s ≤ 0, D.flow s x ∈ K := by
    intro s hs
    set Q : Set ℝ := {s | D.flow s x ∈ K} with hQ
    have hQc : IsClosed Q := hKc.preimage (D.continuous_flow_curve x)
    have hQ0 : (0 : ℝ) ∈ Q := by
      change D.flow 0 x ∈ K
      rw [GradientLikeStrip.flow_zero]
      refine ⟨y, ?_, rfl⟩
      change morseNorm n y ≤ ρ
      rw [Real.le_sqrt hmn (by positivity)]
      nlinarith
    have hsub := Icc_neg_subset_of_isClosed_of_step hQc hQ0 (T := -s) (fun t ht hIcc => by
      have htO : D.flow t x ∈ O := hKO (hIcc ⟨le_rfl, ht.2⟩)
      have hW : {s' | D.flow s' x ∈ O} ∈ 𝓝 t :=
        (hOo.preimage (D.continuous_flow_curve x)).mem_nhds htO
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
      rw [Real.ball_eq_Ioo] at hball
      refine mem_of_superset (Ioo_mem_nhdsLT (show t - δ < t by linarith)) fun s' hs' => ?_
      refine hmemK s' (by linarith [hs'.2, ht.2]) fun s'' hs'' => ?_
      rcases le_or_gt t s'' with h | h
      · exact hKO (hIcc ⟨h, hs''.2⟩)
      · exact hball ⟨by linarith [hs'.1, hs''.1], by linarith⟩)
    exact hsub ⟨by linarith, hs⟩
  have hinO : ∀ s ≤ 0, D.flow s x ∈ O := fun s hs => hKO (hconf s hs)
  set θ₀ : ℝ := (R ^ 2 + d.r₀ ^ 2)⁻¹ with hθ₀
  have hθ₀pos : 0 < θ₀ := by positivity
  set γ : ℝ → Fin n → ℝ := fun s => d.χ.symm (D.flow s x) with hγdef
  have hγ0 : γ 0 = y := by
    simp only [hγdef, GradientLikeStrip.flow_zero]
    exact hsymm y hyR
  have hrate : ∀ T, 0 ≤ T → Real.exp (2 * θ₀ * T) * ‖negPart d.hk (γ (-T))‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    intro T hT
    have hγ : ∀ s ∈ Icc (-T) 0, HasDerivAt γ (ModelField.modelField d.k d.r₀ (γ s)) s :=
      GradientLikeStrip.hasDerivAt_symm_flow_Icc hr (fun s hs => hinO s hs.2)
    have hθ : ∀ s ∈ Icc (-T) (0 : ℝ), θ₀ ≤ ModelField.theta d.r₀ (γ s) := by
      intro s hs
      obtain ⟨z, hz, hzx⟩ := hinO s hs.2
      have hzs : γ s = z := by
        change d.χ.symm (D.flow s x) = z
        rw [← hzx]; exact hsymm z hz
      rw [hzs]
      exact ModelField.theta_ge_of_le d.hr₀ hz.le
    set g : ℝ → ℝ := fun s => Real.exp (-(2 * θ₀) * s) * ‖negPart d.hk (γ s)‖ ^ 2 with hgdef
    have hgd : ∀ s ∈ Icc (-T) 0, HasDerivAt g
        (Real.exp (-(2 * θ₀) * s) * (-(2 * θ₀)) * ‖negPart d.hk (γ s)‖ ^ 2 +
          Real.exp (-(2 * θ₀) * s) *
            (2 * ModelField.theta d.r₀ (γ s) * ‖negPart d.hk (γ s)‖ ^ 2)) s := by
      intro s hs
      have h1 : HasDerivAt (fun s => Real.exp (-(2 * θ₀) * s))
          (Real.exp (-(2 * θ₀) * s) * (-(2 * θ₀))) s := by
        have := ((hasDerivAt_id' (x := s)).const_mul (-(2 * θ₀))).exp
        simpa [mul_comm] using this
      exact h1.mul (ModelField.hasDerivAt_normSq_negPart_curve d.hk hγ hs)
    have hmono : MonotoneOn g (Icc (-T) 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-T) 0)
        (f' := fun s => Real.exp (-(2 * θ₀) * s) * (-(2 * θ₀)) * ‖negPart d.hk (γ s)‖ ^ 2 +
          Real.exp (-(2 * θ₀) * s) *
            (2 * ModelField.theta d.r₀ (γ s) * ‖negPart d.hk (γ s)‖ ^ 2))
        (HasDerivAt.continuousOn hgd) (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact (hgd s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
      · rw [interior_Icc] at hs
        have h1 := hθ s (Ioo_subset_Icc_self hs)
        have h2 := Real.exp_pos (-(2 * θ₀) * s)
        have h3 := sq_nonneg ‖negPart d.hk (γ s)‖
        have : 0 ≤ Real.exp (-(2 * θ₀) * s) * ‖negPart d.hk (γ s)‖ ^ 2 *
            (ModelField.theta d.r₀ (γ s) - θ₀) :=
          mul_nonneg (mul_nonneg h2.le h3) (by linarith)
        nlinarith
    have := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    simp only [hgdef, mul_zero, Real.exp_zero, one_mul, hγ0] at this
    convert this using 2
    ring_nf
  obtain ⟨hlt0, -⟩ := hlevl 0 le_rfl 1 one_pos (hinO 0 le_rfl) (by
    rw [one_smul, inv_one, one_smul]
    change γ 0 = _
    rw [hγ0]
    exact (DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk y).symm)
  rw [one_smul, inv_one, one_smul] at hlt0
  have hu0pos : 0 < ‖u₀‖ ^ 2 := lt_of_le_of_lt (sq_nonneg _) hlt0
  have hkey : ∀ T, 0 ≤ T → ‖v₀‖ ^ 2 * Real.exp (4 * θ₀ * T) < ‖u₀‖ ^ 2 := by
    intro T hT
    obtain ⟨l, hl0, -, heq⟩ := hsc (-T) (by linarith) fun s' hs' => hinO s' hs'.2
    obtain ⟨hlt, -⟩ := hlevl (-T) (by linarith) l hl0 (hinO (-T) (by linarith)) heq
    have hr := hrate T hT
    have heq' : γ (-T) = recombine d.hk (l • u₀) (l⁻¹ • v₀) := heq
    rw [heq', DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine] at hr
    have hnu : ‖l • u₀‖ ^ 2 = l ^ 2 * ‖u₀‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hnv : ‖l⁻¹ • v₀‖ ^ 2 = (l ^ 2)⁻¹ * ‖v₀‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    rw [hnu] at hr
    rw [hnu, hnv] at hlt
    have hl2 : 0 < l ^ 2 := by positivity
    have hE : Real.exp (4 * θ₀ * T) = Real.exp (2 * θ₀ * T) * Real.exp (2 * θ₀ * T) := by
      rw [← Real.exp_add]; ring_nf
    set E := Real.exp (2 * θ₀ * T) with hEdef
    have hEpos : 0 < E := Real.exp_pos _
    have hv : ‖v₀‖ ^ 2 < l ^ 2 * (l ^ 2 * ‖u₀‖ ^ 2) := by
      have := mul_lt_mul_of_pos_left hlt hl2
      rwa [← mul_assoc, mul_inv_cancel₀ hl2.ne', one_mul] at this
    have hEl : E * l ^ 2 ≤ 1 := by
      have : E * l ^ 2 * ‖u₀‖ ^ 2 ≤ 1 * ‖u₀‖ ^ 2 := by linarith
      exact le_of_mul_le_mul_right this hu0pos
    rw [hE]
    have h1 : ‖v₀‖ ^ 2 * (E * E) ≤ l ^ 2 * (l ^ 2 * ‖u₀‖ ^ 2) * (E * E) :=
      mul_le_mul_of_nonneg_right hv.le (by positivity)
    have h2 : l ^ 2 * (l ^ 2 * ‖u₀‖ ^ 2) * (E * E) = (E * l ^ 2) * (E * l ^ 2) * ‖u₀‖ ^ 2 := by
      ring
    have h3 : (E * l ^ 2) * (E * l ^ 2) ≤ 1 := by
      have h0 : 0 ≤ E * l ^ 2 := by positivity
      nlinarith
    have h4 : ‖v₀‖ ^ 2 * (E * E) < l ^ 2 * (l ^ 2 * ‖u₀‖ ^ 2) * (E * E) :=
      mul_lt_mul_of_pos_right hv (by positivity)
    rw [h2] at h4
    exact h4.trans_le (mul_le_of_le_one_left hu0pos.le h3)
  by_contra hne
  have hv0 : 0 < ‖v₀‖ ^ 2 := by
    have : 0 < ‖v₀‖ := norm_pos_iff.2 hne
    positivity
  set T : ℝ := ‖u₀‖ ^ 2 / (4 * θ₀ * ‖v₀‖ ^ 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 := hkey T hT0
  have h2 := Real.add_one_le_exp (4 * θ₀ * T)
  have h3 : 4 * θ₀ * T * ‖v₀‖ ^ 2 = ‖u₀‖ ^ 2 := by
    rw [hT]; field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hv0.le
  have h5 : ‖v₀‖ ^ 2 * (4 * θ₀ * T + 1) = ‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 := by
    rw [← h3]; ring
  linarith

theorem model_flow_scaling (D : GradientLikeStrip I f a b crit) {r : M} (hr : r ∈ crit)
    {y : Fin n → ℝ} (hy : morseNorm n y < D.rm r hr) {t : ℝ}
    (hball : ∀ s ∈ uIcc 0 t, D.flow s ((D.chart r hr).χ y) ∈
      (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr}) :
    ∃ l : ℝ, 0 < l ∧ (0 ≤ t → 1 ≤ l) ∧ (t ≤ 0 → l ≤ 1) ∧
      (D.chart r hr).χ.symm (D.flow t ((D.chart r hr).χ y)) =
        recombine (D.chart r hr).hk (l • negPart (D.chart r hr).hk y)
          (l⁻¹ • posPart (D.chart r hr).hk y) := by
  set d := D.chart r hr with hd
  set γ : ℝ → Fin n → ℝ := fun s => d.χ.symm (D.flow s (d.χ y)) with hγdef
  set a := min 0 t with ha
  set b := max 0 t with hb
  have hab : a ≤ b := min_le_max
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Icc a b := ⟨min_le_right _ _, le_max_right _ _⟩
  have hγ : ∀ s ∈ Icc a b, HasDerivAt γ (ModelField.modelField d.k d.r₀ (γ s)) s :=
    GradientLikeStrip.hasDerivAt_symm_flow_Icc hr (fun s hs => hball s hs)
  have hγ0 : γ 0 = y := by
    simp only [hγdef, GradientLikeStrip.flow_zero]
    exact d.χ.left_inv (d.hsrc y (hy.le.trans (D.hrm r hr).2))
  have hΘ : ContinuousOn (fun s => ModelField.theta d.r₀ (γ s)) (Icc a b) :=
    (ModelField.continuous_theta d.hr₀).comp_continuousOn (ModelField.continuousOn_curve hγ)
  set Θ' : ℝ → ℝ := fun s => ModelField.theta d.r₀ (γ ((projIcc a b hab s : Icc a b) : ℝ))
    with hΘ'def
  have hΘ'c : Continuous Θ' :=
    hΘ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => Subtype.mem _
  have hΘ'eq : ∀ s ∈ Icc a b, Θ' s = ModelField.theta d.r₀ (γ s) := by
    intro s hs
    simp only [hΘ'def, projIcc_of_mem hab hs]
  have hΘ'nn : ∀ s, 0 ≤ Θ' s := fun s => (ModelField.theta_pos d.hr₀ _).le
  set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, Θ' u with hFdef
  have hF : ∀ s, HasDerivAt F (Θ' s) s := fun s =>
    (hΘ'c.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hu : ∀ s ∈ Icc a b,
      HasDerivAt (fun s => Real.exp (-F s) • negPart d.hk (γ s)) 0 s := by
    intro s hs
    have h1 := ((hF s).neg.exp).smul (ModelField.hasDerivAt_negPart_curve d.hk hγ hs)
    convert h1 using 1
    rw [hΘ'eq s hs]
    module
  have hu_const := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hu)
    (fun s hs => (hu s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have hu_t : Real.exp (-F t) • negPart d.hk (γ t) = negPart d.hk y := by
    have := (hu_const t ht).trans (hu_const 0 h0).symm
    simpa [hF0, hγ0] using this
  have hv : ∀ s ∈ Icc a b,
      HasDerivAt (fun s => Real.exp (F s) • posPart d.hk (γ s)) 0 s := by
    intro s hs
    have h1 := ((hF s).exp).smul (ModelField.hasDerivAt_posPart_curve d.hk hγ hs)
    convert h1 using 1
    rw [hΘ'eq s hs]
    module
  have hv_const := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hv)
    (fun s hs => (hv s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have hv_t : Real.exp (F t) • posPart d.hk (γ t) = posPart d.hk y := by
    have := (hv_const t ht).trans (hv_const 0 h0).symm
    simpa [hF0, hγ0] using this
  refine ⟨Real.exp (F t), Real.exp_pos _, ?_, ?_, ?_⟩
  · intro ht0
    apply Real.one_le_exp
    exact intervalIntegral.integral_nonneg ht0 fun u _ => hΘ'nn u
  · intro ht0
    rw [Real.exp_le_one_iff, hFdef]
    simp only
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.2 (intervalIntegral.integral_nonneg ht0 fun u _ => hΘ'nn u)
  · have hneg : negPart d.hk (γ t) = Real.exp (F t) • negPart d.hk y := by
      rw [← hu_t, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
    have hpos : posPart d.hk (γ t) = (Real.exp (F t))⁻¹ • posPart d.hk y := by
      rw [← hv_t, smul_smul, ← Real.exp_neg, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        one_smul]
    change γ t = _
    rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk (γ t),
      hneg, hpos]

theorem flow_ray_stable (D : GradientLikeStrip I f a b crit) (hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {r : M} (hr : r ∈ crit) {e : EuclideanSpace ℝ (Fin (n - (D.chart r hr).k))} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) (htr : t < D.rm r hr) :
    (∀ s, 0 ≤ s → ∃ t' ∈ Ioc 0 t, D.flow s ((D.chart r hr).χ (recombine (D.chart r hr).hk 0 (t • e)))
        = (D.chart r hr).χ (recombine (D.chart r hr).hk 0 (t' • e))) ∧
      ∀ t' ∈ Ioc 0 t, ∃ s, 0 ≤ s ∧
        D.flow s ((D.chart r hr).χ (recombine (D.chart r hr).hk 0 (t • e))) =
          (D.chart r hr).χ (recombine (D.chart r hr).hk 0 (t' • e)) := by
  have _ := hfs
  set y : Fin n → ℝ := recombine (D.chart r hr).hk 0 (t • e) with hydef
  set x := (D.chart r hr).χ y with hxdef
  have hnorm_ray : ∀ c : ℝ, 0 ≤ c → morseNorm n (recombine (D.chart r hr).hk 0 (c • e)) = c := by
    intro c hc
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq (D.chart r hr).hk
      (0 : EuclideanSpace ℝ (Fin (D.chart r hr).k)) (c • e)
    rw [norm_zero, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hc] at h1
    have h2 : morseNorm n (recombine (D.chart r hr).hk 0 (c • e)) ^ 2 = c ^ 2 := by rw [h1]; ring
    exact (sq_eq_sq₀ (ModelField.morseNorm_nonneg _) hc).1 h2
  have hyn : morseNorm n y = t := hnorm_ray t ht.le
  have hyrm : morseNorm n y < D.rm r hr := hyn ▸ htr
  have hyu : negPart (D.chart r hr).hk y = 0 :=
    DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine (D.chart r hr).hk _ _
  have hyv : posPart (D.chart r hr).hk y = t • e :=
    DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine (D.chart r hr).hk _ _
  have hstay : ∀ s, 0 ≤ s → D.flow s x ∈ (D.chart r hr).χ ''
      {z | morseNorm n z ≤ morseNorm n y ∧ negPart (D.chart r hr).hk z = 0} := fun s hs =>
    GradientLikeStrip.flow_mem_of_negPart_eq_zero hr hyrm hyu hs
  have hball : ∀ s, 0 ≤ s → D.flow s x ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} :=
    fun s hs => image_mono (fun z hz => lt_of_le_of_lt hz.1 hyrm) (hstay s hs)
  have key : ∀ s, 0 ≤ s → ∃ l : ℝ, 1 ≤ l ∧
      (D.chart r hr).χ.symm (D.flow s x) = recombine (D.chart r hr).hk 0 ((l⁻¹ * t) • e) ∧
      D.flow s x = (D.chart r hr).χ (recombine (D.chart r hr).hk 0 ((l⁻¹ * t) • e)) := by
    intro s hs
    have hb : ∀ s' ∈ uIcc 0 s, D.flow s' x ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} := by
      intro s' hs'
      rw [uIcc_of_le hs] at hs'
      exact hball s' hs'.1
    obtain ⟨l, -, hl1, -, hleq⟩ := model_flow_scaling D hr hyrm hb
    have hl : 1 ≤ l := hl1 hs
    rw [hyu, hyv, smul_zero, smul_smul] at hleq
    refine ⟨l, hl, hleq, ?_⟩
    obtain ⟨z, hz, hzx⟩ := hstay s hs
    have hzs : (D.chart r hr).χ.symm (D.flow s x) = z := by
      rw [← hzx, (D.chart r hr).χ.left_inv ((D.chart r hr).hsrc z (hz.1.trans (hyrm.le.trans (D.hrm r hr).2)))]
    rw [← hleq, hzs, hzx]
  refine ⟨fun s hs => ?_, fun t' ht' => ?_⟩
  · obtain ⟨l, hl, -, hfl⟩ := key s hs
    have hl0 : 0 < l := lt_of_lt_of_le one_pos hl
    refine ⟨l⁻¹ * t, ⟨by positivity, ?_⟩, hfl⟩
    have : l⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl
    nlinarith
  · set g : ℝ → ℝ := fun s => morseNorm n ((D.chart r hr).χ.symm (D.flow s x)) with hgdef
    have hg : ∀ s, 0 ≤ s → ∃ l : ℝ, 1 ≤ l ∧ g s = l⁻¹ * t ∧
        D.flow s x = (D.chart r hr).χ (recombine (D.chart r hr).hk 0 ((l⁻¹ * t) • e)) := by
      intro s hs
      obtain ⟨l, hl, h1, h2⟩ := key s hs
      have hl0 : 0 < l := lt_of_lt_of_le one_pos hl
      refine ⟨l, hl, ?_, h2⟩
      simp only [hgdef, h1]
      exact hnorm_ray _ (by positivity)
    have hcapt : x ∈ D.captured r hr := ⟨0, by
      rw [GradientLikeStrip.flow_zero]; exact ⟨y, ⟨hyrm, hyu⟩, rfl⟩⟩
    obtain ⟨T, hT⟩ := GradientLikeStrip.captured_eventually_small hcapt ht'.1
    set T' := max T 0 with hT'
    have hT'0 : 0 ≤ T' := le_max_right _ _
    have hgT : g T' < t' := by
      obtain ⟨z, hz, hzx⟩ := hT T' (le_max_left _ _)
      have hzs : (D.chart r hr).χ.symm (D.flow T' x) = z := by
        rw [← hzx, (D.chart r hr).χ.left_inv ((D.chart r hr).hsrc z (hz.1.le.trans (ht'.2.trans htr.le |>.trans
          (D.hrm r hr).2)))]
      simp only [hgdef, hzs]
      exact hz.1
    have hg0 : g 0 = t := by
      simp only [hgdef, GradientLikeStrip.flow_zero, hxdef]
      rw [(D.chart r hr).χ.left_inv ((D.chart r hr).hsrc y (hyrm.le.trans (D.hrm r hr).2))]
      exact hyn
    have hgc : ContinuousOn g (Icc 0 T') := by
      have hder := GradientLikeStrip.hasDerivAt_symm_flow_Icc hr
        (fun s (hs : s ∈ Icc 0 T') => hball s hs.1)
      intro s hs
      exact (continuous_morseNorm.continuousAt.comp
        (hder s hs).continuousAt).continuousWithinAt
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' hT'0 hgc ⟨hgT.le, hg0 ▸ ht'.2⟩
    obtain ⟨l, -, hgl, hfl⟩ := hg s hs.1
    refine ⟨s, hs.1, ?_⟩
    rw [hfl, ← hgl, hgs]

theorem flow_ray_unstable (D : GradientLikeStrip I f a b crit) (hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {r : M} (hr : r ∈ crit) {e : EuclideanSpace ℝ (Fin (D.chart r hr).k)} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) (htr : t < D.rm r hr) :
    (∀ s, 0 ≤ s → ∃ t' ∈ Ioc 0 t,
        D.flow (-s) ((D.chart r hr).χ (recombine (D.chart r hr).hk (t • e) 0)) =
          (D.chart r hr).χ (recombine (D.chart r hr).hk (t' • e) 0)) ∧
      ∀ t' ∈ Ioc 0 t, ∃ s, 0 ≤ s ∧
        D.flow (-s) ((D.chart r hr).χ (recombine (D.chart r hr).hk (t • e) 0)) =
          (D.chart r hr).χ (recombine (D.chart r hr).hk (t' • e) 0) := by
  have _ := hfs
  set y : Fin n → ℝ := recombine (D.chart r hr).hk (t • e) 0 with hydef
  set x := (D.chart r hr).χ y with hx
  have hr₀ := (D.chart r hr).hr₀
  have hneg_y : negPart (D.chart r hr).hk y = t • e :=
    ModelField.negPart_recombine (D.chart r hr).hk _ _
  have hpos_y : posPart (D.chart r hr).hk y = 0 :=
    ModelField.posPart_recombine (D.chart r hr).hk _ _
  have hnorm_te : ‖t • e‖ = t := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  have hny : morseNorm n y = t := by
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart r hr).hk y
    rw [hneg_y, hpos_y, hnorm_te, norm_zero] at h1
    have h2 := ModelField.morseNorm_nonneg y
    nlinarith
  have hy : morseNorm n y < D.rm r hr := by rw [hny]; exact htr
  have hstay : ∀ τ, τ ≤ 0 → D.flow τ x ∈ (D.chart r hr).χ ''
      {z | morseNorm n z ≤ morseNorm n y ∧ posPart (D.chart r hr).hk z = 0} :=
    fun τ hτ => D.flow_mem_of_posPart_eq_zero hr hy hpos_y hτ
  have hmodel : ∀ τ, τ ≤ 0 → D.flow τ x ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} :=
    fun τ hτ => image_mono
      (fun z (hz : morseNorm n z ≤ morseNorm n y ∧ posPart (D.chart r hr).hk z = 0) =>
        hz.1.trans_lt hy) (hstay τ hτ)
  have part1 : ∀ s, 0 ≤ s → ∃ t' ∈ Ioc 0 t,
      D.flow (-s) x = (D.chart r hr).χ (recombine (D.chart r hr).hk (t' • e) 0) := by
    intro s hs
    have hball : ∀ τ ∈ uIcc 0 (-s),
        D.flow τ x ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} := by
      intro τ hτ
      rw [uIcc_of_ge (by linarith)] at hτ
      exact hmodel τ hτ.2
    obtain ⟨l, hl0, -, hl1, heq⟩ := model_flow_scaling D hr hy hball
    have hl1 := hl1 (by linarith)
    refine ⟨l * t, ⟨mul_pos hl0 ht, ?_⟩, ?_⟩
    · nlinarith
    · have h1 : (D.chart r hr).χ ((D.chart r hr).χ.symm (D.flow (-s) x)) = D.flow (-s) x :=
        (D.chart r hr).symm_image_eq
          (D.modelBall_subset_image_ball r hr (hmodel (-s) (by linarith)))
      rw [← h1, heq, hneg_y, hpos_y, smul_zero, smul_smul]
  refine ⟨part1, ?_⟩
  intro t' ht'
  set θ₀ : ℝ := (t ^ 2 + (D.chart r hr).r₀ ^ 2)⁻¹ with hθ₀
  have hθ₀pos : 0 < θ₀ := by positivity
  set S : ℝ := t ^ 2 / (2 * θ₀ * t' ^ 2) with hS
  have hS0 : 0 ≤ S := by
    have := ht'.1
    positivity
  have hball : ∀ τ ∈ Icc (-S) 0,
      D.flow τ x ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} :=
    fun τ hτ => hmodel τ hτ.2
  set γ : ℝ → Fin n → ℝ := fun τ => (D.chart r hr).χ.symm (D.flow τ x) with hγdef
  have hγ : ∀ τ ∈ Icc (-S) 0,
      HasDerivAt γ (ModelField.modelField (D.chart r hr).k (D.chart r hr).r₀ (γ τ)) τ :=
    GradientLikeStrip.hasDerivAt_symm_flow_Icc hr hball
  have hγ0 : γ 0 = y := by
    simp only [hγdef, GradientLikeStrip.flow_zero]
    exact (D.chart r hr).χ.left_inv ((D.chart r hr).hsrc y (hy.le.trans (D.hrm r hr).2))
  have hγle : ∀ τ ∈ Icc (-S) 0, morseNorm n (γ τ) ≤ t := by
    intro τ hτ
    obtain ⟨z, hz, hzs⟩ := hstay τ hτ.2
    change morseNorm n ((D.chart r hr).χ.symm (D.flow τ x)) ≤ t
    rw [← hzs, (D.chart r hr).χ.left_inv
      ((D.chart r hr).hsrc z (hz.1.trans (hy.le.trans (D.hrm r hr).2))), ← hny]
    exact hz.1
  have hθ : ∀ τ ∈ Icc (-S) 0, θ₀ ≤ ModelField.theta (D.chart r hr).r₀ (γ τ) :=
    fun τ hτ => ModelField.theta_ge_of_le hr₀ (hγle τ hτ)
  have hlin := ModelField.normSq_negPart_ge_linear (D.chart r hr).hk hr₀ hγ hθ 0
    (right_mem_Icc.2 (by linarith))
  rw [hγ0, hneg_y, hnorm_te] at hlin
  have hend : ‖negPart (D.chart r hr).hk (γ (-S))‖ ≤ t' := by
    have h1 : ‖negPart (D.chart r hr).hk (γ (-S))‖ ^ 2 * (1 + 2 * θ₀ * S) ≤ t ^ 2 := by
      nlinarith
    have h2 : 2 * θ₀ * S * t' ^ 2 = t ^ 2 := by
      rw [hS]
      have := ht'.1
      field_simp
    have h3 := sq_nonneg ‖negPart (D.chart r hr).hk (γ (-S))‖
    have h4 : ‖negPart (D.chart r hr).hk (γ (-S))‖ ^ 2 ≤ t' ^ 2 := by
      by_contra hcon
      push Not at hcon
      have h5 : t' ^ 2 * (2 * θ₀ * S) <
          ‖negPart (D.chart r hr).hk (γ (-S))‖ ^ 2 * (2 * θ₀ * S) := by
        have : 0 < 2 * θ₀ * S := by
          have h6 : 0 < t ^ 2 := by positivity
          nlinarith
        exact mul_lt_mul_of_pos_right hcon this
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) ht'.1.le two_ne_zero).1 h4
  have hcont : ContinuousOn (fun τ => ‖negPart (D.chart r hr).hk (γ τ)‖) (Icc (-S) 0) :=
    (continuous_norm.comp (ModelField.negPartL (D.chart r hr).hk).continuous).comp_continuousOn
      (ModelField.continuousOn_curve hγ)
  have hstart : ‖negPart (D.chart r hr).hk (γ 0)‖ = t := by rw [hγ0, hneg_y, hnorm_te]
  obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc (by linarith : -S ≤ 0) hcont
    ⟨hend, by rw [hstart]; exact ht'.2⟩
  refine ⟨-σ, by linarith [hσ.2], ?_⟩
  obtain ⟨τ, hτ, hτeq⟩ := part1 (-σ) (by linarith [hσ.2])
  rw [neg_neg] at hτeq
  have hγσ : γ σ = recombine (D.chart r hr).hk (τ • e) 0 := by
    change (D.chart r hr).χ.symm (D.flow σ x) = _
    rw [hτeq]
    refine (D.chart r hr).χ.left_inv ((D.chart r hr).hsrc _ ?_)
    have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart r hr).hk (recombine (D.chart r hr).hk (τ • e) 0)
    rw [ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul, he,
      mul_one, Real.norm_eq_abs, abs_of_pos hτ.1] at h1
    have h2 : morseNorm n (recombine (D.chart r hr).hk (τ • e) 0) ≤ t :=
      MorseNormalChart.morseNorm_le_of_sq_le ht.le (by nlinarith [hτ.2, hτ.1])
    exact (h2.trans htr.le).trans (D.hrm r hr).2
  have hττ : τ = t' := by
    simp only at hσeq
    rw [hγσ, ModelField.negPart_recombine, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hτ.1] at hσeq
    exact hσeq
  rw [neg_neg, hτeq, hττ]

end Backward

end CrossField

end

end DifferentialGeometry.Topology
