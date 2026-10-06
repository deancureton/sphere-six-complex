module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerPi1
public import Mathlib.Geometry.Manifold.Instances.Icc

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

section Birth

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_flowBox_of_levelChart (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {x₀ : M} {c L ρ : ℝ} (hx₀ : f x₀ = c) (hL : 0 < L)
    (hρ : 0 < ρ) (hab : a < c - ρ ∧ c + L + ρ < b)
    (ψ₀ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n)
    (hψ₀ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ₀ ψ₀.source)
    (hψ₀s : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ₀.symm ψ₀.target) (hψ₀0 : ψ₀ 0 = x₀)
    (hψ₀f : ∀ y ∈ ψ₀.source, f (ψ₀ y) = c + y i₀) (hface : bottomFace i₀ ρ ⊆ ψ₀.source)
    (htube : ∀ y ∈ bottomFace i₀ ρ, ∀ s ∈ Icc (-(L + ρ)) ρ, ∀ p (hp : p ∈ crit),
      D.flow s (ψ₀ y) ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') :
    Nonempty (FlowBox D x₀ c L ρ) := by
  have _ := hx₀
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  obtain ⟨e, he⟩ : ∃ e : Fin n → ℝ, e = Pi.single i₀ (1 : ℝ) := ⟨_, rfl⟩
  have he_i : e i₀ = 1 := by simp [he]
  have he_j : ∀ j, j ≠ i₀ → e j = 0 := fun j hj => by simp [he, hj]
  have hproj : ∀ y : Fin n → ℝ, (y - y i₀ • e) i₀ = 0 := by
    intro y; simp [he_i]
  have hproj_j : ∀ y : Fin n → ℝ, ∀ j, j ≠ i₀ → (y - y i₀ • e) j = y j := by
    intro y j hj; simp [he_j j hj]
  have hbox_face : ∀ y ∈ boxSet i₀ ρ L, y - y i₀ • e ∈ bottomFace i₀ ρ := by
    intro y hy
    refine ⟨fun j hj => ?_, hproj y⟩
    rw [hproj_j y j hj]
    exact hy.1 j hj
  have hcI : c ∈ Icc a b := ⟨by linarith [hab.1], by linarith [hab.2]⟩
  have htube_f : ∀ y ∈ bottomFace i₀ ρ, ∀ s ∈ Icc (-(L + ρ)) ρ,
      f (D.flow s (ψ₀ y)) = c - s := by
    intro y hy s hs
    have hfy : f (ψ₀ y) = c := by rw [hψ₀f y (hface hy), hy.2, add_zero]
    have hsub : uIcc 0 s ⊆ Icc (-(L + ρ)) ρ :=
      uIcc_subset_Icc ⟨by linarith, by linarith⟩ hs
    have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hfs (x := ψ₀ y) (T := s)
      (by rw [hfy]; exact hcI)
      (by rw [hfy]; constructor <;> linarith [hs.1, hs.2, hab.1, hab.2])
      (fun u hu p hp hmem => htube y hy u (hsub hu) p hp (D.smallBall_subset_image_ball p hp hmem))
    rw [h s right_mem_uIcc, hfy]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin n → ℝ) → M, ∀ y, Ψ y = D.flow (-(y i₀)) (ψ₀ (y - y i₀ • e)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M → (Fin n → ℝ), ∀ x, Φ x = ψ₀.symm (D.π c x) + (f x - c) • e :=
    ⟨_, fun _ => rfl⟩
  have hmemI : ∀ y ∈ boxSet i₀ ρ L, -(y i₀) ∈ Icc (-(L + ρ)) ρ := fun y hy =>
    ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩
  have hΨlevel : ∀ y ∈ boxSet i₀ ρ L, f (Ψ y) = c + y i₀ := by
    intro y hy
    rw [hΨ, htube_f _ (hbox_face y hy) _ (hmemI y hy)]
    ring
  have hΨΩ : ∀ y ∈ boxSet i₀ ρ L, Ψ y ∈ D.regularFlowDomain c := by
    intro y hy
    refine ⟨by rw [hΨlevel y hy]; constructor <;> linarith [hy.2.1, hy.2.2, hab.1, hab.2],
      fun s hs p hp hmem => ?_⟩
    rw [hΨlevel y hy, add_sub_cancel_left] at hs
    rw [hΨ, D.flow_flow] at hmem
    refine htube _ (hbox_face y hy) (-(y i₀) + s) ?_ p hp
      (D.closedSmallBall_subset_image_ball p hp hmem)
    rw [mem_uIcc] at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith [hy.2.1, hy.2.2]
    · constructor <;> linarith [hy.2.1, hy.2.2]
  have hπΨ : ∀ y ∈ boxSet i₀ ρ L, D.π c (Ψ y) = ψ₀ (y - y i₀ • e) := by
    intro y hy
    unfold GradientLikeStrip.π
    rw [hΨlevel y hy, show c + y i₀ - c = y i₀ by ring, hΨ, D.flow_flow, neg_add_cancel,
      D.flow_zero]
  have hΦΨ : ∀ y ∈ boxSet i₀ ρ L, Φ (Ψ y) = y := by
    intro y hy
    rw [hΦ, hπΨ y hy, ψ₀.left_inv (hface (hbox_face y hy)), hΨlevel y hy,
      show c + y i₀ - c = y i₀ by ring, sub_add_cancel]
  have hbox_open : IsOpen (boxSet i₀ ρ L) := by
    have hEq : boxSet i₀ ρ L = (⋂ j, {y : Fin n → ℝ | j ≠ i₀ → |y j| < ρ}) ∩
        ({y | -ρ < y i₀} ∩ {y | y i₀ < L + ρ}) := by
      ext y
      simp [boxSet]
    rw [hEq]
    refine (isOpen_iInter_of_finite fun j => ?_).inter
      ((isOpen_lt continuous_const (continuous_apply i₀)).inter
        (isOpen_lt (continuous_apply i₀) continuous_const))
    by_cases hj : j = i₀
    · simp [hj]
    · simpa [hj] using isOpen_lt ((continuous_apply j).abs) continuous_const
  set O : Set M := D.regularFlowDomain c ∩ D.π c ⁻¹' ψ₀.target with hO
  have hOopen : IsOpen O :=
    (D.isOpen_regularFlowDomain hfs.continuous c).inter (ψ₀.open_target.preimage (D.continuous_π hfs c))
  have hΦsm : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ Φ O := by
    rw [funext hΦ]
    refine ContMDiffOn.add ?_ ?_
    · exact hψ₀s.comp (D.contMDiff_π hfs c).contMDiffOn (fun x hx => hx.2)
    · exact ((hfs.sub contMDiff_const).smul contMDiff_const).contMDiffOn
  set T : Set M := O ∩ Φ ⁻¹' boxSet i₀ ρ L with hT
  have hTopen : IsOpen T := hΦsm.continuousOn.isOpen_inter_preimage hOopen hbox_open
  have hΨT : MapsTo Ψ (boxSet i₀ ρ L) T := by
    intro y hy
    refine ⟨⟨hΨΩ y hy, ?_⟩, ?_⟩
    · change D.π c (Ψ y) ∈ ψ₀.target
      rw [hπΨ y hy]
      exact ψ₀.map_source (hface (hbox_face y hy))
    · change Φ (Ψ y) ∈ boxSet i₀ ρ L
      rw [hΦΨ y hy]
      exact hy
  have hΦT : MapsTo Φ T (boxSet i₀ ρ L) := fun x hx => hx.2
  have hΨΦ : ∀ x ∈ T, Ψ (Φ x) = x := by
    intro x hx
    obtain ⟨⟨hxΩ, hxt⟩, -⟩ := hx
    have hxt' : D.π c x ∈ ψ₀.target := hxt
    have hw_src : ψ₀.symm (D.π c x) ∈ ψ₀.source := ψ₀.map_target hxt'
    have hw0 : ψ₀.symm (D.π c x) i₀ = 0 := by
      have h := hψ₀f _ hw_src
      rw [ψ₀.right_inv hxt', GradientLikeStrip.f_π hfs hcI hxΩ] at h
      linarith
    have hΦi : Φ x i₀ = f x - c := by
      rw [hΦ, Pi.add_apply, Pi.smul_apply, hw0, he_i, smul_eq_mul, mul_one, zero_add]
    have hΦproj : Φ x - Φ x i₀ • e = ψ₀.symm (D.π c x) := by
      rw [hΦi, hΦ, add_sub_cancel_right]
    rw [hΨ, hΦproj, hΦi, ψ₀.right_inv hxt']
    unfold GradientLikeStrip.π
    exact D.flow_neg_flow x _
  have hΨsm : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ Ψ (boxSet i₀ ρ L) := by
    rw [funext hΨ]
    have h1 : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun y : Fin n → ℝ => (-(y i₀), ψ₀ (y - y i₀ • e))) (boxSet i₀ ρ L) := by
      refine ContMDiffOn.prodMk ?_ ?_
      · exact (contDiff_apply ℝ ℝ i₀).neg.contMDiff.contMDiffOn
      · refine hψ₀.comp ?_ (fun y hy => hface (hbox_face y hy))
        exact (contDiff_id.sub ((contDiff_apply ℝ ℝ i₀).smul contDiff_const)).contMDiff.contMDiffOn
    exact D.contMDiff_flow_joint.comp_contMDiffOn h1
  obtain ⟨E, hEs, -, hEΨ, -, hEsm, hEsms⟩ :=
    exists_openPartialHomeomorph_of_inverse (I := I) hbox_open hTopen hΨT hΦT hΦΨ hΨΦ hΨsm
      (hΦsm.mono inter_subset_left)
  have h0box : (0 : Fin n → ℝ) ∈ boxSet i₀ ρ L :=
    ⟨fun j _ => by simpa using hρ, by simp; linarith, by simp; linarith⟩
  refine ⟨{
      ψ := E
      i₀ := i₀
      map_zero := ?_
      box_subset := hEs.symm.subset
      smooth := hEsm
      smooth_symm := hEsms
      level := ?_
      vertical := ?_
      avoid := ?_ }⟩
  · rw [hEΨ 0 h0box, hΨ]
    simp [hψ₀0]
  · intro y hy
    rw [hEΨ y hy]
    exact hΨlevel y hy
  · intro y hy s hys
    rw [← he] at hys ⊢
    rw [hEΨ y hy, hEΨ _ hys, hΨ, hΨ, D.flow_flow]
    have h1 : (y - s • e) i₀ = y i₀ - s := by
      rw [Pi.sub_apply, Pi.smul_apply, he_i, smul_eq_mul, mul_one]
    rw [h1, show y - s • e - (y i₀ - s) • e = y - y i₀ • e by rw [sub_smul]; abel,
      show -(y i₀) + s = -(y i₀ - s) by ring]
  · intro y hy p hp
    rw [hEΨ y hy, hΨ]
    exact htube _ (hbox_face y hy) _ (hmemI y hy) p hp

theorem exists_flowBox (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit) {x₀ : M}
    {c L : ℝ} (hx₀ : f x₀ = c) (hL : 0 < L) (hab : a < c ∧ c + L < b)
    (hfree : ∀ s ∈ Icc (-L) 0, ∀ p (hp : p ∈ crit),
      D.flow s x₀ ∉ closure ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'))
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ a < c - ρ ∧ c + L + ρ < b ∧ Nonempty (FlowBox D x₀ c L ρ) := by
  classical
  set S : Set (ℝ × M) := {q | ∀ p : crit, D.flow q.1 q.2 ∉
    closure ((D.chart p p.2).χ '' Metric.ball 0 (D.chart p p.2).R')} with hS
  have hSo : IsOpen S := by
    rw [hS, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun p =>
      isClosed_closure.isOpen_compl.preimage D.continuous_flow_joint
  have hsub : Icc (-L) 0 ×ˢ ({x₀} : Set M) ⊆ S := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    simp only [mem_singleton_iff] at hx
    subst hx
    intro p
    exact hfree s hs p p.2
  obtain ⟨u, V, hu, hV, hIu, hxV, huV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hSo hsub
  have hx₀V : x₀ ∈ V := hxV rfl
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 hu (-L) (hIu ⟨le_rfl, by linarith⟩)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.1 hu 0 (hIu ⟨by linarith, le_rfl⟩)
  have hx₀crit : x₀ ∉ crit := by
    intro hx
    have h0 := hfree 0 ⟨by linarith, le_rfl⟩ x₀ hx
    rw [D.flow_zero] at h0
    exact h0 (subset_closure (D.chart x₀ hx).p_mem_image_ball)
  have hnc : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x₀ := by
    intro hc
    have hlt := D.neg x₀ (by
      change f x₀ ∈ Icc a b
      rw [hx₀]; exact ⟨hab.1.le, by linarith⟩) hx₀crit
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hc
    rw [hc] at hlt
    simp at hlt
  obtain ⟨ψ₀, i₀, r, hr, hball, hψ₀0, hψ₀, hψ₀s, hψ₀f⟩ := exists_levelChart hf.smooth hnc
  have hnhds : ψ₀.source ∩ ψ₀ ⁻¹' V ∈ 𝓝 (0 : Fin n → ℝ) := by
    have h0s : (0 : Fin n → ℝ) ∈ ψ₀.source := hball (Metric.mem_ball_self hr)
    refine Filter.inter_mem (ψ₀.open_source.mem_nhds h0s) ?_
    exact (ψ₀.continuousAt h0s).preimage_mem_nhds (hV.mem_nhds (by rw [hψ₀0]; exact hx₀V))
  obtain ⟨r', hr', hr'sub⟩ := Metric.mem_nhds_iff.1 hnhds
  set ρ : ℝ := min (min ρ₀ (min ε₁ ε₂ / 2)) (min r' (min ((c - a) / 2) ((b - (c + L)) / 2)))
    with hρdef
  have hε : 0 < min ε₁ ε₂ / 2 := by positivity
  have hca : 0 < (c - a) / 2 := by linarith [hab.1]
  have hcb : 0 < (b - (c + L)) / 2 := by linarith [hab.2]
  have hρ : 0 < ρ := by
    simp only [hρdef, lt_min_iff]
    exact ⟨⟨hρ₀, hε⟩, hr', hca, hcb⟩
  have hρ1 : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ min ε₁ ε₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ r' := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ (c - a) / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρ5 : ρ ≤ (b - (c + L)) / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hm1 : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
  have hm2 : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
  have hab' : a < c - ρ ∧ c + L + ρ < b := ⟨by linarith, by linarith⟩
  have hfaceBall : bottomFace i₀ ρ ⊆ Metric.ball 0 r' := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_lt_of_le ((pi_norm_lt_iff hρ).2 fun j => ?_) hρ3
    by_cases hj : j = i₀
    · subst hj; rw [hy.2, norm_zero]; exact hρ
    · rw [Real.norm_eq_abs]; exact hy.1 j hj
  have hface : bottomFace i₀ ρ ⊆ ψ₀.source := fun y hy => (hr'sub (hfaceBall hy)).1
  have hfV : ∀ y ∈ bottomFace i₀ ρ, ψ₀ y ∈ V := fun y hy => (hr'sub (hfaceBall hy)).2
  have htube : ∀ y ∈ bottomFace i₀ ρ, ∀ s ∈ Icc (-(L + ρ)) ρ, ∀ p (hp : p ∈ crit),
      D.flow s (ψ₀ y) ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' := by
    intro y hy s hs p hp hmem
    have hsu : s ∈ u := by
      by_cases h1 : s < -L
      · apply hb₁
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1]
      · by_cases h2 : 0 < s
        · apply hb₂
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [hs.2]
        · exact hIu ⟨not_lt.1 h1, not_lt.1 h2⟩
    have hSmem : (s, ψ₀ y) ∈ S := huV ⟨hsu, hfV y hy⟩
    exact hSmem ⟨p, hp⟩ (subset_closure hmem)
  refine ⟨ρ, hρ, hρ1, hab'.1, hab'.2, ?_⟩
  exact exists_flowBox_of_levelChart hf D hx₀ hL hρ hab' ψ₀ i₀ hψ₀ hψ₀s hψ₀0
    (fun y hy => by rw [hψ₀f y hy, hx₀]) hface htube

theorem exists_canonical_birth_profile :
    ∃ (g : ℝ → ℝ) (t₁ t₂ : ℝ), ContDiff ℝ ∞ g ∧ -1 < t₁ ∧ t₁ < t₂ ∧ t₂ < 1 ∧
      (∀ x, x ∉ Ioo (-1 : ℝ) 1 → g x = x) ∧ (∀ x, deriv g x = 0 ↔ x = t₁ ∨ x = t₂) ∧
      deriv (deriv g) t₁ < 0 ∧ 0 < deriv (deriv g) t₂ ∧ g t₂ < g t₁ := by
  set φ : ℝ → ℝ := fun x => expNegInvGlue (1 - (2 * x + 1) ^ 2) with hφdef
  have hφc : ContDiff ℝ ∞ φ := expNegInvGlue.contDiff.comp (by fun_prop)
  have hφcont : Continuous φ := hφc.continuous
  have hφ0 : ∀ x, (x ≤ -1 ∨ 0 ≤ x) → φ x = 0 := by
    intro x hx
    apply expNegInvGlue.zero_of_nonpos
    rcases hx with hx | hx <;> nlinarith
  have hφnn : ∀ x, 0 ≤ φ x := fun x => expNegInvGlue.nonneg _
  have hφpos : ∀ x, -1 < x → x < 0 → φ x = Real.exp (-(1 - (2 * x + 1) ^ 2)⁻¹) := by
    intro x h1 h2
    have hq : 0 < 1 - (2 * x + 1) ^ 2 := by nlinarith
    change expNegInvGlue _ = _
    simp only [expNegInvGlue, not_le.mpr hq, ite_false]
  set Φ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t with hΦdef
  have hΦd : ∀ x, HasDerivAt Φ (φ x) x := fun x =>
    (hφcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hΦzero : ∀ a b, (∀ t ∈ Set.uIcc a b, φ t = 0) → ∫ t in a..b, φ t = 0 := by
    intro a b h
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) h]
    simp
  have hΦpos : ∀ x, 0 ≤ x → Φ x = 0 := by
    intro x hx
    exact hΦzero 0 x (fun t ht => hφ0 t (Or.inr (by rw [Set.uIcc_of_le hx] at ht; exact ht.1)))
  have hΦneg : ∀ x, x ≤ -1 → Φ x = Φ (-1) := by
    intro x hx
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hφcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (-1))
      (hφcont.intervalIntegrable (μ := MeasureTheory.volume) (-1) x)
    have h2 : ∫ t in (-1 : ℝ)..x, φ t = 0 :=
      hΦzero _ _ (fun t ht => hφ0 t (Or.inl (by rw [Set.uIcc_of_ge hx] at ht; exact ht.2)))
    simp only [hΦdef]
    rw [← h1, h2, add_zero]
  set k : ℝ := Real.exp (4 / 3) with hk
  have hkpos : 0 < k := Real.exp_pos _
  set g : ℝ → ℝ := fun x => x + k * (Φ (x - 1) - Φ x) with hgdef
  have hgd : ∀ x, HasDerivAt g (1 + k * (φ (x - 1) - φ x)) x := by
    intro x
    have h1 : HasDerivAt (fun x => Φ (x - 1)) (φ (x - 1)) x :=
      HasDerivAt.comp_sub_const x 1 (hΦd (x - 1))
    exact (hasDerivAt_id x).add ((h1.sub (hΦd x)).const_mul k)
  have hderiv : deriv g = fun x => 1 + k * (φ (x - 1) - φ x) :=
    funext fun x => (hgd x).deriv
  have hgc : ContDiff ℝ ∞ g := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hgd x).differentiableAt, ?_⟩
    rw [hderiv]
    have h1 : ContDiff ℝ ∞ (fun x : ℝ => φ (x - 1)) := hφc.comp (by fun_prop)
    exact contDiff_const.add (contDiff_const.mul (h1.sub hφc))
  have hloc : ∀ x, -1 < x → x < 0 →
      deriv g x = 1 - Real.exp (4 / 3 - (1 - (2 * x + 1) ^ 2)⁻¹) := by
    intro x h1 h2
    rw [hderiv]
    simp only
    rw [hφ0 (x - 1) (Or.inl (by linarith)), hφpos x h1 h2, hk, sub_eq_add_neg (4 / 3 : ℝ),
      Real.exp_add]
    ring
  have hiff : ∀ x, deriv g x = 0 ↔ x = -3 / 4 ∨ x = -1 / 4 := by
    intro x
    by_cases hx : -1 < x ∧ x < 0
    · rw [hloc x hx.1 hx.2]
      constructor
      · intro h
        have h1 : Real.exp (4 / 3 - (1 - (2 * x + 1) ^ 2)⁻¹) = 1 := by linarith
        rw [Real.exp_eq_one_iff] at h1
        have h2 : (1 - (2 * x + 1) ^ 2)⁻¹ = 4 / 3 := by linarith
        have h3 : 1 - (2 * x + 1) ^ 2 = 3 / 4 := by
          rw [inv_eq_iff_eq_inv] at h2
          rw [h2]
          norm_num
        have h4 : (x + 3 / 4) * (x + 1 / 4) = 0 := by nlinarith
        rcases mul_eq_zero.mp h4 with h | h
        · left; linarith
        · right; linarith
      · rintro (rfl | rfl) <;> norm_num
    · have h0 : φ x = 0 := by
        apply hφ0 x
        rcases le_or_gt x (-1) with hc | hc
        · exact Or.inl hc
        · rcases le_or_gt 0 x with hd | hd
          · exact Or.inr hd
          · exact absurd ⟨hc, hd⟩ hx
      rw [hderiv]
      simp only [h0, sub_zero]
      constructor
      · intro h
        nlinarith [hφnn (x - 1)]
      · rintro (rfl | rfl) <;> norm_num at hx
  set h : ℝ → ℝ := fun x => 1 - Real.exp (4 / 3 - (1 - (2 * x + 1) ^ 2)⁻¹) with hhdef
  have hdd : ∀ t, -1 < t → t < 0 → deriv (deriv g) t = deriv h t := by
    intro t h1 h2
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.eventually_of_mem (Ioo_mem_nhds h1 h2) (fun x hx => hloc x hx.1 hx.2)
  have hhd : ∀ t, 1 - (2 * t + 1) ^ 2 ≠ 0 →
      HasDerivAt h (-(Real.exp (4 / 3 - (1 - (2 * t + 1) ^ 2)⁻¹) *
        (-(-(-(2 * (2 * t + 1) * 2)) / (1 - (2 * t + 1) ^ 2) ^ 2)))) t := by
    intro t ht
    have hq : HasDerivAt (fun x : ℝ => 1 - (2 * x + 1) ^ 2) (-(2 * (2 * t + 1) * 2)) t := by
      have := ((((hasDerivAt_id t).const_mul 2).add_const 1).pow 2).const_sub 1
      exact this.congr_deriv (by simp only [id]; ring)
    exact ((hq.inv ht).const_sub (4 / 3)).exp.const_sub 1
  refine ⟨g, -3 / 4, -1 / 4, hgc, by norm_num, by norm_num, by norm_num, ?_, hiff, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
    simp only [hgdef]
    rcases hx with hx | hx
    · rw [hΦneg x hx, hΦneg (x - 1) (by linarith)]
      ring
    · rw [hΦpos x (by linarith), hΦpos (x - 1) (by linarith)]
      ring
  · rw [hdd _ (by norm_num) (by norm_num), (hhd _ (by norm_num)).deriv]
    norm_num
  · rw [hdd _ (by norm_num) (by norm_num), (hhd _ (by norm_num)).deriv]
    norm_num
  · have hanti : StrictAntiOn g (Set.Icc (-3 / 4 : ℝ) (-1 / 4)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hgc.continuous.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [hloc x (by linarith [hx.1]) (by linarith [hx.2])]
      have hq : 3 / 4 < 1 - (2 * x + 1) ^ 2 := by nlinarith [hx.1, hx.2]
      have hq' : (1 - (2 * x + 1) ^ 2)⁻¹ < 4 / 3 := by
        rw [inv_lt_comm₀ (by linarith) (by norm_num)]
        norm_num
        linarith
      have : 1 < Real.exp (4 / 3 - (1 - (2 * x + 1) ^ 2)⁻¹) := Real.one_lt_exp_iff.mpr (by linarith)
      linarith
    exact hanti ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)

theorem exists_birth_profile {α' β' S : ℝ} (hαβ : α' < β') (hS : 0 < S) :
    ∃ (g : ℝ → ℝ) (t₁ t₂ : ℝ), ContDiff ℝ ∞ g ∧ α' < t₁ ∧ t₁ < t₂ ∧ t₂ < β' ∧
      (∀ x, x ∉ Ioo α' β' → g x = x) ∧ (∀ x, |g x - x| < S) ∧
      (∀ x, deriv g x = 0 ↔ x = t₁ ∨ x = t₂) ∧
      deriv (deriv g) t₁ < 0 ∧ 0 < deriv (deriv g) t₂ ∧ g t₂ < g t₁ := by
  obtain ⟨g₀, t₁, t₂, hg₀, h1, h12, h2, hid, hcrit, hmax, hmin, hval⟩ :=
    exists_canonical_birth_profile
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun u => g₀ u - u) ((hg₀.continuous.sub continuous_id).continuousOn)
  have hbd : ∀ u, |g₀ u - u| ≤ C := by
    intro u
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · have := hC u hu
      simpa [Real.norm_eq_abs] using this
    · have hu' : u ∉ Ioo (-1 : ℝ) 1 := fun h => hu (Ioo_subset_Icc_self h)
      have h0 : |g₀ u - u| = 0 := by rw [hid u hu']; simp
      have := hC (-1) (by simp)
      rw [h0]
      exact le_trans (norm_nonneg _) this
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbd 0)
  set h : ℝ := (β' - α') / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set m : ℝ := (α' + β') / 2 with hm
  set lam : ℝ := min h (S / (C + 1)) with hlam
  have hlam0 : 0 < lam := lt_min hh0 (div_pos hS (by linarith))
  have hlamh : lam ≤ h := min_le_left _ _
  have hlamS : lam ≤ S / (C + 1) := min_le_right _ _
  have hlamne : lam ≠ 0 := hlam0.ne'
  set g : ℝ → ℝ := fun x => m + lam * g₀ ((x - m) / lam) with hgdef
  have hd₀ : Differentiable ℝ g₀ := hg₀.differentiable (by simp)
  have hg₀' : ContDiff ℝ ∞ (deriv g₀) := by
    simpa using hg₀.iterate_deriv 1
  have hd₁ : Differentiable ℝ (deriv g₀) := hg₀'.differentiable (by simp)
  have hinner : ∀ x, HasDerivAt (fun x : ℝ => (x - m) / lam) (1 / lam) x := by
    intro x
    simpa using ((hasDerivAt_id x).sub_const m).div_const lam
  have hderiv : deriv g = fun x => deriv g₀ ((x - m) / lam) := by
    funext x
    have h1 : HasDerivAt (g₀ ∘ fun x : ℝ => (x - m) / lam)
        (deriv g₀ ((x - m) / lam) * (1 / lam)) x :=
      (hd₀ _).hasDerivAt.comp x (hinner x)
    have h2 := (h1.const_mul lam).const_add m
    have e : lam * (deriv g₀ ((x - m) / lam) * (1 / lam)) = deriv g₀ ((x - m) / lam) := by
      field_simp
    rw [e] at h2
    exact h2.deriv
  have hderiv2 : deriv (deriv g) = fun x => deriv (deriv g₀) ((x - m) / lam) / lam := by
    rw [hderiv]
    funext x
    have h1 : HasDerivAt (deriv g₀ ∘ fun x : ℝ => (x - m) / lam)
        (deriv (deriv g₀) ((x - m) / lam) * (1 / lam)) x :=
      (hd₁ _).hasDerivAt.comp x (hinner x)
    have e : deriv (deriv g₀) ((x - m) / lam) * (1 / lam) =
        deriv (deriv g₀) ((x - m) / lam) / lam := by
      ring
    rw [e] at h1
    exact h1.deriv
  have hback : ∀ t, ((m + lam * t) - m) / lam = t := by
    intro t
    field_simp
    ring
  refine ⟨g, m + lam * t₁, m + lam * t₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : ContDiff ℝ ∞ (fun x : ℝ => (x - m) / lam) :=
      (contDiff_id.sub contDiff_const).div_const lam
    exact contDiff_const.add (contDiff_const.mul (hg₀.comp this))
  · have : -lam < lam * t₁ := by nlinarith
    rw [hm]; rw [hh] at hlamh; linarith
  · nlinarith
  · have : lam * t₂ < lam := by nlinarith
    rw [hm]; rw [hh] at hlamh; linarith
  · intro x hx
    have hu : (x - m) / lam ∉ Ioo (-1 : ℝ) 1 := by
      rintro ⟨hl, hr⟩
      apply hx
      rw [lt_div_iff₀ hlam0] at hl
      rw [div_lt_iff₀ hlam0] at hr
      rw [hm] at hl hr; rw [hh] at hlamh
      constructor <;> linarith
    change m + lam * g₀ ((x - m) / lam) = x
    rw [hid _ hu]
    field_simp
    ring
  · intro x
    have e : g x - x = lam * (g₀ ((x - m) / lam) - (x - m) / lam) := by
      change m + lam * g₀ ((x - m) / lam) - x = _
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos hlam0]
    have hb := hbd ((x - m) / lam)
    calc lam * |g₀ ((x - m) / lam) - (x - m) / lam| ≤ lam * C :=
          mul_le_mul_of_nonneg_left hb hlam0.le
      _ ≤ S / (C + 1) * C := mul_le_mul_of_nonneg_right hlamS hC0
      _ < S := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  · intro x
    rw [hderiv]
    simp only
    rw [hcrit]
    constructor
    · rintro (hx | hx)
      · left
        rw [← hx]; field_simp; ring
      · right
        rw [← hx]; field_simp; ring
    · rintro (hx | hx)
      · left; rw [hx, hback]
      · right; rw [hx, hback]
  · rw [hderiv2]
    simp only
    rw [hback]
    exact div_neg_of_neg_of_pos hmax hlam0
  · rw [hderiv2]
    simp only
    rw [hback]
    exact div_pos hmin hlam0
  · change m + lam * g₀ ((m + lam * t₂ - m) / lam) < m + lam * g₀ ((m + lam * t₁ - m) / lam)
    rw [hback, hback]
    nlinarith

theorem hessian_diagModel {F : (Fin n → ℝ) → ℝ} {g : ℝ → ℝ} (i₀ : Fin n) (w : Fin n → ℝ)
    (t : ℝ) (hg : ContDiff ℝ ∞ g) (hgt : deriv g t = 0) (hg2 : deriv (deriv g) t ≠ 0)
    (hw : ∀ j, j ≠ i₀ → w j ≠ 0)
    (hF : F =ᶠ[𝓝 (t • Pi.single i₀ (1 : ℝ))]
      fun y => g (y i₀) + ∑ j, (if j = i₀ then 0 else w j * y j ^ 2)) :
    fderiv ℝ F (t • Pi.single i₀ (1 : ℝ)) = 0 ∧
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt F (t • Pi.single i₀ (1 : ℝ)))).SeparatingLeft ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F (t • Pi.single i₀ (1 : ℝ))) =
        {j | j ≠ i₀ ∧ w j < 0}.ncard + (if deriv (deriv g) t < 0 then 1 else 0) := by
  classical
  set x₀ : Fin n → ℝ := t • Pi.single i₀ (1 : ℝ) with hx₀def
  have hx₀i : x₀ i₀ = t := by simp [x₀]
  have hx₀j : ∀ j, j ≠ i₀ → x₀ j = 0 := by
    intro j hj
    simp [x₀, hj]
  set G : (Fin n → ℝ) → ℝ :=
    fun y => g (y i₀) + ∑ j, (if j = i₀ then 0 else w j * y j ^ 2) with hGdef
  set W : Fin n → ℝ := fun j => if j = i₀ then deriv (deriv g) t else 2 * w j with hWdef
  let D : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun y =>
    deriv g (y i₀) • ContinuousLinearMap.proj i₀ +
      ∑ j, (if j = i₀ then 0 else 2 * w j * y j) • ContinuousLinearMap.proj j
  have hterm : ∀ (j : Fin n) (y : Fin n → ℝ),
      HasFDerivAt (fun y : Fin n → ℝ => if j = i₀ then 0 else w j * y j ^ 2)
        ((if j = i₀ then 0 else 2 * w j * y j) • (ContinuousLinearMap.proj j :
          (Fin n → ℝ) →L[ℝ] ℝ)) y := by
    intro j y
    by_cases hj : j = i₀
    · simp only [hj, ite_true, zero_smul]
      exact hasFDerivAt_const _ _
    · simp only [hj, ite_false]
      have h1 := ((hasFDerivAt_apply (𝕜 := ℝ) j y).pow 2).const_mul (w j)
      convert h1 using 1
      ext v
      simp
      ring
  have hgd : ∀ s, HasDerivAt g (deriv g s) s := fun s =>
    ((hg.differentiable (by simp)) s).hasDerivAt
  have hG1 : ∀ y : Fin n → ℝ, HasFDerivAt (fun y : Fin n → ℝ => g (y i₀))
      (deriv g (y i₀) • (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ)) y := fun y =>
    (hgd (y i₀)).comp_hasFDerivAt (f := fun y : Fin n → ℝ => y i₀) y (hasFDerivAt_apply i₀ y)
  have hGd : ∀ y, HasFDerivAt G (D y) y := by
    intro y
    have hs := HasFDerivAt.sum (u := Finset.univ) (x := y) (fun j _ => hterm j y)
    have := (hG1 y).add hs
    convert this using 1
    ext z
    simp [G, Finset.sum_apply]
  have hD : fderiv ℝ G = D := funext fun y => (hGd y).fderiv
  have hdg : ContDiff ℝ ∞ (deriv g) := by
    have := hg.iterate_deriv 1
    simpa using this
  have hgdd : HasDerivAt (deriv g) (deriv (deriv g) t) t :=
    ((hdg.differentiable (by simp)) t).hasDerivAt
  have hA : HasFDerivAt (fun y : Fin n → ℝ => deriv g (y i₀))
      (deriv (deriv g) t • (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ)) x₀ := by
    have hgdd' : HasDerivAt (deriv g) (deriv (deriv g) t) (x₀ i₀) := by
      rw [hx₀i]
      exact hgdd
    exact hgdd'.comp_hasFDerivAt (f := fun y : Fin n → ℝ => y i₀) x₀ (hasFDerivAt_apply i₀ x₀)
  have hB : ∀ j : Fin n, HasFDerivAt (fun y : Fin n → ℝ => if j = i₀ then 0 else 2 * w j * y j)
      ((if j = i₀ then 0 else 2 * w j) • (ContinuousLinearMap.proj j :
        (Fin n → ℝ) →L[ℝ] ℝ)) x₀ := by
    intro j
    by_cases hj : j = i₀
    · simp only [hj, ite_true, zero_smul]
      exact hasFDerivAt_const _ _
    · simp only [hj, ite_false]
      have h1 := (hasFDerivAt_apply (𝕜 := ℝ) j x₀).const_mul (2 * w j)
      convert h1 using 1
  have hD2 : HasFDerivAt D
      ((deriv (deriv g) t • (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ)).smulRight
          (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ) +
        ∑ j, ((if j = i₀ then 0 else 2 * w j) • (ContinuousLinearMap.proj j :
          (Fin n → ℝ) →L[ℝ] ℝ)).smulRight (ContinuousLinearMap.proj j :
            (Fin n → ℝ) →L[ℝ] ℝ)) x₀ := by
    have h1 := hA.smul_const (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ)
    have h2 := HasFDerivAt.sum (u := Finset.univ) (x := x₀)
      (fun j _ => (hB j).smul_const (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))
    have := h1.add h2
    convert this using 1
    funext y
    simp [D, Finset.sum_apply]
  have hH : ∀ u v : Fin n → ℝ, fderiv ℝ (fderiv ℝ G) x₀ u v = ∑ j, W j * u j * v j := by
    intro u v
    rw [hD, hD2.fderiv]
    simp only [add_apply, sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hsplit : ∀ j, W j * u j * v j =
        (if j = i₀ then deriv (deriv g) t * u j * v j else 0) +
          (if j = i₀ then 0 else 2 * w j) * u j * v j := by
      intro j
      by_cases hj : j = i₀ <;> simp [W, hj]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀]
    simp only [Finset.mem_univ, ite_true]
  have hGc : ContDiffAt ℝ 2 G x₀ := by
    have h1 : ContDiff ℝ 2 (fun y : Fin n → ℝ => g (y i₀)) :=
      (hg.of_le (by simp)).comp (contDiff_apply ℝ ℝ i₀)
    have h2 : ContDiff ℝ 2 (fun y : Fin n → ℝ => ∑ j, (if j = i₀ then 0 else w j * y j ^ 2)) := by
      apply ContDiff.sum
      intro j _
      by_cases hj : j = i₀
      · simp only [hj, ite_true]
        exact contDiff_const
      · simp only [hj, ite_false]
        exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).pow 2)
    exact (h1.add h2).contDiffAt
  have hHess : DifferentialGeometry.Topology.Morse.chartHessianAt G x₀ = QuadraticMap.weightedSumSquares ℝ W := by
    ext v
    rw [MonotoneShift.chartHessianAt_apply, hH, QuadraticMap.weightedSumSquares_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_eq_mul]
    ring
  have hFH : DifferentialGeometry.Topology.Morse.chartHessianAt F x₀ = DifferentialGeometry.Topology.Morse.chartHessianAt G x₀ := MorseExistence.chartHessianAt_congr hF
  refine ⟨?_, ?_, ?_⟩
  · rw [hF.fderiv_eq, hD]
    ext z
    simp only [D, hx₀i, hgt, zero_smul, zero_add, sum_apply,
      smul_apply, zero_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = i₀
    · simp [hj]
    · simp [hj, hx₀j j hj]
  · rw [hFH, MorseExistence.separatingLeft_assoc_iff hGc]
    intro v hv
    funext j
    have h := hv (Pi.single j 1)
    rw [hH] at h
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    have hWj : W j ≠ 0 := by
      by_cases hj : j = i₀
      · simp only [W, hj, ite_true]
        exact hg2
      · simp only [W, hj, ite_false]
        exact mul_ne_zero two_ne_zero (hw j hj)
    simpa using (mul_eq_zero.mp h).resolve_left hWj
  · rw [hFH, hHess, QuadraticForm.sigNeg_weightedSumSquares]
    by_cases hneg : deriv (deriv g) t < 0
    · simp only [hneg, ite_true]
      have hset : {i | W i < 0} = insert i₀ {j | j ≠ i₀ ∧ w j < 0} := by
        ext j
        by_cases hj : j = i₀
        · simp [W, hj, hneg]
        · have h2w : (2 * w j < 0 ↔ w j < 0) := by
            constructor <;> intro h <;> linarith
          simp [W, hj, h2w]
      rw [hset, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _)]
    · simp only [hneg, ite_false, add_zero]
      congr 1
      ext j
      by_cases hj : j = i₀
      · simp [W, hj, hneg]
      · have h2w : (2 * w j < 0 ↔ w j < 0) := by
          constructor <;> intro h <;> linarith
        simp [W, hj, h2w]

theorem fderiv_taperedModel_eq_zero_iff (i₀ : Fin n) {κ : ℝ} (hκ : 0 < κ) {w : Fin n → ℝ}
    (hw : ∀ j, j ≠ i₀ → |w j| = κ) {s a b γ : ℝ → ℝ} (hs : ContDiff ℝ ∞ s)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hγ : ContDiff ℝ ∞ γ) {t₁ t₂ : ℝ}
    (hs' : ∀ x, deriv s x = -1 ↔ x = t₁ ∨ x = t₂) (ha0 : a 0 = 1)
    (hsa : ∀ x t, |s x * deriv a t| < κ)
    (hba : ∃ U : Set ℝ, IsOpen U ∧ tsupport a ⊆ U ∧ EqOn b 1 U)
    (hγs : ∃ U : Set ℝ, IsOpen U ∧ tsupport s ⊆ U ∧ EqOn γ 1 U)
    (hγb : ∀ x t, 0 ≤ t → |deriv γ x| * (κ * t * |b t|) < 1) :
    ∀ y, fderiv ℝ (taperedModel i₀ w s a b γ) y = 0 ↔
      y = t₁ • Pi.single i₀ (1 : ℝ) ∨ y = t₂ • Pi.single i₀ (1 : ℝ) := by
  intro y
  classical
  have _ : 0 ≤ κ := hκ.le
  have hsq : ∀ (c : Fin n → ℝ) (z : Fin n → ℝ),
      HasFDerivAt (fun y : Fin n → ℝ => ∑ j, c j * y j ^ 2)
        (∑ j, (c j * (2 * z j)) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) z := by
    intro c z
    apply HasFDerivAt.fun_sum
    intro j _
    have h1 := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) j z).pow 2).const_mul (c j)
    convert h1 using 1
    ext v
    simp
    ring
  have hR : offAxisSq i₀ = fun y : Fin n → ℝ => ∑ j, (if j = i₀ then 0 else 1) * y j ^ 2 := by
    funext y
    simp only [offAxisSq]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hQ : diagQuad i₀ w = fun y : Fin n → ℝ => ∑ j, (if j = i₀ then 0 else w j) * y j ^ 2 := by
    funext y
    simp only [diagQuad]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hx : ∀ z : Fin n → ℝ, HasFDerivAt (fun y : Fin n → ℝ => y i₀)
      (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ) z := fun z =>
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i₀ z
  have hdiff : ∀ {g : ℝ → ℝ}, ContDiff ℝ ∞ g → ∀ t, HasDerivAt g (deriv g t) t := fun hg t =>
    ((hg.differentiable (by simp)) t).hasDerivAt
  have hDv : ∀ z v : Fin n → ℝ, fderiv ℝ (taperedModel i₀ w s a b γ) z v =
      v i₀ + (s (z i₀) * (deriv a (offAxisSq i₀ z) *
          ∑ j, (if j = i₀ then 0 else 1) * (2 * z j) * v j) +
        a (offAxisSq i₀ z) * (deriv s (z i₀) * v i₀)) +
      (γ (z i₀) * diagQuad i₀ w z * (deriv b (offAxisSq i₀ z) *
          ∑ j, (if j = i₀ then 0 else 1) * (2 * z j) * v j) +
        b (offAxisSq i₀ z) * (γ (z i₀) * ∑ j, (if j = i₀ then 0 else w j) * (2 * z j) * v j +
          diagQuad i₀ w z * (deriv γ (z i₀) * v i₀))) := by
    intro z v
    have hr := hsq (fun j => if j = i₀ then 0 else 1) z
    have hq := hsq (fun j => if j = i₀ then 0 else w j) z
    rw [← hR] at hr
    rw [← hQ] at hq
    have hsx := (hdiff hs (z i₀)).comp_hasFDerivAt z (hx z)
    have hγx := (hdiff hγ (z i₀)).comp_hasFDerivAt z (hx z)
    have har := (hdiff ha (offAxisSq i₀ z)).comp_hasFDerivAt z hr
    have hbr := (hdiff hb (offAxisSq i₀ z)).comp_hasFDerivAt z hr
    have hF := ((hx z).add (hsx.mul har)).add ((hγx.mul hq).mul hbr)
    have hF' : HasFDerivAt (taperedModel i₀ w s a b γ) _ z := hF
    rw [hF'.fderiv]
    simp only [add_apply, smul_apply,
      FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply,
      Function.comp_apply, Pi.mul_apply, smul_eq_mul]
  have hsum0 : ∀ (c z : Fin n → ℝ),
      ∑ j, (if j = i₀ then 0 else c j) * (2 * z j) * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j = 0 := by
    intro c z
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i₀ <;> simp [hj]
  have hsumk : ∀ (c z : Fin n → ℝ) (k : Fin n), k ≠ i₀ →
      ∑ j, (if j = i₀ then 0 else c j) * (2 * z j) * (Pi.single k (1 : ℝ) : Fin n → ℝ) j = c k * (2 * z k) := by
    intro c z k hk
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hjk
      simp [hjk]
    · simp
  have hsumax : ∀ (c v : Fin n → ℝ) (t : ℝ),
      ∑ j, (if j = i₀ then 0 else c j) * (2 * (t • (Pi.single i₀ (1 : ℝ) : Fin n → ℝ)) j) * v j = 0 := by
    intro c v t
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i₀ <;> simp [hj]
  have hax : ∀ t : ℝ, offAxisSq i₀ (t • Pi.single i₀ (1 : ℝ)) = 0 ∧
      diagQuad i₀ w (t • Pi.single i₀ (1 : ℝ)) = 0 := by
    intro t
    constructor
    · simp only [offAxisSq]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i₀ <;> simp [hj]
    · simp only [diagQuad]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i₀ <;> simp [hj]
  constructor
  · intro h0
    have hD : ∀ v, fderiv ℝ (taperedModel i₀ w s a b γ) y v = 0 := fun v => by
      rw [h0]; rfl
    have h1 := hD (Pi.single i₀ 1)
    rw [hDv] at h1
    simp only [hsum0, Pi.single_eq_same, mul_zero, mul_one] at h1
    have hRnn : 0 ≤ offAxisSq i₀ y := by
      simp only [offAxisSq]
      refine Finset.sum_nonneg fun j _ => ?_
      split_ifs
      · exact le_rfl
      · positivity
    have hqle : |diagQuad i₀ w y| ≤ κ * offAxisSq i₀ y := by
      simp only [diagQuad, offAxisSq, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      by_cases hj : j = i₀
      · simp [hj]
      · simp only [hj, ↓reduceIte, abs_mul, hw j hj]
        rw [abs_of_nonneg (sq_nonneg _)]
    by_cases hsa0 : deriv s (y i₀) = 0 ∨ a (offAxisSq i₀ y) = 0
    · exfalso
      have hz : a (offAxisSq i₀ y) * deriv s (y i₀) = 0 := by
        rcases hsa0 with h | h <;> simp [h]
      rw [hz, add_zero] at h1
      have hlt := hγb (y i₀) (offAxisSq i₀ y) hRnn
      have hle : |b (offAxisSq i₀ y) * (diagQuad i₀ w y * deriv γ (y i₀))| ≤
          |deriv γ (y i₀)| * (κ * offAxisSq i₀ y * |b (offAxisSq i₀ y)|) := by
        rw [abs_mul, abs_mul]
        have h3 := abs_nonneg (b (offAxisSq i₀ y))
        have h4 := abs_nonneg (deriv γ (y i₀))
        calc |b (offAxisSq i₀ y)| * (|diagQuad i₀ w y| * |deriv γ (y i₀)|)
            ≤ |b (offAxisSq i₀ y)| * ((κ * offAxisSq i₀ y) * |deriv γ (y i₀)|) := by
              gcongr
          _ = _ := by ring
      have heq : b (offAxisSq i₀ y) * (diagQuad i₀ w y * deriv γ (y i₀)) = -1 := by linarith
      rw [heq] at hle
      norm_num at hle
      linarith
    · rw [not_or] at hsa0
      obtain ⟨hs0, ha0'⟩ := hsa0
      obtain ⟨U, hU, haU, hbU⟩ := hba
      obtain ⟨V, hV, hsV, hγV⟩ := hγs
      have hxV : y i₀ ∈ V := hsV (support_deriv_subset (Function.mem_support.2 hs0))
      have hRU : offAxisSq i₀ y ∈ U := haU (subset_tsupport a (Function.mem_support.2 ha0'))
      have hγ1 : γ (y i₀) = 1 := hγV hxV
      have hb1 : b (offAxisSq i₀ y) = 1 := hbU hRU
      have hb' : deriv b (offAxisSq i₀ y) = 0 := by
        rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hRU) hbU).deriv_eq]
        exact deriv_const _ _
      have hyk : ∀ k, k ≠ i₀ → y k = 0 := by
        intro k hk
        have h2 := hD (Pi.single k 1)
        rw [hDv] at h2
        simp only [hsumk _ _ k hk, Pi.single_eq_of_ne' hk, mul_zero,
          add_zero, zero_add, hγ1, hb1, hb', one_mul, zero_mul] at h2
        have hne : s (y i₀) * deriv a (offAxisSq i₀ y) + w k ≠ 0 := by
          intro h
          have hwk : w k = -(s (y i₀) * deriv a (offAxisSq i₀ y)) := by linarith
          have := hsa (y i₀) (offAxisSq i₀ y)
          rw [← abs_neg, ← hwk, hw k hk] at this
          exact lt_irrefl _ this
        have h3 : (2 * y k) * (s (y i₀) * deriv a (offAxisSq i₀ y) + w k) = 0 := by
          linear_combination h2
        rcases mul_eq_zero.1 h3 with h | h
        · linarith
        · exact absurd h hne
      have hR0 : offAxisSq i₀ y = 0 := by
        simp only [offAxisSq]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j = i₀
        · simp [hj]
        · simp [hj, hyk j hj]
      have hq0 : diagQuad i₀ w y = 0 := by
        simp only [diagQuad]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j = i₀
        · simp [hj]
        · simp [hj, hyk j hj]
      rw [hR0, hq0, ha0] at h1
      have hsx : deriv s (y i₀) = -1 := by linarith
      have hy : y = y i₀ • Pi.single i₀ (1 : ℝ) := by
        funext j
        by_cases hj : j = i₀
        · subst hj; simp
        · simp [hj, hyk j hj]
      rcases (hs' (y i₀)).1 hsx with h | h
      · left; rw [hy, h]
      · right; rw [hy, h]
  · have hback : ∀ t : ℝ, deriv s t = -1 →
        fderiv ℝ (taperedModel i₀ w s a b γ) (t • Pi.single i₀ (1 : ℝ)) = 0 := by
      intro t ht
      ext1 v
      rw [hDv, hsumax, hsumax, (hax t).1, (hax t).2, ha0]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ht]
      simp
    rintro (rfl | rfl)
    · exact hback t₁ ((hs' t₁).2 (Or.inl rfl))
    · exact hback t₂ ((hs' t₂).2 (Or.inr rfl))

theorem exists_model_pair_fat {l : ℕ} (hl : l < n) (i₀ : Fin n) {α β : ℝ} (hαβ : α < β) :
    ∃ (F : (Fin n → ℝ) → ℝ) (K : Set (Fin n → ℝ)) (t₁ t₂ : ℝ),
      ContDiff ℝ ∞ F ∧ IsCompact K ∧ K ⊆ {y | α < y i₀ ∧ y i₀ < β} ∧
      (∀ y, y ∉ K → F y = y i₀) ∧ (∀ y ∈ K, α < F y ∧ F y < β) ∧ t₁ < t₂ ∧
      t₁ • Pi.single i₀ (1 : ℝ) ∈ K ∧ t₂ • Pi.single i₀ (1 : ℝ) ∈ K ∧
      F (t₂ • Pi.single i₀ (1 : ℝ)) < F (t₁ • Pi.single i₀ (1 : ℝ)) ∧
      (∀ y, fderiv ℝ F y = 0 ↔
        y = t₁ • Pi.single i₀ (1 : ℝ) ∨ y = t₂ • Pi.single i₀ (1 : ℝ)) ∧
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₁ • Pi.single i₀ (1 : ℝ)))).SeparatingLeft ∧
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₂ • Pi.single i₀ (1 : ℝ)))).SeparatingLeft ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₁ • Pi.single i₀ (1 : ℝ))) = l + 1 ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₂ • Pi.single i₀ (1 : ℝ))) = l := by
  classical
  have bdd : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → ∀ p q : ℝ, (∀ x, x ∉ Icc p q → deriv h x = 0) →
      ∃ C, 0 ≤ C ∧ ∀ x, |deriv h x| ≤ C := by
    intro h hh p q hz
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := p) (b := q)).exists_bound_of_continuousOn
      (hh.continuous_deriv (by simp)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ Icc p q
    · have := hC x hx
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [hz x hx, abs_zero]
      exact le_max_right _ _
  have dz : ∀ (h : ℝ → ℝ) (c : ℝ) (U : Set ℝ), IsOpen U → (∀ x ∈ U, h x = c) →
      ∀ x ∈ U, deriv h x = 0 := by
    intro h c U hU hc x hx
    have hev : h =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hx) hc
    rw [hev.deriv_eq]
    simp
  set R₀ : ℝ → ℝ := Real.smoothTransition with hR₀def
  have hR₀c : ContDiff ℝ ∞ R₀ := Real.smoothTransition.contDiff
  have hR₀0 : ∀ u, u ≤ 0 → R₀ u = 0 := fun u hu => Real.smoothTransition.zero_of_nonpos hu
  have hR₀1 : ∀ u, 1 ≤ u → R₀ u = 1 := fun u hu => Real.smoothTransition.one_of_one_le hu
  have hR₀nn : ∀ u, 0 ≤ R₀ u := fun u => Real.smoothTransition.nonneg u
  have hR₀le : ∀ u, R₀ u ≤ 1 := fun u => Real.smoothTransition.le_one u
  set δ := β - α with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set x₀ := α + δ / 6 with hx₀def
  set x₁ := β - δ / 6 with hx₁def
  set ℓ := δ / 12 with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; positivity
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ → ℝ, γ = fun x => R₀ ((x - x₀) / ℓ) * R₀ ((x₁ - x) / ℓ) :=
    ⟨_, rfl⟩
  have hγc : ContDiff ℝ ∞ γ := by
    rw [hγdef]
    exact (hR₀c.comp ((contDiff_id.sub contDiff_const).div_const ℓ)).mul
      (hR₀c.comp ((contDiff_const.sub contDiff_id).div_const ℓ))
  have hγ0l : ∀ x, x ≤ x₀ → γ x = 0 := by
    intro x hx
    rw [hγdef]
    simp only
    rw [hR₀0 ((x - x₀) / ℓ) (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le), zero_mul]
  have hγ0r : ∀ x, x₁ ≤ x → γ x = 0 := by
    intro x hx
    rw [hγdef]
    simp only
    rw [hR₀0 ((x₁ - x) / ℓ) (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le), mul_zero]
  have hγ1 : ∀ x, x₀ + ℓ ≤ x → x ≤ x₁ - ℓ → γ x = 1 := by
    intro x h1 h2
    rw [hγdef]
    simp only
    rw [hR₀1 ((x - x₀) / ℓ) ((one_le_div hℓ).2 (by linarith)),
      hR₀1 ((x₁ - x) / ℓ) ((one_le_div hℓ).2 (by linarith)), mul_one]
  have hγnn : ∀ x, 0 ≤ γ x := by
    intro x; rw [hγdef]; exact mul_nonneg (hR₀nn _) (hR₀nn _)
  have hγle : ∀ x, γ x ≤ 1 := by
    intro x; rw [hγdef]
    exact (mul_le_mul (hR₀le _) (hR₀le _) (hR₀nn _) zero_le_one).trans (le_of_eq (one_mul 1))
  obtain ⟨Cγ, hCγ0, hCγ⟩ := bdd γ hγc x₀ x₁ (by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact dz γ 0 (Iio x₀) isOpen_Iio (fun z hz => hγ0l z (le_of_lt hz)) x hx
    · exact dz γ 0 (Ioi x₁) isOpen_Ioi (fun z hz => hγ0r z (le_of_lt hz)) x hx)
  set T := min (1 / (4 * (Cγ + 1))) (δ / 24) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hT1 : T ≤ 1 / (4 * (Cγ + 1)) := min_le_left _ _
  have hT2 : T ≤ δ / 24 := min_le_right _ _
  have hT1' : T * (4 * (Cγ + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hT1
  obtain ⟨a, hadef⟩ : ∃ a : ℝ → ℝ, a = fun t => 1 - R₀ (4 * t / T - 1) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ → ℝ, b = fun t => 1 - R₀ (t / T - 1) := ⟨_, rfl⟩
  have hac : ContDiff ℝ ∞ a := by
    rw [hadef]
    exact contDiff_const.sub (hR₀c.comp ((contDiff_const.mul contDiff_id).div_const T |>.sub
      contDiff_const))
  have hbc : ContDiff ℝ ∞ b := by
    rw [hbdef]
    exact contDiff_const.sub (hR₀c.comp (contDiff_id.div_const T |>.sub contDiff_const))
  have ha1 : ∀ t, t ≤ T / 4 → a t = 1 := by
    intro t ht
    rw [hadef]
    simp only
    have : 4 * t / T ≤ 1 := by rw [div_le_one hT]; linarith
    rw [hR₀0 _ (by linarith), sub_zero]
  have ha0' : ∀ t, T / 2 ≤ t → a t = 0 := by
    intro t ht
    rw [hadef]
    simp only
    have : 2 ≤ 4 * t / T := by rw [le_div_iff₀ hT]; linarith
    rw [hR₀1 _ (by linarith), sub_self]
  have hann : ∀ t, 0 ≤ a t := by intro t; rw [hadef]; simp only; linarith [hR₀le (4 * t / T - 1)]
  have hale : ∀ t, a t ≤ 1 := by intro t; rw [hadef]; simp only; linarith [hR₀nn (4 * t / T - 1)]
  have hb1 : ∀ t, t ≤ T → b t = 1 := by
    intro t ht
    rw [hbdef]
    simp only
    have : t / T ≤ 1 := by rw [div_le_one hT]; linarith
    rw [hR₀0 _ (by linarith), sub_zero]
  have hb0 : ∀ t, 2 * T ≤ t → b t = 0 := by
    intro t ht
    rw [hbdef]
    simp only
    have : 2 ≤ t / T := by rw [le_div_iff₀ hT]; linarith
    rw [hR₀1 _ (by linarith), sub_self]
  have hbnn : ∀ t, 0 ≤ b t := by intro t; rw [hbdef]; simp only; linarith [hR₀le (t / T - 1)]
  have hble : ∀ t, b t ≤ 1 := by intro t; rw [hbdef]; simp only; linarith [hR₀nn (t / T - 1)]
  obtain ⟨Ca, hCa0, hCa⟩ := bdd a hac (T / 4) (T / 2) (by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact dz a 1 (Iio (T / 4)) isOpen_Iio (fun z hz => ha1 z (le_of_lt hz)) x hx
    · exact dz a 0 (Ioi (T / 2)) isOpen_Ioi (fun z hz => ha0' z (le_of_lt hz)) x hx)
  set S := min (δ / 24) (1 / (2 * (Ca + 1))) with hSdef
  have hS : 0 < S := lt_min (by positivity) (by positivity)
  have hS1 : S ≤ δ / 24 := min_le_left _ _
  have hS2 : S * (2 * (Ca + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  set α' := α + δ / 3 with hα'def
  set β' := β - δ / 3 with hβ'def
  obtain ⟨g, t₁, t₂, hg, ht₁, ht₁₂, ht₂, hgid, hgS, hgcrit, hg₁, hg₂, hgap⟩ :=
    exists_birth_profile (α' := α') (β' := β') (by rw [hα'def, hβ'def]; linarith) hS
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ → ℝ, s = fun x => g x - x := ⟨_, rfl⟩
  have hsc : ContDiff ℝ ∞ s := by rw [hsdef]; exact hg.sub contDiff_id
  have hs0 : ∀ x, x ∉ Ioo α' β' → s x = 0 := by
    intro x hx; rw [hsdef]; simp only; rw [hgid x hx, sub_self]
  have hsS : ∀ x, |s x| < S := by intro x; rw [hsdef]; exact hgS x
  have hsd : ∀ x, deriv s x = deriv g x - 1 := by
    intro x
    rw [hsdef]
    exact ((hg.differentiable (by simp) x).hasDerivAt.sub (hasDerivAt_id' x)).deriv
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ i₀ = ⟨n - 1, by omega⟩ :=
    ⟨Equiv.swap i₀ _, Equiv.swap_apply_left _ _⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Fin n → ℝ,
      w = fun j => if ((σ j : Fin n) : ℕ) < l then -1 else 1 := ⟨_, rfl⟩
  have hwabs : ∀ j, |w j| = 1 := by
    intro j; rw [hwdef]; simp only; split_ifs <;> simp
  have hJ : {j | j ≠ i₀ ∧ w j < 0}.ncard = l := by
    have hset : {j | j ≠ i₀ ∧ w j < 0} =
        σ.symm '' ((({k | (k : ℕ) < l} : Finset (Fin n))) : Set (Fin n)) := by
      rw [Equiv.image_symm_eq_preimage]
      ext j
      simp only [mem_ofPred_eq, mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and, hwdef]
      by_cases h : ((σ j : Fin n) : ℕ) < l
      · rw [ite_eq_left h]
        refine ⟨fun _ => h, fun _ => ⟨?_, by norm_num⟩⟩
        rintro rfl
        rw [hσ] at h
        simp only at h
        omega
      · rw [ite_eq_right h]
        exact ⟨fun h' => absurd h'.2 (by norm_num), fun h' => absurd h' h⟩
    rw [hset, Set.ncard_image_of_injective _ σ.symm.injective, Set.ncard_coe_finset,
      Fin.card_filter_val_lt, min_eq_right hl.le]
  have hsingle : ∀ (t : ℝ) (j : Fin n),
      (t • Pi.single i₀ (1 : ℝ)) j = if j = i₀ then t else 0 := by
    intro t j; by_cases h : j = i₀ <;> simp [h]
  have hoffe : ∀ t : ℝ, offAxisSq i₀ (t • Pi.single i₀ (1 : ℝ)) = 0 := by
    intro t; unfold offAxisSq
    exact Finset.sum_eq_zero (fun j _ => by by_cases h : j = i₀ <;> simp [h, hsingle])
  have hQe : ∀ t : ℝ, diagQuad i₀ w (t • Pi.single i₀ (1 : ℝ)) = 0 := by
    intro t; unfold diagQuad
    exact Finset.sum_eq_zero (fun j _ => by by_cases h : j = i₀ <;> simp [h, hsingle])
  have hoffc : ContDiff ℝ ∞ (offAxisSq i₀ : (Fin n → ℝ) → ℝ) := by
    change ContDiff ℝ ∞ (fun y : Fin n → ℝ => ∑ j, if j = i₀ then (0 : ℝ) else y j ^ 2)
    refine ContDiff.sum fun j _ => ?_
    by_cases h : j = i₀
    · simp only [h, ite_true]; exact contDiff_const
    · simp only [h, ite_false]; exact (contDiff_apply ℝ ℝ j).pow 2
  have hQc : ContDiff ℝ ∞ (diagQuad i₀ w : (Fin n → ℝ) → ℝ) := by
    change ContDiff ℝ ∞ (fun y : Fin n → ℝ => ∑ j, if j = i₀ then (0 : ℝ) else w j * y j ^ 2)
    refine ContDiff.sum fun j _ => ?_
    by_cases h : j = i₀
    · simp only [h, ite_true]; exact contDiff_const
    · simp only [h, ite_false]; exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).pow 2)
  have hoffnn : ∀ y, 0 ≤ offAxisSq i₀ y := by
    intro y; unfold offAxisSq
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have hsq : ∀ y (j : Fin n), j ≠ i₀ → y j ^ 2 ≤ offAxisSq i₀ y := by
    intro y j hj; unfold offAxisSq
    have := Finset.single_le_sum (f := fun k => if k = i₀ then (0 : ℝ) else y k ^ 2)
      (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ j)
    simpa [hj] using this
  have hQle : ∀ y, |diagQuad i₀ w y| ≤ offAxisSq i₀ y := by
    intro y; unfold diagQuad offAxisSq
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    split_ifs
    · simp
    · rw [abs_mul, hwabs, one_mul, abs_of_nonneg (by positivity)]
  obtain ⟨F, hFdef⟩ : ∃ F : (Fin n → ℝ) → ℝ, F = taperedModel i₀ w s a b γ := ⟨_, rfl⟩
  have hFy : ∀ y, F y = y i₀ + s (y i₀) * a (offAxisSq i₀ y) +
      γ (y i₀) * diagQuad i₀ w y * b (offAxisSq i₀ y) := by
    intro y; rw [hFdef]; rfl
  have hFc : ContDiff ℝ ∞ F := by
    have happ : ContDiff ℝ ∞ (fun y : Fin n → ℝ => y i₀) := contDiff_apply ℝ ℝ i₀
    rw [hFdef]
    exact (happ.add ((hsc.comp happ).mul (hac.comp hoffc))).add
      (((hγc.comp happ).mul hQc).mul (hbc.comp hoffc))
  have hFe : ∀ t : ℝ, F (t • Pi.single i₀ (1 : ℝ)) = g t := by
    intro t
    rw [hFy, hoffe, hQe, hsingle, ite_eq_left rfl, hsdef, ha1 0 (by positivity)]
    ring
  have hx₀α' : x₀ + ℓ < α' := by rw [hx₀def, hℓdef, hα'def]; linarith
  have hβ'x₁ : β' < x₁ - ℓ := by rw [hx₁def, hℓdef, hβ'def]; linarith
  have hloc : ∀ t ∈ Ioo α' β', F =ᶠ[𝓝 (t • Pi.single i₀ (1 : ℝ))]
      fun y => g (y i₀) + ∑ j, (if j = i₀ then 0 else w j * y j ^ 2) := by
    intro t ht
    have hopen : IsOpen {y : Fin n → ℝ | y i₀ ∈ Ioo (x₀ + ℓ) (x₁ - ℓ) ∧ offAxisSq i₀ y < T / 4} :=
      (isOpen_Ioo.preimage (continuous_apply i₀)).inter
        (isOpen_lt hoffc.continuous continuous_const)
    have hmem : t • Pi.single i₀ (1 : ℝ) ∈
        {y : Fin n → ℝ | y i₀ ∈ Ioo (x₀ + ℓ) (x₁ - ℓ) ∧ offAxisSq i₀ y < T / 4} := by
      refine ⟨?_, ?_⟩
      · rw [hsingle, ite_eq_left rfl]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · rw [hoffe]; positivity
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rw [hFy, hγ1 _ hy.1.1.le hy.1.2.le, ha1 _ hy.2.le, hb1 _ (by linarith [hy.2]), hsdef]
    unfold diagQuad
    ring
  have hw0 : ∀ j, j ≠ i₀ → w j ≠ 0 := by
    intro j _ h
    have := hwabs j
    rw [h, abs_zero] at this
    norm_num at this
  obtain ⟨-, hsep₁, hsig₁⟩ := hessian_diagModel (F := F) (g := g) i₀ w t₁ hg
    ((hgcrit t₁).2 (Or.inl rfl)) hg₁.ne hw0 (hloc t₁ ⟨ht₁, by linarith⟩)
  obtain ⟨-, hsep₂, hsig₂⟩ := hessian_diagModel (F := F) (g := g) i₀ w t₂ hg
    ((hgcrit t₂).2 (Or.inr rfl)) hg₂.ne' hw0 (hloc t₂ ⟨by linarith, ht₂⟩)
  have hs' : ∀ x, deriv s x = -1 ↔ x = t₁ ∨ x = t₂ := by
    intro x
    rw [hsd, ← hgcrit x]
    constructor <;> intro h <;> linarith
  have hsa : ∀ x t, |s x * deriv a t| < 1 := by
    intro x t
    rw [abs_mul]
    calc |s x| * |deriv a t| ≤ S * Ca := mul_le_mul (hsS x).le (hCa t) (abs_nonneg _) hS.le
      _ < 1 := by nlinarith
  have hba : ∃ U : Set ℝ, IsOpen U ∧ tsupport a ⊆ U ∧ EqOn b 1 U := by
    refine ⟨Iio T, isOpen_Iio, ?_, fun t ht => hb1 t (le_of_lt ht)⟩
    have hsub : tsupport a ⊆ Iic (T / 2) := by
      refine closure_minimal (fun t ht => ?_) isClosed_Iic
      by_contra h
      rw [mem_Iic, not_le] at h
      exact ht (ha0' t h.le)
    exact hsub.trans fun t ht => show t < T from lt_of_le_of_lt (mem_Iic.mp ht) (by linarith)
  have hγs : ∃ U : Set ℝ, IsOpen U ∧ tsupport s ⊆ U ∧ EqOn γ 1 U := by
    refine ⟨Ioo (x₀ + ℓ) (x₁ - ℓ), isOpen_Ioo, ?_, fun x hx => hγ1 x hx.1.le hx.2.le⟩
    have hsub : tsupport s ⊆ Icc α' β' := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      by_contra h
      exact hx (hs0 x fun h' => h (Ioo_subset_Icc_self h'))
    exact hsub.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hγb : ∀ x t, 0 ≤ t → |deriv γ x| * (1 * t * |b t|) < 1 := by
    intro x t ht
    have htb : 1 * t * |b t| ≤ 2 * T := by
      rw [abs_of_nonneg (hbnn t), one_mul]
      by_cases h : 2 * T ≤ t
      · rw [hb0 t h, mul_zero]; positivity
      · rw [not_le] at h
        nlinarith [hble t, hbnn t]
    calc |deriv γ x| * (1 * t * |b t|) ≤ Cγ * (2 * T) :=
          mul_le_mul (hCγ x) htb (by positivity) hCγ0
      _ < 1 := by nlinarith
  have hcrit := fderiv_taperedModel_eq_zero_iff i₀ one_pos (w := w) (fun j _ => hwabs j) hsc hac
    hbc hγc hs' (ha1 0 (by positivity)) hsa hba hγs hγb
  rw [← hFdef] at hcrit
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Fin n → ℝ),
      K = {y | y i₀ ∈ Icc x₀ x₁ ∧ offAxisSq i₀ y ≤ 2 * T} := ⟨_, rfl⟩
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (isClosed_Icc.preimage (continuous_apply i₀)).inter
      (isClosed_le hoffc.continuous continuous_const)
  have hKc : IsCompact K := by
    set Rb := |x₀| + |x₁| + 2 * T + 1 with hRb
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun _ => isCompact_Icc (a := -Rb) (b := Rb))) hKclosed ?_
    intro y hy
    rw [hKdef] at hy
    rw [mem_univ_pi]
    intro j
    rw [mem_Icc]
    by_cases hj : j = i₀
    · subst hj
      constructor <;> linarith [hy.1.1, hy.1.2, abs_nonneg x₀, abs_nonneg x₁, neg_abs_le x₀,
        le_abs_self x₁]
    · have h1 := hsq y j hj
      have h2 := hy.2
      have h3 := sq_nonneg (y j + 1 / 2)
      have h4 := sq_nonneg (y j - 1 / 2)
      constructor <;> linarith [abs_nonneg x₀, abs_nonneg x₁]
  have hmemK : ∀ t ∈ Ioo α' β', t • Pi.single i₀ (1 : ℝ) ∈ K := by
    intro t ht
    rw [hKdef]
    refine ⟨?_, ?_⟩
    · rw [hsingle, ite_eq_left rfl]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [hoffe]; positivity
  refine ⟨F, K, t₁, t₂, hFc, hKc, ?_, ?_, ?_, ht₁₂, hmemK t₁ ⟨ht₁, by linarith⟩,
    hmemK t₂ ⟨by linarith, ht₂⟩, ?_, hcrit, hsep₁, hsep₂, ?_, ?_⟩
  · intro y hy
    rw [hKdef] at hy
    exact ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  · intro y hy
    rw [hFy]
    by_cases hx : y i₀ ∈ Icc x₀ x₁
    · have h : 2 * T < offAxisSq i₀ y := by
        by_contra h
        rw [not_lt] at h
        exact hy (by rw [hKdef]; exact ⟨hx, h⟩)
      rw [ha0' _ (by linarith), hb0 _ h.le]
      ring
    · rw [mem_Icc, not_and_or, not_le, not_le] at hx
      have hs' : s (y i₀) = 0 := hs0 _ fun hm => by
        rcases hx with hx | hx
        · linarith [hm.1]
        · linarith [hm.2]
      have hg' : γ (y i₀) = 0 := by
        rcases hx with hx | hx
        · exact hγ0l _ hx.le
        · exact hγ0r _ hx.le
      rw [hs', hg']
      ring
  · intro y hy
    rw [hKdef] at hy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    have e1 : |s (y i₀) * a (offAxisSq i₀ y)| < S := by
      rw [abs_mul, abs_of_nonneg (hann _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hale _)).trans_lt (hsS _)
    have e2 : |γ (y i₀) * diagQuad i₀ w y * b (offAxisSq i₀ y)| ≤ 2 * T := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hγnn _), abs_of_nonneg (hbnn _)]
      calc γ (y i₀) * |diagQuad i₀ w y| * b (offAxisSq i₀ y) ≤ 1 * (2 * T) * 1 :=
            mul_le_mul (mul_le_mul (hγle _) ((hQle y).trans h3) (abs_nonneg _) zero_le_one)
              (hble _) (hbnn _) (by positivity)
        _ = 2 * T := by ring
    have e1' := abs_lt.mp e1
    have e2' := abs_le.mp e2
    rw [hFy]
    constructor <;> linarith
  · rw [hFe, hFe]; exact hgap
  · rw [hsig₁, hJ, ite_eq_left hg₁]
  · rw [hsig₂, hJ, ite_eq_right (not_lt.mpr hg₂.le), add_zero]

theorem exists_model_pair {l : ℕ} (hl : l < n) (i₀ : Fin n) {α β ρ : ℝ} (hρ : 0 < ρ)
    (hαβ : α < β) :
    ∃ (F : (Fin n → ℝ) → ℝ) (K : Set (Fin n → ℝ)) (t₁ t₂ : ℝ),
      ContDiff ℝ ∞ F ∧ IsCompact K ∧
      K ⊆ {y | (∀ j, j ≠ i₀ → |y j| < ρ) ∧ α < y i₀ ∧ y i₀ < β} ∧
      (∀ y, y ∉ K → F y = y i₀) ∧ (∀ y ∈ K, α < F y ∧ F y < β) ∧ t₁ < t₂ ∧
      t₁ • Pi.single i₀ (1 : ℝ) ∈ K ∧ t₂ • Pi.single i₀ (1 : ℝ) ∈ K ∧
      F (t₂ • Pi.single i₀ (1 : ℝ)) < F (t₁ • Pi.single i₀ (1 : ℝ)) ∧
      (∀ y, fderiv ℝ F y = 0 ↔
        y = t₁ • Pi.single i₀ (1 : ℝ) ∨ y = t₂ • Pi.single i₀ (1 : ℝ)) ∧
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₁ • Pi.single i₀ (1 : ℝ)))).SeparatingLeft ∧
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₂ • Pi.single i₀ (1 : ℝ)))).SeparatingLeft ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₁ • Pi.single i₀ (1 : ℝ))) = l + 1 ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F (t₂ • Pi.single i₀ (1 : ℝ))) = l := by
  obtain ⟨F₀, K₀, t₁, t₂, hF₀, hK₀, hK₀s, hF₀off, hF₀K, ht, ht₁, ht₂, hgap, hcr, hsep₁, hsep₂,
    hsig₁, hsig₂⟩ := exists_model_pair_fat hl i₀ hαβ
  obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn (f := fun y : Fin n → ℝ => y)
    continuousOn_id
  set μ : ℝ := (|C| + 1) / ρ with hμ
  have hμpos : 0 < μ := by positivity
  let d : Fin n → ℝ := fun j => if j = i₀ then 1 else μ
  have hdpos : ∀ j, 0 < d j := by
    intro j
    by_cases hj : j = i₀
    · simp [d, hj]
    · simp only [d, hj, ite_false]; exact hμpos
  let A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun j => d j • ContinuousLinearMap.proj j
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun j => (d j)⁻¹ • ContinuousLinearMap.proj j
  have hA : ∀ y j, A y j = d j * y j := fun y j => by simp [A]
  have hB : ∀ y j, B y j = (d j)⁻¹ * y j := fun y j => by simp [B]
  have hBA : ∀ y, B (A y) = y := by
    intro y; funext j; rw [hB, hA]; field_simp [(hdpos j).ne']
  have hAB : ∀ y, A (B y) = y := by
    intro y; funext j; rw [hA, hB]; field_simp [(hdpos j).ne']
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.equivOfInverse A B hBA hAB
  have hAe : ∀ t : ℝ, A (t • Pi.single i₀ (1 : ℝ)) = t • Pi.single i₀ (1 : ℝ) := by
    intro t; funext j; rw [hA]
    by_cases hj : j = i₀
    · subst hj; simp [d]
    · simp [hj]
  have hAi : ∀ y, A y i₀ = y i₀ := by intro y; rw [hA]; simp [d]
  have hHess : ∀ x : Fin n → ℝ, fderiv ℝ F₀ (A x) = 0 →
      ((QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt (F₀ ∘ A) x)).SeparatingLeft ↔
        (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt F₀ (A x))).SeparatingLeft) ∧
      sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt (F₀ ∘ A) x) = sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt F₀ (A x)) := by
    intro x hx
    have hF₀x : ContDiffAt ℝ 2 F₀ (A x) := (hF₀.of_le MorseExistence.two_le_infty).contDiffAt
    have hAx : ContDiffAt ℝ 2 (⇑A) x := A.contDiff.contDiffAt
    have hBx : ContDiffAt ℝ 2 (⇑B) (A x) := B.contDiff.contDiffAt
    refine ⟨MorseExistence.separatingLeft_chartHessianAt_comp_iff hF₀x hAx hBx
      (Eventually.of_forall fun y => hBA y) (Eventually.of_forall fun y => hAB y) hx, ?_⟩
    apply QuadraticMap.Equivalent.sigNeg_eq
    refine ⟨{ e.toLinearEquiv with map_app' := ?_ }⟩
    intro v
    change (fderiv ℝ (fderiv ℝ F₀) (A x)) (A v) (A v) =
      (fderiv ℝ (fderiv ℝ (F₀ ∘ A)) x) v v
    rw [MorseExistence.fderiv_fderiv_comp_of_fderiv_eq_zero hF₀x hAx hx, A.fderiv]
  refine ⟨F₀ ∘ A, A ⁻¹' K₀, t₁, t₂, hF₀.comp A.contDiff, ?_, ?_, ?_, ?_, ht, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.2 hK₀
  · intro y hy
    have h1 := hK₀s hy
    simp only [Set.mem_ofPred_eq, hAi] at h1
    refine ⟨fun j hj => ?_, h1.1, h1.2⟩
    have h2 : ‖A y j‖ ≤ C := (norm_le_pi_norm (A y) j).trans (hC _ hy)
    rw [hA, Real.norm_eq_abs] at h2
    have hdj : d j = μ := by simp [d, hj]
    rw [hdj, abs_mul, abs_of_pos hμpos] at h2
    have h3 : μ * |y j| < μ * ρ := by
      rw [hμ, div_mul_cancel₀ _ hρ.ne']
      linarith [le_abs_self C]
    exact lt_of_mul_lt_mul_left h3 hμpos.le
  · intro y hy
    simp only [Function.comp_apply]
    rw [hF₀off _ hy, hAi]
  · intro y hy
    exact hF₀K _ hy
  · change A _ ∈ K₀; rw [hAe]; exact ht₁
  · change A _ ∈ K₀; rw [hAe]; exact ht₂
  · simp only [Function.comp_apply, hAe]; exact hgap
  · intro y
    have hfd : fderiv ℝ (F₀ ∘ A) y = (fderiv ℝ F₀ (A y)).comp (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
      rw [fderiv_comp y ((hF₀.differentiable (by simp)) _) A.differentiableAt, A.fderiv]
    rw [hfd]
    have hiff : (fderiv ℝ F₀ (A y)).comp (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = 0 ↔
        fderiv ℝ F₀ (A y) = 0 := by
      constructor
      · intro H
        ext v
        have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (B v)) H
        simpa [hAB] using this
      · intro H; rw [H]; rfl
    rw [hiff, hcr]
    have hinj : ∀ t : ℝ, A y = t • Pi.single i₀ (1 : ℝ) ↔ y = t • Pi.single i₀ (1 : ℝ) := by
      intro t
      constructor
      · intro H
        have hBt := hBA (t • Pi.single i₀ (1 : ℝ))
        rw [hAe] at hBt
        rw [← hBA y, H, hBt]
      · intro H; rw [H, hAe]
    rw [hinj, hinj]
  · have hx := (hcr (A (t₁ • Pi.single i₀ (1 : ℝ)))).2 (Or.inl (hAe t₁))
    rw [(hHess _ hx).1, hAe]; exact hsep₁
  · have hx := (hcr (A (t₂ • Pi.single i₀ (1 : ℝ)))).2 (Or.inr (hAe t₂))
    rw [(hHess _ hx).1, hAe]; exact hsep₂
  · have hx := (hcr (A (t₁ • Pi.single i₀ (1 : ℝ)))).2 (Or.inl (hAe t₁))
    rw [(hHess _ hx).2, hAe]; exact hsig₁
  · have hx := (hcr (A (t₂ • Pi.single i₀ (1 : ℝ)))).2 (Or.inr (hAe t₂))
    rw [(hHess _ hx).2, hAe]; exact hsig₂

theorem morseIndex_of_chart {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (hψ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source)
    (hψs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target) {y₀ : Fin n → ℝ}
    (hy₀ : y₀ ∈ ψ.source) :
    (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g (ψ y₀) ↔ fderiv ℝ (g ∘ ψ) y₀ = 0) ∧
      (fderiv ℝ (g ∘ ψ) y₀ = 0 →
        (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g (ψ y₀) ↔
          (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt (g ∘ ψ) y₀)).SeparatingLeft) ∧
        morseIndex I g (ψ y₀) = sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt (g ∘ ψ) y₀)) := by
  classical
  have _hT2 : T2Space M := inferInstance
  set p : M := ψ y₀ with hpdef
  set e := extChartAt I p with hedef
  have hψt : p ∈ ψ.target := ψ.map_source hy₀
  have hψsp : ψ.symm p = y₀ := ψ.left_inv hy₀
  have hpe : p ∈ e.source := mem_extChartAt_source p
  have hp' : p ∈ (chartAt H p).source := mem_chart_source H p
  have hgψ : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (g ∘ ψ) y₀ :=
    (hg _).comp y₀ (hψ.contMDiffAt (ψ.open_source.mem_nhds hy₀))
  have hψmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I ψ y₀ :=
    (hψ.contMDiffAt (ψ.open_source.mem_nhds hy₀)).mdifferentiableAt (by simp)
  have hψsmd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) ψ.symm p :=
    (hψs.contMDiffAt (ψ.open_target.mem_nhds hψt)).mdifferentiableAt (by simp)
  have hcrit_iff : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p ↔ fderiv ℝ (g ∘ ψ) y₀ = 0 := by
    have hleft : ((ψ : (Fin n → ℝ) → M) ∘ (ψ.symm : M → Fin n → ℝ)) =ᶠ[𝓝 p] id := by
      filter_upwards [ψ.open_target.mem_nhds hψt] with x hx
      exact ψ.right_inv hx
    have hright : ((ψ.symm : M → Fin n → ℝ) ∘ (ψ : (Fin n → ℝ) → M)) =ᶠ[𝓝 (ψ.symm p)] id := by
      rw [hψsp]
      filter_upwards [ψ.open_source.mem_nhds hy₀] with y hy
      exact ψ.left_inv hy
    have hh : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (g ∘ ψ) (ψ.symm p) := by
      rw [hψsp]; exact hgψ
    have hτmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I ψ (ψ.symm p) := by
      rw [hψsp]; exact hψmd
    have key := MorseExistence.isCriticalPointAt_iff_fderiv_of_localInverse I hleft hright hψsmd
      hτmd hh
    rw [hψsp] at key
    have heq : g =ᶠ[𝓝 p] ((g ∘ ψ) ∘ ψ.symm) := by
      filter_upwards [ψ.open_target.mem_nhds hψt] with x hx
      simp [Function.comp_apply, ψ.right_inv hx]
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
    rw [heq.mfderiv_eq]
    exact key
  refine ⟨hcrit_iff, fun hcrit => ?_⟩
  set h : (Fin n → ℝ) → ℝ := MorseExistence.chartRep I g p with hhdef
  set σ : (Fin n → ℝ) → (Fin n → ℝ) := e ∘ ψ with hσdef
  set τ : (Fin n → ℝ) → (Fin n → ℝ) := ψ.symm ∘ e.symm with hτdef
  have hσx : σ y₀ = e p := rfl
  have hep : e p ∈ e.target := e.map_source hpe
  have hUσ : ψ.source ∩ ψ ⁻¹' e.source ∈ 𝓝 y₀ :=
    (ψ.continuousOn.isOpen_inter_preimage ψ.open_source (isOpen_extChartAt_source p)).mem_nhds
      ⟨hy₀, hpe⟩
  have hUτ : e.target ∩ e.symm ⁻¹' ψ.target ∈ 𝓝 (e p) :=
    ((continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
      ψ.open_target).mem_nhds ⟨hep, by
        change e.symm (e p) ∈ ψ.target
        rw [e.left_inv hpe]; exact hψt⟩
  have hσsm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ σ y₀ :=
    (contMDiffAt_extChartAt' (n := ∞) hp').comp y₀
      (hψ.contMDiffAt (ψ.open_source.mem_nhds hy₀))
  have hτsm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ τ (e p) := by
    have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ e.symm (e p) :=
      (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hep)
    have h2 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm (e.symm (e p)) := by
      rw [e.left_inv hpe]
      exact hψs.contMDiffAt (ψ.open_target.mem_nhds hψt)
    exact h2.comp _ h1
  have hσ : ContDiffAt ℝ 2 σ y₀ :=
    (contMDiffAt_iff_contDiffAt.1 hσsm).of_le MorseExistence.two_le_infty
  have hτ : ContDiffAt ℝ 2 τ (σ y₀) :=
    (contMDiffAt_iff_contDiffAt.1 hτsm).of_le MorseExistence.two_le_infty
  have hh : ContDiffAt ℝ 2 h (σ y₀) :=
    (MorseExistence.contDiffAt_chartRep hg hep).of_le MorseExistence.two_le_infty
  have hτσ : τ ∘ σ =ᶠ[𝓝 y₀] id := by
    filter_upwards [hUσ] with y hy
    simp only [hτdef, hσdef, Function.comp_apply, id, e.left_inv hy.2, ψ.left_inv hy.1]
  have hστ : σ ∘ τ =ᶠ[𝓝 (σ y₀)] id := by
    filter_upwards [hUτ] with z hz
    simp only [hτdef, hσdef, Function.comp_apply, id, ψ.right_inv hz.2, e.right_inv hz.1]
  have hgeq : g ∘ ψ =ᶠ[𝓝 y₀] h ∘ σ := by
    filter_upwards [hUσ] with y hy
    change g (ψ y) = g (e.symm (e (ψ y)))
    rw [e.left_inv hy.2]
  have hcrit' : fderiv ℝ h (σ y₀) = 0 := by
    rw [← MorseExistence.fderiv_comp_eq_zero_iff hh hσ hτ hτσ hστ, ← hgeq.fderiv_eq]
    exact hcrit
  have hcritp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := hcrit_iff.2 hcrit
  have hHess : DifferentialGeometry.Topology.Morse.chartHessianAt (g ∘ ψ) y₀ = DifferentialGeometry.Topology.Morse.chartHessianAt (h ∘ σ) y₀ :=
    MorseExistence.chartHessianAt_congr hgeq
  have hHessp : hessianAt I g p = DifferentialGeometry.Topology.Morse.chartHessianAt h (σ y₀) := rfl
  refine ⟨?_, ?_⟩
  · change (Morse.IsCriticalPointAt I g p ∧
      (QuadraticMap.associated (R := ℝ) (hessianAt I g p)).SeparatingLeft) ↔ _
    rw [hHessp, hHess, MorseExistence.separatingLeft_chartHessianAt_comp_iff hh hσ hτ hτσ hστ
      hcrit']
    exact ⟨fun hx => hx.2, fun hx => ⟨hcritp, hx⟩⟩
  · unfold morseIndex
    rw [hHessp, hHess]
    set S := fderiv ℝ σ y₀ with hS
    set T := fderiv ℝ τ (σ y₀) with hT
    have hτσx : τ (σ y₀) = y₀ := hτσ.eq_of_nhds
    have hTS : ∀ u, T (S u) = u := by
      intro u
      have h1 : fderiv ℝ (τ ∘ σ) y₀ = T.comp S :=
        fderiv_comp y₀ (hτ.differentiableAt (by norm_num)) (hσ.differentiableAt (by norm_num))
      have h2 : fderiv ℝ (τ ∘ σ) y₀ = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
        rw [hτσ.fderiv_eq]; exact fderiv_id
      have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => A u) (h1.symm.trans h2)
      simpa using this
    have hST : ∀ w, S (T w) = w := by
      intro w
      have hσ' : DifferentiableAt ℝ σ (τ (σ y₀)) := by
        rw [hτσx]; exact hσ.differentiableAt (by norm_num)
      have h1 : fderiv ℝ (σ ∘ τ) (σ y₀) = (fderiv ℝ σ (τ (σ y₀))).comp T :=
        fderiv_comp (σ y₀) hσ' (hτ.differentiableAt (by norm_num))
      rw [hτσx] at h1
      have h2 : fderiv ℝ (σ ∘ τ) (σ y₀) = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
        rw [hστ.fderiv_eq]; exact fderiv_id
      have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => A w) (h1.symm.trans h2)
      simpa using this
    have hequiv : QuadraticMap.Equivalent (DifferentialGeometry.Topology.Morse.chartHessianAt (h ∘ σ) y₀)
        (DifferentialGeometry.Topology.Morse.chartHessianAt h (σ y₀)) := by
      let L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
        { toFun := fun u => S u
          map_add' := fun u v => map_add S u v
          map_smul' := fun c u => map_smul S c u
          invFun := fun w => T w
          left_inv := fun u => hTS u
          right_inv := fun w => hST w }
      refine ⟨⟨L, fun u => ?_⟩⟩
      change fderiv ℝ (fderiv ℝ h) (σ y₀) (S u) (S u) =
        fderiv ℝ (fderiv ℝ (h ∘ σ)) y₀ u u
      rw [MorseExistence.fderiv_fderiv_comp_of_fderiv_eq_zero hh hσ hcrit']
    exact hequiv.sigNeg_eq.symm

theorem exists_insert_pair (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {x₀ : M} {c L ρ : ℝ}
    (B : FlowBox D x₀ c L ρ) (hL : 0 < L) (hρ : 0 < ρ) (hab : a < c - ρ ∧ c + L + ρ < b)
    {l : ℕ} (hl : l < n) :
    ∃ (f₁ : M → ℝ) (q r : M) (K : Set (Fin n → ℝ)), IsCompact K ∧ K ⊆ innerBox B.i₀ ρ L ∧
      (∀ x, x ∉ B.ψ '' K → f₁ x = f x) ∧
      (∀ y ∈ K, c + L / 4 < f₁ (B.ψ y) ∧ f₁ (B.ψ y) < c + 3 * L / 4) ∧
      ModifiedWithin f c (c + L) f₁ ∧ MorseStrip I f₁ a b ∧ q ∈ B.ψ '' K ∧ r ∈ B.ψ '' K ∧
      f₁ q < f₁ r ∧ (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∨ x = q ∨ x = r) ∧
      morseIndex I f₁ q = l ∧ morseIndex I f₁ r = l + 1 ∧
      ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f₁ x = morseIndex I f x := by
  classical
  have _ := hcrit
  obtain ⟨F, K, t₁, t₂, hFs, hK, hKsub, hFoff, hFK, ht12, ht₁K, ht₂K, hFlt, hcritF, hnd₁, hnd₂,
    hidx₁, hidx₂⟩ := exists_model_pair (α := L / 4) (β := 3 * L / 4) hl B.i₀ (half_pos hρ)
      (by linarith)
  have hinbox : innerBox B.i₀ ρ L ⊆ boxSet B.i₀ ρ L := by
    rintro y ⟨h1, h2, h3⟩
    exact ⟨fun j hj => (h1 j hj).trans (by linarith), by linarith, by linarith⟩
  have hKin : K ⊆ innerBox B.i₀ ρ L := fun y hy => hKsub hy
  have hKbox : K ⊆ boxSet B.i₀ ρ L := hKin.trans hinbox
  have hboxOpen : IsOpen (boxSet B.i₀ ρ L) := by
    have h1 : IsOpen {y : Fin n → ℝ | ∀ j, j ≠ B.i₀ → |y j| < ρ} := by
      rw [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun j => ?_
      by_cases hj : j = B.i₀
      · simp [hj]
      · simp only [hj, ne_eq, not_false_eq_true, forall_const]
        exact isOpen_lt (continuous_apply j).abs continuous_const
    exact h1.inter ((isOpen_lt continuous_const (continuous_apply _)).inter
      (isOpen_lt (continuous_apply _) continuous_const))
  let f₁ : M → ℝ := fun x => if x ∈ B.ψ '' K then c + F (B.ψ.symm x) else f x
  have hf₁off : ∀ x, x ∉ B.ψ '' K → f₁ x = f x := fun x hx => by simp only [f₁, hx, ↓reduceIte]
  have hbox_img : ∀ y ∈ boxSet B.i₀ ρ L, f₁ (B.ψ y) = c + F y := by
    intro y hy
    by_cases hyK : B.ψ y ∈ B.ψ '' K
    · rw [show f₁ (B.ψ y) = c + F (B.ψ.symm (B.ψ y)) by simp only [f₁, hyK, ↓reduceIte],
        B.ψ.left_inv (B.box_subset hy)]
    · rw [hf₁off _ hyK, B.level y hy, hFoff y (fun h => hyK (mem_image_of_mem _ h))]
  have hKclosed : IsClosed (B.ψ '' K) :=
    (hK.image_of_continuousOn (B.ψ.continuousOn.mono (hKbox.trans B.box_subset))).isClosed
  have hUopen : IsOpen (B.ψ '' boxSet B.i₀ ρ L) :=
    B.ψ.isOpen_image_of_subset_source hboxOpen B.box_subset
  have hKU : B.ψ '' K ⊆ B.ψ '' boxSet B.i₀ ρ L := image_mono hKbox
  have hev_off : ∀ x, x ∉ B.ψ '' K → f₁ =ᶠ[𝓝 x] f := fun x hx => by
    filter_upwards [hKclosed.isOpen_compl.mem_nhds hx] with z hz using hf₁off z hz
  have hev_box : ∀ y ∈ boxSet B.i₀ ρ L, (f₁ ∘ B.ψ) =ᶠ[𝓝 y] fun z => F z + c := by
    intro y hy
    filter_upwards [hboxOpen.mem_nhds hy] with z hz
    rw [comp_apply, hbox_img z hz, add_comm]
  have hevf_box : ∀ y ∈ boxSet B.i₀ ρ L, (f ∘ B.ψ) =ᶠ[𝓝 y] fun z => z B.i₀ + c := by
    intro y hy
    filter_upwards [hboxOpen.mem_nhds hy] with z hz
    rw [comp_apply, B.level z hz, add_comm]
  have hf₁s : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁ := by
    intro x
    by_cases hx : x ∈ B.ψ '' boxSet B.i₀ ρ L
    · obtain ⟨y, hy, rfl⟩ := hx
      have hxt : B.ψ y ∈ B.ψ.target := B.ψ.map_source (B.box_subset hy)
      have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => c + F (B.ψ.symm x)) (B.ψ y) :=
        contMDiffAt_const.add ((hFs.contMDiff.contMDiffAt).comp _
          ((B.smooth_symm _ hxt).contMDiffAt (B.ψ.open_target.mem_nhds hxt)))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hUopen.mem_nhds (mem_image_of_mem _ hy)] with z hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hbox_img w hw, B.ψ.left_inv (B.box_subset hw)]
    · exact (hf.smooth x).congr_of_eventuallyEq (hev_off x (fun h => hx (hKU h)))
  have hMf₁ := fun y (hy : y ∈ boxSet B.i₀ ρ L) =>
    morseIndex_of_chart hf₁s B.ψ B.smooth B.smooth_symm (B.box_subset hy)
  have hMf := fun y (hy : y ∈ boxSet B.i₀ ρ L) =>
    morseIndex_of_chart hf.smooth B.ψ B.smooth B.smooth_symm (B.box_subset hy)
  have hfd₁ : ∀ y ∈ boxSet B.i₀ ρ L, fderiv ℝ (f₁ ∘ B.ψ) y = fderiv ℝ F y := by
    intro y hy
    rw [(hev_box y hy).fderiv_eq, fderiv_add_const]
  have hhess₁ : ∀ y ∈ boxSet B.i₀ ρ L, DifferentialGeometry.Topology.Morse.chartHessianAt (f₁ ∘ B.ψ) y = DifferentialGeometry.Topology.Morse.chartHessianAt F y := by
    intro y hy
    rw [MorseExistence.chartHessianAt_congr (hev_box y hy),
      MonotoneShift.chartHessianAt_add_const]
  have hnocrit : ∀ y ∈ boxSet B.i₀ ρ L, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f (B.ψ y) := by
    intro y hy h
    have h0 := (hMf y hy).1.1 h
    rw [(hevf_box y hy).fderiv_eq, fderiv_add_const, (hasFDerivAt_apply B.i₀ y).fderiv] at h0
    have := congrArg (fun φ : (Fin n → ℝ) →L[ℝ] ℝ => φ (Pi.single B.i₀ (1 : ℝ))) h0
    simp at this
  have hvalK : ∀ x ∈ B.ψ '' K, f₁ x ∈ Ioo a b ∧ f x ∈ Ioo a b := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := hFK y hy
    obtain ⟨_, h3, h4⟩ := hKsub hy
    rw [hbox_img y (hKbox hy), B.level y (hKbox hy)]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hab.1, hab.2]
  have hMS : MorseStrip I f₁ a b := by
    refine ⟨hf₁s, hf.lt, ?_, ?_, ?_⟩
    · have : f₁ ⁻¹' Icc a b = f ⁻¹' Icc a b := by
        ext x
        by_cases hx : x ∈ B.ψ '' K
        · exact ⟨fun _ => Ioo_subset_Icc_self (hvalK x hx).2,
            fun _ => Ioo_subset_Icc_self (hvalK x hx).1⟩
        · simp only [mem_preimage, hf₁off x hx]
      rw [this]
      exact hf.compact
    · intro x hx
      by_cases hxK : x ∈ B.ψ '' K
      · exfalso
        obtain ⟨h1, h2⟩ := (hvalK x hxK).1
        rcases hx with h | h <;> rw [h] at h1 h2 <;> linarith
      · rw [MonotoneShift.isCriticalPointAt_congr_nhds (hev_off x hxK)]
        apply hf.regular
        rwa [← hf₁off x hxK]
    · intro x hx hcr
      by_cases hxU : x ∈ B.ψ '' boxSet B.i₀ ρ L
      · obtain ⟨y, hy, rfl⟩ := hxU
        have h0 := (hMf₁ y hy).1.1 hcr
        refine (((hMf₁ y hy).2 h0).1).2 ?_
        rw [hhess₁ y hy]
        rw [hfd₁ y hy, hcritF] at h0
        rcases h0 with rfl | rfl
        exacts [hnd₁, hnd₂]
      · have hxK : x ∉ B.ψ '' K := fun h => hxU (hKU h)
        rw [MonotoneShift.isNondegenerateCriticalPointAt_congr_nhds (hev_off x hxK)]
        rw [MonotoneShift.isCriticalPointAt_congr_nhds (hev_off x hxK)] at hcr
        exact hf.nondegenerate x (by rwa [← hf₁off x hxK]) hcr
  refine ⟨f₁, B.ψ (t₂ • Pi.single B.i₀ (1 : ℝ)), B.ψ (t₁ • Pi.single B.i₀ (1 : ℝ)), K, hK, hKin,
    hf₁off, ?_, ?_, hMS, mem_image_of_mem _ ht₂K, mem_image_of_mem _ ht₁K, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hbox_img y (hKbox hy)]
    obtain ⟨h1, h2⟩ := hFK y hy
    constructor <;> linarith
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply hf₁off
      rintro ⟨y, hy, rfl⟩
      apply hx
      obtain ⟨_, h2, h3⟩ := hKsub hy
      change f (B.ψ y) ∈ Ioo c (c + L)
      rw [B.level y (hKbox hy)]
      constructor <;> linarith
    · by_cases hxK : x ∈ B.ψ '' K
      · obtain ⟨y, hy, rfl⟩ := hxK
        rw [hbox_img y (hKbox hy)]
        obtain ⟨h1, h2⟩ := hFK y hy
        constructor <;> linarith
      · rw [hf₁off x hxK]
        exact hx
  · rw [hbox_img _ (hKbox ht₂K), hbox_img _ (hKbox ht₁K)]
    linarith
  · intro x
    by_cases hxU : x ∈ B.ψ '' boxSet B.i₀ ρ L
    · obtain ⟨y, hy, rfl⟩ := hxU
      rw [(hMf₁ y hy).1, hfd₁ y hy, hcritF]
      have hinj : ∀ t : ℝ, t • (Pi.single B.i₀ (1 : ℝ) : Fin n → ℝ) ∈ K →
          (B.ψ y = B.ψ (t • (Pi.single B.i₀ (1 : ℝ) : Fin n → ℝ)) ↔
            y = t • (Pi.single B.i₀ (1 : ℝ) : Fin n → ℝ)) :=
        fun t ht => ⟨fun h => B.ψ.injOn (B.box_subset hy) (B.box_subset (hKbox ht)) h,
          fun h => congrArg B.ψ h⟩
      rw [hinj _ ht₂K, hinj _ ht₁K]
      simp only [hnocrit y hy, false_or]
      exact or_comm
    · have hxK : x ∉ B.ψ '' K := fun h => hxU (hKU h)
      rw [MonotoneShift.isCriticalPointAt_congr_nhds (hev_off x hxK)]
      have h2 : x ≠ B.ψ (t₂ • Pi.single B.i₀ (1 : ℝ)) :=
        fun h => hxK (h ▸ mem_image_of_mem _ ht₂K)
      have h1 : x ≠ B.ψ (t₁ • Pi.single B.i₀ (1 : ℝ)) :=
        fun h => hxK (h ▸ mem_image_of_mem _ ht₁K)
      simp only [h1, h2, or_false]
  · have hy := hKbox ht₂K
    have h0 : fderiv ℝ (f₁ ∘ B.ψ) (t₂ • Pi.single B.i₀ (1 : ℝ)) = 0 := by
      rw [hfd₁ _ hy, hcritF]
      exact Or.inr rfl
    rw [((hMf₁ _ hy).2 h0).2, hhess₁ _ hy, hidx₂]
  · have hy := hKbox ht₁K
    have h0 : fderiv ℝ (f₁ ∘ B.ψ) (t₁ • Pi.single B.i₀ (1 : ℝ)) = 0 := by
      rw [hfd₁ _ hy, hcritF]
      exact Or.inl rfl
    rw [((hMf₁ _ hy).2 h0).2, hhess₁ _ hy, hidx₁]
  · intro x hx
    have hxK : x ∉ B.ψ '' K := by
      rintro ⟨y, hy, rfl⟩
      exact hnocrit y (hKbox hy) hx
    exact MonotoneShift.morseIndex_congr_nhds (hev_off x hxK)

theorem exists_local_gradientLike [SigmaCompactSpace M] {f₁ : M → ℝ}
    (hf₁ : MorseStrip I f₁ a b) {Kc O : Set M} (hKc : IsCompact Kc) (hO : IsOpen O)
    (hKO : Kc ⊆ O) {q r : M} (hqr : q ≠ r) (hq : q ∈ interior Kc) (hr : r ∈ interior Kc)
    (hqab : f₁ q ∈ Ioo a b) (hrab : f₁ r ∈ Ioo a b)
    (hcritO : ∀ x ∈ O, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ x = q ∨ x = r) {ε : ℝ} (hε : 0 < ε) :
    ∃ (dq : MorseNormalChart I f₁ q) (dr : MorseNormalChart I f₁ r)
      (V : (x : M) → TangentSpace I x) (ε' : ℝ),
      ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧ tsupport V ⊆ O ∧
      (∀ x, -1 ≤ dfV I f₁ V x ∧ dfV I f₁ V x ≤ 0) ∧
      dq.χ '' Metric.ball 0 dq.R' ⊆ interior Kc ∧ dr.χ '' Metric.ball 0 dr.R' ⊆ interior Kc ∧
      Disjoint (dq.χ '' Metric.ball 0 dq.R') (dr.χ '' Metric.ball 0 dr.R') ∧
      (∀ y ∈ dq.χ '' Metric.ball 0 dq.R', |f₁ y - f₁ q| < ε) ∧
      (∀ y ∈ dr.χ '' Metric.ball 0 dr.R', |f₁ y - f₁ r| < ε) ∧
      (∀ x ∈ Kc, x ∉ dq.χ '' {y | morseNorm n y < dq.r₀} →
        x ∉ dr.χ '' {y | morseNorm n y < dr.r₀} → dfV I f₁ V x = -1) ∧
      (∀ x ∈ Kc, x ≠ q → x ≠ r → dfV I f₁ V x < 0) ∧
      (∀ y, morseNorm n y < dq.R →
        mfderiv I 𝓘(ℝ, Fin n → ℝ) dq.χ.symm (dq.χ y) (V (dq.χ y)) =
          ModelField.modelField dq.k dq.r₀ y) ∧
      (∀ y, morseNorm n y < dr.R →
        mfderiv I 𝓘(ℝ, Fin n → ℝ) dr.χ.symm (dr.χ y) (V (dr.χ y)) =
          ModelField.modelField dr.k dr.r₀ y) ∧
      0 < ε' ∧ ε' ≤ ε ∧ dq.r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < dq.R ^ 2 ∧ dr.r₀ ^ 2 < 2 * ε' ∧
      8 * ε' < dr.R ^ 2 := by
  classical
  have alg1 : ∀ s ρ ε : ℝ, 0 < s → 8 * s < ρ → ρ ≤ 1 → ρ ≤ ε → s ^ 2 / 2 < ε := by
    intro s ρ ε h1 h2 h3 h4
    nlinarith
  have alg2 : ∀ s m : ℝ, 0 < s → 8 * s < m → s ^ 2 / 2 < m ^ 2 / 40 := by
    intro s m h1 h2
    nlinarith
  have alg3 : ∀ e m R : ℝ, 0 < m → m ≤ R → e ≤ m ^ 2 / 40 → 8 * e < (R / 2) ^ 2 := by
    intro e m R h1 h2 h3
    nlinarith
  have hfc : Continuous f₁ := hf₁.smooth.continuous
  obtain ⟨Uq, Ur, hUq, hUr, hqU, hrU, hUdisj⟩ := t2_separation hqr
  have hqO : q ∈ O := hKO (interior_subset hq)
  have hrO : r ∈ O := hKO (interior_subset hr)
  have hqc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ q := (hcritO q hqO).2 (Or.inl rfl)
  have hrc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ r := (hcritO r hrO).2 (Or.inr rfl)
  set ρ : ℝ := min 1 ε with hρdef
  have hρ : 0 < ρ := lt_min one_pos hε
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : ρ ≤ ε := min_le_right _ _
  obtain ⟨cq0, hcq0R, hcq08, hcq0O⟩ := exists_morseNormalChart hf₁ hqab hqc
    ((isOpen_interior.inter hUq).inter
      (isOpen_Ioo.preimage hfc : IsOpen (f₁ ⁻¹' Ioo (f₁ q - ε) (f₁ q + ε))))
    ⟨⟨hq, hqU⟩, by constructor <;> linarith⟩ hρ
  obtain ⟨cr0, hcr0R, hcr08, hcr0O⟩ := exists_morseNormalChart hf₁ hrab hrc
    ((isOpen_interior.inter hUr).inter
      (isOpen_Ioo.preimage hfc : IsOpen (f₁ ⁻¹' Ioo (f₁ r - ε) (f₁ r + ε))))
    ⟨⟨hr, hrU⟩, by constructor <;> linarith⟩ hρ
  set s : ℝ := min cq0.r₀ cr0.r₀ with hsdef
  have hs : 0 < s := lt_min cq0.hr₀ cr0.hr₀
  have hsq : s ≤ cq0.r₀ := min_le_left _ _
  have hsr : s ≤ cr0.r₀ := min_le_right _ _
  let cq : MorseNormalChart I f₁ q :=
    { cq0 with r₀ := s, hr₀ := hs, hr₀R := by linarith [cq0.hr₀R] }
  let cr : MorseNormalChart I f₁ r :=
    { cr0 with r₀ := s, hr₀ := hs, hr₀R := by linarith [cr0.hr₀R] }
  have hcq8 : 8 * cq.r₀ < cq.R := by change 8 * s < cq0.R; linarith
  have hcr8 : 8 * cr.r₀ < cr.R := by change 8 * s < cr0.R; linarith
  have hcqimg : cq.χ '' Metric.ball 0 cq.R' ⊆ interior Kc ∩ Uq ∩
      f₁ ⁻¹' Ioo (f₁ q - ε) (f₁ q + ε) := hcq0O
  have hcrimg : cr.χ '' Metric.ball 0 cr.R' ⊆ interior Kc ∩ Ur ∩
      f₁ ⁻¹' Ioo (f₁ r - ε) (f₁ r + ε) := hcr0O
  have hdisjqr : Disjoint (cq.χ '' Metric.ball 0 cq.R') (cr.χ '' Metric.ball 0 cr.R') :=
    hUdisj.mono (fun x hx => (hcqimg hx).1.2) (fun x hx => (hcrimg hx).1.2)
  set Bq : Set M := cq.χ '' {y | morseNorm n y < cq.r₀} with hBqdef
  set Br : Set M := cr.χ '' {y | morseNorm n y < cr.r₀} with hBrdef
  have hBqo : IsOpen Bq := cq.isOpen_image_of_lt (by linarith [cq.hr₀R, cq.hRR', cq.hr₀])
  have hBro : IsOpen Br := cr.isOpen_image_of_lt (by linarith [cr.hr₀R, cr.hRR', cr.hr₀])
  set Kreg : Set M := Kc \ (Bq ∪ Br) with hKregdef
  have hKregc : IsCompact Kreg := hKc.diff (hBqo.union hBro)
  have hKreg : ∀ x ∈ Kreg, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x := by
    rintro x ⟨hxK, hxB⟩ hxc
    rcases (hcritO x (hKO hxK)).1 hxc with rfl | rfl
    · exact hxB (Or.inl (cq.p_mem_image_lt cq.hr₀))
    · exact hxB (Or.inr (cr.p_mem_image_lt cr.hr₀))
  obtain ⟨Vr, hVr, hVrc, hVrK, hVrb⟩ :=
    DifferentialGeometry.Topology.Morse.exists_unitSpeedVectorField_on_compact I f₁ hf₁.smooth
      Kreg hKregc hKreg
  set bq : M → ℝ := cq.pushFun cq.bumpY with hbqdef
  set br : M → ℝ := cr.pushFun cr.bumpY with hbrdef
  set mq : (x : M) → TangentSpace I x := cq.push cq.modelY with hmqdef
  set mr : (x : M) → TangentSpace I x := cr.push cr.modelY with hmrdef
  set V0 : (x : M) → TangentSpace I x :=
    fun x => bq x • mq x + br x • mr x + (1 - bq x - br x) • Vr x with hV0def
  have hbqs : ContMDiff I 𝓘(ℝ, ℝ) ∞ bq := cq.contMDiff_pushFun_bumpY
  have hbrs : ContMDiff I 𝓘(ℝ, ℝ) ∞ br := cr.contMDiff_pushFun_bumpY
  have hV0s : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, V0 x⟩ : TangentBundle I M)) :=
    ((hbqs.smul_section cq.contMDiff_push_modelY).add_section
      (hbrs.smul_section cr.contMDiff_push_modelY)).add_section
      (((contMDiff_const.sub hbqs).sub hbrs).smul_section hVr)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K', hK'c, hKcK', hK'O⟩ := exists_compact_between hKc hO hKO
  obtain ⟨κ, hκ0, hκ1, hκ01⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    isOpen_interior.isClosed_compl hKc.isClosed
    (disjoint_compl_left_iff_subset.2 hKcK')
  set V : (x : M) → TangentSpace I x := fun x => κ x • V0 x with hVdef
  have hVs : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) :=
    κ.contMDiff.smul_section hV0s
  have hκts : tsupport κ ⊆ K' := by
    refine closure_minimal (fun x hx => ?_) hK'c.isClosed
    by_contra h
    exact hx (hκ0 (fun h' => h (interior_subset h')))
  have hVts : tsupport V ⊆ K' :=
    (tsupport_smul_subset_left (fun x => κ x) (fun x => (V0 x : Fin n → ℝ))).trans hκts
  have hdfV0 : ∀ x, dfV I f₁ V0 x = bq x * dfV I f₁ mq x + br x * dfV I f₁ mr x +
      (1 - bq x - br x) * dfV I f₁ Vr x := by
    intro x
    rw [← dfL_apply]
    simp only [hV0def, map_add, map_smul, smul_eq_mul, dfL_apply]
  have hdfV : ∀ x, dfV I f₁ V x = κ x * dfV I f₁ V0 x := by
    intro x
    rw [← dfL_apply]
    simp only [hVdef, map_smul, smul_eq_mul, dfL_apply]
  have hbq01 : ∀ x, 0 ≤ bq x ∧ bq x ≤ 1 := fun x =>
    ⟨cq.pushFun_bumpY_nonneg x, cq.pushFun_bumpY_le_one x⟩
  have hbr01 : ∀ x, 0 ≤ br x ∧ br x ≤ 1 := fun x =>
    ⟨cr.pushFun_bumpY_nonneg x, cr.pushFun_bumpY_le_one x⟩
  have hbqr : ∀ x, bq x = 0 ∨ br x = 0 := by
    intro x
    by_cases h1 : bq x = 0
    · exact Or.inl h1
    · refine Or.inr (by_contra fun h2 => ?_)
      exact hdisjqr.notMem_of_mem_left (cq.mem_image_ball_of_pushFun_bumpY_ne_zero h1)
        (cr.mem_image_ball_of_pushFun_bumpY_ne_zero h2)
  have hmqb : ∀ x, -1 ≤ dfV I f₁ mq x ∧ dfV I f₁ mq x ≤ 0 :=
    fun x => cq.dfV_push_modelY_bounds hf₁.smooth x
  have hmrb : ∀ x, -1 ≤ dfV I f₁ mr x ∧ dfV I f₁ mr x ≤ 0 :=
    fun x => cr.dfV_push_modelY_bounds hf₁.smooth x
  have hVrb' : ∀ x, -1 ≤ dfV I f₁ Vr x ∧ dfV I f₁ Vr x ≤ 0 := fun x => hVrb x
  have hVrK' : ∀ x ∈ Kreg, dfV I f₁ Vr x = -1 := fun x hx => hVrK x hx
  have hsum1 : ∀ x, bq x + br x ≤ 1 := by
    intro x
    rcases hbqr x with h | h <;> rw [h] <;> linarith [hbq01 x, hbr01 x]
  have hV0rate : ∀ x, -1 ≤ dfV I f₁ V0 x ∧ dfV I f₁ V0 x ≤ 0 := by
    intro x
    rw [hdfV0]
    obtain ⟨h1, h2⟩ := hbq01 x
    obtain ⟨h3, h4⟩ := hbr01 x
    obtain ⟨h5, h6⟩ := hmqb x
    obtain ⟨h7, h8⟩ := hmrb x
    obtain ⟨h9, h10⟩ := hVrb' x
    have h11 := hsum1 x
    have e1 : 0 ≤ bq x * (dfV I f₁ mq x + 1) := mul_nonneg h1 (by linarith)
    have e2 : 0 ≤ br x * (dfV I f₁ mr x + 1) := mul_nonneg h3 (by linarith)
    have e3 : 0 ≤ (1 - bq x - br x) * (dfV I f₁ Vr x + 1) := mul_nonneg (by linarith) (by linarith)
    have e4 : bq x * dfV I f₁ mq x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h6
    have e5 : br x * dfV I f₁ mr x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 h8
    have e6 : (1 - bq x - br x) * dfV I f₁ Vr x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h10
    constructor <;> nlinarith
  have hVrate : ∀ x, -1 ≤ dfV I f₁ V x ∧ dfV I f₁ V x ≤ 0 := by
    intro x
    rw [hdfV]
    obtain ⟨h1, h2⟩ := hκ01 x
    obtain ⟨h3, h4⟩ := hV0rate x
    constructor <;> nlinarith
  have hκKc : ∀ x ∈ Kc, κ x = 1 := fun x hx => hκ1 hx
  have hbq1 : ∀ x ∈ Bq, bq x = 1 := by
    rintro x ⟨y, hy, rfl⟩
    exact cq.pushFun_bumpY_chart_eq_one (by
      have : morseNorm n y < cq.r₀ := hy
      linarith [hcq8, cq.hr₀])
  have hbr1 : ∀ x ∈ Br, br x = 1 := by
    rintro x ⟨y, hy, rfl⟩
    exact cr.pushFun_bumpY_chart_eq_one (by
      have : morseNorm n y < cr.r₀ := hy
      linarith [hcr8, cr.hr₀])
  have hmq1 : ∀ x, x ∉ Bq → bq x * dfV I f₁ mq x = -bq x := by
    intro x hx
    by_cases h : bq x = 0
    · rw [h]; ring
    · obtain ⟨y, hy, rfl⟩ := cq.mem_of_pushFun_bumpY_ne_zero h
      rw [cq.dfV_push_modelY_eq_neg_one hf₁.smooth hy (not_lt.1 fun h' => hx ⟨y, h', rfl⟩)]
      ring
  have hmr1 : ∀ x, x ∉ Br → br x * dfV I f₁ mr x = -br x := by
    intro x hx
    by_cases h : br x = 0
    · rw [h]; ring
    · obtain ⟨y, hy, rfl⟩ := cr.mem_of_pushFun_bumpY_ne_zero h
      rw [cr.dfV_push_modelY_eq_neg_one hf₁.smooth hy (not_lt.1 fun h' => hx ⟨y, h', rfl⟩)]
      ring
  have hunit : ∀ x ∈ Kc, x ∉ Bq → x ∉ Br → dfV I f₁ V x = -1 := by
    intro x hxK hxq hxr
    have hxreg : x ∈ Kreg := ⟨hxK, fun h => h.elim hxq hxr⟩
    rw [hdfV, hκKc x hxK, one_mul, hdfV0, hmq1 x hxq, hmr1 x hxr, hVrK' x hxreg]
    ring
  have hneg : ∀ x ∈ Kc, x ≠ q → x ≠ r → dfV I f₁ V x < 0 := by
    intro x hxK hxq hxr
    rw [hdfV, hκKc x hxK, one_mul, hdfV0]
    obtain ⟨h1, h2⟩ := hbq01 x
    obtain ⟨h3, h4⟩ := hbr01 x
    obtain ⟨h5, h6⟩ := hmqb x
    obtain ⟨h7, h8⟩ := hmrb x
    have e4 : bq x * dfV I f₁ mq x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h6
    have e5 : br x * dfV I f₁ mr x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 h8
    rcases (hsum1 x).lt_or_eq with hlt | heq
    · have hxq' : x ∉ Bq := fun h => by
        have := hbq1 x h
        linarith
      have hxr' : x ∉ Br := fun h => by
        have := hbr1 x h
        linarith
      rw [hVrK' x ⟨hxK, fun h => h.elim hxq' hxr'⟩]
      nlinarith
    · rcases hbqr x with h0 | h0
      · have hb1 : br x = 1 := by linarith
        obtain ⟨y, hy, rfl⟩ := cr.mem_of_pushFun_bumpY_ne_zero
          (show br x ≠ 0 by rw [hb1]; exact one_ne_zero)
        have hy0 : y ≠ 0 := fun h => hxr (by rw [h]; exact cr.hχ0)
        have := cr.dfV_push_modelY_neg hf₁.smooth hy hy0
        rw [h0, hb1]
        nlinarith
      · have hb1 : bq x = 1 := by linarith
        obtain ⟨y, hy, rfl⟩ := cq.mem_of_pushFun_bumpY_ne_zero
          (show bq x ≠ 0 by rw [hb1]; exact one_ne_zero)
        have hy0 : y ≠ 0 := fun h => hxq (by rw [h]; exact cq.hχ0)
        have := cq.dfV_push_modelY_neg hf₁.smooth hy hy0
        rw [h0, hb1]
        nlinarith
  have hmodq : ∀ y, morseNorm n y < cq.R / 2 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) cq.χ.symm (cq.χ y) (V (cq.χ y)) =
        ModelField.modelField cq.k cq.r₀ y := by
    intro y hy
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) cq.R' := cq.mem_ball_of_le (by linarith [cq.R_pos])
    have hxK : cq.χ y ∈ Kc := interior_subset (hcqimg (mem_image_of_mem _ hyb)).1.1
    have hb1 : bq (cq.χ y) = 1 := cq.pushFun_bumpY_chart_eq_one hy.le
    have hb0 : br (cq.χ y) = 0 := (hbqr _).resolve_left (by rw [hb1]; exact one_ne_zero)
    have hVe : V (cq.χ y) = mq (cq.χ y) := by
      simp only [hVdef, hV0def, hκKc _ hxK, hb1, hb0, one_smul, zero_smul, add_zero, sub_self]
    rw [hVe]
    exact cq.pullback_push_modelY (by linarith [cq.R_pos])
  have hmodr : ∀ y, morseNorm n y < cr.R / 2 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) cr.χ.symm (cr.χ y) (V (cr.χ y)) =
        ModelField.modelField cr.k cr.r₀ y := by
    intro y hy
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) cr.R' := cr.mem_ball_of_le (by linarith [cr.R_pos])
    have hxK : cr.χ y ∈ Kc := interior_subset (hcrimg (mem_image_of_mem _ hyb)).1.1
    have hb1 : br (cr.χ y) = 1 := cr.pushFun_bumpY_chart_eq_one hy.le
    have hb0 : bq (cr.χ y) = 0 := (hbqr _).resolve_right (by rw [hb1]; exact one_ne_zero)
    have hVe : V (cr.χ y) = mr (cr.χ y) := by
      simp only [hVdef, hV0def, hκKc _ hxK, hb1, hb0, one_smul, zero_smul, zero_add, sub_zero,
        sub_self, add_zero]
    rw [hVe]
    exact cr.pullback_push_modelY (by linarith [cr.R_pos])
  set m : ℝ := min cq0.R cr0.R with hmdef
  have hm : 0 < m := lt_min cq0.R_pos cr0.R_pos
  have hmq : m ≤ cq0.R := min_le_left _ _
  have hmr : m ≤ cr0.R := min_le_right _ _
  have hsm : 8 * s < m := lt_min (by linarith) (by linarith)
  have hsρ : 8 * s < ρ := by linarith
  set ε' : ℝ := min ε (m ^ 2 / 40) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'm : ε' ≤ m ^ 2 / 40 := min_le_right _ _
  have hs2 : s ^ 2 / 2 < ε' := lt_min (alg1 s ρ ε hs hsρ hρ1 hρε) (alg2 s m hs hsm)
  refine ⟨cq.halve hcq8, cr.halve hcr8, V, ε', hVs,
    hK'c.of_isClosed_subset (isClosed_tsupport _) hVts, hVts.trans hK'O, hVrate,
    fun x hx => (hcqimg hx).1.1, fun x hx => (hcrimg hx).1.1, hdisjqr, ?_, ?_,
    fun x hx h1 h2 => hunit x hx h1 h2, hneg, fun y hy => hmodq y hy, fun y hy => hmodr y hy,
    hε'pos, hε'ε, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have := (hcqimg hy).2
    simp only [mem_preimage, mem_Ioo] at this
    rw [abs_sub_lt_iff]
    constructor <;> linarith [this.1, this.2]
  · intro y hy
    have := (hcrimg hy).2
    simp only [mem_preimage, mem_Ioo] at this
    rw [abs_sub_lt_iff]
    constructor <;> linarith [this.1, this.2]
  · change s ^ 2 < 2 * ε'
    linarith
  · change 8 * ε' < (cq0.R / 2) ^ 2
    exact alg3 ε' m cq0.R hm hmq hε'm
  · change s ^ 2 < 2 * ε'
    linarith
  · change 8 * ε' < (cr0.R / 2) ^ 2
    exact alg3 ε' m cr0.R hm hmr hε'm

theorem exists_gradientLike_insert [SigmaCompactSpace M] [DecidableEq M]
    (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {x₀ : M} {c L ρ : ℝ}
    (B : FlowBox D x₀ c L ρ) (hL : 0 < L) (hρ : 0 < ρ) (hab : a < c - ρ ∧ c + L + ρ < b)
    {f₁ : M → ℝ} (hf₁ : MorseStrip I f₁ a b) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKin : K ⊆ innerBox B.i₀ ρ L) (hf₁K : ∀ x, x ∉ B.ψ '' K → f₁ x = f x)
    {q r : M} (hqK : q ∈ B.ψ '' K) (hrK : r ∈ B.ψ '' K) (hqr : q ≠ r)
    (hf₁Kv : ∀ y ∈ K, c + L / 4 < f₁ (B.ψ y) ∧ f₁ (B.ψ y) < c + 3 * L / 4)
    (hcrit₁ : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∨ x = q ∨ x = r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : GradientLikeStrip I f₁ a b (insert q (insert r crit)),
      (∀ x (hx : x ∈ crit),
        (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).χ =
            (D.chart x hx).χ ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).k =
            (D.chart x hx).k ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R =
            (D.chart x hx).R ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R' =
            (D.chart x hx).R' ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).r₀ =
            (D.chart x hx).r₀ ∧
          D₁.rm x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) = D.rm x hx) ∧
      (∀ x, x ∉ B.ψ '' midBox B.i₀ ρ L → D₁.V x = D.V x) ∧
      (∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
        (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R' ⊆ B.ψ '' midBox B.i₀ ρ L ∧
        ∀ y ∈ (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R', |f₁ y - f₁ x| < ε) ∧
      ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
        (D₁.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D₁.rm x hx ^ 2 := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hf₁s : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁ := hf₁.smooth
  set Q : Set (Fin n → ℝ) := {y | (∀ j, j ≠ B.i₀ → |y j| ≤ 5 * ρ / 8) ∧
    3 * L / 16 ≤ y B.i₀ ∧ y B.i₀ ≤ 13 * L / 16} with hQdef
  set Qo : Set (Fin n → ℝ) := {y | (∀ j, j ≠ B.i₀ → |y j| < 5 * ρ / 8) ∧
    3 * L / 16 < y B.i₀ ∧ y B.i₀ < 13 * L / 16} with hQodef
  have hQoQ : Qo ⊆ Q := fun y hy => ⟨fun j hj => (hy.1 j hj).le, hy.2.1.le, hy.2.2.le⟩
  have hQmid : Q ⊆ midBox B.i₀ ρ L := fun y hy =>
    ⟨fun j hj => by linarith [hy.1 j hj], by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hmidbox : midBox B.i₀ ρ L ⊆ boxSet B.i₀ ρ L := fun y hy =>
    ⟨fun j hj => by linarith [hy.1 j hj], by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hinQo : innerBox B.i₀ ρ L ⊆ Qo := fun y hy =>
    ⟨fun j hj => by linarith [hy.1 j hj], by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hKbox : K ⊆ boxSet B.i₀ ρ L :=
    hKin.trans (hinQo.trans (hQoQ.trans (hQmid.trans hmidbox)))
  have hQbox : Q ⊆ boxSet B.i₀ ρ L := hQmid.trans hmidbox
  have hQc : IsCompact Q := by
    have hEq : Q = (⋂ j, {y : Fin n → ℝ | j ≠ B.i₀ → |y j| ≤ 5 * ρ / 8}) ∩
        ({y | 3 * L / 16 ≤ y B.i₀} ∩ {y | y B.i₀ ≤ 13 * L / 16}) := by
      ext y
      simp [hQdef]
    have hcl : IsClosed Q := by
      rw [hEq]
      refine (isClosed_iInter fun j => ?_).inter
        ((isClosed_le continuous_const (continuous_apply B.i₀)).inter
          (isClosed_le (continuous_apply B.i₀) continuous_const))
      by_cases hj : j = B.i₀
      · simp [hj]
      · simpa [hj] using isClosed_le ((continuous_apply j).abs) continuous_const
    set C : ℝ := 5 * ρ / 8 + 13 * L / 16 with hCdef
    refine (isCompact_Icc (a := fun _ : Fin n => -C) (b := fun _ => C)).of_isClosed_subset hcl ?_
    intro y hy
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = B.i₀
      · subst hj
        change -C ≤ y B.i₀
        linarith [hy.2.1]
      · have := abs_le.1 (hy.1 j hj)
        change -C ≤ y j
        linarith [this.1]
    · by_cases hj : j = B.i₀
      · subst hj
        change y B.i₀ ≤ C
        linarith [hy.2.2]
      · have := abs_le.1 (hy.1 j hj)
        change y j ≤ C
        linarith [this.2]
  have hQoo : IsOpen Qo := by
    have hEq : Qo = (⋂ j, {y : Fin n → ℝ | j ≠ B.i₀ → |y j| < 5 * ρ / 8}) ∩
        ({y | 3 * L / 16 < y B.i₀} ∩ {y | y B.i₀ < 13 * L / 16}) := by
      ext y
      simp [hQodef]
    rw [hEq]
    refine (isOpen_iInter_of_finite fun j => ?_).inter
      ((isOpen_lt continuous_const (continuous_apply B.i₀)).inter
        (isOpen_lt (continuous_apply B.i₀) continuous_const))
    by_cases hj : j = B.i₀
    · simp [hj]
    · simpa [hj] using isOpen_lt ((continuous_apply j).abs) continuous_const
  have hmido : IsOpen (midBox B.i₀ ρ L) := by
    have hEq : midBox B.i₀ ρ L = (⋂ j, {y : Fin n → ℝ | j ≠ B.i₀ → |y j| < 3 * ρ / 4}) ∩
        ({y | L / 8 < y B.i₀} ∩ {y | y B.i₀ < 7 * L / 8}) := by
      ext y
      simp [midBox]
    rw [hEq]
    refine (isOpen_iInter_of_finite fun j => ?_).inter
      ((isOpen_lt continuous_const (continuous_apply B.i₀)).inter
        (isOpen_lt (continuous_apply B.i₀) continuous_const))
    by_cases hj : j = B.i₀
    · simp [hj]
    · simpa [hj] using isOpen_lt ((continuous_apply j).abs) continuous_const
  set Kc : Set M := B.ψ '' Q with hKcdef
  set O : Set M := B.ψ '' midBox B.i₀ ρ L with hOdef
  have hKcc : IsCompact Kc :=
    hQc.image_of_continuousOn (B.ψ.continuousOn.mono (hQbox.trans B.box_subset))
  have hOo : IsOpen O :=
    (B.ψ.isOpen_image_iff_of_subset_source (hmidbox.trans B.box_subset)).2 hmido
  have hKcO : Kc ⊆ O := image_mono hQmid
  have hQoint : B.ψ '' Qo ⊆ interior Kc :=
    interior_maximal (image_mono hQoQ)
      ((B.ψ.isOpen_image_iff_of_subset_source
        (hQoQ.trans (hQbox.trans B.box_subset))).2 hQoo)
  have hψKint : B.ψ '' K ⊆ interior Kc := (image_mono (hKin.trans hinQo)).trans hQoint
  have hintbox : interior Kc ⊆ B.ψ '' boxSet B.i₀ ρ L :=
    interior_subset.trans (image_mono hQbox)
  have hintmid : interior Kc ⊆ O := interior_subset.trans hKcO
  have hψKc : IsCompact (B.ψ '' K) :=
    hK.image_of_continuousOn (B.ψ.continuousOn.mono (hKbox.trans B.box_subset))
  have hf₁box : ∀ y ∈ boxSet B.i₀ ρ L, f₁ (B.ψ y) ∈ Ioo a b := by
    intro y hy
    by_cases hyK : B.ψ y ∈ B.ψ '' K
    · obtain ⟨y', hy', hyy⟩ := hyK
      rw [← hyy]
      obtain ⟨h1, h2⟩ := hf₁Kv y' hy'
      constructor <;> linarith [hab.1, hab.2]
    · rw [hf₁K _ hyK, B.level y hy]
      constructor <;> linarith [hy.2.1, hy.2.2, hab.1, hab.2]
  have hqab : f₁ q ∈ Ioo a b := by
    obtain ⟨y, hy, rfl⟩ := hqK
    exact hf₁box y (hKbox hy)
  have hrab : f₁ r ∈ Ioo a b := by
    obtain ⟨y, hy, rfl⟩ := hrK
    exact hf₁box y (hKbox hy)
  have hold_out : ∀ p (hp : p ∈ crit), ∀ x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R',
      x ∉ B.ψ '' boxSet B.i₀ ρ L := by
    rintro p hp x hx ⟨y, hy, rfl⟩
    exact B.avoid y hy p hp hx
  have hcrit_out : ∀ p ∈ crit, p ∉ B.ψ '' boxSet B.i₀ ρ L := fun p hp =>
    hold_out p hp p (D.chart p hp).p_mem_image_ball
  have hnocrit : ∀ x ∈ B.ψ '' boxSet B.i₀ ρ L, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    rintro x ⟨y, hy, rfl⟩ hc
    have hmem : B.ψ y ∈ crit := (hcrit _).2 ⟨by
      rw [B.level y hy]
      constructor <;> linarith [hy.2.1, hy.2.2, hab.1, hab.2], hc⟩
    exact hcrit_out _ hmem ⟨y, hy, rfl⟩
  have hcritO : ∀ x ∈ O, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ x = q ∨ x = r := by
    intro x hx
    rw [hcrit₁ x]
    have := hnocrit x (image_mono hmidbox hx)
    tauto
  have hqc : q ∉ crit := fun h => hcrit_out q h (image_mono hKbox hqK)
  have hrc : r ∉ crit := fun h => hcrit_out r h (image_mono hKbox hrK)
  obtain ⟨dq, dr, V, ε', hVs, hVc, hVO, hVrate, hdqK, hdrK, hdqr, hdqε, hdrε, hVunit, hVneg,
      hdqmod, hdrmod, hε'0, hε'ε, hdq1, hdq2, hdr1, hdr2⟩ :=
    exists_local_gradientLike hf₁ hKcc hOo hKcO hqr (hψKint hqK) (hψKint hrK) hqab hrab hcritO hε
  set Sq : Set M := dq.χ '' {y | morseNorm n y ≤ dq.R} with hSqdef
  set Sr : Set M := dr.χ '' {y | morseNorm n y ≤ dr.R} with hSrdef
  have hSqc : IsCompact Sq := dq.isCompact_image_le dq.hRR'
  have hSrc : IsCompact Sr := dr.isCompact_image_le dr.hRR'
  have hSqb : Sq ⊆ dq.χ '' Metric.ball 0 dq.R' := image_mono fun y hy => dq.mem_ball_of_le hy
  have hSrb : Sr ⊆ dr.χ '' Metric.ball 0 dr.R' := image_mono fun y hy => dr.mem_ball_of_le hy
  have hSint : B.ψ '' K ∪ Sq ∪ Sr ⊆ interior Kc :=
    union_subset (union_subset hψKint (hSqb.trans hdqK)) (hSrb.trans hdrK)
  obtain ⟨κ, hκ0, hκ1, hκ01⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    isOpen_interior.isClosed_compl ((hψKc.union hSqc).union hSrc).isClosed
    (disjoint_compl_left_iff_subset.2 hSint)
  have hκK : ∀ x ∈ B.ψ '' K, κ x = 1 := fun x hx => hκ1 (Or.inl (Or.inl hx))
  have hκSq : ∀ x ∈ Sq, κ x = 1 := fun x hx => hκ1 (Or.inl (Or.inr hx))
  have hκSr : ∀ x ∈ Sr, κ x = 1 := fun x hx => hκ1 (Or.inr hx)
  have hκint : ∀ x, κ x ≠ 0 → x ∈ interior Kc := by
    intro x hx
    by_contra h
    exact hx (hκ0 h)
  have hκnK : ∀ x, κ x ≠ 1 → x ∉ B.ψ '' K := fun x hx hK => hx (hκK x hK)
  have hκ01' : ∀ x, 0 ≤ κ x ∧ κ x ≤ 1 := fun x => hκ01 x
  set V₁ : (x : M) → TangentSpace I x := fun x => κ x • V x + (1 - κ x) • D.V x with hV₁def
  have hV₁s : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, V₁ x⟩ : TangentBundle I M)) :=
    (κ.contMDiff.smul_section hVs).add_section
      ((contMDiff_const.sub κ.contMDiff).smul_section D.smooth)
  have hV₁c : IsCompact (tsupport V₁) := by
    refine (hVc.union D.compact).of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport _).union (isClosed_tsupport _))
    by_contra h
    simp only [mem_union, not_or] at h
    apply hx
    have h1 : V x = 0 := image_eq_zero_of_notMem_tsupport h.1
    have h2 : D.V x = 0 := image_eq_zero_of_notMem_tsupport h.2
    simp [hV₁def, h1, h2]
    rfl
  have hdfV₁ : ∀ x, dfV I f₁ V₁ x = κ x * dfV I f₁ V x + (1 - κ x) * dfV I f₁ D.V x := by
    intro x
    rw [← dfL_apply]
    simp only [hV₁def, map_add, map_smul, smul_eq_mul, dfL_apply]
  have hev : ∀ x, x ∉ B.ψ '' K → f₁ =ᶠ[𝓝 x] f := fun x hx =>
    eventually_of_mem (hψKc.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hf₁K y hy
  have hdfeq : ∀ x, x ∉ B.ψ '' K → dfV I f₁ D.V x = dfV I f D.V x := by
    intro x hx
    unfold dfV
    rw [(hev x hx).mfderiv_eq]
    rfl
  have hV₁out : ∀ x, κ x = 0 → V₁ x = D.V x := by
    intro x hx
    simp [hV₁def, hx]
  have hV₁in : ∀ x, κ x = 1 → V₁ x = V x := by
    intro x hx
    simp [hV₁def, hx]
  have hold_nK : ∀ p (hp : p ∈ crit), ∀ x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R',
      x ∉ B.ψ '' K := fun p hp x hx hxK => hold_out p hp x hx (image_mono hKbox hxK)
  have hold_nint : ∀ p (hp : p ∈ crit), ∀ x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R',
      x ∉ interior Kc := fun p hp x hx hxK => hold_out p hp x hx (hintbox hxK)
  obtain ⟨old, hold⟩ : ∃ old : ∀ p (hp : p ∈ crit), MorseNormalChart I f₁ p,
      ∀ p hp, (old p hp).χ = (D.chart p hp).χ ∧ (old p hp).k = (D.chart p hp).k ∧
        (old p hp).R = (D.chart p hp).R ∧ (old p hp).R' = (D.chart p hp).R' ∧
        (old p hp).r₀ = (D.chart p hp).r₀ := by
    refine ⟨fun p hp =>
      { k := (D.chart p hp).k
        hk := (D.chart p hp).hk
        hkidx := by
          rw [MonotoneShift.morseIndex_congr_nhds
            (hev p (hold_nK p hp p (D.chart p hp).p_mem_image_ball))]
          exact (D.chart p hp).hkidx
        χ := (D.chart p hp).χ
        R := (D.chart p hp).R
        R' := (D.chart p hp).R'
        r₀ := (D.chart p hp).r₀
        hr₀ := (D.chart p hp).hr₀
        hr₀R := (D.chart p hp).hr₀R
        hRR' := (D.chart p hp).hRR'
        hχ0 := (D.chart p hp).hχ0
        hball := (D.chart p hp).hball
        hsrc := (D.chart p hp).hsrc
        hnorm := fun y hy => by
          rw [hf₁K _ (hold_nK p hp _ (mem_image_of_mem _ ((D.chart p hp).mem_ball_of_le hy))),
            hf₁K _ (hold_nK p hp p (D.chart p hp).p_mem_image_ball)]
          exact (D.chart p hp).hnorm y hy
        hχ := (D.chart p hp).hχ
        hχsymm := (D.chart p hp).hχsymm }, fun p hp => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have hmemc : ∀ p (hp : p ∈ insert q (insert r crit)), p ≠ q → p ≠ r → p ∈ crit :=
    fun p hp hpq hpr => Finset.mem_of_mem_insert_of_ne (Finset.mem_of_mem_insert_of_ne hp hpq) hpr
  obtain ⟨ch, hchq, hchr, hcho⟩ : ∃ ch : ∀ p (hp : p ∈ insert q (insert r crit)),
      MorseNormalChart I f₁ p,
      (∀ hp, ch q hp = dq) ∧ (∀ hp, ch r hp = dr) ∧
        ∀ p (hp : p ∈ crit) hp', ch p hp' = old p hp := by
    refine ⟨fun p hp => if hpq : p = q then hpq ▸ dq else if hpr : p = r then hpr ▸ dr else
      old p (hmemc p hp hpq hpr), fun hp => by simp, fun hp => by simp [hqr.symm], ?_⟩
    intro p hp hp'
    have hpq : p ≠ q := fun h => hqc (h ▸ hp)
    have hpr : p ≠ r := fun h => hrc (h ▸ hp)
    simp [hpq, hpr]
  obtain ⟨rmf, hrmq, hrmr, hrmo⟩ : ∃ rmf : ∀ p (hp : p ∈ insert q (insert r crit)), ℝ,
      (∀ hp, rmf q hp = dq.R) ∧ (∀ hp, rmf r hp = dr.R) ∧
        ∀ p (hp : p ∈ crit) hp', rmf p hp' = D.rm p hp := by
    refine ⟨fun p hp => if hpq : p = q then dq.R else if hpr : p = r then dr.R else
      D.rm p (hmemc p hp hpq hpr), fun hp => by simp, fun hp => by simp [hqr.symm], ?_⟩
    intro p hp hp'
    have hpq : p ≠ q := fun h => hqc (h ▸ hp)
    have hpr : p ≠ r := fun h => hrc (h ▸ hp)
    simp [hpq, hpr]
  have hsplit : ∀ p (hp : p ∈ insert q (insert r crit)),
      p = q ∨ p = r ∨ (p ≠ q ∧ p ≠ r ∧ p ∈ crit) := by
    intro p hp
    by_cases hpq : p = q
    · exact Or.inl hpq
    by_cases hpr : p = r
    · exact Or.inr (Or.inl hpr)
    exact Or.inr (Or.inr ⟨hpq, hpr, hmemc p hp hpq hpr⟩)
  have hqmem : q ∈ insert q (insert r crit) := Finset.mem_insert_self q _
  have hrmem : r ∈ insert q (insert r crit) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self r _)
  have hcmem : ∀ p ∈ crit, p ∈ insert q (insert r crit) := fun p hp =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
  have hrate₁ : ∀ x, -1 ≤ dfV I f₁ V₁ x ∧ dfV I f₁ V₁ x ≤ 0 := by
    intro x
    rw [hdfV₁]
    obtain ⟨h1, h2⟩ := hκ01' x
    obtain ⟨h3, h4⟩ := hVrate x
    by_cases hk1 : κ x = 1
    · rw [hk1]
      constructor <;> linarith
    · rw [hdfeq x (hκnK x hk1)]
      obtain ⟨h5, h6⟩ := D.dfV_rate x
      have e1 : 0 ≤ κ x * (dfV I f₁ V x + 1) := mul_nonneg h1 (by linarith)
      have e2 : 0 ≤ (1 - κ x) * (dfV I f D.V x + 1) := mul_nonneg (by linarith) (by linarith)
      have e3 : κ x * dfV I f₁ V x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h4
      have e4 : (1 - κ x) * dfV I f D.V x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h6
      constructor <;> nlinarith
  have hunit₁ : ∀ x ∈ f₁ ⁻¹' Icc a b,
      (∀ p hp, x ∉ (ch p hp).χ '' {y | morseNorm n y < (ch p hp).r₀}) → dfV I f₁ V₁ x = -1 := by
    intro x hx hxB
    have hA : κ x ≠ 0 → dfV I f₁ V x = -1 := by
      intro hk0
      have hq' := hxB q hqmem
      have hr' := hxB r hrmem
      rw [hchq] at hq'
      rw [hchr] at hr'
      exact hVunit x (interior_subset (hκint x hk0)) hq' hr'
    have hB : κ x ≠ 1 → dfV I f₁ D.V x = -1 := by
      intro hk1
      have hxK := hκnK x hk1
      rw [hdfeq x hxK]
      refine D.unit x ?_ fun p hp hmem => ?_
      · change f x ∈ Icc a b
        rw [← hf₁K x hxK]
        exact hx
      · have := hxB p (hcmem p hp)
        rw [hcho p hp, (hold p hp).1, (hold p hp).2.2.2.2] at this
        exact this hmem
    rw [hdfV₁]
    by_cases hk0 : κ x = 0
    · rw [hk0, hB (by rw [hk0]; norm_num)]
      ring
    by_cases hk1 : κ x = 1
    · rw [hk1, hA (by rw [hk1]; norm_num)]
      ring
    rw [hA hk0, hB hk1]
    ring
  have hneg₁ : ∀ x ∈ f₁ ⁻¹' Icc a b, x ∉ insert q (insert r crit) → dfV I f₁ V₁ x < 0 := by
    intro x hx hxc
    have hxq : x ≠ q := fun h => hxc (h ▸ hqmem)
    have hxr : x ≠ r := fun h => hxc (h ▸ hrmem)
    have hxc' : x ∉ crit := fun h => hxc (hcmem x h)
    have hA : κ x ≠ 0 → dfV I f₁ V x < 0 := fun hk0 =>
      hVneg x (interior_subset (hκint x hk0)) hxq hxr
    have hB : κ x ≠ 1 → dfV I f₁ D.V x < 0 := by
      intro hk1
      have hxK := hκnK x hk1
      rw [hdfeq x hxK]
      refine D.neg x ?_ hxc'
      change f x ∈ Icc a b
      rw [← hf₁K x hxK]
      exact hx
    rw [hdfV₁]
    obtain ⟨h1, h2⟩ := hκ01' x
    by_cases hk0 : κ x = 0
    · rw [hk0]
      have := hB (by rw [hk0]; norm_num)
      linarith
    by_cases hk1 : κ x = 1
    · rw [hk1]
      have := hA (by rw [hk1]; norm_num)
      linarith
    have e1 : κ x * dfV I f₁ V x < 0 :=
      mul_neg_of_pos_of_neg (lt_of_le_of_ne h1 (Ne.symm hk0)) (hA hk0)
    have e2 : (1 - κ x) * dfV I f₁ D.V x < 0 :=
      mul_neg_of_pos_of_neg (by have := lt_of_le_of_ne h2 hk1; linarith) (hB hk1)
    linarith
  have hqbox : dq.χ '' Metric.ball 0 dq.R' ⊆ B.ψ '' boxSet B.i₀ ρ L := hdqK.trans hintbox
  have hrbox : dr.χ '' Metric.ball 0 dr.R' ⊆ B.ψ '' boxSet B.i₀ ρ L := hdrK.trans hintbox
  have hdisj_old : ∀ p (hp : p ∈ crit) (S : Set M), S ⊆ B.ψ '' boxSet B.i₀ ρ L →
      Disjoint S ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') := fun p hp S hS =>
    Set.disjoint_left.2 fun x hx1 hx2 => hold_out p hp x hx2 (hS hx1)
  have hdisj₁ : ∀ p hp p' hp', p ≠ p' →
      Disjoint ((ch p hp).χ '' Metric.ball 0 (ch p hp).R')
        ((ch p' hp').χ '' Metric.ball 0 (ch p' hp').R') := by
    intro p hp p' hp' hpp
    rcases hsplit p hp with rfl | rfl | ⟨hpq, hpr, hpc⟩ <;>
      rcases hsplit p' hp' with rfl | rfl | ⟨hpq', hpr', hpc'⟩
    · exact absurd rfl hpp
    · rw [hchq, hchr]; exact hdqr
    · rw [hchq, hcho p' hpc', (hold p' hpc').1, (hold p' hpc').2.2.2.1]
      exact hdisj_old p' hpc' _ hqbox
    · rw [hchq, hchr]; exact hdqr.symm
    · exact absurd rfl hpp
    · rw [hchr, hcho p' hpc', (hold p' hpc').1, (hold p' hpc').2.2.2.1]
      exact hdisj_old p' hpc' _ hrbox
    · rw [hchq, hcho p hpc, (hold p hpc).1, (hold p hpc).2.2.2.1]
      exact (hdisj_old p hpc _ hqbox).symm
    · rw [hchr, hcho p hpc, (hold p hpc).1, (hold p hpc).2.2.2.1]
      exact (hdisj_old p hpc _ hrbox).symm
    · rw [hcho p hpc, (hold p hpc).1, (hold p hpc).2.2.2.1, hcho p' hpc', (hold p' hpc').1,
        (hold p' hpc').2.2.2.1]
      exact D.disjoint p hpc p' hpc' hpp
  have hinStrip₁ : ∀ p hp, (ch p hp).χ '' Metric.ball 0 (ch p hp).R' ⊆ f₁ ⁻¹' Ioo a b := by
    have hbox' : B.ψ '' boxSet B.i₀ ρ L ⊆ f₁ ⁻¹' Ioo a b := by
      rintro x ⟨y, hy, rfl⟩
      exact hf₁box y hy
    intro p hp
    rcases hsplit p hp with rfl | rfl | ⟨hpq, hpr, hpc⟩
    · rw [hchq]; exact hqbox.trans hbox'
    · rw [hchr]; exact hrbox.trans hbox'
    · rw [hcho p hpc, (hold p hpc).1, (hold p hpc).2.2.2.1]
      intro x hx
      change f₁ x ∈ Ioo a b
      rw [hf₁K x (hold_nK p hpc x hx)]
      exact D.inStrip p hpc hx
  have hrm₁ : ∀ p hp, 2 * (ch p hp).r₀ < rmf p hp ∧ rmf p hp ≤ (ch p hp).R := by
    intro p hp
    rcases hsplit p hp with rfl | rfl | ⟨hpq, hpr, hpc⟩
    · rw [hchq, hrmq]
      exact ⟨by linarith [dq.hr₀R, dq.hr₀], le_rfl⟩
    · rw [hchr, hrmr]
      exact ⟨by linarith [dr.hr₀R, dr.hr₀], le_rfl⟩
    · rw [hcho p hpc, (hold p hpc).2.2.2.2, (hold p hpc).2.2.1, hrmo p hpc]
      exact D.hrm p hpc
  have hmodel₁ : ∀ p hp, ∀ y, morseNorm n y < rmf p hp →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (ch p hp).χ.symm ((ch p hp).χ y) (V₁ ((ch p hp).χ y)) =
        ModelField.modelField (ch p hp).k (ch p hp).r₀ y := by
    intro p hp y hy
    rcases hsplit p hp with rfl | rfl | ⟨hpq, hpr, hpc⟩
    · rw [hrmq] at hy
      rw [hchq, hV₁in _ (hκSq _ (mem_image_of_mem _ hy.le))]
      exact hdqmod y hy
    · rw [hrmr] at hy
      rw [hchr, hV₁in _ (hκSr _ (mem_image_of_mem _ hy.le))]
      exact hdrmod y hy
    · rw [hrmo p hpc] at hy
      rw [hcho p hpc, (hold p hpc).1, (hold p hpc).2.1, (hold p hpc).2.2.2.2]
      have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hpc).R' :=
        (D.chart p hpc).mem_ball_of_le (hy.le.trans (D.hrm p hpc).2)
      have hk0 : κ ((D.chart p hpc).χ y) = 0 := by
        by_contra h
        exact hold_nint p hpc _ (mem_image_of_mem _ hyb) (hκint _ h)
      rw [hV₁out _ hk0]
      exact D.model p hpc y hy
  let D₁ : GradientLikeStrip I f₁ a b (insert q (insert r crit)) :=
    { V := V₁
      smooth := hV₁s
      compact := hV₁c
      rate := hrate₁
      chart := ch
      disjoint := hdisj₁
      inStrip := hinStrip₁
      unit := hunit₁
      neg := hneg₁
      rm := rmf
      hrm := hrm₁
      model := hmodel₁ }
  refine ⟨D₁, ?_, ?_, ?_, ε', hε'0, hε'ε, ?_⟩
  · intro x hx
    change (ch x _).χ = _ ∧ (ch x _).k = _ ∧ (ch x _).R = _ ∧ (ch x _).R' = _ ∧
      (ch x _).r₀ = _ ∧ rmf x _ = _
    rw [hcho x hx, hrmo x hx]
    exact ⟨(hold x hx).1, (hold x hx).2.1, (hold x hx).2.2.1, (hold x hx).2.2.2.1,
      (hold x hx).2.2.2.2, rfl⟩
  · intro x hx
    change V₁ x = D.V x
    refine hV₁out x (by_contra fun h => hx (hintmid (hκint x h)))
  · intro x hx hxqr
    change (ch x hx).χ '' Metric.ball 0 (ch x hx).R' ⊆ O ∧
      ∀ y ∈ (ch x hx).χ '' Metric.ball 0 (ch x hx).R', |f₁ y - f₁ x| < ε
    rcases hxqr with rfl | rfl
    · rw [hchq]
      exact ⟨hdqK.trans hintmid, hdqε⟩
    · rw [hchr]
      exact ⟨hdrK.trans hintmid, hdrε⟩
  · intro x hx hxqr
    change (ch x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < rmf x hx ^ 2
    rcases hxqr with rfl | rfl
    · rw [hchq, hrmq]
      exact ⟨hdq1, hdq2⟩
    · rw [hchr, hrmr]
      exact ⟨hdr1, hdr2⟩

theorem leftLoop_mem_bottomFace {f₁ : M → ℝ} {crit₁ : Finset M} (hf₁ : MorseStrip I f₁ a b)
    (D : GradientLikeStrip I f a b crit) (D₁ : GradientLikeStrip I f₁ a b crit₁) {x₀ : M}
    {c L ρ : ℝ} (B : FlowBox D x₀ c L ρ) (hL : 0 < L) (hρ : 0 < ρ)
    (hab : a < c - ρ ∧ c + L + ρ < b)
    (hf₁eq : ∀ x, x ∉ B.ψ '' midBox B.i₀ ρ L → f₁ x = f x)
    (hf₁mid : ∀ y ∈ midBox B.i₀ ρ L, c < f₁ (B.ψ y))
    (hV : ∀ x, x ∉ B.ψ '' midBox B.i₀ ρ L → D₁.V x = D.V x) {q : M} (hq : q ∈ crit₁) {ε : ℝ}
    (hε : 0 < ε) (hεq : (D₁.chart q hq).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D₁.rm q hq ^ 2)
    (hchart : (D₁.chart q hq).χ '' Metric.ball 0 (D₁.chart q hq).R' ⊆ B.ψ '' midBox B.i₀ ρ L)
    (hothers : ∀ x (hx : x ∈ crit₁), x ≠ q → ∀ y ∈ D₁.closedSmallBall x hx,
      y ∈ B.ψ '' boxSet B.i₀ ρ L → f₁ q - ε < f₁ y) :
    ∀ y ∈ (D₁.chart q hq).leftModelSphere ε,
      (∀ s ∈ Icc 0 (f₁ q - ε - c), ∀ x (hx : x ∈ crit₁),
        D₁.flow s ((D₁.chart q hq).χ y) ∉ D₁.closedSmallBall x hx) ∧
      D₁.flow (f₁ q - ε - c) ((D₁.chart q hq).χ y) ∈ B.ψ '' bottomFace B.i₀ ρ := by
  classical
  intro y hy
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁ := hf₁.smooth
  have hrmpos := D₁.rm_pos q hq
  have hrmR := (D₁.hrm q hq).2
  have hRsq : 2 * ε ≤ (D₁.chart q hq).R ^ 2 := by nlinarith [hεq.2]
  have hyR := (D₁.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hRsq hy
  have hyball := (D₁.chart q hq).mem_ball_of_le hyR
  have hfx : f₁ ((D₁.chart q hq).χ y) = f₁ q - ε :=
    (D₁.chart q hq).f_chart_of_mem_leftModelSphere hRsq hy
  have hxmid : (D₁.chart q hq).χ y ∈ B.ψ '' midBox B.i₀ ρ L :=
    hchart (mem_image_of_mem _ hyball)
  have hxstrip : f₁ ((D₁.chart q hq).χ y) ∈ Ioo a b := D₁.inStrip q hq (mem_image_of_mem _ hyball)
  have hcx : c < f₁ ((D₁.chart q hq).χ y) := by
    obtain ⟨w, hw, hwx⟩ := hxmid
    rw [← hwx]
    exact hf₁mid w hw
  set x := (D₁.chart q hq).χ y with hxdef
  have hT : 0 < f₁ q - ε - c := by linarith
  set e : Fin n → ℝ := Pi.single B.i₀ (1 : ℝ) with he
  have hci : ∀ (z : Fin n → ℝ) (s : ℝ), (z - s • e) B.i₀ = z B.i₀ - s := by
    intro z s
    simp [he]
  have hcj : ∀ (z : Fin n → ℝ) (s : ℝ) (j : Fin n), j ≠ B.i₀ → (z - s • e) j = z j := by
    intro z s j hj
    simp [he, hj]
  have hmid_box : midBox B.i₀ ρ L ⊆ boxSet B.i₀ ρ L := by
    intro z hz
    refine ⟨fun j hj => by linarith [hz.1 j hj], by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hinj : ∀ z w, z ∈ boxSet B.i₀ ρ L → w ∈ boxSet B.i₀ ρ L → B.ψ z = B.ψ w → z = w :=
    fun z w hz hw h => B.ψ.injOn (B.box_subset hz) (B.box_subset hw) h
  have hnotmid : ∀ z ∈ boxSet B.i₀ ρ L, z ∉ midBox B.i₀ ρ L → B.ψ z ∉ B.ψ '' midBox B.i₀ ρ L := by
    rintro z hz hzm ⟨w, hw, hwz⟩
    exact hzm (hinj w z (hmid_box hw) hz hwz ▸ hw)
  set W₀ : Set (Fin n → ℝ) :=
    {z | (∀ j, j ≠ B.i₀ → |z j| < 3 * ρ / 4) ∧ -(ρ / 2) < z B.i₀ ∧ z B.i₀ < 7 * L / 8} with hW₀
  set K₀ : Set (Fin n → ℝ) := Set.pi univ (fun j => if j = B.i₀ then Icc (-(ρ / 2)) (7 * L / 8)
    else Icc (-(3 * ρ / 4)) (3 * ρ / 4)) with hK₀
  have hK₀mem : ∀ z ∈ K₀, (∀ j, j ≠ B.i₀ → |z j| ≤ 3 * ρ / 4) ∧ -(ρ / 2) ≤ z B.i₀ ∧
      z B.i₀ ≤ 7 * L / 8 := by
    intro z hz
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · have h := hz j (mem_univ _)
      simp only [hj, ite_false] at h
      exact abs_le.2 h
    · have h := hz B.i₀ (mem_univ _)
      simp only [ite_true] at h
      exact h.1
    · have h := hz B.i₀ (mem_univ _)
      simp only [ite_true] at h
      exact h.2
  have hW₀K₀ : W₀ ⊆ K₀ := by
    intro z hz j _
    by_cases hj : j = B.i₀
    · subst hj
      simp only [ite_true]
      exact ⟨hz.2.1.le, hz.2.2.le⟩
    · simp only [hj, ite_false]
      exact abs_le.1 (hz.1 j hj).le
  have hK₀box : K₀ ⊆ boxSet B.i₀ ρ L := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hK₀mem z hz
    exact ⟨fun j hj => by linarith [h1 j hj], by linarith, by linarith⟩
  have hmidW₀ : midBox B.i₀ ρ L ⊆ W₀ := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  have hW₀open : IsOpen W₀ := by
    have hEq : W₀ = (⋂ j, {z : Fin n → ℝ | j ≠ B.i₀ → |z j| < 3 * ρ / 4}) ∩
        ({z | -(ρ / 2) < z B.i₀} ∩ {z | z B.i₀ < 7 * L / 8}) := by
      ext z
      simp [hW₀]
    rw [hEq]
    refine (isOpen_iInter_of_finite fun j => ?_).inter
      ((isOpen_lt continuous_const (continuous_apply B.i₀)).inter
        (isOpen_lt (continuous_apply B.i₀) continuous_const))
    by_cases hj : j = B.i₀
    · simp [hj]
    · simpa [hj] using isOpen_lt ((continuous_apply j).abs) continuous_const
  have hK₀compact : IsCompact K₀ :=
    isCompact_univ_pi fun j => by split_ifs <;> exact isCompact_Icc
  have hWopen : IsOpen (B.ψ '' W₀) :=
    B.ψ.isOpen_image_of_subset_source hW₀open ((hW₀K₀.trans hK₀box).trans B.box_subset)
  have hKclosed : IsClosed (B.ψ '' K₀) :=
    (hK₀compact.image_of_continuousOn
      (B.ψ.continuousOn.mono (hK₀box.trans B.box_subset))).isClosed
  have hxW : x ∈ B.ψ '' W₀ := image_mono hmidW₀ hxmid
  have hlev_out : ∀ z ∈ boxSet B.i₀ ρ L, z ∉ midBox B.i₀ ρ L → f₁ (B.ψ z) = c + z B.i₀ := by
    intro z hz hzm
    rw [hf₁eq _ (hnotmid z hz hzm)]
    exact B.level z hz
  have hstay : ∀ s ∈ Icc 0 (f₁ q - ε - c), D₁.flow s x ∈ B.ψ '' W₀ := by
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 (f₁ q - ε - c) ∩ {s | D₁.flow s x ∉ B.ψ '' W₀} with hS
    have hSclosed : IsClosed S :=
      isClosed_Icc.inter (hWopen.isClosed_compl.preimage (D₁.continuous_flow_curve x))
    have hSne : S.Nonempty := by
      obtain ⟨s, hs, hsW⟩ := hcon
      exact ⟨s, hs, hsW⟩
    have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set t₁ := sInf S with ht₁
    have ht₁S : t₁ ∈ S := hSclosed.csInf_mem hSne hbdd
    have hbefore : ∀ s ∈ Ico 0 t₁, D₁.flow s x ∈ B.ψ '' W₀ := by
      intro s hs
      by_contra hsW
      have hsS : s ∈ S := ⟨⟨hs.1, by linarith [hs.2, ht₁S.1.2]⟩, hsW⟩
      linarith [csInf_le hbdd hsS, hs.2]
    have ht₁pos : 0 < t₁ := by
      rcases eq_or_lt_of_le ht₁S.1.1 with h | h
      · exfalso
        apply ht₁S.2
        rw [← h, D₁.flow_zero]
        exact hxW
      · exact h
    have hK : D₁.flow t₁ x ∈ B.ψ '' K₀ := by
      have hQ : IsClosed {s : ℝ | D₁.flow s x ∈ B.ψ '' K₀} :=
        hKclosed.preimage (D₁.continuous_flow_curve x)
      have hsub : Ico 0 t₁ ⊆ {s : ℝ | D₁.flow s x ∈ B.ψ '' K₀} := fun s hs =>
        image_mono hW₀K₀ (hbefore s hs)
      have hcl := closure_minimal hsub hQ
      rw [closure_Ico ht₁pos.ne] at hcl
      exact hcl ⟨ht₁pos.le, le_rfl⟩
    obtain ⟨z, hzK, hzx⟩ := hK
    have hzbox := hK₀box hzK
    obtain ⟨hz1, hz2, hz3⟩ := hK₀mem z hzK
    have hzW : z ∉ W₀ := by
      intro hzW
      apply ht₁S.2
      rw [← hzx]
      exact mem_image_of_mem _ hzW
    have hflev : f₁ x - t₁ ≤ f₁ (D₁.flow t₁ x) :=
      GradientLikeStrip.sub_le_f_flow (D := D₁) hfs x ht₁pos.le
    rcases eq_or_lt_of_le hz2 with hzb | hzb
    · have hzm : z ∉ midBox B.i₀ ρ L := fun hm => by linarith [hm.2.1]
      have h1 := hlev_out z hzbox hzm
      rw [hzx, ← hzb] at h1
      linarith [ht₁S.1.2]
    · have hback : ∀ s : ℝ, s ≤ 0 → z - s • e ∉ W₀ := by
        intro s hs hmem
        apply hzW
        refine ⟨fun j hj => ?_, hzb, ?_⟩
        · have := hmem.1 j hj
          rwa [hcj z s j hj] at this
        · have := hmem.2.2
          rw [hci] at this
          linarith
      set δ := min t₁ (L / 8) with hδ
      have hδpos : 0 < δ := lt_min ht₁pos (by linarith)
      have hδt : δ ≤ t₁ := min_le_left _ _
      have hδL : δ ≤ L / 8 := min_le_right _ _
      have hmembox : ∀ s : ℝ, s ∈ uIcc 0 (-δ) → z - s • e ∈ boxSet B.i₀ ρ L := by
        intro s hs
        rw [uIcc_of_ge (by linarith)] at hs
        refine ⟨fun j hj => ?_, ?_, ?_⟩
        · rw [hcj z s j hj]
          linarith [hz1 j hj]
        · rw [hci]
          linarith [hs.2]
        · rw [hci]
          linarith [hs.1]
      have hagree := flow_eq_of_agree_along D D₁ (x := B.ψ z) (T := -δ) (by
        intro s hs
        rw [B.vertical z hzbox s (hmembox s hs)]
        refine hV _ (hnotmid _ (hmembox s hs) fun hm => ?_)
        rw [uIcc_of_ge (by linarith)] at hs
        exact hback s hs.2 (hmidW₀ hm))
      rw [B.vertical z hzbox (-δ) (hmembox (-δ) right_mem_uIcc), hzx, D₁.flow_flow] at hagree
      have hin := hbefore (t₁ + -δ) ⟨by linarith, by linarith⟩
      rw [hagree] at hin
      obtain ⟨w, hw, hwz⟩ := hin
      have := hinj w _ (hK₀box (hW₀K₀ hw)) (hmembox (-δ) right_mem_uIcc) hwz
      exact hback (-δ) (by linarith) (this ▸ hw)
  have hfree : ∀ s ∈ Icc 0 (f₁ q - ε - c), ∀ x' (hx' : x' ∈ crit₁),
      D₁.flow s x ∉ D₁.closedSmallBall x' hx' := by
    intro s hs x' hx' hmem
    have hle : f₁ (D₁.flow s x) ≤ f₁ x := GradientLikeStrip.f_flow_le (D := D₁) hfs x hs.1
    by_cases hx'q : x' = q
    · subst hx'q
      obtain ⟨w, hw, hwx⟩ := hmem
      have hw' : morseNorm n w ≤ (D₁.chart x' hq).R := by
        linarith [D₁.r₀_lt_R x' hq, (show morseNorm n w ≤ (D₁.chart x' hq).r₀ from hw)]
      have hnf := (D₁.chart x' hq).hnorm w hw'
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hnf
      have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D₁.chart x' hq).hk w
      have hw2 : morseNorm n w ^ 2 ≤ (D₁.chart x' hq).r₀ ^ 2 :=
        pow_le_pow_left₀ (ModelField.morseNorm_nonneg w) hw 2
      rw [hwx] at hnf
      nlinarith [sq_nonneg ‖posPart (D₁.chart x' hq).hk w‖, hεq.1]
    · have hbox : D₁.flow s x ∈ B.ψ '' boxSet B.i₀ ρ L :=
        image_mono (hW₀K₀.trans hK₀box) (hstay s hs)
      have := hothers x' hx' hx'q _ hmem hbox
      linarith
  refine ⟨hfree, ?_⟩
  have hunit : ∀ s ∈ Icc 0 (f₁ q - ε - c), D₁.flow s x ∈ D₁.unitRegion := by
    intro s hs
    refine ⟨⟨?_, ?_⟩, fun p hp hsb => hfree s hs p hp (D₁.smallBall_subset_closedSmallBall p hp hsb)⟩
    · linarith [GradientLikeStrip.sub_le_f_flow (D := D₁) hfs x hs.1, hs.2, hab.1, hρ]
    · linarith [GradientLikeStrip.f_flow_le (D := D₁) hfs x hs.1, hxstrip.2]
  have hlevT := GradientLikeStrip.f_flow_eq_sub (D := D₁) hfs hT.le hunit _
    (right_mem_Icc.2 hT.le)
  obtain ⟨z, hzW, hzx⟩ := hstay _ (right_mem_Icc.2 hT.le)
  have hzbox := hK₀box (hW₀K₀ hzW)
  by_cases hzm : z ∈ midBox B.i₀ ρ L
  · have := hf₁mid z hzm
    rw [hzx, hlevT] at this
    linarith
  · have h1 := hlev_out z hzbox hzm
    rw [hzx, hlevT] at h1
    refine ⟨z, ⟨fun j hj => by linarith [hzW.1 j hj], by linarith⟩, hzx⟩

theorem isLevelLoop_leftLoop (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {q : M} (hq : q ∈ crit) (hk : (D.chart q hq).k = 2)
    {ε c : ℝ} (hε : 0 < ε) (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) (hc : a ≤ c)
    (hcq : c ≤ f q - ε)
    (hfree : ∀ y ∈ (D.chart q hq).leftModelSphere ε, ∀ s ∈ Icc 0 (f q - ε - c),
      ∀ x (hx : x ∈ crit), D.flow s ((D.chart q hq).χ y) ∉ D.closedSmallBall x hx) :
    isLevelLoop I f c (leftLoop D q hq hk ε c) := by
  classical
  have hdef : ∀ t, leftLoop D q hq hk ε c t = D.flow (f q - ε - c) ((D.chart q hq).χ
      ((D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)))) := fun t => rfl
  have hcirc0 : ∀ t, circ2 t 0 = Real.cos (2 * Real.pi * t) := fun t => by simp [circ2]
  have hcirc1 : ∀ t, circ2 t 1 = Real.sin (2 * Real.pi * t) := fun t => by simp [circ2]
  have hw0 : ∀ t, (fun i : Fin (D.chart q hq).k => circ2 t (Fin.cast hk i)) ≠ 0 := by
    intro t h
    have h0 := congrFun h (Fin.cast hk.symm 0)
    have h1 := congrFun h (Fin.cast hk.symm 1)
    simp only [Fin.cast_cast, Fin.cast_eq_self, Pi.zero_apply] at h0 h1
    rw [hcirc0] at h0
    rw [hcirc1] at h1
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
  have hnorm1 : ∀ t, ‖(D.chart q hq).toE (fun i => circ2 t (Fin.cast hk i))‖ = 1 := by
    intro t
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ i : Fin (D.chart q hq).k,
        ‖((D.chart q hq).toE (fun i => circ2 t (Fin.cast hk i))).ofLp i‖ ^ 2 =
        ∑ j : Fin 2, (circ2 t j) ^ 2 :=
      Fintype.sum_equiv (finCongr hk) _ _ (fun i => by
        simp [MorseNormalChart.toE])
    rw [hs, Fin.sum_univ_two, hcirc0, hcirc1, Real.cos_sq_add_sin_sq, Real.sqrt_one]
  set L : Fin 2 → (Fin n → ℝ) →L[ℝ] ℝ := fun j =>
    (EuclideanSpace.proj (Fin.cast hk.symm j)).comp (ModelField.negPartL (D.chart q hq).hk)
    with hL
  have hLsp : ∀ t (j : Fin 2),
      L j ((D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i))) =
        Real.sqrt (2 * ε) * circ2 t j := by
    intro t j
    simp only [hL, ContinuousLinearMap.comp_apply, ModelField.negPartL_apply,
      MorseNormalChart.negPart_sphereParam, hnorm1, div_one]
    simp [MorseNormalChart.toE]
  have hmem : ∀ t, (D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)) ∈
      (D.chart q hq).leftModelSphere ε := fun t =>
    (D.chart q hq).sphereParam_mem_leftModelSphere hε.le (hw0 t)
  have hball : ∀ t, (D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)) ∈
      Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' := fun t =>
    (D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hεR (hw0 t))
  have hsqrt : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
  have hwsmooth : ContDiff ℝ ∞ (fun t : ℝ => (fun i : Fin (D.chart q hq).k =>
      circ2 t (Fin.cast hk i))) := by
    refine contDiff_pi.2 fun i => ?_
    generalize Fin.cast hk i = j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, hcirc0]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, hcirc1]
      fun_prop
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (leftLoop D q hq hk ε c) := by
    intro t
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun t => (D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i))) t :=
      contMDiffAt_iff_contDiffAt.2
        (((D.chart q hq).contDiffAt_sphereParam ε (hw0 t)).comp (f := fun t : ℝ =>
          (fun i : Fin (D.chart q hq).k => circ2 t (Fin.cast hk i))) t hwsmooth.contDiffAt)
    have h2 := ((D.chart q hq).contMDiffAt_chart (hball t)).comp t h1
    exact ((D.contMDiff_flow (f q - ε - c)).contMDiffAt).comp t h2
  have hback : ∀ (j : Fin 2) t, L j ((D.chart q hq).χ.symm
      (D.flow (-(f q - ε - c)) (leftLoop D q hq hk ε c t))) = Real.sqrt (2 * ε) * circ2 t j := by
    intro j t
    rw [hdef, D.flow_neg_flow, (D.chart q hq).χ.left_inv ((D.chart q hq).hball (hball t)), hLsp]
  refine ⟨fun t => ?_, hsmooth, fun t => ?_, fun t t' htt => ?_, fun t => ?_⟩
  · have hper : circ2 (t + 1) = circ2 t := by
      simp only [circ2, mul_add, mul_one, Real.cos_add_two_pi, Real.sin_add_two_pi]
    rw [hdef, hdef, hper]
  · intro h0
    have hder : ∀ j : Fin 2, deriv (fun t => Real.sqrt (2 * ε) * circ2 t j) t = 0 := by
      intro j
      have hLm : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => L j ((D.chart q hq).χ.symm
          (D.flow (-(f q - ε - c)) x))) (leftLoop D q hq hk ε c t) := by
        have hx : D.flow (-(f q - ε - c)) (leftLoop D q hq hk ε c t) ∈
            (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' := by
          rw [hdef, D.flow_neg_flow]
          exact mem_image_of_mem _ (hball t)
        have h1 := (D.chart q hq).contMDiffAt_symm hx
        have h2 := h1.comp (leftLoop D q hq hk ε c t)
          ((D.contMDiff_flow (-(f q - ε - c))).contMDiffAt)
        have h3 := ((L j).contMDiff.contMDiffAt).comp (leftLoop D q hq hk ε c t) h2
        exact h3.mdifferentiableAt (by simp)
      have hgm : MDifferentiableAt 𝓘(ℝ, ℝ) I (leftLoop D q hq hk ε c) t :=
        (hsmooth t).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp t hLm hgm
      have hfun : ((fun x => L j ((D.chart q hq).χ.symm (D.flow (-(f q - ε - c)) x))) ∘
          leftLoop D q hq hk ε c) = fun t => Real.sqrt (2 * ε) * circ2 t j :=
        funext fun t => hback j t
      rw [hfun, mfderiv_eq_fderiv] at hcomp
      rw [← fderiv_apply_one_eq_deriv]
      have h0' := congrArg (mfderiv I 𝓘(ℝ, ℝ) (fun x => L j ((D.chart q hq).χ.symm
        (D.flow (-(f q - ε - c)) x))) (leftLoop D q hq hk ε c t)) h0
      rw [map_zero] at h0'
      exact (DFunLike.congr_fun hcomp (1 : ℝ)).trans h0'
    have hd0 : HasDerivAt (fun t => Real.sqrt (2 * ε) * circ2 t 0)
        (Real.sqrt (2 * ε) * (-Real.sin (2 * Real.pi * t) * (2 * Real.pi))) t := by
      simp only [hcirc0]
      exact (((hasDerivAt_id t).const_mul (2 * Real.pi)).cos.const_mul _).congr_deriv (by simp only [id]; ring)
    have hd1 : HasDerivAt (fun t => Real.sqrt (2 * ε) * circ2 t 1)
        (Real.sqrt (2 * ε) * (Real.cos (2 * Real.pi * t) * (2 * Real.pi))) t := by
      simp only [hcirc1]
      exact (((hasDerivAt_id t).const_mul (2 * Real.pi)).sin.const_mul _).congr_deriv (by simp only [id]; ring)
    have e0 := hder 0
    have e1 := hder 1
    rw [hd0.deriv] at e0
    rw [hd1.deriv] at e1
    have hpi : 0 < 2 * Real.pi := by positivity
    have s0 : Real.sin (2 * Real.pi * t) = 0 := by
      rcases mul_eq_zero.1 e0 with h | h
      · exact absurd h hsqrt.ne'
      · rcases mul_eq_zero.1 h with h' | h'
        · linarith
        · exact absurd h' hpi.ne'
    have c0 : Real.cos (2 * Real.pi * t) = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · exact absurd h hsqrt.ne'
      · rcases mul_eq_zero.1 h with h' | h'
        · exact h'
        · exact absurd h' hpi.ne'
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
  · have hc0 := hback 0 t
    have hc1 := hback 1 t
    rw [htt, hback 0 t'] at hc0
    rw [htt, hback 1 t'] at hc1
    rw [hcirc0, hcirc0] at hc0
    rw [hcirc1, hcirc1] at hc1
    have hcos := mul_left_cancel₀ hsqrt.ne' hc0
    have hsin := mul_left_cancel₀ hsqrt.ne' hc1
    obtain ⟨k, hk'⟩ := Real.cos_eq_cos_iff.1 hcos.symm
    obtain ⟨m, hm⟩ := Real.sin_eq_sin_iff.1 hsin.symm
    have hpi : 0 < Real.pi := Real.pi_pos
    rcases hk' with h | h
    · refine ⟨k, ?_⟩
      have : 2 * Real.pi * (t' - t - k) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
    · rcases hm with h' | h'
      · refine ⟨m, ?_⟩
        have : 2 * Real.pi * (t' - t - m) = 0 := by linarith
        rcases mul_eq_zero.1 this with h'' | h''
        · linarith
        · linarith
      · exfalso
        have : (2 * (k : ℝ) - (2 * m + 1)) * Real.pi = 0 := by linarith
        rcases mul_eq_zero.1 this with h'' | h''
        · have hkm : (2 * k - (2 * m + 1) : ℤ) = 0 := by exact_mod_cast h''
          omega
        · linarith
  · have hfx := (D.chart q hq).f_chart_of_mem_leftModelSphere hεR (hmem t)
    have hq' := D.f_mem_Ioo q hq
    have hT : 0 ≤ f q - ε - c := by linarith
    have key := D.f_flow_eq_sub_of_avoid_uIcc hf
      (x := (D.chart q hq).χ ((D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i))))
      (T := f q - ε - c) (by rw [hfx]; constructor <;> linarith [hq'.2])
      (by rw [hfx]; constructor <;> linarith [hq'.2])
      (fun s hs x hx hmem' => hfree _ (hmem t) s (by rwa [uIcc_of_le hT] at hs) x hx
        (D.smallBall_subset_closedSmallBall x hx hmem'))
      (f q - ε - c) right_mem_uIcc
    rw [hdef, key, hfx]
    ring

theorem exists_birth_in_box [SigmaCompactSpace M] [DecidableEq M] (h5 : 5 ≤ n)
    (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {x₀ : M} {c L ρ : ℝ}
    (B : FlowBox D x₀ c L ρ) (hL : 0 < L) (hρ : 0 < ρ) (hab : a < c - ρ ∧ c + L + ρ < b)
    {ε : ℝ} (hε : 0 < ε) (hεL : 16 * ε < L) :
    ∃ (f₁ : M → ℝ) (q r : M) (D₁ : GradientLikeStrip I f₁ a b (insert q (insert r crit))),
      ModifiedWithin f c (c + L) f₁ ∧ MorseStrip I f₁ a b ∧
      (∀ x, x ∉ B.ψ '' midBox B.i₀ ρ L → f₁ x = f x ∧ D₁.V x = D.V x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∨ x = q ∨ x = r) ∧
      q ∈ B.ψ '' midBox B.i₀ ρ L ∧ r ∈ B.ψ '' midBox B.i₀ ρ L ∧
      c + L / 4 < f₁ q ∧ f₁ q < f₁ r ∧ f₁ r < c + 3 * L / 4 ∧
      morseIndex I f₁ q = 2 ∧ morseIndex I f₁ r = 3 ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f₁ x = morseIndex I f x) ∧
      (∀ x (hx : x ∈ crit),
        (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).χ =
            (D.chart x hx).χ ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).k =
            (D.chart x hx).k ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R =
            (D.chart x hx).R ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R' =
            (D.chart x hx).R' ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).r₀ =
            (D.chart x hx).r₀ ∧
          D₁.rm x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) = D.rm x hx) ∧
      (∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
        (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R' ⊆ B.ψ '' midBox B.i₀ ρ L ∧
        ∀ y ∈ (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R', |f₁ y - f₁ x| < ε) ∧
      ∃ (hkq : (D₁.chart q (Finset.mem_insert_self q _)).k = 2) (ε' : ℝ), 0 < ε' ∧ ε' ≤ ε ∧
        2 * ε' < f₁ r - f₁ q ∧
        (D₁.chart q (Finset.mem_insert_self q _)).r₀ ^ 2 < 2 * ε' ∧
        8 * ε' < D₁.rm q (Finset.mem_insert_self q _) ^ 2 ∧
        (∀ y ∈ (D₁.chart q (Finset.mem_insert_self q _)).leftModelSphere ε',
          ∀ s ∈ Icc 0 (f₁ q - ε' - c), ∀ x (hx : x ∈ insert q (insert r crit)),
            D₁.flow s ((D₁.chart q (Finset.mem_insert_self q _)).χ y) ∉
              D₁.closedSmallBall x hx) ∧
        (∀ t, leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' c t ∈
          B.ψ '' bottomFace B.i₀ ρ) ∧
        isLevelLoop I f₁ c (leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' c) := by
  have hl : 2 < n := by omega
  obtain ⟨f₁, q, r, K, hK, hKin, hf₁K, hlevK, hmod, hf₁, hqK, hrK, hqr, hcrit₁, hidxq, hidxr,
    hidxold⟩ := exists_insert_pair (l := 2) hf D hcrit B hL hρ hab hl
  have hinmid : innerBox B.i₀ ρ L ⊆ midBox B.i₀ ρ L := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hy
    refine ⟨fun j hj => ?_, by linarith, by linarith⟩
    have := h1 j hj
    linarith
  have hKmid : B.ψ '' K ⊆ B.ψ '' midBox B.i₀ ρ L := image_mono (hKin.trans hinmid)
  have hf₁eq : ∀ x, x ∉ B.ψ '' midBox B.i₀ ρ L → f₁ x = f x :=
    fun x hx => hf₁K x (fun h => hx (hKmid h))
  have hqlev : c + L / 4 < f₁ q ∧ f₁ q < c + 3 * L / 4 := by
    obtain ⟨y, hy, rfl⟩ := hqK
    exact hlevK y hy
  have hrlev : c + L / 4 < f₁ r ∧ f₁ r < c + 3 * L / 4 := by
    obtain ⟨y, hy, rfl⟩ := hrK
    exact hlevK y hy
  set ε₅ : ℝ := min ε ((f₁ r - f₁ q) / 4) with hε₅def
  have hε₅pos : 0 < ε₅ := lt_min hε (by linarith)
  have hε₅le : ε₅ ≤ ε := min_le_left _ _
  have hε₅gap : ε₅ ≤ (f₁ r - f₁ q) / 4 := min_le_right _ _
  obtain ⟨D₁, hold, hVeq, hnew, ε', hε'pos, hε'le, hε'⟩ :=
    exists_gradientLike_insert hf D hcrit B hL hρ hab hf₁ hK hKin hf₁K hqK hrK
      (fun h => by subst h; exact lt_irrefl _ hqr) hlevK hcrit₁ hε₅pos
  have hqmem : q ∈ insert q (insert r crit) := Finset.mem_insert_self q _
  have hkq : (D₁.chart q hqmem).k = 2 := by
    rw [← (D₁.chart q hqmem).hkidx, hidxq]
  have hεq := hε' q hqmem (Or.inl rfl)
  have hchartq := (hnew q hqmem (Or.inl rfl)).1
  have hothers : ∀ x (hx : x ∈ insert q (insert r crit)), x ≠ q →
      ∀ y ∈ D₁.closedSmallBall x hx, y ∈ B.ψ '' boxSet B.i₀ ρ L → f₁ q - ε' < f₁ y := by
    intro x hx hxq y hy hyB
    rcases Finset.mem_insert.1 hx with h | hx1
    · exact absurd h hxq
    rcases Finset.mem_insert.1 hx1 with hxr | hx'
    · subst hxr
      have hy' := D₁.closedSmallBall_subset_image_ball x hx hy
      have habs := (hnew x hx (Or.inr rfl)).2 y hy'
      have := (abs_lt.1 habs).1
      linarith
    · exfalso
      obtain ⟨hχ, -, -, -, hr0, -⟩ := hold x hx'
      have hy2 : y ∈ D.closedSmallBall x hx' := by
        simp only [GradientLikeStrip.closedSmallBall] at hy ⊢
        rw [hχ, hr0] at hy
        exact hy
      obtain ⟨z, hz, rfl⟩ := hyB
      exact B.avoid z hz x hx' (D.closedSmallBall_subset_image_ball x hx' hy2)
  have hf₁mid : ∀ y ∈ midBox B.i₀ ρ L, c < f₁ (B.ψ y) := by
    intro y hy
    by_cases hyK : B.ψ y ∈ B.ψ '' K
    · obtain ⟨y', hy', hyy⟩ := hyK
      have := (hlevK y' hy').1
      rw [hyy] at this
      linarith
    · have hyB : y ∈ boxSet B.i₀ ρ L := by
        obtain ⟨h1, h2, h3⟩ := hy
        exact ⟨fun j hj => (h1 j hj).trans (by linarith), by linarith, by linarith⟩
      rw [hf₁K _ hyK, B.level y hyB]
      linarith [hy.2.1]
  have hD6 := leftLoop_mem_bottomFace hf₁ D D₁ B hL hρ hab hf₁eq hf₁mid
    (fun x hx => hVeq x hx) hqmem hε'pos hεq hchartq hothers
  have hfree : ∀ y ∈ (D₁.chart q hqmem).leftModelSphere ε',
      ∀ s ∈ Icc 0 (f₁ q - ε' - c), ∀ x (hx : x ∈ insert q (insert r crit)),
        D₁.flow s ((D₁.chart q hqmem).χ y) ∉ D₁.closedSmallBall x hx :=
    fun y hy => (hD6 y hy).1
  have hcirc : ∀ t : ℝ, (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
    intro t h
    have h0 := congrFun h (Fin.cast hkq.symm 0)
    have h1 := congrFun h (Fin.cast hkq.symm 1)
    simp only [Fin.cast_cast, Fin.cast_eq_self, Pi.zero_apply, circ2] at h0 h1
    change Real.cos (2 * Real.pi * t) = 0 at h0
    change Real.sin (2 * Real.pi * t) = 0 at h1
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h0, h1] at this
    norm_num at this
  have hRq : 2 * ε' ≤ (D₁.chart q hqmem).R ^ 2 := by
    have h1 := (D₁.hrm q hqmem).2
    have h2 := D₁.rm_pos q hqmem
    have h3 : D₁.rm q hqmem ^ 2 ≤ (D₁.chart q hqmem).R ^ 2 := pow_le_pow_left₀ h2.le h1 2
    nlinarith [hεq.2]
  have hc : a ≤ c := by linarith [hab.1]
  have hcq : c ≤ f₁ q - ε' := by linarith [hqlev.1]
  refine ⟨f₁, q, r, D₁, hmod, hf₁, fun x hx => ⟨hf₁eq x hx, hVeq x hx⟩, hcrit₁, hKmid hqK,
    hKmid hrK, hqlev.1, hqr, hrlev.2, hidxq, hidxr, hidxold, hold, ?_, hkq, ε', hε'pos,
    hε'le.trans hε₅le, by linarith, hεq.1, hεq.2, hfree, ?_, ?_⟩
  · intro x hx hxqr
    obtain ⟨h1, h2⟩ := hnew x hx hxqr
    exact ⟨h1, fun y hy => (h2 y hy).trans_le hε₅le⟩
  · intro t
    exact (hD6 _ ((D₁.chart q hqmem).sphereParam_mem_leftModelSphere hε'pos.le (hcirc t))).2
  · exact isLevelLoop_leftLoop hf₁.smooth D₁ hqmem hkq hε'pos hRq hc hcq hfree

theorem isLevelHomotopy_face (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {x₀ : M} {c L ρ : ℝ} (B : FlowBox D x₀ c L ρ)
    (hL : 0 < L) (hρ : 0 < ρ) {c₀ : ℝ} (hac₀ : a ≤ c₀) (hc₀c : c₀ ≤ c) (hcb : c ≤ b)
    (hcollar : ∀ y, f y ∈ Icc c₀ c → ∀ x (hx : x ∈ crit), y ∉ D.closedSmallBall x hx)
    {β : ℝ → M} (hβ : Continuous β) (hβper : Periodic β 1)
    (hβface : ∀ θ, β θ ∈ B.ψ '' bottomFace B.i₀ ρ) :
    isLevelHomotopy f c₀
      (fun θ s => D.flow (c - c₀)
        (B.ψ (((Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ)) • B.ψ.symm (β θ))))
      (fun _ => D.flow (c - c₀) x₀) (fun θ => D.flow (c - c₀) (β θ)) := by
  have hbox : ∀ y ∈ bottomFace B.i₀ ρ, y ∈ boxSet B.i₀ ρ L := by
    intro y hy
    refine ⟨hy.1, ?_, ?_⟩ <;> rw [hy.2] <;> linarith
  have hsymm : ∀ θ, B.ψ.symm (β θ) ∈ bottomFace B.i₀ ρ := by
    intro θ
    obtain ⟨y, hy, hyβ⟩ := hβface θ
    rw [← hyβ, B.ψ.left_inv (B.box_subset (hbox y hy))]
    exact hy
  have htgt : ∀ θ, β θ ∈ B.ψ.target := by
    intro θ
    obtain ⟨y, hy, hyβ⟩ := hβface θ
    rw [← hyβ]
    exact B.ψ.map_source (B.box_subset (hbox y hy))
  have hsmul : ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 → ∀ y ∈ bottomFace B.i₀ ρ,
      t • y ∈ bottomFace B.i₀ ρ := by
    intro t ht y hy
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
      have h1 := hy.1 j hj
      have h2 := abs_nonneg (y j)
      nlinarith [ht.2]
    · rw [Pi.smul_apply, smul_eq_mul, hy.2, mul_zero]
  have hmem : ∀ θ s, ((Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ)) • B.ψ.symm (β θ) ∈
      bottomFace B.i₀ ρ := fun θ s =>
    hsmul _ (Set.projIcc (0 : ℝ) 1 zero_le_one s).2 _ (hsymm θ)
  have hflow := (GradientLikeStrip.flow_level_transport (D := D) hf hac₀ hc₀c hcb
    (fun y hy p hp hyp => hcollar y hy p hp (D.smallBall_subset_closedSmallBall p hp hyp))).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hβs : Continuous (fun θ => B.ψ.symm (β θ)) :=
      B.ψ.continuousOn_symm.comp_continuous hβ htgt
    have hin : Continuous (fun p : ℝ × ℝ =>
        ((Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) • B.ψ.symm (β p.1)) :=
      ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd).smul
        (hβs.comp continuous_fst)
    have hψ : Continuous (fun p : ℝ × ℝ =>
        B.ψ (((Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) • B.ψ.symm (β p.1))) :=
      B.ψ.continuousOn.comp_continuous hin
        (fun p => B.box_subset (hbox _ (hmem p.1 p.2)))
    exact (D.continuous_flow (c - c₀)).comp hψ
  · intro θ s
    simp only [hβper θ]
  · intro θ s
    refine (hflow _ ?_).1
    exact B.level _ (hbox _ (hmem θ s)) ▸ by rw [(hmem θ s).2, add_zero]
  · intro θ
    simp only [Set.projIcc_left, zero_smul, B.map_zero]
  · intro θ
    simp only [Set.projIcc_right, one_smul, B.ψ.right_inv (htgt θ)]

theorem exists_levelAnnulus (h5 : 5 ≤ n) (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {c c' : ℝ} (hcc' : c < c') (hab : a < c ∧ c' < b)
    (hband : ∀ y, f y ∈ Icc c c' → ∀ p (hp : p ∈ crit), y ∉ D.closedSmallBall p hp)
    {γ β : ℝ → M} (hγ : isLevelLoop I f c γ) (hβ : isLevelLoop I f c' β) {Hm : ℝ → ℝ → M}
    (hH : isLevelHomotopy f c Hm γ (fun θ => D.flow (c' - c) (β θ))) :
    ∃ A : ℝ → ℝ → M, isLevelAnnulus D c c' A γ β := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hΔ : 0 < c' - c := sub_pos.2 hcc'
  obtain ⟨hγper, hγs, hγimm, hγinj, hγlev⟩ := hγ
  obtain ⟨hβper, hβs, hβimm, hβinj, hβlev⟩ := hβ
  obtain ⟨hHc, hHper, hHlev, hH0, hH1⟩ := hH
  have hfl : ∀ (t : ℝ) (z : M), MDifferentiableAt I I (D.flow t) z :=
    fun t z => (D.contMDiff_flow t z).mdifferentiableAt (by simp)
  have hflinj : ∀ (t : ℝ) (z : M), Function.Injective (mfderiv I I (D.flow t) z) := by
    intro t z
    have hid : (D.flow (-t) ∘ D.flow t) = id := funext fun w => D.flow_neg_flow w t
    have hc := mfderiv_comp z (hfl (-t) (D.flow t z)) (hfl t z)
    rw [hid, mfderiv_id] at hc
    intro u₁ u₂ hu
    have e1 : u₁ = mfderiv I I (D.flow (-t)) (D.flow t z) (mfderiv I I (D.flow t) z u₁) :=
      DFunLike.congr_fun hc u₁
    have e2 : u₂ = mfderiv I I (D.flow (-t)) (D.flow t z) (mfderiv I I (D.flow t) z u₂) :=
      DFunLike.congr_fun hc u₂
    exact e1.trans ((congrArg (mfderiv I I (D.flow (-t)) (D.flow t z)) hu).trans e2.symm)
  have hδs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun θ => D.flow (c' - c) (β θ)) :=
    (D.contMDiff_flow (c' - c)).comp hβs
  have hδimm : ∀ θ, mfderiv 𝓘(ℝ, ℝ) I (fun θ => D.flow (c' - c) (β θ)) θ (1 : ℝ) ≠ 0 := by
    intro θ
    have hβd : MDifferentiableAt 𝓘(ℝ, ℝ) I β θ := (hβs θ).mdifferentiableAt (by simp)
    have := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) θ (hfl (c' - c) (β θ)) hβd (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I (D.flow (c' - c) ∘ β) θ (1 : ℝ) ≠ 0
    rw [this]
    intro h0
    exact hβimm θ (hflinj (c' - c) (β θ) (h0.trans (map_zero _).symm))
  have hδinj : ∀ θ θ', D.flow (c' - c) (β θ) = D.flow (c' - c) (β θ') → ∃ k : ℤ, θ' = θ + k :=
    fun θ θ' h => hβinj θ θ' (D.flow_injective _ h)
  obtain ⟨σ, hσc, hσ0, hσ1⟩ : ∃ σ : ℝ → ℝ, Continuous σ ∧ (∀ s, s ≤ 1 / 4 → σ s = 0) ∧
      ∀ s, 3 / 4 ≤ s → σ s = 1 := by
    refine ⟨fun s => max 0 (min 1 (2 * s - 1 / 2)), by fun_prop, ?_, ?_⟩
    · intro s hs
      simp only
      rw [max_eq_left]
      exact (min_le_right _ _).trans (by linarith)
    · intro s hs
      simp only
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  set Hs : ℝ → ℝ → M := fun θ s => Hm θ (σ s) with hHsdef
  have hHsc : Continuous (uncurry Hs) := by
    have : uncurry Hs = uncurry Hm ∘ (fun z : ℝ × ℝ => (z.1, σ z.2)) := rfl
    rw [this]
    exact hHc.comp (continuous_fst.prodMk (hσc.comp continuous_snd))
  have hHsper : ∀ θ s, Hs (θ + 1) s = Hs θ s := fun θ s => hHper θ (σ s)
  have hHslev : ∀ θ s, f (Hs θ s) = c := fun θ s => hHlev θ (σ s)
  have hHs0 : ∀ θ s, s ≤ 1 / 4 → Hs θ s = γ θ := by
    intro θ s hs
    simp only [hHsdef, hσ0 s hs, hH0]
  have hHs1 : ∀ θ s, 3 / 4 ≤ s → Hs θ s = D.flow (c' - c) (β θ) := by
    intro θ s hs
    simp only [hHsdef, hσ1 s hs, hH1]
  have hcIoo : c ∈ Ioo a b := ⟨hab.1, hcc'.trans hab.2⟩
  have hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c := by
    intro x hx y hy hyc
    exact hband y (by rw [hyc]; exact ⟨le_rfl, hcc'.le⟩) x hx hy
  have hU1 : IsOpen ({z : ℝ × ℝ | z.2 < 1 / 4} ∪ {z | 3 / 4 < z.2}) :=
    (isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd)
  have hP1 : IsClosed ({z : ℝ × ℝ | z.2 ≤ 1 / 8} ∪ {z | 7 / 8 ≤ z.2}) :=
    (isClosed_le continuous_snd continuous_const).union
      (isClosed_le continuous_const continuous_snd)
  have hFU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry Hs) ({z : ℝ × ℝ | z.2 < 1 / 4} ∪ {z | 3 / 4 < z.2}) := by
    intro z hz
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases hz with hz | hz
    · have hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (fun w : ℝ × ℝ => γ w.1) :=
        hγs.comp (contDiff_fst.contMDiff)
      refine (hsm z).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hz] with w hw
      exact hHs0 w.1 w.2 (le_of_lt hw)
    · have hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (fun w : ℝ × ℝ => D.flow (c' - c) (β w.1)) :=
        hδs.comp (contDiff_fst.contMDiff)
      refine (hsm z).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with w hw
      exact hHs1 w.1 w.2 (le_of_lt hw)
  obtain ⟨F', hF's, hF'per, hF'lev, hF'P, -⟩ := exists_smooth_level_family hf D hcIoo hcU
    hHsc hHsper hHslev hU1 (fun θ s => Iff.rfl) hFU hP1 (fun θ s => Iff.rfl)
    (by
      rintro z (hz | hz)
      · exact Or.inl (show z.2 < 1 / 4 by have : z.2 ≤ 1 / 8 := hz; linarith)
      · exact Or.inr (show 3 / 4 < z.2 by have : 7 / 8 ≤ z.2 := hz; linarith))
    (by
      intro θ s hs
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
      rcases hs with hs | hs
      · exact Or.inl (show s ≤ 1 / 8 by linarith)
      · exact Or.inr (show 7 / 8 ≤ s by linarith))
    isOpen_univ (fun x => mem_univ _)
  have hF'0 : ∀ θ s, s ≤ 1 / 8 → F' θ s = γ θ := fun θ s hs =>
    (hF'P θ s (Or.inl hs)).trans (hHs0 θ s (by linarith))
  have hF'1 : ∀ θ s, 7 / 8 ≤ s → F' θ s = D.flow (c' - c) (β θ) := fun θ s hs =>
    (hF'P θ s (Or.inr hs)).trans (hHs1 θ s (by linarith))
  have hreg : ∀ x, f x = c → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hcrit
    have h1 : dfV I f D.V x = -1 := D.dfV_eq_neg_one_of_level ⟨hab.1.le, (hcc'.trans hab.2).le⟩
      (fun p hp y hy hyc => hcU p hp y (D.smallBall_subset_closedSmallBall p hp hy) hyc) hx
    have h2 : dfV I f D.V x = 0 := by
      unfold dfV
      unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hcrit
      rw [hcrit]
      simp
    linarith
  obtain ⟨h', hh's, hh'per, hh'lev, hh'P, -, hemb⟩ := exists_embedded_slices h5 hfs hreg hF's
    hF'per hF'lev (U := {z : ℝ × ℝ | z.2 < 1 / 8} ∪ {z | 7 / 8 < z.2})
    (P := {z : ℝ × ℝ | z.2 ≤ 1 / 16} ∪ {z | 15 / 16 ≤ z.2})
    ((isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd))
    (fun θ s => Iff.rfl)
    ((isClosed_le continuous_snd continuous_const).union
      (isClosed_le continuous_const continuous_snd))
    (fun θ s => Iff.rfl)
    (by
      rintro z (hz | hz)
      · exact Or.inl (show z.2 < 1 / 8 by have : z.2 ≤ 1 / 16 := hz; linarith)
      · exact Or.inr (show 7 / 8 < z.2 by have : 15 / 16 ≤ z.2 := hz; linarith))
    (by
      rintro z (hz | hz)
      · have : (fun θ => F' θ z.2) = γ := funext fun θ => hF'0 θ z.2 (le_of_lt hz)
        rw [this]
        exact hγimm z.1
      · have : (fun θ => F' θ z.2) = fun θ => D.flow (c' - c) (β θ) :=
          funext fun θ => hF'1 θ z.2 (le_of_lt hz)
        rw [this]
        exact hδimm z.1)
    (by
      rintro θ θ' s (hz | hz) (hz' | hz') he
      · rw [hF'0 θ s (le_of_lt hz), hF'0 θ' s (le_of_lt hz')] at he
        exact hγinj θ θ' he
      · simp only [mem_ofPred_eq] at hz hz'
        linarith
      · simp only [mem_ofPred_eq] at hz hz'
        linarith
      · rw [hF'1 θ s (le_of_lt hz), hF'1 θ' s (le_of_lt hz')] at he
        exact hδinj θ θ' he)
    isOpen_univ (fun x => mem_univ _)
  have hh'0 : ∀ θ s, s ≤ 1 / 16 → h' θ s = γ θ := fun θ s hs =>
    (hh'P θ s (Or.inl hs)).trans (hF'0 θ s (by linarith))
  have hh'1 : ∀ θ s, 15 / 16 ≤ s → h' θ s = D.flow (c' - c) (β θ) := fun θ s hs =>
    (hh'P θ s (Or.inr hs)).trans (hF'1 θ s (by linarith))
  have hU : ∀ y, f y ∈ Icc c c' → ∀ p hp, y ∉ D.smallBall p hp := fun y hy p hp hmem =>
    hband y hy p hp (D.smallBall_subset_closedSmallBall p hp hmem)
  have htr := (GradientLikeStrip.flow_level_transport (D := D) hfs hab.1.le hcc'.le hab.2.le hU).2
  refine ⟨fun θ s => D.flow (-(s * (c' - c))) (h' θ s), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hpair : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun z : ℝ × ℝ => (-(z.2 * (c' - c)), h' z.1 z.2)) :=
      ContMDiff.prodMk (by
        have : ContDiff ℝ ∞ (fun z : ℝ × ℝ => -(z.2 * (c' - c))) := by fun_prop
        exact this.contMDiff) hh's
    exact D.contMDiff_flow_joint.comp hpair
  · intro θ s
    simp only [hh'per]
  · intro θ s hs
    have := (htr (h' θ s) (hh'lev θ s)).2 (-(s * (c' - c)))
      ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩
    simp only
    rw [this]
    ring
  · intro θ θ' s hs s' hs' he
    have hl1 := (htr (h' θ s) (hh'lev θ s)).2 (-(s * (c' - c)))
      ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩
    have hl2 := (htr (h' θ' s') (hh'lev θ' s')).2 (-(s' * (c' - c)))
      ⟨by nlinarith [hs'.1, hs'.2], by nlinarith [hs'.1, hs'.2]⟩
    have hss : s = s' := by
      have := congrArg f he
      simp only at this
      rw [hl1, hl2] at this
      have h3 : (s - s') * (c' - c) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · linarith
    subst hss
    refine ⟨rfl, ?_⟩
    exact (hemb s hs).2 θ θ' (D.flow_injective _ he)
  · intro θ s hs
    have hsl : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun θ' => h' θ' s) θ := by
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun θ' : ℝ => (θ', s)) := by
        have : ContDiff ℝ ∞ (fun θ' : ℝ => (θ', s)) := by fun_prop
        exact this.contMDiff
      exact ((hh's.comp hι) θ).mdifferentiableAt (by simp)
    have := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) θ (hfl (-(s * (c' - c))) (h' θ s)) hsl (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I (D.flow (-(s * (c' - c))) ∘ fun θ' => h' θ' s) θ (1 : ℝ) ≠ 0
    rw [this]
    intro h0
    exact (hemb s hs).1 θ (hflinj _ (h' θ s) (h0.trans (map_zero _).symm))
  · refine ⟨1 / 16, by norm_num, ?_, ?_⟩
    · intro θ s hs
      simp only
      rw [hh'0 θ s hs.2]
    · intro θ s hs
      simp only
      rw [hh'1 θ s (by linarith [hs.1]), D.flow_flow]
      congr 1
      ring

theorem exists_local_param_retraction {A : ℝ → ℝ → M}
    (hA : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry A)) (hper : ∀ θ s, A (θ + 1) s = A θ s)
    (hinj : ∀ θ θ', ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, A θ s = A θ' s' →
      s = s' ∧ ∃ k : ℤ, θ' = θ + k)
    (hrank : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) : Fin n → ℝ),
        (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ) : Fin n → ℝ)])
    {θ₀ s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ U : Set M, IsOpen U ∧ A θ₀ s₀ ∈ U ∧ ∃ Θ : M → ℝ × ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ × ℝ) ∞ Θ U ∧
      ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ U → ∃ k : ℤ, Θ (A θ s) = (θ + k, s) := by
  classical
  have _hI : range I = univ := I.range_eq_univ
  set x₁ : M := A θ₀ s₀ with hx₁
  set φ := extChartAt I x₁ with hφ
  set p₀ : ℝ × ℝ := (θ₀, s₀) with hp₀
  have hAc : Continuous (uncurry A) := hA.continuous
  set O : Set (ℝ × ℝ) := uncurry A ⁻¹' (chartAt H x₁).source with hOdef
  have hO : IsOpen O := (chartAt H x₁).open_source.preimage hAc
  have hp₀O : p₀ ∈ O := mem_chart_source H x₁
  set α : ℝ × ℝ → (Fin n → ℝ) := fun p => φ (uncurry A p) with hαdef
  have hαO : ContDiffOn ℝ ∞ α O := by
    have := (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₁)).comp hA.contMDiffOn
      (fun p hp => hp)
    exact contMDiffOn_iff_contDiffOn.mp this
  set L : ℝ × ℝ →L[ℝ] (Fin n → ℝ) := fderiv ℝ α p₀ with hLdef
  have hαd : HasFDerivAt α L p₀ :=
    ((hαO.contDiffAt (hO.mem_nhds hp₀O)).differentiableAt (by simp)).hasFDerivAt
  have h1 : (mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s₀) θ₀ (1 : ℝ) : Fin n → ℝ) = L (1, 0) := by
    have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun θ' : ℝ => (θ', s₀)) :=
      contMDiff_iff_contDiff.mpr (contDiff_id.prodMk contDiff_const)
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun θ' => A θ' s₀) θ₀ :=
      (hA.comp hc).mdifferentiableAt (by simp)
    rw [hmd.mfderiv]
    have hg : HasFDerivAt (fun θ' : ℝ => α (θ', s₀))
        (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) θ₀ := by
      have : HasFDerivAt (fun θ' : ℝ => (θ', s₀)) (ContinuousLinearMap.inl ℝ ℝ ℝ) θ₀ :=
        (hasFDerivAt_id θ₀).prodMk (hasFDerivAt_const s₀ θ₀)
      exact hαd.comp θ₀ this
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, modelWithCornersSelf_coe,
      range_id, fderivWithin_univ]
    have e : (↑(extChartAt I (A θ₀ s₀)) ∘ (fun θ' => A θ' s₀) ∘ ↑(PartialEquiv.refl ℝ).symm) =
        fun θ' : ℝ => α (θ', s₀) := rfl
    rw [e, show (PartialEquiv.refl ℝ) θ₀ = θ₀ from rfl, hg.fderiv]
    rfl
  have h2 : (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ₀ s') s₀ (1 : ℝ) : Fin n → ℝ) = L (0, 1) := by
    have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s' : ℝ => (θ₀, s')) :=
      contMDiff_iff_contDiff.mpr (contDiff_const.prodMk contDiff_id)
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s' => A θ₀ s') s₀ :=
      (hA.comp hc).mdifferentiableAt (by simp)
    rw [hmd.mfderiv]
    have hg : HasFDerivAt (fun s' : ℝ => α (θ₀, s'))
        (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) s₀ := by
      have : HasFDerivAt (fun s' : ℝ => (θ₀, s')) (ContinuousLinearMap.inr ℝ ℝ ℝ) s₀ :=
        (hasFDerivAt_const θ₀ s₀).prodMk (hasFDerivAt_id s₀)
      exact hαd.comp s₀ this
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, modelWithCornersSelf_coe,
      range_id, fderivWithin_univ]
    have e : (↑(extChartAt I (A θ₀ s₀)) ∘ (fun s' => A θ₀ s') ∘ ↑(PartialEquiv.refl ℝ).symm) =
        fun s' : ℝ => α (θ₀, s') := rfl
    rw [e, show (PartialEquiv.refl ℝ) s₀ = s₀ from rfl, hg.fderiv]
    rfl
  have hLinj : LinearMap.ker (L : ℝ × ℝ →ₗ[ℝ] (Fin n → ℝ)) = ⊥ := by
    have hli : LinearIndependent ℝ ![L (1, 0), L (0, 1)] := by
      have := hrank θ₀ s₀ hs₀
      rw [h1, h2] at this
      exact this
    rw [LinearIndependent.pair_iff] at hli
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hv' : v.1 • L (1, 0) + v.2 • L (0, 1) = 0 := by
      rw [← L.map_smul, ← L.map_smul, ← L.map_add]
      simpa using hv
    obtain ⟨h₁, h₂⟩ := hli v.1 v.2 hv'
    exact Prod.ext h₁ h₂
  obtain ⟨Pl, hPl⟩ := LinearMap.exists_leftInverse_of_injective _ hLinj
  set P : (Fin n → ℝ) →L[ℝ] ℝ × ℝ := LinearMap.toContinuousLinearMap Pl with hPdef
  have hPL : P.comp L = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact LinearMap.congr_fun hPl v
  set F : ℝ × ℝ → ℝ × ℝ := fun p => P (α p) with hFdef
  have hFO : ContDiffOn ℝ ∞ F O := P.contDiff.comp_contDiffOn hαO
  have hFd : HasFDerivAt F (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p₀ := by
    rw [← hPL]
    exact P.hasFDerivAt.comp p₀ hαd
  have hFs : HasStrictFDerivAt F
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ)) p₀ := by
    have := (hFO.contDiffAt (hO.mem_nhds hp₀O)).hasStrictFDerivAt (by simp)
    rw [ContinuousLinearEquiv.coe_refl]
    rwa [hFd.fderiv] at this
  set h := hFs.toOpenPartialHomeomorph F with hhdef
  have hhcoe : (h : ℝ × ℝ → ℝ × ℝ) = F := hFs.toOpenPartialHomeomorph_coe
  have hp₀h : p₀ ∈ h.source := hFs.mem_toOpenPartialHomeomorph_source
  set N : Set (ℝ × ℝ) := h.source ∩ (O ∩ fderiv ℝ F ⁻¹'
    Set.range (ContinuousLinearEquiv.toContinuousLinearMap (R₁ := ℝ) (R₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (M₁ := ℝ × ℝ) (M₂ := ℝ × ℝ))) with hNdef
  have hN : IsOpen N :=
    h.open_source.inter ((hFO.continuousOn_fderiv_of_isOpen hO (by simp)).isOpen_inter_preimage
      hO ContinuousLinearEquiv.isOpen)
  have hp₀N : p₀ ∈ N :=
    ⟨hp₀h, hp₀O, ⟨ContinuousLinearEquiv.refl ℝ (ℝ × ℝ), by rw [hFd.fderiv]; rfl⟩⟩
  set B : Set (ℝ × ℝ) := Icc (θ₀ - 1 / 2) (θ₀ + 1 / 2) ×ˢ Icc (0 : ℝ) 1 with hBdef
  set K : Set M := uncurry A '' (B \ N) with hKdef
  have hK : IsClosed K :=
    (((isCompact_Icc.prod isCompact_Icc).diff hN).image hAc).isClosed
  have hx₁K : x₁ ∉ K := by
    rintro ⟨⟨θ, s⟩, ⟨⟨hθ, hs⟩, hnN⟩, hq⟩
    obtain ⟨hss, m, hm⟩ := hinj θ₀ θ s₀ hs₀ s hs hq.symm
    have hm0 : m = 0 := by
      have hmr : |(m : ℝ)| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hθ.1, hθ.2]
      have : |m| < 1 := by exact_mod_cast hmr
      rw [abs_lt] at this
      omega
    subst hm0
    apply hnN
    have : ((θ, s) : ℝ × ℝ) = p₀ := by
      rw [hp₀, hm, ← hss]
      simp
    rw [this]
    exact hp₀N
  set U : Set M := ((chartAt H x₁).source ∩ φ ⁻¹' (P ⁻¹' (h.target ∩ h.symm ⁻¹' N))) ∩ Kᶜ
    with hUdef
  have hU : IsOpen U := by
    refine IsOpen.inter ?_ hK.isOpen_compl
    have hc : ContinuousOn φ (chartAt H x₁).source := by
      rw [← extChartAt_source I x₁]
      exact continuousOn_extChartAt x₁
    exact hc.isOpen_inter_preimage (chartAt H x₁).open_source
      (P.continuous.isOpen_preimage _ (h.isOpen_inter_preimage_symm hN))
  have hx₁U : x₁ ∈ U := by
    have e : P (φ x₁) = h p₀ := by rw [hhcoe]; rfl
    refine ⟨⟨mem_chart_source H x₁, ?_, ?_⟩, hx₁K⟩
    · show P (φ x₁) ∈ h.target
      rw [e]
      exact h.map_source hp₀h
    · change h.symm (P (φ x₁)) ∈ N
      rw [e, h.left_inv hp₀h]
      exact hp₀N
  refine ⟨U, hU, hx₁U, fun x => h.symm (P (φ x)), ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨hxs, hxt, hxN⟩, -⟩ := hx
    apply ContMDiffAt.contMDiffWithinAt
    have hPφ : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => P (φ x)) x := by
      have := P.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₁))
      exact this.contMDiffAt ((chartAt H x₁).open_source.mem_nhds hxs)
    have hsym : ContDiffAt ℝ ∞ h.symm (P (φ x)) := by
      obtain ⟨hsN, hsO, e, he⟩ := hxN
      have hFc : ContDiffAt ℝ ∞ F (h.symm (P (φ x))) := hFO.contDiffAt (hO.mem_nhds hsO)
      have hFd' : HasFDerivAt h (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) (h.symm (P (φ x))) := by
        rw [hhcoe]
        rw [he]
        exact (hFc.differentiableAt (by simp)).hasFDerivAt
      exact h.contDiffAt_symm hxt hFd' (by rw [hhcoe]; exact hFc)
    exact (contMDiffAt_iff_contDiffAt.mpr hsym).comp x hPφ
  · intro θ s hs hU'
    refine ⟨round (θ₀ - θ), ?_⟩
    have hk := abs_sub_round (θ₀ - θ)
    rw [abs_le] at hk
    have hAk : A (θ + round (θ₀ - θ)) s = A θ s := by
      have hp : Function.Periodic (fun t => A t s) 1 := fun t => hper t s
      simpa using hp.int_mul (round (θ₀ - θ)) θ
    have hq : ((θ + round (θ₀ - θ), s) : ℝ × ℝ) ∈ N := by
      by_contra hnN
      apply hU'.2
      refine ⟨(θ + round (θ₀ - θ), s), ⟨⟨⟨?_, ?_⟩, hs⟩, hnN⟩, hAk⟩
      · linarith [hk.1, hk.2]
      · linarith [hk.1, hk.2]
    change h.symm (P (φ (A θ s))) = (θ + round (θ₀ - θ), s)
    rw [← hAk]
    have e : P (φ (A (θ + round (θ₀ - θ)) s)) = h (θ + round (θ₀ - θ), s) := by
      rw [hhcoe]; rfl
    rw [e, h.left_inv hq.1]

theorem exists_local_extension_along_annulus {A : ℝ → ℝ → M}
    (hA : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry A)) (hper : ∀ θ s, A (θ + 1) s = A θ s)
    (hinj : ∀ θ θ', ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, A θ s = A θ' s' →
      s = s' ∧ ∃ k : ℤ, θ' = θ + k)
    (hrank : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) : Fin n → ℝ),
        (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ) : Fin n → ℝ)])
    {W₀ : ℝ → ℝ → (Fin n → ℝ)}
    (hW₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun z : ℝ × ℝ => (⟨A z.1 z.2, W₀ z.1 z.2⟩ : TangentBundle I M)))
    (hW₀per : ∀ θ s, W₀ (θ + 1) s = W₀ θ s) {θ₀ s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ U : Set M, IsOpen U ∧ A θ₀ s₀ ∈ U ∧ ∃ W : (x : M) → TangentSpace I x,
      ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle I M)) U ∧
      ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ U → W (A θ s) = W₀ θ s := by
  obtain ⟨U, hUo, hxU, Θ, hΘ, hΘA⟩ :=
    exists_local_param_retraction (I := I) hA hper hinj hrank (θ₀ := θ₀) hs₀
  have hAk : ∀ (k : ℤ) θ s, A (θ + k) s = A θ s := by
    intro k θ s
    have hP : Function.Periodic (fun θ' => A θ' s) 1 := fun θ' => hper θ' s
    simpa using (hP.int_mul k) θ
  have hWk : ∀ (k : ℤ) θ s, W₀ (θ + k) s = W₀ θ s := by
    intro k θ s
    have hP : Function.Periodic (fun θ' => W₀ θ' s) 1 := fun θ' => hW₀per θ' s
    simpa using (hP.int_mul k) θ
  set x₁ : M := A θ₀ s₀ with hx₁
  let e := trivializationAt (Fin n → ℝ) (TangentSpace I) x₁
  let F : ℝ × ℝ → TangentBundle I M := fun z => ⟨A z.1 z.2, W₀ z.1 z.2⟩
  have hF : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ F := hW₀
  have hFΘ : ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => F (Θ x)) U :=
    hF.comp_contMDiffOn hΘ
  have hAΘc : ContinuousOn (fun x => A (Θ x).1 (Θ x).2) U :=
    hA.continuous.comp_continuousOn hΘ.continuousOn
  set U' : Set M := U ∩ e.baseSet ∩ ((fun x => A (Θ x).1 (Θ x).2) ⁻¹' e.baseSet) with hU'
  have hU'o : IsOpen U' := by
    have h1 := hAΘc.isOpen_inter_preimage hUo e.open_baseSet
    have : U' = (U ∩ (fun x => A (Θ x).1 (Θ x).2) ⁻¹' e.baseSet) ∩ e.baseSet := by
      rw [hU']; ext x; simp only [mem_inter_iff, mem_preimage]; tauto
    rw [this]; exact h1.inter e.open_baseSet
  have hx₁b : x₁ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₁
  have hx₁U' : x₁ ∈ U' := by
    refine ⟨⟨hxU, hx₁b⟩, ?_⟩
    obtain ⟨k, hk⟩ := hΘA θ₀ s₀ hs₀ hxU
    simp only [mem_preimage]
    rw [hk]
    simp only
    rw [hAk]
    exact hx₁b
  let g : M → (Fin n → ℝ) := fun x => (e (F (Θ x))).2
  have hg : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ g U' := by
    have hmaps : MapsTo (fun x => F (Θ x)) U' e.source := by
      intro x hx
      rw [e.mem_source]
      exact hx.2
    exact ((e.contMDiffOn_iff hmaps).1 (hFΘ.mono (fun x hx => hx.1.1))).2
  refine ⟨U', hU'o, hx₁U', fun x => e.symm x (g x), ?_, ?_⟩
  · rw [e.contMDiffOn_section_iff hU'o (fun x hx => hx.1.2)]
    refine hg.congr ?_
    intro x hx
    rw [e.apply_mk_symm hx.1.2]
  · intro θ s hs hmem
    have hb : A θ s ∈ e.baseSet := hmem.1.2
    obtain ⟨k, hk⟩ := hΘA θ s hs hmem.1.1
    have hFeq : F (Θ (A θ s)) = ⟨A θ s, W₀ θ s⟩ := by
      simp only [F, hk, hWk]
      rw [hAk]
    change e.symm (A θ s) (e (F (Θ (A θ s)))).2 = W₀ θ s
    rw [hFeq]
    exact e.symm_apply_apply_mk hb (W₀ θ s)

theorem exists_extension_along_annulus [SigmaCompactSpace M] {A : ℝ → ℝ → M}
    (hA : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry A)) (hper : ∀ θ s, A (θ + 1) s = A θ s)
    (hinj : ∀ θ θ', ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, A θ s = A θ' s' →
      s = s' ∧ ∃ k : ℤ, θ' = θ + k)
    (hrank : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) : Fin n → ℝ),
        (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ) : Fin n → ℝ)])
    {W₀ : ℝ → ℝ → (Fin n → ℝ)}
    (hW₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun z : ℝ × ℝ => (⟨A z.1 z.2, W₀ z.1 z.2⟩ : TangentBundle I M)))
    (hW₀per : ∀ θ s, W₀ (θ + 1) s = W₀ θ s) {O : Set M} (hO : IsOpen O)
    (hAO : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ O) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport W) ∧ tsupport W ⊆ O ∧ ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, W (A θ s) = W₀ θ s := by
  classical
  let K : Set M := uncurry A '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image hA.continuous
  have hKclosed : IsClosed K := hKc.isClosed
  have hAK : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ K := by
    intro θ s hs
    have hperθ : Function.Periodic (fun θ' => A θ' s) 1 := fun θ' => hper θ' s
    have hfr : A (Int.fract θ) s = A θ s := by
      have h1 := hperθ.sub_int_mul_eq (x := θ) ⌊θ⌋
      rw [mul_one] at h1
      exact h1
    refine ⟨(Int.fract θ, s), ⟨⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩, hs⟩, ?_⟩
    simpa [uncurry] using hfr
  have hKO : K ⊆ O := by
    rintro _ ⟨⟨θ, s⟩, ⟨_, hs⟩, rfl⟩
    exact hAO θ s hs
  have hpts : ∀ x : K, ∃ U : Set M, x.1 ∈ U ∧ IsOpen U ∧ ∃ W : (x : M) → TangentSpace I x,
      ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun y : M => (⟨y, W y⟩ : TangentBundle I M)) U ∧
      ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ U → W (A θ s) = W₀ θ s := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨θ₀, s₀⟩, ⟨_, hs₀⟩, rfl⟩ := hx
    obtain ⟨U, hUo, hxU, W, hW, hWA⟩ :=
      exists_local_extension_along_annulus (θ₀ := θ₀) hA hper hinj hrank hW₀ hW₀per hs₀
    exact ⟨U, hxU, hUo, W, hW, hWA⟩
  choose U hUmem hUopen W hWsec hWA using hpts
  have _ : LocallyCompactSpace H := I.locallyCompactSpace
  have _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hKc hO hKO
    with ⟨W₁, hW₁open, hKW₁, hW₁cl, hW₁compact⟩
  let U' : K → Set M := fun x => U x ∩ W₁
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₁ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₁open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → TangentSpace I x :=
    fun y => ∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)
  have hρzero : ∀ (x : K) (y : M), y ∉ U' x → ρ x y = 0 := by
    intro x y hyU
    have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
    exact image_eq_zero_of_notMem_tsupport hts'
  have hfinSuppρ : ∀ y : M, Function.HasFiniteSupport (fun x : K => ρ x y) := by
    intro y
    have hlf : LocallyFinite (fun x : K => {z : M | ρ x z ≠ 0}) := ρ.locallyFinite
    rcases hlf y with ⟨N, hN, hfinN⟩
    have hsub : (Function.support fun x : K => ρ x y) ⊆
        {x : K | ((fun x : K => {z : M | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
      intro x hx
      rw [Function.support] at hx
      exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
    exact Set.Finite.subset hfinN hsub
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun y : M => (⟨y, ρ x y • W x y⟩ : TangentBundle I M)) := by
      intro x
      have hcoerce : (ρ x : M → ℝ) = (ρ x).1 := rfl
      have hρOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ x : M → ℝ) (U' x) := by
        have hc' : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ρ x : M → ℝ) Set.univ := by
          simpa [hcoerce] using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact (ContMDiffOn.smul_section_of_tsupport (u := U' x) hρOn (hU'open x) (hρsub x)
        ((hWsec x).mono (by intro y hy; exact hy.1)))
    have hfin : LocallyFinite (fun x : K => {y : M | ρ x y • W x y ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (ContMDiff.finsum_section_of_locallyFinite hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support V → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support V ⊆ W₁ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport V ⊆ closure W₁ := closure_mono hsupp₀
    exact hW₁compact.of_isClosed_subset (isClosed_tsupport V) hts
  · have hsupp₀ : Function.support V ⊆ W₁ := by
      intro y hy
      by_contra hyW
      apply hy
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        rw [hρzero x y (fun h => hyW h.2), zero_smul]
      exact finsum_eq_zero_of_forall_eq_zero hall
    exact (closure_mono hsupp₀).trans hW₁cl
  · intro θ s hs
    have hy : A θ s ∈ K := hAK θ s hs
    have hterm : ∀ x : K, (ρ x (A θ s) : ℝ) • W x (A θ s) =
        (ρ x (A θ s) : ℝ) • (show TangentSpace I (A θ s) from W₀ θ s) := by
      intro x
      by_cases hyU : A θ s ∈ U' x
      · have h2 : W x (A θ s) = (show TangentSpace I (A θ s) from W₀ θ s) :=
          hWA x θ s hs hyU.1
        rw [h2]
      · rw [hρzero x _ hyU, zero_smul, zero_smul]
    have hs1 : (∑ᶠ x : K, ρ x (A θ s)) = 1 := ρ.sum_eq_one hy
    change (∑ᶠ x : K, (ρ x (A θ s) : ℝ) • W x (A θ s)) = W₀ θ s
    rw [finsum_congr hterm, ← finsum_smul' (hfinSuppρ (A θ s)), hs1, one_smul]

theorem exists_annulus_velocity (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {c c' : ℝ} (hcc' : c < c') (hab : a < c ∧ c' < b)
    (hband : ∀ y, f y ∈ Icc c c' → ∀ p (hp : p ∈ crit),
      y ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')
    {A : ℝ → ℝ → M} {γ β : ℝ → M} (hA : isLevelAnnulus D c c' A γ β) :
    ∃ W₀ : ℝ → ℝ → (Fin n → ℝ),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun z : ℝ × ℝ => (⟨A z.1 z.2, W₀ z.1 z.2⟩ : TangentBundle I M)) ∧
      (∀ θ s, W₀ (θ + 1) s = W₀ θ s) ∧
      (∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
        mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (W₀ θ s : TangentSpace I (A θ s)) = 0) ∧
      (∃ η > 0, ∀ θ s, s ∈ Icc 0 η ∪ Icc (1 - η) 1 → W₀ θ s = 0) ∧
      ∀ θ s, mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ) =
        (-(c' - c)) • ((show TangentSpace I (A θ s) from W₀ θ s) + D.V (A θ s)) := by
  obtain ⟨hAs, hper, hlev, -, -, η, hη, hleft, hright⟩ := hA
  set Δ : ℝ := c' - c with hΔdef
  have hΔ : Δ ≠ 0 := by rw [hΔdef]; linarith
  let Vf : M → (Fin n → ℝ) := fun x => D.V x
  let dA : ℝ → ℝ → (Fin n → ℝ) := fun θ s => mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ)
  let W₀ : ℝ → ℝ → (Fin n → ℝ) := fun θ s => (-Δ⁻¹) • dA θ s - Vf (A θ s)
  have hW₀dA : ∀ θ s, dA θ s = (-Δ) • (W₀ θ s + Vf (A θ s)) := by
    intro θ s
    simp only [W₀, sub_add_cancel, smul_smul]
    rw [neg_mul_neg, mul_inv_cancel₀ hΔ, one_smul]
  have huniq : ∀ (g₁ g₂ : ℝ → M) (S : Set ℝ) (s : ℝ)
      (g₁' : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (g₁ s))
      (g₂' : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (g₂ s)),
      UniqueDiffWithinAt ℝ S s → s ∈ S → (∀ x ∈ S, g₁ x = g₂ x) →
      HasMFDerivAt 𝓘(ℝ, ℝ) I g₁ s g₁' → HasMFDerivAt 𝓘(ℝ, ℝ) I g₂ s g₂' →
      (g₁' 1 : Fin n → ℝ) = g₂' 1 := by
    intro g₁ g₂ S s g₁' g₂' hU hs heq h₁ h₂
    have h2 := (h₂.hasMFDerivWithinAt (s := S)).congr_mono (f₁ := g₁) heq (heq s hs) subset_rfl
    have := hU.uniqueMDiffWithinAt.eq h₁.hasMFDerivWithinAt h2
    rw [this]
    rfl
  have huniqR : ∀ (g₁ g₂ : ℝ → ℝ) (S : Set ℝ) (s : ℝ)
      (g₁' : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (g₁ s))
      (g₂' : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (g₂ s)),
      UniqueDiffWithinAt ℝ S s → s ∈ S → (∀ x ∈ S, g₁ x = g₂ x) →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g₁ s g₁' → HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g₂ s g₂' →
      (g₁' 1 : ℝ) = g₂' 1 := by
    intro g₁ g₂ S s g₁' g₂' hU hs heq h₁ h₂
    have h2 := (h₂.hasMFDerivWithinAt (s := S)).congr_mono (f₁ := g₁) heq (heq s hs) subset_rfl
    have := hU.uniqueMDiffWithinAt.eq h₁.hasMFDerivWithinAt h2
    rw [this]
    rfl
  have hsl : ∀ θ, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s' => A θ s') := fun θ =>
    show ContMDiff 𝓘(ℝ, ℝ) I ∞ (uncurry A ∘ fun s' : ℝ => (θ, s')) from
      hAs.comp (contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id))
  have hsd : ∀ θ s, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s' => A θ s') s
      (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s) := fun θ s =>
    ((hsl θ).mdifferentiableAt (by simp)).hasMFDerivAt
  have hend : ∀ θ s, s ∈ Icc 0 η ∪ Icc (1 - η) 1 → dA θ s = (-Δ) • Vf (A θ s) := by
    intro θ s hs
    rcases hs with hs | hs
    · have hIC := (D.isMIntegralCurve_flow (γ θ)).comp_mul (-Δ) s
      have heq : ∀ x ∈ Icc 0 η, A θ x = ((fun t => D.flow t (γ θ)) ∘ fun x => x * -Δ) x := by
        intro x hx
        simp only [comp_apply, mul_neg]
        exact hleft θ x hx
      have := huniq _ _ _ s _ _ ((uniqueDiffOn_Icc hη) s hs) hs heq (hsd θ s) hIC
      refine this.trans ?_
      simp only [Pi.smul_apply, comp_apply, Vf]
      rw [mul_neg, ← hleft θ s hs]
      exact one_smul ℝ ((-Δ) • Vf (A θ s))
    · have hIC := (((D.isMIntegralCurve_flow (β θ)).comp_add Δ).comp_mul (-Δ)) s
      have heq : ∀ x ∈ Icc (1 - η) 1, A θ x =
          (((fun t => D.flow t (β θ)) ∘ fun x => x + Δ) ∘ fun x => x * -Δ) x := by
        intro x hx
        simp only [comp_apply]
        rw [hright θ x hx]
        congr 1
        ring
      have hU : UniqueDiffWithinAt ℝ (Icc (1 - η) 1) s :=
        (uniqueDiffOn_Icc (by linarith)) s hs
      have := huniq _ _ _ s _ _ hU hs heq (hsd θ s) hIC
      refine this.trans ?_
      simp only [Pi.smul_apply, comp_apply, Vf]
      rw [show D.flow (s * -Δ + Δ) (β θ) = A θ s from (heq s hs).symm]
      exact one_smul ℝ ((-Δ) • Vf (A θ s))
  refine ⟨W₀, ?_, ?_, ?_, ?_, fun θ s => hW₀dA θ s⟩
  · have hchain : ∀ θ s, mfderiv 𝓘(ℝ, ℝ × ℝ) I (uncurry A) (θ, s) ((0 : ℝ), (1 : ℝ)) = dA θ s := by
      intro θ s
      have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun s' : ℝ => (θ, s')) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : ℝ), (1 : ℝ))) :=
        ((hasDerivAt_const s θ).prodMk (hasDerivAt_id s)).hasFDerivAt.hasMFDerivAt
      have hU : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) I (uncurry A) (θ, s)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (uncurry A) (θ, s)) :=
        (hAs.mdifferentiableAt (by simp)).hasMFDerivAt
      have hc := (hU.comp s hg).mfderiv
      simp only [dA]
      rw [show (fun s' => A θ s') = uncurry A ∘ (fun s' : ℝ => (θ, s')) from rfl, hc]
      exact congrArg (mfderiv 𝓘(ℝ, ℝ × ℝ) I (uncurry A) (θ, s))
        (one_smul ℝ ((0 : ℝ), (1 : ℝ))).symm
    have hT : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun z : ℝ × ℝ => (⟨A z.1 z.2, dA z.1 z.2⟩ : TangentBundle I M)) := by
      have h1 := hAs.contMDiff_tangentMap (m := ∞) (by simp)
      have h2 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞
          (fun z : ℝ × ℝ => (⟨z, ((0 : ℝ), (1 : ℝ))⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
        let g : ℝ × ℝ → ModelProd (ℝ × ℝ) (ℝ × ℝ) := fun z => (z, ((0 : ℝ), (1 : ℝ)))
        have h0 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ).tangent ∞ g := by
          have hcd : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z, ((0 : ℝ), (1 : ℝ)))) :=
            contDiff_id.prodMk contDiff_const
          have h := contMDiff_iff_contDiff.2 hcd
          rw [modelWithCornersSelf_prod] at h
          exact h
        exact contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp h0
      refine (h1.comp h2).congr fun z => ?_
      obtain ⟨θ, s⟩ := z
      change (⟨A θ s, dA θ s⟩ : TangentBundle I M) =
        ⟨uncurry A (θ, s), mfderiv 𝓘(ℝ, ℝ × ℝ) I (uncurry A) (θ, s) ((0 : ℝ), (1 : ℝ))⟩
      rw [hchain]
      rfl
    have hVA : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun z : ℝ × ℝ => (⟨A z.1 z.2, D.V (A z.1 z.2)⟩ : TangentBundle I M)) :=
      D.smooth.comp hAs
    intro z₀
    have hT0 := Bundle.contMDiffAt_totalSpace.1 (hT z₀)
    have hV0 := Bundle.contMDiffAt_totalSpace.1 (hVA z₀)
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨hAs.contMDiffAt, ?_⟩
    have hev : ∀ᶠ z in 𝓝 z₀, A z.1 z.2 ∈
        (trivializationAt (Fin n → ℝ) (TangentSpace I) (A z₀.1 z₀.2)).baseSet :=
      hAs.continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt (Fin n → ℝ) (TangentSpace I) (A z₀.1 z₀.2)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ _))
    have hc : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ × ℝ => (-Δ⁻¹ : ℝ)) z₀ :=
      contMDiffAt_const
    refine ((hc.smul hT0.2).sub hV0.2).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    have hlin := (trivializationAt (Fin n → ℝ) (TangentSpace I) (A z₀.1 z₀.2)).linear ℝ hz
    change ((trivializationAt (Fin n → ℝ) (TangentSpace I) (A z₀.1 z₀.2))
      ⟨A z.1 z.2, (-Δ⁻¹) • (show TangentSpace I (A z.1 z.2) from dA z.1 z.2) -
        D.V (A z.1 z.2)⟩).2 = _
    rw [hlin.map_sub, hlin.map_smul]
    rfl
  · intro θ s
    have hfun : (fun s' => A (θ + 1) s') = fun s' => A θ s' := funext fun s' => hper θ s'
    simp only [W₀, dA]
    rw [hfun, hper]
  · intro θ s hs
    have hΔpos : 0 < Δ := by rw [hΔdef]; linarith
    have hfx : f (A θ s) = c + s * Δ := hlev θ s hs
    have hV1 : dfV I f D.V (A θ s) = -1 := by
      refine D.unit (A θ s) ?_ fun p hp hmem => hband (A θ s) ?_ p hp
        (D.smallBall_subset_image_ball p hp hmem)
      · rw [mem_preimage, hfx]
        constructor <;> nlinarith [hs.1, hs.2]
      · rw [hfx]
        constructor <;> nlinarith [hs.1, hs.2]
    have hfd : mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (dA θ s : TangentSpace I (A θ s)) = Δ := by
      have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ fun s' => A θ s') s
          ((mfderiv I 𝓘(ℝ, ℝ) f (A θ s)).comp (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s)) :=
        ((hf.smooth.mdifferentiableAt (by simp)).hasMFDerivAt).comp s (hsd θ s)
      have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => c + id x * Δ) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (1 * Δ)) :=
        (((hasDerivAt_id s).mul_const Δ).const_add c).hasFDerivAt.hasMFDerivAt
      have := huniqR _ _ (Icc 0 1) s _ _ ((uniqueDiffOn_Icc zero_lt_one) s hs) hs
        (fun x hx => hlev θ x hx) h1 h2
      refine this.trans ?_
      change (1 : ℝ) • (1 * Δ) = Δ
      simp
    have hV1' : mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (D.V (A θ s)) = -1 := hV1
    calc mfderiv I 𝓘(ℝ, ℝ) f (A θ s) ((-Δ⁻¹) • dA θ s - Vf (A θ s))
        = mfderiv I 𝓘(ℝ, ℝ) f (A θ s)
            ((-Δ⁻¹) • (show TangentSpace I (A θ s) from dA θ s) - D.V (A θ s)) := rfl
      _ = (-Δ⁻¹) • mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (dA θ s : TangentSpace I (A θ s)) -
            mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (D.V (A θ s)) := by rw [map_sub, map_smul]
      _ = 0 := by
        rw [hfd, hV1']
        change (-Δ⁻¹) * Δ - (-1) = (0 : ℝ)
        field_simp
        ring
  · refine ⟨η, hη, fun θ s hs => ?_⟩
    simp only [W₀]
    rw [hend θ s hs, smul_smul, neg_mul_neg, inv_mul_cancel₀ hΔ, one_smul, sub_self]

theorem exists_levelTangent_extension [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {c c' : ℝ} (hcc' : c < c') (hab : a < c ∧ c' < b)
    (hband : ∀ y, f y ∈ Icc c c' → ∀ p (hp : p ∈ crit),
      y ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')
    {A : ℝ → ℝ → M} {γ β : ℝ → M} (hA : isLevelAnnulus D c c' A γ β)
    {W₀ : ℝ → ℝ → (Fin n → ℝ)}
    (hW₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun z : ℝ × ℝ => (⟨A z.1 z.2, W₀ z.1 z.2⟩ : TangentBundle I M)))
    (hW₀per : ∀ θ s, W₀ (θ + 1) s = W₀ θ s)
    (hW₀f : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (W₀ θ s : TangentSpace I (A θ s)) = 0)
    (hW₀end : ∃ η > 0, ∀ θ s, s ∈ Icc 0 η ∪ Icc (1 - η) 1 → W₀ θ s = 0) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport W) ∧ tsupport W ⊆ f ⁻¹' Ioo c c' ∧
      (∀ p (hp : p ∈ crit),
        Disjoint (tsupport W) ((D.chart p hp).χ '' {y | morseNorm n y ≤ D.rm p hp})) ∧
      (∀ x, mfderiv I 𝓘(ℝ, ℝ) f x (W x) = 0) ∧
      ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, W (A θ s) = W₀ θ s := by
  obtain ⟨hAs, hAper, hAf, hAinj, hAθ, -⟩ := hA
  obtain ⟨η₁, hη₁, hW₀e⟩ := hW₀end
  have hΔ : 0 < c' - c := sub_pos.2 hcc'
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hrank : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) : Fin n → ℝ),
        (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ) : Fin n → ℝ)] := by
    intro θ s hs
    have hθd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ := by
      have h1 : ContMDiff 𝓘(ℝ, ℝ) I ∞ (uncurry A ∘ fun θ' => (θ', s)) :=
        hAs.comp (contDiff_id.prodMk contDiff_const).contMDiff
      exact h1.mdifferentiableAt (by simp)
    have hsd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s' => A θ s') s := by
      have h1 : ContMDiff 𝓘(ℝ, ℝ) I ∞ (uncurry A ∘ fun s' => (θ, s')) :=
        hAs.comp (contDiff_const.prodMk contDiff_id).contMDiff
      exact h1.mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (A θ s) := hfs.mdifferentiableAt (by simp)
    have h1 : mfderiv I 𝓘(ℝ, ℝ) f (A θ s)
        (mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ)) = 0 := by
      have hc := mfderiv_comp θ hfd hθd
      have hconst : (f ∘ fun θ' => A θ' s) = fun _ => c + s * (c' - c) :=
        funext fun θ' => hAf θ' s hs
      rw [hconst, mfderiv_const] at hc
      have := DFunLike.congr_fun hc (1 : ℝ)
      exact this.symm.trans rfl
    have h2 : mfderiv I 𝓘(ℝ, ℝ) f (A θ s)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') s (1 : ℝ)) = c' - c := by
      have hc := mfderiv_comp s hfd hsd
      have hgd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ fun s' => A θ s') s := hfd.comp s hsd
      have hgd' : DifferentiableAt ℝ (f ∘ fun s' => A θ s') s :=
        mdifferentiableAt_iff_differentiableAt.1 hgd
      rw [mfderiv_eq_fderiv] at hc
      have h3 : fderiv ℝ (f ∘ fun s' => A θ s') s 1 = c' - c := by
        rw [fderiv_apply_one_eq_deriv]
        refine UniqueDiffWithinAt.eq_deriv (Icc (0 : ℝ) 1) (uniqueDiffOn_Icc zero_lt_one s hs)
          hgd'.hasDerivAt.hasDerivWithinAt ?_
        have ha : HasDerivAt (fun s' : ℝ => c + s' * (c' - c)) (c' - c) s := by
          simpa using ((hasDerivAt_id s).mul_const (c' - c)).const_add c
        exact ha.hasDerivWithinAt.congr (fun s' hs' => hAf θ s' hs') (hAf θ s hs)
      exact (DFunLike.congr_fun hc (1 : ℝ)).symm.trans h3
    rw [LinearIndependent.pair_iff]
    intro t₁ t₂ ht
    have hL := congrArg (fun v => mfderiv I 𝓘(ℝ, ℝ) f (A θ s) v) ht
    simp only [map_add, map_smul, map_zero] at hL
    rw [h1, h2] at hL
    have ht2 : t₂ = 0 := by
      have h4 : t₂ * (c' - c) = 0 := by
        rw [smul_zero, zero_add] at hL
        exact hL
      rcases mul_eq_zero.1 h4 with h | h
      · exact h
      · exact absurd h hΔ.ne'
    refine ⟨?_, ht2⟩
    rw [ht2, zero_smul, add_zero] at ht
    rcases smul_eq_zero.1 ht with h | h
    · exact h
    · exact absurd h (hAθ θ s hs)
  let O : Set M := ⋂ q : {p // p ∈ crit},
    ((D.chart q.1 q.2).χ '' {y | morseNorm n y ≤ D.rm q.1 q.2})ᶜ
  have hOo : IsOpen O := isOpen_iInter_of_finite fun q =>
    ((D.chart q.1 q.2).isCompact_image_le (D.rm_lt_R' q.1 q.2)).isClosed.isOpen_compl
  have hAO : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, A θ s ∈ O := by
    intro θ s hs
    simp only [O, mem_iInter, mem_compl_iff]
    intro q hq
    have hlev : f (A θ s) ∈ Icc c c' := by
      rw [hAf θ s hs]
      constructor <;> nlinarith [hs.1, hs.2]
    refine hband (A θ s) hlev q.1 q.2 ?_
    exact image_mono (fun y hy => mem_ball_of_morseNorm_lt
      (lt_of_le_of_lt hy (D.rm_lt_R' q.1 q.2))) hq
  obtain ⟨Ŵ, hŴs, hŴc, hŴO, hŴA⟩ :=
    exists_extension_along_annulus hAs hAper hAinj hrank hW₀ hW₀per hOo hAO
  set η : ℝ := min η₁ (1 / 4) with hηdef
  have hη : 0 < η := lt_min hη₁ (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  let bκ : ContDiffBump ((c + c') / 2) :=
    ⟨(c' - c) / 2 - η * (c' - c), (c' - c) / 2 - η * (c' - c) / 2,
      by nlinarith, by nlinarith⟩
  let κ : ℝ → ℝ := bκ
  have hκs : ContDiff ℝ ∞ κ := bκ.contDiff
  have hκ1 : ∀ t ∈ Icc (c + η * (c' - c)) (c' - η * (c' - c)), κ t = 1 := by
    intro t ht
    apply bκ.one_of_mem_closedBall
    have hr : bκ.rIn = (c' - c) / 2 - η * (c' - c) := rfl
    rw [Real.closedBall_eq_Icc, hr]
    constructor <;> linarith [ht.1, ht.2]
  have hκsupp : tsupport κ ⊆ Ioo c c' := by
    intro t ht
    have ht' : t ∈ Metric.closedBall ((c + c') / 2) bκ.rOut := bκ.tsupport_eq ▸ ht
    rw [Real.closedBall_eq_Icc] at ht'
    have hr : bκ.rOut = (c' - c) / 2 - η * (c' - c) / 2 := rfl
    rw [hr] at ht'
    constructor <;> nlinarith [ht'.1, ht'.2]
  let W' : (x : M) → TangentSpace I x := fun x => κ (f x) • Ŵ x
  have hW's : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, W' x⟩ : TangentBundle I M)) :=
    (hκs.contMDiff.comp hfs).smul_section hŴs
  have hdf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (dfV I f W') := by
    have ht : ContMDiff I.tangent 𝓘(ℝ, ℝ).tangent ∞ (tangentMap I 𝓘(ℝ, ℝ) f) :=
      hfs.contMDiff_tangentMap (by simp)
    have hsnd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ModelProd ℝ ℝ => p.2) := by
      rw [← modelWithCornersSelf_prod]
      exact contDiff_snd.contMDiff
    have h1 := hsnd.comp
      (contMDiff_tangentBundleModelSpaceHomeomorph.comp (ht.comp hW's))
    refine h1.congr fun x => ?_
    rfl
  let W : (x : M) → TangentSpace I x := fun x => W' x + dfV I f W' x • D.V x
  have hWs : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle I M)) :=
    hW's.add_section (hdf.smul_section D.smooth)
  have hW'0 : ∀ x, W' x = 0 → W x = 0 := by
    intro x hx
    have hd : dfV I f W' x = 0 := by
      change NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ, ℝ) f x (W' x)) = 0
      rw [hx, map_zero, map_zero]
    change W' x + dfV I f W' x • D.V x = 0
    rw [hd, hx, zero_smul, add_zero]
  have hsuppW : support W ⊆ support Ŵ ∩ f ⁻¹' support κ := by
    intro x hx
    have hW'x : W' x ≠ 0 := fun h => hx (hW'0 x h)
    have := smul_ne_zero_iff.1 hW'x
    exact ⟨this.2, this.1⟩
  have htsW : tsupport W ⊆ tsupport Ŵ ∩ f ⁻¹' tsupport κ :=
    closure_minimal (hsuppW.trans (inter_subset_inter subset_closure (preimage_mono subset_closure)))
      ((isClosed_tsupport _).inter ((isClosed_tsupport _).preimage hfs.continuous))
  have hnotO : ∀ x ∈ O, ∀ p (hp : p ∈ crit),
      x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ D.rm p hp} := by
    intro x hx p hp
    simp only [O, mem_iInter, mem_compl_iff] at hx
    exact hx ⟨p, hp⟩
  refine ⟨W, hWs, hŴc.of_isClosed_subset (isClosed_tsupport _) (htsW.trans inter_subset_left),
    fun x hx => hκsupp (htsW hx).2, ?_, ?_, ?_⟩
  · intro p hp
    exact Set.disjoint_left.2 fun x hx hx' => hnotO x (hŴO (htsW hx).1) p hp hx'
  · intro x
    by_cases hx : W' x = 0
    · rw [hW'0 x hx, map_zero]
    have hW'x := smul_ne_zero_iff.1 hx
    have hfx : f x ∈ Ioo c c' := hκsupp (subset_closure hW'x.1)
    have hxO : x ∈ O := hŴO (subset_closure hW'x.2)
    have hu : NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ, ℝ) f x (D.V x)) = -1 := by
      refine D.unit x ⟨by linarith [hfx.1, hab.1], by linarith [hfx.2, hab.2]⟩ ?_
      intro p hp hmem
      refine hnotO x hxO p hp (image_mono (fun y hy => ?_) hmem)
      exact le_of_lt (lt_trans hy (D.r₀_lt_rm p hp))
    have hu' : mfderiv I 𝓘(ℝ, ℝ) f x (D.V x) = -1 := hu
    change mfderiv I 𝓘(ℝ, ℝ) f x (W' x + dfV I f W' x • D.V x) = 0
    rw [map_add, map_smul (mfderiv I 𝓘(ℝ, ℝ) f x) (dfV I f W' x) (D.V x), hu']
    have hr : ∀ r : ℝ, r + r • (-1 : ℝ) = 0 := fun r => by simp
    exact hr _
  · intro θ s hs
    have hW'A : W' (A θ s) = W₀ θ s := by
      change κ (f (A θ s)) • Ŵ (A θ s) = W₀ θ s
      rw [hŴA θ s hs]
      by_cases hmid : η ≤ s ∧ s ≤ 1 - η
      · rw [hκ1 _ ?_]
        · exact one_smul ℝ (W₀ θ s)
        rw [hAf θ s hs]
        constructor <;> nlinarith [hmid.1, hmid.2]
      · have hend : s ∈ Icc 0 η₁ ∪ Icc (1 - η₁) 1 := by
          rcases not_and_or.1 hmid with h | h
          · left; exact ⟨hs.1, by linarith [not_le.1 h]⟩
          · right; exact ⟨by linarith [not_le.1 h], hs.2⟩
        rw [hW₀e θ s hend]
        exact (smul_zero (κ (f (A θ s))) : κ (f (A θ s)) • (0 : Fin n → ℝ) = 0)
    have hd : dfV I f W' (A θ s) = 0 := by
      change NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ, ℝ) f (A θ s) (W' (A θ s))) = 0
      rw [hW'A, hW₀f θ s hs, map_zero]
    change W' (A θ s) + dfV I f W' (A θ s) • D.V (A θ s) = W₀ θ s
    rw [hd, zero_smul, add_zero, hW'A]

theorem exists_isotopyField [SigmaCompactSpace M] (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {c c' : ℝ} (hcc' : c < c') (hab : a < c ∧ c' < b)
    (hband : ∀ y, f y ∈ Icc c c' → ∀ p (hp : p ∈ crit),
      y ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')
    {A : ℝ → ℝ → M} {γ β : ℝ → M} (hA : isLevelAnnulus D c c' A γ β) :
    ∃ D₂ : GradientLikeStrip I f a b crit,
      (∀ p hp, (D₂.chart p hp).χ = (D.chart p hp).χ ∧ (D₂.chart p hp).k = (D.chart p hp).k ∧
        (D₂.chart p hp).R = (D.chart p hp).R ∧ (D₂.chart p hp).R' = (D.chart p hp).R' ∧
        (D₂.chart p hp).r₀ = (D.chart p hp).r₀) ∧
      (∀ p hp, D₂.rm p hp = D.rm p hp) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ f ⁻¹' Ioo c c' ∧ ∀ x, x ∉ K → D₂.V x = D.V x) ∧
      ∀ θ, D₂.flow (c' - c) (β θ) = γ θ := by
  obtain ⟨W₀, hW₀, hW₀per, hW₀f, hW₀end, hW₀der⟩ := exists_annulus_velocity hf D hcc' hab hband hA
  obtain ⟨W, hWs, hWc, hWsupp, hWdisj, hWf, hWA⟩ :=
    exists_levelTangent_extension hf D hcc' hab hband hA hW₀ hW₀per hW₀f hW₀end
  have hdf : ∀ x, dfV I f W x = 0 := by
    intro x
    unfold dfV
    rw [hWf x, map_zero]
  have hWmodel : ∀ p (hp : p ∈ crit), ∀ y, morseNorm n y < D.rm p hp →
      W ((D.chart p hp).χ y) = 0 := by
    intro p hp y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact Set.disjoint_left.1 (hWdisj p hp) hmem ⟨y, le_of_lt hy, rfl⟩
  have hadd : ∀ x, dfV I f (fun x => D.V x + W x) x = dfV I f D.V x := by
    intro x
    rw [dfV_add, hdf x, add_zero]
  have hcomp : IsCompact (tsupport (fun x => D.V x + W x)) := by
    refine (D.compact.union hWc).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun x hx => ?_) (D.compact.union hWc).isClosed)
    by_contra h
    rw [mem_union, not_or] at h
    apply hx
    simp only
    rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2]
    exact add_zero (0 : Fin n → ℝ)
  let D₂ : GradientLikeStrip I f a b crit :=
    { V := fun x => D.V x + W x
      smooth := D.smooth.add_section hWs
      compact := hcomp
      rate := fun x => by
        have h := hadd x
        unfold dfV at h
        rw [h]
        exact D.rate x
      chart := D.chart
      disjoint := D.disjoint
      inStrip := D.inStrip
      unit := fun x hx hno => by
        have h := hadd x
        unfold dfV at h
        rw [h]
        exact D.unit x hx hno
      neg := fun x hx hnc => by
        have h := hadd x
        unfold dfV at h
        rw [h]
        exact D.neg x hx hnc
      rm := D.rm
      hrm := D.hrm
      model := fun p hp y hy => by
        have hz := hWmodel p hp y hy
        change mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
          (D.V ((D.chart p hp).χ y) + W ((D.chart p hp).χ y)) = _
        rw [hz, add_zero]
        exact D.model p hp y hy }
  have hD₂V : ∀ x, D₂.V x = D.V x + W x := fun x => rfl
  refine ⟨D₂, fun p hp => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun p hp => rfl,
    ⟨tsupport W, hWc, hWsupp, fun x hx => ?_⟩, fun θ => ?_⟩
  · rw [hD₂V, image_eq_zero_of_notMem_tsupport hx]
    exact add_zero _
  obtain ⟨η, hη, hηlo, hηhi⟩ := hA.2.2.2.2.2
  obtain ⟨η', hη', hW₀0⟩ := hW₀end
  have hΔpos : 0 < c' - c := sub_pos.2 hcc'
  set Δ := c' - c with hΔ
  set e : ℝ := min (min η η') 1 / 2 with he
  have hm0 : 0 < min (min η η') 1 := lt_min (lt_min hη hη') one_pos
  have he0 : 0 < e := by rw [he]; linarith
  have heη : e ≤ η := by
    have := (min_le_left (min η η') 1).trans (min_le_left η η')
    rw [he]; linarith
  have heη' : e ≤ η' := by
    have := (min_le_left (min η η') 1).trans (min_le_right η η')
    rw [he]; linarith
  have he1 : e < 1 := by
    have := min_le_right (min η η') 1
    rw [he]; linarith
  have hAc : Continuous (uncurry A) := hA.1.continuous
  have hσc : Continuous (fun t : ℝ => A θ (1 - t / Δ)) :=
    hAc.comp (continuous_const.prodMk (continuous_const.sub (continuous_id.div_const Δ)))
  have hstep1 : D₂.flow (e * Δ) (β θ) = D.flow (e * Δ) (β θ) := by
    apply flow_eq_of_agree_along D D₂
    intro s hs
    rw [uIcc_of_le (by positivity)] at hs
    have hs0 : 0 ≤ s / Δ := div_nonneg hs.1 hΔpos.le
    have hse : s / Δ ≤ e := by rw [div_le_iff₀ hΔpos]; linarith [hs.2]
    have hu : A θ (1 - s / Δ) = D.flow s (β θ) := by
      rw [hηhi θ (1 - s / Δ) ⟨by linarith, by linarith⟩, sub_sub_cancel,
        div_mul_cancel₀ s hΔpos.ne']
    rw [← hu, hD₂V, hWA θ _ ⟨by linarith, by linarith⟩,
      hW₀0 θ _ (Or.inr ⟨by linarith, by linarith⟩)]
    exact add_zero _
  have ht₀ : A θ (1 - e * Δ / Δ) = D₂.flow (e * Δ) (β θ) := by
    rw [hstep1, hηhi θ _ ⟨by rw [mul_div_cancel_right₀ e hΔpos.ne']; linarith,
      by rw [mul_div_cancel_right₀ e hΔpos.ne']; linarith⟩, sub_sub_cancel,
      div_mul_cancel₀ _ hΔpos.ne']
  have hgs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s' => A θ s') :=
    hA.1.comp (contDiff_const.prodMk contDiff_id).contMDiff
  have hint : IsMIntegralCurveOn (fun t : ℝ => A θ (1 - t / Δ)) D₂.V (Ioo 0 Δ) := by
    intro t ht
    have hs0 : 0 < t / Δ := div_pos ht.1 hΔpos
    have hs1 : t / Δ < 1 := by rw [div_lt_one hΔpos]; exact ht.2
    have hh : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => 1 - t / Δ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(1 / Δ))) := by
      apply HasFDerivAt.hasMFDerivAt
      have hd := ((hasDerivAt_id t).div_const Δ).const_sub 1
      exact hd.hasFDerivAt
    have hg := ((hgs.mdifferentiable (by simp)) (1 - t / Δ)).hasMFDerivAt
    have hc := hg.comp t hh
    have hEq : (mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') (1 - t / Δ)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(1 / Δ))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (D₂.V (A θ (1 - t / Δ))) := by
      apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, one_smul]
      set L := mfderiv 𝓘(ℝ, ℝ) I (fun s' => A θ s') (1 - t / Δ) with hL
      have h3 : L (-(1 / Δ)) = (-(1 / Δ)) • L 1 := by
        rw [← L.map_smul]
        congr 1
        exact (mul_one (-(1 / Δ) : ℝ)).symm
      have h5 : L 1 = (-Δ) • ((show TangentSpace I (A θ (1 - t / Δ)) from W₀ θ (1 - t / Δ)) +
          D.V (A θ (1 - t / Δ))) := hW₀der θ _
      rw [h3, h5, smul_smul]
      have h2 : -(1 / Δ) * -Δ = 1 := by field_simp
      rw [h2, one_smul]
      change _ = D.V (A θ (1 - t / Δ)) + W (A θ (1 - t / Δ))
      rw [hWA θ _ ⟨by linarith, by linarith⟩]
      exact add_comm _ _
    exact (hc.congr_mfderiv hEq).hasMFDerivWithinAt
  have hint' : IsMIntegralCurveOn (fun t => D₂.flow t (β θ)) D₂.V (Ioo 0 Δ) :=
    fun t _ => (D₂.isMIntegralCurve_flow (β θ) t).hasMFDerivWithinAt
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := e * Δ) ⟨by positivity, mul_lt_of_lt_one_left hΔpos he1⟩ D₂.smooth_one hint hint' ht₀
  have hcl : EqOn (fun t : ℝ => A θ (1 - t / Δ)) (fun t => D₂.flow t (β θ))
      (closure (Ioo 0 Δ)) :=
    heq.closure hσc (D₂.continuous_flow_curve (β θ))
  rw [closure_Ioo hΔpos.ne] at hcl
  have hfin := hcl (right_mem_Icc.2 hΔpos.le)
  simp only at hfin
  rw [div_self hΔpos.ne', sub_self, hηlo θ 0 ⟨le_rfl, hη.le⟩, zero_mul, neg_zero,
    GradientLikeStrip.flow_zero] at hfin
  exact hfin.symm

theorem exists_birth_above_loop [SigmaCompactSpace M] [DecidableEq M] (h5 : 5 ≤ n)
    (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c₂ c₃ : ℝ}
    (hc : a < c₂ ∧ c₂ < c₃ ∧ c₃ < b)
    (hband : ∀ y, f y ∈ Icc c₂ c₃ → ∀ p (hp : p ∈ crit),
      y ∉ closure ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'))
    {γ : ℝ → M} (hγ : isLevelLoop I f c₂ γ) {Hm : ℝ → ℝ → M}
    (hH : isLevelHomotopy f c₂ Hm γ (fun _ => γ 0)) {ε : ℝ} (hε : 0 < ε)
    (hεc : 64 * ε < c₃ - c₂) :
    ∃ (f₁ : M → ℝ) (q r : M) (D₁ : GradientLikeStrip I f₁ a b (insert q (insert r crit)))
      (K : Set M), IsCompact K ∧ K ⊆ f ⁻¹' Ioo (c₂ + (c₃ - c₂) / 4) c₃ ∧
      K ⊆ f₁ ⁻¹' Ioo (c₂ + (c₃ - c₂) / 4) c₃ ∧
      (∀ x, x ∉ K → f₁ x = f x ∧ D₁.V x = D.V x) ∧
      ModifiedWithin f c₂ c₃ f₁ ∧ MorseStrip I f₁ a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∨ x = q ∨ x = r) ∧
      q ∈ K ∧ r ∈ K ∧ c₂ + (c₃ - c₂) / 8 < f₁ q ∧ f₁ q < f₁ r ∧
      f₁ r < c₃ - (c₃ - c₂) / 8 ∧
      morseIndex I f₁ q = 2 ∧ morseIndex I f₁ r = 3 ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f₁ x = morseIndex I f x) ∧
      (∀ x (hx : x ∈ crit),
        (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).χ =
            (D.chart x hx).χ ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).k =
            (D.chart x hx).k ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R =
            (D.chart x hx).R ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R' =
            (D.chart x hx).R' ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).r₀ =
            (D.chart x hx).r₀ ∧
          D₁.rm x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) = D.rm x hx) ∧
      (∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
        (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R' ⊆ K ∧
        ∀ y ∈ (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R', |f₁ y - f₁ x| < ε) ∧
      ∃ (hkq : (D₁.chart q (Finset.mem_insert_self q _)).k = 2) (ε' : ℝ), 0 < ε' ∧ ε' ≤ ε ∧
        2 * ε' < f₁ r - f₁ q ∧
        (D₁.chart q (Finset.mem_insert_self q _)).r₀ ^ 2 < 2 * ε' ∧
        8 * ε' < D₁.rm q (Finset.mem_insert_self q _) ^ 2 ∧
        (∀ y ∈ (D₁.chart q (Finset.mem_insert_self q _)).leftModelSphere ε',
          ∀ s ∈ Icc 0 (f₁ q - ε' - (c₂ + (c₃ - c₂) / 4)),
            ∀ x (hx : x ∈ insert q (insert r crit)),
              D₁.flow s ((D₁.chart q (Finset.mem_insert_self q _)).χ y) ∉
                D₁.closedSmallBall x hx) ∧
        isLevelLoop I f (c₂ + (c₃ - c₂) / 4)
          (leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' (c₂ + (c₃ - c₂) / 4)) ∧
        ∃ H : ℝ → ℝ → M, isLevelHomotopy f c₂ H γ (fun θ => D.flow ((c₃ - c₂) / 4)
          (leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' (c₂ + (c₃ - c₂) / 4) θ)) := by
  obtain ⟨ha2, h23, h3b⟩ := hc
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hL₀ : 0 < (c₃ - c₂) / 4 := by linarith
  have hnoSmall : ∀ y, f y ∈ Icc c₂ c₃ → ∀ p (hp : p ∈ crit), y ∉ D.smallBall p hp :=
    fun y hy p hp hmem => hband y hy p hp (subset_closure (D.smallBall_subset_image_ball p hp hmem))
  have hnoClosed : ∀ y, f y ∈ Icc c₂ c₃ → ∀ p (hp : p ∈ crit), y ∉ D.closedSmallBall p hp :=
    fun y hy p hp hmem =>
      hband y hy p hp (subset_closure (D.closedSmallBall_subset_image_ball p hp hmem))
  have hγ0 : f (γ 0) = c₂ := hγ.2.2.2.2 0
  set x₀ : M := D.flow (-((c₃ - c₂) / 4)) (γ 0) with hx₀def
  have hx₀ : f x₀ = c₂ + (c₃ - c₂) / 4 := by
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels hfs (D := D) (x := γ 0)
      (T := -((c₃ - c₂) / 4)) (by rw [hγ0]; exact ⟨ha2.le, (h23.trans h3b).le⟩)
      (by rw [hγ0]; constructor <;> linarith) (by
        intro y hy p hp
        refine hnoSmall y ?_ p hp
        rw [hγ0, uIcc_of_le (by linarith)] at hy
        exact ⟨hy.1, by linarith [hy.2]⟩)
      (-((c₃ - c₂) / 4)) right_mem_uIcc
    rw [h, hγ0]; ring
  have hflowx₀ : D.flow ((c₃ - c₂) / 4) x₀ = γ 0 := D.flow_flow_neg (γ 0) _
  have hfree : ∀ s ∈ Icc (-((c₃ - c₂) / 2)) 0, ∀ p (hp : p ∈ crit),
      D.flow s x₀ ∉ closure ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') := by
    have h := GradientLikeStrip.f_flow_eq_sub_of_levels hfs (D := D) (x := x₀)
      (T := -((c₃ - c₂) / 2)) (by rw [hx₀]; constructor <;> linarith)
      (by rw [hx₀]; constructor <;> linarith) (by
        intro y hy p hp
        refine hnoSmall y ?_ p hp
        rw [hx₀, uIcc_of_le (by linarith)] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    intro s hs p hp
    have hs' : s ∈ uIcc 0 (-((c₃ - c₂) / 2)) := by
      rw [uIcc_of_ge (by linarith)]; exact hs
    refine hband _ ?_ p hp
    rw [h s hs', hx₀]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨ρ, hρ, -, hρa, hρb, ⟨B⟩⟩ := exists_flowBox hf D hx₀ (L := (c₃ - c₂) / 2)
    (by linarith) ⟨by linarith, by linarith⟩ hfree one_pos
  obtain ⟨f₁, q, r, D₁, hmod, hMS, hoff, hcrit₁, hqB, hrB, hq1, hqr, hr1, hiq, hir, hind,
      hcharts, hnew, hkq, ε', hε'0, hε'ε, hε'gap, hr₀q, hrmq, hfreeq, hface, hloop₁⟩ :=
    exists_birth_in_box h5 hf D hcrit B (by linarith) hρ ⟨hρa, hρb⟩ hε (by linarith)
  set lo : Fin n → ℝ := fun j => if j = B.i₀ then (c₃ - c₂) / 2 / 8 else -(3 * ρ / 4) with hlo
  set hi : Fin n → ℝ := fun j => if j = B.i₀ then 7 * ((c₃ - c₂) / 2) / 8 else 3 * ρ / 4
    with hhi
  have hCbox : Icc lo hi ⊆ boxSet B.i₀ ρ ((c₃ - c₂) / 2) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · have h1 := hy1 j
      have h2 := hy2 j
      simp only [hlo, hhi, hj, ↓reduceIte] at h1 h2
      rw [abs_lt]; constructor <;> linarith
    · have h1 := hy1 B.i₀
      simp only [hlo, ↓reduceIte] at h1
      linarith
    · have h2 := hy2 B.i₀
      simp only [hhi, ↓reduceIte] at h2
      linarith
  have hmidC : midBox B.i₀ ρ ((c₃ - c₂) / 2) ⊆ Icc lo hi := by
    intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = B.i₀
      · subst hj; simp only [hlo, ↓reduceIte]; exact hy2.le
      · simp only [hlo, hj, ↓reduceIte]; exact (neg_le_of_abs_le (hy1 j hj).le)
    · by_cases hj : j = B.i₀
      · subst hj; simp only [hhi, ↓reduceIte]; exact hy3.le
      · simp only [hhi, hj, ↓reduceIte]; exact (le_of_abs_le (hy1 j hj).le)
  have hmidK : B.ψ '' midBox B.i₀ ρ ((c₃ - c₂) / 2) ⊆ B.ψ '' Icc lo hi := image_mono hmidC
  have hKf : B.ψ '' Icc lo hi ⊆ f ⁻¹' Ioo (c₂ + (c₃ - c₂) / 4) (c₂ + (c₃ - c₂) / 4 + (c₃ - c₂) / 2) := by
    rintro x ⟨y, hy, rfl⟩
    have hlev := B.level y (hCbox hy)
    have h1 := hy.1 B.i₀
    have h2 := hy.2 B.i₀
    simp only [hlo, hhi, ↓reduceIte] at h1 h2
    simp only [mem_preimage, mem_Ioo, hlev]
    constructor <;> linarith
  refine ⟨f₁, q, r, D₁, B.ψ '' Icc lo hi, ?_, ?_, ?_, ?_, ?_, hMS, hcrit₁, hmidK hqB, hmidK hrB,
    by linarith, hqr, by linarith, hiq, hir, hind, hcharts, ?_, hkq, ε', hε'0, hε'ε, hε'gap,
    hr₀q, hrmq, hfreeq, ?_, ?_⟩
  · exact isCompact_Icc.image_of_continuousOn
      (B.smooth.continuousOn.mono (hCbox.trans B.box_subset))
  · intro x hx
    have h := hKf hx
    simp only [mem_preimage, mem_Ioo] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · intro x hx
    have h := hmod.mapsTo (hKf hx)
    simp only [mem_preimage, mem_Ioo] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · intro x hx
    exact hoff x fun hmem => hx (hmidK hmem)
  · refine ⟨fun x hx => hmod.eqOn fun hmem => hx ?_, fun x hx => ?_⟩
    · simp only [mem_preimage, mem_Ioo] at hmem ⊢
      constructor <;> linarith [hmem.1, hmem.2]
    · by_cases hmem : x ∈ f ⁻¹' Ioo (c₂ + (c₃ - c₂) / 4) (c₂ + (c₃ - c₂) / 4 + (c₃ - c₂) / 2)
      · have h := hmod.mapsTo hmem
        simp only [mem_Ioo] at h ⊢
        constructor <;> linarith [h.1, h.2]
      · rw [hmod.eqOn hmem]; exact hx
  · intro x hx hxqr
    obtain ⟨h1, h2⟩ := hnew x hx hxqr
    exact ⟨h1.trans hmidK, h2⟩
  · have hβlev : ∀ θ, f (leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε'
        (c₂ + (c₃ - c₂) / 4) θ) = c₂ + (c₃ - c₂) / 4 := by
      intro θ
      obtain ⟨y, hy, hyeq⟩ := hface θ
      have hyb : y ∈ boxSet B.i₀ ρ ((c₃ - c₂) / 2) :=
        ⟨hy.1, by rw [hy.2]; linarith, by rw [hy.2]; linarith⟩
      rw [← hyeq, B.level y hyb, hy.2, add_zero]
    exact ⟨hloop₁.1, hloop₁.2.1, hloop₁.2.2.1, hloop₁.2.2.2.1, hβlev⟩
  · have hβc : Continuous (leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε'
        (c₂ + (c₃ - c₂) / 4)) := hloop₁.2.1.continuous
    have h9 := isLevelHomotopy_face hfs D B (by linarith) hρ (c₀ := c₂) ha2.le (by linarith)
      (by linarith) (fun y hy x hx => hnoClosed y ⟨hy.1, by linarith [hy.2]⟩ x hx) hβc
      hloop₁.1 hface
    have e : c₂ + (c₃ - c₂) / 4 - c₂ = (c₃ - c₂) / 4 := by ring
    rw [e, hflowx₀] at h9
    exact hH.trans h9

theorem exists_birth_along_loop [SigmaCompactSpace M] [DecidableEq M] (h5 : 5 ≤ n)
    (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c₂ c₃ : ℝ}
    (hc : a < c₂ ∧ c₂ < c₃ ∧ c₃ < b)
    (hband : ∀ y, f y ∈ Icc c₂ c₃ → ∀ p (hp : p ∈ crit),
      y ∉ closure ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'))
    {γ : ℝ → M} (hγ : isLevelLoop I f c₂ γ) {Hm : ℝ → ℝ → M}
    (hH : isLevelHomotopy f c₂ Hm γ (fun _ => γ 0)) {ε : ℝ} (hε : 0 < ε)
    (hεc : 64 * ε < c₃ - c₂) :
    ∃ (f₁ : M → ℝ) (q r : M) (D₁ : GradientLikeStrip I f₁ a b (insert q (insert r crit)))
      (K : Set M), IsCompact K ∧ K ⊆ f ⁻¹' Ioo c₂ c₃ ∧
      (∀ x, x ∉ K → f₁ x = f x ∧ D₁.V x = D.V x) ∧
      ModifiedWithin f c₂ c₃ f₁ ∧ MorseStrip I f₁ a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∨ x = q ∨ x = r) ∧
      q ∈ K ∧ r ∈ K ∧ c₂ + (c₃ - c₂) / 8 < f₁ q ∧ f₁ q < f₁ r ∧
      f₁ r < c₃ - (c₃ - c₂) / 8 ∧
      morseIndex I f₁ q = 2 ∧ morseIndex I f₁ r = 3 ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I f₁ x = morseIndex I f x) ∧
      (∀ x (hx : x ∈ crit),
        (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).χ =
            (D.chart x hx).χ ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).k =
            (D.chart x hx).k ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R =
            (D.chart x hx).R ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).R' =
            (D.chart x hx).R' ∧
          (D₁.chart x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))).r₀ =
            (D.chart x hx).r₀ ∧
          D₁.rm x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) = D.rm x hx) ∧
      (∀ x (hx : x ∈ insert q (insert r crit)), x = q ∨ x = r →
        (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R' ⊆ K ∧
        ∀ y ∈ (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R', |f₁ y - f₁ x| < ε) ∧
      ∃ (hkq : (D₁.chart q (Finset.mem_insert_self q _)).k = 2) (ε' : ℝ), 0 < ε' ∧ ε' ≤ ε ∧
        2 * ε' < f₁ r - f₁ q ∧
        (D₁.chart q (Finset.mem_insert_self q _)).r₀ ^ 2 < 2 * ε' ∧
        8 * ε' < D₁.rm q (Finset.mem_insert_self q _) ^ 2 ∧
        leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' c₂ = γ ∧
        ∀ y ∈ (D₁.chart q (Finset.mem_insert_self q _)).leftModelSphere ε',
          ∀ s ∈ Icc 0 (f₁ q - ε' - c₂), ∀ x (hx : x ∈ insert q (insert r crit)),
            D₁.flow s ((D₁.chart q (Finset.mem_insert_self q _)).χ y) ∉
              D₁.closedSmallBall x hx := by
  obtain ⟨f₁, q, r, D₁, K, hKc, hKf, hKf₁, hoff, hmod, hms, hcritiff, hqK, hrK, hfq, hqr, hfr,
    hiq, hir, hidx, hch, hnew, hkq, ε', hε', hε'ε, hgap, hr₀q, hrmq, hfree, hβ, Hβ, hHβ⟩ :=
    exists_birth_above_loop h5 hf D hcrit hc hband hγ hH hε hεc
  set c' := c₂ + (c₃ - c₂) / 4 with hc'def
  set β := leftLoop D₁ q (Finset.mem_insert_self q _) hkq ε' c' with hβdef
  have hq₁ : q ∈ insert q (insert r crit) := Finset.mem_insert_self q _
  have hc₂c' : c₂ < c' := by rw [hc'def]; linarith [hc.2.1]
  have hc'c₃ : c' < c₃ := by rw [hc'def]; linarith [hc.2.1]
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hf₁s : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁ := hms.smooth
  have hnotK : ∀ w, f w ≤ c' → w ∉ K := fun w hw hwK => by
    have := (hKf hwK).1
    linarith
  have hnotK₁ : ∀ w, f₁ w ≤ c' → w ∉ K := fun w hw hwK => by
    have := (hKf₁ hwK).1
    linarith
  have hnoball : ∀ w, f₁ w ∈ Icc c₂ c' → ∀ x (hx : x ∈ insert q (insert r crit)),
      w ∉ (D₁.chart x hx).χ '' Metric.ball 0 (D₁.chart x hx).R' := by
    intro w hw x hx hwx
    have hwK : w ∉ K := hnotK₁ w hw.2
    have hfw : f w = f₁ w := ((hoff w hwK).1).symm
    rcases Finset.mem_insert.1 hx with hxq | hx'
    · exact hwK ((hnew x hx (Or.inl hxq)).1 hwx)
    rcases Finset.mem_insert.1 hx' with hxr | hxc
    · exact hwK ((hnew x hx (Or.inr hxr)).1 hwx)
    · obtain ⟨h1, -, -, h4, -, -⟩ := hch x hxc
      rw [h1, h4] at hwx
      exact hband w ⟨by rw [hfw]; exact hw.1, by rw [hfw]; linarith [hw.2]⟩ x hxc
        (subset_closure hwx)
  have hband10 : ∀ y, f y ∈ Icc c₂ c' → ∀ p (hp : p ∈ crit), y ∉ D.closedSmallBall p hp := by
    intro y hy p hp hyp
    exact hband y ⟨hy.1, hy.2.trans hc'c₃.le⟩ p hp
      (subset_closure (D.closedSmallBall_subset_image_ball p hp hyp))
  have hc'sub : c' - c₂ = (c₃ - c₂) / 4 := by rw [hc'def]; ring
  have hH' : isLevelHomotopy f c₂ Hβ γ (fun θ => D.flow (c' - c₂) (β θ)) := by
    rw [hc'sub]; exact hHβ
  obtain ⟨A, hA⟩ := exists_levelAnnulus h5 hf D hc₂c' ⟨hc.1, by linarith [hc.2.2]⟩ hband10 hγ
    hβ hH'
  have hlow : ∀ (x : M) (T : ℝ), f x ≤ c' → f (D.flow T x) ≤ c' →
      ∀ u ∈ uIcc 0 T, D₁.V (D.flow u x) = D.V (D.flow u x) := by
    intro x T hx hT u hu
    have hmem := GradientLikeStrip.f_flow_mem_uIcc_of_mem_uIcc (D := D) hfs x hu
    have hle : f (D.flow u x) ≤ c' := by
      rw [mem_uIcc] at hmem
      rcases hmem with h | h
      · linarith [h.2]
      · linarith [h.2]
    exact (hoff _ (hnotK _ hle)).2
  obtain ⟨hAsm, hAper, hAlev, hAinj, hAimm, η, hη, hA0, hA1⟩ := hA
  have hAlev' : ∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, f (A θ s) ≤ c' := by
    intro θ s hs
    rw [hAlev θ s hs]
    nlinarith [hs.2, hc₂c']
  have hA₁ : isLevelAnnulus D₁ c₂ c' A γ β := by
    refine ⟨hAsm, hAper, ?_, hAinj, hAimm, min η 1, lt_min hη one_pos, ?_, ?_⟩
    · intro θ s hs
      rw [(hoff _ (hnotK _ (hAlev' θ s hs))).1]
      exact hAlev θ s hs
    · intro θ s hs
      have hs' : s ∈ Icc 0 η := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
      rw [hA0 θ s hs']
      symm
      refine flow_eq_of_agree_along D D₁ ?_
      refine hlow (γ θ) _ (by rw [hγ.2.2.2.2 θ]; exact hc₂c'.le) ?_
      rw [← hA0 θ s hs']
      exact hAlev' θ s hs1
    · intro θ s hs
      have hmin : 1 - η ≤ 1 - min η 1 := by linarith [min_le_left η 1]
      have hs' : s ∈ Icc (1 - η) 1 := ⟨hmin.trans hs.1, hs.2⟩
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1, min_le_right η 1], hs.2⟩
      rw [hA1 θ s hs']
      symm
      refine flow_eq_of_agree_along D D₁ ?_
      refine hlow (β θ) _ (by rw [hβ.2.2.2.2 θ]) ?_
      rw [← hA1 θ s hs']
      exact hAlev' θ s hs1
  obtain ⟨D₂, hD₂ch, hD₂rm, ⟨K₂, hK₂c, hK₂f₁, hK₂off⟩, hD₂flow⟩ :=
    exists_isotopyField hms D₁ hc₂c' ⟨hc.1, by linarith [hc.2.2]⟩ hnoball hA₁
  have hfβ : ∀ t, f₁ (β t) = c' := by
    intro t
    have h := hβ.2.2.2.2 t
    rw [(hoff _ (hnotK _ h.le)).1]
    exact h
  have hfγ : ∀ t, f₁ (γ t) = c₂ := by
    intro t
    have h := hγ.2.2.2.2 t
    rw [(hoff _ (hnotK _ (by rw [h]; exact hc₂c'.le))).1]
    exact h
  have hRq : 2 * ε' ≤ (D₁.chart q hq₁).R ^ 2 := by
    have h1 := D₁.rm_pos q hq₁
    have h2 := (D₁.hrm q hq₁).2
    nlinarith
  have hw : ∀ t, (fun i => circ2 t (Fin.cast hkq i)) ≠ 0 := by
    intro t h
    have h0 := congrFun h (Fin.cast hkq.symm 0)
    have h1 := congrFun h (Fin.cast hkq.symm 1)
    simp only [Fin.cast_cast, Fin.cast_eq_self, Pi.zero_apply, circ2] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h0, h1] at this
    norm_num at this
  have hmemS : ∀ t, (D₁.chart q hq₁).sphereParam ε' (fun i => circ2 t (Fin.cast hkq i)) ∈
      (D₁.chart q hq₁).leftModelSphere ε' := fun t =>
    (D₁.chart q hq₁).sphereParam_mem_leftModelSphere hε'.le (hw t)
  have hptK : ∀ t, leftPt D₁ q hq₁ hkq ε' t ∈ K := by
    intro t
    exact (hnew q hq₁ (Or.inl rfl)).1 ⟨_, (D₁.chart q hq₁).mem_ball_of_le
      ((D₁.chart q hq₁).morseNorm_le_R_of_mem_leftModelSphere hRq (hmemS t)), rfl⟩
  have hT : 0 ≤ f₁ q - ε' - c' := by
    by_contra hneg'
    have hneg := not_le.1 hneg'
    have h1 := (hKf₁ (hptK 0)).1
    have h2 := GradientLikeStrip.f_flow_antitone (D := D₁) hf₁s (leftPt D₁ q hq₁ hkq ε' 0)
      hneg.le
    simp only [GradientLikeStrip.flow_zero] at h2
    have h3 : f₁ (D₁.flow (f₁ q - ε' - c') (leftPt D₁ q hq₁ hkq ε' 0)) = c' := hfβ 0
    linarith
  have hup : ∀ t, ∀ u ∈ uIcc 0 (f₁ q - ε' - c'),
      D₂.V (D₁.flow u (leftPt D₁ q hq₁ hkq ε' t)) = D₁.V (D₁.flow u (leftPt D₁ q hq₁ hkq ε' t)) := by
    intro t u hu
    rw [uIcc_of_le hT] at hu
    apply hK₂off
    intro hmem
    have h1 := (hK₂f₁ hmem).2
    have h2 := GradientLikeStrip.f_flow_antitone (D := D₁) hf₁s (leftPt D₁ q hq₁ hkq ε' t) hu.2
    have h3 : f₁ (D₁.flow (f₁ q - ε' - c') (leftPt D₁ q hq₁ hkq ε' t)) = c' := hfβ t
    simp only at h2
    linarith
  have hflowT : ∀ t, D₂.flow (f₁ q - ε' - c') (leftPt D₁ q hq₁ hkq ε' t) =
      D₁.flow (f₁ q - ε' - c') (leftPt D₁ q hq₁ hkq ε' t) := fun t =>
    flow_eq_of_agree_along D₁ D₂ (hup t)
  have hkq₂ : (D₂.chart q hq₁).k = 2 := (hD₂ch q hq₁).2.1.trans hkq
  have hS5 := leftLoop_congr D₁ D₂ hq₁ hq₁ hkq hkq₂ (hD₂ch q hq₁).1 rfl (ε := ε') (c := c')
    hflowT
  have hcsb : ∀ x (hx : x ∈ insert q (insert r crit)),
      D₂.closedSmallBall x hx = D₁.closedSmallBall x hx := by
    intro x hx
    simp only [GradientLikeStrip.closedSmallBall]
    rw [(hD₂ch x hx).1, (hD₂ch x hx).2.2.2.2]
  refine ⟨f₁, q, r, D₂, K ∪ K₂, hKc.union hK₂c, ?_, ?_, hmod, hms, hcritiff,
    Or.inl hqK, Or.inl hrK, hfq, hqr, hfr, hiq, hir, hidx, ?_, ?_, hkq₂, ε', hε', hε'ε, hgap,
    ?_, ?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact ⟨(hKf hx).1.trans' (by linarith [hc.2.1]), (hKf hx).2⟩
    · have h := hK₂f₁ hx
      have hxK : x ∉ K := hnotK₁ x h.2.le
      rw [mem_preimage, ← (hoff x hxK).1]
      exact ⟨h.1, h.2.trans hc'c₃⟩
  · intro x hx
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxK₂ : x ∉ K₂ := fun h => hx (Or.inr h)
    exact ⟨(hoff x hxK).1, (hK₂off x hxK₂).trans (hoff x hxK).2⟩
  · intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hch x hx
    obtain ⟨g1, g2, g3, g4, g5⟩ := hD₂ch x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4, g5.trans h5,
      (hD₂rm x _).trans h6⟩
  · intro x hx hxqr
    rw [(hD₂ch x hx).1, (hD₂ch x hx).2.2.2.1]
    exact ⟨(hnew x hx hxqr).1.trans subset_union_left, (hnew x hx hxqr).2⟩
  · rw [(hD₂ch q hq₁).2.2.2.2]; exact hr₀q
  · rw [hD₂rm q hq₁]; exact hrmq
  · funext t
    change D₂.flow (f₁ q - ε' - c₂) (leftPt D₂ q hq₁ hkq₂ ε' t) = γ t
    rw [hS5.1, show f₁ q - ε' - c₂ = (f₁ q - ε' - c') + (c' - c₂) by ring,
      GradientLikeStrip.flow_add, hflowT t]
    exact hD₂flow t
  · intro y hy s hs x hx
    obtain ⟨t, rfl⟩ := exists_angle_of_mem_leftModelSphere D₂ hq₁ hkq₂ hε' hy
    have hpt : (D₂.chart q hq₁).χ ((D₂.chart q hq₁).sphereParam ε'
        (fun i => circ2 t (Fin.cast hkq₂ i))) = leftPt D₁ q hq₁ hkq ε' t :=
      congrFun hS5.1 t
    rw [hpt, hcsb x hx]
    rcases le_or_gt s (f₁ q - ε' - c') with hsT | hsT
    · rw [flow_eq_of_agree_along D₁ D₂ (T := s) (fun u hu => hup t u (by
        rw [uIcc_of_le hs.1] at hu
        rw [uIcc_of_le hT]
        exact ⟨hu.1, hu.2.trans hsT⟩))]
      exact hfree _ (hmemS t) s ⟨hs.1, hsT⟩ x hx
    · rw [show s = (f₁ q - ε' - c') + (s - (f₁ q - ε' - c')) by ring,
        GradientLikeStrip.flow_add, hflowT t]
      intro hmem
      have hu : s - (f₁ q - ε' - c') ∈ uIcc 0 (c' - c₂) := by
        rw [uIcc_of_le (by linarith)]
        constructor
        · linarith
        · linarith [hs.2]
      have hl := GradientLikeStrip.f_flow_mem_uIcc_of_mem_uIcc (D := D₂) hf₁s (β t) hu
      rw [hD₂flow t, hfγ t, hfβ t, uIcc_of_ge hc₂c'.le] at hl
      exact hnoball _ hl x hx (D₁.closedSmallBall_subset_image_ball x hx hmem)

end Birth

end

end IndexOnePartner

end DifferentialGeometry.Topology
