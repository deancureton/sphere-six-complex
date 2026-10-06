module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelFlowBack

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

noncomputable section

theorem deriv_nonpos_of_antitone {g : ℝ → ℝ} (hg : Antitone g) {t d : ℝ}
    (hd : HasDerivAt g d t) : d ≤ 0 := by
  have := nonneg_of_hasDerivAt_of_le_left (g := fun s => -g s) (r := -d) (t := t) (ε := 1)
    one_pos hd.neg (fun s hs => by show -g s ≤ -g t; linarith [hg hs.2.le])
  linarith

theorem convex_lt_lower {a x y m : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : a ≠ 0 → m < x)
    (hy : a ≠ 1 → m < y) : m < a * x + (1 - a) * y := by
  by_cases h0 : a = 0
  · subst h0; simpa using hy (by norm_num)
  by_cases h1 : a = 1
  · subst h1; simpa using hx (by norm_num)
  have hx' := hx h0
  have hy' := hy h1
  have ha0' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm h0)
  have ha1' : 0 < 1 - a := sub_pos.2 (lt_of_le_of_ne ha1 h1)
  nlinarith [mul_pos ha0' (sub_pos.2 hx'), mul_pos ha1' (sub_pos.2 hy')]

theorem convex_lt_upper {a x y m : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : a ≠ 0 → x < m)
    (hy : a ≠ 1 → y < m) : a * x + (1 - a) * y < m := by
  have := convex_lt_lower (a := a) (x := -x) (y := -y) (m := -m) ha0 ha1
    (fun h => by linarith [hx h]) (fun h => by linarith [hy h])
  linarith

namespace CancelInterp

def lam (h t : ℝ) : ℝ := CancelModel.cut (h / 2) h t

variable {h : ℝ}

theorem contDiff_lam (h : ℝ) : ContDiff ℝ ∞ (lam h) := CancelModel.contDiff_cut _ _

theorem lam_nonneg (h t : ℝ) : 0 ≤ lam h t := CancelModel.cut_nonneg _ _ _

theorem lam_le_one (h t : ℝ) : lam h t ≤ 1 := CancelModel.cut_le_one _ _ _

theorem lam_eq_one (hh : 0 < h) {t : ℝ} (ht : t ≤ h / 2) : lam h t = 1 :=
  CancelModel.cut_eq_one (by linarith) ht

theorem lam_eq_zero (hh : 0 < h) {t : ℝ} (ht : h ≤ t) : lam h t = 0 :=
  CancelModel.cut_eq_zero (by linarith) ht

theorem lam_pos (hh : 0 < h) {t : ℝ} (ht : t < h) : 0 < lam h t :=
  CancelModel.cut_pos_of_lt (by linarith) ht

theorem lam_lt_one (hh : 0 < h) {t : ℝ} (ht : h / 2 < t) : lam h t < 1 := by
  refine lt_of_le_of_ne (lam_le_one h t) fun heq => ?_
  have := (CancelModel.cut_eq_one_iff (lo := h / 2) (hi := h) (t := t) (by linarith)).1 heq
  linarith

theorem lam_antitone (hh : 0 < h) : Antitone (lam h) := CancelModel.cut_antitone (by linarith)

theorem hasDerivAt_lam (h t : ℝ) : HasDerivAt (lam h) (deriv (lam h) t) t :=
  ((contDiff_lam h).differentiable (by simp) t).hasDerivAt

theorem deriv_lam_nonpos (hh : 0 < h) (t : ℝ) : deriv (lam h) t ≤ 0 :=
  deriv_nonpos_of_antitone (lam_antitone hh) (hasDerivAt_lam h t)

theorem deriv_lam_eq_zero_of_le_half (hh : 0 < h) {t : ℝ} (ht : t ≤ h / 2) :
    deriv (lam h) t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Eventually.of_forall fun s => by rw [lam_eq_one hh ht]; exact lam_le_one h s

theorem deriv_lam_eq_zero_of_le (hh : 0 < h) {t : ℝ} (ht : h ≤ t) : deriv (lam h) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Eventually.of_forall fun s => by rw [lam_eq_zero hh ht]; exact lam_nonneg h s

def bridge (L h s t : ℝ) : ℝ := h + (L - 2 * h) * (t / (s + t))

def interpolation (L h s t : ℝ) : ℝ :=
  lam h t * t + (1 - lam h t) * (lam h s * (L - s) + (1 - lam h s) * bridge L h s t)

theorem bridge_mem {L h s t : ℝ} (hL : 2 * h ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 < s + t) :
    h ≤ bridge L h s t ∧ bridge L h s t ≤ L - h := by
  have h1 : 0 ≤ t / (s + t) := div_nonneg ht hst.le
  have h2 : t / (s + t) ≤ 1 := (div_le_one hst).2 (by linarith)
  unfold bridge
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hL) h1, mul_nonneg (sub_nonneg.2 hL)
    (sub_nonneg.2 h2)]

theorem interpolation_of_le_half (hh : 0 < h) {L s t : ℝ} (ht : t ≤ h / 2) : interpolation L h s t = t := by
  simp [interpolation, lam_eq_one hh ht]

theorem interpolation_of_le_half_left (hh : 0 < h) {L s t : ℝ} (hs : s ≤ h / 2) (ht : h ≤ t) :
    interpolation L h s t = L - s := by
  simp [interpolation, lam_eq_one hh hs, lam_eq_zero hh ht]

theorem interpolation_pos (hh : 0 < h) {L s t : ℝ} (hL : 2 * h < L) (hs : 0 < s) (ht : 0 < t) :
    0 < interpolation L h s t := by
  have hst : 0 < s + t := by linarith
  obtain ⟨hB1, -⟩ := bridge_mem (L := L) hL.le hs.le ht.le hst
  unfold interpolation
  refine convex_lt_lower (lam_nonneg h t) (lam_le_one h t) (fun _ => ht) fun hne => ?_
  refine convex_lt_lower (lam_nonneg h s) (lam_le_one h s) (fun hne' => ?_) fun _ => by linarith
  have : s < h := by
    by_contra hc
    exact hne' (lam_eq_zero hh (not_lt.1 hc))
  linarith

theorem interpolation_lt (hh : 0 < h) {L s t : ℝ} (hL : 2 * h < L) (hs : 0 < s) (ht : 0 < t) :
    interpolation L h s t < L := by
  have hst : 0 < s + t := by linarith
  obtain ⟨-, hB2⟩ := bridge_mem (L := L) hL.le hs.le ht.le hst
  unfold interpolation
  refine convex_lt_upper (lam_nonneg h t) (lam_le_one h t) (fun hne => ?_) fun _ => ?_
  · have : t < h := by
      by_contra hc
      exact hne (lam_eq_zero hh (not_lt.1 hc))
    linarith
  · exact convex_lt_upper (lam_nonneg h s) (lam_le_one h s) (fun _ => by linarith)
      fun _ => by linarith

def interpolationLineDeriv (L h s t : ℝ) : ℝ :=
  deriv (lam h) t * ((lam h s * (L - s) + (1 - lam h s) * bridge L h s t) - t) - lam h t
    + (1 - lam h t) * (deriv (lam h) s * (L - s - bridge L h s t) - lam h s
        - (1 - lam h s) * ((L - 2 * h) / (s + t)))

theorem hasDerivAt_interpolation_line (L h s t : ℝ) :
    HasDerivAt (fun r => interpolation L h (s + r) (t - r)) (interpolationLineDeriv L h s t) 0 := by
  have hA : HasDerivAt (fun r : ℝ => t - r) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub t
  have hB : HasDerivAt (fun r : ℝ => s + r) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add s
  have hlt : HasDerivAt (fun r => lam h (t - r)) (-(deriv (lam h) t)) 0 := by
    have := HasDerivAt.comp_const_sub (f := lam h) t 0 (by rw [sub_zero]; exact hasDerivAt_lam h t)
    exact this
  have hls : HasDerivAt (fun r => lam h (s + r)) (deriv (lam h) s) 0 := by
    have := HasDerivAt.comp_const_add (f := lam h) s 0 (by rw [add_zero]; exact hasDerivAt_lam h s)
    exact this
  have hbr : HasDerivAt (fun r => bridge L h (s + r) (t - r)) ((L - 2 * h) * (-1 / (s + t))) 0 := by
    have heq : (fun r => bridge L h (s + r) (t - r)) =
        fun r => h + (L - 2 * h) * ((t - r) / (s + t)) := by
      funext r
      simp only [bridge]
      congr 2
      ring
    rw [heq]
    exact ((hA.div_const (s + t)).const_mul (L - 2 * h)).const_add h
  have hQ : HasDerivAt (fun r => lam h (s + r) * (L - (s + r)) + (1 - lam h (s + r)) *
      bridge L h (s + r) (t - r))
      (deriv (lam h) s * (L - (s + 0)) + lam h (s + 0) * (-1) +
        ((-(deriv (lam h) s)) * bridge L h (s + 0) (t - 0) +
          (1 - lam h (s + 0)) * ((L - 2 * h) * (-1 / (s + t))))) 0 :=
    (hls.mul (hB.const_sub L)).add ((hls.const_sub 1).mul hbr)
  have hmain := (hlt.mul hA).add ((hlt.const_sub 1).mul hQ)
  refine hmain.congr_deriv ?_
  simp only [add_zero, sub_zero]
  unfold interpolationLineDeriv
  ring

theorem interpolationLineDeriv_neg (hh : 0 < h) {L s t : ℝ} (hL : 2 * h < L) (hs : 0 < s) (ht : 0 < t)
    (hreg : h ≤ s ∨ h ≤ t) : interpolationLineDeriv L h s t < 0 := by
  have hst : 0 < s + t := by linarith
  obtain ⟨hB1, hB2⟩ := bridge_mem (L := L) hL.le hs.le ht.le hst
  have hc : 0 < (L - 2 * h) / (s + t) := div_pos (by linarith) hst
  unfold interpolationLineDeriv
  rcases le_or_gt t (h / 2) with ht1 | ht1
  · rw [lam_eq_one hh ht1, deriv_lam_eq_zero_of_le_half hh ht1]
    ring_nf
    norm_num
  rcases lt_or_ge t h with ht2 | ht2
  · have hs2 : h ≤ s := hreg.resolve_right (not_le.2 ht2)
    rw [lam_eq_zero hh hs2, deriv_lam_eq_zero_of_le hh hs2]
    have hl0 := lam_pos hh ht2
    have hl1 := lam_le_one h t
    have hd := deriv_lam_nonpos hh t
    have h1 : deriv (lam h) t * (bridge L h s t - t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hd (by linarith)
    have h2 : 0 ≤ (1 - lam h t) * ((L - 2 * h) / (s + t)) :=
      mul_nonneg (sub_nonneg.2 hl1) hc.le
    nlinarith
  · rw [lam_eq_zero hh ht2, deriv_lam_eq_zero_of_le hh ht2]
    rcases le_or_gt h s with hs2 | hs2
    · rw [lam_eq_zero hh hs2, deriv_lam_eq_zero_of_le hh hs2]
      nlinarith
    · have hd := deriv_lam_nonpos hh s
      have h1 : deriv (lam h) s * (L - s - bridge L h s t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hd (by linarith)
      have hl0 := lam_nonneg h s
      have hl1 := lam_le_one h s
      have h2 : 0 ≤ (1 - lam h s) * ((L - 2 * h) / (s + t)) :=
        mul_nonneg (sub_nonneg.2 hl1) hc.le
      rcases hl0.eq_or_lt with h0 | h0
      · rw [← h0] at h2 ⊢
        nlinarith
      · nlinarith

theorem contDiffAt_interpolation_pair (L h : ℝ) {p : ℝ × ℝ} (hp : p.1 + p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => interpolation L h p.1 p.2) p := by
  have hl : ∀ q : ℝ × ℝ → ℝ, ContDiffAt ℝ ∞ q p → ContDiffAt ℝ ∞ (fun x => lam h (q x)) p :=
    fun q hq => (contDiff_lam h).contDiffAt.comp p hq
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.1) p := contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.2) p := contDiffAt_snd
  have hbr : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => bridge L h p.1 p.2) p := by
    unfold bridge
    exact contDiffAt_const.add (contDiffAt_const.mul (h2.div (h1.add h2) hp))
  unfold interpolation
  exact ((hl _ h2).mul h2).add ((contDiffAt_const.sub (hl _ h2)).mul
    (((hl _ h1).mul (contDiffAt_const.sub h1)).add ((contDiffAt_const.sub (hl _ h1)).mul hbr)))

end CancelInterp

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : IndexZeroCancellingPair I f a' b' p q}

theorem two_η₀_lt (c : IndexZeroCancellingPair I f a' b' p q) : 2 * c.η₀ < b' - a' := by
  have h1 := c.a'_add_η₀_lt_f_p
  have h2 := c.f_q_add_η₀_lt_b'
  have h3 := c.hlt
  have h4 := c.hε
  linarith

namespace CancelConsts

variable (k : c.CancelConsts) (hk : k.Good)

open scoped Classical in
def τ₀ (x : M) : ℝ :=
  if h : f x ∈ Icc a' b' then Classical.choose (k.reaches_bottom hk h) else f x - a'

open scoped Classical in
def τ₁ (x : M) : ℝ :=
  if h : f x ∈ Icc a' b' then Classical.choose (k.reaches_top hk h) else b' - f x

theorem τ₀_spec {x : M} (hx : f x ∈ Icc a' b') :
    0 ≤ k.τ₀ hk x ∧ f (k.cancellationFlow (k.τ₀ hk x) x) = a' ∧ ∀ s ∈ Ico 0 (k.τ₀ hk x), a' < f (k.cancellationFlow s x) := by
  have := Classical.choose_spec (k.reaches_bottom hk hx)
  unfold τ₀
  rw [dite_eq_left hx]
  exact this

theorem τ₁_spec {x : M} (hx : f x ∈ Icc a' b') :
    0 ≤ k.τ₁ hk x ∧ f (k.cancellationFlow (-k.τ₁ hk x) x) = b' ∧
      ∀ s ∈ Ico 0 (k.τ₁ hk x), f (k.cancellationFlow (-s) x) < b' := by
  have := Classical.choose_spec (k.reaches_top hk hx)
  unfold τ₁
  rw [dite_eq_left hx]
  exact this

theorem τ₀_unique {x : M} (hx : f x ∈ Icc a' b') {t : ℝ} (ht : 0 ≤ t) (hf : f (k.cancellationFlow t x) = a')
    (hlt : ∀ s ∈ Ico 0 t, a' < f (k.cancellationFlow s x)) : t = k.τ₀ hk x := by
  obtain ⟨h0, h1, h2⟩ := k.τ₀_spec hk hx
  rcases lt_trichotomy t (k.τ₀ hk x) with h | h | h
  · exact absurd hf (h2 t ⟨ht, h⟩).ne'
  · exact h
  · exact absurd h1 (hlt _ ⟨h0, h⟩).ne'

theorem τ₁_unique {x : M} (hx : f x ∈ Icc a' b') {t : ℝ} (ht : 0 ≤ t)
    (hf : f (k.cancellationFlow (-t) x) = b') (hlt : ∀ s ∈ Ico 0 t, f (k.cancellationFlow (-s) x) < b') : t = k.τ₁ hk x := by
  obtain ⟨h0, h1, h2⟩ := k.τ₁_spec hk hx
  rcases lt_trichotomy t (k.τ₁ hk x) with h | h | h
  · exact absurd hf (h2 t ⟨ht, h⟩).ne
  · exact h
  · exact absurd h1 (hlt _ ⟨h0, h⟩).ne

theorem τ₀_pos {x : M} (hx : f x ∈ Icc a' b') (h : a' < f x) : 0 < k.τ₀ hk x := by
  obtain ⟨h0, h1, -⟩ := k.τ₀_spec hk hx
  refine lt_of_le_of_ne h0 fun heq => ?_
  rw [← heq, k.cancellationFlow_zero] at h1
  exact h.ne' h1

theorem τ₁_pos {x : M} (hx : f x ∈ Icc a' b') (h : f x < b') : 0 < k.τ₁ hk x := by
  obtain ⟨h0, h1, -⟩ := k.τ₁_spec hk hx
  refine lt_of_le_of_ne h0 fun heq => ?_
  rw [← heq, neg_zero, k.cancellationFlow_zero] at h1
  exact h.ne h1

theorem τ₀_add {x : M} (hx : f x ∈ Icc a' b') {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hlt : ∀ s ∈ Icc 0 t₁, a' < f (k.cancellationFlow s x)) : k.τ₀ hk x = t₁ + k.τ₀ hk (k.cancellationFlow t₁ x) := by
  have hy : f (k.cancellationFlow t₁ x) ∈ Icc a' b' :=
    ⟨(hlt t₁ (right_mem_Icc.2 ht₁)).le, k.f_cancellationFlow_le_b' hx.2 ht₁⟩
  obtain ⟨h0, h1, h2⟩ := k.τ₀_spec hk hy
  symm
  apply k.τ₀_unique hk hx (by linarith)
  · rw [← k.cancellationFlow_cancellationFlow]; exact h1
  · intro s hs
    rcases le_or_gt s t₁ with h | h
    · exact hlt s ⟨hs.1, h⟩
    · have := h2 (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rwa [k.cancellationFlow_cancellationFlow, add_sub_cancel] at this

theorem τ₁_add {x : M} (hx : f x ∈ Icc a' b') {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hlt : ∀ s ∈ Icc 0 t₁, f (k.cancellationFlow (-s) x) < b') :
    k.τ₁ hk x = t₁ + k.τ₁ hk (k.cancellationFlow (-t₁) x) := by
  have hy : f (k.cancellationFlow (-t₁) x) ∈ Icc a' b' :=
    ⟨k.f_cancellationFlow_neg_ge_a' hx.1 ht₁, (hlt t₁ (right_mem_Icc.2 ht₁)).le⟩
  obtain ⟨h0, h1, h2⟩ := k.τ₁_spec hk hy
  symm
  apply k.τ₁_unique hk hx (by linarith)
  · rw [k.cancellationFlow_cancellationFlow] at h1; rwa [neg_add]
  · intro s hs
    rcases le_or_gt s t₁ with h | h
    · exact hlt s ⟨hs.1, h⟩
    · have := h2 (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rwa [k.cancellationFlow_cancellationFlow, show -t₁ + -(s - t₁) = -s by ring] at this

theorem τ₀_collar {x : M} (h1 : a' ≤ f x) (h2 : f x < a' + c.η₀) :
    k.τ₀ hk x = f x - a' := by
  have hx : f x ∈ Icc a' b' := ⟨h1, by linarith [c.η₀_pos, c.a'_add_η₀_lt_f_p, c.f_p_mem.2]⟩
  have hflow : ∀ s, 0 ≤ s → k.cancellationFlow s x = c.D.flow s x := fun s hs => k.cancellationFlow_eq_flow_of_f_lt h2 hs
  have hup : ∀ s, 0 ≤ s → f (k.cancellationFlow s x) ≤ f x := fun s hs => by
    rw [hflow s hs]; exact f_flow_le c.hfs x hs
  have hlow : ∀ s, 0 ≤ s → f x - s ≤ f (k.cancellationFlow s x) := fun s hs => by
    rw [hflow s hs]; exact sub_le_f_flow c.hfs x hs
  symm
  apply k.τ₀_unique hk hx (by linarith)
  · rw [k.f_cancellationFlow_lower_collar (by linarith) (fun s hs =>
      ⟨by linarith [hlow s hs.1, hs.2], by linarith [hup s hs.1]⟩)]
    ring
  · intro s hs
    linarith [hlow s hs.1, hs.2]

theorem τ₁_collar {x : M} (h1 : b' - c.η₀ < f x) (h2 : f x ≤ b') :
    k.τ₁ hk x = b' - f x := by
  have hx : f x ∈ Icc a' b' := ⟨by linarith [c.η₀_pos, c.f_q_add_η₀_lt_b', c.f_q_mem.1], h2⟩
  have hflow : ∀ s, 0 ≤ s → k.cancellationFlow (-s) x = c.D.flow (-s) x := fun s hs =>
    k.cancellationFlow_eq_flow_of_lt_f h1 (by linarith)
  have hup : ∀ s, 0 ≤ s → f (k.cancellationFlow (-s) x) ≤ f x + s := fun s hs => by
    rw [hflow s hs]
    have := f_flow_le_sub_of_nonpos (D := c.D) c.hfs x (t := -s) (by linarith)
    linarith
  have hlow : ∀ s, 0 ≤ s → f x ≤ f (k.cancellationFlow (-s) x) := fun s hs => by
    rw [hflow s hs]; exact le_f_flow_of_nonpos c.hfs x (by linarith)
  have hcol : ∀ s ∈ Icc 0 (b' - f x),
      b' - c.η₀ < f (k.cancellationFlow (-s) x) ∧ f (k.cancellationFlow (-s) x) ≤ b' := fun s hs =>
    ⟨by linarith [hlow s hs.1], by linarith [hup s hs.1, hs.2]⟩
  symm
  apply k.τ₁_unique hk hx (by linarith)
  · have := k.f_cancellationFlow_upper_collar (x := k.cancellationFlow (-(b' - f x)) x) (t := b' - f x) (by linarith)
      (fun u hu => by
        rw [k.cancellationFlow_cancellationFlow, show -(b' - f x) + u = -(b' - f x - u) by ring]
        exact hcol (b' - f x - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    rw [k.cancellationFlow_cancellationFlow_neg] at this
    linarith
  · intro s hs
    linarith [hup s hs.1, hs.2]

theorem f_eq_add_τ₀_of_lt {x : M} (hx : f x ∈ Icc a' b') (h : k.τ₀ hk x < c.η₀) :
    f x = a' + k.τ₀ hk x := by
  obtain ⟨h0, h1, h2⟩ := k.τ₀_spec hk hx
  obtain ⟨t, ht⟩ : ∃ t, k.τ₀ hk x = t := ⟨_, rfl⟩
  rw [ht] at h0 h1 h2 h ⊢
  have hge : ∀ s ∈ Icc 0 t, a' ≤ f (k.cancellationFlow s x) := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h, h1]
    · exact (h2 s ⟨hs.1, h⟩).le
  have hlt : ∀ s ∈ Icc 0 t, f (k.cancellationFlow s x) < a' + c.η₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀, hs₀f⟩ := hcon
    have hBc : IsCompact {s | s ∈ Icc 0 t ∧ a' + c.η₀ ≤ f (k.cancellationFlow s x)} :=
      isCompact_Icc.inter_right
        (isClosed_Ici.preimage (c.hfs.continuous.comp (k.continuous_cancellationFlow_curve x)))
    obtain ⟨s₁, ⟨hs₁I, hs₁f⟩, hmax⟩ := hBc.exists_isGreatest ⟨s₀, hs₀, hs₀f⟩
    have hs₁t : s₁ < t := lt_of_le_of_ne hs₁I.2 fun h => by
      rw [h, h1] at hs₁f; linarith [c.η₀_pos]
    have hcol : ∀ s ∈ Ioc s₁ t, a' ≤ f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) < a' + c.η₀ := fun s hs => by
      refine ⟨hge s ⟨by linarith [hs.1, hs₁I.1], hs.2⟩, ?_⟩
      by_contra hc
      have := hmax ⟨⟨by linarith [hs.1, hs₁I.1], hs.2⟩, not_lt.1 hc⟩
      linarith [hs.1]
    have hval : ∀ s ∈ Ioc s₁ t, f (k.cancellationFlow s x) = a' + t - s := fun s hs => by
      have := k.f_cancellationFlow_lower_collar (x := k.cancellationFlow s x) (t := t - s) (by linarith [hs.2]) (fun u hu => by
        rw [k.cancellationFlow_cancellationFlow]; exact hcol (s + u) ⟨by linarith [hu.1, hs.1], by linarith [hu.2]⟩)
      rw [k.cancellationFlow_cancellationFlow, add_sub_cancel, h1] at this
      linarith
    have hcont : Tendsto (fun s => f (k.cancellationFlow s x)) (𝓝[>] s₁) (𝓝 (f (k.cancellationFlow s₁ x))) :=
      ((c.hfs.continuous.comp (k.continuous_cancellationFlow_curve x)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    have hlin : Tendsto (fun s => f (k.cancellationFlow s x)) (𝓝[>] s₁) (𝓝 (a' + t - s₁)) := by
      have : Tendsto (fun s : ℝ => a' + t - s) (𝓝[>] s₁) (𝓝 (a' + t - s₁)) :=
        (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hs₁t] with s hs
      exact (hval s ⟨hs.1, hs.2.le⟩).symm
    have heq := tendsto_nhds_unique hcont hlin
    linarith [hs₁I.1]
  rw [k.f_cancellationFlow_lower_collar h0 (fun s hs => ⟨hge s hs, hlt s hs⟩)] at h1
  linarith

theorem f_eq_sub_τ₁_of_lt {x : M} (hx : f x ∈ Icc a' b') (h : k.τ₁ hk x < c.η₀) :
    f x = b' - k.τ₁ hk x := by
  obtain ⟨h0, h1, h2⟩ := k.τ₁_spec hk hx
  obtain ⟨t, ht⟩ : ∃ t, k.τ₁ hk x = t := ⟨_, rfl⟩
  rw [ht] at h0 h1 h2 h ⊢
  have hle : ∀ s ∈ Icc 0 t, f (k.cancellationFlow (-s) x) ≤ b' := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h, h1]
    · exact (h2 s ⟨hs.1, h⟩).le
  have hgt : ∀ s ∈ Icc 0 t, b' - c.η₀ < f (k.cancellationFlow (-s) x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀, hs₀f⟩ := hcon
    have hBc : IsCompact {s | s ∈ Icc 0 t ∧ f (k.cancellationFlow (-s) x) ≤ b' - c.η₀} :=
      isCompact_Icc.inter_right
        (isClosed_Iic.preimage (c.hfs.continuous.comp (k.continuous_cancellationFlow_neg_curve x)))
    obtain ⟨s₁, ⟨hs₁I, hs₁f⟩, hmax⟩ := hBc.exists_isGreatest ⟨s₀, hs₀, hs₀f⟩
    have hs₁t : s₁ < t := lt_of_le_of_ne hs₁I.2 fun h => by
      rw [h, h1] at hs₁f; linarith [c.η₀_pos]
    have hcol : ∀ s ∈ Ioc s₁ t, b' - c.η₀ < f (k.cancellationFlow (-s) x) ∧ f (k.cancellationFlow (-s) x) ≤ b' :=
      fun s hs => by
      refine ⟨?_, hle s ⟨by linarith [hs.1, hs₁I.1], hs.2⟩⟩
      by_contra hc
      have := hmax ⟨⟨by linarith [hs.1, hs₁I.1], hs.2⟩, not_lt.1 hc⟩
      linarith [hs.1]
    have hval : ∀ s ∈ Ioc s₁ t, f (k.cancellationFlow (-s) x) = b' - t + s := fun s hs => by
      have := k.f_cancellationFlow_upper_collar (x := k.cancellationFlow (-t) x) (t := t - s) (by linarith [hs.2])
        (fun u hu => by
          rw [k.cancellationFlow_cancellationFlow, show -t + u = -(t - u) by ring]
          exact hcol (t - u) ⟨by linarith [hu.2, hs.1], by linarith [hu.1]⟩)
      rw [k.cancellationFlow_cancellationFlow, show -t + (t - s) = -s by ring, h1] at this
      linarith
    have hcont : Tendsto (fun s => f (k.cancellationFlow (-s) x)) (𝓝[>] s₁) (𝓝 (f (k.cancellationFlow (-s₁) x))) :=
      ((c.hfs.continuous.comp (k.continuous_cancellationFlow_neg_curve x)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    have hlin : Tendsto (fun s => f (k.cancellationFlow (-s) x)) (𝓝[>] s₁) (𝓝 (b' - t + s₁)) := by
      have : Tendsto (fun s : ℝ => b' - t + s) (𝓝[>] s₁) (𝓝 (b' - t + s₁)) :=
        (continuous_const.add continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hs₁t] with s hs
      exact (hval s ⟨hs.1, hs.2.le⟩).symm
    have heq := tendsto_nhds_unique hcont hlin
    linarith [hs₁I.1]
  have := k.f_cancellationFlow_upper_collar (x := k.cancellationFlow (-t) x) (t := t) h0 (fun u hu => by
    rw [k.cancellationFlow_cancellationFlow, show -t + u = -(t - u) by ring]
    exact ⟨hgt (t - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩,
      hle (t - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩)
  rw [k.cancellationFlow_cancellationFlow_neg, h1] at this
  linarith

theorem η₀_le_τ₀_of_le {x : M} (hx : f x ∈ Icc a' b') (h : a' + c.η₀ ≤ f x) :
    c.η₀ ≤ k.τ₀ hk x := by
  by_contra hc
  have := k.f_eq_add_τ₀_of_lt hk hx (not_le.1 hc)
  linarith

theorem η₀_le_τ₁_of_le {x : M} (hx : f x ∈ Icc a' b') (h : f x ≤ b' - c.η₀) :
    c.η₀ ≤ k.τ₁ hk x := by
  by_contra hc
  have := k.f_eq_sub_τ₁_of_lt hk hx (not_le.1 hc)
  linarith

theorem η₀_le_τ₁_or_τ₀ {x : M} (hx : f x ∈ Icc a' b') :
    c.η₀ ≤ k.τ₁ hk x ∨ c.η₀ ≤ k.τ₀ hk x := by
  rcases le_or_gt (f x) (b' - c.η₀) with h | h
  · exact Or.inl (k.η₀_le_τ₁_of_le hk hx h)
  · exact Or.inr (k.η₀_le_τ₀_of_le hk hx (by linarith [c.two_η₀_lt]))

theorem exists_shift_τ₀ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ∃ t₁, 0 ≤ t₁ ∧ ∀ᶠ x in 𝓝 x₀, k.τ₀ hk x = t₁ + (f (k.cancellationFlow t₁ x) - a') := by
  have hx₀' : f x₀ ∈ Icc a' b' := Ioo_subset_Icc_self hx₀
  obtain ⟨-, h1, h2⟩ := k.τ₀_spec hk hx₀'
  have hTpos : 0 < k.τ₀ hk x₀ := k.τ₀_pos hk hx₀' hx₀.1
  have hev : ∀ᶠ s in 𝓝[<] k.τ₀ hk x₀, f (k.cancellationFlow s x₀) < a' + c.η₀ := by
    have hc : ContinuousAt (fun s => f (k.cancellationFlow s x₀)) (k.τ₀ hk x₀) :=
      (c.hfs.continuous.comp (k.continuous_cancellationFlow_curve x₀)).continuousAt
    exact (hc.eventually_lt continuousAt_const (by rw [h1]; linarith [c.η₀_pos])).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t₁, ht₁f, ht₁⟩ := (hev.and (Ioo_mem_nhdsLT hTpos)).exists
  refine ⟨t₁, ht₁.1.le, ?_⟩
  have hU₁ : ∀ᶠ x in 𝓝 x₀, ∀ s ∈ Icc 0 t₁, a' < f (k.cancellationFlow s x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hcont : Continuous (fun z : M × ℝ => f (k.cancellationFlow z.2 z.1)) :=
      c.hfs.continuous.comp (k.continuous_cancellationFlow_joint.comp (continuous_snd.prodMk continuous_fst))
    exact continuousAt_const.eventually_lt hcont.continuousAt
      (h2 s ⟨hs.1, by linarith [hs.2, ht₁.2]⟩)
  have hU₂ : ∀ᶠ x in 𝓝 x₀, a' < f (k.cancellationFlow t₁ x) ∧ f (k.cancellationFlow t₁ x) < a' + c.η₀ := by
    have hc : ContinuousAt (fun x => f (k.cancellationFlow t₁ x)) x₀ :=
      (c.hfs.continuous.comp (k.continuous_cancellationFlow t₁)).continuousAt
    exact (continuousAt_const.eventually_lt hc (h2 t₁ ⟨ht₁.1.le, ht₁.2⟩)).and
      (hc.eventually_lt continuousAt_const ht₁f)
  have hU₃ : ∀ᶠ x in 𝓝 x₀, f x ∈ Ioo a' b' :=
    c.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx₀)
  filter_upwards [hU₁, hU₂, hU₃] with x h1x h2x h3x
  rw [k.τ₀_add hk (Ioo_subset_Icc_self h3x) ht₁.1.le h1x, k.τ₀_collar hk h2x.1.le h2x.2]

theorem exists_shift_τ₁ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ∃ t₁, 0 ≤ t₁ ∧ ∀ᶠ x in 𝓝 x₀, k.τ₁ hk x = t₁ + (b' - f (k.cancellationFlow (-t₁) x)) := by
  have hx₀' : f x₀ ∈ Icc a' b' := Ioo_subset_Icc_self hx₀
  obtain ⟨-, h1, h2⟩ := k.τ₁_spec hk hx₀'
  have hTpos : 0 < k.τ₁ hk x₀ := k.τ₁_pos hk hx₀' hx₀.2
  have hev : ∀ᶠ s in 𝓝[<] k.τ₁ hk x₀, b' - c.η₀ < f (k.cancellationFlow (-s) x₀) := by
    have hc : ContinuousAt (fun s => f (k.cancellationFlow (-s) x₀)) (k.τ₁ hk x₀) :=
      (c.hfs.continuous.comp (k.continuous_cancellationFlow_neg_curve x₀)).continuousAt
    exact (continuousAt_const.eventually_lt hc (by rw [h1]; linarith [c.η₀_pos])).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t₁, ht₁f, ht₁⟩ := (hev.and (Ioo_mem_nhdsLT hTpos)).exists
  refine ⟨t₁, ht₁.1.le, ?_⟩
  have hU₁ : ∀ᶠ x in 𝓝 x₀, ∀ s ∈ Icc 0 t₁, f (k.cancellationFlow (-s) x) < b' := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hcont : Continuous (fun z : M × ℝ => f (k.cancellationFlow (-z.2) z.1)) :=
      c.hfs.continuous.comp
        (k.continuous_cancellationFlow_joint.comp (continuous_snd.neg.prodMk continuous_fst))
    exact hcont.continuousAt.eventually_lt continuousAt_const
      (h2 s ⟨hs.1, by linarith [hs.2, ht₁.2]⟩)
  have hU₂ : ∀ᶠ x in 𝓝 x₀, b' - c.η₀ < f (k.cancellationFlow (-t₁) x) := by
    have hc : ContinuousAt (fun x => f (k.cancellationFlow (-t₁) x)) x₀ :=
      (c.hfs.continuous.comp (k.continuous_cancellationFlow (-t₁))).continuousAt
    exact continuousAt_const.eventually_lt hc ht₁f
  have hU₃ : ∀ᶠ x in 𝓝 x₀, f x ∈ Ioo a' b' :=
    c.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx₀)
  filter_upwards [hU₁, hU₂, hU₃] with x h1x h2x h3x
  rw [k.τ₁_add hk (Ioo_subset_Icc_self h3x) ht₁.1.le h1x,
    k.τ₁_collar hk h2x (h1x t₁ (right_mem_Icc.2 ht₁.1.le)).le]

theorem contMDiffAt_τ₀ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (k.τ₀ hk) x₀ := by
  obtain ⟨t₁, -, hev⟩ := k.exists_shift_τ₀ hk hx₀
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => t₁ + (f (k.cancellationFlow t₁ x) - a')) x₀ :=
    contMDiffAt_const.add
      ((c.hfs.contMDiffAt.comp x₀ (k.contMDiff_cancellationFlow t₁).contMDiffAt).sub contMDiffAt_const)
  exact hs.congr_of_eventuallyEq hev

theorem contMDiffAt_τ₁ {x₀ : M} (hx₀ : f x₀ ∈ Ioo a' b') :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (k.τ₁ hk) x₀ := by
  obtain ⟨t₁, -, hev⟩ := k.exists_shift_τ₁ hk hx₀
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => t₁ + (b' - f (k.cancellationFlow (-t₁) x))) x₀ :=
    contMDiffAt_const.add
      (contMDiffAt_const.sub (c.hfs.contMDiffAt.comp x₀ (k.contMDiff_cancellationFlow (-t₁)).contMDiffAt))
  exact hs.congr_of_eventuallyEq hev

theorem contMDiffOn_τ₀ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (k.τ₀ hk) (f ⁻¹' Ioo a' b') :=
  fun _ hx => (k.contMDiffAt_τ₀ hk hx).contMDiffWithinAt

theorem contMDiffOn_τ₁ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (k.τ₁ hk) (f ⁻¹' Ioo a' b') :=
  fun _ hx => (k.contMDiffAt_τ₁ hk hx).contMDiffWithinAt

theorem eventually_τ_cancellationFlow {x : M} (hx : f x ∈ Ioo a' b') :
    ∀ᶠ r in 𝓝 (0 : ℝ), f (k.cancellationFlow r x) ∈ Ioo a' b' ∧ k.τ₀ hk (k.cancellationFlow r x) = k.τ₀ hk x - r ∧
      k.τ₁ hk (k.cancellationFlow r x) = k.τ₁ hk x + r := by
  have hx' : f x ∈ Icc a' b' := Ioo_subset_Icc_self hx
  obtain ⟨-, -, h2⟩ := k.τ₀_spec hk hx'
  obtain ⟨-, -, h2'⟩ := k.τ₁_spec hk hx'
  have hτ₀ : 0 < k.τ₀ hk x := k.τ₀_pos hk hx' hx.1
  have hτ₁ : 0 < k.τ₁ hk x := k.τ₁_pos hk hx' hx.2
  have hfwd : ∀ u, 0 ≤ u → f (k.cancellationFlow u x) < b' := fun u hu => by
    rcases hu.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hx.2
    · by_contra hc
      have := k.b'_lt_f_cancellationFlow_of_le (not_lt.1 hc) h
      rw [k.cancellationFlow_zero] at this
      linarith [hx.2]
  have hbwd : ∀ u, 0 ≤ u → a' < f (k.cancellationFlow (-u) x) := fun u hu => by
    rcases hu.eq_or_lt with h | h
    · rw [← h, neg_zero, k.cancellationFlow_zero]; exact hx.1
    · by_contra hc
      have := k.f_cancellationFlow_lt_of_le_a' (not_lt.1 hc) (by linarith : -u < 0)
      rw [k.cancellationFlow_zero] at this
      linarith [hx.1]
  filter_upwards [Ioo_mem_nhds (by linarith : -k.τ₁ hk x < 0) hτ₀] with r hr
  rcases le_or_gt 0 r with hr0 | hr0
  · have hfr : f (k.cancellationFlow r x) ∈ Ioo a' b' := ⟨h2 r ⟨hr0, hr.2⟩, hfwd r hr0⟩
    refine ⟨hfr, ?_, ?_⟩
    · have := k.τ₀_add hk hx' hr0 (fun s hs => h2 s ⟨hs.1, by linarith [hs.2, hr.2]⟩)
      linarith
    · have := k.τ₁_add hk (Ioo_subset_Icc_self hfr) hr0 (fun s hs => by
        rw [k.cancellationFlow_cancellationFlow]; exact hfwd (r + -s) (by linarith [hs.2]))
      rw [k.cancellationFlow_neg_cancellationFlow] at this
      linarith
  · obtain ⟨v, hv, rfl⟩ : ∃ v, 0 < v ∧ r = -v := ⟨-r, by linarith, by ring⟩
    have hfr : f (k.cancellationFlow (-v) x) ∈ Ioo a' b' := ⟨hbwd v hv.le, h2' v ⟨hv.le, by linarith [hr.1]⟩⟩
    refine ⟨hfr, ?_, ?_⟩
    · have := k.τ₀_add hk (Ioo_subset_Icc_self hfr) hv.le (fun s hs => by
        rw [k.cancellationFlow_cancellationFlow, show -v + s = -(v - s) by ring]; exact hbwd (v - s) (by linarith [hs.2]))
      rw [k.cancellationFlow_cancellationFlow_neg] at this
      linarith
    · have := k.τ₁_add hk hx' hv.le (fun s hs => h2' s ⟨hs.1, by linarith [hs.2, hr.1]⟩)
      linarith

open scoped Classical in
def g (x : M) : ℝ :=
  if f x ∈ Ioo a' b' then
    a' + CancelInterp.interpolation (b' - a') c.η₀ (k.τ₁ hk x) (k.τ₀ hk x)
  else f x

theorem g_of_mem {x : M} (hx : f x ∈ Ioo a' b') :
    k.g hk x = a' + CancelInterp.interpolation (b' - a') c.η₀ (k.τ₁ hk x) (k.τ₀ hk x) := by
  unfold g; rw [ite_eq_left hx]

theorem g_of_notMem {x : M} (hx : f x ∉ Ioo a' b') : k.g hk x = f x := by
  unfold g; rw [ite_eq_right hx]

theorem g_eq_f_of_le {x : M} (hx : f x ≤ a' + c.η₀ / 2) : k.g hk x = f x := by
  by_cases h : f x ∈ Ioo a' b'
  · rw [k.g_of_mem hk h, k.τ₀_collar hk h.1.le (by linarith [c.η₀_pos]),
      CancelInterp.interpolation_of_le_half c.η₀_pos (by linarith)]
    ring
  · exact k.g_of_notMem hk h

theorem g_eq_f_of_ge {x : M} (hx : b' - c.η₀ / 2 ≤ f x) : k.g hk x = f x := by
  by_cases h : f x ∈ Ioo a' b'
  · have hτ₀ : c.η₀ ≤ k.τ₀ hk x :=
      k.η₀_le_τ₀_of_le hk (Ioo_subset_Icc_self h) (by linarith [c.two_η₀_lt, c.η₀_pos])
    rw [k.g_of_mem hk h, k.τ₁_collar hk (by linarith [c.η₀_pos]) h.2.le,
      CancelInterp.interpolation_of_le_half_left c.η₀_pos (by linarith) hτ₀]
    ring
  · exact k.g_of_notMem hk h

theorem g_mem_Ioo {x : M} (hx : f x ∈ Ioo a' b') : k.g hk x ∈ Ioo a' b' := by
  have hx' := Ioo_subset_Icc_self hx
  rw [k.g_of_mem hk hx]
  have h1 := CancelInterp.interpolation_pos c.η₀_pos c.two_η₀_lt (k.τ₁_pos hk hx' hx.2)
    (k.τ₀_pos hk hx' hx.1)
  have h2 := CancelInterp.interpolation_lt c.η₀_pos c.two_η₀_lt (k.τ₁_pos hk hx' hx.2)
    (k.τ₀_pos hk hx' hx.1)
  constructor <;> linarith

theorem modifiedWithin_g : ModifiedWithin f a' b' (k.g hk) :=
  ⟨fun _ hx => k.g_of_notMem hk hx, fun _ hx => k.g_mem_Ioo hk hx⟩

theorem contMDiff_g : ContMDiff I 𝓘(ℝ, ℝ) ∞ (k.g hk) := by
  intro x
  rcases lt_trichotomy (f x) a' with hlt | heq | hgt
  · have hev : k.g hk =ᶠ[𝓝 x] f := by
      filter_upwards [c.hfs.continuous.continuousAt.eventually_lt continuousAt_const
        (show f x < a' + c.η₀ / 2 by linarith [c.η₀_pos])] with y hy
      exact k.g_eq_f_of_le hk hy.le
    exact (c.hfs x).congr_of_eventuallyEq hev
  · have hev : k.g hk =ᶠ[𝓝 x] f := by
      filter_upwards [c.hfs.continuous.continuousAt.eventually_lt continuousAt_const
        (show f x < a' + c.η₀ / 2 by linarith [c.η₀_pos])] with y hy
      exact k.g_eq_f_of_le hk hy.le
    exact (c.hfs x).congr_of_eventuallyEq hev
  rcases lt_trichotomy (f x) b' with hlt' | heq' | hgt'
  · have hx : f x ∈ Ioo a' b' := ⟨hgt, hlt'⟩
    have hx' := Ioo_subset_Icc_self hx
    have hev : k.g hk =ᶠ[𝓝 x]
        fun y => a' + CancelInterp.interpolation (b' - a') c.η₀ (k.τ₁ hk y) (k.τ₀ hk y) := by
      filter_upwards [c.hfs.continuous.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hx)]
        with y hy
      exact k.g_of_mem hk hy
    have hne : k.τ₁ hk x + k.τ₀ hk x ≠ 0 := by
      have := k.τ₁_pos hk hx' hx.2
      have := k.τ₀_pos hk hx' hx.1
      linarith
    have hpair : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) ∞ (fun y => (k.τ₁ hk y, k.τ₀ hk y)) x :=
      (k.contMDiffAt_τ₁ hk hx).prodMk_space (k.contMDiffAt_τ₀ hk hx)
    have hS := ContDiffAt.comp_contMDiffAt (I := I) (f := fun y => (k.τ₁ hk y, k.τ₀ hk y))
      (x := x) (CancelInterp.contDiffAt_interpolation_pair (b' - a') c.η₀
        (p := (k.τ₁ hk x, k.τ₀ hk x)) hne) hpair
    have hS' : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => a' + CancelInterp.interpolation (b' - a') c.η₀ (k.τ₁ hk y) (k.τ₀ hk y)) x :=
      contMDiffAt_const.add hS
    exact hS'.congr_of_eventuallyEq hev
  · have hev : k.g hk =ᶠ[𝓝 x] f := by
      filter_upwards [continuousAt_const.eventually_lt c.hfs.continuous.continuousAt
        (show b' - c.η₀ / 2 < f x by linarith [c.η₀_pos])] with y hy
      exact k.g_eq_f_of_ge hk hy.le
    exact (c.hfs x).congr_of_eventuallyEq hev
  · have hev : k.g hk =ᶠ[𝓝 x] f := by
      filter_upwards [continuousAt_const.eventually_lt c.hfs.continuous.continuousAt
        (show b' - c.η₀ / 2 < f x by linarith [c.η₀_pos])] with y hy
      exact k.g_eq_f_of_ge hk hy.le
    exact (c.hfs x).congr_of_eventuallyEq hev

theorem hasDerivAt_g_cancellationFlow {x : M} (hx : f x ∈ Ioo a' b') :
    HasDerivAt (fun r => k.g hk (k.cancellationFlow r x))
      (CancelInterp.interpolationLineDeriv (b' - a') c.η₀ (k.τ₁ hk x) (k.τ₀ hk x)) 0 := by
  have h := (CancelInterp.hasDerivAt_interpolation_line (b' - a') c.η₀ (k.τ₁ hk x) (k.τ₀ hk x)).const_add a'
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [k.eventually_τ_cancellationFlow hk hx] with r hr
  rw [k.g_of_mem hk hr.1, hr.2.1, hr.2.2]

theorem interpolationLineDeriv_g_neg {x : M} (hx : f x ∈ Ioo a' b') :
    CancelInterp.interpolationLineDeriv (b' - a') c.η₀ (k.τ₁ hk x) (k.τ₀ hk x) < 0 :=
  CancelInterp.interpolationLineDeriv_neg c.η₀_pos c.two_η₀_lt (k.τ₁_pos hk (Ioo_subset_Icc_self hx) hx.2)
    (k.τ₀_pos hk (Ioo_subset_Icc_self hx) hx.1) (k.η₀_le_τ₁_or_τ₀ hk (Ioo_subset_Icc_self hx))

theorem not_isCriticalPointAt_g {x : M} (hx : k.g hk x ∈ Ioo a' b') : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (k.g hk) x := by
  have hfx : f x ∈ Ioo a' b' := by
    by_contra h
    rw [k.g_of_notMem hk h] at hx
    exact h hx
  intro hcrit
  have h1 := hasDerivAt_df_comp_integralCurve (k.g hk) (k.contMDiff_g hk) k.cancellationField
    (k.isMIntegralCurve_cancellationFlow x) 0
  have h2 := k.hasDerivAt_g_cancellationFlow hk hfx
  have hD := k.interpolationLineDeriv_g_neg hk hfx
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hcrit
  have h1' : HasDerivAt (fun r => k.g hk (k.cancellationFlow r x))
      ((mfderiv I 𝓘(ℝ, ℝ) (k.g hk) (k.cancellationFlow 0 x)) (k.cancellationField (k.cancellationFlow 0 x))) 0 := h1
  rw [k.cancellationFlow_zero, hcrit] at h1'
  have := h1'.unique h2
  rw [zero_apply] at this
  exact hD.ne this.symm

theorem morseStrip_g : MorseStrip I (k.g hk) a' b' := by
  refine ⟨k.contMDiff_g hk, c.hf.lt, ?_, ?_, ?_⟩
  · rw [(k.modifiedWithin_g hk).preimage_Icc]; exact c.hf.compact
  · intro x hx
    have hnot : f x ∉ Ioo a' b' := fun h => by
      have := k.g_mem_Ioo hk h
      rcases hx with hx | hx <;> rw [hx] at this <;> simp at this
    have hfx : f x = a' ∨ f x = b' := by rwa [k.g_of_notMem hk hnot] at hx
    have hev : k.g hk =ᶠ[𝓝 x] f := by
      rcases hfx with hfx | hfx
      · filter_upwards [c.hfs.continuous.continuousAt.eventually_lt continuousAt_const
          (show f x < a' + c.η₀ / 2 by linarith [c.η₀_pos])] with y hy
        exact k.g_eq_f_of_le hk hy.le
      · filter_upwards [continuousAt_const.eventually_lt c.hfs.continuous.continuousAt
          (show b' - c.η₀ / 2 < f x by linarith [c.η₀_pos])] with y hy
        exact k.g_eq_f_of_ge hk hy.le
    rw [MonotoneShift.isCriticalPointAt_congr_nhds hev]
    exact c.hf.regular x hfx
  · intro x hx hc
    exact absurd hc (k.not_isCriticalPointAt_g hk hx)

include k hk in
theorem exists_modification :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x :=
  ⟨k.g hk, k.modifiedWithin_g hk, k.morseStrip_g hk, fun _ hx => k.not_isCriticalPointAt_g hk hx⟩

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
