module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelFlowExit

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : IndexZeroCancellingPair I f a' b' p q}

namespace CancelConsts

variable (k : c.CancelConsts)

theorem continuous_cancellationFlow_neg_curve (x : M) : Continuous (fun s => k.cancellationFlow (-s) x) :=
  (k.continuous_cancellationFlow_curve x).comp continuous_neg

theorem hasDerivAt_f_cancellationFlow_neg (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (k.cancellationFlow (-s) x)) (-dfV I f k.cancellationField (k.cancellationFlow (-t) x)) t := by
  have h := (k.hasDerivAt_f_cancellationFlow x (-t)).comp t (hasDerivAt_neg t)
  simpa [Function.comp_def, mul_neg_one] using h

theorem f_cancellationFlow_le_b' {x : M} (hx : f x ≤ b') {t : ℝ} (ht : 0 ≤ t) : f (k.cancellationFlow t x) ≤ b' := by
  have hmain := nonpos_of_deriv_le_mul (h := fun s => f (k.cancellationFlow s x) - b')
    (h' := fun s => dfV I f k.cancellationField (k.cancellationFlow s x)) (K := 0) (a := 0) (b := t)
    (fun s _ => (k.hasDerivAt_f_cancellationFlow x s).sub_const b') (by simpa using hx)
    (fun s _ hle => by
      have hle' : b' ≤ f (k.cancellationFlow s x) := by simpa using hle
      have hnot : k.cancellationFlow s x ∉ k.perturbationSupportRegion := k.notMem_perturbationSupportRegion_of_lt_f (by linarith [c.η₀_pos])
      have := k.dfV_cancellationField_nonpos_of_notMem hnot
      simp only [zero_mul]; exact this)
  have := hmain t (right_mem_Icc.2 ht)
  simpa using this

theorem f_cancellationFlow_neg_ge_a' {x : M} (hx : a' ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    a' ≤ f (k.cancellationFlow (-t) x) := by
  have hmain := nonneg_of_deriv_ge_mul (h := fun s => f (k.cancellationFlow (-s) x) - a')
    (h' := fun s => -dfV I f k.cancellationField (k.cancellationFlow (-s) x)) (K := 0) (a := 0) (b := t)
    (fun s _ => (k.hasDerivAt_f_cancellationFlow_neg x s).sub_const a') (by simpa using hx)
    (fun s _ hle => by
      have hle' : f (k.cancellationFlow (-s) x) ≤ a' := by simpa using hle
      have hnot : k.cancellationFlow (-s) x ∉ k.perturbationSupportRegion := k.notMem_perturbationSupportRegion_of_f_lt (by linarith [c.η₀_pos])
      have := k.dfV_cancellationField_nonpos_of_notMem hnot
      simp only [zero_mul]; linarith)
  have := hmain t (right_mem_Icc.2 ht)
  simpa using this

theorem f_cancellationFlow_le_of_lt_collar {y : M} (hy : f y < a' + c.η₀) {r : ℝ} (hr : 0 ≤ r) :
    f (k.cancellationFlow r y) ≤ f y := by
  rw [k.cancellationFlow_eq_flow_of_f_lt hy hr]; exact f_flow_le c.hfs y hr

theorem le_f_cancellationFlow_of_lt_collar {y : M} (hy : b' - c.η₀ < f y) {r : ℝ} (hr : r ≤ 0) :
    f y ≤ f (k.cancellationFlow r y) := by
  rw [k.cancellationFlow_eq_flow_of_lt_f hy hr]; exact le_f_flow_of_nonpos c.hfs y hr

theorem f_cancellationFlow_lt_of_le_a' {x : M} {t₀ s : ℝ} (h : f (k.cancellationFlow t₀ x) ≤ a') (hs : t₀ < s) :
    f (k.cancellationFlow s x) < a' := by
  obtain ⟨y, hy⟩ : ∃ y, k.cancellationFlow t₀ x = y := ⟨_, rfl⟩
  rw [hy] at h
  have hsy : k.cancellationFlow s x = k.cancellationFlow (s - t₀) y := by rw [← hy, k.cancellationFlow_cancellationFlow, add_sub_cancel]
  have hr : 0 < s - t₀ := by linarith
  rw [hsy]
  rcases h.lt_or_eq with hlt | heq
  · exact (k.f_cancellationFlow_le_of_lt_collar (by linarith [c.η₀_pos]) hr.le).trans_lt hlt
  · have hd : HasDerivAt (fun u => f (k.cancellationFlow u y)) (-1) 0 := by
      have := k.hasDerivAt_f_cancellationFlow y 0
      rwa [k.cancellationFlow_zero, k.dfV_cancellationField_lower_collar heq.ge (by linarith [c.η₀_pos])] at this
    have hev := eventually_lt_of_hasDerivAt_neg (by norm_num : (-1 : ℝ) < 0) hd
    obtain ⟨ε, hε1, hε2⟩ := (hev.and (Ioo_mem_nhdsGT hr)).exists
    rw [k.cancellationFlow_zero, heq] at hε1
    have hz : k.cancellationFlow (s - t₀) y = k.cancellationFlow (s - t₀ - ε) (k.cancellationFlow ε y) := by
      rw [k.cancellationFlow_cancellationFlow, add_sub_cancel]
    rw [hz]
    exact (k.f_cancellationFlow_le_of_lt_collar (by linarith [c.η₀_pos]) (by linarith [hε2.2])).trans_lt hε1

theorem b'_lt_f_cancellationFlow_of_le {x : M} {t₀ s : ℝ} (h : b' ≤ f (k.cancellationFlow t₀ x)) (hs : s < t₀) :
    b' < f (k.cancellationFlow s x) := by
  obtain ⟨y, hy⟩ : ∃ y, k.cancellationFlow t₀ x = y := ⟨_, rfl⟩
  rw [hy] at h
  have hsy : k.cancellationFlow s x = k.cancellationFlow (-(t₀ - s)) y := by rw [← hy, k.cancellationFlow_cancellationFlow]; congr 1; ring
  have hr : 0 < t₀ - s := by linarith
  rw [hsy]
  rcases h.lt_or_eq with hlt | heq
  · exact hlt.trans_le (k.le_f_cancellationFlow_of_lt_collar (by linarith [c.η₀_pos]) (by linarith))
  · have hd : HasDerivAt (fun u => f (k.cancellationFlow (-u) y)) 1 0 := by
      have := k.hasDerivAt_f_cancellationFlow_neg y 0
      rwa [neg_zero, k.cancellationFlow_zero, k.dfV_cancellationField_upper_collar (by linarith [c.η₀_pos]) heq.ge,
        neg_neg] at this
    have hev := eventually_gt_of_hasDerivAt_pos (by norm_num : (0 : ℝ) < 1) hd
    obtain ⟨ε, hε1, hε2⟩ := (hev.and (Ioo_mem_nhdsGT hr)).exists
    rw [neg_zero, k.cancellationFlow_zero, ← heq] at hε1
    have hz : k.cancellationFlow (-(t₀ - s)) y = k.cancellationFlow (-(t₀ - s - ε)) (k.cancellationFlow (-ε) y) := by
      rw [k.cancellationFlow_cancellationFlow]; congr 1; ring
    rw [hz]
    exact hε1.trans_le (k.le_f_cancellationFlow_of_lt_collar (by linarith [c.η₀_pos]) (by linarith [hε2.2]))

theorem b'_lt_f_cancellationFlow_neg_of_lt {x : M} {t s : ℝ} (h : b' ≤ f (k.cancellationFlow (-t) x)) (hs : t < s) :
    b' < f (k.cancellationFlow (-s) x) :=
  k.b'_lt_f_cancellationFlow_of_le h (by linarith)

theorem exists_alphaLimit_subset {C : Set M} (hC : IsCompact C) {x : M}
    (hcon : ∀ t, 0 ≤ t → k.cancellationFlow (-t) x ∈ C) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ C ∧ ∀ t, MapsTo (k.cancellationFlow t) Ω Ω := by
  set ψ : Flow ℝ M := k.toFlow.reverse with hψ
  have hψ' : ∀ t y, ψ t y = k.cancellationFlow (-t) y := fun t y => rfl
  set Ω := omegaLimit atTop (⇑ψ) {x} with hΩ
  have himage : closure (image2 (⇑ψ) (Ici 0) {x}) ⊆ C := by
    refine closure_minimal ?_ hC.isClosed
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    rw [hψ']
    exact hcon t ht
  have hΩC : Ω ⊆ C :=
    (omegaLimit_subset_closure_image2 atTop (⇑ψ) {x} (Ici_mem_atTop (0 : ℝ))).trans himage
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑ψ) {x} hC
      ⟨Ici 0, Ici_mem_atTop 0, himage⟩ (singleton_nonempty x)
  have hΩc : IsCompact Ω := hC.of_isClosed_subset (isClosed_omegaLimit _ _ _) hΩC
  have hinv : ∀ t, MapsTo (ψ t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop ψ {x} fun t => tendsto_add_atTop t
  refine ⟨Ω, hΩne, hΩc, hΩC, fun t z hz => ?_⟩
  have := hinv (-t) hz
  change k.cancellationFlow (-(-t)) z ∈ Ω at this
  rwa [neg_neg] at this

theorem exists_b'_le_f_cancellationFlow_neg (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ T, 0 ≤ T ∧ b' ≤ f (k.cancellationFlow (-T) x) := by
  by_contra hcon
  push Not at hcon
  set S : Set M := f ⁻¹' Icc a' b' with hS
  have hSc : IsCompact S := c.hf.compact
  have hcon' : ∀ t, 0 ≤ t → k.cancellationFlow (-t) x ∈ S := fun t ht =>
    ⟨k.f_cancellationFlow_neg_ge_a' hx.1 ht, (hcon t ht).le⟩
  obtain ⟨Ω, ⟨w, hw⟩, -, hΩS, hinv⟩ := k.exists_alphaLimit_subset hSc hcon'
  have hwS : f w ∈ Icc a' b' := hΩS hw
  obtain ⟨t₀, -, hft₀, -⟩ := k.reaches_bottom hk hwS
  have hlt : f (k.cancellationFlow (t₀ + 1) w) < a' := k.f_cancellationFlow_lt_of_le_a' hft₀.le (by linarith)
  have hmem : k.cancellationFlow (t₀ + 1) w ∈ Ω := hinv (t₀ + 1) hw
  exact absurd (hΩS hmem).1 (not_le.2 hlt)

theorem reaches_top (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.cancellationFlow (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (k.cancellationFlow (-s) x) < b' := by
  obtain ⟨T, hT, hfT⟩ := k.exists_b'_le_f_cancellationFlow_neg hk hx
  have hcl : IsClosed (f ⁻¹' Ici b') := isClosed_Ici.preimage c.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (k.continuous_cancellationFlow_neg_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hlt : ∀ s ∈ Ico 0 t, f (k.cancellationFlow (-s) x) < b' := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm ?_ htK, hlt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, neg_zero, k.cancellationFlow_zero]; exact hx.2
  · refine le_of_tendsto ((c.hfs.continuous.comp (k.continuous_cancellationFlow_neg_curve x)).continuousAt
      |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
    filter_upwards [Ico_mem_nhdsLT h] with s hs using (hlt s hs).le

theorem reaches_top_pos (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') (hb : f x < b') :
    ∃ t, 0 < t ∧ f (k.cancellationFlow (-t) x) = b' ∧ ∀ s ∈ Ico 0 t, f (k.cancellationFlow (-s) x) < b' := by
  obtain ⟨t, ht, hft, hlt⟩ := k.reaches_top hk hx
  refine ⟨t, lt_of_le_of_ne ht fun h => ?_, hft, hlt⟩
  rw [← h, neg_zero, k.cancellationFlow_zero] at hft
  exact hb.ne hft

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
