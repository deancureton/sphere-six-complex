module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelFlow

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose)
open CancelModel

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

theorem antitoneOn_Icc_of_hasDerivAt_nonpos {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hle : ∀ t ∈ Icc a b, g' t ≤ 0) :
    AntitoneOn g (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht; rw [(hd t (interior_subset ht)).deriv]; exact hle t (interior_subset ht)

theorem monotoneOn_Icc_of_hasDerivAt_nonneg {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hle : ∀ t ∈ Icc a b, 0 ≤ g' t) :
    MonotoneOn g (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht; rw [(hd t (interior_subset ht)).deriv]; exact hle t (interior_subset ht)

theorem antitoneOn_Icc_of_hasDerivAt_nonpos' {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hle : ∀ t ∈ Ioo a b, g' t ≤ 0) :
    AntitoneOn g (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t (Ioo_subset_Icc_self ht)).deriv]; exact hle t ht

theorem monotoneOn_Icc_of_hasDerivAt_nonneg' {g g' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hle : ∀ t ∈ Ioo a b, 0 ≤ g' t) :
    MonotoneOn g (Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t (Ioo_subset_Icc_self ht)).deriv]; exact hle t ht

theorem nonpos_of_deriv_le_mul {h h' : ℝ → ℝ} {K a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t) (h0 : h a ≤ 0)
    (hK : ∀ t ∈ Icc a b, 0 ≤ h t → h' t ≤ K * h t) : ∀ t ∈ Icc a b, h t ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₁, ht₁, hpos⟩ := hcon
  have hcont : ContinuousOn h (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  set S : Set ℝ := Icc a t₁ ∩ h ⁻¹' Iic 0 with hS
  have hScl : IsClosed S :=
    (hcont.mono (Icc_subset_Icc_right ht₁.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have haS : a ∈ S := ⟨left_mem_Icc.2 ht₁.1, h0⟩
  obtain ⟨hts, hts0⟩ := hSc.sSup_mem ⟨a, haS⟩
  set ts := sSup S with hts_def
  have hts0' : h ts ≤ 0 := hts0
  have hts1 : ts < t₁ := lt_of_le_of_ne hts.2 (fun h => by rw [h] at hts0'; linarith)
  have hgt : ∀ t ∈ Ioc ts t₁, 0 < h t := by
    intro t ht
    by_contra hle
    push Not at hle
    have hmem : t ∈ S := ⟨⟨hts.1.trans ht.1.le, ht.2⟩, hle⟩
    have := le_csSup hSc.bddAbove hmem
    linarith [ht.1]
  set φ : ℝ → ℝ := fun t => Real.exp (-K * t) * h t with hφ
  have hφd : ∀ t ∈ Icc ts t₁, HasDerivAt φ (Real.exp (-K * t) * (h' t - K * h t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.exp (-K * t)) (Real.exp (-K * t) * (-K)) t := by
      have h0 : HasDerivAt (fun t : ℝ => -K * t) (-K) t := by
        simpa using (hasDerivAt_id t).const_mul (-K)
      exact (Real.hasDerivAt_exp (-K * t)).comp t h0
    have h2 := h1.mul (hd t ⟨hts.1.trans ht.1, ht.2.trans ht₁.2⟩)
    convert h2 using 1; ring
  have hanti : AntitoneOn φ (Icc ts t₁) := by
    refine antitoneOn_Icc_of_hasDerivAt_nonpos' hφd fun t ht => ?_
    have hpos' := hgt t ⟨ht.1, ht.2.le⟩
    have := hK t ⟨hts.1.trans ht.1.le, ht.2.le.trans ht₁.2⟩ hpos'.le
    have : 0 < Real.exp (-K * t) := Real.exp_pos _
    nlinarith
  have hle := hanti (left_mem_Icc.2 hts1.le) (right_mem_Icc.2 hts1.le) hts1.le
  simp only [hφ] at hle
  have e1 : 0 < Real.exp (-K * t₁) := Real.exp_pos _
  have e2 : 0 < Real.exp (-K * ts) := Real.exp_pos _
  nlinarith [mul_pos e1 hpos, mul_nonpos_iff.2 (Or.inl ⟨e2.le, hts0'⟩)]

theorem pos_of_deriv_ge_neg_mul {h h' : ℝ → ℝ} {K a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t) (h0 : 0 < h a)
    (hK : ∀ t ∈ Icc a b, 0 ≤ h t → -K * h t ≤ h' t) : ∀ t ∈ Icc a b, 0 < h t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₁, ht₁, hle⟩ := hcon
  have hcont : ContinuousOn h (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  set S : Set ℝ := Icc a t₁ ∩ h ⁻¹' Iic 0 with hS
  have hScl : IsClosed S :=
    (hcont.mono (Icc_subset_Icc_right ht₁.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have ht₁S : t₁ ∈ S := ⟨right_mem_Icc.2 ht₁.1, hle⟩
  obtain ⟨hts, hts0⟩ := hSc.sInf_mem ⟨t₁, ht₁S⟩
  set ts := sInf S with hts_def
  have hts0' : h ts ≤ 0 := hts0
  have hats : a < ts := lt_of_le_of_ne hts.1 (fun h => by rw [← h] at hts0'; linarith)
  have hgt : ∀ t ∈ Ico a ts, 0 < h t := by
    intro t ht
    by_contra hle'
    push Not at hle'
    have hmem : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hts.2⟩, hle'⟩
    have := csInf_le hSc.bddBelow hmem
    linarith [ht.2]
  set φ : ℝ → ℝ := fun t => Real.exp (K * t) * h t with hφ
  have hφd : ∀ t ∈ Icc a ts, HasDerivAt φ (Real.exp (K * t) * (K * h t + h' t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.exp (K * t)) (Real.exp (K * t) * K) t := by
      have h0 : HasDerivAt (fun t : ℝ => K * t) K t := by
        simpa using (hasDerivAt_id t).const_mul K
      exact (Real.hasDerivAt_exp (K * t)).comp t h0
    have h2 := h1.mul (hd t ⟨ht.1, ht.2.trans (hts.2.trans ht₁.2)⟩)
    convert h2 using 1; ring
  have hmono : MonotoneOn φ (Icc a ts) := by
    refine monotoneOn_Icc_of_hasDerivAt_nonneg' hφd fun t ht => ?_
    have := hK t ⟨ht.1.le, ht.2.le.trans (hts.2.trans ht₁.2)⟩ (hgt t ⟨ht.1.le, ht.2⟩).le
    have : 0 < Real.exp (K * t) := Real.exp_pos _
    nlinarith
  have hle' := hmono (left_mem_Icc.2 hats.le) (right_mem_Icc.2 hats.le) hats.le
  simp only [hφ] at hle'
  have e1 : 0 < Real.exp (K * a) := Real.exp_pos _
  have e2 : 0 < Real.exp (K * ts) := Real.exp_pos _
  nlinarith [mul_pos e1 h0, mul_nonpos_iff.2 (Or.inl ⟨e2.le, hts0'⟩)]

theorem nonneg_of_deriv_ge_mul {h h' : ℝ → ℝ} {K a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t) (h0 : 0 ≤ h a)
    (hK : ∀ t ∈ Icc a b, h t ≤ 0 → K * h t ≤ h' t) : ∀ t ∈ Icc a b, 0 ≤ h t := by
  have := nonpos_of_deriv_le_mul (h := fun t => -h t) (h' := fun t => -h' t) (K := K)
    (fun t ht => (hd t ht).neg) (by simpa using h0) (fun t ht hle => by
      have := hK t ht (by linarith); linarith)
  intro t ht
  have := this t ht
  simpa using this

theorem eventually_lt_left_of_hasDerivAt_pos {g : ℝ → ℝ} {r t : ℝ} (hr : 0 < r)
    (hg : HasDerivAt g r t) : ∀ᶠ s in 𝓝[<] t, g s < g t := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have hev : ∀ᶠ s in 𝓝[<] t, 0 < slope g t s :=
    ((tendsto_order.1 (hslope.mono_left (nhdsWithin_mono _ fun s (hs : s < t) => hs.ne))).1
      0 hr)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hst
  have hst' : s < t := hst
  rw [slope_def_field] at hs
  have hneg : s - t < 0 := by linarith
  have : g s - g t < 0 := by
    by_contra hle
    push Not at hle
    have := div_nonpos_of_nonneg_of_nonpos hle hneg.le
    linarith
  linarith

theorem antitoneOn_Icc_of_right_local {g : ℝ → ℝ} {T : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hloc : ∀ t ∈ Ico 0 T, ∃ ε > 0, ∀ s ∈ Ioc t (t + ε), s ≤ T → g s ≤ g t) :
    AntitoneOn g (Icc 0 T) := by
  intro s₁ hs₁ s₂ hs₂ h12
  set S : Set ℝ := {t | g t ≤ g s₁} with hS
  have hsub : Icc s₁ T ⊆ S := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ (by simp [hS]) ?_
    · have : S ∩ Icc s₁ T = Icc s₁ T ∩ g ⁻¹' Iic (g s₁) := by
        ext t; simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic]; tauto
      rw [this]
      exact (hg.mono (Icc_subset_Icc_left hs₁.1)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Iic
    · rintro t ⟨htS, ht⟩
      have htS' : g t ≤ g s₁ := htS
      obtain ⟨ε, hε, hεt⟩ := hloc t ⟨hs₁.1.trans ht.1, ht.2⟩
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + ε) T, lt_min (by linarith) ht.2,
        fun u hu => ?_⟩
      have hu1 : u ≤ t + ε := hu.2.trans (min_le_left _ _)
      have hu2 : u ≤ T := hu.2.trans (min_le_right _ _)
      change g u ≤ g s₁
      exact (hεt u ⟨hu.1, hu1⟩ hu2).trans htS'
  exact hsub ⟨h12, hs₂.2⟩

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : IndexZeroCancellingPair I f a' b' p q}

namespace CancelConsts

variable (k : c.CancelConsts)

theorem exists_omegaLimit_subset_of_antitone {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C) {Z : Set M}
    (hmono : ∀ x, ∀ T, (∀ s ∈ Icc 0 T, k.cancellationFlow s x ∈ C) →
      AntitoneOn (fun t => L (k.cancellationFlow t x)) (Icc 0 T))
    (hstrict : ∀ x ∈ C \ Z, (∀ t, 0 ≤ t → k.cancellationFlow t x ∈ C) → ∃ t, 0 < t ∧ L (k.cancellationFlow t x) < L x)
    {x : M} (hcon : ∀ t, 0 ≤ t → k.cancellationFlow t x ∈ C) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ C ∩ Z ∧ ∀ t, MapsTo (k.cancellationFlow t) Ω Ω := by
  set g : ℝ → ℝ := fun t => L (k.cancellationFlow t x) with hg
  have hanti : AntitoneOn g (Ici 0) := by
    intro s hs t ht hst
    have hs' : (0 : ℝ) ≤ s := hs
    have ht' : (0 : ℝ) ≤ t := ht
    exact hmono x t (fun u hu => hcon u hu.1) ⟨hs', hst⟩ ⟨ht', le_rfl⟩ hst
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hL
  set G : ℝ → ℝ := fun t => g (max t 0) with hG
  have hGanti : Antitone G := fun a b hab =>
    hanti (by simp) (by simp) (max_le_max hab le_rfl)
  have hGbdd : BddBelow (range G) := ⟨-B, by
    rintro _ ⟨m, rfl⟩
    have h1 := hB _ (hcon (max m 0) (le_max_right _ _))
    rw [Real.norm_eq_abs] at h1
    have := neg_abs_le (L (k.cancellationFlow (max m 0) x))
    change -B ≤ L (k.cancellationFlow (max m 0) x)
    linarith⟩
  set ℓ := ⨅ m, G m with hℓ
  have hGℓ : Tendsto G atTop (𝓝 ℓ) := tendsto_atTop_ciInf hGanti hGbdd
  have hGle : ∀ m, ℓ ≤ G m := fun m => ciInf_le hGbdd m
  have hGeq : ∀ t, 0 ≤ t → G t = L (k.cancellationFlow t x) := fun t ht => by
    simp only [hG, hg, max_eq_left ht]
  set Ω := omegaLimit atTop (⇑k.toFlow) {x} with hΩ
  have himage : closure (image2 (⇑k.toFlow) (Ici 0) {x}) ⊆ C := by
    refine closure_minimal ?_ hC.isClosed
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact hcon t ht
  have hΩC : Ω ⊆ C :=
    (omegaLimit_subset_closure_image2 atTop (⇑k.toFlow) {x} (Ici_mem_atTop (0 : ℝ))).trans
      himage
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop (⇑k.toFlow) {x} hC
      ⟨Ici 0, Ici_mem_atTop 0, himage⟩ (singleton_nonempty x)
  have hΩc : IsCompact Ω := hC.of_isClosed_subset (isClosed_omegaLimit _ _ _) hΩC
  have hinv : ∀ t, MapsTo (k.cancellationFlow t) Ω Ω :=
    Flow.isInvariant_omegaLimit atTop k.toFlow {x} fun t => tendsto_add_atTop t
  set u : ℝ → M := fun t => k.cancellationFlow t x with hu
  set F : Filter M := map u atTop with hF
  have hFC : F ≤ 𝓟 C := by
    rw [hF, le_principal_iff, mem_map]
    exact eventually_atTop.2 ⟨0, fun t ht => hcon t ht⟩
  have hΩZ : ∀ z ∈ Ω, z ∈ Z := by
    intro z hz
    have hzC : z ∈ C := hΩC hz
    by_contra hzZ
    have hzcon : ∀ t, 0 ≤ t → k.cancellationFlow t z ∈ C := fun t _ => hΩC (hinv t hz)
    obtain ⟨t₀, ht₀, hlt⟩ := hstrict z ⟨hzC, hzZ⟩ hzcon
    have hzF : ClusterPt z F :=
      ((mem_omegaLimit_singleton_iff_mapClusterPt atTop (⇑k.toFlow) x z).1 hz).clusterPt
    have hLz : L z = ℓ := by
      by_contra hne
      set ε := |L z - ℓ| / 2 with hε
      have hε0 : 0 < ε := by
        have : 0 < |L z - ℓ| := abs_pos.2 (sub_ne_zero.2 hne)
        positivity
      have h1 : ∀ᶠ y in 𝓝[C] z, |L y - L z| < ε :=
        (hL z hzC).tendsto (Metric.ball_mem_nhds (L z) hε0)
      have h2 : ∀ᶠ y in F, |L y - ℓ| < ε := by
        rw [hF, eventually_map]
        filter_upwards [hGℓ (Metric.ball_mem_nhds ℓ hε0), eventually_ge_atTop 0] with t ht ht0
        rw [← hGeq t ht0]; exact ht
      obtain ⟨y, hy1, hy2⟩ :=
        ((frequently_of_clusterPt_within hzF hFC h1).and_eventually h2).exists
      have := abs_sub_le (L z) (L y) ℓ
      rw [abs_sub_comm (L z) (L y)] at this
      linarith
    rw [hLz] at hlt
    set F' : Filter M := map (k.cancellationFlow t₀) F with hF'
    have hF'C : F' ≤ 𝓟 C := by
      rw [hF', hF, map_map, le_principal_iff, mem_map]
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      change k.cancellationFlow t₀ (k.cancellationFlow t x) ∈ C
      rw [k.cancellationFlow_cancellationFlow]; exact hcon _ (by positivity)
    have hzF' : ClusterPt (k.cancellationFlow t₀ z) F' :=
      hzF.map (k.continuous_cancellationFlow t₀).continuousAt tendsto_map
    have hzC' : k.cancellationFlow t₀ z ∈ C := by
      rw [← hC.isClosed.closure_eq, mem_closure_iff_clusterPt]
      exact hzF'.mono hF'C
    have h1 : ∀ᶠ y in 𝓝[C] (k.cancellationFlow t₀ z), L y < ℓ := (hL _ hzC').tendsto (Iio_mem_nhds hlt)
    have h2 : ∀ᶠ y in F', ℓ ≤ L y := by
      rw [hF', hF, map_map, eventually_map]
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      change ℓ ≤ L (k.cancellationFlow t₀ (k.cancellationFlow t x))
      rw [k.cancellationFlow_cancellationFlow, ← hGeq _ (by positivity)]
      exact hGle _
    obtain ⟨y, hy1, hy2⟩ :=
      ((frequently_of_clusterPt_within hzF' hF'C h1).and_eventually h2).exists
    linarith
  exact ⟨Ω, hΩne, hΩc, fun z hz => ⟨hΩC hz, hΩZ z hz⟩, hinv⟩

theorem exists_exit_of_antitone_weak {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C) {Z : Set M}
    (hmono : ∀ x, ∀ T, (∀ s ∈ Icc 0 T, k.cancellationFlow s x ∈ C) →
      AntitoneOn (fun t => L (k.cancellationFlow t x)) (Icc 0 T))
    (hstrict : ∀ x ∈ C \ Z, (∀ t, 0 ≤ t → k.cancellationFlow t x ∈ C) → ∃ t, 0 < t ∧ L (k.cancellationFlow t x) < L x)
    (hZ : ∀ z ∈ C ∩ Z, ∃ t : ℝ, k.cancellationFlow t z ∉ C ∩ Z) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ C := by
  intro x _
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω, ⟨w, hwΩ⟩, -, hΩCZ, hinv⟩ :=
    k.exists_omegaLimit_subset_of_antitone hC hL hmono hstrict hcon
  obtain ⟨t, ht⟩ := hZ w (hΩCZ hwΩ)
  exact ht (hΩCZ (hinv t hwΩ))

theorem mem_of_mem_Ico {A : Set M} (hA : IsClosed A) {x : M} {t : ℝ} (ht : 0 < t)
    (h : ∀ s ∈ Ico 0 t, k.cancellationFlow s x ∈ A) : k.cancellationFlow t x ∈ A := by
  refine hA.mem_of_tendsto
    ((k.continuous_cancellationFlow_curve x).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio t))) ?_
  filter_upwards [Ico_mem_nhdsLT ht] with s hs using h s hs

theorem exists_first_hit_face {A F : Set M} (hA : IsClosed A) (hF : IsClosed F) {x : M}
    (hx : x ∈ A)
    (hinv : ∀ t, (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∉ F) → ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ A)
    {t : ℝ} (ht : 0 ≤ t) (hexit : k.cancellationFlow t x ∉ A) :
    ∃ t₁, 0 ≤ t₁ ∧ t₁ ≤ t ∧ k.cancellationFlow t₁ x ∈ F ∧ (∀ s ∈ Icc 0 t₁, k.cancellationFlow s x ∈ A) ∧
      ∀ s ∈ Ico 0 t₁, k.cancellationFlow s x ∉ F := by
  have hhit : ∃ s ∈ Icc 0 t, k.cancellationFlow s x ∈ F := by
    by_contra h
    push Not at h
    exact hexit (hinv t h t (right_mem_Icc.2 ht))
  obtain ⟨t₁, ht₁, ht₁F, hmin⟩ := exists_first_time hF (k.continuous_cancellationFlow_curve x) hhit
  have hbefore : ∀ s ∈ Ico 0 t₁, k.cancellationFlow s x ∈ A := fun s hs =>
    hinv s (fun u hu => hmin u ⟨hu.1, hu.2.trans_lt hs.2⟩) s (right_mem_Icc.2 hs.1)
  have ht₁A : k.cancellationFlow t₁ x ∈ A := by
    rcases ht₁.1.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hx
    · exact k.mem_of_mem_Ico hA h hbefore
  refine ⟨t₁, ht₁.1, ht₁.2, ht₁F, fun s hs => ?_, hmin⟩
  rcases hs.2.eq_or_lt with h | h
  · rw [h]; exact ht₁A
  · exact hbefore s ⟨hs.1, h⟩

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
