module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelGood

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

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : IndexZeroCancellingPair I f a' b' p q}

namespace CancelConsts

variable (k : c.CancelConsts)

def pOpenSupportRegion : Set (Fin n → ℝ) :=
  {y | morseNorm n y < c.ρB ∧ perpSq c.e₁ y < k.τ ^ 2 * axial c.e₁ y ^ 2 + 2 * k.δ ^ 2 ∧
    -k.δ < axial c.e₁ y}

theorem isOpen_pOpenSupportRegion : IsOpen k.pOpenSupportRegion :=
  (isOpen_lt continuous_morseNorm continuous_const).inter
    ((isOpen_lt (continuous_perpSq _)
      ((continuous_const.mul ((continuous_axial _).pow 2)).add continuous_const)).inter
      (isOpen_lt continuous_const (continuous_axial _)))

theorem pOpenSupportRegion_subset_pSupportRegion : k.pOpenSupportRegion ⊆ pSupportRegion k.δ k.τ c.e₁ c.ρB := fun _ hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩

theorem isOpen_image_pOpenSupportRegion : IsOpen (c.e.χ '' k.pOpenSupportRegion) := by
  refine (c.e.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 k.isOpen_pOpenSupportRegion
  exact c.e.hball (mem_ball_of_morseNorm_lt (hy.1.trans c.ρB_lt_R'))

theorem image_pOpenSupportRegion_subset_interior : c.e.χ '' k.pOpenSupportRegion ⊆ interior k.perturbationSupportRegion :=
  k.isOpen_image_pOpenSupportRegion.subset_interior_iff.2 fun _ hx =>
    Or.inl (Or.inl (image_mono k.pOpenSupportRegion_subset_pSupportRegion hx))

theorem p_mem_interior_perturbationSupportRegion : p ∈ interior k.perturbationSupportRegion := by
  refine k.image_pOpenSupportRegion_subset_interior ⟨0, ?_, c.e.hχ0⟩
  refine ⟨by rw [morseNorm_zero]; exact c.ρB_pos, ?_, ?_⟩
  · rw [perpSq, axial_zero, morseNorm_zero]; have := k.hδ; nlinarith [sq_nonneg k.τ]
  · rw [axial_zero]; linarith [k.hδ]

def qOpenSupportRegion : Set (Fin n → ℝ) :=
  {y | uq c.d.hk c.hkq y ^ 2 < c.uB ^ 2 ∧
    ‖posPart c.d.hk y‖ ^ 2 < k.τ ^ 2 * uq c.d.hk c.hkq y ^ 2 + 2 * k.δ ^ 2 ∧
    -k.δ < c.σ * uq c.d.hk c.hkq y}

theorem isOpen_qOpenSupportRegion : IsOpen k.qOpenSupportRegion :=
  (isOpen_lt ((continuous_uq c.d.hk c.hkq).pow 2) continuous_const).inter
    ((isOpen_lt (continuous_normSq_posPart c.d.hk)
      ((continuous_const.mul ((continuous_uq c.d.hk c.hkq).pow 2)).add continuous_const)).inter
      (isOpen_lt continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))))

theorem qOpenSupportRegion_subset_qSupportRegion : k.qOpenSupportRegion ⊆ qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB := fun _ hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩

theorem isOpen_image_qOpenSupportRegion : IsOpen (c.d.χ '' k.qOpenSupportRegion) := by
  refine (c.d.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 k.isOpen_qOpenSupportRegion
  exact c.d.hball (k.qSupportRegion_subset_ball (k.qOpenSupportRegion_subset_qSupportRegion hy))

theorem image_qOpenSupportRegion_subset_interior : c.d.χ '' k.qOpenSupportRegion ⊆ interior k.perturbationSupportRegion :=
  k.isOpen_image_qOpenSupportRegion.subset_interior_iff.2 fun _ hx =>
    Or.inl (Or.inr (image_mono k.qOpenSupportRegion_subset_qSupportRegion hx))

theorem q_mem_interior_perturbationSupportRegion : q ∈ interior k.perturbationSupportRegion := by
  refine k.image_qOpenSupportRegion_subset_interior ⟨0, ?_, c.d.hχ0⟩
  refine ⟨by rw [uq_zero]; have := c.uB_pos; nlinarith, ?_, ?_⟩
  · rw [uq_zero, posPart_zero, norm_zero]; have := k.hδ; nlinarith [sq_nonneg k.τ]
  · rw [uq_zero, mul_zero]; linarith [k.hδ]

def openFlowTube : Set M :=
  c.orientedChartTube ∩ {x | c.c₁ - c.η / 2 < f x ∧ f x < c.c₂ + c.η / 2} ∩
    (c.openChartTube ∩ c.ζ ⁻¹' {v | ‖v‖ < k.δ'})

theorem isOpen_openFlowTube : IsOpen k.openFlowTube :=
  (c.isOpen_orientedChartTube.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))).inter
    (c.continuousOn_ζ.isOpen_inter_preimage c.isOpen_openChartTube
      (isOpen_lt continuous_norm continuous_const))

theorem openFlowTube_subset_closedFlowTube : k.openFlowTube ⊆ k.closedFlowTube := fun _ hx =>
  k.mem_closedFlowTube_iff.2 ⟨hx.1.1, ⟨hx.1.2.1.le, hx.1.2.2.le⟩, hx.2.2.le⟩

theorem openFlowTube_subset_interior : k.openFlowTube ⊆ interior k.perturbationSupportRegion :=
  k.isOpen_openFlowTube.subset_interior_iff.2 fun _ hx => Or.inr (k.openFlowTube_subset_closedFlowTube hx)

theorem push_pPerturbationField_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.perturbationSupportRegion) :
    c.e.push k.pPerturbationField x = 0 := by
  by_cases hK : x ∈ c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' := k.pSupportRegion_subset_ball hy
    rw [MorseNormalChart.push_apply_chart _ hyb]
    have hY : k.pPerturbationField y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
    have hnot : y ∉ k.pOpenSupportRegion := fun h => hx (k.image_pOpenSupportRegion_subset_interior ⟨y, h, rfl⟩)
    have h0 : βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y = 0 := by
      simp only [pOpenSupportRegion, mem_ofPred_eq, not_and, not_lt] at hnot
      by_cases h1 : morseNorm n y < c.ρB
      · by_cases h2 : perpSq c.e₁ y < k.τ ^ 2 * axial c.e₁ y ^ 2 + 2 * k.δ ^ 2
        · rw [βp_eq_zero_of_axial k.hδ (hnot h1 h2), zero_mul]
        · rw [βp_eq_zero_of_perpSq k.hδ (not_lt.1 h2), zero_mul]
      · rw [ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB (not_lt.1 h1), mul_zero]
    rw [hY, h0, mul_zero, zero_smul]
    exact ContinuousLinearMap.map_zero _
  · exact k.push_pPerturbationField_eq_zero_of_notMem hK

theorem push_qPerturbationField_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.perturbationSupportRegion) :
    c.d.push k.qPerturbationField x = 0 := by
  by_cases hK : x ∈ c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' := k.qSupportRegion_subset_ball hy
    rw [MorseNormalChart.push_apply_chart _ hyb]
    have hY : k.qPerturbationField y =
        -(c.σ * c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) •
          c.e₀' := rfl
    have hnot : y ∉ k.qOpenSupportRegion := fun h => hx (k.image_qOpenSupportRegion_subset_interior ⟨y, h, rfl⟩)
    have h0 : βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y = 0 := by
      simp only [qOpenSupportRegion, mem_ofPred_eq, not_and, not_lt] at hnot
      by_cases h1 : uq c.d.hk c.hkq y ^ 2 < c.uB ^ 2
      · by_cases h2 : ‖posPart c.d.hk y‖ ^ 2 < k.τ ^ 2 * uq c.d.hk c.hkq y ^ 2 + 2 * k.δ ^ 2
        · rw [βq_eq_zero_of_uq c.d.hk c.hkq k.hδ (hnot h1 h2), zero_mul]
        · rw [βq_eq_zero_of_posPart c.d.hk c.hkq k.hδ (not_lt.1 h2), zero_mul]
      · rw [ψq_eq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB (not_lt.1 h1), mul_zero]
    rw [hY, h0, mul_zero, neg_zero, zero_smul]
    exact ContinuousLinearMap.map_zero _
  · exact k.push_qPerturbationField_eq_zero_of_notMem hK

theorem localizedMiddlePerturbation_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.perturbationSupportRegion) : k.localizedMiddlePerturbation x = 0 := by
  by_cases hS : x ∈ k.closedFlowTube
  · obtain ⟨hT, hf, hζ⟩ := k.mem_closedFlowTube_iff.1 hS
    rw [k.localizedMiddlePerturbation_of_mem hT]
    apply k.middlePerturbation_eq_zero_of
    have hnot : x ∉ k.openFlowTube := fun h => hx (k.openFlowTube_subset_interior h)
    have hlo := c.c₁_sub_half_lt_lo₁
    have hhi := c.hi₂_lt_c₂_add_half
    by_cases h1 : c.c₁ - c.η / 2 < f x
    · by_cases h2 : f x < c.c₂ + c.η / 2
      · have h3 : ¬ ‖c.ζ x‖ < k.δ' := fun h3 => hnot ⟨⟨hT, h1, h2⟩, hT.1, h3⟩
        have hβ : k.βm' x = 0 :=
          cut_eq_zero k.two_δ_sq_lt_δ'_sq (pow_le_pow_left₀ k.δ'_pos.le (not_lt.1 h3) 2)
        rw [hβ, zero_mul]
      · have hψ : c.ψm' x = 0 := plateau_eq_zero_of_ge hhi (by linarith [not_lt.1 h2])
        rw [hψ, mul_zero]
    · have hψ : c.ψm' x = 0 := plateau_eq_zero_of_le hlo (not_lt.1 h1)
      rw [hψ, mul_zero]
  · exact k.localizedMiddlePerturbation_eq_zero_of_notMem_closedFlowTube hS

theorem cancellationField_eq_V_of_notMem_interior {x : M} (hx : x ∉ interior k.perturbationSupportRegion) : k.cancellationField x = c.D.V x := by
  rw [cancellationField_apply, k.push_pPerturbationField_eq_zero_of_notMem_interior hx, k.push_qPerturbationField_eq_zero_of_notMem_interior hx,
    k.localizedMiddlePerturbation_eq_zero_of_notMem_interior hx, add_zero, add_zero, add_zero]

theorem dfV_cancellationField_neg_of_notMem_interior {x : M} (hx : f x ∈ Icc a' b') (hx' : x ∉ interior k.perturbationSupportRegion) :
    dfV I f k.cancellationField x < 0 := by
  unfold dfV
  rw [k.cancellationField_eq_V_of_notMem_interior hx']
  refine c.D.neg x hx ?_
  rw [mem_pair_iff]
  rintro (rfl | rfl)
  · exact hx' k.p_mem_interior_perturbationSupportRegion
  · exact hx' k.q_mem_interior_perturbationSupportRegion

theorem exists_hit_perturbationSupportRegion_or_bottom {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ (k.cancellationFlow t x ∈ k.perturbationSupportRegion ∨ f (k.cancellationFlow t x) ≤ a') ∧
      ∀ s ∈ Ico 0 t, k.cancellationFlow s x ∉ k.perturbationSupportRegion ∧ a' < f (k.cancellationFlow s x) := by
  by_cases hxK : x ∈ interior k.perturbationSupportRegion
  · exact ⟨0, le_rfl, Or.inl (by rw [k.cancellationFlow_zero]; exact interior_subset hxK),
      fun s hs => absurd hs.2 (not_lt.2 hs.1)⟩
  set C₀ : Set M := f ⁻¹' Icc a' b' ∩ (interior k.perturbationSupportRegion)ᶜ with hC₀
  have hC₀c : IsCompact C₀ := c.hf.compact.inter_right isOpen_interior.isClosed_compl
  have hxC : x ∈ C₀ := ⟨hx, hxK⟩
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_of_deriv_pos hC₀c (L := fun y => -f y)
    c.hfs.continuous.neg.continuousOn (fun y hy => by
      refine ⟨-dfV I f k.cancellationField y, by linarith [k.dfV_cancellationField_neg_of_notMem_interior hy.1 hy.2], ?_⟩
      have := (k.hasDerivAt_f_cancellationFlow y 0).neg
      rwa [k.cancellationFlow_zero] at this) x hxC
  set F : Set M := k.perturbationSupportRegion ∪ f ⁻¹' Iic a' with hF
  have hFc : IsClosed F := k.isClosed_perturbationSupportRegion.union (isClosed_Iic.preimage c.hfs.continuous)
  have hhit : ∃ s ∈ Icc 0 t, k.cancellationFlow s x ∈ F := by
    by_contra h
    push Not at h
    have havoid : ∀ s ∈ Ico 0 t, k.cancellationFlow s x ∉ k.perturbationSupportRegion := fun s hs h' =>
      h s (Ico_subset_Icc_self hs) (Or.inl h')
    have heq := k.flow_eq_cancellationFlow_of_avoid havoid t (right_mem_Icc.2 ht)
    apply hexit
    refine ⟨⟨?_, ?_⟩, fun h' => h t (right_mem_Icc.2 ht) (Or.inl (interior_subset h'))⟩
    · by_contra hlt
      exact h t (right_mem_Icc.2 ht) (Or.inr (le_of_lt (not_le.1 hlt)))
    · rw [← heq]; exact (f_flow_le c.hfs x ht).trans hx.2
  obtain ⟨s₀, hs₀, hs₀F, hmin⟩ := exists_first_time hFc (k.continuous_cancellationFlow_curve x) hhit
  refine ⟨s₀, hs₀.1, ?_, fun s hs => ?_⟩
  · rcases hs₀F with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have := hmin s hs
    simp only [hF, mem_union, mem_preimage, mem_Iic, not_or, not_le] at this
    exact this

theorem exists_reach_pAxialAnnulus_middleTube (hk : k.Good) {x : M} (hx : x ∈ c.pClosedBall) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.pAxialAnnulus ∧ k.cancellationFlow t x ∈ k.middleTube ∧ f (k.cancellationFlow t x) = c.lo₂ := by
  have hx' := (k.pClosedBall_eq_union ▸ hx : x ∈ k.pInnerAngularRegion ∪ k.pAxialAnnulus)
  rcases hx' with hx1 | hx2
  · obtain ⟨t₁, ht₁, hW2, -⟩ := k.exists_reach_pAxialAnnulus hk.hζmin hx1
    obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_middleTube_of_mem_pAxialAnnulus hW2
    refine ⟨t₁ + t₂, by positivity, ?_, ?_, ?_⟩
    · rw [k.cancellationFlow_add]; exact hW t₂ (right_mem_Icc.2 ht₂)
    · rw [k.cancellationFlow_add]; exact hT
    · rw [k.cancellationFlow_add]; exact hf
  · obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_middleTube_of_mem_pAxialAnnulus hx2
    exact ⟨t₂, ht₂, hW t₂ (right_mem_Icc.2 ht₂), hT, hf⟩

theorem antitoneOn_normSq_ζ_cancellationFlow_of_band {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.cancellationFlow s x ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) ≤ c.hi₁) :
    AntitoneOn (fun s => ‖c.ζ (k.cancellationFlow s x)‖ ^ 2) (Icc t₀ t₁) := by
  refine antitoneOn_Icc_of_hasDerivAt_nonpos
    (g' := fun s => -(4 * (c.lam * k.βm' (k.cancellationFlow s x))) * ‖c.ζ (k.cancellationFlow s x)‖ ^ 2)
    (fun s hs => k.hasDerivAt_normSq_ζ_cancellationFlow_mid' (h s hs).1 (h s hs).2.1 (h s hs).2.2)
    (fun s _ => ?_)
  have := k.βm'_nonneg (k.cancellationFlow s x)
  have := c.lam_pos
  have : 0 ≤ 4 * (c.lam * k.βm' (k.cancellationFlow s x)) * ‖c.ζ (k.cancellationFlow s x)‖ ^ 2 := by positivity
  linarith

theorem cancellationFlow_mem_middleTube_of_band {x : M} (hζ : ‖c.ζ x‖ ≤ k.δ') {t : ℝ}
    (h : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) ≤ c.hi₁) :
    ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.middleTube := by
  intro s hs
  have hanti := k.antitoneOn_normSq_ζ_cancellationFlow_of_band h
  have h1 : ‖c.ζ (k.cancellationFlow s x)‖ ^ 2 ≤ ‖c.ζ (k.cancellationFlow 0 x)‖ ^ 2 :=
    hanti (left_mem_Icc.2 (hs.1.trans hs.2)) hs hs.1
  rw [k.cancellationFlow_zero] at h1
  have hζs : ‖c.ζ (k.cancellationFlow s x)‖ ≤ k.δ' := by
    have h2 : ‖c.ζ (k.cancellationFlow s x)‖ ^ 2 ≤ k.δ' ^ 2 :=
      h1.trans (pow_le_pow_left₀ (norm_nonneg _) hζ 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h2
  obtain ⟨hT, hf1, hf2⟩ := h s hs
  refine ⟨k.mem_closedFlowTube_iff.2 ⟨hT, ⟨?_, ?_⟩, hζs⟩, hf1, hf2⟩
  · linarith [c.lo₂_mem_levels]
  · linarith [c.hi₁_mem_levels]

theorem ζ_eq_zero_of_band {x : M} (hζ : c.ζ x = 0) {t : ℝ}
    (h : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) ≤ c.hi₁) :
    ∀ s ∈ Icc 0 t, c.ζ (k.cancellationFlow s x) = 0 := by
  intro s hs
  have hanti := k.antitoneOn_normSq_ζ_cancellationFlow_of_band h
  have h1 : ‖c.ζ (k.cancellationFlow s x)‖ ^ 2 ≤ ‖c.ζ (k.cancellationFlow 0 x)‖ ^ 2 :=
    hanti (left_mem_Icc.2 (hs.1.trans hs.2)) hs hs.1
  rw [k.cancellationFlow_zero, hζ, norm_zero] at h1
  have h2 : ‖c.ζ (k.cancellationFlow s x)‖ ^ 2 = 0 := le_antisymm (by simpa using h1) (by positivity)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

theorem exists_band_segment_up {x : M} (hT : x ∈ c.orientedChartTube) (hlo : c.lo₂ ≤ f x)
    (hhi : f x < c.hi₁) (hd : 0 < -1 + 2 * k.βm x) :
    ∃ t, 0 < t ∧ (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x) ∧
      f (k.cancellationFlow s x) ≤ c.hi₁) ∧ (∀ s ∈ Ioc 0 t, f x < f (k.cancellationFlow s x)) ∧ f (k.cancellationFlow t x) < c.hi₁ := by
  obtain ⟨ε₁, hε₁, hO₁⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_orientedChartTube (t := 0) (x := x)
    (by rw [k.cancellationFlow_zero]; exact hT)
  obtain ⟨ε₂, hε₂, hO₂⟩ := k.exists_Icc_cancellationFlow_mem_open (isOpen_lt c.hfs.continuous continuous_const)
    (t := 0) (x := x) (O := {y | f y < c.hi₁}) (by rw [k.cancellationFlow_zero]; exact hhi)
  have hder : HasDerivAt (fun s => f (k.cancellationFlow s x)) (-1 + 2 * k.βm x) 0 := by
    have := k.hasDerivAt_f_cancellationFlow_mid hT hlo hhi.le
    exact this
  have hev := eventually_gt_of_hasDerivAt_pos hd hder
  rw [k.cancellationFlow_zero] at hev
  obtain ⟨ε₃, hε₃, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hε₃' : 0 < ε₃ := hε₃
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃', fun s hs => ?_, fun s hs => ?_, ?_⟩
  · have hs1 : s ≤ ε₁ := hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s ≤ ε₂ := hs.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s ≤ ε₃ := hs.2.trans (min_le_right _ _)
    refine ⟨hO₁ s ⟨by linarith [hs.1], by linarith⟩, ?_,
      (hO₂ s ⟨by linarith [hs.1], by linarith⟩).le⟩
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hlo
    · exact hlo.trans (hsub ⟨h, hs3⟩).le
  · exact hsub ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  · exact hO₂ _ ⟨by linarith [lt_min (lt_min hε₁ hε₂) hε₃'],
      by linarith [min_le_left (min ε₁ ε₂) ε₃, min_le_right ε₁ ε₂]⟩

theorem exists_band_segment_down {x : M} (hT : x ∈ c.orientedChartTube) (hlo : c.lo₂ < f x)
    (hhi : f x ≤ c.hi₁) (hd : -1 + 2 * k.βm x < 0) :
    ∃ t, 0 < t ∧ (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x) ∧
      f (k.cancellationFlow s x) ≤ c.hi₁) ∧ (∀ s ∈ Ioc 0 t, f (k.cancellationFlow s x) < f x) ∧ c.lo₂ < f (k.cancellationFlow t x) := by
  obtain ⟨ε₁, hε₁, hO₁⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_orientedChartTube (t := 0) (x := x)
    (by rw [k.cancellationFlow_zero]; exact hT)
  obtain ⟨ε₂, hε₂, hO₂⟩ := k.exists_Icc_cancellationFlow_mem_open (isOpen_lt continuous_const c.hfs.continuous)
    (t := 0) (x := x) (O := {y | c.lo₂ < f y}) (by rw [k.cancellationFlow_zero]; exact hlo)
  have hder : HasDerivAt (fun s => f (k.cancellationFlow s x)) (-1 + 2 * k.βm x) 0 :=
    k.hasDerivAt_f_cancellationFlow_mid hT hlo.le hhi
  have hev := eventually_lt_of_hasDerivAt_neg hd hder
  rw [k.cancellationFlow_zero] at hev
  obtain ⟨ε₃, hε₃, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hε₃' : 0 < ε₃ := hε₃
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃', fun s hs => ?_, fun s hs => ?_, ?_⟩
  · have hs1 : s ≤ ε₁ := hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s ≤ ε₂ := hs.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s ≤ ε₃ := hs.2.trans (min_le_right _ _)
    refine ⟨hO₁ s ⟨by linarith [hs.1], by linarith⟩, (hO₂ s ⟨by linarith [hs.1], by linarith⟩).le,
      ?_⟩
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hhi
    · exact (hsub ⟨h, hs3⟩).le.trans hhi
  · exact hsub ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  · exact hO₂ _ ⟨by linarith [lt_min (lt_min hε₁ hε₂) hε₃'],
      by linarith [min_le_left (min ε₁ ε₂) ε₃, min_le_right ε₁ ε₂]⟩

theorem exists_reach_hi₁_of_ζ_eq_zero {x : M} (hx : x ∈ k.middleTube) (hζ : c.ζ x = 0) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.middleTube ∧ f (k.cancellationFlow t x) = c.hi₁ ∧ c.ζ (k.cancellationFlow t x) = 0 := by
  have hT := k.middleTube_subset_orientedChartTube hx
  rcases hx.2.2.eq_or_lt with hhi | hhi
  · exact ⟨0, le_rfl, by rw [k.cancellationFlow_zero]; exact hx, by rw [k.cancellationFlow_zero]; exact hhi,
      by rw [k.cancellationFlow_zero]; exact hζ⟩
  have hβ : k.βm x = 1 := k.βm_eq_one_of_ζ_eq_zero hζ
  obtain ⟨ε, hε, hband, hup, hεhi⟩ := k.exists_band_segment_up hT hx.2.1 hhi (by rw [hβ]; norm_num)
  have hζε := k.ζ_eq_zero_of_band hζ hband
  have hTmidε := k.cancellationFlow_mem_middleTube_of_band (by rw [hζ, norm_zero]; exact k.δ'_pos.le) hband
  set x₁ := k.cancellationFlow ε x with hx₁
  have hx₁T : x₁ ∈ k.middleTube := hTmidε ε (right_mem_Icc.2 hε.le)
  have hx₁ζ : c.ζ x₁ = 0 := hζε ε (right_mem_Icc.2 hε.le)
  have hx₁lo : c.lo₂ < f x₁ := lt_of_le_of_lt hx.2.1 (hup ε ⟨hε, le_rfl⟩)
  obtain ⟨t, ht, hall, -, hexit⟩ := k.exists_exit_mid_band hx₁T
  have hband' : ∀ s ∈ Icc 0 t, k.cancellationFlow s x₁ ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow s x₁) ∧
      f (k.cancellationFlow s x₁) ≤ c.hi₁ := fun s hs =>
    ⟨k.middleTube_subset_orientedChartTube (hall s hs), (hall s hs).2.1, (hall s hs).2.2⟩
  have hζt := k.ζ_eq_zero_of_band hx₁ζ hband'
  have hmono : MonotoneOn (fun s => f (k.cancellationFlow s x₁)) (Icc 0 t) := by
    refine monotoneOn_Icc_of_hasDerivAt_nonneg (g' := fun s => -1 + 2 * k.βm (k.cancellationFlow s x₁))
      (fun s hs => k.hasDerivAt_f_cancellationFlow_mid' (hband' s hs).1 (hband' s hs).2.1 (hband' s hs).2.2)
      (fun s hs => ?_)
    rw [k.βm_eq_one_of_ζ_eq_zero (hζt s hs)]; norm_num
  have hft : f x₁ ≤ f (k.cancellationFlow t x₁) := by
    have h1 : f (k.cancellationFlow 0 x₁) ≤ f (k.cancellationFlow t x₁) := hmono (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rwa [k.cancellationFlow_zero] at h1
  have hfhi : f (k.cancellationFlow t x₁) = c.hi₁ := by
    rcases hexit with h | h
    · exact h.1
    · exfalso; linarith
  refine ⟨ε + t, by positivity, ?_, ?_, ?_⟩
  · rw [k.cancellationFlow_add]; exact hall t (right_mem_Icc.2 ht)
  · rw [k.cancellationFlow_add]; exact hfhi
  · rw [k.cancellationFlow_add]; exact hζt t (right_mem_Icc.2 ht)

theorem exists_pos_mem_middleTube_of_two_δ_le {x : M} (hx : x ∈ k.middleTube) (hζ : 2 * k.δ ≤ ‖c.ζ x‖)
    (hlo : c.lo₂ < f x) :
    ∃ t, 0 < t ∧ k.cancellationFlow t x ∈ k.middleTube ∧ f (k.cancellationFlow t x) < f x ∧ c.lo₂ < f (k.cancellationFlow t x) := by
  have hT := k.middleTube_subset_orientedChartTube hx
  have hβ : k.βm x = 0 :=
    cut_eq_zero k.δ_sq_lt_two_δ_sq (pow_le_pow_left₀ (by linarith [k.hδ]) hζ 2)
  obtain ⟨ε, hε, hband, hdown, hεlo⟩ :=
    k.exists_band_segment_down hT hlo hx.2.2 (by rw [hβ]; norm_num)
  have hTmidε := k.cancellationFlow_mem_middleTube_of_band (k.norm_ζ_le_of_mem_closedFlowTube hx.1) hband
  exact ⟨ε, hε, hTmidε ε (right_mem_Icc.2 hε.le), hdown ε ⟨hε, le_rfl⟩, hεlo⟩

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
