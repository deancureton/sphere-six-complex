module

public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.CancelField
public import Mathlib.Dynamics.OmegaLimit

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

section ClusterPt

variable {X : Type*} [TopologicalSpace X]

theorem frequently_of_clusterPt_within {C : Set X} {F : Filter X} {z : X} (hz : ClusterPt z F)
    (hF : F ≤ 𝓟 C) {P : X → Prop} (hP : ∀ᶠ y in 𝓝[C] z, P y) : ∃ᶠ y in F, P y := by
  have hne := hz.neBot
  have h1 : 𝓝 z ⊓ F ≤ 𝓝[C] z := le_inf inf_le_left (inf_le_right.trans hF)
  exact (Eventually.frequently (h1 hP)).filter_mono inf_le_right

end ClusterPt

theorem exists_pos_lt_of_hasDerivAt_pos {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : HasDerivAt g r 0) : ∃ t₀ : ℝ, 0 < t₀ ∧ g 0 < g t₀ := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope g 0 t :=
    ((tendsto_order.1 (hslope.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne'))).1
      0 hr)
  obtain ⟨t₀, ht₀, hpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht₀' : (0 : ℝ) < t₀ := hpos
  rw [slope_def_field, sub_zero] at ht₀
  refine ⟨t₀, ht₀', ?_⟩
  have := (div_pos_iff_of_pos_right ht₀').1 ht₀
  linarith

theorem nonneg_of_hasDerivAt_of_le_left {g : ℝ → ℝ} {r t ε : ℝ} (hε : 0 < ε)
    (hg : HasDerivAt g r t) (hle : ∀ s ∈ Ico (t - ε) t, g s ≤ g t) : 0 ≤ r := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have h1 : Tendsto (slope g t) (𝓝[<] t) (𝓝 r) :=
    hslope.mono_left (nhdsWithin_mono _ fun s (hs : s < t) => hs.ne)
  refine ge_of_tendsto h1 ?_
  filter_upwards [Ico_mem_nhdsLT (show t - ε < t by linarith)] with s hs
  rw [slope_def_field]
  have hst : s - t < 0 := by linarith [hs.2]
  have := hle s hs
  exact div_nonneg_of_nonpos (by linarith) hst.le

theorem eventually_gt_of_hasDerivAt_pos {g : ℝ → ℝ} {r t : ℝ} (hr : 0 < r)
    (hg : HasDerivAt g r t) : ∀ᶠ s in 𝓝[>] t, g t < g s := by
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hg)
  have hev : ∀ᶠ s in 𝓝[>] t, 0 < slope g t s :=
    ((tendsto_order.1 (hslope.mono_left (nhdsWithin_mono _ fun s (hs : t < s) => hs.ne'))).1
      0 hr)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hts
  have hts' : t < s := hts
  rw [slope_def_field] at hs
  have := (div_pos_iff_of_pos_right (by linarith)).1 hs
  linarith

theorem eventually_lt_of_hasDerivAt_neg {g : ℝ → ℝ} {r t : ℝ} (hr : r < 0)
    (hg : HasDerivAt g r t) : ∀ᶠ s in 𝓝[>] t, g s < g t := by
  have := eventually_gt_of_hasDerivAt_pos (g := fun s => -g s) (r := -r) (by linarith) hg.neg
  filter_upwards [this] with s hs
  linarith

theorem exists_pos_gt_of_hasDerivAt_neg {g : ℝ → ℝ} {r : ℝ} (hr : r < 0)
    (hg : HasDerivAt g r 0) : ∃ t₀ : ℝ, 0 < t₀ ∧ g t₀ < g 0 := by
  obtain ⟨t₀, ht₀, h⟩ := exists_pos_lt_of_hasDerivAt_pos (g := fun t => -g t) (r := -r)
    (by linarith) hg.neg
  exact ⟨t₀, ht₀, by simpa using h⟩

section Agree

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem integralCurve_eq_on_Icc_of_agree {V₁ V₂ : (x : M) → TangentSpace I x}
    (hV₁ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, V₁ x⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsOpen U) (hV : ∀ x ∈ U, V₁ x = V₂ x) {γ₁ γ₂ : ℝ → M}
    (hγ₁ : IsMIntegralCurve γ₁ V₁) (hγ₂ : IsMIntegralCurve γ₂ V₂) (h0 : γ₁ 0 = γ₂ 0) {T : ℝ}
    (hmem : ∀ s ∈ Ico 0 T, γ₁ s ∈ U) : ∀ s ∈ Icc 0 T, γ₂ s = γ₁ s := by
  have hQ : IsClosed {s : ℝ | γ₂ s = γ₁ s} := isClosed_eq hγ₂.continuous hγ₁.continuous
  refine Icc_subset_of_isClosed_of_step hQ (by simp [h0]) fun t ht hIcc => ?_
  have hxt : γ₂ t = γ₁ t := hIcc (right_mem_Icc.2 ht.1)
  have hc₁ : IsMIntegralCurveAt γ₁ V₁ t := hγ₁.isMIntegralCurveAt t
  have hc₂ : IsMIntegralCurveAt γ₂ V₁ t := by
    have hev : ∀ᶠ s in 𝓝 t, γ₂ s ∈ U :=
      hγ₂.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (hxt ▸ hmem t ht))
    filter_upwards [hev] with s hs
    have := hγ₂ s
    rwa [← hV _ hs] at this
  have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    hV₁.contMDiffAt hc₁ hc₂ hxt.symm
  exact nhdsWithin_le_nhds (heq.mono fun s hs => hs.symm)

theorem integralCurve_eq_on_Icc_neg_of_agree {V₁ V₂ : (x : M) → TangentSpace I x}
    (hV₁ : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, V₁ x⟩ : TangentBundle I M)))
    {U : Set M} (hU : IsOpen U) (hV : ∀ x ∈ U, V₁ x = V₂ x) {γ₁ γ₂ : ℝ → M}
    (hγ₁ : IsMIntegralCurve γ₁ V₁) (hγ₂ : IsMIntegralCurve γ₂ V₂) (h0 : γ₁ 0 = γ₂ 0) {T : ℝ}
    (hmem : ∀ s ∈ Ioc (-T) 0, γ₁ s ∈ U) : ∀ s ∈ Icc (-T) 0, γ₂ s = γ₁ s := by
  have hV₁' : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1
      (fun x => (⟨x, -V₁ x⟩ : TangentBundle I M)) := hV₁.neg_section
  have hr₁ : IsMIntegralCurve (fun s => γ₁ (-s)) (-V₁) := by
    have hc := hγ₁.comp_mul (-1)
    have e : (γ₁ ∘ fun s : ℝ => s * (-1)) = fun s => γ₁ (-s) := by
      funext s; simp [Function.comp]
    have e' : (-1 : ℝ) • V₁ = -V₁ := by funext y; exact neg_one_smul ℝ (V₁ y)
    rwa [e, e'] at hc
  have hr₂ : IsMIntegralCurve (fun s => γ₂ (-s)) (-V₂) := by
    have hc := hγ₂.comp_mul (-1)
    have e : (γ₂ ∘ fun s : ℝ => s * (-1)) = fun s => γ₂ (-s) := by
      funext s; simp [Function.comp]
    have e' : (-1 : ℝ) • V₂ = -V₂ := by funext y; exact neg_one_smul ℝ (V₂ y)
    rwa [e, e'] at hc
  have h := integralCurve_eq_on_Icc_of_agree (V₁ := -V₁) (V₂ := -V₂) hV₁' hU
    (fun x hx => by simp only [Pi.neg_apply, hV x hx]) hr₁ hr₂ (by simpa using h0) (T := T)
    (fun s hs => hmem (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  intro s hs
  have := h (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa using this

end Agree

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

theorem f_mem_of_mem_smallBall {x : M} {p' : M} {hp' : p' ∈ ({p, q} : Finset M)}
    (hx : x ∈ c.D.smallBall p' hp') : a' + c.η₀ < f x ∧ f x < b' - c.η₀ :=
  c.η₀_spec p' hp' x (image_mono (fun y (hy : morseNorm n y < _) =>
    hy.le.trans (c.D.r₀_lt_R p' hp').le) hx)

def dζ (V : (x : M) → TangentSpace I x) (x : M) : EuclideanSpace ℝ (Fin (n - c.d.k)) :=
  (NormedSpace.fromTangentSpace (c.ζ x))
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ x (V x))

theorem dζ_add (V W : (x : M) → TangentSpace I x) (x : M) :
    c.dζ (fun x => V x + W x) x = c.dζ V x + c.dζ W x := by
  unfold dζ; simp

theorem dζ_smul (a : ℝ) (V : (x : M) → TangentSpace I x) (x : M) :
    c.dζ (fun x => a • V x) x = a • c.dζ V x := by
  unfold dζ; simp

theorem dζ_V_eq_zero {x : M} (hx : x ∈ c.openChartTube) : c.dζ c.D.V x = 0 := c.dζ_V hx

theorem dζ_transverseField_eq {x : M} (hx : x ∈ c.openChartTube) : c.dζ c.transverseField x = -c.ζ x := c.dζ_transverseField hx

theorem dζ_zero (x : M) : c.dζ (fun _ => 0) x = 0 := by
  unfold dζ; simp

theorem isClosed_mid_levels : IsClosed {y : M | c.lo₂ ≤ f y ∧ f y ≤ c.hi₁} :=
  (isClosed_Icc.preimage c.hfs.continuous)

theorem lo₂_mem_levels : c.c₁ - c.η / 2 ≤ c.lo₂ := by
  unfold lo₂; linarith [c.η_pos]

theorem hi₁_mem_levels : c.hi₁ ≤ c.c₂ + c.η / 2 := by
  unfold hi₁; linarith [c.η_pos]

def outsideMiddleBand : Set M := {y | f y ≤ c.lo₂ ∨ c.hi₁ ≤ f y}

theorem isClosed_outsideMiddleBand : IsClosed c.outsideMiddleBand :=
  (isClosed_Iic.preimage c.hfs.continuous).union (isClosed_Ici.preimage c.hfs.continuous)

theorem lt_of_notMem_outsideMiddleBand {y : M} (hy : y ∉ c.outsideMiddleBand) : c.lo₂ < f y ∧ f y < c.hi₁ := by
  simp only [outsideMiddleBand, mem_ofPred_eq, not_or, not_le] at hy
  exact hy

open scoped Classical in
def pRestrictedTransverseField (y : Fin n → ℝ) : Fin n → ℝ := if c.e.χ y ∈ c.orientedChartTube then c.pTransverseField y else 0

theorem pRestrictedTransverseField_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.orientedChartTube) : c.pRestrictedTransverseField y = c.pTransverseField y := by
  classical simp [pRestrictedTransverseField, h]

theorem pRestrictedTransverseField_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.orientedChartTube) : c.pRestrictedTransverseField y = 0 := by
  classical simp [pRestrictedTransverseField, h]

theorem dot_pRestrictedTransverseField {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) : dot y (c.pRestrictedTransverseField y) = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [c.pRestrictedTransverseField_of_mem hT, dot_eq_sum]
    exact c.transverseField_chart_p_orth (c.morseNorm_lt_rmp_of_sq_lt hy) hT.1
  · rw [c.pRestrictedTransverseField_of_notMem hT, dot_zero_right]

theorem pRestrictedTransverseField_eq_zero_of_ζ {y : Fin n → ℝ} (hT : c.e.χ y ∈ c.orientedChartTube)
    (hζ : c.ζ (c.e.χ y) = 0) : c.pRestrictedTransverseField y = 0 := by
  rw [c.pRestrictedTransverseField_of_mem hT]
  unfold pTransverseField
  rw [(c.transverseField_eq_zero_iff hT.1).2 hζ, map_zero]
  rfl

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem smooth_one' :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, k.cancellationField x⟩ : TangentBundle I M)) :=
  k.contMDiff_cancellationField.of_le (by norm_num)

theorem hcomplete' : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ k.cancellationField :=
  exists_globalIntegralCurve_of_compactSupport k.cancellationField k.contMDiff_cancellationField k.isCompact_tsupport_cancellationField

def cancellationFlow (t : ℝ) (x : M) : M := curveAt k.cancellationField k.hcomplete' x t

theorem isMIntegralCurve_cancellationFlow (x : M) : IsMIntegralCurve (fun t => k.cancellationFlow t x) k.cancellationField :=
  curveAt_integralCurve k.cancellationField k.hcomplete' x

@[simp] theorem cancellationFlow_zero (x : M) : k.cancellationFlow 0 x = x := curveAt_zero k.cancellationField k.hcomplete' x

theorem cancellationFlow_add (x : M) (s t : ℝ) : k.cancellationFlow (s + t) x = k.cancellationFlow t (k.cancellationFlow s x) :=
  curveAt_add k.cancellationField k.smooth_one' k.hcomplete' x s t

theorem cancellationFlow_cancellationFlow (x : M) (s t : ℝ) : k.cancellationFlow t (k.cancellationFlow s x) = k.cancellationFlow (s + t) x := (k.cancellationFlow_add x s t).symm

theorem cancellationFlow_neg_cancellationFlow (x : M) (t : ℝ) : k.cancellationFlow (-t) (k.cancellationFlow t x) = x := by
  rw [cancellationFlow_cancellationFlow, add_neg_cancel, cancellationFlow_zero]

theorem cancellationFlow_cancellationFlow_neg (x : M) (t : ℝ) : k.cancellationFlow t (k.cancellationFlow (-t) x) = x := by
  rw [cancellationFlow_cancellationFlow, neg_add_cancel, cancellationFlow_zero]

theorem cancellationFlow_injective (t : ℝ) : Function.Injective (k.cancellationFlow t) :=
  curveAt_injective k.cancellationField k.smooth_one' k.hcomplete' t

theorem cancellationFlow_eq_self_of_notMem_tsupport {x : M} (hx : x ∉ tsupport k.cancellationField) (t : ℝ) :
    k.cancellationFlow t x = x :=
  curveAt_eq_self_of_not_mem_tsupport k.cancellationField k.contMDiff_cancellationField k.hcomplete' hx t

theorem contMDiff_cancellationFlow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => k.cancellationFlow z.1 z.2) :=
  contMDiff_globalFlow_joint_of_compactSupport k.cancellationField k.contMDiff_cancellationField k.isCompact_tsupport_cancellationField

theorem continuous_cancellationFlow_joint : Continuous (fun z : ℝ × M => k.cancellationFlow z.1 z.2) :=
  k.contMDiff_cancellationFlow_joint.continuous

theorem contMDiff_cancellationFlow (t : ℝ) : ContMDiff I I ∞ (k.cancellationFlow t) := fun x =>
  contMDiffAt_globalFlow_of_compactSupport k.cancellationField k.contMDiff_cancellationField k.isCompact_tsupport_cancellationField t x

theorem continuous_cancellationFlow (t : ℝ) : Continuous (k.cancellationFlow t) := (k.contMDiff_cancellationFlow t).continuous

theorem continuous_cancellationFlow_curve (x : M) : Continuous (fun t => k.cancellationFlow t x) :=
  (k.isMIntegralCurve_cancellationFlow x).continuous

theorem exists_Icc_cancellationFlow_mem_open {O : Set M} (hO : IsOpen O) {x : M} {t : ℝ}
    (ht : k.cancellationFlow t x ∈ O) : ∃ δ > 0, ∀ s ∈ Icc (t - δ) (t + δ), k.cancellationFlow s x ∈ O := by
  have hmem : {s | k.cancellationFlow s x ∈ O} ∈ 𝓝 t :=
    (k.continuous_cancellationFlow_curve x).continuousAt.preimage_mem_nhds (hO.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε / 2, by positivity, fun s hs => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

theorem cancellationField_eq_V_on_compl : ∀ x ∈ k.perturbationSupportRegionᶜ, k.cancellationField x = c.D.V x := fun _ hx => k.cancellationField_eq_V_of_notMem hx

theorem flow_eq_cancellationFlow_of_avoid {x : M} {T : ℝ} (h : ∀ s ∈ Ico 0 T, k.cancellationFlow s x ∉ k.perturbationSupportRegion) :
    ∀ s ∈ Icc 0 T, c.D.flow s x = k.cancellationFlow s x :=
  integralCurve_eq_on_Icc_of_agree k.smooth_one' k.isClosed_perturbationSupportRegion.isOpen_compl k.cancellationField_eq_V_on_compl
    (k.isMIntegralCurve_cancellationFlow x) (c.D.isMIntegralCurve_flow x) (by simp) h

theorem cancellationFlow_eq_flow_of_avoid {x : M} {T : ℝ} (h : ∀ s ∈ Ico 0 T, c.D.flow s x ∉ k.perturbationSupportRegion) :
    ∀ s ∈ Icc 0 T, k.cancellationFlow s x = c.D.flow s x :=
  integralCurve_eq_on_Icc_of_agree c.D.smooth_one k.isClosed_perturbationSupportRegion.isOpen_compl
    (fun x hx => (k.cancellationField_eq_V_on_compl x hx).symm) (c.D.isMIntegralCurve_flow x)
    (k.isMIntegralCurve_cancellationFlow x) (by simp) h

theorem flow_eq_cancellationFlow_of_avoid_neg {x : M} {T : ℝ} (h : ∀ s ∈ Ioc (-T) 0, k.cancellationFlow s x ∉ k.perturbationSupportRegion) :
    ∀ s ∈ Icc (-T) 0, c.D.flow s x = k.cancellationFlow s x :=
  integralCurve_eq_on_Icc_neg_of_agree k.smooth_one' k.isClosed_perturbationSupportRegion.isOpen_compl
    k.cancellationField_eq_V_on_compl (k.isMIntegralCurve_cancellationFlow x) (c.D.isMIntegralCurve_flow x) (by simp) h

theorem cancellationFlow_eq_flow_of_avoid_neg {x : M} {T : ℝ} (h : ∀ s ∈ Ioc (-T) 0, c.D.flow s x ∉ k.perturbationSupportRegion) :
    ∀ s ∈ Icc (-T) 0, k.cancellationFlow s x = c.D.flow s x :=
  integralCurve_eq_on_Icc_neg_of_agree c.D.smooth_one k.isClosed_perturbationSupportRegion.isOpen_compl
    (fun x hx => (k.cancellationField_eq_V_on_compl x hx).symm) (c.D.isMIntegralCurve_flow x)
    (k.isMIntegralCurve_cancellationFlow x) (by simp) h

theorem cancellationFlow_eq_flow_of_avoid_uIcc {x : M} {t : ℝ}
    (h : ∀ s ∈ uIcc 0 t, s ≠ t → c.D.flow s x ∉ k.perturbationSupportRegion) : k.cancellationFlow t x = c.D.flow t x := by
  rcases le_or_gt 0 t with ht | ht
  · exact k.cancellationFlow_eq_flow_of_avoid (fun s hs => h s (by rw [uIcc_of_le ht]; exact ⟨hs.1, hs.2.le⟩)
      hs.2.ne) t (right_mem_Icc.2 ht)
  · have := k.cancellationFlow_eq_flow_of_avoid_neg (T := -t) (fun s hs => h s
      (by rw [uIcc_of_ge ht.le]; rw [neg_neg] at hs; exact ⟨hs.1.le, hs.2⟩)
      (by rw [neg_neg] at hs; exact hs.1.ne')) t ⟨by rw [neg_neg], ht.le⟩
    exact this

theorem hasDerivAt_f_cancellationFlow (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (k.cancellationFlow s x)) (dfV I f k.cancellationField (k.cancellationFlow t x)) t :=
  hasDerivAt_df_comp_integralCurve f c.hfs k.cancellationField (k.isMIntegralCurve_cancellationFlow x) t

theorem dfV_cancellationField_eq_of_notMem {x : M} (hx : x ∉ k.perturbationSupportRegion) : dfV I f k.cancellationField x = dfV I f c.D.V x := by
  unfold dfV; rw [k.cancellationField_eq_V_of_notMem hx]

theorem dfV_cancellationField_eq_neg_one {x : M} (hx : x ∉ k.perturbationSupportRegion) (hf : f x ∈ Icc a' b')
    (hsb : ∀ p' hp', x ∉ c.D.smallBall p' hp') : dfV I f k.cancellationField x = -1 := by
  rw [k.dfV_cancellationField_eq_of_notMem hx]; exact c.D.unit x hf hsb

theorem dfV_cancellationField_nonpos_of_notMem {x : M} (hx : x ∉ k.perturbationSupportRegion) : dfV I f k.cancellationField x ≤ 0 := by
  rw [k.dfV_cancellationField_eq_of_notMem hx]; exact (c.D.dfV_rate x).2

theorem neg_one_le_dfV_cancellationField_of_notMem {x : M} (hx : x ∉ k.perturbationSupportRegion) : -1 ≤ dfV I f k.cancellationField x := by
  rw [k.dfV_cancellationField_eq_of_notMem hx]; exact (c.D.dfV_rate x).1

theorem notMem_perturbationSupportRegion_of_f_lt {x : M} (hx : f x < a' + c.η₀) : x ∉ k.perturbationSupportRegion := fun h =>
  absurd (k.perturbationSupportRegion_subset_strip h).1 (not_le.2 hx)

theorem notMem_perturbationSupportRegion_of_lt_f {x : M} (hx : b' - c.η₀ < f x) : x ∉ k.perturbationSupportRegion := fun h =>
  absurd (k.perturbationSupportRegion_subset_strip h).2 (not_le.2 hx)

theorem dfV_cancellationField_lower_collar {x : M} (h1 : a' ≤ f x) (h2 : f x < a' + c.η₀) :
    dfV I f k.cancellationField x = -1 :=
  k.dfV_cancellationField_eq_neg_one (k.notMem_perturbationSupportRegion_of_f_lt h2)
    ⟨h1, by linarith [c.η₀_pos, c.f_p_mem.2, c.a'_add_η₀_lt_f_p]⟩
    fun p' hp' hmem => absurd (c.f_mem_of_mem_smallBall hmem).1 (not_lt.2 h2.le)

theorem dfV_cancellationField_upper_collar {x : M} (h1 : b' - c.η₀ < f x) (h2 : f x ≤ b') :
    dfV I f k.cancellationField x = -1 :=
  k.dfV_cancellationField_eq_neg_one (k.notMem_perturbationSupportRegion_of_lt_f h1)
    ⟨by linarith [c.η₀_pos, c.f_p_mem.1, c.a'_add_η₀_lt_f_p, c.hlt, c.hε, c.f_q_add_η₀_lt_b'], h2⟩
    fun p' hp' hmem => absurd (c.f_mem_of_mem_smallBall hmem).2 (not_lt.2 h1.le)

theorem f_cancellationFlow_lower_collar {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Icc 0 t, a' ≤ f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) < a' + c.η₀) :
    f (k.cancellationFlow t x) = f x - t := by
  have := f_eq_sub_of_integralCurve_on_set f c.hfs k.cancellationField {y | a' ≤ f y ∧ f y < a' + c.η₀}
    (fun y hy => k.dfV_cancellationField_lower_collar hy.1 hy.2) (k.isMIntegralCurve_cancellationFlow x) ht hstay
  simpa using this

theorem f_cancellationFlow_upper_collar {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hstay : ∀ s ∈ Icc 0 t, b' - c.η₀ < f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) ≤ b') :
    f (k.cancellationFlow t x) = f x - t := by
  have := f_eq_sub_of_integralCurve_on_set f c.hfs k.cancellationField {y | b' - c.η₀ < f y ∧ f y ≤ b'}
    (fun y hy => k.dfV_cancellationField_upper_collar hy.1 hy.2) (k.isMIntegralCurve_cancellationFlow x) ht hstay
  simpa using this

theorem cancellationFlow_eq_flow_of_f_lt {x : M} (hx : f x < a' + c.η₀) {t : ℝ} (ht : 0 ≤ t) :
    k.cancellationFlow t x = c.D.flow t x :=
  k.cancellationFlow_eq_flow_of_avoid (fun _ hs => k.notMem_perturbationSupportRegion_of_f_lt
    (lt_of_le_of_lt (f_flow_le c.hfs x hs.1) hx)) t (right_mem_Icc.2 ht)

theorem cancellationFlow_eq_flow_of_lt_f {x : M} (hx : b' - c.η₀ < f x) {t : ℝ} (ht : t ≤ 0) :
    k.cancellationFlow t x = c.D.flow t x :=
  k.cancellationFlow_eq_flow_of_avoid_neg (T := -t) (fun s hs => k.notMem_perturbationSupportRegion_of_lt_f
    (lt_of_lt_of_le hx (le_f_flow_of_nonpos c.hfs x hs.2))) t ⟨by rw [neg_neg], ht⟩

theorem hasDerivAt_symm_cancellationFlow_of_pullback {r : M} (d : MorseNormalChart I f r)
    {Y : (Fin n → ℝ) → Fin n → ℝ} {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ d.χ '' Metric.ball 0 d.R')
    (hY : mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.cancellationFlow s x) (k.cancellationField (k.cancellationFlow s x)) =
      Y (d.χ.symm (k.cancellationFlow s x))) :
    HasDerivAt (fun s => d.χ.symm (k.cancellationFlow s x)) (Y (d.χ.symm (k.cancellationFlow s x))) s := by
  have hγ := k.isMIntegralCurve_cancellationFlow x
  have hsymm : HasMFDerivAt I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.cancellationFlow s x)
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.cancellationFlow s x)) :=
    (d.mdifferentiableAt_symm hs).hasMFDerivAt
  have hcomp := HasMFDerivAt.comp s hsymm (hγ s)
  have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  rw [hasDerivAt_iff_hasFDerivAt]
  refine (hfd.congr_fderiv ?_)
  apply ContinuousLinearMap.ext
  intro r
  change (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (k.cancellationFlow s x)) ((id r : ℝ) • k.cancellationField (k.cancellationFlow s x)) =
    (id r : ℝ) • Y (d.χ.symm (k.cancellationFlow s x))
  rw [map_smul, hY]
  rfl

open scoped Classical in
def pCancellationField (y : Fin n → ℝ) : Fin n → ℝ :=
  ModelField.modelField 0 c.e.r₀ y + k.pPerturbationField y +
    (if c.e.χ y ∈ c.orientedChartTube then
      (2 * (k.βm (c.e.χ y) * c.ψm (c.e.χ y))) • (-ModelField.modelField 0 c.e.r₀ y) +
        (2 * (c.lam * (k.βm' (c.e.χ y) * c.ψm' (c.e.χ y)))) • c.pTransverseField y
    else 0)

open scoped Classical in
def qCancellationField (y : Fin n → ℝ) : Fin n → ℝ :=
  ModelField.modelField c.d.k c.d.r₀ y + k.qPerturbationField y +
    (if c.d.χ y ∈ c.orientedChartTube then
      (2 * (k.βm (c.d.χ y) * c.ψm (c.d.χ y))) • (-ModelField.modelField c.d.k c.d.r₀ y) +
        (2 * (c.lam * (k.βm' (c.d.χ y) * c.ψm' (c.d.χ y)))) • c.qTransverseField y
    else 0)

theorem pullback_cancellationField_p' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (k.cancellationField (c.e.χ y)) : Fin n → ℝ) = k.pCancellationField y := by
  classical
  rw [k.pullback_cancellationField_p hy]; rfl

theorem pullback_cancellationField_q' {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (k.cancellationField (c.d.χ y)) : Fin n → ℝ) = k.qCancellationField y := by
  classical
  rw [k.pullback_cancellationField_q hy]; rfl

theorem symm_cancellationFlow_p_sq_lt {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall') :
    morseNorm n (c.e.χ.symm (k.cancellationFlow s x)) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, hyx⟩ := hs
  rw [← hyx, c.chart_p_symm_eq' hy]; exact hy

theorem symm_cancellationFlow_q_sq_lt {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.qBall') :
    morseNorm n (c.d.χ.symm (k.cancellationFlow s x)) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, hyx⟩ := hs
  rw [← hyx, c.chart_q_symm_eq' hy]; exact hy

theorem hasDerivAt_symm_cancellationFlow_p {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall') :
    HasDerivAt (fun s => c.e.χ.symm (k.cancellationFlow s x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x))) s := by
  refine k.hasDerivAt_symm_cancellationFlow_of_pullback c.e (c.pBall'_subset_image_ball hs) ?_
  have hy := k.symm_cancellationFlow_p_sq_lt hs
  have := k.pullback_cancellationField_p' hy
  rwa [c.e.symm_image_eq (c.pBall'_subset_image_ball hs)] at this

theorem hasDerivAt_symm_cancellationFlow_q {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.qBall') :
    HasDerivAt (fun s => c.d.χ.symm (k.cancellationFlow s x)) (k.qCancellationField (c.d.χ.symm (k.cancellationFlow s x))) s := by
  refine k.hasDerivAt_symm_cancellationFlow_of_pullback c.d (c.qBall'_subset_image_ball hs) ?_
  have hy := k.symm_cancellationFlow_q_sq_lt hs
  have := k.pullback_cancellationField_q' hy
  rwa [c.d.symm_image_eq (c.qBall'_subset_image_ball hs)] at this

theorem hasDerivAt_symm_cancellationFlow_p_Icc {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.cancellationFlow s x ∈ c.pBall') :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => c.e.χ.symm (k.cancellationFlow s x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x))) s :=
  fun s hs => k.hasDerivAt_symm_cancellationFlow_p (h s hs)

theorem hasDerivAt_symm_cancellationFlow_q_Icc {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.cancellationFlow s x ∈ c.qBall') :
    ∀ s ∈ Icc t₀ t₁, HasDerivAt (fun s => c.d.χ.symm (k.cancellationFlow s x)) (k.qCancellationField (c.d.χ.symm (k.cancellationFlow s x))) s :=
  fun s hs => k.hasDerivAt_symm_cancellationFlow_q (h s hs)

theorem hasDerivAt_ζ_cancellationFlow {x : M} {t : ℝ} (ht : k.cancellationFlow t x ∈ c.openChartTube) :
    HasDerivAt (fun s => c.ζ (k.cancellationFlow s x)) (c.dζ k.cancellationField (k.cancellationFlow t x)) t :=
  hasDerivAt_comp_integralCurve (k.isMIntegralCurve_cancellationFlow x) (c.mdifferentiableAt_ζ ht)

theorem dζ_localizedMiddlePerturbation {x : M} (hx : x ∈ c.orientedChartTube) :
    c.dζ k.localizedMiddlePerturbation x = -(2 * (c.lam * (k.βm' x * c.ψm' x))) • c.ζ x := by
  have h : c.dζ k.localizedMiddlePerturbation x = c.dζ k.middlePerturbation x := by
    unfold dζ; rw [k.localizedMiddlePerturbation_of_mem hx]
  rw [h]
  unfold middlePerturbation dζ
  simp only [map_add, map_smul, map_neg]
  have h1 := c.dζ_V hx.1
  have h2 := c.dζ_transverseField hx.1
  rw [h1, h2]
  simp [neg_smul]

theorem dζ_cancellationField {x : M} (hx : x ∈ c.orientedChartTube) (hp : c.e.push k.pPerturbationField x = 0)
    (hq : c.d.push k.qPerturbationField x = 0) :
    c.dζ k.cancellationField x = -(2 * (c.lam * (k.βm' x * c.ψm' x))) • c.ζ x := by
  have e : k.cancellationField = fun x => (fun x => (fun x => c.D.V x + c.e.push k.pPerturbationField x) x + c.d.push k.qPerturbationField x) x
      + k.localizedMiddlePerturbation x := rfl
  rw [e, c.dζ_add, c.dζ_add, c.dζ_add, c.dζ_V_eq_zero hx.1, k.dζ_localizedMiddlePerturbation hx]
  have hp' : c.dζ (c.e.push k.pPerturbationField) x = 0 := by unfold dζ; rw [hp]; simp
  have hq' : c.dζ (c.d.push k.qPerturbationField) x = 0 := by unfold dζ; rw [hq]; simp
  rw [hp', hq']; simp

theorem hasDerivAt_normSq_ζ_cancellationFlow {x : M} {t : ℝ} (ht : k.cancellationFlow t x ∈ c.openChartTube) :
    HasDerivAt (fun s => ‖c.ζ (k.cancellationFlow s x)‖ ^ 2)
      (2 * inner ℝ (c.ζ (k.cancellationFlow t x)) (c.dζ k.cancellationField (k.cancellationFlow t x))) t := by
  have := (k.hasDerivAt_ζ_cancellationFlow ht).norm_sq
  convert this using 1

theorem deriv_normSq_ζ_cancellationFlow_nonpos {x : M} {t : ℝ} (ht : k.cancellationFlow t x ∈ c.orientedChartTube)
    (hp : c.e.push k.pPerturbationField (k.cancellationFlow t x) = 0) (hq : c.d.push k.qPerturbationField (k.cancellationFlow t x) = 0) :
    HasDerivAt (fun s => ‖c.ζ (k.cancellationFlow s x)‖ ^ 2)
      (-(4 * (c.lam * (k.βm' (k.cancellationFlow t x) * c.ψm' (k.cancellationFlow t x)))) * ‖c.ζ (k.cancellationFlow t x)‖ ^ 2) t := by
  have h := k.hasDerivAt_normSq_ζ_cancellationFlow ht.1
  rw [k.dζ_cancellationField ht hp hq, inner_smul_right, real_inner_self_eq_norm_sq] at h
  convert h using 1; ring

theorem exists_uniform_time {C O : Set M} (hC : IsCompact C) (hO : IsOpen O)
    (h : ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ O) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x ∈ C, ∃ t ∈ Icc 0 T, k.cancellationFlow t x ∈ O := by
  set U : {t : ℝ // 0 ≤ t} → Set M := fun t => k.cancellationFlow t.1 ⁻¹' O with hU
  have hUo : ∀ t, IsOpen (U t) := fun t => hO.preimage (k.continuous_cancellationFlow t.1)
  have hcov : C ⊆ ⋃ t, U t := fun x hx => by
    obtain ⟨t, ht, hmem⟩ := h x hx
    exact mem_iUnion.2 ⟨⟨t, ht⟩, hmem⟩
  obtain ⟨sf, hsf⟩ := hC.elim_finite_subcover U hUo hcov
  classical
  refine ⟨∑ t ∈ sf, t.1, Finset.sum_nonneg fun t _ => t.2, fun x hx => ?_⟩
  obtain ⟨t, ht, hmem⟩ := mem_iUnion₂.1 (hsf hx)
  exact ⟨t.1, ⟨t.2, Finset.single_le_sum (f := fun t : {t : ℝ // 0 ≤ t} => t.1)
    (fun t _ => t.2) ht⟩, hmem⟩

theorem hasDerivAt_comp_cancellationFlow_shift {L : M → ℝ} {x : M} {t r : ℝ}
    (h : HasDerivAt (fun s => L (k.cancellationFlow s (k.cancellationFlow t x))) r 0) :
    HasDerivAt (fun s => L (k.cancellationFlow s x)) r t := by
  have h2 : HasDerivAt (fun s => L (k.cancellationFlow (t + s) x)) r 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    change L (k.cancellationFlow (t + s) x) = L (k.cancellationFlow s (k.cancellationFlow t x))
    rw [k.cancellationFlow_cancellationFlow]
  have h2' : HasDerivAt (fun s => L (k.cancellationFlow (t + s) x)) r (t - t) := by rwa [sub_self]
  have h3 := h2'.comp_sub_const t t
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change L (k.cancellationFlow s x) = L (k.cancellationFlow (t + (s - t)) x)
  rw [add_sub_cancel]

def toFlow : Flow ℝ M where
  toFun := k.cancellationFlow
  cont' := k.continuous_cancellationFlow_joint
  map_add' := fun t₁ t₂ x => by rw [add_comm, k.cancellationFlow_add]
  map_zero' := k.cancellationFlow_zero

theorem toFlow_apply (t : ℝ) (x : M) : k.toFlow t x = k.cancellationFlow t x := rfl

theorem tendsto_add_atTop (t : ℝ) : Tendsto (t + ·) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b - t, fun s hs => by linarith⟩

theorem exists_omegaLimit_subset {C : Set M} (hC : IsCompact C) {L₁ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.cancellationFlow s x)) r 0 ∧ (r = 0 → x ∈ Z))
    {x : M} (hcon : ∀ t, 0 ≤ t → k.cancellationFlow t x ∈ C) :
    ∃ Ω : Set M, Ω.Nonempty ∧ IsCompact Ω ∧ Ω ⊆ C ∩ Z ∧ ∀ t, MapsTo (k.cancellationFlow t) Ω Ω := by
  set g : ℝ → ℝ := fun t => L₁ (k.cancellationFlow t x) with hg
  have hder : ∀ t, 0 ≤ t → ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt g r t := by
    intro t ht
    obtain ⟨r, hr, hd', -⟩ := hd₁ _ (hcon t ht)
    exact ⟨r, hr, k.hasDerivAt_comp_cancellationFlow_shift hd'⟩
  have hanti : AntitoneOn g (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · intro t ht
      obtain ⟨r, -, h⟩ := hder t ht
      exact h.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      obtain ⟨r, -, h⟩ := hder t ht.le
      exact h.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      obtain ⟨r, hr, h⟩ := hder t ht.le
      rw [h.deriv]; exact hr
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hL₁
  set G : ℝ → ℝ := fun t => g (max t 0) with hG
  have hGanti : Antitone G := fun a b hab =>
    hanti (by simp) (by simp) (max_le_max hab le_rfl)
  have hGbdd : BddBelow (range G) := ⟨-B, by
    rintro _ ⟨m, rfl⟩
    have h1 := hB _ (hcon (max m 0) (le_max_right _ _))
    rw [Real.norm_eq_abs] at h1
    have := neg_abs_le (L₁ (k.cancellationFlow (max m 0) x))
    change -B ≤ L₁ (k.cancellationFlow (max m 0) x)
    linarith⟩
  set ℓ := ⨅ m, G m with hℓ
  have hGℓ : Tendsto G atTop (𝓝 ℓ) := tendsto_atTop_ciInf hGanti hGbdd
  have hGle : ∀ m, ℓ ≤ G m := fun m => ciInf_le hGbdd m
  have hGeq : ∀ t, 0 ≤ t → G t = L₁ (k.cancellationFlow t x) := fun t ht => by
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
    obtain ⟨r, hr0, hdz, hrZ⟩ := hd₁ z hzC
    by_contra hzZ
    have hrneg : r < 0 := lt_of_le_of_ne hr0 fun h => hzZ (hrZ h)
    have hzF : ClusterPt z F :=
      ((mem_omegaLimit_singleton_iff_mapClusterPt atTop (⇑k.toFlow) x z).1 hz).clusterPt
    have hLz : L₁ z = ℓ := by
      by_contra hne
      set ε := |L₁ z - ℓ| / 2 with hε
      have hε0 : 0 < ε := by
        have : 0 < |L₁ z - ℓ| := abs_pos.2 (sub_ne_zero.2 hne)
        positivity
      have h1 : ∀ᶠ y in 𝓝[C] z, |L₁ y - L₁ z| < ε :=
        (hL₁ z hzC).tendsto (Metric.ball_mem_nhds (L₁ z) hε0)
      have h2 : ∀ᶠ y in F, |L₁ y - ℓ| < ε := by
        rw [hF, eventually_map]
        filter_upwards [hGℓ (Metric.ball_mem_nhds ℓ hε0), eventually_ge_atTop 0] with t ht ht0
        rw [← hGeq t ht0]; exact ht
      obtain ⟨y, hy1, hy2⟩ :=
        ((frequently_of_clusterPt_within hzF hFC h1).and_eventually h2).exists
      have := abs_sub_le (L₁ z) (L₁ y) ℓ
      rw [abs_sub_comm (L₁ z) (L₁ y)] at this
      linarith
    obtain ⟨t₀, ht₀, hlt⟩ := exists_pos_gt_of_hasDerivAt_neg hrneg hdz
    rw [k.cancellationFlow_zero, hLz] at hlt
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
    have h1 : ∀ᶠ y in 𝓝[C] (k.cancellationFlow t₀ z), L₁ y < ℓ := (hL₁ _ hzC').tendsto (Iio_mem_nhds hlt)
    have h2 : ∀ᶠ y in F', ℓ ≤ L₁ y := by
      rw [hF', hF, map_map, eventually_map]
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      change ℓ ≤ L₁ (k.cancellationFlow t₀ (k.cancellationFlow t x))
      rw [k.cancellationFlow_cancellationFlow, ← hGeq _ (by positivity)]
      exact hGle _
    obtain ⟨y, hy1, hy2⟩ :=
      ((frequently_of_clusterPt_within hzF' hF'C h1).and_eventually h2).exists
    linarith
  exact ⟨Ω, hΩne, hΩc, fun z hz => ⟨hΩC hz, hΩZ z hz⟩, hinv⟩

theorem exists_exit_of_lyapunov_pair {C : Set M} (hC : IsCompact C) {L₁ L₂ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) (hL₂ : ContinuousOn L₂ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.cancellationFlow s x)) r 0 ∧ (r = 0 → x ∈ Z))
    (hd₂ : ∀ x ∈ C ∩ Z, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L₂ (k.cancellationFlow s x)) r 0) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ C := by
  intro x _
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω, hΩne, hΩc, hΩCZ, hinv⟩ := k.exists_omegaLimit_subset hC hL₁ hd₁ hcon
  obtain ⟨w, hwΩ, hwmax⟩ := hΩc.exists_isMaxOn hΩne (hL₂.mono fun z hz => (hΩCZ hz).1)
  obtain ⟨r, hr, hdw⟩ := hd₂ w (hΩCZ hwΩ)
  obtain ⟨t₀, -, hgt⟩ := exists_pos_lt_of_hasDerivAt_pos hr hdw
  have h1 : L₂ (k.cancellationFlow 0 w) < L₂ (k.cancellationFlow t₀ w) := hgt
  rw [k.cancellationFlow_zero] at h1
  have h2 : L₂ (k.cancellationFlow t₀ w) ≤ L₂ w := hwmax (hinv t₀ hwΩ)
  linarith

theorem exists_exit_of_lyapunov_weak {C : Set M} (hC : IsCompact C) {L₁ : M → ℝ}
    (hL₁ : ContinuousOn L₁ C) {Z : Set M}
    (hd₁ : ∀ x ∈ C, ∃ r : ℝ, r ≤ 0 ∧ HasDerivAt (fun s => L₁ (k.cancellationFlow s x)) r 0 ∧ (r = 0 → x ∈ Z))
    (hZ : ∀ z ∈ C ∩ Z, ∃ t : ℝ, k.cancellationFlow t z ∉ C ∩ Z) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ C := by
  intro x _
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω, ⟨w, hwΩ⟩, -, hΩCZ, hinv⟩ := k.exists_omegaLimit_subset hC hL₁ hd₁ hcon
  obtain ⟨t, ht⟩ := hZ w (hΩCZ hwΩ)
  exact ht (hΩCZ (hinv t hwΩ))

theorem exists_notMem_union_of_disjoint_closed {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {z : M} (hz : z ∈ A) {t : ℝ} (ht : 0 ≤ t) (htB : k.cancellationFlow t z ∈ B) :
    ∃ s ∈ Icc 0 t, k.cancellationFlow s z ∉ A ∪ B := by
  by_contra hcon
  push Not at hcon
  have hpre : IsPreconnected (Icc (0 : ℝ) t) := isPreconnected_Icc
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
  have h1 : IsClosed ((fun s => k.cancellationFlow s z) ⁻¹' A) := hA.preimage (k.continuous_cancellationFlow_curve z)
  have h2 : IsClosed ((fun s => k.cancellationFlow s z) ⁻¹' B) := hB.preimage (k.continuous_cancellationFlow_curve z)
  have h3 : Icc (0 : ℝ) t ⊆ (fun s => k.cancellationFlow s z) ⁻¹' A ∪ (fun s => k.cancellationFlow s z) ⁻¹' B :=
    fun s hs => hcon s hs
  have h4 : Icc (0 : ℝ) t ∩ ((fun s => k.cancellationFlow s z) ⁻¹' A ∩ (fun s => k.cancellationFlow s z) ⁻¹' B) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    intro _ hsA hsB
    exact hAB.notMem_of_mem_left hsA hsB
  rcases hpre _ _ h1 h2 h3 h4 with h | h
  · have := h (right_mem_Icc.2 ht)
    exact hAB.notMem_of_mem_left this htB
  · have := h (left_mem_Icc.2 ht)
    rw [mem_preimage, k.cancellationFlow_zero] at this
    exact hAB.notMem_of_mem_left hz this

theorem exists_exit_of_deriv_pos {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C)
    (hd : ∀ x ∈ C, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L (k.cancellationFlow s x)) r 0) :
    ∀ x ∈ C, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ C :=
  k.exists_exit_of_lyapunov_pair hC (L₁ := fun y => -L y) (L₂ := L) hL.neg hL (Z := ∅)
    (fun x hx => by
      obtain ⟨r, hr, hd'⟩ := hd x hx
      exact ⟨-r, by linarith, hd'.neg, fun h => absurd h (by linarith)⟩)
    (fun x hx => absurd hx.2 (notMem_empty x))

theorem exists_notMem_of_two_pieces {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {LA LB : M → ℝ} (hLA : ContinuousOn LA A) (hLB : ContinuousOn LB B)
    (hdA : ∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => LA (k.cancellationFlow s x)) r 0)
    (hdB : ∀ x ∈ B, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => LB (k.cancellationFlow s x)) r 0) :
    ∀ z ∈ A ∪ B, ∃ t : ℝ, k.cancellationFlow t z ∉ A ∪ B := by
  rintro z (hz | hz)
  · obtain ⟨t, ht, htA⟩ := k.exists_exit_of_deriv_pos hA hLA hdA z hz
    by_cases htB : k.cancellationFlow t z ∈ B
    · obtain ⟨s, -, hs⟩ := k.exists_notMem_union_of_disjoint_closed hA.isClosed hB.isClosed hAB
        hz ht htB
      exact ⟨s, hs⟩
    · exact ⟨t, fun h => h.elim htA htB⟩
  · obtain ⟨t, ht, htB⟩ := k.exists_exit_of_deriv_pos hB hLB hdB z hz
    by_cases htA : k.cancellationFlow t z ∈ A
    · obtain ⟨s, -, hs⟩ := k.exists_notMem_union_of_disjoint_closed hB.isClosed hA.isClosed
        hAB.symm hz ht htA
      exact ⟨s, fun h => hs (h.symm)⟩
    · exact ⟨t, fun h => h.elim htA htB⟩

theorem exists_uniform_exit_of_deriv_pos {C : Set M} (hC : IsCompact C) {L : M → ℝ}
    (hL : ContinuousOn L C)
    (hd : ∀ x ∈ C, ∃ r : ℝ, 0 < r ∧ HasDerivAt (fun s => L (k.cancellationFlow s x)) r 0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ x ∈ C, ∃ t ∈ Icc 0 T, k.cancellationFlow t x ∉ C :=
  k.exists_uniform_time hC hC.isClosed.isOpen_compl (k.exists_exit_of_deriv_pos hC hL hd)

theorem exists_first_hit {C : Set M} (hC : IsClosed C) {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hhit : k.cancellationFlow t x ∈ C) :
    ∃ t₁ ∈ Icc 0 t, k.cancellationFlow t₁ x ∈ C ∧ ∀ s ∈ Ico 0 t₁, k.cancellationFlow s x ∉ C := by
  obtain ⟨s₀, hs₀, hs₀K, hmin⟩ := exists_first_time hC (k.continuous_cancellationFlow_curve x)
    (t := t) ⟨t, ⟨ht, le_rfl⟩, hhit⟩
  exact ⟨s₀, hs₀, hs₀K, hmin⟩

theorem mem_closedFlowTube_iff {x : M} : x ∈ k.closedFlowTube ↔ x ∈ c.orientedChartTube ∧
    f x ∈ Icc (c.c₁ - c.η / 2) (c.c₂ + c.η / 2) ∧ ‖c.ζ x‖ ≤ k.δ' := by
  constructor
  · intro hx
    have hT := k.closedFlowTube_subset_orientedChartTube hx
    refine ⟨hT, hx.1, ?_⟩
    obtain ⟨y, hy, hyx⟩ := hx.2
    have hw : c.w x = y := by
      unfold w
      rw [← hyx, c.d.χ.left_inv (c.d.hsrc y ((k.morseNorm_lt_rm_of_mem_qTubeCoordinates hy).le.trans
        (c.D.hrm q c.hq).2))]
    have h1 : morseNorm n y ^ 2 ≤ 2 * k.δ' ^ 2 + 2 * c.ε₂ := hy.1
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk, ← hw, c.normSq_negPart_w hT.1,
      ← c.ζ_def] at h1
    have h2 : ‖c.ζ x‖ ^ 2 ≤ k.δ' ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h2
  · rintro ⟨hT, hf, hζ⟩
    refine ⟨hf, ?_⟩
    change c.D.π c.c₂ x ∈ c.d.χ '' k.qTubeCoordinates
    refine ⟨c.w x, ⟨?_, hT.2.le⟩, c.chart_w hT.1⟩
    have h := c.normSq_negPart_w hT.1
    rw [morseNorm_sq_eq_negPart_add_posPart c.d.hk, h, ← c.ζ_def]
    have := pow_le_pow_left₀ (norm_nonneg _) hζ 2
    linarith

theorem mem_orientedChartTube_of_mem_closedFlowTube {x : M} (hx : x ∈ k.closedFlowTube) : x ∈ c.orientedChartTube :=
  k.closedFlowTube_subset_orientedChartTube hx

theorem norm_ζ_le_of_mem_closedFlowTube {x : M} (hx : x ∈ k.closedFlowTube) : ‖c.ζ x‖ ≤ k.δ' :=
  (k.mem_closedFlowTube_iff.1 hx).2.2

theorem continuousOn_ζ_closedFlowTube : ContinuousOn c.ζ k.closedFlowTube :=
  c.continuousOn_ζ.mono fun _ hx => (k.mem_orientedChartTube_of_mem_closedFlowTube hx).1

theorem push_pPerturbationField_eq_zero_of_lo₂_le {x : M} (hx : c.lo₂ ≤ f x) : c.e.push k.pPerturbationField x = 0 := by
  by_cases hK : x ∈ c.e.χ '' pSupportRegion k.δ k.τ c.e₁ c.ρB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyR : morseNorm n y ≤ c.e.R := hy.1.trans c.ρB_le_R
    rw [MorseNormalChart.push_apply_chart _ (c.e.mem_ball_of_le hyR)]
    have hf := c.f_chart_p hyR
    have hρ : c.ρB ≤ morseNorm n y := by
      have h := c.ρB_sq_eq
      have : c.ρB ^ 2 ≤ morseNorm n y ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ c.ρB_pos.le (ModelField.morseNorm_nonneg y) two_ne_zero).1 this
    have : k.pPerturbationField y = 0 := by
      change CancelModel.pPerturbationField c.m' k.δ k.τ c.ρA c.ρB c.e₁ y = 0
      rw [CancelModel.pPerturbationField, ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hρ, mul_zero, mul_zero, zero_smul]
    rw [this]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.e.χ y).map_zero
  · exact k.push_pPerturbationField_eq_zero_of_notMem hK

theorem push_qPerturbationField_eq_zero_of_le_hi₁ {x : M} (hx : f x ≤ c.hi₁) : c.d.push k.qPerturbationField x = 0 := by
  by_cases hK : x ∈ c.d.χ '' qSupportRegion c.d.hk c.hkq k.δ k.τ c.σ c.uB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyR : morseNorm n y ≤ c.d.R := by
      have := (morseNorm_sq_le_of_mem_qSupportRegion c.d.hk c.hkq hy).trans k.Kq_radius_lt.le
      exact ((Real.le_sqrt (ModelField.morseNorm_nonneg y) (by linarith [c.hε])).2 this).trans
        (by linarith [c.sqrt_three_ε_lt_rmq, (c.D.hrm q c.hq).2])
    rw [MorseNormalChart.push_apply_chart _ (c.d.mem_ball_of_le hyR)]
    have hf := c.f_chart_q hyR
    have hu : c.uB ^ 2 ≤ uq c.d.hk c.hkq y ^ 2 := by
      have h := c.uB_sq_eq
      nlinarith [sq_nonneg ‖posPart c.d.hk y‖]
    have : k.qPerturbationField y = 0 := by
      change CancelModel.qPerturbationField c.d.hk c.hkq k.δ k.τ c.σ c.m' c.uA c.uB y = 0
      rw [CancelModel.qPerturbationField, ψq_eq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB hu, mul_zero, mul_zero, neg_zero,
        zero_smul]
    rw [this]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.d.χ y).map_zero
  · exact k.push_qPerturbationField_eq_zero_of_notMem hK

theorem dfV_localizedMiddlePerturbation {x : M} (hx : x ∈ c.orientedChartTube) :
    dfV I f k.localizedMiddlePerturbation x = 2 * (k.βm x * c.ψm x) := by
  have h : dfV I f k.localizedMiddlePerturbation x = dfV I f k.middlePerturbation x := by unfold dfV; rw [k.localizedMiddlePerturbation_of_mem hx]
  rw [h]
  unfold middlePerturbation dfV
  simp only [map_add, map_smul, map_neg]
  have h1 := c.dfV_V_eq_neg_one_of_mem_tube hx.1.1
  have h2 := c.df_transverseField hx.1
  unfold dfV at h1 h2
  rw [h1, h2]
  simp

theorem dfV_cancellationField_tube {x : M} (hx : x ∈ c.orientedChartTube) (hp : c.e.push k.pPerturbationField x = 0)
    (hq : c.d.push k.qPerturbationField x = 0) : dfV I f k.cancellationField x = -1 + 2 * (k.βm x * c.ψm x) := by
  have e : k.cancellationField = fun x => (fun x => (fun x => c.D.V x + c.e.push k.pPerturbationField x) x + c.d.push k.qPerturbationField x) x
      + k.localizedMiddlePerturbation x := rfl
  rw [e, dfV_add, dfV_add, dfV_add, c.dfV_V_eq_neg_one_of_mem_tube hx.1.1, k.dfV_localizedMiddlePerturbation hx]
  have hp' : dfV I f (c.e.push k.pPerturbationField) x = 0 := by unfold dfV; rw [hp]; simp
  have hq' : dfV I f (c.d.push k.qPerturbationField) x = 0 := by unfold dfV; rw [hq]; simp
  rw [hp', hq']; ring

theorem dfV_cancellationField_mid {x : M} (hx : x ∈ c.orientedChartTube) (h1 : c.lo₂ ≤ f x) (h2 : f x ≤ c.hi₁) :
    dfV I f k.cancellationField x = -1 + 2 * k.βm x := by
  rw [k.dfV_cancellationField_tube hx (k.push_pPerturbationField_eq_zero_of_lo₂_le h1) (k.push_qPerturbationField_eq_zero_of_le_hi₁ h2),
    c.ψm_eq_one h1 h2, mul_one]

theorem dζ_cancellationField_mid {x : M} (hx : x ∈ c.orientedChartTube) (h1 : c.lo₂ ≤ f x) (h2 : f x ≤ c.hi₁) :
    c.dζ k.cancellationField x = -(2 * (c.lam * k.βm' x)) • c.ζ x := by
  rw [k.dζ_cancellationField hx (k.push_pPerturbationField_eq_zero_of_lo₂_le h1) (k.push_qPerturbationField_eq_zero_of_le_hi₁ h2),
    c.ψm'_eq_one (c.lo₁_lt_lo₂.le.trans h1) (h2.trans c.hi₁_lt_hi₂.le), mul_one]

theorem hasDerivAt_normSq_ζ_cancellationFlow_mid {x : M} (hx : x ∈ c.orientedChartTube) (h1 : c.lo₂ ≤ f x)
    (h2 : f x ≤ c.hi₁) :
    HasDerivAt (fun s => ‖c.ζ (k.cancellationFlow s x)‖ ^ 2) (-(4 * (c.lam * k.βm' x)) * ‖c.ζ x‖ ^ 2) 0 := by
  have h := k.hasDerivAt_normSq_ζ_cancellationFlow (t := 0) (by rw [k.cancellationFlow_zero]; exact hx.1)
  rw [k.cancellationFlow_zero, k.dζ_cancellationField_mid hx h1 h2, inner_smul_right, real_inner_self_eq_norm_sq] at h
  convert h using 1; ring

theorem hasDerivAt_f_cancellationFlow_mid {x : M} (hx : x ∈ c.orientedChartTube) (h1 : c.lo₂ ≤ f x)
    (h2 : f x ≤ c.hi₁) : HasDerivAt (fun s => f (k.cancellationFlow s x)) (-1 + 2 * k.βm x) 0 := by
  have h := k.hasDerivAt_f_cancellationFlow x 0
  rwa [k.cancellationFlow_zero, k.dfV_cancellationField_mid hx h1 h2] at h

def middleTube : Set M := k.closedFlowTube ∩ {y | c.lo₂ ≤ f y ∧ f y ≤ c.hi₁}

theorem isCompact_middleTube : IsCompact k.middleTube :=
  k.isCompact_closedFlowTube.inter_right c.isClosed_mid_levels

theorem middleTube_subset_orientedChartTube : k.middleTube ⊆ c.orientedChartTube := fun _ hx =>
  k.mem_orientedChartTube_of_mem_closedFlowTube hx.1

theorem continuousOn_ζ_middleTube : ContinuousOn c.ζ k.middleTube :=
  k.continuousOn_ζ_closedFlowTube.mono inter_subset_left

theorem exists_exit_middleTube : ∀ x ∈ k.middleTube, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ k.middleTube := by
  have hlam := c.lam_pos
  set A : Set M := k.middleTube ∩ c.ζ ⁻¹' {0} with hA
  set B : Set M := k.middleTube ∩ c.ζ ⁻¹' {v | k.δ' ≤ ‖v‖} with hB
  have hAc : IsCompact A := k.isCompact_middleTube.of_isClosed_subset
    (k.continuousOn_ζ_middleTube.preimage_isClosed_of_isClosed k.isCompact_middleTube.isClosed
      isClosed_singleton) inter_subset_left
  have hBc : IsCompact B := k.isCompact_middleTube.of_isClosed_subset
    (k.continuousOn_ζ_middleTube.preimage_isClosed_of_isClosed k.isCompact_middleTube.isClosed
      (isClosed_le continuous_const continuous_norm)) inter_subset_left
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hy1⟩ ⟨-, hy2⟩
    have h1 : c.ζ y = 0 := hy1
    have h2 : k.δ' ≤ ‖c.ζ y‖ := hy2
    rw [h1, norm_zero] at h2
    linarith [k.δ'_pos]
  refine k.exists_exit_of_lyapunov_weak k.isCompact_middleTube (L₁ := fun y => ‖c.ζ y‖ ^ 2)
    (k.continuousOn_ζ_middleTube.norm.pow 2) (Z := {y | c.ζ y = 0 ∨ k.δ' ≤ ‖c.ζ y‖}) ?_ ?_
  · intro y hy
    have hT := k.middleTube_subset_orientedChartTube hy
    refine ⟨-(4 * (c.lam * k.βm' y)) * ‖c.ζ y‖ ^ 2, ?_, k.hasDerivAt_normSq_ζ_cancellationFlow_mid hT hy.2.1 hy.2.2,
      ?_⟩
    · have := k.βm'_nonneg y
      have : 0 ≤ 4 * (c.lam * k.βm' y) * ‖c.ζ y‖ ^ 2 := by positivity
      linarith
    · intro h0
      rcases mul_eq_zero.1 h0 with h | h
      · right
        have hβ : k.βm' y = 0 := by
          rcases mul_eq_zero.1 (neg_eq_zero.1 h) with h' | h'
          · norm_num at h'
          · rcases mul_eq_zero.1 h' with h'' | h''
            · exact absurd h'' hlam.ne'
            · exact h''
        have := (cut_eq_zero_iff k.two_δ_sq_lt_δ'_sq).1 hβ
        exact (pow_le_pow_iff_left₀ k.δ'_pos.le (norm_nonneg _) two_ne_zero).1 this
      · left
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  · have hTZ : k.middleTube ∩ {y | c.ζ y = 0 ∨ k.δ' ≤ ‖c.ζ y‖} = A ∪ B := by
      ext y
      simp only [hA, hB, mem_inter_iff, mem_union, mem_ofPred_eq, mem_preimage,
        mem_singleton_iff]
      tauto
    rw [hTZ]
    refine k.exists_notMem_of_two_pieces hAc hBc hAB (LA := f) (LB := fun y => -f y)
      (c.hfs.continuous.continuousOn) (c.hfs.continuous.neg.continuousOn) ?_ ?_
    · rintro y ⟨hy, hζ⟩
      have hζ' : c.ζ y = 0 := hζ
      have hT := k.middleTube_subset_orientedChartTube hy
      refine ⟨-1 + 2 * k.βm y, ?_, k.hasDerivAt_f_cancellationFlow_mid hT hy.2.1 hy.2.2⟩
      rw [k.βm_eq_one_of_ζ_eq_zero hζ']; norm_num
    · rintro y ⟨hy, hζ⟩
      have hζ' : k.δ' ≤ ‖c.ζ y‖ := hζ
      have hT := k.middleTube_subset_orientedChartTube hy
      have hβ : k.βm y = 0 := by
        by_contra h
        have := k.norm_ζ_lt_of_βm_ne_zero h
        linarith [k.hδδ']
      refine ⟨-(-1 + 2 * k.βm y), ?_, (k.hasDerivAt_f_cancellationFlow_mid hT hy.2.1 hy.2.2).neg⟩
      rw [hβ]; norm_num

theorem hasDerivAt_normSq_ζ_cancellationFlow_mid' {x : M} {u : ℝ} (hu : k.cancellationFlow u x ∈ c.orientedChartTube)
    (h1 : c.lo₂ ≤ f (k.cancellationFlow u x)) (h2 : f (k.cancellationFlow u x) ≤ c.hi₁) :
    HasDerivAt (fun s => ‖c.ζ (k.cancellationFlow s x)‖ ^ 2)
      (-(4 * (c.lam * k.βm' (k.cancellationFlow u x))) * ‖c.ζ (k.cancellationFlow u x)‖ ^ 2) u :=
  k.hasDerivAt_comp_cancellationFlow_shift (L := fun y => ‖c.ζ y‖ ^ 2) (k.hasDerivAt_normSq_ζ_cancellationFlow_mid hu h1 h2)

theorem hasDerivAt_f_cancellationFlow_mid' {x : M} {u : ℝ} (hu : k.cancellationFlow u x ∈ c.orientedChartTube)
    (h1 : c.lo₂ ≤ f (k.cancellationFlow u x)) (h2 : f (k.cancellationFlow u x) ≤ c.hi₁) :
    HasDerivAt (fun s => f (k.cancellationFlow s x)) (-1 + 2 * k.βm (k.cancellationFlow u x)) u :=
  k.hasDerivAt_comp_cancellationFlow_shift (L := f) (k.hasDerivAt_f_cancellationFlow_mid hu h1 h2)

theorem cancellationFlow_mem_middleTube_of_notMem_outsideMiddleBand {x : M} (hx : x ∈ k.middleTube) {t : ℝ}
    (hE : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∉ c.outsideMiddleBand) : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.middleTube := by
  have hQ : IsClosed {s : ℝ | k.cancellationFlow s x ∈ k.middleTube} :=
    k.isCompact_middleTube.isClosed.preimage (k.continuous_cancellationFlow_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsT : k.cancellationFlow s x ∈ k.middleTube := hIcc (right_mem_Icc.2 hs.1)
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_orientedChartTube
    (k.middleTube_subset_orientedChartTube hsT)
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  have hs't : s' ≤ t := hs'.2.trans (min_le_right _ _)
  have hs'0 : 0 ≤ s' := hs.1.trans hs'.1.le
  have hmid : ∀ u ∈ Icc s s', k.cancellationFlow u x ∈ c.orientedChartTube ∧
      c.lo₂ ≤ f (k.cancellationFlow u x) ∧ f (k.cancellationFlow u x) ≤ c.hi₁ := by
    intro u hu
    have hu' := c.lt_of_notMem_outsideMiddleBand (hE u ⟨hs.1.trans hu.1, hu.2.trans hs't⟩)
    exact ⟨hεO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩, hu'.1.le, hu'.2.le⟩
  have hanti : AntitoneOn (fun u => ‖c.ζ (k.cancellationFlow u x)‖ ^ 2) (Icc s s') := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s s') ?_ ?_ ?_
    · intro u hu
      exact (k.hasDerivAt_normSq_ζ_cancellationFlow_mid' (hmid u hu).1 (hmid u hu).2.1
        (hmid u hu).2.2).continuousAt.continuousWithinAt
    · intro u hu
      have hu' := interior_subset hu
      exact (k.hasDerivAt_normSq_ζ_cancellationFlow_mid' (hmid u hu').1 (hmid u hu').2.1
        (hmid u hu').2.2).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' := interior_subset hu
      rw [(k.hasDerivAt_normSq_ζ_cancellationFlow_mid' (hmid u hu').1 (hmid u hu').2.1 (hmid u hu').2.2).deriv]
      have := k.βm'_nonneg (k.cancellationFlow u x)
      have := c.lam_pos
      have : 0 ≤ 4 * (c.lam * k.βm' (k.cancellationFlow u x)) * ‖c.ζ (k.cancellationFlow u x)‖ ^ 2 := by positivity
      linarith
  have hζ := hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
  have hζs := k.norm_ζ_le_of_mem_closedFlowTube hsT.1
  have hζ' : ‖c.ζ (k.cancellationFlow s' x)‖ ≤ k.δ' := by
    have h1 : ‖c.ζ (k.cancellationFlow s' x)‖ ^ 2 ≤ k.δ' ^ 2 :=
      hζ.trans (pow_le_pow_left₀ (norm_nonneg _) hζs 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h1
  have hlev := (hmid s' (right_mem_Icc.2 hs'.1.le))
  refine ⟨k.mem_closedFlowTube_iff.2 ⟨hlev.1, ⟨?_, ?_⟩, hζ'⟩, hlev.2⟩
  · linarith [hlev.2.1, c.lo₂_mem_levels]
  · linarith [hlev.2.2, c.hi₁_mem_levels]

theorem exists_exit_mid_band {x : M} (hx : x ∈ k.middleTube) :
    ∃ t, 0 ≤ t ∧ (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.middleTube) ∧
      (∀ s ∈ Ico 0 t, c.lo₂ < f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) < c.hi₁) ∧
      ((f (k.cancellationFlow t x) = c.hi₁ ∧ (0 < t → ‖c.ζ (k.cancellationFlow t x)‖ < 2 * k.δ)) ∨ f (k.cancellationFlow t x) = c.lo₂) := by
  obtain ⟨t, ht, htT⟩ := k.exists_exit_middleTube x hx
  have hhit : ∃ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.outsideMiddleBand := by
    by_contra h
    push Not at h
    exact htT (k.cancellationFlow_mem_middleTube_of_notMem_outsideMiddleBand hx h t (right_mem_Icc.2 ht))
  obtain ⟨s₀, hs₀, hs₀E, hmin⟩ := exists_first_time c.isClosed_outsideMiddleBand (k.continuous_cancellationFlow_curve x) hhit
  have hbefore : ∀ s ∈ Ico 0 s₀, k.cancellationFlow s x ∈ k.middleTube := fun s hs =>
    k.cancellationFlow_mem_middleTube_of_notMem_outsideMiddleBand hx (fun u hu => hmin u ⟨hu.1, hu.2.trans_lt hs.2⟩) s
      (right_mem_Icc.2 hs.1)
  have hs₀T : k.cancellationFlow s₀ x ∈ k.middleTube := by
    rcases hs₀.1.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hx
    · refine k.isCompact_middleTube.isClosed.mem_of_tendsto
        ((k.continuous_cancellationFlow_curve x).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio s₀))) ?_
      filter_upwards [Ico_mem_nhdsLT h] with s hs using hbefore s hs
  have hall : ∀ s ∈ Icc 0 s₀, k.cancellationFlow s x ∈ k.middleTube := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h]; exact hs₀T
    · exact hbefore s ⟨hs.1, h⟩
  have hopen : ∀ s ∈ Ico 0 s₀, c.lo₂ < f (k.cancellationFlow s x) ∧ f (k.cancellationFlow s x) < c.hi₁ := fun s hs =>
    c.lt_of_notMem_outsideMiddleBand (hmin s hs)
  refine ⟨s₀, hs₀.1, hall, hopen, ?_⟩
  rcases hs₀E with h | h
  · right
    exact le_antisymm h hs₀T.2.1
  · left
    have hf : f (k.cancellationFlow s₀ x) = c.hi₁ := le_antisymm hs₀T.2.2 h
    refine ⟨hf, fun hpos => ?_⟩
    have hd := k.hasDerivAt_f_cancellationFlow_mid' (k.middleTube_subset_orientedChartTube hs₀T) hs₀T.2.1 hs₀T.2.2
    have hr := nonneg_of_hasDerivAt_of_le_left hpos hd fun s hs => by
      have := (hopen s ⟨by linarith [hs.1], hs.2⟩).2
      rw [hf]; exact this.le
    have hβ : k.βm (k.cancellationFlow s₀ x) ≠ 0 := by
      intro h0; rw [h0] at hr; linarith
    exact k.norm_ζ_lt_of_βm_ne_zero hβ

open scoped Classical in
def pReversalWeight (y : Fin n → ℝ) : ℝ := if c.e.χ y ∈ c.orientedChartTube then k.βm (c.e.χ y) * c.ψm (c.e.χ y) else 0

open scoped Classical in
def pTransverseWeight (y : Fin n → ℝ) : ℝ :=
  if c.e.χ y ∈ c.orientedChartTube then k.βm' (c.e.χ y) * c.ψm' (c.e.χ y) else 0

theorem pReversalWeight_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.orientedChartTube) :
    k.pReversalWeight y = k.βm (c.e.χ y) * c.ψm (c.e.χ y) := by classical simp [pReversalWeight, h]

theorem pReversalWeight_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.orientedChartTube) : k.pReversalWeight y = 0 := by
  classical simp [pReversalWeight, h]

theorem pTransverseWeight_of_mem {y : Fin n → ℝ} (h : c.e.χ y ∈ c.orientedChartTube) :
    k.pTransverseWeight y = k.βm' (c.e.χ y) * c.ψm' (c.e.χ y) := by classical simp [pTransverseWeight, h]

theorem pTransverseWeight_of_notMem {y : Fin n → ℝ} (h : c.e.χ y ∉ c.orientedChartTube) : k.pTransverseWeight y = 0 := by
  classical simp [pTransverseWeight, h]

theorem pReversalWeight_nonneg (y : Fin n → ℝ) : 0 ≤ k.pReversalWeight y := by
  classical
  unfold pReversalWeight; split_ifs
  · exact mul_nonneg (k.βm_nonneg _) (c.ψm_nonneg _)
  · exact le_rfl

theorem pReversalWeight_le_one (y : Fin n → ℝ) : k.pReversalWeight y ≤ 1 := by
  classical
  unfold pReversalWeight; split_ifs
  · exact (mul_le_mul (k.βm_le_one _) (c.ψm_le_one _) (c.ψm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem pTransverseWeight_nonneg (y : Fin n → ℝ) : 0 ≤ k.pTransverseWeight y := by
  classical
  unfold pTransverseWeight; split_ifs
  · exact mul_nonneg (k.βm'_nonneg _) (c.ψm'_nonneg _)
  · exact le_rfl

theorem pTransverseWeight_le_one (y : Fin n → ℝ) : k.pTransverseWeight y ≤ 1 := by
  classical
  unfold pTransverseWeight; split_ifs
  · exact (mul_le_mul (k.βm'_le_one _) (c.ψm'_le_one _) (c.ψm'_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  · exact zero_le_one

theorem pReversalWeight_eq_zero_of_pTransverseWeight_eq_zero {y : Fin n → ℝ} (h : k.pTransverseWeight y = 0) : k.pReversalWeight y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pTransverseWeight_of_mem hT] at h
    rw [k.pReversalWeight_of_mem hT]
    exact k.βm_mul_ψm_eq_zero h
  · exact k.pReversalWeight_of_notMem hT

theorem pTransverseWeight_eq_one_of_pReversalWeight_ne_zero {y : Fin n → ℝ} (h : k.pReversalWeight y ≠ 0) : k.pTransverseWeight y = 1 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pReversalWeight_of_mem hT] at h
    rw [k.pTransverseWeight_of_mem hT]
    exact k.βm'_mul_ψm'_eq_one h
  · exact absurd (k.pReversalWeight_of_notMem hT) h

theorem mem_of_pTransverseWeight_ne_zero {y : Fin n → ℝ} (h : k.pTransverseWeight y ≠ 0) :
    c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < k.δ' := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pTransverseWeight_of_mem hT] at h
    exact ⟨hT, k.norm_ζ_lt_of_βm'_ne_zero (mul_ne_zero_iff.1 h).1⟩
  · exact absurd (k.pTransverseWeight_of_notMem hT) h

theorem pReversalWeight_eq_zero_of_norm_ζ {y : Fin n → ℝ} (h : c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖) :
    k.pReversalWeight y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pReversalWeight_of_mem hT]
    have : k.βm (c.e.χ y) = 0 := by
      by_contra h'
      exact absurd (k.norm_ζ_lt_of_βm_ne_zero h') (not_lt.2 (h hT))
    rw [this, zero_mul]
  · exact k.pReversalWeight_of_notMem hT

theorem pReversalWeight_eq_zero_of_f_le {y : Fin n → ℝ} (h : f (c.e.χ y) ≤ c.lo₁) : k.pReversalWeight y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pReversalWeight_of_mem hT, c.ψm_eq_zero_of_le h, mul_zero]
  · exact k.pReversalWeight_of_notMem hT

theorem pTransverseWeight_eq_zero_of_f_le {y : Fin n → ℝ} (h : f (c.e.χ y) ≤ c.c₁ - c.η / 2) : k.pTransverseWeight y = 0 := by
  classical
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pTransverseWeight_of_mem hT]
    have : c.ψm' (c.e.χ y) = 0 := plateau_eq_zero_of_le c.c₁_sub_half_lt_lo₁ h
    rw [this, mul_zero]
  · exact k.pTransverseWeight_of_notMem hT

theorem pCancellationField_eq (y : Fin n → ℝ) :
    k.pCancellationField y = (1 - 2 * k.pReversalWeight y) • ModelField.modelField 0 c.e.r₀ y + k.pPerturbationField y +
      (2 * (c.lam * k.pTransverseWeight y)) • c.pRestrictedTransverseField y := by
  classical
  unfold pCancellationField
  by_cases hT : c.e.χ y ∈ c.orientedChartTube
  · rw [k.pReversalWeight_of_mem hT, k.pTransverseWeight_of_mem hT, c.pRestrictedTransverseField_of_mem hT]
    simp only [hT, ite_true]
    module
  · rw [k.pReversalWeight_of_notMem hT, k.pTransverseWeight_of_notMem hT, c.pRestrictedTransverseField_of_notMem hT]
    simp only [hT, ite_false]
    module

theorem dot_pCancellationField {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) :
    dot y (k.pCancellationField y) = -((1 - 2 * k.pReversalWeight y) * (ModelField.theta c.e.r₀ y * morseNorm n y ^ 2)) +
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axial c.e₁ y := by
  rw [k.pCancellationField_eq, dot_add_right, dot_add_right, dot_smul_right, dot_smul_right, c.dot_pRestrictedTransverseField hy,
    modelField_index_zero, dot_neg_right, dot_smul_right, dot_self]
  have : k.pPerturbationField y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  rw [this, dot_smul_right]
  simp only [axial, mul_zero, add_zero]
  ring

theorem axial_pCancellationField (y : Fin n → ℝ) :
    axial c.e₁ (k.pCancellationField y) = -((1 - 2 * k.pReversalWeight y) * (ModelField.theta c.e.r₀ y * axial c.e₁ y)) +
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) +
      2 * (c.lam * k.pTransverseWeight y) * axial c.e₁ (c.pRestrictedTransverseField y) := by
  rw [k.pCancellationField_eq, axial_add, axial_add, axial_smul, axial_smul, modelField_index_zero, axial_neg,
    axial_smul]
  have : k.pPerturbationField y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  have he : axial c.e₁ c.e₁ = 1 := by rw [axial, dot_self, c.morseNorm_e₁]; norm_num
  rw [this, axial_smul, he]
  ring

theorem axialDefectDeriv_pCancellationField {y : Fin n → ℝ} (hy0 : y ≠ 0) :
    axialDefectDeriv c.e₁ y (k.pCancellationField y) =
      c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axialDefectDeriv c.e₁ y c.e₁ +
      2 * (c.lam * k.pTransverseWeight y) * axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) := by
  rw [k.pCancellationField_eq, map_add, map_add, map_smul, map_smul, modelField_index_zero, map_neg, map_smul,
    axialDefectDeriv_self c.e₁ hy0]
  have : k.pPerturbationField y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
  rw [this, map_smul]
  simp only [smul_eq_mul, mul_zero, neg_zero, zero_add]

theorem axial_pRestrictedTransverseField_pos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hT : c.e.χ y ∈ c.orientedChartTube) (hζ0 : 0 < ‖c.ζ (c.e.χ y)‖) (hζ : ‖c.ζ (c.e.χ y)‖ < k.δ') :
    0 < axial c.e₁ (c.pRestrictedTransverseField y) := by
  have hy0 : y ≠ 0 := c.ne_zero_of_mem_openChartTube hy hT.1
  have h := k.hdB y hy hT hζ0 hζ
  rw [c.pRestrictedTransverseField_of_mem hT]
  rw [axialDefectDeriv_apply] at h
  have horth : dot y (c.pTransverseField y) = 0 := by
    rw [dot_eq_sum]; exact c.transverseField_chart_p_orth (c.morseNorm_lt_rmp_of_sq_lt hy) hT.1
  rw [horth, mul_zero, zero_sub, neg_lt_zero] at h
  have hρ := morseNorm_pos hy0
  rw [axial, dot_comm]
  exact pos_of_mul_pos_right h (inv_pos.2 hρ).le

theorem axialDefectDeriv_pRestrictedTransverseField_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε)
    (hB : k.pTransverseWeight y ≠ 0) : axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) ≤ 0 := by
  obtain ⟨hT, hζ⟩ := k.mem_of_pTransverseWeight_ne_zero hB
  by_cases hζ0 : c.ζ (c.e.χ y) = 0
  · rw [c.pRestrictedTransverseField_eq_zero_of_ζ hT hζ0, map_zero]
  · rw [c.pRestrictedTransverseField_of_mem hT]
    exact (k.hdB y hy hT (norm_pos_iff.2 hζ0) hζ).le

theorem axialDefectDeriv_pCancellationField_nonpos {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0) :
    axialDefectDeriv c.e₁ y (k.pCancellationField y) ≤ 0 := by
  rw [k.axialDefectDeriv_pCancellationField hy0]
  have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axialDefectDeriv c.e₁ y c.e₁ ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
    · rw [axialDefectDeriv_e₁ c.morseNorm_e₁ hy0]
      have := perpSq_nonneg c.morseNorm_e₁ y
      have := morseNorm_pos hy0
      have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
      linarith
  have h2 : 2 * (c.lam * k.pTransverseWeight y) * axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) ≤ 0 := by
    by_cases hB : k.pTransverseWeight y = 0
    · rw [hB]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by have := c.lam_pos; have := k.pTransverseWeight_nonneg y; positivity) (k.axialDefectDeriv_pRestrictedTransverseField_nonpos hy hB)
  linarith

theorem of_axialDefectDeriv_pCancellationField_eq_zero {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0)
    (h : axialDefectDeriv c.e₁ y (k.pCancellationField y) = 0) :
    (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y = 0 ∨ perpSq c.e₁ y = 0) ∧
      (k.pTransverseWeight y = 0 ∨ (c.e.χ y ∈ c.orientedChartTube ∧ c.ζ (c.e.χ y) = 0)) := by
  rw [k.axialDefectDeriv_pCancellationField hy0] at h
  have hA0 : 0 ≤ βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y := mul_nonneg (βp_nonneg _) (ψp_nonneg _)
  have hBe : axialDefectDeriv c.e₁ y c.e₁ ≤ 0 := by
    rw [axialDefectDeriv_e₁ c.morseNorm_e₁ hy0]
    have := perpSq_nonneg c.morseNorm_e₁ y
    have := morseNorm_pos hy0
    have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
    linarith
  have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axialDefectDeriv c.e₁ y c.e₁ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg c.m'_pos.le hA0) hBe
  have h2 : 2 * (c.lam * k.pTransverseWeight y) * axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) ≤ 0 := by
    by_cases hB : k.pTransverseWeight y = 0
    · rw [hB]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by have := c.lam_pos; have := k.pTransverseWeight_nonneg y; positivity) (k.axialDefectDeriv_pRestrictedTransverseField_nonpos hy hB)
  have h1' : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axialDefectDeriv c.e₁ y c.e₁ = 0 := by
    linarith
  have h2' : 2 * (c.lam * k.pTransverseWeight y) * axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) = 0 := by linarith
  constructor
  · rcases mul_eq_zero.1 h1' with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 c.m'_pos.ne'
      · exact Or.inl h4
    · right
      rw [axialDefectDeriv_e₁ c.morseNorm_e₁ hy0, neg_eq_zero, div_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · exact h3
      · exact absurd h3 (pow_ne_zero _ (morseNorm_pos hy0).ne')
  · by_cases hB : k.pTransverseWeight y = 0
    · exact Or.inl hB
    · right
      obtain ⟨hT, hζ⟩ := k.mem_of_pTransverseWeight_ne_zero hB
      refine ⟨hT, ?_⟩
      by_contra hζ0
      have := k.hdB y hy hT (norm_pos_iff.2 hζ0) hζ
      rw [← c.pRestrictedTransverseField_of_mem hT] at this
      have hpos : 0 < 2 * (c.lam * k.pTransverseWeight y) := by
        have := c.lam_pos
        have := lt_of_le_of_ne (k.pTransverseWeight_nonneg y) (Ne.symm hB)
        positivity
      have := mul_neg_of_pos_of_neg hpos this
      linarith

theorem hasDerivAt_morseNormSq_cancellationFlow_p {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall') :
    HasDerivAt (fun s => morseNorm n (c.e.χ.symm (k.cancellationFlow s x)) ^ 2)
      (2 * dot (c.e.χ.symm (k.cancellationFlow s x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x)))) s := by
  have h := (hasFDerivAt_morseNorm_sq (c.e.χ.symm (k.cancellationFlow s x))).comp_hasDerivAt s
    (k.hasDerivAt_symm_cancellationFlow_p hs)
  refine h.congr_deriv ?_
  simp [dotL_apply]

theorem hasDerivAt_axial_cancellationFlow_p {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall') :
    HasDerivAt (fun s => axial c.e₁ (c.e.χ.symm (k.cancellationFlow s x)))
      (axial c.e₁ (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x)))) s := by
  have h := (hasFDerivAt_axial c.e₁ (c.e.χ.symm (k.cancellationFlow s x))).comp_hasDerivAt s
    (k.hasDerivAt_symm_cancellationFlow_p hs)
  refine h.congr_deriv ?_
  rw [dotL_apply, axial, dot_comm]

theorem hasDerivAt_axialDefect_cancellationFlow_p {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall')
    (hy0 : c.e.χ.symm (k.cancellationFlow s x) ≠ 0) :
    HasDerivAt (fun s => axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow s x)))
      (axialDefectDeriv c.e₁ (c.e.χ.symm (k.cancellationFlow s x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x)))) s := by
  have h := (hasFDerivAt_axialDefect c.e₁ hy0).comp_hasDerivAt s (k.hasDerivAt_symm_cancellationFlow_p hs)
  exact h

end CancelConsts

theorem exists_ρs : ∃ ρ : ℝ, c.ρA ≤ ρ ∧ ρ < c.ρB ∧
    ∀ y : Fin n → ℝ, morseNorm n y ≤ ρ → 9 / 10 ≤ ψp c.ρA c.ρB y := by
  have hAB : c.ρA ^ 2 < c.ρB ^ 2 := pow_lt_pow_left₀ c.ρA_lt_ρB c.ρA_pos.le two_ne_zero
  have hc : ContinuousAt (cut (c.ρA ^ 2) (c.ρB ^ 2)) (c.ρA ^ 2) :=
    (contDiff_cut _ _).continuous.continuousAt
  have h1 : cut (c.ρA ^ 2) (c.ρB ^ 2) (c.ρA ^ 2) = 1 := cut_eq_one hAB le_rfl
  have hev : ∀ᶠ t in 𝓝 (c.ρA ^ 2), 9 / 10 < cut (c.ρA ^ 2) (c.ρB ^ 2) t :=
    hc (Ioi_mem_nhds (by rw [h1]; norm_num))
  obtain ⟨w, hw, hball⟩ := Metric.mem_nhds_iff.1 hev
  set w' := min (w / 2) ((c.ρB ^ 2 - c.ρA ^ 2) / 2) with hw'
  have hw'0 : 0 < w' := lt_min (by positivity) (by linarith)
  refine ⟨Real.sqrt (c.ρA ^ 2 + w'), ?_, ?_, fun y hy => ?_⟩
  · rw [Real.le_sqrt c.ρA_pos.le (by positivity)]; linarith
  · rw [Real.sqrt_lt' c.ρB_pos]
    have : w' ≤ (c.ρB ^ 2 - c.ρA ^ 2) / 2 := min_le_right _ _
    linarith
  · have hy2 : morseNorm n y ^ 2 ≤ c.ρA ^ 2 + w' := by
      have := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hmono := cut_antitone hAB hy2
    have hmem : c.ρA ^ 2 + w' ∈ Metric.ball (c.ρA ^ 2) w := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hw'0]
      have : w' ≤ w / 2 := min_le_left _ _
      linarith
    have := hball hmem
    exact le_trans this.le hmono

def ρs : ℝ := c.exists_ρs.choose

theorem ρA_le_ρs : c.ρA ≤ c.ρs := c.exists_ρs.choose_spec.1
theorem ρs_lt_ρB : c.ρs < c.ρB := c.exists_ρs.choose_spec.2.1
theorem ψp_ge_of_le_ρs {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρs) :
    9 / 10 ≤ ψp c.ρA c.ρB y := c.exists_ρs.choose_spec.2.2 y hy
theorem ρs_pos : 0 < c.ρs := c.ρA_pos.trans_le c.ρA_le_ρs
theorem r₀p_lt_ρs : c.e.r₀ < c.ρs := c.r₀p_lt_ρA.trans_le c.ρA_le_ρs

theorem theta_mul_lt_third {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y) :
    ModelField.theta c.e.r₀ y * morseNorm n y < c.m' / 3 := by
  have hr := c.e.hr₀
  have hρ : c.e.r₀ < morseNorm n y := c.r₀p_lt_ρs.trans_le hy
  rw [ModelField.theta_eq c.e.hr₀ (by linarith)]
  have hpos : 0 < morseNorm n y := by linarith
  have h1 : (morseNorm n y ^ 2)⁻¹ * morseNorm n y = 1 / morseNorm n y := by field_simp
  rw [h1]
  have h2 : 1 / morseNorm n y < 1 / c.e.r₀ := one_div_lt_one_div_of_lt hr hρ
  have h3 := c.three_div_r₀p_lt_m'
  have : 1 / c.e.r₀ = 3 / c.e.r₀ / 3 := by ring
  linarith

theorem ψp_add_ψm {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρB) :
    ψp c.ρA c.ρB y + c.ψm (c.e.χ y) = 1 := by
  have hyR : morseNorm n y ≤ c.e.R := hy.trans c.ρB_le_R
  have hf := c.f_chart_p hyR
  have hle : f p + morseNorm n y ^ 2 / 2 ≤ c.hi₁ := by
    have h1 := c.ρB_sq_eq
    have h2 : morseNorm n y ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
    have := c.lo₂_lt_hi₁
    linarith
  have := ψp_add_plateau (n := n) c.lo₁_lt_lo₂ c.hi₁_lt_hi₂ c.ρA_sq_eq c.ρB_sq_eq hle
  unfold IndexZeroCancellingPair.ψm
  rw [hf]; exact this

theorem ρB_sq_lt_three_ε : c.ρB ^ 2 < 3 * c.ε := by linarith [c.ρB_sq_lt, c.hε]

theorem sq_lt_three_ε_of_le_ρB {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.ρB) :
    morseNorm n y ^ 2 < 3 * c.ε :=
  (pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2).trans_lt c.ρB_sq_lt_three_ε

def pClosedBall : Set M := c.e.χ '' {y | morseNorm n y ≤ c.ρB}

theorem isCompact_pClosedBall : IsCompact c.pClosedBall := c.e.isCompact_image_le c.ρB_lt_R'

theorem pClosedBall_subset_pBall' : c.pClosedBall ⊆ c.pBall' := image_mono fun _ hy =>
  c.sq_lt_three_ε_of_le_ρB hy

theorem pClosedBall_subset_image_ball : c.pClosedBall ⊆ c.e.χ '' Metric.ball 0 c.e.R' :=
  c.pClosedBall_subset_pBall'.trans c.pBall'_subset_image_ball

theorem symm_mem_of_mem_pClosedBall {x : M} (hx : x ∈ c.pClosedBall) : morseNorm n (c.e.χ.symm x) ≤ c.ρB := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy)]; exact hy

theorem mem_pClosedBall_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ c.pClosedBall ↔ morseNorm n (c.e.χ.symm x) ≤ c.ρB :=
  ⟨c.symm_mem_of_mem_pClosedBall, fun h => c.e.mem_image_of_symm_mem hx h⟩

theorem continuousOn_symm_pClosedBall : ContinuousOn c.e.χ.symm c.pClosedBall :=
  c.e.hχsymm.continuousOn.mono c.pClosedBall_subset_image_ball

theorem isOpen_ball_ρB : IsOpen (c.e.χ '' {y | morseNorm n y < c.ρB}) :=
  c.e.isOpen_image_of_lt c.ρB_lt_R'.le

theorem ball_ρB_subset_pClosedBall : c.e.χ '' {y | morseNorm n y < c.ρB} ⊆ c.pClosedBall :=
  image_mono fun _ (hy : morseNorm n _ < c.ρB) => le_of_lt hy

theorem continuousOn_axialDefect_annulus :
    ContinuousOn (axialDefect c.e₁) {y : Fin n → ℝ | c.ρs ≤ morseNorm n y} := fun y hy =>
  (contDiffAt_axialDefect c.e₁ (by
    rintro rfl; have : c.ρs ≤ morseNorm n (0 : Fin n → ℝ) := hy
    rw [morseNorm_zero] at this; linarith [c.ρs_pos])).continuousAt.continuousWithinAt

namespace CancelConsts

variable {c} (k : c.CancelConsts)

def b₀ : ℝ := k.τ ^ 2 / 4

theorem b₀_pos : 0 < k.b₀ := by unfold b₀; have := k.hτ; positivity

theorem b₀_le : k.b₀ ≤ 1 / 16 := by unfold b₀; have := k.hτ1; linarith

theorem of_axialDefect_le {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y) (hB : axialDefect c.e₁ y ≤ k.b₀) :
    0 < axial c.e₁ y ∧ (1 - k.b₀) ^ 2 * morseNorm n y ^ 2 ≤ axial c.e₁ y ^ 2 ∧
      perpSq c.e₁ y ≤ morseNorm n y ^ 2 * (2 * k.b₀) := by
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [morseNorm_zero] at hy; linarith [c.ρs_pos]
  have hρ := morseNorm_pos hy0
  have hb := k.b₀_le
  have hBm : axialDefect c.e₁ y = 1 - axial c.e₁ y / morseNorm n y := rfl
  have h1b : 0 < 1 - k.b₀ := by linarith
  have ha' : (1 - k.b₀) * morseNorm n y ≤ axial c.e₁ y := by
    have : 1 - axial c.e₁ y / morseNorm n y ≤ k.b₀ := hBm ▸ hB
    have h2 : 1 - k.b₀ ≤ axial c.e₁ y / morseNorm n y := by linarith
    exact (le_div_iff₀ hρ).1 h2
  have hapos : 0 < axial c.e₁ y := lt_of_lt_of_le (mul_pos h1b hρ) ha'
  have hsq : ((1 - k.b₀) * morseNorm n y) ^ 2 ≤ axial c.e₁ y ^ 2 :=
    pow_le_pow_left₀ (mul_pos h1b hρ).le ha' 2
  rw [mul_pow] at hsq
  refine ⟨hapos, hsq, ?_⟩
  have hperp : perpSq c.e₁ y = morseNorm n y ^ 2 - axial c.e₁ y ^ 2 := rfl
  have e : (1 - k.b₀) ^ 2 * morseNorm n y ^ 2 =
      morseNorm n y ^ 2 - 2 * k.b₀ * morseNorm n y ^ 2 + k.b₀ ^ 2 * morseNorm n y ^ 2 := by ring
  have := mul_nonneg (sq_nonneg k.b₀) (sq_nonneg (morseNorm n y))
  rw [hperp]; nlinarith

theorem βp_eq_one_of_axialDefect_le {y : Fin n → ℝ} (hy : c.ρs ≤ morseNorm n y)
    (hB : axialDefect c.e₁ y ≤ k.b₀) : βp k.δ k.τ c.e₁ y = 1 := by
  obtain ⟨hapos, hsq, hperp⟩ := k.of_axialDefect_le hy hB
  have hb := k.b₀_le
  have hδ := k.hδ
  refine βp_eq_one k.hδ ?_ (by linarith)
  have hb₀ : 2 * k.b₀ = k.τ ^ 2 / 2 := by unfold b₀; ring
  have h3 : 1 / 2 ≤ (1 - k.b₀) ^ 2 := by nlinarith
  have hτ2 := sq_nonneg k.τ
  have hρ2 := sq_nonneg (morseNorm n y)
  have h4 : morseNorm n y ^ 2 * (2 * k.b₀) ≤ k.τ ^ 2 * axial c.e₁ y ^ 2 := by
    rw [hb₀]
    have : k.τ ^ 2 * (1 / 2 * morseNorm n y ^ 2) ≤ k.τ ^ 2 * ((1 - k.b₀) ^ 2 * morseNorm n y ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ2
    have h5 : k.τ ^ 2 * ((1 - k.b₀) ^ 2 * morseNorm n y ^ 2) ≤ k.τ ^ 2 * axial c.e₁ y ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hτ2
    linarith
  have := sq_nonneg k.δ
  linarith

theorem mem_tube_of_axialDefect_le {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y) (hy2 : morseNorm n y ≤ c.ρB)
    (hB : axialDefect c.e₁ y ≤ k.b₀) : c.e.χ y ∈ c.orientedChartTube ∧ ‖c.ζ (c.e.χ y)‖ < k.δ' := by
  obtain ⟨hapos, -, hperp⟩ := k.of_axialDefect_le hy1 hB
  refine k.hcone y (c.ρA_le_ρs.trans hy1) hy2 ?_ hapos
  have hb₀ : 2 * k.b₀ = k.τ ^ 2 / 2 := by unfold b₀; ring
  have hτ := k.hτ
  have hρ : 0 < morseNorm n y := c.ρs_pos.trans_le hy1
  have hpos : 0 < 2 * k.δ ^ 2 / c.ρA ^ 2 := by have := k.hδ; have := c.ρA_pos; positivity
  have : morseNorm n y ^ 2 * (2 * k.b₀) < (k.τ ^ 2 + 2 * k.δ ^ 2 / c.ρA ^ 2) * morseNorm n y ^ 2 := by
    rw [hb₀]; nlinarith [sq_nonneg k.τ, mul_pos hpos (pow_pos hρ 2), mul_pos (pow_pos hτ 2) (pow_pos hρ 2)]
  linarith

def pInnerAngularRegion : Set M :=
  c.e.χ '' {y | morseNorm n y ≤ c.ρs ∨
    (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ axialDefect c.e₁ y)}

def pAxialAnnulus : Set M :=
  c.e.χ '' {y | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ axialDefect c.e₁ y ≤ k.b₀}

theorem isClosed_annulus_axialDefect_ge :
    IsClosed {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ axialDefect c.e₁ y} := by
  have h : {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ axialDefect c.e₁ y} =
      {y | c.ρs ≤ morseNorm n y} ∩ (axialDefect c.e₁) ⁻¹' Ici k.b₀ ∩ {y | morseNorm n y ≤ c.ρB} := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]; tauto
  rw [h]
  exact (c.continuousOn_axialDefect_annulus.preimage_isClosed_of_isClosed
    (isClosed_le continuous_const continuous_morseNorm) isClosed_Ici).inter
    (isClosed_le continuous_morseNorm continuous_const)

theorem isClosed_annulus_axialDefect_le :
    IsClosed {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ axialDefect c.e₁ y ≤ k.b₀} := by
  have h : {y : Fin n → ℝ | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ axialDefect c.e₁ y ≤ k.b₀} =
      {y | c.ρs ≤ morseNorm n y} ∩ (axialDefect c.e₁) ⁻¹' Iic k.b₀ ∩ {y | morseNorm n y ≤ c.ρB} := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic]; tauto
  rw [h]
  exact (c.continuousOn_axialDefect_annulus.preimage_isClosed_of_isClosed
    (isClosed_le continuous_const continuous_morseNorm) isClosed_Iic).inter
    (isClosed_le continuous_morseNorm continuous_const)

theorem isCompact_pInnerAngularRegion : IsCompact k.pInnerAngularRegion :=
  c.e.isCompact_image_of_subset
    (((isCompact_morseNorm_le c.ρB).of_isClosed_subset
      ((isClosed_le continuous_morseNorm continuous_const).union k.isClosed_annulus_axialDefect_ge)
      (fun _ hy => by
        rcases hy with h | h
        · exact h.trans c.ρs_lt_ρB.le
        · exact h.2.1))) c.ρB_lt_R' fun _ hy => by
    rcases hy with h | h
    · exact h.trans c.ρs_lt_ρB.le
    · exact h.2.1

theorem isCompact_pAxialAnnulus : IsCompact k.pAxialAnnulus :=
  c.e.isCompact_image_of_subset
    ((isCompact_morseNorm_le c.ρB).of_isClosed_subset k.isClosed_annulus_axialDefect_le fun _ hy => hy.2.1)
    c.ρB_lt_R' fun _ hy => hy.2.1

theorem pInnerAngularRegion_subset_pClosedBall : k.pInnerAngularRegion ⊆ c.pClosedBall := image_mono fun _ hy => by
  rcases hy with h | h
  · exact h.trans c.ρs_lt_ρB.le
  · exact h.2.1

theorem pAxialAnnulus_subset_pClosedBall : k.pAxialAnnulus ⊆ c.pClosedBall := image_mono fun _ hy => hy.2.1

theorem mem_pInnerAngularRegion_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ k.pInnerAngularRegion ↔ (morseNorm n (c.e.χ.symm x) ≤ c.ρs ∨
      (c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB ∧
        k.b₀ ≤ axialDefect c.e₁ (c.e.χ.symm x))) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyB : morseNorm n y ≤ c.ρB := by
      rcases hy with h | h
      · exact h.trans c.ρs_lt_ρB.le
      · exact h.2.1
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hyB)]; exact hy
  · intro h; exact c.e.mem_image_of_symm_mem hx h

theorem mem_pAxialAnnulus_iff {x : M} (hx : x ∈ c.e.χ '' Metric.ball 0 c.e.R') :
    x ∈ k.pAxialAnnulus ↔ (c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB ∧
        axialDefect c.e₁ (c.e.χ.symm x) ≤ k.b₀) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy.2.1)]; exact hy
  · intro h; exact c.e.mem_image_of_symm_mem hx h

theorem pClosedBall_eq_union : c.pClosedBall = k.pInnerAngularRegion ∪ k.pAxialAnnulus := by
  ext x
  constructor
  · intro hx
    have hx' := c.pClosedBall_subset_image_ball hx
    have hρ := c.symm_mem_of_mem_pClosedBall hx
    rw [mem_union, k.mem_pInnerAngularRegion_iff hx', k.mem_pAxialAnnulus_iff hx']
    rcases le_or_gt (morseNorm n (c.e.χ.symm x)) c.ρs with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt k.b₀ (axialDefect c.e₁ (c.e.χ.symm x)) with hb | hb
      · exact Or.inl (Or.inr ⟨h.le, hρ, hb⟩)
      · exact Or.inr ⟨h.le, hρ, hb.le⟩
  · rintro (hx | hx)
    · exact k.pInnerAngularRegion_subset_pClosedBall hx
    · exact k.pAxialAnnulus_subset_pClosedBall hx

end CancelConsts

def pRadialDefect (y : Fin n → ℝ) : ℝ := morseNorm n y ^ 2 - axial c.e₁ y * morseNorm n y

theorem pRadialDefect_eq (y : Fin n → ℝ) : c.pRadialDefect y = morseNorm n y * (morseNorm n y - axial c.e₁ y) := by
  unfold pRadialDefect; ring

theorem pRadialDefect_nonneg (y : Fin n → ℝ) : 0 ≤ c.pRadialDefect y := by
  rw [c.pRadialDefect_eq]
  apply mul_nonneg (ModelField.morseNorm_nonneg y)
  have := abs_dot_le y c.e₁
  rw [c.morseNorm_e₁, mul_one] at this
  have := (abs_le.1 this).2
  unfold axial; linarith

theorem continuous_pRadialDefect : Continuous c.pRadialDefect :=
  (continuous_morseNorm.pow 2).sub ((continuous_axial c.e₁).mul continuous_morseNorm)

theorem pRadialDefect_eq_zero_iff (y : Fin n → ℝ) : c.pRadialDefect y = 0 ↔ y = axial c.e₁ y • c.e₁ ∧ 0 ≤ axial c.e₁ y := by
  rw [c.pRadialDefect_eq]
  by_cases hy0 : y = 0
  · subst hy0; simp [axial_zero, morseNorm_zero]
  have hρ := morseNorm_pos hy0
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 hρ.ne'
    · have ha : axial c.e₁ y = morseNorm n y := by linarith
      have hB : axialDefect c.e₁ y = 0 := by
        unfold axialDefect; rw [ha, div_self hρ.ne', sub_self]
      have := (axialDefect_eq_zero_iff c.morseNorm_e₁ hy0).1 hB
      refine ⟨?_, ha ▸ ModelField.morseNorm_nonneg y⟩
      rw [ha]; exact this
  · rintro ⟨hy, ha⟩
    have : morseNorm n y = axial c.e₁ y := by
      conv_lhs => rw [hy]
      rw [morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha]
    rw [this, sub_self, mul_zero]

def pRadialDefectRate (y v : Fin n → ℝ) : ℝ :=
  2 * dot y v - axial c.e₁ v * morseNorm n y - axial c.e₁ y * dot y v / morseNorm n y

theorem hasDerivAt_axial_mul_morseNorm_of_eq_zero {y : ℝ → Fin n → ℝ} {y' : Fin n → ℝ} {s₀ : ℝ}
    (hy : HasDerivAt y y' s₀) (h0 : y s₀ = 0) :
    HasDerivAt (fun s => axial c.e₁ (y s) * morseNorm n (y s)) 0 s₀ := by
  have hq : HasDerivAt (fun s => morseNorm n (y s) ^ 2) 0 s₀ := by
    have := (hasFDerivAt_morseNorm_sq (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    simp [dotL_apply, h0, dot_zero_left]
  have hq' := hasDerivAt_iff_tendsto.1 hq
  rw [hasDerivAt_iff_tendsto]
  have hbound : ∀ᶠ s in 𝓝 s₀, ‖s - s₀‖⁻¹ * ‖axial c.e₁ (y s) * morseNorm n (y s) -
      axial c.e₁ (y s₀) * morseNorm n (y s₀) - (s - s₀) • (0 : ℝ)‖ ≤
        ‖s - s₀‖⁻¹ * ‖morseNorm n (y s) ^ 2 - morseNorm n (y s₀) ^ 2 - (s - s₀) • (0 : ℝ)‖ := by
    refine Eventually.of_forall fun s => ?_
    rw [h0, axial_zero, morseNorm_zero]
    simp only [mul_zero, sub_zero, smul_zero, zero_pow two_ne_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (ModelField.morseNorm_nonneg (y s)), abs_of_nonneg (sq_nonneg (morseNorm n (y s)))]
    have h1 := abs_dot_le (y s) c.e₁
    rw [c.morseNorm_e₁, mul_one] at h1
    rw [sq]; exact mul_le_mul_of_nonneg_right h1 (ModelField.morseNorm_nonneg _)
  exact squeeze_zero' (Eventually.of_forall fun s => by positivity) hbound hq'

theorem hasDerivAt_pRadialDefect_curve {y : ℝ → Fin n → ℝ} {y' : Fin n → ℝ} {s₀ : ℝ}
    (hy : HasDerivAt y y' s₀) :
    HasDerivAt (fun s => c.pRadialDefect (y s)) (c.pRadialDefectRate (y s₀) y') s₀ := by
  have h1 : HasDerivAt (fun s => morseNorm n (y s) ^ 2) (2 * dot (y s₀) y') s₀ := by
    have := (hasFDerivAt_morseNorm_sq (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    simp [dotL_apply]
  have h2 : HasDerivAt (fun s => axial c.e₁ (y s)) (axial c.e₁ y') s₀ := by
    have := (hasFDerivAt_axial c.e₁ (y s₀)).comp_hasDerivAt s₀ hy
    refine this.congr_deriv ?_
    rw [dotL_apply, axial, dot_comm]
  by_cases h0 : y s₀ = 0
  · have h3 := c.hasDerivAt_axial_mul_morseNorm_of_eq_zero hy h0
    have := h1.sub h3
    refine this.congr_deriv ?_
    unfold pRadialDefectRate
    rw [h0, dot_zero_left, morseNorm_zero, axial_zero]; ring
  · have h3 : HasDerivAt (fun s => morseNorm n (y s)) (dot (y s₀) y' / morseNorm n (y s₀)) s₀ := by
      have := (hasFDerivAt_morseNorm h0).comp_hasDerivAt s₀ hy
      refine this.congr_deriv ?_
      simp [dotL_apply, div_eq_inv_mul]
    have := h1.sub (h2.mul h3)
    refine this.congr_deriv ?_
    unfold pRadialDefectRate
    have hρ := morseNorm_pos h0
    field_simp
    ring

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem pRadialDefectRate_pCancellationField {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 < 3 * c.ε) (hy0 : y ≠ 0) :
    c.pRadialDefectRate y (k.pCancellationField y) =
      -(2 * ((1 - 2 * k.pReversalWeight y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
          (morseNorm n y - axial c.e₁ y) +
        c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * (morseNorm n y - axial c.e₁ y) ^ 2 /
          morseNorm n y +
        2 * (c.lam * k.pTransverseWeight y) * axial c.e₁ (c.pRestrictedTransverseField y) * morseNorm n y) := by
  unfold pRadialDefectRate
  rw [k.dot_pCancellationField hy, k.axial_pCancellationField]
  have hρ := morseNorm_pos hy0
  field_simp
  ring

theorem pReversalWeight_le_of_mem_pInnerAngularRegion
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ c.ρs ∨ (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ axialDefect c.e₁ y)) :
    k.pReversalWeight y ≤ 1 / 10 := by
  classical
  rcases hy with h | ⟨h1, h2, h3⟩
  · by_cases hT : c.e.χ y ∈ c.orientedChartTube
    · rw [k.pReversalWeight_of_mem hT]
      have hψ := c.ψp_add_ψm (h.trans c.ρs_lt_ρB.le)
      have hψp := c.ψp_ge_of_le_ρs h
      have hβ := k.βm_le_one (c.e.χ y)
      have hβ0 := k.βm_nonneg (c.e.χ y)
      have hm0 := c.ψm_nonneg (c.e.χ y)
      nlinarith
    · rw [k.pReversalWeight_of_notMem hT]; norm_num
  · have := k.pReversalWeight_eq_zero_of_norm_ζ fun hT => hζmin y (c.ρA_le_ρs.trans h1) h2 h3 hT
    rw [this]; norm_num

theorem pRadialDefectRate_pCancellationField_nonpos
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ c.ρs ∨ (c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB ∧ k.b₀ ≤ axialDefect c.e₁ y)) :
    c.pRadialDefectRate y (k.pCancellationField y) ≤ 0 ∧ (c.pRadialDefectRate y (k.pCancellationField y) = 0 → c.pRadialDefect y = 0) := by
  have hyB : morseNorm n y ≤ c.ρB := by
    rcases hy with h | h
    · exact h.trans c.ρs_lt_ρB.le
    · exact h.2.1
  have hy3 := c.sq_lt_three_ε_of_le_ρB hyB
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨?_, fun _ => ?_⟩
    · unfold pRadialDefectRate; rw [dot_zero_left, morseNorm_zero, axial_zero]; simp
    · unfold pRadialDefect; rw [morseNorm_zero, axial_zero]; ring
  rw [k.pRadialDefectRate_pCancellationField hy3 hy0]
  have hC := k.pReversalWeight_le_of_mem_pInnerAngularRegion hζmin hy
  have hθ := ModelField.theta_pos c.e.hr₀ y
  have hρ := morseNorm_pos hy0
  have hB : 0 ≤ morseNorm n y - axial c.e₁ y := by
    have := abs_dot_le y c.e₁
    rw [c.morseNorm_e₁, mul_one] at this
    have := (abs_le.1 this).2
    unfold axial; linarith
  have hA : 0 ≤ c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) :=
    mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
  have hZ : 0 ≤ 2 * (c.lam * k.pTransverseWeight y) * axial c.e₁ (c.pRestrictedTransverseField y) := by
    by_cases hBp : k.pTransverseWeight y = 0
    · rw [hBp]; simp
    · obtain ⟨hT, hζ⟩ := k.mem_of_pTransverseWeight_ne_zero hBp
      by_cases hζ0 : c.ζ (c.e.χ y) = 0
      · rw [c.pRestrictedTransverseField_eq_zero_of_ζ hT hζ0, axial_zero, mul_zero]
      · have := k.axial_pRestrictedTransverseField_pos hy3 hT (norm_pos_iff.2 hζ0) hζ
        have := c.lam_pos
        have := k.pTransverseWeight_nonneg y
        positivity
  have h1 : 0 ≤ 2 * ((1 - 2 * k.pReversalWeight y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
      (morseNorm n y - axial c.e₁ y) := by
    have : 0 < 1 - 2 * k.pReversalWeight y := by linarith
    positivity
  have h2 : 0 ≤ c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * (morseNorm n y - axial c.e₁ y) ^ 2 /
      morseNorm n y := by positivity
  have h3 : 0 ≤ 2 * (c.lam * k.pTransverseWeight y) * axial c.e₁ (c.pRestrictedTransverseField y) * morseNorm n y := by positivity
  refine ⟨by linarith, fun h0 => ?_⟩
  have h1' : 2 * ((1 - 2 * k.pReversalWeight y) * ModelField.theta c.e.r₀ y) * morseNorm n y *
      (morseNorm n y - axial c.e₁ y) = 0 := by linarith
  have hpos : 0 < 2 * ((1 - 2 * k.pReversalWeight y) * ModelField.theta c.e.r₀ y) * morseNorm n y := by
    have : 0 < 1 - 2 * k.pReversalWeight y := by linarith
    positivity
  have : morseNorm n y - axial c.e₁ y = 0 := by
    rcases mul_eq_zero.1 h1' with h | h
    · exact absurd h hpos.ne'
    · exact h
  rw [c.pRadialDefect_eq, this, mul_zero]

theorem axial_pCancellationField_pos_axis {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ c.ρB) :
    0 < axial c.e₁ (k.pCancellationField (a • c.e₁)) := by
  classical
  set y := a • c.e₁ with hy
  have hnorm : morseNorm n y = a := by
    rw [hy, morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha0]
  have hyB : morseNorm n y ≤ c.ρB := by rw [hnorm]; exact ha
  have hy3 := c.sq_lt_three_ε_of_le_ρB hyB
  have hβ : βp k.δ k.τ c.e₁ y = 1 := βp_smul_self c.morseNorm_e₁ k.hδ (by linarith [k.hδ])
  have haxial : axial c.e₁ y = a := axial_smul_self c.morseNorm_e₁ a
  have hZ : 2 * (c.lam * k.pTransverseWeight y) * axial c.e₁ (c.pRestrictedTransverseField y) = 0 := by
    by_cases hT : c.e.χ y ∈ c.orientedChartTube
    · have hζ : c.ζ (c.e.χ y) = 0 := by
        by_cases hr : c.e.r₀ < a
        · exact (c.axis_p_mem_orientedChartTube hr (by rw [← hnorm]; exact hy3) hT.1.1).2
        · exfalso
          have hfy := c.f_chart_p (hyB.trans c.ρB_le_R)
          have h1 := hT.1.1.1
          rw [hfy, hnorm] at h1
          have := c.f_p_add_lt_c₁_sub_η
          push Not at hr
          nlinarith [c.e.hr₀]
      rw [c.pRestrictedTransverseField_eq_zero_of_ζ hT hζ, axial_zero, mul_zero]
    · rw [c.pRestrictedTransverseField_of_notMem hT, axial_zero, mul_zero]
  rw [k.axial_pCancellationField, hZ, add_zero, hβ, one_mul, haxial]
  have hψ := c.ψp_add_ψm hyB
  have hCp : k.pReversalWeight y = c.ψm (c.e.χ y) := by
    by_cases hT : c.e.χ y ∈ c.orientedChartTube
    · rw [k.pReversalWeight_of_mem hT]
      have hζ : c.ζ (c.e.χ y) = 0 := by
        by_cases hr : c.e.r₀ < a
        · exact (c.axis_p_mem_orientedChartTube hr (by rw [← hnorm]; exact hy3) hT.1.1).2
        · exfalso
          have hfy := c.f_chart_p (hyB.trans c.ρB_le_R)
          have h1 := hT.1.1.1
          rw [hfy, hnorm] at h1
          have := c.f_p_add_lt_c₁_sub_η
          push Not at hr
          nlinarith [c.e.hr₀]
      rw [k.βm_eq_one_of_ζ_eq_zero hζ, one_mul]
    · rw [k.pReversalWeight_of_notMem hT]
      have : c.ψm (c.e.χ y) = 0 := by
        apply c.ψm_eq_zero_of_le
        rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm]
        by_contra hlt
        push Not at hlt
        have hr : c.e.r₀ < a := by
          have := c.f_p_add_lt_c₁_sub_η
          unfold lo₁ at hlt
          have hη := c.η_pos
          by_contra hle; push Not at hle
          nlinarith [c.e.hr₀]
        have hlev : f (c.e.χ (a • c.e₁)) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
          rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm]
          have := c.η_pos
          have := c.ρB_sq_eq
          have h2 : a ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ ha0 ha 2
          have := c.lo₂_lt_hi₁
          unfold lo₁ lo₂ hi₁ at *
          constructor <;> linarith
        exact hT (c.axis_p_mem_orientedChartTube hr (by rw [← hnorm]; exact hy3) hlev).1
      rw [this]
  rw [hCp]
  have hψp : ψp c.ρA c.ρB y = 1 - c.ψm (c.e.χ y) := by linarith
  rw [hψp]
  rcases ha0.eq_or_lt with h | h
  · rw [← h]
    have := c.m'_pos
    have h0 : c.ψm (c.e.χ y) = 0 := by
      apply c.ψm_eq_zero_of_le
      rw [c.f_chart_p (hyB.trans c.ρB_le_R), hnorm, ← h]
      have := c.f_p_add_lt_c₁_sub_η; have := c.η_pos
      unfold lo₁; nlinarith [sq_nonneg c.e.r₀]
    rw [h0]; norm_num; exact this
  · have hθa : 0 < ModelField.theta c.e.r₀ y * a := mul_pos (ModelField.theta_pos c.e.hr₀ y) h
    have hθm : ModelField.theta c.e.r₀ y * a < c.m' := by rw [← hnorm]; exact c.hm_p y
    have := axis_ineq_p hθa hθm (c.ψm_nonneg (c.e.χ y)) (c.ψm_le_one (c.e.χ y))
    linarith

theorem hasDerivAt_pRadialDefect_cancellationFlow {x : M} {s : ℝ} (hs : k.cancellationFlow s x ∈ c.pBall') :
    HasDerivAt (fun s => c.pRadialDefect (c.e.χ.symm (k.cancellationFlow s x)))
      (c.pRadialDefectRate (c.e.χ.symm (k.cancellationFlow s x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x)))) s :=
  c.hasDerivAt_pRadialDefect_curve (k.hasDerivAt_symm_cancellationFlow_p hs)

theorem pInnerAngularRegion_subset_pBall' : k.pInnerAngularRegion ⊆ c.pBall' := k.pInnerAngularRegion_subset_pClosedBall.trans c.pClosedBall_subset_pBall'
theorem pAxialAnnulus_subset_pBall' : k.pAxialAnnulus ⊆ c.pBall' := k.pAxialAnnulus_subset_pClosedBall.trans c.pClosedBall_subset_pBall'

theorem exists_exit_pInnerAngularRegion
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖) :
    ∀ x ∈ k.pInnerAngularRegion, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ k.pInnerAngularRegion := by
  refine k.exists_exit_of_lyapunov_pair k.isCompact_pInnerAngularRegion (L₁ := fun x => c.pRadialDefect (c.e.χ.symm x))
    (L₂ := fun x => axial c.e₁ (c.e.χ.symm x))
    (c.continuous_pRadialDefect.comp_continuousOn (c.continuousOn_symm_pClosedBall.mono k.pInnerAngularRegion_subset_pClosedBall))
    ((continuous_axial c.e₁).comp_continuousOn
      (c.continuousOn_symm_pClosedBall.mono k.pInnerAngularRegion_subset_pClosedBall))
    (Z := {x | c.pRadialDefect (c.e.χ.symm x) = 0}) ?_ ?_
  · intro x hx
    have hx' := k.pInnerAngularRegion_subset_pClosedBall hx
    have hy := (k.mem_pInnerAngularRegion_iff (c.pClosedBall_subset_image_ball hx')).1 hx
    obtain ⟨h1, h2⟩ := k.pRadialDefectRate_pCancellationField_nonpos hζmin hy
    have hd := k.hasDerivAt_pRadialDefect_cancellationFlow (x := x) (s := 0) (by rw [k.cancellationFlow_zero]; exact c.pClosedBall_subset_pBall' hx')
    rw [k.cancellationFlow_zero] at hd
    exact ⟨_, h1, hd, fun h => h2 h⟩
  · rintro x ⟨hx, hZ⟩
    have hx' := k.pInnerAngularRegion_subset_pClosedBall hx
    have hZ' : c.pRadialDefect (c.e.χ.symm x) = 0 := hZ
    obtain ⟨hax, ha0⟩ := (c.pRadialDefect_eq_zero_iff _).1 hZ'
    have hρ := c.symm_mem_of_mem_pClosedBall hx'
    have hd := k.hasDerivAt_axial_cancellationFlow_p (x := x) (s := 0)
      (by rw [k.cancellationFlow_zero]; exact c.pClosedBall_subset_pBall' hx')
    rw [k.cancellationFlow_zero] at hd
    refine ⟨_, ?_, hd⟩
    have hnorm : morseNorm n (c.e.χ.symm x) = axial c.e₁ (c.e.χ.symm x) := by
      conv_lhs => rw [hax]
      rw [morseNorm_smul_self c.morseNorm_e₁, abs_of_nonneg ha0]
    have := k.axial_pCancellationField_pos_axis ha0 (by rw [← hnorm]; exact hρ)
    rw [← hax] at this
    exact this

theorem dot_pCancellationField_neg_of_sphere
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {y : Fin n → ℝ} (hy : morseNorm n y = c.ρB) (hB : k.b₀ ≤ axialDefect c.e₁ y) :
    dot y (k.pCancellationField y) < 0 := by
  have hy3 : morseNorm n y ^ 2 < 3 * c.ε := by rw [hy]; exact c.ρB_sq_lt_three_ε
  rw [k.dot_pCancellationField hy3]
  have hC : k.pReversalWeight y = 0 := k.pReversalWeight_eq_zero_of_norm_ζ fun hT =>
    hζmin y (by rw [hy]; exact c.ρA_lt_ρB.le) hy.le hB hT
  have hψ : ψp c.ρA c.ρB y = 0 := ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hy.ge
  rw [hC, hψ]
  have hθ := ModelField.theta_pos c.e.hr₀ y
  have : 0 < morseNorm n y := by rw [hy]; exact c.ρB_pos
  simp only [mul_zero, zero_mul, add_zero, sub_zero, one_mul]
  have : 0 < ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by positivity
  linarith

theorem exists_reach_pAxialAnnulus
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {x : M} (hx : x ∈ k.pInnerAngularRegion) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.pAxialAnnulus ∧ ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.pClosedBall := by
  obtain ⟨t₀, ht₀, hexit⟩ := k.exists_exit_pInnerAngularRegion hζmin x hx
  have hinv : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∉ k.pAxialAnnulus) →
      ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.pClosedBall := by
    intro t _ hno
    have hQ : IsClosed {s : ℝ | k.cancellationFlow s x ∈ c.pClosedBall} :=
      c.isCompact_pClosedBall.isClosed.preimage (k.continuous_cancellationFlow_curve x)
    refine Icc_subset_of_isClosed_of_step hQ (by simp [k.pInnerAngularRegion_subset_pClosedBall hx]) fun s hs hIcc => ?_
    have hsW : k.cancellationFlow s x ∈ c.pClosedBall := hIcc (right_mem_Icc.2 hs.1)
    have hs1 : k.cancellationFlow s x ∈ k.pInnerAngularRegion := by
      have := (k.pClosedBall_eq_union ▸ hsW : k.cancellationFlow s x ∈ k.pInnerAngularRegion ∪ k.pAxialAnnulus)
      exact this.resolve_right (hno s ⟨hs.1, hs.2.le⟩)
    have hρ := c.symm_mem_of_mem_pClosedBall hsW
    rcases hρ.lt_or_eq with hlt | heq
    · have hmem : k.cancellationFlow s x ∈ c.e.χ '' {y | morseNorm n y < c.ρB} :=
        c.e.mem_image_of_symm_mem (c.pClosedBall_subset_image_ball hsW) hlt
      obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_ball_ρB hmem
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
      exact c.ball_ρB_subset_pClosedBall (hεO s' ⟨by linarith [hs'.1], hs'.2⟩)
    · have hB : k.b₀ ≤ axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow s x)) := by
        rcases (k.mem_pInnerAngularRegion_iff (c.pClosedBall_subset_image_ball hsW)).1 hs1 with h | h
        · exfalso; rw [heq] at h; linarith [c.ρs_lt_ρB]
        · exact h.2.2
      have hd := k.hasDerivAt_morseNormSq_cancellationFlow_p (c.pClosedBall_subset_pBall' hsW)
      have hneg := k.dot_pCancellationField_neg_of_sphere hζmin heq hB
      have hev := eventually_lt_of_hasDerivAt_neg (by linarith : 2 * dot (c.e.χ.symm (k.cancellationFlow s x))
        (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x))) < 0) hd
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1
        (hev.and (k.exists_Icc_cancellationFlow_mem_open c.e.isOpen_image_ball (c.pClosedBall_subset_image_ball hsW)
          |> fun ⟨ε, hε, hεO⟩ => by
            refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
            exact hεO s' ⟨by linarith [hs'.1], hs'.2⟩))
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨u, hu, fun s' hs' => ?_⟩
      obtain ⟨h1, h2⟩ := hsub hs'
      rw [heq] at h1
      refine c.e.mem_image_of_symm_mem h2 ?_
      change morseNorm n (c.e.χ.symm (k.cancellationFlow s' x)) ≤ c.ρB
      have : morseNorm n (c.e.χ.symm (k.cancellationFlow s' x)) ^ 2 < c.ρB ^ 2 := h1
      exact ((pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg _) c.ρB_pos.le two_ne_zero).1
        this).le
  have hhit : ∃ s ∈ Icc 0 t₀, k.cancellationFlow s x ∈ k.pAxialAnnulus := by
    by_contra h
    push Not at h
    have hW := hinv t₀ ht₀ h t₀ (right_mem_Icc.2 ht₀)
    have := (k.pClosedBall_eq_union ▸ hW : k.cancellationFlow t₀ x ∈ k.pInnerAngularRegion ∪ k.pAxialAnnulus)
    exact hexit (this.resolve_right (h t₀ (right_mem_Icc.2 ht₀)))
  obtain ⟨s₀, hs₀, hs₀W, hmin⟩ := exists_first_time k.isCompact_pAxialAnnulus.isClosed
    (k.continuous_cancellationFlow_curve x) hhit
  refine ⟨s₀, hs₀.1, hs₀W, fun s hs => ?_⟩
  rcases hs.2.eq_or_lt with h | h
  · rw [h]; exact k.pAxialAnnulus_subset_pClosedBall hs₀W
  · exact hinv s hs.1 (fun u hu => hmin u ⟨hu.1, hu.2.trans_lt h⟩) s (right_mem_Icc.2 hs.1)

end CancelConsts

def pOpenAnnulus : Set M := c.e.χ '' {y | c.ρs / 2 < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε}

theorem isOpen_pOpenAnnulus : IsOpen c.pOpenAnnulus := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (c.mem_ball_p_of_sq_lt hy.2)
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt (continuous_morseNorm.pow 2) continuous_const)

theorem pOpenAnnulus_subset_pBall' : c.pOpenAnnulus ⊆ c.pBall' := image_mono fun _ hy => hy.2

theorem symm_ne_zero_of_mem_pOpenAnnulus {x : M} (hx : x ∈ c.pOpenAnnulus) : c.e.χ.symm x ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy.2]
  rintro rfl
  have := hy.1; rw [morseNorm_zero] at this; linarith [c.ρs_pos]

theorem symm_sq_lt_of_mem_pOpenAnnulus {x : M} (hx : x ∈ c.pOpenAnnulus) : morseNorm n (c.e.χ.symm x) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy.2]; exact hy.2

theorem isOpen_annulus_gt :
    IsOpen (c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε}) := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (c.mem_ball_p_of_sq_lt hy.2)
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt (continuous_morseNorm.pow 2) continuous_const)

namespace CancelConsts

variable {c} (k : c.CancelConsts)

theorem pAxialAnnulus_subset_pOpenAnnulus : k.pAxialAnnulus ⊆ c.pOpenAnnulus := image_mono fun y hy => by
  change c.ρs / 2 < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε
  have h1 : c.ρs ≤ morseNorm n y := hy.1
  exact ⟨by have := c.ρs_pos; linarith, c.sq_lt_three_ε_of_le_ρB hy.2.1⟩

theorem pTransverseWeight_pos_of_mem_pAxialAnnulus {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y)
    (hy2 : morseNorm n y ≤ c.ρB) (hB : axialDefect c.e₁ y ≤ k.b₀) : 0 < k.pTransverseWeight y := by
  obtain ⟨hT, hζ⟩ := k.mem_tube_of_axialDefect_le hy1 hy2 hB
  rw [k.pTransverseWeight_of_mem hT]
  have hβ : 0 < k.βm' (c.e.χ y) := by
    apply cut_pos_of_lt k.two_δ_sq_lt_δ'_sq
    exact pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero
  have hψ : c.ψm' (c.e.χ y) = 1 := by
    apply c.ψm'_eq_one
    · rw [c.f_chart_p (hy2.trans c.ρB_le_R)]
      have h1 := c.ρA_sq_eq
      have h2 : c.ρA ^ 2 ≤ morseNorm n y ^ 2 :=
        pow_le_pow_left₀ c.ρA_pos.le (c.ρA_le_ρs.trans hy1) 2
      linarith
    · rw [c.f_chart_p (hy2.trans c.ρB_le_R)]
      have h1 := c.ρB_sq_eq
      have h2 : morseNorm n y ^ 2 ≤ c.ρB ^ 2 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy2 2
      have := c.lo₂_lt_hi₁; have := c.hi₁_lt_hi₂
      linarith
  rw [hψ, mul_one]; exact hβ

theorem axis_of_axialDefectDeriv_pCancellationField_eq_zero {y : Fin n → ℝ} (hy1 : c.ρs ≤ morseNorm n y)
    (hy2 : morseNorm n y ≤ c.ρB) (hB : axialDefect c.e₁ y ≤ k.b₀)
    (h : axialDefectDeriv c.e₁ y (k.pCancellationField y) = 0) : y = morseNorm n y • c.e₁ := by
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [morseNorm_zero] at hy1; linarith [c.ρs_pos]
  obtain ⟨-, h2⟩ := k.of_axialDefectDeriv_pCancellationField_eq_zero (c.sq_lt_three_ε_of_le_ρB hy2) hy0 h
  rcases h2 with h2 | ⟨hT, hζ⟩
  · exact absurd h2 (k.pTransverseWeight_pos_of_mem_pAxialAnnulus hy1 hy2 hB).ne'
  · exact (c.axis_of_ζ_eq_zero_p (c.sq_lt_three_ε_of_le_ρB hy2) hT hζ).1

theorem exists_exit_pAxialAnnulus : ∀ x ∈ k.pAxialAnnulus, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ k.pAxialAnnulus := by
  refine k.exists_exit_of_lyapunov_pair k.isCompact_pAxialAnnulus (L₁ := fun x => axialDefect c.e₁ (c.e.χ.symm x))
    (L₂ := fun x => axial c.e₁ (c.e.χ.symm x))
    (c.continuousOn_axialDefect_annulus.comp (c.continuousOn_symm_pClosedBall.mono k.pAxialAnnulus_subset_pClosedBall)
      fun x hx => ((k.mem_pAxialAnnulus_iff (c.pClosedBall_subset_image_ball (k.pAxialAnnulus_subset_pClosedBall hx))).1 hx).1)
    ((continuous_axial c.e₁).comp_continuousOn
      (c.continuousOn_symm_pClosedBall.mono k.pAxialAnnulus_subset_pClosedBall))
    (Z := {x | c.e.χ.symm x = morseNorm n (c.e.χ.symm x) • c.e₁}) ?_ ?_
  · intro x hx
    have hx' := k.pAxialAnnulus_subset_pClosedBall hx
    obtain ⟨h1, h2, h3⟩ := (k.mem_pAxialAnnulus_iff (c.pClosedBall_subset_image_ball hx')).1 hx
    have hy0 : c.e.χ.symm x ≠ 0 := c.symm_ne_zero_of_mem_pOpenAnnulus (k.pAxialAnnulus_subset_pOpenAnnulus hx)
    have hd := k.hasDerivAt_axialDefect_cancellationFlow_p (x := x) (s := 0)
      (by rw [k.cancellationFlow_zero]; exact c.pClosedBall_subset_pBall' hx') (by rw [k.cancellationFlow_zero]; exact hy0)
    rw [k.cancellationFlow_zero] at hd
    exact ⟨_, k.axialDefectDeriv_pCancellationField_nonpos (c.sq_lt_three_ε_of_le_ρB h2) hy0, hd,
      fun h => k.axis_of_axialDefectDeriv_pCancellationField_eq_zero h1 h2 h3 h⟩
  · rintro x ⟨hx, hZ⟩
    have hx' := k.pAxialAnnulus_subset_pClosedBall hx
    have hZ' : c.e.χ.symm x = morseNorm n (c.e.χ.symm x) • c.e₁ := hZ
    have hρ := c.symm_mem_of_mem_pClosedBall hx'
    have hd := k.hasDerivAt_axial_cancellationFlow_p (x := x) (s := 0)
      (by rw [k.cancellationFlow_zero]; exact c.pClosedBall_subset_pBall' hx')
    rw [k.cancellationFlow_zero] at hd
    refine ⟨_, ?_, hd⟩
    have := k.axial_pCancellationField_pos_axis (ModelField.morseNorm_nonneg (c.e.χ.symm x)) hρ
    rw [← hZ'] at this
    exact this

theorem dot_pCancellationField_pos_of_inner_sphere {y : Fin n → ℝ} (hy : morseNorm n y = c.ρs)
    (hB : axialDefect c.e₁ y ≤ k.b₀) : 0 < dot y (k.pCancellationField y) := by
  have hy3 : morseNorm n y ^ 2 < 3 * c.ε := c.sq_lt_three_ε_of_le_ρB (hy ▸ c.ρs_lt_ρB.le)
  rw [k.dot_pCancellationField hy3, k.βp_eq_one_of_axialDefect_le hy.ge hB]
  obtain ⟨hapos, hsq, -⟩ := k.of_axialDefect_le hy.ge hB
  have hψ := c.ψp_ge_of_le_ρs hy.le
  have hθ := c.theta_mul_lt_third hy.ge
  have hθ0 := ModelField.theta_pos c.e.hr₀ y
  have hρ : 0 < morseNorm n y := hy ▸ c.ρs_pos
  have hC0 := k.pReversalWeight_nonneg y
  have hb := k.b₀_le
  have hm := c.m'_pos
  have h1b : 0 < 1 - k.b₀ := by linarith
  have ha' : (1 - k.b₀) * morseNorm n y ≤ axial c.e₁ y :=
    (pow_le_pow_iff_left₀ (by positivity) hapos.le two_ne_zero).1 (by rw [mul_pow]; exact hsq)
  have h1 : (1 - 2 * k.pReversalWeight y) * (ModelField.theta c.e.r₀ y * morseNorm n y ^ 2) ≤
      ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by
    have : 0 ≤ ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 := by positivity
    nlinarith
  have h2 : ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 < c.m' / 3 * morseNorm n y := by
    have : ModelField.theta c.e.r₀ y * morseNorm n y ^ 2 =
        (ModelField.theta c.e.r₀ y * morseNorm n y) * morseNorm n y := by ring
    rw [this]; exact mul_lt_mul_of_pos_right hθ hρ
  have h3 : c.m' * (9 / 10) * ((1 - k.b₀) * morseNorm n y) ≤
      c.m' * (1 * ψp c.ρA c.ρB y) * axial c.e₁ y := by
    rw [one_mul]
    have := mul_le_mul hψ ha' (by positivity) (ψp_nonneg _)
    have := mul_le_mul_of_nonneg_left this hm.le
    linarith
  have h4 : c.m' * (9 / 10) * (15 / 16 * morseNorm n y) ≤
      c.m' * (9 / 10) * ((1 - k.b₀) * morseNorm n y) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hρ.le
    linarith
  nlinarith

theorem exists_reach_middleTube_of_mem_pAxialAnnulus {x : M} (hx : x ∈ k.pAxialAnnulus) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.middleTube ∧ f (k.cancellationFlow t x) = c.lo₂ ∧ ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.pAxialAnnulus := by
  obtain ⟨t₀, ht₀, hexit⟩ := k.exists_exit_pAxialAnnulus x hx
  set Ob : Set M := c.e.χ '' {y | morseNorm n y < c.ρB} with hOb
  have hOb_symm : ∀ {z : M}, z ∈ Ob → morseNorm n (c.e.χ.symm z) < c.ρB := by
    rintro z ⟨y, hy, rfl⟩
    rw [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB (le_of_lt hy))]; exact hy
  have hinv : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ Ob) →
      ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.pAxialAnnulus := by
    intro t _ hlt
    have hQ : IsClosed {s : ℝ | k.cancellationFlow s x ∈ k.pAxialAnnulus} :=
      k.isCompact_pAxialAnnulus.isClosed.preimage (k.continuous_cancellationFlow_curve x)
    refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
    have hsW : k.cancellationFlow s x ∈ k.pAxialAnnulus := hIcc (right_mem_Icc.2 hs.1)
    have hsWb := k.pAxialAnnulus_subset_pClosedBall hsW
    have hsO := k.pAxialAnnulus_subset_pOpenAnnulus hsW
    obtain ⟨h1, h2, h3⟩ := (k.mem_pAxialAnnulus_iff (c.pClosedBall_subset_image_ball hsWb)).1 hsW
    obtain ⟨ε₁, hε₁, hO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_pOpenAnnulus hsO
    have hev₁ : ∀ᶠ s' in 𝓝[>] s, c.ρs ≤ morseNorm n (c.e.χ.symm (k.cancellationFlow s' x)) := by
      rcases h1.lt_or_eq with hlt' | heq
      · have hmem : k.cancellationFlow s x ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} :=
          c.e.mem_image_of_symm_mem (c.pClosedBall_subset_image_ball hsWb)
            ⟨hlt', c.sq_lt_three_ε_of_le_ρB h2⟩
        obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_annulus_gt hmem
        refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨s + ε, by simp [hε], fun s' hs' => ?_⟩
        obtain ⟨y, hy, hyx⟩ := hεO s' ⟨by linarith [hs'.1], hs'.2⟩
        change c.ρs ≤ morseNorm n (c.e.χ.symm (k.cancellationFlow s' x))
        rw [← hyx, c.chart_p_symm_eq' hy.2]; exact hy.1.le
      · have hd := k.hasDerivAt_morseNormSq_cancellationFlow_p (c.pClosedBall_subset_pBall' hsWb)
        have hpos := k.dot_pCancellationField_pos_of_inner_sphere heq.symm h3
        have := eventually_gt_of_hasDerivAt_pos (by linarith : 0 < 2 * dot (c.e.χ.symm (k.cancellationFlow s x))
          (k.pCancellationField (c.e.χ.symm (k.cancellationFlow s x)))) hd
        filter_upwards [this] with s' hs'
        show c.ρs ≤ morseNorm n (c.e.χ.symm (k.cancellationFlow s' x))
        have : c.ρs ^ 2 < morseNorm n (c.e.χ.symm (k.cancellationFlow s' x)) ^ 2 := by rw [heq]; exact hs'
        exact ((pow_lt_pow_iff_left₀ c.ρs_pos.le (ModelField.morseNorm_nonneg _) two_ne_zero).1
          this).le
    obtain ⟨u₁, hu₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev₁
    refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (min u₁ (s + ε₁)) t,
      lt_min (lt_min hu₁ (by linarith)) hs.2, fun s' hs' => ?_⟩
    have hs'u : s' ≤ u₁ := hs'.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs'ε : s' ≤ s + ε₁ := hs'.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs't : s' ≤ t := hs'.2.trans (min_le_right _ _)
    have hOp : ∀ u ∈ Icc s s', k.cancellationFlow u x ∈ c.pOpenAnnulus := fun u hu =>
      hO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩
    have hanti : AntitoneOn (fun u => axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow u x))) (Icc s s') := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc s s') ?_ ?_ ?_
      · intro u hu
        exact (k.hasDerivAt_axialDefect_cancellationFlow_p (c.pOpenAnnulus_subset_pBall' (hOp u hu))
          (c.symm_ne_zero_of_mem_pOpenAnnulus (hOp u hu))).continuousAt.continuousWithinAt
      · intro u hu
        have hu' := interior_subset hu
        exact (k.hasDerivAt_axialDefect_cancellationFlow_p (c.pOpenAnnulus_subset_pBall' (hOp u hu'))
          (c.symm_ne_zero_of_mem_pOpenAnnulus (hOp u hu'))).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' := interior_subset hu
        rw [(k.hasDerivAt_axialDefect_cancellationFlow_p (c.pOpenAnnulus_subset_pBall' (hOp u hu'))
          (c.symm_ne_zero_of_mem_pOpenAnnulus (hOp u hu'))).deriv]
        exact k.axialDefectDeriv_pCancellationField_nonpos (c.symm_sq_lt_of_mem_pOpenAnnulus (hOp u hu'))
          (c.symm_ne_zero_of_mem_pOpenAnnulus (hOp u hu'))
    have hB' := hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
    have hs'O := hOp s' (right_mem_Icc.2 hs'.1.le)
    refine (k.mem_pAxialAnnulus_iff (c.pBall'_subset_image_ball (c.pOpenAnnulus_subset_pBall' hs'O))).2
      ⟨hsub₁ ⟨hs'.1, hs'u⟩, (hOb_symm (hlt s' ⟨hs.1.trans hs'.1.le, hs't⟩)).le, hB'.trans h3⟩
  have hhit : ∃ s ∈ Icc 0 t₀, k.cancellationFlow s x ∈ Obᶜ := by
    by_contra h
    push Not at h
    exact hexit (hinv t₀ ht₀ (fun s hs => not_not.1 (h s hs)) t₀ (right_mem_Icc.2 ht₀))
  obtain ⟨s₀, hs₀, hs₀E, hmin⟩ := exists_first_time c.isOpen_ball_ρB.isClosed_compl
    (k.continuous_cancellationFlow_curve x) hhit
  have hbefore : ∀ s ∈ Ico 0 s₀, k.cancellationFlow s x ∈ k.pAxialAnnulus := fun s hs =>
    hinv s hs.1 (fun u hu => not_not.1 (hmin u ⟨hu.1, hu.2.trans_lt hs.2⟩)) s
      (right_mem_Icc.2 hs.1)
  have hs₀W : k.cancellationFlow s₀ x ∈ k.pAxialAnnulus := by
    rcases hs₀.1.eq_or_lt with h | h
    · rw [← h, k.cancellationFlow_zero]; exact hx
    · refine k.isCompact_pAxialAnnulus.isClosed.mem_of_tendsto
        ((k.continuous_cancellationFlow_curve x).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio s₀))) ?_
      filter_upwards [Ico_mem_nhdsLT h] with s hs using hbefore s hs
  have hall : ∀ s ∈ Icc 0 s₀, k.cancellationFlow s x ∈ k.pAxialAnnulus := fun s hs => by
    rcases hs.2.eq_or_lt with h | h
    · rw [h]; exact hs₀W
    · exact hbefore s ⟨hs.1, h⟩
  have hs₀Wb := k.pAxialAnnulus_subset_pClosedBall hs₀W
  obtain ⟨h1, h2, h3⟩ := (k.mem_pAxialAnnulus_iff (c.pClosedBall_subset_image_ball hs₀Wb)).1 hs₀W
  have hρ : morseNorm n (c.e.χ.symm (k.cancellationFlow s₀ x)) = c.ρB := by
    refine le_antisymm h2 ?_
    by_contra hlt
    push Not at hlt
    exact hs₀E (c.e.mem_image_of_symm_mem (c.pClosedBall_subset_image_ball hs₀Wb) hlt)
  set y := c.e.χ.symm (k.cancellationFlow s₀ x) with hy
  have hχy : c.e.χ y = k.cancellationFlow s₀ x := c.e.symm_image_eq (c.pClosedBall_subset_image_ball hs₀Wb)
  have hf : f (k.cancellationFlow s₀ x) = c.lo₂ := by
    rw [← hχy, c.f_chart_p (h2.trans c.ρB_le_R), hρ, c.ρB_sq_eq]; ring
  obtain ⟨hT, hζ⟩ := k.mem_tube_of_axialDefect_le h1 h2 h3
  rw [hχy] at hT hζ
  refine ⟨s₀, hs₀.1, ⟨k.mem_closedFlowTube_iff.2 ⟨hT, ⟨?_, ?_⟩, hζ.le⟩, hf.ge, ?_⟩, hf, hall⟩
  · rw [hf]; exact c.lo₂_mem_levels
  · rw [hf]; linarith [c.lo₂_lt_hi₁, c.hi₁_mem_levels]
  · rw [hf]; exact c.lo₂_lt_hi₁.le

theorem exists_reach_middleTube_of_mem_pClosedBall
    (hζmin : ∀ y : Fin n → ℝ, c.ρA ≤ morseNorm n y → morseNorm n y ≤ c.ρB →
      k.b₀ ≤ axialDefect c.e₁ y → c.e.χ y ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ (c.e.χ y)‖)
    {x : M} (hx : x ∈ c.pClosedBall) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.middleTube ∧ f (k.cancellationFlow t x) = c.lo₂ ∧ ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ c.pClosedBall := by
  have hx' := (k.pClosedBall_eq_union ▸ hx : x ∈ k.pInnerAngularRegion ∪ k.pAxialAnnulus)
  rcases hx' with hx1 | hx2
  · obtain ⟨t₁, ht₁, hW2, hball⟩ := k.exists_reach_pAxialAnnulus hζmin hx1
    obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_middleTube_of_mem_pAxialAnnulus hW2
    refine ⟨t₁ + t₂, by positivity, by rw [k.cancellationFlow_add]; exact hT, by rw [k.cancellationFlow_add]; exact hf,
      fun s hs => ?_⟩
    rcases le_or_gt s t₁ with h | h
    · exact hball s ⟨hs.1, h⟩
    · have := hW (s - t₁) ⟨by linarith, by linarith [hs.2]⟩
      rw [k.cancellationFlow_cancellationFlow, add_sub_cancel] at this
      exact k.pAxialAnnulus_subset_pClosedBall this
  · obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_middleTube_of_mem_pAxialAnnulus hx2
    exact ⟨t₂, ht₂, hT, hf, fun s hs => k.pAxialAnnulus_subset_pClosedBall (hW s hs)⟩

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
