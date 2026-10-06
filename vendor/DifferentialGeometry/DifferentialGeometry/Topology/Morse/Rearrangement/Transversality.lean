module

public import DifferentialGeometry.Topology.Morse.Strip.StripFlow

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le negPart posPart morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split
  recombine recombine_decompose morseNorm_recombine_sq)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem flow_eq_of_agree {D₁ D₂ : GradientLikeStrip I f a b crit} {U : Set M} (hU : IsOpen U)
    (hV : ∀ x ∈ U, D₁.V x = D₂.V x) {x : M} {T : ℝ}
    (hmem : ∀ s ∈ Ico 0 T, D₁.flow s x ∈ U) :
    ∀ s ∈ Icc 0 T, D₂.flow s x = D₁.flow s x := by
  have hQ : IsClosed {s : ℝ | D₂.flow s x = D₁.flow s x} :=
    isClosed_eq (D₂.continuous_flow_curve x) (D₁.continuous_flow_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp) fun t ht hIcc => ?_
  have hxt : D₂.flow t x = D₁.flow t x := hIcc (right_mem_Icc.2 ht.1)
  have hγ₁ : IsMIntegralCurveAt (fun s => D₁.flow s x) D₁.V t :=
    (D₁.isMIntegralCurve_flow x).isMIntegralCurveAt t
  have hγ₂ : IsMIntegralCurveAt (fun s => D₂.flow s x) D₁.V t := by
    have hev : ∀ᶠ s in 𝓝 t, D₂.flow s x ∈ U :=
      (D₂.continuous_flow_curve x).continuousAt.preimage_mem_nhds
        (hU.mem_nhds (hxt ▸ hmem t ht))
    filter_upwards [hev] with s hs
    have := D₂.isMIntegralCurve_flow x s
    rwa [← hV _ hs] at this
  have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    (D₁.smooth_one.contMDiffAt) hγ₁ hγ₂ hxt.symm
  exact nhdsWithin_le_nhds (heq.mono fun s hs => hs.symm)

theorem flow_eq_of_agree_neg {D₁ D₂ : GradientLikeStrip I f a b crit} {U : Set M}
    (hU : IsOpen U) (hV : ∀ x ∈ U, D₁.V x = D₂.V x) {x : M} {T : ℝ} (hT : 0 ≤ T)
    (hmem : ∀ s ∈ Ico (-T) 0, D₁.flow s x ∈ U) :
    ∀ s ∈ Icc (-T) 0, D₂.flow s x = D₁.flow s x := by
  set y := D₁.flow (-T) x with hy
  have h1 : ∀ s ∈ Ico 0 T, D₁.flow s y ∈ U := by
    intro s hs
    rw [hy, flow_flow]
    exact hmem _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 := flow_eq_of_agree hU hV h1
  have hTy : D₂.flow T y = x := by
    rw [h2 T (right_mem_Icc.2 hT), hy, flow_flow, neg_add_cancel, flow_zero]
  intro s hs
  have := h2 (s + T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [hy, flow_flow, show -T + (s + T) = s by ring] at this
  calc D₂.flow s x = D₂.flow s (D₂.flow T y) := by rw [hTy]
    _ = D₂.flow (T + s) y := by rw [flow_flow]
    _ = D₁.flow s x := by rw [add_comm]; exact this

end GradientLikeStrip

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} {d : MorseNormalChart I f p}

theorem mfderiv_chart_symm_apply {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R')
    (v : TangentSpace I (d.χ y)) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ y (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) v) = v := by
  have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) (d.χ y)
    (d.mdifferentiableAt_chart (d.symm_mem_ball (mem_image_of_mem _ hy)))
    (d.mdifferentiableAt_symm (mem_image_of_mem _ hy))
  have hev : (d.χ ∘ d.χ.symm) =ᶠ[𝓝 (d.χ y)] id :=
    eventuallyEq_of_mem (d.isOpen_image_ball.mem_nhds (mem_image_of_mem _ hy))
      fun x hx => d.symm_image_eq hx
  have h1 := hev.mfderiv_eq (I := I) (I' := I)
  rw [mfderiv_id] at h1
  have h2 := DFunLike.congr_fun (hcomp.symm.trans h1) v
  rw [d.χ.left_inv (d.hball hy)] at h2
  exact h2

theorem df_mfderiv_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') (w : Fin n → ℝ) :
    (NormedSpace.fromTangentSpace (f (d.χ y)))
        ((mfderiv I 𝓘(ℝ, ℝ) f (d.χ y)) (mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ y w)) =
      fderiv ℝ (f ∘ d.χ) y w := by
  have hcomp := mfderiv_comp y ((hf (d.χ y)).mdifferentiableAt (by simp))
    (d.mdifferentiableAt_chart hy)
  have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (f ∘ d.χ) y = fderiv ℝ (f ∘ d.χ) y :=
    mfderiv_eq_fderiv
  exact DFunLike.congr_fun (hcomp.symm.trans h1) w

theorem dfV_eq_fderiv_pullback (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace I x)
    {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    dfV I f V (d.χ y) =
      fderiv ℝ (f ∘ d.χ) y (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) (V (d.χ y))) := by
  have h := df_mfderiv_chart hf hy (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) (V (d.χ y)))
  rw [mfderiv_chart_symm_apply hy] at h
  exact h

end MorseNormalChart

omit [IsManifold I ∞ M] in
theorem dfV_add (V W : (x : M) → TangentSpace I x) (x : M) :
    dfV I f (fun x => V x + W x) x = dfV I f V x + dfV I f W x := by
  unfold dfV; simp

namespace GradientLikeStrip

variable (D : GradientLikeStrip I f a b crit)

theorem dfV_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (hp : p ∈ crit) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) :
    dfV I f D.V ((D.chart p hp).χ y) =
      -(ModelField.theta (D.chart p hp).r₀ y * morseNorm n y ^ 2) := by
  rw [MorseNormalChart.dfV_eq_fderiv_pullback hf _
    (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' p hp))), D.model p hp y hy,
    (D.chart p hp).fderiv_comp_eq_nf (hy.trans_le (D.hrm p hp).2), ModelField.fderiv_nf_modelField]

variable {D}

theorem V_chart_eq (p : M) (hp : p ∈ crit) {y : Fin n → ℝ} (hy : morseNorm n y < D.rm p hp) :
    D.V ((D.chart p hp).χ y) = mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart p hp).χ y
      (ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀ y) := by
  rw [← D.model p hp y hy, MorseNormalChart.mfderiv_chart_symm_apply
    (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' p hp)))]

section AddPush

variable (p : M) (hp : p ∈ crit) (Y : (Fin n → ℝ) → Fin n → ℝ)

def addPush : (x : M) → TangentSpace I x := fun x => D.V x + (D.chart p hp).push Y x

theorem addPush_apply (x : M) : addPush (D := D) p hp Y x = D.V x + (D.chart p hp).push Y x := rfl

theorem addPush_of_notMem {x : M} (hx : x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') :
    addPush (D := D) p hp Y x = D.V x := by
  rw [addPush_apply, MorseNormalChart.push_apply_of_notMem Y hx, add_zero]

theorem addPush_of_notMem_image {K : Set (Fin n → ℝ)} (hYK : ∀ y ∉ K, Y y = 0) {x : M}
    (hx : x ∉ (D.chart p hp).χ '' K) : addPush (D := D) p hp Y x = D.V x := by
  rw [addPush_apply, MorseNormalChart.push_eq_zero_of_notMem_image hYK hx, add_zero]

theorem addPush_chart_of_ne {q : M} (hq : q ∈ crit) (hpq : q ≠ p) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R') :
    addPush (D := D) p hp Y ((D.chart q hq).χ y) = D.V ((D.chart q hq).χ y) := by
  refine addPush_of_notMem p hp Y fun h => ?_
  exact (D.disjoint q hq p hp hpq).notMem_of_mem_left (mem_image_of_mem _ hy) h

theorem pullback_addPush {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R')
    {v : Fin n → ℝ} (hv : mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
      (D.V ((D.chart p hp).χ y)) = v) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
        (addPush (D := D) p hp Y ((D.chart p hp).χ y)) = v + Y y := by
  rw [addPush_apply, map_add, MorseNormalChart.pullback_push Y hy, hv]
  rfl

theorem dfV_addPush_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R') :
    dfV I f (addPush (D := D) p hp Y) ((D.chart p hp).χ y) =
      dfV I f D.V ((D.chart p hp).χ y) + fderiv ℝ (f ∘ (D.chart p hp).χ) y (Y y) := by
  have h := dfV_add (I := I) (f := f) D.V ((D.chart p hp).push Y) ((D.chart p hp).χ y)
  have h2 : dfV I f ((D.chart p hp).push Y) ((D.chart p hp).χ y) =
      fderiv ℝ (f ∘ (D.chart p hp).χ) y (Y y) := MorseNormalChart.df_push_chart hf Y hy
  rw [h2] at h
  exact h

theorem dfV_addPush_chart_nf (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy : morseNorm n y < (D.chart p hp).R) :
    dfV I f (addPush (D := D) p hp Y) ((D.chart p hp).χ y) =
      dfV I f D.V ((D.chart p hp).χ y) +
        fderiv ℝ (morseNormalForm (D.chart p hp).hk (f p)) y (Y y) := by
  rw [dfV_addPush_chart p hp Y hf (mem_ball_of_morseNorm_lt (hy.trans (D.chart p hp).hRR')),
    (D.chart p hp).fderiv_comp_eq_nf hy]

theorem dfV_addPush_of_notMem {x : M}
    (hx : x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') :
    dfV I f (addPush (D := D) p hp Y) x = dfV I f D.V x := by
  unfold dfV
  rw [addPush_of_notMem p hp Y hx]

variable [T2Space M]

theorem contMDiff_addPush (hY : ContDiff ℝ ∞ Y) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : K ⊆ Metric.ball 0 (D.chart p hp).R') (hYK : ∀ y ∉ K, Y y = 0) :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, addPush (D := D) p hp Y x⟩ : TangentBundle I M)) :=
  D.smooth.add_section ((D.chart p hp).contMDiff_push hY hK hKb hYK)

theorem isCompact_tsupport_addPush {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : K ⊆ Metric.ball 0 (D.chart p hp).R') (hYK : ∀ y ∉ K, Y y = 0) :
    IsCompact (tsupport (addPush (D := D) p hp Y)) := by
  have hC : IsCompact ((D.chart p hp).χ '' K) :=
    hK.image_of_continuousOn ((D.chart p hp).χ.continuousOn.mono (hKb.trans (D.chart p hp).hball))
  refine (D.compact.union hC).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun x hx => ?_) (D.compact.union hC).isClosed)
  by_contra h
  rw [mem_union, not_or] at h
  apply hx
  rw [addPush_apply, image_eq_zero_of_notMem_tsupport h.1,
    MorseNormalChart.push_eq_zero_of_notMem_image hYK h.2]
  exact add_zero (0 : Fin n → ℝ)

end AddPush

section Twisted

variable (p : M) (hp : p ∈ crit) (η ρ : ℝ) (z : EuclideanSpace ℝ (Fin (D.chart p hp).k))

def twistY : (Fin n → ℝ) → Fin n → ℝ :=
  ModelField.twist (D.chart p hp).hk (f p) η ρ z

def twistR (η ρ : ℝ) : ℝ := Real.sqrt (2 * η + 18 * ρ ^ 2 / η)

def twistedV : (x : M) → TangentSpace I x := addPush (D := D) p hp (twistY (D := D) p hp η ρ z)

variable {p hp η ρ z}

theorem twistR_sq (hη : 0 < η) : twistR η ρ ^ 2 = 2 * η + 18 * ρ ^ 2 / η := by
  rw [twistR, Real.sq_sqrt (by positivity)]

theorem twistR_lt_R (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) :
    twistR η ρ < (D.chart p hp).R := by
  rw [twistR]
  exact (Real.sqrt_lt' (D.chart p hp).R_pos).2 hsupp

theorem twistY_eq_zero_of_notMem (hη : 0 < η) (hρ : 0 < ρ) {y : Fin n → ℝ}
    (hy : y ∉ {y : Fin n → ℝ | morseNorm n y ≤ twistR η ρ}) :
    twistY (D := D) p hp η ρ z y = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hy (ModelField.tsupport_twist_subset_ball (D.chart p hp).hk hη hρ (Real.sqrt_nonneg _)
    (twistR_sq hη).ge z h)

theorem twistY_eq_zero_of_R_le (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) {y : Fin n → ℝ}
    (hy : (D.chart p hp).R ≤ morseNorm n y) : twistY (D := D) p hp η ρ z y = 0 :=
  twistY_eq_zero_of_notMem hη hρ fun h => absurd (lt_of_le_of_lt (le_trans hy h)
    (twistR_lt_R hsupp)) (lt_irrefl _)

theorem contDiff_twistY (hη : 0 < η) : ContDiff ℝ ∞ (twistY (D := D) p hp η ρ z) :=
  ModelField.contDiff_twist (D.chart p hp).hk hη ρ z

theorem twistR_ball_subset
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) :
    {y : Fin n → ℝ | morseNorm n y ≤ twistR η ρ} ⊆
      Metric.ball 0 (D.chart p hp).R' :=
  (D.chart p hp).le_subset_ball ((twistR_lt_R hsupp).trans (D.chart p hp).hRR')

theorem dfV_twistedV (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (x : M) :
    dfV I f (twistedV (D := D) p hp η ρ z) x = dfV I f D.V x := by
  by_cases hx : x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'
  · obtain ⟨y, hy, rfl⟩ := hx
    by_cases hyR : morseNorm n y < (D.chart p hp).R
    · rw [twistedV, dfV_addPush_chart_nf p hp _ hf hyR, twistY,
        ModelField.fderiv_nf_twist (D.chart p hp).hk hη ρ z, add_zero]
    · rw [twistedV, dfV_addPush_chart p hp _ hf hy, twistY_eq_zero_of_R_le hη hρ hsupp
        (not_lt.1 hyR), map_zero, add_zero]
  · exact dfV_addPush_of_notMem p hp _ hx

theorem twistedV_of_notMem {x : M}
    (hx : x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') :
    twistedV (D := D) p hp η ρ z x = D.V x :=
  addPush_of_notMem p hp _ hx

theorem twistedV_of_notMem_image (hη : 0 < η) (hρ : 0 < ρ) {x : M}
    (hx : x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ twistR η ρ}) :
    twistedV (D := D) p hp η ρ z x = D.V x :=
  addPush_of_notMem_image p hp _ (fun _ hy => twistY_eq_zero_of_notMem hη hρ hy) hx

theorem pullback_twistedV {y : Fin n → ℝ} (hy : morseNorm n y < D.rm p hp) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
        (twistedV (D := D) p hp η ρ z ((D.chart p hp).χ y)) =
      ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀ y +
        ModelField.twist (D.chart p hp).hk (f p) η ρ z y :=
  pullback_addPush p hp _ (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' p hp)))
    (D.model p hp y hy)

variable [T2Space M]

theorem contMDiff_twistedV (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, twistedV (D := D) p hp η ρ z x⟩ : TangentBundle I M)) :=
  contMDiff_addPush p hp _ (contDiff_twistY hη) (isCompact_morseNorm_le _)
    (twistR_ball_subset hsupp) fun _ hy => twistY_eq_zero_of_notMem hη hρ hy

theorem isCompact_tsupport_twistedV (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) :
    IsCompact (tsupport (twistedV (D := D) p hp η ρ z)) :=
  isCompact_tsupport_addPush p hp _ (isCompact_morseNorm_le _)
    (twistR_ball_subset hsupp) fun _ hy => twistY_eq_zero_of_notMem hη hρ hy

theorem nf_lt_of_morseNorm_sq_lt {k : ℕ} (hk : k ≤ n) (c : ℝ) {y : Fin n → ℝ} {η : ℝ}
    (hy : morseNorm n y ^ 2 < η) : morseNormalForm hk c y < c + η / 2 := by
  rw [morseNormalForm_split]
  rw [morseNorm_sq_eq_negPart_add_posPart hk] at hy
  nlinarith [sq_nonneg ‖negPart hk y‖]

open Classical in
def twisted (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) : GradientLikeStrip I f a b crit where
  V := twistedV (D := D) p hp η ρ z
  smooth := contMDiff_twistedV hη hρ hsupp
  compact := isCompact_tsupport_twistedV hη hρ hsupp
  rate x := by
    have h := D.dfV_rate x
    rw [← dfV_twistedV (z := z) hf hη hρ hsupp x] at h
    exact h
  chart := D.chart
  disjoint := D.disjoint
  inStrip := D.inStrip
  unit x hx hxB := by
    have h : dfV I f D.V x = -1 := D.unit x hx hxB
    rw [← dfV_twistedV (z := z) hf hη hρ hsupp x] at h
    exact h
  neg x hx hxc := by
    have h : dfV I f D.V x < 0 := D.neg x hx hxc
    rw [← dfV_twistedV (z := z) hf hη hρ hsupp x] at h
    exact h
  rm q hq := if q = p then Real.sqrt η else D.rm q hq
  hrm q hq := by
    by_cases h : q = p
    · subst h
      simp only [ite_true]
      constructor
      · rw [Real.lt_sqrt (by linarith [(D.chart q hq).hr₀])]
        linarith
      · refine (Real.sqrt_le_sqrt hηrm).trans ?_
        rw [Real.sqrt_sq (D.rm_pos q hq).le]
        exact (D.hrm q hq).2
    · simp only [h, ite_false]
      exact D.hrm q hq
  model q hq y hy := by
    by_cases h : q = p
    · subst h
      simp only [ite_true] at hy
      have hy2 : morseNorm n y ^ 2 < η := (Real.lt_sqrt (ModelField.morseNorm_nonneg y)).1 hy
      have hyrm : morseNorm n y < D.rm q hq := by
        rw [Real.lt_sqrt (ModelField.morseNorm_nonneg y)] at hy
        exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos q hq).le (hy.trans_le hηrm)
      rw [pullback_twistedV hyrm, ModelField.twist_eq_zero_of_nf_le _ hη z
        (nf_lt_of_morseNorm_sq_lt _ _ hy2).le, add_zero]
    · simp only [h, ite_false] at hy
      have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' :=
        mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' q hq))
      rw [twistedV, addPush_chart_of_ne p hp _ hq h hyb]
      exact D.model q hq y hy

variable (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η)

@[simp] theorem twisted_V : (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).V =
    twistedV (D := D) p hp η ρ z := rfl

@[simp] theorem twisted_chart : (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).chart = D.chart := rfl

theorem twisted_rm_self : (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).rm p hp = Real.sqrt η := by
  simp [twisted]

theorem twisted_rm_of_ne {q : M} (hq : q ∈ crit) (h : q ≠ p) :
    (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).rm q hq = D.rm q hq := by
  simp [twisted, h]

theorem twisted_smallBall (q : M) (hq : q ∈ crit) :
    (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).smallBall q hq = D.smallBall q hq := rfl

end Twisted

section Shrink

variable (p : M) (hp : p ∈ crit) (r₀' : ℝ)

def shrinkY : (Fin n → ℝ) → Fin n → ℝ := fun y =>
  ModelField.modelField (D.chart p hp).k r₀' y - ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀ y

def shrunkV : (x : M) → TangentSpace I x := addPush (D := D) p hp (shrinkY (D := D) p hp r₀')

variable {p hp r₀'}

theorem shrinkY_eq_zero (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) {y : Fin n → ℝ}
    (hy : (D.chart p hp).r₀ / 2 ≤ morseNorm n y) : shrinkY (D := D) p hp r₀' y = 0 := by
  unfold shrinkY ModelField.modelField
  rw [ModelField.theta_eq (D.chart p hp).hr₀ hy, ModelField.theta_eq hr₀' (by linarith), sub_self]

theorem shrinkY_eq_zero_of_notMem (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) {y : Fin n → ℝ}
    (hy : y ∉ {y : Fin n → ℝ | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) :
    shrinkY (D := D) p hp r₀' y = 0 :=
  shrinkY_eq_zero hr₀' hle (le_of_lt (not_le.1 hy))

theorem contDiff_shrinkY (hr₀' : 0 < r₀') : ContDiff ℝ ∞ (shrinkY (D := D) p hp r₀') :=
  (ModelField.contDiff_modelField hr₀').sub (ModelField.contDiff_modelField (D.chart p hp).hr₀)

theorem half_r₀_ball_subset :
    {y : Fin n → ℝ | morseNorm n y ≤ (D.chart p hp).r₀ / 2} ⊆ Metric.ball 0 (D.chart p hp).R' :=
  (D.chart p hp).le_subset_ball (by linarith [D.r₀_lt_R' p hp, (D.chart p hp).hr₀])

theorem shrunkV_of_notMem_image (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) {x : M}
    (hx : x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) :
    shrunkV (D := D) p hp r₀' x = D.V x :=
  addPush_of_notMem_image p hp _ (fun _ hy => shrinkY_eq_zero_of_notMem hr₀' hle hy) hx

theorem shrunkV_of_notMem {x : M}
    (hx : x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') :
    shrunkV (D := D) p hp r₀' x = D.V x :=
  addPush_of_notMem p hp _ hx

theorem pullback_shrunkV {y : Fin n → ℝ} (hy : morseNorm n y < D.rm p hp) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
        (shrunkV (D := D) p hp r₀' ((D.chart p hp).χ y)) =
      ModelField.modelField (D.chart p hp).k r₀' y := by
  rw [shrunkV, pullback_addPush p hp _ (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' p hp)))
    (D.model p hp y hy), shrinkY, add_sub_cancel]

theorem dfV_shrunkV_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy : morseNorm n y < D.rm p hp) :
    dfV I f (shrunkV (D := D) p hp r₀') ((D.chart p hp).χ y) =
      -(ModelField.theta r₀' y * morseNorm n y ^ 2) := by
  rw [MorseNormalChart.dfV_eq_fderiv_pullback hf _
    (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' p hp))), pullback_shrunkV hy,
    (D.chart p hp).fderiv_comp_eq_nf (hy.trans_le (D.hrm p hp).2), ModelField.fderiv_nf_modelField]

theorem dfV_shrunkV_eq (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) {x : M}
    (hx : x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) :
    dfV I f (shrunkV (D := D) p hp r₀') x = dfV I f D.V x := by
  unfold dfV
  rw [shrunkV_of_notMem_image hr₀' hle hx]

theorem half_r₀_lt_rm : (D.chart p hp).r₀ / 2 < D.rm p hp := by
  linarith [D.r₀_lt_rm p hp, (D.chart p hp).hr₀]

variable [T2Space M]

theorem contMDiff_shrunkV (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, shrunkV (D := D) p hp r₀' x⟩ : TangentBundle I M)) :=
  contMDiff_addPush p hp _ (contDiff_shrinkY hr₀') (isCompact_morseNorm_le _)
    half_r₀_ball_subset fun _ hy => shrinkY_eq_zero_of_notMem hr₀' hle hy

theorem isCompact_tsupport_shrunkV (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) :
    IsCompact (tsupport (shrunkV (D := D) p hp r₀')) :=
  isCompact_tsupport_addPush p hp _ (isCompact_morseNorm_le _)
    half_r₀_ball_subset fun _ hy => shrinkY_eq_zero_of_notMem hr₀' hle hy

open Classical in
def shrinkChart (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) (q : M) (hq : q ∈ crit) :
    MorseNormalChart I f q :=
  { D.chart q hq with
    r₀ := if q = p then r₀' else (D.chart q hq).r₀
    hr₀ := by split_ifs <;> [exact hr₀'; exact (D.chart q hq).hr₀]
    hr₀R := by
      split_ifs with h
      · subst h; linarith [(D.chart q hq).hr₀R]
      · exact (D.chart q hq).hr₀R }

open Classical in
def shrinkAt (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) :
    GradientLikeStrip I f a b crit where
  V := shrunkV (D := D) p hp r₀'
  smooth := contMDiff_shrunkV hr₀' hle
  compact := isCompact_tsupport_shrunkV hr₀' hle
  rate x := by
    by_cases hx : x ∈ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}
    · obtain ⟨y, hy, rfl⟩ := hx
      have h := dfV_shrunkV_chart (r₀' := r₀') hf
        (lt_of_le_of_lt (show morseNorm n y ≤ _ from hy) half_r₀_lt_rm)
      have h1 := MorseNormalChart.theta_mul_sq_le_one hr₀' y
      have h2 : 0 ≤ ModelField.theta r₀' y * morseNorm n y ^ 2 :=
        mul_nonneg (ModelField.theta_pos hr₀' y).le (sq_nonneg _)
      change -1 ≤ dfV I f _ _ ∧ dfV I f _ _ ≤ 0
      rw [h]
      constructor <;> linarith
    · have h := D.dfV_rate x
      rw [← dfV_shrunkV_eq hr₀' hle hx] at h
      exact h
  chart := shrinkChart hr₀' hle
  disjoint := D.disjoint
  inStrip := D.inStrip
  unit x hx hxB := by
    change dfV I f _ _ = -1
    by_cases hx' : x ∈ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}
    · obtain ⟨y, hy, rfl⟩ := hx'
      have hyr : r₀' ≤ morseNorm n y := by
        by_contra hlt
        exact hxB p hp ⟨y, by simpa [shrinkChart] using not_le.1 hlt, rfl⟩
      rw [dfV_shrunkV_chart hf (lt_of_le_of_lt (show morseNorm n y ≤ _ from hy) half_r₀_lt_rm),
        ModelField.theta_mul_sq hr₀' (by linarith)]
    · rw [dfV_shrunkV_eq hr₀' hle hx']
      by_cases hx'' : x ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).r₀}
      · obtain ⟨y, hy, rfl⟩ := hx''
        have hy2 : (D.chart p hp).r₀ / 2 ≤ morseNorm n y := by
          by_contra hlt
          exact hx' ⟨y, le_of_lt (not_le.1 hlt), rfl⟩
        rw [D.dfV_chart hf p hp (lt_trans hy (D.r₀_lt_rm p hp)),
          ModelField.theta_mul_sq (D.chart p hp).hr₀ hy2]
      · refine D.unit x hx fun q hq => ?_
        by_cases h : q = p
        · subst h; exact hx''
        · have := hxB q hq
          simpa [shrinkChart, h] using this
  neg x hx hxc := by
    change dfV I f _ _ < 0
    by_cases hx' : x ∈ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}
    · obtain ⟨y, hy, rfl⟩ := hx'
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [(D.chart p hp).hχ0] at hxc
        exact hxc hp
      rw [dfV_shrunkV_chart hf (lt_of_le_of_lt (show morseNorm n y ≤ _ from hy) half_r₀_lt_rm)]
      have h1 := ModelField.theta_pos hr₀' y
      have h2 : 0 < morseNorm n y := by
        rcases (ModelField.morseNorm_nonneg y).lt_or_eq with h | h
        · exact h
        · exact absurd ((ModelField.morseNorm_eq_zero_iff y).1 h.symm) hy0
      have : 0 < ModelField.theta r₀' y * morseNorm n y ^ 2 := by positivity
      linarith
    · rw [dfV_shrunkV_eq hr₀' hle hx']
      exact D.neg x hx hxc
  rm := D.rm
  hrm q hq := by
    refine ⟨?_, (D.hrm q hq).2⟩
    change 2 * (if q = p then r₀' else (D.chart q hq).r₀) < D.rm q hq
    split_ifs with h
    · subst h; linarith [(D.hrm q hq).1]
    · exact (D.hrm q hq).1
  model q hq y hy := by
    by_cases h : q = p
    · subst h
      change mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart q hq).χ.symm ((D.chart q hq).χ y)
        (shrunkV (D := D) q hq r₀' ((D.chart q hq).χ y)) =
        ModelField.modelField (D.chart q hq).k (if q = q then r₀' else (D.chart q hq).r₀) y
      rw [ite_eq_left rfl]
      exact pullback_shrunkV hy
    · change mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart q hq).χ.symm ((D.chart q hq).χ y)
        (shrunkV (D := D) p hp r₀' ((D.chart q hq).χ y)) =
        ModelField.modelField (D.chart q hq).k (if q = p then r₀' else (D.chart q hq).r₀) y
      rw [ite_eq_right h, shrunkV, addPush_chart_of_ne p hp _ hq h
        (mem_ball_of_morseNorm_lt (hy.trans (D.rm_lt_R' q hq)))]
      exact D.model q hq y hy

variable (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀)

@[simp] theorem shrinkAt_V : (shrinkAt hf hr₀' hle).V = shrunkV (D := D) p hp r₀' := rfl

@[simp] theorem shrinkAt_chart_χ (q : M) (hq : q ∈ crit) :
    ((shrinkAt hf hr₀' hle).chart q hq).χ = (D.chart q hq).χ := rfl

@[simp] theorem shrinkAt_chart_k (q : M) (hq : q ∈ crit) :
    ((shrinkAt hf hr₀' hle).chart q hq).k = (D.chart q hq).k := rfl

@[simp] theorem shrinkAt_chart_R (q : M) (hq : q ∈ crit) :
    ((shrinkAt hf hr₀' hle).chart q hq).R = (D.chart q hq).R := rfl

@[simp] theorem shrinkAt_chart_R' (q : M) (hq : q ∈ crit) :
    ((shrinkAt hf hr₀' hle).chart q hq).R' = (D.chart q hq).R' := rfl

@[simp] theorem shrinkAt_rm : (shrinkAt hf hr₀' hle).rm = D.rm := rfl

theorem shrinkAt_chart_r₀_self : ((shrinkAt hf hr₀' hle).chart p hp).r₀ = r₀' := by
  simp [shrinkAt, shrinkChart]

theorem shrinkAt_chart_r₀_of_ne {q : M} (hq : q ∈ crit) (h : q ≠ p) :
    ((shrinkAt hf hr₀' hle).chart q hq).r₀ = (D.chart q hq).r₀ := by
  simp [shrinkAt, shrinkChart, h]

end Shrink

end GradientLikeStrip

namespace ModelField

open scoped RealInnerProductSpace

variable {k : ℕ} (hk : k ≤ n) {c ε ρ r₀ : ℝ} {z : EuclideanSpace ℝ (Fin k)} {γ : ℝ → Fin n → ℝ}
  {t₀ t₁ : ℝ}

theorem ascending_twisted_curve' (hr₀ : 0 < r₀) (hε : 0 < ε) (hρ : 0 < ρ) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hr₀ε₀ : r₀ ^ 2 ≤ 8 * ε₀) (hz : ‖z‖ ≤ ρ) (ht₀₁ : t₀ ≤ t₁)
    (hγ : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt γ (-(modelField k r₀ (γ t) + twist hk c ε ρ z (γ t))) t)
    (hJ0 : scaledNegativePart hk (γ t₀) = 0) (hlow : c + ε₀ ≤ morseNormalForm hk c (γ t₀))
    (hnf0 : morseNormalForm hk c (γ t₀) ≤ c + ε / 2) :
    (∀ t ∈ Icc t₀ t₁, morseNormalForm hk c (γ t) = morseNormalForm hk c (γ t₀) + (t - t₀)) ∧
    (∀ t ∈ Icc t₀ t₁, scaledNegativePart hk (γ t) = levelCutoff c ε (morseNormalForm hk c (γ t)) • z) ∧
    (∀ t ∈ Icc t₀ t₁, ‖scaledNegativePart hk (γ t)‖ ≤ ‖z‖) := by
  have hmono := nf_monotoneOn_ascending hk hr₀ hε hγ
  have hge : ∀ t ∈ Icc t₀ t₁, c + ε₀ ≤ morseNormalForm hk c (γ t) := by
    intro t ht
    have := hmono (left_mem_Icc.2 ht₀₁) ht ht.1
    simp only at this
    linarith
  have hunit : ∀ t ∈ Icc t₀ t₁, r₀ / 2 ≤ morseNorm n (γ t) := fun t ht =>
    morseNorm_ge_of_nf_ge hk hr₀ (c := c) (ε := 2 * ε₀) (by linarith) (by linarith [hge t ht])
  have hpos : ∀ t ∈ Icc t₀ t₁, posPart hk (γ t) ≠ 0 := fun t ht =>
    posPart_ne_zero_of_lt_nf hk (c := c) (by linarith [hge t ht])
  have hlevel : ∀ t ∈ Icc t₀ t₁,
      morseNormalForm hk c (γ t) = morseNormalForm hk c (γ t₀) + (t - t₀) := by
    have hd : ∀ t ∈ Icc t₀ t₁,
        HasDerivAt (fun s => morseNormalForm hk c (γ s) - s) 0 t := by
      intro t ht
      have h2 := (hasDerivAt_nf_ascending hk hε (hγ t ht)).sub (hasDerivAt_id' (x := t))
      rw [theta_mul_sq hr₀ (hunit t ht), sub_self] at h2
      exact h2
    have := constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    intro t ht
    have h := this t ht
    linarith
  refine ⟨hlevel, ?_⟩
  set g : ℝ → EuclideanSpace ℝ (Fin k) :=
    fun s => scaledNegativePart hk (γ s) - levelCutoff c ε (morseNormalForm hk c (γ s)) • z with hg
  have hγc : ContinuousOn γ (Icc t₀ t₁) := HasDerivAt.continuousOn hγ
  have hJcont : ContinuousOn (fun s => scaledNegativePart hk (γ s)) (Icc t₀ t₁) :=
    (continuous_scaledNegativePart hk).comp_continuousOn hγc
  have hBcont : ContinuousOn (fun s => levelCutoff c ε (morseNormalForm hk c (γ s))) (Icc t₀ t₁) :=
    ((contDiff_levelCutoff c ε).continuous.comp (contDiff_nf hk c).continuous).comp_continuousOn hγc
  have hgcont : ContinuousOn g (Icc t₀ t₁) := fun x hx =>
    (hJcont x hx).sub ((hBcont x hx).smul continuousWithinAt_const)
  have hSclosed : IsClosed ({s | g s = 0} ∩ Icc t₀ t₁) := by
    rw [inter_comm]
    exact hgcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hnormJ : ∀ s, g s = 0 → ‖scaledNegativePart hk (γ s)‖ ≤ ‖z‖ := by
    intro s hs
    have : scaledNegativePart hk (γ s) = levelCutoff c ε (morseNormalForm hk c (γ s)) • z := sub_eq_zero.1 hs
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (levelCutoff_nonneg _ _ _)]
    have := levelCutoff_le_one c ε (morseNormalForm hk c (γ s))
    have := norm_nonneg z
    nlinarith
  have hsubset : Icc t₀ t₁ ⊆ {s | g s = 0} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hSclosed ?_ ?_
    · change g t₀ = 0
      simp only [hg, hJ0, levelCutoff_eq_zero hε hnf0, zero_smul, sub_zero]
    · rintro x ⟨hx, hxI⟩
      have hx0 : g x = 0 := hx
      have hxIcc : x ∈ Icc t₀ t₁ := ⟨hxI.1, hxI.2.le⟩
      have hxlt : ‖scaledNegativePart hk (γ x)‖ < 2 * ρ := by linarith [hnormJ x hx0]
      have hIcc : Icc t₀ t₁ ∈ 𝓝[>] x :=
        Filter.mem_of_superset (Icc_mem_nhdsGT hxI.2) (Icc_subset_Icc hxI.1 le_rfl)
      have hev1 : ∀ᶠ s in 𝓝[>] x, ‖scaledNegativePart hk (γ s)‖ < 2 * ρ := by
        have h := ((hJcont.continuousWithinAt hxIcc).norm.tendsto).eventually
          (eventually_lt_nhds hxlt)
        exact h.filter_mono (nhdsWithin_le_of_mem hIcc)
      have hev2 : ∀ᶠ s in 𝓝[>] x, s ∈ Icc t₀ t₁ := hIcc
      obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev1.and hev2)
      refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨u, hu, fun s hs => ?_⟩
      have hs' := hIoo hs
      change g s = 0
      have hxs : x ≤ s := hs.1.le
      have hd : ∀ r ∈ Ico x s, HasDerivWithinAt g 0 (Ici r) r := by
        intro r hr
        have hrI : r ∈ Icc t₀ t₁ := ⟨hxI.1.trans hr.1, hr.2.le.trans hs'.2.2⟩
        have hαr : ‖scaledNegativePart hk (γ r)‖ ≤ 2 * ρ := by
          rcases hr.1.lt_or_eq with h | h
          · exact (hIoo ⟨h, hr.2.trans hs.2⟩).1.le
          · rw [← h]; exact hxlt.le
        refine (hasDerivAt_invariant hk hr₀ hε hρ (σ := -1) ?_ (hunit r hrI) (hpos r hrI)
          hαr).hasDerivWithinAt
        rw [neg_one_smul]; exact hγ r hrI
      have := constant_of_has_deriv_right_zero
        (hgcont.mono (Icc_subset_Icc hxIcc.1 hs'.2.2)) hd s (right_mem_Icc.2 hxs)
      rw [this, hx0]
  refine ⟨fun t ht => sub_eq_zero.1 (hsubset ht), fun t ht => hnormJ t (hsubset ht)⟩

theorem morseNorm_sq_le_of_scaledNegativePart_le {ε₀ η ρ : ℝ} (hε₀ : 0 < ε₀) {y : Fin n → ℝ}
    (h1 : 2 * ε₀ ≤ ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2)
    (h2 : ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2 ≤ 2 * η) (hJ : ‖scaledNegativePart hk y‖ ≤ ρ) :
    morseNorm n y ^ 2 ≤ 2 * η + ρ ^ 2 / ε₀ := by
  rw [norm_scaledNegativePart] at hJ
  rw [morseNorm_sq_eq_negPart_add_posPart hk]
  set a := ‖negPart hk y‖ with ha
  set b := ‖posPart hk y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hab : (b * a) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) hJ 2
  have hbε : 2 * ε₀ ≤ b ^ 2 := by nlinarith [sq_nonneg a]
  have haε : a ^ 2 * (2 * ε₀) ≤ ρ ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha' : a ^ 2 ≤ ρ ^ 2 / (2 * ε₀) := by rw [le_div_iff₀ (by positivity)]; exact haε
  have : ρ ^ 2 / ε₀ = 2 * (ρ ^ 2 / (2 * ε₀)) := by field_simp
  rw [this]
  nlinarith

theorem nf_sub_eq (c : ℝ) (y : Fin n → ℝ) :
    ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2 = 2 * (morseNormalForm hk c y - c) := by
  rw [morseNormalForm_split]; ring

end ModelField

namespace GradientLikeStrip

section Ascent

variable {D : GradientLikeStrip I f a b crit} {p : M} {hp : p ∈ crit} {η ρ : ℝ}
  {z : EuclideanSpace ℝ (Fin (D.chart p hp).k)} [T2Space M] [I.Boundaryless]
  (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
  (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
  (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η)

theorem hasDerivAt_symm_flow_twisted {x : M} {s : ℝ}
    (hs : (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s x ∈
      (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) :
    HasDerivAt (fun s => (D.chart p hp).χ.symm ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s x))
      (ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀
          ((D.chart p hp).χ.symm ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s x)) +
        ModelField.twist (D.chart p hp).hk (f p) η ρ z
          ((D.chart p hp).χ.symm ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s x))) s := by
  obtain ⟨y, hy, hxy⟩ := hs
  have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' :=
    mem_ball_of_morseNorm_lt ((show morseNorm n y < D.rm p hp from hy).trans (D.rm_lt_R' p hp))
  refine hasDerivAt_symm_flow_of_pullback (D := twisted (z := z) hf hη hρ hsupp hηrm hr₀η)
    (D.chart p hp) (Y := fun y => ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀ y +
      ModelField.twist (D.chart p hp).hk (f p) η ρ z y) ⟨y, hyb, hxy⟩ ?_
  rw [← hxy, (D.chart p hp).χ.left_inv ((D.chart p hp).hball hyb)]
  exact pullback_twistedV hy

theorem twisted_ascent {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀η : ε₀ ≤ η / 2)
    (hr₀ε₀ : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε₀) (hz : ‖z‖ ≤ ρ)
    (hB : 2 * η + ρ ^ 2 / ε₀ < D.rm p hp ^ 2)
    {y₀ : Fin n → ℝ} (hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk y₀ = 0)
    (hnf0 : morseNormalForm (D.chart p hp).hk (f p) y₀ = f p + ε₀) :
    ∀ s ∈ Icc (-(η - ε₀)) 0,
      (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s ((D.chart p hp).χ y₀) ∈
        (D.chart p hp).χ '' {y | morseNorm n y ^ 2 ≤ 2 * η + ρ ^ 2 / ε₀} ∧
      morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm
        ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s ((D.chart p hp).χ y₀))) =
          f p + ε₀ - s ∧
      ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm
        ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s ((D.chart p hp).χ y₀))) =
        ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm
          ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow s ((D.chart p hp).χ y₀)))) • z := by
  obtain ⟨Dt, hDt⟩ : ∃ Dt : GradientLikeStrip I f a b crit,
    twisted (z := z) hf hη hρ hsupp hηrm hr₀η = Dt := ⟨_, rfl⟩
  rw [hDt]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : M, (D.chart p hp).χ y₀ = x₀ := ⟨_, rfl⟩
  rw [hx₀]
  set B₀ := 2 * η + ρ ^ 2 / ε₀ with hB₀
  set S : Set (Fin n → ℝ) := {y | morseNorm n y ^ 2 ≤ B₀} with hS
  set O := (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hrm := D.rm_pos p hp
  have hrmR' := D.rm_lt_R' p hp
  have hSsub : S ⊆ {y | morseNorm n y < D.rm p hp} := fun y hy =>
    lt_of_pow_lt_pow_left₀ 2 hrm.le (lt_of_le_of_lt hy hB)
  have hSsub' : S ⊆ {y | morseNorm n y ≤ Real.sqrt B₀} := fun y hy =>
    MorseNormalChart.morseNorm_le_sqrt_of_sq_le hy
  have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset
      ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
      (((Real.sqrt_lt' hrm).2 hB).trans hrmR') hSsub'
  have hKO : (D.chart p hp).χ '' S ⊆ O := image_mono hSsub
  have hOball := D.modelBall_subset_image_ball p hp
  have hv₀ : posPart (D.chart p hp).hk y₀ ≠ 0 :=
    ModelField.posPart_ne_zero_of_lt_nf (D.chart p hp).hk (c := f p) (by rw [hnf0]; linarith)
  have hu₀ : negPart (D.chart p hp).hk y₀ = 0 := (ModelField.scaledNegativePart_eq_zero_iff (D.chart p hp).hk hv₀).1 hJ0
  have hy₀S : y₀ ∈ S := by
    change morseNorm n y₀ ^ 2 ≤ B₀
    have h1 := ModelField.nf_sub_eq (D.chart p hp).hk (f p) y₀
    rw [hnf0, hu₀, norm_zero] at h1
    rw [morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk, hu₀, norm_zero]
    have : 0 ≤ ρ ^ 2 / ε₀ := by positivity
    nlinarith
  have hγ0 : (D.chart p hp).χ.symm (Dt.flow 0 x₀) = y₀ := by
    rw [flow_zero, ← hx₀,
      (D.chart p hp).χ.left_inv ((D.chart p hp).hball (mem_ball_of_morseNorm_lt ((hSsub hy₀S).trans hrmR')))]
  have key : ∀ s', s' ≤ 0 → -(η - ε₀) ≤ s' → (∀ u ∈ Icc s' 0, Dt.flow u x₀ ∈ O) →
      ∀ s ∈ Icc s' 0,
        morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm (Dt.flow s x₀)) =
          f p + ε₀ - s ∧
        ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s x₀)) =
          ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk (f p)
            ((D.chart p hp).χ.symm (Dt.flow s x₀))) • z ∧
        ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s x₀))‖ ≤ ‖z‖ := by
    intro s' hs'0 hs'T hODE
    have hγ : ∀ t ∈ Icc 0 (-s'), HasDerivAt
        (fun t => (D.chart p hp).χ.symm (Dt.flow (-t) x₀))
        (-(ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀
            ((D.chart p hp).χ.symm (Dt.flow (-t) x₀)) +
          ModelField.twist (D.chart p hp).hk (f p) η ρ z
            ((D.chart p hp).χ.symm (Dt.flow (-t) x₀)))) t := by
      intro t ht
      have h := hasDerivAt_symm_flow_twisted hf hη hρ hsupp hηrm hr₀η (x := x₀) (s := -t)
        (by rw [hDt]; exact hODE (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      rw [hDt] at h
      exact ModelField.hasDerivAt_comp_neg'
        (F := fun y => ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀ y +
          ModelField.twist (D.chart p hp).hk (f p) η ρ z y) h
    have hγ0' : (D.chart p hp).χ.symm (Dt.flow (-0) x₀) = y₀ := by
      rw [neg_zero]; exact hγ0
    obtain ⟨h1, h2, h3⟩ := ModelField.ascending_twisted_curve' (D.chart p hp).hk (D.chart p hp).hr₀
      hη hρ hε₀ hr₀ε₀ hz (by linarith) hγ (by rw [hγ0']; exact hJ0) (by rw [hγ0', hnf0])
      (by rw [hγ0', hnf0]; linarith)
    intro s hs
    have hs1 : -s ∈ Icc 0 (-s') := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    refine ⟨?_, ?_, ?_⟩
    · have := h1 (-s) hs1
      simp only [neg_neg, hγ0', hnf0] at this
      rw [this]; ring
    · have := h2 (-s) hs1
      simpa only [neg_neg] using this
    · have := h3 (-s) hs1
      simpa only [neg_neg] using this
  have hbound : ∀ s, -(η - ε₀) ≤ s → s ≤ 0 →
      morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm (Dt.flow s x₀)) =
        f p + ε₀ - s →
      ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s x₀))‖ ≤ ‖z‖ →
      (D.chart p hp).χ.symm (Dt.flow s x₀) ∈ S := by
    intro s hs1 hs2 hnf hJ
    change morseNorm n _ ^ 2 ≤ B₀
    refine ModelField.morseNorm_sq_le_of_scaledNegativePart_le (D.chart p hp).hk hε₀ ?_ ?_ (hJ.trans hz)
    · rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p), hnf]; linarith
    · rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p), hnf]; linarith
  have hQc : IsClosed {s : ℝ | Dt.flow s x₀ ∈ (D.chart p hp).χ '' S} :=
    hSK.isClosed.preimage (Dt.continuous_flow_curve x₀)
  have hmain : Icc (-(η - ε₀)) 0 ⊆ {s | Dt.flow s x₀ ∈ (D.chart p hp).χ '' S} := by
    refine Icc_neg_subset_of_isClosed_of_step hQc ?_ ?_
    · change Dt.flow 0 x₀ ∈ (D.chart p hp).χ '' S
      rw [flow_zero, ← hx₀]; exact ⟨y₀, hy₀S, rfl⟩
    · intro t ht hIcc
      have htO : Dt.flow t x₀ ∈ O := hKO (hIcc (left_mem_Icc.2 ht.2))
      obtain ⟨δ, hδ, hδO⟩ := Dt.exists_Icc_flow_mem_open hOopen htO
      refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨max (t - δ) (-(η - ε₀)), ?_, fun s hs => ?_⟩
      · change max (t - δ) (-(η - ε₀)) < t
        exact max_lt (by linarith) ht.1
      change Dt.flow s x₀ ∈ (D.chart p hp).χ '' S
      have hs0 : s ≤ 0 := hs.2.le.trans ht.2
      have hsT : -(η - ε₀) ≤ s := (le_max_right _ _).trans hs.1
      have hODE : ∀ u ∈ Icc s 0, Dt.flow u x₀ ∈ O := fun u hu => by
        rcases le_or_gt t u with h | h
        · exact hKO (hIcc ⟨h, hu.2⟩)
        · exact hδO u ⟨(le_max_left _ _).trans (hs.1.trans hu.1), by linarith⟩
      obtain ⟨h1, -, h3⟩ := key s hs0 hsT hODE s (left_mem_Icc.2 hs0)
      exact (D.chart p hp).mem_image_of_symm_mem (hOball (hODE s (left_mem_Icc.2 hs0)))
        (hbound s hsT hs0 h1 h3)
  intro s hs
  have hODE : ∀ u ∈ Icc (-(η - ε₀)) 0, Dt.flow u x₀ ∈ O := fun u hu => hKO (hmain hu)
  obtain ⟨h1, h2, -⟩ := key _ (by linarith) le_rfl hODE s hs
  exact ⟨hmain hs, h1, h2⟩

theorem twisted_ascent_end {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀η : ε₀ ≤ η / 2)
    (hr₀ε₀ : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε₀) (hz : ‖z‖ ≤ ρ)
    (hB : 2 * η + ρ ^ 2 / ε₀ < D.rm p hp ^ 2)
    {y₀ : Fin n → ℝ} (hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk y₀ = 0)
    (hnf0 : morseNormalForm (D.chart p hp).hk (f p) y₀ = f p + ε₀) :
    (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow (-(η - ε₀)) ((D.chart p hp).χ y₀) ∈
        (D.chart p hp).χ '' {y | morseNorm n y ^ 2 ≤ 2 * η + ρ ^ 2 / ε₀} ∧
      morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm
        ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow (-(η - ε₀)) ((D.chart p hp).χ y₀))) =
          f p + η ∧
      ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm
        ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow (-(η - ε₀)) ((D.chart p hp).χ y₀))) = z := by
  obtain ⟨h1, h2, h3⟩ := twisted_ascent hf hη hρ hsupp hηrm hr₀η hε₀ hε₀η hr₀ε₀ hz hB hJ0 hnf0
    (-(η - ε₀)) (left_mem_Icc.2 (by linarith))
  have h2' : morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm
      ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow (-(η - ε₀)) ((D.chart p hp).χ y₀))) =
        f p + η := by rw [h2]; ring
  refine ⟨h1, h2', ?_⟩
  rw [h3, h2', ModelField.levelCutoff_eq_one hη le_rfl, one_smul]

omit [T2Space M] [I.Boundaryless] in
theorem twistY_eq_zero_of_notMem' (hη : 0 < η) (hρ : 0 < ρ) {y : Fin n → ℝ}
    (hy : y ∉ {y : Fin n → ℝ | morseNorm n y ≤ twistR η ρ ∧
      morseNormalForm (D.chart p hp).hk (f p) y < f p + η}) :
    twistY (D := D) p hp η ρ z y = 0 := by
  by_cases h1 : morseNorm n y ≤ twistR η ρ
  · have h2 : f p + η ≤ morseNormalForm (D.chart p hp).hk (f p) y := by
      by_contra h
      exact hy ⟨h1, not_le.1 h⟩
    exact ModelField.twist_eq_zero_of_nf_ge _ hη z h2
  · exact twistY_eq_zero_of_notMem hη hρ h1

omit [T2Space M] [I.Boundaryless] in
theorem twistedV_eq_of_level_ge (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) {x : M} (hx : f p + η ≤ f x) :
    twistedV (D := D) p hp η ρ z x = D.V x := by
  refine addPush_of_notMem_image p hp _ (fun _ hy => twistY_eq_zero_of_notMem' hη hρ hy) ?_
  rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
  have hyR : morseNorm n y ≤ (D.chart p hp).R := hy1.trans (twistR_lt_R hsupp).le
  rw [(D.chart p hp).hnorm y hyR] at hx
  linarith

omit [T2Space M] [I.Boundaryless] in
theorem twistedV_eq_of_level_le (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) {x : M} (hx : f x ≤ f p + η / 2) :
    twistedV (D := D) p hp η ρ z x = D.V x := by
  refine addPush_of_notMem_image p hp _ (K := {y : Fin n → ℝ | morseNorm n y ≤ twistR η ρ ∧
    f p + η / 2 < morseNormalForm (D.chart p hp).hk (f p) y}) (fun y hy => ?_) ?_
  · by_cases h1 : morseNorm n y ≤ twistR η ρ
    · have h2 : morseNormalForm (D.chart p hp).hk (f p) y ≤ f p + η / 2 := by
        by_contra h
        exact hy ⟨h1, not_le.1 h⟩
      exact ModelField.twist_eq_zero_of_nf_le _ hη z h2
    · exact twistY_eq_zero_of_notMem hη hρ h1
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    have hyR : morseNorm n y ≤ (D.chart p hp).R := hy1.trans (twistR_lt_R hsupp).le
    rw [(D.chart p hp).hnorm y hyR] at hx
    linarith

omit [T2Space M] in
theorem isOpen_above (hf : Continuous f) (t : ℝ) : IsOpen {x : M | t < f x} :=
  isOpen_lt continuous_const hf

theorem leftSphere_twisted (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) {q : M} (hq : q ∈ crit) {ε c : ℝ}
    (hε : 2 * ε ≤ (D.chart q hq).R ^ 2) (hc : f p + η < c) (hcq : c ≤ f q - ε) :
    (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).leftSphere q hq ε c = D.leftSphere q hq ε c := by
  unfold leftSphere
  rw [twisted_chart]
  refine image_congr fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hfy : f ((D.chart q hq).χ y) = f q - ε := (D.chart q hq).f_chart_of_mem_leftModelSphere hε hy
  refine flow_eq_of_agree (D₁ := D) (isOpen_above hf.continuous (f p + η))
    (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (fun s hs => ?_) _
    (right_mem_Icc.2 (by linarith))
  change f p + η < f (D.flow s ((D.chart q hq).χ y))
  have := sub_le_f_flow (D := D) hf ((D.chart q hq).χ y) hs.1
  rw [hfy] at this
  linarith [hs.2]

theorem rightSphere_twisted_subset (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) {ε c : ℝ} (hε : 0 < ε) (hεη : ε ≤ η / 2)
    (hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε) (hz : ‖z‖ ≤ ρ)
    (hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2) (hc : f p + η < c) (hcb : c ≤ b)
    (hlev : ∀ y, f y ∈ Icc (f p + η) c → ∀ p' hp', y ∉ D.smallBall p' hp') :
    (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).rightSphere p hp ε c ⊆
      D.flow (f p + η - c) '' ((D.chart p hp).χ ''
        {y | morseNorm n y ^ 2 ≤ 2 * η + ρ ^ 2 / ε ∧
          morseNormalForm (D.chart p hp).hk (f p) y = f p + η ∧
          ModelField.scaledNegativePart (D.chart p hp).hk y = z}) := by
  rintro _ ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩
  rw [twisted_chart] at hy₀ ⊢
  have hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk y₀ = 0 := by
    rw [ModelField.scaledNegativePart, hy₀.1, smul_zero]
  have hnf0 : morseNormalForm (D.chart p hp).hk (f p) y₀ = f p + ε :=
    (D.chart p hp).nf_of_mem_rightModelSphere hy₀
  obtain ⟨h1, h2, h3⟩ := twisted_ascent_end hf hη hρ hsupp hηrm hr₀η hε hεη hr₀ε hz hB hJ0 hnf0
  set w₀ := (twisted (z := z) hf hη hρ hsupp hηrm hr₀η).flow (-(η - ε)) ((D.chart p hp).χ y₀)
    with hw₀
  obtain ⟨y₁, hy₁, hy₁w⟩ := h1
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := by
    have := lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le
      (lt_of_le_of_lt (show morseNorm n y₁ ^ 2 ≤ _ from hy₁) hB)
    exact this.trans_le (D.hrm p hp).2
  have hsymm : (D.chart p hp).χ.symm w₀ = y₁ := by
    rw [← hy₁w, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R.le)]
  have hfw₀ : f w₀ = f p + η := by
    rw [← hy₁w, (D.chart p hp).hnorm y₁ hy₁R.le, ← hsymm]
    exact h2
  refine ⟨w₀, ⟨y₁, ⟨hy₁, ?_, ?_⟩, hy₁w⟩, ?_⟩
  · rw [← hsymm]; exact h2
  · rw [← hsymm]; exact h3
  have hw₀strip : f w₀ ∈ Icc a b := by
    rw [← hy₁w]
    have := D.inStrip p hp ⟨y₁, (D.chart p hp).mem_ball_of_le hy₁R.le, rfl⟩
    exact ⟨this.1.le, this.2.le⟩
  have hunit := f_flow_eq_sub_of_levels hf (D := D) (x := w₀) (T := f p + η - c) hw₀strip
    (by rw [hfw₀, sub_sub_cancel]; exact ⟨by linarith [hw₀strip.1], hcb⟩) (by
      intro y hy
      rw [hfw₀, sub_sub_cancel, uIcc_of_le (by linarith)] at hy
      exact hlev y hy)
  rw [uIcc_of_ge (by linarith)] at hunit
  have hagree := flow_eq_of_agree_neg (D₁ := D) (D₂ := twisted (z := z) hf hη hρ hsupp hηrm hr₀η)
    (isOpen_above hf.continuous (f p + η))
    (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (x := w₀)
    (T := c - (f p + η)) (by linarith) (fun s hs => by
      change f p + η < f (D.flow s w₀)
      rw [hunit s ⟨by linarith [hs.1], hs.2.le⟩, hfw₀]
      linarith [hs.2])
  have := hagree (f p + η - c) ⟨by linarith, by linarith⟩
  rw [← this, hw₀, flow_flow]
  congr 1
  ring

end Ascent

end GradientLikeStrip

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {q : M} (e : MorseNormalChart I f q)

def toE (w : Fin e.k → ℝ) : EuclideanSpace ℝ (Fin e.k) := (EuclideanSpace.equiv (Fin e.k) ℝ).symm w

def sphereParam (ε : ℝ) (w : Fin e.k → ℝ) : Fin n → ℝ :=
  recombine e.hk ((Real.sqrt (2 * ε) / ‖e.toE w‖) • e.toE w) 0

theorem toE_ne_zero {w : Fin e.k → ℝ} (hw : w ≠ 0) : e.toE w ≠ 0 := by
  intro h
  exact hw ((EuclideanSpace.equiv (Fin e.k) ℝ).symm.map_eq_zero_iff.1 h)

theorem contDiff_toE : ContDiff ℝ ∞ e.toE := (EuclideanSpace.equiv (Fin e.k) ℝ).symm.contDiff

theorem negPart_sphereParam (ε : ℝ) (w : Fin e.k → ℝ) :
    negPart e.hk (e.sphereParam ε w) = (Real.sqrt (2 * ε) / ‖e.toE w‖) • e.toE w :=
  ModelField.negPart_recombine e.hk _ _

theorem posPart_sphereParam (ε : ℝ) (w : Fin e.k → ℝ) : posPart e.hk (e.sphereParam ε w) = 0 :=
  ModelField.posPart_recombine e.hk _ _

theorem sphereParam_mem_leftModelSphere {ε : ℝ} (hε : 0 ≤ ε) {w : Fin e.k → ℝ} (hw : w ≠ 0) :
    e.sphereParam ε w ∈ e.leftModelSphere ε := by
  refine ⟨e.posPart_sphereParam ε w, ?_⟩
  rw [e.negPart_sphereParam, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
    Real.sq_sqrt (by linarith)]
  have h : ‖e.toE w‖ ≠ 0 := norm_ne_zero_iff.2 (e.toE_ne_zero hw)
  field_simp

theorem sphereParam_of_mem {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ} (hy : y ∈ e.leftModelSphere ε) :
    (EuclideanSpace.equiv (Fin e.k) ℝ) (negPart e.hk y) ≠ 0 ∧
      e.sphereParam ε ((EuclideanSpace.equiv (Fin e.k) ℝ) (negPart e.hk y)) = y := by
  have hu : negPart e.hk y ≠ 0 := by
    intro h
    have := hy.2
    rw [h, norm_zero] at this
    nlinarith
  have htoE : e.toE ((EuclideanSpace.equiv (Fin e.k) ℝ) (negPart e.hk y)) = negPart e.hk y :=
    (EuclideanSpace.equiv (Fin e.k) ℝ).symm_apply_apply _
  refine ⟨fun h => hu ((EuclideanSpace.equiv (Fin e.k) ℝ).map_eq_zero_iff.1 h), ?_⟩
  have hnorm : ‖negPart e.hk y‖ = Real.sqrt (2 * ε) := by
    rw [← hy.2, Real.sqrt_sq (norm_nonneg _)]
  rw [sphereParam, htoE, hnorm, div_self (Real.sqrt_ne_zero'.2 (by linarith)), one_smul, ← hy.1,
    recombine_decompose]

theorem contDiffAt_sphereParam (ε : ℝ) {w : Fin e.k → ℝ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (e.sphereParam ε) w := by
  have heq : e.sphereParam ε = fun w =>
      ModelField.recombineL e.hk ((Real.sqrt (2 * ε) / ‖e.toE w‖) • e.toE w, 0) :=
    funext fun w => (ModelField.recombineL_apply _ _ _).symm
  rw [heq]
  have htoE : ContDiffAt ℝ ∞ e.toE w := e.contDiff_toE.contDiffAt
  have hnorm : ContDiffAt ℝ ∞ (fun w => ‖e.toE w‖) w := htoE.norm ℝ (e.toE_ne_zero hw)
  have h1 : ContDiffAt ℝ ∞ (fun w => (Real.sqrt (2 * ε) / ‖e.toE w‖) • e.toE w) w :=
    (contDiffAt_const.div hnorm (norm_ne_zero_iff.2 (e.toE_ne_zero hw))).smul htoE
  exact (ModelField.recombineL e.hk).contDiff.contDiffAt.comp w (h1.prodMk contDiffAt_const)

theorem morseNorm_sphereParam_le {ε : ℝ} (hε : 0 ≤ ε) (hεR : 2 * ε ≤ e.R ^ 2) {w : Fin e.k → ℝ}
    (hw : w ≠ 0) : morseNorm n (e.sphereParam ε w) ≤ e.R :=
  e.morseNorm_le_R_of_mem_leftModelSphere hεR (e.sphereParam_mem_leftModelSphere hε hw)

theorem exists_near_rightModelSphere {p : M} (d : MorseNormalChart I f p) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) {y : Fin n → ℝ} (hnf : morseNormalForm d.hk (f p) y = f p + ε)
    (hu : ‖negPart d.hk y‖ ^ 2 ≤ δ) :
    ∃ y₀ ∈ d.rightModelSphere ε, morseNorm n (y - y₀) ^ 2 ≤ δ + δ ^ 2 / (2 * ε) := by
  have hv2 : ‖posPart d.hk y‖ ^ 2 = 2 * ε + ‖negPart d.hk y‖ ^ 2 := by
    have := ModelField.nf_sub_eq d.hk (f p) y
    rw [hnf] at this
    linarith
  set s := Real.sqrt (2 * ε) with hs
  have hs2 : s ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set t := ‖posPart d.hk y‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hts : s ≤ t := by nlinarith [sq_nonneg ‖negPart d.hk y‖]
  have htpos : 0 < t := hs0.trans_le hts
  refine ⟨recombine d.hk 0 ((s / t) • posPart d.hk y), ⟨ModelField.negPart_recombine _ _ _, ?_⟩, ?_⟩
  · rw [ModelField.posPart_recombine, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      mul_pow, div_pow, ← ht, hs2]
    field_simp
  · have hneg : negPart d.hk (y - recombine d.hk 0 ((s / t) • posPart d.hk y)) = negPart d.hk y := by
      rw [← ModelField.negPartL_apply, map_sub, ModelField.negPartL_apply, ModelField.negPartL_apply,
        ModelField.negPart_recombine, sub_zero]
    have hpos : posPart d.hk (y - recombine d.hk 0 ((s / t) • posPart d.hk y)) =
        (1 - s / t) • posPart d.hk y := by
      rw [← ModelField.posPartL_apply, map_sub, ModelField.posPartL_apply, ModelField.posPartL_apply,
        ModelField.posPart_recombine, sub_smul, one_smul]
    rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hneg, hpos, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, ← ht]
    have h1 : (1 - s / t) ^ 2 * t ^ 2 = (t - s) ^ 2 := by field_simp
    rw [h1]
    have h2 : (t - s) * s ≤ δ := by nlinarith
    have h3 : (t - s) ^ 2 ≤ δ ^ 2 / (2 * ε) := by
      rw [le_div_iff₀ (by linarith), ← hs2]
      have h2' : ((t - s) * s) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (mul_nonneg (by linarith) hs0.le) h2 2
      rw [mul_pow] at h2'
      exact h2'
    linarith

theorem exists_near_leftModelSphere {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) {y : Fin n → ℝ} (hnf : morseNormalForm e.hk (f q) y = f q - ε)
    (hv : ‖posPart e.hk y‖ ^ 2 ≤ δ) :
    ∃ y₀ ∈ e.leftModelSphere ε, morseNorm n (y - y₀) ^ 2 ≤ δ + δ ^ 2 / (2 * ε) := by
  have hu2 : ‖negPart e.hk y‖ ^ 2 = 2 * ε + ‖posPart e.hk y‖ ^ 2 := by
    have := ModelField.nf_sub_eq e.hk (f q) y
    rw [hnf] at this
    linarith
  set s := Real.sqrt (2 * ε) with hs
  have hs2 : s ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set t := ‖negPart e.hk y‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hts : s ≤ t := by nlinarith [sq_nonneg ‖posPart e.hk y‖]
  have htpos : 0 < t := hs0.trans_le hts
  refine ⟨recombine e.hk ((s / t) • negPart e.hk y) 0, ⟨ModelField.posPart_recombine _ _ _, ?_⟩, ?_⟩
  · rw [ModelField.negPart_recombine, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      mul_pow, div_pow, ← ht, hs2]
    field_simp
  · have hpos : posPart e.hk (y - recombine e.hk ((s / t) • negPart e.hk y) 0) = posPart e.hk y := by
      rw [← ModelField.posPartL_apply, map_sub, ModelField.posPartL_apply, ModelField.posPartL_apply,
        ModelField.posPart_recombine, sub_zero]
    have hneg : negPart e.hk (y - recombine e.hk ((s / t) • negPart e.hk y) 0) =
        (1 - s / t) • negPart e.hk y := by
      rw [← ModelField.negPartL_apply, map_sub, ModelField.negPartL_apply, ModelField.negPartL_apply,
        ModelField.negPart_recombine, sub_smul, one_smul]
    rw [morseNorm_sq_eq_negPart_add_posPart e.hk, hneg, hpos, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, ← ht]
    have h1 : (1 - s / t) ^ 2 * t ^ 2 = (t - s) ^ 2 := by field_simp
    rw [h1]
    have h2 : (t - s) * s ≤ δ := by nlinarith
    have h3 : (t - s) ^ 2 ≤ δ ^ 2 / (2 * ε) := by
      rw [le_div_iff₀ (by linarith), ← hs2]
      have h2' : ((t - s) * s) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (mul_nonneg (by linarith) hs0.le) h2 2
      rw [mul_pow] at h2'
      exact h2'
    linarith

end MorseNormalChart

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless] (D : GradientLikeStrip I f a b crit)

def rightTube (p : M) (hp : p ∈ crit) (ε δ : ℝ) : Set (Fin n → ℝ) :=
  {y | morseNormalForm (D.chart p hp).hk (f p) y = f p + ε ∧ ‖negPart (D.chart p hp).hk y‖ ^ 2 ≤ δ}

def leftTube (q : M) (hq : q ∈ crit) (ε δ : ℝ) : Set (Fin n → ℝ) :=
  {y | morseNormalForm (D.chart q hq).hk (f q) y = f q - ε ∧ ‖posPart (D.chart q hq).hk y‖ ^ 2 ≤ δ}

theorem exists_tube_disjoint (p : M) (hp : p ∈ crit) (q : M) (hq : q ∈ crit) {ε c : ℝ}
    (hε : 0 < ε) (hεp : 2 * ε ≤ (D.chart p hp).R ^ 2) (hεq : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (hdisj : Disjoint (D.rightSphere p hp ε c) (D.leftSphere q hq ε c)) :
    ∃ δ, 0 < δ ∧ Disjoint (D.flow (f p + ε - c) '' ((D.chart p hp).χ '' D.rightTube p hp ε δ))
      (D.flow (f q - ε - c) '' ((D.chart q hq).χ '' D.leftTube q hq ε δ)) := by
  obtain ⟨U, V, hU, hV, hSU, hSV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (D.isCompact_rightSphere p hp hεp c) (D.isCompact_leftSphere q hq hεq c) hdisj
  have hΦR : ContinuousOn (fun y => D.flow (f p + ε - c) ((D.chart p hp).χ y))
      (Metric.ball 0 (D.chart p hp).R') :=
    (D.continuous_flow _).comp_continuousOn ((D.chart p hp).χ.continuousOn.mono (D.chart p hp).hball)
  have hΦL : ContinuousOn (fun y => D.flow (f q - ε - c) ((D.chart q hq).χ y))
      (Metric.ball 0 (D.chart q hq).R') :=
    (D.continuous_flow _).comp_continuousOn ((D.chart q hq).χ.continuousOn.mono (D.chart q hq).hball)
  have hWR : IsOpen (Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' ∩
      (fun y => D.flow (f p + ε - c) ((D.chart p hp).χ y)) ⁻¹' U) :=
    hΦR.isOpen_inter_preimage Metric.isOpen_ball hU
  have hWL : IsOpen (Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' ∩
      (fun y => D.flow (f q - ε - c) ((D.chart q hq).χ y)) ⁻¹' V) :=
    hΦL.isOpen_inter_preimage Metric.isOpen_ball hV
  have hSR : (D.chart p hp).rightModelSphere ε ⊆ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' ∩
      (fun y => D.flow (f p + ε - c) ((D.chart p hp).χ y)) ⁻¹' U := fun y hy =>
    ⟨(D.chart p hp).mem_ball_of_le ((D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere hεp hy),
      hSU ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩
  have hSL : (D.chart q hq).leftModelSphere ε ⊆ Metric.ball (0 : Fin n → ℝ) (D.chart q hq).R' ∩
      (fun y => D.flow (f q - ε - c) ((D.chart q hq).χ y)) ⁻¹' V := fun y hy =>
    ⟨(D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hεq hy),
      hSV ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩
  obtain ⟨η₁, hη₁, hthR⟩ := ((D.chart p hp).isCompact_rightModelSphere ε).exists_thickening_subset_open
    hWR hSR
  obtain ⟨η₂, hη₂, hthL⟩ := ((D.chart q hq).isCompact_leftModelSphere ε).exists_thickening_subset_open
    hWL hSL
  set η := min η₁ η₂ with hη
  have hηpos : 0 < η := lt_min hη₁ hη₂
  set δ := min 1 (η ^ 2 * ε / (2 * ε + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ η ^ 2 * ε / (2 * ε + 1) := min_le_right _ _
  have hkey : δ + δ ^ 2 / (2 * ε) < η ^ 2 := by
    have h1 : δ ^ 2 ≤ δ := by nlinarith
    have h2 : δ * (2 * ε + 1) ≤ η ^ 2 * ε := by
      rw [le_div_iff₀ (by positivity)] at hδ2; exact hδ2
    have h3 : δ + δ ^ 2 / (2 * ε) ≤ δ + δ / (2 * ε) := by
      gcongr
    have h4 : δ + δ / (2 * ε) = δ * (2 * ε + 1) / (2 * ε) := by field_simp
    have h5 : δ * (2 * ε + 1) / (2 * ε) ≤ η ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h6 : 0 < η ^ 2 := by positivity
    linarith
  refine ⟨δ, hδpos, ?_⟩
  have hR : D.flow (f p + ε - c) '' ((D.chart p hp).χ '' D.rightTube p hp ε δ) ⊆ U := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨y₀, hy₀, hyy₀⟩ := (D.chart p hp).exists_near_rightModelSphere hε hδpos.le hy.1 hy.2
    have hdist : dist y y₀ < η₁ := by
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (morseNorm_piNorm_le (y - y₀)) (lt_of_lt_of_le ?_ (min_le_left η₁ η₂))
      exact lt_of_pow_lt_pow_left₀ 2 hηpos.le (hyy₀.trans_lt hkey)
    exact (hthR (Metric.mem_thickening_iff.2 ⟨y₀, hy₀, hdist⟩)).2
  have hL : D.flow (f q - ε - c) '' ((D.chart q hq).χ '' D.leftTube q hq ε δ) ⊆ V := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨y₀, hy₀, hyy₀⟩ := (D.chart q hq).exists_near_leftModelSphere hε hδpos.le hy.1 hy.2
    have hdist : dist y y₀ < η₂ := by
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (morseNorm_piNorm_le (y - y₀)) (lt_of_lt_of_le ?_ (min_le_right η₁ η₂))
      exact lt_of_pow_lt_pow_left₀ 2 hηpos.le (hyy₀.trans_lt hkey)
    exact (hthL (Metric.mem_thickening_iff.2 ⟨y₀, hy₀, hdist⟩)).2
  exact hUV.mono hR hL

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_Ioo (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) :
    f p ∈ Ioo a b :=
  D.inStrip p hp (D.chart p hp).p_mem_image_ball

section Sard

variable (p : M) {q : M} (hq : q ∈ crit) (ε c η : ℝ)

def landing (w : Fin (D.chart q hq).k → ℝ) : M :=
  D.flow (c - (f p + η)) (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))

variable (hp : p ∈ crit)

def sardMap (w : Fin (D.chart q hq).k → ℝ) : EuclideanSpace ℝ (Fin (D.chart p hp).k) :=
  ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c η w))

def sardDom : Set (Fin (D.chart q hq).k → ℝ) :=
  {w | w ≠ 0} ∩ D.landing p hq ε c η ⁻¹' ((D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R})

variable {D p hq ε c η hp}

theorem continuousOn_landing (hε : 0 ≤ ε) (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) :
    ContinuousOn (D.landing p hq ε c η) {w | w ≠ 0} := by
  intro w hw
  have h1 : ContinuousAt ((D.chart q hq).sphereParam ε) w :=
    ((D.chart q hq).contDiffAt_sphereParam ε hw).continuousAt
  have hmem : (D.chart q hq).sphereParam ε w ∈ (D.chart q hq).χ.source :=
    (D.chart q hq).hsrc _ ((D.chart q hq).morseNorm_sphereParam_le hε hεR hw)
  have h2 : ContinuousAt (D.chart q hq).χ ((D.chart q hq).sphereParam ε w) :=
    (D.chart q hq).χ.continuousAt hmem
  exact ((D.continuous_flow _).continuousAt.comp
    ((D.continuous_flow _).continuousAt.comp (h2.comp h1))).continuousWithinAt

theorem isOpen_sardDom (hε : 0 ≤ ε) (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) :
    IsOpen (D.sardDom p hq ε c η hp) :=
  (continuousOn_landing hε hεR).isOpen_inter_preimage isOpen_ne
    ((D.chart p hp).isOpen_image_of_lt (D.chart p hp).hRR'.le)

theorem f_landing (hp : p ∈ crit) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hε : 0 < ε) (hη : 0 < η)
    (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) (hηc : f p + η ≤ c) (hcq : c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    {w : Fin (D.chart q hq).k → ℝ} (hw : w ≠ 0) : f (D.landing p hq ε c η w) = f p + η := by
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  set x₁ := (D.chart q hq).χ ((D.chart q hq).sphereParam ε w) with hx₁
  have hfx₁ : f x₁ = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hεR
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw)
  have h1 : f (D.flow (f q - ε - c) x₁) = c := by
    have := f_flow_eq_sub_of_levels hf (D := D) (x := x₁) (T := f q - ε - c)
      (by rw [hfx₁]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfx₁, sub_sub_cancel]; exact ⟨by linarith, by linarith⟩) (by
        intro y hy
        rw [hfx₁, sub_sub_cancel, uIcc_of_ge hcq] at hy
        exact hlev y ⟨by linarith [hy.1], hy.2⟩) _ right_mem_uIcc
    rw [this, hfx₁]; ring
  have h2 := f_flow_eq_sub_of_levels hf (D := D) (x := D.flow (f q - ε - c) x₁)
    (T := c - (f p + η)) (by rw [h1]; exact ⟨by linarith, by linarith⟩)
    (by rw [h1, sub_sub_cancel]; exact ⟨by linarith, by linarith⟩) (by
      intro y hy
      rw [h1, sub_sub_cancel, uIcc_of_ge hηc] at hy
      exact hlev y ⟨hy.1, by linarith [hy.2]⟩) _ right_mem_uIcc
  change f (D.flow (c - (f p + η)) (D.flow (f q - ε - c) x₁)) = f p + η
  rw [h2, h1]; ring

theorem differentiableOn_sardMap (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hε : 0 < ε) (hη : 0 < η)
    (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) (hηc : f p + η ≤ c) (hcq : c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    DifferentiableOn ℝ (D.sardMap p hq ε c η hp) (D.sardDom p hq ε c η hp) := by
  rintro w ⟨hw0, hland⟩
  have hw0' : w ≠ 0 := hw0
  have hland' : D.landing p hq ε c η w ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
    (D.chart p hp).image_lt_subset_image_ball (D.chart p hp).hRR'.le hland
  have hv : posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c η w)) ≠ 0 := by
    apply ModelField.posPart_ne_zero_of_lt_nf (D.chart p hp).hk (c := f p)
    have hland2 : D.landing p hq ε c η w ∈ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).R} :=
      image_mono (fun y (hy : morseNorm n y < (D.chart p hp).R) => le_of_lt hy) hland
    rw [← (D.chart p hp).f_eq_nf_symm hland2, f_landing hp hf hε hη hεR hηc hcq hlev hw0']
    linarith
  have hsp : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      ((D.chart q hq).sphereParam ε) w :=
    contMDiffAt_iff_contDiffAt.2 ((D.chart q hq).contDiffAt_sphereParam ε hw0')
  have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart q hq).χ ((D.chart q hq).sphereParam ε w) :=
    (D.chart q hq).contMDiffAt_chart
      ((D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hεR hw0'))
  have hfl1 : ContMDiffAt I I ∞ (D.flow (f q - ε - c))
      ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := (D.contMDiff_flow _).contMDiffAt
  have hfl2 : ContMDiffAt I I ∞ (D.flow (c - (f p + η)))
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) :=
    (D.contMDiff_flow _).contMDiffAt
  have hsymm : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (D.chart p hp).χ.symm
      (D.flow (c - (f p + η)) (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))) :=
    (D.chart p hp).contMDiffAt_symm hland'
  have hJ : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) ∞
      (ModelField.scaledNegativePart (D.chart p hp).hk) ((D.chart p hp).χ.symm
        (D.flow (c - (f p + η)) (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))))) :=
    contMDiffAt_iff_contDiffAt.2 (ModelField.contDiffAt_scaledNegativePart _ hv)
  have c1 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
      (fun w => (D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) w := hχq.comp w hsp
  have c2 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
      (fun w => D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) w :=
    hfl1.comp w c1
  have c3 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
      (fun w => D.flow (c - (f p + η))
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))) w :=
    hfl2.comp w c2
  have c4 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun w => (D.chart p hp).χ.symm (D.flow (c - (f p + η))
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))))) w :=
    hsymm.comp w c3
  have c5 := hJ.comp w c4
  have c6 := (contMDiffAt_iff_contDiffAt.1 c5).differentiableAt (by simp)
  exact c6.differentiableWithinAt

theorem exists_sard_z (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hε : 0 < ε) (hη : 0 < η)
    (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2) (hηc : f p + η ≤ c) (hcq : c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    (hlt : (D.chart q hq).k < (D.chart p hp).k) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖z‖ < ρ ∧
      z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp := by
  obtain ⟨z, hz, hz'⟩ := ModelField.exists_avoid_image_euclidean hlt
    (differentiableOn_sardMap hf hε hη hεR hηc hcq hlev) 0 hρ
  exact ⟨z, by simpa using hz, hz'⟩

end Sard

section Disjoint

variable {D} {p : M} {hp : p ∈ crit} {η ρ : ℝ} {z : EuclideanSpace ℝ (Fin (D.chart p hp).k)}
  (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hη : 0 < η) (hρ : 0 < ρ)
  (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
  (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η)

theorem disjoint_spheres_twisted {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hεη : ε ≤ η / 2)
    (hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε) (hz : ‖z‖ ≤ ρ)
    (hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2) (hεq : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (hc : f p + η < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    (hzF : z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp) :
    Disjoint ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).rightSphere p hp ε c)
      ((twisted (z := z) hf hη hρ hsupp hηrm hr₀η).leftSphere q hq ε c) := by
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  rw [leftSphere_twisted hf hη hρ hsupp hηrm hr₀η hq hεq hc hcq.le]
  refine Set.disjoint_left.2 fun x hxR hxL => ?_
  have hxR' := rightSphere_twisted_subset hf hη hρ hsupp hηrm hr₀η hε hεη hr₀ε hz hB hc
    (by linarith) (fun y hy => hlev y ⟨hy.1, by linarith [hy.2]⟩) hxR
  obtain ⟨_, ⟨y₁, ⟨hy₁S, hy₁nf, hy₁J⟩, rfl⟩, rfl⟩ := hxR'
  obtain ⟨_, ⟨y₂, hy₂, rfl⟩, hx⟩ := hxL
  obtain ⟨hw0, hsp⟩ := (D.chart q hq).sphereParam_of_mem hε hy₂
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := by
    have := lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le
      (lt_of_le_of_lt (show morseNorm n y₁ ^ 2 ≤ _ from hy₁S) hB)
    exact this.trans_le (D.hrm p hp).2
  have hland : D.landing p hq ε c η ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ)
      (negPart (D.chart q hq).hk y₂)) = (D.chart p hp).χ y₁ := by
    unfold landing
    rw [hsp, hx, flow_flow, show f p + η - c + (c - (f p + η)) = 0 by ring, flow_zero]
  apply hzF
  refine ⟨_, ⟨hw0, ?_⟩, ?_⟩
  · change D.landing p hq ε c η _ ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hland]
    exact ⟨y₁, hy₁R, rfl⟩
  · unfold sardMap
    rw [hland, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R.le)]
    exact hy₁J

end Disjoint

section Levels

variable {D}

theorem sub_mem_uIcc_of_mem_uIcc {ℓ T s : ℝ} (hs : s ∈ uIcc 0 T) : ℓ - s ∈ uIcc ℓ (ℓ - T) := by
  rw [mem_uIcc] at hs ⊢
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

theorem flow_eq_of_agree_levels {D₁ D₂ : GradientLikeStrip I f a b crit}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ℓ c : ℝ} (hℓ : ℓ ∈ Icc a b) (hc : c ∈ Icc a b)
    (hunit : ∀ y, f y ∈ uIcc ℓ c → ∀ p hp, y ∉ D₁.smallBall p hp) {U : Set M} (hUo : IsOpen U)
    (hV : ∀ x ∈ U, D₁.V x = D₂.V x) (hU : ∀ y, f y ∈ uIcc ℓ c → y ∈ U) {x : M} (hx : f x = ℓ) :
    D₂.flow (ℓ - c) x = D₁.flow (ℓ - c) x := by
  have hlev := f_flow_eq_sub_of_levels hf (D := D₁) (x := x) (T := ℓ - c) (by rw [hx]; exact hℓ)
    (by rw [hx, sub_sub_cancel]; exact hc) (by rw [hx, sub_sub_cancel]; exact hunit)
  have hmem : ∀ s ∈ uIcc 0 (ℓ - c), D₁.flow s x ∈ U := fun s hs => by
    apply hU
    rw [hlev s hs, hx]
    have := sub_mem_uIcc_of_mem_uIcc (ℓ := ℓ) hs
    rwa [sub_sub_cancel] at this
  rcases le_or_gt 0 (ℓ - c) with h | h
  · rw [uIcc_of_le h] at hmem
    exact flow_eq_of_agree hUo hV (fun s hs => hmem s (Ico_subset_Icc_self hs)) _
      (right_mem_Icc.2 h)
  · rw [uIcc_of_ge h.le] at hmem
    have := flow_eq_of_agree_neg hUo hV (T := c - ℓ) (by linarith)
      (fun s hs => hmem s ⟨by linarith [hs.1], hs.2.le⟩) (ℓ - c) ⟨by linarith, by linarith⟩
    exact this

theorem flow_image_eq_of_agree_levels {D₁ D₂ : GradientLikeStrip I f a b crit}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ℓ c : ℝ} (hℓ : ℓ ∈ Icc a b) (hc : c ∈ Icc a b)
    (hunit : ∀ y, f y ∈ uIcc ℓ c → ∀ p hp, y ∉ D₁.smallBall p hp) {U : Set M} (hUo : IsOpen U)
    (hV : ∀ x ∈ U, D₁.V x = D₂.V x) (hU : ∀ y, f y ∈ uIcc ℓ c → y ∈ U) {K : Set M}
    (hK : ∀ x ∈ K, f x = ℓ) : D₂.flow (ℓ - c) '' K = D₁.flow (ℓ - c) '' K :=
  image_congr fun x hx => flow_eq_of_agree_levels hf hℓ hc hunit hUo hV hU (hK x hx)

end Levels

section ShrinkLevels

variable {D} {p : M} {hp : p ∈ crit} {r₀' : ℝ}

omit [T2Space M] [I.Boundaryless] in
theorem shrunkV_eq_of_level (hr₀' : 0 < r₀') (hle : r₀' ≤ (D.chart p hp).r₀) {ε₁ : ℝ}
    (hε₁ : (D.chart p hp).r₀ ^ 2 < 8 * ε₁) {x : M} (hx : f p + ε₁ ≤ f x ∨ f x ≤ f p - ε₁) :
    shrunkV (D := D) p hp r₀' x = D.V x := by
  refine shrunkV_of_notMem_image hr₀' hle ?_
  rintro ⟨y, hy, rfl⟩
  have hyR : morseNorm n y ≤ (D.chart p hp).R := by
    have := (D.chart p hp).hr₀R
    have := (D.chart p hp).hr₀
    linarith [show morseNorm n y ≤ _ from hy]
  have hy2 : morseNorm n y ^ 2 ≤ (D.chart p hp).r₀ ^ 2 / 4 := by
    have := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) (show morseNorm n y ≤ _ from hy) 2
    linarith [this]
  rw [(D.chart p hp).hnorm y hyR, morseNormalForm_split] at hx
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk y
  have h1 := sq_nonneg ‖negPart (D.chart p hp).hk y‖
  have h2 := sq_nonneg ‖posPart (D.chart p hp).hk y‖
  rcases hx with hx | hx <;> nlinarith

omit [I.Boundaryless] in
theorem smallBall_shrinkAt_subset (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hr₀' : 0 < r₀')
    (hle : r₀' ≤ (D.chart p hp).r₀) (q : M) (hq : q ∈ crit) :
    (shrinkAt hf hr₀' hle).smallBall q hq ⊆ D.smallBall q hq := by
  unfold smallBall
  rw [shrinkAt_chart_χ]
  refine image_mono fun y hy => ?_
  change morseNorm n y < (D.chart q hq).r₀
  by_cases h : q = p
  · subst h
    rw [shrinkAt_chart_r₀_self] at hy
    exact lt_of_lt_of_le hy hle
  · rwa [shrinkAt_chart_r₀_of_ne hf hr₀' hle hq h] at hy

end ShrinkLevels

section ShrinkTwo

variable {D}

omit [I.Boundaryless] in
theorem hle₂' (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (_hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) : r₂ ≤ ((shrinkAt hf hr₁ hle₁).chart q hq).r₀ := by
  rw [shrinkAt_chart_r₀_of_ne hf hr₁ hle₁ hq hpq]; exact hle₂

def shrink₂ (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) : GradientLikeStrip I f a b crit :=
  shrinkAt (D := shrinkAt hf hr₁ hle₁) hf hr₂ (hle₂' hf hp hq hpq hr₁ hle₁ hr₂ hle₂)

omit [I.Boundaryless] in
@[simp] theorem shrink₂_chart_χ (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) (q' : M) (hq' : q' ∈ crit) :
    ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q' hq').χ = (D.chart q' hq').χ := rfl

omit [I.Boundaryless] in
@[simp] theorem shrink₂_chart_k (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) (q' : M) (hq' : q' ∈ crit) :
    ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q' hq').k = (D.chart q' hq').k := rfl

omit [I.Boundaryless] in
@[simp] theorem shrink₂_chart_R (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) (q' : M) (hq' : q' ∈ crit) :
    ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q' hq').R = (D.chart q' hq').R := rfl

omit [I.Boundaryless] in
@[simp] theorem shrink₂_chart_R' (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) (q' : M) (hq' : q' ∈ crit) :
    ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q' hq').R' = (D.chart q' hq').R' := rfl

omit [I.Boundaryless] in
@[simp] theorem shrink₂_rm (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) : (shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).rm = D.rm := rfl

omit [I.Boundaryless] in
theorem shrink₂_r₀_p (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) : ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart p hp).r₀ = r₁ := by
  unfold shrink₂
  rw [shrinkAt_chart_r₀_of_ne hf hr₂ _ hp (Ne.symm hpq), shrinkAt_chart_r₀_self]

omit [I.Boundaryless] in
theorem shrink₂_r₀_q (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) : ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q hq).r₀ = r₂ := by
  unfold shrink₂
  rw [shrinkAt_chart_r₀_self]

omit [I.Boundaryless] in
theorem shrink₂_r₀_of_ne (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) {q' : M} (hq' : q' ∈ crit) (h1 : q' ≠ p) (h2 : q' ≠ q) :
    ((shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).chart q' hq').r₀ = (D.chart q' hq').r₀ := by
  unfold shrink₂
  rw [shrinkAt_chart_r₀_of_ne hf hr₂ _ hq' h2, shrinkAt_chart_r₀_of_ne hf hr₁ hle₁ hq' h1]

omit [I.Boundaryless] in
theorem smallBall_shrink₂_subset (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) (q' : M) (hq' : q' ∈ crit) :
    (shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).smallBall q' hq' ⊆ D.smallBall q' hq' :=
  (smallBall_shrinkAt_subset hf hr₂ _ q' hq').trans (smallBall_shrinkAt_subset hf hr₁ hle₁ q' hq')

omit [I.Boundaryless] in
theorem shrink₂_V_eq (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) {ε : ℝ} (hεp : (D.chart p hp).r₀ ^ 2 < 4 * ε)
    (hεq : (D.chart q hq).r₀ ^ 2 < 4 * ε) {x : M} (hx1 : f p + ε / 2 ≤ f x)
    (hx2 : f x ≤ f q - ε / 2) : (shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).V x = D.V x := by
  unfold shrink₂
  rw [shrinkAt_V, shrunkV_eq_of_level hr₂ (hle₂' hf hp hq hpq hr₁ hle₁ hr₂ hle₂) (ε₁ := ε / 2) (by
    rw [shrinkAt_chart_r₀_of_ne hf hr₁ hle₁ hq hpq]; linarith) (Or.inr hx2), shrinkAt_V,
    shrunkV_eq_of_level hr₁ hle₁ (ε₁ := ε / 2) (by linarith) (Or.inl hx1)]

omit [I.Boundaryless] in
theorem shrink₂_V_of_notMem (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) {x : M}
    (hxp : x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')
    (hxq : x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R') :
    (shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).V x = D.V x := by
  unfold shrink₂
  rw [shrinkAt_V, shrunkV_of_notMem (by rw [shrinkAt_chart_χ, shrinkAt_chart_R']; exact hxq),
    shrinkAt_V, shrunkV_of_notMem hxp]

omit [I.Boundaryless] in
theorem shrink₂_V_of_notMem_half (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hpq : q ≠ p) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle₁ : r₁ ≤ (D.chart p hp).r₀)
    (hr₂ : 0 < r₂) (hle₂ : r₂ ≤ (D.chart q hq).r₀) {x : M}
    (hxp : x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2})
    (hxq : x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2}) :
    (shrink₂ hf hp hq hpq hr₁ hle₁ hr₂ hle₂).V x = D.V x := by
  unfold shrink₂
  rw [shrinkAt_V, shrunkV_of_notMem_image hr₂ (hle₂' hf hp hq hpq hr₁ hle₁ hr₂ hle₂) (by
    rw [shrinkAt_chart_χ, shrinkAt_chart_r₀_of_ne hf hr₁ hle₁ hq hpq]; exact hxq),
    shrinkAt_V, shrunkV_of_notMem_image hr₁ hle₁ hxp]

omit [T2Space M] [I.Boundaryless] in
theorem isOpen_between (hfc : Continuous f) (s t : ℝ) : IsOpen {x : M | s < f x ∧ f x < t} :=
  (isOpen_lt continuous_const hfc).inter (isOpen_lt hfc continuous_const)

end ShrinkTwo

section TubeCongr

omit [T2Space M] [I.Boundaryless] in
theorem norm_negPart_congr {k k' : ℕ} (h : k = k') (hk : k ≤ n) (hk' : k' ≤ n) (y : Fin n → ℝ) :
    ‖negPart hk y‖ = ‖negPart hk' y‖ := by subst h; rfl

omit [T2Space M] [I.Boundaryless] in
theorem norm_posPart_congr {k k' : ℕ} (h : k = k') (hk : k ≤ n) (hk' : k' ≤ n) (y : Fin n → ℝ) :
    ‖posPart hk y‖ = ‖posPart hk' y‖ := by subst h; rfl

omit [T2Space M] [I.Boundaryless] in
theorem nf_congr {k k' : ℕ} (h : k = k') (hk : k ≤ n) (hk' : k' ≤ n) (c : ℝ) (y : Fin n → ℝ) :
    morseNormalForm hk c y = morseNormalForm hk' c y := by subst h; rfl

variable {D}

omit [T2Space M] [I.Boundaryless] in
theorem posPart_eq_zero_congr {k k' : ℕ} (h : k = k') (hk : k ≤ n) (hk' : k' ≤ n)
    (y : Fin n → ℝ) : posPart hk y = 0 ↔ posPart hk' y = 0 := by subst h; exact Iff.rfl

omit [T2Space M] [I.Boundaryless] in
theorem negPart_eq_zero_congr {k k' : ℕ} (h : k = k') (hk : k ≤ n) (hk' : k' ≤ n)
    (y : Fin n → ℝ) : negPart hk y = 0 ↔ negPart hk' y = 0 := by subst h; exact Iff.rfl

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem leftModelSphere_eq {q : M} {d d' : MorseNormalChart I f q} (h : d'.k = d.k) (ε : ℝ) :
    d'.leftModelSphere ε = d.leftModelSphere ε := by
  ext y
  simp only [MorseNormalChart.leftModelSphere, mem_ofPred_eq]
  rw [posPart_eq_zero_congr h, norm_negPart_congr h]

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem rightModelSphere_eq {q : M} {d d' : MorseNormalChart I f q} (h : d'.k = d.k) (ε : ℝ) :
    d'.rightModelSphere ε = d.rightModelSphere ε := by
  ext y
  simp only [MorseNormalChart.rightModelSphere, mem_ofPred_eq]
  rw [negPart_eq_zero_congr h, norm_posPart_congr h]

omit [T2Space M] [I.Boundaryless] in
theorem leftTube_eq {D' : GradientLikeStrip I f a b crit} {q : M} (hq : q ∈ crit)
    (hk : (D'.chart q hq).k = (D.chart q hq).k) (ε δ : ℝ) :
    D'.leftTube q hq ε δ = D.leftTube q hq ε δ := by
  ext y
  simp only [leftTube, mem_ofPred_eq]
  rw [nf_congr hk _ _, norm_posPart_congr hk]

omit [T2Space M] [I.Boundaryless] in
theorem rightTube_eq {D' : GradientLikeStrip I f a b crit} {p : M} (hp : p ∈ crit)
    (hk : (D'.chart p hp).k = (D.chart p hp).k) (ε δ : ℝ) :
    D'.rightTube p hp ε δ = D.rightTube p hp ε δ := by
  ext y
  simp only [rightTube, mem_ofPred_eq]
  rw [nf_congr hk _ _, norm_negPart_congr hk]

end TubeCongr

section noCommon

variable {D}

theorem nocommon_of_agree (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D' : GradientLikeStrip I f a b crit}
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hpq : q ≠ p)
    (hχ : ∀ q' hq', (D'.chart q' hq').χ = (D.chart q' hq').χ)
    (hk : ∀ q' hq', (D'.chart q' hq').k = (D.chart q' hq').k)
    (hsmall : ∀ q' hq', D'.smallBall q' hq' ⊆ D.smallBall q' hq')
    {ε c δ r' : ℝ} (hε : 0 < ε) (hr' : 0 < r') (hr'ε : r' ^ 2 < ε) (hr'δ : r' ^ 4 ≤ 2 * ε * δ)
    (hrmp : 4 * ε < D'.rm p hp ^ 2) (hrmq : 4 * ε < D'.rm q hq ^ 2)
    (hV : ∀ x, f p + ε / 2 ≤ f x → f x ≤ f q - ε / 2 → D'.V x = D.V x)
    (hc : f p + ε < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    (htube : Disjoint (D.flow (f p + ε - c) '' ((D.chart p hp).χ '' D.rightTube p hp ε δ))
      (D.flow (f q - ε - c) '' ((D.chart q hq).χ '' D.leftTube q hq ε δ))) :
    ∀ x ∈ (D'.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
      D'.flow t x ∉ (D'.chart q hq).χ '' {y | morseNorm n y < r'} := by
  rintro _ ⟨y, hy, rfl⟩ t ⟨y', hy', hxt⟩
  replace hxt := hxt.symm
  have hy : morseNorm n y < r' := hy
  have hy' : morseNorm n y' < r' := hy'
  have hpa : a < f p := (D'.f_mem_Ioo p hp).1
  have hqb : f q < b := (D'.f_mem_Ioo q hq).2
  have hpq' : p ≠ q := Ne.symm hpq
  have hrmp' := D'.rm_pos p hp
  have hrmq' := D'.rm_pos q hq
  have hr'rmp : r' < D'.rm p hp :=
    lt_of_pow_lt_pow_left₀ 2 hrmp'.le (show r' ^ 2 < D'.rm p hp ^ 2 by linarith)
  have hr'rmq : r' < D'.rm q hq :=
    lt_of_pow_lt_pow_left₀ 2 hrmq'.le (show r' ^ 2 < D'.rm q hq ^ 2 by linarith)
  have hyrm : morseNorm n y < D'.rm p hp := hy.trans hr'rmp
  have hy'rm : morseNorm n y' < D'.rm q hq := hy'.trans hr'rmq
  have hyR : morseNorm n y ≤ (D'.chart p hp).R := hyrm.le.trans (D'.hrm p hp).2
  have hy'R : morseNorm n y' ≤ (D'.chart q hq).R := hy'rm.le.trans (D'.hrm q hq).2
  have hysq : morseNorm n y ^ 2 < r' ^ 2 :=
    pow_lt_pow_left₀ hy (ModelField.morseNorm_nonneg y) two_ne_zero
  have hy'sq : morseNorm n y' ^ 2 < r' ^ 2 :=
    pow_lt_pow_left₀ hy' (ModelField.morseNorm_nonneg y') two_ne_zero
  have hsqy := morseNorm_sq_eq_negPart_add_posPart (D'.chart p hp).hk y
  have hsqy' := morseNorm_sq_eq_negPart_add_posPart (D'.chart q hq).hk y'
  have hu0 := sq_nonneg ‖negPart (D'.chart p hp).hk y‖
  have hv0 := sq_nonneg ‖posPart (D'.chart p hp).hk y‖
  have hu0' := sq_nonneg ‖negPart (D'.chart q hq).hk y'‖
  have hv0' := sq_nonneg ‖posPart (D'.chart q hq).hk y'‖
  have hfy : f ((D'.chart p hp).χ y) = morseNormalForm (D'.chart p hp).hk (f p) y :=
    (D'.chart p hp).hnorm y hyR
  have hfy' : f ((D'.chart q hq).χ y') = morseNormalForm (D'.chart q hq).hk (f q) y' :=
    (D'.chart q hq).hnorm y' hy'R
  have hnfy := morseNormalForm_split (D'.chart p hp).hk (f p) y
  have hnfy' := morseNormalForm_split (D'.chart q hq).hk (f q) y'
  have hfylt : f ((D'.chart p hp).χ y) < f p + ε := by
    rw [hfy, hnfy]; linarith [hsqy, hu0, hysq, hr'ε]
  have hfy'gt : f q - ε < f ((D'.chart q hq).χ y') := by
    rw [hfy', hnfy']; linarith [hsqy', hv0', hy'sq, hr'ε]
  have ht : t < 0 := by
    by_contra h
    have := f_flow_le (D := D') hf ((D'.chart p hp).χ y) (not_lt.1 h)
    rw [hxt] at this
    linarith
  have hback : D'.flow (-t) ((D'.chart q hq).χ y') = (D'.chart p hp).χ y := by
    rw [← hxt, flow_neg_flow]
  have hdisj := D'.disjoint p hp q hq hpq'
  have hyb : (D'.chart p hp).χ y ∈ (D'.chart p hp).χ '' Metric.ball 0 (D'.chart p hp).R' :=
    ⟨y, (D'.chart p hp).mem_ball_of_le hyR, rfl⟩
  have hy'b : (D'.chart q hq).χ y' ∈ (D'.chart q hq).χ '' Metric.ball 0 (D'.chart q hq).R' :=
    ⟨y', (D'.chart q hq).mem_ball_of_le hy'R, rfl⟩
  have hlev' : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D'.smallBall p' hp' :=
    fun y hy p' hp' h => hlev y hy p' hp' (hsmall p' hp' h)
  have hcab : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hcU : ∀ y, f y = c → dfV I f D'.V y = -1 := fun y hy =>
    D'.dfV_eq_neg_one_of_level hcab (fun p' hp' y' hy' hfy' =>
      hlev' y' (by rw [hfy']; exact ⟨hc.le, hcq.le⟩) p' hp' hy') hy
  have hexitq : ∃ T₁, f (D'.flow T₁ ((D'.chart q hq).χ y')) = f q - ε ∧
      D'.flow T₁ ((D'.chart q hq).χ y') ∈ (D'.chart q hq).χ '' D'.leftTube q hq ε δ := by
    by_cases hu' : negPart (D'.chart q hq).hk y' = 0
    · exfalso
      have hmem := flow_mem_of_negPart_eq_zero (D := D') hq hy'rm hu' (t := -t) (by linarith)
      rw [hback] at hmem
      exact hdisj.notMem_of_mem_left hyb (image_mono (fun z hz =>
        (D'.chart q hq).le_subset_ball (hy'R.trans_lt (D'.chart q hq).hRR') hz.1) hmem)
    · obtain ⟨t₁, ht₁, hft₁, hstay, hprod⟩ := exists_exit_desc (D := D') hf hq hε (y := y')
        (by linarith [hsqy', hu0', hy'sq, hr'ε, hrmq]) hu'
        (by rw [hnfy']; linarith [hsqy', hv0', hy'sq, hr'ε])
      obtain ⟨y₁, hy₁, hy₁w⟩ := hstay t₁ (right_mem_Icc.2 ht₁)
      have hy₁R : morseNorm n y₁ ≤ (D'.chart q hq).R := by
        have h1 : morseNorm n y₁ ^ 2 ≤ (D'.chart q hq).R ^ 2 := by
          have h2 := (D'.hrm q hq).2
          have h3 : D'.rm q hq ^ 2 ≤ (D'.chart q hq).R ^ 2 :=
            pow_le_pow_left₀ hrmq'.le h2 2
          linarith [show morseNorm n y₁ ^ 2 ≤ _ from hy₁, hsqy', hu0', hy'sq, hr'ε]
        exact MorseNormalChart.morseNorm_le_of_sq_le (D'.chart q hq).R_pos.le h1
      have hsymm : (D'.chart q hq).χ.symm (D'.flow t₁ ((D'.chart q hq).χ y')) = y₁ := by
        rw [← hy₁w, (D'.chart q hq).χ.left_inv ((D'.chart q hq).hsrc y₁ hy₁R)]
      rw [hsymm] at hprod
      refine ⟨t₁, hft₁, y₁, ⟨?_, ?_⟩, hy₁w⟩
      · rw [← (D'.chart q hq).hnorm y₁ hy₁R, hy₁w]; exact hft₁
      · have hprod' : ‖negPart (D'.chart q hq).hk y'‖ ^ 2 * ‖posPart (D'.chart q hq).hk y'‖ ^ 2 ≤
            r' ^ 4 := by
          have h1 : ‖negPart (D'.chart q hq).hk y'‖ ^ 2 ≤ r' ^ 2 := by linarith [hsqy', hv0', hy'sq]
          have h2 : ‖posPart (D'.chart q hq).hk y'‖ ^ 2 ≤ r' ^ 2 := by linarith [hsqy', hu0', hy'sq]
          calc _ ≤ r' ^ 2 * r' ^ 2 := mul_le_mul h1 h2 hv0' (by positivity)
            _ = r' ^ 4 := by ring
        exact le_of_mul_le_mul_left (hprod.trans (hprod'.trans hr'δ)) (by positivity)
  have hexitp : ∃ T₂, f (D'.flow T₂ ((D'.chart p hp).χ y)) = f p + ε ∧
      D'.flow T₂ ((D'.chart p hp).χ y) ∈ (D'.chart p hp).χ '' D'.rightTube p hp ε δ := by
    by_cases hv : posPart (D'.chart p hp).hk y = 0
    · exfalso
      have hmem := flow_mem_of_posPart_eq_zero (D := D') hp hyrm hv (t := t) ht.le
      rw [hxt] at hmem
      exact hdisj.notMem_of_mem_right hy'b (image_mono (fun z hz =>
        (D'.chart p hp).le_subset_ball (hyR.trans_lt (D'.chart p hp).hRR') hz.1) hmem)
    · obtain ⟨t₂, ht₂, hft₂, hstay, hprod⟩ := exists_exit_asc (D := D') hf hp hε (y := y)
        (by linarith [hsqy, hv0, hysq, hr'ε, hrmp]) hv
        (by rw [hnfy]; linarith [hsqy, hu0, hysq, hr'ε])
      obtain ⟨y₂, hy₂, hy₂w⟩ := hstay (-t₂) (left_mem_Icc.2 (by linarith))
      have hy₂R : morseNorm n y₂ ≤ (D'.chart p hp).R := by
        have h1 : morseNorm n y₂ ^ 2 ≤ (D'.chart p hp).R ^ 2 := by
          have h2 := (D'.hrm p hp).2
          have h3 : D'.rm p hp ^ 2 ≤ (D'.chart p hp).R ^ 2 :=
            pow_le_pow_left₀ hrmp'.le h2 2
          linarith [show morseNorm n y₂ ^ 2 ≤ _ from hy₂, hsqy, hv0, hysq, hr'ε]
        exact MorseNormalChart.morseNorm_le_of_sq_le (D'.chart p hp).R_pos.le h1
      have hsymm : (D'.chart p hp).χ.symm (D'.flow (-t₂) ((D'.chart p hp).χ y)) = y₂ := by
        rw [← hy₂w, (D'.chart p hp).χ.left_inv ((D'.chart p hp).hsrc y₂ hy₂R)]
      rw [hsymm] at hprod
      refine ⟨-t₂, hft₂, y₂, ⟨?_, ?_⟩, hy₂w⟩
      · rw [← (D'.chart p hp).hnorm y₂ hy₂R, hy₂w]; exact hft₂
      · have hprod' : ‖negPart (D'.chart p hp).hk y‖ ^ 2 * ‖posPart (D'.chart p hp).hk y‖ ^ 2 ≤
            r' ^ 4 := by
          have h1 : ‖negPart (D'.chart p hp).hk y‖ ^ 2 ≤ r' ^ 2 := by linarith [hsqy, hv0, hysq]
          have h2 : ‖posPart (D'.chart p hp).hk y‖ ^ 2 ≤ r' ^ 2 := by linarith [hsqy, hu0, hysq]
          calc _ ≤ r' ^ 2 * r' ^ 2 := mul_le_mul h1 h2 hv0 (by positivity)
            _ = r' ^ 4 := by ring
        exact le_of_mul_le_mul_left (hprod.trans (hprod'.trans hr'δ)) (by positivity)
  obtain ⟨T₁, hfT₁, hwL⟩ := hexitq
  obtain ⟨T₂, hfT₂, hwR⟩ := hexitp
  have hunitL : ∀ y, f y ∈ uIcc (f q - ε) c → ∀ p' hp', y ∉ D'.smallBall p' hp' := by
    intro y hy
    rw [uIcc_of_ge hcq.le] at hy
    exact hlev' y ⟨by linarith [hy.1], hy.2⟩
  have hunitR : ∀ y, f y ∈ uIcc (f p + ε) c → ∀ p' hp', y ∉ D'.smallBall p' hp' := by
    intro y hy
    rw [uIcc_of_le hc.le] at hy
    exact hlev' y ⟨hy.1, by linarith [hy.2]⟩
  have hζL : f (D'.flow (f q - ε - c) (D'.flow T₁ ((D'.chart q hq).χ y'))) = c := by
    have := f_flow_eq_sub_of_levels hf (D := D') (x := D'.flow T₁ ((D'.chart q hq).χ y'))
      (T := f q - ε - c) (by rw [hfT₁]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfT₁, sub_sub_cancel]; exact hcab) (by rw [hfT₁, sub_sub_cancel]; exact hunitL)
      _ right_mem_uIcc
    rw [this, hfT₁]; ring
  have hζR : f (D'.flow (f p + ε - c) (D'.flow T₂ ((D'.chart p hp).χ y))) = c := by
    have := f_flow_eq_sub_of_levels hf (D := D') (x := D'.flow T₂ ((D'.chart p hp).χ y))
      (T := f p + ε - c) (by rw [hfT₂]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfT₂, sub_sub_cancel]; exact hcab) (by rw [hfT₂, sub_sub_cancel]; exact hunitR)
      _ right_mem_uIcc
    rw [this, hfT₂]; ring
  have hζeq : D'.flow (f q - ε - c) (D'.flow T₁ ((D'.chart q hq).χ y')) =
      D'.flow (f p + ε - c) (D'.flow T₂ ((D'.chart p hp).χ y)) := by
    rw [← hback, flow_flow, flow_flow] at hζR ⊢
    rw [flow_flow] at hζL ⊢
    rw [flow_level_unique hf hcU hζL hζR]
  have hUo := isOpen_between (M := M) hf.continuous (f p + ε / 2) (f q - ε / 2)
  have hV' : ∀ x ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2}, D.V x = D'.V x :=
    fun x hx => (hV x hx.1.le hx.2.le).symm
  have hunitL₀ : ∀ y, f y ∈ uIcc (f q - ε) c → ∀ p' hp', y ∉ D.smallBall p' hp' := by
    intro y hy
    rw [uIcc_of_ge hcq.le] at hy
    exact hlev y ⟨by linarith [hy.1], hy.2⟩
  have hunitR₀ : ∀ y, f y ∈ uIcc (f p + ε) c → ∀ p' hp', y ∉ D.smallBall p' hp' := by
    intro y hy
    rw [uIcc_of_le hc.le] at hy
    exact hlev y ⟨hy.1, by linarith [hy.2]⟩
  have hL := flow_eq_of_agree_levels (D₁ := D) (D₂ := D') hf (ℓ := f q - ε) (c := c)
    ⟨by linarith, by linarith⟩ hcab hunitL₀ hUo hV' (fun y hy => by
      rw [uIcc_of_ge hcq.le] at hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩) hfT₁
  have hR := flow_eq_of_agree_levels (D₁ := D) (D₂ := D') hf (ℓ := f p + ε) (c := c)
    ⟨by linarith, by linarith⟩ hcab hunitR₀ hUo hV' (fun y hy => by
      rw [uIcc_of_le hc.le] at hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩) hfT₂
  have hwL' : D'.flow T₁ ((D'.chart q hq).χ y') ∈ (D.chart q hq).χ '' D.leftTube q hq ε δ := by
    rw [← hχ q hq, ← leftTube_eq hq (hk q hq)]; exact hwL
  have hwR' : D'.flow T₂ ((D'.chart p hp).χ y) ∈ (D.chart p hp).χ '' D.rightTube p hp ε δ := by
    rw [← hχ p hp, ← rightTube_eq hp (hk p hp)]; exact hwR
  refine Set.disjoint_left.1 htube ⟨_, hwR', hR.symm⟩ ⟨_, hwL', ?_⟩
  rw [← hL, hζeq]

end noCommon

omit [T2Space M] [I.Boundaryless] in
theorem exists_small_radius {A B C E : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hE : 0 < E) :
    ∃ r', 0 < r' ∧ r' ≤ A ∧ r' ≤ B ∧ r' ^ 2 < C ∧ r' ^ 4 ≤ E := by
  refine ⟨min (min A B) (min (Real.sqrt (C / 2)) (Real.sqrt (Real.sqrt E))), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hA hB) (lt_min (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_pos.2 (Real.sqrt_pos.2 hE)))
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have h1 : min (min A B) (min (Real.sqrt (C / 2)) (Real.sqrt (Real.sqrt E))) ≤
        Real.sqrt (C / 2) := (min_le_right _ _).trans (min_le_left _ _)
    have h0 : 0 ≤ min (min A B) (min (Real.sqrt (C / 2)) (Real.sqrt (Real.sqrt E))) :=
      le_min (le_min hA.le hB.le) (le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc _ ≤ Real.sqrt (C / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = C / 2 := Real.sq_sqrt (by positivity)
      _ < C := by linarith
  · have h1 : min (min A B) (min (Real.sqrt (C / 2)) (Real.sqrt (Real.sqrt E))) ≤
        Real.sqrt (Real.sqrt E) := (min_le_right _ _).trans (min_le_right _ _)
    have h0 : 0 ≤ min (min A B) (min (Real.sqrt (C / 2)) (Real.sqrt (Real.sqrt E))) :=
      le_min (le_min hA.le hB.le) (le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc _ ≤ Real.sqrt (Real.sqrt E) ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = (Real.sqrt (Real.sqrt E) ^ 2) ^ 2 := by ring
      _ = E := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hE.le]

omit [T2Space M] [I.Boundaryless] in
theorem levels_avoid_pair {p q : M} (hp : p ∈ crit) (hq : q ∈ crit)
    (hcrit : ∀ p' ∈ crit, p' = p ∨ p' = q) {ε : ℝ} (hr₀p : (D.chart p hp).r₀ ^ 2 ≤ 2 * ε)
    (hr₀q : (D.chart q hq).r₀ ^ 2 ≤ 2 * ε) :
    ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp' := by
  intro y hy p' hp' hmem
  obtain ⟨y₀, hy₀, rfl⟩ := hmem
  have hy₀ : morseNorm n y₀ < (D.chart p' hp').r₀ := hy₀
  have hyR : morseNorm n y₀ ≤ (D.chart p' hp').R := (hy₀.trans (D.r₀_lt_R p' hp')).le
  have hsq : morseNorm n y₀ ^ 2 < (D.chart p' hp').r₀ ^ 2 :=
    pow_lt_pow_left₀ hy₀ (ModelField.morseNorm_nonneg y₀) two_ne_zero
  rw [(D.chart p' hp').hnorm y₀ hyR, morseNormalForm_split] at hy
  have h1 := morseNorm_sq_eq_negPart_add_posPart (D.chart p' hp').hk y₀
  have h2 := sq_nonneg ‖negPart (D.chart p' hp').hk y₀‖
  have h3 := sq_nonneg ‖posPart (D.chart p' hp').hk y₀‖
  rcases hcrit p' hp' with rfl | rfl
  · linarith [hy.1]
  · linarith [hy.2]

theorem exists_gradientLike_generalPosition (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hpq : p ≠ q)
    (hidx : morseIndex I f q < morseIndex I f p) {ε c : ℝ} (hε : 0 < ε)
    (hr₀p : (D.chart p hp).r₀ ^ 2 < 2 * ε) (hr₀q : (D.chart q hq).r₀ ^ 2 < 2 * ε)
    (hrmp : 24 * ε < D.rm p hp ^ 2) (hrmq : 4 * ε < D.rm q hq ^ 2)
    (hc : f p + 8 * ε < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ p' hp', (D'.chart p' hp').χ = (D.chart p' hp').χ ∧
        (D'.chart p' hp').k = (D.chart p' hp').k ∧ (D'.chart p' hp').R = (D.chart p' hp').R ∧
        (D'.chart p' hp').R' = (D.chart p' hp').R') ∧
      (∀ p' hp', (D'.chart p' hp').r₀ ≤ (D.chart p' hp').r₀) ∧
      D'.rm p hp ^ 2 = 8 * ε ∧ (∀ p' hp', p' ≠ p → D'.rm p' hp' = D.rm p' hp') ∧
      (∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' →
        x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' → D'.V x = D.V x) ∧
      (∀ x, (f x ≤ f p + 4 * ε ∨ f p + 8 * ε ≤ f x) →
        x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} →
        x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2} → D'.V x = D.V x) ∧
      D'.leftSphere q hq ε c = D.leftSphere q hq ε c ∧
      Disjoint (D'.rightSphere p hp ε c) (D'.leftSphere q hq ε c) ∧
      ∃ r', 0 < r' ∧ (D'.chart p hp).r₀ < r' ∧ (D'.chart q hq).r₀ < r' ∧ r' ^ 2 < ε ∧
        (∀ x ∈ (D'.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
          D'.flow t x ∉ (D'.chart q hq).χ '' {y | morseNorm n y < r'}) ∧
        ∃ δ, 0 < δ ∧ δ ≤ ε ∧ r' ^ 4 ≤ 2 * ε * δ ∧
          Disjoint (D'.flow (f p + ε - c) '' ((D'.chart p hp).χ '' D'.rightTube p hp ε δ))
            (D'.flow (f q - ε - c) '' ((D'.chart q hq).χ '' D'.leftTube q hq ε δ)) := by
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hpq' : q ≠ p := Ne.symm hpq
  have hrmp0 := D.rm_pos p hp
  have hrmq0 := D.rm_pos q hq
  have hrmpR : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := pow_le_pow_left₀ hrmp0.le (D.hrm p hp).2 2
  have hrmqR : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 := pow_le_pow_left₀ hrmq0.le (D.hrm q hq).2 2
  have hr₀p0 := (D.chart p hp).hr₀
  have hr₀q0 := (D.chart q hq).hr₀
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 8 * ε := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; exact hε
  have hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2 := by
    rw [hρdef, hηdef]
    have : 18 * ε ^ 2 / (8 * ε) = 9 * ε / 4 := by field_simp; ring
    rw [this]; linarith
  have hηrm : η ≤ D.rm p hp ^ 2 := by rw [hηdef]; linarith
  have hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η := by rw [hηdef]; linarith
  have hεη : ε ≤ η / 2 := by rw [hηdef]; linarith
  have hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε := by linarith
  have hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2 := by
    rw [hρdef, hηdef]
    have : ε ^ 2 / ε = ε := by field_simp
    rw [this]; linarith
  have hεq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by linarith
  have hεp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by linarith
  have hηc : f p + η < c := by rw [hηdef]; exact hc
  have hlevη : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp' :=
    fun y hy => hlev y ⟨by rw [hηdef] at hy; linarith [hy.1], hy.2⟩
  have hlt : (D.chart q hq).k < (D.chart p hp).k := by
    rw [← (D.chart q hq).hkidx, ← (D.chart p hp).hkidx]; exact hidx
  obtain ⟨z, hzρ, hzF⟩ := exists_sard_z (D := D) (p := p) (hq := hq) (ε := ε) (c := c) (η := η)
    (hp := hp) hf hε hη hεq hηc.le hcq.le hlevη hlt hρ
  have hz : ‖z‖ ≤ ρ := hzρ.le
  have hsep := disjoint_spheres_twisted hf hη hρ hsupp hηrm hr₀η hq hε hεη hr₀ε hz hB hεq hηc hcq
    hlevη hzF
  have hleft := leftSphere_twisted (z := z) hf hη hρ hsupp hηrm hr₀η hq hεq hηc hcq.le (ε := ε)
  obtain ⟨Dt, hDt⟩ : ∃ Dt : GradientLikeStrip I f a b crit,
    twisted (z := z) hf hη hρ hsupp hηrm hr₀η = Dt := ⟨_, rfl⟩
  have hDtchart : Dt.chart = D.chart := by rw [← hDt]; rfl
  have hDtrmp : Dt.rm p hp = Real.sqrt η := by rw [← hDt]; exact twisted_rm_self _ _ _ _ _ _
  have hDtrmq : ∀ p' hp', p' ≠ p → Dt.rm p' hp' = D.rm p' hp' := fun p' hp' h => by
    rw [← hDt]; exact twisted_rm_of_ne _ _ _ _ _ _ hp' h
  have hDtsmall : ∀ p' hp', Dt.smallBall p' hp' = D.smallBall p' hp' := fun p' hp' => by
    rw [← hDt]; rfl
  have hDtV_ge : ∀ x, f p + η ≤ f x → Dt.V x = D.V x := fun x hx => by
    rw [← hDt]; exact twistedV_eq_of_level_ge hη hρ hsupp hx
  have hDtV_le : ∀ x, f x ≤ f p + η / 2 → Dt.V x = D.V x := fun x hx => by
    rw [← hDt]; exact twistedV_eq_of_level_le hη hρ hsupp hx
  have hDtV_out : ∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' → Dt.V x = D.V x :=
    fun x hx => by rw [← hDt]; exact twistedV_of_notMem hx
  rw [hDt] at hsep hleft
  have hDtrmp2 : Dt.rm p hp ^ 2 = 8 * ε := by
    rw [hDtrmp, Real.sq_sqrt hη.le, hηdef]
  have hDtrmq2 : Dt.rm q hq = D.rm q hq := hDtrmq q hq hpq'
  obtain ⟨δ₀, hδ₀, htube₀⟩ := exists_tube_disjoint Dt p hp q hq hε (by rw [hDtchart]; exact hεp)
    (by rw [hDtchart]; exact hεq) hsep
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₀ ε := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min hδ₀ hε
  have hδε : δ ≤ ε := by rw [hδdef]; exact min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := by rw [hδdef]; exact min_le_left _ _
  have htube : Disjoint (Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ))
      (Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ)) := by
    refine htube₀.mono (image_mono (image_mono fun y hy => And.intro hy.1 (hy.2.trans hδδ₀)))
      (image_mono (image_mono fun y hy => And.intro hy.1 (hy.2.trans hδδ₀)))
  obtain ⟨r', hr', hr'p, hr'q, hr'ε, hr'δ⟩ := exists_small_radius hr₀p0 hr₀q0 hε
    (show 0 < 2 * ε * δ by positivity)
  have hr₁ : 0 < r' / 2 := by positivity
  have hle₁ : r' / 2 ≤ (Dt.chart p hp).r₀ := by rw [hDtchart]; linarith
  have hle₂ : r' / 2 ≤ (Dt.chart q hq).r₀ := by rw [hDtchart]; linarith
  obtain ⟨D', hD'⟩ : ∃ D' : GradientLikeStrip I f a b crit,
    shrink₂ (D := Dt) hf hp hq hpq' hr₁ hle₁ hr₁ hle₂ = D' := ⟨_, rfl⟩
  have hχ : ∀ p' hp', (D'.chart p' hp').χ = (Dt.chart p' hp').χ := fun p' hp' => by
    rw [← hD']; rfl
  have hk : ∀ p' hp', (D'.chart p' hp').k = (Dt.chart p' hp').k := fun p' hp' => by
    rw [← hD']; rfl
  have hR : ∀ p' hp', (D'.chart p' hp').R = (Dt.chart p' hp').R := fun p' hp' => by
    rw [← hD']; rfl
  have hR' : ∀ p' hp', (D'.chart p' hp').R' = (Dt.chart p' hp').R' := fun p' hp' => by
    rw [← hD']; rfl
  have hrm : D'.rm = Dt.rm := by rw [← hD']; rfl
  have hr₀p' : (D'.chart p hp).r₀ = r' / 2 := by
    rw [← hD']; exact shrink₂_r₀_p _ _ _ _ _ _ _ _
  have hr₀q' : (D'.chart q hq).r₀ = r' / 2 := by
    rw [← hD']; exact shrink₂_r₀_q _ _ _ _ _ _ _ _
  have hr₀' : ∀ p' hp', p' ≠ p → p' ≠ q → (D'.chart p' hp').r₀ = (Dt.chart p' hp').r₀ :=
    fun p' hp' h1 h2 => by rw [← hD']; exact shrink₂_r₀_of_ne _ _ _ _ _ _ _ _ hp' h1 h2
  have hsmall : ∀ p' hp', D'.smallBall p' hp' ⊆ Dt.smallBall p' hp' := fun p' hp' => by
    rw [← hD']; exact smallBall_shrink₂_subset _ _ _ _ _ _ _ _ p' hp'
  have hεp' : (Dt.chart p hp).r₀ ^ 2 < 4 * ε := by rw [hDtchart]; linarith
  have hεq' : (Dt.chart q hq).r₀ ^ 2 < 4 * ε := by rw [hDtchart]; linarith
  have hV : ∀ x, f p + ε / 2 ≤ f x → f x ≤ f q - ε / 2 → D'.V x = Dt.V x := fun x hx1 hx2 => by
    rw [← hD']; exact shrink₂_V_eq _ _ _ _ _ _ _ _ hεp' hεq' hx1 hx2
  have hV_out : ∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' →
      x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' → D'.V x = Dt.V x :=
    fun x hxp hxq => by
      rw [← hD']
      exact shrink₂_V_of_notMem _ _ _ _ _ _ _ _ (by rw [hDtchart]; exact hxp)
        (by rw [hDtchart]; exact hxq)
  have hV_half : ∀ x, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} →
      x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2} → D'.V x = Dt.V x :=
    fun x hxp hxq => by
      rw [← hD']
      exact shrink₂_V_of_notMem_half _ _ _ _ _ _ _ _ (by rw [hDtchart]; exact hxp)
        (by rw [hDtchart]; exact hxq)
  have hUo := isOpen_between (M := M) hf.continuous (f p + ε / 2) (f q - ε / 2)
  have hV' : ∀ x ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2}, Dt.V x = D'.V x :=
    fun x hx => (hV x hx.1.le hx.2.le).symm
  have hcab : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hunitL : ∀ y, f y ∈ uIcc (f q - ε) c → ∀ p' hp', y ∉ Dt.smallBall p' hp' := by
    intro y hy p' hp'
    rw [uIcc_of_ge hcq.le] at hy
    rw [hDtsmall]
    exact hlev y ⟨by linarith [hy.1], hy.2⟩ p' hp'
  have hunitR : ∀ y, f y ∈ uIcc (f p + ε) c → ∀ p' hp', y ∉ Dt.smallBall p' hp' := by
    intro y hy p' hp'
    rw [uIcc_of_le (by linarith)] at hy
    rw [hDtsmall]
    exact hlev y ⟨hy.1, by linarith [hy.2]⟩ p' hp'
  have hUL : ∀ y, f y ∈ uIcc (f q - ε) c → y ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2} := by
    intro y hy
    rw [uIcc_of_ge hcq.le] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hUR : ∀ y, f y ∈ uIcc (f p + ε) c → y ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2} := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hℓL : f q - ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hℓR : f p + ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hleftD' : D'.leftSphere q hq ε c = Dt.leftSphere q hq ε c := by
    unfold leftSphere
    rw [hχ q hq, leftModelSphere_eq (hk q hq)]
    exact flow_image_eq_of_agree_levels hf hℓL hcab hunitL hUo hV' hUL fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Dt.chart q hq).f_chart_of_mem_leftModelSphere (by rw [hDtchart]; exact hεq) hy
  have hrightD' : D'.rightSphere p hp ε c = Dt.rightSphere p hp ε c := by
    unfold rightSphere
    rw [hχ p hp, rightModelSphere_eq (hk p hp)]
    exact flow_image_eq_of_agree_levels hf hℓR hcab hunitR hUo hV' hUR fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Dt.chart p hp).f_chart_of_mem_rightModelSphere (by rw [hDtchart]; exact hεp) hy
  have hlevel_tube : ∀ (p' : M) (hp' : p' ∈ crit) (y : Fin n → ℝ), morseNorm n y ^ 2 ≤ 4 * ε →
      4 * ε ≤ (Dt.chart p' hp').R ^ 2 → f ((Dt.chart p' hp').χ y) =
        morseNormalForm (Dt.chart p' hp').hk (f p') y := fun p' hp' y hy hR =>
    (Dt.chart p' hp').hnorm y (MorseNormalChart.morseNorm_le_of_sq_le (Dt.chart p' hp').R_pos.le
      (hy.trans hR))
  have htubeD' : D'.flow (f p + ε - c) '' ((D'.chart p hp).χ '' D'.rightTube p hp ε δ) =
      Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ) := by
    rw [hχ p hp, rightTube_eq hp (hk p hp)]
    exact flow_image_eq_of_agree_levels hf hℓR hcab hunitR hUo hV' hUR fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hlevel_tube p hp y ?_ (by rw [hDtchart]; linarith)]
      · exact hy.1
      · have h1 := ModelField.nf_sub_eq (Dt.chart p hp).hk (f p) y
        rw [hy.1] at h1
        rw [morseNorm_sq_eq_negPart_add_posPart (Dt.chart p hp).hk]
        linarith [hy.2]
  have htubeD'L : D'.flow (f q - ε - c) '' ((D'.chart q hq).χ '' D'.leftTube q hq ε δ) =
      Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ) := by
    rw [hχ q hq, leftTube_eq hq (hk q hq)]
    exact flow_image_eq_of_agree_levels hf hℓL hcab hunitL hUo hV' hUL fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hlevel_tube q hq y ?_ (by rw [hDtchart]; linarith)]
      · exact hy.1
      · have h1 := ModelField.nf_sub_eq (Dt.chart q hq).hk (f q) y
        rw [hy.1] at h1
        rw [morseNorm_sq_eq_negPart_add_posPart (Dt.chart q hq).hk]
        linarith [hy.2]
  have hnocommon := nocommon_of_agree (D := Dt) (D' := D') hf hp hq hpq' hχ hk hsmall hε hr' hr'ε
    hr'δ (by rw [hrm, hDtrmp2]; linarith) (by rw [hrm, hDtrmq2]; exact hrmq) hV (by linarith) hcq
    (fun y hy p' hp' => by rw [hDtsmall]; exact hlev y hy p' hp') htube
  refine ⟨D', fun p' hp' => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r', hr', ?_, ?_, hr'ε,
    hnocommon, δ, hδ, hδε, hr'δ, ?_⟩
  · rw [hχ, hDtchart]
  · rw [hk, hDtchart]
  · rw [hR, hDtchart]
  · rw [hR', hDtchart]
  · intro p' hp'
    by_cases h1 : p' = p
    · subst h1; rw [hr₀p']; linarith
    · by_cases h2 : p' = q
      · subst h2; rw [hr₀q']; linarith
      · rw [hr₀' p' hp' h1 h2, hDtchart]
  · rw [hrm, hDtrmp2]
  · intro p' hp' h
    rw [hrm, hDtrmq p' hp' h]
  · intro x hxp hxq
    rw [hV_out x hxp hxq, hDtV_out x hxp]
  · intro x hx hxp hxq
    rw [hV_half x hxp hxq]
    rcases hx with hx | hx
    · exact hDtV_le x (by rw [hηdef]; linarith)
    · exact hDtV_ge x (by rw [hηdef]; exact hx)
  · rw [hleftD', hleft]
  · rw [hrightD', hleftD']; exact hsep
  · rw [hr₀p']; linarith
  · rw [hr₀q']; linarith
  · rw [htubeD', htubeD'L]; exact htube

end GradientLikeStrip

end

end DifferentialGeometry.Topology
