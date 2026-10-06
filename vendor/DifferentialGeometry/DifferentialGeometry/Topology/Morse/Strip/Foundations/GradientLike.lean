module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.CriticalFinite
public import DifferentialGeometry.Topology.Morse.Strip.Foundations.ModelField
public import DifferentialGeometry.Topology.Morse.RegularLevel.VectorField
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
import all Mathlib.LinearAlgebra.QuadraticForm.Signature

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem continuous_morseNorm : Continuous (morseNorm n) :=
  continuous_norm.comp (PiLp.continuous_toLp 2 _)

theorem isOpen_morseNorm_lt (r : ℝ) : IsOpen {y : Fin n → ℝ | morseNorm n y < r} :=
  isOpen_lt continuous_morseNorm continuous_const

theorem isClosed_morseNorm_le (r : ℝ) : IsClosed {y : Fin n → ℝ | morseNorm n y ≤ r} :=
  isClosed_le continuous_morseNorm continuous_const

theorem isCompact_morseNorm_le (r : ℝ) : IsCompact {y : Fin n → ℝ | morseNorm n y ≤ r} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_morseNorm_le r) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := r)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (morseNorm_piNorm_le y).trans hy

theorem mem_ball_of_morseNorm_lt {r : ℝ} {y : Fin n → ℝ} (hy : morseNorm n y < r) :
    y ∈ Metric.ball (0 : Fin n → ℝ) r := by
  rw [Metric.mem_ball, dist_zero_right]
  exact (morseNorm_piNorm_le y).trans_lt hy

theorem morseNorm_zero : morseNorm n (0 : Fin n → ℝ) = 0 := by simp [morseNorm]

def cutoff (r₁ r₂ : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.smoothTransition ((r₂ ^ 2 - morseNorm n y ^ 2) / (r₂ ^ 2 - r₁ ^ 2))

theorem contDiff_cutoff (r₁ r₂ : ℝ) : ContDiff ℝ ∞ (cutoff (n := n) r₁ r₂) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ModelField.contDiff_morseNorm_sq).div_const _)

theorem cutoff_nonneg (r₁ r₂ : ℝ) (y : Fin n → ℝ) : 0 ≤ cutoff r₁ r₂ y :=
  Real.smoothTransition.nonneg _

theorem cutoff_le_one (r₁ r₂ : ℝ) (y : Fin n → ℝ) : cutoff r₁ r₂ y ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cutoff_eq_one {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ r₁) : cutoff r₁ r₂ y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h2 : morseNorm n y ^ 2 ≤ r₁ ^ 2 := pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
  have h3 : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  rw [le_div_iff₀ h3]
  linarith

theorem cutoff_eq_zero {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂) {y : Fin n → ℝ}
    (hy : r₂ ≤ morseNorm n y) : cutoff r₁ r₂ y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : r₂ ^ 2 ≤ morseNorm n y ^ 2 := pow_le_pow_left₀ (by linarith) hy 2
  have h3 : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) h3.le

theorem morseNorm_lt_of_cutoff_ne_zero {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂)
    {y : Fin n → ℝ} (hy : cutoff r₁ r₂ y ≠ 0) : morseNorm n y < r₂ := by
  by_contra h
  exact hy (cutoff_eq_zero h₁ h₁₂ (not_lt.1 h))

def dfV (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (V : (x : M) → TangentSpace I x)
    (x : M) : ℝ :=
  (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x))

structure MorseNormalChart (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (p : M) where
  k : ℕ
  hk : k ≤ n
  hkidx : morseIndex I f p = k
  χ : OpenPartialHomeomorph (Fin n → ℝ) M
  R : ℝ
  R' : ℝ
  r₀ : ℝ
  hr₀ : 0 < r₀
  hr₀R : 4 * r₀ < R
  hRR' : R < R'
  hχ0 : χ 0 = p
  hball : Metric.ball 0 R' ⊆ χ.source
  hsrc : ∀ y, morseNorm n y ≤ R → y ∈ χ.source
  hnorm : ∀ y, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk (f p) y
  hχ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ χ (Metric.ball 0 R')
  hχsymm : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ χ.symm (χ '' Metric.ball 0 R')

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} (d : MorseNormalChart I f p)

theorem R_pos : 0 < d.R := by linarith [d.hr₀, d.hr₀R]

theorem R'_pos : 0 < d.R' := d.R_pos.trans d.hRR'

theorem mem_ball_of_le {y : Fin n → ℝ} (hy : morseNorm n y ≤ d.R) :
    y ∈ Metric.ball (0 : Fin n → ℝ) d.R' :=
  mem_ball_of_morseNorm_lt (hy.trans_lt d.hRR')

theorem zero_mem_ball : (0 : Fin n → ℝ) ∈ Metric.ball (0 : Fin n → ℝ) d.R' :=
  Metric.mem_ball_self d.R'_pos

theorem isOpen_image_ball : IsOpen (d.χ '' Metric.ball 0 d.R') :=
  (d.χ.isOpen_image_iff_of_subset_source d.hball).2 Metric.isOpen_ball

theorem isOpen_image_of_lt {r : ℝ} (hr : r ≤ d.R') :
    IsOpen (d.χ '' {y | morseNorm n y < r}) := by
  refine (d.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 (isOpen_morseNorm_lt r)
  exact d.hball (mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy hr))

theorem image_lt_subset_image_ball {r : ℝ} (hr : r ≤ d.R') :
    d.χ '' {y | morseNorm n y < r} ⊆ d.χ '' Metric.ball 0 d.R' :=
  image_mono fun _ hy => mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy hr)

theorem isCompact_image_le {r : ℝ} (hr : r < d.R') :
    IsCompact (d.χ '' {y | morseNorm n y ≤ r}) :=
  (isCompact_morseNorm_le r).image_of_continuousOn
    (d.χ.continuousOn.mono fun _ hy => d.hball (mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy hr)))

theorem p_mem_image_ball : p ∈ d.χ '' Metric.ball 0 d.R' :=
  ⟨0, d.zero_mem_ball, d.hχ0⟩

theorem p_mem_image_lt {r : ℝ} (hr : 0 < r) : p ∈ d.χ '' {y | morseNorm n y < r} :=
  ⟨0, by simpa [morseNorm_zero] using hr, d.hχ0⟩

theorem symm_image_eq {x : M} (hx : x ∈ d.χ '' Metric.ball 0 d.R') : d.χ (d.χ.symm x) = x := by
  obtain ⟨_, hy, rfl⟩ := hx
  rw [d.χ.left_inv (d.hball hy)]

theorem symm_mem_ball {x : M} (hx : x ∈ d.χ '' Metric.ball 0 d.R') :
    d.χ.symm x ∈ Metric.ball (0 : Fin n → ℝ) d.R' := by
  obtain ⟨_, hy, rfl⟩ := hx
  rw [d.χ.left_inv (d.hball hy)]
  exact hy

theorem contMDiffAt_chart {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ d.χ y :=
  d.hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds hy)

theorem contMDiffAt_symm {x : M} (hx : x ∈ d.χ '' Metric.ball 0 d.R') :
    ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ d.χ.symm x :=
  d.hχsymm.contMDiffAt (d.isOpen_image_ball.mem_nhds hx)

theorem mdifferentiableAt_chart {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I d.χ y :=
  (d.contMDiffAt_chart hy).mdifferentiableAt (by simp)

theorem mdifferentiableAt_symm {x : M} (hx : x ∈ d.χ '' Metric.ball 0 d.R') :
    MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) d.χ.symm x :=
  (d.contMDiffAt_symm hx).mdifferentiableAt (by simp)

theorem comp_eventuallyEq_nf {y : Fin n → ℝ} (hy : morseNorm n y < d.R) :
    (f ∘ d.χ) =ᶠ[𝓝 y] morseNormalForm d.hk (f p) :=
  eventuallyEq_of_mem ((isOpen_morseNorm_lt d.R).mem_nhds hy) fun z hz => d.hnorm z (le_of_lt hz)

theorem fderiv_comp_eq_nf {y : Fin n → ℝ} (hy : morseNorm n y < d.R) :
    fderiv ℝ (f ∘ d.χ) y = fderiv ℝ (morseNormalForm d.hk (f p)) y :=
  (d.comp_eventuallyEq_nf hy).fderiv_eq

def push (Y : (Fin n → ℝ) → Fin n → ℝ) : (x : M) → TangentSpace I x :=
  fun x => (Set.indicator (M := Fin n → ℝ) (d.χ '' Metric.ball 0 d.R')
    (fun x => tangentLinearMapToModel (mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ (d.χ.symm x))
      (Y (d.χ.symm x))) x : Fin n → ℝ)

def pushFun (b : (Fin n → ℝ) → ℝ) : M → ℝ :=
  Set.indicator (d.χ '' Metric.ball 0 d.R') (fun x => b (d.χ.symm x))

variable {d}

theorem push_apply_chart (Y : (Fin n → ℝ) → Fin n → ℝ) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    d.push Y (d.χ y) = mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ y (Y y) := by
  unfold push
  rw [Set.indicator_of_mem (mem_image_of_mem _ hy)]
  have key : ∀ z, z = y →
      tangentLinearMapToModel (mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ z) (Y z) =
        mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ y (Y y) := by
    rintro z rfl
    rfl
  exact key _ (d.χ.left_inv (d.hball hy))

theorem push_apply_of_notMem (Y : (Fin n → ℝ) → Fin n → ℝ) {x : M}
    (hx : x ∉ d.χ '' Metric.ball 0 d.R') : d.push Y x = 0 := by
  unfold push
  rw [Set.indicator_of_notMem hx]
  rfl

theorem push_eq_zero_of_notMem_image {Y : (Fin n → ℝ) → Fin n → ℝ} {K : Set (Fin n → ℝ)}
    (hYK : ∀ y ∉ K, Y y = 0) {x : M} (hx : x ∉ d.χ '' K) : d.push Y x = 0 := by
  by_cases hx' : x ∈ d.χ '' Metric.ball 0 d.R'
  · obtain ⟨y, hy, rfl⟩ := hx'
    rw [push_apply_chart Y hy, hYK y fun hyK => hx (mem_image_of_mem _ hyK)]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ y).map_zero
  · exact push_apply_of_notMem Y hx'

theorem support_push_subset {Y : (Fin n → ℝ) → Fin n → ℝ} {K : Set (Fin n → ℝ)}
    (hYK : ∀ y ∉ K, Y y = 0) : Function.support (d.push Y) ⊆ d.χ '' K := fun x hx => by
  by_contra h
  exact hx (push_eq_zero_of_notMem_image hYK h)

theorem pushFun_apply_chart (b : (Fin n → ℝ) → ℝ) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') : d.pushFun b (d.χ y) = b y := by
  unfold pushFun
  rw [Set.indicator_of_mem (mem_image_of_mem _ hy), d.χ.left_inv (d.hball hy)]

theorem pushFun_apply_of_notMem (b : (Fin n → ℝ) → ℝ) {x : M}
    (hx : x ∉ d.χ '' Metric.ball 0 d.R') : d.pushFun b x = 0 := by
  unfold pushFun
  rw [Set.indicator_of_notMem hx]

theorem pushFun_eq_zero_of_notMem_image {b : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hbK : ∀ y ∉ K, b y = 0) {x : M} (hx : x ∉ d.χ '' K) : d.pushFun b x = 0 := by
  by_cases hx' : x ∈ d.χ '' Metric.ball 0 d.R'
  · obtain ⟨y, hy, rfl⟩ := hx'
    rw [pushFun_apply_chart b hy, hbK y fun hyK => hx (mem_image_of_mem _ hyK)]
  · exact pushFun_apply_of_notMem b hx'

theorem support_pushFun_subset {b : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hbK : ∀ y ∉ K, b y = 0) : Function.support (d.pushFun b) ⊆ d.χ '' K := fun x hx => by
  by_contra h
  exact hx (pushFun_eq_zero_of_notMem_image hbK h)

theorem pullback_push (Y : (Fin n → ℝ) → Fin n → ℝ) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) (d.push Y (d.χ y)) = Y y := by
  rw [push_apply_chart Y hy]
  have hcomp := mfderiv_comp y (d.mdifferentiableAt_symm (mem_image_of_mem _ hy))
    (d.mdifferentiableAt_chart hy)
  have hev : (d.χ.symm ∘ d.χ) =ᶠ[𝓝 y] id :=
    eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy) fun z hz => d.χ.left_inv (d.hball hz)
  have h1 := hev.mfderiv_eq (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))
  rw [mfderiv_id] at h1
  exact DFunLike.congr_fun (hcomp.symm.trans h1) (Y y)

theorem df_push_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Y : (Fin n → ℝ) → Fin n → ℝ)
    {y : Fin n → ℝ} (hy : y ∈ Metric.ball (0 : Fin n → ℝ) d.R') :
    (NormedSpace.fromTangentSpace (f (d.χ y)))
        ((mfderiv I 𝓘(ℝ, ℝ) f (d.χ y)) (d.push Y (d.χ y))) =
      fderiv ℝ (f ∘ d.χ) y (Y y) := by
  rw [push_apply_chart Y hy]
  have hcomp := mfderiv_comp y ((hf (d.χ y)).mdifferentiableAt (by simp))
    (d.mdifferentiableAt_chart hy)
  have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (f ∘ d.χ) y = fderiv ℝ (f ∘ d.χ) y :=
    mfderiv_eq_fderiv
  exact DFunLike.congr_fun (hcomp.symm.trans h1) (Y y)

theorem df_push_chart_nf (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Y : (Fin n → ℝ) → Fin n → ℝ)
    {y : Fin n → ℝ} (hy : morseNorm n y < d.R) :
    (NormedSpace.fromTangentSpace (f (d.χ y)))
        ((mfderiv I 𝓘(ℝ, ℝ) f (d.χ y)) (d.push Y (d.χ y))) =
      fderiv ℝ (morseNormalForm d.hk (f p)) y (Y y) := by
  rw [df_push_chart hf Y (mem_ball_of_morseNorm_lt (hy.trans d.hRR')), d.fderiv_comp_eq_nf hy]

theorem df_push_of_notMem (Y : (Fin n → ℝ) → Fin n → ℝ) {x : M}
    (hx : x ∉ d.χ '' Metric.ball 0 d.R') :
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (d.push Y x)) = 0 := by
  rw [push_apply_of_notMem Y hx, map_zero, map_zero]

theorem contMDiffAt_comp_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (Fin n → ℝ) → F} {x : M} (hx : x ∈ d.χ '' Metric.ball 0 d.R')
    (hg : ContDiffAt ℝ ∞ g (d.χ.symm x)) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun x => g (d.χ.symm x)) x :=
  ContMDiffAt.comp (I' := 𝓘(ℝ, Fin n → ℝ)) x hg.contMDiffAt (d.contMDiffAt_symm hx)

theorem contMDiff_pushFun [T2Space M] {b : (Fin n → ℝ) → ℝ} (hb : ContDiff ℝ ∞ b)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKb : K ⊆ Metric.ball 0 d.R')
    (hbK : ∀ y ∉ K, b y = 0) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d.pushFun b) := by
  intro x₀
  by_cases hx₀ : x₀ ∈ d.χ '' Metric.ball 0 d.R'
  · refine ContMDiffAt.congr_of_eventuallyEq (contMDiffAt_comp_symm hx₀ hb.contDiffAt) ?_
    filter_upwards [d.isOpen_image_ball.mem_nhds hx₀] with x hx
    unfold pushFun
    rw [Set.indicator_of_mem hx]
  · have hC : IsClosed (d.χ '' K) :=
      (hK.image_of_continuousOn (d.χ.continuousOn.mono (hKb.trans d.hball))).isClosed
    have hx₀' : x₀ ∉ d.χ '' K := fun h => hx₀ (image_mono hKb h)
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hx₀'] with x hx
    exact pushFun_eq_zero_of_notMem_image hbK hx

variable [IsManifold I ∞ M]

theorem contMDiff_push [T2Space M] {Y : (Fin n → ℝ) → Fin n → ℝ} (hY : ContDiff ℝ ∞ Y)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKb : K ⊆ Metric.ball 0 d.R')
    (hYK : ∀ y ∉ K, Y y = 0) :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, d.push Y x⟩ : TangentBundle I M)) := by
  intro x₀
  by_cases hx₀ : x₀ ∈ d.χ '' Metric.ball 0 d.R'
  · obtain ⟨y₀, hy₀, rfl⟩ := hx₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff
      (e := trivializationAt (Fin n → ℝ) (TangentSpace I) (d.χ y₀))
      (FiberBundle.mem_baseSet_trivializationAt (Fin n → ℝ) (TangentSpace I) (d.χ y₀))]
    set g : (Fin n → ℝ) → Fin n → ℝ := fun z => extChartAt I (d.χ y₀) (d.χ z) with hgdef
    set Ω : Set (Fin n → ℝ) := Metric.ball 0 d.R' ∩ d.χ ⁻¹' (extChartAt I (d.χ y₀)).source
      with hΩdef
    have hΩ : IsOpen Ω :=
      (d.χ.continuousOn.mono d.hball).isOpen_inter_preimage Metric.isOpen_ball
        (isOpen_extChartAt_source _)
    have hy₀Ω : y₀ ∈ Ω := ⟨hy₀, mem_extChartAt_source _⟩
    have hg : ContDiffOn ℝ ∞ g Ω := by
      have h1 : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ g Ω := by
        refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := d.χ y₀)).comp
          (d.hχ.mono inter_subset_left) fun z hz => ?_
        rw [← extChartAt_source I]
        exact hz.2
      exact contMDiffOn_iff_contDiffOn.1 h1
    have hG : ContDiffAt ℝ ∞ (fun z => fderiv ℝ g z (Y z)) y₀ := by
      have hfd : ContDiffOn ℝ ∞ (fderiv ℝ g) Ω :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2
      exact (hfd.clm_apply hY.contDiffOn).contDiffAt (hΩ.mem_nhds hy₀Ω)
    have hfib : (fun x => (trivializationAt (Fin n → ℝ) (TangentSpace I) (d.χ y₀)
        ⟨x, d.push Y x⟩).2) =ᶠ[𝓝 (d.χ y₀)]
        (fun x => (fun z => fderiv ℝ g z (Y z)) (d.χ.symm x)) := by
      have hU : d.χ '' Ω ∈ 𝓝 (d.χ y₀) :=
        ((d.χ.isOpen_image_iff_of_subset_source (inter_subset_left.trans d.hball)).2 hΩ).mem_nhds
          (mem_image_of_mem _ hy₀Ω)
      filter_upwards [hU] with x hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [DifferentialGeometry.Topology.Morse.tangentTrivializationAt_apply I (d.χ y₀) (d.χ y)
        hy.2 _, push_apply_chart Y hy.1,
        d.χ.left_inv (d.hball hy.1)]
      have hext : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I (d.χ y₀)) (d.χ y) := by
        refine (contMDiffAt_extChartAt' (I := I) (n := ∞) (x := d.χ y₀) ?_).mdifferentiableAt
          (by simp)
        rw [← extChartAt_source I]
        exact hy.2
      have hcomp := mfderiv_comp y hext (d.mdifferentiableAt_chart hy.1)
      have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt I (d.χ y₀) ∘ d.χ) y =
          fderiv ℝ g y := mfderiv_eq_fderiv
      rw [tangentSpaceModelContinuousLinearEquiv_apply]
      have h2 := DFunLike.congr_fun (hcomp.symm.trans h1) (Y y)
      exact h2
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hfib
    refine contMDiffAt_comp_symm (g := fun z => fderiv ℝ g z (Y z)) (mem_image_of_mem _ hy₀) ?_
    rw [d.χ.left_inv (d.hball hy₀)]
    exact hG
  · have hC : IsClosed (d.χ '' K) :=
      (hK.image_of_continuousOn (d.χ.continuousOn.mono (hKb.trans d.hball))).isClosed
    have hx₀' : x₀ ∉ d.χ '' K := fun h => hx₀ (image_mono hKb h)
    refine ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) (IB := I)
      (n := ∞)).contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hx₀'] with x hx
    change (⟨x, d.push Y x⟩ : TangentBundle I M) = ⟨x, 0⟩
    rw [push_eq_zero_of_notMem_image hYK hx]

end MorseNormalChart

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} {d : MorseNormalChart I f p}

def modelY : (Fin n → ℝ) → Fin n → ℝ :=
  fun y => cutoff (3 * d.R / 4) d.R y • ModelField.modelField d.k d.r₀ y

def bumpY : (Fin n → ℝ) → ℝ := cutoff (d.R / 2) (3 * d.R / 4)

theorem three_quarter_pos : 0 < 3 * d.R / 4 := by linarith [d.R_pos]

theorem three_quarter_lt : 3 * d.R / 4 < d.R := by linarith [d.R_pos]

theorem half_lt_three_quarter : d.R / 2 < 3 * d.R / 4 := by linarith [d.R_pos]

theorem modelY_eq_of_le {y : Fin n → ℝ} (hy : morseNorm n y ≤ 3 * d.R / 4) :
    d.modelY y = ModelField.modelField d.k d.r₀ y := by
  unfold modelY
  rw [cutoff_eq_one d.three_quarter_pos.le d.three_quarter_lt hy, one_smul]

theorem modelY_eq_zero {y : Fin n → ℝ} (hy : d.R ≤ morseNorm n y) : d.modelY y = 0 := by
  unfold modelY
  rw [cutoff_eq_zero d.three_quarter_pos.le d.three_quarter_lt hy, zero_smul]

theorem modelY_eq_zero_of_notMem {y : Fin n → ℝ} (hy : y ∉ {y | morseNorm n y ≤ d.R}) :
    d.modelY y = 0 :=
  d.modelY_eq_zero (le_of_lt (not_le.1 hy))

theorem contDiff_modelY : ContDiff ℝ ∞ d.modelY :=
  (contDiff_cutoff _ _).smul (ModelField.contDiff_modelField d.hr₀)

theorem bumpY_nonneg (y : Fin n → ℝ) : 0 ≤ d.bumpY y := cutoff_nonneg _ _ _

theorem bumpY_le_one (y : Fin n → ℝ) : d.bumpY y ≤ 1 := cutoff_le_one _ _ _

theorem bumpY_eq_one {y : Fin n → ℝ} (hy : morseNorm n y ≤ d.R / 2) : d.bumpY y = 1 :=
  cutoff_eq_one (by linarith [d.R_pos]) d.half_lt_three_quarter hy

theorem bumpY_eq_zero {y : Fin n → ℝ} (hy : 3 * d.R / 4 ≤ morseNorm n y) : d.bumpY y = 0 :=
  cutoff_eq_zero (by linarith [d.R_pos]) d.half_lt_three_quarter hy

theorem bumpY_eq_zero_of_notMem {y : Fin n → ℝ} (hy : y ∉ {y | morseNorm n y ≤ 3 * d.R / 4}) :
    d.bumpY y = 0 :=
  d.bumpY_eq_zero (le_of_lt (not_le.1 hy))

theorem morseNorm_lt_of_bumpY_ne_zero {y : Fin n → ℝ} (hy : d.bumpY y ≠ 0) :
    morseNorm n y < 3 * d.R / 4 :=
  morseNorm_lt_of_cutoff_ne_zero (by linarith [d.R_pos]) d.half_lt_three_quarter hy

theorem contDiff_bumpY : ContDiff ℝ ∞ d.bumpY := contDiff_cutoff _ _

theorem theta_mul_sq_le_one {r₀ : ℝ} (hr₀ : 0 < r₀) (y : Fin n → ℝ) :
    ModelField.theta r₀ y * morseNorm n y ^ 2 ≤ 1 := by
  have hpos := ModelField.thetaDen_pos hr₀ y
  have hle : morseNorm n y ^ 2 ≤ ModelField.thetaDen r₀ y := by
    unfold ModelField.thetaDen
    have := ModelField.bump_nonneg r₀ y
    nlinarith [sq_nonneg r₀]
  rw [ModelField.theta, inv_mul_eq_div, div_le_one hpos]
  exact hle

theorem dfV_push_modelY_bounds (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    -1 ≤ dfV I f (d.push d.modelY) x ∧ dfV I f (d.push d.modelY) x ≤ 0 := by
  unfold dfV
  by_cases hx : x ∈ d.χ '' Metric.ball 0 d.R'
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [df_push_chart hf _ hy]
    by_cases hyR : morseNorm n y < d.R
    · rw [d.fderiv_comp_eq_nf hyR]
      unfold modelY
      rw [map_smul, smul_eq_mul, ModelField.fderiv_nf_modelField]
      have h1 := cutoff_nonneg (3 * d.R / 4) d.R y
      have h2 := cutoff_le_one (3 * d.R / 4) d.R y
      have h3 := ModelField.theta_pos d.hr₀ y
      have h4 := theta_mul_sq_le_one d.hr₀ y
      have h5 : 0 ≤ ModelField.theta d.r₀ y * morseNorm n y ^ 2 := by positivity
      constructor <;> nlinarith
    · rw [d.modelY_eq_zero (not_lt.1 hyR), map_zero]
      simp
  · rw [df_push_of_notMem _ hx]
    simp

theorem dfV_push_modelY_eq_neg_one (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy1 : morseNorm n y < 3 * d.R / 4) (hy2 : d.r₀ ≤ morseNorm n y) :
    dfV I f (d.push d.modelY) (d.χ y) = -1 := by
  unfold dfV
  rw [df_push_chart_nf hf _ (hy1.trans d.three_quarter_lt), d.modelY_eq_of_le hy1.le]
  exact ModelField.fderiv_nf_modelField_eq_neg_one d.hk _ d.hr₀ (by linarith [d.hr₀])

theorem dfV_push_modelY_neg (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : Fin n → ℝ}
    (hy1 : morseNorm n y < 3 * d.R / 4) (hy0 : y ≠ 0) :
    dfV I f (d.push d.modelY) (d.χ y) < 0 := by
  unfold dfV
  rw [df_push_chart_nf hf _ (hy1.trans d.three_quarter_lt), d.modelY_eq_of_le hy1.le]
  exact ModelField.fderiv_nf_modelField_neg d.hk _ d.hr₀ hy0

theorem pullback_push_modelY {y : Fin n → ℝ} (hy : morseNorm n y ≤ 3 * d.R / 4) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) (d.push d.modelY (d.χ y)) =
      ModelField.modelField d.k d.r₀ y := by
  rw [pullback_push _ (d.mem_ball_of_le (hy.trans d.three_quarter_lt.le)), d.modelY_eq_of_le hy]

theorem support_push_modelY_subset :
    Function.support (d.push d.modelY) ⊆ d.χ '' {y | morseNorm n y ≤ d.R} :=
  support_push_subset fun _ hy => d.modelY_eq_zero_of_notMem hy

theorem pushFun_bumpY_nonneg (x : M) : 0 ≤ d.pushFun d.bumpY x := by
  unfold pushFun
  by_cases hx : x ∈ d.χ '' Metric.ball 0 d.R'
  · rw [Set.indicator_of_mem hx]; exact d.bumpY_nonneg _
  · rw [Set.indicator_of_notMem hx]

theorem pushFun_bumpY_le_one (x : M) : d.pushFun d.bumpY x ≤ 1 := by
  unfold pushFun
  by_cases hx : x ∈ d.χ '' Metric.ball 0 d.R'
  · rw [Set.indicator_of_mem hx]; exact d.bumpY_le_one _
  · rw [Set.indicator_of_notMem hx]; exact zero_le_one

theorem pushFun_bumpY_chart_eq_one {y : Fin n → ℝ} (hy : morseNorm n y ≤ d.R / 2) :
    d.pushFun d.bumpY (d.χ y) = 1 := by
  rw [pushFun_apply_chart _ (d.mem_ball_of_le (hy.trans (by linarith [d.R_pos]))),
    d.bumpY_eq_one hy]

theorem pushFun_bumpY_eq_zero_of_notMem {x : M}
    (hx : x ∉ d.χ '' {y | morseNorm n y ≤ 3 * d.R / 4}) : d.pushFun d.bumpY x = 0 :=
  pushFun_eq_zero_of_notMem_image (fun _ hy => d.bumpY_eq_zero_of_notMem hy) hx

theorem mem_of_pushFun_bumpY_ne_zero {x : M} (hx : d.pushFun d.bumpY x ≠ 0) :
    x ∈ d.χ '' {y | morseNorm n y < 3 * d.R / 4} := by
  by_contra h
  apply hx
  exact pushFun_eq_zero_of_notMem_image (fun _ hy => d.bumpY_eq_zero (not_lt.1 hy)) h

theorem mem_image_ball_of_pushFun_bumpY_ne_zero {x : M} (hx : d.pushFun d.bumpY x ≠ 0) :
    x ∈ d.χ '' Metric.ball 0 d.R' :=
  d.image_lt_subset_image_ball (by linarith [d.R_pos, d.hRR'])
    (d.mem_of_pushFun_bumpY_ne_zero hx)

theorem contMDiff_pushFun_bumpY [T2Space M] : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d.pushFun d.bumpY) :=
  contMDiff_pushFun d.contDiff_bumpY (isCompact_morseNorm_le (3 * d.R / 4))
    (fun _ hy => mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy (by linarith [d.R_pos, d.hRR'])))
    fun _ hy => d.bumpY_eq_zero_of_notMem hy

theorem contMDiff_push_modelY [IsManifold I ∞ M] [T2Space M] :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, d.push d.modelY x⟩ : TangentBundle I M)) :=
  contMDiff_push d.contDiff_modelY (isCompact_morseNorm_le d.R)
    (fun _ hy => mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy d.hRR'))
    fun _ hy => d.modelY_eq_zero_of_notMem hy

end MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ}

theorem morseIndex_le (p : M) : morseIndex I f p ≤ n := by
  have h1 : morseIndex I f p = sigPos (-(hessianAt I f p)) := rfl
  rw [h1]
  have := sigPos_le_finrank (-(hessianAt I f p))
  rwa [Module.finrank_fin_fun] at this

theorem exists_morseNormalChart [I.Boundaryless] [IsManifold I ∞ M] (hf : MorseStrip I f a b)
    {p : M} (hp : f p ∈ Ioo a b) (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p) {O : Set M} (hO : IsOpen O)
    (hpO : p ∈ O) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ d : MorseNormalChart I f p, d.R ≤ R₀ ∧ 8 * d.r₀ < d.R ∧
      d.χ '' Metric.ball 0 d.R' ⊆ O := by
  have hk : morseIndex I f p ≤ n := morseIndex_le p
  obtain ⟨R, hR, Φ, h0src, -, hΦ0, hsrc, hnorm, -, -, R', hR', hΦ, hΦsymm⟩ :=
    DifferentialGeometry.Topology.Morse.morse_lemma I f hf.smooth p (morseIndex I f p) hk
      (hf.nondegenerate p hp hc) rfl
  have hnhds : Φ.source ∩ Φ ⁻¹' O ∈ 𝓝 (0 : Fin n → ℝ) := by
    refine inter_mem (Φ.open_source.mem_nhds h0src) ?_
    exact (Φ.continuousAt h0src).preimage_mem_nhds (hO.mem_nhds (hΦ0 ▸ hpO))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.1 hnhds
  set Rs := min R' ρ with hRsdef
  have hRspos : 0 < Rs := lt_min hR' hρ
  set Rn := min R₀ (min R (Rs / 2)) with hRndef
  have hRnpos : 0 < Rn := lt_min hR₀ (lt_min hR (by positivity))
  have hRnR : Rn ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hRnRs : Rn < Rs := by
    have : Rn ≤ Rs / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hballsub : Metric.ball (0 : Fin n → ℝ) Rs ⊆ Φ.source ∩ Φ ⁻¹' O :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hρsub
  refine ⟨{ k := morseIndex I f p
            hk := hk
            hkidx := rfl
            χ := Φ
            R := Rn
            R' := Rs
            r₀ := Rn / 16
            hr₀ := by positivity
            hr₀R := by linarith
            hRR' := hRnRs
            hχ0 := hΦ0
            hball := hballsub.trans inter_subset_left
            hsrc := fun y hy => hsrc y (hy.trans hRnR)
            hnorm := fun y hy => hnorm y (hy.trans hRnR)
            hχ := hΦ.mono (Metric.ball_subset_ball (min_le_left _ _))
            hχsymm := hΦsymm.mono (image_mono (Metric.ball_subset_ball (min_le_left _ _))) },
    min_le_left _ _, ?_, ?_⟩
  · dsimp only
    linarith
  rintro x ⟨y, hy, rfl⟩
  exact (hballsub hy).2

structure GradientLikeStrip (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M]
    (f : M → ℝ) (a b : ℝ) (crit : Finset M) where
  V : (x : M) → TangentSpace I x
  smooth : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M))
  compact : IsCompact (tsupport V)
  rate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ∧
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ≤ 0
  chart : ∀ p ∈ crit, MorseNormalChart I f p
  disjoint : ∀ p hp q hq, p ≠ q →
    Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
      ((chart q hq).χ '' Metric.ball 0 (chart q hq).R')
  inStrip : ∀ p hp, (chart p hp).χ '' Metric.ball 0 (chart p hp).R' ⊆ f ⁻¹' Ioo a b
  unit : ∀ x ∈ f ⁻¹' Icc a b,
    (∀ p hp, x ∉ (chart p hp).χ '' {y | morseNorm n y < (chart p hp).r₀}) →
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) = -1
  neg : ∀ x ∈ f ⁻¹' Icc a b, x ∉ crit →
    (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) < 0
  rm : ∀ p ∈ crit, ℝ
  hrm : ∀ p hp, 2 * (chart p hp).r₀ < rm p hp ∧ rm p hp ≤ (chart p hp).R
  model : ∀ p hp, ∀ y, morseNorm n y < rm p hp →
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (chart p hp).χ.symm ((chart p hp).χ y) (V ((chart p hp).χ y)) =
      ModelField.modelField (chart p hp).k (chart p hp).r₀ y

namespace GradientLikeStrip

variable [IsManifold I ∞ M] {crit : Finset M} (D : GradientLikeStrip I f a b crit)

theorem rm_pos (p : M) (hp : p ∈ crit) : 0 < D.rm p hp := by
  linarith [(D.hrm p hp).1, (D.chart p hp).hr₀]

theorem r₀_lt_rm (p : M) (hp : p ∈ crit) : (D.chart p hp).r₀ < D.rm p hp := by
  linarith [(D.hrm p hp).1, (D.chart p hp).hr₀]

theorem rm_lt_R' (p : M) (hp : p ∈ crit) : D.rm p hp < (D.chart p hp).R' :=
  (D.hrm p hp).2.trans_lt (D.chart p hp).hRR'

theorem dfV_rate (x : M) : -1 ≤ dfV I f D.V x ∧ dfV I f D.V x ≤ 0 := D.rate x

theorem V_crit (p : M) (hp : p ∈ crit) : D.V p = 0 := by
  have h := D.model p hp 0 (by rw [morseNorm_zero]; exact D.rm_pos p hp)
  rw [(D.chart p hp).hχ0, ModelField.modelField_zero] at h
  have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) p
    ((D.chart p hp).mdifferentiableAt_chart
      ((D.chart p hp).symm_mem_ball (D.chart p hp).p_mem_image_ball))
    ((D.chart p hp).mdifferentiableAt_symm (D.chart p hp).p_mem_image_ball)
  have hev : ((D.chart p hp).χ ∘ (D.chart p hp).χ.symm) =ᶠ[𝓝 p] id :=
    eventuallyEq_of_mem ((D.chart p hp).isOpen_image_ball.mem_nhds (D.chart p hp).p_mem_image_ball)
      fun x hx => (D.chart p hp).symm_image_eq hx
  have h1 := hev.mfderiv_eq (I := I) (I' := I)
  rw [mfderiv_id] at h1
  have h2 : (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart p hp).χ ((D.chart p hp).χ.symm p))
      ((mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm p) (D.V p)) = D.V p :=
    DFunLike.congr_fun (hcomp.symm.trans h1) (D.V p)
  have h3 : (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart p hp).χ ((D.chart p hp).χ.symm p))
      ((mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm p) (D.V p)) = 0 := by
    rw [h]
    exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I (D.chart p hp).χ ((D.chart p hp).χ.symm p)).map_zero
  exact h2.symm.trans h3

end GradientLikeStrip

theorem exists_chart_family [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) (crit : Finset M)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ chart : ∀ p ∈ crit, MorseNormalChart I f p,
      (∀ p hp, (chart p hp).R ≤ R₀) ∧ (∀ p hp, 8 * (chart p hp).r₀ < (chart p hp).R) ∧
      (∀ p hp q hq, p ≠ q → Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
        ((chart q hq).χ '' Metric.ball 0 (chart q hq).R')) ∧
      ∀ p hp, (chart p hp).χ '' Metric.ball 0 (chart p hp).R' ⊆ f ⁻¹' Ioo a' b' := by
  obtain ⟨U, hU, hUdisj⟩ := crit.finite_toSet.t2_separation
  have hfc : Continuous f := hf.smooth.continuous
  have hex : ∀ p (hp : p ∈ crit), ∃ d : MorseNormalChart I f p, d.R ≤ R₀ ∧ 8 * d.r₀ < d.R ∧
      d.χ '' Metric.ball 0 d.R' ⊆ U p ∩ f ⁻¹' Ioo a' b' := by
    intro p hp
    obtain ⟨hpo, hpc⟩ := (hcrit p).1 hp
    exact exists_morseNormalChart hf ⟨ha.trans_lt hpo.1, hpo.2.trans_le hb⟩ hpc
      ((hU p).2.inter (isOpen_Ioo.preimage hfc)) ⟨(hU p).1, hpo⟩ hR₀
  choose chart hchart using hex
  refine ⟨chart, fun p hp => (hchart p hp).1, fun p hp => (hchart p hp).2.1, ?_, ?_⟩
  · intro p hp q hq hpq
    have hd : Disjoint (U p) (U q) := hUdisj (by exact_mod_cast hp) (by exact_mod_cast hq) hpq
    exact hd.mono ((hchart p hp).2.2.trans inter_subset_left)
      ((hchart q hq).2.2.trans inter_subset_left)
  · intro p hp
    exact (hchart p hp).2.2.trans inter_subset_right

section Construction

variable {crit : Finset M} (chart : ∀ p ∈ crit, MorseNormalChart I f p)

def bumpFun (q : {q // q ∈ crit}) : M → ℝ :=
  (chart q.1 q.2).pushFun (chart q.1 q.2).bumpY

def modelPart (q : {q // q ∈ crit}) : (x : M) → TangentSpace I x :=
  (chart q.1 q.2).push (chart q.1 q.2).modelY

def glued (Vr : (x : M) → TangentSpace I x) : (x : M) → TangentSpace I x :=
  fun x => ∑ q : {q // q ∈ crit}, bumpFun chart q x • modelPart chart q x +
    (1 - ∑ q : {q // q ∈ crit}, bumpFun chart q x) • Vr x

def dfL (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ((NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap).comp (mfderiv I 𝓘(ℝ, ℝ) f x)

theorem dfL_apply (V : (x : M) → TangentSpace I x) (x : M) : dfL I f x (V x) = dfV I f V x :=
  rfl

theorem dfV_glued (Vr : (x : M) → TangentSpace I x) (x : M) :
    dfV I f (glued chart Vr) x =
      ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x +
        (1 - ∑ q : {q // q ∈ crit}, bumpFun chart q x) * dfV I f Vr x := by
  rw [← dfL_apply]
  simp only [glued, map_add, map_sum, map_smul, smul_eq_mul, dfL_apply]

variable {chart}

theorem bumpFun_unique
    (hdisj : ∀ p hp q hq, p ≠ q → Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
      ((chart q hq).χ '' Metric.ball 0 (chart q hq).R'))
    {q q' : {q // q ∈ crit}} {x : M} (hq : bumpFun chart q x ≠ 0)
    (hq' : bumpFun chart q' x ≠ 0) : q = q' := by
  by_contra hne
  have h1 := (chart q.1 q.2).mem_image_ball_of_pushFun_bumpY_ne_zero hq
  have h2 := (chart q'.1 q'.2).mem_image_ball_of_pushFun_bumpY_ne_zero hq'
  exact (hdisj q.1 q.2 q'.1 q'.2 (fun h => hne (Subtype.ext h))).notMem_of_mem_left h1 h2

theorem sum_bumpFun_eq_zero {x : M} (h : ∀ q, bumpFun chart q x = 0) :
    ∑ q : {q // q ∈ crit}, bumpFun chart q x = 0 :=
  Finset.sum_eq_zero fun q _ => h q

theorem sum_eq_single_of_unique
    (hdisj : ∀ p hp q hq, p ≠ q → Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
      ((chart q hq).χ '' Metric.ball 0 (chart q hq).R'))
    {x : M} {q₀ : {q // q ∈ crit}} (hq₀ : bumpFun chart q₀ x ≠ 0) {β : Type*} [AddCommMonoid β]
    (g : {q // q ∈ crit} → β) (hg : ∀ q, bumpFun chart q x = 0 → g q = 0) :
    ∑ q : {q // q ∈ crit}, g q = g q₀ := by
  refine Finset.sum_eq_single q₀ (fun q _ hq => hg q ?_) fun h => absurd (Finset.mem_univ _) h
  by_contra h
  exact hq (bumpFun_unique hdisj h hq₀)

theorem sum_bumpFun_mem_Icc
    (hdisj : ∀ p hp q hq, p ≠ q → Disjoint ((chart p hp).χ '' Metric.ball 0 (chart p hp).R')
      ((chart q hq).χ '' Metric.ball 0 (chart q hq).R')) (x : M) :
    0 ≤ ∑ q : {q // q ∈ crit}, bumpFun chart q x ∧
      ∑ q : {q // q ∈ crit}, bumpFun chart q x ≤ 1 := by
  by_cases h : ∃ q, bumpFun chart q x ≠ 0
  · obtain ⟨q₀, hq₀⟩ := h
    rw [sum_eq_single_of_unique hdisj hq₀ _ fun q hq => hq]
    exact ⟨(chart q₀.1 q₀.2).pushFun_bumpY_nonneg x, (chart q₀.1 q₀.2).pushFun_bumpY_le_one x⟩
  · rw [sum_bumpFun_eq_zero fun q => of_not_not fun hq => h ⟨q, hq⟩]
    exact ⟨le_rfl, zero_le_one⟩

theorem contMDiff_glued [IsManifold I ∞ M] [T2Space M] {Vr : (x : M) → TangentSpace I x}
    (hVr : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Vr x⟩ : TangentBundle I M))) :
    ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, glued chart Vr x⟩ : TangentBundle I M)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x,
      ∑ q : {q // q ∈ crit}, bumpFun chart q x • modelPart chart q x⟩ : TangentBundle I M)) := by
    have := ContMDiff.finsum_section_of_locallyFinite (I := I) (F := Fin n → ℝ)
      (V := TangentSpace I) (n := ∞)
      (t := fun q : {q // q ∈ crit} => bumpFun chart q • modelPart chart q)
      (locallyFinite_of_finite _) fun q =>
        ((chart q.1 q.2).contMDiff_pushFun_bumpY).smul_section
          (chart q.1 q.2).contMDiff_push_modelY
    simp only [finsum_eq_sum_of_fintype] at this
    exact this
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x,
      (1 - ∑ q : {q // q ∈ crit}, bumpFun chart q x) • Vr x⟩ : TangentBundle I M)) :=
    (contMDiff_const.sub
      (ContMDiff.sum fun q _ => (chart q.1 q.2).contMDiff_pushFun_bumpY)).smul_section hVr
  exact h1.add_section h2

theorem support_glued_subset {Vr : (x : M) → TangentSpace I x} :
    Function.support (glued chart Vr) ⊆ tsupport Vr ∪
      ⋃ q : {q // q ∈ crit},
        (chart q.1 q.2).χ '' {y | morseNorm n y ≤ 3 * (chart q.1 q.2).R / 4} := by
  intro x hx
  by_contra h
  rw [mem_union, not_or, mem_iUnion, not_exists] at h
  apply hx
  have hb : ∀ q, bumpFun chart q x = 0 := fun q =>
    (chart q.1 q.2).pushFun_bumpY_eq_zero_of_notMem (h.2 q)
  have hVr : Vr x = 0 := image_eq_zero_of_notMem_tsupport h.1
  simp only [glued, hb, zero_smul, Finset.sum_const_zero, sub_zero, hVr, smul_zero, add_zero]
  rfl

theorem isCompact_tsupport_glued [T2Space M] {Vr : (x : M) → TangentSpace I x}
    (hVr : IsCompact (tsupport Vr)) : IsCompact (tsupport (glued chart Vr)) := by
  have hK : IsCompact (tsupport Vr ∪
      ⋃ q : {q // q ∈ crit},
        (chart q.1 q.2).χ '' {y | morseNorm n y ≤ 3 * (chart q.1 q.2).R / 4}) :=
    hVr.union (isCompact_iUnion fun q => (chart q.1 q.2).isCompact_image_le
      (by linarith [(chart q.1 q.2).R_pos, (chart q.1 q.2).hRR']))
  exact hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal support_glued_subset hK.isClosed)

end Construction

def MorseNormalChart.halve {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    MorseNormalChart I f p :=
  { d with
    R := d.R / 2
    hr₀R := by linarith
    hRR' := by linarith [d.hRR', d.R_pos]
    hsrc := fun y hy => d.hsrc y (by linarith [d.R_pos])
    hnorm := fun y hy => d.hnorm y (by linarith [d.R_pos]) }

@[simp] theorem MorseNormalChart.halve_χ {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    (d.halve h).χ = d.χ := rfl

@[simp] theorem MorseNormalChart.halve_R {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    (d.halve h).R = d.R / 2 := rfl

@[simp] theorem MorseNormalChart.halve_R' {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    (d.halve h).R' = d.R' := rfl

@[simp] theorem MorseNormalChart.halve_r₀ {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    (d.halve h).r₀ = d.r₀ := rfl

@[simp] theorem MorseNormalChart.halve_k {p : M} (d : MorseNormalChart I f p) (h : 8 * d.r₀ < d.R) :
    (d.halve h).k = d.k := rfl

theorem exists_gradientLikeStrip [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (crit : Finset M)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ D : GradientLikeStrip I f a' b' crit,
      (∀ p hp, (D.chart p hp).R ≤ R₀) ∧ (∀ p hp, D.rm p hp = (D.chart p hp).R) ∧
      ∀ p hp, 4 * (D.chart p hp).r₀ < (D.chart p hp).R := by
  have _ := hab'
  obtain ⟨chart, hR, hr₀, hdisj, hstrip⟩ := exists_chart_family hf ha hb crit hcrit hR₀
  have hfc : Continuous f := hf.smooth.continuous
  have hcompStrip : IsCompact (f ⁻¹' Icc a' b') :=
    hf.compact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc ha hb))
  set B : Set M := ⋃ q : {q // q ∈ crit},
    (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} with hBdef
  have hBopen : IsOpen B := isOpen_iUnion fun q => (chart q.1 q.2).isOpen_image_of_lt
    (by linarith [(chart q.1 q.2).hr₀R, (chart q.1 q.2).hRR', (chart q.1 q.2).hr₀])
  set Kreg := f ⁻¹' Icc a' b' \ B with hKdef
  have hKc : IsCompact Kreg := hcompStrip.diff hBopen
  have hKreg : ∀ x ∈ Kreg, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    rintro x ⟨hx1, hx2⟩ hc
    have hxo : f x ∈ Ioo a' b' :=
      ⟨lt_of_le_of_ne hx1.1 fun h => hreg x (Or.inl h.symm) hc,
        lt_of_le_of_ne hx1.2 fun h => hreg x (Or.inr h) hc⟩
    have hxc : x ∈ crit := (hcrit x).2 ⟨hxo, hc⟩
    exact hx2 (mem_iUnion.2 ⟨⟨x, hxc⟩, (chart x hxc).p_mem_image_lt (chart x hxc).hr₀⟩)
  obtain ⟨Vr, hVr, hVrc, hVrK, hVrb⟩ :=
    DifferentialGeometry.Topology.Morse.exists_unitSpeedVectorField_on_compact I f hf.smooth
      Kreg hKc hKreg
  set V := glued chart Vr with hVdef
  have hmodel_bounds : ∀ q x, -1 ≤ dfV I f (modelPart chart q) x ∧
      dfV I f (modelPart chart q) x ≤ 0 :=
    fun q x => (chart q.1 q.2).dfV_push_modelY_bounds hf.smooth x
  have hb01 : ∀ q x, 0 ≤ bumpFun chart q x ∧ bumpFun chart q x ≤ 1 := fun q x =>
    ⟨(chart q.1 q.2).pushFun_bumpY_nonneg x, (chart q.1 q.2).pushFun_bumpY_le_one x⟩
  have hneg1 : ∀ q x, bumpFun chart q x ≠ 0 →
      x ∉ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} →
      dfV I f (modelPart chart q) x = -1 := by
    intro q x hq hx
    obtain ⟨y, hy, rfl⟩ := (chart q.1 q.2).mem_of_pushFun_bumpY_ne_zero hq
    exact (chart q.1 q.2).dfV_push_modelY_eq_neg_one hf.smooth hy
      (not_lt.1 fun h => hx ⟨y, h, rfl⟩)
  have hlt0 : ∀ q x, bumpFun chart q x ≠ 0 → x ∉ crit → dfV I f (modelPart chart q) x < 0 := by
    intro q x hq hx
    obtain ⟨y, hy, rfl⟩ := (chart q.1 q.2).mem_of_pushFun_bumpY_ne_zero hq
    refine (chart q.1 q.2).dfV_push_modelY_neg hf.smooth hy fun h0 => hx ?_
    rw [h0, (chart q.1 q.2).hχ0]
    exact q.2
  have hsum01 := fun x => sum_bumpFun_mem_Icc hdisj x
  have hb1 : ∀ q x, x ∈ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀} →
      bumpFun chart q x = 1 := by
    rintro q x ⟨y, hy, rfl⟩
    exact (chart q.1 q.2).pushFun_bumpY_chart_eq_one
      (by
        have := hr₀ q.1 q.2
        have := (chart q.1 q.2).hr₀
        simp only [Set.mem_ofPred_eq] at hy
        linarith)
  have hterm2 : ∀ x, ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x ≤ 0 :=
    fun x => Finset.sum_nonpos fun q _ => by nlinarith [hb01 q x, hmodel_bounds q x]
  have hrate : ∀ x, -1 ≤ dfV I f V x ∧ dfV I f V x ≤ 0 := by
    intro x
    rw [hVdef, dfV_glued]
    obtain ⟨hS0, hS1⟩ := hsum01 x
    have hVr' : -1 ≤ dfV I f Vr x ∧ dfV I f Vr x ≤ 0 := hVrb x
    have hterm1 : -∑ q : {q // q ∈ crit}, bumpFun chart q x ≤
        ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun q _ => by nlinarith [hb01 q x, hmodel_bounds q x]
    have := hterm2 x
    constructor <;> nlinarith
  have hunit : ∀ x ∈ f ⁻¹' Icc a' b',
      (∀ q : {q // q ∈ crit}, x ∉ (chart q.1 q.2).χ '' {y | morseNorm n y < (chart q.1 q.2).r₀}) →
      dfV I f V x = -1 := by
    intro x hx hxB
    have hxK : x ∈ Kreg := ⟨hx, fun h => by
      obtain ⟨q, hq⟩ := mem_iUnion.1 h
      exact hxB q hq⟩
    have hVrx : dfV I f Vr x = -1 := hVrK x hxK
    rw [hVdef, dfV_glued, hVrx]
    have : ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x =
        ∑ q : {q // q ∈ crit}, -(bumpFun chart q x) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : bumpFun chart q x = 0
      · rw [hq]; ring
      · rw [hneg1 q x hq (hxB q)]; ring
    rw [this, Finset.sum_neg_distrib]
    ring
  have hneg : ∀ x ∈ f ⁻¹' Icc a' b', x ∉ crit → dfV I f V x < 0 := by
    intro x hx hxc
    rw [hVdef, dfV_glued]
    obtain ⟨hS0, hS1⟩ := hsum01 x
    have hVr' : -1 ≤ dfV I f Vr x ∧ dfV I f Vr x ≤ 0 := hVrb x
    have ht2 := hterm2 x
    rcases hS1.lt_or_eq with hS | hS
    · have hxK : x ∈ Kreg := by
        refine ⟨hx, fun h => ?_⟩
        obtain ⟨q, hq⟩ := mem_iUnion.1 h
        have h1 := hb1 q x hq
        have hsum : ∑ q' : {q // q ∈ crit}, bumpFun chart q' x = 1 := by
          rw [sum_eq_single_of_unique hdisj (q₀ := q) (by rw [h1]; exact one_ne_zero) _
            fun q' hq' => hq']
          exact h1
        linarith
      have hVrx : dfV I f Vr x = -1 := hVrK x hxK
      rw [hVrx]
      nlinarith
    · have hex : ∃ q, bumpFun chart q x ≠ 0 := by
        by_contra h
        have := sum_bumpFun_eq_zero fun q => of_not_not fun hq => h ⟨q, hq⟩
        linarith
      obtain ⟨q₀, hq₀⟩ := hex
      have h1 : ∑ q : {q // q ∈ crit}, bumpFun chart q x * dfV I f (modelPart chart q) x =
          bumpFun chart q₀ x * dfV I f (modelPart chart q₀) x :=
        sum_eq_single_of_unique hdisj hq₀ _ fun q hq => by rw [hq, zero_mul]
      have h2 : ∑ q : {q // q ∈ crit}, bumpFun chart q x = bumpFun chart q₀ x :=
        sum_eq_single_of_unique hdisj hq₀ _ fun q hq => hq
      have hq₀1 : bumpFun chart q₀ x = 1 := by rw [← h2]; exact hS
      rw [h1, hS, sub_self, zero_mul, add_zero, hq₀1, one_mul]
      exact hlt0 q₀ x hq₀ hxc
  have hmodel : ∀ p hp, ∀ y, morseNorm n y < (chart p hp).R / 2 →
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (chart p hp).χ.symm ((chart p hp).χ y) (V ((chart p hp).χ y)) =
        ModelField.modelField (chart p hp).k (chart p hp).r₀ y := by
    intro p hp y hy
    have hq₀1 : bumpFun chart ⟨p, hp⟩ ((chart p hp).χ y) = 1 :=
      (chart p hp).pushFun_bumpY_chart_eq_one hy.le
    have hq₀ne : bumpFun chart ⟨p, hp⟩ ((chart p hp).χ y) ≠ 0 := by
      rw [hq₀1]; exact one_ne_zero
    have hV : V ((chart p hp).χ y) = modelPart chart ⟨p, hp⟩ ((chart p hp).χ y) := by
      rw [hVdef]
      unfold glued
      rw [sum_eq_single_of_unique hdisj hq₀ne
        (fun q => bumpFun chart q ((chart p hp).χ y) • modelPart chart q ((chart p hp).χ y))
        (fun q hq => by rw [hq, zero_smul]),
        sum_eq_single_of_unique hdisj hq₀ne _ (fun q hq => hq), hq₀1, one_smul, sub_self,
        zero_smul, add_zero]
    rw [hV]
    exact (chart p hp).pullback_push_modelY (by linarith [hy, (chart p hp).R_pos])
  refine ⟨{ V := V
            smooth := contMDiff_glued hVr
            compact := isCompact_tsupport_glued hVrc
            rate := hrate
            chart := fun p hp => (chart p hp).halve (hr₀ p hp)
            disjoint := fun p hp q hq hpq => hdisj p hp q hq hpq
            inStrip := fun p hp => hstrip p hp
            unit := fun x hx hxB => hunit x hx fun q => hxB q.1 q.2
            neg := hneg
            rm := fun p hp => (chart p hp).R / 2
            hrm := fun p hp => ⟨by
              have := hr₀ p hp
              have := (chart p hp).hr₀
              simp only [MorseNormalChart.halve_r₀]
              linarith, le_rfl⟩
            model := fun p hp y hy => hmodel p hp y hy }, ?_, ?_, ?_⟩
  · intro p hp
    simp only [MorseNormalChart.halve_R]
    linarith [hR p hp, (chart p hp).R_pos]
  · intro p hp
    rfl
  · intro p hp
    simp only [MorseNormalChart.halve_R, MorseNormalChart.halve_r₀]
    linarith [hr₀ p hp]

end

end DifferentialGeometry.Topology
