module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis.Calculus

universe uE uF

variable {E : Type uE} {F : Type uF}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def portPrivate_799fa192_inlCLM (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    E →L[ℝ] E × F :=
  (1 : E →L[ℝ] E).prod (0 : E →L[ℝ] F)

omit [CompleteSpace F] in
theorem portPrivate_799fa192_fderiv_partial_eq_comp {f : E → ℝ → F} (p : E × ℝ)
    (hd : DifferentiableAt ℝ (fun q : E × ℝ => f q.1 q.2) p) :
    fderiv ℝ (fun y : E => f y p.2) p.1 =
      (fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p).comp (portPrivate_799fa192_inlCLM E ℝ) := by
  have hseg : HasFDerivAt (fun y : E => (y, p.2)) (portPrivate_799fa192_inlCLM E ℝ) p.1 := by
    change HasFDerivAt (fun y : E => (id y, p.2))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) p.1
    exact (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hcomp := hd.hasFDerivAt.comp p.1 hseg
  have hfun : (fun y : E => f y p.2) = (fun q : E × ℝ => f q.1 q.2) ∘ (fun y : E => (y, p.2)) := by
    funext y
    rfl
  rw [← hfun] at hcomp
  exact hcomp.fderiv

omit [CompleteSpace F] in
theorem portPrivate_799fa192_partial_fderiv_contDiffOn {f : E → ℝ → F}
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => f p.1 p.2) Set.univ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => fderiv ℝ (fun y : E => f y p.2) p.1) Set.univ := by
  have hfd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p) Set.univ :=
    hf.fderiv_of_isOpen isOpen_univ
      (le_of_eq (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
  have hcompOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p).comp (portPrivate_799fa192_inlCLM E ℝ)) Set.univ := by
    let precompA : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
      { toLinearMap :=
          { toFun := fun L => L.comp (portPrivate_799fa192_inlCLM E ℝ)
            map_add' := by intro L M; ext x; simp
            map_smul' := by intro c L; ext x; simp }
        cont := by
          fun_prop }
    have hpre : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun L : (E × ℝ) →L[ℝ] F => L.comp (portPrivate_799fa192_inlCLM E ℝ)) := by
      exact (precompA : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F).contDiff
    exact ContDiff.comp_contDiffOn hpre hfd
  convert hcompOn using 1
  funext p
  exact portPrivate_799fa192_fderiv_partial_eq_comp (f := f) p
    (((hf p (Set.mem_univ _)).differentiableWithinAt (by
      norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem)

omit [CompleteSpace F] in
theorem portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral (f : E → ℝ → F)
    [ProperSpace E]
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => f p.1 p.2) Set.univ)
    (x₀ : E) :
    HasFDerivAt (fun x : E => ∫ t in (0 : ℝ)..1, f x t)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E => f y t) x₀) x₀ := by
  let Ff : E → ℝ → F := f
  let F' : E → ℝ → E →L[ℝ] F := fun x t => fderiv ℝ (fun y : E => Ff y t) x
  let s : Set E := Metric.ball x₀ 1
  have hs : s ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
  have hFcont : ∀ x : E, Continuous (fun t : ℝ => Ff x t) := by
    intro x
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    have hprodOn : ContinuousOn (fun t : ℝ => (x, t)) Set.univ := continuousOn_univ.mpr hprod
    have hcontOn := ((hf.of_le le_rfl).continuousOn.comp hprodOn (by intro t ht; trivial))
    exact continuousOn_univ.mp hcontOn
  have hF'_cont : ∀ x : E, Continuous (fun t : ℝ => F' x t) := by
    intro x
    have hpar : Continuous (fun p : E × ℝ => fderiv ℝ (fun y : E => f y p.2) p.1) :=
      continuousOn_univ.mp (portPrivate_799fa192_partial_fderiv_contDiffOn hf).continuousOn
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    exact hpar.comp hprod
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (Ff x) (volume.restrict (Ι (0 : ℝ) 1)) := by
    exact Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable)
  have hF_int : Integrable (Ff x₀) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hIcc : IntegrableOn (Ff x₀) (Set.Icc (0 : ℝ) 1) volume :=
      ContinuousOn.integrableOn_Icc
        ((continuousOn_univ.mpr (hFcont x₀)).mono (by intro t ht; trivial))
    have hIoc : IntegrableOn (Ff x₀) (Ι (0 : ℝ) 1) volume :=
      hIcc.mono_set (by intro t ht; exact (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc] using ht)))
    simpa [IntegrableOn] using hIoc
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hF'_cont x₀).aestronglyMeasurable
  have hfdCont : Continuous (fun p : E × ℝ => fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p) :=
    continuousOn_univ.mp (hf.fderiv_of_isOpen isOpen_univ
      (le_of_eq (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (↑(⊤ : ℕ∞) : WithTop ℕ∞)))).continuousOn
  have hfdNormCont : ContinuousOn (fun p : E × ℝ =>
      ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) p‖)
      ((Metric.closedBall x₀ 1 : Set E).prod (Set.Icc (0 : ℝ) 1)) :=
    (continuous_norm.comp hfdCont).continuousOn
  have hcompct : IsCompact ((Metric.closedBall x₀ 1 : Set E).prod (Set.Icc (0 : ℝ) 1)) :=
    (isCompact_closedBall (x := x₀) (r := 1)).prod isCompact_Icc
  rcases IsCompact.exists_bound_of_continuousOn hcompct hfdNormCont with ⟨M, hM⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (x₀, 0) (by
    constructor <;> simp))
  let C : ℝ := ‖(portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ * (M + 1)
  have hCbound : ∀ y ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' y t‖ ≤ C := by
    intro y hy t ht
    have hyc : y ∈ Metric.closedBall x₀ 1 := by
      have hyt : dist y x₀ ≤ 1 := le_of_lt (Metric.mem_ball.mp hy)
      exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hyt)
    have hb : ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ ≤ M := by
      simpa using hM (y, t) ⟨hyc, ht⟩
    have hcompnorm : ‖(fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)).comp (portPrivate_799fa192_inlCLM E ℝ)‖ ≤
        ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ * ‖(portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    calc
      ‖F' y t‖ = ‖(fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)).comp (portPrivate_799fa192_inlCLM E ℝ)‖ := by
        congr 1
        exact portPrivate_799fa192_fderiv_partial_eq_comp (f := f) (y, t)
          (((hf (y, t) (Set.mem_univ _)).differentiableWithinAt (by
            norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem)
      _ ≤ ‖fderiv ℝ (fun q : E × ℝ => f q.1 q.2) (y, t)‖ * ‖(portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ :=
        hcompnorm
      _ ≤ M * ‖(portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ := by
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ ‖(portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)‖ * (M + 1) := by
        nlinarith [hM0, norm_nonneg (portPrivate_799fa192_inlCLM E ℝ : E →L[ℝ] E × ℝ)]
      _ = C := by
        simp [C]
  have h_bound : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, ‖F' x t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro x hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have h0 : (0 : ℝ) ≤ t := le_of_lt (by simpa using ht.1)
      have h1 : t ≤ 1 := by simpa using ht.2
      exact ⟨h0, h1⟩
    exact hCbound x hx t htIcc
  have h_diff : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s,
      HasFDerivAt (fun y : E => Ff y t) (F' x t) x := by
    exact Eventually.of_forall (fun t => by
      intro x hx
      have hdiff : DifferentiableAt ℝ (fun y : E => Ff y t) x :=
        by
          have hdiffUnc : DifferentiableAt ℝ (fun q : E × ℝ => Ff q.1 q.2) (x, t) :=
            ((hf (x, t) (Set.mem_univ _)).differentiableWithinAt (by
              norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
          have hemb : DifferentiableAt ℝ (fun y : E => (y, t)) x := by
            have h0 : HasFDerivAt (fun y : E => (y, t)) (portPrivate_799fa192_inlCLM E ℝ) x := by
              change HasFDerivAt (fun y : E => (id y, t))
                ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x
              exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
            exact h0.differentiableAt
          exact hdiffUnc.comp x hemb
      simpa [F'] using hdiff.hasFDerivAt)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ι (0 : ℝ) 1))
    (F := Ff) (x₀ := x₀) (bound := fun _ : ℝ => C) (s := s) (F' := F')
    hs hF_meas hF_int hF'_meas h_bound
    (by
      simp) h_diff
  simpa [Ff, intervalIntegral] using hmain

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem portPrivate_799fa192_paramInt_tube
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (a b : ℝ) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc a b ⊆ S)
    (x₀ : E) (hx₀ : x₀ ∈ U) (hG : ContinuousOn G (U ×ˢ S)) :
    ∃ C : ℝ, ∀ᶠ x in nhds x₀, ∀ t ∈ Ι a b, ‖G (x, t)‖ ≤ C := by
  have hslice : ContinuousOn (fun t : ℝ ↦ ‖G (x₀, t)‖) (Set.uIcc a b) := by
    exact hG.norm.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx₀, hSI ht⟩)
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hslice
  let C : ℝ := B + 1
  have hBC : B < C := lt_add_of_pos_right B zero_lt_one
  let V : Set (E × ℝ) := (U ×ˢ S) ∩ (fun p ↦ ‖G p‖) ⁻¹' Set.Iio C
  have hV : IsOpen V := hG.norm.isOpen_inter_preimage (hU.prod hS) isOpen_Iio
  have hsub : ({x₀} : Set E) ×ˢ Set.uIcc a b ⊆ V := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hBt : ‖G (x₀, t)‖ ≤ B := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hB t ht
    exact ⟨⟨hx₀, hSI ht⟩, hBt.trans_lt hBC⟩
  obtain ⟨W, T, hW, _hT, hxW, hKT, hWT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hV hsub
  refine ⟨C, ?_⟩
  filter_upwards [hW.mem_nhds (hxW (Set.mem_singleton x₀))] with x hx t ht
  exact (hWT ⟨hx, hKT (Set.uIoc_subset_uIcc ht)⟩).2.le

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem portPrivate_799fa192_paramInt_slice
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (S : Set ℝ) (hS : IsOpen S)
    (hG : ContinuousOn G (U ×ˢ S)) (x : E) (hx : x ∈ U) :
    ContinuousOn (fun t : ℝ ↦ G (x, t)) S := by
  intro t ht
  refine (hG.continuousAt ((hU.prod hS).mem_nhds ⟨hx, ht⟩)).comp_continuousWithinAt ?_
  exact continuousWithinAt_const.prodMk continuousWithinAt_id

omit [CompleteSpace F] in
theorem portPrivate_799fa192_paramInt_fderiv
    (G : E × ℝ → F) (U : Set E) (hU : IsOpen U)
    (S : Set ℝ) (hS : IsOpen S)
    (hG : ContDiffOn ℝ 1 G (U ×ˢ S)) :
    ContDiffOn ℝ 0
      (fun p : E × ℝ ↦ fderiv ℝ (fun x : E ↦ G (x, p.2)) p.1)
      (U ×ˢ S) := by
  have hopen : IsOpen (U ×ˢ S) := hU.prod hS
  rw [hopen.contDiffOn_iff] at hG ⊢
  intro p hp
  apply ContDiffAt.fderiv (n := (1 : WithTop ℕ∞)) (m := (0 : WithTop ℕ∞))
  · exact (hG hp).comp _
      (by
        fun_prop : ContDiffAt ℝ 1
          (fun w : (E × ℝ) × E ↦ (w.2, w.1.2)) (p, p.1))
  · fun_prop
  · norm_num

omit [CompleteSpace F] in
theorem hasFDerivAt_paramInt
    (f : E → ℝ → F) (U : Set E) (hU : IsOpen U)
    (a b : ℝ) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc a b ⊆ S) (x₀ : E) (hx₀ : x₀ ∈ U)
    (hf : ContDiffOn ℝ 1 (fun p : E × ℝ ↦ f p.1 p.2) (U ×ˢ S)) :
    HasFDerivAt (fun x : E ↦ ∫ t in a..b, f x t)
      (∫ t in a..b, fderiv ℝ (fun y : E ↦ f y t) x₀) x₀ := by
  let G : E × ℝ → F := fun p ↦ f p.1 p.2
  let Gp : E × ℝ → E →L[ℝ] F := fun p ↦
    fderiv ℝ (fun y : E ↦ G (y, p.2)) p.1
  have hfG : ContDiffOn ℝ 1 G (U ×ˢ S) := by
    simpa only [G] using hf
  have hopen : IsOpen (U ×ˢ S) := hU.prod hS
  have hGc : ContinuousOn G (U ×ˢ S) := hf.continuousOn
  have hGp : ContDiffOn ℝ 0 Gp (U ×ˢ S) := by
    simpa only [Gp] using portPrivate_799fa192_paramInt_fderiv G U hU S hS hfG
  have hGpc : ContinuousOn Gp (U ×ˢ S) := hGp.continuousOn
  obtain ⟨C, hC⟩ := portPrivate_799fa192_paramInt_tube Gp U hU a b S hS hSI x₀ hx₀ hGpc
  let s : Set E := {x | ∀ t ∈ Ι a b, ‖Gp (x, t)‖ ≤ C} ∩ U
  have hs : s ∈ nhds x₀ := Filter.inter_mem hC (hU.mem_nhds hx₀)
  have hsU : s ⊆ U := Set.inter_subset_right
  have hI : ∀ t ∈ Ι a b, t ∈ S :=
    fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := volume) (F := fun x t ↦ G (x, t))
    (F' := fun x t ↦ Gp (x, t)) (bound := fun _ ↦ C)
    (x₀ := x₀) (s := s) (a := a) (b := b) hs
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    exact ((portPrivate_799fa192_paramInt_slice G U hU S hS hGc x hx).mono
      (fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
  · exact ((portPrivate_799fa192_paramInt_slice G U hU S hS hGc x₀ hx₀).mono hSI).intervalIntegrable
  · exact ((portPrivate_799fa192_paramInt_slice Gp U hU S hS hGpc x₀ hx₀).mono
      (fun t ht ↦ hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
  · rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all _ fun t ht x hx ↦ hx.1 t ht
  · exact intervalIntegrable_const
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine ae_of_all _ fun t ht x hx ↦ ?_
    have hmem : ((x, t) : E × ℝ) ∈ U ×ˢ S := ⟨hsU hx, hI t ht⟩
    have hAt : ContDiffAt ℝ 1 G (x, t) :=
      hfG.contDiffAt (hopen.mem_nhds hmem)
    have hslice : ContDiffAt ℝ 1 (fun y : E ↦ G (y, t)) x :=
      hAt.comp₂ contDiffAt_id contDiffAt_const
    simpa only [Gp, G] using (hslice.differentiableAt (by norm_num)).hasFDerivAt

omit [NormedSpace ℝ E] in
theorem paramInt_tendstoUniform
    (G : E × ℝ → F) (K U : Set E) (S : Set ℝ)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsOpen S) (h0S : 0 ∈ S)
    (hG : ContinuousOn G (U ×ˢ S)) :
    TendstoUniformlyOn
      (fun s z ↦ ∫ t in (0 : ℝ)..1, G (z, t * s))
      (fun z ↦ G (z, 0)) (𝓝 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hS 0 h0S
  let r₀ : ℝ := r / 2
  have hr₀ : 0 < r₀ := div_pos hr (by norm_num)
  let C : Set (E × ℝ) := K ×ˢ Metric.closedBall 0 r₀
  have hCcompact : IsCompact C := hK.prod (isCompact_closedBall 0 r₀)
  have hCsub : C ⊆ U ×ˢ S := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    refine ⟨hKU hz, hrS ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
    exact hs.trans_lt (by dsimp only [r₀]; linarith)
  have hGc : ContinuousOn G C := hG.mono hCsub
  have hGu : UniformContinuousOn G C :=
    hCcompact.uniformContinuousOn_of_continuous hGc
  rw [Metric.uniformContinuousOn_iff] at hGu
  obtain ⟨δ, hδ, hδG⟩ := hGu (ε / 2) (by positivity)
  filter_upwards [Metric.ball_mem_nhds 0 (lt_min hr₀ hδ)] with s hs z hz
  have hs' : |s| < min r₀ δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
  have hs_r : |s| < r₀ := hs'.trans_le (min_le_left _ _)
  have hs_δ : |s| < δ := hs'.trans_le (min_le_right _ _)
  have hpath : Continuous (fun t : ℝ ↦ (z, t * s)) :=
    continuous_const.prodMk (continuous_id.mul continuous_const)
  have hmaps : Set.MapsTo (fun t : ℝ ↦ (z, t * s)) (Set.Icc 0 1) C := by
    intro t ht
    refine ⟨hz, ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul]
    have ht_abs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    exact (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg s)).trans
      (by simpa only [one_mul] using hs_r.le)
  have hslice : ContinuousOn (fun t : ℝ ↦ G (z, t * s)) (Set.Icc 0 1) :=
    hGc.comp hpath.continuousOn hmaps
  have hslice_int : IntervalIntegrable (fun t : ℝ ↦ G (z, t * s)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hslice
  have hconst : (∫ _t : ℝ in (0 : ℝ)..1, G (z, 0)) = G (z, 0) := by
    simp
  rw [dist_eq_norm, norm_sub_rev, ← hconst,
    ← intervalIntegral.integral_sub hslice_int intervalIntegrable_const]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2)
    fun t ht ↦ ?_).trans_lt ?_
  · have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact ⟨htIoc.1.le, htIoc.2⟩
    have hzt : (z, t * s) ∈ C := hmaps htIcc
    have hz0 : (z, (0 : ℝ)) ∈ C := by
      refine ⟨hz, Metric.mem_closedBall_self hr₀.le⟩
    have hclose := (hδG _ hzt _ hz0 (by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq,
        sub_zero, abs_mul]
      have ht_abs : |t| ≤ 1 := by
        rw [abs_of_nonneg htIcc.1]
        exact htIcc.2
      exact (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg s)).trans_lt
        (by simpa only [one_mul] using hs_δ))).le
    simpa only [dist_eq_norm] using hclose
  · simpa only [abs_sub_comm, sub_zero, abs_one, mul_one] using (half_lt_self hε)

theorem contDiffOn_paramIntervalIntegral
    {E₀ : Type uE} {F₀ : Type uF}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [ProperSpace E₀] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    [CompleteSpace F₀] (f : E₀ → ℝ → F₀)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E₀ × ℝ => f p.1 p.2) Set.univ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ := by
  have hall : ∀ m : ℕ, ∀ (F' : Type (max uE uF))
      [NormedAddCommGroup F'] [NormedSpace ℝ F']
      [CompleteSpace F'], ∀ H : E₀ → ℝ → F',
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : E₀ × ℝ => H p.1 p.2) Set.univ →
      ContDiffOn ℝ (m : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ := by
    intro m
    induction m with
    | zero =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_zero]
      intro x hx
      rw [ContinuousWithinAt, nhdsWithin_univ]
      exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral H hH x).continuousAt
    | succ m ih =>
      intro F' hF'1 hF'2 hF'3 H hH
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, H x t) Set.univ
      rw [contDiffOn_succ_iff_fderivWithin (s := Set.univ) uniqueDiffOn_univ]
      constructor
      · intro x hx
        exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral H hH x).differentiableAt.differentiableWithinAt
      · constructor
        · intro hmω
          exact (WithTop.natCast_ne_top (α := ℕ∞) m hmω).elim
        · have hpar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : E₀ × ℝ => fderiv ℝ (fun y : E₀ => H y p.2) p.1) Set.univ :=
            portPrivate_799fa192_partial_fderiv_contDiffOn hH
          have hIH := ih (E₀ →L[ℝ] F')
            (fun y t => fderiv ℝ (fun z : E₀ => H z t) y) hpar
          have hfdEq : ∀ x : E₀,
              fderiv ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, H y t) x =
                ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E₀ => H y t) x := by
            intro x
            exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral H hH x).fderiv
          have hfw : (fun x : E₀ =>
              fderivWithin ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, H y t) Set.univ x) =
              (fun x : E₀ => ∫ t in (0 : ℝ)..1,
                fderiv ℝ (fun y : E₀ => H y t) x) := by
            funext x
            rw [fderivWithin_univ, hfdEq x]
          simpa [hfw] using hIH
  rw [contDiffOn_iff_forall_nat_le]
  intro m _hm
  cases m with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ
      rw [contDiffOn_zero]
      intro x hx
      rw [ContinuousWithinAt, nhdsWithin_univ]
      exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral f hf x).continuousAt
  | succ m =>
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (fun x : E₀ => ∫ t in (0 : ℝ)..1, f x t) Set.univ
      rw [contDiffOn_succ_iff_fderivWithin (s := Set.univ) uniqueDiffOn_univ]
      constructor
      · intro x hx
        exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral f hf x).differentiableAt.differentiableWithinAt
      · constructor
        · intro hmω
          exact (WithTop.natCast_ne_top (α := ℕ∞) m hmω).elim
        · have hpar : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (fun p : E₀ × ℝ => fderiv ℝ (fun y : E₀ => f y p.2) p.1) Set.univ :=
            portPrivate_799fa192_partial_fderiv_contDiffOn hf
          have hIH := hall m (E₀ →L[ℝ] F₀)
            (fun y t => fderiv ℝ (fun z : E₀ => f z t) y) hpar
          have hfdEq : ∀ x : E₀,
              fderiv ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, f y t) x =
                ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E₀ => f y t) x := by
            intro x
            exact (portPrivate_799fa192_hasFDerivAt_paramIntervalIntegral f hf x).fderiv
          have hfw : (fun x : E₀ =>
              fderivWithin ℝ (fun y : E₀ => ∫ t in (0 : ℝ)..1, f y t) Set.univ x) =
              (fun x : E₀ => ∫ t in (0 : ℝ)..1,
                fderiv ℝ (fun y : E₀ => f y t) x) := by
            funext x
            rw [fderivWithin_univ, hfdEq x]
          simpa [hfw] using hIH

open Set in
theorem continuousWithinAt_paramIntervalIntegral {F : ℝ → ℝ → ℝ} {S : Set ℝ} (hS : IsCompact S)
    (hFc : ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (S ×ˢ (univ : Set ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ContinuousWithinAt (fun t => ∫ x in (0 : ℝ)..1, F x t) S x₀ := by
  have hK : IsCompact (S ×ˢ (Icc (0 : ℝ) 1 : Set ℝ)) := hS.prod isCompact_Icc
  have hcK : ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hFc.mono (Set.prod_mono Subset.rfl (Set.subset_univ _))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcK
  have hslice : ∀ t ∈ S, Continuous (fun x : ℝ => F x t) := by
    intro t ht
    have hcomp : ContinuousOn (fun x : ℝ => F x t) (univ : Set ℝ) :=
      hFc.comp (ContinuousOn.prodMk continuousOn_const continuousOn_id)
        (fun x _ => ⟨ht, mem_univ x⟩)
    exact continuousOn_univ.mp hcomp
  have hslice2 : ∀ ρ : ℝ, ContinuousOn (fun τ : ℝ => F ρ τ) S := fun ρ =>
    hFc.comp (ContinuousOn.prodMk continuousOn_id continuousOn_const)
      (fun τ hτ => ⟨hτ, mem_univ ρ⟩)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (μ := volume) (X := ℝ) (E := ℝ)
    (F := fun t x => F x t) (x₀ := x₀) (bound := fun _ => C) (a := 0) (b := 1)
    (s := S) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hslice t ht).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    refine Eventually.of_forall fun t ht => ?_
    exact hC (x, t) ⟨hx, by simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using Set.uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall fun ρ _ => (hslice2 ρ).continuousWithinAt hx₀

open Set in
theorem portPrivate_799fa192_hasDerivWithinAt_unitIntervalIntegral {F G : ℝ → ℝ → ℝ} {s u : ℝ}
    (hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((univ : Set ℝ) ×ˢ Icc s u))
    (hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) ((univ : Set ℝ) ×ˢ Icc s u))
    (hderiv : ∀ x t, t ∈ Icc s u → HasDerivWithinAt (fun τ => F x τ) (G x t) (Icc s u) t) :
    ∀ t ∈ Icc s u, HasDerivWithinAt (fun τ => ∫ x in (0 : ℝ)..1, F x τ)
      (∫ x in (0 : ℝ)..1, G x t) (Icc s u) t := by
  have hFslice : ∀ τ ∈ Icc s u, Continuous (fun x : ℝ => F x τ) := by
    intro τ hτ
    exact continuousOn_univ.mp (hFc.comp
      (ContinuousOn.prodMk continuousOn_id continuousOn_const)
      (fun x _ => ⟨mem_univ x, hτ⟩))
  have hGslice : ∀ τ ∈ Icc s u, Continuous (fun x : ℝ => G x τ) := by
    intro τ hτ
    exact continuousOn_univ.mp (hGc.comp
      (ContinuousOn.prodMk continuousOn_id continuousOn_const)
      (fun x _ => ⟨mem_univ x, hτ⟩))
  have hGslice2 : ∀ x : ℝ, ContinuousOn (fun ρ : ℝ => G x ρ) (Icc s u) := fun x =>
    hGc.comp (ContinuousOn.prodMk continuousOn_const continuousOn_id)
      (fun ρ hρ => ⟨mem_univ x, hρ⟩)
  have hGc' : ContinuousOn (fun p : ℝ × ℝ => G p.2 p.1) (Icc s u ×ˢ (univ : Set ℝ)) :=
    hGc.comp (ContinuousOn.prodMk continuousOn_snd continuousOn_fst)
      (fun p hp => ⟨mem_univ p.2, hp.1⟩)
  have hΦcont : ContinuousOn (fun τ => ∫ x in (0 : ℝ)..1, G x τ) (Icc s u) := fun τ hτ =>
    continuousWithinAt_paramIntervalIntegral isCompact_Icc hGc' hτ
  intro t ht
  have hFTC : ∀ (x τ : ℝ), τ ∈ Icc s u → (∫ ρ in t..τ, G x ρ) = F x τ - F x t := by
    intro x τ hτ
    have hsub : uIcc t τ ⊆ Icc s u := by
      intro ρ hρ
      exact ⟨le_trans (le_min ht.1 hτ.1) hρ.1, le_trans hρ.2 (max_le ht.2 hτ.2)⟩
    have hsub' : Ioo (min t τ) (max t τ) ⊆ Ioo s u := by
      intro ρ hρ
      exact ⟨lt_of_le_of_lt (le_min ht.1 hτ.1) hρ.1,
        lt_of_lt_of_le hρ.2 (max_le ht.2 hτ.2)⟩
    have hFcontOn : ContinuousOn (fun ρ => F x ρ) (Icc s u) :=
      fun ρ hρ => (hderiv x ρ hρ).continuousWithinAt
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right ?_ ?_ ?_
    · exact hFcontOn.mono hsub
    · intro ρ hρ
      have hρ' := hsub' hρ
      exact ((hderiv x ρ ⟨hρ'.1.le, hρ'.2.le⟩).hasDerivAt
        (Icc_mem_nhds hρ'.1 hρ'.2)).hasDerivWithinAt
    · exact ((hGslice2 x).mono hsub).intervalIntegrable
  have hstep : ∀ τ ∈ Icc s u,
      (∫ x in (0 : ℝ)..1, F x τ) - (∫ x in (0 : ℝ)..1, F x t)
        = ∫ ρ in t..τ, ∫ x in (0 : ℝ)..1, G x ρ := by
    intro τ hτ
    have h1 : (∫ x in (0 : ℝ)..1, F x τ) - (∫ x in (0 : ℝ)..1, F x t)
        = ∫ x in (0 : ℝ)..1, (F x τ - F x t) :=
      (intervalIntegral.integral_sub ((hFslice τ hτ).intervalIntegrable 0 1)
        ((hFslice t ht).intervalIntegrable 0 1)).symm
    have h2 : (∫ x in (0 : ℝ)..1, (F x τ - F x t))
        = ∫ x in (0 : ℝ)..1, ∫ ρ in t..τ, G x ρ :=
      intervalIntegral.integral_congr fun x _ => (hFTC x τ hτ).symm
    have h3 : (∫ x in (0 : ℝ)..1, ∫ ρ in t..τ, G x ρ)
        = ∫ ρ in t..τ, ∫ x in (0 : ℝ)..1, G x ρ := by
      refine intervalIntegral_intervalIntegral_swap ?_
      have hcompact : IsCompact (uIcc (0 : ℝ) 1 ×ˢ uIcc t τ) :=
        isCompact_uIcc.prod isCompact_uIcc
      have hcont : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
          (uIcc (0 : ℝ) 1 ×ˢ uIcc t τ) :=
        hGc.mono (Set.prod_mono (Set.subset_univ _) (by
          intro ρ hρ
          exact ⟨le_trans (le_min ht.1 hτ.1) hρ.1, le_trans hρ.2 (max_le ht.2 hτ.2)⟩))
      have h := (hcont.integrableOn_compact (μ := volume) hcompact).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
      exact h
    exact h1.trans (h2.trans h3)
  have hsub_self : uIcc t t ⊆ Icc s u := by
    intro ρ hρ
    have hρt : ρ = t := by simpa [Set.uIcc_self] using hρ
    exact hρt ▸ ht
  have hΦint : IntervalIntegrable (fun τ => ∫ x in (0 : ℝ)..1, G x τ) volume t t :=
    ContinuousOn.intervalIntegrable (μ := volume) (hΦcont.mono hsub_self)
  have hprim : HasDerivWithinAt (fun τ => ∫ ρ in t..τ, ∫ x in (0 : ℝ)..1, G x ρ)
      (∫ x in (0 : ℝ)..1, G x t) (Icc s u) t :=
    @intervalIntegral.integral_hasDerivWithinAt_right ℝ _ _ _
      (fun τ => ∫ x in (0 : ℝ)..1, G x τ) t t hΦint (Icc s u) (Icc s u)
      (@intervalIntegral.FTCFilter.nhdsIcc t s u ⟨ht⟩)
      (ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin hΦcont measurableSet_Icc t)
      (hΦcont.continuousWithinAt ht)
  refine (hprim.const_add (∫ x in (0 : ℝ)..1, F x t)).congr ?_ ?_
  · intro y hy
    linarith [hstep y hy]
  · linarith [hstep t ht]

open Set in
theorem hasDerivWithinAt_paramIntervalIntegral_on_interval {F G : ℝ → ℝ → ℝ} {s u p q : ℝ}
    (hpq : p ≤ q)
    (hFc : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hGc : ContinuousOn (fun z : ℝ × ℝ => G z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hderiv : ∀ x ∈ Icc p q, ∀ t ∈ Icc s u,
      HasDerivWithinAt (fun τ => F x τ) (G x t) (Icc s u) t) :
    ∀ t ∈ Icc s u, HasDerivWithinAt (fun τ => ∫ x in p..q, F x τ)
      (∫ x in p..q, G x t) (Icc s u) t := by
  let ψ := fun x : ℝ => p + (q - p) * (projIcc (0 : ℝ) 1 zero_le_one x : ℝ)
  have hψ : ∀ x, ψ x ∈ Icc p q := by
    intro x
    have hx := (projIcc (0 : ℝ) 1 zero_le_one x).property
    dsimp only [ψ]
    constructor <;> nlinarith only [hx.1, hx.2, hpq]
  have hψcont : Continuous ψ := by unfold ψ; fun_prop
  have harg : Continuous (fun z : ℝ × ℝ => (ψ z.1, z.2)) :=
    (hψcont.comp continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo (fun z : ℝ × ℝ => (ψ z.1, z.2)) (univ ×ˢ Icc s u) (Icc p q ×ˢ Icc s u) :=
    fun z hz => ⟨hψ z.1, hz.2⟩
  have h := portPrivate_799fa192_hasDerivWithinAt_unitIntervalIntegral
    (F := fun x t => F (ψ x) t) (G := fun x t => G (ψ x) t)
    (hFc.comp harg.continuousOn hmaps) (hGc.comp harg.continuousOn hmaps)
    (fun x t ht => hderiv (ψ x) (hψ x) t ht)
  have hchange (f : ℝ → ℝ) :
      (q - p) * (∫ x in (0 : ℝ)..1, f (ψ x)) = ∫ x in p..q, f x := by
    have heq : (∫ x in (0 : ℝ)..1, f (ψ x)) = ∫ x in (0 : ℝ)..1, f (p + (q - p) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      simp only [ψ, projIcc_of_mem zero_le_one hx']
    rw [heq]
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, add_sub_cancel] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f (q - p) p
  intro t ht
  have hd := (h t ht).const_mul (q - p)
  rw [hchange (fun x => G x t)] at hd
  have heq : (fun τ => (q - p) * ∫ x in (0 : ℝ)..1, F (ψ x) τ) =
      (fun τ => ∫ x in p..q, F x τ) := funext (fun τ => hchange (fun x => F x τ))
  rw [heq] at hd
  exact hd

open Set in
theorem hasDerivWithinAt_paramIntervalIntegral {F G : ℝ → ℝ → ℝ} {s u : ℝ}
    (hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((univ : Set ℝ) ×ˢ Icc s u))
    (hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) ((univ : Set ℝ) ×ˢ Icc s u))
    (hderiv : ∀ x t, t ∈ Icc s u → HasDerivWithinAt (fun τ => F x τ) (G x t) (Icc s u) t) :
    ∀ t ∈ Icc s u, HasDerivWithinAt (fun τ => ∫ x in (0 : ℝ)..1, F x τ)
      (∫ x in (0 : ℝ)..1, G x t) (Icc s u) t :=
  hasDerivWithinAt_paramIntervalIntegral_on_interval zero_le_one
    (hFc.mono (Set.prod_mono (Set.subset_univ _) Subset.rfl))
    (hGc.mono (Set.prod_mono (Set.subset_univ _) Subset.rfl))
    (fun x _ t ht => hderiv x t ht)

end DifferentialGeometry.Analysis.Calculus
