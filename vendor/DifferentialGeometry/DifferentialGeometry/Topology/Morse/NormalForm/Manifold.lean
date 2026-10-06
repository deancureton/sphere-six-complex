module

public import DifferentialGeometry.Topology.Morse.NormalForm.Euclidean
public import DifferentialGeometry.Topology.Morse.Attachment.ModelCell
public import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Local
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.QuadraticForm.Real

@[expose] public section

open scoped Topology Manifold

namespace DifferentialGeometry.Topology.Morse

open Filter
open Set
open DifferentialGeometry.Analysis
open CellAttachment

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem portPrivate_3bdbf777_fderiv_fderiv_translate_of_contDiffOn (g : E → ℝ) (c : E) (r : ℝ)
    (hr : 0 < r) (hg : ContDiffOn ℝ 2 g (Metric.ball c r)) :
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) 0 = fderiv ℝ (fderiv ℝ g) c := by
  have hfun : (fun z : E => fderiv ℝ (fun z : E => g (z + c)) z) =ᶠ[nhds (0 : E)]
      fun z : E => fderiv ℝ g (z + c) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hz
    have hmem : z + c ∈ Metric.ball c r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hdiff : DifferentiableAt ℝ g (z + c) := by
      have h1 : DifferentiableOn ℝ g (Metric.ball c r) :=
        hg.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      exact (h1 (z + c) hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    exact fderiv_translate g c z hdiff
  have hfder : fderiv ℝ (fun z : E => fderiv ℝ (fun z : E => g (z + c)) z) (0 : E) =
      fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) (0 : E) := hfun.fderiv_eq
  have hd1 : ContDiffOn ℝ 1 (fderiv ℝ g) (Metric.ball c r) :=
    hg.fderiv_of_isOpen Metric.isOpen_ball (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hd : DifferentiableAt ℝ (fderiv ℝ g) c := by
    have hmem : c ∈ Metric.ball c r := by
      simp [Metric.mem_ball, hr]
    have hd1' : DifferentiableWithinAt ℝ (fderiv ℝ g) (Metric.ball c r) c :=
      (hd1 c hmem).differentiableWithinAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hd1'.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hlast : fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) (0 : E) = fderiv ℝ (fderiv ℝ g) c := by
    simpa using fderiv_translate (fderiv ℝ g) c (0 : E) (by simpa using hd)
  rw [hfder, hlast]

theorem portPrivate_3bdbf777_hessian_linearPullback_at_critical {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (σ : F →L[ℝ] E) (hf : ContDiff ℝ 2 f)
    (u v : F) :
    (fderiv ℝ (fderiv ℝ (fun x : F => f (σ x))) (0 : F)) u v =
    (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := by
  have hfun : (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) =
      fun x : F => (fderiv ℝ f (σ x)).comp σ := by
    funext x
    have hdσ : DifferentiableAt ℝ σ x := σ.differentiableAt
    have hdf : DifferentiableAt ℝ f (σ x) :=
      (hf.contDiffAt (x := σ x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    have h := fderiv_comp x (g := f) (f := σ) (hg := hdf) (hf := hdσ)
    calc
      fderiv ℝ (fun x : F => f (σ x)) x = fderiv ℝ (f ∘ σ) x := rfl
      _ = (fderiv ℝ f (σ x)).comp (fderiv ℝ σ x) := h
      _ = (fderiv ℝ f (σ x)).comp σ := by rw [σ.fderiv]
  have hfder : fderiv ℝ (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) (0 : F) =
      fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F) := by rw [hfun]
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (0 : E) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
      hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have h1' : DifferentiableWithinAt ℝ (fderiv ℝ f) Set.univ (0 : E) :=
      (h1 (0 : E) (Set.mem_univ (0 : E))).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)
    exact h1'.differentiableAt Filter.univ_mem |> fun h => h.hasFDerivAt
  have hA0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (σ (0 : F)) := by
    simpa [map_zero] using hA
  have hg : HasFDerivAt (fun x : F => fderiv ℝ f (σ x))
      ((fderiv ℝ (fderiv ℝ f) 0).comp σ) (0 : F) :=
    HasFDerivAt.comp (x := (0 : F)) (g := fderiv ℝ f)
      (g' := fderiv ℝ (fderiv ℝ f) 0) (f := σ) (f' := σ) (hg := hA0)
      (hf := (σ.hasFDerivAt : HasFDerivAt σ σ (0 : F)))
  have hC : HasFDerivAt (fun L : E →L[ℝ] ℝ => L.comp σ)
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ) (fderiv ℝ f (σ (0 : F))) := by
    have hh : HasFDerivAt ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ)
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ) (fderiv ℝ f (σ (0 : F))) :=
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).hasFDerivAt
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun L => by rfl)
  have hcomp2 : HasFDerivAt (fun x : F => (fderiv ℝ f (σ x)).comp σ)
      (((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) (0 : F) := by
    have hfun' : (fun x : F => (fderiv ℝ f (σ x)).comp σ) =
        (fun L : E →L[ℝ] ℝ => L.comp σ) ∘ (fun x : F => fderiv ℝ f (σ x)) := rfl
    simpa [hfun'] using (HasFDerivAt.comp (x := (0 : F))
      (g := fun L : E →L[ℝ] ℝ => L.comp σ)
      (g' := (ContinuousLinearMap.compL ℝ F E ℝ).flip σ)
      (f := fun x : F => fderiv ℝ f (σ x))
      (f' := (fderiv ℝ (fderiv ℝ f) 0).comp σ) (hg := hC) (hf := hg))
  have hder : fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F) =
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp ((fderiv ℝ (fderiv ℝ f) 0).comp σ) :=
    hcomp2.fderiv
  have hmain : ((((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp
      ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) u) v = (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
  calc
    (fderiv ℝ (fderiv ℝ (fun x : F => f (σ x))) (0 : F)) u v
        = (fderiv ℝ (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) (0 : F)) u v := rfl
    _ = (fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F)) u v := by rw [hfder]
    _ = ((((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp
          ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) u) v := by rw [hder]
    _ = (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := hmain

theorem portPrivate_3bdbf777_associated_weightedSumSquares_apply {n : ℕ} (w : Fin n → ℝ) (u v : Fin n → ℝ) :
    QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w) u v =
      ∑ i : Fin n, w i * u i * v i := by
  calc
    QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w) u v
        = QuadraticMap.associated (R := ℝ)
            (∑ i : Fin n, w i • QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v := by
      rw [QuadraticMap.weightedSumSquares]
    _ = (∑ i : Fin n, w i • QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i)) u v := by
      simp [map_sum]
    _ = ∑ i : Fin n, w i • (QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v) := by
      simp
    _ = ∑ i : Fin n, w i * u i * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hA : QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v = u i * v i := by
        rw [QuadraticMap.proj]
        rw [QuadraticMap.associated_linMulLin]
        simp [LinearMap.proj_apply]
        ring_nf
      rw [hA]
      rw [smul_eq_mul]
      ring

theorem fderiv_fderiv_eq_associated_chartHessian (f : E → ℝ) (hf : ContDiff ℝ 2 f) (a b : E) :
    (fderiv ℝ (fderiv ℝ f) 0 a) b =
      QuadraticMap.associated (R := ℝ) (chartHessian f) a b := by
  have hQ : ∀ x : E, chartHessian f x = (fderiv ℝ (fderiv ℝ f) 0 x) x := by
    intro x
    rfl
  have hs : IsSymmSndFDerivAt ℝ f 0 := by
    exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm : (fderiv ℝ (fderiv ℝ f) 0 a) b = (fderiv ℝ (fderiv ℝ f) 0 b) a :=
    IsSymmSndFDerivAt.eq hs a b
  have htwoL : 2 * (fderiv ℝ (fderiv ℝ f) 0 a) b =
      (fderiv ℝ (fderiv ℝ f) 0 (a + b)) (a + b) - (fderiv ℝ (fderiv ℝ f) 0 a) a -
        (fderiv ℝ (fderiv ℝ f) 0 b) b := by
    have hba : (fderiv ℝ (fderiv ℝ f) 0 (a + b)) (a + b) =
        (fderiv ℝ (fderiv ℝ f) 0 a) a + (fderiv ℝ (fderiv ℝ f) 0 a) b +
          (fderiv ℝ (fderiv ℝ f) 0 b) a + (fderiv ℝ (fderiv ℝ f) 0 b) b := by
      simp [map_add]
      ring
    rw [hba, hsymm]
    ring
  have htwoR : 2 * QuadraticMap.associated (R := ℝ) (chartHessian f) a b =
      chartHessian f (a + b) - chartHessian f a - chartHessian f b := by
    have htwo := QuadraticMap.two_nsmul_associated (R := ℝ) (S := ℝ) (chartHessian f)
    have hxy : ((2 • QuadraticMap.associatedHom (R := ℝ) (S := ℝ) (chartHessian f)) a b) =
        ((chartHessian f).polarBilin a b) :=
      congrArg (fun F : LinearMap.BilinMap ℝ E ℝ => F a b) htwo
    change 2 • QuadraticMap.associated (R := ℝ) (chartHessian f) a b =
      (chartHessian f).polarBilin a b at hxy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at hxy
    simpa [nsmul_eq_mul] using hxy
  have hmain : 2 * (fderiv ℝ (fderiv ℝ f) 0 a) b =
      2 * QuadraticMap.associated (R := ℝ) (chartHessian f) a b := by
    rw [htwoR, hQ]
    exact htwoL
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain

theorem portPrivate_3bdbf777_morseLemma {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    (f : M → ℝ) (p : M)
    (hg : ContDiffOn ℝ (n + 3) (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p).target)
    (hcrit : fderiv ℝ (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft) :
    ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
      ContDiffAt ℝ 1 (ψ : MorseModel n → MorseModel n) 0 ∧
      ContDiffAt ℝ 1 (ψ.symm : MorseModel n → MorseModel n) 0 ∧
      ∃ w : Fin n → ℝ,
        (∀ i, w i = -1 ∨ w i = 1) ∧
        {i : Fin n | w i < 0}.ncard =
          sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) ∧
        ∃ L : MorseModel n ≃ₗ[ℝ] MorseModel n,
          ∀ y ∈ ψ.target,
            f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ y))) =
              f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  let gp : MorseModel n → ℝ := fun y => f ((extChartAt I p).symm y)
  let e : MorseModel n := extChartAt I p p
  let g₀ : MorseModel n → ℝ := fun z => gp (z + e)
  have he_mem : e ∈ (extChartAt I p).target := by
    dsimp [e]
    exact (extChartAt I p).map_source (mem_extChartAt_source p)
  have htarget_open : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  rcases (Metric.isOpen_iff.mp htarget_open) e he_mem with ⟨r, hr, hball⟩
  have hg₀ : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ (n + 3) g₀ (Metric.ball (0 : MorseModel n) r) := by
    refine ⟨r, hr, ?_⟩
    have htrans : ContDiffOn ℝ (n + 3) (fun z : MorseModel n => z + e)
        (Metric.ball (0 : MorseModel n) r) := by
      exact ((contDiff_id : ContDiff ℝ (n + 3) (fun z : MorseModel n => z)).add
        (contDiff_const : ContDiff ℝ (n + 3) fun _ : MorseModel n => e)).contDiffOn
    have hsub : Set.MapsTo (fun z : MorseModel n => z + e) (Metric.ball (0 : MorseModel n) r)
        (extChartAt I p).target := by
      intro x hx
      have hxe : x + e ∈ Metric.ball e r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      exact hball hxe
    have hcomp' : ContDiffOn ℝ (n + 3) (fun z : MorseModel n => gp (z + e))
        (Metric.ball (0 : MorseModel n) r) :=
      hg.comp htrans hsub
    simpa [g₀, gp, Function.comp_def] using hcomp'
  have hcrit₀ : fderiv ℝ g₀ 0 = 0 := by
    have hd : DifferentiableAt ℝ gp e := by
      have h2 : ContDiffOn ℝ 2 gp (extChartAt I p).target :=
        hg.of_le (by exact_mod_cast (by omega : 2 ≤ n + 3))
      have hd1' : DifferentiableWithinAt ℝ gp (extChartAt I p).target e :=
        (h2 e he_mem).differentiableWithinAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
      exact hd1'.differentiableAt (htarget_open.mem_nhds he_mem)
    have htr := fderiv_translate gp e (0 : MorseModel n) (by simpa using hd)
    have hmain : fderiv ℝ (fun z : MorseModel n => gp (z + e)) 0 = 0 := by
      rw [htr]
      rw [zero_add]
      change fderiv ℝ (fun y : MorseModel n => f ((extChartAt I p).symm y))
        (extChartAt I p p) = 0
      exact hcrit
    simpa [g₀] using hmain
  rcases exists_contDiff_extension (n + 3 : ℕ∞) g₀ (0 : MorseModel n) hg₀ with
    ⟨g1, hg1, hg1Eq⟩
  have hcrit₁ : fderiv ℝ g1 0 = 0 := by
    have hfd : fderiv ℝ g1 0 = fderiv ℝ g₀ 0 := hg1Eq.fderiv_eq
    simpa [hcrit₀] using hfd
  have hchart₁ : chartHessian g1 = chartHessian g₀ := by
    have hS : {x : MorseModel n | g1 x = g₀ x} ∈ nhds (0 : MorseModel n) := hg1Eq
    rcases mem_nhds_iff.mp hS with ⟨U, hUg, hUopen, hU0⟩
    have hfd2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1 x) 0 =
        fderiv ℝ (fun x : MorseModel n => fderiv ℝ g₀ x) 0 := by
      have hfdU : ∀ x ∈ U, fderiv ℝ g1 x = fderiv ℝ g₀ x := by
        intro x hx
        have hgU : g1 =ᶠ[nhds x] g₀ := by
          change {y : MorseModel n | g1 y = g₀ y} ∈ nhds x
          exact Filter.mem_of_superset (hUopen.mem_nhds hx) (by intro y hy; exact hUg hy)
        exact hgU.fderiv_eq
      have hfdEq : (fun x : MorseModel n => fderiv ℝ g1 x) =ᶠ[nhds (0 : MorseModel n)]
          fun x => fderiv ℝ g₀ x := by
        filter_upwards [hUopen.mem_nhds hU0] with x hx
        exact hfdU x hx
      exact hfdEq.fderiv_eq
    have hb : chartHessianBilinAt g1 0 = chartHessianBilinAt g₀ 0 := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ g1) 0 y) z = (fderiv ℝ (fderiv ℝ g₀) 0 y) z := by
        rw [hfd2]
      simpa [chartHessianBilinAt] using hc
    change (chartHessianBilinAt g1 0).toQuadraticMap = (chartHessianBilinAt g₀ 0).toQuadraticMap
    rw [hb]
  have hchart₀ : chartHessian g₀ = chartHessianAt gp e := by
    have h2 : ContDiffOn ℝ 2 gp (Metric.ball e r) :=
      (hg.mono (by intro x hx; exact hball hx)).of_le (by exact_mod_cast (by omega : 2 ≤ n + 3))
    have htr := portPrivate_3bdbf777_fderiv_fderiv_translate_of_contDiffOn gp e r hr h2
    have hb : chartHessianBilinAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianBilinAt gp e := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ (fun z : MorseModel n => gp (z + e))) 0 y) z =
          (fderiv ℝ (fderiv ℝ gp) e y) z := by
        rw [htr]
      simpa [chartHessianBilinAt] using hc
    change chartHessianAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianAt gp e
    dsimp [chartHessianAt, chartHessian]
    rw [hb]
  have hnd₁ : (QuadraticMap.associated (R := ℝ) (chartHessian g1)).SeparatingLeft := by
    rw [hchart₁, hchart₀]
    simpa [e, gp] using hnd
  rcases chartHessian_weightedSumSquares_normalForm g1 hnd₁ with ⟨w', hw', hEq, hsig⟩
  rcases hEq with ⟨L0⟩
  have hfin : Module.finrank ℝ (MorseModel n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : Fin n ≃ Fin (Module.finrank ℝ (MorseModel n)) :=
    Equiv.cast (congrArg Fin hfin.symm)
  let w : Fin n → ℝ := fun i => w' (e0 i)
  have hw : ∀ i : Fin n, w i = -1 ∨ w i = 1 := by
    intro i
    dsimp [w]
    exact hw' (e0 i)
  let τ' : MorseModel n ≃ₗ[ℝ] (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ e0.symm
  let σe : MorseModel n ≃ₗ[ℝ] MorseModel n :=
    τ'.trans (L0.symm : (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) ≃ₗ[ℝ] MorseModel n)
  let σ : MorseModel n →L[ℝ] MorseModel n :=
    σe.toContinuousLinearEquiv.toContinuousLinearMap
  let L : MorseModel n ≃ₗ[ℝ] MorseModel n := σe.symm
  let h : MorseModel n → ℝ := fun u => g1 (σ u)
  have hh : ContDiff ℝ (n + 3) h := by
    dsimp [h]
    exact hg1.comp (σ.contDiff : ContDiff ℝ (n + 3) σ)
  have hcrit_h : fderiv ℝ h 0 = 0 := by
    dsimp [h]
    have hdσ : DifferentiableAt ℝ σ 0 := σ.differentiableAt
    have hd1 : DifferentiableAt ℝ g1 (σ 0) :=
      (hg1.contDiffAt (x := σ (0 : MorseModel n))).differentiableAt
        (by exact_mod_cast (by omega : n + 3 ≠ 0))
    have hcomp' := fderiv_comp (x := (0 : MorseModel n)) (g := g1) (f := σ)
      (hg := hd1) (hf := hdσ)
    have hmain : fderiv ℝ (g1 ∘ σ) 0 = 0 := by
      rw [hcomp', σ.fderiv]
      have hσ0 : σ (0 : MorseModel n) = 0 := by simp
      rw [hσ0, hcrit₁]
      simp
    simpa [h, Function.comp_def] using hmain
  have hLσ : ∀ x : MorseModel n, L.symm x = σ x := by
    intro x
    dsimp [σ, L, σe]
    rfl
  have hg1₂ : ContDiff ℝ 2 g1 := by
    have hle1 : (2 : ℕ) ≤ n + 3 := by omega
    have hle2 : (2 : ℕ∞) ≤ (↑n + 3 : ℕ∞) := by
      exact (WithTop.coe_le_coe (α := ℕ) (a := (n + 3 : ℕ)) (b := (2 : ℕ))).mpr hle1
    exact hg1.of_le ((WithTop.coe_le_coe (α := ℕ∞) (a := (↑n + 3 : ℕ∞)) (b := ((2 : ℕ) : ℕ∞))).mpr hle2)
  have hdiag_h : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ h) 0 u) v = ∑ i : Fin n, w i * u i * v i := by
    intro u v
    change (fderiv ℝ (fderiv ℝ (fun x : MorseModel n => g1 (σ x))) 0 u) v =
      ∑ i : Fin n, w i * u i * v i
    have hpb := portPrivate_3bdbf777_hessian_linearPullback_at_critical g1 σ hg1₂ u v
    have h1 := fderiv_fderiv_eq_associated_chartHessian g1 hg1₂ (σ u) (σ v)
    have hmain : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
        ∑ i : Fin n, w i * u i * v i := by
      have hq' : (QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap = chartHessian g1 := by
        apply QuadraticMap.ext
        intro x
        simp [QuadraticMap.comp_apply]
      have hc := QuadraticMap.associated_comp (R := ℝ) (S := ℝ)
        (Q := QuadraticMap.weightedSumSquares ℝ w') (f := L0.toLinearMap)
      have hc' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
          (QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w')).compl₁₂
            L0.toLinearMap L0.toLinearMap := by
        have hq'' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
            QuadraticMap.associated (R := ℝ) ((QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap) :=
          (congrArg (QuadraticMap.associated (R := ℝ)) hq').symm
        rw [hq'']
        exact hc
      have hev := congrArg (fun F : LinearMap.BilinMap ℝ (MorseModel n) ℝ => F (σ u) (σ v)) hc'
      have hL0σ : ∀ x : MorseModel n, L0 (σ x) = τ' x := by
        intro x
        simp [σ, σe, LinearEquiv.trans_apply]
      have h1' : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
          QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) := by
        simpa [LinearMap.compl₁₂_apply, hL0σ] using hev
      have hre : QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) =
          ∑ i : Fin n, w i * u i * v i := by
        have hre0 : (∑ i : Fin n, w i * u i * v i) =
            ∑ j : Fin (Module.finrank ℝ (MorseModel n)), w' j * (u (e0.symm j)) * (v (e0.symm j)) := by
          refine Fintype.sum_equiv e0 (fun i => w i * u i * v i)
            (fun j => w' j * (u (e0.symm j)) * (v (e0.symm j))) ?_
          intro i
          dsimp [w]
          rw [Equiv.symm_apply_apply e0 i]
        have has := portPrivate_3bdbf777_associated_weightedSumSquares_apply w' (τ' u) (τ' v)
        rw [has]
        have hτu : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' u j = u (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        have hτv : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' v j = v (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        simp_rw [hτu, hτv]
        exact hre0.symm
      rw [h1', hre]
    rw [hpb]
    rw [h1]
    exact hmain
  rcases Completion.morse_lemma_diagonal n h hh hcrit_h w hw hdiag_h
    with ⟨ψ, hψsource, hψtarget, hψ0, hψsmooth, hψsymmSmooth, hψnorm⟩
  rcases mem_nhds_iff.mp hg1Eq with ⟨U, hUg, hUopen, hU0⟩
  let D : Set (MorseModel n) := ψ.target ∩ (fun y => σ (ψ y)) ⁻¹' U
  have hD : D ∈ nhds (0 : MorseModel n) := by
    dsimp [D]
    have h1 : ψ.target ∈ nhds (0 : MorseModel n) := IsOpen.mem_nhds ψ.open_target hψtarget
    have h2 : (fun y : MorseModel n => σ (ψ y)) ⁻¹' U ∈ nhds (0 : MorseModel n) := by
      have hσc : ContinuousAt σ (ψ (0 : MorseModel n)) := σ.cont.continuousAt
      have hcont : ContinuousAt (fun y : MorseModel n => σ (ψ y)) (0 : MorseModel n) :=
        (ContinuousAt.comp (g := σ) (f := ψ) (x := (0 : MorseModel n))
          (hσc : ContinuousAt σ (ψ (0 : MorseModel n))) (ψ.continuousAt hψsource))
      have hval : U ∈ nhds (σ (ψ (0 : MorseModel n))) := by
        have hσ0 : σ (0 : MorseModel n) = 0 := by simp
        simpa [hψ0, hσ0] using (IsOpen.mem_nhds hUopen hU0)
      exact hcont.preimage_mem_nhds hval
    exact Filter.inter_mem h1 h2
  let φ : OpenPartialHomeomorph (MorseModel n) (MorseModel n) := ψ.restr (ψ ⁻¹' D)
  have hW : ψ ⁻¹' D ∈ nhds (0 : MorseModel n) := by
    have hD0 : D ∈ nhds (ψ (0 : MorseModel n)) := by
      simpa [hψ0] using hD
    exact (ψ.continuousAt hψsource).preimage_mem_nhds hD0
  have hφsource0 : (0 : MorseModel n) ∈ φ.source := by
    dsimp [φ]
    constructor
    · exact hψsource
    · exact (mem_interior_iff_mem_nhds).2 hW
  have hψsymm0 : ψ.symm 0 = 0 := by
    have hrinv : ψ (ψ.symm 0) = 0 := ψ.right_inv hψtarget
    have hψeq : ψ (ψ.symm 0) = ψ 0 := by
      simpa [hψ0] using hrinv
    exact (ψ.injOn (ψ.map_target hψtarget) hψsource hψeq)
  have hφtarget0 : (0 : MorseModel n) ∈ φ.target := by
    dsimp [φ]
    constructor
    · exact hψtarget
    · have hW0 : ψ ⁻¹' D ∈ nhds (ψ.symm (0 : MorseModel n)) := by
        simpa [hψsymm0] using hW
      exact (mem_interior_iff_mem_nhds).2 hW0
  have hφ0 : φ 0 = 0 := by
    calc
      φ 0 = ψ 0 := by rfl
      _ = 0 := hψ0
  have hsig' : {i : Fin n | w i < 0}.ncard =
      sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
    have hn : {i : Fin n | w i < 0}.ncard =
        {j : Fin (Module.finrank ℝ (MorseModel n)) | w' j < 0}.ncard := by
      refine Set.ncard_congr (fun i _ => e0 i) ?_ ?_ ?_
      · intro i hi
        change w' (e0 i) < 0
        exact hi
      · intro a b _ _ h
        exact e0.injective h
      · intro j hj
        refine ⟨e0.symm j, ?_, ?_⟩
        · change w' (e0 (e0.symm j)) < 0
          rw [e0.apply_symm_apply]
          exact hj
        · exact e0.apply_symm_apply j
    rw [hn, ← hchart₀, ← hchart₁]
    simpa [gp] using hsig
  refine ⟨φ, hφsource0, hφtarget0, hφ0, ?_, ?_, w, hw, hsig', ?_⟩
  · exact hψsmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by rfl)
  · exact hψsymmSmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by rfl)
  refine ⟨L, ?_⟩
  intro y hy
  have hyAnd : y ∈ ψ.target ∧ ψ.symm y ∈ interior (ψ ⁻¹' D) := by
    dsimp [φ] at hy
    exact hy
  have hyD : y ∈ D := by
    have hWs : ψ.symm y ∈ ψ ⁻¹' D := interior_subset hyAnd.2
    have hΘsV : ψ (ψ.symm y) ∈ D := hWs
    have hΘs : ψ (ψ.symm y) = y := ψ.right_inv hyAnd.1
    rw [hΘs] at hΘsV
    exact hΘsV
  have hσψy : σ (ψ y) ∈ U := hyD.2
  have hpoint : extChartAt I p p + L.symm (φ y) = e + σ (ψ y) := by
    dsimp [e]
    have hφy : φ y = ψ y := by rfl
    rw [hφy, hLσ]
  have hnorm := hψnorm y hyAnd.1
  have h0 : h 0 = f p := by
    have hσ0 : σ (0 : MorseModel n) = 0 := by simp
    calc
      h 0 = g1 (σ 0) := rfl
      _ = g1 0 := by rw [hσ0]
      _ = g₀ 0 := hUg hU0
      _ = gp (0 + e) := rfl
      _ = gp e := by simp
      _ = f ((extChartAt I p).symm (extChartAt I p p)) := rfl
      _ = f p := by
        exact congrArg f ((extChartAt I p).left_inv (mem_extChartAt_source p))
  calc
    f ((extChartAt I p).symm (extChartAt I p p + L.symm (φ y)))
        = f ((extChartAt I p).symm (e + σ (ψ y))) := by rw [hpoint]
    _ = gp (e + σ (ψ y)) := rfl
    _ = g₀ (σ (ψ y)) := by
      dsimp [g₀]
      rw [add_comm]
    _ = g1 (σ (ψ y)) := (hUg hσψy).symm
    _ = h (ψ y) := rfl
    _ = h 0 + (1 / 2) * ∑ i : Fin n, w i * y i * y i := hnorm
    _ = f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by rw [h0]

theorem morse_lemma_smooth {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] (f : M → ℝ) (p : M)
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p).target)
    (hcrit : fderiv ℝ (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft) :
    ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) 0 ∧
      (∃ v : Set (MorseModel n), IsOpen v ∧ (0 : MorseModel n) ∈ v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) (ψ '' v)) ∧
      ∃ w : Fin n → ℝ,
        (∀ i, w i = -1 ∨ w i = 1) ∧
        {i : Fin n | w i < 0}.ncard =
          sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) ∧
        ∃ L : MorseModel n ≃ₗ[ℝ] MorseModel n,
          ∀ y ∈ ψ.target,
            f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ y))) =
              f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  let gp : MorseModel n → ℝ := fun y => f ((extChartAt I p).symm y)
  let e : MorseModel n := extChartAt I p p
  let g₀ : MorseModel n → ℝ := fun z => gp (z + e)
  have he_mem : e ∈ (extChartAt I p).target := by
    dsimp [e]
    exact (extChartAt I p).map_source (mem_extChartAt_source p)
  have htarget_open : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  rcases (Metric.isOpen_iff.mp htarget_open) e he_mem with ⟨r, hr, hball⟩
  have hg₀ : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₀ (Metric.ball (0 : MorseModel n) r) := by
    refine ⟨r, hr, ?_⟩
    have htrans : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => z + e)
        (Metric.ball (0 : MorseModel n) r) := by
      exact ((contDiff_id : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => z)).add
        (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) fun _ : MorseModel n => e)).contDiffOn
    have hsub : Set.MapsTo (fun z : MorseModel n => z + e) (Metric.ball (0 : MorseModel n) r)
        (extChartAt I p).target := by
      intro x hx
      have hxe : x + e ∈ Metric.ball e r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      exact hball hxe
    have hcomp' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => gp (z + e))
        (Metric.ball (0 : MorseModel n) r) :=
      hg.comp htrans hsub
    simpa [g₀, gp, Function.comp_def] using hcomp'
  have hcrit₀ : fderiv ℝ g₀ 0 = 0 := by
    have hd : DifferentiableAt ℝ gp e := by
      have h2 : ContDiffOn ℝ 2 gp (extChartAt I p).target :=
        hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      have hd1' : DifferentiableWithinAt ℝ gp (extChartAt I p).target e :=
        (h2 e he_mem).differentiableWithinAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
      exact hd1'.differentiableAt (htarget_open.mem_nhds he_mem)
    have htr := fderiv_translate gp e (0 : MorseModel n) (by simpa using hd)
    have hmain : fderiv ℝ (fun z : MorseModel n => gp (z + e)) 0 = 0 := by
      rw [htr]
      rw [zero_add]
      change fderiv ℝ (fun y : MorseModel n => f ((extChartAt I p).symm y))
        (extChartAt I p p) = 0
      exact hcrit
    simpa [g₀] using hmain
  rcases exists_contDiff_extension (⊤ : ℕ∞) g₀ (0 : MorseModel n) hg₀ with
    ⟨g1, hg1, hg1Eq⟩
  have hcrit₁ : fderiv ℝ g1 0 = 0 := by
    have hfd : fderiv ℝ g1 0 = fderiv ℝ g₀ 0 := hg1Eq.fderiv_eq
    simpa [hcrit₀] using hfd
  have hchart₁ : chartHessian g1 = chartHessian g₀ := by
    have hS : {x : MorseModel n | g1 x = g₀ x} ∈ nhds (0 : MorseModel n) := hg1Eq
    rcases mem_nhds_iff.mp hS with ⟨U, hUg, hUopen, hU0⟩
    have hfd2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1 x) 0 =
        fderiv ℝ (fun x : MorseModel n => fderiv ℝ g₀ x) 0 := by
      have hfdU : ∀ x ∈ U, fderiv ℝ g1 x = fderiv ℝ g₀ x := by
        intro x hx
        have hgU : g1 =ᶠ[nhds x] g₀ := by
          change {y : MorseModel n | g1 y = g₀ y} ∈ nhds x
          exact Filter.mem_of_superset (hUopen.mem_nhds hx) (by intro y hy; exact hUg hy)
        exact hgU.fderiv_eq
      have hfdEq : (fun x : MorseModel n => fderiv ℝ g1 x) =ᶠ[nhds (0 : MorseModel n)]
          fun x => fderiv ℝ g₀ x := by
        filter_upwards [hUopen.mem_nhds hU0] with x hx
        exact hfdU x hx
      exact hfdEq.fderiv_eq
    have hb : chartHessianBilinAt g1 0 = chartHessianBilinAt g₀ 0 := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ g1) 0 y) z = (fderiv ℝ (fderiv ℝ g₀) 0 y) z := by
        rw [hfd2]
      simpa [chartHessianBilinAt] using hc
    change (chartHessianBilinAt g1 0).toQuadraticMap = (chartHessianBilinAt g₀ 0).toQuadraticMap
    rw [hb]
  have hchart₀ : chartHessian g₀ = chartHessianAt gp e := by
    have h2 : ContDiffOn ℝ 2 gp (Metric.ball e r) :=
      (hg.mono (by intro x hx; exact hball hx)).of_le (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have htr := portPrivate_3bdbf777_fderiv_fderiv_translate_of_contDiffOn gp e r hr h2
    have hb : chartHessianBilinAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianBilinAt gp e := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ (fun z : MorseModel n => gp (z + e))) 0 y) z =
          (fderiv ℝ (fderiv ℝ gp) e y) z := by
        rw [htr]
      simpa [chartHessianBilinAt] using hc
    change chartHessianAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianAt gp e
    dsimp [chartHessianAt, chartHessian]
    rw [hb]
  have hnd₁ : (QuadraticMap.associated (R := ℝ) (chartHessian g1)).SeparatingLeft := by
    rw [hchart₁, hchart₀]
    simpa [e, gp] using hnd
  rcases chartHessian_weightedSumSquares_normalForm g1 hnd₁ with ⟨w', hw', hEq, hsig⟩
  rcases hEq with ⟨L0⟩
  have hfin : Module.finrank ℝ (MorseModel n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : Fin n ≃ Fin (Module.finrank ℝ (MorseModel n)) :=
    Equiv.cast (congrArg Fin hfin.symm)
  let w : Fin n → ℝ := fun i => w' (e0 i)
  have hw : ∀ i : Fin n, w i = -1 ∨ w i = 1 := by
    intro i
    dsimp [w]
    exact hw' (e0 i)
  let τ' : MorseModel n ≃ₗ[ℝ] (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ e0.symm
  let σe : MorseModel n ≃ₗ[ℝ] MorseModel n :=
    τ'.trans (L0.symm : (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) ≃ₗ[ℝ] MorseModel n)
  let σ : MorseModel n →L[ℝ] MorseModel n :=
    σe.toContinuousLinearEquiv.toContinuousLinearMap
  let L : MorseModel n ≃ₗ[ℝ] MorseModel n := σe.symm
  let h : MorseModel n → ℝ := fun u => g1 (σ u)
  have hh : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) h := by
    dsimp [h]
    exact hg1.comp (σ.contDiff : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) σ)
  have hcrit_h : fderiv ℝ h 0 = 0 := by
    dsimp [h]
    have hdσ : DifferentiableAt ℝ σ 0 := σ.differentiableAt
    have hd1 : DifferentiableAt ℝ g1 (σ 0) :=
      (hg1.contDiffAt (x := σ (0 : MorseModel n))).differentiableAt
        (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hcomp' := fderiv_comp (x := (0 : MorseModel n)) (g := g1) (f := σ)
      (hg := hd1) (hf := hdσ)
    have hmain : fderiv ℝ (g1 ∘ σ) 0 = 0 := by
      rw [hcomp', σ.fderiv]
      have hσ0 : σ (0 : MorseModel n) = 0 := by simp
      rw [hσ0, hcrit₁]
      simp
    simpa [h, Function.comp_def] using hmain
  have hLσ : ∀ x : MorseModel n, L.symm x = σ x := by
    intro x
    dsimp [σ, L, σe]
    rfl
  have hg1₂ : ContDiff ℝ 2 g1 :=
    hg1.of_le (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hdiag_h : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ h) 0 u) v = ∑ i : Fin n, w i * u i * v i := by
    intro u v
    change (fderiv ℝ (fderiv ℝ (fun x : MorseModel n => g1 (σ x))) 0 u) v =
      ∑ i : Fin n, w i * u i * v i
    have hpb := portPrivate_3bdbf777_hessian_linearPullback_at_critical g1 σ hg1₂ u v
    have h1 := fderiv_fderiv_eq_associated_chartHessian g1 hg1₂ (σ u) (σ v)
    have hmain : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
        ∑ i : Fin n, w i * u i * v i := by
      have hq' : (QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap = chartHessian g1 := by
        apply QuadraticMap.ext
        intro x
        simp [QuadraticMap.comp_apply]
      have hc := QuadraticMap.associated_comp (R := ℝ) (S := ℝ)
        (Q := QuadraticMap.weightedSumSquares ℝ w') (f := L0.toLinearMap)
      have hc' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
          (QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w')).compl₁₂
            L0.toLinearMap L0.toLinearMap := by
        have hq'' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
            QuadraticMap.associated (R := ℝ) ((QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap) :=
          (congrArg (QuadraticMap.associated (R := ℝ)) hq').symm
        rw [hq'']
        exact hc
      have hev := congrArg (fun F : LinearMap.BilinMap ℝ (MorseModel n) ℝ => F (σ u) (σ v)) hc'
      have hL0σ : ∀ x : MorseModel n, L0 (σ x) = τ' x := by
        intro x
        simp [σ, σe, LinearEquiv.trans_apply]
      have h1' : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
          QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) := by
        simpa [LinearMap.compl₁₂_apply, hL0σ] using hev
      have hre : QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) =
          ∑ i : Fin n, w i * u i * v i := by
        have hre0 : (∑ i : Fin n, w i * u i * v i) =
            ∑ j : Fin (Module.finrank ℝ (MorseModel n)), w' j * (u (e0.symm j)) * (v (e0.symm j)) := by
          refine Fintype.sum_equiv e0 (fun i => w i * u i * v i)
            (fun j => w' j * (u (e0.symm j)) * (v (e0.symm j))) ?_
          intro i
          dsimp [w]
          rw [Equiv.symm_apply_apply e0 i]
        have has := portPrivate_3bdbf777_associated_weightedSumSquares_apply w' (τ' u) (τ' v)
        rw [has]
        have hτu : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' u j = u (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        have hτv : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' v j = v (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        simp_rw [hτu, hτv]
        exact hre0.symm
      rw [h1', hre]
    rw [hpb]
    rw [h1]
    exact hmain
  rcases Completion.morse_lemma_diagonal_smooth n h hh hcrit_h w hw hdiag_h
    with ⟨ψ, hψsource, hψtarget, hψ0, hψsmooth, hψsymmSmooth, hψLocal, hψnorm⟩
  rcases mem_nhds_iff.mp hg1Eq with ⟨U, hUg, hUopen, hU0⟩
  let D : Set (MorseModel n) := ψ.target ∩ (fun y => σ (ψ y)) ⁻¹' U
  have hD : D ∈ nhds (0 : MorseModel n) := by
    dsimp [D]
    have h1 : ψ.target ∈ nhds (0 : MorseModel n) := IsOpen.mem_nhds ψ.open_target hψtarget
    have h2 : (fun y : MorseModel n => σ (ψ y)) ⁻¹' U ∈ nhds (0 : MorseModel n) := by
      have hσc : ContinuousAt σ (ψ (0 : MorseModel n)) := σ.cont.continuousAt
      have hcont : ContinuousAt (fun y : MorseModel n => σ (ψ y)) (0 : MorseModel n) :=
        (ContinuousAt.comp (g := σ) (f := ψ) (x := (0 : MorseModel n))
          (hσc : ContinuousAt σ (ψ (0 : MorseModel n))) (ψ.continuousAt hψsource))
      have hval : U ∈ nhds (σ (ψ (0 : MorseModel n))) := by
        have hσ0 : σ (0 : MorseModel n) = 0 := by simp
        simpa [hψ0, hσ0] using (IsOpen.mem_nhds hUopen hU0)
      exact hcont.preimage_mem_nhds hval
    exact Filter.inter_mem h1 h2
  let φ : OpenPartialHomeomorph (MorseModel n) (MorseModel n) := ψ.restr (ψ ⁻¹' D)
  have hW : ψ ⁻¹' D ∈ nhds (0 : MorseModel n) := by
    have hD0 : D ∈ nhds (ψ (0 : MorseModel n)) := by
      simpa [hψ0] using hD
    exact (ψ.continuousAt hψsource).preimage_mem_nhds hD0
  have hφsource0 : (0 : MorseModel n) ∈ φ.source := by
    dsimp [φ]
    constructor
    · exact hψsource
    · exact (mem_interior_iff_mem_nhds).2 hW
  have hψsymm0 : ψ.symm 0 = 0 := by
    have hrinv : ψ (ψ.symm 0) = 0 := ψ.right_inv hψtarget
    have hψeq : ψ (ψ.symm 0) = ψ 0 := by
      simpa [hψ0] using hrinv
    exact (ψ.injOn (ψ.map_target hψtarget) hψsource hψeq)
  have hφtarget0 : (0 : MorseModel n) ∈ φ.target := by
    dsimp [φ]
    constructor
    · exact hψtarget
    · have hW0 : ψ ⁻¹' D ∈ nhds (ψ.symm (0 : MorseModel n)) := by
        simpa [hψsymm0] using hW
      exact (mem_interior_iff_mem_nhds).2 hW0
  have hφ0 : φ 0 = 0 := by
    calc
      φ 0 = ψ 0 := by rfl
      _ = 0 := hψ0
  have hsig' : {i : Fin n | w i < 0}.ncard =
      sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
    have hn : {i : Fin n | w i < 0}.ncard =
        {j : Fin (Module.finrank ℝ (MorseModel n)) | w' j < 0}.ncard := by
      refine Set.ncard_congr (fun i _ => e0 i) ?_ ?_ ?_
      · intro i hi
        change w' (e0 i) < 0
        exact hi
      · intro a b _ _ h
        exact e0.injective h
      · intro j hj
        refine ⟨e0.symm j, ?_, ?_⟩
        · change w' (e0 (e0.symm j)) < 0
          rw [e0.apply_symm_apply]
          exact hj
        · exact e0.apply_symm_apply j
    rw [hn, ← hchart₀, ← hchart₁]
    simpa [gp] using hsig
  refine ⟨φ, hφsource0, hφtarget0, hφ0, ?_, ?_, ?_, w, hw, hsig', ?_⟩
  · exact hψsmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by rfl)
  · exact hψsymmSmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by rfl)
  · exact hψLocal
  refine ⟨L, ?_⟩
  intro y hy
  have hyAnd : y ∈ ψ.target ∧ ψ.symm y ∈ interior (ψ ⁻¹' D) := by
    dsimp [φ] at hy
    exact hy
  have hyD : y ∈ D := by
    have hWs : ψ.symm y ∈ ψ ⁻¹' D := interior_subset hyAnd.2
    have hΘsV : ψ (ψ.symm y) ∈ D := hWs
    have hΘs : ψ (ψ.symm y) = y := ψ.right_inv hyAnd.1
    rw [hΘs] at hΘsV
    exact hΘsV
  have hσψy : σ (ψ y) ∈ U := hyD.2
  have hpoint : extChartAt I p p + L.symm (φ y) = e + σ (ψ y) := by
    dsimp [e]
    have hφy : φ y = ψ y := by rfl
    rw [hφy, hLσ]
  have hnorm := hψnorm y hyAnd.1
  have h0 : h 0 = f p := by
    have hσ0 : σ (0 : MorseModel n) = 0 := by simp
    calc
      h 0 = g1 (σ 0) := rfl
      _ = g1 0 := by rw [hσ0]
      _ = g₀ 0 := hUg hU0
      _ = gp (0 + e) := rfl
      _ = gp e := by simp
      _ = f ((extChartAt I p).symm (extChartAt I p p)) := rfl
      _ = f p := by
        exact congrArg f ((extChartAt I p).left_inv (mem_extChartAt_source p))
  calc
    f ((extChartAt I p).symm (extChartAt I p p + L.symm (φ y)))
        = f ((extChartAt I p).symm (e + σ (ψ y))) := by rw [hpoint]
    _ = gp (e + σ (ψ y)) := rfl
    _ = g₀ (σ (ψ y)) := by
      dsimp [g₀]
      rw [add_comm]
    _ = g1 (σ (ψ y)) := (hUg hσψy).symm
    _ = h (ψ y) := rfl
    _ = h 0 + (1 / 2) * ∑ i : Fin n, w i * y i * y i := hnorm
    _ = f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by rw [h0]

theorem morse_lemma_of_contMDiff {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft) :
    ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) 0 ∧
      (∃ v : Set (MorseModel n), IsOpen v ∧ (0 : MorseModel n) ∈ v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) (ψ '' v)) ∧
      ∃ w : Fin n → ℝ,
        (∀ i, w i = -1 ∨ w i = 1) ∧
        {i : Fin n | w i < 0}.ncard =
          sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) ∧
        ∃ L : MorseModel n ≃ₗ[ℝ] MorseModel n,
          ∀ y ∈ ψ.target,
            f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ y))) =
              f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  have hg : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (extChartAt I p).symm) (extChartAt I p).target :=
    hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)
  exact morse_lemma_smooth I f p ((contMDiffOn_iff_contDiffOn).1 hg) hcrit hnd

theorem isCriticalPointAt_iff_chart_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (E) H)
    [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) :
    IsCriticalPointAt I f p ↔
      fderiv ℝ (fun y : E => f ((extChartAt I p).symm y))
        (extChartAt I p p) = 0 := by
  let e : PartialEquiv M (E) := extChartAt I p
  have hpsrc : p ∈ e.source := by simp [e]
  have hep : e.symm (e p) = p := e.left_inv hpsrc
  have hσc : ContMDiffAt 𝓘(ℝ, E) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm (e p) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt (by
      have hmemTarget : e p ∈ (extChartAt I p).target :=
        (extChartAt I p).map_source (mem_extChartAt_source p)
      simpa [e] using (isOpen_extChartAt_target p).mem_nhds hmemTarget)
  have hσmd : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e p) :=
    hσc.mdifferentiableAt (by norm_num)
  have hmdChart : MDifferentiableAt I 𝓘(ℝ, E) e p :=
    (contMDiffAt_extChartAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p)).mdifferentiableAt (by norm_num)
  have hmdgAtEp : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm (e p)) := by
    simpa [hep] using ((hf p).mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
  have hfuneq : (fun x : M => f x) =ᶠ[nhds p] (fun x : M => (f ∘ e.symm) (e x)) := by
    have hsrcopen : IsOpen e.source := isOpen_extChartAt_source p
    exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hpsrc))
      (fun x hx => congrArg f (e.left_inv hx).symm)
  have hcomp := mfderiv_comp (x := p) (g := f ∘ e.symm) (f := e) (hg := by
    have hfg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (f ∘ e.symm) (e p) := by
      have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ e.symm) (e p) :=
        ContMDiffAt.comp (x := e p) (g := f) (f := e.symm)
          (hg := by simpa [hep] using (hf p))
          (hf := hσc)
      exact hc.mdifferentiableAt (by norm_num)
    exact hfg) (hf := hmdChart)
  have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
  have hmain : mfderiv I 𝓘(ℝ, ℝ) f p =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ e.symm) (e p)).comp
        (mfderiv I 𝓘(ℝ, E) e p) := by
    exact heq.trans hcomp
  constructor
  · intro hcrit
    have hcomp2 := mfderiv_comp (x := e p) (g := f) (f := e.symm) (hg := hmdgAtEp) (hf := hσmd)
    rw [hep] at hcomp2
    have hzero2 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (f ∘ e.symm) (e p) = 0 := by
      rw [hcomp2, hcrit]
      ext v
      rfl
    exact ((mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ)
      (f := fun y : E => f (e.symm y)) (x := e p)).symm).trans hzero2
  · intro hchart
    have hzero : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (fun y : E => f (e.symm y)) (e p) = 0 := by
      exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ)
        (f := fun y : E => f (e.symm y)) (x := e p)).trans hchart
    change mfderiv I 𝓘(ℝ, ℝ) f p = 0
    rw [hmain]
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (fun y : E => f (e.symm y)) (e p)).comp
        (mfderiv I 𝓘(ℝ, E) e p) = 0
    rw [hzero]
    simp

theorem isCriticalPointAt_iff_fderiv_of_localInverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (E) H)
    {x : M} {σ : M → E} {τ : E → M} {h : E → ℝ}
    (hleft : (τ ∘ σ) =ᶠ[nhds x] id)
    (hright : (σ ∘ τ) =ᶠ[nhds (σ x)] id)
    (hσmd : MDifferentiableAt I 𝓘(ℝ, E) σ x)
    (hτmd : MDifferentiableAt 𝓘(ℝ, E) I τ (σ x))
    (hh : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) h (σ x)) :
    IsCriticalPointAt I (h ∘ σ) x ↔ fderiv ℝ h (σ x) = 0 := by
  have hτσx : τ (σ x) = x := hleft.eq_of_nhds
  have hσmd' : MDifferentiableAt I 𝓘(ℝ, E) σ (τ (σ x)) := by
    simpa [hτσx] using hσmd
  have hcompA : (mfderiv I 𝓘(ℝ, E) σ x).comp
      (mfderiv 𝓘(ℝ, E) I τ (σ x)) =
      ContinuousLinearMap.id ℝ (E) := by
    have hcomp' := mfderiv_comp (x := σ x) (g := σ) (f := τ) (hg := hσmd') (hf := hτmd)
    rw [mfderiv_eq_fderiv] at hcomp'
    have hcompPoint : (σ ∘ τ) (σ x) = σ x := hright.eq_of_nhds
    rw [hτσx] at hcomp'
    rw [hcompPoint] at hcomp'
    have heq := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hright
    rw [heq] at hcomp'
    simpa only [fderiv_id, ContinuousLinearMap.id_comp,
      ContinuousLinearEquiv.coe_symm_comp_coe] using! hcomp'.symm
  have hA_surj : Function.Surjective (mfderiv I 𝓘(ℝ, E) σ x) := by
    intro v
    refine ⟨(mfderiv 𝓘(ℝ, E) I τ (σ x)) v, ?_⟩
    simpa using! (DFunLike.congr_fun hcompA v)
  have hmain : mfderiv I 𝓘(ℝ, ℝ) (h ∘ σ) x =
      (fderiv ℝ h (σ x)).comp (mfderiv I 𝓘(ℝ, E) σ x) := by
    have hcomp' := mfderiv_comp (x := x) (g := h) (f := σ)
      (hg := hh.mdifferentiableAt (by norm_num)) (hf := hσmd)
    rw [mfderiv_eq_fderiv] at hcomp'
    exact hcomp'
  constructor
  · intro hcrit
    change mfderiv I 𝓘(ℝ, ℝ) (h ∘ σ) x = 0 at hcrit
    have hzero : (fderiv ℝ h (σ x)).comp
        (mfderiv I 𝓘(ℝ, E) σ x) = 0 := by
      rwa [← hmain]
    ext v
    rcases hA_surj v with ⟨w, hw⟩
    calc
      fderiv ℝ h (σ x) v =
          fderiv ℝ h (σ x) ((mfderiv I 𝓘(ℝ, E) σ x) w) := by rw [hw]
      _ = ((fderiv ℝ h (σ x)).comp
          (mfderiv I 𝓘(ℝ, E) σ x)) w := rfl
      _ = 0 := by
        rw [hzero]
        simp
  · intro hfd
    change mfderiv I 𝓘(ℝ, ℝ) (h ∘ σ) x = 0
    rw [hmain]
    ext v
    change fderiv ℝ h (σ x) ((mfderiv I 𝓘(ℝ, E) σ x) v) = 0
    rw [hfd]
    rfl

theorem morse_lemma {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k) :
    ∃ R : ℝ, 0 < R ∧
    ∃ Φ : OpenPartialHomeomorph (MorseModel n) M,
      0 ∈ Φ.source ∧ p ∈ Φ.target ∧ Φ 0 = p ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ Φ.source) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (Φ y) = morseNormalForm hk (f p) y) ∧
      ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 ∧
      ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ.symm p ∧
      ∃ R' : ℝ, 0 < R' ∧
        ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ (Metric.ball (0 : MorseModel n) R') ∧
        ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ.symm (Φ '' Metric.ball (0 : MorseModel n) R') := by
  have hcrit : IsCriticalPointAt I f p := hnd.1
  have hcritChart : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0 :=
    (isCriticalPointAt_iff_chart_fderiv I f hf p).1 hcrit
  have hndChart : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft := hnd.2
  rcases morse_lemma_of_contMDiff I f hf p hcritChart hndChart
    with ⟨ψ, hψsource, hψtarget, hψ0, hψsmooth, hψsymmSmooth, hψLocal, w, hw, hsig, L, hnormal⟩
  have hcard : {i : Fin n | w i < 0}.ncard = k := by
    exact hsig.trans hindex
  rcases exists_reindexEquiv hk w hw hcard with ⟨σe, hwneg, hwpos⟩
  let e₀ : MorseModel n := extChartAt I p p
  let Lh : MorseModel n ≃ₜ MorseModel n := L.symm.toContinuousLinearEquiv.toHomeomorph
  let chart : OpenPartialHomeomorph (MorseModel n) M :=
    { toPartialEquiv := (extChartAt I p).symm
      open_source := isOpen_extChartAt_target p
      open_target := isOpen_extChartAt_source p
      continuousOn_toFun := continuousOn_extChartAt_symm p
      continuousOn_invFun := continuousOn_extChartAt p }
  let κ : OpenPartialHomeomorph (MorseModel n) M :=
    ((ψ.trans (Lh.toOpenPartialHomeomorph)).trans
      ((addHomeo n e₀).toOpenPartialHomeomorph)).trans
      chart
  let T : MorseModel n ≃ₜ MorseModel n := reindexHomeo σe
  let Φ : OpenPartialHomeomorph (MorseModel n) M :=
    (T.toOpenPartialHomeomorph).trans κ
  let S : Set (MorseModel n) := κ.source ∩ ψ.target
  have hSopen : IsOpen S := κ.open_source.inter ψ.open_target
  have hS0 : (0 : MorseModel n) ∈ S := by
    dsimp [S]
    constructor
    · have h1 : (0 : MorseModel n) ∈ (ψ.trans (Lh.toOpenPartialHomeomorph)).source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hψsource, by simp⟩
      have h2 : (0 : MorseModel n) ∈
          ((ψ.trans (Lh.toOpenPartialHomeomorph)).trans
            ((addHomeo n e₀).toOpenPartialHomeomorph)).source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨h1, ?_⟩
        simp
      have h3 : (0 : MorseModel n) ∈ κ.source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨h2, ?_⟩
        have hval : ((ψ.trans (Lh.toOpenPartialHomeomorph)).trans
            ((addHomeo n e₀).toOpenPartialHomeomorph)) 0 = e₀ := by
          have hL0 : Lh 0 = 0 := by
            dsimp [Lh]
            exact L.symm.map_zero
          simp [addHomeo, OpenPartialHomeomorph.trans_apply, hψ0, hL0,
            add_zero]
        change ((ψ.trans (Lh.toOpenPartialHomeomorph)).trans
          ((addHomeo n e₀).toOpenPartialHomeomorph)) 0 ∈ chart.source
        rw [hval]
        change e₀ ∈ (extChartAt I p).target
        dsimp [e₀]
        exact (extChartAt I p).map_source (mem_extChartAt_source p)
      exact h3
    · exact hψtarget
  have hTpre : IsOpen (T ⁻¹' S) := T.continuous.isOpen_preimage S hSopen
  have hT0 : (0 : MorseModel n) ∈ T ⁻¹' S := by
    apply Set.mem_preimage.mpr
    rw [show T (0 : MorseModel n) = 0 by dsimp [T]; simp [reindexHomeo]]
    exact hS0
  rcases (Metric.isOpen_iff.mp hTpre) 0 hT0 with ⟨r, hr, hrball⟩
  let R : ℝ := r / 2
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRlt : R < r := by dsimp [R]; linarith
  have hball : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ T ⁻¹' S := by
    intro y hy
    have hsup : ‖y‖ ≤ R := le_trans (supNorm_le_morseNorm y) hy
    have hmem : y ∈ Metric.ball (0 : MorseModel n) r := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact hrball hmem
  have hΦsource : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ Φ.source := by
    intro y hy
    have hyS : T y ∈ S := (Set.mem_preimage.mp (hball y hy))
    have hyκ : T y ∈ κ.source := hyS.1
    dsimp [Φ]
    simp [hyκ]
  have hΦsource0 : (0 : MorseModel n) ∈ Φ.source := by
    have hmemR : morseNorm n 0 ≤ R := by
      simp [morseNorm, le_of_lt hRpos]
    exact hΦsource 0 hmemR
  have hκ0val : κ 0 = p := by
    have hL0 : Lh 0 = 0 := by dsimp [Lh]; exact L.symm.map_zero
    dsimp [κ]
    simp [chart, addHomeo, hψ0, hL0, e₀]
  have hT0val : T 0 = 0 := by
    dsimp [T]
    funext i
    simp [reindexHomeo]
  have hΦtarget0 : p ∈ Φ.target := by
    have hκ0src : (0 : MorseModel n) ∈ κ.source := hS0.1
    have hκp : p ∈ κ.target := by
      rw [← hκ0val]
      exact κ.map_source hκ0src
    dsimp [Φ]
    rw [OpenPartialHomeomorph.trans_target]
    constructor
    · exact hκp
    · simp
  have hΦ0 : Φ 0 = p := by
    dsimp [Φ]
    simp [hT0val, hκ0val]
  have hκfun : (κ : MorseModel n → M) =
      fun y => chart ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))) := by
    dsimp [κ]
    funext y
    rfl
  have hnormal' : ∀ y : MorseModel n, morseNorm n y ≤ R → f (Φ y) = morseNormalForm hk (f p) y := by
    intro y hy
    have hyS : T y ∈ S := (Set.mem_preimage.mp (hball y hy))
    have hyT : T y ∈ ψ.target := hyS.2
    have hwf : f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ (T y)))) =
        f p + (1 / 2) * ∑ i : Fin n, w i * (T y i) * (T y i) := hnormal (T y) hyT
    have hwf' : f (κ (T y)) = f p + (1 / 2) * ∑ i : Fin n, w i * (T y i) * (T y i) := by
      rw [hκfun]
      change f ((extChartAt I p).symm (e₀ + L.symm (ψ (T y)))) =
        f p + (1 / 2) * ∑ i : Fin n, w i * (T y i) * (T y i)
      exact hwf
    have hTval : ∀ i : Fin n, T y i = y (σe.symm i) := by
      intro i
      dsimp [T]
      rfl
    have hwsum : (∑ i : Fin n, w i * (T y i) * (T y i)) =
        (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
      calc
        (∑ i : Fin n, w i * (T y i) * (T y i))
            = (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hTval i]
              ring
        _ = (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) :=
          w_sum_reindexed hk w σe hwneg hwpos y
    have hwf'' : f (κ (T y)) = f p + (1 / 2) * ((∑ i : Fin k, - (y (negIdx hk i)) ^ 2) +
        (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)) := by
      rw [hwf']
      exact congrArg (fun s : ℝ => f p + (1 / 2 : ℝ) * s) hwsum
    dsimp [Φ]
    change f (κ (T y)) = morseNormalForm hk (f p) y
    rw [hwf'']
    rfl
  have hΦfun : (Φ : MorseModel n → M) = fun y => κ (T y) := by
    dsimp [Φ]
    funext y
    rfl
  have hLh0 : Lh 0 = 0 := by dsimp [Lh]; exact L.symm.map_zero
  have hTmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (T : MorseModel n → MorseModel n) 0 := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T : MorseModel n → MorseModel n) := by
      dsimp [T]
      apply contDiff_pi'
      intro i
      change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => y (σe.symm i))
      rw [show (fun y : MorseModel n => y (σe.symm i)) =
        (ContinuousLinearMap.proj (σe.symm i) : MorseModel n →L[ℝ] ℝ) by rfl]
      exact (ContinuousLinearMap.proj (σe.symm i) : MorseModel n →L[ℝ] ℝ).contDiff
    exact hc.contDiffAt.contMDiffAt
  have hLhmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Lh : MorseModel n → MorseModel n) 0 := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => L.symm z) :=
      (L.symm.toContinuousLinearEquiv : MorseModel n →L[ℝ] MorseModel n).contDiff
    simpa [Lh] using hc.contDiffAt.contMDiffAt
  have haddmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (addHomeo n e₀ : MorseModel n → MorseModel n) 0 := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => e₀ + z) := by
      exact (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : MorseModel n => e₀)).add contDiff_id
    simpa [addHomeo] using hc.contDiffAt.contMDiffAt
  have hchartmd : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (chart : MorseModel n → M) e₀ := by
    have he₀ : e₀ ∈ (extChartAt I p).target := by
      dsimp [e₀]
      exact (extChartAt I p).map_source (mem_extChartAt_source p)
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) (extChartAt I p).symm e₀ :=
      (contMDiffOn_extChartAt_symm p).contMDiffAt (by
        exact (isOpen_extChartAt_target p).mem_nhds he₀)
    simpa [chart] using hc
  have hψmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (ψ : MorseModel n → MorseModel n) 0 := hψsmooth.contMDiffAt
  have hκmd : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (κ : MorseModel n → M) 0 := by
    have hLh1 : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Lh : MorseModel n → MorseModel n) (ψ (0 : MorseModel n)) := by
      simpa [hψ0] using hLhmd
    have hψLh : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : MorseModel n => Lh (ψ y)) 0 :=
      ContMDiffAt.comp (x := 0) (g := (Lh : MorseModel n → MorseModel n)) (f := ψ)
        (hg := hLh1) (hf := hψmd)
    have hψLh0 : Lh (ψ 0) = 0 := by simp [hψ0, hLh0]
    have hadd1 : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ (0 : MorseModel n))) := by
      simpa [hψLh0] using haddmd
    have hψLhadd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : MorseModel n => (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))) 0 :=
      ContMDiffAt.comp (x := 0) (g := (addHomeo n e₀ : MorseModel n → MorseModel n))
        (f := fun y : MorseModel n => Lh (ψ y)) (hg := hadd1) (hf := hψLh)
    have hψLhadd0 : (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ 0)) = e₀ := by
      simp [hψLh0, addHomeo]
    have hchart1 : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (chart : MorseModel n → M) ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ (0 : MorseModel n)))) := by
      simpa [hψLhadd0] using hchartmd
    have hκ0 : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : MorseModel n => chart ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)))) 0 :=
      ContMDiffAt.comp (x := 0) (g := (chart : MorseModel n → M))
        (f := fun y : MorseModel n => (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)))
        (hg := hchart1) (hf := hψLhadd)
    rw [hκfun]
    exact hκ0
  have hΦmd : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ : MorseModel n → M) 0 := by
    have hT1 : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (T : MorseModel n → MorseModel n) 0 :=
      hTmd
    have hκT0 : ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (κ : MorseModel n → M) (T (0 : MorseModel n)) := by
      simpa [hT0val] using hκmd
    have hcomp := ContMDiffAt.comp (x := 0) (g := (κ : MorseModel n → M)) (f := T)
      (hg := hκT0) (hf := hT1)
    rw [hΦfun]
    exact hcomp
  have hΦsymm : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ.symm : M → MorseModel n) p := by
    have hΦsymmfun : (Φ.symm : M → MorseModel n) = fun x => T.symm (κ.symm x) := by
      dsimp [Φ]
      funext x
      rfl
    have hκsymmfun : (κ.symm : M → MorseModel n) =
        fun x => ψ.symm (Lh.symm ((addHomeo n e₀).symm (chart.symm x))) := by
      dsimp [κ]
      funext x
      rfl
    have hψsymm0 : ψ.symm 0 = 0 := by
      have hlinv : ψ (ψ.symm 0) = 0 := ψ.right_inv hψtarget
      have hψeq : ψ (ψ.symm 0) = ψ 0 := by simpa [hψ0] using hlinv
      exact (ψ.injOn (ψ.map_target hψtarget) hψsource hψeq)
    have hchartInv0 : chart.symm p = e₀ := by
      change (extChartAt I p) p = e₀
      rfl
    have hchartInvmd : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (chart.symm : M → MorseModel n) p := by
      simpa [chart] using (contMDiffAt_extChartAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p))
    have haddInvmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        ((addHomeo n e₀).symm : MorseModel n → MorseModel n) (chart.symm p) := by
      have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => z - e₀) :=
        contDiff_id.sub (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : MorseModel n => e₀))
      simpa [addHomeo, hchartInv0] using hc.contDiffAt.contMDiffAt
    have hLhInvmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Lh.symm : MorseModel n → MorseModel n) 0 := by
      have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => L z) :=
        (L.toContinuousLinearEquiv : MorseModel n →L[ℝ] MorseModel n).contDiff
      simpa [Lh] using hc.contDiffAt.contMDiffAt
    have hTInvmd : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (T.symm : MorseModel n → MorseModel n) 0 := by
      have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T.symm : MorseModel n → MorseModel n) := by
        dsimp [T]
        apply contDiff_pi'
        intro i
        change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => y (σe i))
        rw [show (fun y : MorseModel n => y (σe i)) =
          (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ) by rfl]
        exact (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ).contDiff
      exact hc.contDiffAt.contMDiffAt
    have h1c : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (chart.symm : M → MorseModel n) p :=
      hchartInvmd
    have h1add : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => (addHomeo n e₀).symm (chart.symm x)) p :=
      ContMDiffAt.comp (x := p) (g := ((addHomeo n e₀).symm : MorseModel n → MorseModel n))
        (f := (chart.symm : M → MorseModel n))
        (hg := haddInvmd) (hf := h1c)
    have h1Lh : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => Lh.symm ((addHomeo n e₀).symm (chart.symm x))) p :=
      ContMDiffAt.comp (x := p) (g := (Lh.symm : MorseModel n → MorseModel n))
        (f := fun x : M => (addHomeo n e₀).symm (chart.symm x))
        (hg := by
          have hg0 : (addHomeo n e₀).symm (chart.symm p) = 0 := by
            simp [addHomeo, hchartInv0]
          simpa [hg0] using hLhInvmd)
        (hf := h1add)
    have h1ψ : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => ψ.symm (Lh.symm ((addHomeo n e₀).symm (chart.symm x)))) p :=
      ContMDiffAt.comp (x := p) (g := (ψ.symm : MorseModel n → MorseModel n))
        (f := fun x : M => Lh.symm ((addHomeo n e₀).symm (chart.symm x)))
        (hg := by
          have hg0 : Lh.symm ((addHomeo n e₀).symm (chart.symm p)) = 0 := by
            simp [Lh, addHomeo, hchartInv0]
          have hψInvmd0 : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
              (ψ.symm : MorseModel n → MorseModel n) 0 := hψsymmSmooth.contMDiffAt
          simpa [hg0] using hψInvmd0)
        (hf := h1Lh)
    have hκInv1 : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (κ.symm : M → MorseModel n) p := by
      rw [hκsymmfun]
      exact h1ψ
    have hTInv1 : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => T.symm (κ.symm x)) p :=
      ContMDiffAt.comp (x := p) (g := (T.symm : MorseModel n → MorseModel n))
        (f := (κ.symm : M → MorseModel n))
        (hg := by
          have hg0 : κ.symm p = 0 := by
            rw [hκsymmfun]
            simp [Lh, addHomeo, hchartInv0, hψsymm0]
          simpa [hg0] using hTInvmd)
        (hf := hκInv1)
    rw [hΦsymmfun]
    exact hTInv1
  rcases hψLocal with ⟨vψ, hvψOpen, hvψ0, hψOn, hψsymmOn⟩
  rcases Metric.mem_nhds_iff.mp (hvψOpen.mem_nhds hvψ0) with ⟨rψ, hrψ, hballψ⟩
  have hψmdOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) (Metric.ball (0 : MorseModel n) rψ) :=
    (contMDiffOn_iff_contDiffOn).2 (hψOn.mono hballψ)
  have hψsymmOn' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (ψ.symm : MorseModel n → MorseModel n) (ψ '' Metric.ball (0 : MorseModel n) rψ) :=
    hψsymmOn.mono (by
      intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨y, hballψ hy, ?_⟩
      exact hxy)
  have hψsymmmdOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n)
      (ψ '' Metric.ball (0 : MorseModel n) rψ) :=
    (contMDiffOn_iff_contDiffOn).2 hψsymmOn'
  have hLhOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Lh : MorseModel n → MorseModel n) Set.univ := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => L.symm z) :=
      (L.symm.toContinuousLinearEquiv : MorseModel n →L[ℝ] MorseModel n).contDiff
    exact (contMDiffOn_iff_contDiffOn).2 (by simpa [Lh] using hc.contDiffOn)
  have haddOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (addHomeo n e₀ : MorseModel n → MorseModel n) Set.univ := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => e₀ + z) :=
      (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : MorseModel n => e₀)).add contDiff_id
    exact (contMDiffOn_iff_contDiffOn).2 (by simpa [addHomeo] using hc.contDiffOn)
  have hchartOn : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (chart : MorseModel n → M) chart.source := by
    simpa [chart] using (contMDiffOn_extChartAt_symm p)
  have hκpre : {y : MorseModel n | (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)) ∈ chart.source} ∈
      nhds (0 : MorseModel n) := by
    have hc : ContinuousAt (fun y : MorseModel n =>
        (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))) (0 : MorseModel n) := by
      have hψc : ContinuousAt ψ (0 : MorseModel n) := ψ.continuousAt hψsource
      have hLhc : ContinuousAt Lh (ψ (0 : MorseModel n)) := Lh.continuous.continuousAt
      have haddc : ContinuousAt (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ (0 : MorseModel n))) :=
        (addHomeo n e₀).continuous.continuousAt
      exact (ContinuousAt.comp (g := (addHomeo n e₀ : MorseModel n → MorseModel n))
        (f := fun y : MorseModel n => Lh (ψ y)) (x := (0 : MorseModel n))
        haddc (hLhc.comp hψc))
    have hval : (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ (0 : MorseModel n))) ∈ chart.source := by
      have hψ0' : ψ (0 : MorseModel n) = 0 := hψ0
      have hLh0 : Lh 0 = 0 := by dsimp [Lh]; exact L.symm.map_zero
      change (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ (0 : MorseModel n))) ∈ (extChartAt I p).target
      rw [hψ0', hLh0]
      dsimp [addHomeo]
      rw [add_zero]
      dsimp [e₀]
      simp
    exact hc.preimage_mem_nhds (by
      dsimp [chart]
      exact (isOpen_extChartAt_target p).mem_nhds hval)
  rcases Metric.mem_nhds_iff.mp (Filter.inter_mem (Metric.ball_mem_nhds (0 : MorseModel n) hrψ) hκpre)
    with ⟨rκ, hrκ, hballκ⟩
  have hκmdOn : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (κ : MorseModel n → M) (Metric.ball (0 : MorseModel n) rκ) := by
    have hψOnκ : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n)
        (Metric.ball (0 : MorseModel n) rκ) :=
      hψmdOn.mono (by intro y hy; exact (hballκ hy).1)
    have hψLh : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => Lh (ψ y))
        (Metric.ball (0 : MorseModel n) rκ) := by
      have hLhOnκ : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (Lh : MorseModel n → MorseModel n) Set.univ := hLhOn
      exact hLhOnκ.comp hψOnκ
        (by intro y hy; trivial)
    have hψLhadd : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n =>
          (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)))
        (Metric.ball (0 : MorseModel n) rκ) := by
      have haddOnκ : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (addHomeo n e₀ : MorseModel n → MorseModel n) Set.univ := haddOn
      exact haddOnκ.comp hψLh
        (by intro y hy; trivial)
    have hψLhaddChart : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : MorseModel n => chart ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))))
        (Metric.ball (0 : MorseModel n) rκ) := by
      have hchartOnκ : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (chart : MorseModel n → M) chart.source := hchartOn
      exact hchartOnκ.comp hψLhadd
        (by intro y hy; exact (hballκ hy).2)
    have hfun : (fun y : MorseModel n => κ y) =
        fun y => chart ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))) := by
      rw [hκfun]
    simpa [hfun] using hψLhaddChart
  have hTpre : {y : MorseModel n | T y ∈ Metric.ball (0 : MorseModel n) rκ} ∈ nhds (0 : MorseModel n) := by
    have hc : ContinuousAt (T : MorseModel n → MorseModel n) (0 : MorseModel n) :=
      (T.toOpenPartialHomeomorph).continuousAt (by simp)
    have hval : T (0 : MorseModel n) = 0 := by dsimp [T]; simp [reindexHomeo]
    exact hc.preimage_mem_nhds (by
      rw [hval]
      exact Metric.ball_mem_nhds (0 : MorseModel n) hrκ)
  rcases Metric.mem_nhds_iff.mp hTpre with ⟨rΦ, hrΦ, hballΦ⟩
  have hΦmdOn : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ : MorseModel n → M) (Metric.ball (0 : MorseModel n) rΦ) := by
    have hTOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T : MorseModel n → MorseModel n) Set.univ := by
      have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T : MorseModel n → MorseModel n) := by
        dsimp [T]
        apply contDiff_pi'
        intro i
        change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => y (σe.symm i))
        rw [show (fun y : MorseModel n => y (σe.symm i)) =
          (ContinuousLinearMap.proj (σe.symm i) : MorseModel n →L[ℝ] ℝ) by rfl]
        exact (ContinuousLinearMap.proj (σe.symm i) : MorseModel n →L[ℝ] ℝ).contDiff
      exact (contMDiffOn_iff_contDiffOn).2 hc.contDiffOn
    have hTOnΦ : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T : MorseModel n → MorseModel n)
        (Metric.ball (0 : MorseModel n) rΦ) :=
      hTOn.mono
        (by intro y hy; trivial)
    have hcomp := hκmdOn.comp hTOnΦ (by intro y hy; exact hballΦ hy)
    exact hcomp.congr (by intro y hy; rfl)
  refine ⟨R, hRpos, Φ, hΦsource0, hΦtarget0, hΦ0, hΦsource, hnormal', hΦmd, hΦsymm,
    rΦ, hrΦ, hΦmdOn, ?_⟩
  have hchartInvOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (chart.symm : M → MorseModel n) chart.target := by
    simpa [chart] using (contMDiffOn_extChartAt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p))
  have haddInvOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      ((addHomeo n e₀).symm : MorseModel n → MorseModel n) Set.univ := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => z - e₀) :=
      contDiff_id.sub (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : MorseModel n => e₀))
    exact (contMDiffOn_iff_contDiffOn).2 (by simpa [addHomeo] using hc.contDiffOn)
  have hLhInvOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Lh.symm : MorseModel n → MorseModel n) Set.univ := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun z : MorseModel n => L z) :=
      (L.toContinuousLinearEquiv : MorseModel n →L[ℝ] MorseModel n).contDiff
    exact (contMDiffOn_iff_contDiffOn).2 (by simpa [Lh] using hc.contDiffOn)
  have hTInvOn : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (T.symm : MorseModel n → MorseModel n) Set.univ := by
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T.symm : MorseModel n → MorseModel n) := by
      dsimp [T]
      apply contDiff_pi'
      intro i
      change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => y (σe i))
      rw [show (fun y : MorseModel n => y (σe i)) =
        (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ) by rfl]
      exact (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ).contDiff
    exact (contMDiffOn_iff_contDiffOn).2 hc.contDiffOn
  have hκimage_target : κ '' Metric.ball (0 : MorseModel n) rκ ⊆ chart.target := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (chart.map_source (by exact (hballκ hy).2))
  have hκinvOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (κ.symm : M → MorseModel n) (κ '' Metric.ball (0 : MorseModel n) rκ) := by
    have h1 : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => (addHomeo n e₀).symm (chart.symm x)) (κ '' Metric.ball (0 : MorseModel n) rκ) := by
      have hchartInv : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (chart.symm : M → MorseModel n) chart.target :=
        hchartInvOn
      have h1' := hchartInv.comp
        (contMDiffOn_id : ContMDiffOn I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) (id : M → M)
          (κ '' Metric.ball (0 : MorseModel n) rκ))
        (by intro x hx; exact hκimage_target hx)
      have haddInv : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          ((addHomeo n e₀).symm : MorseModel n → MorseModel n) Set.univ :=
        haddInvOn
      simpa [Function.comp_def] using (haddInv.comp h1' (by intro x hx; trivial))
    have h2 : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => Lh.symm ((addHomeo n e₀).symm (chart.symm x)))
        (κ '' Metric.ball (0 : MorseModel n) rκ) := by
      have hLhInv : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (Lh.symm : MorseModel n → MorseModel n) Set.univ :=
        hLhInvOn
      simpa [Function.comp_def] using (hLhInv.comp h1 (by intro x hx; trivial))
    have h2maps : Set.MapsTo (fun x : M => Lh.symm ((addHomeo n e₀).symm (chart.symm x)))
        (κ '' Metric.ball (0 : MorseModel n) rκ) (ψ '' Metric.ball (0 : MorseModel n) rψ) := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      have hsrc : (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)) ∈ chart.source :=
        (hballκ hy).2
      have hc1 : chart.symm (chart ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)))) =
          (addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y)) := chart.left_inv hsrc
      have hadd1 : (addHomeo n e₀).symm ((addHomeo n e₀ : MorseModel n → MorseModel n) (Lh (ψ y))) =
          Lh (ψ y) := by
        dsimp [addHomeo]
        simp
      have hLh1 : Lh.symm (Lh (ψ y)) = ψ y := by
        dsimp [Lh]
        simp
      refine ⟨y, (hballκ hy).1, ?_⟩
      symm
      rw [hκfun]
      simp [hadd1, hc1, hLh1]
    have h3 : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => ψ.symm (Lh.symm ((addHomeo n e₀).symm (chart.symm x))))
        (κ '' Metric.ball (0 : MorseModel n) rκ) := by
      have hψsymm' : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (ψ.symm : MorseModel n → MorseModel n) (ψ '' Metric.ball (0 : MorseModel n) rψ) := hψsymmmdOn
      simpa [Function.comp_def] using (hψsymm'.comp h2 h2maps)
    have hfun : (fun x : M => κ.symm x) =
        fun x => ψ.symm (Lh.symm ((addHomeo n e₀).symm (chart.symm x))) := by
      dsimp [κ]
      funext x
      rfl
    simpa [hfun] using h3
  have hΦimage_sub : Φ '' Metric.ball (0 : MorseModel n) rΦ ⊆ κ '' Metric.ball (0 : MorseModel n) rκ := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨T y, hballΦ hy, ?_⟩
    rw [hΦfun]
  have hκinvOn' : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (κ.symm : M → MorseModel n) (Φ '' Metric.ball (0 : MorseModel n) rΦ) :=
    hκinvOn.mono hΦimage_sub
  have hTInv : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (T.symm : MorseModel n → MorseModel n) Set.univ :=
    (contMDiffOn_iff_contDiffOn).2 (by
      have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (T.symm : MorseModel n → MorseModel n) := by
        dsimp [T]
        apply contDiff_pi'
        intro i
        change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => y (σe i))
        rw [show (fun y : MorseModel n => y (σe i)) =
          (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ) by rfl]
        exact (ContinuousLinearMap.proj (σe i) : MorseModel n →L[ℝ] ℝ).contDiff
      exact hc.contDiffOn)
  have hΦsymmOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => T.symm (κ.symm x)) (Φ '' Metric.ball (0 : MorseModel n) rΦ) := by
    simpa [Function.comp_def] using (hTInv.comp hκinvOn' (by intro x hx; trivial))
  have hfun : (fun x : M => Φ.symm x) = fun x => T.symm (κ.symm x) := by
    dsimp [Φ]
    funext x
    rfl
  simpa [hfun] using hΦsymmOn

end
end DifferentialGeometry.Topology.Morse
