module

public import DifferentialGeometry.Topology.Morse.NormalForm.Local
public import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Local
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section


namespace DifferentialGeometry.Topology.Morse


noncomputable def bilinPullback {n : ℕ}
    (H : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (L : MorseModel n →L[ℝ] MorseModel (n + 1)) : MorseModel n →L[ℝ] MorseModel n →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun u => ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ (H (L u)) L
        map_add' := by
          intro u v
          ext w
          simp [map_add]
        map_smul' := by
          intro c u
          ext w
          simp [map_smul] }
    cont := by
      fun_prop }

open Filter
open DifferentialGeometry.Analysis
open scoped _root_.Topology

namespace Completion

variable {n : ℕ}


noncomputable def clmBilin {n : ℕ}
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ) :
    MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)) :=
  fun x =>
    { toFun := fun u => { toFun := fun v => a x u v
                          map_add' := by intro v w; simp [map_add]
                          map_smul' := by intro c v; simp [map_smul] }
      map_add' := by intro u₁ u₂; ext v; simp [map_add]
      map_smul' := by intro c u; ext v; simp [map_smul] }



theorem hessian_pullback_at_critical (f : MorseModel (n + 1) → ℝ)
    (σ : MorseModel n → MorseModel (n + 1))
    (hf : ContDiff ℝ 2 f) (hσ : ContDiffAt ℝ 2 σ (0 : MorseModel n))
    (hσ0 : σ (0 : MorseModel n) = 0) (hcrit : fderiv ℝ f 0 = 0)
    (u v : MorseModel n) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (σ x'))) (0 : MorseModel n)) u v =
    (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n) u)
        (fderiv ℝ σ (0 : MorseModel n) v) := by
  have hfd : ∀ᶠ x in nhds (0 : MorseModel n), fderiv ℝ (fun x' : MorseModel n => f (σ x')) x =
      ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
        (fderiv ℝ f (σ x)) (fderiv ℝ σ x) := by
    rcases (hσ.contDiffOn (le_rfl : (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
      (by intro h; norm_num at h)) with ⟨u, hu, hσOn⟩
    rcases mem_nhds_iff.mp hu with ⟨u', hu'u, hu'open, hu'0⟩
    have hσOn' : ContDiffOn ℝ 2 σ u' := hσOn.mono hu'u
    have hσdiffOn : DifferentiableOn ℝ σ u' :=
      hσOn'.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    filter_upwards [hu'open.mem_nhds hu'0] with x hx
    have hdf : DifferentiableAt ℝ f (σ x) :=
      (hf.contDiffAt (x := σ x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    have hdσ : DifferentiableAt ℝ σ x :=
      (hσdiffOn x hx).differentiableAt (hu'open.mem_nhds hx)
    have h := fderiv_comp x (g := f) (f := σ) (hg := hdf) (hf := hdσ)
    calc
      fderiv ℝ (fun x' : MorseModel n => f (σ x')) x = fderiv ℝ (f ∘ σ) x := by
        rfl
      _ = (fderiv ℝ f (σ x)).comp (fderiv ℝ σ x) := h
      _ = ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ x)) (fderiv ℝ σ x) := by
        rw [ContinuousLinearMap.compL_apply]
  have hdf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (σ (0 : MorseModel n)) :=
    by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
        hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ f) (σ (0 : MorseModel n)) :=
        ((h1 (σ (0 : MorseModel n)) (Set.mem_univ _)).differentiableWithinAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
      exact hd.hasFDerivAt
  have hdσ' : HasFDerivAt σ (fderiv ℝ σ (0 : MorseModel n)) (0 : MorseModel n) :=
    (hσ.differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hd2 : HasFDerivAt (fun x : MorseModel n => fderiv ℝ σ x)
      (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) (0 : MorseModel n) :=
    by
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ σ) (0 : MorseModel n) :=
        hσ.fderiv_right (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ σ) (0 : MorseModel n) :=
        h1.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)
      exact hd.hasFDerivAt
  have hcomp' : HasFDerivAt (fun y : MorseModel n =>
        ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
      (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
        ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n)))
            (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
              (fderiv ℝ σ (0 : MorseModel n))))
      (0 : MorseModel n) := by
    have hg : HasFDerivAt (fun x : MorseModel n => fderiv ℝ f (σ x))
        (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
          (fderiv ℝ σ (0 : MorseModel n)))
        (0 : MorseModel n) :=
      HasFDerivAt.comp (0 : MorseModel n) (g := fderiv ℝ f)
        (g' := fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (f := σ)
        (f' := fderiv ℝ σ (0 : MorseModel n)) (hg := hdf') (hf := hdσ')
    have hh : HasFDerivAt (fun y : MorseModel n =>
        ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
        (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
          ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
            (fderiv ℝ σ (0 : MorseModel n)))
              (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
                (fderiv ℝ σ (0 : MorseModel n))))
        (0 : MorseModel n) := by
      have hc : DifferentiableAt ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) :=
        hg.differentiableAt
      have hd : DifferentiableAt ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) :=
        hd2.differentiableAt
      have hmain := fderiv_clm_comp (𝕜 := ℝ) (E := MorseModel n) (F := MorseModel n)
        (G := MorseModel (n + 1)) (H := ℝ) (c := fun x : MorseModel n => fderiv ℝ f (σ x))
        (d := fun x : MorseModel n => fderiv ℝ σ x) (x := (0 : MorseModel n)) hc hd
      have hfderiv : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
          ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n)) := hg.fderiv
      have hdderiv : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
          fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
      rw [hfderiv, hdderiv] at hmain
      have hhmain : HasFDerivAt (fun y : MorseModel n =>
          ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
          (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
              (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
            ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
              (fderiv ℝ σ (0 : MorseModel n)))
                (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
                  (fderiv ℝ σ (0 : MorseModel n))))
          (0 : MorseModel n) :=
        by
          have hfun : (fun y : MorseModel n =>
              ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
                (fderiv ℝ f (σ y)) (fderiv ℝ σ y)) = fun y : MorseModel n =>
                  (fderiv ℝ f (σ y)).comp (fderiv ℝ σ y) := by
            funext y
            simp [ContinuousLinearMap.compL_apply]
          simpa [hfun, hmain] using (hg.clm_comp hd2 : HasFDerivAt
            (fun y : MorseModel n => (fderiv ℝ f (σ y)).comp (fderiv ℝ σ y))
            (((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ)
                (fderiv ℝ f (σ (0 : MorseModel n)))).comp (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
              ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
                (fderiv ℝ σ (0 : MorseModel n))).comp
                  ((fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))).comp (fderiv ℝ σ (0 : MorseModel n))))
            0)
      simpa [ContinuousLinearMap.comp_apply] using hhmain
    simpa [hfd] using hh
  have hg' : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
      ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
        (fderiv ℝ σ (0 : MorseModel n)) := by
    exact (by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
        hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ f) (σ (0 : MorseModel n)) :=
        ((h1 (σ (0 : MorseModel n)) (Set.mem_univ _)).differentiableWithinAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
      have hc : HasFDerivAt (fun x : MorseModel n => fderiv ℝ f (σ x))
          (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n))) (0 : MorseModel n) :=
        HasFDerivAt.comp (0 : MorseModel n) (g := fderiv ℝ f)
          (g' := fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (f := σ)
          (f' := fderiv ℝ σ (0 : MorseModel n)) (hg := hd.hasFDerivAt) (hf := hdσ')
      exact hc.fderiv)
  have hd2' : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
      fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
  have hh0 : ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))).comp
            (fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n)) +
        ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n))).comp
            (fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n))) =
      bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) := by
    rw [hσ0, hcrit, hg', hd2']
    apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro z
    simp [bilinPullback, hσ0, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  have hmain' : HasFDerivAt (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x)
      (bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)))
      (0 : MorseModel n) := by
    have hfun_ev : (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x) =ᶠ[nhds (0 : MorseModel n)]
        fun y : MorseModel n => ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y) := by
      filter_upwards [hfd] with x hx
      exact hx
    have hderiv' : (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
        ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n)))
            (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
              (fderiv ℝ σ (0 : MorseModel n)))) =
        bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) := by
      have hg2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
          ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n)) := hg'
      have hd2_3 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
          fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
      rw [← hd2_3, ← hg2]
      exact hh0
    rw [hderiv'] at hcomp'
    exact (HasFDerivAt.congr_of_eventuallyEq hcomp' hfun_ev)
  have hfinal : fderiv ℝ (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x)
      (0 : MorseModel n) = bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) :=
    hmain'.fderiv
  have := congrArg (fun L : (MorseModel n) →L[ℝ] (MorseModel n →L[ℝ] ℝ) => L u v) hfinal
  simpa [bilinPullback, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply] using this


noncomputable def morseSection
    {n : ℕ} (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel n → MorseModel (n + 1) :=
  fun x' => φ.symm (morseCons (0 : ℝ) x')

theorem morseSection_tail {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hy : morseCons (0 : ℝ) x' ∈ φ.target) :
    morseTail (morseSection φ x') = x' :=
  morseCriticalSection_tail f φ hφ hy

theorem morseSection_zero {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hcrit : fderiv ℝ f 0 = 0) (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source) :
    morseSection φ (0 : MorseModel n) = 0 :=
  morseCriticalSection_zero f φ hφ hcrit hsrc

theorem morseSection_head_critical {n : ℕ}
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    {x' : MorseModel n} :
    morseHead (morseSection φ x') = morseCriticalSection φ x' := by
  rfl


noncomputable def morseSectionHead {n : ℕ}
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel n → ℝ :=
  fun x' => morseHead (morseCompletionMap a (morseSection φ x'))



theorem morseReduction_identity (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hx' : morseCons (0 : ℝ) x' ∈ φ.target)
    (hpiv : morsePivot (clmBilin a) (morseSection φ x') ≠ 0) :
    f (morseSection φ x') - f 0 =
      (1 / 2 : ℝ) * SignType.sign (morsePivot (clmBilin a) (morseSection φ x')) *
          (morseSectionHead (clmBilin a) φ x') ^ 2 +
        (1 / 2 : ℝ) * morseReducedFamily (clmBilin a) (morseSection φ x') x' x' := by
  have hsec := morseCriticalSection_eq f φ hφ hx'
  have htail : morseTail (morseSection φ x') = x' := morseSection_tail f φ hφ hx'
  have hhead : morseHead (morseSection φ x') = morseCriticalSection φ x' :=
    morseSection_head_critical φ
  let b : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)) := clmBilin a
  have htaylor := second_order_taylor_bilin f hg (morseSection φ x')
  have htaylor' : f (morseSection φ x') - f 0 =
      (morseTaylorBilin f (morseSection φ x')) (morseSection φ x') (morseSection φ x') := by
    rw [htaylor, hcrit]
    simp
  have hquad : (morseTaylorBilin f (morseSection φ x')) (morseSection φ x') (morseSection φ x') =
      (1 / 2 : ℝ) * (a (morseSection φ x') (morseSection φ x') (morseSection φ x')) := by
    rw [ha (morseSection φ x')]
    simp
  have hsym' : ∀ x y z : MorseModel (n + 1), b x y z = b x z y := by
    intro x y z
    simpa [b, clmBilin] using hsym x y z
  have hpiv' : morsePivot b (morseSection φ x') ≠ 0 := by
    simpa [b, clmBilin, morsePivot] using hpiv
  have hcs := morse_complete_square_sqrt b hsym' (morseSection φ x') hpiv'
  have htail' : morseTail (morseSection φ x') = x' := htail
  have hab : a (morseSection φ x') (morseSection φ x') (morseSection φ x') =
      b (morseSection φ x') (morseSection φ x') (morseSection φ x') := by
    simp [b, clmBilin]
  rw [htaylor', hquad, hab, hcs, morseSectionHead]
  rw [htail]
  rw [morseReducedFamily_apply]
  simp [b]
  ring_nf



theorem morsePartialDerivCLE_symm_tail {n : ℕ}
    (p' : MorseModel (n + 1) →L[ℝ] ℝ) (h₀ : p' morseE0 ≠ 0) (u : MorseModel n) :
    morseTail ((morsePartialDerivCLE p' h₀).symm (morseCons (0 : ℝ) u)) = u := by
  let v : MorseModel (n + 1) :=
    morseCons ((0 : ℝ) - p' (morseCons (0 : ℝ) u) / p' morseE0) u
  have hpre : morsePartialDeriv p' v = morseCons (0 : ℝ) u := by
    have hlin : p' v = morseHead v * p' morseE0 + p' (morseCons (0 : ℝ) (morseTail v)) := by
      conv_lhs =>
        rw [morse_cons_decompose v, morseCons_eq_smul_add (morseHead v) (morseTail v)]
      simp [map_add, map_smul, smul_eq_mul]
    have hmv : morseHead v = (0 : ℝ) - p' (morseCons (0 : ℝ) u) / p' morseE0 := by
      simp [v, morseHead, morseCons]
    have htv : morseTail v = u := by
      funext j
      simp [v, morseTail, morseCons, Fin.cons_succ]
    funext i
    cases i using Fin.cases with
    | zero =>
        simp [morsePartialDeriv, morseCons, hlin, hmv, htv]
        field_simp [h₀]
        ring_nf
    | succ j =>
        simp [morsePartialDeriv, v, morseTail, morseCons, Fin.cons_succ]
  have hleft : (morsePartialDerivCLE p' h₀).symm (morseCons (0 : ℝ) u) = v := by
    have hcle : morseCons (0 : ℝ) u = (morsePartialDerivCLE p' h₀) v := by
      simpa [morsePartialDerivCLE] using hpre.symm
    exact (morsePartialDerivCLE p' h₀).symm_apply_eq.mpr hcle
  rw [hleft]
  funext j
  simp [v, morseTail, morseCons, Fin.cons_succ]



theorem morseSection_fderiv_tail {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcrit : fderiv ℝ f 0 = 0)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    {u : MorseModel n} :
    morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u := by
  have htail' : (fun x' : MorseModel n => morseTail (morseSection φ x')) =ᶠ[nhds (0 : MorseModel n)]
      (fun x' : MorseModel n => x') := by
    have hc : Continuous (fun x' : MorseModel n => morseCons (0 : ℝ) x') := by
      have hc' : Continuous (fun p : ℝ × MorseModel n => morseConsLinearCLM p) :=
        morseConsLinearCLM.cont
      exact hc'.comp (continuous_const.prodMk continuous_id)
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hmem : ∀ᶠ y : MorseModel n in nhds (0 : MorseModel n), morseCons (0 : ℝ) y ∈ φ.target := by
      have hφ0 : φ 0 = 0 := by
        have hφm : φ 0 = morsePartialMap f 0 := by rw [hφ]
        rw [hφm]
        funext i
        cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, hcrit, morseCons, morseTail]
      have hφt0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
        rw [← hφ0]
        exact φ.map_source hsrc
      have hnhds : φ.target ∈ nhds (0 : MorseModel (n + 1)) := φ.open_target.mem_nhds hφt0
      have hca : ContinuousAt (fun x' : MorseModel n => morseCons (0 : ℝ) x') (0 : MorseModel n) :=
        hc.continuousAt
      have hnhds' : φ.target ∈ nhds (morseCons (0 : ℝ) (0 : MorseModel n)) := by
        rw [hz]
        exact hnhds
      exact hca.preimage_mem_nhds hnhds'
    filter_upwards [hmem] with y hy
    exact morseSection_tail f φ hφ hy
  have hfd : fderiv ℝ (fun x' : MorseModel n => morseTail (morseSection φ x')) (0 : MorseModel n) =
      fderiv ℝ (fun x' : MorseModel n => x') (0 : MorseModel n) :=
    htail'.fderiv_eq
  have hchain : fderiv ℝ (fun x' : MorseModel n => morseTail (morseSection φ x')) (0 : MorseModel n) =
      (fderiv ℝ morseTail (morseSection φ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ) (0 : MorseModel n)) := by
    have hdt : DifferentiableAt ℝ (morseTail : MorseModel (n + 1) → MorseModel n)
        (morseSection φ (0 : MorseModel n)) := by
      have hdiff : DifferentiableAt ℝ (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)
          (morseSection φ (0 : MorseModel n)) :=
        (morseTailProj.contDiff.contDiffAt (x := morseSection φ (0 : MorseModel n))).differentiableAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)
      simpa [morseTailProj] using hdiff
    have hsec' : DifferentiableAt ℝ (morseSection φ : MorseModel n → MorseModel (n + 1))
        (0 : MorseModel n) := hdf
    exact fderiv_comp (𝕜 := ℝ) (x := (0 : MorseModel n))
      (g := (morseTail : MorseModel (n + 1) → MorseModel n))
      (f := (morseSection φ : MorseModel n → MorseModel (n + 1))) (hg := hdt) (hf := hsec')
  have hdtailproj : fderiv ℝ morseTail (morseSection φ (0 : MorseModel n)) = morseTailProj := by
    change fderiv ℝ (fun x : MorseModel (n + 1) => morseTailProj x) (morseSection φ (0 : MorseModel n)) =
      morseTailProj
    exact (morseTailProj.hasFDerivAt).fderiv
  have hid : fderiv ℝ (fun x' : MorseModel n => x') (0 : MorseModel n) = (1 : MorseModel n →L[ℝ] MorseModel n) := by
    exact (hasFDerivAt_id (x := (0 : MorseModel n))).fderiv
  have happ : (morseTailProj.comp (fderiv ℝ (morseSection φ) (0 : MorseModel n))) u = u := by
    rw [← hdtailproj]
    rw [← hchain, hfd, hid]
    simp
  simpa [morseTail, morseTailProj, ContinuousLinearMap.comp_apply] using happ




theorem morseSection_fderiv_complete {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcrit : fderiv ℝ f 0 = 0)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    {u : MorseModel n} :
    (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
      (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = 0 := by
  have hsec : (fun x' : MorseModel n => morsePartial f (morseSection φ x')) =ᶠ[nhds (0 : MorseModel n)]
      (fun _ : MorseModel n => 0) := by
    have hφ0 : φ 0 = 0 := by
      have hφm : φ 0 = morsePartialMap f 0 := by rw [hφ]
      rw [hφm]
      funext i
      cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, hcrit, morseCons, morseTail]
    have hφt0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
      rw [← hφ0]
      exact φ.map_source hsrc
    have hnhds : φ.target ∈ nhds (0 : MorseModel (n + 1)) := φ.open_target.mem_nhds hφt0
    have hc : Continuous (fun x' : MorseModel n => morseCons (0 : ℝ) x') := by
      have hc' : Continuous (fun p : ℝ × MorseModel n => morseConsLinearCLM p) :=
        morseConsLinearCLM.cont
      exact hc'.comp (continuous_const.prodMk continuous_id)
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hca : ContinuousAt (fun x' : MorseModel n => morseCons (0 : ℝ) x') (0 : MorseModel n) :=
      hc.continuousAt
    have hnhds' : φ.target ∈ nhds (morseCons (0 : ℝ) (0 : MorseModel n)) := by
      rw [hz]
      exact hnhds
    have hmem : ∀ᶠ y : MorseModel n in nhds (0 : MorseModel n), morseCons (0 : ℝ) y ∈ φ.target :=
      hca.preimage_mem_nhds hnhds'
    filter_upwards [hmem] with y hy
    have hsec' : morsePartial f (morseSection φ y) = 0 := by
      have htail' : morseTail (morseSection φ y) = y := morseSection_tail f φ hφ hy
      have hhead' : morseHead (morseSection φ y) = morseCriticalSection φ y :=
        morseSection_head_critical φ
      have hdec : morseSection φ y = morseCons (morseCriticalSection φ y) y := by
        rw [morse_cons_decompose (morseSection φ y)]
        rw [hhead']
        exact congrArg (morseCons (morseCriticalSection φ y)) htail'
      rw [hdec]
      exact morseCriticalSection_eq f φ hφ hy
    exact hsec'
  have hfd : fderiv ℝ (fun x' : MorseModel n => morsePartial f (morseSection φ x')) (0 : MorseModel n) =
      fderiv ℝ (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) :=
    hsec.fderiv_eq
  have hchain' : fderiv ℝ (fun x' : MorseModel n => morsePartial f (morseSection φ x')) (0 : MorseModel n) =
      (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ) (0 : MorseModel n)) := by
    exact fderiv_comp (𝕜 := ℝ) (x := (0 : MorseModel n))
      (g := (morsePartial f : MorseModel (n + 1) → ℝ))
      (f := (morseSection φ : MorseModel n → MorseModel (n + 1)))
      (hg := hdfp) (hf := hdf)
  have hzero : fderiv ℝ (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) = 0 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) (x := (0 : MorseModel n)) (c := (0 : ℝ))).fderiv
  have happ' : ((fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))).comp
      (fderiv ℝ (morseSection φ) (0 : MorseModel n))) u = 0 := by
    rw [← hchain', hfd, hzero]
    simp
  simpa [ContinuousLinearMap.comp_apply] using happ'



theorem fderiv_morsePartial_e0 {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f) :
    ⇑(fderiv ℝ (morsePartial f) 0) =
      (fun w : MorseModel (n + 1) => (fderiv ℝ (fderiv ℝ f) 0) w morseE0) := by
  rw [show (⇑(fderiv ℝ (morsePartial f) 0)) =
      ⇑(fderiv ℝ (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0) 0) by rfl]
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ := by
    exact hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hc : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) 0) 0 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
      ((h1 0 (Set.mem_univ _)).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
    exact hd.hasFDerivAt
  have hcst : HasFDerivAt (fun _ : MorseModel (n + 1) => morseE0) 0 0 :=
    hasFDerivAt_const (𝕜 := ℝ) (x := (0 : MorseModel (n + 1))) (c := (morseE0 : MorseModel (n + 1)))
  have hca' : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0)
      ((fderiv ℝ f 0).comp (0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) +
        (fderiv ℝ (fderiv ℝ f) 0).flip morseE0) 0 :=
    hc.clm_apply hcst
  have hkill : (fderiv ℝ f 0).comp (0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) = 0 := by
    ext w
    simp
  have hca : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0)
      ((fderiv ℝ (fderiv ℝ f) 0).flip morseE0) 0 := by
    simpa [hkill] using hca'
  have hd : fderiv ℝ (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0) 0 =
      (fderiv ℝ (fderiv ℝ f) 0).flip morseE0 := hca.fderiv
  rw [hd]
  funext w
  exact (ContinuousLinearMap.flip_apply (fderiv ℝ (fderiv ℝ f) 0) w morseE0).symm



theorem bilin_completed_head_zero {n : ℕ}
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    {x y : MorseModel (n + 1)}
    (hx : morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
        (clmBilin a 0 morseE0 morseE0) = 0)
    (hy : morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
        (clmBilin a 0 morseE0 morseE0) = 0) :
    a 0 x y = morseReducedFamily (clmBilin a) 0 (morseTail x) (morseTail y) := by
  have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
    dsimp [morsePivot, clmBilin]
    exact hpiv
  have hcrossx : (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) =
      -(morseHead x) * (clmBilin a 0 morseE0 morseE0) := by
    have hmul : (morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
        (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) = 0 := by
      rw [hx, zero_mul]
    have hrel : morseHead x * (clmBilin a 0 morseE0 morseE0) +
        (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) = 0 := by
      have hmm : (morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
          (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) =
          morseHead x * (clmBilin a 0 morseE0 morseE0) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) hpiv']
      rwa [hmm] at hmul
    linarith
  have hcrossy : (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) =
      -(morseHead y) * (clmBilin a 0 morseE0 morseE0) := by
    have hmul : (morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
        (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) = 0 := by
      rw [hy, zero_mul]
    have hrel : morseHead y * (clmBilin a 0 morseE0 morseE0) +
        (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) = 0 := by
      have hmm : (morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
          (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) =
          morseHead y * (clmBilin a 0 morseE0 morseE0) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) hpiv']
      rwa [hmm] at hmul
    linarith
  have hxdec : x = morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x) := by
    conv_lhs =>
      rw [morse_cons_decompose x]
    rw [morseCons_eq_smul_add (morseHead x) (morseTail x)]
  have hydec : y = morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y) := by
    conv_lhs =>
      rw [morse_cons_decompose y]
    rw [morseCons_eq_smul_add (morseHead y) (morseTail y)]
  rw [hxdec, hydec]
  let F : MorseModel (n + 1) →L[ℝ] ℝ :=
    morseHead x • (a 0) morseE0 + (a 0) (morseCons (0 : ℝ) (morseTail x))
  have hF : (a 0) (morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x)) = F := by
    rw [map_add (a 0), map_smul (a 0)]
  rw [hF]
  have hadd : F (morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y)) =
      F (morseHead y • morseE0) + F (morseCons (0 : ℝ) (morseTail y)) :=
    map_add F (morseHead y • morseE0) (morseCons (0 : ℝ) (morseTail y))
  have hsmul : F (morseHead y • morseE0) = morseHead y • F morseE0 :=
    map_smul F (morseHead y) morseE0
  rw [hadd, hsmul]
  have hFe0 : F morseE0 = morseHead x • (a 0 morseE0 morseE0) + (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 := by
    simp [F]
  have hFtail : F (morseCons (0 : ℝ) (morseTail y)) =
      morseHead x • (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) +
        (a 0) (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail y)) := by
    simp [F]
  rw [hFe0, hFtail]
  have hsymCLM0 : ∀ z w, (a 0) z w = (a 0) w z := by
    intro z w
    exact hsym 0 z w
  rw [← hsymCLM0 morseE0 (morseCons (0 : ℝ) (morseTail x))]
  rw [hsymCLM0 morseE0 (morseCons (0 : ℝ) (morseTail y))]
  have htailx' : morseTail (morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x)) = morseTail x := by
    rw [← morseCons_eq_smul_add (morseHead x) (morseTail x)]
    exact morseCons_tail (morseHead x) (morseTail x)
  have htainly' : morseTail (morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y)) = morseTail y := by
    rw [← morseCons_eq_smul_add (morseHead y) (morseTail y)]
    exact morseCons_tail (morseHead y) (morseTail y)
  rw [htailx', htainly']
  have hcrossxCLM : (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 =
      -(morseHead x) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 = (a 0) morseE0 (morseCons (0 : ℝ) (morseTail x)) :=
      hsym 0 (morseCons (0 : ℝ) (morseTail x)) morseE0
    rw [hswap]
    simpa [clmBilin] using hcrossx
  have hcrossyCLM : (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 =
      -(morseHead y) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 = (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) :=
      hsym 0 (morseCons (0 : ℝ) (morseTail y)) morseE0
    rw [hswap]
    simpa [clmBilin] using hcrossy
  have hcrossx0 : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail x)) = -(morseHead x) * (a 0 morseE0 morseE0) := by
    simpa [clmBilin] using hcrossx
  rw [hcrossx0]
  rw [hcrossyCLM]
  rw [morseReducedFamily_apply]
  have hcrossy0 : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) = -(morseHead y) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) = (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 :=
      hsym 0 morseE0 (morseCons (0 : ℝ) (morseTail y))
    simpa [hswap] using hcrossyCLM
  simp [clmBilin, hcrossxCLM]
  simp [hcrossy0]
  have hpiv2 : morsePivot (clmBilin a) 0 = (a 0 morseE0 morseE0) := rfl
  simp [hpiv2]
  field_simp [hpiv']
  ring_nf


theorem hessian_morseReducedFn (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcont : ContDiffAt ℝ 2 (morseSection φ) (0 : MorseModel n))
    (u v : MorseModel n) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (morseSection φ x'))) (0 : MorseModel n)) u v =
      morseReducedFamily (clmBilin a) 0 u v := by
  have hpull := hessian_pullback_at_critical f (morseSection φ) hg hcont
    (morseSection_zero f φ hφ hcrit hsrc) hcrit u v
  have hcs := morse_complete_square_sqrt (clmBilin a) (by
    intro x y z
    simpa [clmBilin] using hsym x y z) (0 : MorseModel (n + 1)) (by
      simpa [morsePivot, clmBilin] using hpiv)
  have hmain : (fun w : MorseModel (n + 1) =>
      (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))) w) =
      fun w : MorseModel (n + 1) => (clmBilin a 0) morseE0 w := by
    have hσ0 : morseSection φ (0 : MorseModel n) = 0 :=
      morseSection_zero f φ hφ hcrit hsrc
    rw [hσ0]
    have hfd0 := fderiv_morsePartial_e0 (n := n) f hg
    funext w
    have hw : (fderiv ℝ (fderiv ℝ f) 0) w morseE0 = clmBilin a 0 morseE0 w := by
      have ha0 : a 0 = 2 • morseTaylorBilin f 0 := ha 0
      have htb : morseTaylorBilin f 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
        morseTaylorBilin_zero f
      have h2 : (fderiv ℝ (fderiv ℝ f) 0) w morseE0 = a 0 morseE0 w := by
        have hsymw : a 0 morseE0 w = a 0 w morseE0 := (hsym 0 w morseE0).symm
        rw [hsymw, ha0, htb]
        simp [smul_eq_mul]
      simpa [clmBilin] using h2
    exact (congrFun hfd0 w).trans hw
  have hhead : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
      (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))) /
        morsePivot (clmBilin a) 0) = 0 := by
    have hp0 : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
        (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = 0 :=
      morseSection_fderiv_complete f φ hφ hsrc hcrit hdf hdfp
    have happ0 : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) = 0 := by
      have hpt : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
          (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) =
          (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) := by
        exact congrFun hmain (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
      exact hpt.symm.trans hp0
    have ht : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u :=
      morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
    have hdec : fderiv ℝ (morseSection φ) (0 : MorseModel n) u =
        morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u := by
      rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)]
      exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))) ht
    have hh0' : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) = 0 := happ0
    have hcross : clmBilin a 0 morseE0
        (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) • morseE0 + morseCons (0 : ℝ) u) =
        morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) * (clmBilin a 0 morseE0 morseE0) +
          clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) := by
      rw [map_add, map_smul]
      simp [smul_eq_mul]
    have hmain0 : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) *
          (clmBilin a 0 morseE0 morseE0) +
        clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) = 0 := by
      rw [hdec, morseCons_eq_smul_add (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u] at hh0'
      rw [hcross] at hh0'
      exact hh0'
    have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
      simpa [clmBilin, morsePivot] using hpiv
    have hdiv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
        clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) / (clmBilin a 0 morseE0 morseE0) = 0 := by
      have hmul : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
          clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) / (clmBilin a 0 morseE0 morseE0)) *
          (clmBilin a 0 morseE0 morseE0) = 0 := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) u)) hpiv']
        exact hmain0
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right hpiv'
    simpa [ht, morsePivot, clmBilin] using hdiv
  rw [hpull]
  have ht' : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u :=
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
  have ht'' : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) = v :=
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
  have hsq : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
      (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
      morseReducedFamily (clmBilin a) 0 u v := by
    have hdecomp : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
          (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
        (morseReducedFamily (clmBilin a) 0 (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))
          (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v))) := by
      have hxy : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
          (morseReducedFamily (clmBilin a) 0 u v) := by
        have ha0 : ∀ x y, (fderiv ℝ (fderiv ℝ f) 0) x y = (clmBilin a 0) x y := by
          intro x y
          have hx : (fderiv ℝ (fderiv ℝ f) 0) x y = a 0 x y := by
            rw [ha 0, morseTaylorBilin_zero f]
            simp [smul_eq_mul]
          rw [hx]
          rfl
        have hhu : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))) /
              morsePivot (clmBilin a) 0 = 0 := by
          simpa [ht'] using hhead
        have hhv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))) /
              morsePivot (clmBilin a) 0 = 0 := by
          have hp0v := morseSection_fderiv_complete (u := v) f φ hφ hsrc hcrit hdf hdfp
          have hptv : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
              (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
              (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) :=
            congrFun hmain (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)
          have hhapp0v : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) = 0 :=
            hptv.symm.trans hp0v
          have hdv : fderiv ℝ (morseSection φ) (0 : MorseModel n) v =
              morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v := by
            rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
            exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))
              (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
          have hh0v : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) = 0 := hhapp0v
          rw [hdv, morseCons_eq_smul_add (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v] at hh0v
          rw [map_add, map_smul] at hh0v
          have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
            simpa [clmBilin, morsePivot] using hpiv
          have hmain0v : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) *
                (clmBilin a 0 morseE0 morseE0) +
              clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) = 0 := by
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hh0v
          have hdivv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
              clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) / (clmBilin a 0 morseE0 morseE0) = 0 := by
            have hmulv : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
                clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) / (clmBilin a 0 morseE0 morseE0)) *
                (clmBilin a 0 morseE0 morseE0) = 0 := by
              rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) v)) hpiv']
              exact hmain0v
            exact (eq_zero_or_eq_zero_of_mul_eq_zero hmulv).resolve_right hpiv'
          simpa [ht'', morsePivot, clmBilin] using hdivv
        have hdu : fderiv ℝ (morseSection φ) (0 : MorseModel n) u =
            morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u := by
          rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)]
          exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
        have hdv : fderiv ℝ (morseSection φ) (0 : MorseModel n) v =
            morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v := by
          rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
          exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
        have hbhz := bilin_completed_head_zero a hsym hpiv hhu hhv
        rw [ha0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
        change ((clmBilin a 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
          morseReducedFamily (clmBilin a) 0 u v
        simpa [clmBilin, ht', ht''] using hbhz
      simpa [ht', ht''] using hxy
    rw [hdecomp, ht', ht'']
  exact hsq


theorem morseReducedFamily_separating (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (hsep : (QuadraticMap.associated (R := ℝ) (clmBilin a 0).toQuadraticMap).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (morseReducedFamily (clmBilin a) 0).toQuadraticMap).SeparatingLeft := by
  unfold LinearMap.SeparatingLeft
  intro u hu
  have hu' : ∀ v : MorseModel n, morseReducedFamily (clmBilin a) 0 u v = 0 := by
    intro v
    have hmain : (QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)) u v =
        morseReducedFamily (clmBilin a) 0 u v := by
      rw [QuadraticMap.associated_apply]
      have hq : (morseReducedFamily (clmBilin a) 0) (u + v) (u + v) -
          (morseReducedFamily (clmBilin a) 0) u u -
          (morseReducedFamily (clmBilin a) 0) v v =
          2 * (morseReducedFamily (clmBilin a) 0) u v := by
        have hsym' : ∀ x y, (morseReducedFamily (clmBilin a) 0) x y =
            (morseReducedFamily (clmBilin a) 0) y x :=
          morseReducedFamily_sym (clmBilin a) (by
            intro x y z
            simpa [clmBilin] using hsym x y z) 0
        simp [map_add, hsym']
        ring_nf
      have hinv : (⅟(2 : ℝ) : ℝ) * (2 * (morseReducedFamily (clmBilin a) 0) u v) =
          morseReducedFamily (clmBilin a) 0 u v := by
        norm_num
        ring
      simpa [hq, hinv, smul_eq_mul] using (show (⅟(2 : ℝ) : ℝ) *
        ((morseReducedFamily (clmBilin a) 0) (u + v) (u + v) -
          (morseReducedFamily (clmBilin a) 0) u u -
          (morseReducedFamily (clmBilin a) 0) v v) =
        morseReducedFamily (clmBilin a) 0 u v by
          rw [hq]
          exact hinv)
    have hu'' : (QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)) u v = 0 :=
      hu v
    rwa [hmain] at hu''
  let cross_u : ℝ := (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u)
  let w : MorseModel (n + 1) := morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0
  have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
    simpa [morsePivot] using hpiv
  have hfull : ∀ z : MorseModel (n + 1), (clmBilin a 0) w z = 0 := by
    intro z
    have hz : z = morseHead z • morseE0 + morseCons (0 : ℝ) (morseTail z) := by
      calc
        z = morseCons (morseHead z) (morseTail z) := morse_cons_decompose z
        _ = morseHead z • morseE0 + morseCons (0 : ℝ) (morseTail z) :=
          morseCons_eq_smul_add (morseHead z) (morseTail z)
    have hwe0 : (clmBilin a 0) w morseE0 = 0 := by
      dsimp [w, cross_u]
      have h1 : (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
          (clmBilin a 0) (morseCons (0 : ℝ) u) -
            (cross_u / (clmBilin a 0 morseE0 morseE0)) • (clmBilin a 0) morseE0 := by
        rw [map_sub, map_smul]
      rw [h1]
      change (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 -
        (cross_u / (clmBilin a 0 morseE0 morseE0)) •
          (clmBilin a 0) morseE0 morseE0 = 0
      have hcu' : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = cross_u := by
        dsimp [cross_u]
        exact hsym 0 (morseCons (0 : ℝ) u) morseE0
      rw [hcu']
      simp [smul_eq_mul]
      field_simp [hpiv']
      ring
    have hwt : ∀ v : MorseModel n, (clmBilin a 0) w (morseCons (0 : ℝ) v) = 0 := by
      intro v
      dsimp [w, cross_u]
      have h1 : (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
          (clmBilin a 0) (morseCons (0 : ℝ) u) -
            (cross_u / (clmBilin a 0 morseE0 morseE0)) • (clmBilin a 0) morseE0 := by
        rw [map_sub, map_smul]
      change (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0)
          (morseCons (0 : ℝ) v) = 0
      rw [h1]
      change (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) -
        (cross_u / (clmBilin a 0 morseE0 morseE0)) •
          (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) = 0
      have hru := hu' v
      have hfam : (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) =
          (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) *
            (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) /
              (clmBilin a 0 morseE0 morseE0) := by
        have hru' : morseReducedFamily (clmBilin a) 0 u v = 0 := hru
        rw [morseReducedFamily_apply] at hru'
        have hsym0 : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 =
            (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) :=
          hsym 0 (morseCons (0 : ℝ) u) morseE0
        rw [hsym0] at hru'
        have hpiv2 : morsePivot (clmBilin a) 0 = (clmBilin a 0 morseE0 morseE0) := rfl
        rw [hpiv2] at hru'
        linear_combination hru'
      rw [hfam]
      have hcu' : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) :=
        hsym 0 (morseCons (0 : ℝ) u) morseE0
      simp [smul_eq_mul]
      field_simp [hpiv']
      ring
    rw [hz]
    rw [map_add, map_smul]
    rw [hwe0, hwt]
    simp
  have hzero : w = 0 := by
    apply hsep
    intro z
    have hz : (QuadraticMap.associated (R := ℝ) ((clmBilin a 0).toQuadraticMap)) w z =
        (clmBilin a 0) w z := by
      rw [QuadraticMap.associated_apply]
      have hsym0 : ∀ x y, (clmBilin a 0) x y = (clmBilin a 0) y x := by
        intro x y
        simpa [clmBilin] using hsym 0 x y
      simp [map_add, hsym0]
      ring_nf
    rw [hz]
    exact hfull z
  have htailw : morseTail w = morseTail (morseCons (0 : ℝ) u) := by
    change morseTail (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
      morseTail (morseCons (0 : ℝ) u)
    have hlin : ∀ x y : MorseModel (n + 1), morseTail (x - y) = morseTail x - morseTail y := by
      intro x y
      calc
        morseTail (x - y) = morseTail (x + (-1 : ℝ) • y) := by
          rw [sub_eq_add_neg]
          rw [← neg_one_smul ℝ y]
        _ = morseTail x + morseTail ((-1 : ℝ) • y) := morseTail_add x ((-1 : ℝ) • y)
        _ = morseTail x + (-1 : ℝ) • morseTail y := by
          rw [morseTail_smul (-1 : ℝ) y]
        _ = morseTail x - morseTail y := by
          simp [sub_eq_add_neg]
    rw [hlin]
    rw [morseTail_smul]
    have htailE0 : morseTail morseE0 = (0 : MorseModel n) := by
      funext i
      simp [morseTail, morseE0]
    rw [htailE0]
    simp [morseCons_tail]
  have htail0 : morseTail w = u := by
    rw [htailw]
    exact morseCons_tail (0 : ℝ) u
  have hu0 : u = 0 := by
    rw [← htail0]
    exact congrArg morseTail hzero
  exact hu0

theorem morseReducedFn_nondegenerate (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcont : ContDiffAt ℝ 2 (morseSection φ) (0 : MorseModel n))
    (hsep : (QuadraticMap.associated (R := ℝ) (chartHessianAt f 0)).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (fun x' : MorseModel n => f (morseSection φ x')) 0)).SeparatingLeft := by
  have hbilin0 : chartHessianBilinAt f 0 = (clmBilin a 0) := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have hA : a 0 = fderiv ℝ (fderiv ℝ f) 0 := by
      rw [ha 0, morseTaylorBilin_zero f]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      simp [smul_eq_mul]
    simp [chartHessianBilinAt, clmBilin, hA]
  have hchart : chartHessianAt f 0 = (clmBilin a 0).toQuadraticMap := by
    change (chartHessianBilinAt f 0).toQuadraticMap = (clmBilin a 0).toQuadraticMap
    rw [hbilin0]
  have hsepFull : (QuadraticMap.associated (R := ℝ) ((clmBilin a 0).toQuadraticMap)).SeparatingLeft := by
    rw [← hchart]
    exact hsep
  have hsepRed := morseReducedFamily_separating a hsym hpiv hsepFull
  have hbilin : chartHessianBilinAt (fun x' : MorseModel n => f (morseSection φ x')) 0 =
      morseReducedFamily (clmBilin a) 0 := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simpa [chartHessianBilinAt] using
      (hessian_morseReducedFn f hg hcrit a ha hsym hpiv φ hφ hsrc hdf hdfp hcont u v)
  have hQ : QuadraticMap.associated (R := ℝ)
        (chartHessianAt (fun x' : MorseModel n => f (morseSection φ x')) 0) =
      QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap) := by
    change QuadraticMap.associated (R := ℝ)
        ((chartHessianBilinAt (fun x' : MorseModel n => f (morseSection φ x')) 0).toQuadraticMap) =
      QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)
    rw [hbilin]
  rwa [hQ]

theorem section_second_order (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x : MorseModel (n + 1)} (hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ.target) :
    f x - f (morseSection φ (morseTail x)) =
      (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 *
        (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0 morseE0 := by
  let σ : MorseModel (n + 1) := morseSection φ (morseTail x)
  let d : ℝ := morseHead x - morseCriticalSection φ (morseTail x)
  have hlin := second_order_taylor_bilin_at f hg σ x
  have hx : x = morseCons (morseHead x) (morseTail x) := morse_cons_decompose x
  have hσ : σ = morseCons (morseCriticalSection φ (morseTail x)) (morseTail x) := by
    dsimp [σ]
    rw [morse_cons_decompose (morseSection φ (morseTail x))]
    rw [morseSection_head_critical φ (x' := morseTail x)]
    rw [morseSection_tail f φ hφ hx']
  have hsub : ∀ (a b : ℝ) (t : MorseModel n),
      morseCons a t - morseCons b t = morseCons (a - b) (0 : MorseModel n) := by
    intro a b t
    calc
      morseCons a t - morseCons b t = morseCons a t + (-1 : ℝ) • morseCons b t := by
        simp [sub_eq_add_neg]
      _ = morseCons a t + morseCons (-b) ((-1 : ℝ) • t) := by
        rw [← morseCons_smul (-1 : ℝ) b t]
        simp
      _ = morseCons (a - b) (0 : MorseModel n) := by
        rw [← morseCons_add a (-b) t ((-1 : ℝ) • t)]
        simp [sub_eq_add_neg]
  have hvec : x - σ = d • morseE0 := by
    rw [hx, hσ]
    rw [hsub (morseHead x) (morseCriticalSection φ (morseTail x)) (morseTail x)]
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hsmul : morseCons d (0 : MorseModel n) = d • morseE0 := by
      rw [morseCons_eq_smul_add d (0 : MorseModel n)]
      simp [hz]
    simpa [d] using hsmul
  have hfd : (fderiv ℝ f σ) (x - σ) = 0 := by
    rw [hvec]
    have hp : (fderiv ℝ f σ) morseE0 = 0 := by
      have hσ' : σ = morseCons (morseCriticalSection φ (morseTail x)) (morseTail x) := hσ
      rw [hσ']
      have hp' := morseCriticalSection_eq f φ hφ hx'
      simpa [morsePartial] using hp'
    rw [map_smul]
    simp [hp, smul_eq_mul]
  have hquad : (morseTaylorBilinAt f σ x) (x - σ) (x - σ) =
      d ^ 2 * (morseTaylorBilinAt f σ x) morseE0 morseE0 := by
    rw [hvec]
    simp [map_smul, smul_eq_mul]
    ring
  rw [hfd, hquad] at hlin
  simpa [σ, d] using hlin

theorem hessian_diagonal_pivot {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    (fderiv ℝ (fderiv ℝ f) 0) morseE0 morseE0 = w 0 := by
  have h := hdiag morseE0 morseE0
  have hsum : (∑ i : Fin (n + 1), w i * morseE0 i * morseE0 i) = w 0 := by
    rw [Fin.sum_univ_succ]
    simp [morseE0]
  simpa [hsum] using h

theorem hessian_diagonal_reduced {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcont : ContDiffAt ℝ 2 (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (u v : MorseModel n) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (morseSection φ x'))) (0 : MorseModel n)) u v =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
  rw [hessian_morseReducedFn f hg hcrit a ha hsym hpiv φ hφ hsrc hdf hdfp hcont u v]
  have hclm : ∀ u v : MorseModel (n + 1), (clmBilin a 0) u v = (a 0 u) v := by
    intro u v
    rfl
  have hA : a 0 = fderiv ℝ (fderiv ℝ f) 0 := by
    rw [ha 0, morseTaylorBilin_zero f]
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp [smul_eq_mul]
  have hcross1 : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = 0 := by
    rw [hclm]
    have hd := hdiag (morseCons (0 : ℝ) u) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (morseCons (0 : ℝ) u) i * morseE0 i) = 0 := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseCons]
    rw [hA]
    rw [hd, hsum]
  have hcross2 : (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) = 0 := by
    rw [hclm]
    have hswap : (a 0) morseE0 (morseCons (0 : ℝ) v) = (a 0) (morseCons (0 : ℝ) v) morseE0 :=
      hsym 0 morseE0 (morseCons (0 : ℝ) v)
    rw [hswap]
    have hd := hdiag (morseCons (0 : ℝ) v) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (morseCons (0 : ℝ) v) i * morseE0 i) = 0 := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseCons]
    rw [hA]
    rw [hd, hsum]
  have hmain : (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    rw [hclm]
    rw [hA]
    rw [hdiag (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v)]
    rw [Fin.sum_univ_succ]
    simp [morseCons]
  rw [morseReducedFamily_apply]
  rw [hcross1, hcross2]
  simp [hmain]

noncomputable def morseSectionB (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : ℝ :=
  (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0 morseE0

noncomputable def morseSectionCompletion (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : MorseModel (n + 1) :=
  morseCons (Real.sqrt (2 * |morseSectionB f φ x|) *
      (morseHead x - morseCriticalSection φ (morseTail x))) (morseTail x)

theorem contDiffAt_morseSectionB {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n)) :
    ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
  have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hσtail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    exact (ContDiffAt.comp 0 hcontσ htail).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hg : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail (contDiffAt_id : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    rw [show morseTail (0 : MorseModel (n + 1)) = 0 by
      funext i
      rfl]
    exact morseSection_zero f φ hφ hcrit hsrc
  have hfam : ContDiffAt ℝ 1 (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
      morseTaylorBilinAt f p.1 p.2) (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt f hf 0 0
  have hfam' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    exact (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have happly : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0) 0 :=
    hfam'.clm_apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0)
  simpa [morseSectionB] using
    (happly.clm_apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0))

theorem contDiffAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ContDiffAt ℝ 1 (morseSectionCompletion f φ) 0 := by
  have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hσtail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    exact (ContDiffAt.comp 0 hcontσ htail).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hg : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail (contDiffAt_id : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    rw [show morseTail (0 : MorseModel (n + 1)) = 0 by
      funext i
      rfl]
    exact morseSection_zero f φ hφ hcrit hsrc
  have hfam : ContDiffAt ℝ 1 (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
      morseTaylorBilinAt f p.1 p.2) (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt f hf 0 0
  have hfam' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    exact (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hB : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
    exact contDiffAt_morseSectionB f hf hcrit φ hφ hsrc hcontσ
  have hsqrt : ContDiffAt ℝ 1 (fun x => Real.sqrt (2 * |morseSectionB f φ x|)) 0 := by
    have habs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) 0 :=
      ContDiffAt.comp 0 (contDiffAt_abs hB0) hB
    have hBcont : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) 0 :=
      ContDiffAt.mul (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => (2 : ℝ)) 0) habs
    have hne : (2 * |morseSectionB f φ 0|) ≠ 0 := by
      have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
      positivity
    exact (Real.contDiffAt_sqrt hne).comp 0 hBcont
  have hhead : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseHead x) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseHeadProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x)) 0 := by
    have hhead0 : ContDiffAt ℝ 1 (fun y : MorseModel (n + 1) => morseHead y)
        (morseSection φ (morseTail (0 : MorseModel (n + 1)))) := by
      simpa [hσ0] using hhead
    have h' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x))) 0 := by
      exact (ContDiffAt.comp (x := 0)
        (g := fun y : MorseModel (n + 1) => morseHead y)
        (f := fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        (hg := hhead0) (hf := hσtail))
    simpa [morseCriticalSection, morseSection] using h'
  have hheadsub : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseHead x - morseCriticalSection φ (morseTail x)) 0 :=
    hhead.sub hs
  have hprod : ContDiffAt ℝ 1 (fun x =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x))) 0 :=
    ContDiffAt.mul hsqrt hheadsub
  have hpair : ContDiffAt ℝ 1 (fun x =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0 :=
    ContDiffAt.prodMk hprod htail
  have hcons : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (Real.sqrt (2 * |morseSectionB f φ (0 : MorseModel (n + 1))|) *
          (morseHead (0 : MorseModel (n + 1)) - morseCriticalSection φ (morseTail (0 : MorseModel (n + 1)))),
        morseTail (0 : MorseModel (n + 1))) := by
    exact ((morseConsLinearCLM.contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun p => morseConsLinearCLM p) _).of_le
      (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ 1 (fun x =>
      morseConsLinearCLM (Real.sqrt (2 * |morseSectionB f φ x|) *
        (morseHead x - morseCriticalSection φ (morseTail x)), morseTail x)) 0 :=
    ContDiffAt.comp 0 hcons hpair
  change ContDiffAt ℝ 1
    (fun x : MorseModel (n + 1) => morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0
  simpa [morseSectionB] using hcomp

theorem contDiffAt_morseSectionB_smooth {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (0 : MorseModel n)) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
  have htail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
  have hσtail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    exact (ContDiffAt.comp 0 hcontσ htail).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hg : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail
      (contDiffAt_id : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    rw [show morseTail (0 : MorseModel (n + 1)) = 0 by
      funext i
      rfl]
    exact morseSection_zero f φ hφ hcrit hsrc
  have hfam : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
        morseTaylorBilinAt f p.1 p.2)
      (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt_smooth f hf 0 0
  have hfam' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    exact (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have happly : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0) 0 :=
    hfam'.clm_apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : MorseModel (n + 1) => morseE0) 0)
  simpa [morseSectionB] using
    (happly.clm_apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : MorseModel (n + 1) => morseE0) 0))

theorem contDiffAt_morseSectionCompletion_smooth {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (0 : MorseModel n))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSectionCompletion f φ) 0 := by
  have htail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
  have hσtail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    exact (ContDiffAt.comp 0 hcontσ htail).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hg : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail
      (contDiffAt_id : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    rw [show morseTail (0 : MorseModel (n + 1)) = 0 by
      funext i
      rfl]
    exact morseSection_zero f φ hφ hcrit hsrc
  have hfam : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
        morseTaylorBilinAt f p.1 p.2)
      (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt_smooth f hf 0 0
  have hfam' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    exact (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hB : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
    exact contDiffAt_morseSectionB_smooth f hf hcrit φ hφ hsrc hcontσ
  have hsqrt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Real.sqrt (2 * |morseSectionB f φ x|)) 0 := by
    have habs : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) 0 :=
      ContDiffAt.comp 0 (contDiffAt_abs hB0) hB
    have hBcont : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) 0 :=
      ContDiffAt.mul (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : MorseModel (n + 1) => (2 : ℝ)) 0) habs
    have hne : (2 * |morseSectionB f φ 0|) ≠ 0 := by
      have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
      positivity
    exact (Real.contDiffAt_sqrt (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) hne).comp 0 hBcont
  have hhead : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseHead x) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseHeadProj x) 0).of_le
        (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
  have hs : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x)) 0 := by
    have hhead0 : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel (n + 1) => morseHead y)
        (morseSection φ (morseTail (0 : MorseModel (n + 1)))) := by
      simpa [hσ0] using hhead
    have h' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x))) 0 := by
      exact (ContDiffAt.comp (x := 0)
        (g := fun y : MorseModel (n + 1) => morseHead y)
        (f := fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        (hg := hhead0) (hf := hσtail))
    simpa [morseCriticalSection, morseSection] using h'
  have hheadsub : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      morseHead x - morseCriticalSection φ (morseTail x)) 0 :=
    hhead.sub hs
  have hprod : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x))) 0 :=
    ContDiffAt.mul hsqrt hheadsub
  have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0 :=
    ContDiffAt.prodMk hprod htail
  have hcons : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (Real.sqrt (2 * |morseSectionB f φ (0 : MorseModel (n + 1))|) *
          (morseHead (0 : MorseModel (n + 1)) - morseCriticalSection φ (morseTail (0 : MorseModel (n + 1)))),
        morseTail (0 : MorseModel (n + 1))) := by
    exact ((morseConsLinearCLM.contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun p => morseConsLinearCLM p) _).of_le
      (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
  have hcomp : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x =>
      morseConsLinearCLM (Real.sqrt (2 * |morseSectionB f φ x|) *
        (morseHead x - morseCriticalSection φ (morseTail x)), morseTail x)) 0 :=
    ContDiffAt.comp 0 hcons hpair
  change ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : MorseModel (n + 1) => morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0
  simpa [morseSectionB] using hcomp

theorem morseSection_fderiv_head_zero {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    (morseHeadProj.comp (fderiv ℝ (morseSection φ) (0 : MorseModel n))) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hcomplete := morseSection_fderiv_complete f φ hφ hsrc hcrit hdf hdfp (u := v)
  have hσ0 : morseSection φ (0 : MorseModel n) = 0 := morseSection_zero f φ hφ hcrit hsrc
  rw [hσ0] at hcomplete
  have hfd0 := fderiv_morsePartial_e0 (n := n) f hg
  have hh : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) 0 v) morseE0 =
      w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) := by
    have hd := hdiag (fderiv ℝ (morseSection φ) 0 v) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (fderiv ℝ (morseSection φ) 0 v) i * morseE0 i) =
        w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseHead]
    rw [hd, hsum]
  have happ : (fderiv ℝ (morsePartial f) 0) (fderiv ℝ (morseSection φ) 0 v) = 0 := hcomplete
  have hmul : w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) = 0 := by
    rw [← hh]
    exact (congrFun hfd0 (fderiv ℝ (morseSection φ) 0 v)).symm.trans hcomplete
  have hw0 : w 0 ≠ 0 := by
    rcases hw 0 with h | h <;> simp [h]
  have hhead0 : morseHead (fderiv ℝ (morseSection φ) 0 v) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hw0
  simpa [ContinuousLinearMap.comp_apply, morseHeadProj, morseHead] using hhead0

noncomputable def morseSectionCompletionDeriv {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) :=
  (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).comp
    ((Real.sqrt (2 * |morseSectionB f φ 0|) •
        (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
      (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))

theorem morseSectionCompletionDeriv_apply {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) (v : MorseModel (n + 1)) :
    morseSectionCompletionDeriv f φ v =
      morseCons (Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead v) (morseTail v) := by
  simp [morseSectionCompletionDeriv, morseConsLinearCLM, morseConsLinear, morseHeadProj,
    morseTailProj, morseHead, morseCons, ContinuousLinearMap.comp_apply]

theorem morseSectionCompletionDeriv_injective {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    Function.Injective (morseSectionCompletionDeriv f φ) := by
  intro u v h
  have hu := congrArg morseHead h
  have hv := congrArg morseTail h
  have hq : Real.sqrt (2 * |morseSectionB f φ 0|) ≠ 0 := by
    have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
    positivity
  have hu' : morseHead u = morseHead v := by
    rw [morseSectionCompletionDeriv_apply f φ u, morseSectionCompletionDeriv_apply f φ v] at hu
    have hmul : Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead u =
        Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead v := by
      simpa [morseCons, morseHead] using hu
    exact mul_left_cancel₀ hq hmul
  have hv' : morseTail u = morseTail v := by
    rw [morseSectionCompletionDeriv_apply f φ u, morseSectionCompletionDeriv_apply f φ v] at hv
    funext i
    exact congrFun hv i
  rw [morse_cons_decompose u, morse_cons_decompose v]
  rw [hu', hv']

theorem morseSectionCompletionDeriv_surjective {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    Function.Surjective (morseSectionCompletionDeriv f φ) := by
  intro y
  let s : ℝ := Real.sqrt (2 * |morseSectionB f φ 0|)
  have hs : s ≠ 0 := by
    have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
    positivity
  let v : MorseModel (n + 1) := morseCons (morseHead y / s) (morseTail y)
  refine ⟨v, ?_⟩
  rw [morseSectionCompletionDeriv_apply f φ v]
  have hmv : morseHead v = morseHead y / s := by simp [v, morseHead, morseCons]
  have htv : morseTail v = morseTail y := by
    simp [v, morseCons_tail]
  rw [hmv, htv]
  dsimp [s]
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [morseCons, morseHead]
      field_simp [hs]
  | succ j =>
      simp [morseCons, morseTail, Fin.cons_succ]

noncomputable def morseSectionCompletionDerivCLE {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) : MorseModel (n + 1) ≃L[ℝ] MorseModel (n + 1) :=
  (LinearEquiv.ofBijective (morseSectionCompletionDeriv f φ)
    (show Function.Bijective (morseSectionCompletionDeriv f φ) from
      ⟨morseSectionCompletionDeriv_injective f φ hB0,
        morseSectionCompletionDeriv_surjective f φ hB0⟩)).toContinuousLinearEquiv

theorem hasFDerivAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    HasFDerivAt (morseSectionCompletion f φ)
      (morseSectionCompletionDerivCLE f φ hB0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 := by
  have hBcont : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 :=
    contDiffAt_morseSectionB f hf hcrit φ hφ hsrc hcontσ
  have hB' : HasFDerivAt (fun x : MorseModel (n + 1) => morseSectionB f φ x)
      (fderiv ℝ (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0) 0 :=
    (hBcont.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hsd : HasFDerivAt (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x))
      (0 : MorseModel (n + 1) →L[ℝ] ℝ) 0 := by
    have hσd : HasFDerivAt (fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)) 0 :=
      HasFDerivAt.comp (x := 0) (g := morseSection φ)
        (g' := fderiv ℝ (morseSection φ) (0 : MorseModel n))
        (f := fun x : MorseModel (n + 1) => morseTail x) (f' := morseTailProj)
        (hg := hdf.hasFDerivAt) (hf := hasFDerivAt_morseTailProj)
    have hheadc : HasFDerivAt (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x)))
        (morseHeadProj.comp ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))) 0 :=
      HasFDerivAt.comp (x := 0) (g := fun y : MorseModel (n + 1) => morseHead y) (g' := morseHeadProj)
        (f := fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        (f' := (fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))
        (hg := by simpa [morseHead, morseHeadProj] using
          (morseHeadProj.hasFDerivAt : HasFDerivAt (fun y : MorseModel (n + 1) => morseHeadProj y)
            morseHeadProj (morseSection φ (morseTail (0 : MorseModel (n + 1))))))
        (hf := hσd)
    have hh := morseSection_fderiv_head_zero f
      (hf.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))) hcrit φ hφ hsrc hdf hdfp w hw hdiag
    have hzero : morseHeadProj.comp ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp morseTailProj) = 0 := by
      rw [← ContinuousLinearMap.comp_assoc, hh]
      simp
    have hsc : HasFDerivAt (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x)))
        (0 : MorseModel (n + 1) →L[ℝ] ℝ) 0 := by
      simpa [hzero] using hheadc
    exact hsc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hgsub : HasFDerivAt (fun x : MorseModel (n + 1) =>
      morseHead x - morseCriticalSection φ (morseTail x)) morseHeadProj 0 := by
    have hsub := HasFDerivAt.sub hasFDerivAt_morseHead hsd
    exact (hsub.congr_fderiv (by simp)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hsqrt' : HasFDerivAt (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|))
      (fderiv ℝ (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|)) 0) 0 := by
    have habs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) 0 :=
      ContDiffAt.comp 0 (contDiffAt_abs hB0) hBcont
    have hBcont' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) 0 :=
      ContDiffAt.mul (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => (2 : ℝ)) 0) habs
    have hne : (2 * |morseSectionB f φ 0|) ≠ 0 := by
      have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
      positivity
    have hsqrtc : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|)) 0 :=
      (Real.contDiffAt_sqrt hne).comp 0 hBcont'
    exact (hsqrtc.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hg0 : morseHead (0 : MorseModel (n + 1)) - morseCriticalSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    have htail0 : morseTail (0 : MorseModel (n + 1)) = 0 := by
      funext i
      simp [morseTail]
    have hsec : φ.symm (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1)))) = 0 := by
      rw [htail0]
      simpa [morseSection] using (morseSection_zero f φ hφ hcrit hsrc : morseSection φ (0 : MorseModel n) = 0)
    simp [morseCriticalSection, hsec]
  have hmul' : HasFDerivAt (fun x : MorseModel (n + 1) =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)))
      (Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)) 0 := by
    have hmul0 := HasFDerivAt.mul hsqrt' hgsub
    exact (hmul0.congr_fderiv (by simp [hg0])).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hpair : HasFDerivAt (fun x : MorseModel (n + 1) =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x))
      ((Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)) 0 :=
    hmul'.prodMk hasFDerivAt_morseTailProj
  have hcons' : HasFDerivAt (fun p : ℝ × MorseModel n => morseConsLinearCLM p) morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ 0|) * (morseHead (0 : MorseModel (n + 1)) -
        morseCriticalSection φ (morseTail (0 : MorseModel (n + 1)))), morseTail (0 : MorseModel (n + 1))) := by
    exact morseConsLinearCLM.hasFDerivAt
  have hcomp' : HasFDerivAt (morseSectionCompletion f φ)
      (morseConsLinearCLM.comp ((Real.sqrt (2 * |morseSectionB f φ 0|) •
        (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))) 0 := by
    have hc := HasFDerivAt.comp 0 (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (g' := morseConsLinearCLM)
      (f := fun x : MorseModel (n + 1) =>
        (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
          morseTail x))
      (f' := (Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))
      (hg := hcons') (hf := hpair)
    exact hc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  exact hcomp'.congr_fderiv <| by
    ext x i
    simp [morseSectionCompletionDerivCLE, morseSectionCompletionDeriv,
      ContinuousLinearMap.comp_apply]

theorem morseSectionCompletion_value {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x : MorseModel (n + 1)} (hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ.target)
    (hBx : morseSectionB f φ x ≠ 0) :
    f x - f (morseSection φ (morseTail x)) =
      (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
        (morseHead (morseSectionCompletion f φ x)) ^ 2 := by
  have hso := section_second_order f hg φ hφ (x := x) hx'
  have hhead : morseHead (morseSectionCompletion f φ x) =
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)) := by
    simp [morseSectionCompletion, morseHead, morseCons]
  have hBabs : |morseSectionB f φ x| ≠ 0 := abs_ne_zero.mpr hBx
  have hmul : (morseHead (morseSectionCompletion f φ x)) ^ 2 =
      2 * |morseSectionB f φ x| * (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 := by
    rw [hhead]
    rw [mul_pow]
    have hsq : (Real.sqrt (2 * |morseSectionB f φ x|)) ^ 2 = 2 * |morseSectionB f φ x| := by
      rw [Real.sq_sqrt]
      positivity
    rw [hsq]
  have hsign : morseSectionB f φ x = SignType.sign (morseSectionB f φ x) * |morseSectionB f φ x| := by
    rw [sign_mul_abs]
  calc
    f x - f (morseSection φ (morseTail x)) =
        (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 * morseSectionB f φ x := hso
    _ = (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 *
          (SignType.sign (morseSectionB f φ x) * |morseSectionB f φ x|) := by
      conv_lhs =>
        rw [hsign]
    _ = (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
          (2 * |morseSectionB f φ x| * (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2) := by ring
    _ = (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
          (morseHead (morseSectionCompletion f φ x)) ^ 2 := by
      rw [← hmul]

theorem isLocalHomeomorphAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseSectionCompletion f φ ∧ 0 ∈ Φ.source ∧
      ContDiffAt ℝ 1 (Φ : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      ContDiffAt ℝ 1 (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
  let hC : ContDiffAt ℝ 1 (morseSectionCompletion f φ) 0 :=
    contDiffAt_morseSectionCompletion f hf hcrit φ hφ hsrc hcontσ hB0
  let hD : HasFDerivAt (morseSectionCompletion f φ)
      (morseSectionCompletionDerivCLE f φ hB0 :
        MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 :=
    hasFDerivAt_morseSectionCompletion f hf hcrit φ hφ hsrc hdf hdfp hcontσ w hw hdiag hB0
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morseSectionCompletion f φ)
      (f' := morseSectionCompletionDerivCLE f φ hB0) hC hD hn
  have hφm0 : morsePartialMap f 0 = 0 := by
    funext i
    cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, morseCons, morseTail, hcrit]
  have hφ00 : φ 0 = 0 := by
    rw [hφ]
    exact hφm0
  have hφsymm0 : φ.symm 0 = 0 := by
    have hlinv : φ.symm (φ 0) = 0 := φ.left_inv hsrc
    rwa [hφ00] at hlinv
  have hc0 : morseCriticalSection φ (0 : MorseModel n) = 0 := by
    dsimp [morseCriticalSection]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    rw [hz0]
    simp [hφsymm0, morseHead]
  have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
    funext i
    simp [morseTail]
  have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
    funext i
    cases i using Fin.cases <;> simp [morseCons]
  have hΦ0 : morseSectionCompletion f φ 0 = 0 := by
    dsimp [morseSectionCompletion]
    simp [morseHead, htail0, hc0, hz0]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source hC hD hn
  · dsimp [Φ]
    exact hC
  · have hloc := ContDiffAt.to_localInverse hC hD hn
    rw [hΦ0] at hloc
    simpa [Φ, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse,
      ContDiffAt.toOpenPartialHomeomorph] using hloc

theorem isLocalHomeomorphAt_morseSectionCompletion_smooth {n : ℕ}
    (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseSectionCompletion f φ ∧ 0 ∈ Φ.source ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Φ : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
  let hC : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSectionCompletion f φ) 0 :=
    contDiffAt_morseSectionCompletion_smooth f hf hcrit φ hφ hsrc hcontσ hB0
  let hD : HasFDerivAt (morseSectionCompletion f φ)
      (morseSectionCompletionDerivCLE f φ hB0 :
        MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 :=
    hasFDerivAt_morseSectionCompletion f (hf.of_le (by decide : (3 : WithTop ℕ∞) ≤
      (↑(⊤ : ℕ∞) : WithTop ℕ∞))) hcrit φ hφ hsrc hdf hdfp
      (hcontσ.of_le (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
      w hw hdiag hB0
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by norm_num
  let Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morseSectionCompletion f φ)
      (f' := morseSectionCompletionDerivCLE f φ hB0) hC hD hn
  have hφm0 : morsePartialMap f 0 = 0 := by
    funext i
    cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, morseCons, morseTail, hcrit]
  have hφ00 : φ 0 = 0 := by
    rw [hφ]
    exact hφm0
  have hφsymm0 : φ.symm 0 = 0 := by
    have hlinv : φ.symm (φ 0) = 0 := φ.left_inv hsrc
    rwa [hφ00] at hlinv
  have hc0 : morseCriticalSection φ (0 : MorseModel n) = 0 := by
    dsimp [morseCriticalSection]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    rw [hz0]
    simp [hφsymm0, morseHead]
  have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
    funext i
    simp [morseTail]
  have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
    funext i
    cases i using Fin.cases <;> simp [morseCons]
  have hΦ0 : morseSectionCompletion f φ 0 = 0 := by
    dsimp [morseSectionCompletion]
    simp [morseHead, htail0, hc0, hz0]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source hC hD hn
  · dsimp [Φ]
    exact hC
  · have hloc := ContDiffAt.to_localInverse hC hD hn
    rw [hΦ0] at hloc
    simpa [Φ, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse,
      ContDiffAt.toOpenPartialHomeomorph] using hloc

theorem morseSection_smooth {n : ℕ} {k : WithTop ℕ∞} (hk : 2 ≤ k)
    (f : MorseModel (n + 1) → ℝ)
    (hcrit : fderiv ℝ f 0 = 0)
    (hcont : ContDiffAt ℝ k (morsePartialMap f) 0)
    (hdf : DifferentiableAt ℝ (morsePartial f) 0)
    (h₀ : fderiv ℝ (morsePartial f) 0 morseE0 ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f ∧ 0 ∈ φ.source ∧
      ContDiffAt ℝ k (morseSection φ) (0 : MorseModel n) ∧
      ContDiffAt ℝ 2 (morseSection φ) (0 : MorseModel n) ∧
      DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n) := by
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morsePartialMap f)
      (f' := morsePartialDerivCLE (fderiv ℝ (morsePartial f) 0) h₀)
      hcont (hasFDerivAt_morsePartialMap f hdf h₀)
      (by exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : WithTop ℕ∞) < (2 : WithTop ℕ∞)) hk))
  have hφ0 : morsePartialMap f 0 = 0 := by
    funext i
    cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, morseCons, morseTail, hcrit]
  have hφsymm : ContDiffAt ℝ k (φ.symm) (morsePartialMap f 0) := by
    have hloc := hcont.to_localInverse (hasFDerivAt_morsePartialMap f hdf h₀)
      (by exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : WithTop ℕ∞) < (2 : WithTop ℕ∞)) hk))
    exact hloc.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  have hφsymm0 : ContDiffAt ℝ k (φ.symm) 0 := by
    simpa [hφ0] using hφsymm
  have hφsymm2 : ContDiffAt ℝ 2 (φ.symm) 0 :=
    hφsymm0.of_le hk
  have hcons0 : ContDiffAt ℝ k (fun x' : MorseModel n => morseCons (0 : ℝ) x') 0 := by
    have hL : (fun x' : MorseModel n => morseConsLinearCLM (0, x')) =
        fun x' : MorseModel n => morseCons (0 : ℝ) x' := by
      funext x'
      rfl
    have hc : ContDiffAt ℝ k (fun x' : MorseModel n => morseConsLinearCLM (0, x')) 0 := by
      have hlin : (fun x' : MorseModel n => morseConsLinearCLM (0, x')) =
          (morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))) := by
        funext x'
        rfl
      rw [hlin]
      exact ((morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))).contDiff.contDiffAt)
    simpa [hL] using hc
  have hcons2 : ContDiffAt ℝ 2 (fun x' : MorseModel n => morseCons (0 : ℝ) x') 0 :=
    hcons0.of_le hk
  have hsec0 : φ.symm (morseCons (0 : ℝ) (0 : MorseModel n)) = 0 := by
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    rw [hz]
    have hφ0' : φ 0 = 0 := by
      have hφm : φ 0 = morsePartialMap f 0 := by rw [ContDiffAt.toOpenPartialHomeomorph_coe]
      rw [hφm, hφ0]
    have hsrc : (0 : MorseModel (n + 1)) ∈ φ.source :=
      ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
    have htarget : (0 : MorseModel (n + 1)) ∈ φ.target := by
      have ht : morsePartialMap f 0 ∈ φ.target := by
        simpa [φ] using (ContDiffAt.image_mem_toOpenPartialHomeomorph_target hcont
          (hasFDerivAt_morsePartialMap f hdf h₀)
          (by exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : WithTop ℕ∞) < (2 : WithTop ℕ∞)) hk)))
      simpa [hφ0] using ht
    have hφinv : φ (φ.symm 0) = 0 := by
      simpa [hφ0'] using (φ.right_inv htarget)
    have hφeq : φ (φ.symm 0) = φ 0 := by
      simpa [hφ0'] using hφinv
    exact (φ.injOn (φ.map_target htarget) hsrc hφeq)
  have hσk : ContDiffAt ℝ k (morseSection φ) (0 : MorseModel n) := by
    change ContDiffAt ℝ k (fun x' : MorseModel n => φ.symm (morseCons (0 : ℝ) x')) (0 : MorseModel n)
    have hg' : ContDiffAt ℝ k (φ.symm) (morseCons (0 : ℝ) (0 : MorseModel n)) := by
      have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      simpa [hz] using hφsymm0
    exact ContDiffAt.comp (x := 0) (g := φ.symm)
      (f := fun x' : MorseModel n => morseCons (0 : ℝ) x') (hg := hg') (hf := hcons0)
  have hσ2 : ContDiffAt ℝ 2 (morseSection φ) (0 : MorseModel n) := by
    change ContDiffAt ℝ 2 (fun x' : MorseModel n => φ.symm (morseCons (0 : ℝ) x')) (0 : MorseModel n)
    have hg' : ContDiffAt ℝ 2 (φ.symm) (morseCons (0 : ℝ) (0 : MorseModel n)) := by
      have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      simpa [hz] using hφsymm2
    exact ContDiffAt.comp (x := 0) (g := φ.symm)
      (f := fun x' : MorseModel n => morseCons (0 : ℝ) x') (hg := hg') (hf := hcons2)
  have hσdiff : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n) :=
    (hσ2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  refine ⟨φ, ?_, ?_, hσk, hσ2, hσdiff⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

theorem portPrivate_e0822189_contDiffOn_symm_of_contDiffOn
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : OpenPartialHomeomorph E F)
    (hφ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : E → F) φ.source)
    (hInv : ∀ x ∈ φ.source, ∃ e : E ≃L[ℝ] F, (e : E →L[ℝ] F) = fderiv ℝ (φ : E → F) x) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : F → E) φ.target := by
  intro a ha
  have hx : φ.symm a ∈ φ.source := φ.map_target ha
  rcases hInv (φ.symm a) hx with ⟨e, he⟩
  have hφAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : E → F) (φ.symm a) :=
    (IsOpen.contDiffOn_iff φ.open_source).1 hφ hx
  have hfd : HasFDerivAt (φ : E → F) (fderiv ℝ (φ : E → F) (φ.symm a)) (φ.symm a) :=
    (hφAt.differentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  exact (φ.contDiffAt_symm (a := a) (f₀' := e) ha (by simpa [he] using hfd) hφAt).contDiffWithinAt

theorem morseSection_contDiffOn_smooth {n : ℕ} (g : MorseModel (n + 1) → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hcrit : fderiv ℝ g 0 = 0)
    (h₀ : fderiv ℝ (morsePartial g) 0 morseE0 ≠ 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap g)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (Metric.ball (0 : MorseModel n) r) := by
  have hmpG : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartial g) := by
    have hfdk : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
      hg.fderiv_right (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have happ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) :=
      hfdk.clm_apply (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : MorseModel (n + 1) => morseE0))
    change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0)
    exact happ
  have hgPartial : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartialMap g) Set.univ := by
    have hmp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartial g) Set.univ := hmpG.contDiffOn
    have htailS : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTail x) Set.univ := by
      simpa [morseTail, morseTailProj] using
        (morseTailProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => morseTailProj x) Set.univ)
    have hpair : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => (morsePartial g x, morseTail x)) Set.univ :=
      ContDiffOn.prodMk hmp htailS
    have hconsFun : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × MorseModel n => morseCons p.1 p.2) Set.univ := by
      have hlin : (fun p : ℝ × MorseModel n => morseCons p.1 p.2) =
          (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)) := by
        funext p
        rfl
      rw [hlin]
      exact (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).contDiff.contDiffOn
    have hcomp' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseCons (morsePartial g x) (morseTail x)) Set.univ := by
      change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun p : ℝ × MorseModel n => morseCons p.1 p.2) ∘
          (fun x : MorseModel (n + 1) => (morsePartial g x, morseTail x))) Set.univ
      exact hconsFun.comp hpair (by intro x hx; trivial)
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseCons (morsePartial g x) (morseTail x)) Set.univ
    exact hcomp'
  have hdfp : DifferentiableAt ℝ (morsePartial g) 0 :=
    (hmpG.contDiffAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartial g) 0).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hfd0eq : fderiv ℝ (morsePartialMap g) 0 =
      (morsePartialDerivCLE (fderiv ℝ (morsePartial g) 0) h₀ :
        MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) :=
    (hasFDerivAt_morsePartialMap g hdfp h₀).fderiv
  have hfd0inv : ∃ e : (MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1)),
      (e : (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1))) = fderiv ℝ (morsePartialMap g) 0 := by
    refine ⟨morsePartialDerivCLE (fderiv ℝ (morsePartial g) 0) h₀, ?_⟩
    exact hfd0eq.symm
  have hInvOpen : IsOpen ((fun x : MorseModel (n + 1) => fderiv ℝ (morsePartialMap g) x) ⁻¹'
      (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
        (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1))))) := by
    have hc : Continuous (fun x : MorseModel (n + 1) => fderiv ℝ (morsePartialMap g) x) :=
      continuousOn_univ.mp (hgPartial.fderiv_of_isOpen isOpen_univ
        (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).continuousOn
    exact hc.isOpen_preimage (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
      (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1)))) ContinuousLinearEquiv.isOpen
  have h0inv : (0 : MorseModel (n + 1)) ∈
      (fun x : MorseModel (n + 1) => fderiv ℝ (morsePartialMap g) x) ⁻¹'
        (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
          (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1)))) := by
    exact Set.mem_preimage.mpr hfd0inv
  let u : Set (MorseModel (n + 1)) := φ.source ∩
    (fun x : MorseModel (n + 1) => fderiv ℝ (morsePartialMap g) x) ⁻¹'
      (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
        (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1))))
  have huOpen : IsOpen u := IsOpen.inter φ.open_source hInvOpen
  have hu0 : (0 : MorseModel (n + 1)) ∈ u := ⟨hsrc, h0inv⟩
  let φ₁ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    φ.restrOpen u huOpen
  have hφ₁source0 : (0 : MorseModel (n + 1)) ∈ φ₁.source := by
    simpa [φ₁, u] using hu0
  have hφ₁0 : φ₁ (0 : MorseModel (n + 1)) = 0 := by
    have hpm0 : morsePartialMap g (0 : MorseModel (n + 1)) = 0 := by
      ext i
      cases i using Fin.cases with
      | zero =>
        change (fderiv ℝ g (0 : MorseModel (n + 1))) morseE0 = 0
        simpa using
          (congrArg (fun L : (MorseModel (n + 1)) →L[ℝ] ℝ => L morseE0) hcrit)
      | succ j =>
        simp [morsePartialMap, morsePartial, morseCons, morseTail, hcrit]
    simpa [φ₁, hφ] using hpm0
  have hφ₁target0 : (0 : MorseModel (n + 1)) ∈ φ₁.target := by
    simpa [hφ₁0] using (φ₁.map_source hφ₁source0)
  have hφ₁symm : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (φ₁.symm : MorseModel (n + 1) → MorseModel (n + 1)) φ₁.target := by
    refine portPrivate_e0822189_contDiffOn_symm_of_contDiffOn φ₁ ?_ ?_
    · simpa [φ₁, hφ] using (hgPartial.mono (by intro x hx; trivial))
    · intro x hx
      simpa [φ₁, hφ] using hx.2.2
  have hcons : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x' : MorseModel n => morseCons (0 : ℝ) x') Set.univ := by
    have hlin : (fun x' : MorseModel n => morseConsLinearCLM (0, x')) =
        (morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))) := by
      funext x'
      rfl
    have hmain : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x' : MorseModel n => morseConsLinearCLM (0, x')) Set.univ := by
      rw [hlin]
      exact (morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))).contDiff.contDiffOn
    exact hmain.congr fun x _ => by rfl
  have hpreOpen : IsOpen ((fun x' : MorseModel n => morseCons (0 : ℝ) x') ⁻¹' φ₁.target) := by
    exact (continuousOn_univ.mp hcons.continuousOn).isOpen_preimage φ₁.target φ₁.open_target
  have hpre0 : (0 : MorseModel n) ∈
      (fun x' : MorseModel n => morseCons (0 : ℝ) x') ⁻¹' φ₁.target := by
    change morseCons (0 : ℝ) (0 : MorseModel n) ∈ φ₁.target
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    simpa [hz0] using hφ₁target0
  rcases (Metric.isOpen_iff.mp hpreOpen) (0 : MorseModel n) hpre0 with ⟨r, hr, hball⟩
  have hσOn' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ)
      ((fun x' : MorseModel n => morseCons (0 : ℝ) x') ⁻¹' φ₁.target) := by
    have hcons' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x' : MorseModel n => morseCons (0 : ℝ) x')
        ((fun x' : MorseModel n => morseCons (0 : ℝ) x') ⁻¹' φ₁.target) :=
      hcons.mono (by intro x hx; trivial)
    have hmorse : (fun x' : MorseModel n => morseSection φ x') =
        (fun y : MorseModel (n + 1) => φ₁.symm y) ∘ (fun x' : MorseModel n => morseCons (0 : ℝ) x') := by
      funext x'
      rfl
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x' : MorseModel n => morseSection φ x')
      ((fun x' : MorseModel n => morseCons (0 : ℝ) x') ⁻¹' φ₁.target)
    rw [hmorse]
    exact hφ₁symm.comp hcons' (by intro x hx; exact hx)
  refine ⟨r, hr, hσOn'.mono (by intro x hx; exact hball (Metric.mem_ball.mp hx))⟩

theorem morseSectionCompletion_contDiffOn_smooth {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hcontσ : ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (Metric.ball (0 : MorseModel n) r))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ∃ u : Set (MorseModel (n + 1)), IsOpen u ∧ (0 : MorseModel (n + 1)) ∈ u ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSectionCompletion f φ) u := by
  rcases hcontσ with ⟨rσ, hrσ, hσOn⟩
  let s : Set (MorseModel (n + 1)) :=
    (fun x : MorseModel (n + 1) => morseTail x) ⁻¹' Metric.ball (0 : MorseModel n) rσ
  have hσtail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) s := by
    have htail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTail x) s := by
      change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTailProj x) s
      exact ((morseTailProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTailProj x) Set.univ).mono (by intro x hx; trivial))
    exact hσOn.comp htail (by intro x hx; exact hx)
  have hB : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSectionB f φ x) s := by
    have hsOpen : IsOpen s := by
      have htail : Continuous (fun x : MorseModel (n + 1) => morseTail x) := by
        change Continuous (fun x : MorseModel (n + 1) => morseTailProj x)
        exact (morseTailProj : (MorseModel (n + 1)) →L[ℝ] MorseModel n).cont
      dsimp [s]
      exact htail.isOpen_preimage (Metric.ball (0 : MorseModel n) rσ) Metric.isOpen_ball
    exact (IsOpen.contDiffOn_iff hsOpen).mpr (by
      intro x hx
      have hσtailAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) x :=
        (IsOpen.contDiffOn_iff hsOpen).1 hσtail hx
      have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) x :=
        ContDiffAt.prodMk hσtailAt (contDiffAt_id : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => x) x)
      have hfam : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
          (morseSection φ (morseTail x), x) :=
        (contDiffOn_morseTaylorBilinAt_smooth f hf).contDiffAt Filter.univ_mem
      have hfam' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => morseTaylorBilinAt f (morseSection φ (morseTail x)) x) x :=
        ContDiffAt.comp (x := x) (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
          morseTaylorBilinAt f p.1 p.2)
          (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
          (hg := hfam) (hf := hpair)
      have happly : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) =>
            (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0) x :=
        hfam'.clm_apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : MorseModel (n + 1) => morseE0) x)
      change ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseSectionB f φ x) x
      simpa only [morseSectionB] using
        (happly.clm_apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : MorseModel (n + 1) => morseE0) x)))
  let u : Set (MorseModel (n + 1)) := s ∩ {x : MorseModel (n + 1) | morseSectionB f φ x ≠ 0}
  have huOpen : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hBcontAt : ContinuousAt (fun x : MorseModel (n + 1) => morseSectionB f φ x) x :=
      (hB.continuousOn x hx.1).continuousAt (by
        have htail : Continuous (fun x : MorseModel (n + 1) => morseTail x) := by
          change Continuous (fun x : MorseModel (n + 1) => morseTailProj x)
          exact (morseTailProj : (MorseModel (n + 1)) →L[ℝ] MorseModel n).cont
        dsimp [s]
        exact (htail.isOpen_preimage (Metric.ball (0 : MorseModel n) rσ) Metric.isOpen_ball).mem_nhds hx.1)
    have hpre : {x : MorseModel (n + 1) | morseSectionB f φ x ≠ 0} ∈ nhds x :=
      hBcontAt.preimage_mem_nhds (isOpen_ne.mem_nhds hx.2)
    have htail : Continuous (fun x : MorseModel (n + 1) => morseTail x) := by
      change Continuous (fun x : MorseModel (n + 1) => morseTailProj x)
      exact (morseTailProj : (MorseModel (n + 1)) →L[ℝ] MorseModel n).cont
    have htailpre : s ∈ nhds x := by
      dsimp [s]
      exact htail.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.1)
    exact Filter.inter_mem htailpre hpre
  have hu0 : (0 : MorseModel (n + 1)) ∈ u := by
    dsimp [u, s]
    constructor
    · change morseTail (0 : MorseModel (n + 1)) ∈ Metric.ball (0 : MorseModel n) rσ
      rw [Metric.mem_ball, dist_zero_right]
      have hz : morseTail (0 : MorseModel (n + 1)) = 0 := by
        funext i
        simp [morseTail]
      rw [hz, norm_zero]
      exact hrσ
    · exact hB0
  have hσtailu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) u :=
    hσtail.mono (by intro x hx; exact hx.1)
  have hBu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseSectionB f φ x) u :=
    hB.mono (by intro x hx; exact hx.1)
  have hBne : ∀ x ∈ u, morseSectionB f φ x ≠ 0 := by
    intro x hx
    exact hx.2
  have habs : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) u :=
    hBu.abs hBne
  have hsqrt : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|)) u := by
    have htwo : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) u :=
      (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : MorseModel (n + 1) => (2 : ℝ)) u).mul habs
    exact htwo.sqrt (by
      intro x hx
      have hBx : morseSectionB f φ x ≠ 0 := hBne x hx
      exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr hBx))
  have hcritSection : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x)) u := by
    have hhead0 : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : MorseModel (n + 1) => morseHead y) Set.univ := by
      simpa [morseHead, morseHeadProj] using
        (morseHeadProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseHeadProj y) Set.univ)
    have h' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x))) u :=
      hhead0.comp hσtailu (by intro x hx; trivial)
    simpa [morseCriticalSection, morseSection] using h'
  have hhead : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseHead x) u := by
    simpa [morseHead, morseHeadProj] using
      (morseHeadProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseHeadProj x) Set.univ).mono (by intro x hx; trivial)
  have hheadsub : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseHead x - morseCriticalSection φ (morseTail x)) u :=
    hhead.sub hcritSection
  have hprod : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x))) u :=
    hsqrt.mul hheadsub
  have htail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : MorseModel (n + 1) => morseTail x) u := by
    simpa [morseTail, morseTailProj] using
      (morseTailProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTailProj x) Set.univ).mono (by intro x hx; trivial)
  have hpair : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) u :=
    ContDiffOn.prodMk hprod htail
  have hcons : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × MorseModel n => morseConsLinearCLM p) Set.univ :=
    (morseConsLinearCLM.contDiff : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × MorseModel n => morseConsLinearCLM p)).contDiffOn
  have hcomp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MorseModel (n + 1) =>
      morseConsLinearCLM (Real.sqrt (2 * |morseSectionB f φ x|) *
        (morseHead x - morseCriticalSection φ (morseTail x)), morseTail x)) u :=
    hcons.comp hpair (by intro x hx; trivial)
  refine ⟨u, huOpen, hu0, ?_⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : MorseModel (n + 1) => morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) u
  simpa [morseSectionCompletion, morseSectionB] using hcomp

theorem isLocalHomeomorphAt_morseSectionCompletion_contDiffOn_smooth {n : ℕ}
    (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morseSection φ) (Metric.ball (0 : MorseModel n) r))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseSectionCompletion f φ ∧ 0 ∈ Φ.source ∧
      ∃ u : Set (MorseModel (n + 1)), IsOpen u ∧ (0 : MorseModel (n + 1)) ∈ u ∧
        u ⊆ Φ.source ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Φ : MorseModel (n + 1) → MorseModel (n + 1)) u ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) (Φ '' u) := by
  rcases morseSectionCompletion_contDiffOn_smooth f hf φ hcontσ hB0
    with ⟨uC, huCopen, huC0, hCompOn⟩
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by decide : (3 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hcontσ1 : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n) := by
    rcases hcontσ with ⟨r, hr, hOn⟩
    exact (hOn.contDiffAt (Metric.ball_mem_nhds (0 : MorseModel n) hr)).of_le
      (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hfd0 : fderiv ℝ (morseSectionCompletion f φ) 0 =
      (morseSectionCompletionDerivCLE f φ hB0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) :=
    (hasFDerivAt_morseSectionCompletion f hf3 hcrit φ hφ hsrc hdf hdfp hcontσ1 w hw hdiag hB0).fderiv
  have hfd0inv : ∃ e : (MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1)),
      (e : (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1))) = fderiv ℝ (morseSectionCompletion f φ) 0 := by
    refine ⟨morseSectionCompletionDerivCLE f φ hB0, ?_⟩
    exact hfd0.symm
  have h0inv : (0 : MorseModel (n + 1)) ∈
      (fun x : MorseModel (n + 1) => fderiv ℝ (morseSectionCompletion f φ) x) ⁻¹'
        (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
          (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1)))) :=
    Set.mem_preimage.mpr hfd0inv
  let Φ₀ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morseSectionCompletion f φ)
      (f' := morseSectionCompletionDerivCLE f φ hB0)
      (contDiffAt_morseSectionCompletion_smooth f hf hcrit φ hφ hsrc
        (by
          rcases hcontσ with ⟨r, hr, hOn⟩
          exact (hOn.contDiffAt (Metric.ball_mem_nhds (0 : MorseModel n) hr))) hB0)
      (hasFDerivAt_morseSectionCompletion f hf3 hcrit φ hφ hsrc hdf hdfp hcontσ1 w hw hdiag hB0)
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  let u : Set (MorseModel (n + 1)) := Φ₀.source ∩ uC ∩
    (fun x : MorseModel (n + 1) => fderiv ℝ (morseSectionCompletion f φ) x) ⁻¹'
      (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
        (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1))))
  have huOpen : IsOpen u := by
    have hfdOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => fderiv ℝ (morseSectionCompletion f φ) x) uC :=
      hCompOn.fderiv_of_isOpen huCopen (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤
        (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxU : x ∈ uC := hx.1.2
    have hc : ContinuousAt (fun x : MorseModel (n + 1) =>
        fderiv ℝ (morseSectionCompletion f φ) x) x :=
      (hfdOn.continuousOn x hxU).continuousAt (huCopen.mem_nhds hxU)
    have hpre : (fun x : MorseModel (n + 1) => fderiv ℝ (morseSectionCompletion f φ) x) ⁻¹'
        (Set.range ((↑) : ((MorseModel (n + 1)) ≃L[ℝ] (MorseModel (n + 1))) →
          (MorseModel (n + 1)) →L[ℝ] (MorseModel (n + 1)))) ∈ nhds x :=
      hc.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hx.2)
    exact Filter.inter_mem
      (Filter.inter_mem (IsOpen.mem_nhds Φ₀.open_source hx.1.1) (huCopen.mem_nhds hxU)) hpre
  have hu0 : (0 : MorseModel (n + 1)) ∈ u :=
    ⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, huC0⟩, h0inv⟩
  let Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) := Φ₀.restrOpen u huOpen
  have hΦfun : (Φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseSectionCompletion f φ := by
    rfl
  have hΦsource0 : (0 : MorseModel (n + 1)) ∈ Φ.source := by
    dsimp [Φ]
    constructor
    · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
    · exact hu0
  have huΦsource : u ⊆ Φ.source := by
    intro x hx
    have hsrc : Φ.source = Φ₀.source ∩ u := by
      dsimp [Φ]
    exact (hsrc.symm ▸ ⟨(by
      dsimp [u] at hx
      exact hx.1.1), hx⟩)
  have hΦOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) u := by
    rw [hΦfun]
    exact hCompOn.mono (by intro x hx; exact hx.1.2)
  have hΦsymmOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) Φ.target := by
    refine portPrivate_e0822189_contDiffOn_symm_of_contDiffOn Φ ?_ ?_
    · rw [hΦfun]
      exact hCompOn.mono (by
        intro x hx
        have hsrc : Φ.source = Φ₀.source ∩ u := by
          dsimp [Φ]
        have hxu : x ∈ u := (hsrc ▸ hx).2
        exact hxu.1.2)
    · intro x hx
      have hsrc : Φ.source = Φ₀.source ∩ u := by
        dsimp [Φ]
      have hxu : x ∈ u := (hsrc ▸ hx).2
      rcases hxu.2 with ⟨e, he⟩
      refine ⟨e, ?_⟩
      rw [hΦfun]
      exact he
  refine ⟨Φ, hΦfun, hΦsource0, u, huOpen, hu0, huΦsource, hΦOn, ?_⟩
  exact hΦsymmOn.mono (by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hsrc : Φ.source = Φ₀.source ∩ u := by
      dsimp [Φ]
    exact Φ.map_source (by
      exact (hsrc.symm ▸ ⟨hy.1.1, hy⟩)))

theorem morseTail_embedding {n : ℕ} (ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n)) :
    ∃ ι : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (ι : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun z => morseCons (morseHead z) (ψ (morseTail z))) ∧
      (ι.symm : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun y => morseCons (morseHead y) (ψ.symm (morseTail y))) ∧
      ι.source = {z : MorseModel (n + 1) | morseTail z ∈ ψ.source} ∧
      ι.target = {z : MorseModel (n + 1) | morseTail z ∈ ψ.target} := by
  let ι : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    { toFun := fun z => morseCons (morseHead z) (ψ (morseTail z))
      invFun := fun y => morseCons (morseHead y) (ψ.symm (morseTail y))
      source := {z : MorseModel (n + 1) | morseTail z ∈ ψ.source}
      target := {z : MorseModel (n + 1) | morseTail z ∈ ψ.target}
      map_source' := by intro z hz; simpa [morseCons_tail] using (ψ.map_source hz)
      map_target' := by intro y hy; simpa [morseCons_tail] using (ψ.map_target hy)
      left_inv' := by
        intro z hz
        have h' : ψ.symm (ψ (morseTail z)) = morseTail z := ψ.left_inv hz
        change morseCons (morseHead (morseCons (morseHead z) (ψ (morseTail z))))
            (ψ.symm (morseTail (morseCons (morseHead z) (ψ (morseTail z))))) = z
        rw [morseCons_tail, morseCons_head, h']
        exact (morse_cons_decompose z).symm
      right_inv' := by
        intro y hy
        have h' : ψ (ψ.symm (morseTail y)) = morseTail y := ψ.right_inv hy
        change morseCons (morseHead (morseCons (morseHead y) (ψ.symm (morseTail y))))
            (ψ (morseTail (morseCons (morseHead y) (ψ.symm (morseTail y))))) = y
        rw [morseCons_tail, morseCons_head, h']
        exact (morse_cons_decompose y).symm
      open_source := by
        have ht : Continuous (fun z : MorseModel (n + 1) => morseTail z) := by
          simpa [morseTail, morseTailProj] using (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont
        exact ψ.open_source.preimage ht
      open_target := by
        have ht : Continuous (fun z : MorseModel (n + 1) => morseTail z) := by
          simpa [morseTail, morseTailProj] using (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont
        exact ψ.open_target.preimage ht
      continuousOn_toFun := by
        have hhead : ContinuousOn (fun z : MorseModel (n + 1) => morseHead z) Set.univ := by
          exact (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ).cont.continuousOn
        have htail : ContinuousOn (fun z : MorseModel (n + 1) => morseTail z) Set.univ := by
          exact (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousOn
        have hψtail : ContinuousOn (fun z : MorseModel (n + 1) => ψ (morseTail z))
            {z : MorseModel (n + 1) | morseTail z ∈ ψ.source} :=
          ψ.continuousOn_toFun.comp (htail.mono (by intro z hz; trivial))
            (by intro z hz; exact hz)
        have hpair : ContinuousOn (fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z)))
            {z : MorseModel (n + 1) | morseTail z ∈ ψ.source} :=
          ContinuousOn.prodMk (hhead.mono (by intro z hz; trivial)) hψtail
        have hcons : ContinuousOn (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
            (Set.univ : Set (ℝ × MorseModel n)) :=
          (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).cont.continuousOn
        have hcomp : ContinuousOn (fun z : MorseModel (n + 1) =>
            morseConsLinearCLM (morseHead z, ψ (morseTail z)))
            {z : MorseModel (n + 1) | morseTail z ∈ ψ.source} :=
          hcons.comp hpair (by intro p hp; trivial)
        exact hcomp.congr fun z _ => by rfl
      continuousOn_invFun := by
        have hhead : ContinuousOn (fun y : MorseModel (n + 1) => morseHead y) Set.univ := by
          exact (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ).cont.continuousOn
        have htail : ContinuousOn (fun y : MorseModel (n + 1) => morseTail y) Set.univ := by
          exact (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousOn
        have hψsymmtail : ContinuousOn (fun y : MorseModel (n + 1) => ψ.symm (morseTail y))
            {y : MorseModel (n + 1) | morseTail y ∈ ψ.target} :=
          ψ.continuousOn_invFun.comp (htail.mono (by intro y hy; trivial))
            (by intro y hy; exact hy)
        have hpair : ContinuousOn (fun y : MorseModel (n + 1) => (morseHead y, ψ.symm (morseTail y)))
            {y : MorseModel (n + 1) | morseTail y ∈ ψ.target} :=
          ContinuousOn.prodMk (hhead.mono (by intro y hy; trivial)) hψsymmtail
        have hcons : ContinuousOn (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
            (Set.univ : Set (ℝ × MorseModel n)) :=
          (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).cont.continuousOn
        have hcomp : ContinuousOn (fun y : MorseModel (n + 1) =>
            morseConsLinearCLM (morseHead y, ψ.symm (morseTail y)))
            {y : MorseModel (n + 1) | morseTail y ∈ ψ.target} :=
          hcons.comp hpair (by intro p hp; trivial)
        exact hcomp.congr fun z _ => by rfl }
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl

theorem contDiffAt_morseTailEmbeddingFun {n : ℕ}
    (ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n))
    (hψ : ContDiffAt ℝ 1 (ψ : MorseModel n → MorseModel n) 0)
    (hψsymm : ContDiffAt ℝ 1 (ψ.symm : MorseModel n → MorseModel n) 0) :
    ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => morseCons (morseHead z) (ψ (morseTail z))) 0 ∧
    ContDiffAt ℝ 1 (fun y : MorseModel (n + 1) => morseCons (morseHead y) (ψ.symm (morseTail y))) 0 := by
  have htail : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => morseTail z) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun z => morseTailProj z) 0).of_le
          (by decide : (1 : WithTop ℕ∞) ≤ ⊤)
  have hhead : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => morseHead z) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ).contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun z => morseHeadProj z) 0).of_le
          (by decide : (1 : WithTop ℕ∞) ≤ ⊤)
  have hψtail : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => ψ (morseTail z)) 0 := by
    have hg' : ContDiffAt ℝ 1 (ψ : MorseModel n → MorseModel n)
        (morseTail (0 : MorseModel (n + 1))) := by
      rw [show morseTail (0 : MorseModel (n + 1)) = 0 by funext i; rfl]
      exact hψ
    exact (ContDiffAt.comp (x := 0) (g := ψ) (f := fun z : MorseModel (n + 1) => morseTail z)
      (hg := hg') (hf := htail))
  have hψtail' : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => ψ.symm (morseTail z)) 0 := by
    have hg' : ContDiffAt ℝ 1 (ψ.symm : MorseModel n → MorseModel n)
        (morseTail (0 : MorseModel (n + 1))) := by
      rw [show morseTail (0 : MorseModel (n + 1)) = 0 by funext i; rfl]
      exact hψsymm
    exact (ContDiffAt.comp (x := 0) (g := ψ.symm) (f := fun z : MorseModel (n + 1) => morseTail z)
      (hg := hg') (hf := htail))
  constructor
  · have hpair : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z))) 0 :=
      ContDiffAt.prodMk hhead hψtail
    have hlin : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morseHead (0 : MorseModel (n + 1)), ψ (morseTail (0 : MorseModel (n + 1)))) := by
      exact ((morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).contDiff.contDiffAt).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤)
    exact (ContDiffAt.comp (x := 0)
      (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (f := fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z)))
      (hg := hlin) (hf := hpair)).congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun z => by rfl
  · have hpair : ContDiffAt ℝ 1 (fun z : MorseModel (n + 1) => (morseHead z, ψ.symm (morseTail z))) 0 :=
      ContDiffAt.prodMk hhead hψtail'
    have hlin : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morseHead (0 : MorseModel (n + 1)), ψ.symm (morseTail (0 : MorseModel (n + 1)))) := by
      exact ((morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).contDiff.contDiffAt).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤)
    exact (ContDiffAt.comp (x := 0)
      (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (f := fun z : MorseModel (n + 1) => (morseHead z, ψ.symm (morseTail z)))
      (hg := hlin) (hf := hpair)).congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun z => by rfl

theorem contDiffAt_morseTailEmbeddingFun_smooth {n : ℕ}
    (ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n))
    (hψ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) 0)
    (hψsymm : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (ψ.symm : MorseModel n → MorseModel n) 0) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => morseCons (morseHead z) (ψ (morseTail z))) 0 ∧
    ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel (n + 1) => morseCons (morseHead y) (ψ.symm (morseTail y))) 0 := by
  have htail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => morseTail z) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun z => morseTailProj z) 0).of_le
          (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hhead : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => morseHead z) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ).contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun z => morseHeadProj z) 0).of_le
          (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hψtail : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => ψ (morseTail z)) 0 := by
    have hg' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n)
        (morseTail (0 : MorseModel (n + 1))) := by
      rw [show morseTail (0 : MorseModel (n + 1)) = 0 by funext i; rfl]
      exact hψ
    exact (ContDiffAt.comp (x := 0) (g := ψ) (f := fun z : MorseModel (n + 1) => morseTail z)
      (hg := hg') (hf := htail))
  have hψtail' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => ψ.symm (morseTail z)) 0 := by
    have hg' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n)
        (morseTail (0 : MorseModel (n + 1))) := by
      rw [show morseTail (0 : MorseModel (n + 1)) = 0 by funext i; rfl]
      exact hψsymm
    exact (ContDiffAt.comp (x := 0) (g := ψ.symm) (f := fun z : MorseModel (n + 1) => morseTail z)
      (hg := hg') (hf := htail))
  constructor
  · have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z))) 0 :=
      ContDiffAt.prodMk hhead hψtail
    have hlin : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morseHead (0 : MorseModel (n + 1)), ψ (morseTail (0 : MorseModel (n + 1)))) := by
      exact ((morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).contDiff.contDiffAt).of_le
        (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
    exact (ContDiffAt.comp (x := 0)
      (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (f := fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z)))
      (hg := hlin) (hf := hpair)).congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun z => by rfl
  · have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : MorseModel (n + 1) => (morseHead z, ψ.symm (morseTail z))) 0 :=
      ContDiffAt.prodMk hhead hψtail'
    have hlin : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morseHead (0 : MorseModel (n + 1)), ψ.symm (morseTail (0 : MorseModel (n + 1)))) := by
      exact ((morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).contDiff.contDiffAt).of_le
        (by decide : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
    exact (ContDiffAt.comp (x := 0)
      (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (f := fun z : MorseModel (n + 1) => (morseHead z, ψ.symm (morseTail z)))
      (hg := hlin) (hf := hpair)).congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun z => by rfl


theorem morse_lemma_diagonal_succ_smooth (n : ℕ)
    (ih : ∀ (g : MorseModel n → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g →
      fderiv ℝ g 0 = 0 →
      ∀ w' : Fin n → ℝ, (∀ i, w' i = -1 ∨ w' i = 1) →
      (∀ u v : MorseModel n, (fderiv ℝ (fderiv ℝ g) 0 u) v = ∑ i : Fin n, w' i * u i * v i) →
      ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
        0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
        ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) 0 ∧
        ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) 0 ∧
        (∃ v : Set (MorseModel n), IsOpen v ∧ (0 : MorseModel n) ∈ v ∧
          ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ : MorseModel n → MorseModel n) v ∧
          ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ψ.symm : MorseModel n → MorseModel n) (ψ '' v)) ∧
        ∀ y ∈ ψ.target, g (ψ y) = g 0 + (1 / 2) * ∑ i : Fin n, w' i * y i * y i)
    (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcrit : fderiv ℝ f 0 = 0)
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      (∃ v : Set (MorseModel (n + 1)), IsOpen v ∧ (0 : MorseModel (n + 1)) ∈ v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel (n + 1) → MorseModel (n + 1)) v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) (φ '' v)) ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin (n + 1), w i * y i * y i := by
  let g : MorseModel (n + 1) → ℝ := f
  have hgSmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g := by simpa [g] using hf
  have hg3 : ContDiff ℝ 3 g :=
    hgSmooth.of_le (by decide : (3 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hg2 : ContDiff ℝ 2 g :=
    hgSmooth.of_le (by decide : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hcritg : fderiv ℝ g 0 = 0 := by
    simpa [g] using hcrit
  have hdiagg : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ g) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i := by
    intro u v
    simpa [g] using hdiag u v
  let a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ :=
    fun x => 2 • morseTaylorBilin g x
  have ha : ∀ x, a x = 2 • morseTaylorBilin g x := by intro x; rfl
  have hsym : ∀ x y z, a x y z = a x z y := by
    intro x y z
    have hs := morseTaylorBilin_symm g hg2 x y z
    rw [ha x]
    simpa only [smul_apply] using congrArg (fun r : ℝ => 2 • r) hs
  have hw0 : w 0 ≠ 0 := by rcases hw 0 with h | h <;> simp [h]
  have hpiv : morsePivot (clmBilin a) 0 ≠ 0 := by
    have hp := hessian_diagonal_pivot g w hdiagg
    have hA : a 0 = fderiv ℝ (fderiv ℝ g) 0 := by
      rw [ha 0, morseTaylorBilin_zero g]
      apply ContinuousLinearMap.ext
      intro x
      apply ContinuousLinearMap.ext
      intro y
      simp [smul_eq_mul]
    dsimp [morsePivot, clmBilin]
    rw [hA, hp]
    exact hw0
  have h₀ : fderiv ℝ (morsePartial g) 0 morseE0 ≠ 0 := by
    have hfd0 := fderiv_morsePartial_e0 (n := n) g hg2
    have hp := hessian_diagonal_pivot g w hdiagg
    have happ : (fderiv ℝ (morsePartial g) 0) morseE0 = (fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0 :=
      congrFun hfd0 morseE0
    rw [happ, hp]
    exact hw0
  have hdfp : DifferentiableAt ℝ (morsePartial g) 0 := by
    have h1 : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0 := by
      have hfd2 : ContDiffAt ℝ 2 (fderiv ℝ g) 0 :=
        hg3.contDiffAt.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
      exact (hfd2.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))).clm_apply
        (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0)
    change DifferentiableAt ℝ (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0
    exact h1.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hcont : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartialMap g) 0 := by
    have hfdk : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) 0 :=
      hgSmooth.contDiffAt.fderiv_right (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤
        (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have hmp : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (morsePartial g) 0 := by
      have happ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0 :=
        hfdk.clm_apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : MorseModel (n + 1) => morseE0) 0)
      change ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0
      exact happ
    have htailc : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => morseTail x) 0 := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x => morseTailProj x) 0))
    have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : MorseModel (n + 1) => (morsePartial g x, morseTail x)) 0 :=
      ContDiffAt.prodMk hmp htailc
    have hcons : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morsePartial g 0, morseTail (0 : MorseModel (n + 1))) :=
      (morseConsLinearCLM.contDiff.contDiffAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p => morseConsLinearCLM p) (morsePartial g 0, morseTail (0 : MorseModel (n + 1))))
    exact (ContDiffAt.comp 0 hcons hpair).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  rcases morseSection_smooth (n := n) (k := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))) g hcritg hcont hdfp h₀
    with ⟨φ₀, hφ₀, hsrc₀, hcontσk, hcontσ2, hdfσ⟩
  have hB0 : morseSectionB g φ₀ 0 ≠ 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hB : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * ((fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0) := by
      dsimp [morseSectionB]
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hσ0]
      have hmt : (morseTaylorBilinAt g 0 0) morseE0 morseE0 =
          (morseTaylorBilin g 0) morseE0 morseE0 := by
        apply congrArg (fun L : MorseModel (n + 1) →L[ℝ] (MorseModel (n + 1) →L[ℝ] ℝ) =>
          L morseE0 morseE0)
        dsimp [morseTaylorBilinAt, morseTaylorBilin]
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      rw [hmt, morseTaylorBilin_zero g]
      simp [smul_eq_mul]
    have hp := hessian_diagonal_pivot g w hdiagg
    rw [hB, hp]
    have : (1 / 2 : ℝ) * w 0 ≠ 0 := by positivity
    exact this
  have hdfp0 : DifferentiableAt ℝ (morsePartial g) (morseSection φ₀ (0 : MorseModel n)) := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    simpa [hσ0] using hdfp
  have hcontσ1 : ContDiffAt ℝ 1 (morseSection φ₀) (0 : MorseModel n) :=
    hcontσ2.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
  rcases morseSection_contDiffOn_smooth g hgSmooth hcritg h₀ φ₀ hφ₀ hsrc₀ with ⟨rσ, hrσ, hσOn⟩
  rcases isLocalHomeomorphAt_morseSectionCompletion_contDiffOn_smooth g hf hcritg φ₀ hφ₀ hsrc₀ hdfσ hdfp0
    ⟨rσ, hrσ, hσOn⟩ w hw hdiagg hB0 with ⟨Φ, hΦ, hΦsource, uΦ, huΦOpen, huΦ0, huΦsource, hΦOn, hΦsymmOn⟩
  let g₁ : MorseModel n → ℝ := fun x' => g (morseSection φ₀ x')
  have hg₁local : ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁ (Metric.ball (0 : MorseModel n) r) := by
    rcases morseSection_contDiffOn_smooth g hgSmooth hcritg h₀ φ₀ hφ₀ hsrc₀ with ⟨r, hr, hσOn⟩
    refine ⟨r, hr, ?_⟩
    have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g Set.univ := hgSmooth.contDiffOn
    have hcomp' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x' : MorseModel n => g (morseSection φ₀ x')) (Metric.ball (0 : MorseModel n) r) :=
      hgOn.comp hσOn (by intro x hx; trivial)
    simpa [g₁] using hcomp'
  have hcritg₁ : fderiv ℝ g₁ 0 = 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hcomp : fderiv ℝ g₁ 0 = (fderiv ℝ g (morseSection φ₀ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ₀) (0 : MorseModel n)) := by
      have hdg : DifferentiableAt ℝ g (morseSection φ₀ (0 : MorseModel n)) :=
        (hg3.contDiffAt (x := morseSection φ₀ (0 : MorseModel n))).differentiableAt
          (by decide : (3 : WithTop ℕ∞) ≠ 0)
      have hdσ : DifferentiableAt ℝ (morseSection φ₀) (0 : MorseModel n) := hdfσ
      have h := fderiv_comp (x := (0 : MorseModel n)) (g := g) (f := morseSection φ₀)
        (hg := hdg) (hf := hdσ)
      change fderiv ℝ (g ∘ morseSection φ₀) 0 =
        (fderiv ℝ g (morseSection φ₀ 0)).comp (fderiv ℝ (morseSection φ₀) 0)
      exact h
    rw [hcomp, hσ0, hcritg]
    simp
  have hdiagg₁ : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ g₁) 0 u) v = ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    intro u v
    have hred := hessian_diagonal_reduced g hg2 hcritg a ha hsym hpiv φ₀ hφ₀ hsrc₀ hdfσ hdfp0 hcontσ2 w hdiagg u v
    simpa [g₁] using hred
  rcases exists_contDiff_extension (⊤ : ℕ∞) g₁ (0 : MorseModel n) hg₁local with
    ⟨g1ext, hg1extSmooth, hg1extEq⟩
  have hcritg1ext : fderiv ℝ g1ext 0 = 0 := by
    have hfd : fderiv ℝ g1ext 0 = fderiv ℝ g₁ 0 := Filter.EventuallyEq.fderiv_eq hg1extEq
    simpa [hcritg₁] using hfd
  have hdiagg1ext : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ g1ext) 0 u) v = ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    intro u v
    have hfd2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1ext x) 0 =
        fderiv ℝ (fun x : MorseModel n => fderiv ℝ g₁ x) 0 := by
      have hS : {x : MorseModel n | g1ext x = g₁ x} ∈ nhds (0 : MorseModel n) := hg1extEq
      rcases mem_nhds_iff.mp hS with ⟨U, hUS, hUopen, hU0⟩
      have hfdU : ∀ x ∈ U, fderiv ℝ g1ext x = fderiv ℝ g₁ x := by
        intro x hx
        have hgU : g1ext =ᶠ[nhds x] g₁ := by
          filter_upwards [hUopen.mem_nhds hx] with y hy
          exact hUS hy
        exact hgU.fderiv_eq
      have hfdEq : (fun x : MorseModel n => fderiv ℝ g1ext x) =ᶠ[nhds (0 : MorseModel n)]
          fun x => fderiv ℝ g₁ x := by
        filter_upwards [hUopen.mem_nhds hU0] with x hx
        exact hfdU x hx
      exact hfdEq.fderiv_eq
    change (fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1ext x) 0 u) v =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j
    rw [hfd2]
    simpa [g₁] using hdiagg₁ u v
  rcases ih g1ext hg1extSmooth hcritg1ext (fun j => w (Fin.succ j)) (by intro j; exact hw (Fin.succ j)) hdiagg1ext
    with ⟨ψ, hψsource, hψtarget, hψ0, hψsmooth, hψsymmSmooth, hψLocal, hψnorm⟩
  rcases mem_nhds_iff.mp hg1extEq with ⟨U, hUg1, hUopen, hU0⟩
  rcases morseTail_embedding ψ with ⟨ι, hι, hιsymm, hιsource, hιtarget⟩
  let Θ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) := ι.trans Φ.symm
  have hpm0 : morsePartialMap g 0 = 0 := by
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    dsimp [morsePartialMap, morsePartial]
    rw [htail0]
    have hfd : (fderiv ℝ g (0 : MorseModel (n + 1))) morseE0 = 0 := by simp [hcritg]
    simp [hfd, hz0]
  have hφ00 : φ₀ 0 = 0 := by
    simp [hφ₀, hpm0]
  have hφ0target0 : (0 : MorseModel (n + 1)) ∈ φ₀.target := by
    simpa [hφ00] using (φ₀.map_source hsrc₀)
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ]
    have hφsymm0 : φ₀.symm 0 = 0 := by
      have hlinv : φ₀.symm (φ₀ 0) = 0 := φ₀.left_inv hsrc₀
      rwa [hφ00] at hlinv
    have hc0 : morseCriticalSection φ₀ (0 : MorseModel n) = 0 := by
      dsimp [morseCriticalSection]
      have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      rw [hz0]
      simp [hφsymm0, morseHead]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    dsimp [morseSectionCompletion]
    simp [morseHead, htail0, hc0, hz0]
  have hΦsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) 0 :=
    hΦOn.contDiffAt (huΦOpen.mem_nhds huΦ0)
  have hΦsymmSmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    have hmem : Φ '' uΦ ∈ nhds (0 : MorseModel (n + 1)) := by
      have huΦopen : IsOpen (Φ '' uΦ) := Φ.isOpen_image_of_subset_source huΦOpen huΦsource
      have hval : Φ (0 : MorseModel (n + 1)) = 0 := hΦ0
      exact huΦopen.mem_nhds (by refine ⟨0, huΦ0, ?_⟩; simp [hval])
    exact hΦsymmOn.contDiffAt hmem
  have hιOnLocal : ∃ v : Set (MorseModel (n + 1)), IsOpen v ∧ (0 : MorseModel (n + 1)) ∈ v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ι : MorseModel (n + 1) → MorseModel (n + 1)) v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ι.symm : MorseModel (n + 1) → MorseModel (n + 1)) (ι '' v) := by
    rcases hψLocal with ⟨vψ, hvψOpen, hvψ0, hψOn, hψsymmOn⟩
    let vι : Set (MorseModel (n + 1)) := (fun z : MorseModel (n + 1) => morseTail z) ⁻¹' vψ
    have htailc : Continuous (fun z : MorseModel (n + 1) => morseTail z) := by
      change Continuous (fun z : MorseModel (n + 1) => morseTailProj z)
      exact (morseTailProj : (MorseModel (n + 1)) →L[ℝ] MorseModel n).cont
    have hvιOpen : IsOpen vι := by
      dsimp [vι]
      exact htailc.isOpen_preimage vψ hvψOpen
    have hvι0 : (0 : MorseModel (n + 1)) ∈ vι := by
      dsimp [vι]
      change morseTail (0 : MorseModel (n + 1)) ∈ vψ
      have hz : morseTail (0 : MorseModel (n + 1)) = 0 := by
        funext i
        simp [morseTail]
      simpa [hz] using hvψ0
    have hιOnV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (ι : MorseModel (n + 1) → MorseModel (n + 1)) vι := by
      rw [hι]
      have hhead : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => morseHead z) vι := by
        simpa [morseHead, morseHeadProj] using
          (morseHeadProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z : MorseModel (n + 1) => morseHeadProj z) Set.univ).mono (by intro z hz; trivial)
      have htail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => morseTail z) vι := by
        change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => morseTailProj z) vι
        exact ((morseTailProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => morseTailProj z) Set.univ).mono (by intro z hz; trivial))
      have hψtail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => ψ (morseTail z)) vι :=
        hψOn.comp htail (by intro z hz; dsimp [vι] at hz; exact hz)
      have hpair : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => (morseHead z, ψ (morseTail z))) vι :=
        ContDiffOn.prodMk hhead hψtail
      have hcons : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × MorseModel n => morseConsLinearCLM p) Set.univ :=
        (morseConsLinearCLM.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × MorseModel n => morseConsLinearCLM p) Set.univ)
      have hcomp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : MorseModel (n + 1) => morseConsLinearCLM (morseHead z, ψ (morseTail z))) vι :=
        hcons.comp hpair (by intro z hz; trivial)
      exact hcomp.congr fun z _ => by rfl
    have hιsymmOnV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (ι.symm : MorseModel (n + 1) → MorseModel (n + 1)) (ι '' vι) := by
      rw [hιsymm]
      have hmaps : Set.MapsTo (fun y : MorseModel (n + 1) => morseTail y) (ι '' vι) (ψ '' vψ) := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        refine ⟨morseTail z, ?_, ?_⟩
        · dsimp [vι] at hz
          exact hz
        · rw [hι]
          simp [morseCons_tail]
      have hhead : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseHead y) (ι '' vι) := by
        simpa [morseHead, morseHeadProj] using
          (morseHeadProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun y : MorseModel (n + 1) => morseHeadProj y) Set.univ).mono (by intro y hy; trivial)
      have htail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseTail y) (ι '' vι) := by
        change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseTailProj y) (ι '' vι)
        exact ((morseTailProj.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseTailProj y) Set.univ).mono (by intro y hy; trivial))
      have hψsymmtail : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => ψ.symm (morseTail y)) (ι '' vι) :=
        hψsymmOn.comp htail hmaps
      have hpair : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => (morseHead y, ψ.symm (morseTail y))) (ι '' vι) :=
        ContDiffOn.prodMk hhead hψsymmtail
      have hcons : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × MorseModel n => morseConsLinearCLM p) Set.univ :=
        (morseConsLinearCLM.contDiff.contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × MorseModel n => morseConsLinearCLM p) Set.univ)
      have hcomp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => morseConsLinearCLM (morseHead y, ψ.symm (morseTail y))) (ι '' vι) :=
        hcons.comp hpair (by intro y hy; trivial)
      exact hcomp.congr fun y _ => by rfl
    exact ⟨vι, hvιOpen, hvι0, hιOnV, hιsymmOnV⟩
  have hΘOnLocal : ∃ v : Set (MorseModel (n + 1)), IsOpen v ∧ (0 : MorseModel (n + 1)) ∈ v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Θ : MorseModel (n + 1) → MorseModel (n + 1)) v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) (Θ '' v) := by
    rcases hιOnLocal with ⟨vι, hvιOpen, hvι0, hιOnV, hιsymmOnV⟩
    have huΦopen : IsOpen (Φ '' uΦ) :=
      Φ.isOpen_image_of_subset_source huΦOpen huΦsource
    let vΘ : Set (MorseModel (n + 1)) := vι ∩ (fun y : MorseModel (n + 1) => ι y) ⁻¹' (Φ '' uΦ)
    have hvΘOpen : IsOpen vΘ := by
      dsimp [vΘ]
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hc : ContinuousAt ι x :=
        (hιOnV.continuousOn x hx.1).continuousAt (hvιOpen.mem_nhds hx.1)
      exact Filter.inter_mem (hvιOpen.mem_nhds hx.1)
        (hc.preimage_mem_nhds (huΦopen.mem_nhds hx.2))
    have hvΘ0 : (0 : MorseModel (n + 1)) ∈ vΘ := by
      dsimp [vΘ]
      constructor
      · exact hvι0
      · change ι (0 : MorseModel (n + 1)) ∈ Φ '' uΦ
        have h0in : (0 : MorseModel (n + 1)) ∈ Φ '' uΦ := by
          refine ⟨0, huΦ0, ?_⟩
          simp [hΦ0]
        have hι0v : ι (0 : MorseModel (n + 1)) = 0 := by
          rw [hι]
          funext i
          cases i using Fin.cases with
          | zero => simp [morseHead, morseCons]
          | succ j =>
              change (ψ (morseTail (0 : MorseModel (n + 1)))) j = 0
              have htail0 : morseTail (0 : MorseModel (n + 1)) = 0 := by
                funext i
                simp [morseTail]
              rw [htail0, hψ0]
              simp
        rw [hι0v]
        exact h0in
    have hΘOnV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Θ : MorseModel (n + 1) → MorseModel (n + 1)) vΘ := by
      have hfun : (Θ : MorseModel (n + 1) → MorseModel (n + 1)) =
          (fun y => Φ.symm (ι y)) := by
        dsimp [Θ]
        funext y
        rfl
      have hιOnV' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (ι : MorseModel (n + 1) → MorseModel (n + 1)) vΘ :=
        hιOnV.mono (by intro y hy; exact hy.1)
      have hmaps : Set.MapsTo (fun y : MorseModel (n + 1) => ι y) vΘ (Φ '' uΦ) := by
        intro y hy
        dsimp [vΘ] at hy
        exact hy.2
      have hcomp := hΦsymmOn.comp hιOnV' hmaps
      rw [hfun]
      exact hcomp
    have hΘsymmOnV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) (Θ '' vΘ) := by
      have hsymmfun : (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) =
          (fun y => ι.symm (Φ y)) := by
        dsimp [Θ]
        funext y
        rfl
      have hΦu_target : Φ '' uΦ ⊆ Φ.target := by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact Φ.map_source (huΦsource hy)
      have hΘv_sub_uΦ : Θ '' vΘ ⊆ uΦ := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        have hιz : ι z ∈ Φ '' uΦ := by
          dsimp [vΘ] at hz
          exact hz.2
        rcases hιz with ⟨w, hw, hιzw⟩
        have hwsrc : w ∈ Φ.source := huΦsource hw
        have hleft : Φ.symm (Φ w) = w := Φ.left_inv hwsrc
        have hΘz : Θ z = Φ.symm (ι z) := by
          dsimp [Θ]
        rw [hΘz, ← hιzw, hleft]
        exact hw
      have hΦOnV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : MorseModel (n + 1) => Φ y) (Θ '' vΘ) :=
        hΦOn.mono hΘv_sub_uΦ
      have hmaps : Set.MapsTo (fun y : MorseModel (n + 1) => Φ y) (Θ '' vΘ) (ι '' vι) := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        have hιzΦ : ι z ∈ Φ.target := hΦu_target (by
          dsimp [vΘ] at hz
          exact hz.2)
        have hΦy : Φ (Θ z) = ι z := by
          have hΘz : Θ z = Φ.symm (ι z) := by
            dsimp [Θ]
          rw [hΘz]
          exact Φ.right_inv hιzΦ
        refine ⟨z, ?_, hΦy.symm⟩
        dsimp [vΘ] at hz
        exact hz.1
      have hcomp := hιsymmOnV.comp hΦOnV hmaps
      rw [hsymmfun]
      exact hcomp
    exact ⟨vΘ, hvΘOpen, hvΘ0, hΘOnV, hΘsymmOnV⟩
  have hΦtarget0 : (0 : MorseModel (n + 1)) ∈ Φ.target := by
    simpa [hΦ0] using (Φ.map_source hΦsource)
  have hΦsymm0 : Φ.symm 0 = 0 := by
    have hrinv : Φ (Φ.symm 0) = 0 := Φ.right_inv hΦtarget0
    have hΦeq : Φ (Φ.symm 0) = Φ 0 := by
      simpa [hΦ0] using hrinv
    exact (Φ.injOn (Φ.map_target hΦtarget0) hΦsource hΦeq)
  have hι0 : ι 0 = 0 := by
    rw [hι]
    funext i
    cases i using Fin.cases with
    | zero => simp [morseHead, morseCons]
    | succ j =>
      change (morseCons (morseHead (0 : MorseModel (n + 1)))
          (ψ (morseTail (0 : MorseModel (n + 1))))) j.succ =
        (0 : MorseModel (n + 1)) j.succ
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hψ0]
      simp [morseCons]
  have hιsource0 : (0 : MorseModel (n + 1)) ∈ ι.source := by
    rw [hιsource]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    simp [htail0, hψsource]
  have hιtarget0 : (0 : MorseModel (n + 1)) ∈ ι.target := by
    rw [hιtarget]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    simp [htail0, hψtarget]
  have hΘsource0 : (0 : MorseModel (n + 1)) ∈ Θ.source := by
    dsimp [Θ]
    constructor
    · exact hιsource0
    · have hιΦ0 : ι 0 ∈ Φ.target := by
        simpa [hι0] using hΦtarget0
      exact hιΦ0
  have hΘtarget0 : (0 : MorseModel (n + 1)) ∈ Θ.target := by
    dsimp [Θ]
    constructor
    · exact hΦsource
    · simpa [hΦ0] using hιtarget0
  have hΘ0 : Θ 0 = 0 := by
    dsimp [Θ]
    simp [hι0, hΦsymm0]
  have hΘsymm0 : Θ.symm 0 = 0 := by
    have hrinv : Θ (Θ.symm 0) = 0 := Θ.right_inv hΘtarget0
    have hΘeq : Θ (Θ.symm 0) = Θ 0 := by
      simpa [hΘ0] using hrinv
    exact (Θ.injOn (Θ.map_target hΘtarget0) hΘsource0 hΘeq)
  have hιsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (ι : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    rw [hι]
    exact (contDiffAt_morseTailEmbeddingFun_smooth ψ hψsmooth hψsymmSmooth).1
  have hιsymmSmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (ι.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    rw [hιsymm]
    exact (contDiffAt_morseTailEmbeddingFun_smooth ψ hψsmooth hψsymmSmooth).2
  have hΘsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Θ : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    have hfun : (Θ : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun y => Φ.symm (ι y)) := by
      dsimp [Θ]
      funext y
      rfl
    have hg' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1))
        (ι (0 : MorseModel (n + 1))) := by
      simpa [hι0] using hΦsymmSmooth
    rw [hfun]
    exact (ContDiffAt.comp (x := 0) (g := Φ.symm) (f := ι) (hg := hg') (hf := hιsmooth))
  have hΘsymmSmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    have hsymmfun : (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun y => ι.symm (Φ y)) := by
      dsimp [Θ]
      rfl
    have hg' : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (ι.symm : MorseModel (n + 1) → MorseModel (n + 1))
        (Φ (0 : MorseModel (n + 1))) := by
      simpa [hΦ0] using hιsymmSmooth
    rw [hsymmfun]
    exact (ContDiffAt.comp (x := 0) (g := ι.symm) (f := Φ) (hg := hg') (hf := hΦsmooth))
  have hB0val : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * w 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hB : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * ((fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0) := by
      dsimp [morseSectionB]
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hσ0]
      have hmt : (morseTaylorBilinAt g 0 0) morseE0 morseE0 =
          (morseTaylorBilin g 0) morseE0 morseE0 := by
        apply congrArg (fun L : MorseModel (n + 1) →L[ℝ] (MorseModel (n + 1) →L[ℝ] ℝ) =>
          L morseE0 morseE0)
        dsimp [morseTaylorBilinAt, morseTaylorBilin]
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      rw [hmt, morseTaylorBilin_zero g]
      simp [smul_eq_mul]
    rw [hB, hessian_diagonal_pivot g w hdiagg]
  have hsign0 : SignType.sign (morseSectionB g φ₀ 0) = w 0 := by
    rw [hB0val]
    rcases hw 0 with hw0n | hw0p
    · rw [hw0n]
      have hs : SignType.sign ((1 / 2 : ℝ) * -1) = (-1 : SignType) := by
        rw [sign_eq_neg_one_iff]
        norm_num
      rw [hs]
      simp
    · rw [hw0p]
      have hs : SignType.sign ((1 / 2 : ℝ) * 1) = (1 : SignType) := by
        rw [sign_eq_one_iff]
        norm_num
      rw [hs]
      simp
  have hBcont : ContinuousAt (fun x : MorseModel (n + 1) => morseSectionB g φ₀ x)
      (0 : MorseModel (n + 1)) :=
    (contDiffAt_morseSectionB_smooth g hf hcritg φ₀ hφ₀ hsrc₀ hcontσk).continuousAt
  have hBΘcont : ContinuousAt (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y))
      (0 : MorseModel (n + 1)) := by
    have hBcont0 : ContinuousAt (fun x : MorseModel (n + 1) => morseSectionB g φ₀ x)
        (Θ (0 : MorseModel (n + 1))) := by
      rwa [hΘ0]
    exact hBcont0.comp (Θ.continuousAt hΘsource0)
  have hsignNhds : {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} ∈
      nhds (0 : MorseModel (n + 1)) := by
    have hc0 : morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) = morseSectionB g φ₀ 0 := by
      simp [hΘ0]
    rcases hw 0 with hw0n | hw0p
    · have hcneg : morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) < (0 : ℝ) := by
        rw [hc0, hB0val, hw0n]
        norm_num
      have hsub : (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y)) ⁻¹' Set.Iio (0 : ℝ) ⊆
          {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} := by
        intro y hy
        have hs : SignType.sign (morseSectionB g φ₀ (Θ y)) = (-1 : SignType) :=
          (sign_eq_neg_one_iff).2 hy
        change (SignType.sign (morseSectionB g φ₀ (Θ y)) : ℝ) = w 0
        rw [hw0n]
        rw [hs]
        simp
      exact Filter.mem_of_superset
        (hBΘcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hcneg)) hsub
    · have hcpos : (0 : ℝ) < morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) := by
        rw [hc0, hB0val, hw0p]
        norm_num
      have hsub : (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y)) ⁻¹' Set.Ioi (0 : ℝ) ⊆
          {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} := by
        intro y hy
        have hs : SignType.sign (morseSectionB g φ₀ (Θ y)) = (1 : SignType) :=
          (sign_eq_one_iff).2 hy
        change (SignType.sign (morseSectionB g φ₀ (Θ y)) : ℝ) = w 0
        rw [hw0p]
        rw [hs]
        simp
      exact Filter.mem_of_superset
        (hBΘcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hcpos)) hsub
  have hN_Θsource : Θ.source ∈ nhds (0 : MorseModel (n + 1)) := IsOpen.mem_nhds Θ.open_source hΘsource0
  have hN_U : {y : MorseModel (n + 1) | ψ (morseTail y) ∈ U} ∈ nhds (0 : MorseModel (n + 1)) := by
    have htailc : ContinuousAt (fun y : MorseModel (n + 1) => morseTail y) (0 : MorseModel (n + 1)) := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousAt)
    have hψc : ContinuousAt ψ (0 : MorseModel n) := ψ.continuousAt hψsource
    have hψt : ContinuousAt (fun y : MorseModel (n + 1) => ψ (morseTail y))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := ψ) (f := fun y : MorseModel (n + 1) => morseTail y)
          (x := (0 : MorseModel (n + 1))) hψc htailc)
    have hUnhds : U ∈ nhds (ψ (morseTail (0 : MorseModel (n + 1)))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hψ0]
      exact (IsOpen.mem_nhds hUopen hU0)
    exact hψt.preimage_mem_nhds hUnhds
  have hN_φ0 : {y : MorseModel (n + 1) | morseCons (0 : ℝ) (ψ (morseTail y)) ∈ φ₀.target} ∈
      nhds (0 : MorseModel (n + 1)) := by
    have htailc : ContinuousAt (fun y : MorseModel (n + 1) => morseTail y) (0 : MorseModel (n + 1)) := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousAt)
    have hψc : ContinuousAt ψ (0 : MorseModel n) := ψ.continuousAt hψsource
    have hψt : ContinuousAt (fun y : MorseModel (n + 1) => ψ (morseTail y))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := ψ) (f := fun y : MorseModel (n + 1) => morseTail y)
          (x := (0 : MorseModel (n + 1))) hψc htailc)
    have hcons0 : ContinuousAt (fun t : MorseModel n => morseCons (0 : ℝ) t)
        (0 : MorseModel n) := by
      have hf : ContinuousAt (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) :=
        continuousAt_const
      have hg : ContinuousAt (fun t : MorseModel n => t) (0 : MorseModel n) :=
        continuousAt_id
      simpa [morseCons] using (ContinuousAt.finCons (A := fun _ : Fin (n + 1) => ℝ) hf hg)
    have hcons0' : ContinuousAt (fun t : MorseModel n => morseCons (0 : ℝ) t)
        (ψ (morseTail (0 : MorseModel (n + 1)))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rwa [htail0, hψ0]
    have hcomp' : ContinuousAt (fun y : MorseModel (n + 1) => morseCons (0 : ℝ) (ψ (morseTail y)))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := fun t : MorseModel n => morseCons (0 : ℝ) t)
          (f := fun y : MorseModel (n + 1) => ψ (morseTail y))
          (x := (0 : MorseModel (n + 1))) hcons0' hψt)
    have htargetNhds : φ₀.target ∈ nhds (morseCons (0 : ℝ) (ψ (morseTail (0 : MorseModel (n + 1))))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      rw [htail0, hψ0, hz0]
      exact (IsOpen.mem_nhds φ₀.open_target hφ0target0)
    exact hcomp'.preimage_mem_nhds htargetNhds
  let V : Set (MorseModel (n + 1)) :=
    Θ.source ∩ {y | ψ (morseTail y) ∈ U} ∩
      {y | morseCons (0 : ℝ) (ψ (morseTail y)) ∈ φ₀.target} ∩
      {y | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0}
  have hV : V ∈ nhds (0 : MorseModel (n + 1)) := by
    dsimp [V]
    exact (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN_Θsource hN_U) hN_φ0) hsignNhds)
  let W : Set (MorseModel (n + 1)) := Θ ⁻¹' V
  have hW0 : W ∈ nhds (0 : MorseModel (n + 1)) := by
    dsimp [W]
    have hV0 : V ∈ nhds (Θ (0 : MorseModel (n + 1))) := by
      rwa [hΘ0]
    exact (Θ.continuousAt hΘsource0).preimage_mem_nhds hV0
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) := Θ.restr W
  have hφsource0 : (0 : MorseModel (n + 1)) ∈ φ.source := by
    dsimp [φ]
    constructor
    · exact hΘsource0
    · exact (mem_interior_iff_mem_nhds).2 hW0
  have hφtarget0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
    dsimp [φ]
    constructor
    · exact hΘtarget0
    · have hW0' : W ∈ nhds (Θ.symm (0 : MorseModel (n + 1))) := by
        rwa [hΘsymm0]
      exact (mem_interior_iff_mem_nhds).2 hW0'
  have hφ0 : φ 0 = 0 := by
    calc
      φ 0 = Θ 0 := by rfl
      _ = 0 := hΘ0
  have hφLocal : ∃ v : Set (MorseModel (n + 1)), IsOpen v ∧ (0 : MorseModel (n + 1)) ∈ v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel (n + 1) → MorseModel (n + 1)) v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) (φ '' v) := by
    rcases hΘOnLocal with ⟨vΘ, hvΘOpen, hvΘ0, hΘOnV, hΘsymmOnV⟩
    refine ⟨vΘ, hvΘOpen, hvΘ0, ?_, ?_⟩
    · dsimp [φ, OpenPartialHomeomorph.restr]
      exact hΘOnV
    · dsimp [φ, OpenPartialHomeomorph.restr]
      exact hΘsymmOnV
  refine ⟨φ, hφsource0, hφtarget0, hφ0, ?_, ?_, hφLocal, ?_⟩
  · dsimp [φ, OpenPartialHomeomorph.restr]
    exact hΘsmooth
  · dsimp [φ, OpenPartialHomeomorph.restr]
    exact hΘsymmSmooth
  intro y hy
  have hyAnd : y ∈ Θ.target ∧ Θ.symm y ∈ interior W := by
    dsimp [φ] at hy
    exact hy
  have hyV : y ∈ V := by
    have hWs : Θ.symm y ∈ W := interior_subset hyAnd.2
    have hΘsV : Θ (Θ.symm y) ∈ V := hWs
    have hΘs : Θ (Θ.symm y) = y := Θ.right_inv hyAnd.1
    rw [hΘs] at hΘsV
    exact hΘsV
  rcases hyV with ⟨⟨⟨hyΘs, hyU⟩, hyφ0⟩, hysign⟩
  have hιyΦ : ι y ∈ Φ.target := by
    have hysrc : y ∈ Θ.source := hyΘs
    dsimp [Θ] at hysrc
    exact hysrc.2
  let x : MorseModel (n + 1) := Θ y
  have hΦx : Φ x = ι y := by
    change Φ (Θ y) = ι y
    have hΘy : Θ y = Φ.symm (ι y) := by
      dsimp [Θ]
    rw [hΘy]
    exact Φ.right_inv hιyΦ
  have htailΦ : ∀ w : MorseModel (n + 1), morseTail (Φ w) = morseTail w := by
    intro w
    rw [hΦ]
    simp [morseSectionCompletion, morseCons_tail]
  have htailx : morseTail x = ψ (morseTail y) := by
    have htailΦx : morseTail (Φ x) = morseTail x := htailΦ x
    have hΦx' : morseTail (Φ x) = ψ (morseTail y) := by
      rw [hΦx, hι]
      simp [morseCons_tail]
    rw [← htailΦx]
    exact hΦx'
  have hheadΦx : morseHead (Φ x) = morseHead y := by
    rw [hΦx, hι]
    simp [morseCons_head]
  have htaily : morseTail y ∈ ψ.target := by
    have hΦyι : Φ y ∈ ι.target := by
      have hyΘt' : y ∈ Θ.target := hyAnd.1
      dsimp [Θ] at hyΘt'
      exact hyΘt'.2
    have hΦyt : morseTail (Φ y) ∈ ψ.target := by
      rw [hιtarget] at hΦyι
      exact hΦyι
    have htailΦy : morseTail (Φ y) = morseTail y := htailΦ y
    rw [← htailΦy]
    exact hΦyt
  have hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ₀.target := by
    rwa [htailx]
  have hsignx : SignType.sign (morseSectionB g φ₀ x) = w 0 := by
    simpa [x] using hysign
  have hBx : morseSectionB g φ₀ x ≠ 0 := by
    intro hB
    have hw0ne : w 0 ≠ 0 := by
      rcases hw 0 with hw0n' | hw0p'
      · simp [hw0n']
      · simp [hw0p']
    have hz : SignType.sign (morseSectionB g φ₀ x) = (0 : SignType) := by simp [hB]
    have hz0 : (SignType.sign (morseSectionB g φ₀ x) : ℝ) = (0 : ℝ) := by
      rw [hz]
      simp
    rw [hsignx] at hz0
    exact hw0ne hz0
  have hval := morseSectionCompletion_value g hg2 φ₀ hφ₀ (x := x) hx' hBx
  have hheadC : morseHead (morseSectionCompletion g φ₀ x) = morseHead y := by
    rw [← hΦ, hheadΦx]
  have hval' : g x - g (morseSection φ₀ (morseTail x)) = (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 := by
    rw [hsignx, hheadC] at hval
    exact hval
  have hg1ext0 : g1ext (0 : MorseModel n) = g 0 := by
    have hEq := hUg1 hU0
    calc
      g1ext (0 : MorseModel n) = g₁ (0 : MorseModel n) := hEq
      _ = g (morseSection φ₀ (0 : MorseModel n)) := rfl
      _ = g 0 := by
        rw [morseSection_zero g φ₀ hφ₀ hcritg hsrc₀]
  have hred : g (morseSection φ₀ (morseTail x)) =
      g 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
    have hg1extEq' : g1ext (ψ (morseTail y)) = g₁ (ψ (morseTail y)) := hUg1 hyU
    have hih := hψnorm (morseTail y) htaily
    have hg1 : g₁ (ψ (morseTail y)) = g (morseSection φ₀ (morseTail x)) := by
      dsimp [g₁]
      rw [← htailx]
    calc
      g (morseSection φ₀ (morseTail x)) = g₁ (ψ (morseTail y)) := hg1.symm
      _ = g1ext (ψ (morseTail y)) := hg1extEq'.symm
      _ = g1ext 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := hih
      _ = g 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
        rw [hg1ext0]
  have hmain : g x = g 0 + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 +
      (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
    have hsplit : g x = g (morseSection φ₀ (morseTail x)) + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 := by
      linarith [hval']
    rw [hred] at hsplit
    linarith
  have hfinal : g x = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by
    calc
      g x = g 0 + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 +
          (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := hmain
      _ = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by
        rw [Fin.sum_univ_succ]
        simp [morseHead, morseTail]
        ring
  have hφy : φ y = Θ y := by
    rfl
  calc
    f (φ y) = f (Θ y) := by rw [hφy]
    _ = g (Θ y) := by rfl
    _ = g x := by rfl
    _ = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := hfinal
    _ = f 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by rfl

theorem morse_lemma_diagonal_succ (n : ℕ)
    (ih : ∀ (g : MorseModel n → ℝ),
      ContDiff ℝ (n + 3) g →
      fderiv ℝ g 0 = 0 →
      ∀ w' : Fin n → ℝ, (∀ i, w' i = -1 ∨ w' i = 1) →
      (∀ u v : MorseModel n, (fderiv ℝ (fderiv ℝ g) 0 u) v = ∑ i : Fin n, w' i * u i * v i) →
      ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
        0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
        ContDiffAt ℝ 1 (ψ : MorseModel n → MorseModel n) 0 ∧
        ContDiffAt ℝ 1 (ψ.symm : MorseModel n → MorseModel n) 0 ∧
        ∀ y ∈ ψ.target, g (ψ y) = g 0 + (1 / 2) * ∑ i : Fin n, w' i * y i * y i)
    (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ (n + 4) f)
    (hcrit : fderiv ℝ f 0 = 0)
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ 1 (φ : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      ContDiffAt ℝ 1 (φ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin (n + 1), w i * y i * y i := by
  let g : MorseModel (n + 1) → ℝ := f
  have hgSmooth : ContDiff ℝ (n + 4) g := by simpa [g] using hf
  have hg3 : ContDiff ℝ 3 g :=
    hgSmooth.of_le (by exact_mod_cast (by omega : 3 ≤ n + 4))
  have hg2 : ContDiff ℝ 2 g :=
    hgSmooth.of_le (by exact_mod_cast (by omega : 2 ≤ n + 4))
  have hcritg : fderiv ℝ g 0 = 0 := by
    simpa [g] using hcrit
  have hdiagg : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ g) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i := by
    intro u v
    simpa [g] using hdiag u v
  let a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ :=
    fun x => 2 • morseTaylorBilin g x
  have ha : ∀ x, a x = 2 • morseTaylorBilin g x := by intro x; rfl
  have hsym : ∀ x y z, a x y z = a x z y := by
    intro x y z
    have hs := morseTaylorBilin_symm g hg2 x y z
    rw [ha x]
    simpa only [smul_apply] using congrArg (fun r : ℝ => 2 • r) hs
  have hw0 : w 0 ≠ 0 := by rcases hw 0 with h | h <;> simp [h]
  have hpiv : morsePivot (clmBilin a) 0 ≠ 0 := by
    have hp := hessian_diagonal_pivot g w hdiagg
    have hA : a 0 = fderiv ℝ (fderiv ℝ g) 0 := by
      rw [ha 0, morseTaylorBilin_zero g]
      apply ContinuousLinearMap.ext
      intro x
      apply ContinuousLinearMap.ext
      intro y
      simp [smul_eq_mul]
    dsimp [morsePivot, clmBilin]
    rw [hA, hp]
    exact hw0
  have h₀ : fderiv ℝ (morsePartial g) 0 morseE0 ≠ 0 := by
    have hfd0 := fderiv_morsePartial_e0 (n := n) g hg2
    have hp := hessian_diagonal_pivot g w hdiagg
    have happ : (fderiv ℝ (morsePartial g) 0) morseE0 = (fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0 :=
      congrFun hfd0 morseE0
    rw [happ, hp]
    exact hw0
  have hdfp : DifferentiableAt ℝ (morsePartial g) 0 := by
    have h1 : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0 := by
      have hfd2 : ContDiffAt ℝ 2 (fderiv ℝ g) 0 :=
        hg3.contDiffAt.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
      exact (hfd2.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))).clm_apply
        (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0)
    change DifferentiableAt ℝ (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0
    exact h1.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hcont : ContDiffAt ℝ (n + 3) (morsePartialMap g) 0 := by
    have hfdk : ContDiffAt ℝ (n + 3) (fderiv ℝ g) 0 :=
      hgSmooth.contDiffAt.fderiv_right (by exact_mod_cast (by omega : n + 3 + 1 ≤ n + 4))
    have hmp : ContDiffAt ℝ (n + 3) (morsePartial g) 0 := by
      have happ : ContDiffAt ℝ (n + 3) (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0 :=
        hfdk.clm_apply (contDiffAt_const : ContDiffAt ℝ (n + 3) (fun _ : MorseModel (n + 1) => morseE0) 0)
      change ContDiffAt ℝ (n + 3)
        (fun x : MorseModel (n + 1) => fderiv ℝ g x morseE0) 0
      exact happ
    have htailc : ContDiffAt ℝ (n + 3) (fun x : MorseModel (n + 1) => morseTail x) 0 := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ (n + 3) (fun x => morseTailProj x) 0))
    have hpair : ContDiffAt ℝ (n + 3) (fun x : MorseModel (n + 1) => (morsePartial g x, morseTail x)) 0 :=
      ContDiffAt.prodMk hmp htailc
    have hcons : ContDiffAt ℝ (n + 3) (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
        (morsePartial g 0, morseTail (0 : MorseModel (n + 1))) :=
      (morseConsLinearCLM.contDiff.contDiffAt : ContDiffAt ℝ (n + 3)
        (fun p => morseConsLinearCLM p) (morsePartial g 0, morseTail (0 : MorseModel (n + 1))))
    exact (ContDiffAt.comp 0 hcons hpair).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun x => by rfl
  rcases morseSection_smooth (n := n) (k := (n + 3 : ℕ))
    (by exact_mod_cast (by omega : 2 ≤ n + 3)) g hcritg hcont hdfp h₀
    with ⟨φ₀, hφ₀, hsrc₀, hcontσk, hcontσ2, hdfσ⟩
  have hB0 : morseSectionB g φ₀ 0 ≠ 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hB : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * ((fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0) := by
      dsimp [morseSectionB]
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hσ0]
      have hmt : (morseTaylorBilinAt g 0 0) morseE0 morseE0 =
          (morseTaylorBilin g 0) morseE0 morseE0 := by
        apply congrArg (fun L : MorseModel (n + 1) →L[ℝ] (MorseModel (n + 1) →L[ℝ] ℝ) =>
          L morseE0 morseE0)
        dsimp [morseTaylorBilinAt, morseTaylorBilin]
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      rw [hmt, morseTaylorBilin_zero g]
      simp [smul_eq_mul]
    have hp := hessian_diagonal_pivot g w hdiagg
    rw [hB, hp]
    have : (1 / 2 : ℝ) * w 0 ≠ 0 := by positivity
    exact this
  have hdfp0 : DifferentiableAt ℝ (morsePartial g) (morseSection φ₀ (0 : MorseModel n)) := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    simpa [hσ0] using hdfp
  have hcontσ1 : ContDiffAt ℝ 1 (morseSection φ₀) (0 : MorseModel n) :=
    hcontσ2.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
  rcases isLocalHomeomorphAt_morseSectionCompletion g hg3 hcritg φ₀ hφ₀ hsrc₀ hdfσ hdfp0 hcontσ1
    w hw hdiagg hB0 with ⟨Φ, hΦ, hΦsource, hΦsmooth, hΦsymmSmooth⟩
  let g₁ : MorseModel n → ℝ := fun x' => g (morseSection φ₀ x')
  have hg₁local : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ (n + 3) g₁ (Metric.ball (0 : MorseModel n) r) := by
    rcases (hcontσk.contDiffOn (le_rfl : ((n + 3 : ℕ) : WithTop ℕ∞) ≤ ((n + 3 : ℕ) : WithTop ℕ∞))
      (by intro h; exact (False.elim (WithTop.coe_ne_top (WithTop.coe_inj.mp h))))) with ⟨u, hu, hσOn⟩
    rcases mem_nhds_iff.mp hu with ⟨u', hu'u, hu'open, hu'0⟩
    have hσOn' : ContDiffOn ℝ (n + 3) (morseSection φ₀) u' := hσOn.mono hu'u
    have hg₁On : ContDiffOn ℝ (n + 3) g₁ u' := by
      have hgOn : ContDiffOn ℝ (n + 3) g Set.univ := hgSmooth.contDiffOn.of_le
        (by exact_mod_cast (by omega : n + 3 ≤ n + 4))
      have hc : ContDiffOn ℝ (n + 3) (fun x' : MorseModel n => morseSection φ₀ x') u' := hσOn'
      have hcomp' : ContDiffOn ℝ (n + 3) (fun x' : MorseModel n => g (morseSection φ₀ x')) u' :=
        hgOn.comp hc (by intro x hx; exact Set.mem_univ _)
      simpa [g₁] using hcomp'
    rcases Metric.mem_nhds_iff.mp (hu'open.mem_nhds hu'0) with ⟨r, hr, hball⟩
    refine ⟨r, hr, ?_⟩
    exact hg₁On.mono (by intro x hx; exact hball (Metric.mem_ball.mp hx))
  have hcritg₁ : fderiv ℝ g₁ 0 = 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hcomp : fderiv ℝ g₁ 0 = (fderiv ℝ g (morseSection φ₀ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ₀) (0 : MorseModel n)) := by
      have hdg : DifferentiableAt ℝ g (morseSection φ₀ (0 : MorseModel n)) :=
        (hg3.contDiffAt (x := morseSection φ₀ (0 : MorseModel n))).differentiableAt
          (by decide : (3 : WithTop ℕ∞) ≠ 0)
      have hdσ : DifferentiableAt ℝ (morseSection φ₀) (0 : MorseModel n) := hdfσ
      have h := fderiv_comp (x := (0 : MorseModel n)) (g := g) (f := morseSection φ₀)
        (hg := hdg) (hf := hdσ)
      change fderiv ℝ (g ∘ morseSection φ₀) 0 =
        (fderiv ℝ g (morseSection φ₀ 0)).comp (fderiv ℝ (morseSection φ₀) 0)
      exact h
    rw [hcomp, hσ0, hcritg]
    simp
  have hdiagg₁ : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ g₁) 0 u) v = ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    intro u v
    have hred := hessian_diagonal_reduced g hg2 hcritg a ha hsym hpiv φ₀ hφ₀ hsrc₀ hdfσ hdfp0 hcontσ2 w hdiagg u v
    simpa [g₁] using hred
  rcases exists_contDiff_extension (n + 3 : ℕ∞) g₁ (0 : MorseModel n) hg₁local with
    ⟨g1ext, hg1extSmooth, hg1extEq⟩
  have hcritg1ext : fderiv ℝ g1ext 0 = 0 := by
    have hfd : fderiv ℝ g1ext 0 = fderiv ℝ g₁ 0 := Filter.EventuallyEq.fderiv_eq hg1extEq
    simpa [hcritg₁] using hfd
  have hdiagg1ext : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ g1ext) 0 u) v = ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    intro u v
    have hfd2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1ext x) 0 =
        fderiv ℝ (fun x : MorseModel n => fderiv ℝ g₁ x) 0 := by
      have hS : {x : MorseModel n | g1ext x = g₁ x} ∈ nhds (0 : MorseModel n) := hg1extEq
      rcases mem_nhds_iff.mp hS with ⟨U, hUS, hUopen, hU0⟩
      have hfdU : ∀ x ∈ U, fderiv ℝ g1ext x = fderiv ℝ g₁ x := by
        intro x hx
        have hgU : g1ext =ᶠ[nhds x] g₁ := by
          filter_upwards [hUopen.mem_nhds hx] with y hy
          exact hUS hy
        exact hgU.fderiv_eq
      have hfdEq : (fun x : MorseModel n => fderiv ℝ g1ext x) =ᶠ[nhds (0 : MorseModel n)]
          fun x => fderiv ℝ g₁ x := by
        filter_upwards [hUopen.mem_nhds hU0] with x hx
        exact hfdU x hx
      exact hfdEq.fderiv_eq
    change (fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1ext x) 0 u) v =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j
    rw [hfd2]
    simpa [g₁] using hdiagg₁ u v
  rcases ih g1ext hg1extSmooth hcritg1ext (fun j => w (Fin.succ j)) (by intro j; exact hw (Fin.succ j)) hdiagg1ext
    with ⟨ψ, hψsource, hψtarget, hψ0, hψsmooth, hψsymmSmooth, hψnorm⟩
  rcases mem_nhds_iff.mp hg1extEq with ⟨U, hUg1, hUopen, hU0⟩
  rcases morseTail_embedding ψ with ⟨ι, hι, hιsymm, hιsource, hιtarget⟩
  let Θ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) := ι.trans Φ.symm
  have hpm0 : morsePartialMap g 0 = 0 := by
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    dsimp [morsePartialMap, morsePartial]
    rw [htail0]
    have hfd : (fderiv ℝ g (0 : MorseModel (n + 1))) morseE0 = 0 := by simp [hcritg]
    simp [hfd, hz0]
  have hφ00 : φ₀ 0 = 0 := by
    simp [hφ₀, hpm0]
  have hφ0target0 : (0 : MorseModel (n + 1)) ∈ φ₀.target := by
    simpa [hφ00] using (φ₀.map_source hsrc₀)
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ]
    have hφsymm0 : φ₀.symm 0 = 0 := by
      have hlinv : φ₀.symm (φ₀ 0) = 0 := φ₀.left_inv hsrc₀
      rwa [hφ00] at hlinv
    have hc0 : morseCriticalSection φ₀ (0 : MorseModel n) = 0 := by
      dsimp [morseCriticalSection]
      have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      rw [hz0]
      simp [hφsymm0, morseHead]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    dsimp [morseSectionCompletion]
    simp [morseHead, htail0, hc0, hz0]
  have hΦtarget0 : (0 : MorseModel (n + 1)) ∈ Φ.target := by
    simpa [hΦ0] using (Φ.map_source hΦsource)
  have hΦsymm0 : Φ.symm 0 = 0 := by
    have hrinv : Φ (Φ.symm 0) = 0 := Φ.right_inv hΦtarget0
    have hΦeq : Φ (Φ.symm 0) = Φ 0 := by
      simpa [hΦ0] using hrinv
    exact (Φ.injOn (Φ.map_target hΦtarget0) hΦsource hΦeq)
  have hι0 : ι 0 = 0 := by
    rw [hι]
    funext i
    cases i using Fin.cases with
    | zero => simp [morseHead, morseCons]
    | succ j =>
      change (morseCons (morseHead (0 : MorseModel (n + 1)))
          (ψ (morseTail (0 : MorseModel (n + 1))))) j.succ =
        (0 : MorseModel (n + 1)) j.succ
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hψ0]
      simp [morseCons]
  have hιsource0 : (0 : MorseModel (n + 1)) ∈ ι.source := by
    rw [hιsource]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    simp [htail0, hψsource]
  have hιtarget0 : (0 : MorseModel (n + 1)) ∈ ι.target := by
    rw [hιtarget]
    have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
      funext i
      simp [morseTail]
    simp [htail0, hψtarget]
  have hΘsource0 : (0 : MorseModel (n + 1)) ∈ Θ.source := by
    dsimp [Θ]
    constructor
    · exact hιsource0
    · have hιΦ0 : ι 0 ∈ Φ.target := by
        simpa [hι0] using hΦtarget0
      exact hιΦ0
  have hΘtarget0 : (0 : MorseModel (n + 1)) ∈ Θ.target := by
    dsimp [Θ]
    constructor
    · exact hΦsource
    · simpa [hΦ0] using hιtarget0
  have hΘ0 : Θ 0 = 0 := by
    dsimp [Θ]
    simp [hι0, hΦsymm0]
  have hΘsymm0 : Θ.symm 0 = 0 := by
    have hrinv : Θ (Θ.symm 0) = 0 := Θ.right_inv hΘtarget0
    have hΘeq : Θ (Θ.symm 0) = Θ 0 := by
      simpa [hΘ0] using hrinv
    exact (Θ.injOn (Θ.map_target hΘtarget0) hΘsource0 hΘeq)
  have hιsmooth : ContDiffAt ℝ 1 (ι : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    rw [hι]
    exact (contDiffAt_morseTailEmbeddingFun ψ hψsmooth hψsymmSmooth).1
  have hιsymmSmooth : ContDiffAt ℝ 1 (ι.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    rw [hιsymm]
    exact (contDiffAt_morseTailEmbeddingFun ψ hψsmooth hψsymmSmooth).2
  have hΘsmooth : ContDiffAt ℝ 1 (Θ : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    have hfun : (Θ : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun y => Φ.symm (ι y)) := by
      dsimp [Θ]
      funext y
      rfl
    have hg' : ContDiffAt ℝ 1 (Φ.symm : MorseModel (n + 1) → MorseModel (n + 1))
        (ι (0 : MorseModel (n + 1))) := by
      simpa [hι0] using hΦsymmSmooth
    rw [hfun]
    exact (ContDiffAt.comp (x := 0) (g := Φ.symm) (f := ι) (hg := hg') (hf := hιsmooth))
  have hΘsymmSmooth : ContDiffAt ℝ 1 (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) 0 := by
    have hsymmfun : (Θ.symm : MorseModel (n + 1) → MorseModel (n + 1)) =
        (fun y => ι.symm (Φ y)) := by
      dsimp [Θ]
      rfl
    have hg' : ContDiffAt ℝ 1 (ι.symm : MorseModel (n + 1) → MorseModel (n + 1))
        (Φ (0 : MorseModel (n + 1))) := by
      simpa [hΦ0] using hιsymmSmooth
    rw [hsymmfun]
    exact (ContDiffAt.comp (x := 0) (g := ι.symm) (f := Φ) (hg := hg') (hf := hΦsmooth))
  have hB0val : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * w 0 := by
    have hσ0 : morseSection φ₀ (0 : MorseModel n) = 0 := morseSection_zero g φ₀ hφ₀ hcritg hsrc₀
    have hB : morseSectionB g φ₀ 0 = (1 / 2 : ℝ) * ((fderiv ℝ (fderiv ℝ g) 0) morseE0 morseE0) := by
      dsimp [morseSectionB]
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hσ0]
      have hmt : (morseTaylorBilinAt g 0 0) morseE0 morseE0 =
          (morseTaylorBilin g 0) morseE0 morseE0 := by
        apply congrArg (fun L : MorseModel (n + 1) →L[ℝ] (MorseModel (n + 1) →L[ℝ] ℝ) =>
          L morseE0 morseE0)
        dsimp [morseTaylorBilinAt, morseTaylorBilin]
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      rw [hmt, morseTaylorBilin_zero g]
      simp [smul_eq_mul]
    rw [hB, hessian_diagonal_pivot g w hdiagg]
  have hsign0 : SignType.sign (morseSectionB g φ₀ 0) = w 0 := by
    rw [hB0val]
    rcases hw 0 with hw0n | hw0p
    · rw [hw0n]
      have hs : SignType.sign ((1 / 2 : ℝ) * -1) = (-1 : SignType) := by
        rw [sign_eq_neg_one_iff]
        norm_num
      rw [hs]
      simp
    · rw [hw0p]
      have hs : SignType.sign ((1 / 2 : ℝ) * 1) = (1 : SignType) := by
        rw [sign_eq_one_iff]
        norm_num
      rw [hs]
      simp
  have hBcont : ContinuousAt (fun x : MorseModel (n + 1) => morseSectionB g φ₀ x)
      (0 : MorseModel (n + 1)) :=
    (contDiffAt_morseSectionB g hg3 hcritg φ₀ hφ₀ hsrc₀ hcontσ1).continuousAt
  have hBΘcont : ContinuousAt (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y))
      (0 : MorseModel (n + 1)) := by
    have hBcont0 : ContinuousAt (fun x : MorseModel (n + 1) => morseSectionB g φ₀ x)
        (Θ (0 : MorseModel (n + 1))) := by
      rwa [hΘ0]
    exact hBcont0.comp (Θ.continuousAt hΘsource0)
  have hsignNhds : {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} ∈
      nhds (0 : MorseModel (n + 1)) := by
    have hc0 : morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) = morseSectionB g φ₀ 0 := by
      simp [hΘ0]
    rcases hw 0 with hw0n | hw0p
    · have hcneg : morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) < (0 : ℝ) := by
        rw [hc0, hB0val, hw0n]
        norm_num
      have hsub : (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y)) ⁻¹' Set.Iio (0 : ℝ) ⊆
          {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} := by
        intro y hy
        have hs : SignType.sign (morseSectionB g φ₀ (Θ y)) = (-1 : SignType) :=
          (sign_eq_neg_one_iff).2 hy
        change (SignType.sign (morseSectionB g φ₀ (Θ y)) : ℝ) = w 0
        rw [hw0n]
        rw [hs]
        simp
      exact Filter.mem_of_superset
        (hBΘcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hcneg)) hsub
    · have hcpos : (0 : ℝ) < morseSectionB g φ₀ (Θ (0 : MorseModel (n + 1))) := by
        rw [hc0, hB0val, hw0p]
        norm_num
      have hsub : (fun y : MorseModel (n + 1) => morseSectionB g φ₀ (Θ y)) ⁻¹' Set.Ioi (0 : ℝ) ⊆
          {y : MorseModel (n + 1) | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0} := by
        intro y hy
        have hs : SignType.sign (morseSectionB g φ₀ (Θ y)) = (1 : SignType) :=
          (sign_eq_one_iff).2 hy
        change (SignType.sign (morseSectionB g φ₀ (Θ y)) : ℝ) = w 0
        rw [hw0p]
        rw [hs]
        simp
      exact Filter.mem_of_superset
        (hBΘcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hcpos)) hsub
  have hN_Θsource : Θ.source ∈ nhds (0 : MorseModel (n + 1)) := IsOpen.mem_nhds Θ.open_source hΘsource0
  have hN_U : {y : MorseModel (n + 1) | ψ (morseTail y) ∈ U} ∈ nhds (0 : MorseModel (n + 1)) := by
    have htailc : ContinuousAt (fun y : MorseModel (n + 1) => morseTail y) (0 : MorseModel (n + 1)) := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousAt)
    have hψc : ContinuousAt ψ (0 : MorseModel n) := ψ.continuousAt hψsource
    have hψt : ContinuousAt (fun y : MorseModel (n + 1) => ψ (morseTail y))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := ψ) (f := fun y : MorseModel (n + 1) => morseTail y)
          (x := (0 : MorseModel (n + 1))) hψc htailc)
    have hUnhds : U ∈ nhds (ψ (morseTail (0 : MorseModel (n + 1)))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rw [htail0, hψ0]
      exact (IsOpen.mem_nhds hUopen hU0)
    exact hψt.preimage_mem_nhds hUnhds
  have hN_φ0 : {y : MorseModel (n + 1) | morseCons (0 : ℝ) (ψ (morseTail y)) ∈ φ₀.target} ∈
      nhds (0 : MorseModel (n + 1)) := by
    have htailc : ContinuousAt (fun y : MorseModel (n + 1) => morseTail y) (0 : MorseModel (n + 1)) := by
      simpa [morseTail, morseTailProj] using
        ((morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n).cont.continuousAt)
    have hψc : ContinuousAt ψ (0 : MorseModel n) := ψ.continuousAt hψsource
    have hψt : ContinuousAt (fun y : MorseModel (n + 1) => ψ (morseTail y))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := ψ) (f := fun y : MorseModel (n + 1) => morseTail y)
          (x := (0 : MorseModel (n + 1))) hψc htailc)
    have hcons0 : ContinuousAt (fun t : MorseModel n => morseCons (0 : ℝ) t)
        (0 : MorseModel n) := by
      have hf : ContinuousAt (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) :=
        continuousAt_const
      have hg : ContinuousAt (fun t : MorseModel n => t) (0 : MorseModel n) :=
        continuousAt_id
      simpa [morseCons] using (ContinuousAt.finCons (A := fun _ : Fin (n + 1) => ℝ) hf hg)
    have hcons0' : ContinuousAt (fun t : MorseModel n => morseCons (0 : ℝ) t)
        (ψ (morseTail (0 : MorseModel (n + 1)))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      rwa [htail0, hψ0]
    have hcomp' : ContinuousAt (fun y : MorseModel (n + 1) => morseCons (0 : ℝ) (ψ (morseTail y)))
        (0 : MorseModel (n + 1)) := by
      simpa [Function.comp_def] using
        (ContinuousAt.comp (g := fun t : MorseModel n => morseCons (0 : ℝ) t)
          (f := fun y : MorseModel (n + 1) => ψ (morseTail y))
          (x := (0 : MorseModel (n + 1))) hcons0' hψt)
    have htargetNhds : φ₀.target ∈ nhds (morseCons (0 : ℝ) (ψ (morseTail (0 : MorseModel (n + 1))))) := by
      have htail0 : morseTail (0 : MorseModel (n + 1)) = (0 : MorseModel n) := by
        funext i
        simp [morseTail]
      have hz0 : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      rw [htail0, hψ0, hz0]
      exact (IsOpen.mem_nhds φ₀.open_target hφ0target0)
    exact hcomp'.preimage_mem_nhds htargetNhds
  let V : Set (MorseModel (n + 1)) :=
    Θ.source ∩ {y | ψ (morseTail y) ∈ U} ∩
      {y | morseCons (0 : ℝ) (ψ (morseTail y)) ∈ φ₀.target} ∩
      {y | SignType.sign (morseSectionB g φ₀ (Θ y)) = w 0}
  have hV : V ∈ nhds (0 : MorseModel (n + 1)) := by
    dsimp [V]
    exact (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN_Θsource hN_U) hN_φ0) hsignNhds)
  let W : Set (MorseModel (n + 1)) := Θ ⁻¹' V
  have hW0 : W ∈ nhds (0 : MorseModel (n + 1)) := by
    dsimp [W]
    have hV0 : V ∈ nhds (Θ (0 : MorseModel (n + 1))) := by
      rwa [hΘ0]
    exact (Θ.continuousAt hΘsource0).preimage_mem_nhds hV0
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) := Θ.restr W
  have hφsource0 : (0 : MorseModel (n + 1)) ∈ φ.source := by
    dsimp [φ]
    constructor
    · exact hΘsource0
    · exact (mem_interior_iff_mem_nhds).2 hW0
  have hφtarget0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
    dsimp [φ]
    constructor
    · exact hΘtarget0
    · have hW0' : W ∈ nhds (Θ.symm (0 : MorseModel (n + 1))) := by
        rwa [hΘsymm0]
      exact (mem_interior_iff_mem_nhds).2 hW0'
  have hφ0 : φ 0 = 0 := by
    calc
      φ 0 = Θ 0 := by rfl
      _ = 0 := hΘ0
  refine ⟨φ, hφsource0, hφtarget0, hφ0, ?_, ?_, ?_⟩
  · dsimp [φ, OpenPartialHomeomorph.restr]
    exact hΘsmooth
  · dsimp [φ, OpenPartialHomeomorph.restr]
    exact hΘsymmSmooth
  intro y hy
  have hyAnd : y ∈ Θ.target ∧ Θ.symm y ∈ interior W := by
    dsimp [φ] at hy
    exact hy
  have hyV : y ∈ V := by
    have hWs : Θ.symm y ∈ W := interior_subset hyAnd.2
    have hΘsV : Θ (Θ.symm y) ∈ V := hWs
    have hΘs : Θ (Θ.symm y) = y := Θ.right_inv hyAnd.1
    rw [hΘs] at hΘsV
    exact hΘsV
  rcases hyV with ⟨⟨⟨hyΘs, hyU⟩, hyφ0⟩, hysign⟩
  have hιyΦ : ι y ∈ Φ.target := by
    have hysrc : y ∈ Θ.source := hyΘs
    dsimp [Θ] at hysrc
    exact hysrc.2
  let x : MorseModel (n + 1) := Θ y
  have hΦx : Φ x = ι y := by
    change Φ (Θ y) = ι y
    have hΘy : Θ y = Φ.symm (ι y) := by
      dsimp [Θ]
    rw [hΘy]
    exact Φ.right_inv hιyΦ
  have htailΦ : ∀ w : MorseModel (n + 1), morseTail (Φ w) = morseTail w := by
    intro w
    rw [hΦ]
    simp [morseSectionCompletion, morseCons_tail]
  have htailx : morseTail x = ψ (morseTail y) := by
    have htailΦx : morseTail (Φ x) = morseTail x := htailΦ x
    have hΦx' : morseTail (Φ x) = ψ (morseTail y) := by
      rw [hΦx, hι]
      simp [morseCons_tail]
    rw [← htailΦx]
    exact hΦx'
  have hheadΦx : morseHead (Φ x) = morseHead y := by
    rw [hΦx, hι]
    simp [morseCons_head]
  have htaily : morseTail y ∈ ψ.target := by
    have hΦyι : Φ y ∈ ι.target := by
      have hyΘt' : y ∈ Θ.target := hyAnd.1
      dsimp [Θ] at hyΘt'
      exact hyΘt'.2
    have hΦyt : morseTail (Φ y) ∈ ψ.target := by
      rw [hιtarget] at hΦyι
      exact hΦyι
    have htailΦy : morseTail (Φ y) = morseTail y := htailΦ y
    rw [← htailΦy]
    exact hΦyt
  have hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ₀.target := by
    rwa [htailx]
  have hsignx : SignType.sign (morseSectionB g φ₀ x) = w 0 := by
    simpa [x] using hysign
  have hBx : morseSectionB g φ₀ x ≠ 0 := by
    intro hB
    have hw0ne : w 0 ≠ 0 := by
      rcases hw 0 with hw0n' | hw0p'
      · simp [hw0n']
      · simp [hw0p']
    have hz : SignType.sign (morseSectionB g φ₀ x) = (0 : SignType) := by simp [hB]
    have hz0 : (SignType.sign (morseSectionB g φ₀ x) : ℝ) = (0 : ℝ) := by
      rw [hz]
      simp
    rw [hsignx] at hz0
    exact hw0ne hz0
  have hval := morseSectionCompletion_value g hg2 φ₀ hφ₀ (x := x) hx' hBx
  have hheadC : morseHead (morseSectionCompletion g φ₀ x) = morseHead y := by
    rw [← hΦ, hheadΦx]
  have hval' : g x - g (morseSection φ₀ (morseTail x)) = (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 := by
    rw [hsignx, hheadC] at hval
    exact hval
  have hg1ext0 : g1ext (0 : MorseModel n) = g 0 := by
    have hEq := hUg1 hU0
    calc
      g1ext (0 : MorseModel n) = g₁ (0 : MorseModel n) := hEq
      _ = g (morseSection φ₀ (0 : MorseModel n)) := rfl
      _ = g 0 := by
        rw [morseSection_zero g φ₀ hφ₀ hcritg hsrc₀]
  have hred : g (morseSection φ₀ (morseTail x)) =
      g 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
    have hg1extEq' : g1ext (ψ (morseTail y)) = g₁ (ψ (morseTail y)) := hUg1 hyU
    have hih := hψnorm (morseTail y) htaily
    have hg1 : g₁ (ψ (morseTail y)) = g (morseSection φ₀ (morseTail x)) := by
      dsimp [g₁]
      rw [← htailx]
    calc
      g (morseSection φ₀ (morseTail x)) = g₁ (ψ (morseTail y)) := hg1.symm
      _ = g1ext (ψ (morseTail y)) := hg1extEq'.symm
      _ = g1ext 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := hih
      _ = g 0 + (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
        rw [hg1ext0]
  have hmain : g x = g 0 + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 +
      (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := by
    have hsplit : g x = g (morseSection φ₀ (morseTail x)) + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 := by
      linarith [hval']
    rw [hred] at hsplit
    linarith
  have hfinal : g x = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by
    calc
      g x = g 0 + (1 / 2 : ℝ) * w 0 * (morseHead y) ^ 2 +
          (1 / 2 : ℝ) * ∑ j : Fin n, w (Fin.succ j) * (morseTail y j) * (morseTail y j) := hmain
      _ = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by
        rw [Fin.sum_univ_succ]
        simp [morseHead, morseTail]
        ring
  have hφy : φ y = Θ y := by
    rfl
  calc
    f (φ y) = f (Θ y) := by rw [hφy]
    _ = g (Θ y) := by rfl
    _ = g x := by rfl
    _ = g 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := hfinal
    _ = f 0 + (1 / 2 : ℝ) * ∑ i : Fin (n + 1), w i * y i * y i := by rfl

theorem morse_lemma_diagonal_zero (f : MorseModel 0 → ℝ) (w : Fin 0 → ℝ) :
    ∃ φ : OpenPartialHomeomorph (MorseModel 0) (MorseModel 0),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ 1 (φ : MorseModel 0 → MorseModel 0) 0 ∧
      ContDiffAt ℝ 1 (φ.symm : MorseModel 0 → MorseModel 0) 0 ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin 0, w i * y i * y i := by
  refine ⟨OpenPartialHomeomorph.refl (MorseModel 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · rfl
  · change ContDiffAt ℝ 1 (id : MorseModel 0 → MorseModel 0) 0
    exact contDiffAt_id
  · change ContDiffAt ℝ 1 (id : MorseModel 0 → MorseModel 0) 0
    exact contDiffAt_id
  · intro y hy
    have hy0 : y = 0 := by
      funext i
      exact (Fin.elim0 i)
    simp [hy0]

theorem morse_lemma_diagonal (n : ℕ) (f : MorseModel n → ℝ) (hf : ContDiff ℝ (n + 3) f)
    (hcrit : fderiv ℝ f 0 = 0) (w : Fin n → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel n, (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin n, w i * u i * v i) :
    ∃ φ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ 1 (φ : MorseModel n → MorseModel n) 0 ∧
      ContDiffAt ℝ 1 (φ.symm : MorseModel n → MorseModel n) 0 ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  induction n with
  | zero =>
      exact morse_lemma_diagonal_zero f w
  | succ n ih =>
      exact morse_lemma_diagonal_succ n ih f hf hcrit w hw hdiag

theorem morse_lemma_diagonal_zero_smooth (f : MorseModel 0 → ℝ)
    (w : Fin 0 → ℝ) :
    ∃ φ : OpenPartialHomeomorph (MorseModel 0) (MorseModel 0),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel 0 → MorseModel 0) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel 0 → MorseModel 0) 0 ∧
      (∃ v : Set (MorseModel 0), IsOpen v ∧ (0 : MorseModel 0) ∈ v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel 0 → MorseModel 0) v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel 0 → MorseModel 0) (φ '' v)) ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin 0, w i * y i * y i := by
  refine ⟨OpenPartialHomeomorph.refl (MorseModel 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · rfl
  · change ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (id : MorseModel 0 → MorseModel 0) 0
    exact contDiffAt_id
  · change ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (id : MorseModel 0 → MorseModel 0) 0
    exact contDiffAt_id
  · refine ⟨Set.univ, isOpen_univ, by simp, ?_, ?_⟩
    · change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (id : MorseModel 0 → MorseModel 0) Set.univ
      exact contDiffOn_id
    · have hfun : (↑(OpenPartialHomeomorph.refl (MorseModel 0)).symm : MorseModel 0 → MorseModel 0) = id := rfl
      have himg : (↑(OpenPartialHomeomorph.refl (MorseModel 0)) '' Set.univ) = Set.univ := by
        ext y
        simp
      rw [hfun, himg]
      exact contDiffOn_id
  · intro y hy
    have hy0 : y = 0 := by
      funext i
      exact (Fin.elim0 i)
    simp [hy0]

theorem morse_lemma_diagonal_smooth (n : ℕ) (f : MorseModel n → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcrit : fderiv ℝ f 0 = 0) (w : Fin n → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel n, (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin n, w i * u i * v i) :
    ∃ φ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ φ.source ∧ 0 ∈ φ.target ∧ φ 0 = 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel n → MorseModel n) 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel n → MorseModel n) 0 ∧
      (∃ v : Set (MorseModel n), IsOpen v ∧ (0 : MorseModel n) ∈ v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : MorseModel n → MorseModel n) v ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm : MorseModel n → MorseModel n) (φ '' v)) ∧
      ∀ y ∈ φ.target, f (φ y) = f 0 + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  induction n with
  | zero =>
      exact morse_lemma_diagonal_zero_smooth f w
  | succ n ih =>
      exact morse_lemma_diagonal_succ_smooth n ih f hf hcrit w hw hdiag

end Completion

end DifferentialGeometry.Topology.Morse
