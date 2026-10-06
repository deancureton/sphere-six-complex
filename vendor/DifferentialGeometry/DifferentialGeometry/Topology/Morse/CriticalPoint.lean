module

public import DifferentialGeometry.Topology.Manifold.OpenSubtype
public import DifferentialGeometry.Topology.Morse.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isCriticalPointAt_transContinuousLinearEquiv_iff (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] E')
    (f : M → ℝ) (x : M) :
    IsCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔
      IsCriticalPointAt I f x := by
  let J : ModelWithCorners ℝ E' H := I.transContinuousLinearEquiv e
  let Φ : M ≃ₘ^1⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e
  have hΦ : MDifferentiableAt I J (Φ : M → M) x :=
    Φ.contMDiffAt.mdifferentiableAt one_ne_zero
  have hΦsymm : MDifferentiableAt J I (Φ.symm : M → M) x :=
    Φ.symm.contMDiffAt.mdifferentiableAt one_ne_zero
  change MDifferentiableAt I J (id : M → M) x at hΦ
  change MDifferentiableAt J I (id : M → M) x at hΦsymm
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · have hfJ : MDifferentiableAt J 𝓘(ℝ, ℝ) f x := by
      simpa only [Function.comp_id] using hf.comp x hΦsymm
    have hforward : mfderiv I 𝓘(ℝ, ℝ) f x =
        (mfderiv J 𝓘(ℝ, ℝ) f x).comp (mfderiv I J (id : M → M) x) := by
      simpa only [Function.comp_id, id_eq] using
        (mfderiv_comp (I := I) (I' := J) (I'' := 𝓘(ℝ, ℝ))
          (x := x) (g := f) (f := (id : M → M)) hfJ hΦ)
    have hbackward : mfderiv J 𝓘(ℝ, ℝ) f x =
        (mfderiv I 𝓘(ℝ, ℝ) f x).comp (mfderiv J I (id : M → M) x) := by
      simpa only [Function.comp_id, id_eq] using
        (mfderiv_comp (I := J) (I' := I) (I'' := 𝓘(ℝ, ℝ))
          (x := x) (g := f) (f := (id : M → M)) hf hΦsymm)
    unfold IsCriticalPointAt
    constructor
    · intro h
      rw [hforward, h]
      simp
    · intro h
      rw [hbackward, h]
      simp
  · have hfJ : ¬MDifferentiableAt J 𝓘(ℝ, ℝ) f x := by
      intro hfJ
      apply hf
      simpa only [Function.comp_id] using hfJ.comp x hΦ
    unfold IsCriticalPointAt
    change mfderiv J 𝓘(ℝ, ℝ) f x = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_zero_of_not_mdifferentiableAt hfJ,
      mfderiv_zero_of_not_mdifferentiableAt hf]
    simp

end

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] {r : ℕ∞ω}

theorem isCriticalPointAt_comp_diffeomorph_iff
    (c : Diffeomorph I J M N r) (hr : r ≠ 0) {f : N → ℝ} {x : M} :
    IsCriticalPointAt I (f ∘ c) x ↔ IsCriticalPointAt J f (c x) := by
  by_cases hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (c x)
  · have hsurj : Function.Surjective (mfderiv I J c x) :=
      (c.mfderivToContinuousLinearEquiv hr x).surjective
    rw [IsCriticalPointAt, IsCriticalPointAt,
      mfderiv_comp x hf (c.mdifferentiable hr x)]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨u, rfl⟩ := hsurj v
      exact congrArg (fun A => A u) h
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
  · have hfc : ¬MDifferentiableAt I 𝓘(ℝ, ℝ) (f ∘ c) x := by
      intro h
      apply hf
      have h' := h.comp_of_eq (c x) (c.symm.mdifferentiable hr (c x))
        (c.symm_apply_apply x)
      simpa only [Function.comp_def, c.apply_symm_apply] using h'
    simp only [IsCriticalPointAt, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hfc]

theorem isCriticalPointAt_subtype_iff
    (U : TopologicalSpace.Opens M) {f : M → ℝ} {x : U} :
    IsCriticalPointAt I (fun y : U => f y) x ↔ IsCriticalPointAt I f (x : M) := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (x : M)
  · change mfderiv I 𝓘(ℝ, ℝ) (f ∘ Subtype.val) x = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f (x : M) = 0
    rw [mfderiv_comp x hf (hasMFDerivAt_subtype_val (I := I) U x).mdifferentiableAt]
    have hval : (mfderiv I 𝓘(ℝ, ℝ) f (x : M)).comp
        (mfderiv I I (Subtype.val : U → M) x) = mfderiv I 𝓘(ℝ, ℝ) f (x : M) := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (mfderiv I 𝓘(ℝ, ℝ) f (x : M))
        (mfderiv_subtype_val_apply (I := I) U x v)
    rw [hval]
    exact Iff.rfl
  · have hsub : ¬MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : U => f y) x := by
      intro h
      apply hf
      exact (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val
        f x).mpr h
    simp only [IsCriticalPointAt, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hsub]
end DifferentialGeometry.Topology.Morse
