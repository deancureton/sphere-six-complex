module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hasMFDerivAt_subtype_val (U : TopologicalSpace.Opens M) (x : U) :
    HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id Real E) := by
  constructor
  · exact continuous_subtype_val.continuousAt
  · let e : OpenPartialHomeomorph U H :=
      (chartAt H (x : M)).subtypeRestr (s := U) (⟨x⟩ : Nonempty U)
    apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := I) x)
      intro y hy
      have hyTarget : I.symm y ∈ e.target := by
        have hy' :
            (∃ z, I z = y) ∧ I.symm y ∈ e.target := by
          simpa [e, extChartAt, TopologicalSpace.Opens.chartAt_eq] using hy
        exact hy'.2
      have hyRange : y ∈ Set.range I := extChartAt_target_subset_range (I := I) x hy
      have hright := e.right_inv hyTarget
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      change I ((chartAt H (x : M)) ((e.symm (I.symm y) : U) : M)) = y
      change (chartAt H (x : M)) ((e.symm (I.symm y) : U) : M) = I.symm y at hright
      rw [hright]
      exact I.right_inv hyRange
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      have hleft := (extChartAt I x).left_inv (mem_extChartAt_source x)
      rw [hleft]
      rfl

theorem mfderiv_subtype_val
    (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id Real E :=
  (hasMFDerivAt_subtype_val (I := I) U x).mfderiv

theorem mfderiv_subtype_val_apply
    (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x v = v := by
  rw [mfderiv_subtype_val (I := I) U x]
  rfl

@[simp] theorem mfderiv_opens_incl {U V : TopologicalSpace.Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x =
      ContinuousLinearMap.id Real E := by
  have hinc : MDifferentiableAt I I (TopologicalSpace.Opens.inclusion hVU : V → U) x :=
    ((contMDiff_inclusion hVU).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : U → M)
      (TopologicalSpace.Opens.inclusion hVU x) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hinc
  change mfderiv I I (Subtype.val : V → M) x =
    (mfderiv I I (Subtype.val : U → M) (TopologicalSpace.Opens.inclusion hVU x)).comp
      (mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x) at hcomp
  rw [mfderiv_subtype_val (I := I) V x,
    mfderiv_subtype_val (I := I) U (TopologicalSpace.Opens.inclusion hVU x)] at hcomp
  simpa using! hcomp.symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem mdifferentiableAt_subtype_iff {U : TopologicalSpace.Opens M} {f : M → N} {x : U} :
    MDifferentiableAt I J (fun y : U => f y) x ↔ MDifferentiableAt I J f (x : M) :=
  (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ _).symm

theorem mfderiv_restrict_open (f : M → N) (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I J (fun y : U => f y) x = mfderiv I J f (x : M) := by
  by_cases hf : MDifferentiableAt I J f (x : M)
  · change mfderiv I J (f ∘ (Subtype.val : U → M)) x = _
    rw [mfderiv_comp x hf (hasMFDerivAt_subtype_val U x).mdifferentiableAt,
      mfderiv_subtype_val]
    rfl
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt (mt mdifferentiableAt_subtype_iff.mp hf)]
    rfl

end DifferentialGeometry

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem MDifferentiableAt.subtypeVal_comp_iff {U : TopologicalSpace.Opens N}
    (f : M → U) (x : M) :
    MDifferentiableAt I J (fun y => (f y : N)) x ↔ MDifferentiableAt I J f x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc, ?_⟩
    exact hd
  · rintro ⟨hc, hd⟩
    exact ⟨continuous_subtype_val.continuousAt.comp hc, hd⟩

theorem DifferentialGeometry.mfderiv_subtypeVal_comp {U : TopologicalSpace.Opens N}
    (f : M → U) (x : M) :
    mfderiv I J (fun y => (f y : N)) x = mfderiv I J f x := by
  classical
  change (if MDifferentiableAt I J (fun y => (f y : N)) x then
      fderivWithin 𝕜 (writtenInExtChartAt I J x (fun y => (f y : N)))
        (Set.range I) ((extChartAt I x) x) else (0 : E →L[𝕜] F)) =
    (if MDifferentiableAt I J f x then
      fderivWithin 𝕜 (writtenInExtChartAt I J x f)
        (Set.range I) ((extChartAt I x) x) else (0 : E →L[𝕜] F))
  by_cases hf : MDifferentiableAt I J f x
  · have hc := (MDifferentiableAt.subtypeVal_comp_iff (I := I) (J := J) f x).mpr hf
    rw [ite_eq_left hc, ite_eq_left hf]
    rfl
  · have hc := mt (MDifferentiableAt.subtypeVal_comp_iff (I := I) (J := J) f x).mp hf
    rw [ite_eq_right hc, ite_eq_right hf]
end
