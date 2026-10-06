module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Adapted from plby/HopfProblem, Solution.lean, commit
9ac8a456b526527837d7082ff775213ca8bc9809, lines 62156–62228.
Released under Apache-2.0; see provenance/APACHE-2.0.txt at the project root.
Modified here to use a punctured ball, the local derivative estimate, and
explicit endpoint and interpolation equations.
-/

open Filter Set
open scoped Topology Asymptotics

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_norm_affine_derivative_lower_bound {f : E → F}
    (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0) :
    ∃ r > 0, ∀ x : E, ‖x‖ < r → ∀ t ∈ Icc (0 : ℝ) 1,
      (1 / 2 : ℝ) * ‖A x‖ ≤ ‖(1 - t) • f x + t • A x‖ := by
  have hrem : (fun x => f x - A x) =o[𝓝 (0 : E)] (fun x => x) := by
    simpa only [zero_add, hzero, sub_zero, ContinuousLinearEquiv.coe_coe] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf)
  have hrel : (fun x => f x - A x) =o[𝓝 (0 : E)] (fun x => A x) :=
    hrem.trans_isBigO (A.isBigO_comp_rev (fun x : E => x) (𝓝 0))
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp
    (hrel.def (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨r, hr, ?_⟩
  intro x hx t ht
  have hxbound : ‖f x - A x‖ ≤ (1 / 2 : ℝ) * ‖A x‖ :=
    hbound (by simpa only [dist_zero_right] using hx)
  have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hone : 1 - t ≤ 1 := by linarith [ht.1]
  have hscale : ‖(1 - t) • (f x - A x)‖ ≤ (1 / 2 : ℝ) * ‖A x‖ := by
    calc
      ‖(1 - t) • (f x - A x)‖ = (1 - t) * ‖f x - A x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ 1 * ‖f x - A x‖ :=
        mul_le_mul_of_nonneg_right hone (norm_nonneg _)
      _ ≤ (1 / 2 : ℝ) * ‖A x‖ := by simpa only [one_mul] using hxbound
  have hid : A x - ((1 - t) • f x + t • A x) =
      -((1 - t) • (f x - A x)) := by module
  have htriangle := norm_sub_norm_le (A x) ((1 - t) • f x + t • A x)
  rw [hid, norm_neg] at htriangle
  linarith

theorem exists_punctured_ball_derivative_homotopy
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0)
    {s : Set E} (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    ∃ r > 0, Metric.ball (0 : E) r ⊆ s ∧
      ∃ g h : C((Metric.ball (0 : E) r \ {0} : Set E), ({0}ᶜ : Set F)),
        (∀ x, (g x : F) = A (x : E)) ∧
        (∀ x, (h x : F) = f (x : E)) ∧
        ∃ H : g.Homotopy h, ∀ p,
          (H p : F) = A (p.2 : E) + (p.1 : ℝ) • (f (p.2 : E) - A (p.2 : E)) := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_norm_affine_derivative_lower_bound A hzero hf
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  let r := min δ ρ
  have hr : 0 < r := lt_min hδ hρ
  have hrs : Metric.ball (0 : E) r ⊆ s :=
    (Metric.ball_subset_ball (min_le_left δ ρ)).trans hδs
  let U : Set E := Metric.ball (0 : E) r \ {0}
  have hU (x : U) : (x : E) ≠ 0 := by simpa using x.property.2
  have hAx (x : U) : A (x : E) ≠ 0 := by
    intro heq
    exact hU x (A.injective (heq.trans (map_zero A).symm))
  have hblend (t : unitInterval) (x : U) :
      A (x : E) + (t : ℝ) • (f (x : E) - A (x : E)) ≠ 0 := by
    have hxρ : ‖(x : E)‖ < ρ :=
      (mem_ball_zero_iff.mp x.property.1).trans_le (min_le_right δ ρ)
    have ht : 1 - (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [t.property.1, t.property.2]
    have hb := hbound (x : E) hxρ (1 - (t : ℝ)) ht
    have heq : (1 - (1 - (t : ℝ))) • f (x : E) +
        (1 - (t : ℝ)) • A (x : E) =
        A (x : E) + (t : ℝ) • (f (x : E) - A (x : E)) := by module
    rw [heq] at hb
    intro hz
    rw [hz, norm_zero] at hb
    exact (not_le_of_gt (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (norm_pos_iff.mpr (hAx x)))) hb
  have hfc : Continuous (fun x : U => f (x : E)) :=
    hc.comp_continuous continuous_subtype_val (fun x => hrs x.property.1)
  have hfU (x : U) : f (x : E) ∈ ({0}ᶜ : Set F) := by
    simpa using hblend 1 x
  let g : C(U, ({0}ᶜ : Set F)) :=
    ⟨fun x => ⟨A (x : E), hAx x⟩, (A.continuous.comp continuous_subtype_val).subtype_mk hAx⟩
  let h : C(U, ({0}ᶜ : Set F)) :=
    ⟨fun x => ⟨f (x : E), hfU x⟩, hfc.subtype_mk hfU⟩
  let H : g.Homotopy h :=
    { toFun := fun p => ⟨A (p.2 : E) + (p.1 : ℝ) •
          (f (p.2 : E) - A (p.2 : E)), hblend p.1 p.2⟩
      continuous_toFun := by
        have ht : Continuous (fun p : unitInterval × U => (p.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        have hAc : Continuous (fun p : unitInterval × U => A (p.2 : E)) :=
          A.continuous.comp (continuous_subtype_val.comp continuous_snd)
        exact (hAc.add (ht.smul ((hfc.comp continuous_snd).sub hAc))).subtype_mk
          (fun p => hblend p.1 p.2)
      map_zero_left := by intro x; apply Subtype.ext; simp [g]
      map_one_left := by intro x; apply Subtype.ext; simp [h] }
  exact ⟨r, hr, hrs, g, h, (fun _ => rfl), (fun _ => rfl), H, (fun _ => rfl)⟩

end DifferentialGeometry.Analysis
