module

public import SphereSixComplex.Prerequisites.Topology.CompactAdjunction
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Tactic.Ring

/-! # Radial coordinates and expansion on ball attachments -/

@[expose] public section

namespace SphereSixComplex.AdjunctionSpace

variable {E T B : Type*} [NormedAddCommGroup E]
  [TopologicalSpace T] [TopologicalSpace B]

/-- The attaching subset of a closed ball product. -/
def ballBoundary : Set (Metric.closedBall (0 : E) 1 × T) :=
  {p | ‖p.1.1‖ = 1}

/-- Radius on a ball attachment, equal to one on the attached space. -/
def radius (g : (ballBoundary (E := E) (T := T)) → B) :
    C(AdjunctionSpace ballBoundary g, ℝ) :=
  desc ballBoundary g
    ⟨fun p ↦ ‖p.1.1‖, continuous_norm.comp (continuous_subtype_val.comp continuous_fst)⟩
    (ContinuousMap.const B 1) (fun a ↦ a.2)

/-- The outer collar, including the attached space when `r < 1`. -/
def radialCollar (g : (ballBoundary (E := E) (T := T)) → B) (r : ℝ) :
    Set (AdjunctionSpace ballBoundary g) := {x | r < radius g x}

end SphereSixComplex.AdjunctionSpace

namespace SphereSixComplex

/-- Polar coordinates restricted to any set of strictly positive radii. -/
noncomputable def normPreimageHomeomorph (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set ℝ) (hS : S ⊆ Set.Ioi 0) :
    {x : E | ‖x‖ ∈ S} ≃ₜ Metric.sphere (0 : E) 1 × S where
  toFun x := (⟨‖x.1‖⁻¹ • x.1, by
    have hx : 0 < ‖x.1‖ := hS x.2
    simp [norm_smul, hx.ne']⟩, ⟨‖x.1‖, x.2⟩)
  invFun y := ⟨y.2.1 • y.1.1, by
    have hy : 0 < y.2.1 := hS y.2.2
    simp [norm_smul, abs_of_pos hy, mem_sphere_zero_iff_norm.mp y.1.2]⟩
  left_inv x := by
    have hx : 0 < ‖x.1‖ := hS x.2
    apply Subtype.ext
    simp [smul_smul, hx.ne']
  right_inv y := by
    have hy : 0 < y.2.1 := hS y.2.2
    apply Prod.ext
    · apply Subtype.ext
      simp [norm_smul, abs_of_pos hy, mem_sphere_zero_iff_norm.mp y.1.2,
        smul_smul, hy.ne']
    · apply Subtype.ext
      simp [norm_smul, abs_of_pos hy, mem_sphere_zero_iff_norm.mp y.1.2]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_norm.comp continuous_subtype_val).inv₀
        (fun x ↦ ne_of_gt (hS x.2))).smul continuous_subtype_val
    · exact (continuous_norm.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _

open scoped unitInterval

/-- A continuous radial expansion of the closed unit ball, with a positive cutoff at zero. -/
noncomputable def ballRadialExpansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    C(I × Metric.closedBall (0 : E) 1, Metric.closedBall (0 : E) 1) where
  toFun p := ⟨((1 - p.1.1) + p.1.1 / max r ‖p.2.1‖) • p.2.1, by
    have hd : 0 < max r ‖p.2.1‖ := hr.trans_le (le_max_left _ _)
    have hn : ‖p.2.1‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.2
    have hfac : 0 ≤ (1 - p.1.1) + p.1.1 / max r ‖p.2.1‖ :=
      add_nonneg (sub_nonneg.mpr p.1.2.2) (div_nonneg p.1.2.1 hd.le)
    have hnd : ‖p.2.1‖ / max r ‖p.2.1‖ ≤ 1 :=
      (div_le_one hd).2 (le_max_right _ _)
    have htn := mul_le_of_le_one_right p.1.2.1 hnd
    have hnn := mul_le_of_le_one_right (sub_nonneg.mpr p.1.2.2) hn
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hfac]
    calc
      ((1 - p.1.1) + p.1.1 / max r ‖p.2.1‖) * ‖p.2.1‖ =
          (1 - p.1.1) * ‖p.2.1‖ + p.1.1 * (‖p.2.1‖ / max r ‖p.2.1‖) := by ring
      _ ≤ (1 - p.1.1) + p.1.1 := add_le_add hnn htn
      _ = 1 := by ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).div
          (continuous_const.max (continuous_norm.comp
            (continuous_subtype_val.comp continuous_snd)))
          (fun _ ↦ ne_of_gt (hr.trans_le (le_max_left _ _))))
    · exact continuous_subtype_val.comp continuous_snd

@[simp] theorem ballRadialExpansion_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (x : Metric.closedBall (0 : E) 1) :
    ballRadialExpansion r hr (0, x) = x := by
  apply Subtype.ext
  simp [ballRadialExpansion]

theorem ballRadialExpansion_of_mem_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (t : I) (x : Metric.closedBall (0 : E) 1) (hx : ‖x.1‖ = 1) :
    ballRadialExpansion r hr (t, x) = x := by
  apply Subtype.ext
  simp [ballRadialExpansion, hx, max_eq_right hr1]

@[simp] theorem norm_ballRadialExpansion_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (x : Metric.closedBall (0 : E) 1)
    (hx : r ≤ ‖x.1‖) : ‖(ballRadialExpansion r hr (1, x)).1‖ = 1 := by
  have hn : 0 < ‖x.1‖ := hr.trans_le hx
  simp [ballRadialExpansion, max_eq_right hx, norm_smul, hn.ne']

theorem norm_le_norm_ballRadialExpansion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (t : I) (x : Metric.closedBall (0 : E) 1) :
    ‖x.1‖ ≤ ‖(ballRadialExpansion r hr (t, x)).1‖ := by
  have hn : ‖x.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
  have hd : 0 < max r ‖x.1‖ := hr.trans_le (le_max_left _ _)
  have ht : t.1 ≤ t.1 / max r ‖x.1‖ :=
    (le_div_iff₀ hd).2 (mul_le_of_le_one_right t.2.1 (max_le hr1 hn))
  have hfac : 1 ≤ (1 - t.1) + t.1 / max r ‖x.1‖ := by
    calc
      1 = (1 - t.1) + t.1 := by ring
      _ ≤ (1 - t.1) + t.1 / max r ‖x.1‖ := add_le_add le_rfl ht
  change ‖x.1‖ ≤ ‖((1 - t.1) + t.1 / max r ‖x.1‖) • x.1‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hfac)]
  exact le_mul_of_one_le_left (norm_nonneg _) hfac

namespace AdjunctionSpace

variable {E T B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T] [TopologicalSpace B]

/-- Expand the ball radially while fixing the attached space pointwise. -/
noncomputable def radialExpansion (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    C(I × AdjunctionSpace ballBoundary g, AdjunctionSpace ballBoundary g) where
  toFun p := Quot.lift
    (Sum.elim (fun k ↦ inl ballBoundary g (ballRadialExpansion r hr (p.1, k.1), k.2))
      (inr ballBoundary g)) (by
        rintro a b ⟨x, rfl, rfl⟩
        change inl ballBoundary g
          (ballRadialExpansion r hr (p.1, x.1.1), x.1.2) = inr ballBoundary g (g x)
        rw [ballRadialExpansion_of_mem_sphere r hr hr1 p.1 x.1.1 x.2]
        exact inl_eq_inr ballBoundary g x) p.2
  continuous_toFun := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    have hK : Continuous (fun p : I × (Metric.closedBall (0 : E) 1 × T) ↦
        inl ballBoundary g (ballRadialExpansion r hr (p.1, p.2.1), p.2.2)) :=
      (continuous_inl ballBoundary g).comp
        (((ballRadialExpansion r hr).continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)
    have hB : Continuous (fun p : I × B ↦ inr ballBoundary g p.2) :=
      (continuous_inr ballBoundary g).comp continuous_snd
    convert (hK.sumElim hB).comp Homeomorph.prodSumDistrib.continuous using 1
    funext p
    rcases p with ⟨t, k | b⟩ <;> rfl

@[simp] theorem radialExpansion_inr (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (t : I) (b : B) :
    radialExpansion g r hr hr1 (t, inr ballBoundary g b) = inr ballBoundary g b := rfl

@[simp] theorem radialExpansion_zero (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (x : AdjunctionSpace ballBoundary g) :
    radialExpansion g r hr hr1 (0, x) = x := by
  induction x using Quot.inductionOn with | _ x =>
    cases x with
    | inl k =>
      exact congrArg (inl ballBoundary g)
        (Prod.ext (ballRadialExpansion_zero r hr k.1) rfl)
    | inr b => rfl

theorem radius_le_radius_radialExpansion
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (t : I)
    (x : AdjunctionSpace ballBoundary g) :
    radius g x ≤ radius g (radialExpansion g r hr hr1 (t, x)) := by
  induction x using Quot.inductionOn with | _ x =>
    cases x with
    | inl k => exact norm_le_norm_ballRadialExpansion r hr hr1 t k.1
    | inr b => exact le_rfl

theorem radialExpansion_mem_radialCollar
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (t : I)
    (x : AdjunctionSpace ballBoundary g) {s : ℝ} (hx : x ∈ radialCollar g s) :
    radialExpansion g r hr hr1 (t, x) ∈ radialCollar g s :=
  hx.trans_le (radius_le_radius_radialExpansion g r hr hr1 t x)

theorem radialExpansion_one_mem_range_inr
    (g : (ballBoundary (E := E) (T := T)) → B)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : AdjunctionSpace ballBoundary g) (hx : x ∈ radialCollar g r) :
    radialExpansion g r hr hr1 (1, x) ∈ Set.range (inr ballBoundary g) := by
  induction x using Quot.inductionOn with | _ x =>
    cases x with
    | inl k =>
      have hk : r < ‖k.1.1‖ := hx
      let a : ballBoundary (E := E) (T := T) :=
        ⟨(ballRadialExpansion r hr (1, k.1), k.2),
          norm_ballRadialExpansion_one r hr k.1 hk.le⟩
      exact ⟨g a, (inl_eq_inr ballBoundary g a).symm⟩
    | inr b => exact ⟨b, rfl⟩

end AdjunctionSpace
end SphereSixComplex
