/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.SphereSimplyConnected
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Null-homotopy of loops on the six-sphere

Every loop on the standard six-sphere is homotopic to a polynomial loop by radial projection of
an endpoint-preserving Bernstein approximation. The cone over that polynomial loop is the image
of a continuously differentiable map from a two-dimensional space into seven-dimensional
Euclidean space, so it misses a nonzero vector. The corresponding point of the sphere is avoided
by the polynomial loop, which can therefore be contracted in a stereographic chart.
-/

@[expose] public section

open Filter Function Metric Set Topology
open scoped Topology unitInterval

noncomputable section

namespace SphereSixComplex

private abbrev Ambient := EuclideanSpace ℝ (Fin 7)

/-- Radial projection of a nonzero ambient vector to the unit sphere. -/
private def radialProjection (y : Ambient) (hy : y ≠ 0) : SixSphere :=
  ((homeomorphUnitSphereProd Ambient) ⟨y, by simpa using hy⟩).1

@[simp]
private theorem coe_radialProjection (y : Ambient) (hy : y ≠ 0) :
    (radialProjection y hy : Ambient) = ‖y‖⁻¹ • y := by
  simp [radialProjection]

/-- A loop avoiding one point of the sphere contracts inside the corresponding punctured sphere. -/
private theorem nullhomotopic_of_avoids (v : SixSphere) {x : SixSphere} (p : Path x x)
    (hp : ∀ t, p t ≠ v) : Path.Homotopic p (.refl x) := by
  obtain ⟨_, hcontract⟩ :=
    isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      (sixSphere_compl_singleton_simplyConnected v)
  obtain ⟨F, -⟩ := hcontract x p (by
    intro t
    simp only [mem_compl_iff, mem_singleton_iff]
    exact hp t)
  exact ⟨F⟩

/-- Every loop on the standard six-sphere is null-homotopic. -/
public theorem sixSphereLoopsNullhomotopic (x : SixSphere) (loop : Path x x) :
    Path.Homotopic loop (.refl x) := by
  let f : C(I, Ambient) := (loop.map continuous_subtype_val).toContinuousMap
  have hf_norm (t : I) : ‖f t‖ = 1 := by
    change ‖(loop t : Ambient)‖ = 1
    exact norm_eq_of_mem_sphere (loop t)

  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (bernsteinApproximation_uniform f) 1 zero_lt_one
  let n := max N 1
  have hnN : N ≤ n := le_max_left _ _
  have hn0 : n ≠ 0 := by
    omega
  let b : C(I, Ambient) := bernsteinApproximation n f
  have hb_close (t : I) : dist (b t) (f t) < 1 := by
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt (hN n hnN)
  have hb_ne (t : I) : b t ≠ 0 := by
    intro hzero
    have h := hb_close t
    rw [hzero, dist_zero_left, hf_norm t] at h
    exact (lt_irrefl 1 h)

  let q : ℝ → Ambient := fun t ↦
    ∑ k : Fin (n + 1),
      ((n.choose (k : ℕ) : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - (k : ℕ))) •
        f (bernstein.z k)
  have hq_restrict (t : I) : q (t : ℝ) = b t := by
    simp only [q, b, bernsteinApproximation.apply, bernstein_apply]
  have hq_contDiff : ContDiff ℝ 1 q := by
    dsimp [q]
    fun_prop

  let p : Path x x :=
    { toFun := fun t ↦ radialProjection (b t) (hb_ne t)
      continuous_toFun := by
        dsimp [radialProjection]
        fun_prop
      source' := by
        apply Subtype.ext
        simp [b, f]
      target' := by
        apply Subtype.ext
        simp [b, f, hn0] }

  let affine : f.Homotopy b := ContinuousMap.Homotopy.affine f b
  have haffine_ne (z : I × I) : affine z ≠ 0 := by
    intro hzero
    have hdist : dist (affine z) (f z.2) < 1 := by
      change dist (AffineMap.lineMap (f z.2) (b z.2) (z.1 : ℝ)) (f z.2) < 1
      rw [dist_lineMap_left]
      calc
        ‖(z.1 : ℝ)‖ * dist (f z.2) (b z.2) ≤ dist (f z.2) (b z.2) := by
          apply mul_le_of_le_one_left dist_nonneg
          simpa only [Real.norm_eq_abs, abs_of_nonneg z.1.2.1] using z.1.2.2
        _ = dist (b z.2) (f z.2) := dist_comm _ _
        _ < 1 := hb_close z.2
    rw [hzero, dist_zero_left, hf_norm z.2] at hdist
    exact (lt_irrefl 1 hdist)

  have happrox : Path.Homotopic loop p := by
    refine ⟨{
      toFun := fun z ↦ radialProjection (affine z) (haffine_ne z)
      continuous_toFun := by
        dsimp [radialProjection]
        fun_prop
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      simp [affine, f]
    · intro t
      apply Subtype.ext
      simp [affine, p]
    · intro s t ht
      rcases ht with rfl | rfl
      · apply Subtype.ext
        simp [affine, b, f]
      · apply Subtype.ext
        simp [affine, b, f, hn0]

  let ray : ℝ × ℝ → Ambient := fun z ↦ z.2 • q z.1
  have hray_contDiff : ContDiff ℝ 1 ray := by
    change ContDiff ℝ 1
      ((fun z : ℝ × ℝ ↦ z.2) • (fun z : ℝ × ℝ ↦ q z.1))
    exact contDiff_snd.smul (hq_contDiff.comp contDiff_fst)
  have hdim : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ Ambient := by
    simp [Ambient]
  obtain ⟨w, hw⟩ :=
    (hray_contDiff.dense_compl_range_of_finrank_lt_finrank hdim).nonempty
  have hw_range : w ∉ Set.range ray := by
    simpa using hw
  have hw_ne : w ≠ 0 := by
    intro hwzero
    apply hw_range
    refine ⟨(0, 0), ?_⟩
    simp [ray, hwzero]
  let pole : SixSphere := radialProjection w hw_ne
  have hp_avoid (t : I) : p t ≠ pole := by
    intro heq
    apply hw_range
    refine ⟨((t : ℝ), ‖w‖ * ‖q (t : ℝ)‖⁻¹), ?_⟩
    have hscaled := congrArg (fun y : Ambient ↦ ‖w‖ • y)
      (congrArg Subtype.val heq)
    simpa [ray, p, pole, hq_restrict, smul_smul, hw_ne, hb_ne] using hscaled

  exact happrox.trans (nullhomotopic_of_avoids pole p hp_avoid)

/-- The standard six-sphere is simply connected. -/
public theorem sixSphere_simplyConnected : SimplyConnectedSpace SixSphere :=
  sixSphere_simplyConnected_of_loops_nullhomotopic sixSphereLoopsNullhomotopic

end SphereSixComplex
