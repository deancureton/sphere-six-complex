module

public import SphereSixComplex.Topology.SixSphereFiveCubeRelativeApproximation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Vanishing of the fifth homotopy group of the six-sphere

Every generalized five-cube loop in `S⁶` is nullhomotopic.  Start with the boundary-exact
`C¹` ambient approximation constructed in `SixSphereFiveCubeRelativeApproximation`.  Its cone is
the image of a differentiable map from a six-dimensional space to `ℝ⁷`, so it misses a nonzero
vector.  Radial projection gives a nearby spherical loop missing the corresponding point of `S⁶`;
the punctured-sphere contraction then finishes the nullhomotopy relative to the cube boundary.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

private abbrev Ambient := EuclideanSpace ℝ (Fin 7)
private abbrev Parameter := Fin 5 → ℝ

private def radialProjection (y : Ambient) (hy : y ≠ 0) : SixSphere :=
  ((homeomorphUnitSphereProd Ambient) ⟨y, by simpa using hy⟩).1

@[simp] private theorem coe_radialProjection (y : Ambient) (hy : y ≠ 0) :
    (radialProjection y hy : Ambient) = ‖y‖⁻¹ • y := by
  simp [radialProjection]

private theorem continuous_fiveCubeRealCoordinates : Continuous fiveCubeRealCoordinates := by
  change Continuous (fun t : I^(Fin 5) ↦ fun i ↦ (t i : ℝ))
  fun_prop

private theorem continuous_radialProjection {Z : Type*} [TopologicalSpace Z]
    (g : Z → Ambient) (hg : Continuous g) (hne : ∀ z, g z ≠ 0) :
    Continuous (fun z ↦ radialProjection (g z) (hne z)) := by
  exact continuous_fst.comp <| (homeomorphUnitSphereProd Ambient).continuous.comp <|
    Continuous.subtype_mk hg (by intro z; simpa using hne z)

/-- The cone on a `C¹` five-parameter ambient map misses a nonzero vector. -/
private theorem exists_nonzero_not_mem_fiveConeRange
    (q : Parameter → Ambient) (hq : ContDiff ℝ 1 q) :
    ∃ w : Ambient, w ≠ 0 ∧ w ∉ Set.range (fun z : Parameter × ℝ ↦ z.2 • q z.1) := by
  let ray : Parameter × ℝ → Ambient := fun z ↦ z.2 • q z.1
  have hray : ContDiff ℝ 1 ray := by
    change ContDiff ℝ 1
      ((fun z : Parameter × ℝ ↦ z.2) • (fun z : Parameter × ℝ ↦ q z.1))
    exact contDiff_snd.smul (hq.comp contDiff_fst)
  have hdim : Module.finrank ℝ (Parameter × ℝ) < Module.finrank ℝ Ambient := by
    simp [Parameter, Ambient]
  have hray_diff : Differentiable ℝ ray := hray.differentiable (by norm_num)
  obtain ⟨w, hw⟩ :=
    (hray_diff.dense_compl_range_of_finrank_lt_finrank hdim).nonempty
  have hw_range : w ∉ Set.range ray := by simpa using hw
  refine ⟨w, ?_, ?_⟩
  · intro hwzero
    apply hw_range
    refine ⟨(0, 0), ?_⟩
    simp [ray, hwzero]
  · simpa [ray] using hw_range

/-- Every five-cube generalized loop in the six-sphere is nullhomotopic. -/
public theorem fiveCubeGenLoop_homotopic_const {x : SixSphere}
    (p : Ω^ (Fin 5) SixSphere x) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨q, hq, hq_close, hq_boundary⟩ := fiveCube_relative_contDiff_approximation p
  let f : C(I^(Fin 5), Ambient) := ⟨fun t ↦ (p t : Ambient), by fun_prop⟩
  have hf_norm (t : I^(Fin 5)) : ‖f t‖ = 1 := norm_eq_of_mem_sphere (p t)
  have hq_ne (t : I^(Fin 5)) : q (fiveCubeRealCoordinates t) ≠ 0 := by
    intro hzero
    have h := hq_close t
    rw [hzero, dist_zero_left, norm_eq_of_mem_sphere (p t)] at h
    exact lt_irrefl 1 h
  let b : Ω^ (Fin 5) SixSphere x := {
    val := ⟨fun t ↦ radialProjection (q (fiveCubeRealCoordinates t)) (hq_ne t), by
      apply continuous_radialProjection
      exact hq.continuous.comp continuous_fiveCubeRealCoordinates⟩
    property := by
      intro t ht
      apply Subtype.ext
      simp [hq_boundary t ht] }
  let ambientQ : C(I^(Fin 5), Ambient) :=
    ⟨fun t ↦ q (fiveCubeRealCoordinates t),
      hq.continuous.comp continuous_fiveCubeRealCoordinates⟩
  let affine : f.Homotopy ambientQ := ContinuousMap.Homotopy.affine f ambientQ
  have haffine_ne (z : I × I^(Fin 5)) : affine z ≠ 0 := by
    intro hzero
    have hdist : dist (affine z) (f z.2) < 1 := by
      change dist (AffineMap.lineMap (f z.2) (ambientQ z.2) (z.1 : ℝ)) (f z.2) < 1
      rw [dist_lineMap_left]
      calc
        ‖(z.1 : ℝ)‖ * dist (f z.2) (ambientQ z.2) ≤ dist (f z.2) (ambientQ z.2) := by
          apply mul_le_of_le_one_left dist_nonneg
          simpa only [Real.norm_eq_abs, abs_of_nonneg z.1.2.1] using z.1.2.2
        _ = dist (q (fiveCubeRealCoordinates z.2)) (p z.2 : Ambient) := dist_comm _ _
        _ < 1 := hq_close z.2
    rw [hzero, dist_zero_left, hf_norm z.2] at hdist
    exact lt_irrefl 1 hdist
  have happrox : GenLoop.Homotopic p b := by
    refine ⟨{
      toFun := fun z ↦ radialProjection (affine z) (haffine_ne z)
      continuous_toFun := continuous_radialProjection affine affine.continuous haffine_ne
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      simp [affine, f]
    · intro t
      apply Subtype.ext
      simp [affine, b, ambientQ]
    · intro s t ht
      change radialProjection (affine (s, t)) (haffine_ne (s, t)) = p t
      apply Eq.trans ?_ (p.property t ht).symm
      apply Subtype.ext
      have hpt : (p t : Ambient) = (x : Ambient) :=
        congrArg Subtype.val (p.property t ht)
      have hline : affine (s, t) = (x : Ambient) := by
        simp [affine, f, ambientQ, hq_boundary t ht, hpt]
      rw [coe_radialProjection, hline]
      simp [norm_eq_of_mem_sphere x]
  obtain ⟨w, hw_ne, hw_range⟩ := exists_nonzero_not_mem_fiveConeRange q hq
  let pole : SixSphere := radialProjection w hw_ne
  have hb_avoid (t : I^(Fin 5)) : b t ≠ pole := by
    intro heq
    apply hw_range
    refine ⟨(fiveCubeRealCoordinates t, ‖w‖ * ‖q (fiveCubeRealCoordinates t)‖⁻¹), ?_⟩
    have heq' : radialProjection (q (fiveCubeRealCoordinates t)) (hq_ne t) =
        radialProjection w hw_ne := by
      change radialProjection (q (fiveCubeRealCoordinates t)) (hq_ne t) = pole at heq
      exact heq
    have hscaled := congrArg (fun y : Ambient ↦ ‖w‖ • y)
      (congrArg Subtype.val heq')
    simpa [smul_smul, hw_ne, hq_ne] using hscaled
  exact happrox.trans (fiveCubeGenLoop_homotopic_const_of_avoids b hb_avoid)

/-- The fifth homotopy group of the standard six-sphere is trivial. -/
public theorem sixSphere_piFive_subsingleton (x : SixSphere) :
    Subsingleton (HomotopyGroup.Pi 5 SixSphere x) := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p r
  apply Quotient.sound
  exact (fiveCubeGenLoop_homotopic_const p).trans
    (fiveCubeGenLoop_homotopic_const r).symm

end SphereSixComplex
