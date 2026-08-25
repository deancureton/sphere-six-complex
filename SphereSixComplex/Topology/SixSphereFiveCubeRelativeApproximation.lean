module

public import SphereSixComplex.Topology.SixSphereFiveCubePuncturedContraction
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Relative smooth approximation of five-cube loops in the six-sphere

Every generalized five-cube loop in `S⁶`, viewed in ambient `ℝ⁷`, admits a global `C¹`
approximation which remains exactly equal to the loop basepoint on the cube boundary.

The proof first clamps all of `ℝ⁵` onto the cube.  A collar cutoff replaces the resulting
continuous extension by the basepoint on a neighborhood of the boundary while changing it by less
than `1 / 4` on the cube.  Compactly supported convolution at a sufficiently small scale then
produces a smooth map.  Because convolution only samples inside that constant collar, the smooth
map is still exactly equal to the basepoint at every boundary point.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

private abbrev Ambient := EuclideanSpace ℝ (Fin 7)
private abbrev Parameter := Fin 5 → ℝ

/-- The standard coordinate inclusion from the unit five-cube into `ℝ⁵`. -/
public def fiveCubeRealCoordinates (t : I^(Fin 5)) : Fin 5 → ℝ :=
  fun i ↦ (t i : ℝ)

private abbrev cubeParameter := fiveCubeRealCoordinates

private theorem isometry_cubeParameter : Isometry cubeParameter := by
  intro x y
  rfl

private def clampCube (z : Parameter) : I^(Fin 5) :=
  fun i ↦ Set.projIcc 0 1 zero_le_one (z i)

@[simp] private theorem clampCube_cubeParameter (t : I^(Fin 5)) :
    clampCube (cubeParameter t) = t := by
  funext i
  exact Set.projIcc_val zero_le_one (t i)

@[fun_prop] private theorem continuous_clampCube : Continuous clampCube := by
  change Continuous (fun z : Parameter ↦ fun i ↦ Set.projIcc 0 1 zero_le_one (z i))
  fun_prop

private def embeddedBoundary : Set Parameter :=
  cubeParameter '' Cube.boundary (Fin 5)

private theorem embeddedBoundary_nonempty : embeddedBoundary.Nonempty := by
  let t : I^(Fin 5) := fun _ ↦ 0
  refine ⟨cubeParameter t, t, ?_, rfl⟩
  exact ⟨0, Or.inl rfl⟩

private def collarWeight (a : ℝ) (z : Parameter) : ℝ :=
  Real.smoothTransition ((Metric.infDist z embeddedBoundary - a) / a)

@[fun_prop] private theorem continuous_collarWeight (a : ℝ) : Continuous (collarWeight a) := by
  unfold collarWeight
  fun_prop

private theorem collarWeight_nonneg (a : ℝ) (z : Parameter) : 0 ≤ collarWeight a z :=
  Real.smoothTransition.nonneg _

private theorem collarWeight_le_one (a : ℝ) (z : Parameter) : collarWeight a z ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem collarWeight_eq_zero_of_infDist_lt {a : ℝ} (ha : 0 < a) {z : Parameter}
    (hz : Metric.infDist z embeddedBoundary < a) : collarWeight a z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz.le) ha.le

private theorem collarWeight_eq_one_of_two_mul_le_infDist {a : ℝ} (ha : 0 < a)
    {z : Parameter} (hz : 2 * a ≤ Metric.infDist z embeddedBoundary) :
    collarWeight a z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ ha]
  linarith

private def collarExtension {x : SixSphere} (p : Ω^ (Fin 5) SixSphere x) (a : ℝ) :
    Parameter → Ambient := fun z ↦
  AffineMap.lineMap (x : Ambient) (p (clampCube z) : Ambient) (collarWeight a z)

private theorem continuous_collarExtension {x : SixSphere}
    (p : Ω^ (Fin 5) SixSphere x) (a : ℝ) : Continuous (collarExtension p a) := by
  unfold collarExtension
  fun_prop

private theorem collarExtension_eq_basepoint_near_boundary {x : SixSphere}
    (p : Ω^ (Fin 5) SixSphere x) {a : ℝ} (ha : 0 < a) {z : Parameter}
    {t : I^(Fin 5)} (ht : t ∈ Cube.boundary (Fin 5))
    (hz : dist z (cubeParameter t) < a) : collarExtension p a z = (x : Ambient) := by
  have htB : cubeParameter t ∈ embeddedBoundary := ⟨t, ht, rfl⟩
  have hinf : Metric.infDist z embeddedBoundary < a :=
    (Metric.infDist_le_dist_of_mem htB).trans_lt hz
  simp [collarExtension, collarWeight_eq_zero_of_infDist_lt ha hinf]

private theorem collarExtension_close_on_cube {x : SixSphere}
    (p : Ω^ (Fin 5) SixSphere x) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hnear : ∀ t : I^(Fin 5),
      Metric.infDist (cubeParameter t) embeddedBoundary < 2 * a →
        dist (p t : Ambient) (x : Ambient) < ε) :
    ∀ t : I^(Fin 5),
      dist (collarExtension p a (cubeParameter t)) (p t : Ambient) < ε := by
  intro t
  rw [collarExtension, clampCube_cubeParameter, dist_lineMap_right]
  by_cases hfar : 2 * a ≤ Metric.infDist (cubeParameter t) embeddedBoundary
  · rw [collarWeight_eq_one_of_two_mul_le_infDist ha hfar]
    simpa using hε
  · have hdist := hnear t (lt_of_not_ge hfar)
    have hw : ‖1 - collarWeight a (cubeParameter t)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · linarith [collarWeight_nonneg a (cubeParameter t)]
      · linarith [collarWeight_le_one a (cubeParameter t)]
    calc
      ‖1 - collarWeight a (cubeParameter t)‖ *
          dist (x : Ambient) (p t : Ambient) ≤
          1 * dist (x : Ambient) (p t : Ambient) :=
        mul_le_mul_of_nonneg_right hw dist_nonneg
      _ = dist (p t : Ambient) (x : Ambient) := by rw [one_mul, dist_comm]
      _ < ε := hdist

private theorem exists_collarWidth {x : SixSphere} (p : Ω^ (Fin 5) SixSphere x) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : I^(Fin 5),
      Metric.infDist (cubeParameter t) embeddedBoundary < 2 * a →
        dist (p t : Ambient) (x : Ambient) < 1 / 4 := by
  have hp_cont : Continuous (fun t : I^(Fin 5) ↦ (p t : Ambient)) := by
    fun_prop
  have hp_uc : UniformContinuous (fun t : I^(Fin 5) ↦ (p t : Ambient)) :=
    CompactSpace.uniformContinuous_of_continuous hp_cont
  obtain ⟨δ, hδ, hpδ⟩ :=
    Metric.uniformContinuous_iff.mp hp_uc (1 / 4) (by norm_num)
  refine ⟨δ / 4, by positivity, ?_⟩
  intro t ht
  have hinf : Metric.infDist (cubeParameter t) embeddedBoundary < δ := by
    calc
      Metric.infDist (cubeParameter t) embeddedBoundary < 2 * (δ / 4) := ht
      _ < δ := by linarith
  obtain ⟨z, hzB, htz⟩ :=
    (Metric.infDist_lt_iff embeddedBoundary_nonempty).mp hinf
  obtain ⟨u, hu, rfl⟩ := hzB
  have htu : dist t u < δ := by
    rw [← isometry_cubeParameter.dist_eq]
    exact htz
  have hpclose := hpδ htu
  have hpu : (p u : Ambient) = (x : Ambient) :=
    congrArg Subtype.val (p.property u hu)
  rw [hpu] at hpclose
  exact hpclose

/-- A five-cube generalized loop in the six-sphere has a global `C¹` ambient approximation
which is uniformly close on the cube and remains exactly equal to the basepoint on its boundary. -/
public theorem fiveCube_relative_contDiff_approximation {x : SixSphere}
    (p : Ω^ (Fin 5) SixSphere x) :
    ∃ q : (Fin 5 → ℝ) → EuclideanSpace ℝ (Fin 7), ContDiff ℝ 1 q ∧
      (∀ t : I^(Fin 5),
        dist (q (fiveCubeRealCoordinates t)) (p t : EuclideanSpace ℝ (Fin 7)) < 1) ∧
      (∀ t ∈ Cube.boundary (Fin 5),
        q (fiveCubeRealCoordinates t) = (x : EuclideanSpace ℝ (Fin 7))) := by
  obtain ⟨a, ha, hnear⟩ := exists_collarWidth p
  let F : Parameter → Ambient := collarExtension p a
  have hF : Continuous F := continuous_collarExtension p a
  have hFclose : ∀ t : I^(Fin 5), dist (F (cubeParameter t)) (p t : Ambient) < 1 / 4 :=
    collarExtension_close_on_cube p ha (by norm_num) hnear
  let K : Set Parameter := Set.range cubeParameter
  have hK : IsCompact K := by
    exact isCompact_range isometry_cubeParameter.continuous
  have hFuc : UniformContinuousOn F (Metric.cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨δ, hδ, hFδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hFuc (1 / 4) (by norm_num)
  let r : ℝ := min (min a δ) 1 / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hra : r < a := by
    dsimp [r]
    have hmin : min (min a δ) 1 ≤ a := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hrone : r < 1 := by
    dsimp [r]
    have hmin : min (min a δ) 1 ≤ 1 := min_le_right _ _
    linarith
  have hrδ : r < δ := by
    dsimp [r]
    have hmin : min (min a δ) 1 ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hlocal (t : I^(Fin 5)) (y : Parameter) (hy : y ∈ Metric.ball (cubeParameter t) r) :
      dist (F y) (F (cubeParameter t)) < 1 / 4 := by
    have htK : cubeParameter t ∈ K := ⟨t, rfl⟩
    have htThick : cubeParameter t ∈ Metric.cthickening 1 K :=
      Metric.self_subset_cthickening K htK
    have hyDist : dist y (cubeParameter t) < r := by
      simpa [dist_comm] using hy
    have hyThick : y ∈ Metric.cthickening 1 K := by
      exact Metric.mem_cthickening_of_dist_le y (cubeParameter t) 1 K htK
        (hyDist.trans hrone).le
    exact hFδ y hyThick (cubeParameter t) htThick (hyDist.trans hrδ)
  obtain ⟨q, hq, hqdist⟩ :=
    hF.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hr
  refine ⟨q, hq.of_le (by norm_num), ?_, ?_⟩
  · intro t
    have hqF : dist (q (cubeParameter t)) (F (cubeParameter t)) ≤ 1 / 4 := by
      apply hqdist (cubeParameter t) (1 / 4)
      intro y hy
      exact (hlocal t y hy).le
    calc
      dist (q (cubeParameter t)) (p t : Ambient) ≤
          dist (q (cubeParameter t)) (F (cubeParameter t)) +
            dist (F (cubeParameter t)) (p t : Ambient) := dist_triangle _ _ _
      _ < 1 / 4 + 1 / 4 := add_lt_add_of_le_of_lt hqF (hFclose t)
      _ < 1 := by norm_num
  · intro t ht
    have hFcenter : F (cubeParameter t) = (x : Ambient) := by
      apply collarExtension_eq_basepoint_near_boundary p ha ht
      simpa using ha
    have hqF : dist (q (cubeParameter t)) (F (cubeParameter t)) ≤ 0 := by
      apply hqdist (cubeParameter t) 0
      intro y hy
      have hyDist : dist y (cubeParameter t) < a := by
        have : dist y (cubeParameter t) < r := by
          simpa [dist_comm] using hy
        exact this.trans hra
      have hFy : F y = (x : Ambient) :=
        collarExtension_eq_basepoint_near_boundary p ha ht hyDist
      simp [hFy, hFcenter]
    have : q (cubeParameter t) = F (cubeParameter t) :=
      dist_eq_zero.mp (le_antisymm hqF dist_nonneg)
    exact this.trans hFcenter

end SphereSixComplex
