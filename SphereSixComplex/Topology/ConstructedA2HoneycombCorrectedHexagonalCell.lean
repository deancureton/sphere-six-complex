module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedQuotientProof

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics

public def constructedA2HexagonGauge (x : Fin 2 → ℝ) : ℝ :=
  max ‖x‖ |x 0 - x 1|

public theorem constructedA2HexagonGauge_continuous :
    Continuous constructedA2HexagonGauge :=
  continuous_norm.max ((continuous_apply 0).sub (continuous_apply 1)).abs

public theorem constructedA2HexagonGauge_nonneg (x : Fin 2 → ℝ) :
    0 ≤ constructedA2HexagonGauge x :=
  le_max_of_le_left (norm_nonneg x)

public theorem norm_le_constructedA2HexagonGauge (x : Fin 2 → ℝ) :
    ‖x‖ ≤ constructedA2HexagonGauge x :=
  le_max_left _ _

public theorem constructedA2HexagonGauge_le_two_mul_norm (x : Fin 2 → ℝ) :
    constructedA2HexagonGauge x ≤ 2 * ‖x‖ := by
  apply max_le
  · nlinarith [norm_nonneg x]
  · calc
      |x 0 - x 1| ≤ |x 0| + |x 1| := abs_sub _ _
      _ = ∑ i : Fin 2, ‖x i‖ := by
        simp only [Fin.sum_univ_two, Real.norm_eq_abs]
      _ ≤ Fintype.card (Fin 2) • ‖x‖ := Pi.sum_norm_apply_le_norm x
      _ = 2 * ‖x‖ := by norm_num [nsmul_eq_mul]

public theorem constructedA2HexagonGauge_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    0 < constructedA2HexagonGauge x :=
  lt_of_lt_of_le (norm_pos_iff.mpr hx) (norm_le_constructedA2HexagonGauge x)

public theorem constructedA2HexagonGauge_smul
    (c : ℝ) (hc : 0 ≤ c) (x : Fin 2 → ℝ) :
    constructedA2HexagonGauge (c • x) = c * constructedA2HexagonGauge x := by
  simp only [constructedA2HexagonGauge, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, Pi.smul_apply, smul_eq_mul]
  rw [show c * x 0 - c * x 1 = c * (x 0 - x 1) by ring,
    abs_mul, abs_of_nonneg hc]
  rw [mul_max_of_nonneg _ _ hc]

public def constructedA2SquareToHexagonRadial (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((2 / 3 : ℝ) * ‖x‖ / constructedA2HexagonGauge x) • x

public def constructedA2HexagonToSquareRadial (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((3 / 2 : ℝ) * constructedA2HexagonGauge y / ‖y‖) • y

public theorem constructedA2HexagonGauge_squareToHexagonRadial (x : Fin 2 → ℝ) :
    constructedA2HexagonGauge (constructedA2SquareToHexagonRadial x) =
      (2 / 3 : ℝ) * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [constructedA2SquareToHexagonRadial, constructedA2HexagonGauge]
  have hgx := constructedA2HexagonGauge_pos hx
  rw [constructedA2SquareToHexagonRadial,
    constructedA2HexagonGauge_smul _
      (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg x)) hgx.le)]
  field_simp

public theorem norm_constructedA2HexagonToSquareRadial (y : Fin 2 → ℝ) :
    ‖constructedA2HexagonToSquareRadial y‖ =
      (3 / 2 : ℝ) * constructedA2HexagonGauge y := by
  by_cases hy : y = 0
  · subst y
    simp [constructedA2HexagonToSquareRadial, constructedA2HexagonGauge]
  have hgy := constructedA2HexagonGauge_pos hy
  have ha : 0 < (3 / 2 : ℝ) * constructedA2HexagonGauge y / ‖y‖ :=
    div_pos (mul_pos (by norm_num) hgy) (norm_pos_iff.mpr hy)
  rw [constructedA2HexagonToSquareRadial, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  field_simp

public theorem constructedA2HexagonToSquareRadial_squareToHexagonRadial
    (x : Fin 2 → ℝ) :
    constructedA2HexagonToSquareRadial (constructedA2SquareToHexagonRadial x) = x := by
  by_cases hx : x = 0
  · subst x
    simp [constructedA2SquareToHexagonRadial, constructedA2HexagonToSquareRadial]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hscale : 0 < (2 / 3 : ℝ) * ‖x‖ / constructedA2HexagonGauge x :=
    div_pos (mul_pos (by norm_num) hnx) (constructedA2HexagonGauge_pos hx)
  have hnorm : ‖constructedA2SquareToHexagonRadial x‖ =
      ((2 / 3 : ℝ) * ‖x‖ / constructedA2HexagonGauge x) * ‖x‖ := by
    rw [constructedA2SquareToHexagonRadial, norm_smul, Real.norm_eq_abs,
      abs_of_pos hscale]
  rw [constructedA2HexagonToSquareRadial,
    constructedA2HexagonGauge_squareToHexagonRadial, hnorm,
    constructedA2SquareToHexagonRadial, smul_smul]
  field_simp
  simp [(constructedA2HexagonGauge_pos hx).ne']

public theorem constructedA2SquareToHexagonRadial_hexagonToSquareRadial
    (y : Fin 2 → ℝ) :
    constructedA2SquareToHexagonRadial (constructedA2HexagonToSquareRadial y) = y := by
  by_cases hy : y = 0
  · subst y
    simp [constructedA2SquareToHexagonRadial, constructedA2HexagonToSquareRadial]
  have hgy := constructedA2HexagonGauge_pos hy
  have hscale : 0 < (3 / 2 : ℝ) * constructedA2HexagonGauge y / ‖y‖ :=
    div_pos (mul_pos (by norm_num) hgy) (norm_pos_iff.mpr hy)
  have hgauge :
      constructedA2HexagonGauge (constructedA2HexagonToSquareRadial y) =
        ((3 / 2 : ℝ) * constructedA2HexagonGauge y / ‖y‖) *
          constructedA2HexagonGauge y := by
    rw [constructedA2HexagonToSquareRadial,
      constructedA2HexagonGauge_smul _ hscale.le]
  rw [constructedA2SquareToHexagonRadial,
    norm_constructedA2HexagonToSquareRadial, hgauge,
    constructedA2HexagonToSquareRadial, smul_smul]
  field_simp
  simp

private theorem constructedA2SquareToHexagonRadial_norm_le (x : Fin 2 → ℝ) :
    ‖constructedA2SquareToHexagonRadial x‖ ≤ ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [constructedA2SquareToHexagonRadial]
  have hgx := constructedA2HexagonGauge_pos hx
  rw [constructedA2SquareToHexagonRadial, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg x)) hgx.le)]
  have hratio : ‖x‖ / constructedA2HexagonGauge x ≤ 1 :=
    (div_le_one hgx).mpr (norm_le_constructedA2HexagonGauge x)
  have hratio0 : 0 ≤ ‖x‖ / constructedA2HexagonGauge x :=
    div_nonneg (norm_nonneg x) hgx.le
  have hfactor : (2 / 3 : ℝ) * ‖x‖ / constructedA2HexagonGauge x ≤ 1 := by
    rw [mul_div_assoc]
    nlinarith
  exact mul_le_of_le_one_left (norm_nonneg x) hfactor

public theorem constructedA2SquareToHexagonRadial_continuous :
    Continuous constructedA2SquareToHexagonRadial := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simp only [constructedA2SquareToHexagonRadial, norm_zero, mul_zero, zero_div,
      zero_smul, dist_zero_right] at hy ⊢
    exact (constructedA2SquareToHexagonRadial_norm_le y).trans_lt hy
  · exact ((continuousAt_const.mul continuous_norm.continuousAt).div
      constructedA2HexagonGauge_continuous.continuousAt
        (constructedA2HexagonGauge_pos hx).ne').smul continuousAt_id

private theorem constructedA2HexagonToSquareRadial_norm_le (y : Fin 2 → ℝ) :
    ‖constructedA2HexagonToSquareRadial y‖ ≤ 3 * ‖y‖ := by
  rw [norm_constructedA2HexagonToSquareRadial]
  nlinarith [constructedA2HexagonGauge_le_two_mul_norm y]

public theorem constructedA2HexagonToSquareRadial_continuous :
    Continuous constructedA2HexagonToSquareRadial := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / 3, by positivity, ?_⟩
    intro x hx
    rw [show constructedA2HexagonToSquareRadial 0 = 0 by
      simp [constructedA2HexagonToSquareRadial], dist_zero_right]
    rw [dist_zero_right] at hx
    exact (constructedA2HexagonToSquareRadial_norm_le x).trans_lt (by linarith)
  · exact ((continuousAt_const.mul
      constructedA2HexagonGauge_continuous.continuousAt).div
        continuous_norm.continuousAt (norm_ne_zero_iff.mpr hy)).smul continuousAt_id

public noncomputable def constructedA2SquareHexagonHomeomorph :
    (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toFun := constructedA2SquareToHexagonRadial
  invFun := constructedA2HexagonToSquareRadial
  left_inv := constructedA2HexagonToSquareRadial_squareToHexagonRadial
  right_inv := constructedA2SquareToHexagonRadial_hexagonToSquareRadial
  continuous_toFun := constructedA2SquareToHexagonRadial_continuous
  continuous_invFun := constructedA2HexagonToSquareRadial_continuous

public def constructedA2CorrectedOpenHexagon (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | constructedA2HexagonGauge
    (x - constructedA2CorrectedPlaneCenter v) < 2 / 3}

public def constructedA2CorrectedClosedHexagon (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | constructedA2HexagonGauge
    (x - constructedA2CorrectedPlaneCenter v) ≤ 2 / 3}

public theorem constructedA2CorrectedOpenHexagon_isOpen (v : ToricLattice) :
    IsOpen (constructedA2CorrectedOpenHexagon v) :=
  isOpen_lt
    (constructedA2HexagonGauge_continuous.comp (continuous_id.sub continuous_const))
    continuous_const

public theorem constructedA2CorrectedClosedHexagon_eq_planeCell (v : ToricLattice) :
    constructedA2CorrectedClosedHexagon v = constructedA2CorrectedPlaneCell v := by
  ext x
  simp only [constructedA2CorrectedClosedHexagon, Set.mem_ofPred_eq,
    constructedA2CorrectedPlaneCell]
  constructor
  · intro h
    have hn : ‖x - constructedA2CorrectedPlaneCenter v‖ ≤ 2 / 3 :=
      (le_max_left _ _).trans h
    have hd : |(x - constructedA2CorrectedPlaneCenter v) 0 -
        (x - constructedA2CorrectedPlaneCenter v) 1| ≤ 2 / 3 :=
      (le_max_right _ _).trans h
    constructor
    · simpa [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x - constructedA2CorrectedPlaneCenter v) 0).trans hn
    constructor
    · simpa [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x - constructedA2CorrectedPlaneCenter v) 1).trans hn
    · rw [show (x 0 - x 1) -
          (constructedA2CorrectedPlaneCenter v 0 -
            constructedA2CorrectedPlaneCenter v 1) =
        (x - constructedA2CorrectedPlaneCenter v) 0 -
          (x - constructedA2CorrectedPlaneCenter v) 1 by
            simp only [Pi.sub_apply]
            ring]
      exact hd
  · rintro ⟨h0, h1, hd⟩
    apply max_le
    · rw [pi_norm_le_iff_of_nonempty]
      intro i
      fin_cases i
      · simpa [Pi.sub_apply, Real.norm_eq_abs] using h0
      · simpa [Pi.sub_apply, Real.norm_eq_abs] using h1
    · rw [show (x - constructedA2CorrectedPlaneCenter v) 0 -
          (x - constructedA2CorrectedPlaneCenter v) 1 =
        (x 0 - x 1) -
          (constructedA2CorrectedPlaneCenter v 0 -
            constructedA2CorrectedPlaneCenter v 1) by
            simp only [Pi.sub_apply]
            ring]
      exact hd

public noncomputable def constructedA2CorrectedHexagonHomeomorph (v : ToricLattice) :
    (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toFun x := constructedA2CorrectedPlaneCenter v +
    constructedA2SquareToHexagonRadial x
  invFun y := constructedA2HexagonToSquareRadial
    (y - constructedA2CorrectedPlaneCenter v)
  left_inv x := by
    change constructedA2HexagonToSquareRadial
      (constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
          constructedA2CorrectedPlaneCenter v) = x
    rw [show constructedA2CorrectedPlaneCenter v +
          constructedA2SquareToHexagonRadial x -
          constructedA2CorrectedPlaneCenter v =
        constructedA2SquareToHexagonRadial x by abel]
    exact constructedA2HexagonToSquareRadial_squareToHexagonRadial x
  right_inv y := by
    change constructedA2CorrectedPlaneCenter v +
      constructedA2SquareToHexagonRadial
        (constructedA2HexagonToSquareRadial
          (y - constructedA2CorrectedPlaneCenter v)) = y
    rw [constructedA2SquareToHexagonRadial_hexagonToSquareRadial]
    abel
  continuous_toFun :=
    continuous_const.add constructedA2SquareToHexagonRadial_continuous
  continuous_invFun :=
    constructedA2HexagonToSquareRadial_continuous.comp
      (continuous_id.sub continuous_const)

public theorem constructedA2CorrectedHexagonHomeomorph_mem_open_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedA2CorrectedHexagonHomeomorph v x ∈
        constructedA2CorrectedOpenHexagon v ↔
      x ∈ Metric.ball 0 1 := by
  change constructedA2HexagonGauge
      (constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
          constructedA2CorrectedPlaneCenter v) < 2 / 3 ↔
    dist x 0 < 1
  rw [show constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
        constructedA2CorrectedPlaneCenter v =
      constructedA2SquareToHexagonRadial x by abel,
    constructedA2HexagonGauge_squareToHexagonRadial, dist_zero_right]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

public theorem constructedA2CorrectedHexagonHomeomorph_mem_closed_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedA2CorrectedHexagonHomeomorph v x ∈
        constructedA2CorrectedPlaneCell v ↔
      x ∈ Metric.closedBall 0 1 := by
  rw [← constructedA2CorrectedClosedHexagon_eq_planeCell]
  change constructedA2HexagonGauge
      (constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
          constructedA2CorrectedPlaneCenter v) ≤ 2 / 3 ↔
    dist x 0 ≤ 1
  rw [show constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
        constructedA2CorrectedPlaneCenter v =
      constructedA2SquareToHexagonRadial x by abel,
    constructedA2HexagonGauge_squareToHexagonRadial, dist_zero_right]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

public theorem constructedA2CorrectedHexagonHomeomorph_image_ball
    (v : ToricLattice) :
    constructedA2CorrectedHexagonHomeomorph v '' Metric.ball 0 1 =
      constructedA2CorrectedOpenHexagon v := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (constructedA2CorrectedHexagonHomeomorph_mem_open_iff v x).mpr hx
  · intro hy
    refine ⟨(constructedA2CorrectedHexagonHomeomorph v).symm y, ?_,
      (constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply y⟩
    apply (constructedA2CorrectedHexagonHomeomorph_mem_open_iff v _).mp
    rw [(constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply]
    exact hy

public theorem constructedA2CorrectedHexagonHomeomorph_image_closedBall
    (v : ToricLattice) :
    constructedA2CorrectedHexagonHomeomorph v '' Metric.closedBall 0 1 =
      constructedA2CorrectedPlaneCell v := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx
  · intro hy
    refine ⟨(constructedA2CorrectedHexagonHomeomorph v).symm y, ?_,
      (constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply y⟩
    apply (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v _).mp
    rw [(constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply]
    exact hy

public theorem constructedA2CorrectedHexagonHomeomorph_mapsTo_sphere_boundary
    (v : ToricLattice) :
    MapsTo (constructedA2CorrectedHexagonHomeomorph v) (Metric.sphere 0 1)
      {x | constructedA2HexagonGauge
        (x - constructedA2CorrectedPlaneCenter v) = 2 / 3} := by
  intro x hx
  rw [Metric.mem_sphere, dist_zero_right] at hx
  change constructedA2HexagonGauge
      (constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
          constructedA2CorrectedPlaneCenter v) = 2 / 3
  rw [show constructedA2CorrectedPlaneCenter v +
        constructedA2SquareToHexagonRadial x -
        constructedA2CorrectedPlaneCenter v =
      constructedA2SquareToHexagonRadial x by abel,
    constructedA2HexagonGauge_squareToHexagonRadial, hx]
  norm_num

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
