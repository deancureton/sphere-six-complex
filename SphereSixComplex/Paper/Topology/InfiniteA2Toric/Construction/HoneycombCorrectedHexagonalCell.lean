module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombCorrectedQuotient

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics

namespace Construction

public def hexagonGauge (x : Fin 2 → ℝ) : ℝ :=
  max ‖x‖ |x 0 - x 1|

public theorem continuous_hexagonGauge :
    Continuous hexagonGauge :=
  continuous_norm.max ((continuous_apply 0).sub (continuous_apply 1)).abs


public theorem norm_le_hexagonGauge (x : Fin 2 → ℝ) :
    ‖x‖ ≤ hexagonGauge x :=
  le_max_left _ _

public theorem hexagonGauge_le_two_mul_norm (x : Fin 2 → ℝ) :
    hexagonGauge x ≤ 2 * ‖x‖ := by
  apply max_le
  · nlinarith [norm_nonneg x]
  · calc
      |x 0 - x 1| ≤ |x 0| + |x 1| := abs_sub _ _
      _ = ∑ i : Fin 2, ‖x i‖ := by
        simp only [Fin.sum_univ_two, Real.norm_eq_abs]
      _ ≤ Fintype.card (Fin 2) • ‖x‖ := Pi.sum_norm_apply_le_norm x
      _ = 2 * ‖x‖ := by norm_num [nsmul_eq_mul]

public theorem hexagonGauge_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    0 < hexagonGauge x :=
  lt_of_lt_of_le (norm_pos_iff.mpr hx) (norm_le_hexagonGauge x)

public theorem hexagonGauge_smul
    (c : ℝ) (hc : 0 ≤ c) (x : Fin 2 → ℝ) :
    hexagonGauge (c • x) = c * hexagonGauge x := by
  simp only [hexagonGauge, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, Pi.smul_apply, smul_eq_mul]
  rw [show c * x 0 - c * x 1 = c * (x 0 - x 1) by ring,
    abs_mul, abs_of_nonneg hc]
  rw [mul_max_of_nonneg _ _ hc]

public def squareToHexagonRadial (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((2 / 3 : ℝ) * ‖x‖ / hexagonGauge x) • x

public def hexagonToSquareRadial (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((3 / 2 : ℝ) * hexagonGauge y / ‖y‖) • y

public theorem hexagonGauge_squareToHexagonRadial (x : Fin 2 → ℝ) :
    hexagonGauge (squareToHexagonRadial x) =
      (2 / 3 : ℝ) * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [squareToHexagonRadial, hexagonGauge]
  have hgx := hexagonGauge_pos hx
  rw [squareToHexagonRadial,
    hexagonGauge_smul _
      (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg x)) hgx.le)]
  field_simp

public theorem norm_hexagonToSquareRadial (y : Fin 2 → ℝ) :
    ‖hexagonToSquareRadial y‖ =
      (3 / 2 : ℝ) * hexagonGauge y := by
  by_cases hy : y = 0
  · subst y
    simp [hexagonToSquareRadial, hexagonGauge]
  have hgy := hexagonGauge_pos hy
  have ha : 0 < (3 / 2 : ℝ) * hexagonGauge y / ‖y‖ :=
    div_pos (mul_pos (by norm_num) hgy) (norm_pos_iff.mpr hy)
  rw [hexagonToSquareRadial, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  field_simp

public theorem hexagonToSquareRadial_squareToHexagonRadial
    (x : Fin 2 → ℝ) :
    hexagonToSquareRadial (squareToHexagonRadial x) = x := by
  by_cases hx : x = 0
  · subst x
    simp [squareToHexagonRadial, hexagonToSquareRadial]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hscale : 0 < (2 / 3 : ℝ) * ‖x‖ / hexagonGauge x :=
    div_pos (mul_pos (by norm_num) hnx) (hexagonGauge_pos hx)
  have hnorm : ‖squareToHexagonRadial x‖ =
      ((2 / 3 : ℝ) * ‖x‖ / hexagonGauge x) * ‖x‖ := by
    rw [squareToHexagonRadial, norm_smul, Real.norm_eq_abs,
      abs_of_pos hscale]
  rw [hexagonToSquareRadial,
    hexagonGauge_squareToHexagonRadial, hnorm,
    squareToHexagonRadial, smul_smul]
  field_simp
  simp [(hexagonGauge_pos hx).ne']

public theorem squareToHexagonRadial_hexagonToSquareRadial
    (y : Fin 2 → ℝ) :
    squareToHexagonRadial (hexagonToSquareRadial y) = y := by
  by_cases hy : y = 0
  · subst y
    simp [squareToHexagonRadial, hexagonToSquareRadial]
  have hgy := hexagonGauge_pos hy
  have hscale : 0 < (3 / 2 : ℝ) * hexagonGauge y / ‖y‖ :=
    div_pos (mul_pos (by norm_num) hgy) (norm_pos_iff.mpr hy)
  have hgauge :
      hexagonGauge (hexagonToSquareRadial y) =
        ((3 / 2 : ℝ) * hexagonGauge y / ‖y‖) *
          hexagonGauge y := by
    rw [hexagonToSquareRadial,
      hexagonGauge_smul _ hscale.le]
  rw [squareToHexagonRadial,
    norm_hexagonToSquareRadial, hgauge,
    hexagonToSquareRadial, smul_smul]
  field_simp
  simp

private theorem squareToHexagonRadial_norm_le (x : Fin 2 → ℝ) :
    ‖squareToHexagonRadial x‖ ≤ ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [squareToHexagonRadial]
  have hgx := hexagonGauge_pos hx
  rw [squareToHexagonRadial, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg x)) hgx.le)]
  have hratio : ‖x‖ / hexagonGauge x ≤ 1 :=
    (div_le_one hgx).mpr (norm_le_hexagonGauge x)
  have hratio0 : 0 ≤ ‖x‖ / hexagonGauge x :=
    div_nonneg (norm_nonneg x) hgx.le
  have hfactor : (2 / 3 : ℝ) * ‖x‖ / hexagonGauge x ≤ 1 := by
    rw [mul_div_assoc]
    nlinarith
  exact mul_le_of_le_one_left (norm_nonneg x) hfactor

public theorem continuous_squareToHexagonRadial :
    Continuous squareToHexagonRadial := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simp only [squareToHexagonRadial, norm_zero, mul_zero, zero_div,
      zero_smul, dist_zero_right] at hy ⊢
    exact (squareToHexagonRadial_norm_le y).trans_lt hy
  · exact ((continuousAt_const.mul continuous_norm.continuousAt).div
      continuous_hexagonGauge.continuousAt
        (hexagonGauge_pos hx).ne').smul continuousAt_id

private theorem hexagonToSquareRadial_norm_le (y : Fin 2 → ℝ) :
    ‖hexagonToSquareRadial y‖ ≤ 3 * ‖y‖ := by
  rw [norm_hexagonToSquareRadial]
  nlinarith [hexagonGauge_le_two_mul_norm y]

public theorem continuous_hexagonToSquareRadial :
    Continuous hexagonToSquareRadial := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / 3, by positivity, ?_⟩
    intro x hx
    rw [show hexagonToSquareRadial 0 = 0 by
      simp [hexagonToSquareRadial], dist_zero_right]
    rw [dist_zero_right] at hx
    exact (hexagonToSquareRadial_norm_le x).trans_lt (by linarith)
  · exact ((continuousAt_const.mul
      continuous_hexagonGauge.continuousAt).div
        continuous_norm.continuousAt (norm_ne_zero_iff.mpr hy)).smul continuousAt_id


public def correctedOpenHexagon (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | hexagonGauge
    (x - correctedPlaneCenter v) < 2 / 3}

public def correctedClosedHexagon (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | hexagonGauge
    (x - correctedPlaneCenter v) ≤ 2 / 3}


public theorem correctedClosedHexagon_eq_planeCell (v : ToricLattice) :
    correctedClosedHexagon v = correctedPlaneCell v := by
  ext x
  simp only [correctedClosedHexagon, Set.mem_ofPred_eq,
    correctedPlaneCell]
  constructor
  · intro h
    have hn : ‖x - correctedPlaneCenter v‖ ≤ 2 / 3 :=
      (le_max_left _ _).trans h
    have hd : |(x - correctedPlaneCenter v) 0 -
        (x - correctedPlaneCenter v) 1| ≤ 2 / 3 :=
      (le_max_right _ _).trans h
    constructor
    · simpa [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x - correctedPlaneCenter v) 0).trans hn
    constructor
    · simpa [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x - correctedPlaneCenter v) 1).trans hn
    · rw [show (x 0 - x 1) -
          (correctedPlaneCenter v 0 -
            correctedPlaneCenter v 1) =
        (x - correctedPlaneCenter v) 0 -
          (x - correctedPlaneCenter v) 1 by
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
    · rw [show (x - correctedPlaneCenter v) 0 -
          (x - correctedPlaneCenter v) 1 =
        (x 0 - x 1) -
          (correctedPlaneCenter v 0 -
            correctedPlaneCenter v 1) by
            simp only [Pi.sub_apply]
            ring]
      exact hd

public noncomputable def correctedHexagonHomeomorph (v : ToricLattice) :
    (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toFun x := correctedPlaneCenter v +
    squareToHexagonRadial x
  invFun y := hexagonToSquareRadial
    (y - correctedPlaneCenter v)
  left_inv x := by
    change hexagonToSquareRadial
      (correctedPlaneCenter v +
        squareToHexagonRadial x -
          correctedPlaneCenter v) = x
    rw [show correctedPlaneCenter v +
          squareToHexagonRadial x -
          correctedPlaneCenter v =
        squareToHexagonRadial x by abel]
    exact hexagonToSquareRadial_squareToHexagonRadial x
  right_inv y := by
    change correctedPlaneCenter v +
      squareToHexagonRadial
        (hexagonToSquareRadial
          (y - correctedPlaneCenter v)) = y
    rw [squareToHexagonRadial_hexagonToSquareRadial]
    abel
  continuous_toFun :=
    continuous_const.add continuous_squareToHexagonRadial
  continuous_invFun :=
    continuous_hexagonToSquareRadial.comp
      (continuous_id.sub continuous_const)

public theorem correctedHexagonHomeomorph_mem_open_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    correctedHexagonHomeomorph v x ∈
        correctedOpenHexagon v ↔
      x ∈ Metric.ball 0 1 := by
  change hexagonGauge
      (correctedPlaneCenter v +
        squareToHexagonRadial x -
          correctedPlaneCenter v) < 2 / 3 ↔
    dist x 0 < 1
  rw [show correctedPlaneCenter v +
        squareToHexagonRadial x -
        correctedPlaneCenter v =
      squareToHexagonRadial x by abel,
    hexagonGauge_squareToHexagonRadial, dist_zero_right]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

public theorem correctedHexagonHomeomorph_mem_closed_iff
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    correctedHexagonHomeomorph v x ∈
        correctedPlaneCell v ↔
      x ∈ Metric.closedBall 0 1 := by
  rw [← correctedClosedHexagon_eq_planeCell]
  change hexagonGauge
      (correctedPlaneCenter v +
        squareToHexagonRadial x -
          correctedPlaneCenter v) ≤ 2 / 3 ↔
    dist x 0 ≤ 1
  rw [show correctedPlaneCenter v +
        squareToHexagonRadial x -
        correctedPlaneCenter v =
      squareToHexagonRadial x by abel,
    hexagonGauge_squareToHexagonRadial, dist_zero_right]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith




end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
