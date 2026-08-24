module

public import SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSchwarzPick
import all SphereSixComplex.Periods.Uniformization.UpperHalfPlaneSchwarzPick
public import SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau
import all SphereSixComplex.Periods.Uniformization.ExactNormalizedModularJTau
public import SphereSixComplex.Periods.Uniformization.IntegerEllipticAdjacency
import all SphereSixComplex.Periods.Uniformization.IntegerEllipticAdjacency

@[expose] public section

noncomputable section

namespace SphereSixComplex.Periods.ModularEllipticAdjacency

open Complex Set Metric
open scoped MatrixGroups Manifold ComplexConjugate
open SphereSixComplex.TriangleGroup
open UpperHalfPlaneSchwarzPick
open IntegerEllipticAdjacency

abbrev entryA (g : ModularMatrix) : ℤ := g.1 0 0
abbrev entryB (g : ModularMatrix) : ℤ := g.1 0 1
abbrev entryC (g : ModularMatrix) : ℤ := g.1 1 0
abbrev entryD (g : ModularMatrix) : ℤ := g.1 1 1

theorem entries_det (g : ModularMatrix) :
    entryA g * entryD g - entryB g * entryC g = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h
  exact h

def rowNormTop (g : ModularMatrix) : ℤ := entryA g ^ 2 + entryB g ^ 2
def rowNormBottom (g : ModularMatrix) : ℤ := entryC g ^ 2 + entryD g ^ 2
def rowDot (g : ModularMatrix) : ℤ := entryA g * entryC g + entryB g * entryD g

theorem row_norm_product (g : ModularMatrix) :
    rowNormTop g * rowNormBottom g = rowDot g ^ 2 + 1 := by
  have hdet := entries_det g
  dsimp [rowNormTop, rowNormBottom, rowDot, entryA, entryB, entryC, entryD] at *
  nlinarith [sq_nonneg (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 - 1)]

theorem rowNormTop_pos (g : ModularMatrix) : 0 < rowNormTop g := by
  have hdet := entries_det g
  dsimp [rowNormTop, entryA, entryB, entryC, entryD] at *
  by_contra h
  have ha : g.1 0 0 = 0 := by
    have : g.1 0 0 ^ 2 = 0 := by
      nlinarith [sq_nonneg (g.1 0 0), sq_nonneg (g.1 0 1)]
    exact sq_eq_zero_iff.mp this
  have hb : g.1 0 1 = 0 := by
    have : g.1 0 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (g.1 0 0), sq_nonneg (g.1 0 1)]
    exact sq_eq_zero_iff.mp this
  simp [ha, hb] at hdet

theorem rowNormBottom_pos (g : ModularMatrix) : 0 < rowNormBottom g := by
  have hdet := entries_det g
  dsimp [rowNormBottom, entryA, entryB, entryC, entryD] at *
  by_contra h
  have hc : g.1 1 0 = 0 := by
    have : g.1 1 0 ^ 2 = 0 := by
      nlinarith [sq_nonneg (g.1 1 0), sq_nonneg (g.1 1 1)]
    exact sq_eq_zero_iff.mp this
  have hd : g.1 1 1 = 0 := by
    have : g.1 1 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (g.1 1 0), sq_nonneg (g.1 1 1)]
    exact sq_eq_zero_iff.mp this
  simp [hc, hd] at hdet

theorem modular_smul_I_coe (g : ModularMatrix) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      ((((rowDot g : ℝ) / (rowNormBottom g : ℝ) : ℝ)) : ℂ) +
        ((((1 : ℝ) / (rowNormBottom g : ℝ) : ℝ)) : ℂ) * Complex.I := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp only [UpperHalfPlane.num, UpperHalfPlane.denom,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      UpperHalfPlane.coe_I]
    push_cast
    change
      (((((entryA g : ℝ) : ℂ) * I + ((entryB g : ℝ) : ℂ)) /
          (((entryC g : ℝ) : ℂ) * I + ((entryD g : ℝ) : ℂ)))) =
        ((rowDot g : ℝ) : ℂ) / ((rowNormBottom g : ℝ) : ℂ) +
          (1 : ℂ) / ((rowNormBottom g : ℝ) : ℂ) * I
    have hden : (((entryC g : ℝ) : ℂ) * I + ((entryD g : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      norm_num [Complex.mul_re, Complex.mul_im] at hre him
      have hc : entryC g = 0 := by exact_mod_cast him
      have hd : entryD g = 0 := by exact_mod_cast hre
      have hp := rowNormBottom_pos g
      simp [rowNormBottom, hc, hd] at hp
    have hN : (((rowNormBottom g : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (rowNormBottom_pos g))
    rw [div_eq_iff hden]
    field_simp [hN]
    apply Complex.ext
    · norm_num [Complex.mul_re, Complex.mul_im]
      norm_cast
      dsimp [rowDot, rowNormBottom, entryA, entryB, entryC, entryD]
      linear_combination -(g.1 1 0) * entries_det g
    · norm_num [Complex.mul_re, Complex.mul_im]
      norm_cast
      dsimp [rowDot, rowNormBottom, entryA, entryB, entryC, entryD]
      linear_combination (g.1 1 1) * entries_det g
  · simp

/-- The two source elliptic corners have centred pseudo-hyperbolic square below `19/50`. -/
theorem source_elliptic_cayley_normSq_lt :
    normSq (halfPlaneToDiscAt ellipticThreeParameter
      (fuchsianTwoFixedPoint : ℂ)) < (19 : ℝ) / 50 := by
  rw [halfPlaneToDiscAt, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  norm_num [fuchsianTwoFixedPoint, ellipticThreeParameter, UpperHalfPlane.ρ]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < (10 : ℝ) / 7 := by
    nlinarith [Real.sqrt_nonneg 2]
  let x : ℝ := Real.sqrt 2 * Real.sqrt 3
  have hx : x ^ 2 = 6 := by
    dsimp [x]
    rw [mul_pow, hs2, hs3]
    norm_num
  have hsq : (31 * (4 + Real.sqrt 2)) ^ 2 < (69 * x) ^ 2 := by
    nlinarith
  have hmain : 31 * (4 + Real.sqrt 2) < 69 * x :=
    (sq_lt_sq₀ (by positivity) (by dsimp [x]; positivity)).mp hsq
  have hden : 0 <
      (-Real.sqrt 2 / 2 - 1 / 2) * (-Real.sqrt 2 / 2 - 1 / 2) +
        (Real.sqrt 2 / 2 + Real.sqrt 3 / 2) *
          (Real.sqrt 2 / 2 + Real.sqrt 3 / 2) := by
    have hy : 0 < Real.sqrt 2 / 2 + Real.sqrt 3 / 2 := by positivity
    nlinarith [mul_pos hy hy,
      sq_nonneg (-Real.sqrt 2 / 2 - 1 / 2)]
  rw [div_lt_iff₀ hden]
  dsimp [x] at hmain
  nlinarith

/-- Closed formula for the centred pseudo-hyperbolic square of a modular image of `I`. -/
theorem modular_I_cayley_normSq (g : ModularMatrix) :
    normSq (halfPlaneToDiscAt ellipticThreeParameter
      ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ)) =
      (((rowNormTop g + rowNormBottom g - rowDot g : ℤ) : ℝ) - Real.sqrt 3) /
        (((rowNormTop g + rowNormBottom g - rowDot g : ℤ) : ℝ) + Real.sqrt 3) := by
  rw [modular_smul_I_coe, halfPlaneToDiscAt, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, mul_zero, zero_mul, add_zero, zero_add]
  norm_num [ellipticThreeParameter, UpperHalfPlane.ρ]
  let m : ℝ := rowNormTop g
  let n : ℝ := rowNormBottom g
  let r : ℝ := rowDot g
  let N : ℝ := m + n - r
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast rowNormTop_pos g
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast rowNormBottom_pos g
  have hprod : m * n = r ^ 2 + 1 := by
    dsimp [m, n, r]
    exact_mod_cast row_norm_product g
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hN : 0 < N := by
    dsimp [N]
    nlinarith [sq_nonneg (m - n)]
  have hnum :
      (r / n - 1 / 2) * (r / n - 1 / 2) +
          (n⁻¹ - Real.sqrt 3 / 2) * (n⁻¹ - Real.sqrt 3 / 2) =
        (N - Real.sqrt 3) / n := by
    field_simp [hn.ne']
    dsimp [N]
    linear_combination -4 * hprod + n ^ 2 * hs3
  have hden :
      (r / n - 1 / 2) * (r / n - 1 / 2) +
          (n⁻¹ + Real.sqrt 3 / 2) * (n⁻¹ + Real.sqrt 3 / 2) =
        (N + Real.sqrt 3) / n := by
    field_simp [hn.ne']
    dsimp [N]
    linear_combination -4 * hprod + n ^ 2 * hs3
  change
    ((r / n - 1 / 2) * (r / n - 1 / 2) +
          (n⁻¹ - Real.sqrt 3 / 2) * (n⁻¹ - Real.sqrt 3 / 2)) /
        ((r / n - 1 / 2) * (r / n - 1 / 2) +
          (n⁻¹ + Real.sqrt 3 / 2) * (n⁻¹ + Real.sqrt 3 / 2)) =
      (N - Real.sqrt 3) / (N + Real.sqrt 3)
  rw [hnum, hden]
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hNp0 : N + Real.sqrt 3 ≠ 0 :=
    ne_of_gt (add_pos hN (Real.sqrt_pos.2 (by norm_num)))
  field_simp [hn0, hNp0]

/-- A non-adjacent modular image of `I` already lies beyond the Schwarz--Pick threshold. -/
theorem modular_I_cayley_normSq_gt_of_four_le (g : ModularMatrix)
    (hfour : 4 ≤ rowNormTop g + rowNormBottom g - rowDot g) :
    (19 : ℝ) / 50 <
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ)) := by
  rw [modular_I_cayley_normSq]
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3lt : 69 * Real.sqrt 3 < 124 := by
    have hsq : (69 * Real.sqrt 3) ^ 2 < (124 : ℝ) ^ 2 := by nlinarith
    exact (sq_lt_sq₀ (by positivity) (by norm_num)).mp hsq
  have hN : (4 : ℝ) ≤
      ((rowNormTop g + rowNormBottom g - rowDot g : ℤ) : ℝ) := by exact_mod_cast hfour
  have hden : 0 <
      ((rowNormTop g + rowNormBottom g - rowDot g : ℤ) : ℝ) + Real.sqrt 3 := by
    positivity
  rw [lt_div_iff₀ hden]
  nlinarith

/-- Schwarz--Pick leaves exactly the three nearest order-two modular points. -/
theorem modular_I_row_cases_of_cayley_bound (g : ModularMatrix)
    (hbound :
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ≤
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        (fuchsianTwoFixedPoint : ℂ))) :
    (rowNormTop g = 1 ∧ rowNormBottom g = 1 ∧ rowDot g = 0) ∨
      (rowNormTop g = 1 ∧ rowNormBottom g = 2 ∧ rowDot g = 1) ∨
      (rowNormTop g = 2 ∧ rowNormBottom g = 1 ∧ rowDot g = 1) := by
  have htarget :
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ)) <
        (19 : ℝ) / 50 :=
    lt_of_le_of_lt hbound source_elliptic_cayley_normSq_lt
  have hN : rowNormTop g + rowNormBottom g - rowDot g < 4 := by
    by_contra hnot
    have hfour : 4 ≤ rowNormTop g + rowNormBottom g - rowDot g := by omega
    exact (not_lt_of_ge
      (modular_I_cayley_normSq_gt_of_four_le g hfour).le) htarget
  exact integer_elliptic_adjacency_cases (rowNormTop_pos g) (rowNormBottom_pos g)
    (row_norm_product g) hN

/-- Equivalently, one of the three powers of the order-three stabilizer carries the nearby
order-two point back to `I`. -/
theorem modular_I_adjacent_under_orderThree (g : ModularMatrix)
    (hbound :
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        ((Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ≤
      normSq (halfPlaneToDiscAt ellipticThreeParameter
        (fuchsianTwoFixedPoint : ℂ))) :
    let w : UpperHalfPlane := Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I
    w = UpperHalfPlane.I ∨
      rhoTauReal g₁ • w = UpperHalfPlane.I ∨
      rhoTauReal (g₁ ^ 2) • w = UpperHalfPlane.I := by
  dsimp only
  rcases modular_I_row_cases_of_cayley_bound g hbound with hcase | hcase | hcase
  · left
    apply UpperHalfPlane.coe_injective
    rw [modular_smul_I_coe]
    rcases hcase with ⟨_, hn, hr⟩
    simp [hn, hr, UpperHalfPlane.I]
  · right; left
    apply UpperHalfPlane.coe_injective
    rw [rhoTauReal_g₁_smul, modular_smul_I_coe]
    rcases hcase with ⟨hm, hn, hr⟩
    rw [hn, hr]
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply,
      UpperHalfPlane.I]
  · right; right
    rcases hcase with ⟨hm, hn, hr⟩
    have hw : Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I =
        rhoTauReal g₁ • UpperHalfPlane.I := by
      apply UpperHalfPlane.coe_injective
      rw [modular_smul_I_coe, rhoTauReal_g₁_smul, hn, hr]
      apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply,
        UpperHalfPlane.I]
    rw [hw]
    calc
      rhoTauReal (g₁ ^ 2) • (rhoTauReal g₁ • UpperHalfPlane.I) =
          rhoTauReal (g₁ ^ 2 * g₁) • UpperHalfPlane.I := by rw [map_mul, mul_smul]
      _ = rhoTauReal (g₁ ^ 3) • UpperHalfPlane.I := by
        congr 2
      _ = UpperHalfPlane.I := by rw [g₁_pow_three, map_one, one_smul]


end SphereSixComplex.Periods.ModularEllipticAdjacency
