module

public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency

@[expose] public section

/-!
# Arithmetic reduction for source fundamental-polygon pairings

This file starts the geometry-only proof of `SourceOrientedFundamentalPairingClassification`.
Both points in the doubled Ford polygon have imaginary part at least `√2 / 2`.  Consequently, if
one is carried to the other by a source-group element, the distinguished real value of the
bottom-left entry of its canonical `ℤ[√2]` matrix has square at most two.  The coefficient-cone
invariant then reduces that entry to the five values `0, ±1, ±√2`.

Tau Ceti is used only transitively through `ScalarFundamentalConsistency`; this file adds no Tau
Ceti import or theorem use.
-/

open Complex Matrix Metric Set Topology UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

private theorem re_sq_le_half_of_mem_source_strip {x : ℝ}
    (hl : -Real.sqrt 2 / 2 ≤ x) (hr : x ≤ 1 / 2) :
    x ^ 2 ≤ 1 / 2 := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hx : 0 ≤ x
  · nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    nlinarith

/-- Every point of the doubled source Ford polygon has the sharp order-four-vertex lower bound
on its imaginary part. -/
theorem sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    Real.sqrt 2 / 2 ≤ z.im := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rcases hz with hz | hz
  · have hx2 : z.re ^ 2 ≤ 1 / 2 :=
      re_sq_le_half_of_mem_source_strip hz.1 hz.2.1
    have hn : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using hz.2.2
    nlinarith [z.im_pos]
  · have htLower : -Real.sqrt 2 / 2 ≤ 1 - z.re := by
      linarith [hz.2.1]
    have htUpper : 1 - z.re ≤ 1 / 2 := by
      linarith [hz.1]
    have ht2 : (1 - z.re) ^ 2 ≤ 1 / 2 :=
      re_sq_le_half_of_mem_source_strip htLower htUpper
    have hn : 1 ≤ (1 - z.re) ^ 2 + z.im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using hz.2.2
    nlinarith [z.im_pos]

/-- The product of the heights of any two points in the doubled polygon is at least one half. -/
theorem half_le_im_mul_im_of_mem_orientedFundamentalRegion
    {z w : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion) :
    1 / 2 ≤ z.im * w.im := by
  have hz' := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hw' := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hw
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- If a source element carries one doubled-polygon point to another, the distinguished
bottom-left coefficient of its canonical integral lift has square at most two. -/
theorem deltaBottomRow_positiveEmbedding_fst_sq_le_two_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    positiveEmbedding (deltaBottomRow g).1 ^ 2 ≤ 2 := by
  let c : ℝ := positiveEmbedding (deltaBottomRow g).1
  let d : ℝ := positiveEmbedding (deltaBottomRow g).2
  let N : ℝ := Complex.normSq (c * (z : ℂ) + d)
  have hNformula : N = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    simp [N, c, d, Complex.normSq_apply, pow_two]
  have hcpart : c ^ 2 * z.im ^ 2 ≤ N := by
    rw [hNformula]
    nlinarith [sq_nonneg (c * z.re + d)]
  have hNpos : 0 < N := by
    dsimp only [N, c, d]
    exact bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  have him := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  change (fuchsianSourceAction g • z).im = z.im / N at him
  rw [hgw] at him
  have hNeq : N * w.im = z.im := by
    have h := (eq_div_iff hNpos.ne').mp him
    nlinarith
  have hyprod := half_le_im_mul_im_of_mem_orientedFundamentalRegion hz hw
  have hzpos : 0 < z.im := z.im_pos
  have hwpos : 0 < w.im := w.im_pos
  have hmul : c ^ 2 * z.im ^ 2 * w.im ≤ N * w.im :=
    mul_le_mul_of_nonneg_right hcpart hwpos.le
  rw [hNeq] at hmul
  have hcprod : c ^ 2 * (z.im * w.im) ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left hzpos).mp
    nlinarith
  dsimp only [c] at hcprod ⊢
  nlinarith [sq_nonneg (positiveEmbedding (deltaBottomRow g).1)]

/-- A quadratic integer in the coefficient cone whose distinguished real embedding has square at
most two is one of `0, ±1, ±√2`. -/
theorem eq_zero_or_one_or_neg_one_or_sqrtd_or_neg_sqrtd_of_inCoefficientCone_sq_le_two
    (a : QuadraticInteger) (haCone : InCoefficientCone a)
    (haSq : positiveEmbedding a ^ 2 ≤ 2) :
    a = 0 ∨ a = 1 ∨ a = -1 ∨ a = Zsqrtd.sqrtd ∨ a = -Zsqrtd.sqrtd := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  change 0 ≤ a.re * a.im at haCone
  have haConeReal : 0 ≤ (a.re : ℝ) * (a.im : ℝ) := by exact_mod_cast haCone
  have hsum : (a.re : ℝ) ^ 2 + 2 * (a.im : ℝ) ^ 2 ≤ 2 := by
    rw [positiveEmbedding_apply] at haSq
    nlinarith [mul_nonneg haConeReal hs]
  have hsumZ : a.re ^ 2 + 2 * a.im ^ 2 ≤ (2 : ℤ) := by exact_mod_cast hsum
  have hreLowerZ : (-1 : ℤ) ≤ a.re := by
    nlinarith [sq_nonneg (a.re + 1), sq_nonneg a.im]
  have hreUpperZ : a.re ≤ (1 : ℤ) := by
    nlinarith [sq_nonneg (a.re - 1), sq_nonneg a.im]
  have himLowerZ : (-1 : ℤ) ≤ a.im := by
    nlinarith [sq_nonneg (a.im + 1), sq_nonneg a.re]
  have himUpperZ : a.im ≤ (1 : ℤ) := by
    nlinarith [sq_nonneg (a.im - 1), sq_nonneg a.re]
  have hnotBoth : ¬ (a.re ≠ 0 ∧ a.im ≠ 0) := by
    rintro ⟨hre, him⟩
    have hreAbs : (1 : ℝ) ≤ |(a.re : ℝ)| := by
      exact_mod_cast Int.one_le_abs hre
    have himAbs : (1 : ℝ) ≤ |(a.im : ℝ)| := by
      exact_mod_cast Int.one_le_abs him
    have hreSq : 1 ≤ (a.re : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (a.re : ℝ)]
    have himSq : 1 ≤ (a.im : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (a.im : ℝ)]
    nlinarith
  have hzeroCoord : a.re = 0 ∨ a.im = 0 := by tauto
  rcases hzeroCoord with hre | him
  · have himCases : a.im = -1 ∨ a.im = 0 ∨ a.im = 1 := by omega
    rcases himCases with him | him | him
    · right; right; right; right
      apply Zsqrtd.ext <;> simp [hre, him]
    · left
      apply Zsqrtd.ext <;> simp [hre, him]
    · right; right; right; left
      apply Zsqrtd.ext <;> simp [hre, him]
  · have hreCases : a.re = -1 ∨ a.re = 0 ∨ a.re = 1 := by omega
    rcases hreCases with hre | hre | hre
    · right; right; left
      apply Zsqrtd.ext <;> simp [hre, him]
    · left
      apply Zsqrtd.ext <;> simp [hre, him]
    · right; left
      apply Zsqrtd.ext <;> simp [hre, him]

/-- Five-case reduction for the bottom-left entry of every source transformation relating two
points of the doubled fundamental polygon. -/
theorem deltaBottomRow_fst_cases_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    (deltaBottomRow g).1 = 0 ∨ (deltaBottomRow g).1 = 1 ∨
      (deltaBottomRow g).1 = -1 ∨
      (deltaBottomRow g).1 = Zsqrtd.sqrtd ∨
      (deltaBottomRow g).1 = -Zsqrtd.sqrtd := by
  apply eq_zero_or_one_or_neg_one_or_sqrtd_or_neg_sqrtd_of_inCoefficientCone_sq_le_two
  · exact wordMatrix_matrixInCoefficientCone (deltaNormalForm g) 1 0
  · exact deltaBottomRow_positiveEmbedding_fst_sq_le_two_of_maps_oriented g hz hw hgw

private theorem factorMatrix_det_one (b : Bool) (a : DeltaFactor b) :
    (factorMatrix b a).det = 1 := by
  cases b <;>
    simp [factorMatrix, Matrix.det_pow, quadraticOne_det, quadraticTwo_det]

/-- Every canonical reduced-word matrix has determinant one already over `ℤ[√2]`. -/
theorem wordMatrix_det_one (w : Monoid.CoprodI.Word DeltaFactor) :
    (wordMatrix w).det = 1 := by
  rw [wordMatrix]
  induction w.toList with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih]
      simpa using factorMatrix_det_one x.1 x.2

private theorem mul_eq_one_of_inCoefficientCone_cases
    {a d : QuadraticInteger} (ha : InCoefficientCone a)
    (hd : InCoefficientCone d) (had : a * d = 1) :
    (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by
  change 0 ≤ a.re * a.im at ha
  change 0 ≤ d.re * d.im at hd
  have hre : a.re * d.re + 2 * a.im * d.im = 1 := by
    have h := congrArg Zsqrtd.re had
    simpa using h
  have him : a.re * d.im + a.im * d.re = 0 := by
    have h := congrArg Zsqrtd.im had
    simpa using h
  rcases mul_nonneg_iff.mp ha with ha | ha <;>
    rcases mul_nonneg_iff.mp hd with hd | hd
  · have hadRe : a.re * d.re = 1 := by
      have h1 : 0 ≤ a.re * d.re := mul_nonneg ha.1 hd.1
      have h2 : 0 ≤ a.im * d.im := mul_nonneg ha.2 hd.2
      let X := a.re * d.re
      let Y := a.im * d.im
      have hre' : X + 2 * Y = 1 := by simpa [X, Y, mul_assoc] using hre
      have hY : Y = 0 := by omega
      omega
    have hare : a.re = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hadRe with h | h
      · exact h.1
      · omega
    have hdre : d.re = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hadRe with h | h
      · exact h.2
      · omega
    rw [hare, hdre] at him
    norm_num at him
    have haim : a.im = 0 := by omega
    have hdim : d.im = 0 := by omega
    left
    constructor <;> apply Zsqrtd.ext <;> simp_all
  · have h1 : a.re * d.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.1 hd.1
    have h2 : a.im * d.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.2 hd.2
    let X := a.re * d.re
    let Y := a.im * d.im
    have hre' : X + 2 * Y = 1 := by simpa [X, Y, mul_assoc] using hre
    omega
  · have h1 : a.re * d.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.1 hd.1
    have h2 : a.im * d.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.2 hd.2
    let X := a.re * d.re
    let Y := a.im * d.im
    have hre' : X + 2 * Y = 1 := by simpa [X, Y, mul_assoc] using hre
    omega
  · have hadRe : a.re * d.re = 1 := by
      have h1 : 0 ≤ a.re * d.re := mul_nonneg_of_nonpos_of_nonpos ha.1 hd.1
      have h2 : 0 ≤ a.im * d.im := mul_nonneg_of_nonpos_of_nonpos ha.2 hd.2
      let X := a.re * d.re
      let Y := a.im * d.im
      have hre' : X + 2 * Y = 1 := by simpa [X, Y, mul_assoc] using hre
      have hY : Y = 0 := by omega
      omega
    have hare : a.re = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hadRe with h | h
      · omega
      · exact h.1
    have hdre : d.re = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hadRe with h | h
      · omega
      · exact h.2
    rw [hare, hdre] at him
    norm_num at him
    have haim : a.im = 0 := by omega
    have hdim : d.im = 0 := by omega
    right
    constructor <;> apply Zsqrtd.ext <;> simp_all

/-- A canonical source matrix with zero bottom-left entry has diagonal `1,1` or `-1,-1`.
The coefficient cone rules out the nontrivial Pell-unit dilations that exist in ambient
`SL₂(ℤ[√2])`. -/
theorem deltaWordMatrix_diagonal_cases_of_bottomLeft_eq_zero
    (g : Delta) (hc : (deltaBottomRow g).1 = 0) :
    ((wordMatrix (deltaNormalForm g)) 0 0 = 1 ∧
      (wordMatrix (deltaNormalForm g)) 1 1 = 1) ∨
    ((wordMatrix (deltaNormalForm g)) 0 0 = -1 ∧
      (wordMatrix (deltaNormalForm g)) 1 1 = -1) := by
  let M := wordMatrix (deltaNormalForm g)
  have hdet := wordMatrix_det_one (deltaNormalForm g)
  have hcM : M 1 0 = 0 := by simpa [M, deltaBottomRow, wordBottomRow] using hc
  have hmul : M 0 0 * M 1 1 = 1 := by
    change M.det = 1 at hdet
    rw [Matrix.det_fin_two, hcM, mul_zero, sub_zero] at hdet
    exact hdet
  have hcone := wordMatrix_matrixInCoefficientCone (deltaNormalForm g)
  simpa [M] using
    (mul_eq_one_of_inCoefficientCone_cases (hcone 0 0) (hcone 1 1) hmul)

/-- Vanishing bottom-left entry forces commutation with the primitive positive cusp translation.
Thus the remaining vertical-pairing classification is purely the centralizer theorem for the
cyclically reduced word `g₁g₂` in `C₃ * C₄`. -/
theorem commute_product_of_deltaBottomRow_fst_eq_zero
    (g : Delta) (hc : (deltaBottomRow g).1 = 0) :
    Commute g (g₁ * g₂) := by
  let A : SL2R := deltaRealSL g
  let M := wordMatrix (deltaNormalForm g)
  have hdiag := deltaWordMatrix_diagonal_cases_of_bottomLeft_eq_zero g hc
  have hAM := positiveMatrix_deltaWordMatrix g
  have hcA : A 1 0 = 0 := by
    have h := congrFun (congrFun hAM (1 : Fin 2)) (0 : Fin 2)
    change positiveEmbedding (M 1 0) = A 1 0 at h
    have hcM : M 1 0 = 0 := by simpa [M, deltaBottomRow, wordBottomRow] using hc
    simpa [hcM] using h.symm
  have hdiagA : (A 0 0 = 1 ∧ A 1 1 = 1) ∨
      (A 0 0 = -1 ∧ A 1 1 = -1) := by
    rcases hdiag with hdiag | hdiag
    · left
      constructor
      · have h := congrFun (congrFun hAM (0 : Fin 2)) (0 : Fin 2)
        change positiveEmbedding (M 0 0) = A 0 0 at h
        simpa [M, hdiag.1] using h.symm
      · have h := congrFun (congrFun hAM (1 : Fin 2)) (1 : Fin 2)
        change positiveEmbedding (M 1 1) = A 1 1 at h
        simpa [M, hdiag.2] using h.symm
    · right
      constructor
      · have h := congrFun (congrFun hAM (0 : Fin 2)) (0 : Fin 2)
        change positiveEmbedding (M 0 0) = A 0 0 at h
        simpa [M, hdiag.1] using h.symm
      · have h := congrFun (congrFun hAM (1 : Fin 2)) (1 : Fin 2)
        change positiveEmbedding (M 1 1) = A 1 1 at h
        simpa [M, hdiag.2] using h.symm
  have hcommA : Commute A fuchsianProductSL := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) ℝ) *
        (!![1, 1 + Real.sqrt 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1, 1 + Real.sqrt 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * A
    rcases hdiagA with hdiagA | hdiagA
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, hcA, hdiagA.1, hdiagA.2]
      all_goals ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, hcA, hdiagA.1, hdiagA.2]
      all_goals ring
  apply FuchsianPingPong.fuchsianSourceAction_injective
  have hprod : fuchsianSourceAction (g₁ * g₂) =
      fuchsianSLAction fuchsianProductSL := by
    rw [map_mul, fuchsianSourceAction_g₁, fuchsianSourceAction_g₂]
    change fuchsianSLAction fuchsianOneSL * fuchsianSLAction fuchsianTwoSL = _
    rw [← map_mul, fuchsianOneSL_mul_fuchsianTwoSL]
  rw [map_mul fuchsianSourceAction g (g₁ * g₂),
    map_mul fuchsianSourceAction (g₁ * g₂) g,
    fuchsianSourceAction_eq_deltaRealSL, hprod]
  simpa [A, ← map_mul] using congrArg fuchsianSLAction hcommA.eq

/-- The one remaining free-product statement for the cusp side: the centralizer of the primitive
cyclically reduced cusp word is its infinite cyclic subgroup. -/
def SourceCuspCentralizerExact : Prop :=
  ∀ g : Delta, Commute g (g₁ * g₂) → ∃ n : ℤ, g = (g₁ * g₂) ^ n

theorem orientedFundamentalRegion_re_bounds {z : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion) :
    -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 + Real.sqrt 2 / 2 := by
  rcases hz with hz | hz
  · refine ⟨hz.1, hz.2.1.trans ?_⟩
    nlinarith [Real.sqrt_nonneg 2]
  · refine ⟨?_, hz.2.1⟩
    calc
      -Real.sqrt 2 / 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg 2)) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
      _ ≤ z.re := hz.1

private theorem sourceRightUHP_eq_of_re_eq_left_and_im_eq
    (z w : UpperHalfPlane) (hz : z.re = -Real.sqrt 2 / 2)
    (hw : w.re = 1 + Real.sqrt 2 / 2) (him : z.im = w.im) :
    sourceRightUHP z = w := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · change (sourceRight (z : ℂ)).re = (w : ℂ).re
    rw [sourceRight_re]
    change 1 - z.re = w.re
    rw [hz, hw]
    ring
  · simpa [sourceRight] using him

/-- Assuming only the standard centralizer theorem for a cyclically reduced free-product word,
the zero-bottom-left case gives exactly equality or the two outer vertical sides of the doubled
polygon. -/
theorem source_oriented_pairing_of_bottomLeft_eq_zero
    (hcusp : SourceCuspCentralizerExact)
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = 0)
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  obtain ⟨n, rfl⟩ := hcusp g (commute_product_of_deltaBottomRow_fst_eq_zero g hc)
  have hcoe := congrArg (fun q : UpperHalfPlane ↦ (q : ℂ)) hgw
  change (((fuchsianSourceAction ((g₁ * g₂) ^ n)) z : UpperHalfPlane) : ℂ) =
    (w : ℂ) at hcoe
  rw [FuchsianTessellation.product_zpow_apply] at hcoe
  have hre := congrArg Complex.re hcoe
  have him := congrArg Complex.im hcoe
  norm_num at hre him
  have hzre := orientedFundamentalRegion_re_bounds hz
  have hwre := orientedFundamentalRegion_re_bounds hw
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hwidth : 0 < cuspWidth := cuspWidth_pos
  have hnLower : (-1 : ℝ) ≤ n := by
    change (-1 : ℝ) ≤ (n : ℝ)
    unfold cuspWidth at hre hwidth
    nlinarith
  have hnUpper : (n : ℝ) ≤ 1 := by
    unfold cuspWidth at hre hwidth
    nlinarith
  have hnLowerZ : (-1 : ℤ) ≤ n := by exact_mod_cast hnLower
  have hnUpperZ : n ≤ (1 : ℤ) := by exact_mod_cast hnUpper
  have hncases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hncases with hn | hn | hn
  · right
    have hzright : z.re = 1 + Real.sqrt 2 / 2 := by
      rw [hn] at hre
      unfold cuspWidth at hre
      push_cast at hre
      nlinarith
    have hwleft : w.re = -Real.sqrt 2 / 2 := by
      rw [hn] at hre
      unfold cuspWidth at hre
      push_cast at hre
      nlinarith
    let u := w
    have huFund : u ∈ fundamentalTriangle := by
      rcases hw with hw | hw
      · exact hw
      · exfalso
        nlinarith [hw.1, Real.sqrt_nonneg 2]
    have huNot : (u : ℂ) ∉ sourceOpenChamber := by
      intro hu
      exact (ne_of_lt hu.1) (by simpa [u] using hwleft.symm)
    refine ⟨u, huFund, huNot, Or.inr ⟨?_, rfl⟩⟩
    exact (sourceRightUHP_eq_of_re_eq_left_and_im_eq w z hwleft hzright him.symm).symm
  · left
    rw [hn] at hcoe
    norm_num at hcoe
    exact hcoe
  · right
    have hzleft : z.re = -Real.sqrt 2 / 2 := by
      rw [hn] at hre
      unfold cuspWidth at hre
      push_cast at hre
      nlinarith
    have hwright : w.re = 1 + Real.sqrt 2 / 2 := by
      rw [hn] at hre
      unfold cuspWidth at hre
      push_cast at hre
      nlinarith
    let u := z
    have huFund : u ∈ fundamentalTriangle := by
      rcases hz with hz | hz
      · exact hz
      · exfalso
        nlinarith [hz.1, Real.sqrt_nonneg 2]
    have huNot : (u : ℂ) ∉ sourceOpenChamber := by
      intro hu
      exact (ne_of_lt hu.1) (by simpa [u] using hzleft.symm)
    refine ⟨u, huFund, huNot, Or.inl ⟨rfl, ?_⟩⟩
    exact (sourceRightUHP_eq_of_re_eq_left_and_im_eq z w hzleft hwright him).symm


end SphereSixComplex.Periods.SourceChamberTopology
