module

public import SphereSixComplex.Periods.Uniformization.SourceCuspWordCentralizer
import all SphereSixComplex.Periods.Uniformization.SourceCuspWordCentralizer

@[expose] public section

/-!
# Exact pairings in the doubled source fundamental polygon

This file completes the nonzero bottom-row cases left by
`SourceFundamentalPairingGeometry` and removes the cusp-centralizer hypothesis from the zero
case.

Tau Ceti is used only transitively through the imported scalar files; this file adds no Tau Ceti
import or theorem use.
-/

open Complex Matrix Metric Set Topology UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTessellation
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sqrt_two_pos, sqrt_two_sq]

private theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [sqrt_two_pos, sqrt_two_sq]

/-! ## Canonical rows of the two finite side-pairing representatives -/

theorem deltaBottomRow_gTwo_cube :
    deltaBottomRow (g₂ ^ 3) = (1, 0) := by
  decide

theorem deltaBottomRow_gOne_sq :
    deltaBottomRow (g₁ ^ 2) = (1, -1) := by
  decide

/-- Both Ford-circle inequalities hold throughout the doubled oriented region. -/
theorem normSq_ge_one_of_mem_orientedFundamentalRegion {z : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion) :
    1 ≤ normSq (z : ℂ) := by
  rcases hz with hz | hz
  · exact hz.2.2
  · have hdiff : normSq (z : ℂ) - normSq (1 - (z : ℂ)) = 2 * z.re - 1 := by
      simp [normSq_apply]
      ring
    nlinarith [hz.1, hz.2.2]

theorem normSq_one_sub_ge_one_of_mem_orientedFundamentalRegion {z : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion) :
    1 ≤ normSq (1 - (z : ℂ)) := by
  rcases hz with hz | hz
  · have hdiff : normSq (1 - (z : ℂ)) - normSq (z : ℂ) = 1 - 2 * z.re := by
      simp [normSq_apply]
      ring
    nlinarith [hz.2.1, hz.2.2]
  · exact hz.2.2

/-- When the bottom-left coefficient has square one, the real part of its denominator is at most
the sharp order-four height `sqrt 2 / 2`. -/
theorem denominator_re_sq_le_half_of_bottomLeft_sq_eq_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : positiveEmbedding (deltaBottomRow g).1 ^ 2 = 1)
    (hgw : fuchsianSourceAction g • z = w) :
    (positiveEmbedding (deltaBottomRow g).1 * z.re +
      positiveEmbedding (deltaBottomRow g).2) ^ 2 ≤ 1 / 2 := by
  let c : ℝ := positiveEmbedding (deltaBottomRow g).1
  let d : ℝ := positiveEmbedding (deltaBottomRow g).2
  let q : ℝ := c * z.re + d
  let N : ℝ := normSq (c * (z : ℂ) + d)
  have hc' : c ^ 2 = 1 := by simpa [c] using hc
  have hN : N = q ^ 2 + z.im ^ 2 := by
    calc
      N = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
        simp [N, normSq_apply, pow_two]
      _ = q ^ 2 + z.im ^ 2 := by
        dsimp only [q]
        nlinarith [hc']
  have hNpos : 0 < N := by
    dsimp only [N, c, d]
    exact bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  have him := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  change (fuchsianSourceAction g • z).im = z.im / N at him
  rw [hgw] at him
  have hNmul : N * w.im = z.im := by
    have h := (eq_div_iff hNpos.ne').mp him
    nlinarith
  have hwlow := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hw
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hNbound : N * (Real.sqrt 2 / 2) ≤ z.im := by
    nlinarith
  change q ^ 2 ≤ 1 / 2
  nlinarith [sq_nonneg (z.im - Real.sqrt 2 / 2)]

private theorem quadraticInteger_cases_of_cone_of_mem_left_interval
    (d : QuadraticInteger) (hd : InCoefficientCone d)
    (hl : -(1 + Real.sqrt 2) ≤ positiveEmbedding d)
    (hu : positiveEmbedding d ≤ Real.sqrt 2) :
    d = -2 ∨ d = -(1 + Zsqrtd.sqrtd) ∨ d = -1 ∨
      d = -Zsqrtd.sqrtd ∨ d = 0 ∨ d = Zsqrtd.sqrtd ∨ d = 1 := by
  change 0 ≤ d.re * d.im at hd
  rw [positiveEmbedding_apply] at hl hu
  have hspos := sqrt_two_pos
  have hslt := sqrt_two_lt_two
  have hone := one_lt_sqrt_two
  rcases mul_nonneg_iff.mp hd with hd | hd
  · have hre0 : 0 ≤ d.re := hd.1
    have him0 : 0 ≤ d.im := hd.2
    have hrelt : (d.re : ℝ) < 2 := by
      have himCast : 0 ≤ (d.im : ℝ) := by exact_mod_cast him0
      nlinarith
    have himlt : (d.im : ℝ) < 2 := by
      have hreCast : 0 ≤ (d.re : ℝ) := by exact_mod_cast hre0
      nlinarith
    have hreltZ : d.re < 2 := by exact_mod_cast hrelt
    have himltZ : d.im < 2 := by exact_mod_cast himlt
    have hreCases : d.re = 0 ∨ d.re = 1 := by omega
    have himCases : d.im = 0 ∨ d.im = 1 := by omega
    rcases hreCases with hre | hre <;> rcases himCases with him | him
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        apply Zsqrtd.ext <;> simp [hre, him])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        apply Zsqrtd.ext <;> simp [hre, him]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        apply Zsqrtd.ext <;> simp [hre, him]))))))
    · rw [hre, him] at hu
      norm_num at hu
  · have hre0 : d.re ≤ 0 := hd.1
    have him0 : d.im ≤ 0 := hd.2
    have hreLower : (-2 : ℤ) ≤ d.re := by
      have himCast : (d.im : ℝ) ≤ 0 := by exact_mod_cast him0
      have hreReal : (-3 : ℝ) < d.re := by nlinarith
      have hreZ : (-3 : ℤ) < d.re := by exact_mod_cast hreReal
      omega
    have himLower : (-1 : ℤ) ≤ d.im := by
      have hreCast : (d.re : ℝ) ≤ 0 := by exact_mod_cast hre0
      have himReal : (-2 : ℝ) < d.im := by nlinarith
      have himZ : (-2 : ℤ) < d.im := by exact_mod_cast himReal
      omega
    have hreCases : d.re = -2 ∨ d.re = -1 ∨ d.re = 0 := by omega
    have himCases : d.im = -1 ∨ d.im = 0 := by omega
    rcases hreCases with hre | hre | hre <;> rcases himCases with him | him
    · rw [hre, him] at hl
      norm_num at hl
    · exact Or.inl (by apply Zsqrtd.ext <;> simp [hre, him])
    · exact Or.inr (Or.inl (by apply Zsqrtd.ext <;> simp [hre, him]))
    · exact Or.inr (Or.inr (Or.inl (by apply Zsqrtd.ext <;> simp [hre, him])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        apply Zsqrtd.ext <;> simp [hre, him]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        apply Zsqrtd.ext <;> simp [hre, him])))))

private theorem quadraticInteger_cases_of_cone_of_mem_right_interval
    (d : QuadraticInteger) (hd : InCoefficientCone d)
    (hl : -Real.sqrt 2 ≤ positiveEmbedding d)
    (hu : positiveEmbedding d ≤ 1 + Real.sqrt 2) :
    d = -1 ∨ d = -Zsqrtd.sqrtd ∨ d = 0 ∨ d = Zsqrtd.sqrtd ∨
      d = 1 ∨ d = 1 + Zsqrtd.sqrtd ∨ d = 2 := by
  have h := quadraticInteger_cases_of_cone_of_mem_left_interval (-d) (by
    simpa [InCoefficientCone] using hd) (by
      rw [map_neg, neg_le_neg_iff]
      exact hu) (by
      rw [map_neg, neg_le]
      exact hl)
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      simpa using congrArg Neg.neg h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa [add_comm] using congrArg Neg.neg h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa using congrArg Neg.neg h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa using congrArg Neg.neg h))))
  · exact Or.inr (Or.inr (Or.inl (by
      simpa using congrArg Neg.neg h)))
  · exact Or.inr (Or.inl (by
      simpa using congrArg Neg.neg h))
  · exact Or.inl (by
      simpa using congrArg Neg.neg h)

/-- Before the three impossible reduced-word rows are removed, geometry and the coefficient cone
leave seven candidates for the second entry when the first entry is `1`. -/
theorem deltaBottomRow_snd_cases_of_fst_eq_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = 1)
    (hgw : fuchsianSourceAction g • z = w) :
    (deltaBottomRow g).2 = -2 ∨
      (deltaBottomRow g).2 = -(1 + Zsqrtd.sqrtd) ∨
      (deltaBottomRow g).2 = -1 ∨
      (deltaBottomRow g).2 = -Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 0 ∨
      (deltaBottomRow g).2 = Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 1 := by
  let d : ℝ := positiveEmbedding (deltaBottomRow g).2
  have hcSq : positiveEmbedding (deltaBottomRow g).1 ^ 2 = 1 := by
    rw [hc]
    norm_num
  have hqSq := denominator_re_sq_le_half_of_bottomLeft_sq_eq_one g hz hw hcSq hgw
  rw [hc] at hqSq
  norm_num at hqSq
  change (z.re + d) ^ 2 ≤ 1 / 2 at hqSq
  have hre := orientedFundamentalRegion_re_bounds hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hqLower : -(Real.sqrt 2 / 2) ≤ z.re + d := by
    dsimp only [d]
    nlinarith
  have hqUpper : z.re + d ≤ Real.sqrt 2 / 2 := by
    dsimp only [d]
    nlinarith
  have hdLower : -(1 + Real.sqrt 2) ≤ d := by
    nlinarith
  have hdUpper : d ≤ Real.sqrt 2 := by
    nlinarith
  exact quadraticInteger_cases_of_cone_of_mem_left_interval _
    (wordMatrix_matrixInCoefficientCone (deltaNormalForm g) 1 1)
    (by simpa [d] using hdLower) (by simpa [d] using hdUpper)

/-- Symmetric seven-candidate reduction for bottom-left entry `-1`. -/
theorem deltaBottomRow_snd_cases_of_fst_eq_neg_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = -1)
    (hgw : fuchsianSourceAction g • z = w) :
    (deltaBottomRow g).2 = -1 ∨
      (deltaBottomRow g).2 = -Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 0 ∨
      (deltaBottomRow g).2 = Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 1 ∨
      (deltaBottomRow g).2 = 1 + Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 2 := by
  let d : ℝ := positiveEmbedding (deltaBottomRow g).2
  have hcSq : positiveEmbedding (deltaBottomRow g).1 ^ 2 = 1 := by
    rw [hc]
    norm_num
  have hqSq := denominator_re_sq_le_half_of_bottomLeft_sq_eq_one g hz hw hcSq hgw
  rw [hc] at hqSq
  norm_num at hqSq
  change (-z.re + d) ^ 2 ≤ 1 / 2 at hqSq
  have hre := orientedFundamentalRegion_re_bounds hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hqLower : -(Real.sqrt 2 / 2) ≤ -z.re + d := by
    dsimp only [d]
    nlinarith
  have hqUpper : -z.re + d ≤ Real.sqrt 2 / 2 := by
    dsimp only [d]
    nlinarith
  have hdLower : -Real.sqrt 2 ≤ d := by
    nlinarith
  have hdUpper : d ≤ 1 + Real.sqrt 2 := by
    nlinarith
  exact quadraticInteger_cases_of_cone_of_mem_right_interval _
    (wordMatrix_matrixInCoefficientCone (deltaNormalForm g) 1 1)
    (by simpa [d] using hdLower) (by simpa [d] using hdUpper)

/-! ## Three spurious bottom rows -/

private theorem neWordMatrix_eq_of_prod_eq' {i j k l : Bool}
    {u : Monoid.CoprodI.NeWord DeltaFactor i j}
    {v : Monoid.CoprodI.NeWord DeltaFactor k l} (h : u.prod = v.prod) :
    neWordMatrix u = neWordMatrix v := by
  rw [neWordMatrix_eq_wordMatrix, neWordMatrix_eq_wordMatrix]
  apply congrArg wordMatrix
  apply (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm.injective
  change u.toWord.prod = v.toWord.prod
  exact h

private theorem neWordMatrix_eq_factorMatrix_of_singleton_prod' {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j)
    (hprod : w.prod = Monoid.CoprodI.of w.last) :
    neWordMatrix w = factorMatrix j w.last := by
  let v : Monoid.CoprodI.NeWord DeltaFactor j j :=
    .singleton w.last (BinaryIndexedCoprod.NeWord.last_ne_one w)
  have hvprod : w.prod = v.prod := by
    rw [hprod]
    simp [v]
  have hmatrix := neWordMatrix_eq_of_prod_eq' hvprod
  simpa [v, neWordMatrix] using hmatrix

private theorem neWordMatrix_eq_init_mul_factorMatrix' {i j k : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j)
    (p : Monoid.CoprodI.NeWord DeltaFactor i k) (hkj : k ≠ j)
    (hprod : w.prod = p.prod * Monoid.CoprodI.of w.last) :
    neWordMatrix w = neWordMatrix p * factorMatrix j w.last := by
  let v : Monoid.CoprodI.NeWord DeltaFactor i j :=
    .append p hkj (.singleton w.last (BinaryIndexedCoprod.NeWord.last_ne_one w))
  have hvprod : w.prod = v.prod := by
    rw [hprod]
    simp [v]
  have hmatrix := neWordMatrix_eq_of_prod_eq' hvprod
  simpa [v, neWordMatrix] using hmatrix

private theorem neWord_bottomRow_ne_one_one {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = 1 ∧ neWordMatrix w 1 1 = 1) := by
  rintro ⟨hc, hd⟩
  cases j with
  | false =>
      have hrow : OppositeQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [OppositeQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | true =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let nb := (Multiplicative.toAdd w.last).val
        change 1 = (quadraticTwo ^ nb) 1 0 at hc'
        change 1 = (quadraticTwo ^ nb) 1 1 at hd'
        have hnb_lt : nb < 4 := ZMod.val_lt _
        have hnb_ne : nb ≠ 0 := by
          intro hnb
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 4
          change nb = 0
          exact hnb
        have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
        rcases hnb with hnb | hnb | hnb
        all_goals
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
        all_goals first
          | (have hbad := congrArg Zsqrtd.re hc'; norm_num at hbad)
          | (have hbad := congrArg Zsqrtd.re hd'; norm_num at hbad)
      · have hk : k = false := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : OppositeQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let nb := (Multiplicative.toAdd w.last).val
        change 1 = (neWordMatrix p * quadraticTwo ^ nb) 1 0 at hc'
        change 1 = (neWordMatrix p * quadraticTwo ^ nb) 1 1 at hd'
        have hnb_lt : nb < 4 := ZMod.val_lt _
        have hnb_ne : nb ≠ 0 := by
          intro hnb
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 4
          change nb = 0
          exact hnb
        have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
        rcases hnb with hnb | hnb | hnb <;>
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
        all_goals
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
        all_goals
          have hcre := congrArg Zsqrtd.re hc'
          have hcim := congrArg Zsqrtd.im hc'
          have hdre := congrArg Zsqrtd.re hd'
          have hdim := congrArg Zsqrtd.im hd'
          norm_num at hcre hcim hdre hdim
          omega

private theorem deltaBottomRow_ne_one_one (g : Delta) :
    deltaBottomRow g ≠ (1, 1) := by
  intro h
  have hc : (deltaBottomRow g).1 = 1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = 1 := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty, Matrix.one_apply] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_one_one v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

private theorem neWord_bottomRow_ne_neg_one_neg_one {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = -1 ∧ neWordMatrix w 1 1 = -1) := by
  rintro ⟨hc, hd⟩
  cases j with
  | false =>
      have hrow : OppositeQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [OppositeQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | true =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let nb := (Multiplicative.toAdd w.last).val
        change -1 = (quadraticTwo ^ nb) 1 0 at hc'
        change -1 = (quadraticTwo ^ nb) 1 1 at hd'
        have hnb_lt : nb < 4 := ZMod.val_lt _
        have hnb_ne : nb ≠ 0 := by
          intro hnb
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 4
          change nb = 0
          exact hnb
        have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
        rcases hnb with hnb | hnb | hnb
        all_goals
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
      · have hk : k = false := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : OppositeQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let nb := (Multiplicative.toAdd w.last).val
        change -1 = (neWordMatrix p * quadraticTwo ^ nb) 1 0 at hc'
        change -1 = (neWordMatrix p * quadraticTwo ^ nb) 1 1 at hd'
        have hnb_lt : nb < 4 := ZMod.val_lt _
        have hnb_ne : nb ≠ 0 := by
          intro hnb
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 4
          change nb = 0
          exact hnb
        have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
        rcases hnb with hnb | hnb | hnb <;>
          norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
        all_goals
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
        all_goals
          have hcre := congrArg Zsqrtd.re hc'
          have hcim := congrArg Zsqrtd.im hc'
          have hdre := congrArg Zsqrtd.re hd'
          have hdim := congrArg Zsqrtd.im hd'
          norm_num at hcre hcim hdre hdim
          omega

private theorem deltaBottomRow_ne_neg_one_neg_one (g : Delta) :
    deltaBottomRow g ≠ (-1, -1) := by
  intro h
  have hc : (deltaBottomRow g).1 = -1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = -1 := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_neg_one_neg_one v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

private theorem neWord_bottomRow_ne_one_neg_sqrtd {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = 1 ∧
      neWordMatrix w 1 1 = -Zsqrtd.sqrtd) := by
  rintro ⟨hc, hd⟩
  cases j with
  | true =>
      have hrow : SameQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [SameQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | false =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let na := (Multiplicative.toAdd w.last).val
        change 1 = (quadraticOne ^ na) 1 0 at hc'
        change -Zsqrtd.sqrtd = (quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
        all_goals first
          | (have hbad := congrArg Zsqrtd.re hc'; norm_num at hbad)
          | (have hbad := congrArg Zsqrtd.im hd'; norm_num at hbad)
      · have hk : k = true := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : SameQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let na := (Multiplicative.toAdd w.last).val
        change 1 = (neWordMatrix p * quadraticOne ^ na) 1 0 at hc'
        change -Zsqrtd.sqrtd =
          (neWordMatrix p * quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna <;>
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
        all_goals
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
        all_goals
          have hcre := congrArg Zsqrtd.re hc'
          have hcim := congrArg Zsqrtd.im hc'
          have hdre := congrArg Zsqrtd.re hd'
          have hdim := congrArg Zsqrtd.im hd'
          norm_num at hcre hcim hdre hdim
          omega

private theorem deltaBottomRow_ne_one_neg_sqrtd (g : Delta) :
    deltaBottomRow g ≠ (1, -Zsqrtd.sqrtd) := by
  intro h
  have hc : (deltaBottomRow g).1 = 1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = -Zsqrtd.sqrtd := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_one_neg_sqrtd v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

private theorem neWord_bottomRow_ne_neg_one_sqrtd {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = -1 ∧
      neWordMatrix w 1 1 = Zsqrtd.sqrtd) := by
  rintro ⟨hc, hd⟩
  cases j with
  | true =>
      have hrow : SameQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [SameQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | false =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let na := (Multiplicative.toAdd w.last).val
        change -1 = (quadraticOne ^ na) 1 0 at hc'
        change Zsqrtd.sqrtd = (quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
        all_goals first
          | (have hbad := congrArg Zsqrtd.re hc'; norm_num at hbad)
          | (have hbad := congrArg Zsqrtd.im hd'; norm_num at hbad)
      · have hk : k = true := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : SameQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let na := (Multiplicative.toAdd w.last).val
        change -1 = (neWordMatrix p * quadraticOne ^ na) 1 0 at hc'
        change Zsqrtd.sqrtd =
          (neWordMatrix p * quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna <;>
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
        all_goals
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
        all_goals
          have hcre := congrArg Zsqrtd.re hc'
          have hcim := congrArg Zsqrtd.im hc'
          have hdre := congrArg Zsqrtd.re hd'
          have hdim := congrArg Zsqrtd.im hd'
          norm_num at hcre hcim hdre hdim
          omega

private theorem deltaBottomRow_ne_neg_one_sqrtd (g : Delta) :
    deltaBottomRow g ≠ (-1, Zsqrtd.sqrtd) := by
  intro h
  have hc : (deltaBottomRow g).1 = -1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = Zsqrtd.sqrtd := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_neg_one_sqrtd v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

private theorem neWord_bottomRow_ne_one_neg_two {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = 1 ∧ neWordMatrix w 1 1 = -2) := by
  rintro ⟨hc, hd⟩
  cases j with
  | true =>
      have hrow : SameQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [SameQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | false =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let na := (Multiplicative.toAdd w.last).val
        change 1 = (quadraticOne ^ na) 1 0 at hc'
        change -2 = (quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
      · have hk : k = true := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : SameQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let na := (Multiplicative.toAdd w.last).val
        change 1 = (neWordMatrix p * quadraticOne ^ na) 1 0 at hc'
        change -2 = (neWordMatrix p * quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        · norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
          all_goals
            have hcre := congrArg Zsqrtd.re hc'
            have hcim := congrArg Zsqrtd.im hc'
            have hdre := congrArg Zsqrtd.re hd'
            have hdim := congrArg Zsqrtd.im hd'
            norm_num at hcre hcim hdre hdim
            omega
        · norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
          apply neWord_bottomRow_ne_one_one p
          constructor
          · apply Zsqrtd.ext
            · have h₁ := congrArg Zsqrtd.re hc'
              have h₂ := congrArg Zsqrtd.re hd'
              norm_num at h₁ h₂ ⊢
              omega
            · have h₁ := congrArg Zsqrtd.im hc'
              have h₂ := congrArg Zsqrtd.im hd'
              norm_num at h₁ h₂ ⊢
              omega
          · apply Zsqrtd.ext
            · have h := congrArg Zsqrtd.re hc'
              norm_num at h ⊢
              omega
            · have h := congrArg Zsqrtd.im hc'
              norm_num at h ⊢
              omega

private theorem deltaBottomRow_ne_one_neg_two (g : Delta) :
    deltaBottomRow g ≠ (1, -2) := by
  intro h
  have hc : (deltaBottomRow g).1 = 1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = -2 := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_one_neg_two v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

private theorem neWord_bottomRow_ne_neg_one_two {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    ¬ (neWordMatrix w 1 0 = -1 ∧ neWordMatrix w 1 1 = 2) := by
  rintro ⟨hc, hd⟩
  cases j with
  | true =>
      have hrow : SameQuadrantRow (neWordMatrix w 1 0) (neWordMatrix w 1 1) := by
        simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor w 1)
      rw [hc, hd] at hrow
      norm_num [SameQuadrantRow, CoeffNonnegative, CoeffNonpositive] at hrow
  | false =>
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, _⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod' w hsingle.2.1
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        let na := (Multiplicative.toAdd w.last).val
        change -1 = (quadraticOne ^ na) 1 0 at hc'
        change 2 = (quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc'
        all_goals
          norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hd'
      · have hk : k = true := by cases k <;> simp_all
        subst k
        have hmatrix := neWordMatrix_eq_init_mul_factorMatrix' w p hkj hwprod
        have hc' := congrArg (fun M => M 1 0) hmatrix
        have hd' := congrArg (fun M => M 1 1) hmatrix
        rw [hc] at hc'
        rw [hd] at hd'
        have hrow : SameQuadrantRow (neWordMatrix p 1 0) (neWordMatrix p 1 1) := by
          simpa [MatrixRowsForFactor] using (neWordMatrix_rowsForFactor p 1)
        let na := (Multiplicative.toAdd w.last).val
        change -1 = (neWordMatrix p * quadraticOne ^ na) 1 0 at hc'
        change 2 = (neWordMatrix p * quadraticOne ^ na) 1 1 at hd'
        have hna_lt : na < 3 := ZMod.val_lt _
        have hna_ne : na ≠ 0 := by
          intro hna
          apply BinaryIndexedCoprod.NeWord.last_ne_one w
          apply Multiplicative.toAdd.injective
          apply ZMod.val_injective 3
          change na = 0
          exact hna
        have hna : na = 1 ∨ na = 2 := by omega
        rcases hna with hna | hna
        · norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
          rcases hrow with hrow | hrow <;>
            simp only [CoeffNonnegative, CoeffNonpositive] at hrow
          all_goals
            have hcre := congrArg Zsqrtd.re hc'
            have hcim := congrArg Zsqrtd.im hc'
            have hdre := congrArg Zsqrtd.re hd'
            have hdim := congrArg Zsqrtd.im hd'
            norm_num at hcre hcim hdre hdim
            omega
        · norm_num [na, hna, quadraticOne, pow_two, pow_succ,
            Matrix.mul_apply, Fin.sum_univ_succ] at hc' hd'
          apply neWord_bottomRow_ne_neg_one_neg_one p
          constructor
          · apply Zsqrtd.ext
            · have h₁ := congrArg Zsqrtd.re hc'
              have h₂ := congrArg Zsqrtd.re hd'
              norm_num at h₁ h₂ ⊢
              omega
            · have h₁ := congrArg Zsqrtd.im hc'
              have h₂ := congrArg Zsqrtd.im hd'
              norm_num at h₁ h₂ ⊢
              omega
          · apply Zsqrtd.ext
            · have h := congrArg Zsqrtd.re hc'
              norm_num at h ⊢
              omega
            · have h := congrArg Zsqrtd.im hc'
              norm_num at h ⊢
              omega

private theorem deltaBottomRow_ne_neg_one_two (g : Delta) :
    deltaBottomRow g ≠ (-1, 2) := by
  intro h
  have hc : (deltaBottomRow g).1 = -1 := congrArg Prod.fst h
  have hd : (deltaBottomRow g).2 = 2 := congrArg Prod.snd h
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · simp [w, deltaBottomRow, wordBottomRow, wordMatrix, hw,
      Monoid.CoprodI.Word.empty] at hc
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    apply neWord_bottomRow_ne_neg_one_two v
    constructor
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    · rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hd

/-- Exact four denominator rows with bottom-left entry `1` that can carry one doubled-polygon
point to another. -/
theorem deltaBottomRow_snd_four_cases_of_fst_eq_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = 1)
    (hgw : fuchsianSourceAction g • z = w) :
    (deltaBottomRow g).2 = 0 ∨ (deltaBottomRow g).2 = -1 ∨
      (deltaBottomRow g).2 = Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = -(1 + Zsqrtd.sqrtd) := by
  rcases deltaBottomRow_snd_cases_of_fst_eq_one g hz hw hc hgw with
    hd | hd | hd | hd | hd | hd | hd
  · exact (deltaBottomRow_ne_one_neg_two g (Prod.ext hc hd)).elim
  · exact Or.inr (Or.inr (Or.inr hd))
  · exact Or.inr (Or.inl hd)
  · exact (deltaBottomRow_ne_one_neg_sqrtd g (Prod.ext hc hd)).elim
  · exact Or.inl hd
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact (deltaBottomRow_ne_one_one g (Prod.ext hc hd)).elim

/-- Exact four denominator rows with bottom-left entry `-1`. -/
theorem deltaBottomRow_snd_four_cases_of_fst_eq_neg_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = -1)
    (hgw : fuchsianSourceAction g • z = w) :
    (deltaBottomRow g).2 = 0 ∨ (deltaBottomRow g).2 = 1 ∨
      (deltaBottomRow g).2 = -Zsqrtd.sqrtd ∨
      (deltaBottomRow g).2 = 1 + Zsqrtd.sqrtd := by
  rcases deltaBottomRow_snd_cases_of_fst_eq_neg_one g hz hw hc hgw with
    hd | hd | hd | hd | hd | hd | hd
  · exact (deltaBottomRow_ne_neg_one_neg_one g (Prod.ext hc hd)).elim
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inl hd
  · exact (deltaBottomRow_ne_neg_one_sqrtd g (Prod.ext hc hd)).elim
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inr hd))
  · exact (deltaBottomRow_ne_neg_one_two g (Prod.ext hc hd)).elim

/-! ## Height equality inside the Ford polygon -/

private theorem normSq_sqrtd_add_ge_one_of_mem_orientedFundamentalRegion
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    1 ≤ normSq ((z : ℂ) + Real.sqrt 2) := by
  have hre := orientedFundamentalRegion_re_bounds hz
  have him := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  rw [normSq_apply]
  norm_num
  nlinarith [sq_nonneg (z.re + Real.sqrt 2 - Real.sqrt 2 / 2),
    sq_nonneg (z.im - Real.sqrt 2 / 2)]

private theorem normSq_sub_one_add_sqrtd_ge_one_of_mem_orientedFundamentalRegion
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    1 ≤ normSq ((z : ℂ) - (1 + Real.sqrt 2)) := by
  have hre := orientedFundamentalRegion_re_bounds hz
  have him := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  rw [normSq_apply]
  norm_num
  nlinarith [sq_nonneg (z.re - (1 + Real.sqrt 2) + Real.sqrt 2 / 2),
    sq_nonneg (z.im - Real.sqrt 2 / 2)]

/-- Every source transformation that carries one point of the doubled Ford polygon to another
has denominator norm at least one at the source point. -/
theorem bottomRowDenominatorNormSq_ge_one_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    1 ≤ normSq
      (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
        positiveEmbedding (deltaBottomRow g).2) := by
  rcases deltaBottomRow_fst_cases_of_maps_oriented g hz hw hgw with
    hc | hc | hc | hc | hc
  · have hdiag := deltaWordMatrix_diagonal_cases_of_bottomLeft_eq_zero g hc
    have hd : (deltaBottomRow g).2 = 1 ∨ (deltaBottomRow g).2 = -1 := by
      rcases hdiag with hdiag | hdiag
      · exact Or.inl (by simpa [deltaBottomRow, wordBottomRow] using hdiag.2)
      · exact Or.inr (by simpa [deltaBottomRow, wordBottomRow] using hdiag.2)
    rcases hd with hd | hd <;> rw [hc, hd] <;> norm_num [normSq_apply]
  · rcases deltaBottomRow_snd_four_cases_of_fst_eq_one g hz hw hc hgw with
      hd | hd | hd | hd
    · simpa [hc, hd] using normSq_ge_one_of_mem_orientedFundamentalRegion hz
    · have h := normSq_one_sub_ge_one_of_mem_orientedFundamentalRegion hz
      rw [hc, hd]
      norm_num [normSq_apply] at h ⊢
      nlinarith
    · have h := normSq_sqrtd_add_ge_one_of_mem_orientedFundamentalRegion hz
      simpa [hc, hd] using h
    · have h := normSq_sub_one_add_sqrtd_ge_one_of_mem_orientedFundamentalRegion hz
      rw [hc, hd]
      norm_num [normSq_apply] at h ⊢
      nlinarith
  · rcases deltaBottomRow_snd_four_cases_of_fst_eq_neg_one g hz hw hc hgw with
      hd | hd | hd | hd
    · have h := normSq_ge_one_of_mem_orientedFundamentalRegion hz
      simpa [hc, hd, normSq_apply] using h
    · have h := normSq_one_sub_ge_one_of_mem_orientedFundamentalRegion hz
      rw [hc, hd]
      norm_num [normSq_apply] at h ⊢
      nlinarith
    · have h := normSq_sqrtd_add_ge_one_of_mem_orientedFundamentalRegion hz
      rw [hc, hd]
      norm_num [normSq_apply] at h ⊢
      nlinarith
    · have h := normSq_sub_one_add_sqrtd_ge_one_of_mem_orientedFundamentalRegion hz
      rw [hc, hd]
      norm_num [normSq_apply] at h ⊢
      nlinarith
  · have him := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
    have hspos := sqrt_two_pos
    have hs2 := sqrt_two_sq
    rw [hc, positiveEmbedding_apply]
    norm_num [normSq_apply]
    have hsy : 1 ≤ Real.sqrt 2 * z.im := by nlinarith
    nlinarith [sq_nonneg (Real.sqrt 2 * z.im - 1),
      sq_nonneg (Real.sqrt 2 * z.re +
        positiveEmbedding (deltaBottomRow g).2)]
  · have him := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
    have hspos := sqrt_two_pos
    have hs2 := sqrt_two_sq
    rw [hc, map_neg, positiveEmbedding_apply]
    norm_num [normSq_apply]
    have hsy : 1 ≤ Real.sqrt 2 * z.im := by nlinarith
    nlinarith [sq_nonneg (Real.sqrt 2 * z.im - 1),
      sq_nonneg (-(Real.sqrt 2 * z.re) +
        positiveEmbedding (deltaBottomRow g).2)]

theorem im_le_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    w.im ≤ z.im := by
  have hN := bottomRowDenominatorNormSq_ge_one_of_maps_oriented g hz hw hgw
  have hformula := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  rw [hgw] at hformula
  have hNpos := bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  rw [hformula]
  exact div_le_self z.im_pos.le hN

/-- Orbit-related points in the doubled Ford polygon have the same height. -/
theorem im_eq_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    z.im = w.im := by
  apply le_antisymm
  · apply im_le_of_maps_oriented g⁻¹ hw hz
    rw [← hgw, map_inv, inv_smul_smul]
  · exact im_le_of_maps_oriented g hz hw hgw

/-- Equality of heights forces the canonical automorphy denominator to have norm one. -/
theorem bottomRowDenominatorNormSq_eq_one_of_maps_oriented
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hgw : fuchsianSourceAction g • z = w) :
    normSq
        (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
          positiveEmbedding (deltaBottomRow g).2) = 1 := by
  have himEq := im_eq_of_maps_oriented g hz hw hgw
  have hformula := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  rw [hgw, ← himEq] at hformula
  have hNpos := bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  change 0 < normSq
      (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
        positiveEmbedding (deltaBottomRow g).2) at hNpos
  have hmul := (eq_div_iff hNpos.ne').mp hformula
  change z.im * normSq
      (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
        positiveEmbedding (deltaBottomRow g).2) = z.im at hmul
  nlinarith [z.im_pos]

private theorem mem_fundamentalTriangle_of_mem_oriented_of_normSq_eq_one
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hnorm : normSq (z : ℂ) = 1) :
    z ∈ fundamentalTriangle := by
  rcases hz with hz | hz
  · exact ⟨hz.1, hz.2.1, hnorm.ge⟩
  · have hrightNorm : 1 ≤ normSq (1 - (z : ℂ)) := hz.2.2
    have hdiff : normSq (1 - (z : ℂ)) = 2 - 2 * z.re := by
      norm_num [normSq_apply] at hnorm ⊢
      nlinarith
    have hre : z.re = 1 / 2 := by
      rw [hdiff] at hrightNorm
      nlinarith [hz.1]
    refine ⟨?_, hre.le, hnorm.ge⟩
    nlinarith [Real.sqrt_nonneg 2]

private theorem mem_rightFundamentalTriangle_of_mem_oriented_of_normSq_one_sub_eq_one
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hnorm : normSq (1 - (z : ℂ)) = 1) :
    z ∈ rightFundamentalTriangle := by
  rcases hz with hz | hz
  · have hleftNorm : 1 ≤ normSq (z : ℂ) := hz.2.2
    have hdiff : normSq (z : ℂ) = 2 * z.re := by
      norm_num [normSq_apply] at hnorm ⊢
      nlinarith
    have hre : z.re = 1 / 2 := by
      rw [hdiff] at hleftNorm
      nlinarith [hz.2.1]
    refine ⟨hre.ge, ?_, hnorm.ge⟩
    nlinarith [Real.sqrt_nonneg 2]
  · exact ⟨hz.1, hz.2.1, hnorm.ge⟩

private theorem gTwo_cube_smul_eq_sourceLeftUHP_of_normSq_eq_one
    (z : UpperHalfPlane) (hnorm : normSq (z : ℂ) = 1) :
    fuchsianSourceAction (g₂ ^ 3) • z = sourceLeftUHP z := by
  apply UpperHalfPlane.coe_injective
  change ((((fuchsianSourceAction (g₂ ^ 3)) z : UpperHalfPlane) : ℂ)) =
    (sourceLeftUHP z : ℂ)
  rw [SphereSixComplex.TriangleGroup.FuchsianPingPong.gTwo_cube_apply]
  change -Real.sqrt 2 - 1 / (z : ℂ) = sourceLeft (z : ℂ)
  apply Complex.ext <;>
    simp [sourceLeft, Complex.div_re, Complex.div_im, hnorm]

private theorem gOne_sq_smul_eq_sourceRightUHP_of_normSq_one_sub_eq_one
    (z : UpperHalfPlane) (hnorm : normSq (1 - (z : ℂ)) = 1) :
    fuchsianSourceAction (g₁ ^ 2) • z = sourceRightUHP z := by
  apply UpperHalfPlane.coe_injective
  change ((((fuchsianSourceAction (g₁ ^ 2)) z : UpperHalfPlane) : ℂ)) =
    (sourceRightUHP z : ℂ)
  rw [SphereSixComplex.TriangleGroup.FuchsianPingPong.gOne_sq_apply]
  change 1 / (1 - (z : ℂ)) = sourceRight (z : ℂ)
  apply Complex.ext <;>
    simp [sourceRight, Complex.div_re, Complex.div_im, hnorm]

/-! ## The order-four vertices -/

theorem eq_fuchsianTwo_or_sourceFarRightVertex_of_im_eq_min
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (him : z.im = Real.sqrt 2 / 2) :
    z = fuchsianTwoFixedPoint ∨ z = sourceFarRightVertex := by
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  rcases hz with hz | hz
  · left
    have hnorm : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
      simpa [normSq_apply, pow_two] using hz.2.2
    have hre : z.re = -Real.sqrt 2 / 2 := by
      have hposImpossible : ¬ Real.sqrt 2 / 2 ≤ z.re := by
        intro hpos
        nlinarith [hz.2.1, one_lt_sqrt_two]
      nlinarith [hz.1]
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simpa [fuchsianTwoFixedPoint] using hre
    · simpa [fuchsianTwoFixedPoint] using him
  · right
    have hnorm : 1 ≤ (1 - z.re) ^ 2 + z.im ^ 2 := by
      simpa [normSq_apply, pow_two] using hz.2.2
    have hposImpossible : ¬ Real.sqrt 2 / 2 ≤ 1 - z.re := by
      intro hpos
      nlinarith [hz.1, one_lt_sqrt_two]
    have ht : 1 - z.re = -(Real.sqrt 2 / 2) := by
      nlinarith [hz.2.1]
    have hre : z.re = 1 + Real.sqrt 2 / 2 := by linarith
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
        fuchsianTwoFixedPoint]
      nlinarith [hre]
    · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
        fuchsianTwoFixedPoint]
      exact him

private theorem eq_fuchsianTwoFixedPoint_of_normSq_sqrtd_add_eq_one
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hnorm : normSq ((z : ℂ) + Real.sqrt 2) = 1) :
    z = fuchsianTwoFixedPoint := by
  have hreBounds := orientedFundamentalRegion_re_bounds hz
  have himLower := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hnorm' : (z.re + Real.sqrt 2) ^ 2 + z.im ^ 2 = 1 := by
    simpa [normSq_apply, pow_two] using hnorm
  have hre : z.re = -Real.sqrt 2 / 2 := by
    nlinarith [sq_nonneg (z.re + Real.sqrt 2 - Real.sqrt 2 / 2),
      sq_nonneg (z.im - Real.sqrt 2 / 2)]
  have him : z.im = Real.sqrt 2 / 2 := by
    nlinarith [sq_nonneg (z.im - Real.sqrt 2 / 2)]
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simpa [fuchsianTwoFixedPoint] using hre
  · simpa [fuchsianTwoFixedPoint] using him

private theorem eq_sourceFarRightVertex_of_normSq_sub_far_eq_one
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hnorm : normSq ((z : ℂ) - (1 + Real.sqrt 2)) = 1) :
    z = sourceFarRightVertex := by
  have hreBounds := orientedFundamentalRegion_re_bounds hz
  have himLower := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hnorm' : (z.re - (1 + Real.sqrt 2)) ^ 2 + z.im ^ 2 = 1 := by
    simpa [normSq_apply, pow_two] using hnorm
  have hre : z.re = 1 + Real.sqrt 2 / 2 := by
    nlinarith [sq_nonneg
      (z.re - (1 + Real.sqrt 2) + Real.sqrt 2 / 2),
      sq_nonneg (z.im - Real.sqrt 2 / 2)]
  have him : z.im = Real.sqrt 2 / 2 := by
    nlinarith [sq_nonneg (z.im - Real.sqrt 2 / 2)]
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
      fuchsianTwoFixedPoint]
    nlinarith
  · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
      fuchsianTwoFixedPoint]
    exact him

private theorem fuchsianTwo_not_mem_sourceOpenChamber :
    (fuchsianTwoFixedPoint : ℂ) ∉ sourceOpenChamber := by
  intro h
  have hspos := sqrt_two_pos
  have hleft := h.1
  change -Real.sqrt 2 / 2 < (fuchsianTwoFixedPoint : ℂ).re at hleft
  simp [fuchsianTwoFixedPoint] at hleft

theorem source_oriented_pairing_of_both_im_eq_min
    {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hzIm : z.im = Real.sqrt 2 / 2)
    (hwIm : w.im = Real.sqrt 2 / 2) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  rcases eq_fuchsianTwo_or_sourceFarRightVertex_of_im_eq_min hz hzIm with hz | hz <;>
    rcases eq_fuchsianTwo_or_sourceFarRightVertex_of_im_eq_min hw hwIm with hw | hw
  · exact Or.inl (hz.trans hw.symm)
  · right
    refine ⟨fuchsianTwoFixedPoint, fuchsianTwoFixedPoint_mem_fundamentalTriangle,
      fuchsianTwo_not_mem_sourceOpenChamber, Or.inl ⟨hz, ?_⟩⟩
    simpa [sourceFarRightVertex] using hw
  · right
    refine ⟨fuchsianTwoFixedPoint, fuchsianTwoFixedPoint_mem_fundamentalTriangle,
      fuchsianTwo_not_mem_sourceOpenChamber, Or.inr ⟨?_, hw⟩⟩
    simpa [sourceFarRightVertex] using hz
  · exact Or.inl (hz.trans hw.symm)

theorem source_oriented_pairing_of_bottomLeft_eq_sqrtd
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = Zsqrtd.sqrtd)
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have himEq := im_eq_of_maps_oriented g hz hw hgw
  have hzlow := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hwlow := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hw
  let N := normSq
    (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
      positiveEmbedding (deltaBottomRow g).2)
  have hNpos : 0 < N := bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  have hformula := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  rw [hgw] at hformula
  change w.im = z.im / N at hformula
  have hNmul : N * w.im = z.im := by
    have h := (eq_div_iff hNpos.ne').mp hformula
    nlinarith
  have hNlower : 2 * z.im ^ 2 ≤ N := by
    dsimp only [N]
    rw [hc, positiveEmbedding_apply]
    norm_num [normSq_apply]
    nlinarith [sqrt_two_sq,
      sq_nonneg (Real.sqrt 2 * z.re + positiveEmbedding (deltaBottomRow g).2)]
  have hprod : z.im * w.im ≤ 1 / 2 := by
    nlinarith [z.im_pos, w.im_pos]
  have hprodLower := half_le_im_mul_im_of_mem_orientedFundamentalRegion hz hw
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hzIm : z.im = Real.sqrt 2 / 2 := by nlinarith
  have hwIm : w.im = Real.sqrt 2 / 2 := by nlinarith
  exact source_oriented_pairing_of_both_im_eq_min hz hw hzIm hwIm

theorem source_oriented_pairing_of_bottomLeft_eq_neg_sqrtd
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = -Zsqrtd.sqrtd)
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have himEq := im_eq_of_maps_oriented g hz hw hgw
  have hzlow := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hz
  have hwlow := sqrt_two_div_two_le_im_of_mem_orientedFundamentalRegion hw
  let N := normSq
    (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
      positiveEmbedding (deltaBottomRow g).2)
  have hNpos : 0 < N := bottomRowDenominatorNormSq_deltaBottomRow_pos g z
  have hformula := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  rw [hgw] at hformula
  change w.im = z.im / N at hformula
  have hNmul : N * w.im = z.im := by
    have h := (eq_div_iff hNpos.ne').mp hformula
    nlinarith
  have hNlower : 2 * z.im ^ 2 ≤ N := by
    dsimp only [N]
    rw [hc, map_neg, positiveEmbedding_apply]
    norm_num [normSq_apply]
    nlinarith [sqrt_two_sq,
      sq_nonneg (-(Real.sqrt 2 * z.re) + positiveEmbedding (deltaBottomRow g).2)]
  have hprod : z.im * w.im ≤ 1 / 2 := by
    nlinarith [z.im_pos, w.im_pos]
  have hprodLower := half_le_im_mul_im_of_mem_orientedFundamentalRegion hz hw
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hzIm : z.im = Real.sqrt 2 / 2 := by nlinarith
  have hwIm : w.im = Real.sqrt 2 / 2 := by nlinarith
  exact source_oriented_pairing_of_both_im_eq_min hz hw hzIm hwIm

/-! ## Equal bottom rows differ by a cusp translation -/

private theorem eq_zero_of_inCoefficientCone_positiveEmbedding_eq_zero
    {a : QuadraticInteger} (ha : InCoefficientCone a)
    (hzero : positiveEmbedding a = 0) : a = 0 := by
  change 0 ≤ a.re * a.im at ha
  rw [positiveEmbedding_apply] at hzero
  have hspos := sqrt_two_pos
  rcases mul_nonneg_iff.mp ha with ha | ha
  · have hre : (a.re : ℝ) = 0 := by
      have him : 0 ≤ (a.im : ℝ) := by exact_mod_cast ha.2
      have hre : 0 ≤ (a.re : ℝ) := by exact_mod_cast ha.1
      nlinarith
    have him : (a.im : ℝ) = 0 := by
      have him : 0 ≤ (a.im : ℝ) := by exact_mod_cast ha.2
      nlinarith
    apply Zsqrtd.ext <;> norm_num at hre him ⊢ <;> assumption
  · have hre : (a.re : ℝ) = 0 := by
      have him : (a.im : ℝ) ≤ 0 := by exact_mod_cast ha.2
      have hre : (a.re : ℝ) ≤ 0 := by exact_mod_cast ha.1
      nlinarith
    have him : (a.im : ℝ) = 0 := by
      have him : (a.im : ℝ) ≤ 0 := by exact_mod_cast ha.2
      nlinarith
    apply Zsqrtd.ext <;> norm_num at hre him ⊢ <;> assumption

private theorem bottomRowDenominatorNormSq_eq_of_eq_or_neg
    {g r : Delta}
    (hrow : deltaBottomRow g = deltaBottomRow r ∨
      deltaBottomRow g = (-(deltaBottomRow r).1, -(deltaBottomRow r).2))
    (z : UpperHalfPlane) :
    normSq (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
      positiveEmbedding (deltaBottomRow g).2) =
    normSq (positiveEmbedding (deltaBottomRow r).1 * (z : ℂ) +
      positiveEmbedding (deltaBottomRow r).2) := by
  rcases hrow with hrow | hrow
  · rw [hrow]
  · have hc := congrArg Prod.fst hrow
    have hd := congrArg Prod.snd hrow
    rw [hc, hd, map_neg, map_neg]
    simp only [Complex.ofReal_neg]
    have hneg :
        -positiveEmbedding (deltaBottomRow r).1 * (z : ℂ) +
            -positiveEmbedding (deltaBottomRow r).2 =
          -(positiveEmbedding (deltaBottomRow r).1 * (z : ℂ) +
            positiveEmbedding (deltaBottomRow r).2) := by ring
    rw [hneg, normSq_neg]

private theorem action_im_eq_of_bottomRow_eq_or_neg
    {g r : Delta}
    (hrow : deltaBottomRow g = deltaBottomRow r ∨
      deltaBottomRow g = (-(deltaBottomRow r).1, -(deltaBottomRow r).2))
    (z : UpperHalfPlane) :
    (fuchsianSourceAction g • z).im =
      (fuchsianSourceAction r • z).im := by
  rw [fuchsianSourceAction_im_eq_div_wordBottomNormSq,
    fuchsianSourceAction_im_eq_div_wordBottomNormSq,
    bottomRowDenominatorNormSq_eq_of_eq_or_neg hrow]

private theorem bottomLeft_eq_zero_of_action_preserves_im
    (h : Delta) (hpres : ∀ z : UpperHalfPlane,
      (fuchsianSourceAction h • z).im = z.im) :
    (deltaBottomRow h).1 = 0 := by
  let z₁ : UpperHalfPlane := ⟨Complex.I, by norm_num⟩
  let z₂ : UpperHalfPlane := ⟨2 * Complex.I, by norm_num⟩
  let c : ℝ := positiveEmbedding (deltaBottomRow h).1
  let d : ℝ := positiveEmbedding (deltaBottomRow h).2
  have h₁ := fuchsianSourceAction_im_eq_div_wordBottomNormSq h z₁
  have h₂ := fuchsianSourceAction_im_eq_div_wordBottomNormSq h z₂
  rw [hpres z₁] at h₁
  rw [hpres z₂] at h₂
  have hN₁ : normSq (c * (z₁ : ℂ) + d) = 1 := by
    change (z₁ : ℂ).im = (z₁ : ℂ).im / normSq (c * (z₁ : ℂ) + d) at h₁
    have hpos : 0 < normSq (c * (z₁ : ℂ) + d) := by
      dsimp only [c, d]
      exact bottomRowDenominatorNormSq_deltaBottomRow_pos h z₁
    have him : (z₁ : ℂ).im = 1 := by norm_num [z₁]
    rw [him] at h₁
    have h := (eq_div_iff hpos.ne').mp h₁
    norm_num at h ⊢
    exact h
  have hN₂ : normSq (c * (z₂ : ℂ) + d) = 1 := by
    change (z₂ : ℂ).im = (z₂ : ℂ).im / normSq (c * (z₂ : ℂ) + d) at h₂
    have hpos : 0 < normSq (c * (z₂ : ℂ) + d) := by
      dsimp only [c, d]
      exact bottomRowDenominatorNormSq_deltaBottomRow_pos h z₂
    have him : (z₂ : ℂ).im = 2 := by norm_num [z₂]
    rw [him] at h₂
    have := (eq_div_iff hpos.ne').mp h₂
    nlinarith
  have hcReal : c = 0 := by
    simp [z₁, normSq_apply] at hN₁
    simp [z₂, normSq_apply] at hN₂
    nlinarith
  apply eq_zero_of_inCoefficientCone_positiveEmbedding_eq_zero
    (wordMatrix_matrixInCoefficientCone (deltaNormalForm h) 1 0)
  simpa [c, deltaBottomRow, wordBottomRow] using hcReal

/-- Two source elements whose canonical bottom rows agree up to simultaneous sign differ by a
left power of the primitive cusp translation. -/
theorem eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
    (g r : Delta)
    (hrow : deltaBottomRow g = deltaBottomRow r ∨
      deltaBottomRow g = (-(deltaBottomRow r).1, -(deltaBottomRow r).2)) :
    ∃ n : ℤ, g = (g₁ * g₂) ^ n * r := by
  let h := g * r⁻¹
  have hpres : ∀ z : UpperHalfPlane,
      (fuchsianSourceAction h • z).im = z.im := by
    intro z
    let u := fuchsianSourceAction r⁻¹ • z
    calc
      (fuchsianSourceAction h • z).im =
          (fuchsianSourceAction g • u).im := by
        simp [h, u, map_mul, mul_smul]
      _ = (fuchsianSourceAction r • u).im :=
        action_im_eq_of_bottomRow_eq_or_neg hrow u
      _ = z.im := by simp [u, map_inv]
  have hc : (deltaBottomRow h).1 = 0 :=
    bottomLeft_eq_zero_of_action_preserves_im h hpres
  obtain ⟨n, hn⟩ := eq_zpow_product_of_deltaBottomRow_fst_eq_zero h hc
  refine ⟨n, ?_⟩
  dsimp only [h] at hn
  calc
    g = (g * r⁻¹) * r := by group
    _ = (g₁ * g₂) ^ n * r := by rw [hn]

/-! ## The two smooth side-pairing rows -/

private theorem source_oriented_pairing_of_bottomRow_eq_one_zero_or_neg
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hrow : deltaBottomRow g = (1, 0) ∨ deltaBottomRow g = (-1, 0))
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have hN := bottomRowDenominatorNormSq_eq_one_of_maps_oriented g hz hw hgw
  have hnorm : normSq (z : ℂ) = 1 := by
    rcases hrow with hrow | hrow <;>
      rw [hrow] at hN <;>
      norm_num [normSq_apply] at hN ⊢ <;>
      nlinarith
  have hzFund :=
    mem_fundamentalTriangle_of_mem_oriented_of_normSq_eq_one hz hnorm
  have hcompare : deltaBottomRow g = deltaBottomRow (g₂ ^ 3) ∨
      deltaBottomRow g =
        (-(deltaBottomRow (g₂ ^ 3)).1, -(deltaBottomRow (g₂ ^ 3)).2) := by
    rw [deltaBottomRow_gTwo_cube]
    simpa using hrow
  obtain ⟨n, hn⟩ :=
    eq_cusp_zpow_mul_of_bottomRow_eq_or_neg g (g₂ ^ 3) hcompare
  have hr := gTwo_cube_smul_eq_sourceLeftUHP_of_normSq_eq_one z hnorm
  have hgw' : fuchsianSourceAction ((g₁ * g₂) ^ n) • sourceLeftUHP z = w := by
    rw [hn, map_mul, mul_smul] at hgw
    rwa [hr] at hgw
  have hcoe := congrArg (fun q : UpperHalfPlane ↦ (q : ℂ)) hgw'
  change ((((fuchsianSourceAction ((g₁ * g₂) ^ n))
    (sourceLeftUHP z) : UpperHalfPlane) : ℂ)) = (w : ℂ) at hcoe
  rw [FuchsianTessellation.product_zpow_apply] at hcoe
  have hre := congrArg Complex.re hcoe
  have him := congrArg Complex.im hcoe
  norm_num [sourceLeftUHP, sourceLeft] at hre him
  have hzre := orientedFundamentalRegion_re_bounds hz
  have hwre := orientedFundamentalRegion_re_bounds hw
  have hzFundLeft : -Real.sqrt 2 / 2 ≤ z.re := hzFund.1
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hwidth := cuspWidth_pos
  have hnLowerReal : (0 : ℝ) ≤ n := by
    change (0 : ℝ) ≤ (n : ℝ)
    unfold cuspWidth at hre hwidth
    nlinarith
  have hnUpperReal : (n : ℝ) < 2 := by
    unfold cuspWidth at hre hwidth
    nlinarith [hzFund.2.1, hwre.2]
  have hnLower : (0 : ℤ) ≤ n := by exact_mod_cast hnLowerReal
  have hnUpper : n < (2 : ℤ) := by exact_mod_cast hnUpperReal
  have hncases : n = 0 ∨ n = 1 := by omega
  rcases hncases with rfl | rfl
  · left
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · change z.re = w.re
      norm_num [cuspWidth] at hre
      nlinarith [hzFundLeft, hwre.1]
    · exact him
  · right
    refine ⟨z, hzFund, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · rintro ⟨_, _, _, hopenNorm⟩
      nlinarith
    · apply UpperHalfPlane.coe_injective
      apply Complex.ext
      · change w.re = (sourceRight (z : ℂ)).re
        rw [sourceRight_re]
        change w.re = 1 - z.re
        norm_num [cuspWidth] at hre
        linarith
      · simpa [sourceRight] using him.symm

private theorem sourceRightUHP_mem_fundamentalTriangle_of_mem_right
    {z : UpperHalfPlane} (hz : z ∈ rightFundamentalTriangle) :
    sourceRightUHP z ∈ fundamentalTriangle := by
  rcases hz with ⟨hzLeft, hzRight, hzNorm⟩
  change 1 / 2 ≤ z.re at hzLeft
  change z.re ≤ 1 + Real.sqrt 2 / 2 at hzRight
  refine ⟨?_, ?_, ?_⟩
  · change -Real.sqrt 2 / 2 ≤ (sourceRight (z : ℂ)).re
    rw [sourceRight_re]
    change -Real.sqrt 2 / 2 ≤ 1 - z.re
    linarith
  · change (sourceRight (z : ℂ)).re ≤ 1 / 2
    rw [sourceRight_re]
    change 1 - z.re ≤ 1 / 2
    linarith
  · change 1 ≤ normSq (sourceRight (z : ℂ))
    have heq : normSq (sourceRight (z : ℂ)) =
        normSq (1 - (z : ℂ)) := by
      simp [sourceRight, normSq_apply]
    rwa [heq]

private theorem sourceRightUHP_involutive (z : UpperHalfPlane) :
    sourceRightUHP (sourceRightUHP z) = z := by
  apply UpperHalfPlane.coe_injective
  exact sourceRight_involutive (z : ℂ)

private theorem source_oriented_pairing_of_bottomRow_eq_one_neg_one_or_neg
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hrow : deltaBottomRow g = (1, -1) ∨ deltaBottomRow g = (-1, 1))
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have hN := bottomRowDenominatorNormSq_eq_one_of_maps_oriented g hz hw hgw
  have hnorm : normSq (1 - (z : ℂ)) = 1 := by
    rcases hrow with hrow | hrow <;>
      rw [hrow] at hN <;>
      norm_num [normSq_apply] at hN ⊢ <;>
      nlinarith
  have hzRight :=
    mem_rightFundamentalTriangle_of_mem_oriented_of_normSq_one_sub_eq_one hz hnorm
  have hcompare : deltaBottomRow g = deltaBottomRow (g₁ ^ 2) ∨
      deltaBottomRow g =
        (-(deltaBottomRow (g₁ ^ 2)).1, -(deltaBottomRow (g₁ ^ 2)).2) := by
    rw [deltaBottomRow_gOne_sq]
    simpa using hrow
  obtain ⟨n, hn⟩ :=
    eq_cusp_zpow_mul_of_bottomRow_eq_or_neg g (g₁ ^ 2) hcompare
  have hr := gOne_sq_smul_eq_sourceRightUHP_of_normSq_one_sub_eq_one z hnorm
  have hgw' : fuchsianSourceAction ((g₁ * g₂) ^ n) • sourceRightUHP z = w := by
    rw [hn, map_mul, mul_smul] at hgw
    rwa [hr] at hgw
  have hcoe := congrArg (fun q : UpperHalfPlane ↦ (q : ℂ)) hgw'
  change ((((fuchsianSourceAction ((g₁ * g₂) ^ n))
    (sourceRightUHP z) : UpperHalfPlane) : ℂ)) = (w : ℂ) at hcoe
  rw [FuchsianTessellation.product_zpow_apply] at hcoe
  have hre := congrArg Complex.re hcoe
  have him := congrArg Complex.im hcoe
  norm_num [sourceRightUHP, sourceRight] at hre him
  have hwre := orientedFundamentalRegion_re_bounds hw
  have hspos := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hwidth := cuspWidth_pos
  have hnLowerReal : (-1 : ℝ) < n := by
    change (-1 : ℝ) < (n : ℝ)
    unfold cuspWidth at hre hwidth
    nlinarith [hzRight.1, hwre.1]
  have hnUpperReal : (n : ℝ) ≤ 1 := by
    unfold cuspWidth at hre hwidth
    nlinarith [hzRight.2.1, hwre.2]
  have hnLower : (-1 : ℤ) < n := by exact_mod_cast hnLowerReal
  have hnUpper : n ≤ (1 : ℤ) := by exact_mod_cast hnUpperReal
  have hncases : n = 0 ∨ n = 1 := by omega
  rcases hncases with rfl | rfl
  · right
    let u : UpperHalfPlane := sourceRightUHP z
    have huFund : u ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right hzRight
    have huNorm : normSq (u : ℂ) = 1 := by
      change normSq (sourceRight (z : ℂ)) = 1
      simpa [sourceRight, normSq_apply] using hnorm
    have hwu : w = u := by
      apply UpperHalfPlane.coe_injective
      apply Complex.ext
      · change w.re = u.re
        dsimp only [u]
        change w.re = (sourceRight (z : ℂ)).re
        rw [sourceRight_re]
        change w.re = 1 - z.re
        norm_num [cuspWidth] at hre
        linarith
      · dsimp only [u]
        simpa [sourceRight] using him.symm
    refine ⟨u, huFund, ?_, Or.inr ⟨?_, hwu⟩⟩
    · rintro ⟨_, _, _, hopenNorm⟩
      nlinarith
    · exact (sourceRightUHP_involutive z).symm
  · left
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · change z.re = w.re
      norm_num [cuspWidth] at hre
      nlinarith [hzRight.2.1, hwre.2]
    · exact him

private theorem source_oriented_pairing_of_bottomRow_sqrtd_center
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hrow : deltaBottomRow g = (1, Zsqrtd.sqrtd) ∨
      deltaBottomRow g = (-1, -Zsqrtd.sqrtd))
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have hN := bottomRowDenominatorNormSq_eq_one_of_maps_oriented g hz hw hgw
  have hnorm : normSq ((z : ℂ) + Real.sqrt 2) = 1 := by
    rcases hrow with hrow | hrow <;>
      rw [hrow] at hN <;>
      norm_num [normSq_apply, positiveEmbedding_apply] at hN ⊢ <;>
      nlinarith
  have hzVertex :=
    eq_fuchsianTwoFixedPoint_of_normSq_sqrtd_add_eq_one hz hnorm
  have himEq := im_eq_of_maps_oriented g hz hw hgw
  have hzIm : z.im = Real.sqrt 2 / 2 := by
    rw [hzVertex]
    simp [fuchsianTwoFixedPoint]
  have hwIm : w.im = Real.sqrt 2 / 2 := by
    rw [← himEq, hzIm]
  exact source_oriented_pairing_of_both_im_eq_min hz hw hzIm hwIm

private theorem source_oriented_pairing_of_bottomRow_far_center
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hrow : deltaBottomRow g = (1, -(1 + Zsqrtd.sqrtd)) ∨
      deltaBottomRow g = (-1, 1 + Zsqrtd.sqrtd))
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  have hN := bottomRowDenominatorNormSq_eq_one_of_maps_oriented g hz hw hgw
  have hnorm : normSq ((z : ℂ) - (1 + Real.sqrt 2)) = 1 := by
    rcases hrow with hrow | hrow <;>
      rw [hrow] at hN <;>
      norm_num [normSq_apply, positiveEmbedding_apply] at hN ⊢ <;>
      nlinarith
  have hzVertex :=
    eq_sourceFarRightVertex_of_normSq_sub_far_eq_one hz hnorm
  have himEq := im_eq_of_maps_oriented g hz hw hgw
  have hzIm : z.im = Real.sqrt 2 / 2 := by
    rw [hzVertex]
    simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
      fuchsianTwoFixedPoint]
  have hwIm : w.im = Real.sqrt 2 / 2 := by
    rw [← himEq, hzIm]
  exact source_oriented_pairing_of_both_im_eq_min hz hw hzIm hwIm

/-- Complete the four nonzero denominator rows with bottom-left coefficient `1`. -/
theorem source_oriented_pairing_of_bottomLeft_eq_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = 1)
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  rcases deltaBottomRow_snd_four_cases_of_fst_eq_one g hz hw hc hgw with
    hd | hd | hd | hd
  · exact source_oriented_pairing_of_bottomRow_eq_one_zero_or_neg
      g hz hw (Or.inl (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_eq_one_neg_one_or_neg
      g hz hw (Or.inl (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_sqrtd_center
      g hz hw (Or.inl (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_far_center
      g hz hw (Or.inl (Prod.ext hc hd)) hgw

/-- Complete the sign-symmetric four denominator rows with bottom-left coefficient `-1`. -/
theorem source_oriented_pairing_of_bottomLeft_eq_neg_one
    (g : Delta) {z w : UpperHalfPlane}
    (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hc : (deltaBottomRow g).1 = -1)
    (hgw : fuchsianSourceAction g • z = w) :
    z = w ∨
      ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
        (u : ℂ) ∉ sourceOpenChamber ∧
        ((z = u ∧ w = sourceRightUHP u) ∨
          (z = sourceRightUHP u ∧ w = u)) := by
  rcases deltaBottomRow_snd_four_cases_of_fst_eq_neg_one g hz hw hc hgw with
    hd | hd | hd | hd
  · exact source_oriented_pairing_of_bottomRow_eq_one_zero_or_neg
      g hz hw (Or.inr (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_eq_one_neg_one_or_neg
      g hz hw (Or.inr (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_sqrtd_center
      g hz hw (Or.inr (Prod.ext hc hd)) hgw
  · exact source_oriented_pairing_of_bottomRow_far_center
      g hz hw (Or.inr (Prod.ext hc hd)) hgw

private theorem sourceRightUHP_eq_of_outer_re_and_im
    (z w : UpperHalfPlane) (hz : z.re = -Real.sqrt 2 / 2)
    (hw : w.re = 1 + Real.sqrt 2 / 2) (him : z.im = w.im) :
    sourceRightUHP z = w := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · change (sourceRight (z : ℂ)).re = w.re
    rw [sourceRight_re]
    change 1 - z.re = w.re
    rw [hz, hw]
    ring
  · simpa [sourceRight] using him

/-- The cusp row, now without the formerly conditional centralizer hypothesis. -/
theorem source_oriented_pairing_of_bottomLeft_eq_zero_unconditional
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
  obtain ⟨n, rfl⟩ := eq_zpow_product_of_deltaBottomRow_fst_eq_zero g hc
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
    exact (sourceRightUHP_eq_of_outer_re_and_im
      w z hwleft hzright him.symm).symm
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
    exact (sourceRightUHP_eq_of_outer_re_and_im
      z w hzleft hwright him).symm

/-! ## Unconditional polygon classification and scalar consistency -/

/-- Exact orbit-pairing classification for the doubled closed source Ford polygon. -/
theorem sourceOrientedFundamentalPairingClassification :
    SourceOrientedFundamentalPairingClassification := by
  intro z w hz hw horbit
  obtain ⟨g, hgw⟩ := horbit
  rcases deltaBottomRow_fst_cases_of_maps_oriented g hz hw hgw with
    hc | hc | hc | hc | hc
  · exact source_oriented_pairing_of_bottomLeft_eq_zero_unconditional
      g hz hw hc hgw
  · exact source_oriented_pairing_of_bottomLeft_eq_one g hz hw hc hgw
  · exact source_oriented_pairing_of_bottomLeft_eq_neg_one g hz hw hc hgw
  · exact source_oriented_pairing_of_bottomLeft_eq_sqrtd g hz hw hc hgw
  · exact source_oriented_pairing_of_bottomLeft_eq_neg_sqrtd g hz hw hc hgw

/-- The chamber scalar is unconditionally consistent on orbit-related representatives in the
doubled closed fundamental polygon. -/
theorem sourceFundamentalScalarConsistent
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    SourceFundamentalScalarConsistent S :=
  sourceFundamentalScalarConsistent_of_pairingClassification S
    sourceOrientedFundamentalPairingClassification


end SphereSixComplex.Periods.SourceChamberTopology
