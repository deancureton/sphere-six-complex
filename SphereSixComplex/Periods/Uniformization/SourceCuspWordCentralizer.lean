module

public import SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingGeometry
import all SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingGeometry

@[expose] public section

/-!
# The cusp-word bottom-row automaton

This file proves the reduced-word input isolated by
`SourceFundamentalPairingGeometry`: the only canonical words with zero bottom-left entry are
integral powers of the primitive cusp word `g₁g₂`.

Tau Ceti is used only transitively through the imported scalar files; this file adds no Tau Ceti
import or theorem use.
-/

open Matrix

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

private theorem sameQuadrant_pair_bottomLeft_zero
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger)
    (hrow : SameQuadrantRow (M 1 0) (M 1 1))
    (hnz : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0)
    (a : DeltaFactor false) (ha : a ≠ 1)
    (b : DeltaFactor true) (hb : b ≠ 1)
    (hzero : (M * factorMatrix false a * factorMatrix true b) 1 0 = 0) :
    M 1 0 = 0 ∧ a = Multiplicative.ofAdd (1 : ZMod 3) ∧
      b = Multiplicative.ofAdd (1 : ZMod 4) := by
  change CyclicThree at a
  change CyclicFour at b
  let na := (Multiplicative.toAdd a).val
  let nb := (Multiplicative.toAdd b).val
  change (M * quadraticOne ^ na * quadraticTwo ^ nb) 1 0 = 0 at hzero
  have hna_lt : na < 3 := ZMod.val_lt _
  have hnb_lt : nb < 4 := ZMod.val_lt _
  have hna_ne : na ≠ 0 := by
    intro h
    apply ha
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    change na = 0
    exact h
  have hnb_ne : nb ≠ 0 := by
    intro h
    apply hb
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    change nb = 0
    exact h
  have hna : na = 1 ∨ na = 2 := by omega
  have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
  rcases hna with hna | hna <;> rcases hnb with hnb | hnb | hnb
  all_goals
    rcases hrow with hrow | hrow
  all_goals
    have hre := congrArg Zsqrtd.re hzero
    have him := congrArg Zsqrtd.im hzero
    norm_num [factorMatrix, na, nb, hna, hnb, quadraticOne, quadraticTwo, pow_two, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ] at hre him
  all_goals
    simp only [CoeffNonnegative, CoeffNonpositive] at hrow
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩
       · apply Zsqrtd.ext <;> norm_num <;> omega
       · apply Multiplicative.toAdd.injective
         rw [toAdd_ofAdd]
         apply ZMod.val_injective 3
         change na = (1 : ZMod 3).val
         exact hna.trans (ZMod.val_one 3).symm
       · apply Multiplicative.toAdd.injective
         rw [toAdd_ofAdd]
         apply ZMod.val_injective 4
         change nb = (1 : ZMod 4).val
         exact hnb.trans (ZMod.val_cast_of_lt (by norm_num : 1 < 4)).symm)
    | (exfalso; rcases hnz with h | h <;> apply h <;>
        apply Zsqrtd.ext <;> norm_num <;> omega)

private theorem oppositeQuadrant_pair_bottomLeft_zero
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger)
    (hrow : OppositeQuadrantRow (M 1 0) (M 1 1))
    (hnz : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0)
    (b : DeltaFactor true) (hb : b ≠ 1)
    (a : DeltaFactor false) (ha : a ≠ 1)
    (hzero : (M * factorMatrix true b * factorMatrix false a) 1 0 = 0) :
    M 1 0 = 0 ∧ b = Multiplicative.ofAdd (3 : ZMod 4) ∧
      a = Multiplicative.ofAdd (2 : ZMod 3) := by
  change CyclicFour at b
  change CyclicThree at a
  let nb := (Multiplicative.toAdd b).val
  let na := (Multiplicative.toAdd a).val
  change (M * quadraticTwo ^ nb * quadraticOne ^ na) 1 0 = 0 at hzero
  have hnb_lt : nb < 4 := ZMod.val_lt _
  have hna_lt : na < 3 := ZMod.val_lt _
  have hnb_ne : nb ≠ 0 := by
    intro h
    apply hb
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    change nb = 0
    exact h
  have hna_ne : na ≠ 0 := by
    intro h
    apply ha
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    change na = 0
    exact h
  have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
  have hna : na = 1 ∨ na = 2 := by omega
  rcases hnb with hnb | hnb | hnb <;> rcases hna with hna | hna
  all_goals
    rcases hrow with hrow | hrow
  all_goals
    have hre := congrArg Zsqrtd.re hzero
    have him := congrArg Zsqrtd.im hzero
    norm_num [factorMatrix, na, nb, hna, hnb, quadraticOne, quadraticTwo, pow_two, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ] at hre him
  all_goals
    simp only [CoeffNonnegative, CoeffNonpositive] at hrow
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩
       · apply Zsqrtd.ext <;> norm_num <;> omega
       · apply Multiplicative.toAdd.injective
         rw [toAdd_ofAdd]
         apply ZMod.val_injective 4
         change nb = (3 : ZMod 4).val
         exact hnb.trans (ZMod.val_cast_of_lt (by norm_num : 3 < 4)).symm
       · apply Multiplicative.toAdd.injective
         rw [toAdd_ofAdd]
         apply ZMod.val_injective 3
         change na = (2 : ZMod 3).val
         exact hna.trans (ZMod.val_cast_of_lt (by norm_num : 2 < 3)).symm)
    | (exfalso; rcases hnz with h | h <;> apply h <;>
        apply Zsqrtd.ext <;> norm_num <;> omega)

private theorem neWordMatrix_eq_of_prod_eq {i j k l : Bool}
    {u : Monoid.CoprodI.NeWord DeltaFactor i j}
    {v : Monoid.CoprodI.NeWord DeltaFactor k l} (h : u.prod = v.prod) :
    neWordMatrix u = neWordMatrix v := by
  rw [neWordMatrix_eq_wordMatrix, neWordMatrix_eq_wordMatrix]
  apply congrArg wordMatrix
  apply (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm.injective
  change u.toWord.prod = v.toWord.prod
  exact h

private theorem neWordMatrix_eq_factorMatrix_of_singleton_prod {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j)
    (hprod : w.prod = Monoid.CoprodI.of w.last) :
    neWordMatrix w = factorMatrix j w.last := by
  let v : Monoid.CoprodI.NeWord DeltaFactor j j :=
    .singleton w.last (BinaryIndexedCoprod.NeWord.last_ne_one w)
  have hvprod : w.prod = v.prod := by
    rw [hprod]
    simp [v]
  have hmatrix := neWordMatrix_eq_of_prod_eq hvprod
  simpa [v, neWordMatrix] using hmatrix

private theorem neWordMatrix_eq_init_mul_factorMatrix {i j k : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j)
    (p : Monoid.CoprodI.NeWord DeltaFactor i k) (hkj : k ≠ j)
    (hprod : w.prod = p.prod * Monoid.CoprodI.of w.last) :
    neWordMatrix w = neWordMatrix p * factorMatrix j w.last := by
  let v : Monoid.CoprodI.NeWord DeltaFactor i j :=
    .append p hkj (.singleton w.last (BinaryIndexedCoprod.NeWord.last_ne_one w))
  have hvprod : w.prod = v.prod := by
    rw [hprod]
    simp [v]
  have hmatrix := neWordMatrix_eq_of_prod_eq hvprod
  simpa [v, neWordMatrix] using hmatrix

private theorem neWordMatrix_det_one {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    (neWordMatrix w).det = 1 := by
  rw [neWordMatrix_eq_wordMatrix]
  exact wordMatrix_det_one w.toWord

private theorem neWordMatrix_bottomRow_ne_zero {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    neWordMatrix w 1 0 ≠ 0 ∨ neWordMatrix w 1 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hdet := neWordMatrix_det_one w
  rw [Matrix.det_fin_two, h.1, h.2] at hdet
  norm_num at hdet

private def indexedCuspForward : Monoid.CoprodI DeltaFactor :=
  (Monoid.CoprodI.of : DeltaFactor false →* Monoid.CoprodI DeltaFactor)
      (Multiplicative.ofAdd (1 : ZMod 3)) *
    (Monoid.CoprodI.of : DeltaFactor true →* Monoid.CoprodI DeltaFactor)
      (Multiplicative.ofAdd (1 : ZMod 4))

private def indexedCuspBackward : Monoid.CoprodI DeltaFactor :=
  (Monoid.CoprodI.of : DeltaFactor true →* Monoid.CoprodI DeltaFactor)
      (Multiplicative.ofAdd (3 : ZMod 4)) *
    (Monoid.CoprodI.of : DeltaFactor false →* Monoid.CoprodI DeltaFactor)
      (Multiplicative.ofAdd (2 : ZMod 3))

private theorem neWord_bottomLeft_zero_classification (n : ℕ) :
    ∀ {i j : Bool} (w : Monoid.CoprodI.NeWord DeltaFactor i j),
      w.toList.length = n → neWordMatrix w 1 0 = 0 →
        (i = false ∧ j = true ∧
          ∃ m : ℕ, 0 < m ∧ w.prod = indexedCuspForward ^ m) ∨
        (i = true ∧ j = false ∧
          ∃ m : ℕ, 0 < m ∧ w.prod = indexedCuspBackward ^ m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro i j w hlength hzero
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨k, p, hkj, hwprod, hpLength⟩
      · have hmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod w hsingle.2.1
        have hfactorZero : factorMatrix j w.last 1 0 = 0 := by
          rw [← hmatrix]
          exact hzero
        have hij := hsingle.1
        subst i
        cases j with
        | false =>
            let a : CyclicThree := w.last
            let na := (Multiplicative.toAdd a).val
            change (quadraticOne ^ na) 1 0 = 0 at hfactorZero
            have hna_lt : na < 3 := ZMod.val_lt _
            have hna_ne : na ≠ 0 := by
              intro hna
              apply BinaryIndexedCoprod.NeWord.last_ne_one w
              change a = 1
              apply Multiplicative.toAdd.injective
              apply ZMod.val_injective 3
              change na = 0
              exact hna
            have hna : na = 1 ∨ na = 2 := by omega
            rcases hna with hna | hna
            · have hre := congrArg Zsqrtd.re hfactorZero
              norm_num [na, hna, quadraticOne, pow_two, pow_succ,
                Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hre
            · have hre := congrArg Zsqrtd.re hfactorZero
              norm_num [na, hna, quadraticOne, pow_two, pow_succ,
                Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hre
        | true =>
            let b : CyclicFour := w.last
            let nb := (Multiplicative.toAdd b).val
            change (quadraticTwo ^ nb) 1 0 = 0 at hfactorZero
            have hnb_lt : nb < 4 := ZMod.val_lt _
            have hnb_ne : nb ≠ 0 := by
              intro hnb
              apply BinaryIndexedCoprod.NeWord.last_ne_one w
              change b = 1
              apply Multiplicative.toAdd.injective
              apply ZMod.val_injective 4
              change nb = 0
              exact hnb
            have hnb : nb = 1 ∨ nb = 2 ∨ nb = 3 := by omega
            rcases hnb with hnb | hnb | hnb
            · have hre := congrArg Zsqrtd.re hfactorZero
              norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
                Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hre
            · have him := congrArg Zsqrtd.im hfactorZero
              norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
                Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at him
            · have hre := congrArg Zsqrtd.re hfactorZero
              norm_num [nb, hnb, quadraticTwo, pow_two, pow_succ,
                Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hre
      · rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last p with
          hpSingle | ⟨l, q, hlk, hpprod, hqLength⟩
        · have hik := hpSingle.1
          subst i
          have hpmatrix := neWordMatrix_eq_factorMatrix_of_singleton_prod p hpSingle.2.1
          have hwmatrix := neWordMatrix_eq_init_mul_factorMatrix w p hkj hwprod
          cases k <;> cases j
          · exact (hkj rfl).elim
          · have hpairZero :
                ((1 : Matrix (Fin 2) (Fin 2) QuadraticInteger) *
                    factorMatrix false p.last * factorMatrix true w.last) 1 0 = 0 := by
                rw [one_mul, ← hpmatrix, ← hwmatrix]
                exact hzero
            have hrow : MatrixRowsSameQuadrant
                (1 : Matrix (Fin 2) (Fin 2) QuadraticInteger) := by
              simpa [MatrixRowsBeforeFactor] using identity_rowsBeforeFactor false
            have hclassified := sameQuadrant_pair_bottomLeft_zero 1 (hrow 1)
              (Or.inr (by norm_num [Matrix.one_apply])) p.last
              (BinaryIndexedCoprod.NeWord.last_ne_one p) w.last
              (BinaryIndexedCoprod.NeWord.last_ne_one w) hpairZero
            refine Or.inl ⟨rfl, rfl, 1, by omega, ?_⟩
            rw [hwprod, hpSingle.2.1, hclassified.2.1, hclassified.2.2]
            unfold indexedCuspForward
            rfl
          · have hpairZero :
                ((1 : Matrix (Fin 2) (Fin 2) QuadraticInteger) *
                    factorMatrix true p.last * factorMatrix false w.last) 1 0 = 0 := by
                rw [one_mul, ← hpmatrix, ← hwmatrix]
                exact hzero
            have hrow : MatrixRowsOppositeQuadrant
                (1 : Matrix (Fin 2) (Fin 2) QuadraticInteger) := by
              simpa [MatrixRowsBeforeFactor] using identity_rowsBeforeFactor true
            have hclassified := oppositeQuadrant_pair_bottomLeft_zero 1 (hrow 1)
              (Or.inr (by norm_num [Matrix.one_apply])) p.last
              (BinaryIndexedCoprod.NeWord.last_ne_one p) w.last
              (BinaryIndexedCoprod.NeWord.last_ne_one w) hpairZero
            refine Or.inr ⟨rfl, rfl, 1, by omega, ?_⟩
            rw [hwprod, hpSingle.2.1, hclassified.2.1, hclassified.2.2]
            unfold indexedCuspBackward
            rfl
          · exact (hkj rfl).elim
        · have hlj : l = j := by
            cases l <;> cases k <;> cases j <;> simp_all
          subst l
          have hpmatrix := neWordMatrix_eq_init_mul_factorMatrix p q hlk hpprod
          have hwmatrix := neWordMatrix_eq_init_mul_factorMatrix w p hkj hwprod
          have hqShort : q.toList.length < n := by omega
          cases j with
          | false =>
              have hk : k = true := by cases k <;> simp_all
              subst k
              have hrow : OppositeQuadrantRow
                  (neWordMatrix q 1 0) (neWordMatrix q 1 1) := by
                have hrows := neWordMatrix_rowsForFactor q
                simpa [MatrixRowsForFactor] using hrows 1
              have hpairZero :
                  (neWordMatrix q * factorMatrix true p.last *
                      factorMatrix false w.last) 1 0 = 0 := by
                rw [← hpmatrix, ← hwmatrix]
                exact hzero
              have hclassified := oppositeQuadrant_pair_bottomLeft_zero
                (neWordMatrix q) hrow (neWordMatrix_bottomRow_ne_zero q)
                p.last (BinaryIndexedCoprod.NeWord.last_ne_one p)
                w.last (BinaryIndexedCoprod.NeWord.last_ne_one w) hpairZero
              have hqClass := ih q.toList.length hqShort q rfl hclassified.1
              rcases hqClass with hqForward | hqBackward
              · simp_all
              · rcases hqBackward with ⟨hi, hj, m, hm, hqprod⟩
                refine Or.inr ⟨hi, rfl, m + 1, by omega, ?_⟩
                rw [hwprod, hpprod, hqprod, hclassified.2.1, hclassified.2.2,
                  pow_succ]
                unfold indexedCuspBackward
                simp only [mul_assoc]
                rfl
          | true =>
              have hk : k = false := by cases k <;> simp_all
              subst k
              have hrow : SameQuadrantRow
                  (neWordMatrix q 1 0) (neWordMatrix q 1 1) := by
                have hrows := neWordMatrix_rowsForFactor q
                simpa [MatrixRowsForFactor] using hrows 1
              have hpairZero :
                  (neWordMatrix q * factorMatrix false p.last *
                      factorMatrix true w.last) 1 0 = 0 := by
                rw [← hpmatrix, ← hwmatrix]
                exact hzero
              have hclassified := sameQuadrant_pair_bottomLeft_zero
                (neWordMatrix q) hrow (neWordMatrix_bottomRow_ne_zero q)
                p.last (BinaryIndexedCoprod.NeWord.last_ne_one p)
                w.last (BinaryIndexedCoprod.NeWord.last_ne_one w) hpairZero
              have hqClass := ih q.toList.length hqShort q rfl hclassified.1
              rcases hqClass with hqForward | hqBackward
              · rcases hqForward with ⟨hi, hj, m, hm, hqprod⟩
                refine Or.inl ⟨hi, rfl, m + 1, by omega, ?_⟩
                rw [hwprod, hpprod, hqprod, hclassified.2.1, hclassified.2.2,
                  pow_succ]
                unfold indexedCuspForward
                simp only [mul_assoc]
                rfl
              · simp_all

private theorem deltaToIndexed_product_eq_indexedCuspForward :
    deltaToIndexed (g₁ * g₂) = indexedCuspForward := by
  rw [map_mul, SphereSixComplex.TriangleGroup.g₁.eq_def,
    SphereSixComplex.TriangleGroup.g₂.eq_def,
    deltaToIndexed_inl, deltaToIndexed_inr]
  rfl

private theorem indexedCuspBackward_eq_inv :
    indexedCuspBackward = indexedCuspForward⁻¹ := by
  unfold indexedCuspBackward indexedCuspForward
  rw [_root_.mul_inv_rev]
  congr 1

/-- A canonical source element with zero bottom-left entry is exactly a (possibly negative)
power of the primitive cusp word.  This is the precise vertical-stabilizer statement needed by
the fundamental-polygon classification. -/
theorem eq_zpow_product_of_deltaBottomRow_fst_eq_zero
    (g : Delta) (hc : (deltaBottomRow g).1 = 0) :
    ∃ n : ℤ, g = (g₁ * g₂) ^ n := by
  let w := deltaNormalForm g
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · refine ⟨0, ?_⟩
    simp only [zpow_zero]
    apply deltaIndexedEquiv.injective
    change deltaToIndexed g = 1
    rw [← deltaNormalForm_prod g, show deltaNormalForm g = w by rfl, hw,
      Monoid.CoprodI.Word.prod_empty]
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    have hvzero : neWordMatrix v 1 0 = 0 := by
      rw [neWordMatrix_eq_wordMatrix, hv]
      simpa [w, deltaBottomRow, wordBottomRow] using hc
    have hvclass := neWord_bottomLeft_zero_classification v.toList.length v rfl hvzero
    have hgindexed : deltaToIndexed g = v.prod := by
      calc
        deltaToIndexed g = (deltaNormalForm g).prod := (deltaNormalForm_prod g).symm
        _ = w.prod := rfl
        _ = v.toWord.prod := by rw [hv]
        _ = v.prod := rfl
    rcases hvclass with hvforward | hvbackward
    · rcases hvforward with ⟨_, _, m, _, hvprod⟩
      refine ⟨(m : ℤ), ?_⟩
      apply deltaIndexedEquiv.injective
      change deltaToIndexed g = deltaToIndexed ((g₁ * g₂) ^ (m : ℤ))
      rw [map_zpow, deltaToIndexed_product_eq_indexedCuspForward,
        hgindexed, hvprod, zpow_natCast]
    · rcases hvbackward with ⟨_, _, m, _, hvprod⟩
      refine ⟨-(m : ℤ), ?_⟩
      apply deltaIndexedEquiv.injective
      change deltaToIndexed g = deltaToIndexed ((g₁ * g₂) ^ (-(m : ℤ)))
      rw [map_zpow, deltaToIndexed_product_eq_indexedCuspForward,
        hgindexed, hvprod, indexedCuspBackward_eq_inv, _root_.zpow_neg, zpow_natCast,
        _root_.inv_pow]

/-- The zero-bottom-left form of the cusp centralizer theorem, packaged in the predicate used by
the existing polygon-side proof. -/
theorem sourceCuspCentralizerExact_of_bottomLeft
    (g : Delta) (hc : (deltaBottomRow g).1 = 0) :
    ∃ n : ℤ, g = (g₁ * g₂) ^ n :=
  eq_zpow_product_of_deltaBottomRow_fst_eq_zero g hc


end SphereSixComplex.Periods.SourceChamberTopology
