module

public import SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
public import SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingClassification
import all SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingClassification

@[expose] public section

/-!
# Rigidity of the peripheral elliptic pair

An order-three/order-four pair in `C₃ * C₄` whose product is the standard peripheral word is
the standard pair conjugated by one common power of that peripheral word.  The proof combines
free-product torsion classification with the canonical integral Fuchsian matrices.
-/

noncomputable section

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open scoped MatrixGroups

namespace SphereSixComplex.Periods.PeripheralEllipticRigidity

abbrev QSL := Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger
abbrev QPSL := Matrix.ProjectiveSpecialLinearGroup (Fin 2) QuadraticInteger

private theorem projective_eq_trace_sq {A B : QSL}
    (h : (QuotientGroup.mk' (Subgroup.center QSL)) A =
      (QuotientGroup.mk' (Subgroup.center QSL)) B) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) QuadraticInteger) ^ 2 =
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) QuadraticInteger) ^ 2 := by
  obtain ⟨z, hzcenter, hz⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := Subgroup.center QSL)).mp h
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzcenter
  change r ^ 2 = 1 at hr
  change Matrix.scalar (Fin 2) r =
    (z : Matrix (Fin 2) (Fin 2) QuadraticInteger) at hrz
  have hmat : (B : Matrix (Fin 2) (Fin 2) QuadraticInteger) =
      (A : Matrix (Fin 2) (Fin 2) QuadraticInteger) * Matrix.scalar (Fin 2) r := by
    have hzval := congrArg
      (fun T : QSL ↦ (T : Matrix (Fin 2) (Fin 2) QuadraticInteger)) hz
    change (A : Matrix (Fin 2) (Fin 2) QuadraticInteger) *
      (z : Matrix (Fin 2) (Fin 2) QuadraticInteger) =
        (B : Matrix (Fin 2) (Fin 2) QuadraticInteger) at hzval
    rw [← hrz] at hzval
    exact hzval.symm
  have htrace : Matrix.trace (B : Matrix (Fin 2) (Fin 2) QuadraticInteger) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) QuadraticInteger) * r := by
    rw [hmat]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.scalar_apply, Fin.sum_univ_succ]
    ring
  rw [htrace, mul_pow, hr, mul_one]

private def factorQSL (b : Bool) (a : BinaryIndexedCoprod.DeltaFactor b) : QSL :=
  ⟨FuchsianArithmeticTermination.factorMatrix b a, by
    cases b <;>
      simp [FuchsianArithmeticTermination.factorMatrix, Matrix.det_pow,
        FuchsianArithmetic.quadraticOne_det, FuchsianArithmetic.quadraticTwo_det]⟩

private theorem qrepr_factor (b : Bool) (a : BinaryIndexedCoprod.DeltaFactor b) :
    FuchsianArithmetic.quadraticProjectiveRepresentation
        (BinaryIndexedCoprod.indexedToDelta
          ((Monoid.CoprodI.of : BinaryIndexedCoprod.DeltaFactor b →*
            Monoid.CoprodI BinaryIndexedCoprod.DeltaFactor) a)) =
      (QuotientGroup.mk' (Subgroup.center QSL)) (factorQSL b a) := by
  cases b with
  | false =>
      change CyclicThree at a
      change FuchsianArithmetic.quadraticProjectiveRepresentation
          (Monoid.Coprod.inl a) =
        (QuotientGroup.mk' (Subgroup.center QSL))
          ⟨FuchsianArithmetic.quadraticOne ^ (Multiplicative.toAdd a).val, _⟩
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 3 := ZMod.val_lt _
      have ha : a = Multiplicative.ofAdd (n : ZMod 3) := by
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 3
        exact (ZMod.val_cast_of_lt hnlt).symm
      have hpow : Multiplicative.ofAdd (n : ZMod 3) =
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ n := by
        apply Multiplicative.toAdd.injective
        simp
      rw [ha]
      have hfactor : factorQSL false (Multiplicative.ofAdd (n : ZMod 3)) =
          FuchsianArithmetic.quadraticOneSL ^ n := by
        apply Subtype.ext
        change FuchsianArithmetic.quadraticOne ^
            (Multiplicative.toAdd (Multiplicative.ofAdd (n : ZMod 3))).val =
          FuchsianArithmetic.quadraticOne ^ n
        rw [toAdd_ofAdd, ZMod.val_cast_of_lt hnlt]
      have hmain : FuchsianArithmetic.quadraticProjectiveRepresentation
            (Monoid.Coprod.inl (Multiplicative.ofAdd (n : ZMod 3))) =
          (QuotientGroup.mk' (Subgroup.center QSL))
            (FuchsianArithmetic.quadraticOneSL ^ n) := by
        rw [hpow]
        rw [map_pow (Monoid.Coprod.inl : CyclicThree →* Delta), map_pow,
          FuchsianArithmetic.quadraticProjectiveRepresentation_inl_generator]
        change ((QuotientGroup.mk' (Subgroup.center QSL))
            FuchsianArithmetic.quadraticOneSL) ^ n = _
        rw [← map_pow]
      exact hmain.trans (congrArg
        (QuotientGroup.mk' (Subgroup.center QSL)) hfactor.symm)

  | true =>
      change CyclicFour at a
      change FuchsianArithmetic.quadraticProjectiveRepresentation
          (Monoid.Coprod.inr a) =
        (QuotientGroup.mk' (Subgroup.center QSL))
          ⟨FuchsianArithmetic.quadraticTwo ^ (Multiplicative.toAdd a).val, _⟩
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 4 := ZMod.val_lt _
      have ha : a = Multiplicative.ofAdd (n : ZMod 4) := by
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 4
        exact (ZMod.val_cast_of_lt hnlt).symm
      have hpow : Multiplicative.ofAdd (n : ZMod 4) =
          (Multiplicative.ofAdd (1 : ZMod 4)) ^ n := by
        apply Multiplicative.toAdd.injective
        simp
      rw [ha]
      have hfactor : factorQSL true (Multiplicative.ofAdd (n : ZMod 4)) =
          FuchsianArithmetic.quadraticTwoSL ^ n := by
        apply Subtype.ext
        change FuchsianArithmetic.quadraticTwo ^
            (Multiplicative.toAdd (Multiplicative.ofAdd (n : ZMod 4))).val =
          FuchsianArithmetic.quadraticTwo ^ n
        rw [toAdd_ofAdd, ZMod.val_cast_of_lt hnlt]
      have hmain : FuchsianArithmetic.quadraticProjectiveRepresentation
            (Monoid.Coprod.inr (Multiplicative.ofAdd (n : ZMod 4))) =
          (QuotientGroup.mk' (Subgroup.center QSL))
            (FuchsianArithmetic.quadraticTwoSL ^ n) := by
        rw [hpow]
        rw [map_pow (Monoid.Coprod.inr : CyclicFour →* Delta), map_pow,
          FuchsianArithmetic.quadraticProjectiveRepresentation_inr_generator]
        change ((QuotientGroup.mk' (Subgroup.center QSL))
            FuchsianArithmetic.quadraticTwoSL) ^ n = _
        rw [← map_pow]
      exact hmain.trans (congrArg
        (QuotientGroup.mk' (Subgroup.center QSL)) hfactor.symm)

private def wordQSL (w : Monoid.CoprodI.Word BinaryIndexedCoprod.DeltaFactor) : QSL :=
  ⟨FuchsianArithmeticTermination.wordMatrix w,
    SphereSixComplex.Periods.SourceChamberTopology.wordMatrix_det_one w⟩

private theorem qrepr_word
    (w : Monoid.CoprodI.Word BinaryIndexedCoprod.DeltaFactor) :
    FuchsianArithmetic.quadraticProjectiveRepresentation
        (BinaryIndexedCoprod.indexedToDelta w.prod) =
      (QuotientGroup.mk' (Subgroup.center QSL)) (wordQSL w) := by
  induction w using Monoid.CoprodI.Word.consRecOn with
  | empty =>
      change FuchsianArithmetic.quadraticProjectiveRepresentation
          (BinaryIndexedCoprod.indexedToDelta 1) =
        (QuotientGroup.mk' (Subgroup.center QSL)) 1
      rw [map_one, map_one, map_one]
  | cons i a w hfirst hone ih =>
      rw [Monoid.CoprodI.Word.prod_cons, map_mul, map_mul, qrepr_factor, ih]
      rw [← map_mul]
      congr 1

private def deltaQSL (g : Delta) : QSL := wordQSL (BinaryIndexedCoprod.deltaNormalForm g)

private theorem qrepr_deltaQSL (g : Delta) :
    FuchsianArithmetic.quadraticProjectiveRepresentation g =
      (QuotientGroup.mk' (Subgroup.center QSL)) (deltaQSL g) := by
  have h := qrepr_word (BinaryIndexedCoprod.deltaNormalForm g)
  rw [BinaryIndexedCoprod.deltaNormalForm_prod] at h
  rw [show BinaryIndexedCoprod.indexedToDelta
      (BinaryIndexedCoprod.deltaToIndexed g) = g from
        DFunLike.congr_fun BinaryIndexedCoprod.indexedToDelta_comp_deltaToIndexed g] at h
  exact h

private theorem trace_conjugated_one_inv_product (C : QSL) :
    Matrix.trace
        ((C * FuchsianArithmetic.quadraticOneSL⁻¹ * C⁻¹ *
          FuchsianArithmetic.quadraticProductSL : QSL) :
            Matrix (Fin 2) (Fin 2) QuadraticInteger) =
      -1 + (1 + Zsqrtd.sqrtd) *
        (C 1 0 ^ 2 + C 1 0 * C 1 1 + C 1 1 ^ 2) := by
  have hdet := C.property
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.adjugate_fin_two, FuchsianArithmetic.quadraticOneSL,
    FuchsianArithmetic.quadraticOne,
    FuchsianArithmetic.quadraticProductSL,
    FuchsianArithmetic.quadraticProduct]
  linear_combination -hdet

private theorem trace_sq_conjugated_two (D : QSL) :
    Matrix.trace
        ((D * FuchsianArithmetic.quadraticTwoSL * D⁻¹ : QSL) :
            Matrix (Fin 2) (Fin 2) QuadraticInteger) ^ 2 = 2 := by
  change (Matrix.trace
      (((D : Matrix (Fin 2) (Fin 2) QuadraticInteger) *
          (FuchsianArithmetic.quadraticTwoSL :
            Matrix (Fin 2) (Fin 2) QuadraticInteger)) *
        ((D⁻¹ : QSL) : Matrix (Fin 2) (Fin 2) QuadraticInteger))) ^ 2 = 2
  rw [Matrix.trace_mul_cycle]
  have hinv :
      (((D⁻¹ : QSL) : Matrix (Fin 2) (Fin 2) QuadraticInteger) *
        (D : Matrix (Fin 2) (Fin 2) QuadraticInteger)) = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel D)
  rw [hinv, one_mul]
  change Zsqrtd.sqrtd ^ 2 = 2
  have hs : (Zsqrtd.sqrtd : QuadraticInteger) ^ 2 = 2 := by
    apply Zsqrtd.ext <;>
      norm_num [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  exact hs

private theorem conjugator_bottomRow_norm (c d : Delta)
    (h : c * g₁⁻¹ * c⁻¹ * (g₁ * g₂) = d * g₂ * d⁻¹) :
    let r := (BinaryIndexedCoprod.deltaNormalForm c |> wordQSL : QSL) 1 0
    let s := (BinaryIndexedCoprod.deltaNormalForm c |> wordQSL : QSL) 1 1
    r ^ 2 + r * s + s ^ 2 = 1 := by
  let C := deltaQSL c
  let D := deltaQSL d
  let q := QuotientGroup.mk' (Subgroup.center QSL)
  let M : QSL := C * FuchsianArithmetic.quadraticOneSL⁻¹ * C⁻¹ *
    FuchsianArithmetic.quadraticProductSL
  let N : QSL := D * FuchsianArithmetic.quadraticTwoSL * D⁻¹
  have hc : q C = FuchsianArithmetic.quadraticProjectiveRepresentation c := by
    exact (qrepr_deltaQSL c).symm
  have hd : q D = FuchsianArithmetic.quadraticProjectiveRepresentation d := by
    exact (qrepr_deltaQSL d).symm
  have hOne : q FuchsianArithmetic.quadraticOneSL =
      FuchsianArithmetic.quadraticProjectiveRepresentation g₁ := by
    rw [g₁.eq_def]
    exact FuchsianArithmetic.quadraticProjectiveRepresentation_inl_generator.symm
  have hTwo : q FuchsianArithmetic.quadraticTwoSL =
      FuchsianArithmetic.quadraticProjectiveRepresentation g₂ := by
    rw [g₂.eq_def]
    exact FuchsianArithmetic.quadraticProjectiveRepresentation_inr_generator.symm
  have hProductSL : FuchsianArithmetic.quadraticProductSL =
      FuchsianArithmetic.quadraticOneSL * FuchsianArithmetic.quadraticTwoSL := by
    apply Subtype.ext
    exact FuchsianArithmetic.quadraticOne_mul_quadraticTwo.symm
  have hProduct : q FuchsianArithmetic.quadraticProductSL =
      FuchsianArithmetic.quadraticProjectiveRepresentation (g₁ * g₂) := by
    rw [hProductSL, map_mul, hOne, hTwo, map_mul]
  have hproj : q M = q N := by
    calc
      q M = q C * (q FuchsianArithmetic.quadraticOneSL)⁻¹ * (q C)⁻¹ *
          q FuchsianArithmetic.quadraticProductSL := by
            simp only [M, map_mul, map_inv]
      _ = FuchsianArithmetic.quadraticProjectiveRepresentation
          (c * g₁⁻¹ * c⁻¹ * (g₁ * g₂)) := by
            rw [hc, hOne, hProduct]
            simp only [map_mul, map_inv]
      _ = FuchsianArithmetic.quadraticProjectiveRepresentation
          (d * g₂ * d⁻¹) := congrArg _ h
      _ = q D * q FuchsianArithmetic.quadraticTwoSL * (q D)⁻¹ := by
            rw [hd, hTwo]
            simp only [map_mul, map_inv]
      _ = q N := by simp only [N, map_mul, map_inv]
  have ht := projective_eq_trace_sq hproj
  change Matrix.trace
      ((C * FuchsianArithmetic.quadraticOneSL⁻¹ * C⁻¹ *
        FuchsianArithmetic.quadraticProductSL : QSL) :
          Matrix (Fin 2) (Fin 2) QuadraticInteger) ^ 2 =
    Matrix.trace
      ((D * FuchsianArithmetic.quadraticTwoSL * D⁻¹ : QSL) :
        Matrix (Fin 2) (Fin 2) QuadraticInteger) ^ 2 at ht
  rw [trace_conjugated_one_inv_product, trace_sq_conjugated_two] at ht
  change C 1 0 ^ 2 + C 1 0 * C 1 1 + C 1 1 ^ 2 = 1
  let S : QuadraticInteger := C 1 0 ^ 2 + C 1 0 * C 1 1 + C 1 1 ^ 2
  change S = 1
  have hsqrt : (Zsqrtd.sqrtd : QuadraticInteger) ^ 2 = 2 := by
    apply Zsqrtd.ext <;>
      norm_num [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  let T : QuadraticInteger := -1 + (1 + Zsqrtd.sqrtd) * S
  have htT : T ^ 2 = (2 : QuadraticInteger) := by exact ht
  have htre := congrArg Zsqrtd.re htT
  simp only [pow_two, Zsqrtd.re_mul, Zsqrtd.re_ofNat,
    Zsqrtd.im_ofNat] at htre
  norm_num at htre
  have hTreSq : T.re ^ 2 < (2 : ℤ) ^ 2 := by
    nlinarith [sq_nonneg T.im]
  have hTimSq : T.im ^ 2 < (2 : ℤ) ^ 2 := by
    nlinarith [sq_nonneg T.re]
  have hTreLower : -2 < T.re := by
    exact (abs_lt_of_sq_lt_sq' hTreSq (by norm_num)).1
  have hTreUpper : T.re < 2 := by
    exact (abs_lt_of_sq_lt_sq' hTreSq (by norm_num)).2
  have hTimLower : -2 < T.im := by
    exact (abs_lt_of_sq_lt_sq' hTimSq (by norm_num)).1
  have hTimUpper : T.im < 2 := by
    exact (abs_lt_of_sq_lt_sq' hTimSq (by norm_num)).2
  have hroot : T = Zsqrtd.sqrtd ∨
      T = -(Zsqrtd.sqrtd : QuadraticInteger) := by
    have ha : T.re = -1 ∨ T.re = 0 ∨ T.re = 1 := by omega
    have hb : T.im = -1 ∨ T.im = 0 ∨ T.im = 1 := by omega
    rcases ha with ha | ha | ha
    · rcases hb with hb | hb | hb <;> norm_num [ha, hb] at htre
    · rcases hb with hb | hb | hb
      · right
        apply Zsqrtd.ext <;> simp [ha, hb]
      · norm_num [ha, hb] at htre
      · left
        apply Zsqrtd.ext <;> simp [ha, hb]
    · rcases hb with hb | hb | hb <;> norm_num [ha, hb] at htre
  rcases hroot with hpos | hneg
  · have hmul : (1 + Zsqrtd.sqrtd) * S =
        (1 + Zsqrtd.sqrtd : QuadraticInteger) := by
      dsimp only [T] at hpos
      linear_combination hpos
    apply Zsqrtd.ext
    · have hre := congrArg Zsqrtd.re hmul
      have him := congrArg Zsqrtd.im hmul
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add,
        Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
        Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd] at hre him ⊢
      omega
    · have hre := congrArg Zsqrtd.re hmul
      have him := congrArg Zsqrtd.im hmul
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add,
        Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
        Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd] at hre him ⊢
      omega
  · have hmul : (1 + Zsqrtd.sqrtd) * S =
        (1 - Zsqrtd.sqrtd : QuadraticInteger) := by
      dsimp only [T] at hneg
      linear_combination hneg
    have hS : S = (-3 + 2 * Zsqrtd.sqrtd : QuadraticInteger) := by
      apply Zsqrtd.ext
      · have hre := congrArg Zsqrtd.re hmul
        have him := congrArg Zsqrtd.im hmul
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add,
          Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_sqrtd,
          Zsqrtd.im_sqrtd, Zsqrtd.re_neg, Zsqrtd.im_neg,
          Zsqrtd.re_ofNat, Zsqrtd.im_ofNat] at hre him ⊢
        omega
      · have hre := congrArg Zsqrtd.re hmul
        have him := congrArg Zsqrtd.im hmul
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add,
          Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_sqrtd,
          Zsqrtd.im_sqrtd, Zsqrtd.re_neg, Zsqrtd.im_neg,
          Zsqrtd.re_ofNat, Zsqrtd.im_ofNat] at hre him ⊢
        omega
    have hre := congrArg Zsqrtd.re hS
    dsimp only [S] at hre
    simp only [pow_two, Zsqrtd.re_add, Zsqrtd.re_mul,
      Zsqrtd.re_neg, Zsqrtd.re_ofNat, Zsqrtd.im_ofNat,
      Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd] at hre
    norm_num at hre
    nlinarith [sq_nonneg ((C 1 0).re + (C 1 1).re),
      sq_nonneg (C 1 0).re, sq_nonneg (C 1 1).re,
      sq_nonneg ((C 1 0).im + (C 1 1).im),
      sq_nonneg (C 1 0).im, sq_nonneg (C 1 1).im]

private theorem quadratic_row_eq_unit_cases (r s : QuadraticInteger)
    (h : r ^ 2 + r * s + s ^ 2 = 1) :
    (r, s) = (0, 1) ∨ (r, s) = (0, -1) ∨
    (r, s) = (-1, 0) ∨ (r, s) = (1, 0) ∨
    (r, s) = (1, -1) ∨ (r, s) = (-1, 1) := by
  have hre := congrArg Zsqrtd.re h
  simp only [pow_two, Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.re_one] at hre
  norm_num at hre
  have hqRe : 0 ≤ r.re ^ 2 + r.re * s.re + s.re ^ 2 := by
    nlinarith [sq_nonneg (r.re + s.re), sq_nonneg r.re, sq_nonneg s.re]
  have hqIm : 0 ≤ r.im ^ 2 + r.im * s.im + s.im ^ 2 := by
    nlinarith [sq_nonneg (r.im + s.im), sq_nonneg r.im, sq_nonneg s.im]
  have hqImZero : r.im ^ 2 + r.im * s.im + s.im ^ 2 = 0 := by
    nlinarith
  have hrIm : r.im = 0 := by
    nlinarith [sq_nonneg (r.im + s.im), sq_nonneg r.im, sq_nonneg s.im]
  have hsIm : s.im = 0 := by
    nlinarith [sq_nonneg (r.im + s.im), sq_nonneg r.im, sq_nonneg s.im]
  have hq : r.re ^ 2 + r.re * s.re + s.re ^ 2 = 1 := by
    nlinarith
  have hrSq : r.re ^ 2 < (2 : ℤ) ^ 2 := by
    nlinarith [sq_nonneg (r.re + s.re), sq_nonneg s.re]
  have hsSq : s.re ^ 2 < (2 : ℤ) ^ 2 := by
    nlinarith [sq_nonneg (r.re + s.re), sq_nonneg r.re]
  have hrLower : -2 < r.re :=
    (abs_lt_of_sq_lt_sq' hrSq (by norm_num)).1
  have hrUpper : r.re < 2 :=
    (abs_lt_of_sq_lt_sq' hrSq (by norm_num)).2
  have hsLower : -2 < s.re :=
    (abs_lt_of_sq_lt_sq' hsSq (by norm_num)).1
  have hsUpper : s.re < 2 :=
    (abs_lt_of_sq_lt_sq' hsSq (by norm_num)).2
  have hrCases : r.re = -1 ∨ r.re = 0 ∨ r.re = 1 := by omega
  have hsCases : s.re = -1 ∨ s.re = 0 ∨ s.re = 1 := by omega
  have eq_int (z : QuadraticInteger) (n : ℤ)
      (hre : z.re = n) (him : z.im = 0) : z = n := by
    apply Zsqrtd.ext <;> simp [hre, him]
  have hrCases' : r = -1 ∨ r = 0 ∨ r = 1 := by
    rcases hrCases with hr | hr | hr
    · exact Or.inl (eq_int r (-1) hr hrIm)
    · exact Or.inr (Or.inl (eq_int r 0 hr hrIm))
    · exact Or.inr (Or.inr (eq_int r 1 hr hrIm))
  have hsCases' : s = -1 ∨ s = 0 ∨ s = 1 := by
    rcases hsCases with hs | hs | hs
    · exact Or.inl (eq_int s (-1) hs hsIm)
    · exact Or.inr (Or.inl (eq_int s 0 hs hsIm))
    · exact Or.inr (Or.inr (eq_int s 1 hs hsIm))
  rcases hrCases' with rfl | rfl | rfl <;>
    rcases hsCases' with rfl | rfl | rfl <;> norm_num at hq
  all_goals norm_num

private def deltaAb : Delta →* CyclicThree × CyclicFour :=
  Monoid.Coprod.lift
    { toFun := fun a ↦ (a, 1)
      map_one' := by simp
      map_mul' := by simp }
    { toFun := fun b ↦ (1, b)
      map_one' := by simp
      map_mul' := by simp }

@[simp] private theorem deltaAb_inl (a : CyclicThree) :
    deltaAb (Monoid.Coprod.inl a) = (a, 1) := by simp [deltaAb]

@[simp] private theorem deltaAb_inr (b : CyclicFour) :
    deltaAb (Monoid.Coprod.inr b) = (1, b) := by simp [deltaAb]

@[simp] private theorem deltaAb_g1 :
    deltaAb g₁ = (Multiplicative.ofAdd (1 : ZMod 3), 1) := by
  rw [g₁.eq_def, deltaAb_inl]

@[simp] private theorem deltaAb_g2 :
    deltaAb g₂ = (1, Multiplicative.ofAdd (1 : ZMod 4)) := by
  rw [g₂.eq_def, deltaAb_inr]

private theorem elliptic_pair_eq_conjugates
    (x y : Delta) (hx3 : x ^ 3 = 1) (hy4 : y ^ 4 = 1)
    (hxy : x * y = g₁ * g₂) :
    (∃ c, x = c * g₁ * c⁻¹) ∧ (∃ d, y = d * g₂ * d⁻¹) := by
  have hx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩
  have hy : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, hy4⟩
  have hxne : x ≠ 1 := by
    intro h
    rw [h, one_mul] at hxy
    rw [hxy] at hy4
    have hab := congrArg deltaAb hy4
    simp only [map_pow, map_one, map_mul, deltaAb_g1, deltaAb_g2,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at hab
    exact (by decide :
      Multiplicative.ofAdd (1 : ZMod 3) ^ 4 ≠ 1)
        (congrArg Prod.fst hab)
  have hyne : y ≠ 1 := by
    intro h
    rw [h, mul_one] at hxy
    rw [hxy] at hx3
    have hab := congrArg deltaAb hx3
    simp only [map_pow, map_one, map_mul, deltaAb_g1, deltaAb_g2,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at hab
    exact (by decide :
      Multiplicative.ofAdd (1 : ZMod 4) ^ 3 ≠ 1)
        (congrArg Prod.snd hab)
  rcases SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_eq_conjugate_factor
      x hx hxne with ⟨c, a, ha, hxa⟩ | ⟨c, b, hb, hxb⟩ <;>
    rcases SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_eq_conjugate_factor
      y hy hyne with ⟨d, a', ha', hya⟩ | ⟨d, b', hb', hyb⟩
  · have hab := congrArg deltaAb hxy
    simp [hxa, hya] at hab
    exfalso
    exact (by decide : (1 : CyclicFour) ≠ Multiplicative.ofAdd (1 : ZMod 4)) hab.2
  · have hab := congrArg deltaAb hxy
    simp [hxa, hyb] at hab
    refine ⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩
    · rw [hxa]
      rw [hab.1, g₁.eq_def]
    · rw [hyb]
      rw [hab.2, g₂.eq_def]
  · have hab := congrArg deltaAb hxy
    simp [hxb, hya] at hab
    let retractRight : Delta →* CyclicFour :=
      Monoid.Coprod.lift 1 (MonoidHom.id CyclicFour)
    have hb3 : b ^ 3 = 1 := by
      have hpow := congrArg retractRight hx3
      simpa [hxb, retractRight] using hpow
    exfalso
    rw [hab.2] at hb3
    exact (by decide :
      Multiplicative.ofAdd (1 : ZMod 4) ^ 3 ≠ 1) hb3
  · have hab := congrArg deltaAb hxy
    simp [hxb, hyb] at hab
    exfalso
    exact (by decide : (1 : CyclicThree) ≠ Multiplicative.ofAdd (1 : ZMod 3)) hab.1

private theorem conjugated_one_eq_cusp_conjugated (c d : Delta)
    (h : c * g₁⁻¹ * c⁻¹ * (g₁ * g₂) = d * g₂ * d⁻¹) :
    ∃ n : ℤ, c * g₁ * c⁻¹ =
      (g₁ * g₂) ^ n * g₁ * ((g₁ * g₂) ^ n)⁻¹ := by
  have hnorm :
      (FuchsianArithmeticTermination.deltaBottomRow c).1 ^ 2 +
        (FuchsianArithmeticTermination.deltaBottomRow c).1 *
          (FuchsianArithmeticTermination.deltaBottomRow c).2 +
        (FuchsianArithmeticTermination.deltaBottomRow c).2 ^ 2 = 1 := by
    simpa [deltaQSL, wordQSL,
      FuchsianArithmeticTermination.deltaBottomRow,
      FuchsianArithmeticTermination.wordBottomRow] using conjugator_bottomRow_norm c d h
  rcases quadratic_row_eq_unit_cases
      (FuchsianArithmeticTermination.deltaBottomRow c).1
      (FuchsianArithmeticTermination.deltaBottomRow c).2 hnorm with
      hrow | hrow | hrow | hrow | hrow | hrow
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        FuchsianArithmeticTermination.deltaBottomRow 1 := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (0, 1) from hrow]
      decide
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c 1 (Or.inl hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        (-(FuchsianArithmeticTermination.deltaBottomRow 1).1,
          -(FuchsianArithmeticTermination.deltaBottomRow 1).2) := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (0, -1) from hrow]
      decide
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c 1 (Or.inr hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        FuchsianArithmeticTermination.deltaBottomRow g₁ := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (-1, 0) from hrow]
      decide
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c g₁ (Or.inl hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        (-(FuchsianArithmeticTermination.deltaBottomRow g₁).1,
          -(FuchsianArithmeticTermination.deltaBottomRow g₁).2) := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (1, 0) from hrow]
      decide
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c g₁ (Or.inr hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        FuchsianArithmeticTermination.deltaBottomRow (g₁ ^ 2) := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (1, -1) from hrow]
      exact SphereSixComplex.Periods.SourceChamberTopology.deltaBottomRow_gOne_sq.symm
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c (g₁ ^ 2) (Or.inl hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group
  · have hcRow : FuchsianArithmeticTermination.deltaBottomRow c =
        (-(FuchsianArithmeticTermination.deltaBottomRow (g₁ ^ 2)).1,
          -(FuchsianArithmeticTermination.deltaBottomRow (g₁ ^ 2)).2) := by
      rw [show FuchsianArithmeticTermination.deltaBottomRow c = (-1, 1) from hrow]
      rw [SphereSixComplex.Periods.SourceChamberTopology.deltaBottomRow_gOne_sq]
      norm_num
    obtain ⟨n, hc⟩ :=
      SphereSixComplex.Periods.SourceChamberTopology.eq_cusp_zpow_mul_of_bottomRow_eq_or_neg
        c (g₁ ^ 2) (Or.inr hcRow)
    refine ⟨n, ?_⟩
    rw [hc]
    group

public theorem elliptic_pair_eq_cusp_conjugates
    (x y : Delta) (hx3 : x ^ 3 = 1) (hy4 : y ^ 4 = 1)
    (hxy : x * y = g₁ * g₂) :
    ∃ n : ℤ,
      x = (g₁ * g₂) ^ n * g₁ * ((g₁ * g₂) ^ n)⁻¹ ∧
      y = (g₁ * g₂) ^ n * g₂ * ((g₁ * g₂) ^ n)⁻¹ := by
  obtain ⟨⟨c, hx⟩, ⟨d, hy⟩⟩ := elliptic_pair_eq_conjugates x y hx3 hy4 hxy
  have hrel : c * g₁⁻¹ * c⁻¹ * (g₁ * g₂) = d * g₂ * d⁻¹ := by
    calc
      c * g₁⁻¹ * c⁻¹ * (g₁ * g₂) = x⁻¹ * (g₁ * g₂) := by
        rw [hx]
        group
      _ = y := by rw [← hxy]; group
      _ = d * g₂ * d⁻¹ := hy
  obtain ⟨n, hxn⟩ := conjugated_one_eq_cusp_conjugated c d hrel
  refine ⟨n, hx.trans hxn, ?_⟩
  calc
    y = x⁻¹ * (g₁ * g₂) := by rw [← hxy]; group
    _ = ((g₁ * g₂) ^ n * g₁ * ((g₁ * g₂) ^ n)⁻¹)⁻¹ *
        (g₁ * g₂) := by rw [hx, hxn]
    _ = (g₁ * g₂) ^ n * g₁⁻¹ * ((g₁ * g₂) ^ n)⁻¹ *
        (g₁ * g₂) := by group
    _ = (g₁ * g₂) ^ n * g₁⁻¹ * (g₁ * g₂) *
        ((g₁ * g₂) ^ n)⁻¹ := by
      rw [mul_assoc ((g₁ * g₂) ^ n * g₁⁻¹),
        ((Commute.self_zpow (g₁ * g₂) n).inv_right).eq.symm,
        ← mul_assoc]
    _ = (g₁ * g₂) ^ n * g₂ * ((g₁ * g₂) ^ n)⁻¹ := by group

end SphereSixComplex.Periods.PeripheralEllipticRigidity

end
