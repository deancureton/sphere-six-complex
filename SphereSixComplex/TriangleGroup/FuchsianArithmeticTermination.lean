module

public import SphereSixComplex.TriangleGroup.FuchsianArithmetic
public import SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
public import SphereSixComplex.TriangleGroup.FuchsianProperFreeness
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# The arithmetic termination invariant

For a quadratic-integer bottom row `(c,d)`, domination of the conjugate Euclidean norm by the
distinguished Euclidean norm is equivalent to nonnegativity of the integral coefficient
`c.re * c.im + d.re * d.im`.  This file proves that this invariant makes every fixed-point
Möbius-denominator sublevel finite.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open scoped MatrixGroups Pointwise

/-- Quadratic integers in the closed positive coefficient quadrant. -/
@[expose] public def CoeffNonnegative (x : QuadraticInteger) : Prop :=
  0 ≤ x.re ∧ 0 ≤ x.im

/-- Quadratic integers in the closed negative coefficient quadrant. -/
@[expose] public def CoeffNonpositive (x : QuadraticInteger) : Prop :=
  x.re ≤ 0 ∧ x.im ≤ 0

/-- Two row entries occupy the same closed coefficient quadrant. -/
@[expose] public def SameQuadrantRow (x y : QuadraticInteger) : Prop :=
  (CoeffNonnegative x ∧ CoeffNonnegative y) ∨
    (CoeffNonpositive x ∧ CoeffNonpositive y)

/-- Two row entries occupy opposite closed coefficient quadrants. -/
@[expose] public def OppositeQuadrantRow (x y : QuadraticInteger) : Prop :=
  (CoeffNonnegative x ∧ CoeffNonpositive y) ∨
    (CoeffNonpositive x ∧ CoeffNonnegative y)

public theorem sameQuadrantRow_mul_one {x y : QuadraticInteger}
    (h : SameQuadrantRow x y) : OppositeQuadrantRow (-(x + y)) x := by
  rcases h with h | h
  · right
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩, ⟨hx1, hx2⟩⟩
  · left
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩, ⟨hx1, hx2⟩⟩

public theorem sameQuadrantRow_mul_one_sq {x y : QuadraticInteger}
    (h : SameQuadrantRow x y) : OppositeQuadrantRow y (-(x + y)) := by
  rcases h with h | h
  · left
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨hy1, hy2⟩, ⟨by simp; omega, by simp; omega⟩⟩
  · right
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨hy1, hy2⟩, ⟨by simp; omega, by simp; omega⟩⟩

public theorem oppositeQuadrantRow_mul_two {x y : QuadraticInteger}
    (h : OppositeQuadrantRow x y) :
    SameQuadrantRow y (-x + Zsqrtd.sqrtd * y) := by
  rcases h with h | h
  · right
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨hy1, hy2⟩, ⟨by simp; omega, by simp; omega⟩⟩
  · left
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨hy1, hy2⟩, ⟨by simp; omega, by simp; omega⟩⟩

public theorem oppositeQuadrantRow_mul_two_sq {x y : QuadraticInteger}
    (h : OppositeQuadrantRow x y) :
    SameQuadrantRow (-x + Zsqrtd.sqrtd * y) (-Zsqrtd.sqrtd * x + y) := by
  rcases h with h | h
  · right
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩,
      ⟨by simp; omega, by simp; omega⟩⟩
  · left
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩,
      ⟨by simp; omega, by simp; omega⟩⟩

public theorem oppositeQuadrantRow_mul_two_cube {x y : QuadraticInteger}
    (h : OppositeQuadrantRow x y) :
    SameQuadrantRow (-Zsqrtd.sqrtd * x + y) (-x) := by
  rcases h with h | h
  · right
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩⟩
  · left
    rcases h with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    exact ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩⟩

/-- Every row of a matrix has same-quadrant entries. -/
@[expose] public def MatrixRowsSameQuadrant
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Prop :=
  ∀ i, SameQuadrantRow (M i 0) (M i 1)

/-- Every row of a matrix has opposite-quadrant entries. -/
@[expose] public def MatrixRowsOppositeQuadrant
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Prop :=
  ∀ i, OppositeQuadrantRow (M i 0) (M i 1)

public theorem rowsSame_mul_quadraticOne {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixRowsSameQuadrant M) : MatrixRowsOppositeQuadrant (M * quadraticOne) := by
  intro i
  simp [quadraticOne, Matrix.mul_apply, Fin.sum_univ_succ]
  convert sameQuadrantRow_mul_one (hM i) using 1
  all_goals ring

public theorem rowsSame_mul_quadraticOne_sq
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixRowsSameQuadrant M) : MatrixRowsOppositeQuadrant (M * quadraticOne ^ 2) := by
  intro i
  simp [quadraticOne, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  convert sameQuadrantRow_mul_one_sq (hM i) using 1
  all_goals ring

public theorem rowsOpposite_mul_quadraticTwo
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixRowsOppositeQuadrant M) : MatrixRowsSameQuadrant (M * quadraticTwo) := by
  intro i
  simp [quadraticTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  convert oppositeQuadrantRow_mul_two (hM i) using 1
  all_goals ring

public theorem rowsOpposite_mul_quadraticTwo_sq
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixRowsOppositeQuadrant M) : MatrixRowsSameQuadrant (M * quadraticTwo ^ 2) := by
  intro i
  simp [quadraticTwo, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  convert oppositeQuadrantRow_mul_two_sq (hM i) using 1
  all_goals ring

public theorem rowsOpposite_mul_quadraticTwo_cube
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixRowsOppositeQuadrant M) : MatrixRowsSameQuadrant (M * quadraticTwo ^ 3) := by
  intro i
  simp [quadraticTwo, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  convert oppositeQuadrantRow_mul_two_cube (hM i) using 1
  all_goals ring

/-- Chosen integral matrix representative of a nontrivial factor syllable. -/
@[expose] public def factorMatrix :
    (b : Bool) → DeltaFactor b → Matrix (Fin 2) (Fin 2) QuadraticInteger
  | false, a => quadraticOne ^ (Multiplicative.toAdd a).val
  | true, a => quadraticTwo ^ (Multiplicative.toAdd a).val

public theorem factorMatrix_false_rowsOpposite (a : DeltaFactor false) (ha : a ≠ 1) :
    MatrixRowsOppositeQuadrant (factorMatrix false a) := by
  let n := (Multiplicative.toAdd a).val
  have hnlt : n < 3 := ZMod.val_lt _
  have hnzero : n ≠ 0 := by
    intro hn
    apply ha
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    change n = _
    rw [hn]
    rfl
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with hn | hn
  · intro i
    fin_cases i <;>
      norm_num [factorMatrix, n, hn, MatrixRowsOppositeQuadrant, OppositeQuadrantRow,
        CoeffNonnegative, CoeffNonpositive, quadraticOne]
  · intro i
    fin_cases i <;>
      norm_num [factorMatrix, n, hn, MatrixRowsOppositeQuadrant, OppositeQuadrantRow,
        CoeffNonnegative, CoeffNonpositive, quadraticOne, pow_two,
        Matrix.mul_apply, Fin.sum_univ_succ]

public theorem factorMatrix_true_rowsSame (a : DeltaFactor true) (ha : a ≠ 1) :
    MatrixRowsSameQuadrant (factorMatrix true a) := by
  let n := (Multiplicative.toAdd a).val
  have hnlt : n < 4 := ZMod.val_lt _
  have hnzero : n ≠ 0 := by
    intro hn
    apply ha
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    change n = _
    rw [hn]
    rfl
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with hn | hn | hn
  · intro i
    fin_cases i <;>
      norm_num [factorMatrix, n, hn, MatrixRowsSameQuadrant, SameQuadrantRow,
        CoeffNonnegative, CoeffNonpositive, quadraticTwo]
  · intro i
    fin_cases i <;>
      norm_num [factorMatrix, n, hn, MatrixRowsSameQuadrant, SameQuadrantRow,
        CoeffNonnegative, CoeffNonpositive, quadraticTwo, pow_two,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;>
      norm_num [factorMatrix, n, hn, MatrixRowsSameQuadrant, SameQuadrantRow,
        CoeffNonnegative, CoeffNonpositive, quadraticTwo, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_succ]

/-- The row-quadrant state after multiplying by a syllable from the indicated factor. -/
@[expose] public def MatrixRowsForFactor
    (b : Bool) (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Prop :=
  match b with
  | false => MatrixRowsOppositeQuadrant M
  | true => MatrixRowsSameQuadrant M

/-- The row-quadrant state required before multiplying by a syllable from the indicated factor. -/
@[expose] public def MatrixRowsBeforeFactor
    (b : Bool) (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Prop :=
  match b with
  | false => MatrixRowsSameQuadrant M
  | true => MatrixRowsOppositeQuadrant M

public theorem rowsForFactor_is_rowsBeforeFactor_of_ne {b c : Bool}
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger} (hbc : b ≠ c)
    (hM : MatrixRowsForFactor b M) : MatrixRowsBeforeFactor c M := by
  cases b <;> cases c <;> simp_all [MatrixRowsForFactor, MatrixRowsBeforeFactor]

public theorem rowsBeforeFactor_mul_factorMatrix {b : Bool} (a : DeltaFactor b) (ha : a ≠ 1)
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger} (hM : MatrixRowsBeforeFactor b M) :
    MatrixRowsForFactor b (M * factorMatrix b a) := by
  cases b with
  | false =>
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 3 := ZMod.val_lt _
      have hnzero : n ≠ 0 := by
        intro hn
        apply ha
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 3
        change n = _
        rw [hn]
        rfl
      have hn : n = 1 ∨ n = 2 := by omega
      rcases hn with hn | hn
      · simpa [MatrixRowsForFactor, MatrixRowsBeforeFactor, factorMatrix, n, hn] using
          rowsSame_mul_quadraticOne hM
      · simpa [MatrixRowsForFactor, MatrixRowsBeforeFactor, factorMatrix, n, hn] using
          rowsSame_mul_quadraticOne_sq hM
  | true =>
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 4 := ZMod.val_lt _
      have hnzero : n ≠ 0 := by
        intro hn
        apply ha
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 4
        change n = _
        rw [hn]
        rfl
      have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn with hn | hn | hn
      · simpa [MatrixRowsForFactor, MatrixRowsBeforeFactor, factorMatrix, n, hn] using
          rowsOpposite_mul_quadraticTwo hM
      · simpa [MatrixRowsForFactor, MatrixRowsBeforeFactor, factorMatrix, n, hn] using
          rowsOpposite_mul_quadraticTwo_sq hM
      · simpa [MatrixRowsForFactor, MatrixRowsBeforeFactor, factorMatrix, n, hn] using
          rowsOpposite_mul_quadraticTwo_cube hM

/-- The integral matrix obtained by multiplying the syllables of a nonempty reduced word. -/
@[expose] public def neWordMatrix :
    {i j : Bool} → Monoid.CoprodI.NeWord DeltaFactor i j →
      Matrix (Fin 2) (Fin 2) QuadraticInteger
  | _, _, .singleton a _ => factorMatrix _ a
  | _, _, .append w₁ _ w₂ => neWordMatrix w₁ * neWordMatrix w₂

public theorem mul_neWordMatrix_rowsForFactor {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j)
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger} (hM : MatrixRowsBeforeFactor i M) :
    MatrixRowsForFactor j (M * neWordMatrix w) := by
  induction w generalizing M with
  | singleton a ha => exact rowsBeforeFactor_mul_factorMatrix a ha hM
  | @append i j k l w₁ hjk w₂ ih₁ ih₂ =>
      rw [neWordMatrix, ← mul_assoc]
      apply ih₂
      exact rowsForFactor_is_rowsBeforeFactor_of_ne hjk (ih₁ hM)

public theorem identity_rowsBeforeFactor (b : Bool) :
    MatrixRowsBeforeFactor b (1 : Matrix (Fin 2) (Fin 2) QuadraticInteger) := by
  cases b <;> intro i <;> fin_cases i <;>
    norm_num [MatrixRowsBeforeFactor, MatrixRowsSameQuadrant, MatrixRowsOppositeQuadrant,
      SameQuadrantRow, OppositeQuadrantRow, CoeffNonnegative, CoeffNonpositive,
      Matrix.one_apply]

public theorem neWordMatrix_rowsForFactor {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) : MatrixRowsForFactor j (neWordMatrix w) := by
  simpa using mul_neWordMatrix_rowsForFactor w (identity_rowsBeforeFactor i)

/-- The integral matrix obtained by multiplying all syllables of a reduced word. -/
@[expose] public def wordMatrix (w : Monoid.CoprodI.Word DeltaFactor) :
    Matrix (Fin 2) (Fin 2) QuadraticInteger :=
  (w.toList.map fun a ↦ factorMatrix a.1 a.2).prod

public theorem neWordMatrix_eq_wordMatrix {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) : neWordMatrix w = wordMatrix w.toWord := by
  induction w with
  | singleton a ha =>
      simp [neWordMatrix, wordMatrix, Monoid.CoprodI.NeWord.toWord,
        Monoid.CoprodI.NeWord.toList]
  | append w₁ h w₂ ih₁ ih₂ =>
      simp [neWordMatrix, wordMatrix, Monoid.CoprodI.NeWord.toWord,
        Monoid.CoprodI.NeWord.toList, ih₁, ih₂]

/-- Distinguished-real special-linear lift of one reduced-word syllable. -/
@[expose] public noncomputable def factorRealSL :
    ∀ b : Bool, DeltaFactor b → SphereSixComplex.TriangleGroup.SL2R
  | false, a => SphereSixComplex.TriangleGroup.fuchsianOneSL ^
      (Multiplicative.toAdd a).val
  | true, a => SphereSixComplex.TriangleGroup.fuchsianTwoSL ^
      (Multiplicative.toAdd a).val

public theorem factorAction_eq_fuchsianSLAction_factorRealSL
    (b : Bool) (a : DeltaFactor b) :
    FuchsianPingPong.factorAction b a =
      SphereSixComplex.TriangleGroup.fuchsianSLAction (factorRealSL b a) := by
  cases b with
  | false =>
      change CyclicThree at a
      change cyclicRepresentation 3 fuchsianOnePerm fuchsianOnePerm_pow_three a =
        fuchsianSLAction (fuchsianOneSL ^ (Multiplicative.toAdd a).val)
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 3 := ZMod.val_lt _
      have ha : a = Multiplicative.ofAdd (n : ZMod 3) := by
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 3
        change n = (n : ZMod 3).val
        rw [ZMod.val_cast_of_lt hnlt]
      have hpow : Multiplicative.ofAdd (n : ZMod 3) =
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ n := by
        apply Multiplicative.toAdd.injective
        simp
      rw [ha]
      have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (n : ZMod 3))).val = n :=
        ZMod.val_cast_of_lt hnlt
      rw [hval, hpow, map_pow, cyclicRepresentation_generator, map_pow]
      change fuchsianSLAction fuchsianOneSL ^ n = fuchsianSLAction fuchsianOneSL ^ n
      rfl
  | true =>
      change CyclicFour at a
      change cyclicRepresentation 4 fuchsianTwoPerm fuchsianTwoPerm_pow_four a =
        fuchsianSLAction (fuchsianTwoSL ^ (Multiplicative.toAdd a).val)
      let n := (Multiplicative.toAdd a).val
      have hnlt : n < 4 := ZMod.val_lt _
      have ha : a = Multiplicative.ofAdd (n : ZMod 4) := by
        apply Multiplicative.toAdd.injective
        apply ZMod.val_injective 4
        change n = (n : ZMod 4).val
        rw [ZMod.val_cast_of_lt hnlt]
      have hpow : Multiplicative.ofAdd (n : ZMod 4) =
          (Multiplicative.ofAdd (1 : ZMod 4)) ^ n := by
        apply Multiplicative.toAdd.injective
        simp
      rw [ha]
      have hval : (Multiplicative.toAdd (Multiplicative.ofAdd (n : ZMod 4))).val = n :=
        ZMod.val_cast_of_lt hnlt
      rw [hval, hpow, map_pow, cyclicRepresentation_generator, map_pow]
      change fuchsianSLAction fuchsianTwoSL ^ n = fuchsianSLAction fuchsianTwoSL ^ n
      rfl

public theorem positiveMatrix_factorMatrix (b : Bool) (a : DeltaFactor b) :
    positiveMatrix (factorMatrix b a) = (factorRealSL b a : Matrix (Fin 2) (Fin 2) ℝ) := by
  cases b with
  | false =>
      change CyclicThree at a
      change positiveMatrix (quadraticOne ^ (Multiplicative.toAdd a).val) =
        (fuchsianOneSL ^ (Multiplicative.toAdd a).val :
          SphereSixComplex.TriangleGroup.SL2R)
      rw [show positiveMatrix (quadraticOne ^ (Multiplicative.toAdd a).val) =
        positiveMatrix quadraticOne ^ (Multiplicative.toAdd a).val by
          exact Matrix.map_pow quadraticOne positiveEmbedding _]
      rw [positiveMatrix_quadraticOne]
      rfl
  | true =>
      change CyclicFour at a
      change positiveMatrix (quadraticTwo ^ (Multiplicative.toAdd a).val) =
        (fuchsianTwoSL ^ (Multiplicative.toAdd a).val :
          SphereSixComplex.TriangleGroup.SL2R)
      rw [show positiveMatrix (quadraticTwo ^ (Multiplicative.toAdd a).val) =
        positiveMatrix quadraticTwo ^ (Multiplicative.toAdd a).val by
          exact Matrix.map_pow quadraticTwo positiveEmbedding _]
      rw [positiveMatrix_quadraticTwo]
      rfl

/-- Distinguished-real special-linear lift of a nonempty reduced word. -/
@[expose] public noncomputable def neWordRealSL :
    {i j : Bool} → Monoid.CoprodI.NeWord DeltaFactor i j →
      SphereSixComplex.TriangleGroup.SL2R
  | _, _, .singleton a _ => factorRealSL _ a
  | _, _, .append w₁ _ w₂ => neWordRealSL w₁ * neWordRealSL w₂

public theorem positiveMatrix_neWordMatrix {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    positiveMatrix (neWordMatrix w) =
      (neWordRealSL w : Matrix (Fin 2) (Fin 2) ℝ) := by
  induction w with
  | singleton a ha => exact positiveMatrix_factorMatrix _ a
  | append w₁ h w₂ ih₁ ih₂ =>
      rw [neWordMatrix, neWordRealSL]
      change (neWordMatrix w₁ * neWordMatrix w₂).map positiveEmbedding = _
      rw [Matrix.map_mul]
      change positiveMatrix (neWordMatrix w₁) * positiveMatrix (neWordMatrix w₂) =
        (neWordRealSL w₁ : Matrix (Fin 2) (Fin 2) ℝ) *
          (neWordRealSL w₂ : Matrix (Fin 2) (Fin 2) ℝ)
      rw [ih₁, ih₂]

public theorem fuchsianSourceAction_indexedToDelta_prod {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    fuchsianSourceAction (indexedToDelta w.prod) = fuchsianSLAction (neWordRealSL w) := by
  induction w with
  | @singleton b a ha =>
      rw [Monoid.CoprodI.NeWord.prod_singleton]
      cases b with
      | false =>
          change CyclicThree at a
          change fuchsianSourceAction (Monoid.Coprod.inl a) =
            fuchsianSLAction (factorRealSL false a)
          rw [← FuchsianPingPong.factorAction_false]
          exact factorAction_eq_fuchsianSLAction_factorRealSL false a
      | true =>
          change CyclicFour at a
          change fuchsianSourceAction (Monoid.Coprod.inr a) =
            fuchsianSLAction (factorRealSL true a)
          rw [← FuchsianPingPong.factorAction_true]
          exact factorAction_eq_fuchsianSLAction_factorRealSL true a
  | append w₁ h w₂ ih₁ ih₂ =>
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul indexedToDelta,
        map_mul fuchsianSourceAction, ih₁, ih₂, neWordRealSL]
      exact (map_mul fuchsianSLAction (neWordRealSL w₁) (neWordRealSL w₂)).symm

/-- Every reduced-word matrix is an actual special-linear lift of the corresponding source
transformation. -/
public theorem wordMatrix_realizes_sourceAction (w : Monoid.CoprodI.Word DeltaFactor) :
    ∃ A : SphereSixComplex.TriangleGroup.SL2R,
      positiveMatrix (wordMatrix w) = (A : Matrix (Fin 2) (Fin 2) ℝ) ∧
        fuchsianSourceAction (indexedToDelta w.prod) = fuchsianSLAction A := by
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · subst w
    refine ⟨1, ?_, ?_⟩
    · ext i j
      simp [wordMatrix, Monoid.CoprodI.Word.empty, positiveMatrix, Matrix.one_apply]
    · rw [Monoid.CoprodI.Word.prod_empty, map_one, map_one]
      exact (map_one fuchsianSLAction).symm
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    subst w
    refine ⟨neWordRealSL v, ?_, fuchsianSourceAction_indexedToDelta_prod v⟩
    rw [← neWordMatrix_eq_wordMatrix]
    exact positiveMatrix_neWordMatrix v

/-- Chosen real special-linear lift of the canonical reduced-word matrix. -/
@[expose] public noncomputable def deltaRealSL (g : Delta) :
    SphereSixComplex.TriangleGroup.SL2R :=
  Classical.choose (wordMatrix_realizes_sourceAction (deltaNormalForm g))

public theorem positiveMatrix_deltaWordMatrix (g : Delta) :
    positiveMatrix (wordMatrix (deltaNormalForm g)) =
      (deltaRealSL g : Matrix (Fin 2) (Fin 2) ℝ) :=
  (Classical.choose_spec (wordMatrix_realizes_sourceAction (deltaNormalForm g))).1

public theorem fuchsianSourceAction_eq_deltaRealSL (g : Delta) :
    fuchsianSourceAction g = fuchsianSLAction (deltaRealSL g) := by
  have hg : indexedToDelta (deltaNormalForm g).prod = g := by
    rw [deltaNormalForm_prod]
    exact DFunLike.congr_fun indexedToDelta_comp_deltaToIndexed g
  exact (congrArg fuchsianSourceAction hg).symm.trans
    (Classical.choose_spec (wordMatrix_realizes_sourceAction (deltaNormalForm g))).2

public theorem deltaWordMatrix_injective : Function.Injective fun g : Delta ↦
    wordMatrix (deltaNormalForm g) := by
  intro g h hgh
  apply FuchsianPingPong.fuchsianSourceAction_injective
  rw [fuchsianSourceAction_eq_deltaRealSL, fuchsianSourceAction_eq_deltaRealSL]
  apply congrArg fuchsianSLAction
  apply Subtype.ext
  rw [← positiveMatrix_deltaWordMatrix, ← positiveMatrix_deltaWordMatrix]
  change wordMatrix (deltaNormalForm g) = wordMatrix (deltaNormalForm h) at hgh
  exact congrArg positiveMatrix hgh

/-- The total-sign cone in `ℤ[√2]`; its two integral coordinates have equal weak sign. -/
@[expose] public def InCoefficientCone (x : QuadraticInteger) : Prop :=
  0 ≤ x.re * x.im

/-- Entrywise coefficient-cone membership for a quadratic-integer matrix. -/
@[expose] public def MatrixInCoefficientCone
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Prop :=
  ∀ i j, InCoefficientCone (M i j)

public theorem inCoefficientCone_of_coeffNonnegative {x : QuadraticInteger}
    (hx : CoeffNonnegative x) : InCoefficientCone x :=
  mul_nonneg hx.1 hx.2

public theorem inCoefficientCone_of_coeffNonpositive {x : QuadraticInteger}
    (hx : CoeffNonpositive x) : InCoefficientCone x :=
  mul_nonneg_of_nonpos_of_nonpos hx.1 hx.2

public theorem conjugateEmbedding_abs_le_positiveEmbedding_abs_of_inCoefficientCone
    {x : QuadraticInteger} (hx : InCoefficientCone x) :
    |conjugateEmbedding x| ≤ |positiveEmbedding x| := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : conjugateEmbedding x ^ 2 ≤ positiveEmbedding x ^ 2 := by
    rw [positiveEmbedding_apply, conjugateEmbedding_apply]
    change 0 ≤ x.re * x.im at hx
    have hxreal : 0 ≤ (x.re : ℝ) * (x.im : ℝ) := by exact_mod_cast hx
    nlinarith
  have habssqConj : |conjugateEmbedding x| ^ 2 = conjugateEmbedding x ^ 2 :=
    sq_abs (conjugateEmbedding x)
  have habssqPos : |positiveEmbedding x| ^ 2 = positiveEmbedding x ^ 2 :=
    sq_abs (positiveEmbedding x)
  nlinarith [abs_nonneg (conjugateEmbedding x), abs_nonneg (positiveEmbedding x)]

public theorem sameQuadrantRow_inCoefficientCone {x y : QuadraticInteger}
    (h : SameQuadrantRow x y) : InCoefficientCone x ∧ InCoefficientCone y := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨inCoefficientCone_of_coeffNonnegative hx,
      inCoefficientCone_of_coeffNonnegative hy⟩
  · exact ⟨inCoefficientCone_of_coeffNonpositive hx,
      inCoefficientCone_of_coeffNonpositive hy⟩

public theorem oppositeQuadrantRow_inCoefficientCone {x y : QuadraticInteger}
    (h : OppositeQuadrantRow x y) : InCoefficientCone x ∧ InCoefficientCone y := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨inCoefficientCone_of_coeffNonnegative hx,
      inCoefficientCone_of_coeffNonpositive hy⟩
  · exact ⟨inCoefficientCone_of_coeffNonpositive hx,
      inCoefficientCone_of_coeffNonnegative hy⟩

public theorem matrixInCoefficientCone_of_rowsForFactor {b : Bool}
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger} (hM : MatrixRowsForFactor b M) :
    MatrixInCoefficientCone M := by
  cases b with
  | false =>
      intro i j
      fin_cases j
      · exact (oppositeQuadrantRow_inCoefficientCone (hM i)).1
      · exact (oppositeQuadrantRow_inCoefficientCone (hM i)).2
  | true =>
      intro i j
      fin_cases j
      · exact (sameQuadrantRow_inCoefficientCone (hM i)).1
      · exact (sameQuadrantRow_inCoefficientCone (hM i)).2

public theorem neWordMatrix_matrixInCoefficientCone {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) : MatrixInCoefficientCone (neWordMatrix w) :=
  matrixInCoefficientCone_of_rowsForFactor (neWordMatrix_rowsForFactor w)

/-- Every entry of every reduced-word representative belongs to the integral coefficient cone. -/
public theorem wordMatrix_matrixInCoefficientCone (w : Monoid.CoprodI.Word DeltaFactor) :
    MatrixInCoefficientCone (wordMatrix w) := by
  by_cases hw : w = Monoid.CoprodI.Word.empty
  · subst w
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [wordMatrix, Monoid.CoprodI.Word.empty, InCoefficientCone, Matrix.one_apply]
  · obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word w hw
    rw [← hv, ← neWordMatrix_eq_wordMatrix]
    exact neWordMatrix_matrixInCoefficientCone v

public theorem quadraticOne_matrixInCoefficientCone : MatrixInCoefficientCone quadraticOne := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [InCoefficientCone, quadraticOne]

public theorem quadraticTwo_matrixInCoefficientCone : MatrixInCoefficientCone quadraticTwo := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [InCoefficientCone, quadraticTwo]

public theorem quadraticProduct_pow_matrixInCoefficientCone (n : ℕ) :
    MatrixInCoefficientCone (quadraticProduct ^ n) := by
  rw [quadraticProduct_pow]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InCoefficientCone]
  all_goals positivity

/-- The integral mixed coefficient controlling the two real norms of a bottom row. -/
@[expose] public def mixedBottomCoefficient
    (p : QuadraticInteger × QuadraticInteger) : ℤ :=
  p.1.re * p.1.im + p.2.re * p.2.im

/-- Squared Euclidean norm of a bottom row in the distinguished embedding. -/
@[expose] public noncomputable def positiveBottomNormSq
    (p : QuadraticInteger × QuadraticInteger) : ℝ :=
  positiveEmbedding p.1 ^ 2 + positiveEmbedding p.2 ^ 2

/-- Squared Euclidean norm of a bottom row in the conjugate embedding. -/
@[expose] public noncomputable def conjugateBottomNormSq
    (p : QuadraticInteger × QuadraticInteger) : ℝ :=
  conjugateEmbedding p.1 ^ 2 + conjugateEmbedding p.2 ^ 2

/-- Exact difference between the distinguished and conjugate bottom-row norms. -/
public theorem positiveBottomNormSq_sub_conjugateBottomNormSq
    (p : QuadraticInteger × QuadraticInteger) :
    positiveBottomNormSq p - conjugateBottomNormSq p =
      4 * Real.sqrt 2 * mixedBottomCoefficient p := by
  simp only [positiveBottomNormSq, conjugateBottomNormSq, positiveEmbedding_apply,
    conjugateEmbedding_apply, mixedBottomCoefficient]
  push_cast
  ring

/-- Nonnegative mixed coefficient is exactly the required Galois-conjugate domination. -/
public theorem conjugateBottomNormSq_le_positiveBottomNormSq_iff
    (p : QuadraticInteger × QuadraticInteger) :
    conjugateBottomNormSq p ≤ positiveBottomNormSq p ↔
      0 ≤ mixedBottomCoefficient p := by
  rw [← sub_nonneg, positiveBottomNormSq_sub_conjugateBottomNormSq]
  rw [mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * Real.sqrt 2)]
  norm_cast

public theorem conjugateBottomNormSq_le_positiveBottomNormSq
    {p : QuadraticInteger × QuadraticInteger}
    (hp : 0 ≤ mixedBottomCoefficient p) :
    conjugateBottomNormSq p ≤ positiveBottomNormSq p :=
  (conjugateBottomNormSq_le_positiveBottomNormSq_iff p).2 hp

/-- The identity bottom row lies on the boundary of the arithmetic cone. -/
public theorem mixedBottomCoefficient_zero_one :
    mixedBottomCoefficient (0, 1) = 0 := by
  norm_num [mixedBottomCoefficient]

/-- The order-three generator's bottom row lies on the boundary of the arithmetic cone. -/
public theorem mixedBottomCoefficient_quadraticOne :
    mixedBottomCoefficient (quadraticOne 1 0, quadraticOne 1 1) = 0 := by
  norm_num [mixedBottomCoefficient, quadraticOne]

/-- The order-four generator's bottom row lies on the boundary of the arithmetic cone. -/
public theorem mixedBottomCoefficient_quadraticTwo :
    mixedBottomCoefficient (quadraticTwo 1 0, quadraticTwo 1 1) = 0 := by
  norm_num [mixedBottomCoefficient, quadraticTwo]

/-- Every positive cusp power has the identity bottom row and hence lies on the cone boundary. -/
public theorem quadraticProduct_pow_bottomRow (n : ℕ) :
    ((quadraticProduct ^ n) 1 0, (quadraticProduct ^ n) 1 1) = (0, 1) := by
  rw [quadraticProduct_pow]
  norm_num

public theorem mixedBottomCoefficient_quadraticProduct_pow (n : ℕ) :
    mixedBottomCoefficient ((quadraticProduct ^ n) 1 0, (quadraticProduct ^ n) 1 1) = 0 := by
  rw [quadraticProduct_pow_bottomRow]
  exact mixedBottomCoefficient_zero_one

/-- Negating both entries does not change the arithmetic cone invariant. -/
public theorem mixedBottomCoefficient_neg (p : QuadraticInteger × QuadraticInteger) :
    mixedBottomCoefficient (-p.1, -p.2) = mixedBottomCoefficient p := by
  simp [mixedBottomCoefficient]

/-- Entrywise membership implies the bottom-row invariant used for termination. -/
public theorem mixedBottomCoefficient_nonneg_of_matrixInCoefficientCone
    {M : Matrix (Fin 2) (Fin 2) QuadraticInteger}
    (hM : MatrixInCoefficientCone M) :
    0 ≤ mixedBottomCoefficient (M 1 0, M 1 1) := by
  exact add_nonneg (hM 1 0) (hM 1 1)

/-- Bottom row of the canonical integral representative of a reduced word. -/
@[expose] public def wordBottomRow (w : Monoid.CoprodI.Word DeltaFactor) :
    QuadraticInteger × QuadraticInteger :=
  (wordMatrix w 1 0, wordMatrix w 1 1)

public theorem wordBottomRow_mixedBottomCoefficient_nonnegative
    (w : Monoid.CoprodI.Word DeltaFactor) :
    0 ≤ mixedBottomCoefficient (wordBottomRow w) :=
  mixedBottomCoefficient_nonneg_of_matrixInCoefficientCone
    (wordMatrix_matrixInCoefficientCone w)

/-- Bottom row of the canonical reduced-word representative of a triangle-group element. -/
@[expose] public def deltaBottomRow (g : Delta) : QuadraticInteger × QuadraticInteger :=
  wordBottomRow (deltaNormalForm g)

public theorem indexedToDelta_deltaNormalForm_prod (g : Delta) :
    indexedToDelta (deltaNormalForm g).prod = g := by
  rw [deltaNormalForm_prod]
  exact DFunLike.congr_fun indexedToDelta_comp_deltaToIndexed g

/-- Exact imaginary-height formula for the actual source action, expressed using the canonical
quadratic-integer bottom row. -/
public theorem fuchsianSourceAction_im_eq_div_wordBottomNormSq (g : Delta)
    (z : UpperHalfPlane) :
    (fuchsianSourceAction g • z).im = z.im /
      Complex.normSq
        (positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
          positiveEmbedding (deltaBottomRow g).2) := by
  obtain ⟨A, hA, haction⟩ := wordMatrix_realizes_sourceAction (deltaNormalForm g)
  have hc := congrFun (congrFun hA (1 : Fin 2)) (0 : Fin 2)
  have hd := congrFun (congrFun hA (1 : Fin 2)) (1 : Fin 2)
  change positiveEmbedding (wordMatrix (deltaNormalForm g) 1 0) = A 1 0 at hc
  change positiveEmbedding (wordMatrix (deltaNormalForm g) 1 1) = A 1 1 at hd
  have hactiong : fuchsianSourceAction g = fuchsianSLAction A := by
    rw [← indexedToDelta_deltaNormalForm_prod g]
    exact haction
  rw [hactiong]
  change ((Matrix.SpecialLinearGroup.mapGL ℝ A) • z).im = _
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  norm_num [Matrix.SpecialLinearGroup.det_mapGL]
  congr 1
  change Complex.normSq (A 1 0 * (z : ℂ) + A 1 1) = _
  rw [← hc, ← hd]
  simp [deltaBottomRow, wordBottomRow]

/-- The arithmetic cone condition makes every denominator sublevel finite, with no separate
conjugate bound required. -/
public theorem finite_bottomRows_of_normSq_le_of_mixed_nonneg
    (z : UpperHalfPlane) (B : ℝ) :
    Set.Finite {p : QuadraticInteger × QuadraticInteger |
      Complex.normSq
          (positiveEmbedding p.1 * (z : ℂ) + positiveEmbedding p.2) ≤ B ∧
        0 ≤ mixedBottomCoefficient p} := by
  let C := (B + 1) / z.im
  let D := B + 1 + C * |z.re|
  let P := C ^ 2 + D ^ 2
  apply (finite_bottomRows_of_embeddings_bounded (max C D) (P + 1)).subset
  intro p hp
  have hpositive := positive_bottomRow_bounded_of_normSq_le z hp.1
  have hC : 0 ≤ C := (abs_nonneg _).trans hpositive.1
  have hD : 0 ≤ D := (abs_nonneg _).trans hpositive.2
  have hposNorm : positiveBottomNormSq p ≤ P := by
    have hc := abs_le.mp hpositive.1
    have hd := abs_le.mp hpositive.2
    simp only [positiveBottomNormSq]
    dsimp only [P]
    nlinarith
  have hconjNorm : conjugateBottomNormSq p ≤ P :=
    (conjugateBottomNormSq_le_positiveBottomNormSq hp.2).trans hposNorm
  have hcConjSq : conjugateEmbedding p.1 ^ 2 ≤ P := by
    dsimp only [conjugateBottomNormSq] at hconjNorm
    nlinarith [sq_nonneg (conjugateEmbedding p.2)]
  have hdConjSq : conjugateEmbedding p.2 ^ 2 ≤ P := by
    dsimp only [conjugateBottomNormSq] at hconjNorm
    nlinarith [sq_nonneg (conjugateEmbedding p.1)]
  have hcConj : |conjugateEmbedding p.1| ≤ P + 1 := by
    have hsquare : |conjugateEmbedding p.1| ^ 2 = conjugateEmbedding p.1 ^ 2 :=
      sq_abs (conjugateEmbedding p.1)
    nlinarith [sq_nonneg (|conjugateEmbedding p.1| - 1 / 2)]
  have hdConj : |conjugateEmbedding p.2| ≤ P + 1 := by
    have hsquare : |conjugateEmbedding p.2| ^ 2 = conjugateEmbedding p.2 ^ 2 :=
      sq_abs (conjugateEmbedding p.2)
    nlinarith [sq_nonneg (|conjugateEmbedding p.2| - 1 / 2)]
  change
    (|positiveEmbedding p.1| ≤ max C D ∧
      |conjugateEmbedding p.1| ≤ P + 1) ∧
      |positiveEmbedding p.2| ≤ max C D ∧
        |conjugateEmbedding p.2| ≤ P + 1
  exact ⟨⟨hpositive.1.trans (le_max_left C D), hcConj⟩,
    hpositive.2.trans (le_max_right C D), hdConj⟩

/-- For a fixed half-plane point, only finitely many canonical reduced-word bottom rows have
bounded physical denominator. -/
public theorem finite_wordBottomRows_of_normSq_le (z : UpperHalfPlane) (B : ℝ) :
    Set.Finite {p : QuadraticInteger × QuadraticInteger |
      ∃ w : Monoid.CoprodI.Word DeltaFactor, p = wordBottomRow w ∧
        Complex.normSq
            (positiveEmbedding p.1 * (z : ℂ) + positiveEmbedding p.2) ≤ B} := by
  apply (finite_bottomRows_of_normSq_le_of_mixed_nonneg z B).subset
  rintro p ⟨w, rfl, hp⟩
  exact ⟨hp, wordBottomRow_mixedBottomCoefficient_nonnegative w⟩

/-- Physical squared Möbius denominator associated to a quadratic-integer bottom row. -/
@[expose] public noncomputable def bottomRowDenominatorNormSq
    (z : UpperHalfPlane) (p : QuadraticInteger × QuadraticInteger) : ℝ :=
  Complex.normSq
    (positiveEmbedding p.1 * (z : ℂ) + positiveEmbedding p.2)

public theorem finite_deltaBottomRows_of_denominatorNormSq_le (z : UpperHalfPlane) (B : ℝ) :
    Set.Finite {p : QuadraticInteger × QuadraticInteger |
      ∃ g : Delta, p = deltaBottomRow g ∧ bottomRowDenominatorNormSq z p ≤ B} := by
  apply (finite_wordBottomRows_of_normSq_le z B).subset
  rintro p ⟨g, rfl, hg⟩
  exact ⟨deltaNormalForm g, rfl, hg⟩

public theorem bottomRowDenominatorNormSq_deltaBottomRow_pos (g : Delta)
    (z : UpperHalfPlane) : 0 < bottomRowDenominatorNormSq z (deltaBottomRow g) := by
  change 0 < Complex.normSq _
  rw [Complex.normSq_pos]
  intro hzero
  have him := fuchsianSourceAction_im_eq_div_wordBottomNormSq g z
  rw [show positiveEmbedding (deltaBottomRow g).1 * (z : ℂ) +
      positiveEmbedding (deltaBottomRow g).2 = 0 by exact hzero, Complex.normSq_zero,
    div_zero] at him
  exact (ne_of_gt (fuchsianSourceAction g • z).im_pos) him

/-- Every orbit of the explicit source action has a representative of maximal imaginary height. -/
public theorem exists_fuchsian_orbitHeightMaximal (z : UpperHalfPlane) :
    ∃ g : Delta, FuchsianTessellation.IsOrbitHeightMaximal (fuchsianSourceAction g • z) := by
  let B := bottomRowDenominatorNormSq z (deltaBottomRow 1)
  let S : Set (QuadraticInteger × QuadraticInteger) :=
    {p | ∃ g : Delta, p = deltaBottomRow g ∧ bottomRowDenominatorNormSq z p ≤ B}
  have hSfinite : S.Finite := finite_deltaBottomRows_of_denominatorNormSq_le z B
  have hSnonempty : S.Nonempty := by
    refine ⟨deltaBottomRow 1, 1, rfl, ?_⟩
    exact le_rfl
  obtain ⟨p, hpS, hpmin⟩ :=
    Set.exists_min_image S (bottomRowDenominatorNormSq z) hSfinite hSnonempty
  obtain ⟨g, rfl, hgB⟩ := hpS
  refine ⟨g, ?_⟩
  intro k
  have hdenom : bottomRowDenominatorNormSq z (deltaBottomRow g) ≤
      bottomRowDenominatorNormSq z (deltaBottomRow (k * g)) := by
    by_cases hkgB : bottomRowDenominatorNormSq z (deltaBottomRow (k * g)) ≤ B
    · apply hpmin
      exact ⟨k * g, rfl, hkgB⟩
    · exact hgB.trans (le_of_lt (lt_of_not_ge hkgB))
  rw [← mul_smul, ← map_mul]
  rw [fuchsianSourceAction_im_eq_div_wordBottomNormSq,
    fuchsianSourceAction_im_eq_div_wordBottomNormSq]
  exact (div_le_div_iff_of_pos_left z.im_pos
    (bottomRowDenominatorNormSq_deltaBottomRow_pos (k * g) z)
    (bottomRowDenominatorNormSq_deltaBottomRow_pos g z)).2 hdenom

/-- Unconditional orbit cover by the coarse Ford region. -/
public theorem exists_smul_mem_coarseFordRegion (z : UpperHalfPlane) :
    ∃ g : Delta, fuchsianSourceAction g • z ∈ FuchsianTessellation.coarseFordRegion :=
  FuchsianTessellation.exists_smul_mem_coarseFordRegion
    exists_fuchsian_orbitHeightMaximal z

public theorem exists_uniform_abs_entry_bound_of_isCompact
    {S : Set SphereSixComplex.TriangleGroup.SL2R} (hS : IsCompact S) :
    ∃ R : ℝ, ∀ A ∈ S, ∀ i j, |A i j| ≤ R := by
  have hcont (i j : Fin 2) :
      Continuous (fun A : SphereSixComplex.TriangleGroup.SL2R ↦ |A i j|) := by
    exact continuous_abs.comp
      ((show Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M i j) from
          continuous_apply_apply i j).comp
        (show Continuous (fun A : SphereSixComplex.TriangleGroup.SL2R ↦
          (A : Matrix (Fin 2) (Fin 2) ℝ)) from continuous_subtype_val))
  have hb00 := hS.bddAbove_image
    (show ContinuousOn (fun A : SphereSixComplex.TriangleGroup.SL2R ↦ |A 0 0|) S by
      exact (hcont 0 0).continuousOn)
  have hb01 := hS.bddAbove_image
    (show ContinuousOn (fun A : SphereSixComplex.TriangleGroup.SL2R ↦ |A 0 1|) S by
      exact (hcont 0 1).continuousOn)
  have hb10 := hS.bddAbove_image
    (show ContinuousOn (fun A : SphereSixComplex.TriangleGroup.SL2R ↦ |A 1 0|) S by
      exact (hcont 1 0).continuousOn)
  have hb11 := hS.bddAbove_image
    (show ContinuousOn (fun A : SphereSixComplex.TriangleGroup.SL2R ↦ |A 1 1|) S by
      exact (hcont 1 1).continuousOn)
  obtain ⟨R00, hR00⟩ := hb00
  obtain ⟨R01, hR01⟩ := hb01
  obtain ⟨R10, hR10⟩ := hb10
  obtain ⟨R11, hR11⟩ := hb11
  refine ⟨max (max R00 R01) (max R10 R11), ?_⟩
  intro A hA i j
  fin_cases i <;> fin_cases j
  · exact (hR00 ⟨A, hA, rfl⟩).trans
      ((le_max_left R00 R01).trans (le_max_left _ _))
  · exact (hR01 ⟨A, hA, rfl⟩).trans
      ((le_max_right R00 R01).trans (le_max_left _ _))
  · exact (hR10 ⟨A, hA, rfl⟩).trans
      ((le_max_left R10 R11).trans (le_max_right _ _))
  · exact (hR11 ⟨A, hA, rfl⟩).trans
      ((le_max_right R10 R11).trans (le_max_right _ _))

/-- Compact-set local finiteness for the explicit Fuchsian source action. -/
public theorem finite_fuchsianSourceAction_intersections_of_isCompact
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L) :
    Set.Finite {g : Delta |
      (((fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) '' K) ∩ L).Nonempty} := by
  let T : Set SphereSixComplex.TriangleGroup.SL2R :=
    {A | (A • K ∩ L).Nonempty}
  have hTcompact : IsCompact T := ProperSMul.isCompact_setOfPred_inter_nonempty hK hL
  obtain ⟨R, hR⟩ := exists_uniform_abs_entry_bound_of_isCompact hTcompact
  apply ((finite_matrices_of_embeddings_bounded R R).preimage
    deltaWordMatrix_injective.injOn).subset
  intro g hg
  have hAg : deltaRealSL g ∈ T := by
    change (deltaRealSL g • K ∩ L).Nonempty
    change (((fun z : UpperHalfPlane ↦ deltaRealSL g • z) '' K) ∩ L).Nonempty
    change (((fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) '' K) ∩ L).Nonempty at hg
    rw [fuchsianSourceAction_eq_deltaRealSL] at hg
    change (((fun z : UpperHalfPlane ↦ deltaRealSL g • z) '' K) ∩ L).Nonempty at hg
    exact hg
  intro i j
  have hij := congrFun (congrFun (positiveMatrix_deltaWordMatrix g) i) j
  change positiveEmbedding (wordMatrix (deltaNormalForm g) i j) = deltaRealSL g i j at hij
  have hpos : |positiveEmbedding (wordMatrix (deltaNormalForm g) i j)| ≤ R := by
    rw [hij]
    exact hR (deltaRealSL g) hAg i j
  exact ⟨hpos,
    (conjugateEmbedding_abs_le_positiveEmbedding_abs_of_inCoefficientCone
      (wordMatrix_matrixInCoefficientCone (deltaNormalForm g) i j)).trans hpos⟩

/-- The concrete source action is properly discontinuous on the upper half-plane. -/
public theorem fuchsianSourceAction_properlyDiscontinuous :
    letI := FuchsianProperFreeness.fuchsianSourceMulAction
    ProperlyDiscontinuousSMul Delta UpperHalfPlane := by
  let _ : MulAction Delta UpperHalfPlane :=
    FuchsianProperFreeness.fuchsianSourceMulAction
  constructor
  intro K L hK hL
  exact finite_fuchsianSourceAction_intersections_of_isCompact hK hL

/-- The project-level compact-set criterion follows for any uniformization whose source action is
the explicit Fuchsian action. -/
public theorem sourceActionProperlyDiscontinuous_of_eq
    {U : SphereSixComplex.Periods.TriangleUniformization}
    (hsource : U.sourceAction = fuchsianSourceAction) :
    SphereSixComplex.Geometry.GlobalTorusFamily.SourceActionProperlyDiscontinuous (U := U) := by
  intro K L hK hL
  simpa only [hsource] using finite_fuchsianSourceAction_intersections_of_isCompact hK hL

/-- Unconditional freeness of the explicit action on the regular Fuchsian locus. -/
public theorem fuchsianRegular_isCancelSMul :
    letI := FuchsianProperFreeness.fuchsianRegularMulAction
    IsCancelSMul Delta FuchsianProperFreeness.FuchsianRegularBase :=
  FuchsianProperFreeness.fuchsianRegular_isCancelSMul
    fuchsianSourceAction_properlyDiscontinuous

end SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
