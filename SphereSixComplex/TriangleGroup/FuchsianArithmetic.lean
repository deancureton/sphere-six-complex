module

public import SphereSixComplex.TriangleGroup.FuchsianTessellation
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Quadratic-integer arithmetic for the Fuchsian action

The two generator matrices have coefficients in `ℤ[√2]`.  This file constructs their two real
embeddings and proves the exact lattice-discreteness statement needed by a bottom-row termination
argument: a set of quadratic integers, or matrices over them, bounded in both embeddings is finite.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianArithmetic

open Matrix
open scoped MatrixGroups

public abbrev QuadraticInteger := Zsqrtd 2

/-- The distinguished embedding `a + b√2 ↦ a + b√2`. -/
@[expose] public noncomputable def positiveEmbedding : QuadraticInteger →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]⟩

/-- The conjugate embedding `a + b√2 ↦ a - b√2`. -/
@[expose] public noncomputable def conjugateEmbedding : QuadraticInteger →+* ℝ :=
  Zsqrtd.lift ⟨-Real.sqrt 2, by
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]⟩

@[simp]
public theorem positiveEmbedding_apply (x : QuadraticInteger) :
    positiveEmbedding x = x.re + x.im * Real.sqrt 2 := rfl

@[simp]
public theorem conjugateEmbedding_apply (x : QuadraticInteger) :
    conjugateEmbedding x = x.re - x.im * Real.sqrt 2 := by
  simp [conjugateEmbedding, Zsqrtd.lift_apply_apply]
  ring

/-- There are only finitely many integers with real absolute value below a fixed bound. -/
public theorem finite_int_abs_cast_le (R : ℝ) :
    Set.Finite {n : ℤ | |(n : ℝ)| ≤ R} := by
  apply (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset
  intro n hn
  change |(n : ℝ)| ≤ R at hn
  rw [Set.mem_Icc]
  have hn' : -R ≤ (n : ℝ) ∧ (n : ℝ) ≤ R := abs_le.mp hn
  have hceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
  constructor
  · exact_mod_cast (neg_le_neg hceil).trans hn'.1
  · exact_mod_cast hn'.2.trans hceil

/-- Coordinate-bounded subsets of `ℤ[√2]` are finite. -/
public theorem finite_of_coordinates_bounded (R S : ℝ) :
    Set.Finite {x : QuadraticInteger | |(x.re : ℝ)| ≤ R ∧ |(x.im : ℝ)| ≤ S} := by
  let A : Set ℤ := {n | |(n : ℝ)| ≤ R}
  let B : Set ℤ := {n | |(n : ℝ)| ≤ S}
  let coordinates : QuadraticInteger → ℤ × ℤ := fun x ↦ (x.re, x.im)
  have hAB : (A ×ˢ B).Finite :=
    (finite_int_abs_cast_le R).prod (finite_int_abs_cast_le S)
  have hinj : Set.InjOn coordinates (coordinates ⁻¹' (A ×ˢ B)) := by
    intro x _ y _ hxy
    apply Zsqrtd.ext
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  change (coordinates ⁻¹' (A ×ˢ B)).Finite
  exact hAB.preimage hinj

/-- Bounding both real embeddings bounds both integral coordinates. -/
public theorem coordinates_bounded_of_embeddings_bounded {x : QuadraticInteger} {R S : ℝ}
    (hpos : |positiveEmbedding x| ≤ R) (hconj : |conjugateEmbedding x| ≤ S) :
    |(x.re : ℝ)| ≤ (R + S) / 2 ∧
      |(x.im : ℝ)| ≤ (R + S) / (2 * Real.sqrt 2) := by
  have hp := abs_le.mp hpos
  have hn := abs_le.mp hconj
  rw [positiveEmbedding_apply] at hp
  rw [conjugateEmbedding_apply] at hn
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    have hden : 0 < 2 * Real.sqrt 2 := by positivity
    constructor
    · rw [show -((R + S) / (2 * Real.sqrt 2)) =
          (-(R + S)) / (2 * Real.sqrt 2) by ring]
      apply (div_le_iff₀ hden).2
      nlinarith
    · apply (le_div_iff₀ hden).2
      nlinarith

/-- Paired-embedding bounded subsets of `ℤ[√2]` are finite. -/
public theorem finite_of_embeddings_bounded (R S : ℝ) :
    Set.Finite {x : QuadraticInteger |
      |positiveEmbedding x| ≤ R ∧ |conjugateEmbedding x| ≤ S} := by
  apply (finite_of_coordinates_bounded ((R + S) / 2)
      ((R + S) / (2 * Real.sqrt 2))).subset
  intro x hx
  exact coordinates_bounded_of_embeddings_bounded hx.1 hx.2

/-- Paired-embedding bounds make the possible bottom rows finite. -/
public theorem finite_bottomRows_of_embeddings_bounded (R S : ℝ) :
    Set.Finite {p : QuadraticInteger × QuadraticInteger |
      (|positiveEmbedding p.1| ≤ R ∧ |conjugateEmbedding p.1| ≤ S) ∧
        (|positiveEmbedding p.2| ≤ R ∧ |conjugateEmbedding p.2| ≤ S)} := by
  let entries : Set QuadraticInteger :=
    {x | |positiveEmbedding x| ≤ R ∧ |conjugateEmbedding x| ≤ S}
  have hentries : entries.Finite := finite_of_embeddings_bounded R S
  change (entries ×ˢ entries).Finite
  exact hentries.prod hentries

/-- A bounded Möbius denominator at one upper-half-plane point bounds both distinguished real
coefficients of its quadratic-integer bottom row. -/
public theorem positive_bottomRow_bounded_of_normSq_le (z : UpperHalfPlane)
    {c d : QuadraticInteger} {B : ℝ}
    (hB : Complex.normSq
      (positiveEmbedding c * (z : ℂ) + positiveEmbedding d) ≤ B) :
    |positiveEmbedding c| ≤ (B + 1) / z.im ∧
      |positiveEmbedding d| ≤
        B + 1 + ((B + 1) / z.im) * |z.re| := by
  let a := positiveEmbedding c
  let b := positiveEmbedding d
  have hsq : (a * z.re + b) ^ 2 + (a * z.im) ^ 2 ≤ B := by
    simpa [a, b, pow_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] using hB
  have himsq : (a * z.im) ^ 2 ≤ B := by
    nlinarith [sq_nonneg (a * z.re + b)]
  have hresq : (a * z.re + b) ^ 2 ≤ B := by
    nlinarith [sq_nonneg (a * z.im)]
  have himabs : |a * z.im| ≤ B + 1 := by
    have habssq : |a * z.im| ^ 2 = (a * z.im) ^ 2 := sq_abs (a * z.im)
    nlinarith [sq_nonneg (|a * z.im| - 1 / 2)]
  have hreabs : |a * z.re + b| ≤ B + 1 := by
    have habssq : |a * z.re + b| ^ 2 = (a * z.re + b) ^ 2 :=
      sq_abs (a * z.re + b)
    nlinarith [sq_nonneg (|a * z.re + b| - 1 / 2)]
  have ha : |a| ≤ (B + 1) / z.im := by
    apply (le_div_iff₀ z.im_pos).2
    simpa [abs_mul, abs_of_pos z.im_pos] using himabs
  constructor
  · exact ha
  · have hmul : |a * z.re| ≤ ((B + 1) / z.im) * |z.re| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ha (abs_nonneg z.re)
    have hb : |b| ≤ |a * z.re + b| + |a * z.re| := by
      calc
        |b| = |(a * z.re + b) - a * z.re| := by ring_nf
        _ ≤ |a * z.re + b| + |a * z.re| := abs_sub _ _
    exact hb.trans (add_le_add hreabs hmul)

/-- A uniform conjugate bound turns a Möbius-denominator sublevel into a finite set of
quadratic-integer bottom rows. -/
public theorem finite_bottomRows_of_normSq_le_of_conjugate_bounded
    (z : UpperHalfPlane) (B S : ℝ) :
    Set.Finite {p : QuadraticInteger × QuadraticInteger |
      Complex.normSq
          (positiveEmbedding p.1 * (z : ℂ) + positiveEmbedding p.2) ≤ B ∧
        |conjugateEmbedding p.1| ≤ S ∧ |conjugateEmbedding p.2| ≤ S} := by
  let C := (B + 1) / z.im
  let D := B + 1 + C * |z.re|
  apply (finite_bottomRows_of_embeddings_bounded (max C D) S).subset
  intro p hp
  have hpositive := positive_bottomRow_bounded_of_normSq_le z hp.1
  change
    (|positiveEmbedding p.1| ≤ max C D ∧ |conjugateEmbedding p.1| ≤ S) ∧
      |positiveEmbedding p.2| ≤ max C D ∧ |conjugateEmbedding p.2| ≤ S
  exact ⟨⟨hpositive.1.trans (le_max_left C D), hp.2.1⟩,
    hpositive.2.trans (le_max_right C D), hp.2.2⟩

/-- The same discreteness statement, entrywise, for two-by-two matrices. -/
public theorem finite_matrices_of_embeddings_bounded (R S : ℝ) :
    Set.Finite {M : Matrix (Fin 2) (Fin 2) QuadraticInteger |
      ∀ i j, |positiveEmbedding (M i j)| ≤ R ∧
        |conjugateEmbedding (M i j)| ≤ S} := by
  let entries : Set QuadraticInteger :=
    {x | |positiveEmbedding x| ≤ R ∧ |conjugateEmbedding x| ≤ S}
  have hentries : entries.Finite := finite_of_embeddings_bounded R S
  have hrows : Set.Finite {row : Fin 2 → QuadraticInteger | ∀ j, row j ∈ entries} :=
    Set.Finite.pi' fun _ ↦ hentries
  have hmatrices : Set.Finite
      {M : Matrix (Fin 2) (Fin 2) QuadraticInteger |
        ∀ i, M i ∈ {row : Fin 2 → QuadraticInteger | ∀ j, row j ∈ entries}} :=
    Set.Finite.pi' fun _ ↦ hrows
  simpa [entries] using hmatrices

/-- The order-three generator over `ℤ[√2]`. -/
@[expose] public def quadraticOne : Matrix (Fin 2) (Fin 2) QuadraticInteger :=
  !![-1, 1; -1, 0]

/-- The order-four generator over `ℤ[√2]`, before projectivizing the central sign. -/
@[expose] public def quadraticTwo : Matrix (Fin 2) (Fin 2) QuadraticInteger :=
  !![0, -1; 1, Zsqrtd.sqrtd]

/-- The positive cusp generator over `ℤ[√2]`. -/
@[expose] public def quadraticProduct : Matrix (Fin 2) (Fin 2) QuadraticInteger :=
  !![1, 1 + Zsqrtd.sqrtd; 0, 1]

public theorem quadraticOne_det : quadraticOne.det = 1 := by
  rw [Matrix.det_fin_two]
  apply Zsqrtd.ext <;> norm_num [quadraticOne]

public theorem quadraticTwo_det : quadraticTwo.det = 1 := by
  rw [Matrix.det_fin_two]
  apply Zsqrtd.ext <;> norm_num [quadraticTwo]

public theorem quadraticProduct_det : quadraticProduct.det = 1 := by
  rw [Matrix.det_fin_two]
  apply Zsqrtd.ext <;> norm_num [quadraticProduct]

/-- Integral special-linear lift of the order-three projective generator. -/
@[expose] public def quadraticOneSL : Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger :=
  ⟨quadraticOne, quadraticOne_det⟩

/-- Integral special-linear lift of the order-four projective generator. -/
@[expose] public def quadraticTwoSL : Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger :=
  ⟨quadraticTwo, quadraticTwo_det⟩

/-- Integral special-linear lift of the positive cusp translation. -/
@[expose] public def quadraticProductSL : Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger :=
  ⟨quadraticProduct, quadraticProduct_det⟩

public theorem quadraticOne_mul_quadraticTwo :
    quadraticOne * quadraticTwo = quadraticProduct := by
  apply Matrix.ext
  intro i j
  apply Zsqrtd.ext <;> fin_cases i <;> fin_cases j <;>
    norm_num [quadraticOne, quadraticTwo, quadraticProduct, Matrix.mul_apply,
      Fin.sum_univ_succ]

public theorem quadraticOne_pow_three : quadraticOne ^ 3 = 1 := by
  apply Matrix.ext
  intro i j
  apply Zsqrtd.ext <;> fin_cases i <;> fin_cases j <;>
    norm_num [quadraticOne, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem quadraticTwo_pow_four : quadraticTwo ^ 4 = -1 := by
  apply Matrix.ext
  intro i j
  apply Zsqrtd.ext <;> fin_cases i <;> fin_cases j <;>
    norm_num [quadraticTwo, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem quadraticOneSL_pow_three : quadraticOneSL ^ 3 = 1 := by
  apply Subtype.ext
  exact quadraticOne_pow_three

public theorem quadraticTwoSL_pow_four : quadraticTwoSL ^ 4 = -1 := by
  apply Subtype.ext
  exact quadraticTwo_pow_four

public abbrev QuadraticPSL :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) QuadraticInteger

/-- Projective quadratic-integer class of the order-three generator. -/
@[expose] public def quadraticOnePSL : QuadraticPSL :=
  (QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger))) quadraticOneSL

/-- Projective quadratic-integer class of the order-four generator. -/
@[expose] public def quadraticTwoPSL : QuadraticPSL :=
  (QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger))) quadraticTwoSL

public theorem quadraticOnePSL_pow_three : quadraticOnePSL ^ 3 = 1 := by
  change ((QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger))) quadraticOneSL) ^ 3 = 1
  rw [← map_pow, quadraticOneSL_pow_three, map_one]

public theorem quadraticTwoPSL_pow_four : quadraticTwoPSL ^ 4 = 1 := by
  change ((QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) QuadraticInteger))) quadraticTwoSL) ^ 4 = 1
  rw [← map_pow, quadraticTwoSL_pow_four]
  apply (QuotientGroup.eq_one_iff (-1)).2
  rw [Subgroup.mem_center_iff]
  intro g
  simp

/-- The canonical projective representation over `ℤ[√2]`. -/
@[expose] public noncomputable def quadraticProjectiveRepresentation :
    SphereSixComplex.TriangleGroup.Delta →* QuadraticPSL :=
  Monoid.Coprod.lift
    (SphereSixComplex.TriangleGroup.cyclicRepresentation 3
      quadraticOnePSL quadraticOnePSL_pow_three)
    (SphereSixComplex.TriangleGroup.cyclicRepresentation 4
      quadraticTwoPSL quadraticTwoPSL_pow_four)

@[simp]
public theorem quadraticProjectiveRepresentation_inl_generator :
    quadraticProjectiveRepresentation
      (Monoid.Coprod.inl (Multiplicative.ofAdd 1)) = quadraticOnePSL := by
  simp [quadraticProjectiveRepresentation]

@[simp]
public theorem quadraticProjectiveRepresentation_inr_generator :
    quadraticProjectiveRepresentation
      (Monoid.Coprod.inr (Multiplicative.ofAdd 1)) = quadraticTwoPSL := by
  simp [quadraticProjectiveRepresentation]

/-- Exact quadratic-integer coefficients of every positive cusp power. -/
public theorem quadraticProduct_pow (n : ℕ) :
    quadraticProduct ^ n = !![1, n * (1 + Zsqrtd.sqrtd); 0, 1] := by
  induction n with
  | zero =>
      apply Matrix.ext
      intro i j
      apply Zsqrtd.ext <;> fin_cases i <;> fin_cases j <;> norm_num
  | succ n ih =>
      rw [pow_succ, ih]
      apply Matrix.ext
      intro i j
      apply Zsqrtd.ext <;> fin_cases i <;> fin_cases j <;>
        norm_num [quadraticProduct, Matrix.mul_apply, Fin.sum_univ_succ]
        <;> ring

/-- Apply the distinguished real embedding entrywise. -/
@[expose] public noncomputable def positiveMatrix
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Matrix (Fin 2) (Fin 2) ℝ :=
  M.map positiveEmbedding

/-- Apply the conjugate real embedding entrywise. -/
@[expose] public noncomputable def conjugateMatrix
    (M : Matrix (Fin 2) (Fin 2) QuadraticInteger) : Matrix (Fin 2) (Fin 2) ℝ :=
  M.map conjugateEmbedding

public theorem positiveMatrix_quadraticOne :
    positiveMatrix quadraticOne =
      (SphereSixComplex.TriangleGroup.fuchsianOneSL : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveMatrix, quadraticOne,
      SphereSixComplex.TriangleGroup.fuchsianOneSL, positiveEmbedding]

public theorem positiveMatrix_quadraticTwo :
    positiveMatrix quadraticTwo =
      (SphereSixComplex.TriangleGroup.fuchsianTwoSL : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveMatrix, quadraticTwo,
      SphereSixComplex.TriangleGroup.fuchsianTwoSL, positiveEmbedding]

public theorem positiveMatrix_quadraticProduct :
    positiveMatrix quadraticProduct =
      (SphereSixComplex.TriangleGroup.fuchsianProductSL : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveMatrix, quadraticProduct,
      SphereSixComplex.TriangleGroup.fuchsianProductSL, positiveEmbedding]

/-- Under conjugation, the cusp width becomes `1 - √2`; it is still a nontrivial parabolic
translation, so conjugate-entry boundedness requires a genuine word estimate. -/
public theorem conjugateMatrix_quadraticProduct :
    conjugateMatrix quadraticProduct = !![1, 1 - Real.sqrt 2; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugateMatrix, quadraticProduct, conjugateEmbedding]
  all_goals ring

/-- The conjugate cusp coefficients grow linearly as `n(1 - √2)`. -/
public theorem conjugateMatrix_quadraticProduct_pow (n : ℕ) :
    conjugateMatrix (quadraticProduct ^ n) =
      !![1, n * (1 - Real.sqrt 2); 0, 1] := by
  rw [quadraticProduct_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugateMatrix, conjugateEmbedding]
  all_goals ring

end SphereSixComplex.TriangleGroup.FuchsianArithmetic
