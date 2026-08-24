module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Two-chart torsor algebra on the projective line

This file proves the Laurent-polynomial Cech splitting behind the standard two-chart calculations
of `H¹(P¹, O) = 0` and `H¹(P¹, O(-1)) = 0`.  It is the algebraic standard-cover model of
the global torsor-gluing step in Sections 3.2--3.3 of the paper.  The corresponding theorem for
arbitrary holomorphic functions on `ℂ×` additionally requires analytic Laurent-series theory.
-/

open Polynomial
open scoped LaurentPolynomial

noncomputable section

namespace SphereSixComplex.Periods.ProjectiveLineCech

open LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- Restriction from the affine chart at zero to its Laurent-polynomial overlap. -/
@[expose] public def restrictZero (p : R[X]) : R[T;T⁻¹] :=
  p.toLaurent

/-- Restriction from the affine chart at infinity for `O(-1)`, expressed in the zero-chart frame. -/
@[expose] public def restrictInfinityNegOne (p : R[X]) : R[T;T⁻¹] :=
  T (-1) * invert p.toLaurent

/-- Restriction from the affine chart at infinity for the structure sheaf. -/
@[expose] public def restrictInfinityZero (p : R[X]) : R[T;T⁻¹] :=
  invert p.toLaurent

/-- The nonnegative Laurent terms, regarded as a polynomial on the zero chart. -/
@[expose] public def zeroPart (p : R[T;T⁻¹]) : R[X] :=
  trunc p

/-- The negative Laurent terms, reindexed as a polynomial in the infinity coordinate. -/
@[expose] public def infinityPartNegOne (p : R[T;T⁻¹]) : R[X] :=
  trunc (invert (p * T 1))

/-- Every Laurent polynomial splits canonically into a zero-chart polynomial and an
`O(-1)` infinity-chart polynomial. -/
public theorem eq_restrictZero_add_restrictInfinityNegOne (p : R[T;T⁻¹]) :
    p = restrictZero (zeroPart p) + restrictInfinityNegOne (infinityPartNegOne p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      calc
        p + q =
            (restrictZero (zeroPart p) + restrictInfinityNegOne (infinityPartNegOne p)) +
              (restrictZero (zeroPart q) +
                restrictInfinityNegOne (infinityPartNegOne q)) :=
          congrArg₂ (fun a b ↦ a + b) hp hq
        _ = restrictZero (zeroPart (p + q)) +
            restrictInfinityNegOne (infinityPartNegOne (p + q)) := by
          simp only [zeroPart, infinityPartNegOne, restrictZero, restrictInfinityNegOne,
            map_add, add_mul, mul_add]
          abel
  | C_mul_T n a =>
      rcases n with n | n
      · simp [zeroPart, infinityPartNegOne, restrictZero, restrictInfinityNegOne]
        simp [show ¬ (n : ℤ) ≤ -1 by omega]
      · simp [zeroPart, infinityPartNegOne, restrictZero, restrictInfinityNegOne,
          Int.negSucc_eq]
        simp [show ¬ (n : ℤ) ≤ -1 by omega]
        congr 2
        omega

/-- The standard two-chart Cech differential for `O(-1)`. -/
@[expose] public def cechDifferentialNegOne (p : R[X] × R[X]) : R[T;T⁻¹] :=
  restrictZero p.1 - restrictInfinityNegOne p.2

/-- The standard two-chart Cech differential for the structure sheaf. -/
@[expose] public def cechDifferentialZero (p : R[X] × R[X]) : R[T;T⁻¹] :=
  restrictZero p.1 - restrictInfinityZero p.2

/-- Laurent-polynomial Cech exactness for `O(-1)` on the standard cover of the projective line. -/
public theorem cechDifferentialNegOne_surjective :
    Function.Surjective (cechDifferentialNegOne : R[X] × R[X] → R[T;T⁻¹]) := by
  intro p
  refine ⟨(zeroPart p, -infinityPartNegOne p), ?_⟩
  change restrictZero (zeroPart p) - restrictInfinityNegOne (-infinityPartNegOne p) = p
  simp only [restrictInfinityNegOne, map_neg, mul_neg, sub_neg_eq_add]
  exact (eq_restrictZero_add_restrictInfinityNegOne p).symm

/-- Every Laurent polynomial is also a structure-sheaf Cech coboundary. -/
public theorem cechDifferentialZero_surjective :
    Function.Surjective (cechDifferentialZero : R[X] × R[X] → R[T;T⁻¹]) := by
  intro p
  obtain ⟨⟨f, g⟩, h⟩ := cechDifferentialNegOne_surjective (R := R) p
  refine ⟨(f, X * g), ?_⟩
  change restrictZero f - restrictInfinityZero (X * g) = p
  have hinfinity : restrictInfinityZero (X * g) = restrictInfinityNegOne g := by
    simp [restrictInfinityZero, restrictInfinityNegOne, T_mul]
  rw [hinfinity]
  simpa [cechDifferentialNegOne] using h

/-- Explicit local corrections glue any Laurent-polynomial `O(-1)` overlap cocycle. -/
public theorem exists_negOne_local_corrections (c : R[T;T⁻¹]) :
    ∃ fZero fInfinity : R[X],
      restrictZero fZero - restrictInfinityNegOne fInfinity = c := by
  simpa [cechDifferentialNegOne] using cechDifferentialNegOne_surjective (R := R) c

/-- Explicit local corrections glue any Laurent-polynomial structure-sheaf overlap cocycle. -/
public theorem exists_zero_local_corrections (c : R[T;T⁻¹]) :
    ∃ fZero fInfinity : R[X],
      restrictZero fZero - restrictInfinityZero fInfinity = c := by
  simpa [cechDifferentialZero] using cechDifferentialZero_surjective (R := R) c

/-- Local `O(-1)` torsor sections with Laurent-polynomial mismatch can be corrected to agree. -/
public theorem exists_compatible_negOne_adjustments (sZero sInfinity : R[T;T⁻¹]) :
    ∃ fZero fInfinity : R[X],
      sZero - restrictZero fZero = sInfinity - restrictInfinityNegOne fInfinity := by
  obtain ⟨fZero, fInfinity, h⟩ :=
    exists_negOne_local_corrections (R := R) (sZero - sInfinity)
  refine ⟨fZero, fInfinity, ?_⟩
  apply sub_eq_zero.mp
  calc
    (sZero - restrictZero fZero) -
        (sInfinity - restrictInfinityNegOne fInfinity) =
      (sZero - sInfinity) -
        (restrictZero fZero - restrictInfinityNegOne fInfinity) := by abel
    _ = 0 := sub_eq_zero.mpr h.symm

/-- Local structure-sheaf torsor sections with Laurent-polynomial mismatch can be corrected to
agree. -/
public theorem exists_compatible_zero_adjustments (sZero sInfinity : R[T;T⁻¹]) :
    ∃ fZero fInfinity : R[X],
      sZero - restrictZero fZero = sInfinity - restrictInfinityZero fInfinity := by
  obtain ⟨fZero, fInfinity, h⟩ :=
    exists_zero_local_corrections (R := R) (sZero - sInfinity)
  refine ⟨fZero, fInfinity, ?_⟩
  apply sub_eq_zero.mp
  calc
    (sZero - restrictZero fZero) - (sInfinity - restrictInfinityZero fInfinity) =
      (sZero - sInfinity) - (restrictZero fZero - restrictInfinityZero fInfinity) := by abel
    _ = 0 := sub_eq_zero.mpr h.symm

end SphereSixComplex.Periods.ProjectiveLineCech
