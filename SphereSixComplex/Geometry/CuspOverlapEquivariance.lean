/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Geometry.CuspPeriodExpansion

/-!
# Equivariance of the cusp overlap map

This file proves the exponential-coordinate calculation in Proposition 4.7(ii) of the source
paper. Componentwise exponentiation kills integral period translations and turns the linear
`B₀` part of the cusp period matrix into the monomial shear on the dense torus. The remaining
correction matrix becomes exactly the phase coefficient already constructed in
`CuspPeriodExpansion`.

The calculation is adapted from
`ComplexStructures.S6.Cusp.CuspCoordinateArithmetic` in the companion formalization. It is the
algebraic equivariance needed for the regular-to-cusp overlap; constructing the descended open
embedding and proving the full cross-piece chart compatibility remain separate geometric tasks.
-/

@[expose] public section

noncomputable section

open Matrix
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

namespace SphereSixComplex.Geometry.CuspOverlapEquivariance

open CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The period `2 * pi * I`, named to keep the overlap formulas readable. -/
public def cuspTwoPiI : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I

/-- Componentwise exponential coordinates on the dense three-torus. The first two entries are
the fibre coordinates and the last entry is the cusp coordinate. -/
public def cuspExponentialDenseTorus (s : ℂ) (zeta : Fin 2 → ℂ) : DenseTorus :=
  ![exponentialUnit (cuspTwoPiI * zeta 0),
    exponentialUnit (cuspTwoPiI * zeta 1),
    exponentialUnit (cuspTwoPiI * s)]

/-- Integral shifts disappear under the cusp exponential. -/
public theorem exp_int_mul_cuspTwoPiI (k : ℤ) :
    Complex.exp ((k : ℂ) * cuspTwoPiI) = 1 := by
  simp [cuspTwoPiI, Complex.exp_int_mul_two_pi_mul_I]

/-- The scalar cusp exponential is invariant under integral translation. -/
public theorem exp_cuspTwoPiI_add_int (z : ℂ) (k : ℤ) :
    Complex.exp (cuspTwoPiI * (z + (k : ℂ))) =
      Complex.exp (cuspTwoPiI * z) := by
  calc
    Complex.exp (cuspTwoPiI * (z + (k : ℂ))) =
        Complex.exp (cuspTwoPiI * z) *
          Complex.exp ((k : ℂ) * cuspTwoPiI) := by
      rw [show cuspTwoPiI * (z + (k : ℂ)) =
        cuspTwoPiI * z + (k : ℂ) * cuspTwoPiI by ring, Complex.exp_add]
    _ = Complex.exp (cuspTwoPiI * z) := by
      rw [exp_int_mul_cuspTwoPiI, mul_one]

/-- Exponentiating a linear period plus an integral shift produces its monomial and phase
factors. -/
public theorem exp_cuspTwoPiI_add_period_add_int
    (s c z : ℂ) (n k : ℤ) :
    Complex.exp (cuspTwoPiI * (z + (s * (n : ℂ) + c) + (k : ℂ))) =
      (Complex.exp (cuspTwoPiI * s) ^ n *
        Complex.exp (cuspTwoPiI * c)) *
        Complex.exp (cuspTwoPiI * z) := by
  calc
    Complex.exp (cuspTwoPiI * (z + (s * (n : ℂ) + c) + (k : ℂ))) =
        Complex.exp (cuspTwoPiI * (z + (s * (n : ℂ) + c))) :=
      exp_cuspTwoPiI_add_int (z + (s * (n : ℂ) + c)) k
    _ = Complex.exp (cuspTwoPiI * z) *
        Complex.exp (cuspTwoPiI * (s * (n : ℂ) + c)) := by
      rw [mul_add, Complex.exp_add]
    _ = (Complex.exp (cuspTwoPiI * s) ^ n *
          Complex.exp (cuspTwoPiI * c)) *
        Complex.exp (cuspTwoPiI * z) := by
      rw [show cuspTwoPiI * (s * (n : ℂ) + c) =
        (n : ℂ) * (cuspTwoPiI * s) + cuspTwoPiI * c by ring]
      rw [Complex.exp_add, Complex.exp_int_mul]
      ring

variable {E : EstablishedFuchsianModularParameter}
  {D : FuchsianPeriodLocalData E}

/-- Translation of a fibre coordinate by the normalized cusp period and an additional integral
period. -/
public def translatedFibreCoordinate
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (lambda k : ParameterLattice) (zeta : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i ↦ zeta i +
    (s * (shearVector lambda i : ℂ) +
      (N.correctionMatrix (cuspQ s) *ᵥ fun j ↦ (lambda j : ℂ)) i) +
    (k i : ℂ)

/-- Proposition 4.7(ii): the cusp exponential intertwines period translation with the
phase-corrected monomial shear on the dense torus. -/
public theorem cuspExponentialDenseTorus_translated
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (lambda k : ParameterLattice) (zeta : Fin 2 → ℂ) :
    cuspExponentialDenseTorus s (translatedFibreCoordinate N s lambda k zeta) =
      phaseEmbedding (N.phaseCoefficient lambda (cuspQ s)) *
        denseTorusShear lambda (cuspExponentialDenseTorus s zeta) := by
  funext i
  fin_cases i
  · apply Units.ext
    simp [cuspExponentialDenseTorus, translatedFibreCoordinate,
      phaseEmbedding, denseTorusShear, phaseCoefficient, exponentialUnit]
    rw [exp_cuspTwoPiI_add_period_add_int]
    simp only [cuspTwoPiI]
    ring_nf
  · apply Units.ext
    simp [cuspExponentialDenseTorus, translatedFibreCoordinate,
      phaseEmbedding, denseTorusShear, phaseCoefficient, exponentialUnit]
    rw [exp_cuspTwoPiI_add_period_add_int]
    simp only [cuspTwoPiI]
    ring_nf
  · apply Units.ext
    simp [cuspExponentialDenseTorus, translatedFibreCoordinate,
      phaseEmbedding, denseTorusShear, exponentialUnit]

/-- On the standard toric model, the same identity says that the exponential overlap map
intertwines period translation with the global phase-corrected fan automorphism. -/
public theorem torusEmbedding_cuspExponentialDenseTorus_translated
    (M : Model) (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (lambda k : ParameterLattice) (zeta : Fin 2 → ℂ) :
    M.torusEmbedding
        (cuspExponentialDenseTorus s (translatedFibreCoordinate N s lambda k zeta)) =
      CuspToricPhaseAction.ToricModel.phaseAction M
        (N.phaseCoefficient lambda (cuspQ s))
        (Additive.toMul (M.fanShear lambda)
          (M.torusEmbedding (cuspExponentialDenseTorus s zeta))) := by
  rw [CuspToricPhaseAction.ToricModel.phaseAction_apply,
    M.fanShear_torus, M.torusAction_torus,
    cuspExponentialDenseTorus_translated]

end SphereSixComplex.Geometry.CuspOverlapEquivariance
