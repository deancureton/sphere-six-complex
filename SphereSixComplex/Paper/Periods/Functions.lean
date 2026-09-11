module

public import SphereSixComplex.Paper.Periods.Invariant
public import SphereSixComplex.Prerequisites.Periods.ModularUniformization
import all SphereSixComplex.Prerequisites.Periods.ModularUniformization
import all SphereSixComplex.Paper.Periods.Matrix
import Mathlib.Geometry.Manifold.Notation

/-!
# Analytic period functions

An interface for Definition 3.1 and the existence assertion of Theorem 3.4.  The normalized
modular function is constructed from the level-one Eisenstein series and discriminant already in
Mathlib.  The paper-specific uniformization and the two additive torsor problems are retained as
explicit data rather than assumed globally.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

@[expose] public def periodValues (tau : UpperHalfPlane → UpperHalfPlane)
    (mu beta : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : Parameters where
  tau := tau z
  mu := mu z
  beta := beta z

public structure PrePeriodFunctions (U : TriangleUniformization) where
  tau : UpperHalfPlane → UpperHalfPlane
  mu : UpperHalfPlane → ℂ
  beta : UpperHalfPlane → ℂ
  tau_holomorphic : MDiff tau
  mu_holomorphic : MDiff mu
  beta_holomorphic : MDiff beta
  modular_equation : ∀ z, normalizedJ (tau z) = 1728 * U.coordinate z
  tau_at_zOne : tau U.zOne = ellipticThreeParameter
  tau_at_zTwo : tau U.zTwo = UpperHalfPlane.I
  transform_one : ∀ z,
    periodValues tau mu beta (U.sourceAction g₁ • z) =
      transformOne (periodValues tau mu beta z)
  transform_two : ∀ z,
    periodValues tau mu beta (U.sourceAction g₂ • z) =
      transformTwo (periodValues tau mu beta z)
  transform_cusp : ∀ z,
    periodValues tau mu beta (U.sourceAction g₀ • z) =
      transformCusp (periodValues tau mu beta z)
  mu_cusp_bounded : BoundedOn mu U.cuspRegion
  beta_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ beta z + (tau z : ℂ)) U.cuspRegion

/-- Equivariant analytic period functions before the final nondegeneracy shift. -/
public structure PeriodFunctions (U : TriangleUniformization) extends PrePeriodFunctions U where
  setup_inequalities : ∀ z, SetupInequalities (periodValues tau mu beta z)

namespace PeriodFunctions

variable {U : TriangleUniformization} (F : PeriodFunctions U)







public theorem tau_transform_cusp (z : UpperHalfPlane) :
    ((F.tau (U.sourceAction g₀ • z) : UpperHalfPlane) : ℂ) = F.tau z - 1 := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.tau (F.transform_cusp z)




public theorem mu_transform_cusp (z : UpperHalfPlane) :
    F.mu (U.sourceAction g₀ • z) = F.mu z := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.mu (F.transform_cusp z)

public theorem beta_transform_cusp (z : UpperHalfPlane) :
    F.beta (U.sourceAction g₀ • z) = F.beta z + 1 := by
  simpa only [periodValues, transformCusp.eq_def] using
    congrArg Parameters.beta (F.transform_cusp z)







end PeriodFunctions

@[ext]
public theorem Parameters.ext {x y : Parameters} (htau : x.tau = y.tau)
    (hmu : x.mu = y.mu) (hbeta : x.beta = y.beta) : x = y := by
  cases x
  cases y
  simp_all















end SphereSixComplex.Periods
