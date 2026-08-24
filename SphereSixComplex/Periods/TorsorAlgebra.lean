module

public import SphereSixComplex.Periods.Functions
public import SphereSixComplex.Periods.Transformations
import all SphereSixComplex.Periods.Matrix

/-!
# Algebra of the period-function torsors

This file isolates the finite-order consistency and local-solvability calculations used for the
`mu`- and `beta`-torsors in Sections 3.2--3.3 of the paper.  It does not assert the global existence
of either holomorphic function.
-/

open UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods

/-- The order-three fractional-linear substitution for `tau`. -/
@[expose] public def tauOneStep (tau : ℂ) : ℂ :=
  (tau - 1) / tau

/-- The order-four fractional-linear substitution for `tau`. -/
@[expose] public def tauTwoStep (tau : ℂ) : ℂ :=
  -1 / tau

/-- The order-three automorphy factor of the homogeneous `mu`-equation. -/
@[expose] public def muAutomorphyOne (tau : ℂ) : ℂ :=
  -tau

/-- The order-four automorphy factor of the homogeneous `mu`-equation. -/
@[expose] public def muAutomorphyTwo (tau : ℂ) : ℂ :=
  tau

/-- The affine order-three substitution occurring in the transformation law for `mu`. -/
@[expose] public def muAffineOne (tau mu : ℂ) : ℂ :=
  (1 - mu) / tau

/-- The affine order-four substitution occurring in the transformation law for `mu`. -/
@[expose] public def muAffineTwo (tau mu : ℂ) : ℂ :=
  1 + mu / tau

/-- The inhomogeneous term in the order-three transformation law for `beta`. -/
@[expose] public def betaCocycleOne (x : Parameters) : ℂ :=
  2 - 6 * (1 - x.mu) ^ 2 / x.tau

/-- The inhomogeneous term in the order-four transformation law for `beta`. -/
@[expose] public def betaCocycleTwo (x : Parameters) : ℂ :=
  -3 - 6 * x.mu ^ 2 / x.tau

public theorem transformOne_tau (x : Parameters) :
    (transformOne x).tau = tauOneStep x.tau := by
  simp only [transformOne.eq_def, tauOneStep]

public theorem transformTwo_tau (x : Parameters) :
    (transformTwo x).tau = tauTwoStep x.tau := by
  simp only [transformTwo.eq_def, tauTwoStep]

public theorem transformOne_mu (x : Parameters) :
    (transformOne x).mu = muAffineOne x.tau x.mu := by
  simp only [transformOne.eq_def, muAffineOne]

public theorem transformTwo_mu (x : Parameters) :
    (transformTwo x).mu = muAffineTwo x.tau x.mu := by
  simp only [transformTwo.eq_def, muAffineTwo]

public theorem transformOne_beta (x : Parameters) :
    (transformOne x).beta = x.beta + betaCocycleOne x := by
  simp [transformOne, betaCocycleOne]
  ring

public theorem transformTwo_beta (x : Parameters) :
    (transformTwo x).beta = x.beta + betaCocycleTwo x := by
  simp [transformTwo, betaCocycleTwo]
  ring

public theorem betaCocycleOne_eq_sub (x : Parameters) :
    betaCocycleOne x = (transformOne x).beta - x.beta := by
  rw [transformOne_beta]
  ring

public theorem betaCocycleTwo_eq_sub (x : Parameters) :
    betaCocycleTwo x = (transformTwo x).beta - x.beta := by
  rw [transformTwo_beta]
  ring

/-- The homogeneous automorphy factors multiply to one around the order-three orbit. -/
public theorem muAutomorphyOne_cycle (tau : ℂ) (htau : tau ≠ 0) (htauOne : tau ≠ 1) :
    muAutomorphyOne tau * muAutomorphyOne (tauOneStep tau) *
      muAutomorphyOne (tauOneStep (tauOneStep tau)) = 1 := by
  simp [muAutomorphyOne, tauOneStep]
  field_simp [htau, htauOne]
  ring

/-- The homogeneous automorphy factors multiply to one around the order-four orbit. -/
public theorem muAutomorphyTwo_cycle (tau : ℂ) (htau : tau ≠ 0) :
    muAutomorphyTwo tau * muAutomorphyTwo (tauTwoStep tau) *
        muAutomorphyTwo (tauTwoStep (tauTwoStep tau)) *
      muAutomorphyTwo (tauTwoStep (tauTwoStep (tauTwoStep tau))) = 1 := by
  simp [muAutomorphyTwo, tauTwoStep]
  field_simp [htau]

/-- The affine `mu` substitution closes after the three successive `tau` substitutions. -/
public theorem muAffineOne_order_three (tau mu : ℂ) (htau : tau ≠ 0)
    (htauOne : tau ≠ 1) :
    muAffineOne (tauOneStep (tauOneStep tau))
        (muAffineOne (tauOneStep tau) (muAffineOne tau mu)) = mu := by
  let x : Parameters := ⟨tau, mu, 0⟩
  have h := congrArg Parameters.mu (transformOne_order_three x htau htauOne)
  simpa [x, transformOne, tauOneStep, muAffineOne] using h

/-- The affine `mu` substitution closes after the four successive `tau` substitutions. -/
public theorem muAffineTwo_order_four (tau mu : ℂ) (htau : tau ≠ 0) :
    muAffineTwo (tauTwoStep (tauTwoStep (tauTwoStep tau)))
        (muAffineTwo (tauTwoStep (tauTwoStep tau))
          (muAffineTwo (tauTwoStep tau) (muAffineTwo tau mu))) = mu := by
  let x : Parameters := ⟨tau, mu, 0⟩
  have h := congrArg Parameters.mu (transformTwo_order_four x htau)
  simpa [x, transformTwo, tauTwoStep, muAffineTwo] using h

/-- The order-three `beta` increments sum to zero around a complete orbit. -/
public theorem betaCocycleOne_cycle (x : Parameters) (htau : x.tau ≠ 0)
    (htauOne : x.tau ≠ 1) :
    betaCocycleOne x + betaCocycleOne (transformOne x) +
      betaCocycleOne (transformOne (transformOne x)) = 0 := by
  have h := congrArg Parameters.beta (transformOne_order_three x htau htauOne)
  rw [betaCocycleOne_eq_sub, betaCocycleOne_eq_sub, betaCocycleOne_eq_sub]
  linear_combination h

/-- The order-four `beta` increments sum to zero around a complete orbit. -/
public theorem betaCocycleTwo_cycle (x : Parameters) (htau : x.tau ≠ 0) :
    betaCocycleTwo x + betaCocycleTwo (transformTwo x) +
        betaCocycleTwo (transformTwo (transformTwo x)) +
      betaCocycleTwo (transformTwo (transformTwo (transformTwo x))) = 0 := by
  have h := congrArg Parameters.beta (transformTwo_order_four x htau)
  rw [betaCocycleTwo_eq_sub, betaCocycleTwo_eq_sub, betaCocycleTwo_eq_sub,
    betaCocycleTwo_eq_sub]
  linear_combination h

/-- The paper's explicit local section of the affine `mu`-torsor at the order-three point. -/
@[expose] public def localMuOne (tau : ℂ) : ℂ :=
  (2 - tau) / 3

/-- The paper's explicit local section of the affine `mu`-torsor at the order-four point. -/
@[expose] public def localMuTwo (tau : ℂ) : ℂ :=
  (1 - tau) / 2

public theorem localMuOne_equivariant (tau : ℂ) (htau : tau ≠ 0) :
    localMuOne (tauOneStep tau) = muAffineOne tau (localMuOne tau) := by
  simp [localMuOne, tauOneStep, muAffineOne]
  field_simp [htau]
  ring

public theorem localMuTwo_equivariant (tau : ℂ) (htau : tau ≠ 0) :
    localMuTwo (tauTwoStep tau) = muAffineTwo tau (localMuTwo tau) := by
  simp [localMuTwo, tauTwoStep, muAffineTwo]
  field_simp [htau]
  ring

/-- A weighted orbit sum is an explicit local primitive of the order-three `beta` cocycle. -/
@[expose] public def localBetaOne (x : Parameters) : ℂ :=
  (betaCocycleOne (transformOne x) +
    2 * betaCocycleOne (transformOne (transformOne x))) / 3

/-- A weighted orbit sum is an explicit local primitive of the order-four `beta` cocycle. -/
@[expose] public def localBetaTwo (x : Parameters) : ℂ :=
  (betaCocycleTwo (transformTwo x) +
      2 * betaCocycleTwo (transformTwo (transformTwo x)) +
    3 * betaCocycleTwo (transformTwo (transformTwo (transformTwo x)))) / 4

public theorem localBetaOne_transform (x : Parameters) (htau : x.tau ≠ 0)
    (htauOne : x.tau ≠ 1) :
    localBetaOne (transformOne x) = localBetaOne x + betaCocycleOne x := by
  have hclose := transformOne_order_three x htau htauOne
  have hsum := betaCocycleOne_cycle x htau htauOne
  simp only [localBetaOne, hclose]
  linear_combination -hsum / 3

public theorem localBetaTwo_transform (x : Parameters) (htau : x.tau ≠ 0) :
    localBetaTwo (transformTwo x) = localBetaTwo x + betaCocycleTwo x := by
  have hclose := transformTwo_order_four x htau
  have hsum := betaCocycleTwo_cycle x htau
  simp only [localBetaTwo, hclose]
  linear_combination -hsum / 4

namespace PeriodFunctions

open SphereSixComplex.TriangleGroup

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The fixed-point value from `mu_at_zOne` agrees with the explicit local section. -/
public theorem mu_at_zOne_eq_localMuOne :
    F.mu U.zOne = localMuOne (F.tau U.zOne) := by
  rw [F.mu_at_zOne, F.tau_at_zOne]
  simp only [localMuOne]
  change 1 / (1 + ((UpperHalfPlane.ρ : ℂ) + 1)) = (2 - ((UpperHalfPlane.ρ : ℂ) + 1)) / 3
  have hrho := UpperHalfPlane.ρ_sq
  have hden : 1 + ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    exact UpperHalfPlane.ρ.im_pos.ne' him
  field_simp [hden]
  linear_combination hrho

/-- The fixed-point value from `mu_at_zTwo` agrees with the explicit local section. -/
public theorem mu_at_zTwo_eq_localMuTwo :
    F.mu U.zTwo = localMuTwo (F.tau U.zTwo) := by
  rw [F.mu_at_zTwo, F.tau_at_zTwo]
  change Complex.I / (Complex.I - 1) = (1 - Complex.I) / 2
  have hden : Complex.I - 1 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
  rw [div_eq_iff hden]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

/-- The order-three `beta` cocycle vanishes at the elliptic fixed point. -/
public theorem betaCocycleOne_at_zOne :
    betaCocycleOne (periodValues F.tau F.mu F.beta U.zOne) = 0 := by
  simpa [betaCocycleOne, periodValues] using F.beta_cocycle_at_zOne

/-- The order-four `beta` cocycle vanishes at the elliptic fixed point. -/
public theorem betaCocycleTwo_at_zTwo :
    betaCocycleTwo (periodValues F.tau F.mu F.beta U.zTwo) = 0 := by
  simpa [betaCocycleTwo, periodValues] using F.beta_cocycle_at_zTwo

end PeriodFunctions

end SphereSixComplex.Periods
