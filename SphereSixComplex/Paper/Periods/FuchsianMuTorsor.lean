module

public import SphereSixComplex.Paper.Periods.FuchsianModularLift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Complex.RemovableSingularity
public import SphereSixComplex.Paper.Periods.TorsorAlgebra
import all SphereSixComplex.Paper.Periods.FuchsianUniformizationBridge

/-!
# Local sections of the affine `mu` torsor

The explicit sections at the two elliptic points and the cusp satisfy the required
holomorphicity and affine transformation laws.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : FuchsianModularLift)

/-- The explicit local affine-torsor section at the order-three point. -/
@[expose] public def ellipticMuOne (z : UpperHalfPlane) : ℂ :=
  localMuOne (E.modularParameter.tau z)

/-- The explicit local affine-torsor section at the order-four point. -/
@[expose] public def ellipticMuTwo (z : UpperHalfPlane) : ℂ :=
  localMuTwo (E.modularParameter.tau z)

/-- The distinguished local section at the cusp. -/
@[expose] public def cuspLocalMu
    (_E : FuchsianModularLift) (_z : UpperHalfPlane) : ℂ := 0

public theorem tau_coe_ne_one (z : UpperHalfPlane) :
    (E.modularParameter.tau z : ℂ) ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him
  exact (E.modularParameter.tau z).im_pos.ne' him

/-- The order-three affine substitution closes around every explicit source orbit. -/
public theorem muAffineOne_closes (z : UpperHalfPlane) (mu : ℂ) :
    muAffineOne
        (tauOneStep (tauOneStep (E.modularParameter.tau z)))
        (muAffineOne (tauOneStep (E.modularParameter.tau z))
          (muAffineOne (E.modularParameter.tau z) mu)) = mu :=
  muAffineOne_order_three _ _ (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)

/-- The order-four affine substitution closes around every explicit source orbit. -/
public theorem muAffineTwo_closes (z : UpperHalfPlane) (mu : ℂ) :
    muAffineTwo
        (tauTwoStep (tauTwoStep (tauTwoStep (E.modularParameter.tau z))))
        (muAffineTwo (tauTwoStep (tauTwoStep (E.modularParameter.tau z)))
          (muAffineTwo (tauTwoStep (E.modularParameter.tau z))
            (muAffineTwo (E.modularParameter.tau z) mu))) = mu :=
  muAffineTwo_order_four _ _ (E.modularParameter.tau z).ne_zero

private theorem tau_transform_one_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₁ • z) : UpperHalfPlane) : ℂ) =
      tauOneStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_one z)).trans (rhoTauReal_g₁_smul _)

private theorem tau_transform_two_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
      tauTwoStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_two z)).trans (rhoTauReal_g₂_smul _)

private theorem tau_coe_holomorphic :
    MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
  intro z
  exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
    (E.modularParameter.tau_holomorphic z)

/-- The order-three local affine section is holomorphic. -/
public theorem ellipticMuOne_holomorphic : MDiff (ellipticMuOne E) := by
  exact (mdifferentiable_const.sub (tau_coe_holomorphic E)).div mdifferentiable_const
    (by norm_num)

/-- The order-four local affine section is holomorphic. -/
public theorem ellipticMuTwo_holomorphic : MDiff (ellipticMuTwo E) := by
  exact (mdifferentiable_const.sub (tau_coe_holomorphic E)).div mdifferentiable_const
    (by norm_num)

/-- The first explicit local section satisfies the order-three affine law. -/
public theorem ellipticMuOne_transform (z : UpperHalfPlane) :
    ellipticMuOne E (fuchsianSourceAction g₁ • z) =
      (1 - ellipticMuOne E z) / (E.modularParameter.tau z : ℂ) := by
  rw [ellipticMuOne, ellipticMuOne, tau_transform_one_coe]
  exact localMuOne_equivariant _ (E.modularParameter.tau z).ne_zero

/-- The second explicit local section satisfies the order-four affine law. -/
public theorem ellipticMuTwo_transform (z : UpperHalfPlane) :
    ellipticMuTwo E (fuchsianSourceAction g₂ • z) =
      1 + ellipticMuTwo E z / (E.modularParameter.tau z : ℂ) := by
  rw [ellipticMuTwo, ellipticMuTwo, tau_transform_two_coe]
  exact localMuTwo_equivariant _ (E.modularParameter.tau z).ne_zero


/-- The cusp section is holomorphic, invariant under the parabolic generator, and bounded on the
distinguished cusp region. -/
public theorem cuspLocalMu_properties :
    MDiff (cuspLocalMu E) ∧
      (∀ z, cuspLocalMu E (fuchsianSourceAction g₀ • z) = cuspLocalMu E z) ∧
      BoundedOn (cuspLocalMu E) fuchsianCuspRegion := by
  refine ⟨mdifferentiable_const, fun _ ↦ rfl, ?_⟩
  exact ⟨0, le_rfl, by simp [cuspLocalMu]⟩


end SphereSixComplex.Periods
