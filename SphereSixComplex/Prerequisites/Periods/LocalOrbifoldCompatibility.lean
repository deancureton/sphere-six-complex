module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianAction
public import SphereSixComplex.Prerequisites.TriangleGroup.ModularParameter

/-!
# Local orbifold compatibility of the source and target actions

The source of the period map carries the genuine `(3, 4, ∞)` Fuchsian action, while its
modular target has signature `(3, 2, ∞)`.  This file records the resulting local identities:
the order-three actions agree, the order-four source stabilizer maps to an order-two target
stabilizer, and the two cusp translations have different widths.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- The projective modular action on the target upper half-plane. -/
@[expose] public noncomputable def modularTargetAction :
    Delta →* Equiv.Perm UpperHalfPlane :=
  (MulAction.toPermHom (GL (Fin 2) ℝ) UpperHalfPlane).comp rhoTauReal

@[expose] public noncomputable def targetOnePerm : Equiv.Perm UpperHalfPlane :=
  modularTargetAction g₁

@[expose] public noncomputable def targetTwoPerm : Equiv.Perm UpperHalfPlane :=
  modularTargetAction g₂


public theorem targetOnePerm_apply (z : UpperHalfPlane) :
    ((targetOnePerm z : UpperHalfPlane) : ℂ) = (z - 1) / z := by
  exact rhoTauReal_g₁_smul z

public theorem targetTwoPerm_apply (z : UpperHalfPlane) :
    ((targetTwoPerm z : UpperHalfPlane) : ℂ) = -1 / z := by
  exact rhoTauReal_g₂_smul z


/-- The order-three source and target transformations are literally the same permutation. -/
public theorem fuchsianOnePerm_eq_targetOnePerm :
    fuchsianOnePerm = targetOnePerm := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.coe_injective
  rw [fuchsianOnePerm_apply, targetOnePerm_apply]













public theorem targetTwoFixedPoint_fixed :
    modularTargetAction g₂ • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  change ((targetTwoPerm UpperHalfPlane.I : UpperHalfPlane) : ℂ) = UpperHalfPlane.I
  rw [targetTwoPerm_apply]
  norm_num [UpperHalfPlane.I]

/-- Width of the inverse parabolic source generator `g₀`. -/
@[expose] public noncomputable def sourceCuspWidth : ℝ := 1 + Real.sqrt 2


public theorem sourceCuspWidth_pos : 0 < sourceCuspWidth := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg 2)


public theorem sourceCusp_translation (z : UpperHalfPlane) :
    (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ) = z - sourceCuspWidth := by
  simpa [sourceCuspWidth] using fuchsianSourceAction_g₀_apply z








end SphereSixComplex.Periods
