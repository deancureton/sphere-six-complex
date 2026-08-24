module

public import SphereSixComplex.TriangleGroup.FuchsianAction
public import SphereSixComplex.TriangleGroup.ModularParameter
public import Mathlib.GroupTheory.OrderOfElement

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

@[expose] public noncomputable def targetCuspPerm : Equiv.Perm UpperHalfPlane :=
  modularTargetAction g₀

public theorem targetOnePerm_apply (z : UpperHalfPlane) :
    ((targetOnePerm z : UpperHalfPlane) : ℂ) = (z - 1) / z := by
  exact rhoTauReal_g₁_smul z

public theorem targetTwoPerm_apply (z : UpperHalfPlane) :
    ((targetTwoPerm z : UpperHalfPlane) : ℂ) = -1 / z := by
  exact rhoTauReal_g₂_smul z

public theorem targetCuspPerm_apply (z : UpperHalfPlane) :
    ((targetCuspPerm z : UpperHalfPlane) : ℂ) = z - 1 := by
  exact rhoTauReal_g₀_smul z

/-- The order-three source and target transformations are literally the same permutation. -/
public theorem fuchsianOnePerm_eq_targetOnePerm :
    fuchsianOnePerm = targetOnePerm := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.coe_injective
  rw [fuchsianOnePerm_apply, targetOnePerm_apply]

public theorem targetOnePerm_pow_three : targetOnePerm ^ 3 = 1 := by
  rw [← fuchsianOnePerm_eq_targetOnePerm]
  exact fuchsianOnePerm_pow_three

public theorem targetOnePerm_ne_one : targetOnePerm ≠ 1 := by
  rw [← fuchsianOnePerm_eq_targetOnePerm]
  exact fuchsianOnePerm_ne_one

public theorem orderOf_targetOnePerm : orderOf targetOnePerm = 3 := by
  rw [← fuchsianOnePerm_eq_targetOnePerm]
  exact orderOf_fuchsianOnePerm

public theorem targetTwoPerm_pow_two : targetTwoPerm ^ 2 = 1 := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.coe_injective
  change ((rhoTauReal g₂ • (rhoTauReal g₂ • z) : UpperHalfPlane) : ℂ) = z
  rw [rhoTauReal_g₂_smul, rhoTauReal_g₂_smul]
  field_simp [z.ne_zero]

@[expose] public def targetTwoTestPoint : UpperHalfPlane :=
  ⟨⟨0, 2⟩, by norm_num⟩

public theorem targetTwoPerm_ne_one : targetTwoPerm ≠ 1 := by
  intro h
  have hz := congrArg (fun e : Equiv.Perm UpperHalfPlane ↦ e targetTwoTestPoint) h
  have hc := congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) hz
  rw [targetTwoPerm_apply] at hc
  have him := congrArg Complex.im hc
  norm_num [targetTwoTestPoint, Complex.div_im, Complex.normSq] at him

public theorem orderOf_targetTwoPerm : orderOf targetTwoPerm = 2 :=
  orderOf_eq_prime targetTwoPerm_pow_two targetTwoPerm_ne_one

public theorem modularTargetAction_g₂_sq : modularTargetAction (g₂ ^ 2) = 1 := by
  rw [map_pow]
  change targetTwoPerm ^ 2 = 1
  exact targetTwoPerm_pow_two

public theorem fuchsianSourceAction_g₂_sq_ne_one :
    fuchsianSourceAction (g₂ ^ 2) ≠ 1 := by
  rw [map_pow, fuchsianSourceAction_g₂]
  exact fuchsianTwoPerm_sq_ne_one

/-- The common order-three fixed point of the source and target actions. -/
@[expose] public noncomputable def commonOneFixedPoint : UpperHalfPlane :=
  fuchsianOneFixedPoint

public theorem commonOneFixedPoint_source_fixed :
    fuchsianSourceAction g₁ • commonOneFixedPoint = commonOneFixedPoint :=
  fuchsianOneFixedPoint_fixed

public theorem commonOneFixedPoint_target_fixed :
    modularTargetAction g₁ • commonOneFixedPoint = commonOneFixedPoint := by
  change targetOnePerm commonOneFixedPoint = commonOneFixedPoint
  rw [← fuchsianOnePerm_eq_targetOnePerm]
  simpa [commonOneFixedPoint] using fuchsianOneFixedPoint_fixed

public theorem targetTwoFixedPoint_fixed :
    modularTargetAction g₂ • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  change ((targetTwoPerm UpperHalfPlane.I : UpperHalfPlane) : ℂ) = UpperHalfPlane.I
  rw [targetTwoPerm_apply]
  norm_num [UpperHalfPlane.I]

/-- Width of the inverse parabolic source generator `g₀`. -/
@[expose] public noncomputable def sourceCuspWidth : ℝ := 1 + Real.sqrt 2

/-- Width of the inverse parabolic modular target generator `g₀`. -/
@[expose] public def targetCuspWidth : ℝ := 1

public theorem sourceCuspWidth_pos : 0 < sourceCuspWidth := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg 2)

public theorem targetCuspWidth_pos : 0 < targetCuspWidth := by
  norm_num [targetCuspWidth]

public theorem sourceCusp_translation (z : UpperHalfPlane) :
    (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ) = z - sourceCuspWidth := by
  simpa [sourceCuspWidth] using fuchsianSourceAction_g₀_apply z

public theorem targetCusp_translation (z : UpperHalfPlane) :
    (((modularTargetAction g₀) z : UpperHalfPlane) : ℂ) = z - targetCuspWidth := by
  change ((targetCuspPerm z : UpperHalfPlane) : ℂ) = z - targetCuspWidth
  simpa [targetCuspWidth] using targetCuspPerm_apply z

public theorem sourceProduct_translation (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ) =
      z + sourceCuspWidth := by
  rw [map_mul, fuchsianSourceAction_g₁, fuchsianSourceAction_g₂]
  simpa [sourceCuspWidth] using fuchsianProductPerm_apply z

public theorem targetProduct_translation (z : UpperHalfPlane) :
    (((modularTargetAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ) =
      z + targetCuspWidth := by
  rw [map_mul]
  change ((targetOnePerm (targetTwoPerm z) : UpperHalfPlane) : ℂ) = _
  rw [targetOnePerm_apply, targetTwoPerm_apply]
  field_simp [z.ne_zero]
  simp [targetCuspWidth]

public theorem cusp_width_relation :
    sourceCuspWidth = (1 + Real.sqrt 2) * targetCuspWidth := by
  simp [sourceCuspWidth, targetCuspWidth]

/-- Representation-side local data required by an orbifold map from the Fuchsian source to the
modular target.  It contains no assertion that the analytic map exists. -/
public structure LocalOrbifoldActionData where
  sourceOneOrder : orderOf (fuchsianSourceAction g₁) = 3
  targetOneOrder : orderOf (modularTargetAction g₁) = 3
  oneActionsAgree : fuchsianSourceAction g₁ = modularTargetAction g₁
  sourceTwoOrder : orderOf (fuchsianSourceAction g₂) = 4
  targetTwoOrder : orderOf (modularTargetAction g₂) = 2
  sourceTwoSquareNontrivial : fuchsianSourceAction (g₂ ^ 2) ≠ 1
  targetTwoSquareTrivial : modularTargetAction (g₂ ^ 2) = 1
  sourceOneFixed : fuchsianSourceAction g₁ • commonOneFixedPoint = commonOneFixedPoint
  targetOneFixed : modularTargetAction g₁ • commonOneFixedPoint = commonOneFixedPoint
  sourceTwoFixed : fuchsianSourceAction g₂ • fuchsianTwoFixedPoint =
    fuchsianTwoFixedPoint
  targetTwoFixed : modularTargetAction g₂ • UpperHalfPlane.I = UpperHalfPlane.I
  sourceCuspFormula : ∀ z, (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ) =
    z - sourceCuspWidth
  targetCuspFormula : ∀ z, (((modularTargetAction g₀) z : UpperHalfPlane) : ℂ) =
    z - targetCuspWidth

public theorem explicitLocalOrbifoldActionData :
    LocalOrbifoldActionData where
  sourceOneOrder := by
    rw [fuchsianSourceAction_g₁]
    exact orderOf_fuchsianOnePerm
  targetOneOrder := orderOf_targetOnePerm
  oneActionsAgree := by
    rw [fuchsianSourceAction_g₁]
    simpa only [targetOnePerm] using fuchsianOnePerm_eq_targetOnePerm
  sourceTwoOrder := by
    rw [fuchsianSourceAction_g₂]
    exact orderOf_fuchsianTwoPerm
  targetTwoOrder := orderOf_targetTwoPerm
  sourceTwoSquareNontrivial := fuchsianSourceAction_g₂_sq_ne_one
  targetTwoSquareTrivial := modularTargetAction_g₂_sq
  sourceOneFixed := commonOneFixedPoint_source_fixed
  targetOneFixed := commonOneFixedPoint_target_fixed
  sourceTwoFixed := fuchsianTwoFixedPoint_fixed
  targetTwoFixed := targetTwoFixedPoint_fixed
  sourceCuspFormula := sourceCusp_translation
  targetCuspFormula := targetCusp_translation

/-- Concrete local conditions on an eventual analytic period map. -/
public structure IsLocallyOrbifoldCompatible
    (tau : UpperHalfPlane → UpperHalfPlane) : Prop where
  mapOneFixedPoint : tau commonOneFixedPoint = commonOneFixedPoint
  mapTwoFixedPoint : tau fuchsianTwoFixedPoint = UpperHalfPlane.I
  equivariantOne : ∀ z,
    tau ((fuchsianSourceAction g₁) z) = (modularTargetAction g₁) (tau z)
  equivariantTwo : ∀ z,
    tau ((fuchsianSourceAction g₂) z) = (modularTargetAction g₂) (tau z)
  equivariantCusp : ∀ z,
    tau ((fuchsianSourceAction g₀) z) = (modularTargetAction g₀) (tau z)

namespace IsLocallyOrbifoldCompatible

variable {tau : UpperHalfPlane → UpperHalfPlane} (h : IsLocallyOrbifoldCompatible tau)

include h

/-- The square of the order-four source stabilizer lies in the local deck group of `tau`,
because its image in the modular target has order two. -/
public theorem invariant_under_two_square (z : UpperHalfPlane) :
    tau ((fuchsianSourceAction g₂) ((fuchsianSourceAction g₂) z)) = tau z := by
  rw [h.equivariantTwo, h.equivariantTwo]
  change targetTwoPerm (targetTwoPerm (tau z)) = tau z
  apply UpperHalfPlane.coe_injective
  rw [targetTwoPerm_apply, targetTwoPerm_apply]
  field_simp [(tau z).ne_zero]

public theorem cusp_value_translation (z : UpperHalfPlane) :
    ((tau ((fuchsianSourceAction g₀) z) : UpperHalfPlane) : ℂ) = tau z - 1 := by
  rw [h.equivariantCusp]
  exact rhoTauReal_g₀_smul (tau z)

end IsLocallyOrbifoldCompatible

end SphereSixComplex.Periods
