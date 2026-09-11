module

public import SphereSixComplex.Prerequisites.Geometry.EquivariantQuotientHomeomorph
public import SphereSixComplex.Prerequisites.Topology.MapHomotopyEquivalence

/-!
# Equivariant homotopy equivalences descend to orbit quotients

An equivariant homeomorphism descends to orbit quotients automatically, but a homotopy
equivalence requires its chosen inverse and both chosen homotopies to be equivariant as well.
This file records that exact hypothesis and performs the descent.  It is useful for radial
deformations of cyclic quotient bundles, where replacing the quotient bundle by a global product
would incorrectly discard its monodromy.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.EquivariantQuotientHomeomorph

universe u v

variable {G : Type*} [Group G]
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]



/-- A homotopy equivalence together with enough equivariance to descend the maps and the chosen
homotopies to orbit quotients. -/
public structure EquivariantHomotopyEquivData
    (sourceAction : MulAction G X) (targetAction : MulAction G Y) where
  toFun : C(X, Y)
  invFun : C(Y, X)
  toFun_equivariant : ∀ (g : G) (x : X),
    toFun (actionMap sourceAction g x) = actionMap targetAction g (toFun x)
  invFun_equivariant : ∀ (g : G) (y : Y),
    invFun (actionMap targetAction g y) = actionMap sourceAction g (invFun y)
  leftInvHomotopy :
    ContinuousMap.Homotopy (invFun.comp toFun) (ContinuousMap.id X)
  rightInvHomotopy :
    ContinuousMap.Homotopy (toFun.comp invFun) (ContinuousMap.id Y)
  leftInvHomotopy_equivariant : ∀ (g : G) (t : unitInterval) (x : X),
    leftInvHomotopy (t, actionMap sourceAction g x) =
      actionMap sourceAction g (leftInvHomotopy (t, x))
  rightInvHomotopy_equivariant : ∀ (g : G) (t : unitInterval) (y : Y),
    rightInvHomotopy (t, actionMap targetAction g y) =
      actionMap targetAction g (rightInvHomotopy (t, y))

namespace EquivariantHomotopyEquivData

variable {sourceAction : MulAction G X} {targetAction : MulAction G Y}
    (E : EquivariantHomotopyEquivData sourceAction targetAction)


/-- The forward equivariant map descended to orbit quotients. -/
public def quotientToFun :
    C(Quotient (orbitRelOf sourceAction), Quotient (orbitRelOf targetAction)) where
  toFun := Quotient.lift (fun x ↦ Quotient.mk _ (E.toFun x)) (by
    intro a b hab
    apply Quotient.sound
    change (∃ g : G, actionMap sourceAction g b = a) at hab
    change ∃ g : G, actionMap targetAction g (E.toFun b) = E.toFun a
    obtain ⟨g, rfl⟩ := hab
    exact ⟨g, (E.toFun_equivariant g b).symm⟩)
  continuous_toFun :=
    continuous_quot_lift _ (continuous_quot_mk.comp E.toFun.continuous)

/-- The inverse equivariant map descended to orbit quotients. -/
public def quotientInvFun :
    C(Quotient (orbitRelOf targetAction), Quotient (orbitRelOf sourceAction)) where
  toFun := Quotient.lift (fun y ↦ Quotient.mk _ (E.invFun y)) (by
    intro a b hab
    apply Quotient.sound
    change (∃ g : G, actionMap targetAction g b = a) at hab
    change ∃ g : G, actionMap sourceAction g (E.invFun b) = E.invFun a
    obtain ⟨g, rfl⟩ := hab
    exact ⟨g, (E.invFun_equivariant g b).symm⟩)
  continuous_toFun :=
    continuous_quot_lift _ (continuous_quot_mk.comp E.invFun.continuous)



/-- The underlying function of the descended left-inverse homotopy. -/
public def quotientLeftInvHomotopyToFun :
    unitInterval × Quotient (orbitRelOf sourceAction) →
      Quotient (orbitRelOf sourceAction) :=
  fun z ↦ Quotient.lift
    (fun x ↦ Quotient.mk _ (E.leftInvHomotopy (z.1, x))) (by
      intro a b hab
      apply Quotient.sound
      change (∃ g : G, actionMap sourceAction g b = a) at hab
      change ∃ g : G,
        actionMap sourceAction g (E.leftInvHomotopy (z.1, b)) =
          E.leftInvHomotopy (z.1, a)
      obtain ⟨g, rfl⟩ := hab
      exact ⟨g, (E.leftInvHomotopy_equivariant g z.1 b).symm⟩) z.2

/-- The underlying function of the descended right-inverse homotopy. -/
public def quotientRightInvHomotopyToFun :
    unitInterval × Quotient (orbitRelOf targetAction) →
      Quotient (orbitRelOf targetAction) :=
  fun z ↦ Quotient.lift
    (fun y ↦ Quotient.mk _ (E.rightInvHomotopy (z.1, y))) (by
      intro a b hab
      apply Quotient.sound
      change (∃ g : G, actionMap targetAction g b = a) at hab
      change ∃ g : G,
        actionMap targetAction g (E.rightInvHomotopy (z.1, b)) =
          E.rightInvHomotopy (z.1, a)
      obtain ⟨g, rfl⟩ := hab
      exact ⟨g, (E.rightInvHomotopy_equivariant g z.1 b).symm⟩) z.2

public theorem quotientLeftInvHomotopyToFun_continuous
    (hcontinuous : letI := sourceAction; ContinuousConstSMul G X) :
    Continuous E.quotientLeftInvHomotopyToFun := by
  let _ := sourceAction
  let _ : ContinuousConstSMul G X := hcontinuous
  let q : X → Quotient (orbitRelOf sourceAction) := Quotient.mk _
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : unitInterval × X ↦
    Quotient.mk _ (E.leftInvHomotopy (z.1, z.2)))
  exact continuous_quot_mk.comp E.leftInvHomotopy.continuous

public theorem quotientRightInvHomotopyToFun_continuous
    (hcontinuous : letI := targetAction; ContinuousConstSMul G Y) :
    Continuous E.quotientRightInvHomotopyToFun := by
  let _ := targetAction
  let _ : ContinuousConstSMul G Y := hcontinuous
  let q : Y → Quotient (orbitRelOf targetAction) := Quotient.mk _
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := Y))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : unitInterval × Y ↦
    Quotient.mk _ (E.rightInvHomotopy (z.1, z.2)))
  exact continuous_quot_mk.comp E.rightInvHomotopy.continuous

/-- The equivariant left-inverse homotopy descended to the source orbit quotient. -/
public def quotientLeftInvHomotopy
    (hcontinuous : letI := sourceAction; ContinuousConstSMul G X) :
    ContinuousMap.Homotopy (E.quotientInvFun.comp E.quotientToFun)
      (ContinuousMap.id (Quotient (orbitRelOf sourceAction))) where
  toFun := E.quotientLeftInvHomotopyToFun
  continuous_toFun := E.quotientLeftInvHomotopyToFun_continuous hcontinuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (E.leftInvHomotopy.map_zero_left x)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (E.leftInvHomotopy.map_one_left x)

/-- The equivariant right-inverse homotopy descended to the target orbit quotient. -/
public def quotientRightInvHomotopy
    (hcontinuous : letI := targetAction; ContinuousConstSMul G Y) :
    ContinuousMap.Homotopy (E.quotientToFun.comp E.quotientInvFun)
      (ContinuousMap.id (Quotient (orbitRelOf targetAction))) where
  toFun := E.quotientRightInvHomotopyToFun
  continuous_toFun := E.quotientRightInvHomotopyToFun_continuous hcontinuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | _ y => exact congrArg (Quotient.mk _) (E.rightInvHomotopy.map_zero_left y)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | _ y => exact congrArg (Quotient.mk _) (E.rightInvHomotopy.map_one_left y)

/-- An equivariant homotopy equivalence descends to a homotopy equivalence of orbit quotients. -/
public def quotientHomotopyEquiv
    (sourceContinuous : letI := sourceAction; ContinuousConstSMul G X)
    (targetContinuous : letI := targetAction; ContinuousConstSMul G Y) :
    Quotient (orbitRelOf sourceAction) ≃ₕ Quotient (orbitRelOf targetAction) where
  toFun := E.quotientToFun
  invFun := E.quotientInvFun
  left_inv := ⟨E.quotientLeftInvHomotopy sourceContinuous⟩
  right_inv := ⟨E.quotientRightInvHomotopy targetContinuous⟩


/-- Homeomorphic models of an equivariant orbit-quotient map transfer its homotopy equivalence
to the literal geometric map. -/
public theorem isHomotopyEquivalence_of_quotient_models
    {E₁ E₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂]
    (totalMap : E₁ → E₂)
    (sourceModel : E₁ ≃ₜ Quotient (orbitRelOf sourceAction))
    (targetModel : E₂ ≃ₜ Quotient (orbitRelOf targetAction))
    (commutes : targetModel ∘ totalMap = E.quotientToFun ∘ sourceModel)
    (sourceContinuous : letI := sourceAction; ContinuousConstSMul G X)
    (targetContinuous : letI := targetAction; ContinuousConstSMul G Y) :
    IsHomotopyEquivalence totalMap := by
  let totalEquiv : E₁ ≃ₕ E₂ :=
    sourceModel.toHomotopyEquiv |>.trans
      (E.quotientHomotopyEquiv sourceContinuous targetContinuous) |>.trans
        targetModel.symm.toHomotopyEquiv
  refine ⟨totalEquiv, ?_⟩
  funext x
  apply targetModel.injective
  change targetModel
      (targetModel.symm (E.quotientHomotopyEquiv sourceContinuous targetContinuous
        (sourceModel x))) = targetModel (totalMap x)
  rw [targetModel.apply_symm_apply]
  exact (congrFun commutes x).symm

end EquivariantHomotopyEquivData

end SphereSixComplex
