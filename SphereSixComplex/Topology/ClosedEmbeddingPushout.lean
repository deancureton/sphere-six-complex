module

public import SphereSixComplex.Topology.ClosedEmbeddingGluing
public import SphereSixComplex.Topology.PushoutHomotopy

/-!
# Comparing the direct sum quotient with the categorical topological pushout

The explicit quotient used for compact-Hausdorff gluing represents the same topological space as
Mathlib's categorical pushout in `TopCat`.  This comparison lets point-set results use the direct
quotient while homotopy arguments use the pushout universal property.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

namespace SphereSixComplex
namespace ClosedEmbeddingGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X Y : Type u}
  [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
  (f : Z → X) (g : Z → Y)
  (hf : Injective f) (hg : Injective g)
  (hfc : Continuous f) (hgc : Continuous g)

/-- The left gluing leg as a `TopCat` morphism. -/
public def leftLeg : TopCat.of Z ⟶ TopCat.of X :=
  TopCat.ofHom ⟨f, hfc⟩

/-- The right gluing leg as a `TopCat` morphism. -/
public def rightLeg : TopCat.of Z ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨g, hgc⟩

/-- Map the explicit quotient into the categorical pushout. -/
public def sumGlueToPushout :
    SumGlue f g hf hg →
      (pushout (leftLeg f hfc) (rightLeg g hgc) : TopCat) :=
  Quotient.lift
    (fun s ↦ match s with
      | .inl x => pushout.inl (leftLeg f hfc) (rightLeg g hgc) x
      | .inr y => pushout.inr (leftLeg f hfc) (rightLeg g hgc) y)
    (by
      intro a b hab
      rcases a with x | y <;> rcases b with x' | y' <;>
        change sumGlueRel f g _ _ at hab
      · subst x'
        rfl
      · rcases hab with ⟨z, rfl, rfl⟩
        exact CategoryTheory.congr_fun
          (pushout.condition (f := leftLeg f hfc) (g := rightLeg g hgc)) z
      · rcases hab with ⟨z, rfl, rfl⟩
        exact (CategoryTheory.congr_fun
          (pushout.condition (f := leftLeg f hfc) (g := rightLeg g hgc)) z).symm
      · subst y'
        rfl)

/-- The comparison map from the explicit quotient to the categorical pushout is continuous. -/
public theorem continuous_sumGlueToPushout :
    Continuous (sumGlueToPushout f g hf hg hfc hgc) := by
  letI : Setoid (X ⊕ Y) := sumGlueSetoid f g hf hg
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have heq : sumGlueToPushout f g hf hg hfc hgc ∘
      (fun s : X ⊕ Y ↦ (Quotient.mk'' s : SumGlue f g hf hg)) =
      Sum.elim
        (pushout.inl (leftLeg f hfc) (rightLeg g hgc))
        (pushout.inr (leftLeg f hfc) (rightLeg g hgc)) := by
    funext s
    rcases s with x | y <;> rfl
  change Continuous (sumGlueToPushout f g hf hg hfc hgc ∘
    (fun s : X ⊕ Y ↦ (Quotient.mk'' s : SumGlue f g hf hg)))
  rw [heq]
  exact (pushout.inl (leftLeg f hfc) (rightLeg g hgc)).hom.continuous.sumElim
    (pushout.inr (leftLeg f hfc) (rightLeg g hgc)).hom.continuous

/-- Map the categorical pushout back to the explicit quotient. -/
public def pushoutToSumGlue :
    pushout (leftLeg f hfc) (rightLeg g hgc) ⟶ TopCat.of (SumGlue f g hf hg) :=
  pushout.desc
    (TopCat.ofHom ⟨toSumGlueLeft f g hf hg, continuous_toSumGlueLeft f g hf hg⟩)
    (TopCat.ofHom ⟨toSumGlueRight f g hf hg, continuous_toSumGlueRight f g hf hg⟩)
    (by
      ext z
      exact toSumGlue_commute f g hf hg z)

@[simp]
public theorem pushoutToSumGlue_inl (x : X) :
    pushoutToSumGlue f g hf hg hfc hgc
        (pushout.inl (leftLeg f hfc) (rightLeg g hgc) x) =
      toSumGlueLeft f g hf hg x :=
  by
    change (pushout.inl (leftLeg f hfc) (rightLeg g hgc) ≫
      pushoutToSumGlue f g hf hg hfc hgc) x = _
    rw [pushoutToSumGlue, pushout.inl_desc]
    rfl

@[simp]
public theorem pushoutToSumGlue_inr (y : Y) :
    pushoutToSumGlue f g hf hg hfc hgc
        (pushout.inr (leftLeg f hfc) (rightLeg g hgc) y) =
      toSumGlueRight f g hf hg y :=
  by
    change (pushout.inr (leftLeg f hfc) (rightLeg g hgc) ≫
      pushoutToSumGlue f g hf hg hfc hgc) y = _
    rw [pushoutToSumGlue, pushout.inr_desc]
    rfl

@[simp]
public theorem sumGlueToPushout_left (x : X) :
    sumGlueToPushout f g hf hg hfc hgc (toSumGlueLeft f g hf hg x) =
      pushout.inl (leftLeg f hfc) (rightLeg g hgc) x :=
  rfl

@[simp]
public theorem sumGlueToPushout_right (y : Y) :
    sumGlueToPushout f g hf hg hfc hgc (toSumGlueRight f g hf hg y) =
      pushout.inr (leftLeg f hfc) (rightLeg g hgc) y :=
  rfl

/-- The direct quotient is canonically homeomorphic to the categorical topological pushout. -/
public def sumGlueHomeomorphPushout :
    SumGlue f g hf hg ≃ₜ
      (pushout (leftLeg f hfc) (rightLeg g hgc) : TopCat) where
  toFun := sumGlueToPushout f g hf hg hfc hgc
  invFun := pushoutToSumGlue f g hf hg hfc hgc
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ s =>
      rcases s with x | y
      · change pushoutToSumGlue f g hf hg hfc hgc
          (sumGlueToPushout f g hf hg hfc hgc
            (toSumGlueLeft f g hf hg x)) =
            toSumGlueLeft f g hf hg x
        rw [sumGlueToPushout_left, pushoutToSumGlue_inl]
      · change pushoutToSumGlue f g hf hg hfc hgc
          (sumGlueToPushout f g hf hg hfc hgc
            (toSumGlueRight f g hf hg y)) =
            toSumGlueRight f g hf hg y
        rw [sumGlueToPushout_right, pushoutToSumGlue_inr]
  right_inv := by
    intro p
    change (sumGlueToPushout f g hf hg hfc hgc ∘
      pushoutToSumGlue f g hf hg hfc hgc) p = p
    have hmaps :
        (pushoutToSumGlue f g hf hg hfc hgc ≫
          TopCat.ofHom ⟨sumGlueToPushout f g hf hg hfc hgc,
            continuous_sumGlueToPushout f g hf hg hfc hgc⟩) =
          𝟙 (pushout (leftLeg f hfc) (rightLeg g hgc)) := by
      apply pushout.hom_ext
      · ext x
        change sumGlueToPushout f g hf hg hfc hgc
          (pushoutToSumGlue f g hf hg hfc hgc
            (pushout.inl (leftLeg f hfc) (rightLeg g hgc) x)) =
            pushout.inl (leftLeg f hfc) (rightLeg g hgc) x
        rw [pushoutToSumGlue_inl, sumGlueToPushout_left]
      · ext y
        change sumGlueToPushout f g hf hg hfc hgc
          (pushoutToSumGlue f g hf hg hfc hgc
            (pushout.inr (leftLeg f hfc) (rightLeg g hgc) y)) =
            pushout.inr (leftLeg f hfc) (rightLeg g hgc) y
        rw [pushoutToSumGlue_inr, sumGlueToPushout_right]
    exact CategoryTheory.congr_fun hmaps p
  continuous_toFun := continuous_sumGlueToPushout f g hf hg hfc hgc
  continuous_invFun := (pushoutToSumGlue f g hf hg hfc hgc).hom.continuous

end ClosedEmbeddingGluing
end SphereSixComplex
