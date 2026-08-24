module

public import Mathlib.Topology.Category.TopCat.EffectiveEpi
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import Mathlib.Topology.CompactOpen

/-!
# Homotopy equivalences induced by strong deformation retracts in topological pushouts

If one leg of a pushout in `TopCat` exhibits the seam as a strong deformation retract, the
opposite coprojection is a homotopy equivalence.  This file constructs the inverse and homotopy
explicitly.  It also records that the canonical map from the topological coproduct to a pushout is
a quotient map, which is useful for related gluing arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace Topology
open ContinuousMap

noncomputable section

universe u

namespace TopCat

variable {A X Y : TopCat.{u}}

/-- The canonical map from the coproduct presentation to a topological pushout. -/
public def coprodToPushout (i : A ⟶ X) (j : A ⟶ Y) :
    X ⨿ Y ⟶ pushout i j :=
  coprod.desc (pushout.inl i j) (pushout.inr i j)

@[reassoc]
public lemma coprod_inl_comp_coprodToPushout (i : A ⟶ X) (j : A ⟶ Y) :
    coprod.inl ≫ coprodToPushout i j = pushout.inl i j :=
  coprod.inl_desc _ _

@[reassoc]
public lemma coprod_inr_comp_coprodToPushout (i : A ⟶ X) (j : A ⟶ Y) :
    coprod.inr ≫ coprodToPushout i j = pushout.inr i j :=
  coprod.inr_desc _ _

/-- The canonical map from the coproduct to a topological pushout is a quotient map. -/
public lemma coprodToPushout_isQuotientMap (i : A ⟶ X) (j : A ⟶ Y) :
    IsQuotientMap (coprodToPushout i j) := by
  let q := coprodToPushout i j
  let _ : EffectiveEpi q := ⟨⟨{
    desc := fun {W} e h ↦ pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) (by
      apply h (i ≫ coprod.inl) (j ≫ coprod.inr)
      rw [Category.assoc, Category.assoc]
      dsimp [q]
      rw [coprodToPushout, coprod.inl_desc, coprod.inr_desc, pushout.condition])
    fac := fun {W} e h ↦ by
      apply coprod.hom_ext
      · rw [← Category.assoc]
        calc
          (coprod.inl ≫ q) ≫
              pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ =
              pushout.inl i j ≫
                pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ := by
            congr 1
            exact coprod_inl_comp_coprodToPushout i j
          _ = coprod.inl ≫ e := pushout.inl_desc _ _ _
      · rw [← Category.assoc]
        calc
          (coprod.inr ≫ q) ≫
              pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ =
              pushout.inr i j ≫
                pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ := by
            congr 1
            exact coprod_inr_comp_coprodToPushout i j
          _ = coprod.inr ≫ e := pushout.inr_desc _ _ _
    uniq := fun {W} e h m hm ↦ by
      apply pushout.hom_ext
      · calc
          pushout.inl i j ≫ m = coprod.inl ≫ e := by
            simpa only [← Category.assoc, q, coprodToPushout, coprod.inl_desc] using
              congrArg (fun k ↦ coprod.inl ≫ k) hm
          _ = pushout.inl i j ≫
              pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ :=
            (pushout.inl_desc _ _ _).symm
      · calc
          pushout.inr i j ≫ m = coprod.inr ≫ e := by
            simpa only [← Category.assoc, q, coprodToPushout, coprod.inr_desc] using
              congrArg (fun k ↦ coprod.inr ≫ k) hm
          _ = pushout.inr i j ≫
              pushout.desc (coprod.inl ≫ e) (coprod.inr ≫ e) _ :=
            (pushout.inr_desc _ _ _).symm
  }⟩⟩
  exact (TopCat.effectiveEpi_iff_isQuotientMap q).mp inferInstance

/-- Explicit data exhibiting the domain of `i : A ⟶ X` as a strong deformation retract of
`X`.  The homotopy runs from `retraction ≫ i` to the identity and fixes the image of `i`
pointwise.  The `Data` suffix avoids colliding with other deformation-retract predicates. -/
public structure StrongDeformationRetractData (i : A ⟶ X) where
  retraction : X ⟶ A
  retract : i ≫ retraction = 𝟙 A
  homotopy : TopCat.Homotopy (retraction ≫ i) (𝟙 X)
  fixed : ∀ (t : unitInterval) (a : A), homotopy (t, i a) = i a

namespace StrongDeformationRetractData

variable {i : A ⟶ X} (D : StrongDeformationRetractData i) (j : A ⟶ Y)

/-- Collapse the left side of a pushout onto its seam. -/
public def pushoutRetraction : pushout i j ⟶ Y :=
  pushout.desc (D.retraction ≫ j) (𝟙 Y) (by
    rw [← Category.assoc, D.retract, Category.id_comp, Category.comp_id])

@[simp]
public lemma inl_pushoutRetraction :
    pushout.inl i j ≫ D.pushoutRetraction j = D.retraction ≫ j :=
  pushout.inl_desc _ _ _

@[simp]
public lemma inr_pushoutRetraction :
    pushout.inr i j ≫ D.pushoutRetraction j = 𝟙 Y :=
  pushout.inr_desc _ _ _

/-- The left branch of the homotopy which collapses the pushout onto `Y`. -/
public def leftHomotopy : TopCat.Homotopy
    (D.retraction ≫ j ≫ pushout.inr i j) (pushout.inl i j) where
  toFun p := pushout.inl i j (D.homotopy p)
  continuous_toFun := (pushout.inl i j).hom.continuous.comp D.homotopy.continuous
  map_zero_left x := by
    calc
      pushout.inl i j (D.homotopy (0, x)) =
          pushout.inl i j ((D.retraction ≫ i) x) :=
        congrArg (pushout.inl i j) (D.homotopy.map_zero_left x)
      _ = (D.retraction ≫ j ≫ pushout.inr i j) x :=
        CategoryTheory.congr_fun (pushout.condition (f := i) (g := j)) (D.retraction x)
  map_one_left x :=
    congrArg (pushout.inl i j) (D.homotopy.map_one_left x)

/-- The right branch stays fixed during the collapse. -/
public def rightHomotopy : TopCat.Homotopy (pushout.inr i j) (pushout.inr i j) :=
  TopCat.Homotopy.refl _

/-- The left branch, curried as a continuous family of paths. -/
public def leftPaths : X ⟶ TopCat.of C(unitInterval, (pushout i j : TopCat)) :=
  TopCat.ofHom <| ContinuousMap.curry
    ⟨fun p : X × unitInterval ↦ D.leftHomotopy j (p.2, p.1),
      (D.leftHomotopy j).continuous.comp continuous_swap⟩

/-- The fixed right branch, curried as a continuous family of paths. -/
public def rightPaths : Y ⟶ TopCat.of C(unitInterval, (pushout i j : TopCat)) :=
  TopCat.ofHom <| ContinuousMap.curry
    ⟨fun p : Y × unitInterval ↦ rightHomotopy (i := i) j (p.2, p.1),
      (rightHomotopy (i := i) j).continuous.comp continuous_swap⟩

public lemma paths_compatible : i ≫ D.leftPaths j = j ≫ rightPaths (i := i) j := by
  ext a t
  change pushout.inl i j (D.homotopy (t, i a)) = pushout.inr i j (j a)
  rw [D.fixed]
  exact CategoryTheory.congr_fun (pushout.condition (f := i) (g := j)) a

/-- A continuous family of paths on the pushout, obtained by its universal property. -/
public def pushoutPaths : pushout i j ⟶
    TopCat.of C(unitInterval, (pushout i j : TopCat)) :=
  pushout.desc (D.leftPaths j) (rightPaths (i := i) j) (D.paths_compatible j)

@[simp]
public lemma inl_pushoutPaths : pushout.inl i j ≫ D.pushoutPaths j = D.leftPaths j :=
  pushout.inl_desc _ _ _

@[simp]
public lemma inr_pushoutPaths :
    pushout.inr i j ≫ D.pushoutPaths j = rightPaths (i := i) j :=
  pushout.inr_desc _ _ _

/-- Evaluate a path at a specified time. -/
public def pathEval (P : TopCat.{u}) (t : unitInterval) :
    TopCat.of C(unitInterval, P) ⟶ P :=
  TopCat.ofHom ⟨fun γ ↦ γ t, continuous_eval_const t⟩

public lemma pushoutPaths_eval_zero :
    D.pushoutPaths j ≫ pathEval (pushout i j) 0 =
      D.pushoutRetraction j ≫ pushout.inr i j := by
  apply pushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, D.inl_pushoutPaths,
      D.inl_pushoutRetraction]
    ext x
    exact (D.leftHomotopy j).map_zero_left x
  · rw [← Category.assoc, ← Category.assoc, D.inr_pushoutPaths,
      D.inr_pushoutRetraction, Category.id_comp]
    ext y
    exact (rightHomotopy (i := i) j).map_zero_left y

public lemma pushoutPaths_eval_one :
    D.pushoutPaths j ≫ pathEval (pushout i j) 1 = 𝟙 (pushout i j) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, D.inl_pushoutPaths, Category.comp_id]
    ext x
    exact (D.leftHomotopy j).map_one_left x
  · rw [← Category.assoc, D.inr_pushoutPaths, Category.comp_id]
    ext y
    exact (rightHomotopy (i := i) j).map_one_left y

/-- The pushout strongly deformation retracts onto its right side. -/
public def pushoutHomotopy : TopCat.Homotopy
    (D.pushoutRetraction j ≫ pushout.inr i j) (𝟙 (pushout i j)) where
  toFun p := D.pushoutPaths j p.2 p.1
  continuous_toFun :=
    (ContinuousMap.uncurry (D.pushoutPaths j).hom).continuous.comp continuous_swap
  map_zero_left p := CategoryTheory.congr_fun (D.pushoutPaths_eval_zero j) p
  map_one_left p := CategoryTheory.congr_fun (D.pushoutPaths_eval_one j) p

/-- If the left leg of a pushout is a strong deformation retract, the right coprojection is a
homotopy equivalence. -/
public def pushoutInrHomotopyEquiv :
    (Y : Type u) ≃ₕ ((pushout i j : TopCat) : Type u) where
  toFun := (pushout.inr i j).hom
  invFun := (D.pushoutRetraction j).hom
  left_inv := by
    have h : (D.pushoutRetraction j).hom.comp (pushout.inr i j).hom =
        ContinuousMap.id Y := by
      ext y
      exact CategoryTheory.congr_fun (D.inr_pushoutRetraction j) y
    rw [h]
  right_inv := ⟨D.pushoutHomotopy j⟩

@[simp]
public lemma pushoutInrHomotopyEquiv_apply (y : Y) :
    D.pushoutInrHomotopyEquiv j y = pushout.inr i j y :=
  rfl

/-- Symmetric form: if the right leg is a strong deformation retract, the left coprojection is a
homotopy equivalence. -/
public def pushoutInlHomotopyEquiv (D' : StrongDeformationRetractData j) :
    (X : Type u) ≃ₕ ((pushout i j : TopCat) : Type u) :=
  (D'.pushoutInrHomotopyEquiv i).trans
    (TopCat.homeoOfIso (pushoutSymmetry j i)).toHomotopyEquiv

@[simp]
public lemma pushoutInlHomotopyEquiv_apply
    (D' : StrongDeformationRetractData j) (x : X) :
    pushoutInlHomotopyEquiv (i := i) (j := j) D' x = pushout.inl i j x := by
  change (pushoutSymmetry j i).hom (pushout.inr j i x) = pushout.inl i j x
  exact CategoryTheory.congr_fun (inr_comp_pushoutSymmetry_hom j i) x

end StrongDeformationRetractData

end TopCat
