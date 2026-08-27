module

public import SphereSixComplex.Topology.BoundarySevenCechLowAssemblyProof

/-!
# Row identifications for the boundary-seven Cech bicomplexes

This file identifies evaluation of the two actual Cech bicomplex augmentations with the
separately constructed evaluated augmented-Cech rows.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

noncomputable def cechPresentationEvaluationArrow
    (A : Arrow SSet) (q : ℕ) : Arrow (Type 0) :=
  Arrow.mk (A.hom.app (Opposite.op (SimplexCategory.mk q)))

noncomputable def cechPresentationWideCospanEvaluationIso
    (A : Arrow SSet) (p q : ℕ) :
    WidePullbackShape.wideCospan A.right
        (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom) ⋙
          (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)) ≅
      WidePullbackShape.wideCospan
        ((cechPresentationEvaluationArrow A q).right)
        (fun _ : Fin (p + 1) ↦ (cechPresentationEvaluationArrow A q).left)
        (fun _ ↦ (cechPresentationEvaluationArrow A q).hom) :=
  NatIso.ofComponents
    (fun x ↦ by cases x <;> exact Iso.refl _)
    (by
      intro X Y f
      cases f <;> rfl)

noncomputable def cechPresentationEvaluationIso
    (A : Arrow SSet) (p q : ℕ) :
    (A.augmentedCechNerve.left.obj
        (Opposite.op (SimplexCategory.mk p))).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve.left.obj
        (Opposite.op (SimplexCategory.mk p)) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  change E.obj (widePullback A.right (fun _ : Fin (p + 1) ↦ A.left)
      (fun _ ↦ A.hom)) ≅
    widePullback (E.obj A.right) (fun _ : Fin (p + 1) ↦ E.obj A.left)
      (fun _ ↦ E.map A.hom)
  exact preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
    (cechPresentationWideCospanEvaluationIso A p q)

@[reassoc]
theorem cechPresentationEvaluationIso_hom_π
    (A : Arrow SSet) (p q : ℕ) (i : Fin (p + 1)) :
    (cechPresentationEvaluationIso A p q).hom ≫
        WidePullback.π
          (fun _ : Fin (p + 1) ↦
            (cechPresentationEvaluationArrow A q).hom) i =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let B := cechPresentationEvaluationArrow A q
  let D' := WidePullbackShape.wideCospan B.right
    (fun _ : Fin (p + 1) ↦ B.left) (fun _ ↦ B.hom)
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (cechPresentationWideCospanEvaluationIso A p q)).hom) ≫
      limit.π D' (some i) = E.map (limit.π D (some i)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i)
  dsimp only [D']
  rw [Iso.trans_hom, Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π
    (cechPresentationWideCospanEvaluationIso A p q) (some i)]
  rw [← Category.assoc, preservesLimitIso_hom_π]

@[reassoc]
theorem cechPresentationEvaluationIso_hom_base
    (A : Arrow SSet) (p q : ℕ) :
    (cechPresentationEvaluationIso A p q).hom ≫
        WidePullback.base
          (fun _ : Fin (p + 1) ↦ (cechPresentationEvaluationArrow A q).hom) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let B := cechPresentationEvaluationArrow A q
  let D' := WidePullbackShape.wideCospan B.right
    (fun _ : Fin (p + 1) ↦ B.left) (fun _ ↦ B.hom)
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (cechPresentationWideCospanEvaluationIso A p q)).hom) ≫
      limit.π D' none = E.map (limit.π D none) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none
  dsimp only [D']
  rw [Iso.trans_hom, Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π
    (cechPresentationWideCospanEvaluationIso A p q) none]
  rw [← Category.assoc, preservesLimitIso_hom_π]

theorem cechPresentationEvaluation_map_π_comp_diagramIso
    (A : Arrow SSet) (p q : ℕ) (i : Fin (p + 1)) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app (some i) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π (fun _ : Fin (p + 1) ↦ A.hom) i) := by
  rfl

theorem cechPresentationEvaluation_map_base_comp_diagramIso
    (A : Arrow SSet) (p q : ℕ) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) ≫
        (cechPresentationWideCospanEvaluationIso A p q).hom.app none =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (p + 1) ↦ A.hom)) := by
  rfl

theorem cechPresentationEvaluationIso_naturality
    (A : Arrow SSet) (q : ℕ) {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.augmentedCechNerve.left.map f) ≫
        (cechPresentationEvaluationIso A b.unop.len q).hom =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        (cechPresentationEvaluationArrow A q).augmentedCechNerve.left.map f := by
  unfold Arrow.augmentedCechNerve Arrow.cechNerve
  apply WidePullback.hom_ext
      (fun _ : Fin (b.unop.len + 1) ↦
        (cechPresentationEvaluationArrow A q).hom)
  · intro i
    erw [Category.assoc, cechPresentationEvaluationIso_hom_π]
    rw [cechPresentationEvaluation_map_π_comp_diagramIso]
    erw [← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.cechNerve.map f ≫
            WidePullback.π (fun _ : Fin (b.unop.len + 1) ↦ A.hom) i) =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        ((cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.π
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) i)
    have hmap :
        (cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.π
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) i =
        WidePullback.π
          (fun _ : Fin (a.unop.len + 1) ↦
            (cechPresentationEvaluationArrow A q).hom)
          (f.unop.toOrderHom i) := by
      rw [Arrow.cechNerve_map, WidePullback.lift_π]
    erw [hmap]
    erw [cechPresentationEvaluationIso_hom_π,
      cechPresentationEvaluation_map_π_comp_diagramIso]
    rw [Arrow.cechNerve_map, WidePullback.lift_π]
  · erw [Category.assoc, cechPresentationEvaluationIso_hom_base]
    rw [cechPresentationEvaluation_map_base_comp_diagramIso]
    erw [← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (A.cechNerve.map f ≫
            WidePullback.base (fun _ : Fin (b.unop.len + 1) ↦ A.hom)) =
      (cechPresentationEvaluationIso A a.unop.len q).hom ≫
        ((cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.base
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom))
    have hmap :
        (cechPresentationEvaluationArrow A q).cechNerve.map f ≫
          WidePullback.base
            (fun _ : Fin (b.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) =
        WidePullback.base
          (fun _ : Fin (a.unop.len + 1) ↦
            (cechPresentationEvaluationArrow A q).hom) := by
      rw [Arrow.cechNerve_map, WidePullback.lift_base]
    erw [hmap]
    erw [cechPresentationEvaluationIso_hom_base,
      cechPresentationEvaluation_map_base_comp_diagramIso]
    rw [Arrow.cechNerve_map, WidePullback.lift_base]

noncomputable def cechPresentationSimplicialEvaluationIso
    (A : Arrow SSet) (q : ℕ) :
    A.augmentedCechNerve.left ⋙
        (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve.left :=
  NatIso.ofComponents
    (fun a ↦ cechPresentationEvaluationIso A a.unop.len q)
    (by
      intro a b f
      exact cechPresentationEvaluationIso_naturality A q f)

noncomputable def cechPresentationAugmentedEvaluationIso
    (A : Arrow SSet) (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve ≅
      (cechPresentationEvaluationArrow A q).augmentedCechNerve :=
  Comma.isoMk
    (cechPresentationSimplicialEvaluationIso A q)
    (Iso.refl _)
    (by
      apply NatTrans.ext
      funext a
      simp only [NatTrans.comp_app, Functor.id_map]
      dsimp only [cechPresentationSimplicialEvaluationIso,
        SimplicialObject.Augmented.whiskering,
        SimplicialObject.Augmented.whiskeringObj]
      change (cechPresentationEvaluationIso A a.unop.len q).hom ≫
          WidePullback.base
            (fun _ : Fin (a.unop.len + 1) ↦
              (cechPresentationEvaluationArrow A q).hom) =
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base (fun _ : Fin (a.unop.len + 1) ↦ A.hom))
      rw [cechPresentationEvaluationIso_hom_base,
        cechPresentationEvaluation_map_base_comp_diagramIso])

noncomputable def boundarySevenFaceNeighborhoodWideCospanEvaluationIso
    (p q : ℕ) :
    WidePullbackShape.wideCospan
        boundarySevenFaceNeighborhoodPresentationArrow.right
        (fun _ : Fin (p + 1) ↦ boundarySevenFaceNeighborhoodPresentationArrow.left)
        (fun _ ↦ boundarySevenFaceNeighborhoodPresentationArrow.hom) ⋙
          (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)) ≅
      WidePullbackShape.wideCospan
        (boundarySevenFaceNeighborhoodPresentationArrow.right.obj
          (Opposite.op (SimplexCategory.mk q)))
        (fun _ : Fin (p + 1) ↦
          boundarySevenFaceNeighborhoodPresentationArrow.left.obj
            (Opposite.op (SimplexCategory.mk q)))
        (fun _ ↦ boundarySevenFaceNeighborhoodPresentationArrow.hom.app
          (Opposite.op (SimplexCategory.mk q))) :=
  NatIso.ofComponents
    (fun x ↦ by cases x <;> exact Iso.refl _)
    (by
      intro X Y f
      cases f <;> rfl)

@[simp]
private theorem boundarySevenFaceNeighborhoodWideCospanEvaluationIso_hom_app
    (p q : ℕ) (x : WidePullbackShape (Fin (p + 1))) :
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app x =
      eqToHom (by cases x <;> rfl) := by
  cases x <;> rfl

@[simp]
private theorem boundarySevenFaceNeighborhoodWideCospanEvaluationIso_hom_app_some
    (p q : ℕ) (i : Fin (p + 1)) :
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app (some i) =
      𝟙 _ := by
  rfl

@[simp]
private theorem boundarySevenFaceNeighborhoodWideCospanEvaluationIso_hom_app_none
    (p q : ℕ) :
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app none = 𝟙 _ := by
  rfl

noncomputable def boundarySevenFaceNeighborhoodCechEvaluationIso
    (p q : ℕ) :
    (boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj
        (Opposite.op (SimplexCategory.mk p))).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
        (Opposite.op (SimplexCategory.mk q))).augmentedCechNerve.left.obj
          (Opposite.op (SimplexCategory.mk p)) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let A := boundarySevenFaceNeighborhoodPresentationArrow
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  change E.obj (widePullback A.right (fun _ : Fin (p + 1) ↦ A.left)
      (fun _ ↦ A.hom)) ≅
    widePullback (E.obj A.right) (fun _ : Fin (p + 1) ↦ E.obj A.left)
      (fun _ ↦ E.map A.hom)
  exact preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q)

@[reassoc]
private theorem boundarySevenFaceNeighborhoodCechEvaluationIso_hom_π
    (p q : ℕ) (i : Fin (p + 1)) :
    (boundarySevenFaceNeighborhoodCechEvaluationIso p q).hom ≫
        WidePullback.π
          (fun _ : Fin (p + 1) ↦
            (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
              (Opposite.op (SimplexCategory.mk q))).hom) i =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom) i) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app
          (some i) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let A := boundarySevenFaceNeighborhoodPresentationArrow
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let D' := WidePullbackShape.wideCospan
    (A.right.obj (Opposite.op (SimplexCategory.mk q)))
    (fun _ : Fin (p + 1) ↦
      A.left.obj (Opposite.op (SimplexCategory.mk q)))
    (fun _ ↦ A.hom.app (Opposite.op (SimplexCategory.mk q)))
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q)).hom) ≫
      limit.π D' (some i) = E.map (limit.π D (some i)) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app
          (some i)
  dsimp only [D', E, A]
  rw [Iso.trans_hom, Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q) (some i)]
  rw [← Category.assoc, preservesLimitIso_hom_π]

@[reassoc]
private theorem boundarySevenFaceNeighborhoodCechEvaluationIso_hom_base
    (p q : ℕ) :
    (boundarySevenFaceNeighborhoodCechEvaluationIso p q).hom ≫
        WidePullback.base
          (fun _ : Fin (p + 1) ↦
            (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
              (Opposite.op (SimplexCategory.mk q))).hom) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom)) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app none := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
    (Opposite.op (SimplexCategory.mk q))
  let A := boundarySevenFaceNeighborhoodPresentationArrow
  let D := WidePullbackShape.wideCospan A.right
    (fun _ : Fin (p + 1) ↦ A.left) (fun _ ↦ A.hom)
  let D' := WidePullbackShape.wideCospan
    (A.right.obj (Opposite.op (SimplexCategory.mk q)))
    (fun _ : Fin (p + 1) ↦
      A.left.obj (Opposite.op (SimplexCategory.mk q)))
    (fun _ ↦ A.hom.app (Opposite.op (SimplexCategory.mk q)))
  change ((preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso
      (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q)).hom) ≫
      limit.π D' none = E.map (limit.π D none) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app none
  dsimp only [D', E, A]
  rw [Iso.trans_hom, Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π
    (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q) none]
  rw [← Category.assoc, preservesLimitIso_hom_π]

@[simp]
private theorem boundarySevenFaceNeighborhoodEvaluation_map_π_comp_diagramIso
    (p q : ℕ) (i : Fin (p + 1)) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom) i) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app
          (some i) =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.π
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom) i) := by
  rfl

@[simp]
private theorem boundarySevenFaceNeighborhoodEvaluation_map_base_comp_diagramIso
    (p q : ℕ) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom)) ≫
        (boundarySevenFaceNeighborhoodWideCospanEvaluationIso p q).hom.app none =
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base
            (fun _ : Fin (p + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom)) := by
  rfl

private noncomputable def boundarySevenFaceNeighborhoodCechRowXIso
    (q p : ℕ) :
    (firstQuadrantHorizontalRow
        boundarySevenFaceNeighborhoodCechBicomplex q).X p ≅
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (boundarySevenFaceNeighborhoodIntegralEvaluationCech q))).X p :=
  (sigmaConst.obj (AddCommGrpCat.of ℤ)).mapIso
    (boundarySevenFaceNeighborhoodCechEvaluationIso p q)

private theorem boundarySevenFaceNeighborhoodCechEvaluationIso_naturality
    (q : ℕ) {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (boundarySevenFaceNeighborhoodAugmentedCechNerve.left.map f) ≫
        (boundarySevenFaceNeighborhoodCechEvaluationIso b.unop.len q).hom =
      (boundarySevenFaceNeighborhoodCechEvaluationIso a.unop.len q).hom ≫
        (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
          (Opposite.op (SimplexCategory.mk q))).augmentedCechNerve.left.map f := by
  unfold Arrow.augmentedCechNerve Arrow.cechNerve
  apply WidePullback.hom_ext
      (fun _ : Fin (b.unop.len + 1) ↦
        (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
          (Opposite.op (SimplexCategory.mk q))).hom)
  · intro i
    erw [Category.assoc,
      boundarySevenFaceNeighborhoodCechEvaluationIso_hom_π]
    rw [boundarySevenFaceNeighborhoodEvaluation_map_π_comp_diagramIso]
    erw [← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (boundarySevenFaceNeighborhoodPresentationArrow.cechNerve.map f ≫
            WidePullback.π
              (fun _ : Fin (b.unop.len + 1) ↦
                boundarySevenFaceNeighborhoodPresentationArrow.hom) i) =
      (boundarySevenFaceNeighborhoodCechEvaluationIso a.unop.len q).hom ≫
        ((boundarySevenFaceNeighborhoodPresentationEvaluationArrow
            (Opposite.op (SimplexCategory.mk q))).cechNerve.map f ≫
          WidePullback.π
            (fun _ : Fin (b.unop.len + 1) ↦
              (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
                (Opposite.op (SimplexCategory.mk q))).hom) i)
    have hmap :
        (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
            (Opposite.op (SimplexCategory.mk q))).cechNerve.map f ≫
          WidePullback.π
            (fun _ : Fin (b.unop.len + 1) ↦
              (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
                (Opposite.op (SimplexCategory.mk q))).hom) i =
        WidePullback.π
          (fun _ : Fin (a.unop.len + 1) ↦
            (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
              (Opposite.op (SimplexCategory.mk q))).hom)
          (f.unop.toOrderHom i) := by
      rw [Arrow.cechNerve_map, WidePullback.lift_π]
    erw [hmap]
    erw [boundarySevenFaceNeighborhoodCechEvaluationIso_hom_π,
      boundarySevenFaceNeighborhoodEvaluation_map_π_comp_diagramIso]
    rw [Arrow.cechNerve_map, WidePullback.lift_π]
  · erw [Category.assoc,
      boundarySevenFaceNeighborhoodCechEvaluationIso_hom_base]
    rw [boundarySevenFaceNeighborhoodEvaluation_map_base_comp_diagramIso]
    erw [← Functor.map_comp]
    change ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
        (Opposite.op (SimplexCategory.mk q))).map
          (boundarySevenFaceNeighborhoodPresentationArrow.cechNerve.map f ≫
            WidePullback.base
              (fun _ : Fin (b.unop.len + 1) ↦
                boundarySevenFaceNeighborhoodPresentationArrow.hom)) =
      (boundarySevenFaceNeighborhoodCechEvaluationIso a.unop.len q).hom ≫
        ((boundarySevenFaceNeighborhoodPresentationEvaluationArrow
            (Opposite.op (SimplexCategory.mk q))).cechNerve.map f ≫
          WidePullback.base
            (fun _ : Fin (b.unop.len + 1) ↦
              (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
                (Opposite.op (SimplexCategory.mk q))).hom))
    have hmap :
        (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
            (Opposite.op (SimplexCategory.mk q))).cechNerve.map f ≫
          WidePullback.base
            (fun _ : Fin (b.unop.len + 1) ↦
              (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
                (Opposite.op (SimplexCategory.mk q))).hom) =
        WidePullback.base
          (fun _ : Fin (a.unop.len + 1) ↦
            (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
              (Opposite.op (SimplexCategory.mk q))).hom) := by
      rw [Arrow.cechNerve_map, WidePullback.lift_base]
    erw [hmap]
    erw [boundarySevenFaceNeighborhoodCechEvaluationIso_hom_base,
      boundarySevenFaceNeighborhoodEvaluation_map_base_comp_diagramIso]
    rw [Arrow.cechNerve_map, WidePullback.lift_base]

noncomputable def boundarySevenFaceNeighborhoodCechSimplicialEvaluationIso
    (q : ℕ) :
    boundarySevenFaceNeighborhoodAugmentedCechNerve.left ⋙
        (evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)) ≅
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
        (Opposite.op (SimplexCategory.mk q))).augmentedCechNerve.left :=
  NatIso.ofComponents
    (fun a ↦ boundarySevenFaceNeighborhoodCechEvaluationIso a.unop.len q)
    (by
      intro a b f
      exact boundarySevenFaceNeighborhoodCechEvaluationIso_naturality q f)

noncomputable def boundarySevenFaceNeighborhoodCechAugmentedEvaluationIso
    (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj
          boundarySevenFaceNeighborhoodAugmentedCechNerve ≅
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
        (Opposite.op (SimplexCategory.mk q))).augmentedCechNerve :=
  Comma.isoMk
    (boundarySevenFaceNeighborhoodCechSimplicialEvaluationIso q)
    (Iso.refl _)
    (by
      apply NatTrans.ext
      funext a
      simp only [NatTrans.comp_app, Functor.id_map]
      dsimp only [boundarySevenFaceNeighborhoodCechSimplicialEvaluationIso,
        SimplicialObject.Augmented.whiskering,
        SimplicialObject.Augmented.whiskeringObj]
      change (boundarySevenFaceNeighborhoodCechEvaluationIso a.unop.len q).hom ≫
          WidePullback.base
            (fun _ : Fin (a.unop.len + 1) ↦
              (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
                (Opposite.op (SimplexCategory.mk q))).hom) =
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q))).map
          (WidePullback.base
            (fun _ : Fin (a.unop.len + 1) ↦
              boundarySevenFaceNeighborhoodPresentationArrow.hom))
      rw [boundarySevenFaceNeighborhoodCechEvaluationIso_hom_base,
        boundarySevenFaceNeighborhoodEvaluation_map_base_comp_diagramIso])

noncomputable def boundarySevenFaceNeighborhoodIntegralCechAugmentedRowIso
    (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
        (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
          ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)))).obj
              boundarySevenFaceNeighborhoodAugmentedCechNerve) ≅
      boundarySevenFaceNeighborhoodIntegralEvaluationCech q :=
  Functor.mapIso _ (boundarySevenFaceNeighborhoodCechAugmentedEvaluationIso q)

noncomputable def boundarySevenFaceNeighborhoodCechRowArrowIso
    (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
        boundarySevenFaceNeighborhoodCechOuterAugmentation q) ≅
      Arrow.mk (boundarySevenFaceNeighborhoodCechOuterAugmentationRow q) := by
  let e := boundarySevenFaceNeighborhoodIntegralCechAugmentedRowIso q
  let X := ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj
            boundarySevenFaceNeighborhoodAugmentedCechNerve)
  let F := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q
  let Y := SimplicialObject.Augmented.drop.obj
    boundarySevenFaceNeighborhoodAugmentedCechChains
  let l₀ : firstQuadrantHorizontalRow
      boundarySevenFaceNeighborhoodCechBicomplex q ≅
      AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj X) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y
  let r₀ : firstQuadrantHorizontalRow
      ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj
        (CoverSmallIntegralSingularChainComplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood)) q ≅
      (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj X) :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app
        (CoverSmallIntegralSingularChainComplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood)
  let e₀ : Arrow.mk (firstQuadrantHorizontalRowMap
      boundarySevenFaceNeighborhoodCechOuterAugmentation q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app X) :=
    Arrow.isoMk' _ _ l₀ r₀ (by
      ext n x
      rcases n with _ | n
      · simp [l₀, r₀, X, F, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow,
          boundarySevenFaceNeighborhoodCechOuterAugmentation,
          boundarySevenFaceNeighborhoodCechBicomplex,
          boundarySevenFaceNeighborhoodAugmentedCechChains,
          SSet.chainComplexFunctor]
        erw [HomologicalComplex.comp_f]
      · rw [HomologicalComplex.comp_f,
          AlternatingFaceMapComplex.ε_app_f_succ, comp_zero]
        rfl)
  let e₁ := Arrow.isoMk'
    (AlternatingFaceMapComplex.ε.app X)
    (boundarySevenFaceNeighborhoodCechOuterAugmentationRow q)
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.drop.mapIso e))
    ((ChainComplex.single₀ AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.point.mapIso e))
    (by
      exact AlternatingFaceMapComplex.ε.naturality e.hom)
  exact e₀ ≪≫ e₁

noncomputable def boundarySevenSimplicialFaceIntegralCechAugmentedRowIso
    (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
        (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
          ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)))).obj
              boundarySevenSimplicialFaceAugmentedCechNerve) ≅
      boundarySevenSimplicialFaceIntegralEvaluationCech q :=
  Functor.mapIso _
    (cechPresentationAugmentedEvaluationIso
      boundarySevenSimplicialFacePresentationArrow q)

noncomputable def boundarySevenSimplicialFaceCechRowArrowIso
    (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
        boundarySevenSimplicialFaceCechOuterAugmentation q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app
        (boundarySevenSimplicialFaceIntegralEvaluationCech q)) := by
  let e := boundarySevenSimplicialFaceIntegralCechAugmentedRowIso q
  let X := ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj
            boundarySevenSimplicialFaceAugmentedCechNerve)
  let F := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q
  let Y := SimplicialObject.Augmented.drop.obj
    boundarySevenSimplicialFaceAugmentedCechChains
  let l₀ : firstQuadrantHorizontalRow
      boundarySevenSimplicialFaceCechBicomplex q ≅
      AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj X) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y
  let r₀ : firstQuadrantHorizontalRow
      (firstQuadrantSingleZeroBicomplex
        ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))) q ≅
      (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj X) :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app
        ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))
  let e₀ : Arrow.mk (firstQuadrantHorizontalRowMap
      boundarySevenSimplicialFaceCechOuterAugmentation q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app X) :=
    Arrow.isoMk' _ _ l₀ r₀ (by
      ext n x
      rcases n with _ | n
      · simp [l₀, r₀, X, F, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow,
          boundarySevenSimplicialFaceCechOuterAugmentation,
          boundarySevenSimplicialFaceCechBicomplex,
          boundarySevenSimplicialFaceAugmentedCechChains,
          SSet.chainComplexFunctor]
        erw [HomologicalComplex.comp_f]
      · rw [HomologicalComplex.comp_f,
          AlternatingFaceMapComplex.ε_app_f_succ, comp_zero]
        rfl)
  let e₁ := Arrow.isoMk'
    (AlternatingFaceMapComplex.ε.app X)
    (AlternatingFaceMapComplex.ε.app
      (boundarySevenSimplicialFaceIntegralEvaluationCech q))
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.drop.mapIso e))
    ((ChainComplex.single₀ AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.point.mapIso e))
    (by
      exact AlternatingFaceMapComplex.ε.naturality e.hom)
  exact e₀ ≪≫ e₁

/-- The actual horizontal rows of both boundary-seven Cech augmentations are canonically the
evaluated rows used by the extra-degeneracy contractions. -/
public noncomputable def boundarySevenCechAugmentationRowIdentifications :
    BoundarySevenCechAugmentationRowIdentifications where
  sourceRowArrowIso q := boundarySevenSimplicialFaceCechRowArrowIso q
  targetRowArrowIso q := boundarySevenFaceNeighborhoodCechRowArrowIso q

end SphereSixComplex
