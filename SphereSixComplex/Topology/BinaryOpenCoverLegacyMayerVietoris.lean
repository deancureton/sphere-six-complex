module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly
public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# The binary open-cover sequence in the legacy interface

This file transports the categorical Mayer--Vietoris sequence for two open subspaces to the
set-subtype interface used by `IntegralMayerVietoris.ExactSequence`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- The set subtype underlying an open is homeomorphic to its `Opens.toTopCat` realization. -/
public def opensCarrierHomeomorph {X : TopCat} (U : Opens X) :
    (U : Set X) ≃ₜ (Opens.toTopCat X).obj U where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Set intersection agrees topologically with infimum in the lattice of opens. -/
public def opensIntersectionHomeomorph {X : TopCat} (U V : Opens X) :
    ((U : Set X) ∩ (V : Set X) : Set X) ≃ₜ (Opens.toTopCat X).obj (U ⊓ V) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- A covered union subtype is homeomorphic to the ambient space. -/
public def opensUnionHomeomorph {X : TopCat} (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    ((U : Set X) ∪ (V : Set X) : Set X) ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, by
    have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

private lemma biprodIsoProd_hom_comp_fst (G H : AddCommGrpCat) :
    (AddCommGrpCat.biprodIsoProd G H).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst G H) =
      (biprod.fst : G ⊞ H ⟶ G) := by
  calc
    _ = (AddCommGrpCat.biprodIsoProd G H).hom ≫
          ((AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.fst) :=
      congrArg ((AddCommGrpCat.biprodIsoProd G H).hom ≫ ·)
        (AddCommGrpCat.biprodIsoProd_inv_comp_fst G H).symm
    _ = ((AddCommGrpCat.biprodIsoProd G H).hom ≫
          (AddCommGrpCat.biprodIsoProd G H).inv) ≫ biprod.fst := by
      rw [Category.assoc]
    _ = _ := by rw [Iso.hom_inv_id, Category.id_comp]

private lemma biprodIsoProd_hom_comp_snd (G H : AddCommGrpCat) :
    (AddCommGrpCat.biprodIsoProd G H).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd G H) =
      (biprod.snd : G ⊞ H ⟶ H) := by
  calc
    _ = (AddCommGrpCat.biprodIsoProd G H).hom ≫
          ((AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.snd) :=
      congrArg ((AddCommGrpCat.biprodIsoProd G H).hom ≫ ·)
        (AddCommGrpCat.biprodIsoProd_inv_comp_snd G H).symm
    _ = ((AddCommGrpCat.biprodIsoProd G H).hom ≫
          (AddCommGrpCat.biprodIsoProd G H).inv) ≫ biprod.snd := by
      rw [Category.assoc]
    _ = _ := by rw [Iso.hom_inv_id, Category.id_comp]

/-- Homology comparison for the set subtype underlying one open. -/
public noncomputable def opensCarrierHomologyIso {X : TopCat} (U : Opens X) (n : ℕ) :
    (integralHomologyFunctor n).obj (TopCat.of (U : Set X)) ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj U) :=
  (integralHomologyFunctor n).mapIso (TopCat.isoOfHomeo (opensCarrierHomeomorph U))

/-- Homology comparison between set intersection and infimum of opens. -/
public noncomputable def opensIntersectionHomologyIso {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (integralHomologyFunctor n).obj
        (TopCat.of ((U : Set X) ∩ (V : Set X) : Set X)) ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) :=
  (integralHomologyFunctor n).mapIso (TopCat.isoOfHomeo (opensIntersectionHomeomorph U V))

/-- Homology comparison between a covered union subtype and the ambient space. -/
public noncomputable def opensUnionHomologyIso {X : TopCat}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    (integralHomologyFunctor n).obj
        (TopCat.of ((U : Set X) ∪ (V : Set X) : Set X)) ≅
      (integralHomologyFunctor n).obj X :=
  (integralHomologyFunctor n).mapIso (TopCat.isoOfHomeo (opensUnionHomeomorph U V hcover))

/-- Homology comparison between the categorical biproduct and the legacy product. -/
public noncomputable def piecesHomologyIso {X : TopCat} (U V : Opens X) (n : ℕ) :
    (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj U) ⊞
        (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj V) ≅
      AddCommGrpCat.of
        (IntegralSingularHomology n (U : Set X) ×
          IntegralSingularHomology n (V : Set X)) :=
  biprod.mapIso (opensCarrierHomologyIso U n).symm (opensCarrierHomologyIso V n).symm ≪≫
    AddCommGrpCat.biprodIsoProd _ _

private noncomputable def legacyDifferenceMorphism {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (integralHomologyFunctor n).obj
        (TopCat.of ((U : Set X) ∩ (V : Set X) : Set X)) ⟶
      AddCommGrpCat.of
        (IntegralSingularHomology n (U : Set X) ×
          IntegralSingularHomology n (V : Set X)) :=
  biprod.lift
      ((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToLeft (U : Set X) (V : Set X))))
      (-((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToRight (U : Set X) (V : Set X))))) ≫
    (AddCommGrpCat.biprodIsoProd _ _).hom

private theorem legacyDifferenceMorphism_hom {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    ConcreteCategory.hom (legacyDifferenceMorphism U V n) =
      IntegralMayerVietoris.differenceMap (U : Set X) (V : Set X) n := by
  ext x
  · change ConcreteCategory.hom
      (legacyDifferenceMorphism U V n ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x =
        ConcreteCategory.hom ((integralHomologyFunctor n).map
          (TopCat.ofHom (IntegralMayerVietoris.interToLeft (U : Set X) (V : Set X)))) x
    rw [legacyDifferenceMorphism, Category.assoc, biprodIsoProd_hom_comp_fst]
    have h := congrArg ConcreteCategory.hom (biprod.lift_fst
      (f := (integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToLeft (U : Set X) (V : Set X))))
      (g := -((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToRight (U : Set X) (V : Set X))))))
    exact DFunLike.congr_fun h x
  · change ConcreteCategory.hom
      (legacyDifferenceMorphism U V n ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x =
        -(ConcreteCategory.hom ((integralHomologyFunctor n).map
          (TopCat.ofHom (IntegralMayerVietoris.interToRight (U : Set X) (V : Set X)))) x)
    rw [legacyDifferenceMorphism, Category.assoc, biprodIsoProd_hom_comp_snd]
    have h := congrArg ConcreteCategory.hom (biprod.lift_snd
      (f := (integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToLeft (U : Set X) (V : Set X))))
      (g := -((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.interToRight (U : Set X) (V : Set X))))))
    exact DFunLike.congr_fun h x

private noncomputable def legacySumMorphism {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    AddCommGrpCat.of
        (IntegralSingularHomology n (U : Set X) ×
          IntegralSingularHomology n (V : Set X)) ⟶
      (integralHomologyFunctor n).obj
        (TopCat.of ((U : Set X) ∪ (V : Set X) : Set X)) :=
  (AddCommGrpCat.biprodIsoProd _ _).inv ≫
    biprod.desc
      ((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.leftToUnion (U : Set X) (V : Set X))))
      ((integralHomologyFunctor n).map
        (TopCat.ofHom (IntegralMayerVietoris.rightToUnion (U : Set X) (V : Set X))))

private theorem legacySumMorphism_hom {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    ConcreteCategory.hom (legacySumMorphism U V n) =
      IntegralMayerVietoris.sumMap (U : Set X) (V : Set X) n := by
  ext x
  rw [legacySumMorphism, AddCommGrpCat.biprodIsoProd_inv_comp_desc]
  rfl

private theorem differenceMorphism_comm {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (opensIntersectionHomologyIso U V n).inv ≫ legacyDifferenceMorphism U V n =
      integralMVToBiprod U V n ≫ (piecesHomologyIso U V n).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · change ConcreteCategory.hom
      (((opensIntersectionHomologyIso U V n).inv ≫ legacyDifferenceMorphism U V n) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x =
      ConcreteCategory.hom
      ((integralMVToBiprod U V n ≫ (piecesHomologyIso U V n).hom) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)) x
    apply ConcreteCategory.congr_hom
    simp only [legacyDifferenceMorphism, piecesHomologyIso, Iso.trans_hom,
      Category.assoc, biprodIsoProd_hom_comp_fst, biprod.lift_fst,
      biprod.mapIso_hom, biprod.map_fst, biprod.lift_fst_assoc, integralMVToBiprod,
      opensIntersectionHomologyIso, opensCarrierHomologyIso, Iso.symm_hom, Functor.mapIso_inv]
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · change ConcreteCategory.hom
      (((opensIntersectionHomologyIso U V n).inv ≫ legacyDifferenceMorphism U V n) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x =
      ConcreteCategory.hom
      ((integralMVToBiprod U V n ≫ (piecesHomologyIso U V n).hom) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)) x
    apply ConcreteCategory.congr_hom
    simp only [legacyDifferenceMorphism, piecesHomologyIso, Iso.trans_hom,
      Category.assoc, biprodIsoProd_hom_comp_snd, biprod.lift_snd,
      biprod.mapIso_hom, biprod.map_snd, biprod.lift_snd_assoc, integralMVToBiprod,
      opensIntersectionHomologyIso, opensCarrierHomologyIso, Iso.symm_hom, Functor.mapIso_inv]
    rw [Preadditive.comp_neg, Preadditive.neg_comp, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl

private theorem sumMorphism_comm {X : TopCat}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    (piecesHomologyIso U V n).hom ≫ legacySumMorphism U V n =
      integralMVFromBiprod U V n ≫ (opensUnionHomologyIso U V hcover n).inv := by
  apply biprod.hom_ext'
  · simp only [piecesHomologyIso, legacySumMorphism, Iso.trans_hom, Category.assoc,
      Iso.hom_inv_id_assoc, biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inl_desc,
      biprod.inl_desc_assoc,
      integralMVFromBiprod, opensCarrierHomologyIso, opensUnionHomologyIso,
      Iso.symm_hom, Functor.mapIso_inv]
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · simp only [piecesHomologyIso, legacySumMorphism, Iso.trans_hom, Category.assoc,
      Iso.hom_inv_id_assoc, biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc,
      biprod.inr_desc_assoc,
      integralMVFromBiprod, opensCarrierHomologyIso, opensUnionHomologyIso,
      Iso.symm_hom, Functor.mapIso_inv]
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- The connecting map in the set-subtype Mayer--Vietoris sequence. -/
public noncomputable def IntegralMayerVietorisData.legacyBoundary {X : TopCat}
    {U V : Opens X} {hcover : U ⊔ V = ⊤}
    (D : IntegralMayerVietorisData U V hcover) (n : ℕ) :
    IntegralSingularHomology (n + 1) ((U : Set X) ∪ (V : Set X) : Set X) →+
      IntegralSingularHomology n ((U : Set X) ∩ (V : Set X) : Set X) :=
  ConcreteCategory.hom
    ((opensUnionHomologyIso U V hcover (n + 1)).hom ≫ D.boundary n ≫
      (opensIntersectionHomologyIso U V n).inv)

/-- The transported connecting map is exact with the legacy difference and sum maps. -/
public theorem IntegralMayerVietorisData.legacyBoundary_exact {X : TopCat}
    {U V : Opens X} {hcover : U ⊔ V = ⊤}
    (D : IntegralMayerVietorisData U V hcover) (n : ℕ) :
    Function.Exact (IntegralMayerVietoris.sumMap (U : Set X) (V : Set X) (n + 1))
        (D.legacyBoundary n) ∧
      Function.Exact (D.legacyBoundary n)
        (IntegralMayerVietoris.differenceMap (U : Set X) (V : Set X) n) ∧
      Function.Exact (IntegralMayerVietoris.differenceMap (U : Set X) (V : Set X) n)
        (IntegralMayerVietoris.sumMap (U : Set X) (V : Set X) n) := by
  refine ⟨?_, ?_, ?_⟩
  · let ePieces := (piecesHomologyIso U V (n + 1)).addCommGroupIsoToAddEquiv
    let eUnion :=
      (opensUnionHomologyIso U V hcover (n + 1)).symm.addCommGroupIsoToAddEquiv
    let eIntersection :=
      (opensIntersectionHomologyIso U V n).symm.addCommGroupIsoToAddEquiv
    apply Function.Exact.of_ladder_addEquiv_of_exact ePieces eUnion eIntersection
    · rw [← legacySumMorphism_hom]
      exact congrArg ConcreteCategory.hom (sumMorphism_comm U V hcover (n + 1))
    · apply AddMonoidHom.ext
      intro x
      change ConcreteCategory.hom
          ((opensUnionHomologyIso U V hcover (n + 1)).inv ≫
            (opensUnionHomologyIso U V hcover (n + 1)).hom ≫ D.boundary n ≫
            (opensIntersectionHomologyIso U V n).inv) x =
        ConcreteCategory.hom
          (D.boundary n ≫ (opensIntersectionHomologyIso U V n).inv) x
      simp
    exact D.exact_at_union n
  · let eUnion :=
      (opensUnionHomologyIso U V hcover (n + 1)).symm.addCommGroupIsoToAddEquiv
    let eIntersection :=
      (opensIntersectionHomologyIso U V n).symm.addCommGroupIsoToAddEquiv
    let ePieces := (piecesHomologyIso U V n).addCommGroupIsoToAddEquiv
    apply Function.Exact.of_ladder_addEquiv_of_exact eUnion eIntersection ePieces
    · apply AddMonoidHom.ext
      intro x
      change ConcreteCategory.hom
          ((opensUnionHomologyIso U V hcover (n + 1)).inv ≫
            (opensUnionHomologyIso U V hcover (n + 1)).hom ≫ D.boundary n ≫
            (opensIntersectionHomologyIso U V n).inv) x =
        ConcreteCategory.hom
          (D.boundary n ≫ (opensIntersectionHomologyIso U V n).inv) x
      simp
    · rw [← legacyDifferenceMorphism_hom]
      exact congrArg ConcreteCategory.hom (differenceMorphism_comm U V n)
    exact D.exact_at_intersection n
  · let eIntersection :=
      (opensIntersectionHomologyIso U V n).symm.addCommGroupIsoToAddEquiv
    let ePieces := (piecesHomologyIso U V n).addCommGroupIsoToAddEquiv
    let eUnion := (opensUnionHomologyIso U V hcover n).symm.addCommGroupIsoToAddEquiv
    apply Function.Exact.of_ladder_addEquiv_of_exact eIntersection ePieces eUnion
    · rw [← legacyDifferenceMorphism_hom]
      exact congrArg ConcreteCategory.hom (differenceMorphism_comm U V n)
    · rw [← legacySumMorphism_hom]
      exact congrArg ConcreteCategory.hom (sumMorphism_comm U V hcover n)
    exact D.exact_at_biprod n

/-- The categorical binary-open-cover sequence supplies the exact set-subtype interface. -/
public theorem IntegralMayerVietorisData.toLegacyExactSequence {X : TopCat}
    {U V : Opens X} {hcover : U ⊔ V = ⊤}
    (D : IntegralMayerVietorisData U V hcover) :
    IntegralMayerVietoris.ExactSequence (U : Set X) (V : Set X) :=
  ⟨D.legacyBoundary, D.legacyBoundary_exact⟩

/-- An open-cover homology comparison yields the exact legacy Mayer--Vietoris sequence. -/
public theorem OpenCoverHomologyComparison.toLegacyExactSequence {X : TopCat}
    {U V : Opens X} (C : OpenCoverHomologyComparison U V) (hcover : U ⊔ V = ⊤) :
    IntegralMayerVietoris.ExactSequence (U : Set X) (V : Set X) :=
  (C.toIntegralMayerVietorisData hcover).toLegacyExactSequence

private def restrictedLeftOpen {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) : Opens (TopCat.of (A ∪ B : Set X)) where
  carrier := Subtype.val ⁻¹' A
  is_open' := hA.preimage continuous_subtype_val

private def restrictedRightOpen {X : Type} [TopologicalSpace X]
    (A B : Set X) (hB : IsOpen B) : Opens (TopCat.of (A ∪ B : Set X)) where
  carrier := Subtype.val ⁻¹' B
  is_open' := hB.preimage continuous_subtype_val

private theorem restrictedOpen_cover {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    restrictedLeftOpen A B hA ⊔ restrictedRightOpen A B hB = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact x.2

private def restrictedLeftHomeomorph {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) :
    (restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def restrictedRightHomeomorph {X : Type} [TopologicalSpace X]
    (A B : Set X) (hB : IsOpen B) :
    (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) ≃ₜ B where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Or.inr x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def restrictedIntersectionHomeomorph {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∩
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
      Set (A ∪ B : Set X)) ≃ₜ (A ∩ B : Set X) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Or.inl x.2.1⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def restrictedUnionHomeomorph {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∪
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
      Set (A ∪ B : Set X)) ≃ₜ (A ∪ B : Set X) where
  toFun := Subtype.val
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

private theorem integralSingularHomologyMap_comp' {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap n (g.comp f) =
      (integralSingularHomologyMap n g).comp (integralSingularHomologyMap n f) := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl,
    Functor.map_comp]
  rfl

private theorem integralSingularHomologyMap_comp_apply {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) (x : IntegralSingularHomology n X) :
    integralSingularHomologyMap n g (integralSingularHomologyMap n f x) =
      integralSingularHomologyMap n (g.comp f) x := by
  rw [integralSingularHomologyMap_comp']
  rfl

private theorem integralSingularHomologyEquiv_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (e : X ≃ₜ Y)
    (x : IntegralSingularHomology n X) :
    integralSingularHomologyEquiv n e x =
      integralSingularHomologyMap n ⟨e, e.continuous⟩ x := by
  rfl

private noncomputable def restrictedLeftHomologyEquiv {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (n : ℕ) :
    IntegralSingularHomology n (restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ≃+
      IntegralSingularHomology n A :=
  integralSingularHomologyEquiv n (restrictedLeftHomeomorph A B hA)

private noncomputable def restrictedRightHomologyEquiv {X : Type} [TopologicalSpace X]
    (A B : Set X) (hB : IsOpen B) (n : ℕ) :
    IntegralSingularHomology n (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) ≃+
      IntegralSingularHomology n B :=
  integralSingularHomologyEquiv n (restrictedRightHomeomorph A B hB)

private noncomputable def restrictedIntersectionHomologyEquiv
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (n : ℕ) :
    IntegralSingularHomology n
        ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∩
          (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
          Set (A ∪ B : Set X)) ≃+
      IntegralSingularHomology n (A ∩ B : Set X) :=
  integralSingularHomologyEquiv n (restrictedIntersectionHomeomorph A B hA hB)

private noncomputable def restrictedUnionHomologyEquiv
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (n : ℕ) :
    IntegralSingularHomology n
        ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∪
          (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
          Set (A ∪ B : Set X)) ≃+
      IntegralSingularHomology n (A ∪ B : Set X) :=
  integralSingularHomologyEquiv n (restrictedUnionHomeomorph A B hA hB)

private theorem restrictedDifferenceMap_comm {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (IntegralMayerVietoris.differenceMap A B n).comp
        (restrictedIntersectionHomologyEquiv A B hA hB n : _ →+ _) =
      ((restrictedLeftHomologyEquiv A B hA n).prodCongr
        (restrictedRightHomologyEquiv A B hB n) : _ →+ _).comp
          (IntegralMayerVietoris.differenceMap
            (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
            (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) n) := by
  ext x
  · change integralSingularHomologyMap n (IntegralMayerVietoris.interToLeft A B)
        (restrictedIntersectionHomologyEquiv A B hA hB n x) =
      restrictedLeftHomologyEquiv A B hA n
        (integralSingularHomologyMap n
          (IntegralMayerVietoris.interToLeft
            (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
            (restrictedRightOpen A B hB : Set (A ∪ B : Set X))) x)
    simp only [restrictedIntersectionHomologyEquiv, restrictedLeftHomologyEquiv]
    rw [integralSingularHomologyEquiv_apply,
      integralSingularHomologyEquiv_apply]
    rw [integralSingularHomologyMap_comp_apply,
      integralSingularHomologyMap_comp_apply]
    rfl
  · change -integralSingularHomologyMap n (IntegralMayerVietoris.interToRight A B)
        (restrictedIntersectionHomologyEquiv A B hA hB n x) =
      restrictedRightHomologyEquiv A B hB n
        (-integralSingularHomologyMap n
          (IntegralMayerVietoris.interToRight
            (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
            (restrictedRightOpen A B hB : Set (A ∪ B : Set X))) x)
    simp only [restrictedIntersectionHomologyEquiv, restrictedRightHomologyEquiv]
    rw [integralSingularHomologyEquiv_apply,
      integralSingularHomologyEquiv_apply]
    rw [map_neg, integralSingularHomologyMap_comp_apply,
      integralSingularHomologyMap_comp_apply]
    rfl

private theorem restrictedSumMap_comm {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (IntegralMayerVietoris.sumMap A B n).comp
        ((restrictedLeftHomologyEquiv A B hA n).prodCongr
          (restrictedRightHomologyEquiv A B hB n) : _ →+ _) =
      (restrictedUnionHomologyEquiv A B hA hB n : _ →+ _).comp
        (IntegralMayerVietoris.sumMap
          (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
          (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) n) := by
  ext x
  change
    integralSingularHomologyMap n (IntegralMayerVietoris.leftToUnion A B)
          (restrictedLeftHomologyEquiv A B hA n x.1) +
        integralSingularHomologyMap n (IntegralMayerVietoris.rightToUnion A B)
          (restrictedRightHomologyEquiv A B hB n x.2) =
      restrictedUnionHomologyEquiv A B hA hB n
        (integralSingularHomologyMap n
            (IntegralMayerVietoris.leftToUnion
              (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
              (restrictedRightOpen A B hB : Set (A ∪ B : Set X))) x.1 +
          integralSingularHomologyMap n
            (IntegralMayerVietoris.rightToUnion
              (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
              (restrictedRightOpen A B hB : Set (A ∪ B : Set X))) x.2)
  simp only [restrictedLeftHomologyEquiv, restrictedRightHomologyEquiv,
    restrictedUnionHomologyEquiv]
  rw [integralSingularHomologyEquiv_apply, integralSingularHomologyEquiv_apply,
    integralSingularHomologyEquiv_apply]
  rw [map_add, integralSingularHomologyMap_comp_apply,
    integralSingularHomologyMap_comp_apply, integralSingularHomologyMap_comp_apply,
    integralSingularHomologyMap_comp_apply]
  rfl

private noncomputable def rebasedBoundary {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (boundary : ∀ n : ℕ,
      IntegralSingularHomology (n + 1)
          ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∪
            (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
            Set (A ∪ B : Set X)) →+
        IntegralSingularHomology n
          ((restrictedLeftOpen A B hA : Set (A ∪ B : Set X)) ∩
            (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) :
            Set (A ∪ B : Set X))) (n : ℕ) :
    IntegralSingularHomology (n + 1) (A ∪ B : Set X) →+
      IntegralSingularHomology n (A ∩ B : Set X) :=
  (restrictedIntersectionHomologyEquiv A B hA hB n : _ →+ _).comp
    ((boundary n).comp
      ((restrictedUnionHomologyEquiv A B hA hB (n + 1)).symm : _ →+ _))

private theorem legacyExactSequence_of_restricted {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (E : IntegralMayerVietoris.ExactSequence
      (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
      (restrictedRightOpen A B hB : Set (A ∪ B : Set X))) :
    IntegralMayerVietoris.ExactSequence A B := by
  obtain ⟨boundary, hExact⟩ := E
  refine ⟨rebasedBoundary A B hA hB boundary, fun n ↦ ⟨?_, ?_, ?_⟩⟩
  · let ePieces := (restrictedLeftHomologyEquiv A B hA (n + 1)).prodCongr
      (restrictedRightHomologyEquiv A B hB (n + 1))
    let eUnion := restrictedUnionHomologyEquiv A B hA hB (n + 1)
    let eIntersection := restrictedIntersectionHomologyEquiv A B hA hB n
    apply Function.Exact.of_ladder_addEquiv_of_exact ePieces eUnion eIntersection
      (f₁₂ := IntegralMayerVietoris.sumMap
        (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) (n + 1))
      (f₂₃ := boundary n) (g₁₂ := IntegralMayerVietoris.sumMap A B (n + 1))
      (g₂₃ := rebasedBoundary A B hA hB boundary n)
    · exact restrictedSumMap_comm A B hA hB (n + 1)
    · apply AddMonoidHom.ext
      intro x
      simp [eUnion, eIntersection, rebasedBoundary]
    exact (hExact n).1
  · let eUnion := restrictedUnionHomologyEquiv A B hA hB (n + 1)
    let eIntersection := restrictedIntersectionHomologyEquiv A B hA hB n
    let ePieces := (restrictedLeftHomologyEquiv A B hA n).prodCongr
      (restrictedRightHomologyEquiv A B hB n)
    apply Function.Exact.of_ladder_addEquiv_of_exact eUnion eIntersection ePieces
      (f₁₂ := boundary n)
      (f₂₃ := IntegralMayerVietoris.differenceMap
        (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) n)
      (g₁₂ := rebasedBoundary A B hA hB boundary n)
      (g₂₃ := IntegralMayerVietoris.differenceMap A B n)
    · apply AddMonoidHom.ext
      intro x
      simp [eUnion, eIntersection, rebasedBoundary]
    · exact restrictedDifferenceMap_comm A B hA hB n
    exact (hExact n).2.1
  · let eIntersection := restrictedIntersectionHomologyEquiv A B hA hB n
    let ePieces := (restrictedLeftHomologyEquiv A B hA n).prodCongr
      (restrictedRightHomologyEquiv A B hB n)
    let eUnion := restrictedUnionHomologyEquiv A B hA hB n
    apply Function.Exact.of_ladder_addEquiv_of_exact eIntersection ePieces eUnion
      (f₁₂ := IntegralMayerVietoris.differenceMap
        (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) n)
      (f₂₃ := IntegralMayerVietoris.sumMap
        (restrictedLeftOpen A B hA : Set (A ∪ B : Set X))
        (restrictedRightOpen A B hB : Set (A ∪ B : Set X)) n)
      (g₁₂ := IntegralMayerVietoris.differenceMap A B n)
      (g₂₃ := IntegralMayerVietoris.sumMap A B n)
    · exact restrictedDifferenceMap_comm A B hA hB n
    · exact restrictedSumMap_comm A B hA hB n
    exact (hExact n).2.2

/-- Integral singular-homology Mayer--Vietoris for arbitrary open subsets, obtained by applying
the binary-cover theorem inside their union and transporting all four subtype terms. -/
public theorem integralMayerVietorisExactSequence_of_isOpen
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    IntegralMayerVietoris.ExactSequence A B := by
  let U := restrictedLeftOpen A B hA
  let V := restrictedRightOpen A B hB
  have hcover : U ⊔ V = ⊤ := restrictedOpen_cover A B hA hB
  let C : OpenCoverHomologyComparison U V := openCoverHomologyComparisonOfCover hcover
  exact legacyExactSequence_of_restricted A B hA hB (C.toLegacyExactSequence hcover)

end SphereSixComplex.BinaryOpenCover
