module

public import SphereSixComplex.Topology.BoundarySevenCechOrderedTuples
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Ordered-intersection decomposition of the simplicial-face Cech nerve

In a fixed outer Cech degree, a compatible ordered tuple of facets of the seven-simplex
has common simplicial face indexed by the complement of the tuple's support.  Full-support
tuples have empty common face and are omitted.  This file identifies the coproduct of all
remaining common faces with the corresponding object of the canonical pullback Cech nerve.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

/-- The common simplicial face belonging to a proper ordered Cech tuple. -/
public abbrev boundarySevenOrderedSourceCommonFace
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) : SSet.{0} :=
  (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0})

/-- The common face includes into the facet selected in slot `i`, expressed in the standard
`Delta[6]` parametrization used by the face presentation. -/
public noncomputable def boundarySevenOrderedSourceCommonFaceToFacet
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourceCommonFace a ⟶ (Δ[6] : SSet.{0}) :=
  SSet.Subcomplex.homOfLE (by
      rw [SSet.stdSimplex.face_le_face_iff]
      intro j hj
      apply Finset.mem_compl.mpr
      simp only [Finset.mem_singleton]
      intro hja
      subst j
      exact (Finset.mem_compl.mp hj) (a.1.mem_support i)) ≫
    (SSet.stdSimplex.faceSingletonComplIso (a.1 i)).inv

/-- The common face includes into the simplicial boundary. -/
public noncomputable def boundarySevenOrderedSourceCommonFaceToBoundary
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenOrderedSourceCommonFace a ⟶ (∂Δ[7] : SSet.{0}) :=
  boundarySevenOrderedSourceCommonFaceToFacet a 0 ≫
    SSet.boundary.ι (a.1 0)

@[reassoc]
public theorem boundarySevenOrderedSourceCommonFaceToBoundary_comp_inclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenOrderedSourceCommonFaceToBoundary a ≫
        (SSet.boundary 7).ι =
      (SSet.stdSimplex.face a.1.supportᶜ).ι := by
  simp [boundarySevenOrderedSourceCommonFaceToBoundary,
    boundarySevenOrderedSourceCommonFaceToFacet]

@[reassoc]
public theorem boundarySevenOrderedSourceCommonFaceToFacet_comp_boundary
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourceCommonFaceToFacet a i ≫
        SSet.boundary.ι (a.1 i) =
      boundarySevenOrderedSourceCommonFaceToBoundary a := by
  apply (cancel_mono (SSet.boundary 7).ι).1
  simp only [Category.assoc,
    boundarySevenOrderedSourceCommonFaceToFacet,
    SSet.boundary.faceSingletonComplIso_inv_ι,
    SSet.boundary.faceι_ι,
    SSet.Subcomplex.homOfLE_ι]
  exact (boundarySevenOrderedSourceCommonFaceToBoundary_comp_inclusion a).symm

/-- The leg from a common face to the coproduct presentation object in slot `i`. -/
public noncomputable def boundarySevenOrderedSourcePresentationLeg
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourceCommonFace a ⟶
      boundarySevenSimplicialFacePresentationSource :=
  boundarySevenOrderedSourceCommonFaceToFacet a i ≫
    Sigma.ι (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0})) (a.1 i)

@[reassoc]
public theorem boundarySevenOrderedSourcePresentationLeg_comp_presentation
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourcePresentationLeg a i ≫
        boundarySevenSimplicialFacePresentation =
      boundarySevenOrderedSourceCommonFaceToBoundary a := by
  simp [boundarySevenOrderedSourcePresentationLeg,
    boundarySevenOrderedSourceCommonFaceToFacet_comp_boundary]

/-- A common face determines a point of the pullback Cech object. -/
public noncomputable def boundarySevenOrderedSourceCechSummand
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenOrderedSourceCommonFace a ⟶
      boundarySevenSimplicialFaceAugmentedCechNerve.left.obj n :=
  WidePullback.lift (boundarySevenOrderedSourceCommonFaceToBoundary a)
    (boundarySevenOrderedSourcePresentationLeg a)
    (boundarySevenOrderedSourcePresentationLeg_comp_presentation a)

/-- The canonical map from the coproduct of proper common faces to the source Cech object. -/
public noncomputable def boundarySevenOrderedSourceToCech
    (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : BoundarySevenProperCechTuple n =>
      boundarySevenOrderedSourceCommonFace a) ⟶
      boundarySevenSimplicialFaceAugmentedCechNerve.left.obj n :=
  Sigma.desc boundarySevenOrderedSourceCechSummand

/-- Projection from the source Cech object to one selected presentation leg. -/
public noncomputable def boundarySevenSourceCechProjection
    (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    boundarySevenSimplicialFaceAugmentedCechNerve.left.obj n ⟶
      boundarySevenSimplicialFacePresentationSource :=
  WidePullback.π
    (fun _ : Fin (n.unop.len + 1) ↦
      boundarySevenSimplicialFacePresentation) i

@[reassoc]
public theorem boundarySevenOrderedSourceCechSummand_comp_projection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourceCechSummand a ≫
      boundarySevenSourceCechProjection n i =
      boundarySevenOrderedSourcePresentationLeg a i := by
  change boundarySevenOrderedSourceCechSummand a ≫
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦
        boundarySevenSimplicialFacePresentation) i =
    boundarySevenOrderedSourcePresentationLeg a i
  unfold boundarySevenOrderedSourceCechSummand
  exact WidePullback.lift_π
    (fun _ : Fin (n.unop.len + 1) ↦
      boundarySevenSimplicialFacePresentation)
    (boundarySevenOrderedSourceCommonFaceToBoundary a)
    (boundarySevenOrderedSourcePresentationLeg a)
    (boundarySevenOrderedSourcePresentationLeg_comp_presentation a) i

@[reassoc]
public theorem boundarySevenOrderedSourceToCech_comp_projection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : BoundarySevenProperCechTuple n ↦
        boundarySevenOrderedSourceCommonFace b) a ≫
        boundarySevenOrderedSourceToCech n ≫
        boundarySevenSourceCechProjection n i =
      boundarySevenOrderedSourcePresentationLeg a i := by
  rw [← Category.assoc, boundarySevenOrderedSourceToCech, Sigma.ι_desc]
  exact boundarySevenOrderedSourceCechSummand_comp_projection a i

public noncomputable def boundarySevenSourceCoproductAppIsColimit
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((∐ X).obj q) (fun i => (Sigma.ι X i).app q)) :=
  isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj q) X
    (fun i ↦ Sigma.ι X i) (coproductIsCoproduct X)

public theorem boundarySevenSourceCoproduct_app_jointly_surjective
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ)
    (x : (∐ X).obj q) : ∃ i y, (Sigma.ι X i).app q y = x :=
  Cofan.inj_jointly_surjective_of_isColimit
    (boundarySevenSourceCoproductAppIsColimit X q) x

public theorem boundarySevenSourceCoproduct_app_index_eq
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ)
    {i j : ι} (x : (X i).obj q) (y : (X j).obj q)
    (h : (Sigma.ι X i).app q x = (Sigma.ι X j).app q y) : i = j :=
  Cofan.eq_of_inj_apply_eq_of_isColimit
    (boundarySevenSourceCoproductAppIsColimit X q) x y h

public theorem boundarySevenSourceCoproduct_app_injective
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ) (i : ι) :
    Function.Injective ((Sigma.ι X i).app q) :=
  Cofan.inj_injective_of_isColimit
    (boundarySevenSourceCoproductAppIsColimit X q) i

public theorem boundarySevenSourceCech_app_ext
    {n q : SimplexCategoryᵒᵖ}
    (x y : (boundarySevenSimplicialFaceAugmentedCechNerve.left.obj n).obj q)
    (h : ∀ i, (boundarySevenSourceCechProjection n i).app q x =
      (boundarySevenSourceCechProjection n i).app q y) : x = y := by
  let arrows := fun _ : Fin (n.unop.len + 1) ↦
    boundarySevenSimplicialFacePresentation
  let D := WidePullbackShape.wideCospan
    (boundarySevenSimplicialFacePresentationArrow.right)
    (fun _ : Fin (n.unop.len + 1) ↦
      boundarySevenSimplicialFacePresentationArrow.left) arrows
  let ev := (evaluation SimplexCategoryᵒᵖ (Type _)).obj q
  have hlim : IsLimit (Functor.mapCone ev (limit.cone D)) :=
    isLimitOfPreserves ev (limit.isLimit D)
  apply (Types.isLimitEquivSections hlim).injective
  apply Subtype.ext
  funext j
  cases j with
  | none =>
      have hx := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows 0)
      have hy := congrArg (fun k ↦ k.app q y) (WidePullback.π_arrow arrows 0)
      exact hx.symm.trans
        ((congrArg (fun z ↦ boundarySevenSimplicialFacePresentation.app q z)
          (h 0)).trans hy)
  | some i => exact h i

public theorem boundarySevenOrderedSourceCommonFaceToFacet_app_injective
    {n q : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Function.Injective
      ((boundarySevenOrderedSourceCommonFaceToFacet a i).app q) := by
  let _ : Mono (boundarySevenOrderedSourceCommonFaceToFacet a i) := by
    dsimp [boundarySevenOrderedSourceCommonFaceToFacet]
    infer_instance
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

public theorem boundarySevenOrderedSourceToCech_app_injective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Injective ((boundarySevenOrderedSourceToCech n).app q) := by
  let X := fun a : BoundarySevenProperCechTuple n ↦
    boundarySevenOrderedSourceCommonFace a
  let Y := fun _j : Fin 8 ↦ (Δ[6] : SSet.{0})
  intro x y hxy
  obtain ⟨a, xa, rfl⟩ :=
    boundarySevenSourceCoproduct_app_jointly_surjective X q x
  obtain ⟨b, xb, rfl⟩ :=
    boundarySevenSourceCoproduct_app_jointly_surjective X q y
  have hcoord (i : Fin (n.unop.len + 1)) :
      (Sigma.ι Y (a.1 i)).app q
          ((boundarySevenOrderedSourceCommonFaceToFacet a i).app q xa) =
        (Sigma.ι Y (b.1 i)).app q
          ((boundarySevenOrderedSourceCommonFaceToFacet b i).app q xb) := by
    have hproj := congrArg
      (fun z ↦ (boundarySevenSourceCechProjection n i).app q z) hxy
    have ha := congrArg (fun k ↦ k.app q xa)
      (boundarySevenOrderedSourceToCech_comp_projection a i)
    have hb := congrArg (fun k ↦ k.app q xb)
      (boundarySevenOrderedSourceToCech_comp_projection b i)
    exact ha.symm.trans (hproj.trans hb)
  have hab : a = b := by
    apply Subtype.ext
    funext i
    exact boundarySevenSourceCoproduct_app_index_eq Y q _ _ (hcoord i)
  subst b
  have hfacet :
      (boundarySevenOrderedSourceCommonFaceToFacet a 0).app q xa =
        (boundarySevenOrderedSourceCommonFaceToFacet a 0).app q xb :=
    boundarySevenSourceCoproduct_app_injective Y q (a.1 0) (hcoord 0)
  have habSimplex : xa = xb :=
    boundarySevenOrderedSourceCommonFaceToFacet_app_injective a 0 hfacet
  exact congrArg ((Sigma.ι X a).app q) habSimplex

public theorem boundarySevenSimplicialFacePresentation_iota_app_injective
    (q : SimplexCategoryᵒᵖ) (i : Fin 8) :
    Function.Injective ((SSet.boundary.ι i).app q) := by
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

public theorem boundarySevenOrderedSourceToCech_app_surjective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((boundarySevenOrderedSourceToCech n).app q) := by
  rcases q with ⟨⟨d⟩⟩
  let q : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk d)
  let X := fun a : BoundarySevenProperCechTuple n ↦
    boundarySevenOrderedSourceCommonFace a
  let Y := fun _j : Fin 8 ↦ (Δ[6] : SSet.{0})
  intro x
  have hex (i : Fin (n.unop.len + 1)) :
      ∃ j y, (Sigma.ι Y j).app q y =
        (boundarySevenSourceCechProjection n i).app q x :=
    boundarySevenSourceCoproduct_app_jointly_surjective Y q _
  choose a y hy using hex
  let arrows := fun _ : Fin (n.unop.len + 1) ↦
    boundarySevenSimplicialFacePresentation
  have hboundary (i : Fin (n.unop.len + 1)) :
      (SSet.boundary.ι (a i)).app q (y i) =
        (SSet.boundary.ι (a 0)).app q (y 0) := by
    have hpresi := congrArg (fun k ↦ k.app q (y i))
      (boundarySevenSimplicialFacePresentation_iota (a i))
    have hpres0 := congrArg (fun k ↦ k.app q (y 0))
      (boundarySevenSimplicialFacePresentation_iota (a 0))
    have hyi := congrArg
      (fun z ↦ boundarySevenSimplicialFacePresentation.app q z) (hy i)
    have hy0 := congrArg
      (fun z ↦ boundarySevenSimplicialFacePresentation.app q z) (hy 0)
    have hpi := congrArg (fun k ↦ k.app q x)
      (WidePullback.π_arrow arrows i)
    have hp0 := congrArg (fun k ↦ k.app q x)
      (WidePullback.π_arrow arrows 0)
    exact hpresi.symm.trans
      (hyi.trans (hpi.trans (hp0.symm.trans (hy0.symm.trans hpres0))))
  let zBoundary := (SSet.boundary.ι (a 0)).app q (y 0)
  let zOrder := (SSet.stdSimplex.objEquiv zBoundary.1).toOrderHom
  have havoid (k : Fin (q.unop.len + 1)) : zOrder k ∉
      BoundarySevenCechTuple.support a := by
    intro hk
    obtain ⟨i, -, hai⟩ := Finset.mem_image.mp hk
    have hiFace :=
      ((SSet.stdSimplex.faceSingletonComplIso (a i)).hom.app q (y i)).2
    rw [SSet.stdSimplex.mem_face_iff] at hiFace
    have hne :
        (SSet.stdSimplex.objEquiv
            ((SSet.stdSimplex.faceSingletonComplIso (a i)).hom.app q (y i)).1).toOrderHom k ≠
          a i := by
      dsimp [q] at hiFace ⊢
      simpa using hiFace k
    have hfacetBoundary :
        (SSet.stdSimplex.faceSingletonComplIso (a i)).hom ≫
            SSet.boundary.faceι (a i) =
          SSet.boundary.ι (a i) := by
      apply (cancel_mono (SSet.boundary 7).ι).1
      simp
    have himage := congrArg Subtype.val
      (ConcreteCategory.congr_hom (congr_app hfacetBoundary q) (y i))
    apply hne
    have himagek := congrArg
      (fun t : (Δ[7] : SSet.{0}).obj q ↦
        (SSet.stdSimplex.objEquiv t).toOrderHom k) himage
    have hboundaryk := congrArg
      (fun t : (∂Δ[7] : SSet.{0}).obj q ↦
        (SSet.stdSimplex.objEquiv t.1).toOrderHom k) (hboundary i)
    exact himagek.trans (hboundaryk.trans hai.symm)
  have hproper : BoundarySevenCechTuple.support a ≠ Finset.univ := by
    intro ha
    exact havoid 0 (by rw [ha]; simp)
  let ap : BoundarySevenProperCechTuple n := ⟨a, hproper⟩
  let z : (boundarySevenOrderedSourceCommonFace ap).obj q :=
    ⟨zBoundary.1, by
      rw [SSet.stdSimplex.mem_face_iff]
      intro k
      dsimp [q, zOrder] at havoid ⊢
      simpa using havoid k⟩
  have hz (i : Fin (n.unop.len + 1)) :
      (boundarySevenOrderedSourceCommonFaceToFacet ap i).app q z = y i := by
    apply boundarySevenSimplicialFacePresentation_iota_app_injective q (a i)
    have hfac :
        (SSet.boundary.ι (a i)).app q
            ((boundarySevenOrderedSourceCommonFaceToFacet ap i).app q z) =
          (boundarySevenOrderedSourceCommonFaceToBoundary ap).app q z := by
      simpa using ConcreteCategory.congr_hom
        (congr_app
          (boundarySevenOrderedSourceCommonFaceToFacet_comp_boundary ap i) q) z
    rw [hfac]
    have hcommon :
        (boundarySevenOrderedSourceCommonFaceToBoundary ap).app q z = zBoundary := by
      apply Subtype.ext
      have hinc := ConcreteCategory.congr_hom
        (congr_app
          (boundarySevenOrderedSourceCommonFaceToBoundary_comp_inclusion ap) q) z
      change ((boundarySevenOrderedSourceCommonFaceToBoundary ap).app q z).1 = z.1 at hinc
      simpa [z] using hinc
    rw [hcommon]
    exact (hboundary i).symm
  refine ⟨(Sigma.ι X ap).app q z, ?_⟩
  apply boundarySevenSourceCech_app_ext
  intro i
  calc
    (boundarySevenSourceCechProjection n i).app q
        ((boundarySevenOrderedSourceToCech n).app q ((Sigma.ι X ap).app q z)) =
      (Sigma.ι Y (a i)).app q
        ((boundarySevenOrderedSourceCommonFaceToFacet ap i).app q z) := by
          simpa [X, Y, boundarySevenOrderedSourcePresentationLeg] using
            congrArg (fun k ↦ k.app q z)
            (boundarySevenOrderedSourceToCech_comp_projection ap i)
    _ = (Sigma.ι Y (a i)).app q (y i) := congrArg _ (hz i)
    _ = (boundarySevenSourceCechProjection n i).app q x := hy i

/-- In every outer degree, the coproduct of proper common simplicial faces is canonically
isomorphic to the corresponding object of the simplicial-face Cech nerve. -/
public noncomputable def boundarySevenOrderedSourceCechIso
    (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : BoundarySevenProperCechTuple n =>
      boundarySevenOrderedSourceCommonFace a) ≅
      boundarySevenSimplicialFaceAugmentedCechNerve.left.obj n := by
  let _ : ∀ q, IsIso ((boundarySevenOrderedSourceToCech n).app q) := fun q ↦
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨boundarySevenOrderedSourceToCech_app_injective n q,
        boundarySevenOrderedSourceToCech_app_surjective n q⟩
  let _ : IsIso (boundarySevenOrderedSourceToCech n) :=
    NatIso.isIso_of_isIso_app (boundarySevenOrderedSourceToCech n)
  exact asIso (boundarySevenOrderedSourceToCech n)

@[simp]
public theorem boundarySevenOrderedSourceCechIso_hom
    (n : SimplexCategoryᵒᵖ) :
    (boundarySevenOrderedSourceCechIso n).hom =
      boundarySevenOrderedSourceToCech n :=
  rfl

@[reassoc]
public theorem boundarySevenOrderedSourceCechIso_hom_comp_projection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : BoundarySevenProperCechTuple n ↦
        boundarySevenOrderedSourceCommonFace b) a ≫
        (boundarySevenOrderedSourceCechIso n).hom ≫
        boundarySevenSourceCechProjection n i =
      boundarySevenOrderedSourcePresentationLeg a i := by
  rw [boundarySevenOrderedSourceCechIso_hom]
  exact boundarySevenOrderedSourceToCech_comp_projection a i

end SphereSixComplex
