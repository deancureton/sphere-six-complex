module

public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Objectwise identification of the ordered and pullback Čech nerves

The ordered tuples used in the Section 7 complex are precisely the choices of summands in
Mathlib's wide-pullback Čech nerve.  This file constructs the canonical isomorphism in each
outer simplicial degree; it makes no chain-level or outer-naturality claim.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

namespace SectionSevenCechNerveChainIdentification

open SectionSevenStarIntersectionChainModels

variable (A : FourPieceStarGluingData)

private abbrev U := (sectionSevenStarOpenCover A).piece

private def intersectionToMember {n : SimplexCategoryᵒᵖ} (a : CechTuple n)
    (i : Fin (n.unop.len + 1)) :
    TopCat.of (finiteCoverIntersection (U A) a.support) ⟶ TopCat.of (U A (a i)) :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨x.1, by
        exact (mem_finiteCoverIntersection_iff (U A) a.support x).mp x.2
          (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
      continuous_toFun := by fun_prop }

private theorem intersectionToMember_comp_inclusion {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) (i : Fin (n.unop.len + 1)) :
    intersectionToMember A a i ≫
      topologicalSubsetInclusion (TopCat.of (GluedSpace A.glueData)) (U A (a i)) =
      topologicalSubsetInclusion (TopCat.of (GluedSpace A.glueData))
        (finiteCoverIntersection (U A) a.support) := by
  ext x
  rfl

private noncomputable def intersectionToPresentationLeg {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) (i : Fin (n.unop.len + 1)) :
    TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support)) ⟶
      finiteCoverPresentationSource (U A) :=
  TopCat.toSSet.map (intersectionToMember A a i) ≫
    Sigma.ι (fun j ↦ TopCat.toSSet.obj (TopCat.of (U A j))) (a i)

private noncomputable def intersectionToSmall {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) :
    TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support)) ⟶
      coverSmallSingularSubcomplex (TopCat.of (GluedSpace A.glueData)) (U A) :=
  TopCat.toSSet.map (intersectionToMember A a 0) ≫
    coverMemberToSmallSingularSet (TopCat.of (GluedSpace A.glueData)) (U A) (a 0)

private theorem intersectionToPresentationLeg_condition {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) (i : Fin (n.unop.len + 1)) :
    intersectionToPresentationLeg A a i ≫ finiteCoverPresentation (U A) =
      intersectionToSmall A a := by
  rw [← cancel_mono
    (coverSmallSingularSubcomplex (TopCat.of (GluedSpace A.glueData)) (U A)).ι]
  simp only [intersectionToPresentationLeg, finiteCoverPresentation, Category.assoc,
    Sigma.ι_desc_assoc, coverMemberToSmallSingularSet_comp_inclusion,
    intersectionToSmall]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private noncomputable def intersectionToCechSummand {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) :
    TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support)) ⟶
      (finiteCoverCechNerve (U A)).obj n :=
  finiteCoverCechLift (U A) n (intersectionToSmall A a)
    (intersectionToPresentationLeg A a)
    (intersectionToPresentationLeg_condition A a)

private noncomputable def orderedIntersectionsToCech (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : CechTuple n ↦
      TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support))) ⟶
      (finiteCoverCechNerve (U A)).obj n :=
  Sigma.desc (intersectionToCechSummand A)

private noncomputable def sSetCoproductAppIsColimit {ι : Type} (X : ι → SSet)
    (q : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((∐ X).obj q) (fun i ↦ (Sigma.ι X i).app q)) :=
  isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj q) X
    (fun i ↦ Sigma.ι X i) (coproductIsCoproduct X)

private noncomputable def sSetCoproductAppEquiv {ι : Type} (X : ι → SSet)
    (q : SimplexCategoryᵒᵖ) :
    (Σ i, (X i).obj q) ≃ (∐ X).obj q :=
  CofanTypes.equivOfIsColimit
    ((Cofan.isColimit_cofanTypes_iff _).2 ⟨sSetCoproductAppIsColimit X q⟩)

private theorem sSetCoproduct_app_jointly_surjective {ι : Type} (X : ι → SSet)
    (q : SimplexCategoryᵒᵖ) (x : (∐ X).obj q) :
    ∃ i y, (Sigma.ι X i).app q y = x :=
  Cofan.inj_jointly_surjective_of_isColimit (sSetCoproductAppIsColimit X q) x

private theorem sSetCoproduct_app_index_eq {ι : Type} (X : ι → SSet)
    (q : SimplexCategoryᵒᵖ) {i j : ι} (x : (X i).obj q) (y : (X j).obj q)
    (h : (Sigma.ι X i).app q x = (Sigma.ι X j).app q y) : i = j :=
  Cofan.eq_of_inj_apply_eq_of_isColimit (sSetCoproductAppIsColimit X q) x y h

private theorem sSetCoproduct_app_injective {ι : Type} (X : ι → SSet)
    (q : SimplexCategoryᵒᵖ) (i : ι) : Function.Injective ((Sigma.ι X i).app q) :=
  Cofan.inj_injective_of_isColimit (sSetCoproductAppIsColimit X q) i

private noncomputable def cechProjection (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    (finiteCoverCechNerve (U A)).obj n ⟶ finiteCoverPresentationSource (U A) :=
  finiteCoverCechProjection (U A) n i

private theorem cech_app_ext {n q : SimplexCategoryᵒᵖ}
    (x y : ((finiteCoverCechNerve (U A)).obj n).obj q)
    (h : ∀ i, (cechProjection A n i).app q x = (cechProjection A n i).app q y) : x = y := by
  let arrows := fun _ : Fin (n.unop.len + 1) ↦ finiteCoverPresentation (U A)
  let D := WidePullbackShape.wideCospan
    (coverSmallSingularSubcomplex (TopCat.of (GluedSpace A.glueData)) (U A) : SSet)
    (fun _ : Fin (n.unop.len + 1) ↦ finiteCoverPresentationSource (U A)) arrows
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
      exact hx.symm.trans ((congrArg (fun z ↦ (arrows 0).app q z) (h 0)).trans hy)
  | some i => exact h i

private theorem orderedIntersectionsToCech_π {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : CechTuple n ↦
        TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) b.support))) a ≫
        orderedIntersectionsToCech A n ≫
        cechProjection A n i =
      TopCat.toSSet.map (intersectionToMember A a i) ≫
        Sigma.ι (fun j ↦ TopCat.toSSet.obj (TopCat.of (U A j))) (a i) := by
  rw [← Category.assoc, orderedIntersectionsToCech, Sigma.ι_desc]
  simpa only [intersectionToCechSummand, cechProjection,
    intersectionToPresentationLeg] using
      finiteCoverCechLift_projection (U A) n (intersectionToSmall A a)
        (intersectionToPresentationLeg A a)
        (intersectionToPresentationLeg_condition A a) i

private theorem intersectionToMember_app_injective {n q : SimplexCategoryᵒᵖ}
    (a : CechTuple n) (i : Fin (n.unop.len + 1)) :
    Function.Injective ((TopCat.toSSet.map (intersectionToMember A a i)).app q) := by
  let _ : Mono (intersectionToMember A a i) :=
    (TopCat.mono_iff_injective _).mpr
      (fun _ _ h ↦ Subtype.ext (congrArg (fun z : U A (a i) ↦ z.1) h))
  let _ : Mono (TopCat.toSSet.map (intersectionToMember A a i)) :=
    Functor.map_mono TopCat.toSSet _
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

private theorem orderedIntersectionsToCech_app_injective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Injective ((orderedIntersectionsToCech A n).app q) := by
  let X := fun a : CechTuple n ↦
    TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support))
  let Y := fun j : Fin 4 ↦ TopCat.toSSet.obj (TopCat.of (U A j))
  intro x y hxy
  obtain ⟨a, xa, rfl⟩ := sSetCoproduct_app_jointly_surjective X q x
  obtain ⟨b, xb, rfl⟩ := sSetCoproduct_app_jointly_surjective X q y
  have hcoord (i : Fin (n.unop.len + 1)) :
      (Sigma.ι Y (a i)).app q
          ((TopCat.toSSet.map (intersectionToMember A a i)).app q xa) =
        (Sigma.ι Y (b i)).app q
          ((TopCat.toSSet.map (intersectionToMember A b i)).app q xb) := by
    have hproj := congrArg (fun z ↦ (cechProjection A n i).app q z) hxy
    have ha := congrArg (fun k ↦ k.app q xa) (orderedIntersectionsToCech_π A a i)
    have hb := congrArg (fun k ↦ k.app q xb) (orderedIntersectionsToCech_π A b i)
    exact ha.symm.trans (hproj.trans hb)
  have hab : a = b := by
    funext i
    exact sSetCoproduct_app_index_eq Y q _ _ (hcoord i)
  subst b
  have hmember :
      (TopCat.toSSet.map (intersectionToMember A a 0)).app q xa =
        (TopCat.toSSet.map (intersectionToMember A a 0)).app q xb :=
    sSetCoproduct_app_injective Y q (a 0) (hcoord 0)
  have habSimplex : xa = xb := intersectionToMember_app_injective A a 0 hmember
  exact congrArg ((Sigma.ι X a).app q) habSimplex

private theorem presentation_ι (j : Fin 4) :
    Sigma.ι (fun k ↦ TopCat.toSSet.obj (TopCat.of (U A k))) j ≫
        finiteCoverPresentation (U A) =
      coverMemberToSmallSingularSet (TopCat.of (GluedSpace A.glueData)) (U A) j := by
  rw [finiteCoverPresentation, Sigma.ι_desc]

private theorem toSSetObjEquiv_map_apply {X Y : TopCat} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj X).obj q)
    (z : stdSimplex ℝ (Fin (q.unop.len + 1))) :
    (TopCat.toSSetObjEquiv Y q) ((TopCat.toSSet.map f).app q x) z =
      f ((TopCat.toSSetObjEquiv X q x) z) := by
  rfl

private theorem orderedIntersectionsToCech_app_surjective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((orderedIntersectionsToCech A n).app q) := by
  let X := fun a : CechTuple n ↦
    TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection (U A) a.support))
  let Y := fun j : Fin 4 ↦ TopCat.toSSet.obj (TopCat.of (U A j))
  intro x
  have hex (i : Fin (n.unop.len + 1)) :
      ∃ j y, (Sigma.ι Y j).app q y = (cechProjection A n i).app q x :=
    sSetCoproduct_app_jointly_surjective Y q _
  choose a y hy using hex
  let arrows := fun _ : Fin (n.unop.len + 1) ↦ finiteCoverPresentation (U A)
  have hsmall (i : Fin (n.unop.len + 1)) :
      (coverMemberToSmallSingularSet (TopCat.of (GluedSpace A.glueData))
          (U A) (a i)).app q (y i) =
        (coverMemberToSmallSingularSet (TopCat.of (GluedSpace A.glueData))
          (U A) (a 0)).app q (y 0) := by
    have hpresi := congrArg (fun k ↦ k.app q (y i)) (presentation_ι A (a i))
    have hpres0 := congrArg (fun k ↦ k.app q (y 0)) (presentation_ι A (a 0))
    have hyi := congrArg (fun z ↦ (finiteCoverPresentation (U A)).app q z) (hy i)
    have hy0 := congrArg (fun z ↦ (finiteCoverPresentation (U A)).app q z) (hy 0)
    have hpi := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows i)
    have hp0 := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows 0)
    exact hpresi.symm.trans
      (hyi.trans (hpi.trans (hp0.symm.trans (hy0.symm.trans hpres0))))
  have hfull (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map
          (topologicalSubsetInclusion (TopCat.of (GluedSpace A.glueData)) (U A (a i)))).app q
          (y i) =
        (TopCat.toSSet.map
          (topologicalSubsetInclusion (TopCat.of (GluedSpace A.glueData)) (U A (a 0)))).app q
          (y 0) := by
    have hi := congrArg (fun k ↦ k.app q (y i))
      (coverMemberToSmallSingularSet_comp_inclusion
        (TopCat.of (GluedSpace A.glueData)) (U A) (a i))
    have h0 := congrArg (fun k ↦ k.app q (y 0))
      (coverMemberToSmallSingularSet_comp_inclusion
        (TopCat.of (GluedSpace A.glueData)) (U A) (a 0))
    exact hi.symm.trans
      ((congrArg (fun z ↦
        (coverSmallSingularSubcomplex
          (TopCat.of (GluedSpace A.glueData)) (U A)).ι.app q z) (hsmall i)).trans h0)
  let y0Map := TopCat.toSSetObjEquiv (TopCat.of (U A (a 0))) q (y 0)
  let zMap : C(stdSimplex ℝ (Fin (q.unop.len + 1)),
      finiteCoverIntersection (U A) (CechTuple.support a)) :=
    { toFun := fun p ↦ ⟨(y0Map p).1, by
        rw [mem_finiteCoverIntersection_iff]
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        have heq := congrArg (fun s ↦
          (TopCat.toSSetObjEquiv (TopCat.of (GluedSpace A.glueData)) q s) p) (hfull i)
        rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at heq
        change ((TopCat.toSSetObjEquiv (TopCat.of (U A (a i))) q (y i)) p).1 =
          (y0Map p).1 at heq
        rw [← heq]
        exact ((TopCat.toSSetObjEquiv (TopCat.of (U A (a i))) q (y i)) p).2⟩
      continuous_toFun := by fun_prop }
  let z := (TopCat.toSSetObjEquiv
    (TopCat.of (finiteCoverIntersection (U A) (CechTuple.support a))) q).symm zMap
  have hz (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map (intersectionToMember A a i)).app q z = y i := by
    apply (TopCat.toSSetObjEquiv (TopCat.of (U A (a i))) q).injective
    ext p
    have heq := congrArg (fun s ↦
      (TopCat.toSSetObjEquiv (TopCat.of (GluedSpace A.glueData)) q s) p) (hfull i)
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at heq
    rw [toSSetObjEquiv_map_apply]
    simp only [z, Equiv.apply_symm_apply]
    exact heq.symm
  refine ⟨(Sigma.ι X a).app q z, ?_⟩
  apply cech_app_ext A
  intro i
  calc
    (cechProjection A n i).app q
        ((orderedIntersectionsToCech A n).app q ((Sigma.ι X a).app q z)) =
      (Sigma.ι Y (a i)).app q
        ((TopCat.toSSet.map (intersectionToMember A a i)).app q z) := by
          simpa using congrArg (fun k ↦ k.app q z)
            (orderedIntersectionsToCech_π A a i)
    _ = (Sigma.ι Y (a i)).app q (y i) := congrArg _ (hz i)
    _ = (cechProjection A n i).app q x := hy i

public noncomputable opaque orderedIntersectionsCechIso (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : CechTuple n ↦
      TopCat.toSSet.obj (TopCat.of (finiteCoverIntersection
        (sectionSevenStarOpenCover A).piece a.support))) ≅
      (finiteCoverCechNerve (sectionSevenStarOpenCover A).piece).obj n := by
  let _ : ∀ q, IsIso ((orderedIntersectionsToCech A n).app q) := fun q ↦
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨orderedIntersectionsToCech_app_injective A n q,
        orderedIntersectionsToCech_app_surjective A n q⟩
  let _ : IsIso (orderedIntersectionsToCech A n) :=
    NatIso.isIso_of_isIso_app (orderedIntersectionsToCech A n)
  exact asIso (orderedIntersectionsToCech A n)

end SectionSevenCechNerveChainIdentification

end SphereSixComplex
