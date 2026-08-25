module

public import SphereSixComplex.Topology.BoundarySevenCechOrderedTuples
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Ordered-tuple decomposition of the boundary-seven target Cech nerve

The iterated pullback in each outer Cech degree is the coproduct of the singular simplicial
sets of the corresponding ordered intersections.  Since the intersection of all eight face
neighbourhoods is empty, only tuples with proper support occur.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

public abbrev boundarySevenTargetAmbient : TopCat :=
  SSet.toTop.obj (∂Δ[7] : SSet.{0})

/-- Inclusion of an ordered proper intersection into one of its selected cover members. -/
public def boundarySevenTargetIntersectionToMember
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support) ⟶
      TopCat.of (boundarySevenComparisonFaceNeighborhood (a.1 i)) :=
  TopCat.ofHom
    { toFun := fun x => ⟨x.1, by
        exact (mem_boundarySevenFaceNeighborhoodIntersection_iff a.1.support x).mp x.2
          (a.1 i) (BoundarySevenCechTuple.mem_support a.1 i)⟩
      continuous_toFun := by fun_prop }

@[reassoc]
public theorem boundarySevenTargetIntersectionToMember_comp_inclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenTargetIntersectionToMember a i ≫
        topologicalSubsetInclusion boundarySevenTargetAmbient
          (boundarySevenComparisonFaceNeighborhood (a.1 i)) =
      topologicalSubsetInclusion boundarySevenTargetAmbient
        (boundarySevenFaceNeighborhoodIntersection a.1.support) := by
  ext x
  rfl

/-- The leg from an ordered intersection to the selected summand of the presentation source. -/
public noncomputable def boundarySevenTargetIntersectionToPresentationLeg
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support)) ⟶
      boundarySevenFaceNeighborhoodPresentationSource :=
  TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i) ≫
    Sigma.ι (fun j : Fin 8 => TopCat.toSSet.obj
      (TopCat.of (boundarySevenComparisonFaceNeighborhood j))) (a.1 i)

public noncomputable def boundarySevenTargetIntersectionToSmall
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support)) ⟶
      coverSmallSingularSubcomplex boundarySevenTargetAmbient
        boundarySevenComparisonFaceNeighborhood :=
  TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a 0) ≫
    coverMemberToSmallSingularSet boundarySevenTargetAmbient
      boundarySevenComparisonFaceNeighborhood (a.1 0)

public theorem boundarySevenTargetIntersectionToPresentationLeg_condition
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenTargetIntersectionToPresentationLeg a i ≫
        boundarySevenFaceNeighborhoodPresentation =
      boundarySevenTargetIntersectionToSmall a := by
  rw [← cancel_mono
    (coverSmallSingularSubcomplex boundarySevenTargetAmbient
      boundarySevenComparisonFaceNeighborhood).ι]
  simp only [boundarySevenTargetIntersectionToPresentationLeg,
    boundarySevenFaceNeighborhoodPresentation, Category.assoc, Sigma.ι_desc_assoc,
    coverMemberToSmallSingularSet_comp_inclusion,
    boundarySevenTargetIntersectionToSmall]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The canonical map from one ordered-intersection summand to the corresponding Cech
wide pullback. -/
public noncomputable def boundarySevenTargetIntersectionToCechSummand
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support)) ⟶
      boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj n :=
  WidePullback.lift (boundarySevenTargetIntersectionToSmall a)
    (boundarySevenTargetIntersectionToPresentationLeg a)
    (boundarySevenTargetIntersectionToPresentationLeg_condition a)

/-- The coproduct map from all proper ordered intersections to the target Cech object. -/
public noncomputable def boundarySevenOrderedTargetCechMap
    (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : BoundarySevenProperCechTuple n =>
      TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support))) ⟶
      boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj n :=
  Sigma.desc boundarySevenTargetIntersectionToCechSummand

private noncomputable def boundarySevenSSetCoproductAppIsColimit
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((∐ X).obj q) (fun i => (Sigma.ι X i).app q)) :=
  isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj q) X
    (fun i => Sigma.ι X i) (coproductIsCoproduct X)

private theorem boundarySevenSSetCoproduct_app_jointly_surjective
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ) (x : (∐ X).obj q) :
    ∃ i y, (Sigma.ι X i).app q y = x :=
  Cofan.inj_jointly_surjective_of_isColimit
    (boundarySevenSSetCoproductAppIsColimit X q) x

private theorem boundarySevenSSetCoproduct_app_index_eq
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ)
    {i j : ι} (x : (X i).obj q) (y : (X j).obj q)
    (h : (Sigma.ι X i).app q x = (Sigma.ι X j).app q y) : i = j :=
  Cofan.eq_of_inj_apply_eq_of_isColimit
    (boundarySevenSSetCoproductAppIsColimit X q) x y h

private theorem boundarySevenSSetCoproduct_app_injective
    {ι : Type} (X : ι → SSet) (q : SimplexCategoryᵒᵖ) (i : ι) :
    Function.Injective ((Sigma.ι X i).app q) :=
  Cofan.inj_injective_of_isColimit
    (boundarySevenSSetCoproductAppIsColimit X q) i

/-- Projection from the target Cech wide pullback to a selected presentation leg. -/
public noncomputable def boundarySevenTargetCechProjection
    (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj n ⟶
      boundarySevenFaceNeighborhoodPresentationSource :=
  WidePullback.π (fun _ : Fin (n.unop.len + 1) =>
    boundarySevenFaceNeighborhoodPresentation) i

private theorem boundarySevenTargetCech_app_ext
    {n q : SimplexCategoryᵒᵖ}
    (x y : (boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj n).obj q)
    (h : ∀ i, (boundarySevenTargetCechProjection n i).app q x =
      (boundarySevenTargetCechProjection n i).app q y) : x = y := by
  let arrows := fun _ : Fin (n.unop.len + 1) =>
    boundarySevenFaceNeighborhoodPresentation
  let D := WidePullbackShape.wideCospan
    (coverSmallSingularSubcomplex boundarySevenTargetAmbient
      boundarySevenComparisonFaceNeighborhood : SSet)
    (fun _ : Fin (n.unop.len + 1) =>
      boundarySevenFaceNeighborhoodPresentationSource) arrows
  let ev := (evaluation SimplexCategoryᵒᵖ (Type _)).obj q
  have hlim : IsLimit (Functor.mapCone ev (limit.cone D)) :=
    isLimitOfPreserves ev (limit.isLimit D)
  apply (Types.isLimitEquivSections hlim).injective
  apply Subtype.ext
  funext j
  cases j with
  | none =>
      have hx := congrArg (fun k => k.app q x) (WidePullback.π_arrow arrows 0)
      have hy := congrArg (fun k => k.app q y) (WidePullback.π_arrow arrows 0)
      exact hx.symm.trans ((congrArg
        (fun z => (arrows 0).app q z) (h 0)).trans hy)
  | some i => exact h i

/-- On a summand, the ordered-target map followed by a Cech projection is the selected
intersection inclusion into the corresponding presentation summand. -/
@[reassoc]
public theorem boundarySevenOrderedTargetCechMap_projection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : BoundarySevenProperCechTuple n =>
        TopCat.toSSet.obj
          (TopCat.of (boundarySevenFaceNeighborhoodIntersection b.1.support))) a ≫
        boundarySevenOrderedTargetCechMap n ≫
        boundarySevenTargetCechProjection n i =
      TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i) ≫
        Sigma.ι (fun j : Fin 8 => TopCat.toSSet.obj
          (TopCat.of (boundarySevenComparisonFaceNeighborhood j))) (a.1 i) := by
  rw [← Category.assoc, boundarySevenOrderedTargetCechMap, Sigma.ι_desc]
  change WidePullback.lift (boundarySevenTargetIntersectionToSmall a)
      (boundarySevenTargetIntersectionToPresentationLeg a)
      (boundarySevenTargetIntersectionToPresentationLeg_condition a) ≫
        WidePullback.π (fun _ : Fin (n.unop.len + 1) =>
          boundarySevenFaceNeighborhoodPresentation) i = _
  rw [WidePullback.lift_π]
  rfl

private theorem boundarySevenTargetIntersectionToMember_app_injective
    {n q : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Function.Injective
      ((TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i)).app q) := by
  let _ : Mono (boundarySevenTargetIntersectionToMember a i) :=
    (TopCat.mono_iff_injective _).mpr
      (fun _ _ h => Subtype.ext
        (congrArg (fun z : boundarySevenComparisonFaceNeighborhood (a.1 i) => z.1) h))
  let _ : Mono (TopCat.toSSet.map
      (boundarySevenTargetIntersectionToMember a i)) :=
    Functor.map_mono TopCat.toSSet _
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

public theorem boundarySevenOrderedTargetCechMap_app_injective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Injective ((boundarySevenOrderedTargetCechMap n).app q) := by
  let X := fun a : BoundarySevenProperCechTuple n =>
    TopCat.toSSet.obj
      (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support))
  let Y := fun j : Fin 8 => TopCat.toSSet.obj
    (TopCat.of (boundarySevenComparisonFaceNeighborhood j))
  intro x y hxy
  obtain ⟨a, xa, rfl⟩ :=
    boundarySevenSSetCoproduct_app_jointly_surjective X q x
  obtain ⟨b, xb, rfl⟩ :=
    boundarySevenSSetCoproduct_app_jointly_surjective X q y
  have hcoord (i : Fin (n.unop.len + 1)) :
      (Sigma.ι Y (a.1 i)).app q
          ((TopCat.toSSet.map
            (boundarySevenTargetIntersectionToMember a i)).app q xa) =
        (Sigma.ι Y (b.1 i)).app q
          ((TopCat.toSSet.map
            (boundarySevenTargetIntersectionToMember b i)).app q xb) := by
    have hproj := congrArg
      (fun z => (boundarySevenTargetCechProjection n i).app q z) hxy
    have ha := congrArg (fun k => k.app q xa)
      (boundarySevenOrderedTargetCechMap_projection a i)
    have hb := congrArg (fun k => k.app q xb)
      (boundarySevenOrderedTargetCechMap_projection b i)
    exact ha.symm.trans (hproj.trans hb)
  have hab : a = b := by
    apply Subtype.ext
    funext i
    exact boundarySevenSSetCoproduct_app_index_eq Y q _ _ (hcoord i)
  subst b
  have hmember :
      (TopCat.toSSet.map
        (boundarySevenTargetIntersectionToMember a 0)).app q xa =
      (TopCat.toSSet.map
        (boundarySevenTargetIntersectionToMember a 0)).app q xb :=
    boundarySevenSSetCoproduct_app_injective Y q (a.1 0) (hcoord 0)
  have habSimplex : xa = xb :=
    boundarySevenTargetIntersectionToMember_app_injective a 0 hmember
  exact congrArg ((Sigma.ι X a).app q) habSimplex

private theorem boundarySevenTargetPresentation_ι (j : Fin 8) :
    Sigma.ι (fun k : Fin 8 => TopCat.toSSet.obj
      (TopCat.of (boundarySevenComparisonFaceNeighborhood k))) j ≫
        boundarySevenFaceNeighborhoodPresentation =
      coverMemberToSmallSingularSet boundarySevenTargetAmbient
        boundarySevenComparisonFaceNeighborhood j := by
  rw [boundarySevenFaceNeighborhoodPresentation, Sigma.ι_desc]

private theorem boundarySevenToSSetObjEquiv_map_apply
    {X Y : TopCat} (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj q)
    (z : stdSimplex ℝ (Fin (q.unop.len + 1))) :
    (TopCat.toSSetObjEquiv Y q) ((TopCat.toSSet.map f).app q x) z =
      f ((TopCat.toSSetObjEquiv X q x) z) := by
  rfl

public theorem boundarySevenOrderedTargetCechMap_app_surjective
    (n q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((boundarySevenOrderedTargetCechMap n).app q) := by
  let X := fun a : BoundarySevenProperCechTuple n =>
    TopCat.toSSet.obj
      (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support))
  let Y := fun j : Fin 8 => TopCat.toSSet.obj
    (TopCat.of (boundarySevenComparisonFaceNeighborhood j))
  intro x
  have hex (i : Fin (n.unop.len + 1)) :
      ∃ j y, (Sigma.ι Y j).app q y =
        (boundarySevenTargetCechProjection n i).app q x :=
    boundarySevenSSetCoproduct_app_jointly_surjective Y q _
  choose a y hy using hex
  let arrows := fun _ : Fin (n.unop.len + 1) =>
    boundarySevenFaceNeighborhoodPresentation
  have hsmall (i : Fin (n.unop.len + 1)) :
      (coverMemberToSmallSingularSet boundarySevenTargetAmbient
          boundarySevenComparisonFaceNeighborhood (a i)).app q (y i) =
        (coverMemberToSmallSingularSet boundarySevenTargetAmbient
          boundarySevenComparisonFaceNeighborhood (a 0)).app q (y 0) := by
    have hpresi := congrArg (fun k => k.app q (y i))
      (boundarySevenTargetPresentation_ι (a i))
    have hpres0 := congrArg (fun k => k.app q (y 0))
      (boundarySevenTargetPresentation_ι (a 0))
    have hyi := congrArg
      (fun z => boundarySevenFaceNeighborhoodPresentation.app q z) (hy i)
    have hy0 := congrArg
      (fun z => boundarySevenFaceNeighborhoodPresentation.app q z) (hy 0)
    have hpi := congrArg (fun k => k.app q x) (WidePullback.π_arrow arrows i)
    have hp0 := congrArg (fun k => k.app q x) (WidePullback.π_arrow arrows 0)
    exact hpresi.symm.trans
      (hyi.trans (hpi.trans (hp0.symm.trans (hy0.symm.trans hpres0))))
  have hfull (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map
        (topologicalSubsetInclusion boundarySevenTargetAmbient
          (boundarySevenComparisonFaceNeighborhood (a i)))).app q (y i) =
      (TopCat.toSSet.map
        (topologicalSubsetInclusion boundarySevenTargetAmbient
          (boundarySevenComparisonFaceNeighborhood (a 0)))).app q (y 0) := by
    have hi := congrArg (fun k => k.app q (y i))
      (coverMemberToSmallSingularSet_comp_inclusion boundarySevenTargetAmbient
        boundarySevenComparisonFaceNeighborhood (a i))
    have h0 := congrArg (fun k => k.app q (y 0))
      (coverMemberToSmallSingularSet_comp_inclusion boundarySevenTargetAmbient
        boundarySevenComparisonFaceNeighborhood (a 0))
    exact hi.symm.trans
      ((congrArg (fun z =>
        (coverSmallSingularSubcomplex boundarySevenTargetAmbient
          boundarySevenComparisonFaceNeighborhood).ι.app q z) (hsmall i)).trans h0)
  let y0Map := TopCat.toSSetObjEquiv
    (TopCat.of (boundarySevenComparisonFaceNeighborhood (a 0))) q (y 0)
  have haProper : BoundarySevenCechTuple.support a ≠ Finset.univ := by
    intro ha
    let p : stdSimplex ℝ (Fin (q.unop.len + 1)) := stdSimplex.barycenter
    have hp : (y0Map p).1 ∈
        boundarySevenFaceNeighborhoodIntersection
          (BoundarySevenCechTuple.support a) := by
      rw [mem_boundarySevenFaceNeighborhoodIntersection_iff]
      intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      have heq := congrArg (fun s =>
        (TopCat.toSSetObjEquiv boundarySevenTargetAmbient q s) p) (hfull i)
      rw [boundarySevenToSSetObjEquiv_map_apply,
        boundarySevenToSSetObjEquiv_map_apply] at heq
      change ((TopCat.toSSetObjEquiv
        (TopCat.of (boundarySevenComparisonFaceNeighborhood (a i))) q (y i)) p).1 =
          (y0Map p).1 at heq
      rw [← heq]
      exact ((TopCat.toSSetObjEquiv
        (TopCat.of (boundarySevenComparisonFaceNeighborhood (a i))) q (y i)) p).2
    rw [ha, boundarySevenFaceNeighborhoodIntersection_univ_eq_empty] at hp
    exact hp
  let ap : BoundarySevenProperCechTuple n := ⟨a, haProper⟩
  let zMap : C(stdSimplex ℝ (Fin (q.unop.len + 1)),
      boundarySevenFaceNeighborhoodIntersection
        (BoundarySevenCechTuple.support a)) :=
    { toFun := fun p => ⟨(y0Map p).1, by
        rw [mem_boundarySevenFaceNeighborhoodIntersection_iff]
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        have heq := congrArg (fun s =>
          (TopCat.toSSetObjEquiv boundarySevenTargetAmbient q s) p) (hfull i)
        rw [boundarySevenToSSetObjEquiv_map_apply,
          boundarySevenToSSetObjEquiv_map_apply] at heq
        change ((TopCat.toSSetObjEquiv
          (TopCat.of (boundarySevenComparisonFaceNeighborhood (a i))) q (y i)) p).1 =
            (y0Map p).1 at heq
        rw [← heq]
        exact ((TopCat.toSSetObjEquiv
          (TopCat.of (boundarySevenComparisonFaceNeighborhood (a i))) q (y i)) p).2⟩
      continuous_toFun := by fun_prop }
  let z := (TopCat.toSSetObjEquiv
    (TopCat.of (boundarySevenFaceNeighborhoodIntersection
      (BoundarySevenCechTuple.support a))) q).symm zMap
  have hz (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map
        (boundarySevenTargetIntersectionToMember ap i)).app q z = y i := by
    apply (TopCat.toSSetObjEquiv
      (TopCat.of (boundarySevenComparisonFaceNeighborhood (a i))) q).injective
    ext p
    have heq := congrArg (fun s =>
      (TopCat.toSSetObjEquiv boundarySevenTargetAmbient q s) p) (hfull i)
    rw [boundarySevenToSSetObjEquiv_map_apply,
      boundarySevenToSSetObjEquiv_map_apply] at heq
    rw [boundarySevenToSSetObjEquiv_map_apply]
    simp only [z]
    exact heq.symm
  refine ⟨(Sigma.ι X ap).app q z, ?_⟩
  apply boundarySevenTargetCech_app_ext
  intro i
  calc
    (boundarySevenTargetCechProjection n i).app q
        ((boundarySevenOrderedTargetCechMap n).app q
          ((Sigma.ι X ap).app q z)) =
      (Sigma.ι Y (a i)).app q
        ((TopCat.toSSet.map
          (boundarySevenTargetIntersectionToMember ap i)).app q z) := by
            simpa using congrArg (fun k => k.app q z)
              (boundarySevenOrderedTargetCechMap_projection ap i)
    _ = (Sigma.ι Y (a i)).app q (y i) := congrArg _ (hz i)
    _ = (boundarySevenTargetCechProjection n i).app q x := hy i

/-- Objectwise, the target Cech nerve is the coproduct of the singular simplicial sets of
proper ordered face-neighbourhood intersections. -/
public noncomputable def boundarySevenOrderedTargetCechIso
    (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : BoundarySevenProperCechTuple n =>
      TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support))) ≅
      boundarySevenFaceNeighborhoodAugmentedCechNerve.left.obj n := by
  let _ : ∀ q, IsIso ((boundarySevenOrderedTargetCechMap n).app q) := fun q =>
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨boundarySevenOrderedTargetCechMap_app_injective n q,
        boundarySevenOrderedTargetCechMap_app_surjective n q⟩
  let _ : IsIso (boundarySevenOrderedTargetCechMap n) :=
    NatIso.isIso_of_isIso_app (boundarySevenOrderedTargetCechMap n)
  exact asIso (boundarySevenOrderedTargetCechMap n)

@[simp]
public theorem boundarySevenOrderedTargetCechIso_hom
    (n : SimplexCategoryᵒᵖ) :
    (boundarySevenOrderedTargetCechIso n).hom =
      boundarySevenOrderedTargetCechMap n :=
  rfl

/-- The public isomorphism restricts on each coproduct summand to the canonical wide-pullback
lift from that ordered intersection. -/
@[reassoc]
public theorem boundarySevenOrderedTargetCechIso_hom_summand
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    Sigma.ι (fun b : BoundarySevenProperCechTuple n =>
        TopCat.toSSet.obj
          (TopCat.of (boundarySevenFaceNeighborhoodIntersection b.1.support))) a ≫
        (boundarySevenOrderedTargetCechIso n).hom =
      boundarySevenTargetIntersectionToCechSummand a := by
  rw [boundarySevenOrderedTargetCechIso_hom,
    boundarySevenOrderedTargetCechMap, Sigma.ι_desc]

/-- Projection formula stated directly for the public objectwise isomorphism. -/
@[reassoc]
public theorem boundarySevenOrderedTargetCechIso_hom_projection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : BoundarySevenProperCechTuple n =>
        TopCat.toSSet.obj
          (TopCat.of (boundarySevenFaceNeighborhoodIntersection b.1.support))) a ≫
        (boundarySevenOrderedTargetCechIso n).hom ≫
        boundarySevenTargetCechProjection n i =
      TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i) ≫
        Sigma.ι (fun j : Fin 8 => TopCat.toSSet.obj
          (TopCat.of (boundarySevenComparisonFaceNeighborhood j))) (a.1 i) := by
  rw [boundarySevenOrderedTargetCechIso_hom]
  exact boundarySevenOrderedTargetCechMap_projection a i

end SphereSixComplex
