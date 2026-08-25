module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Compactness of finite nonsingular simplicial realizations

A finite nonsingular simplicial set is a finite colimit of its nondegenerate standard
simplices.  Geometric realization preserves that colimit, so its underlying space is a finite
union of continuous images of compact topological simplices.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

/-- The nerve of a finite partially ordered type has dimension strictly less than the
cardinality of that type. -/
public theorem finitePartialOrderNerve_hasDimensionLT
    (T : Type) [PartialOrder T] [Fintype T] :
    (CategoryTheory.nerve T).HasDimensionLT (Fintype.card T) := by
  constructor
  intro n hn
  ext s
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  by_contra hs
  have hs' : s ∈ (CategoryTheory.nerve T).nonDegenerate n := by
    simpa [SSet.mem_degenerate_iff_notMem_nonDegenerate] using hs
  have hinj : Function.Injective s.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_injective s).mp hs'
  have hcard : n + 1 ≤ Fintype.card T := by
    simpa using Fintype.card_le_of_injective _ hinj
  omega

set_option linter.style.haveILetI false in
/-- The nerve of a finite partially ordered type is a finite simplicial set. -/
public theorem finitePartialOrderNerve_finite
    (T : Type) [PartialOrder T] [Finite T] :
    (CategoryTheory.nerve T).Finite := by
  letI : Fintype T := Fintype.ofFinite T
  letI : (CategoryTheory.nerve T).HasDimensionLT (Fintype.card T) :=
    finitePartialOrderNerve_hasDimensionLT T
  exact SSet.finite_of_hasDimensionLT (CategoryTheory.nerve T)
    (Fintype.card T) (fun i _ ↦ by
      letI : Finite (ComposableArrows T i) := by
        apply Finite.of_injective
          (fun F : ComposableArrows T i ↦ fun j ↦ F.obj j)
        intro F G h
        apply ComposableArrows.ext (fun j ↦ congrFun h j)
        intro j hj
        subsingleton
      letI : Finite ((CategoryTheory.nerve T).obj
          (Opposite.op (SimplexCategory.mk i))) := by
        change Finite (ComposableArrows T i)
        infer_instance
      exact Finite.of_injective Subtype.val Subtype.val_injective)

/-- The geometric realization of a finite nonsingular simplicial set is compact. -/
public theorem finiteNonsingularSSet_realization_isCompact
    (X : SSet.{0}) [X.Finite] [X.Nonsingular] :
    IsCompact (Set.univ : Set (SSet.toTop.obj X : Type)) := by
  let cTop := SSet.toTop.mapCocone X.coconeN'
  have hcTop : IsColimit cTop :=
    isColimitOfPreserves SSet.toTop X.isColimitCoconeN'
  have hcType : IsColimit ((forget TopCat).mapCocone cTop) :=
    isColimitOfPreserves (forget TopCat) hcTop
  have hcover :
      (Set.univ : Set (SSet.toTop.obj X : Type)) =
        ⋃ s : X.N, Set.range (cTop.ι.app s) := by
    apply (Set.eq_univ_of_forall _).symm
    intro x
    obtain ⟨s, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType x
    exact Set.mem_iUnion.mpr ⟨s, ⟨y, hy⟩⟩
  rw [hcover]
  apply isCompact_iUnion
  intro s
  have hdomain : IsCompact
      (Set.univ : Set (SSet.toTop.obj (X.functorN'.obj s) : Type)) := by
    change IsCompact (Set.univ : Set (SSet.toTop.obj (SSet.stdSimplex.obj
      (SemiSimplexCategory.toSimplexCategory.obj
        ((SSet.N.toSemiSimplexCategory X).obj s))) : Type))
    let e := SimplexCategory.toTopHomeo
      (SemiSimplexCategory.toSimplexCategory.obj
        ((SSet.N.toSemiSimplexCategory X).obj s))
    exact e.isCompact_preimage.mpr isCompact_univ
  have himage := hdomain.image (cTop.ι.app s).hom.continuous
  change IsCompact (Set.range (cTop.ι.app s))
  simpa only [Set.image_univ] using himage

end SphereSixComplex
