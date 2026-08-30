module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly

/-!
# Naturality through an oriented refinement of a binary open cover

An oriented refinement preserves the order of the two members of a binary cover.  This file
packages the two comparison squares needed to transport the canonical generated-chain
Mayer--Vietoris naturality theorem to ordinary singular homology.  It also composes refinement
naturality with pullback naturality along a continuous map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- The map between the intersections of two oriented binary covers induced by refinement. -/
public def openIntersectionRefinementMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat X).obj (U' ⊓ V') :=
  (Opens.toTopCat X).map (homOfLE (inf_le_inf hU hV))

/-- The homology map between the intersections of two oriented binary covers induced by
refinement. -/
public noncomputable def openIntersectionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) ⟶
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U' ⊓ V')) :=
  (integralHomologyFunctor n).map (openIntersectionRefinementMap hU hV)

/-- The induced map between the generated intersection homology groups. -/
public noncomputable def generatedIntersectionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedIntersectionHomology U V n ⟶ generatedIntersectionHomology U' V' n :=
  HomologicalComplex.homologyMap (coverIntersectionRefinementMap hU hV) n

/-- The induced map between the generated union homology groups. -/
public noncomputable def generatedUnionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedUnionHomology U V n ⟶ generatedUnionHomology U' V' n :=
  HomologicalComplex.homologyMap (coverUnionRefinementMap hU hV) n

/-- The generated boundary naturality square, expressed through the typed refinement maps. -/
@[reassoc]
public theorem generatedBoundary_refinement_naturality' {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedBoundary U V n ≫ generatedIntersectionRefinementHomologyMap hU hV n =
      generatedUnionRefinementHomologyMap hU hV (n + 1) ≫
        generatedBoundary U' V' n := by
  exact generatedBoundary_refinement_naturality hU hV n

/-- Compatibility of ordinary-homology comparison isomorphisms with an oriented refinement.

The `intersection` and `union` fields are exactly the two outer squares of the morphism between
the generated-chain Mayer--Vietoris sequences.  No compatibility at the middle biproduct is
needed to transport the connecting morphism. -/
public structure OpenCoverHomologyComparison.RefinementNaturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V')
    (source : OpenCoverHomologyComparison U V)
    (target : OpenCoverHomologyComparison U' V') : Prop where
  intersection (n : ℕ) :
    generatedIntersectionRefinementHomologyMap hU hV n ≫
        (target.intersectionIso n).hom =
      (source.intersectionIso n).hom ≫
        openIntersectionRefinementHomologyMap hU hV n
  union (n : ℕ) :
    generatedUnionRefinementHomologyMap hU hV n ≫
        (target.unionIso n).hom =
      (source.unionIso n).hom

/-- The ordinary singular Mayer--Vietoris boundary is natural under an oriented refinement of
the two members of a binary cover. -/
public theorem OpenCoverHomologyComparison.boundary_refinement_naturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V')
    (source : OpenCoverHomologyComparison U V)
    (target : OpenCoverHomologyComparison U' V')
    (h : source.RefinementNaturality hU hV target) (n : ℕ) :
    source.boundary n ≫ openIntersectionRefinementHomologyMap hU hV n =
      target.boundary n := by
  rw [← cancel_epi (source.unionIso (n + 1)).hom]
  conv_lhs => rw [← Category.assoc]
  rw [source.unionIso_hom_comp_boundary, Category.assoc, ← h.intersection]
  rw [← Category.assoc, generatedBoundary_refinement_naturality' hU hV n,
    Category.assoc, ← target.unionIso_hom_comp_boundary, ← Category.assoc,
    h.union]

/-- Refining a source cover into the pullback of a target cover and then applying the ambient
map gives the expected naturality square for the connecting morphisms. -/
public theorem OpenCoverHomologyComparison.boundary_refinement_pullback_naturality
    {X Y : TopCat} (f : X ⟶ Y) {U₀ V₀ : Opens X} (U V : Opens Y)
    (hU : U₀ ≤ (Opens.map f).obj U) (hV : V₀ ≤ (Opens.map f).obj V)
    (source : OpenCoverHomologyComparison U₀ V₀)
    (pullback : OpenCoverHomologyComparison ((Opens.map f).obj U) ((Opens.map f).obj V))
    (target : OpenCoverHomologyComparison U V)
    (hRefine : source.RefinementNaturality hU hV pullback)
    (hPullback : pullback.PullbackNaturality f U V target) (n : ℕ) :
    source.boundary n ≫ openIntersectionRefinementHomologyMap hU hV n ≫
        openIntersectionPullbackHomologyMap f U V n =
      (integralHomologyFunctor (n + 1)).map f ≫ target.boundary n := by
  rw [← Category.assoc,
    source.boundary_refinement_naturality hU hV pullback hRefine n,
    pullback.boundary_pullback_naturality f U V target hPullback n]

end SphereSixComplex.BinaryOpenCover

end

end
