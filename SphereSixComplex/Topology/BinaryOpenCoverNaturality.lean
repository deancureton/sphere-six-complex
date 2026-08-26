module

public import SphereSixComplex.Topology.BinaryOpenCoverMayerVietoris
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the binary open-cover boundary

Refining both members of a binary cover induces a morphism of the canonical generated-chain
short exact sequences.  Naturality of Mathlib's connecting morphism then gives the corresponding
commuting square on homology.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- The chain map induced by refining both members of a binary-cover intersection. -/
public noncomputable def coverIntersectionRefinementMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    integralSimplicialChains.obj (coverIntersection U V) ⟶
      integralSimplicialChains.obj (coverIntersection U' V') :=
  integralSimplicialChains.map
    (SSet.Subcomplex.homOfLE (inf_le_inf
      (singularOpenSubcomplex_mono hU) (singularOpenSubcomplex_mono hV)))

/-- The chain map induced by refining one open-image subcomplex. -/
public noncomputable def openRefinementMap {X : TopCat} {U U' : Opens X} (hU : U ≤ U') :
    integralSimplicialChains.obj (singularOpenSubcomplex U) ⟶
      integralSimplicialChains.obj (singularOpenSubcomplex U') :=
  integralSimplicialChains.map (SSet.Subcomplex.homOfLE (singularOpenSubcomplex_mono hU))

/-- The biproduct chain map induced by refining both members of a binary cover. -/
public noncomputable def coverBiprodRefinementMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    (integralSimplicialChains.obj (singularOpenSubcomplex U) ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex V)) ⟶
      (integralSimplicialChains.obj (singularOpenSubcomplex U') ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex V')) :=
  biprod.map (openRefinementMap hU) (openRefinementMap hV)

/-- The chain map induced by refining both members of a binary-cover union. -/
public noncomputable def coverUnionRefinementMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    integralSimplicialChains.obj (coverUnion U V) ⟶
      integralSimplicialChains.obj (coverUnion U' V') :=
  integralSimplicialChains.map
    (SSet.Subcomplex.homOfLE (sup_le_sup
      (singularOpenSubcomplex_mono hU) (singularOpenSubcomplex_mono hV)))

/-- Refining a binary cover gives a morphism of its generated-chain short exact sequence. -/
public noncomputable def coverChainShortComplexRefinement {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    coverChainShortComplex U V ⟶ coverChainShortComplex U' V' where
  τ₁ := coverIntersectionRefinementMap hU hV
  τ₂ := coverBiprodRefinementMap hU hV
  τ₃ := coverUnionRefinementMap hU hV
  comm₁₂ := by
    dsimp [coverIntersectionRefinementMap, coverBiprodRefinementMap, openRefinementMap,
      coverChainShortComplex]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst]
      rw [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [Category.assoc, biprod.lift_snd]
      rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      rw [Preadditive.comp_neg, Preadditive.neg_comp,
        ← Functor.map_comp, ← Functor.map_comp]
      rfl
  comm₂₃ := by
    dsimp [coverUnionRefinementMap, coverBiprodRefinementMap, openRefinementMap,
      coverChainShortComplex]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl

/-- The canonical generated Mayer--Vietoris boundary is natural under simultaneous refinement
of both members of the cover. -/
public theorem generatedBoundary_refinement_naturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedBoundary U V n ≫
        HomologicalComplex.homologyMap (coverIntersectionRefinementMap hU hV) n =
      HomologicalComplex.homologyMap (coverUnionRefinementMap hU hV) (n + 1) ≫
        generatedBoundary U' V' n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (coverChainShortComplexRefinement hU hV)
    (coverChainShortComplex_shortExact U V)
    (coverChainShortComplex_shortExact U' V') (n + 1) n rfl

end SphereSixComplex.BinaryOpenCover
