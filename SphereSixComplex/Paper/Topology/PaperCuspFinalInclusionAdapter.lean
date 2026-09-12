module

public import SphereSixComplex.Paper.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberHomology
public import SphereSixComplex.Paper.Topology.PaperCuspPhaseSpreading
public import SphereSixComplex.Paper.Topology.PaperSectionSevenFinalDegreeZero

/-!
# The cusp map in the final Mayer--Vietoris attachment

This file removes the gluing-space coordinates from the cusp-side map.  Under the canonical
homeomorphisms from the common collar and the cusp filling to the final overlap and final piece,
the Mayer--Vietoris right inclusion is exactly the original collar-to-filling embedding.

The remaining coordinate datum is stated on that original embedding.  In particular, no map on
the completed four-piece star is an input here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

/-- Integral singular homology respects composition of continuous maps. -/
public theorem integralSingularHomologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap k (g.comp f) =
      (integralSingularHomologyMap k g).comp (integralSingularHomologyMap k f) := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl,
    Functor.map_comp]
  rfl

/-- A commutative square with horizontal homeomorphisms conjugates the two induced homology
maps. -/
public theorem integralSingularHomologyEquiv_conjugates_commutative_square
    {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (k : ℕ) (e : X ≃ₜ X') (h : Y ≃ₜ Y') (f : C(X, Y)) (g : C(X', Y'))
    (hcomm : g.comp ⟨e, e.continuous⟩ = (⟨h, h.continuous⟩ : C(Y, Y')).comp f)
    (x : IntegralSingularHomology k X') :
    (integralSingularHomologyEquiv k h).symm
        (integralSingularHomologyMap k g x) =
      integralSingularHomologyMap k f
        ((integralSingularHomologyEquiv k e).symm x) := by
  obtain ⟨y, rfl⟩ := (integralSingularHomologyEquiv k e).surjective x
  rw [AddEquiv.symm_apply_apply]
  apply (integralSingularHomologyEquiv k h).injective
  rw [AddEquiv.apply_symm_apply]
  change ((integralSingularHomologyMap k g).comp
      (integralSingularHomologyMap k (⟨e, e.continuous⟩ : C(X, X')))) y =
    ((integralSingularHomologyMap k (⟨h, h.continuous⟩ : C(Y, Y'))).comp
      (integralSingularHomologyMap k f)) y
  rw [← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp, hcomm]

namespace Geometry.AnalyticData

variable (A : AnalyticData)

/-- Pointwise, the final right inclusion is the original cusp collar embedding, transported
through the canonical source and target homeomorphisms. -/
public theorem cuspFinalRightInclusion_comm (x : A.openEmbeddingStarData.collarSource 0) :
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0
        (A.openEmbeddingStarData.toFilling 0 x) =
      IntegralMayerVietoris.interToRight
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)
        (A.cuspCollarToSectionSevenFinalOverlapHomeomorph x) := by
  apply Subtype.ext
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some 0) (A.openEmbeddingStarData.toFilling 0 x) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        none (A.openEmbeddingStarData.toCentral 0 x)
  apply (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 0) none (A.openEmbeddingStarData.toFilling 0 x)
      (A.openEmbeddingStarData.toCentral 0 x)).mpr
  exact ⟨A.openEmbeddingStarData.fillingCollarPoint 0 x, rfl, by
    change ((A.openEmbeddingStarData.collarEquiv 0).symm
      (A.openEmbeddingStarData.fillingCollarPoint 0 x)).1 =
        A.openEmbeddingStarData.toCentral 0 x
    rw [A.openEmbeddingStarData.collarEquiv_symm_toFilling]
    rfl⟩

/-- On homology, the final right inclusion is conjugate to the original cusp
collar-to-filling embedding. -/
public theorem cuspFinalRightHomologyMap_conjugacy (k : ℕ)
    (x : IntegralSingularHomology k
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace)) :
    (integralSingularHomologyEquiv k
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) x) =
      integralSingularHomologyMap k (A.openEmbeddingStarData.toFilling 0).hom
        ((integralSingularHomologyEquiv k
          A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm x) := by
  apply integralSingularHomologyEquiv_conjugates_commutative_square
  apply ContinuousMap.ext
  intro y
  exact (A.cuspFinalRightInclusion_comm y).symm


end Geometry.AnalyticData

end SphereSixComplex
