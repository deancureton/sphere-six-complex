module

public import SphereSixComplex.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeBases

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

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Pointwise, the final right inclusion is the original cusp collar embedding, transported
through the canonical source and target homeomorphisms. -/
public theorem cuspFinalRightInclusion_comm (x : A.openEmbeddingStarData.collarSource 0) :
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0
        (A.openEmbeddingStarData.toFilling 0 x) =
      IntegralMayerVietoris.interToRight
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)
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
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace)) :
    (integralSingularHomologyEquiv k
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      integralSingularHomologyMap k (A.openEmbeddingStarData.toFilling 0).hom
        ((integralSingularHomologyEquiv k
          A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm x) := by
  apply integralSingularHomologyEquiv_conjugates_commutative_square
  apply ContinuousMap.ext
  intro y
  exact (A.cuspFinalRightInclusion_comm y).symm

/-- The two original cusp collar-to-filling coordinate calculations needed by the final
attachment.  The collar bases can, in particular, be supplied by a
`CuspCollarRadialMappingTorusRealization`; no dimensionally incorrect bare mapping-torus model is
used. -/
public structure ActualCuspFillingInclusionCoordinates
    (B : A.SectionSevenCollarInteriorHomologyBases) where
  degreeOne : ∀ x,
    (A.cuspFillingHomologyOneEquiv A.cuspCentralFiberRetractionData)
        (integralSingularHomologyMap 1 (A.openEmbeddingStarData.toFilling 0).hom x) =
      fun i ↦ -sectionSevenFirstBoundaryHom (B.cuspCollarOne x) (Fin.natAdd 1 i)
  degreeTwo : ∀ x,
    (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData)
        (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
      fun i ↦
        -sectionSevenMayerVietorisFinalTwoHom (B.cuspCollarTwo x) (Fin.natAdd 2 i)

namespace ActualCuspFillingInclusionCoordinates

variable {A : PaperAnalyticData} {B : A.SectionSevenCollarInteriorHomologyBases}

/-- Transport the actual degree-one cusp calculation to the final Mayer--Vietoris overlap. -/
public theorem finalCuspOne (C : A.ActualCuspFillingInclusionCoordinates B) (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).cuspPieceOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ -sectionSevenFirstBoundaryHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases B).overlapOne x)
          (Fin.natAdd 1 i) := by
  rw [show (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).cuspPieceOne =
      (integralSingularHomologyEquiv 1
        (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
          (A.cuspFillingHomologyOneEquiv A.cuspCentralFiberRetractionData) from rfl]
  change (A.cuspFillingHomologyOneEquiv A.cuspCentralFiberRetractionData)
      ((integralSingularHomologyEquiv 1
        (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm
          (integralSingularHomologyMap 1 _ x)) = _
  have hconj := A.cuspFinalRightHomologyMap_conjugacy 1 x
  calc
    _ = (A.cuspFillingHomologyOneEquiv A.cuspCentralFiberRetractionData)
        (integralSingularHomologyMap 1 (A.openEmbeddingStarData.toFilling 0).hom
          ((integralSingularHomologyEquiv 1
            A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm x)) :=
      congrArg (A.cuspFillingHomologyOneEquiv A.cuspCentralFiberRetractionData) hconj
    _ = _ := by rw [C.degreeOne]; rfl

/-- Transport the actual degree-two cusp calculation to the final Mayer--Vietoris overlap. -/
public theorem finalCuspTwo (C : A.ActualCuspFillingInclusionCoordinates B) (x) :
    (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).cuspPieceTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToRight
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
            ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
      fun i ↦ -sectionSevenMayerVietorisFinalTwoHom
        ((A.sectionSevenFinalSixHomologyBasesOfLocalBases B).overlapTwo x)
          (Fin.natAdd 2 i) := by
  rw [show (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).cuspPieceTwo =
      (integralSingularHomologyEquiv 2
        (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
          (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData) from rfl]
  change (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData)
      ((integralSingularHomologyEquiv 2
        (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm
          (integralSingularHomologyMap 2 _ x)) = _
  have hconj := A.cuspFinalRightHomologyMap_conjugacy 2 x
  calc
    _ = (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData)
        (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom
          ((integralSingularHomologyEquiv 2
            A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm x)) :=
      congrArg (A.cuspFillingHomologyTwoEquiv A.cuspCentralFiberRetractionData) hconj
    _ = _ := by rw [C.degreeTwo]; rfl

/-- Combine the two proved cusp transports with the independently computed elliptic-interior
maps. -/
public theorem toFinalInclusionCoordinates
    (C : A.ActualCuspFillingInclusionCoordinates B)
    (interiorOne : ∀ x,
      (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).interiorOne
          (integralSingularHomologyMap 1
            (IntegralMayerVietoris.interToLeft
              ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
              ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
        fun i ↦ sectionSevenFirstBoundaryHom
          ((A.sectionSevenFinalSixHomologyBasesOfLocalBases B).overlapOne x)
            (Fin.castAdd 2 i))
    (interiorTwo : ∀ x,
      (A.sectionSevenFinalSixHomologyBasesOfLocalBases B).interiorTwo
          (integralSingularHomologyMap 2
            (IntegralMayerVietoris.interToLeft
              ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
              ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) x) =
        fun i ↦ sectionSevenMayerVietorisFinalTwoHom
          ((A.sectionSevenFinalSixHomologyBasesOfLocalBases B).overlapTwo x)
            (Fin.castAdd 4 i)) :
    A.SectionSevenFinalInclusionCoordinates
      (A.sectionSevenFinalSixHomologyBasesOfLocalBases B) where
  interiorOne := interiorOne
  cuspOne := C.finalCuspOne
  interiorTwo := interiorTwo
  cuspTwo := C.finalCuspTwo

end ActualCuspFillingInclusionCoordinates

end Geometry.PaperAnalyticData

end SphereSixComplex
