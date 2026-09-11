module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenFinalDegreeZero

/-!
# Assembling the positive-degree Section 7 calculation

For the analytic star, the final degree-zero Mayer--Vietoris basis and map are canonical.  This
module packages the remaining source-stated positive-degree data and inserts the proved degree-zero
calculation automatically.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The final positive-degree cusp-attachment identifications that remain after the canonical
`H₀` calculation.  No field describes the homology of the completed star.  The paper's earlier
`α₁` and `α₂` calculation uses a separate two-set cover. -/
public structure PositiveDegreeHomologyAssembly where
  finalOneSource :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 3 → ℤ)
  finalOneTarget :
    (IntegralSingularHomology 1
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 1
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 3 → ℤ)
  finalOne_comm : ∀ x,
    finalOneTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3) 1 x) =
      sectionSevenFirstBoundaryHom (finalOneSource x)
  finalTwoSource :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 6 → ℤ)
  finalTwoTarget :
    (IntegralSingularHomology 2
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 2
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 6 → ℤ)
  finalTwo_comm : ∀ x,
    finalTwoTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3) 2 x) =
      sectionSevenMayerVietorisFinalTwoHom (finalTwoSource x)

namespace PositiveDegreeHomologyAssembly

/-- The actual degree-one attachment map in the chosen integral coordinates. -/
public theorem differenceMap_one_coordinates (H : A.PositiveDegreeHomologyAssembly) :
    H.finalOneTarget.toAddMonoidHom.comp
        (IntegralMayerVietoris.differenceMap
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage (2 : Fin 4))
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) 1) =
      sectionSevenFirstBoundaryHom.comp H.finalOneSource.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact H.finalOne_comm x

/-- The actual degree-two attachment map in the chosen integral coordinates. -/
public theorem differenceMap_two_coordinates (H : A.PositiveDegreeHomologyAssembly) :
    H.finalTwoTarget.toAddMonoidHom.comp
        (IntegralMayerVietoris.differenceMap
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage (2 : Fin 4))
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) 2) =
      sectionSevenMayerVietorisFinalTwoHom.comp H.finalTwoSource.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact H.finalTwo_comm x

/-- Insert the proved canonical degree-zero bases and compatibility square. -/
public noncomputable def toSectionSevenMayerVietorisHomologyAssembly
    (H : A.PositiveDegreeHomologyAssembly) :
    A.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly where
  finalZeroSource := A.cuspAttachmentOverlapHomologyZeroEquiv
  finalZeroTarget := A.cuspAttachmentSidesHomologyZeroEquiv
  finalZero_comm := A.cuspAttachment_differenceMap_zero_coordinates
  finalOneSource := H.finalOneSource
  finalOneTarget := H.finalOneTarget
  finalOne_comm := H.finalOne_comm
  finalTwoSource := H.finalTwoSource
  finalTwoTarget := H.finalTwoTarget
  finalTwo_comm := H.finalTwo_comm

end PositiveDegreeHomologyAssembly

end SphereSixComplex.Geometry.PaperAnalyticData
