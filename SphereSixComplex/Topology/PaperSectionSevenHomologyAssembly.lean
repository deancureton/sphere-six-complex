module

public import SphereSixComplex.Topology.PaperSectionSevenFinalDegreeZero

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
public structure SectionSevenPositiveDegreeHomologyAssembly where
  finalOneSource :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 3 → ℤ)
  finalOneTarget :
    (IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 3 → ℤ)
  finalOne_comm : ∀ x,
    finalOneTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 1 x) =
      sectionSevenFirstBoundaryHom (finalOneSource x)
  finalTwoSource :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 6 → ℤ)
  finalTwoTarget :
    (IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
        IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 6 → ℤ)
  finalTwo_comm : ∀ x,
    finalTwoTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 2 x) =
      sectionSevenMayerVietorisFinalTwoHom (finalTwoSource x)

namespace SectionSevenPositiveDegreeHomologyAssembly

/-- Insert the proved canonical degree-zero bases and compatibility square. -/
public noncomputable def toSectionSevenMayerVietorisHomologyAssembly
    (H : A.SectionSevenPositiveDegreeHomologyAssembly) :
    A.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly where
  pieceModel i k := AddCommGrpCat.of
    (IntegralSingularHomology k
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece i))
  pieceEquiv _ _ := AddEquiv.refl _
  collarModel i k := AddCommGrpCat.of
    (IntegralSingularHomology k (A.openEmbeddingStarData.collarSource i))
  collarEquiv _ _ := AddEquiv.refl _
  stageModel r k := AddCommGrpCat.of
    (IntegralSingularHomology k
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage r.castSucc))
  stageEquiv _ _ := AddEquiv.refl _
  finalZeroSource := A.sectionSevenFinalZeroSource
  finalZeroTarget := A.sectionSevenFinalZeroTarget
  finalZero_comm := A.sectionSevenFinalZero_comm
  finalOneSource := H.finalOneSource
  finalOneTarget := H.finalOneTarget
  finalOne_comm := H.finalOne_comm
  finalTwoSource := H.finalTwoSource
  finalTwoTarget := H.finalTwoTarget
  finalTwo_comm := H.finalTwo_comm

end SectionSevenPositiveDegreeHomologyAssembly

end SphereSixComplex.Geometry.PaperAnalyticData
