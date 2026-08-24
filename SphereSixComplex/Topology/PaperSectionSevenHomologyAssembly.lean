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

/-- The Section 7 homology identifications that remain after the canonical final `H₀` calculation.
No field describes the homology of the completed star. -/
public structure SectionSevenPositiveDegreeHomologyAssembly where
  pieceModel : Fin 4 → ℕ → AddCommGrpCat
  pieceEquiv : ∀ i k,
    IntegralSingularHomology k
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece i) ≃+
      pieceModel i k
  collarModel : Fin 3 → ℕ → AddCommGrpCat
  collarEquiv : ∀ i k,
    IntegralSingularHomology k (A.openEmbeddingStarData.collarSource i) ≃+
      collarModel i k
  stageModel : Fin 3 → ℕ → AddCommGrpCat
  stageEquiv : ∀ r k,
    IntegralSingularHomology k
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage r.castSucc) ≃+
      stageModel r k
  interiorOneSource :
    IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 4 → ℤ)
  interiorOneTarget :
    (IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4)) ×
        IntegralSingularHomology 1
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2)) ≃+
      (Fin 4 → ℤ)
  interiorOne_comm : ∀ x,
    interiorOneTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2) 1 x) =
      alphaOneMatrix.mulVec (interiorOneSource x)
  interiorTwoSource :
    IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4) ∩
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2 :
            Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+
      (Fin 6 → ℤ)
  interiorTwoTarget :
    (IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4)) ×
        IntegralSingularHomology 2
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2)) ≃+
      (Fin 4 → ℤ)
  interiorTwo_comm : ∀ x,
    interiorTwoTarget (IntegralMayerVietoris.differenceMap
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (1 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2) 2 x) =
      alphaTwoMatrix.mulVec (interiorTwoSource x)
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
  pieceModel := H.pieceModel
  pieceEquiv := H.pieceEquiv
  collarModel := H.collarModel
  collarEquiv := H.collarEquiv
  stageModel := H.stageModel
  stageEquiv := H.stageEquiv
  interiorOneSource := H.interiorOneSource
  interiorOneTarget := H.interiorOneTarget
  interiorOne_comm := H.interiorOne_comm
  interiorTwoSource := H.interiorTwoSource
  interiorTwoTarget := H.interiorTwoTarget
  interiorTwo_comm := H.interiorTwo_comm
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
