module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenMayerVietoris
public import SphereSixComplex.Paper.Topology.HomologyComputation
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Zero


/-! # The final cusp attachment cover -/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set

namespace SphereSixComplex

/-- Reorder the star as central, order three, order four, cusp. -/
public def sectionSevenMayerVietorisOrder : Fin 4 → Fin 4 :=
  ![0, 2, 3, 1]

public theorem sectionSevenMayerVietorisOrder_surjective :
    Function.Surjective sectionSevenMayerVietorisOrder := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The actual four-piece star cover in the order used by the Mayer--Vietoris calculation. -/
public noncomputable def sectionSevenMayerVietorisOpenCover (A : OpenEmbeddingStarData) :
    FourPieceOpenCover (GluedSpace A.toFourPieceStarGluingData.glueData) where
  piece i := (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece
    (sectionSevenMayerVietorisOrder i)
  isOpen_piece i := (sectionSevenStarOpenCover
    A.toFourPieceStarGluingData).isOpen_piece (sectionSevenMayerVietorisOrder i)
  covers := by
    rw [← (sectionSevenStarOpenCover A.toFourPieceStarGluingData).covers]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨sectionSevenMayerVietorisOrder i, hi⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, rfl⟩ := sectionSevenMayerVietorisOrder_surjective j
      exact ⟨i, hj⟩


namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

public abbrev SectionSevenMayerVietorisSpace :=
  GluedSpace A.toFourPieceStarGluingData.glueData

public abbrev sectionSevenMayerVietorisCover :=
  sectionSevenMayerVietorisOpenCover A


variable {A : OpenEmbeddingStarData}


public theorem cuspAttachment_union_eq_univ :
    (sectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
      (sectionSevenMayerVietorisCover A).piece 3 = Set.univ := by
  calc
    _ = (sectionSevenMayerVietorisCover A).stage (2 : Fin 3).succ := by
      simpa using
        (sectionSevenMayerVietorisCover A).stage_union_next (2 : Fin 3)
    _ = Set.univ := (sectionSevenMayerVietorisCover A).stage_last

public noncomputable def cuspAttachmentUnionHomeomorph :
    ((sectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
      (sectionSevenMayerVietorisCover A).piece 3 :
        Set (SectionSevenMayerVietorisSpace A)) ≃ₜ SectionSevenMayerVietorisSpace A :=
  topologicalSubsetHomeomorphOfEqUniv _ _ cuspAttachment_union_eq_univ



end OpenEmbeddingStarData

end SphereSixComplex
