module

public import SphereSixComplex.Homology.MayerVietoris


/-! # The final cusp attachment cover -/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set

namespace SphereSixComplex

/-- Reorder the star as central, order three, order four, cusp. -/
public def mayerVietorisOrder : Fin 4 → Fin 4 :=
  ![0, 2, 3, 1]

public theorem mayerVietorisOrder_surjective :
    Function.Surjective mayerVietorisOrder := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The actual four-piece star cover in the order used by the Mayer--Vietoris calculation. -/
public noncomputable def mayerVietorisOpenCover (A : OpenEmbeddingStarData) :
    FourPieceOpenCover (GluedSpace A.toFourPieceStarGluingData.glueData) where
  piece i := (starOpenCover A.toFourPieceStarGluingData).piece
    (mayerVietorisOrder i)
  isOpen_piece i := (starOpenCover
    A.toFourPieceStarGluingData).isOpen_piece (mayerVietorisOrder i)
  covers := by
    rw [← (starOpenCover A.toFourPieceStarGluingData).covers]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨mayerVietorisOrder i, hi⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, rfl⟩ := mayerVietorisOrder_surjective j
      exact ⟨i, hj⟩


namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

public abbrev MayerVietorisSpace :=
  GluedSpace A.toFourPieceStarGluingData.glueData

public abbrev mayerVietorisCover :=
  mayerVietorisOpenCover A


variable {A : OpenEmbeddingStarData}


public theorem cuspAttachment_union_eq_univ :
    (mayerVietorisCover A).stage (2 : Fin 4) ∪
      (mayerVietorisCover A).piece 3 = Set.univ := by
  calc
    _ = (mayerVietorisCover A).stage (2 : Fin 3).succ := by
      simpa using
        (mayerVietorisCover A).stage_union_next (2 : Fin 3)
    _ = Set.univ := (mayerVietorisCover A).stage_last

public noncomputable def cuspAttachmentUnionHomeomorph :
    ((mayerVietorisCover A).stage (2 : Fin 4) ∪
      (mayerVietorisCover A).piece 3 :
        Set (MayerVietorisSpace A)) ≃ₜ MayerVietorisSpace A :=
  topologicalSubsetHomeomorphOfEqUniv _ _ cuspAttachment_union_eq_univ



end OpenEmbeddingStarData

end SphereSixComplex
