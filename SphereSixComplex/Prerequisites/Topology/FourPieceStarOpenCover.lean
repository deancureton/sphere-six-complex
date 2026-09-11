module

public import SphereSixComplex.Prerequisites.Geometry.FourPieceStarGluing
public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem

namespace SphereSixComplex

/-- Identify the central piece and three fillings with the four indices of the canonical cover. -/
@[expose] public def fourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The canonical cover of a star gluing by the open images of its four pieces. -/
@[expose] public noncomputable def FourPieceStarGluingData.openCover
    (A : FourPieceStarGluingData) : FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (fourPieceStarIndex i))
  isOpen_piece i := (A.glueData.ι_isOpenEmbedding (fourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

/-- Mayer--Vietoris is exact at each stage of the canonical star cover. -/
public theorem FourPieceStarGluingData.mayerVietorisExactness (A : FourPieceStarGluingData) :
    FourPieceMayerVietorisExactness A.openCover := by
  intro r
  exact IntegralMayerVietoris.exact_sequence_of_isOpen _ _
    (A.openCover.isOpen_stage r.castSucc) (A.openCover.isOpen_piece r.succ)

end SphereSixComplex
