module

public import SphereSixComplex.Prerequisites.Geometry.Gluing.FourPieceStar
public import SphereSixComplex.Prerequisites.Topology.Gluing.FiniteIntersections
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.OpenCover
public import SphereSixComplex.Prerequisites.Topology.Sphere.Homology

/-! # The four-piece open cover induced by a star gluing -/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

/-- Index the central star piece by zero and its three fillings by one through three. -/
public def fourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The actual four-piece open cover of a star gluing by the open images of its pieces. -/
public noncomputable def starOpenCover (A : FourPieceStarGluingData) :
    FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (fourPieceStarIndex i))
  isOpen_piece i :=
    (A.glueData.ι_isOpenEmbedding (fourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

end SphereSixComplex
