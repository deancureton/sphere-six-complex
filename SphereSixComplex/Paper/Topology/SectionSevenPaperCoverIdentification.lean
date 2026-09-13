module

public import SphereSixComplex.Prerequisites.Geometry.FourPieceStarGluing
public import SphereSixComplex.Prerequisites.Topology.FiniteCoverCechDefs
public import SphereSixComplex.Paper.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Prerequisites.Topology.StandardSphereHomologyZeroCore
public import SphereSixComplex.Paper.Topology.HomologyComputation
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Zero
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import SphereSixComplex.Prerequisites.Topology.SingularExcisionOpenCover

/-! # The four-piece open cover induced by a star gluing -/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

/-- Index the central star piece by zero and its three fillings by one through three. -/
public def sectionSevenFourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The actual four-piece open cover of a star gluing by the open images of its pieces. -/
public noncomputable def sectionSevenStarOpenCover (A : FourPieceStarGluingData) :
    FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (sectionSevenFourPieceStarIndex i))
  isOpen_piece i :=
    (A.glueData.ι_isOpenEmbedding (sectionSevenFourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

end SphereSixComplex
