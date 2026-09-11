module

public import SphereSixComplex.Prerequisites.Geometry.ComplexThreefoldGluing
public import SphereSixComplex.Prerequisites.Geometry.FourPieceStarGluing
public import SphereSixComplex.Prerequisites.Geometry.EstablishedBiholomorphicStarGluing

/-!
# Compact complex threefolds from a four-piece star

Only geometry and point-set topology enter this gluing datum. Fundamental-group and homology
calculations can be stated independently on its glued carrier.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A compact Hausdorff complex threefold obtained by gluing a connected four-piece star. -/
public structure CompactComplexStar where
  /-- The central family and three filling pieces, with their pairwise disjoint collar maps. -/
  star : FourPieceStarGluingData
  /-- Every piece is connected. -/
  connectedPiece : ∀ i, ConnectedSpace (star.glueData.U i)
  /-- Each of the three attaching collars is nonempty. -/
  nonemptyCentralCollar : ∀ i, Nonempty (star.centralCollar i)
  /-- The four pieces are complex manifolds and the collar maps are biholomorphic. -/
  biholomorphicStar :
    BiholomorphicStarGluing.BiholomorphicFourPieceStarData star
  /-- Every piece is second countable. -/
  pieceSecondCountable : ∀ i, SecondCountableTopology (star.glueData.U i)
  /-- The glued topology is Hausdorff. -/
  gluedT2 : T2Space (GluedSpace star.glueData)
  /-- The completed glued space is compact. -/
  gluedCompact : CompactSpace (GluedSpace star.glueData)

namespace CompactComplexStar

variable (A : CompactComplexStar)

/-- The canonical gluing diagram built from the central piece and three collars. -/
public abbrev glueData : TopCat.GlueData := A.star.glueData

/-- The complex atlases on the central piece and three filling pieces. -/
@[instance_reducible] public def complexCharts :
    ∀ i, ChartedSpace ComplexModel (A.glueData.U i) :=
  A.biholomorphicStar.complexCharts

/-- Biholomorphic collar gluing makes the transported piece atlases compatible. -/
public theorem complexCompatible :
    letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
    letI := A.complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) A.glueData :=
  BiholomorphicStarGluing.BiholomorphicFourPieceStarData.gluing_atlas_compatible
    A.star A.nonemptyCentralCollar A.biholomorphicStar

/-- Countability of the four-piece gluing follows from countability of its pieces. -/
public theorem gluedSecondCountable : SecondCountableTopology (GluedSpace A.glueData) := by
  let _ : Countable A.glueData.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : A.glueData.J) := A.pieceSecondCountable i
  exact secondCountableTopology_gluedSpace A.glueData

/-- The compatible piece atlases define a compact complex threefold. -/
@[expose] public noncomputable def toComplexThreefold : ComplexThreefold := by
  letI : Finite A.glueData.J := by
    change Finite (Option (Fin 3))
    infer_instance
  letI : Nonempty A.glueData.J := by
    change Nonempty (Option (Fin 3))
    infer_instance
  letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
  letI := A.connectedPiece
  letI := A.complexCharts
  letI := A.gluedT2
  letI := A.gluedSecondCountable
  exact complexThreefoldOfGluing A.glueData A.complexCompatible A.gluedCompact
    (A.star.intersectionGraphConnected A.nonemptyCentralCollar)

end CompactComplexStar

end

end SphereSixComplex
