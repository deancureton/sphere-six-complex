module

public import SphereSixComplex.Prerequisites.Geometry.ComplexThreefoldGluing
public import SphereSixComplex.Paper.Topology.FundamentalGroupComputation
public import SphereSixComplex.Prerequisites.Geometry.FourPieceStarGluing
public import SphereSixComplex.Prerequisites.Geometry.EstablishedBiholomorphicStarGluing
public import SphereSixComplex.Prerequisites.Geometry.EstablishedComplexToRealManifold
public import SphereSixComplex.Paper.Topology.EstablishedMayerVietoris

/-!
# Exact gluing data for the completed paper threefold

The four-piece gluing gives a compact complex threefold. Its van Kampen presentation
proves simple connectedness, and its integral homology is stated degree by degree.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

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

/-- All data required to assemble the paper's four pieces into a compact complex threefold with
the asserted fundamental group and integral homology. -/
public structure PaperGluingData where
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
  /-- The selected filling twists give the required van Kampen presentation. -/
  vanKampen : Topology.HasVanKampenData (GluedSpace star.glueData) 0 1 (-1)
  /-- The integral Mayer--Vietoris calculation for the completed star. -/
  integralHomology : ∀ k : ℕ, Nonempty
    (IntegralSingularHomology k (GluedSpace star.glueData) ≃+ IntegralSingularHomology k SixSphere)

namespace PaperGluingData

variable (A : PaperGluingData)

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

/-- The standard open-cover Mayer--Vietoris theorem applies to all three stages of the paper's
four-piece cover. -/
public theorem mayerVietorisExactness : FourPieceMayerVietorisExactness A.star.openCover :=
  establishedFourPieceMayerVietorisExactness A.star.openCover

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

/-- The chosen twists kill the fundamental group of the glued threefold. -/
public theorem simplyConnectedSpace : SimplyConnectedSpace (GluedSpace A.glueData) := by
  let : ConnectedSpace (GluedSpace A.glueData) := A.toComplexThreefold.connected
  let : ChartedSpace ComplexModel (GluedSpace A.glueData) := A.toComplexThreefold.charts
  let : LocallyPathConnectedSpace (GluedSpace A.glueData) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel (GluedSpace A.glueData)
  let : PathConnectedSpace (GluedSpace A.glueData) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact A.vanKampen.simplyConnectedSpace

end PaperGluingData


end

end SphereSixComplex
