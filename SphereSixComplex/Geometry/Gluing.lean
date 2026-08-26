module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Gluing

/-!
# Gluing manifold atlases

This file builds a charted space on the topological space obtained from mathlib's `TopCat.GlueData`.
Each piece maps to the glued space by an open embedding. The remaining geometric obligation is the
pairwise compatibility of the transported piece charts.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set OpenPartialHomeomorph Manifold Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- The underlying type of the topological space obtained from a family of gluing data. -/
public abbrev GluedSpace (D : TopCat.GlueData.{w}) : Type w := D.toGlueData.glued

/-- The canonical open partial homeomorphism from a piece into the glued space. -/
public noncomputable def pieceOpenPartialHomeomorph (D : TopCat.GlueData.{w}) (i : D.J)
    [Nonempty (D.U i)] : OpenPartialHomeomorph (D.U i) (GluedSpace D) :=
  (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)

/-- Each piece is an open subspace of the glued space. -/
public theorem piece_isOpenEmbedding (D : TopCat.GlueData.{w}) (i : D.J) :
    IsOpenEmbedding (D.toGlueData.ι i) :=
  D.ι_isOpenEmbedding i

/-- The canonical map from the disjoint union of all pieces to the glued space. -/
public noncomputable def gluingProjection (D : TopCat.GlueData.{w}) :
    (Σ i, D.U i) → GluedSpace D := fun x ↦ D.toGlueData.ι x.1 x.2

@[simp]
public theorem gluingProjection_mk (D : TopCat.GlueData.{w}) (i : D.J) (x : D.U i) :
    gluingProjection D ⟨i, x⟩ = D.toGlueData.ι i x :=
  rfl

/-- The canonical map from the disjoint union of pieces is an open quotient map. -/
public theorem gluingProjection_isOpenQuotientMap (D : TopCat.GlueData.{w}) :
    IsOpenQuotientMap (gluingProjection D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    exact ⟨⟨i, y⟩, hy⟩
  · exact continuous_sigma fun i ↦ (D.ι_isOpenEmbedding i).continuous
  · rw [isOpenMap_sigma]
    exact fun i ↦ (D.ι_isOpenEmbedding i).isOpenMap

/-- A subset of the square of a topological disjoint union is closed exactly when its restriction
to every pair of components is closed. -/
public theorem isClosed_sigmaSquare_iff
    {J : Type*} {U : J → Type*} [∀ i, TopologicalSpace (U i)]
    {S : Set ((Σ i, U i) × (Σ i, U i))} :
    IsClosed S ↔ ∀ i j, IsClosed
      ((Prod.map (@Sigma.mk J U i) (@Sigma.mk J U j)) ⁻¹' S) := by
  constructor
  · intro h i j
    exact h.preimage (continuous_sigmaMk.prodMap continuous_sigmaMk)
  · intro h
    rw [← isOpen_compl_iff]
    have hopen (i j : J) : IsOpen
        ((Prod.map (@Sigma.mk J U i) (@Sigma.mk J U j)) ⁻¹' Sᶜ) := by
      rw [preimage_compl]
      exact (h i j).isOpen_compl
    have heq : Sᶜ = ⋃ i, ⋃ j,
        Prod.map (@Sigma.mk J U i) (@Sigma.mk J U j) ''
          (Prod.map (@Sigma.mk J U i) (@Sigma.mk J U j) ⁻¹' Sᶜ) := by
      apply Set.Subset.antisymm
      · rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩ hp
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
        exact ⟨(x, y), hp, rfl⟩
      · intro p hp
        obtain ⟨i, j, q, hq, rfl⟩ := Set.mem_iUnion₂.mp hp
        exact hq
    rw [heq]
    exact isOpen_iUnion fun i ↦ isOpen_iUnion fun j ↦
      (isOpenMap_sigmaMk.prodMap isOpenMap_sigmaMk) _ (hopen i j)

/-- Hausdorffness of a glued space is equivalent to closedness of the equality kernel on every
ordered pair of pieces. -/
public theorem t2Space_gluedSpace_iff_pieceKernelsClosed (D : TopCat.GlueData.{w}) :
    T2Space (GluedSpace D) ↔ ∀ i j, IsClosed
      {p : D.U i × D.U j | D.toGlueData.ι i p.1 = D.toGlueData.ι j p.2} := by
  rw [t2Space_iff_of_isOpenQuotientMap (gluingProjection_isOpenQuotientMap D)]
  rw [isClosed_sigmaSquare_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  rw [show Prod.map (@Sigma.mk D.J (fun i ↦ D.U i) i)
      (@Sigma.mk D.J (fun i ↦ D.U i) j) ⁻¹'
        {q | gluingProjection D q.1 = gluingProjection D q.2} =
      {p : D.U i × D.U j |
        D.toGlueData.ι i p.1 = D.toGlueData.ι j p.2} by
    ext p
    rfl]

/-- A gluing over a countable index type is second countable when every piece is second
countable. -/
public theorem secondCountableTopology_gluedSpace (D : TopCat.GlueData.{w}) [Countable D.J]
    [∀ i, SecondCountableTopology (D.U i)] :
    SecondCountableTopology (GluedSpace D) := by
  let _ (i : D.J) : SecondCountableTopology
      (Set.range (D.toGlueData.ι i)) :=
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i ↦ Set.range (D.toGlueData.ι i))
  · intro i
    exact (D.ι_isOpenEmbedding i).isOpen_range
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    exact ⟨i, y, hy⟩

/-- A gluing of finitely many compact pieces is compact. -/
public theorem compactSpace_gluedSpace (D : TopCat.GlueData.{w}) [Finite D.J]
    [∀ i, CompactSpace (D.U i)] : CompactSpace (GluedSpace D) := by
  rw [← isCompact_univ_iff]
  have huniv : (Set.univ : Set (GluedSpace D)) =
      ⋃ i, Set.range (D.toGlueData.ι i) := by
    ext x
    simp only [mem_univ, mem_iUnion, mem_range, true_iff]
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    exact ⟨i, y, hy⟩
  rw [huniv]
  exact isCompact_iUnion fun i ↦ by
    simpa only [image_univ] using
      isCompact_univ.image (D.ι_isOpenEmbedding i).continuous

/-- A finite gluing is compact as soon as each piece contains a compact set and the images of
those compact sets cover the glued space.  Unlike `compactSpace_gluedSpace`, this applies to
compactifications assembled from noncompact open pieces. -/
public theorem compactSpace_gluedSpace_of_compact_piece_cover
    (D : TopCat.GlueData.{w}) [Finite D.J]
    (K : ∀ i, Set (D.U i))
    (hK : ∀ i, IsCompact (K i))
    (hcover : ∀ x : GluedSpace D, ∃ i y, y ∈ K i ∧ D.toGlueData.ι i y = x) :
    CompactSpace (GluedSpace D) := by
  rw [← isCompact_univ_iff]
  have huniv : (Set.univ : Set (GluedSpace D)) =
      ⋃ i, D.toGlueData.ι i '' K i := by
    ext x
    simp only [mem_univ, mem_iUnion, mem_image, true_iff]
    obtain ⟨i, y, hyK, hy⟩ := hcover x
    exact ⟨i, y, hyK, hy⟩
  rw [huniv]
  exact isCompact_iUnion fun i ↦
    (hK i).image (D.ι_isOpenEmbedding i).continuous

/-- Connectivity of the graph whose vertices are pieces and whose edges are nonempty overlaps. -/
public def GluingIntersectionGraphConnected (D : TopCat.GlueData.{w}) : Prop :=
  ∀ i j, Relation.ReflTransGen
    (fun i j : D.J ↦ (Set.range (D.toGlueData.ι i) ∩
      Set.range (D.toGlueData.ι j)).Nonempty) i j

/-- Connected pieces with a connected overlap graph have connected gluing. -/
public theorem connectedSpace_gluedSpace (D : TopCat.GlueData.{w}) [Nonempty D.J]
    [∀ i, ConnectedSpace (D.U i)] (h : GluingIntersectionGraphConnected D) :
    ConnectedSpace (GluedSpace D) := by
  rw [connectedSpace_iff_univ]
  have huniv : (Set.univ : Set (GluedSpace D)) =
      ⋃ i, Set.range (D.toGlueData.ι i) := by
    ext x
    simp only [mem_univ, mem_iUnion, mem_range, true_iff]
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    exact ⟨i, y, hy⟩
  rw [huniv]
  apply IsConnected.iUnion_of_reflTransGen
  · intro i
    simpa only [image_univ] using
      isConnected_univ.image (D.toGlueData.ι i)
        (D.ι_isOpenEmbedding i).continuous.continuousOn
  · exact h

variable (D : TopCat.GlueData.{w})

/-- Choose a piece containing a given point of the glued space. -/
public noncomputable def gluedPieceIndex (x : GluedSpace D) : D.J :=
  (D.ι_jointly_surjective x).choose

/-- Choose a preimage of a glued point in its selected piece. -/
public noncomputable def gluedPiecePoint (x : GluedSpace D) : D.U (gluedPieceIndex D x) :=
  (D.ι_jointly_surjective x).choose_spec.choose

public theorem gluedPiecePoint_maps (x : GluedSpace D) :
    D.toGlueData.ι (gluedPieceIndex D x) (gluedPiecePoint D x) = x :=
  (D.ι_jointly_surjective x).choose_spec.choose_spec

/-- The atlas obtained by transporting every piece atlas through its canonical open embedding. -/
@[instance_reducible]
public noncomputable def gluedChartedSpace [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] : ChartedSpace H (GluedSpace D) where
  atlas := ⋃ i, (fun c ↦ (pieceOpenPartialHomeomorph D i).symm.trans c) '' atlas H (D.U i)
  chartAt x :=
    (pieceOpenPartialHomeomorph D (gluedPieceIndex D x)).symm.trans
      (chartAt H (gluedPiecePoint D x))
  mem_chart_source x := by
    let i := gluedPieceIndex D x
    let y := gluedPiecePoint D x
    have hxy : D.toGlueData.ι i y = x := gluedPiecePoint_maps D x
    change x ∈ (pieceOpenPartialHomeomorph D i).target ∩
      (pieceOpenPartialHomeomorph D i).symm ⁻¹' (chartAt H y).source
    constructor
    · unfold pieceOpenPartialHomeomorph
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨y, hxy⟩
    · change (pieceOpenPartialHomeomorph D i).symm x ∈ (chartAt H y).source
      have hinv : (pieceOpenPartialHomeomorph D i).symm x = y := by
        rw [← hxy]
        exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _
      rw [hinv]
      exact mem_chart_source H _
  chart_mem_atlas x := by
    refine mem_iUnion.mpr ⟨gluedPieceIndex D x, ?_⟩
    exact ⟨chartAt H (gluedPiecePoint D x), chart_mem_atlas H _, rfl⟩

/-- Exact compatibility condition needed to make the transported piece atlas a manifold atlas. -/
public def GluingAtlasCompatible [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] : Prop :=
  ∀ (i j : D.J) (c : OpenPartialHomeomorph (D.U i) H)
    (c' : OpenPartialHomeomorph (D.U j) H), c ∈ atlas H (D.U i) →
      c' ∈ atlas H (D.U j) →
      ((pieceOpenPartialHomeomorph D i).symm.trans c).symm.trans
          ((pieceOpenPartialHomeomorph D j).symm.trans c') ∈ contDiffGroupoid n I

/-- Compatible transported piece charts make the glued space a manifold. -/
public theorem isManifold_gluedChartedSpace [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] (hcompat : GluingAtlasCompatible (I := I) (n := n) D) :
    @IsManifold 𝕜 inferInstance E inferInstance inferInstance H inferInstance I n (GluedSpace D)
      inferInstance (gluedChartedSpace D) := by
  let cG : ChartedSpace H (GluedSpace D) := gluedChartedSpace D
  let hG : @HasGroupoid H inferInstance (GluedSpace D) inferInstance cG
      (contDiffGroupoid n I) := by
    refine ⟨fun {e e'} he he' ↦ ?_⟩
    change e ∈ ⋃ i, _ at he
    change e' ∈ ⋃ i, _ at he'
    obtain ⟨i, c, hc, rfl⟩ := mem_iUnion.mp he
    obtain ⟨j, c', hc', rfl⟩ := mem_iUnion.mp he'
    exact hcompat i j c c' hc hc'
  exact @IsManifold.mk' 𝕜 inferInstance E inferInstance inferInstance H inferInstance I n
    (GluedSpace D) inferInstance cG hG

end SphereSixComplex
