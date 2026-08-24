module

public import SphereSixComplex.Geometry.Gluing
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff gluing from a closed identification relation

The canonical map from the disjoint union of the pieces of a topological gluing is an open
quotient map.  Consequently, the glued space is Hausdorff exactly when the induced equivalence
relation on the disjoint union is closed.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex

noncomputable section

universe u

variable (D : TopCat.GlueData.{u})

/-- The canonical projection from the disjoint union of all gluing pieces. -/
public def glueProjection : (Σ i, D.U i) → GluedSpace D :=
  fun x ↦ D.toGlueData.ι x.1 x.2

public theorem glueProjection_continuous : Continuous (glueProjection D) := by
  apply continuous_sigma
  intro i
  exact (D.ι_isOpenEmbedding i).continuous

public theorem glueProjection_isOpenMap : IsOpenMap (glueProjection D) := by
  rw [isOpenMap_sigma]
  intro i
  exact (D.ι_isOpenEmbedding i).isOpenMap

public theorem glueProjection_surjective : Function.Surjective (glueProjection D) := by
  intro x
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact ⟨⟨i, y⟩, rfl⟩

/-- The canonical gluing projection is an open quotient map. -/
public theorem glueProjection_isOpenQuotientMap : IsOpenQuotientMap (glueProjection D) where
  surjective := glueProjection_surjective D
  continuous := glueProjection_continuous D
  isOpenMap := glueProjection_isOpenMap D

/-- The part of the gluing relation between two fixed pieces. -/
@[expose] public def glueRelComponent (i j : D.J) : Set (D.U i × D.U j) :=
  {q | D.Rel ⟨i, q.1⟩ ⟨j, q.2⟩}

/-- Include a fixed pair of pieces into the square of the full disjoint union. -/
public def sigmaPairInclusion (i j : D.J) :
    D.U i × D.U j → (Σ k, D.U k) × (Σ k, D.U k) :=
  Prod.map (@Sigma.mk D.J (fun k ↦ D.U k) i)
    (@Sigma.mk D.J (fun k ↦ D.U k) j)

public theorem sigmaPairInclusion_isClosedEmbedding (i j : D.J) :
    IsClosedEmbedding (sigmaPairInclusion D i j) :=
  Topology.IsClosedEmbedding.sigmaMk.prodMap Topology.IsClosedEmbedding.sigmaMk

/-- The global relation is the union of its fixed-pair components. -/
public theorem glueRel_eq_iUnion_components :
    {q : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel q.1 q.2} =
      ⋃ i, ⋃ j, sigmaPairInclusion D i j '' glueRelComponent D i j := by
  ext q
  rcases q with ⟨⟨i, x⟩, ⟨j, y⟩⟩
  constructor
  · intro h
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
      ⟨(x, y), h, rfl⟩⟩⟩
  · intro h
    obtain ⟨i', hi'⟩ := Set.mem_iUnion.mp h
    obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp hi'
    obtain ⟨q, hq, hqeq⟩ := hj'
    cases hqeq
    exact hq

/-- For a finite gluing diagram, it is enough to prove closedness separately on every ordered
pair of pieces. -/
public theorem glueRel_isClosed_of_components [Finite D.J]
    (h : ∀ i j, IsClosed (glueRelComponent D i j)) :
    IsClosed {q : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel q.1 q.2} := by
  rw [glueRel_eq_iUnion_components D]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_iUnion_of_finite fun j ↦
    (sigmaPairInclusion_isClosedEmbedding D i j).isClosed_iff_image_isClosed.mp (h i j)

/-- A topological gluing is Hausdorff exactly when its explicit identification relation on the
disjoint union of pieces is closed. -/
public theorem t2Space_gluedSpace_iff_isClosed_rel :
    T2Space (GluedSpace D) ↔
      IsClosed {q : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel q.1 q.2} := by
  simpa only [glueProjection, D.ι_eq_iff_rel] using
    (t2Space_iff_of_isOpenQuotientMap (glueProjection_isOpenQuotientMap D))

/-- Closedness of the explicit gluing relation supplies the Hausdorff instance required by the
manifold assembly. -/
public theorem t2Space_gluedSpace_of_isClosed_rel
    (h : IsClosed {q : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel q.1 q.2}) :
    T2Space (GluedSpace D) :=
  (t2Space_gluedSpace_iff_isClosed_rel D).2 h

/-- A finite gluing is Hausdorff when every fixed-pair relation component is closed. -/
public theorem t2Space_gluedSpace_of_closed_components [Finite D.J]
    (h : ∀ i j, IsClosed (glueRelComponent D i j)) :
    T2Space (GluedSpace D) :=
  t2Space_gluedSpace_of_isClosed_rel D (glueRel_isClosed_of_components D h)

/-- A finite family of compact subsets whose canonical images cover the gluing makes the glued
space compact.  Unlike `compactSpace_gluedSpace`, the ambient pieces themselves need not be
compact. -/
public theorem compactSpace_gluedSpace_of_compact_cover [Finite D.J]
    (K : ∀ i, Set (D.U i)) (hK : ∀ i, IsCompact (K i))
    (hcover : (Set.univ : Set (GluedSpace D)) =
      ⋃ i, D.toGlueData.ι i '' K i) : CompactSpace (GluedSpace D) := by
  rw [← isCompact_univ_iff, hcover]
  exact isCompact_iUnion fun i ↦ (hK i).image (D.ι_isOpenEmbedding i).continuous

/-- Exact topological completion data for a finite gluing: closed pairwise identifications and a
finite compact cover selected inside its possibly noncompact open pieces. -/
public structure GluingCompletionData where
  relComponent_closed : ∀ i j, IsClosed (glueRelComponent D i j)
  compactSubset : ∀ i, Set (D.U i)
  compactSubset_isCompact : ∀ i, IsCompact (compactSubset i)
  compactSubset_covers : (Set.univ : Set (GluedSpace D)) =
    ⋃ i, D.toGlueData.ι i '' compactSubset i

namespace GluingCompletionData

variable (C : GluingCompletionData D)

include C

/-- Closed pairwise identifications give the completed gluing a Hausdorff topology. -/
public theorem t2Space [Finite D.J] : T2Space (GluedSpace D) :=
  t2Space_gluedSpace_of_closed_components D
    (GluingCompletionData.relComponent_closed C)

/-- The selected compact subpieces cover the completed gluing. -/
public theorem compactSpace [Finite D.J] : CompactSpace (GluedSpace D) :=
  compactSpace_gluedSpace_of_compact_cover D
    (GluingCompletionData.compactSubset C)
    (GluingCompletionData.compactSubset_isCompact C)
    (GluingCompletionData.compactSubset_covers C)

end GluingCompletionData

end

end SphereSixComplex
