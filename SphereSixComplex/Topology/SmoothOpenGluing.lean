module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Gluing

/-!
# Smooth structures on open gluings

Mathlib's `TopCat.GlueData` constructs a topological space by gluing a family of spaces along
open subsets, and proves that every canonical piece map is an open embedding.  This file supplies
the generic differential-topological layer on top of that construction.

The disjoint-union cover map from the sigma type of pieces to the glued space is a surjective
local homeomorphism, hence an open quotient map.  Consequently, second countability descends from
a finite family of second-countable pieces.  Charts on the pieces can also be pushed through the
canonical open embeddings to give an explicit charted-space structure on the gluing.  For that
structure, the manifold obligation is exactly pairwise compatibility of the pushed piece charts
with the desired differentiability groupoid.

This module deliberately does not assert that arbitrary open gluing data are Hausdorff or compact:
both assertions are false without additional hypotheses.  A closed-kernel criterion below isolates
the precise Hausdorff obligation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set TopologicalSpace Topology

namespace SphereSixComplex

universe u v

/-- The canonical map from the topological disjoint union of the pieces to their open gluing. -/
public def openGluingCoverMap (D : TopCat.GlueData.{u}) :
    (Sigma fun i ↦ (D.U i : Type u)) → D.toGlueData.glued :=
  fun p ↦ D.toGlueData.ι p.1 p.2

/-- The disjoint-union cover map of an open gluing is a local homeomorphism.

Near a point in one summand, a local inverse is obtained by composing the inverse of the open
embedding of that summand into the sigma type with the canonical open embedding into the gluing.
-/
public theorem openGluingCoverMap_isLocalHomeomorph (D : TopCat.GlueData.{u}) :
    IsLocalHomeomorph (openGluingCoverMap D) := by
  apply IsLocalHomeomorph.mk
  rintro ⟨i, x⟩
  let _ : Nonempty (D.U i : Type u) := ⟨x⟩
  let _ : Nonempty (Sigma fun i ↦ (D.U i : Type u)) := ⟨⟨i, x⟩⟩
  let hi : IsOpenEmbedding (@Sigma.mk D.J (fun i ↦ (D.U i : Type u)) i) :=
    IsOpenEmbedding.sigmaMk
  let hj : IsOpenEmbedding (D.toGlueData.ι i) := D.ι_isOpenEmbedding i
  let e : OpenPartialHomeomorph (Sigma fun i ↦ (D.U i : Type u)) D.toGlueData.glued :=
    (hi.toOpenPartialHomeomorph _).symm.trans (hj.toOpenPartialHomeomorph _)
  refine ⟨e, ?_, ?_⟩
  · simp [e]
  · intro y hy
    obtain ⟨z, rfl⟩ : ∃ z : (D.U i : Type u), Sigma.mk i z = y := by
      rcases y with ⟨j, y⟩
      have hji : j = i := by simpa [e] using hy
      subst j
      exact ⟨y, rfl⟩
    simp only [openGluingCoverMap, e, OpenPartialHomeomorph.trans_apply]
    rw [hi.toOpenPartialHomeomorph_left_inv]
    exact congrFun (hj.toOpenPartialHomeomorph_apply _) z |>.symm

/-- The canonical disjoint-union cover map is surjective. -/
public theorem openGluingCoverMap_surjective (D : TopCat.GlueData.{u}) :
    Function.Surjective (openGluingCoverMap D) := by
  intro x
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact ⟨⟨i, y⟩, rfl⟩

/-- The canonical disjoint-union cover map is an open quotient map. -/
public theorem openGluingCoverMap_isOpenQuotientMap (D : TopCat.GlueData.{u}) :
    IsOpenQuotientMap (openGluingCoverMap D) where
  surjective := openGluingCoverMap_surjective D
  continuous := (openGluingCoverMap_isLocalHomeomorph D).continuous
  isOpenMap := (openGluingCoverMap_isLocalHomeomorph D).isOpenMap

/-- A finite open gluing of second-countable spaces is second countable. -/
public theorem openGluing_secondCountableTopology (D : TopCat.GlueData.{u}) [Finite D.J]
    [∀ i, SecondCountableTopology (D.U i)] :
    SecondCountableTopology D.toGlueData.glued := by
  exact (openGluingCoverMap_isOpenQuotientMap D).isQuotientMap.secondCountableTopology
    (openGluingCoverMap_isLocalHomeomorph D).isOpenMap

/-- A closed kernel relation for the disjoint-union cover map makes the open gluing Hausdorff.

For concrete gluing data, the remaining hypothesis can be proved piecewise by identifying the
kernel with the graphs of the transition maps.
-/
public theorem openGluing_t2Space_of_closedKernel (D : TopCat.GlueData.{u})
    (hclosed : IsClosed {p :
      (Sigma fun i ↦ (D.U i : Type u)) × (Sigma fun i ↦ (D.U i : Type u)) |
        openGluingCoverMap D p.1 = openGluingCoverMap D p.2}) :
    T2Space D.toGlueData.glued :=
  (t2Space_iff_of_isOpenQuotientMap (openGluingCoverMap_isOpenQuotientMap D)).2 hclosed

section Charts

variable {H : Type v} [TopologicalSpace H]
  (D : TopCat.GlueData.{u}) [∀ i, ChartedSpace H (D.U i)]

/-- A chart on a piece, pushed to the glued space through its canonical open embedding. -/
public noncomputable def openGluingPieceChart
    (p : Sigma fun i ↦ (D.U i : Type u)) :
    OpenPartialHomeomorph D.toGlueData.glued H := by
  let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
  exact ((D.ι_isOpenEmbedding p.1).toOpenPartialHomeomorph _).symm.trans
    (chartAt H p.2)

/-- A chosen lift of a point of the gluing to one of its pieces. -/
public noncomputable def openGluingChosenLift (x : D.toGlueData.glued) :
    Sigma fun i ↦ (D.U i : Type u) :=
  let h := D.ι_jointly_surjective x
  ⟨h.choose, h.choose_spec.choose⟩

/-- The chosen lift maps back to the original point of the gluing. -/
public theorem openGluingChosenLift_spec (x : D.toGlueData.glued) :
    D.toGlueData.ι (openGluingChosenLift D x).1 (openGluingChosenLift D x).2 = x :=
  (D.ι_jointly_surjective x).choose_spec.choose_spec

/-- The charted-space structure obtained by pushing the preferred charts of all pieces to the
glued space. -/
@[instance_reducible]
public noncomputable def openGluingChartedSpace : ChartedSpace H D.toGlueData.glued where
  atlas := Set.range (openGluingPieceChart D)
  chartAt x := openGluingPieceChart D (openGluingChosenLift D x)
  mem_chart_source x := by
    let p := openGluingChosenLift D x
    let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
    have hpx : D.toGlueData.ι p.1 p.2 = x := openGluingChosenLift_spec D x
    have hmem : D.toGlueData.ι p.1 p.2 ∈
        (openGluingPieceChart (H := H) D p).source := by
      simp only [openGluingPieceChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
        OpenPartialHomeomorph.symm_source,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_range,
        Set.mem_preimage]
      constructor
      · exact ⟨p.2, rfl⟩
      · rw [(D.ι_isOpenEmbedding p.1).toOpenPartialHomeomorph_left_inv]
        exact mem_chart_source H p.2
    rw [hpx] at hmem
    exact hmem
  chart_mem_atlas x := ⟨openGluingChosenLift D x, rfl⟩

/-- The exact smooth compatibility condition for the pushed piece charts of an open gluing. -/
public def OpenGluingSmoothCompatibility
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) : Prop :=
  ∀ p q : Sigma fun i ↦ (D.U i : Type u),
    (openGluingPieceChart D p).symm.trans (openGluingPieceChart D q) ∈
      contDiffGroupoid n I

/-- Pairwise smooth compatibility of the pushed piece charts equips the open gluing with the
corresponding manifold structure. -/
public theorem openGluing_isManifold_of_pieceChart_compatible
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (hcompat : OpenGluingSmoothCompatibility D I n) :
    @IsManifold 𝕜 _ E _ _ H _ I n D.toGlueData.glued _ (openGluingChartedSpace D) := by
  let _ : ChartedSpace H D.toGlueData.glued := openGluingChartedSpace D
  refine { compatible := ?_ }
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  exact hcompat p q

end Charts

end SphereSixComplex
