module

public import SphereSixComplex.Topology.SmoothOpenGluing
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth transition criteria for open gluings

This file turns the abstract chart-compatibility obligation of
`OpenGluingSmoothCompatibility` into the geometric condition one normally verifies: the
partial change of pieces over every overlap is smooth in both directions.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

namespace SphereSixComplex

universe u v

/-- The partial homeomorphism from the piece containing `p` to the piece containing `q`, obtained
by passing through their canonical open embeddings into the glued space.

The points `p` and `q` provide the nonemptiness instances needed to extend the local inverses of
the two open embeddings to total inverse functions.  On the source of the partial homeomorphism,
the resulting map is canonical.
-/
public noncomputable def openGluingPieceTransition (D : TopCat.GlueData.{u})
    (p q : Sigma fun i ↦ (D.U i : Type u)) :
    OpenPartialHomeomorph (D.U p.1) (D.U q.1) := by
  let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
  let _ : Nonempty (D.U q.1 : Type u) := ⟨q.2⟩
  exact ((D.ι_isOpenEmbedding p.1).toOpenPartialHomeomorph _).trans
    ((D.ι_isOpenEmbedding q.1).toOpenPartialHomeomorph _).symm

/-- The domain of the partial change of pieces is precisely the overlap specified by the gluing
data. -/
public theorem openGluingPieceTransition_source (D : TopCat.GlueData.{u})
    (p q : Sigma fun i ↦ (D.U i : Type u)) :
    (openGluingPieceTransition D p q).source = Set.range (D.f p.1 q.1) := by
  let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
  let _ : Nonempty (D.U q.1 : Type u) := ⟨q.2⟩
  simp only [openGluingPieceTransition, OpenPartialHomeomorph.trans_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, univ_inter]
  exact D.preimage_range q.1 p.1

/-- On an overlap point, the partial change of pieces is the transition prescribed by the gluing
data. -/
public theorem openGluingPieceTransition_apply_f (D : TopCat.GlueData.{u})
    (p q : Sigma fun i ↦ (D.U i : Type u)) (z : D.V (p.1, q.1)) :
    openGluingPieceTransition D p q (D.f p.1 q.1 z) =
      D.f q.1 p.1 (D.t p.1 q.1 z) := by
  let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
  let _ : Nonempty (D.U q.1 : Type u) := ⟨q.2⟩
  apply (D.ι_isOpenEmbedding q.1).isEmbedding.injective
  rw [show D.toGlueData.ι q.1 (openGluingPieceTransition D p q (D.f p.1 q.1 z)) =
      D.toGlueData.ι p.1 (D.f p.1 q.1 z) by
    simp only [openGluingPieceTransition, OpenPartialHomeomorph.trans_apply,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    apply (D.ι_isOpenEmbedding q.1).toOpenPartialHomeomorph_right_inv
    exact ⟨D.f q.1 p.1 (D.t p.1 q.1 z), CategoryTheory.GlueData.glue_condition_apply _ _ _ _⟩]
  exact (CategoryTheory.GlueData.glue_condition_apply D.toGlueData p.1 q.1 z).symm

/-- Reversing a partial change of pieces exchanges the two pieces. -/
public theorem openGluingPieceTransition_symm (D : TopCat.GlueData.{u})
    (p q : Sigma fun i ↦ (D.U i : Type u)) :
    (openGluingPieceTransition D p q).symm = openGluingPieceTransition D q p := by
  let _ : Nonempty (D.U p.1 : Type u) := ⟨p.2⟩
  let _ : Nonempty (D.U q.1 : Type u) := ⟨q.2⟩
  simp only [openGluingPieceTransition,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

/-- The image of the partial change of pieces is the overlap in the target piece. -/
public theorem openGluingPieceTransition_target (D : TopCat.GlueData.{u})
    (p q : Sigma fun i ↦ (D.U i : Type u)) :
    (openGluingPieceTransition D p q).target = Set.range (D.f q.1 p.1) := by
  rw [← OpenPartialHomeomorph.symm_source, openGluingPieceTransition_symm,
    openGluingPieceTransition_source]

section ChartTransitions

variable {H : Type v} [TopologicalSpace H]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)

/-- Composing a smooth partial diffeomorphism with a chart on its target produces a member of the
maximal atlas on its source. -/
public theorem OpenPartialHomeomorph.trans_chart_mem_maximalAtlas
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N]
    [IsManifold I n M] [IsManifold I n N]
    (f : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn I I n f f.source)
    (hf_symm : ContMDiffOn I I n f.symm f.target)
    (y : N) :
    f.trans (chartAt H y) ∈ IsManifold.maximalAtlas I n M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hc : ContMDiffOn I I n (chartAt H y) (chartAt H y).source :=
      contMDiffOn_chart (x := y)
    convert hc.comp' hf using 1 <;> rfl
  · have hc : ContMDiffOn I I n (chartAt H y).symm (chartAt H y).target :=
      contMDiffOn_chart_symm (x := y)
    convert hf_symm.comp' hc using 1 <;> rfl

/-- A smooth partial diffeomorphism between manifolds gives a smooth coordinate change between
any source chart and any target chart. -/
public theorem OpenPartialHomeomorph.chart_transition_mem_contDiffGroupoid
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N]
    [IsManifold I n M] [IsManifold I n N]
    (f : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn I I n f f.source)
    (hf_symm : ContMDiffOn I I n f.symm f.target)
    (x : M) (y : N) :
    ((chartAt H x).symm.trans f).trans (chartAt H y) ∈ contDiffGroupoid n I := by
  rw [OpenPartialHomeomorph.trans_assoc]
  exact StructureGroupoid.compatible_of_mem_maximalAtlas_right
    (SphereSixComplex.OpenPartialHomeomorph.trans_chart_mem_maximalAtlas
      I n f hf hf_symm y)

end ChartTransitions

section Gluing

variable {H : Type v} [TopologicalSpace H]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (D : TopCat.GlueData.{u}) [∀ i, ChartedSpace H (D.U i)]
  (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)

/-- A convenient way to prove smoothness of a canonical piece transition is to extend its explicit
`D.f ∘ D.t` formula to a smooth map on the source piece.  Only smoothness on the overlap range
is needed. -/
public theorem contMDiffOn_openGluingPieceTransition_of_eqOn
    (p q : Sigma fun i ↦ (D.U i : Type u)) (g : D.U p.1 → D.U q.1)
    (hg : ContMDiffOn I I n g (Set.range (D.f p.1 q.1)))
    (heq : ∀ z : D.V (p.1, q.1),
      g (D.f p.1 q.1 z) = D.f q.1 p.1 (D.t p.1 q.1 z)) :
    ContMDiffOn I I n (openGluingPieceTransition D p q)
      (openGluingPieceTransition D p q).source := by
  rw [openGluingPieceTransition_source]
  apply hg.congr
  rintro _ ⟨z, rfl⟩
  rw [openGluingPieceTransition_apply_f, heq]

variable [∀ i, IsManifold I n (D.U i)]

/-- If every partial change of pieces in an open gluing is `C^n` in both directions, then the
piece charts pushed to the gluing are pairwise `C^n`-compatible. -/
public theorem openGluingSmoothCompatibility_of_contMDiffOn_pieceTransition_and_symm
    (htrans : ∀ p q : Sigma fun i ↦ (D.U i : Type u),
      ContMDiffOn I I n (openGluingPieceTransition D p q)
          (openGluingPieceTransition D p q).source ∧
        ContMDiffOn I I n (openGluingPieceTransition D p q).symm
          (openGluingPieceTransition D p q).target) :
    OpenGluingSmoothCompatibility D I n := by
  intro p q
  have h := SphereSixComplex.OpenPartialHomeomorph.chart_transition_mem_contDiffGroupoid
    I n (openGluingPieceTransition D p q) (htrans p q).1 (htrans p q).2 p.2 q.2
  simpa only [openGluingPieceChart, openGluingPieceTransition,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using h

/-- To verify smooth compatibility of an open gluing, it suffices to prove that every ordered
partial change of pieces is `C^n`.  The reverse-direction obligations are supplied by the same
hypothesis with the indices exchanged. -/
public theorem openGluingSmoothCompatibility_of_contMDiffOn_pieceTransition
    (htrans : ∀ p q : Sigma fun i ↦ (D.U i : Type u),
      ContMDiffOn I I n (openGluingPieceTransition D p q)
        (openGluingPieceTransition D p q).source) :
    OpenGluingSmoothCompatibility D I n := by
  apply openGluingSmoothCompatibility_of_contMDiffOn_pieceTransition_and_symm D I n
  intro p q
  refine ⟨htrans p q, ?_⟩
  simpa only [openGluingPieceTransition_symm, ← OpenPartialHomeomorph.symm_source] using
    htrans q p

/-- An open gluing whose ordered piece changes are smooth is a manifold for the
charted-space structure built from the pushed piece charts. -/
public theorem openGluing_isManifold_of_contMDiffOn_pieceTransition
    (htrans : ∀ p q : Sigma fun i ↦ (D.U i : Type u),
      ContMDiffOn I I n (openGluingPieceTransition D p q)
        (openGluingPieceTransition D p q).source) :
    @IsManifold 𝕜 _ E _ _ H _ I n D.toGlueData.glued _ (openGluingChartedSpace D) :=
  openGluing_isManifold_of_pieceChart_compatible D I n
    (openGluingSmoothCompatibility_of_contMDiffOn_pieceTransition D I n htrans)

end Gluing

end SphereSixComplex
