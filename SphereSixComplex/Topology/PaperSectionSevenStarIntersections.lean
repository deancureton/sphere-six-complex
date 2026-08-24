module

public import SphereSixComplex.Geometry.PaperBiholomorphicStar
public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification

/-!
# The actual intersections in the Section 7 star cover

This file identifies the nontrivial point-set intersections of the concrete four-piece star
cover.  A singleton intersection is its corresponding gluing piece, a central--filling
intersection is the common collar source, and any intersection containing two distinct filling
indices is empty.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set Topology

namespace SphereSixComplex

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- The common collar source mapped into the glued space through the central piece. -/
public def collarSourceToGlued (i : Fin 3) :
    A.collarSource i → GluedSpace A.toFourPieceStarGluingData.glueData :=
  fun x ↦ A.toFourPieceStarGluingData.glueData.toGlueData.ι none (A.toCentral i x)

/-- The common collar source embeds openly in the glued space. -/
public theorem collarSourceToGlued_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (A.collarSourceToGlued i) :=
  (A.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding none).comp
    (A.toCentral_isOpenEmbedding i)

/-- The image of a common collar source is exactly the overlap of the central piece with the
corresponding filling piece. -/
public theorem range_collarSourceToGlued (i : Fin 3) :
    Set.range (A.collarSourceToGlued i) =
      (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ := by
  let D := A.toFourPieceStarGluingData.glueData
  rw [show (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece 0 =
    Set.range (D.toGlueData.ι none) from rfl]
  rw [show (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ =
    Set.range (D.toGlueData.ι (some i)) from rfl]
  rw [D.image_inter none (some i)]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨A.centralCollarPoint i y, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, ?_⟩
    change D.toGlueData.ι none (A.toCentral i z) = D.toGlueData.ι none y.1
    rw [hz]

/-- Every singleton intersection of the star cover is homeomorphic to its gluing piece. -/
public noncomputable def singletonIntersectionHomeomorph (j : Fin 4) :
    A.toFourPieceStarGluingData.glueData.U (sectionSevenFourPieceStarIndex j) ≃ₜ
      finiteCoverIntersection
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece {j} := by
  let e :
      A.toFourPieceStarGluingData.glueData.U (sectionSevenFourPieceStarIndex j) ≃ₜ
        Set.range (A.toFourPieceStarGluingData.glueData.toGlueData.ι
          (sectionSevenFourPieceStarIndex j)) :=
    (A.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding
      (sectionSevenFourPieceStarIndex j)).isEmbedding.toHomeomorph
  refine e.trans (Homeomorph.setCongr ?_)
  ext x
  simp [finiteCoverIntersection, sectionSevenStarOpenCover]

/-- The central--filling intersection is homeomorphic to the exact common collar source used in
the analytic gluing. -/
public noncomputable def centralFillingIntersectionHomeomorph (i : Fin 3) :
    A.collarSource i ≃ₜ
      finiteCoverIntersection
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece {0, i.succ} := by
  let e : A.collarSource i ≃ₜ Set.range (A.collarSourceToGlued i) :=
    (A.collarSourceToGlued_isOpenEmbedding i).isEmbedding.toHomeomorph
  refine e.trans (Homeomorph.setCongr ?_)
  rw [A.range_collarSourceToGlued i]
  ext x
  simp [finiteCoverIntersection, Set.inter_comm]

/-- Distinct filling images in the four-piece star are disjoint. -/
public theorem fillingPiece_inter_fillingPiece {i j : Fin 3} (hij : i ≠ j) :
    (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ ∩
      (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece j.succ = ∅ := by
  let D := A.toFourPieceStarGluingData.glueData
  rw [show (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ =
    Set.range (D.toGlueData.ι (some i)) from rfl]
  rw [show (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece j.succ =
    Set.range (D.toGlueData.ι (some j)) from rfl]
  rw [D.image_inter (some i) (some j)]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simpa [FourPieceStarGluingData.overlap, hij] using y.2
  · simp

/-- Any finite cover intersection containing two distinct filling indices is empty. -/
public theorem finiteCoverIntersection_eq_empty_of_two_fillings
    (s : Finset (Fin 4)) {i j : Fin 3} (hi : i.succ ∈ s) (hj : j.succ ∈ s)
    (hij : i ≠ j) :
    finiteCoverIntersection
      (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece s = ∅ := by
  ext x
  constructor
  · intro hx
    have hmem := (mem_finiteCoverIntersection_iff
      (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece s x).mp hx
    have hpair :
        x ∈ (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ ∩
          (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece j.succ :=
      ⟨hmem i.succ hi, hmem j.succ hj⟩
    rw [A.fillingPiece_inter_fillingPiece hij] at hpair
    exact hpair
  · simp

end OpenEmbeddingStarData

namespace Geometry.PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The exact singular-intersection diagram for the concrete analytic four-piece star.  This is
the canonical unreduced local model; reducing it to the finite Section 7 matrix requires the
additional deformation-retract data isolated by the preceding homeomorphisms. -/
public noncomputable def sectionSevenSingularIntersectionChainModels :
    SectionSevenStarIntersectionChainModels
      P.openEmbeddingStarData.toFourPieceStarGluingData :=
  SectionSevenStarIntersectionChainModels.singularIntersectionModels
    P.openEmbeddingStarData.toFourPieceStarGluingData

/-- The actual central--filling intersections are the cusp and elliptic common collar sources
selected by the analytic construction. -/
public noncomputable def sectionSevenCentralFillingIntersectionHomeomorph (i : Fin 3) :
    P.openEmbeddingStarData.collarSource i ≃ₜ
      finiteCoverIntersection
        (sectionSevenStarOpenCover
          P.openEmbeddingStarData.toFourPieceStarGluingData).piece {0, i.succ} :=
  P.openEmbeddingStarData.centralFillingIntersectionHomeomorph i

end Geometry.PaperAnalyticData

end SphereSixComplex
