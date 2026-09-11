module

public import SphereSixComplex.Paper.Geometry.PaperBiholomorphicStar
public import SphereSixComplex.Paper.Topology.SectionSevenPaperCoverIdentification

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


end OpenEmbeddingStarData

end SphereSixComplex
