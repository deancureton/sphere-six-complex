module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenStarIntersections

/-!
# Source-faithful Mayer--Vietoris interface for Section 7

The four-piece star has seven relevant local spaces: the central piece, three fillings, and the
three common collar sources.  This file records chain models for exactly that diagram and the
strict comparison squares needed to transport its attaching maps to singular chains.

The three successive Mayer--Vietoris overlaps are identified exactly.  A later assembly must use
the homotopy cofibers of this seven-space diagram; no identification with the finite Leray model
or with a Čech total complex is asserted here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)


/-- At every Mayer--Vietoris stage, the new filling meets the preceding union only in its
central collar.  Earlier fillings contribute no additional points to this overlap. -/
public theorem stage_inter_filling_eq_central_inter (r : Fin 3) :
    (sectionSevenStarOpenCover A.toFourPieceStarGluingData).stage r.castSucc ∩
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece r.succ =
      (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece r.succ := by
  ext x
  constructor
  · rintro ⟨hxstage, hxnew⟩
    rw [FourPieceOpenCover.stage] at hxstage
    simp only [mem_iUnion] at hxstage
    obtain ⟨j, hj, hxj⟩ := hxstage
    by_cases hj0 : j = 0
    · subst j
      exact ⟨hxj, hxnew⟩
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
      by_cases hir : i = r
      · subst i
        exact (not_le_of_gt (Fin.castSucc_lt_succ : r.castSucc < r.succ) hj).elim
      · have hpair :
            x ∈ (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece i.succ ∩
              (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece r.succ :=
          ⟨hxj, hxnew⟩
        rw [A.fillingPiece_inter_fillingPiece hir] at hpair
        exact hpair.elim
  · rintro ⟨hxcentral, hxnew⟩
    refine ⟨?_, hxnew⟩
    rw [FourPieceOpenCover.stage]
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨Fin.zero_le _, hxcentral⟩⟩

/-- The actual common collar source is homeomorphic to the overlap appearing in the corresponding
successive Mayer--Vietoris sequence. -/
public noncomputable def collarToMayerVietorisOverlapHomeomorph (r : Fin 3) :
    A.collarSource r ≃ₜ
      ((sectionSevenStarOpenCover A.toFourPieceStarGluingData).stage r.castSucc ∩
        (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece r.succ : Set
          (GluedSpace A.toFourPieceStarGluingData.glueData)) :=
  (A.centralFillingIntersectionHomeomorph r).trans
    (Homeomorph.setCongr (by
      simpa [finiteCoverIntersection, inter_comm] using
        (A.stage_inter_filling_eq_central_inter r).symm))

end OpenEmbeddingStarData

end SphereSixComplex
