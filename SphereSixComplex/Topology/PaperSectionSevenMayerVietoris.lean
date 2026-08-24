module

public import SphereSixComplex.Topology.PaperSectionSevenStarIntersections

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

/-- Chain models for the seven spaces in a four-piece star: one central space, three filling
spaces, and three collar spaces, together with the two attaching maps from every collar. -/
public structure SevenSpaceChainModels where
  /-- A chain model for the central space. -/
  centralModel : ChainComplex AddCommGrpCat ℕ
  /-- A chain model for each of the three filling spaces. -/
  fillingModel : Fin 3 → ChainComplex AddCommGrpCat ℕ
  /-- A chain model for each of the three common collar sources. -/
  collarModel : Fin 3 → ChainComplex AddCommGrpCat ℕ
  /-- The model map induced by attaching a collar to the central space. -/
  collarToCentral : ∀ i, collarModel i ⟶ centralModel
  /-- The model map induced by attaching a collar to its filling. -/
  collarToFilling : ∀ i, collarModel i ⟶ fillingModel i
  /-- The central model computes the singular chains of the actual central space. -/
  centralRealization : HomotopyEquiv centralModel (IntegralSingularChainComplex A.central)
  /-- Every filling model computes the singular chains of the corresponding actual filling. -/
  fillingRealization : ∀ i,
    HomotopyEquiv (fillingModel i) (IntegralSingularChainComplex (A.filling i))
  /-- Every collar model computes the singular chains of the corresponding common source. -/
  collarRealization : ∀ i,
    HomotopyEquiv (collarModel i) (IntegralSingularChainComplex (A.collarSource i))
  /-- The central attaching map is the exact map induced by the actual collar embedding. -/
  collarToCentral_naturality : ∀ i,
    collarToCentral i ≫ centralRealization.hom =
      (collarRealization i).hom ≫ integralSingularChainMap (A.toCentral i).hom
  /-- The filling attaching map is the exact map induced by the actual collar embedding. -/
  collarToFilling_naturality : ∀ i,
    collarToFilling i ≫ (fillingRealization i).hom =
      (collarRealization i).hom ≫ integralSingularChainMap (A.toFilling i).hom

namespace SevenSpaceChainModels

/-- The exact seven-space diagram with unreduced singular chains at every vertex. -/
public noncomputable def singularModels : A.SevenSpaceChainModels where
  centralModel := IntegralSingularChainComplex A.central
  fillingModel i := IntegralSingularChainComplex (A.filling i)
  collarModel i := IntegralSingularChainComplex (A.collarSource i)
  collarToCentral i := integralSingularChainMap (A.toCentral i).hom
  collarToFilling i := integralSingularChainMap (A.toFilling i).hom
  centralRealization := HomotopyEquiv.refl _
  fillingRealization _ := HomotopyEquiv.refl _
  collarRealization _ := HomotopyEquiv.refl _
  collarToCentral_naturality _ := by simp
  collarToFilling_naturality _ := by simp

end SevenSpaceChainModels

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

namespace Geometry.PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The exact seven-space chain-model interface specialized to the analytic star in the paper. -/
public abbrev SectionSevenSevenSpaceChainModels :=
  P.openEmbeddingStarData.SevenSpaceChainModels

end Geometry.PaperAnalyticData

end SphereSixComplex
