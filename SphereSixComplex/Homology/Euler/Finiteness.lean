module

public import SphereSixComplex.Homology.Euler.Assembly

/-!
# Homological finiteness of the glued threefold

The collars are mapping tori of four-tori, so their sixth homology vanishes. Mayer–Vietoris
therefore preserves the degree-six bound while adjoining each filling to the central piece.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

theorem FourTorusCircleMappingTorusModel.subsingleton_homology_six
    {X : Type} [TopologicalSpace X] (M : FourTorusCircleMappingTorusModel X) :
    Subsingleton (IntegralSingularHomology 6 X) := by
  let _ := M.fiberTopology
  have h := subsingleton_homology_succ_finiteBouquetMappingTorus_of_wang
    (fun _ : Unit ↦ M.clutching) 5
    (M.fiberHomology.subsingleton_homology_of_four_lt 6 (by omega))
    (M.fiberHomology.subsingleton_homology_of_four_lt 5 (by omega))
  exact (integralSingularHomologyEquivOfHomotopyEquiv 6 M.totalHomotopyEquiv).injective.subsingleton

theorem IntegralMayerVietoris.integralHomologyFiniteSix_union
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X))
    (hSix : Subsingleton (IntegralSingularHomology 6 (U ∩ V : Set X))) :
    IntegralHomologyFiniteSix (U ∪ V : Set X) := by
  have hSeven : Subsingleton (IntegralSingularHomology 7 (U ∪ V : Set X)) := by
    have := hUFinite.subsingleton_homology_of_six_lt 7 (by omega)
    have := hVFinite.subsingleton_homology_of_six_lt 7 (by omega)
    obtain ⟨boundary, he⟩ := exact_sequence_of_isOpen U V hU hV
    have hz (z : IntegralSingularHomology 7 (U ∪ V : Set X)) : z = 0 := by
      obtain ⟨w, hw⟩ := ((he 6).1 z).mp (hSix.elim _ _)
      rw [← hw, Subsingleton.elim w 0, map_zero]
    exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact (integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing U V hU hV
    hUFinite hVFinite hInterFinite hSeven).1

namespace OpenEmbeddingStarData

theorem integralHomologyFiniteSix_gluedSpace (A : OpenEmbeddingStarData)
    (hCentral : IntegralHomologyFiniteSix A.central)
    (hFilling : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollar : ∀ i, IntegralHomologyFiniteSix (A.collarSource i))
    (hCollarSix : ∀ i, Subsingleton (IntegralSingularHomology 6 (A.collarSource i))) :
    IntegralHomologyFiniteSix (GluedSpace A.toFourPieceStarGluingData.glueData) := by
  let C := A.sectionSevenEulerCover
  have hStage (i : Fin 4) : IntegralHomologyFiniteSix (C.stage i) := by
    induction i using Fin.induction with
    | zero => exact hCentral.homeomorph A.centralToSectionSevenEulerStageZeroHomeomorph
    | succ i ih =>
      let e := A.collarToMayerVietorisOverlapHomeomorph i
      have hOverlapSix : Subsingleton (IntegralSingularHomology 6
          (C.stage i.castSucc ∩ C.piece i.succ : Set
            (GluedSpace A.toFourPieceStarGluingData.glueData))) := by
        have := hCollarSix i
        exact (integralSingularHomologyEquiv 6 e).symm.injective.subsingleton
      exact (IntegralMayerVietoris.integralHomologyFiniteSix_union _ _
        (C.isOpen_stage i.castSucc) (C.isOpen_piece i.succ) ih
        ((hFilling i).homeomorph (A.fillingToSectionSevenEulerPieceHomeomorph i))
        ((hCollar i).homeomorph e) hOverlapSix).homeomorph
          (A.sectionSevenEulerStageNextHomeomorph i)
  exact (hStage 3).homeomorph A.sectionSevenEulerStageLastHomeomorph

end OpenEmbeddingStarData

theorem Geometry.AnalyticData.integralHomologyFiniteSix_starGlued (A : Geometry.AnalyticData) :
    IntegralHomologyFiniteSix
      (GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  obtain ⟨hCentral, hFilling, hCollar⟩ := A.localEulerModels.localIntegralHomologyFiniteSix
  exact A.openEmbeddingStarData.integralHomologyFiniteSix_gluedSpace hCentral hFilling hCollar
    (fun i ↦ (A.localEulerModels.collarModel i).subsingleton_homology_six)

end SphereSixComplex
