module

public import SphereSixComplex.Topology.SectionSevenSixManifoldCompletion

/-!
# Euler characteristic of the Section 7 four-piece star

This file reduces the Euler characteristic of the glued star to finite-rank calculations on the
central piece, the three fillings, and the three collar sources.  The numerical value `2` is not
part of the general Mayer--Vietoris package and is not stored in any structure.

Mathlib does not currently provide Euler additivity for singular homology.  The general open-cover
theorem is therefore isolated below with its exact homological-finiteness hypotheses.  Everything
after that theorem is a source-faithful application to the actual four-piece star.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Finiteness and dimension support sufficient for the six-dimensional integral-homology Euler
characteristic.  This records no ranks and no value of the Euler characteristic. -/
public structure IntegralHomologyFiniteSix
    (X : Type) [TopologicalSpace X] : Prop where
  /-- Every integral homology group is finitely generated. -/
  finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k X)
  /-- Homology vanishes above degree six. -/
  homologyAboveDimension : ∀ k, 6 < k → Subsingleton (IntegralSingularHomology k X)

namespace IntegralHomologyFiniteSix

/-- Homological finiteness and the dimension bound transport through a homeomorphism. -/
public theorem homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSix X) (e : X ≃ₜ Y) : IntegralHomologyFiniteSix Y where
  finiteHomology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finiteHomology k
    exact Module.Finite.equiv (integralSingularHomologyEquiv k e).toIntLinearEquiv
  homologyAboveDimension k hk := by
    let h := hX.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

/-- The six-dimensional integral-homology Euler characteristic is invariant under homeomorphism. -/
public theorem integralHomologyEulerCharacteristicSix_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    integralHomologyEulerCharacteristicSix X =
      integralHomologyEulerCharacteristicSix Y := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(integralSingularHomologyEquiv 0 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 1 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 2 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 3 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 4 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 5 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 6 e).toIntLinearEquiv.finrank_eq]

/-- Euler additivity for an open binary cover, together with the finite-generation consequence of
the Mayer--Vietoris long exact sequence.  This is a standard general singular-homology theorem;
the local finiteness hypotheses ensure that all displayed ranks are genuine finite ranks. -/
public axiom establishedIntegralMayerVietorisEulerAdditivitySix
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X)) :
    IntegralHomologyFiniteSix (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSix (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSix U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X)

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

public abbrev SectionSevenEulerCover :=
  sectionSevenStarOpenCover A.toFourPieceStarGluingData

/-- The central source is homeomorphic to the first actual open piece. -/
public noncomputable def centralToSectionSevenEulerPieceHomeomorph :
    A.central ≃ₜ (A.SectionSevenEulerCover).piece 0 :=
  (A.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding none)
    |>.isEmbedding.toHomeomorph

/-- Every filling source is homeomorphic to its actual open image. -/
public noncomputable def fillingToSectionSevenEulerPieceHomeomorph (i : Fin 3) :
    A.filling i ≃ₜ (A.SectionSevenEulerCover).piece i.succ :=
  (A.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding (some i))
    |>.isEmbedding.toHomeomorph

public theorem sectionSevenEulerStage_zero :
    (A.SectionSevenEulerCover).stage 0 = (A.SectionSevenEulerCover).piece 0 := by
  ext x
  simp [FourPieceOpenCover.stage]

/-- The central source is homeomorphic to the initial Mayer--Vietoris stage. -/
public noncomputable def centralToSectionSevenEulerStageZeroHomeomorph :
    A.central ≃ₜ (A.SectionSevenEulerCover).stage 0 :=
  A.centralToSectionSevenEulerPieceHomeomorph.trans
    (Homeomorph.setCongr A.sectionSevenEulerStage_zero.symm)

/-- The union occurring at one binary Mayer--Vietoris step is the next partial stage. -/
public noncomputable def sectionSevenEulerStageNextHomeomorph (r : Fin 3) :
    ((A.SectionSevenEulerCover).stage r.castSucc ∪
      (A.SectionSevenEulerCover).piece r.succ : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) ≃ₜ
      (A.SectionSevenEulerCover).stage r.succ :=
  Homeomorph.setCongr ((A.SectionSevenEulerCover).stage_union_next r)

/-- The last partial stage is homeomorphic to the whole glued star. -/
public noncomputable def sectionSevenEulerStageLastHomeomorph :
    (A.SectionSevenEulerCover).stage (3 : Fin 4) ≃ₜ
      GluedSpace A.toFourPieceStarGluingData.glueData :=
  topologicalSubsetHomeomorphOfEqUniv _ _ (A.SectionSevenEulerCover).stage_last

/-- The explicit local finite-rank expression for the Euler characteristic of the star. -/
public noncomputable def sectionSevenLocalEulerExpression : ℤ :=
  integralHomologyEulerCharacteristicSix A.central +
  integralHomologyEulerCharacteristicSix (A.filling 0) +
  integralHomologyEulerCharacteristicSix (A.filling 1) +
  integralHomologyEulerCharacteristicSix (A.filling 2) -
  integralHomologyEulerCharacteristicSix (A.collarSource 0) -
  integralHomologyEulerCharacteristicSix (A.collarSource 1) -
  integralHomologyEulerCharacteristicSix (A.collarSource 2)

/-- Mayer--Vietoris additivity reduces the Euler characteristic of the actual glued star to the
seven local source spaces.  No numerical local rank is assumed by this theorem. -/
public theorem integralHomologyEulerCharacteristicSix_eq_localExpression
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i)) :
    integralHomologyEulerCharacteristicSix
        (GluedSpace A.toFourPieceStarGluingData.glueData) =
      A.sectionSevenLocalEulerExpression := by
  let C := A.SectionSevenEulerCover
  let eCentralStage : A.central ≃ₜ C.stage 0 := by
    simpa only [C] using A.centralToSectionSevenEulerStageZeroHomeomorph
  let ePiece (i : Fin 3) : A.filling i ≃ₜ C.piece i.succ := by
    simpa only [C] using A.fillingToSectionSevenEulerPieceHomeomorph i
  let eOverlap (i : Fin 3) : A.collarSource i ≃ₜ
      (C.stage i.castSucc ∩ C.piece i.succ : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa only [C] using A.collarToMayerVietorisOverlapHomeomorph i
  let eNext (i : Fin 3) :
      (C.stage i.castSucc ∪ C.piece i.succ : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) ≃ₜ C.stage i.succ := by
    simpa only [C] using A.sectionSevenEulerStageNextHomeomorph i
  let eLast : C.stage (3 : Fin 4) ≃ₜ
      GluedSpace A.toFourPieceStarGluingData.glueData := by
    simpa only [C] using A.sectionSevenEulerStageLastHomeomorph
  have hPieceZero : IntegralHomologyFiniteSix (C.piece 0) :=
    hCentralFinite.homeomorph A.centralToSectionSevenEulerPieceHomeomorph
  have hPiece : ∀ (i : Fin 3), IntegralHomologyFiniteSix (C.piece i.succ) := fun i ↦
    (hFillingFinite i).homeomorph (ePiece i)
  have hOverlap : ∀ (i : Fin 3), IntegralHomologyFiniteSix
      (C.stage i.castSucc ∩ C.piece i.succ : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) := fun i ↦
    (hCollarFinite i).homeomorph (eOverlap i)
  have hStageZero : IntegralHomologyFiniteSix (C.stage (0 : Fin 4)) :=
    hCentralFinite.homeomorph eCentralStage
  obtain ⟨hUnionZero, hAddZero⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySix
      (C.stage (0 : Fin 4)) (C.piece 1)
      (C.isOpen_stage 0) (C.isOpen_piece 1) hStageZero (hPiece 0) (hOverlap 0)
  have hStageOne : IntegralHomologyFiniteSix (C.stage (1 : Fin 4)) :=
    hUnionZero.homeomorph (eNext 0)
  have hAddZero' :
      integralHomologyEulerCharacteristicSix (C.stage (1 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (C.stage (0 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 1) -
        integralHomologyEulerCharacteristicSix (C.stage (0 : Fin 4) ∩ C.piece 1 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSix_homeomorph (eNext 0)).symm.trans hAddZero
  obtain ⟨hUnionOne, hAddOne⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySix
      (C.stage (1 : Fin 4)) (C.piece 2)
      (C.isOpen_stage 1) (C.isOpen_piece 2) hStageOne (hPiece 1) (hOverlap 1)
  have hStageTwo : IntegralHomologyFiniteSix (C.stage (2 : Fin 4)) :=
    hUnionOne.homeomorph (eNext 1)
  have hAddOne' :
      integralHomologyEulerCharacteristicSix (C.stage (2 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (C.stage (1 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 2) -
        integralHomologyEulerCharacteristicSix (C.stage (1 : Fin 4) ∩ C.piece 2 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSix_homeomorph (eNext 1)).symm.trans hAddOne
  obtain ⟨-, hAddTwo⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySix
      (C.stage (2 : Fin 4)) (C.piece 3)
      (C.isOpen_stage 2) (C.isOpen_piece 3) hStageTwo (hPiece 2) (hOverlap 2)
  have hAddTwo' :
      integralHomologyEulerCharacteristicSix (C.stage (3 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (C.stage (2 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 3) -
        integralHomologyEulerCharacteristicSix (C.stage (2 : Fin 4) ∩ C.piece 3 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSix_homeomorph (eNext 2)).symm.trans hAddTwo
  have hCentralEuler : integralHomologyEulerCharacteristicSix (C.stage (0 : Fin 4)) =
      integralHomologyEulerCharacteristicSix A.central := by
    exact (integralHomologyEulerCharacteristicSix_homeomorph eCentralStage).symm
  have hPieceEuler : ∀ (i : Fin 3),
      integralHomologyEulerCharacteristicSix (C.piece i.succ) =
        integralHomologyEulerCharacteristicSix (A.filling i) := fun i ↦
    (integralHomologyEulerCharacteristicSix_homeomorph (ePiece i)).symm
  have hOverlapEuler : ∀ (i : Fin 3),
      integralHomologyEulerCharacteristicSix
          (C.stage i.castSucc ∩ C.piece i.succ : Set
            (GluedSpace A.toFourPieceStarGluingData.glueData)) =
        integralHomologyEulerCharacteristicSix (A.collarSource i) := fun i ↦
    (integralHomologyEulerCharacteristicSix_homeomorph (eOverlap i)).symm
  rw [← integralHomologyEulerCharacteristicSix_homeomorph eLast]
  rw [hAddTwo', hAddOne', hAddZero']
  rw [hCentralEuler]
  have hPieceEuler0 : integralHomologyEulerCharacteristicSix (C.piece 1) =
      integralHomologyEulerCharacteristicSix (A.filling 0) := by
    simpa using hPieceEuler 0
  have hPieceEuler1 : integralHomologyEulerCharacteristicSix (C.piece 2) =
      integralHomologyEulerCharacteristicSix (A.filling 1) := by
    simpa using hPieceEuler 1
  have hPieceEuler2 : integralHomologyEulerCharacteristicSix (C.piece 3) =
      integralHomologyEulerCharacteristicSix (A.filling 2) := by
    simpa using hPieceEuler 2
  have hOverlapEuler0 :
      integralHomologyEulerCharacteristicSix (C.stage 0 ∩ C.piece 1 : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) =
      integralHomologyEulerCharacteristicSix (A.collarSource 0) := by
    simpa using hOverlapEuler 0
  have hOverlapEuler1 :
      integralHomologyEulerCharacteristicSix (C.stage 1 ∩ C.piece 2 : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) =
      integralHomologyEulerCharacteristicSix (A.collarSource 1) := by
    simpa using hOverlapEuler 1
  have hOverlapEuler2 :
      integralHomologyEulerCharacteristicSix (C.stage 2 ∩ C.piece 3 : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) =
      integralHomologyEulerCharacteristicSix (A.collarSource 2) := by
    simpa using hOverlapEuler 2
  rw [hPieceEuler0, hPieceEuler1, hPieceEuler2,
    hOverlapEuler0, hOverlapEuler1, hOverlapEuler2]
  unfold sectionSevenLocalEulerExpression
  ring

/-- An explicit local finite-rank calculation of value `2` supplies the separate Euler hypothesis
needed by the closed-six-manifold completion theorem. -/
public theorem integralHomologyEulerCharacteristicSix_eq_two_of_localCalculation
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i))
    (hLocal : A.sectionSevenLocalEulerExpression = 2) :
    integralHomologyEulerCharacteristicSix
        (GluedSpace A.toFourPieceStarGluingData.glueData) = 2 := by
  rw [A.integralHomologyEulerCharacteristicSix_eq_localExpression
    hCentralFinite hFillingFinite hCollarFinite, hLocal]

namespace SectionSevenMayerVietorisHomologyAssembly

/-- The local Euler calculation discharges the last numerical hypothesis in the closed complex
threefold completion theorem. -/
public theorem hasIntegralHomologyOfSixSphere_of_localEulerCalculation
    (H : A.SectionSevenMayerVietorisHomologyAssembly)
    [ChartedSpace ComplexModel (A.SectionSevenMayerVietorisSpace)]
    [T2Space (A.SectionSevenMayerVietorisSpace)]
    [SecondCountableTopology (A.SectionSevenMayerVietorisSpace)]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.SectionSevenMayerVietorisSpace))
    (hCompact : CompactSpace (A.SectionSevenMayerVietorisSpace))
    (hConnected : ConnectedSpace (A.SectionSevenMayerVietorisSpace))
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i))
    (hLocal : A.sectionSevenLocalEulerExpression = 2) :
    HasIntegralHomologyOfSixSphere (A.SectionSevenMayerVietorisSpace) :=
  H.hasIntegralHomologyOfSixSphere_of_closedComplexThreefold
    hManifold hCompact hConnected
      (A.integralHomologyEulerCharacteristicSix_eq_two_of_localCalculation
        hCentralFinite hFillingFinite hCollarFinite hLocal)

end SectionSevenMayerVietorisHomologyAssembly

end OpenEmbeddingStarData

end SphereSixComplex
