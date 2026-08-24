module

public import SphereSixComplex.Topology.PaperSectionSevenMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Chain-level Mayer--Vietoris assembly for Section 7

The homotopy pushout of `K ⟶ A` and `K ⟶ B` is the homotopy cofiber of the signed map
`K ⟶ A ⊞ B`.  This file applies that fixed construction three times to the seven-space
diagram of the four-piece star.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

namespace ChainHomotopyPushout

variable {K A B : ChainComplex AddCommGrpCat ℕ}

/-- The signed attaching map whose homotopy cofiber is the homotopy pushout. -/
public noncomputable def attachingMap (f : K ⟶ A) (g : K ⟶ B) : K ⟶ A ⊞ B :=
  biprod.lift f (-g)

/-- The chain-level homotopy pushout of `K ⟶ A` and `K ⟶ B`. -/
public noncomputable def obj (f : K ⟶ A) (g : K ⟶ B) :
    ChainComplex AddCommGrpCat ℕ :=
  HomologicalComplex.homotopyCofiber (attachingMap f g)

/-- The canonical map from the left-hand chain complex to the homotopy pushout. -/
public noncomputable def inLeft (f : K ⟶ A) (g : K ⟶ B) : A ⟶ obj f g :=
  biprod.inl ≫ HomologicalComplex.homotopyCofiber.inr (attachingMap f g)

/-- The canonical map from the right-hand chain complex to the homotopy pushout. -/
public noncomputable def inRight (f : K ⟶ A) (g : K ⟶ B) : B ⟶ obj f g :=
  biprod.inr ≫ HomologicalComplex.homotopyCofiber.inr (attachingMap f g)

/-- Every degree of a chain complex indexed by `ℕ` has a preceding source degree. -/
public theorem chainComplex_hasPredecessor :
    ∀ j : ℕ, ∃ i : ℕ, (ComplexShape.down ℕ).Rel i j :=
  fun j ↦ ⟨j + 1, by simp⟩

/-- The signed difference of the two attachment composites is the map into the mapping cone. -/
public theorem attachmentDifference_eq (f : K ⟶ A) (g : K ⟶ B) :
    f ≫ inLeft f g - g ≫ inRight f g =
      attachingMap f g ≫ HomologicalComplex.homotopyCofiber.inr (attachingMap f g) := by
  let q := HomologicalComplex.homotopyCofiber.inr (attachingMap f g)
  change f ≫ biprod.inl ≫ q - g ≫ biprod.inr ≫ q = attachingMap f g ≫ q
  calc
    _ = (f ≫ biprod.inl + (-g) ≫ biprod.inr) ≫ q := by
      simp only [sub_eq_add_neg, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]
    _ = biprod.lift f (-g) ≫ q := by rw [biprod.lift_eq]
    _ = attachingMap f g ≫ q := rfl

/-- The two attachment composites commute up to the canonical mapping-cone homotopy. -/
public noncomputable def attachmentHomotopy (f : K ⟶ A) (g : K ⟶ B) :
    Homotopy (f ≫ inLeft f g) (g ≫ inRight f g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (attachmentDifference_eq f g)).trans
      (HomologicalComplex.homotopyCofiber.inrCompHomotopy
        (attachingMap f g) chainComplex_hasPredecessor))

end ChainHomotopyPushout

namespace OpenEmbeddingStarData.SevenSpaceChainModels

variable {A : OpenEmbeddingStarData} (M : A.SevenSpaceChainModels)

/-- The first fixed Mayer--Vietoris stage, attaching filling zero to the central model. -/
public noncomputable def stageOne : ChainComplex AddCommGrpCat ℕ :=
  ChainHomotopyPushout.obj (M.collarToCentral 0) (M.collarToFilling 0)

/-- The canonical central-model map into the first stage. -/
public noncomputable def centralToStageOne : M.centralModel ⟶ M.stageOne :=
  ChainHomotopyPushout.inLeft (M.collarToCentral 0) (M.collarToFilling 0)

/-- The canonical filling-zero map into the first stage. -/
public noncomputable def fillingZeroToStageOne : M.fillingModel 0 ⟶ M.stageOne :=
  ChainHomotopyPushout.inRight (M.collarToCentral 0) (M.collarToFilling 0)

/-- The fixed attaching map from collar one to the first stage. -/
public noncomputable def collarOneToStageOne : M.collarModel 1 ⟶ M.stageOne :=
  M.collarToCentral 1 ≫ M.centralToStageOne

/-- The second fixed Mayer--Vietoris stage. -/
public noncomputable def stageTwo : ChainComplex AddCommGrpCat ℕ :=
  ChainHomotopyPushout.obj M.collarOneToStageOne (M.collarToFilling 1)

/-- The canonical first-stage map into the second stage. -/
public noncomputable def stageOneToStageTwo : M.stageOne ⟶ M.stageTwo :=
  ChainHomotopyPushout.inLeft M.collarOneToStageOne (M.collarToFilling 1)

/-- The canonical central-model map into the second stage. -/
public noncomputable def centralToStageTwo : M.centralModel ⟶ M.stageTwo :=
  M.centralToStageOne ≫ M.stageOneToStageTwo

/-- The canonical filling-one map into the second stage. -/
public noncomputable def fillingOneToStageTwo : M.fillingModel 1 ⟶ M.stageTwo :=
  ChainHomotopyPushout.inRight M.collarOneToStageOne (M.collarToFilling 1)

/-- The fixed attaching map from collar two to the second stage. -/
public noncomputable def collarTwoToStageTwo : M.collarModel 2 ⟶ M.stageTwo :=
  M.collarToCentral 2 ≫ M.centralToStageTwo

/-- The third and final fixed Mayer--Vietoris stage. -/
public noncomputable def stageThree : ChainComplex AddCommGrpCat ℕ :=
  ChainHomotopyPushout.obj M.collarTwoToStageTwo (M.collarToFilling 2)

/-- The canonical second-stage map into the final stage. -/
public noncomputable def stageTwoToStageThree : M.stageTwo ⟶ M.stageThree :=
  ChainHomotopyPushout.inLeft M.collarTwoToStageTwo (M.collarToFilling 2)

/-- The canonical central-model map into the final stage. -/
public noncomputable def centralToStageThree : M.centralModel ⟶ M.stageThree :=
  M.centralToStageTwo ≫ M.stageTwoToStageThree

/-- The canonical filling-two map into the final stage. -/
public noncomputable def fillingTwoToStageThree : M.fillingModel 2 ⟶ M.stageThree :=
  ChainHomotopyPushout.inRight M.collarTwoToStageTwo (M.collarToFilling 2)

/-- The four fixed chain complexes: the central model and the three successive pushouts. -/
public noncomputable def canonicalStage : Fin 4 → ChainComplex AddCommGrpCat ℕ :=
  ![M.centralModel, M.stageOne, M.stageTwo, M.stageThree]

/-- The fixed algebraic output of the three successive Mayer--Vietoris attachments. -/
public noncomputable abbrev finalStage : ChainComplex AddCommGrpCat ℕ :=
  M.stageThree

/-- The first attachment square commutes up to the canonical mapping-cone homotopy. -/
public noncomputable def stageOneAttachmentHomotopy :
    Homotopy (M.collarToCentral 0 ≫ M.centralToStageOne)
      (M.collarToFilling 0 ≫ M.fillingZeroToStageOne) :=
  ChainHomotopyPushout.attachmentHomotopy (M.collarToCentral 0) (M.collarToFilling 0)

/-- The second attachment square commutes up to the canonical mapping-cone homotopy. -/
public noncomputable def stageTwoAttachmentHomotopy :
    Homotopy (M.collarOneToStageOne ≫ M.stageOneToStageTwo)
      (M.collarToFilling 1 ≫ M.fillingOneToStageTwo) :=
  ChainHomotopyPushout.attachmentHomotopy M.collarOneToStageOne (M.collarToFilling 1)

/-- The third attachment square commutes up to the canonical mapping-cone homotopy. -/
public noncomputable def stageThreeAttachmentHomotopy :
    Homotopy (M.collarTwoToStageTwo ≫ M.stageTwoToStageThree)
      (M.collarToFilling 2 ≫ M.fillingTwoToStageThree) :=
  ChainHomotopyPushout.attachmentHomotopy M.collarTwoToStageTwo (M.collarToFilling 2)

/-- Any alternate stage presentation must identify every stage with the canonical assembly. -/
public structure FourStagePresentation where
  /-- The alternate four-stage family. -/
  stage : Fin 4 → ChainComplex AddCommGrpCat ℕ
  /-- A stagewise isomorphism to the fixed mapping-cone construction. -/
  stageIso : ∀ r, stage r ≅ M.canonicalStage r

namespace FourStagePresentation

/-- The final object of an alternate presentation is isomorphic to the fixed final stage. -/
public noncomputable def finalStageIso (D : M.FourStagePresentation) :
    D.stage 3 ≅ M.finalStage :=
  D.stageIso 3

end FourStagePresentation

end OpenEmbeddingStarData.SevenSpaceChainModels

end SphereSixComplex
