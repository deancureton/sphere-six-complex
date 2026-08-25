module

public import SphereSixComplex.Topology.IntegralMayerVietorisEuler
public import SphereSixComplex.Topology.MayerVietorisDegreeZeroBridge
public import SphereSixComplex.Topology.SectionSevenSixManifoldCompletion

/-!
# Euler characteristic of the Section 7 four-piece star

This file reduces the Euler characteristic of the glued star to finite-rank calculations on the
central piece, the three fillings, and the three collar sources.  The numerical value `2` is not
part of the general Mayer--Vietoris package and is not stored in any structure.

The general degree-seven Mayer--Vietoris formula below is proved from the project's established
long exact sequence.  The Section 7 calculation can either supply top-degree vanishing at every
stage or retain degree-seven homology until the final six-manifold truncation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Euler additivity for an open binary cover, together with the finite-generation consequence of
the Mayer--Vietoris long exact sequence.  This is a standard general singular-homology theorem;
the local finiteness hypotheses ensure that all displayed ranks are genuine finite ranks.

The union acquires one extra degree.  Writing the Mayer--Vietoris sequence with the vanishing
`H₇(U) = H₇(V) = H₇(U ∩ V) = 0` inserted, its tail

`0 → H₇(U ∪ V) → H₆(U ∩ V) → H₆(U) ⊕ H₆(V) → H₆(U ∪ V) → ⋯ → H₀(U ∪ V) → 0`

is a finite exact sequence of finitely generated groups, so its alternating rank sum vanishes.
That identity is exactly the formula below, including the degree-seven correction term; the union
itself can genuinely carry homology in degree seven, and only degrees above seven vanish.

The correction term is not optional.  Covering `S⁷` by two contractible open sets whose
intersection is homotopy equivalent to `S⁶` gives pieces satisfying every hypothesis, while
`H₇(S⁷) = ℤ`: both the truncated dimension bound and the uncorrected identity
`1 = 1 + 1 - 2` fail for that cover.  See `integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing`
for the truncated form, which is available exactly when the union has no seventh homology. -/
public theorem establishedIntegralMayerVietorisEulerAdditivitySeven
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X)) :
    (∀ k, Module.Finite ℤ (IntegralSingularHomology k (U ∪ V : Set X))) ∧
      (∀ k, 7 < k → Subsingleton (IntegralSingularHomology k (U ∪ V : Set X))) ∧
      integralHomologyEulerCharacteristicSix (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSix U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) +
        (Module.finrank ℤ (IntegralSingularHomology 7 (U ∪ V : Set X)) : ℤ) := by
  obtain ⟨hUnionFinite, hEuler⟩ :=
    integralMayerVietorisEulerAdditivitySeven_of_finiteSix U V
      hUFinite hVFinite hInterFinite
      (establishedIntegralMayerVietorisExactSequence U V hUOpen hVOpen)
      (IntegralMayerVietoris.sumMap_zero_surjective U V hUOpen hVOpen)
  refine ⟨hUnionFinite.finiteHomology, hUnionFinite.homologyAboveDimension, ?_⟩
  unfold integralHomologyEulerCharacteristicSeven at hEuler
  omega

/-- The degree-six truncated form of Mayer--Vietoris Euler additivity, available exactly when the
union has no seventh integral homology.  Every use in the Section 7 calculation goes through this
theorem, so the top-degree hypothesis stays visible. -/
public theorem integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X))
    (hTop : Subsingleton (IntegralSingularHomology 7 (U ∪ V : Set X))) :
    IntegralHomologyFiniteSix (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSix (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSix U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) := by
  obtain ⟨hFinite, hAbove, hEuler⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySeven U V hUOpen hVOpen hUFinite hVFinite
      hInterFinite
  have hTopRank : Module.finrank ℤ (IntegralSingularHomology 7 (U ∪ V : Set X)) = 0 := by
    have := hTop
    exact Module.finrank_zero_of_subsingleton
  refine ⟨⟨hFinite, ?_⟩, ?_⟩
  · intro k hk
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hk7 | hk7
    · exact hk7 ▸ hTop
    · exact hAbove k hk7
  · rw [hEuler, hTopRank]
    simp

/-- A structure-valued form of the sound open-cover specialization. -/
public theorem establishedIntegralMayerVietorisEulerAdditivitySeven_structured
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X)) :
    IntegralHomologyFiniteSeven (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSeven (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSix U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) :=
  integralMayerVietorisEulerAdditivitySeven_of_finiteSix U V
    hUFinite hVFinite hInterFinite
    (establishedIntegralMayerVietorisExactSequence U V hUOpen hVOpen)
    (IntegralMayerVietoris.sumMap_zero_surjective U V hUOpen hVOpen)

/-- The asymmetric form used to adjoin successive six-dimensional pieces to a partial union that
may already carry degree-seven homology. -/
public theorem establishedIntegralMayerVietorisEulerAdditivitySeven_asymmetric
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUFinite : IntegralHomologyFiniteSeven U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X)) :
    IntegralHomologyFiniteSeven (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSeven (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSeven U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) :=
  integralMayerVietorisEulerAdditivitySeven U V hUFinite hVFinite hInterFinite
    (establishedIntegralMayerVietorisExactSequence U V hUOpen hVOpen)
    (IntegralMayerVietoris.sumMap_zero_surjective U V hUOpen hVOpen)

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

public abbrev SectionSevenEulerCover :=
  sectionSevenStarOpenCover A.toFourPieceStarGluingData

/-- The three intermediate Mayer--Vietoris unions of the star cover carry no seventh integral
homology.

This is the exact top-degree hypothesis that makes the degree-six truncated Euler additivity
formula applicable at each of the three gluing steps; without it the truncated formula is false
(an `S⁷` cover by two contractible opens is a counterexample).  For the actual analytic star each
union is an open subset of the completed six-manifold, where the standard dimension bound gives
the vanishing. -/
public def SectionSevenStageTopDegreeVanishing : Prop :=
  ∀ r : Fin 3, Subsingleton (IntegralSingularHomology 7
    ((A.SectionSevenEulerCover).stage r.castSucc ∪ (A.SectionSevenEulerCover).piece r.succ :
      Set (GluedSpace A.toFourPieceStarGluingData.glueData)))

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

/-- Degree-six derivation with explicit top-degree vanishing at every partial union.  The theorem
`integralHomologyEulerCharacteristicSeven_eq_localExpression` avoids those intermediate
hypotheses by retaining degree-seven homology until the completed space. -/
public theorem integralHomologyEulerCharacteristicSix_eq_localExpression
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i))
    (hTop : A.SectionSevenStageTopDegreeVanishing) :
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
    integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing
      (C.stage (0 : Fin 4)) (C.piece 1)
      (C.isOpen_stage 0) (C.isOpen_piece 1) hStageZero (hPiece 0) (hOverlap 0) (hTop 0)
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
    integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing
      (C.stage (1 : Fin 4)) (C.piece 2)
      (C.isOpen_stage 1) (C.isOpen_piece 2) hStageOne (hPiece 1) (hOverlap 1) (hTop 1)
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
    integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing
      (C.stage (2 : Fin 4)) (C.piece 3)
      (C.isOpen_stage 2) (C.isOpen_piece 3) hStageTwo (hPiece 2) (hOverlap 2) (hTop 2)
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

/-- The sound Mayer--Vietoris iteration retains possible degree-seven homology throughout the
three partial unions. -/
public theorem integralHomologyEulerCharacteristicSeven_eq_localExpression
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i)) :
    integralHomologyEulerCharacteristicSeven
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
  have hPiece : ∀ (i : Fin 3), IntegralHomologyFiniteSix (C.piece i.succ) := fun i ↦
    (hFillingFinite i).homeomorph (ePiece i)
  have hOverlap : ∀ (i : Fin 3), IntegralHomologyFiniteSix
      (C.stage i.castSucc ∩ C.piece i.succ : Set
        (GluedSpace A.toFourPieceStarGluingData.glueData)) := fun i ↦
    (hCollarFinite i).homeomorph (eOverlap i)
  have hStageZeroSix : IntegralHomologyFiniteSix (C.stage (0 : Fin 4)) :=
    hCentralFinite.homeomorph eCentralStage
  have hStageZero : IntegralHomologyFiniteSeven (C.stage (0 : Fin 4)) :=
    IntegralHomologyFiniteSeven.ofFiniteSix hStageZeroSix
  obtain ⟨hUnionZero, hAddZero⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySeven_asymmetric
      (C.stage (0 : Fin 4)) (C.piece 1)
      (C.isOpen_stage 0) (C.isOpen_piece 1) hStageZero (hPiece 0) (hOverlap 0)
  have hStageOne : IntegralHomologyFiniteSeven (C.stage (1 : Fin 4)) :=
    hUnionZero.homeomorph (eNext 0)
  have hAddZero' :
      integralHomologyEulerCharacteristicSeven (C.stage (1 : Fin 4)) =
        integralHomologyEulerCharacteristicSeven (C.stage (0 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 1) -
        integralHomologyEulerCharacteristicSix (C.stage (0 : Fin 4) ∩ C.piece 1 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSeven_homeomorph (eNext 0)).symm.trans hAddZero
  obtain ⟨hUnionOne, hAddOne⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySeven_asymmetric
      (C.stage (1 : Fin 4)) (C.piece 2)
      (C.isOpen_stage 1) (C.isOpen_piece 2) hStageOne (hPiece 1) (hOverlap 1)
  have hStageTwo : IntegralHomologyFiniteSeven (C.stage (2 : Fin 4)) :=
    hUnionOne.homeomorph (eNext 1)
  have hAddOne' :
      integralHomologyEulerCharacteristicSeven (C.stage (2 : Fin 4)) =
        integralHomologyEulerCharacteristicSeven (C.stage (1 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 2) -
        integralHomologyEulerCharacteristicSix (C.stage (1 : Fin 4) ∩ C.piece 2 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSeven_homeomorph (eNext 1)).symm.trans hAddOne
  obtain ⟨-, hAddTwo⟩ :=
    establishedIntegralMayerVietorisEulerAdditivitySeven_asymmetric
      (C.stage (2 : Fin 4)) (C.piece 3)
      (C.isOpen_stage 2) (C.isOpen_piece 3) hStageTwo (hPiece 2) (hOverlap 2)
  have hAddTwo' :
      integralHomologyEulerCharacteristicSeven (C.stage (3 : Fin 4)) =
        integralHomologyEulerCharacteristicSeven (C.stage (2 : Fin 4)) +
        integralHomologyEulerCharacteristicSix (C.piece 3) -
        integralHomologyEulerCharacteristicSix (C.stage (2 : Fin 4) ∩ C.piece 3 :
          Set (GluedSpace A.toFourPieceStarGluingData.glueData)) := by
    simpa using
      (integralHomologyEulerCharacteristicSeven_homeomorph (eNext 2)).symm.trans hAddTwo
  have hCentralEuler :
      integralHomologyEulerCharacteristicSeven (C.stage (0 : Fin 4)) =
        integralHomologyEulerCharacteristicSix A.central := by
    exact (integralHomologyEulerCharacteristicSeven_homeomorph eCentralStage).symm.trans
      (integralHomologyEulerCharacteristicSeven_eq_six_of_finiteSix hCentralFinite)
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
  rw [← integralHomologyEulerCharacteristicSeven_homeomorph eLast]
  rw [hAddTwo', hAddOne', hAddZero', hCentralEuler]
  have hPieceEuler0 :
      integralHomologyEulerCharacteristicSix (C.piece (1 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (A.filling (0 : Fin 3)) := by
    simpa using hPieceEuler (0 : Fin 3)
  have hPieceEuler1 :
      integralHomologyEulerCharacteristicSix (C.piece (2 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (A.filling (1 : Fin 3)) := by
    simpa using hPieceEuler (1 : Fin 3)
  have hPieceEuler2 :
      integralHomologyEulerCharacteristicSix (C.piece (3 : Fin 4)) =
        integralHomologyEulerCharacteristicSix (A.filling (2 : Fin 3)) := by
    simpa using hPieceEuler (2 : Fin 3)
  have hOverlapEuler0 :
      integralHomologyEulerCharacteristicSix
          (C.stage (0 : Fin 4) ∩ C.piece (1 : Fin 4) : Set
            (GluedSpace A.toFourPieceStarGluingData.glueData)) =
        integralHomologyEulerCharacteristicSix (A.collarSource (0 : Fin 3)) := by
    simpa using hOverlapEuler (0 : Fin 3)
  have hOverlapEuler1 :
      integralHomologyEulerCharacteristicSix
          (C.stage (1 : Fin 4) ∩ C.piece (2 : Fin 4) : Set
            (GluedSpace A.toFourPieceStarGluingData.glueData)) =
        integralHomologyEulerCharacteristicSix (A.collarSource (1 : Fin 3)) := by
    simpa using hOverlapEuler (1 : Fin 3)
  have hOverlapEuler2 :
      integralHomologyEulerCharacteristicSix
          (C.stage (2 : Fin 4) ∩ C.piece (3 : Fin 4) : Set
            (GluedSpace A.toFourPieceStarGluingData.glueData)) =
        integralHomologyEulerCharacteristicSix (A.collarSource (2 : Fin 3)) := by
    simpa using hOverlapEuler (2 : Fin 3)
  rw [hPieceEuler0, hPieceEuler1, hPieceEuler2,
    hOverlapEuler0, hOverlapEuler1, hOverlapEuler2]
  unfold sectionSevenLocalEulerExpression
  ring

/-- Six-manifold dimensionality removes the final degree-seven correction from the sound
Mayer--Vietoris iteration. -/
public theorem integralHomologyEulerCharacteristicSix_eq_localExpression_of_homologyTheory
    (T : ClosedOrientedSixManifoldHomologyTheory
      (GluedSpace A.toFourPieceStarGluingData.glueData))
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i)) :
    integralHomologyEulerCharacteristicSix
        (GluedSpace A.toFourPieceStarGluingData.glueData) =
      A.sectionSevenLocalEulerExpression := by
  have hSeven : Subsingleton (IntegralSingularHomology 7
      (GluedSpace A.toFourPieceStarGluingData.glueData)) :=
    T.homologyAboveDimension 7 (by omega)
  have hTruncation : integralHomologyEulerCharacteristicSeven
      (GluedSpace A.toFourPieceStarGluingData.glueData) =
        integralHomologyEulerCharacteristicSix
          (GluedSpace A.toFourPieceStarGluingData.glueData) := by
    let _ := hSeven
    unfold integralHomologyEulerCharacteristicSeven
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero]
  rw [← hTruncation]
  exact A.integralHomologyEulerCharacteristicSeven_eq_localExpression
    hCentralFinite hFillingFinite hCollarFinite

/-- Compatibility corollary through explicit top-degree vanishing at every partial union.  The
final endpoint below uses
`integralHomologyEulerCharacteristicSix_eq_localExpression_of_homologyTheory`. -/
public theorem integralHomologyEulerCharacteristicSix_eq_two_of_localCalculation
    (hCentralFinite : IntegralHomologyFiniteSix A.central)
    (hFillingFinite : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hCollarFinite : ∀ i, IntegralHomologyFiniteSix (A.collarSource i))
    (hTop : A.SectionSevenStageTopDegreeVanishing)
    (hLocal : A.sectionSevenLocalEulerExpression = 2) :
    integralHomologyEulerCharacteristicSix
        (GluedSpace A.toFourPieceStarGluingData.glueData) = 2 := by
  rw [A.integralHomologyEulerCharacteristicSix_eq_localExpression
    hCentralFinite hFillingFinite hCollarFinite hTop, hLocal]

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
    (_hTop : A.SectionSevenStageTopDegreeVanishing)
    (hLocal : A.sectionSevenLocalEulerExpression = 2) :
    HasIntegralHomologyOfSixSphere (A.SectionSevenMayerVietorisSpace) :=
  let T := establishedCompactComplexThreefoldHomologyTheory
    (A.SectionSevenMayerVietorisSpace) hManifold hCompact
  have hEuler : integralHomologyEulerCharacteristicSix
      (A.SectionSevenMayerVietorisSpace) = 2 := by
    rw [A.integralHomologyEulerCharacteristicSix_eq_localExpression_of_homologyTheory
      T hCentralFinite hFillingFinite hCollarFinite, hLocal]
  H.hasIntegralHomologyOfSixSphere_of_closedComplexThreefold
    hManifold hCompact hConnected hEuler

end SectionSevenMayerVietorisHomologyAssembly

end OpenEmbeddingStarData

end SphereSixComplex
