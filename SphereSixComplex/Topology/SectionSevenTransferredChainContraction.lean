module

public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification

/-!
# Algebraic contractions for the Section 7 matrix model

This file contracts the five middle degrees of `sectionSevenLerayChainModel (-1)` by explicit
integer matrices.  The resulting projection is the identity in degrees zero and six and zero in
degrees one through five.

Proposition 7.27 supplies only the differentials on a Leray spectral-sequence page.  It does not
identify the ordered Cech total complex with this matrix model.  Consequently, the second part of
this file is deliberately conditional: a transferred contraction is obtained only from an
explicit direct-sum decomposition of the relevant chain complex and an explicit contraction of
its complementary summand.  Producing such data for the star cover requires a separate
cellular/basis decomposition not contained in Proposition 7.27.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

namespace SphereSixComplex

/-- The degree-one-to-two component of the contraction. -/
public def sectionSevenLerayContractionOneTwo : (Fin 1 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-x 0, 0]
  map_zero' := by
    funext i
    fin_cases i
    all_goals rfl
  map_add' x y := by
    funext i
    fin_cases i
    all_goals dsimp
    all_goals abel

/-- The degree-two-to-three component of the contraction. -/
public def sectionSevenLerayContractionTwoThree : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-x 1, 0]
  map_zero' := by
    funext i
    fin_cases i
    all_goals rfl
  map_add' x y := by
    funext i
    fin_cases i
    all_goals dsimp
    all_goals abel

/-- The degree-three-to-four component of the contraction. -/
public def sectionSevenLerayContractionThreeFour : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  sectionSevenLerayContractionTwoThree

/-- The degree-four-to-five component of the contraction. -/
public def sectionSevenLerayContractionFourFive : (Fin 2 → ℤ) →+ (Fin 1 → ℤ) where
  toFun x := ![-x 1]
  map_zero' := by
    funext i
    fin_cases i
    rfl
  map_add' x y := by
    funext i
    fin_cases i
    dsimp
    abel

@[simp]
public theorem sectionSevenLerayContractionOneTwo_apply (x : Fin 1 → ℤ) :
    sectionSevenLerayContractionOneTwo x = ![-x 0, 0] := rfl

@[simp]
public theorem sectionSevenLerayContractionTwoThree_apply (x : Fin 2 → ℤ) :
    sectionSevenLerayContractionTwoThree x = ![-x 1, 0] := rfl

@[simp]
public theorem sectionSevenLerayContractionThreeFour_apply (x : Fin 2 → ℤ) :
    sectionSevenLerayContractionThreeFour x = ![-x 1, 0] := rfl

@[simp]
public theorem sectionSevenLerayContractionFourFive_apply (x : Fin 2 → ℤ) :
    sectionSevenLerayContractionFourFive x = ![-x 1] := rfl

private theorem contraction_identity_one :
    AddCommGrpCat.ofHom sectionSevenLerayContractionOneTwo ≫
        AddCommGrpCat.ofHom sectionSevenLerayBoundaryTwo =
      𝟙 (AddCommGrpCat.of (Fin 1 → ℤ)) := by
  change AddCommGrpCat.ofHom
      (sectionSevenLerayBoundaryTwo.comp sectionSevenLerayContractionOneTwo) =
    AddCommGrpCat.ofHom (AddMonoidHom.id _)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  simp [sectionSevenLerayBoundaryTwo, chosenLerayDifferential, twistObstruction]

private theorem contraction_identity_two :
    (AddCommGrpCat.ofHom sectionSevenLerayBoundaryTwo ≫
        AddCommGrpCat.ofHom sectionSevenLerayContractionOneTwo) +
      (AddCommGrpCat.ofHom sectionSevenLerayContractionTwoThree ≫
        AddCommGrpCat.ofHom sectionSevenLerayBoundaryThree) =
      𝟙 (AddCommGrpCat.of (Fin 2 → ℤ)) := by
  change AddCommGrpCat.ofHom
      (sectionSevenLerayContractionOneTwo.comp sectionSevenLerayBoundaryTwo +
        sectionSevenLerayBoundaryThree.comp sectionSevenLerayContractionTwoThree) =
    AddCommGrpCat.ofHom (AddMonoidHom.id _)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  · simp [sectionSevenLerayBoundaryTwo, sectionSevenLerayBoundaryThree,
      chosenLerayDifferential, twistObstruction]
  · simp [sectionSevenLerayBoundaryTwo, sectionSevenLerayBoundaryThree,
      chosenLerayDifferential, twistObstruction]

private theorem contraction_identity_three :
    (AddCommGrpCat.ofHom sectionSevenLerayBoundaryThree ≫
        AddCommGrpCat.ofHom sectionSevenLerayContractionTwoThree) +
      (AddCommGrpCat.ofHom sectionSevenLerayContractionThreeFour ≫
        AddCommGrpCat.ofHom sectionSevenLerayBoundaryFour) =
      𝟙 (AddCommGrpCat.of (Fin 2 → ℤ)) := by
  change AddCommGrpCat.ofHom
      (sectionSevenLerayContractionTwoThree.comp sectionSevenLerayBoundaryThree +
        sectionSevenLerayBoundaryFour.comp sectionSevenLerayContractionThreeFour) =
    AddCommGrpCat.ofHom (AddMonoidHom.id _)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  · simp [sectionSevenLerayContractionThreeFour, sectionSevenLerayBoundaryThree,
      sectionSevenLerayBoundaryFour, chosenLerayDifferential, twistObstruction]
  · simp [sectionSevenLerayContractionThreeFour, sectionSevenLerayBoundaryThree,
      sectionSevenLerayBoundaryFour, chosenLerayDifferential, twistObstruction]

private theorem contraction_identity_four :
    (AddCommGrpCat.ofHom sectionSevenLerayBoundaryFour ≫
        AddCommGrpCat.ofHom sectionSevenLerayContractionThreeFour) +
      (AddCommGrpCat.ofHom sectionSevenLerayContractionFourFive ≫
        AddCommGrpCat.ofHom (sectionSevenLerayBoundaryFive (-1))) =
      𝟙 (AddCommGrpCat.of (Fin 2 → ℤ)) := by
  change AddCommGrpCat.ofHom
      (sectionSevenLerayContractionThreeFour.comp sectionSevenLerayBoundaryFour +
        (sectionSevenLerayBoundaryFive (-1)).comp sectionSevenLerayContractionFourFive) =
    AddCommGrpCat.ofHom (AddMonoidHom.id _)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  · simp [sectionSevenLerayContractionThreeFour, sectionSevenLerayBoundaryFour,
      sectionSevenLerayBoundaryFive, chosenLerayDifferential, twistObstruction]
  · simp [sectionSevenLerayContractionThreeFour, sectionSevenLerayBoundaryFour,
      sectionSevenLerayBoundaryFive, chosenLerayDifferential, twistObstruction]

private theorem contraction_identity_five :
    AddCommGrpCat.ofHom (sectionSevenLerayBoundaryFive (-1)) ≫
        AddCommGrpCat.ofHom sectionSevenLerayContractionFourFive =
      𝟙 (AddCommGrpCat.of (Fin 1 → ℤ)) := by
  change AddCommGrpCat.ofHom
      (sectionSevenLerayContractionFourFive.comp (sectionSevenLerayBoundaryFive (-1))) =
    AddCommGrpCat.ofHom (AddMonoidHom.id _)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  simp [sectionSevenLerayBoundaryFive]

public abbrev sectionSevenUnitLerayModel := sectionSevenLerayChainModel (-1)

/-- The relation-indexed family of the four nonzero contraction components. -/
public def sectionSevenLerayContractionComponent
    (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    sectionSevenUnitLerayModel.X i ⟶ sectionSevenUnitLerayModel.X j := by
  rw [ComplexShape.down_Rel] at h
  subst j
  rcases i with (_ | _ | _ | _ | _ | i)
  · exact 0
  · exact AddCommGrpCat.ofHom sectionSevenLerayContractionOneTwo
  · exact AddCommGrpCat.ofHom sectionSevenLerayContractionTwoThree
  · exact AddCommGrpCat.ofHom sectionSevenLerayContractionThreeFour
  · exact AddCommGrpCat.ofHom sectionSevenLerayContractionFourFive
  · exact 0

@[simp]
public theorem sectionSevenLerayContractionComponent_zero_one (h) :
    sectionSevenLerayContractionComponent 0 1 h = 0 := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_one_two (h) :
    sectionSevenLerayContractionComponent 1 2 h =
      AddCommGrpCat.ofHom sectionSevenLerayContractionOneTwo := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_two_three (h) :
    sectionSevenLerayContractionComponent 2 3 h =
      AddCommGrpCat.ofHom sectionSevenLerayContractionTwoThree := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_three_four (h) :
    sectionSevenLerayContractionComponent 3 4 h =
      AddCommGrpCat.ofHom sectionSevenLerayContractionThreeFour := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_four_five (h) :
    sectionSevenLerayContractionComponent 4 5 h =
      AddCommGrpCat.ofHom sectionSevenLerayContractionFourFive := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_five_six (h) :
    sectionSevenLerayContractionComponent 5 6 h = 0 := by rfl

@[simp]
public theorem sectionSevenLerayContractionComponent_six_seven (h) :
    sectionSevenLerayContractionComponent 6 7 h = 0 := by rfl

private theorem sectionSevenUnitLerayModel_d (n : ℕ) :
    sectionSevenUnitLerayModel.d (n + 1) n =
      AddCommGrpCat.ofHom (sectionSevenLerayBoundary (-1) n) := by
  exact ChainComplex.of_d
    (fun k ↦ AddCommGrpCat.of (SectionSevenLerayGroup k))
    (fun k ↦ AddCommGrpCat.ofHom (sectionSevenLerayBoundary (-1) k)) n

/-- The null-homotopic middle-degree identity generated by the explicit contraction. -/
public def sectionSevenLerayMiddleIdentity :
    sectionSevenUnitLerayModel ⟶ sectionSevenUnitLerayModel :=
  Homotopy.nullHomotopicMap' sectionSevenLerayContractionComponent

private theorem sectionSevenLerayMiddleIdentity_f_one :
    sectionSevenLerayMiddleIdentity.f 1 =
      𝟙 (sectionSevenUnitLerayModel.X 1) := by
  rw [sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 2 1 by rfl)
      (show (ComplexShape.down ℕ).Rel 1 0 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  change (0 : AddCommGrpCat.of (Fin 1 → ℤ) ⟶ AddCommGrpCat.of (Fin 1 → ℤ)) +
      AddCommGrpCat.ofHom sectionSevenLerayContractionOneTwo ≫
        AddCommGrpCat.ofHom sectionSevenLerayBoundaryTwo = 𝟙 _
  simpa using contraction_identity_one

private theorem sectionSevenLerayMiddleIdentity_f_two :
    sectionSevenLerayMiddleIdentity.f 2 =
      𝟙 (sectionSevenUnitLerayModel.X 2) := by
  rw [sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 3 2 by rfl)
      (show (ComplexShape.down ℕ).Rel 2 1 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  exact contraction_identity_two

private theorem sectionSevenLerayMiddleIdentity_f_three :
    sectionSevenLerayMiddleIdentity.f 3 =
      𝟙 (sectionSevenUnitLerayModel.X 3) := by
  rw [sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 4 3 by rfl)
      (show (ComplexShape.down ℕ).Rel 3 2 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  exact contraction_identity_three

private theorem sectionSevenLerayMiddleIdentity_f_four :
    sectionSevenLerayMiddleIdentity.f 4 =
      𝟙 (sectionSevenUnitLerayModel.X 4) := by
  rw [sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 5 4 by rfl)
      (show (ComplexShape.down ℕ).Rel 4 3 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  exact contraction_identity_four

private theorem sectionSevenLerayMiddleIdentity_f_five :
    sectionSevenLerayMiddleIdentity.f 5 =
      𝟙 (sectionSevenUnitLerayModel.X 5) := by
  rw [sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 6 5 by rfl)
      (show (ComplexShape.down ℕ).Rel 5 4 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  change AddCommGrpCat.ofHom (sectionSevenLerayBoundaryFive (-1)) ≫
      AddCommGrpCat.ofHom sectionSevenLerayContractionFourFive +
      (0 : AddCommGrpCat.of (Fin 1 → ℤ) ⟶ AddCommGrpCat.of (Fin 1 → ℤ)) ≫
        (0 : AddCommGrpCat.of (Fin 1 → ℤ) ⟶ AddCommGrpCat.of (Fin 1 → ℤ)) =
    𝟙 (AddCommGrpCat.of (Fin 1 → ℤ))
  simpa only [zero_comp, add_zero] using contraction_identity_five

/-- Projection onto the two edge groups of the unit Section 7 matrix model. -/
public def sectionSevenLerayEdgeProjection :
    sectionSevenUnitLerayModel ⟶ sectionSevenUnitLerayModel :=
  𝟙 sectionSevenUnitLerayModel - sectionSevenLerayMiddleIdentity

/-- The explicit matrix homotopy from the identity to the edge projection. -/
public def sectionSevenLerayEdgeContraction :
    Homotopy (𝟙 sectionSevenUnitLerayModel) sectionSevenLerayEdgeProjection :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (by
      simp [sectionSevenLerayEdgeProjection, sectionSevenLerayMiddleIdentity])).trans
      (Homotopy.nullHomotopy' sectionSevenLerayContractionComponent)

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_zero :
    sectionSevenLerayEdgeProjection.f 0 =
      𝟙 (sectionSevenUnitLerayModel.X 0) := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 by rfl)
      (by
        intro l hl
        simp [ComplexShape.down_Rel] at hl),
    sectionSevenUnitLerayModel_d]
  change (𝟙 _) - ((0 : sectionSevenUnitLerayModel.X 0 ⟶
    sectionSevenUnitLerayModel.X 1) ≫ 0) = 𝟙 _
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_one :
    sectionSevenLerayEdgeProjection.f 1 = 0 := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity_f_one]
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_two :
    sectionSevenLerayEdgeProjection.f 2 = 0 := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity_f_two]
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_three :
    sectionSevenLerayEdgeProjection.f 3 = 0 := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity_f_three]
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_four :
    sectionSevenLerayEdgeProjection.f 4 = 0 := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity_f_four]
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_five :
    sectionSevenLerayEdgeProjection.f 5 = 0 := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity_f_five]
  simp

@[simp]
public theorem sectionSevenLerayEdgeProjection_f_six :
    sectionSevenLerayEdgeProjection.f 6 =
      𝟙 (sectionSevenUnitLerayModel.X 6) := by
  rw [sectionSevenLerayEdgeProjection, HomologicalComplex.sub_f_apply,
    sectionSevenLerayMiddleIdentity,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel 7 6 by rfl)
      (show (ComplexShape.down ℕ).Rel 6 5 by rfl),
    sectionSevenUnitLerayModel_d, sectionSevenUnitLerayModel_d]
  change (𝟙 _) - ((0 : sectionSevenUnitLerayModel.X 6 ⟶
      sectionSevenUnitLerayModel.X 5) ≫ 0 +
    (0 : sectionSevenUnitLerayModel.X 6 ⟶ sectionSevenUnitLerayModel.X 7) ≫ 0) = 𝟙 _
  simp

/-- A complex is homotopy equivalent to its direct sum with a contractible complement. -/
public noncomputable def homotopyEquivBiprodContractibleComplement
    (M K : ChainComplex AddCommGrpCat ℕ) (hK : Homotopy (𝟙 K) 0) :
    HomotopyEquiv M (M ⊞ K) where
  hom := biprod.inl
  inv := biprod.fst
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId :=
    let hComplement :=
      (hK.compRight (biprod.inr : K ⟶ M ⊞ K)).compLeft
        (biprod.snd : M ⊞ K ⟶ K)
    let hTotal := Homotopy.add
      (Homotopy.refl (biprod.fst ≫ biprod.inl)) hComplement
    (Homotopy.ofEq (by simp)).trans
      (hTotal.symm.trans (Homotopy.ofEq (by simp)))

/-- Additional chain-level data which, if supplied independently, transfers the Section 7 model
to an ordered Cech total.  This structure does not assert that Proposition 7.27 supplies such a
decomposition. -/
public structure SectionSevenDirectSumContractionData
    {A : FourPieceStarGluingData} (L : SectionSevenStarIntersectionChainModels A) where
  complement : ChainComplex AddCommGrpCat ℕ
  decomposition :
    L.localLerayCechTotal ≅ sectionSevenLerayChainModel (-1) ⊞ complement
  complementContraction : Homotopy (𝟙 complement) 0

namespace SectionSevenDirectSumContractionData

/-- The conditional homotopy equivalence supplied by explicit direct-sum contraction data. -/
public noncomputable def homotopyEquiv
    {A : FourPieceStarGluingData} {L : SectionSevenStarIntersectionChainModels A}
    (d : SectionSevenDirectSumContractionData L) :
    HomotopyEquiv (sectionSevenLerayChainModel (-1)) L.localLerayCechTotal :=
  (homotopyEquivBiprodContractibleComplement _ d.complement d.complementContraction).trans
    (HomotopyEquiv.ofIso d.decomposition.symm)

/-- Convert independently supplied direct-sum contraction data to the transfer package. -/
public noncomputable def transferredChainContraction
    {A : FourPieceStarGluingData} {L : SectionSevenStarIntersectionChainModels A}
    (d : SectionSevenDirectSumContractionData L) :
    SectionSevenTransferredChainContraction L :=
  let e := d.homotopyEquiv
  { transfer := e.hom
    collapse := e.inv
    homotopyTransferCollapse := e.homotopyHomInvId
    homotopyCollapseTransfer := e.homotopyInvHomId }

end SectionSevenDirectSumContractionData

end SphereSixComplex
