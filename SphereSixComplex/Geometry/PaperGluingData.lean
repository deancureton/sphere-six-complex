module

public import SphereSixComplex.Geometry.PaperAssembly
public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
public import SphereSixComplex.Geometry.EstablishedComplexToRealManifold
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Geometry.GlobalTorusFiberFundamentalGroup
public import SphereSixComplex.Geometry.EllipticFillingLoopPower
public import SphereSixComplex.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Exact gluing data for the completed paper threefold

This module packages every geometric and topological input consumed by `completedPaperThreefoldOfGluing`.
It is the concrete construction target upstream of the final existence theorem.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.TorusFamily Geometry.GlobalTorusFamily
open Geometry.AnalyticTorusFamily Geometry.EllipticWholeFiberCompactCover
open Geometry.EllipticVaryingFamilyQuotient
open Geometry.EllipticPuncturedCollarGaugeHomeomorph
open Geometry.EllipticAnalyticCollarDescent
open Geometry.EllipticLinearCollarGlobalDescent
open Geometry.EquivariantQuotientHomeomorph
open Periods TriangleGroup
open TriangleGroup.FuchsianArithmeticTermination

noncomputable section

/-- The selected analytic data specialized to the actual four-piece topological star. -/
@[expose] public noncomputable def paperFourPieceStar : FourPieceStarGluingData :=
  Geometry.paperAnalyticData.fourPieceStarGluingData

/-- The actual carrier formed from the punctured torus family, cusp filling, and two elliptic
fillings. -/
public abbrev PaperGluedCarrier := GluedSpace paperFourPieceStar.glueData

/-- All three collars of the selected paper star are nonempty. -/
public theorem paperFourPieceStar_nonemptyCentralCollar :
    ∀ i, Nonempty (paperFourPieceStar.centralCollar i) :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_nonemptyCentralCollar

/-- Every selected piece is connected. -/
public theorem paperFourPieceStar_connectedPiece :
    ∀ i, ConnectedSpace (paperFourPieceStar.glueData.U i) :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_connectedPiece

/-- Every selected piece is path connected. -/
public theorem paperFourPieceStar_pathConnectedPiece :
    ∀ i, PathConnectedSpace (paperFourPieceStar.glueData.U i) :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_pathConnectedPiece

/-- Every selected attaching collar in the central piece is path connected. -/
public theorem paperFourPieceStar_pathConnectedCentralCollar (i : Fin 3) :
    PathConnectedSpace (paperFourPieceStar.centralCollar i) :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_pathConnectedCentralCollar i

/-- The actual cusp and elliptic attaching maps are biholomorphic in the selected atlases. -/
public noncomputable def paperFourPieceStarBiholomorphicData :
    Geometry.EstablishedBiholomorphicStarGluing.BiholomorphicFourPieceStarData
      paperFourPieceStar :=
  Geometry.paperAnalyticData.fourPieceStarBiholomorphicData

/-- Every selected piece is second countable. -/
public theorem paperFourPieceStar_pieceSecondCountable :
    ∀ i, SecondCountableTopology (paperFourPieceStar.glueData.U i) :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_pieceSecondCountable

/-- The concrete paper carrier is Hausdorff; all three collar graphs are closed. -/
public theorem paperFourPieceStar_gluedT2 : T2Space PaperGluedCarrier :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_gluedT2

/-- The concrete paper carrier is compact; its three ends are covered by compact filling
half-cores and the remaining bounded central base core is compact. -/
public theorem paperFourPieceStar_gluedCompact : CompactSpace PaperGluedCarrier :=
  Geometry.paperAnalyticData.fourPieceStarGluingData_gluedCompact

/-- The central-family point selected in the cusp collar for the van Kampen computation. -/
@[expose] public noncomputable def paperVanKampenCentralPoint :
    Geometry.paperAnalyticData.CentralFamily :=
  (Classical.choice (paperFourPieceStar_nonemptyCentralCollar 0)).1

/-- A concrete basepoint in the cusp collar of the central family, viewed in the actual glued
carrier. -/
@[expose] public noncomputable def paperVanKampenBasepoint : PaperGluedCarrier :=
  paperFourPieceStar.glueData.toGlueData.ι none
    paperVanKampenCentralPoint

/-- A chosen lift of the central van Kampen point through the outer triangle-group quotient. -/
@[expose] public noncomputable def paperVanKampenOuterRepresentative :
    RegularTotalSpace Geometry.paperAnalyticData.periods := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  exact quotientSection
    (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)
    paperVanKampenCentralPoint

/-- The outer triangle-group projection at the concrete paper family is an honest quotient
covering.  The regular base has removed the two elliptic orbits, so the descended action is free
as well as properly discontinuous. -/
public theorem paperVanKampenOuterQuotient_isQuotientCoveringMap :
    let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
    IsQuotientCoveringMap
      (quotientProjection
        (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)) Delta := by
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul
    (regularParameterMap Geometry.paperAnalyticData.periods)
  let _ := familyContinuousConstSMul
    (regularParameterMap Geometry.paperAnalyticData.periods)
    (fun a ↦ (regularPeriodSection_contMDiff Geometry.paperAnalyticData.periods
      hproper a RegularSmoothnessOrder).continuous)
  let _ := familyProperlyDiscontinuousSMul
    (regularParameterMap Geometry.paperAnalyticData.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap Geometry.paperAnalyticData.periods)
      (regularParameterMap_compactUniformLowerBound Geometry.paperAnalyticData.periods))
  let _ : LocallyCompactSpace
      (RegularTotalSpace Geometry.paperAnalyticData.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  let _ : IsCancelSMul Delta
      (RegularTotalSpace Geometry.paperAnalyticData.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian
      Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      hproper
  let _ : ProperlyDiscontinuousSMul Delta
      (RegularTotalSpace Geometry.paperAnalyticData.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source
      Geometry.paperAnalyticData.periods hproper
  let _ : ContinuousConstSMul Delta
      (RegularTotalSpace Geometry.paperAnalyticData.periods) :=
    regularFamilyDeckAction_continuousConstSMul
      Geometry.paperAnalyticData.periods hproper
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- A chosen lift of the same point through the fibrewise period-lattice quotient. -/
@[expose] public noncomputable def paperVanKampenInnerRepresentative :
    RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace :=
  quotientSection
    (M := RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace)
    (G := FamilyPeriodGroup
      (regularParameterMap Geometry.paperAnalyticData.periods))
    paperVanKampenOuterRepresentative

/-- The regular source-base coordinate of the chosen van Kampen lift. -/
public abbrev paperVanKampenRegularBasepoint :
    RegularBase
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
  paperVanKampenInnerRepresentative.1

/-- The `ℂ²` coordinate of the chosen van Kampen lift. -/
public abbrev paperVanKampenFiberPoint : ComplexTwoSpace :=
  paperVanKampenInnerRepresentative.2

/-- The actual torus fibre through the chosen lift of the van Kampen basepoint. -/
public abbrev PaperVanKampenFiberTorus :=
  FiberTorus Geometry.paperAnalyticData.periods paperVanKampenRegularBasepoint

/-- Include the punctured central family into the central open piece of the glued carrier. -/
@[expose] public noncomputable def paperVanKampenCentralToCarrier :
    C(Geometry.paperAnalyticData.CentralFamily, PaperGluedCarrier) :=
  ⟨paperFourPieceStar.glueData.toGlueData.ι none,
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous⟩

/-- The chosen outer lift maps to the selected basepoint after entering the glued carrier. -/
public theorem paperVanKampenCentralToCarrier_basepoint :
    paperVanKampenCentralToCarrier
        (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
          paperVanKampenOuterRepresentative) =
      paperVanKampenBasepoint := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  change paperFourPieceStar.glueData.toGlueData.ι none
      (quotientProjection
        (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)
        paperVanKampenOuterRepresentative) =
    paperFourPieceStar.glueData.toGlueData.ι none paperVanKampenCentralPoint
  congr 1
  exact quotientProjection_section paperVanKampenCentralPoint

/-- The selected path from the van Kampen lift to its translate by a triangle-group element.
The endpoint records the deck monodromy before the path is projected to the central quotient. -/
@[expose] public noncomputable def paperVanKampenMeridianLiftPath (g : Delta) :
    Path paperVanKampenOuterRepresentative
      (regularFamilyDeckMap Geometry.paperAnalyticData.periods g
        paperVanKampenOuterRepresentative) :=
  regularDeckPath Geometry.paperAnalyticData.periods paperVanKampenOuterRepresentative g

/-- A based loop in the actual glued carrier obtained by projecting a path to its deck translate
and then including the central family. -/
@[expose] public noncomputable def paperVanKampenDeckMeridianLoop (g : Delta) :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  ((regularDeckLoop Geometry.paperAnalyticData.periods
      paperVanKampenOuterRepresentative g).map
        paperVanKampenCentralToCarrier.continuous).cast
    paperVanKampenCentralToCarrier_basepoint.symm
    paperVanKampenCentralToCarrier_basepoint.symm

/-- The fundamental-group class of the deck meridian associated to `g`. -/
@[expose] public noncomputable def paperVanKampenDeckMeridian (g : Delta) :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  Path.Homotopic.Quotient.mk (paperVanKampenDeckMeridianLoop g)

/-- The concrete order-three deck-meridian class. -/
public noncomputable def paperVanKampenDeckMeridianOne :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  paperVanKampenDeckMeridian g₁

/-- The concrete order-four deck-meridian class. -/
public noncomputable def paperVanKampenDeckMeridianTwo :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  paperVanKampenDeckMeridian g₂

/-- At any regular-family representative, the two standard triangle-group deck meridians and
the image of the regular torus family's fundamental group generate the central family. -/
public theorem paperVanKampenCentralFamily_outerDeckAndCoverRange_generate_at
    (x : RegularTotalSpace Geometry.paperAnalyticData.periods) :
    let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
    Subgroup.closure
      (({regularDeckMeridian Geometry.paperAnalyticData.periods x g₁,
        regularDeckMeridian Geometry.paperAnalyticData.periods x g₂} :
          Set (FundamentalGroup Geometry.paperAnalyticData.CentralFamily
            (regularFamilyQuotientMap Geometry.paperAnalyticData.periods x))) ∪
        (FundamentalGroup.mapOfEq
          (regularFamilyQuotientMap Geometry.paperAnalyticData.periods)
          (x := x) (y := regularFamilyQuotientMap Geometry.paperAnalyticData.periods x)
          rfl).range) = ⊤ := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  let _ : PathConnectedSpace
      (RegularTotalSpace Geometry.paperAnalyticData.periods) :=
    regularTotalSpace_pathConnected Geometry.paperAnalyticData.periods
  let hp := paperVanKampenOuterQuotient_isQuotientCoveringMap
  let S : Set (FundamentalGroup Geometry.paperAnalyticData.CentralFamily
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods x)) :=
    {regularDeckMeridian Geometry.paperAnalyticData.periods x g₁,
      regularDeckMeridian Geometry.paperAnalyticData.periods x g₂}
  have hmono (g : Delta) :
      hp.fundamentalGroupToMulOpposite
          (⟨x, rfl⟩ : (quotientProjection
              (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)) ⁻¹'
            {quotientProjection
              (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta) x})
          (regularDeckMeridian Geometry.paperAnalyticData.periods x g) =
        MulOpposite.op g := by
    change hp.fundamentalGroupToMulOpposite _
      (pathLoopClass (projectedOrbitDeckPath x g
        (regularDeckPath Geometry.paperAnalyticData.periods x g))) = _
    exact fundamentalGroupToMulOpposite_projectedOrbitDeckPath hp x g
      (regularDeckPath Geometry.paperAnalyticData.periods x g)
  have himage : Subgroup.closure
      (hp.fundamentalGroupToMulOpposite
        (⟨x, rfl⟩ : (quotientProjection
            (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)) ⁻¹'
          {quotientProjection
            (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta) x}) '' S) = ⊤ := by
    rw [show hp.fundamentalGroupToMulOpposite
          (⟨x, rfl⟩ : (quotientProjection
              (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)) ⁻¹'
            {quotientProjection
              (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta) x}) '' S =
        ({MulOpposite.op g₁, MulOpposite.op g₂} : Set Deltaᵐᵒᵖ) by
      ext g
      constructor
      · rintro ⟨m, hm, rfl⟩
        rcases hm with (rfl | rfl)
        · exact Or.inl (hmono g₁)
        · exact Or.inr (hmono g₂)
      · rintro (rfl | rfl)
        · exact ⟨regularDeckMeridian Geometry.paperAnalyticData.periods x g₁,
            Or.inl rfl, hmono g₁⟩
        · exact ⟨regularDeckMeridian Geometry.paperAnalyticData.periods x g₂,
            Or.inr rfl, hmono g₂⟩]
    exact delta_op_generators_generate
  have hgenerate := quotientCovering_generators_and_cover_range_generate hp x S himage
  convert hgenerate using 1; rfl

/-- Before the filling pieces are attached, the two standard triangle-group deck meridians and
the image of the regular torus family's fundamental group generate the central family's
fundamental group.  Thus the remaining central generation problem lies entirely upstairs in the
regular family; no additional generators can arise from the outer `Delta` quotient. -/
public theorem paperVanKampenCentralFamily_outerDeckAndCoverRange_generate :
    let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
    Subgroup.closure
      (({regularDeckMeridian Geometry.paperAnalyticData.periods
          paperVanKampenOuterRepresentative g₁,
        regularDeckMeridian Geometry.paperAnalyticData.periods
          paperVanKampenOuterRepresentative g₂} :
          Set (FundamentalGroup Geometry.paperAnalyticData.CentralFamily
            (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
              paperVanKampenOuterRepresentative))) ∪
        (FundamentalGroup.mapOfEq
          (regularFamilyQuotientMap Geometry.paperAnalyticData.periods)
          (x := paperVanKampenOuterRepresentative)
          (y := regularFamilyQuotientMap Geometry.paperAnalyticData.periods
            paperVanKampenOuterRepresentative) rfl).range) = ⊤ := by
  exact paperVanKampenCentralFamily_outerDeckAndCoverRange_generate_at
    paperVanKampenOuterRepresentative

/-- The selected radii of the two actual affine elliptic filling pieces. -/
public abbrev paperVanKampenOrderThreeRadius : ℝ :=
  Geometry.paperAnalyticData.starSeparation.orderThree.radius

public abbrev paperVanKampenOrderFourRadius : ℝ :=
  Geometry.paperAnalyticData.starSeparation.orderFour.radius

/-- Points of the two real common collar sources used to base the filling-side meridians. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarPoint :
    Geometry.paperAnalyticData.starCollarSourceType 1 :=
  Classical.choice (Geometry.paperAnalyticData.starCollarSource_nonempty 1)

@[expose] public noncomputable def paperVanKampenOrderFourCollarPoint :
    Geometry.paperAnalyticData.starCollarSourceType 2 :=
  Classical.choice (Geometry.paperAnalyticData.starCollarSource_nonempty 2)

/-- Chosen prequotient representatives of the two common elliptic collar points. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarRepresentative :
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderThreeRadius).carrier := by
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderThreeRadius)
  exact quotientSection
    (M := (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderThreeRadius).carrier)
    (G := FiniteCyclic 3) paperVanKampenOrderThreeCollarPoint

@[expose] public noncomputable def paperVanKampenOrderFourCollarRepresentative :
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderFourRadius).carrier := by
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderFourRadius)
  exact quotientSection
    (M := (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderFourRadius).carrier)
    (G := FiniteCyclic 4) paperVanKampenOrderFourCollarPoint

/-- A lift of the selected order-three collar representative to the explicit punctured-disc
times vector-space cover. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarCoverRepresentative :
    Geometry.PaperAnalyticData.ComplexDiscPuncturedBall
        paperVanKampenOrderThreeRadius × ComplexTwoSpace :=
  Classical.choose
    (Geometry.paperAnalyticData.orderThreePuncturedCoverMap_surjective
      paperVanKampenOrderThreeRadius paperVanKampenOrderThreeCollarRepresentative)

public theorem paperVanKampenOrderThreeCollarCoverRepresentative_projects :
    Geometry.paperAnalyticData.orderThreePuncturedCoverMap
        paperVanKampenOrderThreeRadius
        paperVanKampenOrderThreeCollarCoverRepresentative =
      paperVanKampenOrderThreeCollarRepresentative :=
  Classical.choose_spec
    (Geometry.paperAnalyticData.orderThreePuncturedCoverMap_surjective
      paperVanKampenOrderThreeRadius paperVanKampenOrderThreeCollarRepresentative)

/-- A lift of the selected order-four collar representative to the explicit punctured-disc
times vector-space cover. -/
@[expose] public noncomputable def paperVanKampenOrderFourCollarCoverRepresentative :
    Geometry.PaperAnalyticData.ComplexDiscPuncturedBall
        paperVanKampenOrderFourRadius × ComplexTwoSpace :=
  Classical.choose
    (Geometry.paperAnalyticData.orderFourPuncturedCoverMap_surjective
      paperVanKampenOrderFourRadius paperVanKampenOrderFourCollarRepresentative)

public theorem paperVanKampenOrderFourCollarCoverRepresentative_projects :
    Geometry.paperAnalyticData.orderFourPuncturedCoverMap
        paperVanKampenOrderFourRadius
        paperVanKampenOrderFourCollarCoverRepresentative =
      paperVanKampenOrderFourCollarRepresentative :=
  Classical.choose_spec
    (Geometry.paperAnalyticData.orderFourPuncturedCoverMap_surjective
      paperVanKampenOrderFourRadius paperVanKampenOrderFourCollarRepresentative)

/-- Iterating the selected order-three affine lift three times produces the exact `epsilon`
period translate of its chosen punctured-cover representative. -/
public theorem paperVanKampenOrderThreeCollarCoverGenerator_iterate_three :
    (Geometry.paperAnalyticData.orderThreeAffinePuncturedCoverGenerator)^[3]
        paperVanKampenOrderThreeCollarCoverRepresentative =
      Geometry.paperAnalyticData.orderThreeAffinePuncturedCoverPeriodTranslate
        paperVanKampenOrderThreeCollarCoverRepresentative :=
  Geometry.paperAnalyticData.orderThreeAffinePuncturedCoverGenerator_iterate_three
    paperVanKampenOrderThreeCollarCoverRepresentative

/-- Iterating the selected order-four affine lift four times produces the exact `-epsilon'`
period translate of its chosen punctured-cover representative. -/
public theorem paperVanKampenOrderFourCollarCoverGenerator_iterate_four :
    (Geometry.paperAnalyticData.orderFourAffinePuncturedCoverGenerator)^[4]
        paperVanKampenOrderFourCollarCoverRepresentative =
      Geometry.paperAnalyticData.orderFourAffinePuncturedCoverPeriodTranslate
        paperVanKampenOrderFourCollarCoverRepresentative :=
  Geometry.paperAnalyticData.orderFourAffinePuncturedCoverGenerator_iterate_four
    paperVanKampenOrderFourCollarCoverRepresentative

/-- In the selected order-three filling cover, the threefold affine collar path is homotopic
relative endpoints to the straight `epsilon` period path. -/
public theorem paperVanKampenOrderThreeCollarCoverPower_homotopic_periodPath :
    Path.Homotopic
      (Geometry.paperAnalyticData.orderThreeAffinePuncturedCoverLiftPathThreeToFull
        paperVanKampenOrderThreeCollarCoverRepresentative)
      (Geometry.paperAnalyticData.orderThreeFullCoverPeriodPath
        paperVanKampenOrderThreeCollarCoverRepresentative) :=
  Geometry.paperAnalyticData
    |>.orderThreeAffinePuncturedCoverLiftPathThree_homotopic_periodPath
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_lt_one
      paperVanKampenOrderThreeCollarCoverRepresentative

/-- In the selected order-four filling cover, the fourfold affine collar path is homotopic
relative endpoints to the straight `-epsilon'` period path. -/
public theorem paperVanKampenOrderFourCollarCoverPower_homotopic_periodPath :
    Path.Homotopic
      (Geometry.paperAnalyticData.orderFourAffinePuncturedCoverLiftPathFourToFull
        paperVanKampenOrderFourCollarCoverRepresentative)
      (Geometry.paperAnalyticData.orderFourFullCoverPeriodPath
        paperVanKampenOrderFourCollarCoverRepresentative) :=
  Geometry.paperAnalyticData
    |>.orderFourAffinePuncturedCoverLiftPathFour_homotopic_periodPath
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_lt_one
      paperVanKampenOrderFourCollarCoverRepresentative

/-- The selected order-three power-to-period homotopy after projection to the actual
prequotient filling source. -/
public theorem paperVanKampenOrderThreeFillingSourcePower_homotopic_periodPath :
    Path.Homotopic
      ((Geometry.paperAnalyticData
        |>.orderThreeAffinePuncturedCoverLiftPathThreeToFull
          paperVanKampenOrderThreeCollarCoverRepresentative).map
        (Geometry.paperAnalyticData.orderThreeFillingCoverMap_continuous
          paperVanKampenOrderThreeRadius))
      ((Geometry.paperAnalyticData.orderThreeFullCoverPeriodPath
          paperVanKampenOrderThreeCollarCoverRepresentative).map
        (Geometry.paperAnalyticData.orderThreeFillingCoverMap_continuous
          paperVanKampenOrderThreeRadius)) :=
  Geometry.paperAnalyticData
    |>.orderThreeAffinePuncturedCoverLiftPathThree_fillingCover_homotopic_periodPath
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_lt_one
      paperVanKampenOrderThreeCollarCoverRepresentative

/-- The selected order-four power-to-period homotopy after projection to the actual
prequotient filling source. -/
public theorem paperVanKampenOrderFourFillingSourcePower_homotopic_periodPath :
    Path.Homotopic
      ((Geometry.paperAnalyticData
        |>.orderFourAffinePuncturedCoverLiftPathFourToFull
          paperVanKampenOrderFourCollarCoverRepresentative).map
        (Geometry.paperAnalyticData.orderFourFillingCoverMap_continuous
          paperVanKampenOrderFourRadius))
      ((Geometry.paperAnalyticData.orderFourFullCoverPeriodPath
          paperVanKampenOrderFourCollarCoverRepresentative).map
        (Geometry.paperAnalyticData.orderFourFillingCoverMap_continuous
          paperVanKampenOrderFourRadius)) :=
  Geometry.paperAnalyticData
    |>.orderFourAffinePuncturedCoverLiftPathFour_fillingCover_homotopic_periodPath
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_lt_one
      paperVanKampenOrderFourCollarCoverRepresentative

/-- The explicit angular-and-affine path inside the common order-three collar from the selected
representative to its cyclic deck translate. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarDeckPath :
    Path paperVanKampenOrderThreeCollarRepresentative
      (let _ := restrictedMulAction
          (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
          (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
            Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
            paperVanKampenOrderThreeRadius)
       cyclicGenerator 3 • paperVanKampenOrderThreeCollarRepresentative) := by
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderThreeRadius)
  exact (Geometry.paperAnalyticData.orderThreeAffinePuncturedCoverDeckPath
      paperVanKampenOrderThreeCollarCoverRepresentative).cast
    paperVanKampenOrderThreeCollarCoverRepresentative_projects.symm
    (congrArg (fun q => cyclicGenerator 3 • q)
      paperVanKampenOrderThreeCollarCoverRepresentative_projects).symm

/-- The explicit angular-and-affine path inside the common order-four collar from the selected
representative to its cyclic deck translate. -/
@[expose] public noncomputable def paperVanKampenOrderFourCollarDeckPath :
    Path paperVanKampenOrderFourCollarRepresentative
      (let _ := restrictedMulAction
          (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
          (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
            Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
            paperVanKampenOrderFourRadius)
       cyclicGenerator 4 • paperVanKampenOrderFourCollarRepresentative) := by
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderFourRadius)
  exact (Geometry.paperAnalyticData.orderFourAffinePuncturedCoverDeckPath
      paperVanKampenOrderFourCollarCoverRepresentative).cast
    paperVanKampenOrderFourCollarCoverRepresentative_projects.symm
    (congrArg (fun q => cyclicGenerator 4 • q)
      paperVanKampenOrderFourCollarCoverRepresentative_projects).symm

/-- The common-source deck paths descend to loops before either collar embedding is selected. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarDeckLoop :
    Path paperVanKampenOrderThreeCollarPoint paperVanKampenOrderThreeCollarPoint := by
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderThreeRadius)
  exact ((paperVanKampenOrderThreeCollarDeckPath.map
      (orbitQuotientMap (G := FiniteCyclic 3)).continuous).cast rfl
        (orbitQuotientMap_smul paperVanKampenOrderThreeCollarRepresentative
          (cyclicGenerator 3)).symm).cast
    (quotientProjection_section paperVanKampenOrderThreeCollarPoint).symm
    (quotientProjection_section paperVanKampenOrderThreeCollarPoint).symm

@[expose] public noncomputable def paperVanKampenOrderFourCollarDeckLoop :
    Path paperVanKampenOrderFourCollarPoint paperVanKampenOrderFourCollarPoint := by
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
      paperVanKampenOrderFourRadius)
  exact ((paperVanKampenOrderFourCollarDeckPath.map
      (orbitQuotientMap (G := FiniteCyclic 4)).continuous).cast rfl
        (orbitQuotientMap_smul paperVanKampenOrderFourCollarRepresentative
          (cyclicGenerator 4)).symm).cast
    (quotientProjection_section paperVanKampenOrderFourCollarPoint).symm
    (quotientProjection_section paperVanKampenOrderFourCollarPoint).symm

/-- The logarithmically gauged common collars embedded before the outer `Delta` quotient. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarToRegular :
    C((orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
        Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
        paperVanKampenOrderThreeRadius).carrier,
      RegularTotalSpace Geometry.paperAnalyticData.periods) := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let gauge := orderThreePuncturedCollarGaugeDiffeomorph
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    paperVanKampenOrderThreeRadius
  exact ⟨fun q => orderThreeCollarToRegular Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderThree.sourceData (gauge q),
    (orderThreeCollarToRegular_isOpenEmbedding Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderThree.sourceData).continuous.comp
        gauge.continuous⟩

@[expose] public noncomputable def paperVanKampenOrderFourCollarToRegular :
    C((orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
        Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
        paperVanKampenOrderFourRadius).carrier,
      RegularTotalSpace Geometry.paperAnalyticData.periods) := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let gauge := orderFourPuncturedCollarGaugeDiffeomorph
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    paperVanKampenOrderFourRadius
  exact ⟨fun q => orderFourCollarToRegular Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderFour.sourceData (gauge q),
    (orderFourCollarToRegular_isOpenEmbedding Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderFour.sourceData).continuous.comp
        gauge.continuous⟩

/-- The common order-three affine generator becomes exactly the regular-family `g₁` deck map. -/
public theorem paperVanKampenOrderThreeCollarToRegular_generator :
    let _ := restrictedMulAction
      (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
      (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods
        Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
        paperVanKampenOrderThreeRadius)
    paperVanKampenOrderThreeCollarToRegular
        (cyclicGenerator 3 • paperVanKampenOrderThreeCollarRepresentative) =
      regularFamilyDeckMap Geometry.paperAnalyticData.periods g₁
        (paperVanKampenOrderThreeCollarToRegular
          paperVanKampenOrderThreeCollarRepresentative) := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
      paperVanKampenOrderThreeRadius)
  change orderThreeCollarToRegular Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarGaugeDiffeomorph Geometry.paperAnalyticData.periods
          Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
          paperVanKampenOrderThreeRadius
          (restrictedActionMap
            (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
              paperVanKampenOrderThreeRadius)
            (cyclicGenerator 3) paperVanKampenOrderThreeCollarRepresentative)) =
    regularFamilyDeckMap Geometry.paperAnalyticData.periods g₁
      (orderThreeCollarToRegular Geometry.paperAnalyticData.periods hproper
        Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeDiffeomorph Geometry.paperAnalyticData.periods
            Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
            paperVanKampenOrderThreeRadius
            paperVanKampenOrderThreeCollarRepresentative))
  have hgenerator : Monoid.Coprod.inl (cyclicGenerator 3) = g₁ := by
    change Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁
    exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm
  rw [← hgenerator]
  exact orderThreeAffineCollarLift_action Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
    (cyclicGenerator 3) paperVanKampenOrderThreeCollarRepresentative

/-- The common order-four affine generator becomes exactly the regular-family `g₂` deck map. -/
public theorem paperVanKampenOrderFourCollarToRegular_generator :
    let _ := restrictedMulAction
      (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
      (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods
        Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
        paperVanKampenOrderFourRadius)
    paperVanKampenOrderFourCollarToRegular
        (cyclicGenerator 4 • paperVanKampenOrderFourCollarRepresentative) =
      regularFamilyDeckMap Geometry.paperAnalyticData.periods g₂
        (paperVanKampenOrderFourCollarToRegular
          paperVanKampenOrderFourCollarRepresentative) := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
      paperVanKampenOrderFourRadius)
  change orderFourCollarToRegular Geometry.paperAnalyticData.periods hproper
      Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarGaugeDiffeomorph Geometry.paperAnalyticData.periods
          Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
          paperVanKampenOrderFourRadius
          (restrictedActionMap
            (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
              paperVanKampenOrderFourRadius)
            (cyclicGenerator 4) paperVanKampenOrderFourCollarRepresentative)) =
    regularFamilyDeckMap Geometry.paperAnalyticData.periods g₂
      (orderFourCollarToRegular Geometry.paperAnalyticData.periods hproper
        Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeDiffeomorph Geometry.paperAnalyticData.periods
            Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
            paperVanKampenOrderFourRadius
            paperVanKampenOrderFourCollarRepresentative))
  have hgenerator : Monoid.Coprod.inr (cyclicGenerator 4) = g₂ := by
    change Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂
    exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm
  rw [← hgenerator]
  exact orderFourAffineCollarLift_action Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
    (cyclicGenerator 4) paperVanKampenOrderFourCollarRepresentative

/-- Regular-family representatives and genuine `g₁`/`g₂` deck paths obtained from the same
common-source paths used by the filling meridians. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCentralRepresentative :
    RegularTotalSpace Geometry.paperAnalyticData.periods :=
  paperVanKampenOrderThreeCollarToRegular paperVanKampenOrderThreeCollarRepresentative

@[expose] public noncomputable def paperVanKampenOrderFourCentralRepresentative :
    RegularTotalSpace Geometry.paperAnalyticData.periods :=
  paperVanKampenOrderFourCollarToRegular paperVanKampenOrderFourCollarRepresentative

@[expose] public noncomputable def paperVanKampenOrderThreeCollarRegularDeckPath :
    Path paperVanKampenOrderThreeCentralRepresentative
      (regularFamilyDeckMap Geometry.paperAnalyticData.periods g₁
        paperVanKampenOrderThreeCentralRepresentative) :=
  (paperVanKampenOrderThreeCollarDeckPath.map
      paperVanKampenOrderThreeCollarToRegular.continuous).cast rfl
    paperVanKampenOrderThreeCollarToRegular_generator.symm

@[expose] public noncomputable def paperVanKampenOrderFourCollarRegularDeckPath :
    Path paperVanKampenOrderFourCentralRepresentative
      (regularFamilyDeckMap Geometry.paperAnalyticData.periods g₂
        paperVanKampenOrderFourCentralRepresentative) :=
  (paperVanKampenOrderFourCollarDeckPath.map
      paperVanKampenOrderFourCollarToRegular.continuous).cast rfl
    paperVanKampenOrderFourCollarToRegular_generator.symm

/-- The genuine regular-source deck paths project to loops in the central family. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarRegularDeckLoop :
    Path (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderThreeCentralRepresentative)
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderThreeCentralRepresentative) :=
  (paperVanKampenOrderThreeCollarRegularDeckPath.map
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods).continuous).cast rfl
    (regularFamilyQuotientMap_deck Geometry.paperAnalyticData.periods
      paperVanKampenOrderThreeCentralRepresentative g₁).symm

@[expose] public noncomputable def paperVanKampenOrderFourCollarRegularDeckLoop :
    Path (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderFourCentralRepresentative)
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderFourCentralRepresentative) :=
  (paperVanKampenOrderFourCollarRegularDeckPath.map
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods).continuous).cast rfl
    (regularFamilyQuotientMap_deck Geometry.paperAnalyticData.periods
      paperVanKampenOrderFourCentralRepresentative g₂).symm

/-- The order-three regular representative projects to the central image of the selected common
collar point. -/
public theorem paperVanKampenOrderThreeCentralRepresentative_projects :
    regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderThreeCentralRepresentative =
      Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource :=
    Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  have hmk := orderThreeAffineCollarToPuncturedGlobalFamily_mk
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
    paperVanKampenOrderThreeCollarRepresentative
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderThreeAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
      paperVanKampenOrderThreeRadius)
  have hsection := quotientProjection_section paperVanKampenOrderThreeCollarPoint
  calc
    regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderThreeCentralRepresentative =
        Geometry.paperAnalyticData.orderThreePuncturedCollarToCentralFamily
          Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
          (Quotient.mk _ paperVanKampenOrderThreeCollarRepresentative) := by
      exact hmk.symm
    _ = Geometry.paperAnalyticData.starToCentral 1
        (Quotient.mk _ paperVanKampenOrderThreeCollarRepresentative) := rfl
    _ = Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint :=
      congrArg (Geometry.paperAnalyticData.starToCentral 1) hsection

/-- The order-four regular representative projects to the central image of the selected common
collar point. -/
public theorem paperVanKampenOrderFourCentralRepresentative_projects :
    regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderFourCentralRepresentative =
      Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint := by
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource :=
    Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  have hmk := orderFourAffineCollarToPuncturedGlobalFamily_mk
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
    paperVanKampenOrderFourCollarRepresentative
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction Geometry.paperAnalyticData.periods)
    (orderFourAffinePuncturedCarrier Geometry.paperAnalyticData.periods hsource
      paperVanKampenOrderFourRadius)
  have hsection := quotientProjection_section paperVanKampenOrderFourCollarPoint
  calc
    regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOrderFourCentralRepresentative =
        Geometry.paperAnalyticData.orderFourPuncturedCollarToCentralFamily
          Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
          (Quotient.mk _ paperVanKampenOrderFourCollarRepresentative) := by
      exact hmk.symm
    _ = Geometry.paperAnalyticData.starToCentral 2
        (Quotient.mk _ paperVanKampenOrderFourCollarRepresentative) := rfl
    _ = Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint :=
      congrArg (Geometry.paperAnalyticData.starToCentral 2) hsection

/-- The two continuous central-family embeddings of the common elliptic collars. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarToCentral :
    C(Geometry.paperAnalyticData.starCollarSourceType 1,
      Geometry.paperAnalyticData.CentralFamily) :=
  ⟨Geometry.paperAnalyticData.starToCentral 1,
    (Geometry.paperAnalyticData.starToCentral_isOpenEmbedding 1).continuous⟩

@[expose] public noncomputable def paperVanKampenOrderFourCollarToCentral :
    C(Geometry.paperAnalyticData.starCollarSourceType 2,
      Geometry.paperAnalyticData.CentralFamily) :=
  ⟨Geometry.paperAnalyticData.starToCentral 2,
    (Geometry.paperAnalyticData.starToCentral_isOpenEmbedding 2).continuous⟩

/-- On the central side, the common order-three collar loop is pointwise the genuine `g₁`
regular-family deck loop, after changing only its displayed endpoint proof. -/
public theorem paperVanKampenOrderThreeCollarDeckLoop_toCentral_eq :
    paperVanKampenOrderThreeCollarDeckLoop.map
        paperVanKampenOrderThreeCollarToCentral.continuous =
      paperVanKampenOrderThreeCollarRegularDeckLoop.cast
        paperVanKampenOrderThreeCentralRepresentative_projects.symm
        paperVanKampenOrderThreeCentralRepresentative_projects.symm := by
  apply Path.ext
  funext t
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource :=
    Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  exact orderThreeAffineCollarToPuncturedGlobalFamily_mk
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderThree.sourceData
    (paperVanKampenOrderThreeCollarDeckPath t)

/-- On the central side, the common order-four collar loop is pointwise the genuine `g₂`
regular-family deck loop, after changing only its displayed endpoint proof. -/
public theorem paperVanKampenOrderFourCollarDeckLoop_toCentral_eq :
    paperVanKampenOrderFourCollarDeckLoop.map
        paperVanKampenOrderFourCollarToCentral.continuous =
      paperVanKampenOrderFourCollarRegularDeckLoop.cast
        paperVanKampenOrderFourCentralRepresentative_projects.symm
        paperVanKampenOrderFourCentralRepresentative_projects.symm := by
  apply Path.ext
  funext t
  let _ := Geometry.paperAnalyticData.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap Geometry.paperAnalyticData.periods)) :=
    Geometry.paperAnalyticData.totalSpace_isManifold_analytic
  let hsource :=
    Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  exact orderFourAffineCollarToPuncturedGlobalFamily_mk
    Geometry.paperAnalyticData.periods
    Geometry.paperAnalyticData.totalSpace_projection_isLocalDiffeomorph_analytic
    hproper hsource Geometry.paperAnalyticData.starSeparation.orderFour.sourceData
    (paperVanKampenOrderFourCollarDeckPath t)

/-- The corresponding points in the two actual affine filling quotients. -/
@[expose] public noncomputable def paperVanKampenOrderThreeFillingPoint :
    Geometry.paperAnalyticData.starFillingType 1 :=
  Geometry.paperAnalyticData.starToFilling 1 paperVanKampenOrderThreeCollarPoint

@[expose] public noncomputable def paperVanKampenOrderFourFillingPoint :
    Geometry.paperAnalyticData.starFillingType 2 :=
  Geometry.paperAnalyticData.starToFilling 2 paperVanKampenOrderFourCollarPoint

/-- Chosen prequotient lifts of the collar points in the affine filling sources. -/
@[expose] public noncomputable def paperVanKampenOrderThreeFillingRepresentative :
    Geometry.paperAnalyticData.orderThreeFillingOpen paperVanKampenOrderThreeRadius := by
  let _ := Geometry.paperAnalyticData.orderThreeFillingAction
    paperVanKampenOrderThreeRadius
  exact quotientSection
    (M := Geometry.paperAnalyticData.orderThreeFillingOpen
      paperVanKampenOrderThreeRadius)
    (G := FiniteCyclic 3) paperVanKampenOrderThreeFillingPoint

@[expose] public noncomputable def paperVanKampenOrderFourFillingRepresentative :
    Geometry.paperAnalyticData.orderFourFillingOpen paperVanKampenOrderFourRadius := by
  let _ := Geometry.paperAnalyticData.orderFourFillingAction
    paperVanKampenOrderFourRadius
  exact quotientSection
    (M := Geometry.paperAnalyticData.orderFourFillingOpen
      paperVanKampenOrderFourRadius)
    (G := FiniteCyclic 4) paperVanKampenOrderFourFillingPoint

/-- Paths in the actual affine filling sources from each collar lift to its finite cyclic deck
translate.  Unlike the central deck paths above, these endpoints include the prescribed
one-third- and one-quarter-period affine twists. -/
@[expose] public noncomputable def paperVanKampenOrderThreeFillingDeckPath :
    Path paperVanKampenOrderThreeFillingRepresentative
      (let _ := Geometry.paperAnalyticData.orderThreeFillingAction
          paperVanKampenOrderThreeRadius
       cyclicGenerator 3 • paperVanKampenOrderThreeFillingRepresentative) := by
  let _ := Geometry.paperAnalyticData.orderThreeFillingAction
    paperVanKampenOrderThreeRadius
  let _ : PathConnectedSpace
      (Geometry.paperAnalyticData.orderThreeFillingOpen paperVanKampenOrderThreeRadius) :=
    Geometry.paperAnalyticData.orderThreeFillingOpen_pathConnected
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_lt_one
  exact orbitDeckPath paperVanKampenOrderThreeFillingRepresentative (cyclicGenerator 3)

@[expose] public noncomputable def paperVanKampenOrderFourFillingDeckPath :
    Path paperVanKampenOrderFourFillingRepresentative
      (let _ := Geometry.paperAnalyticData.orderFourFillingAction
          paperVanKampenOrderFourRadius
       cyclicGenerator 4 • paperVanKampenOrderFourFillingRepresentative) := by
  let _ := Geometry.paperAnalyticData.orderFourFillingAction
    paperVanKampenOrderFourRadius
  let _ : PathConnectedSpace
      (Geometry.paperAnalyticData.orderFourFillingOpen paperVanKampenOrderFourRadius) :=
    Geometry.paperAnalyticData.orderFourFillingOpen_pathConnected
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_lt_one
  exact orbitDeckPath paperVanKampenOrderFourFillingRepresentative (cyclicGenerator 4)

/-- The projected affine deck loops, based at the selected filling-collar points. -/
@[expose] public noncomputable def paperVanKampenOrderThreeFillingDeckLoop :
    Path paperVanKampenOrderThreeFillingPoint paperVanKampenOrderThreeFillingPoint := by
  let _ := Geometry.paperAnalyticData.orderThreeFillingAction
    paperVanKampenOrderThreeRadius
  let _ : PathConnectedSpace
      (Geometry.paperAnalyticData.orderThreeFillingOpen paperVanKampenOrderThreeRadius) :=
    Geometry.paperAnalyticData.orderThreeFillingOpen_pathConnected
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderThree.radius_lt_one
  exact (orbitDeckLoop paperVanKampenOrderThreeFillingRepresentative
      (cyclicGenerator 3)).cast
    (quotientProjection_section paperVanKampenOrderThreeFillingPoint).symm
    (quotientProjection_section paperVanKampenOrderThreeFillingPoint).symm

@[expose] public noncomputable def paperVanKampenOrderFourFillingDeckLoop :
    Path paperVanKampenOrderFourFillingPoint paperVanKampenOrderFourFillingPoint := by
  let _ := Geometry.paperAnalyticData.orderFourFillingAction
    paperVanKampenOrderFourRadius
  let _ : PathConnectedSpace
      (Geometry.paperAnalyticData.orderFourFillingOpen paperVanKampenOrderFourRadius) :=
    Geometry.paperAnalyticData.orderFourFillingOpen_pathConnected
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_pos
      Geometry.paperAnalyticData.starSeparation.orderFour.radius_lt_one
  exact (orbitDeckLoop paperVanKampenOrderFourFillingRepresentative
      (cyclicGenerator 4)).cast
    (quotientProjection_section paperVanKampenOrderFourFillingPoint).symm
    (quotientProjection_section paperVanKampenOrderFourFillingPoint).symm

/-- Chosen lifts of the two logarithmically gauged collar representatives through the regular
family-period quotient. -/
@[expose] public noncomputable def paperVanKampenOrderThreeRegularCoverRepresentative :
    RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace :=
  quotientSection paperVanKampenOrderThreeCentralRepresentative

@[expose] public noncomputable def paperVanKampenOrderFourRegularCoverRepresentative :
    RegularBase
        (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace :=
  quotientSection paperVanKampenOrderFourCentralRepresentative

public theorem paperVanKampenInnerRepresentative_projects :
    regularFamilyCoverProjection Geometry.paperAnalyticData.periods
        paperVanKampenInnerRepresentative =
      paperVanKampenOuterRepresentative :=
  quotientProjection_section paperVanKampenOuterRepresentative

/-- The outer quotient homomorphism at the selected regular-family representative. -/
public noncomputable def paperVanKampenRegularToCentralFundamentalGroup :
    FundamentalGroup (RegularTotalSpace Geometry.paperAnalyticData.periods)
        paperVanKampenOuterRepresentative →*
      FundamentalGroup Geometry.paperAnalyticData.CentralFamily
        (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
          paperVanKampenOuterRepresentative) :=
  FundamentalGroup.mapOfEq
    (regularFamilyQuotientMap Geometry.paperAnalyticData.periods) rfl

/-- The inner family-period quotient homomorphism at the selected vector-cover representative. -/
public noncomputable def paperVanKampenVectorCoverToRegularFundamentalGroup :
    FundamentalGroup
        (RegularBase
            (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace)
        paperVanKampenInnerRepresentative →*
      FundamentalGroup (RegularTotalSpace Geometry.paperAnalyticData.periods)
        paperVanKampenOuterRepresentative :=
  FundamentalGroup.mapOfEq
    (regularFamilyCoverProjection Geometry.paperAnalyticData.periods)
    paperVanKampenInnerRepresentative_projects

/-- Include the regular source base in its vector-bundle cover by fixing the selected fibre
coordinate.  The product eta equality identifies the displayed image with the named inner
representative. -/
public noncomputable def paperVanKampenRegularBaseToVectorCoverFundamentalGroup :
    FundamentalGroup
        (RegularBase
          (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization))
        paperVanKampenRegularBasepoint →*
      FundamentalGroup
        (RegularBase
            (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace)
        paperVanKampenInnerRepresentative :=
  FundamentalGroup.mapOfEq (prodConstSection paperVanKampenFiberPoint)
    (Prod.eta paperVanKampenInnerRepresentative)

/-- The contractible `ℂ²` factor contributes no further generators: the fixed-fibre inclusion
from the regular source base is surjective on fundamental groups. -/
public theorem paperVanKampenRegularBaseToVectorCoverFundamentalGroup_surjective :
    Function.Surjective paperVanKampenRegularBaseToVectorCoverFundamentalGroup := by
  unfold paperVanKampenRegularBaseToVectorCoverFundamentalGroup
  exact fundamentalGroup_mapOfEq_prodConstSection_surjective
    paperVanKampenRegularBasepoint paperVanKampenFiberPoint
    paperVanKampenInnerRepresentative (Prod.eta paperVanKampenInnerRepresentative)

/-- The two outer deck generators at the central-family basepoint. -/
public def paperVanKampenCentralDeckGeneratorSet :
    Set (FundamentalGroup Geometry.paperAnalyticData.CentralFamily
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods
        paperVanKampenOuterRepresentative)) :=
  {regularDeckMeridian Geometry.paperAnalyticData.periods
      paperVanKampenOuterRepresentative g₁,
    regularDeckMeridian Geometry.paperAnalyticData.periods
      paperVanKampenOuterRepresentative g₂}

/-- The explicit labelled-period loops, rebased at the selected regular-family point. -/
public def paperVanKampenRegularPeriodGeneratorSet :
    Set (FundamentalGroup (RegularTotalSpace Geometry.paperAnalyticData.periods)
      paperVanKampenOuterRepresentative) :=
  Set.range (fun a : IntegerPeriods ↦ pathLoopClass
    ((regularFamilyPeriodLoop Geometry.paperAnalyticData.periods
      paperVanKampenInnerRepresentative a).cast
        paperVanKampenInnerRepresentative_projects.symm
        paperVanKampenInnerRepresentative_projects.symm))

/-- Combining the two quotient-covering exact sequences, the central-family fundamental group is
generated by the two triangle-group meridians, the four labelled period loops, and the image of
the regular vector-bundle cover. -/
public theorem paperVanKampenCentralFamily_twoStageCoverGenerators_generate :
    Subgroup.closure
      (paperVanKampenCentralDeckGeneratorSet ∪
        paperVanKampenRegularToCentralFundamentalGroup ''
          paperVanKampenRegularPeriodGeneratorSet ∪
        ((paperVanKampenRegularToCentralFundamentalGroup.comp
          paperVanKampenVectorCoverToRegularFundamentalGroup).range : Set _)) = ⊤ := by
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  apply closure_nested_generators_and_composite_range_eq_top
    paperVanKampenRegularToCentralFundamentalGroup
    paperVanKampenVectorCoverToRegularFundamentalGroup
    paperVanKampenCentralDeckGeneratorSet
    paperVanKampenRegularPeriodGeneratorSet
  · exact paperVanKampenCentralFamily_outerDeckAndCoverRange_generate
  · exact regularFamilyPeriodLoops_and_vectorCoverRange_generate_of_eq
      Geometry.paperAnalyticData.periods hproper paperVanKampenInnerRepresentative
      paperVanKampenOuterRepresentative paperVanKampenInnerRepresentative_projects

/-- The two-stage covering generation theorem at an arbitrary vector-cover representative and a
propositionally identified point of the regular torus family. -/
public theorem paperVanKampenCentralFamily_twoStageCoverGenerators_generate_of_eq
    (p : RegularBase
          (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace)
    (x : RegularTotalSpace Geometry.paperAnalyticData.periods)
    (hpx : regularFamilyCoverProjection Geometry.paperAnalyticData.periods p = x) :
    let z := regularFamilyQuotientMap Geometry.paperAnalyticData.periods x
    let f := FundamentalGroup.mapOfEq
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods) (x := x) (y := z) rfl
    let g := FundamentalGroup.mapOfEq
      (regularFamilyCoverProjection Geometry.paperAnalyticData.periods) (x := p) (y := x) hpx
    Subgroup.closure
      (({regularDeckMeridian Geometry.paperAnalyticData.periods x g₁,
        regularDeckMeridian Geometry.paperAnalyticData.periods x g₂} : Set _) ∪
        f '' Set.range (fun a : IntegerPeriods ↦ pathLoopClass
          ((regularFamilyPeriodLoop Geometry.paperAnalyticData.periods p a).cast
            hpx.symm hpx.symm)) ∪
        ((f.comp g).range : Set _)) = ⊤ := by
  dsimp only
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  let hproper : SourceActionProperlyDiscontinuous
      (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization_sourceAction
  apply closure_nested_generators_and_composite_range_eq_top
    (FundamentalGroup.mapOfEq
      (regularFamilyQuotientMap Geometry.paperAnalyticData.periods)
      (x := x) (y := _) rfl)
    (FundamentalGroup.mapOfEq
      (regularFamilyCoverProjection Geometry.paperAnalyticData.periods)
      (x := p) (y := x) hpx)
    ({regularDeckMeridian Geometry.paperAnalyticData.periods x g₁,
      regularDeckMeridian Geometry.paperAnalyticData.periods x g₂} : Set _)
    (Set.range (fun a : IntegerPeriods ↦ pathLoopClass
      ((regularFamilyPeriodLoop Geometry.paperAnalyticData.periods p a).cast
        hpx.symm hpx.symm)))
  · exact paperVanKampenCentralFamily_outerDeckAndCoverRange_generate_at x
  · exact regularFamilyPeriodLoops_and_vectorCoverRange_generate_of_eq
      Geometry.paperAnalyticData.periods hproper p x hpx

/-- After discarding the simply connected vector-space factor, the only uncomputed central
generators are loops from the punctured regular source base.  Thus the remaining central
calculation is a planar puncture problem, not a torus-family quotient problem. -/
public theorem paperVanKampenCentralFamily_baseAndDeckGenerators_generate :
    Subgroup.closure
      (paperVanKampenCentralDeckGeneratorSet ∪
        paperVanKampenRegularToCentralFundamentalGroup ''
          paperVanKampenRegularPeriodGeneratorSet ∪
        (((paperVanKampenRegularToCentralFundamentalGroup.comp
            paperVanKampenVectorCoverToRegularFundamentalGroup).comp
          paperVanKampenRegularBaseToVectorCoverFundamentalGroup).range : Set _)) = ⊤ := by
  have hrange :
      ((paperVanKampenRegularToCentralFundamentalGroup.comp
          paperVanKampenVectorCoverToRegularFundamentalGroup).comp
        paperVanKampenRegularBaseToVectorCoverFundamentalGroup).range =
        (paperVanKampenRegularToCentralFundamentalGroup.comp
          paperVanKampenVectorCoverToRegularFundamentalGroup).range := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨paperVanKampenRegularBaseToVectorCoverFundamentalGroup a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ :=
        paperVanKampenRegularBaseToVectorCoverFundamentalGroup_surjective a
      exact ⟨b, rfl⟩
  rw [hrange]
  exact paperVanKampenCentralFamily_twoStageCoverGenerators_generate

public theorem paperVanKampenOrderThreeRegularCoverRepresentative_projects :
    regularFamilyCoverProjection Geometry.paperAnalyticData.periods
        paperVanKampenOrderThreeRegularCoverRepresentative =
      paperVanKampenOrderThreeCentralRepresentative :=
  quotientProjection_section paperVanKampenOrderThreeCentralRepresentative

public theorem paperVanKampenOrderFourRegularCoverRepresentative_projects :
    regularFamilyCoverProjection Geometry.paperAnalyticData.periods
        paperVanKampenOrderFourRegularCoverRepresentative =
      paperVanKampenOrderFourCentralRepresentative :=
  quotientProjection_section paperVanKampenOrderFourCentralRepresentative

/-- Controlled paths in the regular vector-bundle cover.  Their outer projections transport the
same globally labelled lattice coefficient, avoiding an unspecified triangle-group monodromy. -/
@[expose] public noncomputable def paperVanKampenOrderThreeRegularCoverWhiskerLift :
    Path paperVanKampenInnerRepresentative
      paperVanKampenOrderThreeRegularCoverRepresentative := by
  let _ : PathConnectedSpace
      (RegularBase
          (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_pathConnected
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization
  exact PathConnectedSpace.somePath _ _

@[expose] public noncomputable def paperVanKampenOrderFourRegularCoverWhiskerLift :
    Path paperVanKampenInnerRepresentative
      paperVanKampenOrderFourRegularCoverRepresentative := by
  let _ : PathConnectedSpace
      (RegularBase
          (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_pathConnected
      Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization
  exact PathConnectedSpace.somePath _ _

/-- The controlled cover paths projected to paths between the selected representatives in the
regular torus family. -/
@[expose] public noncomputable def paperVanKampenOrderThreeRegularWhisker :
    Path paperVanKampenOuterRepresentative
      paperVanKampenOrderThreeCentralRepresentative :=
  (regularFamilyCoverWhisker Geometry.paperAnalyticData.periods
      paperVanKampenOrderThreeRegularCoverWhiskerLift).cast
    paperVanKampenInnerRepresentative_projects.symm
    paperVanKampenOrderThreeRegularCoverRepresentative_projects.symm

@[expose] public noncomputable def paperVanKampenOrderFourRegularWhisker :
    Path paperVanKampenOuterRepresentative
      paperVanKampenOrderFourCentralRepresentative :=
  (regularFamilyCoverWhisker Geometry.paperAnalyticData.periods
      paperVanKampenOrderFourRegularCoverWhiskerLift).cast
    paperVanKampenInnerRepresentative_projects.symm
    paperVanKampenOrderFourRegularCoverRepresentative_projects.symm

/-- Paths in the central family from the global van Kampen point to the two selected collar
points, projected from the controlled regular-cover paths above. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCentralWhisker :
    Path paperVanKampenCentralPoint
      (Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint) := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  exact (paperVanKampenOrderThreeRegularWhisker.map
    (regularFamilyQuotientMap Geometry.paperAnalyticData.periods).continuous).cast
      (quotientProjection_section paperVanKampenCentralPoint).symm
      paperVanKampenOrderThreeCentralRepresentative_projects.symm

@[expose] public noncomputable def paperVanKampenOrderFourCentralWhisker :
    Path paperVanKampenCentralPoint
      (Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint) := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  exact (paperVanKampenOrderFourRegularWhisker.map
    (regularFamilyQuotientMap Geometry.paperAnalyticData.periods).continuous).cast
      (quotientProjection_section paperVanKampenCentralPoint).symm
      paperVanKampenOrderFourCentralRepresentative_projects.symm

/-- The common-source collar identifications equate the selected central and filling points in
the actual four-piece glued carrier. -/
public theorem paperVanKampenOrderThreeCollarPoint_glued :
    paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint) =
      paperFourPieceStar.glueData.toGlueData.ι (some 1)
        paperVanKampenOrderThreeFillingPoint := by
  change Geometry.paperAnalyticData.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      none
        (Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint) =
    Geometry.paperAnalyticData.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 1)
        (Geometry.paperAnalyticData.starToFilling 1 paperVanKampenOrderThreeCollarPoint)
  exact Geometry.paperAnalyticData.openEmbeddingStarData
    |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
      1 paperVanKampenOrderThreeCollarPoint

public theorem paperVanKampenOrderFourCollarPoint_glued :
    paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint) =
      paperFourPieceStar.glueData.toGlueData.ι (some 2)
        paperVanKampenOrderFourFillingPoint := by
  change Geometry.paperAnalyticData.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      none
        (Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint) =
    Geometry.paperAnalyticData.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 2)
        (Geometry.paperAnalyticData.starToFilling 2 paperVanKampenOrderFourCollarPoint)
  exact Geometry.paperAnalyticData.openEmbeddingStarData
    |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
      2 paperVanKampenOrderFourCollarPoint

/-- The two embeddings of each common elliptic collar into the glued carrier. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarCentralToCarrier :
    C(Geometry.paperAnalyticData.starCollarSourceType 1, PaperGluedCarrier) :=
  ⟨fun x => paperFourPieceStar.glueData.toGlueData.ι none
      (Geometry.paperAnalyticData.starToCentral 1 x),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous.comp
      (Geometry.paperAnalyticData.starToCentral_isOpenEmbedding 1).continuous⟩

@[expose] public noncomputable def paperVanKampenOrderThreeCollarFillingToCarrier :
    C(Geometry.paperAnalyticData.starCollarSourceType 1, PaperGluedCarrier) :=
  ⟨fun x => paperFourPieceStar.glueData.toGlueData.ι (some 1)
      (Geometry.paperAnalyticData.starToFilling 1 x),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 1)).continuous.comp
      (Geometry.paperAnalyticData.starToFilling_isOpenEmbedding 1).continuous⟩

@[expose] public noncomputable def paperVanKampenOrderFourCollarCentralToCarrier :
    C(Geometry.paperAnalyticData.starCollarSourceType 2, PaperGluedCarrier) :=
  ⟨fun x => paperFourPieceStar.glueData.toGlueData.ι none
      (Geometry.paperAnalyticData.starToCentral 2 x),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous.comp
      (Geometry.paperAnalyticData.starToCentral_isOpenEmbedding 2).continuous⟩

@[expose] public noncomputable def paperVanKampenOrderFourCollarFillingToCarrier :
    C(Geometry.paperAnalyticData.starCollarSourceType 2, PaperGluedCarrier) :=
  ⟨fun x => paperFourPieceStar.glueData.toGlueData.ι (some 2)
      (Geometry.paperAnalyticData.starToFilling 2 x),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 2)).continuous.comp
      (Geometry.paperAnalyticData.starToFilling_isOpenEmbedding 2).continuous⟩

/-- The genuine order-three regular-family deck loop, included in the glued carrier and based at
the central image of the selected collar point. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarRegularDeckLoopToCarrier :
    Path
      (paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint))
      (paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 1 paperVanKampenOrderThreeCollarPoint)) :=
  (paperVanKampenOrderThreeCollarRegularDeckLoop.map
      paperVanKampenCentralToCarrier.continuous).cast
    (congrArg paperVanKampenCentralToCarrier
      paperVanKampenOrderThreeCentralRepresentative_projects).symm
    (congrArg paperVanKampenCentralToCarrier
      paperVanKampenOrderThreeCentralRepresentative_projects).symm

/-- The analogous included regular-family deck loop at the order-four collar. -/
@[expose] public noncomputable def paperVanKampenOrderFourCollarRegularDeckLoopToCarrier :
    Path
      (paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint))
      (paperFourPieceStar.glueData.toGlueData.ι none
        (Geometry.paperAnalyticData.starToCentral 2 paperVanKampenOrderFourCollarPoint)) :=
  (paperVanKampenOrderFourCollarRegularDeckLoop.map
      paperVanKampenCentralToCarrier.continuous).cast
    (congrArg paperVanKampenCentralToCarrier
      paperVanKampenOrderFourCentralRepresentative_projects).symm
    (congrArg paperVanKampenCentralToCarrier
      paperVanKampenOrderFourCentralRepresentative_projects).symm

/-- The central image of the common order-three collar loop is exactly the included genuine
regular-family deck loop. -/
public theorem paperVanKampenOrderThreeCollarDeckLoop_toCentralCarrier_eq :
    paperVanKampenOrderThreeCollarDeckLoop.map
        paperVanKampenOrderThreeCollarCentralToCarrier.continuous =
      paperVanKampenOrderThreeCollarRegularDeckLoopToCarrier := by
  apply Path.ext
  funext t
  exact congrArg paperVanKampenCentralToCarrier
    (congrArg (fun p => p t) paperVanKampenOrderThreeCollarDeckLoop_toCentral_eq)

/-- The central image of the common order-four collar loop is exactly the included genuine
regular-family deck loop. -/
public theorem paperVanKampenOrderFourCollarDeckLoop_toCentralCarrier_eq :
    paperVanKampenOrderFourCollarDeckLoop.map
        paperVanKampenOrderFourCollarCentralToCarrier.continuous =
      paperVanKampenOrderFourCollarRegularDeckLoopToCarrier := by
  apply Path.ext
  funext t
  exact congrArg paperVanKampenCentralToCarrier
    (congrArg (fun p => p t) paperVanKampenOrderFourCollarDeckLoop_toCentral_eq)

/-- The order-three common-source deck loop has literally the same path in the glued carrier
whether it is embedded through the central family or through the filling. -/
public theorem paperVanKampenOrderThreeCollarDeckLoop_maps_eq :
    paperVanKampenOrderThreeCollarDeckLoop.map
        paperVanKampenOrderThreeCollarCentralToCarrier.continuous =
      (paperVanKampenOrderThreeCollarDeckLoop.map
        paperVanKampenOrderThreeCollarFillingToCarrier.continuous).cast
          (Geometry.paperAnalyticData.openEmbeddingStarData
            |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
              1 paperVanKampenOrderThreeCollarPoint)
          (Geometry.paperAnalyticData.openEmbeddingStarData
            |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
              1 paperVanKampenOrderThreeCollarPoint) := by
  apply Path.ext
  funext t
  exact Geometry.paperAnalyticData.openEmbeddingStarData
    |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
      1 (paperVanKampenOrderThreeCollarDeckLoop t)

/-- The analogous literal path equality for the order-four collar. -/
public theorem paperVanKampenOrderFourCollarDeckLoop_maps_eq :
    paperVanKampenOrderFourCollarDeckLoop.map
        paperVanKampenOrderFourCollarCentralToCarrier.continuous =
      (paperVanKampenOrderFourCollarDeckLoop.map
        paperVanKampenOrderFourCollarFillingToCarrier.continuous).cast
          (Geometry.paperAnalyticData.openEmbeddingStarData
            |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
              2 paperVanKampenOrderFourCollarPoint)
          (Geometry.paperAnalyticData.openEmbeddingStarData
            |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
              2 paperVanKampenOrderFourCollarPoint) := by
  apply Path.ext
  funext t
  exact Geometry.paperAnalyticData.openEmbeddingStarData
    |>.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
      2 (paperVanKampenOrderFourCollarDeckLoop t)

/-- The central whiskers, transported into the glued carrier and across the literal collar
identifications. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCarrierWhisker :
    Path paperVanKampenBasepoint
      (paperFourPieceStar.glueData.toGlueData.ι (some 1)
        paperVanKampenOrderThreeFillingPoint) :=
  (paperVanKampenOrderThreeCentralWhisker.map
      paperVanKampenCentralToCarrier.continuous).cast rfl
    paperVanKampenOrderThreeCollarPoint_glued.symm

@[expose] public noncomputable def paperVanKampenOrderFourCarrierWhisker :
    Path paperVanKampenBasepoint
      (paperFourPieceStar.glueData.toGlueData.ι (some 2)
        paperVanKampenOrderFourFillingPoint) :=
  (paperVanKampenOrderFourCentralWhisker.map
      paperVanKampenCentralToCarrier.continuous).cast rfl
    paperVanKampenOrderFourCollarPoint_glued.symm

/-- The two affine filling pieces included into the actual glued carrier. -/
@[expose] public noncomputable def paperVanKampenOrderThreeFillingToCarrier :
    C(Geometry.paperAnalyticData.starFillingType 1, PaperGluedCarrier) :=
  ⟨paperFourPieceStar.glueData.toGlueData.ι (some 1),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 1)).continuous⟩

@[expose] public noncomputable def paperVanKampenOrderFourFillingToCarrier :
    C(Geometry.paperAnalyticData.starFillingType 2, PaperGluedCarrier) :=
  ⟨paperFourPieceStar.glueData.toGlueData.ι (some 2),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 2)).continuous⟩

/-- The actual collar-based elliptic meridian loops: travel from the global basepoint through the
central family to the common collar, traverse the shared affine cyclic deck loop, and return along
the same whisker. The loop can be viewed through either side of the collar by the path equalities
above. -/
@[expose] public noncomputable def paperVanKampenEllipticMeridianOneLoop :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  paperVanKampenOrderThreeCarrierWhisker.trans
    ((paperVanKampenOrderThreeCollarDeckLoop.map
      paperVanKampenOrderThreeCollarFillingToCarrier.continuous).trans
        paperVanKampenOrderThreeCarrierWhisker.symm)

@[expose] public noncomputable def paperVanKampenEllipticMeridianTwoLoop :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  paperVanKampenOrderFourCarrierWhisker.trans
    ((paperVanKampenOrderFourCollarDeckLoop.map
      paperVanKampenOrderFourCollarFillingToCarrier.continuous).trans
        paperVanKampenOrderFourCarrierWhisker.symm)

/-- Fundamental-group classes of the two actual affine filling meridians. -/
@[expose] public noncomputable def paperVanKampenEllipticMeridianOne :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  Path.Homotopic.Quotient.mk paperVanKampenEllipticMeridianOneLoop

@[expose] public noncomputable def paperVanKampenEllipticMeridianTwo :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  Path.Homotopic.Quotient.mk paperVanKampenEllipticMeridianTwoLoop

/-- A based version of the genuine regular-family `g₁` deck loop, transported from its collar
representative to the global cusp basepoint. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarBasedDeckMeridianLoop :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  paperVanKampenOrderThreeCarrierWhisker.trans
    ((paperVanKampenOrderThreeCollarRegularDeckLoopToCarrier.cast
      paperVanKampenOrderThreeCollarPoint_glued.symm
      paperVanKampenOrderThreeCollarPoint_glued.symm).trans
        paperVanKampenOrderThreeCarrierWhisker.symm)

/-- A based version of the genuine regular-family `g₂` deck loop, transported from its collar
representative to the global cusp basepoint. -/
@[expose] public noncomputable def paperVanKampenOrderFourCollarBasedDeckMeridianLoop :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  paperVanKampenOrderFourCarrierWhisker.trans
    ((paperVanKampenOrderFourCollarRegularDeckLoopToCarrier.cast
      paperVanKampenOrderFourCollarPoint_glued.symm
      paperVanKampenOrderFourCollarPoint_glued.symm).trans
        paperVanKampenOrderFourCarrierWhisker.symm)

/-- The based genuine `g₁` deck loop is pointwise the actual order-three affine filling
meridian. -/
public theorem paperVanKampenOrderThreeCollarBasedDeckMeridianLoop_eq :
    paperVanKampenOrderThreeCollarBasedDeckMeridianLoop =
      paperVanKampenEllipticMeridianOneLoop := by
  apply Path.ext
  funext t
  change
    (paperVanKampenOrderThreeCarrierWhisker.trans
      ((paperVanKampenOrderThreeCollarRegularDeckLoopToCarrier.cast
        paperVanKampenOrderThreeCollarPoint_glued.symm
        paperVanKampenOrderThreeCollarPoint_glued.symm).trans
          paperVanKampenOrderThreeCarrierWhisker.symm)) t =
      (paperVanKampenOrderThreeCarrierWhisker.trans
        ((paperVanKampenOrderThreeCollarDeckLoop.map
          paperVanKampenOrderThreeCollarFillingToCarrier.continuous).trans
            paperVanKampenOrderThreeCarrierWhisker.symm)) t
  rw [← paperVanKampenOrderThreeCollarDeckLoop_toCentralCarrier_eq]
  rw [paperVanKampenOrderThreeCollarDeckLoop_maps_eq]
  rfl

/-- The based genuine `g₂` deck loop is pointwise the actual order-four affine filling
meridian. -/
public theorem paperVanKampenOrderFourCollarBasedDeckMeridianLoop_eq :
    paperVanKampenOrderFourCollarBasedDeckMeridianLoop =
      paperVanKampenEllipticMeridianTwoLoop := by
  apply Path.ext
  funext t
  change
    (paperVanKampenOrderFourCarrierWhisker.trans
      ((paperVanKampenOrderFourCollarRegularDeckLoopToCarrier.cast
        paperVanKampenOrderFourCollarPoint_glued.symm
        paperVanKampenOrderFourCollarPoint_glued.symm).trans
          paperVanKampenOrderFourCarrierWhisker.symm)) t =
      (paperVanKampenOrderFourCarrierWhisker.trans
        ((paperVanKampenOrderFourCollarDeckLoop.map
          paperVanKampenOrderFourCollarFillingToCarrier.continuous).trans
            paperVanKampenOrderFourCarrierWhisker.symm)) t
  rw [← paperVanKampenOrderFourCollarDeckLoop_toCentralCarrier_eq]
  rw [paperVanKampenOrderFourCollarDeckLoop_maps_eq]
  rfl

/-- Fundamental-group classes of the two collar-based genuine deck meridians. -/
@[expose] public noncomputable def paperVanKampenOrderThreeCollarBasedDeckMeridian :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  Path.Homotopic.Quotient.mk paperVanKampenOrderThreeCollarBasedDeckMeridianLoop

@[expose] public noncomputable def paperVanKampenOrderFourCollarBasedDeckMeridian :
    FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint :=
  Path.Homotopic.Quotient.mk paperVanKampenOrderFourCollarBasedDeckMeridianLoop

/-- The actual filling meridian classes are precisely the collar-based `g₁` and `g₂` deck
classes. -/
public theorem paperVanKampenOrderThreeCollarBasedDeckMeridian_eq :
    paperVanKampenOrderThreeCollarBasedDeckMeridian =
      paperVanKampenEllipticMeridianOne := by
  exact congrArg Path.Homotopic.Quotient.mk
    paperVanKampenOrderThreeCollarBasedDeckMeridianLoop_eq

public theorem paperVanKampenOrderFourCollarBasedDeckMeridian_eq :
    paperVanKampenOrderFourCollarBasedDeckMeridian =
      paperVanKampenEllipticMeridianTwo := by
  exact congrArg Path.Homotopic.Quotient.mk
    paperVanKampenOrderFourCollarBasedDeckMeridianLoop_eq

/-- The fixed torus fibre maps through the two quotient stages and then into the central open
piece of the actual glued carrier. -/
@[expose] public noncomputable def paperVanKampenFiberToCarrier :
    C(PaperVanKampenFiberTorus, PaperGluedCarrier) :=
  ⟨fun q => paperFourPieceStar.glueData.toGlueData.ι none
      (fiberTorusToPuncturedGlobalFamily Geometry.paperAnalyticData.periods
        paperVanKampenRegularBasepoint q),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous.comp
      (fiberTorusToPuncturedGlobalFamily Geometry.paperAnalyticData.periods
        paperVanKampenRegularBasepoint).continuous⟩

/-- The distinguished point of the fixed torus fibre maps to the selected basepoint of the
glued carrier. -/
public theorem paperVanKampenFiberToCarrier_basepoint :
    paperVanKampenFiberToCarrier
        (torusProjection
          (regularParameterMap Geometry.paperAnalyticData.periods
            paperVanKampenRegularBasepoint).1
          paperVanKampenFiberPoint) =
      paperVanKampenBasepoint := by
  let _ := regularFamilyDeckAction Geometry.paperAnalyticData.periods
  change paperFourPieceStar.glueData.toGlueData.ι none
      (quotientProjection
        (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)
        (quotientProjection
          (M := RegularBase
              (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace)
          (G := FamilyPeriodGroup
            (regularParameterMap Geometry.paperAnalyticData.periods))
          paperVanKampenInnerRepresentative)) =
    paperFourPieceStar.glueData.toGlueData.ι none paperVanKampenCentralPoint
  congr 1
  calc
    quotientProjection
        (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)
        (quotientProjection
          (M := RegularBase
              (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace)
          (G := FamilyPeriodGroup
            (regularParameterMap Geometry.paperAnalyticData.periods))
          paperVanKampenInnerRepresentative) =
      quotientProjection
        (M := RegularTotalSpace Geometry.paperAnalyticData.periods) (G := Delta)
        paperVanKampenOuterRepresentative := by
          rw [show quotientProjection
              (M := RegularBase
                  (U := Geometry.paperAnalyticData.modular.modularParameter.toTriangleUniformization) ×
                ComplexTwoSpace)
              (G := FamilyPeriodGroup
                (regularParameterMap Geometry.paperAnalyticData.periods))
              paperVanKampenInnerRepresentative = paperVanKampenOuterRepresentative from
            quotientProjection_section paperVanKampenOuterRepresentative]
    _ = paperVanKampenCentralPoint :=
      quotientProjection_section paperVanKampenCentralPoint

/-- The actual rank-four lattice translation homomorphism in the fundamental group of the glued
carrier.  It is obtained from covering monodromy in the fixed torus fibre and functoriality of
the fundamental group through both quotient stages and the central-piece inclusion. -/
@[expose] public noncomputable def paperVanKampenTranslation :
    LatticeData.Lattice →+ Additive
      (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
  (FundamentalGroup.mapOfEq paperVanKampenFiberToCarrier
      paperVanKampenFiberToCarrier_basepoint).toAdditive.comp
    (fiberTorusTranslation Geometry.paperAnalyticData.periods
      paperVanKampenRegularBasepoint paperVanKampenFiberPoint)

/-- The concrete loop in the glued carrier obtained by projecting a straight period segment in
the chosen `ℂ²` fibre and including it through the central piece. -/
@[expose] public noncomputable def paperVanKampenTranslationLoop
    (a : LatticeData.Lattice) :
    Path paperVanKampenBasepoint paperVanKampenBasepoint :=
  ((fiberPeriodLoop Geometry.paperAnalyticData.periods
      paperVanKampenRegularBasepoint paperVanKampenFiberPoint a).map
        paperVanKampenFiberToCarrier.continuous).cast
    paperVanKampenFiberToCarrier_basepoint.symm
    paperVanKampenFiberToCarrier_basepoint.symm

/-- The fundamental-group class of the concrete straight-period loop. -/
@[expose] public noncomputable def paperVanKampenTranslationClass
    (a : LatticeData.Lattice) :
    Additive (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
  Additive.ofMul
    (Path.Homotopic.Quotient.mk (paperVanKampenTranslationLoop a))

/-- The actual lattice homomorphism used in the van Kampen presentation is represented by the
corresponding straight-period loop in the glued carrier. -/
public theorem paperVanKampenTranslation_apply_eq_class (a : LatticeData.Lattice) :
    paperVanKampenTranslation a = paperVanKampenTranslationClass a := by
  rw [paperVanKampenTranslation]
  change (FundamentalGroup.mapOfEq paperVanKampenFiberToCarrier
      paperVanKampenFiberToCarrier_basepoint).toAdditive
      (fiberTorusTranslation Geometry.paperAnalyticData.periods
        paperVanKampenRegularBasepoint paperVanKampenFiberPoint a) = _
  rw [fiberTorusTranslation_apply_eq_fiberPeriodClass]
  apply Additive.toMul.injective
  change (FundamentalGroup.mapOfEq paperVanKampenFiberToCarrier
      paperVanKampenFiberToCarrier_basepoint)
        (Path.Homotopic.Quotient.mk
          (fiberPeriodLoop Geometry.paperAnalyticData.periods
            paperVanKampenRegularBasepoint paperVanKampenFiberPoint a)) =
      Path.Homotopic.Quotient.mk (paperVanKampenTranslationLoop a)
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

/-- The exact remaining van Kampen input for the selected paper carrier can be supplied in the
unreduced lattice form appearing directly in Theorem 7.17.  The verified obstruction-one reduction
then produces `HasVanKampenData`; no separate no-extra-relations proof is required. -/
public theorem paperFourPieceStar_vanKampen_of_full_relations
    {μ : LatticeData.Lattice}
    (r : Topology.FullVanKampenRelations
      (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint)
      LatticeData.epsilon (-LatticeData.epsilon') μ)
    (hμ : LatticeData.gamma μ = 0)
    (hgenerate : Topology.FullVanKampenGeneratorsGenerate r) :
    Topology.HasVanKampenData PaperGluedCarrier 0 1 (-1) :=
  Topology.hasVanKampenData_of_full_relations_chosen
    paperVanKampenBasepoint r hμ hgenerate

/-- Once the two elliptic meridians are constructed, it is enough to verify the paper's relations
against the concrete fixed-fibre translation homomorphism above.  This version makes explicit that
the translation generator in the final van Kampen data is the actual loop homomorphism induced by
the selected torus fibre, rather than an arbitrary map supplied with the relations. -/
public theorem paperFourPieceStar_vanKampen_of_meridian_relations
    {μ : LatticeData.Lattice}
    (ρ₁ ρ₂ : FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint)
    (conjugate_one : ∀ a,
      ρ₁⁻¹ * Additive.toMul (paperVanKampenTranslation a) * ρ₁ =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₁.mulVec a)))
    (conjugate_two : ∀ a,
      ρ₂⁻¹ * Additive.toMul (paperVanKampenTranslation a) * ρ₂ =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₂.mulVec a)))
    (elliptic_one : ρ₁ ^ 3 =
      Additive.toMul (paperVanKampenTranslation LatticeData.epsilon))
    (elliptic_two : ρ₂ ^ 4 =
      Additive.toMul (paperVanKampenTranslation (-LatticeData.epsilon')))
    (cusp : ρ₁ * ρ₂ = Additive.toMul (paperVanKampenTranslation μ))
    (toric_vanishes : ∀ a, a 0 = 0 → a 1 = 0 →
      Additive.toMul (paperVanKampenTranslation a) = 1)
    (hμ : LatticeData.gamma μ = 0)
    (hgenerate : Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (paperVanKampenTranslation a)) ∪ {ρ₁, ρ₂}) = ⊤) :
    Topology.HasVanKampenData PaperGluedCarrier 0 1 (-1) := by
  let r : Topology.FullVanKampenRelations
      (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint)
      LatticeData.epsilon (-LatticeData.epsilon') μ :=
    { translation := paperVanKampenTranslation
      ρ₁ := ρ₁
      ρ₂ := ρ₂
      conjugate_one := conjugate_one
      conjugate_two := conjugate_two
      elliptic_one := elliptic_one
      elliptic_two := elliptic_two
      cusp := cusp
      toric_vanishes := toric_vanishes }
  apply paperFourPieceStar_vanKampen_of_full_relations r hμ
  exact hgenerate

/-- For the actual deck-meridian loops above, the remaining van Kampen task is exactly the
geometric verification of their monodromy, filling, cusp, and generation relations. -/
public theorem paperFourPieceStar_vanKampen_of_concrete_deck_meridian_relations
    {μ : LatticeData.Lattice}
    (conjugate_one : ∀ a,
      paperVanKampenDeckMeridianOne⁻¹ *
          Additive.toMul (paperVanKampenTranslation a) *
          paperVanKampenDeckMeridianOne =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₁.mulVec a)))
    (conjugate_two : ∀ a,
      paperVanKampenDeckMeridianTwo⁻¹ *
          Additive.toMul (paperVanKampenTranslation a) *
          paperVanKampenDeckMeridianTwo =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₂.mulVec a)))
    (elliptic_one : paperVanKampenDeckMeridianOne ^ 3 =
      Additive.toMul (paperVanKampenTranslation LatticeData.epsilon))
    (elliptic_two : paperVanKampenDeckMeridianTwo ^ 4 =
      Additive.toMul (paperVanKampenTranslation (-LatticeData.epsilon')))
    (cusp : paperVanKampenDeckMeridianOne * paperVanKampenDeckMeridianTwo =
      Additive.toMul (paperVanKampenTranslation μ))
    (toric_vanishes : ∀ a, a 0 = 0 → a 1 = 0 →
      Additive.toMul (paperVanKampenTranslation a) = 1)
    (hμ : LatticeData.gamma μ = 0)
    (hgenerate : Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (paperVanKampenTranslation a)) ∪
        {paperVanKampenDeckMeridianOne, paperVanKampenDeckMeridianTwo}) = ⊤) :
    Topology.HasVanKampenData PaperGluedCarrier 0 1 (-1) :=
  paperFourPieceStar_vanKampen_of_meridian_relations
    paperVanKampenDeckMeridianOne paperVanKampenDeckMeridianTwo
    conjugate_one conjugate_two elliptic_one elliptic_two cusp toric_vanishes hμ hgenerate

/-- Specialization of the van Kampen reduction to the actual collar-based affine filling
meridians.  Only their geometric relations and generation remain as inputs. -/
public theorem paperFourPieceStar_vanKampen_of_concrete_elliptic_meridian_relations
    {μ : LatticeData.Lattice}
    (conjugate_one : ∀ a,
      paperVanKampenEllipticMeridianOne⁻¹ *
          Additive.toMul (paperVanKampenTranslation a) *
          paperVanKampenEllipticMeridianOne =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₁.mulVec a)))
    (conjugate_two : ∀ a,
      paperVanKampenEllipticMeridianTwo⁻¹ *
          Additive.toMul (paperVanKampenTranslation a) *
          paperVanKampenEllipticMeridianTwo =
        Additive.toMul (paperVanKampenTranslation (LatticeData.A₂.mulVec a)))
    (elliptic_one : paperVanKampenEllipticMeridianOne ^ 3 =
      Additive.toMul (paperVanKampenTranslation LatticeData.epsilon))
    (elliptic_two : paperVanKampenEllipticMeridianTwo ^ 4 =
      Additive.toMul (paperVanKampenTranslation (-LatticeData.epsilon')))
    (cusp : paperVanKampenEllipticMeridianOne * paperVanKampenEllipticMeridianTwo =
      Additive.toMul (paperVanKampenTranslation μ))
    (toric_vanishes : ∀ a, a 0 = 0 → a 1 = 0 →
      Additive.toMul (paperVanKampenTranslation a) = 1)
    (hμ : LatticeData.gamma μ = 0)
    (hgenerate : Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (paperVanKampenTranslation a)) ∪
        {paperVanKampenEllipticMeridianOne, paperVanKampenEllipticMeridianTwo}) = ⊤) :
    Topology.HasVanKampenData PaperGluedCarrier 0 1 (-1) :=
  paperFourPieceStar_vanKampen_of_meridian_relations
    paperVanKampenEllipticMeridianOne paperVanKampenEllipticMeridianTwo
    conjugate_one conjugate_two elliptic_one elliptic_two cusp toric_vanishes hμ hgenerate

/-- The selected complex atlas on every piece of the paper star. -/
@[instance_reducible] public noncomputable def paperFourPieceStarComplexCharts :
    ∀ i, ChartedSpace ComplexModel (paperFourPieceStar.glueData.U i) :=
  Geometry.paperAnalyticData.fourPieceStarComplexCharts

/-- Every selected piece is a complex three-manifold in its concrete atlas. -/
public theorem paperFourPieceStar_pieceIsManifold :
    letI (i : Option (Fin 3)) := paperFourPieceStarComplexCharts i
    ∀ i : Option (Fin 3), IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (paperFourPieceStar.glueData.U i) :=
  Geometry.paperAnalyticData.fourPieceStar_pieceIsManifold

/-- Identify the central piece and three fillings with the four indices of the canonical cover. -/
@[expose] public def fourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The canonical cover of a star gluing by the open images of its four pieces. -/
@[expose] public noncomputable def FourPieceStarGluingData.openCover
    (A : FourPieceStarGluingData) : FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (fourPieceStarIndex i))
  isOpen_piece i := (A.glueData.ι_isOpenEmbedding (fourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

/-- The canonical cover stored by the gluing package is the same ordered star cover used by the
Section 7 Čech construction. -/
public theorem FourPieceStarGluingData.openCover_eq_sectionSevenStarOpenCover
    (A : FourPieceStarGluingData) :
    A.openCover = sectionSevenStarOpenCover A := by
  rfl

/-- All data required to assemble the paper's four pieces into a compact complex threefold with
the asserted fundamental group and integral homology. -/
public structure PaperGluingData where
  /-- The central family and three filling pieces, with their pairwise disjoint collar maps. -/
  star : FourPieceStarGluingData
  /-- Every piece is connected. -/
  connectedPiece : ∀ i, ConnectedSpace (star.glueData.U i)
  /-- Each of the three attaching collars is nonempty. -/
  nonemptyCentralCollar : ∀ i, Nonempty (star.centralCollar i)
  /-- The four pieces are complex manifolds and the collar maps are biholomorphic. -/
  biholomorphicStar :
    Geometry.EstablishedBiholomorphicStarGluing.BiholomorphicFourPieceStarData star
  /-- Every piece is second countable. -/
  pieceSecondCountable : ∀ i, SecondCountableTopology (star.glueData.U i)
  /-- The glued topology is Hausdorff. -/
  gluedT2 : T2Space (GluedSpace star.glueData)
  /-- The completed glued space is compact. -/
  gluedCompact : CompactSpace (GluedSpace star.glueData)
  /-- The selected filling twists give the required van Kampen presentation. -/
  vanKampen : Topology.HasVanKampenData (GluedSpace star.glueData) 0 1 (-1)
  /-- The paper-specific comparison from the verified finite Section 7 model to chains small with
  respect to the canonical open images of these four pieces. -/
  homologyComparison : SectionSevenFourPieceSmallChainComparison
    (GluedSpace star.glueData) star.openCover

/-- Package the already constructed analytic and compact topological star once the two genuinely
remaining global calculations have been supplied: van Kampen generation/relations and the
Section 7 intersection-chain identification.  In particular, this constructor does not ask again
for any collar, atlas, separation, compactness, or countability datum. -/
@[expose] public noncomputable def paperGluingDataOfRemainingTopologicalInputs
    (hVanKampen : Topology.HasVanKampenData PaperGluedCarrier 0 1 (-1))
    (hSectionSeven : SectionSevenPaperCoverIdentification paperFourPieceStar) :
    PaperGluingData where
  star := paperFourPieceStar
  connectedPiece := paperFourPieceStar_connectedPiece
  nonemptyCentralCollar := paperFourPieceStar_nonemptyCentralCollar
  biholomorphicStar := paperFourPieceStarBiholomorphicData
  pieceSecondCountable := paperFourPieceStar_pieceSecondCountable
  gluedT2 := paperFourPieceStar_gluedT2
  gluedCompact := paperFourPieceStar_gluedCompact
  vanKampen := hVanKampen
  homologyComparison := by
    rw [FourPieceStarGluingData.openCover_eq_sectionSevenStarOpenCover]
    exact hSectionSeven.toFourPieceSmallChainComparison

namespace PaperGluingData

variable (A : PaperGluingData)

/-- The canonical gluing diagram built from the central piece and three collars. -/
public abbrev D : TopCat.GlueData := A.star.glueData

/-- The complex atlases on the central piece and three filling pieces. -/
@[instance_reducible] public def complexCharts :
    ∀ i, ChartedSpace ComplexModel (A.D.U i) :=
  A.biholomorphicStar.complexCharts

/-- Biholomorphic collar gluing makes the transported piece atlases compatible. -/
public theorem complexCompatible :
    letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
    letI := A.complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) A.D :=
  Geometry.EstablishedBiholomorphicStarGluing.establishedFourPieceBiholomorphicGluingAtlasCompatible
    A.star A.nonemptyCentralCollar A.biholomorphicStar

/-- Countability of the four-piece gluing follows from countability of its pieces. -/
public theorem gluedSecondCountable : SecondCountableTopology (GluedSpace A.D) := by
  let _ : Countable A.D.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : A.D.J) := A.pieceSecondCountable i
  exact secondCountableTopology_gluedSpace A.D

/-- The standard open-cover Mayer--Vietoris theorem applies to all three stages of the paper's
four-piece cover. -/
public theorem mayerVietorisExactness : FourPieceMayerVietorisExactness A.star.openCover :=
  establishedFourPieceMayerVietorisExactness A.star.openCover

/-- The paper-specific small-chain comparison for the actual four-piece cover, together with
general open-cover subdivision and the established homology of the standard sphere, gives the
assembly layer's homology contract. -/
public theorem integralHomology : HasIntegralHomologyOfSixSphere (GluedSpace A.D) :=
  A.homologyComparison.hasIntegralHomologyOfSixSphere

/-- Restricting the glued complex atlas to real scalars supplies its smooth real
six-manifold atlas. -/
public theorem underlyingRealManifold :
    letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
    letI := A.connectedPiece
    letI := A.complexCharts
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ (GluedSpace A.D) inferInstance
      (underlyingRealChartedSpace (gluedChartedSpace A.D)) := by
  let _ := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
  let _ := A.connectedPiece
  let _ := A.complexCharts
  exact Geometry.EstablishedComplexToRealManifold.establishedUnderlyingRealIsManifold
    (gluedChartedSpace A.D) (isManifold_gluedChartedSpace A.D A.complexCompatible)

/-- Exact assembly of packaged gluing data into the completed-threefold contract. -/
@[expose] public noncomputable def toCompletedPaperThreefold : CompletedPaperThreefold := by
  let _ : Finite A.D.J := by
    change Finite (Option (Fin 3))
    infer_instance
  let _ : Nonempty A.D.J := by
    change Nonempty (Option (Fin 3))
    infer_instance
  let _ := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
  let _ := A.connectedPiece
  let _ := A.complexCharts
  let _ := A.gluedT2
  let _ := A.gluedSecondCountable
  exact completedPaperThreefoldOfGluing A.D A.complexCompatible A.underlyingRealManifold A.gluedCompact
    (A.star.intersectionGraphConnected A.nonemptyCentralCollar) A.vanKampen A.integralHomology

end PaperGluingData

/-- Constructing the exact packaged gluing data suffices for the completed paper threefold. -/
public theorem exists_completedPaperThreefold_of_paperGluingData
    (h : Nonempty PaperGluingData) : Nonempty CompletedPaperThreefold :=
  h.map PaperGluingData.toCompletedPaperThreefold

end

end SphereSixComplex
