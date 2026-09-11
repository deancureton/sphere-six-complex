module

public import SphereSixComplex.Prerequisites.Topology.EstablishedChosenAffineFillings
public import SphereSixComplex.Paper.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Paper.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Paper.Topology.PaperCuspUnwrappedFillingCover

/-!
# The chosen affine filling cover for the actual cusp piece

The local unwrapped cusp cover is transported to the exact central--cusp overlap and cusp piece
of the glued analytic star, with the prescribed van Kampen cusp point as its boundary base.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex ComplexTorus CuspPuncturedCollarBridge
open InfiniteA2Toric CuspFilling CuspLocalPhaseAction
open CuspPeriodExpansion
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

private theorem fundamentalGroupHomOfBaseEq_map
    {B N : Type*} [TopologicalSpace B] [TopologicalSpace N]
    (f : C(B, N)) {b b' : B} (hb : b = b') (hn : f b = f b') :
    fundamentalGroupHomOfBaseEq hb hn (FundamentalGroup.map f b) =
      FundamentalGroup.map f b' := by
  subst b'
  rfl

/-- The prescribed cusp point regarded as a point of the actual central--cusp overlap. -/
public def cuspOverlapBase :
    (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
      Set A.VanKampenSpace) :=
  ⟨A.actualVanKampenFourPieceCover.cuspPoint,
    A.actualVanKampenFourPieceCover.cuspPoint_mem⟩

/-- The prescribed cusp point regarded as a point of the actual cusp piece. -/
public def cuspFillingBase : A.actualVanKampenFourPieceCover.cusp :=
  ⟨A.actualVanKampenFourPieceCover.cuspPoint,
    A.actualVanKampenFourPieceCover.cuspPoint_mem.2⟩

/-- The local boundary base point corresponding to the prescribed star-overlap base point. -/
public noncomputable def cuspLocalBoundaryBase :
    PuncturedLocalCuspQuotient A.starCuspWitness :=
  A.cuspCollarToStarOverlapHomeomorph.symm A.cuspOverlapBase

/-- The unwrapped cusp cover transported to the exact overlap and filling piece of the glued
star. -/
public noncomputable def cuspStarUnwrappedFillingCover :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    letI := paperCuspFillingDeckAction A.starCuspWitness
    UnwrappedToricFillingCover Lattice paperToricSubgroup PaperCuspBoundaryDeck
      (additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
      (localCarrier A.toricModel A.starCuspWitness.localWitness.radius)
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.cusp paperCuspBoundaryDeckData := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  exact {
    boundaryProjection := A.cuspBoundaryProjection
    fillingProjection := A.cuspFillingProjectionToStar
    boundaryQuotient :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    fillingQuotient :=
      (actualCuspFillingProjection_isQuotientCoveringMap_fillingDeck W).homeomorph_comp
        A.cuspFillingToStarPieceHomeomorph
    boundarySimplyConnected := additiveCuspBoundaryCover_simplyConnected W
    fillingSimplyConnected :=
      A.toricModel.localCarrierSimplyConnected W.localWitness.radius
        W.localWitness.radius_pos
    lift := additiveCuspFillingLift W
    baseMap := A.cuspOverlapToFillingPiece
    commutes := A.cuspCoverSquare_commutes
    equivariant := additiveCuspFillingLift_paperCuspBoundaryDeck_smul W
    base := paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase
  }

/-- The actual cusp affine filling, bundled with its chosen cover and deck groups. -/
public noncomputable def cuspChosenAffineFillingCover :
    ChosenToricFillingCoverModel Lattice paperToricSubgroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.cusp where
  BoundaryDeck := PaperCuspBoundaryDeck
  FillingDeck := paperCuspBoundaryDeckData.FillingDeck
  BoundaryCover := additiveCuspRadiusCover A.starCuspWitness.localWitness.radius
  FillingCover := localCarrier A.toricModel A.starCuspWitness.localWitness.radius
  boundaryDeckGroup := inferInstance
  fillingDeckGroup := inferInstance
  boundaryCoverTopology := inferInstance
  fillingCoverTopology := inferInstance
  boundaryAction := paperCuspBoundaryDeckAction A.starCuspWitness
  fillingAction := paperCuspFillingDeckAction A.starCuspWitness
  model := by
    let _ := paperCuspBoundaryDeckAction A.starCuspWitness
    let _ := paperCuspFillingDeckAction A.starCuspWitness
    exact A.cuspStarUnwrappedFillingCover.toToricFillingCoverModel

/-- The chosen cover base projects to the prescribed central--cusp overlap point. -/
public theorem cuspChosenAffineFillingCover_boundaryBase_eq :
    A.cuspChosenAffineFillingCover.boundaryBase = A.cuspOverlapBase := by
  change A.cuspBoundaryProjection
      (paperCuspBoundaryBasePreimage A.starCuspWitness A.cuspLocalBoundaryBase) =
    A.cuspOverlapBase
  change A.cuspCollarToStarOverlapHomeomorph
      (additiveCuspBoundaryProjection A.starCuspWitness
        (paperCuspBoundaryBasePreimage A.starCuspWitness A.cuspLocalBoundaryBase)) =
    A.cuspOverlapBase
  rw [additiveCuspBoundaryProjection_basePreimage]
  exact A.cuspCollarToStarOverlapHomeomorph.apply_symm_apply A.cuspOverlapBase

/-- After transport to the prescribed overlap base, the chosen lattice loop is the loop attached
to the corresponding deck translation of the actual additive cusp cover. -/
public theorem cuspChosenAffineFillingCover_translation_eq_ofDeck
    (a : Lattice) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        PaperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (Additive.toMul (A.cuspChosenAffineFillingCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (ofDeck hp
          (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
          (Additive.toMul (paperCuspBoundaryTranslation a))) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      PaperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let C := A.cuspChosenAffineFillingCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw :
      Additive.toMul (A.cuspChosenAffineFillingCover.translation a) =
        ofDeck hp (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
          (Additive.toMul (paperCuspBoundaryTranslation a)) := by
    apply (hp.fundamentalGroupEquiv
      ⟨paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact A.cuspChosenAffineFillingCover.fundamentalGroupData.translation_deck a
  change fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      (Additive.toMul (A.cuspChosenAffineFillingCover.translation a)) =
    fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      (ofDeck hp (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
        (Additive.toMul (paperCuspBoundaryTranslation a)))
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq) hraw

/-- After transport to the prescribed overlap base, the chosen angular meridian is the loop
attached to the actual cusp deck meridian. -/
public theorem cuspChosenAffineFillingCover_meridian_eq_ofDeck :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        PaperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspChosenAffineFillingCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (ofDeck hp (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
          paperCuspBoundaryMeridian) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      PaperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let C := A.cuspChosenAffineFillingCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : A.cuspChosenAffineFillingCover.meridian =
      ofDeck hp (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
        paperCuspBoundaryMeridian := by
    apply (hp.fundamentalGroupEquiv
      ⟨paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact A.cuspChosenAffineFillingCover.fundamentalGroupData.meridian_deck
  change fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover.meridian =
    fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      (ofDeck hp (paperCuspBoundaryBasePreimage W A.cuspLocalBoundaryBase)
        paperCuspBoundaryMeridian)
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq) hraw

/-- The chosen filling base is the prescribed cusp-piece point. -/
public theorem cuspChosenAffineFillingCover_fillingBase_eq :
    A.cuspChosenAffineFillingCover.fillingBase = A.cuspFillingBase := by
  change A.cuspOverlapToFillingPiece
      A.cuspChosenAffineFillingCover.boundaryBase = A.cuspFillingBase
  rw [A.cuspChosenAffineFillingCover_boundaryBase_eq]
  rfl

/-- The chosen cover carries the actual cusp-overlap inclusion on fundamental groups. -/
public theorem cuspChosenAffineFillingCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspChosenAffineFillingCover_fillingBase_eq
        A.cuspChosenAffineFillingCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  exact fundamentalGroupHomOfBaseEq_map
    A.actualVanKampenFourPieceCover.cuspOverlapToPiece
    A.cuspChosenAffineFillingCover_boundaryBase_eq
    A.cuspChosenAffineFillingCover_fillingBase_eq

end SphereSixComplex.Geometry.PaperAnalyticData

end
