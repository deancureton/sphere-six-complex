module

public import SphereSixComplex.Topology.EstablishedChosenAffineFillings
public import SphereSixComplex.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Topology.PaperCuspActualAffineFillingCoverSquare
public import SphereSixComplex.Topology.PaperCuspUnwrappedFillingCover

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
open StandardInfiniteA2ToricModel CuspFilling CuspLocalPhaseAction
open CuspPeriodExpansion CuspPhaseEstimates.CuspPeriodExpansion
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
public def actualCuspOverlapBase :
    (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
      Set A.VanKampenSpace) :=
  ⟨A.actualVanKampenFourPieceCover.cuspPoint,
    A.actualVanKampenFourPieceCover.cuspPoint_mem⟩

/-- The prescribed cusp point regarded as a point of the actual cusp piece. -/
public def actualCuspFillingBase : A.actualVanKampenFourPieceCover.cusp :=
  ⟨A.actualVanKampenFourPieceCover.cuspPoint,
    A.actualVanKampenFourPieceCover.cuspPoint_mem.2⟩

/-- The local boundary base point corresponding to the prescribed star-overlap base point. -/
public noncomputable def actualCuspLocalBoundaryBase :
    puncturedLocalCuspQuotient A.starCuspWitness :=
  A.cuspCollarToStarOverlapHomeomorph.symm A.actualCuspOverlapBase

/-- The unwrapped cusp cover transported to the exact overlap and filling piece of the glued
star. -/
public noncomputable def actualCuspStarUnwrappedFillingCover :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    letI := paperCuspFillingDeckAction A.starCuspWitness
    UnwrappedToricFillingCover Lattice paperToricSubgroup paperCuspBoundaryDeck
      (additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
      (LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius)
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.cusp paperCuspBoundaryDeckData := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  exact {
    boundaryProjection := A.actualCuspBoundaryProjection
    fillingProjection := A.actualCuspFillingProjectionToStar
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
    baseMap := A.actualCuspOverlapToFillingPiece
    commutes := A.actualCuspCoverSquare_commutes
    equivariant := additiveCuspFillingLift_paperCuspBoundaryDeck_smul W
    base := paperCuspBoundaryBasePreimage W A.actualCuspLocalBoundaryBase
  }

/-- The actual cusp affine filling, bundled with its chosen cover and deck groups. -/
public noncomputable def actualCuspChosenAffineFillingCover :
    ChosenToricFillingCoverModel Lattice paperToricSubgroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.cusp where
  BoundaryDeck := paperCuspBoundaryDeck
  FillingDeck := paperCuspBoundaryDeckData.FillingDeck
  BoundaryCover := additiveCuspRadiusCover A.starCuspWitness.localWitness.radius
  FillingCover := LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius
  boundaryDeckGroup := inferInstance
  fillingDeckGroup := inferInstance
  boundaryCoverTopology := inferInstance
  fillingCoverTopology := inferInstance
  boundaryAction := paperCuspBoundaryDeckAction A.starCuspWitness
  fillingAction := paperCuspFillingDeckAction A.starCuspWitness
  model := by
    let _ := paperCuspBoundaryDeckAction A.starCuspWitness
    let _ := paperCuspFillingDeckAction A.starCuspWitness
    exact A.actualCuspStarUnwrappedFillingCover.toToricFillingCoverModel

/-- The chosen cover base projects to the prescribed central--cusp overlap point. -/
public theorem actualCuspChosenAffineFillingCover_boundaryBase_eq :
    A.actualCuspChosenAffineFillingCover.boundaryBase = A.actualCuspOverlapBase := by
  change A.actualCuspBoundaryProjection
      (paperCuspBoundaryBasePreimage A.starCuspWitness A.actualCuspLocalBoundaryBase) =
    A.actualCuspOverlapBase
  change A.cuspCollarToStarOverlapHomeomorph
      (additiveCuspBoundaryProjection A.starCuspWitness
        (paperCuspBoundaryBasePreimage A.starCuspWitness A.actualCuspLocalBoundaryBase)) =
    A.actualCuspOverlapBase
  rw [additiveCuspBoundaryProjection_basePreimage]
  exact A.cuspCollarToStarOverlapHomeomorph.apply_symm_apply A.actualCuspOverlapBase

/-- The chosen filling base is the prescribed cusp-piece point. -/
public theorem actualCuspChosenAffineFillingCover_fillingBase_eq :
    A.actualCuspChosenAffineFillingCover.fillingBase = A.actualCuspFillingBase := by
  change A.actualCuspOverlapToFillingPiece
      A.actualCuspChosenAffineFillingCover.boundaryBase = A.actualCuspFillingBase
  rw [A.actualCuspChosenAffineFillingCover_boundaryBase_eq]
  rfl

/-- The chosen cover carries the actual cusp-overlap inclusion on fundamental groups. -/
public theorem actualCuspChosenAffineFillingCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspChosenAffineFillingCover_fillingBase_eq
        A.actualCuspChosenAffineFillingCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  exact fundamentalGroupHomOfBaseEq_map
    A.actualVanKampenFourPieceCover.cuspOverlapToPiece
    A.actualCuspChosenAffineFillingCover_boundaryBase_eq
    A.actualCuspChosenAffineFillingCover_fillingBase_eq

end SphereSixComplex.Geometry.PaperAnalyticData

end
