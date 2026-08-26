module

public import SphereSixComplex.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Topology.PaperCuspCentralDeckComparison
public import SphereSixComplex.Topology.PaperCuspChosenAffineFilling

/-!
# The actual cusp-to-central universal-cover comparison

The base map in this file is the literal collar chart into the punctured global family.  Its
lift to the selected central universal cover, and the accompanying deck homomorphism, are
obtained from covering-space lifting and monodromy.  Thus the comparison itself carries no
independent naturality or generator-identification assumption.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The canonical comparison from the actual additive cusp cover to the selected central affine
universal cover.  Both the lift and its deck homomorphism are derived from the literal collar
map by the universal lifting property. -/
public noncomputable def actualCuspCentralCoverComparison :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData (G := paperCuspBoundaryDeck)
      (H := paperCentralFreeAffineDeck)
      A.actualCuspBoundaryProjection D.data.projection := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : LocallyPathConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    (additiveCuspRadiusCover_convex W.localWitness.radius
      W.localWitness.radius_pos).locallyPathConnectedSpace
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph)
    D.data.quotientCovering
    A.actualCuspOverlapToCentral
    A.actualCuspBoundaryCoverBase
    A.centralAffineUniversalCoverPoint
    (by
      rw [A.centralAffineUniversalCoverPoint_projects,
        actualCuspCentralBase, A.actualCuspBoundaryCoverBase_projects]
      rfl)

/-- The canonical comparison lift preserves the selected cover basepoints. -/
public theorem actualCuspCentralCoverComparison_lift_base :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    letI : LocallyPathConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      (additiveCuspRadiusCover_convex W.localWitness.radius
        W.localWitness.radius_pos).locallyPathConnectedSpace
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    A.actualCuspCentralCoverComparison.lift A.actualCuspBoundaryCoverBase =
      A.centralAffineUniversalCoverPoint := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : LocallyPathConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    (additiveCuspRadiusCover_convex W.localWitness.radius
      W.localWitness.radius_pos).locallyPathConnectedSpace
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  apply quotientCoverMapDataOfBaseMap_lift_base
  rw [A.centralAffineUniversalCoverPoint_projects,
    actualCuspCentralBase, A.actualCuspBoundaryCoverBase_projects]
  rfl

/-- The comparison square uses the actual cusp quotient projection and the actual central-family
projection. -/
public theorem actualCuspCentralCoverComparison_commutes
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    A.actualCuspOverlapToCentral (A.actualCuspBoundaryProjection p) =
      D.data.projection (A.actualCuspCentralCoverComparison.lift p) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  have hbase : A.actualCuspCentralCoverComparison.baseMap =
      A.actualCuspOverlapToCentral := by
    rfl
  rw [← hbase]
  exact A.actualCuspCentralCoverComparison.commutes p

/-- The lift is equivariant for the deck homomorphism induced by the actual collar map. -/
public theorem actualCuspCentralCoverComparison_equivariant
    (g : paperCuspBoundaryDeck)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    A.actualCuspCentralCoverComparison.lift (g • p) =
      A.actualCuspCentralCoverComparison.deckMap g •
        A.actualCuspCentralCoverComparison.lift p := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact A.actualCuspCentralCoverComparison.equivariant g p

/-- Covering monodromy computes the map induced by the actual cusp collar on every source deck
transformation.  This is the fundamental-group naturality statement before making any claim
about which marked element of the central affine deck group the transformation is. -/
public theorem actualCuspCentralCoverComparison_ofDeck
    (g : paperCuspBoundaryDeck) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.actualCuspCentralCoverComparison
    let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨C.lift A.actualCuspBoundaryCoverBase, rfl⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.actualCuspBoundaryCoverBase)
          (ofDeck hp A.actualCuspBoundaryCoverBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.actualCuspCentralCoverComparison
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality hp D.data.quotientCovering C
      A.actualCuspBoundaryCoverBase
      (ofDeck hp A.actualCuspBoundaryCoverBase g)).symm

/-- Based form of the cover naturality theorem at the actual overlap and selected central
basepoints. -/
public theorem actualCuspCentralCoverComparison_ofDeck_actualBase
    (g : paperCuspBoundaryDeck) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral
          (by
            rw [A.actualCuspBoundaryCoverBase_projects]
            exact A.centralAffineBase_eq_actualCuspCentralBase.symm)
          (ofDeck hp A.actualCuspBoundaryCoverBase g)) =
      MulOpposite.op (A.actualCuspCentralCoverComparison.deckMap g) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let C := A.actualCuspCentralCoverComparison
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
      (FundamentalGroup.mapOfEq C.baseMap _
        (ofDeck hp A.actualCuspBoundaryCoverBase g)) =
    MulOpposite.op (C.deckMap g)
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality_of_lift_eq
      hp D.data.quotientCovering C A.actualCuspBoundaryCoverBase
      A.centralAffineUniversalCoverPoint
      A.actualCuspCentralCoverComparison_lift_base
      (ofDeck hp A.actualCuspBoundaryCoverBase g)).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end
