module

public import SphereSixComplex.Paper.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Paper.Topology.PaperCuspCentralDeckComparison
public import SphereSixComplex.Paper.Topology.PaperCuspChosenAffineFilling

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
public noncomputable def cuspCentralCoverComparison :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData (G := paperCuspBoundaryDeck)
      (H := paperCentralFreeAffineDeck)
      A.cuspBoundaryProjection D.data.projection := by
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
    A.cuspOverlapToCentral
    A.cuspBoundaryCoverBase
    A.centralAffineUniversalCoverPoint
    (by
      rw [A.centralAffineUniversalCoverPoint_projects,
        cuspCentralBase, A.cuspBoundaryCoverBase_projects]
      rfl)

/-- The canonical comparison lift preserves the selected cover basepoints. -/
public theorem cuspCentralCoverComparison_lift_base :
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
    A.cuspCentralCoverComparison.lift A.cuspBoundaryCoverBase =
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
    cuspCentralBase, A.cuspBoundaryCoverBase_projects]
  rfl

/-- The comparison square uses the actual cusp quotient projection and the actual central-family
projection. -/
public theorem cuspCentralCoverComparison_commutes
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    A.cuspOverlapToCentral (A.cuspBoundaryProjection p) =
      D.data.projection (A.cuspCentralCoverComparison.lift p) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  have hbase : A.cuspCentralCoverComparison.baseMap =
      A.cuspOverlapToCentral := by
    rfl
  rw [← hbase]
  exact A.cuspCentralCoverComparison.commutes p

/-- The lift is equivariant for the deck homomorphism induced by the actual collar map. -/
public theorem cuspCentralCoverComparison_equivariant
    (g : paperCuspBoundaryDeck)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    A.cuspCentralCoverComparison.lift (g • p) =
      A.cuspCentralCoverComparison.deckMap g •
        A.cuspCentralCoverComparison.lift p := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact A.cuspCentralCoverComparison.equivariant g p

/-- Covering monodromy computes the map induced by the actual cusp collar on every source deck
transformation.  This is the fundamental-group naturality statement before making any claim
about which marked element of the central affine deck group the transformation is. -/
public theorem cuspCentralCoverComparison_ofDeck
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
    let C := A.cuspCentralCoverComparison
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨C.lift A.cuspBoundaryCoverBase, rfl⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.cuspBoundaryCoverBase)
          (ofDeck hp A.cuspBoundaryCoverBase g)) =
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
  let C := A.cuspCentralCoverComparison
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  simpa using
    (QuotientCoverMapData.fundamentalGroupEquiv_natural hp D.data.quotientCovering C
      A.cuspBoundaryCoverBase
      (ofDeck hp A.cuspBoundaryCoverBase g)).symm

/-- Based form of the cover naturality theorem at the actual overlap and selected central
basepoints. -/
public theorem cuspCentralCoverComparison_ofDeck_actualBase
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
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        (FundamentalGroup.mapOfEq A.cuspOverlapToCentral
          (by
            rw [A.cuspBoundaryCoverBase_projects]
            exact A.centralAffineBase_eq_actualCuspCentralBase.symm)
          (ofDeck hp A.cuspBoundaryCoverBase g)) =
      MulOpposite.op (A.cuspCentralCoverComparison.deckMap g) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let C := A.cuspCentralCoverComparison
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
      (FundamentalGroup.mapOfEq C.baseMap _
        (ofDeck hp A.cuspBoundaryCoverBase g)) =
    MulOpposite.op (C.deckMap g)
  simpa using
    (QuotientCoverMapData.fundamentalGroupEquiv_natural_of_lift_eq
      hp D.data.quotientCovering C A.cuspBoundaryCoverBase
      A.centralAffineUniversalCoverPoint
      A.cuspCentralCoverComparison_lift_base
      (ofDeck hp A.cuspBoundaryCoverBase g)).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end
