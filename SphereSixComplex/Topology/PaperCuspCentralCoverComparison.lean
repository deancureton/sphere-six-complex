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

/-- The exact cusp-overlap chart into the actual central family. -/
public noncomputable def actualCuspOverlapToCentral :
    C((A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace), A.CentralFamily) where
  toFun x := puncturedLocalCuspQuotientMap A.starCuspWitness
    (A.cuspCollarToStarOverlapHomeomorph.symm x)
  continuous_toFun :=
    (puncturedLocalCuspQuotientMap_continuous A.starCuspWitness).comp
      A.cuspCollarToStarOverlapHomeomorph.symm.continuous

/-- On the additive universal cover, the actual overlap chart is the already constructed
normalized map into the global cusp collar. -/
@[simp]
public theorem actualCuspOverlapToCentral_boundaryProjection
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.actualCuspOverlapToCentral (A.actualCuspBoundaryProjection p) =
      additiveCuspCoverToGlobal A.starCuspWitness p := by
  let q : A.openEmbeddingStarData.collarSource 0 :=
    additiveCuspBoundaryProjection A.starCuspWitness p
  change puncturedLocalCuspQuotientMap A.starCuspWitness
      (A.cuspCollarToStarOverlapHomeomorph.symm
        (A.cuspCollarToStarOverlapHomeomorph q)) = _
  rw [A.cuspCollarToStarOverlapHomeomorph.symm_apply_apply]
  change puncturedLocalCuspQuotientMap A.starCuspWitness
      (additiveCuspBoundaryProjection A.starCuspWitness p) = _
  exact puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
    A.starCuspWitness p

/-- A point of the selected central affine universal cover above the image of the actual cusp
base point. -/
public noncomputable def actualCuspBoundaryCoverBase :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  paperCuspBoundaryBasePreimage A.starCuspWitness A.actualCuspLocalBoundaryBase

@[simp]
public theorem actualCuspBoundaryCoverBase_projects :
    A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase =
      A.actualCuspOverlapBase := by
  change A.cuspCollarToStarOverlapHomeomorph
      (additiveCuspBoundaryProjection A.starCuspWitness
        (paperCuspBoundaryBasePreimage A.starCuspWitness
          A.actualCuspLocalBoundaryBase)) = A.actualCuspOverlapBase
  rw [additiveCuspBoundaryProjection_basePreimage]
  exact A.cuspCollarToStarOverlapHomeomorph.apply_symm_apply _

/-- A point of the selected central affine universal cover above the image of the actual cusp
base point. -/
public noncomputable def actualCuspCentralLiftPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose
    (D.data.quotientCovering.surjective
      (A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase)))

@[simp]
public theorem actualCuspCentralLiftPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.actualCuspCentralLiftPoint =
      A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase) := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective
      (A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase)))

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
    A.actualCuspCentralLiftPoint
    A.actualCuspCentralLiftPoint_projects

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

end SphereSixComplex.Geometry.PaperAnalyticData

end
