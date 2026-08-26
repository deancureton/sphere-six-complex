module

public import SphereSixComplex.Topology.PaperCuspFillingDeckAction

/-!
# The actual unwrapped cusp filling cover

The normalized additive cusp coordinates and the local infinite `A₂` toric carrier form the
simply connected cover square used by the toric filling fundamental-group calculation.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.StandardInfiniteA2ToricModel

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- A selected preimage in the normalized additive cover of a prescribed boundary base point. -/
public noncomputable def paperCuspBoundaryBasePreimage
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    additiveCuspRadiusCover W.localWitness.radius := by
  let _ := paperCuspBoundaryDeckAction W
  exact Classical.choose
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap W).surjective b)

@[simp]
public theorem additiveCuspBoundaryProjection_basePreimage
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    additiveCuspBoundaryProjection W (paperCuspBoundaryBasePreimage W b) = b := by
  let _ := paperCuspBoundaryDeckAction W
  exact Classical.choose_spec
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap W).surjective b)

/-- The actual cusp collar and its toric filling as a simply connected unwrapped cover square. -/
public noncomputable def paperCuspUnwrappedFillingCover
    (W : ActualPuncturedCuspCollarWitness N M) (b : puncturedLocalCuspQuotient W) :
    letI := paperCuspBoundaryDeckAction W
    letI := paperCuspFillingDeckAction W
    UnwrappedToricFillingCover Lattice paperToricSubgroup paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius)
      (LocalCarrier M W.localWitness.radius)
      (puncturedLocalCuspQuotient W) (actualLocalCuspFilling W)
      paperCuspBoundaryDeckData := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  exact {
    boundaryProjection := additiveCuspBoundaryProjection W
    fillingProjection := actualCuspFillingProjection W
    boundaryQuotient := additiveCuspBoundaryProjection_isQuotientCoveringMap W
    fillingQuotient := actualCuspFillingProjection_isQuotientCoveringMap_fillingDeck W
    boundarySimplyConnected := additiveCuspBoundaryCover_simplyConnected W
    fillingSimplyConnected :=
      M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
    lift := additiveCuspFillingLift W
    baseMap :=
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
    commutes := additiveCuspCoverSquare_commutes W
    equivariant := additiveCuspFillingLift_paperCuspBoundaryDeck_smul W
    base := paperCuspBoundaryBasePreimage W b
  }

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end
