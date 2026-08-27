module

public import SphereSixComplex.Topology.PaperCuspChosenAffineFilling

/-!
# The actual cusp-overlap map into the central family

This module records the literal collar chart before making any universal-cover choice.  Keeping
it below the affine-core construction lets that construction choose its basepoint over the
geometric cusp base rather than at an unrelated arbitrary point.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
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

/-- The canonical additive-cover point above the selected cusp-overlap base. -/
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

/-- The selected point of the actual central family at which cusp naturality is based. -/
public noncomputable def actualCuspCentralBase : A.CentralFamily :=
  A.actualCuspOverlapToCentral A.actualCuspOverlapBase

/-- The literal cusp chart is exactly the inclusion of the cusp overlap into the central
piece of the glued star. -/
@[simp]
public theorem centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
    (x : (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.actualCuspOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp x := by
  let q := A.cuspCollarToStarOverlapHomeomorph.symm x
  apply Subtype.ext
  calc
    ↑(A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.actualCuspOverlapToCentral x)) =
        A.openEmbeddingStarData.collarSourceToGlued 0 q := rfl
    _ = ↑(A.cuspCollarToStarOverlapHomeomorph q) :=
      (A.cuspCollarToStarOverlapHomeomorph_coe q).symm
    _ = x.1 := congrArg Subtype.val
      (A.cuspCollarToStarOverlapHomeomorph.apply_symm_apply x)

end SphereSixComplex.Geometry.PaperAnalyticData

end
