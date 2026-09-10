module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineActualCuspStripLift
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# Geometric position of the actual cusp meridian

The logarithmic lift of the actual cusp meridian gains exactly `2πi`.  Hence its normalized
central coordinate crosses the affine vertical strip used by the Section 7 two-open cover.
-/

@[expose] public section

noncomputable section

open Set Metric Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The explicit actual cusp meridian meets the precise affine overlap strip. -/
public theorem exists_cuspAngularCoordinateLoop_mem_affineVerticalStrip :
    ∃ t : unitInterval,
      (A.cuspAngularCoordinateLoop t).1 ∈ affineVerticalStrip := by
  obtain ⟨t, ht⟩ := A.exists_cuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  rw [affineVerticalStrip]
  change (1 / 3 : ℝ) < ((A.cuspAngularCoordinateLoop t).1).re ∧
    ((A.cuspAngularCoordinateLoop t).1).re < 2 / 3
  rw [ht]
  norm_num

/-- The literal point of the actual cusp collar below the marked additive angular lift. -/
public noncomputable def cuspAngularCollarPoint (t : unitInterval) :
    A.openEmbeddingStarData.collarSource 0 :=
  additiveCuspBoundaryProjection A.starCuspWitness (A.cuspAngularLiftPoint t)

namespace EllipticTwoDiscCoverData

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

/-- The actual angular collar point enters the elliptic interior through its central piece. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage
    (t : unitInterval) :
    D.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t) ∈
      A.ellipticCentralImage := by
  let q := A.cuspAngularCollarPoint t
  let y := A.cuspCollarToSectionSevenFinalOverlapHomeomorph q
  have hy : y.1 ∈
      (A.openEmbeddingStarData.sectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 := by
    rw [← A.cuspAttachmentOverlap_eq_centralCuspIntersection]
    exact y.2
  change (A.cuspCollarToSectionSevenFinalOverlapHomeomorph q).1 ∈
    (A.openEmbeddingStarData.sectionSevenEulerCover).piece 0
  exact hy.1

/-- In the central chart, the literal collar point has exactly the actual cusp-loop coordinate. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
    (t : unitInterval) :
    A.ellipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.centralFamilyCoordinate
        (A.cuspOverlapToCentral
          (A.cuspBoundaryProjection (A.cuspAngularLiftPoint t))) := by
  unfold ellipticCentralCoordinate
  congr 1
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.cuspOverlapToCentral_boundaryProjection]
  have hglobal :
      additiveCuspCoverToGlobal A.starCuspWitness (A.cuspAngularLiftPoint t) =
        A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.cuspAngularLiftPoint t)) := by
    change additiveCuspCoverToGlobal A.starCuspWitness (A.cuspAngularLiftPoint t) =
      puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness
          (A.cuspAngularLiftPoint t))
    exact (puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
      A.starCuspWitness (A.cuspAngularLiftPoint t)).symm
  calc
    ↑↑(⟨D.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ :
          A.ellipticCentralImage) =
        A.openEmbeddingStarData.collarSourceToGlued 0
          (A.cuspAngularCollarPoint t) := rfl
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.cuspAngularLiftPoint t)))).1 :=
      (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (additiveCuspCoverToGlobal A.starCuspWitness
          (A.cuspAngularLiftPoint t))).1 := by rw [hglobal]

/-- Equivalently, that central coordinate is the explicit normalized cusp-coordinate loop. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop
    (t : unitInterval) :
    A.ellipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.cuspAngularCoordinateLoop t := by
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint]
  rfl

/-- At affine height `1/2`, the literal collar point lies in both concrete sides of the
pulled-back two-open cover. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection
    (R : A.AffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.cuspAngularCoordinateLoop t).1).re = 1 / 2) :
    R.twoDiscCover.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t) ∈
      R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide := by
  let D := R.twoDiscCover
  let x : A.ellipticInterior :=
    D.cuspToEllipticInteriorMap (A.cuspAngularCollarPoint t)
  have hxcentral : x ∈ A.ellipticCentralImage :=
    D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t
  have hheight : A.ellipticCentralHeight ⟨x, hxcentral⟩ = 1 / 2 := by
    change (A.ellipticCentralCoordinate ⟨x, hxcentral⟩).1.re = 1 / 2
    rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop]
    exact ht
  change x ∈ A.actualAffineHeightSplit.allocation.orderThreeSide ∩
    A.actualAffineHeightSplit.allocation.orderFourSide
  constructor
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change A.ellipticCentralHeight ⟨x, hxcentral⟩ < 2 / 3
      rw [hheight]
      norm_num, rfl⟩
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change 1 / 3 < A.ellipticCentralHeight ⟨x, hxcentral⟩
      rw [hheight]
      norm_num, rfl⟩

/-- A concrete point of the actual cusp collar lies in the pulled-back cover intersection. -/
public theorem exists_actualCuspAngularCollarPoint_mem_pulledBackIntersection
    (R : A.AffineRadialCompletionInput) :
    ∃ t : unitInterval,
      A.cuspAngularCollarPoint t ∈
        R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen := by
  obtain ⟨t, ht⟩ := A.exists_cuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  exact cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection R t ht

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
