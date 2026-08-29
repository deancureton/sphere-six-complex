module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization
public import SphereSixComplex.Topology.PaperSectionSevenAffineActualCuspStripLift
public import SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving

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
public theorem exists_actualCuspAngularCoordinateLoop_mem_affineVerticalStrip :
    ∃ t : unitInterval,
      (A.actualCuspAngularCoordinateLoop t).1 ∈ sectionSevenAffineVerticalStrip := by
  obtain ⟨t, ht⟩ := A.exists_actualCuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  rw [sectionSevenAffineVerticalStrip]
  change (1 / 3 : ℝ) < ((A.actualCuspAngularCoordinateLoop t).1).re ∧
    ((A.actualCuspAngularCoordinateLoop t).1).re < 2 / 3
  rw [ht]
  norm_num

/-- The literal point of the actual cusp collar below the marked additive angular lift. -/
public noncomputable def actualCuspAngularCollarPoint (t : unitInterval) :
    A.openEmbeddingStarData.collarSource 0 :=
  additiveCuspBoundaryProjection A.starCuspWitness (A.actualCuspAngularLiftPoint t)

namespace SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

/-- The actual angular collar point enters the elliptic interior through its central piece. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage
    (t : unitInterval) :
    D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t) ∈
      A.sectionSevenEllipticCentralImage := by
  let q := A.actualCuspAngularCollarPoint t
  let y := A.cuspCollarToSectionSevenFinalOverlapHomeomorph q
  have hy : y.1 ∈
      (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := by
    rw [← A.sectionSevenFinalOverlap_eq_centralCuspIntersection]
    exact y.2
  change (A.cuspCollarToSectionSevenFinalOverlapHomeomorph q).1 ∈
    (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0
  exact hy.1

/-- In the central chart, the literal collar point has exactly the actual cusp-loop coordinate. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
    (t : unitInterval) :
    A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.centralFamilyCoordinate
        (A.actualCuspOverlapToCentral
          (A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint t))) := by
  unfold sectionSevenEllipticCentralCoordinate
  congr 1
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.actualCuspOverlapToCentral_boundaryProjection]
  have hglobal :
      additiveCuspCoverToGlobal A.starCuspWitness (A.actualCuspAngularLiftPoint t) =
        A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.actualCuspAngularLiftPoint t)) := by
    change additiveCuspCoverToGlobal A.starCuspWitness (A.actualCuspAngularLiftPoint t) =
      puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness
          (A.actualCuspAngularLiftPoint t))
    exact (puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
      A.starCuspWitness (A.actualCuspAngularLiftPoint t)).symm
  calc
    ↑↑(⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ :
          A.sectionSevenEllipticCentralImage) =
        A.openEmbeddingStarData.collarSourceToGlued 0
          (A.actualCuspAngularCollarPoint t) := rfl
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.actualCuspAngularLiftPoint t)))).1 :=
      (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (additiveCuspCoverToGlobal A.starCuspWitness
          (A.actualCuspAngularLiftPoint t))).1 := by rw [hglobal]

/-- Equivalently, that central coordinate is the explicit normalized cusp-coordinate loop. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop
    (t : unitInterval) :
    A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.actualCuspAngularCoordinateLoop t := by
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint]
  rfl

/-- At affine height `1/2`, the literal collar point lies in both concrete sides of the
pulled-back two-open cover. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2) :
    R.twoDiscCover.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t) ∈
      R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide := by
  let D := R.twoDiscCover
  let x : A.SectionSevenEllipticInterior :=
    D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t)
  have hxcentral : x ∈ A.sectionSevenEllipticCentralImage :=
    D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t
  have hheight : A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩ = 1 / 2 := by
    change (A.sectionSevenEllipticCentralCoordinate ⟨x, hxcentral⟩).1.re = 1 / 2
    rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop]
    exact ht
  change x ∈ A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
    A.sectionSevenActualAffineSplit.allocation.orderFourSide
  constructor
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩ < 2 / 3
      rw [hheight]
      norm_num, rfl⟩
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change 1 / 3 < A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩
      rw [hheight]
      norm_num, rfl⟩

/-- A concrete point of the actual cusp collar lies in the pulled-back cover intersection. -/
public theorem exists_actualCuspAngularCollarPoint_mem_pulledBackIntersection
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ∃ t : unitInterval,
      A.actualCuspAngularCollarPoint t ∈
        R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen := by
  obtain ⟨t, ht⟩ := A.exists_actualCuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  exact cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection R t ht

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
