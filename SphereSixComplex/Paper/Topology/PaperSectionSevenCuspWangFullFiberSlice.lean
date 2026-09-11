module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# A full-fibre slice in the pulled-back cusp cover

The pointwise cusp-crossing argument extends to the whole four-torus fibre because the affine
base coordinate is independent of the additive period coordinate.  This file constructs the
resulting continuous slice and records its induced first-homology map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace Topology
open scoped ContinuousMap
open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- Every point of the actual cusp collar enters the elliptic interior through its central
piece. -/
public theorem cuspToEllipticInteriorMap_mem_centralImage
    (q : A.openEmbeddingStarData.collarSource 0) :
    D.cuspToEllipticInteriorMap q ∈ A.ellipticCentralImage := by
  let y := A.cuspCollarToSectionSevenFinalOverlapHomeomorph q
  have hy : y.1 ∈
      (A.openEmbeddingStarData.sectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 := by
    rw [← A.cuspAttachmentOverlap_eq_centralCuspIntersection]
    exact y.2
  change (A.cuspCollarToSectionSevenFinalOverlapHomeomorph q).1 ∈
    (A.openEmbeddingStarData.sectionSevenEulerCover).piece 0
  exact hy.1

/-- The central coordinate of an arbitrary additive cusp-cover point is computed before the
quotient by the explicit additive-to-global map. -/
public theorem sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.ellipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (additiveCuspBoundaryProjection A.starCuspWitness p)⟩ =
      A.centralFamilyCoordinate
        (A.cuspOverlapToCentral (A.cuspBoundaryProjection p)) := by
  unfold ellipticCentralCoordinate
  congr 1
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.cuspOverlapToCentral_boundaryProjection]
  have hglobal :
      additiveCuspCoverToGlobal A.starCuspWitness p =
        A.starToCentral 0 (additiveCuspBoundaryProjection A.starCuspWitness p) := by
    change additiveCuspCoverToGlobal A.starCuspWitness p =
      puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness p)
    exact (puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
      A.starCuspWitness p).symm
  calc
    ↑↑(⟨D.cuspToEllipticInteriorMap
        (additiveCuspBoundaryProjection A.starCuspWitness p),
      D.cuspToEllipticInteriorMap_mem_centralImage
        (additiveCuspBoundaryProjection A.starCuspWitness p)⟩ :
          A.ellipticCentralImage) =
        A.openEmbeddingStarData.collarSourceToGlued 0
          (additiveCuspBoundaryProjection A.starCuspWitness p) := rfl
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness p))).1 :=
      (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (additiveCuspCoverToGlobal A.starCuspWitness p)).1 := by rw [hglobal]

/-- In particular, the affine base coordinate is independent of the additive period vector. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint_fst
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    (A.ellipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (additiveCuspBoundaryProjection A.starCuspWitness p)⟩).1 =
      A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift p.1.2) := by
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint,
    A.cuspOverlapToCentral_boundaryProjection]
  rfl

/-- Every period point over affine height `1/2` lies in both concrete sides of the pulled-back
two-open cover. -/
public theorem cuspToEllipticInteriorMap_additivePoint_mem_sideIntersection
    (R : A.AffineRadialCompletionInput)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
    (hp : (A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift p.1.2)).re =
      1 / 2) :
    R.twoDiscCover.cuspToEllipticInteriorMap
        (additiveCuspBoundaryProjection A.starCuspWitness p) ∈
      R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide := by
  let D := R.twoDiscCover
  let x : A.ellipticInterior :=
    D.cuspToEllipticInteriorMap (additiveCuspBoundaryProjection A.starCuspWitness p)
  have hxcentral : x ∈ A.ellipticCentralImage :=
    D.cuspToEllipticInteriorMap_mem_centralImage _
  have hheight : A.ellipticCentralHeight ⟨x, hxcentral⟩ = 1 / 2 := by
    change (A.ellipticCentralCoordinate ⟨x, hxcentral⟩).1.re = 1 / 2
    rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint_fst]
    exact hp
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

/-- The fibre over a fixed normalized cusp parameter, written in the marked real-period
coordinates of the radial mapping-torus presentation. -/
public noncomputable def actualCuspFullFiberSlice (s : ℂ)
    (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.openEmbeddingStarData.collarSource 0) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData
    A.starCuspWitness
  letI := G.fiberTopology
  let rho : OpenRadialInterval A.starCuspWitness.localWitness.radius :=
    ⟨‖cuspQ s‖, norm_cuspQ_pos s, hs⟩
  let realSlice : C(G.Fiber, RealMappingTorus G.clutching) :=
    ⟨fun y ↦ Quotient.mk (realMappingTorusSetoid G.clutching) (s.re, y),
      continuous_quot_mk.comp (continuous_const.prodMk continuous_id)⟩
  let totalInverse : C(
      OpenRadialInterval A.starCuspWitness.localWitness.radius ×
        CircleMappingTorus G.clutching,
      A.openEmbeddingStarData.collarSource 0) :=
    ⟨G.totalHomeomorph.symm, G.totalHomeomorph.symm.continuous⟩
  let realQuotientHomeomorph : C(RealMappingTorus G.clutching,
      CircleMappingTorus G.clutching) :=
    ⟨realMappingTorusHomeomorph G.clutching,
      (realMappingTorusHomeomorph G.clutching).continuous⟩
  let slice := totalInverse.comp
    ((ContinuousMap.const G.Fiber rho).prodMk
      (realQuotientHomeomorph.comp realSlice))
  letI := A.actualCuspRadialClutchingData.fiberTopology
  exact slice

/-- On a represented period point, the full-fibre slice is the literal additive cusp
projection at the chosen normalized base parameter. -/
public theorem actualCuspFullFiberSlice_additiveTorusProjection
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    actualCuspFullFiberSlice (A := A) s hs
        (additiveTorusProjection
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1
          (collarFiberEquiv A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness) s zeta)) =
      additiveCuspBoundaryProjection A.starCuspWitness ⟨(zeta, s), hs⟩ := by
  apply (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness)).injective
  change puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness)
        (actualCuspFullFiberSlice (A := A) s hs _) =
    puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness)
        (collarPeriodPointMap A.starCuspWitness ⟨(zeta, s), hs⟩)
  rw [puncturedLocalCuspQuotientHomeomorph_apply]
  unfold actualCuspFullFiberSlice
  change (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness))
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
        (markedCuspParameter A.starCuspWitness)).symm _) = _
  exact ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness)).apply_symm_apply _).trans (by rfl)

/-- At a middle-height crossing, every point of the four-torus slice lies in the pulled-back
intersection, not merely the single marked additive point used by the pointwise argument. -/
public theorem actualCuspFullFiberSlice_mem_pulledBackIntersection
    (R : A.AffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.cuspAngularCoordinateLoop t).1).re = 1 / 2)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let p := A.cuspAngularLiftPoint t
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspFullFiberSlice (A := A) p.1.2 p.2 y ∈
      R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen := by
  let p := A.cuspAngularLiftPoint t
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  obtain ⟨w, hw⟩ := Quotient.exists_rep y
  let zeta := (collarFiberEquiv A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness) p.1.2).symm w
  have hs : ‖cuspQ p.1.2‖ < A.starCuspWitness.localWitness.radius := by
    exact p.2
  let q : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
    ⟨(zeta, p.1.2), hs⟩
  have hslice := actualCuspFullFiberSlice_additiveTorusProjection
    (A := A) p.1.2 hs zeta
  have hzeta : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2 zeta = w :=
    (collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2).apply_symm_apply w
  have hw' : additiveTorusProjection
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 w = y := hw
  rw [hzeta, hw'] at hslice
  change actualCuspFullFiberSlice (A := A) p.1.2 hs y =
    additiveCuspBoundaryProjection A.starCuspWitness q at hslice
  dsimp only at ⊢
  rw [hslice]
  change R.twoDiscCover.cuspToEllipticInteriorMap
      (additiveCuspBoundaryProjection A.starCuspWitness q) ∈
    R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide
  apply cuspToEllipticInteriorMap_additivePoint_mem_sideIntersection R q
  change (A.modular.sourceCoordinate.coordinate
    (A.cuspCoordinate.lift p.1.2)).re = 1 / 2
  rw [A.cuspAngularCoordinateLoop_apply t] at ht
  exact ht

/-- The continuous full four-torus slice, corestricted to the pulled-back cover intersection. -/
public noncomputable def actualCuspFullFiberIntersectionSlice
    (R : A.AffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.cuspAngularCoordinateLoop t).1).re = 1 / 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) := by
  let p := A.cuspAngularLiftPoint t
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact ⟨fun y ↦ ⟨actualCuspFullFiberSlice (A := A) p.1.2 p.2 y,
      actualCuspFullFiberSlice_mem_pulledBackIntersection (A := A) R t ht y⟩,
    (actualCuspFullFiberSlice (A := A) p.1.2 p.2).continuous.subtype_mk _⟩



/-- A selected middle-height crossing of the actual angular cusp loop. -/
public noncomputable def actualCuspFullFiberCrossingTime (A : PaperAnalyticData) :
    unitInterval :=
  Classical.choose A.exists_cuspAngularCoordinateLoop_re_eq_half

/-- The selected full-fibre crossing lies at affine height `1/2`. -/
public theorem actualCuspFullFiberCrossingTime_spec (A : PaperAnalyticData) :
    ((A.cuspAngularCoordinateLoop
      (actualCuspFullFiberCrossingTime A)).1).re = 1 / 2 :=
  Classical.choose_spec A.exists_cuspAngularCoordinateLoop_re_eq_half

/-- The canonical candidate for the fibre-to-intersection map in the chain-realization
interface, obtained by taking the entire fibre at the selected middle-height crossing. -/
public noncomputable def actualCuspWangFiberToCuspCoverIntersectionMap
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) :=
  actualCuspFullFiberIntersectionSlice (A := A) R
    (actualCuspFullFiberCrossingTime A)
    (actualCuspFullFiberCrossingTime_spec A)





end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
