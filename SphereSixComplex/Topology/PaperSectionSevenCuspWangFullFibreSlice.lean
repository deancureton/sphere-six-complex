module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationGeometry

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

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- Every point of the actual cusp collar enters the elliptic interior through its central
piece. -/
public theorem cuspToEllipticInteriorMap_mem_centralImage
    (q : A.openEmbeddingStarData.collarSource 0) :
    D.cuspToEllipticInteriorMap q ∈ A.sectionSevenEllipticCentralImage := by
  let y := A.cuspCollarToSectionSevenFinalOverlapHomeomorph q
  have hy : y.1 ∈
      (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := by
    rw [← A.sectionSevenFinalOverlap_eq_centralCuspIntersection]
    exact y.2
  change (A.cuspCollarToSectionSevenFinalOverlapHomeomorph q).1 ∈
    (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0
  exact hy.1

/-- The central coordinate of an arbitrary additive cusp-cover point is computed before the
quotient by the explicit additive-to-global map. -/
public theorem sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (additiveCuspBoundaryProjection A.starCuspWitness p)⟩ =
      A.centralFamilyCoordinate
        (A.actualCuspOverlapToCentral (A.actualCuspBoundaryProjection p)) := by
  unfold sectionSevenEllipticCentralCoordinate
  congr 1
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.actualCuspOverlapToCentral_boundaryProjection]
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
          A.sectionSevenEllipticCentralImage) =
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
    (A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (additiveCuspBoundaryProjection A.starCuspWitness p)⟩).1 =
      A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift p.1.2) := by
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint,
    A.actualCuspOverlapToCentral_boundaryProjection]
  rfl

/-- Every period point over affine height `1/2` lies in both concrete sides of the pulled-back
two-open cover. -/
public theorem cuspToEllipticInteriorMap_additivePoint_mem_sideIntersection
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
    (hp : (A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift p.1.2)).re =
      1 / 2) :
    R.twoDiscCover.cuspToEllipticInteriorMap
        (additiveCuspBoundaryProjection A.starCuspWitness p) ∈
      R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide := by
  let D := R.twoDiscCover
  let x : A.SectionSevenEllipticInterior :=
    D.cuspToEllipticInteriorMap (additiveCuspBoundaryProjection A.starCuspWitness p)
  have hxcentral : x ∈ A.sectionSevenEllipticCentralImage :=
    D.cuspToEllipticInteriorMap_mem_centralImage _
  have hheight : A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩ = 1 / 2 := by
    change (A.sectionSevenEllipticCentralCoordinate ⟨x, hxcentral⟩).1.re = 1 / 2
    rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint_fst]
    exact hp
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

/-- The fibre over a fixed normalized cusp parameter, written in the marked real-period
coordinates of the radial mapping-torus presentation. -/
public noncomputable def actualCuspFullFibreSlice (s : ℂ)
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
public theorem actualCuspFullFibreSlice_additiveTorusProjection
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    actualCuspFullFibreSlice (A := A) s hs
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
        (actualCuspFullFibreSlice (A := A) s hs _) =
    puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness)
        (collarPeriodPointMap A.starCuspWitness ⟨(zeta, s), hs⟩)
  rw [puncturedLocalCuspQuotientHomeomorph_apply]
  unfold actualCuspFullFibreSlice
  change (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
      (markedCuspParameter A.starCuspWitness))
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
        (markedCuspParameter A.starCuspWitness)).symm _) = _
  exact ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness)).apply_symm_apply _).trans (by rfl)

/-- At a middle-height crossing, every point of the four-torus slice lies in the pulled-back
intersection, not merely the single marked additive point used by the pointwise argument. -/
public theorem actualCuspFullFibreSlice_mem_pulledBackIntersection
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let p := A.actualCuspAngularLiftPoint t
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspFullFibreSlice (A := A) p.1.2 p.2 y ∈
      R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen := by
  let p := A.actualCuspAngularLiftPoint t
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  obtain ⟨w, hw⟩ := Quotient.exists_rep y
  let zeta := (collarFiberEquiv A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness) p.1.2).symm w
  have hs : ‖cuspQ p.1.2‖ < A.starCuspWitness.localWitness.radius := by
    exact p.2
  let q : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
    ⟨(zeta, p.1.2), hs⟩
  have hslice := actualCuspFullFibreSlice_additiveTorusProjection
    (A := A) p.1.2 hs zeta
  have hzeta : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2 zeta = w :=
    (collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2).apply_symm_apply w
  have hw' : additiveTorusProjection
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 w = y := hw
  rw [hzeta, hw'] at hslice
  change actualCuspFullFibreSlice (A := A) p.1.2 hs y =
    additiveCuspBoundaryProjection A.starCuspWitness q at hslice
  dsimp only at ⊢
  rw [hslice]
  change R.twoDiscCover.cuspToEllipticInteriorMap
      (additiveCuspBoundaryProjection A.starCuspWitness q) ∈
    R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide
  apply cuspToEllipticInteriorMap_additivePoint_mem_sideIntersection R q
  change (A.modular.sourceCoordinate.coordinate
    (A.cuspCoordinate.lift p.1.2)).re = 1 / 2
  rw [A.actualCuspAngularCoordinateLoop_apply t] at ht
  exact ht

/-- The continuous full four-torus slice, corestricted to the pulled-back cover intersection. -/
public noncomputable def actualCuspFullFibreIntersectionSlice
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) := by
  let p := A.actualCuspAngularLiftPoint t
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact ⟨fun y ↦ ⟨actualCuspFullFibreSlice (A := A) p.1.2 p.2 y,
      actualCuspFullFibreSlice_mem_pulledBackIntersection (A := A) R t ht y⟩,
    (actualCuspFullFibreSlice (A := A) p.1.2 p.2).continuous.subtype_mk _⟩

/-- The crossing slice induces a map on first integral homology of the pulled-back
intersection. -/
public noncomputable def actualCuspFullFibreIntersectionHomologyOne
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 1
    (actualCuspFullFibreIntersectionSlice (A := A) R t ht)

/-- Transport the induced full-fibre map from the pulled-back intersection to the actual
elliptic band. -/
public noncomputable def actualCuspFullFibreToBandHomologyOne
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1
        (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp
    (actualCuspFullFibreIntersectionHomologyOne (A := A) R t ht)

/-- A selected middle-height crossing of the actual angular cusp loop. -/
public noncomputable def actualCuspFullFibreCrossingTime (A : PaperAnalyticData) :
    unitInterval :=
  Classical.choose A.exists_actualCuspAngularCoordinateLoop_re_eq_half

/-- The selected full-fibre crossing lies at affine height `1/2`. -/
public theorem actualCuspFullFibreCrossingTime_spec (A : PaperAnalyticData) :
    ((A.actualCuspAngularCoordinateLoop
      (actualCuspFullFibreCrossingTime A)).1).re = 1 / 2 :=
  Classical.choose_spec A.exists_actualCuspAngularCoordinateLoop_re_eq_half

/-- The canonical candidate for the fibre-to-intersection map in the chain-realization
interface, obtained by taking the entire fibre at the selected middle-height crossing. -/
public noncomputable def actualCuspWangFibreToCuspCoverIntersectionMap
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) :=
  actualCuspFullFibreIntersectionSlice (A := A) R
    (actualCuspFullFibreCrossingTime A)
    (actualCuspFullFibreCrossingTime_spec A)

/-- The first-homology map induced by the selected full-fibre intersection slice. -/
public noncomputable def actualCuspWangFibreToCuspCoverIntersectionHomologyOne
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 1
    (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)

/-- The induced full-fibre map after transport to the actual elliptic band. -/
public noncomputable def actualCuspWangFibreToBandHomologyOne
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1
        (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp
    (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R)

/-- The full-fibre slice supplies the map field of the chain realization.  Consequently, the
remaining inputs are exactly the period-marked band identification and the oriented Wang
boundary comparison. -/
public noncomputable def actualCuspWangOpenCoverChainRealization_of_fullFibreSlice
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hBand : R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R)
    (hBoundary :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
          (actualCuspWangBoundaryHom A) =
        R.twoDiscCover.cuspOpenCoverConnectingHom) :
    R.twoDiscCover.ActualCuspWangOpenCoverChainRealization where
  fiberToCuspCoverIntersectionMap :=
    actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R
  fiberToBand_homology := hBand
  wangBoundary_eq_chainConnecting := hBoundary

/-- The full-fibre slice induces a map on first integral singular homology of the actual cusp
collar before any attempted corestriction to the pulled-back intersection. -/
public noncomputable def actualCuspFullFibreSliceHomologyOne
    (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 1
    (actualCuspFullFibreSlice (A := A) s hs)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
