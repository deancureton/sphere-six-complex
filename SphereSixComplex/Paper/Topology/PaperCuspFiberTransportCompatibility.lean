module

public import
  SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished
public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport



@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily

variable {A : PaperAnalyticData}

public def centralFamilyToEllipticInteriorMap (A : PaperAnalyticData) :
    C(A.CentralFamily, A.ellipticInterior) :=
  ⟨fun x ↦ (A.ellipticCentralImageHomeomorph.symm x).1,
    continuous_subtype_val.comp A.ellipticCentralImageHomeomorph.symm.continuous⟩

public theorem centralFamilyToEllipticInteriorMap_band (A : PaperAnalyticData)
    (c : centralHeightBand (A.affineCentralHeightSplit
      A.affineCentralSeparation).height
      (A.affineCentralHeightSplit A.affineCentralSeparation).lower
      (A.affineCentralHeightSplit A.affineCentralSeparation).upper) :
    A.centralFamilyToEllipticInteriorMap
      (A.affineCentralBandToCentralFamily A.affineCentralSeparation c) =
      c.1 := by
  change (A.ellipticCentralImageHomeomorph.symm
    (A.ellipticCentralImageHomeomorph _)).1 = _
  rw [Homeomorph.symm_apply_apply]
  rfl

public def affineContractibleStripCenter : affineVerticalStrip :=
  let _ := affineVerticalStrip_contractibleSpace
  (ContractibleSpace.hequiv_unit affineVerticalStrip).some.invFun ()

namespace EllipticTwoDiscCoverData

public theorem actualCuspWangFiberToBand_centralFamily_fixed
    (R : A.AffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let b := actualCuspWangFiberToBandMap (A := A) R y
    let c := A.actualAffineHeightSplit.sidesIntersectionHomeomorph b
    A.affineCentralBandToCentralFamily
        A.affineCentralSeparation c =
      A.regularFixedFiberPoint
        (A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
        (fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let b :
      (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
        Set A.ellipticInterior) :=
    actualCuspWangFiberToBandMap (A := A) R y
  let c : centralHeightBand
      (A.affineCentralHeightSplit
        A.affineCentralSeparation).height
      (A.affineCentralHeightSplit
        A.affineCentralSeparation).lower
      (A.affineCentralHeightSplit
        A.affineCentralSeparation).upper :=
    A.actualAffineHeightSplit.sidesIntersectionHomeomorph b
  dsimp only
  have hcentral :
      A.affineCentralBandToCentralFamily
          A.affineCentralSeparation c =
        A.starToCentral 0
          ((actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R y).1) := by
    apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
    apply Subtype.ext
    change
      (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticCentralImageHomeomorph _)).1 =
      (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0 _)).1
    rw [A.centralToSectionSevenEulerPiece_centralImage]
    calc
      _ = b.1.1 := rfl
      _ = A.openEmbeddingStarData.collarSourceToGlued 0
          ((actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R y).1) := rfl
      _ = _ := (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
  rw [hcentral]
  obtain ⟨w, hw⟩ := Quotient.exists_rep y
  let t := actualCuspFullFiberCrossingTime A
  let p := A.cuspAngularLiftPoint t
  have hs : ‖cuspQ p.1.2‖ < A.starCuspWitness.localWitness.radius := p.2
  let zeta := (collarFiberEquiv A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness) p.1.2).symm w
  let q : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
    ⟨(zeta, p.1.2), hs⟩
  have hzeta : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2 zeta = w :=
    (collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) p.1.2).apply_symm_apply w
  have hw' : additiveTorusProjection
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 w = y := hw
  have hslice := actualCuspFullFiberSlice_additiveTorusProjection
    (A := A) p.1.2 hs zeta
  rw [hzeta, hw'] at hslice
  change actualCuspFullFiberSlice (A := A) p.1.2 hs y =
    additiveCuspBoundaryProjection A.starCuspWitness q at hslice
  have hintersection :
      ((actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R y).1) =
        additiveCuspBoundaryProjection A.starCuspWitness q := hslice
  rw [hintersection]
  have hcoordinate :
      fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y) =
        Quotient.mk _ (A.regularMovingToFixed
          (A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime) zeta) := by
    change fullRankAdditiveTorusHomeomorph
        G.fiberParameter A.duplicatedSectionSevenBandParameter
        G.fiberFullRank A.duplicatedSectionSevenBandFullRank y = _
    rw [← hw]
    change Quotient.mk _
        (A.duplicatedSectionSevenBandFullRank.realEquiv
          (G.fiberFullRank.realEquiv.symm w)) =
      Quotient.mk _ (A.regularMovingToFixed
        (A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime) zeta)
    apply congrArg (Quotient.mk _)
    change A.duplicatedSectionSevenBandFullRank.realEquiv
        (G.fiberFullRank.realEquiv.symm w) =
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (A.cuspAngularRegularBasePoint
          A.affineActualCuspCrossingTime, zeta)).2
    calc
      _ = A.duplicatedSectionSevenBandFullRank.realEquiv
          (G.fiberFullRank.realEquiv.symm
            (collarFiberEquiv A.cuspCoordinate
              (markedCuspParameter A.starCuspWitness) p.1.2 zeta)) := by
        rw [hzeta]
      _ = _ := by
        change A.duplicatedSectionSevenBandFullRank.realEquiv
            ((fullRankDomain (cuspBasePoint A.cuspCoordinate
              (markedCuspParameter A.starCuspWitness))).realEquiv.symm
                (collarFiberEquiv A.cuspCoordinate
                  (markedCuspParameter A.starCuspWitness) p.1.2 zeta)) = _
        rw [collarFiberEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
        rfl
  rw [hcoordinate]
  change A.starToCentral 0 _ = A.regularFixedFiberCover _ (A.regularMovingToFixed _ zeta)
  rw [regularFixedFiberCover, A.regularFixedToMoving_regularMovingToFixed]
  change puncturedLocalCuspQuotientMap A.starCuspWitness
      (additiveCuspBoundaryProjection A.starCuspWitness q) =
    A.centralQuotientProjection
      (projection (regularParameterMap A.periods)
        (A.cuspAngularRegularBasePoint
          A.affineActualCuspCrossingTime, zeta))
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  rfl


public theorem actualCuspWangFiberToEllipticInteriorMap_eq_fixed
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((⟨Subtype.val, continuous_subtype_val⟩ :
      C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.ellipticInterior), A.ellipticInterior)).comp
      (actualCuspWangFiberToBandMap (A := A) R)) =
    A.centralFamilyToEllipticInteriorMap.comp
      ((A.regularFixedFiberMap
        (A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)).comp
        ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
          R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro y
  have h := congrArg A.centralFamilyToEllipticInteriorMap
    (actualCuspWangFiberToBand_centralFamily_fixed R y)
  exact (A.centralFamilyToEllipticInteriorMap_band _).symm.trans h

public theorem canonicalCuspFiberToEllipticInteriorMap_eq_fixed
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap =
    A.centralFamilyToEllipticInteriorMap.comp
      ((A.regularFixedFiberMap
        (A.affineNamedStripLift.lift affineContractibleStripCenter)).comp
        ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
          R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro y
  have h := congrArg A.centralFamilyToEllipticInteriorMap
    (A.affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
      A.affineCentralSeparation
      (affineContractibleStripCenter,
        R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph y))
  exact (A.centralFamilyToEllipticInteriorMap_band _).symm.trans h

public theorem actualCuspWangFiberToEllipticInteriorMap_homotopic_fixed_canonical
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.ellipticInterior), A.ellipticInterior)).comp
        (actualCuspWangFiberToBandMap (A := A) R))
      R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspWangFiberToEllipticInteriorMap_eq_fixed,
    canonicalCuspFiberToEllipticInteriorMap_eq_fixed]
  exact ContinuousMap.Homotopic.comp (.refl A.centralFamilyToEllipticInteriorMap)
    (ContinuousMap.Homotopic.comp (A.regularFixedFiberMap_homotopic _ _) (.refl _))

end EllipticTwoDiscCoverData
end SphereSixComplex.Geometry.PaperAnalyticData
