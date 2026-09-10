module

public import
  SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

/-!
# Canonical cusp-fibre-to-band compatibility reduction

These legacy band-coordinate comparisons require explicit agreement between the normalized
strip lift and the selected cusp crossing. Compatibility after inclusion into the elliptic
interior is proved independently by full-fibre transport in `PaperCuspFiberTransportCompatibility`.
-/

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

namespace EllipticTwoDiscCoverData

private theorem actualCuspWangFiberToBand_centralFamily_completion
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
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
      A.stripLiftPoint A.affineNamedStripLift
        A.affineActualCuspCrossingPoint
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
          (A.affineNamedStripLift.lift
            A.affineActualCuspCrossingPoint) zeta) := by
    change fullRankAdditiveTorusHomeomorph
        G.fiberParameter A.duplicatedSectionSevenBandParameter
        G.fiberFullRank A.duplicatedSectionSevenBandFullRank y = _
    rw [← hw]
    change Quotient.mk _
        (A.duplicatedSectionSevenBandFullRank.realEquiv
          (G.fiberFullRank.realEquiv.symm w)) =
      Quotient.mk _ (A.regularMovingToFixed
        (A.affineNamedStripLift.lift
          A.affineActualCuspCrossingPoint) zeta)
    apply congrArg (Quotient.mk _)
    rw [hmark]
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
  rw [A.stripLiftPoint_regularMovingToFixed]
  rw [hmark]
  change puncturedLocalCuspQuotientMap A.starCuspWitness
      (additiveCuspBoundaryProjection A.starCuspWitness q) =
    A.centralQuotientProjection
      (projection (regularParameterMap A.periods)
        (A.cuspAngularRegularBasePoint
          A.affineActualCuspCrossingTime, zeta))
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  rfl

/-- The actual middle-height cusp slice has exactly the canonical marked band coordinate. -/
public theorem actualCuspWangFiberToBandMap_coordinate
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.bandHomotopyEquiv.toFun.comp
        (actualCuspWangFiberToBandMap (A := A) R) =
      ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
        R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩ := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro y
  let b :
      (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior) :=
    (actualCuspWangFiberToBandMap (A := A) R) y
  let c : centralHeightBand
      (A.affineCentralHeightSplit A.affineCentralSeparation).height
      (A.affineCentralHeightSplit A.affineCentralSeparation).lower
      (A.affineCentralHeightSplit A.affineCentralSeparation).upper :=
    A.actualAffineHeightSplit.sidesIntersectionHomeomorph b
  change
    (A.affineCentralBandMarkedProductHomeomorph
      A.affineCentralSeparation c).2 =
    fullRankAdditiveTorusHomeomorph
      G.fiberParameter A.duplicatedSectionSevenBandParameter
      G.fiberFullRank A.duplicatedSectionSevenBandFullRank
      (G.fiberHomeomorph y)
  refine congrArg Prod.snd
    (?_ : A.affineCentralBandMarkedProductHomeomorph
      A.affineCentralSeparation c =
      (A.affineActualCuspCrossingPoint,
        fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y)))
  apply (A.affineCentralBandMarkedProductHomeomorph
    A.affineCentralSeparation).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply A.affineCentralBandToCentralFamily_injective
  rw [A.affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily]
  exact actualCuspWangFiberToBand_centralFamily_completion hmark R y

/-- The explicit middle-height cusp slice and the canonical fibre-to-band map are homotopic. -/
public theorem actualCuspWangFiberToBandMap_homotopic_canonical
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic (actualCuspWangFiberToBandMap (A := A) R)
      R.twoDiscCover.canonicalCuspFiberToBandMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := R.twoDiscCover.bandHomotopyEquiv
  let f := actualCuspWangFiberToBandMap (A := A) R
  let p : C(G.Fiber, AdditiveTorus R.twoDiscCover.bandParameter) :=
    ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
      R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩
  have hcoordinate : e.toFun.comp f = p :=
    actualCuspWangFiberToBandMap_coordinate hmark R
  have hleft : f.Homotopic (e.invFun.comp (e.toFun.comp f)) := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      (ContinuousMap.Homotopic.comp e.left_inv (.refl f)).symm
  have hright : (e.invFun.comp (e.toFun.comp f)).Homotopic (e.invFun.comp p) := by
    rw [hcoordinate]
  exact hleft.trans hright

/-- After inclusion into the elliptic interior, the explicit middle-height cusp slice is
homotopic to the canonical cusp fibre map. -/
public theorem actualCuspWangFiberToEllipticInteriorMap_homotopic_canonical
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
              Set A.ellipticInterior),
            A.ellipticInterior)).comp
        (actualCuspWangFiberToBandMap (A := A) R))
      R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact ContinuousMap.Homotopic.comp
    (.refl (⟨Subtype.val, continuous_subtype_val⟩ :
      C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.ellipticInterior), A.ellipticInterior)))
    (actualCuspWangFiberToBandMap_homotopic_canonical hmark R)

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
