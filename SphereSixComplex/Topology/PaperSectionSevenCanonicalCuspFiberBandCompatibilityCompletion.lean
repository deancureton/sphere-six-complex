module

public import
  SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

/-!
# Canonical cusp-fibre-to-band compatibility reduction

The marked affine-band trivialization identifies the explicit middle-height cusp-fibre slice
with the canonical fibre-to-band map up to homotopy.  This leaves only the comparison between
that slice and the fibre inclusion selected by the radial homotopy equivalence.
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

namespace SectionSevenEllipticTwoDiscCoverData

private theorem actualCuspWangFibreToBand_centralFamily_completion
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let b := actualCuspWangFibreToBandMap (A := A) R y
    let c := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph b
    A.sectionSevenAffineCentralBandToCentralFamily
        A.sectionSevenAffineCentralSeparation c =
      A.stripLiftPoint A.sectionSevenAffineNamedStripLift
        A.sectionSevenAffineActualCuspCrossingPoint
        (fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let b :
      (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
        Set A.SectionSevenEllipticInterior) :=
    actualCuspWangFibreToBandMap (A := A) R y
  let c : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit
        A.sectionSevenAffineCentralSeparation).height
      (A.sectionSevenAffineCentralHeightSplit
        A.sectionSevenAffineCentralSeparation).lower
      (A.sectionSevenAffineCentralHeightSplit
        A.sectionSevenAffineCentralSeparation).upper :=
    A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph b
  dsimp only
  have hcentral :
      A.sectionSevenAffineCentralBandToCentralFamily
          A.sectionSevenAffineCentralSeparation c =
        A.starToCentral 0
          ((actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R y).1) := by
    apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
    apply Subtype.ext
    change
      (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.sectionSevenEllipticCentralImageHomeomorph _)).1 =
      (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0 _)).1
    rw [A.centralToSectionSevenEulerPiece_centralImage]
    calc
      _ = b.1.1 := rfl
      _ = A.openEmbeddingStarData.collarSourceToGlued 0
          ((actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R y).1) := rfl
      _ = _ := (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
  rw [hcentral]
  obtain ⟨w, hw⟩ := Quotient.exists_rep y
  let t := actualCuspFullFibreCrossingTime A
  let p := A.actualCuspAngularLiftPoint t
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
  have hslice := actualCuspFullFibreSlice_additiveTorusProjection
    (A := A) p.1.2 hs zeta
  rw [hzeta, hw'] at hslice
  change actualCuspFullFibreSlice (A := A) p.1.2 hs y =
    additiveCuspBoundaryProjection A.starCuspWitness q at hslice
  have hintersection :
      ((actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R y).1) =
        additiveCuspBoundaryProjection A.starCuspWitness q := hslice
  rw [hintersection]
  have hcoordinate :
      fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y) =
        Quotient.mk _ (A.regularMovingToFixed
          (A.sectionSevenAffineNamedStripLift.lift
            A.sectionSevenAffineActualCuspCrossingPoint) zeta) := by
    change fullRankAdditiveTorusHomeomorph
        G.fiberParameter A.duplicatedSectionSevenBandParameter
        G.fiberFullRank A.duplicatedSectionSevenBandFullRank y = _
    rw [← hw]
    change Quotient.mk _
        (A.duplicatedSectionSevenBandFullRank.realEquiv
          (G.fiberFullRank.realEquiv.symm w)) =
      Quotient.mk _ (A.regularMovingToFixed
        (A.sectionSevenAffineNamedStripLift.lift
          A.sectionSevenAffineActualCuspCrossingPoint) zeta)
    apply congrArg (Quotient.mk _)
    rw [A.sectionSevenAffineNamedStripLift_apply_actualCuspCrossing]
    change A.duplicatedSectionSevenBandFullRank.realEquiv
        (G.fiberFullRank.realEquiv.symm w) =
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (A.actualCuspAngularRegularBasePoint
          A.sectionSevenAffineActualCuspCrossingTime, zeta)).2
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
  rw [A.sectionSevenAffineNamedStripLift_apply_actualCuspCrossing]
  change puncturedLocalCuspQuotientMap A.starCuspWitness
      (additiveCuspBoundaryProjection A.starCuspWitness q) =
    A.centralQuotientProjection
      (projection (regularParameterMap A.periods)
        (A.actualCuspAngularRegularBasePoint
          A.sectionSevenAffineActualCuspCrossingTime, zeta))
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  rfl

/-- The actual middle-height cusp slice has exactly the canonical marked band coordinate. -/
public theorem actualCuspWangFibreToBandMap_coordinate
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.bandHomotopyEquiv.toFun.comp
        (actualCuspWangFibreToBandMap (A := A) R) =
      ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
        R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩ := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro y
  let b :
      (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior) :=
    (actualCuspWangFibreToBandMap (A := A) R) y
  let c : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).height
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).lower
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).upper :=
    A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph b
  change
    (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation c).2 =
    fullRankAdditiveTorusHomeomorph
      G.fiberParameter A.duplicatedSectionSevenBandParameter
      G.fiberFullRank A.duplicatedSectionSevenBandFullRank
      (G.fiberHomeomorph y)
  refine congrArg Prod.snd
    (?_ : A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation c =
      (A.sectionSevenAffineActualCuspCrossingPoint,
        fullRankAdditiveTorusHomeomorph
          G.fiberParameter A.duplicatedSectionSevenBandParameter
          G.fiberFullRank A.duplicatedSectionSevenBandFullRank
          (G.fiberHomeomorph y)))
  apply (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
    A.sectionSevenAffineCentralSeparation).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply A.sectionSevenAffineCentralBandToCentralFamily_injective
  rw [A.sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily]
  exact actualCuspWangFibreToBand_centralFamily_completion R y

/-- The explicit middle-height cusp slice and the canonical fibre-to-band map are homotopic. -/
public theorem actualCuspWangFibreToBandMap_homotopic_canonical
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic (actualCuspWangFibreToBandMap (A := A) R)
      R.twoDiscCover.canonicalCuspFiberToBandMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := R.twoDiscCover.bandHomotopyEquiv
  let f := actualCuspWangFibreToBandMap (A := A) R
  let p : C(G.Fiber, AdditiveTorus R.twoDiscCover.bandParameter) :=
    ⟨R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph,
      R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩
  have hcoordinate : e.toFun.comp f = p :=
    actualCuspWangFibreToBandMap_coordinate R
  have hleft : f.Homotopic (e.invFun.comp (e.toFun.comp f)) := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      (ContinuousMap.Homotopic.comp e.left_inv (.refl f)).symm
  have hright : (e.invFun.comp (e.toFun.comp f)).Homotopic (e.invFun.comp p) := by
    rw [hcoordinate]
  exact hleft.trans hright

/-- After inclusion into the elliptic interior, the explicit middle-height cusp slice is
homotopic to the canonical cusp fibre map. -/
public theorem actualCuspWangFibreToEllipticInteriorMap_homotopic_canonical
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
              Set A.SectionSevenEllipticInterior),
            A.SectionSevenEllipticInterior)).comp
        (actualCuspWangFibreToBandMap (A := A) R))
      R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact ContinuousMap.Homotopic.comp
    (.refl (⟨Subtype.val, continuous_subtype_val⟩ :
      C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
          Set A.SectionSevenEllipticInterior), A.SectionSevenEllipticInterior)))
    (actualCuspWangFibreToBandMap_homotopic_canonical R)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
