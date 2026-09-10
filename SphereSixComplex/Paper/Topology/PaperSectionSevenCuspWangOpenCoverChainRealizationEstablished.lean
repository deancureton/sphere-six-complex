module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares

/-!
# Oriented chain comparison for the explicit cusp fibre slice

The full-fibre slice constructs the map from the actual cusp fibre into the intersection of the
pulled-back binary cover.  The remaining input is therefore reduced to two equalities for that
specific map: its period-marked identification with the elliptic band and the oriented
connecting-morphism comparison. The band identification here requires explicit crossing-marking
agreement; it is not inferred from the normalized strip marking.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscHomologyCoordinates
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

/-- Restrict the cusp-to-elliptic map to the intersections of the two open covers. -/
public def cuspCoverIntersectionToEllipticOpensIntersectionMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D)) where
  toFun := BinaryOpenCover.openIntersectionPreimageMap D.cuspToEllipticInteriorMap
    (orderThreeOpen D) (orderFourOpen D)
  continuous_toFun := (BinaryOpenCover.openIntersectionPreimageMap
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)).hom.continuous

/-- Forget the `Opens` presentation of the elliptic intersection. -/
public def ellipticOpensIntersectionToBandMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :=
  ⟨(BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm,
    (BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm.continuous⟩

/-- The restriction of the cusp-to-elliptic map from the pulled-back cover intersection to the
elliptic band. -/
public def cuspCoverIntersectionToEllipticBandMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :=
  D.ellipticOpensIntersectionToBandMap.comp
    D.cuspCoverIntersectionToEllipticOpensIntersectionMap

/-- The selected full-fibre slice, transported as an actual continuous map into the elliptic
band. -/
public noncomputable def actualCuspWangFiberToBandMap
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.ellipticInterior)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandMap.comp
    (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R)

/-- The categorical pullback/intersection comparison is induced by the literal restricted map. -/
public theorem cuspCoverIntersectionToEllipticBandHomologyOne_eq_map
    (D : A.EllipticTwoDiscCoverData) :
    D.cuspCoverIntersectionToEllipticBandHomologyOne =
      integralSingularHomologyMap 1 D.cuspCoverIntersectionToEllipticBandMap := by
  rw [cuspCoverIntersectionToEllipticBandHomologyOne,
    cuspCoverIntersectionToEllipticBandMap]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

/-- The previously defined transported homology map is induced by the continuous band map. -/
public theorem actualCuspWangFiberToBandHomologyOne_eq_map
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangFiberToBandHomologyOne (A := A) R =
      integralSingularHomologyMap 1 (actualCuspWangFiberToBandMap (A := A) R) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspWangFiberToBandMap, actualCuspWangFiberToBandHomologyOne,
    R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne_eq_map]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

private theorem actualCuspWangFiberToBand_centralFamily
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
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
    (actualCuspWangFiberToBandMap (A := A) R) y
  let c : centralHeightBand
      (A.affineCentralHeightSplit A.affineCentralSeparation).height
      (A.affineCentralHeightSplit A.affineCentralSeparation).lower
      (A.affineCentralHeightSplit A.affineCentralSeparation).upper :=
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
                  (markedCuspParameter A.starCuspWitness) p.1.2 zeta)) =
          _
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

private theorem actualCuspWangFiberToBandMap_coordinate
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
  exact actualCuspWangFiberToBand_centralFamily hmark R y

private theorem actualCuspWangFiberToBand_homology
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFiberToBandHomologyOne (A := A) R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
  apply (R.twoDiscCover.bandHomologyEquiv 1).injective
  rw [R.twoDiscCover.bandHomologyEquiv_canonicalCuspFiberToBandHomologyOne]
  rw [actualCuspWangFiberToBandHomologyOne_eq_map]
  change integralSingularHomologyMap 1
      R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph x =
    ((integralSingularHomologyMap 1 R.twoDiscCover.bandHomotopyEquiv.toFun).comp
      (integralSingularHomologyMap 1
        (actualCuspWangFiberToBandMap (A := A) R))) x
  rw [← integralSingularHomologyMap_comp]
  rw [actualCuspWangFiberToBandMap_coordinate hmark R]

/-- The exact finite residual comparison for the constructed full-fibre slice.  These six
equalities use the geometric basis of the cusp collar and fix the sign of the connecting
morphism. -/
public structure ActualCuspWangFullFiberSliceComparison
    (R : A.AffineRadialCompletionInput) : Prop where
  wangBoundary_eq_chainConnecting_basis :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6,
      ((actualCuspWangFiberToCuspCoverIntersectionHomologyOne (A := A) R).comp
          (actualCuspWangBoundaryHom A))
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
        R.twoDiscCover.cuspOpenCoverConnectingHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))

namespace ActualCuspWangFullFiberSliceComparison

/-- The four marked fibre-basis checks reconstruct the full band-map equality. -/
public theorem fiberToBand_homology
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (_C : ActualCuspWangFullFiberSliceComparison R) :
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFiberToBandHomologyOne (A := A) R := by
  exact actualCuspWangFiberToBand_homology hmark R

/-- The six geometric collar-basis checks reconstruct the oriented connecting-map equality. -/
public theorem wangBoundary_eq_chainConnecting
    (C : ActualCuspWangFullFiberSliceComparison R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspWangFiberToCuspCoverIntersectionHomologyOne (A := A) R).comp
        (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
    A.cuspRawHomologyTwoEquiv
  exact C.wangBoundary_eq_chainConnecting_basis

end ActualCuspWangFullFiberSliceComparison

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
