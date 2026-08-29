module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice
import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandSquares

/-!
# Oriented chain comparison for the explicit cusp fibre slice

The full-fibre slice constructs the map from the actual cusp fibre into the intersection of the
pulled-back binary cover.  The remaining input is therefore reduced to two equalities for that
specific map: its period-marked identification with the elliptic band and the oriented
connecting-morphism comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
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

/-- Restrict the cusp-to-elliptic map to the intersections of the two open covers. -/
public def cuspCoverIntersectionToEllipticOpensIntersectionMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D)) where
  toFun := BinaryOpenCover.openIntersectionPreimageMap D.cuspToEllipticInteriorMap
    (orderThreeOpen D) (orderFourOpen D)
  continuous_toFun := (BinaryOpenCover.openIntersectionPreimageMap
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)).hom.continuous

/-- Forget the `Opens` presentation of the elliptic intersection. -/
public def ellipticOpensIntersectionToBandMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :=
  ⟨(BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm,
    (BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm.continuous⟩

/-- The restriction of the cusp-to-elliptic map from the pulled-back cover intersection to the
elliptic band. -/
public def cuspCoverIntersectionToEllipticBandMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :=
  D.ellipticOpensIntersectionToBandMap.comp
    D.cuspCoverIntersectionToEllipticOpensIntersectionMap

/-- The selected full-fibre slice, transported as an actual continuous map into the elliptic
band. -/
public noncomputable def actualCuspWangFibreToBandMap
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.SectionSevenEllipticInterior)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandMap.comp
    (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)

/-- The categorical pullback/intersection comparison is induced by the literal restricted map. -/
public theorem cuspCoverIntersectionToEllipticBandHomologyOne_eq_map
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    D.cuspCoverIntersectionToEllipticBandHomologyOne =
      integralSingularHomologyMap 1 D.cuspCoverIntersectionToEllipticBandMap := by
  rw [cuspCoverIntersectionToEllipticBandHomologyOne,
    cuspCoverIntersectionToEllipticBandMap]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

/-- The previously defined transported homology map is induced by the continuous band map. -/
public theorem actualCuspWangFibreToBandHomologyOne_eq_map
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangFibreToBandHomologyOne (A := A) R =
      integralSingularHomologyMap 1 (actualCuspWangFibreToBandMap (A := A) R) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspWangFibreToBandMap, actualCuspWangFibreToBandHomologyOne,
    R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne_eq_map]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

private theorem actualCuspWangFibreToBand_centralFamily
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
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
    (actualCuspWangFibreToBandMap (A := A) R) y
  let c : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).height
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).lower
      (A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation).upper :=
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
                  (markedCuspParameter A.starCuspWitness) p.1.2 zeta)) =
          _
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

private theorem actualCuspWangFibreToBandMap_coordinate
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
  exact actualCuspWangFibreToBand_centralFamily R y

private theorem actualCuspWangFibreToBand_homology
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
  apply (R.twoDiscCover.bandHomologyEquiv 1).injective
  rw [R.twoDiscCover.bandHomologyEquiv_canonicalCuspFiberToBandHomologyOne]
  rw [actualCuspWangFibreToBandHomologyOne_eq_map]
  change integralSingularHomologyMap 1
      R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph x =
    ((integralSingularHomologyMap 1 R.twoDiscCover.bandHomotopyEquiv.toFun).comp
      (integralSingularHomologyMap 1
        (actualCuspWangFibreToBandMap (A := A) R))) x
  rw [← integralSingularHomologyMap_comp]
  rw [actualCuspWangFibreToBandMap_coordinate R]

/-- The exact finite residual comparison for the constructed full-fibre slice.  These six
equalities use the geometric basis of the cusp collar and fix the sign of the connecting
morphism. -/
public structure ActualCuspWangFullFibreSliceComparison
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  wangBoundary_eq_chainConnecting_basis :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 6,
      ((actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
          (actualCuspWangBoundaryHom A))
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
        R.twoDiscCover.cuspOpenCoverConnectingHom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))

namespace ActualCuspWangFullFibreSliceComparison

/-- The four marked fibre-basis checks reconstruct the full band-map equality. -/
public theorem fiberToBand_homology
    (_C : ActualCuspWangFullFibreSliceComparison R) :
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R := by
  exact actualCuspWangFibreToBand_homology R

/-- The six geometric collar-basis checks reconstruct the oriented connecting-map equality. -/
public theorem wangBoundary_eq_chainConnecting
    (C : ActualCuspWangFullFibreSliceComparison R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
        (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyTwoEquiv
  exact C.wangBoundary_eq_chainConnecting_basis

end ActualCuspWangFullFibreSliceComparison

namespace EstablishedActualCuspWangOpenCoverChainRealization

/-- The six oriented chain comparisons for the explicitly constructed full-fibre slice. -/
public axiom fullFibreSliceComparison (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspWangFullFibreSliceComparison R

/-- The standard chain-level Wang theorem for the actual radial mapping-torus cut cover.  Its
content is the oriented realization of the established Wang connecting map by the explicit
short exact singular-chain sequence, before transport to the elliptic cover. -/
public noncomputable def realization (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.ActualCuspWangOpenCoverChainRealization :=
  actualCuspWangOpenCoverChainRealization_of_fullFibreSlice (A := A) R
    (fullFibreSliceComparison R).fiberToBand_homology
    (fullFibreSliceComparison R).wangBoundary_eq_chainConnecting

end EstablishedActualCuspWangOpenCoverChainRealization

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
