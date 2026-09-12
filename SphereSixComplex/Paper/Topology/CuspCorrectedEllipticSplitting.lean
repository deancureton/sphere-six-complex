module

public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking
public import SphereSixComplex.Paper.Topology.CuspFourthSweepCentralImage
public import SphereSixComplex.Paper.Topology.CuspFourthSweepFiberParity

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open EllipticTwoDiscCoverData EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

public theorem cuspRawFour_positiveBoundary {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    (presentationTwo (D := R.twoDiscCover)).totalToInvariants
      (cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) =
      R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1 := by
  apply R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun
    (R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom_eq_cuspDegreeTwoBoundaryCoordinateHom
      R.homologyAlignment)
    (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
  exact h.symm.trans (cuspRawFour_pulled_back_scalar_one R)

public def correctedCuspDegreeTwoSplitting {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)) :=
  R.homologyAlignment.actualHomologyCoordinates.degreeTwoSplittingOfGenerator
    (cuspToEllipticUnionHomology R.twoDiscCover 2
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)))
    (cuspRawFour_positiveBoundary R)

public theorem correctedCuspDegreeTwoSplitting_rawFour {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R)
      (cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = ![0, 1] := by
  let B := R.homologyAlignment.actualHomologyCoordinates
  let S := correctedCuspDegreeTwoSplitting R
  have h := B.normalizedUnionHomologyTwoEquiv_add S 0 (B.degreeTwoInvariantEquiv.symm 1)
  have hs : S.sweptSection (B.degreeTwoInvariantEquiv.symm 1) =
      cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) := by
    change B.degreeTwoInvariantEquiv (B.degreeTwoInvariantEquiv.symm 1) •
      cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) = _
    rw [LinearEquiv.apply_symm_apply, one_smul]
  rw [map_zero, zero_add, hs, LinearEquiv.apply_symm_apply] at h
  simpa only [map_zero] using h

public theorem cuspEllipticFiberCoordinate_eq_union {A : AnalyticData}
    (R : A.AffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    A.cuspEllipticFiberCoordinate R S x =
      R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
        (cuspToEllipticUnionHomology R.twoDiscCover 2 x) 0 := by
  change R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
    (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom x) 0 = _
  rw [R.twoDiscCover.cuspToEllipticInteriorMap_homology]
  exact congrFun (congrArg
    (R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S)
    (AddEquiv.symm_apply_apply _ _)) 0


end SphereSixComplex.Geometry.AnalyticData
