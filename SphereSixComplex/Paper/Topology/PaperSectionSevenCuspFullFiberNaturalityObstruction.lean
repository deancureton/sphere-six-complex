module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMarkedInvariantBasisFromFullFiberNaturality

/-!
The first obstruction uses only the three standard Lean axioms. The naturality negations
also use the existing CW and toric assumptions through the raw Wang coordinates. None uses
the scalar cusp-boundary residual, which these results do not refute.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscCoverData
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace EllipticTwoDiscCoverData

public theorem cuspPulledBackBoundary_coordinate_ne_fourthBasis
    (D : A.EllipticTwoDiscCoverData)
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    B.bandOne (D.cuspPulledBackBoundaryHom x) ≠ ![0, 0, 0, 1] := by
  intro hc
  have hz := (D.cuspPulledBackBoundaryInvariantHom x).2
  change IntegralMayerVietoris.differenceMap D.orderThreeSide
    D.orderFourSide 1 (D.cuspPulledBackBoundaryHom x) = 0 at hz
  have hd := B.differenceOne (D.cuspPulledBackBoundaryHom x)
  rw [hz, map_zero, hc] at hd
  have he := congrFun hd 1
  norm_num [ellipticActualHOneDifferenceMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at he

public theorem not_canonicalCuspWangBoundaryNaturality
    (R : A.AffineRadialCompletionInput) :
    ¬ (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne.comp (actualCuspWangBoundaryHom A) =
           R.twoDiscCover.cuspPulledBackBoundaryHom) := by
  intro h
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
  let B := R.homologyAlignment.actualHomologyCoordinates
  have hm : (R.homologyAlignment.actualHomologyCoordinates.bandOne.toAddMonoidHom.comp
                   R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
                 let G := A.actualCuspRadialClutchingData
                 let _ := G.fiberTopology
                 G.monodromyCoordinates.degreeOne.toAddMonoidHom) :=
    R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree R.homologyAlignment
      (R.canonicalCuspFiberOrderThreePeriodMarking
        (cuspFiberPeriodMarkingCompatibility A))
  have hc : B.bandOne (R.twoDiscCover.cuspPulledBackBoundaryHom x) =
      ![0, 0, 0, 1] := by
    have hh := DFunLike.congr_fun h x
    have hmark := DFunLike.congr_fun hm (actualCuspWangBoundaryHom A x)
    change B.bandOne (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne
      (actualCuspWangBoundaryHom A x)) = _ at hmark
    rw [AddMonoidHom.comp_apply] at hh
    rw [← hh, hmark]
    simpa [x] using actualCuspWangBoundaryHom_rawCoordinates A x
  exact cuspPulledBackBoundary_coordinate_ne_fourthBasis R.twoDiscCover B x hc

public theorem not_actualCuspWangFullFiberOrientedBoundaryNaturality
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    ¬ ActualCuspWangFullFiberOrientedBoundaryNaturality R := by
  intro h
  exact not_canonicalCuspWangBoundaryNaturality R
    (canonicalCuspWangBoundaryNaturality_of_fullFiberOrientedBoundaryNaturality hmark R h)

public theorem not_actualCuspWangFullFiberSliceInvariantResidual
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput) :
    ¬ ActualCuspWangFullFiberSliceInvariantResidual R := by
  intro h
  exact not_actualCuspWangFullFiberOrientedBoundaryNaturality hmark R
    ((fullFiberOrientedBoundaryNaturality_iff_invariantResidual R).mpr h)

end EllipticTwoDiscCoverData
end SphereSixComplex.Geometry.PaperAnalyticData
end
end
