module

public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverRefinementGeometryReduction
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedBoundaryExactResidual

/-!
# Signed low-minus-high reduction for the cusp boundary

The marked comparison needed by the cusp boundary does not require separate formulas for the
low and high overlap legs.  The mapping-torus Mayer--Vietoris boundary is antidiagonal, so only
the difference of their marked values matters.  This file records that exact two-legged
geometric residual and proves that it is equivalent to the marked connecting square.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The explicit vertex--edge cover boundary is the low Wang leg minus the corresponding high
leg. -/
public theorem actualCuspVertexEdgeCoverConnecting_eq_low_add_signedHigh
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    actualCuspVertexEdgeCoverConnectingHom A x =
      actualCuspVertexEdgeOverlapLowLegClass (A := A) (actualCuspWangBoundaryHom A x) +
        actualCuspVertexEdgeOverlapHighLegClass (A := A)
          (-actualCuspWangBoundaryHom A x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let z := e x
  let p := (SphereSixComplex.overlapEquiv (fun _ : Unit ↦ G.clutching) 1).symm
    (actualCuspVertexEdgeCoverConnectingHom A x)
  have hfirst : p.1 () = actualCuspWangBoundaryHom A x := by
    have h := DFunLike.congr_fun
      (actualCuspVertexEdgeOverlapFirstLeg_comp_connecting A) x
    exact h
  have hp : p.2 = -p.1 := by
    change
      ((SphereSixComplex.overlapEquiv (fun _ : Unit ↦ G.clutching) 1).symm
        (SphereSixComplex.coverBoundary (fun _ : Unit ↦ G.clutching) 1
          ((SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2).symm z))).2 =
        -((SphereSixComplex.overlapEquiv (fun _ : Unit ↦ G.clutching) 1).symm
          (SphereSixComplex.coverBoundary (fun _ : Unit ↦ G.clutching) 1
            ((SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2).symm z))).1
    simpa only [SphereSixComplex.coverWangBoundary_apply] using
      SphereSixComplex.coverWangBoundary_snd_eq_neg_fst
        (fun _ : Unit ↦ G.clutching) 1 z
  have hsecond : p.2 () = -actualCuspWangBoundaryHom A x := by
    calc
      p.2 () = (-p.1) () := congrFun hp ()
      _ = -p.1 () := rfl
      _ = -actualCuspWangBoundaryHom A x := congrArg Neg.neg hfirst
  rw [actualCuspVertexEdgeOverlap_eq_lowLeg_add_highLeg
    (A := A) (actualCuspVertexEdgeCoverConnectingHom A x)]
  change _ = actualCuspVertexEdgeOverlapLowLegClass (A := A)
      (actualCuspWangBoundaryHom A x) +
    actualCuspVertexEdgeOverlapHighLegClass (A := A)
      (-actualCuspWangBoundaryHom A x)
  rw [hfirst, hsecond]

/-- The marked value of the transported low leg. -/
public noncomputable def actualCuspSignedRefinementLowMarkedValue
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R)
    (x : ActualCuspFiberHomologyOne A) : ℤ :=
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
    (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (actualCuspSignedRefinementOverlapTransport R C
        (actualCuspVertexEdgeOverlapLowLegClass (A := A) x)))

/-- The marked value of the transported high leg carrying the negative Wang class. -/
public noncomputable def actualCuspSignedRefinementNegativeHighMarkedValue
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R)
    (x : ActualCuspFiberHomologyOne A) : ℤ :=
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
    (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (actualCuspSignedRefinementOverlapTransport R C
        (actualCuspVertexEdgeOverlapHighLegClass (A := A) (-x))))

/-- The honest marked residual on the image of the Wang boundary: the low marked value minus
the high marked value is the selected cusp-fibre coordinate. -/
public def ActualCuspTwoLegMarkedBoundaryDifferenceNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) : Prop :=
  ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
    actualCuspSignedRefinementLowMarkedValue R C (actualCuspWangBoundaryHom A x) +
        actualCuspSignedRefinementNegativeHighMarkedValue R C
          (actualCuspWangBoundaryHom A x) =
      actualCuspFiberFourthCoordinateHom A (actualCuspWangBoundaryHom A x)

/-- The signed low-minus-high formula gives the complete marked connecting square. -/
public theorem cuspMarkedConnectingNaturality_of_twoLegMarkedBoundaryDifference
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R)
    (h : ActualCuspTwoLegMarkedBoundaryDifferenceNaturality R C) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment := by
  constructor
  ext x
  rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
  have hconnecting := DFunLike.congr_fun
    (actualCuspSignedRefinement_connectingNaturality R C) x
  simp only [AddMonoidHom.comp_apply] at hconnecting ⊢
  rw [← hconnecting, actualCuspVertexEdgeCoverConnecting_eq_low_add_signedHigh]
  simp only [map_add]
  exact h x

/-- Conversely, the marked connecting square determines the signed low-minus-high value on the
entire Wang-boundary image. -/
public theorem twoLegMarkedBoundaryDifference_of_cuspMarkedConnectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R)
    (h : R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment) :
    ActualCuspTwoLegMarkedBoundaryDifferenceNaturality R C := by
  intro x
  have hsquare := DFunLike.congr_fun h.square x
  rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp] at hsquare
  have hconnecting := DFunLike.congr_fun
    (actualCuspSignedRefinement_connectingNaturality R C) x
  simp only [AddMonoidHom.comp_apply] at hconnecting hsquare
  rw [← hconnecting, actualCuspVertexEdgeCoverConnecting_eq_low_add_signedHigh,
    map_add] at hsquare
  simpa [actualCuspSignedRefinementLowMarkedValue,
    actualCuspSignedRefinementNegativeHighMarkedValue, map_add] using hsquare

/-- For every actual oriented refinement, the signed two-leg residual is exactly the marked
connecting square. -/
public theorem twoLegMarkedBoundaryDifference_iff_connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    ActualCuspTwoLegMarkedBoundaryDifferenceNaturality R C ↔
      R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment :=
  ⟨cuspMarkedConnectingNaturality_of_twoLegMarkedBoundaryDifference R C,
    twoLegMarkedBoundaryDifference_of_cuspMarkedConnectingNaturality R C⟩

/-- Hence the established invariant-basis input is exactly the signed low-minus-high formula,
provided the two pointwise cover inclusions constructing the oriented refinement are supplied. -/
public theorem cuspPulledBackMarkedInvariantBasisData_iff_twoLegMarkedBoundaryDifference
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    CuspPulledBackMarkedInvariantBasisData R ↔
      ActualCuspTwoLegMarkedBoundaryDifferenceNaturality R C := by
  rw [cuspPulledBackMarkedInvariantBasisData_iff_markedConnectingNaturality,
    twoLegMarkedBoundaryDifference_iff_connectingNaturality]

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
