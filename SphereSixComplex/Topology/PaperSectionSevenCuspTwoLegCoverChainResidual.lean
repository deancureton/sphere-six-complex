module

public import SphereSixComplex.Topology.PaperSectionSevenCuspCanonicalSignedOverlapReduction

/-!
# Two-leg cover-chain residual for the cusp boundary

The Wang boundary used by the cusp model is the first leg of the Mayer--Vietoris boundary of
the explicit vertex/edge cover of its mapping torus.  The other leg is its negative.  This file
keeps that two-leg cover boundary visible and isolates the missing comparison with the pulled-back
cusp cover before evaluating any raw basis vector.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- First homology of the two-component overlap in the explicit vertex/edge cover of the actual
cusp mapping torus. -/
public abbrev ActualCuspVertexEdgeOverlapHomologyOne (A : PaperAnalyticData) :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  IntegralSingularHomology 1
    ↥(SphereSixComplex.vertexPiece (fun _ : Unit ↦ G.clutching) ∩
      SphereSixComplex.edgePiece (fun _ : Unit ↦ G.clutching))

/-- The oriented connecting map of the explicit vertex/edge cover, transported from the actual
cusp collar through its mapping-torus homotopy equivalence. -/
public noncomputable def actualCuspVertexEdgeCoverConnectingHom (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      ActualCuspVertexEdgeOverlapHomologyOne A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact (SphereSixComplex.coverBoundary (fun _ : Unit ↦ G.clutching) 1).comp
    ((SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2).symm.toAddMonoidHom.comp
      (integralSingularHomologyEquivOfHomotopyEquiv 2
        G.totalHomotopyEquiv).toAddMonoidHom)

/-- Projection from the two-legged overlap homology to its low leg. -/
public noncomputable def actualCuspVertexEdgeOverlapFirstLeg (A : PaperAnalyticData) :
    ActualCuspVertexEdgeOverlapHomologyOne A →+
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact
    { toFun := fun z ↦
        ((SphereSixComplex.overlapEquiv
          (fun _ : Unit ↦ G.clutching) 1).symm z).1 ()
      map_zero' := by simp
      map_add' := by intro x y; simp }

/-- The low leg of the explicit two-legged cover boundary is definitionally the constructed
Wang boundary used by the cusp model. -/
public theorem actualCuspVertexEdgeOverlapFirstLeg_comp_connecting
    (A : PaperAnalyticData) :
    (actualCuspVertexEdgeOverlapFirstLeg A).comp
        (actualCuspVertexEdgeCoverConnectingHom A) =
      actualCuspWangBoundaryHom A := by
  apply AddMonoidHom.ext
  intro x
  rfl

/-- The unconditional signed carrier, viewed as a transport from the full two-legged overlap by
first projecting to the oriented low leg. -/
public noncomputable def actualCuspCanonicalTwoLegTransport
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R :=
  (actualCuspCanonicalSignedOverlap R).comp
    (actualCuspVertexEdgeOverlapFirstLeg A)

/-- Naturality of the explicit two-legged mapping-torus cover boundary under a proposed
transport to the overlap of the pulled-back cusp cover. -/
public def ActualCuspTwoLegConnectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (overlapTransport : ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R) : Prop :=
  overlapTransport.comp (actualCuspVertexEdgeCoverConnectingHom A) =
    R.twoDiscCover.cuspOpenCoverConnectingHom

/-- Compatibility of the same two-leg transport with the fourth marked band coordinate.  The
right side reads the low leg before applying the actual cusp-fibre marking. -/
public def ActualCuspTwoLegMarkedOverlapNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (overlapTransport : ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R) : Prop :=
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
      (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp
        overlapTransport) =
    (actualCuspFiberFourthCoordinateHom A).comp
      (actualCuspVertexEdgeOverlapFirstLeg A)

/-- The exact two-leg chain comparison still missing from the geometric development. -/
public def ActualCuspTwoLegCoverChainNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (overlapTransport : ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R) : Prop :=
  ActualCuspTwoLegConnectingNaturality R overlapTransport ∧
    ActualCuspTwoLegMarkedOverlapNaturality R overlapTransport

/-- The canonical two-leg transport already intertwines the two oriented connecting maps.  No
marked coordinate or invariant-basis calculation enters this statement. -/
public theorem actualCuspCanonicalTwoLegTransport_connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspTwoLegConnectingNaturality R
      (actualCuspCanonicalTwoLegTransport R) := by
  rw [ActualCuspTwoLegConnectingNaturality, actualCuspCanonicalTwoLegTransport,
    AddMonoidHom.comp_assoc, actualCuspVertexEdgeOverlapFirstLeg_comp_connecting,
    actualCuspCanonicalSignedOverlap_boundary]

/-- For the canonical two-leg transport, the entire residual is its compatibility with the
fourth marked band coordinate. -/
public theorem canonicalTwoLegCoverChainNaturality_iff_markedOverlapNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspTwoLegCoverChainNaturality R
        (actualCuspCanonicalTwoLegTransport R) ↔
      ActualCuspTwoLegMarkedOverlapNaturality R
        (actualCuspCanonicalTwoLegTransport R) := by
  exact and_iff_right (actualCuspCanonicalTwoLegTransport_connectingNaturality R)

/-- A two-leg cover-chain comparison gives the marked connecting square without evaluating a
single raw cusp basis vector. -/
public theorem cuspMarkedConnectingNaturality_of_twoLegCoverChainNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (overlapTransport : ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R)
    (h : ActualCuspTwoLegCoverChainNaturality R overlapTransport) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment := by
  constructor
  ext x
  calc
    R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspPulledBackBoundaryHom x) =
      R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
          (R.twoDiscCover.cuspOpenCoverConnectingHom x)) := by
            rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
            rfl
    _ = R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
          (overlapTransport (actualCuspVertexEdgeCoverConnectingHom A x))) := by
            have hx := DFunLike.congr_fun h.1 x
            simpa only [AddMonoidHom.comp_apply] using congrArg
              (fun y ↦ R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
                (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne y)) hx.symm
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspVertexEdgeOverlapFirstLeg A
          (actualCuspVertexEdgeCoverConnectingHom A x)) := by
            exact DFunLike.congr_fun h.2 (actualCuspVertexEdgeCoverConnectingHom A x)
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspWangBoundaryHom A x) := by
          have hx := DFunLike.congr_fun
            (actualCuspVertexEdgeOverlapFirstLeg_comp_connecting A) x
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (actualCuspFiberFourthCoordinateHom A) hx

/-- The explicit two-leg cover-chain comparison discharges the two remaining invariant-basis
evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_twoLegCoverChainNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (overlapTransport : ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R)
    (h : ActualCuspTwoLegCoverChainNaturality R overlapTransport) :
    CuspPulledBackMarkedInvariantBasisData R := by
  have hSquare :=
    (cuspMarkedConnectingNaturality_of_twoLegCoverChainNaturality R overlapTransport h).square
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

/-- Consequently, only marked-band compatibility of the canonical explicit two-leg transport
remains in order to eliminate the invariant-basis input. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_canonicalTwoLegMarkedNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspTwoLegMarkedOverlapNaturality R
      (actualCuspCanonicalTwoLegTransport R)) :
    CuspPulledBackMarkedInvariantBasisData R :=
  cuspPulledBackMarkedInvariantBasisData_of_twoLegCoverChainNaturality R
    (actualCuspCanonicalTwoLegTransport R)
    ⟨actualCuspCanonicalTwoLegTransport_connectingNaturality R, h⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
