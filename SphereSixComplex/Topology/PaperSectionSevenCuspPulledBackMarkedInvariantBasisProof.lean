module

public import
  SphereSixComplex.Topology.PaperSectionSevenCuspInvariantBasisFromRadialCompatibilityCompletion

/-!
# Exact adaptive-cover residual for the pulled-back marked cusp basis

The adaptive height-preimage cover already has the correct oriented boundary, and its boundary
is natural under the radial map to the actual cusp collar.  Consequently the two remaining
invariant-basis evaluations are equivalent to one marked carrier equality on the image of that
explicit adaptive boundary.  No equality on the whole overlap homology is required.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The exact remaining marked carrier equality on the adaptive Mayer--Vietoris boundary image.
The left side transports the literal pullback boundary into the elliptic band; the right side
reads the same boundary through the oriented low overlap and applies the cusp-fibre marking. -/
public def ActualCuspAdaptiveMarkedBoundaryCarrierResidual
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let boundary :=
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  ((R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
      (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp pullback)).comp
        boundary =
    ((actualCuspFiberFourthCoordinateHom A).comp
      (actualCuspAdaptiveNaturalSourceRead R)).comp boundary

/-- The adaptive marked carrier equality implies both invariant-basis evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_adaptiveMarkedBoundaryCarrierResidual
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspAdaptiveMarkedBoundaryCarrierResidual R) :
    CuspPulledBackMarkedInvariantBasisData R := by
  apply (cuspPulledBackMarkedInvariantBasisData_iff_markedConnectingNaturality R).2
  constructor
  apply AddMonoidHom.ext
  intro x
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let boundary :=
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  have hread := DFunLike.congr_fun
    (congrArg (fun q ↦ q.comp e.toAddMonoidHom)
      (actualCuspAdaptiveNaturalSourceRead_boundary_eq_wang R)) x
  have hnat := actualCuspHeightPreimageCover_boundary_naturality R 1
  have hnatApply := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) (e x)
  have hcancel :
      SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
          (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have hres := DFunLike.congr_fun h (e x)
  change actualCuspAdaptiveNaturalSourceRead R (boundary (e x)) =
    actualCuspWangBoundaryHom A x at hread
  change pullback (boundary (e x)) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
        (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x)) at hnatApply
  rw [hcancel] at hnatApply
  simp only [AddMonoidHom.comp_apply] at hres
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
          (pullback (boundary (e x)))) := by rw [hnatApply]
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspAdaptiveNaturalSourceRead R (boundary (e x))) := hres
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspWangBoundaryHom A x) := congrArg _ hread

/-- Conversely, the two invariant-basis evaluations determine the marked adaptive carrier on
the complete boundary image. -/
public theorem adaptiveMarkedBoundaryCarrierResidual_of_cuspPulledBackMarkedInvariantBasisData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R) :
    ActualCuspAdaptiveMarkedBoundaryCarrierResidual R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let boundary :=
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  have hsquare :=
    (cuspPulledBackMarkedInvariantBasisData_iff_markedConnectingNaturality R).1 h
  apply AddMonoidHom.ext
  intro y
  have hread := DFunLike.congr_fun
    (actualCuspAdaptiveNaturalSourceRead_boundary_eq_wang R) y
  have hnat := actualCuspHeightPreimageCover_boundary_naturality R 1
  have hnatApply := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) y
  change pullback (boundary y) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
        (actualCuspMappingTorusToCollarTopCatMap A) 2 y) at hnatApply
  change pullback (boundary y) =
    R.twoDiscCover.cuspOpenCoverConnectingHom (e.symm y) at hnatApply
  have hread' : actualCuspAdaptiveNaturalSourceRead R (boundary y) =
      actualCuspWangBoundaryHom A (e.symm y) := by
    change actualCuspAdaptiveNaturalSourceRead R (boundary y) =
      (circleMappingTorusHTwoPresentation G.clutching).boundary (e (e.symm y))
    rw [e.apply_symm_apply]
    exact hread
  have hsquareApply := DFunLike.congr_fun hsquare.square (e.symm y)
  simp only [AddMonoidHom.comp_apply] at hsquareApply ⊢
  calc
    R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
          (pullback (boundary y))) =
      R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
          (R.twoDiscCover.cuspOpenCoverConnectingHom (e.symm y))) := by rw [hnatApply]
    _ = R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment
        (R.twoDiscCover.cuspPulledBackBoundaryHom (e.symm y)) := by
          rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
          rfl
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspWangBoundaryHom A (e.symm y)) := hsquareApply
    _ = actualCuspFiberFourthCoordinateHom A
        (actualCuspAdaptiveNaturalSourceRead R (boundary y)) :=
      congrArg _ hread'.symm

/-- The former pair of scalar evaluations is exactly one marked equality on the adaptive
boundary image. -/
public theorem cuspPulledBackMarkedInvariantBasisData_iff_adaptiveMarkedBoundaryCarrierResidual
    (R : A.SectionSevenAffineRadialCompletionInput) :
    CuspPulledBackMarkedInvariantBasisData R ↔
      ActualCuspAdaptiveMarkedBoundaryCarrierResidual R :=
  ⟨adaptiveMarkedBoundaryCarrierResidual_of_cuspPulledBackMarkedInvariantBasisData R,
    cuspPulledBackMarkedInvariantBasisData_of_adaptiveMarkedBoundaryCarrierResidual R⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
