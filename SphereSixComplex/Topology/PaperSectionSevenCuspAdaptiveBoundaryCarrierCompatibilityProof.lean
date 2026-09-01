module

public import
  SphereSixComplex.Topology.PaperSectionSevenCuspInvariantBasisFromRadialCompatibilityCompletion

/-!
# Exact reduction of adaptive cusp carrier compatibility

The adaptive carrier equality on the Mayer--Vietoris boundary image is equivalent to the
oriented naturality square for the selected full-fibre slice.  Hence it contains exactly the
two invariant-generator comparisons left after the four zero-boundary cases.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- Oriented naturality for the selected full-fibre slice reconstructs the adaptive carrier
equality on the complete Mayer--Vietoris boundary image. -/
public theorem adaptiveBoundaryCarrierCompatibility_of_fullFibreOrientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreOrientedBoundaryNaturality R) :
    ActualCuspAdaptiveBoundaryCarrierCompatibility R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let boundary :=
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  let pullback :=
    SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  apply AddMonoidHom.ext
  intro y
  have hreadRaw := DFunLike.congr_fun
    (actualCuspAdaptiveNaturalSourceRead_boundary_eq_wang R) y
  have hnat := actualCuspHeightPreimageCover_boundary_naturality R 1
  have hnatApply := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) y
  have hboundary := DFunLike.congr_fun h (e.symm y)
  have hread : actualCuspAdaptiveNaturalSourceRead R (boundary y) =
      actualCuspWangBoundaryHom A (e.symm y) := by
    change actualCuspAdaptiveNaturalSourceRead R (boundary y) =
      (circleMappingTorusHTwoPresentation G.clutching).boundary (e (e.symm y))
    rw [e.apply_symm_apply]
    exact hreadRaw
  change pullback (boundary y) =
    R.twoDiscCover.cuspOpenCoverConnectingHom (e.symm y) at hnatApply
  change actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
      (actualCuspWangBoundaryHom A (e.symm y)) =
    R.twoDiscCover.cuspOpenCoverConnectingHom (e.symm y) at hboundary
  simp only [AddMonoidHom.comp_apply]
  calc
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (actualCuspAdaptiveNaturalSourceRead R (boundary y)) =
      actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (actualCuspWangBoundaryHom A (e.symm y)) := congrArg _ hread
    _ = R.twoDiscCover.cuspOpenCoverConnectingHom (e.symm y) := hboundary
    _ = pullback (boundary y) := hnatApply.symm

/-- The adaptive boundary carrier statement is exactly the oriented full-fibre naturality
square; the adaptive reparameterization introduces no additional residual. -/
public theorem adaptiveBoundaryCarrierCompatibility_iff_fullFibreOrientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspAdaptiveBoundaryCarrierCompatibility R ↔
      ActualCuspWangFullFibreOrientedBoundaryNaturality R :=
  ⟨fullFibreOrientedBoundaryNaturality_of_adaptiveCarrierCompatibility R,
    adaptiveBoundaryCarrierCompatibility_of_fullFibreOrientedBoundaryNaturality R⟩

/-- Equivalently, adaptive carrier compatibility consists of precisely the two remaining
invariant-generator comparisons for the explicit full-fibre slice. -/
public theorem adaptiveBoundaryCarrierCompatibility_iff_fullFibreInvariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspAdaptiveBoundaryCarrierCompatibility R ↔
      ActualCuspWangFullFibreSliceInvariantResidual R := by
  rw [adaptiveBoundaryCarrierCompatibility_iff_fullFibreOrientedBoundaryNaturality,
    fullFibreOrientedBoundaryNaturality_iff_invariantResidual]

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
