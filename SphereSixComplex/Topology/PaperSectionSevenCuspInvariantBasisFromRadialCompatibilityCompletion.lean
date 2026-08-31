module

public import
  SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspFiberRadialHomotopyCompletion
public import
  SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveOverlapCarrierCompatibilityCompletion
public import
  SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveCoverInvariantBasisProof

/-!
# Cusp invariant basis from radial carrier compatibility

The radial homotopy identifies the selected full-fibre slice with the canonical fibre map
after passage to the elliptic interior.  This file isolates the remaining corestriction to the
actual cusp-cover intersection, with the cover-swap sign made explicit.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The explicit full-fibre slice induces the canonical fibre-to-band map on first homology. -/
public theorem canonicalCuspFiberToBandHomologyOne_eq_actualCuspWang
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspWangFibreToBandHomologyOne_eq_map]
  ext x
  change integralSingularHomologyMap 1 R.twoDiscCover.canonicalCuspFiberToBandMap x =
    integralSingularHomologyMap 1 (actualCuspWangFibreToBandMap (A := A) R) x
  have hmap := integralSingularHomologyMap_eq_of_homotopic
    (actualCuspWangFibreToBandMap_homotopic_canonical R).symm 1
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hmap) x

/-- The radial homotopy identifies the low-overlap fibre and the selected full-fibre slice
after both are included in the elliptic interior. -/
public theorem actualCuspRadialLowOverlapCarrier_homology
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 1
        R.twoDiscCover.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap =
      integralSingularHomologyMap 1
        ((⟨Subtype.val, continuous_subtype_val⟩ :
            C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
                Set A.SectionSevenEllipticInterior),
              A.SectionSevenEllipticInterior)).comp
          (actualCuspWangFibreToBandMap (A := A) R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom
          R.twoDiscCover.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap)) x = _
  rw [integralSingularHomologyMap_eq_of_homotopic
    (actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_homotopic_wangSlice R) 1]
  rfl

/-- Read the adaptive overlap in the natural order `order three, order four`.  The minus sign
compensates for swapping the order used by the endpoint-corrected phase. -/
public noncomputable def actualCuspAdaptiveNaturalSourceRead
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          (actualCuspMappingTorusOrderThreeOpen R ⊓
            actualCuspMappingTorusOrderFourOpen R)) →+
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let swap : IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          (actualCuspMappingTorusOrderThreeOpen R ⊓
            actualCuspMappingTorusOrderFourOpen R)) →+
      IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          (actualCuspMappingTorusOrderFourOpen R ⊓
            actualCuspMappingTorusOrderThreeOpen R)) :=
    ConcreteCategory.hom
      (SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
        (actualCuspMappingTorusOrderThreeOpen R)
        (actualCuspMappingTorusOrderFourOpen R) 1)
  exact -((actualCuspAdaptiveCoverDegreeOneSelfMap R).actualSourceRead.comp swap)

/-- The natural-order adaptive read sends the pulled-back Mayer--Vietoris boundary to the
actual cusp Wang boundary. -/
public theorem actualCuspAdaptiveNaturalSourceRead_boundary_eq_wang
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspAdaptiveNaturalSourceRead R).comp
        ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1) =
      (circleMappingTorusWangPresentationOfCover G.clutching 1).boundary := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspAdaptiveNaturalSourceRead]
  have h := actualCuspAdaptiveOverlapRead_marked_boundary_eq_neg_wang R
  ext x
  have hx := DFunLike.congr_fun h x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply] at hx ⊢
  rw [hx]
  simp

/-- The remaining carrier statement: on the complete Mayer--Vietoris boundary image, the
natural-order adaptive read followed by the selected full-fibre slice agrees with the literal
pullback map into the cusp-cover intersection. -/
public def ActualCuspAdaptiveBoundaryCarrierCompatibility
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let boundary :=
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1
  ((actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
      (actualCuspAdaptiveNaturalSourceRead R)).comp boundary =
    (SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1).comp boundary

/-- Full-fibre carrier compatibility gives the oriented full-fibre boundary square. -/
public theorem fullFibreOrientedBoundaryNaturality_of_adaptiveCarrierCompatibility
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspAdaptiveBoundaryCarrierCompatibility R) :
    ActualCuspWangFullFibreOrientedBoundaryNaturality R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
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
  have hcarrier := DFunLike.congr_fun h (e x)
  have hnat := actualCuspHeightPreimageCover_boundary_naturality R 1
  have hnatApply := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) (e x)
  have hcancel :
      SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
          (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  change
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (actualCuspWangBoundaryHom A x) =
      R.twoDiscCover.cuspOpenCoverConnectingHom x
  change actualCuspAdaptiveNaturalSourceRead R (boundary (e x)) =
    actualCuspWangBoundaryHom A x at hread
  change actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
      (actualCuspAdaptiveNaturalSourceRead R (boundary (e x))) =
    pullback (boundary (e x)) at hcarrier
  change pullback (boundary (e x)) =
    R.twoDiscCover.cuspOpenCoverConnectingHom
      (SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
        (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x)) at hnatApply
  calc
    _ = actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (actualCuspAdaptiveNaturalSourceRead R (boundary (e x))) :=
      congrArg (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R)
        hread.symm
    _ = pullback (boundary (e x)) := hcarrier
    _ = R.twoDiscCover.cuspOpenCoverConnectingHom
        (SphereSixComplex.BinaryOpenCover.integralHomologyMapHom
          (actualCuspMappingTorusToCollarTopCatMap A) 2 (e x)) := hnatApply
    _ = _ := congrArg R.twoDiscCover.cuspOpenCoverConnectingHom hcancel

/-- The one remaining carrier comparison implies the two marked invariant-basis evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_adaptiveCarrierCompatibility
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspAdaptiveBoundaryCarrierCompatibility R) :
    CuspPulledBackMarkedInvariantBasisData R :=
  cuspPulledBackMarkedInvariantBasisData_of_fullFibreOrientedBoundaryNaturality R
    (fullFibreOrientedBoundaryNaturality_of_adaptiveCarrierCompatibility R h)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
