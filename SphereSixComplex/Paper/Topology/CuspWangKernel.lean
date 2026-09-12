module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import all SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
/-! A cusp class with zero Wang boundary is represented in the cover intersection. Thus equal Wang classes have equal pulled-back elliptic boundaries. -/

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory Set
namespace SphereSixComplex.Geometry.AnalyticData.EllipticTwoDiscCoverData
open SphereSixComplex.Topology
open EllipticTwoDiscHomologyCoordinates
public theorem cuspWangKernel_mem_intersectionImage
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0))
    (hb : actualCuspWangBoundaryHom A x = 0) :
    ∃ w, integralSingularHomologyMap 2
      (TopologicalSpace.Opens.inclusion'
        (R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen)).hom w = x := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let y := e x
  let P := circleMappingTorusHTwoPresentation G.clutching
  have hy : y ∈ Set.range P.inclusion := by
    exact (P.exact_inclusion_boundary y).mp hb
  obtain ⟨z, hz⟩ := hy
  let w := integralSingularHomologyMap 2
    (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R) z
  refine ⟨w, ?_⟩
  apply e.injective
  change integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
      (integralSingularHomologyMap 2
        (TopologicalSpace.Opens.inclusion'
          (R.twoDiscCover.cuspOrderThreeOpen ⊓
            R.twoDiscCover.cuspOrderFourOpen)).hom
        (integralSingularHomologyMap 2
          (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R) z)) = y
  have hsquare := congrArg (fun f ↦ f z)
    (congrArg (integralSingularHomologyMap 2)
      (actualCuspWangFiberSlice_to_mappingTorus R))
  calc
    _ = integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 2
          ((TopologicalSpace.Opens.inclusion'
            (R.twoDiscCover.cuspOrderThreeOpen ⊓
              R.twoDiscCover.cuspOrderFourOpen)).hom.comp
            (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R)) z) := by
      rw [← SphereSixComplex.integralSingularHomologyMap_comp_wang]
    _ = integralSingularHomologyMap 2
        (G.totalHomotopyEquiv.toFun.comp
          ((TopologicalSpace.Opens.inclusion'
            (R.twoDiscCover.cuspOrderThreeOpen ⊓
              R.twoDiscCover.cuspOrderFourOpen)).hom.comp
            (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R))) z :=
      SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _
    _ = integralSingularHomologyMap 2
        (CyclicAngularFundamentalDomain.realFiberSlice G.clutching
          (A.cuspAngularLiftPoint
            (actualCuspFullFiberCrossingTime A)).1.2.re) z := hsquare
    _ = integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) z := by
      rw [integralSingularHomologyMap_eq_of_homotopy 2
        (CyclicAngularFundamentalDomain.realFiberSliceHomotopy G.clutching
          (A.cuspAngularLiftPoint
            (actualCuspFullFiberCrossingTime A)).1.2.re)]
    _ = y := hz

public theorem cuspPulledBackBoundary_eq_zero_of_wang_zero
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0))
    (hx : actualCuspWangBoundaryHom A x = 0) :
    R.twoDiscCover.cuspPulledBackBoundaryHom x = 0 := by
  obtain ⟨w, hw⟩ := cuspWangKernel_mem_intersectionImage R x hx
  rw [cuspPulledBackBoundaryHom_eq_comp, AddMonoidHom.comp_apply,
    cuspOpenCoverConnectingHom_eq_zero_of_intersection_image R x w hw, map_zero]

public theorem cuspPulledBackBoundary_eq_of_wang_eq
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x y : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0))
    (hxy : actualCuspWangBoundaryHom A x = actualCuspWangBoundaryHom A y) :
    R.twoDiscCover.cuspPulledBackBoundaryHom x = R.twoDiscCover.cuspPulledBackBoundaryHom y := by
  have h := cuspPulledBackBoundary_eq_zero_of_wang_zero R (x - y)
    (by rw [map_sub, hxy, sub_self])
  rw [map_sub] at h
  exact sub_eq_zero.mp h

end SphereSixComplex.Geometry.AnalyticData.EllipticTwoDiscCoverData
end
end
