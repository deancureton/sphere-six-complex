module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveCoverPhaseCompletion

/-!
# Source compatibility for the adaptive cusp overlap

The endpoint-corrected phase realizes the genuine order-four/order-three cover as a pullback
of the standard vertex--edge cover.  This file records the resulting source-side identity in
the collar coordinates used by the actual cusp Wang boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- Reading the swapped adaptive boundary and then transporting from the actual cusp collar is
exactly the cusp Wang boundary. -/
public theorem actualCuspAdaptiveOverlapRead_boundary_eq_wang
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((actualCuspAdaptiveCoverDegreeOneSelfMap R).actualSourceRead.comp
        ((actualCuspMappingTorusPulledBackSwappedHomologyComparison R).boundaryHom 1)).comp
      (integralSingularHomologyEquivOfHomotopyEquiv
        2 G.totalHomotopyEquiv).toAddMonoidHom =
      actualCuspWangBoundaryHom A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspAdaptiveCover_actual_boundary_eq_wang]
  rfl

/-- Returning the pulled-back cover from its marked order to the order dictated by the adaptive
phase contributes exactly one minus sign before the low-overlap read. -/
public theorem actualCuspAdaptiveOverlapRead_marked_boundary_eq_neg_wang
    (R : A.SectionSevenAffineRadialCompletionInput) :
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
    (actualCuspAdaptiveCoverDegreeOneSelfMap R).actualSourceRead.comp
        (swap.comp
          ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1)) =
      -(circleMappingTorusWangPresentationOfCover G.clutching 1).boundary := by
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
  have hswap := congrArg ConcreteCategory.hom
    (actualCuspMappingTorusPulledBack_boundary_swap R 1)
  change swap.comp
      ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1) =
    -((actualCuspMappingTorusPulledBackSwappedHomologyComparison R).boundaryHom 1) at hswap
  change (actualCuspAdaptiveCoverDegreeOneSelfMap R).actualSourceRead.comp
      (swap.comp
        ((actualCuspMappingTorusPulledBackHomologyComparison R).boundaryHom 1)) =
    -(circleMappingTorusWangPresentationOfCover G.clutching 1).boundary
  rw [hswap]
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply]
  rw [map_neg]
  exact congrArg Neg.neg (DFunLike.congr_fun
    (actualCuspAdaptiveCover_actual_boundary_eq_wang R) x)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
