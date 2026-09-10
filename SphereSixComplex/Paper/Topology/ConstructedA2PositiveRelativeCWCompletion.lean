module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveQuadrantManifold
public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2PositiveDeckSmooth

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedPositiveDeck_contMDiff
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := localPositiveQuadrantChartedSpace W.localWitness.radius
    letI := normalizedPositiveDeckAction N constructedModel
      (constructedLocalPositivePart W.localWitness.radius)
      (constructedPositiveDeck_mem N W.localWitness.radius)
    ∀ g : Multiplicative ParameterLattice,
      ContMDiff (modelWithCornersEuclideanQuadrant 3) (modelWithCornersEuclideanQuadrant 3)
        1 (fun q : constructedLocalPositivePart W.localWitness.radius ↦ g • q) := by
  let _ := positiveQuadrantChartedSpace
  let _ := positiveQuadrantIsManifold
  let _ := localPositiveQuadrantChartedSpace W.localWitness.radius
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  intro g
  let h := SphereSixComplex.transportDiffeomorph
    (I := modelWithCornersEuclideanQuadrant 3) (n := 1)
    (positiveSublevelHomeomorph W.localWitness.radius)
  let f : positiveSublevel W.localWitness.radius → positiveSublevel W.localWitness.radius :=
    fun x ↦ h.symm (g • h x)
  have hf : ContMDiff (modelWithCornersEuclideanQuadrant 3)
      (modelWithCornersEuclideanQuadrant 3) 1 f := by
    have hv : ContMDiff (modelWithCornersEuclideanQuadrant 3)
        (modelWithCornersEuclideanQuadrant 3) 1 (Subtype.val ∘ f) := by
      exact (positiveTorusShear_contMDiff
        (normalizedCuspPositiveTwist N (Multiplicative.toAdd g))
        (normalizedCuspPositiveTwist_real N (Multiplicative.toAdd g))
        (Multiplicative.toAdd g)).comp contMDiff_subtype_val
    intro x
    have hh : ContMDiffWithinAt (modelWithCornersEuclideanQuadrant 3)
        (modelWithCornersEuclideanQuadrant 3) 1 (Subtype.val ∘ f) univ x ↔
      ContMDiffWithinAt (modelWithCornersEuclideanQuadrant 3)
        (modelWithCornersEuclideanQuadrant 3) 1 f univ x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact hh.mp (hv x)
  have hc := h.contMDiff.comp (hf.comp h.symm.contMDiff)
  convert hc using 1 <;> rfl

public def constructedA2PositiveCOneManifoldBoundaryData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ConstructedA2PositiveCOneManifoldBoundaryData W where
  charts := localPositiveQuadrantChartedSpace W.localWitness.radius
  isManifold := localPositiveQuadrantIsManifold W.localWitness.radius
  boundary_eq := localPositiveQuadrant_boundary W.localWitness.radius
  deck_contMDiff := constructedPositiveDeck_contMDiff W

public theorem constructedA2PositiveQuotientRelativeCW
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Nonempty (ConstructedA2PositiveQuotientRelativeCW W) :=
  constructedA2PositiveQuotientRelativeCW_of_cOneManifoldBoundary
    (constructedA2PositiveCOneManifoldBoundaryData W)

public noncomputable def constructedPolarHoneycombResidualData_of_contractible
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : ContractibleSpace (constructedLocalPositivePart W.localWitness.radius)) :
    ConstructedPolarHoneycombResidualData W where
  honeycomb := constructedA2CorrectedHoneycombHomeomorph W.localWitness.radius_pos
  positive_contractible := h
  quotient_relativeCW := (constructedA2PositiveQuotientRelativeCW W).some

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
