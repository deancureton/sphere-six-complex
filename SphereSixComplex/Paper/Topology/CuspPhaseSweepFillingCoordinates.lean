module

public import SphereSixComplex.Paper.Topology.PhaseSweepSkeletalHomology
public import SphereSixComplex.Paper.Topology.CuspCentralFillingHomologyComparison

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open CuspFilling CuspPeriodExpansion StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepFillingHomologyTwoEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (T : IntegralCWCellularHomologyFoundation) :
    IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) :=
  (actualCuspCentralOrbitFillingHomologyEquiv W R 2).symm.trans
    (phaseSweepHomologyTwoCellEquiv W T)

public theorem phaseSweepFillingHomologyTwoEquiv_central
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (T : IntegralCWCellularHomologyFoundation)
    (x : IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W)) :
    phaseSweepFillingHomologyTwoEquiv W R T
      (integralSingularHomologyMap 2
        ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩ x) =
      phaseSweepHomologyTwoCellEquiv W T x := by
  rw [← actualCuspCentralOrbitFillingHomologyEquiv_apply W R 2 x]
  exact congrArg (phaseSweepHomologyTwoCellEquiv W T)
    ((actualCuspCentralOrbitFillingHomologyEquiv W R 2).symm_apply_apply x)

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
