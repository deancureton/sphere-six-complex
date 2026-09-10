module
public import SphereSixComplex.Paper.Topology.ConstructedCuspPositiveProjection
public import SphereSixComplex.Paper.Topology.ConstructedA2CentralCompactAction
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Periods SphereSixComplex.Topology
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge CuspPeriodExpansion
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Established
open StandardInfiniteA2ToricModel.Construction CircleProductIdentityMappingTorus
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCuspPositiveProjection_central_action
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (q : ActualLocalCuspCentralOrbitQuotient W) :
    let _ := (constructedCuspPolarData W).positiveDeckAction
    constructedCuspPositiveProjection W
      (actualLocalCuspCentralOrbitMap W (constructedA2CentralCompactOrbitMap W k q)) =
      constructedCuspPositiveProjection W (actualLocalCuspCentralOrbitMap W q) := by
  let _ := (constructedCuspPolarData W).positiveDeckAction
  induction q using Quotient.inductionOn with | h x =>
    exact actualPositiveModulusProjection_central_compact W _ _ _
      (constructedA2EffectivePhaseSection k) x.1 x.2

public def constructedCentralPhaseSweepMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (k : C(UnitAddCircle, Fin 2 → Circle)) :
    C(UnitAddCircle × ActualLocalCuspCentralOrbitQuotient W, actualLocalCuspFilling W) := by
  let F : C((Fin 2 → Circle) × ActualLocalCuspCentralOrbitQuotient W,
      ActualLocalCuspCentralOrbitQuotient W) :=
    ⟨fun p ↦ constructedA2CentralCompactOrbitMap W p.1 p.2,
      constructedA2CentralCompactOrbitMap_continuous W⟩
  let K : C(UnitAddCircle × ActualLocalCuspCentralOrbitQuotient W,
      (Fin 2 → Circle) × ActualLocalCuspCentralOrbitQuotient W) :=
    ⟨fun p ↦ (k p.1, p.2), (k.continuous.comp continuous_fst).prodMk continuous_snd⟩
  exact (⟨actualLocalCuspCentralOrbitMap W,
    (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩ : C(_, _)).comp (F.comp K)

public theorem constructedCuspPositiveProjection_phaseSweep_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (k : C(UnitAddCircle, Fin 2 → Circle))
    (x : IntegralSingularHomology 1 (ActualLocalCuspCentralOrbitQuotient W)) :
    let _ := (constructedCuspPolarData W).positiveDeckAction
    integralSingularHomologyMap 2 (constructedCuspPositiveProjection W)
      (integralSingularHomologyMap 2 (constructedCentralPhaseSweepMap W k)
        (normalizedCircleCross 1 x)) = 0 := by
  let _ := (constructedCuspPolarData W).positiveDeckAction
  dsimp only
  rw [integralSingularHomologyMap_comp_wang]
  let f : C(ActualLocalCuspCentralOrbitQuotient W,
      PolarHoneycombData.OrbitQuotient (constructedCuspPolarData W).positivePart) :=
    (constructedCuspPositiveProjection W).comp
      ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
  have h : (constructedCuspPositiveProjection W).comp (constructedCentralPhaseSweepMap W k) =
      f.comp productFiberProjection := by
    ext p
    exact constructedCuspPositiveProjection_central_action W (k p.1) p.2
  rw [h, ← integralSingularHomologyMap_comp_wang, normalizedCircleCross_projection, map_zero]

end SphereSixComplex.Geometry.CuspStraighteningRetraction
