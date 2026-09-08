module
public import SphereSixComplex.Topology.CuspMixedTorusCellularSweeps
public import SphereSixComplex.Topology.ConstructedCuspPositivePhaseVanishing
public import SphereSixComplex.Topology.CuspPhaseCentralCompatibility

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open StandardTorusHomology PositiveCircleCross

public theorem normalizedCircleSweep_projection_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(X,Y)) (a : C(UnitAddCircle × X,X)) (f : C(StdTorus 1,X))
    (h : ∀ t x, p (a (t,f x)) = p (f x)) :
    integralSingularHomologyMap 2 p
      (integralSingularHomologyMap 2 a
        (normalizedCircleCross 1
          (integralSingularHomologyMap 1 f standardCircleHomologyGenerator))) = 0 := by
  have hp : integralSingularHomologyMap 2 (productFiberProjection (X := StdTorus 1))
      positiveCircleProductGenerator = 0 := by
    have hi := positiveCircleCross_projection (ContinuousMap.id (StdTorus 1))
    change integralSingularHomologyMap 2 productFiberProjection
      (integralSingularHomologyMap 2 (ContinuousMap.id _)
        positiveCircleProductGenerator) = 0 at hi
    rwa [integralSingularHomologyMap_id_wang] at hi
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 p
    (integralSingularHomologyMap 2 a
      (integralSingularHomologyMap 2 (circleProductMap f) positiveCircleProductGenerator)) = 0
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  have he : (p.comp a).comp (circleProductMap f) =
      (p.comp f).comp productFiberProjection := by
    ext x
    exact h x.1 x.2
  rw [he, ← integralSingularHomologyMap_comp_wang, hp, map_zero]

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open CuspPuncturedCollarBridge CuspStraighteningRetraction
open StandardInfiniteA2ToricModel.Established CircleProductIdentityMappingTorus
open StandardCircleHomologyLiftDegree

local instance (A : PaperAnalyticData) :
    T2Space (ActualLocalCuspCentralOrbitQuotient A.starCuspWitness) := by
  let _ := actualLocalCuspFilling_t2 A.starCuspWitness
  exact (actualLocalCuspCentralOrbitMap_isEmbedding A.starCuspWitness).t2Space

public theorem cuspCellularGraphSweep_positiveProjection_zero
    (A : PaperAnalyticData) (i : Fin 2) (j k : Fin 3) :
    let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
    integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
      (A.cuspFillingPhaseSweep i
        (loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness j k))) = 0 := by
  let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
  let _ := (constructedCentralCellAtlas A.starCuspWitness).cwComplex
  let p := (constructedCentralCellularEdgePath A.starCuspWitness j).trans
    (constructedCentralCellularEdgePath A.starCuspWitness k).symm
  let inc : C(IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient A.starCuspWitness) 2,
      actualLocalCuspFilling A.starCuspWitness) :=
    ⟨fun x ↦ actualLocalCuspCentralOrbitMap A.starCuspWitness x.1,
      (actualLocalCuspCentralOrbitMap_isEmbedding A.starCuspWitness).continuous.comp
        continuous_subtype_val⟩
  let f := inc.comp (pathCircleMap p)
  have hf : integralSingularHomologyMap 1 f standardCircleHomologyGenerator =
      loopHomologyClass (constructedCellularLoopInFilling A.starCuspWitness j k) := by
    rw [← integralSingularHomologyMap_comp_wang, pathCircleMap_homology,
      integralSingularHomologyMap_loopHomologyClass]
    rfl
  dsimp only
  change integralSingularHomologyMap 2 _
    (integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness i)
      (normalizedCircleCross 1 _)) = 0
  rw [← hf]
  apply normalizedCircleSweep_projection_zero
  intro t x
  change constructedCuspPositiveProjection A.starCuspWitness
    (cuspFillingPeriodCircle A.starCuspWitness i
      (t,actualLocalCuspCentralOrbitMap A.starCuspWitness (pathCircleMap p x).1)) = _
  rw [cuspFillingPeriodCircle_centralOrbit]
  exact constructedCuspPositiveProjection_central_action A.starCuspWitness _ _

public theorem cuspMixedTorus_positiveProjection_zero
    (A : PaperAnalyticData) (j : Fin 3) :
    let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
    integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
      (integralSingularHomologyMap 2
        (A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j))
        standardTwoTorusHomologyGenerator) = 0 := by
  let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
  dsimp only
  rw [cuspMixedTorus_cellularSweeps, map_neg, map_add, map_zsmul, map_zsmul,
    cuspCellularGraphSweep_positiveProjection_zero,
    cuspCellularGraphSweep_positiveProjection_zero]
  simp

end SphereSixComplex.Geometry.PaperAnalyticData
