module
public import SphereSixComplex.Paper.Topology.CuspMixedPhaseTorus
public import SphereSixComplex.Paper.Topology.CuspBoundaryMixedTori
public import SphereSixComplex.Paper.Topology.ConstructedCuspPositivePhaseVanishing
public import SphereSixComplex.Paper.Topology.CuspPhaseCentralCompatibility

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

namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open CuspCollar CuspStraighteningRetraction
open InfiniteA2Toric CircleProductIdentityMappingTorus
open StandardCircleHomologyLiftDegree

public theorem cuspBoundarySweep_positiveProjection_zero
    (A : AnalyticData) (i : Fin 2) {x : Construction.CentralBoundary.Spheres} (p : Path x x) :
    let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
    integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
      (A.cuspFillingPhaseSweep i
        (loopHomologyClass (p.map (Construction.CentralBoundary.toFilling A.starCuspWitness).continuous))) = 0 := by
  let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
  let inc := Construction.CentralBoundary.toFilling A.starCuspWitness
  let f := inc.comp (pathCircleMap p)
  have hf : integralSingularHomologyMap 1 f standardCircleHomologyGenerator =
      loopHomologyClass (p.map inc.continuous) := by
    rw [← integralSingularHomologyMap_comp_wang, pathCircleMap_homology,
      integralSingularHomologyMap_loopHomologyClass]
  dsimp only
  change integralSingularHomologyMap 2 _
    (integralSingularHomologyMap 2 (cuspFillingPeriodCircle A.starCuspWitness i)
      (normalizedCircleCross 1 _)) = 0
  rw [← hf]
  apply normalizedCircleSweep_projection_zero
  intro t z
  change constructedCuspPositiveProjection A.starCuspWitness
    (cuspFillingPeriodCircle A.starCuspWitness i
      (t,actualLocalCuspCentralOrbitMap A.starCuspWitness
        (Construction.CentralBoundary.homeomorph A.starCuspWitness (pathCircleMap p z)))) = _
  rw [cuspFillingPeriodCircle_centralOrbit]
  exact constructedCuspPositiveProjection_central_action A.starCuspWitness _ _

public theorem cuspMixedTorus_positiveProjection_zero
    (A : AnalyticData) (j : Fin 3) :
    let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
    integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
      (integralSingularHomologyMap 2
        (A.cuspFiniteFiberTorusToFilling (cuspMixedTorusIndex j))
        standardTwoTorusHomologyGenerator) = 0 := by
  let _ := (constructedCuspPolarData A.starCuspWitness).positiveDeckAction
  dsimp only
  change integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
    (integralSingularHomologyMap 2
      (A.cuspFiniteFiberTorusToFilling (BoundaryMixedTori.index j))
      standardTwoTorusHomologyGenerator) = 0
  rw [BoundaryMixedTori.torus_homology, map_neg, map_add, map_zsmul, map_zsmul,
    cuspBoundarySweep_positiveProjection_zero, cuspBoundarySweep_positiveProjection_zero]
  simp

end SphereSixComplex.Geometry.AnalyticData
