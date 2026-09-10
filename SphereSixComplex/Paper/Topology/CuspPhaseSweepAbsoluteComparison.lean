module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepRelativeAction
public import SphereSixComplex.Paper.Topology.PhaseSweepSkeletalHomology
public import SphereSixComplex.Prerequisites.Topology.RelativeClosedPrismProjection

@[expose] public section
noncomputable section
open Set Topology CategoryTheory HomologicalComplex
namespace SphereSixComplex

public def topologicalClosedPrismHomology {X Y : TopCat} {f : X ⟶ Y}
    (H : TopCat.Homotopy f f) (n : ℕ) :
    (CWIntegralSingularChainComplexObj X).homology (n + 1) ⟶
      (CWIntegralSingularChainComplexObj Y).homology (n + 2) :=
  closedPrismHomology (H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) n

namespace Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction
open CuspPeriodExpansion
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem phaseSweepSkeletalPrism_toCentral
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    homologyMap (cwIntegralSingularChainMapObj
        (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1 ≫
      topologicalClosedPrismHomology (constructedA2CircleSweepHomotopy W i) 0 =
    topologicalClosedPrismHomology (phaseSweepSkeletalHomotopy W i) 0 ≫
      homologyMap (cwIntegralSingularChainMapObj
        (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 3)) 2 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact closedPrismHomology_naturality
    ((phaseSweepSkeletalHomotopy W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0 (constructedA2CircleSweepPrism W i)
    (cwIntegralSingularChainMapObj
      (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2))
    (cwIntegralSingularChainMapObj
      (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 3))
    (fun p q ↦ topologicalPrism_naturality (phaseSweepSkeletalHomotopy W i)
      (constructedA2CircleSweepHomotopy W i)
      (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)
      (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 3)
      (by rfl) (AddCommGrpCat.of ℤ) p q)

public theorem phaseSweepSkeletalPrism_relative
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    homologyMap (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1)) 1 ≫
      closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0 =
    topologicalClosedPrismHomology (phaseSweepSkeletalHomotopy W i) 0 ≫
      homologyMap (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2)) 2 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact relativeClosedPrismHomology_projection _ _ _ 0

public theorem phaseSweepCentralPrism_relativeCoordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 2) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ x : IntegralSingularHomology 1
        (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2),
      phaseSweepHomologyTwoToRelativeEquiv W T
        (topologicalClosedPrismHomology (constructedA2CircleSweepHomotopy W i) 0
          (homologyMap (cwIntegralSingularChainMapObj
            (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1 x)) =
      closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0
        (homologyMap (cwRelativeIntegralSingularChainProjection
          (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1)) 1 x) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  intro x
  exact (congrArg (phaseSweepHomologyTwoToRelativeEquiv W T)
    (ConcreteCategory.congr_hom (phaseSweepSkeletalPrism_toCentral W i) x)).trans
    ((phaseSweepHomologyTwoToRelativeEquiv_skeletal W T
      (topologicalClosedPrismHomology (phaseSweepSkeletalHomotopy W i) 0 x)).trans
      (ConcreteCategory.congr_hom (phaseSweepSkeletalPrism_relative W i) x).symm)

end Geometry.CuspPuncturedCollarBridge
end SphereSixComplex
