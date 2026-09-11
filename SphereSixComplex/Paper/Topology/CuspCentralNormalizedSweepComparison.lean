module

public import SphereSixComplex.Prerequisites.Topology.UniversalCirclePrism
public import SphereSixComplex.Paper.Topology.CuspPhaseCentralCompatibility
public import SphereSixComplex.Paper.Topology.ConstructedA2CircleSweepPrism
public import SphereSixComplex.Paper.Topology.CuspCellularLoopDeckComparison

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology MonoidalCategory
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex SphereSixComplex.Periods
open CuspFilling CuspPeriodExpansion InfiniteA2Toric
open InfiniteA2Toric.Construction InfiniteA2Toric
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open SphereSixComplex.StandardTorusHomology
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CircleSweepParameter_period (i : Fin 2) (t : unitInterval) :
    constructedA2CircleSweepParameter i t = cuspPeriodCompactCircle i ((t : ℝ) : UnitAddCircle) := by
  have h : CircleCell.ballParam ![2 * (t : ℝ) - 1] =
      AddCircle.toCircle ((t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.toCircle_apply_mk]
    change Circle.exp (Real.pi * ((2 * (t : ℝ) - 1) + 1)) = _
    congr 1
    simp
    ring
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CircleSweepParameter, constructedA2CircleOnePhase,
      cuspPeriodCompactCircle, h]

public theorem constructedA2CircleSweep_filling
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (q : ActualLocalCuspCentralOrbitQuotient W) :
    actualLocalCuspCentralOrbitMap W (constructedA2CircleSweepHomotopy W i (t, q)) =
      cuspFillingPeriodCircle W i (((t : ℝ) : UnitAddCircle), actualLocalCuspCentralOrbitMap W q) := by
  rw [cuspFillingPeriodCircle_centralOrbit]
  change actualLocalCuspCentralOrbitMap W
    (constructedA2CentralCompactOrbitMap W (constructedA2CircleSweepParameter i t) q) = _
  rw [constructedA2CircleSweepParameter_period]

public theorem constructedA2CirclePrism_filling
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (x : IntegralSingularHomology 1 (ActualLocalCuspCentralOrbitQuotient W)) :
    integralSingularHomologyMap 2
      ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
      (closedPrismHomology (constructedA2CircleSweepPrism W i) 0 x) =
    closedPrismHomology ((circleSweepHomotopy (cuspFillingPeriodCircle W i)).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0
      (integralSingularHomologyMap 1
        ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩ x) := by
  let f : TopCat.of (ActualLocalCuspCentralOrbitQuotient W) ⟶ TopCat.of (ActualLocalCuspFilling W) :=
    TopCat.ofHom ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
  have h := closedPrismHomology_naturality (constructedA2CircleSweepPrism W i) 0
    ((circleSweepHomotopy (cuspFillingPeriodCircle W i)).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ))
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f)
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f)
    (fun p q ↦ topologicalPrism_naturality (constructedA2CircleSweepHomotopy W i)
      (circleSweepHomotopy (cuspFillingPeriodCircle W i)) f f (by
        ext z
        exact (constructedA2CircleSweep_filling W i (TopCat.I.homeomorph z.2) z.1).symm)
      (AddCommGrpCat.of ℤ) p q)
  exact (ConcreteCategory.congr_hom h x).symm

public theorem constructedA2CirclePrism_normalized_of_sign
    (n : ℤ) (hn : universalCirclePrismClass = n • standardTwoTorusHomologyGenerator)
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    {q : ActualLocalCuspCentralOrbitQuotient W} (p : Path q q) :
    integralSingularHomologyMap 2
      ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
      (closedPrismHomology (constructedA2CircleSweepPrism W i) 0 (loopHomologyClass p)) =
    n • integralSingularHomologyMap 2 (cuspFillingPeriodCircle W i)
      (normalizedCircleCross 1
        (integralSingularHomologyMap 1
          ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
          (loopHomologyClass p))) := by
  rw [constructedA2CirclePrism_filling, integralSingularHomologyMap_loopHomologyClass]
  rw [← pathCircleMap_homology]
  exact circleSweepPrism_eq_of_universal_sign n hn (cuspFillingPeriodCircle W i) _

public theorem constructedA2GraphPrism_normalized_of_sign
    (n : ℤ) (hn : universalCirclePrismClass = n • standardTwoTorusHomologyGenerator)
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) (j k : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    integralSingularHomologyMap 2
      ⟨actualLocalCuspCentralOrbitMap W, (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous⟩
      (closedPrismHomology (constructedA2CircleSweepPrism W i) 0
        (loopHomologyClass (((constructedCentralCellularEdgePath W j).trans
          (constructedCentralCellularEdgePath W k).symm).map continuous_subtype_val))) =
      n • integralSingularHomologyMap 2 (cuspFillingPeriodCircle W i)
        (normalizedCircleCross 1 (loopHomologyClass (constructedCellularLoopInFilling W j k))) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  dsimp only
  have h := constructedA2CirclePrism_normalized_of_sign n hn W i
    (((constructedCentralCellularEdgePath W j).trans
      (constructedCentralCellularEdgePath W k).symm).map continuous_subtype_val)
  rw [integralSingularHomologyMap_loopHomologyClass] at h
  exact h


end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
