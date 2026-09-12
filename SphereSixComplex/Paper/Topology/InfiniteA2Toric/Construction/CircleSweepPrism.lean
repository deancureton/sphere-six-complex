module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralCompactAction
public import SphereSixComplex.Prerequisites.Topology.ContinuousMapLoopHomotopy
public import SphereSixComplex.Prerequisites.Topology.ClosedHomotopyPrism

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem centralCompactOrbitMap_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : ActualLocalCuspCentralOrbitQuotient W) :
    centralCompactOrbitMap W 1 q = q := by
  let _ := actualLocalCuspQuotientAction W
  induction q using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    apply Subtype.ext
    change constructedModel.torusAction _ p.1.1 = p.1.1
    have h : compactTorusEmbedding (effectivePhaseSection 1) = 1 := by
      ext i
      fin_cases i <;> simp [effectivePhaseSection, compactTorusEmbedding]
    rw [h, map_one, Equiv.Perm.one_apply]

public def circleSweepParameter (i : Fin 2) : ContinuousMap unitInterval (Fin 2 → Circle) where
  toFun t := CircleCell.onePhase i ![2 * (t : ℝ) - 1]
  continuous_toFun := by
    apply (CircleCell.continuous_onePhase i).comp
    fun_prop

public theorem circleSweepParameter_zero (i : Fin 2) :
    circleSweepParameter i 0 = 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [circleSweepParameter, CircleCell.onePhase, CircleCell.ballParam]

public theorem circleSweepParameter_one (i : Fin 2) :
    circleSweepParameter i 1 = 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [circleSweepParameter, CircleCell.onePhase, CircleCell.ballParam]

public def circleSweepHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (𝟙 (TopCat.of (ActualLocalCuspCentralOrbitQuotient W)))
      (𝟙 (TopCat.of (ActualLocalCuspCentralOrbitQuotient W))) :=
  ContinuousMap.homotopyOfLoop
    ⟨fun p ↦ centralCompactOrbitMap W p.1 p.2,
      continuous_centralCompactOrbitMap W⟩
    (centralCompactOrbitMap_one W)
    { toContinuousMap := circleSweepParameter i
      source' := circleSweepParameter_zero i
      target' := circleSweepParameter_one i }

public def circleSweepPrism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  (circleSweepHomotopy W i).singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)


public theorem circleSweepHomotopy_positiveCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (b : Fin 2 → ℝ) :
    circleSweepHomotopy W i (t, correctedPositiveTwoOrbit W b) =
      correctedThreeOrbit W i (Fin.append b ![2 * (t : ℝ) - 1]) := by
  change centralCompactOrbitMap W _ (effectivePhaseCentralOrbit W _ _) = _
  rw [centralCompactOrbitMap_effectivePhase]
  unfold correctedThreeOrbit
  rw [correctedPhaseOrbit_append]
  congr 1
  exact mul_comm _ _


end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
