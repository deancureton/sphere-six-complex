module

public import SphereSixComplex.Paper.Topology.ConstructedA2CentralCompactAction
public import SphereSixComplex.Prerequisites.Topology.ClosedHomotopyPrism

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CentralCompactOrbitMap_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : ActualLocalCuspCentralOrbitQuotient W) :
    constructedA2CentralCompactOrbitMap W 1 q = q := by
  let _ := actualLocalCuspQuotientAction W
  induction q using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    apply Subtype.ext
    change constructedModel.torusAction _ p.1.1 = p.1.1
    have h : compactTorusEmbedding (constructedA2EffectivePhaseSection 1) = 1 := by
      ext i
      fin_cases i <;> simp [constructedA2EffectivePhaseSection, compactTorusEmbedding]
    rw [h, map_one, Equiv.Perm.one_apply]

public def continuousActionLoopHomotopy {X G : Type} [TopologicalSpace X]
    [TopologicalSpace G] [One G] (a : ContinuousMap (G × X) X)
    (ha : ∀ x, a (1, x) = x) (c : ContinuousMap unitInterval G)
    (h₀ : c 0 = 1) (h₁ : c 1 = 1) :
    TopCat.Homotopy (𝟙 (TopCat.of X)) (𝟙 (TopCat.of X)) where
  toFun p := a (c p.1, p.2)
  continuous_toFun := a.continuous.comp ((c.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by
    change a (c 0, x) = x
    rw [h₀]
    exact ha x
  map_one_left x := by
    change a (c 1, x) = x
    rw [h₁]
    exact ha x

public def constructedA2CircleSweepParameter (i : Fin 2) : ContinuousMap unitInterval (Fin 2 → Circle) where
  toFun t := constructedA2CircleOnePhase i ![2 * (t : ℝ) - 1]
  continuous_toFun := by
    apply (constructedA2CircleOnePhase_continuous i).comp
    fun_prop

public theorem constructedA2CircleSweepParameter_zero (i : Fin 2) :
    constructedA2CircleSweepParameter i 0 = 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CircleSweepParameter, constructedA2CircleOnePhase, CircleCell.ballParam]

public theorem constructedA2CircleSweepParameter_one (i : Fin 2) :
    constructedA2CircleSweepParameter i 1 = 1 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [constructedA2CircleSweepParameter, constructedA2CircleOnePhase, CircleCell.ballParam]

public def constructedA2CircleSweepHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (𝟙 (TopCat.of (ActualLocalCuspCentralOrbitQuotient W)))
      (𝟙 (TopCat.of (ActualLocalCuspCentralOrbitQuotient W))) :=
  continuousActionLoopHomotopy
    ⟨fun p ↦ constructedA2CentralCompactOrbitMap W p.1 p.2,
      constructedA2CentralCompactOrbitMap_continuous W⟩
    (constructedA2CentralCompactOrbitMap_one W) (constructedA2CircleSweepParameter i)
    (constructedA2CircleSweepParameter_zero i) (constructedA2CircleSweepParameter_one i)

public def constructedA2CircleSweepPrism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  (constructedA2CircleSweepHomotopy W i).singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)

public theorem constructedA2CircleSweepPrism_preserves_boundaries
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (n : ℕ)
    (z : (CWIntegralSingularChainComplexObj (TopCat.of (ActualLocalCuspCentralOrbitQuotient W))).X n)
    (hz : ∃ c, (CWIntegralSingularChainComplexObj
      (TopCat.of (ActualLocalCuspCentralOrbitQuotient W))).d (n + 1) n c = z) :
    ∃ b, (CWIntegralSingularChainComplexObj
      (TopCat.of (ActualLocalCuspCentralOrbitQuotient W))).d (n + 2) (n + 1) b =
        (constructedA2CircleSweepPrism W i).hom n (n + 1) z :=
  closedHomotopyPrism_preserves_boundaries (constructedA2CircleSweepPrism W i) n z hz

public theorem constructedA2CircleSweepHomotopy_positiveCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (b : Fin 2 → ℝ) :
    constructedA2CircleSweepHomotopy W i (t, constructedA2CorrectedPositiveTwoOrbit W b) =
      constructedA2CorrectedThreeOrbit W i (Fin.append b ![2 * (t : ℝ) - 1]) := by
  change constructedA2CentralCompactOrbitMap W _ (constructedA2EffectivePhaseCentralOrbit W _ _) = _
  rw [constructedA2CentralCompactOrbitMap_effectivePhase]
  unfold constructedA2CorrectedThreeOrbit
  rw [constructedA2CorrectedPhaseOrbit_append]
  congr 1
  exact mul_comm _ _

public theorem constructedA2CircleSweepHomotopy_threeCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : unitInterval) (b : Fin 2 → ℝ) (s : ℝ) :
    constructedA2CircleSweepHomotopy W 0
      (t, constructedA2CorrectedThreeOrbit W 1 (Fin.append b ![s])) =
      constructedA2CorrectedFourOrbit W (Fin.append b ![2 * (t : ℝ) - 1, s]) := by
  change constructedA2CentralCompactOrbitMap W _ (constructedA2CorrectedThreeOrbit W 1 _) = _
  unfold constructedA2CorrectedThreeOrbit constructedA2CorrectedFourOrbit
  rw [constructedA2CorrectedPhaseOrbit_append, constructedA2CorrectedPhaseOrbit_append,
    constructedA2CentralCompactOrbitMap_effectivePhase]
  congr 1
  rw [← mul_assoc, mul_comm _ (constructedA2ActualBoundaryGauge _), mul_assoc]
  congr 1
  ext j
  fin_cases j <;>
    simp [constructedA2CircleSweepParameter, constructedA2CircleOnePhase,
      constructedA2CircleTwoPhase, CircleCell.ballParam]

end SphereSixComplex.Geometry.InfiniteA2Toric
