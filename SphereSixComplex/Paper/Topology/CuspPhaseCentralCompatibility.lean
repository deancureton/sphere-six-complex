module
public import SphereSixComplex.Paper.Topology.CuspFillingPhaseCircle
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralCompactAction

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods InfiniteA2Toric
open InfiniteA2Toric.Construction InfiniteA2Toric
open CuspCombinatorics CuspPeriodExpansion CuspLocalPhaseAction CuspFilling
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def cuspPeriodCompactCircle (i : Fin 2) (z : UnitAddCircle) : Fin 2 → Circle :=
  fun j ↦ if j = i then AddCircle.toCircle z else 1

public theorem cuspFillingPeriodCircle_centralOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (z : UnitAddCircle) (q : ActualLocalCuspCentralOrbitQuotient W) :
    cuspFillingPeriodCircle W i (z,actualLocalCuspCentralOrbitMap W q) =
      actualLocalCuspCentralOrbitMap W
        (centralCompactOrbitMap W (cuspPeriodCompactCircle i z) q) := by
  let _ := actualLocalCuspQuotientAction W
  induction q using Quotient.inductionOn with
  | _ p =>
    change Quotient.mk _ (localCuspPeriodCircle W i (z,p.1)) =
      Quotient.mk _ (centralCompactMap W (cuspPeriodCompactCircle i z) p).1
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change constructedModel.torusAction _ p.1.1 = constructedModel.torusAction _ p.1.1
    apply congrArg (fun g : DenseTorus ↦ constructedModel.torusAction g p.1.1)
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [CuspToricPhaseAction.phaseEmbedding, cuspPeriodPhaseCircle,
        cuspPeriodCompactCircle, effectivePhaseSection,
        compactTorusEmbedding, CircleExponential.toUnits]

end SphereSixComplex.Geometry.CuspCollar
