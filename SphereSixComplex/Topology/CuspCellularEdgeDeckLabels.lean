module
public import SphereSixComplex.Topology.ConstructedA2CellularEdgeLoops
import all SphereSixComplex.LatticeData
import all SphereSixComplex.Topology.StandardA2ToricCentralFiberOneCells

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def centralEdgeEndpointDeck : Fin 3 → ParameterLattice :=
  ![![0,0], ![0,-1], ![1,0]]

public theorem centralEdgeEndpointDeck_shear (j : Fin 3) :
    shearVector (centralEdgeEndpointDeck j) = ![0,-e₁,-e₂] j := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [centralEdgeEndpointDeck, shearVector, B₀, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, e₁, e₂]

public theorem constructedCentralEdge_endpoints_lift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    let F := ![constructedCentralEdgeZeroCarrier, constructedCentralEdgeOneCarrier,
      constructedCentralEdgeTwoCarrier] j
    F (fun _ ↦ -1) = (constructedCentralOrigin W false).1 ∧
      F (fun _ ↦ 1) =
        (((Additive.toMul (centralEdgeEndpointDeck j) : Multiplicative ParameterLattice) • constructedCentralOrigin W true :
          LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  dsimp only
  rw [constructedCentralOrigin_smul_coe]
  change _ ∧ _ = inclusion (true, 0 + shearVector (centralEdgeEndpointDeck j)) 0
  erw [centralEdgeEndpointDeck_shear, zero_add]
  fin_cases j
  · exact ⟨constructedCentralEdgeZeroCarrier_negOne, constructedCentralEdgeZeroCarrier_one⟩
  · exact ⟨constructedCentralEdgeOneCarrier_negOne, constructedCentralEdgeOneCarrier_one⟩
  · exact ⟨constructedCentralEdgeTwoCarrier_negOne, constructedCentralEdgeTwoCarrier_one⟩

public theorem centralCellularBasisDeck (j : Fin 2) :
    centralEdgeEndpointDeck j.castSucc - centralEdgeEndpointDeck 2 =
      ![![-1,0], ![-1,-1]] j := by
  fin_cases j <;> ext i <;> fin_cases i <;> norm_num [centralEdgeEndpointDeck] <;> decide

public theorem constructedCentralEdgeCarrier_continuous (j : Fin 3) :
    Continuous (constructedCentralEdgeCarrier j) := by
  fin_cases j
  · exact constructedCentralEdgeZeroCarrier_continuous
  · exact constructedCentralEdgeOneCarrier_continuous
  · exact constructedCentralEdgeTwoCarrier_continuous

public theorem constructedCentralEdgeCarrier_height (j : Fin 3) (x : Fin 1 → ℝ) :
    carrierHeight (constructedCentralEdgeCarrier j x) = 0 := by
  fin_cases j
  · exact constructedCentralEdgeZeroCarrier_height x
  · exact constructedCentralEdgeOneCarrier_height x
  · exact constructedCentralEdgeTwoCarrier_height x

public def constructedCentralEdgeLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    Path (constructedCentralOrigin W false)
      ((Additive.toMul (centralEdgeEndpointDeck j) : Multiplicative ParameterLattice) •
        constructedCentralOrigin W true) := by
  let _ := actualLocalCuspQuotientAction W
  refine ⟨⟨fun t ↦ ⟨constructedCentralEdgeCarrier j (fun _ ↦ 2 * (t : ℝ) - 1), ?_⟩,
    ?_⟩, ?_, ?_⟩
  · change carrierHeight _ ∈ Metric.ball 0 W.localWitness.radius
    rw [constructedCentralEdgeCarrier_height, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos
  · apply Continuous.subtype_mk
    exact (constructedCentralEdgeCarrier_continuous j).comp (by fun_prop)
  · apply Subtype.ext
    have h := (constructedCentralEdge_endpoints_lift W j).1
    dsimp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
    simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, zero_sub]
    fin_cases j <;> exact h
  · apply Subtype.ext
    have h := (constructedCentralEdge_endpoints_lift W j).2
    dsimp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
    simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one,
      show (2 : ℝ) - 1 = 1 by norm_num]
    fin_cases j <;> exact h

public theorem constructedCentralEdgeLift_projects
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j : Fin 3) (t : unitInterval) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (Quotient.mk _ (constructedCentralEdgeLift W j t) : actualLocalCuspFilling W) =
      actualLocalCuspCentralOrbitMap W
        ((constructedCentralCellularEdgePath W j t).1) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  fin_cases j <;> rfl

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
