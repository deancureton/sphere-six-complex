module

public import SphereSixComplex.Topology.ConstructedA2PositiveLocalCollars
public import SphereSixComplex.Topology.ConstructedA2PositiveInteriorContractibility
public import SphereSixComplex.Topology.ConstructedA2PositiveRelativeCWCompletion
public import SphereSixComplex.Topology.HasCuspPhaseSpreading

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedLocalPositivePart_contractible {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) : ContractibleSpace (constructedLocalPositivePart r) := by
  let B : Set (constructedLocalPositivePart r) := {q | constructedModel.t q.1.1 = 0}
  let _ := constructedLocalPositivePart_metrizable r
  have hB : IsClosed B := isClosed_eq
    (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  let _ : ContractibleSpace ↥(Bᶜ) := constructedA2PositiveOffCentral_contractible hr hr1
  obtain ⟨c⟩ := classicalBrownCollaring B (constructedPositiveCentralFiber_locallyCollared r)
  exact c.contractibleSpace hB

public def constructedPolarHoneycombResidualData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ConstructedPolarHoneycombResidualData W :=
  constructedPolarHoneycombResidualData_of_contractible W
    (constructedLocalPositivePart_contractible W.localWitness.radius_pos W.localWitness.radius_lt_one)

public instance constructedHasCuspPhaseSpreading
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) : HasCuspPhaseSpreading W := by
  let T := constructedPolarHoneycombResidualData W
  let Q := T.toTopologicalData.toConstructionData
  let P := Q.toPolarHoneycombData
  have H : PolarPhaseRadialCompatibility N constructedModel W.localWitness.radius P :=
    ⟨fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i⟩
  have G : PolarPhaseGeometricCore constructedModel W.localWitness.radius P :=
    polarPhaseGeometricCore_of_invariantModulus_only Q
      T.toTopologicalData.toConstructionData_invariantModulus
  exact ⟨⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap constructedModel W.localWitness.radius P)
    H.toDeckLift G⟩⟩⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
