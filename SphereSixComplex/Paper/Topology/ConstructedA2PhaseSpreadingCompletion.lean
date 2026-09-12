module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveLocalCollars
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveInteriorContractibility
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveRelativeCWCompletion
public import SphereSixComplex.Paper.Topology.HasCuspPhaseSpreading

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public theorem constructedLocalPositivePart_contractible {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) : ContractibleSpace (constructedLocalPositivePart r) := by
  let B : Set (constructedLocalPositivePart r) := {q | constructedModel.t q.1.1 = 0}
  let _ := constructedLocalPositivePart_metrizable r
  have hB : IsClosed B := isClosed_eq
    (constructedModel.t_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  let _ : ContractibleSpace ↥(Bᶜ) := constructedA2PositiveOffCentral_contractible hr hr1
  obtain ⟨c⟩ := LocallyCollared.nonempty_collar B (constructedPositiveCentralFiber_locallyCollared r)
  exact c.contractibleSpace hB

public def constructedPolarHoneycombConstruction
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    NormalizedPolarHoneycombConstructionData N constructedModel W.localWitness.radius :=
  constructedPolarHoneycombConstructionData_of_contractible W
    (constructedLocalPositivePart_contractible W.localWitness.radius_pos W.localWitness.radius_lt_one)

public instance constructedHasCuspPhaseSpreading
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) : HasCuspPhaseSpreading W := by
  let Q := constructedPolarHoneycombConstruction W
  let P := Q.toPolarHoneycombData
  letI := P.positiveDeckAction
  let R := P.positiveEquivariantStrongDeformationRetraction
  exact ⟨⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap constructedModel W.localWitness.radius P)
    (PolarPhaseDeckLift.ofNormEq
      (fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i)) R
    (compactPhaseOrbit_homotopy_eq_of_invariantModulus Q
      (constructedLocalModulus_compactPhase W.localWitness.radius) R)⟩⟩⟩

end SphereSixComplex.Geometry.InfiniteA2Toric
