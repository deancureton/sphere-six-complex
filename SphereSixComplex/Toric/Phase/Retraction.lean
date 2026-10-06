module

public import SphereSixComplex.Toric.Positive.QuotientInterior
public import SphereSixComplex.Prerequisites.Topology.Covering.PreimageHomotopyEquivalence
public import SphereSixComplex.Toric.Positive.Interior
public import SphereSixComplex.Toric.Positive.RelativeCWCompletion
public import SphereSixComplex.Cusp.Retraction.PhaseCompatibility

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public theorem constructedLocalPositivePart_contractible
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContractibleSpace (constructedLocalPositivePart W.localWitness.radius) := by
  let c := constructedPositiveQuotientCollar W
  let r := W.localWitness.radius
  let X := constructedLocalPositivePart r
  let G := Multiplicative ParameterLattice
  let act := normalizedPositiveDeckAction N constructedModel X (constructedPositiveDeck_mem N r)
  let _ := act
  let π := PolarHoneycombData.orbitProjection X
  let B := positiveQuotientCore W
  let _ := constructedPositiveQuotient_metrizable W
  obtain ⟨w⟩ := c.nonempty_pushWeight (isClosed_positiveDeck_orbitCore W)
  let norm : C((univ : Set (PositiveQuotient W)), ↥(Bᶜ)) :=
    (c.interiorMap w).comp ⟨Subtype.val, continuous_subtype_val⟩
  let d : CoveringPreimageDeformationData Bᶜ univ (subset_univ _) :=
    { normalize := norm
      homotopy :=
        { toFun := fun p ↦ ⟨c.push w.weight (unitInterval.symm p.1) p.2.1, mem_univ _⟩
          continuous_toFun := ((c.continuous_push w.weight w.inner w.closure_subset w.zero_outside).comp
            ((unitInterval.continuous_symm.comp continuous_fst).prodMk
              (continuous_subtype_val.comp continuous_snd))).subtype_mk _
          map_zero_left := by
            intro x
            apply Subtype.ext
            simp [norm, OpenTopologicalCollar.interiorMap, coveringRegionInclusion]
          map_one_left := by
            intro x
            apply Subtype.ext
            simp [c.push_zero] }
      preservesSmall := fun t x ↦ c.push_notMem_boundary w.weight _ x.2 }
  have hinv : ∀ g x, π (actionMap act g x) = π x := by
    intro g x
    apply Quotient.sound
    change MulAction.orbitRel G X (actionMap act g x) x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  let cov := (constructedPositiveDeck_quotientCovering W).isCoveringMap
  let hcont : ContinuousConstSMul G X := constructedPositiveDeck_continuous N r
  let e := d.equivariantHomotopyEquivData act π hinv cov hcont
  let he : CoveringRegionPreimage π Bᶜ ≃ₕ CoveringRegionPreimage π univ :=
    { toFun := e.toFun
      invFun := e.invFun
      left_inv := ⟨e.leftInvHomotopy⟩
      right_inv := ⟨e.rightInvHomotopy⟩ }
  have hpre : π ⁻¹' Bᶜ = {q : X | constructedModel.t q.1.1 = 0}ᶜ := by
    rw [preimage_compl, positiveDeck_central_preimage W]
  let hs : CoveringRegionPreimage π Bᶜ ≃ₜ positiveOffCentral r :=
    Homeomorph.setCongr hpre
  let _ : ContractibleSpace (positiveOffCentral r) :=
    positiveOffCentral_contractible W.localWitness.radius_pos W.localWitness.radius_lt_one
  let _ : ContractibleSpace (CoveringRegionPreimage π Bᶜ) := hs.contractibleSpace
  let _ : ContractibleSpace (CoveringRegionPreimage π univ) := he.symm.contractibleSpace
  let hb : CoveringRegionPreimage π univ ≃ₜ X :=
    (Homeomorph.setCongr (preimage_univ : π ⁻¹' univ = univ)).trans
      (Homeomorph.Set.univ X)
  exact hb.symm.contractibleSpace

public def constructedPolarHoneycombConstruction
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    NormalizedPolarHoneycombConstructionData N constructedModel W.localWitness.radius :=
  polarHoneycombConstructionData_of_contractible W
    (constructedLocalPositivePart_contractible W)

public instance constructedHasCuspPhaseSpreading
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) : HasCuspPhaseSpreading W := by
  let Q := constructedPolarHoneycombConstruction W
  let P := Q.toPolarHoneycombData
  let := P.positiveDeckAction
  let R := P.positiveEquivariantStrongDeformationRetraction
  exact ⟨⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap constructedModel W.localWitness.radius P)
    (PolarPhaseDeckLift.ofNormEq
      (fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i)) R
    (compactPhaseOrbit_homotopy_eq_of_invariantModulus Q
      (constructedLocalModulus_compactPhase W.localWitness.radius) R)⟩⟩⟩

end SphereSixComplex.Geometry.InfiniteA2Toric
