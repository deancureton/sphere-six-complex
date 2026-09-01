module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicQuotientSymmetry

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

private theorem centralPhaseDisk_one_add_ne_zero_of_ball'
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    (1 : ℂ) + centralPhaseDiskComplex x ≠ 0 := by
  intro h
  have hz : centralPhaseDiskComplex x = -1 := eq_neg_of_add_eq_zero_right h
  have hnorm : ‖centralPhaseDiskComplex x‖ < 1 := by
    rw [norm_centralPhaseDiskComplex]
    simpa [Metric.mem_ball, dist_zero_right] using hx
  rw [hz] at hnorm
  norm_num at hnorm

private theorem centralPhaseDisk_one_sub_ne_zero_of_ball'
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    (1 : ℂ) - centralPhaseDiskComplex x ≠ 0 := by
  intro h
  have hz : centralPhaseDiskComplex x = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖centralPhaseDiskComplex x‖ < 1 := by
    rw [norm_centralPhaseDiskComplex]
    simpa [Metric.mem_ball, dist_zero_right] using hx
  rw [hz] at hnorm
  norm_num at hnorm

private theorem centralPhaseDisk_coordinates_reciprocal'
    (x : Fin 2 → ℝ)
    (hplus : (1 : ℂ) + centralPhaseDiskComplex x ≠ 0)
    (hminus : (1 : ℂ) - centralPhaseDiskComplex x ≠ 0) :
    centralPhaseDiskLowerCoordinate x ≠ 0 ∧
      centralPhaseDiskUpperCoordinate x = (centralPhaseDiskLowerCoordinate x)⁻¹ := by
  have hratio : (1 + centralPhaseDiskComplex x) /
      (1 - centralPhaseDiskComplex x) ≠ 0 := div_ne_zero hplus hminus
  refine ⟨neg_ne_zero.mpr (pow_ne_zero 2 hratio), ?_⟩
  apply eq_inv_of_mul_eq_one_left
  simp only [centralPhaseDiskLowerCoordinate, centralPhaseDiskUpperCoordinate]
  field_simp [hplus, hminus]

private theorem singleAxis_component_iff'
    (a : ChartIndex) (k : Fin 3) (z : ℂ) (hz : z ≠ 0) (v : ToricLattice) :
    inclusion a (singleAxis k z) ∈ carrierCentralComponent v ↔
      ∃ i : Fin 3, i ≠ k ∧ v = a2Triangle a.1 a.2 i := by
  let _ := chartedSpace
  have hchart : inclusion a (singleAxis k z) ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self _
  constructor
  · intro hp
    have hv : v ∈ Set.range (a2Triangle a.1 a.2) := by
      by_contra hn
      exact Set.disjoint_left.mp
        (otherCarrierCentralComponent_disjoint_chart a v hn) hp hchart
    obtain ⟨i, rfl⟩ := hv
    have hzero := (carrierCentralComponent_in_chart a i _ hchart).mp hp
    rw [toricChart_inclusion] at hzero
    have hik : i ≠ k := by
      intro h
      subst i
      simp [rawToComplexModel, singleAxis, hz] at hzero
    exact ⟨i, hik, rfl⟩
  · rintro ⟨i, hik, rfl⟩
    apply (carrierCentralComponent_in_chart a i _ hchart).mpr
    rw [toricChart_inclusion]
    simp [rawToComplexModel, singleAxis, hik]

public theorem constructedCentralPhaseFaceOneCarrier_componentSupport
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralPhaseFaceOneCarrier x) =
      ({0, e₂} : Set ToricLattice) := by
  by_cases hx0 : x 0 ≤ 0
  · have hn : centralPhaseDiskLowerCoordinate x ≠ 0 :=
      (centralPhaseDisk_coordinates_reciprocal' x
        (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).1
    simp only [constructedCentralPhaseFaceOneCarrier, hx0]
    ext v
    change inclusion (false, 0) (singleAxis 1 (centralPhaseDiskLowerCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₂} : Set ToricLattice)
    rw [singleAxis_component_iff' _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by simp [a2Triangle, e₁, e₂]⟩
  · have hn : centralPhaseDiskUpperCoordinate x ≠ 0 := by
      rw [(centralPhaseDisk_coordinates_reciprocal' x
        (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).2]
      exact inv_ne_zero
        (centralPhaseDisk_coordinates_reciprocal' x
          (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
          (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).1
    simp only [constructedCentralPhaseFaceOneCarrier, hx0]
    ext v
    change inclusion (true, -e₁) (singleAxis 1 (centralPhaseDiskUpperCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₂} : Set ToricLattice)
    rw [singleAxis_component_iff' _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩

private theorem centralOrbitRel_coe_eq_of_same_componentSupport'
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (T : Set ToricLattice) (hTfinite : T.Finite) (hTnonempty : T.Nonempty)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel
      ((p : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = T)
    (hq : componentSupport constructedModel
      ((q : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = T)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    ((p : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      ((q : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  have hphase := hcarrier
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (q : LocalCarrier constructedModel W.localWitness.radius) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hphase
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hphase
  have hforward : ∀ v ∈ T, v + shearVector lambda ∈ T := by
    intro v hv
    have hvq : v ∈ componentSupport constructedModel
        ((q : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) := by
      rw [hq]
      exact hv
    have hfan : Additive.toMul (constructedModel.fanShear lambda)
        ((q : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) ∈
          constructedModel.centralComponent (v + shearVector lambda) := by
      rw [← constructedModel.fanShear_component lambda v]
      exact ⟨_, hvq, rfl⟩
    have hphaseComponent :
        CuspToricPhaseAction.ToricModel.phaseAction constructedModel
          (C.phase lambda (constructedModel.t
            (q : LocalCarrier constructedModel W.localWitness.radius)))
          (Additive.toMul (constructedModel.fanShear lambda)
            (q : LocalCarrier constructedModel W.localWitness.radius)) ∈
              constructedModel.centralComponent (v + shearVector lambda) :=
      (constructedModel.torusAction_centralComponent _ _ _).mpr hfan
    rw [hphase] at hphaseComponent
    rw [← hp]
    exact hphaseComponent
  have hshear : shearVector lambda = 0 :=
    translation_eq_zero_of_finite_forward_invariant hTfinite hTnonempty hforward
  have hlambda : lambda = 0 := by
    apply shearVector_injective
    rw [hshear]
    ext i
    simp [shearVector, Matrix.mulVec]
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (q : LocalCarrier constructedModel W.localWitness.radius) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, hlambda, C.psiMap_zero] at hcarrier
  exact hcarrier.symm

public theorem constructedCentralPhaseFaceOneOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralPhaseFaceOneOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralPhaseFaceOnePoint W x)
      (constructedCentralPhaseFaceOnePoint W y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralPhaseFaceOnePoint W x)
      (constructedCentralPhaseFaceOnePoint W y) hxy
  have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport' W
    ({0, e₂} : Set ToricLattice) ((Set.finite_singleton e₂).insert 0)
      ⟨0, by simp⟩
      (constructedCentralPhaseFaceOnePoint W x)
      (constructedCentralPhaseFaceOnePoint W y)
      (constructedCentralPhaseFaceOneCarrier_componentSupport x hx)
      (constructedCentralPhaseFaceOneCarrier_componentSupport y hy) hrel
  exact constructedCentralPhaseFaceOneCarrier_injOn hx hy hcoe

public def constructedCentralPhaseTwoCellOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralPhaseFaceOneOrbit W) (Metric.ball 0 1)
    (constructedCentralPhaseFaceOneOrbit_injOn W)

public theorem constructedCentralPhaseTwoCellOne_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralPhaseTwoCellOne W).source = Metric.ball 0 1 := rfl

public theorem constructedCentralPhaseTwoCellOne_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellOne W) (Metric.closedBall 0 1) :=
  constructedCentralPhaseFaceOneOrbit_continuousOn_closedBall W

public theorem constructedCentralPhaseFaceTwoCarrier_componentSupport
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralPhaseFaceTwoCarrier x) =
      ({0, e₁} : Set ToricLattice) := by
  by_cases hx0 : x 0 ≤ 0
  · have hn : centralPhaseDiskLowerCoordinate x ≠ 0 :=
      (centralPhaseDisk_coordinates_reciprocal' x
        (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).1
    simp only [constructedCentralPhaseFaceTwoCarrier, hx0]
    ext v
    change inclusion (false, 0) (singleAxis 2 (centralPhaseDiskLowerCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₁} : Set ToricLattice)
    rw [singleAxis_component_iff' _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨1, by decide, by simp [a2Triangle, e₁, e₂]⟩
  · have hn : centralPhaseDiskUpperCoordinate x ≠ 0 := by
      rw [(centralPhaseDisk_coordinates_reciprocal' x
        (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).2]
      exact inv_ne_zero
        (centralPhaseDisk_coordinates_reciprocal' x
          (centralPhaseDisk_one_add_ne_zero_of_ball' hx)
          (centralPhaseDisk_one_sub_ne_zero_of_ball' hx)).1
    simp only [constructedCentralPhaseFaceTwoCarrier, hx0]
    ext v
    change inclusion (true, -e₂) (singleAxis 0 (centralPhaseDiskUpperCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₁} : Set ToricLattice)
    rw [singleAxis_component_iff' _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨1, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩

public theorem constructedCentralPhaseFaceTwoOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralPhaseFaceTwoOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralPhaseFaceTwoPoint W x)
      (constructedCentralPhaseFaceTwoPoint W y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralPhaseFaceTwoPoint W x)
      (constructedCentralPhaseFaceTwoPoint W y) hxy
  have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport' W
    ({0, e₁} : Set ToricLattice) ((Set.finite_singleton e₁).insert 0)
      ⟨0, by simp⟩
      (constructedCentralPhaseFaceTwoPoint W x)
      (constructedCentralPhaseFaceTwoPoint W y)
      (constructedCentralPhaseFaceTwoCarrier_componentSupport x hx)
      (constructedCentralPhaseFaceTwoCarrier_componentSupport y hy) hrel
  exact constructedCentralPhaseFaceTwoCarrier_injOn hx hy hcoe

public def constructedCentralPhaseTwoCellTwo
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralPhaseFaceTwoOrbit W) (Metric.ball 0 1)
    (constructedCentralPhaseFaceTwoOrbit_injOn W)

public theorem constructedCentralPhaseTwoCellTwo_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralPhaseTwoCellTwo W).source = Metric.ball 0 1 := rfl

public theorem constructedCentralPhaseTwoCellTwo_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellTwo W) (Metric.closedBall 0 1) :=
  constructedCentralPhaseFaceTwoOrbit_continuousOn_closedBall W

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
