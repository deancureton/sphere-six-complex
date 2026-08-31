module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicSymmetry

/-!
# Cyclic symmetry on the local central-fibre quotient

The order-three carrier rotation preserves the height character.  It therefore restricts to
every local cusp carrier and to its central fibre.
-/

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
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem rawHeight_a2CyclicRaw (upper : Bool) (z : RawCoordinates) :
    rawHeight (a2CyclicRaw upper z) = rawHeight z := by
  cases upper <;>
    simp [a2CyclicRaw, a2CyclicRawLower, a2CyclicRawUpper, rawHeight] <;> ring

/-- The cyclic carrier rotation preserves the toric height character exactly. -/
@[simp]
public theorem carrierHeight_a2CyclicCarrier (p : Carrier) :
    carrierHeight (a2CyclicCarrier p) = carrierHeight p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [a2CyclicCarrier_inclusion, carrierHeight_inclusion, carrierHeight_inclusion]
  exact rawHeight_a2CyclicRaw a.1 z

public noncomputable def a2CyclicConstructedCarrier
    (p : constructedModel.Carrier) : constructedModel.Carrier := by
  change Carrier at p ⊢
  exact a2CyclicCarrier p

@[simp]
public theorem constructedModel_t_a2CyclicConstructedCarrier
    (p : constructedModel.Carrier) :
    constructedModel.t (a2CyclicConstructedCarrier p) = constructedModel.t p := by
  change carrierHeight (a2CyclicCarrier p) = carrierHeight p
  exact carrierHeight_a2CyclicCarrier p

public theorem a2CyclicConstructedCarrier_continuous :
    Continuous a2CyclicConstructedCarrier := by
  change Continuous a2CyclicCarrier
  exact a2CyclicCarrier_continuous

@[simp]
public theorem a2CyclicConstructedCarrier_apply_three (p : constructedModel.Carrier) :
    a2CyclicConstructedCarrier
        (a2CyclicConstructedCarrier (a2CyclicConstructedCarrier p)) = p := by
  change a2CyclicCarrier (a2CyclicCarrier (a2CyclicCarrier p)) = p
  exact a2CyclicCarrier_apply_three p

/-- The carrier rotation restricted to an arbitrary local cusp neighbourhood. -/
public noncomputable def a2CyclicLocalCarrierHomeomorph (r : ℝ) :
    LocalCarrier constructedModel r ≃ₜ LocalCarrier constructedModel r where
  toFun p := ⟨a2CyclicConstructedCarrier p, by
    change constructedModel.t (a2CyclicConstructedCarrier p) ∈ Metric.ball 0 r
    rw [constructedModel_t_a2CyclicConstructedCarrier]
    exact p.property⟩
  invFun p := ⟨a2CyclicConstructedCarrier (a2CyclicConstructedCarrier p), by
    change constructedModel.t
      (a2CyclicConstructedCarrier (a2CyclicConstructedCarrier p)) ∈ Metric.ball 0 r
    rw [constructedModel_t_a2CyclicConstructedCarrier,
      constructedModel_t_a2CyclicConstructedCarrier]
    exact p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact a2CyclicConstructedCarrier_apply_three p
  right_inv p := by
    apply Subtype.ext
    exact a2CyclicConstructedCarrier_apply_three p
  continuous_toFun :=
    (a2CyclicConstructedCarrier_continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (a2CyclicConstructedCarrier_continuous.comp
      (a2CyclicConstructedCarrier_continuous.comp continuous_subtype_val)).subtype_mk _

@[simp]
public theorem a2CyclicLocalCarrierHomeomorph_coe (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    ((a2CyclicLocalCarrierHomeomorph r p : LocalCarrier constructedModel r) :
      constructedModel.Carrier) = a2CyclicConstructedCarrier p :=
  rfl

@[simp]
public theorem a2CyclicLocalCarrierHomeomorph_apply_three (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    a2CyclicLocalCarrierHomeomorph r
        (a2CyclicLocalCarrierHomeomorph r (a2CyclicLocalCarrierHomeomorph r p)) = p := by
  apply Subtype.ext
  exact a2CyclicConstructedCarrier_apply_three p

/-- The local carrier rotation restricted to the height-zero fibre. -/
public noncomputable def a2CyclicLocalCentralFiberHomeomorph (r : ℝ) :
    {p : LocalCarrier constructedModel r // constructedModel.t p = 0} ≃ₜ
      {p : LocalCarrier constructedModel r // constructedModel.t p = 0} where
  toFun p := ⟨a2CyclicLocalCarrierHomeomorph r p, by
    rw [a2CyclicLocalCarrierHomeomorph_coe,
      constructedModel_t_a2CyclicConstructedCarrier]
    exact p.property⟩
  invFun p := ⟨(a2CyclicLocalCarrierHomeomorph r).symm p, by
    change constructedModel.t
      (a2CyclicConstructedCarrier (a2CyclicConstructedCarrier p)) = 0
    rw [constructedModel_t_a2CyclicConstructedCarrier,
      constructedModel_t_a2CyclicConstructedCarrier]
    exact p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact (a2CyclicLocalCarrierHomeomorph r).symm_apply_apply p
  right_inv p := by
    apply Subtype.ext
    exact (a2CyclicLocalCarrierHomeomorph r).apply_symm_apply p
  continuous_toFun :=
    ((a2CyclicLocalCarrierHomeomorph r).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((a2CyclicLocalCarrierHomeomorph r).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp]
public theorem constructedCentralPhaseFaceOneCarrier_height (x : Fin 2 → ℝ) :
    carrierHeight (constructedCentralPhaseFaceOneCarrier x) = 0 := by
  rw [← a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier,
    carrierHeight_a2CyclicCarrier, constructedCentralPhaseFaceZeroCarrier_height]

@[simp]
public theorem constructedCentralPhaseFaceTwoCarrier_height (x : Fin 2 → ℝ) :
    carrierHeight (constructedCentralPhaseFaceTwoCarrier x) = 0 := by
  rw [← a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier,
    carrierHeight_a2CyclicCarrier, carrierHeight_a2CyclicCarrier,
    constructedCentralPhaseFaceZeroCarrier_height]

/-- The parameter-lattice automorphism induced by cyclic rotation of fan translations. -/
public noncomputable def a2CyclicParameter (lambda : ParameterLattice) : ParameterLattice :=
  Classical.choose (shearVector_surjective (a2CyclicLinear (shearVector lambda)))

@[simp]
public theorem shearVector_a2CyclicParameter (lambda : ParameterLattice) :
    shearVector (a2CyclicParameter lambda) = a2CyclicLinear (shearVector lambda) :=
  Classical.choose_spec (shearVector_surjective (a2CyclicLinear (shearVector lambda)))

@[simp]
public theorem a2CyclicParameter_zero : a2CyclicParameter 0 = 0 := by
  apply shearVector_injective
  rw [shearVector_a2CyclicParameter]
  simp [shearVector]

public theorem a2CyclicParameter_add (lambda mu : ParameterLattice) :
    a2CyclicParameter (lambda + mu) =
      a2CyclicParameter lambda + a2CyclicParameter mu := by
  apply shearVector_injective
  rw [shearVector_a2CyclicParameter]
  rw [show shearVector (a2CyclicParameter lambda + a2CyclicParameter mu) =
      shearVector (a2CyclicParameter lambda) + shearVector (a2CyclicParameter mu) by
    exact Matrix.mulVec_add _ _ _]
  rw [shearVector_a2CyclicParameter, shearVector_a2CyclicParameter]
  rw [show shearVector (lambda + mu) = shearVector lambda + shearVector mu by
    exact Matrix.mulVec_add _ _ _]
  rw [a2CyclicLinear_add]

@[simp]
public theorem a2CyclicParameter_apply_three (lambda : ParameterLattice) :
    a2CyclicParameter (a2CyclicParameter (a2CyclicParameter lambda)) = lambda := by
  apply shearVector_injective
  rw [shearVector_a2CyclicParameter, shearVector_a2CyclicParameter,
    shearVector_a2CyclicParameter, a2CyclicLinear_apply_three]

/-- The order-three automorphism of deck parameters induced by fan rotation. -/
public noncomputable def a2CyclicParameterEquiv : ParameterLattice ≃+ ParameterLattice where
  toFun := a2CyclicParameter
  invFun := a2CyclicParameter ∘ a2CyclicParameter
  left_inv := a2CyclicParameter_apply_three
  right_inv := a2CyclicParameter_apply_three
  map_add' := a2CyclicParameter_add

public theorem a2CyclicChartIndex_translate (lambda : ParameterLattice) (a : ChartIndex) :
    a2CyclicChartIndex (translateChartIndex lambda a) =
      translateChartIndex (a2CyclicParameter lambda) (a2CyclicChartIndex a) := by
  rcases a with ⟨upper, v⟩
  cases upper
  · apply Prod.ext
    · simp [a2CyclicChartIndex, translateChartIndex]
    · simp [a2CyclicChartIndex, translateChartIndex, a2CyclicLinear_add]
  · apply Prod.ext
    · simp [a2CyclicChartIndex, translateChartIndex]
    · simp only [a2CyclicChartIndex, translateChartIndex, ↓reduceIte,
        shearVector_a2CyclicParameter, a2CyclicLinear_add]
      abel

/-- Cyclic rotation conjugates fan translation by the induced parameter automorphism. -/
public theorem a2CyclicCarrier_carrierFanShearFun
    (lambda : ParameterLattice) (p : Carrier) :
    a2CyclicCarrier (carrierFanShearFun lambda p) =
      carrierFanShearFun (a2CyclicParameter lambda) (a2CyclicCarrier p) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierFanShearFun_inclusion, a2CyclicCarrier_inclusion,
    a2CyclicCarrier_inclusion, carrierFanShearFun_inclusion,
    a2CyclicChartIndex_translate]
  rfl

/-- The dense-torus automorphism induced by the cyclic fan rotation. -/
public def a2CyclicDenseTorus (g : DenseTorus) : DenseTorus :=
  ![(g 0)⁻¹ * (g 1)⁻¹ * g 2, g 0, g 2]

private theorem a2CyclicRaw_torusChartCoordinates_only
    (a : ChartIndex) (g : DenseTorus) :
    a2CyclicRaw a.1 (torusChartCoordinates a g) =
      torusChartCoordinates (a2CyclicChartIndex a) (a2CyclicDenseTorus g) := by
  rcases a with ⟨upper, v⟩
  cases upper <;> funext i <;> fin_cases i <;>
    simp [a2CyclicRaw, a2CyclicRawLower, a2CyclicRawUpper,
      a2CyclicChartIndex, a2CyclicLinear, a2CyclicDenseTorus,
      torusChartCoordinates, denseRawCoordinates, monomial, dualMatrix,
      a2DualCharacter, Fin.prod_univ_succ, e₁]
  all_goals
    field_simp [Units.ne_zero]
  next =>
    rw [← zpow_add₀ (Units.ne_zero (g 2))]
    convert (zpow_one (g 2 : ℂ)).symm using 1
    all_goals ring_nf
  next =>
    calc
      (g 2 : ℂ) ^ (v 0 + v 1 + 1) =
          (g 2 : ℂ) ^ (v 0 + v 1) * (g 2 : ℂ) ^ (1 : ℤ) :=
        zpow_add₀ (Units.ne_zero (g 2)) (v 0 + v 1) 1
      _ = (g 2 : ℂ) ^ (v 0 + v 1) * (g 2 : ℂ) := by rw [zpow_one]
      _ = (g 2 : ℂ) * (g 2 : ℂ) ^ (v 1 + v 0) := by
        rw [add_comm (v 1) (v 0)]
        ac_rfl
  next =>
    calc
      (g 2 : ℂ) ^ (-v 0 - v 1 - 1) * (g 2 : ℂ) =
          (g 2 : ℂ) ^ (-v 0 - v 1 - 1) * (g 2 : ℂ) ^ (1 : ℤ) := by
            rw [zpow_one]
      _ = (g 2 : ℂ) ^ ((-v 0 - v 1 - 1) + 1) :=
        (zpow_add₀ (Units.ne_zero (g 2)) (-v 0 - v 1 - 1) 1).symm
      _ = (g 2 : ℂ) ^ (-v 0 - v 1) := by
        congr 1
        ring
  next =>
    calc
      (g 2 : ℂ) ^ (v 1 + 1) =
          (g 2 : ℂ) ^ v 1 * (g 2 : ℂ) ^ (1 : ℤ) :=
        zpow_add₀ (Units.ne_zero (g 2)) (v 1) 1
      _ = (g 2 : ℂ) ^ v 1 * (g 2 : ℂ) := by rw [zpow_one]
      _ = (g 2 : ℂ) * (g 2 : ℂ) ^ (1 - (-v 0 - v 1) - v 0 - 1) := by
        have h : 1 - (-v 0 - v 1) - v 0 - 1 = v 1 := by ring
        rw [h]
        ac_rfl

public theorem a2CyclicRaw_torusChartCoordinates
    (a : ChartIndex) (g : DenseTorus) (z : RawCoordinates) :
    a2CyclicRaw a.1 (torusChartCoordinates a g * z) =
      torusChartCoordinates (a2CyclicChartIndex a) (a2CyclicDenseTorus g) *
        a2CyclicRaw a.1 z := by
  rw [← a2CyclicRaw_torusChartCoordinates_only a g]
  rcases a with ⟨upper, v⟩
  cases upper <;> funext i <;> fin_cases i <;>
    rfl

/-- Cyclic rotation intertwines the torus action with the induced dense-torus automorphism. -/
public theorem a2CyclicCarrier_carrierTorusActionFun
    (g : DenseTorus) (p : Carrier) :
    a2CyclicCarrier (carrierTorusActionFun g p) =
      carrierTorusActionFun (a2CyclicDenseTorus g) (a2CyclicCarrier p) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierTorusActionFun_inclusion, a2CyclicCarrier_inclusion,
    a2CyclicCarrier_inclusion, carrierTorusActionFun_inclusion]
  exact congrArg (inclusion (a2CyclicChartIndex a))
    (a2CyclicRaw_torusChartCoordinates a g z)

/-- The phase transformation induced by cyclic rotation of the dense torus. -/
public def a2CyclicPhase (c : Phase) : Phase :=
  ![(c 0)⁻¹ * (c 1)⁻¹, c 0]

public theorem a2CyclicDenseTorus_phaseEmbedding (c : Phase) :
    a2CyclicDenseTorus (phaseEmbedding c) = phaseEmbedding (a2CyclicPhase c) := by
  funext i
  fin_cases i <;> simp [a2CyclicDenseTorus, a2CyclicPhase, phaseEmbedding]

/-- Exact conjugacy of the combined phase and fan action before choosing analytic phase
coefficients. -/
public theorem a2CyclicCarrier_phaseAction_fanShear
    (lambda : ParameterLattice) (c : Phase) (p : Carrier) :
    a2CyclicCarrier
        (carrierTorusActionFun (phaseEmbedding c) (carrierFanShearFun lambda p)) =
      carrierTorusActionFun (phaseEmbedding (a2CyclicPhase c))
        (carrierFanShearFun (a2CyclicParameter lambda) (a2CyclicCarrier p)) := by
  rw [a2CyclicCarrier_carrierTorusActionFun,
    a2CyclicDenseTorus_phaseEmbedding, a2CyclicCarrier_carrierFanShearFun]

public def constructedCentralPhaseFaceOneLocal
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨constructedCentralPhaseFaceOneCarrier x, by
    change carrierHeight (constructedCentralPhaseFaceOneCarrier x) ∈
      Metric.ball 0 W.localWitness.radius
    rw [constructedCentralPhaseFaceOneCarrier_height, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩

public theorem constructedCentralPhaseFaceOneLocal_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceOneLocal W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    constructedCentralPhaseFaceOneCarrier)
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceOneCarrier_continuousOn_closedBall

public def constructedCentralPhaseFaceOnePoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨constructedCentralPhaseFaceOneLocal W x, constructedCentralPhaseFaceOneCarrier_height x⟩

public theorem constructedCentralPhaseFaceOnePoint_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceOnePoint W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    (constructedCentralPhaseFaceOneLocal W))
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceOneLocal_continuousOn_closedBall W

public def constructedCentralPhaseFaceOneOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedCentralPhaseFaceOnePoint W x)

public theorem constructedCentralPhaseFaceOneOrbit_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceOneOrbit W) (Metric.closedBall 0 1) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.continuousOn.comp
    (constructedCentralPhaseFaceOnePoint_continuousOn_closedBall W)
      (fun _ _ ↦ Set.mem_univ _)

public def constructedCentralPhaseFaceTwoLocal
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨constructedCentralPhaseFaceTwoCarrier x, by
    change carrierHeight (constructedCentralPhaseFaceTwoCarrier x) ∈
      Metric.ball 0 W.localWitness.radius
    rw [constructedCentralPhaseFaceTwoCarrier_height, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩

public theorem constructedCentralPhaseFaceTwoLocal_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceTwoLocal W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    constructedCentralPhaseFaceTwoCarrier)
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceTwoCarrier_continuousOn_closedBall

public def constructedCentralPhaseFaceTwoPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨constructedCentralPhaseFaceTwoLocal W x, constructedCentralPhaseFaceTwoCarrier_height x⟩

public theorem constructedCentralPhaseFaceTwoPoint_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceTwoPoint W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    (constructedCentralPhaseFaceTwoLocal W))
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceTwoLocal_continuousOn_closedBall W

public def constructedCentralPhaseFaceTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedCentralPhaseFaceTwoPoint W x)

public theorem constructedCentralPhaseFaceTwoOrbit_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceTwoOrbit W) (Metric.closedBall 0 1) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.continuousOn.comp
    (constructedCentralPhaseFaceTwoPoint_continuousOn_closedBall W)
      (fun _ _ ↦ Set.mem_univ _)

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
