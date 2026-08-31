module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberZeroCells
public import SphereSixComplex.Geometry.CuspPhaseEstimates
public import SphereSixComplex.Geometry.PaperStarPieceHausdorff

/-!
# A one-cell of the standard `A₂` central-fibre quotient

The first compact toric edge is assembled from the positive coordinate axes in a lower chart
and the adjacent upper chart.  Their nonzero parts are identified by reciprocal coordinates.
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
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem transitionMatrix_lower_to_upper_same (v : ToricLattice) :
    transitionMatrix (false, v) (true, v) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

/-- The coordinate axis in a lower chart opposite its first toric divisor. -/
public def lowerAxisZero (z : ℂ) : RawCoordinates :=
  ![z, 0, 0]

/-- The reciprocal coordinate axis in the adjacent upper chart. -/
public def upperAxisTwo (z : ℂ) : RawCoordinates :=
  ![0, 0, z]

public def singleAxis (k : Fin 3) (z : ℂ) : RawCoordinates :=
  fun i ↦ if i = k then z else 0

private theorem singleAxis_component_iff
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

private theorem carrierOrigin_componentSupport (a : ChartIndex) :
    componentSupport constructedModel (inclusion a 0) =
      Set.range (a2Triangle a.1 a.2) := by
  let _ := chartedSpace
  have hchart : inclusion a 0 ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self _
  ext v
  change inclusion a 0 ∈ carrierCentralComponent v ↔ v ∈ Set.range (a2Triangle a.1 a.2)
  constructor
  · intro hp
    by_contra hn
    exact Set.disjoint_left.mp (otherCarrierCentralComponent_disjoint_chart a v hn) hp hchart
  · rintro ⟨i, rfl⟩
    apply (carrierCentralComponent_in_chart a i _ hchart).mpr
    rw [toricChart_inclusion]
    simp [rawToComplexModel]

private theorem a2Triangle_injective_for_origin (upper : Bool) (v : ToricLattice) :
    Function.Injective (a2Triangle upper v) := by
  intro i j h
  have hcone (k : Fin 3) :
      a2ConeMatrix upper v k i = a2ConeMatrix upper v k j := by
    exact congrFun (congrArg heightOneRay h) k
  have hmatrix := dualMatrix_mul_coneMatrix (upper, v)
  have hentry (k : Fin 3) :
      (1 : Matrix (Fin 3) (Fin 3) ℤ) k i = (1 : Matrix (Fin 3) (Fin 3) ℤ) k j := by
    rw [← hmatrix, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcone l]
  by_contra hij
  have hii := hentry i
  simp [hij] at hii

private theorem carrierOrigin_componentSupport_ncard (a : ChartIndex) :
    (componentSupport constructedModel (inclusion a 0)).ncard = 3 := by
  rw [carrierOrigin_componentSupport, Set.ncard_range_of_injective
    (a2Triangle_injective_for_origin a.1 a.2)]
  simp

private theorem componentSupport_phase_fanShear
    (lambda : ParameterLattice) (c : Phase) (p : constructedModel.Carrier) :
    componentSupport constructedModel
      (CuspToricPhaseAction.ToricModel.phaseAction constructedModel c
        (Additive.toMul (constructedModel.fanShear lambda) p)) =
      (fun v ↦ v + shearVector lambda) '' componentSupport constructedModel p := by
  ext w
  change constructedModel.torusAction (phaseEmbedding c)
      (Additive.toMul (constructedModel.fanShear lambda) p) ∈
        constructedModel.centralComponent w ↔ _
  rw [constructedModel.torusAction_centralComponent]
  constructor
  · intro hw
    let v := w - shearVector lambda
    have hvw : v + shearVector lambda = w := sub_add_cancel _ _
    refine ⟨v, ?_, hvw⟩
    rw [← hvw, ← constructedModel.fanShear_component lambda v] at hw
    obtain ⟨q, hq, heq⟩ := hw
    have hqp : q = p := (Additive.toMul (constructedModel.fanShear lambda)).injective heq
    rwa [hqp] at hq
  · rintro ⟨v, hv, rfl⟩
    rw [← constructedModel.fanShear_component lambda v]
    exact ⟨p, hv, rfl⟩

private theorem lowerAxisZero_component_iff (z : ℂ) (hz : z ≠ 0) (v : ToricLattice) :
    inclusion (false, 0) (lowerAxisZero z) ∈ carrierCentralComponent v ↔
      v = e₁ ∨ v = e₂ := by
  let _ := chartedSpace
  have hchart : inclusion (false, 0) (lowerAxisZero z) ∈
      (toricChart (false, 0)).source := by
    rw [toricChart_source]
    exact Set.mem_range_self _
  constructor
  · intro hp
    have hv : v ∈ Set.range (a2Triangle false 0) := by
      by_contra hn
      exact Set.disjoint_left.mp
        (otherCarrierCentralComponent_disjoint_chart (false, 0) v hn) hp hchart
    obtain ⟨i, rfl⟩ := hv
    have hzero := (carrierCentralComponent_in_chart (false, 0) i _ hchart).mp hp
    rw [toricChart_inclusion] at hzero
    fin_cases i <;>
      simp [rawToComplexModel, lowerAxisZero, a2Triangle, e₁, e₂, hz] at hzero ⊢
  · intro hv
    rcases hv with rfl | rfl
    · rw [show e₁ = a2Triangle false 0 1 by simp [a2Triangle, e₁, e₂]]
      apply (carrierCentralComponent_in_chart (false, 0) 1 _ hchart).mpr
      rw [toricChart_inclusion]
      simp [rawToComplexModel, lowerAxisZero]
    · rw [show e₂ = a2Triangle false 0 2 by simp [a2Triangle, e₁, e₂]]
      apply (carrierCentralComponent_in_chart (false, 0) 2 _ hchart).mpr
      rw [toricChart_inclusion]
      simp [rawToComplexModel, lowerAxisZero]

private theorem upperAxisTwo_component_iff (z : ℂ) (hz : z ≠ 0) (v : ToricLattice) :
    inclusion (true, 0) (upperAxisTwo z) ∈ carrierCentralComponent v ↔
      v = e₁ ∨ v = e₂ := by
  let _ := chartedSpace
  have hchart : inclusion (true, 0) (upperAxisTwo z) ∈
      (toricChart (true, 0)).source := by
    rw [toricChart_source]
    exact Set.mem_range_self _
  constructor
  · intro hp
    have hv : v ∈ Set.range (a2Triangle true 0) := by
      by_contra hn
      exact Set.disjoint_left.mp
        (otherCarrierCentralComponent_disjoint_chart (true, 0) v hn) hp hchart
    obtain ⟨i, rfl⟩ := hv
    have hzero := (carrierCentralComponent_in_chart (true, 0) i _ hchart).mp hp
    rw [toricChart_inclusion] at hzero
    fin_cases i <;>
      simp [rawToComplexModel, upperAxisTwo, a2Triangle, e₁, e₂, hz] at hzero ⊢
  · intro hv
    rcases hv with rfl | rfl
    · rw [show e₁ = a2Triangle true 0 0 by simp [a2Triangle, e₁, e₂]]
      apply (carrierCentralComponent_in_chart (true, 0) 0 _ hchart).mpr
      rw [toricChart_inclusion]
      simp [rawToComplexModel, upperAxisTwo]
    · rw [show e₂ = a2Triangle true 0 1 by simp [a2Triangle, e₁, e₂]]
      apply (carrierCentralComponent_in_chart (true, 0) 1 _ hchart).mpr
      rw [toricChart_inclusion]
      simp [rawToComplexModel, upperAxisTwo]

/-- On the overlap of the two charts, the two axis coordinates are reciprocal. -/
public theorem inclusion_lowerAxisZero_eq_upperAxisTwo
    (v : ToricLattice) (z : ℂ) (hz : z ≠ 0) :
    inclusion (false, v) (lowerAxisZero z) =
      inclusion (true, v) (upperAxisTwo z⁻¹) := by
  rw [inclusion_eq_iff]
  constructor
  · rw [chartChange_source, transitionMatrix_lower_to_upper_same]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [lowerAxisZero]
  · change monomial (transitionMatrix (false, v) (true, v)) (lowerAxisZero z) =
      upperAxisTwo z⁻¹
    rw [transitionMatrix_lower_to_upper_same]
    funext i
    fin_cases i <;>
      simp [monomial, lowerAxisZero, upperAxisTwo, Fin.prod_univ_succ]

public theorem inclusion_lowerAxisZero_eq_upperAxisTwo_iff
    (v : ToricLattice) (z w : ℂ) :
    inclusion (false, v) (lowerAxisZero z) = inclusion (true, v) (upperAxisTwo w) ↔
      z ≠ 0 ∧ w = z⁻¹ := by
  rw [inclusion_eq_iff]
  constructor
  · rintro ⟨hs, hc⟩
    rw [chartChange_source, transitionMatrix_lower_to_upper_same] at hs
    have hz : z ≠ 0 := hs 2 0 (by decide)
    refine ⟨hz, ?_⟩
    change monomial (transitionMatrix (false, v) (true, v)) (lowerAxisZero z) =
      upperAxisTwo w at hc
    rw [transitionMatrix_lower_to_upper_same] at hc
    have h := congrFun hc 2
    simpa [monomial, lowerAxisZero, upperAxisTwo, Fin.prod_univ_succ] using h.symm
  · rintro ⟨hz, rfl⟩
    constructor
    · rw [chartChange_source, transitionMatrix_lower_to_upper_same]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [lowerAxisZero]
    · change monomial (transitionMatrix (false, v) (true, v)) (lowerAxisZero z) =
        upperAxisTwo z⁻¹
      rw [transitionMatrix_lower_to_upper_same]
      funext i
      fin_cases i <;>
        simp [monomial, lowerAxisZero, upperAxisTwo, Fin.prod_univ_succ]

public def constructedCentralEdgeZeroLowerBranch (x : Fin 1 → ℝ) : Carrier :=
  inclusion (false, 0) (lowerAxisZero ((1 + x 0 : ℝ) : ℂ))

public def constructedCentralEdgeZeroUpperBranch (x : Fin 1 → ℝ) : Carrier :=
  inclusion (true, 0) (upperAxisTwo ((1 - x 0 : ℝ) : ℂ))

/-- A compactified coordinate axis, from the lower origin to the adjacent upper origin. -/
public def constructedCentralEdgeZeroCarrier (x : Fin 1 → ℝ) : Carrier :=
  if x 0 ≤ 0 then constructedCentralEdgeZeroLowerBranch x
  else constructedCentralEdgeZeroUpperBranch x

public theorem constructedCentralEdgeZeroCarrier_height (x : Fin 1 → ℝ) :
    carrierHeight (constructedCentralEdgeZeroCarrier x) = 0 := by
  by_cases hx : x 0 ≤ 0
  · simp [constructedCentralEdgeZeroCarrier, hx, constructedCentralEdgeZeroLowerBranch,
      carrierHeight_inclusion, rawHeight, lowerAxisZero]
  · simp [constructedCentralEdgeZeroCarrier, hx, constructedCentralEdgeZeroUpperBranch,
      carrierHeight_inclusion, rawHeight, upperAxisTwo]

public theorem constructedCentralEdgeZeroLowerBranch_continuous :
    Continuous constructedCentralEdgeZeroLowerBranch := by
  apply (inclusion_isOpenEmbedding _).continuous.comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [lowerAxisZero] <;> fun_prop

public theorem constructedCentralEdgeZeroUpperBranch_continuous :
    Continuous constructedCentralEdgeZeroUpperBranch := by
  apply (inclusion_isOpenEmbedding _).continuous.comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [upperAxisTwo] <;> fun_prop

/-- The two affine-axis halves glue continuously at reciprocal coordinate one. -/
public theorem constructedCentralEdgeZeroCarrier_continuous :
    Continuous constructedCentralEdgeZeroCarrier := by
  change Continuous ({x | x 0 ≤ 0}.piecewise
    constructedCentralEdgeZeroLowerBranch constructedCentralEdgeZeroUpperBranch)
  apply Continuous.piecewise
  · intro x hx
    have hx0 : x 0 = 0 :=
      frontier_le_subset_eq (continuous_apply 0) continuous_const hx
    simp only [constructedCentralEdgeZeroLowerBranch, constructedCentralEdgeZeroUpperBranch,
      hx0, add_zero, sub_zero]
    simpa using inclusion_lowerAxisZero_eq_upperAxisTwo 0 1 one_ne_zero
  · exact constructedCentralEdgeZeroLowerBranch_continuous
  · exact constructedCentralEdgeZeroUpperBranch_continuous

private theorem finOne_mem_ball_bounds (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.ball 0 1) : -1 < x 0 ∧ x 0 < 1 := by
  have hxext : x = fun _ ↦ x 0 := by
    funext i
    fin_cases i
    rfl
  rw [Metric.mem_ball, dist_zero_right, hxext] at hx
  simpa [Pi.norm_def, Real.norm_eq_abs, abs_lt] using hx

/-- Every interior point of the edge lies on exactly the same two ray components. -/
public theorem constructedCentralEdgeZeroCarrier_componentSupport
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralEdgeZeroCarrier x) =
      ({e₁, e₂} : Set ToricLattice) := by
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  by_cases hx0 : x 0 ≤ 0
  · have hn : ((1 + x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeZeroCarrier, hx0]
    ext v
    change inclusion (false, 0) (lowerAxisZero ((1 + x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ {e₁, e₂}
    rw [lowerAxisZero_component_iff _ hn]
    simp
  · have hn : ((1 - x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 - x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeZeroCarrier, hx0]
    ext v
    change inclusion (true, 0) (upperAxisTwo ((1 - x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ {e₁, e₂}
    rw [upperAxisTwo_component_iff _ hn]
    simp

/-- Before quotienting, the compactified axis is injective on its open parameter interval. -/
public theorem constructedCentralEdgeZeroCarrier_injOn :
    Set.InjOn constructedCentralEdgeZeroCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  obtain ⟨hyl, hyu⟩ := finOne_mem_ball_bounds y hy
  by_cases hx0 : x 0 ≤ 0
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeZeroCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (false, 0)).injective hxy
      have hc0 := congrFun hc 0
      simp [lowerAxisZero] at hc0
      funext i
      fin_cases i
      exact_mod_cast hc0
    · simp only [constructedCentralEdgeZeroCarrier, hx0, hy0,
        constructedCentralEdgeZeroLowerBranch, constructedCentralEdgeZeroUpperBranch] at hxy
      have he := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy
      have hmul : ((1 + x 0 : ℝ) : ℂ) * ((1 - y 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeZeroCarrier, hx0, hy0,
        constructedCentralEdgeZeroLowerBranch, constructedCentralEdgeZeroUpperBranch] at hxy
      have he := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy.symm
      have hmul : ((1 + y 0 : ℝ) : ℂ) * ((1 - x 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
    · simp only [constructedCentralEdgeZeroCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (true, 0)).injective hxy
      have hc2 := congrFun hc 2
      simp [upperAxisTwo] at hc2
      funext i
      fin_cases i
      exact_mod_cast hc2

/-- The compactified axis lies in every sufficiently small local carrier because its height is
zero. -/
public def constructedCentralEdgeZeroLocal
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 1 → ℝ) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨constructedCentralEdgeZeroCarrier x, by
    change carrierHeight (constructedCentralEdgeZeroCarrier x) ∈
      Metric.ball 0 W.localWitness.radius
    rw [constructedCentralEdgeZeroCarrier_height, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩

public theorem constructedCentralEdgeZeroLocal_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedCentralEdgeZeroLocal W) :=
  constructedCentralEdgeZeroCarrier_continuous.subtype_mk _

/-- The compactified axis as a point of the invariant central subspace. -/
public def constructedCentralEdgeZeroPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 1 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨constructedCentralEdgeZeroLocal W x, by
    change carrierHeight (constructedCentralEdgeZeroCarrier x) = 0
    exact constructedCentralEdgeZeroCarrier_height x⟩

public theorem constructedCentralEdgeZeroPoint_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedCentralEdgeZeroPoint W) :=
  (constructedCentralEdgeZeroLocal_continuous W).subtype_mk _

/-- The first compactified toric edge in the central-fibre orbit quotient. -/
public def constructedCentralEdgeZeroOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 1 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedCentralEdgeZeroPoint W x)

public theorem constructedCentralEdgeZeroOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedCentralEdgeZeroOrbit W) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.comp (constructedCentralEdgeZeroPoint_continuous W)

private theorem centralOrbitRel_coe_eq_of_same_componentSupport
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
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
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

private theorem centralOrbitRel_componentSupport_ncard_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    (componentSupport constructedModel
      ((p : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier)).ncard =
    (componentSupport constructedModel
      ((q : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier)).ncard := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (q : LocalCarrier constructedModel W.localWitness.radius) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hcarrier
  have hsupport := componentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : LocalCarrier constructedModel W.localWitness.radius)))
    ((q : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier)
  rw [hcarrier] at hsupport
  rw [hsupport]
  symm
  apply Set.ncard_congr (fun v _ ↦ v + shearVector lambda)
  · intro v hv
    exact ⟨v, hv, rfl⟩
  · intro a b ha hb hab
    exact add_right_cancel hab
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, rfl⟩

private theorem centralOrbitRel_componentSupport_eq_translate
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    ∃ lambda : ParameterLattice,
      componentSupport constructedModel
          ((p : LocalCarrier constructedModel W.localWitness.radius) :
            constructedModel.Carrier) =
        (fun v ↦ v + shearVector lambda) ''
          componentSupport constructedModel
            ((q : LocalCarrier constructedModel W.localWitness.radius) :
              constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (q : LocalCarrier constructedModel W.localWitness.radius) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hcarrier
  refine ⟨lambda, ?_⟩
  have hsupport := componentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : LocalCarrier constructedModel W.localWitness.radius)))
    ((q : LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier)
  rwa [hcarrier] at hsupport

/-- No nontrivial lattice translate identifies two interior points of the chosen edge. -/
public theorem constructedCentralEdgeZeroOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeZeroOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralEdgeZeroPoint W x) (constructedCentralEdgeZeroPoint W y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralEdgeZeroPoint W x) (constructedCentralEdgeZeroPoint W y) hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun p : S ↦ ((p : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  change ((g • constructedCentralEdgeZeroLocal W y :
    LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      constructedCentralEdgeZeroCarrier x at hcarrier
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  have hphase := hcarrier
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (constructedCentralEdgeZeroLocal W y) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        constructedCentralEdgeZeroCarrier x at hphase
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hphase
  have hsupportX := constructedCentralEdgeZeroCarrier_componentSupport x hx
  have hsupportY := constructedCentralEdgeZeroCarrier_componentSupport y hy
  have hforward : ∀ v ∈ ({e₁, e₂} : Set ToricLattice),
      v + shearVector lambda ∈ ({e₁, e₂} : Set ToricLattice) := by
    intro v hv
    have hvY : v ∈ componentSupport constructedModel
        (constructedCentralEdgeZeroCarrier y) := by
      rw [hsupportY]
      exact hv
    have hfan : Additive.toMul (constructedModel.fanShear lambda)
        (constructedCentralEdgeZeroCarrier y) ∈
          constructedModel.centralComponent (v + shearVector lambda) := by
      rw [← constructedModel.fanShear_component lambda v]
      exact ⟨constructedCentralEdgeZeroCarrier y, hvY, rfl⟩
    have hphaseComponent :
        CuspToricPhaseAction.ToricModel.phaseAction constructedModel
          (C.phase lambda (constructedModel.t (constructedCentralEdgeZeroLocal W y)))
          (Additive.toMul (constructedModel.fanShear lambda)
            (constructedCentralEdgeZeroLocal W y)) ∈
              constructedModel.centralComponent (v + shearVector lambda) :=
      (constructedModel.torusAction_centralComponent _ _ _).mpr hfan
    rw [hphase] at hphaseComponent
    rw [← hsupportX]
    exact hphaseComponent
  have hshear : shearVector lambda = 0 :=
    translation_eq_zero_of_finite_forward_invariant
      ((Set.finite_singleton e₂).insert e₁) ⟨e₁, by simp⟩ hforward
  have hlambda : lambda = 0 := by
    apply shearVector_injective
    rw [hshear]
    ext i
    simp [shearVector, Matrix.mulVec]
  have hplain := hcarrier
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda
    (constructedCentralEdgeZeroLocal W y) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        constructedCentralEdgeZeroCarrier x at hplain
  rw [← C.psiMap_eq_generic, hlambda] at hplain
  rw [C.psiMap_zero] at hplain
  exact (constructedCentralEdgeZeroCarrier_injOn hy hx hplain).symm

/-- The characteristic partial equivalence of the first one-cell. -/
public def constructedCentralOneCellZero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 1 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralEdgeZeroOrbit W) (Metric.ball 0 1)
    (constructedCentralEdgeZeroOrbit_injOn W)

public theorem constructedCentralOneCellZero_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralOneCellZero W).source = Metric.ball 0 1 :=
  rfl

public theorem constructedCentralOneCellZero_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellZero W) (Metric.closedBall 0 1) :=
  (constructedCentralEdgeZeroOrbit_continuous W).continuousOn

public theorem constructedCentralEdgeZeroOrbit_negOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeZeroOrbit W (fun _ ↦ -1) =
      constructedCentralOriginOrbit W false := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  apply @Quotient.sound S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
  change MulAction.orbitRel (Multiplicative ParameterLattice) S
    (constructedCentralEdgeZeroPoint W (fun _ ↦ -1))
      (constructedCentralOriginPoint W false)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp [constructedCentralEdgeZeroPoint, constructedCentralEdgeZeroLocal,
    constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroLowerBranch,
    lowerAxisZero, constructedCentralOriginPoint, constructedCentralOrigin]
  congr 1
  funext i
  fin_cases i <;> rfl

public theorem constructedCentralEdgeZeroOrbit_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeZeroOrbit W (fun _ ↦ 1) =
      constructedCentralOriginOrbit W true := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  apply @Quotient.sound S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
  change MulAction.orbitRel (Multiplicative ParameterLattice) S
    (constructedCentralEdgeZeroPoint W (fun _ ↦ 1))
      (constructedCentralOriginPoint W true)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp [constructedCentralEdgeZeroPoint, constructedCentralEdgeZeroLocal,
    constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroUpperBranch,
    upperAxisTwo, constructedCentralOriginPoint, constructedCentralOrigin]
  norm_num
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem finOne_mem_sphere_eq_endpoints (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    x = (fun _ ↦ 1) ∨ x = (fun _ ↦ -1) := by
  have hxext : x = fun _ ↦ x 0 := by
    funext i
    fin_cases i
    rfl
  rw [Metric.mem_sphere, dist_zero_right, hxext] at hx
  simp [Pi.norm_def, Real.norm_eq_abs, abs_eq] at hx
  rcases hx with hx | hx
  · left
    funext i
    fin_cases i
    exact hx
  · right
    funext i
    fin_cases i
    exact hx

private theorem finOne_mem_closedBall_cases (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.closedBall 0 1) :
    x ∈ Metric.ball 0 1 ∨ x = (fun _ ↦ 1) ∨ x = (fun _ ↦ -1) := by
  by_cases hball : x ∈ Metric.ball 0 1
  · exact Or.inl hball
  · right
    apply finOne_mem_sphere_eq_endpoints x
    rw [Metric.mem_sphere]
    have hle : dist x 0 ≤ 1 := Metric.mem_closedBall.mp hx
    have hnot : ¬dist x 0 < 1 := by
      simpa only [Metric.mem_ball] using hball
    exact le_antisymm hle (not_lt.mp hnot)

private def constructedCentralChartOrigin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (a : ChartIndex) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨inclusion a 0, by
    change carrierHeight (inclusion a 0) ∈ Metric.ball 0 W.localWitness.radius
    rw [carrierHeight_inclusion, Metric.mem_ball, dist_zero_right]
    simpa [rawHeight] using W.localWitness.radius_pos⟩

private theorem constructedCentralChartOrigin_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (a : ChartIndex) :
    constructedModel.t (constructedCentralChartOrigin W a) = 0 := by
  change carrierHeight (inclusion a 0) = 0
  rw [carrierHeight_inclusion]
  simp [rawHeight]

private theorem constructedCentralChartOrigin_smul_coe
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (g : Multiplicative ParameterLattice) (a : ChartIndex) :
    letI := actualLocalCuspQuotientAction W
    ((g • constructedCentralChartOrigin W a :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      inclusion (translateChartIndex (Multiplicative.toAdd g) a) 0 := by
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let _ := actualLocalCuspQuotientAction W
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap
    (Multiplicative.toAdd g) (constructedCentralChartOrigin W a) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = _
  rw [← C.psiMap_eq_generic, C.psiMap_coe]
  change carrierTorusActionFun _
    (carrierFanShearFun (Multiplicative.toAdd g) (inclusion a 0)) = _
  rw [carrierFanShearFun_inclusion, carrierTorusActionFun_inclusion]
  simp
/-- The boundary of the first one-cell lands in the two constructed zero-cells. -/
public theorem constructedCentralOneCellZero_mapsTo_zeroCells
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralOneCellZero W) (Metric.sphere 0 1)
      (⋃ j : Fin 2, constructedCentralZeroCell W j '' Metric.closedBall 0 1) := by
  intro x hx
  rcases finOne_mem_sphere_eq_endpoints x hx with rfl | rfl
  · change constructedCentralEdgeZeroOrbit W (fun _ ↦ 1) ∈ _
    rw [constructedCentralEdgeZeroOrbit_one]
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]
  · change constructedCentralEdgeZeroOrbit W (fun _ ↦ -1) ∈ _
    rw [constructedCentralEdgeZeroOrbit_negOne]
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]

public def centralEdgeLocalOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (x : Fin 1 → ℝ) : LocalCarrier constructedModel W.localWitness.radius :=
  ⟨F x, by
    change carrierHeight (F x) ∈ Metric.ball 0 W.localWitness.radius
    rw [hF, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩

public def centralEdgePointOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (x : Fin 1 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  ⟨centralEdgeLocalOf W F hF x, hF x⟩

public def centralEdgeOrbitOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (x : Fin 1 → ℝ) : ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (centralEdgePointOf W F hF x)

private theorem centralEdgeOrbitOf_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (hcontinuous : Continuous F) : Continuous (centralEdgeOrbitOf W F hF) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.comp
    ((hcontinuous.subtype_mk _).subtype_mk _)

private theorem centralEdgeOrbitOf_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (T : Set ToricLattice) (hTfinite : T.Finite) (hTnonempty : T.Nonempty)
    (hsupport : ∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      componentSupport constructedModel (F x) = T)
    (hinj : Set.InjOn F (Metric.ball 0 1)) :
    Set.InjOn (centralEdgeOrbitOf W F hF) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y) hxy
  have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport W T hTfinite hTnonempty
    (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y)
    (hsupport x hx) (hsupport y hy) hrel
  exact hinj hx hy hcoe

private theorem centralEdgePointOf_componentSupport_ncard_of_eq_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (x : Fin 1 → ℝ) (a : ChartIndex) (hx : F x = inclusion a 0) :
    (componentSupport constructedModel
      (((centralEdgePointOf W F hF x : actualLocalCuspCentralSubMulAction W) :
        LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier)).ncard = 3 := by
  change (componentSupport constructedModel (F x)).ncard = 3
  rw [hx]
  exact carrierOrigin_componentSupport_ncard a

private theorem centralEdgeOrbitOf_endpoints_ne
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (upperV : ToricLattice)
    (hneg : F (fun _ ↦ -1) = inclusion (false, 0) 0)
    (hpos : F (fun _ ↦ 1) = inclusion (true, upperV) 0) :
    centralEdgeOrbitOf W F hF (fun _ ↦ -1) ≠
      centralEdgeOrbitOf W F hF (fun _ ↦ 1) := by
  intro h
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (centralEdgePointOf W F hF (fun _ ↦ -1))
      (centralEdgePointOf W F hF (fun _ ↦ 1)) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (centralEdgePointOf W F hF (fun _ ↦ -1))
      (centralEdgePointOf W F hF (fun _ ↦ 1)) h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  have hlocalNeg : centralEdgeLocalOf W F hF (fun _ ↦ -1) =
      constructedCentralChartOrigin W (false, 0) := by
    apply Subtype.ext
    exact hneg
  have hlocalPos : centralEdgeLocalOf W F hF (fun _ ↦ 1) =
      constructedCentralChartOrigin W (true, upperV) := by
    apply Subtype.ext
    exact hpos
  change ((g • centralEdgeLocalOf W F hF (fun _ ↦ 1) :
    LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      (centralEdgeLocalOf W F hF (fun _ ↦ -1) :
        LocalCarrier constructedModel W.localWitness.radius) at hcarrier
  rw [hlocalPos, hlocalNeg, constructedCentralChartOrigin_smul_coe] at hcarrier
  change inclusion (true, upperV + shearVector (Multiplicative.toAdd g)) 0 =
    inclusion (false, 0) 0 at hcarrier
  exact lowerOrigin_ne_upperOrigin 0 _ hcarrier.symm

private theorem centralEdgeOrbitOf_componentSupport_ncard_eq_of_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    {x y : Fin 1 → ℝ}
    (hxy : centralEdgeOrbitOf W F hF x = centralEdgeOrbitOf W F hF y) :
    (componentSupport constructedModel (F x)).ncard =
      (componentSupport constructedModel (F y)).ncard := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y) hxy
  simpa only [centralEdgePointOf, centralEdgeLocalOf] using
    centralOrbitRel_componentSupport_ncard_eq W
      (centralEdgePointOf W F hF x) (centralEdgePointOf W F hF y) hrel

private theorem centralEdgeOrbitOf_injOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (T : Set ToricLattice) (hTcard : T.ncard = 2)
    (hsupport : ∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      componentSupport constructedModel (F x) = T)
    (hinjOpen : Set.InjOn (centralEdgeOrbitOf W F hF) (Metric.ball 0 1))
    (upperV : ToricLattice)
    (hneg : F (fun _ ↦ -1) = inclusion (false, 0) 0)
    (hpos : F (fun _ ↦ 1) = inclusion (true, upperV) 0) :
    Set.InjOn (centralEdgeOrbitOf W F hF) (Metric.closedBall 0 1) := by
  intro x hx y hy hxy
  rcases finOne_mem_closedBall_cases x hx with hxOpen | hxPos | hxNeg
  · rcases finOne_mem_closedBall_cases y hy with hyOpen | hyPos | hyNeg
    · exact hinjOpen hxOpen hyOpen hxy
    · subst y
      have hn := centralEdgeOrbitOf_componentSupport_ncard_eq_of_eq W F hF hxy
      rw [hsupport x hxOpen, hTcard] at hn
      have hthree := centralEdgePointOf_componentSupport_ncard_of_eq_origin W F hF
        (fun _ ↦ 1) (true, upperV) hpos
      change (componentSupport constructedModel (F (fun _ ↦ 1))).ncard = 3 at hthree
      omega
    · subst y
      have hn := centralEdgeOrbitOf_componentSupport_ncard_eq_of_eq W F hF hxy
      rw [hsupport x hxOpen, hTcard] at hn
      have hthree := centralEdgePointOf_componentSupport_ncard_of_eq_origin W F hF
        (fun _ ↦ -1) (false, 0) hneg
      change (componentSupport constructedModel (F (fun _ ↦ -1))).ncard = 3 at hthree
      omega
  · subst x
    rcases finOne_mem_closedBall_cases y hy with hyOpen | hyPos | hyNeg
    · have hn := centralEdgeOrbitOf_componentSupport_ncard_eq_of_eq W F hF hxy
      rw [hsupport y hyOpen, hTcard] at hn
      have hthree := centralEdgePointOf_componentSupport_ncard_of_eq_origin W F hF
        (fun _ ↦ 1) (true, upperV) hpos
      change (componentSupport constructedModel (F (fun _ ↦ 1))).ncard = 3 at hthree
      omega
    · exact hyPos.symm
    · subst y
      exfalso
      exact centralEdgeOrbitOf_endpoints_ne W F hF upperV hneg hpos hxy.symm
  · subst x
    rcases finOne_mem_closedBall_cases y hy with hyOpen | hyPos | hyNeg
    · have hn := centralEdgeOrbitOf_componentSupport_ncard_eq_of_eq W F hF hxy
      rw [hsupport y hyOpen, hTcard] at hn
      have hthree := centralEdgePointOf_componentSupport_ncard_of_eq_origin W F hF
        (fun _ ↦ -1) (false, 0) hneg
      change (componentSupport constructedModel (F (fun _ ↦ -1))).ncard = 3 at hthree
      omega
    · subst y
      exfalso
      exact centralEdgeOrbitOf_endpoints_ne W F hF upperV hneg hpos hxy
    · exact hyNeg.symm

private def centralEdgeClosedBallMapOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0) :
    {x : Fin 1 → ℝ // x ∈ Metric.closedBall 0 1} →
      ActualLocalCuspCentralOrbitQuotient W :=
  fun x ↦ centralEdgeOrbitOf W F hF x

private theorem centralEdgeClosedBallMapOf_isClosedEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (hcontinuous : Continuous (centralEdgeOrbitOf W F hF))
    (hinj : Set.InjOn (centralEdgeOrbitOf W F hF) (Metric.closedBall 0 1)) :
    Topology.IsClosedEmbedding (centralEdgeClosedBallMapOf W F hF) := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  apply (hcontinuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  exact hinj x.property y.property hxy

private theorem centralOrbitPartialEquiv_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (f : (Fin 1 → ℝ) → ActualLocalCuspCentralOrbitQuotient W)
    (hcontinuous : Continuous f)
    (hinjOpen : Set.InjOn f (Metric.ball 0 1))
    (hinjClosed : Set.InjOn f (Metric.closedBall 0 1)) :
    let e := Set.InjOn.toPartialEquiv f (Metric.ball 0 1) hinjOpen
    ContinuousOn e.symm e.target := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let e := Set.InjOn.toPartialEquiv f (Metric.ball 0 1) hinjOpen
  let closedMap : {x : Fin 1 → ℝ // x ∈ Metric.closedBall 0 1} →
      ActualLocalCuspCentralOrbitQuotient W := fun x ↦ f x
  have hclosedMap : Topology.IsClosedEmbedding closedMap := by
    apply (hcontinuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    apply Subtype.ext
    exact hinjClosed x.property y.property hxy
  let lift : e.target → {x : Fin 1 → ℝ // x ∈ Metric.closedBall 0 1} :=
    fun q ↦ ⟨e.symm q, Metric.ball_subset_closedBall (e.map_target q.property)⟩
  have hlift : Continuous lift := by
    apply hclosedMap.isEmbedding.continuous_iff.mpr
    have heq : closedMap ∘ lift =
        (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.property
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 1 → ℝ))
  exact continuous_subtype_val.comp hlift

private theorem transitionMatrix_lower_to_upper_left (v : ToricLattice) :
    transitionMatrix (false, v) (true, v - e₁) =
      !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_lower_to_upper_down (v : ToricLattice) :
    transitionMatrix (false, v) (true, v - e₂) =
      !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem inclusion_middleAxis_left_iff (z w : ℂ) :
    inclusion (false, 0) (singleAxis 1 z) = inclusion (true, -e₁) (singleAxis 1 w) ↔
      z ≠ 0 ∧ w = z⁻¹ := by
  have htm : transitionMatrix (false, 0) (true, -e₁) =
      !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] := by
    simpa using transitionMatrix_lower_to_upper_left 0
  rw [inclusion_eq_iff]
  constructor
  · rintro ⟨hs, hc⟩
    rw [chartChange_source, htm] at hs
    have hz : z ≠ 0 := hs 1 1 (by decide)
    refine ⟨hz, ?_⟩
    change monomial (transitionMatrix (false, 0) (true, -e₁)) (singleAxis 1 z) =
      singleAxis 1 w at hc
    rw [htm] at hc
    have h := congrFun hc 1
    simpa [monomial, singleAxis, Fin.prod_univ_succ] using h.symm
  · rintro ⟨hz, rfl⟩
    constructor
    · rw [chartChange_source, htm]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [singleAxis]
    · change monomial (transitionMatrix (false, 0) (true, -e₁)) (singleAxis 1 z) =
        singleAxis 1 z⁻¹
      rw [htm]
      funext i
      fin_cases i <;> simp [monomial, singleAxis, Fin.prod_univ_succ]

public def constructedCentralEdgeOneCarrier (x : Fin 1 → ℝ) : Carrier :=
  if x 0 ≤ 0 then inclusion (false, 0) (singleAxis 1 ((1 + x 0 : ℝ) : ℂ))
  else inclusion (true, -e₁) (singleAxis 1 ((1 - x 0 : ℝ) : ℂ))

public theorem constructedCentralEdgeOneCarrier_height (x : Fin 1 → ℝ) :
    carrierHeight (constructedCentralEdgeOneCarrier x) = 0 := by
  by_cases hx : x 0 ≤ 0 <;>
    simp [constructedCentralEdgeOneCarrier, hx, carrierHeight_inclusion, rawHeight,
      singleAxis]

public theorem constructedCentralEdgeOneCarrier_continuous :
    Continuous constructedCentralEdgeOneCarrier := by
  change Continuous ({x : Fin 1 → ℝ | x 0 ≤ 0}.piecewise
    (fun x : Fin 1 → ℝ ↦ inclusion (false, 0) (singleAxis 1 ((1 + x 0 : ℝ) : ℂ)))
    (fun x : Fin 1 → ℝ ↦ inclusion (true, -e₁) (singleAxis 1 ((1 - x 0 : ℝ) : ℂ))))
  apply Continuous.piecewise
  · intro x hx
    have hx0 : x 0 = 0 :=
      frontier_le_subset_eq (continuous_apply 0) continuous_const hx
    simp only [hx0, add_zero, sub_zero]
    exact (inclusion_middleAxis_left_iff 1 1).mpr ⟨one_ne_zero, inv_one.symm⟩
  · apply (inclusion_isOpenEmbedding _).continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [singleAxis] <;> fun_prop
  · apply (inclusion_isOpenEmbedding _).continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [singleAxis] <;> fun_prop

public theorem constructedCentralEdgeOneCarrier_componentSupport
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralEdgeOneCarrier x) =
      ({0, e₂} : Set ToricLattice) := by
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  by_cases hx0 : x 0 ≤ 0
  · have hn : ((1 + x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeOneCarrier, hx0]
    ext v
    change inclusion (false, 0) (singleAxis 1 ((1 + x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₂} : Set ToricLattice)
    rw [singleAxis_component_iff _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by simp [a2Triangle, e₁, e₂]⟩
  · have hn : ((1 - x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 - x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeOneCarrier, hx0]
    ext v
    change inclusion (true, -e₁) (singleAxis 1 ((1 - x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₂} : Set ToricLattice)
    rw [singleAxis_component_iff _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by simp [a2Triangle, e₁, e₂]⟩

public theorem constructedCentralEdgeOneCarrier_injOn :
    Set.InjOn constructedCentralEdgeOneCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  obtain ⟨hyl, hyu⟩ := finOne_mem_ball_bounds y hy
  by_cases hx0 : x 0 ≤ 0
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeOneCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (false, 0)).injective hxy
      have hc1 := congrFun hc 1
      simp [singleAxis] at hc1
      funext i
      fin_cases i
      exact_mod_cast hc1
    · simp only [constructedCentralEdgeOneCarrier, hx0, hy0] at hxy
      have he := inclusion_middleAxis_left_iff _ _ |>.mp hxy
      have hmul : ((1 + x 0 : ℝ) : ℂ) * ((1 - y 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeOneCarrier, hx0, hy0] at hxy
      have he := inclusion_middleAxis_left_iff _ _ |>.mp hxy.symm
      have hmul : ((1 + y 0 : ℝ) : ℂ) * ((1 - x 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
    · simp only [constructedCentralEdgeOneCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (true, -e₁)).injective hxy
      have hc1 := congrFun hc 1
      simp [singleAxis] at hc1
      funext i
      fin_cases i
      exact_mod_cast hc1

public noncomputable abbrev constructedCentralEdgeOneOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 1 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  centralEdgeOrbitOf W constructedCentralEdgeOneCarrier constructedCentralEdgeOneCarrier_height x

public theorem constructedCentralEdgeOneOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedCentralEdgeOneOrbit W) :=
  centralEdgeOrbitOf_continuous W _ _ constructedCentralEdgeOneCarrier_continuous

public theorem constructedCentralEdgeOneOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeOneOrbit W) (Metric.ball 0 1) :=
  centralEdgeOrbitOf_injOn W _ _ ({0, e₂} : Set ToricLattice)
    ((Set.finite_singleton e₂).insert 0) ⟨0, by simp⟩
    constructedCentralEdgeOneCarrier_componentSupport constructedCentralEdgeOneCarrier_injOn

public def constructedCentralOneCellOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 1 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralEdgeOneOrbit W) (Metric.ball 0 1)
    (constructedCentralEdgeOneOrbit_injOn W)

public theorem constructedCentralOneCellOne_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralOneCellOne W).source = Metric.ball 0 1 := rfl

public theorem constructedCentralOneCellOne_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellOne W) (Metric.closedBall 0 1) :=
  (constructedCentralEdgeOneOrbit_continuous W).continuousOn

private theorem inclusion_lowerTwo_upperZero_down_iff (z w : ℂ) :
    inclusion (false, 0) (singleAxis 2 z) = inclusion (true, -e₂) (singleAxis 0 w) ↔
      z ≠ 0 ∧ w = z⁻¹ := by
  have htm : transitionMatrix (false, 0) (true, -e₂) =
      !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] := by
    simpa using transitionMatrix_lower_to_upper_down 0
  rw [inclusion_eq_iff]
  constructor
  · rintro ⟨hs, hc⟩
    rw [chartChange_source, htm] at hs
    have hz : z ≠ 0 := hs 0 2 (by decide)
    refine ⟨hz, ?_⟩
    change monomial (transitionMatrix (false, 0) (true, -e₂)) (singleAxis 2 z) =
      singleAxis 0 w at hc
    rw [htm] at hc
    have h := congrFun hc 0
    simpa [monomial, singleAxis, Fin.prod_univ_succ] using h.symm
  · rintro ⟨hz, rfl⟩
    constructor
    · rw [chartChange_source, htm]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [singleAxis]
    · change monomial (transitionMatrix (false, 0) (true, -e₂)) (singleAxis 2 z) =
        singleAxis 0 z⁻¹
      rw [htm]
      funext i
      fin_cases i <;> simp [monomial, singleAxis, Fin.prod_univ_succ]

public def constructedCentralEdgeTwoCarrier (x : Fin 1 → ℝ) : Carrier :=
  if x 0 ≤ 0 then inclusion (false, 0) (singleAxis 2 ((1 + x 0 : ℝ) : ℂ))
  else inclusion (true, -e₂) (singleAxis 0 ((1 - x 0 : ℝ) : ℂ))

public theorem constructedCentralEdgeTwoCarrier_height (x : Fin 1 → ℝ) :
    carrierHeight (constructedCentralEdgeTwoCarrier x) = 0 := by
  by_cases hx : x 0 ≤ 0 <;>
    simp [constructedCentralEdgeTwoCarrier, hx, carrierHeight_inclusion, rawHeight, singleAxis]

public theorem constructedCentralEdgeTwoCarrier_continuous :
    Continuous constructedCentralEdgeTwoCarrier := by
  change Continuous ({x : Fin 1 → ℝ | x 0 ≤ 0}.piecewise
    (fun x : Fin 1 → ℝ ↦ inclusion (false, 0) (singleAxis 2 ((1 + x 0 : ℝ) : ℂ)))
    (fun x : Fin 1 → ℝ ↦ inclusion (true, -e₂) (singleAxis 0 ((1 - x 0 : ℝ) : ℂ))))
  apply Continuous.piecewise
  · intro x hx
    have hx0 : x 0 = 0 :=
      frontier_le_subset_eq (continuous_apply 0) continuous_const hx
    simp only [hx0, add_zero, sub_zero]
    exact (inclusion_lowerTwo_upperZero_down_iff 1 1).mpr ⟨one_ne_zero, inv_one.symm⟩
  · apply (inclusion_isOpenEmbedding _).continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [singleAxis] <;> fun_prop
  · apply (inclusion_isOpenEmbedding _).continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [singleAxis] <;> fun_prop

public theorem constructedCentralEdgeTwoCarrier_componentSupport
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralEdgeTwoCarrier x) =
      ({0, e₁} : Set ToricLattice) := by
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  by_cases hx0 : x 0 ≤ 0
  · have hn : ((1 + x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeTwoCarrier, hx0]
    ext v
    change inclusion (false, 0) (singleAxis 2 ((1 + x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₁} : Set ToricLattice)
    rw [singleAxis_component_iff _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨0, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨1, by decide, by simp [a2Triangle, e₁, e₂]⟩
  · have hn : ((1 - x 0 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 - x 0 : ℝ) ≠ 0 by nlinarith)
    simp only [constructedCentralEdgeTwoCarrier, hx0]
    ext v
    change inclusion (true, -e₂) (singleAxis 0 ((1 - x 0 : ℝ) : ℂ)) ∈
      carrierCentralComponent v ↔ v ∈ ({0, e₁} : Set ToricLattice)
    rw [singleAxis_component_iff _ _ _ hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp [a2Triangle, e₁, e₂] at hi ⊢
    · intro hv
      rcases hv with (rfl | rfl)
      · exact ⟨1, by decide, by
          ext i
          fin_cases i <;> simp [a2Triangle, e₁, e₂]⟩
      · exact ⟨2, by decide, by simp [a2Triangle, e₁, e₂]⟩

public theorem constructedCentralEdgeTwoCarrier_injOn :
    Set.InjOn constructedCentralEdgeTwoCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hxl, hxu⟩ := finOne_mem_ball_bounds x hx
  obtain ⟨hyl, hyu⟩ := finOne_mem_ball_bounds y hy
  by_cases hx0 : x 0 ≤ 0
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeTwoCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (false, 0)).injective hxy
      have hc2 := congrFun hc 2
      simp [singleAxis] at hc2
      funext i
      fin_cases i
      exact_mod_cast hc2
    · simp only [constructedCentralEdgeTwoCarrier, hx0, hy0] at hxy
      have he := inclusion_lowerTwo_upperZero_down_iff _ _ |>.mp hxy
      have hmul : ((1 + x 0 : ℝ) : ℂ) * ((1 - y 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralEdgeTwoCarrier, hx0, hy0] at hxy
      have he := inclusion_lowerTwo_upperZero_down_iff _ _ |>.mp hxy.symm
      have hmul : ((1 + y 0 : ℝ) : ℂ) * ((1 - x 0 : ℝ) : ℂ) = 1 := by
        rw [he.2]
        exact mul_inv_cancel₀ he.1
      have hreal := congrArg Complex.re hmul
      norm_num at hreal
      exfalso
      nlinarith
    · simp only [constructedCentralEdgeTwoCarrier, hx0, hy0] at hxy
      have hc := (inclusion_isOpenEmbedding (true, -e₂)).injective hxy
      have hc0 := congrFun hc 0
      simp [singleAxis] at hc0
      funext i
      fin_cases i
      exact_mod_cast hc0

public noncomputable abbrev constructedCentralEdgeTwoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 1 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  centralEdgeOrbitOf W constructedCentralEdgeTwoCarrier constructedCentralEdgeTwoCarrier_height x

public theorem constructedCentralEdgeTwoOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedCentralEdgeTwoOrbit W) := by
  simpa [constructedCentralEdgeTwoOrbit] using
    centralEdgeOrbitOf_continuous W _ _ constructedCentralEdgeTwoCarrier_continuous

public theorem constructedCentralEdgeTwoOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeTwoOrbit W) (Metric.ball 0 1) := by
  simpa [constructedCentralEdgeTwoOrbit] using
    centralEdgeOrbitOf_injOn W _ _ ({0, e₁} : Set ToricLattice)
      ((Set.finite_singleton e₁).insert 0) ⟨0, by simp⟩
      constructedCentralEdgeTwoCarrier_componentSupport constructedCentralEdgeTwoCarrier_injOn

public def constructedCentralOneCellTwo
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 1 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralEdgeTwoOrbit W) (Metric.ball 0 1)
    (constructedCentralEdgeTwoOrbit_injOn W)

public theorem constructedCentralOneCellTwo_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralOneCellTwo W).source = Metric.ball 0 1 := rfl

public theorem constructedCentralOneCellTwo_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellTwo W) (Metric.closedBall 0 1) :=
  (constructedCentralEdgeTwoOrbit_continuous W).continuousOn

private theorem constructedCentralEdgeZeroCarrier_negOne :
    constructedCentralEdgeZeroCarrier (fun _ ↦ -1) = inclusion (false, 0) 0 := by
  simp [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroLowerBranch, lowerAxisZero]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem constructedCentralEdgeZeroCarrier_one :
    constructedCentralEdgeZeroCarrier (fun _ ↦ 1) = inclusion (true, 0) 0 := by
  norm_num [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroUpperBranch, upperAxisTwo]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem constructedCentralEdgeOneCarrier_negOne :
    constructedCentralEdgeOneCarrier (fun _ ↦ -1) = inclusion (false, 0) 0 := by
  simp [constructedCentralEdgeOneCarrier]
  congr 1
  funext i
  simp [singleAxis]

private theorem constructedCentralEdgeOneCarrier_one :
    constructedCentralEdgeOneCarrier (fun _ ↦ 1) = inclusion (true, -e₁) 0 := by
  norm_num [constructedCentralEdgeOneCarrier]
  congr 1
  funext i
  simp [singleAxis]

private theorem constructedCentralEdgeTwoCarrier_negOne :
    constructedCentralEdgeTwoCarrier (fun _ ↦ -1) = inclusion (false, 0) 0 := by
  simp [constructedCentralEdgeTwoCarrier]
  congr 1
  funext i
  simp [singleAxis]

private theorem constructedCentralEdgeTwoCarrier_one :
    constructedCentralEdgeTwoCarrier (fun _ ↦ 1) = inclusion (true, -e₂) 0 := by
  norm_num [constructedCentralEdgeTwoCarrier]
  congr 1
  funext i
  simp [singleAxis]

public theorem constructedCentralEdgeZeroOrbit_injOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeZeroOrbit W) (Metric.closedBall 0 1) := by
  have hcard : ({e₁, e₂} : Set ToricLattice).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem]
    · simp
    · simp [e₁, e₂]
  exact centralEdgeOrbitOf_injOn_closedBall W constructedCentralEdgeZeroCarrier
    constructedCentralEdgeZeroCarrier_height ({e₁, e₂} : Set ToricLattice) hcard
    constructedCentralEdgeZeroCarrier_componentSupport (constructedCentralEdgeZeroOrbit_injOn W)
    (upperV := 0) constructedCentralEdgeZeroCarrier_negOne
      constructedCentralEdgeZeroCarrier_one

public theorem constructedCentralEdgeOneOrbit_injOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeOneOrbit W) (Metric.closedBall 0 1) := by
  have hcard : ({0, e₂} : Set ToricLattice).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem]
    · simp
    · intro h
      simpa [e₂] using congrFun h 1
  exact centralEdgeOrbitOf_injOn_closedBall W constructedCentralEdgeOneCarrier
    constructedCentralEdgeOneCarrier_height ({0, e₂} : Set ToricLattice) hcard
    constructedCentralEdgeOneCarrier_componentSupport (constructedCentralEdgeOneOrbit_injOn W)
    (upperV := -e₁) constructedCentralEdgeOneCarrier_negOne
      constructedCentralEdgeOneCarrier_one

public theorem constructedCentralEdgeTwoOrbit_injOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralEdgeTwoOrbit W) (Metric.closedBall 0 1) := by
  have hcard : ({0, e₁} : Set ToricLattice).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem]
    · simp
    · intro h
      simpa [e₁] using congrFun h 0
  exact centralEdgeOrbitOf_injOn_closedBall W constructedCentralEdgeTwoCarrier
    constructedCentralEdgeTwoCarrier_height ({0, e₁} : Set ToricLattice) hcard
    constructedCentralEdgeTwoCarrier_componentSupport (constructedCentralEdgeTwoOrbit_injOn W)
    (upperV := -e₂) constructedCentralEdgeTwoCarrier_negOne
      constructedCentralEdgeTwoCarrier_one

public theorem constructedCentralOneCellZero_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellZero W).symm
      (constructedCentralOneCellZero W).target := by
  simpa [constructedCentralOneCellZero] using
    centralOrbitPartialEquiv_continuousOn_symm W (constructedCentralEdgeZeroOrbit W)
      (constructedCentralEdgeZeroOrbit_continuous W)
      (constructedCentralEdgeZeroOrbit_injOn W)
      (constructedCentralEdgeZeroOrbit_injOn_closedBall W)

public theorem constructedCentralOneCellOne_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellOne W).symm
      (constructedCentralOneCellOne W).target := by
  simpa [constructedCentralOneCellOne] using
    centralOrbitPartialEquiv_continuousOn_symm W (constructedCentralEdgeOneOrbit W)
      (constructedCentralEdgeOneOrbit_continuous W)
      (constructedCentralEdgeOneOrbit_injOn W)
      (constructedCentralEdgeOneOrbit_injOn_closedBall W)

public theorem constructedCentralOneCellTwo_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralOneCellTwo W).symm
      (constructedCentralOneCellTwo W).target := by
  simpa [constructedCentralOneCellTwo] using
    centralOrbitPartialEquiv_continuousOn_symm W (constructedCentralEdgeTwoOrbit W)
      (constructedCentralEdgeTwoOrbit_continuous W)
      (constructedCentralEdgeTwoOrbit_injOn W)
      (constructedCentralEdgeTwoOrbit_injOn_closedBall W)

private theorem centralEdgeOrbitOf_eq_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (x : Fin 1 → ℝ) (upper : Bool) (v : ToricLattice)
    (hx : F x = inclusion (upper, v) 0) :
    centralEdgeOrbitOf W F hF x = constructedCentralOriginOrbit W upper := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  apply @Quotient.sound S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
  change MulAction.orbitRel (Multiplicative ParameterLattice) S
    (centralEdgePointOf W F hF x) (constructedCentralOriginPoint W upper)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective v
  refine ⟨Additive.toMul lambda, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (((Additive.toMul lambda : Multiplicative ParameterLattice) •
    constructedCentralOrigin W upper :
    LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = F x
  rw [constructedCentralOrigin_smul_coe]
  change inclusion (upper, 0 + shearVector lambda) 0 = F x
  rw [hlambda, zero_add, hx]

public theorem constructedCentralEdgeOneOrbit_negOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeOneOrbit W (fun _ ↦ -1) =
      constructedCentralOriginOrbit W false := by
  exact centralEdgeOrbitOf_eq_origin W constructedCentralEdgeOneCarrier
    constructedCentralEdgeOneCarrier_height (fun _ ↦ -1) false 0
      constructedCentralEdgeOneCarrier_negOne

public theorem constructedCentralEdgeOneOrbit_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeOneOrbit W (fun _ ↦ 1) =
      constructedCentralOriginOrbit W true := by
  exact centralEdgeOrbitOf_eq_origin W constructedCentralEdgeOneCarrier
    constructedCentralEdgeOneCarrier_height (fun _ ↦ 1) true (-e₁)
      constructedCentralEdgeOneCarrier_one

public theorem constructedCentralEdgeTwoOrbit_negOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeTwoOrbit W (fun _ ↦ -1) =
      constructedCentralOriginOrbit W false := by
  exact centralEdgeOrbitOf_eq_origin W constructedCentralEdgeTwoCarrier
    constructedCentralEdgeTwoCarrier_height (fun _ ↦ -1) false 0
      constructedCentralEdgeTwoCarrier_negOne

public theorem constructedCentralEdgeTwoOrbit_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeTwoOrbit W (fun _ ↦ 1) =
      constructedCentralOriginOrbit W true := by
  exact centralEdgeOrbitOf_eq_origin W constructedCentralEdgeTwoCarrier
    constructedCentralEdgeTwoCarrier_height (fun _ ↦ 1) true (-e₂)
      constructedCentralEdgeTwoCarrier_one

public theorem constructedCentralOneCellOne_mapsTo_zeroCells
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralOneCellOne W) (Metric.sphere 0 1)
      (⋃ j : Fin 2, constructedCentralZeroCell W j '' Metric.closedBall 0 1) := by
  intro x hx
  rcases finOne_mem_sphere_eq_endpoints x hx with rfl | rfl
  · change constructedCentralEdgeOneOrbit W (fun _ ↦ 1) ∈ _
    rw [constructedCentralEdgeOneOrbit_one]
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]
  · change constructedCentralEdgeOneOrbit W (fun _ ↦ -1) ∈ _
    rw [constructedCentralEdgeOneOrbit_negOne]
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]

public theorem constructedCentralOneCellTwo_mapsTo_zeroCells
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralOneCellTwo W) (Metric.sphere 0 1)
      (⋃ j : Fin 2, constructedCentralZeroCell W j '' Metric.closedBall 0 1) := by
  intro x hx
  rcases finOne_mem_sphere_eq_endpoints x hx with rfl | rfl
  · change constructedCentralEdgeTwoOrbit W (fun _ ↦ 1) ∈ _
    rw [constructedCentralEdgeTwoOrbit_one]
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]
  · change constructedCentralEdgeTwoOrbit W (fun _ ↦ -1) ∈ _
    rw [constructedCentralEdgeTwoOrbit_negOne]
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [constructedCentralZeroCell]

private theorem toricPair_eq_translate_imp
    {a b c d k : ToricLattice} (hab : a ≠ b)
    (h : ({a, b} : Set ToricLattice) = (fun v ↦ v + k) '' ({c, d} : Set ToricLattice)) :
    (a = c + k ∧ b = d + k) ∨ (a = d + k ∧ b = c + k) := by
  have ha : a ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  have hb : b ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨v, hv, hvb⟩ := hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hab (hua.symm.trans hvb)).elim
  · exact Or.inl ⟨hua.symm, hvb.symm⟩
  · exact Or.inr ⟨hua.symm, hvb.symm⟩
  · exact (hab (hua.symm.trans hvb)).elim

private theorem edgeSupportZero_ne_translate_one (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₂} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₂)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h10
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega

private theorem edgeSupportZero_ne_translate_two (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₁)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega

private theorem edgeSupportOne_ne_translate_two (k : ToricLattice) :
    ({0, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := 0) (b := e₂) (c := 0) (d := e₁)
      (by
        intro heq
        have hcoord := congrFun heq 1
        simp [e₂] at hcoord) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega

private theorem centralEdgeOrbitOf_ne_of_support_not_translate
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F G : (Fin 1 → ℝ) → Carrier)
    (hF : ∀ x, carrierHeight (F x) = 0) (hG : ∀ x, carrierHeight (G x) = 0)
    (T U : Set ToricLattice)
    (hsupportF : ∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      componentSupport constructedModel (F x) = T)
    (hsupportG : ∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      componentSupport constructedModel (G x) = U)
    (hnot : ∀ k : ToricLattice, T ≠ (fun v ↦ v + k) '' U)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 1 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    centralEdgeOrbitOf W F hF x ≠ centralEdgeOrbitOf W G hG y := by
  intro hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (centralEdgePointOf W F hF x) (centralEdgePointOf W G hG y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (centralEdgePointOf W F hF x) (centralEdgePointOf W G hG y) hxy
  obtain ⟨lambda, hsupport⟩ :=
    centralOrbitRel_componentSupport_eq_translate W
      (centralEdgePointOf W F hF x) (centralEdgePointOf W G hG y) hrel
  change componentSupport constructedModel (F x) =
    (fun v ↦ v + shearVector lambda) '' componentSupport constructedModel (G y) at hsupport
  rw [hsupportF x hx, hsupportG y hy] at hsupport
  exact hnot (shearVector lambda) hsupport

private theorem constructedCentralEdgeZeroOrbit_eq_centralEdgeOrbitOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedCentralEdgeZeroOrbit W =
      centralEdgeOrbitOf W constructedCentralEdgeZeroCarrier
        constructedCentralEdgeZeroCarrier_height := by
  funext x
  rfl

public theorem constructedCentralEdgeZeroOrbit_ne_oneOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 1 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralEdgeZeroOrbit W x ≠ constructedCentralEdgeOneOrbit W y := by
  rw [constructedCentralEdgeZeroOrbit_eq_centralEdgeOrbitOf W]
  exact centralEdgeOrbitOf_ne_of_support_not_translate W
    constructedCentralEdgeZeroCarrier constructedCentralEdgeOneCarrier
    constructedCentralEdgeZeroCarrier_height constructedCentralEdgeOneCarrier_height
    ({e₁, e₂} : Set ToricLattice) ({0, e₂} : Set ToricLattice)
    constructedCentralEdgeZeroCarrier_componentSupport
    constructedCentralEdgeOneCarrier_componentSupport edgeSupportZero_ne_translate_one
    x hx y hy

public theorem constructedCentralEdgeZeroOrbit_ne_twoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 1 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralEdgeZeroOrbit W x ≠ constructedCentralEdgeTwoOrbit W y := by
  rw [constructedCentralEdgeZeroOrbit_eq_centralEdgeOrbitOf W]
  exact centralEdgeOrbitOf_ne_of_support_not_translate W
    constructedCentralEdgeZeroCarrier constructedCentralEdgeTwoCarrier
    constructedCentralEdgeZeroCarrier_height constructedCentralEdgeTwoCarrier_height
    ({e₁, e₂} : Set ToricLattice) ({0, e₁} : Set ToricLattice)
    constructedCentralEdgeZeroCarrier_componentSupport
    constructedCentralEdgeTwoCarrier_componentSupport edgeSupportZero_ne_translate_two
    x hx y hy

public theorem constructedCentralEdgeOneOrbit_ne_twoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 1 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralEdgeOneOrbit W x ≠ constructedCentralEdgeTwoOrbit W y := by
  exact centralEdgeOrbitOf_ne_of_support_not_translate W
    constructedCentralEdgeOneCarrier constructedCentralEdgeTwoCarrier
    constructedCentralEdgeOneCarrier_height constructedCentralEdgeTwoCarrier_height
    ({0, e₂} : Set ToricLattice) ({0, e₁} : Set ToricLattice)
    constructedCentralEdgeOneCarrier_componentSupport
    constructedCentralEdgeTwoCarrier_componentSupport edgeSupportOne_ne_translate_two
    x hx y hy

public def constructedCentralOneCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    PartialEquiv (Fin 1 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  ![constructedCentralOneCellZero W, constructedCentralOneCellOne W,
    constructedCentralOneCellTwo W] i

public theorem constructedCentralOneCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    (constructedCentralOneCell W i).source = Metric.ball 0 1 := by
  fin_cases i
  · exact constructedCentralOneCellZero_source_eq W
  · exact constructedCentralOneCellOne_source_eq W
  · exact constructedCentralOneCellTwo_source_eq W

public theorem constructedCentralOneCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    ContinuousOn (constructedCentralOneCell W i) (Metric.closedBall 0 1) := by
  fin_cases i
  · exact constructedCentralOneCellZero_continuousOn W
  · exact constructedCentralOneCellOne_continuousOn W
  · exact constructedCentralOneCellTwo_continuousOn W

public theorem constructedCentralOneCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    ContinuousOn (constructedCentralOneCell W i).symm
      (constructedCentralOneCell W i).target := by
  fin_cases i
  · exact constructedCentralOneCellZero_continuousOn_symm W
  · exact constructedCentralOneCellOne_continuousOn_symm W
  · exact constructedCentralOneCellTwo_continuousOn_symm W

public theorem constructedCentralOneCell_mapsTo_zeroCells
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    MapsTo (constructedCentralOneCell W i) (Metric.sphere 0 1)
      (⋃ j : Fin 2, constructedCentralZeroCell W j '' Metric.closedBall 0 1) := by
  fin_cases i
  · exact constructedCentralOneCellZero_mapsTo_zeroCells W
  · exact constructedCentralOneCellOne_mapsTo_zeroCells W
  · exact constructedCentralOneCellTwo_mapsTo_zeroCells W

public theorem constructedCentralOneCell_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Fin 3)).PairwiseDisjoint
      (fun i ↦ constructedCentralOneCell W i '' Metric.ball 0 1) := by
  have hzeroOne : Disjoint
      (constructedCentralOneCellZero W '' Metric.ball 0 1)
      (constructedCentralOneCellOne W '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    intro z
    rintro ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    exact constructedCentralEdgeZeroOrbit_ne_oneOrbit W x hx y hy (hxz.trans hyz.symm)
  have hzeroTwo : Disjoint
      (constructedCentralOneCellZero W '' Metric.ball 0 1)
      (constructedCentralOneCellTwo W '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    intro z
    rintro ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    exact constructedCentralEdgeZeroOrbit_ne_twoOrbit W x hx y hy (hxz.trans hyz.symm)
  have honeTwo : Disjoint
      (constructedCentralOneCellOne W '' Metric.ball 0 1)
      (constructedCentralOneCellTwo W '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    intro z
    rintro ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    exact constructedCentralEdgeOneOrbit_ne_twoOrbit W x hx y hy (hxz.trans hyz.symm)
  intro i hi j hj hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hzeroOne
  · exact hzeroTwo
  · exact hzeroOne.symm
  · exact (hij rfl).elim
  · exact honeTwo
  · exact hzeroTwo.symm
  · exact honeTwo.symm
  · exact (hij rfl).elim

private theorem constructedCentralOriginOrbit_ne_centralEdgeOrbitOf
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (F : (Fin 1 → ℝ) → Carrier) (hF : ∀ x, carrierHeight (F x) = 0)
    (T : Set ToricLattice) (hTcard : T.ncard = 2)
    (hsupport : ∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) 1,
      componentSupport constructedModel (F x) = T)
    (upper : Bool) (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedCentralOriginOrbit W upper ≠ centralEdgeOrbitOf W F hF x := by
  intro hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralOriginPoint W upper) (centralEdgePointOf W F hF x) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralOriginPoint W upper) (centralEdgePointOf W F hF x) hxy
  have hn := centralOrbitRel_componentSupport_ncard_eq W
    (constructedCentralOriginPoint W upper) (centralEdgePointOf W F hF x) hrel
  change (componentSupport constructedModel (inclusion (upper, 0) 0)).ncard =
    (componentSupport constructedModel (F x)).ncard at hn
  rw [carrierOrigin_componentSupport_ncard (upper, 0), hsupport x hx, hTcard] at hn
  omega

private theorem constructedCentralOriginOrbit_ne_edgeZero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedCentralOriginOrbit W upper ≠ constructedCentralEdgeZeroOrbit W x := by
  rw [constructedCentralEdgeZeroOrbit_eq_centralEdgeOrbitOf W]
  exact constructedCentralOriginOrbit_ne_centralEdgeOrbitOf W
    constructedCentralEdgeZeroCarrier constructedCentralEdgeZeroCarrier_height
    ({e₁, e₂} : Set ToricLattice) (by
      rw [Set.ncard_insert_of_notMem]
      · simp
      · simp [e₁, e₂])
    constructedCentralEdgeZeroCarrier_componentSupport upper x hx

private theorem constructedCentralOriginOrbit_ne_edgeOne
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedCentralOriginOrbit W upper ≠ constructedCentralEdgeOneOrbit W x := by
  exact constructedCentralOriginOrbit_ne_centralEdgeOrbitOf W
    constructedCentralEdgeOneCarrier constructedCentralEdgeOneCarrier_height
    ({0, e₂} : Set ToricLattice) (by
      rw [Set.ncard_insert_of_notMem]
      · simp
      · intro h
        simpa [e₂] using congrFun h 1)
    constructedCentralEdgeOneCarrier_componentSupport upper x hx

private theorem constructedCentralOriginOrbit_ne_edgeTwo
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (upper : Bool)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    constructedCentralOriginOrbit W upper ≠ constructedCentralEdgeTwoOrbit W x := by
  exact constructedCentralOriginOrbit_ne_centralEdgeOrbitOf W
    constructedCentralEdgeTwoCarrier constructedCentralEdgeTwoCarrier_height
    ({0, e₁} : Set ToricLattice) (by
      rw [Set.ncard_insert_of_notMem]
      · simp
      · intro h
        simpa [e₁] using congrFun h 0)
    constructedCentralEdgeTwoCarrier_componentSupport upper x hx

public theorem constructedCentralZeroCell_oneCell_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (j : Fin 3) :
    Disjoint (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedCentralOneCell W j '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  intro z
  rintro ⟨a, ha, haz⟩ ⟨x, hx, hxz⟩
  fin_cases i <;> fin_cases j
  · exact constructedCentralOriginOrbit_ne_edgeZero W false x hx (haz.trans hxz.symm)
  · exact constructedCentralOriginOrbit_ne_edgeOne W false x hx (haz.trans hxz.symm)
  · exact constructedCentralOriginOrbit_ne_edgeTwo W false x hx (haz.trans hxz.symm)
  · exact constructedCentralOriginOrbit_ne_edgeZero W true x hx (haz.trans hxz.symm)
  · exact constructedCentralOriginOrbit_ne_edgeOne W true x hx (haz.trans hxz.symm)
  · exact constructedCentralOriginOrbit_ne_edgeTwo W true x hx (haz.trans hxz.symm)

public theorem constructedCentralZeroCells_subset_oneCell_closed
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    (⋃ i : Fin 2, constructedCentralZeroCell W i '' Metric.closedBall 0 1) ⊆
      constructedCentralOneCell W j '' Metric.closedBall 0 1 := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨a, ha, haz⟩ := hi
  fin_cases i <;> fin_cases j
  · refine ⟨fun _ ↦ -1, by simp, ?_⟩
    change constructedCentralEdgeZeroOrbit W (fun _ ↦ -1) = z
    rw [constructedCentralEdgeZeroOrbit_negOne]
    simpa [constructedCentralZeroCell] using haz
  · refine ⟨fun _ ↦ -1, by simp, ?_⟩
    change constructedCentralEdgeOneOrbit W (fun _ ↦ -1) = z
    rw [constructedCentralEdgeOneOrbit_negOne]
    simpa [constructedCentralZeroCell] using haz
  · refine ⟨fun _ ↦ -1, by simp, ?_⟩
    change constructedCentralEdgeTwoOrbit W (fun _ ↦ -1) = z
    rw [constructedCentralEdgeTwoOrbit_negOne]
    simpa [constructedCentralZeroCell] using haz
  · refine ⟨fun _ ↦ 1, by simp, ?_⟩
    change constructedCentralEdgeZeroOrbit W (fun _ ↦ 1) = z
    rw [constructedCentralEdgeZeroOrbit_one]
    simpa [constructedCentralZeroCell] using haz
  · refine ⟨fun _ ↦ 1, by simp, ?_⟩
    change constructedCentralEdgeOneOrbit W (fun _ ↦ 1) = z
    rw [constructedCentralEdgeOneOrbit_one]
    simpa [constructedCentralZeroCell] using haz
  · refine ⟨fun _ ↦ 1, by simp, ?_⟩
    change constructedCentralEdgeTwoOrbit W (fun _ ↦ 1) = z
    rw [constructedCentralEdgeTwoOrbit_one]
    simpa [constructedCentralZeroCell] using haz

public theorem constructedCentralOneCell_closedBall_image_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j : Fin 3) :
    constructedCentralOneCell W j '' Metric.closedBall 0 1 =
      (constructedCentralOneCell W j '' Metric.ball 0 1) ∪
        (⋃ i : Fin 2, constructedCentralZeroCell W i '' Metric.closedBall 0 1) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases finOne_mem_closedBall_cases x hx with hxOpen | hxPos | hxNeg
    · exact Or.inl ⟨x, hxOpen, rfl⟩
    · right
      apply constructedCentralOneCell_mapsTo_zeroCells W j
      rw [hxPos]
      simp
    · right
      apply constructedCentralOneCell_mapsTo_zeroCells W j
      rw [hxNeg]
      simp
  · rintro (hz | hz)
    · obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, Metric.ball_subset_closedBall hx, rfl⟩
    · exact constructedCentralZeroCells_subset_oneCell_closed W j hz

/-- The coordinate linear isomorphism from the real characteristic-map plane to `ℂ`. -/
public def centralPhaseLinearComplex (x : Fin 2 → ℝ) : ℂ :=
  (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

/-- Radial transport from the supremum norm used on `Fin 2 → ℝ` to the Euclidean norm on
`ℂ`.  It preserves the norm, so the square-shaped Lean unit ball is sent to the round complex
unit disk. -/
public def centralPhaseDiskComplex (x : Fin 2 → ℝ) : ℂ :=
  if x = 0 then 0
  else ((‖x‖ / ‖centralPhaseLinearComplex x‖ : ℝ) : ℂ) * centralPhaseLinearComplex x

private theorem centralPhaseLinearComplex_injective :
    Function.Injective centralPhaseLinearComplex := by
  intro x y hxy
  funext i
  fin_cases i
  · have hre := congrArg Complex.re hxy
    simpa [centralPhaseLinearComplex] using hre
  · have him := congrArg Complex.im hxy
    simpa [centralPhaseLinearComplex] using him

private theorem centralPhaseLinearComplex_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    centralPhaseLinearComplex x ≠ 0 := by
  intro h
  apply hx
  apply centralPhaseLinearComplex_injective
  simpa [centralPhaseLinearComplex] using h

public theorem norm_centralPhaseDiskComplex (x : Fin 2 → ℝ) :
    ‖centralPhaseDiskComplex x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [centralPhaseDiskComplex, hx]
  · simp only [centralPhaseDiskComplex, hx, ↓reduceIte, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (centralPhaseLinearComplex_ne_zero hx))

private theorem centralPhaseDiskComplex_re (x : Fin 2 → ℝ) :
    (centralPhaseDiskComplex x).re =
      if x = 0 then 0 else (‖x‖ / ‖centralPhaseLinearComplex x‖) * x 0 := by
  by_cases hx : x = 0
  · simp [centralPhaseDiskComplex, hx]
  · simp [centralPhaseDiskComplex, centralPhaseLinearComplex, hx, Complex.mul_re]

/-- The slit-sphere coordinate in the lower affine chart. -/
public def centralPhaseDiskLowerCoordinate (x : Fin 2 → ℝ) : ℂ :=
  -((1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x)) ^ 2

/-- Its reciprocal coordinate in the upper affine chart. -/
public def centralPhaseDiskUpperCoordinate (x : Fin 2 → ℝ) : ℂ :=
  -((1 - centralPhaseDiskComplex x) / (1 + centralPhaseDiskComplex x)) ^ 2

private theorem centralPhaseDisk_one_add_ne_zero_of_nonneg
    (x : Fin 2 → ℝ) (hx : 0 ≤ x 0) :
    (1 : ℂ) + centralPhaseDiskComplex x ≠ 0 := by
  by_cases hx0 : x = 0
  · simp [centralPhaseDiskComplex, hx0]
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    rw [centralPhaseDiskComplex_re, ite_eq_right hx0] at hre
    have hscale : 0 ≤ ‖x‖ / ‖centralPhaseLinearComplex x‖ :=
      div_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith

private theorem centralPhaseDisk_one_sub_ne_zero_of_nonpos
    (x : Fin 2 → ℝ) (hx : x 0 ≤ 0) :
    (1 : ℂ) - centralPhaseDiskComplex x ≠ 0 := by
  by_cases hx0 : x = 0
  · simp [centralPhaseDiskComplex, hx0]
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    rw [centralPhaseDiskComplex_re, ite_eq_right hx0] at hre
    have hscale : 0 ≤ ‖x‖ / ‖centralPhaseLinearComplex x‖ :=
      div_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith

private theorem centralPhaseDisk_coordinates_reciprocal
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

/-- The first phase two-cell before passage to the deck-orbit quotient.  Its interior is the
complex coordinate axis cut along the positive real one-cell. -/
public def constructedCentralPhaseFaceZeroCarrier (x : Fin 2 → ℝ) : Carrier :=
  if x 0 ≤ 0 then
    inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate x))
  else
    inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate x))

public theorem constructedCentralPhaseFaceZeroCarrier_height (x : Fin 2 → ℝ) :
    carrierHeight (constructedCentralPhaseFaceZeroCarrier x) = 0 := by
  by_cases hx : x 0 ≤ 0 <;>
    simp [constructedCentralPhaseFaceZeroCarrier, hx, carrierHeight_inclusion, rawHeight,
      lowerAxisZero, upperAxisTwo]

private theorem constructedCentralPhaseFaceZeroCarrier_eq_on_seam
    (x : Fin 2 → ℝ) (hx : x 0 = 0) :
    inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate x)) =
      inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate x)) := by
  apply (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mpr
  apply centralPhaseDisk_coordinates_reciprocal
  · exact centralPhaseDisk_one_add_ne_zero_of_nonneg x (by rw [hx])
  · exact centralPhaseDisk_one_sub_ne_zero_of_nonpos x (by rw [hx])

private theorem centralPhaseLinearComplex_continuous : Continuous centralPhaseLinearComplex := by
  unfold centralPhaseLinearComplex
  fun_prop

public theorem centralPhaseDiskComplex_continuous : Continuous centralPhaseDiskComplex := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    rw [show centralPhaseDiskComplex 0 = 0 by simp [centralPhaseDiskComplex],
      dist_zero_right, norm_centralPhaseDiskComplex]
    simpa [dist_zero_right] using hy
  · let g : (Fin 2 → ℝ) → ℂ := fun y ↦
      ((‖y‖ / ‖centralPhaseLinearComplex y‖ : ℝ) : ℂ) * centralPhaseLinearComplex y
    have hlinear : ContinuousAt centralPhaseLinearComplex x :=
      centralPhaseLinearComplex_continuous.continuousAt
    have hratio : ContinuousAt (fun y : Fin 2 → ℝ ↦
        ‖y‖ / ‖centralPhaseLinearComplex y‖) x :=
      continuous_norm.continuousAt.div hlinear.norm
        (norm_ne_zero_iff.mpr (centralPhaseLinearComplex_ne_zero hx))
    have hcoe : ContinuousAt (fun y : Fin 2 → ℝ ↦
        ((‖y‖ / ‖centralPhaseLinearComplex y‖ : ℝ) : ℂ)) x := by
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.comp hratio
    have hg : ContinuousAt g x := hcoe.mul hlinear
    apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [g, centralPhaseDiskComplex, hy]

public theorem centralPhaseDiskComplex_injective :
    Function.Injective centralPhaseDiskComplex := by
  intro x y hxy
  have hnorm : ‖x‖ = ‖y‖ := by
    rw [← norm_centralPhaseDiskComplex x, ← norm_centralPhaseDiskComplex y, hxy]
  by_cases hx0 : x = 0
  · subst x
    have hy0 : y = 0 := norm_eq_zero.mp (by simpa using hnorm.symm)
    exact hy0.symm
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    exact hx0 (norm_eq_zero.mp (by simpa using hnorm))
  let ax : ℝ := ‖x‖ / ‖centralPhaseLinearComplex x‖
  let ay : ℝ := ‖y‖ / ‖centralPhaseLinearComplex y‖
  have hax : 0 < ax := div_pos (norm_pos_iff.mpr hx0)
    (norm_pos_iff.mpr (centralPhaseLinearComplex_ne_zero hx0))
  have hay : 0 < ay := div_pos (norm_pos_iff.mpr hy0)
    (norm_pos_iff.mpr (centralPhaseLinearComplex_ne_zero hy0))
  have hcomplex : (ax : ℂ) * centralPhaseLinearComplex x =
      (ay : ℂ) * centralPhaseLinearComplex y := by
    simpa [centralPhaseDiskComplex, hx0, hy0, ax, ay] using hxy
  have hvec : ax • x = ay • y := by
    funext i
    fin_cases i
    · have hre := congrArg Complex.re hcomplex
      simpa [centralPhaseLinearComplex, Complex.mul_re] using hre
    · have him := congrArg Complex.im hcomplex
      simpa [centralPhaseLinearComplex, Complex.mul_im] using him
  have hscaledNorm := congrArg norm hvec
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hax, abs_of_pos hay, hnorm] at hscaledNorm
  have haxy : ax = ay := by
    exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr hy0) hscaledNorm)
  funext i
  have hi := congrFun hvec i
  rw [haxy] at hi
  exact (mul_left_cancel₀ (ne_of_gt hay) hi)

private theorem centralPhaseDiskComplex_norm_lt_one
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    ‖centralPhaseDiskComplex x‖ < 1 := by
  rw [norm_centralPhaseDiskComplex]
  simpa [Metric.mem_ball, dist_zero_right] using hx

private theorem centralPhaseDiskCayley_re_pos
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    0 < ((1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x)).re := by
  let z := centralPhaseDiskComplex x
  have hnorm : ‖z‖ < 1 := centralPhaseDiskComplex_norm_lt_one hx
  have hminus : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz : z = 1 := (sub_eq_zero.mp h).symm
    rw [hz] at hnorm
    norm_num at hnorm
  have hnormSq : Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hden : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hminus
  have hre : ((1 + z) / (1 - z)).re =
      (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_re]
    field_simp [ne_of_gt hden]
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [hre]
  exact div_pos (sub_pos.mpr hnormSq) hden

private theorem norm_eq_one_of_mem_closedBall_not_ball
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.closedBall 0 1)
    (hxb : x ∉ Metric.ball 0 1) : ‖x‖ = 1 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [Metric.mem_ball, dist_zero_right] at hxb
  exact le_antisymm hx (le_of_not_gt hxb)

private theorem centralPhaseDiskCayley_re_eq_zero_of_norm_eq_one
    (x : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hminus : (1 : ℂ) - centralPhaseDiskComplex x ≠ 0) :
    ((1 + centralPhaseDiskComplex x) /
      (1 - centralPhaseDiskComplex x)).re = 0 := by
  let z := centralPhaseDiskComplex x
  change ((1 + z) / (1 - z)).re = 0
  have hznorm : ‖z‖ = 1 := by
    rw [norm_centralPhaseDiskComplex]
    exact hxnorm
  have hnormSq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hznorm]
    norm_num
  have hden : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hminus
  rw [Complex.div_re]
  field_simp [ne_of_gt hden]
  rw [Complex.normSq_apply] at hnormSq
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    Complex.sub_re, Complex.sub_im]
  nlinarith

private theorem centralPhaseDiskUpperCayley_re_pos
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    0 < ((1 - centralPhaseDiskComplex x) /
      (1 + centralPhaseDiskComplex x)).re := by
  let z := centralPhaseDiskComplex x
  have hnorm : ‖z‖ < 1 := centralPhaseDiskComplex_norm_lt_one hx
  have hplus : (1 : ℂ) + z ≠ 0 := by
    intro h
    have hz : z = -1 := eq_neg_of_add_eq_zero_right h
    rw [hz] at hnorm
    norm_num at hnorm
  have hnormSq : Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hden : 0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr hplus
  have hre : ((1 - z) / (1 + z)).re =
      (1 - Complex.normSq z) / Complex.normSq (1 + z) := by
    rw [Complex.div_re]
    field_simp [ne_of_gt hden]
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [hre]
  exact div_pos (sub_pos.mpr hnormSq) hden

private theorem centralPhaseDiskUpperCayley_re_eq_zero_of_norm_eq_one
    (x : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hplus : (1 : ℂ) + centralPhaseDiskComplex x ≠ 0) :
    ((1 - centralPhaseDiskComplex x) /
      (1 + centralPhaseDiskComplex x)).re = 0 := by
  let z := centralPhaseDiskComplex x
  change ((1 - z) / (1 + z)).re = 0
  have hznorm : ‖z‖ = 1 := by
    rw [norm_centralPhaseDiskComplex]
    exact hxnorm
  have hnormSq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hznorm]
    norm_num
  have hden : 0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr hplus
  rw [Complex.div_re]
  field_simp [ne_of_gt hden]
  rw [Complex.normSq_apply] at hnormSq
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    Complex.sub_re, Complex.sub_im]
  nlinarith

private theorem centralPhaseDiskLowerCoordinate_eq_im_sq_of_norm_eq_one
    (x : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hminus : (1 : ℂ) - centralPhaseDiskComplex x ≠ 0) :
    centralPhaseDiskLowerCoordinate x =
      (((((1 + centralPhaseDiskComplex x) /
        (1 - centralPhaseDiskComplex x)).im) ^ 2 : ℝ) : ℂ) := by
  let c := (1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x)
  have hc : c.re = 0 :=
    centralPhaseDiskCayley_re_eq_zero_of_norm_eq_one x hxnorm hminus
  change -(c ^ 2) = ((c.im ^ 2 : ℝ) : ℂ)
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, hc]
  · simp [pow_two, Complex.mul_im, hc]

private theorem centralPhaseDiskUpperCoordinate_eq_im_sq_of_norm_eq_one
    (x : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hplus : (1 : ℂ) + centralPhaseDiskComplex x ≠ 0) :
    centralPhaseDiskUpperCoordinate x =
      (((((1 - centralPhaseDiskComplex x) /
        (1 + centralPhaseDiskComplex x)).im) ^ 2 : ℝ) : ℂ) := by
  let c := (1 - centralPhaseDiskComplex x) / (1 + centralPhaseDiskComplex x)
  have hc : c.re = 0 :=
    centralPhaseDiskUpperCayley_re_eq_zero_of_norm_eq_one x hxnorm hplus
  change -(c ^ 2) = ((c.im ^ 2 : ℝ) : ℂ)
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, hc]
  · simp [pow_two, Complex.mul_im, hc]

private theorem centralPhaseDiskLowerCoordinate_ne_of_norm_eq_one_of_mem_ball
    (x y : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hxminus : (1 : ℂ) - centralPhaseDiskComplex x ≠ 0)
    (hy : y ∈ Metric.ball 0 1) :
    centralPhaseDiskLowerCoordinate x ≠ centralPhaseDiskLowerCoordinate y := by
  intro hxy
  let cx := (1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x)
  let cy := (1 + centralPhaseDiskComplex y) / (1 - centralPhaseDiskComplex y)
  have hsq : cx ^ 2 = cy ^ 2 := by
    simpa [centralPhaseDiskLowerCoordinate, cx, cy] using neg_inj.mp hxy
  have hfac : (cx - cy) * (cx + cy) = 0 := by
    calc
      (cx - cy) * (cx + cy) = cx ^ 2 - cy ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  have hcx : cx.re = 0 :=
    centralPhaseDiskCayley_re_eq_zero_of_norm_eq_one x hxnorm hxminus
  have hcy : 0 < cy.re := centralPhaseDiskCayley_re_pos hy
  rcases mul_eq_zero.mp hfac with hsame | hopp
  · have hre := congrArg Complex.re (sub_eq_zero.mp hsame)
    linarith
  · have hre := congrArg Complex.re (eq_neg_of_add_eq_zero_left hopp)
    have hre' : cx.re = -cy.re := by simpa using hre
    linarith

private theorem centralPhaseDiskUpperCoordinate_ne_of_norm_eq_one_of_mem_ball
    (x y : Fin 2 → ℝ) (hxnorm : ‖x‖ = 1)
    (hxplus : (1 : ℂ) + centralPhaseDiskComplex x ≠ 0)
    (hy : y ∈ Metric.ball 0 1) :
    centralPhaseDiskUpperCoordinate x ≠ centralPhaseDiskUpperCoordinate y := by
  intro hxy
  let cx := (1 - centralPhaseDiskComplex x) / (1 + centralPhaseDiskComplex x)
  let cy := (1 - centralPhaseDiskComplex y) / (1 + centralPhaseDiskComplex y)
  have hsq : cx ^ 2 = cy ^ 2 := by
    simpa [centralPhaseDiskUpperCoordinate, cx, cy] using neg_inj.mp hxy
  have hfac : (cx - cy) * (cx + cy) = 0 := by
    calc
      (cx - cy) * (cx + cy) = cx ^ 2 - cy ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  have hcx : cx.re = 0 :=
    centralPhaseDiskUpperCayley_re_eq_zero_of_norm_eq_one x hxnorm hxplus
  have hcy : 0 < cy.re := centralPhaseDiskUpperCayley_re_pos hy
  rcases mul_eq_zero.mp hfac with hsame | hopp
  · have hre := congrArg Complex.re (sub_eq_zero.mp hsame)
    linarith
  · have hre := congrArg Complex.re (eq_neg_of_add_eq_zero_left hopp)
    have hre' : cx.re = -cy.re := by simpa using hre
    linarith

private theorem centralPhaseDiskCayley_injectiveOn :
    Set.InjOn
      (fun x : Fin 2 → ℝ ↦
        (1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x))
      (Metric.ball 0 1) := by
  intro x hx y hy hxy
  have hxminus : (1 : ℂ) - centralPhaseDiskComplex x ≠ 0 := by
    intro h
    have hz : centralPhaseDiskComplex x = 1 := (sub_eq_zero.mp h).symm
    have := centralPhaseDiskComplex_norm_lt_one hx
    rw [hz] at this
    norm_num at this
  have hyminus : (1 : ℂ) - centralPhaseDiskComplex y ≠ 0 := by
    intro h
    have hz : centralPhaseDiskComplex y = 1 := (sub_eq_zero.mp h).symm
    have := centralPhaseDiskComplex_norm_lt_one hy
    rw [hz] at this
    norm_num at this
  have hzeta : centralPhaseDiskComplex x = centralPhaseDiskComplex y := by
    field_simp [hxminus, hyminus] at hxy
    linear_combination hxy / 2
  exact centralPhaseDiskComplex_injective hzeta

private theorem centralPhaseDiskLowerCoordinate_injOn :
    Set.InjOn centralPhaseDiskLowerCoordinate (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let cx := (1 + centralPhaseDiskComplex x) / (1 - centralPhaseDiskComplex x)
  let cy := (1 + centralPhaseDiskComplex y) / (1 - centralPhaseDiskComplex y)
  have hsq : cx ^ 2 = cy ^ 2 := by
    simpa [centralPhaseDiskLowerCoordinate, cx, cy] using neg_inj.mp hxy
  have hfac : (cx - cy) * (cx + cy) = 0 := by
    calc
      (cx - cy) * (cx + cy) = cx ^ 2 - cy ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfac with hsame | hopp
  · apply centralPhaseDiskCayley_injectiveOn hx hy
    exact sub_eq_zero.mp hsame
  · have hre := congrArg Complex.re (eq_neg_of_add_eq_zero_left hopp)
    have hcx := centralPhaseDiskCayley_re_pos hx
    have hcy := centralPhaseDiskCayley_re_pos hy
    simp [cx, cy] at hre
    linarith

private theorem centralPhaseDisk_one_add_ne_zero_of_ball
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    (1 : ℂ) + centralPhaseDiskComplex x ≠ 0 := by
  intro h
  have hz : centralPhaseDiskComplex x = -1 := eq_neg_of_add_eq_zero_right h
  have hnorm := centralPhaseDiskComplex_norm_lt_one hx
  rw [hz] at hnorm
  norm_num at hnorm

private theorem centralPhaseDisk_one_sub_ne_zero_of_ball
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) :
    (1 : ℂ) - centralPhaseDiskComplex x ≠ 0 := by
  intro h
  have hz : centralPhaseDiskComplex x = 1 := (sub_eq_zero.mp h).symm
  have hnorm := centralPhaseDiskComplex_norm_lt_one hx
  rw [hz] at hnorm
  norm_num at hnorm

public theorem constructedCentralPhaseFaceZeroCarrier_injOn :
    Set.InjOn constructedCentralPhaseFaceZeroCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  by_cases hx0 : x 0 ≤ 0
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have hraw := (inclusion_isOpenEmbedding (false, 0)).injective hxy
      have hcoord := congrFun hraw 0
      simp only [lowerAxisZero, Matrix.cons_val_zero] at hcoord
      exact centralPhaseDiskLowerCoordinate_injOn hx hy hcoord
    · simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have hcross := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy
      have hyrec := centralPhaseDisk_coordinates_reciprocal y
        (centralPhaseDisk_one_add_ne_zero_of_ball hy)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hy)
      have hinv : (centralPhaseDiskLowerCoordinate x)⁻¹ =
          (centralPhaseDiskLowerCoordinate y)⁻¹ := hcross.2.symm.trans hyrec.2
      exact centralPhaseDiskLowerCoordinate_injOn hx hy (inv_injective hinv)
  · by_cases hy0 : y 0 ≤ 0
    · simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have hcross := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy.symm
      have hxrec := centralPhaseDisk_coordinates_reciprocal x
        (centralPhaseDisk_one_add_ne_zero_of_ball hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hx)
      have hinv : (centralPhaseDiskLowerCoordinate y)⁻¹ =
          (centralPhaseDiskLowerCoordinate x)⁻¹ := hcross.2.symm.trans hxrec.2
      exact centralPhaseDiskLowerCoordinate_injOn hx hy (inv_injective hinv).symm
    · simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have hraw := (inclusion_isOpenEmbedding (true, 0)).injective hxy
      have hcoord := congrFun hraw 2
      simp only [upperAxisTwo, Matrix.cons_val_two] at hcoord
      have hxrec := centralPhaseDisk_coordinates_reciprocal x
        (centralPhaseDisk_one_add_ne_zero_of_ball hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hx)
      have hyrec := centralPhaseDisk_coordinates_reciprocal y
        (centralPhaseDisk_one_add_ne_zero_of_ball hy)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hy)
      apply centralPhaseDiskLowerCoordinate_injOn hx hy
      apply inv_injective
      rwa [← hxrec.2, ← hyrec.2]

private theorem constructedCentralPhaseFaceZeroCarrier_ne_of_mem_boundary
    (x y : Fin 2 → ℝ) (hx : x ∈ Metric.closedBall 0 1)
    (hxb : x ∉ Metric.ball 0 1) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralPhaseFaceZeroCarrier x ≠
      constructedCentralPhaseFaceZeroCarrier y := by
  have hxnorm := norm_eq_one_of_mem_closedBall_not_ball hx hxb
  by_cases hx0 : x 0 ≤ 0
  · have hxminus := centralPhaseDisk_one_sub_ne_zero_of_nonpos x hx0
    have hLowerNe :=
      centralPhaseDiskLowerCoordinate_ne_of_norm_eq_one_of_mem_ball
        x y hxnorm hxminus hy
    by_cases hy0 : y 0 ≤ 0
    · intro hxy
      simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      apply hLowerNe
      have hraw := (inclusion_isOpenEmbedding (false, 0)).injective hxy
      have hcoord := congrFun hraw 0
      simpa [lowerAxisZero] using hcoord
    · intro hxy
      simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have he := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy
      have hxplus : (1 : ℂ) + centralPhaseDiskComplex x ≠ 0 := by
        intro hplus
        apply he.1
        simp [centralPhaseDiskLowerCoordinate, hplus]
      have hxrec := centralPhaseDisk_coordinates_reciprocal x hxplus hxminus
      exact centralPhaseDiskUpperCoordinate_ne_of_norm_eq_one_of_mem_ball
        x y hxnorm hxplus hy (hxrec.2.trans he.2.symm)
  · have hxplus := centralPhaseDisk_one_add_ne_zero_of_nonneg x
      (le_of_lt (lt_of_not_ge hx0))
    have hUpperNe :=
      centralPhaseDiskUpperCoordinate_ne_of_norm_eq_one_of_mem_ball
        x y hxnorm hxplus hy
    by_cases hy0 : y 0 ≤ 0
    · intro hxy
      simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      have he := (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp hxy.symm
      have hyrec := centralPhaseDisk_coordinates_reciprocal y
        (centralPhaseDisk_one_add_ne_zero_of_ball hy)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hy)
      exact hUpperNe (he.2.trans hyrec.2.symm)
    · intro hxy
      simp only [constructedCentralPhaseFaceZeroCarrier, hx0, hy0] at hxy
      apply hUpperNe
      have hraw := (inclusion_isOpenEmbedding (true, 0)).injective hxy
      have hcoord := congrFun hraw 2
      simpa [upperAxisTwo] using hcoord

private theorem finOne_mem_closedBall_of_bounds (x : Fin 1 → ℝ)
    (hlower : -1 ≤ x 0) (hupper : x 0 ≤ 1) :
    x ∈ Metric.closedBall 0 1 := by
  have hx : x = fun _ ↦ x 0 := by
    funext i
    fin_cases i
    rfl
  rw [Metric.mem_closedBall, dist_zero_right, hx]
  simpa [Pi.norm_def, Real.norm_eq_abs, abs_le] using ⟨hlower, hupper⟩

public theorem constructedCentralPhaseFaceZeroCarrier_boundary_mem_edgeZero
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    constructedCentralPhaseFaceZeroCarrier x ∈
      constructedCentralEdgeZeroCarrier '' Metric.closedBall 0 1 := by
  have hxnorm : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hx
  by_cases hx0 : x 0 ≤ 0
  · have hxminus := centralPhaseDisk_one_sub_ne_zero_of_nonpos x hx0
    let r : ℝ := (((1 + centralPhaseDiskComplex x) /
      (1 - centralPhaseDiskComplex x)).im) ^ 2
    have hr0 : 0 ≤ r := sq_nonneg _
    have hcoord : centralPhaseDiskLowerCoordinate x = (r : ℂ) :=
      centralPhaseDiskLowerCoordinate_eq_im_sq_of_norm_eq_one x hxnorm hxminus
    by_cases hr1 : r ≤ 1
    · let t : Fin 1 → ℝ := fun _ ↦ r - 1
      have htclosed : t ∈ Metric.closedBall 0 1 :=
        finOne_mem_closedBall_of_bounds t (by dsimp [t]; linarith) (by dsimp [t]; linarith)
      refine ⟨t, htclosed, ?_⟩
      have ht0 : t 0 ≤ 0 := by dsimp [t]; linarith
      simp [constructedCentralPhaseFaceZeroCarrier, hx0,
        constructedCentralEdgeZeroCarrier, ht0, constructedCentralEdgeZeroLowerBranch,
        hcoord, t]
    · have hrpos : 0 < r := lt_trans zero_lt_one (lt_of_not_ge hr1)
      let t : Fin 1 → ℝ := fun _ ↦ 1 - r⁻¹
      have hrinv0 : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hrpos)
      have hrinv1 : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).mpr (le_of_not_ge hr1)
      have htclosed : t ∈ Metric.closedBall 0 1 :=
        finOne_mem_closedBall_of_bounds t (by dsimp [t]; linarith) (by dsimp [t]; linarith)
      refine ⟨t, htclosed, ?_⟩
      have hrinvlt : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge hr1)
      have ht0 : ¬t 0 ≤ 0 := by dsimp [t]; linarith
      have heq := inclusion_lowerAxisZero_eq_upperAxisTwo 0 (r : ℂ)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
      simpa [constructedCentralPhaseFaceZeroCarrier, hx0,
        constructedCentralEdgeZeroCarrier, ht0, constructedCentralEdgeZeroUpperBranch,
        hcoord, t, Complex.ofReal_inv] using heq.symm
  · have hxplus := centralPhaseDisk_one_add_ne_zero_of_nonneg x
      (le_of_lt (lt_of_not_ge hx0))
    let r : ℝ := (((1 - centralPhaseDiskComplex x) /
      (1 + centralPhaseDiskComplex x)).im) ^ 2
    have hr0 : 0 ≤ r := sq_nonneg _
    have hcoord : centralPhaseDiskUpperCoordinate x = (r : ℂ) :=
      centralPhaseDiskUpperCoordinate_eq_im_sq_of_norm_eq_one x hxnorm hxplus
    by_cases hr1 : r < 1
    · let t : Fin 1 → ℝ := fun _ ↦ 1 - r
      have htclosed : t ∈ Metric.closedBall 0 1 :=
        finOne_mem_closedBall_of_bounds t (by dsimp [t]; linarith) (by dsimp [t]; linarith)
      refine ⟨t, htclosed, ?_⟩
      have ht0 : ¬t 0 ≤ 0 := by
        dsimp [t]
        exact not_le.mpr (sub_pos.mpr hr1)
      simp [constructedCentralPhaseFaceZeroCarrier, hx0,
        constructedCentralEdgeZeroCarrier, ht0, constructedCentralEdgeZeroUpperBranch,
        hcoord, t]
    · have hrone : 1 ≤ r := le_of_not_gt hr1
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
      let t : Fin 1 → ℝ := fun _ ↦ r⁻¹ - 1
      have hrinv0 : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hrpos)
      have hrinv1 : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).mpr hrone
      have htclosed : t ∈ Metric.closedBall 0 1 :=
        finOne_mem_closedBall_of_bounds t (by dsimp [t]; linarith) (by dsimp [t]; linarith)
      refine ⟨t, htclosed, ?_⟩
      have ht0 : t 0 ≤ 0 := by dsimp [t]; linarith
      have heq := inclusion_lowerAxisZero_eq_upperAxisTwo 0 ((r : ℂ)⁻¹)
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)))
      simpa [constructedCentralPhaseFaceZeroCarrier, hx0,
        constructedCentralEdgeZeroCarrier, ht0, constructedCentralEdgeZeroLowerBranch,
        hcoord, t, Complex.ofReal_inv] using heq

public theorem constructedCentralPhaseFaceZeroCarrier_componentSupport
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel (constructedCentralPhaseFaceZeroCarrier x) =
      ({e₁, e₂} : Set ToricLattice) := by
  by_cases hx0 : x 0 ≤ 0
  · have hn : centralPhaseDiskLowerCoordinate x ≠ 0 :=
      (centralPhaseDisk_coordinates_reciprocal x
        (centralPhaseDisk_one_add_ne_zero_of_ball hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hx)).1
    simp only [constructedCentralPhaseFaceZeroCarrier, hx0]
    ext v
    change inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ {e₁, e₂}
    rw [lowerAxisZero_component_iff _ hn]
    simp
  · have hn : centralPhaseDiskUpperCoordinate x ≠ 0 := by
      rw [(centralPhaseDisk_coordinates_reciprocal x
        (centralPhaseDisk_one_add_ne_zero_of_ball hx)
        (centralPhaseDisk_one_sub_ne_zero_of_ball hx)).2]
      exact inv_ne_zero
        (centralPhaseDisk_coordinates_reciprocal x
          (centralPhaseDisk_one_add_ne_zero_of_ball hx)
          (centralPhaseDisk_one_sub_ne_zero_of_ball hx)).1
    simp only [constructedCentralPhaseFaceZeroCarrier, hx0]
    ext v
    change inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate x)) ∈
      carrierCentralComponent v ↔ v ∈ {e₁, e₂}
    rw [upperAxisTwo_component_iff _ hn]
    simp

private theorem centralPhaseDiskLowerCoordinate_continuousOn_nonpos :
    ContinuousOn centralPhaseDiskLowerCoordinate {x : Fin 2 → ℝ | x 0 ≤ 0} := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hzeta : ContinuousAt centralPhaseDiskComplex x :=
    centralPhaseDiskComplex_continuous.continuousAt
  have hone : ContinuousAt (fun _ : Fin 2 → ℝ ↦ (1 : ℂ)) x := continuousAt_const
  have hquot := (hone.add hzeta).div (hone.sub hzeta)
    (centralPhaseDisk_one_sub_ne_zero_of_nonpos x hx)
  change ContinuousAt
    (fun y ↦ -(((1 : ℂ) + centralPhaseDiskComplex y) /
      (1 - centralPhaseDiskComplex y)) ^ 2) x
  exact (hquot.pow 2).neg

private theorem centralPhaseDiskUpperCoordinate_continuousOn_nonneg :
    ContinuousOn centralPhaseDiskUpperCoordinate {x : Fin 2 → ℝ | 0 ≤ x 0} := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hzeta : ContinuousAt centralPhaseDiskComplex x :=
    centralPhaseDiskComplex_continuous.continuousAt
  have hone : ContinuousAt (fun _ : Fin 2 → ℝ ↦ (1 : ℂ)) x := continuousAt_const
  have hquot := (hone.sub hzeta).div (hone.add hzeta)
    (centralPhaseDisk_one_add_ne_zero_of_nonneg x hx)
  change ContinuousAt
    (fun y ↦ -(((1 : ℂ) - centralPhaseDiskComplex y) /
      (1 + centralPhaseDiskComplex y)) ^ 2) x
  exact (hquot.pow 2).neg

private def constructedCentralPhaseFaceZeroLowerBranch (x : Fin 2 → ℝ) : Carrier :=
  inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate x))

private def constructedCentralPhaseFaceZeroUpperBranch (x : Fin 2 → ℝ) : Carrier :=
  inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate x))

private theorem constructedCentralPhaseFaceZeroLowerBranch_continuousOn_nonpos :
    ContinuousOn constructedCentralPhaseFaceZeroLowerBranch
      {x : Fin 2 → ℝ | x 0 ≤ 0} := by
  intro x hx
  have hcoord := centralPhaseDiskLowerCoordinate_continuousOn_nonpos x hx
  have hraw : ContinuousWithinAt
      (fun y ↦ lowerAxisZero (centralPhaseDiskLowerCoordinate y))
      {y : Fin 2 → ℝ | y 0 ≤ 0} x := by
    rw [continuousWithinAt_pi]
    intro i
    fin_cases i
    · simpa [lowerAxisZero] using hcoord
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
  change ContinuousWithinAt
    (fun y ↦ inclusion (false, 0) (lowerAxisZero (centralPhaseDiskLowerCoordinate y)))
      {y : Fin 2 → ℝ | y 0 ≤ 0} x
  exact (inclusion_isOpenEmbedding (false, 0)).continuous.continuousAt
    |>.comp_continuousWithinAt hraw

private theorem constructedCentralPhaseFaceZeroUpperBranch_continuousOn_nonneg :
    ContinuousOn constructedCentralPhaseFaceZeroUpperBranch
      {x : Fin 2 → ℝ | 0 ≤ x 0} := by
  intro x hx
  have hcoord := centralPhaseDiskUpperCoordinate_continuousOn_nonneg x hx
  have hraw : ContinuousWithinAt
      (fun y ↦ upperAxisTwo (centralPhaseDiskUpperCoordinate y))
      {y : Fin 2 → ℝ | 0 ≤ y 0} x := by
    rw [continuousWithinAt_pi]
    intro i
    fin_cases i
    · exact continuousWithinAt_const
    · exact continuousWithinAt_const
    · simpa [upperAxisTwo] using hcoord
  change ContinuousWithinAt
    (fun y ↦ inclusion (true, 0) (upperAxisTwo (centralPhaseDiskUpperCoordinate y)))
      {y : Fin 2 → ℝ | 0 ≤ y 0} x
  exact (inclusion_isOpenEmbedding (true, 0)).continuous.continuousAt
    |>.comp_continuousWithinAt hraw

public theorem constructedCentralPhaseFaceZeroCarrier_continuousOn_closedBall :
    ContinuousOn constructedCentralPhaseFaceZeroCarrier (Metric.closedBall 0 1) := by
  change ContinuousOn ({x : Fin 2 → ℝ | x 0 ≤ 0}.piecewise
    constructedCentralPhaseFaceZeroLowerBranch constructedCentralPhaseFaceZeroUpperBranch)
      (Metric.closedBall 0 1)
  apply ContinuousOn.piecewise
  · intro x hx
    exact constructedCentralPhaseFaceZeroCarrier_eq_on_seam x
      (frontier_le_subset_eq (continuous_apply 0) continuous_const hx.2)
  · apply constructedCentralPhaseFaceZeroLowerBranch_continuousOn_nonpos.mono
    intro x hx
    have hclosed : IsClosed {y : Fin 2 → ℝ | y 0 ≤ 0} :=
      isClosed_le (continuous_apply 0) continuous_const
    rw [hclosed.closure_eq] at hx
    exact hx.2
  · apply constructedCentralPhaseFaceZeroUpperBranch_continuousOn_nonneg.mono
    intro x hx
    apply closure_minimal _ (isClosed_le continuous_const (continuous_apply 0)) hx.2
    intro y hy
    change 0 ≤ y 0
    apply le_of_not_ge
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq] using hy

public def constructedCentralPhaseFaceZeroLocal
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    LocalCarrier constructedModel W.localWitness.radius :=
  ⟨constructedCentralPhaseFaceZeroCarrier x, by
    change carrierHeight (constructedCentralPhaseFaceZeroCarrier x) ∈
      Metric.ball 0 W.localWitness.radius
    rw [constructedCentralPhaseFaceZeroCarrier_height, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩

public theorem constructedCentralPhaseFaceZeroLocal_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceZeroLocal W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    constructedCentralPhaseFaceZeroCarrier)
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceZeroCarrier_continuousOn_closedBall

public def constructedCentralPhaseFaceZeroPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨constructedCentralPhaseFaceZeroLocal W x,
    constructedCentralPhaseFaceZeroCarrier_height x⟩

public theorem constructedCentralPhaseFaceZeroPoint_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceZeroPoint W) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  change Continuous ((Metric.closedBall (0 : Fin 2 → ℝ) 1).domRestrict
    (constructedCentralPhaseFaceZeroLocal W))
  rw [← continuousOn_iff_continuous_domRestrict]
  exact constructedCentralPhaseFaceZeroLocal_continuousOn_closedBall W

/-- The first phase two-cell as an actual point of the central deck-orbit quotient. -/
public def constructedCentralPhaseFaceZeroOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedCentralPhaseFaceZeroPoint W x)

public theorem constructedCentralPhaseFaceZeroOrbit_continuousOn_closedBall
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseFaceZeroOrbit W) (Metric.closedBall 0 1) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.continuousOn.comp
    (constructedCentralPhaseFaceZeroPoint_continuousOn_closedBall W)
      (fun _ _ ↦ Set.mem_univ _)

public theorem constructedCentralPhaseFaceZeroOrbit_mapsTo_edgeZero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralPhaseFaceZeroOrbit W) (Metric.sphere 0 1)
      (constructedCentralEdgeZeroOrbit W '' Metric.closedBall 0 1) := by
  intro x hx
  obtain ⟨t, ht, hcarrier⟩ :=
    constructedCentralPhaseFaceZeroCarrier_boundary_mem_edgeZero x hx
  refine ⟨t, ht, ?_⟩
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  change Quotient.mk _ (constructedCentralEdgeZeroPoint W t) =
    Quotient.mk _ (constructedCentralPhaseFaceZeroPoint W x)
  apply congrArg (Quotient.mk (MulAction.orbitRel
    (Multiplicative ParameterLattice) S))
  apply Subtype.ext
  apply Subtype.ext
  exact hcarrier

public def constructedCentralOneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  (⋃ i : Fin 2, constructedCentralZeroCell W i '' Metric.closedBall 0 1) ∪
    (⋃ i : Fin 3, constructedCentralOneCell W i '' Metric.closedBall 0 1)

public theorem constructedCentralPhaseFaceZeroOrbit_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralPhaseFaceZeroOrbit W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) := by
  intro x hx
  have hedge := constructedCentralPhaseFaceZeroOrbit_mapsTo_edgeZero W hx
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨0, ?_⟩
  obtain ⟨t, ht, heq⟩ := hedge
  refine ⟨t, ht, ?_⟩
  change constructedCentralEdgeZeroOrbit W t =
    constructedCentralPhaseFaceZeroOrbit W x
  exact heq

public theorem constructedCentralPhaseFaceZeroOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (constructedCentralPhaseFaceZeroOrbit W) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralPhaseFaceZeroPoint W x)
      (constructedCentralPhaseFaceZeroPoint W y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralPhaseFaceZeroPoint W x)
      (constructedCentralPhaseFaceZeroPoint W y) hxy
  have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport W
    ({e₁, e₂} : Set ToricLattice) ((Set.finite_singleton e₂).insert e₁)
      ⟨e₁, by simp⟩
      (constructedCentralPhaseFaceZeroPoint W x)
      (constructedCentralPhaseFaceZeroPoint W y)
      (constructedCentralPhaseFaceZeroCarrier_componentSupport x hx)
      (constructedCentralPhaseFaceZeroCarrier_componentSupport y hy) hrel
  exact constructedCentralPhaseFaceZeroCarrier_injOn hx hy hcoe

private theorem constructedCentralPhaseFaceZeroOrbit_ne_of_mem_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.closedBall 0 1)
    (hxb : x ∉ Metric.ball 0 1) (y : Fin 2 → ℝ)
    (hy : y ∈ Metric.ball 0 1) :
    constructedCentralPhaseFaceZeroOrbit W x ≠
      constructedCentralPhaseFaceZeroOrbit W y := by
  intro hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedCentralPhaseFaceZeroPoint W x)
      (constructedCentralPhaseFaceZeroPoint W y) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S)
      (constructedCentralPhaseFaceZeroPoint W x)
      (constructedCentralPhaseFaceZeroPoint W y) hxy
  have hySupport := constructedCentralPhaseFaceZeroCarrier_componentSupport y hy
  have hcard : ({e₁, e₂} : Set ToricLattice).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem]
    · simp
    · simp [e₁, e₂]
  by_cases hx0 : x 0 ≤ 0
  · by_cases hxcoord : centralPhaseDiskLowerCoordinate x = 0
    · have hn := centralOrbitRel_componentSupport_ncard_eq W
          (constructedCentralPhaseFaceZeroPoint W x)
          (constructedCentralPhaseFaceZeroPoint W y) hrel
      change (componentSupport constructedModel
          (constructedCentralPhaseFaceZeroCarrier x)).ncard =
        (componentSupport constructedModel
          (constructedCentralPhaseFaceZeroCarrier y)).ncard at hn
      have hxcarrier : constructedCentralPhaseFaceZeroCarrier x =
          inclusion (false, 0) 0 := by
        simp only [constructedCentralPhaseFaceZeroCarrier, hx0, ↓reduceIte, hxcoord]
        congr 1
        funext i
        fin_cases i <;> simp [lowerAxisZero]
      rw [hxcarrier, carrierOrigin_componentSupport_ncard, hySupport, hcard] at hn
      omega
    · have hxSupport :
          componentSupport constructedModel
              (constructedCentralPhaseFaceZeroCarrier x) =
            ({e₁, e₂} : Set ToricLattice) := by
        simp only [constructedCentralPhaseFaceZeroCarrier, hx0]
        ext v
        change inclusion (false, 0)
            (lowerAxisZero (centralPhaseDiskLowerCoordinate x)) ∈
              carrierCentralComponent v ↔ v ∈ {e₁, e₂}
        rw [lowerAxisZero_component_iff _ hxcoord]
        simp
      have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport W
        ({e₁, e₂} : Set ToricLattice) ((Set.finite_singleton e₂).insert e₁)
        ⟨e₁, by simp⟩
        (constructedCentralPhaseFaceZeroPoint W x)
        (constructedCentralPhaseFaceZeroPoint W y) hxSupport hySupport hrel
      exact constructedCentralPhaseFaceZeroCarrier_ne_of_mem_boundary
        x y hx hxb hy hcoe
  · by_cases hxcoord : centralPhaseDiskUpperCoordinate x = 0
    · have hn := centralOrbitRel_componentSupport_ncard_eq W
          (constructedCentralPhaseFaceZeroPoint W x)
          (constructedCentralPhaseFaceZeroPoint W y) hrel
      change (componentSupport constructedModel
          (constructedCentralPhaseFaceZeroCarrier x)).ncard =
        (componentSupport constructedModel
          (constructedCentralPhaseFaceZeroCarrier y)).ncard at hn
      have hxcarrier : constructedCentralPhaseFaceZeroCarrier x =
          inclusion (true, 0) 0 := by
        simp only [constructedCentralPhaseFaceZeroCarrier, hx0, ↓reduceIte, hxcoord]
        congr 1
        funext i
        fin_cases i <;> simp [upperAxisTwo]
      rw [hxcarrier, carrierOrigin_componentSupport_ncard, hySupport, hcard] at hn
      omega
    · have hxSupport :
          componentSupport constructedModel
              (constructedCentralPhaseFaceZeroCarrier x) =
            ({e₁, e₂} : Set ToricLattice) := by
        simp only [constructedCentralPhaseFaceZeroCarrier, hx0]
        ext v
        change inclusion (true, 0)
            (upperAxisTwo (centralPhaseDiskUpperCoordinate x)) ∈
              carrierCentralComponent v ↔ v ∈ {e₁, e₂}
        rw [upperAxisTwo_component_iff _ hxcoord]
        simp
      have hcoe := centralOrbitRel_coe_eq_of_same_componentSupport W
        ({e₁, e₂} : Set ToricLattice) ((Set.finite_singleton e₂).insert e₁)
        ⟨e₁, by simp⟩
        (constructedCentralPhaseFaceZeroPoint W x)
        (constructedCentralPhaseFaceZeroPoint W y) hxSupport hySupport hrel
      exact constructedCentralPhaseFaceZeroCarrier_ne_of_mem_boundary
        x y hx hxb hy hcoe

private theorem isEmbedding_restrict_of_compact_boundary_separation
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (s K : Set X) (hK : IsCompact K) (hsK : s ⊆ K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f s)
    (hboundary : Disjoint (f '' (K \ s)) (f '' s)) :
    Topology.IsEmbedding (s.domRestrict f) := by
  let t : Set Y := f '' s
  let g : s → t := Set.codRestrict (s.domRestrict f) t (fun x ↦ ⟨x, x.2, rfl⟩)
  have hfs : Continuous (s.domRestrict f) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono hsK)
  have hgcont : Continuous g := hfs.codRestrict _
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.2 y.2
    exact congrArg Subtype.val hxy
  have hgclosed : IsClosedMap g := by
    intro A hA
    let L : Set X := closure (Subtype.val '' A)
    have hKclosed : IsClosed K := hK.isClosed
    have hvalAK : Subtype.val '' A ⊆ K := by
      rintro x ⟨a, ha, rfl⟩
      exact hsK a.2
    have hLK : L ⊆ K := closure_minimal hvalAK hKclosed
    have hLcompact : IsCompact L :=
      hK.of_isClosed_subset isClosed_closure hLK
    have hfL : ContinuousOn f L := hf.mono hLK
    have hfLclosed : IsClosed (f '' L) :=
      (hLcompact.image_of_continuousOn hfL).isClosed
    apply isClosed_induced_iff.mpr
    refine ⟨f '' L, hfLclosed, ?_⟩
    ext z
    constructor
    · rintro ⟨x, hxL, hfx⟩
      have hxs : x ∈ s := by
        by_contra hxs
        have hxBoundary : f x ∈ f '' (K \ s) := ⟨x, ⟨hLK hxL, hxs⟩, rfl⟩
        have hzInterior : f x ∈ f '' s := by
          rw [hfx]
          exact z.2
        exact Set.disjoint_left.mp hboundary hxBoundary hzInterior
      have hxClosure : (⟨x, hxs⟩ : s) ∈ closure A :=
        closure_subtype.mpr hxL
      rw [hA.closure_eq] at hxClosure
      refine ⟨⟨x, hxs⟩, hxClosure, ?_⟩
      apply Subtype.ext
      exact hfx
    · rintro ⟨x, hxA, rfl⟩
      refine ⟨x, subset_closure ⟨x, hxA, rfl⟩, rfl⟩
  have hg : Topology.IsEmbedding g :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hgcont hginj hgclosed).isEmbedding
  have hcomp := Topology.IsEmbedding.subtypeVal.comp hg
  change Topology.IsEmbedding (fun x : s ↦ f x)
  convert hcomp using 1
  funext x
  rfl

private theorem constructedCentralPhaseFaceZeroOrbit_boundary_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Disjoint
      (constructedCentralPhaseFaceZeroOrbit W ''
        (Metric.closedBall 0 1 \ Metric.ball 0 1))
      (constructedCentralPhaseFaceZeroOrbit W '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  intro z
  rintro ⟨x, ⟨hx, hxb⟩, rfl⟩ ⟨y, hy, hxy⟩
  exact constructedCentralPhaseFaceZeroOrbit_ne_of_mem_boundary
    W x hx hxb y hy hxy.symm

public theorem constructedCentralPhaseFaceZeroOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Topology.IsEmbedding
      ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (constructedCentralPhaseFaceZeroOrbit W)) := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact isEmbedding_restrict_of_compact_boundary_separation
    (constructedCentralPhaseFaceZeroOrbit W)
    (Metric.ball 0 1) (Metric.closedBall 0 1) (isCompact_closedBall 0 1)
    Metric.ball_subset_closedBall
    (constructedCentralPhaseFaceZeroOrbit_continuousOn_closedBall W)
    (constructedCentralPhaseFaceZeroOrbit_injOn W)
    (constructedCentralPhaseFaceZeroOrbit_boundary_disjoint W)

/-- The first genuine two-dimensional phase characteristic map. -/
public def constructedCentralPhaseTwoCellZero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedCentralPhaseFaceZeroOrbit W) (Metric.ball 0 1)
    (constructedCentralPhaseFaceZeroOrbit_injOn W)

public theorem constructedCentralPhaseTwoCellZero_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralPhaseTwoCellZero W).source = Metric.ball 0 1 := rfl

public theorem constructedCentralPhaseTwoCellZero_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellZero W) (Metric.closedBall 0 1) :=
  constructedCentralPhaseFaceZeroOrbit_continuousOn_closedBall W

public theorem constructedCentralPhaseTwoCellZero_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellZero W).symm
      (constructedCentralPhaseTwoCellZero W).target := by
  let e := constructedCentralPhaseTwoCellZero W
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedCentralPhaseFaceZeroOrbit_isEmbedding W).continuous_iff.mpr
    have heq :
        (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
            (constructedCentralPhaseFaceZeroOrbit W) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

public theorem constructedCentralPhaseTwoCellZero_mapsTo_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    MapsTo (constructedCentralPhaseTwoCellZero W) (Metric.sphere 0 1)
      (constructedCentralOneSkeleton W) := by
  intro x hx
  change constructedCentralPhaseFaceZeroOrbit W x ∈
    constructedCentralOneSkeleton W
  exact constructedCentralPhaseFaceZeroOrbit_mapsTo_oneSkeleton W hx
end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
