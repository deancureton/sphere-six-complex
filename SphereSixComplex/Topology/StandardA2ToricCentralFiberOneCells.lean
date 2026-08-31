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
end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
