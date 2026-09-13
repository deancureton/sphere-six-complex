module

public import SphereSixComplex.Paper.Topology.StandardA2ToricCentralFiberZeroCells
public import SphereSixComplex.Paper.Geometry.PaperStarPieceHausdorff

/-!
# Coordinate axes in the standard `A₂` central-fibre quotient

Adjacent affine axes are identified by reciprocal coordinates. Support and deck-action
calculations describe their images in the central-fibre quotient.
-/

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspCollar

open SphereSixComplex
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
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

private theorem centralOrbitRel_coe_eq_of_same_componentSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (T : Set ToricLattice) (hTfinite : T.Finite) (hTnonempty : T.Nonempty)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel
      ((p : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = T)
    (hq : componentSupport constructedModel
      ((q : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = T)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    ((p : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      ((q : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  have hphase := hcarrier
  change (((C.toCuspActionData (M := constructedModel)).psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hphase
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hphase
  have hforward : ∀ v ∈ T, v + shearVector lambda ∈ T := by
    intro v hv
    have hvq : v ∈ componentSupport constructedModel
        ((q : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) := by
      rw [hq]
      exact hv
    have hfan : Additive.toMul (constructedModel.fanShear lambda)
        ((q : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) ∈
          constructedModel.centralComponent (v + shearVector lambda) := by
      rw [← constructedModel.fanShear_component lambda v]
      exact ⟨_, hvq, rfl⟩
    have hphaseComponent :
        CuspToricPhaseAction.ToricModel.phaseAction constructedModel
          (C.phase lambda (constructedModel.t
            (q : localCarrier constructedModel W.localWitness.radius)))
          (Additive.toMul (constructedModel.fanShear lambda)
            (q : localCarrier constructedModel W.localWitness.radius)) ∈
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
  change (((C.toCuspActionData (M := constructedModel)).psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, hlambda, C.psiMap_zero] at hcarrier
  exact hcarrier.symm

private theorem centralOrbitRel_componentSupport_ncard_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    (componentSupport constructedModel
      ((p : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier)).ncard =
    (componentSupport constructedModel
      ((q : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier)).ncard := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  change (((C.toCuspActionData (M := constructedModel)).psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hcarrier
  have hsupport := componentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : localCarrier constructedModel W.localWitness.radius)))
    ((q : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier)
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
          ((p : localCarrier constructedModel W.localWitness.radius) :
            constructedModel.Carrier) =
        (fun v ↦ v + shearVector lambda) ''
          componentSupport constructedModel
            ((q : localCarrier constructedModel W.localWitness.radius) :
              constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hcarrier := congrArg
    (fun z : S ↦ ((z : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  change (((C.toCuspActionData (M := constructedModel)).psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hcarrier
  refine ⟨lambda, ?_⟩
  have hsupport := componentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : localCarrier constructedModel W.localWitness.radius)))
    ((q : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier)
  rwa [hcarrier] at hsupport

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

end SphereSixComplex.Geometry.CuspCollar

end
