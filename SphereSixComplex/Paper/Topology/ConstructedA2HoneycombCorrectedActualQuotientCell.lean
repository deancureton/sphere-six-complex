module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedPositiveCellAtlas
public import SphereSixComplex.Paper.Topology.StandardA2ToricCentralOrbitCellAtlasProof

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2HexagonGauge_neg (x : Fin 2 → ℝ) :
    constructedA2HexagonGauge (-x) = constructedA2HexagonGauge x := by
  simp only [constructedA2HexagonGauge, norm_neg, Pi.neg_apply]
  rw [show -x 0 - -x 1 = x 1 - x 0 by ring, abs_sub_comm]

public theorem constructedA2HexagonGauge_add_le (x y : Fin 2 → ℝ) :
    constructedA2HexagonGauge (x + y) ≤
      constructedA2HexagonGauge x + constructedA2HexagonGauge y := by
  simp only [constructedA2HexagonGauge]
  apply max_le
  · exact (norm_add_le x y).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · have h := abs_add_le (x 0 - x 1) (y 0 - y 1)
    rw [show (x + y) 0 - (x + y) 1 =
      (x 0 - x 1) + (y 0 - y 1) by simp only [Pi.add_apply]; ring]
    exact h.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

public theorem constructedA2HexagonGauge_sub_le (x y : Fin 2 → ℝ) :
    constructedA2HexagonGauge (x - y) ≤
      constructedA2HexagonGauge x + constructedA2HexagonGauge y := by
  rw [sub_eq_add_neg]
  calc
    constructedA2HexagonGauge (x + -y) ≤
        constructedA2HexagonGauge x + constructedA2HexagonGauge (-y) :=
      constructedA2HexagonGauge_add_le x (-y)
    _ = constructedA2HexagonGauge x + constructedA2HexagonGauge y := by
      rw [constructedA2HexagonGauge_neg]

public theorem constructedA2CorrectedPlaneCenter_neighborGauge
    (v w : ToricLattice)
    (h : w - v ∈ ({e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂} :
      Set ToricLattice)) :
    constructedA2HexagonGauge
        (constructedA2CorrectedPlaneCenter w - constructedA2CorrectedPlaneCenter v) =
      4 / 3 := by
  have hc : constructedA2CorrectedPlaneCenter w -
      constructedA2CorrectedPlaneCenter v =
      constructedA2CorrectedPlaneCenter (w - v) := by
    ext k
    fin_cases k <;> simp [constructedA2CorrectedPlaneCenter] <;> ring
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h
  all_goals
    rw [hc, h]
    simp only [constructedA2HexagonGauge]
    apply le_antisymm
    · apply max_le
      · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
        intro k
        fin_cases k <;>
          norm_num [constructedA2CorrectedPlaneCenter, e₁, e₂, Real.norm_eq_abs,
            div_eq_mul_inv]
      · norm_num [constructedA2CorrectedPlaneCenter, e₁, e₂, div_eq_mul_inv]
    · let c := constructedA2CorrectedPlaneCenter (w - v)
      have hvalue :
          4 / 3 = max (max ‖c 0‖ ‖c 1‖) |c 0 - c 1| := by
        dsimp [c]
        rw [h]
        norm_num [constructedA2CorrectedPlaneCenter, e₁, e₂,
          Real.norm_eq_abs, div_eq_mul_inv]
      have hbound : max (max ‖c 0‖ ‖c 1‖) |c 0 - c 1| ≤
          max ‖c‖ |c 0 - c 1| :=
        max_le_max
          (max_le (norm_le_pi_norm c 0) (norm_le_pi_norm c 1)) le_rfl
      simpa [c, h] using hvalue.trans_le hbound

public theorem constructedA2CorrectedOpenHexagon_inter_planeCell_eq
    (v w : ToricLattice)
    (h : (constructedA2CorrectedOpenHexagon v ∩
      constructedA2CorrectedPlaneCell w).Nonempty) :
    w = v := by
  obtain ⟨x, hxv, hxw⟩ := h
  have hxv' : constructedA2HexagonGauge
      (x - constructedA2CorrectedPlaneCenter v) < 2 / 3 := hxv
  have hxw' : constructedA2HexagonGauge
      (x - constructedA2CorrectedPlaneCenter w) ≤ 2 / 3 := by
    exact (show x ∈ constructedA2CorrectedClosedHexagon w by
      rwa [constructedA2CorrectedClosedHexagon_eq_planeCell])
  have hxvclosed : x ∈ constructedA2CorrectedPlaneCell v := by
    rw [← constructedA2CorrectedClosedHexagon_eq_planeCell]
    exact le_of_lt hxv'
  have hd := constructedA2CorrectedPlaneCell_inter_nonempty_displacement v w
    ⟨x, hxvclosed, hxw⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with hd | hd
  · exact sub_eq_zero.mp hd
  · have hcenter := constructedA2CorrectedPlaneCenter_neighborGauge v w hd
    have htriangle := constructedA2HexagonGauge_sub_le
      (x - constructedA2CorrectedPlaneCenter v)
      (x - constructedA2CorrectedPlaneCenter w)
    rw [show (x - constructedA2CorrectedPlaneCenter v) -
        (x - constructedA2CorrectedPlaneCenter w) =
      constructedA2CorrectedPlaneCenter w - constructedA2CorrectedPlaneCenter v by abel,
      hcenter] at htriangle
    linarith

public theorem constructedA2CorrectedPositiveHexagonMap_componentSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel
        (((constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x).1.1.1 :
          Carrier)) = {v} := by
  let q := constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x
  let z := constructedA2CorrectedHexagonHomeomorph v x
  have hzopen : z ∈ constructedA2CorrectedOpenHexagon v :=
    (constructedA2CorrectedHexagonHomeomorph_mem_open_iff v x).mpr hx
  have hzclosed : z ∈ constructedA2CorrectedPlaneCell v :=
    (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr
      (Metric.ball_subset_closedBall hx)
  have hqeq : q =
      (constructedA2CorrectedFiniteQuotientCellHomeomorph
        W.localWitness.radius_pos v ⟨z, hzclosed⟩ :
          constructedPositiveCentralCell W.localWitness.radius v) := by
    dsimp only [q, z]
    exact constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos v x (Metric.ball_subset_closedBall hx)
  ext w
  constructor
  · intro hw
    have hqcell : q ∈ constructedPositiveCentralCell W.localWitness.radius w := hw
    let qw : constructedPositiveCentralCell W.localWitness.radius w := ⟨q, hqcell⟩
    let y := (constructedA2CorrectedFiniteQuotientCellHomeomorph
      W.localWitness.radius_pos w).symm qw
    have heq : (z : Fin 2 → ℝ) = (y : Fin 2 → ℝ) := by
      apply (constructedA2CorrectedFiniteQuotientCellHomeomorph_compatible
        W.localWitness.radius_pos v w
        ⟨z, hzclosed⟩ y).mpr
      rw [(constructedA2CorrectedFiniteQuotientCellHomeomorph
        W.localWitness.radius_pos w).apply_symm_apply]
      exact hqeq.symm
    exact constructedA2CorrectedOpenHexagon_inter_planeCell_eq v w
      ⟨z, hzopen, heq ▸ y.2⟩
  · intro hwv
    rw [hwv]
    change q ∈ constructedPositiveCentralCell W.localWitness.radius v
    rw [hqeq]
    exact (constructedA2CorrectedFiniteQuotientCellHomeomorph
      W.localWitness.radius_pos v ⟨z, hzclosed⟩).2

public def constructedA2PositiveCentralPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨q.1.1, q.2⟩



public theorem constructedA2ActualCentral_parameter_eq_zero_of_singletonSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (g : Multiplicative ParameterLattice)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel
      ((p : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hq : componentSupport constructedModel
      ((q : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hg : g • q = p) :
    Multiplicative.toAdd g = 0 := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hcarrier := congrArg
    (fun z : S ↦ ((z : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  have hphase := hcarrier
  change ((C.toCuspActionData.psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hphase
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hphase
  have hvq : v ∈ componentSupport constructedModel
      ((q : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) := by
    rw [hq]
    simp
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
  have htranslate : v + shearVector lambda = v := by
    have : v + shearVector lambda ∈ ({v} : Set ToricLattice) := by
      rw [← hp]
      exact hphaseComponent
    simpa using this
  have hshear : shearVector lambda = 0 := by
    simpa using add_left_cancel (show v + shearVector lambda = v + 0 by simpa using htranslate)
  apply shearVector_injective
  simpa [lambda, shearVector] using hshear

public theorem constructedA2ActualCentralOrbitRel_coe_eq_of_singletonSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (p q : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel
      ((p : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hq : componentSupport constructedModel
      ((q : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    ((p : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier) =
      ((q : localCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hlambda := constructedA2ActualCentral_parameter_eq_zero_of_singletonSupport
    W v g p q hp hq hg
  have hcarrier := congrArg
    (fun z : S ↦ ((z : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  change ((C.toCuspActionData.psiMap
    (Multiplicative.toAdd g) (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, hlambda, C.psiMap_zero] at hcarrier
  exact hcarrier.symm

public theorem constructedA2ComponentSupport_phase_fanShear
    (lambda : ParameterLattice) (c : CuspToricPhaseAction.Phase)
    (p : constructedModel.Carrier) :
    componentSupport constructedModel
      (CuspToricPhaseAction.ToricModel.phaseAction constructedModel c
        (Additive.toMul (constructedModel.fanShear lambda) p)) =
      (fun v ↦ v + shearVector lambda) '' componentSupport constructedModel p := by
  ext w
  change constructedModel.torusAction (CuspToricPhaseAction.phaseEmbedding c)
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
    have hqp : q = p :=
      (Additive.toMul (constructedModel.fanShear lambda)).injective heq
    rwa [hqp] at hq
  · rintro ⟨v, hv, rfl⟩
    rw [← constructedModel.fanShear_component lambda v]
    exact ⟨p, hv, rfl⟩

public theorem constructedA2ActualCentralOrbitRel_componentSupport_ncard_eq
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
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  let lambda := Multiplicative.toAdd g
  change ((C.toCuspActionData.psiMap lambda
    (q : localCarrier constructedModel W.localWitness.radius) :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : localCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) at hcarrier
  rw [← C.psiMap_eq_generic, C.psiMap_coe] at hcarrier
  have hsupport := constructedA2ComponentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : localCarrier constructedModel W.localWitness.radius)))
    ((q : localCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)
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





















end SphereSixComplex.Geometry.InfiniteA2Toric

end
