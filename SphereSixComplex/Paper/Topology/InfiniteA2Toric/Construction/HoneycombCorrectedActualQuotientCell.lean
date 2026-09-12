module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombCorrectedPositiveCellAtlas
public import SphereSixComplex.Paper.Topology.StandardA2ToricCentralOrbitCellAtlasProof

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

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

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem hexagonGauge_neg (x : Fin 2 → ℝ) :
    hexagonGauge (-x) = hexagonGauge x := by
  simp only [hexagonGauge, norm_neg, Pi.neg_apply]
  rw [show -x 0 - -x 1 = x 1 - x 0 by ring, abs_sub_comm]

public theorem hexagonGauge_add_le (x y : Fin 2 → ℝ) :
    hexagonGauge (x + y) ≤
      hexagonGauge x + hexagonGauge y := by
  simp only [hexagonGauge]
  apply max_le
  · exact (norm_add_le x y).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · have h := abs_add_le (x 0 - x 1) (y 0 - y 1)
    rw [show (x + y) 0 - (x + y) 1 =
      (x 0 - x 1) + (y 0 - y 1) by simp only [Pi.add_apply]; ring]
    exact h.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

public theorem hexagonGauge_sub_le (x y : Fin 2 → ℝ) :
    hexagonGauge (x - y) ≤
      hexagonGauge x + hexagonGauge y := by
  rw [sub_eq_add_neg]
  calc
    hexagonGauge (x + -y) ≤
        hexagonGauge x + hexagonGauge (-y) :=
      hexagonGauge_add_le x (-y)
    _ = hexagonGauge x + hexagonGauge y := by
      rw [hexagonGauge_neg]

public theorem correctedPlaneCenter_neighborGauge
    (v w : ToricLattice)
    (h : w - v ∈ ({e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂} :
      Set ToricLattice)) :
    hexagonGauge
        (correctedPlaneCenter w - correctedPlaneCenter v) =
      4 / 3 := by
  have hc : correctedPlaneCenter w -
      correctedPlaneCenter v =
      correctedPlaneCenter (w - v) := by
    ext k
    fin_cases k <;> simp [correctedPlaneCenter] <;> ring
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h
  all_goals
    rw [hc, h]
    simp only [hexagonGauge]
    apply le_antisymm
    · apply max_le
      · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
        intro k
        fin_cases k <;>
          norm_num [correctedPlaneCenter, e₁, e₂, Real.norm_eq_abs,
            div_eq_mul_inv]
      · norm_num [correctedPlaneCenter, e₁, e₂, div_eq_mul_inv]
    · let c := correctedPlaneCenter (w - v)
      have hvalue :
          4 / 3 = max (max ‖c 0‖ ‖c 1‖) |c 0 - c 1| := by
        dsimp [c]
        rw [h]
        norm_num [correctedPlaneCenter, e₁, e₂,
          Real.norm_eq_abs, div_eq_mul_inv]
      have hbound : max (max ‖c 0‖ ‖c 1‖) |c 0 - c 1| ≤
          max ‖c‖ |c 0 - c 1| :=
        max_le_max
          (max_le (norm_le_pi_norm c 0) (norm_le_pi_norm c 1)) le_rfl
      simpa [c, h] using hvalue.trans_le hbound

public theorem correctedOpenHexagon_inter_planeCell_eq
    (v w : ToricLattice)
    (h : (correctedOpenHexagon v ∩
      correctedPlaneCell w).Nonempty) :
    w = v := by
  obtain ⟨x, hxv, hxw⟩ := h
  have hxv' : hexagonGauge
      (x - correctedPlaneCenter v) < 2 / 3 := hxv
  have hxw' : hexagonGauge
      (x - correctedPlaneCenter w) ≤ 2 / 3 := by
    exact (show x ∈ correctedClosedHexagon w by
      rwa [correctedClosedHexagon_eq_planeCell])
  have hxvclosed : x ∈ correctedPlaneCell v := by
    rw [← correctedClosedHexagon_eq_planeCell]
    exact le_of_lt hxv'
  have hd := correctedPlaneCell_inter_nonempty_displacement v w
    ⟨x, hxvclosed, hxw⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with hd | hd
  · exact sub_eq_zero.mp hd
  · have hcenter := correctedPlaneCenter_neighborGauge v w hd
    have htriangle := hexagonGauge_sub_le
      (x - correctedPlaneCenter v)
      (x - correctedPlaneCenter w)
    rw [show (x - correctedPlaneCenter v) -
        (x - correctedPlaneCenter w) =
      correctedPlaneCenter w - correctedPlaneCenter v by abel,
      hcenter] at htriangle
    linarith

public theorem correctedPositiveHexagonMap_componentSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel
        (((correctedPositiveHexagonMap W.localWitness.radius_pos v x).1.1.1 :
          Carrier)) = {v} := by
  let q := correctedPositiveHexagonMap W.localWitness.radius_pos v x
  let z := correctedHexagonHomeomorph v x
  have hzopen : z ∈ correctedOpenHexagon v :=
    (correctedHexagonHomeomorph_mem_open_iff v x).mpr hx
  have hzclosed : z ∈ correctedPlaneCell v :=
    (correctedHexagonHomeomorph_mem_closed_iff v x).mpr
      (Metric.ball_subset_closedBall hx)
  have hqeq : q =
      (correctedFiniteQuotientCellHomeomorph
        W.localWitness.radius_pos v ⟨z, hzclosed⟩ :
          constructedPositiveCentralCell W.localWitness.radius v) := by
    dsimp only [q, z]
    exact correctedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos v x (Metric.ball_subset_closedBall hx)
  ext w
  constructor
  · intro hw
    have hqcell : q ∈ constructedPositiveCentralCell W.localWitness.radius w := hw
    let qw : constructedPositiveCentralCell W.localWitness.radius w := ⟨q, hqcell⟩
    let y := (correctedFiniteQuotientCellHomeomorph
      W.localWitness.radius_pos w).symm qw
    have heq : (z : Fin 2 → ℝ) = (y : Fin 2 → ℝ) := by
      apply (correctedFiniteQuotientCellHomeomorph_compatible
        W.localWitness.radius_pos v w
        ⟨z, hzclosed⟩ y).mpr
      rw [(correctedFiniteQuotientCellHomeomorph
        W.localWitness.radius_pos w).apply_symm_apply]
      exact hqeq.symm
    exact correctedOpenHexagon_inter_planeCell_eq v w
      ⟨z, hzopen, heq ▸ y.2⟩
  · intro hwv
    rw [hwv]
    change q ∈ constructedPositiveCentralCell W.localWitness.radius v
    rw [hqeq]
    exact (correctedFiniteQuotientCellHomeomorph
      W.localWitness.radius_pos v ⟨z, hzclosed⟩).2

public def positiveCentralPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨q.1.1, q.2⟩



public theorem actualCentral_parameter_eq_zero_of_singletonSupport
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

public theorem actualCentralOrbitRel_coe_eq_of_singletonSupport
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
  have hlambda := actualCentral_parameter_eq_zero_of_singletonSupport
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

public theorem componentSupport_phase_fanShear
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

public theorem actualCentralOrbitRel_componentSupport_ncard_eq
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
  have hsupport := componentSupport_phase_fanShear lambda
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





















end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
