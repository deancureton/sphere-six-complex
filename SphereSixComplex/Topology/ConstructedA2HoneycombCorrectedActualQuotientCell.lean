module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedPositiveCellAtlas
public import SphereSixComplex.Topology.StandardA2ToricCentralOrbitCellAtlasProof

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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

public def constructedA2PositiveCentralOrbitMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.mk _ (constructedA2PositiveCentralPoint W q)

public theorem constructedA2PositiveCentralOrbitMap_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedA2PositiveCentralOrbitMap W) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact continuous_quotient_mk'.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

public theorem constructedA2ActualCentral_parameter_eq_zero_of_singletonSupport
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (g : Multiplicative ParameterLattice)
    (p q : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel
      ((p : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hq : componentSupport constructedModel
      ((q : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hg : g • q = p) :
    Multiplicative.toAdd g = 0 := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
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
  have hvq : v ∈ componentSupport constructedModel
      ((q : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) := by
    rw [hq]
    simp
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
      ((p : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hq : componentSupport constructedModel
      ((q : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) = {v})
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p q) :
    ((p : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier) =
      ((q : LocalCarrier constructedModel W.localWitness.radius) :
        constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hlambda := constructedA2ActualCentral_parameter_eq_zero_of_singletonSupport
    W v g p q hp hq hg
  have hcarrier := congrArg
    (fun z : S ↦ ((z : LocalCarrier constructedModel W.localWitness.radius) :
      constructedModel.Carrier)) hg
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  change (((C.toCuspActionData W.localWitness.fixedPoint).psiMap
    (Multiplicative.toAdd g) (q : LocalCarrier constructedModel W.localWitness.radius) :
      LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        ((p : LocalCarrier constructedModel W.localWitness.radius) :
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
  have hsupport := constructedA2ComponentSupport_phase_fanShear lambda
    (C.phase lambda (constructedModel.t
      (q : LocalCarrier constructedModel W.localWitness.radius)))
    ((q : LocalCarrier constructedModel W.localWitness.radius) :
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

public def constructedA2CorrectedActualHexagonMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (x : Fin 2 → ℝ) :
    ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2PositiveCentralOrbitMap W
    (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x)

public theorem constructedA2CorrectedActualHexagonMap_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedActualHexagonMap W v)
      (Metric.closedBall 0 1) :=
  (constructedA2PositiveCentralOrbitMap_continuous W).continuousOn.comp
    (constructedA2CorrectedPositiveHexagonMap_continuousOn
      W.localWitness.radius_pos v) (fun _ _ ↦ Set.mem_univ _)

public theorem constructedA2CorrectedActualHexagonMap_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    Set.InjOn (constructedA2CorrectedActualHexagonMap W v)
      (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x))
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v y)) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S) _ _ hxy
  have hcarrier := constructedA2ActualCentralOrbitRel_coe_eq_of_singletonSupport
    W v _ _
    (constructedA2CorrectedPositiveHexagonMap_componentSupport W v x hx)
    (constructedA2CorrectedPositiveHexagonMap_componentSupport W v y hy) hrel
  apply constructedA2CorrectedPositiveHexagonMap_injOn_closedBall
    W.localWitness.radius_pos v
    (Metric.ball_subset_closedBall hx) (Metric.ball_subset_closedBall hy)
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hcarrier

private theorem constructedA2CorrectedActualHexagonMap_boundary_ne_interior
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) (x y : Fin 2 → ℝ)
    (hx : x ∈ Metric.closedBall 0 1) (hy : y ∈ Metric.ball 0 1)
    (hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x))
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v y))) :
    x = y := by
  let px := constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x
  let py := constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v y
  have hyncard : (componentSupport constructedModel
      ((constructedA2PositiveCentralPoint W py :
        LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier)).ncard = 1 := by
    change (componentSupport constructedModel
      ((py.1.1.1 : Carrier) : constructedModel.Carrier)).ncard = 1
    dsimp only [py]
    rw [constructedA2CorrectedPositiveHexagonMap_componentSupport W v y hy]
    simp
  have hxcard : (componentSupport constructedModel
      ((constructedA2PositiveCentralPoint W px :
        LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier)).ncard = 1 := by
    rw [constructedA2ActualCentralOrbitRel_componentSupport_ncard_eq W _ _ hrel]
    exact hyncard
  obtain ⟨w, hxSupport⟩ := Set.ncard_eq_one.mp hxcard
  have hvx : v ∈ componentSupport constructedModel
      ((constructedA2PositiveCentralPoint W px :
        LocalCarrier constructedModel W.localWitness.radius) :
          constructedModel.Carrier) := by
    change px ∈ constructedPositiveCentralCell W.localWitness.radius v
    dsimp only [px]
    rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos v x hx]
    exact (constructedA2CorrectedFiniteQuotientCellHomeomorph
      W.localWitness.radius_pos v
        ⟨constructedA2CorrectedHexagonHomeomorph v x,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩).2
  have hwv : w = v := by
    rw [hxSupport] at hvx
    simpa using hvx.symm
  subst w
  have hcarrier := constructedA2ActualCentralOrbitRel_coe_eq_of_singletonSupport
    W v _ _ hxSupport
      (constructedA2CorrectedPositiveHexagonMap_componentSupport W v y hy) hrel
  apply constructedA2CorrectedPositiveHexagonMap_injOn_closedBall
    W.localWitness.radius_pos v hx (Metric.ball_subset_closedBall hy)
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hcarrier

private theorem constructedA2CorrectedActualHexagonMap_boundary_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    Disjoint
      (constructedA2CorrectedActualHexagonMap W v ''
        (Metric.closedBall 0 1 \ Metric.ball 0 1))
      (constructedA2CorrectedActualHexagonMap W v '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  intro z
  rintro ⟨x, ⟨hx, hxb⟩, rfl⟩ ⟨y, hy, hxy⟩
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  have hrel : MulAction.orbitRel (Multiplicative ParameterLattice) S
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v x))
      (constructedA2PositiveCentralPoint W
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos v y)) :=
    @Quotient.exact S (MulAction.orbitRel (Multiplicative ParameterLattice) S) _ _ hxy.symm
  exact hxb (constructedA2CorrectedActualHexagonMap_boundary_ne_interior
    W v x y hx hy hrel ▸ hy)

private theorem constructedA2IsEmbedding_restrict_of_compact_boundary_separation
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
    have hLcompact : IsCompact L := hK.of_isClosed_subset isClosed_closure hLK
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
      have hxClosure : (⟨x, hxs⟩ : s) ∈ closure A := closure_subtype.mpr hxL
      rw [hA.closure_eq] at hxClosure
      refine ⟨⟨x, hxs⟩, hxClosure, ?_⟩
      apply Subtype.ext
      exact hfx
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨x, subset_closure ⟨x, hxA, rfl⟩, rfl⟩
  have hg : Topology.IsEmbedding g :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hgcont hginj hgclosed).isEmbedding
  have hcomp := Topology.IsEmbedding.subtypeVal.comp hg
  change Topology.IsEmbedding (fun x : s ↦ f x)
  convert hcomp using 1
  funext x
  rfl

public theorem constructedA2CorrectedActualHexagonMap_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    Topology.IsEmbedding
      ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (constructedA2CorrectedActualHexagonMap W v)) := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact constructedA2IsEmbedding_restrict_of_compact_boundary_separation
    (constructedA2CorrectedActualHexagonMap W v)
    (Metric.ball 0 1) (Metric.closedBall 0 1) (isCompact_closedBall 0 1)
    Metric.ball_subset_closedBall
    (constructedA2CorrectedActualHexagonMap_continuousOn W v)
    (constructedA2CorrectedActualHexagonMap_injOn W v)
    (constructedA2CorrectedActualHexagonMap_boundary_disjoint W v)

public def constructedA2CorrectedActualHexagonalCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (constructedA2CorrectedActualHexagonMap W v)
    (Metric.ball 0 1) (constructedA2CorrectedActualHexagonMap_injOn W v)

public theorem constructedA2CorrectedActualHexagonalCell_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    (constructedA2CorrectedActualHexagonalCell W v).source = Metric.ball 0 1 := rfl

public theorem constructedA2CorrectedActualHexagonalCell_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedActualHexagonalCell W v)
      (Metric.closedBall 0 1) :=
  constructedA2CorrectedActualHexagonMap_continuousOn W v

public theorem constructedA2CorrectedActualHexagonalCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedActualHexagonalCell W v).symm
      (constructedA2CorrectedActualHexagonalCell W v).target := by
  let e := constructedA2CorrectedActualHexagonalCell W v
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedA2CorrectedActualHexagonMap_isEmbedding W v).continuous_iff.mpr
    have heq :
        (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
            (constructedA2CorrectedActualHexagonMap W v) ∘ lift =
          (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

public def constructedA2CorrectedActualHexagonalClosedCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) : Set (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedA2CorrectedActualHexagonalCell W v '' Metric.closedBall 0 1

public theorem constructedA2CorrectedActualHexagonalCell_mapsTo_closedCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    MapsTo (constructedA2CorrectedActualHexagonalCell W v) (Metric.sphere 0 1)
      (constructedA2CorrectedActualHexagonalClosedCell W v) := by
  intro x hx
  exact ⟨x, Metric.sphere_subset_closedBall hx, rfl⟩

public theorem constructedA2CorrectedActualHexagonalCell_sphere_disjoint_target
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    Disjoint
      (constructedA2CorrectedActualHexagonalCell W v '' Metric.sphere 0 1)
      (constructedA2CorrectedActualHexagonalCell W v).target := by
  rw [Set.disjoint_left]
  intro q
  rintro ⟨x, hx, rfl⟩ htarget
  change constructedA2CorrectedActualHexagonMap W v x ∈
    (constructedA2CorrectedActualHexagonalCell W v).target at htarget
  rcases htarget with ⟨y, hy, hxy⟩
  have hdisjoint := Set.disjoint_left.mp
    (constructedA2CorrectedActualHexagonMap_boundary_disjoint W v)
  exact hdisjoint
    ⟨x, ⟨Metric.sphere_subset_closedBall hx,
      fun hxb ↦ by linarith [Metric.mem_sphere.mp hx, Metric.mem_ball.mp hxb]⟩, rfl⟩
    ⟨y, hy, hxy⟩

public theorem constructedA2CorrectedActualHexagonalCell_sphere_image
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (v : ToricLattice) :
    constructedA2CorrectedActualHexagonalCell W v '' Metric.sphere 0 1 =
      constructedA2CorrectedActualHexagonalClosedCell W v \
        (constructedA2CorrectedActualHexagonalCell W v).target := by
  let e := constructedA2CorrectedActualHexagonalCell W v
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hq : constructedA2CorrectedActualHexagonalCell W v x ∈
        constructedA2CorrectedActualHexagonalCell W v '' Metric.sphere 0 1 :=
      ⟨x, hx, rfl⟩
    exact ⟨constructedA2CorrectedActualHexagonalCell_mapsTo_closedCell W v hx,
      fun htarget ↦ Set.disjoint_left.mp
        (constructedA2CorrectedActualHexagonalCell_sphere_disjoint_target W v)
        hq htarget⟩
  · rintro ⟨⟨x, hxclosed, hxq⟩, hqtarget⟩
    have hxnot : x ∉ Metric.ball 0 1 := by
      intro hx
      apply hqtarget
      change q ∈ constructedA2CorrectedActualHexagonMap W v '' Metric.ball 0 1
      exact ⟨x, hx, hxq⟩
    have hxsphere : x ∈ Metric.sphere 0 1 := by
      rw [← Metric.closedBall_sdiff_ball]
      exact ⟨hxclosed, hxnot⟩
    exact ⟨x, hxsphere, hxq⟩

public def constructedCentralPhaseTwoCellThree
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  constructedA2CorrectedActualHexagonalCell W 0

public theorem constructedCentralPhaseTwoCellThree_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (constructedCentralPhaseTwoCellThree W).source = Metric.ball 0 1 :=
  constructedA2CorrectedActualHexagonalCell_source_eq W 0

public theorem constructedCentralPhaseTwoCellThree_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellThree W) (Metric.closedBall 0 1) :=
  constructedA2CorrectedActualHexagonalCell_continuousOn W 0

public theorem constructedCentralPhaseTwoCellThree_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousOn (constructedCentralPhaseTwoCellThree W).symm
      (constructedCentralPhaseTwoCellThree W).target :=
  constructedA2CorrectedActualHexagonalCell_continuousOn_symm W 0

public theorem constructedCentralPhaseTwoCellThree_sphere_disjoint_target
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Disjoint (constructedCentralPhaseTwoCellThree W '' Metric.sphere 0 1)
      (constructedCentralPhaseTwoCellThree W).target :=
  constructedA2CorrectedActualHexagonalCell_sphere_disjoint_target W 0

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
