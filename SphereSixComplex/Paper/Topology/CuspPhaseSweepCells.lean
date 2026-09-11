module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCharacteristic

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric.Construction
open InfiniteA2Toric CuspLocalPhaseAction CuspFilling CuspPeriodExpansion
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepRotation (i : Fin 3) : Carrier ≃ₜ Carrier :=
  ![Homeomorph.refl _, a2CyclicCarrierHomeomorph,
    a2CyclicCarrierHomeomorph.trans a2CyclicCarrierHomeomorph] i

public theorem phaseSweepRotation_phase (i : Fin 3) (x : Fin 2 → ℝ) :
    phaseSweepRotation i (constructedCentralPhaseFaceZeroCarrier x) =
      constructedCentralPhaseFaceCarrier i x := by
  fin_cases i
  · rfl
  · exact a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier x
  · exact a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier x

public theorem phaseSweepRotation_edge (i : Fin 3) (x : Fin 1 → ℝ) :
    phaseSweepRotation i (constructedCentralEdgeZeroCarrier x) =
      constructedCentralEdgeCarrier i x := by
  fin_cases i
  · rfl
  · exact a2CyclicCarrier_constructedCentralEdgeZeroCarrier x
  · exact a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier x

public def phaseSweepCarrier (i : Fin 3) (x : Fin 2 → ℝ) : Carrier :=
  phaseSweepRotation i (phaseSweepZeroCarrier x)

public theorem phaseSweepCarrier_height (i : Fin 3) (x : Fin 2 → ℝ) :
    carrierHeight (phaseSweepCarrier i x) = 0 := by
  have hz : carrierHeight (phaseSweepZeroCarrier x) = 0 := by
    unfold phaseSweepZeroCarrier fourthPhaseEdgeZeroSweep
    rw [show carrierHeight (constructedModel.torusAction _ _) =
      _ * carrierHeight (constructedCentralEdgeZeroCarrier (fun _ ↦ x 0)) from
        constructedModel.t_torusAction _ _]
    rw [constructedCentralEdgeZeroCarrier_height, mul_zero]
  fin_cases i
  · exact hz
  · exact (carrierHeight_a2CyclicCarrier _).trans hz
  · exact (carrierHeight_a2CyclicCarrier _).trans ((carrierHeight_a2CyclicCarrier _).trans hz)

public def phaseSweepPoint (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (x : Fin 2 → ℝ) : actualLocalCuspCentralSubMulAction W :=
  ⟨⟨phaseSweepCarrier i x, by
      change carrierHeight (phaseSweepCarrier i x) ∈ Metric.ball 0 W.localWitness.radius
      rw [phaseSweepCarrier_height, Metric.mem_ball, dist_self]
      exact W.localWitness.radius_pos⟩, phaseSweepCarrier_height i x⟩

public theorem phaseSweepPoint_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Continuous (phaseSweepPoint W i) := by
  have hz : Continuous phaseSweepZeroCarrier := by
    have h := continuous_subtype_val.comp
      (continuous_subtype_val.comp (phaseSweepZeroPoint_continuous W))
    have he : (fun x ↦ (phaseSweepZeroPoint W x).1.1) = phaseSweepZeroCarrier :=
      funext (phaseSweepZeroPoint_carrier W)
    change Continuous (fun x ↦ (phaseSweepZeroPoint W x).1.1) at h
    rwa [he] at h
  exact ((phaseSweepRotation i).continuous.comp hz).subtype_mk _ |>.subtype_mk _

public def phaseSweepOrbit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (x : Fin 2 → ℝ) : ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  exact Quotient.mk _ (phaseSweepPoint W i x)

public theorem phaseSweepOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Continuous (phaseSweepOrbit W i) := by
  let _ := actualLocalCuspQuotientAction W
  exact continuous_quotient_mk'.comp (phaseSweepPoint_continuous W i)

public theorem phaseSweepCarrier_image (i : Fin 3) :
    phaseSweepCarrier i '' Metric.ball 0 1 =
      constructedCentralPhaseFaceCarrier i '' Metric.ball 0 1 := by
  change (phaseSweepRotation i ∘ phaseSweepZeroCarrier) '' _ = _
  rw [Set.image_comp, phaseSweepZeroCarrier_image, ← Set.image_comp]
  congr 1
  funext x
  exact phaseSweepRotation_phase i x

public theorem phaseSweepOrbit_eq_phase
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x y : Fin 2 → ℝ)
    (h : phaseSweepCarrier i x = constructedCentralPhaseFaceCarrier i y) :
    phaseSweepOrbit W i x = constructedCentralPhaseTwoCell W i y := by
  let _ := actualLocalCuspQuotientAction W
  have hp : phaseSweepPoint W i x = constructedCentralPhaseCellPoint W i y := by
    apply Subtype.ext
    apply Subtype.ext
    fin_cases i <;> exact h
  change Quotient.mk _ (phaseSweepPoint W i x) = _
  rw [hp]
  fin_cases i <;> rfl

public theorem phaseSweepOrbit_image
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    phaseSweepOrbit W i '' Metric.ball 0 1 =
      constructedCentralPhaseTwoCell W i '' Metric.ball 0 1 := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hm : phaseSweepCarrier i x ∈
        constructedCentralPhaseFaceCarrier i '' Metric.ball 0 1 := by
      rw [← phaseSweepCarrier_image]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hm
    exact ⟨y, hy, (phaseSweepOrbit_eq_phase W i x y he.symm).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hm : constructedCentralPhaseFaceCarrier i y ∈
        phaseSweepCarrier i '' Metric.ball 0 1 := by
      rw [phaseSweepCarrier_image]
      exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, he⟩ := hm
    exact ⟨x, hx, phaseSweepOrbit_eq_phase W i x y he⟩

public theorem phaseSweepOrbit_injOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Set.InjOn (phaseSweepOrbit W i) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  have hm (z : Fin 2 → ℝ) (hz : z ∈ Metric.ball 0 1) :
      ∃ w ∈ Metric.ball 0 1,
        phaseSweepCarrier i z = constructedCentralPhaseFaceCarrier i w := by
    have hh : phaseSweepCarrier i z ∈
        constructedCentralPhaseFaceCarrier i '' Metric.ball 0 1 := by
      rw [← phaseSweepCarrier_image]
      exact ⟨z, hz, rfl⟩
    obtain ⟨w, hw, he⟩ := hh
    exact ⟨w, hw, he.symm⟩
  obtain ⟨a, ha, hea⟩ := hm x hx
  obtain ⟨b, hb, heb⟩ := hm y hy
  have hab : a = b := (constructedCentralPhaseTwoCell W i).injOn
    (by rwa [constructedCentralPhaseTwoCell_source_eq])
    (by rwa [constructedCentralPhaseTwoCell_source_eq])
    ((phaseSweepOrbit_eq_phase W i x a hea).symm.trans
      (hxy.trans (phaseSweepOrbit_eq_phase W i y b heb)))
  apply phaseSweepZeroCarrier_injOn hx hy
  apply (phaseSweepRotation i).injective
  change phaseSweepCarrier i x = phaseSweepCarrier i y
  rw [hea, heb, hab]

public theorem phaseSweepOrbit_closedImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    phaseSweepOrbit W i '' Metric.closedBall 0 1 =
      constructedCentralPhaseTwoCell W i '' Metric.closedBall 0 1 := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  have hcl : closure (Metric.ball (0 : Fin 2 → ℝ) 1) = Metric.closedBall 0 1 :=
    closure_ball 0 one_ne_zero
  have hc : IsCompact (closure (Metric.ball (0 : Fin 2 → ℝ) 1)) := by
    rw [hcl]
    exact isCompact_closedBall 0 1
  have hnew := image_closure_of_isCompact hc (phaseSweepOrbit_continuous W i).continuousOn
  have hold := image_closure_of_isCompact hc
    (hcl ▸ constructedCentralPhaseTwoCell_continuousOn W i)
  rw [hcl] at hnew hold
  rw [hnew, hold, phaseSweepOrbit_image]

public theorem phaseSweepOrbit_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    phaseSweepOrbit W i x = constructedCentralOneCell W i (fun _ ↦ x 0) := by
  let _ := actualLocalCuspQuotientAction W
  have h : phaseSweepCarrier i x = constructedCentralEdgeCarrier i (fun _ ↦ x 0) := by
    unfold phaseSweepCarrier
    rw [phaseSweepZeroCarrier_boundary x hx, phaseSweepRotation_edge]
  have hp : phaseSweepPoint W i x = constructedCentralEdgeCellPoint W i (fun _ ↦ x 0) := by
    apply Subtype.ext
    apply Subtype.ext
    fin_cases i <;> exact h
  change Quotient.mk _ (phaseSweepPoint W i x) = _
  rw [hp]
  fin_cases i <;> rfl

public theorem phaseSweepOrbit_boundary_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    phaseSweepOrbit W i x ∈ constructedCentralOneSkeleton W := by
  rw [phaseSweepOrbit_boundary W i x hx]
  right
  apply Set.mem_iUnion.mpr
  refine ⟨i, (fun _ ↦ x 0), ?_, rfl⟩
  have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hb : |x 0| ≤ 1 := by simpa [Real.norm_eq_abs, hn] using norm_le_pi_norm x 0
  simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def, Real.norm_eq_abs] using hb

public theorem phaseSweepOrbit_boundary_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Disjoint (phaseSweepOrbit W i '' (Metric.closedBall 0 1 \ Metric.ball 0 1))
      (phaseSweepOrbit W i '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, ⟨hx, hxb⟩, rfl⟩ hp
  have hxs : x ∈ Metric.sphere 0 1 := by
    simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
      dist_zero_right, not_lt] at hx hxb ⊢
    exact le_antisymm hx hxb
  rw [phaseSweepOrbit_image] at hp
  exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_oneSkeleton_disjoint W i)
    hp (phaseSweepOrbit_boundary_oneSkeleton W i x hxs)

public theorem phaseSweepOrbit_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Topology.IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
      (phaseSweepOrbit W i)) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact isEmbedding_restrict_compact_separated
    (phaseSweepOrbit W i) (Metric.ball 0 1) (Metric.closedBall 0 1)
    (isCompact_closedBall 0 1) Metric.ball_subset_closedBall
    (phaseSweepOrbit_continuous W i).continuousOn
    (phaseSweepOrbit_injOn W i) (phaseSweepOrbit_boundary_disjoint W i)

public def phaseSweepCell (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.InjOn.toPartialEquiv (phaseSweepOrbit W i) (Metric.ball 0 1)
    (phaseSweepOrbit_injOn W i)

public theorem phaseSweepCell_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    ContinuousOn (phaseSweepCell W i).symm (phaseSweepCell W i).target := by
  let e := phaseSweepCell W i
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (phaseSweepOrbit_isEmbedding W i).continuous_iff.mpr
    have he : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (phaseSweepOrbit W i) ∘ lift =
        (Subtype.val : e.target → ActualLocalCuspCentralOrbitQuotient W) := by
      funext q
      exact e.right_inv q.2
    rw [he]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hlift

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
