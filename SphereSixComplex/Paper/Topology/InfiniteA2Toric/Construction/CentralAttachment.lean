module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveSingletonBall
public import SphereSixComplex.Prerequisites.Topology.CompactAdjunction
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryModel

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem positiveCentralCell_phase_eq_of_first_two
    {r : ℝ} (hr : 0 < r) (q : constructedPositiveCentralCell r 0)
    (k l : CompactTorus) (h : k 0 = l 0 ∧ k 1 = l 1) :
    constructedModel.torusAction (compactTorusEmbedding k) (q.1.1.1.1 : Carrier) =
      constructedModel.torusAction (compactTorusEmbedding l) (q.1.1.1.1 : Carrier) := by
  obtain ⟨⟨i, p⟩, rfl⟩ := surjective_cellSquareProjection hr 0 q
  apply (cellSquareCarrierPoint_compactPhase_eq_iff k l 0 i p).mpr
  intro j _
  exact (zeroRay_effectivePhase_iff k l i).mpr h j

public theorem zeroSupport_mem_closedPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : 0 ∈ componentSupport constructedModel (p.1.1 : Carrier)) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∈ Set.range (closedPhaseCellMap W) := by
  let _ := actualLocalCuspQuotientAction W
  let q : constructedPositiveCentralFiber W.localWitness.radius :=
    ⟨constructedLocalModulusRetraction W.localWitness.radius p.1, by
      change constructedModel.t (constructedLocalModulusRetraction W.localWitness.radius p.1) = 0
      rw [constructedLocalModulusRetraction_t, p.property]
      simp⟩
  obtain ⟨phi, hphi⟩ := constructedLocalModulusRetraction_polar_surjective
    W.localWitness.radius p.1
  have hsupport : componentSupport constructedModel (q.1.1.1 : Carrier) =
      componentSupport constructedModel (p.1.1 : Carrier) := by
    ext v
    have h := constructedModel.torusAction_centralComponent
      (compactTorusEmbedding phi) v (q.1.1.1 : constructedModel.Carrier)
    rw [hphi] at h
    exact h.symm
  let qcell : constructedPositiveCentralCell W.localWitness.radius 0 :=
    ⟨q, by
      change 0 ∈ componentSupport constructedModel (q.1.1.1 : Carrier)
      rwa [hsupport]⟩
  let k : Fin 2 → Circle := fun j ↦ phi j.castSucc
  have hn := (positiveCentralCell_phase_eq_of_first_two
    W.localWitness.radius_pos qcell (effectivePhaseSection k) phi ⟨rfl, rfl⟩)
  have heq : effectivePhaseCentralPoint W k q = p :=
    Subtype.ext (Subtype.ext (hn.trans hphi))
  refine ⟨(qcell, k), ?_⟩
  change Quotient.mk _ (effectivePhaseCentralPoint W k q) = _
  rw [heq]


public theorem closedPhaseCellMap_surjective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Surjective (closedPhaseCellMap W) := by
  let _ := actualLocalCuspQuotientAction W
  intro x
  induction x using Quotient.inductionOn with
  | _ p =>
    obtain ⟨v, hv⟩ := componentSupport_nonempty_of_t_eq_zero constructedModel p.property
    obtain ⟨lambda, hlambda⟩ := shearVector_surjective (-v)
    let g := Multiplicative.ofAdd lambda
    let q : actualLocalCuspCentralSubMulAction W := g • p
    have hq : 0 ∈ componentSupport constructedModel (q.1.1 : Carrier) := by
      rw [actualCentral_support_smul]
      exact ⟨v, hv, by simp [g, hlambda]⟩
    have heq : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W)) q = Quotient.mk _ p := by
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W) q p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, rfl⟩
    rw [← heq]
    exact zeroSupport_mem_closedPhaseImage W q hq

/-- The lower-dimensional orbit locus in the central fiber. -/
public def centralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  (singletonPhaseImage W)ᶜ

/-- The closed positive disk with its two effective phase coordinates. -/
public def centralDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle)) :
    ActualLocalCuspCentralOrbitQuotient W :=
  closedPhaseCellMap W (closedBallPositiveCellHomeomorph W p.1, p.2)

public theorem continuous_centralDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (centralDiskMap W) :=
  (continuous_closedPhaseCellMap W).comp
    (((closedBallPositiveCellHomeomorph W).continuous.comp continuous_fst).prodMk continuous_snd)

public theorem centralDiskMap_surjective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Surjective (centralDiskMap W) := by
  intro x
  obtain ⟨⟨q, k⟩, rfl⟩ := closedPhaseCellMap_surjective W x
  exact ⟨((closedBallPositiveCellHomeomorph W).symm q, k), by
    simp [centralDiskMap]⟩

public theorem centralDiskMap_mem_boundary_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle)) :
    centralDiskMap W p ∈ centralBoundary W ↔ ‖p.1.1‖ = 1 := by
  have h := (closedPhaseCellMap_mem_singletonImage_iff W
    (closedBallPositiveCellHomeomorph W p.1, p.2)).trans
    (closedBallPositiveCellHomeomorph_support_iff W p.1)
  change ¬ closedPhaseCellMap W _ ∈ singletonPhaseImage W ↔ _
  rw [h, Metric.mem_ball, dist_zero_right, not_lt]
  have hp : ‖p.1.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using p.1.property
  exact ⟨fun h ↦ le_antisymm hp h, fun h ↦ h.ge⟩

public theorem centralDiskMap_injOn_interior
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set.InjOn (centralDiskMap W) {p | ‖p.1.1‖ < 1} := by
  intro p hp q hq hpq
  change ‖p.1.1‖ < 1 at hp
  change ‖q.1.1‖ < 1 at hq
  have hp' : componentSupport constructedModel
      ((closedBallPositiveCellHomeomorph W p.1).1.1.1.1 : Carrier) = {0} :=
    (closedBallPositiveCellHomeomorph_support_iff W p.1).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hp)
  have hq' : componentSupport constructedModel
      ((closedBallPositiveCellHomeomorph W q.1).1.1.1.1 : Carrier) = {0} :=
    (closedBallPositiveCellHomeomorph_support_iff W q.1).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hq)
  have h := injective_effectivePhaseCentralOrbit_prod W
    (a₁ := (⟨closedBallPositiveCellHomeomorph W p.1, hp'⟩, p.2))
    (a₂ := (⟨closedBallPositiveCellHomeomorph W q.1, hq'⟩, q.2)) hpq
  apply Prod.ext
  · exact (closedBallPositiveCellHomeomorph W).injective
      (congrArg (fun x ↦ x.1.1) h)
  · exact congrArg (fun x : positiveSingletonStratum W.localWitness.radius × (Fin 2 → Circle) ↦ x.2) h

public theorem centralBoundary_eq_image
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    centralBoundary W = centralDiskMap W '' {p | ‖p.1.1‖ = 1} := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := centralDiskMap_surjective W x
    exact ⟨p, (centralDiskMap_mem_boundary_iff W p).mp hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (centralDiskMap_mem_boundary_iff W p).mpr hp

public theorem isCompact_centralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsCompact (centralBoundary W) := by
  rw [centralBoundary_eq_image]
  apply IsCompact.image _ (continuous_centralDiskMap W)
  exact (isClosed_eq (continuous_norm.comp
    (continuous_subtype_val.comp continuous_fst)) continuous_const).isCompact

public theorem isClosed_centralBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsClosed (centralBoundary W) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact (isCompact_centralBoundary W).isClosed

public def centralAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : {p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) |
      ‖p.1.1‖ = 1}) : centralBoundary W :=
  ⟨centralDiskMap W p.1, (centralDiskMap_mem_boundary_iff W p.1).mpr p.2⟩

public def centralAttachmentHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    AdjunctionSpace {p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) |
      ‖p.1.1‖ = 1} (centralAttachingMap W) ≃ₜ ActualLocalCuspCentralOrbitQuotient W := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let f : C((Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle),
      ActualLocalCuspCentralOrbitQuotient W) :=
    ⟨centralDiskMap W, continuous_centralDiskMap W⟩
  have hinj : Set.InjOn f (f ⁻¹' centralBoundary W)ᶜ := by
    apply (centralDiskMap_injOn_interior W).mono
    intro p hp
    change ¬ centralDiskMap W p ∈ centralBoundary W at hp
    rw [centralDiskMap_mem_boundary_iff] at hp
    have hle : ‖p.1.1‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using p.1.property
    exact lt_of_le_of_ne hle hp
  have hA : f ⁻¹' centralBoundary W = {p | ‖p.1.1‖ = 1} := by
    ext p
    exact centralDiskMap_mem_boundary_iff W p
  exact f.adjunctionHomeomorphOfPreimage (centralDiskMap_surjective W)
    (centralBoundary W) (isClosed_centralBoundary W) _ (centralAttachingMap W) hA
    (fun _ ↦ rfl) (by rwa [← hA])

@[simp] public theorem centralAttachmentHomeomorph_inl
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle)) :
    centralAttachmentHomeomorph W (AdjunctionSpace.inl _ (centralAttachingMap W) p) =
      centralDiskMap W p := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  unfold centralAttachmentHomeomorph
  exact ContinuousMap.adjunctionHomeomorphOfPreimage_inl _ _ _ _ _ _ _ _ _ _

@[simp] public theorem centralAttachmentHomeomorph_inr
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (b : centralBoundary W) :
    centralAttachmentHomeomorph W (AdjunctionSpace.inr _ (centralAttachingMap W) b) = b.1 := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  unfold centralAttachmentHomeomorph
  exact ContinuousMap.adjunctionHomeomorphOfPreimage_inr _ _ _ _ _ _ _ _ _ _

/-- The attaching map expressed in the three-sphere boundary model. -/
public def sphereAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : {p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) |
      ‖p.1.1‖ = 1}) : CentralBoundary.Spheres :=
  (CentralBoundary.homeomorph W).symm (centralAttachingMap W p)

/-- The cusp central fiber is a disk-times-torus attached to three spheres sharing two poles. -/
public def centralFiberAttachmentHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    AdjunctionSpace {p : (Metric.closedBall (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) |
      ‖p.1.1‖ = 1} (sphereAttachingMap W) ≃ₜ ActualLocalCuspCentralOrbitQuotient W :=
  (AdjunctionSpace.congrRight _ (centralAttachingMap W)
    (CentralBoundary.homeomorph W).symm).symm.trans (centralAttachmentHomeomorph W)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
end
