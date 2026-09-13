module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralAttachment
public import SphereSixComplex.Prerequisites.Topology.AdjunctionCollarEquiv
public import SphereSixComplex.Prerequisites.Topology.UnitSphereEquiv

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def centralRadius (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(ActualLocalCuspCentralOrbitQuotient W, ℝ) := by
  let ρ : C(AdjunctionSpace
      {p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle) | ‖p.1.1‖ = 1}
      (centralAttachingMap W), ℝ) :=
    AdjunctionSpace.radius (centralAttachingMap W)
  exact ρ.comp ⟨(centralAttachmentHomeomorph W).symm,
    (centralAttachmentHomeomorph W).symm.continuous⟩

@[simp] public theorem centralRadius_centralDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle)) :
    centralRadius W (centralDiskMap W p) = ‖p.1.1‖ := by
  rw [← centralAttachmentHomeomorph_inl W p]
  change AdjunctionSpace.radius _ ((centralAttachmentHomeomorph W).symm
    ((centralAttachmentHomeomorph W) _)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

public theorem isEmbedding_centralAttachment_inr
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsEmbedding (AdjunctionSpace.inr _ (centralAttachingMap W)) := by
  have h : AdjunctionSpace.inr _ (centralAttachingMap W) =
      (centralAttachmentHomeomorph W).symm ∘ Subtype.val := by
    funext b
    apply (centralAttachmentHomeomorph W).injective
    simp
  rw [h]
  exact (centralAttachmentHomeomorph W).symm.isEmbedding.comp IsEmbedding.subtypeVal

public def centralOuterHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    {x | r < centralRadius W x} ≃ₕ centralBoundary W :=
  ((centralAttachmentHomeomorph W).symm.subtype (fun _ ↦ Iff.rfl)).toHomotopyEquiv.trans
    (AdjunctionSpace.radialCollarHomotopyEquiv (centralAttachingMap W) r hr hr1
      (isEmbedding_centralAttachment_inr W))

public def centralRadialHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (S : Set ℝ) (hS : S ⊆ Iio 1) :
    {x : Fin 2 → ℝ | ‖x‖ ∈ S} × (Fin 2 → Circle) ≃ₜ
      {x | centralRadius W x ∈ S} := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let f : C(Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle),
      ActualLocalCuspCentralOrbitQuotient W) :=
    ⟨centralDiskMap W, continuous_centralDiskMap W⟩
  exact f.radialPreimageHomeomorph (centralDiskMap_surjective W) (centralRadius W)
    (centralRadius_centralDiskMap W) (centralDiskMap_injOn_interior W) S hS

public def centralInnerHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    {x | centralRadius W x < s} ≃ₕ (Fin 2 → Circle) := by
  let hball : {x : Fin 2 → ℝ | ‖x‖ ∈ Iio s} ≃ₜ Metric.ball (0 : Fin 2 → ℝ) s :=
    Homeomorph.setCongr (by ext x; simp [Metric.mem_ball, dist_zero_right])
  exact (centralRadialHomeomorph W (Iio s) (fun _ hx ↦ hx.trans_le hs1)).symm.toHomotopyEquiv.trans
    ((hball.prodCongr (Homeomorph.refl _)).toHomotopyEquiv.trans
      (SphereSixComplex.ballProdHomotopyEquiv (Fin 2 → ℝ) (Fin 2 → Circle) s hs))

@[simp] public theorem centralInnerHomotopyEquiv_diskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle)) (hp : ‖p.1.1‖ < s) :
    centralInnerHomotopyEquiv W s hs hs1
      ⟨centralDiskMap W p, by simpa using hp⟩ = p.2 := by
  have h : (⟨centralDiskMap W p, by simpa using hp⟩ : {x | centralRadius W x < s}) =
      centralRadialHomeomorph W (Iio s) (fun _ hx ↦ hx.trans_le hs1)
        (⟨p.1.1, hp⟩, p.2) := rfl
  rw [h]
  change ((centralRadialHomeomorph W (Iio s) (fun _ hx ↦ hx.trans_le hs1)).symm
    ((centralRadialHomeomorph W (Iio s) (fun _ hx ↦ hx.trans_le hs1)) _)).2 = _
  rw [Homeomorph.symm_apply_apply]

public def centralAnnulusHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    {x | centralRadius W x ∈ Ioo r s} ≃ₕ
      Metric.sphere (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle) :=
  (centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)).symm.toHomotopyEquiv.trans
    (SphereSixComplex.normPreimageProdHomotopyEquiv (Fin 2 → ℝ) (Fin 2 → Circle)
      (Ioo r s) (fun _ hx ↦ hr.trans hx.1) (convex_Ioo r s) (nonempty_Ioo.mpr hrs))

public def centralInnerTorusHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    {x | centralRadius W x < s} ≃ₕ (Fin 2 → UnitAddCircle) :=
  (centralInnerHomotopyEquiv W s hs hs1).trans
    (Homeomorph.piCongrRight (fun _ ↦ (AddCircle.homeomorphCircle one_ne_zero).symm)).toHomotopyEquiv

public def centralAnnulusTorusHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    {x | centralRadius W x ∈ Ioo r s} ≃ₕ (Fin 3 → UnitAddCircle) := by
  let e : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (Fin 1 → UnitAddCircle) :=
    (SphereSixComplex.supNormUnitSphereCircleHomeomorph.trans
      (AddCircle.homeomorphCircle one_ne_zero).symm).trans
        (Homeomorph.funUnique (Fin 1) UnitAddCircle).symm
  let eT : (Fin 2 → Circle) ≃ₜ (Fin 2 → UnitAddCircle) :=
    Homeomorph.piCongrRight (fun _ ↦ (AddCircle.homeomorphCircle one_ne_zero).symm)
  exact (centralAnnulusHomotopyEquiv W r s hr hrs hs1).trans
    (((e.prodCongr eT).trans (Fin.appendHomeomorph 1 2)).toHomotopyEquiv)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
end
