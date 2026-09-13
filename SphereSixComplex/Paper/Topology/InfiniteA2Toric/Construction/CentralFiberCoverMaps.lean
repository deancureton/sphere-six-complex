module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberCover
public import SphereSixComplex.Prerequisites.Topology.ThreeTorusCoordinateMaps

/-! # Inclusion maps in the radial cover of the central fiber -/

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def centralAnnulusToInner (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) : C({x | centralRadius W x ∈ Ioo r s}, {x | centralRadius W x < s}) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem centralAnnulusHomotopyEquiv_diskMap_snd
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle))
    (hp : ‖p.1.1‖ ∈ Ioo r s) :
    (centralAnnulusHomotopyEquiv W r s hr hrs hs1
      ⟨centralDiskMap W p, by simpa using hp⟩).2 = p.2 := by
  have h : (⟨centralDiskMap W p, by simpa using hp⟩ :
      {x | centralRadius W x ∈ Ioo r s}) =
      centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)
        (⟨p.1.1, hp⟩, p.2) := rfl
  rw [h]
  change ((centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)).symm
    ((centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)) _)).2 = _
  rw [Homeomorph.symm_apply_apply]

theorem centralAnnulusToInner_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (x : {x | centralRadius W x ∈ Ioo r s}) :
    centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1 (centralAnnulusToInner W r s x) =
      Fin.tail (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1 x) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := centralDiskMap_surjective W x
  have hp : ‖p.1.1‖ ∈ Ioo r s := by simpa using hx
  have ht : Fin.tail (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1
      ⟨centralDiskMap W p, hx⟩) = fun i ↦
        (AddCircle.homeomorphCircle one_ne_zero).symm
          ((centralAnnulusHomotopyEquiv W r s hr hrs hs1
            ⟨centralDiskMap W p, hx⟩).2 i) := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  funext i
  change (AddCircle.homeomorphCircle one_ne_zero).symm
      (centralInnerHomotopyEquiv W s (hr.trans hrs) hs1
        ⟨centralDiskMap W p, hx.2⟩ i) =
    (AddCircle.homeomorphCircle one_ne_zero).symm
      ((centralAnnulusHomotopyEquiv W r s hr hrs hs1
        ⟨centralDiskMap W p, hx⟩).2 i)
  rw [centralInnerHomotopyEquiv_diskMap W s (hr.trans hrs) hs1 p hp.2,
    centralAnnulusHomotopyEquiv_diskMap_snd W r s hr hrs hs1 p hp]


theorem centralAnnulusToInner_coordinate_maps
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    (centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1).toFun.comp
      (centralAnnulusToInner W r s) =
      StandardTorusHomology.threeTorusTailProjection.comp
        (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1).toFun := by
  ext x i
  exact congrFun (centralAnnulusToInner_coordinates W r s hr hrs hs1 x) i

theorem centralAnnulusToInner_homology_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ)
    (x : IntegralSingularHomology n {x | centralRadius W x ∈ Ioo r s}) :
    integralSingularHomologyMap n
        (centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1).toFun
        (integralSingularHomologyMap n (centralAnnulusToInner W r s) x) =
      integralSingularHomologyMap n StandardTorusHomology.threeTorusTailProjection
        (integralSingularHomologyMap n
          (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1).toFun x) := by
  rw [integralSingularHomologyMap_comp_wang, centralAnnulusToInner_coordinate_maps,
    integralSingularHomologyMap_comp_wang]

def centralAnnulusToOuter (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) : C({x | centralRadius W x ∈ Ioo r s}, {x | r < centralRadius W x}) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem centralOuterHomotopyEquiv_diskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle))
    (hp : r < ‖p.1.1‖) :
    centralOuterHomotopyEquiv W r hr hr1
      ⟨centralDiskMap W p, by simpa using hp⟩ =
      centralAttachingMap W
        ⟨(ballRadialExpansion r hr (1, p.1), p.2),
          norm_ballRadialExpansion_one r hr p.1 hp.le⟩ := by
  have he : (centralAttachmentHomeomorph W).symm (centralDiskMap W p) =
      AdjunctionSpace.inl _ (centralAttachingMap W) p := by
    apply (centralAttachmentHomeomorph W).injective
    rw [Homeomorph.apply_symm_apply, centralAttachmentHomeomorph_inl]
  change AdjunctionSpace.radialCollarRetraction (centralAttachingMap W) r hr hr1
    (isEmbedding_centralAttachment_inr W)
      ⟨(centralAttachmentHomeomorph W).symm (centralDiskMap W p), _⟩ = _
  simp only [he]
  exact AdjunctionSpace.radialCollarRetraction_inl (centralAttachingMap W) r hr hr1
    (isEmbedding_centralAttachment_inr W) p hp


/-- The boundary attaching map in sphere and phase coordinates. -/
def centralSphereAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(Metric.sphere (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle), centralBoundary W) where
  toFun p := centralAttachingMap W
    ⟨(⟨p.1.1, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (mem_sphere_zero_iff_norm.mp p.1.2).le⟩, p.2),
      mem_sphere_zero_iff_norm.mp p.1.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_centralDiskMap W).comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd)

@[simp] theorem centralAnnulusHomotopyEquiv_diskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (p : Metric.closedBall (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle))
    (hp : ‖p.1.1‖ ∈ Ioo r s) :
    centralAnnulusHomotopyEquiv W r s hr hrs hs1
      ⟨centralDiskMap W p, by simpa using hp⟩ =
      ((normPreimageHomeomorph (Fin 2 → ℝ) (Ioo r s)
        (fun _ hx ↦ hr.trans hx.1) ⟨p.1.1, hp⟩).1, p.2) := by
  have h : (⟨centralDiskMap W p, by simpa using hp⟩ :
      {x | centralRadius W x ∈ Ioo r s}) =
      centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)
        (⟨p.1.1, hp⟩, p.2) := rfl
  rw [h]
  change normPreimageProdHomotopyEquiv (Fin 2 → ℝ) (Fin 2 → Circle) (Ioo r s)
    (fun _ hx ↦ hr.trans hx.1) (convex_Ioo r s) (nonempty_Ioo.mpr hrs)
    ((centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)).symm
      ((centralRadialHomeomorph W (Ioo r s) (fun _ hx ↦ hx.2.trans_le hs1)) _)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem centralAnnulusToOuter_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (x : {x | centralRadius W x ∈ Ioo r s}) :
    centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1) (centralAnnulusToOuter W r s x) =
      centralSphereAttachingMap W (centralAnnulusHomotopyEquiv W r s hr hrs hs1 x) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := centralDiskMap_surjective W x
  have hp : ‖p.1.1‖ ∈ Ioo r s := by simpa using hx
  change centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)
    ⟨centralDiskMap W p, hx.1⟩ = _
  rw [centralOuterHomotopyEquiv_diskMap W r hr (hrs.trans_le hs1) p hp.1,
    centralAnnulusHomotopyEquiv_diskMap W r s hr hrs hs1 p hp]
  apply congrArg (centralAttachingMap W)
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change ((1 - (1 : ℝ)) + 1 / max r ‖p.1.1‖) • p.1.1 = ‖p.1.1‖⁻¹ • p.1.1
    simp [max_eq_right hp.1.le]
  · rfl


/-- Sphere and phase coordinates, with the sphere circle first. -/
def centralSpherePhaseTorusHomeomorph :
    Metric.sphere (0 : Fin 2 → ℝ) 1 × (Fin 2 → Circle) ≃ₜ (Fin 3 → UnitAddCircle) := by
  let e : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (Fin 1 → UnitAddCircle) :=
    (supNormUnitSphereCircleHomeomorph.trans
      (AddCircle.homeomorphCircle one_ne_zero).symm).trans
        (Homeomorph.funUnique (Fin 1) UnitAddCircle).symm
  let eT : (Fin 2 → Circle) ≃ₜ (Fin 2 → UnitAddCircle) :=
    Homeomorph.piCongrRight (fun _ ↦ (AddCircle.homeomorphCircle one_ne_zero).symm)
  exact (e.prodCongr eT).trans (Fin.appendHomeomorph 1 2)

/-- The actual attaching map with three additive circle coordinates. -/
def centralTorusAttachingMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(Fin 3 → UnitAddCircle, centralBoundary W) :=
  (centralSphereAttachingMap W).comp (centralSpherePhaseTorusHomeomorph.symm : C(_, _))

@[simp] theorem centralTorusAttachingMap_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (z : Fin 3 → UnitAddCircle) :
    centralTorusAttachingMap W z = centralSphereAttachingMap W
      (supNormUnitSphereCircleHomeomorph.symm (AddCircle.homeomorphCircle one_ne_zero (z 0)),
        fun i ↦ AddCircle.homeomorphCircle one_ne_zero (z i.succ)) := by
  apply congrArg (centralSphereAttachingMap W)
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem centralAnnulusToOuter_torus_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (x : {x | centralRadius W x ∈ Ioo r s}) :
    centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1) (centralAnnulusToOuter W r s x) =
      centralTorusAttachingMap W (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1 x) := by
  rw [centralAnnulusToOuter_coordinates]
  change centralSphereAttachingMap W (centralAnnulusHomotopyEquiv W r s hr hrs hs1 x) =
    centralSphereAttachingMap W (centralSpherePhaseTorusHomeomorph.symm
      (centralSpherePhaseTorusHomeomorph (centralAnnulusHomotopyEquiv W r s hr hrs hs1 x)))
  rw [Homeomorph.symm_apply_apply]

theorem centralAnnulusToOuter_coordinate_maps
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)).toFun.comp
      (centralAnnulusToOuter W r s) =
      (centralTorusAttachingMap W).comp
        (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1).toFun := by
  ext x
  exact congrArg Subtype.val (centralAnnulusToOuter_torus_coordinates W r s hr hrs hs1 x)

theorem centralAnnulusToOuter_homology_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ)
    (x : IntegralSingularHomology n {x | centralRadius W x ∈ Ioo r s}) :
    integralSingularHomologyMap n
        (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)).toFun
        (integralSingularHomologyMap n (centralAnnulusToOuter W r s) x) =
      integralSingularHomologyMap n (centralTorusAttachingMap W)
        (integralSingularHomologyMap n
          (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1).toFun x) := by
  rw [integralSingularHomologyMap_comp_wang, centralAnnulusToOuter_coordinate_maps,
    integralSingularHomologyMap_comp_wang]

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
