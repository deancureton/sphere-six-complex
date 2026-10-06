module

public import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk

@[expose] public section

/-!
# Continuous disks from nullhomotopies

The radial map from the cylinder to the actual closed Euclidean disk is a
quotient map. A nullhomotopy, constant on its collapsed end, therefore gives
a continuous disk with the exact prescribed boundary parameter. This is the
topological input to `lem:rfs-disk-competitor-exists`, before smoothing.
-/

noncomputable section

open ContinuousMap Set
open scoped unitInterval Topology

namespace DifferentialGeometry.Topology

/-- The radial presentation of the disk as the cone on the period-one circle. -/
def diskConeProjection : C(unitInterval × loopCircle, closedDisk) :=
  ⟨fun p => ⟨(p.1 : ℝ) • (AddCircle.toCircle p.2 : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg p.1.property.1]
      exact p.1.property.2⟩,
    by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp continuous_snd))⟩

@[simp] theorem diskConeProjection_norm (p : unitInterval × loopCircle) :
    ‖(diskConeProjection p : ℂ)‖ = (p.1 : ℝ) := by
  change ‖(p.1 : ℝ) • (AddCircle.toCircle p.2 : ℂ)‖ = (p.1 : ℝ)
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg p.1.property.1]

@[simp] theorem diskConeProjection_one (θ : loopCircle) :
    diskConeProjection (1, θ) = diskBoundary θ := by
  apply Subtype.ext
  simp [diskConeProjection, diskBoundary]

theorem diskConeProjection_surjective : Function.Surjective diskConeProjection := by
  intro z
  by_cases hz : (z : ℂ) = 0
  · refine ⟨(0, 0), ?_⟩
    apply Subtype.ext
    simp [diskConeProjection, hz]
  let r : unitInterval := ⟨‖(z : ℂ)‖, norm_nonneg _, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  let a : Circle := ⟨‖(z : ℂ)‖⁻¹ • (z : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  refine ⟨(r, e.symm a), ?_⟩
  apply Subtype.ext
  change ‖(z : ℂ)‖ • (AddCircle.toCircle (e.symm a) : ℂ) = z
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero, e.apply_symm_apply]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hz) (z : ℂ)

theorem diskConeProjection_isQuotientMap :
    _root_.Topology.IsQuotientMap diskConeProjection :=
  .of_surjective_continuous diskConeProjection_surjective diskConeProjection.continuous

theorem diskConeProjection_fiber {p q : unitInterval × loopCircle}
    (h : diskConeProjection p = diskConeProjection q) :
    p.1 = q.1 ∧ ((p.1 : ℝ) = 0 ∨ p.2 = q.2) := by
  have hr : p.1 = q.1 := Subtype.ext (by
    simpa only [diskConeProjection_norm] using congrArg (fun z : closedDisk => ‖(z : ℂ)‖) h)
  refine ⟨hr, ?_⟩
  by_cases hp : (p.1 : ℝ) = 0
  · exact Or.inl hp
  right
  apply AddCircle.injective_toCircle one_ne_zero
  apply Circle.coe_injective
  have he := congrArg (fun z : closedDisk => (z : ℂ)) h
  change (p.1 : ℝ) • (AddCircle.toCircle p.2 : ℂ) =
    (q.1 : ℝ) • (AddCircle.toCircle q.2 : ℂ) at he
  rw [← hr] at he
  exact (smul_right_injective ℂ hp) he

/-- The converse of `diskTrace_nullhomotopic`, with the same exact trace. -/
theorem exists_continuous_disk_of_nullhomotopic {Q : Type*} [TopologicalSpace Q]
    {γ : freeLoop Q} (hγ : γ.Nullhomotopic) :
    ∃ u : C(closedDisk, Q), diskTrace u = γ := by
  classical
  obtain ⟨q, ⟨H⟩⟩ := hγ
  let F := H.symm
  have hfiber {p r : unitInterval × loopCircle}
      (h : diskConeProjection p = diskConeProjection r) : F p = F r := by
    obtain ⟨hr, hp | hp⟩ := diskConeProjection_fiber h
    · have hp0 : p.1 = 0 := Subtype.ext hp
      have hr0 : r.1 = 0 := hr ▸ hp0
      change F (p.1, p.2) = F (r.1, r.2)
      rw [hp0, hr0, F.apply_zero, F.apply_zero]
      rfl
    · exact congrArg F (Prod.ext hr hp)
  let j := Function.surjInv diskConeProjection_surjective
  have hj : ∀ z, diskConeProjection (j z) = z :=
    Function.surjInv_eq diskConeProjection_surjective
  let u : closedDisk → Q := fun z => F (j z)
  have hucomp : u ∘ diskConeProjection = F := by
    funext p
    exact hfiber (hj (diskConeProjection p))
  have hu : Continuous u := diskConeProjection_isQuotientMap.continuous_iff.mpr
    (hucomp.symm ▸ F.continuous)
  refine ⟨⟨u, hu⟩, ?_⟩
  ext θ
  change u (diskBoundary θ) = γ θ
  rw [← diskConeProjection_one θ]
  exact (congrFun hucomp (1, θ)).trans (F.apply_one θ)

theorem nullhomotopic_iff_exists_continuous_disk {Q : Type*} [TopologicalSpace Q]
    (γ : freeLoop Q) : γ.Nullhomotopic ↔ ∃ u : C(closedDisk, Q), diskTrace u = γ :=
  ⟨exists_continuous_disk_of_nullhomotopic, fun ⟨u, hu⟩ => hu ▸ diskTrace_nullhomotopic u⟩

end DifferentialGeometry.Topology
