module

public import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.ContinuousFilling
public import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SimplyConnectedTarget
public import Mathlib.Analysis.Convex.GaugeRescale

@[expose] public section

/-! # Actual extension of planar convex-boundary maps in a simply connected target -/

noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q]

/-- Every continuous map on the actual boundary of a bounded closed planar
convex body extends to the same body. The proof uses the proved ambient
gauge homeomorphism and an actual disk filling of the original boundary loop. -/
theorem exists_convex_plane_boundary_extension {s : Set ℂ}
    (hc : Convex ℝ s) (hs : IsClosed s) (hb : Bornology.IsBounded s)
    (hi : (interior s).Nonempty) (f : C(frontier s, Q)) :
    ∃ F : C(s, Q), ∀ z : frontier s, F ⟨z.val, hs.frontier_subset z.property⟩ = f z := by
  obtain ⟨e, _, he, heB⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi hb
  rw [hs.closure_eq] at he
  have hboundary (z : Circle) : e.symm z.val ∈ frontier s := by
    have hz : z.val ∈ e '' frontier s := by rw [heB]; exact z.property
    obtain ⟨w, hw, hew⟩ := hz
    simpa only [← hew, e.symm_apply_apply] using hw
  let γ : freeLoop Q :=
    ⟨fun θ => f ⟨e.symm (AddCircle.toCircle θ : ℂ), hboundary (AddCircle.toCircle θ)⟩,
      f.continuous.comp ((e.symm.continuous.comp
        (continuous_subtype_val.comp AddCircle.continuous_toCircle)).subtype_mk _)⟩
  obtain ⟨u, hu⟩ := exists_continuous_disk_of_nullhomotopic (circleLoop_nullhomotopic γ)
  have hbody (z : s) : e z.val ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [← he]
    exact ⟨z.val, z.property, rfl⟩
  let F : C(s, Q) := ⟨fun z => u ⟨e z.val, hbody z⟩,
    u.continuous.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  refine ⟨F, ?_⟩
  intro z
  let a : Circle := ⟨e z.val, by
    change e z.val ∈ Metric.sphere (0 : ℂ) 1
    rw [← heB]
    exact ⟨z.val, z.property, rfl⟩⟩
  let θ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm a
  have hθ : AddCircle.toCircle θ = a := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply a
  have hd : (⟨e z.val, hbody ⟨z.val, hs.frontier_subset z.property⟩⟩ : closedDisk) = diskBoundary θ := by
    apply Subtype.ext
    exact (congrArg (fun w : Circle => (w : ℂ)) hθ).symm
  change u ⟨e z.val, hbody ⟨z.val, hs.frontier_subset z.property⟩⟩ = f z
  rw [hd]
  have htrace := congrArg (fun g : freeLoop Q => g θ) hu
  refine htrace.trans ?_
  change f ⟨e.symm (AddCircle.toCircle θ : ℂ), _⟩ = f z
  apply congrArg f
  apply Subtype.ext
  rw [hθ]
  exact e.symm_apply_apply z.val

end DifferentialGeometry.Topology
