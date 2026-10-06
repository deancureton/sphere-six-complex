module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric

abbrev Disk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

def diskSphere (n : ℕ) : Set (Disk n) := Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin n)) 1

def diskInterior (n : ℕ) : Set (Disk n) := Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin n)) 1

theorem mem_diskSphere {n : ℕ} {x : Disk n} :
    x ∈ diskSphere n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simp [diskSphere]

theorem mem_diskInterior {n : ℕ} {x : Disk n} :
    x ∈ diskInterior n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
  simp [diskInterior]

theorem diskSphere_union_diskInterior (n : ℕ) : diskSphere n ∪ diskInterior n = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_diskSphere, mem_diskInterior, Set.mem_univ, iff_true]
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2
  rcases lt_or_eq_of_le hx with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem disjoint_diskSphere_diskInterior (n : ℕ) : Disjoint (diskSphere n) (diskInterior n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_diskSphere] at hx
  rw [mem_diskInterior] at hx'
  exact absurd hx (ne_of_lt hx')

theorem isClosed_diskSphere (n : ℕ) : IsClosed (diskSphere n) :=
  isClosed_sphere.preimage continuous_subtype_val

theorem isOpen_diskInterior (n : ℕ) : IsOpen (diskInterior n) :=
  isOpen_ball.preimage continuous_subtype_val

noncomputable def diskSphereHomeomorph (n : ℕ) :
    diskSphere n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by rw [Subtype.range_coe]; exact sphere_subset_closedBall)

end DifferentialGeometry.Topology
