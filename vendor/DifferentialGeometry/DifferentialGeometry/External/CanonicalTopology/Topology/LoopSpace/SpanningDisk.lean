module

public import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-!
# The parameter disk and its boundary component

The closed disk is the actual Euclidean unit disk in `ℂ ≃ ℝ²`; the
period-one boundary parametrization is `θ ↦ exp (2πiθ)`.

This proves the topological clauses of `master03:lem-plateau-component`:
loops, spanning disks (also with changed boundary parameter), and contractions
corestrict to the same connected component. The differential and area clauses
of that source lemma are not asserted in this file.
-/

noncomputable section

open ContinuousMap Set

namespace DifferentialGeometry.Topology

/-- The closed Euclidean unit disk. -/
abbrev closedDisk := Metric.closedBall (0 : ℂ) 1

instance : ContractibleSpace closedDisk :=
  Metric.contractibleSpace_closedBall (by norm_num)

instance : CompactSpace closedDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)

/-- The positively parametrized boundary with period one. -/
def diskBoundary : C(loopCircle, closedDisk) :=
  ⟨fun θ => ⟨(AddCircle.toCircle θ : ℂ), by
      simp [Metric.mem_closedBall, dist_zero_right]⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp AddCircle.continuous_toCircle⟩

@[simp] theorem diskBoundary_coe (θ : ℝ) :
    (diskBoundary (θ : loopCircle) : ℂ) = Complex.exp ((2 * Real.pi * θ : ℝ) * Complex.I) := by
  simp [diskBoundary, AddCircle.toCircle_apply_mk, Circle.coe_exp]

/-- The exact trace of a continuous disk, still with its given parametrization. -/
def diskTrace {Q : Type*} [TopologicalSpace Q] (u : C(closedDisk, Q)) : freeLoop Q :=
  u.comp diskBoundary

/-- A continuous disk supplies an actual nullhomotopy of its trace. -/
theorem diskTrace_nullhomotopic {Q : Type*} [TopologicalSpace Q] (u : C(closedDisk, Q)) :
    (diskTrace u).Nullhomotopic :=
  ((id_nullhomotopic closedDisk).comp_right u).comp_left diskBoundary

section Component

variable {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]

/-- A connected-domain map meeting a component stays in that component. -/
theorem map_mem_connectedComponent [PreconnectedSpace X] (f : C(X, Q))
    (x₀ : X) (q : Q) (h : f x₀ ∈ connectedComponent q) (x : X) :
    f x ∈ connectedComponent q := by
  have hx := f.continuous.mapsTo_connectedComponent x₀
  rw [PreconnectedSpace.connectedComponent_eq_univ] at hx
  rw [connectedComponent_eq h]
  exact hx (mem_univ x)

/-- The actual connected component of the boundary loop. -/
abbrev loopComponent (γ : freeLoop Q) := connectedComponent (γ 0)

theorem loop_mem_component (γ : freeLoop Q) (θ : loopCircle) : γ θ ∈ loopComponent γ :=
  map_mem_connectedComponent γ 0 (γ 0) mem_connectedComponent θ

/-- Corestriction keeps the values and the parameter of the original loop. -/
def loopInComponent (γ : freeLoop Q) : freeLoop (loopComponent γ) :=
  ⟨fun θ => ⟨γ θ, loop_mem_component γ θ⟩, γ.continuous.subtype_mk _⟩

@[simp] theorem loopInComponent_coe (γ : freeLoop Q) (θ : loopCircle) :
    (loopInComponent γ θ : Q) = γ θ := rfl

/-- Every disk with this boundary lies in the boundary component.
Only continuity of the boundary change is needed for this topological assertion. -/
theorem disk_mem_loopComponent (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) (z : closedDisk) :
    u z ∈ loopComponent γ := by
  apply map_mem_connectedComponent u (diskBoundary 0) (γ 0) _ z
  have h := congrArg (fun η : freeLoop Q => η 0) htrace
  change u (diskBoundary 0) = γ (ψ 0) at h
  rw [h]
  exact loop_mem_component γ (ψ 0)

/-- The selected disk itself, corestricted to the boundary component. -/
def diskInLoopComponent (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) :
    C(closedDisk, loopComponent γ) :=
  ⟨fun z => ⟨u z, disk_mem_loopComponent γ ψ u htrace z⟩, u.continuous.subtype_mk _⟩

@[simp] theorem diskInLoopComponent_coe (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) (z : closedDisk) :
    (diskInLoopComponent γ ψ u htrace z : Q) = u z := rfl

theorem diskInLoopComponent_trace (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) :
    diskTrace (diskInLoopComponent γ ψ u htrace) = (loopInComponent γ).comp ψ := by
  ext θ
  exact congrArg (fun η : freeLoop Q => η θ) htrace

/-- Corestrict a given contraction, with no choice of a new disk or homotopy. -/
theorem loopInComponent_nullhomotopic (γ : freeLoop Q) (hγ : γ.Nullhomotopic) :
    (loopInComponent γ).Nullhomotopic := by
  obtain ⟨q, ⟨H⟩⟩ := hγ
  have hH (p : unitInterval × loopCircle) : H p ∈ loopComponent γ := by
    apply map_mem_connectedComponent H.toContinuousMap (0, 0) (γ 0) _ p
    simpa using (mem_connectedComponent (x := γ 0))
  have hq : q ∈ loopComponent γ := by simpa using hH (1, 0)
  refine ⟨⟨q, hq⟩, ⟨{
    toFun := fun p => ⟨H p, hH p⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro θ
    apply Subtype.ext
    exact H.apply_zero θ
  · intro θ
    apply Subtype.ext
    exact H.apply_one θ

theorem loopComponent_eq_of_contains (γ : freeLoop Q) (q : Q)
    (h : ∀ θ, γ θ ∈ connectedComponent q) : loopComponent γ = connectedComponent q :=
  (connectedComponent_eq (h 0)).symm

theorem isClosed_loopComponent (γ : freeLoop Q) : IsClosed (loopComponent γ) :=
  isClosed_connectedComponent

theorem isOpen_loopComponent [LocallyConnectedSpace Q] (γ : freeLoop Q) :
    IsOpen (loopComponent γ) := isOpen_connectedComponent

instance (γ : freeLoop Q) : ConnectedSpace (loopComponent γ) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

instance [CompactSpace Q] (γ : freeLoop Q) : CompactSpace (loopComponent γ) :=
  isCompact_iff_compactSpace.mp (isClosed_loopComponent γ).isCompact

end Component

end DifferentialGeometry.Topology
