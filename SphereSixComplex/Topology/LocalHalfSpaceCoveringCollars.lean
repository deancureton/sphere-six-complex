module
public import SphereSixComplex.Topology.LocalHalfSpaceCollars
public import SphereSixComplex.Topology.BrownCollaringClassicalBoundary
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section
noncomputable section
open Set Topology
open scoped NNReal
namespace SphereSixComplex

public theorem locallyCollared_of_projected_halfSpaceChart
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (B : Set Z) (p : X → Z) (hp : IsLocalHomeomorph p)
    (e : OpenPartialHomeomorph (Y × ℝ≥0) X) (y : Y)
    (hy : (y, 0) ∈ e.source)
    (hB : ∀ z ∈ e.source, p (e z) ∈ B ↔ z.2 = 0) :
    ∃ V : Set Z, V ⊆ B ∧ p (e (y, 0)) ∈ V ∧ IsOpen {b : B | b.1 ∈ V} ∧
      Nonempty (OpenTopologicalCollar Z V) := by
  obtain ⟨f, hf, hpf⟩ := hp (e (y, 0))
  have hs : (y, 0) ∈ (e.trans f).source := ⟨hy, hf⟩
  have hb : ∀ z ∈ (e.trans f).source, (e.trans f) z ∈ B ↔ z.2 = 0 := by
    intro z hz
    change f (e z) ∈ B ↔ z.2 = 0
    rw [← hpf]
    exact hB z hz.1
  simpa only [OpenPartialHomeomorph.trans_apply, ← hpf] using
    locallyCollared_of_halfSpaceChart B (e.trans f) y hs hb

end SphereSixComplex
