module

public import DifferentialGeometry.Topology.Morse.Cancellation.CancelFunction
public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelGoodExists

@[expose] public section

open Set

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M}

theorem main (c : IndexZeroCancellingPair I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  obtain ⟨k, ⟨hk⟩⟩ := c.exists_good
  exact k.exists_modification hk

end IndexZeroCancellingPair

end GradientLikeStrip

end DifferentialGeometry.Topology
