module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldDefs
public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossingFlow
public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldBand

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_modification_of_crossing (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    {f : M → ℝ} {a' b' : ℝ} (hf : MorseStrip I f a' b') {V' : (x : M) → TangentSpace I x}
    (hV' : isCrossingField I f a' b' V') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  obtain ⟨hsm, hcpt, η₀, hη₀, h2η₀, hcol, hcr⟩ := hV'
  exact (CrossingVectorField.mk V' hsm hcpt hf η₀ hη₀ h2η₀ hcol hcr).exists_modification

theorem exists_crossing_field (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a' b' : ℝ} {p q : M} (h : isCancellingPair I f a' b' p q) :
    ∃ V' : (x : M) → TangentSpace I x, isCrossingField I f a' b' V' := by
  exact CrossField.crossfield_target h

end DifferentialGeometry.Topology
