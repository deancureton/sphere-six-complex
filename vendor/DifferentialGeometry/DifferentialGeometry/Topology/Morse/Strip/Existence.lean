module

public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.Morse.Strip.Foundations.RelativePerturbation

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_morseStrip (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b :=
  exists_morseStrip_proof I f hf hab hcompact hreg

end DifferentialGeometry.Topology
