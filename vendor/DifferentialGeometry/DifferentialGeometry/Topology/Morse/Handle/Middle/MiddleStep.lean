module

public import DifferentialGeometry.Topology.Morse.Cancellation.FirstCancellation
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing
public import DifferentialGeometry.Topology.Morse.Handle.Middle.Cancellation

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_middle_cancel_step (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a})))
    {p₀ : M} (hp₀ : f p₀ ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p₀) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x →
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∧ morseIndex I g x = morseIndex I f x) ∧
      ∃ p, f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := by
  exact middle_target I h6 hf hidx hV₀ hV₁ hH hp₀

end DifferentialGeometry.Topology
