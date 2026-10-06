module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossingField

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_cancel_pair (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a' b' : ℝ} {p q : M} (h : isCancellingPair I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  obtain ⟨V', hV'⟩ := exists_crossing_field I h
  exact exists_modification_of_crossing I h.1 hV'

theorem exists_cancel_pair_strip_of_isCancellingPair (I : ModelWithCorners ℝ (Fin n → ℝ) H)
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {p q : M}
    (h : isCancellingPair I f a' b' p q) :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
        (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x)) ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  obtain ⟨g, hmod, hg, hno⟩ := exists_cancel_pair I h
  obtain ⟨hgs, hoff⟩ := hmod.morseStrip_of_substrip hf ha hb hreg hg
  exact ⟨g, hmod, hmod.mono ha hb, hgs, fun x hx =>
    ⟨(hoff x hx).1, (hoff x hx).2.1, fun h => ((hoff x hx).2.2 h).2⟩, hno⟩

end DifferentialGeometry.Topology
