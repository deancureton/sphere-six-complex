module

public import DifferentialGeometry.Topology.Morse.Strip.Substrip
public import DifferentialGeometry.Topology.Morse.Cancellation.CancelIndexZero

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ} {crit : Finset M}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

theorem exists_cancel_pair_index_zero [DecidableEq M]
    {a' b' : ℝ} (hf : MorseStrip I f a' b') {p q : M}
    (D : GradientLikeStrip I f a' b' {p, q})
    (hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hp : p ∈ ({p, q} : Finset M)) (hq : q ∈ ({p, q} : Finset M)) {ε : ℝ} (hε : 0 < ε)
    (hgood : goodPair D ε p q hp hq)
    (hcst : ∀ p' hp', (D.chart p' hp').r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p' hp' ^ 2)
    (hlt : f p + 2 * ε < f q)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ MorseStrip I g a' b' ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  exact IndexZeroCancellingPair.main ⟨hf, D, hcrit, hp, hq, ε, hε, hgood, hcst, hlt, hlev⟩

theorem exists_cancel_pair_strip [DecidableEq M]
    (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hf' : MorseStrip I f a' b') {p q : M}
    (D : GradientLikeStrip I f a' b' {p, q})
    (hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hp : p ∈ ({p, q} : Finset M)) (hq : q ∈ ({p, q} : Finset M)) {ε : ℝ} (hε : 0 < ε)
    (hgood : goodPair D ε p q hp hq)
    (hcst : ∀ p' hp', (D.chart p' hp').r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p' hp' ^ 2)
    (hlt : f p + 2 * ε < f q)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ g : M → ℝ, ModifiedWithin f a' b' g ∧ ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
        (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x)) ∧
      ∀ x, g x ∈ Ioo a' b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
  obtain ⟨g, hmod, hg, hno⟩ :=
    exists_cancel_pair_index_zero hf' D hcrit hp hq hε hgood hcst hlt hlev
  obtain ⟨hgs, hoff⟩ := hmod.morseStrip_of_substrip hf ha hb hreg hg
  exact ⟨g, hmod, hmod.mono ha hb, hgs, fun x hx =>
    ⟨(hoff x hx).1, (hoff x hx).2.1, fun h => ((hoff x hx).2.2 h).2⟩, hno⟩

end GradientLikeStrip

end DifferentialGeometry.Topology
