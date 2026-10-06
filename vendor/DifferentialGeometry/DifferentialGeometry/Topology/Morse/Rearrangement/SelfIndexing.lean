module

public import DifferentialGeometry.Topology.Morse.Rearrangement.Swap

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_selfIndexing (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
      (∀ x, f x ∈ Ioo a b → (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)) ∧
      (∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) := by
  obtain ⟨f₁, hmod₁, hf₁, hcrit₁, hidx₁, hinj₁⟩ := exists_distinct_critical_values I hf
  have hpre : ∀ x, f₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hinj : InjOn f₁ {x | f₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₁ x} := by
    refine hinj₁.mono fun x hx => ?_
    have hfx : f x ∈ Ioo a b := (hpre x).1 hx.1
    exact ⟨hfx, (hcrit₁ x hfx).1 hx.2⟩
  obtain ⟨g, hmod₂, hg, hself, hcrit₂, hidx₂⟩ :=
    Swap.exists_selfIndexing_of_injOn _ f₁ hf₁ hinj rfl
  refine ⟨g, hmod₁.trans hmod₂, hg, hself, fun x hx => (hcrit₂ x).trans (hcrit₁ x hx),
    fun x hx hc => ?_⟩
  rw [hidx₂ x ((hcrit₁ x hx).2 hc), hidx₁ x hx hc]

end DifferentialGeometry.Topology
