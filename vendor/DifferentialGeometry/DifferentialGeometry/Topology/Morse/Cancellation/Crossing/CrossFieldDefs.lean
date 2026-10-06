module

public import DifferentialGeometry.Topology.Morse.Cancellation.CancellingPair

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

def isCrossingField (I : ModelWithCorners ℝ (Fin n → ℝ) H) [IsManifold I ∞ M] (f : M → ℝ)
    (a' b' : ℝ) (V' : (x : M) → TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle I M)) ∧
    IsCompact (tsupport V') ∧
    ∃ η₀ : ℝ, 0 < η₀ ∧ 2 * η₀ < b' - a' ∧
      (∀ x, f x ∈ Icc a' (a' + η₀) ∪ Icc (b' - η₀) b' → dfV I f V' x = -1) ∧
      ∀ x, f x ∈ Icc a' b' → ∀ γ : ℝ → M, γ 0 = x → IsMIntegralCurve γ V' →
        ∃ t, 0 ≤ t ∧ f (γ t) ≤ a'

end DifferentialGeometry.Topology
