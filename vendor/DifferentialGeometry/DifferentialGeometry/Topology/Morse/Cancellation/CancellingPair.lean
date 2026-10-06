module

public import DifferentialGeometry.Topology.Morse.Cancellation.CancelPair

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem mem_pair_left {α : Type*} [DecidableEq α] (p q : α) : p ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_self p {q}

theorem mem_pair_right {α : Type*} [DecidableEq α] (p q : α) : q ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self q)

def isCancellingPair (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [DecidableEq M] (f : M → ℝ) (a' b' : ℝ) (p q : M) : Prop :=
  MorseStrip I f a' b' ∧
    (∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
    f p < f q ∧ morseIndex I f q = morseIndex I f p + 1 ∧
    ∃ D : GradientLikeStrip I f a' b' {p, q}, ∃ ε c : ℝ, 0 < ε ∧
      (D.chart p (mem_pair_left p q)).r₀ ^ 2 < 2 * ε ∧
      (D.chart q (mem_pair_right p q)).r₀ ^ 2 < 2 * ε ∧
      8 * ε < D.rm p (mem_pair_left p q) ^ 2 ∧ 8 * ε < D.rm q (mem_pair_right p q) ^ 2 ∧
      f p + ε < c ∧ c < f q - ε ∧
      (∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') ∧
      ∃ w₀ ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q),
        D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w₀ = 0 ∧
        (∀ w ∈ D.sardDom p (mem_pair_right p q) ε c ε (mem_pair_left p q),
          D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q) w = 0 →
            ∃ t : ℝ, 0 < t ∧ w = t • w₀) ∧
        Function.Surjective
          (fderiv ℝ (D.sardMap p (mem_pair_right p q) ε c ε (mem_pair_left p q)) w₀)

end DifferentialGeometry.Topology
