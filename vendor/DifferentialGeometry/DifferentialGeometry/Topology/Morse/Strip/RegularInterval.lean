module

public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.Morse.RegularLevel.NoCriticalValues

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem regular_interval (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  obtain ⟨v, Φ, -, -, -, -, ⟨-, hflow, -⟩, hbnd, -, hbnd', -⟩ :=
    DifferentialGeometry.Topology.Morse.no_critical_value_transport (I := I) f hf hab hcompact
      (fun x hx => hreg x hx)
  refine ⟨Φ, hflow, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hbnd x hx
  · intro hy
    exact ⟨Φ.symm y, hbnd' y hy, Φ.apply_symm_apply y⟩

end DifferentialGeometry.Topology
