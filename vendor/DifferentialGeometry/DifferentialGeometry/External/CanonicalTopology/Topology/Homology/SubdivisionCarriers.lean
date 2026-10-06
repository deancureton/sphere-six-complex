module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SingularSubdivisionNaturality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallChains

@[expose] public section

/-! # Subdivision and its homotopy preserve the same original carriers -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Full singular subdivision preserves every actual subspace carrier. -/
theorem integralSingularSubdivision_mem (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivision n c ∈ integralSingularChainsIn n A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨integralSingularSubdivision n b, (integralSingularSubdivision_map n _ b).symm⟩

/-- The SAME full homotopy preserves every actual subspace carrier. -/
theorem integralSingularSubdivisionHomotopy_mem (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivisionHomotopy n c ∈ integralSingularChainsIn (n + 1) A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨integralSingularSubdivisionHomotopy n b, (integralSingularSubdivisionHomotopy_map n _ b).symm⟩

/-- Subdivision of an original small chain is small for the same family. -/
theorem integralSingularSubdivision_small (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivision n c ∈ integralSingularSmallChains n U := by
  have h : integralSingularSmallChains n U ≤
      Submodule.comap (integralSingularSubdivision n) (integralSingularSmallChains n U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularSubdivision_mem n (U i) hb)
  exact h hc

/-- The SAME homotopy on an original small chain is small for the same family. -/
theorem integralSingularSubdivisionHomotopy_small (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivisionHomotopy n c ∈ integralSingularSmallChains (n + 1) U := by
  have h : integralSingularSmallChains n U ≤
      Submodule.comap (integralSingularSubdivisionHomotopy n) (integralSingularSmallChains (n + 1) U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularSubdivisionHomotopy_mem n (U i) hb)
  exact h hc

end DifferentialGeometry.Topology
