module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionSmallness
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallComplex

@[expose] public section

/-! # Small representatives and small bounding chains in the original complex -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Every original positive-degree cycle has an actual small cycle
representative, with an explicit original chain bounding their difference. -/
theorem exists_small_cycle_representative (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : (integralSingularChains X).X (n + 1)) (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    ∃ s : (integralSingularChains X).X (n + 1), s ∈ integralSingularSmallChains (n + 1) U ∧
      (integralSingularChains X).d (n + 1) n s = 0 ∧
        ∃ b : (integralSingularChains X).X (n + 2), (integralSingularChains X).d (n + 2) (n + 1) b = c - s := by
  obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small (n + 1) U hU hcover c
  refine ⟨integralSingularSubdivisionIterate (n + 1) k c, hk k le_rfl, ?_,
    integralSingularSubdivisionIterateHomotopy (n + 1) k c,
    integralSingularSubdivisionIterateHomotopy_cycle n k c hc⟩
  rw [integralSingularSubdivisionIterate_boundary, hc, map_zero]

/-- If an actual small positive-degree cycle bounds in the original
complex, it bounds an actual SMALL chain for the SAME cover. -/
theorem exists_small_boundary_of_boundary (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : (integralSingularChains X).X (n + 1)) (hsmall : c ∈ integralSingularSmallChains (n + 1) U)
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    (b : (integralSingularChains X).X (n + 2)) (hb : (integralSingularChains X).d (n + 2) (n + 1) b = c) :
    ∃ a : (integralSingularChains X).X (n + 2), a ∈ integralSingularSmallChains (n + 2) U ∧
      (integralSingularChains X).d (n + 2) (n + 1) a = c := by
  obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small (n + 2) U hU hcover b
  refine ⟨integralSingularSubdivisionIterate (n + 2) k b +
    integralSingularSubdivisionIterateHomotopy (n + 1) k c,
    Submodule.add_mem _ (hk k le_rfl) (integralSingularSubdivisionIterateHomotopy_small (n + 1) k U hsmall), ?_⟩
  rw [map_add, integralSingularSubdivisionIterate_boundary, hb,
    integralSingularSubdivisionIterateHomotopy_cycle n k c hc]
  abel

/-- Every original degree-zero subdivision is exactly the identity. -/
theorem integralSingularSubdivisionIterate_zero (k : ℕ) :
    integralSingularSubdivisionIterate (X := X) 0 k = LinearMap.id := by
  unfold integralSingularSubdivisionIterate
  rw [integralSingularSubdivision_zero]
  exact one_pow k

/-- Every original zero-chain is already small for an actual open cover. -/
theorem integralSingularSmallChains_zero_all (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : (integralSingularChains X).X 0) : c ∈ integralSingularSmallChains 0 U := by
  obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small 0 U hU hcover c
  have h := hk k le_rfl
  rwa [integralSingularSubdivisionIterate_zero, LinearMap.id_apply] at h

/-- A zero-chain bounding in the original complex has an actual small
bounding one-chain for the same open cover. -/
theorem exists_small_zero_boundary_of_boundary (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : (integralSingularChains X).X 0)
    (b : (integralSingularChains X).X 1) (hb : (integralSingularChains X).d 1 0 b = c) :
    ∃ a : (integralSingularChains X).X 1, a ∈ integralSingularSmallChains 1 U ∧
      (integralSingularChains X).d 1 0 a = c := by
  obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small 1 U hU hcover b
  refine ⟨integralSingularSubdivisionIterate 1 k b, hk k le_rfl, ?_⟩
  rw [integralSingularSubdivisionIterate_boundary 0, hb, integralSingularSubdivisionIterate_zero,
    LinearMap.id_apply]

end DifferentialGeometry.Topology
