module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

@[expose] public section

/-! # Concrete cycles and boundaries of the original singular complex -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Positive-degree cycles in the actual singular chain group. -/
abbrev integralSingularCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom

/-- Use the original kernel's scalar action explicitly, avoiding the fallback
integer action on an arbitrary additive group during elaboration. -/
instance integralSingularCyclesModule (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module ℤ (integralSingularCycles n X) :=
  (LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom).module

/-- The actual next boundary lands in the preceding cycles by d squared zero. -/
def integralSingularBoundaryToCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X (n + 2) →ₗ[ℤ] integralSingularCycles n X :=
  ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatToCycles

/-- The original categorical homology is exactly cycles modulo actual
boundaries, with no replacement homology group. -/
def integralSingularHomologyCycleEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≃+
      (integralSingularCycles n X ⧸ LinearMap.range (integralSingularBoundaryToCycles n X)) :=
  (ShortComplex.homologyMapIso ((integralSingularChains X).isoSc'
      (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv

/-- Vanishing is equivalent to every actual cycle being the boundary of an
actual chain in the same original complex. This is the concrete criterion
used to construct the missing low-degree topology proofs. -/
theorem integralSingularHomology_vanishing_iff (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Subsingleton (integralSingularHomology (n + 1) X) ↔
      ∀ c : (integralSingularChains X).X (n + 1),
        (integralSingularChains X).d (n + 1) n c = 0 →
          ∃ b : (integralSingularChains X).X (n + 2),
            (integralSingularChains X).d (n + 2) (n + 1) b = c := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

end DifferentialGeometry.Topology
