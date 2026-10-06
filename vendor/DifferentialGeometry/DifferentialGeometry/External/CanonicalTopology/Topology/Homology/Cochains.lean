module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

@[expose] public section

/-! # Integral singular cochains on the same original chain complex

Cochains are actual integer-linear functionals on the original singular
chains. Their differential is precomposition with the original boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Integral cochains are actual linear maps on the original chain groups. -/
abbrev integralSingularCochain (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (integralSingularChains X).X n →ₗ[ℤ] integralSingularCoefficients.{u}

/-- The actual coboundary, by precomposition with the original boundary. -/
def integralSingularCoboundary (X : Type u) [TopologicalSpace X] (i j : ℕ) :
    integralSingularCochain i X →ₗ[ℤ] integralSingularCochain j X where
  toFun φ := φ.comp ((integralSingularChains X).d j i).hom
  map_add' φ ψ := by ext c; rfl
  map_smul' k φ := by ext c; rfl

/-- The integral singular cochain complex of the original space. -/
def integralSingularCochains (X : Type u) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (integralSingularCochain n X)
  d i j := ModuleCat.ofHom (integralSingularCoboundary X i j)
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChains X).d j i c) = 0
    rw [(integralSingularChains X).shape j i h]
    exact φ.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChains X).d j i ((integralSingularChains X).d k j c)) = 0
    have h := congrArg (fun f : (integralSingularChains X).X k ⟶
      (integralSingularChains X).X i => f c) ((integralSingularChains X).d_comp_d k j i)
    change (integralSingularChains X).d j i ((integralSingularChains X).d k j c) = 0 at h
    rw [h, map_zero]

/-- Cohomology is the actual cohomology of those original integer cochains. -/
abbrev integralSingularCohomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ :=
  (integralSingularCochains X).homology n

/-- Degree-one vanishing says every original integral 1-cocycle is the
coboundary of an original integral 0-cochain. -/
theorem integralSingularCohomology_one_vanishing_iff (X : Type u) [TopologicalSpace X] :
    Subsingleton (integralSingularCohomology 1 X) ↔
      ∀ φ : integralSingularCochain 1 X, integralSingularCoboundary X 1 2 φ = 0 →
        ∃ ψ : integralSingularCochain 0 X, integralSingularCoboundary X 0 1 ψ = φ := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

end DifferentialGeometry.Topology
