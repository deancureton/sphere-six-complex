module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TriangleFilling

@[expose] public section

/-! # Path cones in the actual original integral singular complex -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Extend the actual chosen paths from a to vertices linearly on the
original singular degree-zero basis. -/
def integralSingularConeZero (a : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 1) ℕ (fun σ =>
    integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))

/-- On each original vertex this is its same chosen path chain. -/
theorem integralSingularConeZero_simplex (a : X) (σ : integralSingularSimplex 0 X) :
    integralSingularConeZero a (integralSimplexChain 0 σ) =
      integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

/-- A selected actual triangle fills the original singular edge together
with its two original chosen vertex paths. -/
def integralSingularConeTriangle (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularSimplex 2 X :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose

/-- This selected triangle has the exact original signed boundary. -/
theorem integralSingularConeTriangle_boundary (a : X) (σ : integralSingularSimplex 1 X) :
    (integralSingularChains X).d 2 1 (integralSimplexChain 2 (integralSingularConeTriangle a σ)) =
      integralSimplexChain 1 σ -
        integralSingularConeZero a (integralSimplexChain 0
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) +
        integralSingularConeZero a (integralSimplexChain 0
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) := by
  have h (i : Fin 3) :
      (TopCat.toSSet.obj (TopCat.of X)).δ i (integralSingularConeTriangle a σ) =
        ![integralPathSimplex (integralSimplexPath σ),
          integralPathSimplex (PathConnectedSpace.somePath a
            (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))),
          integralPathSimplex (PathConnectedSpace.somePath a
            (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)))] i :=
    (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
      (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose_spec i
  rw [integralSimplexChain_boundary_two, h 0, h 1, h 2]
  change integralPathChain (integralSimplexPath σ) -
      integralPathChain (PathConnectedSpace.somePath a _) +
      integralPathChain (PathConnectedSpace.somePath a _) = _
  rw [integralPathChain_simplexPath, integralSingularConeZero_simplex,
    integralSingularConeZero_simplex]

/-- Extend those same actual triangles linearly on the original edge basis. -/
def integralSingularConeOne (a : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 2 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 2) ℕ (fun σ =>
    integralSimplexChain 2 (integralSingularConeTriangle a σ))

/-- No replacement of an original basis edge occurs in linear extension. -/
theorem integralSingularConeOne_simplex (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularConeOne a (integralSimplexChain 1 σ) =
      integralSimplexChain 2 (integralSingularConeTriangle a σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

/-- The actual degree-one cone equation, for the original singular
boundary operators and original integral chain groups. -/
theorem integralSingularConeOne_equation (a : X) :
    ((integralSingularChains X).d 2 1).hom.comp (integralSingularConeOne a) =
      LinearMap.id - (integralSingularConeZero a).comp ((integralSingularChains X).d 1 0).hom := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    integralSingularConeOne_simplex, integralSingularConeTriangle_boundary,
    integralSimplexChain_boundary_one, map_sub]
  abel

/-- Every actual singular 1-cycle is bounded by the same constructed cone. -/
theorem integralSingularConeOne_bounds (a : X) (c : (integralSingularChains X).X 1)
    (hc : (integralSingularChains X).d 1 0 c = 0) :
    (integralSingularChains X).d 2 1 (integralSingularConeOne a c) = c := by
  have h := LinearMap.congr_fun (integralSingularConeOne_equation a) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hc, map_zero, sub_zero] using h

/-- First integral singular homology vanishes for every simply connected
space, proved by actual triangle fillings of its original chains. -/
theorem integralSingularHomology_one_subsingleton :
    Subsingleton (integralSingularHomology 1 X) := by
  apply (integralSingularHomology_vanishing_iff 0 X).mpr
  intro c hc
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨integralSingularConeOne a c, integralSingularConeOne_bounds a c hc⟩

end DifferentialGeometry.Topology
