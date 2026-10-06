module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

private theorem integralSingularChainMap_empty_eq_zero
    (X : Type u) [TopologicalSpace X] :
    integralSingularChainMap (singularSubspaceInclusion (∅ : Set X)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hc : c = 0 := by
    apply (integralSingularChainRepr n (∅ : Set X)).injective
    ext σ
    exact ((integralSingularSimplexEquiv n (∅ : Set X) σ)
      (Convexity.StdSimplex.single 0)).2.elim
  subst c
  exact map_zero _

theorem integralAbsoluteToRelative_empty_bijective
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (integralAbsoluteToRelative n (∅ : Set X)) := by
  let π := (integralRelativeChainSequence (∅ : Set X)).g
  have hπ : IsIso π := by
    change IsIso (cokernel.π (integralSingularChainMap (singularSubspaceInclusion (∅ : Set X))))
    rw [integralSingularChainMap_empty_eq_zero]
    infer_instance
  have hi : IsIso (HomologicalComplex.homologyMap π n) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

def integralAbsoluteToRelativeEmptyEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology n X ≃ₗ[ℤ] integralRelativeHomology n (∅ : Set X) :=
  LinearEquiv.ofBijective (integralAbsoluteToRelative n (∅ : Set X))
    (integralAbsoluteToRelative_empty_bijective X n)

theorem integralAbsoluteToRelativeEmptyEquiv_toLinearMap
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralAbsoluteToRelativeEmptyEquiv n X).toLinearMap =
      integralAbsoluteToRelative n (∅ : Set X) := rfl

private theorem integralSingularCochainMap_empty_eq_zero
    (X : Type u) [TopologicalSpace X] :
    integralSingularCochainMap (singularSubspaceInclusion (∅ : Set X)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (singularSubspaceInclusion (∅ : Set X)) = 0
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (singularSubspaceInclusion (∅ : Set X))).f n c) = 0
  rw [integralSingularChainMap_empty_eq_zero]
  exact map_zero φ

theorem integralRelativeToAbsoluteCohomology_empty_bijective
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Function.Bijective (integralRelativeToAbsoluteCohomology n (∅ : Set X)) := by
  let ι := integralRelativeCochainInclusion (∅ : Set X)
  have hι : IsIso ι := by
    change IsIso (kernel.ι (integralSingularCochainMap (singularSubspaceInclusion (∅ : Set X))))
    rw [integralSingularCochainMap_empty_eq_zero]
    infer_instance
  have hi : IsIso (HomologicalComplex.homologyMap ι n) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

def integralRelativeToAbsoluteCohomologyEmptyEquiv
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralRelativeCohomology n (∅ : Set X) ≃ₗ[ℤ] integralSingularCohomology n X :=
  LinearEquiv.ofBijective (integralRelativeToAbsoluteCohomology n (∅ : Set X))
    (integralRelativeToAbsoluteCohomology_empty_bijective X n)

theorem integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap
    (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralRelativeToAbsoluteCohomologyEmptyEquiv n X).toLinearMap =
      integralRelativeToAbsoluteCohomology n (∅ : Set X) := rfl

end DifferentialGeometry.Topology

end
