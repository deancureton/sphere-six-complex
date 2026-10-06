module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cochains

@[expose] public section

/-! # Actual pullback of integral singular cochains -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original singular chain functor preserves the actual identity map. -/
theorem integralSingularChainMap_id : integralSingularChainMap (.id X) = 𝟙 _ :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map_id
    (TopCat.of X)

/-- Pullback evaluates each original cochain on the original image chain. -/
def integralSingularCochainPullback (n : ℕ) (f : C(X, Y)) :
    integralSingularCochain n Y →ₗ[ℤ] integralSingularCochain n X where
  toFun φ := φ.comp ((integralSingularChainMap f).f n).hom
  map_add' φ ψ := by ext c; rfl
  map_smul' k φ := by ext c; rfl

/-- Pullback is an actual morphism of the original integral cochain complexes. -/
def integralSingularCochainMap (f : C(X, Y)) :
    integralSingularCochains Y ⟶ integralSingularCochains X where
  f n := ModuleCat.ofHom (integralSingularCochainPullback n f)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    change (integralSingularCoboundary X i j).comp (integralSingularCochainPullback i f) =
      (integralSingularCochainPullback j f).comp (integralSingularCoboundary Y i j)
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChainMap f).f i ((integralSingularChains X).d j i c)) =
      φ ((integralSingularChains Y).d j i ((integralSingularChainMap f).f j c))
    exact congrArg φ (congrArg (fun g : (integralSingularChains X).X j ⟶
      (integralSingularChains Y).X i => g c) ((integralSingularChainMap f).comm j i)).symm

/-- The actual identity induces identity on the full cochain complex. -/
theorem integralSingularCochainMap_id : integralSingularCochainMap (.id X) = 𝟙 _ := by
  ext n : 1
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (.id X) = LinearMap.id
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (.id X)).f n c) = φ c
  rw [integralSingularChainMap_id]
  rfl

/-- Pullback reverses the original composition. -/
theorem integralSingularCochainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularCochainMap (g.comp f) =
      integralSingularCochainMap g ≫ integralSingularCochainMap f := by
  ext n : 1
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (g.comp f) =
    (integralSingularCochainPullback n f).comp (integralSingularCochainPullback n g)
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (g.comp f)).f n c) =
    φ ((integralSingularChainMap g).f n ((integralSingularChainMap f).f n c))
  rw [integralSingularChainMap_comp]
  rfl

/-- The cohomology map is induced by that same cochain pullback. -/
def integralSingularCohomologyMap (n : ℕ) (f : C(X, Y)) :
    integralSingularCohomology n Y →ₗ[ℤ] integralSingularCohomology n X :=
  (HomologicalComplex.homologyMap (integralSingularCochainMap f) n).hom

/-- Identity on the original space induces identity on its cohomology. -/
theorem integralSingularCohomologyMap_id (n : ℕ) :
    integralSingularCohomologyMap n (.id X) = LinearMap.id := by
  unfold integralSingularCohomologyMap
  rw [integralSingularCochainMap_id, HomologicalComplex.homologyMap_id]
  rfl

/-- The induced cohomology maps obey the actual contravariant composition law. -/
theorem integralSingularCohomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularCohomologyMap n (g.comp f) =
      (integralSingularCohomologyMap n f).comp (integralSingularCohomologyMap n g) := by
  unfold integralSingularCohomologyMap
  rw [integralSingularCochainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

end DifferentialGeometry.Topology
