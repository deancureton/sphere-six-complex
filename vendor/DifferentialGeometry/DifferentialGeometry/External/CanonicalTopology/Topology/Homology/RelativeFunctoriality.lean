module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps

@[expose] public section

/-! # Exact functoriality of the original relative singular chain maps -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original pair map acts through the SAME original quotient projection. -/
@[reassoc]
theorem integralRelativeChainMap_π (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A)) ≫ integralRelativeChainMap f hf =
      integralSingularChainMap f ≫ cokernel.π (integralSingularChainMap (singularSubspaceInclusion B)) :=
  cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Identity of the original pair induces identity on its SAME relative complex. -/
theorem integralRelativeChainMap_id (A : Set X) :
    integralRelativeChainMap (.id X) (show MapsTo (ContinuousMap.id X) A A from fun _ h => h) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A)))).mp
  rw [integralRelativeChainMap_π, integralSingularChainMap_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- An actual pair endomorphism equal to identity has the SAME identity
relative chain map, independently of the proof of its carrier condition. -/
theorem integralRelativeChainMap_eq_id (f : C(X, X)) (A : Set X)
    (hf : MapsTo f A A) (h : f = ContinuousMap.id X) : integralRelativeChainMap f hf = 𝟙 _ := by
  subst f
  exact integralRelativeChainMap_id A

set_option backward.isDefEq.respectTransparency false in
/-- Composition of actual pair maps induces composition on the SAME
original quotient complexes. -/
theorem integralRelativeChainMap_comp (f : C(X, Y)) (g : C(Y, Z))
    {A : Set X} {B : Set Y} {D : Set Z} (hf : MapsTo f A B) (hg : MapsTo g B D) :
    integralRelativeChainMap (g.comp f) (hg.comp hf) =
      integralRelativeChainMap f hf ≫ integralRelativeChainMap g hg := by
  apply (cancel_epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A)))).mp
  rw [integralRelativeChainMap_π, ← Category.assoc, integralRelativeChainMap_π_assoc, Category.assoc,
    integralRelativeChainMap_π, integralSingularChainMap_comp, Category.assoc]

/-- Identity acts as identity on the original relative homology. -/
theorem integralRelativeHomologyMap_id (n : ℕ) (A : Set X) :
    integralRelativeHomologyMap n (.id X) (show MapsTo (ContinuousMap.id X) A A from fun _ h => h) = LinearMap.id := by
  unfold integralRelativeHomologyMap
  rw [integralRelativeChainMap_id, HomologicalComplex.homologyMap_id]
  rfl

/-- Original relative homology maps compose through the SAME middle pair. -/
theorem integralRelativeHomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    {A : Set X} {B : Set Y} {D : Set Z} (hf : MapsTo f A B) (hg : MapsTo g B D) :
    integralRelativeHomologyMap n (g.comp f) (hg.comp hf) =
      (integralRelativeHomologyMap n g hg).comp (integralRelativeHomologyMap n f hf) := by
  unfold integralRelativeHomologyMap
  rw [integralRelativeChainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

end DifferentialGeometry.Topology
