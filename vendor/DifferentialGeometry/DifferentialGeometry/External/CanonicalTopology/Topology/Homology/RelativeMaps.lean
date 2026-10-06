module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

/-! # Naturality for the original pairs and their actual singular complexes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original chain functor respects composition of actual continuous maps. -/
theorem integralSingularChainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularChainMap (g.comp f) = integralSingularChainMap f ≫ integralSingularChainMap g :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map_comp
    (TopCat.ofHom f) (TopCat.ofHom g)

/-- Restrict the original pair map to the original subspaces. -/
def singularPairRestriction (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x.val, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The inclusion square commutes on the original chain maps. -/
theorem integralSingularChainMap_pair_square (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralSingularChainMap (singularSubspaceInclusion A) ≫ integralSingularChainMap f =
      integralSingularChainMap (singularPairRestriction f hf) ≫
        integralSingularChainMap (singularSubspaceInclusion B) := by
  rw [← integralSingularChainMap_comp, ← integralSingularChainMap_comp]
  rfl

/-- The same commuting square induces the actual map of quotient complexes. -/
def integralRelativeChainMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeChains A ⟶ integralRelativeChains B :=
  cokernel.map _ _ (integralSingularChainMap (singularPairRestriction f hf))
    (integralSingularChainMap f) (integralSingularChainMap_pair_square f hf)

/-- All three maps form a morphism of the original short exact sequences. -/
def integralRelativeSequenceMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeChainSequence A ⟶ integralRelativeChainSequence B where
  τ₁ := integralSingularChainMap (singularPairRestriction f hf)
  τ₂ := integralSingularChainMap f
  τ₃ := integralRelativeChainMap f hf
  comm₁₂ := (integralSingularChainMap_pair_square f hf).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The induced relative homology map is the map on these same quotient complexes. -/
def integralRelativeHomologyMap (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeHomology n A →ₗ[ℤ] integralRelativeHomology n B :=
  (HomologicalComplex.homologyMap (integralRelativeChainMap f hf) n).hom

/-- Absolute-to-relative maps commute with every original continuous map of pairs. -/
theorem integralAbsoluteToRelative_natural (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralAbsoluteToRelative n B).comp (integralSingularHomologyMap n f) =
      (integralRelativeHomologyMap n f hf).comp (integralAbsoluteToRelative n A) := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralRelativeSequenceMap f hf).comm₂₃
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h

/-- The actual connecting homomorphism is natural for the same original pair
maps, from the pinned proved snake-map naturality theorem. -/
theorem integralRelativeConnecting_natural (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralSingularHomologyMap n (singularPairRestriction f hf)).comp (integralRelativeConnecting n A) =
      (integralRelativeConnecting n B).comp (integralRelativeHomologyMap (n + 1) f hf) := by
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (integralRelativeSequenceMap f hf)
      (integralRelativeChainSequence_shortExact A) (integralRelativeChainSequence_shortExact B)
        (n + 1) n (by simp))

open Set in
theorem integralRelativeHomologyMap_eq_of_restriction_homotopic (n : ℕ)
    [Subsingleton (integralSingularHomology (n + 1) Y)]
    (f g : ContinuousMap X Y) (A : Set X) (B : Set Y)
    (hf : MapsTo f A B) (hg : MapsTo g A B)
    (h : (singularPairRestriction f hf).Homotopic (singularPairRestriction g hg)) :
    integralRelativeHomologyMap (n + 1) f hf =
      integralRelativeHomologyMap (n + 1) g hg := by
  have hzero : integralAbsoluteToRelative (n + 1) B = 0 := by
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  have hinj : Function.Injective (integralRelativeConnecting n B) :=
    (LinearMap.injective_iff_eq_zero_of_exact (integralRelative_exact_relative n B)).mpr hzero
  have hmaps := integralSingularHomologyMap_homotopic n h
  apply LinearMap.ext
  intro a
  apply hinj
  calc
    integralRelativeConnecting n B (integralRelativeHomologyMap (n + 1) f hf a) =
        integralSingularHomologyMap n (singularPairRestriction f hf)
          (integralRelativeConnecting n A a) :=
      (LinearMap.congr_fun (integralRelativeConnecting_natural n f hf) a).symm
    _ = integralSingularHomologyMap n (singularPairRestriction g hg)
        (integralRelativeConnecting n A a) :=
      LinearMap.congr_fun hmaps (integralRelativeConnecting n A a)
    _ = integralRelativeConnecting n B (integralRelativeHomologyMap (n + 1) g hg a) :=
      LinearMap.congr_fun (integralRelativeConnecting_natural n g hg) a

end DifferentialGeometry.Topology
