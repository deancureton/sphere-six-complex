module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev integerCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

example : Abelian (ModuleCat.{u} ℤ) := inferInstance
example : HasCoproducts.{u} (ModuleCat.{u} ℤ) := inferInstance
example : CategoryWithHomology (ModuleCat.{u} ℤ) := inferInstance
instance : TopCat.toSSet.{u}.PreservesMonomorphisms := inferInstance

variable (R : ModuleCat.{u} ℤ)

abbrev singularChainFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj R

abbrev singularChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ := (singularChainFunctor R).obj X

abbrev singularHomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).obj X

example (X : TopCat.{u}) (n : ℕ) : singularHomology R X n = (singularChains R X).homology n := rfl
example (X : TopCat.{u}) : singularChains R X = (TopCat.toSSet.obj X).chainComplex R := rfl

def incl (X : TopCat.{u}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance (X : TopCat.{u}) (A : Set X) : Mono (incl X A) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

abbrev singSub (X : TopCat.{u}) (A : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (incl X A))

lemma mem_singSub_iff (X : TopCat.{u}) (A : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (singSub X A).obj n ↔ Set.range (X.toSSetObjEquiv n σ) ⊆ A := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨x, rfl⟩
    exact ((TopCat.of A).toSSetObjEquiv n τ x).2
  · intro h
    refine ⟨(TopCat.toSSetObjEquiv _ n).symm ⟨fun x => ⟨X.toSSetObjEquiv n σ x, h ⟨x, rfl⟩⟩,
      by fun_prop⟩, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext x
    rfl

def pair (X : TopCat.{u}) (A : Set X) : SSetPair.{u} :=
  SSetPair.of (TopCat.toSSet.map (incl X A))

abbrev relativeHomology (X : TopCat.{u}) (A : Set X) (n : ℕ) : ModuleCat.{u} ℤ :=
  (pair X A).homology R n

example (X : TopCat.{u}) (A : Set X) (n : ℕ) : (pair X A).right.homology R n = singularHomology R X n := rfl
example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (pair X A).left.homology R n = singularHomology R (TopCat.of A) n := rfl

abbrev inclMap (X : TopCat.{u}) (A : Set X) (n : ℕ) : singularHomology R (TopCat.of A) n ⟶ singularHomology R X n :=
  SSet.homologyMap (pair X A).hom R n

example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = homologyMap ((singularChainFunctor R).map (incl X A)) n := rfl

abbrev relπ (X : TopCat.{u}) (A : Set X) (n : ℕ) : singularHomology R X n ⟶ relativeHomology R X A n :=
  (pair X A).homologyπ R n

abbrev δ (X : TopCat.{u}) (A : Set X) (n : ℕ) : relativeHomology R X A (n + 1) ⟶ singularHomology R (TopCat.of A) n :=
  (pair X A).homologyδ R (n + 1) n rfl

theorem les_exact₁ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (δ R X A n) (inclMap R X A n)
      ((pair X A).homologyδ_comp R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₁ R (n + 1) n rfl

theorem les_exact₂ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (inclMap R X A n) (relπ R X A n)
      ((pair X A).homologyMap_hom_homologyπ R n :)).Exact :=
  (pair X A).homology_exact₂ R n

theorem les_exact₃ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relπ R X A (n + 1)) (δ R X A n)
      ((pair X A).comp_homologyδ R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₃ R (n + 1) n rfl

def pairMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    pair X A ⟶ pair Y B :=
  SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom ⟨hf.restrict, by fun_prop⟩))
    (TopCat.toSSet.map f)
    (by
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map (incl Y B) =
        TopCat.toSSet.map (incl X A) ≫ TopCat.toSSet.map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

abbrev relativeHomologyMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (n : ℕ) : relativeHomology R X A n ⟶ relativeHomology R Y B n :=
  SSetPair.homologyMap (pairMap f hf) R n

def chainHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : HomotopyEquiv (singularChains R (TopCat.of X)) (singularChains R (TopCat.of Y)) where
  hom := (singularChainFunctor R).map (TopCat.ofHom e.toFun)
  inv := (singularChainFunctor R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of X) (Y := TopCat.of X)
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (g := 𝟙 _)
      (Classical.choice e.left_inv) R).trans (Homotopy.ofEq (by simp))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (g := 𝟙 _)
      (Classical.choice e.right_inv) R).trans (Homotopy.ofEq (by simp))

def homologyIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : singularHomology R (TopCat.of X) n ≅ singularHomology R (TopCat.of Y) n :=
  haveI : IsIso (homologyMap (chainHomotopyEquiv R e).hom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  @asIso _ _ _ _ _ this

theorem isZero_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (singularHomology R (TopCat.of X) n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let e' : ContinuousMap.HomotopyEquiv X PUnit.{u + 1} :=
    e.trans (Homeomorph.homeomorphOfUnique Unit PUnit.{u + 1}).toHomotopyEquiv
  have h1 : IsZero (singularHomology R (TopCat.of PUnit.{u + 1}) n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ n R (TopCat.of PUnit.{u + 1}) hn
  have h2 : singularHomology R (TopCat.of X) n ≅ singularHomology R (TopCat.of PUnit.{u + 1}) n := homologyIso R e' n
  exact h1.of_iso h2

end DifferentialGeometry.Topology.SingularPair
