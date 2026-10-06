module

public import DifferentialGeometry.Topology.Homology.Subdivision.Singular

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

local notation "A" => smallSingularSimplices X U


def smallSingularSimplexPushforward {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌) ⟶ (A : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularSimplexMap X σ.val)) (by
    intro m τ hτ
    obtain ⟨ρ, rfl⟩ := hτ
    obtain ⟨i, hi⟩ := σ.property
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨((SimplexCategory.toTop.obj ⦋n⦌).toSSetObjEquiv m ρ z).down, rfl⟩)


@[reassoc (attr := simp)]
theorem smallSingularSimplexPushforward_ι {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    smallSingularSimplexPushforward X U σ ≫ (A).ι =
      TopCat.toSSet.map (singularSimplexMap X σ.val) := rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "KA" => _root_.SSet.chainComplex (A : SSet) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj X) R
local notation "I" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A)) R

private theorem smallPushforward_inclusion {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R ≫ (I) =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ.val)) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, smallSingularSimplexPushforward_ι]


def smallSingularSubdivisionMap (n : ℕ) : (KA).X n ⟶ (KA).X n :=
  Sigma.desc (fun σ : (A : SSet) _⦋n⦌ ↦ barycentricSimplexChain R n ≫
    (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n)


@[reassoc]
theorem ι_smallSingularSubdivisionMap {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallSingularSubdivisionMap X U R n =
      barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n :=
  Sigma.ι_comp_desc _ _


theorem smallSingularSubdivisionMap_inclusion (n : ℕ) :
    smallSingularSubdivisionMap X U R n ≫ (I).f n =
      (I).f n ≫ singularSubdivisionMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionMap, Category.assoc,
    ← Category.assoc ((A : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl


def smallSingularSubdivisionHomotopyMap (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  Sigma.desc (fun σ : (A : SSet) _⦋n⦌ ↦ barycentricSimplexHomotopyChain R n ≫
    (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1))


@[reassoc]
theorem ι_smallSingularSubdivisionHomotopyMap {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallSingularSubdivisionHomotopyMap X U R n =
      barycentricSimplexHomotopyChain R n ≫
        (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1) :=
  Sigma.ι_comp_desc _ _


theorem smallSingularSubdivisionHomotopyMap_inclusion (n : ℕ) :
    smallSingularSubdivisionHomotopyMap X U R n ≫ (I).f (n + 1) =
      (I).f n ≫ singularSubdivisionHomotopyMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionHomotopyMap, Category.assoc,
    ← Category.assoc ((A : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionHomotopyMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) (n + 1)
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl

theorem SingularSupport.smallSingularSubdivision_comm (n : ℕ) :
    smallSingularSubdivisionMap X U R (n + 1) ≫ (KA).d (n + 1) n =
      (KA).d (n + 1) n ≫ smallSingularSubdivisionMap X U R n := by
  have : Mono ((I).f n) := mono_smallChainMap_f X U R n
  apply (cancel_mono ((I).f n)).mp
  simp only [Category.assoc]
  rw [← (I).comm, ← Category.assoc, smallSingularSubdivisionMap_inclusion,
    Category.assoc, singularSubdivisionMap_comm, smallSingularSubdivisionMap_inclusion]
  rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
  simp only [Category.assoc]


def smallSingularSubdivision : (KA) ⟶ (KA) where
  f := smallSingularSubdivisionMap X U R
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact SingularSupport.smallSingularSubdivision_comm X U R j


@[simp]
theorem smallSingularSubdivision_f (n : ℕ) :
    (smallSingularSubdivision X U R).f n = smallSingularSubdivisionMap X U R n := rfl


theorem smallSingularSubdivision_inclusion :
    smallSingularSubdivision X U R ≫ (I) = (I) ≫ singularSubdivision R X := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact smallSingularSubdivisionMap_inclusion X U R n

theorem SingularSupport.smallSingularSubdivisionHomotopy_comm (n : ℕ) :
    smallSingularSubdivisionMap X U R (n + 1) - 𝟙 _ =
      (KA).d (n + 1) n ≫ smallSingularSubdivisionHomotopyMap X U R n +
        smallSingularSubdivisionHomotopyMap X U R (n + 1) ≫ (KA).d (n + 2) (n + 1) := by
  have : Mono ((I).f (n + 1)) := mono_smallChainMap_f X U R (n + 1)
  apply (cancel_mono ((I).f (n + 1))).mp
  calc
    _ = (I).f (n + 1) ≫ (singularSubdivisionMap R X (n + 1) - 𝟙 _) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, smallSingularSubdivisionMap_inclusion]
    _ = _ := by
      rw [singularSubdivisionHomotopyMap_comm, Preadditive.comp_add, Preadditive.add_comp]
      simp only [Category.assoc]
      rw [smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← (I).comm, ← Category.assoc (smallSingularSubdivisionHomotopyMap X U R (n + 1)),
        smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
      simp only [Category.assoc]


@[simp]
theorem smallSingularSubdivisionMap_zero : smallSingularSubdivisionMap X U R 0 = 𝟙 _ := by
  have : Mono ((I).f 0) := mono_smallChainMap_f X U R 0
  apply (cancel_mono ((I).f 0)).mp
  rw [smallSingularSubdivisionMap_inclusion, singularSubdivisionMap_zero,
    Category.id_comp, Category.comp_id]


@[simp]
theorem smallSingularSubdivisionHomotopyMap_zero :
    smallSingularSubdivisionHomotopyMap X U R 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_smallSingularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    zero_comp, comp_zero]


def smallSingularSubdivisionHomotopy : Homotopy (smallSingularSubdivision X U R) (𝟙 (KA)) where
  hom i j := if h : i + 1 = j then
    smallSingularSubdivisionHomotopyMap X U R i ≫ eqToHom (congrArg (KA).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        smallSingularSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        smallSingularSubdivision_f, smallSingularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        smallSingularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (SingularSupport.smallSingularSubdivisionHomotopy_comm X U R n)


@[simp]
theorem smallSingularSubdivisionHomotopy_hom (n : ℕ) :
    (smallSingularSubdivisionHomotopy X U R).hom n (n + 1) =
      smallSingularSubdivisionHomotopyMap X U R n := by
  change (if h : n + 1 = n + 1 then
    smallSingularSubdivisionHomotopyMap X U R n ≫ eqToHom (congrArg (KA).X h) else 0) = _
  rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

end DifferentialGeometry.Homology
