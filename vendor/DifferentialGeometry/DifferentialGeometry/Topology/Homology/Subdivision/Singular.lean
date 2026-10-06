module

public import DifferentialGeometry.Topology.Homology.Subdivision.Universal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) (X : TopCat.{u})


def singularSimplexMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    SimplexCategory.toTop.obj ⦋n⦌ ⟶ X := σ.down

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj X) R


@[reassoc]
theorem fundamentalSimplexChain_pushforward {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    fundamentalSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl

private theorem pushforward_face {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    SSet.chainComplexMap (TopCat.toSSet.map
        (SimplexCategory.toTop.map (SimplexCategory.δ i))) R ≫
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X ((TopCat.toSSet.obj X).δ i σ))) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp]
  rfl


def singularSubdivisionMap (n : ℕ) : (K).X n ⟶ (K).X n :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ barycentricSimplexChain R n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)


@[reassoc]
theorem ι_singularSubdivisionMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionMap R X n =
      barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n :=
  Sigma.ι_comp_desc _ _


@[simp]
theorem singularSubdivisionMap_zero : singularSubdivisionMap R X 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionMap, barycentricSimplexChain_zero,
    fundamentalSimplexChain_pushforward, Category.comp_id]


theorem singularSubdivisionMap_comm (n : ℕ) :
    singularSubdivisionMap R X (n + 1) ≫ (K).d (n + 1) n =
      (K).d (n + 1) n ≫ singularSubdivisionMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc,
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm, ← Category.assoc, barycentricSimplexChain_boundary]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ), SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    ι_singularSubdivisionMap]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]


def singularSubdivision : (K) ⟶ (K) where
  f := singularSubdivisionMap R X
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact singularSubdivisionMap_comm R X j


@[simp]
theorem singularSubdivision_f (n : ℕ) :
    (singularSubdivision R X).f n = singularSubdivisionMap R X n := rfl


def singularSubdivisionHomotopyMap (n : ℕ) : (K).X n ⟶ (K).X (n + 1) :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ barycentricSimplexHomotopyChain R n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1))


@[reassoc]
theorem ι_singularSubdivisionHomotopyMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionHomotopyMap R X n =
      barycentricSimplexHomotopyChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1) :=
  Sigma.ι_comp_desc _ _


@[simp]
theorem singularSubdivisionHomotopyMap_zero : singularSubdivisionHomotopyMap R X 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    zero_comp, comp_zero]


theorem singularSubdivisionHomotopyMap_comm (n : ℕ) :
    singularSubdivisionMap R X (n + 1) - 𝟙 _ =
      (K).d (n + 1) n ≫ singularSubdivisionHomotopyMap R X n +
        singularSubdivisionHomotopyMap R X (n + 1) ≫ (K).d (n + 2) (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_sub, ι_singularSubdivisionMap, Category.comp_id,
    ← fundamentalSimplexChain_pushforward R X σ, ← Preadditive.sub_comp,
    barycentricSimplexHomotopyChain_boundary, Preadditive.add_comp, Preadditive.comp_add,
    fundamentalSimplexChain_pushforward]
  congr 1
  · rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
      ι_singularSubdivisionHomotopyMap]
    apply Finset.sum_congr rfl
    intro i _
    have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) (n + 1)
    simp only [HomologicalComplex.comp_f] at h
    rw [h]
  · rw [Category.assoc, ← (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm]
    rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
      ι_singularSubdivisionHomotopyMap, Category.assoc]


def singularSubdivisionHomotopy : Homotopy (singularSubdivision R X) (𝟙 (K)) where
  hom i j := if h : i + 1 = j then
    singularSubdivisionHomotopyMap R X i ≫ eqToHom (congrArg (K).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        singularSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        singularSubdivision_f, singularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        singularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (singularSubdivisionHomotopyMap_comm R X n)


@[simp]
theorem singularSubdivisionHomotopy_hom (n : ℕ) :
    (singularSubdivisionHomotopy R X).hom n (n + 1) =
      singularSubdivisionHomotopyMap R X n := by
  change (if h : n + 1 = n + 1 then
    singularSubdivisionHomotopyMap R X n ≫ eqToHom (congrArg (K).X h) else 0) = _
  rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

variable {Y : TopCat.{u}} (f : X ⟶ Y)


theorem singularSimplexMap_naturality {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularSimplexMap Y ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) =
      singularSimplexMap X σ ≫ f := rfl

private theorem pushforward_postcomp {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap Y ((TopCat.toSSet.map f).app (op ⦋n⦌) σ))) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp, singularSimplexMap_naturality]


theorem singularSubdivisionMap_naturality (n : ℕ) :
    singularSubdivisionMap R X n ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫ singularSubdivisionMap R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
    SSet.ι_chainComplexMap_f, ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (pushforward_postcomp R X f σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]


theorem singularSubdivision_naturality :
    singularSubdivision R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ singularSubdivision R Y := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact singularSubdivisionMap_naturality R X f n


theorem singularSubdivisionHomotopyMap_naturality (n : ℕ) :
    singularSubdivisionHomotopyMap R X n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫
        singularSubdivisionHomotopyMap R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionHomotopyMap, Category.assoc]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
    SSet.ι_chainComplexMap_f, ι_singularSubdivisionHomotopyMap]
  have h := HomologicalComplex.congr_hom (pushforward_postcomp R X f σ) (n + 1)
  simp only [HomologicalComplex.comp_f] at h
  rw [h]

end DifferentialGeometry.Homology
