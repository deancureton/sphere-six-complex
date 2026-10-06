module

public import DifferentialGeometry.Topology.Homology.Subdivision.AffineSimplex
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem affineCone_boundary_generator {n : ℕ} (p : E) (v : Fin (n + 2) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p v)) ≫
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1) =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) -
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
          (affineSingularSimplex (Fin.cons p (v ∘ i.succAbove))) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_succ]
  simp only [δ_affineSingularSimplex, Fin.val_zero, pow_zero, one_zsmul,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove,
    Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  rfl


theorem affineCone_boundary_generator_zero (p q : E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (fun _ : Fin 1 ↦ q))) ≫
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ q)) -
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ p)) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [δ_affineSingularSimplex]
  have h₀ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (0 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ q) := rfl
  have h₁ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (1 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ p) := by
    funext i
    fin_cases i
    rfl
  rw [h₀, h₁]
  simp [sub_eq_add_neg]

def affineCone (p : E) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X (n + 1) :=
  Sigma.desc (fun σ ↦ (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
    (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))))


@[reassoc (attr := simp)]
theorem ι_affineCone (p : E) {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ affineCone R p n =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))) :=
  Sigma.ι_comp_desc _ _

theorem affineCone_boundary (p : E) (n : ℕ) :
    affineCone R p (n + 1) ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫ affineCone R p n =
        (SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_add, ← Category.assoc, ι_affineCone,
    affineCone_boundary_generator, ← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ι_affineCone,
    SSet.ι_chainComplexMap_f, singularSimplexVertices_δ]
  apply sub_add_cancel


def singularChainAugmentation :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X 0 ⟶ R :=
  Sigma.desc (fun _ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌ ↦ 𝟙 R)

omit [NormedSpace ℝ E] in
@[reassoc (attr := simp)]
theorem ι_singularChainAugmentation (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
      singularChainAugmentation (E := E) R = 𝟙 R :=
  Sigma.ι_comp_desc _ _

omit [NormedSpace ℝ E] in
theorem d_singularChainAugmentation :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 ≫
      singularChainAugmentation (E := E) R = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Preadditive.add_comp, Preadditive.neg_comp,
    ι_singularChainAugmentation, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, add_neg_cancel, comp_zero]


theorem affineCone_boundary_zero (p : E) :
    affineCone R p 0 ≫ ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 =
      𝟙 _ - singularChainAugmentation (E := E) R ≫
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
            (affineSingularSimplex (fun _ : Fin 1 ↦ p)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, Preadditive.comp_sub, Category.comp_id]
  have hσ : singularSimplexVertices σ = (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) := by
    funext i
    fin_cases i
    rfl
  rw [hσ, affineCone_boundary_generator_zero]
  have hpoint : affineSingularSimplex (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) = σ := by
    rw [← hσ]
    exact affineSingularSimplex_vertices_zero σ
  rw [hpoint]
  rw [← Category.assoc, ι_singularChainAugmentation, Category.id_comp]


theorem affineStraightening_f_zero :
    (SSet.chainComplexMap (affineStraightening (E := E)) R).f 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SSet.ι_chainComplexMap_f, Category.comp_id]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      (affineSingularSimplex (singularSimplexVertices σ)) = _
  rw [affineSingularSimplex_vertices_zero]


theorem affineCone_straightening (p : E) (n : ℕ) :
    affineCone R p n ≫ (SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1) =
      affineCone R p n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    affineStraightening_affineSingularSimplex]


theorem straightening_affineCone (p : E) (n : ℕ) :
    (SSet.chainComplexMap (affineStraightening (E := E)) R).f n ≫ affineCone R p n =
      affineCone R p n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ι_affineCone, ι_affineCone]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      (affineSingularSimplex (Fin.cons p
        (singularSimplexVertices (affineSingularSimplex (singularSimplexVertices σ))))) = _
  rw [singularSimplexVertices_affineSingularSimplex]

end DifferentialGeometry.Homology
