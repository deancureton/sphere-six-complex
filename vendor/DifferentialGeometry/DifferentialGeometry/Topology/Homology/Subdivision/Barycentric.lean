module

public import DifferentialGeometry.Topology.Homology.Subdivision.Cone

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def singularSimplexBarycenter {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) : E :=
  Finset.univ.centerMass (fun _ : Fin (n + 1) ↦ (1 : ℝ)) (singularSimplexVertices σ)


theorem singularSimplexBarycenter_mem {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, singularSimplexVertices σ i ∈ s) :
    singularSimplexBarycenter σ ∈ s :=
  hs.centerMass_mem (fun _ _ ↦ zero_le_one)
    (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
    (fun i _ ↦ hv i)

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def affineSubdivisionMap (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
          affineSubdivisionMap n ≫ affineCone R (singularSimplexBarycenter σ) n)


@[simp]
theorem affineSubdivisionMap_zero : affineSubdivisionMap (E := E) R 0 = 𝟙 _ := rfl


@[reassoc]
theorem ι_affineSubdivisionMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ affineSubdivisionMap R (n + 1) =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
          affineSubdivisionMap R n ≫ affineCone R (singularSimplexBarycenter σ) n :=
  Sigma.ι_comp_desc _ _


theorem affineSubdivisionMap_straightening (n : ℕ) :
    affineSubdivisionMap (E := E) R n ≫
      (SSet.chainComplexMap (affineStraightening (E := E)) R).f n =
        affineSubdivisionMap R n := by
  cases n with
  | zero => rw [affineSubdivisionMap_zero, affineStraightening_f_zero, Category.id_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc, affineCone_straightening]


theorem affineSubdivisionMap_comm (n : ℕ) :
    affineSubdivisionMap (E := E) R (n + 1) ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n =
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
        affineSubdivisionMap R n := by
  induction n with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [affineSubdivisionMap_zero, Category.id_comp, Category.comp_id, Category.assoc]
    rw [affineCone_boundary_zero]
    simp only [Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc _ (singularChainAugmentation (E := E) R),
      d_singularChainAugmentation, zero_comp, comp_zero, sub_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [eq_sub_of_add_eq (affineCone_boundary R (singularSimplexBarycenter σ) n)]
    simp only [Preadditive.comp_sub, affineSubdivisionMap_straightening]
    rw [← Category.assoc (affineSubdivisionMap R (n + 1)), hn]
    simp only [Category.assoc]
    rw [← Category.assoc
      (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1))]
    simp only [HomologicalComplex.d_comp_d, zero_comp, comp_zero, sub_zero]

def affineSubdivision :
    (TopCat.toSSet.obj (TopCat.of E)).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of E)).chainComplex R where
  f := affineSubdivisionMap R
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact affineSubdivisionMap_comm R j


@[simp]
theorem affineSubdivision_f (n : ℕ) :
    (affineSubdivision (E := E) R).f n = affineSubdivisionMap R n := rfl


theorem affineSubdivision_comp_straightening :
    affineSubdivision (E := E) R ≫ SSet.chainComplexMap (affineStraightening (E := E)) R =
      affineSubdivision R := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact affineSubdivisionMap_straightening (E := E) R n

end DifferentialGeometry.Homology
