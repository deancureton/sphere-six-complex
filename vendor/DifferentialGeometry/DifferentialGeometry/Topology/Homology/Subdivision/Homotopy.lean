module

public import DifferentialGeometry.Topology.Homology.Subdivision.Barycentric
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.Abel

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "S" => SSet.chainComplexMap (affineStraightening (E := E)) R
local notation "B" => affineSubdivision (E := E) R
local notation "F" => (B - S)

private theorem straightening_f_idempotent (n : ℕ) : (S).f n ≫ (S).f n = (S).f n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      ((affineStraightening (E := E)).app (op ⦋n⦌)
        (affineSingularSimplex (singularSimplexVertices σ))) = _
  rw [affineStraightening_affineSingularSimplex]
  rfl

private theorem difference_f_straightening (n : ℕ) : (F).f n ≫ (S).f n = (F).f n := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_straightening, straightening_f_idempotent]

private theorem difference_f_zero : (F).f 0 = 0 := by
  rw [HomologicalComplex.sub_f_apply, affineSubdivision_f, affineSubdivisionMap_zero,
    affineStraightening_f_zero, sub_self]


theorem affineCone_fills_cycle (p : E) {n : ℕ} {T : ModuleCat.{u} k}
    (z : T ⟶ (K).X (n + 1)) (hz : z ≫ (K).d (n + 1) n = 0)
    (haff : z ≫ (S).f (n + 1) = z) :
    z ≫ affineCone R p (n + 1) ≫ (K).d (n + 2) (n + 1) = z := by
  rw [eq_sub_of_add_eq (affineCone_boundary R p n), Preadditive.comp_sub, haff,
    ← Category.assoc, hz, zero_comp, sub_zero]


def affineSubdivisionHomotopyMap (n : ℕ) : (K).X n ⟶ (K).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap n) ≫ affineCone R (singularSimplexBarycenter σ) (n + 1))


@[simp]
theorem affineSubdivisionHomotopyMap_zero : affineSubdivisionHomotopyMap (E := E) R 0 = 0 := rfl


@[reassoc]
theorem ι_affineSubdivisionHomotopyMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        affineSubdivisionHomotopyMap R (n + 1) =
      ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap R n) ≫
        affineCone R (singularSimplexBarycenter σ) (n + 1) :=
  Sigma.ι_comp_desc _ _


theorem affineSubdivisionHomotopyMap_straightening (n : ℕ) :
    affineSubdivisionHomotopyMap (E := E) R n ≫ (S).f (n + 1) =
      affineSubdivisionHomotopyMap R n := by
  cases n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, zero_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ]
    simp only [Category.assoc, affineCone_straightening]

private def homotopyPrev (n : ℕ) : (K).X n ⟶ (K).X n :=
  match n with
  | 0 => 0
  | n + 1 => (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n

private theorem d_homotopyPrev (n : ℕ) : (K).d (n + 1) n ≫ homotopyPrev R n = 0 := by
  cases n with
  | zero => exact comp_zero
  | succ n =>
    change (K).d (n + 2) (n + 1) ≫
      ((K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n) = 0
    rw [← Category.assoc, (K).d_comp_d, zero_comp]

private theorem affineSubdivisionHomotopyMap_comm_aux (n : ℕ) :
    (F).f n = homotopyPrev R n +
      affineSubdivisionHomotopyMap R n ≫ (K).d (n + 1) n := by
  induction n with
  | zero => simp only [homotopyPrev, affineSubdivisionHomotopyMap_zero,
      difference_f_zero, zero_comp, add_zero]
  | succ n hn =>
    change (F).f (n + 1) = (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n +
      affineSubdivisionHomotopyMap R (n + 1) ≫ (K).d (n + 2) (n + 1)
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [Preadditive.comp_add]
    rw [← Category.assoc _ (affineSubdivisionHomotopyMap R (n + 1)),
      ι_affineSubdivisionHomotopyMap_succ, Category.assoc]
    let z : R ⟶ (K).X (n + 1) :=
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap R n
    have hza : z ≫ (S).f (n + 1) = z := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc, difference_f_straightening,
        affineSubdivisionHomotopyMap_straightening]
    have hzc : z ≫ (K).d (n + 1) n = 0 := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [(F).comm, hn]
      simp only [Preadditive.comp_add]
      rw [d_homotopyPrev]
      simp only [comp_zero, zero_add, sub_self]
    rw [affineCone_fills_cycle R (singularSimplexBarycenter σ) z hzc hza]
    dsimp only [z]
    abel


theorem affineSubdivisionHomotopyMap_comm (n : ℕ) :
    (F).f (n + 1) = (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n +
      affineSubdivisionHomotopyMap R (n + 1) ≫ (K).d (n + 2) (n + 1) :=
  affineSubdivisionHomotopyMap_comm_aux R (n + 1)

def affineSubdivisionHomotopy : Homotopy (B) (S) where
  hom i j := if h : i + 1 = j then
    affineSubdivisionHomotopyMap R i ≫ eqToHom (congrArg (K).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        affineSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        affineSubdivision_f, affineSubdivisionMap_zero, affineStraightening_f_zero]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
      exact sub_eq_iff_eq_add.mp (affineSubdivisionHomotopyMap_comm R n)


@[simp]
theorem affineSubdivisionHomotopy_hom (n : ℕ) :
    (affineSubdivisionHomotopy (E := E) R).hom n (n + 1) =
      affineSubdivisionHomotopyMap R n := by
  change (if h : n + 1 = n + 1 then
    affineSubdivisionHomotopyMap R n ≫ eqToHom (congrArg (K).X h) else 0) = _
  rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

end DifferentialGeometry.Homology
