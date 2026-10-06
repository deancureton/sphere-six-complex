module

public import DifferentialGeometry.Topology.Homology.Subdivision.Homotopy
public import DifferentialGeometry.Topology.Homology.SmallChains

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (hs : Convex ℝ s)

local notation "A" => smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)

omit [NormedSpace ℝ E] in
theorem small_vertices_mem {n : ℕ} (σ : (A : SSet) _⦋n⦌) (i : Fin (n + 1)) :
    singularSimplexVertices σ.val i ∈ s := by
  obtain ⟨_, hσ⟩ := σ.property
  exact hσ ⟨Convexity.StdSimplex.single i, rfl⟩


def smallBarycenter {n : ℕ} (σ : (A : SSet) _⦋n⦌) : s :=
  ⟨singularSimplexBarycenter σ.val,
    singularSimplexBarycenter_mem _ hs (small_vertices_mem σ)⟩


def smallAffineSimplex {n : ℕ} (σ : (A : SSet) _⦋n⦌) : (A : SSet) _⦋n⦌ :=
  ⟨affineSingularSimplex (singularSimplexVertices σ.val), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (small_vertices_mem σ)⟩


def smallConeSimplex (p : s) {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet) _⦋n + 1⦌ :=
  ⟨affineSingularSimplex (Fin.cons (p : E) (singularSimplexVertices σ.val)), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (Fin.cases p.property (small_vertices_mem σ))⟩


def smallAffineStraightening : (A : SSet) ⟶ (A : SSet) :=
  SSet.Subcomplex.lift ((A).ι ≫ affineStraightening) (by
    intro n τ hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact (smallAffineSimplex hs (n := n.unop.len) σ).property)


@[reassoc]
theorem smallAffineStraightening_ι :
    smallAffineStraightening hs ≫ (A).ι = (A).ι ≫ affineStraightening := rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "KA" => _root_.SSet.chainComplex (A : SSet) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "I" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A)) R
local notation "SA" => _root_.SSet.chainComplexMap (smallAffineStraightening hs) R
local notation "S" => _root_.SSet.chainComplexMap (affineStraightening (E := E)) R


theorem smallAffineStraightening_inclusion : (SA) ≫ (I) = (I) ≫ (S) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallAffineStraightening_ι]


def smallAffineCone (p : s) (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  Sigma.desc (fun σ ↦ (A : SSet).ιChainComplex (smallConeSimplex hs p σ))


@[reassoc]
theorem ι_smallAffineCone (p : s) {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineCone hs R p n =
      (A : SSet).ιChainComplex (smallConeSimplex hs p σ) :=
  Sigma.ι_comp_desc _ _


@[reassoc]
theorem smallAffineCone_inclusion (p : s) (n : ℕ) :
    smallAffineCone hs R p n ≫ (I).f (n + 1) = (I).f n ≫ affineCone R (p : E) n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallAffineCone, SSet.ι_chainComplexMap_f,
    ← Category.assoc, SSet.ι_chainComplexMap_f, ι_affineCone]
  rfl


def smallAffineSubdivisionMap (n : ℕ) : (KA).X n ⟶ (KA).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦ (A : SSet).ιChainComplex σ ≫
      (KA).d (n + 1) n ≫ smallAffineSubdivisionMap n ≫
        smallAffineCone hs R (smallBarycenter hs σ) n)


@[simp]
theorem smallAffineSubdivisionMap_zero : smallAffineSubdivisionMap hs R 0 = 𝟙 _ := rfl


@[reassoc]
theorem ι_smallAffineSubdivisionMap_succ (n : ℕ) (σ : (A : SSet) _⦋n + 1⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineSubdivisionMap hs R (n + 1) =
      (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
        smallAffineSubdivisionMap hs R n ≫ smallAffineCone hs R (smallBarycenter hs σ) n :=
  Sigma.ι_comp_desc _ _


theorem smallAffineSubdivisionMap_inclusion (n : ℕ) :
    smallAffineSubdivisionMap hs R n ≫ (I).f n = (I).f n ≫ affineSubdivisionMap R n := by
  induction n with
  | zero => rw [smallAffineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_smallAffineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [smallAffineCone_inclusion]
    rw [← Category.assoc (smallAffineSubdivisionMap hs R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
    simp only [Category.assoc]
    rw [← Category.assoc _ ((I).f (n + 1)), SSet.ι_chainComplexMap_f]
    rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ]
    rfl

private theorem smallDifference_inclusion (n : ℕ) :
    (smallAffineSubdivisionMap hs R n - (SA).f n) ≫ (I).f n =
      (I).f n ≫ (affineSubdivision R - S).f n := by
  rw [Preadditive.sub_comp, smallAffineSubdivisionMap_inclusion]
  have h := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]


def smallAffineSubdivisionHomotopyMap (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      ((A : SSet).ιChainComplex σ ≫ (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
        (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
          smallAffineSubdivisionHomotopyMap n) ≫
        smallAffineCone hs R (smallBarycenter hs σ) (n + 1))


@[simp]
theorem smallAffineSubdivisionHomotopyMap_zero :
    smallAffineSubdivisionHomotopyMap hs R 0 = 0 := rfl


@[reassoc]
theorem ι_smallAffineSubdivisionHomotopyMap_succ (n : ℕ) (σ : (A : SSet) _⦋n + 1⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineSubdivisionHomotopyMap hs R (n + 1) =
      ((A : SSet).ιChainComplex σ ≫ (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
        (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
          smallAffineSubdivisionHomotopyMap hs R n) ≫
        smallAffineCone hs R (smallBarycenter hs σ) (n + 1) :=
  Sigma.ι_comp_desc _ _

theorem smallAffineSubdivisionHomotopyMap_inclusion (n : ℕ) :
    smallAffineSubdivisionHomotopyMap hs R n ≫ (I).f (n + 1) =
      (I).f n ≫ affineSubdivisionHomotopyMap R n := by
  induction n with
  | zero => rw [smallAffineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      zero_comp, comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        ((A : SSet).ιChainComplex σ ≫
            (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
          (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
            smallAffineSubdivisionHomotopyMap hs R n) ≫ (I).f (n + 1) =
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val ≫
            (affineSubdivision R - S).f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val ≫
            (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [smallDifference_inclusion, hn]
      rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
      simp only [Category.assoc]
      rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rfl
    rw [← Category.assoc, ι_smallAffineSubdivisionHomotopyMap_succ, Category.assoc,
      smallAffineCone_inclusion, ← Category.assoc, hz]
    rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ]
    rfl

end DifferentialGeometry.Homology
