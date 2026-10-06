module

public import DifferentialGeometry.Topology.Homology.Subdivision.Support
public import DifferentialGeometry.Topology.Homology.Subdivision.Naturality
public import DifferentialGeometry.Topology.Homology.SmallChains.Subspace

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (hs : Convex ℝ s) {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "A" => smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)
local notation "KA" => _root_.SSet.chainComplex (A : SSet) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "I" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A)) R
local notation "SA" => _root_.SSet.chainComplexMap (smallAffineStraightening hs) R
local notation "S" => _root_.SSet.chainComplexMap (affineStraightening (E := E)) R

theorem Restriction.smallSubdivision_comm (n : ℕ) :
    smallAffineSubdivisionMap hs R (n + 1) ≫ (KA).d (n + 1) n =
      (KA).d (n + 1) n ≫ smallAffineSubdivisionMap hs R n := by
  have : Mono ((I).f n) := mono_smallChainMap_f _ _ R n
  apply (cancel_mono ((I).f n)).mp
  simp only [Category.assoc]
  rw [← (I).comm, ← Category.assoc, smallAffineSubdivisionMap_inclusion,
    Category.assoc, affineSubdivisionMap_comm, smallAffineSubdivisionMap_inclusion]
  rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
  simp only [Category.assoc]


def smallAffineSubdivision : (KA) ⟶ (KA) where
  f := smallAffineSubdivisionMap hs R
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact Restriction.smallSubdivision_comm hs R j


@[simp]
theorem smallAffineSubdivision_f (n : ℕ) :
    (smallAffineSubdivision hs R).f n = smallAffineSubdivisionMap hs R n := rfl


theorem smallAffineSubdivision_inclusion :
    smallAffineSubdivision hs R ≫ (I) = (I) ≫ affineSubdivision R := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact smallAffineSubdivisionMap_inclusion hs R n

theorem Restriction.smallHomotopy_comm (n : ℕ) :
    (smallAffineSubdivision hs R - SA).f (n + 1) =
      (KA).d (n + 1) n ≫ smallAffineSubdivisionHomotopyMap hs R n +
        smallAffineSubdivisionHomotopyMap hs R (n + 1) ≫ (KA).d (n + 2) (n + 1) := by
  have : Mono ((I).f (n + 1)) := mono_smallChainMap_f _ _ R (n + 1)
  apply (cancel_mono ((I).f (n + 1))).mp
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, smallAffineSubdivision_f,
    smallAffineSubdivisionMap_inclusion]
  have hS := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) (n + 1)
  simp only [HomologicalComplex.comp_f] at hS
  rw [hS, ← Preadditive.comp_sub]
  change (I).f (n + 1) ≫ (affineSubdivision R - S).f (n + 1) = _
  rw [affineSubdivisionHomotopyMap_comm, Preadditive.comp_add, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← (I).comm, ← Category.assoc (smallAffineSubdivisionHomotopyMap hs R (n + 1)),
    smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
  simp only [Category.assoc]

theorem Restriction.smallStraightening_zero : (SA).f 0 = 𝟙 _ := by
  have : Mono ((I).f 0) := mono_smallChainMap_f _ _ R 0
  apply (cancel_mono ((I).f 0)).mp
  have h := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) 0
  simpa only [HomologicalComplex.comp_f, affineStraightening_f_zero,
    Category.id_comp, Category.comp_id] using h


def smallAffineSubdivisionHomotopy : Homotopy (smallAffineSubdivision hs R) (SA) where
  hom i j := if h : i + 1 = j then
    smallAffineSubdivisionHomotopyMap hs R i ≫ eqToHom (congrArg (KA).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        smallAffineSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        smallAffineSubdivision_f, smallAffineSubdivisionMap_zero, Restriction.smallStraightening_zero]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
      exact sub_eq_iff_eq_add.mp (Restriction.smallHomotopy_comm hs R n)


@[simp]
theorem smallAffineSubdivisionHomotopy_hom (n : ℕ) :
    (smallAffineSubdivisionHomotopy hs R).hom n (n + 1) =
      smallAffineSubdivisionHomotopyMap hs R n := by
  change (if h : n + 1 = n + 1 then
    smallAffineSubdivisionHomotopyMap hs R n ≫ eqToHom (congrArg (KA).X h) else 0) = _
  rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

variable {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {t : Set E'} (ht : Convex ℝ t) (f : E →L[ℝ] E') (hf : Set.MapsTo f s t)

local notation "A'" => smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)
local notation "I'" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A')) R
local notation "Φ" => TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
local notation "T" => _root_.SSet.chainComplexMap (Φ) R
local notation "Tₛ" => _root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R

private theorem supported_linear_inclusion (n : ℕ) :
    (Tₛ).f n ≫ (I').f n = (I).f n ≫ (T).f n := by
  have h : (Tₛ) ≫ (I') = (I) ≫ (T) := by
    change ((SSet.chainComplexFunctor _).obj R).map _ ≫
        ((SSet.chainComplexFunctor _).obj R).map _ =
      ((SSet.chainComplexFunctor _).obj R).map _ ≫
        ((SSet.chainComplexFunctor _).obj R).map _
    rw [← Functor.map_comp, ← Functor.map_comp, smallSingularSimplicesMap_ι]
  exact HomologicalComplex.congr_hom h n


theorem smallAffineSubdivisionMap_naturality_linear (n : ℕ) :
    smallAffineSubdivisionMap hs R n ≫ (Tₛ).f n =
      (Tₛ).f n ≫ smallAffineSubdivisionMap ht R n := by
  have : Mono ((I').f n) := mono_smallChainMap_f _ _ R n
  apply (cancel_mono ((I').f n)).mp
  simp only [Category.assoc]
  rw [supported_linear_inclusion R f hf, smallAffineSubdivisionMap_inclusion]
  rw [← Category.assoc, smallAffineSubdivisionMap_inclusion, Category.assoc,
    affineSubdivisionMap_naturality_linear]
  rw [← Category.assoc ((Tₛ).f n), supported_linear_inclusion R f hf]
  simp only [Category.assoc]


theorem smallAffineSubdivisionHomotopyMap_naturality_linear (n : ℕ) :
    smallAffineSubdivisionHomotopyMap hs R n ≫ (Tₛ).f (n + 1) =
      (Tₛ).f n ≫ smallAffineSubdivisionHomotopyMap ht R n := by
  have : Mono ((I').f (n + 1)) := mono_smallChainMap_f _ _ R (n + 1)
  apply (cancel_mono ((I').f (n + 1))).mp
  simp only [Category.assoc]
  rw [supported_linear_inclusion R f hf, smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← Category.assoc, smallAffineSubdivisionHomotopyMap_inclusion, Category.assoc,
    affineSubdivisionHomotopyMap_naturality_linear]
  rw [← Category.assoc ((Tₛ).f n), supported_linear_inclusion R f hf]
  simp only [Category.assoc]

end DifferentialGeometry.Homology
