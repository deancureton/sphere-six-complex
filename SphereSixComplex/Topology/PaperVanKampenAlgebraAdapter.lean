module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import SphereSixComplex.Topology.FullVanKampenReduction

/-!
# Algebraic adapter for the paper's affine van Kampen data

This file contains no topology assumption. It converts generic affine-core and filling data at the
paper's explicit matrices and twists into `FullVanKampenRelations`, then proves that core generation
implies generation by the three reduced paper generators.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology

open LatticeData

/-- The order-three lattice monodromy as an additive homomorphism. -/
public def paperMonodromyOne : Lattice →+ Lattice where
  toFun := fun a : Lattice ↦ A₁.mulVec a
  map_zero' := A₁.mulVec_zero
  map_add' := A₁.mulVec_add

/-- The order-four lattice monodromy as an additive homomorphism. -/
public def paperMonodromyTwo : Lattice →+ Lattice where
  toFun := fun a : Lattice ↦ A₂.mulVec a
  map_zero' := A₂.mulVec_zero
  map_add' := A₂.mulVec_add

/-- The toric sublattice killed by the cusp filling. -/
public def paperToricSubgroup : AddSubgroup Lattice where
  carrier := {a | a 0 = 0 ∧ a 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a 0 = 0 ∧ a 1 = 0 at ha
    change b 0 = 0 ∧ b 1 = 0 at hb
    change (a + b) 0 = 0 ∧ (a + b) 1 = 0
    simp [ha.1, ha.2, hb.1, hb.2]
  neg_mem' := by
    intro a ha
    change a 0 = 0 ∧ a 1 = 0 at ha
    change (-a) 0 = 0 ∧ (-a) 1 = 0
    simp [ha.1, ha.2]

/-- Reindex an affine-core translation homomorphism by the lattice involution `a ↦ -a`. -/
public def negateTranslationBasis
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo) :
    Lattice →+ Additive G where
  toFun a := C.translation (-a)
  map_zero' := by simp
  map_add' a b := by simp [add_comm]

@[simp]
public theorem negateTranslationBasis_apply
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (a : Lattice) :
    negateTranslationBasis C a = C.translation (-a) := rfl

/-- Reindex every affine-core translation by the lattice involution `a ↦ -a`. -/
public def negateTranslationBasisCoreData
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo) :
    AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo where
  translation := negateTranslationBasis C
  rhoOne := C.rhoOne
  rhoTwo := C.rhoTwo
  conjugate_one := by
    intro a
    simpa only [negateTranslationBasis_apply, map_neg] using C.conjugate_one (-a)
  conjugate_two := by
    intro a
    simpa only [negateTranslationBasis_apply, map_neg] using C.conjugate_two (-a)
  generators_generate := by
    rw [show Set.range (fun a ↦ Additive.toMul (negateTranslationBasis C a)) =
        Set.range (fun a ↦ Additive.toMul (C.translation a)) by
      ext g
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨-a, by simp⟩
      · rintro ⟨a, rfl⟩
        exact ⟨-a, by simp⟩]
    exact C.generators_generate

@[simp]
public theorem negateTranslationBasisCoreData_translation
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (a : Lattice) :
    (negateTranslationBasisCoreData C).translation a = C.translation (-a) := rfl

/-- Simultaneously negating both elliptic twists is exactly a change of lattice translation
basis. The toric vanishing condition is preserved because the toric lattice is a subgroup. -/
public theorem negateTranslationBasisRelations
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (F : AffineTorusStarFillingRelations C 3 4 (-epsilon) epsilon' 0
      paperToricSubgroup) :
    AffineTorusStarFillingRelations (negateTranslationBasisCoreData C)
      3 4 epsilon (-epsilon') 0 paperToricSubgroup where
  elliptic_one := by
    change C.rhoOne ^ 3 = Additive.toMul (C.translation (-epsilon))
    exact F.elliptic_one
  elliptic_two := by
    simpa only [negateTranslationBasisCoreData, negateTranslationBasis_apply,
      neg_neg] using F.elliptic_two
  cusp := by
    change C.rhoOne * C.rhoTwo = Additive.toMul (C.translation 0)
    exact F.cusp
  toric_vanishes := by
    intro a ha
    simpa only [negateTranslationBasisCoreData_translation] using
      F.toric_vanishes (-a) (paperToricSubgroup.neg_mem ha)

/-- Generic affine-core and filling data specialize to the paper's full van Kampen relations. -/
public def fullVanKampenRelationsOfAffineData
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (F : AffineTorusStarFillingRelations C 3 4 epsilon (-epsilon') 0
      paperToricSubgroup) :
    FullVanKampenRelations G epsilon (-epsilon') 0 where
  translation := C.translation
  ρ₁ := C.rhoOne
  ρ₂ := C.rhoTwo
  conjugate_one a := by simpa [paperMonodromyOne] using C.conjugate_one a
  conjugate_two a := by simpa [paperMonodromyTwo] using C.conjugate_two a
  elliptic_one := F.elliptic_one
  elliptic_two := F.elliptic_two
  cusp := F.cusp
  toric_vanishes a ha hb := F.toric_vanishes a ⟨ha, hb⟩

namespace FullVanKampenRelations

variable {G : Type*} [Group G]

/-- The fourth standard basis vector belongs to the toric sublattice. -/
public def tailBasis : Lattice := ![0, 0, 0, 1]

@[simp]
private theorem tailBasis_apply_zero : tailBasis 0 = 0 := rfl

@[simp]
private theorem tailBasis_apply_one : tailBasis 1 = 0 := rfl

/-- The cusp filling kills the fourth standard basis translation. -/
@[simp]
public theorem translationMul_tailBasis_eq_one
    (R : FullVanKampenRelations G epsilon (-epsilon') 0) :
    R.translationMul tailBasis = 1 :=
  R.toric_vanishes tailBasis (by simp) (by simp)

/-- The selected full relations kill every lattice translation. -/
@[simp]
public theorem translationMul_eq_one
    (R : FullVanKampenRelations G epsilon (-epsilon') 0) (a : Lattice) :
    R.translationMul a = 1 := by
  have hdecomp :
      a = a 0 • epsilon + (a 1 - 2 * a 0) • uVec +
        (a 2 + 4 * a 0) • wVec + a 3 • tailBasis := by
    funext i
    fin_cases i <;> simp [epsilon, uVec, wVec, tailBasis] <;> ring
  rw [hdecomp, R.translationMul_add, R.translationMul_add, R.translationMul_add,
    R.translationMul_zsmul, R.translationMul_zsmul, R.translationMul_zsmul,
    R.translationMul_zsmul, R.translationMul_epsilon_eq_one,
    R.translationMul_uVec_eq_one, R.translationMul_wVec_eq_one,
    R.translationMul_tailBasis_eq_one]
  simp

end FullVanKampenRelations

/-- Generation by all affine-core generators implies generation by the paper's reduced three
generators after the selected filling relations have been imposed. -/
public theorem paperGeneratorsGenerate_of_affineData
    {G : Type*} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (F : AffineTorusStarFillingRelations C 3 4 epsilon (-epsilon') 0
      paperToricSubgroup) :
    let R := fullVanKampenRelationsOfAffineData C F
    PaperGeneratorsGenerate R.toSatisfiesPaperRelations := by
  let R := fullVanKampenRelationsOfAffineData C F
  have hsource :
      Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪ {C.rhoOne, C.rhoTwo} ⊆
        ({1} : Set G) := by
    intro g hg
    rcases hg with ⟨a, rfl⟩ | hg
    · rw [Set.mem_singleton_iff]
      change R.translationMul a = 1
      exact R.translationMul_eq_one a
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [Set.mem_singleton_iff]
        change R.ρ₁ = 1
        exact R.rhoOne_eq_one
      · rw [Set.mem_singleton_iff]
        change R.ρ₂ = 1
        exact R.rhoTwo_eq_one
  have hclosure :
      Subgroup.closure
          (Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪ {C.rhoOne, C.rhoTwo}) ≤
        ⊥ := by
    rw [Subgroup.closure_le]
    intro g hg
    change g = 1
    exact hsource hg
  have hall (g : G) : g = 1 := by
    have hg : g ∈ Subgroup.closure
        (Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪ {C.rhoOne, C.rhoTwo}) := by
      rw [C.generators_generate]
      trivial
    exact Subgroup.mem_bot.mp (hclosure hg)
  apply top_unique
  intro g _
  rw [hall g]
  exact Subgroup.one_mem _

/-- The generic affine topology data give the verified paper van Kampen contract. -/
public theorem hasVanKampenData_of_affineData
    {X : Type*} [TopologicalSpace X] (base : X)
    (C : AffineTorusCorePiOneData (FundamentalGroup X base) Lattice
      paperMonodromyOne paperMonodromyTwo)
    (F : AffineTorusStarFillingRelations C 3 4 epsilon (-epsilon') 0
      paperToricSubgroup) :
    HasVanKampenData X 0 1 (-1) :=
  hasVanKampenData_of_fullRelations base (fullVanKampenRelationsOfAffineData C F)
    (paperGeneratorsGenerate_of_affineData C F)

/-- The physically oriented elliptic twists give the same paper presentation after the explicit
simultaneous negation of the lattice translation basis. -/
public theorem hasVanKampenData_of_correctedAffineData
    {X : Type*} [TopologicalSpace X] (base : X)
    (C : AffineTorusCorePiOneData (FundamentalGroup X base) Lattice
      paperMonodromyOne paperMonodromyTwo)
    (F : AffineTorusStarFillingRelations C 3 4 (-epsilon) epsilon' 0
      paperToricSubgroup) :
    HasVanKampenData X 0 1 (-1) :=
  hasVanKampenData_of_affineData base (negateTranslationBasisCoreData C)
    (negateTranslationBasisRelations C F)

end SphereSixComplex.Topology

end
