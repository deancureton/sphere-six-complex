module

public import SphereSixComplex.Topology.FundamentalGroupComputation
import all SphereSixComplex.LatticeData

/-!
# Reduction of the full van Kampen relations at the chosen twists

This file carries out the algebraic reduction from the lattice-valued relations appearing before
the final presentation in Theorem 7.17.  For the chosen twist vectors `epsilon` and `-epsilon'`
and zero cusp twist, the toric relations and the order-three monodromy force the two auxiliary
translations to vanish.  The elliptic and cusp relations then force both elliptic generators, and
finally the surviving translation generator, to be the identity.

Consequently the full relations give the three displayed paper relations.  Since the obstruction
group for `(0, 1, -1)` is `ZMod 1`, the no-extra-relations condition is automatic; generation by
the displayed generators is the only remaining hypothesis needed to construct `HasVanKampenData`.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.LatticeData

/-- The order-three monodromy sends the second toric basis vector to `uVec - wVec`. -/
@[simp]
public theorem A₁_mulVec_wVec : A₁ *ᵥ wVec = uVec - wVec := by
  funext i
  fin_cases i <;>
    simp [A₁, uVec, wVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The difference of the two chosen elliptic twist vectors is entirely toric. -/
@[simp]
public theorem epsilon_sub_epsilon' : epsilon - epsilon' = -uVec - wVec := by
  funext i
  fin_cases i <;> simp [epsilon, epsilon', uVec, wVec]

end SphereSixComplex.LatticeData

namespace SphereSixComplex.Topology

open LatticeData

namespace FullVanKampenRelations

variable {G : Type*} [Group G]
variable {v₁ v₂ μ : Lattice}

/-- Multiplicative notation for the image of a lattice translation. -/
public def translationMul (R : FullVanKampenRelations G v₁ v₂ μ) (a : Lattice) : G :=
  Additive.toMul (R.translation a)

@[simp]
public theorem translationMul_zero (R : FullVanKampenRelations G v₁ v₂ μ) :
    R.translationMul 0 = 1 := by
  simp [translationMul]

@[simp]
public theorem translationMul_add (R : FullVanKampenRelations G v₁ v₂ μ)
    (a b : Lattice) : R.translationMul (a + b) = R.translationMul a * R.translationMul b := by
  simp [translationMul]

@[simp]
public theorem translationMul_neg (R : FullVanKampenRelations G v₁ v₂ μ)
    (a : Lattice) : R.translationMul (-a) = (R.translationMul a)⁻¹ := by
  simp [translationMul]

@[simp]
public theorem translationMul_sub (R : FullVanKampenRelations G v₁ v₂ μ)
    (a b : Lattice) : R.translationMul (a - b) = R.translationMul a / R.translationMul b := by
  simp [translationMul]

@[simp]
public theorem translationMul_zsmul (R : FullVanKampenRelations G v₁ v₂ μ)
    (n : ℤ) (a : Lattice) : R.translationMul (n • a) = R.translationMul a ^ n := by
  change Additive.toMul (R.translation (n • a)) = Additive.toMul (R.translation a) ^ n
  rw [map_zsmul, toMul_zsmul]

variable (R : FullVanKampenRelations G epsilon (-epsilon') 0)

/-- The toric-vanishing relation kills the basis translation `wVec`. -/
@[simp]
public theorem translationMul_wVec_eq_one : R.translationMul wVec = 1 := by
  exact R.toric_vanishes wVec
    (by simp [wVec])
    (by simp [wVec])

/-- Conjugating the vanished `wVec` translation by the order-three generator kills `uVec`. -/
@[simp]
public theorem translationMul_uVec_eq_one : R.translationMul uVec = 1 := by
  have h := R.conjugate_one wVec
  change R.ρ₁ * R.translationMul wVec * R.ρ₁⁻¹ =
    R.translationMul (A₁ *ᵥ wVec) at h
  rw [A₁_mulVec_wVec, R.translationMul_sub, R.translationMul_wVec_eq_one] at h
  simpa only [mul_one, mul_inv_cancel, div_one] using h.symm

/-- The difference of the two elliptic twist translations is therefore trivial. -/
@[simp]
public theorem translationMul_epsilon_sub_epsilonPrime_eq_one :
    R.translationMul (epsilon - epsilon') = 1 := by
  rw [epsilon_sub_epsilon', R.translationMul_sub, R.translationMul_neg,
    R.translationMul_uVec_eq_one, R.translationMul_wVec_eq_one]
  simp

/-- The zero cusp twist identifies the product of the two elliptic generators with the identity. -/
public theorem rhoOne_mul_rhoTwo_eq_one : R.ρ₁ * R.ρ₂ = 1 := by
  have h := R.cusp
  change R.ρ₁ * R.ρ₂ = R.translationMul 0 at h
  simpa using h

/-- Equivalently, the order-three generator is the inverse of the order-four generator. -/
public theorem rhoOne_eq_inv_rhoTwo : R.ρ₁ = R.ρ₂⁻¹ :=
  eq_inv_of_mul_eq_one_left R.rhoOne_mul_rhoTwo_eq_one

/-- Combining the two elliptic filling relations expresses `ρ₂` by a toric translation. -/
public theorem rhoTwo_eq_translationMul_epsilon_sub_epsilonPrime :
    R.ρ₂ = R.translationMul (epsilon - epsilon') := by
  calc
    R.ρ₂ = R.ρ₁ ^ 3 * R.ρ₂ ^ 4 := by
      rw [R.rhoOne_eq_inv_rhoTwo]
      group
    _ = R.translationMul epsilon * R.translationMul (-epsilon') := by
      change R.ρ₁ ^ 3 * R.ρ₂ ^ 4 =
        Additive.toMul (R.translation epsilon) * Additive.toMul (R.translation (-epsilon'))
      rw [R.elliptic_one, R.elliptic_two]
    _ = R.translationMul (epsilon - epsilon') := by
      rw [sub_eq_add_neg, R.translationMul_add]

/-- The order-four elliptic generator is trivial at the chosen twists. -/
@[simp]
public theorem rhoTwo_eq_one : R.ρ₂ = 1 :=
  R.rhoTwo_eq_translationMul_epsilon_sub_epsilonPrime.trans
    R.translationMul_epsilon_sub_epsilonPrime_eq_one

/-- The cusp relation then makes the order-three elliptic generator trivial as well. -/
@[simp]
public theorem rhoOne_eq_one : R.ρ₁ = 1 := by
  rw [R.rhoOne_eq_inv_rhoTwo, R.rhoTwo_eq_one, inv_one]

/-- The surviving translation generator is trivial by the order-three filling relation. -/
@[simp]
public theorem translationMul_epsilon_eq_one : R.translationMul epsilon = 1 := by
  calc
    R.translationMul epsilon = R.ρ₁ ^ 3 := R.elliptic_one.symm
    _ = 1 := by rw [R.rhoOne_eq_one]; simp

/-- Forget the lattice-valued presentation and retain the paper's three chosen relations. -/
public def toSatisfiesPaperRelations : SatisfiesPaperRelations G 0 1 (-1) where
  c := R.translationMul epsilon
  x := R.ρ₁
  y := R.ρ₂
  central_c g := by
    rw [R.translationMul_epsilon_eq_one]
    simp
  xy := by
    rw [R.rhoOne_eq_one, R.rhoTwo_eq_one, R.translationMul_epsilon_eq_one]
    simp
  x_cube := by
    rw [R.rhoOne_eq_one, R.translationMul_epsilon_eq_one]
    simp
  y_fourth := by
    rw [R.rhoTwo_eq_one, R.translationMul_epsilon_eq_one]
    simp

@[simp]
public theorem toSatisfiesPaperRelations_c_eq_one : R.toSatisfiesPaperRelations.c = 1 :=
  R.translationMul_epsilon_eq_one

@[simp]
public theorem toSatisfiesPaperRelations_x_eq_one : R.toSatisfiesPaperRelations.x = 1 :=
  R.rhoOne_eq_one

@[simp]
public theorem toSatisfiesPaperRelations_y_eq_one : R.toSatisfiesPaperRelations.y = 1 :=
  R.rhoTwo_eq_one

end FullVanKampenRelations

/-- At the chosen twists the cyclic classifier takes values in `ZMod 1`, so no additional
normal-form relation can exist. -/
public theorem SatisfiesPaperRelations.hasNoExtraChosen
    {G : Type*} [Group G] (r : SatisfiesPaperRelations G 0 1 (-1)) :
    HasNoExtraPaperRelations r := by
  intro z _
  have hmod : (paperObstruction 0 1 (-1)).natAbs = 1 := by
    norm_num [paperObstruction]
  let _ : Subsingleton (ZMod (paperObstruction 0 1 (-1)).natAbs) := by
    rw [hmod]
    infer_instance
  exact Subsingleton.elim _ _

/-- Full van Kampen relations at the chosen twists yield the complete presentation data once the
three displayed generators are known to generate the fundamental group. -/
public theorem hasVanKampenData_of_fullRelations
    {X : Type*} [TopologicalSpace X] (base : X)
    (R : FullVanKampenRelations (FundamentalGroup X base) epsilon (-epsilon') 0)
    (hgenerate : PaperGeneratorsGenerate R.toSatisfiesPaperRelations) :
    HasVanKampenData X 0 1 (-1) :=
  ⟨base, R.toSatisfiesPaperRelations, hgenerate,
    R.toSatisfiesPaperRelations.hasNoExtraChosen⟩

end SphereSixComplex.Topology
