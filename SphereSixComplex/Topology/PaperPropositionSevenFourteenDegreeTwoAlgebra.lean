module

public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra
public import Mathlib.Data.ZMod.Basic

/-!
# Degree-two integral algebra at the two elliptic fibres

This module proves the exterior-square calculations underlying the degree-two part of
Proposition 7.14.  It identifies the two invariant lattices, computes their intersection
pairings, and isolates the full-index and index-two candidate pullback lattices.  It does not
identify either candidate with the image of a map on the homology or cohomology of a space.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.PaperPropositionSevenFourteenDegreeTwoAlgebra

open LatticeData
open PaperLemmaSevenThirteenAlgebra

public abbrev DegreeTwoLattice := Fin 6 → ℤ

/-- The second compound of the order-three cohomological monodromy. -/
public def orderThreeDegreeTwoMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1, 1, 1, -6, 2, -8;
     -1, 0, 1, -6, 2, -6;
     0, 0, 1, 0, 0, -6;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, -1, 1;
     0, 0, 0, 0, -1, 0]

/-- The second compound of the order-four cohomological monodromy. -/
public def orderFourDegreeTwoMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, -1, 1, -6, 6, -3;
     1, 0, 0, 0, 3, 0;
     0, 0, 1, 0, 6, 0;
     0, 0, 0, 1, -1, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0]

public theorem TOne_eq_transpose_AOne_sq : T₁ = (A₁ ^ 2)ᵀ := by
  rw [A₁_eq_transpose_T₁_sq, ← Matrix.transpose_pow]
  simp only [Matrix.transpose_transpose]
  rw [← pow_mul']
  norm_num
  rw [show T₁ ^ 4 = T₁ ^ 3 * T₁ by rw [pow_succ], T₁_pow_three, one_mul]

public theorem TTwo_eq_transpose_ATwo_cube : T₂ = (A₂ ^ 3)ᵀ := by
  rw [A₂_eq_transpose_T₂_cube, ← Matrix.transpose_pow]
  simp only [Matrix.transpose_transpose]
  rw [← pow_mul']
  norm_num
  rw [show T₂ ^ 9 = T₂ ^ (4 + 4 + 1) by norm_num]
  rw [pow_add, pow_add, T₂_pow_four]
  simp

public theorem secondCompoundMatrix_TOne :
    secondCompoundMatrix T₁ = orderThreeDegreeTwoMatrix := by
  rw [TOne_eq_transpose_AOne_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondCompoundMatrix, A₁, orderThreeDegreeTwoMatrix, periodPairFirst,
      periodPairSecond, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

public theorem secondCompoundMatrix_TTwo :
    secondCompoundMatrix T₂ = orderFourDegreeTwoMatrix := by
  rw [TTwo_eq_transpose_ATwo_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondCompoundMatrix, A₂, orderFourDegreeTwoMatrix, periodPairFirst,
      periodPairSecond, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

/-- The class `gamma ∧ epsilonOne` in coordinates `(01, 02, 03, 12, 13, 23)`. -/
public def gammaEpsilonOne : DegreeTwoLattice := ![2, 1, 3, 0, 0, 0]

/-- The class `gamma ∧ epsilonTwo` in coordinates `(01, 02, 03, 12, 13, 23)`. -/
public def gammaEpsilonTwo : DegreeTwoLattice := ![1, 1, 2, 0, 0, 0]

/-- The common invariant class `q = u ∧ w + 6 gamma ∧ delta`. -/
public def qClass : DegreeTwoLattice := ![0, 0, 6, 1, 0, 0]

public theorem orderThreeDegreeTwo_fixed_iff (x : DegreeTwoLattice) :
    secondCompoundMatrix T₁ *ᵥ x = x ↔
      ∃ a b : ℤ, x = a • gammaEpsilonOne + b • qClass := by
  rw [secondCompoundMatrix_TOne]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 6)
    have h1 := congrFun h (1 : Fin 6)
    have h2 := congrFun h (2 : Fin 6)
    have h3 := congrFun h (3 : Fin 6)
    have h4 := congrFun h (4 : Fin 6)
    have h5 := congrFun h (5 : Fin 6)
    simp [orderThreeDegreeTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    simp [orderThreeDegreeTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h3 h4 h5
    refine ⟨x 1, x 3, ?_⟩
    funext i
    fin_cases i <;> simp [gammaEpsilonOne, qClass] <;> omega
  · rintro ⟨a, b, rfl⟩
    funext i
    fin_cases i <;>
      simp [orderThreeDegreeTwoMatrix, gammaEpsilonOne, qClass, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
    all_goals ring

public theorem orderFourDegreeTwo_fixed_iff (x : DegreeTwoLattice) :
    secondCompoundMatrix T₂ *ᵥ x = x ↔
      ∃ a b : ℤ, x = a • gammaEpsilonTwo + b • qClass := by
  rw [secondCompoundMatrix_TTwo]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 6)
    have h1 := congrFun h (1 : Fin 6)
    have h2 := congrFun h (2 : Fin 6)
    have h3 := congrFun h (3 : Fin 6)
    have h4 := congrFun h (4 : Fin 6)
    have h5 := congrFun h (5 : Fin 6)
    simp [orderFourDegreeTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    simp [orderFourDegreeTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h3 h4 h5
    refine ⟨x 0, x 3, ?_⟩
    funext i
    fin_cases i <;> simp [gammaEpsilonTwo, qClass] <;> omega
  · rintro ⟨a, b, rfl⟩
    funext i
    fin_cases i <;>
      simp [orderFourDegreeTwoMatrix, gammaEpsilonTwo, qClass, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
    all_goals ring

/-- Coefficient of the oriented volume form in the wedge of two degree-two classes. -/
public def degreeTwoIntersection (x y : DegreeTwoLattice) : ℤ :=
  x 0 * y 5 - x 1 * y 4 + x 2 * y 3 + x 3 * y 2 - x 4 * y 1 + x 5 * y 0

public theorem orderThree_invariant_gram :
    degreeTwoIntersection gammaEpsilonOne gammaEpsilonOne = 0 ∧
      degreeTwoIntersection gammaEpsilonOne qClass = 3 ∧
      degreeTwoIntersection qClass qClass = 12 := by
  norm_num [degreeTwoIntersection, gammaEpsilonOne, qClass]; decide

public theorem orderFour_invariant_gram :
    degreeTwoIntersection gammaEpsilonTwo gammaEpsilonTwo = 0 ∧
      degreeTwoIntersection gammaEpsilonTwo qClass = 2 ∧
      degreeTwoIntersection qClass qClass = 12 := by
  norm_num [degreeTwoIntersection, gammaEpsilonTwo, qClass]; decide

/-- The exterior-square action as an integral linear map. -/
public def degreeTwoAction (M : Matrix (Fin 4) (Fin 4) ℤ) :
    DegreeTwoLattice →ₗ[ℤ] DegreeTwoLattice :=
  Matrix.toLin' (secondCompoundMatrix M)

/-- The fixed lattice of an exterior-square action. -/
public abbrev DegreeTwoInvariants (M : Matrix (Fin 4) (Fin 4) ℤ) :=
  LinearMap.ker (degreeTwoAction M - LinearMap.id)

public abbrev OrderThreeDegreeTwoInvariants := DegreeTwoInvariants T₁

public abbrev OrderFourDegreeTwoInvariants := DegreeTwoInvariants T₂

public theorem mem_degreeTwoInvariants_iff
    {M : Matrix (Fin 4) (Fin 4) ℤ} {x : DegreeTwoLattice} :
    x ∈ DegreeTwoInvariants M ↔ secondCompoundMatrix M *ᵥ x = x := by
  simp [DegreeTwoInvariants, degreeTwoAction, sub_eq_zero]

public theorem orderThree_combination_fixed (a b : ℤ) :
    a • gammaEpsilonOne + b • qClass ∈ OrderThreeDegreeTwoInvariants := by
  rw [mem_degreeTwoInvariants_iff, orderThreeDegreeTwo_fixed_iff]
  exact ⟨a, b, rfl⟩

public theorem orderFour_combination_fixed (a b : ℤ) :
    a • gammaEpsilonTwo + b • qClass ∈ OrderFourDegreeTwoInvariants := by
  rw [mem_degreeTwoInvariants_iff, orderFourDegreeTwo_fixed_iff]
  exact ⟨a, b, rfl⟩

/-- Coordinates in the basis `(gamma ∧ epsilonOne, q)`. -/
public noncomputable def orderThreeInvariantEquivIntSquared :
    OrderThreeDegreeTwoInvariants ≃ₗ[ℤ] IntSquared where
  toFun x := ![x.1 1, x.1 3]
  invFun c := ⟨c 0 • gammaEpsilonOne + c 1 • qClass,
    orderThree_combination_fixed (c 0) (c 1)⟩
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
  left_inv x := by
    apply Subtype.ext
    have hxmem := x.2
    rw [mem_degreeTwoInvariants_iff, orderThreeDegreeTwo_fixed_iff] at hxmem
    obtain ⟨a, b, hx⟩ := hxmem
    have hx1 := congrFun hx (1 : Fin 6)
    have hx3 := congrFun hx (3 : Fin 6)
    simp [gammaEpsilonOne, qClass] at hx1 hx3
    change x.1 1 • gammaEpsilonOne + x.1 3 • qClass = x.1
    rw [hx1, hx3, hx]
  right_inv c := by
    funext i
    fin_cases i <;> simp [gammaEpsilonOne, qClass]

/-- Coordinates in the basis `(gamma ∧ epsilonTwo, q)`. -/
public noncomputable def orderFourInvariantEquivIntSquared :
    OrderFourDegreeTwoInvariants ≃ₗ[ℤ] IntSquared where
  toFun x := ![x.1 0, x.1 3]
  invFun c := ⟨c 0 • gammaEpsilonTwo + c 1 • qClass,
    orderFour_combination_fixed (c 0) (c 1)⟩
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
  left_inv x := by
    apply Subtype.ext
    have hxmem := x.2
    rw [mem_degreeTwoInvariants_iff, orderFourDegreeTwo_fixed_iff] at hxmem
    obtain ⟨a, b, hx⟩ := hxmem
    have hx0 := congrFun hx (0 : Fin 6)
    have hx3 := congrFun hx (3 : Fin 6)
    simp [gammaEpsilonTwo, qClass] at hx0 hx3
    change x.1 0 • gammaEpsilonTwo + x.1 3 • qClass = x.1
    rw [hx0, hx3, hx]
  right_inv c := by
    funext i
    fin_cases i <;> simp [gammaEpsilonTwo, qClass]

/-- The degree-two order-three candidate is the whole invariant lattice, hence has index one. -/
public def orderThreeDegreeTwoPullbackCandidate :
    Submodule ℤ OrderThreeDegreeTwoInvariants := ⊤

/-- Reduction of the difference of the two invariant coordinates modulo two. -/
public def orderFourParity : OrderFourDegreeTwoInvariants →ₗ[ℤ] ZMod 2 where
  toFun x := (x.1 0 : ZMod 2) - (x.1 3 : ZMod 2)
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

/-- The index-two candidate from the source: coefficients of `gamma ∧ epsilonTwo` and `q`
have the same parity. -/
public def orderFourDegreeTwoPullbackCandidate :
    Submodule ℤ OrderFourDegreeTwoInvariants :=
  LinearMap.ker orderFourParity

public theorem orderFourParity_surjective : Function.Surjective orderFourParity := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨⟨n • gammaEpsilonTwo, ?_⟩, ?_⟩
  · simpa using orderFour_combination_fixed n 0
  · simp [orderFourParity, gammaEpsilonTwo]

/-- The candidate cokernel at the order-four fibre is exactly cyclic of order two. -/
public noncomputable def orderFourCandidateQuotientEquivZModTwo :
    (OrderFourDegreeTwoInvariants ⧸ orderFourDegreeTwoPullbackCandidate) ≃ₗ[ℤ] ZMod 2 :=
  orderFourParity.quotKerEquivOfSurjective orderFourParity_surjective

public def orderFourQInvariant : OrderFourDegreeTwoInvariants :=
  ⟨qClass, by simpa using orderFour_combination_fixed 0 1⟩

/-- The class of `q` generates the index-two candidate cokernel. -/
@[simp]
public theorem orderFourCandidateQuotientEquivZModTwo_q :
    orderFourCandidateQuotientEquivZModTwo
        (Submodule.Quotient.mk orderFourQInvariant) = 1 := by
  rfl

public theorem orderFourQInvariant_not_mem_candidate :
    orderFourQInvariant ∉ orderFourDegreeTwoPullbackCandidate := by
  intro h
  have hz := LinearMap.mem_ker.mp h
  change (1 : ZMod 2) = 0 at hz
  norm_num at hz

/-- Membership in the index-two candidate is the parity condition printed in the source. -/
public theorem mem_orderFourDegreeTwoPullbackCandidate_iff
    (x : OrderFourDegreeTwoInvariants) :
    x ∈ orderFourDegreeTwoPullbackCandidate ↔
      (x.1 0 : ZMod 2) = (x.1 3 : ZMod 2) := by
  simp [orderFourDegreeTwoPullbackCandidate, orderFourParity, sub_eq_zero]

end SphereSixComplex.Topology.PaperPropositionSevenFourteenDegreeTwoAlgebra
