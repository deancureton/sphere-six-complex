module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombCyclicOverlapIdentity

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
namespace Construction






public theorem cellTransitionMatrix_zero_three (v : ToricLattice) :
    transitionMatrix (cellChart v 0) (cellChart v 3) =
      !![(0 : ℤ), 0, -1; 0, -1, 0; 1, 2, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cellChart, transitionMatrix, dualMatrix,
      a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
      Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem planeTile_zero_eq_three_iff
    (v : ToricLattice) (p q : CellSquare) :
    planeTile v 0 p = planeTile v 3 q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hq0 := q.2 0
  have hq1 := q.2 1
  constructor
  · intro h
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [planeTile_of_le v 0 p hp,
          planeTile_of_le v 3 q hq] at h
      | rw [planeTile_of_le v 0 p hp,
          planeTile_of_ge v 3 q hq] at h
      | rw [planeTile_of_ge v 0 p hp,
          planeTile_of_le v 3 q hq] at h
      | rw [planeTile_of_ge v 0 p hp,
          planeTile_of_ge v 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset] at h0 h1
      have hp0eq : p.1 0 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hp1eq : p.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq0eq : q.1 0 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq1eq : q.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      exact ⟨hp0eq, hp1eq, hq0eq, hq1eq⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [planeTile, hp0, hp1, hq0, hq1,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset]

public theorem zero_three_transition_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 0) (cellChart v 3)) ∧
      monomial
          (transitionMatrix (cellChart v 0) (cellChart v 3))
          (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [cellTransitionMatrix_zero_three]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [cellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [cellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1
    have hprod1 : p.1 1 * q.1 1 = 1 := by
      field_simp [hp1c] at heq0
      exact (by exact_mod_cast congrArg Complex.re heq0.symm)
    have hprod0 : p.1 0 * q.1 0 = 1 := by
      field_simp [hp0c] at heq1
      exact (by exact_mod_cast congrArg Complex.re heq1.symm)
    have hp1q1_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1eq : q.1 1 = 1 :=
      (q.2 1).2.antisymm (hprod1.ge.trans hp1q1_le)
    have hp1eq : p.1 1 = 1 := by
      rw [hq1eq] at hprod1
      simpa using hprod1
    have hp0q0_le : p.1 0 * q.1 0 ≤ q.1 0 :=
      mul_le_of_le_one_left (q.2 0).1 (p.2 0).2
    have hq0eq : q.1 0 = 1 :=
      (q.2 0).2.antisymm (hprod0.ge.trans hp0q0_le)
    have hp0eq : p.1 0 = 1 := by
      rw [hq0eq] at hprod0
      simpa using hprod0
    exact ⟨hp0eq, hp1eq, hq0eq, hq1eq⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem honeycombLaurentFiniteIdentity_zero_three
    (v : ToricLattice) (p q : CellSquare) :
    planeTile v 0 p = planeTile v 3 q ↔
      cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 0) (cellChart v 3)) ∧
        monomial
            (transitionMatrix (cellChart v 0) (cellChart v 3))
            (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) :=
  (planeTile_zero_eq_three_iff v p q).trans
    (zero_three_transition_iff v p q).symm

public theorem laurentTransition_comm
    (v w : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v i) (cellChart w j)) ∧
      monomial
          (transitionMatrix (cellChart v i) (cellChart w j))
          (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) ↔
    (cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart w j) (cellChart v i)) ∧
      monomial
          (transitionMatrix (cellChart w j) (cellChart v i))
          (cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) =
        cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) := by
  rw [← cellSquareProjection_eq_iff_monomial
      (r := 1) zero_lt_one v w i j p q,
    ← cellSquareProjection_eq_iff_monomial
      (r := 1) zero_lt_one w v j i q p]
  exact eq_comm






end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
