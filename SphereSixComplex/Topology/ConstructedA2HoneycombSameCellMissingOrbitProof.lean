module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedCellGeometry

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2CellTransitionMatrix_four_zero (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 4) (constructedA2CellChart v 0) =
      !![(2 : ℤ), 1, 1; 0, 1, 0; -1, -1, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2PlaneTile_four_eq_zero_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 4 p = constructedA2PlaneTile v 0 q ↔
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
      | rw [constructedA2PlaneTile_of_le v 4 p hp,
          constructedA2PlaneTile_of_le v 0 q hq] at h
      | rw [constructedA2PlaneTile_of_le v 4 p hp,
          constructedA2PlaneTile_of_ge v 0 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 4 p hp,
          constructedA2PlaneTile_of_le v 0 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 4 p hp,
          constructedA2PlaneTile_of_ge v 0 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset]

public theorem constructedA2_four_zero_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 4 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 4) (constructedA2CellChart v 0)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 4) (constructedA2CellChart v 0))
          (constructedA2CellLiftCoordinates 4 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 0 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_four_zero]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (2 : Fin 3) (1 : Fin 3) (by decide)
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq1 heq2
    have hprod : p.1 0 * p.1 1 * q.1 1 = 1 := by
      field_simp [hp0c, hp1c] at heq2
      exact (by exact_mod_cast congrArg Complex.re heq2.symm)
    have hbc : 1 ≤ p.1 1 * q.1 1 := by
      have hn : 0 ≤ (1 - p.1 0) * (p.1 1 * q.1 1) :=
        mul_nonneg (sub_nonneg.mpr (p.2 0).2)
          (mul_nonneg (p.2 1).1 (q.2 1).1)
      nlinarith
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hbc.trans hpq_le)
    have hp1 : p.1 1 = 1 := by
      have : 1 ≤ p.1 1 := by simpa [hq1] using hbc
      exact (p.2 1).2.antisymm this
    have hp0 : p.1 0 = 1 := by
      rw [hp1, hq1] at hprod
      simpa using hprod
    have hq0 : q.1 0 = 1 := by
      exact_mod_cast heq1.symm.trans (by exact_mod_cast hp1)
    exact ⟨hp0, hp1, hq0, hq1⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_four_zero
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 4 p = constructedA2CorrectedPlaneTile v 0 q ↔
      constructedA2CellLiftCoordinates 4 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 4) (constructedA2CellChart v 0)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 4) (constructedA2CellChart v 0))
            (constructedA2CellLiftCoordinates 4 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 0 (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CorrectedPlaneTile_sameCell_iff,
    constructedA2PlaneTile_four_eq_zero_iff, constructedA2_four_zero_transition_iff]

public theorem constructedA2CorrectedLaurentIdentity_zero_four
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 0 p = constructedA2CorrectedPlaneTile v 4 q ↔
      constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 4)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 4))
            (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ)) :=
  constructedA2CorrectedLaurentIdentity_reverse v v 4 0 q p
    (constructedA2CorrectedLaurentIdentity_four_zero v q p)

public theorem constructedA2CellTransitionMatrix_one_three (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 3) =
      !![(0 : ℤ), -1, -1; 0, 1, 0; 1, 1, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2PlaneTile_one_eq_three_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 1 p = constructedA2PlaneTile v 3 q ↔
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
      | rw [constructedA2PlaneTile_of_le v 1 p hp,
          constructedA2PlaneTile_of_le v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_le v 1 p hp,
          constructedA2PlaneTile_of_ge v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 1 p hp,
          constructedA2PlaneTile_of_le v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 1 p hp,
          constructedA2PlaneTile_of_ge v 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset]

public theorem constructedA2_one_three_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 3)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 3))
          (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_one_three]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1
    have hprod : p.1 0 * p.1 1 * q.1 1 = 1 := by
      field_simp [hp0c, hp1c] at heq0
      have hprod' : p.1 1 * p.1 0 * q.1 1 = 1 := by
        exact_mod_cast congrArg Complex.re heq0.symm
      simpa [mul_comm] using hprod'
    have hbc : 1 ≤ p.1 1 * q.1 1 := by
      have hn : 0 ≤ (1 - p.1 0) * (p.1 1 * q.1 1) :=
        mul_nonneg (sub_nonneg.mpr (p.2 0).2)
          (mul_nonneg (p.2 1).1 (q.2 1).1)
      nlinarith
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hbc.trans hpq_le)
    have hp1 : p.1 1 = 1 := by
      have : 1 ≤ p.1 1 := by simpa [hq1] using hbc
      exact (p.2 1).2.antisymm this
    have hp0 : p.1 0 = 1 := by
      rw [hp1, hq1] at hprod
      simpa using hprod
    have hq0 : q.1 0 = 1 := by
      exact_mod_cast heq1.symm.trans (by exact_mod_cast hp1)
    exact ⟨hp0, hp1, hq0, hq1⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_one_three
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 1 p = constructedA2CorrectedPlaneTile v 3 q ↔
      constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 3)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 3))
            (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CorrectedPlaneTile_sameCell_iff,
    constructedA2PlaneTile_one_eq_three_iff, constructedA2_one_three_transition_iff]

public theorem constructedA2CorrectedLaurentIdentity_three_one
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 3 p = constructedA2CorrectedPlaneTile v 1 q ↔
      constructedA2CellLiftCoordinates 3 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 3) (constructedA2CellChart v 1)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 3) (constructedA2CellChart v 1))
            (constructedA2CellLiftCoordinates 3 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 1 (fun k ↦ (q.1 k : ℂ)) :=
  constructedA2CorrectedLaurentIdentity_reverse v v 1 3 q p
    (constructedA2CorrectedLaurentIdentity_one_three v q p)

public theorem constructedA2PlaneTile_eq_secondNext_iff
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p =
        constructedA2PlaneTile v
          (constructedA2CellNextIndex (constructedA2CellNextIndex i)) q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hq0 := q.2 0
  have hq1 := q.2 1
  constructor
  · intro h
    fin_cases i
    all_goals
      rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
        rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [constructedA2PlaneTile_of_le _ _ p hp,
          constructedA2PlaneTile_of_le _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_le _ _ p hp,
          constructedA2PlaneTile_of_ge _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_ge _ _ p hp,
          constructedA2PlaneTile_of_le _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_ge _ _ p hp,
          constructedA2PlaneTile_of_ge _ _ q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2CellNextIndex, constructedA2PlaneVertexOffset,
        constructedA2PlaneMidpointOffset, constructedA2PlaneNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1]

public def constructedA2DistanceTwoTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![(0 : ℤ), -1, -1; 1, 2, 1; 0, 0, 1],
    !![(0 : ℤ), -1, -1; 0, 1, 0; 1, 1, 2],
    !![(1 : ℤ), 0, 0; -1, 0, -1; 1, 1, 2],
    !![(1 : ℤ), 0, 0; 1, 2, 1; -1, -1, 0],
    !![(2 : ℤ), 1, 1; 0, 1, 0; -1, -1, 0],
    !![(2 : ℤ), 1, 1; -1, 0, -1; 0, 0, 1]]

public theorem constructedA2CellTransitionMatrix_secondNext
    (v : ToricLattice) (i : Fin 6) :
    transitionMatrix (constructedA2CellChart v i)
        (constructedA2CellChart v
          (constructedA2CellNextIndex (constructedA2CellNextIndex i))) =
      constructedA2DistanceTwoTransitionMatrix i := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  fin_cases i <;>
    ext a b <;>
    fin_cases a <;>
    fin_cases b <;>
    simp [constructedA2DistanceTwoTransitionMatrix, constructedA2CellChart,
      constructedA2CellNextIndex, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem constructedA2_all_one_of_inverse_product
    (p q : ConstructedA2CellSquare)
    (hp0c : (p.1 0 : ℂ) ≠ 0) (hp1c : (p.1 1 : ℂ) ≠ 0)
    (hinv : ((p.1 0 : ℂ)⁻¹) * ((p.1 1 : ℂ)⁻¹) = (q.1 1 : ℂ))
    (hpq : (p.1 1 : ℂ) = (q.1 0 : ℂ)) :
    p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  have hprod : p.1 0 * p.1 1 * q.1 1 = 1 := by
    field_simp [hp0c, hp1c] at hinv
    exact_mod_cast congrArg Complex.re hinv.symm
  have hbc : 1 ≤ p.1 1 * q.1 1 := by
    have hn : 0 ≤ (1 - p.1 0) * (p.1 1 * q.1 1) :=
      mul_nonneg (sub_nonneg.mpr (p.2 0).2)
        (mul_nonneg (p.2 1).1 (q.2 1).1)
    nlinarith
  have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
    mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
  have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hbc.trans hpq_le)
  have hp1 : p.1 1 = 1 := by
    have : 1 ≤ p.1 1 := by simpa [hq1] using hbc
    exact (p.2 1).2.antisymm this
  have hp0 : p.1 0 = 1 := by
    rw [hp1, hq1] at hprod
    simpa using hprod
  have hq0 : q.1 0 = 1 := by
    have hq0c : (q.1 0 : ℂ) = 1 := hpq.symm.trans (by exact_mod_cast hp1)
    exact_mod_cast hq0c
  exact ⟨hp0, hp1, hq0, hq1⟩

public theorem constructedA2_secondNext_transition_iff
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v i)
            (constructedA2CellChart v
              (constructedA2CellNextIndex (constructedA2CellNextIndex i)))) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v i)
            (constructedA2CellChart v
              (constructedA2CellNextIndex (constructedA2CellNextIndex i))))
          (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates
          (constructedA2CellNextIndex (constructedA2CellNextIndex i))
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_secondNext]
  constructor
  · rintro ⟨hdomain, heq⟩
    fin_cases i
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial, mul_comm,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (1 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (1 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial, mul_comm,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (2 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial, mul_comm,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (2 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
    · apply constructedA2_all_one_of_inverse_product p q
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (1 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix,
          constructedA2CellLiftCoordinates] using
          hdomain (1 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
      · simpa [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex, monomial,
          constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    fin_cases i
    all_goals
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;>
          simp_all [constructedA2DistanceTwoTransitionMatrix,
            constructedA2CellLiftCoordinates]
      · ext k
        fin_cases k <;>
          simp [constructedA2DistanceTwoTransitionMatrix, constructedA2CellNextIndex,
            monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
            hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_secondNext
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p =
        constructedA2CorrectedPlaneTile v
          (constructedA2CellNextIndex (constructedA2CellNextIndex i)) q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v
                (constructedA2CellNextIndex (constructedA2CellNextIndex i)))) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v
                (constructedA2CellNextIndex (constructedA2CellNextIndex i))))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates
            (constructedA2CellNextIndex (constructedA2CellNextIndex i))
            (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CorrectedPlaneTile_sameCell_iff,
    constructedA2PlaneTile_eq_secondNext_iff, constructedA2_secondNext_transition_iff]

public theorem constructedA2PlaneTile_eq_thirdNext_iff
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p =
        constructedA2PlaneTile v
          (constructedA2CellNextIndex
            (constructedA2CellNextIndex (constructedA2CellNextIndex i))) q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hq0 := q.2 0
  have hq1 := q.2 1
  constructor
  · intro h
    fin_cases i
    all_goals
      rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
        rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [constructedA2PlaneTile_of_le _ _ p hp,
          constructedA2PlaneTile_of_le _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_le _ _ p hp,
          constructedA2PlaneTile_of_ge _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_ge _ _ p hp,
          constructedA2PlaneTile_of_le _ _ q hq] at h
      | rw [constructedA2PlaneTile_of_ge _ _ p hp,
          constructedA2PlaneTile_of_ge _ _ q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2CellNextIndex, constructedA2PlaneVertexOffset,
        constructedA2PlaneMidpointOffset, constructedA2PlaneNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1]

private theorem constructedA2_all_one_of_two_inverses
    (p q : ConstructedA2CellSquare)
    (hp0c : (p.1 0 : ℂ) ≠ 0) (hp1c : (p.1 1 : ℂ) ≠ 0)
    (h0 : (p.1 0 : ℂ)⁻¹ = (q.1 0 : ℂ))
    (h1 : (p.1 1 : ℂ)⁻¹ = (q.1 1 : ℂ)) :
    p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  have hprod0 : p.1 0 * q.1 0 = 1 := by
    field_simp [hp0c] at h0
    exact_mod_cast congrArg Complex.re h0.symm
  have hprod1 : p.1 1 * q.1 1 = 1 := by
    field_simp [hp1c] at h1
    exact_mod_cast congrArg Complex.re h1.symm
  have hq0 : q.1 0 = 1 := by
    have hle : p.1 0 * q.1 0 ≤ q.1 0 :=
      mul_le_of_le_one_left (q.2 0).1 (p.2 0).2
    exact (q.2 0).2.antisymm (hprod0.ge.trans hle)
  have hp0 : p.1 0 = 1 := by
    rw [hq0] at hprod0
    simpa using hprod0
  have hq1 : q.1 1 = 1 := by
    have hle : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    exact (q.2 1).2.antisymm (hprod1.ge.trans hle)
  have hp1 : p.1 1 = 1 := by
    rw [hq1] at hprod1
    simpa using hprod1
  exact ⟨hp0, hp1, hq0, hq1⟩

public theorem constructedA2CellTransitionMatrix_one_four (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 4) =
      !![(0 : ℤ), 0, -1; 0, -1, 0; 1, 2, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2_one_four_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 4)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 4))
          (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_one_four]
  constructor
  · rintro ⟨hdomain, heq⟩
    apply constructedA2_all_one_of_two_inverses p q
    · simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    · simpa [constructedA2CellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    · simpa [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 0
    · simpa [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 1
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CellTransitionMatrix_two_five (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 2) (constructedA2CellChart v 5) =
      !![(0 : ℤ), 0, -1; 2, 1, 2; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2_two_five_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 2) (constructedA2CellChart v 5)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 2) (constructedA2CellChart v 5))
          (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_two_five]
  constructor
  · rintro ⟨hdomain, heq⟩
    apply constructedA2_all_one_of_two_inverses p q
    · simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    · simpa [constructedA2CellLiftCoordinates] using
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    · simpa [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 0
    · simpa [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 2
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_one_four
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 1 p = constructedA2CorrectedPlaneTile v 4 q ↔
      constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 4)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 1) (constructedA2CellChart v 4))
            (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CorrectedPlaneTile_sameCell_iff]
  have hplane := constructedA2PlaneTile_eq_thirdNext_iff v (1 : Fin 6) p q
  have hplane' : constructedA2PlaneTile v 1 p = constructedA2PlaneTile v 4 q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
    simpa [constructedA2CellNextIndex] using hplane
  exact hplane'.trans (constructedA2_one_four_transition_iff v p q).symm

public theorem constructedA2CorrectedLaurentIdentity_two_five
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 2 p = constructedA2CorrectedPlaneTile v 5 q ↔
      constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 2) (constructedA2CellChart v 5)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 2) (constructedA2CellChart v 5))
            (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CorrectedPlaneTile_sameCell_iff]
  have hplane := constructedA2PlaneTile_eq_thirdNext_iff v (2 : Fin 6) p q
  have hplane' : constructedA2PlaneTile v 2 p = constructedA2PlaneTile v 5 q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
    simpa [constructedA2CellNextIndex] using hplane
  exact hplane'.trans (constructedA2_two_five_transition_iff v p q).symm

public theorem constructedA2CorrectedLaurentIdentity_thirdNext
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p =
        constructedA2CorrectedPlaneTile v
          (constructedA2CellNextIndex
            (constructedA2CellNextIndex (constructedA2CellNextIndex i))) q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v
                (constructedA2CellNextIndex
                  (constructedA2CellNextIndex (constructedA2CellNextIndex i))))) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v
                (constructedA2CellNextIndex
                  (constructedA2CellNextIndex (constructedA2CellNextIndex i)))))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates
            (constructedA2CellNextIndex
              (constructedA2CellNextIndex (constructedA2CellNextIndex i)))
            (fun k ↦ (q.1 k : ℂ)) := by
  have h03 (a b : ConstructedA2CellSquare) :=
    constructedA2CorrectedLaurentIdentity_of_sameCell v 0 3 a b
      (constructedA2HoneycombLaurentFiniteIdentity_zero_three v a b)
  fin_cases i
  · simpa [constructedA2CellNextIndex] using h03 p q
  · simpa [constructedA2CellNextIndex] using
      constructedA2CorrectedLaurentIdentity_one_four v p q
  · simpa [constructedA2CellNextIndex] using
      constructedA2CorrectedLaurentIdentity_two_five v p q
  · simpa [constructedA2CellNextIndex] using
      constructedA2CorrectedLaurentIdentity_reverse v v 0 3 q p (h03 q p)
  · simpa [constructedA2CellNextIndex] using
      constructedA2CorrectedLaurentIdentity_reverse v v 1 4 q p
        (constructedA2CorrectedLaurentIdentity_one_four v q p)
  · simpa [constructedA2CellNextIndex] using
      constructedA2CorrectedLaurentIdentity_reverse v v 2 5 q p
        (constructedA2CorrectedLaurentIdentity_two_five v q p)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
