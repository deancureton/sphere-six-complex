module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombSameCellMissingOrbit

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public theorem neighborChart_zero_two (v : ToricLattice) :
    cellChart v 0 = cellChart (v + e₁) 2 := by
  simp [cellChart]

public theorem correctedPlaneTile_neighbor_zero_two_iff
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 0 p =
        correctedPlaneTile (v + e₁) 2 q ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
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
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 0 p hp,
          planeTile_of_le (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 0 p hp,
          planeTile_of_ge (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 0 p hp,
          planeTile_of_le (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 0 p hp,
          planeTile_of_ge (v + e₁) 2 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [correctedPlaneCenter, Pi.add_apply,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hq1, hpq⟩
    have hp : p.1 0 ≤ p.1 1 := by linarith [(p.2 1).1]
    have hq : q.1 1 ≤ q.1 0 := by linarith [(q.2 0).1]
    rw [correctedPlaneTile, correctedPlaneTile,
      planeTile_of_le v 0 p hp,
      planeTile_of_ge (v + e₁) 2 q hq]
    ext k
    fin_cases k <;>
      simp [correctedPlaneCenter, Pi.add_apply,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁, hp0, hq1, hpq] <;>
      ring

public theorem neighborTransition_zero_two_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 0)
            (cellChart (v + e₁) 2)) ∧
      monomial
          (transitionMatrix (cellChart v 0)
            (cellChart (v + e₁) 2))
          (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  rw [← neighborChart_zero_two v, transitionMatrix_self, monomial_one]
  constructor
  · rintro ⟨-, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [cellLiftCoordinates] at h0 h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h0.symm, by exact_mod_cast h2⟩
  · rintro ⟨hp0, hq1, hpq⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
    · ext k
      fin_cases k <;>
        simp [cellLiftCoordinates, hp0, hq1, hpq]


public theorem neighborChart_five_three (v : ToricLattice) :
    cellChart v 5 = cellChart (v + e₁) 3 := by
  simp [cellChart]

public theorem correctedPlaneTile_neighbor_five_three_iff
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 5 p =
        correctedPlaneTile (v + e₁) 3 q ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
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
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 5 p hp,
          planeTile_of_le (v + e₁) 3 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 5 p hp,
          planeTile_of_ge (v + e₁) 3 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 5 p hp,
          planeTile_of_le (v + e₁) 3 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 5 p hp,
          planeTile_of_ge (v + e₁) 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [correctedPlaneCenter, Pi.add_apply,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp1, hq0, hpq⟩
    have hp : p.1 1 ≤ p.1 0 := by linarith [(p.2 0).1]
    have hq : q.1 0 ≤ q.1 1 := by linarith [(q.2 1).1]
    rw [correctedPlaneTile, correctedPlaneTile,
      planeTile_of_ge v 5 p hp,
      planeTile_of_le (v + e₁) 3 q hq]
    ext k
    fin_cases k <;>
      simp [correctedPlaneCenter, Pi.add_apply,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁, hp1, hq0, hpq] <;>
      ring

public theorem neighborTransition_five_three_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 5)
            (cellChart (v + e₁) 3)) ∧
      monomial
          (transitionMatrix (cellChart v 5)
            (cellChart (v + e₁) 3))
          (cellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  rw [← neighborChart_five_three v, transitionMatrix_self, monomial_one]
  constructor
  · rintro ⟨-, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [cellLiftCoordinates] at h0 h1 h2
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1.symm, by exact_mod_cast h0⟩
  · rintro ⟨hp1, hq0, hpq⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
    · ext k
      fin_cases k <;>
        simp [cellLiftCoordinates, hp1, hq0, hpq]


public theorem correctedPlaneTile_neighbor_five_two_iff
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 5 p =
        correctedPlaneTile (v + e₁) 2 q ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
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
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 5 p hp,
          planeTile_of_le (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_le v 5 p hp,
          planeTile_of_ge (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 5 p hp,
          planeTile_of_le (v + e₁) 2 q hq] at h
      | rw [correctedPlaneTile, correctedPlaneTile,
          planeTile_of_ge v 5 p hp,
          planeTile_of_ge (v + e₁) 2 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [correctedPlaneCenter, Pi.add_apply,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [correctedPlaneTile, correctedPlaneCenter,
        planeTile, planeVertexOffset,
        planeMidpointOffset, planeNextMidpointOffset,
        hp0, hp1, hq0, hq1, e₁] <;>
      ring

public theorem neighborTransition_five_two_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 5)
            (cellChart (v + e₁) 2)) ∧
      monomial
          (transitionMatrix (cellChart v 5)
            (cellChart (v + e₁) 2))
          (cellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  rw [show transitionMatrix (cellChart v 5)
      (cellChart (v + e₁) 2) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] by
    have hv0 : Matrix.vecHead v = v 0 := rfl
    have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [cellChart, transitionMatrix, dualMatrix,
        a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
        Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [cellLiftCoordinates] using
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
    have hprod : p.1 0 * q.1 0 = 1 := by
      field_simp [hp0c] at heq2
      exact (by exact_mod_cast congrArg Complex.re heq2.symm)
    have hpq_le : p.1 0 * q.1 0 ≤ q.1 0 :=
      mul_le_of_le_one_left (q.2 0).1 (p.2 0).2
    have hq0 : q.1 0 = 1 := (q.2 0).2.antisymm (hprod.ge.trans hpq_le)
    have hp0 : p.1 0 = 1 := by rw [hq0] at hprod; simpa using hprod
    have hp1 : p.1 1 = 0 := by
      rcases heq1 with hp0zero | hp1zero
      · have hp0r : p.1 0 ≠ 0 := by exact_mod_cast hp0c
        exact (hp0r hp0zero).elim
      · exact_mod_cast hp1zero
    have hq1 : q.1 1 = 0 := by exact_mod_cast heq0.symm
    exact ⟨hp0, hp1, hq0, hq1⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]


public theorem neighbor_e1_chartIncidence
    (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart (v + e₁) j)) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart (v + e₁) j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    (i = 0 ∨ i = 5) ∧ (j = 2 ∨ j = 3) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    laurentRelation_chartIncidence v (v + e₁) i j p q h
  constructor
  · fin_cases i <;> fin_cases a <;>
      simp [cellChart, a2Triangle, e₁, e₂, sub_eq_add_neg] at ha ⊢
  · fin_cases j <;> fin_cases b <;>
      simp [cellChart, a2Triangle, e₁, e₂, sub_eq_add_neg] at hb ⊢
    all_goals
      have hv0 : Matrix.vecHead v = v 0 := rfl
      have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
      have hb0 := congrFun hb 0
      have hb1 := congrFun hb 1
      simp at hb0 hb1
      omega

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
