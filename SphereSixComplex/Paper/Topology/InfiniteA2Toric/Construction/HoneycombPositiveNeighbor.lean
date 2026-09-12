module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombNeighborBoundary

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric

public def positiveNeighborDisplacement : Fin 3 → ToricLattice :=
  ![e₁, e₂, e₂ - e₁]

public def positiveNeighborSource : Fin 3 → Fin 6 := ![0, 1, 2]

public def positiveNeighborPreviousSource : Fin 3 → Fin 6 := ![5, 0, 1]

public def positiveNeighborTargetLow : Fin 3 → Fin 6 := ![2, 3, 4]

public def positiveNeighborTargetHigh : Fin 3 → Fin 6 := ![3, 4, 5]

public theorem positiveNeighborChart_low
    (r : Fin 3) (v : ToricLattice) :
    cellChart v (positiveNeighborSource r) =
      cellChart (v + positiveNeighborDisplacement r)
        (positiveNeighborTargetLow r) := by
  fin_cases r <;>
    simp [positiveNeighborSource, positiveNeighborDisplacement,
      positiveNeighborTargetLow, cellChart, e₁, e₂]
  all_goals first | ring | (ext k; fin_cases k <;> rfl)

public theorem correctedPlaneTile_positiveNeighbor_low_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetLow r) q ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  fin_cases r
  · exact correctedPlaneTile_neighbor_zero_two_iff v p q
  all_goals
    dsimp [positiveNeighborSource, positiveNeighborDisplacement,
      positiveNeighborTargetLow]
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
            planeTile_of_le _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_le _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [correctedPlaneCenter, Pi.add_apply,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset, e₁, e₂] at h0 h1
        norm_num [div_eq_mul_inv] at h0 h1
        refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
    · rintro ⟨hp0, hq1, hpq⟩
      have hp : p.1 0 ≤ p.1 1 := by linarith [(p.2 1).1]
      have hq : q.1 1 ≤ q.1 0 := by linarith [(q.2 0).1]
      rw [correctedPlaneTile, correctedPlaneTile,
        planeTile_of_le _ _ p hp,
        planeTile_of_ge _ _ q hq]
      ext k
      fin_cases k <;>
        simp [correctedPlaneCenter, Pi.add_apply,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset, e₁, e₂, hp0, hq1, hpq] <;>
        ring

public theorem positiveNeighborTransition_low_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates (positiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r)))
          (cellLiftCoordinates (positiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  fin_cases r
  · exact neighborTransition_zero_two_iff v p q
  ·
    dsimp [positiveNeighborSource, positiveNeighborTargetLow]
    have hchart : cellChart v 1 =
        cellChart (v + positiveNeighborDisplacement 1) 3 := by
      simpa [positiveNeighborSource, positiveNeighborTargetLow] using
        positiveNeighborChart_low 1 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [cellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h0.symm,
        by exact_mod_cast h1⟩
    · rintro ⟨hp0, hq1, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [cellLiftCoordinates, hp0, hq1, hpq]
  ·
    dsimp [positiveNeighborSource, positiveNeighborTargetLow]
    have hchart : cellChart v 2 =
        cellChart (v + positiveNeighborDisplacement 2) 4 := by
      simpa [positiveNeighborSource, positiveNeighborTargetLow] using
        positiveNeighborChart_low 2 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [cellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1.symm,
        by exact_mod_cast h0⟩
    · rintro ⟨hp0, hq1, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [cellLiftCoordinates, hp0, hq1, hpq]

public theorem correctedLaurentIdentity_positiveNeighbor_low
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetLow r) q ↔
      cellLiftCoordinates (positiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r)))
          (cellLiftCoordinates (positiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_positiveNeighbor_low_iff r v p q).trans
    (positiveNeighborTransition_low_iff r v p q).symm

public theorem positiveNeighborChart_high
    (r : Fin 3) (v : ToricLattice) :
    cellChart v (positiveNeighborPreviousSource r) =
      cellChart (v + positiveNeighborDisplacement r)
        (positiveNeighborTargetHigh r) := by
  fin_cases r <;>
    simp [positiveNeighborPreviousSource,
      positiveNeighborDisplacement, positiveNeighborTargetHigh,
      cellChart, e₁, e₂]
  all_goals first | ring | (ext k; fin_cases k <;> rfl)

public theorem correctedPlaneTile_positiveNeighbor_high_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborPreviousSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetHigh r) q ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  fin_cases r
  · exact correctedPlaneTile_neighbor_five_three_iff v p q
  all_goals
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborDisplacement, positiveNeighborTargetHigh]
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
            planeTile_of_le _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_le _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [correctedPlaneCenter, Pi.add_apply,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset, e₁, e₂] at h0 h1
        norm_num [div_eq_mul_inv] at h0 h1
        refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
    · rintro ⟨hp1, hq0, hpq⟩
      have hp : p.1 1 ≤ p.1 0 := by linarith [(p.2 0).1]
      have hq : q.1 0 ≤ q.1 1 := by linarith [(q.2 1).1]
      rw [correctedPlaneTile, correctedPlaneTile,
        planeTile_of_ge _ _ p hp,
        planeTile_of_le _ _ q hq]
      ext k
      fin_cases k <;>
        simp [correctedPlaneCenter, Pi.add_apply,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset, e₁, e₂, hp1, hq0, hpq] <;>
        ring

public theorem positiveNeighborTransition_high_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates (positiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r)))
          (cellLiftCoordinates (positiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  fin_cases r
  · exact neighborTransition_five_three_iff v p q
  ·
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborTargetHigh]
    have hchart : cellChart v 0 =
        cellChart (v + positiveNeighborDisplacement 1) 4 := by
      simpa [positiveNeighborPreviousSource,
        positiveNeighborTargetHigh] using
        positiveNeighborChart_high 1 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [cellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h0.symm,
        by exact_mod_cast h1⟩
    · rintro ⟨hp1, hq0, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [cellLiftCoordinates, hp1, hq0, hpq]
  ·
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborTargetHigh]
    have hchart : cellChart v 1 =
        cellChart (v + positiveNeighborDisplacement 2) 5 := by
      simpa [positiveNeighborPreviousSource,
        positiveNeighborTargetHigh] using
        positiveNeighborChart_high 2 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [cellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h0.symm,
        by exact_mod_cast h2⟩
    · rintro ⟨hp1, hq0, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [cellLiftCoordinates, hp1, hq0, hpq]

public theorem correctedLaurentIdentity_positiveNeighbor_high
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborPreviousSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetHigh r) q ↔
      cellLiftCoordinates (positiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r)))
          (cellLiftCoordinates (positiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_positiveNeighbor_high_iff r v p q).trans
    (positiveNeighborTransition_high_iff r v p q).symm

public theorem correctedPlaneTile_positiveNeighbor_backwardVertex_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborPreviousSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetLow r) q ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  fin_cases r
  · exact correctedPlaneTile_neighbor_five_two_iff v p q
  all_goals
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborDisplacement, positiveNeighborTargetLow]
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
            planeTile_of_le _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_le _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_le _ _ q hq] at h
        | rw [correctedPlaneTile, correctedPlaneTile,
            planeTile_of_ge _ _ p hp,
            planeTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [correctedPlaneCenter, Pi.add_apply,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset, e₁, e₂] at h0 h1
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
          hp0, hp1, hq0, hq1, e₁, e₂] <;>
        ring

public theorem positiveNeighborTransition_backwardVertex_iff
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates (positiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r)))
          (cellLiftCoordinates (positiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  fin_cases r
  · exact neighborTransition_five_two_iff v p q
  ·
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborDisplacement, positiveNeighborTargetLow]
    rw [show transitionMatrix (cellChart v 0)
        (cellChart (v + e₂) 3) =
        !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] by
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
          hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
      have heq0 := congrFun heq 0
      have heq1 := congrFun heq 1
      have heq2 := congrFun heq 2
      simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
      have hprod : p.1 0 * q.1 0 = 1 := by
        field_simp [hp0c] at heq1
        exact (by exact_mod_cast congrArg Complex.re heq1.symm)
      have hpq_le : p.1 0 * q.1 0 ≤ q.1 0 :=
        mul_le_of_le_one_left (q.2 0).1 (p.2 0).2
      have hq0 : q.1 0 = 1 := (q.2 0).2.antisymm (hprod.ge.trans hpq_le)
      have hp0 : p.1 0 = 1 := by rw [hq0] at hprod; simpa using hprod
      have hp1 : p.1 1 = 0 := by
        rcases heq2 with hp0zero | hp1zero
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
  ·
    dsimp [positiveNeighborPreviousSource,
      positiveNeighborDisplacement, positiveNeighborTargetLow]
    rw [show transitionMatrix (cellChart v 1)
        (cellChart (v + (e₂ - e₁)) 4) =
        !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] by
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
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      have heq0 := congrFun heq 0
      have heq1 := congrFun heq 1
      have heq2 := congrFun heq 2
      simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
      have hprod : p.1 0 * q.1 0 = 1 := by
        field_simp [hp0c] at heq0
        exact (by exact_mod_cast congrArg Complex.re heq0.symm)
      have hpq_le : p.1 0 * q.1 0 ≤ q.1 0 :=
        mul_le_of_le_one_left (q.2 0).1 (p.2 0).2
      have hq0 : q.1 0 = 1 := (q.2 0).2.antisymm (hprod.ge.trans hpq_le)
      have hp0 : p.1 0 = 1 := by rw [hq0] at hprod; simpa using hprod
      have hp1 : p.1 1 = 0 := by
        rcases heq2 with hp1zero | hp0zero
        · exact_mod_cast hp1zero
        · have hp0r : p.1 0 ≠ 0 := by exact_mod_cast hp0c
          exact (hp0r hp0zero).elim
      have hq1 : q.1 1 = 0 := by exact_mod_cast heq1.symm
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

public theorem correctedLaurentIdentity_positiveNeighbor_backwardVertex
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborPreviousSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetLow r) q ↔
      cellLiftCoordinates (positiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborPreviousSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetLow r)))
          (cellLiftCoordinates (positiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_positiveNeighbor_backwardVertex_iff r v p q).trans
    (positiveNeighborTransition_backwardVertex_iff r v p q).symm

public theorem correctedLaurentIdentity_positiveNeighbor_forwardVertex
    (r : Fin 3) (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v (positiveNeighborSource r) p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r)
          (positiveNeighborTargetHigh r) q ↔
      cellLiftCoordinates (positiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (cellChart v (positiveNeighborSource r))
            (cellChart (v + positiveNeighborDisplacement r)
              (positiveNeighborTargetHigh r)))
          (cellLiftCoordinates (positiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (positiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ)) := by
  fin_cases r
  · exact correctedLaurentIdentity_neighbor v p q
  · exact correctedLaurentIdentity_neighbor_e₂ v p q
  · exact correctedLaurentIdentity_thirdNeighbor v p q

public theorem positiveNeighbor_chartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    (i = positiveNeighborSource r ∨
        i = positiveNeighborPreviousSource r) ∧
      (j = positiveNeighborTargetLow r ∨
        j = positiveNeighborTargetHigh r) := by
  fin_cases r
  · simpa [positiveNeighborSource, positiveNeighborPreviousSource,
      positiveNeighborTargetLow, positiveNeighborTargetHigh,
      positiveNeighborDisplacement] using
      neighbor_e1_chartIncidence v i j p q h
  all_goals
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      laurentRelation_chartIncidence v
        (v + positiveNeighborDisplacement _ ) i j p q h
    constructor
    · fin_cases i <;> fin_cases a <;>
        simp [positiveNeighborSource,
          positiveNeighborPreviousSource,
          positiveNeighborDisplacement, cellChart,
          a2Triangle, e₁, e₂, sub_eq_add_neg] at ha ⊢
      all_goals
        have hv0 : Matrix.vecHead v = v 0 := rfl
        have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
        have ha0 := congrFun ha 0
        have ha1 := congrFun ha 1
        simp at ha0 ha1
        omega
    · fin_cases j <;> fin_cases b <;>
        simp [positiveNeighborTargetLow,
          positiveNeighborTargetHigh,
          positiveNeighborDisplacement, cellChart,
          a2Triangle, e₁, e₂, sub_eq_add_neg] at hb ⊢
      all_goals
        have hv0 : Matrix.vecHead v = v 0 := rfl
        have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
        have hb0 := congrFun hb 0
        have hb1 := congrFun hb 1
        simp at hb0 hb1
        omega

public theorem correctedLaurentIdentity_positiveNeighbor_of_chartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (hi : i = positiveNeighborSource r ∨
      i = positiveNeighborPreviousSource r)
    (hj : j = positiveNeighborTargetLow r ∨
      j = positiveNeighborTargetHigh r) :
    correctedPlaneTile v i p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r) j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact correctedLaurentIdentity_positiveNeighbor_low r v p q
  · exact correctedLaurentIdentity_positiveNeighbor_forwardVertex r v p q
  · exact correctedLaurentIdentity_positiveNeighbor_backwardVertex r v p q
  · exact correctedLaurentIdentity_positiveNeighbor_high r v p q

public theorem correctedPlaneTile_eq_of_positiveNeighborLaurent
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    correctedPlaneTile v i p =
      correctedPlaneTile
        (v + positiveNeighborDisplacement r) j q := by
  obtain ⟨hi, hj⟩ := positiveNeighbor_chartIncidence r v i j p q h
  exact (correctedLaurentIdentity_positiveNeighbor_of_chartIncidence
    r v i j p q hi hj).mpr h

private theorem correctedPlaneTile_e1_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : (correctedPlaneTile v i p 0 -
        correctedPlaneTile v i p 1) -
        (correctedPlaneCenter v 0 -
          correctedPlaneCenter v 1) = 2 / 3) :
    i = 0 ∨ i = 5 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc (k : Fin 2) :
      correctedPlaneTile v i p k - correctedPlaneCenter v k =
        planeTile v i p k - (v k : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  have h' :
      (correctedPlaneTile v i p 0 - correctedPlaneCenter v 0) -
        (correctedPlaneTile v i p 1 -
          correctedPlaneCenter v 1) = 2 / 3 := by
    linarith
  rw [hc, hc] at h'
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht := planeTile_of_le v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht := planeTile_of_ge v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem correctedPlaneTile_e1_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : (correctedPlaneTile v i p 0 -
        correctedPlaneTile v i p 1) -
        (correctedPlaneCenter v 0 -
          correctedPlaneCenter v 1) = -(2 / 3)) :
    i = 2 ∨ i = 3 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc (k : Fin 2) :
      correctedPlaneTile v i p k - correctedPlaneCenter v k =
        planeTile v i p k - (v k : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  have h' :
      (correctedPlaneTile v i p 0 - correctedPlaneCenter v 0) -
        (correctedPlaneTile v i p 1 -
          correctedPlaneCenter v 1) = -(2 / 3) := by
    linarith
  rw [hc, hc] at h'
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht := planeTile_of_le v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht := planeTile_of_ge v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem correctedPlaneTile_e2_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : correctedPlaneTile v i p 0 -
      correctedPlaneCenter v 0 = 2 / 3) :
    i = 0 ∨ i = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : correctedPlaneTile v i p 0 -
      correctedPlaneCenter v 0 =
        planeTile v i p 0 - (v 0 : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht0 := congrFun (planeTile_of_le v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht0 := congrFun (planeTile_of_ge v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem correctedPlaneTile_e2_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : correctedPlaneTile v i p 0 -
      correctedPlaneCenter v 0 = -(2 / 3)) :
    i = 3 ∨ i = 4 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : correctedPlaneTile v i p 0 -
      correctedPlaneCenter v 0 =
        planeTile v i p 0 - (v 0 : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht0 := congrFun (planeTile_of_le v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht0 := congrFun (planeTile_of_ge v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem correctedPlaneTile_e3_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : correctedPlaneTile v i p 1 -
      correctedPlaneCenter v 1 = 2 / 3) :
    i = 1 ∨ i = 2 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : correctedPlaneTile v i p 1 -
      correctedPlaneCenter v 1 =
        planeTile v i p 1 - (v 1 : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht1 := congrFun (planeTile_of_le v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht1 := congrFun (planeTile_of_ge v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem correctedPlaneTile_e3_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (h : correctedPlaneTile v i p 1 -
      correctedPlaneCenter v 1 = -(2 / 3)) :
    i = 4 ∨ i = 5 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : correctedPlaneTile v i p 1 -
      correctedPlaneCenter v 1 =
        planeTile v i p 1 - (v 1 : ℝ) := by
    simp [correctedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht1 := congrFun (planeTile_of_le v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht1 := congrFun (planeTile_of_ge v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [planeVertexOffset, planeNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

public theorem positiveNeighbor_planeChartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : correctedPlaneTile v i p =
      correctedPlaneTile
        (v + positiveNeighborDisplacement r) j q) :
    (i = positiveNeighborSource r ∨
        i = positiveNeighborPreviousSource r) ∧
      (j = positiveNeighborTargetLow r ∨
        j = positiveNeighborTargetHigh r) := by
  fin_cases r
  · dsimp [positiveNeighborSource,
      positiveNeighborPreviousSource, positiveNeighborTargetLow,
      positiveNeighborTargetHigh, positiveNeighborDisplacement] at h ⊢
    have hv := correctedPlaneTile_mem v i p
    have hw := correctedPlaneTile_mem (v + e₁) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.2.2).2
    have hwlo := (abs_le.mp hw.2.2).1
    have hs : (correctedPlaneTile v i p 0 -
        correctedPlaneTile v i p 1) -
        (correctedPlaneCenter v 0 -
          correctedPlaneCenter v 1) = 2 / 3 := by
      simp [correctedPlaneCenter, e₁] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : (correctedPlaneTile (v + e₁) j q 0 -
        correctedPlaneTile (v + e₁) j q 1) -
        (correctedPlaneCenter (v + e₁) 0 -
          correctedPlaneCenter (v + e₁) 1) = -(2 / 3) := by
      rw [← h]
      simp [correctedPlaneCenter, e₁] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨correctedPlaneTile_e1_sourceIncidence v i p hs,
      correctedPlaneTile_e1_targetIncidence (v + e₁) j q ht⟩
  · dsimp [positiveNeighborSource,
      positiveNeighborPreviousSource, positiveNeighborTargetLow,
      positiveNeighborTargetHigh, positiveNeighborDisplacement] at h ⊢
    have hv := correctedPlaneTile_mem v i p
    have hw := correctedPlaneTile_mem (v + e₂) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.1).2
    have hwlo := (abs_le.mp hw.1).1
    have hs : correctedPlaneTile v i p 0 -
        correctedPlaneCenter v 0 = 2 / 3 := by
      simp [correctedPlaneCenter, e₂] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : correctedPlaneTile (v + e₂) j q 0 -
        correctedPlaneCenter (v + e₂) 0 = -(2 / 3) := by
      rw [← h]
      simp [correctedPlaneCenter, e₂] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨(correctedPlaneTile_e2_sourceIncidence v i p hs).symm,
      correctedPlaneTile_e2_targetIncidence (v + e₂) j q ht⟩
  · dsimp [positiveNeighborSource,
      positiveNeighborPreviousSource, positiveNeighborTargetLow,
      positiveNeighborTargetHigh, positiveNeighborDisplacement] at h ⊢
    have hv := correctedPlaneTile_mem v i p
    have hw := correctedPlaneTile_mem (v + (e₂ - e₁)) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.2.1).2
    have hwlo := (abs_le.mp hw.2.1).1
    have hs : correctedPlaneTile v i p 1 -
        correctedPlaneCenter v 1 = 2 / 3 := by
      simp [correctedPlaneCenter, e₁, e₂] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : correctedPlaneTile (v + (e₂ - e₁)) j q 1 -
        correctedPlaneCenter (v + (e₂ - e₁)) 1 = -(2 / 3) := by
      rw [← h]
      simp [correctedPlaneCenter, e₁, e₂] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨(correctedPlaneTile_e3_sourceIncidence v i p hs).symm,
      correctedPlaneTile_e3_targetIncidence (v + (e₂ - e₁)) j q ht⟩

public theorem correctedLaurentIdentity_positiveNeighbor
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p =
        correctedPlaneTile
          (v + positiveNeighborDisplacement r) j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart (v + positiveNeighborDisplacement r) j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := positiveNeighbor_planeChartIncidence r v i j p q h
    exact (correctedLaurentIdentity_positiveNeighbor_of_chartIncidence
      r v i j p q hi hj).mp h
  · exact correctedPlaneTile_eq_of_positiveNeighborLaurent r v i j p q
end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
