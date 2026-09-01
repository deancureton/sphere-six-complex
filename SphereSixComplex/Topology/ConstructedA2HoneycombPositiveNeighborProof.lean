module

public import SphereSixComplex.Topology.ConstructedA2HoneycombNeighborBoundaryProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def constructedA2PositiveNeighborDisplacement : Fin 3 → ToricLattice :=
  ![e₁, e₂, e₂ - e₁]

public def constructedA2PositiveNeighborSource : Fin 3 → Fin 6 := ![0, 1, 2]

public def constructedA2PositiveNeighborPreviousSource : Fin 3 → Fin 6 := ![5, 0, 1]

public def constructedA2PositiveNeighborTargetLow : Fin 3 → Fin 6 := ![2, 3, 4]

public def constructedA2PositiveNeighborTargetHigh : Fin 3 → Fin 6 := ![3, 4, 5]

public theorem constructedA2PositiveNeighborChart_low
    (r : Fin 3) (v : ToricLattice) :
    constructedA2CellChart v (constructedA2PositiveNeighborSource r) =
      constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
        (constructedA2PositiveNeighborTargetLow r) := by
  fin_cases r <;>
    simp [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborDisplacement,
      constructedA2PositiveNeighborTargetLow, constructedA2CellChart, e₁, e₂]
  all_goals first | ring | (ext k; fin_cases k <;> rfl)

public theorem constructedA2CorrectedPlaneTile_positiveNeighbor_low_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetLow r) q ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  fin_cases r
  · exact constructedA2CorrectedPlaneTile_neighbor_zero_two_iff v p q
  all_goals
    dsimp [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborDisplacement,
      constructedA2PositiveNeighborTargetLow]
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
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset, e₁, e₂] at h0 h1
        norm_num [div_eq_mul_inv] at h0 h1
        refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
    · rintro ⟨hp0, hq1, hpq⟩
      have hp : p.1 0 ≤ p.1 1 := by linarith [(p.2 1).1]
      have hq : q.1 1 ≤ q.1 0 := by linarith [(q.2 0).1]
      rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
        constructedA2PlaneTile_of_le _ _ p hp,
        constructedA2PlaneTile_of_ge _ _ q hq]
      ext k
      fin_cases k <;>
        simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset, e₁, e₂, hp0, hq1, hpq] <;>
        ring

public theorem constructedA2PositiveNeighborTransition_low_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  fin_cases r
  · exact constructedA2NeighborTransition_zero_two_iff v p q
  ·
    dsimp [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborTargetLow]
    have hchart : constructedA2CellChart v 1 =
        constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement 1) 3 := by
      simpa [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborTargetLow] using
        constructedA2PositiveNeighborChart_low 1 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [constructedA2CellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h0.symm,
        by exact_mod_cast h1⟩
    · rintro ⟨hp0, hq1, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [constructedA2CellLiftCoordinates, hp0, hq1, hpq]
  ·
    dsimp [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborTargetLow]
    have hchart : constructedA2CellChart v 2 =
        constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement 2) 4 := by
      simpa [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborTargetLow] using
        constructedA2PositiveNeighborChart_low 2 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [constructedA2CellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1.symm,
        by exact_mod_cast h0⟩
    · rintro ⟨hp0, hq1, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [constructedA2CellLiftCoordinates, hp0, hq1, hpq]

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor_low
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetLow r) q ↔
      constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_positiveNeighbor_low_iff r v p q).trans
    (constructedA2PositiveNeighborTransition_low_iff r v p q).symm

public theorem constructedA2PositiveNeighborChart_high
    (r : Fin 3) (v : ToricLattice) :
    constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r) =
      constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
        (constructedA2PositiveNeighborTargetHigh r) := by
  fin_cases r <;>
    simp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborDisplacement, constructedA2PositiveNeighborTargetHigh,
      constructedA2CellChart, e₁, e₂]
  all_goals first | ring | (ext k; fin_cases k <;> rfl)

public theorem constructedA2CorrectedPlaneTile_positiveNeighbor_high_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborPreviousSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetHigh r) q ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  fin_cases r
  · exact constructedA2CorrectedPlaneTile_neighbor_five_three_iff v p q
  all_goals
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborDisplacement, constructedA2PositiveNeighborTargetHigh]
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
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset, e₁, e₂] at h0 h1
        norm_num [div_eq_mul_inv] at h0 h1
        refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
    · rintro ⟨hp1, hq0, hpq⟩
      have hp : p.1 1 ≤ p.1 0 := by linarith [(p.2 0).1]
      have hq : q.1 0 ≤ q.1 1 := by linarith [(q.2 1).1]
      rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
        constructedA2PlaneTile_of_ge _ _ p hp,
        constructedA2PlaneTile_of_le _ _ q hq]
      ext k
      fin_cases k <;>
        simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset, e₁, e₂, hp1, hq0, hpq] <;>
        ring

public theorem constructedA2PositiveNeighborTransition_high_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  fin_cases r
  · exact constructedA2NeighborTransition_five_three_iff v p q
  ·
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborTargetHigh]
    have hchart : constructedA2CellChart v 0 =
        constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement 1) 4 := by
      simpa [constructedA2PositiveNeighborPreviousSource,
        constructedA2PositiveNeighborTargetHigh] using
        constructedA2PositiveNeighborChart_high 1 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [constructedA2CellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h0.symm,
        by exact_mod_cast h1⟩
    · rintro ⟨hp1, hq0, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [constructedA2CellLiftCoordinates, hp1, hq0, hpq]
  ·
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborTargetHigh]
    have hchart : constructedA2CellChart v 1 =
        constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement 2) 5 := by
      simpa [constructedA2PositiveNeighborPreviousSource,
        constructedA2PositiveNeighborTargetHigh] using
        constructedA2PositiveNeighborChart_high 2 v
    rw [← hchart, transitionMatrix_self, monomial_one]
    constructor
    · rintro ⟨-, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      have h2 := congrFun heq 2
      simp [constructedA2CellLiftCoordinates] at h0 h1 h2
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h0.symm,
        by exact_mod_cast h2⟩
    · rintro ⟨hp1, hq0, hpq⟩
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab
      · ext k
        fin_cases k <;>
          simp [constructedA2CellLiftCoordinates, hp1, hq0, hpq]

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor_high
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborPreviousSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetHigh r) q ↔
      constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_positiveNeighbor_high_iff r v p q).trans
    (constructedA2PositiveNeighborTransition_high_iff r v p q).symm

public theorem constructedA2CorrectedPlaneTile_positiveNeighbor_backwardVertex_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborPreviousSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetLow r) q ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  fin_cases r
  · exact constructedA2CorrectedPlaneTile_neighbor_five_two_iff v p q
  all_goals
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborDisplacement, constructedA2PositiveNeighborTargetLow]
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
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_le _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_le _ _ q hq] at h
        | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
            constructedA2PlaneTile_of_ge _ _ p hp,
            constructedA2PlaneTile_of_ge _ _ q hq] at h
      all_goals
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset, e₁, e₂] at h0 h1
        norm_num [div_eq_mul_inv] at h0 h1
        refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
          by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
    · rintro ⟨hp0, hp1, hq0, hq1⟩
      ext k
      fin_cases k <;>
        simp [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneCenter,
          constructedA2PlaneTile, constructedA2PlaneVertexOffset,
          constructedA2PlaneMidpointOffset, constructedA2PlaneNextMidpointOffset,
          hp0, hp1, hq0, hq1, e₁, e₂] <;>
        ring

public theorem constructedA2PositiveNeighborTransition_backwardVertex_iff
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  fin_cases r
  · exact constructedA2NeighborTransition_five_two_iff v p q
  ·
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborDisplacement, constructedA2PositiveNeighborTargetLow]
    rw [show transitionMatrix (constructedA2CellChart v 0)
        (constructedA2CellChart (v + e₂) 3) =
        !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] by
      have hv0 : Matrix.vecHead v = v 0 := rfl
      have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [constructedA2CellChart, transitionMatrix, dualMatrix,
          a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
          Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring]
    constructor
    · rintro ⟨hdomain, heq⟩
      have hp0c : (p.1 0 : ℂ) ≠ 0 := by
        simpa [constructedA2CellLiftCoordinates] using
          hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
      have heq0 := congrFun heq 0
      have heq1 := congrFun heq 1
      have heq2 := congrFun heq 2
      simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
          simp_all [constructedA2CellLiftCoordinates]
      · ext k
        fin_cases k <;>
          simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
            hp0, hp1, hq0, hq1]
  ·
    dsimp [constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborDisplacement, constructedA2PositiveNeighborTargetLow]
    rw [show transitionMatrix (constructedA2CellChart v 1)
        (constructedA2CellChart (v + (e₂ - e₁)) 4) =
        !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] by
      have hv0 : Matrix.vecHead v = v 0 := rfl
      have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [constructedA2CellChart, transitionMatrix, dualMatrix,
          a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
          Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring]
    constructor
    · rintro ⟨hdomain, heq⟩
      have hp0c : (p.1 0 : ℂ) ≠ 0 := by
        simpa [constructedA2CellLiftCoordinates] using
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      have heq0 := congrFun heq 0
      have heq1 := congrFun heq 1
      have heq2 := congrFun heq 2
      simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
          simp_all [constructedA2CellLiftCoordinates]
      · ext k
        fin_cases k <;>
          simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
            hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor_backwardVertex
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborPreviousSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetLow r) q ↔
      constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborPreviousSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetLow r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborPreviousSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetLow r)
          (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_positiveNeighbor_backwardVertex_iff r v p q).trans
    (constructedA2PositiveNeighborTransition_backwardVertex_iff r v p q).symm

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor_forwardVertex
    (r : Fin 3) (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v (constructedA2PositiveNeighborSource r) p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r)
          (constructedA2PositiveNeighborTargetHigh r) q ↔
      constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
          (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r))) ∧
      monomial
          (transitionMatrix
            (constructedA2CellChart v (constructedA2PositiveNeighborSource r))
            (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r)
              (constructedA2PositiveNeighborTargetHigh r)))
          (constructedA2CellLiftCoordinates (constructedA2PositiveNeighborSource r)
            (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2PositiveNeighborTargetHigh r)
          (fun k ↦ (q.1 k : ℂ)) := by
  fin_cases r
  · exact constructedA2CorrectedLaurentIdentity_neighbor v p q
  · exact constructedA2CorrectedLaurentIdentity_neighbor_e₂ v p q
  · exact constructedA2CorrectedLaurentIdentity_thirdNeighbor v p q

public theorem constructedA2PositiveNeighbor_chartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    (i = constructedA2PositiveNeighborSource r ∨
        i = constructedA2PositiveNeighborPreviousSource r) ∧
      (j = constructedA2PositiveNeighborTargetLow r ∨
        j = constructedA2PositiveNeighborTargetHigh r) := by
  fin_cases r
  · simpa [constructedA2PositiveNeighborSource, constructedA2PositiveNeighborPreviousSource,
      constructedA2PositiveNeighborTargetLow, constructedA2PositiveNeighborTargetHigh,
      constructedA2PositiveNeighborDisplacement] using
      constructedA2Neighbor_e1_chartIncidence v i j p q h
  all_goals
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      constructedA2LaurentRelation_chartIncidence v
        (v + constructedA2PositiveNeighborDisplacement _ ) i j p q h
    constructor
    · fin_cases i <;> fin_cases a <;>
        simp [constructedA2PositiveNeighborSource,
          constructedA2PositiveNeighborPreviousSource,
          constructedA2PositiveNeighborDisplacement, constructedA2CellChart,
          a2Triangle, e₁, e₂, sub_eq_add_neg] at ha ⊢
      all_goals
        have hv0 : Matrix.vecHead v = v 0 := rfl
        have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
        have ha0 := congrFun ha 0
        have ha1 := congrFun ha 1
        simp at ha0 ha1
        omega
    · fin_cases j <;> fin_cases b <;>
        simp [constructedA2PositiveNeighborTargetLow,
          constructedA2PositiveNeighborTargetHigh,
          constructedA2PositiveNeighborDisplacement, constructedA2CellChart,
          a2Triangle, e₁, e₂, sub_eq_add_neg] at hb ⊢
      all_goals
        have hv0 : Matrix.vecHead v = v 0 := rfl
        have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
        have hb0 := congrFun hb 0
        have hb1 := congrFun hb 1
        simp at hb0 hb1
        omega

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor_of_chartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (hi : i = constructedA2PositiveNeighborSource r ∨
      i = constructedA2PositiveNeighborPreviousSource r)
    (hj : j = constructedA2PositiveNeighborTargetLow r ∨
      j = constructedA2PositiveNeighborTargetHigh r) :
    constructedA2CorrectedPlaneTile v i p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r) j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact constructedA2CorrectedLaurentIdentity_positiveNeighbor_low r v p q
  · exact constructedA2CorrectedLaurentIdentity_positiveNeighbor_forwardVertex r v p q
  · exact constructedA2CorrectedLaurentIdentity_positiveNeighbor_backwardVertex r v p q
  · exact constructedA2CorrectedLaurentIdentity_positiveNeighbor_high r v p q

public theorem constructedA2CorrectedPlaneTile_eq_of_positiveNeighborLaurent
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    constructedA2CorrectedPlaneTile v i p =
      constructedA2CorrectedPlaneTile
        (v + constructedA2PositiveNeighborDisplacement r) j q := by
  obtain ⟨hi, hj⟩ := constructedA2PositiveNeighbor_chartIncidence r v i j p q h
  exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor_of_chartIncidence
    r v i j p q hi hj).mpr h

private theorem constructedA2CorrectedPlaneTile_e1_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : (constructedA2CorrectedPlaneTile v i p 0 -
        constructedA2CorrectedPlaneTile v i p 1) -
        (constructedA2CorrectedPlaneCenter v 0 -
          constructedA2CorrectedPlaneCenter v 1) = 2 / 3) :
    i = 0 ∨ i = 5 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc (k : Fin 2) :
      constructedA2CorrectedPlaneTile v i p k - constructedA2CorrectedPlaneCenter v k =
        constructedA2PlaneTile v i p k - (v k : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  have h' :
      (constructedA2CorrectedPlaneTile v i p 0 - constructedA2CorrectedPlaneCenter v 0) -
        (constructedA2CorrectedPlaneTile v i p 1 -
          constructedA2CorrectedPlaneCenter v 1) = 2 / 3 := by
    linarith
  rw [hc, hc] at h'
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht := constructedA2PlaneTile_of_le v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht := constructedA2PlaneTile_of_ge v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem constructedA2CorrectedPlaneTile_e1_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : (constructedA2CorrectedPlaneTile v i p 0 -
        constructedA2CorrectedPlaneTile v i p 1) -
        (constructedA2CorrectedPlaneCenter v 0 -
          constructedA2CorrectedPlaneCenter v 1) = -(2 / 3)) :
    i = 2 ∨ i = 3 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc (k : Fin 2) :
      constructedA2CorrectedPlaneTile v i p k - constructedA2CorrectedPlaneCenter v k =
        constructedA2PlaneTile v i p k - (v k : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  have h' :
      (constructedA2CorrectedPlaneTile v i p 0 - constructedA2CorrectedPlaneCenter v 0) -
        (constructedA2CorrectedPlaneTile v i p 1 -
          constructedA2CorrectedPlaneCenter v 1) = -(2 / 3) := by
    linarith
  rw [hc, hc] at h'
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht := constructedA2PlaneTile_of_le v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht := constructedA2PlaneTile_of_ge v i p hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0 ht1
    rw [ht0, ht1] at h'
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h'
      norm_num [div_eq_mul_inv] at h'
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem constructedA2CorrectedPlaneTile_e2_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p 0 -
      constructedA2CorrectedPlaneCenter v 0 = 2 / 3) :
    i = 0 ∨ i = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : constructedA2CorrectedPlaneTile v i p 0 -
      constructedA2CorrectedPlaneCenter v 0 =
        constructedA2PlaneTile v i p 0 - (v 0 : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht0 := congrFun (constructedA2PlaneTile_of_le v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht0 := congrFun (constructedA2PlaneTile_of_ge v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem constructedA2CorrectedPlaneTile_e2_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p 0 -
      constructedA2CorrectedPlaneCenter v 0 = -(2 / 3)) :
    i = 3 ∨ i = 4 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : constructedA2CorrectedPlaneTile v i p 0 -
      constructedA2CorrectedPlaneCenter v 0 =
        constructedA2PlaneTile v i p 0 - (v 0 : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht0 := congrFun (constructedA2PlaneTile_of_le v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht0 := congrFun (constructedA2PlaneTile_of_ge v i p hp) 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht0
    rw [ht0] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem constructedA2CorrectedPlaneTile_e3_sourceIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p 1 -
      constructedA2CorrectedPlaneCenter v 1 = 2 / 3) :
    i = 1 ∨ i = 2 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : constructedA2CorrectedPlaneTile v i p 1 -
      constructedA2CorrectedPlaneCenter v 1 =
        constructedA2PlaneTile v i p 1 - (v 1 : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht1 := congrFun (constructedA2PlaneTile_of_le v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht1 := congrFun (constructedA2PlaneTile_of_ge v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem constructedA2CorrectedPlaneTile_e3_targetIncidence
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p 1 -
      constructedA2CorrectedPlaneCenter v 1 = -(2 / 3)) :
    i = 4 ∨ i = 5 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hc : constructedA2CorrectedPlaneTile v i p 1 -
      constructedA2CorrectedPlaneCenter v 1 =
        constructedA2PlaneTile v i p 1 - (v 1 : ℝ) := by
    simp [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hc] at h
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · have ht1 := congrFun (constructedA2PlaneTile_of_le v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · have ht1 := congrFun (constructedA2PlaneTile_of_ge v i p hp) 1
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht1
    rw [ht1] at h
    fin_cases i <;> simp
    all_goals
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset] at h
      norm_num [div_eq_mul_inv] at h
      linarith [hp0.1, hp0.2, hp1.1, hp1.2]

public theorem constructedA2PositiveNeighbor_planeChartIncidence
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p =
      constructedA2CorrectedPlaneTile
        (v + constructedA2PositiveNeighborDisplacement r) j q) :
    (i = constructedA2PositiveNeighborSource r ∨
        i = constructedA2PositiveNeighborPreviousSource r) ∧
      (j = constructedA2PositiveNeighborTargetLow r ∨
        j = constructedA2PositiveNeighborTargetHigh r) := by
  fin_cases r
  · dsimp [constructedA2PositiveNeighborSource,
      constructedA2PositiveNeighborPreviousSource, constructedA2PositiveNeighborTargetLow,
      constructedA2PositiveNeighborTargetHigh, constructedA2PositiveNeighborDisplacement] at h ⊢
    have hv := constructedA2CorrectedPlaneTile_mem v i p
    have hw := constructedA2CorrectedPlaneTile_mem (v + e₁) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.2.2).2
    have hwlo := (abs_le.mp hw.2.2).1
    have hs : (constructedA2CorrectedPlaneTile v i p 0 -
        constructedA2CorrectedPlaneTile v i p 1) -
        (constructedA2CorrectedPlaneCenter v 0 -
          constructedA2CorrectedPlaneCenter v 1) = 2 / 3 := by
      simp [constructedA2CorrectedPlaneCenter, e₁] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : (constructedA2CorrectedPlaneTile (v + e₁) j q 0 -
        constructedA2CorrectedPlaneTile (v + e₁) j q 1) -
        (constructedA2CorrectedPlaneCenter (v + e₁) 0 -
          constructedA2CorrectedPlaneCenter (v + e₁) 1) = -(2 / 3) := by
      rw [← h]
      simp [constructedA2CorrectedPlaneCenter, e₁] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨constructedA2CorrectedPlaneTile_e1_sourceIncidence v i p hs,
      constructedA2CorrectedPlaneTile_e1_targetIncidence (v + e₁) j q ht⟩
  · dsimp [constructedA2PositiveNeighborSource,
      constructedA2PositiveNeighborPreviousSource, constructedA2PositiveNeighborTargetLow,
      constructedA2PositiveNeighborTargetHigh, constructedA2PositiveNeighborDisplacement] at h ⊢
    have hv := constructedA2CorrectedPlaneTile_mem v i p
    have hw := constructedA2CorrectedPlaneTile_mem (v + e₂) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.1).2
    have hwlo := (abs_le.mp hw.1).1
    have hs : constructedA2CorrectedPlaneTile v i p 0 -
        constructedA2CorrectedPlaneCenter v 0 = 2 / 3 := by
      simp [constructedA2CorrectedPlaneCenter, e₂] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : constructedA2CorrectedPlaneTile (v + e₂) j q 0 -
        constructedA2CorrectedPlaneCenter (v + e₂) 0 = -(2 / 3) := by
      rw [← h]
      simp [constructedA2CorrectedPlaneCenter, e₂] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨(constructedA2CorrectedPlaneTile_e2_sourceIncidence v i p hs).symm,
      constructedA2CorrectedPlaneTile_e2_targetIncidence (v + e₂) j q ht⟩
  · dsimp [constructedA2PositiveNeighborSource,
      constructedA2PositiveNeighborPreviousSource, constructedA2PositiveNeighborTargetLow,
      constructedA2PositiveNeighborTargetHigh, constructedA2PositiveNeighborDisplacement] at h ⊢
    have hv := constructedA2CorrectedPlaneTile_mem v i p
    have hw := constructedA2CorrectedPlaneTile_mem (v + (e₂ - e₁)) j q
    rw [← h] at hw
    have hvhi := (abs_le.mp hv.2.1).2
    have hwlo := (abs_le.mp hw.2.1).1
    have hs : constructedA2CorrectedPlaneTile v i p 1 -
        constructedA2CorrectedPlaneCenter v 1 = 2 / 3 := by
      simp [constructedA2CorrectedPlaneCenter, e₁, e₂] at hvhi hwlo ⊢
      norm_num [div_eq_mul_inv] at hvhi hwlo ⊢
      linarith
    have ht : constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) j q 1 -
        constructedA2CorrectedPlaneCenter (v + (e₂ - e₁)) 1 = -(2 / 3) := by
      rw [← h]
      simp [constructedA2CorrectedPlaneCenter, e₁, e₂] at hs ⊢
      norm_num [div_eq_mul_inv] at hs ⊢
      linarith
    exact ⟨(constructedA2CorrectedPlaneTile_e3_sourceIncidence v i p hs).symm,
      constructedA2CorrectedPlaneTile_e3_targetIncidence (v + (e₂ - e₁)) j q ht⟩

public theorem constructedA2CorrectedLaurentIdentity_positiveNeighbor
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p =
        constructedA2CorrectedPlaneTile
          (v + constructedA2PositiveNeighborDisplacement r) j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + constructedA2PositiveNeighborDisplacement r) j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := constructedA2PositiveNeighbor_planeChartIncidence r v i j p q h
    exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor_of_chartIncidence
      r v i j p q hi hj).mp h
  · exact constructedA2CorrectedPlaneTile_eq_of_positiveNeighborLaurent r v i j p q
end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
