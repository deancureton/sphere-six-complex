module

public import SphereSixComplex.Topology.ConstructedA2HoneycombSameCellMissingOrbitProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2NeighborChart_zero_two (v : ToricLattice) :
    constructedA2CellChart v 0 = constructedA2CellChart (v + e₁) 2 := by
  simp [constructedA2CellChart]

public theorem constructedA2CorrectedPlaneTile_neighbor_zero_two_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 0 p =
        constructedA2CorrectedPlaneTile (v + e₁) 2 q ↔
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
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 2 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hq1, hpq⟩
    have hp : p.1 0 ≤ p.1 1 := by linarith [(p.2 1).1]
    have hq : q.1 1 ≤ q.1 0 := by linarith [(q.2 0).1]
    rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
      constructedA2PlaneTile_of_le v 0 p hp,
      constructedA2PlaneTile_of_ge (v + e₁) 2 q hq]
    ext k
    fin_cases k <;>
      simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁, hp0, hq1, hpq] <;>
      ring

public theorem constructedA2NeighborTransition_zero_two_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 2)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 2))
          (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0 := by
  rw [← constructedA2NeighborChart_zero_two v, transitionMatrix_self, monomial_one]
  constructor
  · rintro ⟨-, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [constructedA2CellLiftCoordinates] at h0 h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h0.symm, by exact_mod_cast h2⟩
  · rintro ⟨hp0, hq1, hpq⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
    · ext k
      fin_cases k <;>
        simp [constructedA2CellLiftCoordinates, hp0, hq1, hpq]

public theorem constructedA2CorrectedLaurentIdentity_neighbor_zero_two
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 0 p =
        constructedA2CorrectedPlaneTile (v + e₁) 2 q ↔
      constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 0)
              (constructedA2CellChart (v + e₁) 2)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 0)
              (constructedA2CellChart (v + e₁) 2))
            (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_neighbor_zero_two_iff v p q).trans
    (constructedA2NeighborTransition_zero_two_iff v p q).symm

public theorem constructedA2NeighborChart_five_three (v : ToricLattice) :
    constructedA2CellChart v 5 = constructedA2CellChart (v + e₁) 3 := by
  simp [constructedA2CellChart]

public theorem constructedA2CorrectedPlaneTile_neighbor_five_three_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 5 p =
        constructedA2CorrectedPlaneTile (v + e₁) 3 q ↔
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
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 5 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 3 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 5 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 3 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 5 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 3 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 5 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp1, hq0, hpq⟩
    have hp : p.1 1 ≤ p.1 0 := by linarith [(p.2 0).1]
    have hq : q.1 0 ≤ q.1 1 := by linarith [(q.2 1).1]
    rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
      constructedA2PlaneTile_of_ge v 5 p hp,
      constructedA2PlaneTile_of_le (v + e₁) 3 q hq]
    ext k
    fin_cases k <;>
      simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁, hp1, hq0, hpq] <;>
      ring

public theorem constructedA2NeighborTransition_five_three_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 5)
            (constructedA2CellChart (v + e₁) 3)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 5)
            (constructedA2CellChart (v + e₁) 3))
          (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1 := by
  rw [← constructedA2NeighborChart_five_three v, transitionMatrix_self, monomial_one]
  constructor
  · rintro ⟨-, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [constructedA2CellLiftCoordinates] at h0 h1 h2
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1.symm, by exact_mod_cast h0⟩
  · rintro ⟨hp1, hq0, hpq⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
    · ext k
      fin_cases k <;>
        simp [constructedA2CellLiftCoordinates, hp1, hq0, hpq]

public theorem constructedA2CorrectedLaurentIdentity_neighbor_five_three
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 5 p =
        constructedA2CorrectedPlaneTile (v + e₁) 3 q ↔
      constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 5)
              (constructedA2CellChart (v + e₁) 3)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 5)
              (constructedA2CellChart (v + e₁) 3))
            (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_neighbor_five_three_iff v p q).trans
    (constructedA2NeighborTransition_five_three_iff v p q).symm

public theorem constructedA2CorrectedPlaneTile_neighbor_five_two_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 5 p =
        constructedA2CorrectedPlaneTile (v + e₁) 2 q ↔
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
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 5 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_le v 5 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 5 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 2 q hq] at h
      | rw [constructedA2CorrectedPlaneTile, constructedA2CorrectedPlaneTile,
          constructedA2PlaneTile_of_ge v 5 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 2 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2CorrectedPlaneCenter, Pi.add_apply,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁] at h0 h1
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
        hp0, hp1, hq0, hq1, e₁] <;>
      ring

public theorem constructedA2NeighborTransition_five_two_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 5)
            (constructedA2CellChart (v + e₁) 2)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 5)
            (constructedA2CellChart (v + e₁) 2))
          (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 0 ∧ q.1 0 = 1 ∧ q.1 1 = 0 := by
  rw [show transitionMatrix (constructedA2CellChart v 5)
      (constructedA2CellChart (v + e₁) 2) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] by
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
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_neighbor_five_two
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 5 p =
        constructedA2CorrectedPlaneTile (v + e₁) 2 q ↔
      constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 5)
              (constructedA2CellChart (v + e₁) 2)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 5)
              (constructedA2CellChart (v + e₁) 2))
            (constructedA2CellLiftCoordinates 5 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_neighbor_five_two_iff v p q).trans
    (constructedA2NeighborTransition_five_two_iff v p q).symm

public theorem constructedA2Neighbor_e1_chartIncidence
    (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + e₁) j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart (v + e₁) j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    (i = 0 ∨ i = 5) ∧ (j = 2 ∨ j = 3) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    constructedA2LaurentRelation_chartIncidence v (v + e₁) i j p q h
  constructor
  · fin_cases i <;> fin_cases a <;>
      simp [constructedA2CellChart, a2Triangle, e₁, e₂, sub_eq_add_neg] at ha ⊢
  · fin_cases j <;> fin_cases b <;>
      simp [constructedA2CellChart, a2Triangle, e₁, e₂, sub_eq_add_neg] at hb ⊢
    all_goals
      have hv0 : Matrix.vecHead v = v 0 := rfl
      have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
      have hb0 := congrFun hb 0
      have hb1 := congrFun hb 1
      simp at hb0 hb1
      omega

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
