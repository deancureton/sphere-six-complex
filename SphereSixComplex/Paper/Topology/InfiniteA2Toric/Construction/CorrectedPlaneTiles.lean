module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.SeparatedOverlap

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
namespace Construction


public def correctedPlaneCenter (v : ToricLattice) : Fin 2 → ℝ :=
  ![(2 / 3 : ℝ) * v 0 + (4 / 3 : ℝ) * v 1,
    -(2 / 3 : ℝ) * v 0 + (2 / 3 : ℝ) * v 1]

public def correctedPlaneTile (v : ToricLattice) (i : Fin 6)
    (p : CellSquare) : Fin 2 → ℝ :=
  (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
    planeTile v i p

public theorem correctedPlaneTile_sameCell_iff
    (v : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p = correctedPlaneTile v j q ↔
      planeTile v i p = planeTile v j q := by
  simp only [correctedPlaneTile]
  exact add_left_cancel_iff

public theorem correctedLaurentIdentity_of_sameCell
    (v : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : planeTile v i p = planeTile v j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart v j)) ∧
        monomial
            (transitionMatrix (cellChart v i) (cellChart v j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    correctedPlaneTile v i p = correctedPlaneTile v j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart v j)) ∧
        monomial
            (transitionMatrix (cellChart v i) (cellChart v j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_sameCell_iff v i j p q).trans h

public theorem correctedPlaneTile_neighbor_iff
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 0 p =
        correctedPlaneTile (v + e₁) 3 q ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
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
      | rw [show correctedPlaneTile v 0 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 0 p by rfl,
          show correctedPlaneTile (v + e₁) 3 q =
            (correctedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              planeTile (v + e₁) 3 q by rfl,
          planeTile_of_le v 0 p hp,
          planeTile_of_le (v + e₁) 3 q hq] at h
      | rw [show correctedPlaneTile v 0 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 0 p by rfl,
          show correctedPlaneTile (v + e₁) 3 q =
            (correctedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              planeTile (v + e₁) 3 q by rfl,
          planeTile_of_le v 0 p hp,
          planeTile_of_ge (v + e₁) 3 q hq] at h
      | rw [show correctedPlaneTile v 0 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 0 p by rfl,
          show correctedPlaneTile (v + e₁) 3 q =
            (correctedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              planeTile (v + e₁) 3 q by rfl,
          planeTile_of_ge v 0 p hp,
          planeTile_of_le (v + e₁) 3 q hq] at h
      | rw [show correctedPlaneTile v 0 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 0 p by rfl,
          show correctedPlaneTile (v + e₁) 3 q =
            (correctedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              planeTile (v + e₁) 3 q by rfl,
          planeTile_of_ge v 0 p hp,
          planeTile_of_ge (v + e₁) 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneCenter,
        planeVertexOffset,
        planeMidpointOffset, planeNextMidpointOffset,
        e₁] at h0 h1
      have hp0eq : p.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hp1eq : p.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq0eq : q.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq1eq : q.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      exact ⟨hp0eq, hp1eq, hq0eq, hq1eq⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneTile,
        correctedPlaneCenter,
        planeTile, planeVertexOffset,
        planeMidpointOffset, planeNextMidpointOffset,
        hp0, hp1, hq0, hq1, e₁] <;> ring

public theorem neighborTransition_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 0)
            (cellChart (v + e₁) 3)) ∧
      monomial
          (transitionMatrix (cellChart v 0)
            (cellChart (v + e₁) 3))
          (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (cellChart v 0)
      (cellChart (v + e₁) 3) =
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
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [cellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
    have hprod : p.1 1 * q.1 1 = 1 := by
      field_simp [hp1c] at heq0
      exact (by exact_mod_cast congrArg Complex.re heq0.symm)
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hprod.ge.trans hpq_le)
    have hp1 : p.1 1 = 1 := by rw [hq1] at hprod; simpa using hprod
    have hp0 : p.1 0 = 0 := by
      rcases heq2 with hp0 | hp1zero
      · exact_mod_cast hp0
      · have hp1r : p.1 1 ≠ 0 := by exact_mod_cast hp1c
        exact (hp1r hp1zero).elim
    have hq0 : q.1 0 = 0 := by exact_mod_cast heq1.symm
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

public theorem correctedLaurentIdentity_neighbor
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 0 p =
        correctedPlaneTile (v + e₁) 3 q ↔
      cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 0)
              (cellChart (v + e₁) 3)) ∧
        monomial
            (transitionMatrix (cellChart v 0)
              (cellChart (v + e₁) 3))
            (cellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_neighbor_iff v p q).trans
    (neighborTransition_iff v p q).symm



public theorem correctedPlaneTile_neighbor_e₂_iff
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 1 p =
        correctedPlaneTile (v + e₂) 4 q ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
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
      | rw [show correctedPlaneTile v 1 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 1 p by rfl,
          show correctedPlaneTile (v + e₂) 4 q =
            (correctedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              planeTile (v + e₂) 4 q by rfl,
          planeTile_of_le v 1 p hp,
          planeTile_of_le (v + e₂) 4 q hq] at h
      | rw [show correctedPlaneTile v 1 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 1 p by rfl,
          show correctedPlaneTile (v + e₂) 4 q =
            (correctedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              planeTile (v + e₂) 4 q by rfl,
          planeTile_of_le v 1 p hp,
          planeTile_of_ge (v + e₂) 4 q hq] at h
      | rw [show correctedPlaneTile v 1 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 1 p by rfl,
          show correctedPlaneTile (v + e₂) 4 q =
            (correctedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              planeTile (v + e₂) 4 q by rfl,
          planeTile_of_ge v 1 p hp,
          planeTile_of_le (v + e₂) 4 q hq] at h
      | rw [show correctedPlaneTile v 1 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 1 p by rfl,
          show correctedPlaneTile (v + e₂) 4 q =
            (correctedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              planeTile (v + e₂) 4 q by rfl,
          planeTile_of_ge v 1 p hp,
          planeTile_of_ge (v + e₂) 4 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneCenter,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₂] at h0 h1
      have hp0eq : p.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hp1eq : p.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq0eq : q.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      have hq1eq : q.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
      exact ⟨hp0eq, hp1eq, hq0eq, hq1eq⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    ext k
    fin_cases k <;>
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneTile,
        correctedPlaneCenter, planeTile,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, hp0, hp1, hq0, hq1, e₂] <;> ring

public theorem neighborTransition_e₂_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 1)
            (cellChart (v + e₂) 4)) ∧
      monomial
          (transitionMatrix (cellChart v 1)
            (cellChart (v + e₂) 4))
          (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (cellChart v 1)
      (cellChart (v + e₂) 4) =
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
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [cellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
    have hprod : p.1 1 * q.1 1 = 1 := by
      field_simp [hp1c] at heq1
      exact (by exact_mod_cast congrArg Complex.re heq1.symm)
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hprod.ge.trans hpq_le)
    have hp1 : p.1 1 = 1 := by rw [hq1] at hprod; simpa using hprod
    have hp0r : p.1 0 = 0 := by
      rcases heq2 with hp1zero | hp0zero
      · have hp1r : p.1 1 ≠ 0 := by exact_mod_cast hp1c
        exact (hp1r hp1zero).elim
      · exact_mod_cast hp0zero
    have hq0 : q.1 0 = 0 := by exact_mod_cast heq0.symm
    exact ⟨hp0r, hp1, hq0, hq1⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem correctedLaurentIdentity_neighbor_e₂
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 1 p =
        correctedPlaneTile (v + e₂) 4 q ↔
      cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 1)
              (cellChart (v + e₂) 4)) ∧
        monomial
            (transitionMatrix (cellChart v 1)
              (cellChart (v + e₂) 4))
            (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_neighbor_e₂_iff v p q).trans
    (neighborTransition_e₂_iff v p q).symm

public theorem correctedLaurentIdentity_reverse
    (v w : ToricLattice) (i j : Fin 6) (p q : CellSquare)
    (h : correctedPlaneTile v i p =
        correctedPlaneTile w j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart w j)) ∧
        monomial
            (transitionMatrix (cellChart v i) (cellChart w j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    correctedPlaneTile w j q =
        correctedPlaneTile v i p ↔
      cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart w j) (cellChart v i)) ∧
        monomial
            (transitionMatrix (cellChart w j) (cellChart v i))
            (cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) =
          cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) := by
  rw [eq_comm, h, laurentTransition_comm]

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
