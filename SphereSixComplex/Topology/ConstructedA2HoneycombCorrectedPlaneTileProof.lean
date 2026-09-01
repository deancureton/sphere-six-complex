module

public import SphereSixComplex.Topology.ConstructedA2HoneycombSeparatedOverlapIdentityProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def constructedA2CorrectedPlaneCenter (v : ToricLattice) : Fin 2 → ℝ :=
  ![(2 / 3 : ℝ) * v 0 + (4 / 3 : ℝ) * v 1,
    -(2 / 3 : ℝ) * v 0 + (2 / 3 : ℝ) * v 1]

public def constructedA2CorrectedPlaneTile (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) : Fin 2 → ℝ :=
  (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
    constructedA2PlaneTile v i p

public theorem constructedA2CorrectedPlaneTile_sameCell_iff
    (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p = constructedA2CorrectedPlaneTile v j q ↔
      constructedA2PlaneTile v i p = constructedA2PlaneTile v j q := by
  simp only [constructedA2CorrectedPlaneTile]
  exact add_left_cancel_iff

public theorem constructedA2CorrectedLaurentIdentity_of_sameCell
    (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2PlaneTile v i p = constructedA2PlaneTile v j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    constructedA2CorrectedPlaneTile v i p = constructedA2CorrectedPlaneTile v j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_sameCell_iff v i j p q).trans h

public theorem constructedA2CorrectedPlaneTile_neighbor_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 0 p =
        constructedA2CorrectedPlaneTile (v + e₁) 3 q ↔
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
      | rw [show constructedA2CorrectedPlaneTile v 0 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 0 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₁) 3 q =
            (constructedA2CorrectedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              constructedA2PlaneTile (v + e₁) 3 q by rfl,
          constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 3 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 0 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 0 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₁) 3 q =
            (constructedA2CorrectedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              constructedA2PlaneTile (v + e₁) 3 q by rfl,
          constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 3 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 0 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 0 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₁) 3 q =
            (constructedA2CorrectedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              constructedA2PlaneTile (v + e₁) 3 q by rfl,
          constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_le (v + e₁) 3 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 0 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 0 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₁) 3 q =
            (constructedA2CorrectedPlaneCenter (v + e₁) -
                fun k ↦ ((v + e₁) k : ℝ)) +
              constructedA2PlaneTile (v + e₁) 3 q by rfl,
          constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_ge (v + e₁) 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneCenter,
        constructedA2PlaneVertexOffset,
        constructedA2PlaneMidpointOffset, constructedA2PlaneNextMidpointOffset,
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
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneTile,
        constructedA2CorrectedPlaneCenter,
        constructedA2PlaneTile, constructedA2PlaneVertexOffset,
        constructedA2PlaneMidpointOffset, constructedA2PlaneNextMidpointOffset,
        hp0, hp1, hq0, hq1, e₁] <;> ring

public theorem constructedA2NeighborTransition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 3)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 3))
          (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (constructedA2CellChart v 0)
      (constructedA2CellChart (v + e₁) 3) =
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
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_neighbor
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 0 p =
        constructedA2CorrectedPlaneTile (v + e₁) 3 q ↔
      constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 0)
              (constructedA2CellChart (v + e₁) 3)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 0)
              (constructedA2CellChart (v + e₁) 3))
            (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_neighbor_iff v p q).trans
    (constructedA2NeighborTransition_iff v p q).symm

public theorem constructedA2CorrectedPlaneCenter_e₁ (v : ToricLattice) :
    constructedA2CorrectedPlaneCenter (v + e₁) - constructedA2CorrectedPlaneCenter v =
      ![(2 / 3 : ℝ), -2 / 3] := by
  ext k
  fin_cases k <;> simp [constructedA2CorrectedPlaneCenter, e₁] <;> ring

public theorem constructedA2CorrectedPlaneCenter_e₂ (v : ToricLattice) :
    constructedA2CorrectedPlaneCenter (v + e₂) - constructedA2CorrectedPlaneCenter v =
      ![(4 / 3 : ℝ), 2 / 3] := by
  ext k
  fin_cases k <;> simp [constructedA2CorrectedPlaneCenter, e₂] <;> ring

public theorem constructedA2CorrectedPlaneTile_neighbor_e₂_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 1 p =
        constructedA2CorrectedPlaneTile (v + e₂) 4 q ↔
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
      | rw [show constructedA2CorrectedPlaneTile v 1 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 1 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₂) 4 q =
            (constructedA2CorrectedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              constructedA2PlaneTile (v + e₂) 4 q by rfl,
          constructedA2PlaneTile_of_le v 1 p hp,
          constructedA2PlaneTile_of_le (v + e₂) 4 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 1 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 1 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₂) 4 q =
            (constructedA2CorrectedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              constructedA2PlaneTile (v + e₂) 4 q by rfl,
          constructedA2PlaneTile_of_le v 1 p hp,
          constructedA2PlaneTile_of_ge (v + e₂) 4 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 1 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 1 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₂) 4 q =
            (constructedA2CorrectedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              constructedA2PlaneTile (v + e₂) 4 q by rfl,
          constructedA2PlaneTile_of_ge v 1 p hp,
          constructedA2PlaneTile_of_le (v + e₂) 4 q hq] at h
      | rw [show constructedA2CorrectedPlaneTile v 1 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 1 p by rfl,
          show constructedA2CorrectedPlaneTile (v + e₂) 4 q =
            (constructedA2CorrectedPlaneCenter (v + e₂) -
                fun k ↦ ((v + e₂) k : ℝ)) +
              constructedA2PlaneTile (v + e₂) 4 q by rfl,
          constructedA2PlaneTile_of_ge v 1 p hp,
          constructedA2PlaneTile_of_ge (v + e₂) 4 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneCenter,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₂] at h0 h1
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
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneTile,
        constructedA2CorrectedPlaneCenter, constructedA2PlaneTile,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, hp0, hp1, hq0, hq1, e₂] <;> ring

public theorem constructedA2NeighborTransition_e₂_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 1)
            (constructedA2CellChart (v + e₂) 4)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 1)
            (constructedA2CellChart (v + e₂) 4))
          (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (constructedA2CellChart v 1)
      (constructedA2CellChart (v + e₂) 4) =
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
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2CorrectedLaurentIdentity_neighbor_e₂
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 1 p =
        constructedA2CorrectedPlaneTile (v + e₂) 4 q ↔
      constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 1)
              (constructedA2CellChart (v + e₂) 4)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 1)
              (constructedA2CellChart (v + e₂) 4))
            (constructedA2CellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_neighbor_e₂_iff v p q).trans
    (constructedA2NeighborTransition_e₂_iff v p q).symm

public theorem constructedA2CorrectedLaurentIdentity_reverse
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p =
        constructedA2CorrectedPlaneTile w j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    constructedA2CorrectedPlaneTile w j q =
        constructedA2CorrectedPlaneTile v i p ↔
      constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i))
            (constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) =
          constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) := by
  rw [eq_comm, h, constructedA2LaurentTransition_comm]

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
