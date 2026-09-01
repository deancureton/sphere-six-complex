module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCyclicOverlapIdentityProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2CellTransitionMatrix_zero_two (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 2) =
      !![(0 : ℤ), -1, -1; 1, 2, 1; 0, 0, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix,
      a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
      Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2PlaneTile_zero_eq_two_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 0 p = constructedA2PlaneTile v 2 q ↔
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
      | rw [constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_le v 2 q hq] at h
      | rw [constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_ge v 2 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_le v 2 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_ge v 2 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] at h0 h1
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
      simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset]

public theorem constructedA2_zero_two_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 2)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 2))
          (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_zero_two]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq2
    have hprod : p.1 0 * p.1 1 * q.1 1 = 1 := by
      field_simp [hp0c, hp1c] at heq0
      exact (by exact_mod_cast congrArg Complex.re heq0.symm)
    have hbc : 1 ≤ p.1 1 * q.1 1 := by
      have hn : 0 ≤ (1 - p.1 0) * (p.1 1 * q.1 1) :=
        mul_nonneg (sub_nonneg.mpr (p.2 0).2)
          (mul_nonneg (p.2 1).1 (q.2 1).1)
      nlinarith
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1eq : q.1 1 = 1 :=
      (q.2 1).2.antisymm (hbc.trans hpq_le)
    have hp1eq : p.1 1 = 1 := by
      have hbc' : 1 ≤ p.1 1 := by simpa [hq1eq] using hbc
      exact (p.2 1).2.antisymm hbc'
    have hp0eq : p.1 0 = 1 := by
      rw [hp1eq, hq1eq] at hprod
      simpa using hprod
    have hq0eq : q.1 0 = 1 := by
      rw [hp1eq] at heq2
      exact heq2.symm
    exact ⟨hp0eq, hp1eq, hq0eq, hq1eq⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2HoneycombLaurentFiniteIdentity_zero_two
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 0 p = constructedA2PlaneTile v 2 q ↔
      constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 2)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 2))
            (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 2 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2PlaneTile_zero_eq_two_iff v p q).trans
    (constructedA2_zero_two_transition_iff v p q).symm

public theorem constructedA2CellTransitionMatrix_zero_three (v : ToricLattice) :
    transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 3) =
      !![(0 : ℤ), 0, -1; 0, -1, 0; 1, 2, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, transitionMatrix, dualMatrix,
      a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂,
      Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem constructedA2PlaneTile_zero_eq_three_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 0 p = constructedA2PlaneTile v 3 q ↔
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
      | rw [constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_le v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_le v 0 p hp,
          constructedA2PlaneTile_of_ge v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_le v 3 q hq] at h
      | rw [constructedA2PlaneTile_of_ge v 0 p hp,
          constructedA2PlaneTile_of_ge v 3 q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] at h0 h1
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
      simp [constructedA2PlaneTile, hp0, hp1, hq0, hq1,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset]

public theorem constructedA2_zero_three_transition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 3)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 3))
          (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [constructedA2CellTransitionMatrix_zero_three]
  constructor
  · rintro ⟨hdomain, heq⟩
    have hp0c : (p.1 0 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1
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
        simp_all [constructedA2CellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem constructedA2HoneycombLaurentFiniteIdentity_zero_three
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v 0 p = constructedA2PlaneTile v 3 q ↔
      constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 3)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 0) (constructedA2CellChart v 3))
            (constructedA2CellLiftCoordinates 0 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 3 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2PlaneTile_zero_eq_three_iff v p q).trans
    (constructedA2_zero_three_transition_iff v p q).symm

public theorem constructedA2LaurentTransition_comm
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
          (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) ↔
    (constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i))
          (constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) =
        constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) := by
  rw [← constructedA2CellSquareProjection_eq_iff_monomial
      (r := 1) zero_lt_one v w i j p q,
    ← constructedA2CellSquareProjection_eq_iff_monomial
      (r := 1) zero_lt_one w v j i q p]
  exact eq_comm

public theorem constructedA2HoneycombLaurentFiniteIdentity_reverse
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2PlaneTile v i p = constructedA2PlaneTile w j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    constructedA2PlaneTile w j q = constructedA2PlaneTile v i p ↔
      constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart w j) (constructedA2CellChart v i))
            (constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) =
          constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) := by
  rw [eq_comm, h, constructedA2LaurentTransition_comm]

public def constructedA2NeighborMismatchSquare : ConstructedA2CellSquare :=
  ⟨![0, 1], by intro k; fin_cases k <;> simp⟩

public theorem constructedA2NeighborMismatch_plane
    (v : ToricLattice) :
    constructedA2PlaneTile v 0 constructedA2NeighborMismatchSquare ≠
      constructedA2PlaneTile (v + e₁) 3 constructedA2NeighborMismatchSquare := by
  intro h
  have h0 := congrFun h 0
  simp [constructedA2NeighborMismatchSquare, constructedA2PlaneTile,
    constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
    constructedA2PlaneNextMidpointOffset, e₁] at h0
  norm_num at h0
  linarith

public theorem constructedA2NeighborMismatch_laurent
    (v : ToricLattice) :
    constructedA2CellLiftCoordinates 0
          (fun k ↦ (constructedA2NeighborMismatchSquare.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 3)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 0)
            (constructedA2CellChart (v + e₁) 3))
          (constructedA2CellLiftCoordinates 0
            (fun k ↦ (constructedA2NeighborMismatchSquare.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 3
          (fun k ↦ (constructedA2NeighborMismatchSquare.1 k : ℂ)) := by
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
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [constructedA2NeighborMismatchSquare, constructedA2CellLiftCoordinates]
  · ext k
    fin_cases k <;>
      simp [constructedA2NeighborMismatchSquare, monomial,
        constructedA2CellLiftCoordinates, Fin.prod_univ_succ]

public theorem not_constructedA2HoneycombLaurentFiniteIdentity :
    ¬ ConstructedA2HoneycombLaurentFiniteIdentity := by
  intro h
  have hv := h 0 e₁ 0 3 constructedA2NeighborMismatchSquare
    constructedA2NeighborMismatchSquare
  apply constructedA2NeighborMismatch_plane 0
  simpa using hv.mpr (constructedA2NeighborMismatch_laurent 0)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
