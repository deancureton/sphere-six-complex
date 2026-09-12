module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CorrectedCellGeometry

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric











public theorem planeTile_eq_secondNext_iff
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    planeTile v i p =
        planeTile v
          (cellNextIndex (cellNextIndex i)) q ↔
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
      | rw [planeTile_of_le _ _ p hp,
          planeTile_of_le _ _ q hq] at h
      | rw [planeTile_of_le _ _ p hp,
          planeTile_of_ge _ _ q hq] at h
      | rw [planeTile_of_ge _ _ p hp,
          planeTile_of_le _ _ q hq] at h
      | rw [planeTile_of_ge _ _ p hp,
          planeTile_of_ge _ _ q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [cellNextIndex, planeVertexOffset,
        planeMidpointOffset, planeNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    simp [planeTile, hp0, hp1, hq0, hq1]

public def distanceTwoTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![(0 : ℤ), -1, -1; 1, 2, 1; 0, 0, 1],
    !![(0 : ℤ), -1, -1; 0, 1, 0; 1, 1, 2],
    !![(1 : ℤ), 0, 0; -1, 0, -1; 1, 1, 2],
    !![(1 : ℤ), 0, 0; 1, 2, 1; -1, -1, 0],
    !![(2 : ℤ), 1, 1; 0, 1, 0; -1, -1, 0],
    !![(2 : ℤ), 1, 1; -1, 0, -1; 0, 0, 1]]

public theorem cellTransitionMatrix_secondNext
    (v : ToricLattice) (i : Fin 6) :
    transitionMatrix (cellChart v i)
        (cellChart v
          (cellNextIndex (cellNextIndex i))) =
      distanceTwoTransitionMatrix i := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  fin_cases i <;>
    ext a b <;>
    fin_cases a <;>
    fin_cases b <;>
    simp [distanceTwoTransitionMatrix, cellChart,
      cellNextIndex, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem all_one_of_inverse_product
    (p q : CellSquare)
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

public theorem secondNext_transition_iff
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v i)
            (cellChart v
              (cellNextIndex (cellNextIndex i)))) ∧
      monomial
          (transitionMatrix (cellChart v i)
            (cellChart v
              (cellNextIndex (cellNextIndex i))))
          (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates
          (cellNextIndex (cellNextIndex i))
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [cellTransitionMatrix_secondNext]
  constructor
  · rintro ⟨hdomain, heq⟩
    fin_cases i
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (0 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial, mul_comm,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (1 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (1 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial, mul_comm,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (2 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial, mul_comm,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 0
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (2 : Fin 3) (1 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
    · apply all_one_of_inverse_product p q
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (1 : Fin 3) (0 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix,
          cellLiftCoordinates] using
          hdomain (1 : Fin 3) (2 : Fin 3) (by decide)
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 1
      · simpa [distanceTwoTransitionMatrix, cellNextIndex, monomial,
          cellLiftCoordinates, Fin.prod_univ_succ] using congrFun heq 2
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    fin_cases i
    all_goals
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b <;>
          simp_all [distanceTwoTransitionMatrix,
            cellLiftCoordinates]
      · ext k
        fin_cases k <;>
          simp [distanceTwoTransitionMatrix, cellNextIndex,
            monomial, cellLiftCoordinates, Fin.prod_univ_succ,
            hp0, hp1, hq0, hq1]

public theorem correctedLaurentIdentity_secondNext
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p =
        correctedPlaneTile v
          (cellNextIndex (cellNextIndex i)) q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart v
                (cellNextIndex (cellNextIndex i)))) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart v
                (cellNextIndex (cellNextIndex i))))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates
            (cellNextIndex (cellNextIndex i))
            (fun k ↦ (q.1 k : ℂ)) := by
  rw [correctedPlaneTile_sameCell_iff,
    planeTile_eq_secondNext_iff, secondNext_transition_iff]

public theorem planeTile_eq_thirdNext_iff
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    planeTile v i p =
        planeTile v
          (cellNextIndex
            (cellNextIndex (cellNextIndex i))) q ↔
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
      | rw [planeTile_of_le _ _ p hp,
          planeTile_of_le _ _ q hq] at h
      | rw [planeTile_of_le _ _ p hp,
          planeTile_of_ge _ _ q hq] at h
      | rw [planeTile_of_ge _ _ p hp,
          planeTile_of_le _ _ q hq] at h
      | rw [planeTile_of_ge _ _ p hp,
          planeTile_of_ge _ _ q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [cellNextIndex, planeVertexOffset,
        planeMidpointOffset, planeNextMidpointOffset] at h0 h1
      norm_num [div_eq_mul_inv] at h0 h1
      refine ⟨by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2],
        by linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]⟩
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    simp [planeTile, hp0, hp1, hq0, hq1]

private theorem all_one_of_two_inverses
    (p q : CellSquare)
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

public theorem cellTransitionMatrix_one_four (v : ToricLattice) :
    transitionMatrix (cellChart v 1) (cellChart v 4) =
      !![(0 : ℤ), 0, -1; 0, -1, 0; 1, 2, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem one_four_transition_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 1) (cellChart v 4)) ∧
      monomial
          (transitionMatrix (cellChart v 1) (cellChart v 4))
          (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [cellTransitionMatrix_one_four]
  constructor
  · rintro ⟨hdomain, heq⟩
    apply all_one_of_two_inverses p q
    · simpa [cellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    · simpa [cellLiftCoordinates] using
        hdomain (1 : Fin 3) (1 : Fin 3) (by decide)
    · simpa [monomial, cellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 0
    · simpa [monomial, cellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 1
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem cellTransitionMatrix_two_five (v : ToricLattice) :
    transitionMatrix (cellChart v 2) (cellChart v 5) =
      !![(0 : ℤ), 0, -1; 2, 1, 2; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cellChart, transitionMatrix, dualMatrix, a2DualCharacter,
      a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

public theorem two_five_transition_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 2) (cellChart v 5)) ∧
      monomial
          (transitionMatrix (cellChart v 2) (cellChart v 5))
          (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
  rw [cellTransitionMatrix_two_five]
  constructor
  · rintro ⟨hdomain, heq⟩
    apply all_one_of_two_inverses p q
    · simpa [cellLiftCoordinates] using
        hdomain (0 : Fin 3) (2 : Fin 3) (by decide)
    · simpa [cellLiftCoordinates] using
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    · simpa [monomial, cellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 0
    · simpa [monomial, cellLiftCoordinates, Fin.prod_univ_succ] using
        congrFun heq 2
  · rintro ⟨hp0, hp1, hq0, hq1⟩
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem correctedLaurentIdentity_one_four
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 1 p = correctedPlaneTile v 4 q ↔
      cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 1) (cellChart v 4)) ∧
        monomial
            (transitionMatrix (cellChart v 1) (cellChart v 4))
            (cellLiftCoordinates 1 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 4 (fun k ↦ (q.1 k : ℂ)) := by
  rw [correctedPlaneTile_sameCell_iff]
  have hplane := planeTile_eq_thirdNext_iff v (1 : Fin 6) p q
  have hplane' : planeTile v 1 p = planeTile v 4 q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
    simpa [cellNextIndex] using hplane
  exact hplane'.trans (one_four_transition_iff v p q).symm

public theorem correctedLaurentIdentity_two_five
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 2 p = correctedPlaneTile v 5 q ↔
      cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 2) (cellChart v 5)) ∧
        monomial
            (transitionMatrix (cellChart v 2) (cellChart v 5))
            (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ)) := by
  rw [correctedPlaneTile_sameCell_iff]
  have hplane := planeTile_eq_thirdNext_iff v (2 : Fin 6) p q
  have hplane' : planeTile v 2 p = planeTile v 5 q ↔
      p.1 0 = 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = 1 := by
    simpa [cellNextIndex] using hplane
  exact hplane'.trans (two_five_transition_iff v p q).symm

public theorem correctedLaurentIdentity_thirdNext
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p =
        correctedPlaneTile v
          (cellNextIndex
            (cellNextIndex (cellNextIndex i))) q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart v
                (cellNextIndex
                  (cellNextIndex (cellNextIndex i))))) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart v
                (cellNextIndex
                  (cellNextIndex (cellNextIndex i)))))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates
            (cellNextIndex
              (cellNextIndex (cellNextIndex i)))
            (fun k ↦ (q.1 k : ℂ)) := by
  have h03 (a b : CellSquare) :=
    correctedLaurentIdentity_of_sameCell v 0 3 a b
      (honeycombLaurentFiniteIdentity_zero_three v a b)
  fin_cases i
  · simpa [cellNextIndex] using h03 p q
  · simpa [cellNextIndex] using
      correctedLaurentIdentity_one_four v p q
  · simpa [cellNextIndex] using
      correctedLaurentIdentity_two_five v p q
  · simpa [cellNextIndex] using
      correctedLaurentIdentity_reverse v v 0 3 q p (h03 q p)
  · simpa [cellNextIndex] using
      correctedLaurentIdentity_reverse v v 1 4 q p
        (correctedLaurentIdentity_one_four v q p)
  · simpa [cellNextIndex] using
      correctedLaurentIdentity_reverse v v 2 5 q p
        (correctedLaurentIdentity_two_five v q p)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
