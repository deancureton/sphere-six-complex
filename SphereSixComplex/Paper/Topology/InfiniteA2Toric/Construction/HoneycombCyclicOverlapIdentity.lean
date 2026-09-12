module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombSameCellFiniteIdentity

/-!
# Cyclic overlap identities for the constructed A₂ honeycomb

The adjacent planar sectors meet along the same edge as their explicit Laurent toric charts.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public theorem planeTile_eq_nextIndex_iff
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    planeTile v i p =
        planeTile v (cellNextIndex i) q ↔
      p.1 0 = 1 ∧ q.1 1 = 1 ∧ p.1 1 = q.1 0 := by
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
      | rw [planeTile_of_le v i p hp,
          planeTile_of_le v (cellNextIndex i) q hq] at h
      | rw [planeTile_of_le v i p hp,
          planeTile_of_ge v (cellNextIndex i) q hq] at h
      | rw [planeTile_of_ge v i p hp,
          planeTile_of_le v (cellNextIndex i) q hq] at h
      | rw [planeTile_of_ge v i p hp,
          planeTile_of_ge v (cellNextIndex i) q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      fin_cases i <;>
        simp [cellNextIndex, Pi.add_apply, smul_eq_mul,
          planeVertexOffset, planeMidpointOffset,
          planeNextMidpointOffset] at h0 h1 <;>
        norm_num at h0 h1 <;>
        refine ⟨?_, ?_, ?_⟩ <;>
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
  · rintro ⟨hp, hq, hpq⟩
    have hpord : p.1 1 ≤ p.1 0 := by linarith [hp1.2]
    have hqord : q.1 0 ≤ q.1 1 := by linarith [hq0.2]
    rw [planeTile_of_ge v i p hpord,
      planeTile_of_le v (cellNextIndex i) q hqord]
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [cellNextIndex, Pi.add_apply, smul_eq_mul,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset] <;>
      norm_num <;> linarith

public theorem cellLift_mem_nextTransitionDomain_iff
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) :
    cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v i)
            (cellChart v (cellNextIndex i))) ↔
      p.1 0 ≠ 0 := by
  rw [cellTransitionMatrix_nextIndex]
  fin_cases i
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 1 1 (by norm_num)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 0 2 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 0 2 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 1 1 (by norm_num)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 2 0 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, cellLiftCoordinates, hp] using h 2 0 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [cellLiftCoordinates]

public theorem nextTransition_eq_of_boundary
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare)
    (hp : p.1 0 = 1) (hq : q.1 1 = 1) (hpq : p.1 1 = q.1 0) :
    monomial
        (transitionMatrix (cellChart v i)
          (cellChart v (cellNextIndex i)))
        (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
      cellLiftCoordinates (cellNextIndex i)
        (fun k ↦ (q.1 k : ℂ)) := by
  rw [cellTransitionMatrix_nextIndex]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [monomial, cellLiftCoordinates, cellNextIndex,
      Fin.prod_univ_succ, hp, hq, hpq]

private theorem boundary_of_inverse_and_mul
    (p q : CellSquare) (hpne : p.1 0 ≠ 0)
    (hinv : ((p.1 0 : ℂ)⁻¹) = (q.1 1 : ℂ))
    (hmul : (p.1 0 : ℂ) * (p.1 1 : ℂ) = (q.1 0 : ℂ)) :
    p.1 0 = 1 ∧ q.1 1 = 1 ∧ p.1 1 = q.1 0 := by
  have hpne' : (p.1 0 : ℂ) ≠ 0 := by exact_mod_cast hpne
  have hc : (p.1 0 : ℂ) * (q.1 1 : ℂ) = 1 := by
    rw [← hinv]
    exact mul_inv_cancel₀ hpne'
  have hr : p.1 0 * q.1 1 = 1 := by
    simpa using congrArg Complex.re hc
  have hnonneg₀ : 0 ≤ (1 - p.1 0) * q.1 1 :=
    mul_nonneg (sub_nonneg.mpr (p.2 0).2) (q.2 1).1
  have hnonneg₁ : 0 ≤ (1 - q.1 1) * p.1 0 :=
    mul_nonneg (sub_nonneg.mpr (q.2 1).2) (p.2 0).1
  have hp : p.1 0 = 1 := by nlinarith
  have hq : q.1 1 = 1 := by nlinarith
  refine ⟨hp, hq, ?_⟩
  have hmul' := congrArg Complex.re hmul
  simpa [hp] using hmul'

public theorem nextTransition_boundary_iff
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v i)
            (cellChart v (cellNextIndex i))) ∧
      monomial
          (transitionMatrix (cellChart v i)
            (cellChart v (cellNextIndex i)))
          (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates (cellNextIndex i)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ q.1 1 = 1 ∧ p.1 1 = q.1 0 := by
  constructor
  · rintro ⟨hdomain, heq⟩
    have hpne :=
      (cellLift_mem_nextTransitionDomain_iff v i p).mp hdomain
    rw [cellTransitionMatrix_nextIndex] at heq
    fin_cases i
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 2
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 1
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 0
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
    · apply boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
      · simpa [monomial, cellLiftCoordinates, cellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
  · rintro ⟨hp, hq, hpq⟩
    constructor
    · apply (cellLift_mem_nextTransitionDomain_iff v i p).mpr
      simp [hp]
    · exact nextTransition_eq_of_boundary v i p q hp hq hpq

public theorem honeycombLaurentFiniteIdentity_nextChart
    (v : ToricLattice) (i : Fin 6) (p q : CellSquare) :
    planeTile v i p =
        planeTile v (cellNextIndex i) q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i)
              (cellChart v (cellNextIndex i))) ∧
        monomial
            (transitionMatrix (cellChart v i)
              (cellChart v (cellNextIndex i)))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates (cellNextIndex i)
            (fun k ↦ (q.1 k : ℂ)) :=
  (planeTile_eq_nextIndex_iff v i p q).trans
    (nextTransition_boundary_iff v i p q).symm

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end

end
