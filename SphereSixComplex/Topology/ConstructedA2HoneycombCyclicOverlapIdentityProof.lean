module

public import SphereSixComplex.Topology.ConstructedA2HoneycombSameCellFiniteIdentityProof

/-!
# Cyclic overlap identities for the constructed A₂ honeycomb

The adjacent planar sectors meet along the same edge as their explicit Laurent toric charts.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2PlaneTile_eq_nextIndex_iff
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p =
        constructedA2PlaneTile v (constructedA2CellNextIndex i) q ↔
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
      | rw [constructedA2PlaneTile_of_le v i p hp,
          constructedA2PlaneTile_of_le v (constructedA2CellNextIndex i) q hq] at h
      | rw [constructedA2PlaneTile_of_le v i p hp,
          constructedA2PlaneTile_of_ge v (constructedA2CellNextIndex i) q hq] at h
      | rw [constructedA2PlaneTile_of_ge v i p hp,
          constructedA2PlaneTile_of_le v (constructedA2CellNextIndex i) q hq] at h
      | rw [constructedA2PlaneTile_of_ge v i p hp,
          constructedA2PlaneTile_of_ge v (constructedA2CellNextIndex i) q hq] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      fin_cases i <;>
        simp [constructedA2CellNextIndex, Pi.add_apply, smul_eq_mul,
          constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          constructedA2PlaneNextMidpointOffset] at h0 h1 <;>
        norm_num at h0 h1 <;>
        refine ⟨?_, ?_, ?_⟩ <;>
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]
  · rintro ⟨hp, hq, hpq⟩
    have hpord : p.1 1 ≤ p.1 0 := by linarith [hp1.2]
    have hqord : q.1 0 ≤ q.1 1 := by linarith [hq0.2]
    rw [constructedA2PlaneTile_of_ge v i p hpord,
      constructedA2PlaneTile_of_le v (constructedA2CellNextIndex i) q hqord]
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [constructedA2CellNextIndex, Pi.add_apply, smul_eq_mul,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] <;>
      norm_num <;> linarith

public theorem constructedA2CellLift_mem_nextTransitionDomain_iff
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v i)
            (constructedA2CellChart v (constructedA2CellNextIndex i))) ↔
      p.1 0 ≠ 0 := by
  rw [constructedA2CellTransitionMatrix_nextIndex]
  fin_cases i
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 1 1 (by norm_num)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 0 2 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 0 2 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 1 1 (by norm_num)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 2 0 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]
  · constructor
    · intro h hp
      simpa [monomialDomain, constructedA2CellLiftCoordinates, hp] using h 2 0 (by decide)
    · intro hp a b hab
      fin_cases a <;> fin_cases b <;> simp_all [constructedA2CellLiftCoordinates]

public theorem constructedA2_nextTransition_eq_of_boundary
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare)
    (hp : p.1 0 = 1) (hq : q.1 1 = 1) (hpq : p.1 1 = q.1 0) :
    monomial
        (transitionMatrix (constructedA2CellChart v i)
          (constructedA2CellChart v (constructedA2CellNextIndex i)))
        (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
      constructedA2CellLiftCoordinates (constructedA2CellNextIndex i)
        (fun k ↦ (q.1 k : ℂ)) := by
  rw [constructedA2CellTransitionMatrix_nextIndex]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
      Fin.prod_univ_succ, hp, hq, hpq]

private theorem constructedA2_boundary_of_inverse_and_mul
    (p q : ConstructedA2CellSquare) (hpne : p.1 0 ≠ 0)
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

public theorem constructedA2_nextTransition_boundary_iff
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v i)
            (constructedA2CellChart v (constructedA2CellNextIndex i))) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v i)
            (constructedA2CellChart v (constructedA2CellNextIndex i)))
          (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates (constructedA2CellNextIndex i)
          (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 1 ∧ q.1 1 = 1 ∧ p.1 1 = q.1 0 := by
  constructor
  · rintro ⟨hdomain, heq⟩
    have hpne :=
      (constructedA2CellLift_mem_nextTransitionDomain_iff v i p).mp hdomain
    rw [constructedA2CellTransitionMatrix_nextIndex] at heq
    fin_cases i
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 2
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 1
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ, mul_comm] using congrFun heq 0
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 0
    · apply constructedA2_boundary_of_inverse_and_mul p q hpne
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 2
      · simpa [monomial, constructedA2CellLiftCoordinates, constructedA2CellNextIndex,
          Fin.prod_univ_succ] using congrFun heq 1
  · rintro ⟨hp, hq, hpq⟩
    constructor
    · apply (constructedA2CellLift_mem_nextTransitionDomain_iff v i p).mpr
      simp [hp]
    · exact constructedA2_nextTransition_eq_of_boundary v i p q hp hq hpq

public theorem constructedA2HoneycombLaurentFiniteIdentity_nextChart
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p =
        constructedA2PlaneTile v (constructedA2CellNextIndex i) q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v (constructedA2CellNextIndex i))) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i)
              (constructedA2CellChart v (constructedA2CellNextIndex i)))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates (constructedA2CellNextIndex i)
            (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2PlaneTile_eq_nextIndex_iff v i p q).trans
    (constructedA2_nextTransition_boundary_iff v i p q).symm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
