module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedPlaneTileProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2CorrectedPlaneTile_thirdNeighbor_iff
    (v : ToricLattice) (p r : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 2 p =
        constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 r ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ r.1 0 = 0 ∧ r.1 1 = 1 := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hr0 := r.2 0
  have hr1 := r.2 1
  constructor
  · intro h
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (r.1 0) (r.1 1) with hr | hr
    all_goals
      first
      | rw [show constructedA2CorrectedPlaneTile v 2 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 2 p by rfl,
          show constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 r =
            (constructedA2CorrectedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              constructedA2PlaneTile (v + (e₂ - e₁)) 5 r by rfl,
          constructedA2PlaneTile_of_le v 2 p hp,
          constructedA2PlaneTile_of_le (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show constructedA2CorrectedPlaneTile v 2 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 2 p by rfl,
          show constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 r =
            (constructedA2CorrectedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              constructedA2PlaneTile (v + (e₂ - e₁)) 5 r by rfl,
          constructedA2PlaneTile_of_le v 2 p hp,
          constructedA2PlaneTile_of_ge (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show constructedA2CorrectedPlaneTile v 2 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 2 p by rfl,
          show constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 r =
            (constructedA2CorrectedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              constructedA2PlaneTile (v + (e₂ - e₁)) 5 r by rfl,
          constructedA2PlaneTile_of_ge v 2 p hp,
          constructedA2PlaneTile_of_le (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show constructedA2CorrectedPlaneTile v 2 p =
            (constructedA2CorrectedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              constructedA2PlaneTile v 2 p by rfl,
          show constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 r =
            (constructedA2CorrectedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              constructedA2PlaneTile (v + (e₂ - e₁)) 5 r by rfl,
          constructedA2PlaneTile_of_ge v 2 p hp,
          constructedA2PlaneTile_of_ge (v + (e₂ - e₁)) 5 r hr] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneCenter,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, e₁, e₂] at h0 h1
      have hp0eq : p.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hr0.1, hr0.2, hr1.1, hr1.2]
      have hp1eq : p.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hr0.1, hr0.2, hr1.1, hr1.2]
      have hr0eq : r.1 0 = 0 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hr0.1, hr0.2, hr1.1, hr1.2]
      have hr1eq : r.1 1 = 1 := by
        norm_num [div_eq_mul_inv] at h0 h1
        linarith [hp0.1, hp0.2, hp1.1, hp1.2, hr0.1, hr0.2, hr1.1, hr1.2]
      exact ⟨hp0eq, hp1eq, hr0eq, hr1eq⟩
  · rintro ⟨hp0, hp1, hr0, hr1⟩
    ext k
    fin_cases k <;>
      simp [Matrix.vecHead, Matrix.vecTail, constructedA2CorrectedPlaneTile,
        constructedA2CorrectedPlaneCenter, constructedA2PlaneTile,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset, hp0, hp1, hr0, hr1, e₁, e₂] <;> ring

public theorem constructedA2ThirdNeighborTransition_iff
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (constructedA2CellChart v 2)
            (constructedA2CellChart (v + (e₂ - e₁)) 5)) ∧
      monomial
          (transitionMatrix (constructedA2CellChart v 2)
            (constructedA2CellChart (v + (e₂ - e₁)) 5))
          (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
        constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (constructedA2CellChart v 2)
      (constructedA2CellChart (v + (e₂ - e₁)) 5) =
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
    have hp1c : (p.1 1 : ℂ) ≠ 0 := by
      simpa [constructedA2CellLiftCoordinates] using
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, constructedA2CellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
    have hprod : p.1 1 * q.1 1 = 1 := by
      field_simp [hp1c] at heq2
      exact (by exact_mod_cast congrArg Complex.re heq2.symm)
    have hpq_le : p.1 1 * q.1 1 ≤ q.1 1 :=
      mul_le_of_le_one_left (q.2 1).1 (p.2 1).2
    have hq1 : q.1 1 = 1 := (q.2 1).2.antisymm (hprod.ge.trans hpq_le)
    have hp1 : p.1 1 = 1 := by rw [hq1] at hprod; simpa using hprod
    have hp0r : p.1 0 = 0 := by
      rcases heq1 with hp1zero | hp0zero
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

public theorem constructedA2CorrectedLaurentIdentity_thirdNeighbor
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v 2 p =
        constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5 q ↔
      constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v 2)
              (constructedA2CellChart (v + (e₂ - e₁)) 5)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v 2)
              (constructedA2CellChart (v + (e₂ - e₁)) 5))
            (constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ)) :=
  (constructedA2CorrectedPlaneTile_thirdNeighbor_iff v p q).trans
    (constructedA2ThirdNeighborTransition_iff v p q).symm

public theorem constructedA2CorrectedLaurentIdentity_thirdNeighbor_reverse
    (v : ToricLattice) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile (v + (e₂ - e₁)) 5
        q = constructedA2CorrectedPlaneTile v 2 p ↔
      constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix
              (constructedA2CellChart (v + (e₂ - e₁)) 5)
              (constructedA2CellChart v 2)) ∧
        monomial
            (transitionMatrix
              (constructedA2CellChart (v + (e₂ - e₁)) 5)
              (constructedA2CellChart v 2))
            (constructedA2CellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ))) =
          constructedA2CellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) := by
  rw [eq_comm, constructedA2CorrectedLaurentIdentity_thirdNeighbor,
    constructedA2LaurentTransition_comm]

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
