module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CorrectedPlaneTiles

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public theorem correctedPlaneTile_thirdNeighbor_iff
    (v : ToricLattice) (p r : CellSquare) :
    correctedPlaneTile v 2 p =
        correctedPlaneTile (v + (e₂ - e₁)) 5 r ↔
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
      | rw [show correctedPlaneTile v 2 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 2 p by rfl,
          show correctedPlaneTile (v + (e₂ - e₁)) 5 r =
            (correctedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              planeTile (v + (e₂ - e₁)) 5 r by rfl,
          planeTile_of_le v 2 p hp,
          planeTile_of_le (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show correctedPlaneTile v 2 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 2 p by rfl,
          show correctedPlaneTile (v + (e₂ - e₁)) 5 r =
            (correctedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              planeTile (v + (e₂ - e₁)) 5 r by rfl,
          planeTile_of_le v 2 p hp,
          planeTile_of_ge (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show correctedPlaneTile v 2 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 2 p by rfl,
          show correctedPlaneTile (v + (e₂ - e₁)) 5 r =
            (correctedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              planeTile (v + (e₂ - e₁)) 5 r by rfl,
          planeTile_of_ge v 2 p hp,
          planeTile_of_le (v + (e₂ - e₁)) 5 r hr] at h
      | rw [show correctedPlaneTile v 2 p =
            (correctedPlaneCenter v - fun k ↦ (v k : ℝ)) +
              planeTile v 2 p by rfl,
          show correctedPlaneTile (v + (e₂ - e₁)) 5 r =
            (correctedPlaneCenter (v + (e₂ - e₁)) -
                fun k ↦ ((v + (e₂ - e₁)) k : ℝ)) +
              planeTile (v + (e₂ - e₁)) 5 r by rfl,
          planeTile_of_ge v 2 p hp,
          planeTile_of_ge (v + (e₂ - e₁)) 5 r hr] at h
    all_goals
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneCenter,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, e₁, e₂] at h0 h1
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
      simp [Matrix.vecHead, Matrix.vecTail, correctedPlaneTile,
        correctedPlaneCenter, planeTile,
        planeVertexOffset, planeMidpointOffset,
        planeNextMidpointOffset, hp0, hp1, hr0, hr1, e₁, e₂] <;> ring

public theorem thirdNeighborTransition_iff
    (v : ToricLattice) (p q : CellSquare) :
    (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
        monomialDomain
          (transitionMatrix (cellChart v 2)
            (cellChart (v + (e₂ - e₁)) 5)) ∧
      monomial
          (transitionMatrix (cellChart v 2)
            (cellChart (v + (e₂ - e₁)) 5))
          (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
        cellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ))) ↔
      p.1 0 = 0 ∧ p.1 1 = 1 ∧ q.1 0 = 0 ∧ q.1 1 = 1 := by
  rw [show transitionMatrix (cellChart v 2)
      (cellChart (v + (e₂ - e₁)) 5) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] by
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
        hdomain (2 : Fin 3) (0 : Fin 3) (by decide)
    have heq0 := congrFun heq 0
    have heq1 := congrFun heq 1
    have heq2 := congrFun heq 2
    simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ] at heq0 heq1 heq2
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
        simp_all [cellLiftCoordinates]
    · ext k
      fin_cases k <;>
        simp [monomial, cellLiftCoordinates, Fin.prod_univ_succ,
          hp0, hp1, hq0, hq1]

public theorem correctedLaurentIdentity_thirdNeighbor
    (v : ToricLattice) (p q : CellSquare) :
    correctedPlaneTile v 2 p =
        correctedPlaneTile (v + (e₂ - e₁)) 5 q ↔
      cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v 2)
              (cellChart (v + (e₂ - e₁)) 5)) ∧
        monomial
            (transitionMatrix (cellChart v 2)
              (cellChart (v + (e₂ - e₁)) 5))
            (cellLiftCoordinates 2 (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates 5 (fun k ↦ (q.1 k : ℂ)) :=
  (correctedPlaneTile_thirdNeighbor_iff v p q).trans
    (thirdNeighborTransition_iff v p q).symm


end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
