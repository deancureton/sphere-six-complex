module

public import SphereSixComplex.Topology.ConstructedA2HoneycombFiniteQuotientProof

/-!
# The same-cell finite identity for the constructed A₂ honeycomb

This file proves the Laurent finite identity when both square charts lie over the same
lattice cell.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- Each of the six planar tile parametrizations is injective. -/
public theorem constructedA2PlaneTile_injective (v : ToricLattice) (i : Fin 6) :
    Function.Injective (constructedA2PlaneTile v i) := by
  intro p q hpq
  apply Subtype.ext
  funext k
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hq0 := q.2 0
  have hq1 := q.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
    rcases le_total (q.1 0) (q.1 1) with hq | hq
  all_goals
    first
    | rw [constructedA2PlaneTile_of_le v i p hp,
        constructedA2PlaneTile_of_le v i q hq] at hpq
    | rw [constructedA2PlaneTile_of_le v i p hp,
        constructedA2PlaneTile_of_ge v i q hq] at hpq
    | rw [constructedA2PlaneTile_of_ge v i p hp,
        constructedA2PlaneTile_of_le v i q hq] at hpq
    | rw [constructedA2PlaneTile_of_ge v i p hp,
        constructedA2PlaneTile_of_ge v i q hq] at hpq
  all_goals
    have h0 := congrFun hpq 0
    have h1 := congrFun hpq 1
    fin_cases i <;> fin_cases k <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
        constructedA2PlaneNextMidpointOffset] at h0 h1 ⊢ <;>
      norm_num at h0 h1 ⊢ <;>
      linarith [hp0.1, hp0.2, hp1.1, hp1.2, hq0.1, hq0.2, hq1.1, hq1.2]

/-- The Laurent finite identity when both sides use the same square chart. -/
public theorem constructedA2HoneycombLaurentFiniteIdentity_sameChart
    (v : ToricLattice) (i : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p = constructedA2PlaneTile v i q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v i)) ∧
        monomial (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v i))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates i (fun k ↦ (q.1 k : ℂ)) := by
  rw [transitionMatrix_self]
  rw [monomial_one]
  have hdomain : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
      monomialDomain (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
    intro a b hab
    simp only [Matrix.one_apply] at hab
    split at hab <;> omega
  constructor
  · intro hpq
    have hpq' : p = q := constructedA2PlaneTile_injective v i hpq
    subst q
    exact ⟨hdomain, rfl⟩
  · rintro ⟨_, hpq⟩
    apply congrArg (constructedA2PlaneTile v i)
    apply Subtype.ext
    funext k
    have h := congrArg (constructedA2CellRemoveCoordinates i) hpq
    simp only [constructedA2CellRemoveCoordinates_lift] at h
    exact congrArg Complex.re (congrFun h k)

public theorem constructedA2CellTransitionMatrix_nextIndex (v : ToricLattice) (i : Fin 6) :
    transitionMatrix (constructedA2CellChart v i)
        (constructedA2CellChart v (constructedA2CellNextIndex i)) =
      ![!![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1],
        !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1],
        !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1],
        !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1],
        !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0],
        !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0]] i := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [constructedA2CellChart, constructedA2CellNextIndex, transitionMatrix, dualMatrix,
      a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply,
      Fin.sum_univ_succ, hv0, hv1] <;> ring

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
