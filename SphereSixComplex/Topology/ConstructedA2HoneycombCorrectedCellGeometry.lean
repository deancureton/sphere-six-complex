module

public import SphereSixComplex.Topology.ConstructedA2HoneycombThirdNeighborProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def constructedA2CorrectedPlaneCell (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | |x 0 - constructedA2CorrectedPlaneCenter v 0| ≤ 2 / 3 ∧
    |x 1 - constructedA2CorrectedPlaneCenter v 1| ≤ 2 / 3 ∧
    |(x 0 - x 1) -
      (constructedA2CorrectedPlaneCenter v 0 - constructedA2CorrectedPlaneCenter v 1)| ≤ 2 / 3}

public theorem constructedA2CorrectedPlaneTile_mem
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p ∈ constructedA2CorrectedPlaneCell v := by
  have h := constructedA2PlaneTile_mem v i p
  rcases h with ⟨h0, h1, hd⟩
  have hcoordinate (k : Fin 2) :
      constructedA2CorrectedPlaneTile v i p k - constructedA2CorrectedPlaneCenter v k =
        constructedA2PlaneTile v i p k - (v k : ℝ) := by
    simp only [constructedA2CorrectedPlaneTile, Pi.add_apply, Pi.sub_apply]
    ring
  constructor
  · rw [hcoordinate]
    exact h0
  constructor
  · rw [hcoordinate]
    exact h1
  · rw [show (constructedA2CorrectedPlaneTile v i p 0 -
          constructedA2CorrectedPlaneTile v i p 1) -
          (constructedA2CorrectedPlaneCenter v 0 - constructedA2CorrectedPlaneCenter v 1) =
        (constructedA2CorrectedPlaneTile v i p 0 - constructedA2CorrectedPlaneCenter v 0) -
          (constructedA2CorrectedPlaneTile v i p 1 - constructedA2CorrectedPlaneCenter v 1) by
        ring, hcoordinate, hcoordinate]
    rw [show constructedA2PlaneTile v i p 0 - (v 0 : ℝ) -
          (constructedA2PlaneTile v i p 1 - (v 1 : ℝ)) =
        constructedA2PlaneTile v i p 0 - constructedA2PlaneTile v i p 1 -
          ((v 0 : ℝ) - (v 1 : ℝ)) by ring]
    exact hd

public theorem constructedA2CorrectedPlaneCell_inter_nonempty_displacement
    (v w : ToricLattice)
    (h : (constructedA2CorrectedPlaneCell v ∩
      constructedA2CorrectedPlaneCell w).Nonempty) :
    w - v ∈ ({0, e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂} :
      Set ToricLattice) := by
  obtain ⟨x, hxv, hxw⟩ := h
  rcases hxv with ⟨hv0, hv1, hvd⟩
  rcases hxw with ⟨hw0, hw1, hwd⟩
  have hv0' := abs_le.mp hv0
  have hv1' := abs_le.mp hv1
  have hvd' := abs_le.mp hvd
  have hw0' := abs_le.mp hw0
  have hw1' := abs_le.mp hw1
  have hwd' := abs_le.mp hwd
  have h0lo : (-2 : ℤ) ≤ (w 0 - v 0) + 2 * (w 1 - v 1) := by
    have hr : (-2 : ℝ) ≤ ((w 0 - v 0) + 2 * (w 1 - v 1) : ℤ) := by
      simp only [constructedA2CorrectedPlaneCenter] at hv0' hw0'
      norm_num [div_eq_mul_inv] at hv0' hw0' ⊢
      linarith
    exact_mod_cast hr
  have h0hi : (w 0 - v 0) + 2 * (w 1 - v 1) ≤ (2 : ℤ) := by
    have hr : (((w 0 - v 0) + 2 * (w 1 - v 1) : ℤ) : ℝ) ≤ 2 := by
      simp only [constructedA2CorrectedPlaneCenter] at hv0' hw0'
      norm_num [div_eq_mul_inv] at hv0' hw0' ⊢
      linarith
    exact_mod_cast hr
  have h1lo : (-2 : ℤ) ≤ -(w 0 - v 0) + (w 1 - v 1) := by
    have hr : (-2 : ℝ) ≤ ((-(w 0 - v 0) + (w 1 - v 1) : ℤ) : ℝ) := by
      simp only [constructedA2CorrectedPlaneCenter] at hv1' hw1'
      norm_num [div_eq_mul_inv] at hv1' hw1' ⊢
      linarith
    exact_mod_cast hr
  have h1hi : -(w 0 - v 0) + (w 1 - v 1) ≤ (2 : ℤ) := by
    have hr : (((-(w 0 - v 0) + (w 1 - v 1) : ℤ) : ℝ)) ≤ 2 := by
      simp only [constructedA2CorrectedPlaneCenter] at hv1' hw1'
      norm_num [div_eq_mul_inv] at hv1' hw1' ⊢
      linarith
    exact_mod_cast hr
  have hdlo : (-2 : ℤ) ≤ 2 * (w 0 - v 0) + (w 1 - v 1) := by
    have hr : (-2 : ℝ) ≤ ((2 * (w 0 - v 0) + (w 1 - v 1) : ℤ) : ℝ) := by
      simp only [constructedA2CorrectedPlaneCenter] at hvd' hwd'
      norm_num [div_eq_mul_inv] at hvd' hwd' ⊢
      linarith
    exact_mod_cast hr
  have hdhi : 2 * (w 0 - v 0) + (w 1 - v 1) ≤ (2 : ℤ) := by
    have hr : (((2 * (w 0 - v 0) + (w 1 - v 1) : ℤ) : ℝ)) ≤ 2 := by
      simp only [constructedA2CorrectedPlaneCenter] at hvd' hwd'
      norm_num [div_eq_mul_inv] at hvd' hwd' ⊢
      linarith
    exact_mod_cast hr
  have hdifference : w - v = ![w 0 - v 0, w 1 - v 1] := by
    ext k
    fin_cases k <;> simp
  rw [hdifference]
  simp [e₁, e₂]
  omega

public theorem constructedA2CorrectedPlaneTile_eq_displacement
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CorrectedPlaneTile v i p =
      constructedA2CorrectedPlaneTile w j q) :
    w - v ∈ ({0, e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂} :
      Set ToricLattice) := by
  apply constructedA2CorrectedPlaneCell_inter_nonempty_displacement v w
  exact ⟨constructedA2CorrectedPlaneTile v i p,
    constructedA2CorrectedPlaneTile_mem v i p, h ▸ constructedA2CorrectedPlaneTile_mem w j q⟩

public theorem constructedA2LaurentRelation_chartIncidence
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    w ∈ Set.range
        (a2Triangle (constructedA2CellChart v i).1 (constructedA2CellChart v i).2) ∧
      v ∈ Set.range
        (a2Triangle (constructedA2CellChart w j).1 (constructedA2CellChart w j).2) := by
  have heq : constructedA2CellSquareCarrierPoint v i p =
      constructedA2CellSquareCarrierPoint w j q := by
    apply (inclusion_eq_iff _ _ _ _).mpr
    rw [chartChange_source]
    exact h
  constructor
  · by_contra hw
    have hd := otherCarrierCentralComponent_disjoint_chart
      (constructedA2CellChart v i) w hw
    rw [Set.disjoint_left] at hd
    apply hd (constructedA2CellSquareCarrierPoint_mem_component w j q)
    rw [← heq]
    rw [toricChart_source]
    exact ⟨constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)), rfl⟩
  · by_contra hv
    have hd := otherCarrierCentralComponent_disjoint_chart
      (constructedA2CellChart w j) v hv
    rw [Set.disjoint_left] at hd
    apply hd (constructedA2CellSquareCarrierPoint_mem_component v i p)
    rw [heq]
    rw [toricChart_source]
    exact ⟨constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)), rfl⟩

public theorem constructedA2LaurentRelation_displacement
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare)
    (h : constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ))) :
    w - v ∈ ({0, e₁, e₂, e₂ - e₁, -e₁, -e₂, e₁ - e₂} :
      Set ToricLattice) := by
  obtain ⟨⟨k, hk⟩, -⟩ := constructedA2LaurentRelation_chartIncidence v w i j p q h
  fin_cases i <;> fin_cases k <;>
    simp [constructedA2CellChart, a2Triangle, sub_eq_add_neg] at hk <;>
    subst w <;>
    abel_nf <;>
    simp

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
