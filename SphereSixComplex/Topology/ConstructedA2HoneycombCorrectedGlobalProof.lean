module

public import SphereSixComplex.Topology.ConstructedA2HoneycombPositiveNeighborProof

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2CorrectedLaurentIdentity_sameCell
    (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p = constructedA2CorrectedPlaneTile v j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j)) ∧
        monomial (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart v j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  have hsame (k : Fin 6) (a b : ConstructedA2CellSquare) :=
    constructedA2CorrectedLaurentIdentity_of_sameCell v k k a b
      (constructedA2HoneycombLaurentFiniteIdentity_sameChart v k a b)
  have hnext (k : Fin 6) (a b : ConstructedA2CellSquare) :=
    constructedA2CorrectedLaurentIdentity_of_sameCell v k (constructedA2CellNextIndex k) a b
      (constructedA2HoneycombLaurentFiniteIdentity_nextChart v k a b)
  have hj :
      j = i ∨
      j = constructedA2CellNextIndex i ∨
      j = constructedA2CellNextIndex (constructedA2CellNextIndex i) ∨
      j = constructedA2CellNextIndex
        (constructedA2CellNextIndex (constructedA2CellNextIndex i)) ∨
      j = constructedA2CellNextIndex
        (constructedA2CellNextIndex
          (constructedA2CellNextIndex (constructedA2CellNextIndex i))) ∨
      j = constructedA2CellNextIndex
        (constructedA2CellNextIndex
          (constructedA2CellNextIndex
            (constructedA2CellNextIndex (constructedA2CellNextIndex i)))) := by
    fin_cases i <;> fin_cases j <;> simp [constructedA2CellNextIndex]
  rcases hj with h | h | h | h | h | h
  · subst j
    exact hsame i p q
  · subst j
    exact hnext i p q
  · subst j
    exact constructedA2CorrectedLaurentIdentity_secondNext v i p q
  · subst j
    exact constructedA2CorrectedLaurentIdentity_thirdNext v i p q
  · subst j
    let k := constructedA2CellNextIndex
      (constructedA2CellNextIndex
        (constructedA2CellNextIndex (constructedA2CellNextIndex i)))
    have hr := constructedA2CorrectedLaurentIdentity_reverse v v k
      (constructedA2CellNextIndex (constructedA2CellNextIndex k)) q p
      (constructedA2CorrectedLaurentIdentity_secondNext v k q p)
    fin_cases i <;> simpa [k, constructedA2CellNextIndex] using hr
  · subst j
    let k := constructedA2CellNextIndex
      (constructedA2CellNextIndex
        (constructedA2CellNextIndex
          (constructedA2CellNextIndex (constructedA2CellNextIndex i))))
    have hr := constructedA2CorrectedLaurentIdentity_reverse v v k
      (constructedA2CellNextIndex k) q p (hnext k q p)
    fin_cases i <;> simpa [k, constructedA2CellNextIndex] using hr

public theorem constructedA2CorrectedLaurentIdentity_negativeNeighbor
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile
        (v + constructedA2PositiveNeighborDisplacement r) i p =
        constructedA2CorrectedPlaneTile v j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix
              (constructedA2CellChart
                (v + constructedA2PositiveNeighborDisplacement r) i)
              (constructedA2CellChart v j)) ∧
        monomial
            (transitionMatrix
              (constructedA2CellChart
                (v + constructedA2PositiveNeighborDisplacement r) i)
              (constructedA2CellChart v j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) :=
  constructedA2CorrectedLaurentIdentity_reverse v
    (v + constructedA2PositiveNeighborDisplacement r) j i q p
    (constructedA2CorrectedLaurentIdentity_positiveNeighbor r v j i q p)

public theorem constructedA2CorrectedLaurentIdentity_global
    (v w : ToricLattice) (i j : Fin 6) (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p = constructedA2CorrectedPlaneTile w j q ↔
      constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j)) ∧
        monomial (transitionMatrix (constructedA2CellChart v i) (constructedA2CellChart w j))
            (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          constructedA2CellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  constructor
  · intro h
    have hd := constructedA2CorrectedPlaneTile_eq_displacement v w i j p q h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have hw : w = v := by
        calc
          w = (w - v) + v := by abel
          _ = v := by rw [hd]; simp
      subst w
      exact (constructedA2CorrectedLaurentIdentity_sameCell v i j p q).mp h
    · have hw : w = v + e₁ := by
        calc
          w = (w - v) + v := by abel
          _ = e₁ + v := by rw [hd]
          _ = v + e₁ := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 0 v i j p q).mp h
    · have hw : w = v + e₂ := by
        calc
          w = (w - v) + v := by abel
          _ = e₂ + v := by rw [hd]
          _ = v + e₂ := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 1 v i j p q).mp h
    · have hw : w = v + (e₂ - e₁) := by
        calc
          w = (w - v) + v := by abel
          _ = (e₂ - e₁) + v := by rw [hd]
          _ = v + (e₂ - e₁) := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 2 v i j p q).mp h
    · have hv : v = w + e₁ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₁) := by rw [hd]
          _ = w + e₁ := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 0 w i j p q).mp h
    · have hv : v = w + e₂ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₂) := by rw [hd]
          _ = w + e₂ := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 1 w i j p q).mp h
    · have hv : v = w + (e₂ - e₁) := by
        calc
          v = w - (w - v) := by abel
          _ = w - (e₁ - e₂) := by rw [hd]
          _ = w + (e₂ - e₁) := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 2 w i j p q).mp h
  · intro h
    have hd := constructedA2LaurentRelation_displacement v w i j p q h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have hw : w = v := by
        calc
          w = (w - v) + v := by abel
          _ = v := by rw [hd]; simp
      subst w
      exact (constructedA2CorrectedLaurentIdentity_sameCell v i j p q).mpr h
    · have hw : w = v + e₁ := by
        calc
          w = (w - v) + v := by abel
          _ = e₁ + v := by rw [hd]
          _ = v + e₁ := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 0 v i j p q).mpr h
    · have hw : w = v + e₂ := by
        calc
          w = (w - v) + v := by abel
          _ = e₂ + v := by rw [hd]
          _ = v + e₂ := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 1 v i j p q).mpr h
    · have hw : w = v + (e₂ - e₁) := by
        calc
          w = (w - v) + v := by abel
          _ = (e₂ - e₁) + v := by rw [hd]
          _ = v + (e₂ - e₁) := add_comm _ _
      rw [hw] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_positiveNeighbor 2 v i j p q).mpr h
    · have hv : v = w + e₁ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₁) := by rw [hd]
          _ = w + e₁ := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 0 w i j p q).mpr h
    · have hv : v = w + e₂ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₂) := by rw [hd]
          _ = w + e₂ := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 1 w i j p q).mpr h
    · have hv : v = w + (e₂ - e₁) := by
        calc
          v = w - (w - v) := by abel
          _ = w - (e₁ - e₂) := by rw [hd]
          _ = w + (e₂ - e₁) := by abel
      rw [hv] at h ⊢
      exact (constructedA2CorrectedLaurentIdentity_negativeNeighbor 2 w i j p q).mpr h

public theorem constructedA2CorrectedPlaneTile_eq_iff_cellSquareProjection
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneTile v i p = constructedA2CorrectedPlaneTile w j q ↔
      ((constructedA2CellSquareProjection hr v (i, p) :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        constructedA2CellSquareProjection hr w (j, q) :=
  (constructedA2CorrectedLaurentIdentity_global v w i j p q).trans
    (constructedA2CellSquareProjection_eq_iff_monomial hr v w i j p q).symm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
