module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombPositiveNeighbor

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
namespace Construction


public theorem correctedLaurentIdentity_sameCell
    (v : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p = correctedPlaneTile v j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart v j)) ∧
        monomial (transitionMatrix (cellChart v i) (cellChart v j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  have hsame (k : Fin 6) (a b : CellSquare) :=
    correctedLaurentIdentity_of_sameCell v k k a b
      (honeycombLaurentFiniteIdentity_sameChart v k a b)
  have hnext (k : Fin 6) (a b : CellSquare) :=
    correctedLaurentIdentity_of_sameCell v k (cellNextIndex k) a b
      (honeycombLaurentFiniteIdentity_nextChart v k a b)
  have hj :
      j = i ∨
      j = cellNextIndex i ∨
      j = cellNextIndex (cellNextIndex i) ∨
      j = cellNextIndex
        (cellNextIndex (cellNextIndex i)) ∨
      j = cellNextIndex
        (cellNextIndex
          (cellNextIndex (cellNextIndex i))) ∨
      j = cellNextIndex
        (cellNextIndex
          (cellNextIndex
            (cellNextIndex (cellNextIndex i)))) := by
    fin_cases i <;> fin_cases j <;> simp [cellNextIndex]
  rcases hj with h | h | h | h | h | h
  · subst j
    exact hsame i p q
  · subst j
    exact hnext i p q
  · subst j
    exact correctedLaurentIdentity_secondNext v i p q
  · subst j
    exact correctedLaurentIdentity_thirdNext v i p q
  · subst j
    let k := cellNextIndex
      (cellNextIndex
        (cellNextIndex (cellNextIndex i)))
    have hr := correctedLaurentIdentity_reverse v v k
      (cellNextIndex (cellNextIndex k)) q p
      (correctedLaurentIdentity_secondNext v k q p)
    fin_cases i <;> simpa [k, cellNextIndex] using hr
  · subst j
    let k := cellNextIndex
      (cellNextIndex
        (cellNextIndex
          (cellNextIndex (cellNextIndex i))))
    have hr := correctedLaurentIdentity_reverse v v k
      (cellNextIndex k) q p (hnext k q p)
    fin_cases i <;> simpa [k, cellNextIndex] using hr

public theorem correctedLaurentIdentity_negativeNeighbor
    (r : Fin 3) (v : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    correctedPlaneTile
        (v + positiveNeighborDisplacement r) i p =
        correctedPlaneTile v j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix
              (cellChart
                (v + positiveNeighborDisplacement r) i)
              (cellChart v j)) ∧
        monomial
            (transitionMatrix
              (cellChart
                (v + positiveNeighborDisplacement r) i)
              (cellChart v j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) :=
  correctedLaurentIdentity_reverse v
    (v + positiveNeighborDisplacement r) j i q p
    (correctedLaurentIdentity_positiveNeighbor r v j i q p)

public theorem correctedPlaneTile_eq_iff_monomial
    (v w : ToricLattice) (i j : Fin 6) (p q : CellSquare) :
    correctedPlaneTile v i p = correctedPlaneTile w j q ↔
      cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)) ∈
          monomialDomain
            (transitionMatrix (cellChart v i) (cellChart w j)) ∧
        monomial (transitionMatrix (cellChart v i) (cellChart w j))
            (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
          cellLiftCoordinates j (fun k ↦ (q.1 k : ℂ)) := by
  constructor
  · intro h
    have hd := correctedPlaneTile_eq_displacement v w i j p q h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have hw : w = v := by
        calc
          w = (w - v) + v := by abel
          _ = v := by rw [hd]; simp
      subst w
      exact (correctedLaurentIdentity_sameCell v i j p q).mp h
    · have hw : w = v + e₁ := by
        calc
          w = (w - v) + v := by abel
          _ = e₁ + v := by rw [hd]
          _ = v + e₁ := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 0 v i j p q).mp h
    · have hw : w = v + e₂ := by
        calc
          w = (w - v) + v := by abel
          _ = e₂ + v := by rw [hd]
          _ = v + e₂ := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 1 v i j p q).mp h
    · have hw : w = v + (e₂ - e₁) := by
        calc
          w = (w - v) + v := by abel
          _ = (e₂ - e₁) + v := by rw [hd]
          _ = v + (e₂ - e₁) := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 2 v i j p q).mp h
    · have hv : v = w + e₁ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₁) := by rw [hd]
          _ = w + e₁ := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 0 w i j p q).mp h
    · have hv : v = w + e₂ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₂) := by rw [hd]
          _ = w + e₂ := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 1 w i j p q).mp h
    · have hv : v = w + (e₂ - e₁) := by
        calc
          v = w - (w - v) := by abel
          _ = w - (e₁ - e₂) := by rw [hd]
          _ = w + (e₂ - e₁) := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 2 w i j p q).mp h
  · intro h
    have hd := laurentRelation_displacement v w i j p q h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · have hw : w = v := by
        calc
          w = (w - v) + v := by abel
          _ = v := by rw [hd]; simp
      subst w
      exact (correctedLaurentIdentity_sameCell v i j p q).mpr h
    · have hw : w = v + e₁ := by
        calc
          w = (w - v) + v := by abel
          _ = e₁ + v := by rw [hd]
          _ = v + e₁ := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 0 v i j p q).mpr h
    · have hw : w = v + e₂ := by
        calc
          w = (w - v) + v := by abel
          _ = e₂ + v := by rw [hd]
          _ = v + e₂ := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 1 v i j p q).mpr h
    · have hw : w = v + (e₂ - e₁) := by
        calc
          w = (w - v) + v := by abel
          _ = (e₂ - e₁) + v := by rw [hd]
          _ = v + (e₂ - e₁) := add_comm _ _
      rw [hw] at h ⊢
      exact (correctedLaurentIdentity_positiveNeighbor 2 v i j p q).mpr h
    · have hv : v = w + e₁ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₁) := by rw [hd]
          _ = w + e₁ := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 0 w i j p q).mpr h
    · have hv : v = w + e₂ := by
        calc
          v = w - (w - v) := by abel
          _ = w - (-e₂) := by rw [hd]
          _ = w + e₂ := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 1 w i j p q).mpr h
    · have hv : v = w + (e₂ - e₁) := by
        calc
          v = w - (w - v) := by abel
          _ = w - (e₁ - e₂) := by rw [hd]
          _ = w + (e₂ - e₁) := by abel
      rw [hv] at h ⊢
      exact (correctedLaurentIdentity_negativeNeighbor 2 w i j p q).mpr h

public theorem correctedPlaneTile_eq_iff_cellSquareProjection
    {r : ℝ} (hr : 0 < r) (v w : ToricLattice) (i j : Fin 6)
    (p q : CellSquare) :
    correctedPlaneTile v i p = correctedPlaneTile w j q ↔
      ((cellSquareProjection hr v (i, p) :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        cellSquareProjection hr w (j, q) :=
  (correctedPlaneTile_eq_iff_monomial v w i j p q).trans
    (cellSquareProjection_eq_iff_monomial hr v w i j p q).symm

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
