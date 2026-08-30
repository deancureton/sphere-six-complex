module

public import SphereSixComplex.Topology.IntegralHomologyEuler

/-!
# Cell-count reduction for finite-cover Euler multiplicativity

This file isolates the formal algebra at the end of the finite-cover Euler argument.  The
topological work is exactly the construction of compatible finite CW structures on the base and
cover, the two Euler--Poincare identities, and the degree-wise count of lifted cells.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

/-- The alternating sum of cell counts through dimension six. -/
public def alternatingCellCountSix (cells : Fin 7 → ℕ) : ℤ :=
  (cells 0 : ℤ) - cells 1 + cells 2 - cells 3 + cells 4 - cells 5 + cells 6

/-- Euler multiplicativity follows formally once every base cell has exactly `degree` lifts.

The two Euler--Poincare equalities and the lifted-cell count are kept as explicit hypotheses, so
this theorem has no dependence on a cellular-homology comparison or a covering-space theorem. -/
public theorem integralHomologyEulerCharacteristicSix_eq_mul_of_cellCounts
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (degree : ℕ) (coverCells baseCells : Fin 7 → ℕ)
    (coverEulerPoincare :
      integralHomologyEulerCharacteristicSix E = alternatingCellCountSix coverCells)
    (baseEulerPoincare :
      integralHomologyEulerCharacteristicSix X = alternatingCellCountSix baseCells)
    (liftedCellCount : ∀ n, coverCells n = degree * baseCells n) :
    integralHomologyEulerCharacteristicSix E =
      (degree : ℤ) * integralHomologyEulerCharacteristicSix X := by
  rw [coverEulerPoincare, baseEulerPoincare]
  simp only [alternatingCellCountSix, liftedCellCount, Nat.cast_mul]
  ring

end SphereSixComplex

end

end
