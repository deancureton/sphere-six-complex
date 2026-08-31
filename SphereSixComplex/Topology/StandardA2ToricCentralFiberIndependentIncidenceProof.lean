module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberZeroCells
public import SphereSixComplex.Topology.StandardA2ToricCentralFiberOneCells
public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicSymmetry
public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicQuotientSymmetry
public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicCorrectionMatrixAudit
public import SphereSixComplex.Topology.PaperCuspCentralFiberCWModel

/-!
# Independent incidence values for the standard `A₂` central fibre

This file evaluates the prescribed side of all twenty-four independent incidence equations.
It isolates the exact remaining compatibility required between the characteristic-map CW atlas
and the cellular chain model selected by the classical cellular-homology theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex

/-- The twenty-four independent cellular-boundary entries, with their prescribed values
evaluated explicitly. -/
public structure StandardA2ToricCentralFiberIndependentIncidenceValues
    {X : Type} [TopologicalSpace X] [T2Space X]
    (A : StandardA2ToricCentralFiberCellAtlas X) : Prop where
  boundaryZeroNeg :
    let D := A.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ j : Fin 3,
      standardA2ToricCellularCoordinateBoundary D 0
          (Pi.single j 1 : Fin 3 → ℤ) (0 : Fin 2) = -1
  boundaryZeroPos :
    let D := A.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ j : Fin 3,
      standardA2ToricCellularCoordinateBoundary D 0
          (Pi.single j 1 : Fin 3 → ℤ) (1 : Fin 2) = 1
  boundaryOneIndependent :
    let D := A.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 4) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 1
          (Pi.single j 1 : Fin 4 → ℤ) i.castSucc = 0
  boundaryTwo :
    let D := A.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 2) (i : Fin 4),
      standardA2ToricCellularCoordinateBoundary D 2
          (Pi.single j 1 : Fin 2 → ℤ) i = 0
  boundaryThree :
    let D := A.toCWDecomposition
    let _ := D.topology
    let _ := D.cwComplex
    ∀ (j : Fin 1) (i : Fin 2),
      standardA2ToricCellularCoordinateBoundary D 3
          (Pi.single j 1 : Fin 1 → ℤ) i = 0

namespace StandardA2ToricCentralFiberIndependentIncidenceValues

variable {X : Type} [TopologicalSpace X] [T2Space X]
  {A : StandardA2ToricCentralFiberCellAtlas X}

/-- Explicit evaluation of the twenty-four prescribed entries turns the numeric interface into
the original independent-incidence residual without changing its target. -/
public theorem toResidual
    (V : StandardA2ToricCentralFiberIndependentIncidenceValues A) :
    StandardA2ToricCentralFiberIndependentIncidenceResidual A where
  boundaryZero := by
    dsimp only
    intro j i
    fin_cases i
    · have h := V.boundaryZeroNeg j
      fin_cases j <;>
        exact h.trans (by rfl)
    · have h := V.boundaryZeroPos j
      fin_cases j <;>
        exact h.trans (by rfl)
  boundaryOneIndependent := by
    dsimp only
    intro j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 1
      (Pi.single j 1 : Fin 4 → ℤ) i.castSucc = 0
    exact V.boundaryOneIndependent j i
  boundaryTwo := by
    dsimp only
    intro j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 2
      (Pi.single j 1 : Fin 2 → ℤ) i = 0
    exact V.boundaryTwo j i
  boundaryThree := by
    dsimp only
    intro j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 3
      (Pi.single j 1 : Fin 1 → ℤ) i = 0
    exact V.boundaryThree j i

/-- Conversely, the residual supplies exactly the explicit twenty-four numeric entries. -/
public theorem ofResidual
    (T : StandardA2ToricCentralFiberIndependentIncidenceResidual A) :
    StandardA2ToricCentralFiberIndependentIncidenceValues A where
  boundaryZeroNeg := by
    dsimp only
    intro j
    have h := T.boundaryZero j 0
    fin_cases j <;>
      exact h.trans (by rfl)
  boundaryZeroPos := by
    dsimp only
    intro j
    have h := T.boundaryZero j 1
    fin_cases j <;>
      exact h.trans (by rfl)
  boundaryOneIndependent := by
    dsimp only
    intro j i
    have h := T.boundaryOneIndependent j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 1
      (Pi.single j 1 : Fin 4 → ℤ) i.castSucc = 0 at h
    exact h
  boundaryTwo := by
    dsimp only
    intro j i
    have h := T.boundaryTwo j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 2
      (Pi.single j 1 : Fin 2 → ℤ) i = 0 at h
    exact h
  boundaryThree := by
    dsimp only
    intro j i
    have h := T.boundaryThree j i
    change standardA2ToricCellularCoordinateBoundary A.toCWDecomposition 3
      (Pi.single j 1 : Fin 1 → ℤ) i = 0 at h
    exact h

public theorem residual_iff_values :
    Nonempty (StandardA2ToricCentralFiberIndependentIncidenceResidual A) ↔
      Nonempty (StandardA2ToricCentralFiberIndependentIncidenceValues A) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨ofResidual T⟩
  · rintro ⟨V⟩
    exact ⟨V.toResidual⟩

end StandardA2ToricCentralFiberIndependentIncidenceValues

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The exact replacement interface for the established incidence residual: it is enough to
prove the explicitly evaluated twenty-four entries for the transported atlas. -/
public theorem establishedStandardA2ToricCentralFiberIndependentIncidenceResidual_of_values
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (V :
      let _ : T2Space (actualLocalCuspFilling W) :=
        SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
      let _ : T2Space (R.quotientCentralFiber W) := inferInstance
      StandardA2ToricCentralFiberIndependentIncidenceValues
        (establishedStandardA2ToricCentralFiberCellAtlas W R)) :
    let _ : T2Space (actualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberIndependentIncidenceResidual
      (establishedStandardA2ToricCentralFiberCellAtlas W R) := by
  let _ : T2Space (actualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  exact V.toResidual

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
