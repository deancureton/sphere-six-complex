module

public import SphereSixComplex.Paper.Topology.CuspToricCellularHomologyBridge
public import SphereSixComplex.Paper.Topology.CuspDeckHomologyOne

/-!
# Integral homology of the cusp filling

The standard periodic `A₂` toric CW decomposition has one nonzero cellular boundary: its three
oriented edges all run between the two vertices.  Combining that established attaching-incidence
calculation with the cellular-to-singular comparison computes the homology of the actual quotient
central fibre.  The constructed strong deformation retraction then transports the calculation to
the actual cusp filling.

No specialization map from a nearby regular fibre is computed here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

private theorem standardA2ToricCellularBoundary_eq (n : ℕ)
    (x : CuspWCellIndex n.succ → ℤ) :
    standardA2ToricCellularBoundary n x = cuspToricCellularBoundary n x := by
  rcases n with _ | n
  · change standardA2ToricCellularBoundaryOne x = cuspToricCellularBoundaryOne x
    funext i
    fin_cases i <;>
      simp [standardA2ToricCellularBoundaryOne, cuspToricCellularBoundaryOne]
  · rfl

/-- For the standard periodic `A₂` toric decomposition, the cellular attaching maps have the
incidence formula encoded by `cuspToricCellularBoundary`: the three oriented one-cells run from
the first vertex to the second, and every higher cellular boundary is zero. -/
public theorem establishedStandardA2ToricCentralFiberCellularIncidence
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
    C.CellularIncidenceData := by
  let T := establishedStandardA2ToricCentralFiberCellularRealization W R
  change T.decomposition.CellularIncidenceData
  let C := T.decomposition
  let _ := C.topology
  let _ := C.cwComplex
  constructor
  intro n x
  change C.establishedIntegralCellularChainModel.chainComplex.d n.succ n
      (labelledA2CellBasis C.cellEquiv C.establishedIntegralCellularChainModel n.succ x) =
    labelledA2CellBasis C.cellEquiv C.establishedIntegralCellularChainModel n
      (cuspToricCellularBoundary n x)
  rw [← standardA2ToricCellularBoundary_eq]
  change C.integralCellularChainModel.chainComplex.d n.succ n
      (C.labelledCellBasis n.succ x) =
    C.labelledCellBasis n (standardA2ToricCellularBoundary n x)
  exact T.boundary_eq n x


/-- The actual quotient cusp central fibre has second integral homology `ℤ⁴`. -/
public noncomputable def actualCuspCentralFiberHomologyTwoEquiv
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (R.quotientCentralFiber W) ≃+ (Fin 4 → ℤ) := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 C.homotopyEquiv).trans
    (C.carrierIntegralSingularHomologyTwoEquiv
      (establishedStandardA2ToricCentralFiberCellularIncidence W R))




public noncomputable def actualLocalCuspFillingHomologyOneEquiv
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (_R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 1 (ActualLocalCuspFilling W) ≃+ (Fin 2 → ℤ) :=
  actualCuspDeckHomologyOneEquiv W


/-- The actual local cusp filling has second integral homology `ℤ⁴`. -/
public noncomputable def actualLocalCuspFillingHomologyTwoEquiv
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (ActualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) :=
  (R.specializationHomologyEquiv W 2).trans (actualCuspCentralFiberHomologyTwoEquiv W R)



end Geometry.CuspPuncturedCollarBridge

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The cusp filling selected in the paper's four-piece star has first integral homology `ℤ²`. -/
public noncomputable def cuspFillingHomologyOneEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 2 → ℤ) := by
  change IntegralSingularHomology 1 (ActualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness R

/-- The cusp filling selected in the paper's four-piece star has second integral homology
`ℤ⁴`. -/
public noncomputable def cuspFillingHomologyTwoEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 4 → ℤ) := by
  change IntegralSingularHomology 2 (ActualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness R



end Geometry.PaperAnalyticData

end SphereSixComplex
