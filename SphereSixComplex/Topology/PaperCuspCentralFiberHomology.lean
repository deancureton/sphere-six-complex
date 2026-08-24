module

public import SphereSixComplex.Topology.CuspToricCellularHomologyBridge

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
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

/-- For the standard periodic `A₂` toric decomposition, the cellular attaching maps have the
incidence formula encoded by `cuspToricCellularBoundary`: the three oriented one-cells run from
the first vertex to the second, and every higher cellular boundary is zero. -/
public axiom establishedStandardA2ToricCentralFiberCellularIncidence
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
    C.CellularIncidenceData

/-- The actual quotient cusp central fibre has first integral homology `ℤ²`. -/
public noncomputable def actualCuspCentralFiberHomologyOneEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 1 (R.quotientCentralFiber W) ≃+ (Fin 2 → ℤ) := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1 C.homotopyEquiv).trans
    (C.carrierIntegralSingularHomologyOneEquiv
      (establishedStandardA2ToricCentralFiberCellularIncidence W R))

/-- The actual quotient cusp central fibre has second integral homology `ℤ⁴`. -/
public noncomputable def actualCuspCentralFiberHomologyTwoEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (R.quotientCentralFiber W) ≃+ (Fin 4 → ℤ) := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 C.homotopyEquiv).trans
    (C.carrierIntegralSingularHomologyTwoEquiv
      (establishedStandardA2ToricCentralFiberCellularIncidence W R))

/-- The actual quotient cusp central fibre has third integral homology `ℤ²`. -/
public noncomputable def actualCuspCentralFiberHomologyThreeEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 3 (R.quotientCentralFiber W) ≃+ (Fin 2 → ℤ) := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 3 C.homotopyEquiv).trans
    (C.carrierIntegralSingularHomologyThreeEquiv
      (establishedStandardA2ToricCentralFiberCellularIncidence W R))

/-- The actual quotient cusp central fibre has fourth integral homology `ℤ`. -/
public noncomputable def actualCuspCentralFiberHomologyFourEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 4 (R.quotientCentralFiber W) ≃+ ℤ := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 4 C.homotopyEquiv).trans
    (C.carrierIntegralSingularHomologyFourEquiv
      (establishedStandardA2ToricCentralFiberCellularIncidence W R))

/-- The actual local cusp filling has first integral homology `ℤ²`. -/
public noncomputable def actualLocalCuspFillingHomologyOneEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃+ (Fin 2 → ℤ) :=
  (R.specializationHomologyEquiv W 1).trans (actualCuspCentralFiberHomologyOneEquiv W R)

/-- The actual local cusp filling has second integral homology `ℤ⁴`. -/
public noncomputable def actualLocalCuspFillingHomologyTwoEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) :=
  (R.specializationHomologyEquiv W 2).trans (actualCuspCentralFiberHomologyTwoEquiv W R)

/-- The actual local cusp filling has third integral homology `ℤ²`. -/
public noncomputable def actualLocalCuspFillingHomologyThreeEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 3 (actualLocalCuspFilling W) ≃+ (Fin 2 → ℤ) :=
  (R.specializationHomologyEquiv W 3).trans (actualCuspCentralFiberHomologyThreeEquiv W R)

/-- The actual local cusp filling has fourth integral homology `ℤ`. -/
public noncomputable def actualLocalCuspFillingHomologyFourEquiv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 4 (actualLocalCuspFilling W) ≃+ ℤ :=
  (R.specializationHomologyEquiv W 4).trans (actualCuspCentralFiberHomologyFourEquiv W R)

end Geometry.CuspPuncturedCollarBridge

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The cusp filling selected in the paper's four-piece star has first integral homology `ℤ²`. -/
public noncomputable def cuspFillingHomologyOneEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 2 → ℤ) := by
  change IntegralSingularHomology 1 (actualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness R

/-- The cusp filling selected in the paper's four-piece star has second integral homology
`ℤ⁴`. -/
public noncomputable def cuspFillingHomologyTwoEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 4 → ℤ) := by
  change IntegralSingularHomology 2 (actualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness R

/-- The cusp filling selected in the paper's four-piece star has third integral homology `ℤ²`. -/
public noncomputable def cuspFillingHomologyThreeEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 3 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 2 → ℤ) := by
  change IntegralSingularHomology 3 (actualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyThreeEquiv A.starCuspWitness R

/-- The cusp filling selected in the paper's four-piece star has fourth integral homology `ℤ`. -/
public noncomputable def cuspFillingHomologyFourEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 4 (A.openEmbeddingStarData.filling 0) ≃+ ℤ := by
  change IntegralSingularHomology 4 (actualLocalCuspFilling A.starCuspWitness) ≃+ ℤ
  exact actualLocalCuspFillingHomologyFourEquiv A.starCuspWitness R

end Geometry.PaperAnalyticData

end SphereSixComplex
