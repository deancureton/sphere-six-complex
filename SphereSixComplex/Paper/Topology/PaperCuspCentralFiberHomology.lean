module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberHomologyCoordinates
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence
public import SphereSixComplex.Paper.Topology.CuspDeckHomologyOne

/-! # Integral homology of the cusp filling

The radial cover of the central fiber computes its homology by Mayer–Vietoris.
The cusp retraction transports these groups to the filling.
-/

@[expose] public section
noncomputable section

namespace SphereSixComplex
namespace Geometry.CuspCollar

open SphereSixComplex.Periods
open CuspPeriodExpansion InfiniteA2Toric

public def actualCuspCentralFiberHomologyTwoEquiv
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (R.quotientCentralFiber W) ≃+ (Fin 4 → ℤ) := by
  let W₀ := Classical.choice
    (QuantitativeRegions.BoundedPolydiscRegions.exists_actualLocalCuspQuotientWitness
      N Construction.constructedModel)
  let W₁ := Classical.choice (exists_actualPuncturedCuspCollarWitness W₀)
  exact (integralSingularHomologyEquiv 2
    ((actualLocalCuspCentralOrbitCoreHomeomorph W R).symm.trans
      (centralOrbitModelHomeomorph W₁ W).symm)).trans
        (Construction.CentralFiberHomology.homologyTwoEquiv W₁)

/-- The actual local cusp filling has second integral homology `ℤ⁴`. -/
public noncomputable def actualLocalCuspFillingHomologyTwoEquiv
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IntegralSingularHomology 2 (ActualLocalCuspFilling W) ≃+ (Fin 4 → ℤ) :=
  (R.specializationHomologyEquiv W 2).trans (actualCuspCentralFiberHomologyTwoEquiv W R)



end Geometry.CuspCollar

namespace Geometry.AnalyticData

open CuspCollar

variable (A : AnalyticData)

/-- The cusp filling selected in the paper's four-piece star has first integral homology `ℤ²`. -/
public noncomputable def cuspFillingHomologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 2 → ℤ) := by
  change IntegralSingularHomology 1 (ActualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualCuspDeckHomologyOneEquiv A.starCuspWitness

/-- The cusp filling selected in the paper's four-piece star has second integral homology
`ℤ⁴`. -/
public noncomputable def cuspFillingHomologyTwoEquiv
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) ≃+ (Fin 4 → ℤ) := by
  change IntegralSingularHomology 2 (ActualLocalCuspFilling A.starCuspWitness) ≃+ _
  exact actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness R



end Geometry.AnalyticData

end SphereSixComplex
