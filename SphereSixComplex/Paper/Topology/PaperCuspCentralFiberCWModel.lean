module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence
public import SphereSixComplex.Paper.Topology.ConstructedA2HigherIncidenceProof
public import SphereSixComplex.Paper.Topology.ConstructedA2DegreeTwoIncidence
public import SphereSixComplex.Paper.Topology.ToricCellAtlasIncidenceTransport

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap
namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric

/-- Transport the explicit characteristic maps from the constructed toric model. -/
public noncomputable def establishedStandardA2ToricCentralOrbitCellAtlas
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    StandardA2ToricCentralFiberCellAtlas (ActualLocalCuspCentralOrbitQuotient W) := by
  let W₀ := Classical.choice
    (SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions.BoundedPolydiscRegions.exists_actualLocalCuspQuotientWitness
      N Construction.constructedModel)
  let W₁ := Classical.choice (exists_actualPuncturedCuspCollarWitness W₀)
  exact (constructedCentralCellAtlas W₁).transport (centralOrbitModelHomeomorph W₁ W)

/-- Transport the orbit-quotient atlas to the radial retraction's concrete central-fibre
subspace. -/
public noncomputable def establishedStandardA2ToricCentralFiberCellAtlas
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberCellAtlas (R.quotientCentralFiber W) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (establishedStandardA2ToricCentralOrbitCellAtlas W).transport
    (actualLocalCuspCentralOrbitCoreHomeomorph W R)

/-- The ten remaining higher-dimensional cellular-incidence entries. -/
public theorem establishedStandardA2ToricCentralFiberHigherIncidenceResidual
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberHigherIncidenceResidual
      (establishedStandardA2ToricCentralFiberCellAtlas W R) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  let W₀ := Classical.choice
    (SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions.BoundedPolydiscRegions.exists_actualLocalCuspQuotientWitness
      N Construction.constructedModel)
  let W₁ := Classical.choice (exists_actualPuncturedCuspCollarWitness W₀)
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let _ : T2Space (ActualLocalCuspFilling W₁) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W₁
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W₁) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W₁).t2Space
  let C := constructedCentralCellAtlas W₁
  let e₁ := centralOrbitModelHomeomorph W₁ W
  let e₂ := actualLocalCuspCentralOrbitCoreHomeomorph W R
  constructor
  · dsimp only
    intro j i
    let : DecidableEq (CuspWCellIndex 3) := inferInstanceAs (DecidableEq (Fin 2))
    change standardA2ToricCellularCoordinateBoundary ((C.transport e₁).transport e₂).toCWDecomposition
      2 (Pi.single j 1 : Fin 2 → ℤ) i = 0
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 2 j i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 2 j i).symm.trans ?_
    exact (C.coordinateBoundary_single_eq_attachingDegree 2 j i).trans
      (constructedA2ThreeCell_attachingDegree_zero W₁ _ j i)
  · dsimp only
    intro j i
    fin_cases j
    let : DecidableEq (CuspWCellIndex 4) := inferInstanceAs (DecidableEq (Fin 1))
    change standardA2ToricCellularCoordinateBoundary ((C.transport e₁).transport e₂).toCWDecomposition
      3 (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) i = 0
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 3 (0 : Fin 1) i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 3 (0 : Fin 1) i).symm.trans ?_
    exact (C.coordinateBoundary_single_eq_attachingDegree 3 (0 : Fin 1) i).trans
      (constructedA2FourCell_attachingDegree_zero W₁ _ i)

public theorem establishedStandardA2ToricCentralFiberIndependentIncidenceResidual
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberIndependentIncidenceResidual
      (establishedStandardA2ToricCentralFiberCellAtlas W R) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  let H := establishedStandardA2ToricCentralFiberHigherIncidenceResidual W R
  let W₀ := Classical.choice
    (SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions.BoundedPolydiscRegions.exists_actualLocalCuspQuotientWitness
      N Construction.constructedModel)
  let W₁ := Classical.choice (exists_actualPuncturedCuspCollarWitness W₀)
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let _ : T2Space (ActualLocalCuspFilling W₁) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W₁
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W₁) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W₁).t2Space
  let C := constructedCentralCellAtlas W₁
  let e₁ := centralOrbitModelHomeomorph W₁ W
  let e₂ := actualLocalCuspCentralOrbitCoreHomeomorph W R
  refine ⟨?_, ?_, H.boundaryTwo, H.boundaryThree⟩
  · dsimp only
    intro j i
    let : DecidableEq (CuspWCellIndex 1) := inferInstanceAs (DecidableEq (Fin 3))
    change standardA2ToricCellularCoordinateBoundary ((C.transport e₁).transport e₂).toCWDecomposition
      0 (Pi.single j 1 : Fin 3 → ℤ) i = _
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 0 j i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 0 j i).symm.trans ?_
    refine (C.coordinateBoundary_single_eq_attachingDegree 0 j i).trans ?_
    refine (constructedCentralCellAtlas_edge_attachingDegree W₁ _ j i).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  · dsimp only
    intro j i
    let : DecidableEq (CuspWCellIndex 2) := inferInstanceAs (DecidableEq (Fin 4))
    change standardA2ToricCellularCoordinateBoundary ((C.transport e₁).transport e₂).toCWDecomposition
      1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc = _
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 1 j i.castSucc).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 1 j i.castSucc).symm.trans ?_
    exact constructedA2TwoCell_coordinateBoundary_single_zero W₁ j i.castSucc

/-- The remaining combinatorial input: the twenty-eight scalar cellular-incidence entries in
the atlas coordinates. -/
public theorem establishedStandardA2ToricCentralFiberIncidenceResidual
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    StandardA2ToricCentralFiberIncidenceResidual
      (establishedStandardA2ToricCentralFiberCellAtlas W R) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  exact StandardA2ToricCentralFiberIncidenceResidual.ofIndependent
    (establishedStandardA2ToricCentralFiberIndependentIncidenceResidual W R)

/-- The actual quotient carrier, equipped with the CW structure constructed from the residual
characteristic maps and with the verified finite incidence table. -/
public noncomputable def establishedStandardA2ToricCentralFiberFiniteCellularRealization
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberFiniteCellularRealization (R.quotientCentralFiber W) := by
  letI : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact StandardA2ToricCentralFiberFiniteCellularRealization.ofAtlasAndIncidence
    (establishedStandardA2ToricCentralFiberCellAtlas W R)
    (establishedStandardA2ToricCentralFiberIncidenceResidual W R)

/-- The compact periodic `A₂` central fibre has its standard labelled CW realization and exact
attaching-incidence formula. -/
public noncomputable def establishedStandardA2ToricCentralFiberCellularRealization
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberCellularRealization (R.quotientCentralFiber W)
  := (establishedStandardA2ToricCentralFiberFiniteCellularRealization W R).toCellularRealization

/-- Standard toric-orbit CW decomposition for the compact quotient of the periodic `A₂` central
fibre.  This is the exact general toric-topology boundary absent from Mathlib: it supplies a CW
realization and labels its cells by the orbit strata, but asserts no homology or Euler value. -/
public noncomputable def establishedStandardA2ToricCentralFiberCWDecomposition
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    StandardA2ToricCentralFiberCWDecomposition (R.quotientCentralFiber W) := by
  letI : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (establishedStandardA2ToricCentralFiberCellAtlas W R).toCWDecomposition

/-- The actual quotient central fibre has the cusp toric cell model required by the local Euler
calculation. -/
public noncomputable def actualCuspCentralFiberCellModel
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    CuspToricCellModel (R.quotientCentralFiber W) :=
  (establishedStandardA2ToricCentralFiberCWDecomposition W R).toCuspToricCellModel


end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex
