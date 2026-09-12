module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HigherIncidence
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.DegreeTwoIncidence
public import SphereSixComplex.Paper.Topology.ToricCellAtlasIncidenceTransport

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap
namespace SphereSixComplex

namespace Geometry.CuspCollar

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric

/-- Transport the explicit characteristic maps from the constructed toric model. -/
public noncomputable def centralOrbitCellAtlas
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    CentralFiber.CellAtlas (ActualLocalCuspCentralOrbitQuotient W) := by
  let W₀ := Classical.choice
    (SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions.BoundedPolydiscRegions.exists_actualLocalCuspQuotientWitness
      N Construction.constructedModel)
  let W₁ := Classical.choice (exists_actualPuncturedCuspCollarWitness W₀)
  exact (constructedCentralCellAtlas W₁).transport (centralOrbitModelHomeomorph W₁ W)

/-- Transport the orbit-quotient atlas to the radial retraction's concrete central-fibre
subspace. -/
public noncomputable def centralFiberCellAtlas
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    CentralFiber.CellAtlas (R.quotientCentralFiber W) := by
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (centralOrbitCellAtlas W).transport
    (actualLocalCuspCentralOrbitCoreHomeomorph W R)

public theorem centralFiber_coordinateBoundary_eq
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    let _ : T2Space (ActualLocalCuspFilling W) :=
      SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
    let _ : T2Space (R.quotientCentralFiber W) := inferInstance
    ∀ n, CentralFiber.CWModel.coordinateBoundary
        (centralFiberCellAtlas W R).toCWModel n =
      CentralFiber.boundary n := by
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
  dsimp only
  intro n
  apply CentralFiber.CWModel.coordinateBoundary_eq_of_independent
  · intro j i
    let : DecidableEq (CentralFiber.Cell 1) := inferInstanceAs (DecidableEq (Fin 3))
    change CentralFiber.CWModel.coordinateBoundary ((C.transport e₁).transport e₂).toCWModel
      0 (Pi.single j 1 : Fin 3 → ℤ) i = _
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 0 j i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 0 j i).symm.trans ?_
    refine (C.coordinateBoundary_single_eq_attachingDegree 0 j i).trans ?_
    refine (constructedCentralCellAtlas_edge_attachingDegree W₁ _ j i).trans ?_
    fin_cases i <;> fin_cases j <;> rfl
  · intro j i
    let : DecidableEq (CentralFiber.Cell 2) := inferInstanceAs (DecidableEq (Fin 4))
    change CentralFiber.CWModel.coordinateBoundary ((C.transport e₁).transport e₂).toCWModel
      1 (Pi.single j 1 : Fin 4 → ℤ) i.castSucc = _
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 1 j i.castSucc).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 1 j i.castSucc).symm.trans ?_
    exact twoCell_coordinateBoundary_single_zero W₁ j i.castSucc
  · intro j i
    let : DecidableEq (CentralFiber.Cell 3) := inferInstanceAs (DecidableEq (Fin 2))
    change CentralFiber.CWModel.coordinateBoundary ((C.transport e₁).transport e₂).toCWModel
      2 (Pi.single j 1 : Fin 2 → ℤ) i = 0
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 2 j i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 2 j i).symm.trans ?_
    exact (C.coordinateBoundary_single_eq_attachingDegree 2 j i).trans
      (threeCell_attachingDegree_zero W₁ _ j i)
  · intro j i
    fin_cases j
    let : DecidableEq (CentralFiber.Cell 4) := inferInstanceAs (DecidableEq (Fin 1))
    change CentralFiber.CWModel.coordinateBoundary ((C.transport e₁).transport e₂).toCWModel
      3 (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) i = 0
    refine ((C.transport e₁).transport_coordinateBoundary_single e₂ 3 (0 : Fin 1) i).symm.trans ?_
    refine (C.transport_coordinateBoundary_single e₁ 3 (0 : Fin 1) i).symm.trans ?_
    exact (C.coordinateBoundary_single_eq_attachingDegree 3 (0 : Fin 1) i).trans
      (fourCell_attachingDegree_zero W₁ _ i)

/-- The compact periodic `A₂` central fibre has its standard labelled CW realization and exact
attaching-incidence formula. -/
public noncomputable def centralFiberCellularModel
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    CentralFiber.CellularModel (R.quotientCentralFiber W)
    := by
  letI : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (centralFiberCellAtlas W R).toCWModel.toCellularModel
    (centralFiber_coordinateBoundary_eq W R)

/-- The quotient central fibre equipped with its labelled CW model. -/
public noncomputable def centralFiberCWModel
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    CentralFiber.CWModel (R.quotientCentralFiber W) := by
  letI : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  letI : T2Space (R.quotientCentralFiber W) := inferInstance
  exact (centralFiberCellAtlas W R).toCWModel

/-- The actual quotient central fibre has the cusp toric cell model required by the local Euler
calculation. -/
public noncomputable def actualCuspCentralFiberCellModel
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    CuspToricCellModel (R.quotientCentralFiber W) :=
  (centralFiberCWModel W R).toCuspToricCellModel


end Geometry.CuspCollar

end SphereSixComplex
