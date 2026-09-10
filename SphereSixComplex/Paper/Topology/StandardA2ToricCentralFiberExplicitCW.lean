module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

/-!
# The explicit cellular specialization of the standard `A₂` cusp fibre

The actual radial specialization is transported into toric cellular homology. Degree one is
read in canonical deck coordinates through an explicit change from the cellular basis; degree
two retains the cellular coordinates. The Wang comparison follows from these marked values.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The actual collar specialization, followed by the selected homotopy equivalence from the
quotient central fibre to its labelled toric CW carrier. -/
public noncomputable def actualSpecializationToCWCarrierChainMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    integralSingularChainComplex (PuncturedLocalCuspQuotient W) ⟶
      let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
      let _ := C.topology
      integralSingularChainComplex C.Carrier := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  exact
    integralSingularChainMap
        ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ ≫
      R.specializationChainMap W ≫ integralSingularChainMap C.homotopyEquiv.toFun

/-- The canonical cellular homology class of a collar class under radial specialization. -/
public noncomputable def standardA2CellularSpecializationHomologyMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) (k : ℕ) :
    IntegralSingularHomology k (PuncturedLocalCuspQuotient W) →+
      cuspToricCellularChainComplex.homology k := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  letI := C.topology
  letI := C.cwComplex
  let I := establishedStandardA2ToricCentralFiberCellularIncidence W R
  exact
    (I.integralSingularHomologyEquiv k).toAddMonoidHom.comp
        ((integralSingularHomologyEquivOfHomotopyEquiv k C.homotopyEquiv).toAddMonoidHom.comp
          ((R.specializationHomologyMap W k).comp
            (integralSingularHomologyMap k
              ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩)))

/-- The existing degree-one coordinates of the cusp filling are exactly the explicit cellular
coordinates of the radial specialization. -/
public theorem actualLocalCuspFillingCellularHomologyOneEquiv_specialization_eq_cellular
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (x : IntegralSingularHomology 1 (PuncturedLocalCuspQuotient W)) :
    actualLocalCuspFillingCellularHomologyOneEquiv W R
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
      cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap W R 1 x) := by
  simp only [actualLocalCuspFillingCellularHomologyOneEquiv,
    actualCuspCentralFiberHomologyOneEquiv,
    StandardA2ToricCentralFiberCWDecomposition.carrierIntegralSingularHomologyOneEquiv,
    StandardA2ToricCellularIncidenceData.integralSingularHomologyOneEquiv,
    standardA2CellularSpecializationHomologyMap, AddEquiv.trans_apply,
    ActualLocalCuspCentralFiberRetractionData.specializationHomologyMap_eq_equiv]
  rfl

public theorem actualLocalCuspFillingHomologyOneEquiv_specialization_eq_cellular
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (x : IntegralSingularHomology 1 (PuncturedLocalCuspQuotient W)) :
    actualLocalCuspFillingHomologyOneEquiv W R
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
      actualCuspDeckCellularHomologyOneEquiv W R
        (standardA2CellularSpecializationHomologyMap W R 1 x) := by
  unfold actualCuspDeckCellularHomologyOneEquiv
  simp only [AddEquiv.trans_apply]
  rw [← actualLocalCuspFillingCellularHomologyOneEquiv_specialization_eq_cellular,
    AddEquiv.symm_apply_apply]
  rfl

/-- The analogous exact reduction in degree two. -/
public theorem actualLocalCuspFillingHomologyTwoEquiv_specialization_eq_cellular
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (x : IntegralSingularHomology 2 (PuncturedLocalCuspQuotient W)) :
    actualLocalCuspFillingHomologyTwoEquiv W R
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
      cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap W R 2 x) := by
  simp only [actualLocalCuspFillingHomologyTwoEquiv,
    actualCuspCentralFiberHomologyTwoEquiv,
    StandardA2ToricCentralFiberCWDecomposition.carrierIntegralSingularHomologyTwoEquiv,
    StandardA2ToricCellularIncidenceData.integralSingularHomologyTwoEquiv,
    standardA2CellularSpecializationHomologyMap, AddEquiv.trans_apply,
    ActualLocalCuspCentralFiberRetractionData.specializationHomologyMap_eq_equiv]
  rfl

/-- The calculation of the canonical cellular specialization on the Wang coordinates.  These
fields concern the explicit cellular complex, rather than the homology coordinates of the actual
cusp filling. -/
public structure StandardA2ToricCentralFiberExplicitCWRealization
    (W : ActualPuncturedCuspCollarWitness N M) [HasCuspPhaseSpreading W]
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (G : ActualCuspRadialClutchingData W) : Prop where
  degreeOne_wangCoordinates : ∀ x : IntegralSingularHomology 1
      (PuncturedLocalCuspQuotient W),
    actualCuspDeckCellularHomologyOneEquiv W R
        (standardA2CellularSpecializationHomologyMap W R 1 x) =
      fun i ↦ G.geometricHomologyOneEquiv x (Fin.castAdd 1 i)
  degreeTwo_wangCoordinates : ∀ x : IntegralSingularHomology 2
      (PuncturedLocalCuspQuotient W),
    cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap W R 2 x) =
      fun i ↦ G.geometricHomologyTwoEquiv x (Fin.castAdd 2 i)

namespace StandardA2ToricCentralFiberExplicitCWRealization

variable {W : ActualPuncturedCuspCollarWitness N M} [HasCuspPhaseSpreading W]
  {R : ActualLocalCuspCentralFiberRetractionData W}
  {G : ActualCuspRadialClutchingData W}

/-- The chain-level realization implies the degree-one specialization formula. -/
public theorem degreeOne
    (T : StandardA2ToricCentralFiberExplicitCWRealization W R G)
    (x : IntegralSingularHomology 1 (PuncturedLocalCuspQuotient W)) :
    actualLocalCuspFillingHomologyOneEquiv W R
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
      fun i ↦ G.geometricHomologyOneEquiv x (Fin.castAdd 1 i) := by
  rw [actualLocalCuspFillingHomologyOneEquiv_specialization_eq_cellular]
  exact T.degreeOne_wangCoordinates x

/-- The chain-level realization implies the degree-two specialization formula. -/
public theorem degreeTwo
    (T : StandardA2ToricCentralFiberExplicitCWRealization W R G)
    (x : IntegralSingularHomology 2 (PuncturedLocalCuspQuotient W)) :
    actualLocalCuspFillingHomologyTwoEquiv W R
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
      fun i ↦ G.geometricHomologyTwoEquiv x (Fin.castAdd 2 i) := by
  rw [actualLocalCuspFillingHomologyTwoEquiv_specialization_eq_cellular]
  exact T.degreeTwo_wangCoordinates x

end StandardA2ToricCentralFiberExplicitCWRealization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
