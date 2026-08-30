module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization

/-!
# Geometric reduction of the cusp fibre specialization matrix

The finite matrix in `PaperCuspGeometricSpecialization` is reduced here to the images of
explicit homology classes on the marked period torus under its literal inclusion into the cusp
filling.  This keeps the existing labelled cellular coordinates fixed: no target basis is
renormalized.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Topology.PaperCuspSpecializationAlgebra
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace ActualCuspRadialClutchingData

/-- The marked fibre of the radial mapping-torus model, included back into the actual punctured
cusp collar. -/
public def markedFiberToPuncturedCusp (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    C(G.Fiber, puncturedLocalCuspQuotient W) := by
  let _ := G.fiberTopology
  let s : C(G.Fiber,
      OpenRadialInterval W.localWitness.radius × CircleMappingTorus G.clutching) :=
    (ContinuousMap.const G.Fiber G.markingRadius).prodMk
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
  exact (⟨G.totalHomeomorph.symm, G.totalHomeomorph.symm.continuous⟩ :
    C(OpenRadialInterval W.localWitness.radius × CircleMappingTorus G.clutching,
      puncturedLocalCuspQuotient W)).comp s

/-- The literal marked period fibre included into the cusp filling. -/
public def markedFiberToCuspFilling (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    C(G.Fiber, actualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  let i : C(puncturedLocalCuspQuotient W, actualLocalCuspFilling W) :=
    ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
  exact i.comp G.markedFiberToPuncturedCusp

/-- The marked fibre inclusion is literally the normalized additive-period point of the collar.
This is the point-set compatibility that rules out changing the source basis by a hidden torus
automorphism. -/
public theorem markedFiberToPuncturedCusp_eq_actualCuspCollarPeriodPoint
    (G : ActualCuspRadialClutchingData W) (y : let _ := G.fiberTopology; G.Fiber)
    (zeta : ComplexTwoSpace)
    (hy : let _ := G.fiberTopology
      G.fiberHomeomorph y = additiveTorusProjection G.fiberParameter zeta) :
    let _ := G.fiberTopology
    G.markedFiberToPuncturedCusp y =
      actualCuspCollarPeriodPoint W G.markingParameter_mem zeta := by
  let _ := G.fiberTopology
  exact (G.fiberNormalization y zeta).2 hy

/-- After adjoining the central fibre, the literal marked-fibre inclusion is still the quotient
of the same normalized additive-period point. -/
public theorem markedFiberToCuspFilling_eq_actualCuspCollarPeriodPoint
    (G : ActualCuspRadialClutchingData W) (y : let _ := G.fiberTopology; G.Fiber)
    (zeta : ComplexTwoSpace)
    (hy : let _ := G.fiberTopology
      G.fiberHomeomorph y = additiveTorusProjection G.fiberParameter zeta) :
    let _ := G.fiberTopology
    G.markedFiberToCuspFilling y =
      puncturedLocalCuspToFilling W
        (actualCuspCollarPeriodPoint W G.markingParameter_mem zeta) := by
  let _ := G.fiberTopology
  exact congrArg (puncturedLocalCuspToFilling W)
    (G.markedFiberToPuncturedCusp_eq_actualCuspCollarPeriodPoint y zeta hy)

private theorem openRadialIntervalProdHomotopyEquiv_apply
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    (p : OpenRadialInterval r × X) :
    openRadialIntervalProdHomotopyEquiv hr p = p.2 := by
  rfl

/-- Removing the radial coordinate sends the marked fibre inclusion to the standard mapping-torus
fibre inclusion. -/
public theorem totalHomotopyEquiv_comp_markedFiberToPuncturedCusp
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.toFun.comp G.markedFiberToPuncturedCusp =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching) := by
  let _ := G.fiberTopology
  ext y
  change openRadialIntervalProdHomotopyEquiv _
      (G.totalHomeomorph (G.totalHomeomorph.symm
        (G.markingRadius,
          finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching) y))) = _
  rw [G.totalHomeomorph.apply_symm_apply, openRadialIntervalProdHomotopyEquiv_apply]

private theorem specializationHomologyOneMap_apply
    (G : ActualCuspRadialClutchingData W)
    (y : let _ := G.fiberTopology;
      IntegralSingularHomology 1 (CircleMappingTorus G.clutching)) :
    let _ := G.fiberTopology
    G.specializationHomologyOneMap y =
      actualLocalCuspFillingHomologyOneEquiv W
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
          ((integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).symm y)) := by
  rfl

private theorem specializationHomologyTwoMap_apply
    (G : ActualCuspRadialClutchingData W)
    (y : let _ := G.fiberTopology;
      IntegralSingularHomology 2 (CircleMappingTorus G.clutching)) :
    let _ := G.fiberTopology
    G.specializationHomologyTwoMap y =
      actualLocalCuspFillingHomologyTwoEquiv W
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
          ((integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).symm y)) := by
  rfl

/-- The degree-one specialization map on a fibre class is the homology map of the literal marked
fibre inclusion into the filling. -/
public theorem specializationHomologyOneMap_fiberInclusion
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 1 G.Fiber) :
    let _ := G.fiberTopology
    G.specializationHomologyOneMap
        (integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x) =
      actualLocalCuspFillingHomologyOneEquiv W
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)
        (integralSingularHomologyMap 1 G.markedFiberToCuspFilling x) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  have hinv : e.symm
      (integralSingularHomologyMap 1
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x) =
      integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp x := by
    apply e.injective
    rw [e.apply_symm_apply]
    change integralSingularHomologyMap 1
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x =
      integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp x)
    rw [integralSingularHomologyMap_comp_wang]
    exact (congrArg (fun f ↦ integralSingularHomologyMap 1 f x)
      G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp).symm
  rw [specializationHomologyOneMap_apply, hinv, integralSingularHomologyMap_comp_wang]
  rfl

/-- The degree-two counterpart of `specializationHomologyOneMap_fiberInclusion`. -/
public theorem specializationHomologyTwoMap_fiberInclusion
    (G : ActualCuspRadialClutchingData W)
    (x : let _ := G.fiberTopology; IntegralSingularHomology 2 G.Fiber) :
    let _ := G.fiberTopology
    G.specializationHomologyTwoMap
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x) =
      actualLocalCuspFillingHomologyTwoEquiv W
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)
        (integralSingularHomologyMap 2 G.markedFiberToCuspFilling x) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  have hinv : e.symm
      (integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x) =
      integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp x := by
    apply e.injective
    rw [e.apply_symm_apply]
    change integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x =
      integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp x)
    rw [integralSingularHomologyMap_comp_wang]
    exact (congrArg (fun f ↦ integralSingularHomologyMap 2 f x)
      G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp).symm
  rw [specializationHomologyTwoMap_apply, hinv, integralSingularHomologyMap_comp_wang]
  rfl

/-- The standard representative of a degree-one cusp coinvariant generator in the marked
four-torus. -/
public noncomputable def degreeOneFiberGenerator
    (G : ActualCuspRadialClutchingData W) (j : Fin 2) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber := by
  let _ := G.fiberTopology
  exact G.monodromyCoordinates.degreeOne.symm
    (Pi.single (Fin.castAdd 2 j) 1)

/-- A section of the explicit degree-two coinvariant projection. -/
public def degreeTwoCoinvariantRepresentative (y : Fin 4 → ℤ) : Fin 6 → ℤ :=
  ![y 0, y 3, y 1, y 2, 0, 0]

/-- The standard representative of a degree-two cusp coinvariant generator in the marked
four-torus. -/
public noncomputable def degreeTwoFiberGenerator
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    let _ := G.fiberTopology
    IntegralSingularHomology 2 G.Fiber := by
  let _ := G.fiberTopology
  exact G.monodromyCoordinates.degreeTwo.symm
    (degreeTwoCoinvariantRepresentative (Pi.single j 1))

public theorem degreeOneCoinvariantsEquiv_symm_single
    (G : ActualCuspRadialClutchingData W) (j : Fin 2) :
    let _ := G.fiberTopology
    G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1) =
      Submodule.Quotient.mk (G.degreeOneFiberGenerator j) := by
  let _ := G.fiberTopology
  apply G.degreeOneCoinvariantsEquiv.injective
  rw [G.degreeOneCoinvariantsEquiv.apply_symm_apply]
  symm
  calc
    G.degreeOneCoinvariantsEquiv
        (Submodule.Quotient.mk (G.degreeOneFiberGenerator j)) =
        mZeroCoinvariantsEquivIntSquared
          (Submodule.Quotient.mk
            (G.monodromyCoordinates.degreeOne (G.degreeOneFiberGenerator j))) := rfl
    _ = headCoordinateProjection
        (G.monodromyCoordinates.degreeOne (G.degreeOneFiberGenerator j)) := rfl
    _ = headCoordinateProjection (Pi.single (Fin.castAdd 2 j) 1) := by
      rw [degreeOneFiberGenerator, G.monodromyCoordinates.degreeOne.apply_symm_apply]
    _ = Pi.single j 1 := by
      funext i
      fin_cases i <;> fin_cases j <;> rfl

public theorem degreeTwoCoinvariantsEquiv_symm_single
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    let _ := G.fiberTopology
    G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1) =
      Submodule.Quotient.mk (G.degreeTwoFiberGenerator j) := by
  let _ := G.fiberTopology
  apply G.degreeTwoCoinvariantsEquiv.injective
  rw [G.degreeTwoCoinvariantsEquiv.apply_symm_apply]
  symm
  calc
    G.degreeTwoCoinvariantsEquiv
        (Submodule.Quotient.mk (G.degreeTwoFiberGenerator j)) =
        mZeroExteriorTwoCoinvariantsEquivIntFourth
          (Submodule.Quotient.mk
            (G.monodromyCoordinates.degreeTwo (G.degreeTwoFiberGenerator j))) := rfl
    _ = mZeroExteriorTwoProjection
        (G.monodromyCoordinates.degreeTwo (G.degreeTwoFiberGenerator j)) := rfl
    _ = mZeroExteriorTwoProjection
        (degreeTwoCoinvariantRepresentative (Pi.single j 1)) := by
      rw [degreeTwoFiberGenerator, G.monodromyCoordinates.degreeTwo.apply_symm_apply]
    _ = Pi.single j 1 := by
      funext i
      fin_cases i <;> fin_cases j <;> rfl

end ActualCuspRadialClutchingData

namespace EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

/-- The exact point-set/cellular residue after removing all Wang-coordinate algebra: the images
of the six explicit marked-torus generators in the already selected cellular coordinates. -/
public structure MarkedFiberGeneratorSpecializationMatrix (A : PaperAnalyticData) : Prop where
  degreeOne (j : Fin 2) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1 G.markedFiberToCuspFilling
          (G.degreeOneFiberGenerator j)) =
      (Pi.single j 1 : Fin 2 → ℤ)
  degreeTwo (j : Fin 4) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
          (G.degreeTwoFiberGenerator j)) =
      (Pi.single j 1 : Fin 4 → ℤ)

/-- The literal marked-fibre calculation implies the original finite Wang-generator matrix
without changing any source or target coordinates. -/
public theorem finiteFiberGeneratorSpecializationMatrix_of_markedFiber
    (A : PaperAnalyticData) (h : MarkedFiberGeneratorSpecializationMatrix A) :
    FiniteFiberGeneratorSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j i
    change G.specializationHomologyOneMap
        ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i = _
    rw [G.degreeOneCoinvariantsEquiv_symm_single]
    change G.specializationHomologyOneMap
        (integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeOneFiberGenerator j)) i = _
    rw [G.specializationHomologyOneMap_fiberInclusion]
    have hj := congrFun (h.degreeOne j) i
    simpa [G, Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using hj
  · intro j i
    change G.specializationHomologyTwoMap
        ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) i = _
    rw [G.degreeTwoCoinvariantsEquiv_symm_single]
    change G.specializationHomologyTwoMap
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeTwoFiberGenerator j)) i = _
    rw [G.specializationHomologyTwoMap_fiberInclusion]
    have hj := congrFun (h.degreeTwo j) i
    simpa [G, Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using hj

end EstablishedStandardA2CuspSpecialization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
