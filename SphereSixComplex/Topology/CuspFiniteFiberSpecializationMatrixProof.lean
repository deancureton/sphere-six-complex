module

public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Topology.StandardA2ToricCentralFiberExplicitCW
public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationProof

/-!
# The finite cusp-fibre specialization matrix from cellular homology

This file reduces the marked fibre-generator matrix to the labelled cellular homology of the
standard `A₂` toric central fibre.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace WangHomologyPresentation

/-- A Wang splitting sends a class from the fibre coinvariants to the pure coinvariant summand. -/
public theorem totalLinearEquivCoinvariantsProdInvariantsOfSection_coinvariantsToTotal
    {HighRelations High Total LowRelations Low : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (x : P.Coinvariants) :
    P.totalLinearEquivCoinvariantsProdInvariantsOfSection S (P.coinvariantsToTotal x) =
      (x, 0) := by
  apply (P.totalLinearEquivCoinvariantsProdInvariantsOfSection S).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change P.coinvariantsToTotal x = P.coinvariantsToTotal x + S.lift 0
  rw [map_zero, add_zero]

end WangHomologyPresentation

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open WangHomologyPresentation

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

namespace ActualCuspRadialClutchingData

/-- A marked degree-one fibre generator occupies its corresponding pure Wang coinvariant. -/
public theorem geometricHomologyOneEquiv_markedFiberGenerator
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : ActualCuspRadialClutchingData W) (j : Fin 2) :
    let _ := G.fiberTopology
    G.geometricHomologyOneEquiv
        (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
          (G.degreeOneFiberGenerator j)) =
      Pi.single (Fin.castAdd 1 j) 1 := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  let P := circleMappingTorusHOnePresentation G.clutching
  have he :
      e (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
          (G.degreeOneFiberGenerator j)) =
        integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeOneFiberGenerator j) := by
    symm
    change integralSingularHomologyMap 1
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (G.degreeOneFiberGenerator j) =
      integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
          (G.degreeOneFiberGenerator j))
    rw [integralSingularHomologyMap_comp_wang]
    exact (congrArg
      (fun f ↦ integralSingularHomologyMap 1 f (G.degreeOneFiberGenerator j))
      G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp).symm
  have hincl :
      integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeOneFiberGenerator j) =
        P.coinvariantsToTotal (Submodule.Quotient.mk (G.degreeOneFiberGenerator j)) := by
    rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
    rfl
  have hc :
      G.degreeOneCoinvariantsEquiv
          (Submodule.Quotient.mk (G.degreeOneFiberGenerator j)) = Pi.single j 1 := by
    rw [← G.degreeOneCoinvariantsEquiv_symm_single j,
      G.degreeOneCoinvariantsEquiv.apply_symm_apply]
  change G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (e (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
        (G.degreeOneFiberGenerator j))) = _
  rw [he, hincl, circleMappingTorusHOneAddEquiv_apply, honeSplit,
    totalLinearEquivCoinvariantsProdInvariantsOfSection_coinvariantsToTotal]
  simp only [map_zero]
  change finTwoProdIntLinearEquiv
      (G.degreeOneCoinvariantsEquiv
        (Submodule.Quotient.mk (G.degreeOneFiberGenerator j)), 0) = _
  rw [hc]
  funext i
  fin_cases i <;> fin_cases j <;> rfl

/-- A marked degree-two fibre generator occupies its corresponding pure Wang coinvariant. -/
public theorem geometricHomologyTwoEquiv_markedFiberGenerator
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : ActualCuspRadialClutchingData W) (j : Fin 4) :
    let _ := G.fiberTopology
    G.geometricHomologyTwoEquiv
        (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
          (G.degreeTwoFiberGenerator j)) =
      Pi.single (Fin.castAdd 2 j) 1 := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let P := circleMappingTorusHTwoPresentation G.clutching
  have he :
      e (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
          (G.degreeTwoFiberGenerator j)) =
        integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeTwoFiberGenerator j) := by
    symm
    change integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (G.degreeTwoFiberGenerator j) =
      integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun
        (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
          (G.degreeTwoFiberGenerator j))
    rw [integralSingularHomologyMap_comp_wang]
    exact (congrArg
      (fun f ↦ integralSingularHomologyMap 2 f (G.degreeTwoFiberGenerator j))
      G.totalHomotopyEquiv_comp_markedFiberToPuncturedCusp).symm
  have hincl :
      integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeTwoFiberGenerator j) =
        P.coinvariantsToTotal (Submodule.Quotient.mk (G.degreeTwoFiberGenerator j)) := by
    rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
    rfl
  have hc :
      G.degreeTwoCoinvariantsEquiv
          (Submodule.Quotient.mk (G.degreeTwoFiberGenerator j)) = Pi.single j 1 := by
    rw [← G.degreeTwoCoinvariantsEquiv_symm_single j,
      G.degreeTwoCoinvariantsEquiv.apply_symm_apply]
  change G.geometricWangSections.circleMappingTorusHTwoAddEquiv
      (e (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
        (G.degreeTwoFiberGenerator j))) = _
  rw [he, hincl, circleMappingTorusHTwoAddEquiv_apply, htwoSplit,
    totalLinearEquivCoinvariantsProdInvariantsOfSection_coinvariantsToTotal]
  simp only [map_zero]
  change finFourProdFinTwoLinearEquiv
      (G.degreeTwoCoinvariantsEquiv
        (Submodule.Quotient.mk (G.degreeTwoFiberGenerator j)), 0) = _
  rw [hc]
  funext i
  fin_cases i <;> fin_cases j <;> rfl

end ActualCuspRadialClutchingData

namespace EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

/-- The residual calculation expressed entirely in the labelled `A₂` cellular homology. -/
public structure MarkedFiberCellularSpecializationMatrix (A : PaperAnalyticData) : Prop where
  degreeOne (j : Fin 2) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 1
          (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
            (G.degreeOneFiberGenerator j))) =
      (Pi.single j 1 : Fin 2 → ℤ)
  degreeTwo (j : Fin 4) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 2
          (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
            (G.degreeTwoFiberGenerator j))) =
      (Pi.single j 1 : Fin 4 → ℤ)

/-- A cellular realization with the standard Wang-coordinate calculation supplies all six
marked cellular coefficients. -/
public theorem markedFiberCellularSpecializationMatrix_of_explicitCWRealization
    (A : PaperAnalyticData)
    (T :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      StandardA2ToricCentralFiberExplicitCWRealization A.starCuspWitness
        A.cuspCentralFiberRetractionData G) :
    MarkedFiberCellularSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j
    change cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 1
          (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
            (G.degreeOneFiberGenerator j))) = Pi.single j 1
    rw [T.degreeOne_wangCoordinates,
      G.geometricHomologyOneEquiv_markedFiberGenerator j]
    funext i
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    change cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 2
          (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
            (G.degreeTwoFiberGenerator j))) = Pi.single j 1
    rw [T.degreeTwo_wangCoordinates,
      G.geometricHomologyTwoEquiv_markedFiberGenerator j]
    funext i
    fin_cases i <;> fin_cases j <;> rfl

/-- The labelled cellular calculation implies the marked-fibre specialization matrix. -/
public theorem markedFiberGeneratorSpecializationMatrix_of_cellular
    (A : PaperAnalyticData) (h : MarkedFiberCellularSpecializationMatrix A) :
    MarkedFiberGeneratorSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j
    calc
      actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 1 G.markedFiberToCuspFilling
            (G.degreeOneFiberGenerator j)) =
        actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
            (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
              (G.degreeOneFiberGenerator j))) := by
          apply congrArg (actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
            A.cuspCentralFiberRetractionData)
          change integralSingularHomologyMap 1
              ((⟨puncturedLocalCuspToFilling A.starCuspWitness,
                puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ :
                C(_, _)).comp G.markedFiberToPuncturedCusp)
              (G.degreeOneFiberGenerator j) = _
          rw [integralSingularHomologyMap_comp_wang]
      _ = cuspToricCellularChainComplex_homologyOneEquiv
          (standardA2CellularSpecializationHomologyMap A.starCuspWitness
            A.cuspCentralFiberRetractionData 1
            (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
              (G.degreeOneFiberGenerator j))) :=
        actualLocalCuspFillingHomologyOneEquiv_specialization_eq_cellular _ _ _
      _ = Pi.single j 1 := h.degreeOne j
  · intro j
    calc
      actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
            (G.degreeTwoFiberGenerator j)) =
        actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
            (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
              (G.degreeTwoFiberGenerator j))) := by
          apply congrArg (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
            A.cuspCentralFiberRetractionData)
          change integralSingularHomologyMap 2
              ((⟨puncturedLocalCuspToFilling A.starCuspWitness,
                puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ :
                C(_, _)).comp G.markedFiberToPuncturedCusp)
              (G.degreeTwoFiberGenerator j) = _
          rw [integralSingularHomologyMap_comp_wang]
      _ = cuspToricCellularChainComplex_homologyTwoEquiv
          (standardA2CellularSpecializationHomologyMap A.starCuspWitness
            A.cuspCentralFiberRetractionData 2
            (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
              (G.degreeTwoFiberGenerator j))) :=
        actualLocalCuspFillingHomologyTwoEquiv_specialization_eq_cellular _ _ _
      _ = Pi.single j 1 := h.degreeTwo j

/-- The cellular marked-generator calculation implies the original finite Wang matrix. -/
public theorem finiteFiberGeneratorSpecializationMatrix_of_cellular
    (A : PaperAnalyticData) (h : MarkedFiberCellularSpecializationMatrix A) :
    FiniteFiberGeneratorSpecializationMatrix A :=
  finiteFiberGeneratorSpecializationMatrix_of_markedFiber A
    (markedFiberGeneratorSpecializationMatrix_of_cellular A h)

/-- The standard explicit cellular realization implies the original finite Wang matrix. -/
public theorem finiteFiberGeneratorSpecializationMatrix_of_explicitCWRealization
    (A : PaperAnalyticData)
    (T :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      StandardA2ToricCentralFiberExplicitCWRealization A.starCuspWitness
        A.cuspCentralFiberRetractionData G) :
    FiniteFiberGeneratorSpecializationMatrix A :=
  finiteFiberGeneratorSpecializationMatrix_of_cellular A
    (markedFiberCellularSpecializationMatrix_of_explicitCWRealization A T)

end EstablishedStandardA2CuspSpecialization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
