module

public import SphereSixComplex.Topology.CuspMarkedFiberCellularCoinvariantNaturality

/-!
# Exact residual for the finite cusp-fibre specialization matrix

The toric atlas and incidence table determine the labelled cellular chain complex, but not the
naturality of its objectwise cellular-to-singular homology equivalence.  This file proves that
the finite specialization matrix is exactly the pair of labelled naturality squares on the Wang
coinvariants.  Thus no generator coefficient remains after supplying that comparison, and the
incidence axioms alone do not contain it.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

namespace EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

/-- The finite Wang matrix recovers the same statement on the literal marked-fibre generators. -/
public theorem markedFiberGeneratorSpecializationMatrix_of_finiteFiber
    (A : PaperAnalyticData) (h : FiniteFiberGeneratorSpecializationMatrix A) :
    MarkedFiberGeneratorSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j
    funext i
    have hij := h.degreeOne j i
    change G.specializationHomologyOneMap
        ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i = _ at hij
    rw [G.degreeOneCoinvariantsEquiv_symm_single] at hij
    change G.specializationHomologyOneMap
        (integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeOneFiberGenerator j)) i = _ at hij
    rw [G.specializationHomologyOneMap_fiberInclusion] at hij
    simpa [G, Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using hij
  · intro j
    funext i
    have hij := h.degreeTwo j i
    change G.specializationHomologyTwoMap
        ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) i = _ at hij
    rw [G.degreeTwoCoinvariantsEquiv_symm_single] at hij
    change G.specializationHomologyTwoMap
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeTwoFiberGenerator j)) i = _ at hij
    rw [G.specializationHomologyTwoMap_fiberInclusion] at hij
    simpa [G, Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using hij

/-- The literal marked-fibre matrix determines its expression in the fixed labelled cellular
coordinates; no target coordinate equivalence is changed. -/
public theorem markedFiberCellularSpecializationMatrix_of_markedFiber
    (A : PaperAnalyticData) (h : MarkedFiberGeneratorSpecializationMatrix A) :
    MarkedFiberCellularSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  constructor
  · intro j
    rw [← h.degreeOne j]
    change cuspToricCellularChainComplex_homologyOneEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 1
          (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
            (G.degreeOneFiberGenerator j))) =
      actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1 G.markedFiberToCuspFilling
          (G.degreeOneFiberGenerator j))
    calc
      _ = actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
            (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
              (G.degreeOneFiberGenerator j))) :=
        (actualLocalCuspFillingHomologyOneEquiv_specialization_eq_cellular
          A.starCuspWitness A.cuspCentralFiberRetractionData _).symm
      _ = _ := by
        apply congrArg (actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData)
        change integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
              (integralSingularHomologyMap 1 G.markedFiberToPuncturedCusp
                (G.degreeOneFiberGenerator j)) =
          integralSingularHomologyMap 1
            ((⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ : C(_, _)).comp
                G.markedFiberToPuncturedCusp)
            (G.degreeOneFiberGenerator j)
        exact integralSingularHomologyMap_comp_wang 1 _ _ _
  · intro j
    rw [← h.degreeTwo j]
    change cuspToricCellularChainComplex_homologyTwoEquiv
        (standardA2CellularSpecializationHomologyMap A.starCuspWitness
          A.cuspCentralFiberRetractionData 2
          (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
            (G.degreeTwoFiberGenerator j))) =
      actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
          (G.degreeTwoFiberGenerator j))
    calc
      _ = actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
            (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
              (G.degreeTwoFiberGenerator j))) :=
        (actualLocalCuspFillingHomologyTwoEquiv_specialization_eq_cellular
          A.starCuspWitness A.cuspCentralFiberRetractionData _).symm
      _ = _ := by
        apply congrArg (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
          A.cuspCentralFiberRetractionData)
        change integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
              (integralSingularHomologyMap 2 G.markedFiberToPuncturedCusp
                (G.degreeTwoFiberGenerator j)) =
          integralSingularHomologyMap 2
            ((⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ : C(_, _)).comp
                G.markedFiberToPuncturedCusp)
            (G.degreeTwoFiberGenerator j)
        exact integralSingularHomologyMap_comp_wang 2 _ _ _

/-- The finite matrix is precisely the missing pair of labelled cellular naturality squares on
the Wang coinvariants. -/
public theorem finiteFiberGeneratorSpecializationMatrix_iff_coinvariantNaturality
    (A : PaperAnalyticData) :
    FiniteFiberGeneratorSpecializationMatrix A ↔
      MarkedFiberCellularCoinvariantNaturality A := by
  constructor
  · intro h
    exact coinvariantNaturality_of_markedFiberCellularSpecializationMatrix A
      (markedFiberCellularSpecializationMatrix_of_markedFiber A
        (markedFiberGeneratorSpecializationMatrix_of_finiteFiber A h))
  · intro h
    exact finiteFiberGeneratorSpecializationMatrix_of_cellular A
      (markedFiberCellularSpecializationMatrix_of_coinvariantNaturality A h)

end EstablishedStandardA2CuspSpecialization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
