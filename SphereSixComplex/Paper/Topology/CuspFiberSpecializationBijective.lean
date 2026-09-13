module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationTypes
public import SphereSixComplex.Paper.Topology.CuspFiberSpecializationColumns
public import SphereSixComplex.Prerequisites.Topology.PrimitiveFourColumnBasis
public import SphereSixComplex.Paper.Topology.CuspBoundaryMixedCoordinates

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open CuspCollar CuspRadialClutchingConstruction
open InfiniteA2Toric
open CircleMappingTorusHomologyBases

theorem cuspFiberSpecializationTwoBijective_of_columns (A : AnalyticData)
    (e : IntegralSingularHomology 2 (ActualLocalCuspFilling A.starCuspWitness) ≃+ (Fin 4 → ℤ))
    (a b c : ℤˣ)
    (hc : ∀ j : Fin 3, e (A.cuspFiberSpecializationColumn j.succ) =
      signedMixedThreeColumnEquiv a b c (Pi.single j.succ 1)) :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      Function.Bijective (G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)) := by
  obtain ⟨r, hr⟩ := exists_fourCoordinates_of_signed_mixed e A.cuspFiberSpecializationColumn
    (constructedCuspHomologyTwoPositiveReadout A) a b c hc
    A.cuspFiberSpecializationColumn_positive_zero A.cuspFiberSpecializationColumn_positive_one
  rw [A.actualCuspRadialClutchingData_eq]
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  let t := actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
    (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
  apply additive_bijective_of_basis_readout G.degreeTwoCoinvariantsEquiv.toAddEquiv
    (t.symm.trans r)
    (G.specializationHomologyTwoMap.comp
      (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal).toAddMonoidHom
  intro j
  change r (t.symm (G.specializationHomologyTwoMap
    ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
      (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))))) = _
  rw [G.degreeTwoCoinvariantsEquiv_symm_single]
  change r (t.symm (G.specializationHomologyTwoMap
    (integralSingularHomologyMap 2
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
      (G.degreeTwoFiberGenerator j)))) = _
  rw [G.specializationHomologyTwoMap_fiberInclusion]
  change r (t.symm (t (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
    (G.degreeTwoFiberGenerator j)))) = _
  rw [AddEquiv.symm_apply_apply, ← A.cuspFiniteFiberTorusToFilling_homology j]
  exact hr j

theorem cuspFiberSpecializationTwoBijective (A : AnalyticData) :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      Function.Bijective (G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)) := by
  apply A.cuspFiberSpecializationTwoBijective_of_columns
    (Construction.CentralFiberHomology.fillingHomologyTwoEquiv
      A.starCuspWitness A.cuspCentralFiberRetractionData) 1 (-1) (-1)
  intro j
  have h := BoundaryMixedTori.fillingHomologyTwoEquiv_mixedTorus
    A A.cuspCentralFiberRetractionData j
  fin_cases j <;>
    simpa [cuspFiberSpecializationColumn, BoundaryMixedTori.index,
      signedMixedThreeColumnEquiv_apply] using h

end SphereSixComplex.Geometry.AnalyticData
