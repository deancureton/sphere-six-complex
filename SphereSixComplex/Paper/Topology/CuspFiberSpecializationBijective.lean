module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationTypes
public import SphereSixComplex.Paper.Topology.CuspFiberSpecializationColumns
public import SphereSixComplex.Prerequisites.Topology.PrimitiveFourColumnBasis
public import SphereSixComplex.Paper.Topology.CuspMixedTorusIntegralColumns

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

theorem cuspFiberSpecializationTwoBijective (A : AnalyticData)
    (T : CellularHomology.IntegralComparison) : (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      Function.Bijective (G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)) := by
  let _ := actualLocalCuspFilling_t2 A.starCuspWitness
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient A.starCuspWitness) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding A.starCuspWitness).t2Space
  obtain ⟨a,b,c,ha,hb,hc,h1,h2,h3⟩ := A.cuspMixedSourceColumns T
  have hu (z : ℤ) (hz : z = 1 ∨ z = -1) : IsUnit z := by
    rcases hz with rfl | rfl <;> simp
  obtain ⟨a, rfl⟩ := hu a ha
  obtain ⟨b, rfl⟩ := hu b hb
  obtain ⟨c, rfl⟩ := hu c hc
  apply A.cuspFiberSpecializationTwoBijective_of_columns
    (phaseSweepFillingHomologyTwoEquiv A.starCuspWitness A.cuspCentralFiberRetractionData T) a b c
  intro j
  fin_cases j
  · exact h1.trans (signedMixedThreeColumnEquiv_one a b c).symm
  · exact h2.trans (signedMixedThreeColumnEquiv_two a b c).symm
  · exact h3.trans (signedMixedThreeColumnEquiv_three a b c).symm

end SphereSixComplex.Geometry.AnalyticData
