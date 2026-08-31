module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianSectionGeneratorCompletion
public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationMatrixProof

/-!
# Specialization of the selected cusp meridian

The specialization-normalized Wang section is killed by the cusp filling map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open CuspPuncturedCollarBridge
open CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization
open CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

/-- The selected positive Wang-section generator lies in the cusp-filling kernel. -/
public theorem rawDegreeOneTotalSpecialization_selectedPositiveMeridianClass
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    rawDegreeOneTotalSpecialization G (actualCuspSelectedPositiveMeridianClass A) = 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  let c := actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
    A.cuspCentralFiberRetractionData
  apply c.injective
  have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeOne
    (e.symm (actualCuspSelectedPositiveMeridianClass A))
  have hspec :
      c (rawDegreeOneTotalSpecialization G
        (actualCuspSelectedPositiveMeridianClass A)) =
        degreeOneFiberProjection
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv
            (actualCuspSelectedPositiveMeridianClass A)) := by
    change c (integralSingularHomologyMap 1
        ⟨puncturedLocalCuspToFilling A.starCuspWitness,
          puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
        (e.symm (actualCuspSelectedPositiveMeridianClass A))) = _
    change _ = degreeOneFiberProjection
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (e (e.symm (actualCuspSelectedPositiveMeridianClass A)))) at h
    rw [e.apply_symm_apply] at h
    simpa [G, actualCuspRadialClutchingData_eq] using h
  change c (rawDegreeOneTotalSpecialization G
    (actualCuspSelectedPositiveMeridianClass A)) = c 0
  rw [map_zero, hspec, actualCuspSelectedPositiveMeridianClass_rawCoordinate]
  ext i
  fin_cases i <;> rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end
