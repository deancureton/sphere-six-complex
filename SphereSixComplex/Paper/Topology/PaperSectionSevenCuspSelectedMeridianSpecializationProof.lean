module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianSectionGeneratorCompletion
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof

/-!
# Specialization of the selected cusp meridian

The specialization-normalized Wang section is killed by the cusp filling map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open CuspCollar
open CuspCollar.CuspFiberSpecializationNormalization
open CuspSpecialization

/-- The selected positive Wang-section generator lies in the cusp-filling kernel. -/
public theorem rawDegreeOneTotalSpecialization_selectedPositiveMeridianClass
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    rawDegreeOneTotalSpecialization G (cuspSelectedPositiveMeridianClass A) = 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  let c := actualCuspDeckHomologyOneEquiv A.starCuspWitness
  apply c.injective
  have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeOne
    (e.symm (cuspSelectedPositiveMeridianClass A))
  have hspec :
      c (rawDegreeOneTotalSpecialization G
        (cuspSelectedPositiveMeridianClass A)) =
        degreeOneFiberProjection
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv
            (cuspSelectedPositiveMeridianClass A)) := by
    change c (integralSingularHomologyMap 1
        ⟨puncturedLocalCuspToFilling A.starCuspWitness,
          puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
        (e.symm (cuspSelectedPositiveMeridianClass A))) = _
    change _ = degreeOneFiberProjection
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (e (e.symm (cuspSelectedPositiveMeridianClass A)))) at h
    rw [e.apply_symm_apply] at h
    simpa [G, actualCuspRadialClutchingData_eq] using h
  change c (rawDegreeOneTotalSpecialization G
    (cuspSelectedPositiveMeridianClass A)) = c 0
  rw [map_zero, hspec, cuspSelectedPositiveMeridianClass_raw_coordinate]
  ext i
  fin_cases i <;> rfl

end SphereSixComplex.Geometry.AnalyticData

end
