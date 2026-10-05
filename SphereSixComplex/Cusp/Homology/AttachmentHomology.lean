module

public import SphereSixComplex.Elliptic.Homology.FourthHomologySweep
public import SphereSixComplex.Regular.Transport.Fiber
public import SphereSixComplex.Cusp.Wang.BandCoordinates
public import SphereSixComplex.Cusp.Wang.NormalizedBandMarking


@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData

public theorem cuspToFilling_homologyTwo_surjective (A : AnalyticData) :
    Function.Surjective (integralSingularHomologyMap 2
      (A.openEmbeddingStarData.toFilling 0).hom) := by
  have hp (x) : A.actualCuspFillingHomologyTwoEquiv
      (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
      fun i ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i) :=
    CuspSpecialization.degreeTwo A x
  intro y
  refine ⟨A.cuspRawHomologyTwoEquiv.symm
    (Fin.append (A.actualCuspFillingHomologyTwoEquiv y) (0 : Fin 2 → ℤ)), ?_⟩
  apply A.actualCuspFillingHomologyTwoEquiv.injective
  rw [hp, AddEquiv.apply_symm_apply]
  ext i
  simp

end SphereSixComplex.Geometry.AnalyticData
