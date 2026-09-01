module

public import SphereSixComplex.Topology.CuspFiberSpecializationHOneSurjectivity
public import SphereSixComplex.Topology.PaperCuspMarkedFiberAngularVanishingProof

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

namespace CuspFiberSpecializationNormalization

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

/-- The actual degree-one fibre specialization is a basis-free isomorphism. -/
public theorem rawDegreeOneFiberSpecialization_bijective
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    Function.Bijective (rawDegreeOneFiberSpecialization G) := by
  let _ := G.fiberTopology
  obtain ⟨S, hS⟩ := actualCuspDegreeOne_section G b
  exact
    WangHomologyPresentation.coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
      (circleMappingTorusHOnePresentation G.clutching) S
      (rawDegreeOneTotalSpecialization G)
      (rawDegreeOneTotalSpecialization_surjective G b) hS
      G.degreeOneCoinvariantsEquiv
      (actualLocalCuspFillingHomologyOneEquiv W
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)).toIntLinearEquiv

/-- Some target coordinates make the two degree-one fibre-generator coefficients the identity
matrix. -/
public theorem exists_degreeOneFiberSpecializationNormalization
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
    let _ := G.fiberTopology
    ∃ e : IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 2 → ℤ),
      ∀ j i : Fin 2,
        e (rawDegreeOneFiberSpecialization G
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i =
            (Pi.single j 1 : Fin 2 → ℤ) i := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let h := rawDegreeOneFiberSpecialization_bijective G b
  let e := WangHomologyPresentation.normalizedTargetCoordinates P
    (rawDegreeOneFiberSpecialization G) h G.degreeOneCoinvariantsEquiv
  refine ⟨e, ?_⟩
  intro j i
  have he := DFunLike.congr_fun
    (WangHomologyPresentation.normalizedTargetCoordinates_comp P
      (rawDegreeOneFiberSpecialization G) h G.degreeOneCoinvariantsEquiv)
    (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))
  change e (rawDegreeOneFiberSpecialization G
      (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) =
    G.degreeOneCoinvariantsEquiv
      (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1)) at he
  rw [G.degreeOneCoinvariantsEquiv.apply_symm_apply] at he
  exact congrFun he i

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
