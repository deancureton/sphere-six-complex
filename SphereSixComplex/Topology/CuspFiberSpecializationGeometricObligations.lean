module

public import SphereSixComplex.Topology.CuspFiberSpecializationHOneSurjectivity

/-!
# Remaining basis-free cusp specialization geometry

Degree-one surjectivity follows from the unwrapped filling cover and first Hurewicz. The remaining
content is one killed meridian section and, in degree two, surjectivity plus two killed invariant
suspension sections.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- The three source-specific topology facts remaining after degree-one surjectivity. -/
public structure RemainingFiberSpecializationGeometry
    (G : ActualCuspRadialClutchingData W) : Prop where
  degreeOne_section :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHOnePresentation G.clutching).GeometricSection,
      (rawDegreeOneTotalSpecialization G).comp S.lift = 0
  degreeTwo_surjective : Function.Surjective (rawDegreeTwoTotalSpecialization G)
  degreeTwo_section :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHTwoPresentation G.clutching).GeometricSection,
      (rawDegreeTwoTotalSpecialization G).comp S.lift = 0

/-- The remaining three geometric facts imply the two basis-free specialization
isomorphisms. -/
public theorem fiberCoinvariantSpecializationIsomorphisms_of_remainingGeometry
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : RemainingFiberSpecializationGeometry G)
    (cOne : IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 2 → ℤ))
    (cTwo : IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 4 → ℤ)) :
    FiberCoinvariantSpecializationIsomorphisms G :=
  fiberCoinvariantSpecializationIsomorphisms_of_surjective_of_section_eq_zero G
    { degreeOne_surjective := rawDegreeOneTotalSpecialization_surjective G b
      degreeOne_section := h.degreeOne_section
      degreeTwo_surjective := h.degreeTwo_surjective
      degreeTwo_section := h.degreeTwo_section }
    cOne cTwo

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
