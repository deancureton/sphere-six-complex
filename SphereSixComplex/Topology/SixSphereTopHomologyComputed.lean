module

public import SphereSixComplex.Topology.BoundarySevenRealizationInjective
public import SphereSixComplex.Topology.SimplicialSixSphereTopHomologyKernel

/-!
# The standard six-sphere's top-homology orientation

The finite normalized-chain calculation and the explicit realization homeomorphism are now
complete.  This file combines them with the sole remaining comparison input, producing a
specific additive orientation of singular top homology.  The degree-theory endpoint then exposes
only the sign of the analytic antipodal map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- Once the integral simplicial-to-singular comparison is a quasi-isomorphism, the completed
finite calculation and realization homeomorphism give a specific additive orientation of
`H₆(S⁶;ℤ)`. -/
public noncomputable def sixSphereTopHomologyAddEquivOfComparisonQuasiIsomorphism
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) :
    IntegralSingularHomology 6 SixSphere ≃+ ℤ := by
  let e := Classical.choice boundarySevenRealizationHomeomorphSixSphere
  let orientation := Classical.choice boundarySevenSimplicialTopHomologyOrientation
  exact sixSphereTopHomologyAddEquivOfBoundaryComparison hcomparison e orientation

/-- The comparison quasi-isomorphism is therefore the only remaining input for the existence of
an additive top-homology orientation. -/
public theorem sixSphereTopHomologyOrientation_of_comparisonQuasiIsomorphism
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) :
    Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ) :=
  ⟨sixSphereTopHomologyAddEquivOfComparisonQuasiIsomorphism hcomparison⟩

/-- For the now-explicitly selected top-homology orientation, the antipodal sign is the sole
remaining field needed for the complete degree theory used by oriented markings. -/
public theorem sixSphereDegreeTheory_of_comparisonQuasiIsomorphism
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (hantipodal : sixSphereHomologicalDegree
        (sixSphereTopHomologyAddEquivOfComparisonQuasiIsomorphism hcomparison)
        OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1) :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory :=
  ⟨SixSphereTopHomologyOrientation.toDegreeTheory
    ⟨sixSphereTopHomologyAddEquivOfComparisonQuasiIsomorphism hcomparison,
      hantipodal⟩⟩

end SphereSixComplex
