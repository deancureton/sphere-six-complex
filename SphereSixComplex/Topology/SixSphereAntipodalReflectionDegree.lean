module

public import SphereSixComplex.Topology.SixSphereAntipodalDegree
public import SphereSixComplex.Topology.SixSphereAntipodalReflectionHomotopy
public import SphereSixComplex.Topology.SixSphereTopHomologyComputed

/-!
# Antipodal degree reduced to one coordinate reflection

The explicit ambient rotation homotopy identifies the analytic antipodal map with reflection in
coordinate zero.  Homotopy invariance of singular homology therefore reduces the remaining sign
calculation to that elementary reflection, independently of any chosen top-homology generator.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology ContinuousMap Simplicial

namespace SphereSixComplex

/-- The analytic antipodal map and coordinate reflection induce the same endomorphism of top
integral homology. -/
public theorem sixSphereTopIntegralHomologyMap_antipodal_eq_coordinateReflection :
    sixSphereTopIntegralHomologyMap
        OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun =
      sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap :=
  sixSphereTopIntegralHomologyMap_eq_of_homotopic
    sixSphere_antipodal_homotopic_coordinateReflection

/-- The orientation-free antipodal calculation is exactly the assertion that coordinate
reflection acts by negation on top integral homology. -/
public theorem sixSphereAntipodalActsByNegation_iff_coordinateReflection :
    SixSphereAntipodalActsByNegation ↔
      sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
        -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) := by
  unfold SixSphereAntipodalActsByNegation
  rw [sixSphereTopIntegralHomologyMap_antipodal_eq_coordinateReflection]

/-- Negation for the coordinate-reflection action proves antipodal degree `-1` for any selected
top-homology generator. -/
public theorem sixSphere_antipodalDegree_of_coordinateReflection
    (hreflection :
      sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
        -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere))
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1 :=
  sixSphere_antipodalDegree_of_actsByNegation
    (sixSphereAntipodalActsByNegation_iff_coordinateReflection.mpr hreflection)
    orientation

/-- The complete degree theory now has exactly two independent inputs: the canonical integral
simplicial-to-singular comparison and the top-homology action of coordinate reflection. -/
public theorem sixSphereDegreeTheory_of_comparison_coordinateReflection
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (hreflection :
      sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
        -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere)) :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory :=
  sixSphereDegreeTheory_of_comparisonQuasiIsomorphism hcomparison
    (sixSphere_antipodalDegree_of_coordinateReflection hreflection
      (sixSphereTopHomologyAddEquivOfComparisonQuasiIsomorphism hcomparison))

end SphereSixComplex
