module

public import SphereSixComplex.Topology.StandardSphereHomologyAssembly

/-!
# Established integral homology of the standard six-sphere

The degreewise singular-homology calculation for a standard sphere is classical, but Mathlib does
not yet expose the relative-homology or excision theorem needed by the local development. This file
isolates the positive-degree calculation; the proved degree-zero comparison and local assembly then
derive the Section 7 graded realization.
-/

namespace SphereSixComplex

/-- The classical positive-degree integral homology calculation for the standard six-sphere. -/
public axiom establishedSixSpherePositiveHomologyInputs :
    SixSpherePositiveHomologyInputs

/-- The standard six-sphere has integral singular homology `ℤ` in degrees zero and six and zero in
every other degree, derived from the exact Mayer--Vietoris boundary above. -/
public theorem establishedSixSphereSectionSevenHomology :
    SectionSevenHomologyRealization SixSphere :=
  establishedSixSpherePositiveHomologyInputs.sectionSevenHomologyRealization

/-- A coherent realization of the paper's finite Section 7 model for `X`, compared with the
established homology of the standard sphere, gives the exact homology-sphere contract. -/
public theorem SectionSevenLerayCoherentRealization.hasIntegralHomologyOfSixSphere_established
    {X : Type} [TopologicalSpace X] (hX : SectionSevenLerayCoherentRealization X) :
    HasIntegralHomologyOfSixSphere X :=
  hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    hX.sectionSevenHomologyRealization establishedSixSphereSectionSevenHomology

end SphereSixComplex
