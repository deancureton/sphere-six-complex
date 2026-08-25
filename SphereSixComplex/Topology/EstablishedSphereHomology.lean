module

public import SphereSixComplex.Topology.StandardSphereHomologyAssembly
public import SphereSixComplex.Topology.SixSpherePositiveHomologyInputsProof

/-!
# Integral homology of the standard six-sphere

The degreewise singular-homology calculation for a standard sphere is transported from the
explicit simplicial calculation on the boundary of the seven-simplex. This file assembles it with
the proved degree-zero comparison into the Section 7 graded realization.
-/

namespace SphereSixComplex

/-- The proved positive-degree integral homology calculation for the standard six-sphere. -/
public theorem establishedSixSpherePositiveHomologyInputs :
    SixSpherePositiveHomologyInputs :=
  establishedSixSpherePositiveHomologyInputs_proof

/-- The standard six-sphere has integral singular homology `ℤ` in degrees zero and six and zero in
every other degree. -/
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
