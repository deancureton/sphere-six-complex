module

public import SphereSixComplex.Topology.StandardSphereHomologyAssembly
public import SphereSixComplex.Topology.StandardSphereMayerVietoris

/-!
# Integral homology of the standard six-sphere

The degreewise singular-homology calculation for a standard sphere is derived in
`StandardSphereMayerVietoris` from the two-puncture cover of the sphere and the established binary
open-cover Mayer--Vietoris sequence. The only external input behind the positive-degree calculation
is therefore `establishedIntegralMayerVietorisExactSequence`; this file assembles it with the proved
degree-zero comparison into the Section 7 graded realization.
-/

namespace SphereSixComplex

/-- The classical positive-degree integral homology calculation for the standard six-sphere,
derived from the established Mayer--Vietoris theorem alone. -/
public theorem establishedSixSpherePositiveHomologyInputs :
    SixSpherePositiveHomologyInputs :=
  sixSpherePositiveHomologyInputs_of_mayerVietorisInputs standardSphereMayerVietorisInputs

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
