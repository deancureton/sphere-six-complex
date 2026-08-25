module

public import SphereSixComplex.Topology.DiskSevenRelativeHomologyLow
public import SphereSixComplex.Topology.HomotopySphereHomology
public import SphereSixComplex.Topology.SingularHomologyModTwo

/-!
# From the cover-small disk pair to mod-two middle homology

This file connects the explicit relative-chain reduction for `(D⁷,S⁶)` to the exact mod-two
homology input used by the Kervaire route.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The two explicit low-degree cover-small relative calculations imply the required mod-two
middle-homology vanishing for the project's standard six-sphere. -/
public theorem sixSphere_modTwoHomology_three_isZero_of_coverSmallRelative
    (h : DiskSevenCoverSmallRelativeLowAcyclic) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)) := by
  have h₂ : IsZero ((IntegralSingularChainComplexObj
      (TopCat.sphere 6)).homology 2) :=
    standardSphereSix_integralSingularHomology_two_isZero_of_coverSmallRelative h.1
  have h₃ : IsZero ((IntegralSingularChainComplexObj
      (TopCat.sphere 6)).homology 3) :=
    standardSphereSix_integralSingularHomology_three_isZero_of_coverSmallRelative h.2
  have hmod : IsZero ((ModTwoSingularChainComplexObj
      (TopCat.sphere 6)).homology 3) :=
    modTwoSingularHomologyThree_isZero (TopCat.sphere 6) h₃ h₂
  exact hmod.of_iso
    (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).mapIso
        (TopCat.isoOfHomeo sixSphereHomeomorphTopCatSphereSix))

/-- The same two local relative calculations give the Kervaire homology input for every marked
smooth homotopy six-sphere. -/
public theorem markedHomotopySixSphere_modTwoHomology_three_isZero_of_coverSmallRelative
    (h : DiskSevenCoverSmallRelativeLowAcyclic)
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)) :=
  markedHomotopySixSphere_modTwoHomology_three_isZero_of_standard
    (sixSphere_modTwoHomology_three_isZero_of_coverSmallRelative h) S

end SphereSixComplex
