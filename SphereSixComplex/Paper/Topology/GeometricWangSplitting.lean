module

public import SphereSixComplex.Paper.Topology.CircleMappingTorusHomologyBases
public import SphereSixComplex.Prerequisites.Topology.GeometricWangSection

/-!
# Geometric splittings of the Wang sequence

The abstract Wang calculation only determines the homology of a mapping torus as an extension.
For maps out of the mapping torus one must fix the geometric suspension classes, rather than use
an arbitrary projective lifting.  This file constructs the resulting coordinates from a supplied
right inverse to the Wang boundary map.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

namespace CircleMappingTorusHomologyBases

open LatticeData LatticeWangAlgebra Topology.PaperCuspSpecializationAlgebra

/-- Geometrically chosen suspension sections in degrees one and two. -/
public structure CuspGeometricWangSections
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) where
  degreeOne : (circleMappingTorusHOnePresentation phi).Section
  degreeTwo : (circleMappingTorusHTwoPresentation phi).Section

namespace CuspGeometricWangSections

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    {B : CuspMonodromyCoordinates phi}

/-- First-homology coordinates whose last coordinate is the specified geometric base-circle
class. -/
public noncomputable def circleMappingTorusHOneLinearEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 3 → ℤ) := by
  let P := circleMappingTorusHOnePresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroCoinvariantsEquivIntSquared
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
      (circleMonodromyDifference phi 0).toIntLinearMap 0
      B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt
  exact (P.linearEquivOfSection S.degreeOne).trans
    ((coinvariants.prodCongr invariants).trans finTwoProdIntLinearEquiv)

/-- Second-homology coordinates whose last two coordinates are the specified invariant
suspension classes. -/
public noncomputable def circleMappingTorusHTwoLinearEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 6 → ℤ) := by
  let P := circleMappingTorusHTwoPresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeTwo.toIntLinearEquiv
      (circleMonodromyDifference phi 2).toIntLinearMap mZeroExteriorTwoDifference
      B.degreeTwoDifference_conjugacy).trans mZeroExteriorTwoCoinvariantsEquivIntFourth
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  exact (P.linearEquivOfSection S.degreeTwo).trans
    ((coinvariants.prodCongr invariants).trans finFourProdFinTwoLinearEquiv)

public noncomputable def circleMappingTorusHOneAddEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃+ (Fin 3 → ℤ) :=
  S.circleMappingTorusHOneLinearEquiv.toAddEquiv

public noncomputable def circleMappingTorusHTwoAddEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃+ (Fin 6 → ℤ) :=
  S.circleMappingTorusHTwoLinearEquiv.toAddEquiv

end CuspGeometricWangSections

namespace CuspMonodromyCoordinates

/-- Projectivity of the two invariant lattices supplies sections of the Wang boundary maps. -/
public noncomputable def wangSections
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) : CuspGeometricWangSections B := by
  let degreeOnePresentation := circleMappingTorusHOnePresentation phi
  let degreeOneInvariants :=
    (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
      (circleMonodromyDifference phi 0).toIntLinearMap 0
      B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt
  letI : Module.Projective ℤ degreeOnePresentation.invariants :=
    Module.Projective.of_equiv' degreeOneInvariants.symm
  let degreeTwoPresentation := circleMappingTorusHTwoPresentation phi
  let degreeTwoInvariants :=
    (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  letI : Module.Projective ℤ degreeTwoPresentation.invariants :=
    Module.Projective.of_equiv' degreeTwoInvariants.symm
  exact
    { degreeOne := WangHomologyPresentation.Section.ofProjective degreeOnePresentation
      degreeTwo := WangHomologyPresentation.Section.ofProjective degreeTwoPresentation }

end CuspMonodromyCoordinates
end CircleMappingTorusHomologyBases

end SphereSixComplex
