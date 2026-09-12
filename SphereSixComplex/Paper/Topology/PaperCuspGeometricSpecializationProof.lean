module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

/-!
# Degree-two Wang coordinate evaluation

The geometric degree-two equivalence is evaluated through its chosen section, the coinvariant
and invariant coordinates, and the finite-product coordinate equivalence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex

namespace CircleMappingTorusHomologyBases

open LatticeData LatticeWangAlgebra CuspMonodromyCoinvariants

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}


/-- The degree-two coinvariant coordinates attached to a fibre marking. -/
public def htwoCoinv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHTwoPresentation phi).Coinvariants ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (coinvariantsEquivOfConjugacy B.degreeTwo.toIntLinearEquiv
    (circleMonodromyDifference phi 2).toIntLinearMap mZeroExteriorTwoDifference
    B.degreeTwoDifference_conjugacy).trans mZeroExteriorTwoCoinvariantsEquivIntFourth

/-- The degree-two invariant coordinates attached to a fibre marking. -/
public def htwoInv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHTwoPresentation phi).invariants ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
    B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared

/-- The chosen geometric splitting of the degree-two Wang sequence. -/
public def htwoSplit (S : (circleMappingTorusHTwoPresentation phi).Section) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ]
      (circleMappingTorusHTwoPresentation phi).Coinvariants ×
        (circleMappingTorusHTwoPresentation phi).invariants :=
  WangHomologyPresentation.linearEquivOfSection _ S

public theorem circleMappingTorusHTwoAddEquiv_apply {B : CuspMonodromyCoordinates phi}
    (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 2 (CircleMappingTorus phi)) :
    S.circleMappingTorusHTwoAddEquiv y =
      finFourProdFinTwoLinearEquiv
        (htwoCoinv B (htwoSplit S.degreeTwo y).1, htwoInv B (htwoSplit S.degreeTwo y).2) := rfl


end CircleMappingTorusHomologyBases




end SphereSixComplex
