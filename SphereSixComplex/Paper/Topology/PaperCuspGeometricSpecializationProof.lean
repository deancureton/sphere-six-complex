module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

/-!
# Regression test: the cusp clutching datum must be normalized

The Section 7 specialization equations
`EstablishedStandardA2CuspSpecialization.degreeOne` and `.degreeTwo` have a left-hand side that
does not mention the clutching datum at all.  They are therefore only sound if the datum is
*rigid*.  This file proves that the un-normalized shape of the datum,
`UnnormalizedCuspRadialClutchingData`, is **not** rigid, so that quantifying either equation over
every `G : UnnormalizedCuspRadialClutchingData W` yields a false statement.  This is the reason
`ActualCuspRadialClutchingData` carries the normalization fields
`fiberMarkingCompatibilityTwo`, `fiberParameter_eq` and `fiberNormalization`; **do not remove
them.**

*Degree two.*  `UnnormalizedCuspRadialClutchingData` records a fibre marking
`monodromyCoordinates : CuspMonodromyCoordinates clutching` whose degree-two component
`degreeTwo` is constrained *only* by `degreeTwo_monodromy`, an equation that is invariant under
negation because `mZeroExteriorTwoMatrix *ᵥ (-v) = -(mZeroExteriorTwoMatrix *ᵥ v)`.  Hence
`UnnormalizedCuspRadialClutchingData.negDegreeTwo` is a second, equally valid, un-normalized datum
for the same `W`, and `geometricHomologyTwoEquiv_negDegreeTwo` shows that it reverses the sign of
exactly the four degree-two coinvariant coordinates that the equation pins down.  This refutes the
degree-two statement: `not_standardA2CuspSpecializationDegreeTwoStatement`.

*Degree one.*  The degree-one marking `degreeOne` is additionally tied to the standard period
basis by `fiberMarkingCompatibility`, but that constraint is not rigid either.  Negation of a
period torus is a descended affine automorphism whose integral lattice map is `-1`
(`negDescendedAffineTorusAutomorphism`), so composing the marking homeomorphism with it produces
a second un-normalized datum `UnnormalizedCuspRadialClutchingData.negDegreeOne` whose degree-one
marking is the negative of the original and which still satisfies `fiberMarkingCompatibility`.
Since `-1` commutes with the cusp monodromy matrix `M₀`, `degreeOne_monodromy` survives as well.
This refutes the degree-one statement: `not_standardA2CuspSpecializationDegreeOneStatement`.

Both refutations take an un-normalized datum as an input. They show that either overbroad
universal specialization statement would make the type of un-normalized data empty: see
`isEmpty_unnormalizedCuspRadialClutchingData_of_degreeOneStatement` and
`isEmpty_unnormalizedCuspRadialClutchingData_of_degreeTwoStatement`.

## The gate

Neither construction survives the normalization.  `negDegreeTwo` cannot supply
`fiberMarkingCompatibilityTwo` because the second compound of `-I` is `I`, so the torus basis does
not see the sign it reverses: `not_degreeTwoMarkingCompatible_negDegreeTwo`.  `negDegreeOne`
cannot supply `fiberNormalization` because the actual period coordinate of the collar is pinned
pointwise, and a normalized fibre coordinate is unique
(`IsActualCuspFiberPeriodCoordinate.fiberCoordinate_unique`):
`not_isActualCuspFiberPeriodCoordinate_neg`.  Both are stated below against a genuine normalized
datum, so they fail as soon as anybody weakens the normalization.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex

namespace CircleMappingTorusHomologyBases

open LatticeData LatticeWangAlgebra Topology.PaperCuspSpecializationAlgebra

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






/-- The degree-one coinvariant coordinates attached to a fibre marking. -/
public def honeCoinv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHOnePresentation phi).Coinvariants ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (coinvariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
    B.degreeOneDifference_conjugacy).trans mZeroCoinvariantsEquivIntSquared

/-- The degree-one invariant coordinate attached to a fibre marking. -/
public def honeInv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHOnePresentation phi).invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
    (circleMonodromyDifference phi 0).toIntLinearMap 0
    B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt

/-- The chosen geometric splitting of the degree-one Wang sequence. -/
public def honeSplit (S : (circleMappingTorusHOnePresentation phi).Section) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃ₗ[ℤ]
      (circleMappingTorusHOnePresentation phi).Coinvariants ×
        (circleMappingTorusHOnePresentation phi).invariants :=
  WangHomologyPresentation.linearEquivOfSection _ S

public theorem circleMappingTorusHOneAddEquiv_apply {B : CuspMonodromyCoordinates phi}
    (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 1 (CircleMappingTorus phi)) :
    S.circleMappingTorusHOneAddEquiv y =
      finTwoProdIntLinearEquiv
        (honeCoinv B (honeSplit S.degreeOne y).1, honeInv B (honeSplit S.degreeOne y).2) := rfl





end CircleMappingTorusHomologyBases

/-! ## The gate: neither refutation survives the normalization

Both constructions above are stated for `UnnormalizedCuspRadialClutchingData` because they no
longer produce an `ActualCuspRadialClutchingData`: the normalization fields cannot be filled in.
The two theorems below make that failure explicit, each measured against a genuine normalized
datum, so they break immediately if anybody weakens the normalization. -/



end SphereSixComplex
