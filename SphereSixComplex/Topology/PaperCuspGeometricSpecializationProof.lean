module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization

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

section TorusNegation

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization

variable (p : SphereSixComplex.Periods.Parameters)

public theorem continuous_neg_additiveTorus :
    Continuous (fun q : AdditiveTorus p ↦ -q) :=
  continuous_quot_lift _ (continuous_quot_mk.comp continuous_neg)

/-- Negation of a period torus, as a self-homeomorphism. -/
public def additiveTorusNegHomeomorph : AdditiveTorus p ≃ₜ AdditiveTorus p where
  toFun q := -q
  invFun q := -q
  left_inv q := neg_neg q
  right_inv q := neg_neg q
  continuous_toFun := continuous_neg_additiveTorus p
  continuous_invFun := continuous_neg_additiveTorus p

/-- Negation of a period torus, as a descended affine automorphism whose integral lattice map
is `-1`.  It is this automorphism that makes the degree-one fibre marking of a cusp radial
clutching datum non-rigid. -/
public def negDescendedAffineTorusAutomorphism : DescendedAffineTorusAutomorphism p where
  latticeMap := LinearEquiv.neg ℤ
  lift := AddEquiv.neg ComplexTwoSpace
  lift_period n := by
    show -periodVector p n = periodVector p (-n)
    exact ((periodHom p).map_neg n).symm
  translation := 0
  map := ⟨fun q ↦ -q, continuous_neg_additiveTorus p⟩
  map_mk z := by
    show -(Quotient.mk _ z : AdditiveTorus p) = (Quotient.mk _ (-z) : AdditiveTorus p) + 0
    rw [add_zero, additiveTorus_mk_neg]

/-- In the standard period basis, negation of the torus acts on first homology by `-1`. -/
public theorem additiveTorusHomologyBasis_degreeOne_neg (hfull : FullRank p)
    (x : IntegralSingularHomology 1 (AdditiveTorus p)) :
    (EstablishedTorusHomology.additiveTorusHomologyBasis p hfull).degreeOne
        (integralSingularHomologyMap 1 (negDescendedAffineTorusAutomorphism p).map x) =
      -(EstablishedTorusHomology.additiveTorusHomologyBasis p hfull).degreeOne x :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality p hfull
    (negDescendedAffineTorusAutomorphism p)).1 x

/-- Composing a fibre marking homeomorphism with negation of the period torus reverses the
degree-one period marking it induces.  This is the whole content of the degree-one sign
ambiguity. -/
public theorem additiveTorusHomologyBasis_degreeOne_comp_neg
    {F : Type} [TopologicalSpace F] (hfull : FullRank p) (e : F ≃ₜ AdditiveTorus p)
    (x : IntegralSingularHomology 1 F) :
    (EstablishedTorusHomology.additiveTorusHomologyBasis p hfull).degreeOne
        (integralSingularHomologyMap 1 (e.trans (additiveTorusNegHomeomorph p)) x) =
      -(EstablishedTorusHomology.additiveTorusHomologyBasis p hfull).degreeOne
        (integralSingularHomologyMap 1 e x) := by
  have hcomp :
      (⟨e.trans (additiveTorusNegHomeomorph p),
          (e.trans (additiveTorusNegHomeomorph p)).continuous⟩ : C(F, AdditiveTorus p)) =
        (negDescendedAffineTorusAutomorphism p).map.comp ⟨e, e.continuous⟩ := rfl
  show (EstablishedTorusHomology.additiveTorusHomologyBasis p hfull).degreeOne
      (integralSingularHomologyMap 1
        (⟨e.trans (additiveTorusNegHomeomorph p),
          (e.trans (additiveTorusNegHomeomorph p)).continuous⟩ : C(F, AdditiveTorus p)) x) = _
  rw [hcomp, integralSingularHomologyMap_comp]
  exact additiveTorusHomologyBasis_degreeOne_neg p hfull _

end TorusNegation

namespace CircleMappingTorusHomologyBases

open LatticeData LatticeWangAlgebra Topology.PaperCuspSpecializationAlgebra

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}

/-- Reverse the sign of the degree-two fibre marking of a cusp monodromy coordinate system. -/
public def CuspMonodromyCoordinates.negDegreeTwo (B : CuspMonodromyCoordinates phi) :
    CuspMonodromyCoordinates phi where
  degreeZero := B.degreeZero
  degreeOne := B.degreeOne
  degreeTwo := B.degreeTwo.trans (AddEquiv.neg _)
  degreeZero_monodromy := B.degreeZero_monodromy
  degreeOne_monodromy := B.degreeOne_monodromy
  degreeTwo_monodromy x := by
    show -B.degreeTwo (integralSingularHomologyMap 2 phi x) = _
    rw [B.degreeTwo_monodromy x]
    show _ = mZeroExteriorTwoMatrix *ᵥ (-B.degreeTwo x)
    rw [Matrix.mulVec_neg]

public theorem coinvariantsEquivOfConjugacy_apply_mk {A C : Type*} [AddCommGroup A]
    [AddCommGroup C] (e : A ≃ₗ[ℤ] C) (d : A →ₗ[ℤ] A) (D : C →ₗ[ℤ] C)
    (h : e.toLinearMap.comp d = D.comp e.toLinearMap) (x : A) :
    coinvariantsEquivOfConjugacy e d D h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

/-- The degree-two coinvariant coordinates attached to a fibre marking. -/
public def htwoCoinv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHTwoPresentation phi).Coinvariants ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (coinvariantsEquivOfConjugacy B.degreeTwo.toIntLinearEquiv
    (circleMonodromyDifference phi 2).toIntLinearMap mZeroExteriorTwoDifference
    B.degreeTwoDifference_conjugacy).trans mZeroExteriorTwoCoinvariantsEquivIntFourth

/-- The degree-two invariant coordinates attached to a fibre marking. -/
public def htwoInv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHTwoPresentation phi).Invariants ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
    B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared

/-- The chosen geometric splitting of the degree-two Wang sequence. -/
public def htwoSplit (S : (circleMappingTorusHTwoPresentation phi).GeometricSection) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ]
      (circleMappingTorusHTwoPresentation phi).Coinvariants ×
        (circleMappingTorusHTwoPresentation phi).Invariants :=
  WangHomologyPresentation.totalLinearEquivCoinvariantsProdInvariantsOfSection _ S

public theorem circleMappingTorusHTwoAddEquiv_apply {B : CuspMonodromyCoordinates phi}
    (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 2 (CircleMappingTorus phi)) :
    S.circleMappingTorusHTwoAddEquiv y =
      finFourProdFinTwoLinearEquiv
        (htwoCoinv B (htwoSplit S.degreeTwo y).1, htwoInv B (htwoSplit S.degreeTwo y).2) := rfl

public theorem htwoInv_negDegreeTwo (B : CuspMonodromyCoordinates phi) :
    htwoInv B.negDegreeTwo = htwoInv B := rfl

public theorem sections_negDegreeTwo_degreeTwo (B : CuspMonodromyCoordinates phi) :
    (EstablishedCircleMappingTorusGeometricSections.sections B.negDegreeTwo).degreeTwo =
      (EstablishedCircleMappingTorusGeometricSections.sections B).degreeTwo := rfl

public theorem htwoCoinv_negDegreeTwo (B : CuspMonodromyCoordinates phi)
    (w : (circleMappingTorusHTwoPresentation phi).Coinvariants) :
    htwoCoinv B.negDegreeTwo w = -htwoCoinv B w := by
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    show mZeroExteriorTwoCoinvariantsEquivIntFourth
          (Submodule.Quotient.mk (-B.degreeTwo x)) =
        -mZeroExteriorTwoCoinvariantsEquivIntFourth
          (Submodule.Quotient.mk (B.degreeTwo x))
    rw [Submodule.Quotient.mk_neg, map_neg]

/-- Reversing the sign of the degree-two fibre marking reverses the sign of the four
degree-two coinvariant coordinates, leaving the two invariant suspension coordinates alone. -/
public theorem circleMappingTorusHTwoAddEquiv_negDegreeTwo_castAdd
    (B : CuspMonodromyCoordinates phi)
    (y : IntegralSingularHomology 2 (CircleMappingTorus phi)) (i : Fin 4) :
    (EstablishedCircleMappingTorusGeometricSections.sections
          B.negDegreeTwo).circleMappingTorusHTwoAddEquiv y (Fin.castAdd 2 i) =
      -(EstablishedCircleMappingTorusGeometricSections.sections
          B).circleMappingTorusHTwoAddEquiv y (Fin.castAdd 2 i) := by
  rw [circleMappingTorusHTwoAddEquiv_apply, circleMappingTorusHTwoAddEquiv_apply,
    sections_negDegreeTwo_degreeTwo, htwoInv_negDegreeTwo, htwoCoinv_negDegreeTwo]
  fin_cases i <;> rfl

/-- Reverse the sign of the degree-one fibre marking of a cusp monodromy coordinate system. -/
public def CuspMonodromyCoordinates.negDegreeOne (B : CuspMonodromyCoordinates phi) :
    CuspMonodromyCoordinates phi where
  degreeZero := B.degreeZero
  degreeOne := B.degreeOne.trans (AddEquiv.neg _)
  degreeTwo := B.degreeTwo
  degreeZero_monodromy := B.degreeZero_monodromy
  degreeOne_monodromy x := by
    show -B.degreeOne (integralSingularHomologyMap 1 phi x) =
      SphereSixComplex.LatticeData.M₀ *ᵥ (-B.degreeOne x)
    rw [B.degreeOne_monodromy x, Matrix.mulVec_neg]
  degreeTwo_monodromy := B.degreeTwo_monodromy

/-- The degree-one coinvariant coordinates attached to a fibre marking. -/
public def honeCoinv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHOnePresentation phi).Coinvariants ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (coinvariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
    B.degreeOneDifference_conjugacy).trans mZeroCoinvariantsEquivIntSquared

/-- The degree-one invariant coordinate attached to a fibre marking. -/
public def honeInv (B : CuspMonodromyCoordinates phi) :
    (circleMappingTorusHOnePresentation phi).Invariants ≃ₗ[ℤ] ℤ :=
  (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
    (circleMonodromyDifference phi 0).toIntLinearMap 0
    B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt

/-- The chosen geometric splitting of the degree-one Wang sequence. -/
public def honeSplit (S : (circleMappingTorusHOnePresentation phi).GeometricSection) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃ₗ[ℤ]
      (circleMappingTorusHOnePresentation phi).Coinvariants ×
        (circleMappingTorusHOnePresentation phi).Invariants :=
  WangHomologyPresentation.totalLinearEquivCoinvariantsProdInvariantsOfSection _ S

public theorem circleMappingTorusHOneAddEquiv_apply {B : CuspMonodromyCoordinates phi}
    (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 1 (CircleMappingTorus phi)) :
    S.circleMappingTorusHOneAddEquiv y =
      finTwoProdIntLinearEquiv
        (honeCoinv B (honeSplit S.degreeOne y).1, honeInv B (honeSplit S.degreeOne y).2) := rfl

public theorem honeInv_negDegreeOne (B : CuspMonodromyCoordinates phi) :
    honeInv B.negDegreeOne = honeInv B := rfl

public theorem sections_negDegreeOne_degreeOne (B : CuspMonodromyCoordinates phi) :
    (EstablishedCircleMappingTorusGeometricSections.sections B.negDegreeOne).degreeOne =
      (EstablishedCircleMappingTorusGeometricSections.sections B).degreeOne := rfl

public theorem honeCoinv_negDegreeOne (B : CuspMonodromyCoordinates phi)
    (w : (circleMappingTorusHOnePresentation phi).Coinvariants) :
    honeCoinv B.negDegreeOne w = -honeCoinv B w := by
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    show mZeroCoinvariantsEquivIntSquared (Submodule.Quotient.mk (-B.degreeOne x)) =
      -mZeroCoinvariantsEquivIntSquared (Submodule.Quotient.mk (B.degreeOne x))
    rw [Submodule.Quotient.mk_neg, map_neg]

/-- Reversing the sign of the degree-one fibre marking reverses the sign of the two degree-one
coinvariant coordinates, leaving the base-circle coordinate alone. -/
public theorem circleMappingTorusHOneAddEquiv_negDegreeOne_castAdd
    (B : CuspMonodromyCoordinates phi)
    (y : IntegralSingularHomology 1 (CircleMappingTorus phi)) (i : Fin 2) :
    (EstablishedCircleMappingTorusGeometricSections.sections
          B.negDegreeOne).circleMappingTorusHOneAddEquiv y (Fin.castAdd 1 i) =
      -(EstablishedCircleMappingTorusGeometricSections.sections
          B).circleMappingTorusHOneAddEquiv y (Fin.castAdd 1 i) := by
  rw [circleMappingTorusHOneAddEquiv_apply, circleMappingTorusHOneAddEquiv_apply,
    sections_negDegreeOne_degreeOne, honeInv_negDegreeOne, honeCoinv_negDegreeOne]
  fin_cases i <;> rfl

end CircleMappingTorusHomologyBases

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The same geometric radial clutching data with the sign of its degree-two fibre marking
reversed.  Nothing in `UnnormalizedCuspRadialClutchingData` constrains that sign: only the
degree-one marking is tied to the period basis by `fiberMarkingCompatibility`.

This does *not* produce an `ActualCuspRadialClutchingData`: it cannot supply
`fiberMarkingCompatibilityTwo`, which is exactly what the normalization added.  See
`not_degreeTwoMarkingCompatible_negDegreeTwo`. -/
public def UnnormalizedCuspRadialClutchingData.negDegreeTwo
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : UnnormalizedCuspRadialClutchingData W) :
    UnnormalizedCuspRadialClutchingData W := by
  letI := G.fiberTopology
  exact
    { Fiber := G.Fiber
      fiberTopology := G.fiberTopology
      clutching := G.clutching
      totalHomeomorph := G.totalHomeomorph
      monodromyCoordinates := G.monodromyCoordinates.negDegreeTwo
      fiberParameter := G.fiberParameter
      fiberFullRank := G.fiberFullRank
      fiberHomeomorph := G.fiberHomeomorph
      fiberMarkingCompatibility := G.fiberMarkingCompatibility }

/-- The sign-reversed marking changes the raw degree-two coinvariant coordinates by a sign. -/
public theorem geometricHomologyTwoEquiv_negDegreeTwo
    {W : ActualPuncturedCuspCollarWitness N M} (G : UnnormalizedCuspRadialClutchingData W)
    (x : IntegralSingularHomology 2 (puncturedLocalCuspQuotient W)) (i : Fin 4) :
    G.negDegreeTwo.geometricHomologyTwoEquiv x (Fin.castAdd 2 i) =
      -G.geometricHomologyTwoEquiv x (Fin.castAdd 2 i) := by
  let _ := G.fiberTopology
  exact circleMappingTorusHTwoAddEquiv_negDegreeTwo_castAdd G.monodromyCoordinates
    (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv x) i

/-- The same geometric radial clutching data with the sign of its degree-one fibre marking
reversed.  The marking compatibility with the period basis is preserved because the marking
homeomorphism is composed with negation of the period torus, whose integral lattice map is
`-1`, and `-1` commutes with the cusp monodromy matrix `M₀`.

This does *not* produce an `ActualCuspRadialClutchingData`: composing the fibre coordinate with
the hyperelliptic involution destroys `fiberNormalization`, which is exactly what the
normalization added.  See `not_isActualCuspFiberPeriodCoordinate_neg`. -/
public def UnnormalizedCuspRadialClutchingData.negDegreeOne
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : UnnormalizedCuspRadialClutchingData W) :
    UnnormalizedCuspRadialClutchingData W := by
  letI := G.fiberTopology
  exact
    { Fiber := G.Fiber
      fiberTopology := G.fiberTopology
      clutching := G.clutching
      totalHomeomorph := G.totalHomeomorph
      monodromyCoordinates := G.monodromyCoordinates.negDegreeOne
      fiberParameter := G.fiberParameter
      fiberFullRank := G.fiberFullRank
      fiberHomeomorph := G.fiberHomeomorph.trans (additiveTorusNegHomeomorph G.fiberParameter)
      fiberMarkingCompatibility := by
        intro _ x
        show (EstablishedTorusHomology.additiveTorusHomologyBasis G.fiberParameter
              G.fiberFullRank).degreeOne
            (integralSingularHomologyMap 1
              (G.fiberHomeomorph.trans (additiveTorusNegHomeomorph G.fiberParameter)) x) =
          -G.monodromyCoordinates.degreeOne x
        rw [additiveTorusHomologyBasis_degreeOne_comp_neg, G.fiberMarkingCompatibility x] }

/-- The sign-reversed degree-one marking changes the raw degree-one coinvariant coordinates by
a sign. -/
public theorem geometricHomologyOneEquiv_negDegreeOne
    {W : ActualPuncturedCuspCollarWitness N M} (G : UnnormalizedCuspRadialClutchingData W)
    (x : IntegralSingularHomology 1 (puncturedLocalCuspQuotient W)) (i : Fin 2) :
    G.negDegreeOne.geometricHomologyOneEquiv x (Fin.castAdd 1 i) =
      -G.geometricHomologyOneEquiv x (Fin.castAdd 1 i) := by
  let _ := G.fiberTopology
  exact circleMappingTorusHOneAddEquiv_negDegreeOne_castAdd G.monodromyCoordinates
    (integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv x) i

/-- The false overbroad degree-one statement obtained by quantifying over every *un-normalized*
clutching datum. -/
public def StandardA2CuspSpecializationDegreeOneStatement : Prop :=
  ∀ {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (G : UnnormalizedCuspRadialClutchingData W)
    (x : IntegralSingularHomology 1 (puncturedLocalCuspQuotient W)),
      actualLocalCuspFillingHomologyOneEquiv W R
          (integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
        fun i ↦ G.geometricHomologyOneEquiv x (Fin.castAdd 1 i)

/-- The degree-one specialization equation is refuted by the sign ambiguity of the degree-one
fibre marking. -/
public theorem not_standardA2CuspSpecializationDegreeOneStatement
    {W : ActualPuncturedCuspCollarWitness N M}
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (G : UnnormalizedCuspRadialClutchingData W) :
    ¬ StandardA2CuspSpecializationDegreeOneStatement := by
  intro h
  set x := G.geometricHomologyOneEquiv.symm (fun _ ↦ 1) with hx
  have hG := h W R G x
  have hG' := h W R G.negDegreeOne x
  rw [hG] at hG'
  have hi := congrFun hG' (0 : Fin 2)
  rw [geometricHomologyOneEquiv_negDegreeOne] at hi
  have hval : G.geometricHomologyOneEquiv x (Fin.castAdd 1 (0 : Fin 2)) = 1 := by
    rw [hx, AddEquiv.apply_symm_apply]
  rw [hval] at hi
  omega

/-- The false overbroad degree-two statement obtained by quantifying over every *un-normalized*
clutching datum. -/
public def StandardA2CuspSpecializationDegreeTwoStatement : Prop :=
  ∀ {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (G : UnnormalizedCuspRadialClutchingData W)
    (x : IntegralSingularHomology 2 (puncturedLocalCuspQuotient W)),
      actualLocalCuspFillingHomologyTwoEquiv W R
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x) =
        fun i ↦ G.geometricHomologyTwoEquiv x (Fin.castAdd 2 i)

/-- The degree-two specialization equation is refuted by the sign ambiguity of the degree-two
fibre marking: its left-hand side does not mention the clutching data, while its right-hand side
does, and the clutching data is not rigid. -/
public theorem not_standardA2CuspSpecializationDegreeTwoStatement
    {W : ActualPuncturedCuspCollarWitness N M}
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (G : UnnormalizedCuspRadialClutchingData W) :
    ¬ StandardA2CuspSpecializationDegreeTwoStatement := by
  intro h
  set x := G.geometricHomologyTwoEquiv.symm (fun _ ↦ 1) with hx
  have hG := h W R G x
  have hG' := h W R G.negDegreeTwo x
  rw [hG] at hG'
  have hi := congrFun hG' (0 : Fin 4)
  rw [geometricHomologyTwoEquiv_negDegreeTwo] at hi
  have hval : G.geometricHomologyTwoEquiv x (Fin.castAdd 2 (0 : Fin 4)) = 1 := by
    rw [hx, AddEquiv.apply_symm_apply]
  rw [hval] at hi
  omega

/-- If the overbroad degree-one specialization equation held, no punctured cusp collar witness
carrying a central-fibre retraction could carry an un-normalized radial clutching datum, hence
none could carry a normalized one either. -/
public theorem isEmpty_unnormalizedCuspRadialClutchingData_of_degreeOneStatement
    (h : StandardA2CuspSpecializationDegreeOneStatement)
    {W : ActualPuncturedCuspCollarWitness N M}
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IsEmpty (UnnormalizedCuspRadialClutchingData W) :=
  ⟨fun G ↦ not_standardA2CuspSpecializationDegreeOneStatement R G h⟩

/-- The degree-two counterpart of
`isEmpty_unnormalizedCuspRadialClutchingData_of_degreeOneStatement`. -/
public theorem isEmpty_unnormalizedCuspRadialClutchingData_of_degreeTwoStatement
    (h : StandardA2CuspSpecializationDegreeTwoStatement)
    {W : ActualPuncturedCuspCollarWitness N M}
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    IsEmpty (UnnormalizedCuspRadialClutchingData W) :=
  ⟨fun G ↦ not_standardA2CuspSpecializationDegreeTwoStatement R G h⟩

/-! ## The gate: neither refutation survives the normalization

Both constructions above are stated for `UnnormalizedCuspRadialClutchingData` because they no
longer produce an `ActualCuspRadialClutchingData`: the normalization fields cannot be filled in.
The two theorems below make that failure explicit, each measured against a genuine normalized
datum, so they break immediately if anybody weakens the normalization. -/

/-- The degree-two refutation stops applying.  `negDegreeTwo` keeps the fibre coordinate and
reverses only the degree-two marking, so it cannot satisfy
`ActualCuspRadialClutchingData.fiberMarkingCompatibilityTwo`: negation of the fibre coordinate
would not help either, because the second compound of `-I` is `I`. -/
public theorem not_degreeTwoMarkingCompatible_negDegreeTwo
    {W : ActualPuncturedCuspCollarWitness N M} (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    ¬ ∀ x : IntegralSingularHomology 2 G.Fiber,
        (EstablishedTorusHomology.additiveTorusHomologyBasis
            G.fiberParameter G.fiberFullRank).degreeTwo
            (integralSingularHomologyMap 2 G.fiberHomeomorph x) =
          G.monodromyCoordinates.negDegreeTwo.degreeTwo x := by
  intro _ h
  set x := G.monodromyCoordinates.degreeTwo.symm (fun _ ↦ 1) with hx
  have hval : G.monodromyCoordinates.degreeTwo x = fun _ ↦ 1 := by
    rw [hx, AddEquiv.apply_symm_apply]
  have hneg : G.monodromyCoordinates.degreeTwo x = -G.monodromyCoordinates.degreeTwo x :=
    (G.fiberMarkingCompatibilityTwo x).symm.trans (h x)
  have hi : (1 : ℤ) = -1 := by
    have h0 : G.monodromyCoordinates.degreeTwo x (0 : Fin 6) =
        -G.monodromyCoordinates.degreeTwo x (0 : Fin 6) := congrFun hneg 0
    rwa [hval] at h0
  omega

/-- The degree-one refutation stops applying.  `negDegreeOne` composes the fibre coordinate with
the hyperelliptic involution of the torus fibre, and a normalized fibre coordinate is unique, so
the composite cannot itself be a period coordinate of the collar. -/
public theorem not_isActualCuspFiberPeriodCoordinate_neg
    {W : ActualPuncturedCuspCollarWitness N M} (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    ¬ IsActualCuspFiberPeriodCoordinate G.totalHomeomorph G.markingRadius
        G.markingParameter_mem G.fiberParameter
        (G.fiberHomeomorph.trans (additiveTorusNegHomeomorph G.fiberParameter)) := by
  intro _ h
  have heq := G.fiberNormalization.fiberCoordinate_unique h
  set x := G.monodromyCoordinates.degreeOne.symm (fun _ ↦ 1) with hx
  have hval : G.monodromyCoordinates.degreeOne x = fun _ ↦ 1 := by
    rw [hx, AddEquiv.apply_symm_apply]
  have hneg : G.monodromyCoordinates.degreeOne x = -G.monodromyCoordinates.degreeOne x := by
    calc G.monodromyCoordinates.degreeOne x
        = (EstablishedTorusHomology.additiveTorusHomologyBasis
            G.fiberParameter G.fiberFullRank).degreeOne
            (integralSingularHomologyMap 1
              (G.fiberHomeomorph.trans (additiveTorusNegHomeomorph G.fiberParameter)) x) := by
          rw [← heq]
          exact (G.fiberMarkingCompatibility x).symm
      _ = -G.monodromyCoordinates.degreeOne x := by
          rw [additiveTorusHomologyBasis_degreeOne_comp_neg, G.fiberMarkingCompatibility x]
  have hi : (1 : ℤ) = -1 := by
    have h0 : G.monodromyCoordinates.degreeOne x (0 : Fin 4) =
        -G.monodromyCoordinates.degreeOne x (0 : Fin 4) := congrFun hneg 0
    rwa [hval] at h0
  omega

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex
