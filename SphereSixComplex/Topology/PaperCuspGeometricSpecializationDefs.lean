module

public import SphereSixComplex.Topology.GeometricWangSplitting
public import SphereSixComplex.Topology.PaperCuspFinalInclusionAdapter

/-!
# Geometric cusp specialization coordinates: definitions

This file carries the period coordinates of the punctured cusp collar and the two radial
clutching structures.  It is split off from `PaperCuspGeometricSpecialization` so that the
construction of the clutching datum in `PaperCuspRadialClutchingConstruction` can be used to
discharge it there.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

/-! ## The actual period coordinates of the cusp collar

The punctured cusp collar is presented by the additive cover `additiveCuspRadiusCover`, whose
points are pairs `(zeta, s)` with `zeta : ℂ²` an additive period coordinate and `s` a normalized
cusp parameter.  Over a fixed `s` the residual identifications on `zeta` are exactly the two
integral columns of the identity block together with the two columns of the period block at
`N.lift s`, that is, exactly the period lattice of `actualCuspCollarPeriodParameter N s`.  The
fibre of the collar over `s` is therefore *canonically* the additive torus of that parameter, with
no residual `±1` ambiguity: this is what `actualCuspCollarPeriodPoint` records and what the
normalization field of `ActualCuspRadialClutchingData` pins the fibre marking to. -/

/-- The actual period parameter of the punctured cusp collar over the normalized cusp
parameter `s`: the value of the assembled Fuchsian period functions at `N.lift s`. -/
public noncomputable def actualCuspCollarPeriodParameter
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ) :
    SphereSixComplex.Periods.Parameters :=
  SphereSixComplex.Periods.periodValues (assembledFuchsianPeriodFunctions E D).tau
    (assembledFuchsianPeriodFunctions E D).mu (assembledFuchsianPeriodFunctions E D).beta
    (N.lift s)

/-- The point of the punctured cusp collar with additive period coordinate `zeta` over the
normalized cusp parameter `s`.  This is the honest period coordinate of the collar, read off its
additive cover, and it depends on nothing but `W`. -/
public noncomputable def actualCuspCollarPeriodPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {s : ℂ}
    (hs : ‖cuspQ s‖ < W.localWitness.radius) (zeta : ComplexTwoSpace) :
    puncturedLocalCuspQuotient W :=
  Quotient.mk _
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      (Quotient.mk _ ⟨(zeta, s), hs⟩))

/-- The marked fibre coordinate `e` of a radial mapping-torus presentation `total` really is the
actual period coordinate of the collar: the fibre sitting at radius `t` over the base circle
basepoint consists of the collar points with period coordinate `zeta`, and `e` reads off exactly
that `zeta` modulo periods.

This is the cusp analogue of the marking carried by
`SectionSevenAffineCentralBandMarkedTrivialization`, and unlike a bare homeomorphism to a
full-rank torus it admits no `±1` ambiguity: see
`IsActualCuspFiberPeriodCoordinate.fiberCoordinate_unique`. -/
public def IsActualCuspFiberPeriodCoordinate
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    {W : ActualPuncturedCuspCollarWitness N M}
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (total : puncturedLocalCuspQuotient W ≃ₜ
      OpenRadialInterval W.localWitness.radius × CircleMappingTorus phi)
    (t : OpenRadialInterval W.localWitness.radius) {s : ℂ}
    (hs : ‖cuspQ s‖ < W.localWitness.radius)
    (p : SphereSixComplex.Periods.Parameters) (e : F ≃ₜ AdditiveTorus p) : Prop :=
  ∀ (y : F) (zeta : ComplexTwoSpace),
    total.symm (t, finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) y) =
        actualCuspCollarPeriodPoint W hs zeta ↔
      e y = additiveTorusProjection p zeta

/-- The normalization leaves no freedom in the fibre coordinate.  In particular composing a
normalized fibre coordinate with the hyperelliptic involution `-1` of the torus fibre destroys
the normalization, which is exactly what the un-normalized structure failed to prevent. -/
public theorem IsActualCuspFiberPeriodCoordinate.fiberCoordinate_unique
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    {W : ActualPuncturedCuspCollarWitness N M}
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    {total : puncturedLocalCuspQuotient W ≃ₜ
      OpenRadialInterval W.localWitness.radius × CircleMappingTorus phi}
    {t : OpenRadialInterval W.localWitness.radius} {s : ℂ}
    {hs : ‖cuspQ s‖ < W.localWitness.radius}
    {p : SphereSixComplex.Periods.Parameters} {e e' : F ≃ₜ AdditiveTorus p}
    (h : IsActualCuspFiberPeriodCoordinate total t hs p e)
    (h' : IsActualCuspFiberPeriodCoordinate total t hs p e') :
    e = e' := by
  apply Homeomorph.ext
  intro y
  obtain ⟨zeta, hzeta⟩ := Quotient.exists_rep (e y)
  have hy : e y = additiveTorusProjection p zeta := hzeta.symm
  exact hy.trans ((h' y zeta).1 ((h y zeta).2 hy)).symm

/-- A radial fundamental domain for the actual punctured local cusp quotient, including the
identified `M₀` monodromy coordinates on its four-torus fibre, but with the fibre marking left
un-normalized.

This is the shape the datum used to have.  It is retained only so that the two sign
refutations of `PaperCuspGeometricSpecializationProof` can still be stated: the marking it
records is invisible to the hyperelliptic `±1` involution of the torus fibre, so the specialization
equations are *false* when quantified over data of this type.  Use
`ActualCuspRadialClutchingData` instead. -/
public structure UnnormalizedCuspRadialClutchingData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) where
  Fiber : Type
  fiberTopology : TopologicalSpace Fiber
  clutching : let _ := fiberTopology; Fiber ≃ₜ Fiber
  totalHomeomorph : let _ := fiberTopology
    puncturedLocalCuspQuotient W ≃ₜ
      OpenRadialInterval W.localWitness.radius × CircleMappingTorus clutching
  monodromyCoordinates : let _ := fiberTopology
    CuspMonodromyCoordinates clutching
  /-- The fibre named in this structure's summary, recorded rather than left implicit: it is the
  additive four-torus of a full-rank period parameter.  The same three fields appear on
  `AdditiveFourTorusBundleRealization`, which records the identification for the bundle picture. -/
  fiberParameter : SphereSixComplex.Periods.Parameters
  fiberFullRank : SphereSixComplex.Geometry.ComplexTorus.FullRank fiberParameter
  fiberHomeomorph : let _ := fiberTopology
    Fiber ≃ₜ SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus fiberParameter
  fiberMarkingCompatibility : let _ := fiberTopology
    ∀ x : IntegralSingularHomology 1 Fiber,
      (EstablishedTorusHomology.additiveTorusHomologyBasis
          fiberParameter fiberFullRank).degreeOne
          (integralSingularHomologyMap 1 fiberHomeomorph x) =
        monodromyCoordinates.degreeOne x

/-- A radial fundamental domain for the actual punctured local cusp quotient, including the
identified `M₀` monodromy coordinates on its four-torus fibre and, crucially, a normalization
of that fibre marking against the collar's own period coordinates.

The extra fields over `UnnormalizedCuspRadialClutchingData` are what make the datum rigid.
`fiberNormalization` says that the recorded fibre coordinate is the actual additive period
coordinate of the collar (`actualCuspCollarPeriodPoint`), not merely some homeomorphism onto some
full-rank torus, and `fiberMarkingCompatibilityTwo` ties the degree-two marking to the same
coordinate.  Without them the hyperelliptic `±1` involution of the torus fibre is invisible to the
datum and the Section 7 specialization equations are refutable: see
`not_standardA2CuspSpecializationDegreeOneStatement`
and its degree-two counterpart. -/
public structure ActualCuspRadialClutchingData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    extends UnnormalizedCuspRadialClutchingData W where
  /-- The degree-two fibre marking is read off the same period marking as the degree-one one.
  This is the field the `negDegreeTwo` refutation cannot supply: the second compound of `-I` is
  `I`, so the left-hand side is insensitive to the sign of `fiberHomeomorph`. -/
  fiberMarkingCompatibilityTwo : let _ := fiberTopology
    ∀ x : IntegralSingularHomology 2 Fiber,
      (EstablishedTorusHomology.additiveTorusHomologyBasis
          fiberParameter fiberFullRank).degreeTwo
          (integralSingularHomologyMap 2 fiberHomeomorph x) =
        monodromyCoordinates.degreeTwo x
  /-- The normalized cusp parameter of the marked fibre. -/
  markingParameter : ℂ
  /-- The marked fibre lies inside the chosen cusp collar. -/
  markingParameter_mem : ‖cuspQ markingParameter‖ < W.localWitness.radius
  /-- The radial coordinate at which the marked fibre sits. -/
  markingRadius : OpenRadialInterval W.localWitness.radius
  /-- The recorded period parameter is the collar's own period parameter at the marked fibre. -/
  fiberParameter_eq : fiberParameter = actualCuspCollarPeriodParameter N markingParameter
  /-- The normalization: the recorded fibre coordinate is the actual period coordinate of the
  cusp collar.  This is the field the `negDegreeOne` refutation cannot supply. -/
  fiberNormalization : let _ := fiberTopology
    IsActualCuspFiberPeriodCoordinate totalHomeomorph markingRadius markingParameter_mem
      fiberParameter fiberHomeomorph

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex
