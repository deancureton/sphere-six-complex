module

public import SphereSixComplex.Topology.GeometricWangSplitting
public import SphereSixComplex.Topology.PaperCuspFinalInclusionAdapter

/-!
# Geometric cusp specialization coordinates

This file fixes the geometric Wang splitting of the radial cusp collar and compares its fibre
coinvariants with the labelled cellular basis of the standard periodic `A₂` toric central fibre.
It then performs the integral basis changes used in the final Section 7 attachment.
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

namespace EstablishedActualCuspRadialClutching

/-- Polar coordinates and a fundamental strip for the normalized cusp parameter give the radial
mapping-torus quotient.  Period transport across the strip is the matrix `M₀`.

The marked fibre is the collar's own fibre over a normalized cusp parameter `markingParameter`
inside the horodisc, and its recorded coordinate is the actual additive period coordinate there
(`fiberNormalization`); the degree-one and degree-two markings are read off that one coordinate.
Producing the marking is the same real-period-coordinate construction used for the central band in
`PaperSectionSevenAffineMarkedBandTrivialization`: lift the contractible base through the
covering, then read the period coordinate on the lifted sheet. -/
public axiom data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : ActualCuspRadialClutchingData W

end EstablishedActualCuspRadialClutching

namespace UnnormalizedCuspRadialClutchingData

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M} (G : UnnormalizedCuspRadialClutchingData W)

/-- The canonical singular-prism suspension sections for this clutching map. -/
public noncomputable def geometricWangSections :
    let _ := G.fiberTopology
    CuspGeometricWangSections G.monodromyCoordinates := by
  letI := G.fiberTopology
  exact EstablishedCircleMappingTorusGeometricSections.sections G.monodromyCoordinates

/-- Remove the contractible radial coordinate from the actual punctured cusp quotient. -/
public noncomputable def totalHomotopyEquiv :
    let _ := G.fiberTopology
    puncturedLocalCuspQuotient W ≃ₕ CircleMappingTorus G.clutching := by
  let _ := G.fiberTopology
  exact G.totalHomeomorph.toHomotopyEquiv.trans
    (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos)

/-- The geometrically split raw degree-one Wang coordinates: two fibre coinvariants followed by
the base circle. -/
public noncomputable def geometricHomologyOneEquiv :
    IntegralSingularHomology 1 (puncturedLocalCuspQuotient W) ≃+ (Fin 3 → ℤ) := by
  letI := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHOneAddEquiv

/-- The geometrically split raw degree-two Wang coordinates: four fibre coinvariants followed by
the two invariant suspension classes. -/
public noncomputable def geometricHomologyTwoEquiv :
    IntegralSingularHomology 2 (puncturedLocalCuspQuotient W) ≃+ (Fin 6 → ℤ) := by
  letI := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHTwoAddEquiv

end UnnormalizedCuspRadialClutchingData

end Geometry.CuspPuncturedCollarBridge

/-! ## The integral basis changes used by Section 7 -/

/-- Change from the raw `(coinvariant₀, coinvariant₁, meridian)` basis to the Section 7 cusp
basis. -/
public def cuspSectionSevenOneCoordinateChange : (Fin 3 → ℤ) ≃+ (Fin 3 → ℤ) where
  toFun x := ![-4 * x 2 + x 0 - x 1, -3 * x 2 + x 0 - x 1,
    -12 * x 2 + 4 * x 0 - 3 * x 1]
  invFun y := ![-3 * y 0 + y 2, -4 * y 1 + y 2, -y 0 + y 1]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  left_inv x := by funext i; fin_cases i <;> simp <;> ring
  right_inv y := by funext i; fin_cases i <;> simp <;> ring

/-- In the changed degree-one basis, the raw specialization projection is the negative of the
last two rows of the Section 7 boundary matrix. -/
public theorem cuspSectionSevenOneCoordinateChange_specialization (x : Fin 3 → ℤ) :
    (fun i : Fin 2 ↦ x (Fin.castAdd 1 i)) =
      fun i ↦ -sectionSevenFirstBoundaryHom (cuspSectionSevenOneCoordinateChange x)
        (Fin.natAdd 1 i) := by
  funext i
  fin_cases i <;>
    simp [cuspSectionSevenOneCoordinateChange, sectionSevenFirstBoundaryHom,
      sectionSevenFirstBoundaryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Change from the raw four coinvariants followed by two suspension classes to the Section 7
degree-two cusp basis. -/
public def cuspSectionSevenTwoCoordinateChange : (Fin 6 → ℤ) ≃+ (Fin 6 → ℤ) where
  toFun x := ![x 4, x 5, -x 0, -x 1, -x 2, x 3]
  invFun y := ![-y 2, -y 3, -y 4, y 5, y 0, y 1]
  map_add' x y := by funext i; fin_cases i <;> simp <;> abel
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv y := by funext i; fin_cases i <;> simp

/-- In the changed degree-two basis, the raw specialization projection is the negative of the
last four rows of the normalized Section 7 map. -/
public theorem cuspSectionSevenTwoCoordinateChange_specialization (x : Fin 6 → ℤ) :
    (fun i : Fin 4 ↦ x (Fin.castAdd 2 i)) =
      fun i ↦ -sectionSevenMayerVietorisFinalTwoHom
        (cuspSectionSevenTwoCoordinateChange x) (Fin.natAdd 2 i) := by
  funext i
  fin_cases i <;>
    simp [cuspSectionSevenTwoCoordinateChange, sectionSevenMayerVietorisFinalTwoHom,
      sectionSevenMayerVietorisFinalTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.CircleMappingTorusHomologyBases

variable (A : PaperAnalyticData)

/-- The source-independent radial fundamental-domain theorem specialized to the paper's chosen
cusp witness. -/
public noncomputable def actualCuspRadialClutchingData :
    ActualCuspRadialClutchingData A.starCuspWitness :=
  EstablishedActualCuspRadialClutching.data A.starCuspWitness

end Geometry.PaperAnalyticData

namespace Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

/-- Cellular-to-singular naturality for the paper's selected periodic `A₂` cusp marking in
degree one: specialization preserves its two fibre coinvariants and kills the base circle.

The left-hand side does not mention the clutching datum, so this equation is only sound because
`ActualCuspRadialClutchingData` is *normalized*: `fiberNormalization` pins the fibre marking to
the collar's own period coordinates.  Do not weaken that field.  If the datum is replaced by the
un-normalized `UnnormalizedCuspRadialClutchingData`, this equation becomes false — the fibre
marking may be composed with the hyperelliptic `±1` involution of the torus fibre, which reverses
exactly the two coordinates pinned here.  The refutation is
`not_standardA2CuspSpecializationDegreeOneStatement`,
kept as a permanent regression test in `PaperCuspGeometricSpecializationProof`. -/
public axiom degreeOne
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyOneEquiv x (Fin.castAdd 1 i)

/-- Cellular-to-singular naturality for the paper's selected periodic `A₂` cusp marking in
degree two: specialization preserves its four fibre coinvariants and kills the two invariant
suspensions.

As in degree one the left-hand side does not mention the clutching datum, so this equation is
only sound because `ActualCuspRadialClutchingData` is *normalized*.  Here it is
`fiberMarkingCompatibilityTwo` that does the work: it ties the degree-two marking to the same
period marking as the degree-one one.  Do not weaken that field.  Over the un-normalized
`UnnormalizedCuspRadialClutchingData` the degree-two marking is constrained only by
`degreeTwo_monodromy`, which is invariant under negation, and the equation becomes false; the
refutation is
`not_standardA2CuspSpecializationDegreeTwoStatement`,
kept as a permanent regression test in `PaperCuspGeometricSpecializationProof`. -/
public axiom degreeTwo
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv x (Fin.castAdd 2 i)

end Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.CircleMappingTorusHomologyBases

variable (A : PaperAnalyticData)

/-- The corresponding dimensionally correct realization of the paper's cusp collar. -/
public noncomputable def actualCuspCollarRadialMappingTorusRealization :
    A.CuspCollarRadialMappingTorusRealization where
  radius := A.starCuspWitness.localWitness.radius
  radius_pos := A.starCuspWitness.localWitness.radius_pos
  Fiber := A.actualCuspRadialClutchingData.Fiber
  fiberTopology := A.actualCuspRadialClutchingData.fiberTopology
  clutching := A.actualCuspRadialClutchingData.clutching
  totalHomeomorph := A.actualCuspRadialClutchingData.totalHomeomorph
  monodromyCoordinates := A.actualCuspRadialClutchingData.monodromyCoordinates

/-- Raw geometrically split coordinates on the actual cusp collar. -/
public noncomputable def actualCuspRawHomologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 3 → ℤ) := by
  exact A.actualCuspRadialClutchingData.geometricHomologyOneEquiv

public noncomputable def actualCuspRawHomologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) := by
  exact A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv

/-- The actual cusp collar bases normalized for the final Section 7 attachment. -/
public noncomputable def actualCuspSectionSevenHomologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 3 → ℤ) :=
  A.actualCuspRawHomologyOneEquiv.trans cuspSectionSevenOneCoordinateChange

public noncomputable def actualCuspSectionSevenHomologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+ (Fin 6 → ℤ) :=
  A.actualCuspRawHomologyTwoEquiv.trans cuspSectionSevenTwoCoordinateChange

/-- Replace only the cusp fields of any local basis package by the controlled geometric bases. -/
public noncomputable def withActualGeometricCuspBases
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := A.actualCuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := B.ellipticInteriorOne
  cuspCollarTwo := A.actualCuspSectionSevenHomologyTwoEquiv
  ellipticInteriorTwo := B.ellipticInteriorTwo

/-- Build the local basis package from the elliptic interior alone.

The cusp collar's own degree-one and degree-two bases are already available geometrically, so the
elliptic interior's are the only ones the package still has to be given.  `withActualGeometricCuspBases`
says the same thing but needs a package to start from; this one does not. -/
public noncomputable def sectionSevenCollarInteriorHomologyBasesOfEllipticInterior
    (ellipticOne : IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ))
    (ellipticTwo : IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := A.actualCuspSectionSevenHomologyOneEquiv
  ellipticInteriorOne := ellipticOne
  cuspCollarTwo := A.actualCuspSectionSevenHomologyTwoEquiv
  ellipticInteriorTwo := ellipticTwo

/-- The package built from the elliptic interior already carries the geometric cusp bases. -/
public theorem withActualGeometricCuspBases_ofEllipticInterior
    (ellipticOne : IntegralSingularHomology 1
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 1 → ℤ))
    (ellipticTwo : IntegralSingularHomology 2
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ≃+
      (Fin 2 → ℤ)) :
    A.withActualGeometricCuspBases
        (A.sectionSevenCollarInteriorHomologyBasesOfEllipticInterior ellipticOne ellipticTwo) =
      A.sectionSevenCollarInteriorHomologyBasesOfEllipticInterior ellipticOne ellipticTwo :=
  rfl

/-- The actual cusp inclusion has the degree-one and degree-two coordinates required by the
final Section 7 attachment. -/
public theorem actualCuspFillingInclusionCoordinates
    (B : A.SectionSevenCollarInteriorHomologyBases) :
    A.ActualCuspFillingInclusionCoordinates (A.withActualGeometricCuspBases B) where
  degreeOne x := by
    change actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 1
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    rw [EstablishedStandardA2CuspSpecialization.degreeOne A x]
    exact cuspSectionSevenOneCoordinateChange_specialization
      (A.actualCuspRawHomologyOneEquiv x)
  degreeTwo x := by
    change actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
          (integralSingularHomologyMap 2
            ⟨puncturedLocalCuspToFilling A.starCuspWitness,
              puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) = _
    rw [EstablishedStandardA2CuspSpecialization.degreeTwo A x]
    exact cuspSectionSevenTwoCoordinateChange_specialization
      (A.actualCuspRawHomologyTwoEquiv x)

end Geometry.PaperAnalyticData

end SphereSixComplex
