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
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

/-- A radial fundamental domain for the actual punctured local cusp quotient, including the
identified `M₀` monodromy coordinates on its four-torus fibre. -/
public structure ActualCuspRadialClutchingData
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

namespace EstablishedActualCuspRadialClutching

/-- Polar coordinates and a fundamental strip for the normalized cusp parameter give the radial
mapping-torus quotient.  Period transport across the strip is the matrix `M₀`. -/
public axiom data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : ActualCuspRadialClutchingData W

end EstablishedActualCuspRadialClutching

namespace ActualCuspRadialClutchingData

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M} (G : ActualCuspRadialClutchingData W)

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

end ActualCuspRadialClutchingData

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
degree one: specialization preserves its two fibre coinvariants and kills the base circle. -/
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
suspensions. -/
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
