module

public import SphereSixComplex.Prerequisites.Topology.WangSectionCorrection
public import SphereSixComplex.Paper.Topology.ConstructedA2PhaseSpreadingCompletion
public import SphereSixComplex.Paper.Topology.PaperCuspRadialClutchingConstruction

/-!
# Geometric cusp specialization coordinates

This file fixes the geometric Wang splitting of the radial cusp collar and compares its fibre
coinvariants with the canonical deck basis in degree one and the labelled cellular basis
of the standard periodic `A₂` toric central fibre in degree two.
It then performs the integral basis changes used in the final Section 7 attachment.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspCollar

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup


namespace ActualPuncturedCuspCollarWitness
open _root_.SphereSixComplex.Geometry.CuspCollar
/-- Polar coordinates and a fundamental strip for the normalized cusp parameter give the radial
mapping-torus quotient.  Period transport across the strip is the matrix `M₀`.

The marked fibre is the collar's own fibre over a normalized cusp parameter `markingParameter`
inside the horodisc, and its recorded coordinate is the actual additive period coordinate there
(`fiberNormalization`); the degree-one and degree-two markings are read off that one coordinate.
Producing the marking is the same real-period-coordinate construction used for the central band in
`PaperSectionSevenAffineMarkedBandTrivialization`: lift the contractible base through the
covering, then read the period coordinate on the lifted sheet. -/
public noncomputable def radialClutchingData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : ActualCuspRadialClutchingData W :=
  SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData W

end ActualPuncturedCuspCollarWitness
namespace UnnormalizedCuspRadialClutchingData

open LatticeData LatticeWangAlgebra CuspMonodromyCoinvariants

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M} [HasCuspPhaseSpreading W] (G : UnnormalizedCuspRadialClutchingData W)

/-- The established polar honeycomb and phase-spreading data selected for the radial collar. -/
public noncomputable def radialPhaseSpreadingPackage
    (W : ActualPuncturedCuspCollarWitness N M) [HasCuspPhaseSpreading W] :
    Σ P : PolarHoneycombData M W.localWitness.radius,
      Geometry.CuspStraighteningRetraction.FrozenLocalCuspPhaseSpreadingData N M
        W.localWitness.radius P :=
  cuspPhaseSpreadingData W

/-- The resulting radial deformation retraction onto the standard central fibre. -/
public noncomputable def radialCentralFiberRetractionData
    (W : ActualPuncturedCuspCollarWitness N M) [HasCuspPhaseSpreading W] :
    ActualLocalCuspCentralFiberRetractionData W :=
  Geometry.CuspStraighteningRetraction.actualLocalCuspCentralFiberRetractionData W
    (radialPhaseSpreadingPackage W).1 (radialPhaseSpreadingPackage W).2

/-- Degree-one specialization, transported from the mapping-torus model to cellular coordinates. -/
public noncomputable def specializationHomologyOneMap :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) →ₗ[ℤ] (Fin 2 → ℤ) := by
  let _ := G.fiberTopology
  exact ((actualCuspDeckHomologyOneEquiv W).toAddMonoidHom.comp
    ((integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩).comp
        (integralSingularHomologyEquivOfHomotopyEquiv 1
          (G.totalHomeomorph.toHomotopyEquiv.trans
            (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos))).symm.toAddMonoidHom)).toIntLinearMap

/-- Degree-two specialization, transported from the mapping-torus model to cellular coordinates. -/
public noncomputable def specializationHomologyTwoMap :
    let _ := G.fiberTopology
    IntegralSingularHomology 2 (CircleMappingTorus G.clutching) →ₗ[ℤ] (Fin 4 → ℤ) := by
  let _ := G.fiberTopology
  exact ((actualLocalCuspFillingHomologyTwoEquiv W (radialCentralFiberRetractionData W)).toAddMonoidHom.comp
    ((integralSingularHomologyMap 2
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩).comp
        (integralSingularHomologyEquivOfHomotopyEquiv 2
          (G.totalHomeomorph.toHomotopyEquiv.trans
            (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos))).symm.toAddMonoidHom)).toIntLinearMap

/-- The monodromy-coordinate identification of the degree-one Wang coinvariants. -/
public noncomputable def degreeOneCoinvariantsEquiv :
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let _ := G.fiberTopology
  exact (coinvariantsEquivOfConjugacy G.monodromyCoordinates.degreeOne.toIntLinearEquiv
    (circleMonodromyDifference G.clutching 1).toIntLinearMap mZeroDifference
    G.monodromyCoordinates.degreeOneDifference_conjugacy).trans
      mZeroCoinvariantsEquivIntSquared

/-- The monodromy-coordinate identification of the degree-two Wang coinvariants. -/
public noncomputable def degreeTwoCoinvariantsEquiv :
    let _ := G.fiberTopology
    (circleMappingTorusHTwoPresentation G.clutching).Coinvariants ≃ₗ[ℤ] (Fin 4 → ℤ) := by
  let _ := G.fiberTopology
  exact (coinvariantsEquivOfConjugacy G.monodromyCoordinates.degreeTwo.toIntLinearEquiv
    (circleMonodromyDifference G.clutching 2).toIntLinearMap mZeroExteriorTwoDifference
    G.monodromyCoordinates.degreeTwoDifference_conjugacy).trans
      mZeroExteriorTwoCoinvariantsEquivIntFourth


/-- Remove the contractible radial coordinate from the actual punctured cusp quotient. -/
public noncomputable def totalHomotopyEquiv :
    let _ := G.fiberTopology
    PuncturedLocalCuspQuotient W ≃ₕ CircleMappingTorus G.clutching := by
  let _ := G.fiberTopology
  exact G.totalHomeomorph.toHomotopyEquiv.trans
    (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos)



end UnnormalizedCuspRadialClutchingData

namespace ActualCuspRadialClutchingData

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M} [HasCuspPhaseSpreading W] (G : ActualCuspRadialClutchingData W)

/-- Wang sections corrected by the radial specialization; degree two uses its actual restriction
to the fiber whenever that restriction is bijective. -/
@[irreducible] public noncomputable def geometricWangSections :
    let _ := G.fiberTopology
    CuspGeometricWangSections G.monodromyCoordinates := by
  let _ := G.fiberTopology
  let U := G.toUnnormalizedCuspRadialClutchingData
  let S := _root_.SphereSixComplex.CircleMappingTorusHomologyBases.CuspMonodromyCoordinates.wangSections
    G.monodromyCoordinates
  exact
    { degreeOne := WangHomologyPresentation.correctedSection
        (circleMappingTorusHOnePresentation G.clutching) S.degreeOne
        (UnnormalizedCuspRadialClutchingData.degreeOneCoinvariantsEquiv U)
        (UnnormalizedCuspRadialClutchingData.specializationHomologyOneMap U)
      degreeTwo := WangHomologyPresentation.correctedSectionIfBijective
        (circleMappingTorusHTwoPresentation G.clutching) S.degreeTwo
        (UnnormalizedCuspRadialClutchingData.degreeTwoCoinvariantsEquiv U)
        (UnnormalizedCuspRadialClutchingData.specializationHomologyTwoMap U) }

public theorem geometricWangSections_degreeTwo_of_bijective
    (h : let _ := G.fiberTopology
      Function.Bijective (G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal)) :
    let _ := G.fiberTopology
    G.geometricWangSections.degreeTwo =
      WangHomologyPresentation.correctedSection
        (circleMappingTorusHTwoPresentation G.clutching)
        (_root_.SphereSixComplex.CircleMappingTorusHomologyBases.CuspMonodromyCoordinates.wangSections G.monodromyCoordinates).degreeTwo
        (LinearEquiv.ofBijective (G.specializationHomologyTwoMap.comp
          (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal) h)
        G.specializationHomologyTwoMap := by
  let _ := G.fiberTopology
  unfold geometricWangSections
  exact WangHomologyPresentation.correctedSectionIfBijective_of_bijective
    _ _ _ _ h

public theorem geometricWangSections_degreeTwo_first
    (h : let _ := G.fiberTopology
      Function.Bijective (G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal))
    (x : let _ := G.fiberTopology
      IntegralSingularHomology 2 (CircleMappingTorus G.clutching)) (i : Fin 4) :
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHTwoLinearEquiv x (Fin.castAdd 2 i) =
      G.degreeTwoCoinvariantsEquiv
        ((LinearEquiv.ofBijective (G.specializationHomologyTwoMap.comp
          (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal) h).symm
            (G.specializationHomologyTwoMap x)) i := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let S := _root_.SphereSixComplex.CircleMappingTorusHomologyBases.CuspMonodromyCoordinates.wangSections G.monodromyCoordinates
  let e := LinearEquiv.ofBijective (G.specializationHomologyTwoMap.comp P.coinvariantsToTotal) h
  have he := WangHomologyPresentation.map_eq_correctedSection_coinvariant
    P S.degreeTwo e G.specializationHomologyTwoMap rfl x
  rw [← G.geometricWangSections_degreeTwo_of_bijective h] at he
  have hc : G.degreeTwoCoinvariantsEquiv
      ((P.linearEquivOfSection
        G.geometricWangSections.degreeTwo x).1) =
      G.degreeTwoCoinvariantsEquiv (e.symm (G.specializationHomologyTwoMap x)) := by
    rw [he, e.symm_apply_apply]
  fin_cases i <;> exact congrFun hc _


/-- The specialization-normalized degree-one Wang coordinates for an actual clutching datum. -/
public noncomputable def geometricHomologyOneEquiv :
    IntegralSingularHomology 1 (PuncturedLocalCuspQuotient W) ≃+ (Fin 3 → ℤ) := by
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1
      G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHOneAddEquiv

/-- The specialization-normalized degree-two Wang coordinates for an actual clutching datum. -/
public noncomputable def geometricHomologyTwoEquiv :
    IntegralSingularHomology 2 (PuncturedLocalCuspQuotient W) ≃+ (Fin 6 → ℤ) := by
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2
      G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHTwoAddEquiv

end ActualCuspRadialClutchingData

end Geometry.CuspCollar

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

namespace Geometry.AnalyticData

open CuspCollar
open SphereSixComplex.CircleMappingTorusHomologyBases

variable (A : AnalyticData)

/-- The source-independent radial fundamental-domain theorem specialized to the paper's chosen
cusp witness. -/
public noncomputable def actualCuspRadialClutchingData :
    ActualCuspRadialClutchingData A.starCuspWitness :=
  _root_.SphereSixComplex.Geometry.CuspCollar.ActualPuncturedCuspCollarWitness.radialClutchingData A.starCuspWitness

/-- The paper's selected radial clutching datum is the explicit additive-period construction. -/
public theorem actualCuspRadialClutchingData_eq :
    A.actualCuspRadialClutchingData =
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness := rfl

/-- The paper's selected central-fibre retraction is the radial construction used above. -/
public theorem cuspCentralFiberRetractionData_eq_radial :
    A.cuspCentralFiberRetractionData =
      UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData
        A.starCuspWitness := rfl

end Geometry.AnalyticData

namespace CuspSpecialization

open Geometry Geometry.CuspCollar Geometry.AnalyticData

/-- Projection from the raw degree-one Wang basis to its two fibre coinvariants. -/
public def degreeOneFiberProjection : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := fun i ↦ x (Fin.castAdd 1 i)
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Projection from the raw degree-two Wang basis to its four fibre coinvariants. -/
public def degreeTwoFiberProjection : (Fin 6 → ℤ) →+ (Fin 4 → ℤ) where
  toFun x := fun i ↦ x (Fin.castAdd 2 i)
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- The remaining cellular naturality input, stated as two equalities of homomorphisms in the
explicit finite bases.  The radial coordinates are the constructed additive-period coordinates,
not an arbitrary clutching datum. -/
public structure FiniteBasisNaturality (A : AnalyticData)
    (K : (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) := AddEquiv.refl _) : Prop where
  degreeOne :
    (actualCuspDeckHomologyOneEquiv A.starCuspWitness).toAddMonoidHom.comp
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩) =
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      degreeOneFiberProjection.comp G.geometricHomologyOneEquiv.toAddMonoidHom
  degreeTwo :
    ((actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
      A.cuspCentralFiberRetractionData).trans K).toAddMonoidHom.comp
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩) =
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      degreeTwoFiberProjection.comp G.geometricHomologyTwoEquiv.toAddMonoidHom



end CuspSpecialization

end SphereSixComplex
