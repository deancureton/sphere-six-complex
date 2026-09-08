module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationDefs
public import SphereSixComplex.Topology.ConstructedA2PhaseSpreadingCompletion
public import SphereSixComplex.Topology.PaperCuspRadialClutchingConstruction

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

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup


namespace EstablishedActualCuspRadialClutching

/-- Polar coordinates and a fundamental strip for the normalized cusp parameter give the radial
mapping-torus quotient.  Period transport across the strip is the matrix `M₀`.

The marked fibre is the collar's own fibre over a normalized cusp parameter `markingParameter`
inside the horodisc, and its recorded coordinate is the actual additive period coordinate there
(`fiberNormalization`); the degree-one and degree-two markings are read off that one coordinate.
Producing the marking is the same real-period-coordinate construction used for the central band in
`PaperSectionSevenAffineMarkedBandTrivialization`: lift the contractible base through the
covering, then read the period coordinate on the lifted sheet. -/
public noncomputable def data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : ActualCuspRadialClutchingData W :=
  SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData W

end EstablishedActualCuspRadialClutching

namespace UnnormalizedCuspRadialClutchingData

open LatticeData LatticeWangAlgebra Topology.PaperCuspSpecializationAlgebra

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
  exact ((actualLocalCuspFillingHomologyOneEquiv W (radialCentralFiberRetractionData W)).toAddMonoidHom.comp
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

/-- Adjust a Wang section by its coinvariant component so that a given map kills its lift. -/
public noncomputable def geometricSectionInMapKernel
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L) :
    P.GeometricSection where
  lift := S.lift - P.coinvariantsToTotal.comp
    (c.symm.toLinearMap.comp (f.comp S.lift))
  rightInverse := by
    apply LinearMap.ext
    intro z
    change P.totalToInvariants
      (S.lift z - P.coinvariantsToTotal (c.symm (f (S.lift z)))) = z
    rw [map_sub, P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero, sub_zero]
    exact DFunLike.congr_fun S.rightInverse z

/-- The adjusted Wang section is killed by a map whose restriction to coinvariants is the
specified coordinate equivalence. -/
public theorem geometricSectionInMapKernel_lift
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L)
    (h : f.comp P.coinvariantsToTotal = c.toLinearMap) :
    f.comp (geometricSectionInMapKernel P S c f).lift = 0 := by
  apply LinearMap.ext
  intro z
  change f (S.lift z - P.coinvariantsToTotal (c.symm (f (S.lift z)))) = 0
  rw [map_sub]
  have hi := DFunLike.congr_fun h (c.symm (f (S.lift z)))
  simp only [LinearMap.coe_comp, Function.comp_apply] at hi
  rw [hi]
  change f (S.lift z) - c (c.symm (f (S.lift z))) = 0
  rw [c.apply_symm_apply, sub_self]

/-- In the splitting defined by the adjusted section, a map is exactly its coinvariant
coordinate. -/
public theorem geometricSectionInMapKernel_map_eq_coinvariant
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L)
    (h : f.comp P.coinvariantsToTotal = c.toLinearMap) (x : Total) :
    f x = c ((P.totalLinearEquivCoinvariantsProdInvariantsOfSection
      (geometricSectionInMapKernel P S c f) x).1) := by
  let K := geometricSectionInMapKernel P S c f
  let T := P.totalLinearEquivCoinvariantsProdInvariantsOfSection K
  let y := T x
  have hx : x = T.symm y := (T.symm_apply_apply x).symm
  rw [hx, T.apply_symm_apply]
  have hinv : T.symm y = P.coinvariantsToTotal y.1 + K.lift y.2 := by rfl
  rw [hinv]
  rw [map_add]
  have hi := DFunLike.congr_fun h y.1
  simp only [LinearMap.coe_comp, Function.comp_apply] at hi
  have hs := DFunLike.congr_fun
    (geometricSectionInMapKernel_lift P S c f h) y.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] at hs
  rw [hi, hs, add_zero]
  rfl

/-- The projective Wang sections for an unnormalized clutching datum. -/
public noncomputable def geometricWangSections :
    let _ := G.fiberTopology
    CuspGeometricWangSections G.monodromyCoordinates := by
  let _ := G.fiberTopology
  exact CircleMappingTorusHomologyBases.EstablishedCircleMappingTorusGeometricSections.sections
    G.monodromyCoordinates

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
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHOneAddEquiv

/-- The geometrically split raw degree-two Wang coordinates: four fibre coinvariants followed by
the two invariant suspension classes. -/
public noncomputable def geometricHomologyTwoEquiv :
    IntegralSingularHomology 2 (puncturedLocalCuspQuotient W) ≃+ (Fin 6 → ℤ) := by
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHTwoAddEquiv

end UnnormalizedCuspRadialClutchingData

namespace ActualCuspRadialClutchingData

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M} [HasCuspPhaseSpreading W] (G : ActualCuspRadialClutchingData W)

/-- Wang sections normalized so that their suspension summands lie in the kernel of the radial
specialization map. -/
@[irreducible] public noncomputable def geometricWangSections :
    let _ := G.fiberTopology
    CuspGeometricWangSections G.monodromyCoordinates := by
  let _ := G.fiberTopology
  let U := G.toUnnormalizedCuspRadialClutchingData
  let S := CircleMappingTorusHomologyBases.EstablishedCircleMappingTorusGeometricSections.sections
    G.monodromyCoordinates
  exact
    { degreeOne := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel
        (circleMappingTorusHOnePresentation G.clutching) S.degreeOne
        (UnnormalizedCuspRadialClutchingData.degreeOneCoinvariantsEquiv U)
        (UnnormalizedCuspRadialClutchingData.specializationHomologyOneMap U)
      degreeTwo := UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel
        (circleMappingTorusHTwoPresentation G.clutching) S.degreeTwo
        (UnnormalizedCuspRadialClutchingData.degreeTwoCoinvariantsEquiv U)
        (UnnormalizedCuspRadialClutchingData.specializationHomologyTwoMap U) }

/-- The specialization-normalized degree-one Wang coordinates for an actual clutching datum. -/
public noncomputable def geometricHomologyOneEquiv :
    IntegralSingularHomology 1 (puncturedLocalCuspQuotient W) ≃+ (Fin 3 → ℤ) := by
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1
      G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv).trans
    G.geometricWangSections.circleMappingTorusHOneAddEquiv

/-- The specialization-normalized degree-two Wang coordinates for an actual clutching datum. -/
public noncomputable def geometricHomologyTwoEquiv :
    IntegralSingularHomology 2 (puncturedLocalCuspQuotient W) ≃+ (Fin 6 → ℤ) := by
  let _ := G.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2
      G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv).trans
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

end Geometry.PaperAnalyticData

namespace Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData

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
public structure FiniteBasisNaturality (A : PaperAnalyticData) : Prop where
  degreeOne :
    (actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
      A.cuspCentralFiberRetractionData).toAddMonoidHom.comp
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩) =
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      degreeOneFiberProjection.comp G.geometricHomologyOneEquiv.toAddMonoidHom
  degreeTwo :
    (actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
      A.cuspCentralFiberRetractionData).toAddMonoidHom.comp
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩) =
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      degreeTwoFiberProjection.comp G.geometricHomologyTwoEquiv.toAddMonoidHom

/-- The exact remaining geometric calculation, reduced to the integer matrix entries on the
standard Wang generators.  Unlike `FiniteBasisNaturality`, this asks only for thirty scalar
equalities: `3 × 2` in degree one and `6 × 4` in degree two. -/
public structure FiniteGeneratorSpecializationMatrix (A : PaperAnalyticData) : Prop where
  degreeOne (j : Fin 3) (i : Fin 2) :
    actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
          ((SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
              A.starCuspWitness).geometricHomologyOneEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 3 → ℤ) (Fin.castAdd 1 i)
  degreeTwo (j : Fin 6) (i : Fin 4) :
    actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩
          ((SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
              A.starCuspWitness).geometricHomologyTwoEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 6 → ℤ) (Fin.castAdd 2 i)

/-- The residual cellular calculation on the fibre-coinvariant generators.  The Wang suspension
generators are excluded: the chosen sections lie in the kernel of radial specialization by
construction. -/
public structure FiniteFiberGeneratorSpecializationMatrix (A : PaperAnalyticData) : Prop where
  degreeOne (j i : Fin 2) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap
        ((circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal
          (G.degreeOneCoinvariantsEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 2 → ℤ) i
  degreeTwo (j i : Fin 4) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyTwoMap
        ((circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) i =
      (Pi.single j 1 : Fin 4 → ℤ) i

end Geometry.CuspPuncturedCollarBridge.EstablishedStandardA2CuspSpecialization

end SphereSixComplex
