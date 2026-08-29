module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationDefs
public import SphereSixComplex.Topology.PaperCuspRadialClutchingConstruction

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
  {W : ActualPuncturedCuspCollarWitness N M} (G : UnnormalizedCuspRadialClutchingData W)

/-- The established polar honeycomb and phase-spreading data selected for the radial collar. -/
public noncomputable def radialPhaseSpreadingPackage
    (W : ActualPuncturedCuspCollarWitness N M) :
    Σ P : PolarHoneycombData M W.localWitness.radius,
      Geometry.CuspStraighteningRetraction.FrozenLocalCuspPhaseSpreadingData N M
        W.localWitness.radius P :=
  Classical.choice
    (StandardInfiniteA2ToricModel.Established.polarHoneycombPhaseSpreadingPackage N M
      W.localWitness.radius W.localWitness.radius_pos)

/-- The resulting radial deformation retraction onto the standard central fibre. -/
public noncomputable def radialCentralFiberRetractionData
    (W : ActualPuncturedCuspCollarWitness N M) :
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
  {W : ActualPuncturedCuspCollarWitness N M} (G : ActualCuspRadialClutchingData W)

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

/-- The twenty fibre-generator coefficients not forced by the Wang splitting. -/
public axiom establishedFiniteFiberGeneratorSpecializationMatrix
    (A : PaperAnalyticData) : FiniteFiberGeneratorSpecializationMatrix A

private theorem addMonoidHom_ext_of_equiv_pi_single_one
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (f g : G →+ H)
    (h : ∀ i, f (e.symm (Pi.single i 1)) = g (e.symm (Pi.single i 1))) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  let y := e x
  have hx : x = e.symm y := by simp [y]
  rw [hx]
  apply Pi.single_induction (M := fun _ : Fin n ↦ ℤ)
    (p := fun z ↦ f (e.symm z) = g (e.symm z)) y
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      classical
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    calc
      f (e.symm (Pi.single i z)) =
          f (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [hz]
      _ = z • f (e.symm (Pi.single i 1)) := by rw [map_zsmul, map_zsmul]
      _ = z • g (e.symm (Pi.single i 1)) := congrArg (z • ·) (h i)
      _ = g (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [map_zsmul, map_zsmul]
      _ = g (e.symm (Pi.single i z)) := by rw [hz]

private theorem specializationHomologyOneMap_comp_coinvariants (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap.comp
        (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal =
      G.degreeOneCoinvariantsEquiv.toLinearMap := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let c := G.degreeOneCoinvariantsEquiv
  have hhom : (G.specializationHomologyOneMap.comp P.coinvariantsToTotal).toAddMonoidHom =
      c.toLinearMap.toAddMonoidHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one c.toAddEquiv
    intro j
    funext i
    change G.specializationHomologyOneMap
        (P.coinvariantsToTotal (c.symm (Pi.single j 1))) i = _
    simpa using (establishedFiniteFiberGeneratorSpecializationMatrix A).degreeOne j i
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hhom x

private theorem specializationHomologyTwoMap_comp_coinvariants (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyTwoMap.comp
        (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal =
      G.degreeTwoCoinvariantsEquiv.toLinearMap := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let c := G.degreeTwoCoinvariantsEquiv
  have hhom : (G.specializationHomologyTwoMap.comp P.coinvariantsToTotal).toAddMonoidHom =
      c.toLinearMap.toAddMonoidHom := by
    apply addMonoidHom_ext_of_equiv_pi_single_one c.toAddEquiv
    intro j
    funext i
    change G.specializationHomologyTwoMap
        (P.coinvariantsToTotal (c.symm (Pi.single j 1))) i = _
    simpa using (establishedFiniteFiberGeneratorSpecializationMatrix A).degreeTwo j i
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hhom x

private theorem specializationHomologyOneMap_eq_projection (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyOneMap.toAddMonoidHom =
      degreeOneFiberProjection.comp
        G.geometricWangSections.circleMappingTorusHOneAddEquiv.toAddMonoidHom := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  let S :=
    _root_.SphereSixComplex.CircleMappingTorusHomologyBases.EstablishedCircleMappingTorusGeometricSections.sections
      G.monodromyCoordinates
  let c := G.degreeOneCoinvariantsEquiv
  let f := G.specializationHomologyOneMap
  apply AddMonoidHom.ext
  intro x
  have hx :=
    UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel_map_eq_coinvariant P
      S.degreeOne c f
    (specializationHomologyOneMap_comp_coinvariants A) x
  change f x = _
  rw [hx]
  unfold ActualCuspRadialClutchingData.geometricWangSections
  change c _ = degreeOneFiberProjection
    (CircleMappingTorusHomologyBases.finTwoProdIntLinearEquiv (c _, _))
  funext i
  fin_cases i <;> rfl

private theorem specializationHomologyTwoMap_eq_projection (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    G.specializationHomologyTwoMap.toAddMonoidHom =
      degreeTwoFiberProjection.comp
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.toAddMonoidHom := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let S :=
    _root_.SphereSixComplex.CircleMappingTorusHomologyBases.EstablishedCircleMappingTorusGeometricSections.sections
      G.monodromyCoordinates
  let c := G.degreeTwoCoinvariantsEquiv
  let f := G.specializationHomologyTwoMap
  apply AddMonoidHom.ext
  intro x
  have hx :=
    UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel_map_eq_coinvariant P
      S.degreeTwo c f
    (specializationHomologyTwoMap_comp_coinvariants A) x
  change f x = _
  rw [hx]
  unfold ActualCuspRadialClutchingData.geometricWangSections
  change c _ = degreeTwoFiberProjection
    (CircleMappingTorusHomologyBases.finFourProdFinTwoLinearEquiv (c _, _))
  funext i
  fin_cases i <;> rfl

/-- Cellular-to-singular naturality for the explicit periodic `A₂` cellular basis. -/
public theorem finiteBasisNaturality (A : PaperAnalyticData) : FiniteBasisNaturality A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  refine ⟨?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
    have h := DFunLike.congr_fun (specializationHomologyOneMap_eq_projection A)
      (e x)
    change actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ (e.symm (e x))) =
      degreeOneFiberProjection (G.geometricWangSections.circleMappingTorusHOneAddEquiv (e x)) at h
    rw [e.symm_apply_apply] at h
    simpa [G, e, ActualCuspRadialClutchingData.geometricHomologyOneEquiv,
      Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using h
  · apply AddMonoidHom.ext
    intro x
    let _ := G.fiberTopology
    let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
    have h := DFunLike.congr_fun (specializationHomologyTwoMap_eq_projection A)
      (e x)
    change actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData A.starCuspWitness)
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ (e.symm (e x))) =
      degreeTwoFiberProjection (G.geometricWangSections.circleMappingTorusHTwoAddEquiv (e x)) at h
    rw [e.symm_apply_apply] at h
    simpa [G, e, ActualCuspRadialClutchingData.geometricHomologyTwoEquiv,
      Geometry.PaperAnalyticData.cuspCentralFiberRetractionData_eq_radial] using h

/-- The former thirty-entry input, now derived from the twenty fibre entries and the
specialization-normalized Wang sections. -/
public theorem establishedFiniteGeneratorSpecializationMatrix
    (A : PaperAnalyticData) : FiniteGeneratorSpecializationMatrix A := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  constructor
  · intro j i
    have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeOne
      (G.geometricHomologyOneEquiv.symm (Pi.single j 1))
    simpa [G, degreeOneFiberProjection] using congrFun h i
  · intro j i
    have h := DFunLike.congr_fun (finiteBasisNaturality A).degreeTwo
      (G.geometricHomologyTwoEquiv.symm (Pi.single j 1))
    simpa [G, degreeTwoFiberProjection] using congrFun h i

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
public theorem degreeOne
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 1
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyOneEquiv x (Fin.castAdd 1 i) := by
  rw [A.actualCuspRadialClutchingData_eq]
  exact DFunLike.congr_fun (finiteBasisNaturality A).degreeOne x

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
public theorem degreeTwo
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    actualLocalCuspFillingHomologyTwoEquiv A.starCuspWitness
        A.cuspCentralFiberRetractionData
        (integralSingularHomologyMap 2
          ⟨puncturedLocalCuspToFilling A.starCuspWitness,
            puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ x) =
      fun i ↦ A.actualCuspRadialClutchingData.geometricHomologyTwoEquiv x (Fin.castAdd 2 i) := by
  rw [A.actualCuspRadialClutchingData_eq]
  exact DFunLike.congr_fun (finiteBasisNaturality A).degreeTwo x

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
