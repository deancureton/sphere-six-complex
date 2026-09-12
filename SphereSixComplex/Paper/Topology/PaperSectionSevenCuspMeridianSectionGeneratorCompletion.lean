module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry
public import SphereSixComplex.Paper.Topology.PaperCuspFiniteFiberDegreeOneKilledSection
public import SphereSixComplex.Paper.Topology.PaperCuspMarkedFiberAngularVanishingProof
public import SphereSixComplex.Prerequisites.Topology.IdentityPointMappingTorusWindingBoundary

/-!
# The selected positive cusp meridian section

The specialization-adjusted Wang section has a canonically normalized invariant generator.  This
file identifies its lift with the third raw degree-one basis class and shows that the complete
source-circle homology coordinate reduces to its single winding evaluation.  The two fibre
evaluations are supplied by the explicit fibre character.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix Topology

namespace SphereSixComplex

open CircleMappingTorusHomologyBases
open Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily Geometry.CuspRadialClutchingConstruction
open Periods

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- A geometric section lift has zero residual coordinate and its prescribed invariant
coordinate. -/
public theorem linearEquivOfSection_lift
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.Section) (x : P.invariants) :
    P.linearEquivOfSection S (S.lift x) = (0, x) := by
  let e := P.linearEquivOfSection S
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change S.lift x = P.coinvariantsToTotal 0 + S.lift x
  rw [map_zero, zero_add]

/-- A map injective on the Wang coinvariant subgroup has at most one zero-mapped lift of any
fixed invariant class. -/
public theorem eq_of_totalToInvariants_eq_of_map_eq_zero
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    {L : Type*} [AddCommGroup L] (f : Total →ₗ[ℤ] L)
    (hf : Function.Injective (f.comp P.coinvariantsToTotal))
    {x y : Total} (hinvariant : P.totalToInvariants x = P.totalToInvariants y)
    (hx : f x = 0) (hy : f y = 0) : x = y := by
  have hdifference : P.totalToInvariants (x - y) = 0 := by
    rw [map_sub, hinvariant, sub_self]
  obtain ⟨q, hq⟩ := (P.exact_coinvariantsToTotal_totalToInvariants (x - y)).mp hdifference
  have hmap : (f.comp P.coinvariantsToTotal) q =
      (f.comp P.coinvariantsToTotal) 0 := by
    simp only [LinearMap.comp_apply, map_zero]
    rw [hq, map_sub, hx, hy, sub_self]
  have hqzero : q = 0 := hf hmap
  rw [hqzero, map_zero] at hq
  exact sub_eq_zero.mp hq.symm

end WangHomologyPresentation

namespace Geometry.AnalyticData

open CuspCollar
open CuspCollar.CuspFiberSpecializationNormalization
open EllipticInteriorMarkedCycleData
open EllipticTwoDiscCoverData

/-- The positive generator of the actual cusp degree-one Wang invariant lattice. -/
public noncomputable def cuspPositiveDegreeOneInvariantGenerator
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).invariants := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).symm 1

/-- The specialization-adjusted section lift of the positive invariant generator. -/
public noncomputable def cuspSelectedPositiveMeridianClass
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact G.geometricWangSections.degreeOne.lift
    (cuspPositiveDegreeOneInvariantGenerator A)

/-- The chosen positive invariant generator has invariant coordinate one. -/
public theorem cuspPositiveDegreeOneInvariantGenerator_coordinate
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    degreeOneWangInvariantEquivInteger G
      (cuspPositiveDegreeOneInvariantGenerator A) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).apply_symm_apply 1


/-- The selected positive section class is exactly the third raw degree-one basis class. -/
public theorem cuspSelectedPositiveMeridianClass_raw_coordinate
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (cuspSelectedPositiveMeridianClass A) = Pi.single (2 : Fin 3) 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  change G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (G.geometricWangSections.degreeOne.lift
        ((degreeOneWangInvariantEquivInteger G).symm 1)) = _
  rw [circleMappingTorusHOneAddEquiv_apply]
  change finTwoProdIntLinearEquiv
      ((honeCoinv G.monodromyCoordinates).prodCongr
        (honeInv G.monodromyCoordinates)
        (P.linearEquivOfSection
          G.geometricWangSections.degreeOne
          (G.geometricWangSections.degreeOne.lift
            (cuspPositiveDegreeOneInvariantGenerator A)))) = _
  rw [P.linearEquivOfSection_lift]
  change finTwoProdIntLinearEquiv
      (honeCoinv G.monodromyCoordinates 0,
        honeInv G.monodromyCoordinates
          (cuspPositiveDegreeOneInvariantGenerator A)) = _
  rw [map_zero]
  change finTwoProdIntLinearEquiv
      (0, degreeOneWangInvariantEquivInteger G
        (cuspPositiveDegreeOneInvariantGenerator A)) = _
  rw [cuspPositiveDegreeOneInvariantGenerator_coordinate]
  funext i
  fin_cases i <;> rfl

/-- Equivalently, the inverse raw coordinate map sends the third basis vector to the selected
positive section lift. -/
public theorem cuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass
    (A : AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1) =
      cuspSelectedPositiveMeridianClass A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
  rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
  exact (cuspSelectedPositiveMeridianClass_raw_coordinate A).symm


/-- The actual filling map is an isomorphism on the degree-one Wang coinvariants, without using
the coordinate specialization matrix. -/
public theorem cuspRawDegreeOneFiberSpecialization_bijective
    (A : AnalyticData) (b : PuncturedLocalCuspQuotient A.starCuspWitness) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    Function.Bijective (rawDegreeOneFiberSpecialization G) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  obtain ⟨S, hS⟩ := actualCuspDegreeOne_section G b
  exact WangHomologyPresentation.coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
    P S (rawDegreeOneTotalSpecialization G)
    (rawDegreeOneTotalSpecialization_surjective G b) hS G.degreeOneCoinvariantsEquiv
    (actualCuspDeckHomologyOneEquiv A.starCuspWitness).toIntLinearEquiv

/-- Once the explicit angular meridian has the negative Wang orientation and the selected section
is killed by specialization, uniqueness in the specialization kernel identifies the selected
positive class with the negative angular meridian. -/
public theorem cuspSelectedPositiveMeridianClass_eq_neg_explicit_of_normalizations
    (A : AnalyticData) (b : PuncturedLocalCuspQuotient A.starCuspWitness)
    (hselected :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      rawDegreeOneTotalSpecialization G (cuspSelectedPositiveMeridianClass A) = 0)
    (hexplicit :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      degreeOneWangInvariantEquivInteger G
          ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
            (-(cuspMappingTorusMeridianHomologyClass G b))) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    cuspSelectedPositiveMeridianClass A =
      -(cuspMappingTorusMeridianHomologyClass G b) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  apply P.eq_of_totalToInvariants_eq_of_map_eq_zero
    (rawDegreeOneTotalSpecialization G)
    (cuspRawDegreeOneFiberSpecialization_bijective A b).1
  · apply (degreeOneWangInvariantEquivInteger G).injective
    rw [hexplicit]
    change degreeOneWangInvariantEquivInteger G
        (P.totalToInvariants
          (G.geometricWangSections.degreeOne.lift
            (cuspPositiveDegreeOneInvariantGenerator A))) = 1
    have hright := DFunLike.congr_fun G.geometricWangSections.degreeOne.right_inv
      (cuspPositiveDegreeOneInvariantGenerator A)
    change P.totalToInvariants
        (G.geometricWangSections.degreeOne.lift
          (cuspPositiveDegreeOneInvariantGenerator A)) =
      cuspPositiveDegreeOneInvariantGenerator A at hright
    rw [hright, cuspPositiveDegreeOneInvariantGenerator_coordinate]
  · exact hselected
  · rw [map_neg,
      rawDegreeOneTotalSpecialization_cuspMappingTorusMeridianHomologyClass, neg_zero]





end Geometry.AnalyticData

end SphereSixComplex

end
