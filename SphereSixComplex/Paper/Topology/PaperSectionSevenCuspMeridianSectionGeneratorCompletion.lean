module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianSourceHomologyCompletion
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
    (S : P.Section) (x : P.Invariants) :
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

namespace Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization
open EllipticInteriorMarkedCycleData
open EllipticTwoDiscCoverData

/-- The positive generator of the actual cusp degree-one Wang invariant lattice. -/
public noncomputable def cuspPositiveDegreeOneInvariantGenerator
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Invariants := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).symm 1

/-- The specialization-adjusted section lift of the positive invariant generator. -/
public noncomputable def cuspSelectedPositiveMeridianClass
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact G.geometricWangSections.degreeOne.lift
    (cuspPositiveDegreeOneInvariantGenerator A)

/-- The chosen positive invariant generator has invariant coordinate one. -/
public theorem cuspPositiveDegreeOneInvariantGenerator_coordinate
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    degreeOneWangInvariantEquivInteger G
      (cuspPositiveDegreeOneInvariantGenerator A) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).apply_symm_apply 1

/-- The selected positive section has base-circle winding one by its Wang normalization. -/
public theorem cuspSelectedPositiveMeridianClass_baseCircle_winding_one
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection G.clutching)
          (cuspSelectedPositiveMeridianClass A)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let _ : PathConnectedSpace (AdditiveTorus G.fiberParameter) :=
    additiveTorus_pathConnected G.fiberParameter
  let _ : PathConnectedSpace G.Fiber :=
    G.fiberHomeomorph.symm.surjective.pathConnectedSpace
      G.fiberHomeomorph.symm.continuous
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (cuspSelectedPositiveMeridianClass A)) = 1
  rw [SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary.circleMappingTorusBaseCircle_winding_eq_wangBoundary]
  change degreeOneWangInvariantEquivInteger G
      ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
        (cuspSelectedPositiveMeridianClass A)) = 1
  change degreeOneWangInvariantEquivInteger G
      ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
        (G.geometricWangSections.degreeOne.lift
          (cuspPositiveDegreeOneInvariantGenerator A))) = 1
  have hright := DFunLike.congr_fun
    G.geometricWangSections.degreeOne.right_inv
    (cuspPositiveDegreeOneInvariantGenerator A)
  change (circleMappingTorusHOnePresentation G.clutching).totalToInvariants
      (G.geometricWangSections.degreeOne.lift
        (cuspPositiveDegreeOneInvariantGenerator A)) =
    cuspPositiveDegreeOneInvariantGenerator A at hright
  rw [hright, cuspPositiveDegreeOneInvariantGenerator_coordinate]

/-- The selected positive section class is exactly the third raw degree-one basis class. -/
public theorem cuspSelectedPositiveMeridianClass_raw_coordinate
    (A : PaperAnalyticData) :
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
    (A : PaperAnalyticData) :
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

/-- The third raw degree-one basis class has canonical base-circle winding one. -/
public theorem cuspRawDegreeOneThirdBasis_baseCircle_winding_one
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection G.clutching)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (2 : Fin 3) 1))) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection G.clutching)
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single (2 : Fin 3) 1))) = 1
  rw [cuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass]
  exact cuspSelectedPositiveMeridianClass_baseCircle_winding_one A

/-- The actual filling map is an isomorphism on the degree-one Wang coinvariants, without using
the coordinate specialization matrix. -/
public theorem cuspRawDegreeOneFiberSpecialization_bijective
    (A : PaperAnalyticData) (b : puncturedLocalCuspQuotient A.starCuspWitness) :
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
    (actualLocalCuspFillingHomologyOneEquiv A.starCuspWitness
      (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData
        A.starCuspWitness)).toIntLinearEquiv

/-- Once the explicit angular meridian has the negative Wang orientation and the selected section
is killed by specialization, uniqueness in the specialization kernel identifies the selected
positive class with the negative angular meridian. -/
public theorem cuspSelectedPositiveMeridianClass_eq_neg_explicit_of_normalizations
    (A : PaperAnalyticData) (b : puncturedLocalCuspQuotient A.starCuspWitness)
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

/-- The marked source winding follows from three independent geometric normalizations: the
selected section lies in the filling kernel, the explicit angular meridian has negative Wang
orientation, and its negative has positive source winding. -/
public theorem cuspSelectedPositiveMeridianClass_winding_one_of_explicit_normalizations
    (A : PaperAnalyticData) (b : puncturedLocalCuspQuotient A.starCuspWitness)
    (hselected :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      rawDegreeOneTotalSpecialization G (cuspSelectedPositiveMeridianClass A) = 0)
    (hexplicit :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      degreeOneWangInvariantEquivInteger G
          ((circleMappingTorusHOnePresentation G.clutching).totalToInvariants
            (-(cuspMappingTorusMeridianHomologyClass G b))) = 1)
    (hwinding :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
            (-(cuspMappingTorusMeridianHomologyClass G b))) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (cuspSelectedPositiveMeridianClass A)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [cuspSelectedPositiveMeridianClass_eq_neg_explicit_of_normalizations
    A b hselected hexplicit]
  exact hwinding

/-- A winding-one evaluation on the selected positive section is the sole missing scalar for the
full source character: the resulting three raw basis values are `[12, 0, 1]`. -/
public theorem cuspMeridianSourceCircleMap_rawBasisValues_of_selectedPositive_winding_one
    (A : PaperAnalyticData)
    (hmeridian :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
            (cuspSelectedPositiveMeridianClass A)) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 3 ↦
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single i 1)))) = ![12, 0, 1] := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  funext i
  fin_cases i
  · let x := actualCuspFiberCoinvariantHomologyOneBasis A 0
    have hClass :
        G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (0 : Fin 3) 1) =
          integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x := by
      apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
      rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
      exact (actualCuspFiberCoinvariantHomologyOneBasis_inclusion A 0).symm
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (0 : Fin 3) 1))) = 12
    rw [hClass]
    dsimp [G, actualCuspFiberCoinvariantHomologyOneBasis,
      Geometry.PaperAnalyticData.actualCuspRadialClutchingData,
      EstablishedActualCuspRadialClutching.data,
      CuspRadialClutchingConstruction.actualCuspRadialClutchingData] at x ⊢
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (_root_.SphereSixComplex.cuspMeridianSourceCircleMap
            (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))
          (integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion
              (fun _ : Unit ↦ cuspFiberClutching
                (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))) x)) = 12
    rw [cuspMeridianSourceCircleMap_fiber_homology]
    change 12 * G.monodromyCoordinates.degreeOne
      (G.monodromyCoordinates.degreeOne.symm ![1, 0, 0, 0]) 0 = 12
    rw [G.monodromyCoordinates.degreeOne.apply_symm_apply]
    rfl
  · let x := actualCuspFiberCoinvariantHomologyOneBasis A 1
    have hClass :
        G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (1 : Fin 3) 1) =
          integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x := by
      apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
      rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
      exact (actualCuspFiberCoinvariantHomologyOneBasis_inclusion A 1).symm
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (1 : Fin 3) 1))) = 0
    rw [hClass]
    dsimp [G, actualCuspFiberCoinvariantHomologyOneBasis,
      Geometry.PaperAnalyticData.actualCuspRadialClutchingData,
      EstablishedActualCuspRadialClutching.data,
      CuspRadialClutchingConstruction.actualCuspRadialClutchingData] at x ⊢
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (_root_.SphereSixComplex.cuspMeridianSourceCircleMap
            (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))
          (integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion
              (fun _ : Unit ↦ cuspFiberClutching
                (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)))) x)) = 0
    rw [cuspMeridianSourceCircleMap_fiber_homology]
    change 12 * G.monodromyCoordinates.degreeOne
      (G.monodromyCoordinates.degreeOne.symm ![0, 1, 0, 0]) 0 = 0
    rw [G.monodromyCoordinates.degreeOne.apply_symm_apply]
    rfl
  · change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (2 : Fin 3) 1))) = 1
    rw [cuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass]
    exact hmeridian

/-- The exact source homology identity follows from the single selected-section normalization. -/
public theorem cuspMeridianSourceCircleMap_homology_coordinate_of_selectedPositive_winding_one
    (A : PaperAnalyticData)
    (hmeridian :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
            (cuspSelectedPositiveMeridianClass A)) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply addMonoidHom_ext_of_equiv_pi_single_one
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
  intro i
  have hvalues := congrFun
    (cuspMeridianSourceCircleMap_rawBasisValues_of_selectedPositive_winding_one A hmeridian) i
  change cuspEllipticDegreeOneRawCoordinate
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single i 1))) = _
  rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
  rw [AddMonoidHom.comp_apply]
  calc
    cuspEllipticDegreeOneRawCoordinate (Pi.single i 1) = ![12, 0, 1] i := by
      fin_cases i <;> simp [cuspEllipticDegreeOneRawCoordinate]
    _ = StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single i 1))) := hvalues.symm

/-- Thus the full source-coordinate identity is equivalent to one concrete normalization: the
explicit circle map has winding one on the selected positive Wang-section generator. -/
public theorem cuspMeridianSourceCircleMap_homology_coordinate_iff_selectedPositive_winding_one
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
          G.geometricWangSections.circleMappingTorusHOneAddEquiv =
        StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
          (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap))) ↔
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
            (cuspSelectedPositiveMeridianClass A)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h
    have hvalue := DFunLike.congr_fun h (cuspSelectedPositiveMeridianClass A)
    change cuspEllipticDegreeOneRawCoordinate
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv
          (cuspSelectedPositiveMeridianClass A)) =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.cuspMeridianSourceCircleMap)
          (cuspSelectedPositiveMeridianClass A)) at hvalue
    rw [cuspSelectedPositiveMeridianClass_raw_coordinate] at hvalue
    simpa [cuspEllipticDegreeOneRawCoordinate] using hvalue.symm
  · exact cuspMeridianSourceCircleMap_homology_coordinate_of_selectedPositive_winding_one A

end Geometry.PaperAnalyticData

end SphereSixComplex

end
