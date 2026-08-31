module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianSourceHomologyCompletion
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry
public import SphereSixComplex.Topology.PaperCuspFiniteFiberDegreeOneKilledSection

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
public theorem totalLinearEquivCoinvariantsProdInvariantsOfSection_lift
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (x : P.Invariants) :
    P.totalLinearEquivCoinvariantsProdInvariantsOfSection S (S.lift x) = (0, x) := by
  let e := P.totalLinearEquivCoinvariantsProdInvariantsOfSection S
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
open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

/-- The positive generator of the actual cusp degree-one Wang invariant lattice. -/
public noncomputable def actualCuspPositiveDegreeOneInvariantGenerator
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Invariants := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).symm 1

/-- The specialization-adjusted section lift of the positive invariant generator. -/
public noncomputable def actualCuspSelectedPositiveMeridianClass
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact G.geometricWangSections.degreeOne.lift
    (actualCuspPositiveDegreeOneInvariantGenerator A)

/-- The chosen positive invariant generator has invariant coordinate one. -/
public theorem actualCuspPositiveDegreeOneInvariantGenerator_coordinate
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    degreeOneWangInvariantEquivInteger G
      (actualCuspPositiveDegreeOneInvariantGenerator A) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (degreeOneWangInvariantEquivInteger G).apply_symm_apply 1

/-- The selected positive section class is exactly the third raw degree-one basis class. -/
public theorem actualCuspSelectedPositiveMeridianClass_rawCoordinate
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (actualCuspSelectedPositiveMeridianClass A) = Pi.single (2 : Fin 3) 1 := by
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
        (P.totalLinearEquivCoinvariantsProdInvariantsOfSection
          G.geometricWangSections.degreeOne
          (G.geometricWangSections.degreeOne.lift
            (actualCuspPositiveDegreeOneInvariantGenerator A)))) = _
  rw [P.totalLinearEquivCoinvariantsProdInvariantsOfSection_lift]
  change finTwoProdIntLinearEquiv
      (honeCoinv G.monodromyCoordinates 0,
        honeInv G.monodromyCoordinates
          (actualCuspPositiveDegreeOneInvariantGenerator A)) = _
  rw [map_zero]
  change finTwoProdIntLinearEquiv
      (0, degreeOneWangInvariantEquivInteger G
        (actualCuspPositiveDegreeOneInvariantGenerator A)) = _
  rw [actualCuspPositiveDegreeOneInvariantGenerator_coordinate]
  funext i
  fin_cases i <;> rfl

/-- Equivalently, the inverse raw coordinate map sends the third basis vector to the selected
positive section lift. -/
public theorem actualCuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1) =
      actualCuspSelectedPositiveMeridianClass A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
  rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
  exact (actualCuspSelectedPositiveMeridianClass_rawCoordinate A).symm

/-- A winding-one evaluation on the selected positive section is the sole missing scalar for the
full source character: the resulting three raw basis values are `[12, 0, 1]`. -/
public theorem actualCuspMeridianSourceCircleMap_rawBasisValues_of_selectedPositive_winding_one
    (A : PaperAnalyticData)
    (hmeridian :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
            (actualCuspSelectedPositiveMeridianClass A)) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 3 ↦
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
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
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (0 : Fin 3) 1))) = 12
    rw [hClass]
    dsimp [G, actualCuspFiberCoinvariantHomologyOneBasis,
      Geometry.PaperAnalyticData.actualCuspRadialClutchingData,
      EstablishedActualCuspRadialClutching.data,
      CuspRadialClutchingConstruction.actualCuspRadialClutchingData] at x ⊢
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (cuspMeridianSourceCircleMap
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
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (1 : Fin 3) 1))) = 0
    rw [hClass]
    dsimp [G, actualCuspFiberCoinvariantHomologyOneBasis,
      Geometry.PaperAnalyticData.actualCuspRadialClutchingData,
      EstablishedActualCuspRadialClutching.data,
      CuspRadialClutchingConstruction.actualCuspRadialClutchingData] at x ⊢
    change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (cuspMeridianSourceCircleMap
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
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (2 : Fin 3) 1))) = 1
    rw [actualCuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass]
    exact hmeridian

/-- The exact source homology identity follows from the single selected-section normalization. -/
public theorem actualCuspMeridianSourceCircleMap_homologyCoordinate_of_selectedPositive_winding_one
    (A : PaperAnalyticData)
    (hmeridian :
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
            (actualCuspSelectedPositiveMeridianClass A)) = 1) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply addMonoidHom_ext_of_equiv_pi_single_one
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
  intro i
  have hvalues := congrFun
    (actualCuspMeridianSourceCircleMap_rawBasisValues_of_selectedPositive_winding_one A hmeridian) i
  change actualCuspEllipticDegreeOneRawCoordinate
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single i 1))) = _
  rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
  rw [AddMonoidHom.comp_apply]
  calc
    actualCuspEllipticDegreeOneRawCoordinate (Pi.single i 1) = ![12, 0, 1] i := by
      fin_cases i <;> simp [actualCuspEllipticDegreeOneRawCoordinate]
    _ = StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single i 1))) := hvalues.symm

/-- Thus the full source-coordinate identity is equivalent to one concrete normalization: the
explicit circle map has winding one on the selected positive Wang-section generator. -/
public theorem actualCuspMeridianSourceCircleMap_homologyCoordinate_iff_selectedPositive_winding_one
    (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
          G.geometricWangSections.circleMappingTorusHOneAddEquiv =
        StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
          (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap))) ↔
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
            (actualCuspSelectedPositiveMeridianClass A)) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h
    have hvalue := DFunLike.congr_fun h (actualCuspSelectedPositiveMeridianClass A)
    change actualCuspEllipticDegreeOneRawCoordinate
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv
          (actualCuspSelectedPositiveMeridianClass A)) =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (A.actualCuspMeridianSourceCircleMap)
          (actualCuspSelectedPositiveMeridianClass A)) at hvalue
    rw [actualCuspSelectedPositiveMeridianClass_rawCoordinate] at hvalue
    simpa [actualCuspEllipticDegreeOneRawCoordinate] using hvalue.symm
  · exact actualCuspMeridianSourceCircleMap_homologyCoordinate_of_selectedPositive_winding_one A

end Geometry.PaperAnalyticData

end SphereSixComplex

end
