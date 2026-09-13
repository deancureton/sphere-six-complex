module

public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorMayerVietorisBases
public import SphereSixComplex.Paper.Topology.FiniteCoverPerfectPairing

@[expose] public section
noncomputable section
open AlgebraicTopology Set
namespace SphereSixComplex.Geometry.AnalyticData.EllipticHomologyGeneratorAlignment
open EllipticFilling Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Topology.FiniteCoverPerfectPairing
variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

public def reducedFibersToUnion (k : ℕ) :=
  (IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide k).comp
    (D.sideHomologyEquiv k).symm.toAddMonoidHom

public theorem reducedFibersToUnion_band_left (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    reducedFibersToUnion D k
      (integralSingularHomologyMap k D.orderThreeBandProjection (D.bandHomologyEquiv k x), 0) =
      integralSingularHomologyMap k
        ((IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide).comp
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)) x := by
  let e := integralSingularHomologyEquivOfHomotopyEquiv k D.orderThreeSideHomotopyEquiv
  have hc := congrArg Prod.fst (D.differenceMap_conjugacy k x)
  change e (integralSingularHomologyMap k
    (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x) = _ at hc
  dsimp only at hc
  change integralSingularHomologyMap k
      (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide)
      (e.symm (integralSingularHomologyMap k D.orderThreeBandProjection
        (D.bandHomologyEquiv k x))) +
    integralSingularHomologyMap k
      (IntegralMayerVietoris.rightToUnion D.orderThreeSide D.orderFourSide)
      ((integralSingularHomologyEquivOfHomotopyEquiv k D.orderFourSideHomotopyEquiv).symm 0) = _
  rw [map_zero, map_zero, add_zero, ← hc, AddEquiv.symm_apply_apply,
    integralSingularHomologyMap_comp_wang]

public theorem band_images_eq (x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter)) :
    reducedFibersToUnion D 2 (integralSingularHomologyMap 2 D.orderThreeBandProjection x, 0) =
      reducedFibersToUnion D 2 (0, integralSingularHomologyMap 2 D.orderFourBandProjection x) := by
  let z := (D.bandHomologyEquiv 2).symm x
  have hc := D.differenceMap_conjugacy 2 z
  rw [AddEquiv.apply_symm_apply] at hc
  have hz := (EllipticTwoDiscHomologyCoordinates.presentationTwo (D := D)).exact_highDifference_inclusion.apply_apply_eq_zero z
  change IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 2
    (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 2 z) = 0 at hz
  have h : reducedFibersToUnion D 2
      (integralSingularHomologyMap 2 D.orderThreeBandProjection x,
        -integralSingularHomologyMap 2 D.orderFourBandProjection x) = 0 := by
    rw [← hc]
    change IntegralMayerVietoris.sumMap _ _ 2 ((D.sideHomologyEquiv 2).symm
      ((D.sideHomologyEquiv 2) _)) = 0
    rw [AddEquiv.symm_apply_apply]
    exact hz
  have hp : (integralSingularHomologyMap 2 D.orderThreeBandProjection x,
      -integralSingularHomologyMap 2 D.orderFourBandProjection x) =
      (integralSingularHomologyMap 2 D.orderThreeBandProjection x, 0) -
      (0, integralSingularHomologyMap 2 D.orderFourBandProjection x) := by
    apply Prod.ext
    · exact (sub_zero _).symm
    · exact (zero_sub _).symm
  rw [hp, map_sub, sub_eq_zero] at h
  exact h

public theorem projected_generators_eq
    (hAlignment : ∀ x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter),
      (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2 D.bandToOrderFourCoverSource x) =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2 D.bandToOrderThreeCoverSource x)) (i : Fin 6) :
    reducedFibersToUnion D 2 (orderThreeProjectedDegreeTwoGenerator A.periods i, 0) =
      reducedFibersToUnion D 2 (0, orderFourProjectedDegreeTwoGenerator A.periods i) := by
  let e := (integralSingularHomologyEquiv 2 D.bandToOrderThreeCoverSource).trans
    (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
  let x := e.symm (Pi.single i 1)
  have h3 : integralSingularHomologyMap 2 D.bandToOrderThreeCoverSource x =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm (Pi.single i 1) := by
    apply (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.injective
    exact (e.apply_symm_apply _).trans
      ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.apply_symm_apply _).symm
  have h4 : integralSingularHomologyMap 2 D.bandToOrderFourCoverSource x =
      (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm (Pi.single i 1) := by
    apply (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.injective
    rw [hAlignment, h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h := band_images_eq D x
  simp only [EllipticTwoDiscCoverData.orderThreeBandProjection,
    EllipticTwoDiscCoverData.orderFourBandProjection,
    ← integralSingularHomologyMap_comp_wang, h3, h4] at h
  exact h

end SphereSixComplex.Geometry.AnalyticData.EllipticHomologyGeneratorAlignment
