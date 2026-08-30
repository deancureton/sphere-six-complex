module

public import SphereSixComplex.Topology.PaperAffineCyclicProjectionQuotient
public import SphereSixComplex.Topology.PaperAffineCyclicProjectedPeriodLoop
public import SphereSixComplex.Topology.PaperMultipleFiberAffineDeckAction
public import SphereSixComplex.Topology.QuotientCoveringMarkedLoops

open Set Topology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.QuotientCoveringMarkedLoops

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m (AdditiveTorus p)}

public theorem reducedCentralFiber_pathConnectedSpace
    (D : RadialEllipticActionData m (AdditiveTorus p)) :
    PathConnectedSpace D.reducedCentralFiber :=
  (complexTwoReducedCentralFiberProjection_isQuotientMap D).surjective.pathConnectedSpace
    (complexTwoReducedCentralFiberProjection (D := D)).continuous

public theorem affineCyclicFilling_isQuotientCoveringMap
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift)
    (hLinv : Continuous P.affine.lift.symm) :
    letI := affineCyclicFillingDeckAction P
    IsQuotientCoveringMap
      (complexTwoReducedCentralFiberProjection (D := D))
      (affineCyclicBoundaryDeckData P).FillingDeck := by
  let _ := affineCyclicFillingDeckAction P
  let _ : ContinuousConstSMul
      (affineCyclicBoundaryDeckData P).FillingDeck ComplexTwoSpace :=
    affineCyclicFillingDeckAction_continuous P hL hLinv
  let _ : ProperlyDiscontinuousSMul
      (affineCyclicBoundaryDeckData P).FillingDeck ComplexTwoSpace :=
    affineCyclicFillingDeckAction_properlyDiscontinuous P hL hLinv
  let _ : IsCancelSMul
      (affineCyclicBoundaryDeckData P).FillingDeck ComplexTwoSpace :=
    affineCyclicFillingDeckAction_free P
  apply isQuotientCoveringMap_of_properlyDiscontinuous_of_isCancelSMul
    (complexTwoReducedCentralFiberProjection_isQuotientMap D)
  intro z w
  exact complexTwoReducedCentralFiberProjection_eq_iff_exists_fillingDeck P z w

public noncomputable def affineCyclicKernelPath
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    letI := affineCyclicFillingDeckAction P
    Path (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x • 0) := by
  let _ := affineCyclicFillingDeckAction P
  exact (Path.segment (0 : ComplexTwoSpace) (periodVector p x)).cast rfl (by
    rw [affineCyclicKernelIncl_smul]
    simp)

public theorem affineCyclicKernelPath_fundamentalGroupEquiv
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hp : letI := affineCyclicFillingDeckAction P
      IsQuotientCoveringMap
        (complexTwoReducedCentralFiberProjection (D := D))
        (affineCyclicBoundaryDeckData P).FillingDeck)
    (x : Lattice) :
    letI := affineCyclicFillingDeckAction P
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (SphereSixComplex.Geometry.projectedQuotientDeckPath hp
            (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x)
            (affineCyclicKernelPath P x))) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  let _ := affineCyclicFillingDeckAction P
  exact fundamentalGroupEquiv_projectedQuotientDeckPath hp
    (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x) (affineCyclicKernelPath P x)

public theorem projectedQuotientDeckPath_affineCyclicKernel_eq
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hp : letI := affineCyclicFillingDeckAction P
      IsQuotientCoveringMap
        (complexTwoReducedCentralFiberProjection (D := D))
        (affineCyclicBoundaryDeckData P).FillingDeck)
    (x : Lattice) :
    letI := affineCyclicFillingDeckAction P
    SphereSixComplex.Geometry.projectedQuotientDeckPath hp
        (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x)
        (affineCyclicKernelPath P x) =
      projectedStraightPeriodLoop P x := by
  let _ := affineCyclicFillingDeckAction P
  ext t
  rfl

public theorem projectedStraightPeriodLoop_fundamentalGroupEquiv
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hp : letI := affineCyclicFillingDeckAction P
      IsQuotientCoveringMap
        (complexTwoReducedCentralFiberProjection (D := D))
        (affineCyclicBoundaryDeckData P).FillingDeck)
    (x : Lattice) :
    letI := affineCyclicFillingDeckAction P
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (projectedStraightPeriodLoop P x)) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  let _ := affineCyclicFillingDeckAction P
  rw [← projectedQuotientDeckPath_affineCyclicKernel_eq P hp x]
  exact affineCyclicKernelPath_fundamentalGroupEquiv P hp x

variable {U : TriangleUniformization}

public theorem orderThreeAffineCyclicFilling_isQuotientCoveringMap
    (F : SphereSixComplex.Periods.PeriodFunctions U) :
    let P := orderThreeCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    IsQuotientCoveringMap
      (complexTwoReducedCentralFiberProjection (D := orderThreeRadialActionData F))
      (affineCyclicBoundaryDeckData P).FillingDeck := by
  exact affineCyclicFilling_isQuotientCoveringMap
    (orderThreeCentralFiberPresentationData F)
    (orderThreeCentralFiberPresentationData_lift_continuous F)
    (orderThreeCentralFiberPresentationData_lift_symm_continuous F)

public theorem orderFourAffineCyclicFilling_isQuotientCoveringMap
    (F : SphereSixComplex.Periods.PeriodFunctions U) :
    let P := orderFourCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    IsQuotientCoveringMap
      (complexTwoReducedCentralFiberProjection (D := orderFourRadialActionData F))
      (affineCyclicBoundaryDeckData P).FillingDeck := by
  exact affineCyclicFilling_isQuotientCoveringMap
    (orderFourCentralFiberPresentationData F)
    (orderFourCentralFiberPresentationData_lift_continuous F)
    (orderFourCentralFiberPresentationData_lift_symm_continuous F)

public theorem orderThreeAffineCyclicKernelPath_fundamentalGroupEquiv
    (F : SphereSixComplex.Periods.PeriodFunctions U) (x : Lattice) :
    let P := orderThreeCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    let hp := orderThreeAffineCyclicFilling_isQuotientCoveringMap F
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (SphereSixComplex.Geometry.projectedQuotientDeckPath hp
            (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x)
            (affineCyclicKernelPath P x))) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  exact affineCyclicKernelPath_fundamentalGroupEquiv
    (orderThreeCentralFiberPresentationData F)
    (orderThreeAffineCyclicFilling_isQuotientCoveringMap F) x

public theorem orderFourAffineCyclicKernelPath_fundamentalGroupEquiv
    (F : SphereSixComplex.Periods.PeriodFunctions U) (x : Lattice) :
    let P := orderFourCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    let hp := orderFourAffineCyclicFilling_isQuotientCoveringMap F
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (SphereSixComplex.Geometry.projectedQuotientDeckPath hp
            (0 : ComplexTwoSpace) (affineCyclicKernelIncl P x)
            (affineCyclicKernelPath P x))) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  exact affineCyclicKernelPath_fundamentalGroupEquiv
    (orderFourCentralFiberPresentationData F)
    (orderFourAffineCyclicFilling_isQuotientCoveringMap F) x

public theorem orderThreeProjectedStraightPeriodLoop_fundamentalGroupEquiv
    (F : SphereSixComplex.Periods.PeriodFunctions U) (x : Lattice) :
    let P := orderThreeCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    let hp := orderThreeAffineCyclicFilling_isQuotientCoveringMap F
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (projectedStraightPeriodLoop P x)) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  exact projectedStraightPeriodLoop_fundamentalGroupEquiv
    (orderThreeCentralFiberPresentationData F)
    (orderThreeAffineCyclicFilling_isQuotientCoveringMap F) x

public theorem orderFourProjectedStraightPeriodLoop_fundamentalGroupEquiv
    (F : SphereSixComplex.Periods.PeriodFunctions U) (x : Lattice) :
    let P := orderFourCentralFiberPresentationData F
    letI := affineCyclicFillingDeckAction P
    let hp := orderFourAffineCyclicFilling_isQuotientCoveringMap F
    hp.fundamentalGroupEquiv ⟨(0 : ComplexTwoSpace), rfl⟩
        (SphereSixComplex.Geometry.pathLoopClass
          (projectedStraightPeriodLoop P x)) =
      MulOpposite.op (affineCyclicKernelIncl P x) := by
  exact projectedStraightPeriodLoop_fundamentalGroupEquiv
    (orderFourCentralFiberPresentationData F)
    (orderFourAffineCyclicFilling_isQuotientCoveringMap F) x

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
