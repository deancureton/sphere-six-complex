module

public import SphereSixComplex.Paper.Topology.PaperAffineCyclicProjectionQuotient
public import SphereSixComplex.Paper.Topology.PaperAffineCyclicProjectedPeriodLoop
public import SphereSixComplex.Paper.Topology.PaperMultipleFiberAffineDeckAction
public import SphereSixComplex.Prerequisites.Topology.QuotientCoveringMarkedLoops

open Set Topology

namespace SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex SphereSixComplex.Topology
open SphereSixComplex.AffineCyclicQuotientHomology

open _root_.SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.EllipticFilling
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

end SphereSixComplex.AffineCyclicQuotientHomology
