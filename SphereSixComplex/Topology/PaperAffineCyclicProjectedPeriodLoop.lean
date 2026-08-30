module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

/-!
# Marked period loops in an affine cyclic reduced central fibre

This module constructs the literal projected straight period loops and reduces their marked
homology calculation to the corresponding marked-basis statement on the covering torus.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open LatticeData Periods
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels

namespace EstablishedAffineCyclicQuotientHomology

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The finite cyclic reduced-central-fibre projection, expressed with the period torus itself
as source. -/
public def reducedCentralFiberTorusProjection :
    C(AdditiveTorus p, D.reducedCentralFiber) :=
  (RadialEllipticActionData.centralFiberCoverProjection D).comp
    ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩

/-- The straight segment from zero to an integral period, projected to the period torus. -/
public def additiveTorusStraightPeriodLoop (x : Lattice) : Path (0 : AdditiveTorus p) 0 :=
  ((Path.segment (0 : ComplexTwoSpace) (periodVector p x)).map
      (continuous_quot_mk : Continuous (torusProjection p))).cast
    (additiveTorus_mk_zero p).symm
    (additiveTorusProjection_periodVector p x).symm

private def additiveTorusStandardCoordinate
    (P : AffineCyclicCentralFiberPresentationData m p D) (i : Fin 4) :
    C(AdditiveTorus p, UnitAddCircle) :=
  (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
    C(StandardTorusHomology.StdTorus 1, UnitAddCircle)).comp
    ((StandardTorusHomology.standardFourTorusCoordinateProjection i).comp
      ⟨StandardTorusHomology.additiveTorusStdMap p P.fullRank,
        (StandardTorusHomology.additiveTorusStdHomeomorph p P.fullRank).continuous⟩)

private theorem additiveTorusStandardCoordinate_apply_projection
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (i : Fin 4) (z : ComplexTwoSpace) :
    additiveTorusStandardCoordinate P i (torusProjection p z) =
      (((P.fullRank.realEquiv.symm z i : ℝ)) : UnitAddCircle) := rfl

private theorem additiveTorusStandardCoordinate_zero
    (P : AffineCyclicCentralFiberPresentationData m p D) (i : Fin 4) :
    additiveTorusStandardCoordinate P i 0 = 0 := by
  rw [← additiveTorus_mk_zero p]
  change (((P.fullRank.realEquiv.symm (0 : ComplexTwoSpace)) i : ℝ) :
    UnitAddCircle) = 0
  simp

private def additiveTorusStraightPeriodCoordinateLoop
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x : Lattice) (i : Fin 4) : Path (0 : UnitAddCircle) 0 :=
  ((additiveTorusStraightPeriodLoop (p := p) x).map
    (additiveTorusStandardCoordinate P i).continuous).cast
      (additiveTorusStandardCoordinate_zero P i).symm
      (additiveTorusStandardCoordinate_zero P i).symm

private theorem additiveTorusStraightPeriodCoordinateLoop_eq
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x : Lattice) (i : Fin 4) :
    additiveTorusStraightPeriodCoordinateLoop P x i =
      StandardCircleHomologyLiftDegree.unitCircleIntegerLoop (x i) := by
  ext t
  rw [show additiveTorusStraightPeriodCoordinateLoop P x i t =
      additiveTorusStandardCoordinate P i
        (additiveTorusStraightPeriodLoop (p := p) x t) by rfl]
  rw [show additiveTorusStraightPeriodLoop (p := p) x t =
      torusProjection p
        (Path.segment (0 : ComplexTwoSpace) (periodVector p x) t) by rfl]
  rw [additiveTorusStandardCoordinate_apply_projection]
  rw [show Path.segment (0 : ComplexTwoSpace) (periodVector p x) t =
      (t : ℝ) • periodVector p x by
        simp [Path.segment, AffineMap.lineMap_apply_module]]
  rw [show StandardCircleHomologyLiftDegree.unitCircleIntegerLoop (x i) t =
      ((((t : ℝ) * (x i : ℝ) : ℝ)) : UnitAddCircle) by rfl]
  rw [map_smul, StandardTorusHomology.realEquiv_symm_periodVector]
  rfl

private theorem additiveTorusStraightPeriodLoop_degreeOne
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne
      (StandardCircleHomologyLiftDegree.loopHomologyClass
        (additiveTorusStraightPeriodLoop (p := p) x)) = x := by
  rw [EstablishedTorusHomology.additiveTorusHomologyBasis_degreeOne]
  change StandardTorusHomology.standardFourTorusCoordinateHom
    (integralSingularHomologyMap 1
      (StandardTorusHomology.additiveTorusStdHomeomorph p P.fullRank :
        C(AdditiveTorus p, StandardTorusHomology.StdTorus 4))
      (StandardCircleHomologyLiftDegree.loopHomologyClass
        (additiveTorusStraightPeriodLoop (p := p) x))) = x
  funext i
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
    (integralSingularHomologyMap 1
      (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
        C(StandardTorusHomology.StdTorus 1, UnitAddCircle))
      (integralSingularHomologyMap 1
        (StandardTorusHomology.standardFourTorusCoordinateProjection i)
        (integralSingularHomologyMap 1
          (StandardTorusHomology.additiveTorusStdHomeomorph p P.fullRank :
            C(AdditiveTorus p, StandardTorusHomology.StdTorus 4))
          (StandardCircleHomologyLiftDegree.loopHomologyClass
            (additiveTorusStraightPeriodLoop (p := p) x))))) = x i
  rw [integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
    (integralSingularHomologyMap 1 (additiveTorusStandardCoordinate P i)
      (StandardCircleHomologyLiftDegree.loopHomologyClass
        (additiveTorusStraightPeriodLoop (p := p) x))) = x i
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  rw [← StandardCircleHomologyLiftDegree.loopHomologyClass_cast
    ((additiveTorusStraightPeriodLoop (p := p) x).map
      (additiveTorusStandardCoordinate P i).continuous)
    (additiveTorusStandardCoordinate_zero P i).symm]
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
    (StandardCircleHomologyLiftDegree.loopHomologyClass
      (additiveTorusStraightPeriodCoordinateLoop P x i)) = x i
  rw [additiveTorusStraightPeriodCoordinateLoop_eq,
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_integerLoop]

public theorem additiveTorusStraightPeriodLoop_homologyClass
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    StandardCircleHomologyLiftDegree.loopHomologyClass
        (additiveTorusStraightPeriodLoop (p := p) x) =
      (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne.symm x := by
  apply (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne.injective
  rw [additiveTorusStraightPeriodLoop_degreeOne]
  exact
    (EstablishedTorusHomology.additiveTorusHomologyBasis p
      P.fullRank).degreeOne.apply_symm_apply x |>.symm

/-- The straight period segment in `ℂ²`, projected to the reduced central fibre. -/
public def projectedStraightPeriodLoop
    (_P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    Path (reducedCentralFiberTorusProjection (D := D) 0)
      (reducedCentralFiberTorusProjection (D := D) 0) :=
  (additiveTorusStraightPeriodLoop (p := p) x).map
    (reducedCentralFiberTorusProjection (D := D)).continuous

/-- Pointwise, `projectedStraightPeriodLoop` is the canonical `ℂ²` projection applied to
the literal straight segment from zero to the labelled period. -/
public theorem projectedStraightPeriodLoop_apply
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice)
    (t : unitInterval) :
    projectedStraightPeriodLoop P x t =
      complexTwoReducedCentralFiberProjection (D := D)
        (Path.segment (0 : ComplexTwoSpace) (periodVector p x) t) :=
  rfl

/-- The homology class of a projected straight period loop is the image of its torus loop
class. -/
public theorem projectedStraightPeriodLoop_homologyClass
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    StandardCircleHomologyLiftDegree.loopHomologyClass
        (projectedStraightPeriodLoop P x) =
      integralSingularHomologyMap 1 (reducedCentralFiberTorusProjection (D := D))
        (StandardCircleHomologyLiftDegree.loopHomologyClass
          (additiveTorusStraightPeriodLoop (p := p) x)) := by
  exact
    (StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass
      (reducedCentralFiberTorusProjection (D := D))
      (additiveTorusStraightPeriodLoop (p := p) x)).symm

/-- The reduced-fibre straight-period loop class is the covering-projection lattice map. -/
public theorem projectedStraightPeriodLoop_homologyClass_eq_coverProjectionLatticeMap
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Lattice) :
    StandardCircleHomologyLiftDegree.loopHomologyClass
        (projectedStraightPeriodLoop P x) = coverProjectionLatticeMap P x := by
  rw [projectedStraightPeriodLoop_homologyClass P x,
    additiveTorusStraightPeriodLoop_homologyClass P x]
  rw [coverProjectionLatticeMap_apply]
  rw [show (centralFiberCoverSourceDegreeOneBasis P).symm x =
      integralSingularHomologyMap 1
        ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩
        ((EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne.symm x) by
    rfl]
  exact (integralSingularHomologyMap_comp_wang 1
    ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩
    (RadialEllipticActionData.centralFiberCoverProjection D)
    ((EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeOne.symm x)).symm

end EstablishedAffineCyclicQuotientHomology

end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
