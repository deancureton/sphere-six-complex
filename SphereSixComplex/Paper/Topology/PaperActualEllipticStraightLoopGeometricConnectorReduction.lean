module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticLocalMarkedLoopCompatibilityProof

/-!
# Geometric connector reduction for the actual elliptic straight loops
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

public theorem ellipticThreeOverlapToCentral_boundaryProjection_apply
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.ellipticThreeOverlapToCentral
        (A.ellipticThreeBoundaryProjection q) =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)) := by
  simp [ellipticThreeOverlapToCentral,
    ellipticThreeBoundaryProjection,
    orderThreeRadialMappingTorusToActualOverlapHomeomorph]
  apply congrArg (A.starToCentral 1)
  exact A.orderThreeCollarToActualOverlapHomeomorph.symm_apply_apply _

public theorem ellipticFourOverlapToCentral_boundaryProjection_apply
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.ellipticFourOverlapToCentral
        (A.ellipticFourBoundaryProjection q) =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)) := by
  simp [ellipticFourOverlapToCentral,
    ellipticFourBoundaryProjection,
    orderFourRadialMappingTorusToActualOverlapHomeomorph]
  apply congrArg (A.starToCentral 2)
  exact A.orderFourCollarToActualOverlapHomeomorph.symm_apply_apply _

/-- The order-three straight deck loop after applying the literal overlap chart. -/
public noncomputable def ellipticThreeBoundaryDeckStraightCentralLoop
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase := by
  let _ := A.ellipticThreeBoundaryAction
  exact (A.ellipticThreeBoundaryDeckStraightLoop g).map
    A.ellipticThreeOverlapToCentral.continuous

/-- The order-four straight deck loop after applying the literal overlap chart. -/
public noncomputable def ellipticFourBoundaryDeckStraightCentralLoop
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    Path A.ellipticFourCentralBase A.ellipticFourCentralBase := by
  let _ := A.ellipticFourBoundaryAction
  exact (A.ellipticFourBoundaryDeckStraightLoop g).map
    A.ellipticFourOverlapToCentral.continuous

public theorem ellipticThreeBoundaryDeckStraightCentralLoop_class
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightLoop g)) =
      Path.Homotopic.Quotient.mk
        (A.ellipticThreeBoundaryDeckStraightCentralLoop g) := by
  let _ := A.ellipticThreeBoundaryAction
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem ellipticFourBoundaryDeckStraightCentralLoop_class
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticFourBoundaryDeckStraightLoop g)) =
      Path.Homotopic.Quotient.mk
        (A.ellipticFourBoundaryDeckStraightCentralLoop g) := by
  let _ := A.ellipticFourBoundaryAction
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem ellipticThreeBoundaryDeckStraightCentralLoop_apply
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.ellipticThreeBoundaryAction
    A.ellipticThreeBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          ((A.ellipticThreeBoundaryDeckStraightLift g t).1,
            orderThreeAffineMappingTorusLiftProjection A.periods
              (A.ellipticThreeBoundaryDeckStraightLift g t).2)) := by
  let _ := A.ellipticThreeBoundaryAction
  unfold ellipticThreeBoundaryDeckStraightCentralLoop
    ellipticThreeBoundaryDeckStraightLoop
  exact A.ellipticThreeOverlapToCentral_boundaryProjection_apply
    (A.ellipticThreeBoundaryDeckStraightLift g t)

public theorem ellipticFourBoundaryDeckStraightCentralLoop_apply
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    letI := A.ellipticFourBoundaryAction
    A.ellipticFourBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          ((A.ellipticFourBoundaryDeckStraightLift g t).1,
            orderFourAffineMappingTorusLiftProjection A.periods
              (A.ellipticFourBoundaryDeckStraightLift g t).2)) := by
  let _ := A.ellipticFourBoundaryAction
  unfold ellipticFourBoundaryDeckStraightCentralLoop
    ellipticFourBoundaryDeckStraightLoop
  exact A.ellipticFourOverlapToCentral_boundaryProjection_apply
    (A.ellipticFourBoundaryDeckStraightLift g t)

public theorem ellipticThreeBoundaryDeckStraightCentralLoop_apply_segment
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.ellipticThreeBoundaryAction
    A.ellipticThreeBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          (A.ellipticThreeBoundaryBase.1,
            orderThreeAffineMappingTorusLiftProjection A.periods
              (Path.segment A.ellipticThreeBoundaryBase.2
                (g • A.ellipticThreeBoundaryBase.2) t))) := by
  let _ := A.ellipticThreeBoundaryAction
  simpa [ellipticThreeBoundaryDeckStraightLift] using
    A.ellipticThreeBoundaryDeckStraightCentralLoop_apply g t

public theorem ellipticFourBoundaryDeckStraightCentralLoop_apply_segment
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    letI := A.ellipticFourBoundaryAction
    A.ellipticFourBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          (A.ellipticFourBoundaryBase.1,
            orderFourAffineMappingTorusLiftProjection A.periods
              (Path.segment A.ellipticFourBoundaryBase.2
                (g • A.ellipticFourBoundaryBase.2) t))) := by
  let _ := A.ellipticFourBoundaryAction
  simpa [ellipticFourBoundaryDeckStraightLift] using
    A.ellipticFourBoundaryDeckStraightCentralLoop_apply g t







end SphereSixComplex.Geometry.PaperAnalyticData

end

end
