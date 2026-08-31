module

public import SphereSixComplex.Topology.PaperActualEllipticRelatorClassificationProof
public import SphereSixComplex.Topology.PuncturedComplexFundamentalGroup

/-!
# Local coordinate classification of the complete elliptic filling relations
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The nonzero Cayley coordinate at the order-three filling-relation basepoint. -/
public noncomputable def orderThreeFillingRelationCayleyBaseValue : ℂ :=
  ((A.orderThreeActualEllipticBoundaryBase.1 : ℝ) : ℂ) *
    ((angleMap 3 A.orderThreeActualEllipticBoundaryBase.2.1 : Circle) : ℂ)

public theorem orderThreeFillingRelationCayleyBaseValue_ne_zero :
    A.orderThreeFillingRelationCayleyBaseValue ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt A.orderThreeActualEllipticBoundaryBase.1.2.1
  · exact Circle.coe_ne_zero _

/-- The nonzero Cayley coordinate at the order-four filling-relation basepoint. -/
public noncomputable def orderFourFillingRelationCayleyBaseValue : ℂ :=
  ((A.orderFourActualEllipticBoundaryBase.1 : ℝ) : ℂ) *
    ((angleMap 4 A.orderFourActualEllipticBoundaryBase.2.1 : Circle) : ℂ)

public theorem orderFourFillingRelationCayleyBaseValue_ne_zero :
    A.orderFourFillingRelationCayleyBaseValue ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt A.orderFourActualEllipticBoundaryBase.1.2.1
  · exact Circle.coe_ne_zero _

/-- The order-three Cayley coordinate makes one positive turn around the puncture. -/
public noncomputable def orderThreeFillingRelationCayleyLoop :
    Path
      (⟨A.orderThreeFillingRelationCayleyBaseValue,
        A.orderThreeFillingRelationCayleyBaseValue_ne_zero⟩ : PuncturedComplex)
      ⟨A.orderThreeFillingRelationCayleyBaseValue,
        A.orderThreeFillingRelationCayleyBaseValue_ne_zero⟩ :=
  puncturedComplexIntegerCircle A.orderThreeFillingRelationCayleyBaseValue
    A.orderThreeFillingRelationCayleyBaseValue_ne_zero 1

/-- The order-four Cayley coordinate makes one positive turn around the puncture. -/
public noncomputable def orderFourFillingRelationCayleyLoop :
    Path
      (⟨A.orderFourFillingRelationCayleyBaseValue,
        A.orderFourFillingRelationCayleyBaseValue_ne_zero⟩ : PuncturedComplex)
      ⟨A.orderFourFillingRelationCayleyBaseValue,
        A.orderFourFillingRelationCayleyBaseValue_ne_zero⟩ :=
  puncturedComplexIntegerCircle A.orderFourFillingRelationCayleyBaseValue
    A.orderFourFillingRelationCayleyBaseValue_ne_zero 1

/-- Pointwise, the concrete order-three collar coordinate is the one-turn punctured-plane loop. -/
public theorem orderThreeFillingRelationCayleyLoop_apply (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    ((orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative
          (A.orderThreeActualEllipticBoundaryDeckStraightLift
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (A.orderThreeFillingRelationCayleyLoop t).1 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [A.orderThreeFillingRelationInverseRepresentative_cayley_fullTurn]
  simp only [orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle]
  rw [Circle.coe_exp]
  change _ = (puncturedComplexIntegerCirclePoint
    A.orderThreeFillingRelationCayleyBaseValue
    A.orderThreeFillingRelationCayleyBaseValue_ne_zero 1 t).1
  simp [puncturedComplexIntegerCirclePoint, orderThreeFillingRelationCayleyBaseValue]

/-- Pointwise, the concrete order-four collar coordinate is the one-turn punctured-plane loop. -/
public theorem orderFourFillingRelationCayleyLoop_apply (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    ((orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative
          (A.orderFourActualEllipticBoundaryDeckStraightLift
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (A.orderFourFillingRelationCayleyLoop t).1 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rw [A.orderFourFillingRelationInverseRepresentative_cayley_fullTurn]
  simp only [orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle]
  rw [Circle.coe_exp]
  change _ = (puncturedComplexIntegerCirclePoint
    A.orderFourFillingRelationCayleyBaseValue
    A.orderFourFillingRelationCayleyBaseValue_ne_zero 1 t).1
  simp [puncturedComplexIntegerCirclePoint, orderFourFillingRelationCayleyBaseValue]

/-- The base-coordinate loop of the order-three complete relation has winding number one. -/
public theorem orderThreeFillingRelationCayleyLoop_classification :
    puncturedComplexFundamentalGroupEquiv
        A.orderThreeFillingRelationCayleyBaseValue
        A.orderThreeFillingRelationCayleyBaseValue_ne_zero
        (Path.Homotopic.Quotient.mk A.orderThreeFillingRelationCayleyLoop) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple 1)) := by
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    A.orderThreeFillingRelationCayleyBaseValue
    A.orderThreeFillingRelationCayleyBaseValue_ne_zero 1

/-- The base-coordinate loop of the order-four complete relation has winding number one. -/
public theorem orderFourFillingRelationCayleyLoop_classification :
    puncturedComplexFundamentalGroupEquiv
        A.orderFourFillingRelationCayleyBaseValue
        A.orderFourFillingRelationCayleyBaseValue_ne_zero
        (Path.Homotopic.Quotient.mk A.orderFourFillingRelationCayleyLoop) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple 1)) := by
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    A.orderFourFillingRelationCayleyBaseValue
    A.orderFourFillingRelationCayleyBaseValue_ne_zero 1

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
