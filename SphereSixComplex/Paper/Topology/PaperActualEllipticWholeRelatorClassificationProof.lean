module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorClassificationProof

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
  ((A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) *
    ((angleMap 3 A.ellipticThreeBoundaryBase.2.1 : Circle) : ℂ)

public theorem orderThreeFillingRelationCayleyBaseValue_ne_zero :
    A.orderThreeFillingRelationCayleyBaseValue ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt A.ellipticThreeBoundaryBase.1.2.1
  · exact Circle.coe_ne_zero _

/-- The nonzero Cayley coordinate at the order-four filling-relation basepoint. -/
public noncomputable def orderFourFillingRelationCayleyBaseValue : ℂ :=
  ((A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) *
    ((angleMap 4 A.ellipticFourBoundaryBase.2.1 : Circle) : ℂ)

public theorem orderFourFillingRelationCayleyBaseValue_ne_zero :
    A.orderFourFillingRelationCayleyBaseValue ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt A.ellipticFourBoundaryBase.1.2.1
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
    letI := A.ellipticThreeBoundaryAction
    ((orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative
          (A.ellipticThreeBoundaryDeckStraightLift
            A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (A.orderThreeFillingRelationCayleyLoop t).1 := by
  let _ := A.ellipticThreeBoundaryAction
  rw [A.orderThreeFillingRelationInverseRepresentative_cayley_fullTurn]
  simp only [orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle]
  rw [Circle.coe_exp]
  change _ = (puncturedComplexIntegerCirclePoint
    A.orderThreeFillingRelationCayleyBaseValue
    A.orderThreeFillingRelationCayleyBaseValue_ne_zero 1 t).1
  simp [puncturedComplexIntegerCirclePoint, orderThreeFillingRelationCayleyBaseValue]

/-- Pointwise, the concrete order-four collar coordinate is the one-turn punctured-plane loop. -/
public theorem orderFourFillingRelationCayleyLoop_apply (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    ((orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative
          (A.ellipticFourBoundaryDeckStraightLift
            A.ellipticFourBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (A.orderFourFillingRelationCayleyLoop t).1 := by
  let _ := A.ellipticFourBoundaryAction
  rw [A.orderFourFillingRelationInverseRepresentative_cayley_fullTurn]
  simp only [orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle]
  rw [Circle.coe_exp]
  change _ = (puncturedComplexIntegerCirclePoint
    A.orderFourFillingRelationCayleyBaseValue
    A.orderFourFillingRelationCayleyBaseValue_ne_zero 1 t).1
  simp [puncturedComplexIntegerCirclePoint, orderFourFillingRelationCayleyBaseValue]



end SphereSixComplex.Geometry.PaperAnalyticData

end

end
