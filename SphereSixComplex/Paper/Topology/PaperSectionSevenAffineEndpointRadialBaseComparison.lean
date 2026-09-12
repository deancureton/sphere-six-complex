module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffinePrincipalGaugeRadialBaseSquare

/-!
# Radial base lifts over the marked affine strip

Restrict the explicit inverse radial base equivalences to the named affine-strip lift.  Their
regular-coordinate projections are the explicit normalized strip maps, which are independent of
the torus fibre coordinate.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open GlobalTorusFamily
open EllipticLinearCollarGlobalDescent EllipticLogarithmicGauge
open EllipticWholeFiberCompactCover
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The named strip lift, regarded as a point of the order-three half-plane preimage. -/
public def affineOrderThreeHalfPlaneBaseLift
    (A : AnalyticData) :
    C(affineVerticalStrip, A.OrderThreeAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNamedStripLift.lift z, by
      change (A.regularCoordinate (A.affineNamedStripLift.lift z)).1.re < 2 / 3
      rw [A.affineNamedStripLift.lift_coordinate]
      exact z.2.2⟩,
    A.affineNamedStripLift.lift.continuous.subtype_mk _⟩

/-- The named strip lift, regarded as a point of the order-four half-plane preimage. -/
public def affineOrderFourHalfPlaneBaseLift
    (A : AnalyticData) :
    C(affineVerticalStrip, A.OrderFourAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNamedStripLift.lift z, by
      change 1 / 3 < (A.regularCoordinate
        (A.affineNamedStripLift.lift z)).1.re
      rw [A.affineNamedStripLift.lift_coordinate]
      exact z.2.1⟩,
    A.affineNamedStripLift.lift.continuous.subtype_mk _⟩



/-- The order-three inverse radial lift over the named strip. -/
public noncomputable def affineOrderThreeRadialBaseLift
    (A : AnalyticData) :
    C(affineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr₀ := A.affineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.affineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  ⟨fun z ↦ ((A.orderThreeBaseRadialEquiv
      (s := r / 2) (by linarith) (by linarith) hr).invFun
        (A.affineOrderThreeHalfPlaneBaseLift z)).1,
    continuous_subtype_val.comp
      ((A.orderThreeBaseRadialEquiv
        (s := r / 2) (by linarith) (by linarith) hr).invFun.continuous.comp
          A.affineOrderThreeHalfPlaneBaseLift.continuous)⟩

/-- The order-four inverse radial lift over the named strip. -/
public noncomputable def affineOrderFourRadialBaseLift
    (A : AnalyticData) :
    C(affineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  ⟨fun z ↦ ((A.orderFourBaseRadialEquiv
      (s := r / 2) (by linarith) (by linarith) hr).invFun
        (A.affineOrderFourHalfPlaneBaseLift z)).1,
    continuous_subtype_val.comp
      ((A.orderFourBaseRadialEquiv
        (s := r / 2) (by linarith) (by linarith) hr).invFun.continuous.comp
          A.affineOrderFourHalfPlaneBaseLift.continuous)⟩







/-! ## The principal-gauge leg of the radial base square -/









end SphereSixComplex.Geometry.AnalyticData

end
