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

namespace SphereSixComplex.Geometry.PaperAnalyticData

open GlobalTorusFamily
open EllipticLinearCollarGlobalDescent EllipticPuncturedCollarGaugeHomeomorph
open EllipticWholeFiberCompactCover
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The named strip lift, regarded as a point of the order-three half-plane preimage. -/
public def affineOrderThreeHalfPlaneBaseLift
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, A.OrderThreeAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNamedStripLift.lift z, by
      change (A.regularCoordinate (A.affineNamedStripLift.lift z)).1.re < 2 / 3
      rw [A.affineNamedStripLift.lift_coordinate]
      exact z.2.2⟩,
    A.affineNamedStripLift.lift.continuous.subtype_mk _⟩

/-- The named strip lift, regarded as a point of the order-four half-plane preimage. -/
public def affineOrderFourHalfPlaneBaseLift
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, A.OrderFourAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNamedStripLift.lift z, by
      change 1 / 3 < (A.regularCoordinate
        (A.affineNamedStripLift.lift z)).1.re
      rw [A.affineNamedStripLift.lift_coordinate]
      exact z.2.1⟩,
    A.affineNamedStripLift.lift.continuous.subtype_mk _⟩

/-- The order-three half-plane coordinate carried by the named strip lift. -/
public noncomputable def affineOrderThreeHalfPlaneCoordinate
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, orderThreeAffineHalfPlaneCoordinateRegion) :=
  ⟨fun z ↦
      ⟨A.regularCoordinate (A.affineOrderThreeHalfPlaneBaseLift z).1,
        (A.affineOrderThreeHalfPlaneBaseLift z).2⟩,
    (A.regularCoordinate_isLocalHomeomorph.continuous.comp
      (continuous_subtype_val.comp
        A.affineOrderThreeHalfPlaneBaseLift.continuous)).subtype_mk _⟩

/-- The order-four half-plane coordinate carried by the named strip lift. -/
public noncomputable def affineOrderFourHalfPlaneCoordinate
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, orderFourAffineHalfPlaneCoordinateRegion) :=
  ⟨fun z ↦
      ⟨A.regularCoordinate (A.affineOrderFourHalfPlaneBaseLift z).1,
        (A.affineOrderFourHalfPlaneBaseLift z).2⟩,
    (A.regularCoordinate_isLocalHomeomorph.continuous.comp
      (continuous_subtype_val.comp
        A.affineOrderFourHalfPlaneBaseLift.continuous)).subtype_mk _⟩

/-- The order-three inverse radial lift over the named strip. -/
public noncomputable def affineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) :
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
    (A : PaperAnalyticData) :
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

/-- The normalized order-three coordinate map on the affine strip. -/
public noncomputable def affineOrderThreeNormalizedBaseCoordinate
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, regularCoordinateBase) :=
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr₀ := A.affineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.affineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let D := orderThreeCoordinateDeformation
    (s := r / 2) (by linarith) (by linarith) hr
  ⟨fun z ↦ (D.normalize (A.affineOrderThreeHalfPlaneCoordinate z)).1,
    continuous_subtype_val.comp
      (D.normalize.continuous.comp
        A.affineOrderThreeHalfPlaneCoordinate.continuous)⟩

/-- The normalized order-four coordinate map on the affine strip. -/
public noncomputable def affineOrderFourNormalizedBaseCoordinate
    (A : PaperAnalyticData) :
    C(affineVerticalStrip, regularCoordinateBase) :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let D := orderFourCoordinateDeformation
    (s := r / 2) (by linarith) (by linarith) hr
  ⟨fun z ↦ (D.normalize (A.affineOrderFourHalfPlaneCoordinate z)).1,
    continuous_subtype_val.comp
      (D.normalize.continuous.comp
        A.affineOrderFourHalfPlaneCoordinate.continuous)⟩

/-- The order-three radial base lift projects to the explicit normalized strip coordinate. -/
public theorem regularCoordinate_affineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    A.regularCoordinate (A.affineOrderThreeRadialBaseLift z) =
      A.affineOrderThreeNormalizedBaseCoordinate z := by
  dsimp only [affineOrderThreeRadialBaseLift,
    affineOrderThreeNormalizedBaseCoordinate,
    affineOrderThreeHalfPlaneCoordinate]
  exact A.orderThreeBaseRadialEquiv_invFun_regularCoordinate _ _ _ _

/-- The order-four radial base lift projects to the explicit normalized strip coordinate. -/
public theorem regularCoordinate_affineOrderFourRadialBaseLift
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    A.regularCoordinate (A.affineOrderFourRadialBaseLift z) =
      A.affineOrderFourNormalizedBaseCoordinate z := by
  dsimp only [affineOrderFourRadialBaseLift,
    affineOrderFourNormalizedBaseCoordinate,
    affineOrderFourHalfPlaneCoordinate]
  exact A.orderFourBaseRadialEquiv_invFun_regularCoordinate _ _ _ _

/-- Continuous-map form of the order-three radial base square. -/
public theorem regularCoordinate_comp_affineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.affineOrderThreeRadialBaseLift =
      A.affineOrderThreeNormalizedBaseCoordinate := by
  funext z
  exact A.regularCoordinate_affineOrderThreeRadialBaseLift z

/-- Continuous-map form of the order-four radial base square. -/
public theorem regularCoordinate_comp_affineOrderFourRadialBaseLift
    (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.affineOrderFourRadialBaseLift =
      A.affineOrderFourNormalizedBaseCoordinate := by
  funext z
  exact A.regularCoordinate_affineOrderFourRadialBaseLift z

/-! ## The principal-gauge leg of the radial base square -/

/-- The regular base obtained after applying the order-three principal gauge to a selected
collar representative. -/
public noncomputable def affineOrderThreePrincipalGaugeRegularBase
    (A : PaperAnalyticData) (q : A.orderThreeCollarCarrier.carrier) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  regularTotalSpaceBase A.periods
    (orderThreeCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius q))

/-- The regular base obtained after applying the order-four principal gauge to a selected
collar representative. -/
public noncomputable def affineOrderFourPrincipalGaugeRegularBase
    (A : PaperAnalyticData) (q : A.orderFourCollarCarrier.carrier) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  regularTotalSpaceBase A.periods
    (orderFourCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius q))

/-- The order-three principal-gauge regular base retains the base of its collar
representative. -/
public theorem affineOrderThreePrincipalGaugeRegularBase_val
    (A : PaperAnalyticData) (q : A.orderThreeCollarCarrier.carrier) :
    (A.affineOrderThreePrincipalGaugeRegularBase q).1 =
      familyTotalSpaceBase A.periods q.1 := by
  unfold affineOrderThreePrincipalGaugeRegularBase
  exact orderThreeCollarToRegular_principalGauge_base A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.sourceData q

/-- The order-four principal-gauge regular base retains the base of its collar
representative. -/
public theorem affineOrderFourPrincipalGaugeRegularBase_val
    (A : PaperAnalyticData) (q : A.orderFourCollarCarrier.carrier) :
    (A.affineOrderFourPrincipalGaugeRegularBase q).1 =
      familyTotalSpaceBase A.periods q.1 := by
  unfold affineOrderFourPrincipalGaugeRegularBase
  exact orderFourCollarToRegular_principalGauge_base A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.sourceData q

/-- An order-three collar representative over the named radial strip produces exactly the
named radial base lift after applying the principal gauge. -/
public theorem affineOrderThreePrincipalGaugeRegularBase_eq_radialBaseLift
    (A : PaperAnalyticData) (z : affineVerticalStrip)
    (q : A.orderThreeCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.affineOrderThreeRadialBaseLift z).1) :
    A.affineOrderThreePrincipalGaugeRegularBase q =
      A.affineOrderThreeRadialBaseLift z := by
  apply Subtype.ext
  exact (A.affineOrderThreePrincipalGaugeRegularBase_val q).trans hbase

/-- An order-four collar representative over the named radial strip produces exactly the
named radial base lift after applying the principal gauge. -/
public theorem affineOrderFourPrincipalGaugeRegularBase_eq_radialBaseLift
    (A : PaperAnalyticData) (z : affineVerticalStrip)
    (q : A.orderFourCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.affineOrderFourRadialBaseLift z).1) :
    A.affineOrderFourPrincipalGaugeRegularBase q =
      A.affineOrderFourRadialBaseLift z := by
  apply Subtype.ext
  exact (A.affineOrderFourPrincipalGaugeRegularBase_val q).trans hbase

/-- The order-three principal-gauge base and the radial lift have the same explicit normalized
strip coordinate. -/
public theorem regularCoordinate_affineOrderThreePrincipalGaugeRegularBase
    (A : PaperAnalyticData) (z : affineVerticalStrip)
    (q : A.orderThreeCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.affineOrderThreeRadialBaseLift z).1) :
    A.regularCoordinate (A.affineOrderThreePrincipalGaugeRegularBase q) =
      A.affineOrderThreeNormalizedBaseCoordinate z := by
  rw [A.affineOrderThreePrincipalGaugeRegularBase_eq_radialBaseLift z q hbase]
  exact A.regularCoordinate_affineOrderThreeRadialBaseLift z

/-- The order-four principal-gauge base and the radial lift have the same explicit normalized
strip coordinate. -/
public theorem regularCoordinate_affineOrderFourPrincipalGaugeRegularBase
    (A : PaperAnalyticData) (z : affineVerticalStrip)
    (q : A.orderFourCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.affineOrderFourRadialBaseLift z).1) :
    A.regularCoordinate (A.affineOrderFourPrincipalGaugeRegularBase q) =
      A.affineOrderFourNormalizedBaseCoordinate z := by
  rw [A.affineOrderFourPrincipalGaugeRegularBase_eq_radialBaseLift z q hbase]
  exact A.regularCoordinate_affineOrderFourRadialBaseLift z

end SphereSixComplex.Geometry.PaperAnalyticData

end
