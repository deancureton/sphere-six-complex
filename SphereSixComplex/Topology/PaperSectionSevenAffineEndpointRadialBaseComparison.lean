module

public import SphereSixComplex.Topology.PaperSectionSevenAffinePrincipalGaugeRadialBaseSquare

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
public def sectionSevenAffineOrderThreeHalfPlaneBaseLift
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, A.orderThreeAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.sectionSevenAffineNamedStripLift.lift z, by
      change (A.regularCoordinate (A.sectionSevenAffineNamedStripLift.lift z)).1.re < 2 / 3
      rw [A.sectionSevenAffineNamedStripLift.lift_coordinate]
      exact z.2.2⟩,
    A.sectionSevenAffineNamedStripLift.lift.continuous.subtype_mk _⟩

/-- The named strip lift, regarded as a point of the order-four half-plane preimage. -/
public def sectionSevenAffineOrderFourHalfPlaneBaseLift
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, A.orderFourAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.sectionSevenAffineNamedStripLift.lift z, by
      change 1 / 3 < (A.regularCoordinate
        (A.sectionSevenAffineNamedStripLift.lift z)).1.re
      rw [A.sectionSevenAffineNamedStripLift.lift_coordinate]
      exact z.2.1⟩,
    A.sectionSevenAffineNamedStripLift.lift.continuous.subtype_mk _⟩

/-- The order-three half-plane coordinate carried by the named strip lift. -/
public noncomputable def sectionSevenAffineOrderThreeHalfPlaneCoordinate
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, orderThreeAffineHalfPlaneCoordinateRegion) :=
  ⟨fun z ↦
      ⟨A.regularCoordinate (A.sectionSevenAffineOrderThreeHalfPlaneBaseLift z).1,
        (A.sectionSevenAffineOrderThreeHalfPlaneBaseLift z).2⟩,
    (A.regularCoordinate_isLocalHomeomorph.continuous.comp
      (continuous_subtype_val.comp
        A.sectionSevenAffineOrderThreeHalfPlaneBaseLift.continuous)).subtype_mk _⟩

/-- The order-four half-plane coordinate carried by the named strip lift. -/
public noncomputable def sectionSevenAffineOrderFourHalfPlaneCoordinate
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, orderFourAffineHalfPlaneCoordinateRegion) :=
  ⟨fun z ↦
      ⟨A.regularCoordinate (A.sectionSevenAffineOrderFourHalfPlaneBaseLift z).1,
        (A.sectionSevenAffineOrderFourHalfPlaneBaseLift z).2⟩,
    (A.regularCoordinate_isLocalHomeomorph.continuous.comp
      (continuous_subtype_val.comp
        A.sectionSevenAffineOrderFourHalfPlaneBaseLift.continuous)).subtype_mk _⟩

/-- The order-three inverse radial lift over the named strip. -/
public noncomputable def sectionSevenAffineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  ⟨fun z ↦ ((A.orderThreeBaseRadialEquiv
      (s := r / 2) (by linarith) (by linarith) hr).invFun
        (A.sectionSevenAffineOrderThreeHalfPlaneBaseLift z)).1,
    continuous_subtype_val.comp
      ((A.orderThreeBaseRadialEquiv
        (s := r / 2) (by linarith) (by linarith) hr).invFun.continuous.comp
          A.sectionSevenAffineOrderThreeHalfPlaneBaseLift.continuous)⟩

/-- The order-four inverse radial lift over the named strip. -/
public noncomputable def sectionSevenAffineOrderFourRadialBaseLift
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  ⟨fun z ↦ ((A.orderFourBaseRadialEquiv
      (s := r / 2) (by linarith) (by linarith) hr).invFun
        (A.sectionSevenAffineOrderFourHalfPlaneBaseLift z)).1,
    continuous_subtype_val.comp
      ((A.orderFourBaseRadialEquiv
        (s := r / 2) (by linarith) (by linarith) hr).invFun.continuous.comp
          A.sectionSevenAffineOrderFourHalfPlaneBaseLift.continuous)⟩

/-- The normalized order-three coordinate map on the affine strip. -/
public noncomputable def sectionSevenAffineOrderThreeNormalizedBaseCoordinate
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, RegularCoordinateBase) :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let D := orderThreeCoordinateDeformation
    (s := r / 2) (by linarith) (by linarith) hr
  ⟨fun z ↦ (D.normalize (A.sectionSevenAffineOrderThreeHalfPlaneCoordinate z)).1,
    continuous_subtype_val.comp
      (D.normalize.continuous.comp
        A.sectionSevenAffineOrderThreeHalfPlaneCoordinate.continuous)⟩

/-- The normalized order-four coordinate map on the affine strip. -/
public noncomputable def sectionSevenAffineOrderFourNormalizedBaseCoordinate
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, RegularCoordinateBase) :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let D := orderFourCoordinateDeformation
    (s := r / 2) (by linarith) (by linarith) hr
  ⟨fun z ↦ (D.normalize (A.sectionSevenAffineOrderFourHalfPlaneCoordinate z)).1,
    continuous_subtype_val.comp
      (D.normalize.continuous.comp
        A.sectionSevenAffineOrderFourHalfPlaneCoordinate.continuous)⟩

/-- The order-three radial base lift projects to the explicit normalized strip coordinate. -/
public theorem regularCoordinate_sectionSevenAffineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    A.regularCoordinate (A.sectionSevenAffineOrderThreeRadialBaseLift z) =
      A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate z := by
  dsimp only [sectionSevenAffineOrderThreeRadialBaseLift,
    sectionSevenAffineOrderThreeNormalizedBaseCoordinate,
    sectionSevenAffineOrderThreeHalfPlaneCoordinate]
  exact A.orderThreeBaseRadialEquiv_invFun_regularCoordinate _ _ _ _

/-- The order-four radial base lift projects to the explicit normalized strip coordinate. -/
public theorem regularCoordinate_sectionSevenAffineOrderFourRadialBaseLift
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    A.regularCoordinate (A.sectionSevenAffineOrderFourRadialBaseLift z) =
      A.sectionSevenAffineOrderFourNormalizedBaseCoordinate z := by
  dsimp only [sectionSevenAffineOrderFourRadialBaseLift,
    sectionSevenAffineOrderFourNormalizedBaseCoordinate,
    sectionSevenAffineOrderFourHalfPlaneCoordinate]
  exact A.orderFourBaseRadialEquiv_invFun_regularCoordinate _ _ _ _

/-- Continuous-map form of the order-three radial base square. -/
public theorem regularCoordinate_comp_sectionSevenAffineOrderThreeRadialBaseLift
    (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.sectionSevenAffineOrderThreeRadialBaseLift =
      A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate := by
  funext z
  exact A.regularCoordinate_sectionSevenAffineOrderThreeRadialBaseLift z

/-- Continuous-map form of the order-four radial base square. -/
public theorem regularCoordinate_comp_sectionSevenAffineOrderFourRadialBaseLift
    (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.sectionSevenAffineOrderFourRadialBaseLift =
      A.sectionSevenAffineOrderFourNormalizedBaseCoordinate := by
  funext z
  exact A.regularCoordinate_sectionSevenAffineOrderFourRadialBaseLift z

/-! ## The principal-gauge leg of the radial base square -/

/-- The regular base obtained after applying the order-three principal gauge to a selected
collar representative. -/
public noncomputable def sectionSevenAffineOrderThreePrincipalGaugeRegularBase
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
public noncomputable def sectionSevenAffineOrderFourPrincipalGaugeRegularBase
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
public theorem sectionSevenAffineOrderThreePrincipalGaugeRegularBase_val
    (A : PaperAnalyticData) (q : A.orderThreeCollarCarrier.carrier) :
    (A.sectionSevenAffineOrderThreePrincipalGaugeRegularBase q).1 =
      familyTotalSpaceBase A.periods q.1 := by
  unfold sectionSevenAffineOrderThreePrincipalGaugeRegularBase
  exact orderThreeCollarToRegular_principalGauge_base A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.sourceData q

/-- The order-four principal-gauge regular base retains the base of its collar
representative. -/
public theorem sectionSevenAffineOrderFourPrincipalGaugeRegularBase_val
    (A : PaperAnalyticData) (q : A.orderFourCollarCarrier.carrier) :
    (A.sectionSevenAffineOrderFourPrincipalGaugeRegularBase q).1 =
      familyTotalSpaceBase A.periods q.1 := by
  unfold sectionSevenAffineOrderFourPrincipalGaugeRegularBase
  exact orderFourCollarToRegular_principalGauge_base A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.sourceData q

/-- An order-three collar representative over the named radial strip produces exactly the
named radial base lift after applying the principal gauge. -/
public theorem sectionSevenAffineOrderThreePrincipalGaugeRegularBase_eq_radialBaseLift
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip)
    (q : A.orderThreeCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.sectionSevenAffineOrderThreeRadialBaseLift z).1) :
    A.sectionSevenAffineOrderThreePrincipalGaugeRegularBase q =
      A.sectionSevenAffineOrderThreeRadialBaseLift z := by
  apply Subtype.ext
  exact (A.sectionSevenAffineOrderThreePrincipalGaugeRegularBase_val q).trans hbase

/-- An order-four collar representative over the named radial strip produces exactly the
named radial base lift after applying the principal gauge. -/
public theorem sectionSevenAffineOrderFourPrincipalGaugeRegularBase_eq_radialBaseLift
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip)
    (q : A.orderFourCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.sectionSevenAffineOrderFourRadialBaseLift z).1) :
    A.sectionSevenAffineOrderFourPrincipalGaugeRegularBase q =
      A.sectionSevenAffineOrderFourRadialBaseLift z := by
  apply Subtype.ext
  exact (A.sectionSevenAffineOrderFourPrincipalGaugeRegularBase_val q).trans hbase

/-- The order-three principal-gauge base and the radial lift have the same explicit normalized
strip coordinate. -/
public theorem regularCoordinate_sectionSevenAffineOrderThreePrincipalGaugeRegularBase
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip)
    (q : A.orderThreeCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.sectionSevenAffineOrderThreeRadialBaseLift z).1) :
    A.regularCoordinate (A.sectionSevenAffineOrderThreePrincipalGaugeRegularBase q) =
      A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate z := by
  rw [A.sectionSevenAffineOrderThreePrincipalGaugeRegularBase_eq_radialBaseLift z q hbase]
  exact A.regularCoordinate_sectionSevenAffineOrderThreeRadialBaseLift z

/-- The order-four principal-gauge base and the radial lift have the same explicit normalized
strip coordinate. -/
public theorem regularCoordinate_sectionSevenAffineOrderFourPrincipalGaugeRegularBase
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip)
    (q : A.orderFourCollarCarrier.carrier)
    (hbase : familyTotalSpaceBase A.periods q.1 =
      (A.sectionSevenAffineOrderFourRadialBaseLift z).1) :
    A.regularCoordinate (A.sectionSevenAffineOrderFourPrincipalGaugeRegularBase q) =
      A.sectionSevenAffineOrderFourNormalizedBaseCoordinate z := by
  rw [A.sectionSevenAffineOrderFourPrincipalGaugeRegularBase_eq_radialBaseLift z q hbase]
  exact A.regularCoordinate_sectionSevenAffineOrderFourRadialBaseLift z

end SphereSixComplex.Geometry.PaperAnalyticData

end
