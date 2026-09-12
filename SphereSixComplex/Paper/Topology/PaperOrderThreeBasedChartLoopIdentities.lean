module

public import SphereSixComplex.Paper.Topology.PaperOrderThreeCentralBoundaryCoverComparison

/-!
# Literal loops for the based order-three boundary comparison

The physical translation and positive angular generators are represented here by straight paths
from the selected point of the explicit radial cover to its deck translates.  Their projections
are proved to represent the corresponding `ofDeck` classes.  This reduces the based chart
comparison to exact equalities between these concrete projected paths and the already constructed
global period and finite-meridian loops, transported along one fixed path.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : AnalyticData)

/-- The straight path in the explicit radial cover from its selected basepoint to a deck
translate.  The radial coordinate is fixed and the affine cover coordinates follow the segment
joining the two endpoints. -/
public noncomputable def ellipticThreeBoundaryDeckStraightLift
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    Path A.ellipticThreeBoundaryBase
      (g • A.ellipticThreeBoundaryBase) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  let b := A.ellipticThreeBoundaryBase
  exact {
    toFun := fun t ↦ (b.1, Path.segment b.2 (g • b.2) t)
    continuous_toFun :=
      continuous_const.prodMk (Path.segment b.2 (g • b.2)).continuous
    source' := by rw [(Path.segment b.2 (g • b.2)).source]
    target' := by
      rw [(Path.segment b.2 (g • b.2)).target]
      change (b.1, g • b.2) = (b.1, g • b.2)
      rfl
  }

/-- Projection of the straight deck path is a loop in the literal order-three overlap. -/
public noncomputable def ellipticThreeBoundaryDeckStraightLoop
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    Path
      (A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase)
      (A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
  exact ((A.ellipticThreeBoundaryDeckStraightLift g).map
      A.ellipticThreeBoundaryProjection.continuous).cast rfl
        (hp.map_smul g).symm

/-- The straight projected loop represents exactly the `ofDeck` class with the same deck
label.  In particular, no inverse is introduced at this stage. -/
public theorem ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    Path.Homotopic.Quotient.mk (A.ellipticThreeBoundaryDeckStraightLoop g) =
      ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase g := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
  let e : A.ellipticThreeBoundaryProjection ⁻¹'
      {A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase} :=
    ⟨A.ellipticThreeBoundaryBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  let e' : A.ellipticThreeBoundaryProjection ⁻¹'
      {A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase} :=
    ⟨g • A.ellipticThreeBoundaryBase, hp.map_smul g⟩
  let Γ : Path.Homotopic.Quotient A.ellipticThreeBoundaryBase
      (g • A.ellipticThreeBoundaryBase) :=
    Path.Homotopic.Quotient.mk (A.ellipticThreeBoundaryDeckStraightLift g)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq (ex := e) (ey := e') Γ (by
    dsimp [e, e']
    change (Path.Homotopic.Quotient.mk
        (A.ellipticThreeBoundaryDeckStraightLift g)).map
          A.ellipticThreeBoundaryProjection =
      (Path.Homotopic.Quotient.mk
        (A.ellipticThreeBoundaryDeckStraightLoop g)).cast _ _
    rw [← Path.Homotopic.Quotient.mk_map]
    unfold ellipticThreeBoundaryDeckStraightLoop
    rw [Path.Homotopic.Quotient.mk_cast]
    exact eq_of_heq
      ((Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm








end SphereSixComplex.Geometry.AnalyticData

end

end
