module

public import SphereSixComplex.Paper.Topology.PaperOrderThreeBasedChartLoopIdentities
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourCentralConnectorCoherence

/-!
# Local marked-loop inputs for the actual elliptic collars
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology


public theorem mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (a : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq f h a =
      fundamentalGroupElementOfBaseEq h
        (FundamentalGroup.mapOfEq f rfl a) := by
  subst y
  rfl

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)





public noncomputable def ellipticFourBoundaryDeckStraightLift
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    Path A.ellipticFourBoundaryBase
      (g • A.ellipticFourBoundaryBase) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  let b := A.ellipticFourBoundaryBase
  exact {
    toFun := fun t ↦ (b.1, Path.segment b.2 (g • b.2) t)
    continuous_toFun :=
      continuous_const.prodMk (Path.segment b.2 (g • b.2)).continuous
    source' := by rw [(Path.segment b.2 (g • b.2)).source]
    target' := by
      rw [(Path.segment b.2 (g • b.2)).target]
      rfl
  }

public noncomputable def ellipticFourBoundaryDeckStraightLoop
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    Path
      (A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase)
      (A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
  exact ((A.ellipticFourBoundaryDeckStraightLift g).map
      A.ellipticFourBoundaryProjection.continuous).cast rfl
        (hp.map_smul g).symm

public theorem ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    Path.Homotopic.Quotient.mk (A.ellipticFourBoundaryDeckStraightLoop g) =
      ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase g := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
  let e : A.ellipticFourBoundaryProjection ⁻¹'
      {A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase} :=
    ⟨A.ellipticFourBoundaryBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  let e' : A.ellipticFourBoundaryProjection ⁻¹'
      {A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase} :=
    ⟨g • A.ellipticFourBoundaryBase, hp.map_smul g⟩
  let Γ : Path.Homotopic.Quotient A.ellipticFourBoundaryBase
      (g • A.ellipticFourBoundaryBase) :=
    Path.Homotopic.Quotient.mk (A.ellipticFourBoundaryDeckStraightLift g)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq (ex := e) (ey := e') Γ (by
    dsimp [e, e']
    change (Path.Homotopic.Quotient.mk
        (A.ellipticFourBoundaryDeckStraightLift g)).map
          A.ellipticFourBoundaryProjection =
      (Path.Homotopic.Quotient.mk
        (A.ellipticFourBoundaryDeckStraightLoop g)).cast _ _
    rw [← Path.Homotopic.Quotient.mk_map]
    unfold ellipticFourBoundaryDeckStraightLoop
    rw [Path.Homotopic.Quotient.mk_cast]
    exact eq_of_heq
      ((Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm





end SphereSixComplex.Geometry.PaperAnalyticData

end

end
