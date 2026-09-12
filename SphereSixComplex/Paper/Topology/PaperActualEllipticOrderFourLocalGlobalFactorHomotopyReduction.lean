module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeLocalGlobalFactorHomotopyReduction

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap


namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus

variable (A : AnalyticData)

public theorem ellipticFourCentralBase_eq_offsetGaugeRealization :
    letI := A.ellipticFourBoundaryAction
    A.ellipticFourCentralBase =
      A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0 +
            Quotient.mk _ A.ellipticFourBoundaryBase.2.2) := by
  let _ := A.ellipticFourBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.ellipticFourBoundaryBase.2.2
  have hregular : A.orderFourCollarRegularRepresentativeMap
      A.ellipticFourBoundaryBase =
        A.orderFourPuncturedProductRegularRealizationMap (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg A.orderFourPuncturedProductRegularRealizationMap
          (Prod.ext A.orderFourFillingRelationCayleyPuncturedLoop.source
            A.orderFourPrincipalGaugeWithOffsetPath.source)))
  exact A.orderFourCollarRegularRepresentative_base_projects.symm.trans
    (congrArg A.centralQuotientProjection hregular)

/-- The classified straight period, translated by the collar offset so that it remains based
at the actual elliptic point. -/
public noncomputable def orderFourCentralActualBasedStraightFiberPath :
    letI := A.ellipticFourBoundaryAction
    Path A.ellipticFourCentralBase A.ellipticFourCentralBase := by
  let _ := A.ellipticFourBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let offset : A.OrderFourTorus := Quotient.mk _ A.ellipticFourBoundaryBase.2.2
  let g : C(A.OrderFourTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderFourPuncturedProductCentralRealizationMap (x, q + offset)
      continuous_toFun := A.orderFourPuncturedProductCentralRealizationMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  let qbase := torusProjection
    (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo).1
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
  have hqbase : qbase = A.orderFourFillingRelationPrincipalGaugeLoop 0 := by
    rfl
  have hbase : A.ellipticFourCentralBase =
      g qbase :=
    (ellipticFourCentralBase_eq_offsetGaugeRealization A).trans
      (congrArg g hqbase).symm
  exact (A.orderFourPrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase

/-- Straightening can be performed after translating by the fixed collar offset, hence with
the actual elliptic basepoint fixed throughout. -/
public theorem orderFourCentralFiberFactor_homotopic_actualBasedStraight :
    letI := A.ellipticFourBoundaryAction
    Nonempty (Path.Homotopy A.orderFourCentralFiberFactor
      A.orderFourCentralActualBasedStraightFiberPath) := by
  let _ := A.ellipticFourBoundaryAction
  have hclass := A.orderFourFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderFourFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderFourPrincipalGaugeStraightLoop at hclass
  rcases (Quotient.exact hclass : Path.Homotopic
    A.orderFourFillingRelationPrincipalGaugeLoop
      A.orderFourPrincipalGaugeStraightLoop) with ⟨Htorus⟩
  let x := A.orderFourCayleyPuncturedBasepoint
  let offset : A.OrderFourTorus := Quotient.mk _ A.ellipticFourBoundaryBase.2.2
  let g : C(A.OrderFourTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderFourPuncturedProductCentralRealizationMap (x, q + offset)
      continuous_toFun := A.orderFourPuncturedProductCentralRealizationMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  have hbase : A.ellipticFourCentralBase =
      g (A.orderFourFillingRelationPrincipalGaugeLoop 0) :=
    ellipticFourCentralBase_eq_offsetGaugeRealization A
  let Hmapped := (Htorus.map g).pathCast hbase hbase
  have hsource :
      (A.orderFourFillingRelationPrincipalGaugeLoop.map g.continuous).cast hbase hbase =
        A.orderFourCentralFiberFactor := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      (A.orderFourPrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase =
        A.orderFourCentralActualBasedStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩


end SphereSixComplex.Geometry.AnalyticData

end

end
