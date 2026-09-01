module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The local fixed-base fibre loop after removing the constant collar offset. -/
public noncomputable def orderFourCentralPrincipalGaugeFiberPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0))
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact ((Path.refl A.orderFourCayleyPuncturedBasepoint).prod
    A.orderFourFillingRelationPrincipalGaugeLoop).map
      A.orderFourPuncturedProductCentralRealizationMap.continuous

/-- Contracting the collar offset gives a free homotopy to the literal principal-gauge fibre
loop. -/
public def orderFourCentralFiberFactor_offsetHomotopy :
    letI := A.orderFourActualEllipticBoundaryAction
    ContinuousMap.Homotopy A.orderFourCentralFiberFactor.toContinuousMap
      A.orderFourCentralPrincipalGaugeFiberPath.toContinuousMap := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let f := A.orderFourPuncturedProductCentralRealizationMap
  let Hoffset := A.orderFourPrincipalGaugeOffsetHomotopy
  exact
    { toFun := fun st ↦ f (x, Hoffset st)
      continuous_toFun := f.continuous.comp
        (continuous_const.prodMk Hoffset.continuous)
      map_zero_left := by
        intro t
        change f (x, Hoffset (0, t)) = f (x, A.orderFourPrincipalGaugeWithOffsetPath t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_zero_left t)
      map_one_left := by
        intro t
        change f (x, Hoffset (1, t)) =
          f (x, A.orderFourFillingRelationPrincipalGaugeLoop t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_one_left t) }

/-- The offset contraction has equal loop-endpoint traces. -/
public theorem orderFourCentralFiberFactor_offsetHomotopy_trace
    (s : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    let H := A.orderFourCentralFiberFactor_offsetHomotopy
    H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourCayleyPuncturedBasepoint,
        A.orderFourPrincipalGaugeOffsetHomotopy (s, 0)) =
    A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourCayleyPuncturedBasepoint,
        A.orderFourPrincipalGaugeOffsetHomotopy (s, 1))
  apply congrArg (fun q ↦ A.orderFourPuncturedProductCentralRealizationMap
    (A.orderFourCayleyPuncturedBasepoint, q))
  change A.orderFourFillingRelationPrincipalGaugeLoop 0 + _ =
    A.orderFourFillingRelationPrincipalGaugeLoop 1 + _
  rw [A.orderFourFillingRelationPrincipalGaugeLoop.source,
    A.orderFourFillingRelationPrincipalGaugeLoop.target]

/-- The same fixed-base fibre loop, using the straight cover segment with the classified
period endpoint. -/
public noncomputable def orderFourCentralPrincipalGaugeStraightFiberPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0))
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let q := A.orderFourPrincipalGaugeStraightLoop
  have hbase :
      torusProjection
          (AnalyticTorusFamily.parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1
          (A.orderFourFillingRelationPrincipalGaugeCoverLift 0) =
        A.orderFourFillingRelationPrincipalGaugeLoop 0 := by
    rfl
  exact (((Path.refl A.orderFourCayleyPuncturedBasepoint).prod q).map
    A.orderFourPuncturedProductCentralRealizationMap.continuous).cast
      (congrArg
        (fun z ↦ A.orderFourPuncturedProductCentralRealizationMap
          (A.orderFourCayleyPuncturedBasepoint, z)) hbase)
      (congrArg
        (fun z ↦ A.orderFourPuncturedProductCentralRealizationMap
          (A.orderFourCayleyPuncturedBasepoint, z)) hbase)

/-- Equality of the two fixed-torus path classes yields an endpoint-relative homotopy after
mapping through the local central realization. -/
public theorem orderFourCentralPrincipalGaugeFiberPath_homotopic_straight :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (Path.Homotopy A.orderFourCentralPrincipalGaugeFiberPath
      A.orderFourCentralPrincipalGaugeStraightFiberPath) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have hclass := A.orderFourFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderFourFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderFourPrincipalGaugeStraightLoop at hclass
  have htorus : Path.Homotopic A.orderFourFillingRelationPrincipalGaugeLoop
      A.orderFourPrincipalGaugeStraightLoop := Quotient.exact hclass
  rcases htorus with ⟨Htorus⟩
  let f : C(A.orderFourTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint, q)
      continuous_toFun := A.orderFourPuncturedProductCentralRealizationMap.continuous.comp
        (continuous_const.prodMk continuous_id) }
  let Hmapped := Htorus.map f
  have hsource :
      A.orderFourFillingRelationPrincipalGaugeLoop.map f.continuous =
        A.orderFourCentralPrincipalGaugeFiberPath := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      A.orderFourPrincipalGaugeStraightLoop.map f.continuous =
        A.orderFourCentralPrincipalGaugeStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩

/-- The local fibre factor is freely homotopic, with equal endpoint traces, to the central
realization of the classified straight period loop. -/
public theorem orderFourCentralFiberFactor_homotopy_localStraight_with_trace :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy A.orderFourCentralFiberFactor.toContinuousMap
        A.orderFourCentralPrincipalGaugeStraightFiberPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let Hoffset := A.orderFourCentralFiberFactor_offsetHomotopy
  rcases A.orderFourCentralPrincipalGaugeFiberPath_homotopic_straight with ⟨Hpath⟩
  let Hstraight := pathHomotopyToFreeHomotopy Hpath
  let H := Hoffset.trans Hstraight
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact A.orderFourCentralFiberFactor_offsetHomotopy_trace r
  · intro r
    exact (Hpath.source r).trans (Hpath.target r).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
