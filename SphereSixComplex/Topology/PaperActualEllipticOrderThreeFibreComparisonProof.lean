module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeBaseFactorHomotopyProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The local fixed-base fibre loop after removing the constant collar offset. -/
public noncomputable def orderThreeCentralPrincipalGaugeFiberPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact ((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
    A.orderThreeFillingRelationPrincipalGaugeLoop).map
      A.orderThreePuncturedProductToCentralMap.continuous

/-- Contracting the collar offset gives a free homotopy to the principal-gauge fibre loop. -/
public def orderThreeLocalOffsetFiberCentralPath_offsetHomotopy :
    letI := A.orderThreeActualEllipticBoundaryAction
    ContinuousMap.Homotopy A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeCentralPrincipalGaugeFiberPath.toContinuousMap := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let x := A.orderThreeCayleyPuncturedBasepoint
  let f := A.orderThreePuncturedProductToCentralMap
  let Hoffset := A.orderThreePrincipalGaugeOffsetHomotopy
  exact
    { toFun := fun st ↦ f (x, Hoffset st)
      continuous_toFun := f.continuous.comp
        (continuous_const.prodMk Hoffset.continuous)
      map_zero_left := by
        intro t
        change f (x, Hoffset (0, t)) = f (x, A.orderThreePrincipalGaugeWithOffsetPath t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_zero_left t)
      map_one_left := by
        intro t
        change f (x, Hoffset (1, t)) =
          f (x, A.orderThreeFillingRelationPrincipalGaugeLoop t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_one_left t) }

public theorem orderThreeLocalOffsetFiberCentralPath_offsetHomotopy_trace
    (s : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let H := A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy
    H (s, 0) = H (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  change A.orderThreePuncturedProductToCentralMap
      (A.orderThreeCayleyPuncturedBasepoint,
        A.orderThreePrincipalGaugeOffsetHomotopy (s, 0)) =
    A.orderThreePuncturedProductToCentralMap
      (A.orderThreeCayleyPuncturedBasepoint,
        A.orderThreePrincipalGaugeOffsetHomotopy (s, 1))
  apply congrArg (fun q ↦ A.orderThreePuncturedProductToCentralMap
    (A.orderThreeCayleyPuncturedBasepoint, q))
  change A.orderThreeFillingRelationPrincipalGaugeLoop 0 + _ =
    A.orderThreeFillingRelationPrincipalGaugeLoop 1 + _
  rw [A.orderThreeFillingRelationPrincipalGaugeLoop.source,
    A.orderThreeFillingRelationPrincipalGaugeLoop.target]

/-- The fixed-base local realization of the classified straight period segment. -/
public noncomputable def orderThreeCentralPrincipalGaugeStraightFiberPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let q := A.orderThreePrincipalGaugeStraightLoop
  have hbase :
      torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1
          (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) =
        A.orderThreeFillingRelationPrincipalGaugeLoop 0 := by
    rfl
  exact (((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod q).map
    A.orderThreePuncturedProductToCentralMap.continuous).cast
      (congrArg
        (fun z ↦ A.orderThreePuncturedProductToCentralMap
          (A.orderThreeCayleyPuncturedBasepoint, z)) hbase)
      (congrArg
        (fun z ↦ A.orderThreePuncturedProductToCentralMap
          (A.orderThreeCayleyPuncturedBasepoint, z)) hbase)

public theorem orderThreeCentralPrincipalGaugeFiberPath_homotopic_straight :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (Path.Homotopy A.orderThreeCentralPrincipalGaugeFiberPath
      A.orderThreeCentralPrincipalGaugeStraightFiberPath) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have hclass := A.orderThreeFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderThreeFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderThreePrincipalGaugeStraightLoop at hclass
  have htorus : Path.Homotopic A.orderThreeFillingRelationPrincipalGaugeLoop
      A.orderThreePrincipalGaugeStraightLoop := Quotient.exact hclass
  rcases htorus with ⟨Htorus⟩
  let f : C(A.orderThreeTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, q)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk continuous_id) }
  let Hmapped := Htorus.map f
  have hsource :
      A.orderThreeFillingRelationPrincipalGaugeLoop.map f.continuous =
        A.orderThreeCentralPrincipalGaugeFiberPath := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      A.orderThreePrincipalGaugeStraightLoop.map f.continuous =
        A.orderThreeCentralPrincipalGaugeStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩

public theorem orderThreeLocalOffsetFiberCentralPath_homotopy_localStraight_with_trace :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
        A.orderThreeCentralPrincipalGaugeStraightFiberPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let Hoffset := A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy
  rcases A.orderThreeCentralPrincipalGaugeFiberPath_homotopic_straight with ⟨Hpath⟩
  let Hstraight := pathHomotopyToFreeHomotopy Hpath
  let H := Hoffset.trans Hstraight
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy_trace r
  · intro r
    exact (Hpath.source r).trans (Hpath.target r).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
