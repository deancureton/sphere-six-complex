module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeFullProductCoordinateProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

public def freePathHomotopySwapExtend
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) :
    C(ℝ, C(unitInterval, X)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry.IccExtend zero_le_one

public theorem freePathHomotopySwapExtend_apply_coe
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (s t : unitInterval) :
    freePathHomotopySwapExtend H t s = H (s, t) := by
  rw [freePathHomotopySwapExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem]
  rfl

public theorem freePathHomotopySwapExtend_zero
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (t : ℝ) :
    freePathHomotopySwapExtend H t 0 = p.extend t := by
  rw [freePathHomotopySwapExtend, ContinuousMap.coe_IccExtend]
  change H (0, _) = p _
  exact H.map_zero_left _

public theorem freePathHomotopySwapExtend_one
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (t : ℝ) :
    freePathHomotopySwapExtend H t 1 = q.extend t := by
  rw [freePathHomotopySwapExtend, ContinuousMap.coe_IccExtend]
  change H (1, _) = q _
  exact H.map_one_left _

/-- Horizontal composition for free loop homotopies with a common moving basepoint. -/
public def freeLoopHomotopyHcomp
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0)) :
    ContinuousMap.Homotopy (p₀.trans q₀).toContinuousMap
      (p₁.trans q₁).toContinuousMap where
  toFun x := if (x.2 : ℝ) ≤ 1 / 2 then
      freePathHomotopySwapExtend H (2 * x.2) x.1
    else freePathHomotopySwapExtend K (2 * x.2 - 1) x.1
  continuous_toFun := by
    have hcontH : Continuous (fun x : unitInterval × unitInterval ↦
        freePathHomotopySwapExtend H (2 * x.2) x.1) := by fun_prop
    have hcontK : Continuous (fun x : unitInterval × unitInterval ↦
        freePathHomotopySwapExtend K (2 * x.2 - 1) x.1) := by fun_prop
    apply continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
      hcontH.continuousOn hcontK.continuousOn
    intro x hx
    change (x.2 : ℝ) = 1 / 2 at hx
    rw [hx]
    norm_num
    exact (freePathHomotopySwapExtend_apply_coe H x.1 1).trans
      ((hjoin x.1).trans
        (freePathHomotopySwapExtend_apply_coe K x.1 0).symm)
  map_zero_left t := by
    simp only [freePathHomotopySwapExtend_zero]
    rfl
  map_one_left t := by
    simp only [freePathHomotopySwapExtend_one]
    rfl

public theorem freeLoopHomotopyHcomp_apply
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0))
    (x : unitInterval × unitInterval) :
    freeLoopHomotopyHcomp H K hjoin x =
      if (x.2 : ℝ) ≤ 1 / 2 then
        freePathHomotopySwapExtend H (2 * x.2) x.1
      else freePathHomotopySwapExtend K (2 * x.2 - 1) x.1 := rfl

public theorem freeLoopHomotopyHcomp_trace
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0))
    (htrace : ∀ s : unitInterval, H (s, 0) = K (s, 1))
    (s : unitInterval) :
    freeLoopHomotopyHcomp H K hjoin (s, 0) =
      freeLoopHomotopyHcomp H K hjoin (s, 1) := by
  rw [freeLoopHomotopyHcomp_apply, freeLoopHomotopyHcomp_apply]
  norm_num
  exact (freePathHomotopySwapExtend_apply_coe H s 0).trans
    ((htrace s).trans
      (freePathHomotopySwapExtend_apply_coe K s 1).symm)

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The local offset-period factor of the punctured product splitting. -/
public noncomputable def orderThreeLocalOffsetFiberCentralPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact (((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
    A.orderThreePrincipalGaugeWithOffsetPath).map
      A.orderThreePuncturedProductToCentralMap.continuous).cast
        A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
        A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase

/-- The local base-circle factor, with its torus coordinate held fixed. -/
public noncomputable def orderThreeLocalOffsetBaseCentralPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
    (Path.refl (A.orderThreePrincipalGaugeWithOffsetPath 0))).map
      A.orderThreePuncturedProductToCentralMap.continuous).cast
        A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
        A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase

public theorem orderThreeLocalFiberThenBaseCentralPath_eq_trans :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeLocalFiberThenBaseCentralPath =
      A.orderThreeLocalOffsetFiberCentralPath.trans
        A.orderThreeLocalOffsetBaseCentralPath := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  unfold orderThreeLocalFiberThenBaseCentralPath
    orderThreeLocalOffsetFiberCentralPath orderThreeLocalOffsetBaseCentralPath
  rw [Path.map_trans]
  rfl

/-- The corrected cusp period displayed at the final affine basepoint. -/
public noncomputable def orderThreeCentralAffineCorrectedEpsilonPeriodPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderThreeActualCuspCorrectedEpsilonPeriodPath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

/-- The global zero-section triple displayed at the final affine basepoint. -/
public noncomputable def orderThreeCentralAffineZeroSectionTriplePath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderThreeActualCuspZeroSectionTriplePath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderThreeCentralAffineCorrectedGeometricRelatorPath_eq_trans :
    A.orderThreeCentralAffineCorrectedGeometricRelatorPath =
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.trans
        A.orderThreeCentralAffineZeroSectionTriplePath := by
  unfold orderThreeCentralAffineCorrectedGeometricRelatorPath
    orderThreeActualCuspCorrectedGeometricRelatorPath
    orderThreeCentralAffineCorrectedEpsilonPeriodPath
    orderThreeCentralAffineZeroSectionTriplePath
  rw [Path.cast_trans]

/-- The precise remaining geometric datum: the local fibre and base factors move to their
global counterparts through one common moving basepoint.  This is strictly point-set data, not
an equality of fundamental-group classes. -/
public def OrderThreeLocalGlobalFactorPointSetComparison : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  ∃ Hfiber : ContinuousMap.Homotopy
      A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap,
    ∃ Hbase : ContinuousMap.Homotopy
      A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap,
      (∀ s : unitInterval, Hfiber (s, 1) = Hbase (s, 0)) ∧
      (∀ s : unitInterval, Hfiber (s, 0) = Hbase (s, 1))

public theorem OrderThreeLocalGlobalFactorPointSetComparison.fiber
    (h : A.OrderThreeLocalGlobalFactorPointSetComparison) :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  exact ⟨Hfiber⟩

public theorem OrderThreeLocalGlobalFactorPointSetComparison.base
    (h : A.OrderThreeLocalGlobalFactorPointSetComparison) :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  exact ⟨Hbase⟩

public theorem OrderThreeLocalGlobalFactorPointSetComparison.factorConcatenation
    (h : A.OrderThreeLocalGlobalFactorPointSetComparison) :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
      (A.orderThreeLocalOffsetFiberCentralPath.trans
        A.orderThreeLocalOffsetBaseCentralPath).toContinuousMap
      (A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.trans
        A.orderThreeCentralAffineZeroSectionTriplePath).toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  let Hfactors := freeLoopHomotopyHcomp Hfiber Hbase hjoin
  exact ⟨Hfactors, freeLoopHomotopyHcomp_trace Hfiber Hbase hjoin htrace⟩

/-- The two coherent factor comparisons assemble to a free homotopy of the complete split
relator, with pointwise equal endpoint traces. -/
public theorem OrderThreeLocalGlobalFactorPointSetComparison.assemble
    (h : A.OrderThreeLocalGlobalFactorPointSetComparison) :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
      A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  let H := freeLoopHomotopyHcomp Hfiber Hbase hjoin
  have hsource :
      (A.orderThreeLocalOffsetFiberCentralPath.trans
        A.orderThreeLocalOffsetBaseCentralPath).toContinuousMap =
      A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap :=
    congrArg Path.toContinuousMap
      A.orderThreeLocalFiberThenBaseCentralPath_eq_trans.symm
  have htarget :
      (A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.trans
        A.orderThreeCentralAffineZeroSectionTriplePath).toContinuousMap =
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath.toContinuousMap :=
    congrArg Path.toContinuousMap
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath_eq_trans.symm
  let H' := H.cast hsource htarget
  refine ⟨H', ?_⟩
  intro s
  change H (s, 0) = H (s, 1)
  exact freeLoopHomotopyHcomp_trace Hfiber Hbase hjoin htrace s

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
