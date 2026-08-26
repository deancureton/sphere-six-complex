module

public import SphereSixComplex.Geometry.PaperMarkedPuncturedBase
public import SphereSixComplex.Topology.PaperActualCuspCentralBaseMap

/-!
# The actual marked angular loop of the paper cusp

The chosen cusp-boundary meridian is represented here by the literal straight path in the
additive logarithm coordinate.  Its endpoint is the actual semidirect-product deck translate,
so covering monodromy identifies its projection with the `ofDeck` class used by the affine
filling interface.  This removes any source-side generator choice from the cusp comparison.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open CuspPeriodExpansion CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The straight angular path `s \mapsto s - t` in the actual additive cusp cover. -/
public def actualCuspAngularLiftPoint (t : unitInterval) :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  ⟨(A.actualCuspBoundaryCoverBase.1.1,
      A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ)), by
    change ‖cuspQ (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))‖ <
      A.starCuspWitness.localWitness.radius
    have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.actualCuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase⟩

@[simp]
public theorem actualCuspAngularLiftPoint_zero :
    A.actualCuspAngularLiftPoint 0 = A.actualCuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [actualCuspAngularLiftPoint]

@[simp]
public theorem actualCuspAngularLiftPoint_one :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    A.actualCuspAngularLiftPoint 1 =
      paperCuspBoundaryMeridian • A.actualCuspBoundaryCoverBase := by
  let _ := paperCuspBoundaryDeckAction A.starCuspWitness
  change A.actualCuspAngularLiftPoint 1 =
    cuspBoundaryLatticeTranslate A.starCuspWitness 0
      (cuspBoundaryAngularTranslate A.starCuspWitness 1
        A.actualCuspBoundaryCoverBase)
  rw [cuspBoundaryLatticeTranslate_zero]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [actualCuspAngularLiftPoint, cuspBoundaryAngularTranslate]

/-- The actual lifted angular path, retaining its deck-labelled endpoint. -/
public def actualCuspAngularLiftPath :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    Path A.actualCuspBoundaryCoverBase
      (paperCuspBoundaryMeridian • A.actualCuspBoundaryCoverBase) where
  toFun := A.actualCuspAngularLiftPoint
  continuous_toFun := by
    unfold actualCuspAngularLiftPoint
    apply Continuous.subtype_mk
    fun_prop
  source' := A.actualCuspAngularLiftPoint_zero
  target' := A.actualCuspAngularLiftPoint_one

/-- Projection of the explicit angular lift, based literally at the projection of its selected
cover point. -/
public def actualCuspAngularProjectedLoop :
    Path (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase)
      (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase) := by
  let _ := paperCuspBoundaryDeckAction A.starCuspWitness
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap
      A.starCuspWitness).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
  exact (A.actualCuspAngularLiftPath.map
    A.actualCuspBoundaryProjection.continuous).cast
      rfl (hp.map_smul paperCuspBoundaryMeridian
        (e := A.actualCuspBoundaryCoverBase)).symm

/-- The same literal cusp loop after applying the actual collar chart into the central family. -/
public def actualCuspAngularCentralLoop :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  ((A.actualCuspAngularProjectedLoop.map
      A.actualCuspOverlapToCentral.continuous).cast
    (by
      rw [actualCuspCentralBase, A.actualCuspBoundaryCoverBase_projects])
    (by
      rw [actualCuspCentralBase, A.actualCuspBoundaryCoverBase_projects]))

/-- The actual normalized cusp loop in the marked twice-punctured base coordinate. -/
public def actualCuspAngularCoordinateLoop :
    Path (A.centralFamilyCoordinate A.actualCuspCentralBase)
      (A.centralFamilyCoordinate A.actualCuspCentralBase) :=
  A.actualCuspAngularCentralLoop.map A.centralFamilyCoordinate_continuous

/-- Pointwise, the coordinate loop is the normalized modular coordinate evaluated on the
literal angular path `s - t`. -/
public theorem actualCuspAngularCoordinateLoop_apply (t : unitInterval) :
    (A.actualCuspAngularCoordinateLoop t).1 =
      A.modular.sourceCoordinate.coordinate
        (A.cuspCoordinate.lift
          (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))) := by
  change (A.centralFamilyCoordinate
      (A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint t)))).1 = _
  rw [A.actualCuspOverlapToCentral_boundaryProjection]
  rfl

/-- The actual marked cusp loop remains outside the closed radius-two disc. -/
public theorem actualCuspAngularCoordinateLoop_norm_gt_two (t : unitInterval) :
    2 < ‖(A.actualCuspAngularCoordinateLoop t).1‖ := by
  rw [A.actualCuspAngularCoordinateLoop_apply]
  apply A.actualPuncturedCuspWitness_coordinate_exterior
  · apply mem_cuspHalfPlane_of_norm_cuspQ_lt
      A.starCuspWitness.localWitness.radius_le
    have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.actualCuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase
  · have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.actualCuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit projected angular loop is exactly the `ofDeck` meridian class used by the
chosen affine cusp filling. -/
theorem actualCuspAngularProjectedLoop_class_eq_ofDeck :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    Path.Homotopic.Quotient.mk A.actualCuspAngularProjectedLoop =
      ofDeck hp A.actualCuspBoundaryCoverBase paperCuspBoundaryMeridian := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  apply (hp.fundamentalGroupEquiv
    ⟨A.actualCuspBoundaryCoverBase, by
      change A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase = _
      rfl⟩).injective
  rw [fundamentalGroupEquiv_ofDeck]
  change hp.fundamentalGroupToMulOpposite
      ⟨A.actualCuspBoundaryCoverBase, by
        change A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase = _
        rfl⟩
      (Path.Homotopic.Quotient.mk A.actualCuspAngularProjectedLoop) =
    MulOpposite.op paperCuspBoundaryMeridian
  rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let Γ : Path.Homotopic.Quotient A.actualCuspBoundaryCoverBase
      (paperCuspBoundaryMeridian • A.actualCuspBoundaryCoverBase) :=
    Path.Homotopic.Quotient.mk A.actualCuspAngularLiftPath
  have hmono := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := ⟨A.actualCuspBoundaryCoverBase, by
      change A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase = _
      rfl⟩)
    (ey := ⟨paperCuspBoundaryMeridian • A.actualCuspBoundaryCoverBase, by
      change A.actualCuspBoundaryProjection
          (paperCuspBoundaryMeridian • A.actualCuspBoundaryCoverBase) =
        A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase
      exact hp.map_smul paperCuspBoundaryMeridian
        (e := A.actualCuspBoundaryCoverBase)⟩)
    Γ (by
      change (Path.Homotopic.Quotient.mk A.actualCuspAngularLiftPath).map
          A.actualCuspBoundaryProjection =
        (Path.Homotopic.Quotient.mk A.actualCuspAngularProjectedLoop).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold actualCuspAngularProjectedLoop
      rw [Path.Homotopic.Quotient.mk_cast,
        Path.Homotopic.Quotient.cast_cast]
      simp only [Path.Homotopic.Quotient.cast_rfl_rfl])
  simpa only [MulOpposite.unop_op] using congrArg Subtype.val hmono.symm

end SphereSixComplex.Geometry.PaperAnalyticData

end
