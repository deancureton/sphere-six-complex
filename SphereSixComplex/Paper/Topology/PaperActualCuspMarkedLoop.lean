module

public import SphereSixComplex.Paper.Geometry.PaperMarkedPuncturedBase
public import SphereSixComplex.Paper.Topology.PaperActualCuspCentralBaseMap

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
public def cuspAngularLiftPoint (t : unitInterval) :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  ⟨(A.cuspBoundaryCoverBase.1.1,
      A.cuspBoundaryCoverBase.1.2 - (t : ℝ)), by
    change ‖cuspQ (A.cuspBoundaryCoverBase.1.2 - (t : ℝ))‖ <
      A.starCuspWitness.localWitness.radius
    have hbase : ‖cuspQ A.cuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.cuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase⟩

@[simp]
public theorem cuspAngularLiftPoint_zero :
    A.cuspAngularLiftPoint 0 = A.cuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [cuspAngularLiftPoint]

@[simp]
public theorem cuspAngularLiftPoint_one :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    A.cuspAngularLiftPoint 1 =
      paperCuspBoundaryMeridian • A.cuspBoundaryCoverBase := by
  let _ := paperCuspBoundaryDeckAction A.starCuspWitness
  change A.cuspAngularLiftPoint 1 =
    cuspBoundaryLatticeTranslate A.starCuspWitness 0
      (cuspBoundaryAngularTranslate A.starCuspWitness 1
        A.cuspBoundaryCoverBase)
  rw [cuspBoundaryLatticeTranslate_zero]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [cuspAngularLiftPoint, cuspBoundaryAngularTranslate]

/-- The actual lifted angular path, retaining its deck-labelled endpoint. -/
public def cuspAngularLiftPath :
    letI := paperCuspBoundaryDeckAction A.starCuspWitness
    Path A.cuspBoundaryCoverBase
      (paperCuspBoundaryMeridian • A.cuspBoundaryCoverBase) where
  toFun := A.cuspAngularLiftPoint
  continuous_toFun := by
    unfold cuspAngularLiftPoint
    apply Continuous.subtype_mk
    fun_prop
  source' := A.cuspAngularLiftPoint_zero
  target' := A.cuspAngularLiftPoint_one

/-- Projection of the explicit angular lift, based literally at the projection of its selected
cover point. -/
public def cuspAngularProjectedLoop :
    Path (A.cuspBoundaryProjection A.cuspBoundaryCoverBase)
      (A.cuspBoundaryProjection A.cuspBoundaryCoverBase) := by
  let _ := paperCuspBoundaryDeckAction A.starCuspWitness
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap
      A.starCuspWitness).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
  exact (A.cuspAngularLiftPath.map
    A.cuspBoundaryProjection.continuous).cast
      rfl (hp.map_smul paperCuspBoundaryMeridian
        (e := A.cuspBoundaryCoverBase)).symm

/-- The same literal cusp loop after applying the actual collar chart into the central family. -/
public def cuspAngularCentralLoop :
    Path A.cuspCentralBase A.cuspCentralBase :=
  ((A.cuspAngularProjectedLoop.map
      A.cuspOverlapToCentral.continuous).cast
    (by
      rw [cuspCentralBase, A.cuspBoundaryCoverBase_projects])
    (by
      rw [cuspCentralBase, A.cuspBoundaryCoverBase_projects]))

/-- The actual normalized cusp loop in the marked twice-punctured base coordinate. -/
public def cuspAngularCoordinateLoop :
    Path (A.centralFamilyCoordinate A.cuspCentralBase)
      (A.centralFamilyCoordinate A.cuspCentralBase) :=
  A.cuspAngularCentralLoop.map A.centralFamilyCoordinate_continuous

/-- Pointwise, the coordinate loop is the normalized modular coordinate evaluated on the
literal angular path `s - t`. -/
public theorem cuspAngularCoordinateLoop_apply (t : unitInterval) :
    (A.cuspAngularCoordinateLoop t).1 =
      A.modular.sourceCoordinate.coordinate
        (A.cuspCoordinate.lift
          (A.cuspBoundaryCoverBase.1.2 - (t : ℝ))) := by
  change (A.centralFamilyCoordinate
      (A.cuspOverlapToCentral
        (A.cuspBoundaryProjection (A.cuspAngularLiftPoint t)))).1 = _
  rw [A.cuspOverlapToCentral_boundaryProjection]
  rfl

/-- The actual marked cusp loop remains outside the closed radius-two disc. -/
public theorem cuspAngularCoordinateLoop_norm_gt_two (t : unitInterval) :
    2 < ‖(A.cuspAngularCoordinateLoop t).1‖ := by
  rw [A.cuspAngularCoordinateLoop_apply]
  apply A.actualPuncturedCuspWitness_coordinate_exterior
  · apply mem_cuspHalfPlane_of_norm_cuspQ_lt
      A.starCuspWitness.localWitness.radius_le
    have hbase : ‖cuspQ A.cuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.cuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase
  · have hbase : ‖cuspQ A.cuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.cuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase

/-- The explicit projected angular loop is exactly the `ofDeck` meridian class used by the
chosen affine cusp filling. -/
theorem cuspAngularProjectedLoop_class_eq_ofDeck :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    Path.Homotopic.Quotient.mk A.cuspAngularProjectedLoop =
      ofDeck hp A.cuspBoundaryCoverBase paperCuspBoundaryMeridian := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  apply (hp.fundamentalGroupEquiv
    ⟨A.cuspBoundaryCoverBase, by
      change A.cuspBoundaryProjection A.cuspBoundaryCoverBase = _
      rfl⟩).injective
  rw [fundamentalGroupEquiv_ofDeck]
  change hp.fundamentalGroupToMulOpposite
      ⟨A.cuspBoundaryCoverBase, by
        change A.cuspBoundaryProjection A.cuspBoundaryCoverBase = _
        rfl⟩
      (Path.Homotopic.Quotient.mk A.cuspAngularProjectedLoop) =
    MulOpposite.op paperCuspBoundaryMeridian
  rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let Γ : Path.Homotopic.Quotient A.cuspBoundaryCoverBase
      (paperCuspBoundaryMeridian • A.cuspBoundaryCoverBase) :=
    Path.Homotopic.Quotient.mk A.cuspAngularLiftPath
  have hmono := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := ⟨A.cuspBoundaryCoverBase, by
      change A.cuspBoundaryProjection A.cuspBoundaryCoverBase = _
      rfl⟩)
    (ey := ⟨paperCuspBoundaryMeridian • A.cuspBoundaryCoverBase, by
      change A.cuspBoundaryProjection
          (paperCuspBoundaryMeridian • A.cuspBoundaryCoverBase) =
        A.cuspBoundaryProjection A.cuspBoundaryCoverBase
      exact hp.map_smul paperCuspBoundaryMeridian
        (e := A.cuspBoundaryCoverBase)⟩)
    Γ (by
      change (Path.Homotopic.Quotient.mk A.cuspAngularLiftPath).map
          A.cuspBoundaryProjection =
        (Path.Homotopic.Quotient.mk A.cuspAngularProjectedLoop).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold cuspAngularProjectedLoop
      rw [Path.Homotopic.Quotient.mk_cast]
      apply eq_of_heq
      symm
      exact (Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _))
  simpa only [MulOpposite.unop_op] using congrArg Subtype.val hmono.symm

end SphereSixComplex.Geometry.PaperAnalyticData

end
