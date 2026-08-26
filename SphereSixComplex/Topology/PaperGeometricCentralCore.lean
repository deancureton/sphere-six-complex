module

public import SphereSixComplex.Topology.PaperGeometricCentralMonodromy
public import SphereSixComplex.Topology.PaperMarkedEllipticMonodromy

/-!
# Geometric generators for the actual central family

The marked zero section already supplies geometric lattice translations and two concrete
finite-puncture meridians.  This file transports them to the selected actual cusp point and
proves, without a chosen universal cover, that they generate the full central fundamental group.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open CuspPuncturedCollarBridge
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The marked lattice translations transported to the selected actual cusp point. -/
public noncomputable def geometricCentralTranslation :
    Lattice →+ Additive
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :=
  A.markedCentralToActualCuspEquiv.toMonoidHom.toAdditive.comp
    A.markedCentralTranslation

/-- The literal straight period-translation path in the normalized additive cusp cover. -/
public noncomputable def actualCuspBoundaryTranslationLiftPoint
    (a : Lattice) (t : unitInterval) :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  ⟨((t : ℝ) • periodVector
        (regularParameterMap A.periods
          (A.actualCuspAngularRegularBasePoint 0)).1 a +
      A.actualCuspBoundaryCoverBase.1.1,
    A.actualCuspBoundaryCoverBase.1.2), A.actualCuspBoundaryCoverBase.2⟩

@[simp]
public theorem actualCuspBoundaryTranslationLiftPoint_zero (a : Lattice) :
    A.actualCuspBoundaryTranslationLiftPoint a 0 =
      A.actualCuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · simp [actualCuspBoundaryTranslationLiftPoint]
  · rfl

@[simp]
public theorem actualCuspBoundaryTranslationLiftPoint_one (a : Lattice) :
    A.actualCuspBoundaryTranslationLiftPoint a 1 =
      cuspBoundaryLatticeTranslate A.starCuspWitness a
        A.actualCuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · simp [actualCuspBoundaryTranslationLiftPoint,
      cuspBoundaryLatticeTranslate, actualCuspAngularRegularBasePoint,
      actualCuspAngularLiftPoint]
    rfl
  · rfl

/-- The literal straight path from the selected cusp lift to its `a`-period translate. -/
public noncomputable def actualCuspBoundaryTranslationLift (a : Lattice) :
    Path A.actualCuspBoundaryCoverBase
      (cuspBoundaryLatticeTranslate A.starCuspWitness a
        A.actualCuspBoundaryCoverBase) where
  toFun := A.actualCuspBoundaryTranslationLiftPoint a
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact continuous_const
  source' := A.actualCuspBoundaryTranslationLiftPoint_zero a
  target' := A.actualCuspBoundaryTranslationLiftPoint_one a

/-- Projection of the literal cusp translation lift to the actual overlap. -/
public noncomputable def actualCuspBoundaryTranslationLoop (a : Lattice) :
    Path
      (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase)
      (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase) :=
  ((A.actualCuspBoundaryTranslationLift a).map
    A.actualCuspBoundaryProjection.continuous).cast rfl (by
      exact (congrArg A.cuspCollarToStarOverlapHomeomorph
        (additiveCuspBoundaryProjection_latticeTranslate
          A.starCuspWitness a A.actualCuspBoundaryCoverBase)).symm)

/-- The explicit straight cusp translation loop is the loop classified by the corresponding
boundary deck transformation. -/
public theorem actualCuspBoundaryTranslationLoop_class_eq_ofDeck (a : Lattice) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    Path.Homotopic.Quotient.mk (A.actualCuspBoundaryTranslationLoop a) =
      ofDeck hp A.actualCuspBoundaryCoverBase
        (Additive.toMul (paperCuspBoundaryTranslation a)) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let e : A.actualCuspBoundaryProjection ⁻¹'
      {A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase} :=
    ⟨A.actualCuspBoundaryCoverBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  have hsmul :
      Additive.toMul (paperCuspBoundaryTranslation a) •
          A.actualCuspBoundaryCoverBase =
        cuspBoundaryLatticeTranslate A.starCuspWitness a
          A.actualCuspBoundaryCoverBase := by
    simp [paperCuspBoundaryDeck_smul_apply, paperCuspBoundaryTranslation,
      canonicalCyclicAffineTranslation]
  change Additive.toMul (paperCuspBoundaryTranslation a) •
      A.actualCuspBoundaryCoverBase =
    (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (A.actualCuspBoundaryTranslationLoop a)) e :
        additiveCuspRadiusCover W.localWitness.radius)
  rw [hsmul]
  let e' : A.actualCuspBoundaryProjection ⁻¹'
      {A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase} :=
    ⟨cuspBoundaryLatticeTranslate W a A.actualCuspBoundaryCoverBase, by
      exact congrArg A.cuspCollarToStarOverlapHomeomorph
        (additiveCuspBoundaryProjection_latticeTranslate
          A.starCuspWitness a A.actualCuspBoundaryCoverBase)⟩
  let Γ : Path.Homotopic.Quotient A.actualCuspBoundaryCoverBase
      (cuspBoundaryLatticeTranslate W a A.actualCuspBoundaryCoverBase) :=
    Path.Homotopic.Quotient.mk (A.actualCuspBoundaryTranslationLift a)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') Γ (by
      dsimp [e, e']
      change (Path.Homotopic.Quotient.mk
          (A.actualCuspBoundaryTranslationLift a)).map
            A.actualCuspBoundaryProjection =
        (Path.Homotopic.Quotient.mk
          (A.actualCuspBoundaryTranslationLoop a)).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold actualCuspBoundaryTranslationLoop
      rw [Path.Homotopic.Quotient.mk_cast]
      exact eq_of_heq
        ((Path.Homotopic.Quotient.cast_heq _ _).trans
          (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm

/-- The straight cusp translation loop after applying the literal overlap chart to the central
family. -/
public noncomputable def actualCuspBoundaryTranslationCentralLoop (a : Lattice) :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  ((A.actualCuspBoundaryTranslationLoop a).map
    A.actualCuspOverlapToCentral.continuous).cast
      (congrArg A.actualCuspOverlapToCentral
        A.actualCuspBoundaryCoverBase_projects).symm
      (congrArg A.actualCuspOverlapToCentral
        A.actualCuspBoundaryCoverBase_projects).symm

/-- The same labelled period drawn directly in the two-stage regular torus-family cover. -/
public noncomputable def actualCuspCentralPeriodLoop (a : Lattice) :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  ((regularFamilyPeriodLoop A.periods A.actualCuspRegularCoverPoint a).map
    (regularFamilyQuotientMap A.periods).continuous).cast
      A.actualCuspRegularRepresentative_projects.symm
      A.actualCuspRegularRepresentative_projects.symm

/-- Endpoint-casting a loop realizes the elementary based transport of its fundamental-group
class. -/
public theorem pathLoopClass_cast_eq_elementOfBaseEq
    {X : Type*} [TopologicalSpace X] {x y : X}
    (L : Path x x) (h : x = y) :
    pathLoopClass (L.cast h.symm h.symm) =
      fundamentalGroupElementOfBaseEq h (pathLoopClass L) := by
  subst y
  rfl

/-- The additive cusp chart sends the literal straight translation to the globally labelled
period loop, point for point. -/
public theorem actualCuspBoundaryTranslationCentralLoop_eq_periodLoop (a : Lattice) :
    A.actualCuspBoundaryTranslationCentralLoop a =
      A.actualCuspCentralPeriodLoop a := by
  apply Path.ext
  funext t
  simp only [actualCuspBoundaryTranslationCentralLoop,
    actualCuspCentralPeriodLoop]
  change A.actualCuspOverlapToCentral
      (A.actualCuspBoundaryProjection
        (A.actualCuspBoundaryTranslationLiftPoint a t)) = _
  rw [A.actualCuspOverlapToCentral_boundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change regularFamilyQuotientMap A.periods
      (regularFamilyCoverProjection A.periods
        ((additiveCuspBundleHomeomorph A.starCuspWitness
          (A.actualCuspBoundaryTranslationLiftPoint a t)).1 :
            RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace)) =
    regularFamilyQuotientMap A.periods
      (regularFamilyPeriodLoop A.periods A.actualCuspRegularCoverPoint a t)
  rw [regularFamilyPeriodLoop_apply]
  apply congrArg (regularFamilyQuotientMap A.periods)
  apply congrArg (regularFamilyCoverProjection A.periods)
  apply Prod.ext
  · apply Subtype.ext
    change A.cuspCoordinate.lift A.actualCuspBoundaryCoverBase.1.2 =
      A.cuspCoordinate.lift (A.actualCuspAngularLiftPoint 0).1.2
    rw [A.actualCuspAngularLiftPoint_zero]
  · rfl

/-- The translation selected by the affine filling is represented, after transport to the
prescribed overlap point, by the literal straight boundary loop. -/
public theorem actualCuspAffineBridgeTranslation_eq_boundaryLoop (a : Lattice) :
    fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        (Additive.toMul (A.actualCuspChosenAffineFillingCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.actualCuspBoundaryTranslationLoop a)) := by
  rw [A.actualCuspChosenAffineFillingCover_translation_eq_ofDeck]
  apply congrArg
    (fundamentalGroupElementOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq)
  exact (A.actualCuspBoundaryTranslationLoop_class_eq_ofDeck a).symm

/-- The actual cusp translation is exactly the globally labelled period loop in the central
family. -/
public theorem actualCuspCentralTranslation_eq_periodLoop (a : Lattice) :
    Additive.toMul (A.actualCuspCentralTranslation a) =
      Path.Homotopic.Quotient.mk (A.actualCuspCentralPeriodLoop a) := by
  unfold actualCuspCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply]
  rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.actualCuspAffineBridgeTranslation_eq_boundaryLoop]
  unfold actualCuspOverlapToCentralPiOne
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hsource :
      A.actualCuspOverlapToCentral
          A.actualCuspChosenAffineFillingCover.boundaryBase =
        A.actualCuspCentralBase := by
    rw [A.actualCuspChosenAffineFillingCover_boundaryBase_eq]
    rfl
  calc
    _ = FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral hsource
          (Path.Homotopic.Quotient.mk
            (A.actualCuspBoundaryTranslationLoop a)) :=
      mapOfEq_fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspOverlapToCentral hsource rfl _
    _ = Path.Homotopic.Quotient.mk
          (A.actualCuspBoundaryTranslationCentralLoop a) := by
      rw [FundamentalGroup.mapOfEq_apply]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl
    _ = Path.Homotopic.Quotient.mk
          (A.actualCuspCentralPeriodLoop a) := by
      exact congrArg Path.Homotopic.Quotient.mk
        (A.actualCuspBoundaryTranslationCentralLoop_eq_periodLoop a)

set_option backward.isDefEq.respectTransparency.types false in
/-- Any loop at the actual cusp point acts on the actual period translations through its
outer triangle-group deck label. -/
public theorem actualCuspCentralLoop_conjugates_translation_of_outerDeck
    (g : Delta)
    (delta : FundamentalGroup A.CentralFamily A.actualCuspCentralBase)
    (hdelta :
      letI := regularFamilyDeckAction A.periods
      let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
      hp.fundamentalGroupToMulOpposite
          ⟨A.actualCuspRegularRepresentative,
            A.actualCuspRegularRepresentative_projects⟩ delta = MulOpposite.op g)
    (a : Lattice) :
    delta⁻¹ * Additive.toMul (A.actualCuspCentralTranslation a) * delta =
      Additive.toMul (A.actualCuspCentralTranslation (rhoLambda g a)) := by
  rw [A.actualCuspCentralTranslation_eq_periodLoop,
    A.actualCuspCentralTranslation_eq_periodLoop]
  exact fundamentalGroup_conjugates_period_of_outerDeck_of_baseEq A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    g A.actualCuspRegularCoverPoint A.actualCuspRegularRepresentative_projects
    delta hdelta a

/-- The ordinary (non-opposite) deck label of the clockwise inverse of the first geometric
finite meridian. -/
public noncomputable def geometricCentralClockwiseOneDeck : Delta :=
  MulOpposite.unop
    (A.actualCuspOuterDeckHom A.geometricCentralRhoOne⁻¹)

/-- The analogous clockwise deck label at the order-four puncture. -/
public noncomputable def geometricCentralClockwiseTwoDeck : Delta :=
  MulOpposite.unop
    (A.actualCuspOuterDeckHom A.geometricCentralRhoTwo⁻¹)

/-- The actual first clockwise meridian retains finite outer deck order after transport from the
marked zero section to the selected cusp point. -/
public theorem geometricCentralClockwiseOneDeck_isOfFinOrder :
    IsOfFinOrder A.geometricCentralClockwiseOneDeck := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have hfin := fundamentalGroupToMulOpposite_isOfFinOrder_transport hp
    A.actualCuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
    A.markedZeroCentralMeridianClass
    A.markedCentralOuterDeckHom_zero_isOfFinOrder
  have hrho : A.geometricCentralRhoOne⁻¹ =
      A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass := by
    simp only [geometricCentralRhoOne, map_inv, inv_inv]
  rw [geometricCentralClockwiseOneDeck, hrho]
  exact hfin

/-- The actual second clockwise meridian likewise retains finite outer deck order. -/
public theorem geometricCentralClockwiseTwoDeck_isOfFinOrder :
    IsOfFinOrder A.geometricCentralClockwiseTwoDeck := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have hfin := fundamentalGroupToMulOpposite_isOfFinOrder_transport hp
    A.actualCuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
    A.markedOneCentralMeridianClass
    A.markedCentralOuterDeckHom_one_isOfFinOrder
  have hrho : A.geometricCentralRhoTwo⁻¹ =
      A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass := by
    simp only [geometricCentralRhoTwo, map_inv, inv_inv]
  rw [geometricCentralClockwiseTwoDeck, hrho]
  exact hfin

/-- The first geometric meridian acts on actual cusp translations through its exact, retained
outer deck label. -/
public theorem geometricCentralRhoOne_conjugates_actualTranslation (a : Lattice) :
    A.geometricCentralRhoOne *
        Additive.toMul (A.actualCuspCentralTranslation a) *
        A.geometricCentralRhoOne⁻¹ =
      Additive.toMul (A.actualCuspCentralTranslation
        (rhoLambda A.geometricCentralClockwiseOneDeck a)) := by
  simpa only [inv_inv] using
    (A.actualCuspCentralLoop_conjugates_translation_of_outerDeck
      A.geometricCentralClockwiseOneDeck A.geometricCentralRhoOne⁻¹ rfl a)

/-- The second geometric meridian has the analogous labelled action. -/
public theorem geometricCentralRhoTwo_conjugates_actualTranslation (a : Lattice) :
    A.geometricCentralRhoTwo *
        Additive.toMul (A.actualCuspCentralTranslation a) *
        A.geometricCentralRhoTwo⁻¹ =
      Additive.toMul (A.actualCuspCentralTranslation
        (rhoLambda A.geometricCentralClockwiseTwoDeck a)) := by
  simpa only [inv_inv] using
    (A.actualCuspCentralLoop_conjugates_translation_of_outerDeck
      A.geometricCentralClockwiseTwoDeck A.geometricCentralRhoTwo⁻¹ rfl a)

/-- The retained clockwise labels multiply to the positive peripheral word.  This is the exact
deck-level shadow of the geometric pair-of-pants relation. -/
public theorem geometricCentralClockwiseDeck_mul :
    A.geometricCentralClockwiseOneDeck *
        A.geometricCentralClockwiseTwoDeck = g₁ * g₂ := by
  apply MulOpposite.op_injective
  rw [MulOpposite.op_mul]
  unfold geometricCentralClockwiseOneDeck geometricCentralClockwiseTwoDeck
  simp only [MulOpposite.op_unop]
  calc
    A.actualCuspOuterDeckHom A.geometricCentralRhoTwo⁻¹ *
          A.actualCuspOuterDeckHom A.geometricCentralRhoOne⁻¹ =
        A.actualCuspOuterDeckHom
          ((A.geometricCentralRhoOne * A.geometricCentralRhoTwo)⁻¹) := by
      simp only [map_inv, map_mul, mul_inv_rev]
    _ = A.actualCuspOuterDeckHom A.actualCuspCentralMeridian⁻¹ := by
      rw [A.actualCuspCentralMeridian_eq_geometricRhoProduct]
    _ = (MulOpposite.op g₀)⁻¹ := by
      rw [map_inv, A.actualCuspOuterDeckHom_meridian]
    _ = MulOpposite.op (g₁ * g₂) := by
      rw [← MulOpposite.op_inv]
      congr 1
      have h := congrArg Inv.inv
        (inv_eq_of_mul_eq_one_right g₁_mul_g₂_mul_g₀)
      simpa only [inv_inv] using h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal cusp meridian acts on the literal cusp translations by the prescribed
parabolic lattice monodromy.  This is the paper's usual conjugation formula, written in
Mathlib's reversed path-composition convention. -/
public theorem actualCuspCentralMeridian_conjugates_translation (a : Lattice) :
    A.actualCuspCentralMeridian⁻¹ *
        Additive.toMul (A.actualCuspCentralTranslation a) *
        A.actualCuspCentralMeridian =
      Additive.toMul
        (A.actualCuspCentralTranslation (rhoLambda g₀ a)) := by
  rw [A.actualCuspCentralMeridian_eq_angularLoop,
    A.actualCuspAngularCentralLoop_eq_actualRegularDeckLoop,
    A.actualCuspCentralTranslation_eq_periodLoop,
    A.actualCuspCentralTranslation_eq_periodLoop]
  have h := regularFamilyDeckPathLoop_conjugates_period A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    g₀ A.actualCuspRegularCoverPoint A.actualCuspRegularDeckPath a
  have hbase :
      regularFamilyQuotientMap A.periods
          (regularFamilyCoverProjection A.periods
            A.actualCuspRegularCoverPoint) =
        A.actualCuspCentralBase :=
    A.actualCuspRegularRepresentative_projects
  change
    (pathLoopClass
        ((regularFamilyDeckPathLoop A.periods g₀
          A.actualCuspRegularCoverPoint A.actualCuspRegularDeckPath).cast
            hbase.symm hbase.symm))⁻¹ *
        pathLoopClass
          (((regularFamilyPeriodLoop A.periods
            A.actualCuspRegularCoverPoint a).map
              (regularFamilyQuotientMap A.periods).continuous).cast
                hbase.symm hbase.symm) *
        pathLoopClass
          ((regularFamilyDeckPathLoop A.periods g₀
            A.actualCuspRegularCoverPoint A.actualCuspRegularDeckPath).cast
              hbase.symm hbase.symm) =
      pathLoopClass
        (((regularFamilyPeriodLoop A.periods A.actualCuspRegularCoverPoint
          (rhoLambda g₀ a)).map
            (regularFamilyQuotientMap A.periods).continuous).cast
              hbase.symm hbase.symm)
  rw [pathLoopClass_cast_eq_elementOfBaseEq
      (regularFamilyDeckPathLoop A.periods g₀
        A.actualCuspRegularCoverPoint A.actualCuspRegularDeckPath) hbase,
    pathLoopClass_cast_eq_elementOfBaseEq
      ((regularFamilyPeriodLoop A.periods
        A.actualCuspRegularCoverPoint a).map
          (regularFamilyQuotientMap A.periods).continuous) hbase,
    pathLoopClass_cast_eq_elementOfBaseEq
      ((regularFamilyPeriodLoop A.periods A.actualCuspRegularCoverPoint
        (rhoLambda g₀ a)).map
          (regularFamilyQuotientMap A.periods).continuous) hbase]
  have htransport := congrArg
    (fundamentalGroupElementOfBaseEq hbase) h
  simpa only [fundamentalGroupElementOfBaseEq_mul,
    fundamentalGroupElementOfBaseEq_inv] using htransport

/-- At the marked zero-section point, the geometric translations and the two concrete finite
meridians generate the central fundamental group. -/
public theorem markedCentralFundamentalGroup_generated_by_translations_and_meridians :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
        {A.markedZeroCentralMeridianClass⁻¹,
          A.markedOneCentralMeridianClass⁻¹}) = ⊤ := by
  let K := Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
      {A.markedZeroCentralMeridianClass⁻¹,
        A.markedOneCentralMeridianClass⁻¹})
  have hzeroInv : A.markedZeroCentralMeridianClass⁻¹ ∈ K := by
    apply Subgroup.subset_closure
    simp
  have honeInv : A.markedOneCentralMeridianClass⁻¹ ∈ K := by
    apply Subgroup.subset_closure
    simp
  have hzero : A.markedZeroCentralMeridianClass ∈ K := by
    simpa using K.inv_mem hzeroInv
  have hone : A.markedOneCentralMeridianClass ∈ K := by
    simpa using K.inv_mem honeInv
  have hfinite :
      Subgroup.closure ({A.markedZeroCentralMeridianClass,
        A.markedOneCentralMeridianClass} :
          Set (FundamentalGroup A.CentralFamily
            (A.centralZeroSection A.markedPuncturedBasepoint))) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact hzero
    · exact hone
  have hle :
      Subgroup.closure
        (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
          Set.range A.centralZeroSectionFundamentalGroupMap) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hg | hg
    · apply Subgroup.subset_closure
      exact Or.inl hg
    · exact hfinite
        (A.centralZeroSectionFundamentalGroupMap_range_le_markedClosure hg)
  change K = ⊤
  apply top_unique
  intro g _
  apply hle
  rw [A.markedCentralFundamentalGroup_generated_by_translations_and_zeroSection]
  trivial

/-- At the actual cusp point, the transported lattice translations and the two concrete finite
meridians generate the full central fundamental group. -/
public theorem geometricCentralFundamentalGroup_generated :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) ∪
        {A.geometricCentralRhoOne, A.geometricCentralRhoTwo}) = ⊤ := by
  let E := A.markedCentralToActualCuspEquiv
  let K := Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) ∪
      {A.geometricCentralRhoOne, A.geometricCentralRhoTwo})
  let S : Set (FundamentalGroup A.CentralFamily
      (A.centralZeroSection A.markedPuncturedBasepoint)) :=
    Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
      {A.markedZeroCentralMeridianClass⁻¹,
        A.markedOneCentralMeridianClass⁻¹}
  have hle : Subgroup.closure S ≤ K.comap E.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change E g ∈ K
    apply Subgroup.subset_closure
    rcases hg with ⟨a, rfl⟩ | hg
    · apply Or.inl
      refine ⟨a, ?_⟩
      rfl
    · rcases hg with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  change K = ⊤
  apply top_unique
  intro g _
  obtain ⟨δ, rfl⟩ := E.surjective g
  apply hle
  rw [A.markedCentralFundamentalGroup_generated_by_translations_and_meridians]
  trivial

end SphereSixComplex.Geometry.PaperAnalyticData

end
