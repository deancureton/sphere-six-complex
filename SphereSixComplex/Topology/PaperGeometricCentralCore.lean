module

public import SphereSixComplex.Topology.PaperGeometricCentralMonodromy
public import SphereSixComplex.Topology.PaperMarkedEllipticMonodromy
public import SphereSixComplex.Periods.Uniformization.PeripheralEllipticRigidity

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

/-- Pointwise form of the definition of the literal cusp translation through the overlap
chart. -/
public theorem actualCuspOverlapToCentralPiOne_translation (a : Lattice) :
    A.actualCuspOverlapToCentralPiOne
        (fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          (Additive.toMul (A.actualCuspChosenAffineFillingCover.translation a))) =
      Additive.toMul (A.actualCuspCentralTranslation a) := by
  unfold actualCuspCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply]
  rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  congr 1

/-- Pointwise form of the definition of the literal cusp meridian through the overlap chart. -/
public theorem actualCuspOverlapToCentralPiOne_meridian :
    A.actualCuspOverlapToCentralPiOne
        (fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspChosenAffineFillingCover.meridian) =
      A.actualCuspCentralMeridian := by
  rfl

/-- Transport from the marked zero section to the actual cusp point changes the global period
label only by one triangle-group automorphism.  In particular, the transported marked periods
and the literal cusp periods are the same subgroup, with no universal-cover marking involved. -/
public theorem exists_geometricCentralTranslationReindexing :
    ∃ g : Delta, ∀ a : Lattice,
      Additive.toMul (A.geometricCentralTranslation a) =
        Additive.toMul
          (A.actualCuspCentralTranslation (rhoLambda g⁻¹ a)) := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let p₀ : RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
    (A.markedRegularBaseLift, (0 : ComplexTwoSpace))
  let x₀ : RegularTotalSpace A.periods :=
    regularFamilyCoverProjection A.periods p₀
  let W := A.actualCuspMarkedCentralWhisker
  have hx₀ : regularFamilyQuotientMap A.periods x₀ =
      A.centralZeroSection A.markedPuncturedBasepoint := by
    exact A.markedCentralBase_eq_lift.symm
  let L := hp.isCoveringMap.liftPath W x₀ (W.source.trans hx₀.symm)
  let Q : Path x₀ (L 1) := {
    toFun := L
    continuous_toFun := by fun_prop
    source' := hp.isCoveringMap.liftPath_zero W x₀ (W.source.trans hx₀.symm)
    target' := rfl
  }
  have hQprojects : ∀ t, regularFamilyQuotientMap A.periods (Q t) = W t := by
    intro t
    exact congrFun
      (hp.isCoveringMap.liftPath_lifts W x₀ (W.source.trans hx₀.symm)) t
  have hQend : regularFamilyQuotientMap A.periods (Q 1) =
      A.actualCuspCentralBase := by
    rw [hQprojects]
    exact W.target
  let eQ : (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.actualCuspCentralBase} := ⟨Q 1, hQend⟩
  let eC : (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.actualCuspCentralBase} :=
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
  letI fiberAction : MulAction Delta
      ((regularFamilyQuotientMap A.periods) ⁻¹'
        {A.actualCuspCentralBase}) :=
    hp.mulActionFiber A.actualCuspCentralBase
  have hpre : MulAction.IsPretransitive Delta
      ((regularFamilyQuotientMap A.periods) ⁻¹'
        {A.actualCuspCentralBase}) :=
    hp.mulActionFiber_isPretransitive A.actualCuspCentralBase
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq eC eQ
  have hgraw := congrArg Subtype.val hg
  have hg' : regularFamilyDeckMap A.periods g A.actualCuspRegularRepresentative =
      Q 1 := by
    change regularFamilyDeckMap A.periods g A.actualCuspRegularRepresentative =
      Q 1 at hgraw
    exact hgraw
  refine ⟨g, ?_⟩
  intro a
  let p₁ := regularDeckMap A.periods g A.actualCuspRegularCoverPoint
  have hp₁ : regularFamilyCoverProjection A.periods p₁ = Q 1 := by
    calc
      regularFamilyCoverProjection A.periods p₁ =
          regularFamilyDeckMap A.periods g A.actualCuspRegularRepresentative := by
        exact regularFamilyCoverProjection_regularDeckMap A.periods g
          A.actualCuspRegularCoverPoint
      _ = Q 1 := hg'
  let Q' : Path (regularFamilyCoverProjection A.periods p₀)
      (regularFamilyCoverProjection A.periods p₁) := Q.cast rfl hp₁
  have htransport := regularFamilyPeriodLoop_transport_map_of_path A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    Q' a (regularFamilyQuotientMap A.periods)
  have hp₁outer : regularFamilyQuotientMap A.periods
      (regularFamilyCoverProjection A.periods p₁) =
        A.actualCuspCentralBase := by
    rw [hp₁]
    exact hQend
  have hQmap : (Q'.map (regularFamilyQuotientMap A.periods).continuous).cast
      hx₀.symm hp₁outer.symm = W := by
    apply Path.ext
    funext t
    exact hQprojects t
  have hdeck := regularFamilyPeriodLoop_deck A.periods g
    A.actualCuspRegularCoverPoint (rhoLambda g⁻¹ a)
  have hrho : rhoLambda g (rhoLambda g⁻¹ a) = a := by simp
  rw [hrho] at hdeck
  unfold geometricCentralTranslation markedCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  unfold markedCentralToActualCuspEquiv markedCentralBaseEquiv
  unfold centralTranslationAtZero
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  rw [regularFamilyTranslationAtZero_apply_eq_periodLoop]
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  change (FundamentalGroup.fundamentalGroupMulEquivOfPath W)
      (SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
        A.markedCentralBase_eq_lift.symm
        (pathLoopClass ((regularFamilyPeriodLoop A.periods p₀ a).map
          (regularFamilyQuotientMap A.periods).continuous))) = _
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]
  rw [A.actualCuspCentralTranslation_eq_periodLoop]
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  apply E.symm.injective
  rw [E.symm_apply_apply]
  dsimp only [E]
  change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
    (pathLoopClass (A.actualCuspCentralPeriodLoop (rhoLambda g⁻¹ a)))
  rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
  rw [htransport]
  rw [← hQmap]
  unfold actualCuspCentralPeriodLoop
  rw [← hdeck]
  unfold whiskeredLoopClass
  rfl

/-- The transported marked translations and the literal cusp translations have exactly the
same range in the actual central fundamental group. -/
public theorem geometricCentralTranslation_range_eq_actualCuspCentralTranslation :
    Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) =
      Set.range (fun a ↦ Additive.toMul (A.actualCuspCentralTranslation a)) := by
  obtain ⟨g, hg⟩ := A.exists_geometricCentralTranslationReindexing
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rhoLambda g⁻¹ a, (hg a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rhoLambda g a, ?_⟩
    calc
      Additive.toMul (A.geometricCentralTranslation (rhoLambda g a)) =
          Additive.toMul (A.actualCuspCentralTranslation
            (rhoLambda g⁻¹ (rhoLambda g a))) := hg _
      _ = Additive.toMul (A.actualCuspCentralTranslation a) := by simp

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

/-- The actual first clockwise meridian retains its exact trivial third deck power after
transport from the marked zero section to the selected cusp point. -/
public theorem geometricCentralClockwiseOneDeck_pow_three :
    A.geometricCentralClockwiseOneDeck ^ 3 = 1 := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have hpow := fundamentalGroupToMulOpposite_pow_transport hp
    A.actualCuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
    A.markedZeroCentralMeridianClass 3
    A.markedCentralOuterDeckHom_zero_pow_three
  have hrho : A.geometricCentralRhoOne⁻¹ =
      A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass := by
    simp only [geometricCentralRhoOne, map_inv, inv_inv]
  rw [geometricCentralClockwiseOneDeck, hrho]
  exact hpow

/-- Finite-order form of the exact first geometric elliptic monodromy calculation. -/
public theorem geometricCentralClockwiseOneDeck_isOfFinOrder :
    IsOfFinOrder A.geometricCentralClockwiseOneDeck := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨3, by norm_num, A.geometricCentralClockwiseOneDeck_pow_three⟩

/-- The actual second clockwise meridian likewise retains its exact trivial fourth deck power. -/
public theorem geometricCentralClockwiseTwoDeck_pow_four :
    A.geometricCentralClockwiseTwoDeck ^ 4 = 1 := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have hpow := fundamentalGroupToMulOpposite_pow_transport hp
    A.actualCuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
    A.markedOneCentralMeridianClass 4
    A.markedCentralOuterDeckHom_one_pow_four
  have hrho : A.geometricCentralRhoTwo⁻¹ =
      A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass := by
    simp only [geometricCentralRhoTwo, map_inv, inv_inv]
  rw [geometricCentralClockwiseTwoDeck, hrho]
  exact hpow

/-- Finite-order form of the exact second geometric elliptic monodromy calculation. -/
public theorem geometricCentralClockwiseTwoDeck_isOfFinOrder :
    IsOfFinOrder A.geometricCentralClockwiseTwoDeck := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨4, by norm_num, A.geometricCentralClockwiseTwoDeck_pow_four⟩

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

/-- The actual geometric elliptic pair is the standard pair conjugated by one common cusp
power.  This is forced by its exact local orders and its geometric peripheral product. -/
public theorem exists_geometricCentralCuspConjugatorExponent :
    ∃ n : ℤ,
      A.geometricCentralClockwiseOneDeck =
          (g₁ * g₂) ^ n * g₁ * ((g₁ * g₂) ^ n)⁻¹ ∧
        A.geometricCentralClockwiseTwoDeck =
          (g₁ * g₂) ^ n * g₂ * ((g₁ * g₂) ^ n)⁻¹ := by
  exact SphereSixComplex.Periods.PeripheralEllipticRigidity.elliptic_pair_eq_cusp_conjugates
      A.geometricCentralClockwiseOneDeck
      A.geometricCentralClockwiseTwoDeck
      A.geometricCentralClockwiseOneDeck_pow_three
      A.geometricCentralClockwiseTwoDeck_pow_four
      A.geometricCentralClockwiseDeck_mul

/-- A coherent exponent supplied by geometric elliptic-pair rigidity. -/
public noncomputable def geometricCentralCuspConjugatorExponent : ℤ :=
  Classical.choose A.exists_geometricCentralCuspConjugatorExponent

public theorem geometricCentralClockwiseOneDeck_eq_cuspConjugate :
    A.geometricCentralClockwiseOneDeck =
      (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent * g₁ *
        ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ :=
  (Classical.choose_spec A.exists_geometricCentralCuspConjugatorExponent).1

public theorem geometricCentralClockwiseTwoDeck_eq_cuspConjugate :
    A.geometricCentralClockwiseTwoDeck =
      (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent * g₂ *
      ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ :=
  (Classical.choose_spec A.exists_geometricCentralCuspConjugatorExponent).2

/-- The literal cusp translations, reindexed by the common peripheral conjugator.  With this
marking the two geometric finite meridians act by the paper's standard monodromy matrices. -/
public noncomputable def correctedActualCuspCentralTranslation :
    Lattice →+ Additive
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :=
  A.actualCuspCentralTranslation.comp
    (rhoLambda
      ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)).toLinearMap.toAddMonoidHom

/-- The first geometric meridian acts on the corrected literal cusp marking by
`paperMonodromyOne`. -/
public theorem geometricCentralRhoOne_conjugates_correctedTranslation (a : Lattice) :
    A.geometricCentralRhoOne *
        Additive.toMul (A.correctedActualCuspCentralTranslation a) *
        A.geometricCentralRhoOne⁻¹ =
      Additive.toMul
        (A.correctedActualCuspCentralTranslation (paperMonodromyOne a)) := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  rw [show Additive.toMul (A.correctedActualCuspCentralTranslation a) =
      Additive.toMul (A.actualCuspCentralTranslation (rhoLambda q a)) by rfl]
  rw [A.geometricCentralRhoOne_conjugates_actualTranslation]
  rw [A.geometricCentralClockwiseOneDeck_eq_cuspConjugate]
  change Additive.toMul
      (A.actualCuspCentralTranslation (rhoLambda (q * g₁ * q⁻¹) (rhoLambda q a))) =
    Additive.toMul
      (A.actualCuspCentralTranslation (rhoLambda q (paperMonodromyOne a)))
  congr 2
  simp only [map_mul, map_inv]
  simp [paperMonodromyOne]

/-- The second geometric meridian acts on the corrected literal cusp marking by
`paperMonodromyTwo`. -/
public theorem geometricCentralRhoTwo_conjugates_correctedTranslation (a : Lattice) :
    A.geometricCentralRhoTwo *
        Additive.toMul (A.correctedActualCuspCentralTranslation a) *
        A.geometricCentralRhoTwo⁻¹ =
      Additive.toMul
        (A.correctedActualCuspCentralTranslation (paperMonodromyTwo a)) := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  rw [show Additive.toMul (A.correctedActualCuspCentralTranslation a) =
      Additive.toMul (A.actualCuspCentralTranslation (rhoLambda q a)) by rfl]
  rw [A.geometricCentralRhoTwo_conjugates_actualTranslation]
  rw [A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate]
  change Additive.toMul
      (A.actualCuspCentralTranslation (rhoLambda (q * g₂ * q⁻¹) (rhoLambda q a))) =
    Additive.toMul
      (A.actualCuspCentralTranslation (rhoLambda q (paperMonodromyTwo a)))
  congr 2
  simp only [map_mul, map_inv]
  simp [paperMonodromyTwo]

/-- Reindexing by the peripheral conjugator does not change the literal cusp translation
subgroup. -/
public theorem correctedActualCuspCentralTranslation_range_eq_actual :
    Set.range (fun a ↦ Additive.toMul (A.correctedActualCuspCentralTranslation a)) =
      Set.range (fun a ↦ Additive.toMul (A.actualCuspCentralTranslation a)) := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rhoLambda q a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rhoLambda q⁻¹ a, ?_⟩
    change Additive.toMul
        (A.actualCuspCentralTranslation (rhoLambda q (rhoLambda q⁻¹ a))) =
      Additive.toMul (A.actualCuspCentralTranslation a)
    simp

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

/-- Inner correction by the chosen cusp power.  It removes the common peripheral conjugator
from the corrected translation marking while leaving the cusp meridian fixed. -/
public noncomputable def actualCuspCentralMarkingCorrection :
    MulAut (FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :=
  MulAut.conj
    ((A.actualCuspCentralMeridian ^
      A.geometricCentralCuspConjugatorExponent)⁻¹)

/-- The inner cusp correction sends each corrected translation to the literal translation with
the original lattice label. -/
public theorem actualCuspCentralMarkingCorrection_translation (a : Lattice) :
    A.actualCuspCentralMarkingCorrection
        (Additive.toMul (A.correctedActualCuspCentralTranslation a)) =
      Additive.toMul (A.actualCuspCentralTranslation a) := by
  let n := A.geometricCentralCuspConjugatorExponent
  let M := A.actualCuspCentralMeridian
  have hdeck : A.actualCuspOuterDeckHom (M ^ n) =
      MulOpposite.op (g₀ ^ n) := by
    dsimp only [M]
    rw [map_zpow, A.actualCuspOuterDeckHom_meridian]
    rfl
  have hconj := A.actualCuspCentralLoop_conjugates_translation_of_outerDeck
    (g₀ ^ n) (M ^ n) hdeck
      (rhoLambda ((g₁ * g₂) ^ n) a)
  unfold actualCuspCentralMarkingCorrection correctedActualCuspCentralTranslation
  simp only [MulAut.conj_apply, AddMonoidHom.comp_apply, inv_inv]
  change (A.actualCuspCentralMeridian ^
          A.geometricCentralCuspConjugatorExponent)⁻¹ *
        Additive.toMul (A.actualCuspCentralTranslation
          (rhoLambda ((g₁ * g₂) ^
            A.geometricCentralCuspConjugatorExponent) a)) *
        A.actualCuspCentralMeridian ^
          A.geometricCentralCuspConjugatorExponent = _
  rw [hconj]
  congr 2
  calc
    rhoLambda (g₀ ^ n) (rhoLambda ((g₁ * g₂) ^ n) a) =
        rhoLambda (g₀ ^ n * (g₁ * g₂) ^ n) a := by
      rw [map_mul]
      rfl
    _ = a := by
      have hgzero : g₀ = (g₁ * g₂)⁻¹ :=
        eq_inv_of_mul_eq_one_right g₁_mul_g₂_mul_g₀
      rw [hgzero, inv_zpow, inv_mul_cancel, map_one]
      rfl

/-- The inner cusp correction fixes the literal cusp meridian. -/
public theorem actualCuspCentralMarkingCorrection_meridian :
    A.actualCuspCentralMarkingCorrection A.actualCuspCentralMeridian =
      A.actualCuspCentralMeridian := by
  unfold actualCuspCentralMarkingCorrection
  simp only [MulAut.conj_apply]
  group

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

/-- The literal cusp translations together with the two geometric finite meridians generate
the actual central fundamental group. -/
public theorem actualCuspCentralFundamentalGroup_generated :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.actualCuspCentralTranslation a)) ∪
        {A.geometricCentralRhoOne, A.geometricCentralRhoTwo}) = ⊤ := by
  rw [← A.geometricCentralTranslation_range_eq_actualCuspCentralTranslation]
  exact A.geometricCentralFundamentalGroup_generated

/-- The actual cusp translations with the peripheral-conjugator marking and the two geometric
finite meridians form an affine-core presentation with the paper's monodromy matrices. -/
public noncomputable def actualCuspGeometricCorePiOneData :
    AffineTorusCorePiOneData
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase)
      Lattice paperMonodromyOne paperMonodromyTwo where
  translation := A.correctedActualCuspCentralTranslation
  rhoOne := A.geometricCentralRhoOne
  rhoTwo := A.geometricCentralRhoTwo
  conjugate_one := A.geometricCentralRhoOne_conjugates_correctedTranslation
  conjugate_two := A.geometricCentralRhoTwo_conjugates_correctedTranslation
  generators_generate := by
    rw [A.correctedActualCuspCentralTranslation_range_eq_actual]
    exact A.actualCuspCentralFundamentalGroup_generated

end SphereSixComplex.Geometry.PaperAnalyticData

end
