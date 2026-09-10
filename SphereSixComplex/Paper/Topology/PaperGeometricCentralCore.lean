module

public import SphereSixComplex.Paper.Topology.PaperGeometricCentralMonodromy
public import SphereSixComplex.Paper.Topology.PaperMarkedEllipticMonodromy
public import SphereSixComplex.Prerequisites.Periods.Uniformization.PeripheralEllipticRigidity

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
      (FundamentalGroup A.CentralFamily A.cuspCentralBase) :=
  A.markedCentralToActualCuspEquiv.toMonoidHom.toAdditive.comp
    A.markedCentralTranslation

/-- The literal straight period-translation path in the normalized additive cusp cover. -/
public noncomputable def cuspBoundaryTranslationLiftPoint
    (a : Lattice) (t : unitInterval) :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  ⟨((t : ℝ) • periodVector
        (regularParameterMap A.periods
          (A.cuspAngularRegularBasePoint 0)).1 a +
      A.cuspBoundaryCoverBase.1.1,
    A.cuspBoundaryCoverBase.1.2), A.cuspBoundaryCoverBase.2⟩

@[simp]
public theorem cuspBoundaryTranslationLiftPoint_zero (a : Lattice) :
    A.cuspBoundaryTranslationLiftPoint a 0 =
      A.cuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · simp [cuspBoundaryTranslationLiftPoint]
  · rfl

@[simp]
public theorem cuspBoundaryTranslationLiftPoint_one (a : Lattice) :
    A.cuspBoundaryTranslationLiftPoint a 1 =
      cuspBoundaryLatticeTranslate A.starCuspWitness a
        A.cuspBoundaryCoverBase := by
  apply Subtype.ext
  apply Prod.ext
  · simp [cuspBoundaryTranslationLiftPoint,
      cuspBoundaryLatticeTranslate, cuspAngularRegularBasePoint,
      cuspAngularLiftPoint]
    rfl
  · rfl

/-- The literal straight path from the selected cusp lift to its `a`-period translate. -/
public noncomputable def cuspBoundaryTranslationLift (a : Lattice) :
    Path A.cuspBoundaryCoverBase
      (cuspBoundaryLatticeTranslate A.starCuspWitness a
        A.cuspBoundaryCoverBase) where
  toFun := A.cuspBoundaryTranslationLiftPoint a
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact continuous_const
  source' := A.cuspBoundaryTranslationLiftPoint_zero a
  target' := A.cuspBoundaryTranslationLiftPoint_one a

/-- Projection of the literal cusp translation lift to the actual overlap. -/
public noncomputable def cuspBoundaryTranslationLoop (a : Lattice) :
    Path
      (A.cuspBoundaryProjection A.cuspBoundaryCoverBase)
      (A.cuspBoundaryProjection A.cuspBoundaryCoverBase) :=
  ((A.cuspBoundaryTranslationLift a).map
    A.cuspBoundaryProjection.continuous).cast rfl (by
      exact (congrArg A.cuspCollarToStarOverlapHomeomorph
        (additiveCuspBoundaryProjection_latticeTranslate
          A.starCuspWitness a A.cuspBoundaryCoverBase)).symm)

/-- The explicit straight cusp translation loop is the loop classified by the corresponding
boundary deck transformation. -/
public theorem cuspBoundaryTranslationLoop_class_eq_ofDeck (a : Lattice) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
        PaperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    Path.Homotopic.Quotient.mk (A.cuspBoundaryTranslationLoop a) =
      ofDeck hp A.cuspBoundaryCoverBase
        (Additive.toMul (paperCuspBoundaryTranslation a)) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      PaperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  let e : A.cuspBoundaryProjection ⁻¹'
      {A.cuspBoundaryProjection A.cuspBoundaryCoverBase} :=
    ⟨A.cuspBoundaryCoverBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  have hsmul :
      Additive.toMul (paperCuspBoundaryTranslation a) •
          A.cuspBoundaryCoverBase =
        cuspBoundaryLatticeTranslate A.starCuspWitness a
          A.cuspBoundaryCoverBase := by
    simp [paperCuspBoundaryDeck_smul_apply, paperCuspBoundaryTranslation,
      canonicalCyclicAffineTranslation]
  change Additive.toMul (paperCuspBoundaryTranslation a) •
      A.cuspBoundaryCoverBase =
    (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (A.cuspBoundaryTranslationLoop a)) e :
        additiveCuspRadiusCover W.localWitness.radius)
  rw [hsmul]
  let e' : A.cuspBoundaryProjection ⁻¹'
      {A.cuspBoundaryProjection A.cuspBoundaryCoverBase} :=
    ⟨cuspBoundaryLatticeTranslate W a A.cuspBoundaryCoverBase, by
      exact congrArg A.cuspCollarToStarOverlapHomeomorph
        (additiveCuspBoundaryProjection_latticeTranslate
          A.starCuspWitness a A.cuspBoundaryCoverBase)⟩
  let Γ : Path.Homotopic.Quotient A.cuspBoundaryCoverBase
      (cuspBoundaryLatticeTranslate W a A.cuspBoundaryCoverBase) :=
    Path.Homotopic.Quotient.mk (A.cuspBoundaryTranslationLift a)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') Γ (by
      dsimp [e, e']
      change (Path.Homotopic.Quotient.mk
          (A.cuspBoundaryTranslationLift a)).map
            A.cuspBoundaryProjection =
        (Path.Homotopic.Quotient.mk
          (A.cuspBoundaryTranslationLoop a)).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold cuspBoundaryTranslationLoop
      rw [Path.Homotopic.Quotient.mk_cast]
      exact eq_of_heq
        ((Path.Homotopic.Quotient.cast_heq _ _).trans
          (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm

/-- The straight cusp translation loop after applying the literal overlap chart to the central
family. -/
public noncomputable def cuspBoundaryTranslationCentralLoop (a : Lattice) :
    Path A.cuspCentralBase A.cuspCentralBase :=
  ((A.cuspBoundaryTranslationLoop a).map
    A.cuspOverlapToCentral.continuous).cast
      (congrArg A.cuspOverlapToCentral
        A.cuspBoundaryCoverBase_projects).symm
      (congrArg A.cuspOverlapToCentral
        A.cuspBoundaryCoverBase_projects).symm

/-- The same labelled period drawn directly in the two-stage regular torus-family cover. -/
public noncomputable def cuspCentralPeriodLoop (a : Lattice) :
    Path A.cuspCentralBase A.cuspCentralBase :=
  ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint a).map
    (regularFamilyQuotientMap A.periods).continuous).cast
      A.cuspRegularRepresentative_projects.symm
      A.cuspRegularRepresentative_projects.symm

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
public theorem cuspBoundaryTranslationCentralLoop_eq_periodLoop (a : Lattice) :
    A.cuspBoundaryTranslationCentralLoop a =
      A.cuspCentralPeriodLoop a := by
  apply Path.ext
  funext t
  simp only [cuspBoundaryTranslationCentralLoop,
    cuspCentralPeriodLoop]
  change A.cuspOverlapToCentral
      (A.cuspBoundaryProjection
        (A.cuspBoundaryTranslationLiftPoint a t)) = _
  rw [A.cuspOverlapToCentral_boundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change regularFamilyQuotientMap A.periods
      (regularFamilyCoverProjection A.periods
        ((additiveCuspBundleHomeomorph A.starCuspWitness
          (A.cuspBoundaryTranslationLiftPoint a t)).1 :
            RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace)) =
    regularFamilyQuotientMap A.periods
      (regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint a t)
  rw [regularFamilyPeriodLoop_apply]
  apply congrArg (regularFamilyQuotientMap A.periods)
  apply congrArg (regularFamilyCoverProjection A.periods)
  apply Prod.ext
  · apply Subtype.ext
    change A.cuspCoordinate.lift A.cuspBoundaryCoverBase.1.2 =
      A.cuspCoordinate.lift (A.cuspAngularLiftPoint 0).1.2
    rw [A.cuspAngularLiftPoint_zero]
  · rfl

/-- The translation selected by the affine filling is represented, after transport to the
prescribed overlap point, by the literal straight boundary loop. -/
public theorem cuspAffineBridgeTranslation_eq_boundaryLoop (a : Lattice) :
    fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (Additive.toMul (A.cuspChosenAffineFillingCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.cuspBoundaryTranslationLoop a)) := by
  rw [A.cuspChosenAffineFillingCover_translation_eq_ofDeck]
  apply congrArg
    (fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq)
  exact (A.cuspBoundaryTranslationLoop_class_eq_ofDeck a).symm

/-- The actual cusp translation is exactly the globally labelled period loop in the central
family. -/
public theorem cuspCentralTranslation_eq_periodLoop (a : Lattice) :
    Additive.toMul (A.cuspCentralTranslation a) =
      Path.Homotopic.Quotient.mk (A.cuspCentralPeriodLoop a) := by
  unfold cuspCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply]
  rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.cuspAffineBridgeTranslation_eq_boundaryLoop]
  unfold cuspOverlapToCentralPiOne
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hsource :
      A.cuspOverlapToCentral
          A.cuspChosenAffineFillingCover.boundaryBase =
        A.cuspCentralBase := by
    rw [A.cuspChosenAffineFillingCover_boundaryBase_eq]
    rfl
  calc
    _ = FundamentalGroup.mapOfEq A.cuspOverlapToCentral hsource
          (Path.Homotopic.Quotient.mk
            (A.cuspBoundaryTranslationLoop a)) :=
      mapOfEq_fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspOverlapToCentral hsource rfl _
    _ = Path.Homotopic.Quotient.mk
          (A.cuspBoundaryTranslationCentralLoop a) := by
      rw [FundamentalGroup.mapOfEq_apply]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl
    _ = Path.Homotopic.Quotient.mk
          (A.cuspCentralPeriodLoop a) := by
      exact congrArg Path.Homotopic.Quotient.mk
        (A.cuspBoundaryTranslationCentralLoop_eq_periodLoop a)

/-- Pointwise form of the definition of the literal cusp translation through the overlap
chart. -/
public theorem cuspOverlapToCentralPiOne_translation (a : Lattice) :
    A.cuspOverlapToCentralPiOne
        (fundamentalGroupElementOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          (Additive.toMul (A.cuspChosenAffineFillingCover.translation a))) =
      Additive.toMul (A.cuspCentralTranslation a) := by
  unfold cuspCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply]
  rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  congr 1

/-- Pointwise form of the definition of the literal cusp meridian through the overlap chart. -/
public theorem cuspOverlapToCentralPiOne_meridian :
    A.cuspOverlapToCentralPiOne
        (fundamentalGroupElementOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          A.cuspChosenAffineFillingCover.meridian) =
      A.cuspCentralMeridian := by
  rfl

/-- Transport from the marked zero section to the actual cusp point changes the global period
label only by one triangle-group automorphism.  In particular, the transported marked periods
and the literal cusp periods are the same subgroup, with no universal-cover marking involved. -/
public theorem exists_geometricCentralTranslationReindexing :
    ∃ g : Delta, ∀ a : Lattice,
      Additive.toMul (A.geometricCentralTranslation a) =
        Additive.toMul
          (A.cuspCentralTranslation (rhoLambda g⁻¹ a)) := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let p₀ : RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
    (A.markedRegularBaseLift, (0 : ComplexTwoSpace))
  let x₀ : RegularTotalSpace A.periods :=
    regularFamilyCoverProjection A.periods p₀
  let W := A.cuspMarkedCentralWhisker
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
      A.cuspCentralBase := by
    rw [hQprojects]
    exact W.target
  let eQ : (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.cuspCentralBase} := ⟨Q 1, hQend⟩
  let eC : (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.cuspCentralBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects⟩
  letI fiberAction : MulAction Delta
      ((regularFamilyQuotientMap A.periods) ⁻¹'
        {A.cuspCentralBase}) :=
    hp.mulActionFiber A.cuspCentralBase
  have hpre : MulAction.IsPretransitive Delta
      ((regularFamilyQuotientMap A.periods) ⁻¹'
        {A.cuspCentralBase}) :=
    hp.mulActionFiber_isPretransitive A.cuspCentralBase
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq eC eQ
  have hgraw := congrArg Subtype.val hg
  have hg' : regularFamilyDeckMap A.periods g A.cuspRegularRepresentative =
      Q 1 := by
    change regularFamilyDeckMap A.periods g A.cuspRegularRepresentative =
      Q 1 at hgraw
    exact hgraw
  refine ⟨g, ?_⟩
  intro a
  let p₁ := regularDeckMap A.periods g A.cuspRegularCoverPoint
  have hp₁ : regularFamilyCoverProjection A.periods p₁ = Q 1 := by
    calc
      regularFamilyCoverProjection A.periods p₁ =
          regularFamilyDeckMap A.periods g A.cuspRegularRepresentative := by
        exact regularFamilyCoverProjection_regularDeckMap A.periods g
          A.cuspRegularCoverPoint
      _ = Q 1 := hg'
  let Q' : Path (regularFamilyCoverProjection A.periods p₀)
      (regularFamilyCoverProjection A.periods p₁) := Q.cast rfl hp₁
  have htransport := regularFamilyPeriodLoop_transport_map_of_path A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    Q' a (regularFamilyQuotientMap A.periods)
  have hp₁outer : regularFamilyQuotientMap A.periods
      (regularFamilyCoverProjection A.periods p₁) =
        A.cuspCentralBase := by
    rw [hp₁]
    exact hQend
  have hQmap : (Q'.map (regularFamilyQuotientMap A.periods).continuous).cast
      hx₀.symm hp₁outer.symm = W := by
    apply Path.ext
    funext t
    exact hQprojects t
  have hdeck := regularFamilyPeriodLoop_deck A.periods g
    A.cuspRegularCoverPoint (rhoLambda g⁻¹ a)
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
  rw [A.cuspCentralTranslation_eq_periodLoop]
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  apply E.symm.injective
  rw [E.symm_apply_apply]
  dsimp only [E]
  change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
    (pathLoopClass (A.cuspCentralPeriodLoop (rhoLambda g⁻¹ a)))
  rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
  rw [htransport]
  rw [← hQmap]
  unfold cuspCentralPeriodLoop
  rw [← hdeck]
  unfold whiskeredLoopClass
  rfl

/-- The transported marked translations and the literal cusp translations have exactly the
same range in the actual central fundamental group. -/
public theorem geometricCentralTranslation_range_eq_cuspCentralTranslation :
    Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) =
      Set.range (fun a ↦ Additive.toMul (A.cuspCentralTranslation a)) := by
  obtain ⟨g, hg⟩ := A.exists_geometricCentralTranslationReindexing
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rhoLambda g⁻¹ a, (hg a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rhoLambda g a, ?_⟩
    calc
      Additive.toMul (A.geometricCentralTranslation (rhoLambda g a)) =
          Additive.toMul (A.cuspCentralTranslation
            (rhoLambda g⁻¹ (rhoLambda g a))) := hg _
      _ = Additive.toMul (A.cuspCentralTranslation a) := by simp

/-- Any loop at the actual cusp point acts on the actual period translations through its
outer triangle-group deck label. -/
public theorem cuspCentralLoop_conjugates_translation_of_outerDeck
    (g : Delta)
    (delta : FundamentalGroup A.CentralFamily A.cuspCentralBase)
    (hdelta :
      letI := regularFamilyDeckAction A.periods
      let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
      hp.fundamentalGroupToMulOpposite
          ⟨A.cuspRegularRepresentative,
            A.cuspRegularRepresentative_projects⟩ delta = MulOpposite.op g)
    (a : Lattice) :
    delta⁻¹ * Additive.toMul (A.cuspCentralTranslation a) * delta =
      Additive.toMul (A.cuspCentralTranslation (rhoLambda g a)) := by
  rw [A.cuspCentralTranslation_eq_periodLoop,
    A.cuspCentralTranslation_eq_periodLoop]
  exact fundamentalGroup_conjugates_period_of_outerDeck_of_baseEq A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    g A.cuspRegularCoverPoint A.cuspRegularRepresentative_projects
    delta hdelta a

/-- The ordinary (non-opposite) deck label of the clockwise inverse of the first geometric
finite meridian. -/
public noncomputable def geometricCentralClockwiseOneDeck : Delta :=
  MulOpposite.unop
    (A.cuspOuterDeckHom A.geometricCentralRhoOne⁻¹)

/-- The analogous clockwise deck label at the order-four puncture. -/
public noncomputable def geometricCentralClockwiseTwoDeck : Delta :=
  MulOpposite.unop
    (A.cuspOuterDeckHom A.geometricCentralRhoTwo⁻¹)

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
    A.cuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects⟩
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
    A.cuspMarkedCentralWhisker
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects⟩
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
        Additive.toMul (A.cuspCentralTranslation a) *
        A.geometricCentralRhoOne⁻¹ =
      Additive.toMul (A.cuspCentralTranslation
        (rhoLambda A.geometricCentralClockwiseOneDeck a)) := by
  simpa only [inv_inv] using
    (A.cuspCentralLoop_conjugates_translation_of_outerDeck
      A.geometricCentralClockwiseOneDeck A.geometricCentralRhoOne⁻¹ rfl a)

/-- The second geometric meridian has the analogous labelled action. -/
public theorem geometricCentralRhoTwo_conjugates_actualTranslation (a : Lattice) :
    A.geometricCentralRhoTwo *
        Additive.toMul (A.cuspCentralTranslation a) *
        A.geometricCentralRhoTwo⁻¹ =
      Additive.toMul (A.cuspCentralTranslation
        (rhoLambda A.geometricCentralClockwiseTwoDeck a)) := by
  simpa only [inv_inv] using
    (A.cuspCentralLoop_conjugates_translation_of_outerDeck
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
    A.cuspOuterDeckHom A.geometricCentralRhoTwo⁻¹ *
          A.cuspOuterDeckHom A.geometricCentralRhoOne⁻¹ =
        A.cuspOuterDeckHom
          ((A.geometricCentralRhoOne * A.geometricCentralRhoTwo)⁻¹) := by
      simp only [map_inv, map_mul, mul_inv_rev]
    _ = A.cuspOuterDeckHom A.cuspCentralMeridian⁻¹ := by
      rw [A.cuspCentralMeridian_eq_geometricRhoProduct]
    _ = (MulOpposite.op g₀)⁻¹ := by
      rw [map_inv, A.cuspOuterDeckHom_meridian]
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
      (FundamentalGroup A.CentralFamily A.cuspCentralBase) :=
  A.cuspCentralTranslation.comp
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
      Additive.toMul (A.cuspCentralTranslation (rhoLambda q a)) by rfl]
  rw [A.geometricCentralRhoOne_conjugates_actualTranslation]
  rw [A.geometricCentralClockwiseOneDeck_eq_cuspConjugate]
  change Additive.toMul
      (A.cuspCentralTranslation (rhoLambda (q * g₁ * q⁻¹) (rhoLambda q a))) =
    Additive.toMul
      (A.cuspCentralTranslation (rhoLambda q (paperMonodromyOne a)))
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
      Additive.toMul (A.cuspCentralTranslation (rhoLambda q a)) by rfl]
  rw [A.geometricCentralRhoTwo_conjugates_actualTranslation]
  rw [A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate]
  change Additive.toMul
      (A.cuspCentralTranslation (rhoLambda (q * g₂ * q⁻¹) (rhoLambda q a))) =
    Additive.toMul
      (A.cuspCentralTranslation (rhoLambda q (paperMonodromyTwo a)))
  congr 2
  simp only [map_mul, map_inv]
  simp [paperMonodromyTwo]

/-- Reindexing by the peripheral conjugator does not change the literal cusp translation
subgroup. -/
public theorem correctedActualCuspCentralTranslation_range_eq_actual :
    Set.range (fun a ↦ Additive.toMul (A.correctedActualCuspCentralTranslation a)) =
      Set.range (fun a ↦ Additive.toMul (A.cuspCentralTranslation a)) := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rhoLambda q a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rhoLambda q⁻¹ a, ?_⟩
    change Additive.toMul
        (A.cuspCentralTranslation (rhoLambda q (rhoLambda q⁻¹ a))) =
      Additive.toMul (A.cuspCentralTranslation a)
    simp

/-- The literal cusp meridian acts on the literal cusp translations by the prescribed
parabolic lattice monodromy.  This is the paper's usual conjugation formula, written in
Mathlib's reversed path-composition convention. -/
public theorem cuspCentralMeridian_conjugates_translation (a : Lattice) :
    A.cuspCentralMeridian⁻¹ *
        Additive.toMul (A.cuspCentralTranslation a) *
        A.cuspCentralMeridian =
      Additive.toMul
        (A.cuspCentralTranslation (rhoLambda g₀ a)) := by
  rw [A.cuspCentralMeridian_eq_angularLoop,
    A.cuspAngularCentralLoop_eq_actualRegularDeckLoop,
    A.cuspCentralTranslation_eq_periodLoop,
    A.cuspCentralTranslation_eq_periodLoop]
  have h := regularFamilyDeckPathLoop_conjugates_period A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    g₀ A.cuspRegularCoverPoint A.cuspRegularDeckPath a
  have hbase :
      regularFamilyQuotientMap A.periods
          (regularFamilyCoverProjection A.periods
            A.cuspRegularCoverPoint) =
        A.cuspCentralBase :=
    A.cuspRegularRepresentative_projects
  change
    (pathLoopClass
        ((regularFamilyDeckPathLoop A.periods g₀
          A.cuspRegularCoverPoint A.cuspRegularDeckPath).cast
            hbase.symm hbase.symm))⁻¹ *
        pathLoopClass
          (((regularFamilyPeriodLoop A.periods
            A.cuspRegularCoverPoint a).map
              (regularFamilyQuotientMap A.periods).continuous).cast
                hbase.symm hbase.symm) *
        pathLoopClass
          ((regularFamilyDeckPathLoop A.periods g₀
            A.cuspRegularCoverPoint A.cuspRegularDeckPath).cast
              hbase.symm hbase.symm) =
      pathLoopClass
        (((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
          (rhoLambda g₀ a)).map
            (regularFamilyQuotientMap A.periods).continuous).cast
              hbase.symm hbase.symm)
  rw [pathLoopClass_cast_eq_elementOfBaseEq
      (regularFamilyDeckPathLoop A.periods g₀
        A.cuspRegularCoverPoint A.cuspRegularDeckPath) hbase,
    pathLoopClass_cast_eq_elementOfBaseEq
      ((regularFamilyPeriodLoop A.periods
        A.cuspRegularCoverPoint a).map
          (regularFamilyQuotientMap A.periods).continuous) hbase,
    pathLoopClass_cast_eq_elementOfBaseEq
      ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
        (rhoLambda g₀ a)).map
          (regularFamilyQuotientMap A.periods).continuous) hbase]
  have htransport := congrArg
    (fundamentalGroupElementOfBaseEq hbase) h
  simpa only [fundamentalGroupElementOfBaseEq_mul,
    fundamentalGroupElementOfBaseEq_inv] using htransport

/-- Inner correction by the chosen cusp power.  It removes the common peripheral conjugator
from the corrected translation marking while leaving the cusp meridian fixed. -/
public noncomputable def cuspCentralMarkingCorrection :
    MulAut (FundamentalGroup A.CentralFamily A.cuspCentralBase) :=
  MulAut.conj
    ((A.cuspCentralMeridian ^
      A.geometricCentralCuspConjugatorExponent)⁻¹)

/-- The inner cusp correction sends each corrected translation to the literal translation with
the original lattice label. -/
public theorem cuspCentralMarkingCorrection_translation (a : Lattice) :
    A.cuspCentralMarkingCorrection
        (Additive.toMul (A.correctedActualCuspCentralTranslation a)) =
      Additive.toMul (A.cuspCentralTranslation a) := by
  let n := A.geometricCentralCuspConjugatorExponent
  let M := A.cuspCentralMeridian
  have hdeck : A.cuspOuterDeckHom (M ^ n) =
      MulOpposite.op (g₀ ^ n) := by
    dsimp only [M]
    rw [map_zpow, A.cuspOuterDeckHom_meridian]
    rfl
  have hconj := A.cuspCentralLoop_conjugates_translation_of_outerDeck
    (g₀ ^ n) (M ^ n) hdeck
      (rhoLambda ((g₁ * g₂) ^ n) a)
  unfold cuspCentralMarkingCorrection correctedActualCuspCentralTranslation
  simp only [MulAut.conj_apply, AddMonoidHom.comp_apply, inv_inv]
  change (A.cuspCentralMeridian ^
          A.geometricCentralCuspConjugatorExponent)⁻¹ *
        Additive.toMul (A.cuspCentralTranslation
          (rhoLambda ((g₁ * g₂) ^
            A.geometricCentralCuspConjugatorExponent) a)) *
        A.cuspCentralMeridian ^
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
public theorem cuspCentralMarkingCorrection_meridian :
    A.cuspCentralMarkingCorrection A.cuspCentralMeridian =
      A.cuspCentralMeridian := by
  unfold cuspCentralMarkingCorrection
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
public theorem cuspCentralFundamentalGroup_generated :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.cuspCentralTranslation a)) ∪
        {A.geometricCentralRhoOne, A.geometricCentralRhoTwo}) = ⊤ := by
  rw [← A.geometricCentralTranslation_range_eq_cuspCentralTranslation]
  exact A.geometricCentralFundamentalGroup_generated

/-- The actual cusp translations with the peripheral-conjugator marking and the two geometric
finite meridians form an affine-core presentation with the paper's monodromy matrices. -/
public noncomputable def cuspGeometricCorePiOneData :
    AffineTorusCorePiOneData
      (FundamentalGroup A.CentralFamily A.cuspCentralBase)
      Lattice paperMonodromyOne paperMonodromyTwo where
  translation := A.correctedActualCuspCentralTranslation
  rhoOne := A.geometricCentralRhoOne
  rhoTwo := A.geometricCentralRhoTwo
  conjugate_one := A.geometricCentralRhoOne_conjugates_correctedTranslation
  conjugate_two := A.geometricCentralRhoTwo_conjugates_correctedTranslation
  generators_generate := by
    rw [A.correctedActualCuspCentralTranslation_range_eq_actual]
    exact A.cuspCentralFundamentalGroup_generated

end SphereSixComplex.Geometry.PaperAnalyticData

end
