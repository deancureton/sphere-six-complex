module

public import SphereSixComplex.Topology.PaperOrderThreeCentralBoundaryDeckEmbedding
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry
public import SphereSixComplex.Topology.QuotientCoverMapDeckConjugacy

/-!
# The order-three boundary cover comparison

The central universal cover is the based-path universal cover.  Consequently its transported
deck action reverses the deck element represented by a loop.  The physical inverse meridian
therefore maps to the inverse first free lift, while a local translation by `a` maps to the
global affine translation by `-a`.

This file isolates the remaining point-set input: a continuous lift of the literal order-three
collar chart with those equivariance formulas.  Once such a lift is supplied, uniqueness of
lifts proves that its two marked deck transformations and the canonical lift-induced ones differ
by one common conjugator.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

/-- Simultaneous conjugacy is symmetric. -/
public theorem SimultaneouslyConjugate.symm
    {G : Type*} [Group G] {left right : G × G}
    (h : SimultaneouslyConjugate left right) :
    SimultaneouslyConjugate right left := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨c⁻¹, ?_, ?_⟩
  · rw [hfirst]
    group
  · rw [hsecond]
    group

/-- Simultaneous conjugacy is transitive. -/
public theorem SimultaneouslyConjugate.trans
    {G : Type*} [Group G] {left middle right : G × G}
    (h₁ : SimultaneouslyConjugate left middle)
    (h₂ : SimultaneouslyConjugate middle right) :
    SimultaneouslyConjugate left right := by
  obtain ⟨c₁, hfirst₁, hsecond₁⟩ := h₁
  obtain ⟨c₂, hfirst₂, hsecond₂⟩ := h₂
  refine ⟨c₁ * c₂, ?_, ?_⟩
  · rw [hfirst₁, hfirst₂]
    group
  · rw [hsecond₁, hsecond₂]
    group

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The cyclic-affine boundary deck homomorphism with the orientation forced by the based-path
universal cover: lattice translations change sign, while the positive angular meridian retains
the first free-meridian lift. -/
public def paperOrderThreeCentralBoundaryToUniversalDeck :
    CanonicalCyclicAffineBoundaryDeck
        (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv →*
      paperCentralFreeAffineDeck :=
  SemidirectProduct.lift
    ((freeAffineTranslation (M := paperCentralFreeMonodromy)).comp
      (-AddMonoidHom.id Lattice)).toMultiplicative
    paperOrderThreeCentralAngularDeck (by
      intro n
      apply MonoidHom.ext
      intro a
      change Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy)
            (-((integerAffineMonodromy
              (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv
              n a).toAdd))) =
        freeAffineLift (M := paperCentralFreeMonodromy) (firstMeridian ^ n.toAdd) *
          Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a.toAdd)) *
          (freeAffineLift (M := paperCentralFreeMonodromy)
            (firstMeridian ^ n.toAdd))⁻¹
      rw [freeAffine_conjugate]
      congr 2
      rw [map_neg]
      exact congrArg Neg.neg (A.paperOrderThreeCentralMonodromy_zpow n a.toAdd).symm)

@[simp]
public theorem paperOrderThreeCentralBoundaryToUniversalDeck_translation (a : Lattice) :
    A.paperOrderThreeCentralBoundaryToUniversalDeck
        (Additive.toMul (canonicalCyclicAffineTranslation
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv a)) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) := by
  change Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) * 1 = _
  simp

@[simp]
public theorem paperOrderThreeCentralBoundaryToUniversalDeck_meridian :
    A.paperOrderThreeCentralBoundaryToUniversalDeck
        (canonicalCyclicAffineMeridian
          (orderThreeCentralFiberPresentationData A.periods).affine.latticeMap.toAddEquiv) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  change 1 * paperOrderThreeCentralAngularDeck (Multiplicative.ofAdd 1) = _
  rw [one_mul, paperOrderThreeCentralAngularDeck_one]

/-- The physical mapping-torus deck group, mapped with the based-path universal-cover
orientation. -/
public noncomputable def paperOrderThreeActualBoundaryToUniversalDeck :
    OrderThreeAffineMappingTorusDeck A.periods →* paperCentralFreeAffineDeck :=
  A.paperOrderThreeCentralBoundaryToUniversalDeck.comp
    A.orderThreeActualToCentralBoundaryDeckEquiv.toMonoidHom

@[simp]
public theorem paperOrderThreeActualBoundaryToUniversalDeck_translation (a : Lattice) :
    A.paperOrderThreeActualBoundaryToUniversalDeck
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) := by
  rw [paperOrderThreeActualBoundaryToUniversalDeck, MonoidHom.comp_apply]
  change A.paperOrderThreeCentralBoundaryToUniversalDeck
      (A.orderThreeActualToCentralBoundaryDeckEquiv
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) = _
  rw [A.orderThreeActualToCentralBoundaryDeckEquiv_translation,
    A.paperOrderThreeCentralBoundaryToUniversalDeck_translation]

@[simp]
public theorem paperOrderThreeActualBoundaryToUniversalDeck_positive_meridian :
    A.paperOrderThreeActualBoundaryToUniversalDeck
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  rw [paperOrderThreeActualBoundaryToUniversalDeck, MonoidHom.comp_apply]
  change A.paperOrderThreeCentralBoundaryToUniversalDeck
      (A.orderThreeActualToCentralBoundaryDeckEquiv
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods))) = _
  rw [A.orderThreeActualToCentralBoundaryDeckEquiv_meridian,
    A.paperOrderThreeCentralBoundaryToUniversalDeck_meridian]

@[simp]
public theorem paperOrderThreeActualBoundaryToUniversalDeck_physical_meridian :
    A.paperOrderThreeActualBoundaryToUniversalDeck
        A.orderThreeActualEllipticBoundaryDeckData.meridian =
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ := by
  rw [orderThreeActualEllipticBoundaryDeckData, map_inv,
    A.paperOrderThreeActualBoundaryToUniversalDeck_positive_meridian]

/-- The constant-path point of the based-path model underlying the chosen global affine cover. -/
public noncomputable def centralAffineUniversalCoverBasepoint :
    A.centralAffineUniversalCover.Cover := by
  change TauCeti.UniversalCover A.actualCuspCentralBase
  exact (TauCeti.UniversalCover.basepointLift A.actualCuspCentralBase).1

public theorem centralAffineUniversalCoverBasepoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.centralAffineUniversalCoverBasepoint = A.actualCuspCentralBase := by
  change TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.basepointLift A.actualCuspCentralBase).1 =
    A.actualCuspCentralBase
  exact TauCeti.UniversalCover.proj_basepointLift A.actualCuspCentralBase

/-- At the constant-path lift, the quotient-cover equivalence sends a loop represented by the
affine presentation element `d` to `op d⁻¹`.  This is the source of the translation sign in
`paperOrderThreeActualBoundaryToUniversalDeck`. -/
public theorem centralAffineUniversalCoverBasepoint_fundamentalGroupEquiv
    (d : paperCentralFreeAffineDeck) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverBasepoint,
          A.centralAffineUniversalCoverBasepoint_projects⟩
        (paperPuncturedGlobalFamilyAffinePresentation A d) =
      MulOpposite.op d⁻¹ := by
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_locallyPathConnected A.modular.modularParameter A.periods
  let _ : PathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_pathConnected A.modular.modularParameter A.periods
  let _ : TauCeti.SemilocallySimplyConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
      A.modular.modularParameter A.periods
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  apply (D.data.quotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  change (paperPuncturedGlobalFamilyAffinePresentation A d⁻¹) •
      (TauCeti.UniversalCover.basepointLift A.actualCuspCentralBase).1 =
    ((TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).monodromy
      (paperPuncturedGlobalFamilyAffinePresentation A d)
      (TauCeti.UniversalCover.basepointLift A.actualCuspCentralBase) :
        TauCeti.UniversalCover A.actualCuspCentralBase)
  rw [TauCeti.UniversalCover.monodromy_basepointLift, map_inv]

/-- Exact point-set residual for the order-three collar.  The lift must cover the literal
overlap chart and intertwine the explicit local action with the correctly oriented global affine
deck action. -/
public def OrderThreeCentralBoundaryCoverComparison : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  letI := D.topology
  letI := D.action
  ∃ C : QuotientCoverMapData
      (G := OrderThreeAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.orderThreeActualEllipticBoundaryProjection D.data.projection,
    C.deckMap = A.paperOrderThreeActualBoundaryToUniversalDeck ∧
      C.baseMap = A.orderThreeActualOverlapToCentral

/-- The point-set comparison and the canonical lift of the same base map induce deck pairs that
differ by one common conjugator. -/
public theorem OrderThreeCentralBoundaryCoverComparison.canonicalDeckPair
    (h : A.OrderThreeCentralBoundaryCoverComparison) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let C := A.orderThreeActualCentralCoverComparison
    SimultaneouslyConjugate
      (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
        C.deckMap (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
      ((freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹,
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  change ∃ E : QuotientCoverMapData
      (G := OrderThreeAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.orderThreeActualEllipticBoundaryProjection D.data.projection,
    E.deckMap = A.paperOrderThreeActualBoundaryToUniversalDeck ∧
      E.baseMap = A.orderThreeActualOverlapToCentral at h
  obtain ⟨E, hdeck, hbase⟩ := h
  obtain ⟨c, hmeridian, htranslation⟩ :=
    E.exists_deckPair_eq_conj_of_baseMap_eq D.data.quotientCovering C (hbase.trans rfl.symm)
      A.orderThreeActualEllipticBoundaryBase
      A.orderThreeActualEllipticBoundaryDeckData.meridian
      (Additive.toMul
        (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))
  refine ⟨c, ?_, ?_⟩
  · rw [hdeck] at hmeridian
    simpa only [A.paperOrderThreeActualBoundaryToUniversalDeck_physical_meridian] using hmeridian
  · rw [hdeck] at htranslation
    simpa only [orderThreeActualEllipticBoundaryDeckData,
      A.paperOrderThreeActualBoundaryToUniversalDeck_translation, neg_neg] using htranslation

/-- The deck labels of the two central marked loops at the lift selected by the canonical collar
comparison. -/
public noncomputable def orderThreeCentralUniversalDeckMarkedPair :
    paperCentralFreeAffineDeck × paperCentralFreeAffineDeck := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  exact
    (MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.orderThreeActualEllipticBoundaryBase)
            A.orderThreeCentralMeridianAtOverlap)),
      MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.orderThreeActualEllipticBoundaryBase)
            A.orderThreeCentralTranslationAtOverlap)))

/-- The remaining marking-side statement after the point-set collar lift has been isolated.  It
identifies the deck labels of the transported central marked loops with the correctly oriented
free-affine pair, up to the single unavoidable basepoint gauge. -/
public def OrderThreeCentralUniversalDeckMarkingCompatibility : Prop :=
  SimultaneouslyConjugate A.orderThreeCentralUniversalDeckMarkedPair
    ((freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹,
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon))

/-- The point-set cover comparison and the marking comparison together give exactly the deck
compatibility used by the existing local-loop API. -/
public theorem OrderThreeCentralBoundaryCoverComparison.toDeckCompatibility
    (hcover : A.OrderThreeCentralBoundaryCoverComparison)
    (hmark : A.OrderThreeCentralUniversalDeckMarkingCompatibility) :
    A.OrderThreeCentralCoverDeckCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  have hcanonical := hcover.canonicalDeckPair A
  change SimultaneouslyConjugate A.orderThreeCentralUniversalDeckMarkedPair
    ((freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹,
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) at hmark
  change SimultaneouslyConjugate
    (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
      C.deckMap (Additive.toMul
        (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
    ((freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹,
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) at hcanonical
  change SimultaneouslyConjugate A.orderThreeCentralUniversalDeckMarkedPair
    (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
      C.deckMap (Additive.toMul
        (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
  exact hmark.trans hcanonical.symm

/-- Hence the two exact residuals also imply the equivalent marked-loop statement. -/
public theorem OrderThreeCentralBoundaryCoverComparison.toMarkedLoopCompatibility
    (hcover : A.OrderThreeCentralBoundaryCoverComparison)
    (hmark : A.OrderThreeCentralUniversalDeckMarkingCompatibility) :
    A.OrderThreeCentralMarkedLoopCompatibility :=
  (hcover.toDeckCompatibility A hmark).toMarkedLoopCompatibility A

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
