module

public import SphereSixComplex.Topology.PaperOrderThreeCentralBoundaryCoverComparison

/-!
# Reduction of the order-three boundary comparison to generator monodromy

The continuous lift of the literal collar chart already follows from the universal lifting
property.  The remaining content is that its induced deck homomorphism has the prescribed
orientation on every lattice translation and on the positive angular meridian.  This file
records that exact generator condition and proves that it is sufficient.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The corrected translation and positive-meridian formulas determine the full physical
mapping-torus deck homomorphism. -/
public theorem paperOrderThreeActualBoundaryToUniversalDeck_unique
    (f : OrderThreeAffineMappingTorusDeck A.periods →* paperCentralFreeAffineDeck)
    (htranslation : ∀ a : Lattice,
      f (Additive.toMul (affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)))
    (hmeridian :
      f (affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
        freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian) :
    f = A.paperOrderThreeActualBoundaryToUniversalDeck := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro a
    change f (SemidirectProduct.inl a) =
      A.paperOrderThreeActualBoundaryToUniversalDeck (SemidirectProduct.inl a)
    have ha : SemidirectProduct.inl a =
        Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a.toAdd) := by
      change SemidirectProduct.inl a = SemidirectProduct.inl (Multiplicative.ofAdd a.toAdd)
      exact congrArg
        (SemidirectProduct.inl
          (φ := affineDeckIntegerMonodromy
            (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.toAddEquiv))
        (ofAdd_toAdd a).symm
    rw [ha, htranslation,
      A.paperOrderThreeActualBoundaryToUniversalDeck_translation]
  · apply MonoidHom.ext
    intro n
    have hn : SemidirectProduct.inr n =
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) ^ n.toAdd := by
      change SemidirectProduct.inr n =
        (SemidirectProduct.inr (Multiplicative.ofAdd 1)) ^ n.toAdd
      rw [← map_zpow]
      congr 1
      apply Multiplicative.toAdd.injective
      simp
    change f (SemidirectProduct.inr n) =
      A.paperOrderThreeActualBoundaryToUniversalDeck (SemidirectProduct.inr n)
    rw [hn, map_zpow, map_zpow, hmeridian,
      A.paperOrderThreeActualBoundaryToUniversalDeck_positive_meridian]

/-- The target deck label obtained by applying the literal overlap map to the loop belonging to
a physical mapping-torus deck transformation. -/
public noncomputable def orderThreeCentralBoundaryMappedDeckClass
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    paperCentralFreeAffineDeckᵐᵒᵖ := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  exact D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
    (FundamentalGroup.mapOfEq C.baseMap
      (C.commutes A.orderThreeActualEllipticBoundaryBase)
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase g))

/-- Naturality identifies the mapped loop label with the deck map of the canonical continuous
lift. -/
public theorem orderThreeCentralBoundaryMappedDeckClass_eq
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let C := A.orderThreeActualCentralCoverComparison
    A.orderThreeCentralBoundaryMappedDeckClass g = MulOpposite.op (C.deckMap g) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact A.orderThreeActualCentralCoverComparison_ofDeck g

/-- Exact loop-level residual.  It asks for the images of the explicit mapping-torus generator
loops under the literal collar chart, stated in the target cover's based-path convention. -/
public def OrderThreeCentralBoundaryGeneratorMonodromy : Prop :=
  (∀ a : Lattice,
    A.orderThreeCentralBoundaryMappedDeckClass
        (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      MulOpposite.op
        (Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)))) ∧
  A.orderThreeCentralBoundaryMappedDeckClass
      (affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
    MulOpposite.op (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)

/-- The exact generator calculation missing from the canonical continuous lift. -/
public def OrderThreeCentralBoundaryDeckGeneratorCompatibility : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  letI := D.topology
  letI := D.action
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  (∀ a : Lattice,
      C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a))) ∧
    C.deckMap (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian

/-- The loop-level generator calculation is exactly enough to identify the canonical lift's
deck homomorphism on generators. -/
public theorem OrderThreeCentralBoundaryGeneratorMonodromy.toDeckGeneratorCompatibility
    (h : A.OrderThreeCentralBoundaryGeneratorMonodromy) :
    A.OrderThreeCentralBoundaryDeckGeneratorCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  change (∀ a : Lattice,
      A.orderThreeCentralBoundaryMappedDeckClass
          (Additive.toMul (affineTorusMappingTorusDeckTranslation
            (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
        MulOpposite.op
          (Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)))) ∧
    A.orderThreeCentralBoundaryMappedDeckClass
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      MulOpposite.op (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian) at h
  change (∀ a : Lattice,
      C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a))) ∧
    C.deckMap (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian
  constructor
  · intro a
    apply MulOpposite.op_injective
    rw [← A.orderThreeCentralBoundaryMappedDeckClass_eq]
    exact h.1 a
  · apply MulOpposite.op_injective
    rw [← A.orderThreeCentralBoundaryMappedDeckClass_eq]
    exact h.2

/-- Once the literal collar map has the corrected monodromy on the mapping-torus generators,
its canonical continuous lift is the required exact equivariant comparison. -/
public theorem OrderThreeCentralBoundaryDeckGeneratorCompatibility.toCoverComparison
    (h : A.OrderThreeCentralBoundaryDeckGeneratorCompatibility) :
    A.OrderThreeCentralBoundaryCoverComparison := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  change (∀ a : Lattice,
      C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a))) ∧
    C.deckMap (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian at h
  have hdeck : C.deckMap = A.paperOrderThreeActualBoundaryToUniversalDeck :=
    A.paperOrderThreeActualBoundaryToUniversalDeck_unique C.deckMap h.1 h.2
  refine ⟨C, hdeck, ?_⟩
  rfl

/-- The exact loop-level generator calculation supplies the requested point-set comparison. -/
public theorem OrderThreeCentralBoundaryGeneratorMonodromy.toCoverComparison
    (h : A.OrderThreeCentralBoundaryGeneratorMonodromy) :
    A.OrderThreeCentralBoundaryCoverComparison :=
  (h.toDeckGeneratorCompatibility A).toCoverComparison A

/-- Therefore the same generator calculation also yields the canonical simultaneous deck-pair
comparison used by the downstream common-gauge argument. -/
public theorem OrderThreeCentralBoundaryDeckGeneratorCompatibility.canonicalDeckPair
    (h : A.OrderThreeCentralBoundaryDeckGeneratorCompatibility) :
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
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) :=
  (h.toCoverComparison A).canonicalDeckPair A

/-- Loop-level generator monodromy therefore also gives the canonical simultaneous deck pair. -/
public theorem OrderThreeCentralBoundaryGeneratorMonodromy.canonicalDeckPair
    (h : A.OrderThreeCentralBoundaryGeneratorMonodromy) :
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
        Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) :=
  (h.toDeckGeneratorCompatibility A).canonicalDeckPair A

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
