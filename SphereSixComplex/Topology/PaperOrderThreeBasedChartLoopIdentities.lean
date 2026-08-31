module

public import SphereSixComplex.Topology.PaperOrderThreeExplicitBasedBoundaryCoverComparison

/-!
# Literal loops for the based order-three boundary comparison

The physical translation and positive angular generators are represented here by straight paths
from the selected point of the explicit radial cover to its deck translates.  Their projections
are proved to represent the corresponding `ofDeck` classes.  This reduces the based chart
comparison to exact equalities between these concrete projected paths and the already constructed
global period and finite-meridian loops, transported along one fixed path.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The straight path in the explicit radial cover from its selected basepoint to a deck
translate.  The radial coordinate is fixed and the affine cover coordinates follow the segment
joining the two endpoints. -/
public noncomputable def orderThreeActualEllipticBoundaryDeckStraightLift
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticBoundaryBase
      (g • A.orderThreeActualEllipticBoundaryBase) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let b := A.orderThreeActualEllipticBoundaryBase
  exact {
    toFun := fun t ↦ (b.1, Path.segment b.2 (g • b.2) t)
    continuous_toFun :=
      continuous_const.prodMk (Path.segment b.2 (g • b.2)).continuous
    source' := by rw [(Path.segment b.2 (g • b.2)).source]
    target' := by
      rw [(Path.segment b.2 (g • b.2)).target]
      change (b.1, g • b.2) = (b.1, g • b.2)
      rfl
  }

/-- Projection of the straight deck path is a loop in the literal order-three overlap. -/
public noncomputable def orderThreeActualEllipticBoundaryDeckStraightLoop
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase)
      (A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
  exact ((A.orderThreeActualEllipticBoundaryDeckStraightLift g).map
      A.orderThreeActualEllipticBoundaryProjection.continuous).cast rfl
        (hp.map_smul g).symm

/-- The straight projected loop represents exactly the `ofDeck` class with the same deck
label.  In particular, no inverse is introduced at this stage. -/
public theorem orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    Path.Homotopic.Quotient.mk (A.orderThreeActualEllipticBoundaryDeckStraightLoop g) =
      ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase g := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
  let e : A.orderThreeActualEllipticBoundaryProjection ⁻¹'
      {A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase} :=
    ⟨A.orderThreeActualEllipticBoundaryBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  let e' : A.orderThreeActualEllipticBoundaryProjection ⁻¹'
      {A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase} :=
    ⟨g • A.orderThreeActualEllipticBoundaryBase, hp.map_smul g⟩
  let Γ : Path.Homotopic.Quotient A.orderThreeActualEllipticBoundaryBase
      (g • A.orderThreeActualEllipticBoundaryBase) :=
    Path.Homotopic.Quotient.mk (A.orderThreeActualEllipticBoundaryDeckStraightLift g)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq (ex := e) (ey := e') Γ (by
    dsimp [e, e']
    change (Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightLift g)).map
          A.orderThreeActualEllipticBoundaryProjection =
      (Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightLoop g)).cast _ _
    rw [← Path.Homotopic.Quotient.mk_map]
    unfold orderThreeActualEllipticBoundaryDeckStraightLoop
    rw [Path.Homotopic.Quotient.mk_cast]
    exact eq_of_heq
      ((Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm

/-- The endpoint of a physical lattice-translation lift is the literal period translate of the
selected affine coordinate. -/
public theorem orderThreeActualEllipticBoundaryTranslation_endpoint (a : Lattice) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderThreeDescendedAffineTorusAutomorphism A.periods) a) •
        A.orderThreeActualEllipticBoundaryBase.2 =
      (A.orderThreeActualEllipticBoundaryBase.2.1,
        periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne).1 a +
          A.orderThreeActualEllipticBoundaryBase.2.2) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  exact affineTorusMappingTorusDeckTranslation_smul _ _ _ _

/-- The positive angular deck generator moves one turn in the negative real-cover direction and
applies the order-three affine clutching lift. -/
public theorem orderThreeActualEllipticBoundaryPositiveMeridian_endpoint :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods) •
        A.orderThreeActualEllipticBoundaryBase.2 =
      (A.orderThreeActualEllipticBoundaryBase.2.1 - 1,
        (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
            A.orderThreeActualEllipticBoundaryBase.2.2 +
          (3 : ℂ)⁻¹ • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  exact affineTorusMappingTorusDeckMeridian_smul _ _ _

/-- The affine presentation sends a translation to the corresponding corrected literal cusp
period loop. -/
public theorem paperPuncturedGlobalFamilyAffinePresentation_translation_loop
    (a : Lattice) :
    paperPuncturedGlobalFamilyAffinePresentation A
        (Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) a)) =
      Path.Homotopic.Quotient.mk
        (A.actualCuspCentralPeriodLoop
          (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) a)) := by
  unfold paperPuncturedGlobalFamilyAffinePresentation
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_translation]
  change Additive.toMul (A.actualCuspCentralTranslation
    (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) a)) = _
  rw [A.actualCuspCentralTranslation_eq_periodLoop]

/-- The inverse first free meridian occurring in the order-three chart statement is the inverse
geometric first meridian.  Together with the preceding positive-deck formula, this records the
opposite-group sign convention explicitly. -/
public theorem paperPuncturedGlobalFamilyAffinePresentation_firstMeridian_inv :
    paperPuncturedGlobalFamilyAffinePresentation A
        (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ =
      A.geometricCentralRhoOne⁻¹ := by
  rw [map_inv]
  unfold paperPuncturedGlobalFamilyAffinePresentation
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_first,
    paperPuncturedGlobalFamilyAffineCorePiOneData_rhoOne]

/-- One fixed path used for both translation and meridian comparisons. -/
public noncomputable def orderThreeCentralBoundaryChartPath :
    Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase := by
  rw [← A.centralAffineBase_eq_actualCuspCentralBase]
  exact A.orderThreeCentralBaseWhisker

/-- The exact remaining coordinate calculation, expressed with concrete source and target
loops.  The source loops are straight segments in the explicit radial universal cover; the
target translation loops are literal global period loops, and the target angular loop is the
inverse geometric first finite meridian. -/
public def OrderThreeCentralBoundaryStraightLoopIdentities : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  (∀ a : Lattice,
    FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightLoop
            (Additive.toMul (affineTorusMappingTorusDeckTranslation
              (orderThreeDescendedAffineTorusAutomorphism A.periods) a)))) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBoundaryChartPath
        (Path.Homotopic.Quotient.mk
          (A.actualCuspCentralPeriodLoop
            (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) a)))) ∧
  FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      (Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightLoop
          (affineTorusMappingTorusDeckMeridian
            (orderThreeDescendedAffineTorusAutomorphism A.periods)))) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      A.orderThreeCentralBoundaryChartPath A.geometricCentralRhoOne⁻¹

/-- The concrete straight-loop identities imply the based chart identities. -/
public theorem OrderThreeCentralBoundaryStraightLoopIdentities.toBasedChartIdentities
    (h : A.OrderThreeCentralBoundaryStraightLoopIdentities) :
    A.OrderThreeCentralBoundaryBasedChartIdentities := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  change (∀ a : Lattice, _) ∧ _ at h
  refine ⟨A.orderThreeCentralBoundaryChartPath, ?_, ?_⟩
  · intro a
    rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    rw [A.paperPuncturedGlobalFamilyAffinePresentation_translation_loop]
    exact h.1 a
  · rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    rw [A.paperPuncturedGlobalFamilyAffinePresentation_firstMeridian_inv]
    exact h.2

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
