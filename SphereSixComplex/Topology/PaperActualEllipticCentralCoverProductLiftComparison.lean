module

public import SphereSixComplex.Topology.PaperActualEllipticWholeRelatorClassificationProof
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeMarkedWhiskerLoopClassesProof
public import SphereSixComplex.Topology.PaperEllipticCollarLoopClassProof

/-!
# Product-lift comparison for the complete elliptic relations

The Cayley-coordinate calculation and the principal-gauge calculation determine the complete
central affine deck products.  This file reduces each whole-relator chart identity to one
endpoint calculation for the lift of the complete regular loop to the based-path universal
cover.  Thus the remaining input is a single point-set comparison for each elliptic point, not
independent choices for the meridian and fibre generators.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The central affine deck product classified by the order-three Cayley and principal-gauge
windings. -/
public noncomputable def orderThreeFillingRelationClassifiedCentralProductDeck :
    paperCentralFreeAffineDeck :=
  freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian ^ 3 *
    (Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))⁻¹

/-- The central affine deck product classified by the order-four Cayley and principal-gauge
windings. -/
public noncomputable def orderFourFillingRelationClassifiedCentralProductDeck :
    paperCentralFreeAffineDeck :=
  freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian ^ 4 *
    (Additive.toMul
      (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon'))⁻¹

public theorem orderThreeFillingRelationClassifiedCentralProductDeck_eq :
    orderThreeFillingRelationClassifiedCentralProductDeck =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian ^ 3 *
        Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon) := by
  simp [orderThreeFillingRelationClassifiedCentralProductDeck]

public theorem orderFourFillingRelationClassifiedCentralProductDeck_eq :
    orderFourFillingRelationClassifiedCentralProductDeck =
      freeAffineLift (M := paperCentralFreeMonodromy) secondMeridian ^ 4 *
        Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon')) := by
  simp [orderFourFillingRelationClassifiedCentralProductDeck]

/-- The physical order-three complete relation has exactly the inverse classified central
product label in the based-path orientation. -/
public theorem paperOrderThreeActualBoundaryToUniversalDeck_fillingRelation :
    A.paperOrderThreeActualBoundaryToUniversalDeck
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
      orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ := by
  have hcomm : Commute
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)
      (Additive.toMul
        (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) := by
    rw [commute_iff_eq]
    have h := freeAffine_conjugate
      (M := paperCentralFreeMonodromy) firstMeridian epsilon
    rw [show (paperCentralFreeMonodromy firstMeridian).toAdd epsilon = epsilon by
      unfold paperCentralFreeMonodromy freeTwoMeridianMonodromy
        integralOrbifoldPeriodMonodromy
      change (rhoLambda ((twoMeridianOrbifoldMap g₁ g₂) firstMeridian)) epsilon = epsilon
      rw [twoMeridianOrbifoldMap_first, rhoLambda_g₁_apply, A₁_epsilon]] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    orderThreeActualEllipticBoundaryDeckData, map_mul, map_pow, map_inv]
  rw [A.paperOrderThreeActualBoundaryToUniversalDeck_positive_meridian]
  rw [A.paperOrderThreeActualBoundaryToUniversalDeck_translation]
  rw [orderThreeFillingRelationClassifiedCentralProductDeck]
  simp only [map_neg, toMul_neg, inv_inv, inv_pow]
  exact (hcomm.pow_left 3).inv.symm

/-- The order-three expected relator is the affine presentation of the classified product. -/
public theorem orderThreeCentralExpectedRelator_eq_classifiedPresentation :
    A.orderThreeCentralExpectedRelator =
      A.actualCuspToCentralAffineBaseEquiv
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderThreeFillingRelationClassifiedCentralProductDeck) := by
  rw [orderThreeCentralExpectedRelator,
    orderThreeFillingRelationClassifiedCentralProductDeck, map_mul, map_pow, map_inv]
  rw [centralAffineCorePiOneData_rhoOne, centralAffineCorePiOneData_translation]
  unfold paperPuncturedGlobalFamilyAffinePresentation
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_first]
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_translation]
  rw [paperPuncturedGlobalFamilyAffineCorePiOneData_rhoOne]
  rw [paperPuncturedGlobalFamilyAffineCorePiOneData_translation]
  rw [map_mul, map_pow, map_inv]

/-- The order-four expected relator is the affine presentation of the classified product. -/
public theorem orderFourCentralExpectedRelator_eq_classifiedPresentation :
    A.orderFourCentralExpectedRelator =
      A.actualCuspToCentralAffineBaseEquiv
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderFourFillingRelationClassifiedCentralProductDeck) := by
  rw [orderFourCentralExpectedRelator,
    orderFourFillingRelationClassifiedCentralProductDeck, map_mul, map_pow, map_inv]
  rw [centralAffineCorePiOneData_rhoTwo, centralAffineCorePiOneData_translation]
  unfold paperPuncturedGlobalFamilyAffinePresentation
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_second]
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_translation]
  rw [paperPuncturedGlobalFamilyAffineCorePiOneData_rhoTwo]
  rw [paperPuncturedGlobalFamilyAffineCorePiOneData_translation]
  rw [map_mul, map_pow, map_inv]

/-- The based-path universal-cover point represented by a connector from the actual cusp base. -/
public noncomputable def centralAffineUniversalCoverPointOfPath
    {y : A.CentralFamily} (beta : Path A.actualCuspCentralBase y) :
    A.centralAffineUniversalCover.Cover := by
  change TauCeti.UniversalCover A.actualCuspCentralBase
  exact TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath beta)

@[simp]
public theorem centralAffineUniversalCoverPointOfPath_projects
    {y : A.CentralFamily} (beta : Path A.actualCuspCentralBase y) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection (A.centralAffineUniversalCoverPointOfPath beta) = y := by
  change TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath beta)) = y
  rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]

/-- At the point represented by `beta`, a transported affine-presentation loop has the inverse
deck label. -/
public theorem centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv
    {y : A.CentralFamily} (beta : Path A.actualCuspCentralBase y)
    (d : paperCentralFreeAffineDeck) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPointOfPath beta,
          A.centralAffineUniversalCoverPointOfPath_projects beta⟩
        (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A d)) =
      MulOpposite.op d⁻¹ := by
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_locallyPathConnected
      A.modular.modularParameter A.periods
  let _ : PathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_pathConnected
      A.modular.modularParameter A.periods
  let _ : TauCeti.SemilocallySimplyConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
      A.modular.modularParameter A.periods
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let g := paperPuncturedGlobalFamilyAffinePresentation A d
  let delta := FundamentalGroup.fundamentalGroupMulEquivOfPath beta g
  let e : (TauCeti.UniversalCover.proj (x₀ := A.actualCuspCentralBase)) ⁻¹' {y} :=
    ⟨TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath beta), by
      change TauCeti.UniversalCover.proj
        (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
          (BasedPath.ofPath beta)) = y
      rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]⟩
  apply (D.data.quotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  change (paperPuncturedGlobalFamilyAffinePresentation A d⁻¹) •
      TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath beta) =
    ((TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).monodromy delta.toPath e :
      TauCeti.UniversalCover A.actualCuspCentralBase)
  rw [map_inv]
  obtain ⟨gamma, hgamma⟩ := Quotient.exists_rep delta.toPath
  rw [← hgamma]
  let eta : Path (BasedPath.endpoint (BasedPath.ofPath beta)) y :=
    gamma.cast (BasedPath.endpoint_ofPath _) rfl
  have hgamma0 : gamma 0 = TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.ofPath beta)) := by
    rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]
    exact gamma.source
  have heta0 : eta 0 = TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.ofPath beta)) := by
    rw [TauCeti.UniversalCover.proj_ofBasedPath]
    exact eta.source
  change g⁻¹ • TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
      (BasedPath.ofPath beta) =
    (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath gamma
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath beta))
      hgamma0 1
  have hlift :
      (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath gamma
          (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
            (BasedPath.ofPath beta)) hgamma0 1 =
        TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
          (BasedPath.append (BasedPath.ofPath beta) eta) := by
    calc
      _ = (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath eta
          (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
            (BasedPath.ofPath beta)) heta0 1 := by congr 1
      _ = _ := TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append eta
  rw [hlift, TauCeti.UniversalCover.ofBasedPath_ofPath,
    TauCeti.UniversalCover.inv_smul_mk, TauCeti.UniversalCover.ofBasedPath_def]
  let hend := BasedPath.endpoint_append (BasedPath.ofPath beta) eta
  apply TauCeti.UniversalCover.ext hend.symm
  have hcast : HEq
      (Path.Homotopic.Quotient.mk
        (BasedPath.append (BasedPath.ofPath beta) eta).toPath)
      (Path.Homotopic.Quotient.mk (beta.trans gamma)) :=
    Path.Homotopic.hpath_hext (fun _ ↦ rfl)
  refine (heq_of_eq ?_).trans hcast.symm
  simp only [Path.Homotopic.Quotient.mk_trans]
  have htrans := congrArg
    (fun q ↦ (Path.Homotopic.Quotient.mk beta).trans q) hgamma
  have hdelta : g.toPath.trans (Path.Homotopic.Quotient.mk beta) =
      (Path.Homotopic.Quotient.mk beta).trans delta.toPath := by
    change g.toPath.trans (Path.Homotopic.Quotient.mk beta) =
      (Path.Homotopic.Quotient.mk beta).trans
        ((Path.Homotopic.Quotient.mk beta).symm.trans
          (g.toPath.trans (Path.Homotopic.Quotient.mk beta)))
    rw [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
  exact hdelta.trans htrans.symm

/-- The geometric connector, regarded as a path from the based-path cover's basepoint. -/
public noncomputable def orderThreeActualCentralProductConnector :
    Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase :=
  A.orderThreeActualCentralGeometricConnector.cast
    A.centralAffineBase_eq_actualCuspCentralBase.symm rfl

/-- The order-four analogue of the geometric based-path connector. -/
public noncomputable def orderFourActualCentralProductConnector :
    Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase :=
  A.orderFourActualCentralGeometricConnector.cast
    A.centralAffineBase_eq_actualCuspCentralBase.symm rfl

/-- In the local product coordinates, the complete order-three regular loop is exactly the
one-turn Cayley loop together with the principal-gauge loop and its fixed fibre offset. -/
public theorem orderThreeFillingRelationRegularLoop_localProductCoordinate
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (((orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative
              (A.orderThreeActualEllipticBoundaryDeckStraightLift
                A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ),
      (orderThreeRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderThreeFillingRelationRegularLoop t))).2) =
      ((A.orderThreeFillingRelationCayleyLoop t).1,
        A.orderThreeFillingRelationPrincipalGaugeLoop t +
          Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  apply Prod.ext
  · exact A.orderThreeFillingRelationCayleyLoop_apply t
  · rw [A.orderThreeFillingRelationRegularLoop_realPeriod_snd]
    rw [A.orderThreeFillingRelationPrincipalGaugeLoop_apply]

/-- The analogous exact local-product description of the order-four complete loop. -/
public theorem orderFourFillingRelationRegularLoop_localProductCoordinate
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    (((orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative
              (A.orderFourActualEllipticBoundaryDeckStraightLift
                A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ),
      (orderFourRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderFourFillingRelationRegularLoop t))).2) =
      ((A.orderFourFillingRelationCayleyLoop t).1,
        A.orderFourFillingRelationPrincipalGaugeLoop t +
          Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  apply Prod.ext
  · exact A.orderFourFillingRelationCayleyLoop_apply t
  · rw [A.orderFourFillingRelationRegularLoop_realPeriod_snd]
    rw [A.orderFourFillingRelationPrincipalGaugeLoop_apply]

/-- The single remaining order-three point-set statement: the complete regular loop has the
classified product endpoint in the central affine universal cover. -/
public def OrderThreeActualEllipticCentralCoverProductLiftComparison : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPointOfPath beta,
        A.centralAffineUniversalCoverPointOfPath_projects beta⟩
      (Path.Homotopic.Quotient.mk
        ((A.orderThreeFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderThreeCollarRegularRepresentative_base_projects.symm
            A.orderThreeCollarRegularRepresentative_base_projects.symm)) =
    MulOpposite.op orderThreeFillingRelationClassifiedCentralProductDeck⁻¹

/-- The single remaining order-four point-set statement. -/
public def OrderFourActualEllipticCentralCoverProductLiftComparison : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPointOfPath beta,
        A.centralAffineUniversalCoverPointOfPath_projects beta⟩
      (Path.Homotopic.Quotient.mk
        ((A.orderFourFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderFourCollarRegularRepresentative_base_projects.symm
            A.orderFourCollarRegularRepresentative_base_projects.symm)) =
    MulOpposite.op orderFourFillingRelationClassifiedCentralProductDeck⁻¹

/-- Endpoint form of the order-three comparison.  This is the literal remaining point-set
calculation in the chosen universal cover. -/
public def OrderThreeActualEllipticCentralCoverProductMonodromyEndpoint : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let beta := A.orderThreeActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ • e.1 =
    D.data.quotientCovering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk
        ((A.orderThreeFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderThreeCollarRegularRepresentative_base_projects.symm
            A.orderThreeCollarRegularRepresentative_base_projects.symm)) e

/-- Endpoint form of the order-four comparison. -/
public def OrderFourActualEllipticCentralCoverProductMonodromyEndpoint : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let beta := A.orderFourActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  orderFourFillingRelationClassifiedCentralProductDeck⁻¹ • e.1 =
    D.data.quotientCovering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk
        ((A.orderFourFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm)) e

/-- The exact global marking still required after the local Cayley and gauge computations: the
projected complete loop must be the transported affine-presentation loop through the chosen
geometric connector. -/
public def OrderThreeActualEllipticCentralProductPathClassIdentity : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let beta := A.orderThreeActualCentralProductConnector
  Path.Homotopic.Quotient.mk
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath beta
      (paperPuncturedGlobalFamilyAffinePresentation A
        orderThreeFillingRelationClassifiedCentralProductDeck)

/-- Order-four form of the remaining global marking identity. -/
public def OrderFourActualEllipticCentralProductPathClassIdentity : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let beta := A.orderFourActualCentralProductConnector
  Path.Homotopic.Quotient.mk
      ((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath beta
      (paperPuncturedGlobalFamilyAffinePresentation A
        orderFourFillingRelationClassifiedCentralProductDeck)

public theorem orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity :
    A.OrderThreeActualEllipticCentralCoverProductLiftComparison ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  let E := D.data.quotientCovering.fundamentalGroupEquiv e
  let loopClass := Path.Homotopic.Quotient.mk
    ((A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm)
  let expectedClass := FundamentalGroup.fundamentalGroupMulEquivOfPath beta
    (paperPuncturedGlobalFamilyAffinePresentation A
      orderThreeFillingRelationClassifiedCentralProductDeck)
  have hexpected : E expectedClass =
      MulOpposite.op orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ :=
    A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _
  change E loopClass = _ ↔ loopClass = expectedClass
  constructor
  · intro h
    exact E.injective (h.trans hexpected.symm)
  · intro h
    rw [h]
    exact hexpected

public theorem orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity :
    A.OrderFourActualEllipticCentralCoverProductLiftComparison ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  let E := D.data.quotientCovering.fundamentalGroupEquiv e
  let loopClass := Path.Homotopic.Quotient.mk
    ((A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm)
  let expectedClass := FundamentalGroup.fundamentalGroupMulEquivOfPath beta
    (paperPuncturedGlobalFamilyAffinePresentation A
      orderFourFillingRelationClassifiedCentralProductDeck)
  have hexpected : E expectedClass =
      MulOpposite.op orderFourFillingRelationClassifiedCentralProductDeck⁻¹ :=
    A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _
  change E loopClass = _ ↔ loopClass = expectedClass
  constructor
  · intro h
    exact E.injective (h.trans hexpected.symm)
  · intro h
    rw [h]
    exact hexpected

public theorem orderThreeCentralCoverProductLiftComparison_iff_monodromyEndpoint :
    A.OrderThreeActualEllipticCentralCoverProductLiftComparison ↔
      A.OrderThreeActualEllipticCentralCoverProductMonodromyEndpoint := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  unfold OrderThreeActualEllipticCentralCoverProductLiftComparison
    OrderThreeActualEllipticCentralCoverProductMonodromyEndpoint
  exact D.data.quotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff

public theorem orderFourCentralCoverProductLiftComparison_iff_monodromyEndpoint :
    A.OrderFourActualEllipticCentralCoverProductLiftComparison ↔
      A.OrderFourActualEllipticCentralCoverProductMonodromyEndpoint := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  unfold OrderFourActualEllipticCentralCoverProductLiftComparison
    OrderFourActualEllipticCentralCoverProductMonodromyEndpoint
  exact D.data.quotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff

/-- The endpoint calculation is equivalent to the one exact global path-class marking. -/
public theorem orderThreeCentralCoverProductMonodromyEndpoint_iff_pathClassIdentity :
    A.OrderThreeActualEllipticCentralCoverProductMonodromyEndpoint ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity :=
  A.orderThreeCentralCoverProductLiftComparison_iff_monodromyEndpoint.symm.trans
    A.orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity

/-- Order-four analogue of the endpoint/path-class equivalence. -/
public theorem orderFourCentralCoverProductMonodromyEndpoint_iff_pathClassIdentity :
    A.OrderFourActualEllipticCentralCoverProductMonodromyEndpoint ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity :=
  A.orderFourCentralCoverProductLiftComparison_iff_monodromyEndpoint.symm.trans
    A.orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity

/-- The single order-three product-lift endpoint calculation implies the complete chart
identity. -/
public theorem OrderThreeActualEllipticCentralCoverProductLiftComparison.toWholeIdentity
    (h : A.OrderThreeActualEllipticCentralCoverProductLiftComparison) :
    A.OrderThreeWholeFillingRelatorChartIdentity := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  let E := D.data.quotientCovering.fundamentalGroupEquiv e
  let loopClass := Path.Homotopic.Quotient.mk
    ((A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm)
  have htransport :
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector A.orderThreeCentralExpectedRelator =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) := by
    rw [A.orderThreeCentralExpectedRelator_eq_classifiedPresentation]
    simpa [beta, orderThreeActualCentralProductConnector,
      actualCuspToCentralAffineBaseEquiv,
      fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
      fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
        A.orderThreeActualCentralGeometricConnector
        A.centralAffineBase_eq_actualCuspCentralBase.symm
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderThreeFillingRelationClassifiedCentralProductDeck)
  have hlabelExpected :
      E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderThreeFillingRelationClassifiedCentralProductDeck)) =
        MulOpposite.op orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ := by
    exact A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
      orderThreeFillingRelationClassifiedCentralProductDeck
  have hloop :
      loopClass =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector A.orderThreeCentralExpectedRelator := by
    apply E.injective
    rw [htransport]
    exact h.trans hlabelExpected.symm
  let hover := A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨A.orderThreeActualCentralGeometricConnector.cast rfl hover.symm, ?_⟩
  rw [A.orderThreeActualCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover loopClass =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.orderThreeActualCentralGeometricConnector.cast rfl hover.symm)
      A.orderThreeCentralExpectedRelator
  rw [hloop]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    A.orderThreeActualCentralGeometricConnector hover.symm
      A.orderThreeCentralExpectedRelator).symm

/-- The order-four product-lift endpoint calculation implies its complete chart identity. -/
public theorem OrderFourActualEllipticCentralCoverProductLiftComparison.toWholeIdentity
    (h : A.OrderFourActualEllipticCentralCoverProductLiftComparison) :
    A.OrderFourWholeFillingRelatorChartIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let e : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  let E := D.data.quotientCovering.fundamentalGroupEquiv e
  let loopClass := Path.Homotopic.Quotient.mk
    ((A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm)
  have htransport :
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderFourActualCentralGeometricConnector A.orderFourCentralExpectedRelator =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) := by
    rw [A.orderFourCentralExpectedRelator_eq_classifiedPresentation]
    simpa [beta, orderFourActualCentralProductConnector,
      actualCuspToCentralAffineBaseEquiv,
      fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
      fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
        A.orderFourActualCentralGeometricConnector
        A.centralAffineBase_eq_actualCuspCentralBase.symm
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderFourFillingRelationClassifiedCentralProductDeck)
  have hlabelExpected :
      E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderFourFillingRelationClassifiedCentralProductDeck)) =
        MulOpposite.op orderFourFillingRelationClassifiedCentralProductDeck⁻¹ := by
    exact A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
      orderFourFillingRelationClassifiedCentralProductDeck
  have hloop :
      loopClass =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderFourActualCentralGeometricConnector A.orderFourCentralExpectedRelator := by
    apply E.injective
    rw [htransport]
    exact h.trans hlabelExpected.symm
  let hover := A.orderFourActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨A.orderFourActualCentralGeometricConnector.cast rfl hover.symm, ?_⟩
  rw [A.orderFourActualCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover loopClass =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.orderFourActualCentralGeometricConnector.cast rfl hover.symm)
      A.orderFourCentralExpectedRelator
  rw [hloop]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    A.orderFourActualCentralGeometricConnector hover.symm
      A.orderFourCentralExpectedRelator).symm

/-- The two product-lift endpoint comparisons imply the exact remaining normal-closure
residual. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_centralCoverProductLiftComparisons
    (hThree : A.OrderThreeActualEllipticCentralCoverProductLiftComparison)
    (hFour : A.OrderFourActualEllipticCentralCoverProductLiftComparison) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_wholeFillingRelatorChartIdentities
    (hThree.toWholeIdentity A) (hFour.toWholeIdentity A)

/-- Consequently, the two exact global path-class markings are the only remaining inputs for the
normal-closure residual. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_centralProductPathClassIdentities
    (hThree : A.OrderThreeActualEllipticCentralProductPathClassIdentity)
    (hFour : A.OrderFourActualEllipticCentralProductPathClassIdentity) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_centralCoverProductLiftComparisons
    (A.orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr hThree)
    (A.orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr hFour)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
