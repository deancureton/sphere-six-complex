module

public import SphereSixComplex.Topology.PaperOrderThreeCentralBoundaryCoverComparisonProof

/-!
# An explicitly based order-three boundary comparison

An arbitrary point in the target fibre conjugates the induced deck homomorphism.  Here the
target point is instead represented by a specified path from the global affine base to the
literal order-three overlap base.  This isolates the remaining geometry as two literal
generator-loop evaluations along the same path.
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

/-- The point of the based-path universal cover represented by a path from the global affine
base to the order-three overlap base. -/
public noncomputable def orderThreeCentralAffineUniversalCoverPointOfPath
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase) :
    A.centralAffineUniversalCover.Cover := by
  change TauCeti.UniversalCover A.actualCuspCentralBase
  exact TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β)

@[simp]
public theorem orderThreeCentralAffineUniversalCoverPointOfPath_projects
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection (A.orderThreeCentralAffineUniversalCoverPointOfPath β) =
      A.orderThreeActualEllipticCentralBase := by
  change TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β)) = _
  rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]

/-- The canonical lift of the literal overlap chart pinned to the point represented by `β`. -/
public noncomputable def orderThreeActualCentralCoverComparisonOfPath
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData
      (G := OrderThreeAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.orderThreeActualEllipticBoundaryProjection D.data.projection := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
    D.data.quotientCovering A.orderThreeActualOverlapToCentral
    A.orderThreeActualEllipticBoundaryBase
    (A.orderThreeCentralAffineUniversalCoverPointOfPath β)
    (by
      rw [A.orderThreeCentralAffineUniversalCoverPointOfPath_projects]
      rfl)

/-- The explicitly based comparison sends the source basepoint to the point represented by
`β`. -/
public theorem orderThreeActualCentralCoverComparisonOfPath_lift_base
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let C := A.orderThreeActualCentralCoverComparisonOfPath β
    C.lift A.orderThreeActualEllipticBoundaryBase =
      A.orderThreeCentralAffineUniversalCoverPointOfPath β := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  apply quotientCoverMapDataOfBaseMap_lift_base
  rw [A.orderThreeCentralAffineUniversalCoverPointOfPath_projects]
  rfl

/-- At the lift represented by `β`, transporting a global affine presentation along `β` does
not introduce a conjugacy ambiguity: the based-path action still records the inverse affine
deck element. -/
public theorem orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (d : paperCentralFreeAffineDeck) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
          A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β
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
  let δ := FundamentalGroup.fundamentalGroupMulEquivOfPath β g
  let e : (TauCeti.UniversalCover.proj (x₀ := A.actualCuspCentralBase)) ⁻¹'
      {A.orderThreeActualEllipticCentralBase} :=
    ⟨TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β), by
      change TauCeti.UniversalCover.proj
          (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β)) =
        A.orderThreeActualEllipticCentralBase
      rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]⟩
  apply (D.data.quotientCovering.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  change (paperPuncturedGlobalFamilyAffinePresentation A d⁻¹) •
      TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β) =
    ((TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).monodromy δ.toPath e :
        TauCeti.UniversalCover A.actualCuspCentralBase)
  rw [map_inv]
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep δ.toPath
  rw [← hγ]
  let η : Path (BasedPath.endpoint (BasedPath.ofPath β))
      A.orderThreeActualEllipticCentralBase :=
    γ.cast (BasedPath.endpoint_ofPath _) rfl
  have hγ0 : γ 0 = TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β)) := by
    rw [TauCeti.UniversalCover.proj_ofBasedPath, BasedPath.endpoint_ofPath]
    exact γ.source
  have hη0 : η 0 = TauCeti.UniversalCover.proj
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β)) := by
    rw [TauCeti.UniversalCover.proj_ofBasedPath]
    exact η.source
  change g⁻¹ • TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
      (BasedPath.ofPath β) =
    (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath γ
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β))
      hγ0 1
  have hlift :
      (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath γ
          (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β))
          hγ0 1 =
        TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
          (BasedPath.append (BasedPath.ofPath β) η) := by
    calc
      _ = (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath η
          (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase (BasedPath.ofPath β))
          hη0 1 := by congr 1
      _ = _ :=
        TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append η
  rw [hlift]
  rw [TauCeti.UniversalCover.ofBasedPath_ofPath,
    TauCeti.UniversalCover.inv_smul_mk]
  rw [TauCeti.UniversalCover.ofBasedPath_def]
  let hend := BasedPath.endpoint_append (BasedPath.ofPath β) η
  apply TauCeti.UniversalCover.ext hend.symm
  have hcast : HEq
      (Path.Homotopic.Quotient.mk (BasedPath.append (BasedPath.ofPath β) η).toPath)
      (Path.Homotopic.Quotient.mk (β.trans γ)) :=
    Path.Homotopic.hpath_hext (fun _ ↦ rfl)
  refine (heq_of_eq ?_).trans hcast.symm
  simp only [Path.Homotopic.Quotient.mk_trans]
  have htrans := congrArg
    (fun q ↦ (Path.Homotopic.Quotient.mk β).trans q) hγ
  have hdelta : g.toPath.trans (Path.Homotopic.Quotient.mk β) =
      (Path.Homotopic.Quotient.mk β).trans δ.toPath := by
    change g.toPath.trans (Path.Homotopic.Quotient.mk β) =
      (Path.Homotopic.Quotient.mk β).trans
        ((Path.Homotopic.Quotient.mk β).symm.trans
          (g.toPath.trans (Path.Homotopic.Quotient.mk β)))
    rw [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans]
  exact hdelta.trans htrans.symm

/-- The remaining literal chart calculation.  Both generator families use one path `β`, so the
statement retains the common basepoint gauge rather than choosing unrelated conjugators. -/
public def OrderThreeCentralBoundaryBasedChartIdentities : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  ∃ β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase,
    (∀ a : Lattice,
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (affineTorusMappingTorusDeckTranslation
              (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) a)))) ∧
    FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (affineTorusMappingTorusDeckMeridian
            (orderThreeDescendedAffineTorusAutomorphism A.periods))) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (paperPuncturedGlobalFamilyAffinePresentation A
          (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹)

/-- Naturality transported from the literal projection of a selected lift to an equal
target basepoint. -/
private theorem quotientCoverFundamentalGroupNaturality_of_lift_eq_to_eq
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    [SimplyConnectedSpace E] [SimplyConnectedSpace E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (C : QuotientCoverMapData (G := G) (H := H) p q) (e : E) (e' : E')
    (he' : C.lift e = e') {x' : X'} (hproj : q e' = x')
    (g : FundamentalGroup X (p e)) :
    hq.fundamentalGroupEquiv ⟨e', hproj⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (((C.commutes e).trans (congrArg q he')).trans hproj) g) =
      (MonoidHom.op C.deckMap) (hp.fundamentalGroupEquiv ⟨e, rfl⟩ g) := by
  subst x'
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality_of_lift_eq
      hp hq C e e' he' g).symm

/-- Naturality computes the deck label of every physical loop for the explicitly based
comparison. -/
public theorem orderThreeActualCentralCoverComparisonOfPath_ofDeck
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.orderThreeActualCentralCoverComparisonOfPath β
    let hbase := (C.commutes A.orderThreeActualEllipticBoundaryBase).trans
      ((congrArg D.data.projection
        (A.orderThreeActualCentralCoverComparisonOfPath_lift_base β)).trans
          (A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β))
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
          A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
        (FundamentalGroup.mapOfEq C.baseMap hbase
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  let hbase := (C.commutes A.orderThreeActualEllipticBoundaryBase).trans
    ((congrArg D.data.projection
      (A.orderThreeActualCentralCoverComparisonOfPath_lift_base β)).trans
        (A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β))
  change _ = (MonoidHom.op C.deckMap) (MulOpposite.op g)
  simpa only [fundamentalGroupEquiv_ofDeck] using
    (quotientCoverFundamentalGroupNaturality_of_lift_eq_to_eq
      A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.orderThreeActualEllipticBoundaryBase
      (A.orderThreeCentralAffineUniversalCoverPointOfPath β)
      (A.orderThreeActualCentralCoverComparisonOfPath_lift_base β)
      (A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β)
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase g))

/-- The literal translation-loop identity forces the corrected negative translation in the
based-path deck action. -/
public theorem orderThreeActualCentralCoverComparisonOfPath_deckMap_translation
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (a : Lattice)
    (hchart :
      letI := A.orderThreeActualEllipticBoundaryAction
      letI : SimplyConnectedSpace
          (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
        A.orderThreeActualEllipticBoundaryCover_simplyConnected
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (affineTorusMappingTorusDeckTranslation
              (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) a)))) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let C := A.orderThreeActualCentralCoverComparisonOfPath β
    C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderThreeDescendedAffineTorusAutomorphism A.periods) a)) =
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) (-a)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck β
    (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderThreeDescendedAffineTorusAutomorphism A.periods) a))
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
        A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
      (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul (affineTorusMappingTorusDeckTranslation
            (orderThreeDescendedAffineTorusAutomorphism A.periods) a)))) =
    MulOpposite.op
      (C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) at hnat
  rw [hchart] at hnat
  let d := Additive.toMul
    (freeAffineTranslation (M := paperCentralFreeMonodromy) a)
  have hfund :=
    A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β d
  have hop : MulOpposite.op
        (C.deckMap (Additive.toMul (affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods) a))) =
      MulOpposite.op d⁻¹ :=
    hnat.symm.trans hfund
  apply MulOpposite.op_injective
  simpa only [d, map_neg, toMul_neg] using hop

/-- The literal positive-angular-loop identity forces the positive first free lift in the
based-path deck action. -/
public theorem orderThreeActualCentralCoverComparisonOfPath_deckMap_meridian
    (β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (hchart :
      letI := A.orderThreeActualEllipticBoundaryAction
      letI : SimplyConnectedSpace
          (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
        A.orderThreeActualEllipticBoundaryCover_simplyConnected
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            (affineTorusMappingTorusDeckMeridian
              (orderThreeDescendedAffineTorusAutomorphism A.periods))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let C := A.orderThreeActualCentralCoverComparisonOfPath β
    C.deckMap (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods)) =
      freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck β
    (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods))
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
        A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
      (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (affineTorusMappingTorusDeckMeridian
            (orderThreeDescendedAffineTorusAutomorphism A.periods)))) =
    MulOpposite.op
      (C.deckMap (affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods))) at hnat
  rw [hchart] at hnat
  let d := (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹
  have hfund :=
    A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β d
  have hop : MulOpposite.op
        (C.deckMap (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods))) =
      MulOpposite.op d⁻¹ :=
    hnat.symm.trans hfund
  apply MulOpposite.op_injective
  simpa only [d, inv_inv] using hop

/-- The two literal chart identities construct the requested exact comparison with no opaque
target-fibre choice. -/
public theorem OrderThreeCentralBoundaryBasedChartIdentities.toCoverComparison
    (h : A.OrderThreeCentralBoundaryBasedChartIdentities) :
    A.OrderThreeCentralBoundaryCoverComparison := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  change ∃ β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase,
      (∀ a : Lattice, _) ∧ _ at h
  obtain ⟨β, htranslation, hmeridian⟩ := h
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  have hdeck : C.deckMap = A.paperOrderThreeActualBoundaryToUniversalDeck :=
    A.paperOrderThreeActualBoundaryToUniversalDeck_unique C.deckMap
      (fun a ↦ A.orderThreeActualCentralCoverComparisonOfPath_deckMap_translation
        β a (htranslation a))
      (A.orderThreeActualCentralCoverComparisonOfPath_deckMap_meridian β hmeridian)
  refine ⟨C, hdeck, ?_⟩
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
