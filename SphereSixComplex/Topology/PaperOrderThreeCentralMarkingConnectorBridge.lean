module

public import SphereSixComplex.Topology.FundamentalGroupConnectorConjugacy
public import SphereSixComplex.Topology.PaperOrderThreeExplicitBasedBoundaryCoverComparison
public import SphereSixComplex.Topology.PaperActualEllipticOrderFourCommonGaugeGeometry

/-!
# Based marking and connector gauge for the order-three affine cover

The deck labels of a pair of loops are computed first at the lift represented by one common
path.  Changing from that lift to the lift selected by the collar comparison changes both labels
by one simultaneous conjugation.  Thus the remaining geometric input consists only of two loop
identities along the same existentially chosen path.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

/-- Simultaneously transporting a fibre point and a fundamental-group element across a basepoint
equality does not change its quotient-cover deck label. -/
public theorem quotientCoverFundamentalGroupEquiv_of_base_eq
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E]
    {x y : X} (h : x = y) (e : p ⁻¹' {x}) (a : FundamentalGroup X x) :
    hp.fundamentalGroupEquiv ⟨e.1, e.2.trans h⟩
        (fundamentalGroupElementOfBaseEq h a) =
      hp.fundamentalGroupEquiv e a := by
  subst y
  rfl

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The two central marked loops are represented by the canonical affine presentation after
transport along one common path to the order-three overlap base. -/
public def OrderThreeCentralAffineBasedMarkingCoherence : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  letI := D.topology
  letI := D.action
  let C := A.orderThreeActualCentralCoverComparison
  ∃ β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase,
    fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralMeridianAtOverlap =
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian))) ∧
    fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralTranslationAtOverlap =
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))))

/-- A based affine marking computes the canonical collar lift's two deck labels up to one
common conjugator. -/
public theorem OrderThreeCentralAffineBasedMarkingCoherence.toUniversalDeckCompatibility
    (h : A.OrderThreeCentralAffineBasedMarkingCoherence) :
    A.OrderThreeCentralUniversalDeckMarkingCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  change ∃ β : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase,
      _ ∧ _ at h
  obtain ⟨β, hmeridian, htranslation⟩ := h
  let m : FundamentalGroup A.CentralFamily A.orderThreeActualEllipticCentralBase :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath β
      (paperPuncturedGlobalFamilyAffinePresentation A
        (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian))
  let t : FundamentalGroup A.CentralFamily A.orderThreeActualEllipticCentralBase :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath β
      (paperPuncturedGlobalFamilyAffinePresentation A
        (Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon))))
  let hbase : A.orderThreeActualEllipticCentralBase =
      D.data.projection (C.lift A.orderThreeActualEllipticBoundaryBase) :=
    C.commutes A.orderThreeActualEllipticBoundaryBase
  let ePath : D.data.projection ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
      A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
  let eCollar : D.data.projection ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨C.lift A.orderThreeActualEllipticBoundaryBase, hbase.symm⟩
  let c := D.data.quotientCovering.fiberEquivGroup ePath eCollar
  have he : eCollar.1 = c • ePath.1 := by
    exact (D.data.quotientCovering.fiberEquivGroup_smul_self
      ePath (e' := eCollar)).symm
  have hchange := quotientCoverFundamentalGroupPair_simultaneouslyConjugate_of_smul
    D.data.quotientCovering ePath eCollar c he m t
  have hmeridianDeck :
      D.data.quotientCovering.fundamentalGroupEquiv ePath m =
        MulOpposite.op
          (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ := by
    exact A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β _
  have htranslationDeck :
      D.data.quotientCovering.fundamentalGroupEquiv ePath t =
        MulOpposite.op
          (Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))⁻¹ := by
    exact A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β _
  have hmeridianBase := quotientCoverFundamentalGroupEquiv_of_base_eq
    D.data.quotientCovering hbase eCollar m
  have htranslationBase := quotientCoverFundamentalGroupEquiv_of_base_eq
    D.data.quotientCovering hbase eCollar t
  have hmeridian' :
      fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralMeridianAtOverlap =
        fundamentalGroupElementOfBaseEq hbase m := by
    exact hmeridian
  have htranslation' :
      fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralTranslationAtOverlap =
        fundamentalGroupElementOfBaseEq hbase t := by
    exact htranslation
  have hmeridianBase' :
      MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase m)) =
        MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv eCollar m) := by
    exact congrArg MulOpposite.unop hmeridianBase
  have htranslationBase' :
      MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase t)) =
        MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv eCollar t) := by
    exact congrArg MulOpposite.unop htranslationBase
  have hleft : A.orderThreeCentralUniversalDeckMarkedPair =
      (MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv eCollar m),
        MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv eCollar t)) := by
    apply Prod.ext
    · change MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderThreeCentralMeridianAtOverlap)) = _
      rw [hmeridian']
      exact hmeridianBase'
    · change MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderThreeCentralTranslationAtOverlap)) = _
      rw [htranslation']
      exact htranslationBase'
  rw [hmeridianDeck, htranslationDeck] at hchange
  change SimultaneouslyConjugate A.orderThreeCentralUniversalDeckMarkedPair
    ((freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹,
      Additive.toMul (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon))
  rw [hleft]
  simpa only [MulOpposite.unop_op, map_neg, toMul_neg, inv_inv] using hchange

/-- The point-set comparison and the based marking coherence give the local order-three deck
comparison used by the common-gauge reduction. -/
public theorem OrderThreeCentralAffineBasedMarkingCoherence.toDeckCompatibility
    (h : A.OrderThreeCentralAffineBasedMarkingCoherence)
    (hcover : A.OrderThreeCentralBoundaryCoverComparison) :
    A.OrderThreeCentralCoverDeckCompatibility :=
  hcover.toDeckCompatibility A (h.toUniversalDeckCompatibility A)

/-- The same hypotheses give the equivalent local marked-loop comparison. -/
public theorem OrderThreeCentralAffineBasedMarkingCoherence.toMarkedLoopCompatibility
    (h : A.OrderThreeCentralAffineBasedMarkingCoherence)
    (hcover : A.OrderThreeCentralBoundaryCoverComparison) :
    A.OrderThreeCentralMarkedLoopCompatibility :=
  (h.toDeckCompatibility A hcover).toMarkedLoopCompatibility A

/-- The narrow order-four analogue of the based marking calculation.  It asks for one path and
one lift at which the two transported central generators have the physical deck labels. -/
public def OrderFourCentralAffineBasedDeckMarkingCoherence : Prop :=
  letI := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  letI := D.topology
  letI := D.action
  letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  ∃ β : Path A.centralAffineBase A.orderFourActualEllipticCentralBase,
    ∃ e : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase},
      MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv e
            (FundamentalGroup.fundamentalGroupMulEquivOfPath β
              A.centralAffineCorePiOneData.rhoTwo)) =
        C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian ∧
      MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv e
            (FundamentalGroup.fundamentalGroupMulEquivOfPath β
              (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon')))) =
        C.deckMap
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))

/-- The existential order-four based marking calculation implies the connector-invariant deck
comparison, independently of the arbitrary path used in the production definition. -/
public theorem OrderFourCentralAffineBasedDeckMarkingCoherence.toDeckCompatibility
    (h : A.OrderFourCentralAffineBasedDeckMarkingCoherence) :
    A.OrderFourCentralCoverDeckCompatibility := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  change ∃ β : Path A.centralAffineBase A.orderFourActualEllipticCentralBase,
      ∃ e : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase}, _ ∧ _ at h
  obtain ⟨β, e, hmeridian, htranslation⟩ := h
  let m : FundamentalGroup A.CentralFamily A.orderFourActualEllipticCentralBase :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath β
      A.centralAffineCorePiOneData.rhoTwo
  let t : FundamentalGroup A.CentralFamily A.orderFourActualEllipticCentralBase :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath β
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))
  let hbase : A.orderFourActualEllipticCentralBase =
      D.data.projection (C.lift A.orderFourActualEllipticBoundaryBase) :=
    C.commutes A.orderFourActualEllipticBoundaryBase
  let eCollar : D.data.projection ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨C.lift A.orderFourActualEllipticBoundaryBase, hbase.symm⟩
  let c := D.data.quotientCovering.fiberEquivGroup e eCollar
  have he : eCollar.1 = c • e.1 := by
    exact (D.data.quotientCovering.fiberEquivGroup_smul_self e (e' := eCollar)).symm
  have hlift := quotientCoverFundamentalGroupPair_simultaneouslyConjugate_of_smul
    D.data.quotientCovering e eCollar c he m t
  have hpath := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    A.orderFourCentralBaseWhisker β A.centralAffineCorePiOneData.rhoTwo
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))
  have hpathDeck :=
    (hpath.map
      (D.data.quotientCovering.fundamentalGroupEquiv eCollar).toMonoidHom).unop
  have hcombined := hpathDeck.trans hlift
  have hmeridian' :
      MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv e m) =
        C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian := by
    exact hmeridian
  have htranslation' :
      MulOpposite.unop (D.data.quotientCovering.fundamentalGroupEquiv e t) =
        C.deckMap
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')) := by
    exact htranslation
  rw [hmeridian', htranslation'] at hcombined
  have hmeridianBase := quotientCoverFundamentalGroupEquiv_of_base_eq
    D.data.quotientCovering hbase eCollar A.orderFourCentralMeridianAtOverlap
  have htranslationBase := quotientCoverFundamentalGroupEquiv_of_base_eq
    D.data.quotientCovering hbase eCollar A.orderFourCentralTranslationAtOverlap
  have hleft :
      (MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderFourCentralMeridianAtOverlap)),
        MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderFourCentralTranslationAtOverlap))) =
      (MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv eCollar
            A.orderFourCentralMeridianAtOverlap),
        MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv eCollar
            A.orderFourCentralTranslationAtOverlap)) := by
    apply Prod.ext
    · exact congrArg MulOpposite.unop hmeridianBase
    · exact congrArg MulOpposite.unop htranslationBase
  have hresult : SimultaneouslyConjugate
      (MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderFourCentralMeridianAtOverlap)),
        MulOpposite.unop
          (D.data.quotientCovering.fundamentalGroupEquiv
            ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
            (fundamentalGroupElementOfBaseEq hbase
              A.orderFourCentralTranslationAtOverlap)))
      (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian,
        C.deckMap
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))) := by
    rw [hleft]
    exact hcombined
  exact hresult

/-- Hence the same order-four based input also gives the equivalent local loop comparison. -/
public theorem OrderFourCentralAffineBasedDeckMarkingCoherence.toMarkedLoopCompatibility
    (h : A.OrderFourCentralAffineBasedDeckMarkingCoherence) :
    A.OrderFourCentralMarkedLoopCompatibility :=
  (h.toDeckCompatibility A).toMarkedLoopCompatibility A

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
