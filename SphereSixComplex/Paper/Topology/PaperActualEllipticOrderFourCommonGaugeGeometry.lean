module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourRelatorComparison
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry

/-!
# The invariant order-four common-gauge comparison

The two marked order-four generators must be compared with one common change of basepoint.
This module moves that comparison back through the marked central-to-core equivalence.  The
result is an equality of diagonal conjugacy orbits of ordered pairs in the central fundamental
group.  It is independent of the connector used to transport the elliptic overlap into the core.

The marked physical meridian is used with its covering-space orientation, without inversion.
The paired lattice translation is `epsilon'`; the `-epsilon'` occurring in the analytic collar
formula is the affine lift convention and is not the marked deck translation in the relator.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The exact order-four overlap chart into the punctured central family. -/
public noncomputable def ellipticFourOverlapToCentral :
    C((A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace),
      A.CentralFamily) where
  toFun x := A.starToCentral 2 (A.orderFourCollarToActualOverlapHomeomorph.symm x)
  continuous_toFun :=
    (A.starToCentral_isOpenEmbedding 2).continuous.comp
      A.orderFourCollarToActualOverlapHomeomorph.symm.continuous

/-- The literal order-four overlap chart commutes with the inclusion into the actual core. -/
public theorem centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral
    (x : (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticFourOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour x := by
  apply Subtype.ext
  let q := A.orderFourCollarToActualOverlapHomeomorph.symm x
  calc
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticFourOverlapToCentral x)).1 =
        A.openEmbeddingStarData.collarSourceToGlued 2 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 2 q
    _ = x.1 := by
      change (A.orderFourCollarToActualOverlapHomeomorph q).1 = x.1
      exact congrArg Subtype.val
        (A.orderFourCollarToActualOverlapHomeomorph.apply_symm_apply x)

/-- The literal order-four overlap base viewed in the central family. -/
public noncomputable def ellipticFourOverlapCentralBase : A.CentralFamily :=
  A.ellipticFourOverlapToCentral
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩

/-- The central-family homeomorphism, followed by the order-four connector, gives an
equivalence from the literal central overlap base to the van Kampen core base. -/
public noncomputable def ellipticFourCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.ellipticFourOverlapCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (A.centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticFourConnector
        A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1).symm)

/-- The literal central chart followed by the geometric central-to-core equivalence is exactly
the actual overlap inclusion with its prescribed order-four connector. -/
public theorem ellipticFourOverlapToCore_eq_central
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) :
    A.ellipticFourOverlapToCore gamma =
      A.ellipticFourCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl gamma) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.ellipticFourOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticFour := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.ellipticFourOverlapCentralBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticFour
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral _
  have hcompbase := congrArg
    (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦
        k ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) hmap
  have hinner : ∀ delta,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph hcentral)
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl delta) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ delta := by
    intro delta
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl delta) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.ellipticFourOverlapToCentral)
          hcompbase delta :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ rfl hcentral delta
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour) rfl delta :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl delta
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ delta := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ := by
    ext delta
    exact hinner delta
  simp only [ellipticFourOverlapToCore, ellipticFourCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- The central-family point under the chosen lift of the order-four overlap base. -/
public noncomputable def ellipticFourCentralBase : A.CentralFamily :=
  A.ellipticFourOverlapToCentral
    (A.ellipticFourBoundaryProjection
      A.ellipticFourBoundaryBase)

/-- A lift of the order-four overlap base to the selected global affine universal cover. -/
public noncomputable def orderFourCentralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose
    (D.data.quotientCovering.surjective A.ellipticFourCentralBase)

public theorem orderFourCentralAffineUniversalCoverPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.orderFourCentralAffineUniversalCoverPoint =
      A.ellipticFourCentralBase := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective A.ellipticFourCentralBase)

/-- The canonical comparison from the explicit radial overlap cover to the selected global
affine universal cover.  Its lift and deck homomorphism are derived from the literal overlap
chart by the covering-space lifting property. -/
public noncomputable def ellipticFourCentralCoverComparison :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData
      (G := OrderFourAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.ellipticFourBoundaryProjection D.data.projection := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    D.data.quotientCovering A.ellipticFourOverlapToCentral
    A.ellipticFourBoundaryBase
    A.orderFourCentralAffineUniversalCoverPoint
    A.orderFourCentralAffineUniversalCoverPoint_projects

/-- The induced comparison computes the image of every physical deck loop in the central
universal cover. -/
public theorem ellipticFourCentralCoverComparison_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.ellipticFourCentralCoverComparison
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨C.lift A.ellipticFourBoundaryBase, rfl⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.ellipticFourBoundaryBase)
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  simpa using
    (QuotientCoverMapData.fundamentalGroupEquiv_natural
      A.ellipticFourBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.ellipticFourBoundaryBase
      (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase g)).symm

/-- A common path from the displayed affine base to the order-four overlap base in the central
family. -/
public noncomputable def orderFourCentralBaseWhisker :
    Path A.centralAffineBase A.ellipticFourCentralBase := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  exact PathConnectedSpace.somePath _ _

/-- The central marked meridian transported to the order-four overlap base. -/
public noncomputable def orderFourCentralMeridianAtOverlap :
    FundamentalGroup A.CentralFamily A.ellipticFourCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
    A.centralAffineCorePiOneData.rhoTwo

/-- The central marked twist translation transported along the same path. -/
public noncomputable def orderFourCentralTranslationAtOverlap :
    FundamentalGroup A.CentralFamily A.ellipticFourCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
    (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

/-- The exact local loop statement behind the deck comparison.  The literal collar chart sends
the two physical deck loops to the two marked central loops up to one common change of basepoint.
Unlike the final core statement, this involves neither the van Kampen connector nor the cusp
marking correction. -/
public def OrderFourCentralMarkedLoopCompatibility : Prop :=
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon'))))

/-- The remaining local geometric computation for the order-four collar.  It says that the
lift-induced images of the two physical generators and the two marked central loops differ by
one deck transformation.  The simultaneous conjugacy is necessary: both the lift above the
overlap base and the path from the displayed central base are chosen independently. -/
public def OrderFourCentralCoverDeckCompatibility : Prop :=
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  SimultaneouslyConjugate
    (MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.ellipticFourBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.ellipticFourBoundaryBase)
            A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.ellipticFourBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.ellipticFourBoundaryBase)
            A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.ellipticFourBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.ellipticFourBoundaryDeckData.translation epsilon')))

/-- The local loop comparison implies the deck-group comparison by quotient-cover monodromy. -/
public theorem OrderFourCentralMarkedLoopCompatibility.toDeckCompatibility
    (H : A.OrderFourCentralMarkedLoopCompatibility) :
    A.OrderFourCentralCoverDeckCompatibility := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.ellipticFourBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon')))) at H
  have h := H.map E.toMonoidHom
  change SimultaneouslyConjugate
    (E (fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralMeridianAtOverlap),
      E (fundamentalGroupElementOfBaseEq
        (C.commutes A.ellipticFourBoundaryBase)
        A.orderFourCentralTranslationAtOverlap))
    (E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian)),
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon'))))) at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.ellipticFourBoundaryDeckData.meridian) := by
    exact A.ellipticFourCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon')))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon'))) := by
    exact A.ellipticFourCentralCoverComparison_ofDeck _
  rw [hmeridian, htranslation] at h
  have h := h.unop
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.ellipticFourBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.ellipticFourBoundaryDeckData.translation epsilon')))
  simpa only [MulOpposite.unop_op] using h

/-- Conversely, the deck comparison contains exactly the local marked-loop statement. -/
public theorem OrderFourCentralCoverDeckCompatibility.toMarkedLoopCompatibility
    (H : A.OrderFourCentralCoverDeckCompatibility) :
    A.OrderFourCentralMarkedLoopCompatibility := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.ellipticFourBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.ellipticFourBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.ellipticFourBoundaryDeckData.translation epsilon'))) at H
  have h := H.op
  simp only [MulOpposite.op_unop] at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.ellipticFourBoundaryDeckData.meridian) := by
    exact A.ellipticFourCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.ellipticFourBoundaryBase)
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon')))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon'))) := by
    exact A.ellipticFourCentralCoverComparison_ofDeck _
  rw [← hmeridian, ← htranslation] at h
  have hlocal :=
    (simultaneouslyConjugate_map_equiv_iff E
      (fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralMeridianAtOverlap,
        fundamentalGroupElementOfBaseEq
          (C.commutes A.ellipticFourBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)
      (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.ellipticFourBoundaryBase)
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase
            A.ellipticFourBoundaryDeckData.meridian),
        FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.ellipticFourBoundaryBase)
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase
            (Additive.toMul
              (A.ellipticFourBoundaryDeckData.translation epsilon'))))).mp h
  exact hlocal

public theorem orderFourCentralMarkedLoopCompatibility_iff_deckCompatibility :
    A.OrderFourCentralMarkedLoopCompatibility ↔
      A.OrderFourCentralCoverDeckCompatibility :=
  ⟨fun h ↦ h.toDeckCompatibility A, fun h ↦ h.toMarkedLoopCompatibility A⟩

/-- The central order-four meridian and twist translation, before applying the chosen
central-to-core marking. -/
public noncomputable def orderFourCentralMarkedPair
    (_N : A.CuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (A.centralAffineCorePiOneData.rhoTwo,
    Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

/-- The physical order-four deck meridian and twist translation, pulled back from the core
through the same central marking. -/
public noncomputable def orderFourPhysicalMarkedPairInCentral
    (N : A.CuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (N.centralToCore.symm A.ellipticFourPhysicalMeridianToCore,
    N.centralToCore.symm
      (Additive.toMul (A.ellipticFourPhysicalTranslationToCore epsilon')))

/-- The connector-invariant geometric residual: the two ordered peripheral pairs lie in the
same diagonal inner-conjugacy orbit in the central fundamental group. -/
public def OrderFourCentralPairOrbitComparison
    (N : A.CuspCentralNaturality) : Prop :=
  SimultaneouslyConjugate
    (A.orderFourCentralMarkedPair N)
    (A.orderFourPhysicalMarkedPairInCentral N)

/-- The connector-invariant central comparison gives the common gauge required by the relator
calculation. -/
public theorem OrderFourCentralPairOrbitComparison.toCommonGaugeComparison
    {N : A.CuspCentralNaturality}
    (h : A.OrderFourCentralPairOrbitComparison N) :
    A.OrderFourCommonGaugeComparison N := by
  obtain ⟨c, hmeridian, htranslation⟩ := h
  refine ⟨N.centralToCore c, ?_, ?_⟩
  · simpa only [orderFourCentralMarkedPair, orderFourPhysicalMarkedPairInCentral,
      MulEquiv.apply_symm_apply, map_mul, map_inv] using
      congrArg N.centralToCore hmeridian
  · change N.centralToCore
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon')) = _
    simpa only [orderFourCentralMarkedPair, orderFourPhysicalMarkedPairInCentral,
      MulEquiv.apply_symm_apply, map_mul, map_inv] using
      congrArg N.centralToCore htranslation

/-- Conversely, every core common gauge pulls back to the invariant central pair comparison.
Thus the orbit statement is the exact connector-independent content still missing from the
geometric construction. -/
public theorem OrderFourCommonGaugeComparison.toCentralPairOrbitComparison
    {N : A.CuspCentralNaturality}
    (h : A.OrderFourCommonGaugeComparison N) :
    A.OrderFourCentralPairOrbitComparison N := by
  obtain ⟨c, hmeridian, htranslation⟩ := h
  refine ⟨N.centralToCore.symm c, ?_, ?_⟩
  · simpa only [orderFourCentralMarkedPair, orderFourPhysicalMarkedPairInCentral,
      MulEquiv.symm_apply_apply, map_mul, map_inv] using
      congrArg N.centralToCore.symm hmeridian
  · change N.centralToCore
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon')) = _ at htranslation
    simpa only [orderFourCentralMarkedPair, orderFourPhysicalMarkedPairInCentral,
      MulEquiv.symm_apply_apply, map_mul, map_inv] using
      congrArg N.centralToCore.symm htranslation

public theorem orderFourCentralPairOrbitComparison_iff_commonGaugeComparison
    (N : A.CuspCentralNaturality) :
    A.OrderFourCentralPairOrbitComparison N ↔ A.OrderFourCommonGaugeComparison N := by
  exact ⟨fun h ↦ OrderFourCentralPairOrbitComparison.toCommonGaugeComparison A h,
    fun h ↦ OrderFourCommonGaugeComparison.toCentralPairOrbitComparison A h⟩

/-- An exact based identification of the two central pairs is sufficient; the orbit comparison
then uses the identity gauge. -/
public theorem orderFourCentralPairOrbitComparison_of_eq
    (N : A.CuspCentralNaturality)
    (h : A.orderFourCentralMarkedPair N = A.orderFourPhysicalMarkedPairInCentral N) :
    A.OrderFourCentralPairOrbitComparison N := by
  unfold OrderFourCentralPairOrbitComparison
  rw [h]
  exact simultaneouslyConjugate_refl _

end SphereSixComplex.Geometry.PaperAnalyticData

end
