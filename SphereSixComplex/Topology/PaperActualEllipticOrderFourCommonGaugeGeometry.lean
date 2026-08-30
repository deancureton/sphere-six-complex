module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourRelatorComparison
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry

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
public noncomputable def orderFourActualOverlapToCentral :
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
        (A.orderFourActualOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour x := by
  apply Subtype.ext
  let q := A.orderFourCollarToActualOverlapHomeomorph.symm x
  calc
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.orderFourActualOverlapToCentral x)).1 =
        A.openEmbeddingStarData.collarSourceToGlued 2 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 2 q
    _ = x.1 := by
      change (A.orderFourCollarToActualOverlapHomeomorph q).1 = x.1
      exact congrArg Subtype.val
        (A.orderFourCollarToActualOverlapHomeomorph.apply_symm_apply x)

/-- The literal order-four overlap base viewed in the central family. -/
public noncomputable def orderFourActualOverlapCentralBase : A.CentralFamily :=
  A.orderFourActualOverlapToCentral
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩

/-- The central-family homeomorphism, followed by the order-four connector, gives an
equivalence from the literal central overlap base to the van Kampen core base. -/
public noncomputable def orderFourActualCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.orderFourActualOverlapCentralBase ≃*
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
public theorem actualEllipticFourOverlapToCore_eq_central
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) :
    A.actualEllipticFourOverlapToCore gamma =
      A.orderFourActualCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl gamma) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.orderFourActualOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticFour := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.orderFourActualOverlapCentralBase =
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
          (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl delta) =
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
          (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl delta) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.orderFourActualOverlapToCentral)
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
          (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ := by
    ext delta
    exact hinner delta
  simp only [actualEllipticFourOverlapToCore, orderFourActualCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- The central-family point under the chosen lift of the order-four overlap base. -/
public noncomputable def orderFourActualEllipticCentralBase : A.CentralFamily :=
  A.orderFourActualOverlapToCentral
    (A.orderFourActualEllipticBoundaryProjection
      A.orderFourActualEllipticBoundaryBase)

/-- A lift of the order-four overlap base to the selected global affine universal cover. -/
public noncomputable def orderFourCentralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose
    (D.data.quotientCovering.surjective A.orderFourActualEllipticCentralBase)

public theorem orderFourCentralAffineUniversalCoverPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.orderFourCentralAffineUniversalCoverPoint =
      A.orderFourActualEllipticCentralBase := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective A.orderFourActualEllipticCentralBase)

/-- The canonical comparison from the explicit radial overlap cover to the selected global
affine universal cover.  Its lift and deck homomorphism are derived from the literal overlap
chart by the covering-space lifting property. -/
public noncomputable def orderFourActualCentralCoverComparison :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData
      (G := OrderFourAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.orderFourActualEllipticBoundaryProjection D.data.projection := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
    D.data.quotientCovering A.orderFourActualOverlapToCentral
    A.orderFourActualEllipticBoundaryBase
    A.orderFourCentralAffineUniversalCoverPoint
    A.orderFourCentralAffineUniversalCoverPoint_projects

/-- The induced comparison computes the image of every physical deck loop in the central
universal cover. -/
public theorem orderFourActualCentralCoverComparison_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.orderFourActualCentralCoverComparison
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality
      A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.orderFourActualEllipticBoundaryBase
      (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase g)).symm

/-- A common path from the displayed affine base to the order-four overlap base in the central
family. -/
public noncomputable def orderFourCentralBaseWhisker :
    Path A.centralAffineBase A.orderFourActualEllipticCentralBase := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  exact PathConnectedSpace.somePath _ _

/-- The central marked meridian transported to the order-four overlap base. -/
public noncomputable def orderFourCentralMeridianAtOverlap :
    FundamentalGroup A.CentralFamily A.orderFourActualEllipticCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
    A.centralAffineCorePiOneData.rhoTwo

/-- The central marked twist translation transported along the same path. -/
public noncomputable def orderFourCentralTranslationAtOverlap :
    FundamentalGroup A.CentralFamily A.orderFourActualEllipticCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
    (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

/-- The exact local loop statement behind the deck comparison.  The literal collar chart sends
the two physical deck loops to the two marked central loops up to one common change of basepoint.
Unlike the final core statement, this involves neither the van Kampen connector nor the cusp
marking correction. -/
public def OrderFourCentralMarkedLoopCompatibility : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))

/-- The remaining local geometric computation for the order-four collar.  It says that the
lift-induced images of the two physical generators and the two marked central loops differ by
one deck transformation.  The simultaneous conjugacy is necessary: both the lift above the
overlap base and the path from the displayed central base are chosen independently. -/
public def OrderFourCentralCoverDeckCompatibility : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  SimultaneouslyConjugate
    (MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.orderFourActualEllipticBoundaryBase)
            A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (D.data.quotientCovering.fundamentalGroupEquiv
          ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
          (fundamentalGroupElementOfBaseEq
            (C.commutes A.orderFourActualEllipticBoundaryBase)
            A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))

/-- The local loop comparison implies the deck-group comparison by quotient-cover monodromy. -/
public theorem OrderFourCentralMarkedLoopCompatibility.toDeckCompatibility
    (H : A.OrderFourCentralMarkedLoopCompatibility) :
    A.OrderFourCentralCoverDeckCompatibility := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))) at H
  have h := H.map E.toMonoidHom
  change SimultaneouslyConjugate
    (E (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralMeridianAtOverlap),
      E (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralTranslationAtOverlap))
    (E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian)),
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))) at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian) := by
    exact A.orderFourActualCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))) := by
    exact A.orderFourActualCentralCoverComparison_ofDeck _
  rw [hmeridian, htranslation] at h
  have h := h.unop
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))
  simpa only [MulOpposite.unop_op] using h

/-- Conversely, the deck comparison contains exactly the local marked-loop statement. -/
public theorem OrderFourCentralCoverDeckCompatibility.toMarkedLoopCompatibility
    (H : A.OrderFourCentralCoverDeckCompatibility) :
    A.OrderFourCentralMarkedLoopCompatibility := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.orderFourActualEllipticBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)))
    (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))) at H
  have h := H.op
  simp only [MulOpposite.op_unop] at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.orderFourActualEllipticBoundaryDeckData.meridian) := by
    exact A.orderFourActualCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))) := by
    exact A.orderFourActualCentralCoverComparison_ofDeck _
  rw [← hmeridian, ← htranslation] at h
  have hlocal :=
    (simultaneouslyConjugate_map_equiv_iff E
      (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralMeridianAtOverlap,
        fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralTranslationAtOverlap)
      (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase
            A.orderFourActualEllipticBoundaryDeckData.meridian),
        FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase
            (Additive.toMul
              (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))).mp h
  exact hlocal

public theorem orderFourCentralMarkedLoopCompatibility_iff_deckCompatibility :
    A.OrderFourCentralMarkedLoopCompatibility ↔
      A.OrderFourCentralCoverDeckCompatibility :=
  ⟨fun h ↦ h.toDeckCompatibility A, fun h ↦ h.toMarkedLoopCompatibility A⟩

/-- The central order-four meridian and twist translation, before applying the chosen
central-to-core marking. -/
public noncomputable def orderFourCentralMarkedPair
    (_N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (A.centralAffineCorePiOneData.rhoTwo,
    Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

/-- The physical order-four deck meridian and twist translation, pulled back from the core
through the same central marking. -/
public noncomputable def orderFourPhysicalMarkedPairInCentral
    (N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (N.centralToCore.symm A.orderFourActualEllipticPhysicalMeridianToCore,
    N.centralToCore.symm
      (Additive.toMul (A.orderFourActualEllipticPhysicalTranslationToCore epsilon')))

/-- The connector-invariant geometric residual: the two ordered peripheral pairs lie in the
same diagonal inner-conjugacy orbit in the central fundamental group. -/
public def OrderFourCentralPairOrbitComparison
    (N : A.ActualCuspCentralNaturality) : Prop :=
  SimultaneouslyConjugate
    (A.orderFourCentralMarkedPair N)
    (A.orderFourPhysicalMarkedPairInCentral N)

/-- The connector-invariant central comparison gives the common gauge required by the relator
calculation. -/
public theorem OrderFourCentralPairOrbitComparison.toCommonGaugeComparison
    {N : A.ActualCuspCentralNaturality}
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
    {N : A.ActualCuspCentralNaturality}
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
    (N : A.ActualCuspCentralNaturality) :
    A.OrderFourCentralPairOrbitComparison N ↔ A.OrderFourCommonGaugeComparison N := by
  exact ⟨fun h ↦ OrderFourCentralPairOrbitComparison.toCommonGaugeComparison A h,
    fun h ↦ OrderFourCommonGaugeComparison.toCentralPairOrbitComparison A h⟩

/-- An exact based identification of the two central pairs is sufficient; the orbit comparison
then uses the identity gauge. -/
public theorem orderFourCentralPairOrbitComparison_of_eq
    (N : A.ActualCuspCentralNaturality)
    (h : A.orderFourCentralMarkedPair N = A.orderFourPhysicalMarkedPairInCentral N) :
    A.OrderFourCentralPairOrbitComparison N := by
  unfold OrderFourCentralPairOrbitComparison
  rw [h]
  exact simultaneouslyConjugate_refl _

end SphereSixComplex.Geometry.PaperAnalyticData

end
