module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeRelatorComparison
public import SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# The invariant order-three common-gauge comparison

The two marked order-three generators must be compared with one common change of basepoint.
This module moves that comparison back through the marked central-to-core equivalence.  The
result is an equality of diagonal conjugacy orbits of ordered pairs in the central fundamental
group.  It is independent of the connector used to transport the elliptic overlap into the core.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

/-- Two ordered pairs in a group differ by one common inner automorphism. -/
public def SimultaneouslyConjugate {G : Type*} [Group G]
    (left right : G × G) : Prop :=
  ∃ c : G, left.1 = c * right.1 * c⁻¹ ∧ left.2 = c * right.2 * c⁻¹

public theorem simultaneouslyConjugate_refl {G : Type*} [Group G] (p : G × G) :
    SimultaneouslyConjugate p p := by
  refine ⟨1, ?_, ?_⟩ <;> simp

/-- Simultaneous conjugacy is preserved by a group homomorphism. -/
public theorem SimultaneouslyConjugate.map
    {G H : Type*} [Group G] [Group H] {left right : G × G}
    (h : SimultaneouslyConjugate left right) (f : G →* H) :
    SimultaneouslyConjugate (f left.1, f left.2) (f right.1, f right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨f c, ?_, ?_⟩
  · simpa only [map_mul, map_inv] using congrArg f hfirst
  · simpa only [map_mul, map_inv] using congrArg f hsecond

/-- Passing from an opposite group back to the original group preserves simultaneous
conjugacy, with the inverse conjugator. -/
public theorem SimultaneouslyConjugate.unop
    {G : Type*} [Group G] {left right : Gᵐᵒᵖ × Gᵐᵒᵖ}
    (h : SimultaneouslyConjugate left right) :
    SimultaneouslyConjugate
      (MulOpposite.unop left.1, MulOpposite.unop left.2)
      (MulOpposite.unop right.1, MulOpposite.unop right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨(MulOpposite.unop c)⁻¹, ?_, ?_⟩
  · rw [mul_assoc]
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_inv, inv_inv] using
      congrArg MulOpposite.unop hfirst
  · rw [mul_assoc]
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_inv, inv_inv] using
      congrArg MulOpposite.unop hsecond

/-- Passing to the opposite group also preserves simultaneous conjugacy. -/
public theorem SimultaneouslyConjugate.op
    {G : Type*} [Group G] {left right : G × G}
    (h : SimultaneouslyConjugate left right) :
    SimultaneouslyConjugate
      (MulOpposite.op left.1, MulOpposite.op left.2)
      (MulOpposite.op right.1, MulOpposite.op right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨(MulOpposite.op c)⁻¹, ?_, ?_⟩
  · rw [mul_assoc]
    simpa only [MulOpposite.op_mul, MulOpposite.op_inv, inv_inv] using
      congrArg MulOpposite.op hfirst
  · rw [mul_assoc]
    simpa only [MulOpposite.op_mul, MulOpposite.op_inv, inv_inv] using
      congrArg MulOpposite.op hsecond

/-- A group equivalence reflects simultaneous conjugacy as well as preserving it. -/
public theorem simultaneouslyConjugate_map_equiv_iff
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (left right : G × G) :
    SimultaneouslyConjugate (e left.1, e left.2) (e right.1, e right.2) ↔
      SimultaneouslyConjugate left right := by
  constructor
  · intro h
    obtain ⟨c, hfirst, hsecond⟩ := h
    refine ⟨e.symm c, ?_, ?_⟩
    · apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using hfirst
    · apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using hsecond
  · intro h
    exact h.map e.toMonoidHom

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The exact order-three overlap chart into the punctured central family. -/
public noncomputable def orderThreeActualOverlapToCentral :
    C((A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace),
      A.CentralFamily) where
  toFun x := A.starToCentral 1 (A.orderThreeCollarToActualOverlapHomeomorph.symm x)
  continuous_toFun :=
    (A.starToCentral_isOpenEmbedding 1).continuous.comp
      A.orderThreeCollarToActualOverlapHomeomorph.symm.continuous

/-- The literal order-three overlap chart commutes with the inclusion into the actual core. -/
public theorem centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral
    (x : (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.orderThreeActualOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree x := by
  apply Subtype.ext
  let q := A.orderThreeCollarToActualOverlapHomeomorph.symm x
  calc
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.orderThreeActualOverlapToCentral x)).1 =
        A.openEmbeddingStarData.collarSourceToGlued 1 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 1 q
    _ = x.1 := by
      change (A.orderThreeCollarToActualOverlapHomeomorph q).1 = x.1
      exact congrArg Subtype.val
        (A.orderThreeCollarToActualOverlapHomeomorph.apply_symm_apply x)

/-- The literal order-three overlap base viewed in the central family. -/
public noncomputable def orderThreeActualOverlapCentralBase : A.CentralFamily :=
  A.orderThreeActualOverlapToCentral
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩

/-- The central-family homeomorphism, followed by the order-three connector, gives an
equivalence from the literal central overlap base to the van Kampen core base. -/
public noncomputable def orderThreeActualCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.orderThreeActualOverlapCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (A.centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticThreeConnector
        A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1).symm)

/-- The literal central chart followed by the geometric central-to-core equivalence is exactly
the actual overlap inclusion with its prescribed order-three connector. -/
public theorem actualEllipticThreeOverlapToCore_eq_central
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) :
    A.actualEllipticThreeOverlapToCore gamma =
      A.orderThreeActualCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl gamma) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.orderThreeActualOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticThree := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.orderThreeActualOverlapCentralBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticThree
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral _
  have hcompbase := congrArg
    (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦
        k ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) hmap
  have hinner : ∀ delta,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph hcentral)
          (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl delta) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ delta := by
    intro delta
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl delta) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.orderThreeActualOverlapToCentral)
          hcompbase delta :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ rfl hcentral delta
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree) rfl delta :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl delta
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ delta := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ := by
    ext delta
    exact hinner delta
  simp only [actualEllipticThreeOverlapToCore, orderThreeActualCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- The central-family point under the chosen lift of the order-three overlap base. -/
public noncomputable def orderThreeActualEllipticCentralBase : A.CentralFamily :=
  A.orderThreeActualOverlapToCentral
    (A.orderThreeActualEllipticBoundaryProjection
      A.orderThreeActualEllipticBoundaryBase)

/-- A lift of the order-three overlap base to the selected global affine universal cover. -/
public noncomputable def orderThreeCentralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose
    (D.data.quotientCovering.surjective A.orderThreeActualEllipticCentralBase)

public theorem orderThreeCentralAffineUniversalCoverPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.orderThreeCentralAffineUniversalCoverPoint =
      A.orderThreeActualEllipticCentralBase := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective A.orderThreeActualEllipticCentralBase)

/-- The canonical comparison from the explicit radial overlap cover to the selected global
affine universal cover.  Its lift and deck homomorphism are derived from the literal overlap
chart by the covering-space lifting property. -/
public noncomputable def orderThreeActualCentralCoverComparison :
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
    A.orderThreeCentralAffineUniversalCoverPoint
    A.orderThreeCentralAffineUniversalCoverPoint_projects

/-- The induced comparison computes the image of every physical deck loop in the central
universal cover. -/
public theorem orderThreeActualCentralCoverComparison_ofDeck
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.orderThreeActualCentralCoverComparison
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
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
  let C := A.orderThreeActualCentralCoverComparison
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality
      A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.orderThreeActualEllipticBoundaryBase
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase g)).symm

/-- A common path from the displayed affine base to the order-three overlap base in the central
family. -/
public noncomputable def orderThreeCentralBaseWhisker :
    Path A.centralAffineBase A.orderThreeActualEllipticCentralBase := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  exact PathConnectedSpace.somePath _ _

/-- The central marked meridian transported to the order-three overlap base. -/
public noncomputable def orderThreeCentralMeridianAtOverlap :
    FundamentalGroup A.CentralFamily A.orderThreeActualEllipticCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderThreeCentralBaseWhisker
    A.centralAffineCorePiOneData.rhoOne

/-- The central marked twist translation transported along the same path. -/
public noncomputable def orderThreeCentralTranslationAtOverlap :
    FundamentalGroup A.CentralFamily A.orderThreeActualEllipticCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderThreeCentralBaseWhisker
    (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))

/-- The exact local loop statement behind the deck comparison.  The literal collar chart sends
the two physical deck loops to the two marked central loops up to one common change of basepoint.
Unlike the final core statement, this involves neither the van Kampen connector nor the cusp
marking correction. -/
public def OrderThreeCentralMarkedLoopCompatibility : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))

/-- The remaining local geometric computation for the order-three collar.  It says that the
lift-induced images of the two physical generators and the two marked central loops differ by
one deck transformation.  The simultaneous conjugacy is necessary: both the lift above the
overlap base and the path from the displayed central base are chosen independently. -/
public def OrderThreeCentralCoverDeckCompatibility : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  SimultaneouslyConjugate
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
    (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))

/-- The local loop comparison implies the deck-group comparison by quotient-cover monodromy. -/
public theorem OrderThreeCentralMarkedLoopCompatibility.toDeckCompatibility
    (H : A.OrderThreeCentralMarkedLoopCompatibility) :
    A.OrderThreeCentralCoverDeckCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) at H
  have h := H.map E.toMonoidHom
  change SimultaneouslyConjugate
    (E (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralMeridianAtOverlap),
      E (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralTranslationAtOverlap))
    (E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian)),
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))) at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian) := by
    exact A.orderThreeActualCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) := by
    exact A.orderThreeActualCentralCoverComparison_ofDeck _
  rw [hmeridian, htranslation] at h
  have h := h.unop
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralTranslationAtOverlap)))
    (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
  simpa only [MulOpposite.unop_op] using h

/-- Conversely, the deck comparison contains exactly the local marked-loop statement. -/
public theorem OrderThreeCentralCoverDeckCompatibility.toMarkedLoopCompatibility
    (H : A.OrderThreeCentralCoverDeckCompatibility) :
    A.OrderThreeCentralMarkedLoopCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨C.lift A.orderThreeActualEllipticBoundaryBase, rfl⟩
  change SimultaneouslyConjugate
    (MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralMeridianAtOverlap)),
      MulOpposite.unop
        (E (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralTranslationAtOverlap)))
    (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian,
      C.deckMap
        (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) at H
  have h := H.op
  simp only [MulOpposite.op_unop] at h
  have hmeridian :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
        MulOpposite.op
          (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian) := by
    exact A.orderThreeActualCentralCoverComparison_ofDeck _
  have htranslation :
      E (FundamentalGroup.mapOfEq C.baseMap
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
        MulOpposite.op
          (C.deckMap (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) := by
    exact A.orderThreeActualCentralCoverComparison_ofDeck _
  rw [← hmeridian, ← htranslation] at h
  have hlocal :=
    (simultaneouslyConjugate_map_equiv_iff E
      (fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralMeridianAtOverlap,
        fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralTranslationAtOverlap)
      (FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            A.orderThreeActualEllipticBoundaryDeckData.meridian),
        FundamentalGroup.mapOfEq C.baseMap
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))).mp h
  exact hlocal

public theorem orderThreeCentralMarkedLoopCompatibility_iff_deckCompatibility :
    A.OrderThreeCentralMarkedLoopCompatibility ↔
      A.OrderThreeCentralCoverDeckCompatibility :=
  ⟨fun h ↦ h.toDeckCompatibility A, fun h ↦ h.toMarkedLoopCompatibility A⟩

/-- The central order-three meridian and twist translation, before applying the chosen
central-to-core marking. -/
public noncomputable def orderThreeCentralMarkedPair
    (_N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (A.centralAffineCorePiOneData.rhoOne,
    Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))

/-- The physical order-three deck meridian and twist translation, pulled back from the core
through the same central marking. -/
public noncomputable def orderThreePhysicalMarkedPairInCentral
    (N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.CentralFamily A.centralAffineBase ×
      FundamentalGroup A.CentralFamily A.centralAffineBase :=
  (N.centralToCore.symm A.orderThreeActualEllipticPhysicalMeridianToCore,
    N.centralToCore.symm
      (Additive.toMul (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon))))

/-- The connector-invariant geometric residual: the two ordered peripheral pairs lie in the
same diagonal inner-conjugacy orbit in the central fundamental group. -/
public def OrderThreeCentralPairOrbitComparison
    (N : A.ActualCuspCentralNaturality) : Prop :=
  SimultaneouslyConjugate
    (A.orderThreeCentralMarkedPair N)
    (A.orderThreePhysicalMarkedPairInCentral N)

/-- The connector-invariant central comparison gives the common gauge required by the relator
calculation. -/
public theorem OrderThreeCentralPairOrbitComparison.toCommonGaugeComparison
    {N : A.ActualCuspCentralNaturality}
    (h : A.OrderThreeCentralPairOrbitComparison N) :
    A.OrderThreeCommonGaugeComparison N := by
  obtain ⟨c, hmeridian, htranslation⟩ := h
  refine ⟨N.centralToCore c, ?_, ?_⟩
  · simpa only [orderThreeCentralMarkedPair, orderThreePhysicalMarkedPairInCentral,
      MulEquiv.apply_symm_apply, map_mul, map_inv] using
      congrArg N.centralToCore hmeridian
  · change N.centralToCore
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) = _
    simpa only [orderThreeCentralMarkedPair, orderThreePhysicalMarkedPairInCentral,
      MulEquiv.apply_symm_apply, map_mul, map_inv] using
      congrArg N.centralToCore htranslation

/-- Conversely, every core common gauge pulls back to the invariant central pair comparison.
Thus the orbit statement is the exact connector-independent content still missing from the
geometric construction. -/
public theorem OrderThreeCommonGaugeComparison.toCentralPairOrbitComparison
    {N : A.ActualCuspCentralNaturality}
    (h : A.OrderThreeCommonGaugeComparison N) :
    A.OrderThreeCentralPairOrbitComparison N := by
  obtain ⟨c, hmeridian, htranslation⟩ := h
  refine ⟨N.centralToCore.symm c, ?_, ?_⟩
  · simpa only [orderThreeCentralMarkedPair, orderThreePhysicalMarkedPairInCentral,
      MulEquiv.symm_apply_apply, map_mul, map_inv] using
      congrArg N.centralToCore.symm hmeridian
  · change N.centralToCore
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) = _ at htranslation
    simpa only [orderThreeCentralMarkedPair, orderThreePhysicalMarkedPairInCentral,
      MulEquiv.symm_apply_apply, map_mul, map_inv] using
      congrArg N.centralToCore.symm htranslation

public theorem orderThreeCentralPairOrbitComparison_iff_commonGaugeComparison
    (N : A.ActualCuspCentralNaturality) :
    A.OrderThreeCentralPairOrbitComparison N ↔ A.OrderThreeCommonGaugeComparison N := by
  exact ⟨fun h ↦ OrderThreeCentralPairOrbitComparison.toCommonGaugeComparison A h,
    fun h ↦ OrderThreeCommonGaugeComparison.toCentralPairOrbitComparison A h⟩

/-- An exact based identification of the two central pairs is sufficient; the orbit comparison
then uses the identity gauge. -/
public theorem orderThreeCentralPairOrbitComparison_of_eq
    (N : A.ActualCuspCentralNaturality)
    (h : A.orderThreeCentralMarkedPair N = A.orderThreePhysicalMarkedPairInCentral N) :
    A.OrderThreeCentralPairOrbitComparison N := by
  unfold OrderThreeCentralPairOrbitComparison
  rw [h]
  exact simultaneouslyConjugate_refl _

end SphereSixComplex.Geometry.PaperAnalyticData

end
