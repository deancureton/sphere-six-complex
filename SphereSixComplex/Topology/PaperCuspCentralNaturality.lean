module

public import SphereSixComplex.Topology.PaperCuspCentralCoverComparison
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# Marked cusp naturality in the actual affine core

This module isolates the marked peripheral identification between the explicit cusp cover and the
affine presentation of the central family. It does not assert a filling relation or a conclusion
about the fundamental group of the filled star.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The actual cusp overlap included into the core and transported along the specified connector
to the base point of the four-piece cover. -/
public noncomputable def actualCuspOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.actualCuspOverlapBase →*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.cuspConnector
        A.actualVanKampenFourPieceCover.cuspConnector_mem
        A.actualVanKampenFourPieceCover.cuspPoint_mem.1).symm).toMonoidHom.comp
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp)
      A.actualCuspOverlapBase)

/-- The actual central-family identification with the core piece, based at the geometric cusp
point and then transported along the specified connector to the van Kampen base. -/
public noncomputable def actualCuspCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (by
        rw [A.centralAffineBase_eq_actualCuspCentralBase]
        exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
          A.actualCuspOverlapBase)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.cuspConnector
        A.actualVanKampenFourPieceCover.cuspConnector_mem
        A.actualVanKampenFourPieceCover.cuspPoint_mem.1).symm)

/-- The map induced by the literal cusp chart, followed by the actual central-to-core
identification, is the overlap inclusion with its prescribed basepoint transport. -/
public theorem actualCuspOverlapToCore_eq_central
    (γ : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)
      A.actualCuspOverlapBase) :
    A.actualCuspOverlapToCore γ =
      A.actualCuspCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral
          A.centralAffineBase_eq_actualCuspCentralBase.symm γ) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.actualCuspOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.centralAffineBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp A.actualCuspOverlapBase := by
    rw [A.centralAffineBase_eq_actualCuspCentralBase]
    exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
      A.actualCuspOverlapBase
  have hcusp : A.actualCuspOverlapToCentral A.actualCuspOverlapBase =
      A.centralAffineBase :=
    A.centralAffineBase_eq_actualCuspCentralBase.symm
  have hcompbase :
      ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.actualCuspOverlapToCentral) A.actualCuspOverlapBase =
        (A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp) A.actualCuspOverlapBase :=
    congrArg (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦ k A.actualCuspOverlapBase) hmap
  have hinner : ∀ δ,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral)
          (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral
            hcusp δ) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.actualCuspOverlapBase δ := by
    intro δ
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral hcusp δ) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.actualCuspOverlapToCentral)
          hcompbase δ :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ hcusp hcentral δ
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp) rfl δ :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl δ
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.actualCuspOverlapBase δ := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral
            hcusp) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.actualCuspOverlapBase := by
    ext δ
    exact hinner δ
  simp only [actualCuspOverlapToCore, actualCuspCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- If the induced deck map has the marked algebraic value, cover naturality identifies every
actual cusp deck loop with that marked central loop. -/
public theorem actualCuspOverlapToCore_ofDeck
    (hdeck :
      let W := A.starCuspWitness
      letI := paperCuspBoundaryDeckAction W
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      A.actualCuspCentralCoverComparison.deckMap =
        paperCuspBoundaryToCentralDeck)
    (g : paperCuspBoundaryDeck) :
    let W := A.starCuspWitness
    letI := paperCuspBoundaryDeckAction W
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (additiveCuspRadiusCover W.localWitness.radius) :=
      additiveCuspBoundaryCover_simplyConnected W
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
        paperCuspBoundaryDeck :=
      (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
        A.cuspCollarToStarOverlapHomeomorph
    A.actualCuspOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          (ofDeck hp
            (paperCuspBoundaryBasePreimage W A.actualCuspLocalBoundaryBase) g)) =
      A.actualCuspCentralToCoreEquiv
        ((D.data.quotientCovering.fundamentalGroupEquiv
          ⟨A.centralAffineUniversalCoverPoint, rfl⟩).symm
          (MulOpposite.op (paperCuspBoundaryToCentralDeck g))) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  dsimp only
  dsimp only at hdeck
  rw [A.actualCuspOverlapToCore_eq_central]
  congr 1
  apply (D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPoint, rfl⟩).injective
  rw [(D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPoint, rfl⟩).apply_symm_apply]
  have hsource :
      A.actualCuspOverlapToCentral
          (A.actualCuspBoundaryProjection
            (paperCuspBoundaryBasePreimage W A.actualCuspLocalBoundaryBase)) =
        A.centralAffineBase := by
    change A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase) =
      A.centralAffineBase
    rw [A.actualCuspBoundaryCoverBase_projects]
    exact A.centralAffineBase_eq_actualCuspCentralBase.symm
  calc
    _ = D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral hsource
          (ofDeck hp
            (paperCuspBoundaryBasePreimage W A.actualCuspLocalBoundaryBase) g)) :=
      congrArg (D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩)
        (mapOfEq_fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspOverlapToCentral hsource
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (ofDeck hp
            (paperCuspBoundaryBasePreimage W A.actualCuspLocalBoundaryBase) g))
    _ = MulOpposite.op (A.actualCuspCentralCoverComparison.deckMap g) :=
      A.actualCuspCentralCoverComparison_ofDeck_actualBase g
    _ = MulOpposite.op (paperCuspBoundaryToCentralDeck g) :=
      congrArg (fun k ↦ MulOpposite.op (k g)) hdeck

/-- Marked peripheral naturality between the explicit cusp cover and the actual affine core.

The equivalence is part of the marking data. In particular, it is not identified with the
unrelated path-based equivalence chosen in the general van Kampen assembly. -/
public structure ActualCuspCentralNaturality where
  centralToCore : FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩
  translation_naturality :
    A.actualCuspOverlapToCore.toAdditive.comp
        (fundamentalGroupAddHomOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspChosenAffineFillingCover.translation) =
      centralToCore.toMonoidHom.toAdditive.comp A.centralAffineCorePiOneData.translation
  meridian_naturality :
    A.actualCuspOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspChosenAffineFillingCover.meridian) =
      centralToCore
        (A.centralAffineCorePiOneData.rhoOne * A.centralAffineCorePiOneData.rhoTwo)

/-- The actual cover square supplies marked peripheral naturality once its induced deck map is
identified with the explicit algebraic cusp inclusion. -/
public noncomputable def actualCuspCentralNaturality_of_deckMap_eq
    (hdeck :
      let W := A.starCuspWitness
      letI := paperCuspBoundaryDeckAction W
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      A.actualCuspCentralCoverComparison.deckMap =
        paperCuspBoundaryToCentralDeck) :
    A.ActualCuspCentralNaturality := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let E : FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
      paperCentralFreeAffineDeckᵐᵒᵖ :=
    D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
  refine {
    centralToCore := A.actualCuspCentralToCoreEquiv
    translation_naturality := ?_
    meridian_naturality := ?_
  }
  · apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul]
    rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
    rw [A.actualCuspChosenAffineFillingCover_translation_eq_ofDeck]
    calc
      _ = A.actualCuspCentralToCoreEquiv
          (E.symm (MulOpposite.op (paperCuspBoundaryToCentralDeck
            (Additive.toMul (paperCuspBoundaryTranslation a))))) :=
        A.actualCuspOverlapToCore_ofDeck hdeck _
      _ = A.actualCuspCentralToCoreEquiv
          (Additive.toMul (A.centralAffineCorePiOneData.translation a)) := by
        congr 1
        apply E.injective
        rw [E.apply_symm_apply, paperCuspBoundaryToCentralDeck_translation]
        exact (A.centralAffineCorePiOneData_translation_deck a).symm
  · rw [A.actualCuspChosenAffineFillingCover_meridian_eq_ofDeck]
    calc
      _ = A.actualCuspCentralToCoreEquiv
          (E.symm (MulOpposite.op
            (paperCuspBoundaryToCentralDeck paperCuspBoundaryMeridian))) :=
        A.actualCuspOverlapToCore_ofDeck hdeck _
      _ = A.actualCuspCentralToCoreEquiv
          (A.centralAffineCorePiOneData.rhoOne *
            A.centralAffineCorePiOneData.rhoTwo) := by
        congr 1
        apply E.injective
        rw [E.apply_symm_apply, map_mul,
          paperCuspBoundaryToCentralDeck_meridian]
        calc
          MulOpposite.op
              (freeAffineLift (M := paperCentralFreeMonodromy)
                paperCuspCentralBaseMeridian) =
              (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoOne *
                (oppositeFreeAffineCorePiOneData paperCentralFreeMonodromy).rhoTwo :=
            opposite_paperCuspCentralBaseMeridian_eq_rhoOne_mul_rhoTwo
          _ = E A.centralAffineCorePiOneData.rhoOne *
              E A.centralAffineCorePiOneData.rhoTwo :=
            congrArg₂ (· * ·)
              A.centralAffineCorePiOneData_rhoOne_deck.symm
              A.centralAffineCorePiOneData_rhoTwo_deck.symm

/-- The established marked peripheral naturality theorem for the actual cusp collar.

This is only the geometric identification of the cusp translation and meridian in the marked
central affine presentation. It is neither a filling relation nor a conclusion about the final
glued space. -/
public axiom establishedActualCuspCentralNaturality :
    Nonempty A.ActualCuspCentralNaturality

/-- A coherent choice of the marked cusp-to-central naturality data. -/
public noncomputable def actualCuspCentralNaturality :
    A.ActualCuspCentralNaturality :=
  Classical.choice A.establishedActualCuspCentralNaturality

namespace ActualCuspCentralNaturality

variable {A : PaperAnalyticData}

/-- Pointwise form of marked translation naturality, in multiplicative notation. -/
public theorem translation_core (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    A.actualCuspOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq
            A.actualCuspChosenAffineFillingCover_boundaryBase_eq
            A.actualCuspChosenAffineFillingCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a)) := by
  exact congrArg Additive.toMul (DFunLike.congr_fun N.translation_naturality a)

/-- Pointwise form of marked cusp-meridian naturality. -/
public theorem meridian_core (N : A.ActualCuspCentralNaturality) :
    A.actualCuspOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspChosenAffineFillingCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne *
        N.centralToCore A.centralAffineCorePiOneData.rhoTwo := by
  rw [← map_mul]
  exact N.meridian_naturality

end ActualCuspCentralNaturality

end SphereSixComplex.Geometry.PaperAnalyticData

end
