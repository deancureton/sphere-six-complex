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

/-- The central-to-core equivalence, viewed directly from the literal actual cusp base. -/
public noncomputable def actualCuspToCoreEquiv :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.actualCuspToCentralAffineBaseEquiv.trans A.actualCuspCentralToCoreEquiv

/-- The geometric core marking corrected by the appropriate inner cusp power. -/
public noncomputable def geometricMarkedCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.actualCuspToCentralAffineBaseEquiv.symm.trans
    (A.actualCuspCentralMarkingCorrection.trans A.actualCuspToCoreEquiv)

/-- Evaluation of the corrected geometric marking on a class transported from the literal
actual cusp base. -/
public theorem geometricMarkedCentralToCoreEquiv_apply_actualCusp
    (gamma : FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :
    A.geometricMarkedCentralToCoreEquiv
        (A.actualCuspToCentralAffineBaseEquiv gamma) =
      A.actualCuspToCoreEquiv
        (A.actualCuspCentralMarkingCorrection gamma) := by
  unfold geometricMarkedCentralToCoreEquiv
  change A.actualCuspToCoreEquiv
      (A.actualCuspCentralMarkingCorrection
        (A.actualCuspToCentralAffineBaseEquiv.symm
          (A.actualCuspToCentralAffineBaseEquiv gamma))) = _
  rw [A.actualCuspToCentralAffineBaseEquiv.symm_apply_apply]

/-- Monoid-hom form of the corrected geometric marking evaluation lemma. -/
public theorem geometricMarkedCentralToCoreEquiv_toMonoidHom_apply_actualCusp
    (gamma : FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :
    A.geometricMarkedCentralToCoreEquiv.toMonoidHom
        (A.actualCuspToCentralAffineBaseEquiv gamma) =
      A.actualCuspToCoreEquiv
        (A.actualCuspCentralMarkingCorrection gamma) := by
  exact A.geometricMarkedCentralToCoreEquiv_apply_actualCusp gamma

/-- The literal cusp chart followed by the core inclusion is compatible with the direct
actual-cusp-to-core equivalence. -/
public theorem actualCuspOverlapToCore_eq_fromActual
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)
      A.actualCuspOverlapBase) :
    A.actualCuspOverlapToCore gamma =
      A.actualCuspToCoreEquiv (A.actualCuspOverlapToCentralPiOne gamma) := by
  rw [A.actualCuspOverlapToCore_eq_central]
  unfold actualCuspToCoreEquiv actualCuspToCentralAffineBaseEquiv
    actualCuspOverlapToCentralPiOne
  change A.actualCuspCentralToCoreEquiv
      (FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral _ gamma) =
    A.actualCuspCentralToCoreEquiv
      (SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
        A.centralAffineBase_eq_actualCuspCentralBase.symm
        (FundamentalGroup.map A.actualCuspOverlapToCentral
          A.actualCuspOverlapBase gamma))
  congr 1

/-- Marked cusp-to-central naturality constructed from the literal cusp loops, geometric finite
meridians, and their proved common peripheral conjugator. -/
public noncomputable def actualCuspCentralNaturality :
    A.ActualCuspCentralNaturality := by
  refine {
    centralToCore := A.geometricMarkedCentralToCoreEquiv
    translation_naturality := ?_
    meridian_naturality := ?_
  }
  · apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul]
    rw [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
    rw [A.actualCuspOverlapToCore_eq_fromActual]
    rw [A.actualCuspOverlapToCentralPiOne_translation]
    rw [A.centralAffineCorePiOneData_translation]
    rw [A.geometricMarkedCentralToCoreEquiv_toMonoidHom_apply_actualCusp]
    rw [A.actualCuspCentralMarkingCorrection_translation]
  · rw [A.actualCuspOverlapToCore_eq_fromActual]
    rw [A.actualCuspOverlapToCentralPiOne_meridian]
    rw [A.centralAffineCorePiOneData_rhoOne,
      A.centralAffineCorePiOneData_rhoTwo, ← map_mul]
    rw [← A.actualCuspCentralMeridian_eq_geometricRhoProduct]
    rw [A.geometricMarkedCentralToCoreEquiv_apply_actualCusp]
    rw [A.actualCuspCentralMarkingCorrection_meridian]

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
