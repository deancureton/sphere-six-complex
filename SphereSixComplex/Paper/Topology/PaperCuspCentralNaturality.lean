module

public import SphereSixComplex.Paper.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Paper.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperActualVanKampenNiceness

/-!
# Marked cusp naturality in the actual affine core

This module isolates the marked peripheral identification between the explicit cusp cover and the
affine presentation of the central family. It does not assert a filling relation or a conclusion
about the fundamental group of the filled star.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open CuspPuncturedCollarBridge

variable (A : AnalyticData)

/-- The actual cusp overlap included into the core and transported along the specified connector
to the base point of the four-piece cover. -/
public noncomputable def cuspOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.cuspOverlapBase →*
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
      A.cuspOverlapBase)

/-- The actual central-family identification with the core piece, based at the geometric cusp
point and then transported along the specified connector to the van Kampen base. -/
public noncomputable def cuspCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (by
        rw [A.centralAffineBase_eq_cuspCentralBase]
        exact A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral
          A.cuspOverlapBase)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.cuspConnector
        A.actualVanKampenFourPieceCover.cuspConnector_mem
        A.actualVanKampenFourPieceCover.cuspPoint_mem.1).symm)

/-- The map induced by the literal cusp chart, followed by the actual central-to-core
identification, is the overlap inclusion with its prescribed basepoint transport. -/
public theorem cuspOverlapToCore_eq_central
    (γ : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)
      A.cuspOverlapBase) :
    A.cuspOverlapToCore γ =
      A.cuspCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.cuspOverlapToCentral
          A.centralAffineBase_eq_cuspCentralBase.symm γ) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.cuspOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.centralAffineBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp A.cuspOverlapBase := by
    rw [A.centralAffineBase_eq_cuspCentralBase]
    exact A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral
      A.cuspOverlapBase
  have hcusp : A.cuspOverlapToCentral A.cuspOverlapBase =
      A.centralAffineBase :=
    A.centralAffineBase_eq_cuspCentralBase.symm
  have hcompbase :
      ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.cuspOverlapToCentral) A.cuspOverlapBase =
        (A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.cusp) A.cuspOverlapBase :=
    congrArg (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦ k A.cuspOverlapBase) hmap
  have hinner : ∀ δ,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral)
          (FundamentalGroup.mapOfEq A.cuspOverlapToCentral
            hcusp δ) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.cuspOverlapBase δ := by
    intro δ
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.cuspOverlapToCentral hcusp δ) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.cuspOverlapToCentral)
          hcompbase δ :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ hcusp hcentral δ
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp) rfl δ :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl δ
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.cuspOverlapBase δ := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.cuspOverlapToCentral
            hcusp) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.cusp)
          A.cuspOverlapBase := by
    ext δ
    exact hinner δ
  simp only [cuspOverlapToCore, cuspCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- Marked peripheral naturality between the explicit cusp cover and the actual affine core.

The equivalence is part of the marking data. In particular, it is not identified with the
unrelated path-based equivalence chosen in the general van Kampen assembly. -/
public structure CuspCentralNaturality where
  centralToCore : FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩
  translation_naturality :
    A.cuspOverlapToCore.toAdditive.comp
        (fundamentalGroupAddHomOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          A.cuspChosenAffineFillingCover.translation) =
      centralToCore.toMonoidHom.toAdditive.comp A.centralAffineCorePiOneData.translation
  meridian_naturality :
    A.cuspOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          A.cuspChosenAffineFillingCover.meridian) =
      centralToCore
        (A.centralAffineCorePiOneData.rhoOne * A.centralAffineCorePiOneData.rhoTwo)

/-- The central-to-core equivalence, viewed directly from the literal actual cusp base. -/
public noncomputable def cuspToCoreEquiv :
    FundamentalGroup A.CentralFamily A.cuspCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.cuspToCentralAffineBaseEquiv.trans A.cuspCentralToCoreEquiv

/-- The geometric core marking corrected by the appropriate inner cusp power. -/
public noncomputable def geometricMarkedCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.cuspToCentralAffineBaseEquiv.symm.trans
    (A.cuspCentralMarkingCorrection.trans A.cuspToCoreEquiv)

/-- Evaluation of the corrected geometric marking on a class transported from the literal
actual cusp base. -/
public theorem geometricMarkedCentralToCoreEquiv_apply_actualCusp
    (gamma : FundamentalGroup A.CentralFamily A.cuspCentralBase) :
    A.geometricMarkedCentralToCoreEquiv
        (A.cuspToCentralAffineBaseEquiv gamma) =
      A.cuspToCoreEquiv
        (A.cuspCentralMarkingCorrection gamma) := by
  unfold geometricMarkedCentralToCoreEquiv
  change A.cuspToCoreEquiv
      (A.cuspCentralMarkingCorrection
        (A.cuspToCentralAffineBaseEquiv.symm
          (A.cuspToCentralAffineBaseEquiv gamma))) = _
  rw [A.cuspToCentralAffineBaseEquiv.symm_apply_apply]

/-- Monoid-hom form of the corrected geometric marking evaluation lemma. -/
public theorem geometricMarkedCentralToCoreEquiv_toMonoidHom_apply_actualCusp
    (gamma : FundamentalGroup A.CentralFamily A.cuspCentralBase) :
    A.geometricMarkedCentralToCoreEquiv.toMonoidHom
        (A.cuspToCentralAffineBaseEquiv gamma) =
      A.cuspToCoreEquiv
        (A.cuspCentralMarkingCorrection gamma) := by
  exact A.geometricMarkedCentralToCoreEquiv_apply_actualCusp gamma

/-- The literal cusp chart followed by the core inclusion is compatible with the direct
actual-cusp-to-core equivalence. -/
public theorem cuspOverlapToCore_eq_fromActual
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)
      A.cuspOverlapBase) :
    A.cuspOverlapToCore gamma =
      A.cuspToCoreEquiv (A.cuspOverlapToCentralPiOne gamma) := by
  rw [A.cuspOverlapToCore_eq_central]
  unfold cuspToCoreEquiv cuspToCentralAffineBaseEquiv
    cuspOverlapToCentralPiOne
  change A.cuspCentralToCoreEquiv
      (FundamentalGroup.mapOfEq A.cuspOverlapToCentral _ gamma) =
    A.cuspCentralToCoreEquiv
      (SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
        A.centralAffineBase_eq_cuspCentralBase.symm
        (FundamentalGroup.map A.cuspOverlapToCentral
          A.cuspOverlapBase gamma))
  congr 1

/-- Marked cusp-to-central naturality constructed from the literal cusp loops, geometric finite
meridians, and their proved common peripheral conjugator. -/
public noncomputable def cuspCentralNaturality :
    A.CuspCentralNaturality := by
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
    rw [A.cuspOverlapToCore_eq_fromActual]
    rw [A.cuspOverlapToCentralPiOne_translation]
    rw [A.centralAffineCorePiOneData_translation]
    rw [A.geometricMarkedCentralToCoreEquiv_toMonoidHom_apply_actualCusp]
    rw [A.cuspCentralMarkingCorrection_translation]
  · rw [A.cuspOverlapToCore_eq_fromActual]
    rw [A.cuspOverlapToCentralPiOne_meridian]
    rw [A.centralAffineCorePiOneData_rhoOne,
      A.centralAffineCorePiOneData_rhoTwo, ← map_mul]
    rw [← A.cuspCentralMeridian_eq_geometricRhoProduct]
    rw [A.geometricMarkedCentralToCoreEquiv_apply_actualCusp]
    rw [A.cuspCentralMarkingCorrection_meridian]

namespace CuspCentralNaturality

variable {A : AnalyticData}

/-- Pointwise form of marked translation naturality, in multiplicative notation. -/
public theorem translation_core (N : A.CuspCentralNaturality) (a : Lattice) :
    A.cuspOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq
            A.cuspChosenAffineFillingCover_boundaryBase_eq
            A.cuspChosenAffineFillingCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a)) := by
  exact congrArg Additive.toMul (DFunLike.congr_fun N.translation_naturality a)

/-- Pointwise form of marked cusp-meridian naturality. -/
public theorem meridian_core (N : A.CuspCentralNaturality) :
    A.cuspOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          A.cuspChosenAffineFillingCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne *
        N.centralToCore A.centralAffineCorePiOneData.rhoTwo := by
  rw [← map_mul]
  exact N.meridian_naturality

end CuspCentralNaturality

end SphereSixComplex.Geometry.AnalyticData

end
