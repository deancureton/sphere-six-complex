module

public import SphereSixComplex.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Topology.PaperCuspChosenAffineFilling

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
