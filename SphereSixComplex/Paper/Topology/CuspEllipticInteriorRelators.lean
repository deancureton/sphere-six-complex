module
public import SphereSixComplex.Paper.Topology.AffinePeripheralAbelianization
public import SphereSixComplex.Paper.Topology.PaperEllipticSynchronizedPeriodTransport
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.LatticeData
open PaperVanKampenFourPieceCover
variable (A : PaperAnalyticData)

public theorem actualCore_subset_ellipticInterior :
    A.actualVanKampenFourPieceCover.core ⊆
      A.SectionSevenEllipticCover.stage (2 : Fin 4) := by
  intro x hx
  rw [A.sectionSevenFinalStage_eq_threePieceUnion]
  exact Or.inl (Or.inl hx)

public def actualCoreToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.core, A.SectionSevenEllipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.actualCore_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualThreeToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticThree, A.SectionSevenEllipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.sectionSevenOrderThreePiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualFourToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticFour, A.SectionSevenEllipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.sectionSevenOrderFourPiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualCoreToEllipticInteriorPiOne :=
  FundamentalGroup.map A.actualCoreToEllipticInterior
    ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩

public theorem actualThreeRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.actualEllipticThreeOverlapToCore
        A.orderThreeActualEllipticCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticThreeConnector
    D.ellipticThreeConnector_mem D.ellipticThreePoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticThree) _
        A.orderThreeActualEllipticCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualThreeToEllipticInterior.comp D.ellipticThreeOverlapToPiece) _
      A.orderThreeActualEllipticCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualThreeToEllipticInterior _
    (D.ellipticThreeOverlapFundamentalGroupMap
      A.orderThreeActualEllipticCanonicalRelator) = 1
  rw [A.orderThreeActualEllipticCanonicalRelator_killed, map_one]

public theorem actualFourRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.actualEllipticFourOverlapToCore
        A.orderFourActualEllipticCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticFourConnector
    D.ellipticFourConnector_mem D.ellipticFourPoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticFour) _
        A.orderFourActualEllipticCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualFourToEllipticInterior.comp D.ellipticFourOverlapToPiece) _
      A.orderFourActualEllipticCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualFourToEllipticInterior _
    (D.ellipticFourOverlapFundamentalGroupMap
      A.orderFourActualEllipticCanonicalRelator) = 1
  rw [A.orderFourActualEllipticCanonicalRelator_killed, map_one]

public theorem ellipticInterior_orderThree_fullIterate :
    let C := A.coreDataOf A.actualCuspCentralNaturality
    A.actualCoreToEllipticInteriorPiOne C.rhoOne ^ 3 =
      A.actualCoreToEllipticInteriorPiOne (Additive.toMul (C.translation (-epsilon))) := by
  have hn : Subgroup.normalClosure
      {A.actualEllipticThreeOverlapToCore A.orderThreeActualEllipticCanonicalRelator} ≤
      A.actualCoreToEllipticInteriorPiOne.ker := by
    apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact A.actualThreeRelator_ellipticInterior_killed
  have h := hn (Classical.choice A.actualEllipticRelatorNormalClosureResidual_proved).orderThree
  rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
  exact mul_inv_eq_one.mp h

public theorem ellipticInterior_orderFour_fullIterate :
    let C := A.coreDataOf A.actualCuspCentralNaturality
    A.actualCoreToEllipticInteriorPiOne C.rhoTwo ^ 4 =
      A.actualCoreToEllipticInteriorPiOne (Additive.toMul (C.translation epsilon')) := by
  have hn : Subgroup.normalClosure
      {A.actualEllipticFourOverlapToCore A.orderFourActualEllipticCanonicalRelator} ≤
      A.actualCoreToEllipticInteriorPiOne.ker := by
    apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact A.actualFourRelator_ellipticInterior_killed
  have h := hn (Classical.choice A.actualEllipticRelatorNormalClosureResidual_proved).orderFour
  rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
  exact mul_inv_eq_one.mp h

public theorem ellipticInterior_peripheral_twelfth_abelian
    {H : Type*} [AddCommGroup H]
    (f : FundamentalGroup A.SectionSevenEllipticInterior
      (A.actualCoreToEllipticInterior
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) →*
        Multiplicative H) :
    let C := A.coreDataOf A.actualCuspCentralNaturality
    f (A.actualCoreToEllipticInteriorPiOne ((C.rhoOne * C.rhoTwo)⁻¹)) ^ 12 =
      f (A.actualCoreToEllipticInteriorPiOne
        (Additive.toMul (C.translation (Pi.single (0 : Fin 4) 1)))) := by
  apply affineCore_peripheral_twelfth_abelian
    (A.coreDataOf A.actualCuspCentralNaturality)
    (f.comp A.actualCoreToEllipticInteriorPiOne)
  · simpa only [map_pow, MonoidHom.comp_apply] using
      congrArg f A.ellipticInterior_orderThree_fullIterate
  · simpa only [map_pow, MonoidHom.comp_apply] using
      congrArg f A.ellipticInterior_orderFour_fullIterate

public theorem ellipticInterior_cuspMeridian_twelfth_abelian
    {H : Type*} [AddCommGroup H]
    (f : FundamentalGroup A.SectionSevenEllipticInterior
      (A.actualCoreToEllipticInterior
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) →*
        Multiplicative H) :
    f (A.actualCoreToEllipticInteriorPiOne
      (A.actualCuspOverlapToCore A.actualCuspAffineBridgeMeridian)⁻¹) ^ 12 =
      f (A.actualCoreToEllipticInteriorPiOne
        (A.actualCuspOverlapToCore (Additive.toMul
          (A.actualCuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))) := by
  rw [A.cuspBridge_translation_core A.actualCuspCentralNaturality,
    A.cuspBridge_meridian_core A.actualCuspCentralNaturality]
  have hz : Additive.toMul
      ((A.coreDataOf A.actualCuspCentralNaturality).translation 0) = 1 :=
    congrArg Additive.toMul (map_zero
      (A.coreDataOf A.actualCuspCentralNaturality).translation)
  rw [hz]
  simp only [inv_one, mul_one]
  exact A.ellipticInterior_peripheral_twelfth_abelian f

end SphereSixComplex.Geometry.PaperAnalyticData
end
