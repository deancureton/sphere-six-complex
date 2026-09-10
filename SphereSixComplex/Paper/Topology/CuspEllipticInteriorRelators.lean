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
      A.starCover.stage (2 : Fin 4) := by
  intro x hx
  rw [A.ellipticInterior_eq_threePieceUnion]
  exact Or.inl (Or.inl hx)

public def actualCoreToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.core, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.actualCore_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualThreeToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticThree, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.orderThreePiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualFourToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticFour, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.orderFourPiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualCoreToEllipticInteriorPiOne :=
  FundamentalGroup.map A.actualCoreToEllipticInterior
    ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩

public theorem actualThreeRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.ellipticThreeOverlapToCore
        A.ellipticThreeCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticThreeConnector
    D.ellipticThreeConnector_mem D.ellipticThreePoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticThree) _
        A.ellipticThreeCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualThreeToEllipticInterior.comp D.ellipticThreeOverlapToPiece) _
      A.ellipticThreeCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualThreeToEllipticInterior _
    (D.ellipticThreeOverlapFundamentalGroupMap
      A.ellipticThreeCanonicalRelator) = 1
  rw [A.ellipticThreeCanonicalRelator_killed, map_one]

public theorem actualFourRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.ellipticFourOverlapToCore
        A.ellipticFourCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticFourConnector
    D.ellipticFourConnector_mem D.ellipticFourPoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticFour) _
        A.ellipticFourCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualFourToEllipticInterior.comp D.ellipticFourOverlapToPiece) _
      A.ellipticFourCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualFourToEllipticInterior _
    (D.ellipticFourOverlapFundamentalGroupMap
      A.ellipticFourCanonicalRelator) = 1
  rw [A.ellipticFourCanonicalRelator_killed, map_one]

public theorem ellipticInterior_orderThree_fullIterate :
    let C := A.coreDataOf A.cuspCentralNaturality
    A.actualCoreToEllipticInteriorPiOne C.rhoOne ^ 3 =
      A.actualCoreToEllipticInteriorPiOne (Additive.toMul (C.translation (-epsilon))) := by
  have hn : Subgroup.normalClosure
      {A.ellipticThreeOverlapToCore A.ellipticThreeCanonicalRelator} ≤
      A.actualCoreToEllipticInteriorPiOne.ker := by
    apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact A.actualThreeRelator_ellipticInterior_killed
  have h := hn (Classical.choice A.ellipticRelatorMembership_proved).orderThree
  rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
  exact mul_inv_eq_one.mp h

public theorem ellipticInterior_orderFour_fullIterate :
    let C := A.coreDataOf A.cuspCentralNaturality
    A.actualCoreToEllipticInteriorPiOne C.rhoTwo ^ 4 =
      A.actualCoreToEllipticInteriorPiOne (Additive.toMul (C.translation epsilon')) := by
  have hn : Subgroup.normalClosure
      {A.ellipticFourOverlapToCore A.ellipticFourCanonicalRelator} ≤
      A.actualCoreToEllipticInteriorPiOne.ker := by
    apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact A.actualFourRelator_ellipticInterior_killed
  have h := hn (Classical.choice A.ellipticRelatorMembership_proved).orderFour
  rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
  exact mul_inv_eq_one.mp h

public theorem ellipticInterior_peripheral_twelfth_abelian
    {H : Type*} [AddCommGroup H]
    (f : FundamentalGroup A.ellipticInterior
      (A.actualCoreToEllipticInterior
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) →*
        Multiplicative H) :
    let C := A.coreDataOf A.cuspCentralNaturality
    f (A.actualCoreToEllipticInteriorPiOne ((C.rhoOne * C.rhoTwo)⁻¹)) ^ 12 =
      f (A.actualCoreToEllipticInteriorPiOne
        (Additive.toMul (C.translation (Pi.single (0 : Fin 4) 1)))) := by
  apply affineCore_peripheral_twelfth_abelian
    (A.coreDataOf A.cuspCentralNaturality)
    (f.comp A.actualCoreToEllipticInteriorPiOne)
  · simpa only [map_pow, MonoidHom.comp_apply] using
      congrArg f A.ellipticInterior_orderThree_fullIterate
  · simpa only [map_pow, MonoidHom.comp_apply] using
      congrArg f A.ellipticInterior_orderFour_fullIterate

public theorem ellipticInterior_cuspMeridian_twelfth_abelian
    {H : Type*} [AddCommGroup H]
    (f : FundamentalGroup A.ellipticInterior
      (A.actualCoreToEllipticInterior
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) →*
        Multiplicative H) :
    f (A.actualCoreToEllipticInteriorPiOne
      (A.cuspOverlapToCore A.cuspAffineBridgeMeridian)⁻¹) ^ 12 =
      f (A.actualCoreToEllipticInteriorPiOne
        (A.cuspOverlapToCore (Additive.toMul
          (A.cuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))) := by
  rw [A.cuspBridge_translation_core A.cuspCentralNaturality,
    A.cuspBridge_meridian_core A.cuspCentralNaturality]
  have hz : Additive.toMul
      ((A.coreDataOf A.cuspCentralNaturality).translation 0) = 1 :=
    congrArg Additive.toMul (map_zero
      (A.coreDataOf A.cuspCentralNaturality).translation)
  rw [hz]
  simp only [inv_one, mul_one]
  exact A.ellipticInterior_peripheral_twelfth_abelian f

end SphereSixComplex.Geometry.PaperAnalyticData
end
