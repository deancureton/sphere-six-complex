module

public import SphereSixComplex.Paper.Topology.AffineStarRelatorNormalClosureBridge
public import SphereSixComplex.Paper.Topology.PaperActualEllipticCanonicalFiniteMarking

/-!
# Connector-invariant elliptic relators for the actual paper star

The two elliptic filling relations are compared with the central affine presentation only up to
normal closure.  This is invariant under changing the connector paths in the four-piece cover.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : AnalyticData)

public theorem ellipticThreeCanonicalChosenCover_fillingBase_eq :
    A.ellipticThreeCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩ :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase
    |>.toChosenCover_fillingBase_eq

public theorem ellipticFourCanonicalChosenCover_fillingBase_eq :
    A.ellipticFourCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩ :=
  A.ellipticFourFillingExtensionAtBase
    |>.toChosenCover_fillingBase_eq

public theorem ellipticThreeCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        A.ellipticThreeCanonicalChosenCover_fillingBase_eq
        A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq

public theorem ellipticFourCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        A.ellipticFourCanonicalChosenCover_fillingBase_eq
        A.ellipticFourCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq

/-- The sign-correct order-three filling relator in the actual overlap fundamental group. -/
public noncomputable def ellipticThreeCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
      A.ellipticThreeCanonicalChosenCover.meridian) ^ 3 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        A.ellipticThreeCanonicalChosenCover.translation) (-epsilon)))⁻¹

/-- The sign-correct order-four filling relator in the actual overlap fundamental group. -/
public noncomputable def ellipticFourCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.ellipticFourCanonicalChosenCover_boundaryBase_eq
      A.ellipticFourCanonicalChosenCover.meridian) ^ 4 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        A.ellipticFourCanonicalChosenCover.translation) epsilon'))⁻¹

public theorem ellipticThreeCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
        A.ellipticThreeCanonicalRelator = 1 := by
  rw [← A.ellipticThreeCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.ellipticThreeCanonicalChosenCover
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq rfl

public theorem ellipticFourCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
        A.ellipticFourCanonicalRelator = 1 := by
  rw [← A.ellipticFourCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.ellipticFourCanonicalChosenCover
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq rfl

public theorem ellipticThreeOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  rw [← A.ellipticThreeCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq
    A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap
    A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap_surjective

public theorem ellipticFourOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  rw [← A.ellipticFourCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq
    A.ellipticFourCanonicalChosenCover.fundamentalGroupMap
    A.ellipticFourCanonicalChosenCover.fundamentalGroupMap_surjective

/-- The only remaining connector-invariant elliptic input: each expected central relator is in
the normal closure of the corresponding actual transported local relator. -/
public structure EllipticRelatorMembership
    (N : A.CuspCentralNaturality) : Prop where
  orderThree :
    (A.coreDataOf N).rhoOne ^ 3 *
        (Additive.toMul ((A.coreDataOf N).translation (-epsilon)))⁻¹ ∈
      Subgroup.normalClosure
        {A.ellipticThreeOverlapToCore
          A.ellipticThreeCanonicalRelator}
  orderFour :
    (A.coreDataOf N).rhoTwo ^ 4 *
        (Additive.toMul ((A.coreDataOf N).translation epsilon'))⁻¹ ∈
      Subgroup.normalClosure
        {A.ellipticFourOverlapToCore
          A.ellipticFourCanonicalRelator}

namespace EllipticRelatorMembership

variable {A : AnalyticData} {N : A.CuspCentralNaturality}

/-- Assemble the connector-invariant affine filling bridge for the actual four-piece star. -/
public noncomputable def bridge
    (R : EllipticRelatorMembership A N) :
    AffineTorusStarRelatorNormalClosureBridge
      A.actualVanKampenFourPieceCover (A.coreDataOf N)
      3 4 (-epsilon) epsilon' 0 paperToricSubgroup where
  cuspSurjective := A.cuspOverlapFundamentalGroupMap_surjective
  oneSurjective := A.ellipticThreeOverlapFundamentalGroupMap_surjective
  twoSurjective := A.ellipticFourOverlapFundamentalGroupMap_surjective
  cuspToCore := A.cuspOverlapToCore
  oneToCore := A.ellipticThreeOverlapToCore
  twoToCore := A.ellipticFourOverlapToCore
  cuspSquare := A.cuspAffineBridge_cuspSquare
  oneSquare := A.ellipticThreeAffineBridge_square
  twoSquare := A.ellipticFourAffineBridge_square
  cuspTranslation := A.cuspAffineBridgeTranslation
  cuspMeridian := A.cuspAffineBridgeMeridian
  cuspTranslation_core := A.cuspBridge_translation_core N
  cuspMeridian_core := A.cuspBridge_meridian_core N
  cuspMeridian_killed := A.cuspAffineBridge_meridian_killed
  cuspToric_killed := A.cuspAffineBridge_toric_killed
  oneRelator := A.ellipticThreeCanonicalRelator
  oneRelator_killed := A.ellipticThreeCanonicalRelator_killed
  oneExpected_mem_normalClosure := R.orderThree
  twoRelator := A.ellipticFourCanonicalRelator
  twoRelator_killed := A.ellipticFourCanonicalRelator_killed
  twoExpected_mem_normalClosure := R.orderFour

/-- The two connector-invariant elliptic relator comparisons imply the paper's complete van
Kampen presentation for the actual analytic star. -/
public theorem hasVanKampenData
    (R : EllipticRelatorMembership A N) :
    HasVanKampenData A.VanKampenSpace 0 1 (-1) := by
  let _ := A.vanKampenCharts
  have _ : StronglyLocallyContractibleSpace A.VanKampenSpace := A.vanKampen_locallyNice
  have _ : PathConnectedSpace A.VanKampenSpace := A.vanKampen_pathConnected
  have _ : TauCeti.SemilocallySimplyConnectedSpace A.VanKampenSpace :=
    A.vanKampen_semilocallySimplyConnected
  obtain ⟨hcore, relations⟩ := R.bridge.relationsAndCoreSurjective
  exact hasVanKampenData_of_correctedAffineData _
    ((A.coreDataOf N).mapSurjective
      A.actualVanKampenFourPieceCover.coreFundamentalGroupMap hcore)
    relations

end EllipticRelatorMembership

end SphereSixComplex.Geometry.AnalyticData

end

end
