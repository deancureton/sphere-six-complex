module

public import SphereSixComplex.Topology.AffineStarRelatorNormalClosureBridge
public import SphereSixComplex.Topology.PaperActualEllipticCanonicalFiniteMarking
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

/-!
# Connector-invariant elliptic relators for the actual paper star

The two elliptic filling relations are compared with the central affine presentation only up to
normal closure.  This is invariant under changing the connector paths in the four-piece cover.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

public theorem orderThreeActualEllipticCanonicalChosenCover_fillingBase_eq :
    A.orderThreeActualEllipticCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩ :=
  A.orderThreeActualEllipticFillingMarkedDeckData.toExtensionAtBase.toFillingExtension
    |>.toChosenCover_fillingBase_eq

public theorem orderFourActualEllipticCanonicalChosenCover_fillingBase_eq :
    A.orderFourActualEllipticCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩ :=
  A.orderFourActualEllipticFillingExtensionAtBase.toFillingExtension
    |>.toChosenCover_fillingBase_eq

public theorem orderThreeActualEllipticCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderThreeActualEllipticCanonicalChosenCover_fillingBase_eq
        A.orderThreeActualEllipticCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderThreeActualEllipticCanonicalChosenCover_fillingBase_eq

public theorem orderFourActualEllipticCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderFourActualEllipticCanonicalChosenCover_fillingBase_eq
        A.orderFourActualEllipticCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderFourActualEllipticCanonicalChosenCover_fillingBase_eq

/-- The sign-correct order-three filling relator in the actual overlap fundamental group. -/
public noncomputable def orderThreeActualEllipticCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
      A.orderThreeActualEllipticCanonicalChosenCover.meridian) ^ 3 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderThreeActualEllipticCanonicalChosenCover.translation) (-epsilon)))⁻¹

/-- The sign-correct order-four filling relator in the actual overlap fundamental group. -/
public noncomputable def orderFourActualEllipticCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
      A.orderFourActualEllipticCanonicalChosenCover.meridian) ^ 4 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderFourActualEllipticCanonicalChosenCover.translation) epsilon'))⁻¹

public theorem orderThreeActualEllipticCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
        A.orderThreeActualEllipticCanonicalRelator = 1 := by
  rw [← A.orderThreeActualEllipticCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.orderThreeActualEllipticCanonicalChosenCover
    A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderThreeActualEllipticCanonicalChosenCover_fillingBase_eq rfl

public theorem orderFourActualEllipticCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
        A.orderFourActualEllipticCanonicalRelator = 1 := by
  rw [← A.orderFourActualEllipticCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.orderFourActualEllipticCanonicalChosenCover
    A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderFourActualEllipticCanonicalChosenCover_fillingBase_eq rfl

public theorem orderThreeActualEllipticOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  rw [← A.orderThreeActualEllipticCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderThreeActualEllipticCanonicalChosenCover_fillingBase_eq
    A.orderThreeActualEllipticCanonicalChosenCover.fundamentalGroupMap
    A.orderThreeActualEllipticCanonicalChosenCover.fundamentalGroupMap_surjective

public theorem orderFourActualEllipticOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  rw [← A.orderFourActualEllipticCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
    A.orderFourActualEllipticCanonicalChosenCover_fillingBase_eq
    A.orderFourActualEllipticCanonicalChosenCover.fundamentalGroupMap
    A.orderFourActualEllipticCanonicalChosenCover.fundamentalGroupMap_surjective

/-- The only remaining connector-invariant elliptic input: each expected central relator is in
the normal closure of the corresponding actual transported local relator. -/
public structure ActualEllipticRelatorNormalClosureResidual
    (N : A.ActualCuspCentralNaturality) : Prop where
  orderThree :
    (A.coreDataOf N).rhoOne ^ 3 *
        (Additive.toMul ((A.coreDataOf N).translation (-epsilon)))⁻¹ ∈
      Subgroup.normalClosure
        {A.actualEllipticThreeOverlapToCore
          A.orderThreeActualEllipticCanonicalRelator}
  orderFour :
    (A.coreDataOf N).rhoTwo ^ 4 *
        (Additive.toMul ((A.coreDataOf N).translation epsilon'))⁻¹ ∈
      Subgroup.normalClosure
        {A.actualEllipticFourOverlapToCore
          A.orderFourActualEllipticCanonicalRelator}

/-- The remaining actual elliptic comparison, stated invariantly as two whole-relator
normal-closure memberships. -/
public axiom establishedActualEllipticRelatorNormalClosureResidual :
    Nonempty
      (ActualEllipticRelatorNormalClosureResidual
        A A.actualCuspCentralNaturality)

namespace ActualEllipticRelatorNormalClosureResidual

variable {A : PaperAnalyticData} {N : A.ActualCuspCentralNaturality}

/-- Assemble the connector-invariant affine filling bridge for the actual four-piece star. -/
public noncomputable def bridge
    (R : ActualEllipticRelatorNormalClosureResidual A N) :
    AffineTorusStarRelatorNormalClosureBridge
      A.actualVanKampenFourPieceCover (A.coreDataOf N)
      3 4 (-epsilon) epsilon' 0 paperToricSubgroup where
  cuspSurjective := A.actualCuspOverlapFundamentalGroupMap_surjective
  oneSurjective := A.orderThreeActualEllipticOverlapFundamentalGroupMap_surjective
  twoSurjective := A.orderFourActualEllipticOverlapFundamentalGroupMap_surjective
  cuspToCore := A.actualCuspOverlapToCore
  oneToCore := A.actualEllipticThreeOverlapToCore
  twoToCore := A.actualEllipticFourOverlapToCore
  cuspSquare := A.actualCuspAffineBridge_cuspSquare
  oneSquare := A.actualEllipticThreeAffineBridge_square
  twoSquare := A.actualEllipticFourAffineBridge_square
  cuspTranslation := A.actualCuspAffineBridgeTranslation
  cuspMeridian := A.actualCuspAffineBridgeMeridian
  cuspTranslation_core := A.cuspBridge_translation_core N
  cuspMeridian_core := A.cuspBridge_meridian_core N
  cuspMeridian_killed := A.actualCuspAffineBridge_meridian_killed
  cuspToric_killed := A.actualCuspAffineBridge_toric_killed
  oneRelator := A.orderThreeActualEllipticCanonicalRelator
  oneRelator_killed := A.orderThreeActualEllipticCanonicalRelator_killed
  oneExpected_mem_normalClosure := R.orderThree
  twoRelator := A.orderFourActualEllipticCanonicalRelator
  twoRelator_killed := A.orderFourActualEllipticCanonicalRelator_killed
  twoExpected_mem_normalClosure := R.orderFour

/-- The two connector-invariant elliptic relator comparisons imply the paper's complete van
Kampen presentation for the actual analytic star. -/
public theorem hasVanKampenData
    (R : ActualEllipticRelatorNormalClosureResidual A N) :
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

end ActualEllipticRelatorNormalClosureResidual

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
