module

public import SphereSixComplex.Topology.EstablishedAffineStarBridge
public import SphereSixComplex.Topology.PaperCuspCentralNaturality

/-!
# The actual cusp side of the affine filling bridge

The explicit chosen cusp cover and its marked central naturality supply every cusp field of the
four-piece affine filling bridge. No elliptic filling data or final van Kampen relation is used.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

/-- The central affine presentation transported through the marked cusp naturality equivalence. -/
public noncomputable def actualCuspAffineCoreData :
    AffineTorusCorePiOneData
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.centralAffineCorePiOneData.mapSurjective
    A.actualCuspCentralNaturality.centralToCore.toMonoidHom
    A.actualCuspCentralNaturality.centralToCore.surjective

/-- The chosen cusp translation, transported to the prescribed overlap base point. -/
public noncomputable def actualCuspAffineBridgeTranslation :
    Lattice →+ Additive
      (FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.actualCuspOverlapBase) :=
  fundamentalGroupAddHomOfBaseEq
    A.actualCuspChosenAffineFillingCover_boundaryBase_eq
    A.actualCuspChosenAffineFillingCover.translation

/-- The chosen cusp meridian, transported to the prescribed overlap base point. -/
public noncomputable def actualCuspAffineBridgeMeridian :
    FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.actualCuspOverlapBase :=
  fundamentalGroupElementOfBaseEq
    A.actualCuspChosenAffineFillingCover_boundaryBase_eq
    A.actualCuspChosenAffineFillingCover.meridian

/-- The actual cusp overlap inclusion is onto on fundamental groups. -/
public theorem actualCuspOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  rw [← A.actualCuspChosenAffineFillingCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.actualCuspChosenAffineFillingCover_boundaryBase_eq
    A.actualCuspChosenAffineFillingCover_fillingBase_eq
    A.actualCuspChosenAffineFillingCover.fundamentalGroupMap
    A.actualCuspChosenAffineFillingCover.fundamentalGroupMap_surjective

/-- The actual overlap-to-core map gives the cusp square required by the affine star bridge. -/
public theorem actualCuspAffineBridge_cuspSquare :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.actualCuspOverlapToCore =
      A.actualVanKampenFourPieceCover.cuspFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  ext γ
  let connCore :=
    A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.cuspConnector
      A.actualVanKampenFourPieceCover.cuspConnector_mem
      A.actualVanKampenFourPieceCover.cuspPoint_mem.1
  have hnat := map_fundamentalGroupMulEquivOfPath
    (subsetInclusion A.actualVanKampenFourPieceCover.core) connCore.symm
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp)
      A.actualCuspOverlapBase γ)
  have hpath :
      connCore.symm.map
          (subsetInclusion A.actualVanKampenFourPieceCover.core).continuous =
        A.actualVanKampenFourPieceCover.cuspConnector.symm := by
    ext t
    rfl
  change FundamentalGroup.map
      (subsetInclusion A.actualVanKampenFourPieceCover.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      A.actualVanKampenFourPieceCover.cuspConnector.symm) _
  apply Eq.trans hnat
  rw [hpath]
  congr 1
  have h1 :
      FundamentalGroup.map
          (subsetInclusion A.actualVanKampenFourPieceCover.core)
          ⟨A.actualVanKampenFourPieceCover.cuspPoint,
            A.actualVanKampenFourPieceCover.cuspPoint_mem.1⟩
          (FundamentalGroup.map
            (A.actualVanKampenFourPieceCover.overlapToCore
              A.actualVanKampenFourPieceCover.cusp)
            A.actualCuspOverlapBase γ) =
        FundamentalGroup.map
          ((subsetInclusion A.actualVanKampenFourPieceCover.core).comp
            (A.actualVanKampenFourPieceCover.overlapToCore
              A.actualVanKampenFourPieceCover.cusp))
          A.actualCuspOverlapBase γ :=
    map_map _ _ _ _
  have h2 :
      FundamentalGroup.map
          (subsetInclusion A.actualVanKampenFourPieceCover.cusp)
          ⟨A.actualVanKampenFourPieceCover.cuspPoint,
            A.actualVanKampenFourPieceCover.cuspPoint_mem.2⟩
          (FundamentalGroup.map
            A.actualVanKampenFourPieceCover.cuspOverlapToPiece
            A.actualCuspOverlapBase γ) =
        FundamentalGroup.map
          ((subsetInclusion A.actualVanKampenFourPieceCover.cusp).comp
            A.actualVanKampenFourPieceCover.cuspOverlapToPiece)
          A.actualCuspOverlapBase γ :=
    map_map _ _ _ _
  apply Eq.trans h1
  apply Eq.trans ?_ h2.symm
  rfl

/-- Every marked cusp translation maps to the corresponding transported core translation. -/
public theorem actualCuspAffineBridge_translation_core (a : Lattice) :
    A.actualCuspOverlapToCore
        (Additive.toMul (A.actualCuspAffineBridgeTranslation a)) =
      Additive.toMul (A.actualCuspAffineCoreData.translation a) := by
  exact A.actualCuspCentralNaturality.translation_core a

/-- At cusp twist zero, the marked cusp meridian maps to the product of the two core meridians. -/
public theorem actualCuspAffineBridge_meridian_core :
    A.actualCuspOverlapToCore A.actualCuspAffineBridgeMeridian =
      A.actualCuspAffineCoreData.rhoOne * A.actualCuspAffineCoreData.rhoTwo *
        (Additive.toMul (A.actualCuspAffineCoreData.translation 0))⁻¹ := by
  apply Eq.trans A.actualCuspCentralNaturality.meridian_core
  change
    A.actualCuspCentralNaturality.centralToCore A.centralAffineCorePiOneData.rhoOne *
      A.actualCuspCentralNaturality.centralToCore A.centralAffineCorePiOneData.rhoTwo =
    A.actualCuspCentralNaturality.centralToCore A.centralAffineCorePiOneData.rhoOne *
      A.actualCuspCentralNaturality.centralToCore A.centralAffineCorePiOneData.rhoTwo *
      (A.actualCuspCentralNaturality.centralToCore
        (Additive.toMul (A.centralAffineCorePiOneData.translation 0)))⁻¹
  have hz : Additive.toMul (A.centralAffineCorePiOneData.translation 0) = 1 := by
    rw [map_zero]
    rfl
  rw [hz, map_one, inv_one, mul_one]

/-- The actual cusp filling kills the marked angular meridian. -/
public theorem actualCuspAffineBridge_meridian_killed :
    A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap
        A.actualCuspAffineBridgeMeridian = 1 := by
  rw [← A.actualCuspChosenAffineFillingCover_map_eq]
  change fundamentalGroupHomOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq
      A.actualCuspChosenAffineFillingCover_fillingBase_eq
      A.actualCuspChosenAffineFillingCover.fundamentalGroupMap
      (fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspChosenAffineFillingCover.meridian) = 1
  rw [fundamentalGroupHomOfBaseEq_apply,
    A.actualCuspChosenAffineFillingCover.fundamentalGroupMap_meridian]
  exact fundamentalGroupElementOfBaseEq_one _

/-- The actual cusp filling kills every marked translation in the paper's toric sublattice. -/
public theorem actualCuspAffineBridge_toric_killed (a : Lattice)
    (ha : a ∈ paperToricSubgroup) :
    A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap
        (Additive.toMul (A.actualCuspAffineBridgeTranslation a)) = 1 := by
  obtain ⟨k, hk⟩ := paperCuspVanishing_onto a ha
  rw [← hk, ← A.actualCuspChosenAffineFillingCover_map_eq]
  unfold actualCuspAffineBridgeTranslation
  have hinput :
      Additive.toMul
          ((fundamentalGroupAddHomOfBaseEq
            A.actualCuspChosenAffineFillingCover_boundaryBase_eq
            A.actualCuspChosenAffineFillingCover.translation)
              (paperCuspVanishing k)) =
        fundamentalGroupElementOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          (Additive.toMul
            (A.actualCuspChosenAffineFillingCover.translation
              (paperCuspVanishing k))) := by
    change Additive.toMul
        ((fundamentalGroupAddHomOfBaseEq
          A.actualCuspChosenAffineFillingCover_boundaryBase_eq
          A.actualCuspChosenAffineFillingCover.translation)
            (paperCuspVanishing k)) =
      Additive.toMul
        (Additive.ofMul
          (fundamentalGroupElementOfBaseEq
            A.actualCuspChosenAffineFillingCover_boundaryBase_eq
            (Additive.toMul
              (A.actualCuspChosenAffineFillingCover.translation
                (paperCuspVanishing k)))))
    exact congrArg Additive.toMul
      (fundamentalGroupAddHomOfBaseEq_apply
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspChosenAffineFillingCover.translation
        (paperCuspVanishing k))
  have htransport :=
    fundamentalGroupHomOfBaseEq_apply
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq
      A.actualCuspChosenAffineFillingCover_fillingBase_eq
      A.actualCuspChosenAffineFillingCover.fundamentalGroupMap
      (Additive.toMul
        (A.actualCuspChosenAffineFillingCover.translation
          (paperCuspVanishing k)))
  exact (congrArg
    (fundamentalGroupHomOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq
      A.actualCuspChosenAffineFillingCover_fillingBase_eq
      A.actualCuspChosenAffineFillingCover.fundamentalGroupMap) hinput).trans <|
    htransport.trans <| by
      change fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_fillingBase_eq
        (A.actualCuspChosenAffineFillingCover.fundamentalGroupMap
          (Additive.toMul
            (A.actualCuspChosenAffineFillingCover.translation
              (A.actualCuspChosenAffineFillingCover.vanishing k)))) = 1
      rw [A.actualCuspChosenAffineFillingCover.fundamentalGroupMap_vanishing]
      exact fundamentalGroupElementOfBaseEq_one _

/-- The chosen cusp vanishing map reaches every vector in the paper's toric sublattice. -/
public theorem actualCuspAffineBridge_vanishing_onto (a : Lattice)
    (ha : a ∈ paperToricSubgroup) :
    ∃ k, A.actualCuspChosenAffineFillingCover.vanishing k = a := by
  obtain ⟨k, hk⟩ := paperCuspVanishing_onto a ha
  refine ⟨k, ?_⟩
  change paperCuspVanishing k = a
  exact hk

end SphereSixComplex.Geometry.PaperAnalyticData

end
