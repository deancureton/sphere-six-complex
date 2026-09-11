module

public import SphereSixComplex.Paper.Topology.AffineVanKampenTransport
public import SphereSixComplex.Paper.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Paper.Topology.PaperCuspCentralNaturality

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


/-- The chosen cusp translation, transported to the prescribed overlap base point. -/
public noncomputable def cuspAffineBridgeTranslation :
    Lattice →+ Additive
      (FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.cuspOverlapBase) :=
  fundamentalGroupAddHomOfBaseEq
    A.cuspChosenAffineFillingCover_boundaryBase_eq
    A.cuspChosenAffineFillingCover.translation

/-- The chosen cusp meridian, transported to the prescribed overlap base point. -/
public noncomputable def cuspAffineBridgeMeridian :
    FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
        Set A.VanKampenSpace)
      A.cuspOverlapBase :=
  fundamentalGroupElementOfBaseEq
    A.cuspChosenAffineFillingCover_boundaryBase_eq
    A.cuspChosenAffineFillingCover.meridian

/-- The actual cusp overlap inclusion is onto on fundamental groups. -/
public theorem cuspOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  rw [← A.cuspChosenAffineFillingCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.cuspChosenAffineFillingCover_boundaryBase_eq
    A.cuspChosenAffineFillingCover_fillingBase_eq
    A.cuspChosenAffineFillingCover.fundamentalGroupMap
    A.cuspChosenAffineFillingCover.fundamentalGroupMap_surjective

/-- The actual overlap-to-core map gives the cusp square required by the affine star bridge. -/
public theorem cuspAffineBridge_cuspSquare :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.cuspOverlapToCore =
      A.actualVanKampenFourPieceCover.cuspFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap := by
  ext γ
  let connCore :=
    A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.cuspConnector
      A.actualVanKampenFourPieceCover.cuspConnector_mem
      A.actualVanKampenFourPieceCover.cuspPoint_mem.1
  have hnat := CoveringSpace.map_fundamentalGroupMulEquivOfPath
    (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core) connCore.symm
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp)
      A.cuspOverlapBase γ)
  have hpath :
      connCore.symm.map
          (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core).continuous =
        A.actualVanKampenFourPieceCover.cuspConnector.symm := by
    ext t
    rfl
  change FundamentalGroup.map
      (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      A.actualVanKampenFourPieceCover.cuspConnector.symm) _
  apply Eq.trans hnat
  rw [hpath]
  congr 1
  have h1 :
      FundamentalGroup.map
          (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core)
          ⟨A.actualVanKampenFourPieceCover.cuspPoint,
            A.actualVanKampenFourPieceCover.cuspPoint_mem.1⟩
          (FundamentalGroup.map
            (A.actualVanKampenFourPieceCover.overlapToCore
              A.actualVanKampenFourPieceCover.cusp)
            A.cuspOverlapBase γ) =
        FundamentalGroup.map
          ((CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core).comp
            (A.actualVanKampenFourPieceCover.overlapToCore
              A.actualVanKampenFourPieceCover.cusp))
          A.cuspOverlapBase γ :=
    CoveringSpace.map_map _ _ _ _
  have h2 :
      FundamentalGroup.map
          (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.cusp)
          ⟨A.actualVanKampenFourPieceCover.cuspPoint,
            A.actualVanKampenFourPieceCover.cuspPoint_mem.2⟩
          (FundamentalGroup.map
            A.actualVanKampenFourPieceCover.cuspOverlapToPiece
            A.cuspOverlapBase γ) =
        FundamentalGroup.map
          ((CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.cusp).comp
            A.actualVanKampenFourPieceCover.cuspOverlapToPiece)
          A.cuspOverlapBase γ :=
    CoveringSpace.map_map _ _ _ _
  apply Eq.trans h1
  apply Eq.trans ?_ h2.symm
  rfl



/-- The actual cusp filling kills the marked angular meridian. -/
public theorem cuspAffineBridge_meridian_killed :
    A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap
        A.cuspAffineBridgeMeridian = 1 := by
  rw [← A.cuspChosenAffineFillingCover_map_eq]
  change fundamentalGroupHomOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover_fillingBase_eq
      A.cuspChosenAffineFillingCover.fundamentalGroupMap
      (fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspChosenAffineFillingCover.meridian) = 1
  rw [fundamentalGroupHomOfBaseEq_apply,
    A.cuspChosenAffineFillingCover.fundamentalGroupMap_meridian]
  exact fundamentalGroupElementOfBaseEq_one _

/-- The actual cusp filling kills every marked translation in the paper's toric sublattice. -/
public theorem cuspAffineBridge_toric_killed (a : Lattice)
    (ha : a ∈ paperToricSubgroup) :
    A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap
        (Additive.toMul (A.cuspAffineBridgeTranslation a)) = 1 := by
  obtain ⟨k, hk⟩ := paperCuspVanishing_onto a ha
  rw [← hk, ← A.cuspChosenAffineFillingCover_map_eq]
  unfold cuspAffineBridgeTranslation
  have hinput :
      Additive.toMul
          ((fundamentalGroupAddHomOfBaseEq
            A.cuspChosenAffineFillingCover_boundaryBase_eq
            A.cuspChosenAffineFillingCover.translation)
              (paperCuspVanishing k)) =
        fundamentalGroupElementOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          (Additive.toMul
            (A.cuspChosenAffineFillingCover.translation
              (paperCuspVanishing k))) := by
    change Additive.toMul
        ((fundamentalGroupAddHomOfBaseEq
          A.cuspChosenAffineFillingCover_boundaryBase_eq
          A.cuspChosenAffineFillingCover.translation)
            (paperCuspVanishing k)) =
      Additive.toMul
        (Additive.ofMul
          (fundamentalGroupElementOfBaseEq
            A.cuspChosenAffineFillingCover_boundaryBase_eq
            (Additive.toMul
              (A.cuspChosenAffineFillingCover.translation
                (paperCuspVanishing k)))))
    exact congrArg Additive.toMul
      (fundamentalGroupAddHomOfBaseEq_apply
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspChosenAffineFillingCover.translation
        (paperCuspVanishing k))
  have htransport :=
    fundamentalGroupHomOfBaseEq_apply
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover_fillingBase_eq
      A.cuspChosenAffineFillingCover.fundamentalGroupMap
      (Additive.toMul
        (A.cuspChosenAffineFillingCover.translation
          (paperCuspVanishing k)))
  exact (congrArg
    (fundamentalGroupHomOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover_fillingBase_eq
      A.cuspChosenAffineFillingCover.fundamentalGroupMap) hinput).trans <|
    htransport.trans <| by
      change fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_fillingBase_eq
        (A.cuspChosenAffineFillingCover.fundamentalGroupMap
          (Additive.toMul
            (A.cuspChosenAffineFillingCover.translation
              (A.cuspChosenAffineFillingCover.vanishing k)))) = 1
      rw [A.cuspChosenAffineFillingCover.fundamentalGroupMap_vanishing]
      exact fundamentalGroupElementOfBaseEq_one _


end SphereSixComplex.Geometry.PaperAnalyticData

end
