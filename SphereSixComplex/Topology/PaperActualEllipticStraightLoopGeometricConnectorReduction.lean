module

public import SphereSixComplex.Topology.PaperActualEllipticStraightLoopIdentitiesProof

/-!
# Geometric connector reduction for the actual elliptic straight loops
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

public theorem orderThreeActualOverlapToCentral_boundaryProjection_apply
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.orderThreeActualOverlapToCentral
        (A.orderThreeActualEllipticBoundaryProjection q) =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)) := by
  simp [orderThreeActualOverlapToCentral,
    orderThreeActualEllipticBoundaryProjection,
    orderThreeRadialMappingTorusToActualOverlapHomeomorph]
  apply congrArg (A.starToCentral 1)
  exact A.orderThreeCollarToActualOverlapHomeomorph.symm_apply_apply _

public theorem orderFourActualOverlapToCentral_boundaryProjection_apply
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.orderFourActualOverlapToCentral
        (A.orderFourActualEllipticBoundaryProjection q) =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)) := by
  simp [orderFourActualOverlapToCentral,
    orderFourActualEllipticBoundaryProjection,
    orderFourRadialMappingTorusToActualOverlapHomeomorph]
  apply congrArg (A.starToCentral 2)
  exact A.orderFourCollarToActualOverlapHomeomorph.symm_apply_apply _

/-- The order-three straight deck loop after applying the literal overlap chart. -/
public noncomputable def orderThreeActualEllipticBoundaryDeckStraightCentralLoop
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact (A.orderThreeActualEllipticBoundaryDeckStraightLoop g).map
    A.orderThreeActualOverlapToCentral.continuous

/-- The order-four straight deck loop after applying the literal overlap chart. -/
public noncomputable def orderFourActualEllipticBoundaryDeckStraightCentralLoop
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact (A.orderFourActualEllipticBoundaryDeckStraightLoop g).map
    A.orderFourActualOverlapToCentral.continuous

public theorem orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightLoop g)) =
      Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderFourActualEllipticBoundaryDeckStraightCentralLoop_class
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightLoop g)) =
      Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          ((A.orderThreeActualEllipticBoundaryDeckStraightLift g t).1,
            orderThreeAffineMappingTorusLiftProjection A.periods
              (A.orderThreeActualEllipticBoundaryDeckStraightLift g t).2)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  unfold orderThreeActualEllipticBoundaryDeckStraightCentralLoop
    orderThreeActualEllipticBoundaryDeckStraightLoop
  exact A.orderThreeActualOverlapToCentral_boundaryProjection_apply
    (A.orderThreeActualEllipticBoundaryDeckStraightLift g t)

public theorem orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          ((A.orderFourActualEllipticBoundaryDeckStraightLift g t).1,
            orderFourAffineMappingTorusLiftProjection A.periods
              (A.orderFourActualEllipticBoundaryDeckStraightLift g t).2)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  unfold orderFourActualEllipticBoundaryDeckStraightCentralLoop
    orderFourActualEllipticBoundaryDeckStraightLoop
  exact A.orderFourActualOverlapToCentral_boundaryProjection_apply
    (A.orderFourActualEllipticBoundaryDeckStraightLift g t)

public theorem orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_segment
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          (A.orderThreeActualEllipticBoundaryBase.1,
            orderThreeAffineMappingTorusLiftProjection A.periods
              (Path.segment A.orderThreeActualEllipticBoundaryBase.2
                (g • A.orderThreeActualEllipticBoundaryBase.2) t))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  simpa [orderThreeActualEllipticBoundaryDeckStraightLift] using
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply g t

public theorem orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_segment
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          (A.orderFourActualEllipticBoundaryBase.1,
            orderFourAffineMappingTorusLiftProjection A.periods
              (Path.segment A.orderFourActualEllipticBoundaryBase.2
                (g • A.orderFourActualEllipticBoundaryBase.2) t))) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  simpa [orderFourActualEllipticBoundaryDeckStraightLift] using
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply g t

/-- The prescribed van Kampen connector, pulled back through the central-piece chart. -/
public noncomputable def orderThreeActualCentralGeometricConnector :
    Path A.centralAffineBase A.orderThreeActualEllipticCentralBase := by
  let H := A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let c := A.actualVanKampenFourPieceCover.connectorInCore
    A.actualVanKampenFourPieceCover.ellipticThreeConnector
    A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
    A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1
  have hs : H.symm (⟨A.vanKampenBase,
      A.actualVanKampenFourPieceCover.base_mem_core⟩ :
        A.actualVanKampenFourPieceCover.core) = A.centralAffineBase := by
    have hcore : H A.centralAffineBase =
        (⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :
          A.actualVanKampenFourPieceCover.core) := by
      rw [A.centralAffineBase_eq_actualCuspCentralBase]
      exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
        A.actualCuspOverlapBase
    apply H.injective
    exact (H.apply_symm_apply _).trans hcore.symm
  have ht : H.symm (⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1⟩ :
        A.actualVanKampenFourPieceCover.core) =
      A.orderThreeActualEllipticCentralBase := by
    have hcore : H A.orderThreeActualEllipticCentralBase =
        (⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1⟩ :
            A.actualVanKampenFourPieceCover.core) := by
      rw [A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase]
      exact A.centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
    apply H.injective
    exact (H.apply_symm_apply _).trans hcore.symm
  exact (c.map H.symm.continuous).cast hs.symm ht.symm

/-- The prescribed order-four van Kampen connector, pulled back through the central chart. -/
public noncomputable def orderFourActualCentralGeometricConnector :
    Path A.centralAffineBase A.orderFourActualEllipticCentralBase := by
  let H := A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let c := A.actualVanKampenFourPieceCover.connectorInCore
    A.actualVanKampenFourPieceCover.ellipticFourConnector
    A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
    A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1
  have hs : H.symm (⟨A.vanKampenBase,
      A.actualVanKampenFourPieceCover.base_mem_core⟩ :
        A.actualVanKampenFourPieceCover.core) = A.centralAffineBase := by
    have hcore : H A.centralAffineBase =
        (⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :
          A.actualVanKampenFourPieceCover.core) := by
      rw [A.centralAffineBase_eq_actualCuspCentralBase]
      exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
        A.actualCuspOverlapBase
    apply H.injective
    exact (H.apply_symm_apply _).trans hcore.symm
  have ht : H.symm (⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1⟩ :
        A.actualVanKampenFourPieceCover.core) =
      A.orderFourActualEllipticCentralBase := by
    have hcore : H A.orderFourActualEllipticCentralBase =
        (⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1⟩ :
            A.actualVanKampenFourPieceCover.core) := by
      rw [A.orderFourActualEllipticCentralBase_eq_overlapCentralBase]
      exact A.centralToSectionSevenEulerPiece_orderFourActualOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
    apply H.injective
    exact (H.apply_symm_apply _).trans hcore.symm
  exact (c.map H.symm.continuous).cast hs.symm ht.symm

public theorem centralToSectionSevenEulerPiece_orderThreeActualCentralGeometricConnector_apply
    (t : unitInterval) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.orderThreeActualCentralGeometricConnector t) =
      A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticThreeConnector
        A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1 t := by
  unfold orderThreeActualCentralGeometricConnector
  exact A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.apply_symm_apply _

public theorem centralToSectionSevenEulerPiece_orderFourActualCentralGeometricConnector_apply
    (t : unitInterval) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.orderFourActualCentralGeometricConnector t) =
      A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticFourConnector
        A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1 t := by
  unfold orderFourActualCentralGeometricConnector
  exact A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.apply_symm_apply _

/-- The two remaining concrete path-class equalities for the order-three chart are sufficient. -/
public theorem orderThreeCentralBoundaryExistentialStraightLoopIdentities_of_geometricConnector_loopClasses
    (hmeridian :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
            A.orderThreeActualEllipticBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector A.centralAffineCorePiOneData.rhoOne)
    (htranslation :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
            (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector
          (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))) :
    A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  refine ⟨A.orderThreeActualCentralGeometricConnector, ?_, ?_⟩
  · rw [A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class]
    exact hmeridian
  · rw [A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class]
    exact htranslation

/-- The two remaining concrete path-class equalities for the order-four chart are sufficient. -/
public theorem orderFourCentralBoundaryExistentialStraightLoopIdentities_of_geometricConnector_loopClasses
    (hmeridian :
      letI := A.orderFourActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
            A.orderFourActualEllipticBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderFourActualCentralGeometricConnector A.centralAffineCorePiOneData.rhoTwo)
    (htranslation :
      letI := A.orderFourActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
            (Additive.toMul
              (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderFourActualCentralGeometricConnector
          (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))) :
    A.OrderFourCentralBoundaryExistentialStraightLoopIdentities := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  refine ⟨A.orderFourActualCentralGeometricConnector, ?_, ?_⟩
  · rw [A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class]
    exact hmeridian
  · rw [A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class]
    exact htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
