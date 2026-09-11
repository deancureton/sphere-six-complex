module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeRelatorComparison
public import SphereSixComplex.Prerequisites.Topology.GroupPairConjugacy

/-!
# The invariant order-three common-gauge comparison

The two marked order-three generators must be compared with one common change of basepoint.
This module moves that comparison back through the marked central-to-core equivalence.  The
result is an equality of diagonal conjugacy orbits of ordered pairs in the central fundamental
group.  It is independent of the connector used to transport the elliptic overlap into the core.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The exact order-three overlap chart into the punctured central family. -/
public noncomputable def ellipticThreeOverlapToCentral :
    C((A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace),
      A.CentralFamily) where
  toFun x := A.starToCentral 1 (A.orderThreeCollarToActualOverlapHomeomorph.symm x)
  continuous_toFun :=
    (A.starToCentral_isOpenEmbedding 1).continuous.comp
      A.orderThreeCollarToActualOverlapHomeomorph.symm.continuous

/-- The literal order-three overlap chart commutes with the inclusion into the actual core. -/
public theorem centralToSectionSevenEulerPiece_ellipticThreeOverlapToCentral
    (x : (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticThreeOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree x := by
  apply Subtype.ext
  let q := A.orderThreeCollarToActualOverlapHomeomorph.symm x
  calc
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticThreeOverlapToCentral x)).1 =
        A.openEmbeddingStarData.collarSourceToGlued 1 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 1 q
    _ = x.1 := by
      change (A.orderThreeCollarToActualOverlapHomeomorph q).1 = x.1
      exact congrArg Subtype.val
        (A.orderThreeCollarToActualOverlapHomeomorph.apply_symm_apply x)

/-- The literal order-three overlap base viewed in the central family. -/
public noncomputable def ellipticThreeOverlapCentralBase : A.CentralFamily :=
  A.ellipticThreeOverlapToCentral
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩

/-- The central-family homeomorphism, followed by the order-three connector, gives an
equivalence from the literal central overlap base to the van Kampen core base. -/
public noncomputable def ellipticThreeCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.ellipticThreeOverlapCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (A.centralToSectionSevenEulerPiece_ellipticThreeOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticThreeConnector
        A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1).symm)

/-- The literal central chart followed by the geometric central-to-core equivalence is exactly
the actual overlap inclusion with its prescribed order-three connector. -/
public theorem ellipticThreeOverlapToCore_eq_central
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) :
    A.ellipticThreeOverlapToCore gamma =
      A.ellipticThreeCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl gamma) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.ellipticThreeOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticThree := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPiece_ellipticThreeOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.ellipticThreeOverlapCentralBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticThree
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_ellipticThreeOverlapToCentral _
  have hcompbase := congrArg
    (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦
        k ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) hmap
  have hinner : ∀ delta,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph hcentral)
          (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl delta) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ delta := by
    intro delta
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl delta) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.ellipticThreeOverlapToCentral)
          hcompbase delta :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ rfl hcentral delta
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree) rfl delta :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl delta
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ delta := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticThree)
          ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
            A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ := by
    ext delta
    exact hinner delta
  simp only [ellipticThreeOverlapToCore, ellipticThreeCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- The central-family point under the chosen lift of the order-three overlap base. -/
public noncomputable def ellipticThreeCentralBase : A.CentralFamily :=
  A.ellipticThreeOverlapToCentral
    (A.ellipticThreeBoundaryProjection
      A.ellipticThreeBoundaryBase)





/-- A common path from the displayed affine base to the order-three overlap base in the central
family. -/
public noncomputable def orderThreeCentralBaseWhisker :
    Path A.centralAffineBase A.ellipticThreeCentralBase := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  exact PathConnectedSpace.somePath _ _















end SphereSixComplex.Geometry.PaperAnalyticData

end
