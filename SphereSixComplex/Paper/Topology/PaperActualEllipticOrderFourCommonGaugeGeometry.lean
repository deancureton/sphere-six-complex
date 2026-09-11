module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourRelatorComparison
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry

/-!
# The invariant order-four common-gauge comparison

The two marked order-four generators must be compared with one common change of basepoint.
This module moves that comparison back through the marked central-to-core equivalence.  The
result is an equality of diagonal conjugacy orbits of ordered pairs in the central fundamental
group.  It is independent of the connector used to transport the elliptic overlap into the core.

The marked physical meridian is used with its covering-space orientation, without inversion.
The paired lattice translation is `epsilon'`; the `-epsilon'` occurring in the analytic collar
formula is the affine lift convention and is not the marked deck translation in the relator.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The exact order-four overlap chart into the punctured central family. -/
public noncomputable def ellipticFourOverlapToCentral :
    C((A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace),
      A.CentralFamily) where
  toFun x := A.starToCentral 2 (A.orderFourCollarToActualOverlapHomeomorph.symm x)
  continuous_toFun :=
    (A.starToCentral_isOpenEmbedding 2).continuous.comp
      A.orderFourCollarToActualOverlapHomeomorph.symm.continuous

/-- The literal order-four overlap chart commutes with the inclusion into the actual core. -/
public theorem centralToSectionSevenEulerPiece_ellipticFourOverlapToCentral
    (x : (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)) :
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticFourOverlapToCentral x) =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour x := by
  apply Subtype.ext
  let q := A.orderFourCollarToActualOverlapHomeomorph.symm x
  calc
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.ellipticFourOverlapToCentral x)).1 =
        A.openEmbeddingStarData.collarSourceToGlued 2 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 2 q
    _ = x.1 := by
      change (A.orderFourCollarToActualOverlapHomeomorph q).1 = x.1
      exact congrArg Subtype.val
        (A.orderFourCollarToActualOverlapHomeomorph.apply_symm_apply x)

/-- The literal order-four overlap base viewed in the central family. -/
public noncomputable def ellipticFourOverlapCentralBase : A.CentralFamily :=
  A.ellipticFourOverlapToCentral
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩

/-- The central-family homeomorphism, followed by the order-four connector, gives an
equivalence from the literal central overlap base to the van Kampen core base. -/
public noncomputable def ellipticFourCentralToCoreEquiv :
    FundamentalGroup A.CentralFamily A.ellipticFourOverlapCentralBase ≃*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
      (A.centralToSectionSevenEulerPiece_ellipticFourOverlapToCentral
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticFourConnector
        A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1).symm)

/-- The literal central chart followed by the geometric central-to-core equivalence is exactly
the actual overlap inclusion with its prescribed order-four connector. -/
public theorem ellipticFourOverlapToCore_eq_central
    (gamma : FundamentalGroup
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) :
    A.ellipticFourOverlapToCore gamma =
      A.ellipticFourCentralToCoreEquiv
        (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl gamma) := by
  have hmap :
      (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
        C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
          A.ellipticFourOverlapToCentral =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticFour := by
    apply ContinuousMap.ext
    intro x
    exact A.centralToSectionSevenEulerPiece_ellipticFourOverlapToCentral x
  have hcentral :
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
          A.ellipticFourOverlapCentralBase =
        A.actualVanKampenFourPieceCover.overlapToCore
          A.actualVanKampenFourPieceCover.ellipticFour
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_ellipticFourOverlapToCentral _
  have hcompbase := congrArg
    (fun k : C((A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace),
      A.actualVanKampenFourPieceCover.core) ↦
        k ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) hmap
  have hinner : ∀ delta,
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph hcentral)
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl delta) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ delta := by
    intro delta
    change FundamentalGroup.mapOfEq
        (⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)) hcentral
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl delta) = _
    calc
      _ = FundamentalGroup.mapOfEq
          ((⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
              A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩ :
            C(A.CentralFamily, A.actualVanKampenFourPieceCover.core)).comp
              A.ellipticFourOverlapToCentral)
          hcompbase delta :=
        TauCeti.FundamentalGroup.mapOfEq_comp _ _ rfl hcentral delta
      _ = FundamentalGroup.mapOfEq
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour) rfl delta :=
        TauCeti.FundamentalGroup.mapOfEq_congr hmap _ rfl delta
      _ = FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ delta := by
        rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hhom :
      (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        hcentral).toMonoidHom.comp
          (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl) =
        FundamentalGroup.map
          (A.actualVanKampenFourPieceCover.overlapToCore
            A.actualVanKampenFourPieceCover.ellipticFour)
          ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
            A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ := by
    ext delta
    exact hinner delta
  simp only [ellipticFourOverlapToCore, ellipticFourCentralToCoreEquiv]
  rw [← hhom]
  rfl

/-- The central-family point under the chosen lift of the order-four overlap base. -/
public noncomputable def ellipticFourCentralBase : A.CentralFamily :=
  A.ellipticFourOverlapToCentral
    (A.ellipticFourBoundaryProjection
      A.ellipticFourBoundaryBase)





/-- A common path from the displayed affine base to the order-four overlap base in the central
family. -/
public noncomputable def orderFourCentralBaseWhisker :
    Path A.centralAffineBase A.ellipticFourCentralBase := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  exact PathConnectedSpace.somePath _ _















end SphereSixComplex.Geometry.PaperAnalyticData

end
