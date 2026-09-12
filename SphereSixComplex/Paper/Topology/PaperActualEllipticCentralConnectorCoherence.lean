module

public import SphereSixComplex.Prerequisites.Topology.FundamentalGroupConnectorConjugacy
public import SphereSixComplex.Paper.Topology.PaperOrderThreeCentralBoundaryCoverComparison
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourCommonGaugeGeometry

/-!
# Connector coherence for the actual elliptic central charts

Changing both the point in the central family and the connector from its image into the core
changes every transported loop by one common conjugation.  This is the point-set bridge between
the order-specific overlap charts and the cusp marking used in the actual affine core.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex.Topology

open PaperVanKampenFourPieceCover

/-- Transport along a concatenated path is the composite of the two basepoint transports. -/
public theorem fundamentalGroupMulEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath q
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.trans q) a := by
  let ip := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk y)).symm ⟦p⟧
  let iq := (Groupoid.isoEquivHom (FundamentalGroupoid.mk y)
    (FundamentalGroupoid.mk z)).symm ⟦q⟧
  let ir := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk z)).symm ⟦p.trans q⟧
  have hir : ir = ip ≪≫ iq := by
    apply Iso.ext
    rfl
  simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply]
  change iq.inv ≫ (ip.inv ≫ a ≫ ip.hom) ≫ iq.hom = ir.inv ≫ a ≫ ir.hom
  rw [hir]
  simp [Category.assoc]

/-- Mapping a pair from two source basepoints and then using two target connectors gives one
simultaneous conjugacy. -/
public theorem fundamentalGroupMappedPair_simultaneouslyConjugate_of_sourcePath
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x z : X} {y : Y} (source : Path x z)
    (p : Path (f x) y) (q : Path (f z) y)
    (a b : FundamentalGroup X x) :
    SimultaneouslyConjugate
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x a),
        FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x b))
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q
          (FundamentalGroup.map f z
            (FundamentalGroup.fundamentalGroupMulEquivOfPath source a)),
        FundamentalGroup.fundamentalGroupMulEquivOfPath q
          (FundamentalGroup.map f z
            (FundamentalGroup.fundamentalGroupMulEquivOfPath source b))) := by
  have h := fundamentalGroupPair_simultaneouslyConjugate_of_paths p
    ((source.map f.continuous).trans q)
    (FundamentalGroup.map f x a) (FundamentalGroup.map f x b)
  rw [← fundamentalGroupMulEquivOfPath_trans,
    ← fundamentalGroupMulEquivOfPath_trans] at h
  rw [← CoveringSpace.map_fundamentalGroupMulEquivOfPath,
    ← CoveringSpace.map_fundamentalGroupMulEquivOfPath] at h
  exact h

/-- An equality-adjusted map followed by a connector is the same as the ordinary map followed
by the connector whose source has been cast along that equality. -/
public theorem fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y z : Y} (h : f x = y)
    (p : Path y z) (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.mapOfEq f h a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.cast h rfl)
        (FundamentalGroup.map f x a) := by
  subst y
  simp






/-- Casting the endpoint of a path and then changing basepoint along it is equality transport of
the original path-induced class. -/
public theorem fundamentalGroupMulEquivOfPath_cast_right
    {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y) (h : z = y)
    (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.cast rfl h) a =
      fundamentalGroupElementOfBaseEq h.symm
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p a) := by
  subst z
  unfold fundamentalGroupElementOfBaseEq
  simp

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.LatticeData

variable (A : AnalyticData)

/-- The central point obtained from the selected radial lift is the marked order-three overlap
point after applying the overlap chart. -/
public theorem ellipticThreeCentralBase_eq_overlapCentralBase :
    A.ellipticThreeCentralBase = A.ellipticThreeOverlapCentralBase := by
  exact congrArg A.ellipticThreeOverlapToCentral
    A.ellipticThreeBoundaryProjection_base

/-- The cusp connector and the order-three connector induce the same diagonal conjugacy orbit
on every ordered pair transported through the central-family homeomorphism. -/
public theorem cuspCentralToCorePair_simultaneouslyConjugate_orderThree
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderThreeCentralBaseWhisker.cast rfl
      A.ellipticThreeCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b)
      (A.ellipticThreeCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.ellipticThreeCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)) := by
  let H := A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let f : C(A.CentralFamily, A.actualVanKampenFourPieceCover.core) := ⟨H, H.continuous⟩
  let cuspConnector :=
    (A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.cuspConnector
      A.actualVanKampenFourPieceCover.cuspConnector_mem
      A.actualVanKampenFourPieceCover.cuspPoint_mem.1).symm
  let threeConnector :=
    (A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.ellipticThreeConnector
      A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1).symm
  let source := A.orderThreeCentralBaseWhisker.cast rfl
    A.ellipticThreeCentralBase_eq_overlapCentralBase.symm
  have hcusp : H A.centralAffineBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp A.cuspOverlapBase := by
    rw [A.centralAffineBase_eq_cuspCentralBase]
    exact A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral
      A.cuspOverlapBase
  have hthree : H A.ellipticThreeOverlapCentralBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_ellipticThreeOverlapToCentral _
  let p := cuspConnector.cast hcusp rfl
  let q := threeConnector.cast hthree rfl
  have h := fundamentalGroupMappedPair_simultaneouslyConjugate_of_sourcePath
    f source p q a b
  have hcuspA := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hcusp cuspConnector a
  have hcuspB := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hcusp cuspConnector b
  have hthreeA := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hthree threeConnector
      (FundamentalGroup.fundamentalGroupMulEquivOfPath source a)
  have hthreeB := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hthree threeConnector
      (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)
  change SimultaneouslyConjugate
    (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b) _
  change SimultaneouslyConjugate
    (FundamentalGroup.fundamentalGroupMulEquivOfPath cuspConnector
        (FundamentalGroup.mapOfEq f hcusp a),
      FundamentalGroup.fundamentalGroupMulEquivOfPath cuspConnector
        (FundamentalGroup.mapOfEq f hcusp b))
    (FundamentalGroup.fundamentalGroupMulEquivOfPath threeConnector
        (FundamentalGroup.mapOfEq f hthree
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a)),
      FundamentalGroup.fundamentalGroupMulEquivOfPath threeConnector
        (FundamentalGroup.mapOfEq f hthree
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)))
  convert h using 1
  · exact Prod.ext hcuspA hcuspB
  · exact Prod.ext hthreeA hthreeB

/-- The marking correction in the constructed cusp naturality changes any ordered pair only by
one common inner conjugation after transport to the actual core. -/
public theorem cuspCentralNaturalityPair_simultaneouslyConjugate_actualCusp
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    SimultaneouslyConjugate
      (A.cuspCentralNaturality.centralToCore a,
        A.cuspCentralNaturality.centralToCore b)
      (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b) := by
  let c : FundamentalGroup A.CentralFamily A.cuspCentralBase :=
    (A.cuspCentralMeridian ^ A.geometricCentralCuspConjugatorExponent)⁻¹
  let d := A.cuspToCentralAffineBaseEquiv c
  change SimultaneouslyConjugate
    (A.geometricMarkedCentralToCoreEquiv a,
      A.geometricMarkedCentralToCoreEquiv b)
    (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b)
  refine ⟨A.cuspCentralToCoreEquiv d, ?_, ?_⟩ <;>
    simp only [geometricMarkedCentralToCoreEquiv, cuspToCoreEquiv,
      cuspCentralMarkingCorrection, MulEquiv.trans_apply, MulAut.conj_inv_apply,
      map_mul, map_inv, MulEquiv.apply_symm_apply]
  <;> dsimp only [d, c]
  <;> simp only [map_inv, inv_inv]

/-- After both the cusp marking correction and the change of geometric connector, the
constructed central-to-core marking and the order-three overlap marking give the same diagonal
conjugacy orbit on every ordered pair. -/
public theorem cuspCentralNaturalityPair_simultaneouslyConjugate_orderThree
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderThreeCentralBaseWhisker.cast rfl
      A.ellipticThreeCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.cuspCentralNaturality.centralToCore a,
        A.cuspCentralNaturality.centralToCore b)
      (A.ellipticThreeCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.ellipticThreeCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)) := by
  exact (A.cuspCentralNaturalityPair_simultaneouslyConjugate_actualCusp a b).trans
    (A.cuspCentralToCorePair_simultaneouslyConjugate_orderThree a b)





end SphereSixComplex.Geometry.AnalyticData

end

end
