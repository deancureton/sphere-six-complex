module

public import SphereSixComplex.Topology.PaperOrderThreeCentralMarkingConnectorBridge
public import SphereSixComplex.Topology.EstablishedBasedVanKampen

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
  rw [← map_fundamentalGroupMulEquivOfPath,
    ← map_fundamentalGroupMulEquivOfPath] at h
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

/-- A group equivalence carries simultaneous inner conjugation of a pair to simultaneous inner
conjugation by the image of the same element. -/
public theorem mulEquiv_conjugatedPair_simultaneouslyConjugate
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (c a b : G) :
    SimultaneouslyConjugate
      (e (c * a * c⁻¹), e (c * b * c⁻¹)) (e a, e b) := by
  refine ⟨e c, ?_, ?_⟩ <;> simp

/-- The categorical fundamental-group equivalence attached to a point equality is the same
point transport as `fundamentalGroupElementOfBaseEq`. -/
public theorem fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (a : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfEq h a = fundamentalGroupElementOfBaseEq h a := by
  subst y
  rw [fundamentalGroupMulEquivOfEq_apply]
  unfold fundamentalGroupElementOfBaseEq
  simp

/-- Two successive equality transports of a loop are transport along the composite equality. -/
public theorem fundamentalGroupElementOfBaseEq_trans
    {X : Type*} [TopologicalSpace X] {x y z : X} (h : x = y) (k : y = z)
    (a : FundamentalGroup X x) :
    fundamentalGroupElementOfBaseEq k (fundamentalGroupElementOfBaseEq h a) =
      fundamentalGroupElementOfBaseEq (h.trans k) a := by
  subst y
  subst z
  rfl

/-- Equality transport after equality transport through the categorical equivalence is the
single composite point transport. -/
public theorem fundamentalGroupMulEquivOfEq_elementOfBaseEq_trans
    {X : Type*} [TopologicalSpace X] {x y z : X} (h : x = y) (k : y = z)
    (a : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfEq k (fundamentalGroupElementOfBaseEq h a) =
      fundamentalGroupElementOfBaseEq (h.trans k) a := by
  rw [fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq,
    fundamentalGroupElementOfBaseEq_trans]

/-- Changing the target basepoint of an equality-adjusted fundamental-group map composes the
two target equalities. -/
public theorem fundamentalGroupMulEquivOfEq_mapOfEq_trans
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y z : Y} (h : f x = y) (k : y = z)
    (a : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfEq k (FundamentalGroup.mapOfEq f h a) =
      FundamentalGroup.mapOfEq f (h.trans k) a := by
  subst y
  subst z
  rw [fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq]
  unfold fundamentalGroupElementOfBaseEq
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

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.LatticeData

variable (A : PaperAnalyticData)

/-- The central point obtained from the selected radial lift is the marked order-three overlap
point after applying the overlap chart. -/
public theorem orderThreeActualEllipticCentralBase_eq_overlapCentralBase :
    A.orderThreeActualEllipticCentralBase = A.orderThreeActualOverlapCentralBase := by
  exact congrArg A.orderThreeActualOverlapToCentral
    A.orderThreeActualEllipticBoundaryProjection_base

/-- The cusp connector and the order-three connector induce the same diagonal conjugacy orbit
on every ordered pair transported through the central-family homeomorphism. -/
public theorem actualCuspCentralToCorePair_simultaneouslyConjugate_orderThree
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderThreeCentralBaseWhisker.cast rfl
      A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.actualCuspCentralToCoreEquiv a, A.actualCuspCentralToCoreEquiv b)
      (A.orderThreeActualCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.orderThreeActualCentralToCoreEquiv
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
    A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase.symm
  have hcusp : H A.centralAffineBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp A.actualCuspOverlapBase := by
    rw [A.centralAffineBase_eq_actualCuspCentralBase]
    exact A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral
      A.actualCuspOverlapBase
  have hthree : H A.orderThreeActualOverlapCentralBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_orderThreeActualOverlapToCentral _
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
    (A.actualCuspCentralToCoreEquiv a, A.actualCuspCentralToCoreEquiv b) _
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
public theorem actualCuspCentralNaturalityPair_simultaneouslyConjugate_actualCusp
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    SimultaneouslyConjugate
      (A.actualCuspCentralNaturality.centralToCore a,
        A.actualCuspCentralNaturality.centralToCore b)
      (A.actualCuspCentralToCoreEquiv a, A.actualCuspCentralToCoreEquiv b) := by
  let c : FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
    (A.actualCuspCentralMeridian ^ A.geometricCentralCuspConjugatorExponent)⁻¹
  let d := A.actualCuspToCentralAffineBaseEquiv c
  change SimultaneouslyConjugate
    (A.geometricMarkedCentralToCoreEquiv a,
      A.geometricMarkedCentralToCoreEquiv b)
    (A.actualCuspCentralToCoreEquiv a, A.actualCuspCentralToCoreEquiv b)
  refine ⟨A.actualCuspCentralToCoreEquiv d, ?_, ?_⟩ <;>
    simp only [geometricMarkedCentralToCoreEquiv, actualCuspToCoreEquiv,
      actualCuspCentralMarkingCorrection, MulEquiv.trans_apply, MulAut.conj_inv_apply,
      map_mul, map_inv, MulEquiv.apply_symm_apply]
  <;> dsimp only [d, c]
  <;> simp only [map_inv, inv_inv]

/-- After both the cusp marking correction and the change of geometric connector, the
constructed central-to-core marking and the order-three overlap marking give the same diagonal
conjugacy orbit on every ordered pair. -/
public theorem actualCuspCentralNaturalityPair_simultaneouslyConjugate_orderThree
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderThreeCentralBaseWhisker.cast rfl
      A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.actualCuspCentralNaturality.centralToCore a,
        A.actualCuspCentralNaturality.centralToCore b)
      (A.orderThreeActualCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.orderThreeActualCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)) := by
  exact (A.actualCuspCentralNaturalityPair_simultaneouslyConjugate_actualCusp a b).trans
    (A.actualCuspCentralToCorePair_simultaneouslyConjugate_orderThree a b)

public theorem orderThreeCentralMeridianAtOverlap_eq_pathTransport :
    A.orderThreeCentralMeridianAtOverlap =
      FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderThreeCentralBaseWhisker
        A.centralAffineCorePiOneData.rhoOne := by
  unfold orderThreeCentralMeridianAtOverlap
  rfl

public theorem orderThreeCentralTranslationAtOverlap_eq_pathTransport :
    A.orderThreeCentralTranslationAtOverlap =
      FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderThreeCentralBaseWhisker
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) := by
  unfold orderThreeCentralTranslationAtOverlap
  rfl

/-- The local order-three marked-loop comparison, transported through the literal overlap chart
and its geometric connector, is the physical marked pair in the actual core. -/
public theorem OrderThreeCentralMarkedLoopCompatibility.toActualCorePair
    (H : A.OrderThreeCentralMarkedLoopCompatibility) :
    let source := A.orderThreeCentralBaseWhisker.cast rfl
      A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.orderThreeActualCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source
            A.centralAffineCorePiOneData.rhoOne),
        A.orderThreeActualCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source
            (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))))
      (A.orderThreeActualEllipticPhysicalMeridianToCore,
        Additive.toMul (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let C := A.orderThreeActualCentralCoverComparison
  dsimp only [OrderThreeCentralMarkedLoopCompatibility] at H
  let hbase := C.commutes A.orderThreeActualEllipticBoundaryBase
  let hoverlap := A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  have hpoint : D.data.projection (C.lift A.orderThreeActualEllipticBoundaryBase) =
      A.orderThreeActualOverlapCentralBase := by
    calc
      _ = C.baseMap
          (A.orderThreeActualEllipticBoundaryProjection
            A.orderThreeActualEllipticBoundaryBase) :=
        (C.commutes A.orderThreeActualEllipticBoundaryBase).symm
      _ = A.orderThreeActualEllipticCentralBase := rfl
      _ = A.orderThreeActualOverlapCentralBase :=
        A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  let E := fundamentalGroupMulEquivOfEq hpoint
  let source := A.orderThreeCentralBaseWhisker.cast rfl hoverlap.symm
  have hcomp : hbase.trans hpoint = hoverlap := Subsingleton.elim _ _
  have hleftAny (a : FundamentalGroup A.CentralFamily A.centralAffineBase) :
      E (fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker a)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath source a := by
    have ht := fundamentalGroupMulEquivOfEq_elementOfBaseEq_trans hbase hpoint
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBaseWhisker a)
    rw [hcomp] at ht
    exact ht.trans
      (fundamentalGroupMulEquivOfPath_cast_right A.orderThreeCentralBaseWhisker
        hoverlap.symm a).symm
  rw [A.orderThreeCentralMeridianAtOverlap_eq_pathTransport,
    A.orderThreeCentralTranslationAtOverlap_eq_pathTransport] at H
  let meridianLoop :=
    ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
      A.orderThreeActualEllipticBoundaryBase
      A.orderThreeActualEllipticBoundaryDeckData.meridian
  let translationLoop :=
    ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
      A.orderThreeActualEllipticBoundaryBase
      (Additive.toMul
        (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))
  let boundaryEq := A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
  have htransportRightMeridian :
      E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop) =
        FundamentalGroup.mapOfEq C.baseMap hoverlap meridianLoop := by
    have ht := fundamentalGroupMulEquivOfEq_mapOfEq_trans C.baseMap hbase hpoint
      meridianLoop
    rw [hcomp] at ht
    exact ht
  have hrightMeridian :
      E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop) =
        FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq boundaryEq meridianLoop) := by
    rw [htransportRightMeridian]
    symm
    exact mapOfEq_fundamentalGroupElementOfBaseEq boundaryEq
      A.orderThreeActualOverlapToCentral hoverlap rfl meridianLoop
  have htransportRightTranslation :
      E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop) =
        FundamentalGroup.mapOfEq C.baseMap hoverlap translationLoop := by
    have ht := fundamentalGroupMulEquivOfEq_mapOfEq_trans C.baseMap hbase hpoint
      translationLoop
    rw [hcomp] at ht
    exact ht
  have hrightTranslation :
      E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop) =
        FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq boundaryEq translationLoop) := by
    rw [htransportRightTranslation]
    symm
    exact mapOfEq_fundamentalGroupElementOfBaseEq boundaryEq
      A.orderThreeActualOverlapToCentral hoverlap rfl translationLoop
  have hcoreMeridian :
      A.orderThreeActualCentralToCoreEquiv
          (E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop)) =
        A.orderThreeActualEllipticPhysicalMeridianToCore := by
    rw [hrightMeridian, ← A.actualEllipticThreeOverlapToCore_eq_central]
    rfl
  have hcoreTranslation :
      A.orderThreeActualCentralToCoreEquiv
          (E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop)) =
        Additive.toMul
          (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon)) := by
    rw [hrightTranslation, ← A.actualEllipticThreeOverlapToCore_eq_central]
    rfl
  have h := H.map (E.trans A.orderThreeActualCentralToCoreEquiv).toMonoidHom
  convert h using 1
  · exact Prod.ext
      (congrArg A.orderThreeActualCentralToCoreEquiv
        (hleftAny A.centralAffineCorePiOneData.rhoOne)).symm
      (congrArg A.orderThreeActualCentralToCoreEquiv
        (hleftAny (Additive.toMul
          (A.centralAffineCorePiOneData.translation (-epsilon))))).symm
  · exact Prod.ext hcoreMeridian.symm hcoreTranslation.symm

/-- Thus the local order-three marked-loop theorem supplies the exact common gauge for the
constructed cusp naturality, with no coherence assumption on the arbitrary central whisker. -/
public theorem OrderThreeCentralMarkedLoopCompatibility.toActualCommonGaugeComparison
    (H : A.OrderThreeCentralMarkedLoopCompatibility) :
    A.OrderThreeCommonGaugeComparison A.actualCuspCentralNaturality := by
  have hcentral :=
    A.actualCuspCentralNaturalityPair_simultaneouslyConjugate_orderThree
      A.centralAffineCorePiOneData.rhoOne
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))
  have hphysical := H.toActualCorePair A
  have h := hcentral.trans hphysical
  exact h

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
