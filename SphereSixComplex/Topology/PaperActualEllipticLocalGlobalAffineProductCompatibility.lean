module

public import SphereSixComplex.Topology.PaperActualEllipticCentralCoverProductLiftComparison

/-!
# Local/global affine product compatibility at the elliptic collars

The local Cayley and principal-gauge calculations live in the regular torus-family cover,
whereas the canonical affine presentation is based at the selected cusp point of the global
quotient.  This file isolates the stronger point-set residue joining those descriptions: a
representative of the globally based presentation whose whiskering by the prescribed geometric
connector is literally the projected local regular loop.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- A globally based loop representative, whiskered to the order-three elliptic base by the
prescribed geometric connector. -/
public noncomputable def orderThreeWhiskeredGlobalAffineProductLoop
    (gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase) :
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase :=
  A.orderThreeActualCentralProductConnector.symm.trans
    (gamma.trans A.orderThreeActualCentralProductConnector)

/-- The order-four analogue of the whiskered global affine-product loop. -/
public noncomputable def orderFourWhiskeredGlobalAffineProductLoop
    (gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase) :
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase :=
  A.orderFourActualCentralProductConnector.symm.trans
    (gamma.trans A.orderFourActualCentralProductConnector)

/-- Strong point-set form of the remaining order-three local/global comparison.  The witness is
an actual representative of the canonical affine-presentation class, and the conclusion is an
equality of paths rather than merely an equality of their homotopy classes. -/
public def OrderThreeActualEllipticLocalGlobalAffineProductCompatibility : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let localLoop :=
    (A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm
  ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase,
    Path.Homotopic.Quotient.mk gamma =
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderThreeFillingRelationClassifiedCentralProductDeck).toPath ∧
      localLoop = A.orderThreeWhiskeredGlobalAffineProductLoop gamma

/-- Strong point-set form of the remaining order-four local/global comparison. -/
public def OrderFourActualEllipticLocalGlobalAffineProductCompatibility : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  let localLoop :=
    (A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm
  ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase,
    Path.Homotopic.Quotient.mk gamma =
        (paperPuncturedGlobalFamilyAffinePresentation A
          orderFourFillingRelationClassifiedCentralProductDeck).toPath ∧
      localLoop = A.orderFourWhiskeredGlobalAffineProductLoop gamma

/-- The strong order-three point-set compatibility transports the local Cayley--gauge product
coordinate all the way to a connector-whiskered representative of the global affine
presentation. -/
public theorem OrderThreeActualEllipticLocalGlobalAffineProductCompatibility.coordinate
    (h : A.OrderThreeActualEllipticLocalGlobalAffineProductCompatibility) :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase,
      Path.Homotopic.Quotient.mk gamma =
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck).toPath ∧
        ∀ t : unitInterval,
          (((orderThreeCayleyHomeomorph
                (familyTotalSpaceBase A.periods
                  (A.orderThreeCollarInverseRepresentative
                    (A.orderThreeActualEllipticBoundaryDeckStraightLift
                      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)).1) :
                  ComplexUnitDisc) : ℂ),
            (orderThreeRealPeriodProductHomeomorph A.periods
              (regularFamilyInclusion A.periods
                (A.orderThreeFillingRelationRegularLoop t))).2) =
              ((A.orderThreeFillingRelationCayleyLoop t).1,
                A.orderThreeFillingRelationPrincipalGaugeLoop t +
                  Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2) ∧
            ((A.orderThreeFillingRelationRegularLoop.map
                A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
                  A.orderThreeCollarRegularRepresentative_base_projects.symm
                  A.orderThreeCollarRegularRepresentative_base_projects.symm) t =
              A.orderThreeWhiskeredGlobalAffineProductLoop gamma t := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  change ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase, _ ∧ _ at h
  obtain ⟨gamma, hgamma, hloop⟩ := h
  refine ⟨gamma, hgamma, fun t ↦
    ⟨A.orderThreeFillingRelationRegularLoop_localProductCoordinate t,
      congrFun (congrArg DFunLike.coe hloop) t⟩⟩

/-- The corresponding order-four pointwise transport. -/
public theorem OrderFourActualEllipticLocalGlobalAffineProductCompatibility.coordinate
    (h : A.OrderFourActualEllipticLocalGlobalAffineProductCompatibility) :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase,
      Path.Homotopic.Quotient.mk gamma =
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck).toPath ∧
        ∀ t : unitInterval,
          (((orderFourCayleyHomeomorph
                (familyTotalSpaceBase A.periods
                  (A.orderFourCollarInverseRepresentative
                    (A.orderFourActualEllipticBoundaryDeckStraightLift
                      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)).1) :
                  ComplexUnitDisc) : ℂ),
            (orderFourRealPeriodProductHomeomorph A.periods
              (regularFamilyInclusion A.periods
                (A.orderFourFillingRelationRegularLoop t))).2) =
              ((A.orderFourFillingRelationCayleyLoop t).1,
                A.orderFourFillingRelationPrincipalGaugeLoop t +
                  Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2) ∧
            ((A.orderFourFillingRelationRegularLoop.map
                A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
                  A.orderFourCollarRegularRepresentative_base_projects.symm
                  A.orderFourCollarRegularRepresentative_base_projects.symm) t =
              A.orderFourWhiskeredGlobalAffineProductLoop gamma t := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase, _ ∧ _ at h
  obtain ⟨gamma, hgamma, hloop⟩ := h
  refine ⟨gamma, hgamma, fun t ↦
    ⟨A.orderFourFillingRelationRegularLoop_localProductCoordinate t,
      congrFun (congrArg DFunLike.coe hloop) t⟩⟩

/-- The stronger order-three point-set residue implies the universal-cover product-lift
comparison. -/
public theorem OrderThreeActualEllipticLocalGlobalAffineProductCompatibility.toCoverComparison
    (h : A.OrderThreeActualEllipticLocalGlobalAffineProductCompatibility) :
    A.OrderThreeActualEllipticCentralCoverProductLiftComparison := by
  rw [A.orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity]
  let _ := A.orderThreeActualEllipticBoundaryAction
  change ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase, _ ∧ _ at h
  obtain ⟨gamma, hgamma, hloop⟩ := h
  change Path.Homotopic.Quotient.mk _ = _
  rw [hloop]
  unfold orderThreeWhiskeredGlobalAffineProductLoop
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderThreeActualCentralProductConnector _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rw [hgamma]
  rfl

/-- The stronger order-four point-set residue likewise implies the product-lift comparison. -/
public theorem OrderFourActualEllipticLocalGlobalAffineProductCompatibility.toCoverComparison
    (h : A.OrderFourActualEllipticLocalGlobalAffineProductCompatibility) :
    A.OrderFourActualEllipticCentralCoverProductLiftComparison := by
  rw [A.orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity]
  let _ := A.orderFourActualEllipticBoundaryAction
  change ∃ gamma : Path A.actualCuspCentralBase A.actualCuspCentralBase, _ ∧ _ at h
  obtain ⟨gamma, hgamma, hloop⟩ := h
  change Path.Homotopic.Quotient.mk _ = _
  rw [hloop]
  unfold orderFourWhiskeredGlobalAffineProductLoop
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderFourActualCentralProductConnector _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rw [hgamma]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
