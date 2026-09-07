module
public import SphereSixComplex.Topology.PaperEllipticOuterDeckCoordinateNaturality
public import SphereSixComplex.Topology.PaperEllipticSynchronizedBaseMarking
public import SphereSixComplex.Topology.PaperEllipticBoundaryMeridianEndpoint

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
variable (A : PaperAnalyticData)

public theorem orderFourBaseComparisonTrace_enteringSheet
    (H : ContinuousMap.Homotopy A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1)) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderFourActualEllipticCentralBase} :=
      ⟨A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase,
        A.orderFourCollarRegularBase_projects⟩
    let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
      ⟨A.actualCuspRegularRepresentative,
        A.actualCuspRegularRepresentative_projects.trans A.centralAffineBase_eq_actualCuspCentralBase.symm⟩
    ∃ g : Delta,
      hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (A.orderFourCentralBaseComparisonTracePath H)) ex =
          hp.toPermFiber A.centralAffineBase g ey ∧
      g⁻¹ * g₂ * g = A.geometricCentralClockwiseTwoDeck := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryCover_simplyConnected
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase,
      A.orderFourCollarRegularBase_projects⟩
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects.trans A.centralAffineBase_eq_actualCuspCentralBase.symm⟩
  let W := A.orderFourCentralBaseComparisonTracePath H
  let gamma := Path.Homotopic.Quotient.mk
    (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
      A.orderFourActualEllipticBoundaryDeckData.meridian)
  obtain ⟨g, hg⟩ := hp.exists_toPermFiber_eq ey
    (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk W) ex)
  refine ⟨g, hg.symm, ?_⟩
  have ht := fundamentalGroupToMulOpposite_transport_of_endpoint_sheet
    hp W ex ey g hg.symm gamma
  have heq := A.regularFamilyOuterDeck_eq_of_coordinate_class_eq_at ey _ _
    (A.orderFourCentralBaseComparisonTrace_first_power H hH)
  have hlocal := A.orderFourBoundaryMeridian_outerLabel
  change hp.fundamentalGroupToMulOpposite ex gamma = MulOpposite.op g₂⁻¹ at hlocal
  rw [heq, hlocal] at ht
  have hglobal : hp.fundamentalGroupToMulOpposite ey
      (A.actualCuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo) =
        A.actualCuspOuterDeckHom A.geometricCentralRhoTwo := by
    exact fundamentalGroupToMulOpposite_fiberBaseEq hp
      ⟨A.actualCuspRegularRepresentative, A.actualCuspRegularRepresentative_projects⟩
      A.centralAffineBase_eq_actualCuspCentralBase.symm A.geometricCentralRhoTwo

  rw [hglobal] at ht
  have hi := congrArg Inv.inv ht
  simp only [mul_inv_rev, inv_inv] at hi
  have hi' : (A.actualCuspOuterDeckHom A.geometricCentralRhoTwo).unop⁻¹ =
      A.geometricCentralClockwiseTwoDeck := by
    unfold geometricCentralClockwiseTwoDeck
    rw [map_inv, MulOpposite.unop_inv]
  rw [hi'] at hi
  simpa only [MulOpposite.unop_op, inv_inv, mul_assoc] using hi.symm

end SphereSixComplex.Geometry.PaperAnalyticData
