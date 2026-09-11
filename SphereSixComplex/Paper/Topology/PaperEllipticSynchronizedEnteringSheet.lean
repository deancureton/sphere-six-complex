module
public import SphereSixComplex.Paper.Topology.PaperEllipticSynchronizedBaseMarking
public import SphereSixComplex.Paper.Topology.PaperEllipticBoundaryMeridianEndpoint

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
    letI := A.ellipticFourBoundaryAction
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticFourCentralBase} :=
      ⟨A.orderFourCollarRegularRepresentativeMap A.ellipticFourBoundaryBase,
        A.orderFourCollarRegularBase_projects⟩
    let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
      ⟨A.cuspRegularRepresentative,
        A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_cuspCentralBase.symm⟩
    ∃ g : Delta,
      hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (A.orderFourCentralBaseComparisonTracePath H)) ex =
          hp.toPermFiber A.centralAffineBase g ey ∧
      g⁻¹ * g₂ * g = A.geometricCentralClockwiseTwoDeck := by
  let _ := A.ellipticFourBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  let _ := A.ellipticFourBoundaryCover_simplyConnected
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticFourCentralBase} :=
    ⟨A.orderFourCollarRegularRepresentativeMap A.ellipticFourBoundaryBase,
      A.orderFourCollarRegularBase_projects⟩
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_cuspCentralBase.symm⟩
  let W := A.orderFourCentralBaseComparisonTracePath H
  let gamma := Path.Homotopic.Quotient.mk
    (A.ellipticFourBoundaryDeckStraightCentralLoop
      A.ellipticFourBoundaryDeckData.meridian)
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
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo) =
        A.cuspOuterDeckHom A.geometricCentralRhoTwo := by
    exact fundamentalGroupToMulOpposite_fiberBaseEq hp
      ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩
      A.centralAffineBase_eq_cuspCentralBase.symm A.geometricCentralRhoTwo

  rw [hglobal] at ht
  have hi := congrArg Inv.inv ht
  simp only [mul_inv_rev, inv_inv] at hi
  have hi' : (A.cuspOuterDeckHom A.geometricCentralRhoTwo).unop⁻¹ =
      A.geometricCentralClockwiseTwoDeck := by
    unfold geometricCentralClockwiseTwoDeck
    rw [map_inv, MulOpposite.unop_inv]
  rw [hi'] at hi
  simpa only [MulOpposite.unop_op, inv_inv, mul_assoc] using hi.symm

public theorem orderThreeBaseComparisonTrace_enteringSheet
    (H : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1)) :
    letI := A.ellipticThreeBoundaryAction
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticThreeCentralBase} :=
      ⟨A.orderThreeCollarRegularRepresentativeMap A.ellipticThreeBoundaryBase,
        A.orderThreeCollarRegularBase_projects⟩
    let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
      ⟨A.cuspRegularRepresentative,
        A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_cuspCentralBase.symm⟩
    ∃ g : Delta,
      hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (A.orderThreeCentralBaseComparisonTracePath H)) ex =
          hp.toPermFiber A.centralAffineBase g ey ∧
      g⁻¹ * g₁ * g = A.geometricCentralClockwiseOneDeck := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  let _ := A.ellipticThreeBoundaryCover_simplyConnected
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticThreeCentralBase} :=
    ⟨A.orderThreeCollarRegularRepresentativeMap A.ellipticThreeBoundaryBase,
      A.orderThreeCollarRegularBase_projects⟩
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_cuspCentralBase.symm⟩
  let W := A.orderThreeCentralBaseComparisonTracePath H
  let gamma := Path.Homotopic.Quotient.mk
    (A.ellipticThreeBoundaryDeckStraightCentralLoop
      A.ellipticThreeBoundaryDeckData.meridian)
  obtain ⟨g, hg⟩ := hp.exists_toPermFiber_eq ey
    (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk W) ex)
  refine ⟨g, hg.symm, ?_⟩
  have ht := fundamentalGroupToMulOpposite_transport_of_endpoint_sheet
    hp W ex ey g hg.symm gamma
  have heq := A.regularFamilyOuterDeck_eq_of_coordinate_class_eq_at ey _ _
    (A.orderThreeCentralBaseComparisonTrace_first_power H hH)
  have hlocal := A.orderThreeBoundaryMeridian_outerLabel
  change hp.fundamentalGroupToMulOpposite ex gamma = MulOpposite.op g₁⁻¹ at hlocal
  rw [heq, hlocal] at ht
  have hglobal : hp.fundamentalGroupToMulOpposite ey
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne) =
        A.cuspOuterDeckHom A.geometricCentralRhoOne := by
    exact fundamentalGroupToMulOpposite_fiberBaseEq hp
      ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩
      A.centralAffineBase_eq_cuspCentralBase.symm A.geometricCentralRhoOne

  rw [hglobal] at ht
  have hi := congrArg Inv.inv ht
  simp only [mul_inv_rev, inv_inv] at hi
  have hi' : (A.cuspOuterDeckHom A.geometricCentralRhoOne).unop⁻¹ =
      A.geometricCentralClockwiseOneDeck := by
    unfold geometricCentralClockwiseOneDeck
    rw [map_inv, MulOpposite.unop_inv]
  rw [hi'] at hi
  simpa only [MulOpposite.unop_op, inv_inv, mul_assoc] using hi.symm

end SphereSixComplex.Geometry.PaperAnalyticData
