module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedMeridianLifts

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

public noncomputable def sectionSevenAffinePeripheralMidpointTotal (A : PaperAnalyticData) :
    (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.centralZeroSection A.markedPuncturedBasepoint} := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.isCoveringMap.monodromy
    (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralWhisker).symm
    ⟨A.actualCuspRegularRepresentative, A.actualCuspRegularRepresentative_projects⟩

public theorem sectionSevenAffinePeripheralMidpointTotal_transport (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralWhisker)
      A.sectionSevenAffinePeripheralMidpointTotal =
        ⟨A.actualCuspRegularRepresentative, A.actualCuspRegularRepresentative_projects⟩ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  change hp.isCoveringMap.monodromy
    (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralWhisker)
    (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralWhisker).symm
      ⟨A.actualCuspRegularRepresentative, A.actualCuspRegularRepresentative_projects⟩) = _
  rw [← hp.isCoveringMap.monodromy_trans_apply]
  simp only [Path.Homotopic.Quotient.symm_trans, hp.isCoveringMap.monodromy_refl]
  rfl

public noncomputable def sectionSevenAffineNormalizedMidpointTotal (A : PaperAnalyticData) :
    (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.centralZeroSection A.markedPuncturedBasepoint} := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.toPermFiber _ (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    A.sectionSevenAffinePeripheralMidpointTotal

public theorem sectionSevenAffineNormalizedMidpointTotal_label (A : PaperAnalyticData)
    (γ : FundamentalGroup A.CentralFamily (A.centralZeroSection A.markedPuncturedBasepoint)) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.sectionSevenAffineNormalizedMidpointTotal γ).unop =
      ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
        (A.actualCuspOuterDeckHom (A.markedCentralToActualCuspEquiv γ)).unop *
        (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have ht := fundamentalGroupToMulOpposite_transport_endpoint hp
    A.actualCuspMarkedCentralWhisker A.sectionSevenAffinePeripheralMidpointTotal γ
  rw [A.sectionSevenAffinePeripheralMidpointTotal_transport] at ht
  change (hp.fundamentalGroupToMulOpposite
    (hp.toPermFiber _ (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      A.sectionSevenAffinePeripheralMidpointTotal) γ).unop = _
  rw [fundamentalGroupToMulOpposite_change_sheet]
  simp only [MulOpposite.unop_op, inv_inv]
  rw [← ht]
  rfl

public theorem sectionSevenAffineNormalizedMidpointTotal_zero_label (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.sectionSevenAffineNormalizedMidpointTotal
      A.markedZeroCentralMeridianClass).unop = g₁ := by
  refine (A.sectionSevenAffineNormalizedMidpointTotal_label A.markedZeroCentralMeridianClass).trans ?_
  have hγ : A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass =
      A.geometricCentralRhoOne⁻¹ := by
    simp only [geometricCentralRhoOne, map_inv, inv_inv]
  rw [hγ]
  change ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
    A.geometricCentralClockwiseOneDeck *
    (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent = g₁
  rw [A.geometricCentralClockwiseOneDeck_eq_cuspConjugate]
  group

public theorem sectionSevenAffineNormalizedMidpointTotal_one_label (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.sectionSevenAffineNormalizedMidpointTotal
      A.markedOneCentralMeridianClass).unop = g₂ := by
  refine (A.sectionSevenAffineNormalizedMidpointTotal_label A.markedOneCentralMeridianClass).trans ?_
  have hγ : A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass =
      A.geometricCentralRhoTwo⁻¹ := by
    simp only [geometricCentralRhoTwo, map_inv, inv_inv]
  rw [hγ]
  change ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
    A.geometricCentralClockwiseTwoDeck *
    (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent = g₂
  rw [A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate]
  group

public noncomputable def sectionSevenAffineNormalizedMidpoint (A : PaperAnalyticData) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    (regularTotalSpaceBase A.periods A.sectionSevenAffinePeripheralMidpointTotal.val)

public theorem sectionSevenAffineNormalizedMidpoint_projects (A : PaperAnalyticData) :
    A.regularCoordinate A.sectionSevenAffineNormalizedMidpoint =
      twicePuncturedComplexBasepoint := by
  unfold sectionSevenAffineNormalizedMidpoint
  change A.regularCoordinate
    (SphereSixComplex.Geometry.EquivariantQuotientHomeomorph.actionMap A.regularBaseDeckAction
      (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      (regularTotalSpaceBase A.periods A.sectionSevenAffinePeripheralMidpointTotal.val)) = _
  rw [A.regularCoordinate_deck_invariant]
  rw [← A.centralFamilyCoordinate_centralQuotientProjection]
  rw [show A.centralQuotientProjection A.sectionSevenAffinePeripheralMidpointTotal.val =
    A.centralZeroSection A.markedPuncturedBasepoint from
    A.sectionSevenAffinePeripheralMidpointTotal.property]
  rw [A.centralFamilyCoordinate_zeroSection]
  simp [markedPuncturedBasepoint]

public noncomputable def sectionSevenAffineNormalizedStripContinuousLift (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    sectionSevenAffineStripMidpoint A.sectionSevenAffineNormalizedMidpoint
    A.sectionSevenAffineNormalizedMidpoint_projects).choose

public theorem sectionSevenAffineNormalizedStripContinuousLift_midpoint (A : PaperAnalyticData) :
    A.sectionSevenAffineNormalizedStripContinuousLift sectionSevenAffineStripMidpoint =
      A.sectionSevenAffineNormalizedMidpoint :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    sectionSevenAffineStripMidpoint A.sectionSevenAffineNormalizedMidpoint
    A.sectionSevenAffineNormalizedMidpoint_projects).choose_spec.1.1

public theorem sectionSevenAffineNormalizedStripContinuousLift_coordinate (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.sectionSevenAffineNormalizedStripContinuousLift = stripInclusion :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    sectionSevenAffineStripMidpoint A.sectionSevenAffineNormalizedMidpoint
    A.sectionSevenAffineNormalizedMidpoint_projects).choose_spec.1.2

end SphereSixComplex.Geometry.PaperAnalyticData
