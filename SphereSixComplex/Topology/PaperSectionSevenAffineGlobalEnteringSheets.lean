module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandBasepointReduction

@[expose] public section

namespace SphereSixComplex.Geometry.PaperAnalyticData

noncomputable section
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.Geometry.EllipticHolomorphicLogCover
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover

public theorem regularMovingToFixed_deck_fixedToMoving
    (A : PaperAnalyticData) (g : Delta)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (v : SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace) :
    A.regularMovingToFixed (regularSourceEquiv g b)
      (periodTransport g
        (regularParameterMap A.periods b) (A.regularFixedToMoving b v)) =
      (fullRankDomain
        (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv
        (rhoLambdaReal g
          ((fullRankDomain
            (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv.symm v)) := by
  simp only [regularMovingToFixed, regularFixedToMoving,
    SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization.movingToFixedCover,
    SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization.fixedToMovingCover]
  simp only [regularParameterMap]
  rw [periodTransport_realEquiv]
  change (fullRankDomain _).realEquiv
    ((fullRankDomain (parameterMap A.periods (regularSourceEquiv g b).1)).realEquiv.symm
      ((fullRankDomain _).realEquiv _)) = _
  rw [show parameterMap A.periods (regularSourceEquiv g b).1 =
    SphereSixComplex.Periods.rhoParameters g (parameterMap A.periods b.1) from
    parameterMap_equivariant A.periods g b.1]
  simp

public theorem exists_orderThree_globalEnteringSheet (A : PaperAnalyticData) :
    ∃ g : Delta, ∀ z : sectionSevenAffineVerticalStrip,
      A.OrderThreeDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨g, hg⟩ := A.exists_orderThreeDeckEntersNamedCollarAtStrip
    A.sectionSevenAffineActualCuspCrossingPoint
  exact ⟨g, A.orderThreeDeckEntersNamedCollarAtStrip_of_basepoint g
    A.sectionSevenAffineActualCuspCrossingPoint hg⟩

public theorem exists_orderFour_globalEnteringSheet (A : PaperAnalyticData) :
    ∃ g : Delta, ∀ z : sectionSevenAffineVerticalStrip,
      A.OrderFourDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨g, hg⟩ := A.exists_orderFourDeckEntersNamedCollarAtStrip
    A.sectionSevenAffineActualCuspCrossingPoint
  exact ⟨g, A.orderFourDeckEntersNamedCollarAtStrip_of_basepoint g
    A.sectionSevenAffineActualCuspCrossingPoint hg⟩

public theorem exists_orderThree_globalCollarRepresentative (A : PaperAnalyticData) :
    ∃ g : Delta, ∀ x : A.SectionSevenAffineMarkedBand,
      ∃ q : (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier,
        A.orderThreeOverlapCollarHomeomorph
          (A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x) = Quotient.mk _ q ∧
        orderThreeCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderThree.radius q) =
          regularFamilyDeckMap A.periods g
            (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 := by
  obtain ⟨g, hg⟩ := A.exists_orderThree_globalEnteringSheet
  refine ⟨g, fun x ↦ ?_⟩
  let y := regularFamilyDeckMap A.periods g
    (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1
  let q := (orderThreePrincipalGaugeEquiv A.periods).symm
    (regularFamilyInclusion A.periods y)
  have hb : familyTotalSpaceBase A.periods q =
      (regularTotalSpaceBase A.periods y).1 := by
    rw [← familyTotalSpaceBase_orderThreePrincipalGauge A.periods q]
    change familyTotalSpaceBase A.periods
      (orderThreePrincipalGaugeEquiv A.periods
        ((orderThreePrincipalGaugeEquiv A.periods).symm _)) = _
    rw [Equiv.apply_symm_apply, familyTotalSpaceBase_regularFamilyInclusion]
  have hpos : 0 < orderThreeFamilyRadius A.periods q := by
    rw [orderThreeFamilyRadius.eq_def, hb, norm_pos_iff]
    apply coe_ne_zero_of_ne_center
    intro hc
    have hfixed : (regularTotalSpaceBase A.periods y).1 = fuchsianOneFixedPoint := by
      apply orderThreeCayleyHomeomorph.injective
      simpa [orderThreeCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
        discCenter, orderThreeCayley_fixedPoint] using hc
    have hregular := (regularTotalSpaceBase A.periods y).2
    have hmem := (A.isRegularBasePoint_iff_coordinate_mem _).mp hregular
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.1 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_one)
  have hlt : orderThreeFamilyRadius A.periods q < A.starSeparation.orderThree.radius := by
    rw [orderThreeFamilyRadius.eq_def, hb]
    dsimp only [y]
    rw [regularTotalSpaceBase_familyDeckMap, regularTotalSpaceBase_namedOrderThreeDiscLiftPoint]
    exact hg (A.sectionSevenAffineBandStripCoordinate x)
  let q' : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius).carrier := ⟨q, ⟨hpos, hlt⟩⟩
  have hreg : orderThreeCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius q') = y := by
    apply regularFamilyInclusion_injective A.periods
    rw [regularFamilyInclusion_orderThreeCollarToRegular]
    exact (orderThreePrincipalGaugeEquiv A.periods).apply_symm_apply _
  refine ⟨q', ?_, hreg⟩
  apply (A.starToCentral_isOpenEmbedding (1 : Fin 3)).injective
  rw [A.starToCentral_orderThreeOverlapCollarHomeomorph, A.orderThreeStarToCentral_mk,
    hreg]
  dsimp only [y]
  rw [A.centralQuotientProjection_familyDeckMap,
    A.centralQuotientProjection_namedOrderThreeDiscLiftPoint]
  apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
  apply Subtype.ext
  exact A.sectionSevenAffineOrderThreeDiscOverlapEndpoint_val x

public theorem exists_orderFour_globalCollarRepresentative (A : PaperAnalyticData) :
    ∃ g : Delta, ∀ x : A.SectionSevenAffineMarkedBand,
      ∃ q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier,
        A.orderFourOverlapCollarHomeomorph
          (A.sectionSevenAffineOrderFourDiscOverlapEndpoint x) = Quotient.mk _ q ∧
        orderFourCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderFour.radius q) =
          regularFamilyDeckMap A.periods g
            (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 := by
  obtain ⟨g, hg⟩ := A.exists_orderFour_globalEnteringSheet
  refine ⟨g, fun x ↦ ?_⟩
  let y := regularFamilyDeckMap A.periods g
    (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1
  let q := (orderFourPrincipalGaugeEquiv A.periods).symm
    (regularFamilyInclusion A.periods y)
  have hb : familyTotalSpaceBase A.periods q =
      (regularTotalSpaceBase A.periods y).1 := by
    rw [← familyTotalSpaceBase_orderFourPrincipalGauge A.periods q]
    change familyTotalSpaceBase A.periods
      (orderFourPrincipalGaugeEquiv A.periods
        ((orderFourPrincipalGaugeEquiv A.periods).symm _)) = _
    rw [Equiv.apply_symm_apply, familyTotalSpaceBase_regularFamilyInclusion]
  have hpos : 0 < orderFourFamilyRadius A.periods q := by
    rw [orderFourFamilyRadius.eq_def, hb, norm_pos_iff]
    apply coe_ne_zero_of_ne_center
    intro hc
    have hfixed : (regularTotalSpaceBase A.periods y).1 = fuchsianTwoFixedPoint := by
      apply orderFourCayleyHomeomorph.injective
      simpa [orderFourCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
        discCenter, orderFourCayley_fixedPoint] using hc
    have hregular := (regularTotalSpaceBase A.periods y).2
    have hmem := (A.isRegularBasePoint_iff_coordinate_mem _).mp hregular
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.2 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_two)
  have hlt : orderFourFamilyRadius A.periods q < A.starSeparation.orderFour.radius := by
    rw [orderFourFamilyRadius.eq_def, hb]
    dsimp only [y]
    rw [regularTotalSpaceBase_familyDeckMap, regularTotalSpaceBase_namedDiscLiftPoint]
    exact hg (A.sectionSevenAffineBandStripCoordinate x)
  let q' : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius).carrier := ⟨q, ⟨hpos, hlt⟩⟩
  have hreg : orderFourCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius q') = y := by
    apply regularFamilyInclusion_injective A.periods
    rw [regularFamilyInclusion_orderFourCollarToRegular]
    exact (orderFourPrincipalGaugeEquiv A.periods).apply_symm_apply _
  refine ⟨q', ?_, hreg⟩
  apply (A.starToCentral_isOpenEmbedding (2 : Fin 3)).injective
  rw [A.starToCentral_orderFourOverlapCollarHomeomorph, A.orderFourStarToCentral_mk,
    hreg]
  dsimp only [y]
  rw [A.centralQuotientProjection_familyDeckMap,
    A.centralQuotientProjection_namedDiscLiftPoint]
  apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
  apply Subtype.ext
  exact A.sectionSevenAffineOrderFourDiscOverlapEndpoint_val x

end

end SphereSixComplex.Geometry.PaperAnalyticData
