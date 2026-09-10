module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineStripMidpoint
public import SphereSixComplex.Paper.Topology.PaperEllipticOuterDeckCoordinateNaturality

@[expose] public section
noncomputable section

namespace SphereSixComplex

public theorem quotientCover_fundamentalGroupToMulOpposite_naturality_at
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (D : QuotientCoverMapData (G := G) (H := H) p q) {x : X}
    (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (MonoidHom.op D.deckMap) (hp.fundamentalGroupToMulOpposite e γ) =
      hq.fundamentalGroupToMulOpposite
        ⟨D.lift e.val, (D.commutes e.val).symm.trans (congrArg D.baseMap e.property)⟩
        (FundamentalGroup.map D.baseMap x γ) := by
  obtain ⟨e, he⟩ := e
  change p e = x at he
  cases he
  have h := quotientCover_fundamentalGroupToMulOpposite_naturality hp hq D e γ
  have hc := fundamentalGroupToMulOpposite_fiberBaseEq hq ⟨D.lift e, rfl⟩
    (D.commutes e).symm (FundamentalGroup.mapOfEq D.baseMap (D.commutes e) γ)
  simp only [Topology.fundamentalGroupMulEquivOfEq_apply,
    FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl] at hc
  simp only [FundamentalGroup.mapOfEq_apply] at h
  simpa only [FundamentalGroup.map_apply] using h.trans hc.symm

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

public noncomputable def affinePeripheralMidpointTotal (A : PaperAnalyticData) :
    (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.centralZeroSection A.markedPuncturedBasepoint} := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.isCoveringMap.monodromy
    (Path.Homotopic.Quotient.mk A.cuspMarkedCentralWhisker).symm
    ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩

public theorem affinePeripheralMidpointTotal_transport (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.cuspMarkedCentralWhisker)
      A.affinePeripheralMidpointTotal =
        ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  change hp.isCoveringMap.monodromy
    (Path.Homotopic.Quotient.mk A.cuspMarkedCentralWhisker)
    (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.cuspMarkedCentralWhisker).symm
      ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩) = _
  rw [← hp.isCoveringMap.monodromy_trans_apply]
  simp only [Path.Homotopic.Quotient.symm_trans, hp.isCoveringMap.monodromy_refl]
  rfl

public noncomputable def affineNormalizedMidpointTotal (A : PaperAnalyticData) :
    (regularFamilyQuotientMap A.periods) ⁻¹'
      {A.centralZeroSection A.markedPuncturedBasepoint} := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.toPermFiber _ (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    A.affinePeripheralMidpointTotal

public theorem affineNormalizedMidpointTotal_label (A : PaperAnalyticData)
    (γ : FundamentalGroup A.CentralFamily (A.centralZeroSection A.markedPuncturedBasepoint)) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.affineNormalizedMidpointTotal γ).unop =
      ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
        (A.cuspOuterDeckHom (A.markedCentralToActualCuspEquiv γ)).unop *
        (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  have ht := fundamentalGroupToMulOpposite_transport_endpoint hp
    A.cuspMarkedCentralWhisker A.affinePeripheralMidpointTotal γ
  rw [A.affinePeripheralMidpointTotal_transport] at ht
  change (hp.fundamentalGroupToMulOpposite
    (hp.toPermFiber _ (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      A.affinePeripheralMidpointTotal) γ).unop = _
  rw [fundamentalGroupToMulOpposite_change_sheet]
  simp only [MulOpposite.unop_op, inv_inv]
  rw [← ht]
  rfl

public theorem affineNormalizedMidpointTotal_zero_label (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.affineNormalizedMidpointTotal
      A.markedZeroCentralMeridianClass).unop = g₁ := by
  refine (A.affineNormalizedMidpointTotal_label A.markedZeroCentralMeridianClass).trans ?_
  have hγ : A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass =
      A.geometricCentralRhoOne⁻¹ := by
    simp only [geometricCentralRhoOne, map_inv, inv_inv]
  rw [hγ]
  change ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
    A.geometricCentralClockwiseOneDeck *
    (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent = g₁
  rw [A.geometricCentralClockwiseOneDeck_eq_cuspConjugate]
  group

public theorem affineNormalizedMidpointTotal_one_label (A : PaperAnalyticData) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    (hp.fundamentalGroupToMulOpposite A.affineNormalizedMidpointTotal
      A.markedOneCentralMeridianClass).unop = g₂ := by
  refine (A.affineNormalizedMidpointTotal_label A.markedOneCentralMeridianClass).trans ?_
  have hγ : A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass =
      A.geometricCentralRhoTwo⁻¹ := by
    simp only [geometricCentralRhoTwo, map_inv, inv_inv]
  rw [hγ]
  change ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ *
    A.geometricCentralClockwiseTwoDeck *
    (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent = g₂
  rw [A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate]
  group

public noncomputable def affineNormalizedMidpoint (A : PaperAnalyticData) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    (regularTotalSpaceBase A.periods A.affinePeripheralMidpointTotal.val)

public theorem affineNormalizedMidpointTotal_base (A : PaperAnalyticData) :
    regularTotalSpaceBase A.periods A.affineNormalizedMidpointTotal.val =
      A.affineNormalizedMidpoint := by
  change regularTotalSpaceBase A.periods
    (regularFamilyDeckMap A.periods
      (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      A.affinePeripheralMidpointTotal.val) = _
  exact regularTotalSpaceBase_familyDeckMap A.periods _ _

public theorem exists_affineNormalizedCuspPath (A : PaperAnalyticData) :
    ∃ L : Path A.affineNormalizedMidpoint
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.cuspRegularRepresentative)),
      ∀ t, A.regularCoordinate (L t) =
        A.centralFamilyCoordinate (A.cuspMarkedCentralWhisker t) := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.cuspCentralBase} :=
    ⟨A.cuspRegularRepresentative, A.cuspRegularRepresentative_projects⟩
  let ey' := hp.toPermFiber _ q⁻¹ ey
  have ht : hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.cuspMarkedCentralWhisker)
      A.affineNormalizedMidpointTotal = ey' := by
    change hp.isCoveringMap.monodromy _
      (hp.toPermFiber _ q⁻¹ A.affinePeripheralMidpointTotal) = _
    rw [hp.monodromy_toPermFiber, A.affinePeripheralMidpointTotal_transport]
  obtain ⟨Q, hQ⟩ := hp.isCoveringMap.exists_path_lift_of_monodromy_eq
    A.cuspMarkedCentralWhisker A.affineNormalizedMidpointTotal ey' ht
  let L := (Q.map (regularTotalSpaceBase_continuous A.periods)).cast
    A.affineNormalizedMidpointTotal_base.symm
    (regularTotalSpaceBase_familyDeckMap A.periods q⁻¹ A.cuspRegularRepresentative).symm
  refine ⟨L, fun t ↦ ?_⟩
  change A.regularCoordinate (regularTotalSpaceBase A.periods (Q t)) = _
  rw [← A.centralFamilyCoordinate_centralQuotientProjection]
  exact congrArg A.centralFamilyCoordinate (congrArg (fun p : Path _ _ ↦ p t) hQ)

public noncomputable def affineNormalizedCuspPath (A : PaperAnalyticData) :
    Path A.affineNormalizedMidpoint
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.cuspRegularRepresentative)) :=
  A.exists_affineNormalizedCuspPath.choose

public theorem affineNormalizedCuspPath_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.affineNormalizedCuspPath t) =
      A.centralFamilyCoordinate (A.cuspMarkedCentralWhisker t) :=
  A.exists_affineNormalizedCuspPath.choose_spec t

public theorem affineNormalizedMidpoint_projects (A : PaperAnalyticData) :
    A.regularCoordinate A.affineNormalizedMidpoint =
      twicePuncturedComplexBasepoint := by
  unfold affineNormalizedMidpoint
  change A.regularCoordinate
    (SphereSixComplex.Geometry.EquivariantQuotientHomeomorph.actionMap A.regularBaseDeckAction
      (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      (regularTotalSpaceBase A.periods A.affinePeripheralMidpointTotal.val)) = _
  rw [A.regularCoordinate_deck_invariant]
  rw [← A.centralFamilyCoordinate_centralQuotientProjection]
  rw [show A.centralQuotientProjection A.affinePeripheralMidpointTotal.val =
    A.centralZeroSection A.markedPuncturedBasepoint from
    A.affinePeripheralMidpointTotal.property]
  rw [A.centralFamilyCoordinate_zeroSection]
  simp [markedPuncturedBasepoint]

public theorem affineMarkedCentralCoordinate_base (A : PaperAnalyticData) :
    A.centralFamilyCoordinate (A.centralZeroSection A.markedPuncturedBasepoint) =
      twicePuncturedComplexBasepoint := by
  rw [A.centralFamilyCoordinate_zeroSection]
  simp [markedPuncturedBasepoint]

public noncomputable def affineNormalizedBaseDeckHom (A : PaperAnalyticData) :
    FundamentalGroup regularCoordinateBase twicePuncturedComplexBasepoint →* Deltaᵐᵒᵖ := by
  let _ := A.regularBaseDeckAction
  exact A.regularCoordinate_isQuotientCoveringMap.fundamentalGroupToMulOpposite
    ⟨A.affineNormalizedMidpoint, A.affineNormalizedMidpoint_projects⟩

public theorem affineNormalizedBaseDeckHom_coordinate (A : PaperAnalyticData)
    (γ : FundamentalGroup A.CentralFamily (A.centralZeroSection A.markedPuncturedBasepoint)) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite A.affineNormalizedMidpointTotal γ =
      A.affineNormalizedBaseDeckHom
        (FundamentalGroup.mapOfEq
          ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
          A.affineMarkedCentralCoordinate_base γ) := by
  let _ := regularFamilyDeckAction A.periods
  let _ := A.regularBaseDeckAction
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let hq := A.regularCoordinate_isQuotientCoveringMap
  let D : QuotientCoverMapData
      (G := Delta) (H := Delta) (regularFamilyQuotientMap A.periods)
      ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩ := {
    baseMap := ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
    lift := ⟨regularTotalSpaceBase A.periods, regularTotalSpaceBase_continuous A.periods⟩
    deckMap := MonoidHom.id Delta
    commutes := fun z ↦ A.centralFamilyCoordinate_centralQuotientProjection z
    equivariant := fun g z ↦ regularTotalSpaceBase_familyDeckMap A.periods g z }
  let e := A.affineNormalizedMidpointTotal
  have h := quotientCover_fundamentalGroupToMulOpposite_naturality_at hp hq D e γ
  let be : A.regularCoordinate ⁻¹'
      {A.centralFamilyCoordinate (A.centralZeroSection A.markedPuncturedBasepoint)} :=
    ⟨regularTotalSpaceBase A.periods e.val,
      (D.commutes e.val).symm.trans (congrArg D.baseMap e.property)⟩
  have hc := fundamentalGroupToMulOpposite_fiberBaseEq
    (p := ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩)
    hq be A.affineMarkedCentralCoordinate_base
    (FundamentalGroup.map D.baseMap _ γ)
  have hc' : A.affineNormalizedBaseDeckHom
      (FundamentalGroup.mapOfEq
        ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
        A.affineMarkedCentralCoordinate_base γ) =
        hq.fundamentalGroupToMulOpposite be (FundamentalGroup.map D.baseMap _ γ) := by
    simpa only [Topology.fundamentalGroupMulEquivOfEq_apply,
      FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      affineNormalizedBaseDeckHom, be, e, D,
      affineNormalizedMidpointTotal_base] using hc
  exact h.trans hc'.symm

public theorem affineNormalizedBaseDeckHom_zero (A : PaperAnalyticData) :
    (A.affineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridian)).unop = g₁ := by
  have h := A.affineNormalizedBaseDeckHom_coordinate A.markedZeroCentralMeridianClass
  have hm : FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.affineMarkedCentralCoordinate_base A.markedZeroCentralMeridianClass =
        Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridian := by
    rw [A.markedZeroCentralMeridianClass_eq_pathLoopClass, FundamentalGroup.mapOfEq_apply]
    unfold markedZeroCentralMeridian markedZeroBaseMeridian
    rw [← Path.Homotopic.Quotient.mk_map]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    change A.centralFamilyCoordinate
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (twicePuncturedClockwiseZeroMeridian t))) = _
    rw [A.centralFamilyCoordinate_zeroSection]
    exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _
  rw [hm] at h
  exact (congrArg MulOpposite.unop h.symm).trans A.affineNormalizedMidpointTotal_zero_label

public theorem affineNormalizedBaseDeckHom_one (A : PaperAnalyticData) :
    (A.affineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridian)).unop = g₂ := by
  have h := A.affineNormalizedBaseDeckHom_coordinate A.markedOneCentralMeridianClass
  have hm : FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.affineMarkedCentralCoordinate_base A.markedOneCentralMeridianClass =
        Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridian := by
    rw [A.markedOneCentralMeridianClass_eq_pathLoopClass, FundamentalGroup.mapOfEq_apply]
    unfold markedOneCentralMeridian markedOneBaseMeridian
    rw [← Path.Homotopic.Quotient.mk_map]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    change A.centralFamilyCoordinate
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (twicePuncturedClockwiseOneMeridian t))) = _
    rw [A.centralFamilyCoordinate_zeroSection]
    exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _
  rw [hm] at h
  exact (congrArg MulOpposite.unop h.symm).trans A.affineNormalizedMidpointTotal_one_label

public theorem exists_sectionSevenAffineNormalizedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) (g : Delta)
    (hg : (A.affineNormalizedBaseDeckHom (Path.Homotopic.Quotient.mk γ)).unop = g) :
    ∃ L : Path A.affineNormalizedMidpoint
      (regularSourceEquiv g A.affineNormalizedMidpoint),
      ∀ t, A.regularCoordinate (L t) = γ t := by
  let _ := A.regularBaseDeckAction
  let hp := A.regularCoordinate_isQuotientCoveringMap
  let e : A.regularCoordinate ⁻¹' {twicePuncturedComplexBasepoint} :=
    ⟨A.affineNormalizedMidpoint, A.affineNormalizedMidpoint_projects⟩
  let e' := hp.toPermFiber _ g e
  have hm : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e = e' := by
    apply Subtype.ext
    have h := hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := Path.Homotopic.Quotient.mk γ)
    change (A.affineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk γ)).unop • e.val = _ at h
    rw [hg] at h
    exact h.symm
  let p : C(RegularBase (U := A.modular.modularParameter.toTriangleUniformization),
      regularCoordinateBase) :=
    ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩
  obtain ⟨L, hL⟩ := IsCoveringMap.exists_path_lift_of_monodromy_eq
    (p := p) hp.isCoveringMap γ e e' hm
  exact ⟨L, fun t ↦ congrArg (fun p : Path _ _ ↦ p t) hL⟩

public noncomputable def affineNormalizedZeroLift (A : PaperAnalyticData) :
    Path A.affineNormalizedMidpoint
      (regularSourceEquiv g₁ A.affineNormalizedMidpoint) :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseZeroMeridian g₁
    A.affineNormalizedBaseDeckHom_zero).choose

public theorem affineNormalizedZeroLift_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.affineNormalizedZeroLift t) =
      twicePuncturedClockwiseZeroMeridian t :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseZeroMeridian g₁
    A.affineNormalizedBaseDeckHom_zero).choose_spec t

public noncomputable def affineNormalizedOneLift (A : PaperAnalyticData) :
    Path A.affineNormalizedMidpoint
      (regularSourceEquiv g₂ A.affineNormalizedMidpoint) :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseOneMeridian g₂
    A.affineNormalizedBaseDeckHom_one).choose

public theorem affineNormalizedOneLift_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.affineNormalizedOneLift t) =
      twicePuncturedClockwiseOneMeridian t :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseOneMeridian g₂
    A.affineNormalizedBaseDeckHom_one).choose_spec t

public noncomputable def affineNormalizedStripContinuousLift (A : PaperAnalyticData) :
    C(affineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    affineStripMidpoint A.affineNormalizedMidpoint
    A.affineNormalizedMidpoint_projects).choose

public theorem affineNormalizedStripContinuousLift_midpoint (A : PaperAnalyticData) :
    A.affineNormalizedStripContinuousLift affineStripMidpoint =
      A.affineNormalizedMidpoint :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    affineStripMidpoint A.affineNormalizedMidpoint
    A.affineNormalizedMidpoint_projects).choose_spec.1.1

public theorem affineNormalizedStripContinuousLift_coordinate (A : PaperAnalyticData) :
    A.regularCoordinate ∘ A.affineNormalizedStripContinuousLift = stripInclusion :=
  (A.existsUnique_sectionSevenAffineStripContinuousLift
    affineStripMidpoint A.affineNormalizedMidpoint
    A.affineNormalizedMidpoint_projects).choose_spec.1.2

public noncomputable def affineNormalizedStripLift (A : PaperAnalyticData) :
    A.AffineStripLift where
  lift := A.affineNormalizedStripContinuousLift
  lift_coordinate z := congrArg Subtype.val
    (congrFun A.affineNormalizedStripContinuousLift_coordinate z)

end SphereSixComplex.Geometry.PaperAnalyticData
