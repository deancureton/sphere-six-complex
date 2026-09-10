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

public theorem sectionSevenAffineNormalizedMidpointTotal_base (A : PaperAnalyticData) :
    regularTotalSpaceBase A.periods A.sectionSevenAffineNormalizedMidpointTotal.val =
      A.sectionSevenAffineNormalizedMidpoint := by
  change regularTotalSpaceBase A.periods
    (regularFamilyDeckMap A.periods
      (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      A.sectionSevenAffinePeripheralMidpointTotal.val) = _
  exact regularTotalSpaceBase_familyDeckMap A.periods _ _

public theorem exists_sectionSevenAffineNormalizedCuspPath (A : PaperAnalyticData) :
    ∃ L : Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.actualCuspRegularRepresentative)),
      ∀ t, A.regularCoordinate (L t) =
        A.centralFamilyCoordinate (A.actualCuspMarkedCentralWhisker t) := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.actualCuspCentralBase} :=
    ⟨A.actualCuspRegularRepresentative, A.actualCuspRegularRepresentative_projects⟩
  let ey' := hp.toPermFiber _ q⁻¹ ey
  have ht : hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralWhisker)
      A.sectionSevenAffineNormalizedMidpointTotal = ey' := by
    change hp.isCoveringMap.monodromy _
      (hp.toPermFiber _ q⁻¹ A.sectionSevenAffinePeripheralMidpointTotal) = _
    rw [hp.monodromy_toPermFiber, A.sectionSevenAffinePeripheralMidpointTotal_transport]
  obtain ⟨Q, hQ⟩ := hp.isCoveringMap.exists_path_lift_of_monodromy_eq
    A.actualCuspMarkedCentralWhisker A.sectionSevenAffineNormalizedMidpointTotal ey' ht
  let L := (Q.map (regularTotalSpaceBase_continuous A.periods)).cast
    A.sectionSevenAffineNormalizedMidpointTotal_base.symm
    (regularTotalSpaceBase_familyDeckMap A.periods q⁻¹ A.actualCuspRegularRepresentative).symm
  refine ⟨L, fun t ↦ ?_⟩
  change A.regularCoordinate (regularTotalSpaceBase A.periods (Q t)) = _
  rw [← A.centralFamilyCoordinate_centralQuotientProjection]
  exact congrArg A.centralFamilyCoordinate (congrArg (fun p : Path _ _ ↦ p t) hQ)

public noncomputable def sectionSevenAffineNormalizedCuspPath (A : PaperAnalyticData) :
    Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.actualCuspRegularRepresentative)) :=
  A.exists_sectionSevenAffineNormalizedCuspPath.choose

public theorem sectionSevenAffineNormalizedCuspPath_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.sectionSevenAffineNormalizedCuspPath t) =
      A.centralFamilyCoordinate (A.actualCuspMarkedCentralWhisker t) :=
  A.exists_sectionSevenAffineNormalizedCuspPath.choose_spec t

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

public theorem sectionSevenAffineMarkedCentralCoordinate_base (A : PaperAnalyticData) :
    A.centralFamilyCoordinate (A.centralZeroSection A.markedPuncturedBasepoint) =
      twicePuncturedComplexBasepoint := by
  rw [A.centralFamilyCoordinate_zeroSection]
  simp [markedPuncturedBasepoint]

public noncomputable def sectionSevenAffineNormalizedBaseDeckHom (A : PaperAnalyticData) :
    FundamentalGroup RegularCoordinateBase twicePuncturedComplexBasepoint →* Deltaᵐᵒᵖ := by
  let _ := A.regularBaseDeckAction
  exact A.regularCoordinate_isQuotientCoveringMap.fundamentalGroupToMulOpposite
    ⟨A.sectionSevenAffineNormalizedMidpoint, A.sectionSevenAffineNormalizedMidpoint_projects⟩

public theorem sectionSevenAffineNormalizedBaseDeckHom_coordinate (A : PaperAnalyticData)
    (γ : FundamentalGroup A.CentralFamily (A.centralZeroSection A.markedPuncturedBasepoint)) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite A.sectionSevenAffineNormalizedMidpointTotal γ =
      A.sectionSevenAffineNormalizedBaseDeckHom
        (FundamentalGroup.mapOfEq
          ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
          A.sectionSevenAffineMarkedCentralCoordinate_base γ) := by
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
  let e := A.sectionSevenAffineNormalizedMidpointTotal
  have h := quotientCover_fundamentalGroupToMulOpposite_naturality_at hp hq D e γ
  let be : A.regularCoordinate ⁻¹'
      {A.centralFamilyCoordinate (A.centralZeroSection A.markedPuncturedBasepoint)} :=
    ⟨regularTotalSpaceBase A.periods e.val,
      (D.commutes e.val).symm.trans (congrArg D.baseMap e.property)⟩
  have hc := fundamentalGroupToMulOpposite_fiberBaseEq
    (p := ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩)
    hq be A.sectionSevenAffineMarkedCentralCoordinate_base
    (FundamentalGroup.map D.baseMap _ γ)
  have hc' : A.sectionSevenAffineNormalizedBaseDeckHom
      (FundamentalGroup.mapOfEq
        ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
        A.sectionSevenAffineMarkedCentralCoordinate_base γ) =
        hq.fundamentalGroupToMulOpposite be (FundamentalGroup.map D.baseMap _ γ) := by
    simpa only [Topology.fundamentalGroupMulEquivOfEq_apply,
      FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      sectionSevenAffineNormalizedBaseDeckHom, be, e, D,
      sectionSevenAffineNormalizedMidpointTotal_base] using hc
  exact h.trans hc'.symm

public theorem sectionSevenAffineNormalizedBaseDeckHom_zero (A : PaperAnalyticData) :
    (A.sectionSevenAffineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridian)).unop = g₁ := by
  have h := A.sectionSevenAffineNormalizedBaseDeckHom_coordinate A.markedZeroCentralMeridianClass
  have hm : FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.sectionSevenAffineMarkedCentralCoordinate_base A.markedZeroCentralMeridianClass =
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
  exact (congrArg MulOpposite.unop h.symm).trans A.sectionSevenAffineNormalizedMidpointTotal_zero_label

public theorem sectionSevenAffineNormalizedBaseDeckHom_one (A : PaperAnalyticData) :
    (A.sectionSevenAffineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridian)).unop = g₂ := by
  have h := A.sectionSevenAffineNormalizedBaseDeckHom_coordinate A.markedOneCentralMeridianClass
  have hm : FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.sectionSevenAffineMarkedCentralCoordinate_base A.markedOneCentralMeridianClass =
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
  exact (congrArg MulOpposite.unop h.symm).trans A.sectionSevenAffineNormalizedMidpointTotal_one_label

public theorem exists_sectionSevenAffineNormalizedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) (g : Delta)
    (hg : (A.sectionSevenAffineNormalizedBaseDeckHom (Path.Homotopic.Quotient.mk γ)).unop = g) :
    ∃ L : Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv g A.sectionSevenAffineNormalizedMidpoint),
      ∀ t, A.regularCoordinate (L t) = γ t := by
  let _ := A.regularBaseDeckAction
  let hp := A.regularCoordinate_isQuotientCoveringMap
  let e : A.regularCoordinate ⁻¹' {twicePuncturedComplexBasepoint} :=
    ⟨A.sectionSevenAffineNormalizedMidpoint, A.sectionSevenAffineNormalizedMidpoint_projects⟩
  let e' := hp.toPermFiber _ g e
  have hm : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e = e' := by
    apply Subtype.ext
    have h := hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := Path.Homotopic.Quotient.mk γ)
    change (A.sectionSevenAffineNormalizedBaseDeckHom
      (Path.Homotopic.Quotient.mk γ)).unop • e.val = _ at h
    rw [hg] at h
    exact h.symm
  let p : C(RegularBase (U := A.modular.modularParameter.toTriangleUniformization),
      RegularCoordinateBase) :=
    ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩
  obtain ⟨L, hL⟩ := IsCoveringMap.exists_path_lift_of_monodromy_eq
    (p := p) hp.isCoveringMap γ e e' hm
  exact ⟨L, fun t ↦ congrArg (fun p : Path _ _ ↦ p t) hL⟩

public noncomputable def sectionSevenAffineNormalizedZeroLift (A : PaperAnalyticData) :
    Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv g₁ A.sectionSevenAffineNormalizedMidpoint) :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseZeroMeridian g₁
    A.sectionSevenAffineNormalizedBaseDeckHom_zero).choose

public theorem sectionSevenAffineNormalizedZeroLift_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.sectionSevenAffineNormalizedZeroLift t) =
      twicePuncturedClockwiseZeroMeridian t :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseZeroMeridian g₁
    A.sectionSevenAffineNormalizedBaseDeckHom_zero).choose_spec t

public noncomputable def sectionSevenAffineNormalizedOneLift (A : PaperAnalyticData) :
    Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv g₂ A.sectionSevenAffineNormalizedMidpoint) :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseOneMeridian g₂
    A.sectionSevenAffineNormalizedBaseDeckHom_one).choose

public theorem sectionSevenAffineNormalizedOneLift_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.sectionSevenAffineNormalizedOneLift t) =
      twicePuncturedClockwiseOneMeridian t :=
  (A.exists_sectionSevenAffineNormalizedLoopLift twicePuncturedClockwiseOneMeridian g₂
    A.sectionSevenAffineNormalizedBaseDeckHom_one).choose_spec t

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

public noncomputable def sectionSevenAffineNormalizedStripLift (A : PaperAnalyticData) :
    A.SectionSevenAffineStripLift where
  lift := A.sectionSevenAffineNormalizedStripContinuousLift
  lift_coordinate z := congrArg Subtype.val
    (congrFun A.sectionSevenAffineNormalizedStripContinuousLift_coordinate z)

end SphereSixComplex.Geometry.PaperAnalyticData
