module

public import SphereSixComplex.Geometry.PaperCentralEndCover
public import SphereSixComplex.Topology.PaperCentralFundamentalGroupGeneration
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence

/-!
# Finite outer monodromy of the marked elliptic meridians

The two marked loops in the twice-punctured affine base are lifted through the actual regular
source cover.  Equivariant radial normalization moves those lifts into the linear elliptic
collars without changing their deck labels.  The collar separation theorem then proves that the
labels have finite order.  No identification of those labels with chosen triangle generators is
assumed.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

/-- Changing a quotient-cover basepoint by an equality does not change the deck label when the
loop is transported by the same equality. -/
public theorem fundamentalGroupToMulOpposite_baseEq
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) (e : E) {y : X}
    (h : p e = y) (gamma : FundamentalGroup X (p e)) :
    hp.fundamentalGroupToMulOpposite ⟨e, h⟩
        (Topology.fundamentalGroupMulEquivOfEq h gamma) =
      hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ gamma := by
  cases h
  simp only [Topology.fundamentalGroupMulEquivOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Finite deck order is invariant under transport of a loop to another basepoint of the same
regular quotient cover. -/
public theorem fundamentalGroupToMulOpposite_isOfFinOrder_transport
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : C(E, X)}
    (hp : IsQuotientCoveringMap p G) {x y : X}
    (W : Path x y) (ex : p ⁻¹' {x}) (ey : p ⁻¹' {y})
    (gamma : FundamentalGroup X x)
    (hfin : IsOfFinOrder
      (MulOpposite.unop (hp.fundamentalGroupToMulOpposite ex gamma))) :
    IsOfFinOrder (MulOpposite.unop
      (hp.fundamentalGroupToMulOpposite ey
        (FundamentalGroup.fundamentalGroupMulEquivOfPath W gamma))) := by
  rw [isOfFinOrder_iff_pow_eq_one] at hfin ⊢
  obtain ⟨n, hn, hpow⟩ := hfin
  refine ⟨n, hn, ?_⟩
  let phiX := hp.fundamentalGroupToMulOpposite ex
  let phiY := hp.fundamentalGroupToMulOpposite ey
  let gammaY := FundamentalGroup.fundamentalGroupMulEquivOfPath W gamma
  have hphiX : phiX (gamma ^ n) = 1 := by
    rw [map_pow]
    apply MulOpposite.unop_injective
    simpa [phiX] using hpow
  have hxfix : hp.isCoveringMap.monodromy (gamma ^ n) ex = ex := by
    have hlabel := (hp.fundamentalGroupToMulOpposite_apply_eq_Iff
      (e := ex) (γ := gamma ^ n) (g := 1)).mp hphiX
    apply Subtype.ext
    simpa using hlabel.symm
  have hmonoId : hp.isCoveringMap.monodromy (gamma ^ n) = id :=
    (hp.monodromy_eq_id_iff ex).mpr hxfix
  have hyfix : hp.isCoveringMap.monodromy (gammaY ^ n) ey = ey := by
    change hp.isCoveringMap.monodromy
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath W gamma) ^ n) ey = ey
    rw [← map_pow]
    change hp.isCoveringMap.monodromy
      ((Path.Homotopic.Quotient.mk W).symm.trans
        ((gamma ^ n).trans (Path.Homotopic.Quotient.mk W))) ey = ey
    rw [hp.isCoveringMap.monodromy_trans_apply,
      hp.isCoveringMap.monodromy_trans_apply, hmonoId]
    simp only [id_eq]
    rw [← hp.isCoveringMap.monodromy_trans_apply]
    have hcancel : (Path.Homotopic.Quotient.mk W).symm.trans
        (Path.Homotopic.Quotient.mk W) = Path.Homotopic.Quotient.refl y := by
      simp
    rw [hcancel, hp.isCoveringMap.monodromy_refl]
    rfl
  have hphiY : phiY (gammaY ^ n) = 1 := by
    apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff
      (e := ey) (γ := gammaY ^ n) (g := 1)).mpr
    simpa using congrArg Subtype.val hyfix.symm
  rw [map_pow] at hphiY
  have hu := congrArg MulOpposite.unop hphiY
  simpa [phiY, gammaY] using hu

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The outer triangle-group monodromy of the actual regular base cover at the marked lift. -/
public noncomputable def markedBaseOuterDeckHom :
    FundamentalGroup
        (PuncturedOrbifoldBase (U := A.paperTriangleUniformization))
        A.markedPuncturedBasepoint →* Deltaᵐᵒᵖ := by
  let _ := A.regularBaseDeckAction
  let hp := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.fundamentalGroupToMulOpposite
    ⟨A.markedRegularBaseLift, A.markedRegularBaseLift_projects⟩

/-- The clockwise meridian about the order-three point has finite outer deck order. -/
public theorem markedZeroBaseDeck_isOfFinOrder :
    letI := A.regularBaseDeckAction
    let hp := regularBaseQuotientMap_isQuotientCoveringMap
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    IsOfFinOrder (MulOpposite.unop
      (hp.fundamentalGroupToMulOpposite
        ⟨A.markedRegularBaseLift, A.markedRegularBaseLift_projects⟩
        A.markedZeroBaseMeridianClass)) := by
  let _ := A.regularBaseDeckAction
  let hproper : SourceActionProperlyDiscontinuous := sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hp := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let e : (regularBaseQuotientMap (U := A.paperTriangleUniformization)) ⁻¹'
      {A.markedPuncturedBasepoint} :=
    ⟨A.markedRegularBaseLift, A.markedRegularBaseLift_projects⟩
  let gamma : FundamentalGroup
      (PuncturedOrbifoldBase (U := A.paperTriangleUniformization))
      A.markedPuncturedBasepoint :=
    Path.Homotopic.Quotient.mk A.markedZeroBaseMeridian
  let g : Delta := MulOpposite.unop
    (hp.fundamentalGroupToMulOpposite e gamma)
  have hgamma : gamma = A.markedZeroBaseMeridianClass := by
    exact A.markedZeroBaseMeridianClass_eq_pathLoopClass.symm
  change IsOfFinOrder (MulOpposite.unop
    (hp.fundamentalGroupToMulOpposite e A.markedZeroBaseMeridianClass))
  rw [← hgamma]
  change IsOfFinOrder g
  have hsource : A.markedZeroBaseMeridian 0 =
      regularBaseQuotientMap (U := A.paperTriangleUniformization)
        A.markedRegularBaseLift :=
    A.markedZeroBaseMeridian.source.trans A.markedRegularBaseLift_projects.symm
  let L := hp.isCoveringMap.liftPath A.markedZeroBaseMeridian
    A.markedRegularBaseLift hsource
  have hLzero : L 0 = A.markedRegularBaseLift :=
    hp.isCoveringMap.liftPath_zero _ _ _
  have hLone : L 1 = actionMap A.regularBaseDeckAction g
      A.markedRegularBaseLift := by
    have hdeck := hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := gamma)
    change actionMap A.regularBaseDeckAction g A.markedRegularBaseLift =
      (hp.isCoveringMap.monodromy gamma e :
        RegularBase (U := A.paperTriangleUniformization)) at hdeck
    calc
      L 1 = (hp.isCoveringMap.monodromy gamma e :
          RegularBase (U := A.paperTriangleUniformization)) := by rfl
      _ = actionMap A.regularBaseDeckAction g A.markedRegularBaseLift := hdeck.symm
  let Q : Path A.markedRegularBaseLift
      (actionMap A.regularBaseDeckAction g A.markedRegularBaseLift) :=
    { toFun := L
      continuous_toFun := L.continuous
      source' := hLzero
      target' := hLone }
  have hQcoordinate (t : unitInterval) :
      A.regularCoordinate (Q t) = twicePuncturedClockwiseZeroPoint t := by
    have hproj := congrFun
      (hp.isCoveringMap.liftPath_lifts A.markedZeroBaseMeridian
        A.markedRegularBaseLift hsource) t
    change regularBaseQuotientMap (U := A.paperTriangleUniformization) (Q t) =
      A.markedZeroBaseMeridian t at hproj
    calc
      A.regularCoordinate (Q t) =
          A.puncturedBaseHomeomorphTwicePuncturedComplex
            (regularBaseQuotientMap (U := A.paperTriangleUniformization) (Q t)) :=
        (A.puncturedBaseHomeomorphTwicePuncturedComplex_mk (Q t)).symm
      _ = A.puncturedBaseHomeomorphTwicePuncturedComplex
          (A.markedZeroBaseMeridian t) := congrArg _ hproj
      _ = twicePuncturedClockwiseZeroPoint t := by
        change A.puncturedBaseHomeomorphTwicePuncturedComplex
          (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
            (twicePuncturedClockwiseZeroPoint t)) = _
        rw [A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply]
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderThreeAffineHalfPlaneCoordinateRegion := by
    rw [hQcoordinate]
    exact twicePuncturedClockwiseZeroPoint_mem_left t
  obtain ⟨R, hR, _hRone, D⟩ :=
    exists_orderThreeLinearCollarSourceData
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let inner := R / 2
  have hinner : 0 < inner := by dsimp [inner]; linarith
  have hinnerR : inner < R := by dsimp [inner]; linarith
  obtain ⟨delta, hdelta, hcoordinate⟩ := A.exists_orderThree_coordinate_radius inner hinner
  let r := min (delta / 2) (1 / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (by norm_num)
  have hrdelta : r < delta := by
    exact (min_le_left _ _).trans_lt (by linarith)
  have hrhalf : r ≤ 2 / 3 := by
    exact (min_le_right _ _).trans (by norm_num)
  let s := r / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  let E := A.orderThreeBaseRadialEquiv hs hsr hrhalf
  let xbig : A.orderThreeAffineHalfPlaneBaseLift :=
    ⟨A.markedRegularBaseLift, by simpa [Q.source] using hQhalf 0⟩
  let xbigg : A.orderThreeAffineHalfPlaneBaseLift :=
    ⟨actionMap A.regularBaseDeckAction g A.markedRegularBaseLift,
      by simpa [Q.target] using hQhalf 1⟩
  let Qbig : Path xbig xbigg :=
    { toFun := fun t ↦ ⟨Q t, hQhalf t⟩
      continuous_toFun := Q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact Q.source
      target' := by apply Subtype.ext; exact Q.target }
  have hbigAction : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant
        orderThreeAffineHalfPlaneCoordinateRegion) g xbig = xbigg := by
    apply Subtype.ext
    rfl
  have hsmallEnd : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant
        (orderThreeAffineDiscCoordinateRegion r)) g (E.invFun xbig) =
      E.invFun xbigg := by
    rw [← hbigAction]
    exact (E.invFun_equivariant g xbig).symm
  let QsmallCarrier : Path (E.invFun xbig)
      (actionMap
        (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
          A.regularCoordinate_deck_invariant
          (orderThreeAffineDiscCoordinateRegion r)) g (E.invFun xbig)) :=
    (Qbig.map E.invFun.continuous).cast rfl hsmallEnd
  let QsmallRegular := QsmallCarrier.map continuous_subtype_val
  let Qsmall : Path (E.invFun xbig).1.1
      (fuchsianSourceAction g • (E.invFun xbig).1.1) :=
    (QsmallRegular.map continuous_subtype_val).cast rfl (by rfl)
  apply A.orderThree_path_deck_isOfFinOrder_of_coordinate_small hinnerR D hcoordinate
    (E.invFun xbig).1.1 g Qsmall
  intro t
  have ht := (QsmallCarrier t).2
  change ‖(A.regularCoordinate (QsmallCarrier t).1).1‖ < delta
  exact ht.trans hrdelta

/-- The clockwise meridian about the order-four point has finite outer deck order. -/
public theorem markedOneBaseDeck_isOfFinOrder :
    letI := A.regularBaseDeckAction
    let hp := regularBaseQuotientMap_isQuotientCoveringMap
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    IsOfFinOrder (MulOpposite.unop
      (hp.fundamentalGroupToMulOpposite
        ⟨A.markedRegularBaseLift, A.markedRegularBaseLift_projects⟩
        A.markedOneBaseMeridianClass)) := by
  let _ := A.regularBaseDeckAction
  let hproper : SourceActionProperlyDiscontinuous := sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hp := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let e : (regularBaseQuotientMap (U := A.paperTriangleUniformization)) ⁻¹'
      {A.markedPuncturedBasepoint} :=
    ⟨A.markedRegularBaseLift, A.markedRegularBaseLift_projects⟩
  let gamma : FundamentalGroup
      (PuncturedOrbifoldBase (U := A.paperTriangleUniformization))
      A.markedPuncturedBasepoint :=
    Path.Homotopic.Quotient.mk A.markedOneBaseMeridian
  let g : Delta := MulOpposite.unop
    (hp.fundamentalGroupToMulOpposite e gamma)
  have hgamma : gamma = A.markedOneBaseMeridianClass := by
    exact A.markedOneBaseMeridianClass_eq_pathLoopClass.symm
  change IsOfFinOrder (MulOpposite.unop
    (hp.fundamentalGroupToMulOpposite e A.markedOneBaseMeridianClass))
  rw [← hgamma]
  change IsOfFinOrder g
  have hsource : A.markedOneBaseMeridian 0 =
      regularBaseQuotientMap (U := A.paperTriangleUniformization)
        A.markedRegularBaseLift :=
    A.markedOneBaseMeridian.source.trans A.markedRegularBaseLift_projects.symm
  let L := hp.isCoveringMap.liftPath A.markedOneBaseMeridian
    A.markedRegularBaseLift hsource
  have hLzero : L 0 = A.markedRegularBaseLift :=
    hp.isCoveringMap.liftPath_zero _ _ _
  have hLone : L 1 = actionMap A.regularBaseDeckAction g
      A.markedRegularBaseLift := by
    have hdeck := hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := gamma)
    change actionMap A.regularBaseDeckAction g A.markedRegularBaseLift =
      (hp.isCoveringMap.monodromy gamma e :
        RegularBase (U := A.paperTriangleUniformization)) at hdeck
    calc
      L 1 = (hp.isCoveringMap.monodromy gamma e :
          RegularBase (U := A.paperTriangleUniformization)) := by rfl
      _ = actionMap A.regularBaseDeckAction g A.markedRegularBaseLift := hdeck.symm
  let Q : Path A.markedRegularBaseLift
      (actionMap A.regularBaseDeckAction g A.markedRegularBaseLift) :=
    { toFun := L
      continuous_toFun := L.continuous
      source' := hLzero
      target' := hLone }
  have hQcoordinate (t : unitInterval) :
      A.regularCoordinate (Q t) = twicePuncturedClockwiseOnePoint t := by
    have hproj := congrFun
      (hp.isCoveringMap.liftPath_lifts A.markedOneBaseMeridian
        A.markedRegularBaseLift hsource) t
    change regularBaseQuotientMap (U := A.paperTriangleUniformization) (Q t) =
      A.markedOneBaseMeridian t at hproj
    calc
      A.regularCoordinate (Q t) =
          A.puncturedBaseHomeomorphTwicePuncturedComplex
            (regularBaseQuotientMap (U := A.paperTriangleUniformization) (Q t)) :=
        (A.puncturedBaseHomeomorphTwicePuncturedComplex_mk (Q t)).symm
      _ = A.puncturedBaseHomeomorphTwicePuncturedComplex
          (A.markedOneBaseMeridian t) := congrArg _ hproj
      _ = twicePuncturedClockwiseOnePoint t := by
        change A.puncturedBaseHomeomorphTwicePuncturedComplex
          (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
            (twicePuncturedClockwiseOnePoint t)) = _
        rw [A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply]
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderFourAffineHalfPlaneCoordinateRegion := by
    rw [hQcoordinate]
    exact twicePuncturedClockwiseOnePoint_mem_right t
  obtain ⟨R, hR, _hRone, D⟩ :=
    exists_orderFourLinearCollarSourceData
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let inner := R / 2
  have hinner : 0 < inner := by dsimp [inner]; linarith
  have hinnerR : inner < R := by dsimp [inner]; linarith
  obtain ⟨delta, hdelta, hcoordinate⟩ := A.exists_orderFour_coordinate_radius inner hinner
  let r := min (delta / 2) (1 / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (by norm_num)
  have hrdelta : r < delta := by
    exact (min_le_left _ _).trans_lt (by linarith)
  have hrhalf : r ≤ 1 - 1 / 3 := by
    exact (min_le_right _ _).trans (by norm_num)
  let s := r / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  let E := A.orderFourBaseRadialEquiv hs hsr hrhalf
  let xbig : A.orderFourAffineHalfPlaneBaseLift :=
    ⟨A.markedRegularBaseLift, by simpa [Q.source] using hQhalf 0⟩
  let xbigg : A.orderFourAffineHalfPlaneBaseLift :=
    ⟨actionMap A.regularBaseDeckAction g A.markedRegularBaseLift,
      by simpa [Q.target] using hQhalf 1⟩
  let Qbig : Path xbig xbigg :=
    { toFun := fun t ↦ ⟨Q t, hQhalf t⟩
      continuous_toFun := Q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact Q.source
      target' := by apply Subtype.ext; exact Q.target }
  have hbigAction : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant
        orderFourAffineHalfPlaneCoordinateRegion) g xbig = xbigg := by
    apply Subtype.ext
    rfl
  have hsmallEnd : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant
        (orderFourAffineDiscCoordinateRegion r)) g (E.invFun xbig) =
      E.invFun xbigg := by
    rw [← hbigAction]
    exact (E.invFun_equivariant g xbig).symm
  let QsmallCarrier : Path (E.invFun xbig)
      (actionMap
        (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
          A.regularCoordinate_deck_invariant
          (orderFourAffineDiscCoordinateRegion r)) g (E.invFun xbig)) :=
    (Qbig.map E.invFun.continuous).cast rfl hsmallEnd
  let QsmallRegular := QsmallCarrier.map continuous_subtype_val
  let Qsmall : Path (E.invFun xbig).1.1
      (fuchsianSourceAction g • (E.invFun xbig).1.1) :=
    (QsmallRegular.map continuous_subtype_val).cast rfl (by rfl)
  apply A.orderFour_path_deck_isOfFinOrder_of_coordinate_small hinnerR D hcoordinate
    (E.invFun xbig).1.1 g Qsmall
  intro t
  have ht := (QsmallCarrier t).2
  change ‖(A.regularCoordinate (QsmallCarrier t).1).1 - 1‖ < delta
  exact ht.trans hrdelta

public theorem markedBaseOuterDeckHom_zero_isOfFinOrder :
    IsOfFinOrder (MulOpposite.unop
      (A.markedBaseOuterDeckHom A.markedZeroBaseMeridianClass)) := by
  exact A.markedZeroBaseDeck_isOfFinOrder

public theorem markedBaseOuterDeckHom_one_isOfFinOrder :
    IsOfFinOrder (MulOpposite.unop
      (A.markedBaseOuterDeckHom A.markedOneBaseMeridianClass)) := by
  exact A.markedOneBaseDeck_isOfFinOrder

/-- Outer triangle-group monodromy at the marked zero-section point of the central family. -/
public noncomputable def markedCentralOuterDeckHom :
    FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint) →* Deltaᵐᵒᵖ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.fundamentalGroupToMulOpposite
    ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift,
      A.markedCentralBase_eq_lift.symm⟩

/-- The zero section preserves the outer triangle-group deck label at the marked point. -/
public theorem markedCentralOuterDeckHom_zeroSection
    (gamma : FundamentalGroup
      (PuncturedOrbifoldBase (U := A.paperTriangleUniformization))
      A.markedPuncturedBasepoint) :
    A.markedCentralOuterDeckHom
        (A.centralZeroSectionFundamentalGroupMap gamma) =
      A.markedBaseOuterDeckHom gamma := by
  let _ := regularSourceMulAction A.paperTriangleUniformization
  let _ := regularFamilyDeckAction A.periods
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hpB := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let hpE := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let hB := A.markedRegularBaseLift_projects
  let gammaLit := (Topology.fundamentalGroupMulEquivOfEq hB).symm gamma
  have hgamma : Topology.fundamentalGroupMulEquivOfEq hB gammaLit = gamma := by
    exact (Topology.fundamentalGroupMulEquivOfEq hB).apply_symm_apply gamma
  let hE : regularFamilyQuotientMap A.periods
        (regularFamilyZeroSection A.periods A.markedRegularBaseLift) =
      A.centralZeroSection A.markedPuncturedBasepoint :=
    A.markedCentralBase_eq_lift.symm
  have hbase : hpB.fundamentalGroupToMulOpposite
        ⟨A.markedRegularBaseLift, hB⟩ gamma =
      hpB.fundamentalGroupToMulOpposite
        ⟨A.markedRegularBaseLift, rfl⟩ gammaLit := by
    rw [← hgamma]
    exact fundamentalGroupToMulOpposite_baseEq hpB
      A.markedRegularBaseLift hB gammaLit
  have hcentralClass :
      Topology.fundamentalGroupMulEquivOfEq hE
        (centralZeroSectionAtLiftMap A.periods A.markedRegularBaseLift gammaLit) =
      A.centralZeroSectionFundamentalGroupMap gamma := by
    calc
      _ = A.centralZeroSectionFundamentalGroupMap
          (A.markedBaseFundamentalGroupEquiv gammaLit) :=
        A.markedCentralZeroSection_naturality gammaLit
      _ = A.centralZeroSectionFundamentalGroupMap gamma := congrArg _ hgamma
  have hcentral : hpE.fundamentalGroupToMulOpposite
        ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift, hE⟩
        (A.centralZeroSectionFundamentalGroupMap gamma) =
      hpE.fundamentalGroupToMulOpposite
        ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift, rfl⟩
        (centralZeroSectionAtLiftMap A.periods A.markedRegularBaseLift gammaLit) := by
    rw [← hcentralClass]
    exact fundamentalGroupToMulOpposite_baseEq hpE
      (regularFamilyZeroSection A.periods A.markedRegularBaseLift) hE _
  unfold markedCentralOuterDeckHom markedBaseOuterDeckHom
  change hpE.fundamentalGroupToMulOpposite
      ⟨regularFamilyZeroSection A.periods A.markedRegularBaseLift, hE⟩
      (A.centralZeroSectionFundamentalGroupMap gamma) =
    hpB.fundamentalGroupToMulOpposite
      ⟨A.markedRegularBaseLift, hB⟩ gamma
  rw [hcentral, hbase]
  exact zeroSection_fundamentalGroupToMulOpposite A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
    A.markedRegularBaseLift gammaLit

public theorem markedCentralOuterDeckHom_zero_isOfFinOrder :
    IsOfFinOrder (MulOpposite.unop
      (A.markedCentralOuterDeckHom A.markedZeroCentralMeridianClass)) := by
  rw [markedZeroCentralMeridianClass,
    A.markedCentralOuterDeckHom_zeroSection]
  exact A.markedBaseOuterDeckHom_zero_isOfFinOrder

public theorem markedCentralOuterDeckHom_one_isOfFinOrder :
    IsOfFinOrder (MulOpposite.unop
      (A.markedCentralOuterDeckHom A.markedOneCentralMeridianClass)) := by
  rw [markedOneCentralMeridianClass,
    A.markedCentralOuterDeckHom_zeroSection]
  exact A.markedBaseOuterDeckHom_one_isOfFinOrder

end SphereSixComplex.Geometry.PaperAnalyticData

end
