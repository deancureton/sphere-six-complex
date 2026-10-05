module

public import SphereSixComplex.Prerequisites.Topology.HomotopyProductSlice
public import SphereSixComplex.Paper.Geometry.EllipticLogarithmicGauge.Homeomorph
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Geometry.PaperEllipticCentralEscape
public import SphereSixComplex.Paper.Topology.EllipticDiscCircleGluing
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedCayleyBounds
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving
public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCarriers
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open GlobalTorusFamily ComplexTorus EllipticFamilySpecialization EllipticVaryingFamilyQuotient
open EllipticWholeFiberCompactCover EllipticFixedPointCriterion

variable (A : AnalyticData)

public theorem regularFixedFiberPoint_coordinate
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.centralFamilyCoordinate (A.regularFixedFiberPoint b t) = A.regularCoordinate b := by
  induction t using Quotient.inductionOn with
  | _ v => rfl

theorem midpointComparisonLowerFiber_mem
    (p : A.OrderThreeAffineHalfPlaneBaseLift × AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.ellipticCentralHeight (A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)) < 2 / 3 := by
  change (A.centralFamilyCoordinate (A.ellipticCentralImageHomeomorph
    (A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)))).1.re < 2 / 3
  rw [Homeomorph.apply_symm_apply, A.regularFixedFiberPoint_coordinate]
  exact p.1.2

public def midpointComparisonLowerFiber :
    C(A.OrderThreeAffineHalfPlaneBaseLift ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter, A.affineOrderThreeCentralRegion) where
  toFun p := ⟨(A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)).1,
    ⟨A.ellipticCentralImageHomeomorph.symm (A.regularFixedFiberPoint p.1.1 p.2),
      A.midpointComparisonLowerFiber_mem p, rfl⟩⟩
  continuous_toFun := (continuous_subtype_val.comp
    (A.ellipticCentralImageHomeomorph.symm.continuous.comp
      (A.regularFixedFiberPoint_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)))).subtype_mk _

public def midpointComparisonLowerFiberSide :
    C(A.OrderThreeAffineHalfPlaneBaseLift ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter,
      A.actualAffineHeightSplit.allocation.orderThreeSide) :=
  (⟨fun x : A.affineOrderThreeCentralRegion ↦ ⟨x.1, Or.inr x.2⟩,
      continuous_subtype_val.subtype_mk _⟩ : C(_, _)).comp A.midpointComparisonLowerFiber

public def midpointComparisonLowerRadialHomotopy
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3)
    (b : A.OrderThreeAffineHalfPlaneBaseLift) :
    ContinuousMap.Homotopy
      (A.midpointComparisonLowerFiberSide.comp
        ((ContinuousMap.const _ b).prodMk (ContinuousMap.id _)))
      (A.midpointComparisonLowerFiberSide.comp
        ((ContinuousMap.const _ ((A.orderThreeBaseRadialEquiv hs hsr hr).toFun
          ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun b))).prodMk
            (ContinuousMap.id _))) :=
  (ContinuousMap.Homotopy.refl A.midpointComparisonLowerFiberSide).comp
    ((((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy.evalAt b).symm.toHomotopyConst).prodMk (ContinuousMap.Homotopy.refl (ContinuousMap.id _)))

open AnalyticTorusFamily RealPeriodTrivialization EllipticLogarithmicGauge TorusFamily

public def midpointComparisonThreeGauge (z : UpperHalfPlane) :
    AdditiveTorus
      (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne).1 :=
  Quotient.mk _
    (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (z, orderThreePrincipalGaugeSection A.periods z)).2

public theorem midpointComparisonThreeGauge_formula (q : TotalSpace (parameterMap A.periods)) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      ((orderThreePrincipalGaugeEquiv A.periods).symm q)).2 =
      -A.midpointComparisonThreeGauge (familyTotalSpaceBase A.periods q) +
        (orderThreeRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk, familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

open EllipticLinearCollarGlobalDescent EllipticLocalCoordinates EllipticFilling

theorem midpointComparisonThreeCollarTorus_mem
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderThree.radius)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    (orderThreeRealPeriodProductHomeomorph A.periods).symm (c, t) ∈
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier := by
  change 0 < orderThreeFamilyRadius A.periods _ ∧
    orderThreeFamilyRadius A.periods _ < A.starSeparation.orderThree.radius
  simpa only [orderThreeFamilyRadius_eq_productNorm, Homeomorph.apply_symm_apply]
    using And.intro hc0 hcr

public def midpointComparisonThreeCollarTorus
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderThree.radius)
    (a : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    C(AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier) :=
  ⟨fun t ↦ ⟨(orderThreeRealPeriodProductHomeomorph A.periods).symm (c, a + t),
      A.midpointComparisonThreeCollarTorus_mem c hc0 hcr (a + t)⟩,
    ((orderThreeRealPeriodProductHomeomorph A.periods).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.add continuous_id))).subtype_mk _⟩

public def midpointComparisonThreeFillingTorus
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderThree.radius)
    (a : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    C(AdditiveTorus A.duplicatedSectionSevenBandParameter,
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
  (⟨A.starToFilling 1, (A.starToFilling_isOpenEmbedding 1).continuous⟩ : C(_, _)).comp
    ((⟨Quotient.mk _, continuous_quot_mk⟩ : C(_, _)).comp
      (A.midpointComparisonThreeCollarTorus c hc0 hcr a))

public theorem midpointComparisonThreeFillingTorus_retraction
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderThree.radius)
    (a t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.midpointComparisonThreeFillingTorus c hc0 hcr a t) =
      RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm (a + t)) := by
  change RadialEllipticActionData.centralFiberCoverProjection _
    ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _).symm
      (orderThreeRealPeriodProductHomeomorph A.periods
        ((orderThreeRealPeriodProductHomeomorph A.periods).symm (c, a + t))).2) = _
  rw [Homeomorph.apply_symm_apply]

public theorem midpointComparisonThreeFillingTorus_homotopic
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderThree.radius)
    (a : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      (A.midpointComparisonThreeFillingTorus c hc0 hcr a)).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)).comp
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm.toHomotopyEquiv.toFun) := by
  let : PathConnectedSpace (AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
    Function.Surjective.pathConnectedSpace
      (f := torusProjection A.duplicatedSectionSevenBandParameter)
      Quotient.mk_surjective continuous_quot_mk
  let p := (PathConnectedSpace.joined a 0).some
  let k := (RadialEllipticActionData.centralFiberCoverProjection
    (orderThreeRadialActionData A.periods)).comp
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderThreeRadialActionData A.periods)).symm.toHomotopyEquiv.toFun
  refine ⟨{ toFun := fun tx ↦ k (p tx.1 + tx.2)
            continuous_toFun := k.continuous.comp
              ((p.continuous.comp continuous_fst).add continuous_snd)
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro t
    rw [p.source]
    exact (A.midpointComparisonThreeFillingTorus_retraction c hc0 hcr a t).symm
  · intro t
    rw [p.target, zero_add]
    rfl

open EllipticCayleyHomeomorph

public theorem midpointComparisonThreeCollarTorus_central
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (hc0 : 0 < ‖(orderThreeCayleyHomeomorph b.1 : ℂ)‖)
    (hcr : ‖(orderThreeCayleyHomeomorph b.1 : ℂ)‖ < A.starSeparation.orderThree.radius)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.starToCentral 1 (Quotient.mk _
      (A.midpointComparisonThreeCollarTorus (orderThreeCayleyHomeomorph b.1) hc0 hcr
        (-A.midpointComparisonThreeGauge b.1) t)) = A.regularFixedFiberPoint b t := by
  induction t using Quotient.inductionOn with
  | _ v =>
      let r := regularFamilyCoverProjection A.periods
        (b, A.regularFixedToMoving b v)
      have ht : (orderThreeRealPeriodProductHomeomorph A.periods
          (regularFamilyInclusion A.periods r)).2 = Quotient.mk _ v := by
        change (orderThreeRealPeriodProductHomeomorph A.periods
          (regularFamilyInclusion A.periods (Quotient.mk _ (b, A.regularFixedToMoving b v)))).2 = _
        rw [regularFamilyInclusion_mk, orderThreeRealPeriodProductHomeomorph_mk]
        apply congrArg (Quotient.mk _)
        change A.regularMovingToFixed b (A.regularFixedToMoving b v) = v
        exact A.regularMovingToFixed_regularFixedToMoving b v
      have hq : (A.midpointComparisonThreeCollarTorus
          (orderThreeCayleyHomeomorph b.1) hc0 hcr
          (-A.midpointComparisonThreeGauge b.1) (Quotient.mk _ v)).1 =
          (orderThreePrincipalGaugeEquiv A.periods).symm
            (regularFamilyInclusion A.periods r) := by
        apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
        change (orderThreeRealPeriodProductHomeomorph A.periods)
          ((orderThreeRealPeriodProductHomeomorph A.periods).symm _) = _
        rw [Homeomorph.apply_symm_apply]
        apply Prod.ext
        · rfl
        · rw [A.midpointComparisonThreeGauge_formula, ht]
          rfl
      rw [A.orderThreeStarToCentral_mk]
      change A.centralQuotientProjection _ = A.centralQuotientProjection r
      apply congrArg A.centralQuotientProjection
      apply regularFamilyInclusion_injective A.periods
      rw [regularFamilyInclusion_orderThreeCollarToRegular]
      change orderThreePrincipalGaugeEquiv A.periods _ = _
      rw [hq, Equiv.apply_symm_apply]

public def midpointComparisonThreeFillingToSide :
    C(A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius,
      A.actualAffineHeightSplit.allocation.orderThreeSide) :=
  (⟨fun x : A.orderThreeFillingImage ↦ ⟨x.1, Or.inl x.2⟩,
    continuous_subtype_val.subtype_mk _⟩ : C(_, _)).comp
    (A.orderThreeFillingImageToPiece.symm.toHomotopyEquiv.toFun.comp
      A.orderThreePieceHomeomorph.toHomotopyEquiv.toFun)

public theorem midpointComparisonThree_endpoint_in_side
    (b : A.OrderThreeAffineHalfPlaneBaseLift)
    (hc0 : 0 < ‖(orderThreeCayleyHomeomorph b.1.1 : ℂ)‖)
    (hcr : ‖(orderThreeCayleyHomeomorph b.1.1 : ℂ)‖ < A.starSeparation.orderThree.radius)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.midpointComparisonLowerFiberSide (b, t) =
      A.midpointComparisonThreeFillingToSide
        (A.midpointComparisonThreeFillingTorus (orderThreeCayleyHomeomorph b.1.1)
          hc0 hcr (-A.midpointComparisonThreeGauge b.1.1) t) := by
  apply Subtype.ext
  apply Subtype.ext
  let q : A.StarCollarSource 1 := Quotient.mk _ (A.midpointComparisonThreeCollarTorus
    (orderThreeCayleyHomeomorph b.1.1) hc0 hcr
    (-A.midpointComparisonThreeGauge b.1.1) t)
  let y := A.ellipticCentralImageHomeomorph.symm (A.regularFixedFiberPoint b.1 t)
  change y.1.1 = _
  calc
    y.1.1 = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.regularFixedFiberPoint b.1 t)).1 := by
      have h := A.centralToSectionSevenEulerPiece_centralImage y
      rw [show A.ellipticCentralImageHomeomorph y = A.regularFixedFiberPoint b.1 t
        from A.ellipticCentralImageHomeomorph.apply_symm_apply _] at h
      exact h.symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 1 q)).1 := by
      rw [A.midpointComparisonThreeCollarTorus_central b.1 hc0 hcr t]
    _ = A.openEmbeddingStarData.collarSourceToGlued 1 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 1 q
    _ = _ := (A.openEmbeddingStarData.fillingInclusion_toFilling 1 q).symm

public theorem midpointComparisonThree_chosen_inverse :
    ((A.affineOrderThreeSideToReducedFiberHomotopyEquiv).toFun.comp
      A.midpointComparisonThreeFillingToSide).Homotopic
      (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun := by
  let E := orderThreeOverlapIsHomotopyEquivalence_inclusion
    A.orderThreeOverlapIsHomotopyEquivalence
  let e := E.toHomotopyEquiv.trans
    (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
      A.orderThreeFillingImage
      A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv |>.trans
      A.orderThreeFillingImageToPiece.toHomotopyEquiv |>.trans
      A.orderThreePieceHomeomorph.symm.toHomotopyEquiv
  have he : e.invFun = A.midpointComparisonThreeFillingToSide := by
    dsimp only [e, ContinuousMap.HomotopyEquiv.trans]
    rw [E.toHomotopyEquiv_invFun]
    apply ContinuousMap.ext
    intro x
    rfl
  have h := ContinuousMap.Homotopic.comp
    (.refl (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun) e.right_inv
  rw [he] at h
  convert h using 1 <;> rfl

public def midpointComparisonProduct :
    (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
      A.actualAffineHeightSplit.allocation.orderFourSide : Set A.ellipticInterior) ≃ₜ
      affineVerticalStrip × AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  A.actualAffineHeightSplit.sidesIntersectionHomeomorph.trans
    (A.affineCentralBandMarkedProductHomeomorph A.affineCentralSeparation)

public def midpointComparisonSlice :=
  A.midpointComparisonProduct.symm.toHomotopyEquiv.toFun.comp
    ((ContinuousMap.const _ affineStripMidpoint).prodMk (ContinuousMap.id
      (AdditiveTorus A.duplicatedSectionSevenBandParameter)))

public theorem midpointComparisonSlice_lower :
    (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).comp A.midpointComparisonSlice =
      A.midpointComparisonLowerFiberSide.comp
        ((ContinuousMap.const _ (A.affineNormalizedOrderThreeHalfPlaneLift affineStripMidpoint)).prodMk
          (ContinuousMap.id (AdditiveTorus A.duplicatedSectionSevenBandParameter))) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have h := A.affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.affineCentralSeparation (affineStripMidpoint, t)
  have hb := A.affineNamedStripLift_apply_midpoint
  change _ = A.regularFixedFiberPoint (A.affineNamedStripLift.lift affineStripMidpoint) t at h
  rw [hb] at h
  have hv := congrArg (fun x : A.CentralFamily ↦
    (A.ellipticCentralImageHomeomorph.symm x).1) h
  simp only [affineCentralBandToCentralFamily, Homeomorph.symm_apply_apply] at hv
  change _ = (A.ellipticCentralImageHomeomorph.symm
    (A.regularFixedFiberPoint (A.affineNormalizedStripContinuousLift affineStripMidpoint) t)).1
  rw [A.affineNormalizedStripContinuousLift_midpoint]
  exact hv


public theorem midpointComparison_regular_three_positive
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    0 < ‖(orderThreeCayleyHomeomorph b.1 : ℂ)‖ := by
  apply norm_pos_iff.mpr
  apply EllipticLogarithmicGauge.coe_ne_zero_of_ne_center
  intro hzero
  have hfixed : b.1 = SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint := by
    apply orderThreeCayleyHomeomorph.injective
    simpa [orderThreeCayleyHomeomorph, UpperHalfPlane.cayleyHomeomorph,
      UpperHalfPlane.cayleyToDisc, ComplexUnitDisc.center, orderThreeCayley_fixedPoint] using hzero
  have hm := (A.isRegularBasePoint_iff_coordinate_mem _).mp b.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm
  exact hm.1 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_one)

public theorem midpointComparisonThree_compatibility :
    (affineOrderThreeBandToReducedFiber
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
        A.orderThreeOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderThreeCoverMap A) := by
  let : ContractibleSpace affineVerticalStrip := affineVerticalStrip_contractibleSpace
  apply ContinuousMap.Homotopic.of_product_slice
    A.midpointComparisonProduct affineStripMidpoint
  let b := A.affineNormalizedOrderThreeHalfPlaneLift affineStripMidpoint
  let r := A.affineOrderThreeMarkedDiscRadius
  have hr0 : 0 < r := A.affineOrderThreeMarkedDiscRadius_spec.1
  have hr : r ≤ 2 / 3 := A.affineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderThreeBaseRadialEquiv (s := r / 2) (by linarith) (by linarith) hr
  let z := E.toFun (E.invFun b)
  have hz0 := A.midpointComparison_regular_three_positive z.1
  have hzr : ‖(orderThreeCayleyHomeomorph z.1.1 : ℂ)‖ <
      A.starSeparation.orderThree.radius := A.affineNormalizedOrderThreeRadialLift_midpoint_cayley
  let q := A.midpointComparisonThreeFillingTorus (orderThreeCayleyHomeomorph z.1.1)
    hz0 hzr (-A.midpointComparisonThreeGauge z.1.1)
  have hrad := A.midpointComparisonLowerRadialHomotopy
    (s := r / 2) (by linarith) (by linarith) hr b
  have hend : A.midpointComparisonLowerFiberSide.comp
      ((ContinuousMap.const _ z).prodMk (ContinuousMap.id _)) =
      A.midpointComparisonThreeFillingToSide.comp q := by
    apply ContinuousMap.ext
    intro t
    exact A.midpointComparisonThree_endpoint_in_side z hz0 hzr t
  have hside : ((IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).comp
        A.midpointComparisonSlice).Homotopic (A.midpointComparisonThreeFillingToSide.comp q) := by
    rw [A.midpointComparisonSlice_lower, ← hend]
    exact ⟨hrad⟩
  have h₁ := ContinuousMap.Homotopic.comp
    (.refl A.affineOrderThreeSideToReducedFiberHomotopyEquiv.toFun) hside
  have h₂ := ContinuousMap.Homotopic.comp A.midpointComparisonThree_chosen_inverse (.refl q)
  have h₃ := A.midpointComparisonThreeFillingTorus_homotopic
    (orderThreeCayleyHomeomorph z.1.1) hz0 hzr (-A.midpointComparisonThreeGauge z.1.1)
  rw [ContinuousMap.comp_assoc] at h₂
  have h := h₁.trans (h₂.trans h₃)
  convert h using 1
  · rfl
  · apply ContinuousMap.ext
    intro t
    change (orderThreeRadialActionData A.periods).centralFiberCoverProjection
      ((orderThreeRadialActionData A.periods).centralFiberCoverSourceHomeomorph.symm
        (A.midpointComparisonProduct
          (A.midpointComparisonProduct.symm (affineStripMidpoint, t))).2) = _
    rw [Homeomorph.apply_symm_apply]
    rfl


theorem midpointComparisonUpperFiber_mem
    (p : A.OrderFourAffineHalfPlaneBaseLift × AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.ellipticCentralHeight (A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)) > 1 / 3 := by
  change (A.centralFamilyCoordinate (A.ellipticCentralImageHomeomorph
    (A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)))).1.re > 1 / 3
  rw [Homeomorph.apply_symm_apply, A.regularFixedFiberPoint_coordinate]
  exact p.1.2

public def midpointComparisonUpperFiber :
    C(A.OrderFourAffineHalfPlaneBaseLift ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter, A.affineOrderFourCentralRegion) where
  toFun p := ⟨(A.ellipticCentralImageHomeomorph.symm
      (A.regularFixedFiberPoint p.1.1 p.2)).1,
    ⟨A.ellipticCentralImageHomeomorph.symm (A.regularFixedFiberPoint p.1.1 p.2),
      A.midpointComparisonUpperFiber_mem p, rfl⟩⟩
  continuous_toFun := (continuous_subtype_val.comp
    (A.ellipticCentralImageHomeomorph.symm.continuous.comp
      (A.regularFixedFiberPoint_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)))).subtype_mk _

public def midpointComparisonUpperFiberSide :
    C(A.OrderFourAffineHalfPlaneBaseLift ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter,
      A.actualAffineHeightSplit.allocation.orderFourSide) :=
  (⟨fun x : A.affineOrderFourCentralRegion ↦ ⟨x.1, Or.inr x.2⟩,
      continuous_subtype_val.subtype_mk _⟩ : C(_, _)).comp A.midpointComparisonUpperFiber

public def midpointComparisonUpperRadialHomotopy
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3)
    (b : A.OrderFourAffineHalfPlaneBaseLift) :
    ContinuousMap.Homotopy
      (A.midpointComparisonUpperFiberSide.comp
        ((ContinuousMap.const _ b).prodMk (ContinuousMap.id _)))
      (A.midpointComparisonUpperFiberSide.comp
        ((ContinuousMap.const _ ((A.orderFourBaseRadialEquiv hs hsr hr).toFun
          ((A.orderFourBaseRadialEquiv hs hsr hr).invFun b))).prodMk
            (ContinuousMap.id _))) :=
  (ContinuousMap.Homotopy.refl A.midpointComparisonUpperFiberSide).comp
    ((((A.orderFourBaseRadialEquiv hs hsr hr).rightInvHomotopy.evalAt b).symm.toHomotopyConst).prodMk (ContinuousMap.Homotopy.refl (ContinuousMap.id _)))

open AnalyticTorusFamily RealPeriodTrivialization EllipticLogarithmicGauge TorusFamily

public def midpointComparisonFourGauge (z : UpperHalfPlane) :
    AdditiveTorus
      (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1 :=
  Quotient.mk _
    (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (z, orderFourPrincipalGaugeSection A.periods z)).2

public theorem midpointComparisonFourGauge_formula (q : TotalSpace (parameterMap A.periods)) :
    (orderFourRealPeriodProductHomeomorph A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm q)).2 =
      -A.midpointComparisonFourGauge (familyTotalSpaceBase A.periods q) +
        (orderFourRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk, familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

open EllipticLinearCollarGlobalDescent EllipticLocalCoordinates EllipticFilling

theorem midpointComparisonFourCollarTorus_mem
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderFour.radius)
    (t : AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    (orderFourRealPeriodProductHomeomorph A.periods).symm (c, t) ∈
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier := by
  change 0 < orderFourFamilyRadius A.periods _ ∧
    orderFourFamilyRadius A.periods _ < A.starSeparation.orderFour.radius
  simpa only [orderFourFamilyRadius_eq_productNorm, Homeomorph.apply_symm_apply]
    using And.intro hc0 hcr

public def midpointComparisonFourCollarTorus
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderFour.radius)
    (a : AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    C(AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1,
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier) :=
  ⟨fun t ↦ ⟨(orderFourRealPeriodProductHomeomorph A.periods).symm (c, a + t),
      A.midpointComparisonFourCollarTorus_mem c hc0 hcr (a + t)⟩,
    ((orderFourRealPeriodProductHomeomorph A.periods).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.add continuous_id))).subtype_mk _⟩

public def midpointComparisonFourFillingTorus
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderFour.radius)
    (a : AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    C(AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1,
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
  (⟨A.starToFilling 2, (A.starToFilling_isOpenEmbedding 2).continuous⟩ : C(_, _)).comp
    ((⟨Quotient.mk _, continuous_quot_mk⟩ : C(_, _)).comp
      (A.midpointComparisonFourCollarTorus c hc0 hcr a))

public theorem midpointComparisonFourFillingTorus_retraction
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderFour.radius)
    (a t : AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.midpointComparisonFourFillingTorus c hc0 hcr a t) =
      RadialEllipticActionData.centralFiberCoverProjection (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm (a + t)) := by
  change RadialEllipticActionData.centralFiberCoverProjection _
    ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _).symm
      (orderFourRealPeriodProductHomeomorph A.periods
        ((orderFourRealPeriodProductHomeomorph A.periods).symm (c, a + t))).2) = _
  rw [Homeomorph.apply_symm_apply]

public theorem midpointComparisonFourFillingTorus_homotopic
    (c : ComplexUnitDisc) (hc0 : 0 < ‖(c : ℂ)‖)
    (hcr : ‖(c : ℂ)‖ < A.starSeparation.orderFour.radius)
    (a : AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    ((orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      (A.midpointComparisonFourFillingTorus c hc0 hcr a)).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)).comp
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm.toHomotopyEquiv.toFun) := by
  let : PathConnectedSpace (AdditiveTorus (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
    Function.Surjective.pathConnectedSpace
      (f := torusProjection (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      Quotient.mk_surjective continuous_quot_mk
  let p := (PathConnectedSpace.joined a 0).some
  let k := (RadialEllipticActionData.centralFiberCoverProjection
    (orderFourRadialActionData A.periods)).comp
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderFourRadialActionData A.periods)).symm.toHomotopyEquiv.toFun
  refine ⟨{ toFun := fun tx ↦ k (p tx.1 + tx.2)
            continuous_toFun := k.continuous.comp
              ((p.continuous.comp continuous_fst).add continuous_snd)
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro t
    rw [p.source]
    exact (A.midpointComparisonFourFillingTorus_retraction c hc0 hcr a t).symm
  · intro t
    rw [p.target, zero_add]

open EllipticCayleyHomeomorph

public theorem midpointComparisonFourCollarTorus_central
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (hc0 : 0 < ‖(orderFourCayleyHomeomorph b.1 : ℂ)‖)
    (hcr : ‖(orderFourCayleyHomeomorph b.1 : ℂ)‖ < A.starSeparation.orderFour.radius)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.starToCentral 2 (Quotient.mk _
      (A.midpointComparisonFourCollarTorus (orderFourCayleyHomeomorph b.1) hc0 hcr
        (-A.midpointComparisonFourGauge b.1) (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph t))) = A.regularFixedFiberPoint b t := by
  induction t using Quotient.inductionOn with
  | _ v =>
      let r := regularFamilyCoverProjection A.periods
        (b, A.regularFixedToMoving b v)
      have ht : (orderFourRealPeriodProductHomeomorph A.periods
          (regularFamilyInclusion A.periods r)).2 = A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph (Quotient.mk _ v) := by
        change (orderFourRealPeriodProductHomeomorph A.periods
          (regularFamilyInclusion A.periods (Quotient.mk _ (b, A.regularFixedToMoving b v)))).2 = _
        rw [regularFamilyInclusion_mk, orderFourRealPeriodProductHomeomorph_mk]
        apply congrArg (Quotient.mk _)
        simp [regularBundleInclusion, movingToFixedCover, regularFixedToMoving,
          fixedToMovingCover, periodCoordinates, fullRankDomain,
          duplicatedSectionSevenBandFullRank, duplicatedSectionSevenBandParameter]
      have hq : (A.midpointComparisonFourCollarTorus
          (orderFourCayleyHomeomorph b.1) hc0 hcr
          (-A.midpointComparisonFourGauge b.1)
            (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph (Quotient.mk _ v))).1 =
          (orderFourPrincipalGaugeEquiv A.periods).symm
            (regularFamilyInclusion A.periods r) := by
        apply (orderFourRealPeriodProductHomeomorph A.periods).injective
        change (orderFourRealPeriodProductHomeomorph A.periods)
          ((orderFourRealPeriodProductHomeomorph A.periods).symm _) = _
        rw [Homeomorph.apply_symm_apply]
        apply Prod.ext
        · rfl
        · rw [A.midpointComparisonFourGauge_formula, ht]
          rfl
      rw [A.orderFourStarToCentral_mk]
      change A.centralQuotientProjection _ = A.centralQuotientProjection r
      apply congrArg A.centralQuotientProjection
      apply regularFamilyInclusion_injective A.periods
      rw [regularFamilyInclusion_orderFourCollarToRegular]
      change orderFourPrincipalGaugeEquiv A.periods _ = _
      rw [hq, Equiv.apply_symm_apply]

public def midpointComparisonFourFillingToSide :
    C(A.OrderFourVaryingFilling A.starSeparation.orderFour.radius,
      A.actualAffineHeightSplit.allocation.orderFourSide) :=
  (⟨fun x : A.orderFourFillingImage ↦ ⟨x.1, Or.inl x.2⟩,
    continuous_subtype_val.subtype_mk _⟩ : C(_, _)).comp
    (A.orderFourFillingImageToPiece.symm.toHomotopyEquiv.toFun.comp
      A.orderFourPieceHomeomorph.toHomotopyEquiv.toFun)

public theorem midpointComparisonFour_endpoint_in_side
    (b : A.OrderFourAffineHalfPlaneBaseLift)
    (hc0 : 0 < ‖(orderFourCayleyHomeomorph b.1.1 : ℂ)‖)
    (hcr : ‖(orderFourCayleyHomeomorph b.1.1 : ℂ)‖ < A.starSeparation.orderFour.radius)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.midpointComparisonUpperFiberSide (b, t) =
      A.midpointComparisonFourFillingToSide
        (A.midpointComparisonFourFillingTorus (orderFourCayleyHomeomorph b.1.1)
          hc0 hcr (-A.midpointComparisonFourGauge b.1.1)
          (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph t)) := by
  apply Subtype.ext
  apply Subtype.ext
  let q : A.StarCollarSource 2 := Quotient.mk _ (A.midpointComparisonFourCollarTorus
    (orderFourCayleyHomeomorph b.1.1) hc0 hcr
    (-A.midpointComparisonFourGauge b.1.1)
          (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph t))
  let y := A.ellipticCentralImageHomeomorph.symm (A.regularFixedFiberPoint b.1 t)
  change y.1.1 = _
  calc
    y.1.1 = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.regularFixedFiberPoint b.1 t)).1 := by
      have h := A.centralToSectionSevenEulerPiece_centralImage y
      rw [show A.ellipticCentralImageHomeomorph y = A.regularFixedFiberPoint b.1 t
        from A.ellipticCentralImageHomeomorph.apply_symm_apply _] at h
      exact h.symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 2 q)).1 := by
      rw [A.midpointComparisonFourCollarTorus_central b.1 hc0 hcr t]
    _ = A.openEmbeddingStarData.collarSourceToGlued 2 q :=
      A.centralToSectionSevenEulerPiece_starToCentral 2 q
    _ = _ := (A.openEmbeddingStarData.fillingInclusion_toFilling 2 q).symm

public theorem midpointComparisonFour_chosen_inverse :
    ((A.affineOrderFourSideToReducedFiberHomotopyEquiv).toFun.comp
      A.midpointComparisonFourFillingToSide).Homotopic
      (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun := by
  let E := orderFourOverlapIsHomotopyEquivalence_inclusion
    A.orderFourOverlapIsHomotopyEquivalence
  let e := E.toHomotopyEquiv.trans
    (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
      A.orderFourFillingImage
      A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv |>.trans
      A.orderFourFillingImageToPiece.toHomotopyEquiv |>.trans
      A.orderFourPieceHomeomorph.symm.toHomotopyEquiv
  have he : e.invFun = A.midpointComparisonFourFillingToSide := by
    dsimp only [e, ContinuousMap.HomotopyEquiv.trans]
    rw [E.toHomotopyEquiv_invFun]
    apply ContinuousMap.ext
    intro x
    rfl
  have h := ContinuousMap.Homotopic.comp
    (.refl (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun) e.right_inv
  rw [he] at h
  convert h using 2 <;> rfl


public theorem midpointComparisonSlice_upper :
    (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).comp A.midpointComparisonSlice =
      A.midpointComparisonUpperFiberSide.comp
        ((ContinuousMap.const _ (A.affineNormalizedOrderFourHalfPlaneLift affineStripMidpoint)).prodMk
          (ContinuousMap.id (AdditiveTorus A.duplicatedSectionSevenBandParameter))) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have h := A.affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.affineCentralSeparation (affineStripMidpoint, t)
  have hb := A.affineNamedStripLift_apply_midpoint
  change _ = A.regularFixedFiberPoint (A.affineNamedStripLift.lift affineStripMidpoint) t at h
  rw [hb] at h
  have hv := congrArg (fun x : A.CentralFamily ↦
    (A.ellipticCentralImageHomeomorph.symm x).1) h
  simp only [affineCentralBandToCentralFamily, Homeomorph.symm_apply_apply] at hv
  change _ = (A.ellipticCentralImageHomeomorph.symm
    (A.regularFixedFiberPoint (A.affineNormalizedStripContinuousLift affineStripMidpoint) t)).1
  rw [A.affineNormalizedStripContinuousLift_midpoint]
  exact hv


public theorem midpointComparison_regular_four_positive
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    0 < ‖(orderFourCayleyHomeomorph b.1 : ℂ)‖ := by
  apply norm_pos_iff.mpr
  apply EllipticLogarithmicGauge.coe_ne_zero_of_ne_center
  intro hzero
  have hfixed : b.1 = SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint := by
    apply orderFourCayleyHomeomorph.injective
    simpa [orderFourCayleyHomeomorph, UpperHalfPlane.cayleyHomeomorph,
      UpperHalfPlane.cayleyToDisc, ComplexUnitDisc.center, orderFourCayley_fixedPoint] using hzero
  have hm := (A.isRegularBasePoint_iff_coordinate_mem _).mp b.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm
  exact hm.2 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_two)


public theorem midpointComparisonFour_compatibility :
    (affineOrderFourBandToReducedFiber
      (orderFourOverlapIsHomotopyEquivalence_inclusion
        A.orderFourOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderFourCoverMap A) := by
  let : ContractibleSpace affineVerticalStrip := affineVerticalStrip_contractibleSpace
  apply ContinuousMap.Homotopic.of_product_slice
    A.midpointComparisonProduct affineStripMidpoint
  let b := A.affineNormalizedOrderFourHalfPlaneLift affineStripMidpoint
  let r := A.affineOrderFourMarkedDiscRadius
  have hr0 : 0 < r := A.affineOrderFourMarkedDiscRadius_spec.1
  have hr : r ≤ 1 - 1 / 3 := A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderFourBaseRadialEquiv (s := r / 2) (by linarith) (by linarith) hr
  let z := E.toFun (E.invFun b)
  have hz0 := A.midpointComparison_regular_four_positive z.1
  have hzr : ‖(orderFourCayleyHomeomorph z.1.1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := A.affineNormalizedOrderFourRadialLift_midpoint_cayley
  let H := A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.toHomotopyEquiv.toFun
  let q := (A.midpointComparisonFourFillingTorus (orderFourCayleyHomeomorph z.1.1)
    hz0 hzr (-A.midpointComparisonFourGauge z.1.1)).comp H
  have hrad := A.midpointComparisonUpperRadialHomotopy
    (s := r / 2) (by linarith) (by linarith) hr b
  have hend : A.midpointComparisonUpperFiberSide.comp
      ((ContinuousMap.const _ z).prodMk (ContinuousMap.id _)) =
      A.midpointComparisonFourFillingToSide.comp q := by
    apply ContinuousMap.ext
    intro t
    exact A.midpointComparisonFour_endpoint_in_side z hz0 hzr t
  have hside : ((IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).comp
        A.midpointComparisonSlice).Homotopic (A.midpointComparisonFourFillingToSide.comp q) := by
    rw [A.midpointComparisonSlice_upper, ← hend]
    exact ⟨hrad⟩
  have h₁ := ContinuousMap.Homotopic.comp
    (.refl A.affineOrderFourSideToReducedFiberHomotopyEquiv.toFun) hside
  have h₂ := ContinuousMap.Homotopic.comp A.midpointComparisonFour_chosen_inverse (.refl q)
  have h₃ := ContinuousMap.Homotopic.comp
    (A.midpointComparisonFourFillingTorus_homotopic
      (orderFourCayleyHomeomorph z.1.1) hz0 hzr (-A.midpointComparisonFourGauge z.1.1)) (.refl H)
  rw [ContinuousMap.comp_assoc] at h₃
  rw [ContinuousMap.comp_assoc] at h₂
  have h := h₁.trans (h₂.trans h₃)
  convert h using 1
  · rfl
  · apply ContinuousMap.ext
    intro t
    change (orderFourRadialActionData A.periods).centralFiberCoverProjection
      ((orderFourRadialActionData A.periods).centralFiberCoverSourceHomeomorph.symm
        (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
          (A.midpointComparisonProduct
            (A.midpointComparisonProduct.symm (affineStripMidpoint, t))).2)) = _
    rw [Homeomorph.apply_symm_apply]
    rfl


end SphereSixComplex.Geometry.AnalyticData
