module

public import SphereSixComplex.Paper.Topology.EllipticDiscCircleHomology
public import SphereSixComplex.Paper.Topology.EllipticDiscCircleGauge
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Geometry.PaperMarkedPuncturedBase
public import SphereSixComplex.Prerequisites.Topology.LoopProductHomology

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Hurewicz.Chains

namespace SphereSixComplex.Geometry.EllipticDiscCircle

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open AnalyticData AnalyticTorusFamily ComplexTorus RealPeriodTrivialization
open EllipticFamilySpecialization EllipticFixedPointCriterion EllipticVaryingFamilyQuotient
open EllipticCayleyHomeomorph EllipticLinearCollarGlobalDescent GlobalTorusFamily
open EllipticWholeFiberCompactCover FuchsianArithmeticTermination

variable {U : TriangleUniformization}

def fixedGaugeLift (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (z : C(unitInterval, UpperHalfPlane)) (c : C(unitInterval, ℂ)) (a : IntegerPeriods) :
    C(unitInterval, ComplexTwoSpace) :=
  ⟨fun t ↦ (movingToFixedCover F z₀
      (z t, c t • periodVector (parameterMap F (z t)).1 a)).2,
    continuous_snd.comp ((movingToFixedCover_continuous F z₀).comp
      (z.continuous.prodMk (c.continuous.smul
        ((periodSection_contMDiff F a 0).continuous.comp z.continuous))))⟩

theorem fixedGaugeLift_endpoint (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (z : C(unitInterval, UpperHalfPlane)) (c : C(unitInterval, ℂ)) (a : IntegerPeriods)
    (hz : z 1 = z 0) (hc : c 1 = c 0 + 1) :
    fixedGaugeLift F z₀ z c a 1 =
      periodVector (parameterMap F z₀).1 a + fixedGaugeLift F z₀ z c a 0 := by
  change (movingToFixedCover F z₀
    (z 1, c 1 • periodVector (parameterMap F (z 1)).1 a)).2 = _
  rw [hz, hc, add_smul, one_smul, add_comm (c 0 • _)]
  exact congrArg Prod.snd (movingToFixedCover_period_add F z₀ (z 0) a _)

def fixedGaugePath (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (z : C(unitInterval, UpperHalfPlane)) (c : C(unitInterval, ℂ)) (a : IntegerPeriods)
    (hz : z 1 = z 0) (hc : c 1 = c 0 + 1) :
    Path (fixedGaugeLift F z₀ z c a 0)
      (periodVector (parameterMap F z₀).1 a + fixedGaugeLift F z₀ z c a 0) where
  toContinuousMap := fixedGaugeLift F z₀ z c a
  source' := rfl
  target' := fixedGaugeLift_endpoint F z₀ z c a hz hc

theorem periodProjection_endpoint (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (a : IntegerPeriods) (v : ComplexTwoSpace) :
    (Quotient.mk _ v : AdditiveTorus (parameterMap F z₀).1) =
      Quotient.mk _ (periodVector (parameterMap F z₀).1 a + v) := by
  symm
  exact (quotient_eq_iff_exists_period _ _).mpr ⟨a, rfl⟩

def fixedGaugeLoop (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (z : C(unitInterval, UpperHalfPlane)) (c : C(unitInterval, ℂ)) (a : IntegerPeriods)
    (hz : z 1 = z 0) (hc : c 1 = c 0 + 1) :
    Path (Quotient.mk _ (fixedGaugeLift F z₀ z c a 0) : AdditiveTorus (parameterMap F z₀).1)
      (Quotient.mk _ (fixedGaugeLift F z₀ z c a 0)) :=
  ((fixedGaugePath F z₀ z c a hz hc).map continuous_quot_mk).cast rfl
    (periodProjection_endpoint F z₀ a _)

def fixedPeriodLoop (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (a : IntegerPeriods) (v : ComplexTwoSpace) :
    Path (Quotient.mk _ v : AdditiveTorus (parameterMap F z₀).1) (Quotient.mk _ v) :=
  ((Path.segment v (periodVector (parameterMap F z₀).1 a + v)).map
    continuous_quot_mk).cast rfl (periodProjection_endpoint F z₀ a v)

theorem fixedGaugeLoop_homology_split
    {B Y : Type} [TopologicalSpace B] [TopologicalSpace Y] {b : B}
    (F : PeriodFunctions U) (z₀ : UpperHalfPlane)
    (z : C(unitInterval, UpperHalfPlane)) (c : C(unitInterval, ℂ)) (a : IntegerPeriods)
    (hz : z 1 = z 0) (hc : c 1 = c 0 + 1) (p : Path b b)
    (f : C(B × AdditiveTorus (parameterMap F z₀).1, Y)) :
    loopHomologyClass ((p.prod (fixedGaugeLoop F z₀ z c a hz hc)).map f.continuous) =
      loopHomologyClass (((Path.refl b).prod
        (fixedPeriodLoop F z₀ a (fixedGaugeLift F z₀ z c a 0))).map f.continuous) +
      loopHomologyClass ((p.prod
        (Path.refl (Quotient.mk _ (fixedGaugeLift F z₀ z c a 0)))).map f.continuous) := by
  exact loopHomologyClass_prod_map_of_lift p (fixedGaugePath F z₀ z c a hz hc)
    (Path.segment _ _) ⟨Quotient.mk _, continuous_quot_mk⟩
    (periodProjection_endpoint F z₀ a _) f

abbrev PuncturedDiscBall (r : ℝ) := {w : ComplexDiscBall r // (w.val.val : ℂ) ≠ 0}

def orderThreeProductToCollar (A : AnalyticData) (r : ℝ) :
    C(PuncturedDiscBall r × A.OrderThreeTorus,
      orderThreePuncturedFamilyCollar A.periods r) where
  toFun q := ⟨(orderThreeRealPeriodProductHomeomorph A.periods).symm (q.1.val.val, q.2), by
    have hb := congrArg Prod.fst
      ((orderThreeRealPeriodProductHomeomorph A.periods).apply_symm_apply (q.1.val.val, q.2))
    rw [orderThreeRealPeriodProductHomeomorph_fst] at hb
    change 0 < ‖(orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods _)).val‖ ∧
        ‖(orderThreeCayleyHomeomorph (familyTotalSpaceBase A.periods _)).val‖ < r
    rw [hb]
    exact ⟨norm_pos_iff.mpr q.1.property, q.1.val.property⟩⟩
  continuous_toFun := ((orderThreeRealPeriodProductHomeomorph A.periods).symm.continuous.comp
    (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
      continuous_snd)).subtype_mk _

def orderThreeProductToRegular (A : AnalyticData) :
    C(PuncturedDiscBall A.starSeparation.orderThree.radius × A.OrderThreeTorus,
      RegularTotalSpace A.periods) :=
  ⟨fun q ↦ orderThreeCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderThree.sourceData
      (orderThreeProductToCollar A A.starSeparation.orderThree.radius q),
    (orderThreeCollarToRegular_isOpenEmbedding A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderThree.sourceData).continuous.comp
          (orderThreeProductToCollar A A.starSeparation.orderThree.radius).continuous⟩

def orderThreeProductToCentral (A : AnalyticData) :
    C(PuncturedDiscBall A.starSeparation.orderThree.radius × A.OrderThreeTorus,
      A.CentralFamily) := by
  let _ := regularFamilyDeckAction A.periods
  exact ⟨fun q ↦ quotientProjection (orderThreeProductToRegular A q),
    continuous_quot_mk.comp (orderThreeProductToRegular A).continuous⟩

def orderFourProductToCollar (A : AnalyticData) (r : ℝ) :
    C(PuncturedDiscBall r × A.OrderFourTorus,
      orderFourPuncturedFamilyCollar A.periods r) where
  toFun q := ⟨(orderFourRealPeriodProductHomeomorph A.periods).symm (q.1.val.val, q.2), by
    have hb := congrArg Prod.fst
      ((orderFourRealPeriodProductHomeomorph A.periods).apply_symm_apply (q.1.val.val, q.2))
    rw [orderFourRealPeriodProductHomeomorph_fst] at hb
    change 0 < ‖(orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods _)).val‖ ∧
        ‖(orderFourCayleyHomeomorph (familyTotalSpaceBase A.periods _)).val‖ < r
    rw [hb]
    exact ⟨norm_pos_iff.mpr q.1.property, q.1.val.property⟩⟩
  continuous_toFun := ((orderFourRealPeriodProductHomeomorph A.periods).symm.continuous.comp
    (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
      continuous_snd)).subtype_mk _

def orderFourProductToRegular (A : AnalyticData) :
    C(PuncturedDiscBall A.starSeparation.orderFour.radius × A.OrderFourTorus,
      RegularTotalSpace A.periods) :=
  ⟨fun q ↦ orderFourCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderFour.sourceData
      (orderFourProductToCollar A A.starSeparation.orderFour.radius q),
    (orderFourCollarToRegular_isOpenEmbedding A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderFour.sourceData).continuous.comp
          (orderFourProductToCollar A A.starSeparation.orderFour.radius).continuous⟩

def orderFourProductToCentral (A : AnalyticData) :
    C(PuncturedDiscBall A.starSeparation.orderFour.radius × A.OrderFourTorus,
      A.CentralFamily) := by
  let _ := regularFamilyDeckAction A.periods
  exact ⟨fun q ↦ quotientProjection (orderFourProductToRegular A q),
    continuous_quot_mk.comp (orderFourProductToRegular A).continuous⟩


open EllipticLogarithmicGauge SphereSixComplex.LatticeData

theorem orderThreeGauge_product (F : PeriodFunctions U) (z : UpperHalfPlane) (l : ℂ)
    (hl : Complex.exp l = (orderThreeCayleyHomeomorph z : ℂ)) :
    orderThreeRealPeriodProductHomeomorph F
      (orderThreePrincipalGaugeEquiv F (Quotient.mk _ (z, 0))) =
      (orderThreeCayleyHomeomorph z, Quotient.mk _
        (movingToFixedCover F U.zOne
          (z, logarithmicGaugeScalar l • periodVector (parameterMap F z).1 epsilon)).2) := by
  rw [orderThreePrincipalGauge_zero_of_exp F z l hl,
    orderThreeRealPeriodProductHomeomorph_mk]

theorem orderFourGauge_product (F : PeriodFunctions U) (z : UpperHalfPlane) (l : ℂ)
    (hl : Complex.exp l = (orderFourCayleyHomeomorph z : ℂ)) :
    orderFourRealPeriodProductHomeomorph F
      (orderFourPrincipalGaugeEquiv F (Quotient.mk _ (z, 0))) =
      (orderFourCayleyHomeomorph z, Quotient.mk _
        (movingToFixedCover F U.zTwo
          (z, logarithmicGaugeScalar l • periodVector (parameterMap F z).1 (-epsilon'))).2) := by
  rw [orderFourPrincipalGauge_zero_of_exp F z l hl,
    orderFourRealPeriodProductHomeomorph_mk]


def scaledPuncturedPoint {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) : PuncturedDiscBall r :=
  ⟨discBallScale hr hr1 w, mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hw⟩

theorem orderThreeDiscToStar_eq_gaugeProduct (A : AnalyticData)
    (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) (l : ℂ)
    (hl : Complex.exp l = (discBallScale A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one w).val.val) :
    let b := scaledPuncturedPoint A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one w hw
    let z := orderThreeCayleyHomeomorph.symm b.val.val
    orderThreeDiscToStar A w = centralInclusion A
      (orderThreeProductToCentral A
        (b, Quotient.mk _ (movingToFixedCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          (z, logarithmicGaugeScalar l • periodVector (parameterMap A.periods z).1 epsilon)).2)) := by
  let _ := regularFamilyDeckAction A.periods
  dsimp only
  rw [orderThreeDiscToStar_eq_central A w hw]
  apply congrArg (centralInclusion A)
  change (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) (orderThreeCollarToRegular A.periods _ _ _) =
    (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) (orderThreeCollarToRegular A.periods _ _ _)
  apply congrArg (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily)
  apply congrArg (orderThreeCollarToRegular A.periods _ _)
  apply Subtype.ext
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  change orderThreeRealPeriodProductHomeomorph A.periods
    (orderThreePrincipalGaugeEquiv A.periods (Quotient.mk _ (_, 0))) =
      orderThreeRealPeriodProductHomeomorph A.periods
        ((orderThreeRealPeriodProductHomeomorph A.periods).symm _)
  rw [Homeomorph.apply_symm_apply]
  convert orderThreeGauge_product A.periods
    (orderThreeCayleyHomeomorph.symm
      (discBallScale A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one w).val) l
    (by simpa only [Homeomorph.apply_symm_apply] using hl) using 1
  simp only [Homeomorph.apply_symm_apply, scaledPuncturedPoint]

theorem orderFourDiscToStar_eq_gaugeProduct (A : AnalyticData)
    (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) (l : ℂ)
    (hl : Complex.exp l = (discBallScale A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one w).val.val) :
    let b := scaledPuncturedPoint A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one w hw
    let z := orderFourCayleyHomeomorph.symm b.val.val
    orderFourDiscToStar A w = centralInclusion A
      (orderFourProductToCentral A
        (b, Quotient.mk _ (movingToFixedCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo
          (z, logarithmicGaugeScalar l • periodVector (parameterMap A.periods z).1 (-epsilon'))).2)) := by
  let _ := regularFamilyDeckAction A.periods
  dsimp only
  rw [orderFourDiscToStar_eq_central A w hw]
  apply congrArg (centralInclusion A)
  change (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) (orderFourCollarToRegular A.periods _ _ _) =
    (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) (orderFourCollarToRegular A.periods _ _ _)
  apply congrArg (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily)
  apply congrArg (orderFourCollarToRegular A.periods _ _)
  apply Subtype.ext
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  change orderFourRealPeriodProductHomeomorph A.periods
    (orderFourPrincipalGaugeEquiv A.periods (Quotient.mk _ (_, 0))) =
      orderFourRealPeriodProductHomeomorph A.periods
        ((orderFourRealPeriodProductHomeomorph A.periods).symm _)
  rw [Homeomorph.apply_symm_apply]
  convert orderFourGauge_product A.periods
    (orderFourCayleyHomeomorph.symm
      (discBallScale A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one w).val) l
    (by simpa only [Homeomorph.apply_symm_apply] using hl) using 1
  simp only [Homeomorph.apply_symm_apply, scaledPuncturedPoint]


def scaledPuncturedLoop {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {b : ComplexUnitDisc} (hb : (b : ℂ) ≠ 0) (p : Path b b)
    (hp : ∀ t, (p t : ℂ) ≠ 0) :
    Path (scaledPuncturedPoint hr hr1 b hb) (scaledPuncturedPoint hr hr1 b hb) where
  toFun t := scaledPuncturedPoint hr hr1 (p t) (hp t)
  continuous_toFun := ((discBallScale hr hr1).continuous.comp p.continuous).subtype_mk _
  source' := by apply Subtype.ext; exact congrArg (discBallScale hr hr1) p.source
  target' := by apply Subtype.ext; exact congrArg (discBallScale hr hr1) p.target

def orderThreeSourceLoop (A : AnalyticData) {b : ComplexUnitDisc}
    (hb : (b : ℂ) ≠ 0) (p : Path b b) (hp : ∀ t, (p t : ℂ) ≠ 0) :
    Path
      (orderThreeCayleyHomeomorph.symm
        (discBallScale A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one b).val)
      (orderThreeCayleyHomeomorph.symm
        (discBallScale A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one b).val) :=
  (scaledPuncturedLoop A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one hb p hp).map
      (orderThreeCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))

theorem orderThree_disc_loop_homology_split (A : AnalyticData) {b : ComplexUnitDisc}
    (hb : (b : ℂ) ≠ 0) (p : Path b b) (hp : ∀ t, (p t : ℂ) ≠ 0)
    (c : C(unitInterval, ℂ)) (hc : c 1 = c 0 + 1)
    (hlog : ∀ t, Complex.exp ((2 * Real.pi * Complex.I) * c t) =
      (discBallScale A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one (p t)).val.val) :
    let bp := scaledPuncturedLoop A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one hb p hp
    let z := (orderThreeSourceLoop A hb p hp).toContinuousMap
    let z₀ := A.modular.modularParameter.toTriangleUniformization.zOne
    let v := fixedGaugeLift A.periods z₀ z c epsilon 0
    let f := (centralInclusion A).comp (orderThreeProductToCentral A)
    0 = loopHomologyClass (((Path.refl (scaledPuncturedPoint A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one b hb)).prod
        (fixedPeriodLoop A.periods z₀ epsilon v)).map f.continuous) +
      loopHomologyClass ((bp.prod (Path.refl (Quotient.mk _ v))).map f.continuous) := by
  dsimp only
  let bp := scaledPuncturedLoop A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one hb p hp
  let z := (orderThreeSourceLoop A hb p hp).toContinuousMap
  let z₀ := A.modular.modularParameter.toTriangleUniformization.zOne
  have hz : z 1 = z 0 := (orderThreeSourceLoop A hb p hp).target.trans
    (orderThreeSourceLoop A hb p hp).source.symm
  let f := (centralInclusion A).comp (orderThreeProductToCentral A)
  have heq : (p.map (orderThreeDiscToStar A).continuous).toContinuousMap =
      ((bp.prod (fixedGaugeLoop A.periods z₀ z c epsilon hz hc)).map
        f.continuous).toContinuousMap := by
    ext t
    have ht := orderThreeDiscToStar_eq_gaugeProduct A (p t) (hp t)
      ((2 * Real.pi * Complex.I) * c t) (hlog t)
    have hc' : logarithmicGaugeScalar ((2 * Real.pi * Complex.I) * c t) = c t := by
      unfold logarithmicGaugeScalar
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    change orderThreeDiscToStar A (p t) = centralInclusion A
      (orderThreeProductToCentral A
        (scaledPuncturedPoint A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one (p t) (hp t),
          Quotient.mk _ (movingToFixedCover A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne
            (orderThreeCayleyHomeomorph.symm
              (discBallScale A.starSeparation.orderThree.radius_pos
                A.starSeparation.orderThree.radius_lt_one (p t)).val,
              c t • periodVector (parameterMap A.periods
                (orderThreeCayleyHomeomorph.symm
                  (discBallScale A.starSeparation.orderThree.radius_pos
                    A.starSeparation.orderThree.radius_lt_one (p t)).val)).1 epsilon)).2))
    simpa only [hc', scaledPuncturedPoint] using ht
  have hzero := orderThreeDiscToStar_loop_eq_zero A p
  have hclass := loopHomologyClass_eq_of_toContinuousMap_eq _ _ heq
  have hsplit := fixedGaugeLoop_homology_split A.periods z₀ z c epsilon hz hc bp f
  exact hzero.symm.trans (hclass.trans hsplit)

def orderFourSourceLoop (A : AnalyticData) {b : ComplexUnitDisc}
    (hb : (b : ℂ) ≠ 0) (p : Path b b) (hp : ∀ t, (p t : ℂ) ≠ 0) :
    Path
      (orderFourCayleyHomeomorph.symm
        (discBallScale A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one b).val)
      (orderFourCayleyHomeomorph.symm
        (discBallScale A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one b).val) :=
  (scaledPuncturedLoop A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one hb p hp).map
      (orderFourCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))

theorem orderFour_disc_loop_homology_split (A : AnalyticData) {b : ComplexUnitDisc}
    (hb : (b : ℂ) ≠ 0) (p : Path b b) (hp : ∀ t, (p t : ℂ) ≠ 0)
    (c : C(unitInterval, ℂ)) (hc : c 1 = c 0 + 1)
    (hlog : ∀ t, Complex.exp ((2 * Real.pi * Complex.I) * c t) =
      (discBallScale A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one (p t)).val.val) :
    let bp := scaledPuncturedLoop A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one hb p hp
    let z := (orderFourSourceLoop A hb p hp).toContinuousMap
    let z₀ := A.modular.modularParameter.toTriangleUniformization.zTwo
    let v := fixedGaugeLift A.periods z₀ z c (-epsilon') 0
    let f := (centralInclusion A).comp (orderFourProductToCentral A)
    0 = loopHomologyClass (((Path.refl (scaledPuncturedPoint A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one b hb)).prod
        (fixedPeriodLoop A.periods z₀ (-epsilon') v)).map f.continuous) +
      loopHomologyClass ((bp.prod (Path.refl (Quotient.mk _ v))).map f.continuous) := by
  dsimp only
  let bp := scaledPuncturedLoop A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one hb p hp
  let z := (orderFourSourceLoop A hb p hp).toContinuousMap
  let z₀ := A.modular.modularParameter.toTriangleUniformization.zTwo
  have hz : z 1 = z 0 := (orderFourSourceLoop A hb p hp).target.trans
    (orderFourSourceLoop A hb p hp).source.symm
  let f := (centralInclusion A).comp (orderFourProductToCentral A)
  have heq : (p.map (orderFourDiscToStar A).continuous).toContinuousMap =
      ((bp.prod (fixedGaugeLoop A.periods z₀ z c (-epsilon') hz hc)).map
        f.continuous).toContinuousMap := by
    ext t
    have ht := orderFourDiscToStar_eq_gaugeProduct A (p t) (hp t)
      ((2 * Real.pi * Complex.I) * c t) (hlog t)
    have hc' : logarithmicGaugeScalar ((2 * Real.pi * Complex.I) * c t) = c t := by
      unfold logarithmicGaugeScalar
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    change orderFourDiscToStar A (p t) = centralInclusion A
      (orderFourProductToCentral A
        (scaledPuncturedPoint A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one (p t) (hp t),
          Quotient.mk _ (movingToFixedCover A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo
            (orderFourCayleyHomeomorph.symm
              (discBallScale A.starSeparation.orderFour.radius_pos
                A.starSeparation.orderFour.radius_lt_one (p t)).val,
              c t • periodVector (parameterMap A.periods
                (orderFourCayleyHomeomorph.symm
                  (discBallScale A.starSeparation.orderFour.radius_pos
                    A.starSeparation.orderFour.radius_lt_one (p t)).val)).1 (-epsilon'))).2))
    simpa only [hc', scaledPuncturedPoint] using ht
  have hzero := orderFourDiscToStar_loop_eq_zero A p
  have hclass := loopHomologyClass_eq_of_toContinuousMap_eq _ _ heq
  have hsplit := fixedGaugeLoop_homology_split A.periods z₀ z c (-epsilon') hz hc bp f
  exact hzero.symm.trans (hclass.trans hsplit)


theorem orderThreeProductToRegular_coordinates (A : AnalyticData)
    (q : PuncturedDiscBall A.starSeparation.orderThree.radius × A.OrderThreeTorus) :
    orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods (orderThreeProductToRegular A q)) = (q.1.val.val, q.2) := by
  change orderThreeRealPeriodProductHomeomorph A.periods
    (regularFamilyInclusion A.periods (orderThreeCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction) _ _)) = _
  rw [regularFamilyInclusion_orderThreeCollarToRegular]
  exact (orderThreeRealPeriodProductHomeomorph A.periods).apply_symm_apply _

theorem orderThreeProductToRegular_base (A : AnalyticData)
    (q : PuncturedDiscBall A.starSeparation.orderThree.radius × A.OrderThreeTorus) :
    (regularTotalSpaceBase A.periods (orderThreeProductToRegular A q)).val =
      orderThreeCayleyHomeomorph.symm q.1.val.val := by
  apply orderThreeCayleyHomeomorph.injective
  have h := congrArg Prod.fst (orderThreeProductToRegular_coordinates A q)
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at h
  simpa only [Homeomorph.apply_symm_apply] using h

theorem orderThreeProductToRegular_zero (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderThree.radius) :
    orderThreeProductToRegular A (b, 0) = regularFamilyZeroSection A.periods
      (regularTotalSpaceBase A.periods (orderThreeProductToRegular A (b, 0))) := by
  have hcoord := orderThreeProductToRegular_coordinates A (b, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  rw [hcoord]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion, orderThreeRealPeriodProductHomeomorph_mk]
  apply Prod.ext
  · exact hbase.symm
  · simp only [movingToFixedCover, periodCoordinates, map_zero]
    exact (additiveTorus_mk_zero _).symm

theorem orderFourProductToRegular_coordinates (A : AnalyticData)
    (q : PuncturedDiscBall A.starSeparation.orderFour.radius × A.OrderFourTorus) :
    orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods (orderFourProductToRegular A q)) = (q.1.val.val, q.2) := by
  change orderFourRealPeriodProductHomeomorph A.periods
    (regularFamilyInclusion A.periods (orderFourCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction) _ _)) = _
  rw [regularFamilyInclusion_orderFourCollarToRegular]
  exact (orderFourRealPeriodProductHomeomorph A.periods).apply_symm_apply _

theorem orderFourProductToRegular_base (A : AnalyticData)
    (q : PuncturedDiscBall A.starSeparation.orderFour.radius × A.OrderFourTorus) :
    (regularTotalSpaceBase A.periods (orderFourProductToRegular A q)).val =
      orderFourCayleyHomeomorph.symm q.1.val.val := by
  apply orderFourCayleyHomeomorph.injective
  have h := congrArg Prod.fst (orderFourProductToRegular_coordinates A q)
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at h
  simpa only [Homeomorph.apply_symm_apply] using h

theorem orderFourProductToRegular_zero (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderFour.radius) :
    orderFourProductToRegular A (b, 0) = regularFamilyZeroSection A.periods
      (regularTotalSpaceBase A.periods (orderFourProductToRegular A (b, 0))) := by
  have hcoord := orderFourProductToRegular_coordinates A (b, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  apply regularFamilyInclusion_injective A.periods
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  rw [hcoord]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion, orderFourRealPeriodProductHomeomorph_mk]
  apply Prod.ext
  · exact hbase.symm
  · simp only [movingToFixedCover, periodCoordinates, map_zero]
    exact (additiveTorus_mk_zero _).symm


theorem loopHomologyClass_prod_refl_map_eq
    {B T Y : Type} [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace Y]
    {b : B} {c d : T} (p : Path b b) (W : Path c d) (f : C(B × T, Y)) :
    loopHomologyClass ((p.prod (Path.refl c)).map f.continuous) =
      loopHomologyClass ((p.prod (Path.refl d)).map f.continuous) := by
  let H : ContinuousMap.Homotopy
      ((p.prod (Path.refl c)).map f.continuous).toContinuousMap
      ((p.prod (Path.refl d)).map f.continuous).toContinuousMap :=
    { toFun := fun st ↦ f (p st.2, W st.1)
      continuous_toFun := f.continuous.comp
        ((p.continuous.comp continuous_snd).prodMk (W.continuous.comp continuous_fst))
      map_zero_left := by intro t; simp
      map_one_left := by intro t; simp }
  exact loopHomologyClass_eq_of_freeHomotopy _ _ H (by
    intro t
    change f (p 0, W t) = f (p 1, W t)
    rw [p.source, p.target])


theorem baseLoop_homology_zeroFiber
    {B Y : Type} [TopologicalSpace B] [TopologicalSpace Y] {b : B}
    (F : PeriodFunctions U) (z₀ : UpperHalfPlane) (p : Path b b) (v : ComplexTwoSpace)
    (f : C(B × AdditiveTorus (parameterMap F z₀).1, Y)) :
    loopHomologyClass ((p.prod (Path.refl (Quotient.mk _ v))).map f.continuous) =
      loopHomologyClass ((p.prod (Path.refl 0)).map f.continuous) := by
  let W : Path (Quotient.mk _ v : AdditiveTorus (parameterMap F z₀).1) 0 :=
    ((Path.segment v 0).map continuous_quot_mk).cast rfl (additiveTorus_mk_zero _).symm
  exact loopHomologyClass_prod_refl_map_eq p W f

end SphereSixComplex.Geometry.EllipticDiscCircle
