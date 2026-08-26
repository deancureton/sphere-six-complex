module

public import SphereSixComplex.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Geometry.EllipticUniformizerCayleyComparison
public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
import all SphereSixComplex.Geometry.CuspPuncturedCollarBridge
import all SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# Pairwise separation of the three filling collars

The elliptic collars must be shrunk simultaneously: each avoids the closed orbit-saturation of
the selected cusp horodisc, and their images in the Fuchsian base quotient are disjoint.
-/

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily GlobalTorusFamily EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover EllipticPuncturedCollarGaugeHomeomorph
open EllipticVaryingFamilyQuotient EllipticAffineGlobalSeparation
open EllipticLinearCollarGlobalDescent StandardInfiniteA2ToricModel
open StandardInfiniteA2ToricQuantitativeRegions.BoundedPolydiscRegions
open CuspPeriodExpansion CuspPuncturedCollarBridge EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Equality in the punctured global family forces the corresponding regular source points to
lie in one triangle-group orbit. -/
public theorem regularBase_orbit_of_global_eq
    {U : TriangleUniformization} (F : PeriodFunctions U)
    {x y : RegularTotalSpace F}
    (h : (Quotient.mk _ x : PuncturedGlobalFamily F) = Quotient.mk _ y) :
    ∃ g : Delta,
      U.sourceAction g • (regularTotalSpaceBase F y).1 =
        (regularTotalSpaceBase F x).1 := by
  let _ := regularFamilyDeckAction F
  have hrel := Quotient.exact h
  change MulAction.orbitRel Delta (RegularTotalSpace F) x y at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  refine ⟨g, ?_⟩
  change regularFamilyDeckMap F g y = x at hg
  calc
    U.sourceAction g • (regularTotalSpaceBase F y).1 =
        (regularTotalSpaceBase F (regularFamilyDeckMap F g y)).1 :=
      congrArg Subtype.val (regularTotalSpaceBase_familyDeckMap F g y).symm
    _ = (regularTotalSpaceBase F x).1 :=
      congrArg (fun z ↦ (regularTotalSpaceBase F z).1) hg

public theorem orderThreeCollarToRegular_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : (orderThreeLinearPuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F (orderThreeCollarToRegular F hproper D q)).1 =
      familyTotalSpaceBase F q := by
  have h := congrArg (familyTotalSpaceBase F)
    (regularFamilyInclusion_orderThreeCollarToRegular F hproper D q)
  rw [familyTotalSpaceBase_regularFamilyInclusion] at h
  exact h

public theorem orderFourCollarToRegular_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : (orderFourLinearPuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F (orderFourCollarToRegular F hproper D q)).1 =
      familyTotalSpaceBase F q := by
  have h := congrArg (familyTotalSpaceBase F)
    (regularFamilyInclusion_orderFourCollarToRegular F hproper D q)
  rw [familyTotalSpaceBase_regularFamilyInclusion] at h
  exact h

/-- The quantitative local cusp witness attached to the selected analytic package. -/
@[expose] public noncomputable def actualLocalCuspWitness :
    ActualLocalCuspQuotientWitness A.cuspCoordinate A.toricModel :=
  Classical.choice (exists_actualLocalCuspQuotientWitness A.cuspCoordinate A.toricModel
    A.toricModel.toTorusActionPreservesComponents)

/-- The fixed exact modular uniformization used to control the paper cusp collar. -/
@[expose] public noncomputable def actualNormalizedModularJUniformization
    (_A : PaperAnalyticData) :
    ExactNormalizedModularJUniformization :=
  Classical.choice establishedExactNormalizedModularJUniformization

/-- Analytic facts retained by the quantitative choice of the actual cusp collar.  In addition
to placing the quotient coordinate in the exterior region, this records the exact reciprocal
factorization and the nonvanishing domain of its holomorphic unit. -/
public structure ActualCuspCoordinateControl
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) : Prop where
  coordinate_exterior : ∀ s : ℂ, s ∈ cuspHalfPlane A.cuspCoordinate.height →
    ‖cuspQ s‖ < W.localWitness.radius →
      2 < ‖A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s)‖
  radius_le_cuspUnitRadius :
    W.localWitness.radius ≤ A.actualNormalizedModularJUniformization.cusp.cuspRadius
  cuspUnit_ne : ∀ q : ℂ, ‖q‖ < W.localWitness.radius →
    A.actualNormalizedModularJUniformization.cusp.cuspUnit q ≠ 0
  cuspProduct_norm_lt_half : ∀ q : ℂ, ‖q‖ < W.localWitness.radius →
    ‖q * A.actualNormalizedModularJUniformization.cusp.cuspUnit q‖ < (1 / 2 : ℝ)
  reciprocal_factorization : ∀ s : ℂ,
    s ∈ cuspHalfPlane A.cuspCoordinate.height →
    ‖cuspQ s‖ < W.localWitness.radius →
      (A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s))⁻¹ =
        cuspQ s * A.actualNormalizedModularJUniformization.cusp.cuspUnit (cuspQ s)

/-- A common-radius cusp witness can be chosen far enough into the normalized cusp that the
actual source quotient coordinate has norm greater than two throughout the selected horodisc.
This turns the asymptotic simple-cusp factorization into a quantitative fact about every point
used by the later toric collar. -/
public theorem exists_actualPuncturedCuspWitness_coordinate_exterior :
    ∃ W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel,
      A.ActualCuspCoordinateControl W := by
  let J : ExactNormalizedModularJUniformization :=
    A.actualNormalizedModularJUniformization
  obtain ⟨H, hH⟩ :=
    (eventually_upperHalfPlaneAtInfinity_iff (P := fun z ↦
      (normalizedModularJCoordinate z)⁻¹ =
          modularCuspQ z * J.cusp.cuspUnit (modularCuspQ z) ∧
        normalizedModularJCoordinate z ≠ 0)).mp
      (J.cusp.reciprocal_factorization.and
        J.cusp.coordinate_eventually_ne_zero)
  let M : ℝ := ‖J.cusp.cuspUnit 0‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hunitContinuous : ContinuousAt J.cusp.cuspUnit 0 :=
    (J.cusp.cuspUnit_holomorphic 0
      (by simpa using J.cusp.cuspRadius_pos)).continuousAt
  have hunitEventually : ∀ᶠ q in nhds (0 : ℂ), ‖J.cusp.cuspUnit q‖ < M := by
    exact hunitContinuous.norm.eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  have hunitNeEventually : ∀ᶠ q in nhds (0 : ℂ), J.cusp.cuspUnit q ≠ 0 :=
    hunitContinuous.eventually_ne J.cusp.cuspUnit_zero_ne
  obtain ⟨δ, hδ, hδunit⟩ :=
    Metric.mem_nhds_iff.mp (hunitEventually.and hunitNeEventually)
  let r : ℝ := min A.actualLocalCuspWitness.radius
    (min δ (min J.cusp.cuspRadius (min (cuspRadius H) (1 / (2 * M)))))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min A.actualLocalCuspWitness.radius_pos
      (lt_min hδ (lt_min J.cusp.cuspRadius_pos
        (lt_min (cuspRadius_pos H) (by positivity))))
  have hrLocal : r ≤ A.actualLocalCuspWitness.radius := min_le_left _ _
  let W₀ := restrictActualLocalCuspQuotientWitness
    A.actualLocalCuspWitness r hr hrLocal
  obtain ⟨S⟩ := EstablishedFuchsianCuspNeighborhood.Established.data
    A.cuspCoordinate W₀.radius W₀.radius_pos
  let W₁ := restrictActualLocalCuspQuotientWitness
    W₀ S.radius S.radius_pos S.radius_le_upper
  let W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel :=
    ⟨W₁, S.region_open, S.region_regular, S.orbitClosure_region_regular,
      S.translates_meet_only_parabolic⟩
  refine ⟨W, ?_⟩
  have hWr : W.localWitness.radius ≤ r := by
    exact S.radius_le_upper
  have hWJ : W.localWitness.radius ≤ J.cusp.cuspRadius :=
    hWr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hWunit : ∀ q : ℂ, ‖q‖ < W.localWitness.radius → J.cusp.cuspUnit q ≠ 0 := by
    intro q hq
    apply (hδunit ?_).2
    rw [Metric.mem_ball, dist_zero_right]
    exact hq.trans_le (hWr.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hWproduct : ∀ q : ℂ, ‖q‖ < W.localWitness.radius →
      ‖q * J.cusp.cuspUnit q‖ < (1 / 2 : ℝ) := by
    intro q hq
    by_cases hq0 : q = 0
    · simp [hq0]
    have hqr : ‖q‖ < r := hq.trans_le hWr
    have hqδ : q ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hqr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hunit : ‖J.cusp.cuspUnit q‖ < M := (hδunit hqδ).1
    have hqsmall : ‖q‖ < 1 / (2 * M) :=
      hqr.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    rw [norm_mul]
    calc
      ‖q‖ * ‖J.cusp.cuspUnit q‖ < ‖q‖ * M :=
        mul_lt_mul_of_pos_left hunit (norm_pos_iff.mpr hq0)
      _ < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hqsmall hM
      _ = 1 / 2 := by field_simp
  refine ⟨?_, hWJ, hWunit, hWproduct, ?_⟩
  · intro s hs hq
    have hqr : ‖cuspQ s‖ < r := hq.trans_le hWr
    have hqδ : cuspQ s ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hqr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hunit : ‖J.cusp.cuspUnit (cuspQ s)‖ < M := (hδunit hqδ).1
    have hqsmall : ‖cuspQ s‖ < 1 / (2 * M) :=
      hqr.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have himH : H ≤ s.im := by
      have hsH : s ∈ cuspHalfPlane H :=
        mem_cuspHalfPlane_of_norm_cuspQ_lt
          ((min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))) hqr
      exact le_of_lt hsH
    let z : UpperHalfPlane := A.periods.tau (A.cuspCoordinate.lift s)
    have hzcoe : (z : ℂ) = s := A.cuspCoordinate.lift_tau s hs
    have hzH : H ≤ z.im := by
      change H ≤ (z : ℂ).im
      rw [hzcoe]
      exact himH
    have hfactor := (hH z hzH).1
    have hcoordNe := (hH z hzH).2
    have hqeq : modularCuspQ z = cuspQ s := by
      unfold modularCuspQ cuspQ Function.Periodic.qParam
      rw [hzcoe]
      congr 1
      norm_num
    rw [hqeq] at hfactor
    have hproduct : ‖cuspQ s * J.cusp.cuspUnit (cuspQ s)‖ < (1 / 2 : ℝ) := by
      rw [norm_mul]
      calc
        ‖cuspQ s‖ * ‖J.cusp.cuspUnit (cuspQ s)‖ < ‖cuspQ s‖ * M :=
          mul_lt_mul_of_pos_left hunit (norm_pos_iff.mpr (Complex.exp_ne_zero _))
        _ < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hqsmall hM
        _ = 1 / 2 := by field_simp
    have hinv : ‖(normalizedModularJCoordinate z)⁻¹‖ < (1 / 2 : ℝ) := by
      rw [hfactor]
      exact hproduct
    have hnormPos : 0 < ‖normalizedModularJCoordinate z‖ := norm_pos_iff.mpr hcoordNe
    have hlarge : 2 < ‖normalizedModularJCoordinate z‖ := by
      rw [norm_inv] at hinv
      have := (inv_lt_comm₀ hnormPos (by norm_num : (0 : ℝ) < 1 / 2)).mp hinv
      norm_num at this
      exact this
    have hsource : A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s) =
        normalizedModularJCoordinate z := by
      have hperiod := A.periods.modular_equation (A.cuspCoordinate.lift s)
      change normalizedJ z = 1728 *
        A.modular.modularParameter.coordinate (A.cuspCoordinate.lift s) at hperiod
      rw [A.modular.induced_coordinate] at hperiod
      change _ = normalizedJ z / 1728
      rw [hperiod]
      ring
    rw [hsource]
    exact hlarge
  · intro s hs hq
    have hqr : ‖cuspQ s‖ < r := by
      exact hq.trans_le hWr
    have himH : H ≤ s.im := by
      have hsH : s ∈ cuspHalfPlane H :=
        mem_cuspHalfPlane_of_norm_cuspQ_lt
          ((min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))) hqr
      exact le_of_lt hsH
    let z : UpperHalfPlane := A.periods.tau (A.cuspCoordinate.lift s)
    have hzcoe : (z : ℂ) = s := A.cuspCoordinate.lift_tau s hs
    have hzH : H ≤ z.im := by
      change H ≤ (z : ℂ).im
      rw [hzcoe]
      exact himH
    have hfactor := (hH z hzH).1
    have hqeq : modularCuspQ z = cuspQ s := by
      unfold modularCuspQ cuspQ Function.Periodic.qParam
      rw [hzcoe]
      congr 1
      norm_num
    rw [hqeq] at hfactor
    have hsource : A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s) =
        normalizedModularJCoordinate z := by
      have hperiod := A.periods.modular_equation (A.cuspCoordinate.lift s)
      change normalizedJ z = 1728 *
        A.modular.modularParameter.coordinate (A.cuspCoordinate.lift s) at hperiod
      rw [A.modular.induced_coordinate] at hperiod
      change _ = normalizedJ z / 1728
      rw [hperiod]
      ring
    rw [hsource]
    exact hfactor

/-- The quantitatively normalized common-radius cusp witness used by the paper star. -/
@[expose] public noncomputable def actualPuncturedCuspWitness :
    ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel :=
  Classical.choose A.exists_actualPuncturedCuspWitness_coordinate_exterior

public theorem actualPuncturedCuspWitness_coordinate_exterior
    (s : ℂ) (hs : s ∈ cuspHalfPlane A.cuspCoordinate.height)
    (hq : ‖cuspQ s‖ < A.actualPuncturedCuspWitness.localWitness.radius) :
    2 < ‖A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s)‖ :=
  (Classical.choose_spec A.exists_actualPuncturedCuspWitness_coordinate_exterior).coordinate_exterior
    s hs hq

public theorem actualPuncturedCuspWitness_radius_le_cuspUnitRadius :
    A.actualPuncturedCuspWitness.localWitness.radius ≤
      A.actualNormalizedModularJUniformization.cusp.cuspRadius :=
  (Classical.choose_spec
    A.exists_actualPuncturedCuspWitness_coordinate_exterior).radius_le_cuspUnitRadius

public theorem actualPuncturedCuspWitness_cuspUnit_ne
    (q : ℂ) (hq : ‖q‖ < A.actualPuncturedCuspWitness.localWitness.radius) :
    A.actualNormalizedModularJUniformization.cusp.cuspUnit q ≠ 0 :=
  (Classical.choose_spec A.exists_actualPuncturedCuspWitness_coordinate_exterior).cuspUnit_ne q hq

public theorem actualPuncturedCuspWitness_cuspProduct_norm_lt_half
    (q : ℂ) (hq : ‖q‖ < A.actualPuncturedCuspWitness.localWitness.radius) :
    ‖q * A.actualNormalizedModularJUniformization.cusp.cuspUnit q‖ < (1 / 2 : ℝ) :=
  (Classical.choose_spec
    A.exists_actualPuncturedCuspWitness_coordinate_exterior).cuspProduct_norm_lt_half q hq

public theorem actualPuncturedCuspWitness_reciprocal_factorization
    (s : ℂ) (hs : s ∈ cuspHalfPlane A.cuspCoordinate.height)
    (hq : ‖cuspQ s‖ < A.actualPuncturedCuspWitness.localWitness.radius) :
    (A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s))⁻¹ =
      cuspQ s * A.actualNormalizedModularJUniformization.cusp.cuspUnit (cuspQ s) :=
  (Classical.choose_spec
    A.exists_actualPuncturedCuspWitness_coordinate_exterior).reciprocal_factorization s hs hq

/-- The completed leading unit for the order-three branch after expressing its arbitrary
uniformizer in the explicit Cayley coordinate. -/
@[expose] public def actualOrderThreeCayleyLeadingUnit (w : ℂ) : ℂ :=
  ellipticCayleyLeadingUnit fuchsianOneFixedPoint 3
    A.modular.sourceCoordinate.branch_one.uniformizer
    A.modular.sourceCoordinate.branch_one.unit w

/-- The analogous completed leading unit at the order-four branch. -/
@[expose] public def actualOrderFourCayleyLeadingUnit (w : ℂ) : ℂ :=
  ellipticCayleyLeadingUnit fuchsianTwoFixedPoint 4
    A.modular.sourceCoordinate.branch_two.uniformizer
    A.modular.sourceCoordinate.branch_two.unit w

public theorem continuousAt_actualOrderThreeCayleyLeadingUnit_zero :
    ContinuousAt A.actualOrderThreeCayleyLeadingUnit 0 :=
  continuousAt_ellipticCayleyLeadingUnit_zero
    (A.modular.sourceCoordinate.branch_one.uniformizer_isLocalDiffeomorph.mdifferentiableAt
      (by simp))
    A.modular.sourceCoordinate.branch_one.unit_holomorphic

public theorem continuousAt_actualOrderFourCayleyLeadingUnit_zero :
    ContinuousAt A.actualOrderFourCayleyLeadingUnit 0 :=
  continuousAt_ellipticCayleyLeadingUnit_zero
    (A.modular.sourceCoordinate.branch_two.uniformizer_isLocalDiffeomorph.mdifferentiableAt
      (by simp))
    A.modular.sourceCoordinate.branch_two.unit_holomorphic

public theorem actualOrderThreeCayleyLeadingUnit_zero_ne :
    A.actualOrderThreeCayleyLeadingUnit 0 ≠ 0 :=
  ellipticCayleyLeadingUnit_zero_ne
    A.modular.sourceCoordinate.branch_one.uniformizer_center
    A.modular.sourceCoordinate.branch_one.uniformizer_isLocalDiffeomorph
    A.modular.sourceCoordinate.branch_one.unit_ne_zero

public theorem actualOrderFourCayleyLeadingUnit_zero_ne :
    A.actualOrderFourCayleyLeadingUnit 0 ≠ 0 :=
  ellipticCayleyLeadingUnit_zero_ne
    A.modular.sourceCoordinate.branch_two.uniformizer_center
    A.modular.sourceCoordinate.branch_two.uniformizer_isLocalDiffeomorph
    A.modular.sourceCoordinate.branch_two.unit_ne_zero

/-- Simultaneously shrunk elliptic radii, separated from one another and from the cusp orbit. -/
public structure CollarSeparationData
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) where
  orderThree : A.OrderThreeFillingPiece
  orderFour : A.OrderFourFillingPiece
  /-- The whole selected order-three Cayley ball lies in the exact ramification
  neighbourhood of the normalized quotient coordinate. -/
  orderThree_branch_factorization : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      A.modular.sourceCoordinate.coordinate z =
          A.modular.sourceCoordinate.branch_one.uniformizer z ^ 3 *
            A.modular.sourceCoordinate.branch_one.unit z ∧
        A.modular.sourceCoordinate.branch_one.unit z ≠ 0
  /-- The whole selected order-four Cayley ball lies in the exact ramification
  neighbourhood of the normalized quotient coordinate. -/
  orderFour_branch_factorization : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      A.modular.sourceCoordinate.coordinate z - 1 =
          A.modular.sourceCoordinate.branch_two.uniformizer z ^ 4 *
          A.modular.sourceCoordinate.branch_two.unit z ∧
        A.modular.sourceCoordinate.branch_two.unit z ≠ 0
  /-- On the selected order-three Cayley ball, the transition factor from the arbitrary analytic
  branch uniformizer to the explicit Cayley coordinate is continuous and nonvanishing. -/
  orderThree_cayleyFactor_control : ∀ w : ℂ, ‖w‖ < orderThree.radius →
    ContinuousAt
        (uniformizerCayleyFactor fuchsianOneFixedPoint
          A.modular.sourceCoordinate.branch_one.uniformizer) w ∧
      uniformizerCayleyFactor fuchsianOneFixedPoint
        A.modular.sourceCoordinate.branch_one.uniformizer w ≠ 0
  /-- The analogous transition-factor control on the selected order-four Cayley ball. -/
  orderFour_cayleyFactor_control : ∀ w : ℂ, ‖w‖ < orderFour.radius →
    ContinuousAt
        (uniformizerCayleyFactor fuchsianTwoFixedPoint
          A.modular.sourceCoordinate.branch_two.uniformizer) w ∧
      uniformizerCayleyFactor fuchsianTwoFixedPoint
        A.modular.sourceCoordinate.branch_two.uniformizer w ≠ 0
  /-- The residual order-three leading unit stays in a fixed logarithm chart about its central
  value on the entire selected Cayley ball. -/
  orderThree_leadingUnit_normalized_close : ∀ w : ℂ, ‖w‖ < orderThree.radius →
    ‖A.actualOrderThreeCayleyLeadingUnit w /
          A.actualOrderThreeCayleyLeadingUnit 0 - 1‖ < (1 / 2 : ℝ)
  /-- The analogous fixed logarithm-chart estimate for the order-four residual unit. -/
  orderFour_leadingUnit_normalized_close : ∀ w : ℂ, ‖w‖ < orderFour.radius →
    ‖A.actualOrderFourCayleyLeadingUnit w /
          A.actualOrderFourCayleyLeadingUnit 0 - 1‖ < (1 / 2 : ℝ)
  /-- The selected order-three ball maps into a fixed small disc about zero, disjoint from the
  other finite branch value. -/
  orderThree_coordinate_mem_halfBall : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      A.modular.sourceCoordinate.coordinate z ∈ Metric.ball 0 (1 / 2 : ℝ)
  /-- The selected order-four ball maps into a fixed small disc about one, disjoint from zero. -/
  orderFour_coordinate_mem_halfBall : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      A.modular.sourceCoordinate.coordinate z ∈ Metric.ball 1 (1 / 2 : ℝ)
  orderThree_avoids_cusp : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      z ∉ closure (⋃ g : Delta,
        (fun x : UpperHalfPlane ↦
          A.modular.modularParameter.toTriangleUniformization.sourceAction g • x) ''
            normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  orderFour_avoids_cusp : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      z ∉ closure (⋃ g : Delta,
        (fun x : UpperHalfPlane ↦
          A.modular.modularParameter.toTriangleUniformization.sourceAction g • x) ''
            normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  orderThree_coordinate_bound : ∀ z : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
      ‖A.modular.sourceCoordinate.coordinate z‖ < 1 / 3
  orderFour_coordinate_bound : ∀ z : UpperHalfPlane,
    ‖(orderFourCayleyHomeomorph z : ℂ)‖ < orderFour.radius →
      ‖A.modular.sourceCoordinate.coordinate z - 1‖ < 1 / 3
  elliptic_orbits_disjoint : ∀ z x : UpperHalfPlane,
    ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < orderThree.radius →
    ‖(orderFourCayleyHomeomorph x : ℂ)‖ < orderFour.radius →
      ∀ g : Delta,
        A.modular.modularParameter.toTriangleUniformization.sourceAction g • x ≠ z

public theorem exists_collarSeparationData
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    Nonempty (A.CollarSeparationData W) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let C : Set UpperHalfPlane := closure (⋃ g : Delta,
    (fun x : UpperHalfPlane ↦ U.sourceAction g • x) ''
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius)
  let Q := Quotient (MulAction.orbitRel Delta UpperHalfPlane)
  let q : UpperHalfPlane → Q := Quotient.mk _
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have hnotRegularOne : ¬IsRegularBasePoint (U := U) fuchsianOneFixedPoint := by
    intro h
    simp only [GlobalTorusFamily.IsRegularBasePoint] at h
    apply (h 1).1
    simpa using hfixed.1.symm
  have hnotRegularTwo : ¬IsRegularBasePoint (U := U) fuchsianTwoFixedPoint := by
    intro h
    simp only [GlobalTorusFamily.IsRegularBasePoint] at h
    apply (h 1).2
    simpa using hfixed.2.symm
  have hnotCOne : fuchsianOneFixedPoint ∉ C := fun h ↦
    hnotRegularOne (W.orbitClosure_region_regular h)
  have hnotCTwo : fuchsianTwoFixedPoint ∉ C := fun h ↦
    hnotRegularTwo (W.orbitClosure_region_regular h)
  have hquotientNe : q fuchsianOneFixedPoint ≠ q fuchsianTwoFixedPoint := by
    intro h
    have hr := Quotient.exact h
    change MulAction.orbitRel Delta UpperHalfPlane
      fuchsianOneFixedPoint fuchsianTwoFixedPoint at hr
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
    obtain ⟨g, hg⟩ := hr
    exact fuchsianTwo_orbit_ne_one g hg
  obtain ⟨S, T, hSopen, hTopen, hqOne, hqTwo, hST⟩ :=
    t2_separation hquotientNe
  let S' := q ⁻¹' S ∩ Cᶜ ∩
    {z | ‖A.modular.sourceCoordinate.coordinate z‖ < 1 / 3}
  let T' := q ⁻¹' T ∩ Cᶜ ∩
    {z | ‖A.modular.sourceCoordinate.coordinate z - 1‖ < 1 / 3}
  have hS'open : IsOpen S' :=
    ((hSopen.preimage continuous_quot_mk).inter isClosed_closure.isOpen_compl).inter
      (isOpen_lt
        (continuous_norm.comp A.modular.sourceCoordinate.coordinate_holomorphic.continuous)
        continuous_const)
  have hT'open : IsOpen T' :=
    ((hTopen.preimage continuous_quot_mk).inter isClosed_closure.isOpen_compl).inter
      (isOpen_lt
        (continuous_norm.comp
          (A.modular.sourceCoordinate.coordinate_holomorphic.continuous.sub continuous_const))
        continuous_const)
  have hOneS' : fuchsianOneFixedPoint ∈ S' := by
    refine ⟨⟨hqOne, hnotCOne⟩, ?_⟩
    change ‖A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint‖ < 1 / 3
    rw [A.modular.sourceCoordinate.coordinate_at_one]
    norm_num
  have hTwoT' : fuchsianTwoFixedPoint ∈ T' := by
    refine ⟨⟨hqTwo, hnotCTwo⟩, ?_⟩
    change ‖A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint - 1‖ < 1 / 3
    rw [A.modular.sourceCoordinate.coordinate_at_two]
    norm_num
  let B₃ := A.modular.sourceCoordinate.branch_one
  let B₄ := A.modular.sourceCoordinate.branch_two
  have hbranch₃ : ∀ᶠ z in nhds fuchsianOneFixedPoint,
      A.modular.sourceCoordinate.coordinate z = B₃.uniformizer z ^ 3 * B₃.unit z ∧
        B₃.unit z ≠ 0 := by
    filter_upwards [B₃.factorization,
      B₃.unit_holomorphic.continuousAt.eventually_ne B₃.unit_ne_zero] with z hz hunit
    exact ⟨by simpa only [sub_zero] using hz, hunit⟩
  have hbranch₄ : ∀ᶠ z in nhds fuchsianTwoFixedPoint,
      A.modular.sourceCoordinate.coordinate z - 1 =
          B₄.uniformizer z ^ 4 * B₄.unit z ∧
        B₄.unit z ≠ 0 := by
    filter_upwards [B₄.factorization,
      B₄.unit_holomorphic.continuousAt.eventually_ne B₄.unit_ne_zero] with z hz hunit
    exact ⟨hz, hunit⟩
  have hfactor₃ : ∀ᶠ w in nhds (0 : ℂ),
      ContinuousAt
          (uniformizerCayleyFactor fuchsianOneFixedPoint B₃.uniformizer) w ∧
        uniformizerCayleyFactor fuchsianOneFixedPoint B₃.uniformizer w ≠ 0 :=
    eventually_uniformizerCayleyFactor_continuousAt_ne_zero
      B₃.uniformizer_center B₃.uniformizer_isLocalDiffeomorph
  have hfactor₄ : ∀ᶠ w in nhds (0 : ℂ),
      ContinuousAt
          (uniformizerCayleyFactor fuchsianTwoFixedPoint B₄.uniformizer) w ∧
        uniformizerCayleyFactor fuchsianTwoFixedPoint B₄.uniformizer w ≠ 0 :=
    eventually_uniformizerCayleyFactor_continuousAt_ne_zero
      B₄.uniformizer_center B₄.uniformizer_isLocalDiffeomorph
  have hclose₃ : ∀ᶠ w in nhds (0 : ℂ),
      ‖A.actualOrderThreeCayleyLeadingUnit w /
          A.actualOrderThreeCayleyLeadingUnit 0 - 1‖ < (1 / 2 : ℝ) := by
    have hcont : ContinuousAt (fun w ↦
        A.actualOrderThreeCayleyLeadingUnit w /
          A.actualOrderThreeCayleyLeadingUnit 0 - 1) 0 :=
      (A.continuousAt_actualOrderThreeCayleyLeadingUnit_zero.div_const _).sub
        continuousAt_const
    have hzero : A.actualOrderThreeCayleyLeadingUnit 0 /
          A.actualOrderThreeCayleyLeadingUnit 0 - 1 = 0 := by
      rw [div_self A.actualOrderThreeCayleyLeadingUnit_zero_ne]
      ring
    have hmem : {y : ℝ | y < 1 / 2} ∈ nhds
        ‖A.actualOrderThreeCayleyLeadingUnit 0 /
            A.actualOrderThreeCayleyLeadingUnit 0 - 1‖ := by
      rw [hzero, norm_zero]
      exact Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    exact hcont.norm.eventually hmem
  have hclose₄ : ∀ᶠ w in nhds (0 : ℂ),
      ‖A.actualOrderFourCayleyLeadingUnit w /
          A.actualOrderFourCayleyLeadingUnit 0 - 1‖ < (1 / 2 : ℝ) := by
    have hcont : ContinuousAt (fun w ↦
        A.actualOrderFourCayleyLeadingUnit w /
          A.actualOrderFourCayleyLeadingUnit 0 - 1) 0 :=
      (A.continuousAt_actualOrderFourCayleyLeadingUnit_zero.div_const _).sub
        continuousAt_const
    have hzero : A.actualOrderFourCayleyLeadingUnit 0 /
          A.actualOrderFourCayleyLeadingUnit 0 - 1 = 0 := by
      rw [div_self A.actualOrderFourCayleyLeadingUnit_zero_ne]
      ring
    have hmem : {y : ℝ | y < 1 / 2} ∈ nhds
        ‖A.actualOrderFourCayleyLeadingUnit 0 /
            A.actualOrderFourCayleyLeadingUnit 0 - 1‖ := by
      rw [hzero, norm_zero]
      exact Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    exact hcont.norm.eventually hmem
  obtain ⟨d₃, hd₃, hd₃factor⟩ := Metric.mem_nhds_iff.mp (hfactor₃.and hclose₃)
  obtain ⟨d₄, hd₄, hd₄factor⟩ := Metric.mem_nhds_iff.mp (hfactor₄.and hclose₄)
  obtain ⟨V₃, hV₃, hV₃open, honeV₃⟩ := mem_nhds_iff.mp hbranch₃
  obtain ⟨V₄, hV₄, hV₄open, htwoV₄⟩ := mem_nhds_iff.mp hbranch₄
  let V₃' := V₃ ∩ A.modular.sourceCoordinate.coordinate ⁻¹' Metric.ball 0 (1 / 2 : ℝ)
  let V₄' := V₄ ∩ A.modular.sourceCoordinate.coordinate ⁻¹' Metric.ball 1 (1 / 2 : ℝ)
  have hV₃'open : IsOpen V₃' := hV₃open.inter
    (Metric.isOpen_ball.preimage
      A.modular.sourceCoordinate.coordinate_holomorphic.continuous)
  have hV₄'open : IsOpen V₄' := hV₄open.inter
    (Metric.isOpen_ball.preimage
      A.modular.sourceCoordinate.coordinate_holomorphic.continuous)
  have honeV₃' : fuchsianOneFixedPoint ∈ V₃' := by
    refine ⟨honeV₃, ?_⟩
    change A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint ∈
      Metric.ball 0 (1 / 2 : ℝ)
    rw [A.modular.sourceCoordinate.coordinate_at_one]
    simp
  have htwoV₄' : fuchsianTwoFixedPoint ∈ V₄' := by
    refine ⟨htwoV₄, ?_⟩
    change A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint ∈
      Metric.ball 1 (1 / 2 : ℝ)
    rw [A.modular.sourceCoordinate.coordinate_at_two]
    simp
  obtain ⟨b₃, hb₃, hb₃one, hb₃V⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hV₃'open honeV₃'
  obtain ⟨b₄, hb₄, hb₄one, hb₄V⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hV₄'open htwoV₄'
  obtain ⟨s₃, hs₃, hs₃one, hs₃S⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hS'open hOneS'
  obtain ⟨s₄, hs₄, hs₄one, hs₄T⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hT'open hTwoT'
  obtain ⟨P₃⟩ := A.exists_orderThreeFillingPiece
  obtain ⟨P₄⟩ := A.exists_orderFourFillingPiece
  let r₃ := min (min (min P₃.radius s₃) b₃) d₃
  let r₄ := min (min (min P₄.radius s₄) b₄) d₄
  have hr₃ : 0 < r₃ := lt_min (lt_min (lt_min P₃.radius_pos hs₃) hb₃) hd₃
  have hr₄ : 0 < r₄ := lt_min (lt_min (lt_min P₄.radius_pos hs₄) hb₄) hd₄
  have hr₃P : r₃ ≤ P₃.radius :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₃s : r₃ ≤ s₃ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr₃b : r₃ ≤ b₃ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₃d : r₃ ≤ d₃ := min_le_right _ _
  have hr₄P : r₄ ≤ P₄.radius :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₄s : r₄ ≤ s₄ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr₄b : r₄ ≤ b₄ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₄d : r₄ ≤ d₄ := min_le_right _ _
  let P₃' : A.OrderThreeFillingPiece :=
    ⟨r₃, hr₃, hr₃P.trans_lt P₃.radius_lt_one,
      A.orderThreeLinearCollarSourceData_mono hr₃P P₃.sourceData⟩
  let P₄' : A.OrderFourFillingPiece :=
    ⟨r₄, hr₄, hr₄P.trans_lt P₄.radius_lt_one,
      A.orderFourLinearCollarSourceData_mono hr₄P P₄.sourceData⟩
  refine ⟨⟨P₃', P₄', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    exact hV₃ (hb₃V z (hz.trans_le hr₃b)).1
  · intro z hz
    exact hV₄ (hb₄V z (hz.trans_le hr₄b)).1
  · intro w hw
    exact (hd₃factor (by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw.trans_le hr₃d)).1
  · intro w hw
    exact (hd₄factor (by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw.trans_le hr₄d)).1
  · intro w hw
    exact (hd₃factor (by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw.trans_le hr₃d)).2
  · intro w hw
    exact (hd₄factor (by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw.trans_le hr₄d)).2
  · intro z hz
    exact (hb₃V z (hz.trans_le hr₃b)).2
  · intro z hz
    exact (hb₄V z (hz.trans_le hr₄b)).2
  · intro z hz
    exact (hs₃S z (hz.trans_le hr₃s)).1.2
  · intro z hz
    exact (hs₄T z (hz.trans_le hr₄s)).1.2
  · intro z hz
    exact (hs₃S z (hz.trans_le hr₃s)).2
  · intro z hz
    exact (hs₄T z (hz.trans_le hr₄s)).2
  · intro z x hz hx g hg
    have hzS : q z ∈ S :=
      (hs₃S z (hz.trans_le hr₃s)).1.1
    have hxT : q x ∈ T :=
      (hs₄T x (hx.trans_le hr₄s)).1.1
    have hqxz : q x = q z := by
      apply Quotient.sound
      change MulAction.orbitRel Delta UpperHalfPlane x z
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [← hg]
      change fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • x) = x
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact Set.disjoint_left.mp hST hzS (hqxz ▸ hxT)

namespace CollarSeparationData

variable {A : PaperAnalyticData}
  {W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel}

/-- The two simultaneously shrunk elliptic collar images are disjoint in the central family. -/
public theorem elliptic_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData))
      (Set.range (A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₃, rfl⟩ ⟨q₄, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  change orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄) =
    orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃) at hp
  generalize hQ₃ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃ = Q₃ at hp
  generalize hQ₄ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄ = Q₄ at hp
  induction Q₃ using Quotient.inductionOn with
  | _ x₃ =>
    induction Q₄ using Quotient.inductionOn with
    | _ x₄ =>
      rw [orderFourLinearCollarToPuncturedGlobalFamily_mk,
        orderThreeLinearCollarToPuncturedGlobalFamily_mk] at hp
      obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hp
      rw [orderFourCollarToRegular_base A.periods hproper hsource
          S.orderFour.sourceData,
        orderThreeCollarToRegular_base A.periods hproper hsource
          S.orderThree.sourceData] at hg
      have hx₃ : ‖(orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods x₃) : ℂ)‖ < S.orderThree.radius := by
        simpa only [orderThreeLinearPuncturedCarrier.eq_def,
          orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using x₃.property.2
      have hx₄ : ‖(orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods x₄) : ℂ)‖ < S.orderFour.radius := by
        simpa only [orderFourLinearPuncturedCarrier.eq_def,
          orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using x₄.property.2
      apply S.elliptic_orbits_disjoint (familyTotalSpaceBase A.periods x₃)
        (familyTotalSpaceBase A.periods x₄) hx₃ hx₄ g⁻¹
      calc
        U.sourceAction g⁻¹ • familyTotalSpaceBase A.periods x₄ =
            U.sourceAction g⁻¹ •
              (U.sourceAction g • familyTotalSpaceBase A.periods x₃) :=
          congrArg _ hg.symm
        _ = familyTotalSpaceBase A.periods x₃ := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The cusp collar image is disjoint from the simultaneously shrunk order-three image. -/
public theorem cusp_orderThree_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (puncturedLocalCuspQuotientMap W))
      (Set.range (A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₀, rfl⟩ ⟨q₃, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  have hcusp : puncturedLocalCuspQuotientMap W q₀ ∈ puncturedGlobalCuspCollar W := by
    rw [← puncturedLocalCuspQuotientMap_range W]
    exact ⟨q₀, rfl⟩
  change puncturedLocalCuspQuotientMap W q₀ ∈
    quotientProjection '' regularCuspFamilyRegion W at hcusp
  obtain ⟨y, hy, hyq⟩ := hcusp
  have hglobal : (Quotient.mk _ y : A.CentralFamily) =
      A.orderThreePuncturedCollarToCentralFamily S.orderThree.sourceData q₃ := by
    simpa only [quotientProjection.eq_def] using hyq.trans hp.symm
  change (Quotient.mk _ y : A.CentralFamily) =
    orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃) at hglobal
  generalize hQ₃ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderThree.radius q₃ = Q₃ at hglobal
  induction Q₃ using Quotient.inductionOn with
  | _ x₃ =>
    rw [orderThreeLinearCollarToPuncturedGlobalFamily_mk] at hglobal
    obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hglobal
    rw [orderThreeCollarToRegular_base A.periods hproper hsource
      S.orderThree.sourceData] at hg
    change (regularTotalSpaceBase A.periods y).1 ∈
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius at hy
    have hx₃ : ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase A.periods x₃) : ℂ)‖ < S.orderThree.radius := by
      simpa only [orderThreeLinearPuncturedCarrier.eq_def,
        orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderThreeFamilyRadius.eq_def] using x₃.property.2
    apply S.orderThree_avoids_cusp (familyTotalSpaceBase A.periods x₃) hx₃
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨g⁻¹, (Set.mem_image _ _ _).mpr ⟨(regularTotalSpaceBase A.periods y).1,
      hy, ?_⟩⟩
    calc
      U.sourceAction g⁻¹ • (regularTotalSpaceBase A.periods y).1 =
          U.sourceAction g⁻¹ •
            (U.sourceAction g • familyTotalSpaceBase A.periods x₃) :=
        congrArg _ hg.symm
      _ = familyTotalSpaceBase A.periods x₃ := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The cusp collar image is disjoint from the simultaneously shrunk order-four image. -/
public theorem cusp_orderFour_centralRanges_disjoint (S : A.CollarSeparationData W) :
    Disjoint
      (Set.range (puncturedLocalCuspQuotientMap W))
      (Set.range (A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData)) := by
  rw [Set.disjoint_left]
  rintro p ⟨q₀, rfl⟩ ⟨q₄, hp⟩
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ := regularFamilyDeckAction A.periods
  have hcusp : puncturedLocalCuspQuotientMap W q₀ ∈ puncturedGlobalCuspCollar W := by
    rw [← puncturedLocalCuspQuotientMap_range W]
    exact ⟨q₀, rfl⟩
  change puncturedLocalCuspQuotientMap W q₀ ∈
    quotientProjection '' regularCuspFamilyRegion W at hcusp
  obtain ⟨y, hy, hyq⟩ := hcusp
  have hglobal : (Quotient.mk _ y : A.CentralFamily) =
      A.orderFourPuncturedCollarToCentralFamily S.orderFour.sourceData q₄ := by
    simpa only [quotientProjection.eq_def] using hyq.trans hp.symm
  change (Quotient.mk _ y : A.CentralFamily) =
    orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      S.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄) at hglobal
  generalize hQ₄ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource S.orderFour.radius q₄ = Q₄ at hglobal
  induction Q₄ using Quotient.inductionOn with
  | _ x₄ =>
    rw [orderFourLinearCollarToPuncturedGlobalFamily_mk] at hglobal
    obtain ⟨g, hg⟩ := regularBase_orbit_of_global_eq A.periods hglobal
    rw [orderFourCollarToRegular_base A.periods hproper hsource
      S.orderFour.sourceData] at hg
    change (regularTotalSpaceBase A.periods y).1 ∈
      normalizedCuspRegion A.cuspCoordinate W.localWitness.radius at hy
    have hx₄ : ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase A.periods x₄) : ℂ)‖ < S.orderFour.radius := by
      simpa only [orderFourLinearPuncturedCarrier.eq_def,
        orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderFourFamilyRadius.eq_def] using x₄.property.2
    apply S.orderFour_avoids_cusp (familyTotalSpaceBase A.periods x₄) hx₄
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨g⁻¹, (Set.mem_image _ _ _).mpr ⟨(regularTotalSpaceBase A.periods y).1,
      hy, ?_⟩⟩
    calc
      U.sourceAction g⁻¹ • (regularTotalSpaceBase A.periods y).1 =
          U.sourceAction g⁻¹ •
            (U.sourceAction g • familyTotalSpaceBase A.periods x₄) :=
        congrArg _ hg.symm
      _ = familyTotalSpaceBase A.periods x₄ := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

end CollarSeparationData

/-- A fixed simultaneous choice of the three pairwise separated collar radii. -/
@[expose] public noncomputable def collarSeparationData :
    A.CollarSeparationData A.actualPuncturedCuspWitness :=
  Classical.choice (A.exists_collarSeparationData A.actualPuncturedCuspWitness)

end PaperAnalyticData

end

end SphereSixComplex.Geometry
