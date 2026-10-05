module

public import SphereSixComplex.Paper.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Paper.Periods.FuchsianModularLift.Ramification
public import SphereSixComplex.Prerequisites.Periods.Uniformization.SourceAutomaticBranch
public import SphereSixComplex.Prerequisites.Topology.ExactLocalFactorizationCircleHomotopy
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology
public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedCircleReflection

@[expose] public section
noncomputable section
open Complex Filter Metric Set Topology

namespace SphereSixComplex.Geometry.EllipticDiscCircle

open SphereSixComplex.Topology SphereSixComplex.Periods
open SphereSixComplex.Periods.SourceAutomaticBranch SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : AnalyticData)

public theorem orderThreeCayleyRegularCoordinate_chartFunction
    (z : UpperHalfPlane) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
        ((orderThreeCayleyHomeomorph z :
          ComplexUnitDisc) : ℂ) =
      A.modular.sourceCoordinate.coordinate z := by
  unfold ellipticChartFunction
  let w := orderThreeCayleyHomeomorph z
  have him : 0 < (cayleyRawInverse fuchsianOneFixedPoint (w : ℂ)).im :=
    cayleyRawInverse_im_pos w.property
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  change A.modular.sourceCoordinate.coordinate
      (UpperHalfPlane.cayleyFromDisc fuchsianOneFixedPoint w) =
    A.modular.sourceCoordinate.coordinate z
  rw [show UpperHalfPlane.cayleyFromDisc fuchsianOneFixedPoint w = z by
    exact orderThreeCayleyHomeomorph.symm_apply_apply z]


public theorem orderFourCayleyRegularCoordinate_chartFunction
    (z : UpperHalfPlane) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
        ((orderFourCayleyHomeomorph z :
          ComplexUnitDisc) : ℂ) =
      A.modular.sourceCoordinate.coordinate z := by
  unfold ellipticChartFunction
  let w := orderFourCayleyHomeomorph z
  have him : 0 < (cayleyRawInverse fuchsianTwoFixedPoint (w : ℂ)).im :=
    cayleyRawInverse_im_pos w.property
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  change A.modular.sourceCoordinate.coordinate
      (UpperHalfPlane.cayleyFromDisc fuchsianTwoFixedPoint w) =
    A.modular.sourceCoordinate.coordinate z
  rw [show UpperHalfPlane.cayleyFromDisc fuchsianTwoFixedPoint w = z by
    exact orderFourCayleyHomeomorph.symm_apply_apply z]



public theorem orderThreeCayleyRegularCoordinate_analyticOrderAt :
    analyticOrderAt
      (ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint) 0 = 3 := by
  change analyticOrderAt
      (fun w : ℂ ↦
        A.modular.sourceCoordinate.coordinate
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianOneFixedPoint w))) 0 = 3
  let f : ℂ → ℂ := fun z ↦
    A.modular.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex z) - 0
  have hbase :
      analyticOrderAt f (fuchsianOneFixedPoint : ℂ) = 3 := by
    simpa [f] using
      A.modular.sourceCoordinate.branch_one.analyticOrderAt
        A.modular.sourceCoordinate.coordinate_holomorphic
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := cayleyRawInverse fuchsianOneFixedPoint) (z₀ := (0 : ℂ))
    (cayleyRawInverse_analyticAt_zero fuchsianOneFixedPoint)
    (cayleyRawInverse_deriv_zero_ne fuchsianOneFixedPoint)
  rw [cayleyRawInverse_zero, hbase] at hcomp
  simpa [f, Function.comp_def] using hcomp

/-- Near the order-three centre, the affine coordinate is a Cayley-coordinate cube times a
nonvanishing analytic unit. -/
public theorem exists_orderThreeCayleyRegularCoordinate_cubicUnit :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧
      u 0 ≠ 0 ∧
      ∀ᶠ w in 𝓝 0,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianOneFixedPoint w = w ^ 3 * u w := by
  let G : ℂ → ℂ :=
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianOneFixedPoint
  have hG : AnalyticAt ℂ G 0 :=
    ellipticChartFunction_analyticAt_zero
      A.modular.sourceCoordinate.coordinate_holomorphic fuchsianOneFixedPoint
  have horder : analyticOrderAt G 0 = (3 : ℕ∞) := by
    simpa [G] using orderThreeCayleyRegularCoordinate_analyticOrderAt A
  obtain ⟨u, hu, hu0, hfac⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 3)).mp horder
  refine ⟨u, hu, hu0, ?_⟩
  simpa [G, smul_eq_mul] using hfac


public theorem orderFourCayleyRegularCoordinate_sub_one_analyticOrderAt :
    analyticOrderAt
      (fun w : ℂ ↦
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w - 1) 0 = 4 := by
  change analyticOrderAt
      (fun w : ℂ ↦
        A.modular.sourceCoordinate.coordinate
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianTwoFixedPoint w)) - 1) 0 = 4
  let f : ℂ → ℂ := fun z ↦
    A.modular.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex z) - 1
  have hbase :
      analyticOrderAt f (fuchsianTwoFixedPoint : ℂ) = 4 := by
    simpa [f] using
      A.modular.sourceCoordinate.branch_two.analyticOrderAt
        A.modular.sourceCoordinate.coordinate_holomorphic
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := cayleyRawInverse fuchsianTwoFixedPoint) (z₀ := (0 : ℂ))
    (cayleyRawInverse_analyticAt_zero fuchsianTwoFixedPoint)
    (cayleyRawInverse_deriv_zero_ne fuchsianTwoFixedPoint)
  rw [cayleyRawInverse_zero, hbase] at hcomp
  simpa [f, Function.comp_def] using hcomp

/-- Near the order-four centre, the affine coordinate minus one is a Cayley-coordinate fourth
power times a nonvanishing analytic unit. -/
public theorem exists_orderFourCayleyRegularCoordinate_quarticUnit :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧
      u 0 ≠ 0 ∧
      ∀ᶠ w in 𝓝 0,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianTwoFixedPoint w - 1 = w ^ 4 * u w := by
  let G : ℂ → ℂ := fun w ↦
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianTwoFixedPoint w - 1
  have hG : AnalyticAt ℂ G 0 :=
    (ellipticChartFunction_analyticAt_zero
      A.modular.sourceCoordinate.coordinate_holomorphic fuchsianTwoFixedPoint).sub
        analyticAt_const
  have horder : analyticOrderAt G 0 = (4 : ℕ∞) := by
    simpa [G] using orderFourCayleyRegularCoordinate_sub_one_analyticOrderAt A
  obtain ⟨u, hu, hu0, hfac⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 4)).mp horder
  refine ⟨u, hu, hu0, ?_⟩
  simpa [G, smul_eq_mul] using hfac


public theorem exists_positive_factorization_radius
    (f u : ℂ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 0, f z = z ^ n * u z)
    (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ContinuousOn u (closedBall (0 : ℂ) r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, f z = z ^ n * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, r ^ n * ‖u z‖ < 1) := by
  obtain ⟨a, ha, haR, hc, hne, hf, hb⟩ :=
    exists_factorizationCircleData_lt f u n hn hu hu0 hfactor R hR
  exact ⟨‖a‖, norm_pos_iff.mpr ha, haR, hc, hne, hf, hb⟩

public theorem exists_orderThree_positive_factorization_radius :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧
      r < A.starSeparation.orderThree.radius ∧
      ContinuousOn u (closedBall (0 : ℂ) r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) r,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianOneFixedPoint z = z ^ 3 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, r ^ 3 * ‖u z‖ < 1) := by
  obtain ⟨u, hu, hu0, hf⟩ := exists_orderThreeCayleyRegularCoordinate_cubicUnit A
  obtain ⟨r, hr⟩ := exists_positive_factorization_radius _ u 3 (by decide)
    hu hu0 hf A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
  exact ⟨u, r, hr⟩

public theorem exists_orderFour_positive_factorization_radius :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧
      r < A.starSeparation.orderFour.radius ∧
      ContinuousOn u (closedBall (0 : ℂ) r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) r,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint z - 1 = z ^ 4 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, r ^ 4 * ‖u z‖ < 1) := by
  obtain ⟨u, hu, hu0, hf⟩ := exists_orderFourCayleyRegularCoordinate_quarticUnit A
  obtain ⟨r, hr⟩ := exists_positive_factorization_radius _ u 4 (by decide)
    hu hu0 hf A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
  exact ⟨u, r, hr⟩

public def factorizedCoordinateCircle
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    C(unitInterval, TwoPunctureComplement b) where
  toFun t := ⟨f (localDegreeCirclePoint a t), by
    rw [hf _ (by rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])]
    exact (factorizedLocalDegreeCircleTwoPunctures u n a b ha hu hune hb t).property⟩
  continuous_toFun := by
    have h : (fun t ↦ f (localDegreeCirclePoint a t)) =
        fun t ↦ ((factorizedLocalDegreeCircleTwoPunctures u n a b ha hu hune hb t) : ℂ) := by
      funext t
      exact hf _ (by rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
    apply Continuous.subtype_mk
    rw [h]
    exact continuous_subtype_val.comp
      (factorizedLocalDegreeCircleTwoPunctures u n a b ha hu hune hb).continuous

public theorem factorizedCoordinateCircle_eq
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    factorizedCoordinateCircle f u n a b ha hu hune hf hb =
      factorizedLocalDegreeCircleTwoPunctures u n a b ha hu hune hb := by
  ext t
  exact hf _ (by rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])

public def factorizedCoordinateCircleHomotopy
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    ContinuousMap.Homotopy
      (factorizedCoordinateCircle f u n a b ha hu hune hf hb)
      (frozenLocalDegreeCircleTwoPunctures u n a b ha hune hb) :=
  (exactLocalFactorizationCircleHomotopyTwoPunctures u n a b ha hu hune hb).cast
    (factorizedCoordinateCircle_eq f u n a b ha hu hune hf hb).symm rfl

public theorem factorizedCoordinateCircleHomotopy_trace
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖)
    (s : unitInterval) :
    factorizedCoordinateCircleHomotopy f u n a b ha hu hune hf hb (s, 0) =
      factorizedCoordinateCircleHomotopy f u n a b ha hu hune hf hb (s, 1) := by
  apply Subtype.ext
  change localDegreeCirclePoint a 0 ^ n * u (localDegreeRadialPoint a (s, 0)) =
    localDegreeCirclePoint a 1 ^ n * u (localDegreeRadialPoint a (s, 1))
  have h : localDegreeCirclePoint a 0 = localDegreeCirclePoint a 1 := by
    unfold localDegreeCirclePoint
    norm_num
  rw [h]
  congr 2
  unfold localDegreeRadialPoint
  rw [h]

public def factorizedCoordinateLoop
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    Path (factorizedCoordinateCircle f u n a b ha hu hune hf hb 0)
      (factorizedCoordinateCircle f u n a b ha hu hune hf hb 0) where
  toContinuousMap := factorizedCoordinateCircle f u n a b ha hu hune hf hb
  source' := rfl
  target' := by
    apply Subtype.ext
    change f (localDegreeCirclePoint a 1) = f (localDegreeCirclePoint a 0)
    congr 1
    unfold localDegreeCirclePoint
    norm_num

public def frozenCoordinateLoop
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    Path (frozenLocalDegreeCircleTwoPunctures u n a b ha hune hb 0)
      (frozenLocalDegreeCircleTwoPunctures u n a b ha hune hb 0) where
  toContinuousMap := frozenLocalDegreeCircleTwoPunctures u n a b ha hune hb
  source' := rfl
  target' := by
    apply Subtype.ext
    change localDegreeCirclePoint a 1 ^ n * u 0 = localDegreeCirclePoint a 0 ^ n * u 0
    congr 2
    unfold localDegreeCirclePoint
    norm_num

public theorem frozenCoordinateLoop_value
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖)
    (t : unitInterval) :
    (frozenCoordinateLoop u n a b ha hune hb t : ℂ) =
      (a ^ n * u 0) * Complex.exp
        (((2 * Real.pi * (n : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
  change localDegreeCirclePoint a t ^ n * u 0 = _
  rw [localDegreeCirclePoint, mul_pow, ← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((2 * Real.pi * (t : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * (n : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  ring

public theorem factorizedCoordinateLoop_homology_eq_frozen
    (f u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
        (factorizedCoordinateLoop f u n a b ha hu hune hf hb) =
      SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
        (frozenCoordinateLoop u n a b ha hune hb) := by
  exact loopHomologyClass_eq_of_freeHomotopy _ _
    (factorizedCoordinateCircleHomotopy f u n a b ha hu hune hf hb)
    (factorizedCoordinateCircleHomotopy_trace f u n a b ha hu hune hf hb)

open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

public def zeroPunctureMap : C(TwoPunctureComplement (1 : ℂ), TwicePuncturedComplex) where
  toFun z := ⟨z.1, by
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] using z.property⟩
  continuous_toFun := by fun_prop

public def onePunctureMap : C(TwoPunctureComplement (-1 : ℂ), TwicePuncturedComplex) where
  toFun z := ⟨1 + z.1, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      apply z.property.2
      linear_combination h
    · intro h
      apply z.property.1
      linear_combination h⟩
  continuous_toFun := by fun_prop

public theorem factorizedCoordinateLoop_zero_homology
    (f u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖(1 : ℂ)‖) :
    loopHomologyClass ((factorizedCoordinateLoop f u n a (1) ha hu hune hf hb).map
      zeroPunctureMap.continuous) = n • hurewiczFunction twicePuncturedComplexBasepoint
        TwicePuncturedComplex.zeroMeridianClass⁻¹ := by
  have h := congrArg (integralSingularHomologyMap 1 zeroPunctureMap)
    (factorizedCoordinateLoop_homology_eq_frozen f u n a (1) ha hu hune hf hb)
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass] at h
  refine h.trans (TwicePuncturedComplex.Circles.coefficientCircle_homology
    n (a ^ n * u 0) (mul_ne_zero (pow_ne_zero n ha) (hune 0 (by simp)))
    (by rw [norm_mul, norm_pow]; simpa using hb 0 (by simp)) _ ?_)
  intro t
  change (frozenCoordinateLoop u n a 1 ha hune hb t : ℂ) = _
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    frozenCoordinateLoop_value u n a 1 ha hune hb t

public theorem factorizedCoordinateLoop_one_homology
    (f u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < ‖(-1 : ℂ)‖) :
    loopHomologyClass ((factorizedCoordinateLoop f u n a (-1) ha hu hune hf hb).map
      onePunctureMap.continuous) = n • hurewiczFunction twicePuncturedComplexBasepoint
        TwicePuncturedComplex.oneMeridianClass⁻¹ := by
  have h := congrArg (integralSingularHomologyMap 1 onePunctureMap)
    (factorizedCoordinateLoop_homology_eq_frozen f u n a (-1) ha hu hune hf hb)
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass] at h
  refine h.trans (TwicePuncturedComplex.Circles.coefficientCircleOne_homology
    n (a ^ n * u 0) (mul_ne_zero (pow_ne_zero n ha) (hune 0 (by simp)))
    (by rw [norm_mul, norm_pow]; simpa using hb 0 (by simp)) _ ?_)
  intro t
  change 1 + (frozenCoordinateLoop u n a (-1) ha hune hb t : ℂ) = _
  rw [frozenCoordinateLoop_value]
  push_cast
  rfl

end SphereSixComplex.Geometry.EllipticDiscCircle
