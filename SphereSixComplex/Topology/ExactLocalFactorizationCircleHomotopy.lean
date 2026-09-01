module

public import SphereSixComplex.Topology.PuncturedComplexFundamentalGroup

/-!
# Circle homotopies from exact local factorizations

An exact factorization by a power of the local coordinate determines the free homotopy
class of every sufficiently small circle. The homotopy contracts only the argument of the
nonvanishing unit, leaving the power term fixed.
-/

@[expose] public section

noncomputable section

open Complex Metric Set Topology

namespace SphereSixComplex.Topology

/-- A positively oriented circle with arbitrary nonzero complex base value. -/
public def localDegreeCirclePoint (a : ℂ) (t : unitInterval) : ℂ :=
  a * Complex.exp (((2 * Real.pi * (t : ℝ) : ℂ) * Complex.I))

public theorem localDegreeCirclePoint_continuous (a : ℂ) :
    Continuous (localDegreeCirclePoint a) := by
  unfold localDegreeCirclePoint
  fun_prop

public theorem localDegreeCirclePoint_norm (a : ℂ) (t : unitInterval) :
    ‖localDegreeCirclePoint a t‖ = ‖a‖ := by
  simp [localDegreeCirclePoint, Complex.norm_exp]

public theorem localDegreeCirclePoint_ne_zero {a : ℂ} (ha : a ≠ 0)
    (t : unitInterval) :
    localDegreeCirclePoint a t ≠ 0 := by
  simp [localDegreeCirclePoint, ha]

/-- Radially contract the input of the unit factor while retaining the original circle in the
power factor. -/
public def localDegreeRadialPoint (a : ℂ)
    (p : unitInterval × unitInterval) : ℂ :=
  (((1 - (p.1 : ℝ)) : ℝ) : ℂ) * localDegreeCirclePoint a p.2

public theorem localDegreeRadialPoint_continuous (a : ℂ) :
    Continuous (localDegreeRadialPoint a) := by
  unfold localDegreeRadialPoint localDegreeCirclePoint
  fun_prop

public theorem localDegreeRadialPoint_mem_closedBall (a : ℂ)
    (p : unitInterval × unitInterval) :
    localDegreeRadialPoint a p ∈ closedBall (0 : ℂ) ‖a‖ := by
  rw [mem_closedBall, dist_zero_right, localDegreeRadialPoint, norm_mul,
    localDegreeCirclePoint_norm]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · exact mul_le_of_le_one_left (norm_nonneg a) (by
      linarith [p.1.property.1])
  · linarith [p.1.property.2]

/-- The image circle supplied by an exact factorization. -/
public def factorizedLocalDegreeCircle
    (u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) :
    C(unitInterval, PuncturedComplex) where
  toFun t :=
    ⟨localDegreeCirclePoint a t ^ n * u (localDegreeCirclePoint a t),
      mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha t))
        (hune _ (by
          rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm]))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (localDegreeCirclePoint_continuous a).pow n |>.mul
    exact hu.comp_continuous (localDegreeCirclePoint_continuous a)
      (fun t => by
        rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])

/-- The same power circle with the unit frozen at the centre. -/
public def frozenLocalDegreeCircle
    (u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) :
    C(unitInterval, PuncturedComplex) where
  toFun t :=
    ⟨localDegreeCirclePoint a t ^ n * u 0,
      mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha t))
        (hune 0 (by simp))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (localDegreeCirclePoint_continuous a).pow n |>.mul continuous_const

/-- A nonvanishing unit does not change the free homotopy class contributed by the power term. -/
public def exactLocalFactorizationCircleHomotopy
    (u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) :
    ContinuousMap.Homotopy
      (factorizedLocalDegreeCircle u n a ha hu hune)
      (frozenLocalDegreeCircle u n a ha hune) where
  toFun p :=
    ⟨localDegreeCirclePoint a p.2 ^ n * u (localDegreeRadialPoint a p),
      mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha p.2))
        (hune _ (localDegreeRadialPoint_mem_closedBall a p))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ((localDegreeCirclePoint_continuous a).comp continuous_snd).pow n |>.mul
    exact hu.comp_continuous (localDegreeRadialPoint_continuous a)
      (localDegreeRadialPoint_mem_closedBall a)
  map_zero_left t := by
    apply Subtype.ext
    simp [factorizedLocalDegreeCircle, localDegreeRadialPoint]
  map_one_left t := by
    apply Subtype.ext
    simp [frozenLocalDegreeCircle, localDegreeRadialPoint]

/-- Freezing the unit produces the standard n-turn punctured-plane circle. -/
public theorem frozenLocalDegreeCircle_eq_integerCircle
    (u : ℂ → ℂ) (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) :
    frozenLocalDegreeCircle u n a ha hune =
      (puncturedComplexIntegerCircle
        (a ^ n * u 0)
        (mul_ne_zero (pow_ne_zero n ha) (hune 0 (by simp)))
        (n : ℤ)).toContinuousMap := by
  ext t
  change localDegreeCirclePoint a t ^ n * u 0 =
    (a ^ n * u 0) * Complex.exp
      ((2 * Real.pi * ((n : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  have hexp :
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℂ) * Complex.I)) ^ n =
        Complex.exp
          ((2 * Real.pi * ((n : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [localDegreeCirclePoint, mul_pow, hexp]
  ring

/-- The complex plane with zero and a second marked value removed. -/
public abbrev TwoPunctureComplement (b : ℂ) :=
  {z : ℂ // z ≠ 0 ∧ z ≠ b}

public theorem localDegreeHomotopyValue_ne_second
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖)
    (p : unitInterval × unitInterval) :
    localDegreeCirclePoint a p.2 ^ n * u (localDegreeRadialPoint a p) ≠ b := by
  intro h
  have hn := congrArg norm h
  rw [norm_mul, norm_pow, localDegreeCirclePoint_norm] at hn
  exact (ne_of_lt
    (hbound _ (localDegreeRadialPoint_mem_closedBall a p))) hn

/-- The factorized circle in a target with a second marked value removed. -/
public def factorizedLocalDegreeCircleTwoPunctures
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    C(unitInterval, TwoPunctureComplement b) where
  toFun t :=
    ⟨localDegreeCirclePoint a t ^ n * u (localDegreeCirclePoint a t),
      ⟨mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha t))
        (hune _ (by
            rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])),
        by
          simpa [localDegreeRadialPoint] using
            localDegreeHomotopyValue_ne_second u n a b hbound (0, t)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (localDegreeCirclePoint_continuous a).pow n |>.mul
    exact hu.comp_continuous (localDegreeCirclePoint_continuous a)
      (fun t => by
        rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])

/-- The frozen power circle in a target with a second marked value removed. -/
public def frozenLocalDegreeCircleTwoPunctures
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    C(unitInterval, TwoPunctureComplement b) where
  toFun t :=
    ⟨localDegreeCirclePoint a t ^ n * u 0,
      ⟨mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha t))
          (hune 0 (by simp)),
        by
          simpa [localDegreeRadialPoint] using
            localDegreeHomotopyValue_ne_second u n a b hbound (1, t)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (localDegreeCirclePoint_continuous a).pow n |>.mul continuous_const

/-- If the whole unit-factor contraction avoids a second value, the local-degree homotopy
lives in the twice-punctured target. The displayed norm bound is a convenient sufficient
condition for avoidance. -/
public def exactLocalFactorizationCircleHomotopyTwoPunctures
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖) :
    ContinuousMap.Homotopy
      (factorizedLocalDegreeCircleTwoPunctures u n a b ha hu hune hbound)
      (frozenLocalDegreeCircleTwoPunctures u n a b ha hune hbound) where
  toFun p :=
    ⟨localDegreeCirclePoint a p.2 ^ n * u (localDegreeRadialPoint a p),
      ⟨mul_ne_zero (pow_ne_zero n (localDegreeCirclePoint_ne_zero ha p.2))
          (hune _ (localDegreeRadialPoint_mem_closedBall a p)),
        localDegreeHomotopyValue_ne_second u n a b hbound p⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ((localDegreeCirclePoint_continuous a).comp continuous_snd).pow n |>.mul
    exact hu.comp_continuous (localDegreeRadialPoint_continuous a)
      (localDegreeRadialPoint_mem_closedBall a)
  map_zero_left t := by
    apply Subtype.ext
    simp [factorizedLocalDegreeCircleTwoPunctures, localDegreeRadialPoint]
  map_one_left t := by
    apply Subtype.ext
    simp [frozenLocalDegreeCircleTwoPunctures, localDegreeRadialPoint]

/-- An analytic factorization of positive order admits a nonzero closed circle on which the
factorization, unit nonvanishing, and avoidance of a prescribed unit-distance second value all
hold uniformly. -/
public theorem exists_factorizationCircleData
    (f u : ℂ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 0, f z = z ^ n * u z) :
    ∃ a : ℂ,
      a ≠ 0 ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < 1) := by
  let C : ℝ := ‖u 0‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hune : ∀ᶠ z in 𝓝 0, u z ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hnorm : ∀ᶠ z in 𝓝 0, ‖u z‖ < C := by
    apply hu.continuousAt.norm.eventually_lt continuousAt_const
    simp [C]
  have hlocal : {z : ℂ |
      AnalyticAt ℂ u z ∧ u z ≠ 0 ∧ f z = z ^ n * u z ∧ ‖u z‖ < C} ∈ 𝓝 0 := by
    filter_upwards [hu.eventually_analyticAt, hune, hfactor, hnorm] with z hz hne hfac hbd
    exact ⟨hz, hne, hfac, hbd⟩
  obtain ⟨e, he, hesub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hlocal
  let r : ℝ := min (e / 2) (min (1 / 2) (1 / (2 * C)))
  have hre : r ≤ e / 2 := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1 / (2 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hre' : r ≤ e := by linarith
  let a : ℂ := (r : ℂ)
  have hnorma : ‖a‖ = r := by
    simp [a, abs_of_pos hr]
  have hball : closedBall (0 : ℂ) ‖a‖ ⊆
      {z : ℂ | AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        f z = z ^ n * u z ∧ ‖u z‖ < C} := by
    rw [hnorma]
    intro z hz
    exact hesub (closedBall_subset_closedBall hre' hz)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a, ne_of_gt hr]
  · intro z hz
    exact (hball hz).1.continuousAt.continuousWithinAt
  · intro z hz
    exact (hball hz).2.1
  · intro z hz
    exact (hball hz).2.2.1
  · intro z hz
    have hzu : ‖u z‖ < C := (hball hz).2.2.2
    have hr0 : 0 ≤ r := hr.le
    have hr1 : r ≤ 1 := hrhalf.trans (by norm_num)
    have hrpow : r ^ n ≤ r := pow_le_of_le_one hr0 hr1 hn
    rw [hnorma]
    calc
      r ^ n * ‖u z‖ < r ^ n * C :=
        (mul_lt_mul_of_pos_left hzu (pow_pos hr n))
      _ ≤ r * C := mul_le_mul_of_nonneg_right hrpow hC.le
      _ ≤ (1 / (2 * C)) * C := mul_le_mul_of_nonneg_right hrC hC.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num

/-- The factorization circle can be chosen below any prescribed positive radius. -/
public theorem exists_factorizationCircleData_lt
    (f u : ℂ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 0, f z = z ^ n * u z)
    (R : ℝ) (hR : 0 < R) :
    ∃ a : ℂ,
      a ≠ 0 ∧ ‖a‖ < R ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ n * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ n * ‖u z‖ < 1) := by
  obtain ⟨a₀, ha₀, hucont, hune, hfac, hbound⟩ :=
    exists_factorizationCircleData f u n hn hu hu0 hfactor
  have ha₀norm : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  let r : ℝ := min (‖a₀‖ / 2) (R / 2)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hra₀ : r ≤ ‖a₀‖ := (min_le_left _ _).trans (by linarith)
  have hrR : r < R := (min_le_right _ _).trans_lt (by linarith)
  let a : ℂ := (r : ℂ)
  have hnorma : ‖a‖ = r := by simp [a, abs_of_pos hr]
  have hsub : closedBall (0 : ℂ) ‖a‖ ⊆ closedBall (0 : ℂ) ‖a₀‖ := by
    exact closedBall_subset_closedBall (hnorma.le.trans hra₀)
  refine ⟨a, by simp [a, ne_of_gt hr], by simpa [hnorma], ?_, ?_, ?_, ?_⟩
  · exact hucont.mono hsub
  · exact fun z hz ↦ hune z (hsub hz)
  · exact fun z hz ↦ hfac z (hsub hz)
  · intro z hz
    have hp : ‖a‖ ^ n ≤ ‖a₀‖ ^ n := by
      exact pow_le_pow_left₀ (norm_nonneg a) (by simpa [hnorma] using hra₀) n
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg (u z))).trans_lt
      (hbound z (hsub hz))

/-- An analytic cubic factorization admits a nonzero closed circle on which the factorization,
unit nonvanishing, and avoidance of the second value one all hold uniformly. -/
public theorem exists_cubicFactorizationCircleData
    (f u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 0, f z = z ^ 3 * u z) :
    ∃ a : ℂ,
      a ≠ 0 ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ 3 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 3 * ‖u z‖ < 1) := by
  let C : ℝ := ‖u 0‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hune : ∀ᶠ z in 𝓝 0, u z ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hnorm : ∀ᶠ z in 𝓝 0, ‖u z‖ < C := by
    apply hu.continuousAt.norm.eventually_lt continuousAt_const
    simp [C]
  have hlocal : {z : ℂ |
      AnalyticAt ℂ u z ∧ u z ≠ 0 ∧ f z = z ^ 3 * u z ∧ ‖u z‖ < C} ∈ 𝓝 0 := by
    filter_upwards [hu.eventually_analyticAt, hune, hfactor, hnorm] with z hz hne hfac hbd
    exact ⟨hz, hne, hfac, hbd⟩
  obtain ⟨e, he, hesub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hlocal
  let r : ℝ := min (e / 2) (min (1 / 2) (1 / (2 * C)))
  have hre : r ≤ e / 2 := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1 / (2 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hre' : r ≤ e := by linarith
  let a : ℂ := (r : ℂ)
  have hnorma : ‖a‖ = r := by
    simp [a, abs_of_pos hr]
  have hball : closedBall (0 : ℂ) ‖a‖ ⊆
      {z : ℂ | AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        f z = z ^ 3 * u z ∧ ‖u z‖ < C} := by
    rw [hnorma]
    intro z hz
    exact hesub (closedBall_subset_closedBall hre' hz)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a, ne_of_gt hr]
  · intro z hz
    exact (hball hz).1.continuousAt.continuousWithinAt
  · intro z hz
    exact (hball hz).2.1
  · intro z hz
    exact (hball hz).2.2.1
  · intro z hz
    have hzu : ‖u z‖ < C := (hball hz).2.2.2
    have hr0 : 0 ≤ r := hr.le
    have hr1 : r ≤ 1 := hrhalf.trans (by norm_num)
    have hrpow : r ^ 3 ≤ r := by nlinarith [sq_nonneg r]
    rw [hnorma]
    calc
      r ^ 3 * ‖u z‖ < r ^ 3 * C :=
        (mul_lt_mul_of_pos_left hzu (pow_pos hr 3))
      _ ≤ r * C := mul_le_mul_of_nonneg_right hrpow hC.le
      _ ≤ (1 / (2 * C)) * C := mul_le_mul_of_nonneg_right hrC hC.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num

/-- The cubic factorization circle can be chosen below any prescribed positive radius. -/
public theorem exists_cubicFactorizationCircleData_lt
    (f u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 0, f z = z ^ 3 * u z)
    (R : ℝ) (hR : 0 < R) :
    ∃ a : ℂ,
      a ≠ 0 ∧ ‖a‖ < R ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, f z = z ^ 3 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 3 * ‖u z‖ < 1) := by
  obtain ⟨a₀, ha₀, hucont, hune, hfac, hbound⟩ :=
    exists_cubicFactorizationCircleData f u hu hu0 hfactor
  have ha₀norm : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  let r : ℝ := min (‖a₀‖ / 2) (R / 2)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hra₀ : r ≤ ‖a₀‖ := (min_le_left _ _).trans (by linarith)
  have hrR : r < R := (min_le_right _ _).trans_lt (by linarith)
  let a : ℂ := (r : ℂ)
  have hnorma : ‖a‖ = r := by simp [a, abs_of_pos hr]
  have hsub : closedBall (0 : ℂ) ‖a‖ ⊆ closedBall (0 : ℂ) ‖a₀‖ := by
    exact closedBall_subset_closedBall (hnorma.le.trans hra₀)
  refine ⟨a, by simp [a, ne_of_gt hr], by simpa [hnorma], ?_, ?_, ?_, ?_⟩
  · exact hucont.mono hsub
  · exact fun z hz => hune z (hsub hz)
  · exact fun z hz => hfac z (hsub hz)
  · intro z hz
    have hp : ‖a‖ ^ 3 ≤ ‖a₀‖ ^ 3 := by
      exact pow_le_pow_left₀ (norm_nonneg a) (by simpa [hnorma] using hra₀) 3
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg (u z))).trans_lt
      (hbound z (hsub hz))

end SphereSixComplex.Topology

end

end
