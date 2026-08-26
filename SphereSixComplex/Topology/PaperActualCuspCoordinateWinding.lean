module

public import SphereSixComplex.Topology.PaperActualCuspMarkedLoop
import Mathlib.Analysis.Complex.BranchLogRoot

/-!
# Winding of the actual marked cusp coordinate

The exact reciprocal modular factorization writes the central base coordinate as the inverse of
`q u(q)`.  Along the literal selected cusp meridian the parameter `q` makes one negative turn,
while the nonvanishing unit has a logarithm on the chosen completed-cusp disc.  Consequently the
actual central coordinate makes exactly one positive turn about the finite plane.
-/

@[expose] public section

noncomputable section

open Set Metric Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Forget the puncture at one. -/
public def twicePuncturedComplexForgetZero : C(TwicePuncturedComplex, PuncturedComplex) where
  toFun z := ⟨z.1, by
    have hz := z.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz
    exact hz.1⟩
  continuous_toFun := by
    fun_prop

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open CuspPeriodExpansion CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The completed-cusp parameter disc retained by the actual collar choice. -/
public def actualCuspParameterBall : Set ℂ :=
  Metric.ball 0 A.starCuspWitness.localWitness.radius

/-- The exact holomorphic unit in the selected reciprocal cusp factorization. -/
public abbrev actualCuspFactorizationUnit : ℂ → ℂ :=
  A.actualNormalizedModularJUniformization.cusp.cuspUnit

public theorem actualCuspFactorizationUnit_continuousOn :
    ContinuousOn A.actualCuspFactorizationUnit A.actualCuspParameterBall := by
  intro q hq
  apply (A.actualNormalizedModularJUniformization.cusp
    |>.cuspUnit_holomorphic q ?_).continuousAt.continuousWithinAt
  rw [Metric.mem_ball, dist_zero_right]
  exact (show ‖q‖ < A.starCuspWitness.localWitness.radius by
    simpa [actualCuspParameterBall, Metric.mem_ball, dist_zero_right] using hq).trans_le
      A.actualPuncturedCuspWitness_radius_le_cuspUnitRadius

public theorem actualCuspFactorizationUnit_zero_not_mem_image :
    0 ∉ A.actualCuspFactorizationUnit '' A.actualCuspParameterBall := by
  rintro ⟨q, hq, hzero⟩
  apply A.actualPuncturedCuspWitness_cuspUnit_ne q
    (by simpa [actualCuspParameterBall, Metric.mem_ball, dist_zero_right] using hq)
  exact hzero

/-- A continuous logarithm of the exact unit on the entire selected parameter disc. -/
public theorem exists_actualCuspFactorizationUnitLog :
    ∃ f : ℂ → ℂ, ContinuousOn f A.actualCuspParameterBall ∧
      Set.EqOn (Complex.exp ∘ f) A.actualCuspFactorizationUnit
        A.actualCuspParameterBall := by
  let _ : ContractibleSpace A.actualCuspParameterBall :=
    (convex_ball (0 : ℂ) A.starCuspWitness.localWitness.radius).contractibleSpace
      ⟨0, by
        simpa [actualCuspParameterBall, Metric.mem_ball] using
          A.starCuspWitness.localWitness.radius_pos⟩
  have hSimplyConnected : IsSimplyConnected A.actualCuspParameterBall := by
    change SimplyConnectedSpace A.actualCuspParameterBall
    infer_instance
  exact Complex.exists_continuousOn_eqOn_exp_comp hSimplyConnected Metric.isOpen_ball
    A.actualCuspFactorizationUnit_continuousOn
    A.actualCuspFactorizationUnit_zero_not_mem_image

public noncomputable def actualCuspFactorizationUnitLog : ℂ → ℂ :=
  Classical.choose A.exists_actualCuspFactorizationUnitLog

public theorem actualCuspFactorizationUnitLog_continuousOn :
    ContinuousOn A.actualCuspFactorizationUnitLog A.actualCuspParameterBall :=
  (Classical.choose_spec A.exists_actualCuspFactorizationUnitLog).1

public theorem actualCuspFactorizationUnitLog_exp
    {q : ℂ} (hq : q ∈ A.actualCuspParameterBall) :
    Complex.exp (A.actualCuspFactorizationUnitLog q) =
      A.actualCuspFactorizationUnit q :=
  (Classical.choose_spec A.exists_actualCuspFactorizationUnitLog).2 hq

/-! ## The completed-cusp parameter along the actual angular loop -/

public def actualCuspAngularQPoint (t : unitInterval) : ℂ :=
  cuspQ (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))

public theorem actualCuspAngularQPoint_mem_parameterBall (t : unitInterval) :
    A.actualCuspAngularQPoint t ∈ A.actualCuspParameterBall := by
  rw [actualCuspParameterBall, Metric.mem_ball, dist_zero_right]
  unfold actualCuspAngularQPoint
  have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
      A.starCuspWitness.localWitness.radius :=
    A.actualCuspBoundaryCoverBase.2
  rw [norm_cuspQ] at hbase ⊢
  simpa using hbase

/-- Along `s - t`, the completed cusp parameter makes one negative exponential turn. -/
public theorem actualCuspAngularQPoint_apply (t : unitInterval) :
    A.actualCuspAngularQPoint t =
      A.actualCuspAngularQPoint 0 *
        Complex.exp (-(((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  unfold actualCuspAngularQPoint cuspQ
  rw [show
    2 * (Real.pi : ℂ) * Complex.I *
          (A.actualCuspBoundaryCoverBase.1.2 - ((t : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I *
            (A.actualCuspBoundaryCoverBase.1.2 - (0 : ℂ)) +
          -(((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
  exact Complex.exp_add _ _

public theorem actualCuspAngularQPoint_one :
    A.actualCuspAngularQPoint 1 = A.actualCuspAngularQPoint 0 := by
  rw [A.actualCuspAngularQPoint_apply]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]

public theorem actualCuspAngularCoordinateLoop_inv_apply (t : unitInterval) :
    ((A.actualCuspAngularCoordinateLoop t).1)⁻¹ =
      A.actualCuspAngularQPoint t *
        A.actualCuspFactorizationUnit (A.actualCuspAngularQPoint t) := by
  rw [A.actualCuspAngularCoordinateLoop_apply]
  apply A.actualPuncturedCuspWitness_reciprocal_factorization
  · apply mem_cuspHalfPlane_of_norm_cuspQ_lt
      A.starCuspWitness.localWitness.radius_le
    have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
        A.starCuspWitness.localWitness.radius :=
      A.actualCuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase
  · have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
        A.actualPuncturedCuspWitness.localWitness.radius :=
      A.actualCuspBoundaryCoverBase.2
    rw [norm_cuspQ] at hbase ⊢
    simpa using hbase

/-- An unnormalized logarithm of the actual central coordinate. -/
public noncomputable def actualCuspAngularZeroRawLog (t : unitInterval) : ℂ :=
  -(Complex.log (A.actualCuspAngularQPoint 0) -
      (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) +
      A.actualCuspFactorizationUnitLog (A.actualCuspAngularQPoint t))

public theorem actualCuspAngularQPoint_zero_ne :
    A.actualCuspAngularQPoint 0 ≠ 0 := by
  unfold actualCuspAngularQPoint cuspQ
  exact Complex.exp_ne_zero _

public theorem continuous_actualCuspAngularZeroRawLog :
    Continuous A.actualCuspAngularZeroRawLog := by
  have hq : Continuous A.actualCuspAngularQPoint := by
    unfold actualCuspAngularQPoint cuspQ
    fun_prop
  have hunitLog : Continuous
      (A.actualCuspFactorizationUnitLog ∘ A.actualCuspAngularQPoint) :=
    A.actualCuspFactorizationUnitLog_continuousOn.comp_continuous hq
      A.actualCuspAngularQPoint_mem_parameterBall
  unfold actualCuspAngularZeroRawLog
  fun_prop

public theorem actualCuspAngularZeroRawLog_exp (t : unitInterval) :
    Complex.exp (A.actualCuspAngularZeroRawLog t) =
      (A.actualCuspAngularCoordinateLoop t).1 := by
  unfold actualCuspAngularZeroRawLog
  rw [Complex.exp_neg, Complex.exp_add, Complex.exp_sub,
    Complex.exp_log A.actualCuspAngularQPoint_zero_ne,
    A.actualCuspFactorizationUnitLog_exp
      (A.actualCuspAngularQPoint_mem_parameterBall t)]
  have hq : A.actualCuspAngularQPoint 0 /
        Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
      A.actualCuspAngularQPoint t := by
    calc
      _ = A.actualCuspAngularQPoint 0 *
          Complex.exp (-((((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I))) := by
        rw [div_eq_mul_inv, ← Complex.exp_neg]
      _ = A.actualCuspAngularQPoint t :=
        (A.actualCuspAngularQPoint_apply t).symm
  rw [hq]
  rw [← A.actualCuspAngularCoordinateLoop_inv_apply]
  simp

/-- The raw logarithm gains exactly `2πi` around the selected cusp meridian. -/
public theorem actualCuspAngularZeroRawLog_one :
    A.actualCuspAngularZeroRawLog 1 =
      A.actualCuspAngularZeroRawLog 0 + 2 * Real.pi * Complex.I := by
  unfold actualCuspAngularZeroRawLog
  rw [A.actualCuspAngularQPoint_one]
  norm_num
  ring

/-! ## Normalize the lift at Mathlib's logarithmic basepoint -/

public def actualCuspAngularZeroPuncturedLoop :
    Path (twicePuncturedComplexForgetZero
      (A.centralFamilyCoordinate A.actualCuspCentralBase))
      (twicePuncturedComplexForgetZero
        (A.centralFamilyCoordinate A.actualCuspCentralBase)) :=
  A.actualCuspAngularCoordinateLoop.map twicePuncturedComplexForgetZero.continuous

public abbrev actualCuspAngularZeroPuncturedBasepoint : PuncturedComplex :=
  twicePuncturedComplexForgetZero
    (A.centralFamilyCoordinate A.actualCuspCentralBase)

public noncomputable def actualCuspAngularZeroLogLiftPoint
    (t : unitInterval) : ℂ :=
  Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 +
    (A.actualCuspAngularZeroRawLog t - A.actualCuspAngularZeroRawLog 0)

public theorem actualCuspAngularZeroLogLiftPoint_zero :
    A.actualCuspAngularZeroLogLiftPoint 0 =
      Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 := by
  simp [actualCuspAngularZeroLogLiftPoint]

public theorem actualCuspAngularZeroLogLiftPoint_one :
    A.actualCuspAngularZeroLogLiftPoint 1 =
      Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I) := by
  rw [actualCuspAngularZeroLogLiftPoint, A.actualCuspAngularZeroRawLog_one]
  simp

public theorem continuous_actualCuspAngularZeroLogLiftPoint :
    Continuous A.actualCuspAngularZeroLogLiftPoint := by
  unfold actualCuspAngularZeroLogLiftPoint
  exact continuous_const.add
    (A.continuous_actualCuspAngularZeroRawLog.sub continuous_const)

public theorem actualCuspAngularZeroLogLiftPoint_exp (t : unitInterval) :
    Complex.exp (A.actualCuspAngularZeroLogLiftPoint t) =
      (A.actualCuspAngularZeroPuncturedLoop t).1 := by
  rw [actualCuspAngularZeroLogLiftPoint,
    Complex.exp_add, Complex.exp_sub,
    Complex.exp_log A.actualCuspAngularZeroPuncturedBasepoint.2,
    A.actualCuspAngularZeroRawLog_exp,
    A.actualCuspAngularZeroRawLog_exp]
  have hbase : A.actualCuspAngularZeroPuncturedBasepoint.1 =
      (A.actualCuspAngularCoordinateLoop 0).1 := by
    change (A.centralFamilyCoordinate A.actualCuspCentralBase).1 =
      (A.actualCuspAngularCoordinateLoop 0).1
    exact (congrArg (fun z ↦ z.1)
      A.actualCuspAngularCoordinateLoop.source).symm
  rw [hbase]
  have hzero : (A.actualCuspAngularCoordinateLoop 0).1 ≠ 0 := by
    have h := (A.actualCuspAngularCoordinateLoop 0).2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at h
    exact h.1
  change (A.actualCuspAngularCoordinateLoop 0).1 *
      ((A.actualCuspAngularCoordinateLoop t).1 /
        (A.actualCuspAngularCoordinateLoop 0).1) =
      (A.actualCuspAngularCoordinateLoop t).1
  field_simp

public noncomputable def actualCuspAngularZeroLogLift :
    Path (Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1)
      (Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I)) where
  toFun := A.actualCuspAngularZeroLogLiftPoint
  continuous_toFun := A.continuous_actualCuspAngularZeroLogLiftPoint
  source' := A.actualCuspAngularZeroLogLiftPoint_zero
  target' := A.actualCuspAngularZeroLogLiftPoint_one

public theorem actualCuspAngularZeroLogLift_map_exp :
    ((A.actualCuspAngularZeroLogLift.map
        complexExpCoverContinuousMap.continuous).cast
      (complexExpCoverContinuousMap_log
        A.actualCuspAngularZeroPuncturedBasepoint.1
        A.actualCuspAngularZeroPuncturedBasepoint.2).symm
      (complexExpCoverContinuousMap_log_add_deck
        A.actualCuspAngularZeroPuncturedBasepoint.1
        A.actualCuspAngularZeroPuncturedBasepoint.2 1).symm) =
      A.actualCuspAngularZeroPuncturedLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact A.actualCuspAngularZeroLogLiftPoint_exp t

/-- Relative to the finite plane, the actual selected cusp meridian is exactly the `+1`
integer-circle class. -/
public theorem actualCuspAngularZero_loopClass_eq_integerCircle :
    Path.Homotopic.Quotient.mk A.actualCuspAngularZeroPuncturedLoop =
      Path.Homotopic.Quotient.mk
        (puncturedComplexIntegerCircle
          A.actualCuspAngularZeroPuncturedBasepoint.1
          A.actualCuspAngularZeroPuncturedBasepoint.2 1) := by
  exact puncturedComplex_loopClass_eq_integerCircle_of_lift
    A.actualCuspAngularZeroPuncturedBasepoint.1
    A.actualCuspAngularZeroPuncturedBasepoint.2 1
    A.actualCuspAngularZeroPuncturedLoop
    A.actualCuspAngularZeroLogLift
    A.actualCuspAngularZeroLogLift_map_exp

end SphereSixComplex.Geometry.PaperAnalyticData

end
