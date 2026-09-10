module

public import SphereSixComplex.Paper.Topology.PaperActualCuspMarkedLoop
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

public def cuspAngularQPoint (t : unitInterval) : ℂ :=
  cuspQ (A.actualCuspBoundaryCoverBase.1.2 - (t : ℝ))

public theorem cuspAngularQPoint_mem_parameterBall (t : unitInterval) :
    A.cuspAngularQPoint t ∈ A.actualCuspParameterBall := by
  rw [actualCuspParameterBall, Metric.mem_ball, dist_zero_right]
  unfold cuspAngularQPoint
  have hbase : ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ <
      A.starCuspWitness.localWitness.radius :=
    A.actualCuspBoundaryCoverBase.2
  rw [norm_cuspQ] at hbase ⊢
  simpa using hbase

/-- Along `s - t`, the completed cusp parameter makes one negative exponential turn. -/
public theorem cuspAngularQPoint_apply (t : unitInterval) :
    A.cuspAngularQPoint t =
      A.cuspAngularQPoint 0 *
        Complex.exp (-(((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  unfold cuspAngularQPoint cuspQ
  rw [show
    2 * (Real.pi : ℂ) * Complex.I *
          (A.actualCuspBoundaryCoverBase.1.2 - ((t : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I *
            (A.actualCuspBoundaryCoverBase.1.2 - (0 : ℂ)) +
          -(((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
  exact Complex.exp_add _ _

public theorem cuspAngularQPoint_one :
    A.cuspAngularQPoint 1 = A.cuspAngularQPoint 0 := by
  rw [A.cuspAngularQPoint_apply]
  norm_num [Complex.exp_neg, Complex.exp_two_pi_mul_I]

public theorem cuspAngularCoordinateLoop_inv_apply (t : unitInterval) :
    ((A.cuspAngularCoordinateLoop t).1)⁻¹ =
      A.cuspAngularQPoint t *
        A.actualCuspFactorizationUnit (A.cuspAngularQPoint t) := by
  rw [A.cuspAngularCoordinateLoop_apply]
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
public noncomputable def cuspAngularZeroRawLog (t : unitInterval) : ℂ :=
  -(Complex.log (A.cuspAngularQPoint 0) -
      (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) +
      A.actualCuspFactorizationUnitLog (A.cuspAngularQPoint t))

public theorem cuspAngularQPoint_zero_ne :
    A.cuspAngularQPoint 0 ≠ 0 := by
  unfold cuspAngularQPoint cuspQ
  exact Complex.exp_ne_zero _

public theorem continuous_actualCuspAngularZeroRawLog :
    Continuous A.cuspAngularZeroRawLog := by
  have hq : Continuous A.cuspAngularQPoint := by
    unfold cuspAngularQPoint cuspQ
    fun_prop
  have hunitLog : Continuous
      (A.actualCuspFactorizationUnitLog ∘ A.cuspAngularQPoint) :=
    A.actualCuspFactorizationUnitLog_continuousOn.comp_continuous hq
      A.cuspAngularQPoint_mem_parameterBall
  unfold cuspAngularZeroRawLog
  fun_prop

public theorem cuspAngularZeroRawLog_exp (t : unitInterval) :
    Complex.exp (A.cuspAngularZeroRawLog t) =
      (A.cuspAngularCoordinateLoop t).1 := by
  unfold cuspAngularZeroRawLog
  rw [Complex.exp_neg, Complex.exp_add, Complex.exp_sub,
    Complex.exp_log A.cuspAngularQPoint_zero_ne,
    A.actualCuspFactorizationUnitLog_exp
      (A.cuspAngularQPoint_mem_parameterBall t)]
  have hq : A.cuspAngularQPoint 0 /
        Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
      A.cuspAngularQPoint t := by
    calc
      _ = A.cuspAngularQPoint 0 *
          Complex.exp (-((((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I))) := by
        rw [div_eq_mul_inv, ← Complex.exp_neg]
      _ = A.cuspAngularQPoint t :=
        (A.cuspAngularQPoint_apply t).symm
  rw [hq]
  rw [← A.cuspAngularCoordinateLoop_inv_apply]
  simp

/-- The raw logarithm gains exactly `2πi` around the selected cusp meridian. -/
public theorem cuspAngularZeroRawLog_one :
    A.cuspAngularZeroRawLog 1 =
      A.cuspAngularZeroRawLog 0 + 2 * Real.pi * Complex.I := by
  unfold cuspAngularZeroRawLog
  rw [A.cuspAngularQPoint_one]
  norm_num
  ring

/-! ## Normalize the lift at Mathlib's logarithmic basepoint -/

public def cuspAngularZeroPuncturedLoop :
    Path (twicePuncturedComplexForgetZero
      (A.centralFamilyCoordinate A.actualCuspCentralBase))
      (twicePuncturedComplexForgetZero
        (A.centralFamilyCoordinate A.actualCuspCentralBase)) :=
  A.cuspAngularCoordinateLoop.map twicePuncturedComplexForgetZero.continuous

public abbrev cuspAngularZeroPuncturedBasepoint : PuncturedComplex :=
  twicePuncturedComplexForgetZero
    (A.centralFamilyCoordinate A.actualCuspCentralBase)

public noncomputable def cuspAngularZeroLogLiftPoint
    (t : unitInterval) : ℂ :=
  Complex.log A.cuspAngularZeroPuncturedBasepoint.1 +
    (A.cuspAngularZeroRawLog t - A.cuspAngularZeroRawLog 0)

public theorem cuspAngularZeroLogLiftPoint_zero :
    A.cuspAngularZeroLogLiftPoint 0 =
      Complex.log A.cuspAngularZeroPuncturedBasepoint.1 := by
  simp [cuspAngularZeroLogLiftPoint]

public theorem cuspAngularZeroLogLiftPoint_one :
    A.cuspAngularZeroLogLiftPoint 1 =
      Complex.log A.cuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I) := by
  rw [cuspAngularZeroLogLiftPoint, A.cuspAngularZeroRawLog_one]
  simp

public theorem continuous_actualCuspAngularZeroLogLiftPoint :
    Continuous A.cuspAngularZeroLogLiftPoint := by
  unfold cuspAngularZeroLogLiftPoint
  exact continuous_const.add
    (A.continuous_actualCuspAngularZeroRawLog.sub continuous_const)

public theorem cuspAngularZeroLogLiftPoint_exp (t : unitInterval) :
    Complex.exp (A.cuspAngularZeroLogLiftPoint t) =
      (A.cuspAngularZeroPuncturedLoop t).1 := by
  rw [cuspAngularZeroLogLiftPoint,
    Complex.exp_add, Complex.exp_sub,
    Complex.exp_log A.cuspAngularZeroPuncturedBasepoint.2,
    A.cuspAngularZeroRawLog_exp,
    A.cuspAngularZeroRawLog_exp]
  have hbase : A.cuspAngularZeroPuncturedBasepoint.1 =
      (A.cuspAngularCoordinateLoop 0).1 := by
    change (A.centralFamilyCoordinate A.actualCuspCentralBase).1 =
      (A.cuspAngularCoordinateLoop 0).1
    exact (congrArg (fun z ↦ z.1)
      A.cuspAngularCoordinateLoop.source).symm
  rw [hbase]
  have hzero : (A.cuspAngularCoordinateLoop 0).1 ≠ 0 := by
    have h := (A.cuspAngularCoordinateLoop 0).2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at h
    exact h.1
  change (A.cuspAngularCoordinateLoop 0).1 *
      ((A.cuspAngularCoordinateLoop t).1 /
        (A.cuspAngularCoordinateLoop 0).1) =
      (A.cuspAngularCoordinateLoop t).1
  field_simp

public noncomputable def cuspAngularZeroLogLift :
    Path (Complex.log A.cuspAngularZeroPuncturedBasepoint.1)
      (Complex.log A.cuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I)) where
  toFun := A.cuspAngularZeroLogLiftPoint
  continuous_toFun := A.continuous_actualCuspAngularZeroLogLiftPoint
  source' := A.cuspAngularZeroLogLiftPoint_zero
  target' := A.cuspAngularZeroLogLiftPoint_one

public theorem cuspAngularZeroLogLift_map_exp :
    ((A.cuspAngularZeroLogLift.map
        complexExpCoverContinuousMap.continuous).cast
      (complexExpCoverContinuousMap_log
        A.cuspAngularZeroPuncturedBasepoint.1
        A.cuspAngularZeroPuncturedBasepoint.2).symm
      (complexExpCoverContinuousMap_log_add_deck
        A.cuspAngularZeroPuncturedBasepoint.1
        A.cuspAngularZeroPuncturedBasepoint.2 1).symm) =
      A.cuspAngularZeroPuncturedLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact A.cuspAngularZeroLogLiftPoint_exp t

/-- Relative to the finite plane, the actual selected cusp meridian is exactly the `+1`
integer-circle class. -/
public theorem cuspAngularZero_loopClass_eq_integerCircle :
    Path.Homotopic.Quotient.mk A.cuspAngularZeroPuncturedLoop =
      Path.Homotopic.Quotient.mk
        (puncturedComplexIntegerCircle
          A.cuspAngularZeroPuncturedBasepoint.1
          A.cuspAngularZeroPuncturedBasepoint.2 1) := by
  exact puncturedComplex_loopClass_eq_integerCircle_of_lift
    A.cuspAngularZeroPuncturedBasepoint.1
    A.cuspAngularZeroPuncturedBasepoint.2 1
    A.cuspAngularZeroPuncturedLoop
    A.cuspAngularZeroLogLift
    A.cuspAngularZeroLogLift_map_exp

end SphereSixComplex.Geometry.PaperAnalyticData

end
