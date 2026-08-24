module

public import SphereSixComplex.Geometry.EllipticLogarithmicGauge
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Holomorphic logarithm charts on the elliptic collars

Every nonzero point of the Cayley disc lies in an explicit slit-plane logarithm chart.  Rotating
that chart gives the paired source and target branches used by the logarithmic elliptic gauges.
This supplies local branch coverage without asserting a global logarithm on the punctured disc.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.EllipticHolomorphicLogCover

open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup

/-- A slit-plane logarithm chart centered at a prescribed nonzero complex number. -/
public noncomputable def centeredLogBranch (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    HolomorphicLogBranch where
  carrier := (fun w : ℂ => starRingEnd ℂ z₀ * w) ⁻¹' Complex.slitPlane
  isOpen_carrier :=
    Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
  avoids_zero := by
    simp [Complex.mem_slitPlane_iff]
  log := fun w =>
    Complex.log (starRingEnd ℂ z₀ * w) - Complex.log (starRingEnd ℂ z₀)
  differentiableOn_log := by
    apply DifferentiableOn.sub_const
    apply DifferentiableOn.clog
    · fun_prop
    · intro w hw
      exact hw
  exp_log := by
    intro w hw
    rw [Complex.exp_sub, Complex.exp_log]
    · rw [Complex.exp_log ((map_ne_zero (starRingEnd ℂ)).2 hz₀)]
      exact mul_div_cancel_left₀ w ((map_ne_zero (starRingEnd ℂ)).2 hz₀)
    · intro hzero
      change starRingEnd ℂ z₀ * w ∈ Complex.slitPlane at hw
      rw [hzero] at hw
      simp [Complex.mem_slitPlane_iff] at hw

/-- The chosen center belongs to its logarithm chart. -/
public theorem mem_centeredLogBranch (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    z₀ ∈ (centeredLogBranch z₀ hz₀).carrier := by
  change starRingEnd ℂ z₀ * z₀ ∈ Complex.slitPlane
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_mem_slitPlane]
  exact Complex.normSq_pos.mpr hz₀

/-- Rotate a holomorphic logarithm chart by a scalar whose logarithmic increment is prescribed. -/
public noncomputable def rotatedLogBranchesOfScalar
    (m : ℕ) (rotation : Equiv.Perm ComplexUnitDisc)
    (theta rho : ℂ)
    (htheta : theta = ((2 : ℂ) * Real.pi * Complex.I) / m)
    (hrho : Complex.exp (-theta) = rho)
    (hrotation : ∀ w : ComplexUnitDisc, (rotation w : ℂ) = rho * (w : ℂ))
    (source : HolomorphicLogBranch) :
    RotatedLogBranches m rotation where
  source := source
  target :=
    { carrier := (fun z : ℂ => rho⁻¹ * z) ⁻¹' source.carrier
      isOpen_carrier :=
        source.isOpen_carrier.preimage (continuous_const.mul continuous_id)
      avoids_zero := by
        intro h
        exact source.avoids_zero (by simpa using h)
      log := fun z => source.log (rho⁻¹ * z) - theta
      differentiableOn_log := by
        have hinner : DifferentiableOn ℂ (fun z : ℂ => rho⁻¹ * z)
            ((fun z : ℂ => rho⁻¹ * z) ⁻¹' source.carrier) := by
          fun_prop
        have hmaps : MapsTo (fun z : ℂ => rho⁻¹ * z)
            ((fun z : ℂ => rho⁻¹ * z) ⁻¹' source.carrier) source.carrier :=
          fun _ hz => hz
        simpa [Function.comp_def] using
          (source.differentiableOn_log.comp hinner hmaps).sub_const theta
      exp_log := by
        intro z hz
        rw [sub_eq_add_neg, Complex.exp_add, source.exp_log _ hz, hrho]
        have hrhone : rho ≠ 0 := by
          rw [← hrho]
          exact Complex.exp_ne_zero _
        simp [mul_comm, hrhone] }
  rotation_mem := by
    intro w hw
    change rho⁻¹ * (rotation w : ℂ) ∈ source.carrier
    rw [hrotation]
    have hrhone : rho ≠ 0 := by
      rw [← hrho]
      exact Complex.exp_ne_zero _
    simpa [mul_assoc, hrhone] using hw
  log_rotation := by
    intro w _hw
    change source.log (rho⁻¹ * (rotation w : ℂ)) - theta =
      source.log w - ((2 : ℂ) * Real.pi * Complex.I) / m
    rw [hrotation]
    have hrhone : rho ≠ 0 := by
      rw [← hrho]
      exact Complex.exp_ne_zero _
    simp [mul_assoc, hrhone, htheta]

/-- The order-three Cayley multiplier is the required negative logarithmic increment. -/
public theorem exp_negative_orderThree_increment :
    Complex.exp (-(((2 : ℂ) * Real.pi * Complex.I) / 3)) =
      orderThreeMultiplier := by
  rw [show -(((2 : ℂ) * Real.pi * Complex.I) / 3) =
      (Real.pi / 3 : ℂ) * Complex.I - Real.pi * Complex.I by ring]
  rw [Complex.exp_sub_pi_mul_I, Complex.exp_mul_I]
  have hcast : (Real.pi / 3 : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) := by
    norm_num
  rw [hcast, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> norm_num [orderThreeMultiplier, div_eq_mul_inv]

/-- The order-four Cayley multiplier is the required negative logarithmic increment. -/
public theorem exp_negative_orderFour_increment :
    Complex.exp (-(((2 : ℂ) * Real.pi * Complex.I) / 4)) =
      orderFourMultiplier := by
  rw [show -(((2 : ℂ) * Real.pi * Complex.I) / 4) =
      -Real.pi / 2 * Complex.I by ring]
  exact Complex.exp_neg_pi_div_two_mul_I

/-- A point of the unit disc away from its center has nonzero complex coordinate. -/
public theorem coe_ne_zero_of_ne_center {w : ComplexUnitDisc} (hw : w ≠ discCenter) :
    (w : ℂ) ≠ 0 := by
  intro h
  apply hw
  apply Subtype.ext
  change (w : ℂ) = 0
  exact h

/-- Compatible order-three logarithm branches centered at a prescribed punctured-disc point. -/
public noncomputable def orderThreeBranchesAt
    (w : ComplexUnitDisc) (hw : w ≠ discCenter) :
    RotatedLogBranches 3 orderThreeDiscRotation :=
  rotatedLogBranchesOfScalar 3 orderThreeDiscRotation
    (((2 : ℂ) * Real.pi * Complex.I) / 3) orderThreeMultiplier rfl
    exp_negative_orderThree_increment
    (fun u => discScalarEquiv_apply_val orderThreeMultiplier norm_orderThreeMultiplier u)
    (centeredLogBranch w (coe_ne_zero_of_ne_center hw))

/-- Compatible order-four logarithm branches centered at a prescribed punctured-disc point. -/
public noncomputable def orderFourBranchesAt
    (w : ComplexUnitDisc) (hw : w ≠ discCenter) :
    RotatedLogBranches 4 orderFourDiscRotation :=
  rotatedLogBranchesOfScalar 4 orderFourDiscRotation
    (((2 : ℂ) * Real.pi * Complex.I) / 4) orderFourMultiplier rfl
    exp_negative_orderFour_increment
    (fun u => discScalarEquiv_apply_val orderFourMultiplier norm_orderFourMultiplier u)
    (centeredLogBranch w (coe_ne_zero_of_ne_center hw))

/-- The centered order-three source branch contains its prescribed point. -/
public theorem mem_orderThreeBranchesAt
    (w : ComplexUnitDisc) (hw : w ≠ discCenter) :
    (w : ℂ) ∈ (orderThreeBranchesAt w hw).source.carrier :=
  mem_centeredLogBranch w (coe_ne_zero_of_ne_center hw)

/-- The centered order-four source branch contains its prescribed point. -/
public theorem mem_orderFourBranchesAt
    (w : ComplexUnitDisc) (hw : w ≠ discCenter) :
    (w : ℂ) ∈ (orderFourBranchesAt w hw).source.carrier :=
  mem_centeredLogBranch w (coe_ne_zero_of_ne_center hw)

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The explicit order-three logarithm charts cover the entire punctured family collar. -/
public theorem exists_orderThreeBranches_covering
    (r : ℝ) (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ∃ B : RotatedLogBranches 3 orderThreeDiscRotation,
      q ∈ orderThreeLogarithmicGaugeCarrier F r B := by
  let w := orderThreeCayleyHomeomorph (familyTotalSpaceBase F q)
  have hw : w ≠ discCenter := by
    intro h
    have hpos := hq.1
    change 0 < ‖(w : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  refine ⟨orderThreeBranchesAt w hw, hq, ?_⟩
  change (w : ℂ) ∈ (orderThreeBranchesAt w hw).source.carrier
  exact mem_orderThreeBranchesAt w hw

/-- The explicit order-four logarithm charts cover the entire punctured family collar. -/
public theorem exists_orderFourBranches_covering
    (r : ℝ) (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ∃ B : RotatedLogBranches 4 orderFourDiscRotation,
      q ∈ orderFourLogarithmicGaugeCarrier F r B := by
  let w := orderFourCayleyHomeomorph (familyTotalSpaceBase F q)
  have hw : w ≠ discCenter := by
    intro h
    have hpos := hq.1
    change 0 < ‖(w : ℂ)‖ at hpos
    rw [h] at hpos
    norm_num [discCenter] at hpos
  refine ⟨orderFourBranchesAt w hw, hq, ?_⟩
  change (w : ℂ) ∈ (orderFourBranchesAt w hw).source.carrier
  exact mem_orderFourBranchesAt w hw

/-- Every point of the order-three punctured collar has a logarithm chart on which the affine
generator is conjugate to the linear family deck generator. -/
public theorem exists_orderThreeLocalGaugeConjugacy
    (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ∃ B : RotatedLogBranches 3 orderThreeDiscRotation,
      q ∈ orderThreeLogarithmicGaugeCarrier F r B ∧
        orderThreeLogarithmicGaugeMap F (fun w => B.target.log w)
            (orderThreeAffineFamilyGenerator F q) =
          familyDeckMap F g₁
            (orderThreeLogarithmicGaugeMap F (fun w => B.source.log w) q) := by
  obtain ⟨B, hqB⟩ := exists_orderThreeBranches_covering F r q hq
  refine ⟨B, hqB, ?_⟩
  exact orderThreeLogarithmicGauge_conjugates_generator_on F hsource B r hqB

/-- Every point of the order-four punctured collar has a logarithm chart on which the affine
generator is conjugate to the linear family deck generator. -/
public theorem exists_orderFourLocalGaugeConjugacy
    (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (q : TotalSpace (parameterMap F))
    (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ∃ B : RotatedLogBranches 4 orderFourDiscRotation,
      q ∈ orderFourLogarithmicGaugeCarrier F r B ∧
        orderFourLogarithmicGaugeMap F (fun w => B.target.log w)
            (orderFourAffineFamilyGenerator F q) =
          familyDeckMap F g₂
            (orderFourLogarithmicGaugeMap F (fun w => B.source.log w) q) := by
  obtain ⟨B, hqB⟩ := exists_orderFourBranches_covering F r q hq
  refine ⟨B, hqB, ?_⟩
  exact orderFourLogarithmicGauge_conjugates_generator_on F hsource B r hqB

end SphereSixComplex.Geometry.EllipticHolomorphicLogCover
