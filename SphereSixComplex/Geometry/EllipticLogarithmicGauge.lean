module

public import SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
import all SphereSixComplex.Geometry.GlobalTorusFamily
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Logarithmic gauges on the elliptic collars

The affine cyclic actions at the two elliptic fillings are conjugate to the linear family deck
actions on every collar chart carrying compatible branches of the logarithm.  The gauge is the
fiber translation by `(2 * pi * I)⁻¹ log(s) * Pi(z) v`, with `v = epsilon` at the order-three
point and `v = -epsilon'` at the order-four point.

The branch data below is deliberately local.  A single-valued logarithm on an entire punctured
disc does not exist.
-/

namespace SphereSixComplex.Geometry.EllipticLogarithmicGauge

open Matrix Set
open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- A holomorphic logarithm on an open subset of `C \ {0}`. -/
public structure HolomorphicLogBranch where
  carrier : Set ℂ
  isOpen_carrier : IsOpen carrier
  avoids_zero : 0 ∉ carrier
  log : ℂ → ℂ
  differentiableOn_log : DifferentiableOn ℂ log carrier
  exp_log : ∀ z ∈ carrier, Complex.exp (log z) = z

/-- Two local logarithm branches related by an order-`m` rotation. -/
public structure RotatedLogBranches
    (m : ℕ) (rotation : ComplexUnitDisc → ComplexUnitDisc) where
  source : HolomorphicLogBranch
  target : HolomorphicLogBranch
  rotation_mem : ∀ w : ComplexUnitDisc, (w : ℂ) ∈ source.carrier →
    (rotation w : ℂ) ∈ target.carrier
  log_rotation : ∀ w : ComplexUnitDisc, (w : ℂ) ∈ source.carrier →
    target.log (rotation w : ℂ) =
      source.log w - ((2 : ℂ) * Real.pi * Complex.I) / m

/-- The scalar multiplying the period vector in the logarithmic gauge. -/
@[expose] public noncomputable def logarithmicGaugeScalar (w : ℂ) : ℂ :=
  ((2 : ℂ) * Real.pi * Complex.I)⁻¹ * w

public theorem logarithmicGaugeScalar_sub_period (m : ℕ) (hm : m ≠ 0) (w : ℂ) :
    logarithmicGaugeScalar
        (w - ((2 : ℂ) * Real.pi * Complex.I) / m) +
      (m : ℂ)⁻¹ =
    logarithmicGaugeScalar w := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  simp only [logarithmicGaugeScalar]
  field_simp
  ring

public theorem logarithmicGaugeScalar_add_period (k : ℤ) (w : ℂ) :
    logarithmicGaugeScalar
        (w + ((2 : ℂ) * Real.pi * Complex.I) * k) =
      logarithmicGaugeScalar w + k := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  simp only [logarithmicGaugeScalar]
  field_simp

/-- Fiberwise translation section determined by a logarithm in a Cayley coordinate. -/
@[expose] public noncomputable def logarithmicGaugeSection
    (cayley : UpperHalfPlane → ComplexUnitDisc) (v : Lattice)
    (log : ComplexUnitDisc → ℂ) (z : UpperHalfPlane) : ComplexTwoSpace :=
  logarithmicGaugeScalar (log (cayley z)) •
    periodVector (parameterMap F z).1 v

public theorem periodVector_zsmul_complex
    (x : Parameters) (k : ℤ) (v : IntegerPeriods) :
    periodVector x (k • v) = (k : ℂ) • periodVector x v := by
  change periodHom x (k • v) = _
  rw [map_zsmul]
  change k • periodVector x v = (k : ℂ) • periodVector x v
  ext i
  simp [smul_eq_mul]

/-- Changing a logarithm branch by `2 * pi * I * k` changes the gauge section by the lattice
period `k * v`, so it induces the same map on the torus quotient. -/
public theorem logarithmicGaugeMap_mk_eq_of_branch_change
    (cayley : UpperHalfPlane → ComplexUnitDisc) (v : Lattice)
    (logOne logTwo : ComplexUnitDisc → ℂ)
    (z : UpperHalfPlane) (u : ComplexTwoSpace) (k : ℤ)
    (hlog : logTwo (cayley z) =
      logOne (cayley z) + ((2 : ℂ) * Real.pi * Complex.I) * k) :
    familyTranslationMap F
        (logarithmicGaugeSection F cayley v logTwo)
        (Quotient.mk _ (z, u)) =
      familyTranslationMap F
        (logarithmicGaugeSection F cayley v logOne)
        (Quotient.mk _ (z, u)) := by
  simp only [familyTranslationMap_mk, familyTranslationCover.eq_def]
  apply Quotient.sound
  change MulAction.orbitRel (FamilyPeriodGroup (parameterMap F))
    (UpperHalfPlane × ComplexTwoSpace)
    (z, logarithmicGaugeSection F cayley v logTwo z + u)
    (z, logarithmicGaugeSection F cayley v logOne z + u)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  let a : FamilyPeriodGroup (parameterMap F) :=
    Multiplicative.ofAdd (k • v)
  refine ⟨a, ?_⟩
  apply Prod.ext
  · rfl
  · change periodVector (parameterMap F z).1 (k • v) +
        (logarithmicGaugeSection F cayley v logOne z + u) =
      logarithmicGaugeSection F cayley v logTwo z + u
    rw [logarithmicGaugeSection, logarithmicGaugeSection, hlog,
      logarithmicGaugeScalar_add_period, periodVector_zsmul_complex]
    rw [add_smul]
    abel

@[expose] public noncomputable def orderThreeLogarithmicGaugeMap
    (log : ComplexUnitDisc → ℂ) :
    TotalSpace (parameterMap F) → TotalSpace (parameterMap F) :=
  familyTranslationMap F
    (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon log)

@[expose] public noncomputable def orderFourLogarithmicGaugeMap
    (log : ComplexUnitDisc → ℂ) :
    TotalSpace (parameterMap F) → TotalSpace (parameterMap F) :=
  familyTranslationMap F
    (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon') log)

/-- The part of the order-three punctured collar covered by the source branch. -/
@[expose] public def orderThreeLogarithmicGaugeCarrier
    (r : ℝ) (B : RotatedLogBranches 3 orderThreeDiscRotation) :
    Set (TotalSpace (parameterMap F)) :=
  orderThreePuncturedFamilyCollar F r ∩
    familyTotalSpaceBase F ⁻¹' {z |
      (orderThreeCayleyHomeomorph z : ℂ) ∈ B.source.carrier}

/-- The part of the order-four punctured collar covered by the source branch. -/
@[expose] public def orderFourLogarithmicGaugeCarrier
    (r : ℝ) (B : RotatedLogBranches 4 orderFourDiscRotation) :
    Set (TotalSpace (parameterMap F)) :=
  orderFourPuncturedFamilyCollar F r ∩
    familyTotalSpaceBase F ⁻¹' {z |
      (orderFourCayleyHomeomorph z : ℂ) ∈ B.source.carrier}

/-- Pointwise order-three logarithmic gauge conjugacy on quotient representatives. -/
public theorem orderThreeLogarithmicGauge_conjugates_generator_mk
    (hsource : U.sourceAction = fuchsianSourceAction)
    (sourceLog targetLog : ComplexUnitDisc → ℂ) (z : UpperHalfPlane)
    (hlog :
      targetLog (orderThreeDiscRotation (orderThreeCayleyHomeomorph z)) =
        sourceLog (orderThreeCayleyHomeomorph z) -
          ((2 : ℂ) * Real.pi * Complex.I) / 3)
    (v : ComplexTwoSpace) :
    familyTranslationMap F
        (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon targetLog)
        (orderThreeAffineFamilyGenerator F (Quotient.mk _ (z, v))) =
      familyDeckMap F g₁
        (familyTranslationMap F
          (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon sourceLog)
          (Quotient.mk _ (z, v))) := by
  simp only [orderThreeAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
    familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def,
    familyTranslationEquiv_apply, familyTranslationMap_mk,
    familyTranslationCover.eq_def, logarithmicGaugeSection, map_add]
  apply congrArg (Quotient.mk _)
  apply Prod.ext
  · rfl
  · have hcayley :
        orderThreeCayleyHomeomorph (U.sourceAction g₁ • z) =
          orderThreeDiscRotation (orderThreeCayleyHomeomorph z) := by
      rw [hsource, orderThreeCayleyHomeomorph_generator]
    have hparam := parameterMap_equivariant F g₁
    rw [ParameterEquivariant.eq_def] at hparam
    rw [hcayley, hlog, orderThreeTwistSection.eq_def, hparam z,
      rhoParameters_g₁_apply, periodTransport_gOne]
    change
      logarithmicGaugeScalar
            (sourceLog (orderThreeCayleyHomeomorph z) -
              ((2 : ℂ) * Real.pi * Complex.I) / 3) •
          periodVector (transformOne (parameterMap F z).1) epsilon +
        ((3 : ℂ)⁻¹ •
            periodVector (transformOne (parameterMap F z).1) epsilon +
          rightOneLinearEquiv (parameterMap F z).1
            (parameterMap F z).tau_ne_zero v) =
      rightOneLinearEquiv (parameterMap F z).1
          (parameterMap F z).tau_ne_zero
          (logarithmicGaugeScalar
              (sourceLog (orderThreeCayleyHomeomorph z)) •
            periodVector (parameterMap F z).1 epsilon) +
        rightOneLinearEquiv (parameterMap F z).1
          (parameterMap F z).tau_ne_zero v
    rw [map_smul]
    simp_rw [rightOneLinearEquiv_apply]
    rw [← generatorOne_periodVector (parameterMap F z).1
      (parameterMap F z).tau_ne_zero epsilon, a₁_apply, A₁_epsilon]
    rw [← add_assoc, ← add_smul]
    have hscalar :
        logarithmicGaugeScalar
              (sourceLog (orderThreeCayleyHomeomorph z) -
                ((2 : ℂ) * Real.pi * Complex.I) / 3) +
            (3 : ℂ)⁻¹ =
          logarithmicGaugeScalar
            (sourceLog (orderThreeCayleyHomeomorph z)) := by
      simpa using
        logarithmicGaugeScalar_sub_period 3 (by decide)
          (sourceLog (orderThreeCayleyHomeomorph z))
    rw [hscalar]

/-- Pointwise order-four logarithmic gauge conjugacy on quotient representatives. -/
public theorem orderFourLogarithmicGauge_conjugates_generator_mk
    (hsource : U.sourceAction = fuchsianSourceAction)
    (sourceLog targetLog : ComplexUnitDisc → ℂ) (z : UpperHalfPlane)
    (hlog :
      targetLog (orderFourDiscRotation (orderFourCayleyHomeomorph z)) =
        sourceLog (orderFourCayleyHomeomorph z) -
          ((2 : ℂ) * Real.pi * Complex.I) / 4)
    (v : ComplexTwoSpace) :
    familyTranslationMap F
        (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon') targetLog)
        (orderFourAffineFamilyGenerator F (Quotient.mk _ (z, v))) =
      familyDeckMap F g₂
        (familyTranslationMap F
          (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon') sourceLog)
          (Quotient.mk _ (z, v))) := by
  simp only [orderFourAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
    familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def,
    familyTranslationEquiv_apply, familyTranslationMap_mk,
    familyTranslationCover.eq_def, logarithmicGaugeSection, map_add]
  apply congrArg (Quotient.mk _)
  apply Prod.ext
  · rfl
  · have hcayley :
        orderFourCayleyHomeomorph (U.sourceAction g₂ • z) =
          orderFourDiscRotation (orderFourCayleyHomeomorph z) := by
      rw [hsource, orderFourCayleyHomeomorph_generator]
    have hparam := parameterMap_equivariant F g₂
    rw [ParameterEquivariant.eq_def] at hparam
    rw [hcayley, hlog, orderFourTwistSection.eq_def, hparam z,
      rhoParameters_g₂_apply, periodTransport_gTwo]
    change
      logarithmicGaugeScalar
            (sourceLog (orderFourCayleyHomeomorph z) -
              ((2 : ℂ) * Real.pi * Complex.I) / 4) •
          periodVector (transformTwo (parameterMap F z).1) (-epsilon') +
        ((4 : ℂ)⁻¹ •
            periodVector (transformTwo (parameterMap F z).1) (-epsilon') +
          rightTwoLinearEquiv (parameterMap F z).1
            (parameterMap F z).tau_ne_zero v) =
      rightTwoLinearEquiv (parameterMap F z).1
          (parameterMap F z).tau_ne_zero
          (logarithmicGaugeScalar
              (sourceLog (orderFourCayleyHomeomorph z)) •
            periodVector (parameterMap F z).1 (-epsilon')) +
        rightTwoLinearEquiv (parameterMap F z).1
          (parameterMap F z).tau_ne_zero v
    rw [map_smul]
    simp_rw [rightTwoLinearEquiv_apply]
    rw [← generatorTwo_periodVector (parameterMap F z).1
      (parameterMap F z).tau_ne_zero (-epsilon'), a₂_apply,
      Matrix.mulVec_neg, A₂_epsilon']
    rw [← add_assoc, ← add_smul]
    have hscalar :
        logarithmicGaugeScalar
              (sourceLog (orderFourCayleyHomeomorph z) -
                ((2 : ℂ) * Real.pi * Complex.I) / 4) +
            (4 : ℂ)⁻¹ =
          logarithmicGaugeScalar
            (sourceLog (orderFourCayleyHomeomorph z)) := by
      simpa using
        logarithmicGaugeScalar_sub_period 4 (by decide)
          (sourceLog (orderFourCayleyHomeomorph z))
    rw [hscalar]

/-- On every compatible logarithm chart in the order-three punctured collar, the affine cyclic
generator is conjugate to the linear family deck generator. -/
public theorem orderThreeLogarithmicGauge_conjugates_generator_on
    (hsource : U.sourceAction = fuchsianSourceAction)
    (B : RotatedLogBranches 3 orderThreeDiscRotation) (r : ℝ) :
    Set.EqOn
      (orderThreeLogarithmicGaugeMap F (fun w => B.target.log w) ∘
        orderThreeAffineFamilyGenerator F)
      (familyDeckMap F g₁ ∘
        orderThreeLogarithmicGaugeMap F (fun w => B.source.log w))
      (orderThreeLogarithmicGaugeCarrier F r B) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    apply orderThreeLogarithmicGauge_conjugates_generator_mk
      F hsource (fun w => B.source.log w) (fun w => B.target.log w) p.1
    exact B.log_rotation _ hq.2

/-- On every compatible logarithm chart in the order-four punctured collar, the affine cyclic
generator is conjugate to the linear family deck generator. -/
public theorem orderFourLogarithmicGauge_conjugates_generator_on
    (hsource : U.sourceAction = fuchsianSourceAction)
    (B : RotatedLogBranches 4 orderFourDiscRotation) (r : ℝ) :
    Set.EqOn
      (orderFourLogarithmicGaugeMap F (fun w => B.target.log w) ∘
        orderFourAffineFamilyGenerator F)
      (familyDeckMap F g₂ ∘
        orderFourLogarithmicGaugeMap F (fun w => B.source.log w))
      (orderFourLogarithmicGaugeCarrier F r B) := by
  intro q hq
  induction q using Quotient.inductionOn with
  | _ p =>
    apply orderFourLogarithmicGauge_conjugates_generator_mk
      F hsource (fun w => B.source.log w) (fun w => B.target.log w) p.1
    exact B.log_rotation _ hq.2

end

end SphereSixComplex.Geometry.EllipticLogarithmicGauge
