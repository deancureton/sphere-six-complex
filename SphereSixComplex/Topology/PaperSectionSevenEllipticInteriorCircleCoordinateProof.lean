module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianDegreeOneProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspDegreeOneIndexTwoProof
public import SphereSixComplex.Geometry.EllipticAffineCuspObstruction
public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus
public import SphereSixComplex.Topology.TwicePuncturedComplexMarkedMeridians
public import SphereSixComplex.Topology.PaperSectionSevenEllipticBaseCoordinate
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

noncomputable section

open Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Rescaling angles modulo `2π` to real numbers modulo one. -/
public noncomputable def angleToUnitAddCircle : Real.Angle ≃ₜ UnitAddCircle := by
  change AddCircle (2 * Real.pi) ≃ₜ AddCircle (1 : ℝ)
  exact AddCircle.homeomorphAddCircle (2 * Real.pi) 1
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) one_ne_zero

/-- The continuously varying argument class of a nonzero complex number. -/
public noncomputable def puncturedComplexAngle : C(PuncturedComplex, Real.Angle) where
  toFun z := (Complex.arg z.1 : Real.Angle)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (Complex.continuousAt_arg_coe_angle z.2).comp continuousAt_subtype_val

/-- The normalized argument of a nonzero complex number, valued in `ℝ / ℤ`. -/
public noncomputable def puncturedComplexPhase : C(PuncturedComplex, UnitAddCircle) :=
  (angleToUnitAddCircle : C(Real.Angle, UnitAddCircle)).comp puncturedComplexAngle

@[simp]
public theorem puncturedComplexPhase_apply (z : PuncturedComplex) :
    puncturedComplexPhase z =
      (((Complex.arg z.1 / (2 * Real.pi) : ℝ)) : UnitAddCircle) := by
  change angleToUnitAddCircle (Complex.arg z.1 : Real.Angle) = _
  change (((Complex.arg z.1) * ((2 * Real.pi)⁻¹ * 1) : ℝ) : UnitAddCircle) = _
  congr 1
  field_simp

public theorem puncturedComplexPhase_mul (x y : PuncturedComplex) :
    puncturedComplexPhase
        ⟨x.1 * y.1, mul_ne_zero x.2 y.2⟩ =
      puncturedComplexPhase x + puncturedComplexPhase y := by
  change angleToUnitAddCircle (Complex.arg (x.1 * y.1) : Real.Angle) =
    angleToUnitAddCircle (Complex.arg x.1 : Real.Angle) +
      angleToUnitAddCircle (Complex.arg y.1 : Real.Angle)
  rw [Complex.arg_mul_coe_angle x.2 y.2]
  change AddCircle.equivAddCircle (2 * Real.pi) 1
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) one_ne_zero
        ((Complex.arg x.1 : Real.Angle) + (Complex.arg y.1 : Real.Angle)) = _
  exact map_add _ _ _

public theorem puncturedComplexPhase_inv (x : PuncturedComplex) :
    puncturedComplexPhase ⟨x.1⁻¹, inv_ne_zero x.2⟩ =
      -puncturedComplexPhase x := by
  change angleToUnitAddCircle (Complex.arg x.1⁻¹ : Real.Angle) =
    -angleToUnitAddCircle (Complex.arg x.1 : Real.Angle)
  rw [Complex.arg_inv_coe_angle]
  change AddCircle.equivAddCircle (2 * Real.pi) 1
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) one_ne_zero
        (-(Complex.arg x.1 : Real.Angle)) = _
  exact map_neg _ _

/-- The normalized phase of the exponential cusp parameter is its real additive coordinate. -/
public theorem puncturedComplexPhase_cuspQ (s : ℂ) :
    puncturedComplexPhase
        ⟨SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s,
          Complex.exp_ne_zero _⟩ =
      ((s.re : ℝ) : UnitAddCircle) := by
  have hang :
      (Complex.arg
          (SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s) : Real.Angle) =
        ((2 * Real.pi * s.re : ℝ) : Real.Angle) := by
    unfold SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ
    rw [Complex.arg_exp]
    rw [Real.Angle.coe_toIocMod]
    congr 1
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
  change angleToUnitAddCircle
      (Complex.arg
        (SphereSixComplex.Geometry.CuspPeriodExpansion.cuspQ s) : Real.Angle) = _
  rw [hang]
  change (((2 * Real.pi * s.re) * ((2 * Real.pi)⁻¹ * 1) : ℝ) :
      UnitAddCircle) = _
  congr 1
  field_simp

/-- Forgetting the second puncture gives a map to the ordinary punctured plane. -/
public def twicePuncturedToZeroPunctured : C(TwicePuncturedComplex, PuncturedComplex) where
  toFun z := ⟨z.1, by
    have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] using z.2
    exact hz.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ by
    have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] using z.2
    exact hz.1

/-- Translating the second puncture to zero gives a map to the punctured plane. -/
public def twicePuncturedToOnePunctured : C(TwicePuncturedComplex, PuncturedComplex) where
  toFun z := ⟨z.1 - 1, sub_ne_zero.mpr (by
    have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] using z.2
    exact hz.2)⟩
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk fun z ↦
    sub_ne_zero.mpr (by
      have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using z.2
      exact hz.2)

/-- The phase around the zero puncture of the twice-punctured affine base. -/
public def twicePuncturedZeroPhase : C(TwicePuncturedComplex, UnitAddCircle) :=
  puncturedComplexPhase.comp twicePuncturedToZeroPunctured

/-- The phase around the one puncture of the twice-punctured affine base. -/
public def twicePuncturedOnePhase : C(TwicePuncturedComplex, UnitAddCircle) :=
  puncturedComplexPhase.comp twicePuncturedToOnePunctured

/-- The nonvanishing factor `1 - z⁻¹` on the twice-punctured affine base. -/
public def twicePuncturedInfinityUnit : C(TwicePuncturedComplex, PuncturedComplex) where
  toFun z := ⟨1 - z.1⁻¹, sub_ne_zero.mpr (by
    intro h
    have hz : z.1 = 1 := inv_eq_one.mp h.symm
    have hz' : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] using z.2
    exact hz'.2 hz)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_const.sub (continuous_subtype_val.inv₀ fun z ↦ by
      have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using z.2
      exact hz.1)) _

/-- The base correction dictated by the two elliptic isotropy orders. -/
public def ellipticOrbifoldBasePhase : C(TwicePuncturedComplex, UnitAddCircle) where
  toFun z := (-4 : ℤ) • twicePuncturedZeroPhase z +
    (3 : ℤ) • twicePuncturedOnePhase z
  continuous_toFun := by fun_prop

@[simp]
public theorem ellipticOrbifoldBasePhase_apply (z : TwicePuncturedComplex) :
    ellipticOrbifoldBasePhase z =
      (-4 : ℤ) • (((Complex.arg z.1 / (2 * Real.pi) : ℝ)) : UnitAddCircle) +
      (3 : ℤ) • (((Complex.arg (z.1 - 1) / (2 * Real.pi) : ℝ)) : UnitAddCircle) := by
  change (-4 : ℤ) • puncturedComplexPhase (twicePuncturedToZeroPunctured z) +
      (3 : ℤ) • puncturedComplexPhase (twicePuncturedToOnePunctured z) = _
  rw [puncturedComplexPhase_apply, puncturedComplexPhase_apply]
  rfl

/-- At the exterior end the correction is one copy of the inverse radial phase, plus a
zero-winding unit term. -/
public theorem ellipticOrbifoldBasePhase_infinity_normalForm
    (z : TwicePuncturedComplex) :
    ellipticOrbifoldBasePhase z =
      -twicePuncturedZeroPhase z +
        (3 : ℤ) • puncturedComplexPhase (twicePuncturedInfinityUnit z) := by
  have hz0 : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] using z.2
  have hfactor : z.1 - 1 = z.1 * (1 - z.1⁻¹) := by
    field_simp [hz0.1]
  have hphase : twicePuncturedOnePhase z =
      twicePuncturedZeroPhase z +
        puncturedComplexPhase (twicePuncturedInfinityUnit z) := by
    change puncturedComplexPhase (twicePuncturedToOnePunctured z) = _
    rw [show twicePuncturedToOnePunctured z =
        ⟨z.1 * (1 - z.1⁻¹), mul_ne_zero hz0.1 (twicePuncturedInfinityUnit z).2⟩ by
      apply Subtype.ext
      exact hfactor]
    exact puncturedComplexPhase_mul
      (twicePuncturedToZeroPunctured z) (twicePuncturedInfinityUnit z)
  change (-4 : ℤ) • twicePuncturedZeroPhase z +
      (3 : ℤ) • twicePuncturedOnePhase z = _
  rw [hphase]
  module

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open AlgebraicTopology CategoryTheory
open SphereSixComplex
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus

variable (A : PaperAnalyticData)

/-- Twelve times the invariant period character on the universal vector cover of the regular
torus family. -/
public noncomputable def regularTwelveGammaRaw :
    UpperHalfPlane × ComplexTwoSpace → UnitAddCircle :=
  fun p ↦ (((12 * gammaCoordinate (parameterMap A.periods p.1) p.2 : ℝ)) : UnitAddCircle)

public theorem regularTwelveGammaRaw_continuous :
    Continuous A.regularTwelveGammaRaw := by
  apply continuous_quotient_mk'.comp
  convert (continuous_const : Continuous
      (fun _ : UpperHalfPlane × ComplexTwoSpace ↦ (12 : ℝ))).mul
    ((continuous_apply 0).comp
      (periodCoordinates_parameterMap_continuous A.periods)) using 1
  funext p
  change 12 * gammaReal (periodCoordinates (parameterMap A.periods p.1) p.2) =
    12 * periodCoordinates (parameterMap A.periods p.1) p.2 0
  rw [gammaReal_eq_head]

public theorem regularTwelveGammaRaw_family_period_invariant
    (g : FamilyPeriodGroup (parameterMap A.periods))
    (p : UpperHalfPlane × ComplexTwoSpace) :
    A.regularTwelveGammaRaw (g • p) = A.regularTwelveGammaRaw p := by
  change (((12 * gammaCoordinate (parameterMap A.periods p.1)
      (periodVector (parameterMap A.periods p.1).1 g.coeff + p.2) : ℝ)) :
        UnitAddCircle) = _
  rw [map_add, gammaCoordinate_periodVector]
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨12 * gamma g.coeff, ?_⟩
  push_cast
  ring

/-- The twelvefold gamma character descends continuously to the varying regular torus family. -/
public noncomputable def regularTwelveGamma :
    C(TotalSpace (parameterMap A.periods), UnitAddCircle) where
  toFun := Quotient.lift A.regularTwelveGammaRaw fun p q h ↦ by
    change MulAction.orbitRel (FamilyPeriodGroup (parameterMap A.periods))
      (UpperHalfPlane × ComplexTwoSpace) p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, rfl⟩ := h
    exact A.regularTwelveGammaRaw_family_period_invariant g q
  continuous_toFun := by
    apply continuous_quot_lift
      (fun p q h ↦ by
        change MulAction.orbitRel (FamilyPeriodGroup (parameterMap A.periods))
          (UpperHalfPlane × ComplexTwoSpace) p q at h
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
        obtain ⟨g, rfl⟩ := h
        exact A.regularTwelveGammaRaw_family_period_invariant g q)
    exact A.regularTwelveGammaRaw_continuous

@[simp]
public theorem regularTwelveGamma_projection
    (p : UpperHalfPlane × ComplexTwoSpace) :
    A.regularTwelveGamma (projection (parameterMap A.periods) p) =
      A.regularTwelveGammaRaw p :=
  rfl

public theorem regularTwelveGamma_orderThreeGenerator
    (q : TotalSpace (parameterMap A.periods)) :
    A.regularTwelveGamma (orderThreeAffineFamilyGenerator A.periods q) =
      A.regularTwelveGamma q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      simp only [orderThreeAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
        familyTranslationEquiv_apply, familyDeckEquiv_apply,
        familyTranslationMap_mk, familyDeckMap_mk, deckMap.eq_def,
        familyTranslationCover.eq_def]
      change A.regularTwelveGammaRaw
        (A.modular.modularParameter.toTriangleUniformization.sourceAction
            SphereSixComplex.TriangleGroup.g₁ • p.1,
          orderThreeTwistSection A.periods
              (A.modular.modularParameter.toTriangleUniformization.sourceAction
                SphereSixComplex.TriangleGroup.g₁ • p.1) +
            periodTransport SphereSixComplex.TriangleGroup.g₁
              (parameterMap A.periods p.1) p.2) =
        A.regularTwelveGammaRaw p
      change (((12 * gammaCoordinate
          (parameterMap A.periods
            (A.modular.modularParameter.toTriangleUniformization.sourceAction
              SphereSixComplex.TriangleGroup.g₁ • p.1))
          (orderThreeTwistSection A.periods
              (A.modular.modularParameter.toTriangleUniformization.sourceAction
                SphereSixComplex.TriangleGroup.g₁ • p.1) +
            periodTransport SphereSixComplex.TriangleGroup.g₁
              (parameterMap A.periods p.1) p.2) : ℝ)) : UnitAddCircle) = _
      have hparam := parameterMap_equivariant A.periods
        SphereSixComplex.TriangleGroup.g₁
      rw [ParameterEquivariant.eq_def] at hparam
      rw [hparam p.1, map_add,
        EllipticAffineCuspObstruction.gammaCoordinate_transport_gOne,
        orderThreeTwistSection.eq_def, hparam p.1,
        EllipticAffineCuspObstruction.gammaCoordinate_oneThirdPeriod]
      apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
      refine ⟨4, ?_⟩
      norm_num
      ring

public theorem regularTwelveGamma_orderFourGenerator
    (q : TotalSpace (parameterMap A.periods)) :
    A.regularTwelveGamma (orderFourAffineFamilyGenerator A.periods q) =
      A.regularTwelveGamma q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      simp only [orderFourAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
        familyTranslationEquiv_apply, familyDeckEquiv_apply,
        familyTranslationMap_mk, familyDeckMap_mk, deckMap.eq_def,
        familyTranslationCover.eq_def]
      change A.regularTwelveGammaRaw
        (A.modular.modularParameter.toTriangleUniformization.sourceAction
            SphereSixComplex.TriangleGroup.g₂ • p.1,
          orderFourTwistSection A.periods
              (A.modular.modularParameter.toTriangleUniformization.sourceAction
                SphereSixComplex.TriangleGroup.g₂ • p.1) +
            periodTransport SphereSixComplex.TriangleGroup.g₂
              (parameterMap A.periods p.1) p.2) =
        A.regularTwelveGammaRaw p
      change (((12 * gammaCoordinate
          (parameterMap A.periods
            (A.modular.modularParameter.toTriangleUniformization.sourceAction
              SphereSixComplex.TriangleGroup.g₂ • p.1))
          (orderFourTwistSection A.periods
              (A.modular.modularParameter.toTriangleUniformization.sourceAction
                SphereSixComplex.TriangleGroup.g₂ • p.1) +
            periodTransport SphereSixComplex.TriangleGroup.g₂
              (parameterMap A.periods p.1) p.2) : ℝ)) : UnitAddCircle) = _
      have hparam := parameterMap_equivariant A.periods
        SphereSixComplex.TriangleGroup.g₂
      rw [ParameterEquivariant.eq_def] at hparam
      have htransport : gammaCoordinate
          (rhoParameters SphereSixComplex.TriangleGroup.g₂
            (parameterMap A.periods p.1))
          (periodTransport SphereSixComplex.TriangleGroup.g₂
            (parameterMap A.periods p.1) p.2) =
          gammaCoordinate (parameterMap A.periods p.1) p.2 := by
        change gammaReal (periodCoordinates _ _) = gammaReal (periodCoordinates _ _)
        rw [periodCoordinates_transport, gammaReal_rhoLambdaReal_gTwo]
      rw [hparam p.1, map_add,
        htransport,
        orderFourTwistSection.eq_def, hparam p.1,
        EllipticAffineCuspObstruction.gammaCoordinate_negOneQuarterPeriod]
      apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
      refine ⟨-3, ?_⟩
      norm_num
      ring

public theorem regularTwelveGamma_orderThreeRepresentation
    (g : FiniteCyclic 3) (q : TotalSpace (parameterMap A.periods)) :
    A.regularTwelveGamma (orderThreeAffineFamilyRepresentation A.periods g q) =
      A.regularTwelveGamma q := by
  have hgen : orderThreeAffineFamilyRepresentation A.periods (cyclicGenerator 3) =
      orderThreeAffineFamilyGenerator A.periods := by
    change cyclicRepresentation 3 (orderThreeAffineFamilyGenerator A.periods)
      (orderThreeAffineFamilyGenerator_pow A.periods) (Multiplicative.ofAdd 1) = _
    exact cyclicRepresentation_generator 3 _ _
  generalize hk : (Multiplicative.toAdd g).val = k
  rw [cyclic_eq_generator_pow g, map_pow, hk]
  clear hk g
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      rw [hgen]
      exact regularTwelveGamma_orderThreeGenerator A q

public theorem regularTwelveGamma_orderFourRepresentation
    (g : FiniteCyclic 4) (q : TotalSpace (parameterMap A.periods)) :
    A.regularTwelveGamma (orderFourAffineFamilyRepresentation A.periods g q) =
      A.regularTwelveGamma q := by
  have hgen : orderFourAffineFamilyRepresentation A.periods (cyclicGenerator 4) =
      orderFourAffineFamilyGenerator A.periods := by
    change cyclicRepresentation 4 (orderFourAffineFamilyGenerator A.periods)
      (orderFourAffineFamilyGenerator_pow A.periods) (Multiplicative.ofAdd 1) = _
    exact cyclicRepresentation_generator 4 _ _
  generalize hk : (Multiplicative.toAdd g).val = k
  rw [cyclic_eq_generator_pow g, map_pow, hk]
  clear hk g
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      rw [hgen]
      exact regularTwelveGamma_orderFourGenerator A q

/-- The invariant twelvefold character on the order-three filling quotient. -/
public noncomputable def orderThreeFillingTwelveGamma
    (r : ℝ) : C(A.OrderThreeVaryingFilling r, UnitAddCircle) := by
  let _ := A.orderThreeFillingAction r
  refine
    { toFun := Quotient.lift
        (fun q : A.orderThreeFillingOpen r ↦ A.regularTwelveGamma q.1) ?_
      continuous_toFun := ?_ }
  · intro p q h
    change MulAction.orbitRel (FiniteCyclic 3) (A.orderThreeFillingOpen r) p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, rfl⟩ := h
    change A.regularTwelveGamma
        (orderThreeAffineFamilyRepresentation A.periods g q.1) =
      A.regularTwelveGamma q.1
    exact A.regularTwelveGamma_orderThreeRepresentation g q.1
  · apply continuous_quot_lift
      (fun p q h ↦ by
        change MulAction.orbitRel (FiniteCyclic 3) (A.orderThreeFillingOpen r) p q at h
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
        obtain ⟨g, rfl⟩ := h
        change A.regularTwelveGamma
            (orderThreeAffineFamilyRepresentation A.periods g q.1) =
          A.regularTwelveGamma q.1
        exact A.regularTwelveGamma_orderThreeRepresentation g q.1)
    exact A.regularTwelveGamma.continuous.comp continuous_subtype_val

/-- The invariant twelvefold character on the order-four filling quotient. -/
public noncomputable def orderFourFillingTwelveGamma
    (r : ℝ) : C(A.OrderFourVaryingFilling r, UnitAddCircle) := by
  let _ := A.orderFourFillingAction r
  refine
    { toFun := Quotient.lift
        (fun q : A.orderFourFillingOpen r ↦ A.regularTwelveGamma q.1) ?_
      continuous_toFun := ?_ }
  · intro p q h
    change MulAction.orbitRel (FiniteCyclic 4) (A.orderFourFillingOpen r) p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, rfl⟩ := h
    change A.regularTwelveGamma
        (orderFourAffineFamilyRepresentation A.periods g q.1) =
      A.regularTwelveGamma q.1
    exact A.regularTwelveGamma_orderFourRepresentation g q.1
  · apply continuous_quot_lift
      (fun p q h ↦ by
        change MulAction.orbitRel (FiniteCyclic 4) (A.orderFourFillingOpen r) p q at h
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
        obtain ⟨g, rfl⟩ := h
        change A.regularTwelveGamma
            (orderFourAffineFamilyRepresentation A.periods g q.1) =
          A.regularTwelveGamma q.1
        exact A.regularTwelveGamma_orderFourRepresentation g q.1)
    exact A.regularTwelveGamma.continuous.comp continuous_subtype_val

@[simp]
public theorem orderThreeFillingTwelveGamma_mk
    (r : ℝ) (q : A.orderThreeFillingOpen r) :
    A.orderThreeFillingTwelveGamma r (Quotient.mk _ q) =
      A.regularTwelveGamma q.1 :=
  rfl

@[simp]
public theorem orderFourFillingTwelveGamma_mk
    (r : ℝ) (q : A.orderFourFillingOpen r) :
    A.orderFourFillingTwelveGamma r (Quotient.mk _ q) =
      A.regularTwelveGamma q.1 :=
  rfl

public theorem gammaReal_rhoLambdaReal (g : Delta) (u : RealPeriods) :
    gammaReal (rhoLambdaReal g u) = gammaReal u := by
  induction g using Monoid.Coprod.induction_on generalizing u with
  | inl a =>
      obtain ⟨n, hn⟩ := inl_exists_gOne_pow a
      rw [hn, map_pow]
      clear hn a
      induction n generalizing u with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, LinearEquiv.mul_apply, ih,
            gammaReal_rhoLambdaReal_gOne]
  | inr a =>
      obtain ⟨n, hn⟩ := inr_exists_gTwo_pow a
      rw [hn, map_pow]
      clear hn a
      induction n generalizing u with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, LinearEquiv.mul_apply, ih,
            gammaReal_rhoLambdaReal_gTwo]
  | mul g h hg hh =>
      rw [map_mul, LinearEquiv.mul_apply, hg, hh]

public theorem regularTwelveGamma_familyDeckEquiv
    (g : Delta) (q : TotalSpace (parameterMap A.periods)) :
    A.regularTwelveGamma (familyDeckEquiv A.periods g q) =
      A.regularTwelveGamma q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      simp only [familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def]
      change A.regularTwelveGammaRaw
          (A.modular.modularParameter.toTriangleUniformization.sourceAction g • p.1,
            periodTransport g (parameterMap A.periods p.1) p.2) =
        A.regularTwelveGammaRaw p
      have hparam := parameterMap_equivariant A.periods g
      rw [ParameterEquivariant.eq_def] at hparam
      change (((12 * gammaReal
          (periodCoordinates
            (parameterMap A.periods
              (A.modular.modularParameter.toTriangleUniformization.sourceAction g • p.1))
            (periodTransport g (parameterMap A.periods p.1) p.2)) : ℝ)) :
        UnitAddCircle) = _
      rw [hparam p.1, periodCoordinates_transport, gammaReal_rhoLambdaReal]
      rfl

/-- The twelvefold character restricted to the regular-base family. -/
public noncomputable def regularPartTwelveGamma :
    C(RegularTotalSpace A.periods, UnitAddCircle) :=
  A.regularTwelveGamma.comp
    ⟨regularFamilyInclusion A.periods,
      regularFamilyInclusion_continuous A.periods⟩

public theorem regularPartTwelveGamma_regularFamilyDeckMap
    (g : Delta) (q : RegularTotalSpace A.periods) :
    A.regularPartTwelveGamma (regularFamilyDeckMap A.periods g q) =
      A.regularPartTwelveGamma q := by
  change A.regularTwelveGamma
      (regularFamilyInclusion A.periods (regularFamilyDeckMap A.periods g q)) = _
  rw [regularFamilyInclusion_regularFamilyDeckMap]
  exact A.regularTwelveGamma_familyDeckEquiv g _

/-- The twelvefold character descends to the actual central-family quotient. -/
public noncomputable def centralFamilyTwelveGamma :
    C(A.CentralFamily, UnitAddCircle) := by
  let _ := regularFamilyDeckAction A.periods
  refine
    { toFun := Quotient.lift A.regularPartTwelveGamma ?_
      continuous_toFun := ?_ }
  · intro p q h
    change MulAction.orbitRel Delta (RegularTotalSpace A.periods) p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, rfl⟩ := h
    exact A.regularPartTwelveGamma_regularFamilyDeckMap g q
  · apply continuous_quot_lift
      (fun p q h ↦ by
        change MulAction.orbitRel Delta (RegularTotalSpace A.periods) p q at h
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
        obtain ⟨g, rfl⟩ := h
        exact A.regularPartTwelveGamma_regularFamilyDeckMap g q)
    exact A.regularPartTwelveGamma.continuous

@[simp]
public theorem centralFamilyTwelveGamma_centralQuotientProjection
    (q : RegularTotalSpace A.periods) :
    A.centralFamilyTwelveGamma (A.centralQuotientProjection q) =
      A.regularPartTwelveGamma q :=
  rfl

/-- The `(-4, 3)` orbifold phase correction pulled back from the twice-punctured affine base. -/
public noncomputable def centralFamilyOrbifoldBasePhase :
    C(A.CentralFamily, UnitAddCircle) :=
  SphereSixComplex.Topology.ellipticOrbifoldBasePhase.comp
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩

/-- The central character corrected by the two elliptic orbifold base phases. -/
public noncomputable def centralFamilyCorrectedTwelveGamma :
    C(A.CentralFamily, UnitAddCircle) where
  toFun q := A.centralFamilyTwelveGamma q + A.centralFamilyOrbifoldBasePhase q
  continuous_toFun := A.centralFamilyTwelveGamma.continuous.add
    A.centralFamilyOrbifoldBasePhase.continuous

@[simp]
public theorem centralFamilyCorrectedTwelveGamma_apply (q : A.CentralFamily) :
    A.centralFamilyCorrectedTwelveGamma q =
      A.centralFamilyTwelveGamma q +
        SphereSixComplex.Topology.ellipticOrbifoldBasePhase
          (A.centralFamilyCoordinate q) :=
  rfl

/-- The central affine coordinate on an additive cusp-cover representative is the literal
regular coordinate of its lifted cusp parameter. -/
public theorem centralFamilyCoordinate_puncturedLocalCusp_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralFamilyCoordinate
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      A.regularCoordinate (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1 := by
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change A.centralFamilyCoordinate
      (A.centralQuotientProjection
        (projection (regularParameterMap A.periods)
          (additiveCuspBundleHomeomorph A.starCuspWitness p).1)) = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  rfl

/-- The exponential cusp parameter, bundled as a nonzero complex number. -/
public def additiveCuspQPhasePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    SphereSixComplex.Topology.PuncturedComplex :=
  (Subtype.mk (CuspPeriodExpansion.cuspQ p.1.2) (Complex.exp_ne_zero _) :
    {z : ℂ // z ≠ 0})

/-- The nonvanishing unit in the reciprocal cusp factorization. -/
public def additiveCuspFactorizationUnitPhasePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    SphereSixComplex.Topology.PuncturedComplex :=
  (Subtype.mk
    (A.actualNormalizedModularJUniformization.cusp.cuspUnit
      (CuspPeriodExpansion.cuspQ p.1.2))
    (A.actualPuncturedCuspWitness_cuspUnit_ne
      (CuspPeriodExpansion.cuspQ p.1.2) p.2) : {z : ℂ // z ≠ 0})

@[simp]
public theorem puncturedComplexPhase_additiveCuspQPhasePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    SphereSixComplex.Topology.puncturedComplexPhase
        (A.additiveCuspQPhasePoint p) =
      ((p.1.2.re : ℝ) : UnitAddCircle) := by
  exact SphereSixComplex.Topology.puncturedComplexPhase_cuspQ p.1.2

/-- Radially contract the completed cusp parameter while retaining the additive-cover point. -/
public def additiveCuspRadialQ
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) : ℂ :=
  (((1 - (u.1 : ℝ) : ℝ) : ℂ) * CuspPeriodExpansion.cuspQ u.2.1.2)

public theorem additiveCuspRadialQ_norm_lt
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    ‖A.additiveCuspRadialQ u‖ < A.starCuspWitness.localWitness.radius := by
  have ht0 : 0 ≤ 1 - (u.1 : ℝ) := sub_nonneg.mpr u.1.property.2
  have ht1 : 1 - (u.1 : ℝ) ≤ 1 := sub_le_self 1 u.1.property.1
  rw [additiveCuspRadialQ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt u.2.2

public theorem additiveCuspRadialQ_continuous :
    Continuous A.additiveCuspRadialQ := by
  unfold additiveCuspRadialQ CuspPeriodExpansion.cuspQ
  fun_prop

/-- The factorization unit evaluated along the radial contraction. -/
public def additiveCuspRadialFactorizationUnit
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) : ℂ :=
  A.actualNormalizedModularJUniformization.cusp.cuspUnit
    (A.additiveCuspRadialQ u)

public theorem additiveCuspRadialFactorizationUnit_ne_zero
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.additiveCuspRadialFactorizationUnit u ≠ 0 :=
  A.actualPuncturedCuspWitness_cuspUnit_ne _ (A.additiveCuspRadialQ_norm_lt u)

public theorem additiveCuspRadialFactorizationUnit_continuous :
    Continuous A.additiveCuspRadialFactorizationUnit := by
  apply A.actualCuspFactorizationUnit_continuousOn.comp_continuous
    A.additiveCuspRadialQ_continuous
  intro u
  rw [actualCuspParameterBall, Metric.mem_ball, dist_zero_right]
  exact A.additiveCuspRadialQ_norm_lt u

/-- The unit-phase summand on the additive cusp cover. -/
public def additiveCuspFactorizationUnitPhaseMap :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      UnitAddCircle) :=
  SphereSixComplex.Topology.puncturedComplexPhase.comp
    ⟨A.additiveCuspFactorizationUnitPhasePoint, by
      apply Continuous.subtype_mk
      have hunit := A.actualCuspFactorizationUnit_continuousOn.comp_continuous
        (show Continuous (fun p : additiveCuspRadiusCover
            A.starCuspWitness.localWitness.radius ↦
              CuspPeriodExpansion.cuspQ p.1.2) by
          unfold CuspPeriodExpansion.cuspQ
          fun_prop)
        (fun p ↦ by
          rw [actualCuspParameterBall, Metric.mem_ball, dist_zero_right]
          exact p.2)
      change Continuous (A.actualCuspFactorizationUnit ∘
        fun p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius ↦
          CuspPeriodExpansion.cuspQ p.1.2)
      exact hunit⟩

/-- Radial contraction nullhomotopes the factorization-unit phase to its value at the center. -/
public noncomputable def additiveCuspFactorizationUnitPhaseRadialHomotopy :
    ContinuousMap.Homotopy A.additiveCuspFactorizationUnitPhaseMap
      (ContinuousMap.const _
        (SphereSixComplex.Topology.puncturedComplexPhase
          (Subtype.mk
            (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
              A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
                SphereSixComplex.Topology.PuncturedComplex))) where
  toFun u := SphereSixComplex.Topology.puncturedComplexPhase
    (Subtype.mk (A.additiveCuspRadialFactorizationUnit u)
      (A.additiveCuspRadialFactorizationUnit_ne_zero u) :
        SphereSixComplex.Topology.PuncturedComplex)
  continuous_toFun := SphereSixComplex.Topology.puncturedComplexPhase.continuous.comp
    (Continuous.subtype_mk A.additiveCuspRadialFactorizationUnit_continuous _)
  map_zero_left p := by
    have hpoint :
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (0, p))
          (A.additiveCuspRadialFactorizationUnit_ne_zero (0, p)) :
          SphereSixComplex.Topology.PuncturedComplex) =
          A.additiveCuspFactorizationUnitPhasePoint p := by
      apply Subtype.ext
      simp [additiveCuspRadialFactorizationUnit, additiveCuspRadialQ,
        additiveCuspFactorizationUnitPhasePoint]
    change SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (0, p))
          (A.additiveCuspRadialFactorizationUnit_ne_zero (0, p)) :
            SphereSixComplex.Topology.PuncturedComplex) =
      SphereSixComplex.Topology.puncturedComplexPhase
        (A.additiveCuspFactorizationUnitPhasePoint p)
    exact congrArg SphereSixComplex.Topology.puncturedComplexPhase hpoint
  map_one_left p := by
    have hpoint :
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (1, p))
          (A.additiveCuspRadialFactorizationUnit_ne_zero (1, p)) :
          SphereSixComplex.Topology.PuncturedComplex) =
        (Subtype.mk
          (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
          A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
            SphereSixComplex.Topology.PuncturedComplex) := by
      apply Subtype.ext
      simp [additiveCuspRadialFactorizationUnit, additiveCuspRadialQ]
    change SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (1, p))
          (A.additiveCuspRadialFactorizationUnit_ne_zero (1, p)) :
            SphereSixComplex.Topology.PuncturedComplex) =
      SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk
          (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
          A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
            SphereSixComplex.Topology.PuncturedComplex)
    exact congrArg SphereSixComplex.Topology.puncturedComplexPhase hpoint

/-- The second unit in the exterior normal form, extended across the completed cusp disc. -/
public def additiveCuspRadialExteriorUnit
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) : ℂ :=
  1 - A.additiveCuspRadialQ u * A.additiveCuspRadialFactorizationUnit u

public theorem additiveCuspRadialExteriorUnit_ne_zero
    (u : unitInterval ×
      additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.additiveCuspRadialExteriorUnit u ≠ 0 := by
  have hnorm := A.actualPuncturedCuspWitness_cuspProduct_norm_lt_half
    (A.additiveCuspRadialQ u) (A.additiveCuspRadialQ_norm_lt u)
  change ‖A.additiveCuspRadialQ u *
    A.additiveCuspRadialFactorizationUnit u‖ < 1 / 2 at hnorm
  intro hzero
  have hone : A.additiveCuspRadialQ u *
      A.additiveCuspRadialFactorizationUnit u = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  rw [hone] at hnorm
  norm_num at hnorm

public theorem additiveCuspRadialExteriorUnit_continuous :
    Continuous A.additiveCuspRadialExteriorUnit := by
  unfold additiveCuspRadialExteriorUnit
  exact continuous_const.sub
    (A.additiveCuspRadialQ_continuous.mul
      A.additiveCuspRadialFactorizationUnit_continuous)

/-- The exterior-unit phase on the additive cusp cover. -/
public def additiveCuspExteriorUnitPhaseMap :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      UnitAddCircle) :=
  SphereSixComplex.Topology.puncturedComplexPhase.comp
    ⟨fun p ↦ Subtype.mk (A.additiveCuspRadialExteriorUnit (0, p))
        (A.additiveCuspRadialExteriorUnit_ne_zero (0, p)),
      Continuous.subtype_mk
        (A.additiveCuspRadialExteriorUnit_continuous.comp
          (continuous_const.prodMk continuous_id)) _⟩

/-- Radial contraction nullhomotopes the exterior-unit phase to the zero circle element. -/
public noncomputable def additiveCuspExteriorUnitPhaseRadialHomotopy :
    ContinuousMap.Homotopy A.additiveCuspExteriorUnitPhaseMap
      (ContinuousMap.const _ (0 : UnitAddCircle)) where
  toFun u := SphereSixComplex.Topology.puncturedComplexPhase
    (Subtype.mk (A.additiveCuspRadialExteriorUnit u)
      (A.additiveCuspRadialExteriorUnit_ne_zero u) :
        SphereSixComplex.Topology.PuncturedComplex)
  continuous_toFun := SphereSixComplex.Topology.puncturedComplexPhase.continuous.comp
    (Continuous.subtype_mk A.additiveCuspRadialExteriorUnit_continuous _)
  map_zero_left p := rfl
  map_one_left p := by
    change SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialExteriorUnit (1, p))
          (A.additiveCuspRadialExteriorUnit_ne_zero (1, p)) :
            SphereSixComplex.Topology.PuncturedComplex) = 0
    rw [show (Subtype.mk (A.additiveCuspRadialExteriorUnit (1, p))
        (A.additiveCuspRadialExteriorUnit_ne_zero (1, p)) :
          SphereSixComplex.Topology.PuncturedComplex) =
        (Subtype.mk 1 one_ne_zero : SphereSixComplex.Topology.PuncturedComplex) by
      apply Subtype.ext
      simp [additiveCuspRadialExteriorUnit, additiveCuspRadialQ]]
    rw [SphereSixComplex.Topology.puncturedComplexPhase_apply]
    norm_num

/-- The reciprocal central coordinate is exactly the cusp parameter times its holomorphic
unit on every additive-cover representative. -/
public theorem regularCoordinate_additiveCusp_reciprocal_factorization
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    (A.regularCoordinate
      (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1).1⁻¹ =
      (A.additiveCuspQPhasePoint p).1 *
        (A.additiveCuspFactorizationUnitPhasePoint p).1 := by
  change (A.modular.sourceCoordinate.coordinate
      (A.cuspCoordinate.lift p.1.2))⁻¹ =
    CuspPeriodExpansion.cuspQ p.1.2 *
      A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (CuspPeriodExpansion.cuspQ p.1.2)
  exact A.actualPuncturedCuspWitness_reciprocal_factorization p.1.2
    (additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le p) p.2

/-- The extended exterior unit is exactly `1 - z⁻¹` on the original cusp collar. -/
public theorem additiveCuspExteriorUnitPhaseMap_eq_infinityUnit
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.additiveCuspExteriorUnitPhaseMap p =
      SphereSixComplex.Topology.puncturedComplexPhase
        (SphereSixComplex.Topology.twicePuncturedInfinityUnit
            (A.regularCoordinate
              (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)) := by
  change SphereSixComplex.Topology.puncturedComplexPhase
      (Subtype.mk (A.additiveCuspRadialExteriorUnit (0, p))
        (A.additiveCuspRadialExteriorUnit_ne_zero (0, p)) :
          SphereSixComplex.Topology.PuncturedComplex) = _
  congr 1
  apply Subtype.ext
  change A.additiveCuspRadialExteriorUnit (0, p) =
    1 - (A.regularCoordinate
      (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1).1⁻¹
  rw [A.regularCoordinate_additiveCusp_reciprocal_factorization]
  simp [additiveCuspRadialExteriorUnit, additiveCuspRadialQ,
    additiveCuspRadialFactorizationUnit, additiveCuspQPhasePoint,
    additiveCuspFactorizationUnitPhasePoint]

/-- Consequently the finite-plane phase of the central coordinate is minus the phase of the
cusp parameter and minus the phase of the nonvanishing factorization unit. -/
public theorem twicePuncturedZeroPhase_regularCoordinate_additiveCusp
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    SphereSixComplex.Topology.twicePuncturedZeroPhase
        (A.regularCoordinate
          (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1) =
      -(SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspQPhasePoint p) +
        SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspFactorizationUnitPhasePoint p)) := by
  let z := SphereSixComplex.Topology.twicePuncturedToZeroPunctured
    (A.regularCoordinate
      (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)
  have hrecip : (Subtype.mk z.1⁻¹ (inv_ne_zero z.2) :
        SphereSixComplex.Topology.PuncturedComplex) =
      (Subtype.mk
        ((A.additiveCuspQPhasePoint p).1 *
          (A.additiveCuspFactorizationUnitPhasePoint p).1)
        (mul_ne_zero (A.additiveCuspQPhasePoint p).2
          (A.additiveCuspFactorizationUnitPhasePoint p).2) :
            SphereSixComplex.Topology.PuncturedComplex) := by
    apply Subtype.ext
    exact A.regularCoordinate_additiveCusp_reciprocal_factorization p
  have hinv := SphereSixComplex.Topology.puncturedComplexPhase_inv z
  rw [hrecip, SphereSixComplex.Topology.puncturedComplexPhase_mul] at hinv
  change SphereSixComplex.Topology.puncturedComplexPhase z = _
  rw [← neg_inj, neg_neg]
  exact hinv.symm

/-- The exact exterior normal form of the orbifold correction on the normalized cusp cover. -/
public theorem centralFamilyOrbifoldBasePhase_puncturedLocalCusp_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralFamilyOrbifoldBasePhase
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      -SphereSixComplex.Topology.twicePuncturedZeroPhase
          (A.regularCoordinate
            (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1) +
        (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
          (SphereSixComplex.Topology.twicePuncturedInfinityUnit
            (A.regularCoordinate
              (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)) := by
  change SphereSixComplex.Topology.ellipticOrbifoldBasePhase
      (A.centralFamilyCoordinate
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p))) = _
  rw [A.centralFamilyCoordinate_puncturedLocalCusp_additivePoint]
  exact SphereSixComplex.Topology.ellipticOrbifoldBasePhase_infinity_normalForm _

/-- The pulled-back correction contains exactly one copy of the exponential cusp phase.  Its
other two summands are phases of nonvanishing factors on the completed cusp disc. -/
public theorem centralFamilyOrbifoldBasePhase_additiveCusp_parameter_normalForm
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralFamilyOrbifoldBasePhase
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspQPhasePoint p) +
        SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspFactorizationUnitPhasePoint p) +
        (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
          (SphereSixComplex.Topology.twicePuncturedInfinityUnit
            (A.regularCoordinate
              (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)) := by
  rw [A.centralFamilyOrbifoldBasePhase_puncturedLocalCusp_additivePoint]
  rw [A.twicePuncturedZeroPhase_regularCoordinate_additiveCusp]
  module

/-- In particular, the distinguished cusp summand is literally the angular additive-cover
coordinate, not merely a class with the same winding. -/
public theorem centralFamilyOrbifoldBasePhase_additiveCusp_angular_normalForm
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralFamilyOrbifoldBasePhase
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      ((p.1.2.re : ℝ) : UnitAddCircle) +
        SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspFactorizationUnitPhasePoint p) +
        (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
          (SphereSixComplex.Topology.twicePuncturedInfinityUnit
            (A.regularCoordinate
              (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)) := by
  rw [A.centralFamilyOrbifoldBasePhase_additiveCusp_parameter_normalForm]
  rw [A.puncturedComplexPhase_additiveCuspQPhasePoint]

/-- On the normalized additive cusp cover, the central twelvefold character is exactly the
twelvefold first coordinate after transport to the marked cusp fibre. -/
public theorem centralFamilyTwelveGamma_puncturedLocalCusp_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralFamilyTwelveGamma
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      cuspFiberTwelveFirstCoordinate
        (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness))
        (additiveTorusProjection
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1
          (collarFiberEquiv A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness) p.1.2 p.1.1)) := by
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change (((12 * gammaCoordinate (cuspBasePoint A.cuspCoordinate p.1.2) p.1.1 : ℝ)) :
      UnitAddCircle) = _
  rw [cuspFiberTwelveFirstCoordinate_projection]
  rw [collarFiberEquiv_apply]
  change (((12 * gammaCoordinate (cuspBasePoint A.cuspCoordinate p.1.2) p.1.1 : ℝ)) :
      UnitAddCircle) =
    (12 : ℤ) • (((((fullRankDomain
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))).realEquiv.symm
          ((fullRankDomain
            (cuspBasePoint A.cuspCoordinate
              (markedCuspParameter A.starCuspWitness))).realEquiv
                (periodCoordinates
                  (cuspBasePoint A.cuspCoordinate p.1.2) p.1.1))) 0 : ℝ)) :
                    UnitAddCircle)
  rw [(fullRankDomain
    (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness))).realEquiv.symm_apply_apply]
  change (((12 * gammaReal
      (periodCoordinates (cuspBasePoint A.cuspCoordinate p.1.2) p.1.1) : ℝ)) :
        UnitAddCircle) =
    (12 : ℤ) • (((periodCoordinates
      (cuspBasePoint A.cuspCoordinate p.1.2) p.1.1 0 : ℝ)) : UnitAddCircle)
  rw [gammaReal_eq_head]
  apply (StandardTorusHomology.unitAddCircle_eq_iff _ _).2
  refine ⟨0, ?_⟩
  norm_num

/-- The source meridian character differs from the pullback of the central twelvefold character
by precisely the angular additive-cover coordinate. -/
public theorem actualCuspMeridianSourceCircleMap_additivePoint_eq_angular_add_central
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    A.actualCuspMeridianSourceCircleMap
        (G.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      ((p.1.2.re : ℝ) : UnitAddCircle) +
        A.centralFamilyTwelveGamma
          (puncturedLocalCuspQuotientMap A.starCuspWitness
            (additiveCuspBoundaryProjection A.starCuspWitness p)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
      (G.totalHomotopyEquiv.toFun
        (additiveCuspBoundaryProjection A.starCuspWitness p)) = _
  rw [show additiveCuspBoundaryProjection A.starCuspWitness p =
      collarPeriodPointMap A.starCuspWitness p by rfl]
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
        (markedCuspParameter A.starCuspWitness)
        (collarPeriodPointMap A.starCuspWitness p)).2) = _
  rw [puncturedLocalCuspQuotientHomeomorph_apply]
  change cuspMeridianSourceCircleMap
      (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness))
      (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph
        (cuspFiberClutching
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)))
        (Quotient.mk _
          (p.1.2.re,
            additiveTorusProjection
              (cuspBasePoint A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness)).1
              (collarFiberEquiv A.cuspCoordinate
                (markedCuspParameter A.starCuspWitness) p.1.2 p.1.1)))) = _
  rw [cuspMeridianSourceCircleMap_realMappingTorus_mk]
  change ((p.1.2.re : ℝ) : UnitAddCircle) +
      cuspFiberTwelveFirstCoordinate
        (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness))
        (additiveTorusProjection
          (cuspBasePoint A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness)).1
          (collarFiberEquiv A.cuspCoordinate
            (markedCuspParameter A.starCuspWitness) p.1.2 p.1.1)) =
    ((p.1.2.re : ℝ) : UnitAddCircle) +
      A.centralFamilyTwelveGamma
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness p))
  rw [centralFamilyTwelveGamma_puncturedLocalCusp_additivePoint]

/-- Replacing the central character by its globally corrected version isolates the entire cusp
contribution in the angular term minus the pulled-back orbifold base phase. -/
public theorem actualCuspMeridianSourceCircleMap_additivePoint_eq_correctedCentral
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    A.actualCuspMeridianSourceCircleMap
        (G.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      ((p.1.2.re : ℝ) : UnitAddCircle) +
        A.centralFamilyCorrectedTwelveGamma
          (puncturedLocalCuspQuotientMap A.starCuspWitness
            (additiveCuspBoundaryProjection A.starCuspWitness p)) -
        A.centralFamilyOrbifoldBasePhase
          (puncturedLocalCuspQuotientMap A.starCuspWitness
            (additiveCuspBoundaryProjection A.starCuspWitness p)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  dsimp only
  rw [A.actualCuspMeridianSourceCircleMap_additivePoint_eq_angular_add_central]
  rw [A.centralFamilyCorrectedTwelveGamma_apply]
  change _ = _ + (_ + A.centralFamilyOrbifoldBasePhase _) -
    A.centralFamilyOrbifoldBasePhase _
  module

/-- The cusp angular term cancels pointwise against the `+1` exterior summand of the global
orbifold correction.  What remains consists only of the two explicit nonvanishing-unit phases. -/
public theorem actualCuspMeridianSourceCircleMap_additivePoint_eq_correctedCentral_sub_units
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    A.actualCuspMeridianSourceCircleMap
        (G.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p)) =
      A.centralFamilyCorrectedTwelveGamma
          (puncturedLocalCuspQuotientMap A.starCuspWitness
            (additiveCuspBoundaryProjection A.starCuspWitness p)) -
        SphereSixComplex.Topology.puncturedComplexPhase
          (A.additiveCuspFactorizationUnitPhasePoint p) -
        (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
          (SphereSixComplex.Topology.twicePuncturedInfinityUnit
            (A.regularCoordinate
              (additiveCuspBundleHomeomorph A.starCuspWitness p).1.1)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  dsimp only
  rw [A.actualCuspMeridianSourceCircleMap_additivePoint_eq_correctedCentral]
  rw [A.centralFamilyOrbifoldBasePhase_additiveCusp_angular_normalForm]
  module

/-- The source cusp character pulled back to the normalized additive cover. -/
public noncomputable def additiveCuspTransportedSourceCircleMap :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact A.actualCuspMeridianSourceCircleMap.comp
    (G.totalHomotopyEquiv.toFun.comp
      (additiveCuspBoundaryProjection A.starCuspWitness))

/-- The corrected central character pulled back through the actual cusp overlap. -/
public noncomputable def additiveCuspCorrectedCentralCircleMap :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      UnitAddCircle) :=
  A.centralFamilyCorrectedTwelveGamma.comp
    ⟨fun p ↦ puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness p),
      (puncturedLocalCuspQuotientMap_continuous A.starCuspWitness).comp
        (additiveCuspBoundaryProjection A.starCuspWitness).continuous⟩

/-- The endpoint left after radially contracting the two holomorphic-unit phases. -/
public noncomputable def additiveCuspCorrectedCentralMinusCenterUnitMap :
    C(additiveCuspRadiusCover A.starCuspWitness.localWitness.radius,
      UnitAddCircle) where
  toFun p := A.additiveCuspCorrectedCentralCircleMap p -
    SphereSixComplex.Topology.puncturedComplexPhase
      (Subtype.mk
        (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
        A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
          SphereSixComplex.Topology.PuncturedComplex)
  continuous_toFun := A.additiveCuspCorrectedCentralCircleMap.continuous.sub
    continuous_const

/-- Simultaneously contracting the two nonvanishing factors deforms the transported source
character to the corrected central character up to one constant circle translation. -/
public noncomputable def additiveCuspSourceToCorrectedMinusCenterUnitHomotopy :
    ContinuousMap.Homotopy A.additiveCuspTransportedSourceCircleMap
      A.additiveCuspCorrectedCentralMinusCenterUnitMap where
  toFun u := A.additiveCuspCorrectedCentralCircleMap u.2 -
    A.additiveCuspFactorizationUnitPhaseRadialHomotopy u -
      (3 : ℤ) • A.additiveCuspExteriorUnitPhaseRadialHomotopy u
  continuous_toFun := by
    fun_prop
  map_zero_left p := by
    change A.additiveCuspCorrectedCentralCircleMap p -
        A.additiveCuspFactorizationUnitPhaseRadialHomotopy (0, p) -
          (3 : ℤ) • A.additiveCuspExteriorUnitPhaseRadialHomotopy (0, p) =
      A.actualCuspMeridianSourceCircleMap
        (A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun
          (additiveCuspBoundaryProjection A.starCuspWitness p))
    rw [A.actualCuspMeridianSourceCircleMap_additivePoint_eq_correctedCentral_sub_units]
    rw [← A.additiveCuspExteriorUnitPhaseMap_eq_infinityUnit]
    rw [show A.additiveCuspFactorizationUnitPhaseRadialHomotopy (0, p) =
        A.additiveCuspFactorizationUnitPhaseMap p from
      A.additiveCuspFactorizationUnitPhaseRadialHomotopy.map_zero_left p]
    rw [show A.additiveCuspExteriorUnitPhaseRadialHomotopy (0, p) =
        A.additiveCuspExteriorUnitPhaseMap p from
      A.additiveCuspExteriorUnitPhaseRadialHomotopy.map_zero_left p]
    rfl
  map_one_left p := by
    change A.additiveCuspCorrectedCentralCircleMap p -
        A.additiveCuspFactorizationUnitPhaseRadialHomotopy (1, p) -
          (3 : ℤ) • A.additiveCuspExteriorUnitPhaseRadialHomotopy (1, p) =
      A.additiveCuspCorrectedCentralCircleMap p -
        SphereSixComplex.Topology.puncturedComplexPhase
          (Subtype.mk
            (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
            A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
              SphereSixComplex.Topology.PuncturedComplex)
    rw [show A.additiveCuspFactorizationUnitPhaseRadialHomotopy (1, p) =
        SphereSixComplex.Topology.puncturedComplexPhase
          (Subtype.mk
            (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
            A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
              SphereSixComplex.Topology.PuncturedComplex) from
      A.additiveCuspFactorizationUnitPhaseRadialHomotopy.map_one_left p]
    rw [show A.additiveCuspExteriorUnitPhaseRadialHomotopy (1, p) = 0 from
      A.additiveCuspExteriorUnitPhaseRadialHomotopy.map_one_left p]
    module

/-- A constant translation in the circle does not affect the homotopy class of the corrected
central character. -/
public noncomputable def additiveCuspRemoveCenterUnitTranslationHomotopy :
    ContinuousMap.Homotopy A.additiveCuspCorrectedCentralMinusCenterUnitMap
      A.additiveCuspCorrectedCentralCircleMap where
  toFun u := A.additiveCuspCorrectedCentralCircleMap u.2 +
    PathConnectedSpace.somePath
      (-SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk
          (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
          A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
            SphereSixComplex.Topology.PuncturedComplex)) 0 u.1
  continuous_toFun := A.additiveCuspCorrectedCentralCircleMap.continuous.comp
      continuous_snd |>.add
    ((PathConnectedSpace.somePath
      (-SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk
          (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
          A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
            SphereSixComplex.Topology.PuncturedComplex)) 0).continuous.comp continuous_fst)
  map_zero_left p := by
    simp [additiveCuspCorrectedCentralMinusCenterUnitMap, sub_eq_add_neg]
  map_one_left p := by simp

/-- On the normalized additive cusp cover, the transported meridian character and the global
`(-4,3)`-corrected central character are homotopic. -/
public noncomputable def additiveCuspTransportedSourceHomotopyCorrectedCentral :
    ContinuousMap.Homotopy A.additiveCuspTransportedSourceCircleMap
      A.additiveCuspCorrectedCentralCircleMap :=
  A.additiveCuspSourceToCorrectedMinusCenterUnitHomotopy.trans
    A.additiveCuspRemoveCenterUnitTranslationHomotopy

/-- The transported source character on the actual punctured cusp quotient. -/
public noncomputable def puncturedCuspTransportedSourceCircleMap :
    C(puncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact A.actualCuspMeridianSourceCircleMap.comp G.totalHomotopyEquiv.toFun

/-- The global corrected central character restricted to the actual punctured cusp quotient. -/
public noncomputable def puncturedCuspCorrectedCentralCircleMap :
    C(puncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) :=
  A.centralFamilyCorrectedTwelveGamma.comp
    ⟨puncturedLocalCuspQuotientMap A.starCuspWitness,
      puncturedLocalCuspQuotientMap_continuous A.starCuspWitness⟩

/-- The constant-translated corrected central character on the punctured cusp quotient. -/
public noncomputable def puncturedCuspCorrectedCentralMinusCenterUnitMap :
    C(puncturedLocalCuspQuotient A.starCuspWitness, UnitAddCircle) where
  toFun q := A.puncturedCuspCorrectedCentralCircleMap q -
    SphereSixComplex.Topology.puncturedComplexPhase
      (Subtype.mk
        (A.actualNormalizedModularJUniformization.cusp.cuspUnit 0)
        A.actualNormalizedModularJUniformization.cusp.cuspUnit_zero_ne :
          SphereSixComplex.Topology.PuncturedComplex)
  continuous_toFun := A.puncturedCuspCorrectedCentralCircleMap.continuous.sub
    continuous_const

public noncomputable def descendHomotopyAlongQuotient
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace unitInterval]
    (q : C(X, Y)) (hq : IsQuotientMap q) (f g : C(Y, Z))
    (H : ContinuousMap.Homotopy (f.comp q) (g.comp q))
    (hH : ∀ t x x', q x = q x' → H (t, x) = H (t, x')) :
    ContinuousMap.Homotopy f g where
  toFun u := H (u.1, Function.surjInv hq.surjective u.2)
  continuous_toFun := by
    apply hq.continuous_lift_prod_right
    convert H.continuous using 1
    funext u
    apply hH
    exact Function.rightInverse_surjInv hq.surjective (q u.2)
  map_zero_left y := by
    change H (0, Function.surjInv hq.surjective y) = f y
    calc
      _ = (f.comp q) (Function.surjInv hq.surjective y) :=
        H.map_zero_left (Function.surjInv hq.surjective y)
      _ = f y := by
        change f (q (Function.surjInv hq.surjective y)) = f y
        rw [Function.surjInv_eq hq.surjective y]
  map_one_left y := by
    change H (1, Function.surjInv hq.surjective y) = g y
    calc
      _ = (g.comp q) (Function.surjInv hq.surjective y) :=
        H.map_one_left (Function.surjInv hq.surjective y)
      _ = g y := by
        change g (q (Function.surjInv hq.surjective y)) = g y
        rw [Function.surjInv_eq hq.surjective y]

/-- Radial contraction of the exponential parameter is constant on every fibre of the actual
cusp boundary quotient. -/
public theorem additiveCuspRadialQ_eq_of_boundaryProjection_eq
    (t : unitInterval)
    (a b : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
    (h : additiveCuspBoundaryProjection A.starCuspWitness a =
      additiveCuspBoundaryProjection A.starCuspWitness b) :
    A.additiveCuspRadialQ (t, a) = A.additiveCuspRadialQ (t, b) := by
  obtain ⟨k, hk, -⟩ := additiveCuspBoundaryProjection_eq_period_data
    A.starCuspWitness a b h
  unfold additiveCuspRadialQ
  rw [hk]
  congr 1
  rw [show b.1.2 - (k : ℂ) = b.1.2 + (-k : ℤ) by
    push_cast
    ring]
  exact cuspQ_add_int b.1.2 (-k)

@[simp]
public theorem puncturedCuspTransportedSourceCircleMap_boundaryProjection
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.puncturedCuspTransportedSourceCircleMap
        (additiveCuspBoundaryProjection A.starCuspWitness p) =
      A.additiveCuspTransportedSourceCircleMap p :=
  rfl

@[simp]
public theorem puncturedCuspCorrectedCentralCircleMap_boundaryProjection
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.puncturedCuspCorrectedCentralCircleMap
        (additiveCuspBoundaryProjection A.starCuspWitness p) =
      A.additiveCuspCorrectedCentralCircleMap p :=
  rfl

@[simp]
public theorem puncturedCuspCorrectedCentralMinusCenterUnitMap_boundaryProjection
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.puncturedCuspCorrectedCentralMinusCenterUnitMap
        (additiveCuspBoundaryProjection A.starCuspWitness p) =
      A.additiveCuspCorrectedCentralMinusCenterUnitMap p :=
  rfl

public theorem additiveCuspSourceToCorrectedMinusCenterUnitHomotopy_fiberwise
    (t : unitInterval)
    (a b : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
    (h : additiveCuspBoundaryProjection A.starCuspWitness a =
      additiveCuspBoundaryProjection A.starCuspWitness b) :
    A.additiveCuspSourceToCorrectedMinusCenterUnitHomotopy (t, a) =
      A.additiveCuspSourceToCorrectedMinusCenterUnitHomotopy (t, b) := by
  have hcentral : A.additiveCuspCorrectedCentralCircleMap a =
      A.additiveCuspCorrectedCentralCircleMap b := by
    change A.centralFamilyCorrectedTwelveGamma
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness a)) =
      A.centralFamilyCorrectedTwelveGamma
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspBoundaryProjection A.starCuspWitness b))
    rw [h]
  have hradial := A.additiveCuspRadialQ_eq_of_boundaryProjection_eq t a b h
  change A.additiveCuspCorrectedCentralCircleMap a -
      SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (t, a)) _) -
      (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialExteriorUnit (t, a)) _) =
    A.additiveCuspCorrectedCentralCircleMap b -
      SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialFactorizationUnit (t, b)) _) -
      (3 : ℤ) • SphereSixComplex.Topology.puncturedComplexPhase
        (Subtype.mk (A.additiveCuspRadialExteriorUnit (t, b)) _)
  rw [hcentral]
  congr 2
  · congr 2
    simpa [additiveCuspRadialFactorizationUnit] using congrArg
      A.actualNormalizedModularJUniformization.cusp.cuspUnit hradial
  · congr 2
    simp only [additiveCuspRadialExteriorUnit]
    rw [hradial]
    congr 2
    simpa [additiveCuspRadialFactorizationUnit] using congrArg
      A.actualNormalizedModularJUniformization.cusp.cuspUnit hradial

public theorem additiveCuspRemoveCenterUnitTranslationHomotopy_fiberwise
    (t : unitInterval)
    (a b : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius)
    (h : additiveCuspBoundaryProjection A.starCuspWitness a =
      additiveCuspBoundaryProjection A.starCuspWitness b) :
    A.additiveCuspRemoveCenterUnitTranslationHomotopy (t, a) =
      A.additiveCuspRemoveCenterUnitTranslationHomotopy (t, b) := by
  change A.additiveCuspCorrectedCentralCircleMap a + _ =
    A.additiveCuspCorrectedCentralCircleMap b + _
  congr 1
  change A.centralFamilyCorrectedTwelveGamma
      (puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness a)) =
    A.centralFamilyCorrectedTwelveGamma
      (puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness b))
  rw [h]

/-- The radial unit-phase homotopy descends from normalized logarithmic coordinates to the
actual punctured cusp quotient. -/
public noncomputable def puncturedCuspSourceToCorrectedMinusCenterUnitHomotopy :
    ContinuousMap.Homotopy A.puncturedCuspTransportedSourceCircleMap
      A.puncturedCuspCorrectedCentralMinusCenterUnitMap :=
  descendHomotopyAlongQuotient
    (additiveCuspBoundaryProjection A.starCuspWitness)
    (additiveCuspBoundaryProjection_isQuotientMap A.starCuspWitness)
    A.puncturedCuspTransportedSourceCircleMap
    A.puncturedCuspCorrectedCentralMinusCenterUnitMap
    A.additiveCuspSourceToCorrectedMinusCenterUnitHomotopy
    A.additiveCuspSourceToCorrectedMinusCenterUnitHomotopy_fiberwise

/-- The homotopy removing the constant center phase also descends to the actual quotient. -/
public noncomputable def puncturedCuspRemoveCenterUnitTranslationHomotopy :
    ContinuousMap.Homotopy A.puncturedCuspCorrectedCentralMinusCenterUnitMap
      A.puncturedCuspCorrectedCentralCircleMap :=
  descendHomotopyAlongQuotient
    (additiveCuspBoundaryProjection A.starCuspWitness)
    (additiveCuspBoundaryProjection_isQuotientMap A.starCuspWitness)
    A.puncturedCuspCorrectedCentralMinusCenterUnitMap
    A.puncturedCuspCorrectedCentralCircleMap
    A.additiveCuspRemoveCenterUnitTranslationHomotopy
    A.additiveCuspRemoveCenterUnitTranslationHomotopy_fiberwise

/-- On the actual punctured cusp quotient, the transported source character is homotopic to
the restriction of the global `(-4,3)`-corrected central character. -/
public noncomputable def puncturedCuspTransportedSourceHomotopyCorrectedCentral :
    ContinuousMap.Homotopy A.puncturedCuspTransportedSourceCircleMap
      A.puncturedCuspCorrectedCentralCircleMap :=
  A.puncturedCuspSourceToCorrectedMinusCenterUnitHomotopy.trans
    A.puncturedCuspRemoveCenterUnitTranslationHomotopy

/-- The corrected central character on the cusp mapping-torus model, obtained through the
actual radial equivalence and cusp inclusion. -/
public noncomputable def cuspMappingTorusCorrectedCentralCircleMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, UnitAddCircle) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact A.puncturedCuspCorrectedCentralCircleMap.comp G.totalHomotopyEquiv.invFun

/-- Inclusion through the actual punctured cusp quotient identifies the source circle character
with the corrected central character on the mapping-torus model up to homotopy. -/
public theorem actualCuspMeridianSourceCircleMap_homotopic_correctedCentral :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    A.actualCuspMeridianSourceCircleMap.Homotopic
      A.cuspMappingTorusCorrectedCentralCircleMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hradial :
      (A.puncturedCuspTransportedSourceCircleMap.comp
          G.totalHomotopyEquiv.invFun).Homotopic
        (A.puncturedCuspCorrectedCentralCircleMap.comp
          G.totalHomotopyEquiv.invFun) :=
    ContinuousMap.Homotopic.comp
      ⟨A.puncturedCuspTransportedSourceHomotopyCorrectedCentral⟩
      (.refl G.totalHomotopyEquiv.invFun)
  have hreturn :
      (A.actualCuspMeridianSourceCircleMap.comp
          (G.totalHomotopyEquiv.toFun.comp
            G.totalHomotopyEquiv.invFun)).Homotopic
        A.actualCuspMeridianSourceCircleMap := by
    simpa using ContinuousMap.Homotopic.comp
      (.refl A.actualCuspMeridianSourceCircleMap)
      G.totalHomotopyEquiv.right_inv
  exact hreturn.symm.trans hradial

/-- The induced first-homology maps of the source character and the inclusion-pulled corrected
central character agree. -/
public theorem actualCuspMeridianSourceCircleMap_homology_eq_correctedCentral :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 A.actualCuspMeridianSourceCircleMap =
      integralSingularHomologyMap 1 A.cuspMappingTorusCorrectedCentralCircleMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply AddMonoidHom.ext
  intro x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom A.actualCuspMeridianSourceCircleMap)) x = _
  rw [integralSingularHomologyMap_eq_of_homotopic
    A.actualCuspMeridianSourceCircleMap_homotopic_correctedCentral 1]
  rfl

/-- The inclusion-pulled corrected central circle character realizes the complete cusp
degree-one coordinate `[12,0,1]`. -/
public theorem cuspMappingTorusCorrectedCentralCircleMap_homologyCoordinate :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    SectionSevenEllipticInteriorMarkedCycleData.actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
        (integralSingularHomologyMap 1 A.cuspMappingTorusCorrectedCentralCircleMap) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [← A.actualCuspMeridianSourceCircleMap_homology_eq_correctedCentral]
  exact A.actualCuspMeridianSourceCircleMap_homologyCoordinate

end SphereSixComplex.Geometry.PaperAnalyticData

end
