module

public import SphereSixComplex.Geometry.AnalyticTorusFamily
public import SphereSixComplex.Geometry.FamilyEquivariance
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The global triangle-group quotient of the analytic torus family

This file constructs the full triangle-group deck action on the varying period quotient.  It
extends the integral monodromy to real period coordinates, transports the complex fibre through
the period bases, and descends that action through the lattice quotient.  The result is the
concrete global family before the three special fibres are filled.
-/

open Matrix

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance

public noncomputable section

/-- Matrix of an integral automorphism in the standard basis of the period lattice. -/
@[expose] public def integralMatrix (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  LinearMap.toMatrix' e.toLinearMap

/-- Real scalar extension of the matrix of an integral period-lattice automorphism. -/
@[expose] public def realMatrix (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (integralMatrix e).map (Int.castRingHom ℝ)

public theorem realMatrix_mul (e f : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    realMatrix (e * f) = realMatrix e * realMatrix f := by
  unfold realMatrix integralMatrix
  rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp]
  congr 2

public theorem integralMatrix_mul_symm (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    integralMatrix e * integralMatrix e.symm = 1 := by
  unfold integralMatrix
  rw [← LinearMap.toMatrix'_comp]
  rw [show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id by ext v; simp]
  exact LinearMap.toMatrix'_one

public theorem realMatrix_mul_symm (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    realMatrix e * realMatrix e.symm = 1 := by
  unfold realMatrix
  rw [← Matrix.map_mul, integralMatrix_mul_symm]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Scalar extension from an integral lattice automorphism to its real coefficient space. -/
@[expose] public noncomputable def realExtension
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) : RealPeriods ≃ₗ[ℝ] RealPeriods :=
  Matrix.toLinearEquiv' (realMatrix e)
    (invertibleOfRightInverse (realMatrix e) (realMatrix e.symm) (realMatrix_mul_symm e))

public theorem realExtension_apply (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (v : RealPeriods) :
    realExtension e v = realMatrix e *ᵥ v := by
  change Matrix.toLin' (realMatrix e) v = _
  rfl

/-- Scalar extension agrees with the original automorphism on integral points. -/
public theorem realExtension_integer (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods)
    (n : IntegerPeriods) :
    realExtension e (integerToReal n) = integerToReal (e n) := by
  rw [realExtension_apply]
  ext i
  change ((integralMatrix e).map (Int.castRingHom ℝ) *ᵥ
    ((Int.castRingHom ℝ) ∘ n)) i = (Int.castRingHom ℝ) (e n i)
  rw [← RingHom.map_mulVec]
  congr 1
  exact congrFun (LinearMap.toMatrix'_mulVec e.toLinearMap n) i

public theorem realMatrix_one :
    realMatrix (1 : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) = 1 := by
  unfold realMatrix integralMatrix
  rw [show (1 : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods).toLinearMap = LinearMap.id by
    ext v
    simp]
  have h : LinearMap.toMatrix'
      (LinearMap.id : IntegerPeriods →ₗ[ℤ] IntegerPeriods) = 1 :=
    LinearMap.toMatrix'_one
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

public theorem realExtension_one :
    realExtension (1 : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [realExtension_apply, realMatrix_one]
  simp

public theorem realExtension_mul (e f : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) :
    realExtension (e * f) = realExtension e * realExtension f := by
  apply LinearEquiv.ext
  intro v
  simp only [realExtension_apply, LinearEquiv.mul_apply]
  rw [realMatrix_mul, Matrix.mulVec_mulVec]

/-- The full triangle-group monodromy on real period coefficients. -/
@[expose] public noncomputable def rhoLambdaReal :
    Delta →* (RealPeriods ≃ₗ[ℝ] RealPeriods) where
  toFun g := realExtension (rhoLambda g)
  map_one' := by rw [map_one, realExtension_one]
  map_mul' g h := by rw [map_mul, realExtension_mul]

public theorem rhoLambdaReal_integer (g : Delta) (n : IntegerPeriods) :
    rhoLambdaReal g (integerToReal n) = integerToReal (rhoLambda g n) :=
  realExtension_integer (rhoLambda g) n

/-- The canonical full-rank real period basis at a point of the period domain. -/
@[expose] public noncomputable def fullRankDomain (x : PeriodDomain) : FullRank x.1 :=
  FullRank.ofSetupInequalities x.1 x.2

/-- Fibre transport obtained by changing to real period coordinates, applying monodromy, and
changing back through the transformed period basis. -/
@[expose] public noncomputable def periodTransport (g : Delta) (x : PeriodDomain) :
    ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace :=
  LinearEquiv.trans (fullRankDomain x).realEquiv.toLinearEquiv.symm
    (LinearEquiv.trans (rhoLambdaReal g)
      (fullRankDomain (rhoParameters g x)).realEquiv.toLinearEquiv)

/-- Fibre transport sends every period to the period prescribed by integral monodromy. -/
public theorem periodTransport_periodVector (g : Delta) (x : PeriodDomain)
    (n : IntegerPeriods) :
    periodTransport g x (periodVector x.1 n) =
      periodVector (rhoParameters g x).1 (rhoLambda g n) := by
  change (fullRankDomain (rhoParameters g x)).realEquiv
    (rhoLambdaReal g ((fullRankDomain x).realEquiv.symm (periodVector x.1 n))) = _
  rw [show (fullRankDomain x).realEquiv.symm (periodVector x.1 n) = integerToReal n by
    apply (fullRankDomain x).realEquiv.injective
    rw [(fullRankDomain x).realEquiv.apply_symm_apply]
    exact ((fullRankDomain x).map_integer n).symm]
  rw [rhoLambdaReal_integer]
  exact (fullRankDomain (rhoParameters g x)).map_integer _

public theorem periodTransport_one (x : PeriodDomain) :
    periodTransport 1 x = 1 := by
  apply LinearEquiv.ext
  intro z
  change (fullRankDomain (rhoParameters 1 x)).realEquiv
    (rhoLambdaReal 1 ((fullRankDomain x).realEquiv.symm z)) = z
  rw [map_one, Equiv.Perm.one_apply, map_one]
  simp

/-- Fibre transport satisfies the triangle-group cocycle law. -/
public theorem periodTransport_mul (g h : Delta) (x : PeriodDomain) :
    periodTransport (g * h) x =
      periodTransport g (rhoParameters h x) * periodTransport h x := by
  apply LinearEquiv.ext
  intro z
  change (fullRankDomain (rhoParameters (g * h) x)).realEquiv
      (rhoLambdaReal (g * h) ((fullRankDomain x).realEquiv.symm z)) =
    (fullRankDomain (rhoParameters g (rhoParameters h x))).realEquiv
      (rhoLambdaReal g ((fullRankDomain (rhoParameters h x)).realEquiv.symm
        ((fullRankDomain (rhoParameters h x)).realEquiv
          (rhoLambdaReal h ((fullRankDomain x).realEquiv.symm z)))))
  rw [map_mul, Equiv.Perm.mul_apply, map_mul, LinearEquiv.mul_apply,
    (fullRankDomain (rhoParameters h x)).realEquiv.symm_apply_apply]

/-- The standard integral basis vector in period coordinates. -/
@[expose] public def integralBasisVector (i : Fin 4) : IntegerPeriods :=
  Pi.single i 1

public theorem integerToReal_integralBasisVector (i : Fin 4) :
    integerToReal (integralBasisVector i) = (Pi.basisFun ℝ (Fin 4)) i := by
  rw [Pi.basisFun_apply]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [SphereSixComplex.Geometry.ComplexTorus.integerToReal.eq_def,
      integralBasisVector, Pi.single]

/-- At the order-three generator, canonical period transport is exactly the paper's complex
linear fibre-coordinate change. -/
public theorem periodTransport_gOne (x : PeriodDomain) :
    periodTransport g₁ x =
      (rightOneLinearEquiv x.1 x.tau_ne_zero).restrictScalars ℝ := by
  let hx := (fullRankDomain x).realEquiv.toLinearEquiv
  let R := (rightOneLinearEquiv x.1 x.tau_ne_zero).restrictScalars ℝ
  have hcomp : hx.trans (periodTransport g₁ x) = hx.trans R := by
    apply (Pi.basisFun ℝ (Fin 4)).ext'
    intro i
    rw [← integerToReal_integralBasisVector]
    change periodTransport g₁ x
        ((fullRankDomain x).realEquiv (integerToReal (integralBasisVector i))) =
      rightOneLinearEquiv x.1 x.tau_ne_zero
        ((fullRankDomain x).realEquiv (integerToReal (integralBasisVector i)))
    rw [(fullRankDomain x).map_integer, periodTransport_periodVector]
    rw [rhoParameters_g₁_apply, rhoLambda_g₁_apply]
    rw [rightOneLinearEquiv_apply, ← a₁_apply]
    exact generatorOne_periodVector x.1 x.tau_ne_zero (integralBasisVector i)
  apply LinearEquiv.ext
  intro z
  let v := hx.symm z
  have hz := DFunLike.congr_fun hcomp v
  simpa [hx, R, v] using hz

/-- At the order-four generator, canonical period transport is exactly the paper's complex
linear fibre-coordinate change. -/
public theorem periodTransport_gTwo (x : PeriodDomain) :
    periodTransport g₂ x =
      (rightTwoLinearEquiv x.1 x.tau_ne_zero).restrictScalars ℝ := by
  let hx := (fullRankDomain x).realEquiv.toLinearEquiv
  let R := (rightTwoLinearEquiv x.1 x.tau_ne_zero).restrictScalars ℝ
  have hcomp : hx.trans (periodTransport g₂ x) = hx.trans R := by
    apply (Pi.basisFun ℝ (Fin 4)).ext'
    intro i
    rw [← integerToReal_integralBasisVector]
    change periodTransport g₂ x
        ((fullRankDomain x).realEquiv (integerToReal (integralBasisVector i))) =
      rightTwoLinearEquiv x.1 x.tau_ne_zero
        ((fullRankDomain x).realEquiv (integerToReal (integralBasisVector i)))
    rw [(fullRankDomain x).map_integer, periodTransport_periodVector]
    rw [rhoParameters_g₂_apply, rhoLambda_g₂_apply]
    rw [rightTwoLinearEquiv_apply, ← a₂_apply]
    exact generatorTwo_periodVector x.1 x.tau_ne_zero (integralBasisVector i)
  apply LinearEquiv.ext
  intro z
  let v := hx.symm z
  have hz := DFunLike.congr_fun hcomp v
  simpa [hx, R, v] using hz

/-- Pointwise complex linearity of canonical fibre transport. -/
public def TransportIsComplexLinear (g : Delta) : Prop :=
  ∀ x : PeriodDomain, ∃ R : ComplexTwoSpace ≃ₗ[ℂ] ComplexTwoSpace,
    periodTransport g x = R.restrictScalars ℝ

public theorem transportIsComplexLinear_one : TransportIsComplexLinear 1 := by
  intro x
  refine ⟨1, ?_⟩
  rw [periodTransport_one]
  apply LinearEquiv.ext
  intro z
  rfl

public theorem TransportIsComplexLinear.mul {g h : Delta}
    (hg : TransportIsComplexLinear g) (hh : TransportIsComplexLinear h) :
    TransportIsComplexLinear (g * h) := by
  intro x
  obtain ⟨Rg, hRg⟩ := hg (rhoParameters h x)
  obtain ⟨Rh, hRh⟩ := hh x
  refine ⟨Rg * Rh, ?_⟩
  rw [periodTransport_mul, hRg, hRh]
  apply LinearEquiv.ext
  intro z
  rfl

public theorem TransportIsComplexLinear.pow {g : Delta} (hg : TransportIsComplexLinear g)
    (n : ℕ) : TransportIsComplexLinear (g ^ n) := by
  induction n with
  | zero => simpa using transportIsComplexLinear_one
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hg

public theorem transportIsComplexLinear_gOne : TransportIsComplexLinear g₁ := by
  intro x
  exact ⟨rightOneLinearEquiv x.1 x.tau_ne_zero, periodTransport_gOne x⟩

public theorem transportIsComplexLinear_gTwo : TransportIsComplexLinear g₂ := by
  intro x
  exact ⟨rightTwoLinearEquiv x.1 x.tau_ne_zero, periodTransport_gTwo x⟩

/-- Equivariance of a map into the period domain under one triangle-group element. -/
@[expose] public def ParameterEquivariant {U : TriangleUniformization} (F : PeriodFunctions U)
    (g : Delta) : Prop :=
  ∀ z, parameterMap F (U.sourceAction g • z) = rhoParameters g (parameterMap F z)

public theorem parameterEquivariant_one {U : TriangleUniformization} (F : PeriodFunctions U) :
    ParameterEquivariant F 1 := by
  intro z
  simp

public theorem ParameterEquivariant.mul {U : TriangleUniformization} (F : PeriodFunctions U)
    {g h : Delta} (hg : ParameterEquivariant F g) (hh : ParameterEquivariant F h) :
    ParameterEquivariant F (g * h) := by
  intro z
  calc
    parameterMap F (U.sourceAction (g * h) • z) =
        parameterMap F (U.sourceAction g • (U.sourceAction h • z)) := by
      rw [map_mul, mul_smul]
    _ = rhoParameters g (parameterMap F (U.sourceAction h • z)) := hg _
    _ = rhoParameters g (rhoParameters h (parameterMap F z)) := congrArg _ (hh z)
    _ = rhoParameters (g * h) (parameterMap F z) := by rw [map_mul]; rfl

public theorem ParameterEquivariant.pow {U : TriangleUniformization} (F : PeriodFunctions U)
    {g : Delta} (hg : ParameterEquivariant F g) (n : ℕ) : ParameterEquivariant F (g ^ n) := by
  induction n with
  | zero => simpa using parameterEquivariant_one F
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul F hg

public theorem parameterEquivariant_gOne {U : TriangleUniformization} (F : PeriodFunctions U) :
    ParameterEquivariant F g₁ := by
  intro z
  rw [rhoParameters_g₁_apply]
  apply Subtype.ext
  exact F.transform_one z

public theorem parameterEquivariant_gTwo {U : TriangleUniformization} (F : PeriodFunctions U) :
    ParameterEquivariant F g₂ := by
  intro z
  rw [rhoParameters_g₂_apply]
  apply Subtype.ext
  exact F.transform_two z

public theorem inl_exists_gOne_pow (a : CyclicThree) :
    ∃ n : ℕ, Monoid.Coprod.inl a = g₁ ^ n := by
  fin_cases a
  · refine ⟨0, ?_⟩
    change Monoid.Coprod.inl (Multiplicative.ofAdd (0 : ZMod 3)) = 1
    exact (Monoid.Coprod.inl : CyclicThree →* Delta).map_one
  · refine ⟨1, ?_⟩
    rw [pow_one, SphereSixComplex.TriangleGroup.g₁.eq_def]
    congr 1
  · refine ⟨2, ?_⟩
    change Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ ^ 2
    have hg := SphereSixComplex.TriangleGroup.g₁.eq_def
    rw [pow_two, hg]
    calc
      Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) =
          Monoid.Coprod.inl
            (Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 1) := by congr 1
      _ = _ := (Monoid.Coprod.inl : CyclicThree →* Delta).map_mul _ _

public theorem inr_exists_gTwo_pow (a : CyclicFour) :
    ∃ n : ℕ, Monoid.Coprod.inr a = g₂ ^ n := by
  fin_cases a
  · refine ⟨0, ?_⟩
    change Monoid.Coprod.inr (Multiplicative.ofAdd (0 : ZMod 4)) = 1
    exact (Monoid.Coprod.inr : CyclicFour →* Delta).map_one
  · refine ⟨1, ?_⟩
    rw [pow_one, SphereSixComplex.TriangleGroup.g₂.eq_def]
    congr 1
  · refine ⟨2, ?_⟩
    change Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ ^ 2
    have hg := SphereSixComplex.TriangleGroup.g₂.eq_def
    rw [pow_two, hg]
    calc
      Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) =
          Monoid.Coprod.inr
            (Multiplicative.ofAdd (1 : ZMod 4) * Multiplicative.ofAdd 1) := by congr 1
      _ = _ := (Monoid.Coprod.inr : CyclicFour →* Delta).map_mul _ _
  · refine ⟨3, ?_⟩
    change Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ ^ 3
    have hg := SphereSixComplex.TriangleGroup.g₂.eq_def
    rw [pow_succ, pow_two, hg]
    calc
      Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) =
          Monoid.Coprod.inr
            (Multiplicative.ofAdd (1 : ZMod 4) *
              (Multiplicative.ofAdd (1 : ZMod 4) * Multiplicative.ofAdd 1)) := by congr 1
      _ = Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) *
          Monoid.Coprod.inr
            (Multiplicative.ofAdd (1 : ZMod 4) * Multiplicative.ofAdd 1) :=
        (Monoid.Coprod.inr : CyclicFour →* Delta).map_mul _ _
      _ = Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) *
          (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) *
            Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4))) := by
        rw [(Monoid.Coprod.inr : CyclicFour →* Delta).map_mul]
      _ = _ := (mul_assoc _ _ _).symm

/-- Canonical fibre transport is complex linear for every triangle-group element. -/
public theorem periodTransport_isComplexLinear (g : Delta) : TransportIsComplexLinear g := by
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      obtain ⟨n, hn⟩ := inl_exists_gOne_pow a
      rw [hn]
      exact transportIsComplexLinear_gOne.pow n
  | inr a =>
      obtain ⟨n, hn⟩ := inr_exists_gTwo_pow a
      rw [hn]
      exact transportIsComplexLinear_gTwo.pow n
  | mul g h hg hh => exact hg.mul hh

/-- The period map is equivariant under every element of the triangle group. -/
public theorem parameterMap_equivariant {U : TriangleUniformization} (F : PeriodFunctions U)
    (g : Delta) : ParameterEquivariant F g := by
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      obtain ⟨n, hn⟩ := inl_exists_gOne_pow a
      rw [hn]
      exact (parameterEquivariant_gOne F).pow F _
  | inr a =>
      obtain ⟨n, hn⟩ := inr_exists_gTwo_pow a
      rw [hn]
      exact (parameterEquivariant_gTwo F).pow F _
  | mul g h hg hh => exact hg.mul F hh

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The regular part of the uniformizing upper half-plane, obtained by removing the two elliptic
orbits.  This is the base used for the paper's family `J`. -/
public def IsRegularBasePoint (z : UpperHalfPlane) : Prop :=
  ∀ g : Delta, U.sourceAction g • z ≠ U.zOne ∧ U.sourceAction g • z ≠ U.zTwo

/-- The upper-half-plane cover with both elliptic orbits removed. -/
public abbrev RegularBase := {z : UpperHalfPlane // IsRegularBasePoint (U := U) z}

public theorem isRegularBasePoint_smul (h : Delta) {z : UpperHalfPlane}
    (hz : IsRegularBasePoint (U := U) z) :
    IsRegularBasePoint (U := U) (U.sourceAction h • z) := by
  intro g
  simpa only [← mul_smul, ← map_mul] using hz (g * h)

/-- The triangle group acts by permutations of the regular upper-half-plane cover. -/
@[expose] public noncomputable def regularSourceEquiv (g : Delta) :
    Equiv.Perm (RegularBase (U := U)) where
  toFun z := ⟨U.sourceAction g • z.1, isRegularBasePoint_smul g z.2⟩
  invFun z := ⟨U.sourceAction g⁻¹ • z.1, isRegularBasePoint_smul g⁻¹ z.2⟩
  left_inv z := by
    apply Subtype.ext
    change U.sourceAction g⁻¹ • (U.sourceAction g • z.1) = z.1
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  right_inv z := by
    apply Subtype.ext
    change U.sourceAction g • (U.sourceAction g⁻¹ • z.1) = z.1
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

@[simp]
public theorem regularSourceEquiv_val (g : Delta) (z : RegularBase (U := U)) :
    (regularSourceEquiv g z).1 = U.sourceAction g • z.1 :=
  rfl

/-- The analytic period map restricted to the regular base. -/
@[expose] public def regularParameterMap (z : RegularBase (U := U)) : PeriodDomain :=
  parameterMap F z.1

/-- The lifted deck map on the analytic vector-bundle cover. -/
@[expose] public noncomputable def deckMap (g : Delta)
    (p : UpperHalfPlane × ComplexTwoSpace) : UpperHalfPlane × ComplexTwoSpace :=
  (U.sourceAction g • p.1, periodTransport g (parameterMap F p.1) p.2)

public theorem deckMap_one (p : UpperHalfPlane × ComplexTwoSpace) : deckMap F 1 p = p := by
  apply Prod.ext
  · simp [deckMap]
  · simp [deckMap, periodTransport_one]

public theorem deckMap_mul (g h : Delta) (p : UpperHalfPlane × ComplexTwoSpace) :
    deckMap F (g * h) p = deckMap F g (deckMap F h p) := by
  apply Prod.ext
  · simp [deckMap, map_mul, mul_smul]
  · change periodTransport (g * h) (parameterMap F p.1) p.2 =
      periodTransport g (parameterMap F (U.sourceAction h • p.1))
        (periodTransport h (parameterMap F p.1) p.2)
    rw [parameterMap_equivariant F h, periodTransport_mul, LinearEquiv.mul_apply]

/-- Every lifted deck map is an equivalence, with inverse indexed by the inverse group element. -/
@[expose] public noncomputable def deckEquiv (g : Delta) :
    Equiv.Perm (UpperHalfPlane × ComplexTwoSpace) where
  toFun := deckMap F g
  invFun := deckMap F g⁻¹
  left_inv p := by
    rw [← deckMap_mul, inv_mul_cancel, deckMap_one]
  right_inv p := by
    rw [← deckMap_mul, mul_inv_cancel, deckMap_one]

@[simp]
public theorem deckEquiv_apply (g : Delta) (p : UpperHalfPlane × ComplexTwoSpace) :
    deckEquiv F g p = deckMap F g p :=
  rfl

/-- The full triangle group acts on the analytic vector-bundle cover. -/
@[expose] public noncomputable def deckRepresentation :
    Delta →* Equiv.Perm (UpperHalfPlane × ComplexTwoSpace) where
  toFun := deckEquiv F
  map_one' := by
    apply Equiv.ext
    intro p
    change deckMap F 1 p = p
    exact deckMap_one F p
  map_mul' g h := by
    apply Equiv.ext
    intro p
    change deckMap F (g * h) p = deckMap F g (deckMap F h p)
    exact deckMap_mul F g h p

@[expose, instance_reducible] public noncomputable def deckAction :
    MulAction Delta (UpperHalfPlane × ComplexTwoSpace) where
  smul := deckMap F
  one_smul := deckMap_one F
  mul_smul := deckMap_mul F

/-- Monodromy transports a family-period group element by its integral coefficient. -/
@[expose] public def transportFamilyPeriod (g : Delta)
    (a : FamilyPeriodGroup (parameterMap F)) : FamilyPeriodGroup (parameterMap F) :=
  Multiplicative.ofAdd (rhoLambda g a.coeff)

/-- The lifted deck map intertwines lattice translation with integral monodromy. -/
public theorem deckMap_family_smul (g : Delta) (a : FamilyPeriodGroup (parameterMap F))
    (p : UpperHalfPlane × ComplexTwoSpace) :
    deckMap F g (a • p) = transportFamilyPeriod F g a • deckMap F g p := by
  apply Prod.ext
  · rfl
  · change periodTransport g (parameterMap F p.1)
        (periodVector (parameterMap F p.1).1 a.coeff + p.2) =
      periodVector (parameterMap F (U.sourceAction g • p.1)).1 (rhoLambda g a.coeff) +
        periodTransport g (parameterMap F p.1) p.2
    rw [map_add, periodTransport_periodVector, parameterMap_equivariant F g]

/-- The lifted deck map preserves, and reflects, the varying period-lattice orbit relation. -/
public theorem deckMap_orbitRel_iff (g : Delta) (p q : UpperHalfPlane × ComplexTwoSpace) :
    MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _ p q ↔
      MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _
        (deckMap F g p) (deckMap F g q) := by
  constructor
  · rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    rintro ⟨a, ha⟩
    refine ⟨transportFamilyPeriod F g a, ?_⟩
    calc
      transportFamilyPeriod F g a • deckMap F g q = deckMap F g (a • q) :=
        (deckMap_family_smul F g a q).symm
      _ = deckMap F g p := congrArg (deckMap F g) ha
  · rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    rintro ⟨a, ha⟩
    refine ⟨transportFamilyPeriod F g⁻¹ a, ?_⟩
    calc
      transportFamilyPeriod F g⁻¹ a • q = deckMap F g⁻¹ (a • deckMap F g q) := by
        rw [deckMap_family_smul, ← deckMap_mul, inv_mul_cancel, deckMap_one]
      _ = deckMap F g⁻¹ (deckMap F g p) := congrArg (deckMap F g⁻¹) ha
      _ = p := by rw [← deckMap_mul, inv_mul_cancel, deckMap_one]

/-- A triangle-group element descends from the vector-bundle cover to the analytic torus family. -/
@[expose] public noncomputable def familyDeckMap (g : Delta) :
    TotalSpace (parameterMap F) → TotalSpace (parameterMap F) :=
  Quotient.map (deckMap F g) fun p q h ↦ (deckMap_orbitRel_iff F g p q).mp h

@[simp]
public theorem familyDeckMap_mk (g : Delta) (p : UpperHalfPlane × ComplexTwoSpace) :
    familyDeckMap F g (Quotient.mk _ p) = Quotient.mk _ (deckMap F g p) :=
  rfl

public theorem familyDeckMap_one (x : TotalSpace (parameterMap F)) : familyDeckMap F 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ p => simp [familyDeckMap_mk, deckMap_one]

public theorem familyDeckMap_mul (g h : Delta) (x : TotalSpace (parameterMap F)) :
    familyDeckMap F (g * h) x = familyDeckMap F g (familyDeckMap F h x) := by
  induction x using Quotient.inductionOn with
  | _ p => simp [familyDeckMap_mk, deckMap_mul]

/-- The triangle group acts on the actual varying-lattice quotient. -/
@[expose, instance_reducible] public noncomputable def familyDeckAction :
    MulAction Delta (TotalSpace (parameterMap F)) where
  smul := familyDeckMap F
  one_smul := familyDeckMap_one F
  mul_smul := familyDeckMap_mul F

/-- The unexcised quotient of the analytic torus family by the full triangle-group deck action.
The paper's family uses `PuncturedGlobalFamily`, which removes the elliptic orbits first. -/
public abbrev UnexcisedGlobalFamily :=
  letI := familyDeckAction F
  OrbitQuotient (M := TotalSpace (parameterMap F)) (G := Delta)

/-- The lifted deck map on the regular analytic vector-bundle cover. -/
@[expose] public noncomputable def regularDeckMap (g : Delta)
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    RegularBase (U := U) × ComplexTwoSpace :=
  (regularSourceEquiv g p.1, periodTransport g (regularParameterMap F p.1) p.2)

public theorem regularDeckMap_one (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularDeckMap F 1 p = p := by
  apply Prod.ext
  · apply Subtype.ext
    simp [regularDeckMap, regularSourceEquiv]
  · simp [regularDeckMap, periodTransport_one]

public theorem regularDeckMap_mul (g h : Delta)
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularDeckMap F (g * h) p = regularDeckMap F g (regularDeckMap F h p) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [regularDeckMap, regularSourceEquiv, map_mul, mul_smul]
  · change periodTransport (g * h) (regularParameterMap F p.1) p.2 =
      periodTransport g (regularParameterMap F (regularSourceEquiv h p.1))
        (periodTransport h (regularParameterMap F p.1) p.2)
    change periodTransport (g * h) (parameterMap F p.1.1) p.2 =
      periodTransport g (parameterMap F (U.sourceAction h • p.1.1))
        (periodTransport h (parameterMap F p.1.1) p.2)
    rw [parameterMap_equivariant F h, periodTransport_mul, LinearEquiv.mul_apply]

/-- Monodromy on the family-period group over the regular base. -/
@[expose] public def transportRegularFamilyPeriod (g : Delta)
    (a : FamilyPeriodGroup (regularParameterMap F)) :
    FamilyPeriodGroup (regularParameterMap F) :=
  Multiplicative.ofAdd (rhoLambda g a.coeff)

/-- The regular lifted action intertwines lattice translation with integral monodromy. -/
public theorem regularDeckMap_family_smul (g : Delta)
    (a : FamilyPeriodGroup (regularParameterMap F))
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularDeckMap F g (a • p) =
      transportRegularFamilyPeriod F g a • regularDeckMap F g p := by
  apply Prod.ext
  · rfl
  · change periodTransport g (parameterMap F p.1.1)
        (periodVector (parameterMap F p.1.1).1 a.coeff + p.2) =
      periodVector (parameterMap F (U.sourceAction g • p.1.1)).1 (rhoLambda g a.coeff) +
        periodTransport g (parameterMap F p.1.1) p.2
    rw [map_add, periodTransport_periodVector, parameterMap_equivariant F g]

/-- The regular lifted deck map preserves and reflects varying-lattice orbits. -/
public theorem regularDeckMap_orbitRel_iff (g : Delta)
    (p q : RegularBase (U := U) × ComplexTwoSpace) :
    MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p q ↔
      MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
        (regularDeckMap F g p) (regularDeckMap F g q) := by
  constructor
  · rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    rintro ⟨a, ha⟩
    refine ⟨transportRegularFamilyPeriod F g a, ?_⟩
    calc
      transportRegularFamilyPeriod F g a • regularDeckMap F g q =
          regularDeckMap F g (a • q) := (regularDeckMap_family_smul F g a q).symm
      _ = regularDeckMap F g p := congrArg (regularDeckMap F g) ha
  · rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    rintro ⟨a, ha⟩
    refine ⟨transportRegularFamilyPeriod F g⁻¹ a, ?_⟩
    calc
      transportRegularFamilyPeriod F g⁻¹ a • q =
          regularDeckMap F g⁻¹ (a • regularDeckMap F g q) := by
        rw [regularDeckMap_family_smul, ← regularDeckMap_mul, inv_mul_cancel,
          regularDeckMap_one]
      _ = regularDeckMap F g⁻¹ (regularDeckMap F g p) :=
        congrArg (regularDeckMap F g⁻¹) ha
      _ = p := by rw [← regularDeckMap_mul, inv_mul_cancel, regularDeckMap_one]

/-- The analytic torus family over the regular upper-half-plane cover. -/
public abbrev RegularTotalSpace := TotalSpace (regularParameterMap F)

/-- A triangle-group element descends to the torus family over the regular base. -/
@[expose] public noncomputable def regularFamilyDeckMap (g : Delta) :
    RegularTotalSpace F → RegularTotalSpace F :=
  Quotient.map (regularDeckMap F g) fun p q h ↦ (regularDeckMap_orbitRel_iff F g p q).mp h

@[simp]
public theorem regularFamilyDeckMap_mk (g : Delta)
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularFamilyDeckMap F g (Quotient.mk _ p) = Quotient.mk _ (regularDeckMap F g p) :=
  rfl

public theorem regularFamilyDeckMap_one (x : RegularTotalSpace F) :
    regularFamilyDeckMap F 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ p => simp [regularFamilyDeckMap_mk, regularDeckMap_one]

public theorem regularFamilyDeckMap_mul (g h : Delta) (x : RegularTotalSpace F) :
    regularFamilyDeckMap F (g * h) x =
      regularFamilyDeckMap F g (regularFamilyDeckMap F h x) := by
  induction x using Quotient.inductionOn with
  | _ p => simp [regularFamilyDeckMap_mk, regularDeckMap_mul]

/-- The triangle group acts on the actual torus family over the regular base. -/
@[expose, instance_reducible] public noncomputable def regularFamilyDeckAction :
    MulAction Delta (RegularTotalSpace F) where
  smul := regularFamilyDeckMap F
  one_smul := regularFamilyDeckMap_one F
  mul_smul := regularFamilyDeckMap_mul F

/-- The paper's global family `J` before adjoining its cusp and elliptic fillings. -/
public abbrev PuncturedGlobalFamily :=
  letI := regularFamilyDeckAction F
  OrbitQuotient (M := RegularTotalSpace F) (G := Delta)

end

end SphereSixComplex.Geometry.GlobalTorusFamily
