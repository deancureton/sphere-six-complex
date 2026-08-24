module

public import SphereSixComplex.Geometry.GlobalTorusFamily
import all SphereSixComplex.Periods.Matrix
import all SphereSixComplex.Periods.Domain

/-!
# Smoothness of the global lifted deck action

The generator transports are the explicit complex-linear maps `rightOne` and `rightTwo`; the
cusp transport is the identity.  Their coefficients are smooth functions of the analytic period
map.  The cocycle law for `deckMap` then extends smoothness to every free-product word.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open Matrix UpperHalfPlane SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance

public noncomputable section

public abbrev GlobalDeckBaseModel := modelWithCornersSelf ℂ ℂ
public abbrev GlobalDeckFiberModel := modelWithCornersSelf ℂ ComplexTwoSpace
public abbrev GlobalDeckTotalModel := GlobalDeckBaseModel.prod GlobalDeckFiberModel

variable {U : TriangleUniformization} (F : PeriodFunctions U)

private theorem tauOnTotal_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ (F.tau p.1 : ℂ)) :=
  (tau_contMDiff F n).comp contMDiff_fst

private theorem muOnTotal_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ F.mu p.1) :=
  (mu_contMDiff F n).comp contMDiff_fst

private theorem fiberComponent_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ p.2 i) := by
  have h : ContMDiff GlobalDeckTotalModel GlobalDeckFiberModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ p.2) := contMDiff_snd
  exact (contMDiff_pi_space.mp h) i

private theorem inverseTauOnTotal_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ ((F.tau p.1 : ℂ))⁻¹) :=
  (tauOnTotal_contMDiff F n).inv₀ fun p ↦ (F.tau p.1).ne_zero

private theorem oneOnTotal_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) n
      (fun _ : UpperHalfPlane × ComplexTwoSpace ↦ (1 : ℂ)) :=
  contMDiff_const

/-- The first generator's explicit fibre-coordinate change is jointly smooth in base and fibre. -/
public theorem rightOne_parameterMap_mulVec_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckFiberModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦
        rightOne (parameterMap F p.1).1 *ᵥ p.2) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h := (inverseTauOnTotal_contMDiff F n).neg.mul
      (fiberComponent_contMDiff (0 : Fin 2) n)
    convert h using 1
    funext p
    simp [rightOne, parameterMap, periodValues, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · have h := (((((oneOnTotal_contMDiff n).sub (muOnTotal_contMDiff F n)).mul
        (inverseTauOnTotal_contMDiff F n)).mul
          (fiberComponent_contMDiff (0 : Fin 2) n)).add
            (fiberComponent_contMDiff (1 : Fin 2) n))
    convert h using 1
    funext p
    simp [rightOne, parameterMap, periodValues, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    left
    rw [div_eq_mul_inv]

/-- The second generator's explicit fibre-coordinate change is jointly smooth in base and fibre. -/
public theorem rightTwo_parameterMap_mulVec_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckFiberModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦
        rightTwo (parameterMap F p.1).1 *ᵥ p.2) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h := (inverseTauOnTotal_contMDiff F n).mul
      (fiberComponent_contMDiff (0 : Fin 2) n)
    convert h using 1
    funext p
    simp [rightTwo, parameterMap, periodValues, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · have h := ((((muOnTotal_contMDiff F n).neg.mul
        (inverseTauOnTotal_contMDiff F n)).mul
          (fiberComponent_contMDiff (0 : Fin 2) n)).add
            (fiberComponent_contMDiff (1 : Fin 2) n))
    convert h using 1
    funext p
    simp [rightTwo, parameterMap, periodValues, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring

/-- Canonical fibre transport at the cusp generator is the identity. -/
public theorem periodTransport_gZero (x : PeriodDomain) : periodTransport g₀ x = 1 := by
  let hx := (fullRankDomain x).realEquiv.toLinearEquiv
  have hcomp : hx.trans (periodTransport g₀ x) = hx := by
    apply (Pi.basisFun ℝ (Fin 4)).ext'
    intro i
    rw [← integerToReal_integralBasisVector]
    change periodTransport g₀ x
        ((fullRankDomain x).realEquiv (integerToReal (integralBasisVector i))) =
      (fullRankDomain x).realEquiv (integerToReal (integralBasisVector i))
    rw [(fullRankDomain x).map_integer, periodTransport_periodVector]
    rw [rhoParameters_g₀_apply, rhoLambda_g0]
    change periodVector (transformCusp x.1) (m₀ (integralBasisVector i)) = _
    exact cusp_periodVector x.1 (integralBasisVector i)
  apply LinearEquiv.ext
  intro z
  let v := hx.symm z
  have hz := DFunLike.congr_fun hcomp v
  simpa [hx, v] using hz

/-- The lifted deck transformation at the order-three generator is smooth. -/
public theorem deckMap_gOne_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F g₁) := by
  have hbase : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ U.sourceAction g₁ • p.1) :=
    (U.sourceAction_contMDiff g₁ n).comp contMDiff_fst
  apply hbase.prodMk
  convert rightOne_parameterMap_mulVec_contMDiff F n using 1
  funext p
  rw [periodTransport_gOne]
  change rightOneLinearEquiv (parameterMap F p.1).1
    (parameterMap F p.1).tau_ne_zero p.2 = _
  rw [rightOneLinearEquiv_apply]

/-- The lifted deck transformation at the order-four generator is smooth. -/
public theorem deckMap_gTwo_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F g₂) := by
  have hbase : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ U.sourceAction g₂ • p.1) :=
    (U.sourceAction_contMDiff g₂ n).comp contMDiff_fst
  apply hbase.prodMk
  convert rightTwo_parameterMap_mulVec_contMDiff F n using 1
  funext p
  rw [periodTransport_gTwo]
  change rightTwoLinearEquiv (parameterMap F p.1).1
    (parameterMap F p.1).tau_ne_zero p.2 = _
  rw [rightTwoLinearEquiv_apply]

/-- The lifted cusp deck transformation is smooth. -/
public theorem deckMap_gZero_contMDiff (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F g₀) := by
  have hbase : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel n
      (fun p : UpperHalfPlane × ComplexTwoSpace ↦ U.sourceAction g₀ • p.1) :=
    (U.sourceAction_contMDiff g₀ n).comp contMDiff_fst
  apply hbase.prodMk
  convert contMDiff_snd using 1
  funext p
  simp [periodTransport_gZero]

private def DeckMapContMDiff (n : WithTop ℕ∞) (g : Delta) : Prop :=
  ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F g)

private theorem deckMap_one_contMDiff (n : WithTop ℕ∞) : DeckMapContMDiff F n 1 := by
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F 1)
  convert (contMDiff_id : ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
    (id : UpperHalfPlane × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace)) using 1
  funext p
  exact deckMap_one F p

private theorem deckMapContMDiff_mul {n : WithTop ℕ∞} {g h : Delta}
    (hg : DeckMapContMDiff F n g) (hh : DeckMapContMDiff F n h) :
    DeckMapContMDiff F n (g * h) := by
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F (g * h))
  convert hg.comp hh using 1
  funext p
  exact deckMap_mul F g h p

private theorem deckMapContMDiff_pow {n : WithTop ℕ∞} {g : Delta}
    (hg : DeckMapContMDiff F n g) (k : ℕ) : DeckMapContMDiff F n (g ^ k) := by
  induction k with
  | zero => simpa using deckMap_one_contMDiff F n
  | succ k ih =>
      rw [pow_succ]
      exact deckMapContMDiff_mul F ih hg

/-- Every lifted triangle-group deck map is smooth.  This is the smooth-action hypothesis needed
by the generic quotient-manifold construction, independently of freeness or proper discontinuity. -/
public theorem deckMap_contMDiff (g : Delta) (n : WithTop ℕ∞) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (deckMap F g) := by
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      obtain ⟨k, hk⟩ := inl_exists_gOne_pow a
      rw [hk]
      exact deckMapContMDiff_pow F (deckMap_gOne_contMDiff F n) k
  | inr a =>
      obtain ⟨k, hk⟩ := inr_exists_gTwo_pow a
      rw [hk]
      exact deckMapContMDiff_pow F (deckMap_gTwo_contMDiff F n) k
  | mul g h hg hh => exact deckMapContMDiff_mul F hg hh

end

end SphereSixComplex.Geometry.GlobalTorusFamily
