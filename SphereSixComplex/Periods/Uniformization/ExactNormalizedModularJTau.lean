module

public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Periods.FuchsianModularParameterExistence
public import Mathlib.Analysis.Complex.OpenMapping
import all Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import all Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import all Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import all Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
import all TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
import all TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Order.Orbits
import all TauCeti.NumberTheory.ModularForms.Order.Orbits
public import TauCeti.NumberTheory.ModularForms.Order.OrbitReduction
import all TauCeti.NumberTheory.ModularForms.Order.OrbitReduction
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ValencePV
import all TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ValencePV
public import TauCeti.NumberTheory.ModularForms.LevelOne.ValenceFormula
import all TauCeti.NumberTheory.ModularForms.LevelOne.ValenceFormula

@[expose] public section

/-!
# Exact normalized modular-`J` uniformization

This module assembles Tau Ceti's level-one modular-form results into the exact quotient,
ramification, special-value, fibre, and cusp properties of the normalized modular invariant.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm Modular

noncomputable section

namespace SphereSixComplex.Periods.ExactNormalizedModularJTau

open SphereSixComplex.TriangleGroup
open TauCeti

local notation "SLZ" => MonoidHom.range
  (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)

local notation "SLRZ" => MonoidHom.range
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ))

/-- Tau Ceti's orbit-sum valence assembly, restated locally with explicit type parameters. -/
theorem levelOneValenceFormula {F : Type*} [FunLike F UpperHalfPlane ℂ] {k : ℤ}
    [ModularFormClass F SLZ k] (f : F) (hf : (f : UpperHalfPlane → ℂ) ≠ 0) :
    ((∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
        TauCeti.ModularForm.orderOfVanishingOnOrbit f q.val : ℤ) : ℂ)
      + 1 / 2 * ((orderOfVanishingAt (f : UpperHalfPlane → ℂ) UpperHalfPlane.I : ℤ) : ℂ)
      + 1 / 3 * ((orderOfVanishingAt (f : UpperHalfPlane → ℂ) UpperHalfPlane.ρ : ℤ) : ℂ)
      + qExpansionOrderAtCusp 1 (f : UpperHalfPlane → ℂ) = (k : ℂ) / 12 := by
  exact TauCeti.ModularForm.valence_formula f hf

/-- The integral modular group embedded into `SL(2, ℝ)`. -/
def sl2zToSLRZ (g : SL(2, ℤ)) : SLRZ :=
  ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g, ⟨g, rfl⟩⟩

theorem sl2zToSLRZ_injective : Function.Injective sl2zToSLRZ := by
  intro g h hgh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hij := congrArg
    (fun x : SLRZ ↦ (((x : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j)) hgh
  change ((g i j : ℤ) : ℝ) = ((h i j : ℤ) : ℝ) at hij
  exact_mod_cast hij

@[simp]
theorem sl2zToSLRZ_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    sl2zToSLRZ g • z = g • z := by
  rfl

local instance instContinuousConstSMulPSL2Z :
    ContinuousConstSMul PSL(2, ℤ) UpperHalfPlane where
  continuous_const_smul g := by
    refine QuotientGroup.induction_on g fun a ↦ ?_
    change Continuous fun z : UpperHalfPlane ↦ a • z
    change Continuous fun z : UpperHalfPlane ↦
      Matrix.SpecialLinearGroup.mapGL ℝ a • z
    exact continuous_const_smul _

local instance instProperlyDiscontinuousSMulPSL2Z :
    ProperlyDiscontinuousSMul PSL(2, ℤ) UpperHalfPlane where
  finite_disjoint_inter_image {K L} hK hL := by
    let B : Set SL(2, ℤ) := {g | ((g • ·) '' K ∩ L).Nonempty}
    let C : Set SLRZ := {g | ((g • ·) '' K ∩ L).Nonempty}
    have hC : C.Finite :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hL
    have hBpre : B = sl2zToSLRZ ⁻¹' C := by
      ext g
      simp only [B, C, Set.mem_setOf_eq, Set.mem_preimage, sl2zToSLRZ_smul]
    have hB : B.Finite := by
      rw [hBpre]
      exact hC.preimage sl2zToSLRZ_injective.injOn
    have hquot : {g : PSL(2, ℤ) | ((g • ·) '' K ∩ L).Nonempty} =
        ((↑) : SL(2, ℤ) → PSL(2, ℤ)) '' B := by
      ext g
      constructor
      · intro hg
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
        refine ⟨a, ?_, rfl⟩
        simpa only [B, Set.mem_setOf_eq, UpperHalfPlane.pslMk_smul] using hg
      · rintro ⟨a, ha, rfl⟩
        simpa only [B, Set.mem_setOf_eq, UpperHalfPlane.pslMk_smul] using ha
    rw [hquot]
    exact hB.image _

/-- The weight-twelve form whose zeros are the fibre of normalized `J` over `c`. -/
noncomputable def fiberForm (c : ℂ) :
    ModularForm SLZ 12 :=
  ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) -
    (1728 * c) •
      (CuspForm.discriminant : ModularForm SLZ 12)

@[simp]
theorem fiberForm_apply (c : ℂ) (z : UpperHalfPlane) :
    fiberForm c z = ModularForm.E₄ z ^ 3 - 1728 * c * ModularForm.discriminant z := by
  simp only [fiberForm, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply,
    _root_.sub_apply, FunLike.coe_smul, ModularFormClass.coe_modularForm,
    CuspForm.coe_discriminant, Pi.smul_apply, smul_eq_mul]

/-- The constant coefficient of every fibre form is one. -/
theorem fiberForm_qExpansion_coeff_zero (c : ℂ) :
    (UpperHalfPlane.qExpansion 1 (fiberForm c)).coeff 0 = 1 := by
  let Δmf : ModularForm SLZ 12 :=
    (CuspForm.discriminant : ModularForm SLZ 12)
  rw [fiberForm]
  rw [FunLike.coe_sub]
  rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  rw [FunLike.coe_smul]
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  rw [ModularForm.coe_mcast]
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hΔ0 : (UpperHalfPlane.qExpansion 1 (Δmf : UpperHalfPlane → ℂ)).coeff 0 = 0 := by
    simpa [Δmf, ModularFormClass.coe_modularForm] using
      (CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL)
  rw [map_sub, PowerSeries.coeff_smul, hΔ0]
  simp only [smul_zero, sub_zero]
  have hE : (UpperHalfPlane.qExpansion 1
      (ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
  simpa [pow_succ, PowerSeries.coeff_mul, hE]

/-- No fibre form is identically zero. -/
theorem fiberForm_ne_zero (c : ℂ) :
    ((fiberForm c : ModularForm SLZ 12) :
      UpperHalfPlane → ℂ) ≠ 0 := by
  intro h
  have hc := fiberForm_qExpansion_coeff_zero c
  rw [h, UpperHalfPlane.qExpansion_zero] at hc
  simpa using hc

/-- Every fibre form has order zero at the cusp. -/
theorem fiberForm_cuspOrder (c : ℂ) :
    qExpansionOrderAtCusp 1 (fiberForm c : UpperHalfPlane → ℂ) = 0 := by
  apply (TauCeti.ModularForm.qExpansionOrderAtCusp_eq_zero_iff
    (f := fiberForm c) one_pos one_mem_strictPeriods_SL (fiberForm_ne_zero c)).2
  have hval : UpperHalfPlane.cuspFunction 1 (fiberForm c : UpperHalfPlane → ℂ) 0 = 1 := by
    simpa [UpperHalfPlane.qExpansion_coeff] using fiberForm_qExpansion_coeff_zero c
  rw [hval]
  norm_num

/-- The fibre form vanishes exactly on the corresponding normalized-`J` fibre. -/
theorem fiberForm_eq_zero_iff (c : ℂ) (z : UpperHalfPlane) :
    fiberForm c z = 0 ↔ normalizedModularJCoordinate z = c := by
  rw [fiberForm_apply, normalizedModularJCoordinate, normalizedJ]
  have hΔ := ModularForm.discriminant_ne_zero z
  constructor
  · intro h
    field_simp [hΔ]
    linear_combination h
  · intro h
    field_simp [hΔ] at h
    linear_combination h

/-- The exact orbit-sum valence statement needed from the TauCeti backport. -/
def LevelOneValenceInput : Prop :=
  ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {k : ℤ}
      [ModularFormClass F SLZ k]
      (f : F), ((f : UpperHalfPlane → ℂ) ≠ 0) →
    ((∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
        TauCeti.ModularForm.orderOfVanishingOnOrbit f q.val : ℤ) : ℂ)
      + 1 / 2 * ((orderOfVanishingAt (f : UpperHalfPlane → ℂ) UpperHalfPlane.I : ℤ) : ℂ)
      + 1 / 3 * ((orderOfVanishingAt (f : UpperHalfPlane → ℂ) UpperHalfPlane.ρ : ℤ) : ℂ)
      + qExpansionOrderAtCusp 1 (f : UpperHalfPlane → ℂ) = (k : ℂ) / 12

/-- TauCeti's unconditional valence theorem supplies exactly the input used below. -/
theorem levelOneValenceInput : LevelOneValenceInput := by
  intro F instFunLike k instModularFormClass f hf
  exact levelOneValenceFormula f hf

/-- The weight-six Eisenstein series vanishes at the order-two elliptic point. -/
theorem E₆_at_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  letI : SlashInvariantFormClass (ModularForm SLZ 6)
      (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (⊤ : Subgroup SL(2, ℤ))) 6 := by
    rw [← MonoidHom.range_eq_map]
    infer_instance
  have h := SlashInvariantForm.slash_action_eqn_SL'' (Γ := ⊤) (k := 6)
    ModularForm.E₆ (γ := ModularGroup.S) (by simp) UpperHalfPlane.I
  have hSI : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.modular_S_smul]
    norm_num [UpperHalfPlane.I]
  rw [hSI] at h
  change ModularForm.E₆ UpperHalfPlane.I =
    UpperHalfPlane.denom ModularGroup.S UpperHalfPlane.I ^ (6 : ℤ) *
      ModularForm.E₆ UpperHalfPlane.I at h
  rw [ModularGroup.denom_S] at h
  norm_num [zpow_ofNat, pow_succ, Complex.I_mul_I] at h
  linear_combination h / 2

/-- The normalized coordinate takes the value one at the order-two elliptic point. -/
theorem coordinate_at_I :
    normalizedModularJCoordinate UpperHalfPlane.I = 1 := by
  rw [normalizedModularJCoordinate, normalizedJ,
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, E₆_at_I]
  have hΔ := ModularForm.discriminant_ne_zero UpperHalfPlane.I
  have hE : ModularForm.E₄ UpperHalfPlane.I ^ 3 ≠ 0 := by
    intro h
    apply hΔ
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, E₆_at_I, h]
    norm_num
  simp [hE]

/-- The weight-four Eisenstein series vanishes at the translated order-three point. -/
theorem E₄_at_ellipticThreeParameter :
    ModularForm.E₄ ellipticThreeParameter = 0 := by
  letI : SlashInvariantFormClass (ModularForm SLZ 4)
      (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (⊤ : Subgroup SL(2, ℤ))) 4 := by
    rw [← MonoidHom.range_eq_map]
    infer_instance
  have hzFixed : modularOne • ellipticThreeParameter = ellipticThreeParameter := by
    change modularToReal modularOne • ellipticThreeParameter = ellipticThreeParameter
    rw [← rhoTau_g₁]
    change rhoTauReal g₁ • ellipticThreeParameter = ellipticThreeParameter
    exact (rhoTauReal_gOne_fixed_iff ellipticThreeParameter).mpr rfl
  have h := SlashInvariantForm.slash_action_eqn_SL'' (Γ := ⊤) (k := 4)
    ModularForm.E₄ (γ := modularOne) (by simp) ellipticThreeParameter
  rw [hzFixed] at h
  change ModularForm.E₄ ellipticThreeParameter =
    UpperHalfPlane.denom modularOne ellipticThreeParameter ^ (4 : ℤ) *
      ModularForm.E₄ ellipticThreeParameter at h
  have hdenom : UpperHalfPlane.denom modularOne ellipticThreeParameter =
      -(ellipticThreeParameter : ℂ) := by
    rw [ModularGroup.denom_apply]
    norm_num [modularOne]
  rw [hdenom] at h
  have hz2 : (ellipticThreeParameter : ℂ) ^ 2 = UpperHalfPlane.ρ := by
    change ((UpperHalfPlane.ρ : ℂ) + 1) ^ 2 = UpperHalfPlane.ρ
    rw [show ((UpperHalfPlane.ρ : ℂ) + 1) ^ 2 =
      (UpperHalfPlane.ρ : ℂ) ^ 2 + 2 * UpperHalfPlane.ρ + 1 by ring]
    rw [UpperHalfPlane.ρ_sq]
    ring
  have hz4 : (-(ellipticThreeParameter : ℂ)) ^ (4 : ℤ) =
      -(ellipticThreeParameter : ℂ) := by
    rw [zpow_ofNat]
    calc
      (-(ellipticThreeParameter : ℂ)) ^ 4 =
          ((ellipticThreeParameter : ℂ) ^ 2) ^ 2 := by ring
      _ = (UpperHalfPlane.ρ : ℂ) ^ 2 := by rw [hz2]
      _ = -(ellipticThreeParameter : ℂ) := by
        rw [UpperHalfPlane.ρ_sq]
        change -(UpperHalfPlane.ρ : ℂ) - 1 = -((UpperHalfPlane.ρ : ℂ) + 1)
        ring
  rw [hz4] at h
  have hfactor : -(ellipticThreeParameter : ℂ) ≠ 1 := by
    intro heq
    have him := congrArg Complex.im heq
    norm_num at him
    exact (ne_of_gt ellipticThreeParameter.im_pos) him
  have hprod : (1 - (-(ellipticThreeParameter : ℂ))) *
      ModularForm.E₄ ellipticThreeParameter = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hfactor.symm)

/-- The normalized coordinate takes the value zero at the translated order-three point. -/
theorem coordinate_at_ellipticThreeParameter :
    normalizedModularJCoordinate ellipticThreeParameter = 0 := by
  simp [normalizedModularJCoordinate, normalizedJ, E₄_at_ellipticThreeParameter]

/-- The fundamental-domain representative `ρ` has normalized coordinate zero as well. -/
theorem coordinate_at_rho : normalizedModularJCoordinate UpperHalfPlane.ρ = 0 := by
  have h := normalizedModularJCoordinate_invariant ModularGroup.T UpperHalfPlane.ρ
  change normalizedModularJCoordinate (ModularGroup.T • UpperHalfPlane.ρ) =
    normalizedModularJCoordinate UpperHalfPlane.ρ at h
  rw [UpperHalfPlane.modular_T_smul] at h
  rw [← h]
  have hp : (1 : ℝ) +ᵥ UpperHalfPlane.ρ = ellipticThreeParameter := by
    apply UpperHalfPlane.coe_injective
    change (1 : ℂ) + (UpperHalfPlane.ρ : ℂ) = (UpperHalfPlane.ρ : ℂ) + 1
    ring
  rw [hp]
  exact coordinate_at_ellipticThreeParameter

/-- The orbit-sum valence identity specialized to the weight-twelve fibre form. -/
theorem fiberForm_valence (c : ℂ) :
    ((∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
        TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm c) q.val : ℤ) : ℂ)
      + 1 / 2 * ((orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ)
          UpperHalfPlane.I : ℤ) : ℂ)
      + 1 / 3 * ((orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ)
          UpperHalfPlane.ρ : ℤ) : ℂ) = 1 := by
  have h := levelOneValenceFormula (fiberForm c) (fiberForm_ne_zero c)
  rw [fiberForm_cuspOrder] at h
  norm_num at h ⊢
  linear_combination h

/-- The fibre form is holomorphic as a function on the upper half-plane. -/
theorem fiberForm_holomorphic (c : ℂ) :
    MDiff (fiberForm c : UpperHalfPlane → ℂ) :=
  ModularFormClass.holo (fiberForm c)

/-- Positive order of the fibre form is exactly membership in the corresponding fibre. -/
theorem fiberForm_order_pos_iff (c : ℂ) (z : UpperHalfPlane) :
    0 < orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ) z ↔
      normalizedModularJCoordinate z = c := by
  rw [orderOfVanishingAt_pos_iff (fiberForm_holomorphic c) (fiberForm_ne_zero c),
    fiberForm_eq_zero_iff]

/-- Every orbit summand in the fibre-form valence formula is nonnegative. -/
theorem fiberForm_orbitOrder_nonneg (c : ℂ)
    (q : TauCeti.ModularForm.NonEllipticOrbit) :
    0 ≤ TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm c) q.val := by
  refine Quotient.inductionOn' q.val ?_
  intro z
  simpa using orderOfVanishingAt_nonneg (fiberForm_holomorphic c) z

/-- At `c = 0`, the fibre form is the cube of `E₄`. -/
theorem fiberForm_zero_fun :
    (fiberForm 0 : UpperHalfPlane → ℂ) =
      (ModularForm.E₄ : UpperHalfPlane → ℂ) ^ 3 := by
  funext z
  simp [fiberForm_apply]

/-- At `c = 1`, the fibre form is the square of `E₆`. -/
theorem fiberForm_one_fun :
    (fiberForm 1 : UpperHalfPlane → ℂ) =
      (ModularForm.E₆ : UpperHalfPlane → ℂ) ^ 2 := by
  funext z
  change fiberForm 1 z = ModularForm.E₆ z ^ 2
  rw [fiberForm_apply, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- The fibre over zero has exact order three at `ρ`. -/
theorem fiberForm_zero_order_rho :
    orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ) UpperHalfPlane.ρ = 3 := by
  let S : ℤ := ∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 0) q.val
  let a : ℤ := orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ) UpperHalfPlane.I
  let b : ℤ := orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ) UpperHalfPlane.ρ
  have hval := fiberForm_valence 0
  have hval' : 6 * S + 3 * a + 2 * b = 6 := by
    have hc : (((6 * S + 3 * a + 2 * b : ℤ) : ℂ)) = 6 := by
      push_cast
      dsimp [S, a, b]
      linear_combination 6 * hval
    exact_mod_cast hc
  have hS : 0 ≤ S := finsum_nonneg (fiberForm_orbitOrder_nonneg 0)
  have ha : 0 ≤ a := orderOfVanishingAt_nonneg (fiberForm_holomorphic 0) _
  have hb : 0 ≤ b := orderOfVanishingAt_nonneg (fiberForm_holomorphic 0) _
  have hbpos : 0 < b := (fiberForm_order_pos_iff 0 UpperHalfPlane.ρ).2 coordinate_at_rho
  have hbmul : b = 3 * orderOfVanishingAt
      (ModularForm.E₄ : UpperHalfPlane → ℂ) UpperHalfPlane.ρ := by
    dsimp [b]
    rw [fiberForm_zero_fun,
      orderOfVanishingAt_pow (ModularFormClass.holo ModularForm.E₄)]
    norm_num
  have hb3 : 3 ≤ b := by
    rw [hbmul] at hbpos ⊢
    omega
  change b = 3
  omega

/-- The fibre over one has exact order two at `i`. -/
theorem fiberForm_one_order_I :
    orderOfVanishingAt (fiberForm 1 : UpperHalfPlane → ℂ) UpperHalfPlane.I = 2 := by
  let S : ℤ := ∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 1) q.val
  let a : ℤ := orderOfVanishingAt (fiberForm 1 : UpperHalfPlane → ℂ) UpperHalfPlane.I
  let b : ℤ := orderOfVanishingAt (fiberForm 1 : UpperHalfPlane → ℂ) UpperHalfPlane.ρ
  have hval := fiberForm_valence 1
  have hval' : 6 * S + 3 * a + 2 * b = 6 := by
    have hc : (((6 * S + 3 * a + 2 * b : ℤ) : ℂ)) = 6 := by
      push_cast
      dsimp [S, a, b]
      linear_combination 6 * hval
    exact_mod_cast hc
  have hS : 0 ≤ S := finsum_nonneg (fiberForm_orbitOrder_nonneg 1)
  have ha : 0 ≤ a := orderOfVanishingAt_nonneg (fiberForm_holomorphic 1) _
  have hb : 0 ≤ b := orderOfVanishingAt_nonneg (fiberForm_holomorphic 1) _
  have hapos : 0 < a := (fiberForm_order_pos_iff 1 UpperHalfPlane.I).2 coordinate_at_I
  have hamul : a = 2 * orderOfVanishingAt
      (ModularForm.E₆ : UpperHalfPlane → ℂ) UpperHalfPlane.I := by
    dsimp [a]
    rw [fiberForm_one_fun,
      orderOfVanishingAt_pow (ModularFormClass.holo ModularForm.E₆)]
    norm_num
  have ha2 : 2 ≤ a := by
    rw [hamul] at hapos ⊢
    omega
  change a = 2
  omega

/-- The inclusion of the open upper half-plane is locally a complex diffeomorphism. -/
theorem coe_isLocalDiffeomorphAt (z : UpperHalfPlane) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
      (fun w : UpperHalfPlane ↦ (w : ℂ)) z := by
  let e := UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : UpperHalfPlane → ℂ)
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) UpperHalfPlane ℂ ⊤ := {
    __ := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      simpa [e] using (UpperHalfPlane.contMDiff_coe (n := ⊤)).contMDiffOn
    contMDiffOn_invFun := by
      intro w hw
      have hw' : w ∈ Set.range ((↑) : UpperHalfPlane → ℂ) := by
        simpa [e] using hw
      obtain ⟨u, rfl⟩ := hw'
      have heq : e.symm =ᶠ[nhds (u : ℂ)] UpperHalfPlane.ofComplex := by
        filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds u.im_pos] with v hv
        apply UpperHalfPlane.coe_injective
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hv]
        exact UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph_right_inv _
          (by simpa [UpperHalfPlane.range_coe] using hv)
      have hmd : CMDiffAt ⊤ e.symm (u : ℂ) :=
        (UpperHalfPlane.contMDiffAt_ofComplex u.im_pos).congr_of_eventuallyEq heq.symm
      simpa using hmd.contMDiffWithinAt
    }
  refine PartialDiffeomorph.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤ Φ ?_
  change z ∈ e.source
  simp [e]

/-- Subtraction of the centre is a local complex coordinate on the upper half-plane. -/
theorem sub_center_isLocalDiffeomorphAt (center : UpperHalfPlane) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
      (fun z : UpperHalfPlane ↦ (z : ℂ) - (center : ℂ)) center := by
  let t : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ℂ ℂ ⊤ := {
    toEquiv := Equiv.vaddConst (-(center : ℂ))
    contMDiff_toFun := by
      rw [Equiv.coe_vaddConst]
      exact contMDiff_id.add contMDiff_const
    contMDiff_invFun := by
      rw [Equiv.coe_vaddConst_symm]
      exact contMDiff_id.sub contMDiff_const
    }
  have ht := t.isLocalDiffeomorph (center : ℂ)
  have h := IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ℂ) ℂ
    (coe_isLocalDiffeomorphAt center) ht
  have heq : (t ∘ (fun z : UpperHalfPlane ↦ (z : ℂ))) =
      (fun z : UpperHalfPlane ↦ (z : ℂ) - (center : ℂ)) := by
    funext z
    change (z : ℂ) +ᵥ (-(center : ℂ)) = (z : ℂ) - (center : ℂ)
    simp [sub_eq_add_neg]
  rwa [heq] at h

/-- A nonzero holomorphic function on `ℍ` has finite complex meromorphic order everywhere. -/
theorem meromorphicOrderAt_comp_ofComplex_ne_top_of_mdiff {f : UpperHalfPlane → ℂ}
    (hf : MDiff f) (hne : f ≠ 0) (z : UpperHalfPlane) :
    meromorphicOrderAt (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ ⊤ := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hne
  refine MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun w hw ↦ (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hf hw).meromorphicAt)
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) τ.im_pos z.im_pos ?_
  have hnf := (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hf τ.im_pos).meromorphicNFAt
  rw [hnf.meromorphicOrderAt_eq_zero_iff.mpr
    (by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ)]
  exact WithTop.zero_ne_top

/-- The fibre form is a nowhere-zero discriminant factor times the coordinate difference. -/
theorem fiberForm_factor_fun (c : ℂ) :
    (fiberForm c : UpperHalfPlane → ℂ) =
      (fun z ↦ 1728 * ModularForm.discriminant z) *
        (fun z ↦ normalizedModularJCoordinate z - c) := by
  funext z
  rw [fiberForm_apply]
  change ModularForm.E₄ z ^ 3 - 1728 * c * ModularForm.discriminant z =
    1728 * ModularForm.discriminant z * (normalizedJ z / 1728 - c)
  rw [normalizedJ]
  have hΔ := ModularForm.discriminant_ne_zero z
  field_simp [hΔ]

/-- The fibre over zero has exact order three at the translated elliptic point. -/
theorem fiberForm_zero_order_three :
    orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ)
      ellipticThreeParameter = 3 := by
  have hper : Function.Periodic
      ((fiberForm 0 : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (fiberForm 0)
      one_mem_strictPeriods_SL
  have h := orderOfVanishingAt_eq_of_coe_eq_add hper
    (z := UpperHalfPlane.ρ) (w := ellipticThreeParameter) (by rfl)
  exact h.trans fiberForm_zero_order_rho

/-- The normalized coordinate difference has exact order three at its order-three point. -/
theorem coordinate_order_three :
    orderOfVanishingAt (fun z ↦ normalizedModularJCoordinate z - 0)
      ellipticThreeParameter = 3 := by
  let A : UpperHalfPlane → ℂ := fun z ↦ 1728 * ModularForm.discriminant z
  let J₀ : UpperHalfPlane → ℂ := fun z ↦ normalizedModularJCoordinate z - 0
  have hA : MDiff A := by
    dsimp [A]
    exact mdifferentiable_const.mul
      (by simpa [CuspForm.coe_discriminant] using
        (CuspFormClass.holo CuspForm.discriminant))
  have hJ : MDiff J₀ := by
    exact normalizedModularJCoordinate_holomorphic.sub mdifferentiable_const
  have hAne : A ≠ 0 := by
    intro h
    have hne : A UpperHalfPlane.I ≠ 0 :=
      mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero _)
    exact hne (by simpa using congrFun h UpperHalfPlane.I)
  have hJne : J₀ ≠ 0 := by
    intro h
    have hz := congrFun h UpperHalfPlane.I
    norm_num [J₀, coordinate_at_I] at hz
  have hA0 : orderOfVanishingAt A ellipticThreeParameter = 0 := by
    apply orderOfVanishingAt_eq_zero_of_ne_zero
      (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hA
        ellipticThreeParameter.im_pos).meromorphicNFAt
    exact mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero _)
  have hmul := orderOfVanishingAt_mul hA hJ hAne hJne ellipticThreeParameter
  have hfactor : (fiberForm 0 : UpperHalfPlane → ℂ) = A * J₀ := by
    simpa [A, J₀] using fiberForm_factor_fun 0
  rw [← hfactor, fiberForm_zero_order_three, hA0] at hmul
  change orderOfVanishingAt J₀ ellipticThreeParameter = 3
  omega

/-- The normalized coordinate difference has exact order two at `i`. -/
theorem coordinate_order_two :
    orderOfVanishingAt (fun z ↦ normalizedModularJCoordinate z - 1)
      UpperHalfPlane.I = 2 := by
  let A : UpperHalfPlane → ℂ := fun z ↦ 1728 * ModularForm.discriminant z
  let J₁ : UpperHalfPlane → ℂ := fun z ↦ normalizedModularJCoordinate z - 1
  have hA : MDiff A := by
    dsimp [A]
    exact mdifferentiable_const.mul
      (by simpa [CuspForm.coe_discriminant] using
        (CuspFormClass.holo CuspForm.discriminant))
  have hJ : MDiff J₁ :=
    normalizedModularJCoordinate_holomorphic.sub mdifferentiable_const
  have hAne : A ≠ 0 := by
    intro h
    have hne : A UpperHalfPlane.I ≠ 0 :=
      mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero _)
    exact hne (by simpa using congrFun h UpperHalfPlane.I)
  have hJne : J₁ ≠ 0 := by
    intro h
    have hz := congrFun h UpperHalfPlane.ρ
    norm_num [J₁, coordinate_at_rho] at hz
  have hA0 : orderOfVanishingAt A UpperHalfPlane.I = 0 := by
    have hnf :=
      (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hA UpperHalfPlane.I.im_pos).meromorphicNFAt
    apply orderOfVanishingAt_eq_zero_of_ne_zero hnf
    exact mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero _)
  have hmul := orderOfVanishingAt_mul hA hJ hAne hJne UpperHalfPlane.I
  have hfactor : (fiberForm 1 : UpperHalfPlane → ℂ) = A * J₁ := by
    simpa [A, J₁] using fiberForm_factor_fun 1
  rw [← hfactor, fiberForm_one_order_I, hA0] at hmul
  change orderOfVanishingAt J₁ UpperHalfPlane.I = 2
  omega

/-- A finite exact TauCeti vanishing order packages the project's explicit local branch
factorization contract. -/
noncomputable def hasExactHolomorphicBranchAt_of_order
    {f : UpperHalfPlane → ℂ} (hf : MDiff f) (center : UpperHalfPlane)
    (value : ℂ) (order : ℕ) (horderPos : 0 < order)
    (hne : (fun z ↦ f z - value) ≠ 0)
    (horder : orderOfVanishingAt (fun z ↦ f z - value) center = order) :
    HasExactHolomorphicBranchAt f center value order := by
  let F : UpperHalfPlane → ℂ := fun z ↦ f z - value
  let A : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex
  have hF : MDiff F := hf.sub mdifferentiable_const
  have hA : AnalyticAt ℂ A (center : ℂ) :=
    TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hF center.im_pos
  have htop : meromorphicOrderAt A (center : ℂ) ≠ ⊤ := by
    exact meromorphicOrderAt_comp_ofComplex_ne_top_of_mdiff hF (by simpa [F] using hne) center
  have hmer : meromorphicOrderAt A (center : ℂ) = (order : ℤ) := by
    calc
      meromorphicOrderAt A (center : ℂ) =
          ((meromorphicOrderAt A (center : ℂ)).untop₀ : WithTop ℤ) :=
        (WithTop.coe_untop₀_of_ne_top htop).symm
      _ = (order : ℤ) := by
        have hc := congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) horder
        simpa [F, A, orderOfVanishingAt_def] using hc
  have hanaOrder : analyticOrderAt A (center : ℂ) = (order : ℕ∞) := by
    have hmapped := hA.meromorphicOrderAt_eq
    rw [hmer] at hmapped
    cases haord : analyticOrderAt A (center : ℂ) with
    | top =>
        rw [haord, ENat.map_top] at hmapped
        exact (WithTop.coe_ne_top hmapped).elim
    | coe n =>
        rw [haord, ENat.map_natCast] at hmapped
        have hn : n = order := by exact_mod_cast WithTop.coe_eq_coe.mp hmapped.symm
        simpa [haord, hn]
  have hex := hA.analyticOrderAt_eq_natCast.mp hanaOrder
  let g : ℂ → ℂ := Classical.choose hex
  have hg : AnalyticAt ℂ g (center : ℂ) := (Classical.choose_spec hex).1
  have hg0 : g (center : ℂ) ≠ 0 := (Classical.choose_spec hex).2.1
  have hfactor : ∀ᶠ z in nhds (center : ℂ),
      A z = (z - (center : ℂ)) ^ order • g z := (Classical.choose_spec hex).2.2
  refine {
    order_pos := horderPos
    uniformizer := fun z ↦ (z : ℂ) - (center : ℂ)
    uniformizer_center := by simp
    uniformizer_isLocalDiffeomorph := sub_center_isLocalDiffeomorphAt center
    unit := fun z ↦ g (z : ℂ)
    unit_holomorphic := ?_
    unit_ne_zero := hg0
    factorization := ?_
  }
  · exact MDifferentiableAt.comp center hg.differentiableAt.mdifferentiableAt
      center.mdifferentiable_coe
  · have hpull : ∀ᶠ z : UpperHalfPlane in nhds center,
        A (z : ℂ) = ((z : ℂ) - (center : ℂ)) ^ order * g (z : ℂ) :=
      (UpperHalfPlane.continuous_coe.tendsto center).eventually hfactor
    filter_upwards [hpull] with z hz
    have hof : UpperHalfPlane.ofComplex (z : ℂ) = z := UpperHalfPlane.ofComplex_apply z
    simpa [A, F, Function.comp_apply, hof] using hz

/-- Exact order-three branch structure at the first elliptic point. -/
noncomputable def coordinate_branch_three :
    HasExactHolomorphicBranchAt normalizedModularJCoordinate
      ellipticThreeParameter 0 3 :=
  hasExactHolomorphicBranchAt_of_order normalizedModularJCoordinate_holomorphic
    ellipticThreeParameter 0 3 (by norm_num) (by
      intro h
      have hi := congrFun h UpperHalfPlane.I
      norm_num [coordinate_at_I] at hi) coordinate_order_three

/-- Exact order-two branch structure at `i`. -/
noncomputable def coordinate_branch_two :
    HasExactHolomorphicBranchAt normalizedModularJCoordinate UpperHalfPlane.I 1 2 :=
  hasExactHolomorphicBranchAt_of_order normalizedModularJCoordinate_holomorphic
    UpperHalfPlane.I 1 2 (by norm_num) (by
      intro h
      have hρ := congrFun h UpperHalfPlane.ρ
      norm_num [coordinate_at_rho] at hρ) coordinate_order_two

/-- The normalized modular coordinate is an open map. -/
theorem coordinate_isOpenMap : IsOpenMap normalizedModularJCoordinate := by
  let g : ℂ → ℂ := normalizedModularJCoordinate ∘ UpperHalfPlane.ofComplex
  have hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.im} := by
    intro z hz
    exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic hz
  have hnonconst : ¬ ∃ w, ∀ z ∈ ({z : ℂ | 0 < z.im} : Set ℂ), g z = w := by
    rintro ⟨w, hw⟩
    have hI := hw (UpperHalfPlane.I : ℂ) UpperHalfPlane.I.im_pos
    have hρ := hw (UpperHalfPlane.ρ : ℂ) UpperHalfPlane.ρ.im_pos
    have heq : normalizedModularJCoordinate UpperHalfPlane.I =
        normalizedModularJCoordinate UpperHalfPlane.ρ := by
      calc
        normalizedModularJCoordinate UpperHalfPlane.I = g (UpperHalfPlane.I : ℂ) := by
          change normalizedModularJCoordinate UpperHalfPlane.I =
            normalizedModularJCoordinate (UpperHalfPlane.ofComplex (UpperHalfPlane.I : ℂ))
          rw [UpperHalfPlane.ofComplex_apply]
        _ = w := hI
        _ = g (UpperHalfPlane.ρ : ℂ) := hρ.symm
        _ = normalizedModularJCoordinate UpperHalfPlane.ρ := by
          change normalizedModularJCoordinate
              (UpperHalfPlane.ofComplex (UpperHalfPlane.ρ : ℂ)) =
            normalizedModularJCoordinate UpperHalfPlane.ρ
          rw [UpperHalfPlane.ofComplex_apply]
    rw [coordinate_at_I, coordinate_at_rho] at heq
    exact one_ne_zero heq
  have hopen := (hg.is_constant_or_isOpen
    (convex_halfSpace_im_gt 0).isPreconnected).resolve_left hnonconst
  intro s hs
  have hsopen : IsOpen (((↑) : UpperHalfPlane → ℂ) '' s) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs
  have hsub : ((↑) : UpperHalfPlane → ℂ) '' s ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨z, -, rfl⟩
    exact z.im_pos
  have himg := hopen _ hsub hsopen
  convert himg using 1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(z : ℂ), ⟨⟨z, hz, rfl⟩, by
      change normalizedModularJCoordinate (UpperHalfPlane.ofComplex (z : ℂ)) =
        normalizedModularJCoordinate z
      rw [UpperHalfPlane.ofComplex_apply]⟩⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by
      change normalizedModularJCoordinate z =
        normalizedModularJCoordinate (UpperHalfPlane.ofComplex (z : ℂ))
      rw [UpperHalfPlane.ofComplex_apply]⟩

/-- Away from the value one, the fibre form does not vanish at `i`. -/
theorem fiberForm_order_I_eq_zero_of_ne_one {c : ℂ} (hc : c ≠ 1) :
    orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ) UpperHalfPlane.I = 0 := by
  have hn := orderOfVanishingAt_nonneg (fiberForm_holomorphic c) UpperHalfPlane.I
  have hp : ¬ 0 < orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ)
      UpperHalfPlane.I := by
    rw [fiberForm_order_pos_iff, coordinate_at_I]
    exact fun h ↦ hc h.symm
  omega

/-- Away from the value zero, the fibre form does not vanish at `ρ`. -/
theorem fiberForm_order_rho_eq_zero_of_ne_zero {c : ℂ} (hc : c ≠ 0) :
    orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ) UpperHalfPlane.ρ = 0 := by
  have hn := orderOfVanishingAt_nonneg (fiberForm_holomorphic c) UpperHalfPlane.ρ
  have hp : ¬ 0 < orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ)
      UpperHalfPlane.ρ := by
    rw [fiberForm_order_pos_iff, coordinate_at_rho]
    exact fun h ↦ hc h.symm
  omega

/-- A generic fibre has total non-elliptic orbit multiplicity one. -/
theorem fiberForm_nonEllipticSum_eq_one {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
      TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm c) q.val : ℤ) = 1 := by
  have h := fiberForm_valence c
  rw [fiberForm_order_I_eq_zero_of_ne_one hc1,
    fiberForm_order_rho_eq_zero_of_ne_zero hc0] at h
  norm_num at h
  exact_mod_cast h

/-- Every generic value is attained by the normalized modular coordinate. -/
theorem exists_coordinate_eq_of_ne_zero_one {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∃ z : UpperHalfPlane, normalizedModularJCoordinate z = c := by
  let ord : TauCeti.ModularForm.NonEllipticOrbit → ℤ := fun q ↦
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm c) q.val
  have hsum : ∑ᶠ q, ord q = 1 := by
    simpa [ord] using fiberForm_nonEllipticSum_eq_one hc0 hc1
  have hex : ∃ q, 0 < ord q := by
    by_contra h
    push_neg at h
    have hz : ∀ q, ord q = 0 := by
      intro q
      have hn : 0 ≤ ord q := by simpa [ord] using fiberForm_orbitOrder_nonneg c q
      exact le_antisymm (h q) hn
    rw [finsum_eq_zero_of_forall_eq_zero hz] at hsum
    omega
  obtain ⟨q, hq⟩ := hex
  let z : UpperHalfPlane := Quotient.out q.val
  have hmk : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      q.val := Quotient.out_eq q.val
  have hzord : 0 < orderOfVanishingAt (fiberForm c : UpperHalfPlane → ℂ) z := by
    rw [← TauCeti.ModularForm.orderOfVanishingOnOrbit_mk (fiberForm c) z, hmk]
    exact hq
  exact ⟨z, (fiberForm_order_pos_iff c z).mp hzord⟩

/-- The normalized modular coordinate is surjective. -/
theorem coordinate_surjective : Function.Surjective normalizedModularJCoordinate := by
  intro c
  by_cases hc0 : c = 0
  · exact ⟨ellipticThreeParameter, by simpa [hc0] using
      coordinate_at_ellipticThreeParameter⟩
  by_cases hc1 : c = 1
  · exact ⟨UpperHalfPlane.I, by simpa [hc1] using coordinate_at_I⟩
  exact exists_coordinate_eq_of_ne_zero_one hc0 hc1

/-- The normalized modular coordinate realizes the quotient topology. -/
theorem coordinate_isQuotientMap :
    Topology.IsQuotientMap normalizedModularJCoordinate :=
  coordinate_isOpenMap.isQuotientMap normalizedModularJCoordinate_holomorphic.continuous
    coordinate_surjective

/-- The normalized coordinate is constant on an equality of modular orbits. -/
theorem coordinate_eq_of_orbitQuotient_eq {z w : UpperHalfPlane}
    (h : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      Quotient.mk'' w) :
    normalizedModularJCoordinate z = normalizedModularJCoordinate w := by
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), g • w = z := Quotient.exact' h
  rw [← hg]
  exact normalizedModularJCoordinate_invariant g w

/-- Two points in a generic fibre belong to the same modular orbit. -/
theorem generic_fiber_orbit_eq {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {z w : UpperHalfPlane} (hz : normalizedModularJCoordinate z = c)
    (hw : normalizedModularJCoordinate w = c) :
    (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      Quotient.mk'' w := by
  classical
  let qz : TauCeti.ModularForm.NonEllipticOrbit := ⟨Quotient.mk'' z, by
    constructor
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hz, coordinate_at_I] at heq
      exact hc1 heq
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hz, coordinate_at_rho] at heq
      exact hc0 heq⟩
  let qw : TauCeti.ModularForm.NonEllipticOrbit := ⟨Quotient.mk'' w, by
    constructor
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hw, coordinate_at_I] at heq
      exact hc1 heq
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hw, coordinate_at_rho] at heq
      exact hc0 heq⟩
  let ord : TauCeti.ModularForm.NonEllipticOrbit → ℤ := fun q ↦
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm c) q.val
  have hsum : ∑ᶠ q, ord q = 1 := by
    simpa [ord] using fiberForm_nonEllipticSum_eq_one hc0 hc1
  have hzord : 0 < ord qz := by
    simpa [ord, qz] using (fiberForm_order_pos_iff c z).2 hz
  have hword : 0 < ord qw := by
    simpa [ord, qw] using (fiberForm_order_pos_iff c w).2 hw
  have hfin : Function.HasFiniteSupport ord := by
    simpa [ord] using
      (TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic
        (fiberForm c))
  change (Function.support ord).Finite at hfin
  have hzmem : qz ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simpa [Function.mem_support] using hzord.ne'
  have hwmem : qw ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simpa [Function.mem_support] using hword.ne'
  by_contra hne
  have hqne : qz ≠ qw := fun h ↦ hne (congrArg Subtype.val h)
  let pair : Finset TauCeti.ModularForm.NonEllipticOrbit := {qz, qw}
  have hpair : ord qz + ord qw ≤ ∑ q ∈ hfin.toFinset, ord q := by
    calc
      ord qz + ord qw = ∑ q ∈ pair, ord q := by simp [pair, hqne]
      _ ≤ ∑ q ∈ hfin.toFinset, ord q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact hzmem
          · exact hwmem
        · intro q hq _hqnot
          exact fiberForm_orbitOrder_nonneg c q
  rw [finsum_eq_sum ord hfin] at hsum
  omega

/-- At value zero the non-elliptic part of the valence sum vanishes. -/
theorem fiberForm_zero_nonEllipticSum_eq_zero :
    (∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
      TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 0) q.val : ℤ) = 0 := by
  let S : ℤ := ∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 0) q.val
  let a : ℤ := orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ) UpperHalfPlane.I
  let b : ℤ := orderOfVanishingAt (fiberForm 0 : UpperHalfPlane → ℂ) UpperHalfPlane.ρ
  have hval := fiberForm_valence 0
  have hval' : 6 * S + 3 * a + 2 * b = 6 := by
    have hc : (((6 * S + 3 * a + 2 * b : ℤ) : ℂ)) = 6 := by
      push_cast
      dsimp [S, a, b]
      linear_combination 6 * hval
    exact_mod_cast hc
  have hS : 0 ≤ S := finsum_nonneg (fiberForm_orbitOrder_nonneg 0)
  have ha : 0 ≤ a := orderOfVanishingAt_nonneg (fiberForm_holomorphic 0) _
  have hb : b = 3 := fiberForm_zero_order_rho
  change S = 0
  omega

/-- At value one the non-elliptic part of the valence sum vanishes. -/
theorem fiberForm_one_nonEllipticSum_eq_zero :
    (∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
      TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 1) q.val : ℤ) = 0 := by
  let S : ℤ := ∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit,
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 1) q.val
  let a : ℤ := orderOfVanishingAt (fiberForm 1 : UpperHalfPlane → ℂ) UpperHalfPlane.I
  let b : ℤ := orderOfVanishingAt (fiberForm 1 : UpperHalfPlane → ℂ) UpperHalfPlane.ρ
  have hval := fiberForm_valence 1
  have hval' : 6 * S + 3 * a + 2 * b = 6 := by
    have hc : (((6 * S + 3 * a + 2 * b : ℤ) : ℂ)) = 6 := by
      push_cast
      dsimp [S, a, b]
      linear_combination 6 * hval
    exact_mod_cast hc
  have hS : 0 ≤ S := finsum_nonneg (fiberForm_orbitOrder_nonneg 1)
  have hb : 0 ≤ b := orderOfVanishingAt_nonneg (fiberForm_holomorphic 1) _
  have ha : a = 2 := fiberForm_one_order_I
  change S = 0
  omega

/-- Every point above zero is in the order-three elliptic orbit. -/
theorem zero_fiber_orbit_rho {z : UpperHalfPlane}
    (hz : normalizedModularJCoordinate z = 0) :
    (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      Quotient.mk'' UpperHalfPlane.ρ := by
  by_contra hzρ
  let qz : TauCeti.ModularForm.NonEllipticOrbit := ⟨Quotient.mk'' z, by
    constructor
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hz, coordinate_at_I] at heq
      exact zero_ne_one heq
    · exact hzρ⟩
  let ord : TauCeti.ModularForm.NonEllipticOrbit → ℤ := fun q ↦
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 0) q.val
  have hpos : 0 < ord qz := by
    simpa [ord, qz] using (fiberForm_order_pos_iff 0 z).2 hz
  have hfin : Function.HasFiniteSupport ord := by
    simpa [ord] using
      (TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic
        (fiberForm 0))
  have hle : ord qz ≤ ∑ᶠ q, ord q :=
    single_le_finsum qz hfin (fun q ↦ by
      simpa [ord] using fiberForm_orbitOrder_nonneg 0 q)
  have hsum : ∑ᶠ q, ord q = 0 := by
    simpa [ord] using fiberForm_zero_nonEllipticSum_eq_zero
  rw [hsum] at hle
  omega

/-- Every point above one is in the order-two elliptic orbit. -/
theorem one_fiber_orbit_I {z : UpperHalfPlane}
    (hz : normalizedModularJCoordinate z = 1) :
    (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      Quotient.mk'' UpperHalfPlane.I := by
  by_contra hzI
  let qz : TauCeti.ModularForm.NonEllipticOrbit := ⟨Quotient.mk'' z, by
    constructor
    · exact hzI
    · intro h
      have heq := coordinate_eq_of_orbitQuotient_eq h
      rw [hz, coordinate_at_rho] at heq
      exact one_ne_zero heq⟩
  let ord : TauCeti.ModularForm.NonEllipticOrbit → ℤ := fun q ↦
    TauCeti.ModularForm.orderOfVanishingOnOrbit (fiberForm 1) q.val
  have hpos : 0 < ord qz := by
    simpa [ord, qz] using (fiberForm_order_pos_iff 1 z).2 hz
  have hfin : Function.HasFiniteSupport ord := by
    simpa [ord] using
      (TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic
        (fiberForm 1))
  have hle : ord qz ≤ ∑ᶠ q, ord q :=
    single_le_finsum qz hfin (fun q ↦ by
      simpa [ord] using fiberForm_orbitOrder_nonneg 1 q)
  have hsum : ∑ᶠ q, ord q = 0 := by
    simpa [ord] using fiberForm_one_nonEllipticSum_eq_zero
  rw [hsum] at hle
  omega

/-- Equality of normalized modular coordinates implies equality of modular orbits. -/
theorem coordinate_eq_imp_orbitQuotient_eq {z w : UpperHalfPlane}
    (h : normalizedModularJCoordinate z = normalizedModularJCoordinate w) :
    (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) UpperHalfPlane) =
      Quotient.mk'' w := by
  let c := normalizedModularJCoordinate z
  have hz : normalizedModularJCoordinate z = c := rfl
  have hw : normalizedModularJCoordinate w = c := h.symm
  by_cases hc0 : c = 0
  · exact (zero_fiber_orbit_rho (hz.trans hc0)).trans
      (zero_fiber_orbit_rho (hw.trans hc0)).symm
  by_cases hc1 : c = 1
  · exact (one_fiber_orbit_I (hz.trans hc1)).trans
      (one_fiber_orbit_I (hw.trans hc1)).symm
  exact generic_fiber_orbit_eq hc0 hc1 hz hw

/-- Fibres of normalized `J` are exactly the level-one modular-group orbits. -/
theorem coordinate_eq_iff_orbit (z w : UpperHalfPlane) :
    normalizedModularJCoordinate z = normalizedModularJCoordinate w ↔
      ∃ g : ModularMatrix, Matrix.SpecialLinearGroup.mapGL ℝ g • z = w := by
  constructor
  · intro h
    have hq := coordinate_eq_imp_orbitQuotient_eq h
    obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), g • w = z := Quotient.exact' hq
    refine ⟨g⁻¹, ?_⟩
    change g⁻¹ • z = w
    rw [← hg, inv_smul_smul]
  · rintro ⟨g, hg⟩
    have hi := normalizedModularJCoordinate_invariant g z
    rw [hg] at hi
    exact hi.symm

/-- Projective modular invariance, descended from `SL(2, ℤ)`. -/
theorem coordinate_invariant_psl (g : PSL(2, ℤ)) (z : UpperHalfPlane) :
    normalizedModularJCoordinate (g • z) = normalizedModularJCoordinate z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  change normalizedModularJCoordinate (a • z) = normalizedModularJCoordinate z
  exact normalizedModularJCoordinate_invariant a z

/-- The same exact-fibre theorem for the faithful projective modular action. -/
theorem coordinate_eq_iff_pslOrbit {z w : UpperHalfPlane} :
    normalizedModularJCoordinate z = normalizedModularJCoordinate w ↔
      z ∈ MulAction.orbit PSL(2, ℤ) w := by
  constructor
  · intro h
    have hq := coordinate_eq_imp_orbitQuotient_eq h
    obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), g • w = z := Quotient.exact' hq
    exact MulAction.mem_orbit_iff.mpr ⟨(g : PSL(2, ℤ)), by
      change g • w = z
      exact hg⟩
  · intro h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    rw [← hg]
    exact coordinate_invariant_psl g w

/-- Away from the two elliptic values, the faithful projective action has trivial stabilizer. -/
theorem psl_stabilizer_eq_bot_of_regular {z : UpperHalfPlane}
    (h0 : normalizedModularJCoordinate z ≠ 0)
    (h1 : normalizedModularJCoordinate z ≠ 1) :
    MulAction.stabilizer PSL(2, ℤ) z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  have hfix := MulAction.mem_stabilizer_iff.mp hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change ((a : PSL(2, ℤ)) : PSL(2, ℤ)) = 1
  change a • z = z at hfix
  obtain ⟨g, hgfd⟩ := ModularGroup.exists_smul_mem_fd z
  let p : UpperHalfPlane := g • z
  have hpfd : p ∈ ModularGroup.fd := hgfd
  have hpJ : normalizedModularJCoordinate p = normalizedModularJCoordinate z := by
    exact normalizedModularJCoordinate_invariant g z
  have hpI : p ≠ UpperHalfPlane.I := by
    intro hp
    apply h1
    calc
      normalizedModularJCoordinate z = normalizedModularJCoordinate p := hpJ.symm
      _ = 1 := by rw [hp, coordinate_at_I]
  have hpρ : p ≠ UpperHalfPlane.ρ := by
    intro hp
    apply h0
    calc
      normalizedModularJCoordinate z = normalizedModularJCoordinate p := hpJ.symm
      _ = 0 := by rw [hp, coordinate_at_rho]
  have hvadd : (1 : ℝ) +ᵥ UpperHalfPlane.ρ = ellipticThreeParameter := by
    apply UpperHalfPlane.coe_injective
    change (1 : ℂ) + (UpperHalfPlane.ρ : ℂ) = (UpperHalfPlane.ρ : ℂ) + 1
    ring
  have hpρ' : p ≠ (1 : ℝ) +ᵥ UpperHalfPlane.ρ := by
    intro hp
    apply h0
    calc
      normalizedModularJCoordinate z = normalizedModularJCoordinate p := hpJ.symm
      _ = 0 := by rw [hp, hvadd, coordinate_at_ellipticThreeParameter]
  let b : SL(2, ℤ) := g * a * g⁻¹
  have hbfix : b • p = p := by
    dsimp [b, p]
    calc
      (g * a * g⁻¹) • (g • z) = g • (a • (g⁻¹ • (g • z))) := by
        rw [mul_smul, mul_smul]
      _ = g • (a • z) := by rw [inv_smul_smul]
      _ = g • z := by rw [hfix]
  have hb := ModularGroup.stabilizer_of_ne hpfd hbfix hpI hpρ hpρ'
  dsimp [b] at hb
  rcases hb with hb | hb
  · have ha : a = 1 := by
      calc
        a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hb]
        _ = 1 := by group
    simp [ha]
  · have ha : a = -1 := by
      calc
        a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * (-1) * g := by rw [hb]
        _ = -1 := by simp
    rw [ha]
    exact (QuotientGroup.eq_one_iff (-1 : SL(2, ℤ))).2
      (Subgroup.mem_center_iff.mpr fun x ↦ by rw [neg_one_mul, mul_neg_one])

/-- Away from `0` and `1`, normalized `J` is an ordinary covering map. -/
theorem coordinate_regular_covering :
    IsCoveringMapOn normalizedModularJCoordinate ({0, 1} : Set ℂ)ᶜ := by
  have hcover : IsCoveringMapOn normalizedModularJCoordinate
      (normalizedModularJCoordinate ''
        {z | MulAction.stabilizer PSL(2, ℤ) z = ⊥}) :=
    coordinate_isQuotientMap.isCoveringMapOn_of_properlyDiscontinuousSMul
      (@coordinate_eq_iff_pslOrbit)
  apply hcover.mono
  intro c hc
  obtain ⟨z, rfl⟩ := coordinate_surjective c
  have hne : normalizedModularJCoordinate z ≠ 0 ∧
      normalizedModularJCoordinate z ≠ 1 := by
    simpa using hc
  exact ⟨z, psl_stabilizer_eq_bot_of_regular hne.1 hne.2, rfl⟩

/-- The constant term of the weight-four Eisenstein series is one. -/
theorem E₄_cuspFunction_zero : UpperHalfPlane.cuspFunction 1
    (ModularForm.E₄ : UpperHalfPlane → ℂ) 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)
  simpa [UpperHalfPlane.qExpansion_coeff] using h

/-- The holomorphic factor left after removing the leading `q` from the discriminant. -/
noncomputable def discriminantCuspUnit (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

/-- The unit in the reciprocal normalized-`J` cusp factorization. -/
noncomputable def normalizedModularJCuspUnit (q : ℂ) : ℂ :=
  1728 * discriminantCuspUnit q /
    UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) q ^ 3

theorem reciprocal_factorization_of_E₄_cusp_ne_zero (z : UpperHalfPlane)
    (hq : modularCuspQ z ∈ Metric.ball (0 : ℂ) 1)
    (hE : UpperHalfPlane.cuspFunction 1
      (ModularForm.E₄ : UpperHalfPlane → ℂ) (modularCuspQ z) ≠ 0) :
    (normalizedModularJCoordinate z)⁻¹ =
      modularCuspQ z * normalizedModularJCuspUnit (modularCuspQ z) := by
  have hEq := SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ z
    one_mem_strictPeriods_SL one_ne_zero
  have hEq' : UpperHalfPlane.cuspFunction 1
      (ModularForm.E₄ : UpperHalfPlane → ℂ) (modularCuspQ z) = ModularForm.E₄ z := by
    simpa [modularCuspQ] using hEq
  have hE' : ModularForm.E₄ z ≠ 0 := by rwa [hEq'] at hE
  have hq0 : modularCuspQ z ≠ 0 :=
    Function.Periodic.qParam_ne_zero (z : ℂ)
  have hΔ := ModularForm.discriminant_cuspFunction_eqOn hq
  have hΔEq := SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant z
    one_mem_strictPeriods_SL one_ne_zero
  have hΔEq' : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant
      (modularCuspQ z) = ModularForm.discriminant z := by
    simpa [modularCuspQ] using hΔEq
  have hprod : discriminantCuspUnit (modularCuspQ z) ≠ 0 := by
    intro hp
    apply ModularForm.discriminant_ne_zero z
    rw [← hΔEq', hΔ]
    exact mul_eq_zero.mpr (Or.inr (by simpa [discriminantCuspUnit] using hp))
  rw [normalizedModularJCoordinate, normalizedJ, ← hEq', ← hΔEq', hΔ]
  simp only [normalizedModularJCuspUnit, discriminantCuspUnit]
  field_simp [hE, hq0, hprod]

/-- The normalized modular quotient has its standard simple completed cusp. -/
noncomputable def exact_normalizedModularJ_cusp : HasExactNormalizedModularJCusp := by
  have hE₄diff : DifferentiableAt ℂ
      (UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) 0 :=
    ModularFormClass.differentiableAt_cuspFunction ModularForm.E₄ one_pos
      one_mem_strictPeriods_SL (by norm_num)
  have hE₄nhds : ∀ᶠ q in nhds (0 : ℂ),
      UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) q ≠ 0 :=
    hE₄diff.continuousAt.eventually_ne
      (show UpperHalfPlane.cuspFunction 1
        (ModularForm.E₄ : UpperHalfPlane → ℂ) 0 ≠ (0 : ℂ) by
          rw [E₄_cuspFunction_zero]
          norm_num)
  let ε : ℝ := Classical.choose (Metric.mem_nhds_iff.mp hE₄nhds)
  have hεspec := Classical.choose_spec (Metric.mem_nhds_iff.mp hE₄nhds)
  have hε : 0 < ε := hεspec.1
  have hεE : Metric.ball (0 : ℂ) ε ⊆
      {q | UpperHalfPlane.cuspFunction 1
        (ModularForm.E₄ : UpperHalfPlane → ℂ) q ≠ 0} := hεspec.2
  let r : ℝ := min ε (1 / 2)
  have hr : 0 < r := lt_min hε (by norm_num)
  have hrε : r ≤ ε := min_le_left _ _
  have hr1 : r < 1 := (min_le_right ε (1 / 2)).trans_lt (by norm_num)
  have hE₄ball : ∀ q ∈ Metric.ball (0 : ℂ) r,
      UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) q ≠ 0 := by
    intro q hq
    exact hεE (Metric.ball_subset_ball hrε hq)
  have hqevent : ∀ᶠ z in UpperHalfPlane.atImInfty,
      modularCuspQ z ∈ Metric.ball (0 : ℂ) r := by
    simpa [modularCuspQ] using
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos).eventually
        (Metric.ball_mem_nhds (0 : ℂ) hr)
  refine
    { cuspUnit := normalizedModularJCuspUnit
      cuspRadius := r
      cuspRadius_pos := hr
      cuspUnit_holomorphic := ?_
      cuspUnit_zero_ne := ?_
      cuspParameter_eventually_mem := ?_
      coordinate_eventually_ne_zero := ?_
      reciprocal_factorization := ?_ }
  · intro q hq
    have hq1 : q ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.ball_subset_ball hr1.le hq
    have hprod : DifferentiableAt ℂ discriminantCuspUnit q := by
      change DifferentiableAt ℂ (fun q ↦ ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) q
      exact (ModularForm.differentiableOn_tprod_one_sub_pow_pow 24 q hq1).differentiableAt
        (Metric.isOpen_ball.mem_nhds hq1)
    have hE : DifferentiableAt ℂ
        (UpperHalfPlane.cuspFunction 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) q :=
      ModularFormClass.differentiableAt_cuspFunction ModularForm.E₄ one_pos
        one_mem_strictPeriods_SL (by simpa using hq1)
    have hnum : DifferentiableAt ℂ (fun x ↦ (1728 : ℂ) * discriminantCuspUnit x) q :=
      (differentiableAt_const (c := (1728 : ℂ))).mul hprod
    exact (hnum.div (hE.pow 3) (pow_ne_zero 3 (hE₄ball q hq))).mdifferentiableAt
  · norm_num [normalizedModularJCuspUnit, discriminantCuspUnit, E₄_cuspFunction_zero]
  · change ∀ᶠ z in UpperHalfPlane.atImInfty,
      modularCuspQ z ∈ Metric.ball (0 : ℂ) r
    exact hqevent
  · change ∀ᶠ z in UpperHalfPlane.atImInfty,
      normalizedModularJCoordinate z ≠ 0
    filter_upwards [hqevent] with z hz
    have hE := hE₄ball (modularCuspQ z) hz
    have hEq := SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ z
      one_mem_strictPeriods_SL one_ne_zero
    have hE' : ModularForm.E₄ z ≠ 0 := by
      rw [← hEq]
      simpa [modularCuspQ] using hE
    exact div_ne_zero
      (div_ne_zero (pow_ne_zero 3 hE') (ModularForm.discriminant_ne_zero z)) (by norm_num)
  · change ∀ᶠ z in UpperHalfPlane.atImInfty,
      (normalizedModularJCoordinate z)⁻¹ =
        modularCuspQ z * normalizedModularJCuspUnit (modularCuspQ z)
    filter_upwards [hqevent] with z hz
    exact reciprocal_factorization_of_E₄_cusp_ne_zero z
      (Metric.ball_subset_ball hr1.le hz) (hE₄ball (modularCuspQ z) hz)

/-- Full exact normalized modular-`J` uniformization, with every field discharged. -/
noncomputable def exactNormalizedModularJUniformization :
    ExactNormalizedModularJUniformization where
  coordinate_isQuotientMap := coordinate_isQuotientMap
  coordinate_eq_iff_orbit := coordinate_eq_iff_orbit
  coordinate_at_three := coordinate_at_ellipticThreeParameter
  coordinate_at_two := coordinate_at_I
  regular_covering := coordinate_regular_covering
  branch_three := coordinate_branch_three
  branch_two := coordinate_branch_two
  cusp := exact_normalizedModularJ_cusp

end SphereSixComplex.Periods.ExactNormalizedModularJTau
