module

public import SphereSixComplex.TriangleGroup.FuchsianAction
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Reduced words and elliptic stabilizers for the triangle group

This file proves from Mathlib's indexed reduced-word model that every cyclically reduced word
involving two factors has infinite order.  It also classifies the fixed points of the two
distinguished cyclic factors of the explicit Fuchsian action.
-/

open UpperHalfPlane

noncomputable section

namespace SphereSixComplex.TriangleGroup.FreeProductTorsion

open SphereSixComplex.TriangleGroup

namespace ReducedWord

open Monoid.CoprodI

variable {I : Type*} [DecidableEq I]
variable {G : I → Type*} [∀ i, Group (G i)]

/-- Positive concatenation powers of a reduced word whose endpoint factors differ. -/
@[expose] public def cyclicPower {i j : I} (w : NeWord G i j) (hij : j ≠ i) :
    ℕ → NeWord G i j
  | 0 => w
  | n + 1 => NeWord.append (cyclicPower w hij n) hij w

omit [DecidableEq I] in
@[simp]
public theorem cyclicPower_prod {i j : I} (w : NeWord G i j) (hij : j ≠ i) (n : ℕ) :
    (cyclicPower w hij n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [cyclicPower]
  | succ n ih =>
      rw [cyclicPower, NeWord.append_prod, ih]
      simp [pow_succ]

variable [∀ i, DecidableEq (G i)]

public theorem neWord_prod_ne_one {i j : I} (w : NeWord G i j) : w.prod ≠ 1 := by
  intro hw
  have heq : w.toWord = Word.empty := by
    exact (Word.equiv (M := G)).symm.injective (by
      change w.toWord.prod = Word.empty.prod
      simpa [NeWord.prod] using hw)
  have hlist := congrArg Word.toList heq
  exact w.toList_ne_nil (by simpa [NeWord.toWord, Word.empty] using hlist)

/-- A cyclically reduced nonempty word crossing between factors has no positive trivial power. -/
public theorem cyclicallyReduced_pow_ne_one {i j : I} (w : NeWord G i j) (hij : j ≠ i)
    {n : ℕ} (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [← cyclicPower_prod]
  exact neWord_prod_ne_one (cyclicPower w hij k)

/-- A cyclically reduced word involving at least two free-product factors has infinite order. -/
public theorem cyclicallyReduced_not_isOfFinOrder {i j : I} (w : NeWord G i j)
    (hij : j ≠ i) : ¬IsOfFinOrder w.prod := by
  rw [isOfFinOrder_iff_pow_eq_one]
  push Not
  exact fun n hn ↦ cyclicallyReduced_pow_ne_one w hij hn

end ReducedWord

/-- The order-three generator has exactly one fixed point in the upper half-plane. -/
public theorem fuchsianSourceAction_gOne_fixed_iff (z : UpperHalfPlane) :
    fuchsianSourceAction g₁ • z = z ↔ z = fuchsianOneFixedPoint := by
  constructor
  · intro hz
    have hc := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) hz
    change (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) = z at hc
    rw [fuchsianSourceAction_g₁_apply] at hc
    have hmul : (z : ℂ) - 1 = (z : ℂ) * z := (div_eq_iff z.ne_zero).mp hc
    have him := congrArg Complex.im hmul
    have hre := congrArg Complex.re hmul
    have ha : z.re = 1 / 2 := by
      norm_num [Complex.mul_im] at him
      nlinarith [z.im_pos]
    have hb_sq : z.im ^ 2 = 3 / 4 := by
      norm_num [Complex.mul_re, ha] at hre
      nlinarith
    have hb : z.im = Real.sqrt 3 / 2 := by
      have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      have hsqrt_nonneg := Real.sqrt_nonneg 3
      have hroot : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by nlinarith
      nlinarith [z.im_pos]
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simpa [fuchsianOneFixedPoint] using ha
    · simpa [fuchsianOneFixedPoint] using hb
  · rintro rfl
    exact fuchsianOneFixedPoint_fixed

/-- The inverse generator in the order-three factor has the same unique fixed point. -/
public theorem fuchsianSourceAction_gOne_sq_fixed_iff (z : UpperHalfPlane) :
    fuchsianSourceAction (g₁ ^ 2) • z = z ↔ z = fuchsianOneFixedPoint := by
  constructor
  · intro hz
    apply (fuchsianSourceAction_gOne_fixed_iff z).mp
    calc
      fuchsianSourceAction g₁ • z =
          fuchsianSourceAction g₁ • (fuchsianSourceAction (g₁ ^ 2) • z) :=
        congrArg (fun w ↦ fuchsianSourceAction g₁ • w) hz.symm
      _ = (fuchsianSourceAction g₁ * fuchsianSourceAction (g₁ ^ 2)) • z :=
        (mul_smul _ _ _).symm
      _ = fuchsianSourceAction (g₁ * g₁ ^ 2) • z := by rw [map_mul]
      _ = z := by rw [show g₁ * g₁ ^ 2 = g₁ ^ 3 by group, g₁_pow_three, map_one, one_smul]
  · rintro rfl
    rw [map_pow, pow_two, mul_smul]
    rw [fuchsianOneFixedPoint_fixed, fuchsianOneFixedPoint_fixed]

/-- The order-four generator has exactly one fixed point in the upper half-plane. -/
public theorem fuchsianSourceAction_gTwo_fixed_iff (z : UpperHalfPlane) :
    fuchsianSourceAction g₂ • z = z ↔ z = fuchsianTwoFixedPoint := by
  constructor
  · intro hz
    have hc := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) hz
    change (((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) = z at hc
    rw [fuchsianSourceAction_g₂_apply] at hc
    have hden : (z : ℂ) + Real.sqrt 2 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      exact z.im_pos.ne' him
    have hmul : (-1 : ℂ) = (z : ℂ) * (z + Real.sqrt 2) :=
      (div_eq_iff hden).mp hc
    have him := congrArg Complex.im hmul
    have hre := congrArg Complex.re hmul
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have ha : z.re = -Real.sqrt 2 / 2 := by
      norm_num [Complex.mul_im] at him
      nlinarith [z.im_pos]
    have hb_sq : z.im ^ 2 = 1 / 2 := by
      norm_num [Complex.mul_re, ha] at hre
      nlinarith
    have hb : z.im = Real.sqrt 2 / 2 := by
      have hsqrt_nonneg := Real.sqrt_nonneg 2
      have hroot : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by nlinarith
      nlinarith [z.im_pos]
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simpa [fuchsianTwoFixedPoint] using ha
    · simpa [fuchsianTwoFixedPoint] using hb
  · rintro rfl
    exact fuchsianTwoFixedPoint_fixed

public theorem fuchsianSourceAction_gTwo_sq_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₂ ^ 2)) z : UpperHalfPlane) : ℂ) =
      (-(z : ℂ) - Real.sqrt 2) / (Real.sqrt 2 * z + 1) := by
  rw [map_pow, fuchsianSourceAction_g₂]
  rw [show fuchsianTwoPerm ^ 2 = fuchsianSLAction (fuchsianTwoSL ^ 2) by
    exact (map_pow _ _ _).symm]
  rw [fuchsianTwoSL_pow_two]
  change (((fuchsianTwoSquaredGL • z : UpperHalfPlane) : ℂ)) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, fuchsianTwoSquaredGL_matrix]
    ring
  · simp [fuchsianTwoSquaredGL.eq_def]

/-- The involution in the order-four factor has the same unique upper-half-plane fixed point. -/
public theorem fuchsianSourceAction_gTwo_sq_fixed_iff (z : UpperHalfPlane) :
    fuchsianSourceAction (g₂ ^ 2) • z = z ↔ z = fuchsianTwoFixedPoint := by
  constructor
  · intro hz
    have hc := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) hz
    change (((fuchsianSourceAction (g₂ ^ 2)) z : UpperHalfPlane) : ℂ) = z at hc
    rw [fuchsianSourceAction_gTwo_sq_apply] at hc
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hden : Real.sqrt 2 * (z : ℂ) + 1 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num [Complex.mul_im] at him
      nlinarith [z.im_pos]
    have hmul : -(z : ℂ) - Real.sqrt 2 =
        (z : ℂ) * (Real.sqrt 2 * z + 1) := (div_eq_iff hden).mp hc
    have him := congrArg Complex.im hmul
    have hre := congrArg Complex.re hmul
    have ha : z.re = -Real.sqrt 2 / 2 := by
      norm_num [Complex.mul_im] at him
      have hfactor : z.im * (Real.sqrt 2 * z.re + 1) = 0 := by nlinarith
      have hlinear := (mul_eq_zero.mp hfactor).resolve_left z.im_pos.ne'
      nlinarith
    have hb_sq : z.im ^ 2 = 1 / 2 := by
      norm_num [Complex.mul_re, ha] at hre
      nlinarith
    have hb : z.im = Real.sqrt 2 / 2 := by
      have hsqrt_nonneg := Real.sqrt_nonneg 2
      have hroot : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by nlinarith
      nlinarith [z.im_pos]
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simpa [fuchsianTwoFixedPoint] using ha
    · simpa [fuchsianTwoFixedPoint] using hb
  · rintro rfl
    rw [map_pow, pow_two, mul_smul]
    rw [fuchsianTwoFixedPoint_fixed, fuchsianTwoFixedPoint_fixed]

/-- The inverse generator in the order-four factor has the same unique fixed point. -/
public theorem fuchsianSourceAction_gTwo_cube_fixed_iff (z : UpperHalfPlane) :
    fuchsianSourceAction (g₂ ^ 3) • z = z ↔ z = fuchsianTwoFixedPoint := by
  constructor
  · intro hz
    apply (fuchsianSourceAction_gTwo_fixed_iff z).mp
    calc
      fuchsianSourceAction g₂ • z =
          fuchsianSourceAction g₂ • (fuchsianSourceAction (g₂ ^ 3) • z) :=
        congrArg (fun w ↦ fuchsianSourceAction g₂ • w) hz.symm
      _ = (fuchsianSourceAction g₂ * fuchsianSourceAction (g₂ ^ 3)) • z :=
        (mul_smul _ _ _).symm
      _ = fuchsianSourceAction (g₂ * g₂ ^ 3) • z := by rw [map_mul]
      _ = z := by rw [show g₂ * g₂ ^ 3 = g₂ ^ 4 by group, g₂_pow_four, map_one, one_smul]
  · rintro rfl
    rw [map_pow, pow_succ, pow_two, mul_smul, mul_smul]
    rw [fuchsianTwoFixedPoint_fixed, fuchsianTwoFixedPoint_fixed,
      fuchsianTwoFixedPoint_fixed]

/-- Every nonidentity element of the order-three free factor fixes exactly its elliptic point. -/
public theorem fuchsianSourceAction_inl_fixed_iff (a : CyclicThree) (ha : a ≠ 1)
    (z : UpperHalfPlane) :
    fuchsianSourceAction (Monoid.Coprod.inl a) • z = z ↔ z = fuchsianOneFixedPoint := by
  fin_cases a
  · exact (ha rfl).elim
  · change fuchsianSourceAction g₁ • z = z ↔ z = fuchsianOneFixedPoint
    exact fuchsianSourceAction_gOne_fixed_iff z
  · change fuchsianSourceAction
      (Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3))) • z = z ↔
        z = fuchsianOneFixedPoint
    rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ ^ 2 by
      unfold g₁
      rw [pow_two, ← map_mul]
      congr]
    exact fuchsianSourceAction_gOne_sq_fixed_iff z

/-- Every nonidentity element of the order-four free factor fixes exactly its elliptic point. -/
public theorem fuchsianSourceAction_inr_fixed_iff (a : CyclicFour) (ha : a ≠ 1)
    (z : UpperHalfPlane) :
    fuchsianSourceAction (Monoid.Coprod.inr a) • z = z ↔ z = fuchsianTwoFixedPoint := by
  fin_cases a
  · exact (ha rfl).elim
  · change fuchsianSourceAction g₂ • z = z ↔ z = fuchsianTwoFixedPoint
    exact fuchsianSourceAction_gTwo_fixed_iff z
  · change fuchsianSourceAction
      (Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4))) • z = z ↔
        z = fuchsianTwoFixedPoint
    rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ ^ 2 by
      unfold g₂
      rw [pow_two, ← map_mul]
      congr]
    exact fuchsianSourceAction_gTwo_sq_fixed_iff z
  · change fuchsianSourceAction
      (Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4))) • z = z ↔
        z = fuchsianTwoFixedPoint
    rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ ^ 3 by
      unfold g₂
      rw [pow_succ, pow_two, ← map_mul, ← map_mul]
      congr]
    exact fuchsianSourceAction_gTwo_cube_fixed_iff z

/-- A fixed point of a conjugate of the order-three factor lies in the removed elliptic orbit. -/
public theorem fixed_by_conjugate_inl_iff (c : Delta) (a : CyclicThree) (ha : a ≠ 1)
    (z : UpperHalfPlane) :
    fuchsianSourceAction (c * Monoid.Coprod.inl a * c⁻¹) • z = z ↔
      z = fuchsianSourceAction c • fuchsianOneFixedPoint := by
  constructor
  · intro hz
    have hz' := congrArg (fun w ↦ fuchsianSourceAction c⁻¹ • w) hz
    have hfactor : fuchsianSourceAction (Monoid.Coprod.inl a) •
        (fuchsianSourceAction c⁻¹ • z) = fuchsianSourceAction c⁻¹ • z := by
      simpa only [map_mul, map_inv, mul_smul, inv_smul_smul] using hz'
    have horbit := (fuchsianSourceAction_inl_fixed_iff a ha _).mp hfactor
    calc
      z = fuchsianSourceAction c • (fuchsianSourceAction c⁻¹ • z) := by
        rw [map_inv, smul_inv_smul]
      _ = fuchsianSourceAction c • fuchsianOneFixedPoint := congrArg _ horbit
  · rintro rfl
    simp only [map_mul, map_inv, mul_smul, inv_smul_smul]
    rw [(fuchsianSourceAction_inl_fixed_iff a ha _).mpr rfl]

/-- A fixed point of a conjugate of the order-four factor lies in the removed elliptic orbit. -/
public theorem fixed_by_conjugate_inr_iff (c : Delta) (a : CyclicFour) (ha : a ≠ 1)
    (z : UpperHalfPlane) :
    fuchsianSourceAction (c * Monoid.Coprod.inr a * c⁻¹) • z = z ↔
      z = fuchsianSourceAction c • fuchsianTwoFixedPoint := by
  constructor
  · intro hz
    have hz' := congrArg (fun w ↦ fuchsianSourceAction c⁻¹ • w) hz
    have hfactor : fuchsianSourceAction (Monoid.Coprod.inr a) •
        (fuchsianSourceAction c⁻¹ • z) = fuchsianSourceAction c⁻¹ • z := by
      simpa only [map_mul, map_inv, mul_smul, inv_smul_smul] using hz'
    have horbit := (fuchsianSourceAction_inr_fixed_iff a ha _).mp hfactor
    calc
      z = fuchsianSourceAction c • (fuchsianSourceAction c⁻¹ • z) := by
        rw [map_inv, smul_inv_smul]
      _ = fuchsianSourceAction c • fuchsianTwoFixedPoint := congrArg _ horbit
  · rintro rfl
    simp only [map_mul, map_inv, mul_smul, inv_smul_smul]
    rw [(fuchsianSourceAction_inr_fixed_iff a ha _).mpr rfl]

/-- The complement of the two elliptic orbits for the explicit Fuchsian action. -/
@[expose] public def IsFuchsianRegularPoint (z : UpperHalfPlane) : Prop :=
  ∀ g : Delta,
    fuchsianSourceAction g • z ≠ fuchsianOneFixedPoint ∧
      fuchsianSourceAction g • z ≠ fuchsianTwoFixedPoint

public theorem regular_not_fixed_by_conjugate_inl {z : UpperHalfPlane}
    (hz : IsFuchsianRegularPoint z) (c : Delta) (a : CyclicThree) (ha : a ≠ 1) :
    fuchsianSourceAction (c * Monoid.Coprod.inl a * c⁻¹) • z ≠ z := by
  intro hfixed
  have horbit := (fixed_by_conjugate_inl_iff c a ha z).mp hfixed
  exact (hz c⁻¹).1 (by rw [horbit, map_inv, inv_smul_smul])

public theorem regular_not_fixed_by_conjugate_inr {z : UpperHalfPlane}
    (hz : IsFuchsianRegularPoint z) (c : Delta) (a : CyclicFour) (ha : a ≠ 1) :
    fuchsianSourceAction (c * Monoid.Coprod.inr a * c⁻¹) • z ≠ z := by
  intro hfixed
  have horbit := (fixed_by_conjugate_inr_iff c a ha z).mp hfixed
  exact (hz c⁻¹).2 (by rw [horbit, map_inv, inv_smul_smul])

end SphereSixComplex.TriangleGroup.FreeProductTorsion
