module

public import SphereSixComplex.TriangleGroup.FuchsianPingPong
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import all SphereSixComplex.TriangleGroup.FuchsianAction

/-!
# A concrete fundamental triangle and cusp displacement

The reflection triangle for the `(3, 4, ∞)` action is bounded by the vertical geodesics
`Re z = -√2 / 2`, `Re z = 1 / 2`, and the unit semicircle.  This file records that region and
proves the exact displacement estimates for the parabolic product of the two elliptic generators.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

open SphereSixComplex.TriangleGroup
open scoped Pointwise

/-- Width of the parabolic translation obtained from the two elliptic generators. -/
@[expose] public noncomputable def cuspWidth : ℝ := 1 + Real.sqrt 2

public theorem cuspWidth_pos : 0 < cuspWidth := by
  unfold cuspWidth
  positivity

/-- The closed reflection triangle with elliptic vertices of orders three and four and ideal
vertex at infinity. -/
@[expose] public noncomputable def fundamentalTriangle : Set UpperHalfPlane :=
  {z | -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 ≤ Complex.normSq (z : ℂ)}

/-- The two finite vertices of the triangle lie on its unit-circle side. -/
public theorem fuchsianOneFixedPoint_mem_fundamentalTriangle :
    fuchsianOneFixedPoint ∈ fundamentalTriangle := by
  change -Real.sqrt 2 / 2 ≤ (1 : ℝ) / 2 ∧
    (1 : ℝ) / 2 ≤ 1 / 2 ∧
      1 ≤ Complex.normSq (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ)
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · linarith
  constructor
  · norm_num
  · norm_num [Complex.normSq_apply]
    nlinarith

public theorem fuchsianTwoFixedPoint_mem_fundamentalTriangle :
    fuchsianTwoFixedPoint ∈ fundamentalTriangle := by
  change -Real.sqrt 2 / 2 ≤ -Real.sqrt 2 / 2 ∧
    -Real.sqrt 2 / 2 ≤ (1 : ℝ) / 2 ∧
      1 ≤ Complex.normSq (⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ : ℂ)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rfl
  constructor
  · linarith
  · norm_num [Complex.normSq_apply]
    nlinarith

public theorem fundamentalTriangle_nonempty : fundamentalTriangle.Nonempty :=
  ⟨fuchsianOneFixedPoint, fuchsianOneFixedPoint_mem_fundamentalTriangle⟩

/-- The unit-circle side is paired with the right vertical side by the inverse order-three
rotation. -/
public theorem gOne_sq_unitCircle_re (z : UpperHalfPlane)
    (hz : Complex.normSq (z : ℂ) = 1) :
    (fuchsianSourceAction (g₁ ^ 2) • z).re = 1 / 2 := by
  have hre := congrArg Complex.re
    (FuchsianPingPong.gOne_sq_apply z)
  rw [Complex.div_re] at hre
  norm_num at hre
  have hnorm : Complex.normSq (1 - (z : ℂ)) = 2 * (1 - z.re) := by
    norm_num [Complex.normSq_apply] at hz ⊢
    nlinarith
  have hne : 1 - z.re ≠ 0 := by
    intro hzero
    have hreOne : z.re = 1 := by linarith
    norm_num [Complex.normSq_apply, hreOne] at hz
    nlinarith [z.im_pos]
  rw [map_pow]
  change ((fuchsianOnePerm ^ 2) z).re = 1 / 2
  rw [hre, hnorm]
  field_simp [hne]

/-- The order-three rotation sends the right vertical side to the unit-circle side. -/
public theorem gOne_rightSide_normSq (z : UpperHalfPlane) (hz : z.re = 1 / 2) :
    Complex.normSq ((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ) = 1 := by
  have happly := fuchsianSourceAction_g₁_apply z
  change Complex.normSq (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) = 1
  rw [happly, Complex.normSq_div]
  have heq : Complex.normSq ((z : ℂ) - 1) = Complex.normSq (z : ℂ) := by
    norm_num [Complex.normSq_apply] at hz ⊢
    nlinarith
  rw [heq]
  exact div_self z.normSq_ne_zero

/-- On the left vertical side, the order-four rotation inverts the squared Euclidean norm. -/
public theorem gTwo_leftSide_normSq (z : UpperHalfPlane)
    (hz : z.re = -Real.sqrt 2 / 2) :
    Complex.normSq ((fuchsianSourceAction g₂ • z : UpperHalfPlane) : ℂ) =
      (Complex.normSq (z : ℂ))⁻¹ := by
  have happly := fuchsianSourceAction_g₂_apply z
  change Complex.normSq (((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) = _
  rw [happly, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one]
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have heq : Complex.normSq ((z : ℂ) + Real.sqrt 2) = Complex.normSq (z : ℂ) := by
    norm_num [Complex.normSq_apply] at hz ⊢
    nlinarith
  rw [heq, one_div]

public theorem gTwo_leftSide_outside_to_inside (z : UpperHalfPlane)
    (hside : z.re = -Real.sqrt 2 / 2) (houtside : 1 ≤ Complex.normSq (z : ℂ)) :
    Complex.normSq ((fuchsianSourceAction g₂ • z : UpperHalfPlane) : ℂ) ≤ 1 := by
  rw [gTwo_leftSide_normSq z hside]
  exact inv_le_one_of_one_le₀ houtside

/-- The product `g₁g₂` is the positive cusp translation. -/
public theorem product_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ) = z + cuspWidth := by
  rw [map_mul, fuchsianSourceAction_g₁, fuchsianSourceAction_g₂]
  unfold cuspWidth
  push_cast
  exact fuchsianProductPerm_apply z

/-- Every positive power of the parabolic product has exact linear displacement. -/
public theorem product_pow_apply (n : ℕ) (z : UpperHalfPlane) :
    (((fuchsianSourceAction ((g₁ * g₂) ^ n)) z : UpperHalfPlane) : ℂ) =
      z + n * cuspWidth := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul]
      change (((fuchsianSourceAction ((g₁ * g₂) ^ n))
        (fuchsianSourceAction (g₁ * g₂) z) : UpperHalfPlane) : ℂ) = _
      rw [ih, product_apply]
      push_cast
      ring

/-- Every positive power of the cusp generator has exact negative linear displacement. -/
public theorem cusp_pow_apply (n : ℕ) (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₀ ^ n)) z : UpperHalfPlane) : ℂ) =
      z - n * cuspWidth := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul]
      change (((fuchsianSourceAction (g₀ ^ n))
        (fuchsianSourceAction g₀ z) : UpperHalfPlane) : ℂ) = _
      rw [ih, fuchsianSourceAction_g₀_apply]
      push_cast
      unfold cuspWidth
      push_cast
      ring

public theorem product_pow_re (n : ℕ) (z : UpperHalfPlane) :
    (fuchsianSourceAction ((g₁ * g₂) ^ n) • z).re = z.re + n * cuspWidth := by
  have h := congrArg Complex.re (product_pow_apply n z)
  simpa using h

public theorem cusp_pow_re (n : ℕ) (z : UpperHalfPlane) :
    (fuchsianSourceAction (g₀ ^ n) • z).re = z.re - n * cuspWidth := by
  have h := congrArg Complex.re (cusp_pow_apply n z)
  simpa using h

/-- Quantitative local-finiteness estimate for positive cusp translates of two real-part-bounded
sets. -/
public theorem product_pow_intersection_index_bound
    {K L : Set UpperHalfPlane} {R : ℝ}
    (hK : ∀ z ∈ K, |z.re| ≤ R) (hL : ∀ z ∈ L, |z.re| ≤ R)
    {n : ℕ} (hn : ((fuchsianSourceAction ((g₁ * g₂) ^ n) • ·) '' K ∩ L).Nonempty) :
    n * cuspWidth ≤ 2 * R := by
  obtain ⟨w, ⟨z, hzK, rfl⟩, hwL⟩ := hn
  have hz := hK z hzK
  have hw := hL _ hwL
  rw [product_pow_re] at hw
  rw [abs_le] at hz hw
  nlinarith

/-- The analogous estimate for negative cusp translates. -/
public theorem cusp_pow_intersection_index_bound
    {K L : Set UpperHalfPlane} {R : ℝ}
    (hK : ∀ z ∈ K, |z.re| ≤ R) (hL : ∀ z ∈ L, |z.re| ≤ R)
    {n : ℕ} (hn : ((fuchsianSourceAction (g₀ ^ n) • ·) '' K ∩ L).Nonempty) :
    n * cuspWidth ≤ 2 * R := by
  obtain ⟨w, ⟨z, hzK, rfl⟩, hwL⟩ := hn
  have hz := hK z hzK
  have hw := hL _ hwL
  rw [cusp_pow_re] at hw
  rw [abs_le] at hz hw
  nlinarith

/-- Positive powers of the parabolic product meet two real-part-bounded sets for only finitely
many exponents. -/
public theorem finite_product_pow_intersections_of_re_bounded
    {K L : Set UpperHalfPlane} {R : ℝ}
    (hK : ∀ z ∈ K, |z.re| ≤ R) (hL : ∀ z ∈ L, |z.re| ≤ R) :
    Set.Finite {n : ℕ |
      ((fuchsianSourceAction ((g₁ * g₂) ^ n) • ·) '' K ∩ L).Nonempty} := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R / cuspWidth)
  apply (Set.finite_le_nat N).subset
  intro n hn
  have hbound := product_pow_intersection_index_bound hK hL hn
  have hnreal : (n : ℝ) ≤ 2 * R / cuspWidth :=
    (le_div_iff₀ cuspWidth_pos).2 (by simpa using hbound)
  exact_mod_cast hnreal.trans hN

/-- Negative cusp powers meet two real-part-bounded sets for only finitely many exponents. -/
public theorem finite_cusp_pow_intersections_of_re_bounded
    {K L : Set UpperHalfPlane} {R : ℝ}
    (hK : ∀ z ∈ K, |z.re| ≤ R) (hL : ∀ z ∈ L, |z.re| ≤ R) :
    Set.Finite {n : ℕ |
      ((fuchsianSourceAction (g₀ ^ n) • ·) '' K ∩ L).Nonempty} := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R / cuspWidth)
  apply (Set.finite_le_nat N).subset
  intro n hn
  have hbound := cusp_pow_intersection_index_bound hK hL hn
  have hnreal : (n : ℝ) ≤ 2 * R / cuspWidth :=
    (le_div_iff₀ cuspWidth_pos).2 (by simpa using hbound)
  exact_mod_cast hnreal.trans hN

/-- Compact sets satisfy the real-part bound needed for positive cusp local finiteness. -/
public theorem finite_product_pow_intersections_of_isCompact
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L) :
    Set.Finite {n : ℕ |
      ((fuchsianSourceAction ((g₁ * g₂) ^ n) • ·) '' K ∩ L).Nonempty} := by
  obtain ⟨A, _, _, hKA⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  obtain ⟨B, _, _, hLB⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hL
  apply finite_product_pow_intersections_of_re_bounded
      (R := max A B)
  · intro z hz
    exact (hKA hz).1.trans (le_max_left _ _)
  · intro z hz
    exact (hLB hz).1.trans (le_max_right _ _)

/-- Compact sets satisfy the real-part bound needed for negative cusp local finiteness. -/
public theorem finite_cusp_pow_intersections_of_isCompact
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L) :
    Set.Finite {n : ℕ |
      ((fuchsianSourceAction (g₀ ^ n) • ·) '' K ∩ L).Nonempty} := by
  obtain ⟨A, _, _, hKA⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  obtain ⟨B, _, _, hLB⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hL
  apply finite_cusp_pow_intersections_of_re_bounded
      (R := max A B)
  · intro z hz
    exact (hKA hz).1.trans (le_max_left _ _)
  · intro z hz
    exact (hLB hz).1.trans (le_max_right _ _)

/-- All integral powers of the parabolic product meet two compact sets for only finitely many
exponents.  This is the compact-set proper-discontinuity criterion for the cusp subgroup. -/
public theorem finite_product_zpow_intersections_of_isCompact
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L) :
    Set.Finite {k : ℤ |
      ((fuchsianSourceAction ((g₁ * g₂) ^ k) • ·) '' K ∩ L).Nonempty} := by
  let positive := {n : ℕ |
    ((fuchsianSourceAction ((g₁ * g₂) ^ n) • ·) '' K ∩ L).Nonempty}
  let negative := {n : ℕ |
    ((fuchsianSourceAction (g₀ ^ n) • ·) '' K ∩ L).Nonempty}
  have hpositive : positive.Finite := finite_product_pow_intersections_of_isCompact hK hL
  have hnegative : negative.Finite := finite_cusp_pow_intersections_of_isCompact hK hL
  apply ((hpositive.image fun n : ℕ ↦ (n : ℤ)).union
    (hnegative.image fun n : ℕ ↦ -(n : ℤ))).subset
  intro k hk
  cases k with
  | ofNat n =>
      left
      refine ⟨n, ?_, rfl⟩
      change
        ((fuchsianSourceAction ((g₁ * g₂) ^ (Int.ofNat n)) • ·) '' K ∩ L).Nonempty at hk
      change ((fuchsianSourceAction ((g₁ * g₂) ^ n) • ·) '' K ∩ L).Nonempty
      have heq : (g₁ * g₂) ^ (Int.ofNat n) = (g₁ * g₂) ^ n := zpow_ofNat _ _
      rw [heq] at hk
      exact hk
  | negSucc n =>
      right
      refine ⟨n + 1, ?_, ?_⟩
      · change ((fuchsianSourceAction (g₀ ^ (n + 1)) • ·) '' K ∩ L).Nonempty
        let translate := fun z : UpperHalfPlane ↦
          fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc n)) • z
        change (translate '' K ∩ L).Nonempty at hk
        have hinv : (g₁ * g₂)⁻¹ = g₀ := by simp [g₀]
        dsimp only [translate] at hk
        rw [zpow_negSucc, ← inv_pow, hinv] at hk
        exact hk
      · rw [Int.negSucc_eq]
        push_cast
        rfl

end SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
