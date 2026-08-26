module

public import SphereSixComplex.Topology.EstablishedStrongDeformationRetracts
public import Mathlib.Analysis.Complex.Basic

/-!
# Radial geometry of punctured affine half-planes

Punctured discs and the punctured half-planes containing them retract through the same radial
normalization.  In particular, the literal disc inclusion is a homotopy equivalence.  This is the
base-space calculation needed by the two affine elliptic sides.
-/

@[expose] public section

noncomputable section

open Set Topology unitInterval
open scoped ContinuousMap

namespace SphereSixComplex

/-- A subset of the complex plane closed under radial interpolation to the circle of radius
`radius`. -/
public structure ComplexRadialDomain (X : Set ℂ) (radius : ℝ) : Prop where
  radius_pos : 0 < radius
  nonzero : ∀ x : X, x.1 ≠ 0
  circle_mem : ∀ z : ℂ, ‖z‖ = radius → z ∈ X
  interpolate_mem : ∀ (t : I) (x : X),
    ((t : ℝ) + (1 - (t : ℝ)) * radius * ‖x.1‖⁻¹) • x.1 ∈ X

namespace ComplexRadialDomain

variable {X Y : Set ℂ} {radius : ℝ}

/-- The positive radial interpolation factor. -/
public theorem interpolateScale_pos
    (D : ComplexRadialDomain X radius) (t : I) (x : X) :
    0 < (t : ℝ) + (1 - (t : ℝ)) * radius * ‖x.1‖⁻¹ := by
  have hnorm : 0 < ‖x.1‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (D.nonzero x))
  by_cases ht : (t : ℝ) = 0
  · simp [ht, D.radius_pos, hnorm]
  · exact add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne t.2.1 (Ne.symm ht))
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) D.radius_pos.le) hnorm.le)

/-- Radial normalization from a radial domain to a smaller radial domain containing the same
normalizing circle. -/
public def normalizeTo
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius) :
    C(Y, X) where
  toFun y := ⟨(radius * ‖y.1‖⁻¹) • y.1, by
    apply small.circle_mem
    have hcoeff : 0 < radius * ‖y.1‖⁻¹ :=
      mul_pos small.radius_pos (inv_pos.mpr (norm_pos_iff.mpr (big.nonzero y)))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoeff,
      mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr (big.nonzero y)).ne', mul_one]⟩
  continuous_toFun := by
    have hy : Continuous (fun y : Y ↦ y.1) := continuous_subtype_val
    exact ((continuous_const.mul (hy.norm.inv₀ (fun y ↦
      (norm_pos_iff.mpr (big.nonzero y)).ne'))).smul hy).subtype_mk _

/-- The literal inclusion between nested radial domains. -/
public def inclusion (hXY : X ⊆ Y) : C(X, Y) where
  toFun x := ⟨x.1, hXY x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Radial interpolation from normalization to the identity. -/
public def radialHomotopyFunction
    (D : ComplexRadialDomain X radius) (p : I × X) : X :=
  ⟨((p.1 : ℝ) + (1 - (p.1 : ℝ)) * radius * ‖p.2.1‖⁻¹) • p.2.1,
    D.interpolate_mem p.1 p.2⟩

public theorem continuous_radialHomotopyFunction
    (D : ComplexRadialDomain X radius) :
    Continuous D.radialHomotopyFunction := by
  apply Continuous.subtype_mk
  have ht : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × X ↦ p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hn : Continuous (fun p : I × X ↦ ‖p.2.1‖⁻¹) :=
    hx.norm.inv₀ (fun p ↦ (norm_pos_iff.mpr (D.nonzero p.2)).ne')
  exact (ht.add (((continuous_const.sub ht).mul continuous_const).mul hn)).smul hx

@[simp]
public theorem radialHomotopyFunction_zero
    (D : ComplexRadialDomain X radius) (x : X) :
    D.radialHomotopyFunction (0, x) = D.normalizeTo D x := by
  apply Subtype.ext
  change ((0 : ℝ) + (1 - (0 : ℝ)) * radius * ‖x.1‖⁻¹) • x.1 =
    (radius * ‖x.1‖⁻¹) • x.1
  congr 1
  ring

@[simp]
public theorem radialHomotopyFunction_one
    (D : ComplexRadialDomain X radius) (x : X) :
    D.radialHomotopyFunction (1, x) = x := by
  apply Subtype.ext
  simp [radialHomotopyFunction]

/-- The normalization-to-identity radial homotopy. -/
public def radialHomotopy (D : ComplexRadialDomain X radius) :
    ContinuousMap.Homotopy (D.normalizeTo D) (ContinuousMap.id X) where
  toFun := D.radialHomotopyFunction
  continuous_toFun := D.continuous_radialHomotopyFunction
  map_zero_left := D.radialHomotopyFunction_zero
  map_one_left := D.radialHomotopyFunction_one

/-- Nested radial domains containing the same normalizing circle are homotopy equivalent through
the literal inclusion. -/
public def homotopyEquivOfSubset
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius)
    (hXY : X ⊆ Y) : Y ≃ₕ X where
  toFun := small.normalizeTo big
  invFun := inclusion hXY
  left_inv := ⟨
    { toFun := big.radialHomotopyFunction
      continuous_toFun := big.continuous_radialHomotopyFunction
      map_zero_left := fun y ↦ by
        apply Subtype.ext
        change ((0 : ℝ) + (1 - (0 : ℝ)) * radius * ‖y.1‖⁻¹) • y.1 =
          (radius * ‖y.1‖⁻¹) • y.1
        congr 1
        ring
      map_one_left := big.radialHomotopyFunction_one }⟩
  right_inv := ⟨
    { toFun := small.radialHomotopyFunction
      continuous_toFun := small.continuous_radialHomotopyFunction
      map_zero_left := fun x ↦ by
        apply Subtype.ext
        change ((0 : ℝ) + (1 - (0 : ℝ)) * radius * ‖x.1‖⁻¹) • x.1 =
          (radius * ‖x.1‖⁻¹) • x.1
        congr 1
        ring
      map_one_left := small.radialHomotopyFunction_one }⟩

/-- The nested-subtype model of a subset is homeomorphic to the original subtype. -/
public def nestedSubtypeHomeomorph (hXY : X ⊆ Y) :
    (Subtype.val ⁻¹' X : Set Y) ≃ₜ X where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hXY x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The radial equivalence records the literal nested-subspace inclusion as its inverse. -/
public theorem isHomotopyEquivalenceInclusionOfSubset
    (small : ComplexRadialDomain X radius) (big : ComplexRadialDomain Y radius)
    (hXY : X ⊆ Y) :
    IsHomotopyEquivalenceInclusion (Subtype.val ⁻¹' X : Set Y) := by
  let e : Y ≃ₕ (Subtype.val ⁻¹' X : Set Y) :=
    (small.homotopyEquivOfSubset big hXY).trans
      (nestedSubtypeHomeomorph hXY).symm.toHomotopyEquiv
  refine ⟨e, ?_⟩
  ext x
  rfl

end ComplexRadialDomain

/-- The punctured disc of radius `r`. -/
public def puncturedComplexDisc (r : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ < r}

/-- The punctured left half-plane containing the origin in its closure. -/
public def puncturedComplexLeftHalfPlane (c : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ z.re < c}

/-- A punctured disc is radial around every smaller positive radius. -/
public theorem puncturedComplexDisc_radial
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    ComplexRadialDomain (puncturedComplexDisc r) s where
  radius_pos := hs
  nonzero x := x.2.1
  circle_mem z hz := ⟨by
    exact fun h ↦ hs.ne' (by simpa [h] using hz.symm), hz.trans_lt hsr⟩
  interpolate_mem t x := by
    have hnorm : 0 < ‖x.1‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.2.1)
    have hscale : 0 < (t : ℝ) + (1 - (t : ℝ)) * s * ‖x.1‖⁻¹ := by
      by_cases ht : (t : ℝ) = 0
      · simp [ht, hs, hnorm]
      · exact add_pos_of_pos_of_nonneg
          (lt_of_le_of_ne t.2.1 (Ne.symm ht))
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) hs.le) hnorm.le)
    constructor
    · exact smul_ne_zero hscale.ne' x.2.1
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      rw [add_mul, mul_assoc, mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr x.2.1).ne',
        mul_one]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      by_cases ht : (t : ℝ) = 1
      · rw [ht]
        simpa using x.2.2
      · have hweight : 0 < 1 - (t : ℝ) :=
          sub_pos.mpr (lt_of_le_of_ne ht1 ht)
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (le_of_lt x.2.2)),
          mul_pos hweight (sub_pos.mpr hsr)]

/-- A punctured left half-plane is radial around every positive circle lying inside it. -/
public theorem puncturedComplexLeftHalfPlane_radial
    {s c : ℝ} (hs : 0 < s) (hsc : s < c) :
    ComplexRadialDomain (puncturedComplexLeftHalfPlane c) s where
  radius_pos := hs
  nonzero x := x.2.1
  circle_mem z hz := ⟨by
    exact fun h ↦ hs.ne' (by simpa [h] using hz.symm),
    (Complex.re_le_norm z).trans_lt (hz.trans_lt hsc)⟩
  interpolate_mem t x := by
    have hnorm : 0 < ‖x.1‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.2.1)
    have hscale : 0 < (t : ℝ) + (1 - (t : ℝ)) * s * ‖x.1‖⁻¹ := by
      by_cases ht : (t : ℝ) = 0
      · simp [ht, hs, hnorm]
      · exact add_pos_of_pos_of_nonneg
          (lt_of_le_of_ne t.2.1 (Ne.symm ht))
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) hs.le) hnorm.le)
    constructor
    · exact smul_ne_zero hscale.ne' x.2.1
    · rw [Complex.smul_re]
      change ((t : ℝ) + (1 - (t : ℝ)) * s * ‖x.1‖⁻¹) * x.1.re < c
      have hnormalized : s * ‖x.1‖⁻¹ * x.1.re ≤ s := by
        have hle := Complex.re_le_norm x.1
        have hfactor : 0 ≤ s * ‖x.1‖⁻¹ :=
          mul_nonneg hs.le hnorm.le
        calc
          s * ‖x.1‖⁻¹ * x.1.re ≤
              s * ‖x.1‖⁻¹ * ‖x.1‖ :=
            mul_le_mul_of_nonneg_left hle hfactor
          _ = s := by
            rw [mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr x.2.1).ne', mul_one]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      by_cases ht : (t : ℝ) = 1
      · rw [ht]
        simpa using x.2.2
      · have hweight : 0 < 1 - (t : ℝ) :=
          sub_pos.mpr (lt_of_le_of_ne ht1 ht)
        have hnormalized_lt : s * ‖x.1‖⁻¹ * x.1.re < c :=
          hnormalized.trans_lt hsc
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (le_of_lt x.2.2)),
          mul_pos hweight (sub_pos.mpr hnormalized_lt)]

/-- The literal inclusion of a sufficiently small punctured disc into the corresponding
punctured left half-plane is a homotopy equivalence. -/
public def puncturedComplexDiscHomotopyEquivLeftHalfPlane
    {s r c : ℝ} (hs : 0 < s) (hsr : s < r) (hrc : r ≤ c) :
    puncturedComplexLeftHalfPlane c ≃ₕ puncturedComplexDisc r :=
  (puncturedComplexDisc_radial hs hsr).homotopyEquivOfSubset
    (puncturedComplexLeftHalfPlane_radial hs (hsr.trans_le hrc))
    (fun z hz ↦ ⟨hz.1, (Complex.re_le_norm z).trans_lt (hz.2.trans_le hrc)⟩)

/-- The punctured disc centered at one. -/
public def puncturedComplexDiscAtOne (r : ℝ) : Set ℂ :=
  {z | z ≠ 1 ∧ ‖z - 1‖ < r}

/-- The punctured right half-plane whose missing point is one. -/
public def puncturedComplexRightHalfPlane (c : ℝ) : Set ℂ :=
  {z | z ≠ 1 ∧ c < z.re}

/-- Reflection about `1 / 2` identifies the right half-plane at one with a left half-plane at
zero. -/
public def puncturedComplexRightHalfPlaneHomeomorphLeft (c : ℝ) :
    puncturedComplexRightHalfPlane c ≃ₜ puncturedComplexLeftHalfPlane (1 - c) where
  toFun z := ⟨1 - z.1, by
    constructor
    · intro h
      apply z.2.1
      exact (sub_eq_zero.mp h).symm
    · change 1 - z.1.re < 1 - c
      linarith [z.2.2]⟩
  invFun z := ⟨1 - z.1, by
    constructor
    · intro h
      apply z.2.1
      exact sub_eq_self.mp h
    · change c < 1 - z.1.re
      linarith [z.2.2]⟩
  left_inv z := by
    apply Subtype.ext
    ring
  right_inv z := by
    apply Subtype.ext
    ring
  continuous_toFun :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- The same reflection identifies discs centered at one with discs centered at zero. -/
public def puncturedComplexDiscAtOneHomeomorphDisc (r : ℝ) :
    puncturedComplexDiscAtOne r ≃ₜ puncturedComplexDisc r where
  toFun z := ⟨1 - z.1, by
    constructor
    · intro h
      apply z.2.1
      exact (sub_eq_zero.mp h).symm
    · convert z.2.2 using 1
      rw [show 1 - z.1 = -(z.1 - 1) by ring, norm_neg]⟩
  invFun z := ⟨1 - z.1, by
    constructor
    · intro h
      apply z.2.1
      exact sub_eq_self.mp h
    · convert z.2.2 using 1
      rw [show 1 - z.1 - 1 = -z.1 by ring, norm_neg]⟩
  left_inv z := by
    apply Subtype.ext
    ring
  right_inv z := by
    apply Subtype.ext
    ring
  continuous_toFun :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- A punctured disc centered at one is homotopy equivalent to the containing punctured right
half-plane, with the inverse induced by its literal inclusion. -/
public def puncturedComplexDiscAtOneHomotopyEquivRightHalfPlane
    {s r c : ℝ} (hs : 0 < s) (hsr : s < r) (hrc : r ≤ 1 - c) :
    puncturedComplexRightHalfPlane c ≃ₕ puncturedComplexDiscAtOne r :=
  (puncturedComplexRightHalfPlaneHomeomorphLeft c).toHomotopyEquiv.trans
    ((puncturedComplexDiscHomotopyEquivLeftHalfPlane hs hsr hrc).trans
      (puncturedComplexDiscAtOneHomeomorphDisc r).symm.toHomotopyEquiv)

end SphereSixComplex
