module

public import SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhoodDefs
public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
public import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
public import Mathlib.Analysis.Complex.OpenMapping
import all SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# The classical separated Fuchsian cusp neighbourhood, proved

This module proves the standard horodisc theorem for the explicit `(3, 4, ∞)` Fuchsian source
action, replacing the two established inputs of
`SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood` by theorems.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.FuchsianCuspNeighborhoodProof

open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
open scoped Manifold

/-! ## Arithmetic of the quadratic-integer bottom row -/

/-- Two is not an integer square. -/
public theorem two_ne_sq (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  rcases le_or_gt n 1 with hn | hn
  · rcases le_or_gt (-1) n with hn' | hn' <;> nlinarith
  · nlinarith

public theorem positiveEmbedding_mul_conjugateEmbedding (x : QuadraticInteger) :
    positiveEmbedding x * conjugateEmbedding x = (x.norm : ℝ) := by
  rw [positiveEmbedding_apply, conjugateEmbedding_apply, Zsqrtd.norm_def]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  push_cast
  linear_combination (-(x.im : ℝ) ^ 2) * h2

/-- Injectivity of the distinguished real embedding of `ℤ[√2]`. -/
public theorem positiveEmbedding_injective : Function.Injective positiveEmbedding := by
  intro x y hxy
  have h : positiveEmbedding (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero : x - y = 0 := by
    by_contra hne
    have hcone : (0 : ℝ) < |positiveEmbedding (x - y)| * |conjugateEmbedding (x - y)| := by
      rw [← abs_mul, positiveEmbedding_mul_conjugateEmbedding]
      have hnorm : (x - y).norm ≠ 0 := fun hn ↦ hne ((Zsqrtd.norm_eq_zero two_ne_sq _).mp hn)
      positivity
    rw [h] at hcone
    simp at hcone
  exact sub_eq_zero.mp hzero

/-- A nonzero quadratic integer of the coefficient cone has distinguished embedding of absolute
value at least one. -/
public theorem one_le_abs_positiveEmbedding {x : QuadraticInteger}
    (hcone : InCoefficientCone x) (hx : x ≠ 0) : 1 ≤ |positiveEmbedding x| := by
  have hnorm : x.norm ≠ 0 := fun hn ↦ hx ((Zsqrtd.norm_eq_zero two_ne_sq x).mp hn)
  have hone : (1 : ℝ) ≤ |(x.norm : ℝ)| := by
    have h1 : 1 ≤ |x.norm| := Int.one_le_abs hnorm
    have h2 : (1 : ℝ) ≤ ((|x.norm| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs] at h2
  have hprod : |positiveEmbedding x| * |conjugateEmbedding x| = |(x.norm : ℝ)| := by
    rw [← abs_mul, positiveEmbedding_mul_conjugateEmbedding]
  have hle := conjugateEmbedding_abs_le_positiveEmbedding_abs_of_inCoefficientCone hcone
  nlinarith [abs_nonneg (positiveEmbedding x), abs_nonneg (conjugateEmbedding x)]

/-- Every entry of the canonical reduced-word matrix lies in the coefficient cone. -/
public theorem deltaEntry_inCoefficientCone (g : Delta) (i j : Fin 2) :
    InCoefficientCone (wordMatrix (deltaNormalForm g) i j) :=
  wordMatrix_matrixInCoefficientCone _ i j

public theorem deltaBottomRow_fst (g : Delta) :
    (deltaBottomRow g).1 = wordMatrix (deltaNormalForm g) 1 0 := rfl

public theorem deltaBottomRow_snd (g : Delta) :
    (deltaBottomRow g).2 = wordMatrix (deltaNormalForm g) 1 1 := rfl

/-- An element with nonzero lower-left entry contracts imaginary heights above one. -/
public theorem im_smul_le_one_div_im {g : Delta} (hc : (deltaBottomRow g).1 ≠ 0)
    (z : UpperHalfPlane) : (fuchsianSourceAction g • z).im ≤ 1 / z.im := by
  have hcone : InCoefficientCone (deltaBottomRow g).1 := by
    rw [deltaBottomRow_fst]; exact deltaEntry_inCoefficientCone g 1 0
  have hone : 1 ≤ |positiveEmbedding (deltaBottomRow g).1| := one_le_abs_positiveEmbedding hcone hc
  set c := positiveEmbedding (deltaBottomRow g).1 with hcdef
  set d := positiveEmbedding (deltaBottomRow g).2 with hddef
  have hcsq : 1 ≤ c ^ 2 := by nlinarith [abs_nonneg c, sq_abs c]
  have hnormSq : Complex.normSq (c * (z : ℂ) + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, pow_two]
  have hlower : z.im ^ 2 ≤ Complex.normSq (c * (z : ℂ) + d) := by
    rw [hnormSq]
    nlinarith [sq_nonneg (c * z.re + d), sq_nonneg z.im, z.im_pos]
  have hpos : 0 < Complex.normSq (c * (z : ℂ) + d) :=
    lt_of_lt_of_le (by positivity) hlower
  rw [fuchsianSourceAction_im_eq_div_wordBottomNormSq]
  rw [div_le_div_iff₀ hpos z.im_pos]
  nlinarith [z.im_pos, hlower]

/-! ## Elements acting by parabolic translations -/

/-- The explicit Möbius formula for the projective action of a real special-linear lift. -/
public theorem coe_fuchsianSLAction (A : SL2R) (z : UpperHalfPlane) :
    ((fuchsianSLAction A z : UpperHalfPlane) : ℂ) =
      ((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (z : ℂ) +
          (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) /
        ((A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (z : ℂ) +
          (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ A) • z : UpperHalfPlane) : ℂ) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
  · simp [Matrix.SpecialLinearGroup.det_mapGL]

/-- The distinguished lift entries of a triangle-group element. -/
public theorem positiveEmbedding_wordMatrix (g : Delta) (i j : Fin 2) :
    positiveEmbedding (wordMatrix (deltaNormalForm g) i j) =
      (deltaRealSL g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  congrFun (congrFun (positiveMatrix_deltaWordMatrix g) i) j

/-- An element of the triangle group acting as a translation of the upper half-plane. -/
public def IsTranslationBy (g : Delta) (t : ℝ) : Prop :=
  ∀ z : UpperHalfPlane, ((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ) = (z : ℂ) + t

public theorem IsTranslationBy.im {g : Delta} {t : ℝ} (h : IsTranslationBy g t)
    (z : UpperHalfPlane) : (fuchsianSourceAction g • z).im = z.im := by
  have := congrArg Complex.im (h z)
  simpa using this

public theorem IsTranslationBy.mul {g h : Delta} {t u : ℝ}
    (hg : IsTranslationBy g t) (hh : IsTranslationBy h u) : IsTranslationBy (g * h) (t + u) := by
  intro z
  rw [map_mul, mul_smul, hg, hh]
  push_cast
  ring

public theorem IsTranslationBy.inv {g : Delta} {t : ℝ} (hg : IsTranslationBy g t) :
    IsTranslationBy g⁻¹ (-t) := by
  intro z
  have := hg (fuchsianSourceAction g⁻¹ • z)
  rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one] at this
  change (z : ℂ) = _ at this
  rw [this]
  push_cast
  ring

public theorem IsTranslationBy.zpow {g : Delta} {t : ℝ} (hg : IsTranslationBy g t) (n : ℤ) :
    IsTranslationBy (g ^ n) (n * t) := by
  induction n using Int.induction_on with
  | zero => intro z; simp
  | succ n ih =>
      have := ih.mul hg
      rw [show ((n : ℤ) + 1) = ((n : ℤ) + 1) from rfl]
      have hpow : g ^ ((n : ℤ) + 1) = g ^ (n : ℤ) * g := by
        rw [zpow_add_one]
      rw [hpow]
      convert this using 1
      push_cast
      ring
  | pred n ih =>
      have := ih.mul hg.inv
      have hpow : g ^ (-(n : ℤ) - 1) = g ^ (-(n : ℤ)) * g⁻¹ := by
        rw [zpow_sub_one]
      rw [hpow]
      convert this using 1
      push_cast
      ring

/-- The permutation action is the underlying map. -/
public theorem smul_eq_apply (g : Delta) (z : UpperHalfPlane) :
    fuchsianSourceAction g • z = fuchsianSourceAction g z := rfl

/-- The parabolic generator translates by the cusp width. -/
public theorem isTranslationBy_g₀ : IsTranslationBy g₀ (-(1 + Real.sqrt 2)) := by
  intro z
  rw [smul_eq_apply, fuchsianSourceAction_g₀_apply]
  push_cast
  ring

/-- The high point `2i`, used to detect nontrivial contraction of heights. -/
public def twoI : UpperHalfPlane := ⟨⟨0, 2⟩, by norm_num⟩

public theorem twoI_im : twoI.im = 2 := rfl

/-- A translation has vanishing lower-left entry. -/
public theorem bottomLeft_eq_zero_of_isTranslationBy {g : Delta} {t : ℝ}
    (h : IsTranslationBy g t) : (deltaBottomRow g).1 = 0 := by
  by_contra hc
  have h1 := im_smul_le_one_div_im hc twoI
  rw [h.im twoI, twoI_im] at h1
  norm_num at h1

/-- An element with vanishing lower-left entry acts by a quadratic-integer translation. -/
public theorem exists_isTranslationBy_of_bottomLeft_eq_zero {g : Delta}
    (hc : (deltaBottomRow g).1 = 0) :
    ∃ B : QuadraticInteger, InCoefficientCone B ∧ IsTranslationBy g (positiveEmbedding B) := by
  have hentry := positiveEmbedding_wordMatrix g
  set A := deltaRealSL g with hA
  set M := (A : Matrix (Fin 2) (Fin 2) ℝ) with hM
  have hW10 : wordMatrix (deltaNormalForm g) 1 0 = 0 := hc
  have h10 : M 1 0 = 0 := by
    rw [← hentry 1 0, hW10, map_zero]
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact A.2
  rw [h10, mul_zero, sub_zero] at hdet
  -- the diagonal entries are units in the quadratic ring
  have hmulQ : wordMatrix (deltaNormalForm g) 0 0 * wordMatrix (deltaNormalForm g) 1 1 = 1 := by
    apply positiveEmbedding_injective
    rw [map_mul, hentry 0 0, hentry 1 1, hdet, map_one]
  have hnormQ : (wordMatrix (deltaNormalForm g) 0 0).norm *
      (wordMatrix (deltaNormalForm g) 1 1).norm = 1 := by
    rw [← Zsqrtd.norm_mul, hmulQ, Zsqrtd.norm_one]
  have habs00 : |((wordMatrix (deltaNormalForm g) 0 0).norm : ℝ)| = 1 := by
    have hunit : IsUnit (wordMatrix (deltaNormalForm g) 0 0).norm :=
      IsUnit.of_mul_eq_one _ hnormQ
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  have habs11 : |((wordMatrix (deltaNormalForm g) 1 1).norm : ℝ)| = 1 := by
    have hunit : IsUnit (wordMatrix (deltaNormalForm g) 1 1).norm :=
      IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hnormQ)
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  have hge00 : 1 ≤ |M 0 0| := by
    have hprod : |positiveEmbedding (wordMatrix (deltaNormalForm g) 0 0)| *
        |conjugateEmbedding (wordMatrix (deltaNormalForm g) 0 0)| = 1 := by
      rw [← abs_mul, positiveEmbedding_mul_conjugateEmbedding, habs00]
    have hle := conjugateEmbedding_abs_le_positiveEmbedding_abs_of_inCoefficientCone
      (deltaEntry_inCoefficientCone g 0 0)
    rw [← hentry 0 0]
    nlinarith [abs_nonneg (positiveEmbedding (wordMatrix (deltaNormalForm g) 0 0)),
      abs_nonneg (conjugateEmbedding (wordMatrix (deltaNormalForm g) 0 0))]
  have hge11 : 1 ≤ |M 1 1| := by
    have hprod : |positiveEmbedding (wordMatrix (deltaNormalForm g) 1 1)| *
        |conjugateEmbedding (wordMatrix (deltaNormalForm g) 1 1)| = 1 := by
      rw [← abs_mul, positiveEmbedding_mul_conjugateEmbedding, habs11]
    have hle := conjugateEmbedding_abs_le_positiveEmbedding_abs_of_inCoefficientCone
      (deltaEntry_inCoefficientCone g 1 1)
    rw [← hentry 1 1]
    nlinarith [abs_nonneg (positiveEmbedding (wordMatrix (deltaNormalForm g) 1 1)),
      abs_nonneg (conjugateEmbedding (wordMatrix (deltaNormalForm g) 1 1))]
  have habsmul : |M 0 0| * |M 1 1| = 1 := by rw [← abs_mul, hdet, abs_one]
  have habs0 : |M 0 0| = 1 := by nlinarith
  have hsign : M 0 0 = 1 ∨ M 0 0 = -1 := abs_eq (by norm_num) |>.mp habs0
  have hdiag : M 1 1 = M 0 0 := by
    rcases hsign with h | h <;> rw [h] at hdet ⊢ <;> linarith
  -- the resulting translation
  have haction : ∀ z : UpperHalfPlane,
      ((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ) = (z : ℂ) + M 0 0 * M 0 1 := by
    intro z
    rw [smul_eq_apply, fuchsianSourceAction_eq_deltaRealSL g]
    rw [coe_fuchsianSLAction]
    rw [← hM, h10, hdiag]
    rcases hsign with h | h <;> rw [h] <;> push_cast <;> field_simp <;> ring
  rcases hsign with h | h
  · refine ⟨wordMatrix (deltaNormalForm g) 0 1, deltaEntry_inCoefficientCone g 0 1, ?_⟩
    intro z
    rw [haction z, hentry 0 1, h]
    push_cast
    ring
  · refine ⟨-(wordMatrix (deltaNormalForm g) 0 1), ?_, ?_⟩
    · have := deltaEntry_inCoefficientCone g 0 1
      change 0 ≤ (wordMatrix (deltaNormalForm g) 0 1).re *
        (wordMatrix (deltaNormalForm g) 0 1).im at this
      change 0 ≤ (-(wordMatrix (deltaNormalForm g) 0 1)).re *
        (-(wordMatrix (deltaNormalForm g) 0 1)).im
      simpa using this
    · intro z
      rw [haction z, map_neg, hentry 0 1, h]
      push_cast
      ring

public theorem IsTranslationBy.unique {g : Delta} {t u : ℝ}
    (ht : IsTranslationBy g t) (hu : IsTranslationBy g u) : t = u := by
  have h := (ht twoI).symm.trans (hu twoI)
  have h' : (t : ℂ) = (u : ℂ) := by
    have := congrArg (fun w : ℂ ↦ w - (twoI : ℂ)) h
    simpa using this
  exact_mod_cast h'

/-- The cusp width as a quadratic integer. -/
public def cuspWidthQ : QuadraticInteger := ⟨1, 1⟩

public theorem positiveEmbedding_cuspWidthQ :
    positiveEmbedding cuspWidthQ = 1 + Real.sqrt 2 := by
  simp [cuspWidthQ]

/-- An integer pair whose doubled shifted products never change sign is diagonal. -/
public theorem eq_of_even_products {a b : ℤ}
    (h : ∀ k : ℤ, 0 ≤ (2 * a - k) * (2 * b - k)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hk := h (2 * a + 1)
    nlinarith
  · exact hab
  · have hk := h (2 * b + 1)
    nlinarith

/-- Every element acting by a translation is a power of the parabolic generator. -/
public theorem exists_zpow_g₀_of_isTranslationBy {g : Delta} {t : ℝ}
    (ht : IsTranslationBy g t) : ∃ k : ℤ, g = g₀ ^ k := by
  obtain ⟨B, hcone, hB⟩ :=
    exists_isTranslationBy_of_bottomLeft_eq_zero (bottomLeft_eq_zero_of_isTranslationBy ht)
  have hkey : ∀ k : ℤ, 0 ≤ (2 * B.re - k) * (2 * B.im - k) := by
    intro k
    have hmul : IsTranslationBy (g ^ (2 : ℤ) * g₀ ^ k)
        (2 * positiveEmbedding B + k * -(1 + Real.sqrt 2)) :=
      (hB.zpow 2).mul (isTranslationBy_g₀.zpow k)
    obtain ⟨B', hcone', hB'⟩ :=
      exists_isTranslationBy_of_bottomLeft_eq_zero (bottomLeft_eq_zero_of_isTranslationBy hmul)
    have hBeq : B' = (2 : QuadraticInteger) * B - (k : QuadraticInteger) * cuspWidthQ := by
      apply positiveEmbedding_injective
      rw [hB'.unique hmul]
      rw [map_sub, map_mul, map_mul, positiveEmbedding_cuspWidthQ, map_intCast, map_ofNat]
      ring
    have hre : B'.re = 2 * B.re - k := by
      rw [hBeq]; simp [cuspWidthQ]
    have him : B'.im = 2 * B.im - k := by
      rw [hBeq]; simp [cuspWidthQ]
    have := hcone'
    change 0 ≤ B'.re * B'.im at this
    rwa [hre, him] at this
  have hdiag : B.re = B.im := eq_of_even_products hkey
  have hposB : positiveEmbedding B = (B.re : ℝ) * (1 + Real.sqrt 2) := by
    rw [positiveEmbedding_apply, ← hdiag]
    ring
  refine ⟨-B.re, ?_⟩
  apply FuchsianPingPong.fuchsianSourceAction_injective
  have hpow : IsTranslationBy (g₀ ^ (-B.re)) ((-B.re : ℤ) * -(1 + Real.sqrt 2)) :=
    isTranslationBy_g₀.zpow _
  have hsame : ((-B.re : ℤ) : ℝ) * -(1 + Real.sqrt 2) = positiveEmbedding B := by
    rw [hposB]
    push_cast
    ring
  rw [hsame] at hpow
  ext z
  have h1 := hB z
  have h2 := hpow z
  rw [smul_eq_apply] at h1 h2
  rw [h1, h2]

/-! ## Orbit heights and the regular locus -/

/-- Imaginary heights are bounded along every orbit of the explicit Fuchsian action. -/
public theorem exists_orbit_height_bound (w : UpperHalfPlane) :
    ∃ M : ℝ, ∀ g : Delta, (fuchsianSourceAction g • w).im ≤ M := by
  obtain ⟨h, hmax⟩ := exists_fuchsian_orbitHeightMaximal w
  refine ⟨(fuchsianSourceAction h • w).im, fun g ↦ ?_⟩
  have hg := hmax (g * h⁻¹)
  rw [map_mul, mul_smul, map_inv] at hg
  rwa [inv_smul_smul] at hg

/-- Away from a bounded height, every element with nonzero lower-left entry contracts. -/
public theorem im_smul_le_max (g : Delta) (z : UpperHalfPlane) :
    (fuchsianSourceAction g • z).im ≤ max z.im (1 / z.im) := by
  by_cases hc : (deltaBottomRow g).1 = 0
  · obtain ⟨B, _, hB⟩ := exists_isTranslationBy_of_bottomLeft_eq_zero hc
    rw [hB.im z]
    exact le_max_left _ _
  · exact (im_smul_le_one_div_im hc z).trans (le_max_right _ _)

/-- High points of the upper half-plane are regular for the explicit Fuchsian action. -/
public theorem exists_regular_height (U : SphereSixComplex.Periods.TriangleUniformization)
    (hsource : U.sourceAction = fuchsianSourceAction) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ z : UpperHalfPlane, M < z.im →
      SphereSixComplex.Geometry.GlobalTorusFamily.IsRegularBasePoint (U := U) z := by
  obtain ⟨M₁, hM₁⟩ := exists_orbit_height_bound U.zOne
  obtain ⟨M₂, hM₂⟩ := exists_orbit_height_bound U.zTwo
  refine ⟨max (max M₁ M₂) 1, le_max_right _ _, ?_⟩
  intro z hz
  intro g
  constructor
  · intro hgz
    have hzeq : z = fuchsianSourceAction g⁻¹ • U.zOne := by
      rw [← hgz, hsource, ← mul_smul, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have := hM₁ g⁻¹
    rw [← hzeq] at this
    exact absurd (lt_of_le_of_lt (this.trans ((le_max_left M₁ M₂).trans (le_max_left _ _))) hz)
      (lt_irrefl _)
  · intro hgz
    have hzeq : z = fuchsianSourceAction g⁻¹ • U.zTwo := by
      rw [← hgz, hsource, ← mul_smul, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have := hM₂ g⁻¹
    rw [← hzeq] at this
    exact absurd (lt_of_le_of_lt (this.trans ((le_max_right M₁ M₂).trans (le_max_left _ _))) hz)
      (lt_irrefl _)

/-! ## Growth of the normalized cusp lift -/

section Tau

open SphereSixComplex.Periods

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem tau_transform_cusp_inv (z : UpperHalfPlane) :
    ((F.tau (U.sourceAction g₀⁻¹ • z) : UpperHalfPlane) : ℂ) = (F.tau z : ℂ) + 1 := by
  have h := F.tau_transform_cusp (U.sourceAction g₀⁻¹ • z)
  rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at h
  rw [h]
  ring

/-- Iterated cusp translation on the target parameter. -/
public theorem tau_zpow_cusp (n : ℤ) : ∀ z : UpperHalfPlane,
    ((F.tau (U.sourceAction (g₀ ^ n) • z) : UpperHalfPlane) : ℂ) = (F.tau z : ℂ) - n := by
  induction n using Int.induction_on with
  | zero => intro z; simp
  | succ n ih =>
      intro z
      rw [zpow_add_one, map_mul, mul_smul, ih (U.sourceAction g₀ • z), F.tau_transform_cusp]
      push_cast
      ring
  | pred n ih =>
      intro z
      rw [zpow_sub_one, map_mul, mul_smul, ih (U.sourceAction g₀⁻¹ • z),
        tau_transform_cusp_inv F z]
      push_cast
      ring

public theorem tau_zpow_cusp_im (n : ℤ) (z : UpperHalfPlane) :
    (F.tau (U.sourceAction (g₀ ^ n) • z)).im = (F.tau z).im := by
  have h := congrArg Complex.im (tau_zpow_cusp F n z)
  simpa using h

public theorem tau_continuous : Continuous (fun z : UpperHalfPlane ↦ (F.tau z).im) :=
  Complex.continuous_im.comp
    (UpperHalfPlane.continuous_coe.comp F.tau_holomorphic.continuous)

end Tau

/-- A closed horizontal band of the upper half-plane is compact. -/
public theorem isCompact_band (a b c : ℝ) (hb : 0 < b) :
    IsCompact {z : UpperHalfPlane | |z.re| ≤ a ∧ b ≤ z.im ∧ z.im ≤ c} := by
  have hrect : IsCompact ((Set.Icc (-a) a) ×ℂ Set.Icc b c) :=
    isCompact_Icc.reProdIm isCompact_Icc
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  convert hrect using 1
  ext z
  constructor
  · rintro ⟨w, ⟨hwre, hwimLower, hwimUpper⟩, rfl⟩
    exact ⟨⟨(abs_le.mp hwre).1, (abs_le.mp hwre).2⟩, hwimLower, hwimUpper⟩
  · rintro ⟨⟨hzreLower, hzreUpper⟩, hzimLower, hzimUpper⟩
    have hzimPos : 0 < z.im := lt_of_lt_of_le hb hzimLower
    exact ⟨⟨z, hzimPos⟩, ⟨abs_le.mpr ⟨hzreLower, hzreUpper⟩, hzimLower, hzimUpper⟩, rfl⟩

/-- Every point can be translated by the parabolic generator into the standard vertical strip. -/
public theorem exists_zpow_g₀_mem_strip (z : UpperHalfPlane) :
    ∃ n : ℤ, |(fuchsianSourceAction (g₀ ^ n) • z).re| ≤ (1 + Real.sqrt 2) / 2 ∧
      (fuchsianSourceAction (g₀ ^ n) • z).im = z.im := by
  have hw : 0 < 1 + Real.sqrt 2 := by positivity
  refine ⟨round (z.re / (1 + Real.sqrt 2)), ?_, ?_⟩
  · have htr := isTranslationBy_g₀.zpow (round (z.re / (1 + Real.sqrt 2)))
    have hre := congrArg Complex.re (htr z)
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    change (fuchsianSourceAction (g₀ ^ round (z.re / (1 + Real.sqrt 2))) • z).re
        = z.re + (round (z.re / (1 + Real.sqrt 2)) : ℝ) * -(1 + Real.sqrt 2) at hre
    rw [hre]
    have hround :
        |z.re / (1 + Real.sqrt 2) - (round (z.re / (1 + Real.sqrt 2)) : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    have hsplit : z.re + (round (z.re / (1 + Real.sqrt 2)) : ℝ) * -(1 + Real.sqrt 2) =
        (1 + Real.sqrt 2) *
          (z.re / (1 + Real.sqrt 2) - (round (z.re / (1 + Real.sqrt 2)) : ℝ)) := by
      field_simp
      ring
    rw [hsplit, abs_mul, abs_of_pos hw]
    nlinarith [abs_nonneg (z.re / (1 + Real.sqrt 2) -
      (round (z.re / (1 + Real.sqrt 2)) : ℝ))]
  · exact (isTranslationBy_g₀.zpow _).im z

/-! ## The normalized horodisc -/

public theorem norm_cuspQ (s : ℂ) : ‖cuspQ s‖ = Real.exp (-(2 * Real.pi * s.im)) := by
  rw [cuspQ, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

public theorem isOpen_cuspHalfPlane (H : ℝ) : IsOpen (cuspHalfPlane H) :=
  isOpen_Ioi.preimage Complex.continuous_im

public theorem convex_cuspHalfPlane (H : ℝ) : Convex ℝ (cuspHalfPlane H) :=
  convex_halfSpace_im_gt H

/-- The source disc of the normalized horodisc. -/
public def cuspSource (H r : ℝ) : Set ℂ := {s | s ∈ cuspHalfPlane H ∧ ‖cuspQ s‖ < r}

public theorem isOpen_cuspSource (H r : ℝ) : IsOpen (cuspSource H r) := by
  have hcont : Continuous fun s : ℂ ↦ ‖cuspQ s‖ :=
    continuous_norm.comp
      (Complex.continuous_exp.comp (continuous_const.mul continuous_id))
  exact (isOpen_cuspHalfPlane H).inter (hcont.isOpen_preimage _ isOpen_Iio)

public theorem cuspSource_subset (H r : ℝ) : cuspSource H r ⊆ cuspHalfPlane H :=
  fun _ hs ↦ hs.1

/-- Deep enough source discs sit above any prescribed height. -/
public theorem cuspSource_im (H A r : ℝ) (hr : r ≤ Real.exp (-(2 * Real.pi * A)))
    {s : ℂ} (hs : s ∈ cuspSource H r) : A < s.im := by
  have hlt : Real.exp (-(2 * Real.pi * s.im)) < Real.exp (-(2 * Real.pi * A)) := by
    rw [← norm_cuspQ]
    exact lt_of_lt_of_le hs.2 hr
  have := (Real.exp_lt_exp).mp hlt
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

/-! ## Precise invariance of a deep horodisc -/

section Precise

open SphereSixComplex.Periods SphereSixComplex.Geometry.GlobalTorusFamily

public theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h4.le, h4.ge]

public theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa using h

public theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have h : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h4.le, h4.ge]

public theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  have h : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa using h

public theorem fuchsianOneFixedPoint_im : fuchsianOneFixedPoint.im = Real.sqrt 3 / 2 := rfl

public theorem fuchsianTwoFixedPoint_im : fuchsianTwoFixedPoint.im = Real.sqrt 2 / 2 := rfl

/-- The saturation of a deep horodisc avoids the two elliptic orbits, even after closure. -/
public theorem orbitClosure_regular
    (U : TriangleUniformization) (hsource : U.sourceAction = fuchsianSourceAction)
    (hzOne : U.zOne = fuchsianOneFixedPoint) (hzTwo : U.zTwo = fuchsianTwoFixedPoint)
    {Y : ℝ} (hY : 2 ≤ Y) (S : Set UpperHalfPlane) (hS : ∀ z ∈ S, Y < z.im) :
    closure (⋃ g : Delta, (fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' S) ⊆
      {z | IsRegularBasePoint (U := U) z} := by
  have hYpos : (0 : ℝ) < Y := by linarith
  set T : Set UpperHalfPlane := ⋃ g : Delta, (fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' S
    with hTdef
  have hband : IsOpen {z : UpperHalfPlane | 1 / Y < z.im ∧ z.im < Y} := by
    have hcont : Continuous fun z : UpperHalfPlane ↦ z.im :=
      Complex.continuous_im.comp UpperHalfPlane.continuous_coe
    exact (hcont.isOpen_preimage _ isOpen_Ioi).inter (hcont.isOpen_preimage _ isOpen_Iio)
  have hdisjoint : ∀ z ∈ T, ¬ (1 / Y < z.im ∧ z.im < Y) := by
    rintro z hz ⟨hlow, hhigh⟩
    rw [hTdef, Set.mem_iUnion] at hz
    obtain ⟨g, w, hw, rfl⟩ := hz
    have hwY := hS w hw
    have hwpos : 0 < w.im := lt_trans hYpos hwY
    rw [hsource] at hhigh hlow
    by_cases hc : (deltaBottomRow g).1 = 0
    · obtain ⟨B, _, hB⟩ := exists_isTranslationBy_of_bottomLeft_eq_zero hc
      rw [hB.im w] at hhigh
      linarith
    · have hle := im_smul_le_one_div_im hc w
      have : 1 / w.im < 1 / Y := by
        apply one_div_lt_one_div_of_lt hYpos hwY
      linarith
  have hclosed : closure T ⊆ {z : UpperHalfPlane | 1 / Y < z.im ∧ z.im < Y}ᶜ := by
    apply closure_minimal
    · intro z hz
      exact hdisjoint z hz
    · exact hband.isClosed_compl
  have hinvariant : ∀ h : Delta, (fun z : UpperHalfPlane ↦ U.sourceAction h • z) '' T ⊆ T := by
    rintro h _ ⟨z, hz, rfl⟩
    rw [hTdef, Set.mem_iUnion] at hz ⊢
    obtain ⟨g, w, hw, rfl⟩ := hz
    refine ⟨h * g, w, hw, ?_⟩
    show U.sourceAction (h * g) • w = U.sourceAction h • U.sourceAction g • w
    rw [map_mul, mul_smul]
  intro z hz g
  have hcont : Continuous fun w : UpperHalfPlane ↦ U.sourceAction g • w :=
    (U.sourceAction_contMDiff g ⊤).continuous
  have hmem : U.sourceAction g • z ∈ closure T := by
    have h1 : (fun w : UpperHalfPlane ↦ U.sourceAction g • w) '' closure T ⊆
        closure ((fun w : UpperHalfPlane ↦ U.sourceAction g • w) '' T) :=
      image_closure_subset_closure_image hcont
    exact (closure_mono (hinvariant g)) (h1 ⟨z, hz, rfl⟩)
  have hnot := hclosed hmem
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_lt] at hnot
  constructor
  · intro hone
    rw [hone, hzOne, fuchsianOneFixedPoint_im] at hnot
    have h3 := one_lt_sqrt_three
    have h3' := sqrt_three_lt_two
    have : 1 / Y ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) hY
    have hcontra := hnot (by linarith)
    linarith
  · intro htwo
    rw [htwo, hzTwo, fuchsianTwoFixedPoint_im] at hnot
    have h2 := one_lt_sqrt_two
    have h2' := sqrt_two_lt_two
    have : 1 / Y ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) hY
    have hcontra := hnot (by linarith)
    linarith

end Precise

/-! ## The cusp parameter of the source half-plane -/

public theorem exists_exp_neg_lt {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A < y → Real.exp (-(c * y)) < ε := by
  refine ⟨max 1 ((1 / ε) / c), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro y hy
  have hy1 : 1 < y := lt_of_le_of_lt (le_max_left _ _) hy
  have hy2 : (1 / ε) / c < y := lt_of_le_of_lt (le_max_right _ _) hy
  have hcy : 1 / ε < c * y := by
    rw [div_lt_iff₀ hc] at hy2
    linarith [hy2]
  have hexp : 1 + c * y ≤ Real.exp (c * y) := by
    have := Real.add_one_le_exp (c * y)
    linarith
  have hpos : 0 < Real.exp (c * y) := Real.exp_pos _
  rw [Real.exp_neg, inv_lt_comm₀ hpos hε, ← one_div]
  linarith

/-- The cusp parameter of the source half-plane, normalized by the cusp width. -/
public def sourceQ (z : UpperHalfPlane) : ℂ := cuspQ ((z : ℂ) / (1 + Real.sqrt 2))

public theorem norm_sourceQ (z : UpperHalfPlane) :
    ‖sourceQ z‖ = Real.exp (-(2 * Real.pi * (z.im / (1 + Real.sqrt 2)))) := by
  rw [sourceQ, norm_cuspQ]
  congr 2
  have hw : (1 : ℝ) + Real.sqrt 2 ≠ 0 := by positivity
  rw [Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp

public theorem sourceQ_ne_zero (z : UpperHalfPlane) : sourceQ z ≠ 0 :=
  Complex.exp_ne_zero _

/-- Two points with the same source cusp parameter differ by a parabolic translation. -/
public theorem exists_zpow_g₀_of_sourceQ_eq {z w : UpperHalfPlane} (h : sourceQ z = sourceQ w) :
    ∃ k : ℤ, fuchsianSourceAction (g₀ ^ k) • w = z := by
  have hw : (1 : ℝ) + Real.sqrt 2 ≠ 0 := by positivity
  have hwC : ((1 : ℂ) + (Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro hzero
    apply hw
    have := congrArg Complex.re hzero
    simpa using this
  rw [sourceQ, sourceQ, cuspQ, cuspQ, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hkey : (z : ℂ) = (w : ℂ) + n * (1 + Real.sqrt 2) := by
    field_simp at hn
    push_cast at hn ⊢
    linear_combination hn
  refine ⟨-n, ?_⟩
  apply UpperHalfPlane.coe_injective
  have htr := (isTranslationBy_g₀.zpow (-n)) w
  rw [smul_eq_apply] at htr ⊢
  rw [htr, hkey]
  push_cast
  ring

/-- Every small nonzero value is a cusp parameter of a deep point of the half-plane. -/
public theorem exists_cuspQ_preimage {q : ℂ} (hq : q ≠ 0) {A : ℝ}
    (hnorm : ‖q‖ < Real.exp (-(2 * Real.pi * A))) :
    ∃ s : ℂ, A < s.im ∧ cuspQ s = q := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨⟨Complex.arg q / (2 * Real.pi), -(Real.log ‖q‖) / (2 * Real.pi)⟩, ?_, ?_⟩
  · have hlog : Real.log ‖q‖ < -(2 * Real.pi * A) := by
      have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
      calc Real.log ‖q‖ < Real.log (Real.exp (-(2 * Real.pi * A))) :=
            Real.log_lt_log hqpos hnorm
        _ = -(2 * Real.pi * A) := Real.log_exp _
    change A < -(Real.log ‖q‖) / (2 * Real.pi)
    rw [lt_div_iff₀ (by linarith)]
    linarith
  · rw [cuspQ]
    have hlogq : (2 : ℂ) * Real.pi * Complex.I *
        (⟨Complex.arg q / (2 * Real.pi), -(Real.log ‖q‖) / (2 * Real.pi)⟩ : ℂ) =
        Complex.log q := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.mul_im, Complex.log_re]
        field_simp
      · simp [Complex.mul_re, Complex.mul_im, Complex.log_im]
        field_simp
    rw [hlogq, Complex.exp_log hq]

section Lift

open SphereSixComplex.Periods

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  (N : NormalizedFuchsianCuspCoordinate E D)

/-- The normalized lift goes arbitrarily deep into the source cusp. -/
public theorem exists_lift_height_bound (Y : ℝ) :
    ∃ T : ℝ, ∀ s : ℂ, s ∈ cuspHalfPlane N.height → T < s.im → Y < (N.lift s).im := by
  classical
  set F := assembledFuchsianPeriodFunctions E D with hF
  set K : Set UpperHalfPlane :=
    {z | |z.re| ≤ (1 + Real.sqrt 2) / 2 ∧ 1 ≤ z.im ∧ z.im ≤ max Y 1} with hKdef
  have hKcompact : IsCompact K := isCompact_band _ _ _ one_pos
  obtain ⟨T, hT⟩ := hKcompact.bddAbove_image (tau_continuous F).continuousOn
  refine ⟨T, ?_⟩
  intro s hs hTs
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, hstrip, him⟩ := exists_zpow_g₀_mem_strip (N.lift s)
  have hmemK : fuchsianSourceAction (g₀ ^ n) • N.lift s ∈ K := by
    refine ⟨hstrip, ?_, ?_⟩
    · rw [him]
      exact N.lift_mem_cusp s hs
    · rw [him]
      exact hcon.trans (le_max_left _ _)
  have hbound : (F.tau (fuchsianSourceAction (g₀ ^ n) • N.lift s)).im ≤ T :=
    hT ⟨_, hmemK, rfl⟩
  have hshift : (F.tau (fuchsianSourceAction (g₀ ^ n) • N.lift s)).im =
      (F.tau (N.lift s)).im := tau_zpow_cusp_im F n (N.lift s)
  have hvalue : (F.tau (N.lift s)).im = s.im := by
    have h := N.lift_tau s hs
    exact congrArg Complex.im h
  rw [hshift, hvalue] at hbound
  linarith

/-- The normalized lift is injective on its half-plane. -/
public theorem lift_injOn : Set.InjOn N.lift (cuspHalfPlane N.height) := by
  intro s hs s' hs' h
  rw [← N.lift_tau s hs, ← N.lift_tau s' hs', h]

public theorem lift_differentiableOn :
    DifferentiableOn ℂ (fun s ↦ ((N.lift s : UpperHalfPlane) : ℂ)) (cuspHalfPlane N.height) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  change MDiff[cuspHalfPlane N.height] ((fun z : UpperHalfPlane ↦ (z : ℂ)) ∘ N.lift)
  exact UpperHalfPlane.mdifferentiable_coe.comp_mdifferentiableOn N.lift_holomorphic

public theorem normalizedCuspRegion_eq (r : ℝ) :
    normalizedCuspRegion N r = N.lift '' cuspSource N.height r := rfl

/-- The normalized horodisc is open. -/
public theorem normalizedCuspRegion_isOpen (r : ℝ) : IsOpen (normalizedCuspRegion N r) := by
  have hanalytic : AnalyticOnNhd ℂ (fun s ↦ ((N.lift s : UpperHalfPlane) : ℂ))
      (cuspHalfPlane N.height) :=
    (lift_differentiableOn N).analyticOnNhd (isOpen_cuspHalfPlane _)
  have hpre : IsPreconnected (cuspHalfPlane N.height) :=
    (convex_cuspHalfPlane _).isPreconnected
  have hnotconst : ¬ ∃ w, ∀ s ∈ cuspHalfPlane N.height, ((N.lift s : UpperHalfPlane) : ℂ) = w := by
    rintro ⟨w, hw⟩
    have hs₀ : (⟨0, N.height + 1⟩ : ℂ) ∈ cuspHalfPlane N.height := by
      change N.height < (⟨0, N.height + 1⟩ : ℂ).im
      simp
    have hs₁ : (⟨0, N.height + 1⟩ : ℂ) + 1 ∈ cuspHalfPlane N.height := by
      change N.height < ((⟨0, N.height + 1⟩ : ℂ) + 1).im
      simp
    have hlift : N.lift (⟨0, N.height + 1⟩ : ℂ) = N.lift ((⟨0, N.height + 1⟩ : ℂ) + 1) := by
      apply UpperHalfPlane.coe_injective
      rw [hw _ hs₀, hw _ hs₁]
    have h1 := N.lift_tau (⟨0, N.height + 1⟩ : ℂ) hs₀
    have h2 := N.lift_tau ((⟨0, N.height + 1⟩ : ℂ) + 1) hs₁
    rw [hlift, h2] at h1
    have : (1 : ℂ) = 0 := by linear_combination h1
    simp at this
  have hopenmap := (hanalytic.is_constant_or_isOpen hpre).resolve_left hnotconst
  have himage : IsOpen ((fun s ↦ ((N.lift s : UpperHalfPlane) : ℂ)) '' cuspSource N.height r) :=
    hopenmap _ (cuspSource_subset _ _) (isOpen_cuspSource _ _)
  have hset : normalizedCuspRegion N r =
      (fun z : UpperHalfPlane ↦ (z : ℂ)) ⁻¹'
        ((fun s ↦ ((N.lift s : UpperHalfPlane) : ℂ)) '' cuspSource N.height r) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hzs⟩
      exact ⟨s, hs, UpperHalfPlane.coe_injective hzs⟩
  rw [hset]
  exact himage.preimage UpperHalfPlane.continuous_coe

/-- Deep normalized horodiscs lie above any prescribed height. -/
public theorem normalizedCuspRegion_im (Y : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ cuspRadius N.height ∧
      ∀ r : ℝ, r ≤ ρ → ∀ z ∈ normalizedCuspRegion N r, Y < z.im := by
  obtain ⟨T, hT⟩ := exists_lift_height_bound N Y
  refine ⟨Real.exp (-(2 * Real.pi * max N.height T)), Real.exp_pos _, ?_, ?_⟩
  · rw [cuspRadius]
    apply Real.exp_le_exp.mpr
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [le_max_left N.height T]
  · rintro r hr z ⟨s, hs, rfl⟩
    have hsource : s ∈ cuspSource N.height r := hs
    have hmax : max N.height T < s.im :=
      cuspSource_im N.height (max N.height T) r hr hsource
    exact hT s hs.1 (lt_of_le_of_lt (le_max_right _ _) hmax)

/-! ## Surjectivity of the normalized horodisc onto the cusp end -/

/-- The source cusp parameter along the normalized lift. -/
public def liftQ (s : ℂ) : ℂ := sourceQ (N.lift s)

public theorem liftQ_apply (s : ℂ) :
    liftQ N s =
      Complex.exp (2 * Real.pi * Complex.I *
        (((N.lift s : UpperHalfPlane) : ℂ) / (1 + (Real.sqrt 2 : ℂ)))) := rfl

public theorem liftQ_ne_zero (s : ℂ) : liftQ N s ≠ 0 := sourceQ_ne_zero _

public theorem liftQ_differentiableOn :
    DifferentiableOn ℂ (liftQ N) (cuspHalfPlane N.height) := by
  have h1 := lift_differentiableOn N
  have h2 : DifferentiableOn ℂ
      (fun s ↦ 2 * (Real.pi : ℂ) * Complex.I *
        (((N.lift s : UpperHalfPlane) : ℂ) / (1 + (Real.sqrt 2 : ℂ))))
      (cuspHalfPlane N.height) :=
    (differentiableOn_const _).mul (h1.div_const _)
  exact Complex.differentiable_exp.comp_differentiableOn h2

public theorem liftQ_periodic (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    liftQ N (s - 1) = liftQ N s := by
  have hw : (1 : ℝ) + Real.sqrt 2 ≠ 0 := by positivity
  have hwC : ((1 : ℂ) + (Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro hzero
    apply hw
    have := congrArg Complex.re hzero
    simpa using this
  have hshift : ((N.lift (s - 1) : UpperHalfPlane) : ℂ) =
      ((N.lift s : UpperHalfPlane) : ℂ) - (1 + (Real.sqrt 2 : ℂ)) := by
    rw [N.lift_shift s hs]
    show ((fuchsianSourceAction g₀ • N.lift s : UpperHalfPlane) : ℂ) =
      ((N.lift s : UpperHalfPlane) : ℂ) - (1 + (Real.sqrt 2 : ℂ))
    rw [isTranslationBy_g₀ (N.lift s)]
    push_cast
    ring
  rw [liftQ_apply, liftQ_apply, hshift]
  have hsplit : (((N.lift s : UpperHalfPlane) : ℂ) - (1 + (Real.sqrt 2 : ℂ))) /
      (1 + (Real.sqrt 2 : ℂ)) = ((N.lift s : UpperHalfPlane) : ℂ) / (1 + (Real.sqrt 2 : ℂ)) - 1 := by
    field_simp
  rw [hsplit, mul_sub, mul_one]
  exact Complex.exp_periodic.sub_eq _

public theorem liftQ_bounded : NormBoundedOn (liftQ N) (cuspHalfPlane N.height) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro s hs
  have hnorm : ‖liftQ N s‖ =
      Real.exp (-(2 * Real.pi * ((N.lift s).im / (1 + Real.sqrt 2)))) := norm_sourceQ _
  rw [hnorm]
  have him : (1 : ℝ) ≤ (N.lift s).im := N.lift_mem_cusp s hs
  have hw : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hquot : 0 ≤ (N.lift s).im / (1 + Real.sqrt 2) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.exp_le_one_iff]
  nlinarith

/-- The holomorphic descent of the source cusp parameter through the normalized lift. -/
public noncomputable def liftDescent : HolomorphicCuspDescent N.height (liftQ N) :=
  Classical.choice
    (CuspPeriodExpansion.Established.periodicBoundedHolomorphicCuspDescent N.height (liftQ N)
      (liftQ_differentiableOn N) (liftQ_periodic N) (liftQ_bounded N))

public theorem liftDescent_zero : (liftDescent N).extension 0 = 0 := by
  classical
  have hR : 0 < cuspRadius N.height := cuspRadius_pos _
  have hcont : ContinuousAt (liftDescent N).extension 0 :=
    ((liftDescent N).extension_holomorphic.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).continuousAt
  by_contra hne
  have hcpos : 0 < ‖(liftDescent N).extension 0‖ := norm_pos_iff.mpr hne
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.mp hcont (‖(liftDescent N).extension 0‖ / 2) (by linarith)
  obtain ⟨A₁, hA₁pos, hA₁⟩ := exists_exp_neg_lt hδ (show (0 : ℝ) < 2 * Real.pi by positivity)
  obtain ⟨A₂, hA₂pos, hA₂⟩ :=
    exists_exp_neg_lt (show (0 : ℝ) < ‖(liftDescent N).extension 0‖ / 2 by linarith)
      (show (0 : ℝ) < 2 * Real.pi / (1 + Real.sqrt 2) by positivity)
  obtain ⟨T, hT⟩ := exists_lift_height_bound N A₂
  set s : ℂ := ⟨0, max (max A₁ T) N.height + 1⟩ with hsdef
  have hsim : s.im = max (max A₁ T) N.height + 1 := rfl
  have hsmem : s ∈ cuspHalfPlane N.height := by
    change N.height < s.im
    rw [hsim]
    have := le_max_right (max A₁ T) N.height
    linarith
  have hsA₁ : A₁ < s.im := by
    rw [hsim]
    have h1 := le_max_left A₁ T
    have h2 := le_max_left (max A₁ T) N.height
    linarith
  have hsT : T < s.im := by
    rw [hsim]
    have h1 := le_max_right A₁ T
    have h2 := le_max_left (max A₁ T) N.height
    linarith
  have hqsmall : ‖cuspQ s‖ < δ := by
    rw [norm_cuspQ]
    exact hA₁ s.im hsA₁
  have hliftbig : A₂ < (N.lift s).im := hT s hsmem hsT
  have hliftsmall : ‖liftQ N s‖ < ‖(liftDescent N).extension 0‖ / 2 := by
    have hnorm : ‖liftQ N s‖ =
        Real.exp (-(2 * Real.pi * ((N.lift s).im / (1 + Real.sqrt 2)))) := norm_sourceQ _
    have hrew : -(2 * Real.pi * ((N.lift s).im / (1 + Real.sqrt 2))) =
        -(2 * Real.pi / (1 + Real.sqrt 2) * (N.lift s).im) := by ring
    rw [hnorm, hrew]
    exact hA₂ _ hliftbig
  have hfact : (liftDescent N).extension (cuspQ s) = liftQ N s :=
    (liftDescent N).factorization s hsmem
  have hdist := hball (show dist (cuspQ s) 0 < δ by simpa [dist_eq_norm] using hqsmall)
  rw [dist_eq_norm, hfact] at hdist
  have htri : ‖(liftDescent N).extension 0‖ ≤
      ‖liftQ N s - (liftDescent N).extension 0‖ + ‖liftQ N s‖ := by
    have := norm_sub_norm_le (liftQ N s) (liftQ N s - (liftDescent N).extension 0)
    simp at this
    calc ‖(liftDescent N).extension 0‖
        = ‖liftQ N s - (liftQ N s - (liftDescent N).extension 0)‖ := by ring_nf
      _ ≤ ‖liftQ N s‖ + ‖liftQ N s - (liftDescent N).extension 0‖ := norm_sub_le _ _
      _ = ‖liftQ N s - (liftDescent N).extension 0‖ + ‖liftQ N s‖ := by ring
  linarith

public theorem norm_cuspQ_lt_cuspRadius {s : ℂ} (hs : s ∈ cuspHalfPlane N.height) :
    ‖cuspQ s‖ < cuspRadius N.height := by
  rw [norm_cuspQ, cuspRadius]
  apply Real.exp_lt_exp.mpr
  have hpi : 0 < Real.pi := Real.pi_pos
  have : N.height < s.im := hs
  nlinarith

/-- Every point deep enough in the cusp has a parabolic translate in the normalized horodisc. -/
public theorem exists_translate_mem_region {r : ℝ} (hr0 : 0 < r) :
    ∃ Y : ℝ, ∀ z : UpperHalfPlane, Y < z.im →
      ∃ k : ℤ, fuchsianSourceAction (g₀ ^ k) • z ∈ normalizedCuspRegion N r := by
  classical
  have hRpos : 0 < cuspRadius N.height := cuspRadius_pos _
  have hρpos : 0 < min (cuspRadius N.height) r := lt_min hRpos hr0
  have hanalytic : AnalyticOnNhd ℂ (liftDescent N).extension
      (Metric.ball 0 (cuspRadius N.height)) :=
    (liftDescent N).extension_holomorphic.analyticOnNhd Metric.isOpen_ball
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (cuspRadius N.height)) :=
    (convex_ball 0 _).isPreconnected
  have hnotconst : ¬ ∃ w, ∀ q ∈ Metric.ball (0 : ℂ) (cuspRadius N.height),
      (liftDescent N).extension q = w := by
    rintro ⟨w, hw⟩
    have hs₀ : (⟨0, N.height + 1⟩ : ℂ) ∈ cuspHalfPlane N.height := by
      change N.height < (⟨0, N.height + 1⟩ : ℂ).im
      simp
    have hmem : cuspQ (⟨0, N.height + 1⟩ : ℂ) ∈ Metric.ball (0 : ℂ) (cuspRadius N.height) := by
      simpa [Metric.mem_ball, dist_eq_norm] using norm_cuspQ_lt_cuspRadius N hs₀
    have h1 := hw _ hmem
    have h2 := hw 0 (Metric.mem_ball_self hRpos)
    rw [liftDescent_zero] at h2
    rw [(liftDescent N).factorization _ hs₀, ← h2] at h1
    exact liftQ_ne_zero N _ h1
  have hopen := (hanalytic.is_constant_or_isOpen hpre).resolve_left hnotconst
  have himage : IsOpen ((liftDescent N).extension ''
      Metric.ball 0 (min (cuspRadius N.height) r)) :=
    hopen _ (Metric.ball_subset_ball (min_le_left _ _)) Metric.isOpen_ball
  have hzero : (0 : ℂ) ∈ (liftDescent N).extension ''
      Metric.ball 0 (min (cuspRadius N.height) r) :=
    ⟨0, Metric.mem_ball_self hρpos, liftDescent_zero N⟩
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp himage 0 hzero
  obtain ⟨Y, hYpos, hY⟩ :=
    exists_exp_neg_lt hδ (show (0 : ℝ) < 2 * Real.pi / (1 + Real.sqrt 2) by positivity)
  refine ⟨Y, ?_⟩
  intro z hz
  have hsmallz : ‖sourceQ z‖ < δ := by
    rw [norm_sourceQ]
    have hrew : -(2 * Real.pi * (z.im / (1 + Real.sqrt 2))) =
        -(2 * Real.pi / (1 + Real.sqrt 2) * z.im) := by ring
    rw [hrew]
    exact hY _ hz
  obtain ⟨q, hqball, hqval⟩ := hsub
    (show sourceQ z ∈ Metric.ball (0 : ℂ) δ by
      simpa [Metric.mem_ball, dist_eq_norm] using hsmallz)
  have hqnorm : ‖q‖ < min (cuspRadius N.height) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hqball
  have hqne : q ≠ 0 := by
    intro h
    rw [h, liftDescent_zero] at hqval
    exact sourceQ_ne_zero z hqval.symm
  have hqheight : ‖q‖ < Real.exp (-(2 * Real.pi * N.height)) := by
    have h := lt_of_lt_of_le hqnorm (min_le_left _ _)
    rw [cuspRadius] at h
    have hrew : -2 * Real.pi * N.height = -(2 * Real.pi * N.height) := by ring
    rwa [hrew] at h
  obtain ⟨s, hsim, hsq⟩ := exists_cuspQ_preimage hqne hqheight
  have hsmem : s ∈ cuspHalfPlane N.height := hsim
  have hsource : s ∈ cuspSource N.height r := by
    refine ⟨hsmem, ?_⟩
    rw [hsq]
    exact lt_of_lt_of_le hqnorm (min_le_right _ _)
  have hfact : (liftDescent N).extension (cuspQ s) = liftQ N s :=
    (liftDescent N).factorization s hsmem
  rw [hsq, hqval] at hfact
  obtain ⟨k, hk⟩ := exists_zpow_g₀_of_sourceQ_eq (z := N.lift s) (w := z) hfact.symm
  exact ⟨k, by rw [hk]; exact ⟨s, hsource, rfl⟩⟩

/-! ## The separated horodisc -/

/-- The classical cusp-neighbourhood theorem for the explicit cofinite Fuchsian triangle group:
a sufficiently deep normalized horodisc is regular, has regular orbit closure, and is precisely
invariant under the parabolic cyclic subgroup. -/
public theorem exists_data (upperRadius : ℝ) (hupper : 0 < upperRadius) :
    Nonempty (EstablishedFuchsianCuspNeighborhood.Data N upperRadius) := by
  classical
  obtain ⟨M, hM1, hMreg⟩ :=
    exists_regular_height E.modularParameter.toTriangleUniformization rfl
  obtain ⟨ρ, hρpos, hρle, hρ⟩ := normalizedCuspRegion_im N (M + 2)
  have hheight : ∀ z ∈ normalizedCuspRegion N (min ρ upperRadius), M + 2 < z.im :=
    hρ _ (min_le_left _ _)
  refine ⟨{ radius := min ρ upperRadius
            radius_pos := lt_min hρpos hupper
            radius_le := (min_le_left _ _).trans hρle
            radius_le_upper := min_le_right _ _
            region_open := normalizedCuspRegion_isOpen N _
            region_regular := ?_
            orbitClosure_region_regular := ?_
            translates_meet_only_parabolic := ?_ }⟩
  · intro z hz
    exact hMreg z (by linarith [hheight z hz])
  · exact orbitClosure_regular E.modularParameter.toTriangleUniformization rfl rfl rfl
      (by linarith) _ hheight
  · rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
    have hwY := hheight w hw
    have hzY := hheight _ hz
    have hM0 : (0 : ℝ) < M + 2 := by linarith
    by_cases hc : (deltaBottomRow g).1 = 0
    · obtain ⟨B, _, hB⟩ := exists_isTranslationBy_of_bottomLeft_eq_zero hc
      exact exists_zpow_g₀_of_isTranslationBy hB
    · exfalso
      have hle := im_smul_le_one_div_im hc w
      have hlt : 1 / w.im < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      change (fuchsianSourceAction g • w).im ≤ 1 / w.im at hle
      have : (fuchsianSourceAction g • w).im < 1 := lt_of_le_of_lt hle hlt
      have hz' : M + 2 < (fuchsianSourceAction g • w).im := hzY
      linarith

/-- The oriented fundamental region lies in a fixed vertical strip. -/
public theorem abs_re_le_two_of_mem_orientedFundamentalRegion {z : UpperHalfPlane}
    (hz : z ∈ FuchsianTriangleCover.orientedFundamentalRegion) : |z.re| ≤ 2 := by
  have hsqrt : Real.sqrt 2 < 2 := sqrt_two_lt_two
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases hz with hz | hz
  · obtain ⟨hlow, hhigh, -⟩ := hz
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨hlow, hhigh, -⟩ := hz
    rw [abs_le]
    constructor <;> linarith

/-- Removing a precisely invariant horodisc from the explicit cofinite Fuchsian quotient leaves a
compact truncated quotient. -/
public theorem exists_compactTruncation {upperRadius : ℝ}
    (H : EstablishedFuchsianCuspNeighborhood.Data N upperRadius) :
    Nonempty (EstablishedFuchsianCuspNeighborhood.CompactTruncationData H) := by
  classical
  obtain ⟨Y, hY⟩ := exists_translate_mem_region N H.radius_pos
  refine ⟨{ core := {z : UpperHalfPlane | |z.re| ≤ 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ max Y 1}
            core_isCompact := isCompact_band _ _ _ (by norm_num)
            orbit_covers := ?_ }⟩
  intro z
  obtain ⟨g, hg⟩ := FuchsianTriangleCover.exists_smul_mem_orientedFundamentalRegion z
  by_cases hcase : max Y 1 < (fuchsianSourceAction g • z).im
  · obtain ⟨k, hk⟩ := hY _ (lt_of_le_of_lt (le_max_left _ _) hcase)
    refine ⟨g₀ ^ k * g, Or.inl ?_⟩
    rw [map_mul, mul_smul]
    exact hk
  · rw [not_lt] at hcase
    refine ⟨g, Or.inr ?_⟩
    refine ⟨abs_re_le_two_of_mem_orientedFundamentalRegion hg, ?_, hcase⟩
    rcases Periods.orientedFundamentalRegion_mem_cusp_or_compactCore hg with hcusp | hcore
    · have : (1 : ℝ) ≤ (fuchsianSourceAction g • z).im := hcusp
      linarith
    · exact hcore.2.1

end Lift

#print axioms SphereSixComplex.Geometry.FuchsianCuspNeighborhoodProof.exists_data

end SphereSixComplex.Geometry.FuchsianCuspNeighborhoodProof

end

end
