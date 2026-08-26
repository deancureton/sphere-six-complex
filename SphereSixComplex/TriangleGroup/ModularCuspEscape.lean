module

public import SphereSixComplex.TriangleGroup.ModularParameter
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Separation.Basic

/-!
# Escape of the modular cusp

An integral modular transform of a point high in the upper half-plane either preserves its
height or sends it below the reciprocal height.  Consequently all modular translates of a
sufficiently high point avoid any prescribed compact subset of the upper half-plane.
-/

open Matrix
open scoped MatrixGroups

namespace SphereSixComplex.TriangleGroup

/-- A modular matrix with zero lower-left entry preserves imaginary height. -/
public theorem modularToReal_smul_im_of_lowerLeft_eq_zero
    (A : ModularMatrix) (z : UpperHalfPlane) (hc : A 1 0 = 0) :
    (modularToReal A • z).im = z.im := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  have hd : (A 1 1) ^ 2 = 1 := by
    have hdet := A.property
    rw [Matrix.det_fin_two] at hdet
    rw [hc, mul_zero, sub_zero] at hdet
    rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet) with h | h
    · rw [h.2]
      norm_num
    · rw [h.2]
      norm_num
  simp only [show |((modularToReal A : GL (Fin 2) ℝ).det.val)| = 1 by
    simp [modularToReal], one_mul]
  rw [show UpperHalfPlane.denom (modularToReal A) z = (A 1 1 : ℂ) by
    simp [UpperHalfPlane.denom, modularToReal, hc]]
  rw [Complex.normSq_intCast]
  have hdreal : (A 1 1 : ℝ) ^ 2 = 1 := by exact_mod_cast hd
  rw [show (A 1 1 : ℝ) * (A 1 1 : ℝ) = 1 by simpa [pow_two] using hdreal]
  exact div_one _

/-- A modular matrix with nonzero integral lower-left entry sends height at most to its
reciprocal. -/
public theorem modularToReal_smul_im_le_inv_of_lowerLeft_ne_zero
    (A : ModularMatrix) (z : UpperHalfPlane) (hc : A 1 0 ≠ 0) :
    (modularToReal A • z).im ≤ 1 / z.im := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [show |((modularToReal A : GL (Fin 2) ℝ).det.val)| = 1 by
    simp [modularToReal], one_mul]
  have hc_abs_int : 1 ≤ |A 1 0| := Int.one_le_abs hc
  have hc_abs : (1 : ℝ) ≤ |(A 1 0 : ℝ)| := by exact_mod_cast hc_abs_int
  have hc_sq : (1 : ℝ) ≤ (A 1 0 : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (A 1 0 : ℝ)]
  have hlower : z.im ^ 2 ≤
      (((modularToReal A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * z.im) ^ 2 := by
    simp only [show (((modularToReal A : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) 1 0) = (A 1 0 : ℝ) by simp [modularToReal]]
    nlinarith [z.im_pos, sq_nonneg z.im]
  have hdenom : z.im ^ 2 ≤
      Complex.normSq (UpperHalfPlane.denom (modularToReal A) z) :=
    hlower.trans (UpperHalfPlane.c_mul_im_sq_le_normSq_denom (modularToReal A) z)
  calc
    z.im / Complex.normSq (UpperHalfPlane.denom (modularToReal A) z)
        ≤ z.im / z.im ^ 2 := by
          exact (div_le_div_iff_of_pos_left z.im_pos
            (UpperHalfPlane.normSq_denom_pos _ z.im_ne_zero)
            (sq_pos_of_pos z.im_pos)).2 hdenom
    _ = 1 / z.im := by field_simp

/-- All integral modular translates of a sufficiently high point avoid a fixed compact set. -/
public theorem exists_height_modularTranslates_avoid_compact
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H : ℝ, 0 < H ∧ ∀ (A : ModularMatrix) (z : UpperHalfPlane),
      H < z.im → modularToReal A • z ∉ K := by
  by_cases hne : K.Nonempty
  · let him : UpperHalfPlane → ℝ := fun z ↦ z.im
    have him_cont : Continuous him :=
      Complex.continuous_im.comp UpperHalfPlane.continuous_coe
    obtain ⟨zmin, hzminK, hzmin⟩ :=
      hK.exists_isMinOn hne him_cont.continuousOn
    obtain ⟨zmax, hzmaxK, hzmax⟩ :=
      hK.exists_isMaxOn hne him_cont.continuousOn
    refine ⟨max zmax.im (zmin.im)⁻¹ + 1, ?_, ?_⟩
    · have hmax : zmax.im ≤ max zmax.im (zmin.im)⁻¹ := le_max_left _ _
      linarith [zmax.im_pos]
    · intro A z hz hmem
      by_cases hc : A 1 0 = 0
      · have heq := modularToReal_smul_im_of_lowerLeft_eq_zero A z hc
        have hle : (modularToReal A • z).im ≤ zmax.im := hzmax hmem
        rw [heq] at hle
        have hmax : zmax.im ≤ max zmax.im (zmin.im)⁻¹ := le_max_left _ _
        linarith
      · have hle := modularToReal_smul_im_le_inv_of_lowerLeft_ne_zero A z hc
        have hmin : zmin.im ≤ (modularToReal A • z).im := hzmin hmem
        have hinvBound : (zmin.im)⁻¹ < z.im := by
          have hmax : (zmin.im)⁻¹ ≤ max zmax.im (zmin.im)⁻¹ := le_max_right _ _
          linarith
        have hinv : z.im⁻¹ < zmin.im :=
          (inv_lt_comm₀ z.im_pos zmin.im_pos).2 hinvBound
        rw [one_div] at hle
        linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro A z hz hmem
    exact hne ⟨modularToReal A • z, hmem⟩

end SphereSixComplex.TriangleGroup
