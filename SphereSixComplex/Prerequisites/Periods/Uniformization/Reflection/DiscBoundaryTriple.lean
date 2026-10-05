module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import all Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import all Mathlib.Analysis.Complex.UnitDisc.Basic
public import TauCeti.Analysis.Complex.UnitDisc.Basic
import all TauCeti.Analysis.Complex.UnitDisc.Basic
public import TauCeti.Analysis.Complex.Conformal.InverseFunction
import all TauCeti.Analysis.Complex.Conformal.InverseFunction

@[expose] public section

open Complex Metric Set

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-! Elementary Cayley coordinates for marked triples on the unit circle. -/

/-- The Cayley transform with pole `zeta` on the unit circle. -/
def boundaryCayley (zeta z : ℂ) : ℂ :=
  Complex.I * (zeta + z) / (zeta - z)

/-- The inverse Cayley transform, with `zeta` as the point at infinity. -/
def boundaryCayleyInv (zeta w : ℂ) : ℂ :=
  zeta * (w - Complex.I) / (w + Complex.I)

theorem boundaryCayleyInv_boundaryCayley {zeta z : ℂ}
    (hzeta : zeta ≠ 0) (hz : z ≠ zeta) :
    boundaryCayleyInv zeta (boundaryCayley zeta z) = z := by
  unfold boundaryCayleyInv boundaryCayley
  have hsub : zeta - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp [hsub, hzeta, hI]
  ring_nf

theorem boundaryCayley_boundaryCayleyInv {zeta w : ℂ}
    (hzeta : zeta ≠ 0) (hw : w ≠ -Complex.I) :
    boundaryCayley zeta (boundaryCayleyInv zeta w) = w := by
  unfold boundaryCayleyInv boundaryCayley
  have hadd : w + Complex.I ≠ 0 := by
    simpa [add_eq_zero_iff_eq_neg] using hw
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp [hadd, hzeta, hI]
  ring_nf

theorem boundaryCayley_im (zeta z : ℂ) :
    (boundaryCayley zeta z).im =
      (Complex.normSq zeta - Complex.normSq z) / Complex.normSq (zeta - z) := by
  unfold boundaryCayley
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  simp only [Complex.normSq_apply]
  ring

theorem boundaryCayley_im_pos {zeta z : ℂ} (hzeta : ‖zeta‖ = 1) (hz : ‖z‖ < 1) :
    0 < (boundaryCayley zeta z).im := by
  rw [boundaryCayley_im]
  have hne : zeta - z ≠ 0 := by
    intro h
    have : zeta = z := sub_eq_zero.mp h
    rw [this] at hzeta
    linarith
  have hden : 0 < Complex.normSq (zeta - z) := Complex.normSq_pos.mpr hne
  have hnzeta : Complex.normSq zeta = 1 := by
    rw [Complex.normSq_eq_norm_sq, hzeta]
    norm_num
  have hnz : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [hnzeta]
  exact div_pos (sub_pos.mpr hnz) hden

theorem boundaryCayley_im_eq_zero {zeta z : ℂ}
    (hzeta : ‖zeta‖ = 1) (hz : ‖z‖ = 1) :
    (boundaryCayley zeta z).im = 0 := by
  rw [boundaryCayley_im, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    hzeta, hz]
  simp

theorem boundaryCayleyInv_norm_lt_one {zeta w : ℂ}
    (hzeta : ‖zeta‖ = 1) (hw : 0 < w.im) :
    ‖boundaryCayleyInv zeta w‖ < 1 := by
  unfold boundaryCayleyInv
  rw [norm_div, norm_mul, hzeta, one_mul]
  have hadd : w + Complex.I ≠ 0 := by
    intro hzero
    have : w = -Complex.I := add_eq_zero_iff_eq_neg.mp hzero
    rw [this] at hw
    norm_num at hw
  rw [div_lt_one (norm_pos_iff.mpr hadd)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
    Complex.sub_im, Complex.I_im, Complex.add_re, add_zero, Complex.add_im]
  nlinarith

/-- Cayley coordinates identify the open unit disc with the upper half-plane. -/
noncomputable def unitDiscEquivUpperHalfPlane (zeta : Circle) :
    Complex.UnitDisc ≃ UpperHalfPlane where
  toFun z := ⟨boundaryCayley zeta z,
    boundaryCayley_im_pos (Circle.norm_coe zeta) z.norm_lt_one⟩
  invFun w := Complex.UnitDisc.mk (boundaryCayleyInv zeta w)
    (boundaryCayleyInv_norm_lt_one (Circle.norm_coe zeta) w.im_pos)
  left_inv z := by
    apply Complex.UnitDisc.coe_injective
    exact boundaryCayleyInv_boundaryCayley zeta.coe_ne_zero
      (fun h => z.norm_ne_one (by
        have hn := congrArg norm h
        simpa [Circle.norm_coe] using hn))
  right_inv w := by
    apply UpperHalfPlane.coe_injective
    exact boundaryCayley_boundaryCayleyInv zeta.coe_ne_zero
      (fun h => by
        have hi := congrArg Complex.im h
        norm_num at hi
        linarith [w.im_pos])





/-- The real Cayley coordinate of a circle point, with another point chosen as infinity. -/
def circleCayleyCoord (pole z : Circle) : ℝ :=
  (boundaryCayley pole z).re

theorem boundaryCayley_circle_eq_ofReal (pole z : Circle) :
    boundaryCayley pole z = (circleCayleyCoord pole z : ℝ) := by
  apply Complex.ext
  · rfl
  · simpa using boundaryCayley_im_eq_zero (Circle.norm_coe pole) (Circle.norm_coe z)

theorem circleCayleyCoord_ne {pole z w : Circle} (hz : z ≠ pole) (hw : w ≠ pole)
    (hzw : z ≠ w) : circleCayleyCoord pole z ≠ circleCayleyCoord pole w := by
  intro hcoord
  have hcayley : boundaryCayley pole z = boundaryCayley pole w := by
    rw [boundaryCayley_circle_eq_ofReal, boundaryCayley_circle_eq_ofReal, hcoord]
  have hinv := congrArg (boundaryCayleyInv (pole : ℂ)) hcayley
  rw [boundaryCayleyInv_boundaryCayley pole.coe_ne_zero
      (fun h ↦ hz (Circle.coe_injective h)),
    boundaryCayleyInv_boundaryCayley pole.coe_ne_zero
      (fun h ↦ hw (Circle.coe_injective h))] at hinv
  exact hzw (Circle.coe_injective hinv)
















theorem differentiableAt_boundaryCayley {zeta z : ℂ} (hz : zeta - z ≠ 0) :
    DifferentiableAt ℂ (boundaryCayley zeta) z := by
  unfold boundaryCayley
  fun_prop

theorem differentiableAt_boundaryCayleyInv {zeta w : ℂ} (hw : w + Complex.I ≠ 0) :
    DifferentiableAt ℂ (boundaryCayleyInv zeta) w := by
  unfold boundaryCayleyInv
  fun_prop






end SphereSixComplex.Periods.SourceChamberTopology
