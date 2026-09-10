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

@[simp] theorem coe_unitDiscEquivUpperHalfPlane_apply (zeta : Circle)
    (z : Complex.UnitDisc) :
    ((unitDiscEquivUpperHalfPlane zeta z : UpperHalfPlane) : ℂ) = boundaryCayley zeta z := rfl

@[simp] theorem coe_unitDiscEquivUpperHalfPlane_symm_apply (zeta : Circle)
    (w : UpperHalfPlane) :
    ((unitDiscEquivUpperHalfPlane zeta).symm w : ℂ) = boundaryCayleyInv zeta w := rfl

/-- Positive real affine maps are precisely the elementary automorphisms of the upper half-plane
used below. -/
noncomputable def upperHalfPlaneAffineEquiv (a : ℝ) (ha : 0 < a) (b : ℝ) :
    UpperHalfPlane ≃ UpperHalfPlane where
  toFun w := ⟨(a : ℂ) * w + b, by simpa using mul_pos ha w.im_pos⟩
  invFun w := ⟨w / (a : ℂ) - (b / a : ℝ), by
    simp only [Complex.sub_im, Complex.div_im, ofReal_re, ofReal_im, mul_zero, zero_mul,
      sub_zero, Complex.normSq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    simpa using div_pos (mul_pos w.im_pos ha) (mul_pos ha ha)⟩
  left_inv w := by
    apply UpperHalfPlane.coe_injective
    push_cast
    field_simp [ha.ne']
    ring
  right_inv w := by
    apply UpperHalfPlane.coe_injective
    push_cast
    field_simp [ha.ne']
    ring

@[simp] theorem coe_upperHalfPlaneAffineEquiv_apply (a : ℝ) (ha : 0 < a) (b : ℝ)
    (w : UpperHalfPlane) :
    ((upperHalfPlaneAffineEquiv a ha b w : UpperHalfPlane) : ℂ) = (a : ℂ) * w + b := rfl

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

/-- Two marked circle triples have the same orientation when their finite Cayley coordinates have
the same strict order after the first point is sent to infinity. -/
def SameCircleTripleOrientation
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) : Prop :=
  (circleCayleyCoord s₀ s₁ < circleCayleyCoord s₀ s₂ ∧
      circleCayleyCoord t₀ t₁ < circleCayleyCoord t₀ t₂) ∨
    (circleCayleyCoord s₀ s₂ < circleCayleyCoord s₀ s₁ ∧
      circleCayleyCoord t₀ t₂ < circleCayleyCoord t₀ t₁)

/-- The positive affine scale carrying the two finite source coordinates to the target ones. -/
def circleTripleScale (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) : ℝ :=
  (circleCayleyCoord t₀ t₂ - circleCayleyCoord t₀ t₁) /
    (circleCayleyCoord s₀ s₂ - circleCayleyCoord s₀ s₁)

/-- The affine shift after the scale has been chosen. -/
def circleTripleShift (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) : ℝ :=
  circleCayleyCoord t₀ t₁ -
    circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ * circleCayleyCoord s₀ s₁

theorem circleTripleScale_pos {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    0 < circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ := by
  rcases horient with h | h
  · exact div_pos (sub_pos.mpr h.2) (sub_pos.mpr h.1)
  · exact div_pos_of_neg_of_neg (sub_neg.mpr h.2) (sub_neg.mpr h.1)

/-- The open-disc equivalence obtained by Cayley-transforming, applying the unique positive affine
map on the upper half-plane, and transforming back. -/
noncomputable def orientedCircleTripleUnitDiscEquiv
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    Complex.UnitDisc ≃ Complex.UnitDisc :=
  (unitDiscEquivUpperHalfPlane s₀).trans
    ((upperHalfPlaneAffineEquiv
      (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂)
      (circleTripleScale_pos horient)
      (circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂)).trans
      (unitDiscEquivUpperHalfPlane t₀).symm)

/-- The scalar extension of the preceding equivalence. The separate value at the Cayley pole is
the removable boundary value. -/
def orientedCircleTripleMap
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) (z : ℂ) : ℂ :=
  if z = s₀ then t₀ else
    boundaryCayleyInv t₀
      ((circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ z +
        circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂)

/-- The rational formula on the open disc, before filling in its boundary value at the pole. -/
def orientedCircleTripleOpenMap
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) (z : ℂ) : ℂ :=
  boundaryCayleyInv t₀
    ((circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ z +
      circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂)

theorem orientedCircleTripleMap_eq_openMap_of_ne
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) {z : ℂ} (hz : z ≠ s₀) :
    orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ z =
      orientedCircleTripleOpenMap s₀ s₁ s₂ t₀ t₁ t₂ z := by
  simp [orientedCircleTripleMap, orientedCircleTripleOpenMap, hz]

@[simp] theorem orientedCircleTripleMap_pole
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) :
    orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ s₀ = t₀ := by
  simp [orientedCircleTripleMap]

private theorem circleTriple_affine_cayley_first
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ s₁ +
        circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ =
      boundaryCayley t₀ t₁ := by
  rw [boundaryCayley_circle_eq_ofReal, boundaryCayley_circle_eq_ofReal]
  simp only [circleTripleShift]
  norm_cast
  ring

private theorem circleTriple_affine_cayley_second
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ s₂ +
        circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ =
      boundaryCayley t₀ t₂ := by
  rw [boundaryCayley_circle_eq_ofReal, boundaryCayley_circle_eq_ofReal]
  simp only [circleTripleShift, circleTripleScale]
  norm_cast
  have hden : circleCayleyCoord s₀ s₂ - circleCayleyCoord s₀ s₁ ≠ 0 := by
    rcases horient with h | h <;> linarith
  field_simp [hden]
  ring

theorem orientedCircleTripleMap_first
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂)
    (hs₁ : s₁ ≠ s₀) (ht₁ : t₁ ≠ t₀) :
    orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ s₁ = t₁ := by
  rw [orientedCircleTripleMap_eq_openMap_of_ne _ _ _ _ _ _
      (fun h ↦ hs₁ (Circle.coe_injective h)),
    orientedCircleTripleOpenMap, circleTriple_affine_cayley_first horient,
    boundaryCayleyInv_boundaryCayley t₀.coe_ne_zero
      (fun h ↦ ht₁ (Circle.coe_injective h))]

theorem orientedCircleTripleMap_second
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂)
    (hs₂ : s₂ ≠ s₀) (ht₂ : t₂ ≠ t₀) :
    orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ s₂ = t₂ := by
  rw [orientedCircleTripleMap_eq_openMap_of_ne _ _ _ _ _ _
      (fun h ↦ hs₂ (Circle.coe_injective h)),
    orientedCircleTripleOpenMap, circleTriple_affine_cayley_second horient,
    boundaryCayleyInv_boundaryCayley t₀.coe_ne_zero
      (fun h ↦ ht₂ (Circle.coe_injective h))]

theorem coe_orientedCircleTripleUnitDiscEquiv_apply
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂)
    (z : Complex.UnitDisc) :
    (orientedCircleTripleUnitDiscEquiv s₀ s₁ s₂ t₀ t₁ t₂ horient z : ℂ) =
      orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ z := by
  rw [orientedCircleTripleMap, if_neg]
  · rfl
  · intro hz
    have hn := congrArg norm hz
    have : ‖(z : ℂ)‖ = 1 := by simpa [Circle.norm_coe] using hn
    exact z.norm_ne_one this

theorem orientedCircleTripleMap_bijOn_ball
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    BijOn (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (ball (0 : ℂ) 1) (ball 0 1) :=
  TauCeti.bijOn_ball_of_unitDiscEquiv
    (orientedCircleTripleUnitDiscEquiv s₀ s₁ s₂ t₀ t₁ t₂ horient)
    (coe_orientedCircleTripleUnitDiscEquiv_apply s₀ s₁ s₂ t₀ t₁ t₂ horient)

theorem differentiableAt_boundaryCayley {zeta z : ℂ} (hz : zeta - z ≠ 0) :
    DifferentiableAt ℂ (boundaryCayley zeta) z := by
  unfold boundaryCayley
  fun_prop

theorem differentiableAt_boundaryCayleyInv {zeta w : ℂ} (hw : w + Complex.I ≠ 0) :
    DifferentiableAt ℂ (boundaryCayleyInv zeta) w := by
  unfold boundaryCayleyInv
  fun_prop

theorem orientedCircleTripleOpenMap_differentiableOn_ball
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    DifferentiableOn ℂ (orientedCircleTripleOpenMap s₀ s₁ s₂ t₀ t₁ t₂)
      (ball (0 : ℂ) 1) := by
  intro z hz
  have hznorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hsub : (s₀ : ℂ) - z ≠ 0 := by
    intro h
    have heq : (s₀ : ℂ) = z := sub_eq_zero.mp h
    have hn := congrArg norm heq
    rw [Circle.norm_coe] at hn
    linarith
  have hc : DifferentiableAt ℂ (boundaryCayley s₀) z :=
    differentiableAt_boundaryCayley hsub
  let a : ℝ := circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂
  let b : ℝ := circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂
  let w : ℂ := (a : ℂ) * boundaryCayley s₀ z + b
  have ha : 0 < a := circleTripleScale_pos horient
  have hwim : 0 < w.im := by
    have hcim : 0 < (boundaryCayley (s₀ : ℂ) z).im :=
      boundaryCayley_im_pos (Circle.norm_coe s₀) hznorm
    change 0 < ((a : ℂ) * boundaryCayley s₀ z + (b : ℂ)).im
    simpa [Complex.mul_im] using mul_pos ha hcim
  have hwden : w + Complex.I ≠ 0 := by
    intro hzero
    have hi := congrArg Complex.im hzero
    change w.im + 1 = 0 at hi
    linarith
  have haff : DifferentiableAt ℂ
      (fun u : ℂ ↦ (a : ℂ) * boundaryCayley s₀ u + b) z :=
    ((differentiableAt_const (c := (a : ℂ))).mul hc).add
      (differentiableAt_const (c := (b : ℂ)))
  have hout : DifferentiableAt ℂ (boundaryCayleyInv t₀) w :=
    differentiableAt_boundaryCayleyInv hwden
  have houter :
      (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ z +
          circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ + Complex.I ≠ 0 := by
    simpa only [a, b, w] using hwden
  have hcWithin : DifferentiableWithinAt ℂ (boundaryCayley s₀) (ball (0 : ℂ) 1) z := by
    unfold boundaryCayley
    apply DifferentiableWithinAt.div
    · fun_prop
    · fun_prop
    · exact hsub
  have haffWithin : DifferentiableWithinAt ℂ
      (fun u : ℂ ↦
        (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * boundaryCayley s₀ u +
          circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂)
      (ball (0 : ℂ) 1) z := by
    exact ((differentiableWithinAt_const (c :=
      (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ))).mul hcWithin).add
        (differentiableWithinAt_const (c :=
          (circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ : ℂ)))
  unfold orientedCircleTripleOpenMap boundaryCayleyInv
  apply DifferentiableWithinAt.div
  · exact ((differentiableWithinAt_const (c := (t₀ : ℂ))).mul
      (haffWithin.sub (differentiableWithinAt_const (c := Complex.I))))
  · exact haffWithin.add (differentiableWithinAt_const (c := Complex.I))
  · exact houter

theorem orientedCircleTripleMap_differentiableOn_ball
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    DifferentiableOn ℂ (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (ball (0 : ℂ) 1) := by
  apply (orientedCircleTripleOpenMap_differentiableOn_ball
    s₀ s₁ s₂ t₀ t₁ t₂ horient).congr
  intro z hz
  exact orientedCircleTripleMap_eq_openMap_of_ne (z := z) s₀ s₁ s₂ t₀ t₁ t₂
    (fun heq ↦ by
      have hn := congrArg norm heq
      have hzlt : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
      rw [Circle.norm_coe] at hn
      linarith)

theorem orientedCircleTripleMap_invFunOn_differentiableOn_ball
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle)
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    DifferentiableOn ℂ
      (Function.invFunOn
        (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂) (ball (0 : ℂ) 1))
      (ball (0 : ℂ) 1) := by
  have hbij := orientedCircleTripleMap_bijOn_ball s₀ s₁ s₂ t₀ t₁ t₂ horient
  have hinv := TauCeti.DifferentiableOn.invFunOn
    (orientedCircleTripleMap_differentiableOn_ball s₀ s₁ s₂ t₀ t₁ t₂ horient)
    isOpen_ball hbij.injOn
  rwa [hbij.image_eq] at hinv



end SphereSixComplex.Periods.SourceChamberTopology
