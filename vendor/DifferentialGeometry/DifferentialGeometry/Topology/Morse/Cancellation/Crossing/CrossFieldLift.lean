module

public import DifferentialGeometry.Topology.Morse.Cancellation.Crossing.CrossFieldArc

@[expose] public section

set_option autoImplicit false

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace
open DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace CrossField

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  {f : M → ℝ} {a' b' : ℝ} {p q : M}

def liftScale (c₀ s a : ℝ) : ℝ := Real.sqrt ((c₀ - s) + Real.sqrt ((c₀ - s) ^ 2 + a))

def modelLift {k : ℕ} (hk : k ≤ n) (c₀ s : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  recombine hk
    ((liftScale c₀ s (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) / ‖negPart hk y‖) • negPart hk y)
    ((‖negPart hk y‖ / liftScale c₀ s (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2)) • posPart hk y)

section ModelLift

variable {k : ℕ} (hk : k ≤ n)

theorem modelLift_spec {c₀ s : ℝ} (hs : s < c₀) {y : Fin n → ℝ} (hu : negPart hk y ≠ 0) :
    morseNormalForm hk c₀ (modelLift hk c₀ s y) = s ∧
      ‖negPart hk (modelLift hk c₀ s y)‖⁻¹ • negPart hk (modelLift hk c₀ s y) =
        ‖negPart hk y‖⁻¹ • negPart hk y ∧
      ‖negPart hk (modelLift hk c₀ s y)‖ • posPart hk (modelLift hk c₀ s y) =
        ‖negPart hk y‖ • posPart hk y ∧
      (morseNormalForm hk c₀ y < c₀ → modelLift hk c₀ (morseNormalForm hk c₀ y) y = y) := by
  have hsplit := DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split hk
  have hA : 0 < ‖negPart hk y‖ := norm_pos_iff.mpr hu
  have hgen : ∀ s' : ℝ, s' < c₀ →
      0 < liftScale c₀ s' (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) ∧
      liftScale c₀ s' (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) ^ 2 =
        (c₀ - s') + Real.sqrt ((c₀ - s') ^ 2 + ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) ∧
      Real.sqrt ((c₀ - s') ^ 2 + ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) ^ 2 =
        (c₀ - s') ^ 2 + ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2 ∧
      0 ≤ Real.sqrt ((c₀ - s') ^ 2 + ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) := by
    intro s' hs'
    have hR0 := Real.sqrt_nonneg ((c₀ - s') ^ 2 + ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2)
    refine ⟨Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith),
      Real.sq_sqrt (by positivity), hR0⟩
  have hneg : ∀ s' : ℝ, negPart hk (modelLift hk c₀ s' y) =
      (liftScale c₀ s' (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2) / ‖negPart hk y‖) •
        negPart hk y := by
    intro s'
    unfold modelLift
    exact ModelField.negPart_recombine hk _ _
  have hpos : ∀ s' : ℝ, posPart hk (modelLift hk c₀ s' y) =
      (‖negPart hk y‖ / liftScale c₀ s' (‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2)) •
        posPart hk y := by
    intro s'
    unfold modelLift
    exact ModelField.posPart_recombine hk _ _
  obtain ⟨hL, hL2, hR2, hR0⟩ := hgen s hs
  have hnegs := hneg s
  have hposs := hpos s
  set A := ‖negPart hk y‖ with hAdef
  set B := ‖posPart hk y‖ with hBdef
  set L := liftScale c₀ s (A ^ 2 * B ^ 2) with hLdef
  set R := Real.sqrt ((c₀ - s) ^ 2 + A ^ 2 * B ^ 2) with hRdef
  have hnormneg : ‖negPart hk (modelLift hk c₀ s y)‖ = L := by
    rw [hnegs, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hL hA)]
    exact div_mul_cancel₀ L hA.ne'
  have hnormpos : ‖posPart hk (modelLift hk c₀ s y)‖ = A / L * B := by
    rw [hposs, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hA hL)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit, hnormneg, hnormpos]
    have hLne : L ≠ 0 := hL.ne'
    have hB0 : 0 ≤ B := norm_nonneg _
    have hkey : A ^ 2 * B ^ 2 = L ^ 2 * L ^ 2 - 2 * (c₀ - s) * L ^ 2 := by
      rw [hL2]; nlinarith [hR2]
    field_simp
    linear_combination hkey
  · rw [hnormneg, hnegs, smul_smul]
    congr 1
    field_simp
  · rw [hnormneg, hposs, smul_smul]
    congr 1
    field_simp
  · intro hy
    set s₀ := morseNormalForm hk c₀ y with hs₀def
    have hs₀ : s₀ = c₀ + (1 / 2) * (B ^ 2 - A ^ 2) := hsplit c₀ y
    obtain ⟨hL', hL2', hR2', hR0'⟩ := hgen s₀ hy
    have hB0 : 0 ≤ B := norm_nonneg _
    have hRval : Real.sqrt ((c₀ - s₀) ^ 2 + A ^ 2 * B ^ 2) = (A ^ 2 + B ^ 2) / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
      rw [hs₀]; ring
    have hLA : liftScale c₀ s₀ (A ^ 2 * B ^ 2) = A := by
      have h2 : liftScale c₀ s₀ (A ^ 2 * B ^ 2) ^ 2 = A ^ 2 := by
        rw [hL2', hRval, hs₀]; ring
      nlinarith [hL', hA, sq_nonneg (liftScale c₀ s₀ (A ^ 2 * B ^ 2) - A),
        sq_nonneg (liftScale c₀ s₀ (A ^ 2 * B ^ 2) + A)]
    unfold modelLift
    rw [← hAdef, ← hBdef, hLA, div_self hA.ne', one_smul, one_smul]
    exact DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose hk y

theorem modelLift_congr {c₀ s : ℝ} {y y' : Fin n → ℝ} (hu : negPart hk y ≠ 0)
    (hu' : negPart hk y' ≠ 0)
    (hdir : ‖negPart hk y‖⁻¹ • negPart hk y = ‖negPart hk y'‖⁻¹ • negPart hk y')
    (hprod : ‖negPart hk y‖ • posPart hk y = ‖negPart hk y'‖ • posPart hk y') :
    modelLift hk c₀ s y = modelLift hk c₀ s y' := by
  have _hne : negPart hk y ≠ 0 ∧ negPart hk y' ≠ 0 := ⟨hu, hu'⟩
  have hA : ‖negPart hk y‖ ^ 2 * ‖posPart hk y‖ ^ 2 =
      ‖negPart hk y'‖ ^ 2 * ‖posPart hk y'‖ ^ 2 := by
    have h1 := congrArg (fun w => ‖w‖ ^ 2) hprod
    simp only [norm_smul, norm_norm, mul_pow] at h1
    exact h1
  have key : ∀ z : Fin n → ℝ, modelLift hk c₀ s z =
      recombine hk
        (liftScale c₀ s (‖negPart hk z‖ ^ 2 * ‖posPart hk z‖ ^ 2) •
          (‖negPart hk z‖⁻¹ • negPart hk z))
        ((liftScale c₀ s (‖negPart hk z‖ ^ 2 * ‖posPart hk z‖ ^ 2))⁻¹ •
          (‖negPart hk z‖ • posPart hk z)) := by
    intro z
    unfold modelLift
    rw [smul_smul, smul_smul, div_eq_mul_inv, div_eq_inv_mul]
  rw [key y, key y', hA, hdir, hprod]

theorem contDiffOn_modelLift (c₀ : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => modelLift hk c₀ z.1 z.2)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} := by
  have hneg : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => negPart hk z.2)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} :=
    ((ModelField.negPartL hk).contDiff.comp contDiff_snd).contDiffOn
  have hpos : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => posPart hk z.2)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} :=
    ((ModelField.posPartL hk).contDiff.comp contDiff_snd).contDiffOn
  have hN : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => ‖negPart hk z.2‖)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} :=
    hneg.norm ℝ (fun z hz => hz.2)
  have hP2 : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => ‖posPart hk z.2‖ ^ 2)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} :=
    ((contDiff_norm_sq ℝ).comp
      ((ModelField.posPartL hk).contDiff.comp contDiff_snd)).contDiffOn
  have hN0 : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < c₀ ∧ negPart hk z.2 ≠ 0},
      ‖negPart hk z.2‖ ≠ 0 := fun z hz => norm_ne_zero_iff.mpr hz.2
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => c₀ - z.1)
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} :=
    (contDiff_const.sub contDiff_fst).contDiffOn
  have hin : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      Real.sqrt ((c₀ - z.1) ^ 2 + ‖negPart hk z.2‖ ^ 2 * ‖posPart hk z.2‖ ^ 2))
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} := by
    refine ((hc.pow 2).add ((hN.pow 2).mul hP2)).sqrt ?_
    intro z hz
    have h1 : 0 < c₀ - z.1 := sub_pos.mpr hz.1
    positivity
  have hL : ContDiffOn ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      liftScale c₀ z.1 (‖negPart hk z.2‖ ^ 2 * ‖posPart hk z.2‖ ^ 2))
      {z | z.1 < c₀ ∧ negPart hk z.2 ≠ 0} := by
    refine (hc.add hin).sqrt ?_
    intro z hz
    have h1 : 0 < c₀ - z.1 := sub_pos.mpr hz.1
    positivity
  have hL0 : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < c₀ ∧ negPart hk z.2 ≠ 0},
      liftScale c₀ z.1 (‖negPart hk z.2‖ ^ 2 * ‖posPart hk z.2‖ ^ 2) ≠ 0 := by
    intro z hz
    have h1 : 0 < c₀ - z.1 := sub_pos.mpr hz.1
    unfold liftScale
    positivity
  have hA := (hL.div hN hN0).smul hneg
  have hB := (hN.div hL hL0).smul hpos
  have hR := (ModelField.recombineL hk).contDiff.comp_contDiffOn (hA.prodMk hB)
  refine hR.congr ?_
  intro z _
  simp only [Function.comp_apply, ModelField.recombineL_apply, modelLift]
  rfl

theorem hasDerivAt_modelLift {c₀ s r₀ : ℝ} (hr₀ : 0 < r₀) (hs : s < c₀) {y : Fin n → ℝ}
    (hu : negPart hk y ≠ 0) (hbig : r₀ / 2 ≤ morseNorm n (modelLift hk c₀ s y)) :
    HasDerivAt (fun s => modelLift hk c₀ s y)
      (-(ModelField.modelField k r₀ (modelLift hk c₀ s y))) s := by
  set u := negPart hk y with hu_def
  set v := posPart hk y with hv_def
  set w := ‖u‖ with hw_def
  set a := ‖u‖ ^ 2 * ‖v‖ ^ 2 with ha_def
  have hw : 0 < w := norm_pos_iff.2 hu
  have ha : 0 ≤ a := by positivity
  set D := c₀ - s with hD_def
  have hD : 0 < D := by rw [hD_def]; linarith
  set R := Real.sqrt (D ^ 2 + a) with hR_def
  have hR2 : R ^ 2 = D ^ 2 + a := Real.sq_sqrt (by positivity)
  have hDR : D ≤ R := Real.le_sqrt_of_sq_le (by linarith)
  have hR : 0 < R := lt_of_lt_of_le hD hDR
  set L := liftScale c₀ s a with hL_def
  have hL2 : L ^ 2 = D + R := Real.sq_sqrt (by linarith)
  have hL : 0 < L := Real.sqrt_pos.2 (by linarith)
  have hDs : HasDerivAt (fun t : ℝ => c₀ - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub c₀
  have hRs : HasDerivAt (fun t : ℝ => Real.sqrt ((c₀ - t) ^ 2 + a)) (-D / R) s := by
    have h1 : HasDerivAt (fun t : ℝ => (c₀ - t) ^ 2 + a) (2 * D * (-1)) s := by
      have := (hDs.pow 2).add_const a
      convert this using 1
      simp [hD_def]
    have h2 := h1.sqrt (by positivity)
    convert h2 using 1
    rw [← hR_def]
    field_simp
  have hLs : HasDerivAt (fun t : ℝ => liftScale c₀ t a) (-L / (2 * R)) s := by
    have h1 : HasDerivAt (fun t : ℝ => (c₀ - t) + Real.sqrt ((c₀ - t) ^ 2 + a)) (-1 + -D / R) s :=
      hDs.add hRs
    have h2 := h1.sqrt (by rw [← hD_def, ← hR_def]; linarith)
    have hval : (-1 + -D / R) / (2 * Real.sqrt (c₀ - s + Real.sqrt ((c₀ - s) ^ 2 + a))) =
        -L / (2 * R) := by
      change (-1 + -D / R) / (2 * L) = -L / (2 * R)
      field_simp
      nlinarith [hL2]
    rw [hval] at h2
    exact h2
  have hg : HasDerivAt (fun t : ℝ => liftScale c₀ t a / w) ((-L / (2 * R)) / w) s :=
    hLs.div_const w
  have hh : HasDerivAt (fun t : ℝ => w / liftScale c₀ t a)
      (-(w * (-L / (2 * R))) / L ^ 2) s := by
    have := (hasDerivAt_const s w).div hLs hL.ne'
    convert this using 1
    simp only [zero_mul, zero_sub]
    rfl
  have hpair : HasDerivAt
      (fun t : ℝ => ((liftScale c₀ t a / w) • u, (w / liftScale c₀ t a) • v))
      (((-L / (2 * R)) / w) • u, (-(w * (-L / (2 * R))) / L ^ 2) • v) s :=
    (hg.smul_const u).prodMk (hh.smul_const v)
  have hcomp := (ModelField.recombineL hk).hasFDerivAt.comp_hasDerivAt s hpair
  have hfun : (fun t => modelLift hk c₀ t y) =
      (ModelField.recombineL hk) ∘
        (fun t : ℝ => ((liftScale c₀ t a / w) • u, (w / liftScale c₀ t a) • v)) := by
    funext t
    simp only [Function.comp_apply, ModelField.recombineL_apply]
    rfl
  rw [hfun]
  convert hcomp using 1
  rw [ModelField.recombineL_apply]
  have hlift : modelLift hk c₀ s y = recombine hk ((L / w) • u) ((w / L) • v) := rfl
  have hnormsq : morseNorm n (modelLift hk c₀ s y) ^ 2 = 2 * R := by
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart hk,
      hlift, ModelField.negPart_recombine, ModelField.posPart_recombine, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos hL hw),
      abs_of_pos (div_pos hw hL)]
    have hv2 : w ^ 2 * ‖v‖ ^ 2 = a := rfl
    field_simp
    rw [← hw_def]
    linear_combination (w ^ 2 * (L ^ 2 + D - R)) * hL2 - w ^ 2 * hR2 + w ^ 2 * hv2
  have htheta : ModelField.theta r₀ (modelLift hk c₀ s y) = (2 * R)⁻¹ := by
    rw [ModelField.theta_eq hr₀ hbig, hnormsq]
  have hneg : negPart hk (-(ModelField.modelField k r₀ (modelLift hk c₀ s y))) =
      ((-L / (2 * R)) / w) • u := by
    rw [ModelField.negPart_neg, ModelField.negPart_modelField, htheta, hlift,
      ModelField.negPart_recombine, smul_smul, ← neg_smul]
    congr 1
    field_simp
  have hpos : posPart hk (-(ModelField.modelField k r₀ (modelLift hk c₀ s y))) =
      (-(w * (-L / (2 * R))) / L ^ 2) • v := by
    rw [ModelField.posPart_neg, ModelField.posPart_modelField, neg_neg, htheta, hlift,
      ModelField.posPart_recombine, smul_smul]
    congr 1
    field_simp
  rw [← hneg, ← hpos,
    DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]

end ModelLift

namespace TransverseCancellingPair

variable [DecidableEq M] (c : TransverseCancellingPair I f a' b' p q)

def ρq : ℝ := Real.sqrt (5 * c.ε / 2)

def cq : ℝ := f q - c.ε

def fb : ℝ := f p + c.ε

def βmax : ℝ := min (min (c.ε / 16) ((f q - f p - 2 * c.ε) / 16)) ((2 * c.ε - c.dp.r₀ ^ 2) / 16)

def sqSum : ℝ := 2 * (c.cq - c.fb) + 4 * c.ε

def pArc (y : Fin n → ℝ) : ℝ := ⟪posPart c.dp.hk y, c.e₁⟫

def pPerp (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n - c.dp.k)) :=
  posPart c.dp.hk y - c.pArc y • c.e₁

def pQuad (η : ℝ) (y : Fin n → ℝ) : ℝ := ‖negPart c.dp.hk y‖ ^ 2 - η * ‖c.pPerp y‖ ^ 2

def qArc (y : Fin n → ℝ) : ℝ := ⟪negPart c.dq.hk y, c.u₀⟫

def qPerp (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin c.dq.k) := negPart c.dq.hk y - c.qArc y • c.u₀

def qQuad (η : ℝ) (y : Fin n → ℝ) : ℝ := η * ‖c.qPerp y‖ ^ 2 - ‖posPart c.dq.hk y‖ ^ 2

def kH : ℝ := c.ρq / Real.sqrt (c.sqSum - c.ρq ^ 2) + 1

def qHeightProfile (σ : ℝ) : ℝ :=
  Real.sqrt (c.sqSum - σ ^ 2) +
    c.kH * (Real.sqrt (2 * c.ε) - σ) * CancelModel.cut (Real.sqrt (2 * c.ε) / 2)
      (Real.sqrt (2 * c.ε)) σ

def κ (β s : ℝ) : ℝ := 1 - CancelModel.cut (c.fb - β) (c.fb + β) s

def pRayAt (s : ℝ) : Fin n → ℝ := recombine c.dp.hk 0 (Real.sqrt (2 * (s - f p)) • c.e₁)

def qBall : Set M := c.dq.χ '' {y | morseNorm n y < c.ρq}

def qTube : Set M :=
  {x | f x < c.cq ∧ x ∈ c.D.regularFlowDomain c.cq ∧
    c.D.π c.cq x ∈ c.dq.χ '' {y | morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0}}

def qDom : Set M := c.qBall ∪ c.qTube

open Classical in
def qExtendedChart (x : M) : Fin n → ℝ :=
  if x ∈ c.qBall then c.dq.χ.symm x
  else modelLift c.dq.hk (f q) (f x) (c.dq.χ.symm (c.D.π c.cq x))

def blendedQuadraticFunction (η β : ℝ) (x : M) : ℝ :=
  (1 - c.κ β (f x)) * c.pQuad η (c.dp.χ.symm x) + c.κ β (f x) * c.qQuad η (c.qExtendedChart x)

def blendedArcCoordinate (β : ℝ) (x : M) : ℝ :=
  (1 - c.κ β (f x)) * c.pArc (c.dp.χ.symm x) + c.κ β (f x) * c.qHeightProfile (c.qArc (c.qExtendedChart x))

end TransverseCancellingPair

namespace TransverseCancellingPair

variable [DecidableEq M] (c : TransverseCancellingPair I f a' b' p q)

theorem unit_dirs : ‖c.e₁‖ = 1 ∧ ‖c.u₀‖ = 1 ∧
    c.y₀ = recombine c.dp.hk 0 (Real.sqrt (2 * c.ε) • c.e₁) := by
  have hw0 : c.w₀ ≠ 0 := c.hw₀.1
  have hland := c.hw₀.2
  have hrm := c.D.hrm q (mem_pair_right p q)
  have hrmpos := c.D.rm_pos q (mem_pair_right p q)
  have hεR : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have h1 : c.D.rm q (mem_pair_right p q) ^ 2 ≤ c.dq.R ^ 2 := by
      have := hrm.2
      exact pow_le_pow_left₀ hrmpos.le this 2
    linarith [c.hrmq, c.hε]
  have hfl : f (c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀) = f p + c.ε :=
    GradientLikeStrip.f_landing (mem_pair_left p q) c.hf.smooth c.hε c.hε hεR c.hc₁.le c.hc₂.le
      c.hlev hw0
  have hland2 : c.D.landing p (mem_pair_right p q) c.ε c.c c.ε c.w₀ ∈
      c.dp.χ '' {y | morseNorm n y ≤ c.dp.R} :=
    image_mono (fun y (hy : morseNorm n y < c.dp.R) => le_of_lt hy) hland
  have hnf : morseNormalForm c.dp.hk (f p) c.y₀ = f p + c.ε := by
    rw [← hfl]
    exact (c.dp.f_eq_nf_symm hland2).symm
  rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hnf
  have hsq : ‖posPart c.dp.hk c.y₀‖ ^ 2 = 2 * c.ε + ‖negPart c.dp.hk c.y₀‖ ^ 2 := by linarith
  have hvpos : 0 < ‖posPart c.dp.hk c.y₀‖ := by
    have h2 : 0 < ‖posPart c.dp.hk c.y₀‖ ^ 2 := by
      rw [hsq]; nlinarith [c.hε, sq_nonneg ‖negPart c.dp.hk c.y₀‖]
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h2; simp at h2)
  have hJ : ‖posPart c.dp.hk c.y₀‖ • negPart c.dp.hk c.y₀ = 0 := c.hzero
  have hu : negPart c.dp.hk c.y₀ = 0 := by
    rcases smul_eq_zero.1 hJ with h | h
    · exact absurd h hvpos.ne'
    · exact h
  rw [hu, norm_zero] at hsq
  have hvn : ‖posPart c.dp.hk c.y₀‖ = Real.sqrt (2 * c.ε) := by
    rw [← Real.sqrt_sq (norm_nonneg (posPart c.dp.hk c.y₀)), hsq]
    ring_nf
  have hsqrt : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (by linarith [c.hε])
  refine ⟨?_, ?_, ?_⟩
  · change ‖(Real.sqrt (2 * c.ε))⁻¹ • posPart c.dp.hk c.y₀‖ = 1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hsqrt, hvn, inv_mul_cancel₀ hsqrt.ne']
  · change ‖‖c.dq.toE c.w₀‖⁻¹ • c.dq.toE c.w₀‖ = 1
    exact norm_smul_inv_norm (c.dq.toE_ne_zero hw0)
  · have he : Real.sqrt (2 * c.ε) • c.e₁ = posPart c.dp.hk c.y₀ := by
      change Real.sqrt (2 * c.ε) • ((Real.sqrt (2 * c.ε))⁻¹ • posPart c.dp.hk c.y₀) = _
      rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    rw [he, ← hu, DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]

theorem fderiv_pQuad_modelField (η : ℝ) (y : Fin n → ℝ) :
    fderiv ℝ (c.pQuad η) y (ModelField.modelField c.dp.k c.dp.r₀ y) =
      ModelField.theta c.dp.r₀ y * (2 * ‖negPart c.dp.hk y‖ ^ 2 + 2 * η * ‖c.pPerp y‖ ^ 2) := by
  let P : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n - c.dp.k)) :=
    ModelField.posPartL c.dp.hk -
      ((innerSL ℝ c.e₁).comp (ModelField.posPartL c.dp.hk)).smulRight c.e₁
  have hP : ∀ z, P z = c.pPerp z := by
    intro z
    simp only [P, pPerp, pArc, sub_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ModelField.posPartL_apply, real_inner_comm]
  have hfun : c.pQuad η = fun z =>
      ‖ModelField.negPartL c.dp.hk z‖ ^ 2 - η * ‖P z‖ ^ 2 := by
    funext z
    simp only [pQuad, ModelField.negPartL_apply, hP]
  have h1 := (ModelField.negPartL c.dp.hk).hasFDerivAt (x := y) |>.norm_sq
  have h2 := P.hasFDerivAt (x := y) |>.norm_sq
  have h : HasFDerivAt (fun z => ‖ModelField.negPartL c.dp.hk z‖ ^ 2 - η * ‖P z‖ ^ 2) _ y :=
    h1.sub (h2.const_mul η)
  rw [hfun, h.fderiv]
  have hPw : P (ModelField.modelField c.dp.k c.dp.r₀ y) =
      -(ModelField.theta c.dp.r₀ y • c.pPerp y) := by
    rw [hP]
    simp only [pPerp, pArc, ModelField.posPart_modelField c.dp.hk, inner_neg_left,
      inner_smul_left, neg_smul, smul_sub, smul_smul, RCLike.conj_to_real]
    abel
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ModelField.negPartL_apply,
    ModelField.negPart_modelField c.dp.hk, hPw, hP, smul_eq_mul, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem fderiv_pArc_modelField (y : Fin n → ℝ) :
    fderiv ℝ c.pArc y (ModelField.modelField c.dp.k c.dp.r₀ y) =
      -(ModelField.theta c.dp.r₀ y * c.pArc y) := by
  have hL : c.pArc = ⇑((innerSL ℝ c.e₁).comp (ModelField.posPartL c.dp.hk)) := by
    funext z
    simp only [pArc, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ModelField.posPartL_apply, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hL, ContinuousLinearMap.fderiv, ← hL]
  simp only [pArc, ModelField.posPart_modelField, inner_neg_left, inner_smul_left,
    RCLike.conj_to_real]

theorem fderiv_qQuad_modelField (η : ℝ) (y : Fin n → ℝ) :
    fderiv ℝ (c.qQuad η) y (ModelField.modelField c.dq.k c.dq.r₀ y) =
      ModelField.theta c.dq.r₀ y * (2 * η * ‖c.qPerp y‖ ^ 2 + 2 * ‖posPart c.dq.hk y‖ ^ 2) := by
  let P : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin c.dq.k) :=
    ModelField.negPartL c.dq.hk -
      ((innerSL ℝ c.u₀).comp (ModelField.negPartL c.dq.hk)).smulRight c.u₀
  have hP : ∀ z, P z = c.qPerp z := by
    intro z
    simp only [P, qPerp, qArc, sub_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ModelField.negPartL_apply, real_inner_comm]
  have hfun : c.qQuad η = fun z =>
      η * ‖P z‖ ^ 2 - ‖ModelField.posPartL c.dq.hk z‖ ^ 2 := by
    funext z
    simp only [qQuad, ModelField.posPartL_apply, hP]
  have h1 := (ModelField.posPartL c.dq.hk).hasFDerivAt (x := y) |>.norm_sq
  have h2 := P.hasFDerivAt (x := y) |>.norm_sq
  have h : HasFDerivAt (fun z => η * ‖P z‖ ^ 2 - ‖ModelField.posPartL c.dq.hk z‖ ^ 2) _ y :=
    (h2.const_mul η).sub h1
  rw [hfun, h.fderiv]
  have hPw : P (ModelField.modelField c.dq.k c.dq.r₀ y) =
      ModelField.theta c.dq.r₀ y • c.qPerp y := by
    rw [hP]
    simp only [qPerp, qArc, ModelField.negPart_modelField c.dq.hk, inner_smul_left, smul_sub,
      smul_smul, RCLike.conj_to_real]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ModelField.posPartL_apply,
    ModelField.posPart_modelField c.dq.hk, hPw, hP, smul_eq_mul, inner_neg_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem qHeightProfile_spec :
    (∀ σ : ℝ, -c.ρq ≤ σ → σ ^ 2 < c.sqSum → ContDiffAt ℝ ∞ c.qHeightProfile σ ∧ deriv c.qHeightProfile σ < 0) ∧
      ∀ s ∈ Icc (c.fb - 3 * c.βmax) (c.fb + 3 * c.βmax),
        c.qHeightProfile (Real.sqrt (2 * (f q - s))) = Real.sqrt (2 * (s - f p)) := by
  have hε := c.hε
  have hc₁ := c.hc₁
  have hc₂ := c.hc₂
  have hS : c.sqSum = 2 * (f q - f p) := by
    simp only [TransverseCancellingPair.sqSum, TransverseCancellingPair.cq, TransverseCancellingPair.fb]; ring
  have hρ2 : c.ρq ^ 2 = 5 * c.ε / 2 := by
    simp only [TransverseCancellingPair.ρq]; rw [Real.sq_sqrt (by linarith)]
  have hρ0 : 0 ≤ c.ρq := Real.sqrt_nonneg _
  have hSρ : 0 < c.sqSum - c.ρq ^ 2 := by rw [hS, hρ2]; linarith
  have hsqρ : 0 < Real.sqrt (c.sqSum - c.ρq ^ 2) := Real.sqrt_pos.2 hSρ
  have hkH : c.kH = c.ρq / Real.sqrt (c.sqSum - c.ρq ^ 2) + 1 := rfl
  have hkH1 : 1 ≤ c.kH := by
    rw [hkH]; have := div_nonneg hρ0 hsqρ.le; linarith
  set a := Real.sqrt (2 * c.ε) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hlohi : a / 2 < a := by linarith
  have hHq : c.qHeightProfile = fun σ => Real.sqrt (c.sqSum - σ ^ 2) +
      c.kH * (a - σ) * CancelModel.cut (a / 2) a σ := by
    funext σ; rfl
  refine ⟨fun σ hσ₁ hσ₂ => ?_, fun s hs => ?_⟩
  · have hpos : 0 < c.sqSum - σ ^ 2 := by linarith
    have hne : c.sqSum - σ ^ 2 ≠ 0 := hpos.ne'
    have hsq : 0 < Real.sqrt (c.sqSum - σ ^ 2) := Real.sqrt_pos.2 hpos
    have hcutd : DifferentiableAt ℝ (CancelModel.cut (a / 2) a) σ :=
      ((CancelModel.contDiff_cut (a / 2) a).differentiable (by simp)).differentiableAt
    have hg : HasDerivAt (fun σ : ℝ => c.sqSum - σ ^ 2) (-(2 * σ)) σ := by
      have := ((hasDerivAt_id σ).pow 2).const_sub c.sqSum
      simpa using this
    have hD : HasDerivAt c.qHeightProfile
        ((-(2 * σ)) / (2 * Real.sqrt (c.sqSum - σ ^ 2)) +
          (c.kH * (-1) * CancelModel.cut (a / 2) a σ +
            c.kH * (a - σ) * deriv (CancelModel.cut (a / 2) a) σ)) σ := by
      rw [hHq]
      refine (hg.sqrt hne).add ?_
      have h1 : HasDerivAt (fun σ : ℝ => c.kH * (a - σ)) (c.kH * (-1)) σ := by
        have := ((hasDerivAt_id σ).const_sub a).const_mul c.kH
        simpa using this
      exact h1.mul hcutd.hasDerivAt
    refine ⟨?_, ?_⟩
    · rw [hHq]
      refine ContDiffAt.add ?_ ?_
      · exact ContDiffAt.sqrt (contDiffAt_const.sub (contDiffAt_id.pow 2)) hne
      · exact (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).mul
          (CancelModel.contDiff_cut (a / 2) a).contDiffAt
    · rw [hD.deriv]
      have hcd : deriv (CancelModel.cut (a / 2) a) σ ≤ 0 :=
        (CancelModel.cut_antitone hlohi).deriv_nonpos
      have hc0 := CancelModel.cut_nonneg (a / 2) a σ
      have hfrac : (-(2 * σ)) / (2 * Real.sqrt (c.sqSum - σ ^ 2)) =
          -(σ / Real.sqrt (c.sqSum - σ ^ 2)) := by
        field_simp
      rw [hfrac]
      rcases le_or_gt σ a with hσa | hσa
      · have hterm : c.kH * (a - σ) * deriv (CancelModel.cut (a / 2) a) σ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith)) hcd
        rcases le_or_gt σ (a / 2) with hσl | hσl
        · have hc1 : CancelModel.cut (a / 2) a σ = 1 := CancelModel.cut_eq_one hlohi hσl
          rw [hc1]
          have hlt : -(σ / Real.sqrt (c.sqSum - σ ^ 2)) < c.kH := by
            rcases le_or_gt 0 σ with h0 | h0
            · have := div_nonneg h0 hsq.le; linarith
            · have hσρ : σ ^ 2 ≤ c.ρq ^ 2 := by nlinarith
              have hsle : Real.sqrt (c.sqSum - c.ρq ^ 2) ≤ Real.sqrt (c.sqSum - σ ^ 2) :=
                Real.sqrt_le_sqrt (by linarith)
              have h3 : -σ / Real.sqrt (c.sqSum - σ ^ 2) ≤
                  c.ρq / Real.sqrt (c.sqSum - c.ρq ^ 2) := by
                calc -σ / Real.sqrt (c.sqSum - σ ^ 2)
                    ≤ c.ρq / Real.sqrt (c.sqSum - σ ^ 2) :=
                      div_le_div_of_nonneg_right (by linarith) hsq.le
                  _ ≤ c.ρq / Real.sqrt (c.sqSum - c.ρq ^ 2) :=
                      div_le_div_of_nonneg_left hρ0 hsqρ hsle
              rw [neg_div] at h3
              rw [hkH]; linarith
          linarith
        · have h0 : 0 < σ := by linarith
          have := div_pos h0 hsq
          have : 0 ≤ c.kH * CancelModel.cut (a / 2) a σ := mul_nonneg (by linarith) hc0
          linarith
      · have hev : CancelModel.cut (a / 2) a =ᶠ[𝓝 σ] fun _ => (0 : ℝ) := by
          filter_upwards [lt_mem_nhds hσa] with t ht
          exact CancelModel.cut_eq_zero hlohi ht.le
        have hcd0 : deriv (CancelModel.cut (a / 2) a) σ = 0 := by
          rw [hev.deriv_eq]; simp
        rw [hcd0, CancelModel.cut_eq_zero hlohi hσa.le]
        have h0 : 0 < σ := by linarith
        have := div_pos h0 hsq
        linarith
  · obtain ⟨hs₁, hs₂⟩ := hs
    have hβ : c.βmax ≤ (f q - f p - 2 * c.ε) / 16 := by
      simp only [TransverseCancellingPair.βmax]
      exact (min_le_left _ _).trans (min_le_right _ _)
    have hfb : c.fb = f p + c.ε := rfl
    have hqs : c.ε ≤ f q - s := by rw [hfb] at hs₂; linarith
    have hσ : a ≤ Real.sqrt (2 * (f q - s)) := Real.sqrt_le_sqrt (by linarith)
    rw [hHq]
    simp only
    rw [CancelModel.cut_eq_zero hlohi hσ, mul_zero, add_zero,
      Real.sq_sqrt (by linarith), hS]
    congr 1; ring

theorem fderiv_qHeightProfile_qArc_modelField {y : Fin n → ℝ} (h₁ : -c.ρq ≤ c.qArc y)
    (h₂ : c.qArc y ^ 2 < c.sqSum) :
    fderiv ℝ (fun y => c.qHeightProfile (c.qArc y)) y (ModelField.modelField c.dq.k c.dq.r₀ y) =
      ModelField.theta c.dq.r₀ y * (deriv c.qHeightProfile (c.qArc y) * c.qArc y) := by
  set L : (Fin n → ℝ) →L[ℝ] ℝ := (innerSL ℝ c.u₀).comp (ModelField.negPartL c.dq.hk) with hL
  have hqL : c.qArc = fun y => L y := by
    funext z
    simp only [hL, TransverseCancellingPair.qArc, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ModelField.negPartL_apply, innerSL_apply_apply]
    exact real_inner_comm _ _
  have hA : HasFDerivAt c.qArc L y := by
    rw [hqL]; exact L.hasFDerivAt
  have hH : HasDerivAt c.qHeightProfile (deriv c.qHeightProfile (c.qArc y)) (c.qArc y) :=
    (((c.qHeightProfile_spec.1 _ h₁ h₂).1).differentiableAt (by simp)).hasDerivAt
  have hC : HasFDerivAt (fun y => c.qHeightProfile (c.qArc y)) (deriv c.qHeightProfile (c.qArc y) • L) y :=
    hH.comp_hasFDerivAt y hA
  rw [hC.fderiv, smul_apply, smul_eq_mul, hL, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ModelField.negPartL_apply, ModelField.negPart_modelField,
    innerSL_apply_apply, inner_smul_right, real_inner_comm, TransverseCancellingPair.qArc]
  ring

theorem fderiv_ascent (η μ : ℝ) (y : Fin n → ℝ) :
    fderiv ℝ (fun y => c.pQuad η y + μ * c.pArc y) y (recombine c.dp.hk 0 c.e₁) = μ ∧
      (-c.ρq ≤ c.qArc y → c.qArc y ^ 2 < c.sqSum →
        fderiv ℝ (fun y => c.qQuad η y + μ * c.qHeightProfile (c.qArc y)) y (recombine c.dq.hk c.u₀ 0) =
          μ * deriv c.qHeightProfile (c.qArc y)) := by
  obtain ⟨he₁n, hu₀n, -⟩ := c.unit_dirs
  have he₁ : ⟪c.e₁, c.e₁⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he₁n]; norm_num
  have hu₀ : ⟪c.u₀, c.u₀⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu₀n]; norm_num
  have hline : ∀ (F : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (g : ℝ → ℝ) (b : ℝ),
      DifferentiableAt ℝ F y → HasDerivAt g b 0 → (∀ t : ℝ, F (y + t • w) = g t) →
        fderiv ℝ F y w = b := by
    intro F w g b hF hg hFl
    have hl : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
    have h1 : HasDerivAt (F ∘ fun t : ℝ => y + t • w) (fderiv ℝ F y w) 0 :=
      hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    have hfun : (F ∘ fun t : ℝ => y + t • w) = g := by
      funext t
      exact hFl t
    rw [hfun] at h1
    exact h1.unique hg
  have hNp : Differentiable ℝ (fun y : Fin n → ℝ => negPart c.dp.hk y) :=
    (ModelField.negPartL c.dp.hk).differentiable
  have hPp : Differentiable ℝ (fun y : Fin n → ℝ => posPart c.dp.hk y) :=
    (ModelField.posPartL c.dp.hk).differentiable
  have hNq : Differentiable ℝ (fun y : Fin n → ℝ => negPart c.dq.hk y) :=
    (ModelField.negPartL c.dq.hk).differentiable
  have hPq : Differentiable ℝ (fun y : Fin n → ℝ => posPart c.dq.hk y) :=
    (ModelField.posPartL c.dq.hk).differentiable
  have hArcD : Differentiable ℝ c.pArc := fun z =>
    (hPp z).inner ℝ (differentiableAt_const c.e₁)
  have hqArcD : Differentiable ℝ c.qArc := fun z =>
    (hNq z).inner ℝ (differentiableAt_const c.u₀)
  refine ⟨?_, ?_⟩
  · apply hline _ _ (fun t : ℝ => (c.pQuad η y + μ * c.pArc y) + t * μ) μ
    · have hperp : DifferentiableAt ℝ c.pPerp y :=
        (hPp y).sub ((hArcD y).smul_const c.e₁)
      have hQ : DifferentiableAt ℝ (c.pQuad η) y :=
        ((hNp y).norm_sq ℝ).sub ((hperp.norm_sq ℝ).const_mul η)
      exact hQ.add ((hArcD y).const_mul μ)
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const μ).const_add (c.pQuad η y + μ * c.pArc y)
    · intro t
      have hneg : negPart c.dp.hk (y + t • recombine c.dp.hk 0 c.e₁) = negPart c.dp.hk y := by
        rw [← ModelField.negPartL_apply, map_add, map_smul, ModelField.negPartL_apply,
          ModelField.negPartL_apply, Topology.Morse.CellAttachment.negPart_recombine, smul_zero,
          add_zero]
      have hpos : posPart c.dp.hk (y + t • recombine c.dp.hk 0 c.e₁) =
          posPart c.dp.hk y + t • c.e₁ := by
        rw [← ModelField.posPartL_apply, map_add, map_smul, ModelField.posPartL_apply,
          ModelField.posPartL_apply, Topology.Morse.CellAttachment.posPart_recombine]
      have harc : c.pArc (y + t • recombine c.dp.hk 0 c.e₁) = c.pArc y + t := by
        simp only [TransverseCancellingPair.pArc]
        rw [hpos, inner_add_left, real_inner_smul_left, he₁, mul_one]
      have hperp : c.pPerp (y + t • recombine c.dp.hk 0 c.e₁) = c.pPerp y := by
        simp only [TransverseCancellingPair.pPerp]
        rw [hpos, harc, add_smul]
        abel
      simp only [TransverseCancellingPair.pQuad]
      rw [hneg, hperp, harc]
      ring
  · intro h₁ h₂
    have hHq : DifferentiableAt ℝ c.qHeightProfile (c.qArc y) :=
      ((c.qHeightProfile_spec.1 _ h₁ h₂).1).differentiableAt (by simp)
    apply hline _ _ (fun t : ℝ => c.qQuad η y + μ * c.qHeightProfile (c.qArc y + t))
      (μ * deriv c.qHeightProfile (c.qArc y))
    · have hperp : DifferentiableAt ℝ c.qPerp y :=
        (hNq y).sub ((hqArcD y).smul_const c.u₀)
      have hQ : DifferentiableAt ℝ (c.qQuad η) y :=
        ((hperp.norm_sq ℝ).const_mul η).sub ((hPq y).norm_sq ℝ)
      exact hQ.add ((hHq.comp y (hqArcD y)).const_mul μ)
    · have hs : HasDerivAt (fun t : ℝ => c.qArc y + t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (c.qArc y)
      have hH : HasDerivAt (fun t : ℝ => c.qHeightProfile (c.qArc y + t)) (deriv c.qHeightProfile (c.qArc y) * 1) 0 := by
        have hH0 : HasDerivAt c.qHeightProfile (deriv c.qHeightProfile (c.qArc y)) (c.qArc y + 0) := by
          rw [add_zero]
          exact hHq.hasDerivAt
        exact hH0.comp (0 : ℝ) hs
      rw [mul_one] at hH
      exact (hH.const_mul μ).const_add (c.qQuad η y)
    · intro t
      have hneg : negPart c.dq.hk (y + t • recombine c.dq.hk c.u₀ 0) =
          negPart c.dq.hk y + t • c.u₀ := by
        rw [← ModelField.negPartL_apply, map_add, map_smul, ModelField.negPartL_apply,
          ModelField.negPartL_apply, Topology.Morse.CellAttachment.negPart_recombine]
      have hpos : posPart c.dq.hk (y + t • recombine c.dq.hk c.u₀ 0) = posPart c.dq.hk y := by
        rw [← ModelField.posPartL_apply, map_add, map_smul, ModelField.posPartL_apply,
          ModelField.posPartL_apply, Topology.Morse.CellAttachment.posPart_recombine, smul_zero,
          add_zero]
      have harc : c.qArc (y + t • recombine c.dq.hk c.u₀ 0) = c.qArc y + t := by
        simp only [TransverseCancellingPair.qArc]
        rw [hneg, inner_add_left, real_inner_smul_left, hu₀, mul_one]
      have hperp : c.qPerp (y + t • recombine c.dq.hk c.u₀ 0) = c.qPerp y := by
        simp only [TransverseCancellingPair.qPerp]
        rw [hneg, harc, add_smul]
        abel
      simp only [TransverseCancellingPair.qQuad]
      rw [hpos, hperp, harc]

theorem qExtendedChart_eq_of_mem_qTube {x : M} (hx : x ∈ c.qTube) :
    c.qExtendedChart x = modelLift c.dq.hk (f q) (f x) (c.dq.χ.symm (c.D.π c.cq x)) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hq : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  obtain ⟨hfx, -, z, ⟨hzρ, hz0⟩, hzx⟩ := hx
  unfold TransverseCancellingPair.qExtendedChart
  split_ifs with hB
  swap
  · rfl
  obtain ⟨y, hyρ, rfl⟩ := hB
  have hε := c.hε
  have hrmq := c.hrmq
  have hrm0 : 0 < c.D.rm q hq := c.D.rm_pos q hq
  have hR := (c.D.hrm q hq).2
  have hρsq : ∀ w : Fin n → ℝ, morseNorm n w < c.ρq → morseNorm n w ^ 2 < 5 * c.ε / 2 := by
    intro w hw
    have h0 := ModelField.morseNorm_nonneg w
    have := (Real.lt_sqrt h0).1 hw
    exact this
  have hrm_of : ∀ w : Fin n → ℝ, morseNorm n w ^ 2 < 8 * c.ε → morseNorm n w < c.D.rm q hq := by
    intro w hw
    exact (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg w) hrm0.le two_ne_zero).1
      (hw.trans hrmq)
  have hy2 := hρsq y hyρ
  have hyrm : morseNorm n y < c.D.rm q hq := hrm_of y (by linarith)
  have hyR : morseNorm n y ≤ c.dq.R := hyrm.le.trans hR
  have hfxy : f (c.dq.χ y) = f q + (1 / 2) * (‖posPart c.dq.hk y‖ ^ 2 - ‖negPart c.dq.hk y‖ ^ 2) := by
    rw [c.dq.hnorm y hyR, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
  have hsplit_y := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart c.dq.hk y
  have hcq : c.cq = f q - c.ε := rfl
  set x := c.dq.χ y with hxdef
  set t := f x - c.cq with htdef
  have ht0 : t ≤ 0 := by linarith
  set B := morseNorm n y ^ 2 - 2 * t with hBdef
  have hBlt : B < c.D.rm q hq ^ 2 := by
    have := sq_nonneg ‖posPart c.dq.hk y‖
    nlinarith
  set S : Set (Fin n → ℝ) := {w | morseNorm n w ^ 2 ≤ B} with hS
  have hSsub : S ⊆ {w | morseNorm n w < c.D.rm q hq} := fun w hw =>
    (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg w) hrm0.le two_ne_zero).1
      (lt_of_le_of_lt hw hBlt)
  have hSK : IsCompact (c.dq.χ '' S) :=
    c.dq.isCompact_image_of_subset ((isCompact_morseNorm_le (Real.sqrt B)).of_isClosed_subset
      (isClosed_le (continuous_morseNorm.pow 2) continuous_const) fun w hw =>
        Real.le_sqrt_of_sq_le hw) (c.D.rm_lt_R' q hq)
      fun w hw => show morseNorm n w ≤ _ from le_of_lt (hSsub hw)
  have hQc : IsClosed {s : ℝ | c.D.flow s x ∈ c.dq.χ '' S} :=
    hSK.isClosed.preimage (c.D.continuous_flow_curve x)
  have hstay : ∀ s ∈ Icc t 0, c.D.flow s x ∈ c.dq.χ '' S := by
    have hmain := Icc_neg_subset_of_isClosed_of_step hQc (T := -t) ?_ ?_
    · rwa [neg_neg] at hmain
    · change c.D.flow 0 x ∈ c.dq.χ '' S
      rw [GradientLikeStrip.flow_zero]
      exact ⟨y, by change morseNorm n y ^ 2 ≤ B; linarith, rfl⟩
    · intro s hs hIcc
      have hsO : c.D.flow s x ∈ c.dq.χ '' {w | morseNorm n w < c.D.rm q hq} :=
        image_mono hSsub (hIcc (left_mem_Icc.2 hs.2))
      obtain ⟨δ, hδ, hδO⟩ := c.D.exists_Icc_flow_mem_open (c.D.isOpen_modelBall q hq) hsO
      have hts : t < s := by have := hs.1; rwa [neg_neg] at this
      refine mem_nhdsLT_iff_exists_Ico_subset.2 ⟨max (s - δ) t,
        by simp only [mem_Iio, max_lt_iff]; exact ⟨by linarith, hts⟩, fun s' hs' => ?_⟩
      have hs'δ : s - δ ≤ s' := (le_max_left _ _).trans hs'.1
      have hs't : t ≤ s' := (le_max_right _ _).trans hs'.1
      change c.D.flow s' x ∈ c.dq.χ '' S
      have hODE : ∀ u ∈ Icc s' 0,
          c.D.flow u x ∈ c.dq.χ '' {w | morseNorm n w < c.D.rm q hq} := by
        intro u hu
        rcases le_or_gt s u with hus | hus
        · exact image_mono hSsub (hIcc ⟨hus, hu.2⟩)
        · exact hδO u ⟨hs'δ.trans hu.1, by linarith [hus]⟩
      have hγ := GradientLikeStrip.hasDerivAt_symm_flow_Icc (D := c.D) hq hODE
      have hss' : s' ≤ 0 := hs'.2.le.trans hs.2
      have hγ0 : c.dq.χ.symm (c.D.flow 0 x) = y := by
        rw [GradientLikeStrip.flow_zero, hxdef, c.dq.χ.left_inv (c.dq.hsrc y hyR)]
      have hmono : ‖negPart c.dq.hk (c.dq.χ.symm (c.D.flow s' x))‖ ^ 2 ≤
          ‖negPart c.dq.hk (c.dq.χ.symm (c.D.flow 0 x))‖ ^ 2 :=
        ModelField.normSq_negPart_monotoneOn c.dq.hk c.dq.hr₀ hγ (left_mem_Icc.2 hss')
          (right_mem_Icc.2 hss') hss'
      rw [hγ0] at hmono
      have hmem' : c.D.flow s' x ∈ c.dq.χ '' Metric.ball 0 c.dq.R' :=
        c.D.modelBall_subset_image_ball q hq (hODE s' (left_mem_Icc.2 hss'))
      have hlev : f (c.D.flow s' x) = f q + (1 / 2) *
          (‖posPart c.dq.hk (c.dq.χ.symm (c.D.flow s' x))‖ ^ 2 -
            ‖negPart c.dq.hk (c.dq.χ.symm (c.D.flow s' x))‖ ^ 2) := by
        rw [← DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
        exact c.dq.f_eq_nf_symm (c.D.modelBall_subset_image_le q hq
          (hODE s' (left_mem_Icc.2 hss')))
      have hf1 := GradientLikeStrip.f_flow_le_sub_of_nonpos hfs (D := c.D) x hss'
      refine c.dq.mem_image_of_symm_mem hmem' ?_
      change morseNorm n (c.dq.χ.symm (c.D.flow s' x)) ^ 2 ≤ B
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart c.dq.hk]
      nlinarith
  obtain ⟨l, hl0, -, -, hscale⟩ := model_flow_scaling c.D hq hyrm (t := t) (fun s hs => by
    rw [uIcc_of_ge ht0] at hs
    exact image_mono hSsub (hstay s hs))
  have hπ : c.D.π c.cq x = c.D.flow t x := rfl
  have hzsrc : z ∈ c.dq.χ.source := c.dq.hsrc z
    ((hrm_of z (by linarith [hρsq z hzρ])).le.trans hR)
  have hzeq : c.dq.χ.symm (c.D.π c.cq x) = z := by
    rw [← hzx, c.dq.χ.left_inv hzsrc]
  have hyc : c.dq.χ.symm (c.D.π c.cq x) =
      recombine c.dq.hk (l • negPart c.dq.hk y) (l⁻¹ • posPart c.dq.hk y) := by
    rw [hπ]; exact hscale
  have hneg_c : negPart c.dq.hk (c.dq.χ.symm (c.D.π c.cq x)) = l • negPart c.dq.hk y := by
    rw [hyc, DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine]
  have hpos_c : posPart c.dq.hk (c.dq.χ.symm (c.D.π c.cq x)) = l⁻¹ • posPart c.dq.hk y := by
    rw [hyc, DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine]
  have hzne : negPart c.dq.hk (c.dq.χ.symm (c.D.π c.cq x)) ≠ 0 := by rw [hzeq]; exact hz0
  have hune : negPart c.dq.hk y ≠ 0 := by
    intro h; apply hzne; rw [hneg_c, h, smul_zero]
  have hcong := modelLift_congr c.dq.hk (c₀ := f q) (s := f x) hzne hune
    (by rw [hneg_c, norm_smul, Real.norm_of_nonneg hl0.le, mul_inv, smul_smul]
        congr 1; field_simp)
    (by rw [hneg_c, hpos_c, norm_smul, Real.norm_of_nonneg hl0.le, smul_smul]
        congr 1; field_simp)
  have hself := (modelLift_spec c.dq.hk (c₀ := f q) (s := f x) (by linarith) hune).2.2.2
  have hnf : morseNormalForm c.dq.hk (f q) y = f x := (c.dq.hnorm y hyR).symm
  rw [hnf] at hself
  have hxsymm : c.dq.χ.symm x = y := c.dq.χ.left_inv (c.dq.hsrc y hyR)
  rw [hcong, hself (by linarith), hxsymm]

theorem contMDiffOn_qExtendedChart : IsOpen c.qDom ∧ ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ c.qExtendedChart c.qDom := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hε := c.hε
  have hrm := c.hrmq
  have hrmpos : 0 < c.D.rm q (mem_pair_right p q) := c.D.rm_pos q (mem_pair_right p q)
  have hrmR' : c.D.rm q (mem_pair_right p q) < c.dq.R' := c.D.rm_lt_R' q (mem_pair_right p q)
  have hρq : c.ρq < c.dq.R' := by
    refine lt_trans ?_ hrmR'
    unfold ρq
    rw [Real.sqrt_lt' hrmpos]
    linarith
  set S : Set (Fin n → ℝ) := {y | morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0} with hS
  have hSsrc : S ⊆ c.dq.χ.source := fun y hy =>
    c.dq.hball (mem_ball_of_morseNorm_lt (lt_trans hy.1 hρq))
  have hSopen : IsOpen S :=
    (isOpen_morseNorm_lt c.ρq).inter
      (isOpen_ne_fun (DifferentialGeometry.Topology.Morse.CellAttachment.continuous_negPart
        c.dq.hk) continuous_const)
  have hχS : IsOpen (c.dq.χ '' S) := (c.dq.χ.isOpen_image_iff_of_subset_source hSsrc).2 hSopen
  have hχSball : c.dq.χ '' S ⊆ c.dq.χ '' Metric.ball 0 c.dq.R' :=
    image_mono fun y hy => mem_ball_of_morseNorm_lt (lt_trans hy.1 hρq)
  have hBall : IsOpen c.qBall := c.dq.isOpen_image_of_lt hρq.le
  have hTube : IsOpen c.qTube := by
    have : c.qTube = {x | f x < c.cq} ∩ c.D.regularFlowDomain c.cq ∩ c.D.π c.cq ⁻¹' (c.dq.χ '' S) := by
      ext x; simp only [qTube, mem_inter_iff, mem_ofPred_eq, mem_preimage, hS]; tauto
    rw [this]
    exact ((isOpen_lt hfs.continuous continuous_const).inter
      (c.D.isOpen_regularFlowDomain hfs.continuous c.cq)).inter (hχS.preimage (c.D.continuous_π hfs c.cq))
  have hDom : IsOpen c.qDom := hBall.union hTube
  refine ⟨hDom, fun x hx => ?_⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  rcases hx with hxB | hxT
  · have hev : c.qExtendedChart =ᶠ[𝓝 x] c.dq.χ.symm := by
      filter_upwards [hBall.mem_nhds hxB] with z hz
      simp only [qExtendedChart, hz, ↓reduceIte]
    exact (c.dq.contMDiffAt_symm (c.dq.image_lt_subset_image_ball hρq.le hxB)).congr_of_eventuallyEq
      hev
  · have hev : c.qExtendedChart =ᶠ[𝓝 x]
        fun z => modelLift c.dq.hk (f q) (f z) (c.dq.χ.symm (c.D.π c.cq z)) := by
      filter_upwards [hTube.mem_nhds hxT] with z hz
      exact c.qExtendedChart_eq_of_mem_qTube hz
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    obtain ⟨y, hyS, hyx⟩ := hxT.2.2
    have hsymm : c.dq.χ.symm (c.D.π c.cq x) = y := by
      rw [← hyx]; exact c.dq.χ.left_inv (hSsrc hyS)
    have hπ : c.D.π c.cq x ∈ c.dq.χ '' Metric.ball 0 c.dq.R' := hχSball ⟨y, hyS, hyx⟩
    have hin : (f x, c.dq.χ.symm (c.D.π c.cq x)) ∈
        {z : ℝ × (Fin n → ℝ) | z.1 < f q ∧ negPart c.dq.hk z.2 ≠ 0} := by
      refine ⟨?_, ?_⟩
      · have h1 := hxT.1
        simp only [cq] at h1
        change f x < f q
        linarith
      · change negPart c.dq.hk (c.dq.χ.symm (c.D.π c.cq x)) ≠ 0
        rw [hsymm]; exact hyS.2
    have hopen : IsOpen {z : ℝ × (Fin n → ℝ) | z.1 < f q ∧ negPart c.dq.hk z.2 ≠ 0} :=
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_ne_fun ((DifferentialGeometry.Topology.Morse.CellAttachment.continuous_negPart
          c.dq.hk).comp continuous_snd) continuous_const)
    have hg : ContDiffAt ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => modelLift c.dq.hk (f q) z.1 z.2)
        (f x, c.dq.χ.symm (c.D.π c.cq x)) :=
      (contDiffOn_modelLift c.dq.hk (f q)).contDiffAt (hopen.mem_nhds hin)
    have hin' : ContMDiffAt I 𝓘(ℝ, ℝ × (Fin n → ℝ)) ∞
        (fun z => (f z, c.dq.χ.symm (c.D.π c.cq z))) x :=
      ContMDiffAt.prodMk_space hfs.contMDiffAt
        ((c.dq.contMDiffAt_symm hπ).comp x (c.D.contMDiff_π hfs c.cq).contMDiffAt)
    exact ContDiffAt.comp_contMDiffAt
      (g := fun z : ℝ × (Fin n → ℝ) => modelLift c.dq.hk (f q) z.1 z.2)
      (f := fun z => (f z, c.dq.χ.symm (c.D.π c.cq z))) hg hin'

theorem nf_qExtendedChart {x : M} (hx : x ∈ c.qDom) : morseNormalForm c.dq.hk (f q) (c.qExtendedChart x) = f x := by
  have hρ : c.ρq < c.D.rm q (mem_pair_right p q) := by
    have hrm := c.D.rm_pos q (mem_pair_right p q)
    have h8 := c.hrmq
    have hε := c.hε
    unfold ρq
    rw [Real.sqrt_lt' hrm]
    linarith
  have hρR : c.ρq ≤ c.dq.R := hρ.le.trans (c.D.hrm q (mem_pair_right p q)).2
  by_cases hb : x ∈ c.qBall
  · have hΨ : c.qExtendedChart x = c.dq.χ.symm x := by
      unfold qExtendedChart
      simp only [hb, ite_true]
    obtain ⟨y, hy, rfl⟩ := hb
    have hyR : morseNorm n y ≤ c.dq.R := (le_of_lt hy).trans hρR
    rw [hΨ, c.dq.χ.left_inv (c.dq.hsrc y hyR), c.dq.hnorm y hyR]
  · have hΨ : c.qExtendedChart x =
        modelLift c.dq.hk (f q) (f x) (c.dq.χ.symm (c.D.π c.cq x)) := by
      unfold qExtendedChart
      simp only [hb, ite_false]
    have ht : x ∈ c.qTube := by
      rcases hx with h | h
      · exact absurd h hb
      · exact h
    obtain ⟨hfx, -, y, ⟨hy, hu⟩, hyx⟩ := ht
    have hyR : morseNorm n y ≤ c.dq.R := (le_of_lt hy).trans hρR
    have hs : f x < f q := by
      have hε := c.hε
      unfold cq at hfx
      linarith
    rw [hΨ, ← hyx, c.dq.χ.left_inv (c.dq.hsrc y hyR)]
    exact (modelLift_spec c.dq.hk hs hu).1

theorem mfderiv_qExtendedChart_V {x : M} (hx : x ∈ c.qDom) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x (c.D.V x) =
      ModelField.modelField c.dq.k c.dq.r₀ (c.qExtendedChart x) := by
  classical
  have hq : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hε : 0 < c.ε := c.hε
  have hrm : 8 * c.ε < c.D.rm q hq ^ 2 := c.hrmq
  have hrm0 : 0 < c.D.rm q hq := c.D.rm_pos q hq
  have hρ : c.ρq < c.D.rm q hq := by
    unfold ρq
    rw [Real.sqrt_lt' hrm0]
    linarith
  have hρR : c.ρq ≤ c.dq.R := hρ.le.trans (c.D.hrm q hq).2
  by_cases hxB : x ∈ c.qBall
  · obtain ⟨y, hy, rfl⟩ := hxB
    have hy' : morseNorm n y < c.ρq := hy
    have hBopen : IsOpen c.qBall := c.dq.isOpen_image_of_lt (hρR.trans c.dq.hRR'.le)
    have hyB : c.dq.χ y ∈ c.qBall := ⟨y, hy, rfl⟩
    have hev : c.qExtendedChart =ᶠ[𝓝 (c.dq.χ y)] c.dq.χ.symm := by
      filter_upwards [hBopen.mem_nhds hyB] with z hz
      simp only [qExtendedChart, hz, ↓reduceIte]
    have hΨ : c.qExtendedChart (c.dq.χ y) = y := by
      simp only [qExtendedChart, hyB, ↓reduceIte]
      exact c.dq.χ.left_inv (c.dq.hsrc y (hy'.le.trans hρR))
    rw [hev.mfderiv_eq]
    refine (c.D.model q hq y (hy'.trans hρ)).trans ?_
    rw [hΨ]
  · have hxT : x ∈ c.qTube := hx.resolve_left hxB
    have hΨx := c.qExtendedChart_eq_of_mem_qTube hxT
    obtain ⟨hxf, hxΩ, y', ⟨hy'n, hy'u⟩, hy'x⟩ := hxT
    have hqs : f q ∈ Ioo a' b' := ((c.hcrit q).1 hq).1
    have hps : f p ∈ Ioo a' b' := ((c.hcrit p).1 (mem_pair_left p q)).1
    have hcq : c.cq = f q - c.ε := rfl
    have hc₁ := c.hc₁
    have hc₂ := c.hc₂
    have hcqI : c.cq ∈ Icc a' b' := ⟨by rw [hcq]; linarith [hps.1], by rw [hcq]; linarith [hqs.2]⟩
    have hcU : ∀ r hr, ∀ z ∈ c.D.smallBall r hr, f z ≠ c.cq := by
      intro r hr z hz hfz
      exact c.hlev z ⟨by rw [hfz, hcq]; linarith, by rw [hfz, hcq]⟩ r hr hz
    have hyc : c.dq.χ.symm (c.D.π c.cq x) = y' := by
      rw [← hy'x, c.dq.χ.left_inv (c.dq.hsrc y' (hy'n.le.trans hρR))]
    have hflowc : Continuous (fun t => c.D.flow t x) := c.D.continuous_flow_curve x
    have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), f (c.D.flow t x) < c.cq ∧ c.D.flow t x ∈ c.D.regularFlowDomain c.cq := by
      have h1 : ContinuousAt (fun t => f (c.D.flow t x)) 0 :=
        (hfs.continuous.comp hflowc).continuousAt
      have h2 : ContinuousAt (fun t => c.D.flow t x) 0 := hflowc.continuousAt
      refine (h1.eventually (gt_mem_nhds ?_)).and (h2.preimage_mem_nhds ?_)
      · simpa [GradientLikeStrip.flow_zero] using hxf
      · rw [GradientLikeStrip.flow_zero]
        exact (c.D.isOpen_regularFlowDomain hfs.continuous c.cq).mem_nhds hxΩ
    have hev : (fun t => c.qExtendedChart (c.D.flow t x)) =ᶠ[𝓝 0]
        (fun t => modelLift c.dq.hk (f q) (f (c.D.flow t x)) y') := by
      filter_upwards [hev1] with t ht
      have hπ : c.D.π c.cq (c.D.flow t x) = c.D.π c.cq x :=
        GradientLikeStrip.π_flow hfs hcqI hcU hxΩ ht.2
      have hT : c.D.flow t x ∈ c.qTube :=
        ⟨ht.1, ht.2, by rw [hπ]; exact ⟨y', ⟨hy'n, hy'u⟩, hy'x⟩⟩
      rw [c.qExtendedChart_eq_of_mem_qTube hT, hπ, hyc]
    have hunit : dfV I f c.D.V x = -1 := by
      refine c.D.dfV_eq_neg_one_of_mem_unitRegion ⟨⟨hxΩ.1.1.le, hxΩ.1.2.le⟩, fun r hr hmem => ?_⟩
      refine hxΩ.2 0 left_mem_uIcc r hr ?_
      rw [GradientLikeStrip.flow_zero]
      exact c.D.smallBall_subset_closedSmallBall r hr hmem
    have hfx : f x < f q := hxf.trans (by rw [hcq]; linarith)
    have hspec := modelLift_spec c.dq.hk hfx hy'u
    set L := modelLift c.dq.hk (f q) (f x) y' with hL
    have hbig : c.dq.r₀ / 2 ≤ morseNorm n L := by
      have h1 := Topology.Morse.CellAttachment.morseNormalForm_split c.dq.hk (f q) L
      have h2 := Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart c.dq.hk L
      rw [hspec.1] at h1
      have hr := c.hr₀q
      have h3 : c.dq.r₀ ^ 2 < morseNorm n L ^ 2 := by
        nlinarith [sq_nonneg ‖posPart c.dq.hk L‖]
      have h4 : c.dq.r₀ < morseNorm n L :=
        lt_of_pow_lt_pow_left₀ 2 (ModelField.morseNorm_nonneg L) h3
      linarith [c.dq.hr₀]
    have hd1 : HasDerivAt (fun s => modelLift c.dq.hk (f q) s y')
        (-(ModelField.modelField c.dq.k c.dq.r₀ L)) (f (c.D.flow 0 x)) := by
      rw [GradientLikeStrip.flow_zero]
      exact hasDerivAt_modelLift c.dq.hk c.dq.hr₀ hfx hy'u hbig
    have hd2 : HasDerivAt (fun t => f (c.D.flow t x)) (-1) 0 := by
      have := GradientLikeStrip.hasDerivAt_f_flow (D := c.D) hfs x 0
      rwa [GradientLikeStrip.flow_zero, hunit] at this
    have hd3 := (hd1.scomp (0 : ℝ) hd2).congr_of_eventuallyEq hev
    have hmd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x :=
      (c.contMDiffOn_qExtendedChart.2.contMDiffAt (c.contMDiffOn_qExtendedChart.1.mem_nhds hx)).mdifferentiableAt
        (by simp)
    have hd4 := hasDerivAt_comp_integralCurve (c.D.isMIntegralCurve_flow x) (t := 0)
      (φ := c.qExtendedChart) (by rw [GradientLikeStrip.flow_zero]; exact hmd)
    rw [GradientLikeStrip.flow_zero] at hd4
    have h5 := hd4.unique hd3
    have h6 : mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x (c.D.V x) =
        (-1 : ℝ) • -(ModelField.modelField c.dq.k c.dq.r₀ L) := h5
    rw [h6, hΨx, hyc]
    change (-1 : ℝ) • -(ModelField.modelField c.dq.k c.dq.r₀ L) = ModelField.modelField c.dq.k c.dq.r₀ L
    rw [neg_one_smul, neg_neg]

theorem surjective_mfderiv_qExtendedChart {x : M} (hx : x ∈ c.qDom) :
    Function.Surjective (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  obtain ⟨hDopen, hsm⟩ := c.contMDiffOn_qExtendedChart
  have hΨd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x :=
    (hsm.contMDiffAt (hDopen.mem_nhds hx)).mdifferentiableAt (by simp)
  have key : ∀ G : (Fin n → ℝ) → M, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I G (c.qExtendedChart x) →
      (G ∘ c.qExtendedChart) =ᶠ[𝓝 x] id →
      Function.Surjective (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x) := by
    intro G hG hev
    have hcomp := mfderiv_comp x hG hΨd
    have h1 := hev.mfderiv_eq (I := I) (I' := I)
    rw [mfderiv_id] at h1
    have e : ∀ u : Fin n → ℝ, mfderiv 𝓘(ℝ, Fin n → ℝ) I G (c.qExtendedChart x)
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x u) = u := fun u =>
      DFunLike.congr_fun (hcomp.symm.trans h1) u
    have hinj : Function.Injective (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x) := by
      intro v w hvw
      have h2 := congrArg (mfderiv 𝓘(ℝ, Fin n → ℝ) I G (c.qExtendedChart x)) hvw
      exact (e v).symm.trans (h2.trans (e w))
    exact LinearMap.injective_iff_surjective
      (f := (show (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) from
        mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart x).toLinearMap).mp hinj
  have hρR : c.ρq < c.dq.R := by
    have hpos : 0 < c.D.rm q (mem_pair_right p q) := c.D.rm_pos q _
    have h8 := c.hrmq
    have hlt : c.ρq < c.D.rm q (mem_pair_right p q) := by
      unfold ρq
      rw [Real.sqrt_lt' hpos]
      linarith [c.hε]
    exact hlt.trans_le (c.D.hrm q (mem_pair_right p q)).2
  have hρR' : c.ρq ≤ c.dq.R' := (hρR.trans c.dq.hRR').le
  by_cases hxt : x ∈ c.qTube
  · have hS : IsOpen (c.dq.χ '' {y | morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0}) := by
      refine (c.dq.χ.isOpen_image_iff_of_subset_source ?_).2 ?_
      · intro y hy
        exact c.dq.hball (mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy.1 hρR'))
      · exact (isOpen_morseNorm_lt _).inter
          (isOpen_ne_fun c.dq.continuous_negPart continuous_const)
    have hTopen : IsOpen c.qTube := by
      change IsOpen ({x | f x < c.cq} ∩ (c.D.regularFlowDomain c.cq ∩ c.D.π c.cq ⁻¹'
        (c.dq.χ '' {y | morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0})))
      exact (isOpen_lt hfs.continuous continuous_const).inter
        ((c.D.isOpen_regularFlowDomain hfs.continuous c.cq).inter (hS.preimage (c.D.continuous_π hfs c.cq)))
    have hq := ((c.hcrit q).1 (by simp)).1
    have hp := ((c.hcrit p).1 (by simp)).1
    have hcq : c.cq ∈ Icc a' b' := by
      unfold cq
      constructor <;> linarith [hq.1, hq.2, hp.1, c.hc₁, c.hc₂, c.hε]
    have hcqlt : c.cq < f q := by unfold cq; linarith [c.hε]
    have tube_fact : ∀ x' ∈ c.qTube, ∃ y, morseNorm n y < c.ρq ∧ negPart c.dq.hk y ≠ 0 ∧
        c.dq.χ.symm (c.D.π c.cq x') = y ∧ c.dq.χ y = c.D.π c.cq x' ∧
        morseNormalForm c.dq.hk (f q) y = c.cq := by
      intro x' hx'
      obtain ⟨y, ⟨hy1, hy2⟩, hyeq⟩ := hx'.2.2
      have hsrc : y ∈ c.dq.χ.source :=
        c.dq.hball (mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy1 hρR'))
      refine ⟨y, hy1, hy2, by rw [← hyeq, c.dq.χ.left_inv hsrc], hyeq, ?_⟩
      rw [← c.dq.hnorm y (hy1.le.trans hρR.le), hyeq]
      exact GradientLikeStrip.f_π hfs hcq hx'.2.1
    have lift_fact : ∀ x' ∈ c.qTube, negPart c.dq.hk (c.qExtendedChart x') ≠ 0 ∧
        modelLift c.dq.hk (f q) c.cq (c.qExtendedChart x') = c.dq.χ.symm (c.D.π c.cq x') := by
      intro x' hx'
      obtain ⟨y, -, hy2, hyc, -, hynf⟩ := tube_fact x' hx'
      have hfx' : f x' < f q := hx'.1.trans hcqlt
      obtain ⟨-, hdir, hprod, -⟩ := modelLift_spec c.dq.hk hfx' hy2
      rw [c.qExtendedChart_eq_of_mem_qTube hx', hyc]
      have hne : negPart c.dq.hk (modelLift c.dq.hk (f q) (f x') y) ≠ 0 := by
        intro h0
        rw [h0, smul_zero] at hdir
        have hn : ‖negPart c.dq.hk y‖ ≠ 0 := norm_ne_zero_iff.mpr hy2
        exact hy2 ((smul_eq_zero.mp hdir.symm).resolve_left (inv_ne_zero hn))
      refine ⟨hne, ?_⟩
      rw [modelLift_congr c.dq.hk hne hy2 hdir hprod]
      have h := (modelLift_spec c.dq.hk hcqlt hy2).2.2.2 (by rw [hynf]; exact hcqlt)
      rwa [hynf] at h
    set G : (Fin n → ℝ) → M := fun y' => c.D.flow (c.cq - morseNormalForm c.dq.hk (f q) y')
      (c.dq.χ (modelLift c.dq.hk (f q) c.cq y')) with hG
    have hGinv : ∀ x' ∈ c.qTube, G (c.qExtendedChart x') = x' := by
      intro x' hx'
      obtain ⟨y, -, -, hyc, hyχ, -⟩ := tube_fact x' hx'
      have hnf := c.nf_qExtendedChart (Or.inr hx' : x' ∈ c.qDom)
      simp only [hG]
      rw [hnf, (lift_fact x' hx').2, hyc, hyχ]
      unfold GradientLikeStrip.π
      rw [c.D.flow_flow, show f x' - c.cq + (c.cq - f x') = 0 by ring, c.D.flow_zero]
    have hev : (G ∘ c.qExtendedChart) =ᶠ[𝓝 x] id :=
      eventuallyEq_of_mem (hTopen.mem_nhds hxt) fun x' hx' => hGinv x' hx'
    obtain ⟨hne0, hlift0⟩ := lift_fact x hxt
    obtain ⟨y0, hy01, -, hy0c, -, -⟩ := tube_fact x hxt
    have hML : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
        (fun y' => modelLift c.dq.hk (f q) c.cq y') (c.qExtendedChart x) := by
      have hopen : IsOpen {z : ℝ × (Fin n → ℝ) | z.1 < f q ∧ negPart c.dq.hk z.2 ≠ 0} :=
        (isOpen_lt continuous_fst continuous_const).inter
          (isOpen_ne_fun (c.dq.continuous_negPart.comp continuous_snd) continuous_const)
      have h1 := (contDiffOn_modelLift c.dq.hk (f q)).contDiffAt
        (hopen.mem_nhds (show (c.cq, c.qExtendedChart x) ∈ _ from ⟨hcqlt, hne0⟩))
      have h2 : ContDiffAt ℝ ∞ (fun y' : Fin n → ℝ => ((c.cq, y') : ℝ × (Fin n → ℝ)))
          (c.qExtendedChart x) :=
        (contDiff_const.prodMk contDiff_id).contDiffAt
      exact ((h1.comp (c.qExtendedChart x) h2).differentiableAt (by simp)).mdifferentiableAt
    have hχd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I c.dq.χ
        (modelLift c.dq.hk (f q) c.cq (c.qExtendedChart x)) := by
      rw [hlift0, hy0c]
      exact c.dq.mdifferentiableAt_chart (mem_ball_of_morseNorm_lt (lt_of_lt_of_le hy01 hρR'))
    have hnfd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ)
        (fun y' => c.cq - morseNormalForm c.dq.hk (f q) y') (c.qExtendedChart x) :=
      ((contDiff_const.sub (ModelField.contDiff_nf c.dq.hk (f q))).contDiffAt.differentiableAt
        (by simp)).mdifferentiableAt
    have hpair : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, ℝ).prod I)
        (fun y' => (c.cq - morseNormalForm c.dq.hk (f q) y',
          c.dq.χ (modelLift c.dq.hk (f q) c.cq y'))) (c.qExtendedChart x) :=
      hnfd.prodMk (hχd.comp (c.qExtendedChart x) hML)
    have hGd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I G (c.qExtendedChart x) :=
      (c.D.contMDiff_flow_joint.mdifferentiableAt (by simp)).comp (c.qExtendedChart x) hpair
    exact key G hGd hev
  · have hxb : x ∈ c.qBall := (show x ∈ c.qBall ∨ x ∈ c.qTube from hx).resolve_right hxt
    have hBopen : IsOpen c.qBall := c.dq.isOpen_image_of_lt hρR'
    have hball : ∀ x' ∈ c.qBall, c.qExtendedChart x' = c.dq.χ.symm x' := fun x' hx' => by
      simp only [qExtendedChart, hx', ↓reduceIte]
    have hev : (c.dq.χ ∘ c.qExtendedChart) =ᶠ[𝓝 x] id :=
      eventuallyEq_of_mem (hBopen.mem_nhds hxb) fun x' hx' => by
        change c.dq.χ (c.qExtendedChart x') = x'
        rw [hball x' hx']
        exact c.dq.symm_image_eq (c.dq.image_lt_subset_image_ball hρR' hx')
    have hχd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I c.dq.χ (c.qExtendedChart x) := by
      rw [hball x hxb]
      exact c.dq.mdifferentiableAt_chart
        (c.dq.symm_mem_ball (c.dq.image_lt_subset_image_ball hρR' hxb))
    exact key c.dq.χ hχd hev

theorem mem_arc_of_qExtendedChart {x : M} (hx : x ∈ c.qDom) (h₁ : c.qPerp (c.qExtendedChart x) = 0)
    (h₂ : posPart c.dq.hk (c.qExtendedChart x) = 0) (h₃ : 0 ≤ c.qArc (c.qExtendedChart x)) : x ∈ c.arc := by
  classical
  have hε := c.hε
  obtain ⟨-, hu₀, -⟩ := c.unit_dirs
  have hneg : negPart c.dq.hk (c.qExtendedChart x) = c.qArc (c.qExtendedChart x) • c.u₀ := sub_eq_zero.1 h₁
  have hy : c.qExtendedChart x = recombine c.dq.hk (c.qArc (c.qExtendedChart x) • c.u₀) 0 := by
    rw [← hneg, ← h₂, DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]
  have hrm := c.D.hrm q (mem_pair_right p q)
  have hρq : c.ρq < c.D.rm q (mem_pair_right p q) := by
    have hrm0 : 0 < c.D.rm q (mem_pair_right p q) := c.D.rm_pos q (mem_pair_right p q)
    have h8 := c.hrmq
    unfold ρq
    rw [Real.sqrt_lt' hrm0]
    linarith
  by_cases hball : x ∈ c.qBall
  · obtain ⟨y', hy', rfl⟩ := hball
    have hy'lt : morseNorm n y' < c.ρq := hy'
    have hsrc : y' ∈ c.dq.χ.source := c.dq.hsrc y' (by linarith [hy'lt.le, hρq, hrm.2])
    have hb : c.dq.χ y' ∈ c.qBall := mem_image_of_mem _ hy'
    have hΨ : c.qExtendedChart (c.dq.χ y') = y' := by
      simp only [qExtendedChart, hb, ↓reduceIte]
      rw [c.dq.χ.left_inv hsrc]
    set t := c.qArc (c.qExtendedChart (c.dq.χ y')) with ht
    rw [hΨ] at hy
    rw [hy] at hy'lt
    have hnorm : morseNorm n (recombine c.dq.hk (t • c.u₀) 0) = t := by
      have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq
        c.dq.hk (t • c.u₀) 0
      rw [norm_smul, hu₀, norm_zero, Real.norm_eq_abs, abs_of_nonneg h₃] at hsq
      have h0 : 0 ≤ morseNorm n (recombine c.dq.hk (t • c.u₀) 0) := by
        unfold morseNorm; positivity
      nlinarith
    rw [hy]
    rcases h₃.eq_or_lt with h0 | hpos
    · rw [← h0, zero_smul]
      have : recombine c.dq.hk (0 : EuclideanSpace ℝ (Fin c.dq.k)) 0 = 0 := by
        rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dq.hk 0]
        rfl
      rw [this, c.dq.hχ0]
      exact c.q_mem_arc
    · apply c.q_ray_mem_arc hpos
      have hlt : t < c.ρq := by rw [hnorm] at hy'lt; exact hy'lt
      have hsq : c.ρq ^ 2 = 5 * c.ε / 2 := Real.sq_sqrt (by linarith)
      nlinarith
  · obtain ⟨hfx, hΩ, y'', ⟨hy''n, hy''u⟩, hπ⟩ := hx.resolve_left hball
    have hsrc : y'' ∈ c.dq.χ.source := c.dq.hsrc y'' (by linarith [hy''n.le, hρq, hrm.2])
    have hΨ : c.qExtendedChart x = modelLift c.dq.hk (f q) (f x) y'' := by
      simp only [qExtendedChart, hball, ↓reduceIte]
      rw [← hπ, c.dq.χ.left_inv hsrc]
    have hs : f x < f q := by
      have : c.cq = f q - c.ε := rfl
      linarith
    obtain ⟨-, hdir, hprod, -⟩ := modelLift_spec c.dq.hk hs hy''u
    set t := c.qArc (c.qExtendedChart x) with ht
    rw [← hΨ, hy, ModelField.negPart_recombine] at hdir
    rw [← hΨ, hy, ModelField.negPart_recombine, ModelField.posPart_recombine] at hprod
    have hN : ‖negPart c.dq.hk y''‖ ≠ 0 := norm_ne_zero_iff.2 hy''u
    have hv : posPart c.dq.hk y'' = 0 := by
      rw [smul_zero] at hprod
      exact (smul_eq_zero.1 hprod.symm).resolve_left hN
    have htpos : 0 < t := by
      rcases h₃.eq_or_lt with h0 | hpos
      · exfalso
        rw [← h0, zero_smul, smul_zero] at hdir
        exact hy''u ((smul_eq_zero.1 hdir.symm).resolve_left (inv_ne_zero hN))
      · exact hpos
    have hdir' : ‖negPart c.dq.hk y''‖⁻¹ • negPart c.dq.hk y'' = c.u₀ := by
      rw [← hdir, norm_smul, hu₀, mul_one, Real.norm_eq_abs, abs_of_pos htpos, smul_smul,
        inv_mul_cancel₀ htpos.ne', one_smul]
    have hu : negPart c.dq.hk y'' = ‖negPart c.dq.hk y''‖ • c.u₀ := by
      rw [← hdir', smul_smul, mul_inv_cancel₀ hN, one_smul]
    have hp' : f p ∈ Ioo a' b' := ((c.hcrit p).1 (mem_pair_left p q)).1
    have hq' : f q ∈ Ioo a' b' := ((c.hcrit q).1 (mem_pair_right p q)).1
    have hc : c.cq ∈ Icc a' b' := by
      have : c.cq = f q - c.ε := rfl
      have h1 := c.hc₁
      have h2 := c.hc₂
      constructor <;> linarith [hp'.1, hq'.2]
    have hlev : f (c.D.π c.cq x) = c.cq := GradientLikeStrip.f_π c.hf.smooth hc hΩ
    have hnf : f (c.dq.χ y'') = morseNormalForm c.dq.hk (f q) y'' :=
      c.dq.hnorm y'' (by linarith [hy''n.le, hρq, hrm.2])
    rw [← hπ, hnf, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hv,
      norm_zero] at hlev
    have hsq : ‖negPart c.dq.hk y''‖ ^ 2 = 2 * c.ε := by
      have : c.cq = f q - c.ε := rfl
      linarith
    have hnrm : ‖negPart c.dq.hk y''‖ = Real.sqrt (2 * c.ε) := by
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    have hy''eq : y'' = c.dq.sphereParam c.ε c.w₀ := by
      rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose c.dq.hk y'',
        hv, hu, hnrm, MorseNormalChart.sphereParam, TransverseCancellingPair.u₀, smul_smul, div_eq_mul_inv]
    have hπz : c.D.π c.cq x = c.z₀ := by
      rw [← hπ, hy''eq]
      rfl
    refine Or.inr ⟨-(f x - c.cq), ?_⟩
    change c.D.flow (-(f x - c.cq)) c.z₀ = x
    rw [← hπz, GradientLikeStrip.π, c.D.flow_flow, add_neg_cancel, GradientLikeStrip.flow_zero]

theorem qExtendedChart_p_ray {t : ℝ} (ht : 0 < t) (ht' : |t ^ 2 - 2 * c.ε| ≤ 6 * c.βmax) :
    c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈ c.qTube ∧
      c.qExtendedChart (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) =
        recombine c.dq.hk (Real.sqrt (c.sqSum - t ^ 2) • c.u₀) 0 := by
  classical
  have hε : 0 < c.ε := c.hε
  have hr₀p : c.dp.r₀ ^ 2 < 2 * c.ε := c.hr₀p
  have hr₀q : c.dq.r₀ ^ 2 < 2 * c.ε := c.hr₀q
  have hc₁ : f p + c.ε < c.c := c.hc₁
  have hc₂ : c.c < f q - c.ε := c.hc₂
  have hβ1 : c.βmax ≤ c.ε / 16 := (min_le_left _ _).trans (min_le_left _ _)
  have hβ2 : c.βmax ≤ (f q - f p - 2 * c.ε) / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have hβ3 : c.βmax ≤ (2 * c.ε - c.dp.r₀ ^ 2) / 16 := min_le_right _ _
  obtain ⟨ht1, ht2⟩ := abs_le.1 ht'
  have ht0 : 0 < t ^ 2 := pow_pos ht 2
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  obtain ⟨he₁, hu₀, -⟩ := c.unit_dirs
  have hRp : 8 * c.ε < c.dp.R ^ 2 := by
    have h1 := (c.D.hrm p (Finset.mem_insert_self p {q})).2
    have h2 := c.D.rm_pos p (Finset.mem_insert_self p {q})
    have h3 : 8 * c.ε < c.D.rm p (Finset.mem_insert_self p {q}) ^ 2 := c.hrmp
    have h4 := pow_le_pow_left₀ h2.le h1 2
    linarith only [h3, h4]
  have hRq : 8 * c.ε < c.dq.R ^ 2 := by
    have h1 := (c.D.hrm q (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))).2
    have h2 := c.D.rm_pos q (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    have h3 : 8 * c.ε < c.D.rm q (Finset.mem_insert_of_mem (Finset.mem_singleton_self q)) ^ 2 :=
      c.hrmq
    have h4 := pow_le_pow_left₀ h2.le h1 2
    linarith only [h3, h4]
  have hRq' : c.dq.R < c.dq.R' := c.dq.hRR'
  have hRq0 : 0 < c.dq.R := c.dq.R_pos
  have hyn : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ^ 2 = t ^ 2 := by
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_recombine_sq, norm_zero,
      norm_smul, he₁, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hyR : morseNorm n (recombine c.dp.hk 0 (t • c.e₁)) ≤ c.dp.R :=
    MorseNormalChart.morseNorm_le_of_sq_le c.dp.R_pos.le (by
      rw [hyn]; linarith only [hRp, ht2, hβ1, hε])
  have hfx : f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) = f p + t ^ 2 / 2 := by
    rw [c.dp.hnorm _ hyR, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split,
      ModelField.negPart_recombine, ModelField.posPart_recombine, norm_zero, norm_smul, he₁,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hfxlt : f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) < f q - c.ε := by
    rw [hfx]; linarith only [ht2, hβ2, hc₁, hc₂]
  have hfxgt : f p + c.dp.r₀ ^ 2 / 2 < f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) := by
    rw [hfx]; linarith only [ht1, hβ3, hr₀p]
  have hpS : f p ∈ Ioo a' b' := c.D.inStrip p _ c.dp.p_mem_image_ball
  have hqS : f q ∈ Ioo a' b' := c.D.inStrip q _ c.dq.p_mem_image_ball
  have hpq : p ≠ q := fun h => by have := c.hlt; rw [h] at this; exact lt_irrefl _ this
  have hxarc := c.p_ray_mem_arc ht (by linarith only [ht2, hβ1, hε])
  obtain ⟨τ, hτ⟩ : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈
      range (fun s : ℝ => c.D.flow s c.z₀) := by
    rcases hxarc with (h | h) | h
    · exfalso
      have h' : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) = p := h
      have := hfx; rw [h'] at this; linarith only [this, ht0]
    · exfalso
      have h' : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) = q := h
      have := hfxlt; rw [h'] at this; linarith only [this, hε]
    · exact h
  have hcqS : c.cq ∈ Icc a' b' := by
    unfold cq; constructor
    · linarith only [hpS.1, hc₁, hc₂, hε]
    · linarith only [hqS.2, hε]
  have hΩ : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈ c.D.regularFlowDomain c.cq := by
    refine ⟨⟨by linarith only [hpS.1, hfx, ht0], by linarith only [hqS.2, hfxlt, hε]⟩,
      fun s hs p' hp' hmem => ?_⟩
    have hfxlt' : f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) - c.cq ≤ 0 := by
      unfold cq; linarith only [hfxlt]
    rw [uIcc_of_ge hfxlt'] at hs
    have hlev := GradientLikeStrip.f_flow_mem_uIcc (D := c.D) hfs
      (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) s
    rw [uIcc_of_le (by linarith only [hs.2])] at hlev
    have hlev2 : f (c.D.flow s (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)))) ≤ f q - c.ε := by
      have h3 := hs.1
      unfold cq at h3
      linarith only [hlev.2, h3]
    obtain ⟨z, hz, hzx⟩ := hmem
    have hz' : morseNorm n z ≤ (c.D.chart p' hp').r₀ := hz
    have hzR : morseNorm n z ≤ (c.D.chart p' hp').R :=
      hz'.trans (c.D.r₀_lt_R p' hp').le
    have hnf := (c.D.chart p' hp').hnorm z hzR
    rw [hzx, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hnf
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (c.D.chart p' hp').hk z
    have hn0 := ModelField.morseNorm_nonneg z
    have hz2 : morseNorm n z ^ 2 ≤ (c.D.chart p' hp').r₀ ^ 2 :=
      pow_le_pow_left₀ hn0 hz' 2
    have hA := sq_nonneg ‖negPart (c.D.chart p' hp').hk z‖
    have hB := sq_nonneg ‖posPart (c.D.chart p' hp').hk z‖
    rcases Finset.mem_insert.1 hp' with hp'' | hp''
    · subst p'
      linarith only [hnf, hsq, hz2, hA, hlev.1, hfxgt]
    · rw [Finset.mem_singleton] at hp''
      subst p'
      linarith only [hnf, hsq, hz2, hB, hlev2, hr₀q]
  have hw₀ : c.w₀ ≠ 0 := c.hw₀.1
  have hRq2 : 2 * c.ε ≤ c.dq.R ^ 2 := by linarith only [hRq, hε]
  have hz₀lev : f c.z₀ = f q - c.ε :=
    c.dq.f_chart_of_mem_leftModelSphere hRq2 (c.dq.sphereParam_mem_leftModelSphere hε.le hw₀)
  have hπ : c.D.π c.cq (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) = c.z₀ := by
    refine c.arc_level_inj ⟨τ + (f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) - c.cq), ?_⟩
      ⟨0, GradientLikeStrip.flow_zero _ _⟩ ?_
    · change c.D.flow _ c.z₀ = c.D.flow _ _
      rw [← GradientLikeStrip.flow_flow]
      exact congrArg _ hτ
    · rw [GradientLikeStrip.f_π hfs hcqS hΩ, hz₀lev]; rfl
  have hsph := c.dq.sphereParam_mem_leftModelSphere hε.le hw₀
  have hsphn : morseNorm n (c.dq.sphereParam c.ε c.w₀) ^ 2 = 2 * c.ε :=
    c.dq.morseNorm_sq_of_mem_leftModelSphere hsph
  have hsymm : c.dq.χ.symm c.z₀ = c.dq.sphereParam c.ε c.w₀ :=
    c.dq.χ.left_inv (c.dq.hsrc _ (c.dq.morseNorm_sphereParam_le hε.le hRq2 hw₀))
  refine ⟨⟨hfxlt, hΩ, ?_⟩, ?_⟩
  · rw [hπ]
    refine ⟨c.dq.sphereParam c.ε c.w₀, ⟨?_, ?_⟩, rfl⟩
    · change morseNorm n (c.dq.sphereParam c.ε c.w₀) < Real.sqrt (5 * c.ε / 2)
      rw [Real.lt_sqrt (ModelField.morseNorm_nonneg _), hsphn]; linarith only [hε]
    · intro h
      have := hsph.2
      rw [h, norm_zero] at this
      linarith only [this, hε]
  · have hnb : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∉ c.qBall := by
      intro hmem
      have hρ : c.ρq ≤ c.dq.R' := by
        unfold ρq
        rw [Real.sqrt_le_iff]
        refine ⟨(hRq0.trans hRq').le, ?_⟩
        have := pow_lt_pow_left₀ hRq' hRq0.le two_ne_zero
        linarith only [this, hRq, hε]
      have h1 : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈ c.dq.χ '' Metric.ball 0 c.dq.R' :=
        c.dq.image_lt_subset_image_ball hρ hmem
      have h2 : c.dp.χ (recombine c.dp.hk 0 (t • c.e₁)) ∈ c.dp.χ '' Metric.ball 0 c.dp.R' :=
        ⟨_, c.dp.mem_ball_of_le hyR, rfl⟩
      exact Set.disjoint_left.1 (c.D.disjoint p _ q _ hpq) h2 h1
    have hs0 : 0 < Real.sqrt (2 * c.ε) := Real.sqrt_pos.2 (mul_pos two_pos hε)
    have hneg : negPart c.dq.hk (c.dq.sphereParam c.ε c.w₀) = Real.sqrt (2 * c.ε) • c.u₀ := by
      rw [MorseNormalChart.negPart_sphereParam]
      unfold u₀
      rw [smul_smul, div_eq_mul_inv]
    have hpos : posPart c.dq.hk (c.dq.sphereParam c.ε c.w₀) = 0 :=
      MorseNormalChart.posPart_sphereParam _ _ _
    have hNn : ‖Real.sqrt (2 * c.ε) • c.u₀‖ = Real.sqrt (2 * c.ε) := by
      rw [norm_smul, hu₀, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
    have hpos' : 0 ≤ f q - f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))) := by
      linarith only [hfxlt, hε]
    have hL : liftScale (f q) (f (c.dp.χ (recombine c.dp.hk 0 (t • c.e₁))))
        (‖Real.sqrt (2 * c.ε) • c.u₀‖ ^ 2 * ‖(0 : EuclideanSpace ℝ (Fin (n - c.dq.k)))‖ ^ 2) =
        Real.sqrt (c.sqSum - t ^ 2) := by
      unfold liftScale
      rw [norm_zero, zero_pow two_ne_zero, mul_zero, add_zero, Real.sqrt_sq hpos']
      congr 1
      rw [hfx]; unfold sqSum cq fb; ring
    unfold qExtendedChart
    rw [ite_eq_right hnb, hπ, hsymm]
    unfold modelLift
    rw [hneg, hpos, hL, hNn]
    congr 1
    · rw [smul_smul, div_mul_cancel₀ _ hs0.ne']
    · exact smul_zero _

theorem transversal_y₀ :
    DifferentiableAt ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀ ∧
      Function.Injective (fun w : Fin n → ℝ =>
        (fderiv ℝ (morseNormalForm c.dp.hk (f p)) c.y₀ w, negPart c.dp.hk w,
          fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀ w)) := by
  classical
  have hqc : q ∈ ({p, q} : Finset M) := mem_pair_right p q
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth
  have hε : 0 < c.ε := c.hε
  obtain ⟨he₁, hu₀, hy₀⟩ := c.unit_dirs
  have hpq1 := c.hc₁
  have hpq2 := c.hc₂
  have hr₀p := c.hr₀p
  have hβ : 0 ≤ c.βmax := by
    unfold βmax
    refine le_min (le_min ?_ ?_) ?_
    · linarith
    · linarith
    · linarith
  have hsq : c.sqSum = 2 * (f q - f p) := by unfold sqSum cq fb; ring
  set s₀ : ℝ := Real.sqrt (2 * c.ε) with hs₀def
  have hs₀ : 0 < s₀ := Real.sqrt_pos.2 (by linarith)
  have hs₀sq : s₀ ^ 2 = 2 * c.ε := Real.sq_sqrt (by linarith)
  obtain ⟨hmemT, hΨ⟩ := c.qExtendedChart_p_ray hs₀ (by rw [hs₀sq, sub_self, abs_zero]; linarith)
  rw [← hy₀] at hmemT hΨ
  obtain ⟨y', hy'R, hy'eq⟩ := c.hw₀.2
  have hy₀' : c.y₀ = y' := by
    change c.dp.χ.symm _ = y'
    rw [← hy'eq]; exact c.dp.χ.left_inv (c.dp.hsrc y' (le_of_lt hy'R))
  have hy₀R : morseNorm n c.y₀ < c.dp.R := hy₀' ▸ hy'R
  have hχy₀ : c.dp.χ c.y₀ = c.D.landing p hqc c.ε c.c c.ε c.w₀ := by rw [hy₀', hy'eq]
  obtain ⟨hqDomOpen, hΨsmooth⟩ := c.contMDiffOn_qExtendedChart
  have hx₀Dom : c.dp.χ c.y₀ ∈ c.qDom := Or.inr hmemT
  have hy₀ball : c.y₀ ∈ Metric.ball (0 : Fin n → ℝ) c.dp.R' := c.dp.mem_ball_of_le hy₀R.le
  have hχsm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ c.dp.χ c.y₀ := c.dp.contMDiffAt_chart hy₀ball
  have hΨsmAt : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.qExtendedChart (c.dp.χ c.y₀) :=
    hΨsmooth.contMDiffAt (hqDomOpen.mem_nhds hx₀Dom)
  have hGsm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀ :=
    hΨsmAt.comp c.y₀ hχsm
  have hGd : DifferentiableAt ℝ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀ :=
    (contMDiffAt_iff_contDiffAt.1 hGsm).differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀ :=
    (ModelField.posPartL c.dq.hk).differentiableAt.comp c.y₀ hGd
  have hΨmd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ c.y₀) :=
    hΨsmAt.mdifferentiableAt (by simp)
  have hχmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀ := c.dp.mdifferentiableAt_chart hy₀ball
  have hGmf : fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀ =
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.qExtendedChart (c.dp.χ c.y₀)).comp
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀) := by
    have hcomp := mfderiv_comp c.y₀ hΨmd hχmd
    rw [mfderiv_eq_fderiv] at hcomp
    ext1 v
    exact DFunLike.congr_fun hcomp v
  have hχinj : Function.Injective (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀) := by
    have hcomp := mfderiv_comp c.y₀ (c.dp.mdifferentiableAt_symm (mem_image_of_mem _ hy₀ball)) hχmd
    have hev : (c.dp.χ.symm ∘ c.dp.χ) =ᶠ[𝓝 c.y₀] id :=
      eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy₀ball) fun z hz =>
        c.dp.χ.left_inv (c.dp.hball hz)
    have h1 := hev.mfderiv_eq (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))
    rw [mfderiv_id] at h1
    have key : ∀ v, mfderiv I 𝓘(ℝ, Fin n → ℝ) c.dp.χ.symm (c.dp.χ c.y₀)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀ v) = v := fun v =>
      DFunLike.congr_fun (hcomp.symm.trans h1) v
    exact Function.LeftInverse.injective key
  have hχsurj : Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀) := by
    let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := mfderiv 𝓘(ℝ, Fin n → ℝ) I c.dp.χ c.y₀
    have hinj : Function.Injective L.toLinearMap := hχinj
    exact LinearMap.injective_iff_surjective.1 hinj
  have hGsurj : Function.Surjective (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀) := by
    rw [hGmf]
    exact (c.surjective_mfderiv_qExtendedChart hx₀Dom).comp hχsurj
  have hNev : morseNormalForm c.dp.hk (f p) =ᶠ[𝓝 c.y₀]
      (fun y => morseNormalForm c.dq.hk (f q) (c.qExtendedChart (c.dp.χ y))) := by
    have h1 : ∀ᶠ y in 𝓝 c.y₀, morseNorm n y < c.dp.R := (isOpen_morseNorm_lt _).mem_nhds hy₀R
    have h2 : ∀ᶠ y in 𝓝 c.y₀, c.dp.χ y ∈ c.qDom :=
      hχsm.continuousAt.preimage_mem_nhds (hqDomOpen.mem_nhds hx₀Dom)
    filter_upwards [h1, h2] with y hy1 hy2
    rw [c.nf_qExtendedChart hy2, c.dp.hnorm y hy1.le]
  have hA : fderiv ℝ (morseNormalForm c.dp.hk (f p)) c.y₀ =
      (fderiv ℝ (morseNormalForm c.dq.hk (f q)) (c.qExtendedChart (c.dp.χ c.y₀))).comp
        (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀) := by
    rw [hNev.fderiv_eq]
    exact fderiv_comp (x := c.y₀) (g := morseNormalForm c.dq.hk (f q))
      (f := fun y => c.qExtendedChart (c.dp.χ y))
      ((ModelField.contDiff_nf c.dq.hk (f q)).differentiable (by simp) _) hGd
  have hB : fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀ =
      (ModelField.posPartL c.dq.hk).comp (fderiv ℝ (fun y => c.qExtendedChart (c.dp.χ y)) c.y₀) :=
    ((ModelField.posPartL c.dq.hk).hasFDerivAt.comp c.y₀ hGd.hasFDerivAt).fderiv
  set σ : ℝ := Real.sqrt (c.sqSum - s₀ ^ 2) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by rw [hsq, hs₀sq]; linarith)
  set Φ : (Fin n → ℝ) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin (n - c.dq.k)) :=
    (fderiv ℝ (morseNormalForm c.dp.hk (f p)) c.y₀).prod
      (fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀) with hΦdef
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨s, v'⟩
    obtain ⟨w, hw⟩ := hGsurj (recombine c.dq.hk ((-s / σ) • c.u₀) v')
    refine ⟨w, ?_⟩
    rw [hΦdef, ContinuousLinearMap.prod_apply, hA, hB, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hw, ModelField.fderiv_nf_apply, hΨ, ModelField.posPartL_apply,
      ModelField.posPart_recombine, ModelField.posPart_recombine, ModelField.negPart_recombine,
      ModelField.negPart_recombine, inner_zero_left, zero_sub, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hu₀]
    congr 1
    simp only [RCLike.conj_to_real]
    field_simp
  have hkq : c.dq.k = c.dp.k + 1 := by
    rw [← c.dq.hkidx, ← c.dp.hkidx]; exact c.hidx
  have hkn : c.dq.k ≤ n := c.dq.hk
  have hker : Module.finrank ℝ (LinearMap.ker Φ.toLinearMap) = c.dp.k := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ.toLinearMap
    rw [LinearMap.range_eq_top.2 hΦsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin, Module.finrank_fin_fun] at h1
    omega
  have hw₀ne : c.w₀ ≠ 0 := c.hw₀.1
  have hεR : 2 * c.ε ≤ c.dq.R ^ 2 := by
    have h1 := c.hrmq
    have h2 := (c.D.hrm q hqc).2
    have h3 := c.D.rm_pos q hqc
    have h4 : c.D.rm q hqc ^ 2 ≤ c.dq.R ^ 2 := pow_le_pow_left₀ h3.le h2 2
    linarith
  set ℓ : (Fin c.dq.k → ℝ) → Fin n → ℝ :=
    fun w => c.dp.χ.symm (c.D.landing p hqc c.ε c.c c.ε w) with hℓdef
  have hℓw₀ : ℓ c.w₀ = c.y₀ := rfl
  have hℓd : DifferentiableAt ℝ ℓ c.w₀ := by
    have hsp : ContMDiffAt 𝓘(ℝ, Fin c.dq.k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (c.dq.sphereParam c.ε) c.w₀ :=
      contMDiffAt_iff_contDiffAt.2 (c.dq.contDiffAt_sphereParam c.ε hw₀ne)
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ c.dq.χ (c.dq.sphereParam c.ε c.w₀) :=
      c.dq.contMDiffAt_chart (c.dq.mem_ball_of_le (c.dq.morseNorm_sphereParam_le hε.le hεR hw₀ne))
    have hfl1 : ContMDiffAt I I ∞ (c.D.flow (f q - c.ε - c.c))
        (c.dq.χ (c.dq.sphereParam c.ε c.w₀)) := (c.D.contMDiff_flow _).contMDiffAt
    have hfl2 : ContMDiffAt I I ∞ (c.D.flow (c.c - (f p + c.ε)))
        (c.D.flow (f q - c.ε - c.c) (c.dq.χ (c.dq.sphereParam c.ε c.w₀))) :=
      (c.D.contMDiff_flow _).contMDiffAt
    have hsymm : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ c.dp.χ.symm
        (c.D.flow (c.c - (f p + c.ε))
          (c.D.flow (f q - c.ε - c.c) (c.dq.χ (c.dq.sphereParam c.ε c.w₀)))) := by
      apply c.dp.contMDiffAt_symm
      have := mem_image_of_mem c.dp.χ hy₀ball
      rw [hχy₀] at this
      exact this
    have c4 : ContMDiffAt 𝓘(ℝ, Fin c.dq.k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ℓ c.w₀ :=
      hsymm.comp c.w₀ (hfl2.comp c.w₀ (hfl1.comp c.w₀ (hχq.comp c.w₀ hsp)))
    exact (contMDiffAt_iff_contDiffAt.1 c4).differentiableAt (by simp)
  have hv₀ : posPart c.dp.hk c.y₀ = s₀ • c.e₁ := by rw [hy₀, ModelField.posPart_recombine]
  have hu₀y : negPart c.dp.hk c.y₀ = 0 := by rw [hy₀, ModelField.negPart_recombine]
  have hv₀ne : posPart c.dp.hk c.y₀ ≠ 0 := by
    rw [hv₀]
    exact smul_ne_zero hs₀.ne' (norm_ne_zero_iff.1 (by rw [he₁]; exact one_ne_zero))
  have hv₀norm : ‖posPart c.dp.hk c.y₀‖ = s₀ := by
    rw [hv₀, norm_smul, he₁, mul_one, Real.norm_eq_abs, abs_of_pos hs₀]
  have hsard : ∀ ξ, fderiv ℝ (c.D.sardMap p hqc c.ε c.c c.ε (mem_pair_left p q)) c.w₀ ξ =
      s₀ • negPart c.dp.hk (fderiv ℝ ℓ c.w₀ ξ) := by
    intro ξ
    have hJd : DifferentiableAt ℝ (ModelField.scaledNegativePart c.dp.hk) (ℓ c.w₀) :=
      (ModelField.contDiffAt_scaledNegativePart c.dp.hk hv₀ne).differentiableAt (by simp)
    have h1 : fderiv ℝ (c.D.sardMap p hqc c.ε c.c c.ε (mem_pair_left p q)) c.w₀ =
        (fderiv ℝ (ModelField.scaledNegativePart c.dp.hk) (ℓ c.w₀)).comp (fderiv ℝ ℓ c.w₀) :=
      fderiv_comp (x := c.w₀) (g := ModelField.scaledNegativePart c.dp.hk) (f := ℓ) hJd hℓd
    rw [h1, ContinuousLinearMap.comp_apply, hℓw₀, ModelField.fderiv_scaledNegativePart_apply c.dp.hk hv₀ne, hu₀y,
      smul_zero, zero_add, hv₀norm]
  have hpa : a' < f p := (c.D.f_mem_Ioo p (mem_pair_left p q)).1
  have hqb : f q < b' := (c.D.f_mem_Ioo q hqc).2
  have hr₀q := c.hr₀q
  have hdomO : IsOpen (c.D.sardDom p hqc c.ε c.c c.ε (mem_pair_left p q)) :=
    GradientLikeStrip.isOpen_sardDom hε.le hεR
  have hdom : ∀ w ∈ c.D.sardDom p hqc c.ε c.c c.ε (mem_pair_left p q),
      morseNormalForm c.dp.hk (f p) (ℓ w) = f p + c.ε ∧
        posPart c.dq.hk (c.qExtendedChart (c.dp.χ (ℓ w))) = 0 := by
    rintro w ⟨hw, y'', hy''R, hy''eq⟩
    have hw' : w ≠ 0 := hw
    have hℓw : ℓ w = y'' := by
      change c.dp.χ.symm _ = y''
      rw [← hy''eq]; exact c.dp.χ.left_inv (c.dp.hsrc y'' (le_of_lt hy''R))
    have hχℓ : c.dp.χ (ℓ w) = c.D.landing p hqc c.ε c.c c.ε w := by rw [hℓw, hy''eq]
    set x₁ : M := c.dq.χ (c.dq.sphereParam c.ε w) with hx₁
    have hsph := c.dq.sphereParam_mem_leftModelSphere hε.le hw'
    have hfx₁ : f x₁ = f q - c.ε := c.dq.f_chart_of_mem_leftModelSphere hεR hsph
    set T : ℝ := f q - c.ε - (f p + c.ε) with hT
    have hland : c.D.landing p hqc c.ε c.c c.ε w = c.D.flow T x₁ := by
      change c.D.flow (c.c - (f p + c.ε)) (c.D.flow (f q - c.ε - c.c) x₁) = _
      rw [GradientLikeStrip.flow_flow, hT]
      congr 1
      ring
    have hlevels : ∀ s ∈ uIcc 0 T, f (c.D.flow s x₁) = f x₁ - s :=
      GradientLikeStrip.f_flow_eq_sub_of_levels hfs
        (by rw [hfx₁]; exact ⟨by linarith, by linarith⟩)
        (by rw [hfx₁, hT]; exact ⟨by linarith, by linarith⟩) (by
          intro y hy
          rw [hfx₁, hT, uIcc_of_ge (by linarith)] at hy
          exact c.hlev y ⟨by linarith [hy.1], hy.2⟩)
    have hfland : f (c.D.landing p hqc c.ε c.c c.ε w) = f p + c.ε := by
      rw [hland, hlevels T right_mem_uIcc, hfx₁, hT]; ring
    refine ⟨?_, ?_⟩
    · rw [hℓw, ← c.dp.hnorm y'' (le_of_lt hy''R), hy''eq, hfland]
    · set x := c.D.landing p hqc c.ε c.c c.ε w with hxdef
      have hfxcq : f x - c.cq = -T := by rw [hfland]; unfold cq; rw [hT]; ring
      have hπ : c.D.π c.cq x = x₁ := by
        change c.D.flow (f x - c.cq) x = x₁
        rw [hfxcq, hland, GradientLikeStrip.flow_neg_flow]
      have hΩ : x ∈ c.D.regularFlowDomain c.cq := by
        refine ⟨by rw [hfland]; exact ⟨by linarith, by linarith⟩, ?_⟩
        intro s hs p' hp' hmem
        rw [hfxcq, uIcc_of_ge (by linarith)] at hs
        have hfs' : f (c.D.flow s x) = f p + c.ε - s := by
          rw [hland, GradientLikeStrip.flow_flow, hlevels (T + s) (by
            rw [uIcc_of_le (by linarith)]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩),
            hfx₁, hT]
          ring
        have hab := GradientLikeStrip.abs_f_sub_le_of_mem_closedSmallBall hmem
        rw [hfs', abs_le] at hab
        rcases (mem_pair_iff.1 hp') with rfl | rfl
        · linarith [hab.2, hs.2]
        · linarith [hab.1, hs.1]
      have hmemT' : x ∈ c.qTube := by
        refine ⟨?_, hΩ, ?_⟩
        · rw [hfland]; unfold cq; linarith
        · rw [hπ]
          refine ⟨c.dq.sphereParam c.ε w, ⟨?_, ?_⟩, rfl⟩
          · have h1 := Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart c.dq.hk
              (c.dq.sphereParam c.ε w)
            rw [hsph.1, hsph.2, norm_zero] at h1
            unfold ρq
            rw [show morseNorm n (c.dq.sphereParam c.ε w) =
                Real.sqrt (morseNorm n (c.dq.sphereParam c.ε w) ^ 2) from
                (Real.sqrt_sq (ModelField.morseNorm_nonneg _)).symm, h1]
            exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
          · intro h0
            have h2 := hsph.2
            rw [h0, norm_zero, zero_pow two_ne_zero] at h2
            linarith
      rw [hχℓ, c.qExtendedChart_eq_of_mem_qTube hmemT', hπ, hx₁,
        c.dq.χ.left_inv (c.dq.hsrc _ (c.dq.morseNorm_sphereParam_le hε.le hεR hw'))]
      unfold modelLift
      rw [ModelField.posPart_recombine, hsph.1, smul_zero]
  have hw₀dom : c.w₀ ∈ c.D.sardDom p hqc c.ε c.c c.ε (mem_pair_left p q) := c.hw₀
  have hNℓ : (fun w => morseNormalForm c.dp.hk (f p) (ℓ w)) =ᶠ[𝓝 c.w₀] fun _ => f p + c.ε :=
    eventuallyEq_of_mem (hdomO.mem_nhds hw₀dom) fun w hw => (hdom w hw).1
  have hbℓ : (fun w => posPart c.dq.hk (c.qExtendedChart (c.dp.χ (ℓ w)))) =ᶠ[𝓝 c.w₀]
      fun _ => (0 : EuclideanSpace ℝ (Fin (n - c.dq.k))) :=
    eventuallyEq_of_mem (hdomO.mem_nhds hw₀dom) fun w hw => (hdom w hw).2
  have hNℓ' : ∀ ξ, fderiv ℝ (morseNormalForm c.dp.hk (f p)) c.y₀ (fderiv ℝ ℓ c.w₀ ξ) = 0 := by
    intro ξ
    have h1 : fderiv ℝ (fun w => morseNormalForm c.dp.hk (f p) (ℓ w)) c.w₀ =
        (fderiv ℝ (morseNormalForm c.dp.hk (f p)) (ℓ c.w₀)).comp (fderiv ℝ ℓ c.w₀) :=
      fderiv_comp (x := c.w₀) (g := morseNormalForm c.dp.hk (f p)) (f := ℓ)
        ((ModelField.contDiff_nf c.dp.hk (f p)).differentiable (by simp) _) hℓd
    have h2 := DFunLike.congr_fun (h1.symm.trans (hNℓ.fderiv_eq.trans (fderiv_const_apply _))) ξ
    rw [ContinuousLinearMap.comp_apply, _root_.zero_apply] at h2
    exact h2
  have hbℓ' : ∀ ξ, fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) c.y₀
      (fderiv ℝ ℓ c.w₀ ξ) = 0 := by
    intro ξ
    have h1 : fderiv ℝ (fun w => posPart c.dq.hk (c.qExtendedChart (c.dp.χ (ℓ w)))) c.w₀ =
        (fderiv ℝ (fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (ℓ c.w₀)).comp
          (fderiv ℝ ℓ c.w₀) :=
      fderiv_comp (x := c.w₀) (g := fun y => posPart c.dq.hk (c.qExtendedChart (c.dp.χ y))) (f := ℓ) hbd hℓd
    have h2 := DFunLike.congr_fun (h1.symm.trans (hbℓ.fderiv_eq.trans (fderiv_const_apply _))) ξ
    rw [ContinuousLinearMap.comp_apply, _root_.zero_apply] at h2
    exact h2
  set K := LinearMap.ker Φ.toLinearMap with hK
  have hmemK : ∀ ξ, fderiv ℝ ℓ c.w₀ ξ ∈ K := by
    intro ξ
    rw [hK, LinearMap.mem_ker]
    change Φ (fderiv ℝ ℓ c.w₀ ξ) = 0
    rw [hΦdef, ContinuousLinearMap.prod_apply, hNℓ' ξ, hbℓ' ξ]
    rfl
  let φ : K →ₗ[ℝ] EuclideanSpace ℝ (Fin c.dp.k) :=
    (ModelField.negPartL c.dp.hk).toLinearMap ∘ₗ K.subtype
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨ξ, hξ⟩ := c.hsurj (s₀ • e)
    refine ⟨⟨fderiv ℝ ℓ c.w₀ ξ, hmemK ξ⟩, ?_⟩
    have h1 := hsard ξ
    rw [hξ] at h1
    change negPart c.dp.hk (fderiv ℝ ℓ c.w₀ ξ) = e
    exact (smul_right_injective _ hs₀.ne' h1).symm
  have hφinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hker, finrank_euclideanSpace_fin])).2 hφsurj
  refine ⟨hbd, ?_⟩
  intro w₁ w₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hdiff : w₁ - w₂ ∈ K := by
    rw [hK, LinearMap.mem_ker]
    change Φ (w₁ - w₂) = 0
    rw [map_sub, hΦdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply, h1, h3,
      sub_self]
  have hφ0 : φ ⟨w₁ - w₂, hdiff⟩ = 0 := by
    change negPart c.dp.hk (w₁ - w₂) = 0
    rw [← ModelField.negPartL_apply, map_sub, ModelField.negPartL_apply,
      ModelField.negPartL_apply, h2, sub_self]
  have h0 := hφinj (hφ0.trans φ.map_zero.symm)
  have h4 := congrArg Subtype.val h0
  exact sub_eq_zero.1 h4

end TransverseCancellingPair

end CrossField

end

end DifferentialGeometry.Topology
