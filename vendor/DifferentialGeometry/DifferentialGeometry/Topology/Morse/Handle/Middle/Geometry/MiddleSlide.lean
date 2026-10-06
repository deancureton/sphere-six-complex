module

public import Mathlib.Topology.Algebra.Order.Floor
public import DifferentialGeometry.Topology.Morse.Handle.Middle.Geometry.MiddleWhitney

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

def slideDom (m : ℕ) (η : ℝ) : Set (Fin m → ℝ) :=
  {y | 0 < coordN y 0 ∧ coordN y 0 < 3 ∧ ∀ j, 1 ≤ j → |coordN y j| < η}

def slideA (m ℓ : ℕ) : Set (Fin m → ℝ) :=
  {y | coordN y 0 = 1 ∧ ∀ j, ℓ + 1 ≤ j → coordN y j = 0}

def slideB (m ℓ : ℕ) : Set (Fin m → ℝ) :=
  {y | coordN y 0 = 2 ∧ ∀ j, 1 ≤ j → j ≤ ℓ → coordN y j = 0}

def slidePt (m : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

def slideTwist (m : ℕ) (y : Fin m → ℝ) : Fin m → ℝ := fun i =>
  if (i : ℕ) = 1 then
    Real.cos (Real.pi * Real.smoothTransition (3 * coordN y 0 - 4)) * coordN y 1 -
      Real.sin (Real.pi * Real.smoothTransition (3 * coordN y 0 - 4)) * coordN y (m - 1)
  else if (i : ℕ) = m - 1 then
    Real.sin (Real.pi * Real.smoothTransition (3 * coordN y 0 - 4)) * coordN y 1 +
      Real.cos (Real.pi * Real.smoothTransition (3 * coordN y 0 - 4)) * coordN y (m - 1)
  else y i

def isSlideFinger (m ℓ : ℕ) (η : ℝ) (K : Set (Fin m → ℝ)) (Hs : ℝ → (Fin m → ℝ) → (Fin m → ℝ)) :
    Prop :=
  IsCompact K ∧ K ⊆ slideDom m η ∧ ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => Hs p.1 p.2) ∧
    (∀ t, Function.Bijective (Hs t)) ∧ (∀ t y, Function.Bijective (fderiv ℝ (Hs t) y)) ∧
    (∀ t y, y ∉ K → Hs t y = y) ∧ (∀ t, t ≤ 0 → ∀ y, Hs t y = y) ∧
    (∀ t, 1 ≤ t → ∀ y, Hs t y = Hs 1 y) ∧ (∀ t y j, 1 ≤ j → coordN (Hs t y) j = coordN y j) ∧
    (∀ y ∈ slideA m ℓ, y ∈ slideDom m η → Hs 1 y ∉ slideB m ℓ) ∧
    ∃ t₀ ∈ Ioo (0 : ℝ) 1, Hs t₀ (slidePt m) ∈ slideB m ℓ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ slideA m ℓ, y ∈ slideDom m η → Hs t y ∈ slideB m ℓ →
        t = t₀ ∧ y = slidePt m) ∧
      0 < deriv (fun t => coordN (Hs t (slidePt m)) 0) t₀

theorem exists_finger_isotopy (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓm : ℓ + 2 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ K Hs, isSlideFinger m ℓ η K Hs := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨ρ, hρs, hρd, hρm, hρid, -, hρ1, -⟩ :=
    MonotoneShift.exists_monotoneShift (c₀ := 1 / 2) (x₀ := 1) (y₀ := 5 / 2) (c₁ := 11 / 4)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have hcoord : ∀ (y : Fin (k + 1) → ℝ) (i : Fin (k + 1)), coordN y (i : ℕ) = y i := by
    intro y i
    simp [coordN, i.isLt]
  have hcoord0 : ∀ (y : Fin (k + 1) → ℝ), coordN y 0 = y 0 := fun y => hcoord y 0
  obtain ⟨e, he⟩ : ∃ e : Fin (k + 1) → ℝ, e = Pi.single 0 1 := ⟨_, rfl⟩
  have he0 : e 0 = 1 := by simp [he]
  have hei : ∀ i : Fin (k + 1), i ≠ 0 → e i = 0 := by
    intro i hi; simp [he, hi]
  obtain ⟨P, hP⟩ : ∃ P : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ), P = fun y => y - y 0 • e :=
    ⟨_, rfl⟩
  have hPs : ContDiff ℝ ∞ P := by
    rw [hP]
    exact contDiff_id.sub ((contDiff_apply ℝ ℝ (0 : Fin (k + 1))).smul contDiff_const)
  have hP_line : ∀ (y : Fin (k + 1) → ℝ) (c : ℝ), P (y + c • e) = P y := by
    intro y c
    rw [hP]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he0]
    ring
  have hP0 : ∀ y, P y 0 = 0 := by
    intro y; rw [hP]; simp [he0]
  have hPi : ∀ y (i : Fin (k + 1)), i ≠ 0 → P y i = y i := by
    intro y i hi; rw [hP]; simp [hei i hi]
  have hdecomp : ∀ y, y = P y + y 0 • e := by
    intro y; rw [hP]; simp
  obtain ⟨B, hBin, hBout⟩ : ∃ B : ContDiffBump (0 : Fin (k + 1) → ℝ), B.rIn = η / 4 ∧
      B.rOut = η / 2 :=
    ⟨⟨η / 4, η / 2, by positivity, by linarith⟩, rfl, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ, σ = fun t => Real.smoothTransition (4 * t) *
      (t + (1 - t) * Real.smoothTransition (4 * t - 3)) := ⟨_, rfl⟩
  have hσs : ContDiff ℝ ∞ σ := by
    simp only [hσ]
    have h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (4 * t)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
    have h2 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (4 * t - 3)) :=
      Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
    exact h1.mul (contDiff_id.add ((contDiff_const.sub contDiff_id).mul h2))
  have hσ01 : ∀ t, 0 ≤ σ t ∧ σ t ≤ 1 := by
    intro t
    simp only [hσ]
    rcases le_or_gt t 0 with ht | ht
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
    rcases le_or_gt 1 t with ht1 | ht1
    · rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith)]
      constructor <;> linarith
    have a0 := Real.smoothTransition.nonneg (4 * t)
    have a1 := Real.smoothTransition.le_one (4 * t)
    have b0 := Real.smoothTransition.nonneg (4 * t - 3)
    have b1 := Real.smoothTransition.le_one (4 * t - 3)
    have c0 : 0 ≤ t + (1 - t) * Real.smoothTransition (4 * t - 3) := by nlinarith
    have c1 : t + (1 - t) * Real.smoothTransition (4 * t - 3) ≤ 1 := by nlinarith
    exact ⟨mul_nonneg a0 c0, by nlinarith⟩
  have hσ0 : ∀ t, t ≤ 0 → σ t = 0 := by
    intro t ht; rw [hσ]; simp [Real.smoothTransition.zero_of_nonpos (show 4 * t ≤ 0 by linarith)]
  have hσ1 : ∀ t, 1 ≤ t → σ t = 1 := by
    intro t ht; simp only [hσ]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    ring
  have hσmid : ∀ t, 1 / 4 ≤ t → t ≤ 3 / 4 → σ t = t := by
    intro t h1 h2; simp only [hσ]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  have hσlow : ∀ t, 0 ≤ t → t ≤ 1 / 4 → σ t ≤ t := by
    intro t h1 h2; simp only [hσ]
    rw [Real.smoothTransition.zero_of_nonpos (show 4 * t - 3 ≤ 0 by linarith)]
    have a1 := Real.smoothTransition.le_one (4 * t)
    nlinarith
  have hσhigh : ∀ t, 3 / 4 ≤ t → t ≤ 1 → t ≤ σ t := by
    intro t h1 h2; simp only [hσ]
    rw [Real.smoothTransition.one_of_one_le (show 1 ≤ 4 * t by linarith)]
    have b0 := Real.smoothTransition.nonneg (4 * t - 3)
    nlinarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ → (Fin (k + 1) → ℝ) → ℝ, S = fun t y => σ t * B (P y) := ⟨_, rfl⟩
  have hS01 : ∀ t y, 0 ≤ S t y ∧ S t y ≤ 1 := by
    intro t y
    rw [hS]
    obtain ⟨h0, h1⟩ := hσ01 t
    have b0 : 0 ≤ B (P y) := B.nonneg
    have b1 : B (P y) ≤ 1 := B.le_one
    exact ⟨mul_nonneg h0 b0, by nlinarith⟩
  have hS_line : ∀ t y (c : ℝ), S t (y + c • e) = S t y := by
    intro t y c; rw [hS]; simp only [hP_line]
  obtain ⟨Hs, hHs⟩ : ∃ Hs : ℝ → (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ),
      Hs = fun t y => y + (S t y * (ρ (y 0) - y 0)) • e := ⟨_, rfl⟩
  have hHs0 : ∀ t y, Hs t y 0 = y 0 + S t y * (ρ (y 0) - y 0) := by
    intro t y; rw [hHs]; simp [he0]
  have hHsi : ∀ t y (i : Fin (k + 1)), i ≠ 0 → Hs t y i = y i := by
    intro t y i hi; rw [hHs]; simp [hei i hi]
  have hPHs : ∀ t y, P (Hs t y) = P y := by
    intro t y; rw [hHs]; exact hP_line _ _
  have hFmono : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → StrictMono (fun x => x + s * (ρ x - x)) := by
    intro s h0 h1 x x' hxx'
    have hd : 0 < x' - x := by linarith
    have hr : 0 < ρ x' - ρ x := by linarith [hρm hxx']
    change x + s * (ρ x - x) < x' + s * (ρ x' - x')
    rcases eq_or_lt_of_le h0 with hs | hs
    · subst hs; linarith
    · nlinarith [mul_pos hs hr, mul_nonneg (sub_nonneg.2 h1) hd.le]
  have hHs_smooth : ContDiff ℝ ∞ (fun p : ℝ × (Fin (k + 1) → ℝ) => Hs p.1 p.2) := by
    rw [hHs, hS]
    have hB : ContDiff ℝ ∞ (fun p : ℝ × (Fin (k + 1) → ℝ) => B (P p.2)) :=
      B.contDiff.comp (hPs.comp contDiff_snd)
    have h0 : ContDiff ℝ ∞ (fun p : ℝ × (Fin (k + 1) → ℝ) => p.2 0) :=
      (contDiff_apply ℝ ℝ (0 : Fin (k + 1))).comp contDiff_snd
    exact contDiff_snd.add ((((hσs.comp contDiff_fst).mul hB).mul
      ((hρs.comp h0).sub h0)).smul contDiff_const)
  have hSP : ∀ t w, S t (P w) = S t w := by
    intro t w
    conv_rhs => rw [hdecomp w]
    rw [hS_line]
  have hbij : ∀ t, Function.Bijective (Hs t) := by
    intro t
    constructor
    · intro y z hyz
      have hPyz : P y = P z := by rw [← hPHs t y, ← hPHs t z, hyz]
      have hSyz : S t y = S t z := by rw [← hSP t y, ← hSP t z, hPyz]
      have h0 : y 0 = z 0 := by
        have := congrFun hyz 0
        rw [hHs0, hHs0, ← hSyz] at this
        exact (hFmono _ (hS01 t y).1 (hS01 t y).2).injective this
      rw [hdecomp y, hdecomp z, hPyz, h0]
    · intro w
      set s := S t w with hs
      have hcont : Continuous (fun x => x + s * (ρ x - x)) :=
        continuous_id.add (continuous_const.mul (hρs.continuous.sub continuous_id))
      obtain ⟨x, hx⟩ : ∃ x, x + s * (ρ x - x) = w 0 := by
        by_cases hw : w 0 ∈ Ioo (1 / 2 : ℝ) (11 / 4)
        · have hmem : w 0 ∈ Icc ((fun x => x + s * (ρ x - x)) (1 / 2))
              ((fun x => x + s * (ρ x - x)) (11 / 4)) := by
            simp only
            rw [hρid (1 / 2) (by simp), hρid (11 / 4) (by simp)]
            exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
          obtain ⟨x, -, hx⟩ := intermediate_value_Icc (show (1 / 2 : ℝ) ≤ 11 / 4 by norm_num)
            hcont.continuousOn hmem
          exact ⟨x, hx⟩
        · exact ⟨w 0, by rw [hρid _ hw]; ring⟩
      have hS' : S t (P w + x • e) = s := by rw [hS_line, hSP]
      have hy0 : (P w + x • e) 0 = x := by simp [hP0, he0]
      refine ⟨P w + x • e, funext fun i => ?_⟩
      by_cases hi : i = 0
      · subst hi; rw [hHs0, hy0, hS', hx]
      · rw [hHsi t _ i hi]; simp [hPi w i hi, hei i hi]
  have hfd : ∀ t y, Function.Bijective (fderiv ℝ (Hs t) y) := by
    intro t y
    obtain ⟨g, hg⟩ : ∃ g : (Fin (k + 1) → ℝ) → ℝ, g = fun y => S t y * (ρ (y 0) - y 0) :=
      ⟨_, rfl⟩
    have hgs : ContDiff ℝ ∞ g := by
      rw [hg, hS]
      have h0 : ContDiff ℝ ∞ (fun y : Fin (k + 1) → ℝ => y 0) := contDiff_apply ℝ ℝ 0
      exact (contDiff_const.mul (B.contDiff.comp hPs)).mul ((hρs.comp h0).sub h0)
    have hgd : DifferentiableAt ℝ g y := (hgs.differentiable (by simp)) y
    have hHt : Hs t = fun y => y + g y • e := by rw [hHs, hg]
    have hD : HasFDerivAt (Hs t) (ContinuousLinearMap.id ℝ (Fin (k + 1) → ℝ) +
        (fderiv ℝ g y).smulRight e) y := by
      rw [hHt]; exact (hasFDerivAt_id y).add (hgd.hasFDerivAt.smul_const e)
    rw [hD.fderiv]
    have hge : fderiv ℝ g y e = S t y * (deriv ρ (y 0) - 1) := by
      have hl : HasDerivAt (fun τ : ℝ => y + τ • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
      have h1 : HasDerivAt (g ∘ fun τ : ℝ => y + τ • e) (fderiv ℝ g y e) 0 :=
        hgd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
      have hfun : (g ∘ fun τ : ℝ => y + τ • e) = fun τ => S t y * (ρ (y 0 + τ) - (y 0 + τ)) := by
        funext τ
        simp only [Function.comp, hg, hS_line]
        congr 2 <;> simp [he0]
      rw [hfun] at h1
      have hρ' : HasDerivAt (fun τ => ρ (y 0 + τ)) (deriv ρ (y 0)) 0 := by
        apply HasDerivAt.comp_const_add
        simpa using ((hρs.differentiable (by simp)) (y 0)).hasDerivAt
      have h2 : HasDerivAt (fun τ => S t y * (ρ (y 0 + τ) - (y 0 + τ)))
          (S t y * (deriv ρ (y 0) - 1)) 0 :=
        (hρ'.sub ((hasDerivAt_id (0 : ℝ)).const_add (y 0))).const_mul (S t y)
      exact h1.unique h2
    have hinj : Function.Injective (ContinuousLinearMap.id ℝ (Fin (k + 1) → ℝ) +
        (fderiv ℝ g y).smulRight e) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      have hv' : ∀ i, v i + fderiv ℝ g y v * e i = 0 := fun i => by
        have := congrFun hv i
        simpa using this
      have hvi : ∀ i, i ≠ 0 → v i = 0 := fun i hi => by
        have := hv' i
        rw [hei i hi] at this
        linarith
      have hvdec : v = v 0 • e := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp [he0]
        · simp [hvi i hi, hei i hi]
      have h1 : fderiv ℝ g y v = v 0 * fderiv ℝ g y e := by
        conv_lhs => rw [hvdec]
        rw [map_smul, smul_eq_mul]
      have h0 := hv' 0
      rw [h1, hge, he0] at h0
      obtain ⟨s0, s1⟩ := hS01 t y
      have hpos : 0 < 1 + S t y * (deriv ρ (y 0) - 1) := by
        have := hρd (y 0)
        rcases eq_or_lt_of_le s0 with hs | hs
        · rw [← hs]; norm_num
        · nlinarith [mul_pos hs this]
      have hv0 : v 0 = 0 := by
        have : v 0 * (1 + S t y * (deriv ρ (y 0) - 1)) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · linarith
      rw [hvdec, hv0, zero_smul]
    refine ⟨hinj, ?_⟩
    have := (LinearMap.injective_iff_surjective
      (f := ((ContinuousLinearMap.id ℝ (Fin (k + 1) → ℝ) + (fderiv ℝ g y).smulRight e :
        (Fin (k + 1) → ℝ) →L[ℝ] (Fin (k + 1) → ℝ)) : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ)))).mp
      hinj
    exact this
  have hsp0 : slidePt (k + 1) 0 = 1 := by simp [slidePt]
  have hPsp : P (slidePt (k + 1)) = 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi; rw [hP0]; rfl
    · rw [hPi _ i hi]
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [slidePt, this]
  have hB0 : B 0 = 1 := B.one_of_mem_closedBall (Metric.mem_closedBall_self (by rw [hBin]; positivity))
  have hHsp0 : ∀ t, Hs t (slidePt (k + 1)) 0 = 1 + σ t * (3 / 2) := by
    intro t
    rw [hHs0, hS]
    simp only [hPsp, hB0, hsp0, hρ1]
    ring
  have hAB : ∀ t y, y ∈ slideA (k + 1) ℓ → Hs t y ∈ slideB (k + 1) ℓ → y = slidePt (k + 1) := by
    intro t y hA hB
    obtain ⟨hA0, hA1⟩ := hA
    obtain ⟨-, hB1⟩ := hB
    funext i
    simp only [slidePt]
    by_cases hi : (i : ℕ) = 0
    · have : i = 0 := Fin.ext hi
      subst this; rw [← hcoord0 y, hA0]; simp
    · simp only [hi, ↓reduceIte]
      have hi' : i ≠ 0 := fun h => hi (by simp [h])
      by_cases hiℓ : (i : ℕ) ≤ ℓ
      · have := hB1 i (by omega) hiℓ
        rw [hcoord, hHsi t y i hi'] at this
        exact this
      · have := hA1 i (by omega)
        rw [hcoord] at this
        exact this
  set K : Set (Fin (k + 1) → ℝ) := Set.univ.pi (fun i : Fin (k + 1) =>
    if i = 0 then Icc (1 / 2 : ℝ) (11 / 4) else Icc (-(η / 2)) (η / 2)) with hK
  have hmemK : ∀ y, y ∈ K ↔ y 0 ∈ Icc (1 / 2 : ℝ) (11 / 4) ∧
      ∀ i, i ≠ 0 → y i ∈ Icc (-(η / 2)) (η / 2) := by
    intro y
    rw [hK, Set.mem_univ_pi]
    constructor
    · intro h
      refine ⟨by simpa using h 0, fun i hi => by simpa [hi] using h i⟩
    · rintro ⟨h0, h1⟩ i
      by_cases hi : i = 0
      · subst hi; simpa using h0
      · simpa [hi] using h1 i hi
  unfold isSlideFinger
  refine ⟨K, Hs, ?_, ?_, hHs_smooth, hbij, hfd, ?_, ?_, ?_, ?_, ?_, 2 / 3,
    ⟨by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · exact isCompact_univ_pi fun i => by split_ifs <;> exact isCompact_Icc
  · intro y hy
    obtain ⟨h0, h1⟩ := (hmemK y).1 hy
    refine ⟨by rw [hcoord0]; linarith [h0.1], by rw [hcoord0]; linarith [h0.2], fun j hj => ?_⟩
    unfold coordN
    split_ifs with h
    · have hne : (⟨j, h⟩ : Fin (k + 1)) ≠ 0 := by
        intro hc; rw [Fin.ext_iff] at hc; simp at hc; omega
      obtain ⟨a1, a2⟩ := h1 _ hne
      rw [abs_lt]; constructor <;> linarith
    · simpa using hη
  · intro t y hy
    rw [hHs]
    simp only
    have hz : S t y * (ρ (y 0) - y 0) = 0 := by
      by_cases h0 : y 0 ∈ Ioo (1 / 2 : ℝ) (11 / 4)
      · have : ∃ i, i ≠ 0 ∧ y i ∉ Icc (-(η / 2)) (η / 2) := by
          by_contra hcon
          simp only [not_exists, not_and, not_not] at hcon
          exact hy ((hmemK y).2 ⟨Ioo_subset_Icc_self h0, hcon⟩)
        obtain ⟨i, hi, hyi⟩ := this
        have hBz : B (P y) = 0 := by
          apply B.zero_of_le_dist
          rw [hBout, dist_zero_right]
          have h1 := norm_le_pi_norm (P y) i
          rw [hPi y i hi, Real.norm_eq_abs] at h1
          have h2 : η / 2 < |y i| := by
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hyi
            rcases hyi with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; exact h
          linarith
        rw [hS]; simp [hBz]
      · rw [hρid _ h0]; ring
    rw [hz, zero_smul, add_zero]
  · intro t ht y
    rw [hHs, hS]
    simp [hσ0 t ht]
  · intro t ht y
    rw [hHs, hS]
    simp only [hσ1 t ht, hσ1 1 le_rfl]
  · intro t y j hj
    unfold coordN
    split_ifs with h
    · have hne : (⟨j, h⟩ : Fin (k + 1)) ≠ 0 := by
        intro hc; rw [Fin.ext_iff] at hc; simp at hc; omega
      exact hHsi t y _ hne
    · rfl
  · intro y hA _ hB
    have hy := hAB 1 y hA hB
    subst hy
    obtain ⟨h0, -⟩ := hB
    rw [hcoord0, hHsp0, hσ1 1 le_rfl] at h0
    norm_num at h0
  · refine ⟨?_, fun j hj1 _ => ?_⟩
    · rw [hcoord0, hHsp0, hσmid _ (by norm_num) (by norm_num)]; norm_num
    · unfold coordN
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin (k + 1)) ≠ 0 := by
          intro hc; rw [Fin.ext_iff] at hc; simp at hc; omega
        rw [hHsi _ _ _ hne]
        have : j ≠ 0 := by omega
        simp [slidePt, this]
      · rfl
  · intro t ht y hA _ hB
    have hy := hAB t y hA hB
    subst hy
    refine ⟨?_, rfl⟩
    obtain ⟨h0, -⟩ := hB
    rw [hcoord0, hHsp0] at h0
    have hσt : σ t = 2 / 3 := by linarith
    rcases lt_or_ge t (1 / 4) with h1 | h1
    · have := hσlow t ht.1 h1.le
      linarith
    rcases lt_or_ge (3 / 4) t with h2 | h2
    · have := hσhigh t h2.le ht.2
      linarith
    rw [hσmid t h1 h2] at hσt
    exact hσt
  · have hfun : (fun t => coordN (Hs t (slidePt (k + 1))) 0) = fun t => 1 + σ t * (3 / 2) := by
      funext t; rw [hcoord0, hHsp0]
    rw [hfun]
    have hev : (fun t => 1 + σ t * (3 / 2)) =ᶠ[𝓝 (2 / 3 : ℝ)] fun t => 1 + t * (3 / 2) := by
      filter_upwards [Ioo_mem_nhds (show (1 / 4 : ℝ) < 2 / 3 by norm_num)
        (show (2 / 3 : ℝ) < 3 / 4 by norm_num)] with t ht
      rw [hσmid t ht.1.le ht.2.le]
    rw [hev.deriv_eq]
    have : HasDerivAt (fun t : ℝ => 1 + t * (3 / 2)) (3 / 2) (2 / 3) := by
      simpa using ((hasDerivAt_id (2 / 3 : ℝ)).mul_const (3 / 2 : ℝ)).const_add 1
    rw [this.deriv]; norm_num

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

def isSlideChart (D : GradientLikeStrip I f a b crit) {c₂ κ : ℝ} (Ch : D.CollarChart c₂ κ)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) (ε η : ℝ) (ℓ : ℕ) : Prop :=
  Ch.U = slideDom (n - 1) η ∧
    (∀ y ∈ slideDom (n - 1) η, Ch.φ y ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ y ∈ slideA (n - 1) ℓ) ∧
    ∀ y ∈ slideDom (n - 1) η, Ch.φ y ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ y ∈ slideB (n - 1) ℓ

structure SlideSetup (D : GradientLikeStrip I f a b crit) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit)
    (hq₂ : q₂ ∈ crit) (ε : ℝ) (ℓ : ℕ) (c c₂ κ : ℝ) : Prop where
  hε : 0 < ε
  hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2
  hℓ : 2 ≤ ℓ
  hℓn : ℓ + 3 ≤ n
  hk₁ : (D.chart q₁ hq₁).k = ℓ + 1
  hk₂ : (D.chart q₂ hq₂).k = ℓ + 1
  hne : q₁ ≠ q₂
  hac : a < c
  hcq₂ : c < f q₂ - ε
  hκ : 0 < κ
  hq₂c₂ : f q₂ + ε < c₂ - κ
  hc₂q₁ : c₂ + κ < f q₁ - ε
  hq₁b : f q₁ < b
  hunit : ∀ y, f y ∈ Icc c (f q₂ - ε) ∪ Icc (f q₂ + ε) (f q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx
  hslab : ∀ x ∈ crit, f x ∈ Icc c (f q₁ - ε) → x = q₂
  hmodel : ∀ x (hx : x ∈ crit), ∀ z ∈ (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx},
    f z ∉ Icc (c₂ - κ) (c₂ + κ)
  hdisj : Disjoint (D.leftSphere q₁ hq₁ ε c₂) (D.rightSphere q₂ hq₂ ε c₂)

theorem disjoint_spheres_of_noCommon (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {x y : M} (hx : x ∈ crit) (hy : y ∈ crit) {ε c r : ℝ}
    (hε : 0 < ε) (hεr : ∀ z hz, (D.chart z hz).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm z hz ^ 2)
    (hr : 0 < r) (hyc : f y + ε ≤ c) (hcx : c ≤ f x - ε) (hcb : a ≤ c ∧ c ≤ b)
    (hU : ∀ z, f z ∈ Icc (f y + ε) (f x - ε) → ∀ w hw, z ∉ D.smallBall w hw)
    (hnoc : D.noCommon x hx y hy r r) :
    Disjoint (D.leftSphere x hx ε c) (D.rightSphere y hy ε c) := by
  have _hlev : _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨hf, hyc, hcx, hcb, hU⟩
  clear _hlev hf hyc hcx hcb hU
  rw [Set.disjoint_left]
  intro z hzL hzR
  obtain ⟨p₀, ⟨w, hw, rfl⟩, hzp⟩ := hzL
  obtain ⟨q₀, ⟨w', hw', rfl⟩, hzq⟩ := hzR
  set dx := D.chart x hx with hdx
  set dy := D.chart y hy with hdy
  have hr₀x := dx.hr₀
  have hεx := hεr x hx
  have hεy := hεr y hy
  have hrmx := D.rm_pos x hx
  have hrmy := D.rm_pos y hy
  have hwn : morseNorm n w ^ 2 = 2 * ε := dx.morseNorm_sq_of_mem_leftModelSphere hw
  have hw'n : morseNorm n w' ^ 2 = 2 * ε := dy.morseNorm_sq_of_mem_rightModelSphere hw'
  have hwrm : morseNorm n w < D.rm x hx := by
    have h0 := ModelField.morseNorm_nonneg w
    nlinarith
  have hw'rm : morseNorm n w' < D.rm y hy := by
    have h0 := ModelField.morseNorm_nonneg w'
    nlinarith
  have hwR : morseNorm n w ≤ dx.R := hwrm.le.trans (D.hrm x hx).2
  have hcap : dy.χ w' ∈ D.captured y hy :=
    D.mem_captured_of_mem_stable ⟨w', ⟨hw'rm, hw'.1⟩, rfl⟩
  obtain ⟨T', hT'⟩ := D.captured_eventually_small hcap hr
  have hfwd := hT' T' le_rfl
  set θ₀ : ℝ := (morseNorm n w ^ 2 + dx.r₀ ^ 2)⁻¹ with hθ₀def
  have hθ₀ : 0 < θ₀ := by positivity
  set T : ℝ := 2 * ε / (2 * θ₀ * r ^ 2) with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hTr : r ^ 2 * (2 * θ₀ * T) = 2 * ε := by
    rw [hTdef]
    field_simp
  have hstay : ∀ s, s ≤ 0 → D.flow s (dx.χ w) ∈ dx.χ ''
      {z | morseNorm n z ≤ morseNorm n w ∧ posPart dx.hk z = 0} := fun s hs =>
    flow_mem_of_posPart_eq_zero hx hwrm hw.1 hs
  have hsub : {z : Fin n → ℝ | morseNorm n z ≤ morseNorm n w ∧ posPart dx.hk z = 0} ⊆
      {z | morseNorm n z < D.rm x hx} := fun z hz => lt_of_le_of_lt hz.1 hwrm
  have hODE : ∀ s ∈ Icc (-T) 0, D.flow s (dx.χ w) ∈ dx.χ '' {z | morseNorm n z < D.rm x hx} :=
    fun s hs => image_mono hsub (hstay s hs.2)
  have hγ := hasDerivAt_symm_flow_Icc hx hODE
  have hθ : ∀ s ∈ Icc (-T) 0,
      θ₀ ≤ ModelField.theta dx.r₀ (dx.χ.symm (D.flow s (dx.χ w))) := fun s hs => by
    have hmem := dx.symm_mem (hsub.trans (dx.lt_subset_ball (D.rm_lt_R' x hx).le))
      (hstay s hs.2)
    exact ModelField.theta_ge_of_le hr₀x hmem.1
  have hgrow := ModelField.normSq_negPart_ge_linear dx.hk hr₀x hγ hθ 0
    (right_mem_Icc.2 (by linarith))
  obtain ⟨z₁, ⟨hz₁a, hz₁b⟩, hz₁x⟩ := hstay (-T) (by linarith)
  have hγ0 : dx.χ.symm (D.flow 0 (dx.χ w)) = w := by
    rw [flow_zero, dx.χ.left_inv (dx.hsrc w hwR)]
  have hγT : dx.χ.symm (D.flow (-T) (dx.χ w)) = z₁ := by
    rw [← hz₁x, dx.χ.left_inv (dx.hsrc z₁ (hz₁a.trans hwR))]
  rw [hγ0, hγT] at hgrow
  have hz' := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
    dx.hk z₁
  have hwsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
    dx.hk w
  rw [hz₁b, norm_zero] at hz'
  rw [hw.1, norm_zero] at hwsq
  have hz₁r : morseNorm n z₁ < r := by
    have hlt : morseNorm n z₁ ^ 2 < r ^ 2 := by
      by_contra hcon
      replace hcon := not_lt.1 hcon
      have h1 : r ^ 2 * (2 * θ₀ * T) ≤ morseNorm n z₁ ^ 2 * (2 * θ₀ * T) :=
        mul_le_mul_of_nonneg_right hcon (by positivity)
      have hr2 : 0 < r ^ 2 := by positivity
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hr.le hlt
  have hback : D.flow (-T) (dx.χ w) ∈ dx.χ '' {z | morseNorm n z < r} :=
    ⟨z₁, hz₁r, hz₁x⟩
  refine hnoc _ hback ((f x - ε - c) + T + (c - (f y + ε)) + T') ?_
  obtain ⟨v, hv, hvx⟩ := hfwd
  refine ⟨v, hv.1, ?_⟩
  rw [hvx]
  have e1 : D.flow (f x - ε - c) (dx.χ w) = D.flow (f y + ε - c) (dy.χ w') := hzp.trans hzq.symm
  have e2 : dy.χ w' = D.flow (f x - ε - c + (c - (f y + ε))) (dx.χ w) := by
    rw [← flow_flow, e1, flow_flow, show f y + ε - c + (c - (f y + ε)) = 0 by ring, flow_zero]
  rw [e2, flow_flow, flow_flow]
  congr 1
  ring

theorem exists_level_path {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (L : Finset M)
    (hL : ∀ x ∈ L, x ∈ crit ∧ c₂ + κ < g x - ε ∧ morseIndex I g x ≤ ℓ + 1)
    (hLR : ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ →
      Disjoint (D.leftSphere x hx ε c₂) (D.rightSphere q₂ hq₂ ε c₂))
    (hpc : PathConnectedSpace ↥(g ⁻¹' {c₂})) :
    ∃ δ : ℝ → M, Continuous δ ∧ (∀ t, g (δ t) = c₂) ∧ δ 0 ∈ D.leftSphere q₁ hq₁ ε c₂ ∧
      δ 1 ∈ D.rightSphere q₂ hq₂ ε c₂ ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, δ t ∉ D.leftSphere q₁ hq₁ ε c₂ ∧ δ t ∉ D.rightSphere q₂ hq₂ ε c₂) ∧
      ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ → ∀ t ∈ Icc (0 : ℝ) 1, δ t ∉ D.leftSphere x hx ε c₂ := by
  classical
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hε := hS.hε
  have hεr := hS.hεr
  have hκ := hS.hκ
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hac := hS.hac
  have hcq₂ := hS.hcq₂
  have hq₁b := hS.hq₁b
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hεr x hx).2
    have h2 : D.rm x hx ^ 2 ≤ (D.chart x hx).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos x hx).le (D.hrm x hx).2 2
    linarith
  have hunit' : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hS.hunit y (Or.inr hy)
  have hSL : D.leftSphere q₁ hq₁ ε c₂ ⊆ g ⁻¹' {c₂} := by
    refine D.leftSphere_subset_level hf q₁ hq₁ (hεR _ _) ⟨by linarith, by linarith⟩ ?_
    intro y hy
    rw [uIcc_of_ge (by linarith)] at hy
    exact hunit' y ⟨by linarith [hy.1], hy.2⟩
  have hSR : D.rightSphere q₂ hq₂ ε c₂ ⊆ g ⁻¹' {c₂} := by
    refine D.rightSphere_subset_level hf q₂ hq₂ (hεR _ _) ⟨by linarith, by linarith⟩ ?_
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    exact hunit' y ⟨hy.1, by linarith [hy.2]⟩
  have hLc : IsClosed (D.leftSphere q₁ hq₁ ε c₂) :=
    (D.isCompact_leftSphere q₁ hq₁ (hεR _ _) c₂).isClosed
  have hRc : IsClosed (D.rightSphere q₂ hq₂ ε c₂) :=
    (D.isCompact_rightSphere q₂ hq₂ (hεR _ _) c₂).isClosed
  have key : ∀ y (hy : y ∈ crit), ∀ z ∈ D.leftSphere y hy ε c₂, ∀ s ≤ c₂ - (g y - ε),
      D.flow s z ∈ (D.chart y hy).χ '' Metric.ball 0 (D.chart y hy).R' := by
    intro y hy z hz s hs
    rw [D.mem_leftSphere_iff] at hz
    obtain ⟨u, hu, hux⟩ := hz
    have hurm : morseNorm n u < D.rm y hy := by
      have h1 := (D.chart y hy).morseNorm_sq_of_mem_leftModelSphere hu
      have h2 := (hεr y hy).2
      exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos y hy).le (by linarith)
    have hflow : D.flow s z = D.flow (s - (c₂ - (g y - ε))) (D.flow (c₂ - (g y - ε)) z) := by
      rw [D.flow_flow]; congr 1; ring
    rw [hflow, ← hux]
    obtain ⟨w, hw, hwx⟩ := flow_mem_of_posPart_eq_zero (D := D) hy hurm hu.1
      (t := s - (c₂ - (g y - ε))) (by linarith)
    exact ⟨w, mem_ball_of_morseNorm_lt (lt_of_le_of_lt hw.1 (hurm.trans (D.rm_lt_R' y hy))), hwx⟩
  have hLL : ∀ x (hx : x ∈ crit), x ≠ q₁ →
      Disjoint (D.leftSphere q₁ hq₁ ε c₂) (D.leftSphere x hx ε c₂) := by
    intro x hx hne
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 := key q₁ hq₁ z hz1 (min (c₂ - (g q₁ - ε)) (c₂ - (g x - ε))) (min_le_left _ _)
    have h2 := key x hx z hz2 (min (c₂ - (g q₁ - ε)) (c₂ - (g x - ε))) (min_le_right _ _)
    exact Set.disjoint_left.1 (D.disjoint x hx q₁ hq₁ hne) h2 h1
  obtain ⟨u₀, hu₀⟩ := (D.chart q₁ hq₁).leftModelSphere_nonempty
    (by rw [hS.hk₁]; omega) hε.le
  have hp₀ : D.flow (g q₁ - ε - c₂) ((D.chart q₁ hq₁).χ u₀) ∈ D.leftSphere q₁ hq₁ ε c₂ :=
    ⟨_, ⟨u₀, hu₀, rfl⟩, rfl⟩
  have hk₂n : (D.chart q₂ hq₂).k < n := by have := hS.hk₂; have := hS.hℓn; omega
  obtain ⟨v₀, hv₀⟩ : ((D.chart q₂ hq₂).rightModelSphere ε).Nonempty := by
    refine ⟨recombine (D.chart q₂ hq₂).hk 0 (EuclideanSpace.single
      (⟨0, by omega⟩ : Fin (n - (D.chart q₂ hq₂).k)) (Real.sqrt (2 * ε))), ?_, ?_⟩
    · exact DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine _ _ _
    · rw [DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine]
      simp only [PiLp.norm_single]
      simp only [Nat.ofNat_nonneg, Real.sqrt_mul, norm_mul, Real.norm_eq_abs]
      rw [← abs_mul, sq_abs, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hε.le]
  have hp₁ : D.flow (g q₂ + ε - c₂) ((D.chart q₂ hq₂).χ v₀) ∈ D.rightSphere q₂ hq₂ ε c₂ :=
    ⟨_, ⟨v₀, hv₀, rfl⟩, rfl⟩
  set p₀ := D.flow (g q₁ - ε - c₂) ((D.chart q₁ hq₁).χ u₀) with hp₀def
  set p₁ := D.flow (g q₂ + ε - c₂) ((D.chart q₂ hq₂).χ v₀) with hp₁def
  let P := PathConnectedSpace.somePath (⟨p₀, hSL hp₀⟩ : ↥(g ⁻¹' {c₂})) ⟨p₁, hSR hp₁⟩
  let β : ℝ → M := fun t => ((P.extend t : ↥(g ⁻¹' {c₂})) : M)
  have hβc : Continuous β := continuous_subtype_val.comp P.continuous_extend
  have hβlev : ∀ t, g (β t) = c₂ := fun t => (P.extend t).2
  have hβ0 : β 0 = p₀ := by simp [β, P]
  have hβ1 : β 1 = p₁ := by simp [β, P]
  obtain ⟨Hm, hHc, -, hHA, hHmaps, hHavoid⟩ := D.exists_level_pushOff hf hε hεr hκ
    (c := c₂) ⟨by linarith, by linarith⟩
    (fun y hy => hunit' y ⟨by linarith [hy.1], by linarith [hy.2]⟩) (L.erase q₁) ∅ (m := 1)
    (by
      intro q hq hqL
      obtain ⟨hne, hqL'⟩ := Finset.mem_erase.1 hqL
      obtain ⟨-, h1, h2⟩ := hL q hqL'
      have hk := (D.chart q hq).hkidx
      have := hS.hℓn
      exact ⟨h1, by omega⟩)
    (by intro p hp hpR; simp at hpR) isOpen_univ (F := fun y => β (y 0))
    (hβc.comp (continuous_apply 0)).continuousOn
    (fun y _ => ⟨hβlev (y 0), Set.mem_univ _⟩)
    (A := {y | y 0 = 0 ∨ y 0 = 1})
    ((isClosed_eq (continuous_apply 0) continuous_const).union
      (isClosed_eq (continuous_apply 0) continuous_const))
    (by
      rintro y ⟨hyA, -⟩ hmem
      simp only [sphereUnion, mem_union, mem_iUnion] at hmem
      rcases hmem with ⟨x, hx, hxL, hmem⟩ | ⟨p, hp, hpR, -⟩
      · obtain ⟨hne, hxL'⟩ := Finset.mem_erase.1 hxL
        rcases hyA with h0 | h1
        · have : β (y 0) = p₀ := by rw [h0, hβ0]
          rw [this] at hmem
          exact Set.disjoint_left.1 (hLL x hx hne) hp₀ hmem
        · have : β (y 0) = p₁ := by rw [h1, hβ1]
          rw [this] at hmem
          exact Set.disjoint_left.1 (hLR x hx hxL' hne) hmem hp₁
      · simp at hpR)
  let e : ℝ → (Fin 1 → ℝ) := fun t _ => max 0 (min 1 t)
  have he : ∀ t, e t ∈ Icc (0 : Fin 1 → ℝ) 1 :=
    fun t => ⟨fun _ => le_max_left _ _, fun _ => max_le zero_le_one (min_le_left _ _)⟩
  let γ₀ : ℝ → M := fun t => Hm 1 (e t)
  have hγc : Continuous γ₀ :=
    hHc.comp_continuous (continuous_const.prodMk (continuous_pi fun _ =>
      continuous_const.max (continuous_const.min continuous_id)))
      (fun t => ⟨⟨zero_le_one, le_rfl⟩, he t⟩)
  have hγlev : ∀ t, g (γ₀ t) = c₂ := fun t => (hHmaps 1 ⟨zero_le_one, le_rfl⟩ (he t)).1
  have hγ0 : γ₀ 0 = p₀ := by
    have h := hHA 1 (e 0) (Or.inl (by simp [e]))
    simp only [γ₀, h]
    rw [show e 0 0 = 0 by simp [e], hβ0]
  have hγ1 : γ₀ 1 = p₁ := by
    have h := hHA 1 (e 1) (Or.inr (by simp [e]))
    simp only [γ₀, h]
    rw [show e 1 0 = 1 by simp [e], hβ1]
  have hγL : ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ → ∀ t, γ₀ t ∉ D.leftSphere x hx ε c₂ := by
    intro x hx hxL hne t hmem
    apply hHavoid (e t) (he t)
    exact Or.inl (mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hx, mem_iUnion.2
      ⟨Finset.mem_erase.2 ⟨hne, hxL⟩, hmem⟩⟩⟩)
  obtain ⟨t₀, ⟨ht₀I, ht₀L⟩, ht₀max⟩ :=
    (isCompact_Icc.inter_right (hLc.preimage hγc) :
      IsCompact (Icc (0 : ℝ) 1 ∩ γ₀ ⁻¹' D.leftSphere q₁ hq₁ ε c₂)).exists_isGreatest
      ⟨0, ⟨le_rfl, zero_le_one⟩, by simp only [mem_preimage, hγ0]; exact hp₀⟩
  obtain ⟨t₁, ⟨ht₁I, ht₁R⟩, ht₁min⟩ :=
    (isCompact_Icc.inter_right (hRc.preimage hγc) :
      IsCompact (Icc t₀ 1 ∩ γ₀ ⁻¹' D.rightSphere q₂ hq₂ ε c₂)).exists_isLeast
      ⟨1, ⟨ht₀I.2, le_rfl⟩, by simp only [mem_preimage, hγ1]; exact hp₁⟩
  have ht₀₁ : t₀ < t₁ := by
    rcases ht₁I.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at ht₁R
      exact Set.disjoint_left.1 hS.hdisj ht₀L ht₁R
  refine ⟨fun t => γ₀ (t₀ + t * (t₁ - t₀)), hγc.comp (by fun_prop), fun t => hγlev _, ?_, ?_, ?_, ?_⟩
  · simp only [zero_mul, add_zero]; exact ht₀L
  · simp only [one_mul, add_sub_cancel]; exact ht₁R
  · intro t ht
    have hs₀ : t₀ < t₀ + t * (t₁ - t₀) := by nlinarith [ht.1, ht.2]
    have hs₁ : t₀ + t * (t₁ - t₀) < t₁ := by nlinarith [ht.1, ht.2]
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · have := ht₀max ⟨⟨by linarith [ht₀I.1], by linarith [ht₁I.2]⟩, hmem⟩
      linarith
    · have := ht₁min ⟨⟨hs₀.le, by linarith [ht₁I.2]⟩, hmem⟩
      linarith
  · intro x hx hxL hne t _
    exact hγL x hx hxL hne _

theorem exists_level_arc {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (L : Finset M)
    (hL : ∀ x ∈ L, x ∈ crit ∧ c₂ + κ < g x - ε ∧ morseIndex I g x ≤ ℓ + 1) (δ : ℝ → M)
    (hδ : Continuous δ) (hδlev : ∀ t, g (δ t) = c₂) (hδ0 : δ 0 ∈ D.leftSphere q₁ hq₁ ε c₂)
    (hδ1 : δ 1 ∈ D.rightSphere q₂ hq₂ ε c₂)
    (hδint : ∀ t ∈ Ioo (0 : ℝ) 1, δ t ∉ D.leftSphere q₁ hq₁ ε c₂ ∧ δ t ∉ D.rightSphere q₂ hq₂ ε c₂)
    (hδL : ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ → ∀ t ∈ Icc (0 : ℝ) 1,
      δ t ∉ D.leftSphere x hx ε c₂) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ (∀ t ∈ Icc (0 : ℝ) 3, g (γ t) = c₂) ∧
      InjOn γ (Icc 0 3) ∧ (∀ t ∈ Icc (0 : ℝ) 3, mfderiv 𝓘(ℝ, ℝ) I γ t 1 ≠ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 3, γ t ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ t = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 3, γ t ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ t = 2) ∧
      (∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ → ∀ t ∈ Icc (0 : ℝ) 3, γ t ∉ D.leftSphere x hx ε c₂) ∧
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q₁ hq₁).k))) (D.leftCoord q₁ hq₁ ε) (γ 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ 1 1) ≠ 0 ∧
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε) (γ 2)
          (mfderiv 𝓘(ℝ, ℝ) I γ 2 1) ≠ 0 := by
  classical
  have hlin : ∀ (m : ℕ) (A : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) (v : Fin n → ℝ) (r : ℝ),
      r ≠ 0 → A v ≠ 0 → A (r • v) ≠ 0 := by
    intro m A v r hr hv
    rw [A.map_smul]
    exact smul_ne_zero hr hv
  have harg : ∀ ρ y : ℝ, 0 < ρ → |y| < 1 / 4 → ρ * (4 * y) ∈ Ioo (-ρ) ρ := by
    intro ρ y hρ hy
    rw [abs_lt] at hy
    constructor <;> nlinarith
  have harI1 : ∀ ρ t : ℝ, 0 < ρ → 0 ≤ t → t ≤ 4 / 3 → ρ * (t - 1) ∈ Icc (-ρ) ρ := by
    intro ρ t hρ h0 h1
    constructor <;> nlinarith
  have harI2 : ∀ ρ t : ℝ, 0 < ρ → 5 / 3 < t → t ≤ 3 → ρ * (t - 2) ∈ Icc (-ρ) ρ := by
    intro ρ t hρ h0 h1
    constructor <;> nlinarith
  obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Icc 0 (15 / 16) ∪ Icc (17 / 16) (31 / 16) ∪ Icc (33 / 16) 3 :=
    ⟨_, rfl⟩
  have hJc : IsCompact J := by
    rw [hJdef]; exact (isCompact_Icc.union isCompact_Icc).union isCompact_Icc
  have hJsub : ∀ t ∈ J, t ∈ Icc (0 : ℝ) 3 ∧ t ≠ 1 ∧ t ≠ 2 := by
    intro t ht
    rw [hJdef] at ht
    rcases ht with (h | h) | h <;> obtain ⟨h1, h2⟩ := h <;>
      exact ⟨⟨by linarith, by linarith⟩, by intro h; subst h; norm_num at *,
        by intro h; subst h; norm_num at *⟩
  have hJcov : ∀ t ∈ Icc (0 : ℝ) 3, t ∈ J ∨ |t - 1| < 1 / 16 ∨ |t - 2| < 1 / 16 := by
    intro t ht
    rw [hJdef]
    by_cases h1 : t ≤ 15 / 16
    · exact Or.inl (Or.inl (Or.inl ⟨ht.1, h1⟩))
    by_cases h2 : t < 17 / 16
    · exact Or.inr (Or.inl (abs_lt.2 ⟨by linarith, by linarith⟩))
    by_cases h3 : t ≤ 31 / 16
    · exact Or.inl (Or.inl (Or.inr ⟨by linarith, h3⟩))
    by_cases h4 : t < 33 / 16
    · exact Or.inr (Or.inr (abs_lt.2 ⟨by linarith, by linarith⟩))
    · exact Or.inl (Or.inr ⟨by linarith, ht.2⟩)
  clear hJdef
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ℝ → ℝ → Set ℝ, Pc = fun c w =>
      {θ | Real.cos (2 * Real.pi * w) ≤ Real.cos (2 * Real.pi * (θ - c))} := ⟨_, rfl⟩
  obtain ⟨Uo, hUodef⟩ : ∃ Uo : ℝ → ℝ → Set ℝ, Uo = fun c w =>
      {θ | Real.cos (2 * Real.pi * w) < Real.cos (2 * Real.pi * (θ - c))} := ⟨_, rfl⟩
  have hcosk : ∀ (x : ℝ) (k : ℤ), Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * |x - k|) := by
    intro x k
    have h : 2 * Real.pi * |x - k| = |2 * Real.pi * (x - k)| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    rw [h, Real.cos_abs, show 2 * Real.pi * (x - k) = 2 * Real.pi * x - k * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  have hwI : ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 → 2 * Real.pi * w ∈ Icc 0 Real.pi := fun w h0 h1 =>
    ⟨by positivity, (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (le_of_eq (by ring))⟩
  have hw16 : (0 : ℝ) ≤ 1 / 16 ∧ (1 / 16 : ℝ) ≤ 1 / 2 := by norm_num
  have hw32 : (0 : ℝ) ≤ 1 / 32 ∧ (1 / 32 : ℝ) ≤ 1 / 2 := by norm_num
  have hw64 : (0 : ℝ) ≤ 1 / 64 ∧ (1 / 64 : ℝ) ≤ 1 / 2 := by norm_num
  have h6432 : (1 / 64 : ℝ) < 1 / 32 := by norm_num
  have h3216 : (1 / 32 : ℝ) < 1 / 16 := by norm_num
  have h164 : (1 / 16 : ℝ) < 1 / 4 := by norm_num
  have hmemP : ∀ c w θ, 0 ≤ w → w ≤ 1 / 2 → (θ ∈ Pc c w ↔ ∃ k : ℤ, |θ - c - k| ≤ w) := by
    intro c w θ hw0 hw1
    rw [hPcdef]
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨round (θ - c), ?_⟩
      have hr := abs_sub_round (θ - c)
      rw [hcosk (θ - c) (round (θ - c))] at h
      have := (Real.strictAntiOn_cos.le_iff_ge (hwI w hw0 hw1)
        (hwI _ (abs_nonneg _) hr)).1 h
      exact le_of_mul_le_mul_left this (by positivity)
    · rintro ⟨k, hk⟩
      rw [hcosk (θ - c) k]
      exact (Real.strictAntiOn_cos.le_iff_ge (hwI w hw0 hw1)
        (hwI _ (abs_nonneg _) (hk.trans hw1))).2
        (mul_le_mul_of_nonneg_left hk (by positivity))
  have hmemU : ∀ c w θ, 0 ≤ w → w ≤ 1 / 2 → (θ ∈ Uo c w ↔ ∃ k : ℤ, |θ - c - k| < w) := by
    intro c w θ hw0 hw1
    rw [hUodef]
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨round (θ - c), ?_⟩
      have hr := abs_sub_round (θ - c)
      rw [hcosk (θ - c) (round (θ - c))] at h
      have := (Real.strictAntiOn_cos.lt_iff_gt (hwI w hw0 hw1)
        (hwI _ (abs_nonneg _) hr)).1 h
      exact lt_of_mul_lt_mul_left this (by positivity)
    · rintro ⟨k, hk⟩
      rw [hcosk (θ - c) k]
      exact (Real.strictAntiOn_cos.lt_iff_gt (hwI w hw0 hw1)
        (hwI _ (abs_nonneg _) (hk.le.trans hw1))).2
        (mul_lt_mul_of_pos_left hk (by positivity))
  clear hcosk hwI
  have hPcl : ∀ c w, IsClosed (Pc c w) := fun c w => by
    rw [hPcdef]; exact isClosed_le continuous_const (by fun_prop)
  have hUop : ∀ c w, IsOpen (Uo c w) := fun c w => by
    rw [hUodef]; exact isOpen_lt continuous_const (by fun_prop)
  have hPper : ∀ c w θ, θ ∈ Pc c w ↔ θ + 1 ∈ Pc c w := fun c w θ => by
    rw [hPcdef]
    simp only [mem_ofPred_eq]
    rw [show 2 * Real.pi * (θ + 1 - c) = 2 * Real.pi * (θ - c) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  clear hPcdef
  have hUper : ∀ c w θ, θ ∈ Uo c w ↔ θ + 1 ∈ Uo c w := fun c w θ => by
    rw [hUodef]
    simp only [mem_ofPred_eq]
    rw [show 2 * Real.pi * (θ + 1 - c) = 2 * Real.pi * (θ - c) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  clear hUodef
  have hmaff : ∀ (σ : ℝ → M) (α β t : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I σ (α * t + β) →
      mfderiv 𝓘(ℝ, ℝ) I (fun t => σ (α * t + β)) t 1 =
        α • mfderiv 𝓘(ℝ, ℝ) I σ (α * t + β) 1 := by
    intro σ α β t hσ
    have hcd : ContDiff ℝ ∞ (fun t : ℝ => α * t + β) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    have haff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => α * t + β) t :=
      hcd.contMDiff.mdifferentiableAt (by simp)
    have h := mfderiv_comp_apply (f := fun t : ℝ => α * t + β) (g := σ) t hσ haff 1
    have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => α * t + β) t 1 = α • (1 : ℝ) := by
      rw [mfderiv_eq_fderiv]
      have hd : HasDerivAt (fun t : ℝ => α * t + β) (α * 1) t :=
        ((hasDerivAt_id t).const_mul α).add_const β
      exact (fderiv_apply_one_eq_deriv (f := fun t : ℝ => α * t + β) (x := t)).trans
        (by rw [hd.deriv, smul_eq_mul])
    rw [h1] at h
    exact h.trans (ContinuousLinearMap.map_smul _ _ _)
  have hsmaff : ∀ (σ : ℝ → M) (ρ α β θ : ℝ), ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Ioo (-ρ) ρ) →
      α * θ + β ∈ Ioo (-ρ) ρ → ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun t => σ (α * t + β)) θ := by
    intro σ ρ α β θ hσ hθ
    have hcd : ContDiff ℝ ∞ (fun t : ℝ => α * t + β) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    exact (hσ.contMDiffAt (isOpen_Ioo.mem_nhds hθ)).comp θ hcd.contMDiff.contMDiffAt
  have htrv : ∀ (m : ℕ) (G : M → EuclideanSpace ℝ (Fin m)) (σ γ : ℝ → M) (ρ c : ℝ) (p : M),
      0 < ρ → ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Ioo (-ρ) ρ) →
      γ =ᶠ[𝓝 c] (fun t => σ (ρ * t + -(ρ * c))) → γ c = p →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) G p (mfderiv 𝓘(ℝ, ℝ) I σ 0 1) ≠ 0 →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) G (γ c) (mfderiv 𝓘(ℝ, ℝ) I γ c 1) ≠ 0 := by
    intro m G σ γ ρ c p hρ hσ hev hγc htr
    have hz : ρ * c + -(ρ * c) = 0 := by ring
    have hmd0 : MDifferentiableAt 𝓘(ℝ, ℝ) I σ (ρ * c + -(ρ * c)) := by
      rw [hz]
      exact (hσ.contMDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith only [hρ], hρ⟩)).mdifferentiableAt
        (by simp)
    have hd : mfderiv 𝓘(ℝ, ℝ) I γ c 1 = ρ • mfderiv 𝓘(ℝ, ℝ) I σ 0 1 := by
      rw [hev.mfderiv_eq]
      change mfderiv 𝓘(ℝ, ℝ) I (fun t => σ (ρ * t + -(ρ * c))) c 1 = _
      rw [hmaff σ ρ (-(ρ * c)) c hmd0, mfderiv_congr_point hz]
      rfl
    rw [hd, mfderiv_congr_point hγc]
    exact hlin _ _ _ _ hρ.ne' htr
  clear hlin
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hε := hS.hε
  have hκ := hS.hκ
  have hc₂lo : g q₂ + ε < c₂ := by linarith only [hS.hq₂c₂, hS.hκ]
  have hc₂hi : c₂ < g q₁ - ε := by linarith only [hS.hc₂q₁, hS.hκ]
  have hac₂ : a ≤ c₂ := by linarith only [hS.hac, hS.hcq₂, hS.hq₂c₂, hS.hε, hS.hκ]
  have hc₂b : c₂ ≤ b := by linarith only [hS.hc₂q₁, hS.hq₁b, hS.hε, hS.hκ]
  have hregz : ∀ z, g z = c₂ → mfderiv I 𝓘(ℝ, ℝ) g z ≠ 0 := by
    intro z hz h0
    have hu := D.unit z (by simp [hz, hac₂, hc₂b])
      (fun p hp => hS.hunit z (Or.inr ⟨by linarith only [hz, hc₂lo], by linarith only [hz, hc₂hi]⟩) p hp)
    rw [h0] at hu
    simp at hu
  have hseg : ∀ (d : ℕ) (G : M → EuclideanSpace ℝ (Fin d)) (O : Set M) (p : M) (Z Sph : Set M),
      0 < d → IsOpen O → p ∈ O → ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G O → g p = c₂ →
      p ∈ Sph → (∀ z, g z = c₂ → z ∈ Sph → G z = 0) → IsClosed Z → p ∉ Z →
      (∀ w : EuclideanSpace ℝ (Fin d), ∃ v : TangentSpace I p, mfderiv I 𝓘(ℝ, ℝ) g p v = 0 ∧
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) G p v = w) →
      ∃ σ : ℝ → M, ∃ ρ : ℝ, 0 < ρ ∧ Continuous σ ∧ σ 0 = p ∧ (∀ s, g (σ s) = c₂) ∧
        (∀ s, σ s ∉ Z) ∧ ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Ioo (-ρ) ρ) ∧ InjOn σ (Icc (-ρ) ρ) ∧
        (∀ s ∈ Ioo (-ρ) ρ, mfderiv 𝓘(ℝ, ℝ) I σ s 1 ≠ 0) ∧
        (∀ s ∈ Icc (-ρ) ρ, σ s ∈ Sph ↔ s = 0) ∧
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) G p (mfderiv 𝓘(ℝ, ℝ) I σ 0 1) ≠ 0 := by
    intro d G O p Z Sph hd hO hpO hG hp hpS hmemS hZ hpZ hv
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin d)) := IsBoundedSMul.continuousSMul
    obtain ⟨v', hv'g, hv'G⟩ := hv (EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1)
    clear hv
    replace hv'G : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) G p v' ≠ 0 := by
      rw [hv'G]
      intro h
      have := congrArg (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) h
      simp only [PiLp.norm_single, norm_one] at this
      exact one_ne_zero (this.trans (norm_zero (E := EuclideanSpace ℝ (Fin d))))
    have hcrit : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := hregz p hp
    obtain ⟨ψ, i₀, r, hr, hball, hψ0, hψs, hψis, hψf⟩ := IndexOnePartner.exists_levelChart hf hcrit
    clear hcrit
    have h0src : (0 : Fin n → ℝ) ∈ ψ.source := hball (Metric.mem_ball_self hr)
    have hptgt : p ∈ ψ.target := by rw [← hψ0]; exact ψ.map_source h0src
    have hψmd : ∀ y ∈ ψ.source, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I ψ y := fun y hy =>
      (hψs.contMDiffAt (ψ.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    have hψsmd : ∀ x ∈ ψ.target, MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) ψ.symm x := fun x hx =>
      (hψis.contMDiffAt (ψ.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
    clear hψis
    have hψinj : ∀ y ∈ ψ.source, ∀ w : Fin n → ℝ, mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ y w = 0 → w = 0 := by
      intro y hy w hw
      have hcomp := mfderiv_comp_apply y (hψsmd _ (ψ.map_source hy)) (hψmd y hy) w
      have heq : (ψ.symm ∘ ψ) =ᶠ[𝓝 y] id := by
        filter_upwards [ψ.open_source.mem_nhds hy] with z hz
        exact ψ.left_inv hz
      have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ψ.symm ∘ ψ) y w = w := by
        rw [heq.mfderiv_eq, mfderiv_id]; rfl
      rw [h1, hw, map_zero] at hcomp
      exact hcomp
    set v : Fin n → ℝ := mfderiv I 𝓘(ℝ, Fin n → ℝ) ψ.symm p v' with hvdef
    have hψv : mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ 0 v = v' := by
      have hcomp := mfderiv_comp_apply p (hψmd _ (ψ.map_target hptgt)) (hψsmd p hptgt) v'
      have heq : (ψ ∘ ψ.symm) =ᶠ[𝓝 p] id := by
        filter_upwards [ψ.open_target.mem_nhds hptgt] with z hz
        exact ψ.right_inv hz
      have h1 : mfderiv I I (ψ ∘ ψ.symm) p v' = v' := by
        rw [heq.mfderiv_eq, mfderiv_id]; rfl
      rw [h1] at hcomp
      have h2 : ψ.symm p = 0 := by rw [← hψ0]; exact ψ.left_inv h0src
      rw [hcomp, mfderiv_congr_point h2]
      rfl
    clear hptgt hψsmd
    have hv'0 : v' ≠ 0 := by
      intro h0; apply hv'G; rw [h0]; exact ContinuousLinearMap.map_zero _
    have hv0 : v ≠ 0 := by
      intro h0; apply hv'0
      have h := congrArg (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ 0) h0
      rw [hψv] at h
      rw [h]; exact (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ 0).map_zero
    clear hv'0
    have hvi : v i₀ = 0 := by
      have hgmd : MDifferentiableAt I 𝓘(ℝ, ℝ) g (ψ 0) := hf.mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp_apply (0 : Fin n → ℝ) hgmd (hψmd 0 h0src) v
      have hgψ : (g ∘ ψ) =ᶠ[𝓝 (0 : Fin n → ℝ)] (fun y : Fin n → ℝ => c₂ + y i₀) := by
        filter_upwards [ψ.open_source.mem_nhds h0src] with y hy
        simp only [Function.comp_apply, hψf y hy, hp]
      have hfd : HasFDerivAt (fun y : Fin n → ℝ => c₂ + y i₀)
          (ContinuousLinearMap.proj i₀ : (Fin n → ℝ) →L[ℝ] ℝ) 0 :=
        (hasFDerivAt_apply i₀ (0 : Fin n → ℝ)).const_add c₂
      have h1 : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (g ∘ ψ) 0 v = v i₀ := by
        rw [hgψ.mfderiv_eq]
        change mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun y : Fin n → ℝ => c₂ + y i₀) 0 v = v i₀
        rw [mfderiv_eq_fderiv, hfd.fderiv]
        rfl
      rw [h1, hψv, mfderiv_congr_point hψ0] at hcomp
      rw [hcomp]
      exact hv'g
    clear hv'g
    set σ₀ : ℝ → M := fun s => ψ (s • v) with hσ₀def
    have hsm : ContDiff ℝ ∞ (fun s : ℝ => s • v) := contDiff_id.smul contDiff_const
    have hsmd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s • v) v s := by
      intro s
      simpa using (hasDerivAt_id s).smul_const v
    have hσ₀md : ∀ s : ℝ, s • v ∈ ψ.source → MDifferentiableAt 𝓘(ℝ, ℝ) I σ₀ s := by
      intro s hs
      exact (hψmd _ hs).comp s (hsm.contMDiff.mdifferentiableAt (x := s) (by simp))
    have hσ₀d : ∀ s : ℝ, s • v ∈ ψ.source →
        mfderiv 𝓘(ℝ, ℝ) I σ₀ s 1 = mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (s • v) v := by
      intro s hs
      have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ)) (I'' := I) s
        (f := fun s : ℝ => s • v) (g := ψ) (hψmd _ hs)
        (hsm.contMDiff.mdifferentiableAt (x := s) (by simp)) 1
      have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun s : ℝ => s • v) s 1 = v := by
        rw [mfderiv_eq_fderiv]
        exact (fderiv_apply_one_eq_deriv (f := fun s : ℝ => s • v) (x := s)).trans (hsmd s).deriv
      rw [h1] at hcomp
      exact hcomp
    clear hψmd hsmd
    have hσ₀0 : σ₀ 0 = p := by simp only [hσ₀def, zero_smul, hψ0]
    clear hψ0
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : EuclideanSpace ℝ (Fin d),
        w₀ = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) G p v' := ⟨_, rfl⟩
    have hw₀0 : w₀ ≠ 0 := by rw [hw₀]; exact hv'G
    have hGd : HasDerivAt (fun s : ℝ => G (σ₀ s)) w₀ (0 : ℝ) := by
      have hGmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) G (σ₀ 0) := by
        rw [hσ₀0]
        exact (hG.contMDiffAt (hO.mem_nhds hpO)).mdifferentiableAt (by simp)
      have h0v : (0 : ℝ) • v ∈ ψ.source := by rw [zero_smul]; exact h0src
      have hmd := hGmd.comp (0 : ℝ) (hσ₀md 0 h0v)
      have hdiff : DifferentiableAt ℝ (fun s => G (σ₀ s)) 0 :=
        mdifferentiableAt_iff_differentiableAt.1 hmd
      have hcomp := mfderiv_comp_apply (0 : ℝ) hGmd (hσ₀md 0 h0v) 1
      rw [hσ₀d 0 h0v] at hcomp
      have hval : deriv (fun s => G (σ₀ s)) 0 = w₀ := by
        rw [hw₀]
        rw [← fderiv_apply_one_eq_deriv]
        rw [mfderiv_eq_fderiv] at hcomp
        have hcomp' : fderiv ℝ (G ∘ σ₀) 0 1 = _ := hcomp
        change fderiv ℝ (G ∘ σ₀) 0 1 = _
        rw [hcomp', mfderiv_congr_point hσ₀0, ← hψv]
        congr 2
        rw [zero_smul]
      rw [← hval]
      exact hdiff.hasDerivAt
    clear hG hσ₀md hw₀
    have hσ₀c0 : ContinuousAt σ₀ 0 := by
      have h0v : (0 : ℝ) • v ∈ ψ.source := by rw [zero_smul]; exact h0src
      exact ContinuousAt.comp (f := fun s : ℝ => s • v) (g := ψ) (x := 0) (ψ.continuousAt h0v)
        hsm.continuous.continuousAt
    clear h0src
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), s • v ∈ Metric.ball (0 : Fin n → ℝ) r ∧ σ₀ s ∈ O ∧
        σ₀ s ∉ Z ∧ (s ≠ 0 → G (σ₀ s) ≠ 0) := by
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), s • v ∈ Metric.ball (0 : Fin n → ℝ) r := by
        have hc : ContinuousAt (fun s : ℝ => s • v) 0 := hsm.continuous.continuousAt
        have hm : Metric.ball (0 : Fin n → ℝ) r ∈ 𝓝 ((0 : ℝ) • v) := by
          rw [zero_smul]; exact Metric.ball_mem_nhds _ hr
        exact hc hm
      have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₀ s ∈ O :=
        hσ₀c0 (by rw [hσ₀0]; exact hO.mem_nhds hpO)
      have h3 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₀ s ∉ Z :=
        hσ₀c0 (by rw [hσ₀0]; exact hZ.isOpen_compl.mem_nhds hpZ)
      have h4 : ∀ᶠ s in 𝓝 (0 : ℝ), s ≠ 0 → G (σ₀ s) ≠ 0 := by
        have := hGd.eventually_ne (c := 0) hw₀0
        rw [eventually_nhdsWithin_iff] at this
        filter_upwards [this] with s hs hs0
        exact hs hs0
      filter_upwards [h1, h2, h3, h4] with s a1 a2 a3 a4
      exact ⟨a1, a2, a3, a4⟩
    clear hO hpO hZ hpZ hr hw₀0 hGd hσ₀c0
    obtain ⟨ρ₁, hρ₁, hρ₁P⟩ := Metric.eventually_nhds_iff.1 hev
    clear hev
    set ρ : ℝ := ρ₁ / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    set cl : ℝ → ℝ := fun s => max (-ρ) (min ρ s) with hcldef
    have hclI : ∀ s, cl s ∈ Icc (-ρ) ρ := fun s =>
      ⟨le_max_left _ _, max_le (by linarith only [hρ]) (min_le_left _ _)⟩
    have hclid : ∀ s ∈ Icc (-ρ) ρ, cl s = s := fun s hs => by
      simp only [hcldef, min_eq_right hs.2, max_eq_right hs.1]
    have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
    have hP : ∀ s ∈ Icc (-ρ) ρ, s • v ∈ Metric.ball (0 : Fin n → ℝ) r ∧ σ₀ s ∈ O ∧
        σ₀ s ∉ Z ∧ (s ≠ 0 → G (σ₀ s) ≠ 0) := by
      intro s hs
      apply hρ₁P
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith only [hs.1, hs.2, hρ₁, hρdef]
    clear hρ₁ hρ₁P
    have hsrc : ∀ s ∈ Icc (-ρ) ρ, s • v ∈ ψ.source := fun s hs => hball (hP s hs).1
    clear hball
    have hσ₀cont : ContinuousOn σ₀ (Icc (-ρ) ρ) :=
      ψ.continuousOn.comp hsm.continuous.continuousOn (fun s hs => hsrc s hs)
    have hlevσ : ∀ s, g (σ₀ (cl s)) = c₂ := by
      intro s
      change g (ψ (cl s • v)) = c₂
      rw [hψf _ (hsrc _ (hclI s)), hp]
      simp [hvi]
    clear hp hψf hvi
    refine ⟨fun s => σ₀ (cl s), ρ, hρ, hσ₀cont.comp_continuous hclc hclI, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · change σ₀ (cl 0) = p
      rw [hclid 0 ⟨by linarith only [hρ], by linarith only [hρ]⟩, hσ₀0]
    · exact hlevσ
    · intro s
      exact (hP _ (hclI s)).2.2.1
    · have h1 : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ₀ (Ioo (-ρ) ρ) :=
        hψs.comp hsm.contMDiff.contMDiffOn (fun s hs => hsrc s (Ioo_subset_Icc_self hs))
      exact h1.congr fun s hs => by simp only [hclid s (Ioo_subset_Icc_self hs)]
    · intro s hs s' hs' hss
      simp only [hclid s hs, hclid s' hs'] at hss
      have h1 := ψ.injOn (hsrc s hs) (hsrc s' hs') hss
      exact smul_left_injective ℝ hv0 h1
    · intro s hs
      have heq : (fun s => σ₀ (cl s)) =ᶠ[𝓝 s] σ₀ := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
        rw [hclid u (Ioo_subset_Icc_self hu)]
      rw [heq.mfderiv_eq]
      change mfderiv 𝓘(ℝ, ℝ) I σ₀ s 1 ≠ 0
      rw [hσ₀d s (hsrc s (Ioo_subset_Icc_self hs))]
      intro h0
      exact hv0 (hψinj _ (hsrc s (Ioo_subset_Icc_self hs)) v h0)
    · intro s hs
      constructor
      · intro hmem
        by_contra hs0
        have h1 := hmemS _ (hlevσ s) hmem
        rw [hclid s hs] at h1
        exact (hP s hs).2.2.2 hs0 h1
      · rintro rfl
        change σ₀ (cl 0) ∈ Sph
        rw [hclid 0 ⟨by linarith only [hρ], by linarith only [hρ]⟩, hσ₀0]
        exact hpS
    · have hs0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith only [hρ], hρ⟩
      have heq : (fun s => σ₀ (cl s)) =ᶠ[𝓝 0] σ₀ := by
        filter_upwards [isOpen_Ioo.mem_nhds hs0] with u hu
        rw [hclid u (Ioo_subset_Icc_self hu)]
      have h1 : mfderiv 𝓘(ℝ, ℝ) I (fun s => σ₀ (cl s)) 0 1 = mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ 0 v := by
        rw [heq.mfderiv_eq]
        change mfderiv 𝓘(ℝ, ℝ) I σ₀ 0 1 = _
        rw [hσ₀d 0 (hsrc 0 (Ioo_subset_Icc_self hs0))]
        congr 2
        rw [zero_smul]
      rw [h1, hψv]
      exact hv'G
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 : D.rm x hx ^ 2 ≤ (D.chart x hx).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos x hx).le (D.hrm x hx).2 2
    linarith only [h1, h2, hε]
  have hrm₁ : 2 * ε < D.rm q₁ hq₁ ^ 2 := by linarith only [(hS.hεr q₁ hq₁).2, hε]
  have hrm₂ : 2 * ε < D.rm q₂ hq₂ ^ 2 := by linarith only [(hS.hεr q₂ hq₂).2, hε]
  have hU₁ : ∀ y, g y ∈ Icc c₂ (g q₁ - ε) → ∀ x (hx : x ∈ crit), y ∉ D.smallBall x hx :=
    fun y hy x hx => hS.hunit y (Or.inr ⟨by linarith only [hy.1, hc₂lo], hy.2⟩) x hx
  have hU₂ : ∀ y, g y ∈ Icc (g q₂ + ε) c₂ → ∀ x (hx : x ∈ crit), y ∉ D.smallBall x hx :=
    fun y hy x hx => hS.hunit y (Or.inr ⟨hy.1, by linarith only [hy.2, hc₂hi]⟩) x hx
  obtain ⟨O₁, hO₁, hSO₁, hG₁, hsub₁⟩ := leftCoord_submersion hf D hq₁ hε hrm₁ hac₂ hc₂hi.le hU₁
  obtain ⟨O₂, hO₂, hSO₂, hG₂, hsub₂⟩ := rightCoord_submersion hf D hq₂ hε hrm₂ hc₂lo.le hc₂b hU₂
  have hmemL : ∀ z, g z = c₂ → z ∈ D.leftSphere q₁ hq₁ ε c₂ → D.leftCoord q₁ hq₁ ε z = 0 :=
    fun z hz hmem =>
      ((mem_leftSphere_iff_coord hf D hq₁ hε hrm₁ hac₂ hc₂hi.le hU₁ hz).1 hmem).1
  clear hc₂hi hac₂ hrm₁ hU₁
  have hmemR : ∀ z, g z = c₂ → z ∈ D.rightSphere q₂ hq₂ ε c₂ → D.rightCoord q₂ hq₂ ε z = 0 :=
    fun z hz hmem =>
      ((mem_rightSphere_iff_coord hf D hq₂ hε hrm₂ hc₂lo.le hc₂b hU₂ hz).1 hmem).1
  clear hc₂lo hc₂b hrm₂ hU₂
  set SL := D.leftSphere q₁ hq₁ ε c₂ with hSLdef
  clear hSLdef
  set SR := D.rightSphere q₂ hq₂ ε c₂ with hSRdef
  clear hSRdef
  obtain ⟨SO, hSOdef⟩ : ∃ SO : Set M, SO = ⋃ x ∈ (L.erase q₁ : Set M), ⋃ (hx : x ∈ crit),
      D.leftSphere x hx ε c₂ := ⟨_, rfl⟩
  have hSLc : IsClosed SL := (D.isCompact_leftSphere q₁ hq₁ (hεR _ _) c₂).isClosed
  have hSRc : IsClosed SR := (D.isCompact_rightSphere q₂ hq₂ (hεR _ _) c₂).isClosed
  have hSOc : IsClosed SO := by
    rw [hSOdef]
    refine (L.erase q₁).finite_toSet.isClosed_biUnion fun x _ => ?_
    exact isClosed_iUnion_of_finite fun hx => (D.isCompact_leftSphere x hx (hεR _ _) c₂).isClosed
  clear hεR
  have hmemSO : ∀ z, z ∈ SO ↔ ∃ x, ∃ (hx : x ∈ crit), x ∈ L ∧ x ≠ q₁ ∧
      z ∈ D.leftSphere x hx ε c₂ := by
    intro z
    rw [hSOdef]
    simp only [mem_iUnion, Finset.coe_erase, Set.mem_sdiff, mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨x, ⟨hxL, hne⟩, hx, hz⟩
      exact ⟨x, hx, hxL, hne, hz⟩
    · rintro ⟨x, hx, hxL, hne, hz⟩
      exact ⟨x, ⟨hxL, hne⟩, hx, hz⟩
  clear hSOdef
  have hδSO : ∀ t ∈ Icc (0 : ℝ) 1, δ t ∉ SO := by
    intro t ht hmem
    obtain ⟨x, hx, hxL, hne, hz⟩ := (hmemSO _).1 hmem
    exact hδL x hx hxL hne t ht hz
  clear hδL
  set p₀ := δ 0 with hp₀def
  clear hp₀def
  set p₁ := δ 1 with hp₁def
  clear hp₁def
  have hp₀SR : p₀ ∉ SR := fun h => Set.disjoint_left.1 hS.hdisj hδ0 h
  have hp₁SL : p₁ ∉ SL := fun h => Set.disjoint_left.1 hS.hdisj h hδ1
  have hp₀SO : p₀ ∉ SO := hδSO 0 ⟨le_rfl, zero_le_one⟩
  have hp₁SO : p₁ ∉ SO := hδSO 1 ⟨zero_le_one, le_rfl⟩
  clear hδSO
  have hp01 : p₀ ≠ p₁ := fun h => hp₁SL (h ▸ hδ0)
  obtain ⟨W₁, W₂, hW₁, hW₂, hpW₁, hpW₂, hW12⟩ := t2_separation hp01
  clear hp01
  have hk₁ := hS.hk₁
  have hk₂ := hS.hk₂
  have hℓn := hS.hℓn
  have hℓ2 := hS.hℓ
  obtain ⟨σ₁, ρ₁, hρ₁, hσ₁c, hσ₁0, hσ₁lev, hσ₁Z, hσ₁sm, hσ₁inj, hσ₁imm, hσ₁SL, hσ₁tr⟩ :=
    hseg _ (D.leftCoord q₁ hq₁ ε) O₁ p₀ (SR ∪ SO ∪ W₁ᶜ) SL (by omega) hO₁ (hSO₁ hδ0) hG₁ (hδlev 0)
      hδ0 hmemL ((hSRc.union hSOc).union hW₁.isClosed_compl)
      (by simp only [mem_union, mem_compl_iff, not_or, not_not]; exact ⟨⟨hp₀SR, hp₀SO⟩, hpW₁⟩)
      (hsub₁ p₀ hδ0).2
  clear hδ0 hO₁ hSO₁ hG₁ hsub₁ hmemL hp₀SR hp₀SO hW₁ hpW₁
  obtain ⟨σ₂, ρ₂, hρ₂, hσ₂c, hσ₂0, hσ₂lev, hσ₂Z, hσ₂sm, hσ₂inj, hσ₂imm, hσ₂SR, hσ₂tr⟩ :=
    hseg _ (D.rightCoord q₂ hq₂ ε) O₂ p₁ (SL ∪ SO ∪ W₂ᶜ) SR (by omega) hO₂ (hSO₂ hδ1) hG₂ (hδlev 1)
      hδ1 hmemR ((hSLc.union hSOc).union hW₂.isClosed_compl)
      (by simp only [mem_union, mem_compl_iff, not_or, not_not]; exact ⟨⟨hp₁SL, hp₁SO⟩, hpW₂⟩)
      (hsub₂ p₁ hδ1).2
  clear hδ1 hseg hO₂ hSO₂ hG₂ hsub₂ hmemR hp₁SL hp₁SO hW₂ hpW₂
  have hσ₁SR : ∀ s, σ₁ s ∉ SR := fun s h => hσ₁Z s (Or.inl (Or.inl h))
  have hσ₁SO : ∀ s, σ₁ s ∉ SO := fun s h => hσ₁Z s (Or.inl (Or.inr h))
  have hσ₁W : ∀ s, σ₁ s ∈ W₁ := fun s => by
    by_contra h; exact hσ₁Z s (Or.inr h)
  clear hσ₁Z
  have hσ₂SL : ∀ s, σ₂ s ∉ SL := fun s h => hσ₂Z s (Or.inl (Or.inl h))
  have hσ₂SO : ∀ s, σ₂ s ∉ SO := fun s h => hσ₂Z s (Or.inl (Or.inr h))
  have hσ₂W : ∀ s, σ₂ s ∈ W₂ := fun s => by
    by_contra h; exact hσ₂Z s (Or.inr h)
  clear hσ₂Z
  have hnotSU : ∀ z, z ∉ SL → z ∉ SR → z ∉ SO → z ∉ D.sphereUnion (insert q₁ L) {q₂} ε c₂ := by
    intro z h1 h2 h3 hmem
    simp only [sphereUnion, mem_union, mem_iUnion, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with ⟨x, hx, hxL, hz⟩ | ⟨p, hp, hpq, hz⟩
    · by_cases hxq : x = q₁
      · subst hxq; exact h1 hz
      · rcases hxL with hxL | hxL
        · exact hxq hxL
        · exact h3 ((hmemSO z).2 ⟨x, hx, hxL, hxq, hz⟩)
    · subst hpq; exact h2 hz
  have hSUnot : ∀ z, z ∉ D.sphereUnion (insert q₁ L) {q₂} ε c₂ → z ∉ SL ∧ z ∉ SR ∧ z ∉ SO := by
    intro z hz
    refine ⟨fun h => hz ?_, fun h => hz ?_, fun h => hz ?_⟩
    · exact Or.inl (mem_iUnion.2 ⟨q₁, mem_iUnion.2 ⟨hq₁, mem_iUnion.2
        ⟨Finset.mem_insert_self _ _, h⟩⟩⟩)
    · exact Or.inr (mem_iUnion.2 ⟨q₂, mem_iUnion.2 ⟨hq₂, mem_iUnion.2
        ⟨Finset.mem_singleton_self _, h⟩⟩⟩)
    · obtain ⟨x, hx, hxL, -, hzx⟩ := (hmemSO z).1 h
      exact Or.inl (mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hx, mem_iUnion.2
        ⟨Finset.mem_insert_of_mem hxL, hzx⟩⟩⟩)
  have hρ₁3 : ρ₁ / 3 ∈ Icc (-ρ₁) ρ₁ := ⟨by linarith only [hρ₁], by linarith only [hρ₁]⟩
  have hρ₂3 : -(ρ₂ / 3) ∈ Icc (-ρ₂) ρ₂ := ⟨by linarith only [hρ₂], by linarith only [hρ₂]⟩
  have ha₁ : σ₁ (ρ₁ / 3) ∉ D.sphereUnion (insert q₁ L) {q₂} ε c₂ := by
    refine hnotSU _ (fun h => ?_) (hσ₁SR _) (hσ₁SO _)
    have := (hσ₁SL _ hρ₁3).1 h
    linarith only [this, hρ₁]
  clear hρ₁3
  have hb₂ : σ₂ (-(ρ₂ / 3)) ∉ D.sphereUnion (insert q₁ L) {q₂} ε c₂ := by
    refine hnotSU _ (hσ₂SL _) (fun h => ?_) (hσ₂SO _)
    have := (hσ₂SR _ hρ₂3).1 h
    linarith only [this, hρ₂]
  clear hnotSU hρ₂3
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ → M, β = fun u => if u ≤ 1 / 3 then σ₁ (ρ₁ / 3 * (1 - 3 * u))
      else if u ≤ 2 / 3 then δ (3 * u - 1) else σ₂ (-(ρ₂ / 3) * (3 * u - 2)) := ⟨_, rfl⟩
  have hβc : Continuous β := by
    rw [hβdef]
    refine Continuous.if_le (hσ₁c.comp (by fun_prop))
      (Continuous.if_le (hδ.comp (by fun_prop)) (hσ₂c.comp (by fun_prop)) continuous_id
        continuous_const ?_) continuous_id continuous_const ?_
    · intro u hu
      subst hu
      norm_num
      rw [hσ₂0]
    · intro u hu
      subst hu
      norm_num
      rw [hσ₁0]
  clear hδ
  have hβlev : ∀ u, g (β u) = c₂ := by
    intro u
    rw [hβdef]
    dsimp only
    split_ifs
    · exact hσ₁lev _
    · exact hδlev _
    · exact hσ₂lev _
  clear hδlev
  have hβ0 : β 0 = σ₁ (ρ₁ / 3) := by rw [hβdef]; norm_num
  have hβ1 : β 1 = σ₂ (-(ρ₂ / 3)) := by rw [hβdef]; norm_num
  clear hβdef
  obtain ⟨Hm, hHc, -, hHA, hHmaps, hHavoid⟩ := D.exists_level_pushOff hf hε hS.hεr hκ (c := c₂)
    ⟨by linarith only [hS.hac, hS.hcq₂, hS.hq₂c₂, hε], by linarith only [hS.hc₂q₁, hS.hq₁b, hε]⟩
    (fun y hy => hS.hunit y (Or.inr ⟨by linarith only [hy.1, hS.hq₂c₂], by linarith only [hy.2, hS.hc₂q₁]⟩))
    (insert q₁ L) {q₂} (m := 1)
    (by
      intro q hq hqL
      rcases Finset.mem_insert.1 hqL with hqq | hqL
      · subst hqq
        refine ⟨hS.hc₂q₁, ?_⟩
        change (D.chart q hq₁).k + 1 < n
        omega
      · obtain ⟨-, h1, h2⟩ := hL q hqL
        have hk := (D.chart q hq).hkidx
        exact ⟨h1, by omega⟩)
    (by
      intro p hp hpR
      rw [Finset.mem_singleton] at hpR
      subst hpR
      refine ⟨hS.hq₂c₂, ?_⟩
      change n - (D.chart p hq₂).k + 1 < n
      omega)
    isOpen_univ (F := fun y => β (y 0)) (hβc.comp (continuous_apply 0)).continuousOn
    (fun y _ => ⟨hβlev (y 0), Set.mem_univ _⟩)
    (A := {y | y 0 = 0 ∨ y 0 = 1})
    ((isClosed_eq (continuous_apply 0) continuous_const).union
      (isClosed_eq (continuous_apply 0) continuous_const))
    (by
      rintro y ⟨hyA, -⟩
      rcases hyA with h0 | h1
      · show β (y 0) ∉ _
        rw [h0, hβ0]; exact ha₁
      · show β (y 0) ∉ _
        rw [h1, hβ1]; exact hb₂)
  clear hL ha₁ hb₂ hβc hβlev
  let e : ℝ → (Fin 1 → ℝ) := fun t _ => max 0 (min 1 t)
  have he : ∀ t, e t ∈ Icc (0 : Fin 1 → ℝ) 1 :=
    fun t => ⟨fun _ => le_max_left _ _, fun _ => max_le zero_le_one (min_le_left _ _)⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ → M, μ = fun t => Hm 1 (e t) := ⟨_, rfl⟩
  have hμc : Continuous μ := by
    rw [hμdef]
    exact hHc.comp_continuous (continuous_const.prodMk (continuous_pi fun _ =>
      continuous_const.max (continuous_const.min continuous_id)))
      (fun t => ⟨⟨zero_le_one, le_rfl⟩, he t⟩)
  clear hHc
  have hμlev : ∀ t, g (μ t) = c₂ := fun t => by
    rw [hμdef]; exact (hHmaps 1 ⟨zero_le_one, le_rfl⟩ (he t)).1
  clear hHmaps
  have hμ0 : μ 0 = σ₁ (ρ₁ / 3) := by
    have h := hHA 1 (e 0) (Or.inl (by simp [e]))
    rw [hμdef]
    simp only [h]
    rw [show e 0 0 = 0 by simp [e], hβ0]
  clear hβ0
  have hμ1 : μ 1 = σ₂ (-(ρ₂ / 3)) := by
    have h := hHA 1 (e 1) (Or.inr (by simp [e]))
    rw [hμdef]
    simp only [h]
    rw [show e 1 0 = 1 by simp [e], hβ1]
  clear hβ1 hHA
  have hμav : ∀ t, μ t ∉ SL ∧ μ t ∉ SR ∧ μ t ∉ SO := fun t => by
    rw [hμdef]; exact hSUnot _ (hHavoid (e t) (he t))
  clear hSUnot hHavoid hμdef
  obtain ⟨arc, harcdef⟩ : ∃ arc : ℝ → M, arc = fun t => if t ≤ 4 / 3 then σ₁ (ρ₁ * (t - 1))
      else if t ≤ 5 / 3 then μ (3 * (t - 4 / 3)) else σ₂ (ρ₂ * (t - 2)) := ⟨_, rfl⟩
  have harcc : Continuous arc := by
    rw [harcdef]
    refine Continuous.if_le (hσ₁c.comp (by fun_prop))
      (Continuous.if_le (hμc.comp (by fun_prop)) (hσ₂c.comp (by fun_prop)) continuous_id
        continuous_const ?_) continuous_id continuous_const ?_
    · intro u hu
      subst hu
      norm_num
      rw [hμ1]
      congr 1
      ring
    · intro u hu
      subst hu
      norm_num
      rw [hμ0]
      congr 1
      ring
  clear hσ₁c hσ₂c hμc hμ0 hμ1
  have harc1 : ∀ t, t ≤ 4 / 3 → arc t = σ₁ (ρ₁ * (t - 1)) := fun t ht => by
    rw [harcdef]; simp only [ite_eq_left ht]
  have harc2 : ∀ t, 5 / 3 < t → arc t = σ₂ (ρ₂ * (t - 2)) := fun t ht => by
    rw [harcdef]; simp only [ite_eq_right (by linarith only [ht] : ¬ t ≤ 4 / 3), ite_eq_right (not_le.2 ht)]
  have harcm : ∀ t, 4 / 3 < t → t ≤ 5 / 3 → arc t = μ (3 * (t - 4 / 3)) := fun t ht ht' => by
    rw [harcdef]; simp only [ite_eq_right (not_le.2 ht), ite_eq_left ht']
  have harclev : ∀ t, g (arc t) = c₂ := by
    intro t
    rw [harcdef]
    dsimp only
    split_ifs
    · exact hσ₁lev _
    · exact hμlev _
    · exact hσ₂lev _
  clear hσ₁lev hσ₂lev hμlev harcdef
  have harcK : ∀ t ∈ Icc (0 : ℝ) 3, (arc t ∈ SL ↔ t = 1) ∧ (arc t ∈ SR ↔ t = 2) ∧ arc t ∉ SO := by
    intro t ht
    by_cases h1 : t ≤ 4 / 3
    · rw [harc1 t h1]
      have hs : ρ₁ * (t - 1) ∈ Icc (-ρ₁) ρ₁ := harI1 ρ₁ t hρ₁ ht.1 h1
      refine ⟨?_, ⟨fun h => absurd h (hσ₁SR _), fun h => by linarith only [h, h1]⟩, hσ₁SO _⟩
      rw [hσ₁SL _ hs, mul_eq_zero, sub_eq_zero]
      exact ⟨fun h => h.resolve_left hρ₁.ne', Or.inr⟩
    · by_cases h2 : t ≤ 5 / 3
      · rw [harcm t (not_le.1 h1) h2]
        obtain ⟨a1, a2, a3⟩ := hμav (3 * (t - 4 / 3))
        refine ⟨⟨fun h => absurd h a1, fun h => by linarith only [h, h1]⟩,
          ⟨fun h => absurd h a2, fun h => by linarith only [h, h2]⟩, a3⟩
      · rw [harc2 t (not_le.1 h2)]
        have hs : ρ₂ * (t - 2) ∈ Icc (-ρ₂) ρ₂ := harI2 ρ₂ t hρ₂ (not_le.1 h2) ht.2
        refine ⟨⟨fun h => absurd h (hσ₂SL _), fun h => by linarith only [h, h2]⟩, ?_, hσ₂SO _⟩
        rw [hσ₂SR _ hs, mul_eq_zero, sub_eq_zero]
        exact ⟨fun h => h.resolve_left hρ₂.ne', Or.inr⟩
  clear harI1 harI2 hσ₁SL hσ₂SR hσ₁SR hσ₁SO hσ₂SL hσ₂SO hμav harcm
  obtain ⟨base, hbasedef⟩ : ∃ base : ℝ → M, base = fun t => if t ≤ 3 then arc t
      else arc (3 * (4 - t)) := ⟨_, rfl⟩
  have hbasec : Continuous base := by
    rw [hbasedef]
    refine Continuous.if_le harcc (harcc.comp (by fun_prop)) continuous_id continuous_const ?_
    intro u hu
    subst hu
    norm_num
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ → M, lam = fun θ => base (4 * Int.fract θ) := ⟨_, rfl⟩
  have hlamc : Continuous lam := by
    rw [hlamdef]
    exact ContinuousOn.comp_fract'' (f := fun u => base (4 * u))
      (hbasec.comp (by fun_prop)).continuousOn (by simp only [hbasedef]; norm_num)
  clear hbasec
  have hlamper : Function.Periodic lam 1 := by
    intro θ
    rw [hlamdef]
    simp only [Int.fract_add_one]
  have hlamlev : ∀ θ, g (lam θ) = c₂ := by
    intro θ
    rw [hlamdef, hbasedef]
    dsimp only
    split_ifs
    · exact harclev _
    · exact harclev _
  clear harclev
  have hlamt : ∀ t ∈ Icc (0 : ℝ) 3, lam (t / 4) = arc t := by
    intro t ht
    rw [hlamdef, hbasedef]
    dsimp only
    rw [Int.fract_eq_self.2 ⟨by linarith only [ht.1], by linarith only [ht.2]⟩,
      show 4 * (t / 4) = t by ring, ite_eq_left ht.2]
  have hloc1 : ∀ (θ : ℝ) (k : ℤ), |θ - 1 / 4 - k| < 1 / 16 →
      lam θ = σ₁ (ρ₁ * (4 * (θ - k) - 1)) := by
    intro θ k hk
    rw [abs_lt] at hk
    have hfr : Int.fract θ = θ - k :=
      Int.fract_eq_iff.2 ⟨by linarith only [hk.1], by linarith only [hk.2], k, by ring⟩
    rw [hlamdef, hbasedef]
    dsimp only
    rw [hfr, ite_eq_left (by linarith only [hk.2]), harc1 _ (by linarith only [hk.2])]
  have hloc2 : ∀ (θ : ℝ) (k : ℤ), |θ - 1 / 2 - k| < 1 / 16 →
      lam θ = σ₂ (ρ₂ * (4 * (θ - k) - 2)) := by
    intro θ k hk
    rw [abs_lt] at hk
    have hfr : Int.fract θ = θ - k :=
      Int.fract_eq_iff.2 ⟨by linarith only [hk.1], by linarith only [hk.2], k, by ring⟩
    rw [hlamdef, hbasedef]
    dsimp only
    rw [hfr, ite_eq_left (by linarith only [hk.2]), harc2 _ (by linarith only [hk.1])]
  clear hbasedef hlamdef
  have hUa : IsOpen (Uo (1 / 4) (1 / 16) ∪ Uo (1 / 2) (1 / 16)) := (hUop _ _).union (hUop _ _)
  have hPa : IsClosed (Pc (1 / 4) (1 / 32) ∪ Pc (1 / 2) (1 / 32)) := (hPcl _ _).union (hPcl _ _)
  have hUaper : ∀ t, t ∈ (Uo (1 / 4) (1 / 16) ∪ Uo (1 / 2) (1 / 16)) ↔ t + 1 ∈ (Uo (1 / 4) (1 / 16) ∪ Uo (1 / 2) (1 / 16)) := fun t => by
    simp only [mem_union, ← hUper]
  have hPaper : ∀ t, t ∈ (Pc (1 / 4) (1 / 32) ∪ Pc (1 / 2) (1 / 32)) ↔ t + 1 ∈ (Pc (1 / 4) (1 / 32) ∪ Pc (1 / 2) (1 / 32)) := fun t => by
    simp only [mem_union, ← hPper]
  have hPaUa : (Pc (1 / 4) (1 / 32) ∪ Pc (1 / 2) (1 / 32)) ⊆ (Uo (1 / 4) (1 / 16) ∪ Uo (1 / 2) (1 / 16)) := by
    rintro θ (h | h)
    · obtain ⟨k, hk⟩ := (hmemP _ _ θ hw32.1 hw32.2).1 h
      exact Or.inl ((hmemU _ _ θ hw16.1 hw16.2).2 ⟨k, hk.trans_lt h3216⟩)
    · obtain ⟨k, hk⟩ := (hmemP _ _ θ hw32.1 hw32.2).1 h
      exact Or.inr ((hmemU _ _ θ hw16.1 hw16.2).2 ⟨k, hk.trans_lt h3216⟩)
  have heq1 : ∀ (θ : ℝ) (k : ℤ) (w : ℝ), w ≤ 1 / 16 → |θ - 1 / 4 - k| < w →
      lam =ᶠ[𝓝 θ] (fun θ' => σ₁ ((4 * ρ₁) * θ' + (-(4 * ρ₁ * k) - ρ₁))) := by
    intro θ k w hw hk
    have hN : {θ' : ℝ | |θ' - 1 / 4 - k| < w} ∈ 𝓝 θ :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds hk
    filter_upwards [hN] with θ' h'
    rw [hloc1 θ' k (lt_of_lt_of_le h' hw)]
    congr 1
    ring
  clear hloc1
  have heq2 : ∀ (θ : ℝ) (k : ℤ) (w : ℝ), w ≤ 1 / 16 → |θ - 1 / 2 - k| < w →
      lam =ᶠ[𝓝 θ] (fun θ' => σ₂ ((4 * ρ₂) * θ' + (-(4 * ρ₂ * k) - 2 * ρ₂))) := by
    intro θ k w hw hk
    have hN : {θ' : ℝ | |θ' - 1 / 2 - k| < w} ∈ 𝓝 θ :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds hk
    filter_upwards [hN] with θ' h'
    rw [hloc2 θ' k (lt_of_lt_of_le h' hw)]
    congr 1
    ring
  clear hloc2
  have hin1 : ∀ (θ : ℝ) (k : ℤ), |θ - 1 / 4 - k| < 1 / 16 →
      (4 * ρ₁) * θ + (-(4 * ρ₁ * k) - ρ₁) ∈ Ioo (-ρ₁) ρ₁ := by
    intro θ k hk
    have h := harg ρ₁ (θ - 1 / 4 - k) hρ₁ (hk.trans h164)
    rwa [show ρ₁ * (4 * (θ - 1 / 4 - k)) = (4 * ρ₁) * θ + (-(4 * ρ₁ * k) - ρ₁) by ring] at h
  have hin2 : ∀ (θ : ℝ) (k : ℤ), |θ - 1 / 2 - k| < 1 / 16 →
      (4 * ρ₂) * θ + (-(4 * ρ₂ * k) - 2 * ρ₂) ∈ Ioo (-ρ₂) ρ₂ := by
    intro θ k hk
    have h := harg ρ₂ (θ - 1 / 2 - k) hρ₂ (hk.trans h164)
    rwa [show ρ₂ * (4 * (θ - 1 / 2 - k)) = (4 * ρ₂) * θ + (-(4 * ρ₂ * k) - 2 * ρ₂) by ring] at h
  clear harg h164
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ lam (Uo (1 / 4) (1 / 16) ∪ Uo (1 / 2) (1 / 16)) := by
    intro θ hθ
    rcases hθ with hθ | hθ
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw16.1 hw16.2).1 hθ
      exact ((hsmaff σ₁ ρ₁ _ _ θ hσ₁sm (hin1 θ k hk)).congr_of_eventuallyEq
        (heq1 θ k _ le_rfl hk)).contMDiffWithinAt
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw16.1 hw16.2).1 hθ
      exact ((hsmaff σ₂ ρ₂ _ _ θ hσ₂sm (hin2 θ k hk)).congr_of_eventuallyEq
        (heq2 θ k _ le_rfl hk)).contMDiffWithinAt
  clear hw16 hsmaff
  have hcU : ∀ x (hx : x ∈ crit), ∀ y ∈ D.closedSmallBall x hx, g y ≠ c₂ := by
    intro x hx y hy hyc
    obtain ⟨w, hw, rfl⟩ := hy
    have h1 := hS.hεr x hx
    have hr₀ := (D.chart x hx).hr₀
    have hrm := D.rm_pos x hx
    have hlt : (D.chart x hx).r₀ < D.rm x hx :=
      lt_of_pow_lt_pow_left₀ 2 hrm.le (by linarith only [h1.1, h1.2, hε])
    exact hS.hmodel x hx _ ⟨w, lt_of_le_of_lt hw hlt, rfl⟩ ⟨by linarith only [hyc, hκ], by linarith only [hyc, hκ]⟩
  have hcab : c₂ ∈ Ioo a b := ⟨by linarith only [hS.hac, hS.hcq₂, hS.hq₂c₂, hε, hκ], by linarith only [hS.hc₂q₁, hS.hq₁b, hε, hκ]⟩
  clear hε hκ
  have hKc : IsClosed (SL ∪ SR ∪ SO) := (hSLc.union hSRc).union hSOc
  clear hSLc hSRc hSOc
  have harcJ : ∀ t ∈ J, arc t ∉ (SL ∪ SR ∪ SO) := by
    intro t ht hmem
    obtain ⟨htI, h1, h2⟩ := hJsub t ht
    obtain ⟨a1, a2, a3⟩ := harcK t htI
    rcases hmem with (h | h) | h
    · exact h1 (a1.1 h)
    · exact h2 (a2.1 h)
    · exact a3 h
  have hOopen : ∀ φ : ℝ → M, Continuous φ →
      IsOpen (((SL ∪ SR ∪ SO)ᶜ ×ˢ (SL ∪ SR ∪ SO)ᶜ) ∪ ((φ '' J)ᶜ ×ˢ (univ : Set M))) := fun φ hφ =>
    (hKc.isOpen_compl.prod hKc.isOpen_compl).union
      ((hJc.image hφ).isClosed.isOpen_compl.prod isOpen_univ)
  clear hJc hKc
  have hOdiag : ∀ φ : ℝ → M, (∀ t ∈ J, φ t ∉ (SL ∪ SR ∪ SO)) →
      ∀ x, (x, x) ∈ ((SL ∪ SR ∪ SO)ᶜ ×ˢ (SL ∪ SR ∪ SO)ᶜ) ∪ ((φ '' J)ᶜ ×ˢ (univ : Set M)) := by
    intro φ hφ x
    by_cases hx : x ∈ (SL ∪ SR ∪ SO)
    · refine Or.inr ⟨?_, mem_univ _⟩
      rintro ⟨t, ht, rfl⟩
      exact hφ t ht hx
    · exact Or.inl ⟨hx, hx⟩
  have hOuse : ∀ (φ : ℝ → M) (t : ℝ) (x : M), t ∈ J →
      (φ t, x) ∈ ((SL ∪ SR ∪ SO)ᶜ ×ˢ (SL ∪ SR ∪ SO)ᶜ) ∪ ((φ '' J)ᶜ ×ˢ (univ : Set M)) → x ∉ (SL ∪ SR ∪ SO) := by
    intro φ t x ht h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd ⟨t, ht, rfl⟩ h
  obtain ⟨γ₁, hγ₁sm, hγ₁per, hγ₁lev, hγ₁P, hγ₁O⟩ := IndexOnePartner.exists_smooth_level_loop hg D
    hcab hcU hlamc hlamper hlamlev hUa hUaper hsm hPa hPaper hPaUa (hOopen arc harcc)
    (hOdiag arc harcJ)
  clear harcc hlamc hlamper hlamlev hUa hPa hUaper hPaper hPaUa hsm hcU hcab harcJ
  have hγ₁J : ∀ t ∈ J, γ₁ (t / 4) ∉ (SL ∪ SR ∪ SO) := by
    intro t ht
    have h := hγ₁O (t / 4)
    rw [hlamt t (hJsub t ht).1] at h
    exact hOuse arc t _ ht h
  clear hγ₁O
  have hUb : IsOpen (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) := (hUop _ _).union (hUop _ _)
  clear hUop
  have hPb : IsClosed (Pc (1 / 4) (1 / 64) ∪ Pc (1 / 2) (1 / 64)) := (hPcl _ _).union (hPcl _ _)
  clear hPcl
  have hPbUb : (Pc (1 / 4) (1 / 64) ∪ Pc (1 / 2) (1 / 64)) ⊆ (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) := by
    rintro θ (h | h)
    · obtain ⟨k, hk⟩ := (hmemP _ _ θ hw64.1 hw64.2).1 h
      exact Or.inl ((hmemU _ _ θ hw32.1 hw32.2).2 ⟨k, hk.trans_lt h6432⟩)
    · obtain ⟨k, hk⟩ := (hmemP _ _ θ hw64.1 hw64.2).1 h
      exact Or.inr ((hmemU _ _ θ hw32.1 hw32.2).2 ⟨k, hk.trans_lt h6432⟩)
  have hγ₁lam : ∀ θ : ℝ, (∃ k : ℤ, |θ - 1 / 4 - k| < 1 / 32) ∨ (∃ k : ℤ, |θ - 1 / 2 - k| < 1 / 32) →
      γ₁ =ᶠ[𝓝 θ] lam := by
    intro θ hθ
    rcases hθ with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hN : {θ' : ℝ | |θ' - 1 / 4 - k| < 1 / 32} ∈ 𝓝 θ :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds hk
      filter_upwards [hN] with θ' h'
      exact hγ₁P θ' (Or.inl ((hmemP _ _ θ' hw32.1 hw32.2).2 ⟨k, h'.le⟩))
    · have hN : {θ' : ℝ | |θ' - 1 / 2 - k| < 1 / 32} ∈ 𝓝 θ :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds hk
      filter_upwards [hN] with θ' h'
      exact hγ₁P θ' (Or.inr ((hmemP _ _ θ' hw32.1 hw32.2).2 ⟨k, h'.le⟩))
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ → ℝ → M, hh = fun θ _ => γ₁ θ := ⟨_, rfl⟩
  have hhsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry hh) := by
    rw [hhdef]; exact hγ₁sm.comp (contDiff_fst.contMDiff)
  have hhper : ∀ θ s, hh (θ + 1) s = hh θ s := fun θ s => by rw [hhdef]; exact hγ₁per θ
  clear hγ₁per
  have hhlev : ∀ θ s, g (hh θ s) = c₂ := fun θ s => by rw [hhdef]; exact hγ₁lev θ
  clear hγ₁lev
  have himm : ∀ z ∈ (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) ×ˢ (univ : Set ℝ), mfderiv 𝓘(ℝ, ℝ) I (fun θ => hh θ z.2) z.1 1 ≠ 0 := by
    rintro ⟨θ, s⟩ ⟨hθ, -⟩
    have hfun : (fun θ' => hh θ' s) = γ₁ := by rw [hhdef]
    rw [hfun]
    rcases hθ with hθ | hθ
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw32.1 hw32.2).1 hθ
      have hk' : |θ - 1 / 4 - k| < 1 / 16 := hk.trans h3216
      have heq : γ₁ =ᶠ[𝓝 θ] (fun θ' => σ₁ ((4 * ρ₁) * θ' + (-(4 * ρ₁ * k) - ρ₁))) :=
        (hγ₁lam θ (Or.inl ⟨k, hk⟩)).trans (heq1 θ k _ le_rfl hk')
      rw [heq.mfderiv_eq]
      change mfderiv 𝓘(ℝ, ℝ) I (fun θ' => σ₁ ((4 * ρ₁) * θ' + (-(4 * ρ₁ * k) - ρ₁))) θ 1 ≠ 0
      rw [hmaff σ₁ _ _ θ ((hσ₁sm.contMDiffAt (isOpen_Ioo.mem_nhds (hin1 θ k hk'))).mdifferentiableAt
        (by simp))]
      exact smul_ne_zero (by positivity) (hσ₁imm _ (hin1 θ k hk'))
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw32.1 hw32.2).1 hθ
      have hk' : |θ - 1 / 2 - k| < 1 / 16 := hk.trans h3216
      have heq : γ₁ =ᶠ[𝓝 θ] (fun θ' => σ₂ ((4 * ρ₂) * θ' + (-(4 * ρ₂ * k) - 2 * ρ₂))) :=
        (hγ₁lam θ (Or.inr ⟨k, hk⟩)).trans (heq2 θ k _ le_rfl hk')
      rw [heq.mfderiv_eq]
      change mfderiv 𝓘(ℝ, ℝ) I (fun θ' => σ₂ ((4 * ρ₂) * θ' + (-(4 * ρ₂ * k) - 2 * ρ₂))) θ 1 ≠ 0
      rw [hmaff σ₂ _ _ θ ((hσ₂sm.contMDiffAt (isOpen_Ioo.mem_nhds (hin2 θ k hk'))).mdifferentiableAt
        (by simp))]
      exact smul_ne_zero (by positivity) (hσ₂imm _ (hin2 θ k hk'))
  clear hσ₁imm hσ₂imm
  have hUbval : ∀ θ ∈ (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)), (∃ k : ℤ, (4 * ρ₁) * θ + (-(4 * ρ₁ * k) - ρ₁) ∈ Ioo (-ρ₁) ρ₁ ∧
        γ₁ θ = σ₁ ((4 * ρ₁) * θ + (-(4 * ρ₁ * k) - ρ₁))) ∨
      (∃ k : ℤ, (4 * ρ₂) * θ + (-(4 * ρ₂ * k) - 2 * ρ₂) ∈ Ioo (-ρ₂) ρ₂ ∧
        γ₁ θ = σ₂ ((4 * ρ₂) * θ + (-(4 * ρ₂ * k) - 2 * ρ₂))) := by
    intro θ hθ
    rcases hθ with hθ | hθ
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw32.1 hw32.2).1 hθ
      have hk' : |θ - 1 / 4 - k| < 1 / 16 := hk.trans h3216
      exact Or.inl ⟨k, hin1 θ k hk', ((hγ₁lam θ (Or.inl ⟨k, hk⟩)).trans
        (heq1 θ k _ le_rfl hk')).self_of_nhds⟩
    · obtain ⟨k, hk⟩ := (hmemU _ _ θ hw32.1 hw32.2).1 hθ
      have hk' : |θ - 1 / 2 - k| < 1 / 16 := hk.trans h3216
      exact Or.inr ⟨k, hin2 θ k hk', ((hγ₁lam θ (Or.inr ⟨k, hk⟩)).trans
        (heq2 θ k _ le_rfl hk')).self_of_nhds⟩
  clear h3216 hmemU heq1 heq2 hin1 hin2 hγ₁lam
  have hshift : ∀ (ρ θ θ' β : ℝ) (k k' : ℤ), 0 < ρ →
      (4 * ρ) * θ + (-(4 * ρ * k) - β) = (4 * ρ) * θ' + (-(4 * ρ * k') - β) →
      ∃ j : ℤ, θ' = θ + j := by
    intro ρ θ θ' β k k' hρ h
    refine ⟨k' - k, ?_⟩
    have h4 : (4 * ρ) * (θ' - θ - (k' - k)) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (by positivity)
    · push_cast; linarith only [h5]
  have hinj : ∀ θ θ' s, (θ, s) ∈ (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) ×ˢ (univ : Set ℝ) → (θ', s) ∈ (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) ×ˢ (univ : Set ℝ) →
      hh θ s = hh θ' s → ∃ k : ℤ, θ' = θ + k := by
    rintro θ θ' s ⟨hθ, -⟩ ⟨hθ', -⟩ heq
    have heq' : γ₁ θ = γ₁ θ' := by rw [hhdef] at heq; exact heq
    rcases hUbval θ hθ with ⟨k, hkI, hk⟩ | ⟨k, hkI, hk⟩ <;>
      rcases hUbval θ' hθ' with ⟨k', hkI', hk'⟩ | ⟨k', hkI', hk'⟩ <;> rw [hk, hk'] at heq'
    · exact hshift ρ₁ θ θ' ρ₁ k k' hρ₁
        (hσ₁inj (Ioo_subset_Icc_self hkI) (Ioo_subset_Icc_self hkI') heq')
    · exact absurd (heq' ▸ hσ₁W _) (Set.disjoint_left.1 hW12.symm (hσ₂W _))
    · exact absurd (heq' ▸ hσ₂W _) (Set.disjoint_left.1 hW12 (hσ₁W _))
    · exact hshift ρ₂ θ θ' (2 * ρ₂) k k' hρ₂
        (hσ₂inj (Ioo_subset_Icc_self hkI) (Ioo_subset_Icc_self hkI') heq')
  clear hW12 hσ₁inj hσ₂inj hσ₁W hσ₂W hUbval hshift
  have hγ₁J' : ∀ t ∈ J, (fun t => γ₁ (t / 4)) t ∉ (SL ∪ SR ∪ SO) := fun t ht => hγ₁J t ht
  clear hγ₁J
  obtain ⟨h', hh'sm, hh'per, hh'lev, hh'P, hh'O, hh'emb⟩ :=
    IndexOnePartner.exists_embedded_slices (by omega) hf (c := c₂)
      (fun x hx hcr => hregz x hx hcr) hhsm hhper hhlev (U := (Uo (1 / 4) (1 / 32) ∪ Uo (1 / 2) (1 / 32)) ×ˢ univ) (P := (Pc (1 / 4) (1 / 64) ∪ Pc (1 / 2) (1 / 64)) ×ˢ univ)
      (hUb.prod isOpen_univ)
      (fun θ s => by
        simp only [mem_prod, mem_univ, and_true, mem_union, ← hUper])
      (hPb.prod isClosed_univ)
      (fun θ s => by
        simp only [mem_prod, mem_univ, and_true, mem_union, ← hPper])
      (prod_mono hPbUb subset_rfl) himm hinj
      (hOopen _ (hγ₁sm.continuous.comp (continuous_id.div_const 4)))
      (hOdiag _ hγ₁J')
  clear hPper hUper hf hregz hOopen hOdiag hγ₁sm hUb hPb hPbUb hhsm hhper hhlev himm hinj hγ₁J' hh'per
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → M, S = fun θ => h' θ 0 := ⟨_, rfl⟩
  have hSsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ S := hSdef ▸
    hh'sm.comp (ContDiff.contMDiff (by fun_prop : ContDiff ℝ ∞ (fun θ : ℝ => (θ, (0 : ℝ)))))
  clear hh'sm
  have hSmd : ∀ θ, MDifferentiableAt 𝓘(ℝ, ℝ) I S θ := fun θ => hSsm.mdifferentiableAt (by simp)
  have hγarc : ∀ t, (|t - 1| ≤ 1 / 16 ∨ |t - 2| ≤ 1 / 16) → S ((1 / 4) * t + 0) = arc t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 3 := by
      rcases ht with h | h <;> rw [abs_le] at h <;> exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have hθ : (1 / 4) * t + 0 = t / 4 := by ring
    have hPb' : ((1 / 4) * t + 0, (0 : ℝ)) ∈ (Pc (1 / 4) (1 / 64) ∪ Pc (1 / 2) (1 / 64)) ×ˢ (univ : Set ℝ) := by
      refine ⟨?_, mem_univ _⟩
      rcases ht with h | h <;> rw [abs_le] at h
      · refine Or.inl ((hmemP _ _ _ hw64.1 hw64.2).2 ⟨0, abs_le.2 ⟨?_, ?_⟩⟩) <;>
          push_cast <;> linarith only [h.1, h.2]
      · refine Or.inr ((hmemP _ _ _ hw64.1 hw64.2).2 ⟨0, abs_le.2 ⟨?_, ?_⟩⟩) <;>
          push_cast <;> linarith only [h.1, h.2]
    have hPa' : (1 / 4) * t + 0 ∈ (Pc (1 / 4) (1 / 32) ∪ Pc (1 / 2) (1 / 32)) := by
      rcases hPb'.1 with h | h
      · obtain ⟨k, hk⟩ := (hmemP _ _ _ hw64.1 hw64.2).1 h
        exact Or.inl ((hmemP _ _ _ hw32.1 hw32.2).2 ⟨k, hk.trans h6432.le⟩)
      · obtain ⟨k, hk⟩ := (hmemP _ _ _ hw64.1 hw64.2).1 h
        exact Or.inr ((hmemP _ _ _ hw32.1 hw32.2).2 ⟨k, hk.trans h6432.le⟩)
    rw [hSdef]
    change h' _ 0 = arc t
    rw [hh'P _ _ hPb', hhdef]
    change γ₁ _ = arc t
    rw [hγ₁P _ hPa', hθ, hlamt t htI]
  clear hw32 hw64 h6432 hmemP hlamt hγ₁P hh'P
  have hγJ : ∀ t ∈ J, S ((1 / 4) * t + 0) ∉ (SL ∪ SR ∪ SO) := by
    intro t ht
    have h := hh'O ((1 / 4) * t + 0) 0
    have he : hh ((1 / 4) * t + 0) 0 = (fun t => γ₁ (t / 4)) t := by
      rw [hhdef]
      change γ₁ _ = γ₁ _
      congr 1
      ring
    rw [he] at h
    rw [hSdef]
    exact hOuse _ t _ ht h
  clear hOuse hhdef hh'O
  have hemb := hh'emb 0 ⟨le_rfl, zero_le_one⟩
  clear hh'emb
  refine ⟨fun t => S ((1 / 4) * t + 0), hSsm.comp
    (ContDiff.contMDiff (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (1 / 4) * t + 0))),
    fun t _ => by rw [hSdef]; exact hh'lev _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht t' ht' heq
    have heq' : h' ((1 / 4) * t + 0) 0 = h' ((1 / 4) * t' + 0) 0 := by
      rw [hSdef] at heq; exact heq
    obtain ⟨k, hk⟩ := hemb.2 _ _ heq'
    have hk1 : (k : ℝ) < 1 := by linarith only [hk, ht.1, ht'.2]
    have hk2 : (-1 : ℝ) < k := by linarith only [hk, ht.2, ht'.1]
    have hk0 : k = 0 := by
      have h1 : k < 1 := by exact_mod_cast hk1
      have h2 : -1 < k := by exact_mod_cast hk2
      omega
    rw [hk0, Int.cast_zero, add_zero] at hk
    linarith only [hk]
  · intro t _
    rw [hmaff S (1 / 4) 0 t (hSmd _)]
    rw [hSdef]
    exact smul_ne_zero (by norm_num) (hemb.1 _)
  · intro t ht
    rcases hJcov t ht with hJ | h1 | h2
    · exact ⟨fun h => absurd (Or.inl (Or.inl h)) (hγJ t hJ), fun h => absurd h (hJsub t hJ).2.1⟩
    · change S _ ∈ SL ↔ t = 1
      rw [hγarc t (Or.inl h1.le)]; exact (harcK t ht).1
    · change S _ ∈ SL ↔ t = 1
      rw [hγarc t (Or.inr h2.le)]; exact (harcK t ht).1
  · intro t ht
    rcases hJcov t ht with hJ | h1 | h2
    · exact ⟨fun h => absurd (Or.inl (Or.inr h)) (hγJ t hJ), fun h => absurd h (hJsub t hJ).2.2⟩
    · change S _ ∈ SR ↔ t = 2
      rw [hγarc t (Or.inl h1.le)]; exact (harcK t ht).2.1
    · change S _ ∈ SR ↔ t = 2
      rw [hγarc t (Or.inr h2.le)]; exact (harcK t ht).2.1
  · intro x hx hxL hne t ht hmem
    have hSO' : S ((1 / 4) * t + 0) ∈ SO := (hmemSO _).2 ⟨x, hx, hxL, hne, hmem⟩
    rcases hJcov t ht with hJ | h1 | h2
    · exact hγJ t hJ (Or.inr hSO')
    · rw [hγarc t (Or.inl h1.le)] at hSO'; exact (harcK t ht).2.2 hSO'
    · rw [hγarc t (Or.inr h2.le)] at hSO'; exact (harcK t ht).2.2 hSO'
  · have hN : {t : ℝ | |t - 1| < 1 / 16} ∈ 𝓝 (1 : ℝ) :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by norm_num)
    refine htrv _ _ σ₁ (fun t => S ((1 / 4) * t + 0)) ρ₁ 1 p₀ hρ₁ hσ₁sm ?_ ?_ hσ₁tr
    · filter_upwards [hN] with t ht
      rw [hγarc t (Or.inl ht.le), harc1 t (by rw [abs_lt] at ht; linarith only [ht.2])]
      congr 1
      ring
    · rw [hγarc 1 (Or.inl (by norm_num)), harc1 1 (by norm_num), sub_self, mul_zero, hσ₁0]
  · have hN : {t : ℝ | |t - 2| < 1 / 16} ∈ 𝓝 (2 : ℝ) :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by norm_num)
    refine htrv _ _ σ₂ (fun t => S ((1 / 4) * t + 0)) ρ₂ 2 p₁ hρ₂ hσ₂sm ?_ ?_ hσ₂tr
    · filter_upwards [hN] with t ht
      rw [hγarc t (Or.inr ht.le), harc2 t (by rw [abs_lt] at ht; linarith only [ht.1])]
      congr 1
      ring
    · rw [hγarc 2 (Or.inr (by norm_num)), harc2 2 (by norm_num), sub_self, mul_zero, hσ₂0]

theorem exists_arcFrame {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hγlev : ∀ t ∈ Icc (0 : ℝ) 3, g (γ t) = c₂) (hγinj : InjOn γ (Icc 0 3))
    (hγimm : ∀ t ∈ Icc (0 : ℝ) 3, mfderiv 𝓘(ℝ, ℝ) I γ t 1 ≠ 0)
    (hγ1 : γ 1 ∈ D.leftSphere q₁ hq₁ ε c₂) (hγ2 : γ 2 ∈ D.rightSphere q₂ hq₂ ε c₂)
    (ht1 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q₁ hq₁).k))) (D.leftCoord q₁ hq₁ ε)
      (γ 1) (mfderiv 𝓘(ℝ, ℝ) I γ 1 1) ≠ 0)
    (ht2 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε)
      (γ 2) (mfderiv 𝓘(ℝ, ℝ) I γ 2 1) ≠ 0) :
    ∃ Ys : Fin (n - 2) → LevelField I g,
      (∀ t ∈ Icc (0 : ℝ) 3, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        coordN v 0 • mfderiv 𝓘(ℝ, ℝ) I γ t 1 +
          ∑ j : Fin (n - 2), coordN v (1 + j) • (Ys j).Y (γ t))) ∧
      (∃ N₁ ∈ 𝓝 (γ 1), ∀ z ∈ N₁, ∀ j : Fin (n - 2), (j : ℕ) < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q₁ hq₁).k))) (D.leftCoord q₁ hq₁ ε) z
          ((Ys j).Y z) = 0) ∧
      ∃ N₂ ∈ 𝓝 (γ 2), ∀ z ∈ N₂, ∀ j : Fin (n - 2), ℓ ≤ (j : ℕ) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε) z
          ((Ys j).Y z) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hS.hℓn; omega⟩
  have hℓ2 := hS.hℓ
  have hℓm : ℓ + 1 ≤ m := by have := hS.hℓn; omega
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hε := hS.hε
  have hc₂lo : g q₂ + ε < c₂ := by linarith [hS.hq₂c₂, hS.hκ]
  have hc₂hi : c₂ < g q₁ - ε := by linarith [hS.hc₂q₁, hS.hκ]
  have hac₂ : a ≤ c₂ := by linarith [hS.hac, hS.hcq₂]
  have hc₂b : c₂ ≤ b := by linarith [hS.hq₁b]
  have hregz : ∀ z, g z = c₂ → mfderiv I 𝓘(ℝ, ℝ) g z ≠ 0 := by
    intro z hz h0
    have hu := D.unit z (by simp [hz, hac₂, hc₂b])
      (fun p hp => hS.hunit z (Or.inr ⟨by linarith, by linarith⟩) p hp)
    rw [h0] at hu
    simp at hu
  have hlevd : ∀ t ∈ Icc (0 : ℝ) 3,
      mfderiv I 𝓘(ℝ, ℝ) g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 0 := by
    intro t ht
    have hgγ : ContDiff ℝ 1 (g ∘ γ) :=
      (contMDiff_iff_contDiff.1 (hf.comp hγ)).of_le (by norm_num)
    have hd : HasDerivAt (g ∘ γ) (deriv (g ∘ γ) t) t :=
      ((hgγ.differentiable (by norm_num)) t).hasDerivAt
    have h0 : deriv (g ∘ γ) t = 0 := by
      have h1 : HasDerivWithinAt (g ∘ γ) 0 (Icc 0 3) t :=
        (hasDerivWithinAt_const t (Icc (0 : ℝ) 3) c₂).congr_of_mem
          (fun s hs => hγlev s hs) ht
      exact (uniqueDiffOn_Icc (by norm_num) t ht).eq_deriv _ hd.hasDerivWithinAt h1
    have hcomp := mfderiv_comp t (hf.mdifferentiableAt (x := γ t) (by simp))
      (hγ.mdifferentiableAt (x := t) (by simp))
    have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (g ∘ γ) t 1 = 0 := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (f := g ∘ γ) (x := t)).trans h0
    rw [hcomp] at h2
    exact h2
  have hrm₁ : 2 * ε < D.rm q₁ hq₁ ^ 2 := by linarith [(hS.hεr q₁ hq₁).2]
  have hrm₂ : 2 * ε < D.rm q₂ hq₂ ^ 2 := by linarith [(hS.hεr q₂ hq₂).2]
  obtain ⟨O₁, hO₁, hSO₁, hG₁, hsub₁⟩ := leftCoord_submersion hf D hq₁ hε hrm₁ hac₂ hc₂hi.le
    (fun y hy x hx => hS.hunit y (Or.inr ⟨by linarith [hy.1], hy.2⟩) x hx)
  obtain ⟨O₂, hO₂, hSO₂, hG₂, hsub₂⟩ := rightCoord_submersion hf D hq₂ hε hrm₂ hc₂lo.le hc₂b
    (fun y hy x hx => hS.hunit y (Or.inr ⟨hy.1, by linarith [hy.2]⟩) x hx)
  have hk₁ := hS.hk₁
  have hk₂ := hS.hk₂
  obtain ⟨YA, NA, hNA, hYAt, hYAi⟩ := exists_adaptedFields hf (k := ℓ)
    (s := m + 2 - (D.chart q₁ hq₁).k) (by omega) (D.leftCoord q₁ hq₁ ε) (γ 1)
    ⟨O₁, hO₁.mem_nhds (hSO₁ hγ1), hG₁⟩ (hsub₁ _ hγ1).1 (hsub₁ _ hγ1).2
  obtain ⟨YB, NB, hNB, hYBt, hYBi⟩ := exists_adaptedFields hf (k := m - ℓ)
    (s := (D.chart q₂ hq₂).k) (by omega) (D.rightCoord q₂ hq₂ ε) (γ 2)
    ⟨O₂, hO₂.mem_nhds (hSO₂ hγ2), hG₂⟩ (hsub₂ _ hγ2).1 (hsub₂ _ hγ2).2
  set K : Set (Fin 1 → ℝ) := Icc (fun _ => 0) (fun _ => 3) with hKdef
  have hKmem : ∀ y : Fin 1 → ℝ, y ∈ K ↔ y 0 ∈ Icc (0 : ℝ) 3 := by
    intro y
    simp only [hKdef, mem_Icc, Pi.le_def, Fin.forall_fin_one]
  have hK : IsCompact K := isCompact_Icc
  have hKc : Convex ℝ K := convex_Icc _ _
  have hemb : ∀ y : Fin 1 → ℝ, y = fun _ => y 0 := fun y =>
    funext fun i => by rw [Subsingleton.elim i 0]
  set ψ : (Fin 1 → ℝ) → M := fun y => γ (y 0) with hψdef
  have hψ : ContinuousOn ψ K := (hγ.continuous.comp (continuous_apply 0)).continuousOn
  have hreg : ∀ y ∈ K, mfderiv I 𝓘(ℝ, ℝ) g (ψ y) ≠ 0 := fun y hy =>
    hregz _ (hγlev _ ((hKmem y).1 hy))
  obtain ⟨E, hEc, hE⟩ : ∃ E : (Fin 1 → ℝ) → Fin (m + 1) → (Fin (m + 2) → ℝ),
      (∀ j, ContinuousOn (fun y => (⟨ψ y, E y j⟩ : TangentBundle I M)) K) ∧
      ∀ y ∈ K, (∀ j, mfderiv I 𝓘(ℝ, ℝ) g (ψ y) (E y j) = 0) ∧ LinearIndependent ℝ (E y) :=
    exists_levelFrame_along hf hK hKc hψ hreg
  have hspan_ker : ∀ (φ : (Fin (m + 2) → ℝ) →L[ℝ] ℝ), φ ≠ 0 →
      ∀ w : Fin (m + 1) → (Fin (m + 2) → ℝ), LinearIndependent ℝ w → (∀ j, φ (w j) = 0) →
      ∀ v, φ v = 0 → v ∈ Submodule.span ℝ (range w) := by
    intro φ hφ w hw hwφ v hv
    have hsurj : LinearMap.range (φ : (Fin (m + 2) → ℝ) →ₗ[ℝ] ℝ) = ⊤ := by
      obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
        by_contra h
        exact hφ (ContinuousLinearMap.ext fun u => not_not.1 fun hu => h ⟨u, hu⟩)
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨(r / φ u) • u, ?_⟩
      simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      field_simp
    have hker : Module.finrank ℝ (LinearMap.ker (φ : (Fin (m + 2) → ℝ) →ₗ[ℝ] ℝ)) = m + 1 := by
      have h := LinearMap.finrank_range_add_finrank_ker (φ : (Fin (m + 2) → ℝ) →ₗ[ℝ] ℝ)
      rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
      omega
    have hle : Submodule.span ℝ (range w) ≤ LinearMap.ker (φ : (Fin (m + 2) → ℝ) →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hwφ j
    have heq : Submodule.span ℝ (range w) = LinearMap.ker (φ : (Fin (m + 2) → ℝ) →ₗ[ℝ] ℝ) :=
      Submodule.eq_of_le_of_finrank_eq hle
        (by rw [finrank_span_eq_card hw, Fintype.card_fin, hker])
    rw [heq]
    exact hv
  have hEs : ∀ y ∈ K, ∀ v : TangentSpace I (ψ y), mfderiv I 𝓘(ℝ, ℝ) g (ψ y) v = 0 →
      v ∈ Submodule.span ℝ (Set.range (E y)) := fun y hy v hv =>
    hspan_ker (mfderiv I 𝓘(ℝ, ℝ) g (ψ y) : (Fin (m + 2) → ℝ) →L[ℝ] ℝ) (hreg y hy) (E y)
      (hE y hy).2 (hE y hy).1 v hv
  have hγT : Continuous (fun t : ℝ => (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t 1⟩ : TangentBundle I M)) := by
    have h1 := hγ.continuous_tangentMap (by simp)
    have h2 : Continuous (fun t : ℝ =>
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, (1 : ℝ)))) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (h1.comp h2).congr fun t => rfl
  obtain ⟨a, hac, ha⟩ := exists_continuousOn_frameCoeff hψ hEc (fun y hy => (hE y hy).2)
    (v := fun y => (mfderiv 𝓘(ℝ, ℝ) I γ (y 0) 1 : Fin (m + 2) → ℝ))
    (hγT.comp (continuous_apply 0)).continuousOn
    (fun y hy => hEs y hy _ (hlevd _ ((hKmem y).1 hy)))
  have ha0 : ∀ y ∈ K, a y ≠ 0 := by
    intro y hy h0
    have h := ha y hy
    rw [h0] at h
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h
    exact hγimm _ ((hKmem y).1 hy) h.symm
  have haa : ∀ y ∈ K, a y ⬝ᵥ a y ≠ 0 := fun y hy h => ha0 y hy (dotProduct_self_eq_zero.1 h)
  let Plin : (Fin 1 → ℝ) → (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) := fun y =>
    { toFun := fun v => v - ((a y ⬝ᵥ v) / (a y ⬝ᵥ a y)) • a y
      map_add' := fun u v => by
        simp only [dotProduct_add, add_div, add_smul]
        abel
      map_smul' := fun r v => by
        simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul,
          smul_sub] }
  let P : (Fin 1 → ℝ) → (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) := fun y =>
    LinearMap.toContinuousLinearMap (Plin y)
  have hPapp : ∀ y v, P y v = v - ((a y ⬝ᵥ v) / (a y ⬝ᵥ a y)) • a y := fun y v => rfl
  have hPdot : ∀ y ∈ K, ∀ v, a y ⬝ᵥ P y v = 0 := by
    intro y hy v
    rw [hPapp, dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ (haa y hy),
      sub_self]
  have hPcont : ContinuousOn P K := by
    rw [continuousOn_clm_apply]
    intro v
    simp only [hPapp]
    have hd : ∀ w : Fin (m + 1) → ℝ, ContinuousOn (fun y => a y ⬝ᵥ w) K := fun w => by
      simp only [dotProduct]
      exact continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 hac) i).mul continuousOn_const
    have hdd : ContinuousOn (fun y => a y ⬝ᵥ a y) K := by
      simp only [dotProduct]
      exact continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_pi.1 hac) i).mul ((continuousOn_pi.1 hac) i)
    exact continuousOn_const.sub (((hd v).div hdd haa).smul hac)
  have hPidem : ∀ y ∈ K, (P y).comp (P y) = P y := by
    intro y hy
    ext1 v
    rw [ContinuousLinearMap.comp_apply, hPapp y (P y v), hPdot y hy v, zero_div, zero_smul,
      sub_zero]
  have hPrank : ∀ y ∈ K, Module.finrank ℝ
      (LinearMap.range (P y : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ))) = m := by
    intro y hy
    have hker : LinearMap.ker (P y : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) = ℝ ∙ a y := by
      ext v
      rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
      constructor
      · intro hv
        refine ⟨(a y ⬝ᵥ v) / (a y ⬝ᵥ a y), ?_⟩
        have h : P y v = 0 := hv
        rw [hPapp, sub_eq_zero] at h
        exact h.symm
      · rintro ⟨r, rfl⟩
        change P y (r • a y) = 0
        rw [hPapp, dotProduct_smul, smul_eq_mul, mul_div_assoc, div_self (haa y hy), mul_one,
          sub_self]
    have h := LinearMap.finrank_range_add_finrank_ker
      (P y : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ))
    rw [hker, finrank_span_singleton (ha0 y hy), Module.finrank_fin_fun] at h
    omega
  obtain ⟨F, hFc, hF⟩ := exists_frame_of_projections hK hKc P hPcont hPidem hPrank
  have hFdot : ∀ y ∈ K, ∀ i, a y ⬝ᵥ F y i = 0 := by
    intro y hy i
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 ((hF y hy).2 i)
    rw [← hu]
    exact hPdot y hy u
  have hRi : ∀ y ∈ K,
      LinearIndependent ℝ (Fin.cons (a y) (F y) : Fin (m + 1) → Fin (m + 1) → ℝ) := by
    intro y hy
    rw [linearIndependent_finCons]
    refine ⟨(hF y hy).1, fun hmem => haa y hy ?_⟩
    let dl : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => a y ⬝ᵥ v
        map_add' := dotProduct_add _
        map_smul' := fun r v => by simp [dotProduct_smul] }
    have hle : Submodule.span ℝ (range (F y)) ≤ LinearMap.ker dl := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hFdot y hy i
    exact hle hmem
  have hdecomp : ∀ y ∈ K, ∀ w : Fin (m + 1) → ℝ,
      ∃ z : ℝ, ∃ L : Fin m → ℝ, w = z • a y + ∑ i, L i • F y i := by
    intro y hy w
    have htop := (hRi y hy).span_eq_top_of_card_eq_finrank' (by simp)
    have hw : w ∈ Submodule.span ℝ
        (range (Fin.cons (a y) (F y) : Fin (m + 1) → Fin (m + 1) → ℝ)) := by
      rw [htop]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    refine ⟨c 0, fun i => c i.succ, ?_⟩
    rw [← hc, Fin.sum_univ_succ]
    simp
  have hswap : ∀ {p : ℕ} (c z : Fin p → ℝ) (L : Fin p → Fin m → ℝ) (u : Fin (m + 1) → ℝ)
      (Fv : Fin m → Fin (m + 1) → ℝ),
      ∑ j, c j • (z j • u + ∑ i, L j i • Fv i) =
        (∑ j, c j * z j) • u + ∑ i, (∑ j, c j * L j i) • Fv i := by
    intro p c z L u Fv
    simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm (f := fun j i => (c j * L j i) • Fv i)]
  set y₁ : Fin 1 → ℝ := fun _ => 1 with hy₁def
  set y₂ : Fin 1 → ℝ := fun _ => 2 with hy₂def
  have hy₁K : y₁ ∈ K := (hKmem _).2 ⟨by norm_num, by norm_num⟩
  have hy₂K : y₂ ∈ K := (hKmem _).2 ⟨by norm_num, by norm_num⟩
  have hAlev : ∀ j, mfderiv I 𝓘(ℝ, ℝ) g (γ 1) ((YA j).Y (γ 1)) = 0 := fun j =>
    (NormedSpace.fromTangentSpace _).map_eq_zero_iff.1 ((YA j).level (γ 1))
  have hBlev : ∀ j, mfderiv I 𝓘(ℝ, ℝ) g (γ 2) ((YB j).Y (γ 2)) = 0 := fun j =>
    (NormedSpace.fromTangentSpace _).map_eq_zero_iff.1 ((YB j).level (γ 2))
  have hαex : ∀ j : Fin ℓ, ∃ α : Fin (m + 1) → ℝ, ∑ k, α k • E y₁ k = (YA j).Y (γ 1) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hEs y₁ hy₁K _ (hAlev j))
  have hβex : ∀ j : Fin (m - ℓ), ∃ β : Fin (m + 1) → ℝ, ∑ k, β k • E y₂ k = (YB j).Y (γ 2) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hEs y₂ hy₂K _ (hBlev j))
  choose α hα using hαex
  choose β hβ using hβex
  have hαi : LinearIndependent ℝ (Fin.cons (a y₁) α : Fin (ℓ + 1) → Fin (m + 1) → ℝ) := by
    apply LinearIndependent.of_comp (Fintype.linearCombination ℝ (E y₁))
    have hcomp : (Fintype.linearCombination ℝ (E y₁)) ∘
        (Fin.cons (a y₁) α : Fin (ℓ + 1) → Fin (m + 1) → ℝ) =
        (Fin.cons (mfderiv 𝓘(ℝ, ℝ) I γ 1 1 : Fin (m + 2) → ℝ)
          (fun j => ((YA j).Y (γ 1) : Fin (m + 2) → ℝ)) : Fin (ℓ + 1) → Fin (m + 2) → ℝ) := by
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Function.comp_apply, Fin.cons_zero, Fintype.linearCombination_apply]
        exact ha y₁ hy₁K
      · simp only [Function.comp_apply, Fin.cons_succ, Fintype.linearCombination_apply]
        exact hα j
    rw [hcomp]
    refine linearIndependent_finCons.2 ⟨hYAi, fun hmem => ht1 ?_⟩
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    let φ : (Fin (m + 2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (m + 2 - (D.chart q₁ hq₁).k)) :=
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 2 - (D.chart q₁ hq₁).k)))
        (D.leftCoord q₁ hq₁ ε) (γ 1)
    change φ (mfderiv 𝓘(ℝ, ℝ) I γ 1 1) = 0
    rw [← hcc, map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      have h0 : φ ((YA j).Y (γ 1)) = 0 := hYAt (γ 1) (mem_of_mem_nhds hNA) j
      have h1 : φ (cc j • ((YA j).Y (γ 1) : Fin (m + 2) → ℝ)) =
          cc j • φ ((YA j).Y (γ 1)) := φ.map_smul _ _
      rw [h0, smul_zero] at h1
      exact h1
  have hβi : LinearIndependent ℝ (Fin.cons (a y₂) β : Fin (m - ℓ + 1) → Fin (m + 1) → ℝ) := by
    apply LinearIndependent.of_comp (Fintype.linearCombination ℝ (E y₂))
    have hcomp : (Fintype.linearCombination ℝ (E y₂)) ∘
        (Fin.cons (a y₂) β : Fin (m - ℓ + 1) → Fin (m + 1) → ℝ) =
        (Fin.cons (mfderiv 𝓘(ℝ, ℝ) I γ 2 1 : Fin (m + 2) → ℝ)
          (fun j => ((YB j).Y (γ 2) : Fin (m + 2) → ℝ)) :
          Fin (m - ℓ + 1) → Fin (m + 2) → ℝ) := by
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Function.comp_apply, Fin.cons_zero, Fintype.linearCombination_apply]
        exact ha y₂ hy₂K
      · simp only [Function.comp_apply, Fin.cons_succ, Fintype.linearCombination_apply]
        exact hβ j
    rw [hcomp]
    refine linearIndependent_finCons.2 ⟨hYBi, fun hmem => ht2 ?_⟩
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    let φ : (Fin (m + 2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k) :=
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε) (γ 2)
    change φ (mfderiv 𝓘(ℝ, ℝ) I γ 2 1) = 0
    rw [← hcc, map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      have h0 : φ ((YB j).Y (γ 2)) = 0 := hYBt (γ 2) (mem_of_mem_nhds hNB) j
      have h1 : φ (cc j • ((YB j).Y (γ 2) : Fin (m + 2) → ℝ)) =
          cc j • φ ((YB j).Y (γ 2)) := φ.map_smul _ _
      rw [h0, smul_zero] at h1
      exact h1
  choose zα Lα hzLα using fun j => hdecomp y₁ hy₁K (α j)
  choose zβ Lβ hzLβ using fun j => hdecomp y₂ hy₂K (β j)
  have hLαi : LinearIndependent ℝ Lα := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∀ i, ∑ j, c j * Lα j i = 0 := fun i => by
      have := congrFun hc i
      simpa [Finset.sum_apply] using this
    have h1 : ∑ j, c j • α j = (∑ j, c j * zα j) • a y₁ := by
      simp only [hzLα]
      rw [hswap]
      simp [hc']
    have h2 := (Fintype.linearIndependent_iff.1 hαi) (Fin.cons (-(∑ j, c j * zα j)) c)
      (by rw [Fin.sum_univ_succ]; simp [h1])
    intro j
    simpa using h2 j.succ
  have hLβi : LinearIndependent ℝ Lβ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∀ i, ∑ j, c j * Lβ j i = 0 := fun i => by
      have := congrFun hc i
      simpa [Finset.sum_apply] using this
    have h1 : ∑ j, c j • β j = (∑ j, c j * zβ j) • a y₂ := by
      simp only [hzLβ]
      rw [hswap]
      simp [hc']
    have h2 := (Fintype.linearIndependent_iff.1 hβi) (Fin.cons (-(∑ j, c j * zβ j)) c)
      (by rw [Fin.sum_univ_succ]; simp [h1])
    intro j
    simpa using h2 j.succ
  have hcomplete : ∀ k p : ℕ, p + k = m → ∀ u : Fin p → (Fin m → ℝ), LinearIndependent ℝ u →
      ∃ w : Fin m → (Fin m → ℝ), LinearIndependent ℝ w ∧
        ∀ (j : Fin m) (h : (j : ℕ) < p), w j = u ⟨j, h⟩ := by
    intro k
    induction k with
    | zero =>
      intro p hp u hu
      refine ⟨fun j => u ⟨j, by have := j.isLt; omega⟩, ?_, fun j h => rfl⟩
      exact hu.comp (fun j : Fin m => (⟨j, by have := j.isLt; omega⟩ : Fin p))
        (fun i j h => by
          simp only [Fin.mk.injEq] at h
          exact Fin.ext h)
    | succ k ih =>
      intro p hp u hu
      obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hu
        (by rw [Module.finrank_fin_fun]; omega)
      obtain ⟨w, hw, hwu⟩ := ih (p + 1) (by omega) _ hx
      refine ⟨w, hw, fun j h => ?_⟩
      rw [hwu j (by omega)]
      simp [Fin.snoc, h]
  obtain ⟨w1, hw1, hw1u⟩ := hcomplete (m - ℓ) ℓ (by omega) Lα hLαi
  obtain ⟨w', hw', hw'u⟩ := hcomplete ℓ (m - ℓ) (by omega) (fun i => Lβ (Fin.rev i))
    (hLβi.comp _ Fin.rev_injective)
  set w2 : Fin m → (Fin m → ℝ) := fun j => w' (Fin.rev j) with hw2def
  have hw2 : LinearIndependent ℝ w2 := hw'.comp _ Fin.rev_injective
  have hw2u : ∀ (j : Fin m) (h : ℓ ≤ (j : ℕ)),
      w2 j = Lβ ⟨j - ℓ, by have := j.isLt; omega⟩ := by
    intro j h
    have hlt : ((Fin.rev j : Fin m) : ℕ) < m - ℓ := by
      rw [Fin.val_rev]
      omega
    simp only [hw2def]
    rw [hw'u (Fin.rev j) hlt]
    congr 1
    ext
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  have hdetne : ∀ w : Fin m → (Fin m → ℝ), LinearIndependent ℝ w → (Matrix.of w).det ≠ 0 := by
    intro w hw
    have hu : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hflip : ∀ (L : Matrix (Fin m) (Fin m) ℝ) (i : Fin m),
      (L.updateRow i (-(L i))).det = -L.det := by
    intro L i
    have h := Matrix.det_updateRow_smul L i (-1) (L i)
    rw [neg_one_smul, Matrix.updateRow_eq_self] at h
    rw [h]
    ring
  obtain ⟨L1, hL1pos, hL1row⟩ : ∃ L : Matrix (Fin m) (Fin m) ℝ, 0 < L.det ∧
      ∀ j : Fin m, (j : ℕ) < ℓ → L j = w1 j := by
    rcases lt_or_gt_of_ne (hdetne w1 hw1) with h | h
    · refine ⟨(Matrix.of w1).updateRow ⟨m - 1, by omega⟩ (-(Matrix.of w1 ⟨m - 1, by omega⟩)),
        by rw [hflip]; linarith, fun j hj => ?_⟩
      rw [Matrix.updateRow_ne (fun h' => by
        have := congrArg Fin.val h'
        simp only at this
        omega)]
      rfl
    · exact ⟨Matrix.of w1, h, fun j _ => rfl⟩
  obtain ⟨L2, hL2pos, hL2row⟩ : ∃ L : Matrix (Fin m) (Fin m) ℝ, 0 < L.det ∧
      ∀ j : Fin m, ℓ ≤ (j : ℕ) → L j = w2 j := by
    rcases lt_or_gt_of_ne (hdetne w2 hw2) with h | h
    · refine ⟨(Matrix.of w2).updateRow ⟨0, by omega⟩ (-(Matrix.of w2 ⟨0, by omega⟩)),
        by rw [hflip]; linarith, fun j hj => ?_⟩
      rw [Matrix.updateRow_ne (fun h' => by
        have := congrArg Fin.val h'
        simp only at this
        omega)]
      rfl
    · exact ⟨Matrix.of w2, h, fun j _ => rfl⟩
  obtain ⟨Lp, hLpc, hLp0, hLp1, hLpdet⟩ : ∃ Lp : ℝ → Matrix (Fin m) (Fin m) ℝ, Continuous Lp ∧
      Lp 0 = L1 ∧ Lp 1 = L2 ∧ ∀ s, 0 < (Lp s).det := by
    have hJ := joinedIn_det_pos hL1pos hL2pos
    exact ⟨hJ.somePath.extend, hJ.somePath.extend.continuous, hJ.somePath.extend_zero,
      hJ.somePath.extend_one, fun s => hJ.somePath_mem _⟩
  set z1 : Fin m → ℝ := fun j => if h : (j : ℕ) < ℓ then zα ⟨j, h⟩ else 0 with hz1def
  set z2 : Fin m → ℝ := fun j => if h : ℓ ≤ (j : ℕ) then zβ ⟨j - ℓ, by have := j.isLt; omega⟩
    else 0 with hz2def
  set zf : (Fin 1 → ℝ) → Fin m → ℝ := fun y => z1 + (y 0 - 1) • (z2 - z1) with hzfdef
  set Lf : (Fin 1 → ℝ) → Matrix (Fin m) (Fin m) ℝ := fun y => Lp (y 0 - 1) with hLfdef
  set cf : (Fin 1 → ℝ) → Fin m → (Fin (m + 1) → ℝ) :=
    fun y j => zf y j • a y + ∑ i, Lf y j i • F y i with hcfdef
  have hcf1 : ∀ (j : Fin m) (h : (j : ℕ) < ℓ), cf y₁ j = α ⟨j, h⟩ := by
    intro j h
    have hz : zf y₁ = z1 := by simp [hzfdef, hy₁def]
    have hL : Lf y₁ = L1 := by simp [hLfdef, hy₁def, hLp0]
    rw [hzLα ⟨j, h⟩]
    simp only [hcfdef, hz, hL, hL1row j h, hw1u j h, hz1def, dite_eq_left_of_eq_true (eq_true h)]
  have hcf2 : ∀ (j : Fin m) (h : ℓ ≤ (j : ℕ)),
      cf y₂ j = β ⟨j - ℓ, by have := j.isLt; omega⟩ := by
    intro j h
    have hz : zf y₂ = z2 := by
      simp only [hzfdef, hy₂def]
      norm_num
    have hL : Lf y₂ = L2 := by
      simp only [hLfdef, hy₂def]
      norm_num [hLp1]
    rw [hzLβ]
    simp only [hcfdef, hz, hL, hL2row j h, hw2u j h, hz2def, dite_eq_left_of_eq_true (eq_true h)]
  have hFci : ∀ i, ContinuousOn (fun y => F y i) K := fun i => continuousOn_pi.1 hFc i
  have hcfc : ContinuousOn cf K := by
    refine continuousOn_pi.2 fun j => ?_
    have hz : ContinuousOn (fun y => zf y j) K := by
      simp only [hzfdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact continuousOn_const.add
        ((((continuous_apply 0).sub continuous_const).continuousOn).mul continuousOn_const)
    have hL : ∀ i, ContinuousOn (fun y => Lf y j i) K := fun i =>
      ((hLpc.comp ((continuous_apply 0).sub continuous_const)).matrix_elem j i).continuousOn
    exact (hz.smul hac).add (continuousOn_finsetSum _ fun i _ => (hL i).smul (hFci i))
  have hcfi : ∀ y ∈ K,
      LinearIndependent ℝ (Fin.cons (a y) (cf y) : Fin (m + 1) → Fin (m + 1) → ℝ) := by
    intro y hy
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_succ] at hc
    simp only [Fin.cons_zero, Fin.cons_succ, hcfdef] at hc
    rw [show ∑ j, c j.succ • (zf y j • a y + ∑ i, Lf y j i • F y i) = _ from
      hswap (fun j => c j.succ) (zf y) (fun j i => Lf y j i) (a y) (F y)] at hc
    have h2 := (Fintype.linearIndependent_iff.1 (hRi y hy))
      (Fin.cons (c 0 + ∑ j, c j.succ * zf y j) (fun i => ∑ j, c j.succ * Lf y j i))
      (by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [add_smul, add_assoc]
        exact hc)
    have hv : Matrix.vecMul (fun j => c j.succ) (Lf y) = 0 := by
      funext i
      simpa [Matrix.vecMul, dotProduct] using h2 i.succ
    have hc0 := Matrix.eq_zero_of_vecMul_eq_zero (hLpdet _).ne' hv
    have hcs : ∀ j : Fin m, c j.succ = 0 := fun j => congrFun hc0 j
    intro k
    refine Fin.cases ?_ (fun j => hcs j) k
    have h0 := h2 0
    simp only [Fin.cons_zero, hcs, zero_mul, Finset.sum_const_zero, add_zero] at h0
    exact h0
  obtain ⟨η, hη, hrob⟩ : ∃ η > 0, ∀ y ∈ K, ∀ c' : Fin m → Fin (m + 1) → ℝ,
      (∀ j k, |c' j k - cf y j k| < η) →
      LinearIndependent ℝ (Fin.cons (a y) c' : Fin (m + 1) → Fin (m + 1) → ℝ) := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 hK
    let Φ : (Fin m → Fin (m + 1) → ℝ) × K → ℝ := fun p =>
      Matrix.det (Matrix.of (Fin.cons (a p.2) (cf p.2 + p.1) : Fin (m + 1) → Fin (m + 1) → ℝ))
    have hac' : Continuous (fun x : K => a x) :=
      hac.comp_continuous continuous_subtype_val (fun x => x.2)
    have hcf' : Continuous (fun x : K => cf x) :=
      hcfc.comp_continuous continuous_subtype_val (fun x => x.2)
    have hΦ : Continuous Φ := by
      apply Continuous.matrix_det
      have h1 : Continuous (fun p : (Fin m → Fin (m + 1) → ℝ) × K => a p.2) :=
        hac'.comp continuous_snd
      have h2 : Continuous (fun p : (Fin m → Fin (m + 1) → ℝ) × K => cf p.2 + p.1) :=
        (hcf'.comp continuous_snd).add continuous_fst
      exact Continuous.finCons (A := fun _ => Fin (m + 1) → ℝ) h1 h2
    have hdet : ∀ x : K, Φ (0, x) ≠ 0 := by
      intro x
      have hi := hcfi x x.2
      have hu : IsUnit (Matrix.of (Fin.cons (a x) (cf x) : Fin (m + 1) → Fin (m + 1) → ℝ)) :=
        Matrix.linearIndependent_rows_iff_isUnit.1 hi
      have h := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
      simpa [Φ] using h
    have hev := (isCompact_univ (X := K)).eventually_forall_of_forall_eventually
      (x₀ := (0 : Fin m → Fin (m + 1) → ℝ)) (P := fun Δ x => Φ (Δ, x) ≠ 0)
      (fun x _ => hΦ.continuousAt.eventually_ne (hdet x))
    obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨η, hη, fun y hy c' hc' => ?_⟩
    have hdist : dist (c' - cf y) 0 < η := by
      rw [dist_pi_lt_iff hη]
      intro j
      rw [dist_pi_lt_iff hη]
      intro k
      simpa [Real.dist_eq] using hc' j k
    have h := hηP hdist ⟨y, hy⟩ (mem_univ _)
    have e : cf y + (c' - cf y) = c' := by abel
    have h' : (Matrix.of (Fin.cons (a y) c' : Fin (m + 1) → Fin (m + 1) → ℝ)).det ≠ 0 := by
      simpa only [Φ, e] using h
    exact Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h'))
  have hψi : InjOn ψ K := by
    intro y hy y' hy' h
    have h0 : y 0 = y' 0 := hγinj ((hKmem y).1 hy) ((hKmem y').1 hy') h
    rw [hemb y, hemb y', h0]
  have hEf : ∀ y ∈ K, ∀ k, mfderiv I 𝓘(ℝ, ℝ) g (ψ y) (E y k) = 0 := fun y hy => (hE y hy).1
  have hEi : ∀ y ∈ K, LinearIndependent ℝ (E y) := fun y hy => (hE y hy).2
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
  have h2I : (2 : ℝ) ∈ Icc (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
  have happrox : ∀ j : Fin m, ∃ Y : LevelField I g,
      ((j : ℕ) < ℓ → ∀ᶠ z in 𝓝 (γ 1),
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 2 - (D.chart q₁ hq₁).k)))
          (D.leftCoord q₁ hq₁ ε) z (Y.Y z) = 0) ∧
      (ℓ ≤ (j : ℕ) → ∀ᶠ z in 𝓝 (γ 2),
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k))
          (D.rightCoord q₂ hq₂ ε) z (Y.Y z) = 0) ∧
      ∀ y ∈ K, ∃ c' : Fin (m + 1) → ℝ, Y.Y (ψ y) = frameVec E y c' ∧
        ∀ k, |c' k - cf y j k| < η := by
    intro j
    by_cases hj : (j : ℕ) < ℓ
    · have hcfS : ∀ y ∈ K, ψ y ∈ ({γ 1} : Set M) →
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 2 - (D.chart q₁ hq₁).k)))
            (D.leftCoord q₁ hq₁ ε) (ψ y) (frameVec E y (cf y j)) = 0 := by
        intro y hy hψy
        have hy0 : y 0 = 1 := hγinj ((hKmem y).1 hy) h1I hψy
        have hyy : y = y₁ := by rw [hemb y, hy0]
        subst hyy
        have hfv : frameVec E y₁ (cf y₁ j) = (YA ⟨j, hj⟩).Y (γ 1) := by
          rw [hcf1 j hj]
          exact hα ⟨j, hj⟩
        rw [hfv]
        exact hYAt (γ 1) (mem_of_mem_nhds hNA) ⟨j, hj⟩
      obtain ⟨Y, hYS, hYa⟩ := exists_levelField_approx hf hO₁ hG₁ isClosed_singleton
        (singleton_subset_iff.2 (hSO₁ hγ1))
        (fun z hz => by
          rw [mem_singleton_iff] at hz
          subst hz
          exact (hsub₁ _ hγ1).2)
        hK hψ hψi hreg hEc hEf hEi hEs (cf := fun y => cf y j) (continuousOn_pi.1 hcfc j) hcfS hη
      refine ⟨Y, fun _ => ?_, fun h => absurd h (by omega), hYa⟩
      obtain ⟨N, hN, hNY⟩ := hYS (γ 1) rfl
      exact Filter.mem_of_superset hN hNY
    · have hj' : ℓ ≤ (j : ℕ) := by omega
      have hcfS : ∀ y ∈ K, ψ y ∈ ({γ 2} : Set M) →
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k))
            (D.rightCoord q₂ hq₂ ε) (ψ y) (frameVec E y (cf y j)) = 0 := by
        intro y hy hψy
        have hy0 : y 0 = 2 := hγinj ((hKmem y).1 hy) h2I hψy
        have hyy : y = y₂ := by rw [hemb y, hy0]
        subst hyy
        have hfv : frameVec E y₂ (cf y₂ j) =
            (YB ⟨j - ℓ, by have := j.isLt; omega⟩).Y (γ 2) := by
          rw [hcf2 j hj']
          exact hβ _
        rw [hfv]
        exact hYBt (γ 2) (mem_of_mem_nhds hNB) _
      obtain ⟨Y, hYS, hYa⟩ := exists_levelField_approx hf hO₂ hG₂ isClosed_singleton
        (singleton_subset_iff.2 (hSO₂ hγ2))
        (fun z hz => by
          rw [mem_singleton_iff] at hz
          subst hz
          exact (hsub₂ _ hγ2).2)
        hK hψ hψi hreg hEc hEf hEi hEs (cf := fun y => cf y j) (continuousOn_pi.1 hcfc j) hcfS hη
      refine ⟨Y, fun h => absurd h hj, fun _ => ?_, hYa⟩
      obtain ⟨N, hN, hNY⟩ := hYS (γ 2) rfl
      exact Filter.mem_of_superset hN hNY
  choose Ys hYs1 hYs2 hYs3 using happrox
  refine ⟨Ys, ?_, ?_, ?_⟩
  · intro t ht
    set y : Fin 1 → ℝ := fun _ => t with hydef
    have hyK : y ∈ K := (hKmem y).2 ht
    choose c' hc'Y hc'a using fun j => hYs3 j y hyK
    have hli := hrob y hyK c' (fun j k => hc'a j k)
    have hker : LinearMap.ker (Fintype.linearCombination ℝ (E y)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      rw [Fintype.linearCombination_apply] at hv
      funext k
      exact Fintype.linearIndependent_iff.1 (hEi y hyK) v hv k
    have hli2 := hli.map' _ hker
    set Vt : Fin (m + 1) → (Fin (m + 2) → ℝ) :=
      Fin.cons (@id (Fin (m + 2) → ℝ) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
        (fun j => @id (Fin (m + 2) → ℝ) ((Ys j).Y (γ t))) with hVtdef
    have hcomp : (Fintype.linearCombination ℝ (E y)) ∘
        (Fin.cons (a y) c' : Fin (m + 1) → Fin (m + 1) → ℝ) = Vt := by
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Function.comp_apply, Fin.cons_zero, Fintype.linearCombination_apply, hVtdef]
        exact ha y hyK
      · simp only [Function.comp_apply, Fin.cons_succ, Fintype.linearCombination_apply, hVtdef]
        exact (hc'Y j).symm
    rw [hcomp] at hli2
    change Function.Injective (fun v : Fin (m + 1) → ℝ =>
      coordN v 0 • @id (Fin (m + 2) → ℝ) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) +
        ∑ j : Fin m, coordN v (1 + j) • @id (Fin (m + 2) → ℝ) ((Ys j).Y (γ t)))
    have hsum : ∀ v : Fin (m + 1) → ℝ,
        coordN v 0 • @id (Fin (m + 2) → ℝ) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) +
          ∑ j : Fin m, coordN v (1 + j) • @id (Fin (m + 2) → ℝ) ((Ys j).Y (γ t)) =
        ∑ k, v k • Vt k := by
      intro v
      rw [Fin.sum_univ_succ]
      simp only [hVtdef, Fin.cons_zero, Fin.cons_succ]
      have h0 : coordN v 0 = v 0 := by simp [coordN]
      have hs : ∀ j : Fin m, coordN v (1 + (j : ℕ)) = v j.succ := fun j => by
        simp only [coordN, dite_eq_left_of_eq_true (eq_true (show 1 + (j : ℕ) < m + 1 by omega))]
        congr 1
        ext
        simp only [Fin.val_succ]
        omega
      simp only [h0, hs]
    intro v₁ v₂ hv
    simp only at hv
    rw [hsum v₁, hsum v₂] at hv
    have h0 := Fintype.linearIndependent_iff.1 hli2 (v₁ - v₂)
      (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hv, sub_self])
    funext k
    exact sub_eq_zero.1 (h0 k)
  · refine ⟨_, Filter.eventually_all.2 fun j => ?_, fun z hz => hz⟩
    by_cases hj : (j : ℕ) < ℓ
    · exact (hYs1 j hj).mono fun z hz _ => hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hj
  · refine ⟨_, Filter.eventually_all.2 fun j => ?_, fun z hz => hz⟩
    by_cases hj : ℓ ≤ (j : ℕ)
    · exact (hYs2 j hj).mono fun z hz _ => hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hj

theorem slideChart_of_frame {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (L : Finset M)
    (hL : ∀ x ∈ L, x ∈ crit ∧ c₂ + κ < g x - ε ∧ morseIndex I g x ≤ ℓ + 1)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγlev : ∀ t ∈ Icc (0 : ℝ) 3, g (γ t) = c₂)
    (hγinj : InjOn γ (Icc 0 3)) (hγimm : ∀ t ∈ Icc (0 : ℝ) 3, mfderiv 𝓘(ℝ, ℝ) I γ t 1 ≠ 0)
    (hγL : ∀ t ∈ Icc (0 : ℝ) 3, γ t ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ t = 1)
    (hγR : ∀ t ∈ Icc (0 : ℝ) 3, γ t ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ t = 2)
    (hγO : ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ → ∀ t ∈ Icc (0 : ℝ) 3,
      γ t ∉ D.leftSphere x hx ε c₂)
    (Ys : Fin (n - 2) → LevelField I g)
    (hframe : ∀ t ∈ Icc (0 : ℝ) 3, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        coordN v 0 • mfderiv 𝓘(ℝ, ℝ) I γ t 1 +
          ∑ j : Fin (n - 2), coordN v (1 + j) • (Ys j).Y (γ t)))
    (hA : ∃ N₁ ∈ 𝓝 (γ 1), ∀ z ∈ N₁, ∀ j : Fin (n - 2), (j : ℕ) < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q₁ hq₁).k))) (D.leftCoord q₁ hq₁ ε) z
          ((Ys j).Y z) = 0)
    (hB : ∃ N₂ ∈ 𝓝 (γ 2), ∀ z ∈ N₂, ∀ j : Fin (n - 2), ℓ ≤ (j : ℕ) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε) z
          ((Ys j).Y z) = 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ Ch : D.CollarChart c₂ κ, D.isSlideChart Ch hq₁ hq₂ ε η ℓ ∧
      (∀ y, Ch.φ y = flowChart 1 (n - 2) Ys (fun s => γ (s 0)) y) ∧
      ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ →
        Disjoint (D.leftSphere x hx ε c₂) (Ch.φ '' slideDom (n - 1) η) := by
  classical
  have _hL := hL
  have _hγimm := hγimm
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hℓ2 : 2 ≤ ℓ := hS.hℓ
  have hℓn : ℓ + 3 ≤ n := hS.hℓn
  have hε : 0 < ε := hS.hε
  have hflow0 : ∀ (Z : LevelField I g) (x : M), Z.flow 0 x = x := fun Z x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hflowC : ∀ (Z : LevelField I g) (x : M), IsMIntegralCurve (fun t => Z.flow t x) Z.Y :=
    fun Z x => DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ x
  have hFL : ∀ (s : ℕ) (G : M → EuclideanSpace ℝ (Fin s)) (R : Set M),
      (∀ z ∈ R, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z) →
      ∀ (r : ℕ) (Z : Fin r → LevelField I g) (t : ℕ → ℝ) (x : M),
      (∀ s' : ℕ → ℝ, (∀ j, s' j ∈ uIcc 0 (t j)) →
        (List.finRange r).foldl (fun x j => (Z j).flow (s' j) x) x ∈ R) →
      (∀ j : Fin r, t j ≠ 0 → ∀ z ∈ R,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z ((Z j).Y z) = 0) →
      G ((List.finRange r).foldl (fun x j => (Z j).flow (t j) x) x) = G x := by
    intro s G R hGR r
    induction r with
    | zero => intro Z t x _ _; simp
    | succ r ih =>
      intro Z t x hreg htan
      have hdec : ∀ t' : ℕ → ℝ,
          (List.finRange (r + 1)).foldl (fun x j => (Z j).flow (t' j) x) x =
            (Z (Fin.last r)).flow (t' r) ((List.finRange r).foldl
              (fun x j => (Z (Fin.castSucc j)).flow (t' j) x) x) := by
        intro t'
        rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
        simp
      have hcongr : ∀ t' t'' : ℕ → ℝ, (∀ j, j < r → t' j = t'' j) →
          (List.finRange r).foldl (fun x j => (Z (Fin.castSucc j)).flow (t' j) x) x =
          (List.finRange r).foldl (fun x j => (Z (Fin.castSucc j)).flow (t'' j) x) x := by
        intro t' t'' h
        apply List.foldl_ext
        intro a j _
        rw [h j j.isLt]
      set z := (List.finRange r).foldl (fun x j => (Z (Fin.castSucc j)).flow (t j) x) x with hz
      have hIH : G z = G x := by
        apply ih (fun j => Z (Fin.castSucc j)) t x
        · intro s' hs'
          have h1 := hreg (Function.update s' r 0) (by
            intro j
            by_cases hj : j = r
            · subst hj; simp
            · rw [Function.update_of_ne hj]; exact hs' j)
          rw [hdec, Function.update_self, hflow0] at h1
          rwa [hcongr (Function.update s' r 0) s'
            (fun j hj => Function.update_of_ne (ne_of_lt hj) _ _)] at h1
        · intro j hj z hz
          exact htan (Fin.castSucc j) (by simpa using hj) z hz
      rw [hdec, ← hz, ← hIH]
      by_cases ht : t r = 0
      · rw [ht, hflow0]
      have htanL := htan (Fin.last r) (by simpa using ht)
      set c : ℝ → M := fun u => (Z (Fin.last r)).flow u z with hc
      have hcR : ∀ u ∈ uIcc 0 (t r), c u ∈ R := by
        intro u hu
        have h1 := hreg (Function.update t r u) (by
          intro j
          by_cases hj : j = r
          · subst hj; simpa using hu
          · rw [Function.update_of_ne hj]; exact right_mem_uIcc)
        rw [hdec, Function.update_self, hcongr (Function.update t r u) t
          (fun j hj => Function.update_of_ne (ne_of_lt hj) _ _)] at h1
        exact h1
      have hderiv : ∀ u ∈ uIcc 0 (t r), HasDerivAt (G ∘ c) 0 u := by
        intro u hu
        have hGd := (hGR _ (hcR u hu)).hasMFDerivAt
        have hcomp := hGd.comp u (hflowC (Z (Fin.last r)) z u)
        have h2 := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
        rw [hasDerivAt_iff_hasFDerivAt]
        refine h2.congr_fderiv ?_
        apply ContinuousLinearMap.ext
        intro w
        have h0 := htanL _ (hcR u hu)
        change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (c u) ((show ℝ from w) • (Z (Fin.last r)).Y (c u)) =
          (ContinuousLinearMap.toSpanSingleton ℝ (0 : EuclideanSpace ℝ (Fin s))) w
        rw [map_smul, h0, smul_zero]
        exact (smul_zero (show ℝ from w)).symm
      have hconst : ∀ u ∈ Icc (0 ⊓ t r) (0 ⊔ t r), (G ∘ c) u = (G ∘ c) (0 ⊓ t r) := by
        apply constant_of_has_deriv_right_zero
        · intro u hu; exact (hderiv u hu).continuousAt.continuousWithinAt
        · intro u hu; exact (hderiv u (Ico_subset_Icc_self hu)).hasDerivWithinAt
      have h0 := hconst 0 left_mem_uIcc
      have h1 := hconst (t r) right_mem_uIcc
      have h3 : (G ∘ c) (t r) = (G ∘ c) 0 := h1.trans h0.symm
      simpa [hc, hflow0] using h3
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin (n - 1) → ℝ) → M,
      Φ = flowChart 1 (n - 2) Ys (fun s => γ (s 0)) := ⟨_, rfl⟩
  have hbase : ContMDiffOn 𝓘(ℝ, Fin 1 → ℝ) I ∞ (fun s : Fin 1 → ℝ => γ (s 0)) univ := by
    have : ContMDiff 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : Fin 1 → ℝ => s 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contMDiff
    exact (hγ.comp this).contMDiffOn
  obtain ⟨hsm, hlev, hder⟩ := flowChart_spec (m := n - 1) hf (show n - 1 = 1 + (n - 2) by omega)
    Ys (fun s => γ (s 0)) isOpen_univ hbase
  have hΦsm : ContMDiff 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ Φ := by
    rw [hΦ, ← contMDiffOn_univ]; simpa using hsm
  have hΦcont : Continuous Φ := hΦsm.continuous
  have hΦlev : ∀ y, g (Φ y) = g (γ (coordN y 0)) := fun y => by rw [hΦ]; exact hlev y
  have hΦfold : ∀ y, Φ y = (List.finRange (n - 2)).foldl
      (fun x j => (Ys j).flow (coordN y (1 + j)) x) (γ (coordN y 0)) := fun y => by
    rw [hΦ]; rfl
  have hcoordc : ∀ j, Continuous (fun y : Fin (n - 1) → ℝ => coordN y j) := by
    intro j
    unfold coordN
    split_ifs with h
    · exact continuous_apply _
    · exact continuous_const
  obtain ⟨lv, hlv⟩ : ∃ lv : ℝ → Fin (n - 1) → ℝ,
      ∀ t (i : Fin (n - 1)), lv t i = if (i : ℕ) = 0 then t else 0 :=
    ⟨fun t i => if (i : ℕ) = 0 then t else 0, fun _ _ => rfl⟩
  have hcoord0 : ∀ t, coordN (lv t) 0 = t := by
    intro t; simp [coordN, hlv, show 0 < n - 1 by omega]
  have hcoordj : ∀ t (j : ℕ), 1 ≤ j → coordN (lv t) j = 0 := by
    intro t j hj
    unfold coordN
    split_ifs with h
    · rw [hlv]; simp; omega
    · rfl
  have hlvc : Continuous lv := by
    apply continuous_pi; intro i; rw [show (fun t => lv t i) = fun t => if (i : ℕ) = 0 then t else 0
      from funext fun t => hlv t i]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have hlvdist : ∀ t t', dist (lv t) (lv t') ≤ |t - t'| := by
    intro t t'
    refine (dist_pi_le_iff (abs_nonneg _)).2 fun i => ?_
    rw [hlv, hlv]
    split_ifs
    · rw [Real.dist_eq]
    · simp
  have hlvinj : Function.Injective lv := by
    intro t t' h
    rw [← hcoord0 t, ← hcoord0 t', h]
  have hfold0 : ∀ (l : List (Fin (n - 2))) (x : M), l.foldl (fun x j => (Ys j).flow 0 x) x = x := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons j l ih => intro x; rw [List.foldl_cons, hflow0]; exact ih x
  have hΦlv : ∀ t, Φ (lv t) = γ t := by
    intro t
    rw [hΦfold, hcoord0]
    have : (fun x (j : Fin (n - 2)) => (Ys j).flow (coordN (lv t) (1 + j)) x) =
        fun x j => (Ys j).flow 0 x := by
      funext x j; rw [hcoordj t _ (by omega)]
    rw [this, hfold0]
  have hbd : ∀ (s w : Fin 1 → ℝ), mfderiv 𝓘(ℝ, Fin 1 → ℝ) I (fun s : Fin 1 → ℝ => γ (s 0)) s w =
      w 0 • mfderiv 𝓘(ℝ, ℝ) I γ (s 0) 1 := by
    intro s w
    have hp : (fun s : Fin 1 → ℝ => γ (s 0)) =
        γ ∘ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) := rfl
    rw [hp, mfderiv_comp s ((hγ (s 0)).mdifferentiableAt (by simp))
      (ContinuousLinearMap.mdifferentiableAt _), ContinuousLinearMap.mfderiv_eq]
    change mfderiv 𝓘(ℝ, ℝ) I γ (s 0) (w 0) = _
    have h1 : (w 0 : ℝ) = w 0 • (1 : ℝ) := (mul_one _).symm
    calc mfderiv 𝓘(ℝ, ℝ) I γ (s 0) (w 0) = mfderiv 𝓘(ℝ, ℝ) I γ (s 0) (w 0 • (1 : ℝ)) := by
          rw [← h1]
      _ = _ := map_smul _ _ _
  have hΦd : ∀ t v, mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t) v =
      coordN v 0 • mfderiv 𝓘(ℝ, ℝ) I γ t 1 + ∑ j : Fin (n - 2), coordN v (1 + j) • (Ys j).Y (γ t) := by
    intro t v
    rw [hΦ, hder (lv t) (mem_univ _) (fun j hj => hcoordj t j hj) v, hbd]
    simp only [Fin.val_zero]
    rw [hcoord0]
    rfl
  have hΦimm : ∀ t ∈ Icc (0 : ℝ) 3,
      Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t)) := by
    intro t ht v w hvw
    apply hframe t ht
    have h1 := hΦd t v
    have h2 := hΦd t w
    simp only
    rw [← h1, ← h2]
    exact hvw
  have hK0c : IsCompact (lv '' Icc (0 : ℝ) 3) := isCompact_Icc.image hlvc
  obtain ⟨U, hUo, hKU, -, hUinj, hUimm⟩ := exists_injOn_nhds_of_immersion (I := I) isOpen_univ
    (hΦsm.contMDiffOn.of_le (by simp)) hK0c (subset_univ _)
    (by rintro _ ⟨t, ht, rfl⟩; exact hΦimm t ht)
    (by
      rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ h
      rw [hΦlv, hΦlv] at h
      rw [hγinj ht ht' h])
  obtain ⟨δU, hδU, hUsub⟩ := hK0c.exists_thickening_subset_open hUo hKU
  have hcoordF' : ∀ (y : Fin (n - 1) → ℝ) (k : Fin (n - 1)), coordN y k = y k := by
    intro y k
    simp [coordN, k.isLt]
  have hdom_open : ∀ η : ℝ, 0 < η → IsOpen (slideDom (n - 1) η) := by
    intro η hη
    have : slideDom (n - 1) η = {y | 0 < coordN y 0} ∩ {y | coordN y 0 < 3} ∩
        ⋂ i : Fin (n - 1), {y | 1 ≤ (i : ℕ) → |y i| < η} := by
      ext y
      simp only [slideDom, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h0, h3, hj⟩
        refine ⟨⟨h0, h3⟩, fun i hi => ?_⟩
        have := hj i hi
        simpa [coordN, i.isLt] using this
      · rintro ⟨⟨h0, h3⟩, hi⟩
        refine ⟨h0, h3, fun j hj => ?_⟩
        unfold coordN
        split_ifs with h
        · exact hi ⟨j, h⟩ hj
        · simpa using hη
    rw [this]
    refine ((isOpen_lt continuous_const (hcoordc 0)).inter
      (isOpen_lt (hcoordc 0) continuous_const)).inter (isOpen_iInter_of_finite fun i => ?_)
    by_cases hi : 1 ≤ (i : ℕ)
    · simp only [hi, true_implies]
      exact isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const
    · simp only [hi, false_implies, ofPred_true]
      exact isOpen_univ
  have hdom_near : ∀ (η : ℝ) (y : Fin (n - 1) → ℝ), y ∈ slideDom (n - 1) η → 0 < η →
      dist y (lv (coordN y 0)) < η := by
    intro η y hy hη
    rw [dist_pi_lt_iff hη]
    intro i
    rw [hlv]
    split_ifs with hi
    · have : coordN y 0 = y i := by
        rw [show (0 : ℕ) = (i : ℕ) from hi.symm, hcoordF']
      rw [this, dist_self]
      exact hη
    · rw [Real.dist_eq, sub_zero]
      have := hy.2.2 i (by omega)
      simpa [coordN, i.isLt] using this
  have hfar : ∀ C : Set M, IsClosed C → ∀ A : Set ℝ, IsCompact A → (∀ t ∈ A, γ t ∉ C) →
      ∃ δ > 0, ∀ y t, t ∈ A → dist y (lv t) < δ → Φ y ∉ C := by
    intro C hC A hA hAC
    obtain ⟨δ, hδ, hsub⟩ := (hA.image hlvc).exists_thickening_subset_open
      (hΦcont.isOpen_preimage _ hC.isOpen_compl)
      (by
        rintro _ ⟨t, ht, rfl⟩
        simp only [mem_preimage, mem_compl_iff, hΦlv]
        exact hAC t ht)
    refine ⟨δ, hδ, fun y t ht hy => ?_⟩
    exact hsub (Metric.mem_thickening_iff.2 ⟨lv t, mem_image_of_mem _ ht, hy⟩)
  have h2R : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 := pow_le_pow_left₀ (D.rm_pos x hx).le (D.hrm x hx).2 2
    linarith
  have hstrip : a ≤ c₂ - κ ∧ c₂ + κ ≤ b :=
    ⟨by linarith [hS.hac, hS.hcq₂, hS.hq₂c₂], by linarith [hS.hc₂q₁, hS.hq₁b]⟩
  have hW : IsOpen (U ∩ {y | coordN y 0 ∈ Ioo (0 : ℝ) 3}) :=
    hUo.inter (isOpen_Ioo.preimage (hcoordc 0))
  have hloc : ∀ y ∈ U ∩ {y | coordN y 0 ∈ Ioo (0 : ℝ) 3}, ∃ U₀ : Set (Fin (n - 1) → ℝ),
      IsOpen U₀ ∧ y ∈ U₀ ∧
      ∀ V ⊆ U₀, IsOpen V → ∃ Ch : D.CollarChart c₂ κ, Ch.U = V ∧ Ch.φ = Φ := by
    intro y hy
    obtain ⟨U₀, hU₀, hyU₀, -, hU₀V⟩ := D.exists_collarChart_of_injOn hf hS.hκ hstrip hS.hmodel Φ hW
      hΦsm.contMDiffOn
      (fun y hy => by rw [hΦlev]; exact hγlev _ (Ioo_subset_Icc_self hy.2)) isCompact_singleton
      (singleton_subset_iff.2 hy) (fun z hz => by rw [mem_singleton_iff.1 hz]; exact hUimm y hy.1) (injOn_singleton _ _)
    exact ⟨U₀, hU₀, hyU₀ rfl, hU₀V⟩
  choose U₀ hU₀o hyU₀ hU₀ch using hloc
  have hLA : ∀ (s : ℕ) (A : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (dg : (Fin n → ℝ) →ₗ[ℝ] ℝ)
      (dG : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin s)), Function.Injective A →
      (∀ u, dg (A u) = 0) → dg ≠ 0 → (∀ w, ∃ v, dg v = 0 ∧ dG v = w) →
      ∀ e : Fin s → Fin (n - 1), Function.Injective e →
      (∀ q, q ∉ Set.range e → dG (A (fun j => if q = j then 1 else 0)) = 0) →
      ∀ v : Fin (n - 1) → ℝ, (∀ q, q ∉ Finset.univ.image e → v q = 0) → dG (A v) = 0 → v = 0 := by
    intro s A dg dG hA hdgA hdg0 hsurj e he hoff v hv hAv
    have hn1 : 1 ≤ n := by omega
    have hle : LinearMap.range A ≤ LinearMap.ker dg := by
      rintro _ ⟨u, rfl⟩
      exact hdgA u
    have hrA : Module.finrank ℝ (LinearMap.range A) = n - 1 := by
      rw [LinearMap.finrank_range_of_inj hA, Module.finrank_fin_fun]
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, dg v₀ ≠ 0 := by
      by_contra h
      exact hdg0 (LinearMap.ext fun v => not_not.1 fun hv => h ⟨v, hv⟩)
    have hdgs : LinearMap.range dg = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨(r / dg v₀) • v₀, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀]
    have hrk := LinearMap.finrank_range_add_finrank_ker dg
    rw [hdgs, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrk
    have heq : LinearMap.range A = LinearMap.ker dg :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hrA]; omega)
    have hLs : ∀ w, ∃ u, dG (A u) = w := by
      intro w
      obtain ⟨v, hv1, hv2⟩ := hsurj w
      have : v ∈ LinearMap.range A := by rw [heq]; exact hv1
      obtain ⟨u, rfl⟩ := this
      exact ⟨u, hv2⟩
    let Lm : (Fin (n - 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin s) := dG ∘ₗ A
    let M' : (Fin s → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin s) :=
      { toFun := fun u => ∑ i, u i • Lm (fun j => if e i = j then 1 else 0)
        map_add' := by
          intro u u'
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro c u
          simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
    have hLmv : ∀ v, Lm v = M' (fun i => v (e i)) := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ Lm v]
      change _ = ∑ i, v (e i) • Lm (fun j => if e i = j then 1 else 0)
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)), Finset.sum_image]
      · intro i _ i' _ h
        exact he h
      · intro q _ hq
        have : q ∉ Set.range e := by
          rintro ⟨i, rfl⟩
          exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ _))
        change v q • dG (A _) = 0
        rw [hoff q this, smul_zero]
    have hMs : Function.Surjective M' := by
      intro w
      obtain ⟨u, hu⟩ := hLs w
      exact ⟨fun i => u (e i), by rw [← hLmv]; exact hu⟩
    have hMi : Function.Injective M' :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).2 hMs
    have hz : (fun i => v (e i)) = 0 := by
      apply hMi
      rw [← hLmv, map_zero]
      exact hAv
    funext q
    by_cases hq : q ∈ Finset.univ.image e
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
      exact congr_fun hz i
    · exact hv q hq
  have hcoordF : ∀ (y : Fin (n - 1) → ℝ) (k : Fin (n - 1)), coordN y k = y k := by
    intro y k
    simp [coordN, k.isLt]
  have habs : ∀ x b : ℝ, x ∈ uIcc 0 b → |x| ≤ |b| := by
    intro x b h
    rcases mem_uIcc.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
      exact h2
    · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
      linarith
  have hblock : ∀ t₀ ∈ Ioo (0 : ℝ) 3, ∀ (s : ℕ) (G : M → EuclideanSpace ℝ (Fin s)) (O : Set M),
      IsOpen O → γ t₀ ∈ O → ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O → G (γ t₀) = 0 →
      mfderiv I 𝓘(ℝ, ℝ) g (γ t₀) ≠ 0 →
      (∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I (γ t₀),
        mfderiv I 𝓘(ℝ, ℝ) g (γ t₀) v = 0 ∧
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t₀) v = w) →
      ∀ e : Fin s → Fin (n - 1), Function.Injective e → (∃ i, (e i : ℕ) = 0) →
      (∃ N ∈ 𝓝 (γ t₀), ∀ z ∈ N, ∀ j : Fin (n - 2), (∀ i, (e i : ℕ) ≠ 1 + j) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z ((Ys j).Y z) = 0) →
      ∀ᶠ y in 𝓝 (lv t₀), (G (Φ y) = 0 ↔ ∀ i, y (e i) = lv t₀ (e i)) := by
    intro t₀ ht₀ s G O hO hγO hGs hG0 hdg hsurj e he he0 hN
    obtain ⟨N, hNn, hNt⟩ := hN
    obtain ⟨i₀, hi₀⟩ := he0
    have hΦp : Φ (lv t₀) = γ t₀ := hΦlv t₀
    have hRo : IsOpen (O ∩ interior N) := hO.inter isOpen_interior
    have hγR : γ t₀ ∈ O ∩ interior N := ⟨hγO, mem_interior_iff_mem_nhds.2 hNn⟩
    have hGR : ∀ z ∈ O ∩ interior N, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z :=
      fun z hz => ((hGs z hz.1).contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)
    have hpre : Φ ⁻¹' (O ∩ interior N) ∈ 𝓝 (lv t₀) :=
      hΦcont.continuousAt.preimage_mem_nhds (by rw [hΦp]; exact hRo.mem_nhds hγR)
    obtain ⟨ρ₀, hρ₀, hρ₀R⟩ := Metric.mem_nhds_iff.1 hpre
    have hP : ∀ᶠ y in 𝓝 (lv t₀), (∀ j ∈ Finset.univ.image e, y j = lv t₀ j) →
        (G ∘ Φ) y = 0 := by
      filter_upwards [Metric.ball_mem_nhds (lv t₀) hρ₀] with y hy hplane
      have hy0 : coordN y 0 = t₀ := by
        have h1 := hplane (e i₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
        have h2 : e i₀ = (⟨0, by omega⟩ : Fin (n - 1)) := Fin.ext hi₀
        rw [h2] at h1
        rw [show (0 : ℕ) = ((⟨0, by omega⟩ : Fin (n - 1)) : ℕ) from rfl, hcoordF, h1, hlv]
        simp
      have hyj : ∀ j : Fin (n - 2), coordN y (1 + j) ≠ 0 → ∀ i, (e i : ℕ) ≠ 1 + j := by
        intro j hj i hi
        apply hj
        have h1 := hplane (e i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
        have h2 : e i = (⟨1 + j, by omega⟩ : Fin (n - 1)) := Fin.ext hi
        rw [h2] at h1
        rw [show 1 + (j : ℕ) = ((⟨1 + j, by omega⟩ : Fin (n - 1)) : ℕ) from rfl, hcoordF, h1, hlv]
        simp
      change G (Φ y) = 0
      rw [hΦfold, hy0]
      refine (hFL s G (O ∩ interior N) hGR (n - 2) Ys (fun k => coordN y (1 + k)) (γ t₀) ?_ ?_).trans
        hG0
      · intro s' hs'
        let y' : Fin (n - 1) → ℝ := fun i => if (i : ℕ) = 0 then t₀ else s' ((i : ℕ) - 1)
        have hy'0 : coordN y' 0 = t₀ := by simp [y', coordN, show 0 < n - 1 by omega]
        have hy'j : ∀ k : ℕ, k < n - 2 → coordN y' (1 + k) = s' k := by
          intro k hk
          simp [y', coordN, show 1 + k < n - 1 by omega]
        have hmem : Φ y' ∈ O ∩ interior N := hρ₀R (by
          rw [Metric.mem_ball, dist_pi_lt_iff hρ₀]
          intro i
          simp only [y', hlv]
          split_ifs with hi
          · rw [dist_self]; exact hρ₀
          · rw [Real.dist_eq, sub_zero]
            have h1 := habs _ _ (hs' ((i : ℕ) - 1))
            have h2 : coordN y (1 + ((i : ℕ) - 1)) = y i := by
              rw [show 1 + ((i : ℕ) - 1) = (i : ℕ) by omega, hcoordF]
            simp only [h2] at h1
            have h3 := (dist_pi_lt_iff hρ₀).1 (Metric.mem_ball.1 hy) i
            simp only [hlv, hi, ↓reduceIte, Real.dist_eq, sub_zero] at h3
            linarith)
        rw [hΦfold, hy'0] at hmem
        have hfun : (fun x (j : Fin (n - 2)) => (Ys j).flow (coordN y' (1 + j)) x) =
            fun x j => (Ys j).flow (s' j) x := by
          funext x j
          rw [hy'j j j.isLt]
        rw [hfun] at hmem
        exact hmem
      · intro j hj z hz
        exact hNt z (interior_subset hz.2) j (hyj j hj)
    have hF : ContDiffAt ℝ 1 (G ∘ Φ) (lv t₀) := by
      have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G (Φ (lv t₀)) := by
        rw [hΦp]; exact (hGs _ hγO).contMDiffAt (hO.mem_nhds hγO)
      exact (contMDiffAt_iff_contDiffAt.1 (h1.comp (lv t₀) (hΦsm (lv t₀)))).of_le (by simp)
    have hinj : ∀ v : Fin (n - 1) → ℝ, (∀ j, j ∉ Finset.univ.image e → v j = 0) →
        fderiv ℝ (G ∘ Φ) (lv t₀) v = 0 → v = 0 := by
      intro v hv hFv
      have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (lv t₀)) := by
        rw [hΦp]; exact hGR _ hγR
      have hΦdiff : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t₀) :=
        (hΦsm (lv t₀)).mdifferentiableAt (by simp)
      have hcomp : fderiv ℝ (G ∘ Φ) (lv t₀) v =
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (lv t₀))
            (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t₀) v) := by
        have hc := mfderiv_comp (lv t₀) hGd hΦdiff
        rw [mfderiv_eq_fderiv] at hc
        exact DFunLike.congr_fun hc v
      have hgd : MDifferentiableAt I 𝓘(ℝ, ℝ) g (Φ (lv t₀)) := (hf _).mdifferentiableAt (by simp)
      have hloc : (g ∘ Φ) =ᶠ[𝓝 (lv t₀)] fun _ => c₂ := by
        have : ∀ᶠ y in 𝓝 (lv t₀), coordN y 0 ∈ Ioo (0 : ℝ) 3 :=
          (hcoordc 0).continuousAt.preimage_mem_nhds (by rw [hcoord0]; exact isOpen_Ioo.mem_nhds ht₀)
        filter_upwards [this] with y hy
        simp only [Function.comp_apply]
        rw [hΦlev]
        exact hγlev _ (Ioo_subset_Icc_self hy)
      have hdgA : ∀ u, mfderiv I 𝓘(ℝ, ℝ) g (Φ (lv t₀))
          (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t₀) u) = 0 := by
        intro u
        have h1 := mfderiv_comp (lv t₀) hgd hΦdiff
        rw [hloc.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero] at h1
        have h2 := DFunLike.congr_fun h1 u
        exact h2.symm
      rw [← hΦp] at hsurj hdg
      refine hLA s (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t₀)).toLinearMap
        (mfderiv I 𝓘(ℝ, ℝ) g (Φ (lv t₀))).toLinearMap
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (lv t₀))).toLinearMap
        (hΦimm t₀ (Ioo_subset_Icc_self ht₀)) hdgA ?_ hsurj e he ?_ v hv (by rw [hcomp] at hFv; exact hFv)
      · intro h
        apply hdg
        exact ContinuousLinearMap.coe_injective h
      · intro q hq
        have hq0 : (q : ℕ) ≠ 0 := by
          intro h
          apply hq
          exact ⟨i₀, Fin.ext (hi₀.trans h.symm)⟩
        have hqlt : (q : ℕ) - 1 < n - 2 := by omega
        have htan : ∀ i, (e i : ℕ) ≠ 1 + ((q : ℕ) - 1) := by
          intro i hi
          apply hq
          exact ⟨i, Fin.ext (by rw [hi]; omega)⟩
        change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (lv t₀))
          (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (lv t₀) (fun j => if q = j then 1 else 0)) = 0
        refine (congrArg (fun w => mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (lv t₀)) w)
          (hΦd t₀ (fun j => if q = j then (1 : ℝ) else 0))).trans ?_
        have hc0 : coordN (fun j : Fin (n - 1) => if q = j then (1 : ℝ) else 0) 0 = 0 := by
          have h0 : 0 < n - 1 := by omega
          have hne : q ≠ ⟨0, h0⟩ := fun h => hq0 (by rw [h])
          simp only [coordN, h0, ↓reduceDIte, hne, ↓reduceIte]
        have hcj : ∀ j : Fin (n - 2), coordN (fun j : Fin (n - 1) => if q = j then (1 : ℝ) else 0)
            (1 + j) = if j = ⟨(q : ℕ) - 1, hqlt⟩ then 1 else 0 := by
          intro j
          have h1 : 1 + (j : ℕ) < n - 1 := by omega
          have hiff : q = ⟨1 + j, h1⟩ ↔ j = ⟨(q : ℕ) - 1, hqlt⟩ := by
            constructor
            · intro h
              apply Fin.ext
              change (j : ℕ) = (q : ℕ) - 1
              rw [h]
              change (j : ℕ) = 1 + (j : ℕ) - 1
              omega
            · intro h
              apply Fin.ext
              change (q : ℕ) = 1 + (j : ℕ)
              rw [h]
              change (q : ℕ) = 1 + ((q : ℕ) - 1)
              omega
          simp only [coordN, h1, ↓reduceDIte, hiff]
        simp only [hc0, zero_smul, zero_add, hcj, ite_smul, one_smul]
        rw [Finset.sum_ite_eq' Finset.univ (⟨(q : ℕ) - 1, hqlt⟩ : Fin (n - 2))]
        simp only [Finset.mem_univ, ↓reduceIte]
        have h1 := hNt (Φ (lv t₀)) (by rw [hΦp]; exact mem_of_mem_nhds hNn) ⟨(q : ℕ) - 1, hqlt⟩ htan
        have h2 : (Ys ⟨(q : ℕ) - 1, hqlt⟩).Y (Φ (lv t₀)) = (Ys ⟨(q : ℕ) - 1, hqlt⟩).Y (γ t₀) := by
          rw [hΦp]
        rw [h2] at h1
        exact h1
    filter_upwards [zero_set_eq_of_fderiv (G ∘ Φ) (lv t₀) hF (Finset.univ.image e) hP hinj]
      with y hy
    rw [show G (Φ y) = (G ∘ Φ) y from rfl, hy]
    simp
  have hlev0 : ∀ t₀ ∈ Ioo (0 : ℝ) 3, ∀ᶠ y in 𝓝 (lv t₀), g (Φ y) = c₂ := by
    intro t₀ ht₀
    have : ∀ᶠ y in 𝓝 (lv t₀), coordN y 0 ∈ Ioo (0 : ℝ) 3 :=
      (hcoordc 0).continuousAt.preimage_mem_nhds (by rw [hcoord0]; exact isOpen_Ioo.mem_nhds ht₀)
    filter_upwards [this] with y hy
    rw [hΦlev]
    exact hγlev _ (Ioo_subset_Icc_self hy)
  have hLnear : ∃ ρ > 0, ∀ y, dist y (lv 1) < ρ →
      (Φ y ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ y ∈ slideA (n - 1) ℓ) := by
    have hk : (D.chart q₁ hq₁).k = ℓ + 1 := hS.hk₁
    have h1I : (1 : ℝ) ∈ Ioo (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
    have hγ1 : γ 1 ∈ D.leftSphere q₁ hq₁ ε c₂ := (hγL 1 (Ioo_subset_Icc_self h1I)).2 rfl
    have hrm : 2 * ε < D.rm q₁ hq₁ ^ 2 := by linarith [(hS.hεr q₁ hq₁).2]
    have hac : a ≤ c₂ := by linarith [hS.hac, hS.hcq₂, hS.hq₂c₂, hS.hκ]
    have hcq : c₂ ≤ g q₁ - ε := by linarith [hS.hc₂q₁, hS.hκ]
    have hU : ∀ y, g y ∈ Icc c₂ (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
      hS.hunit y (Or.inr ⟨by linarith [hy.1, hS.hq₂c₂, hS.hκ], hy.2⟩)
    obtain ⟨O, hO, hSO, hGs, hsub⟩ := leftCoord_submersion hf D hq₁ hε hrm hac hcq hU
    obtain ⟨hL0, hLball⟩ :=
      (mem_leftSphere_iff_coord hf D hq₁ hε hrm hac hcq hU (hγlev 1 (Ioo_subset_Icc_self h1I))).1 hγ1
    have hs : n - (D.chart q₁ hq₁).k + ℓ + 1 = n := by omega
    let e : Fin (n - (D.chart q₁ hq₁).k) → Fin (n - 1) :=
      fun i => ⟨if (i : ℕ) = 0 then 0 else i + ℓ, by split_ifs <;> omega⟩
    have he : Function.Injective e := by
      intro i i' h
      have h' := congrArg Fin.val h
      simp only [e] at h'
      apply Fin.ext
      split_ifs at h' <;> omega
    have htan : ∃ N ∈ 𝓝 (γ 1), ∀ z ∈ N, ∀ j : Fin (n - 2), (∀ i, (e i : ℕ) ≠ 1 + j) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q₁ hq₁).k))) (D.leftCoord q₁ hq₁ ε) z
          ((Ys j).Y z) = 0 := by
      obtain ⟨N₁, hN₁, hA'⟩ := hA
      refine ⟨N₁, hN₁, fun z hz j hj => hA' z hz j ?_⟩
      by_contra hjl
      apply hj ⟨1 + j - ℓ, by omega⟩
      simp only [e]
      split_ifs <;> omega
    have hblk := hblock 1 h1I _ (D.leftCoord q₁ hq₁ ε) O hO (hSO hγ1) hGs hL0 (hsub _ hγ1).1
      (hsub _ hγ1).2 e he ⟨⟨0, by omega⟩, by simp [e]⟩ htan
    have hball : ∀ᶠ y in 𝓝 (lv 1), D.flow (c₂ - (g q₁ - ε)) (Φ y) ∈
        (D.chart q₁ hq₁).χ '' {w | morseNorm n w < D.rm q₁ hq₁} := by
      have hopen := (D.chart q₁ hq₁).isOpen_image_of_lt (D.rm_lt_R' q₁ hq₁).le
      have hc : ContinuousAt (fun y => D.flow (c₂ - (g q₁ - ε)) (Φ y)) (lv 1) :=
        ((D.continuous_flow _).comp hΦcont).continuousAt
      exact hc.preimage_mem_nhds (hopen.mem_nhds (by simp only [hΦlv]; exact hLball))
    have hev : ∀ᶠ y in 𝓝 (lv 1), (Φ y ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ y ∈ slideA (n - 1) ℓ) := by
      filter_upwards [hblk, hball, hlev0 1 h1I] with y hy1 hy2 hy3
      rw [mem_leftSphere_iff_coord hf D hq₁ hε hrm hac hcq hU hy3, and_iff_left hy2, hy1]
      change (∀ i, y (e i) = lv 1 (e i)) ↔ coordN y 0 = 1 ∧ ∀ j, ℓ + 1 ≤ j → coordN y j = 0
      constructor
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · have h1 := h ⟨0, by omega⟩
          have hv : ((e ⟨0, by omega⟩ : Fin (n - 1)) : ℕ) = 0 := by simp [e]
          have hc := hcoordF y (e ⟨0, by omega⟩)
          rw [hv] at hc
          rw [hc, h1, hlv]
          simp only [hv, ↓reduceIte]
        · by_cases hjn : j < n - 1
          · have h1 := h ⟨j - ℓ, by omega⟩
            have hv : ((e ⟨j - ℓ, by omega⟩ : Fin (n - 1)) : ℕ) = j := by
              change (if j - ℓ = 0 then 0 else j - ℓ + ℓ) = j
              split_ifs <;> omega
            have hc := hcoordF y (e ⟨j - ℓ, by omega⟩)
            rw [hv] at hc
            rw [hc, h1, hlv]
            simp only [hv, show j ≠ 0 by omega, ↓reduceIte]
          · simp [coordN, hjn]
      · rintro ⟨h0, hj⟩ i
        have hc := hcoordF y (e i)
        rw [hlv]
        by_cases hi : (i : ℕ) = 0
        · have hv : ((e i : Fin (n - 1)) : ℕ) = 0 := by
            change (if (i : ℕ) = 0 then 0 else (i : ℕ) + ℓ) = 0
            simp [hi]
          rw [hv] at hc
          simp only [hv, ↓reduceIte]
          rw [← hc, h0]
        · have hv : ((e i : Fin (n - 1)) : ℕ) = i + ℓ := by
            change (if (i : ℕ) = 0 then 0 else (i : ℕ) + ℓ) = i + ℓ
            simp [hi]
          rw [hv] at hc
          simp only [hv, show (i : ℕ) + ℓ ≠ 0 by omega, ↓reduceIte]
          rw [← hc, hj _ (by omega)]
    obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ρ, hρ, fun y hy => hρs hy⟩
  have hRnear : ∃ ρ > 0, ∀ y, dist y (lv 2) < ρ →
      (Φ y ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ y ∈ slideB (n - 1) ℓ) := by
    have hk : (D.chart q₂ hq₂).k = ℓ + 1 := hS.hk₂
    have h2I : (2 : ℝ) ∈ Ioo (0 : ℝ) 3 := ⟨by norm_num, by norm_num⟩
    have hγ2 : γ 2 ∈ D.rightSphere q₂ hq₂ ε c₂ := (hγR 2 (Ioo_subset_Icc_self h2I)).2 rfl
    have hrm : 2 * ε < D.rm q₂ hq₂ ^ 2 := by linarith [(hS.hεr q₂ hq₂).2]
    have hcq : g q₂ + ε ≤ c₂ := by linarith [hS.hq₂c₂, hS.hκ]
    have hcb : c₂ ≤ b := by linarith [hS.hc₂q₁, hS.hq₁b, hS.hκ]
    have hU : ∀ y, g y ∈ Icc (g q₂ + ε) c₂ → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
      hS.hunit y (Or.inr ⟨hy.1, by linarith [hy.2, hS.hc₂q₁, hS.hκ]⟩)
    obtain ⟨O, hO, hSO, hGs, hsub⟩ := rightCoord_submersion hf D hq₂ hε hrm hcq hcb hU
    obtain ⟨hR0, hRball⟩ :=
      (mem_rightSphere_iff_coord hf D hq₂ hε hrm hcq hcb hU (hγlev 2 (Ioo_subset_Icc_self h2I))).1 hγ2
    let e : Fin (D.chart q₂ hq₂).k → Fin (n - 1) := fun i => ⟨i, by omega⟩
    have he : Function.Injective e := by
      intro i i' h
      have h' := congrArg Fin.val h
      exact Fin.ext h'
    have htan : ∃ N ∈ 𝓝 (γ 2), ∀ z ∈ N, ∀ j : Fin (n - 2), (∀ i, (e i : ℕ) ≠ 1 + j) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q₂ hq₂).k)) (D.rightCoord q₂ hq₂ ε) z
          ((Ys j).Y z) = 0 := by
      obtain ⟨N₂, hN₂, hB'⟩ := hB
      refine ⟨N₂, hN₂, fun z hz j hj => hB' z hz j ?_⟩
      by_contra hjl
      exact hj ⟨1 + j, by omega⟩ rfl
    have hblk := hblock 2 h2I _ (D.rightCoord q₂ hq₂ ε) O hO (hSO hγ2) hGs hR0 (hsub _ hγ2).1
      (hsub _ hγ2).2 e he ⟨⟨0, by omega⟩, rfl⟩ htan
    have hball : ∀ᶠ y in 𝓝 (lv 2), D.flow (c₂ - (g q₂ + ε)) (Φ y) ∈
        (D.chart q₂ hq₂).χ '' {w | morseNorm n w < D.rm q₂ hq₂} := by
      have hopen := (D.chart q₂ hq₂).isOpen_image_of_lt (D.rm_lt_R' q₂ hq₂).le
      have hc : ContinuousAt (fun y => D.flow (c₂ - (g q₂ + ε)) (Φ y)) (lv 2) :=
        ((D.continuous_flow _).comp hΦcont).continuousAt
      exact hc.preimage_mem_nhds (hopen.mem_nhds (by simp only [hΦlv]; exact hRball))
    have hev : ∀ᶠ y in 𝓝 (lv 2), (Φ y ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ y ∈ slideB (n - 1) ℓ) := by
      filter_upwards [hblk, hball, hlev0 2 h2I] with y hy1 hy2 hy3
      rw [mem_rightSphere_iff_coord hf D hq₂ hε hrm hcq hcb hU hy3, and_iff_left hy2, hy1]
      change (∀ i, y (e i) = lv 2 (e i)) ↔
        coordN y 0 = 2 ∧ ∀ j, 1 ≤ j → j ≤ ℓ → coordN y j = 0
      constructor
      · intro h
        refine ⟨?_, fun j hj1 hj2 => ?_⟩
        · have h1 := h ⟨0, by omega⟩
          have hc := hcoordF y (e ⟨0, by omega⟩)
          change coordN y 0 = y (e ⟨0, by omega⟩) at hc
          rw [hc, h1, hlv]
          rfl
        · have h1 := h ⟨j, by omega⟩
          have hc := hcoordF y (e ⟨j, by omega⟩)
          change coordN y j = y (e ⟨j, by omega⟩) at hc
          rw [hc, h1, hlv]
          simp only [show ((e ⟨j, by omega⟩ : Fin (n - 1)) : ℕ) = j from rfl,
            show j ≠ 0 by omega, ↓reduceIte]
      · rintro ⟨h0, hj⟩ i
        have hc := hcoordF y (e i)
        change coordN y i = y (e i) at hc
        rw [hlv]
        by_cases hi : (i : ℕ) = 0
        · simp only [show ((e i : Fin (n - 1)) : ℕ) = i from rfl, hi, ↓reduceIte]
          rw [← hc, hi, h0]
        · simp only [show ((e i : Fin (n - 1)) : ℕ) = i from rfl, hi, ↓reduceIte]
          rw [← hc, hj _ (by omega) (by omega)]
    obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ρ, hρ, fun y hy => hρs hy⟩
  obtain ⟨ρL, hρL, hLn⟩ := hLnear
  obtain ⟨ρR, hρR, hRn⟩ := hRnear
  obtain ⟨δL, hδL, hLf⟩ := hfar _ (D.isCompact_leftSphere q₁ hq₁ (h2R q₁ hq₁) c₂).isClosed
    (Icc 0 3 \ Ioo (1 - ρL / 2) (1 + ρL / 2)) (isCompact_Icc.diff isOpen_Ioo)
    (fun t ht h => by
      have := (hγL t ht.1).1 h
      subst this
      exact ht.2 ⟨by linarith, by linarith⟩)
  obtain ⟨δR, hδR, hRf⟩ := hfar _ (D.isCompact_rightSphere q₂ hq₂ (h2R q₂ hq₂) c₂).isClosed
    (Icc 0 3 \ Ioo (2 - ρR / 2) (2 + ρR / 2)) (isCompact_Icc.diff isOpen_Ioo)
    (fun t ht h => by
      have := (hγR t ht.1).1 h
      subst this
      exact ht.2 ⟨by linarith, by linarith⟩)
  obtain ⟨δO, hδO, hOf⟩ := hfar
    (⋃ x ∈ L, ⋃ (hx : x ∈ crit), ⋃ (_ : x ≠ q₁), D.leftSphere x hx ε c₂)
    (isClosed_biUnion_finset fun x _ => isClosed_iUnion_of_finite fun hx =>
      isClosed_iUnion_of_finite fun _ => (D.isCompact_leftSphere x hx (h2R x hx) c₂).isClosed)
    (Icc 0 3) isCompact_Icc
    (fun t ht h => by
      simp only [mem_iUnion] at h
      obtain ⟨x, hxL, hx, hxq, hmem⟩ := h
      exact hγO x hx hxL hxq t ht hmem)
  set η := min (min (ρL / 2) (ρR / 2)) (min (min δL δR) (min δO δU)) with hη
  have hηpos : 0 < η := by
    simp only [hη, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨hδL, hδR⟩, hδO, hδU⟩
  have hηL : η ≤ ρL / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hηR : η ≤ ρR / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηδL : η ≤ δL := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηδR : η ≤ δR := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηδO : η ≤ δO := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηδU : η ≤ δU := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdomW : slideDom (n - 1) η ⊆ U ∩ {y | coordN y 0 ∈ Ioo (0 : ℝ) 3} := by
    intro y hy
    refine ⟨hUsub (Metric.mem_thickening_iff.2 ⟨lv (coordN y 0),
      mem_image_of_mem _ ⟨hy.1.le, hy.2.1.le⟩, (hdom_near η y hy hηpos).trans_le hηδU⟩),
      hy.1, hy.2.1⟩
  obtain ⟨Ch, hChU, hChφ⟩ : ∃ Ch : D.CollarChart c₂ κ, Ch.U = slideDom (n - 1) η ∧ Ch.φ = Φ := by
    refine ⟨⟨slideDom (n - 1) η, hdom_open η hηpos, Φ,
      hΦsm.contMDiffOn, fun y hy => hUimm y (hdomW hy).1,
      hUinj.mono (fun y hy => (hdomW hy).1),
      fun y hy => by rw [hΦlev]; exact hγlev _ ⟨hy.1.le, hy.2.1.le⟩,
      ?_, hS.hκ, hstrip, ?_⟩, rfl, rfl⟩
    · intro V hV hVo
      have hG : ∀ y (hy : y ∈ V), ∃ G : Set M, IsOpen G ∧
          Φ '' (V ∩ U₀ y (hdomW (hV hy))) = G ∩ g ⁻¹' {c₂} := by
        intro y hy
        obtain ⟨Ch', hCh'U, hCh'φ⟩ := hU₀ch y (hdomW (hV hy)) (V ∩ U₀ y (hdomW (hV hy)))
          inter_subset_right (hVo.inter (hU₀o _ _))
        obtain ⟨G, hGo, hG⟩ := Ch'.open_image (V ∩ U₀ y (hdomW (hV hy)))
          (by rw [hCh'U]) (hVo.inter (hU₀o _ _))
        exact ⟨G, hGo, by rw [← hG, hCh'φ]⟩
      choose G hGo hGeq using hG
      refine ⟨⋃ y, ⋃ hy : y ∈ V, G y hy, isOpen_iUnion fun y => isOpen_iUnion fun hy => hGo y hy, ?_⟩
      ext z
      simp only [mem_image, mem_inter_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : Φ y ∈ Φ '' (V ∩ U₀ y (hdomW (hV hy))) := mem_image_of_mem _ ⟨hy, hyU₀ y (hdomW (hV hy))⟩
        rw [hGeq y hy] at this
        exact ⟨⟨y, hy, this.1⟩, this.2⟩
      · rintro ⟨⟨y, hy, hzG⟩, hz⟩
        have : z ∈ G y hy ∩ g ⁻¹' {c₂} := ⟨hzG, hz⟩
        rw [← hGeq y hy] at this
        obtain ⟨y', hy', rfl⟩ := this
        exact ⟨y', hy'.1, rfl⟩
    · intro y hy s hs x hx
      obtain ⟨Ch', hCh'U, hCh'φ⟩ := hU₀ch y (hdomW hy) (U₀ y (hdomW hy)) subset_rfl (hU₀o _ _)
      have := Ch'.avoid y (by rw [hCh'U]; exact hyU₀ _ _) s hs x hx
      rwa [hCh'φ] at this
  have hdist1 : ∀ y ∈ slideDom (n - 1) η, ∀ t₀, dist y (lv t₀) < η + |coordN y 0 - t₀| := by
    intro y hy t₀
    calc dist y (lv t₀) ≤ dist y (lv (coordN y 0)) + dist (lv (coordN y 0)) (lv t₀) :=
          dist_triangle _ _ _
      _ < η + |coordN y 0 - t₀| := add_lt_add_of_lt_of_le (hdom_near η y hy hηpos) (hlvdist _ _)
  refine ⟨η, hηpos, Ch, ⟨hChU, ?_, ?_⟩, fun y => by rw [hChφ, hΦ], ?_⟩
  · intro y hy
    rw [hChφ]
    by_cases hnear : dist y (lv 1) < ρL
    · exact hLn y hnear
    · have ht : coordN y 0 ∉ Ioo (1 - ρL / 2) (1 + ρL / 2) := by
        intro ht
        apply hnear
        have := hdist1 y hy 1
        have h2 : |coordN y 0 - 1| < ρL / 2 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
        linarith
      constructor
      · intro h
        exact absurd h (hLf y (coordN y 0) ⟨⟨hy.1.le, hy.2.1.le⟩, ht⟩
          ((hdom_near η y hy hηpos).trans_le hηδL))
      · intro h
        exfalso
        apply ht
        rw [h.1]
        constructor <;> linarith
  · intro y hy
    rw [hChφ]
    by_cases hnear : dist y (lv 2) < ρR
    · exact hRn y hnear
    · have ht : coordN y 0 ∉ Ioo (2 - ρR / 2) (2 + ρR / 2) := by
        intro ht
        apply hnear
        have := hdist1 y hy 2
        have h2 : |coordN y 0 - 2| < ρR / 2 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
        linarith
      constructor
      · intro h
        exact absurd h (hRf y (coordN y 0) ⟨⟨hy.1.le, hy.2.1.le⟩, ht⟩
          ((hdom_near η y hy hηpos).trans_le hηδR))
      · intro h
        exfalso
        apply ht
        rw [h.1]
        constructor <;> linarith
  · intro x hx hxL hxq
    rw [Set.disjoint_right]
    rintro _ ⟨y, hy, rfl⟩ hmem
    rw [hChφ] at hmem
    apply hOf y (coordN y 0) ⟨hy.1.le, hy.2.1.le⟩ ((hdom_near η y hy hηpos).trans_le hηδO)
    simp only [mem_iUnion]
    exact ⟨x, hxL, hx, hxq, hmem⟩

theorem exists_slideChart {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (L : Finset M)
    (hL : ∀ x ∈ L, x ∈ crit ∧ c₂ + κ < g x - ε ∧ morseIndex I g x ≤ ℓ + 1)
    (hLR : ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ →
      Disjoint (D.leftSphere x hx ε c₂) (D.rightSphere q₂ hq₂ ε c₂))
    (hpc : PathConnectedSpace ↥(g ⁻¹' {c₂})) :
    ∃ η : ℝ, 0 < η ∧ ∃ Ch : D.CollarChart c₂ κ, D.isSlideChart Ch hq₁ hq₂ ε η ℓ ∧
      ∀ x (hx : x ∈ crit), x ∈ L → x ≠ q₁ →
        Disjoint (D.leftSphere x hx ε c₂) (Ch.φ '' slideDom (n - 1) η) := by
  obtain ⟨δ, hδ, hδlev, hδ0, hδ1, hδint, hδL⟩ := exists_level_path hg D hq₁ hq₂ hS L hL hLR hpc
  obtain ⟨γ, hγ, hγlev, hγinj, hγimm, hγL, hγR, hγO, ht1, ht2⟩ :=
    exists_level_arc hg D hq₁ hq₂ hS L hL δ hδ hδlev hδ0 hδ1 hδint hδL
  have hγ1 : γ 1 ∈ D.leftSphere q₁ hq₁ ε c₂ :=
    (hγL 1 ⟨by norm_num, by norm_num⟩).mpr rfl
  have hγ2 : γ 2 ∈ D.rightSphere q₂ hq₂ ε c₂ :=
    (hγR 2 ⟨by norm_num, by norm_num⟩).mpr rfl
  obtain ⟨Ys, hframe, hA, hB⟩ :=
    exists_arcFrame hg D hq₁ hq₂ hS γ hγ hγlev hγinj hγimm hγ1 hγ2 ht1 ht2
  obtain ⟨η, hη, Ch, hCh, -, hdis⟩ :=
    slideChart_of_frame hg D hq₁ hq₂ hS L hL γ hγ hγlev hγinj hγimm hγL hγR hγO Ys hframe hA hB
  exact ⟨η, hη, Ch, hCh, hdis⟩

theorem CollarChart.exists_twist (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D : GradientLikeStrip I f a b crit} {c₂ κ : ℝ} (Ch : D.CollarChart c₂ κ) {q₁ q₂ : M}
    {hq₁ : q₁ ∈ crit} {hq₂ : q₂ ∈ crit} {ε η : ℝ} {ℓ : ℕ} (hη : 0 < η) (hn : ℓ + 3 ≤ n)
    (hℓ : 1 ≤ ℓ) (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) :
    ∃ Ch₂ : D.CollarChart c₂ κ, D.isSlideChart Ch₂ hq₁ hq₂ ε (η / 2) ℓ ∧
      ∀ y, Ch₂.φ y = Ch.φ (slideTwist (n - 1) y) := by
  classical
  have _hf := hf
  have hm3 : 3 ≤ n - 1 := by omega
  let θ : (Fin (n - 1) → ℝ) → ℝ := fun y =>
    Real.pi * Real.smoothTransition (3 * coordN y 0 - 4)
  let G : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ) := fun y i =>
    if (i : ℕ) = 1 then Real.cos (θ y) * coordN y 1 + Real.sin (θ y) * coordN y (n - 1 - 1)
    else if (i : ℕ) = n - 1 - 1 then
      -(Real.sin (θ y) * coordN y 1) + Real.cos (θ y) * coordN y (n - 1 - 1)
    else y i
  have hTdef : ∀ y, slideTwist (n - 1) y = fun i : Fin (n - 1) =>
      if (i : ℕ) = 1 then Real.cos (θ y) * coordN y 1 - Real.sin (θ y) * coordN y (n - 1 - 1)
      else if (i : ℕ) = n - 1 - 1 then
        Real.sin (θ y) * coordN y 1 + Real.cos (θ y) * coordN y (n - 1 - 1)
      else y i := fun y => rfl
  have hc1 : (1 : ℕ) < n - 1 := by omega
  have hcm : n - 1 - 1 < n - 1 := by omega
  have h1m : (1 : ℕ) ≠ n - 1 - 1 := by omega
  have hT1 : ∀ y, coordN (slideTwist (n - 1) y) 1 =
      Real.cos (θ y) * coordN y 1 - Real.sin (θ y) * coordN y (n - 1 - 1) := by
    intro y
    rw [hTdef]
    simp [coordN, hc1]
  have hTm : ∀ y, coordN (slideTwist (n - 1) y) (n - 1 - 1) =
      Real.sin (θ y) * coordN y 1 + Real.cos (θ y) * coordN y (n - 1 - 1) := by
    intro y
    rw [hTdef]
    simp [coordN, hcm, Ne.symm h1m]
  have hTj : ∀ y j, j ≠ 1 → j ≠ n - 1 - 1 → coordN (slideTwist (n - 1) y) j = coordN y j := by
    intro y j hj1 hjm
    rw [hTdef]
    unfold coordN
    split_ifs <;> simp_all
  have hG1 : ∀ y, coordN (G y) 1 =
      Real.cos (θ y) * coordN y 1 + Real.sin (θ y) * coordN y (n - 1 - 1) := by
    intro y
    simp [G, coordN, hc1]
  have hGm : ∀ y, coordN (G y) (n - 1 - 1) =
      -(Real.sin (θ y) * coordN y 1) + Real.cos (θ y) * coordN y (n - 1 - 1) := by
    intro y
    simp [G, coordN, hcm, Ne.symm h1m]
  have hGj : ∀ y j, j ≠ 1 → j ≠ n - 1 - 1 → coordN (G y) j = coordN y j := by
    intro y j hj1 hjm
    simp only [G]
    unfold coordN
    split_ifs <;> simp_all
  have hT0 : ∀ y, coordN (slideTwist (n - 1) y) 0 = coordN y 0 :=
    fun y => hTj y 0 (by omega) (by omega)
  have hG0 : ∀ y, coordN (G y) 0 = coordN y 0 :=
    fun y => hGj y 0 (by omega) (by omega)
  have hθT : ∀ y, θ (slideTwist (n - 1) y) = θ y := fun y => by simp only [θ, hT0]
  have hθG : ∀ y, θ (G y) = θ y := fun y => by simp only [θ, hG0]
  have hext : ∀ u v : Fin (n - 1) → ℝ, (∀ j, coordN u j = coordN v j) → u = v := by
    intro u v h
    funext i
    have := h i.val
    simpa [coordN, i.isLt] using this
  have hGT : ∀ y, G (slideTwist (n - 1) y) = y := by
    intro y
    apply hext
    intro j
    by_cases hj1 : j = 1
    · subst hj1
      rw [hG1, hθT, hT1, hTm]
      have := Real.sin_sq_add_cos_sq (θ y)
      linear_combination (coordN y 1) * this
    · by_cases hjm : j = n - 1 - 1
      · subst hjm
        rw [hGm, hθT, hT1, hTm]
        have := Real.sin_sq_add_cos_sq (θ y)
        linear_combination (coordN y (n - 1 - 1)) * this
      · rw [hGj _ _ hj1 hjm, hTj _ _ hj1 hjm]
  have hTG : ∀ y, slideTwist (n - 1) (G y) = y := by
    intro y
    apply hext
    intro j
    by_cases hj1 : j = 1
    · subst hj1
      rw [hT1, hθG, hG1, hGm]
      have := Real.sin_sq_add_cos_sq (θ y)
      linear_combination (coordN y 1) * this
    · by_cases hjm : j = n - 1 - 1
      · subst hjm
        rw [hTm, hθG, hG1, hGm]
        have := Real.sin_sq_add_cos_sq (θ y)
        linear_combination (coordN y (n - 1 - 1)) * this
      · rw [hTj _ _ hj1 hjm, hGj _ _ hj1 hjm]
  have hcoord : ∀ j, ContDiff ℝ ∞ (fun y : Fin (n - 1) → ℝ => coordN y j) := by
    intro j
    unfold coordN
    split_ifs
    · exact contDiff_apply ℝ ℝ _
    · exact contDiff_const
  have hθs : ContDiff ℝ ∞ θ :=
    contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (hcoord 0)).sub contDiff_const))
  have hTs : ContDiff ℝ ∞ (slideTwist (n - 1)) := by
    rw [contDiff_pi]
    intro i
    simp only [hTdef]
    split_ifs
    · exact ((Real.contDiff_cos.comp hθs).mul (hcoord 1)).sub
        ((Real.contDiff_sin.comp hθs).mul (hcoord _))
    · exact ((Real.contDiff_sin.comp hθs).mul (hcoord 1)).add
        ((Real.contDiff_cos.comp hθs).mul (hcoord _))
    · exact contDiff_apply ℝ ℝ _
  have hGs : ContDiff ℝ ∞ G := by
    rw [contDiff_pi]
    intro i
    simp only [G]
    split_ifs
    · exact ((Real.contDiff_cos.comp hθs).mul (hcoord 1)).add
        ((Real.contDiff_sin.comp hθs).mul (hcoord _))
    · exact ((Real.contDiff_sin.comp hθs).mul (hcoord 1)).neg.add
        ((Real.contDiff_cos.comp hθs).mul (hcoord _))
    · exact contDiff_apply ℝ ℝ _
  have hmaps : ∀ y ∈ slideDom (n - 1) (η / 2), slideTwist (n - 1) y ∈ slideDom (n - 1) η := by
    intro y hy
    obtain ⟨h0, h3, hj⟩ := hy
    refine ⟨by rw [hT0]; exact h0, by rw [hT0]; exact h3, fun j hj1 => ?_⟩
    have hb1 := hj 1 le_rfl
    have hbm := hj (n - 1 - 1) (by omega)
    have hc := Real.abs_cos_le_one (θ y)
    have hs := Real.abs_sin_le_one (θ y)
    by_cases h1 : j = 1
    · subst h1
      rw [hT1]
      calc |Real.cos (θ y) * coordN y 1 - Real.sin (θ y) * coordN y (n - 1 - 1)|
          ≤ |Real.cos (θ y) * coordN y 1| + |Real.sin (θ y) * coordN y (n - 1 - 1)| :=
            abs_sub _ _
        _ = |Real.cos (θ y)| * |coordN y 1| + |Real.sin (θ y)| * |coordN y (n - 1 - 1)| := by
            rw [abs_mul, abs_mul]
        _ ≤ 1 * |coordN y 1| + 1 * |coordN y (n - 1 - 1)| := by
            gcongr
        _ < η := by linarith
    · by_cases hm : j = n - 1 - 1
      · subst hm
        rw [hTm]
        calc |Real.sin (θ y) * coordN y 1 + Real.cos (θ y) * coordN y (n - 1 - 1)|
            ≤ |Real.sin (θ y) * coordN y 1| + |Real.cos (θ y) * coordN y (n - 1 - 1)| :=
              abs_add_le _ _
          _ = |Real.sin (θ y)| * |coordN y 1| + |Real.cos (θ y)| * |coordN y (n - 1 - 1)| := by
              rw [abs_mul, abs_mul]
          _ ≤ 1 * |coordN y 1| + 1 * |coordN y (n - 1 - 1)| := by
              gcongr
          _ < η := by linarith
      · rw [hTj _ _ h1 hm]
        linarith [hj j hj1]
  have hopen : ∀ η' : ℝ, 0 < η' → IsOpen (slideDom (n - 1) η') := by
    intro η' hη'
    have hset : slideDom (n - 1) η' = ({y | 0 < coordN y 0} ∩ {y | coordN y 0 < 3}) ∩
        ⋂ j ∈ Finset.Icc 1 (n - 1), {y : Fin (n - 1) → ℝ | |coordN y j| < η'} := by
      ext y
      simp only [slideDom, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_Icc]
      constructor
      · rintro ⟨h0, h3, hj⟩
        exact ⟨⟨h0, h3⟩, fun j hj' => hj j hj'.1⟩
      · rintro ⟨⟨h0, h3⟩, hj⟩
        refine ⟨h0, h3, fun j hj1 => ?_⟩
        by_cases hjn : j ≤ n - 1
        · exact hj j ⟨hj1, hjn⟩
        · have hz : coordN y j = 0 := by
            simp [coordN, show ¬ j < n - 1 by omega]
          rw [hz, abs_zero]
          exact hη'
    rw [hset]
    exact ((isOpen_lt continuous_const (hcoord 0).continuous).inter
      (isOpen_lt (hcoord 0).continuous continuous_const)).inter
      (isOpen_biInter_finset fun j _ => isOpen_lt (hcoord j).continuous.abs continuous_const)
  have hTinj : Function.Injective (slideTwist (n - 1)) := fun u v h => by
    rw [← hGT u, ← hGT v, h]
  have hU : Ch.U = slideDom (n - 1) η := hCh.1
  have hmapsU : ∀ y ∈ slideDom (n - 1) (η / 2), slideTwist (n - 1) y ∈ Ch.U := by
    intro y hy
    rw [hU]
    exact hmaps y hy
  have hfix : ∀ y, coordN y 0 = 1 → slideTwist (n - 1) y = y := by
    intro y h0
    have hθ : θ y = 0 := by
      simp only [θ, h0]
      rw [Real.smoothTransition.zero_of_nonpos (by norm_num), mul_zero]
    apply hext
    intro j
    by_cases hj1 : j = 1
    · subst hj1
      rw [hT1, hθ]
      simp
    · by_cases hjm : j = n - 1 - 1
      · subst hjm
        rw [hTm, hθ]
        simp
      · exact hTj _ _ hj1 hjm
  have hflip : ∀ y, coordN y 0 = 2 → coordN (slideTwist (n - 1) y) 1 = -coordN y 1 ∧
      ∀ j, 2 ≤ j → j ≤ ℓ → coordN (slideTwist (n - 1) y) j = coordN y j := by
    intro y h0
    have hθ : θ y = Real.pi := by
      simp only [θ, h0]
      rw [Real.smoothTransition.one_of_one_le (by norm_num), mul_one]
    refine ⟨?_, fun j hj2 hjl => hTj _ _ (by omega) (by omega)⟩
    rw [hT1, hθ]
    simp
  refine ⟨{ U := slideDom (n - 1) (η / 2)
            isOpen_U := hopen _ (by linarith)
            φ := fun y => Ch.φ (slideTwist (n - 1) y)
            smooth := ?_
            immersion := ?_
            inj := ?_
            level := fun y hy => Ch.level _ (hmapsU y hy)
            open_image := ?_
            hκ := Ch.hκ
            strip := Ch.strip
            avoid := fun y hy s hs x hx => Ch.avoid _ (hmapsU y hy) s hs x hx }, ⟨rfl, ?_, ?_⟩,
    fun y => rfl⟩
  · exact Ch.smooth.comp hTs.contMDiff.contMDiffOn hmapsU
  · intro y hy
    have hTy := hmapsU y hy
    have hφd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ (slideTwist (n - 1) y) :=
      (Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hTy)).mdifferentiableAt (by simp)
    have hTd' : DifferentiableAt ℝ (slideTwist (n - 1)) y := hTs.differentiable (by simp) _
    have hGd : DifferentiableAt ℝ G (slideTwist (n - 1) y) := hGs.differentiable (by simp) _
    have hcomp := fderiv_comp y hGd hTd'
    have hid : G ∘ slideTwist (n - 1) = id := funext hGT
    rw [hid, fderiv_id] at hcomp
    have key : ∀ w, fderiv ℝ G (slideTwist (n - 1) y) (fderiv ℝ (slideTwist (n - 1)) y w) = w := by
      intro w
      have := congrArg (fun L => L w) hcomp
      simpa using this.symm
    have hinjT : Function.Injective (fderiv ℝ (slideTwist (n - 1)) y) := by
      intro u v huv
      rw [← key u, ← key v, huv]
    change Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I (Ch.φ ∘ slideTwist (n - 1)) y)
    rw [mfderiv_comp y hφd hTd'.mdifferentiableAt, mfderiv_eq_fderiv]
    exact (Ch.immersion _ hTy).comp hinjT
  · intro x hx y hy h
    exact hTinj (Ch.inj (hmapsU x hx) (hmapsU y hy) h)
  · intro V hV hVo
    have hTV : slideTwist (n - 1) '' V = G ⁻¹' V := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        change G (slideTwist (n - 1) w) ∈ V
        rw [hGT]
        exact hw
      · intro hz
        exact ⟨G z, hz, hTG z⟩
    obtain ⟨W, hW, hWeq⟩ := Ch.open_image (slideTwist (n - 1) '' V)
      (by rintro _ ⟨w, hw, rfl⟩; exact hmapsU w (hV hw))
      (by rw [hTV]; exact hVo.preimage hGs.continuous)
    refine ⟨W, hW, ?_⟩
    rw [← hWeq, Set.image_image]
  · intro y hy
    change Ch.φ (slideTwist (n - 1) y) ∈ _ ↔ _
    rw [hCh.2.1 _ (hmaps y hy)]
    simp only [slideA, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hj⟩
      have h0' : coordN y 0 = 1 := by rw [← hT0]; exact h0
      rw [hfix y h0'] at hj
      exact ⟨h0', hj⟩
    · rintro ⟨h0, hj⟩
      rw [hfix y h0]
      exact ⟨h0, hj⟩
  · intro y hy
    change Ch.φ (slideTwist (n - 1) y) ∈ _ ↔ _
    rw [hCh.2.2 _ (hmaps y hy)]
    simp only [slideB, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hj⟩
      have h0' : coordN y 0 = 2 := by rw [← hT0]; exact h0
      refine ⟨h0', fun j hj1 hjl => ?_⟩
      by_cases hj1' : j = 1
      · subst hj1'
        have := hj 1 le_rfl hℓ
        rw [(hflip y h0').1] at this
        linarith
      · have := hj j hj1 hjl
        rwa [(hflip y h0').2 j (by omega) hjl] at this
    · rintro ⟨h0, hj⟩
      have h0' : coordN (slideTwist (n - 1) y) 0 = 2 := by rw [hT0]; exact h0
      refine ⟨h0', fun j hj1 hjl => ?_⟩
      by_cases hj1' : j = 1
      · subst hj1'
        rw [(hflip y h0).1, hj 1 le_rfl hℓ, neg_zero]
      · rw [(hflip y h0).2 j (by omega) hjl]
        exact hj j hj1 hjl

theorem noCommon_after_slide {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (D : GradientLikeStrip I g a b crit) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {ℓ : ℕ}
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {c₂ κ η : ℝ} (Ch : D.CollarChart c₂ κ)
    (hU : Ch.U = slideDom (n - 1) η)
    (hA : ∀ y ∈ slideDom (n - 1) η, Ch.φ y ∈ D.leftSphere q₁ hq₁ ε c₂ ↔ y ∈ slideA (n - 1) ℓ)
    (hB : ∀ y ∈ slideDom (n - 1) η, Ch.φ y ∈ D.rightSphere q₂ hq₂ ε c₂ ↔ y ∈ slideB (n - 1) ℓ)
    (hc₂ : g q₂ + ε < c₂ - κ) (hc₂' : c₂ + κ < g q₁ - ε)
    (hunit : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hdisj : Disjoint (D.leftSphere q₁ hq₁ ε c₂) (D.rightSphere q₂ hq₂ ε c₂))
    (hLdisj : ∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₁ →
      Disjoint (D.leftSphere x hx ε c₂) (Ch.φ '' slideDom (n - 1) η))
    (hD : ∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₁ →
      Disjoint (D.rightSphere q₂ hq₂ ε c₂) (D.leftSphere x hx ε c₂))
    {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ slideDom (n - 1) η)
    {H₁ : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hH₁K : ∀ y, y ∉ K → H₁ y = y)
    (hH₁bij : Function.Bijective H₁)
    (hH₁ : ∀ y ∈ slideA (n - 1) ℓ, y ∈ slideDom (n - 1) η → H₁ y ∉ slideB (n - 1) ℓ)
    {Z : (x : M) → TangentSpace I x} (hZ : Ch.realizes K H₁ Z)
    (E : GradientLikeStrip I g a b crit) (hE : ∀ x, E.V x = D.V x + Z x)
    (hEchart : ∀ x hx, E.chart x hx = D.chart x hx) (hErm : ∀ x hx, E.rm x hx = D.rm x hx) :
    ∃ ρ > 0, ∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₂ → E.noCommon q₂ hq₂ x hx ρ ρ := by
  classical
  have _ := hK
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have hrm0 := D.rm_pos x hx
    have := pow_le_pow_left₀ hrm0.le (D.hrm x hx).2 2
    linarith [pow_pos hrm0 2, (hεr x hx).2]
  have hκ : 0 < κ := Ch.hκ
  have hZs := hZ.2.2.2.1
  have hfl := CollarChart.flow_of_realizes hg Ch hZ (hU ▸ hKU) E hE
  have hbox : ∀ z ∈ tsupport Z, c₂ - κ < g z ∧ g z < c₂ + κ := by
    intro z hz
    obtain ⟨⟨y, s⟩, ⟨hyK, hs⟩, rfl⟩ := hZs hz
    have hyU : y ∈ Ch.U := hU ▸ hKU hyK
    have hlev : g (Ch.φ y) = c₂ := Ch.level y hyU
    have hs' : -κ < s ∧ s < κ := hs
    change c₂ - κ < g (D.flow s (Ch.φ y)) ∧ g (D.flow s (Ch.φ y)) < c₂ + κ
    rcases le_total 0 s with h0 | h0
    · have h1 := D.sub_le_f_flow hg (Ch.φ y) h0
      have h2 := D.f_flow_le hg (Ch.φ y) h0
      constructor <;> linarith [hs'.1, hs'.2]
    · have h1 := D.le_f_flow_of_nonpos hg (Ch.φ y) h0
      have h2 := D.f_flow_le_sub_of_nonpos hg (Ch.φ y) h0
      constructor <;> linarith [hs'.1, hs'.2]
  have hR : E.rightSphere q₂ hq₂ ε (c₂ - κ) ⊆ D.rightSphere q₂ hq₂ ε (c₂ - κ) := by
    intro z hz
    rw [GradientLikeStrip.rightSphere, hEchart] at hz
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hz
    have hm : g ((D.chart q₂ hq₂).χ y) = g q₂ + ε :=
      (D.chart q₂ hq₂).f_chart_of_mem_rightModelSphere (hεR q₂ hq₂) hy
    have hT : g q₂ + ε - (c₂ - κ) ≤ 0 := by linarith
    rw [hfl.1 _ _ ?_]
    · exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · intro s hs hsZ
      rw [min_eq_right hT, max_eq_left hT] at hs
      have h1 := D.f_flow_le_sub_of_nonpos hg ((D.chart q₂ hq₂).χ y) hs.2
      have := (hbox _ hsZ).1
      linarith [hs.1]
  have hL : ∀ x (hx : x ∈ crit), g x = g q₁ → ∀ z ∈ E.leftSphere x hx ε (c₂ - κ),
      (∃ y ∈ K, Ch.φ y ∈ D.leftSphere x hx ε c₂ ∧ z = D.flow κ (Ch.φ (H₁ y))) ∨
        D.flow (-κ) z ∈ D.leftSphere x hx ε c₂ := by
    intro x hx hgx z hz
    rw [GradientLikeStrip.leftSphere, hEchart] at hz
    obtain ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩ := hz
    set m := (D.chart x hx).χ y₀ with hmdef
    have hm : g m = g x - ε := (D.chart x hx).f_chart_of_mem_leftModelSphere (hεR x hx) hy₀
    set T₁ := g x - ε - (c₂ + κ) with hT₁
    have hT₁0 : 0 ≤ T₁ := by rw [hT₁, hgx]; linarith
    rw [show g x - ε - (c₂ - κ) = T₁ + 2 * κ by rw [hT₁]; ring, ← E.flow_flow]
    have hEw : E.flow T₁ m = D.flow T₁ m := by
      refine hfl.1 _ _ ?_
      intro s hs hsZ
      rw [min_eq_left hT₁0, max_eq_right hT₁0] at hs
      have h1 := D.sub_le_f_flow hg m hs.1
      have := (hbox _ hsZ).2
      linarith [hs.2]
    rw [hEw]
    have hmL : ∀ t, D.flow t m ∈ D.leftSphere x hx ε (g x - ε - t) := by
      intro t
      refine ⟨m, ⟨y₀, hy₀, rfl⟩, ?_⟩
      congr 1
      ring
    by_cases hw : D.flow T₁ m ∈ D.flow (-κ) '' (Ch.φ '' K)
    · obtain ⟨_, ⟨y, hyK, rfl⟩, hw'⟩ := hw
      have hyU : y ∈ Ch.U := hU ▸ hKU hyK
      left
      refine ⟨y, hyK, ?_, ?_⟩
      · have h1 : Ch.φ y = D.flow (T₁ + κ) m := by
          rw [← D.flow_flow, ← hw', D.flow_flow_neg]
        rw [h1]
        convert hmL (T₁ + κ) using 2
        rw [hT₁]; ring
      · rw [← hw']
        exact hZ.2.2.2.2 E hE y hyU
    · right
      have hlevw : g (D.flow T₁ m) = c₂ + κ := by
        have hsub := D.leftSphere_subset_level hg x hx (hεR x hx)
          (c := c₂ + κ) ⟨by linarith [Ch.strip.1], Ch.strip.2⟩ (by
            intro y hy p hp
            refine hunit y ?_ p hp
            rw [hgx] at hy
            rw [uIcc_of_ge (by linarith)] at hy
            exact ⟨by linarith [hy.1], hy.2⟩)
        have hmem : D.flow T₁ m ∈ D.leftSphere x hx ε (c₂ + κ) := by
          convert hmL T₁ using 2
          rw [hT₁]; ring
        exact hsub hmem
      rw [hfl.2 _ hlevw hw, D.flow_flow, D.flow_flow]
      convert hmL (T₁ + κ) using 2
      · ring
      · rw [hT₁]; ring
  have hdisjE : ∀ x (hx : x ∈ crit), g x = g q₁ →
      Disjoint (E.rightSphere q₂ hq₂ ε (c₂ - κ)) (E.leftSphere x hx ε (c₂ - κ)) := by
    intro x hx hgx
    rw [Set.disjoint_left]
    intro z hzR hzL
    have hzR' := hR hzR
    have hR2 : D.flow (-κ) z ∈ D.rightSphere q₂ hq₂ ε c₂ := by
      rw [D.mem_rightSphere_iff] at hzR' ⊢
      rw [D.flow_flow]
      convert hzR' using 2
      ring
    rcases hL x hx hgx z hzL with ⟨y, hyK, hyL, rfl⟩ | hzL'
    · rw [D.flow_neg_flow] at hR2
      have hHK : H₁ y ∈ K := by
        by_contra hc
        have h1 := hH₁bij.1 (hH₁K (H₁ y) hc)
        rw [h1] at hc
        exact hc hyK
      have hyD := hKU hyK
      have hHD := hKU hHK
      have hBy := (hB _ hHD).1 hR2
      by_cases hxq : x = q₁
      · subst hxq
        exact hH₁ y ((hA y hyD).1 hyL) hyD hBy
      · exact Set.disjoint_left.1 (hLdisj x hx hgx hxq) hyL ⟨y, hyD, rfl⟩
    · by_cases hxq : x = q₁
      · subst hxq
        exact Set.disjoint_left.1 hdisj hzL' hR2
      · exact Set.disjoint_left.1 (hD x hx hgx hxq) hR2 hzL'
  have hεrE : ∀ z hz, (E.chart z hz).r₀ ^ 2 < 2 * ε ∧ 8 * ε < E.rm z hz ^ 2 := by
    intro z hz
    rw [hEchart, hErm]
    exact hεr z hz
  have hρ : ∀ x (hx : x ∈ crit), ∃ ρ > 0, g x = g q₁ →
      ∀ rx ry, rx < ρ → ry < ρ → E.noCommon q₂ hq₂ x hx rx ry := by
    intro x hx
    by_cases hgx : g x = g q₁
    · obtain ⟨ρ, hρ, h⟩ := E.exists_noCommon_of_disjoint hg hq₂ hx hε hεrE (by linarith)
        (by rw [hgx]; linarith) (by
          intro z hz w hw
          change z ∉ (E.chart w hw).χ '' {y | morseNorm n y < (E.chart w hw).r₀}
          rw [hEchart]
          rw [hgx] at hz
          exact hunit z hz w hw) (hdisjE x hx hgx)
      exact ⟨ρ, hρ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hgx⟩
  choose ρf hρf hρN using hρ
  obtain ⟨x₀, -, hx₀⟩ := crit.attach.exists_min_image (fun x => ρf x.1 x.2)
    ⟨⟨q₁, hq₁⟩, Finset.mem_attach _ _⟩
  refine ⟨ρf x₀.1 x₀.2 / 2, by linarith [hρf x₀.1 x₀.2], fun x hx hgx _ =>
    hρN x hx hgx _ _ ?_ ?_⟩ <;>
    linarith [hx₀ ⟨x, hx⟩ (Finset.mem_attach _ _), hρf x₀.1 x₀.2]

open Classical in
def slideTrack (D : GradientLikeStrip I f a b crit) {c₂ κ : ℝ} (Ch : D.CollarChart c₂ κ)
    (Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)) (q₁ : M) (ℓ : ℕ) (ε t : ℝ)
    (z : EuclideanSpace ℝ (Fin (ℓ + 1))) : M :=
  if h : ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z then
    D.flow κ (Ch.φ (Hs t (Classical.choose h)))
  else D.flow (2 * κ) (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z)

open Classical in
def slideAnnulus (D : GradientLikeStrip I f a b crit) {c₂ κ : ℝ} (Ch : D.CollarChart c₂ κ)
    (Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)) (q₁ : M) (ℓ : ℕ) (ε c : ℝ)
    (z : EuclideanSpace ℝ (Fin (ℓ + 1))) : M :=
  if ‖z‖ ≤ 4 / 3 then
    D.flow ((4 - 3 * ‖z‖) * D.hitTime c (D.slideTrack Ch Hs q₁ ℓ ε 0 (‖z‖⁻¹ • z)))
      (D.slideTrack Ch Hs q₁ ℓ ε 0 (‖z‖⁻¹ • z))
  else if ‖z‖ ≤ 5 / 3 then D.slideTrack Ch Hs q₁ ℓ ε (3 * ‖z‖ - 4) (‖z‖⁻¹ • z)
  else
    D.flow ((3 * ‖z‖ - 5) * D.hitTime c (D.slideTrack Ch Hs q₁ ℓ ε 1 (‖z‖⁻¹ • z)))
      (D.slideTrack Ch Hs q₁ ℓ ε 1 (‖z‖⁻¹ • z))

theorem slideAnnulus_mapsTo {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ) {η η' : ℝ} (hη' : η' ≤ η)
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ η' K Hs) :
    ContinuousOn (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulus (ℓ + 1)) ∧
      MapsTo (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulus (ℓ + 1)) (g ⁻¹' Icc a (c₂ - κ)) ∧
      MapsTo (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulusBdry (ℓ + 1) ∩ Handle.annulus (ℓ + 1))
        (g ⁻¹' Icc a c) := by
  classical
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  obtain ⟨hKc, hKdom, hHsC, hHsbij, -, hHsK, hHs0, -, -, hA1, -⟩ := hfin
  obtain ⟨hUeq, hLA, hRB⟩ := hCh
  have hε : 0 < ε := hS.hε
  have hκ : 0 < κ := hS.hκ
  have hac := hS.hac
  have hcq₂ := hS.hcq₂
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hq₁b := hS.hq₁b
  have hq₂ab := ((hcrit q₂).1 hq₂).1
  have hq₁ab := D.f_mem_Ioo q₁ hq₁
  have hstrip := Ch.strip
  have hU' : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x (hx : x ∈ crit), y ∉ D.smallBall x hx :=
    fun y hy => hS.hunit y (Or.inr hy)
  have htrans : ∀ c₁ c₃ : ℝ, g q₂ + ε ≤ c₁ → c₁ ≤ c₃ → c₃ ≤ g q₁ - ε → ∀ x, g x = c₃ →
      g (D.flow (c₃ - c₁) x) = c₁ := by
    intro c₁ c₃ h1 h13 h3 x hx
    exact ((flow_level_transport (D := D) hf (by linarith) h13 (by linarith)
      (fun y hy p hp => hU' y ⟨by linarith [hy.1], by linarith [hy.2]⟩ p hp)).1 x hx).1
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 := (D.hrm x hx).2
    have h3 := D.rm_pos x hx
    nlinarith
  have hcol : ∀ y ∈ Ch.U, ∀ s ∈ Icc (-κ) κ, g (D.flow s (Ch.φ y)) = c₂ - s := by
    intro y hy s hs
    have hlev := Ch.level y hy
    have havoid : ∀ s' ∈ uIcc 0 s, ∀ (p : M) (hp : p ∈ crit),
        D.flow s' (Ch.φ y) ∉ D.smallBall p hp := by
      intro s' hs' p hp hmem
      have hs'' : s' ∈ Icc (-κ) κ := by
        rw [mem_uIcc] at hs'
        rcases hs' with h | h <;> constructor <;> linarith [hs.1, hs.2, h.1, h.2]
      exact Ch.avoid y hy s' hs'' p hp
        (image_mono (fun z (hz : morseNorm n z < _) => hz.trans (D.r₀_lt_rm p hp)) hmem)
    have := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := s)
      (by rw [hlev]; constructor <;> linarith) (by rw [hlev]; constructor <;> linarith [hs.1, hs.2])
      havoid s right_mem_uIcc
    rw [this, hlev]
  have hdomsub : slideDom (n - 1) η' ⊆ Ch.U := by
    rw [hUeq]
    intro y hy
    exact ⟨hy.1, hy.2.1, fun j hj => (hy.2.2 j hj).trans_le hη'⟩
  have hKU : K ⊆ Ch.U := hKdom.trans hdomsub
  have hHsKK : ∀ t, ∀ y ∈ K, Hs t y ∈ K := by
    intro t y hy
    by_contra hw
    have h1 := hHsK t _ hw
    have h2 := (hHsbij t).1 h1
    exact hw (by rw [h2]; exact hy)
  have hHsU : ∀ t, ∀ y ∈ Ch.U, Hs t y ∈ Ch.U := by
    intro t y hy
    by_cases hyK : y ∈ K
    · exact hKU (hHsKK t y hyK)
    · rw [hHsK t y hyK]; exact hy
  obtain ⟨σ, hσdef⟩ : ∃ σ : EuclideanSpace ℝ (Fin (ℓ + 1)) → M,
      σ = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) := ⟨_, rfl⟩
  have hk₁ := hS.hk₁
  have hreidx : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      (Handle.reidx u : Fin (D.chart q₁ hq₁).k → ℝ) ≠ 0 := by
    intro u hu h0
    apply hu
    ext i
    have := congrFun h0 ⟨i, by rw [hk₁]; exact i.isLt⟩
    simp only [Handle.reidx, Pi.zero_apply, show (i : ℕ) < ℓ + 1 from i.isLt, ↓reduceDIte] at this
    exact this
  have hσeq : ∀ u, σ u = D.flow (g q₁ - ε - (c₂ + κ)) ((D.chart q₁ hq₁).χ
      ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx u))) := by
    intro u
    simp only [hσdef, leftSphereMap, hq₁, ↓reduceDIte]
  have hσL : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 → ∀ s,
      D.flow s (σ u) ∈ D.leftSphere q₁ hq₁ ε (c₂ + κ - s) := by
    intro u hu s
    rw [hσeq, flow_flow]
    unfold leftSphere
    refine ⟨(D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx u)),
      mem_image_of_mem _ ((D.chart q₁ hq₁).sphereParam_mem_leftModelSphere hε.le (hreidx u hu)), ?_⟩
    congr 1
    ring
  have hσlev : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 → ∀ s ∈ Icc 0 (2 * κ),
      g (D.flow s (σ u)) = c₂ + κ - s := by
    intro u hu s hs
    have hsub := D.leftSphere_subset_level hf q₁ hq₁ (hεR q₁ hq₁) (c := c₂ + κ - s)
      ⟨by linarith [hs.2, hstrip.1], by linarith [hs.1, hstrip.2]⟩ (fun y hy p hp => hU' y (by
        rw [uIcc_of_ge (by linarith [hs.1])] at hy
        exact ⟨by linarith [hy.1, hs.2], hy.2⟩) p hp)
    exact hsub (hσL u hu s)
  have hreidxc : Continuous (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) =>
      (Handle.reidx u : Fin (D.chart q₁ hq₁).k → ℝ)) := by
    refine continuous_pi fun i => ?_
    simp only [Handle.reidx]
    split_ifs with h
    · exact PiLp.continuous_apply 2 (fun _ : Fin (ℓ + 1) => ℝ) ⟨i, h⟩
    · exact continuous_const
  have hσcont : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 → ContinuousAt σ u := by
    intro u hu
    have h1 : ContinuousAt ((D.chart q₁ hq₁).sphereParam ε) (Handle.reidx u) :=
      ((D.chart q₁ hq₁).contDiffAt_sphereParam ε (hreidx u hu)).continuousAt
    have hmem : (D.chart q₁ hq₁).sphereParam ε (Handle.reidx u) ∈ (D.chart q₁ hq₁).χ.source :=
      (D.chart q₁ hq₁).hsrc _
        ((D.chart q₁ hq₁).morseNorm_sphereParam_le hε.le (hεR q₁ hq₁) (hreidx u hu))
    have h2 : ContinuousAt (D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx u)) :=
      (D.chart q₁ hq₁).χ.continuousAt hmem
    have hfun : σ = fun u => D.flow (g q₁ - ε - (c₂ + κ)) ((D.chart q₁ hq₁).χ
        ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx u))) := funext hσeq
    rw [hfun]
    exact (D.continuous_flow _).continuousAt.comp (ContinuousAt.comp (x := u) h2 (h1.comp hreidxc.continuousAt))
  have htr_eq : ∀ t u y, y ∈ Ch.U → D.flow (-κ) (Ch.φ y) = σ u →
      D.slideTrack Ch Hs q₁ ℓ ε t u = D.flow κ (Ch.φ (Hs t y)) := by
    intro t u y hy hyσ
    have h : ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u :=
      ⟨y, hy, by rw [← hσdef]; exact hyσ⟩
    simp only [slideTrack, h, ↓reduceDIte]
    have hs := Classical.choose_spec h
    have h1 : Classical.choose h = y :=
      Ch.inj hs.1 hy (D.flow_injective (-κ) (hs.2.trans (by rw [← hσdef]; exact hyσ.symm)))
    rw [h1]
  have htr_not : ∀ t u, (¬ ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = σ u) →
      D.slideTrack Ch Hs q₁ ℓ ε t u = D.flow (2 * κ) (σ u) := by
    intro t u h
    have h' : ¬ ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u := by
      rw [← hσdef]; exact h
    simp only [slideTrack, h', ↓reduceDIte]
    rw [← hσdef]
  have htr_id : ∀ t u, (∀ y ∈ Ch.U, D.flow (-κ) (Ch.φ y) = σ u → Hs t y = y) →
      D.slideTrack Ch Hs q₁ ℓ ε t u = D.flow (2 * κ) (σ u) := by
    intro t u hid
    by_cases h : ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = σ u
    · obtain ⟨y, hy, hyσ⟩ := h
      rw [htr_eq t u y hy hyσ, hid y hy hyσ, ← hyσ, flow_flow]
      congr 1
      ring
    · exact htr_not t u h
  have htr0 : ∀ u, D.slideTrack Ch Hs q₁ ℓ ε 0 u = D.flow (2 * κ) (σ u) :=
    fun u => htr_id 0 u fun y _ _ => hHs0 0 le_rfl y
  have htr_lev : ∀ t u, u ≠ 0 → g (D.slideTrack Ch Hs q₁ ℓ ε t u) = c₂ - κ := by
    intro t u hu
    by_cases h : ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = σ u
    · obtain ⟨y, hy, hyσ⟩ := h
      rw [htr_eq t u y hy hyσ]
      exact hcol _ (hHsU t y hy) κ ⟨by linarith, le_rfl⟩
    · rw [htr_not t u h, hσlev u hu (2 * κ) ⟨by linarith, le_rfl⟩]
      ring
  have hcapR : ∀ w, g w = c₂ → w ∈ D.captured q₂ hq₂ → w ∈ D.rightSphere q₂ hq₂ ε c₂ := by
    intro w hw hcap
    have hrm := D.rm_pos q₂ hq₂
    have h8 := (hS.hεr q₂ hq₂).2
    have hρ : 0 < min (Real.sqrt ε) (D.rm q₂ hq₂) := lt_min (Real.sqrt_pos.2 hε) hrm
    obtain ⟨T, hT⟩ := captured_eventually_small hcap hρ
    obtain ⟨y, ⟨hyρ, hyu⟩, hyT⟩ := hT T le_rfl
    have hysq : morseNorm n y ^ 2 < ε :=
      (Real.lt_sqrt (ModelField.morseNorm_nonneg y)).1 (hyρ.trans_le (min_le_left _ _))
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart q₂ hq₂).hk y
    rw [hyu, norm_zero] at hsq
    have hv : posPart (D.chart q₂ hq₂).hk y ≠ 0 := by
      intro hv0
      rw [hv0, norm_zero] at hsq
      have hy0 : y = 0 := (ModelField.morseNorm_eq_zero_iff y).1
        (by nlinarith [ModelField.morseNorm_nonneg y])
      have hwq : w = q₂ := by
        have h1 : D.flow T w = q₂ := by rw [← hyT, hy0, (D.chart q₂ hq₂).hχ0]
        rw [← D.flow_neg_flow w T, h1, D.flow_crit hq₂]
      rw [hwq] at hw
      linarith
    have hball : 2 * ε + 2 * ‖negPart (D.chart q₂ hq₂).hk y‖ ^ 2 < D.rm q₂ hq₂ ^ 2 := by
      rw [hyu, norm_zero]; nlinarith
    have hlevel : morseNormalForm (D.chart q₂ hq₂).hk (g q₂) y ≤ g q₂ + ε := by
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hyu, norm_zero]
      nlinarith
    obtain ⟨t, ht0, hft, hstay, hprod⟩ := exists_exit_asc (D := D) hf hq₂ hε hball hv hlevel
    rw [hyu, norm_zero] at hprod hstay
    obtain ⟨z, hz, hze⟩ := hstay (-t) (left_mem_Icc.2 (by linarith))
    have hz' : morseNorm n z ^ 2 ≤ 2 * ε := by
      have hz'' : morseNorm n z ^ 2 ≤ 2 * ε + 2 * (0 : ℝ) ^ 2 := hz
      linarith
    have hR0 : 0 < (D.chart q₂ hq₂).R := (D.chart q₂ hq₂).hr₀.trans (D.r₀_lt_R q₂ hq₂)
    have hzR : morseNorm n z ≤ (D.chart q₂ hq₂).R :=
      MorseNormalChart.morseNorm_le_of_sq_le hR0.le (hz'.trans (hεR q₂ hq₂))
    have hzsymm : (D.chart q₂ hq₂).χ.symm ((D.chart q₂ hq₂).χ z) = z :=
      (D.chart q₂ hq₂).χ.left_inv ((D.chart q₂ hq₂).hsrc z hzR)
    rw [← hze, hzsymm] at hprod
    have hzu : negPart (D.chart q₂ hq₂).hk z = 0 := by
      have h0 : ‖negPart (D.chart q₂ hq₂).hk z‖ ^ 2 = 0 := by
        have := sq_nonneg ‖negPart (D.chart q₂ hq₂).hk z‖
        nlinarith
      exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
    have hfz : g ((D.chart q₂ hq₂).χ z) = g q₂ + ε := by rw [hze]; exact hft
    have hnz := (D.chart q₂ hq₂).hnorm z hzR
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hzu, norm_zero,
      hfz] at hnz
    have hzRS : z ∈ (D.chart q₂ hq₂).rightModelSphere ε := ⟨hzu, by linarith⟩
    have hτ : g (D.flow (c₂ - (g q₂ + ε)) w) = g q₂ + ε :=
      htrans (g q₂ + ε) c₂ le_rfl (by linarith) (by linarith) w hw
    have hTt : g (D.flow (T + -t) w) = g q₂ + ε := by
      rw [← flow_flow, ← hyT]; exact hft
    have hunitlev : ∀ y, g y = g q₂ + ε → dfV I g D.V y = -1 :=
      fun y hy => D.dfV_eq_neg_one_of_level (c := g q₂ + ε) ⟨by linarith, by linarith⟩
        (fun p hp y' hy' hy'lev => hU' y' (by rw [hy'lev]; constructor <;> linarith) p hp hy') hy
    have heq := flow_level_unique (D := D) hf hunitlev hτ hTt
    rw [mem_rightSphere_iff, heq, ← flow_flow, ← hyT, ← hze]
    exact mem_image_of_mem _ hzRS
  have hreg : ∀ x ∈ crit, g x ≠ c := by
    intro x hx hxc
    have := hS.hslab x hx ⟨hxc.ge, by linarith⟩
    subst this
    linarith
  have hreach : ∀ w, g w = c₂ → w ∉ D.rightSphere q₂ hq₂ ε c₂ →
      ∃ s, 0 ≤ s ∧ g (D.flow s w) < c := by
    intro w hw hwR
    by_contra hno
    push Not at hno
    rcases trichotomy (D := D) hf hε hS.hεr (x := w) (by rw [hw]; constructor <;> linarith) with
      ⟨s, hs, hlt⟩ | ⟨r, hr, hcap⟩
    · linarith [hno s hs]
    · by_cases hrc : g r < c
      · obtain ⟨T, hT⟩ := exists_f_flow_lt_of_mem_captured hcap (η := c - g r) (by linarith)
        have h1 := f_flow_antitone (D := D) hf w (le_max_left T 0)
        have h2 := hno (max T 0) (le_max_right T 0)
        simp only at h1
        linarith
      · push Not at hrc
        have h1 := f_le_of_mem_captured hf hcap 0
        rw [D.flow_zero, hw] at h1
        have hrq : r = q₂ := hS.hslab r hr ⟨hrc, by linarith⟩
        subst hrq
        exact hwR (hcapR w hw hcap)
  have hSκ : ∀ w, g w = c₂ → w ∉ D.rightSphere q₂ hq₂ ε c₂ →
      ∃ s, 0 ≤ s ∧ g (D.flow s (D.flow κ w)) < c := by
    intro w hw hwR
    obtain ⟨s, hs, hlt⟩ := hreach w hw hwR
    refine ⟨s, hs, lt_of_le_of_lt ?_ hlt⟩
    rw [flow_flow]
    exact f_flow_antitone (D := D) hf w (by linarith)
  have hS0 : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      ∃ s, 0 ≤ s ∧ g (D.flow s (D.slideTrack Ch Hs q₁ ℓ ε 0 u)) < c := by
    intro u hu
    have hL := hσL u hu κ
    rw [show c₂ + κ - κ = c₂ by ring] at hL
    have hlev : g (D.flow κ (σ u)) = c₂ := by
      rw [hσlev u hu κ ⟨hκ.le, by linarith⟩]; ring
    have := hSκ _ hlev (fun hR => Set.disjoint_left.1 hS.hdisj hL hR)
    rw [htr0, show 2 * κ = κ + κ by ring, ← flow_flow]
    exact this
  have hS1 : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      ∃ s, 0 ≤ s ∧ g (D.flow s (D.slideTrack Ch Hs q₁ ℓ ε 1 u)) < c := by
    intro u hu
    by_cases h : ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = σ u
    · obtain ⟨y, hy, hyσ⟩ := h
      rw [htr_eq 1 u y hy hyσ]
      refine hSκ _ (Ch.level _ (hHsU 1 y hy)) fun hR => ?_
      have hB : Hs 1 y ∈ slideB (n - 1) ℓ :=
        (hRB _ (by rw [← hUeq]; exact hHsU 1 y hy)).1 hR
      have hφy : Ch.φ y = D.flow κ (σ u) := by rw [← hyσ, D.flow_flow_neg]
      have hL := hσL u hu κ
      rw [show c₂ + κ - κ = c₂ by ring, ← hφy] at hL
      have hA : y ∈ slideA (n - 1) ℓ := (hLA y (by rw [← hUeq]; exact hy)).1 hL
      by_cases hyK : y ∈ K
      · exact hA1 y hA (hKdom hyK) hB
      · rw [hHsK 1 y hyK] at hB
        have h1 := hA.1
        have h2 := hB.1
        rw [h1] at h2
        norm_num at h2
    · rw [htr_not 1 u h, ← htr0]
      exact hS0 u hu
  obtain ⟨hopen, inv, hinvC, hinv⟩ := Ch.exists_boxInverse hf
  obtain ⟨B, hBdef⟩ : ∃ B : Set M,
      B = (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (Ch.U ×ˢ Ioo (-κ) κ) :=
    ⟨_, rfl⟩
  rw [← hBdef] at hinvC
  have hBopen : IsOpen B := by
    rw [hBdef]; exact hopen _ subset_rfl (Ch.isOpen_U.prod isOpen_Ioo)
  have hCcl : IsClosed ((fun y => D.flow (-κ) (Ch.φ y)) '' K) :=
    (hKc.image_of_continuousOn ((D.continuous_flow _).comp_continuousOn
      (Ch.smooth.continuousOn.mono hKU))).isClosed
  have hTcont : ∀ t (u : EuclideanSpace ℝ (Fin (ℓ + 1))), u ≠ 0 →
      ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) =>
        D.slideTrack Ch Hs q₁ ℓ ε p.1 p.2) (t, u) := by
    intro t u hu
    have hσu : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) => σ p.2) (t, u) :=
      (hσcont u hu).comp continuousAt_snd
    by_cases hC : σ u ∈ (fun y => D.flow (-κ) (Ch.φ y)) '' K
    · obtain ⟨y₀, hy₀K, hy₀⟩ := hC
      have hκmem : -(κ / 2) ∈ Ioo (-κ) κ := by constructor <;> linarith
      have hG : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) =>
          D.flow (κ / 2) (σ p.2)) (t, u) :=
        (D.continuous_flow _).continuousAt.comp hσu
      have hGu : D.flow (κ / 2) (σ u) = D.flow (-(κ / 2)) (Ch.φ y₀) := by
        rw [← hy₀, flow_flow]; congr 1; ring
      have hGB : D.flow (κ / 2) (σ u) ∈ B := by
        rw [hBdef]; exact ⟨(y₀, -(κ / 2)), ⟨hKU hy₀K, hκmem⟩, hGu.symm⟩
      have hinvu : inv (D.flow (κ / 2) (σ u)) = (y₀, -(κ / 2)) := by
        have := hinv (y₀, -(κ / 2)) ⟨hKU hy₀K, hκmem⟩
        dsimp only at this
        rw [hGu, this]
      have hev : ∀ᶠ p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) in 𝓝 (t, u),
          p.2 ≠ 0 ∧ D.flow (κ / 2) (σ p.2) ∈ B :=
        (continuousAt_snd.eventually (isOpen_ne.mem_nhds
          (show u ∈ {v : EuclideanSpace ℝ (Fin (ℓ + 1)) | v ≠ 0} from hu))).and
          (hG.eventually (hBopen.mem_nhds hGB))
      have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) =>
          D.flow κ (Ch.φ (Hs p.1 (inv (D.flow (κ / 2) (σ p.2))).1))) =ᶠ[𝓝 (t, u)]
          (fun p => D.slideTrack Ch Hs q₁ ℓ ε p.1 p.2) := by
        filter_upwards [hev] with p hp
        obtain ⟨hp0, hpB⟩ := hp
        rw [hBdef] at hpB
        obtain ⟨⟨y', s'⟩, ⟨hy'U, hs'⟩, hbox⟩ := hpB
        dsimp only at hbox
        have hl1 := hcol y' hy'U s' ⟨hs'.1.le, hs'.2.le⟩
        have hl2 : g (D.flow (κ / 2) (σ p.2)) = c₂ + κ - κ / 2 :=
          hσlev p.2 hp0 (κ / 2) ⟨by linarith, by linarith⟩
        rw [← hbox, hl1] at hl2
        have hs'eq : s' = -(κ / 2) := by linarith
        subst hs'eq
        have hyσ : D.flow (-κ) (Ch.φ y') = σ p.2 := by
          have := congrArg (D.flow (-(κ / 2))) hbox
          rw [D.flow_neg_flow, flow_flow] at this
          rw [← this]; congr 1; ring
        have hinv' := hinv (y', -(κ / 2)) ⟨hy'U, hs'⟩
        dsimp only at hinv'
        rw [htr_eq p.1 p.2 y' hy'U hyσ, ← hbox, hinv']
      refine ContinuousAt.congr ?_ heq
      have hinvc : ContinuousAt inv (D.flow (κ / 2) (σ u)) :=
        hinvC.continuousOn.continuousAt (hBopen.mem_nhds hGB)
      have h1 : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) =>
          (p.1, (inv (D.flow (κ / 2) (σ p.2))).1)) (t, u) :=
        continuousAt_fst.prodMk (continuousAt_fst.comp (ContinuousAt.comp (x := (t, u)) hinvc hG))
      have h2 : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) =>
          Hs p.1 (inv (D.flow (κ / 2) (σ p.2))).1) (t, u) :=
        hHsC.continuous.continuousAt.comp h1
      have hmemU : Hs t (inv (D.flow (κ / 2) (σ u))).1 ∈ Ch.U := by
        rw [hinvu]; exact hHsU t y₀ (hKU hy₀K)
      have h3 : ContinuousAt Ch.φ (Hs t (inv (D.flow (κ / 2) (σ u))).1) :=
        Ch.smooth.continuousOn.continuousAt (Ch.isOpen_U.mem_nhds hmemU)
      exact (D.continuous_flow κ).continuousAt.comp (ContinuousAt.comp (x := (t, u)) h3 h2)
    · have hev : ∀ᶠ p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) in 𝓝 (t, u),
          σ p.2 ∉ (fun y => D.flow (-κ) (Ch.φ y)) '' K :=
        hσu.eventually (hCcl.isOpen_compl.mem_nhds hC)
      have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) => D.flow (2 * κ) (σ p.2)) =ᶠ[𝓝 (t, u)]
          (fun p => D.slideTrack Ch Hs q₁ ℓ ε p.1 p.2) := by
        filter_upwards [hev] with p hp
        exact (htr_id p.1 p.2 fun y _ hyσ => hHsK p.1 y fun hyK => hp ⟨y, hyK, hyσ⟩).symm
      exact ((D.continuous_flow _).continuousAt.comp hσu).congr heq
  obtain ⟨hHitC, -⟩ := continuousOn_hitTime hf D (t := c) hac.le (by linarith) hreg
  have hband : ∀ x, g x = c₂ - κ → (∃ s, 0 ≤ s ∧ g (D.flow s x) < c) → ∀ s ∈ Icc (0 : ℝ) 1,
      g (D.flow (s * D.hitTime c x) x) ∈ Icc c (c₂ - κ) ∧
        (s = 1 → g (D.flow (s * D.hitTime c x) x) = c) := by
    intro x hx hSx s hs
    obtain ⟨s₀, hs₀, hlt⟩ := hSx
    obtain ⟨hdesc, hh0, hbefore⟩ := descend_spec hf D (t := c) (x := x) (by rw [hx]; linarith)
      ⟨s₀, hs₀, hlt.le⟩
    have hsh0 : 0 ≤ s * D.hitTime c x := mul_nonneg hs.1 hh0
    have hle : s * D.hitTime c x ≤ D.hitTime c x := by nlinarith [hs.2]
    refine ⟨⟨?_, ?_⟩, fun h1 => ?_⟩
    · rcases hle.lt_or_eq with hlt' | heq'
      · exact (hbefore _ hsh0 hlt').le
      · rw [heq']; exact hdesc.ge
    · rw [← hx]; exact f_flow_le (D := D) hf x hsh0
    · rw [h1, one_mul]; exact hdesc
  have hunitv : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), 1 ≤ ‖z‖ → ‖z‖⁻¹ • z ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hz0)) hz0
  have hucont : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), 1 ≤ ‖z‖ →
      ContinuousAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z := by
    intro z hz
    exact (continuous_norm.continuousAt.inv₀ (by positivity)).smul continuousAt_id
  have hTz : ∀ (τ : EuclideanSpace ℝ (Fin (ℓ + 1)) → ℝ), Continuous τ →
      ContinuousOn (fun z => D.slideTrack Ch Hs q₁ ℓ ε (τ z) (‖z‖⁻¹ • z))
        (Handle.annulus (ℓ + 1)) := by
    intro τ hτ z hz
    have hz1 : 1 ≤ ‖z‖ := hz.1
    exact (ContinuousAt.comp (x := z) (hTcont (τ z) (‖z‖⁻¹ • z) (hunitv z hz1))
      (hτ.continuousAt.prodMk (hucont z hz1))).continuousWithinAt
  have hF : ∀ (τ₀ : ℝ) (α : EuclideanSpace ℝ (Fin (ℓ + 1)) → ℝ), Continuous α →
      (τ₀ = 0 ∨ τ₀ = 1) →
      ContinuousOn (fun z => D.flow (α z * D.hitTime c (D.slideTrack Ch Hs q₁ ℓ ε τ₀ (‖z‖⁻¹ • z)))
        (D.slideTrack Ch Hs q₁ ℓ ε τ₀ (‖z‖⁻¹ • z))) (Handle.annulus (ℓ + 1)) := by
    intro τ₀ α hα hτ₀
    have htr := hTz (fun _ => τ₀) continuous_const
    have hmaps : MapsTo (fun z => D.slideTrack Ch Hs q₁ ℓ ε τ₀ (‖z‖⁻¹ • z))
        (Handle.annulus (ℓ + 1)) {x | ∃ s, 0 ≤ s ∧ g (D.flow s x) < c} := by
      intro z hz
      rcases hτ₀ with h | h <;> subst h
      · exact hS0 _ (hunitv z hz.1)
      · exact hS1 _ (hunitv z hz.1)
    have hhit := hHitC.comp htr hmaps
    exact D.continuous_flow_joint.comp_continuousOn ((hα.continuousOn.mul hhit).prodMk htr)
  have hF1 := hF 0 (fun z => 4 - 3 * ‖z‖)
    (continuous_const.sub (continuous_const.mul continuous_norm)) (Or.inl rfl)
  have hF2 := hTz (fun z => 3 * ‖z‖ - 4)
    ((continuous_const.mul continuous_norm).sub continuous_const)
  have hF3 := hF 1 (fun z => 3 * ‖z‖ - 5)
    ((continuous_const.mul continuous_norm).sub continuous_const) (Or.inr rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold slideAnnulus
    refine ContinuousOn.if ?_ (hF1.mono inter_subset_left)
      (ContinuousOn.if ?_ (hF2.mono (inter_subset_left.trans inter_subset_left))
        (hF3.mono (inter_subset_left.trans inter_subset_left)))
    · rintro z ⟨-, hfr⟩
      have hz43 : ‖z‖ = 4 / 3 := frontier_le_subset_eq continuous_norm continuous_const hfr
      have hle : ‖z‖ ≤ 5 / 3 := by rw [hz43]; norm_num
      simp only [hle, ↓reduceIte]
      rw [hz43, show (4 : ℝ) - 3 * (4 / 3) = 0 by norm_num,
        zero_mul, D.flow_zero, show (3 : ℝ) * (4 / 3) - 4 = 0 by norm_num]
    · rintro z ⟨-, hfr⟩
      have hz53 : ‖z‖ = 5 / 3 := frontier_le_subset_eq continuous_norm continuous_const hfr
      rw [hz53, show (3 : ℝ) * (5 / 3) - 5 = 0 by norm_num, zero_mul, D.flow_zero,
        show (3 : ℝ) * (5 / 3) - 4 = 1 by norm_num]
  · intro z hz
    have hz1 : 1 ≤ ‖z‖ := hz.1
    have hz2 : ‖z‖ ≤ 2 := hz.2
    have hu := hunitv z hz1
    unfold slideAnnulus
    rw [mem_preimage]
    split_ifs with h1 h2
    · have := (hband _ (htr_lev 0 _ hu) (hS0 _ hu) (4 - 3 * ‖z‖) ⟨by linarith, by linarith⟩).1
      exact ⟨by linarith [this.1], this.2⟩
    · rw [htr_lev _ _ hu]; exact ⟨hstrip.1, le_rfl⟩
    · have := (hband _ (htr_lev 1 _ hu) (hS1 _ hu) (3 * ‖z‖ - 5) ⟨by linarith, by linarith⟩).1
      exact ⟨by linarith [this.1], this.2⟩
  · rintro z ⟨hzb, hz⟩
    have hz1 : 1 ≤ ‖z‖ := hz.1
    have hu := hunitv z hz1
    unfold slideAnnulus
    rw [mem_preimage]
    rcases hzb with h | h
    · have hle : ‖z‖ ≤ 4 / 3 := by rw [h]; norm_num
      simp only [hle, ↓reduceIte]
      have := hband _ (htr_lev 0 _ hu) (hS0 _ hu) (4 - 3 * ‖z‖) ⟨by linarith, by linarith⟩
      rw [this.2 (by rw [h]; norm_num)]
      exact ⟨hac.le, le_rfl⟩
    · have hn1 : ¬ ‖z‖ ≤ 4 / 3 := by rw [h]; norm_num
      have hn2 : ¬ ‖z‖ ≤ 5 / 3 := by rw [h]; norm_num
      simp only [hn1, hn2, ↓reduceIte]
      have := hband _ (htr_lev 1 _ hu) (hS1 _ hu) (3 * ‖z‖ - 5) ⟨by linarith, by linarith⟩
      rw [this.2 (by rw [h]; norm_num)]
      exact ⟨hac.le, le_rfl⟩

theorem slideAnnulus_crossing {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ) {η η' : ℝ} (hη' : η' ≤ η)
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ η' K Hs) :
    ∃ z₀ : EuclideanSpace ℝ (Fin (ℓ + 1)), 4 / 3 < ‖z₀‖ ∧ ‖z₀‖ < 5 / 3 ∧
      D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) (‖z₀‖⁻¹ • z₀) = D.flow (-κ) (Ch.φ (slidePt (n - 1))) ∧
      Hs (3 * ‖z₀‖ - 4) (slidePt (n - 1)) ∈ slideB (n - 1) ℓ ∧
      (∀ z ∈ Handle.annulus (ℓ + 1), D.slideAnnulus Ch Hs q₁ ℓ ε c z ∈ D.slabCap (g q₂) → z = z₀) ∧
      D.slideAnnulus Ch Hs q₁ ℓ ε c z₀ ∈ D.captured q₂ hq₂ := by
  classical
  have _hcrit := hcrit
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  obtain ⟨hK, hKdom, -, hbij, -, hsupp, -, -, -, -, t₀, ht₀, ht₀B, huniq, -⟩ := hfin
  have hε : 0 < ε := hS.hε
  have hκ : 0 < κ := hS.hκ
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hcq₂ := hS.hcq₂
  have hac := hS.hac
  have hq₁b := hS.hq₁b
  have hk₁ : (D.chart q₁ hq₁).k = ℓ + 1 := hS.hk₁
  have hn1 : 0 < n - 1 := by have := hS.hℓn; omega
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 := D.hrm x hx
    have h3 := D.rm_pos x hx
    nlinarith
  have hεrm : ∀ x (hx : x ∈ crit), 2 * ε < D.rm x hx ^ 2 := fun x hx => by
    have := (hS.hεr x hx).2; linarith
  have hcoord0 : coordN (slidePt (n - 1)) 0 = 1 := by
    simp [coordN, slidePt, hn1]
  have hcoordj : ∀ j, 1 ≤ j → coordN (slidePt (n - 1)) j = 0 := by
    intro j hj
    unfold coordN slidePt
    split_ifs with h1 h2
    · simp at h2; omega
    · rfl
    · rfl
  have hAB : ∀ y, y ∈ slideA (n - 1) ℓ → y ∉ slideB (n - 1) ℓ := by
    intro y hA hB
    have := hA.1.symm.trans hB.1
    norm_num at this
  have hdom : slideDom (n - 1) η' ⊆ slideDom (n - 1) η := fun y hy =>
    ⟨hy.1, hy.2.1, fun j hj => (hy.2.2 j hj).trans_le hη'⟩
  have hKU : K ⊆ Ch.U := by rw [hCh.1]; exact hKdom.trans hdom
  have hKK : ∀ t, ∀ y ∈ K, Hs t y ∈ K := by
    intro t y hy
    by_contra h
    have h' := hsupp t (Hs t y) h
    have := (hbij t).1 h'
    exact h (by rw [this]; exact hy)
  have hPA : slidePt (n - 1) ∈ slideA (n - 1) ℓ :=
    ⟨hcoord0, fun j hj => hcoordj j (by omega)⟩
  have hPK : slidePt (n - 1) ∈ K := by
    by_contra h
    rw [hsupp t₀ _ h] at ht₀B
    exact hAB _ hPA ht₀B
  have hPU : slidePt (n - 1) ∈ Ch.U := hKU hPK
  have hlev_free : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hS.hunit y (Or.inr hy)
  have hRMS : ∀ z : Fin n → ℝ, morseNorm n z ≤ (D.chart q₂ hq₂).R →
      negPart (D.chart q₂ hq₂).hk z = 0 → g ((D.chart q₂ hq₂).χ z) = g q₂ + ε →
      z ∈ (D.chart q₂ hq₂).rightModelSphere ε := by
    intro z hzR hz0 hzg
    refine ⟨hz0, ?_⟩
    rw [(D.chart q₂ hq₂).hnorm z hzR, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hz0, norm_zero] at hzg
    have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
    linarith
  have hlvl : g q₂ + ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hdfV : ∀ y, g y = g q₂ + ε → dfV I g D.V y = -1 := by
    intro y hy
    refine D.dfV_eq_neg_one_of_level hlvl (fun p hp w hw hwg => ?_) hy
    exact hlev_free w (by rw [hwg]; exact ⟨le_rfl, by linarith⟩) p hp hw
  have hcapR : ∀ x, g x = c₂ → x ∈ D.captured q₂ hq₂ → x ∈ D.rightSphere q₂ hq₂ ε c₂ := by
    intro x hx hcap
    set d := D.chart q₂ hq₂ with hd
    have htr := (flow_level_transport (D := D) hf (c' := g q₂ + ε) (c := c₂) (by linarith)
      (by linarith) (by linarith) (fun y hy => hlev_free y ⟨hy.1, by linarith [hy.2]⟩)).1 x hx
    set x' := D.flow (c₂ - (g q₂ + ε)) x with hx'
    have hx'g : g x' = g q₂ + ε := htr.1
    have hx'cap : x' ∈ D.captured q₂ hq₂ := (flow_mem_captured_iff _).2 hcap
    rw [mem_rightSphere_iff]
    obtain ⟨T, y, ⟨hy1, hy2⟩, hyT⟩ := hx'cap
    have hyR : morseNorm n y ≤ d.R := hy1.le.trans (D.hrm q₂ hq₂).2
    rcases lt_or_ge T 0 with hT | hT
    · have hxy : x' = D.flow (-T) (d.χ y) := by rw [hyT, flow_neg_flow]
      obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ :=
        flow_mem_of_negPart_eq_zero hq₂ hy1 hy2 (t := -T) (by linarith)
      refine ⟨z, hRMS z (hz1.trans hyR) hz2 ?_, ?_⟩
      · rw [hzx, ← hxy, hx'g]
      · rw [hzx, ← hxy]
    · have hle : g (d.χ y) ≤ g q₂ + ε := by rw [hyT, ← hx'g]; exact f_flow_le hf x' hT
      by_cases hv : posPart d.hk y = 0
      · exfalso
        have hy0 : y = 0 := by
          have h1 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart d.hk y
          rw [hy2, hv, norm_zero] at h1
          have h2 : morseNorm n y = 0 := by
            have h3 : morseNorm n y ^ 2 = 0 := by rw [h1]; norm_num
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
          exact (ModelField.morseNorm_eq_zero_iff y).1 h2
        rw [hy0, d.hχ0] at hyT
        have : x' = q₂ := by rw [← D.flow_neg_flow x' T, ← hyT, D.flow_crit hq₂]
        rw [this] at hx'g
        linarith
      · obtain ⟨t, ht, htg, hball, hprod⟩ := exists_exit_asc hf hq₂ hε (y := y)
          (by rw [hy2, norm_zero]; have := hεrm q₂ hq₂; nlinarith) hv
          (by rw [← d.hnorm y hyR]; exact hle)
        have hflow : D.flow (-t) (d.χ y) = D.flow (T + -t) x' := by rw [hyT, flow_flow]
        have hT0 : T + -t = 0 :=
          flow_level_unique hf hdfV (by rw [← hflow]; exact htg) (by rw [flow_zero]; exact hx'g)
        have hxx : D.flow (-t) (d.χ y) = x' := by rw [hflow, hT0, flow_zero]
        obtain ⟨w, hw, hwx⟩ := hball (-t) (left_mem_Icc.2 (by linarith))
        rw [hxx] at hwx
        have hwR : morseNorm n w ≤ d.R := by
          have hw' : morseNorm n w ^ 2 ≤ 2 * ε + 2 * ‖negPart d.hk y‖ ^ 2 := hw
          rw [hy2, norm_zero] at hw'
          refine MorseNormalChart.morseNorm_le_of_sq_le d.R_pos.le ?_
          have : 2 * ε ≤ d.R ^ 2 := hεR q₂ hq₂
          have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
          linarith
        have hsymm : d.χ.symm x' = w := by rw [← hwx]; exact d.χ.left_inv (d.hsrc w hwR)
        rw [hxx, hsymm, hy2, norm_zero] at hprod
        have hw0 : negPart d.hk w = 0 := by
          have h4 : ‖negPart d.hk w‖ ^ 2 = 0 := by
            have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
            rw [h00, zero_mul] at hprod
            nlinarith [sq_nonneg ‖negPart d.hk w‖]
          exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4)
        exact ⟨w, hRMS w hwR hw0 (by rw [hwx]; exact hx'g), hwx⟩
  have hRcap : ∀ x ∈ D.rightSphere q₂ hq₂ ε c₂, x ∈ D.captured q₂ hq₂ := by
    intro x hx
    rw [mem_rightSphere_iff] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyrm : morseNorm n y < D.rm q₂ hq₂ := by
      have h1 := (D.chart q₂ hq₂).morseNorm_sq_of_mem_rightModelSphere hy
      exact lt_of_pow_lt_pow_left₀ 2 (D.rm_pos q₂ hq₂).le (by rw [h1]; exact hεrm q₂ hq₂)
    exact (flow_mem_captured_iff _).1 (mem_captured_of_mem_stable ⟨y, ⟨hyrm, hy.1⟩, hyx⟩)
  have hsepr : ∀ x ∈ D.leftSphere q₁ hq₁ ε c₂, x ∉ D.captured q₂ hq₂ := by
    intro x hxL hcap
    have hxg : g x = c₂ := D.leftSphere_subset_level hf q₁ hq₁ (hεR q₁ hq₁)
      ⟨by linarith, by linarith⟩ (fun y hy => hlev_free y (by
        rw [uIcc_of_ge (by linarith)] at hy; exact ⟨by linarith [hy.1], hy.2⟩)) hxL
    exact Set.disjoint_left.1 hS.hdisj hxL (hcapR x hxg hcap)
  set d₁ := D.chart q₁ hq₁ with hd₁
  have hreidx : ∀ (u : EuclideanSpace ℝ (Fin (ℓ + 1))) (j : Fin d₁.k),
      (Handle.reidx u : Fin d₁.k → ℝ) j = u ⟨j, by have := j.isLt; omega⟩ := by
    intro u j
    have hj : (j : ℕ) < ℓ + 1 := by have := j.isLt; omega
    simp [Handle.reidx, hj]
  have hreidx_ne : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      (Handle.reidx u : Fin d₁.k → ℝ) ≠ 0 := by
    intro u hu h
    apply hu
    ext i
    have := congrFun h ⟨i, by have := i.isLt; omega⟩
    rw [hreidx] at this
    simpa using this
  have hσ : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u =
      D.flow (g q₁ - ε - (c₂ + κ)) (d₁.χ (d₁.sphereParam ε (Handle.reidx u))) := by
    intro u
    rw [leftSphereMap, dite_eq_left hq₁]
  have hLS : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) ∈ D.leftSphere q₁ hq₁ ε c₂ := by
    intro u hu
    rw [hσ, flow_flow]
    refine ⟨_, ⟨_, d₁.sphereParam_mem_leftModelSphere hε.le (hreidx_ne u hu), rfl⟩, ?_⟩
    congr 1
    ring
  have hinj : ∀ u u' : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖u‖ = 1 → ‖u'‖ = 1 →
      D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u' →
      u = u' := by
    intro u u' hu hu' h
    have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; norm_num at hu
    have hu0' : u' ≠ 0 := by intro h0; rw [h0, norm_zero] at hu'; norm_num at hu'
    rw [hσ, hσ] at h
    have h1 := D.flow_injective _ h
    have hsp : d₁.sphereParam ε (Handle.reidx u) = d₁.sphereParam ε (Handle.reidx u') := by
      have e1 := d₁.χ.left_inv (d₁.hsrc _
        (d₁.morseNorm_sphereParam_le hε.le (hεR q₁ hq₁) (hreidx_ne u hu0)))
      have e2 := d₁.χ.left_inv (d₁.hsrc _
        (d₁.morseNorm_sphereParam_le hε.le (hεR q₁ hq₁) (hreidx_ne u' hu0')))
      rw [← e1, ← e2, h1]
    have h2 := congrArg (negPart d₁.hk) hsp
    rw [d₁.negPart_sphereParam, d₁.negPart_sphereParam] at h2
    obtain ⟨α, hαdef⟩ : ∃ α, α = Real.sqrt (2 * ε) / ‖d₁.toE (Handle.reidx u)‖ := ⟨_, rfl⟩
    obtain ⟨β, hβdef⟩ : ∃ β, β = Real.sqrt (2 * ε) / ‖d₁.toE (Handle.reidx u')‖ := ⟨_, rfl⟩
    rw [← hαdef, ← hβdef] at h2
    have hα : 0 < α := hαdef ▸ div_pos (Real.sqrt_pos.2 (by linarith))
      (norm_pos_iff.2 (d₁.toE_ne_zero (hreidx_ne u hu0)))
    have hβ : 0 < β := hβdef ▸ div_pos (Real.sqrt_pos.2 (by linarith))
      (norm_pos_iff.2 (d₁.toE_ne_zero (hreidx_ne u' hu0')))
    have hcomp : ∀ i : Fin (ℓ + 1), α * u i = β * u' i := by
      intro i
      have := congrArg (fun v => v ⟨i, by have := i.isLt; omega⟩) h2
      simpa [MorseNormalChart.toE, hreidx] using this
    have hlin : u = (β / α) • u' := by
      ext i
      have := hcomp i
      simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    have hnorm : β / α = 1 := by
      have := congrArg norm hlin
      rw [norm_smul, hu, hu', Real.norm_eq_abs, abs_of_pos (div_pos hβ hα)] at this
      linarith
    rw [hlin, hnorm, one_smul]
  have hsurj : ∀ x ∈ D.leftSphere q₁ hq₁ ε c₂, ∃ u : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖u‖ = 1 ∧
      D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u = D.flow (-κ) x := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨hv0, hvw⟩ := d₁.sphereParam_of_mem hε hw
    obtain ⟨v, hvdef⟩ : ∃ v, v = (EuclideanSpace.equiv (Fin d₁.k) ℝ) (negPart d₁.hk w) :=
      ⟨_, rfl⟩
    rw [← hvdef] at hv0 hvw
    let u' : EuclideanSpace ℝ (Fin (ℓ + 1)) :=
      WithLp.toLp 2 (fun i => v ⟨i, by have := i.isLt; omega⟩)
    have hru' : (Handle.reidx u' : Fin d₁.k → ℝ) = v := by
      funext j
      rw [hreidx]
    have hu'0 : u' ≠ 0 := by
      intro h
      apply hv0
      rw [← hru', h]
      funext j
      simp [Handle.reidx]
    refine ⟨‖u'‖⁻¹ • u', ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu'0)]
    · have hr : (Handle.reidx (‖u'‖⁻¹ • u') : Fin d₁.k → ℝ) = ‖u'‖⁻¹ • v := by
        funext j
        rw [hreidx, Pi.smul_apply, ← hru', hreidx]
        simp
      rw [hσ, hr, d₁.sphereParam_smul ε (inv_pos.2 (norm_pos_iff.2 hu'0)) hv0, hvw, flow_flow]
      congr 1
      ring
  have htrack_if : ∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin (ℓ + 1))) (y : Fin (n - 1) → ℝ),
      y ∈ Ch.U → D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u →
      D.slideTrack Ch Hs q₁ ℓ ε t u = D.flow κ (Ch.φ (Hs t y)) := by
    intro t u y hy hyu
    have hex : ∃ y, y ∈ Ch.U ∧
        D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u := ⟨y, hy, hyu⟩
    rw [slideTrack, dite_eq_left hex]
    have hc := Classical.choose_spec hex
    have : Classical.choose hex = y := Ch.inj hc.1 hy (D.flow_injective _ (hc.2.trans hyu.symm))
    rw [this]
  have htrack_else : ∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin (ℓ + 1))),
      (¬ ∃ y, y ∈ Ch.U ∧ D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) →
      D.slideTrack Ch Hs q₁ ℓ ε t u =
        D.flow (2 * κ) (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) := by
    intro t u h
    rw [slideTrack, dite_eq_right h]
  have hkey : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖u‖ = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
      D.slideTrack Ch Hs q₁ ℓ ε t u ∈ D.captured q₂ hq₂ →
      t = t₀ ∧ D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u = D.flow (-κ) (Ch.φ (slidePt (n - 1))) := by
    intro u hu t ht hcap
    have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; norm_num at hu
    by_cases hex : ∃ y, y ∈ Ch.U ∧
        D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u
    · obtain ⟨y, hyU, hyu⟩ := hex
      rw [htrack_if t u y hyU hyu, flow_mem_captured_iff] at hcap
      have hφy : Ch.φ y = D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) := by
        rw [← hyu, flow_flow, neg_add_cancel, flow_zero]
      have hyL : Ch.φ y ∈ D.leftSphere q₁ hq₁ ε c₂ := by rw [hφy]; exact hLS u hu0
      have hyD : y ∈ slideDom (n - 1) η := by rw [← hCh.1]; exact hyU
      have hyA : y ∈ slideA (n - 1) ℓ := (hCh.2.1 y hyD).1 hyL
      have hyK : y ∈ K := by
        by_contra hyK
        rw [hsupp t y hyK] at hcap
        exact hsepr _ hyL hcap
      have hHU : Hs t y ∈ Ch.U := hKU (hKK t y hyK)
      have hHR := hcapR _ (Ch.level _ hHU) hcap
      have hHB : Hs t y ∈ slideB (n - 1) ℓ :=
        (hCh.2.2 _ (by rw [← hCh.1]; exact hHU)).1 hHR
      obtain ⟨rfl, rfl⟩ := huniq t ht y hyA (hKdom hyK) hHB
      exact ⟨rfl, hyu.symm⟩
    · rw [htrack_else t u hex, show 2 * κ = κ + κ by ring, ← flow_flow,
        flow_mem_captured_iff] at hcap
      exact absurd hcap (hsepr _ (hLS u hu0))
  have hφA : Ch.φ (slidePt (n - 1)) ∈ D.leftSphere q₁ hq₁ ε c₂ :=
    (hCh.2.1 _ (by rw [← hCh.1]; exact hPU)).2 hPA
  obtain ⟨uA, huA, hσA⟩ := hsurj _ hφA
  have ht₀pos : 0 < (4 + t₀) / 3 := by linarith [ht₀.1]
  refine ⟨((4 + t₀) / 3) • uA, ?_⟩
  have hnz : ‖((4 + t₀) / 3) • uA‖ = (4 + t₀) / 3 := by
    rw [norm_smul, huA, mul_one, Real.norm_eq_abs, abs_of_pos ht₀pos]
  have hnu : ‖((4 + t₀) / 3) • uA‖⁻¹ • (((4 + t₀) / 3) • uA) = uA := by
    rw [hnz, smul_smul, inv_mul_cancel₀ ht₀pos.ne', one_smul]
  refine ⟨by rw [hnz]; linarith [ht₀.1], by rw [hnz]; linarith [ht₀.2], by rw [hnu, hσA],
    by rw [hnz, show 3 * ((4 + t₀) / 3) - 4 = t₀ by ring]; exact ht₀B, ?_, ?_⟩
  · intro z hz hzcap
    have hzcap' : D.slideAnnulus Ch Hs q₁ ℓ ε c z ∈ D.captured q₂ hq₂ := by
      simp only [slabCap, mem_iUnion] at hzcap
      obtain ⟨x, hx, hxg, hxc⟩ := hzcap
      have : x = q₂ := hS.hslab x hx ⟨by linarith, by linarith⟩
      subst this
      exact hxc
    have hz1 : 1 ≤ ‖z‖ := hz.1
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; norm_num at hz1
    have hnpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hu : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
    rw [slideAnnulus] at hzcap'
    split_ifs at hzcap' with h1 h2
    · rw [flow_mem_captured_iff] at hzcap'
      have := (hkey _ hu 0 ⟨le_rfl, zero_le_one⟩ hzcap').1
      linarith [ht₀.1]
    · have hk := hkey _ hu (3 * ‖z‖ - 4) ⟨by linarith, by linarith⟩ hzcap'
      have hzeq : ‖z‖⁻¹ • z = uA := hinj _ _ hu huA (hk.2.trans hσA.symm)
      have hnorm : ‖z‖ = (4 + t₀) / 3 := by linarith [hk.1]
      calc z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
        _ = ((4 + t₀) / 3) • uA := by rw [hzeq, hnorm]
    · rw [flow_mem_captured_iff] at hzcap'
      have := (hkey _ hu 1 ⟨zero_le_one, le_rfl⟩ hzcap').1
      linarith [ht₀.2]
  · rw [slideAnnulus, ite_eq_right (by rw [hnz]; linarith [ht₀.1]),
      ite_eq_left (by rw [hnz]; linarith [ht₀.2]), hnu, htrack_if _ uA _ hPU hσA.symm,
      flow_mem_captured_iff, hnz, show 3 * ((4 + t₀) / 3) - 4 = t₀ by ring]
    have hHU : Hs t₀ (slidePt (n - 1)) ∈ Ch.U := hKU (hKK t₀ _ hPK)
    exact hRcap _ ((hCh.2.2 _ (by rw [← hCh.1]; exact hHU)).2 ht₀B)

theorem slideAnnulus_det {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ) {η η' : ℝ} (hη' : η' ≤ η)
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ η' K Hs)
    {z₀ : EuclideanSpace ℝ (Fin (ℓ + 1))} (hz₀ : 4 / 3 < ‖z₀‖ ∧ ‖z₀‖ < 5 / 3)
    (hzA : D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) (‖z₀‖⁻¹ • z₀) = D.flow (-κ) (Ch.φ (slidePt (n - 1))))
    (hzB : Hs (3 * ‖z₀‖ - 4) (slidePt (n - 1)) ∈ slideB (n - 1) ℓ) :
    ContDiffAt ℝ 1 (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ ∧
      LinearMap.det (fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ :
        EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) ≠ 0 := by
  classical
  have _instE : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (ℓ + 1))) := IsBoundedSMul.continuousSMul
  have _hcrit := hcrit
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  obtain ⟨hK, hKdom, hHsC, hbij, -, hsupp, -, -, hHscoord, -, t₀, ht₀, ht₀B, huniq, hderiv⟩ := hfin
  have hε : 0 < ε := hS.hε
  have hκ : 0 < κ := hS.hκ
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hk₁ : (D.chart q₁ hq₁).k = ℓ + 1 := hS.hk₁
  have hk₂ : (D.chart q₂ hq₂).k = ℓ + 1 := hS.hk₂
  have hℓn := hS.hℓn
  have hℓ2 := hS.hℓ
  have hn1 : 0 < n - 1 := by omega
  have hℓlt : ℓ < n - 1 := by omega
  have hin : ∀ i : Fin (ℓ + 1), (i : ℕ) < n := fun i => lt_of_lt_of_le i.isLt (by omega)
  have hin' : ∀ i : Fin (ℓ + 1), (i : ℕ) < n - 1 := fun i => lt_of_lt_of_le i.isLt hℓlt
  have hstrip := Ch.strip
  have hac := hS.hac
  have hcq₂ := hS.hcq₂
  have hq₁b := hS.hq₁b
  have hq₂ab := ((hcrit q₂).1 hq₂).1
  have hq₁ab := D.f_mem_Ioo q₁ hq₁
  have hεR' : ∀ x (hx : x ∈ crit), 2 * ε < (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h4 : D.rm x hx ^ 2 ≤ (D.chart x hx).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos x hx).le (D.hrm x hx).2 2
    linarith only [h1, h4, hε]
  have hεR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := fun x hx => (hεR' x hx).le
  have hcoord0 : coordN (slidePt (n - 1)) 0 = 1 := by
    simp [coordN, slidePt, hn1]
  have hcoordj : ∀ j, 1 ≤ j → coordN (slidePt (n - 1)) j = 0 := by
    intro j hj
    unfold coordN slidePt
    split_ifs with h1 h2
    · simp at h2; omega
    · rfl
    · rfl
  have hAB : ∀ y, y ∈ slideA (n - 1) ℓ → y ∉ slideB (n - 1) ℓ := by
    intro y hA hB
    have := hA.1.symm.trans hB.1
    norm_num at this
  have hdom : slideDom (n - 1) η' ⊆ slideDom (n - 1) η := fun y hy =>
    ⟨hy.1, hy.2.1, fun j hj => (hy.2.2 j hj).trans_le hη'⟩
  have hKU : K ⊆ Ch.U := by rw [hCh.1]; exact hKdom.trans hdom
  have hKK : ∀ t, ∀ y ∈ K, Hs t y ∈ K := by
    intro t y hy
    by_contra h
    have h' := hsupp t (Hs t y) h
    have := (hbij t).1 h'
    exact h (by rw [this]; exact hy)
  have hHsU : ∀ t, ∀ y ∈ Ch.U, Hs t y ∈ Ch.U := by
    intro t y hy
    by_cases hyK : y ∈ K
    · exact hKU (hKK t y hyK)
    · rw [hsupp t y hyK]; exact hy
  have hPA : slidePt (n - 1) ∈ slideA (n - 1) ℓ :=
    ⟨hcoord0, fun j hj => hcoordj j (by omega)⟩
  have hPK : slidePt (n - 1) ∈ K := by
    by_contra h
    rw [hsupp t₀ _ h] at ht₀B
    exact hAB _ hPA ht₀B
  have hPU : slidePt (n - 1) ∈ Ch.U := hKU hPK
  have hnz₀ : 0 < ‖z₀‖ := lt_trans (by norm_num) hz₀.1
  have hz₀ne : z₀ ≠ 0 := norm_pos_iff.1 hnz₀
  have ht₀eq : 3 * ‖z₀‖ - 4 = t₀ := by
    by_cases hmem : 3 * ‖z₀‖ - 4 ∈ Icc (0 : ℝ) 1
    · exact (huniq _ hmem _ hPA (hKdom hPK) hzB).1
    · exfalso; exact hmem ⟨by linarith only [hz₀.1], by linarith only [hz₀.2]⟩
  rw [ht₀eq] at hzB
  have hU' : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x (hx : x ∈ crit), y ∉ D.smallBall x hx :=
    fun y hy => hS.hunit y (Or.inr hy)
  have htrans : ∀ c₁ c₃ : ℝ, g q₂ + ε ≤ c₁ → c₁ ≤ c₃ → c₃ ≤ g q₁ - ε → ∀ x, g x = c₃ →
      g (D.flow (c₃ - c₁) x) = c₁ := by
    intro c₁ c₃ h1 h13 h3 x hx
    exact ((flow_level_transport (D := D) hf (by linarith only [hac, hcq₂, h1, hε]) h13
      (by linarith only [h3, hq₁b, hε])
      (fun y hy p hp => hU' y ⟨by linarith only [hy.1, h1], by linarith only [hy.2, h3]⟩ p
        hp)).1 x hx).1
  have hcol : ∀ y ∈ Ch.U, ∀ s ∈ Icc (-κ) κ, g (D.flow s (Ch.φ y)) = c₂ - s := by
    intro y hy s hs
    have hlev := Ch.level y hy
    have havoid : ∀ s' ∈ uIcc 0 s, ∀ (p : M) (hp : p ∈ crit),
        D.flow s' (Ch.φ y) ∉ D.smallBall p hp := by
      intro s' hs' p hp hmem
      have hs'' : s' ∈ Icc (-κ) κ :=
        uIcc_subset_Icc ⟨neg_nonpos.2 hκ.le, hκ.le⟩ hs hs'
      exact Ch.avoid y hy s' hs'' p hp
        (image_mono (fun z (hz : morseNorm n z < _) => hz.trans (D.r₀_lt_rm p hp)) hmem)
    have := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := s)
      (by rw [hlev]; exact ⟨by linarith only [hstrip.1, hκ], by linarith only [hstrip.2, hκ]⟩)
      (by rw [hlev]; exact ⟨by linarith only [hstrip.1, hs.2], by linarith only [hstrip.2, hs.1]⟩)
      havoid s right_mem_uIcc
    rw [this, hlev]
  set d₁ := D.chart q₁ hq₁ with hd₁
  set d₂ := D.chart q₂ hq₂ with hd₂
  obtain ⟨σ, hσdef⟩ : ∃ σ : EuclideanSpace ℝ (Fin (ℓ + 1)) → M,
      σ = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) := ⟨_, rfl⟩
  rw [← hσdef] at hzA
  have hreidx : ∀ (u : EuclideanSpace ℝ (Fin (ℓ + 1))) (j : Fin d₁.k),
      (Handle.reidx u : Fin d₁.k → ℝ) j = u ⟨j, by have := j.isLt; omega⟩ := by
    intro u j
    have hj : (j : ℕ) < ℓ + 1 := by have := j.isLt; omega
    simp [Handle.reidx, hj]
  have hreidx_ne : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      (Handle.reidx u : Fin d₁.k → ℝ) ≠ 0 := by
    intro u hu h
    apply hu
    ext i
    have := congrFun h ⟨i, by have := i.isLt; omega⟩
    rw [hreidx] at this
    simpa using this
  have hσeq : ∀ u, σ u = D.flow (g q₁ - ε - (c₂ + κ)) (d₁.χ (d₁.sphereParam ε (Handle.reidx u))) := by
    intro u
    rw [hσdef, leftSphereMap, dite_eq_left hq₁]
  have hσL : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      D.flow κ (σ u) ∈ D.leftSphere q₁ hq₁ ε c₂ := by
    intro u hu
    rw [hσeq, flow_flow]
    refine ⟨_, ⟨_, d₁.sphereParam_mem_leftModelSphere hε.le (hreidx_ne u hu), rfl⟩, ?_⟩
    congr 1
    ring
  have hσlev : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 → ∀ s ∈ Icc 0 (2 * κ),
      g (D.flow s (σ u)) = c₂ + κ - s := by
    intro u hu s hs
    have hL : D.flow s (σ u) ∈ D.leftSphere q₁ hq₁ ε (c₂ + κ - s) := by
      rw [hσeq, flow_flow]
      refine ⟨_, ⟨_, d₁.sphereParam_mem_leftModelSphere hε.le (hreidx_ne u hu), rfl⟩, ?_⟩
      congr 1
      ring
    have hsub := D.leftSphere_subset_level hf q₁ hq₁ (hεR q₁ hq₁) (c := c₂ + κ - s)
      ⟨by linarith only [hs.2, hstrip.1], by linarith only [hs.1, hstrip.2]⟩ (fun y hy p hp =>
        hU' y (by
        rw [uIcc_of_ge (by linarith only [hs.1, hc₂q₁])] at hy
        exact ⟨by linarith only [hy.1, hs.2, hq₂c₂], hy.2⟩) p hp)
    exact hsub hL
  obtain ⟨hopen, inv, hinvC, hinv⟩ := Ch.exists_boxInverse hf
  obtain ⟨B, hBdef⟩ : ∃ B : Set M,
      B = (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) '' (Ch.U ×ˢ Ioo (-κ) κ) :=
    ⟨_, rfl⟩
  rw [← hBdef] at hinvC
  have hBopen : IsOpen B := by
    rw [hBdef]; exact hopen _ subset_rfl (Ch.isOpen_U.prod isOpen_Ioo)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : EuclideanSpace ℝ (Fin (ℓ + 1)) → (Fin (n - 1) → ℝ),
      ψ = fun u => (inv (D.flow (κ / 2) (σ u))).1 := ⟨_, rfl⟩
  have hψ : ∀ u, u ≠ 0 → D.flow (κ / 2) (σ u) ∈ B →
      ψ u ∈ Ch.U ∧ D.flow (-κ) (Ch.φ (ψ u)) = σ u := by
    intro u hu0 hpB
    rw [hBdef] at hpB
    obtain ⟨⟨y', s'⟩, ⟨hy'U, hs'⟩, hbox⟩ := hpB
    dsimp only at hbox
    have hl1 := hcol y' hy'U s' ⟨hs'.1.le, hs'.2.le⟩
    have hl2 : g (D.flow (κ / 2) (σ u)) = c₂ + κ - κ / 2 :=
      hσlev u hu0 (κ / 2) ⟨by linarith only [hκ], by linarith only [hκ]⟩
    rw [← hbox, hl1] at hl2
    have hs'eq : s' = -(κ / 2) := by linarith only [hl2]
    subst hs'eq
    have hyσ : D.flow (-κ) (Ch.φ y') = σ u := by
      have := congrArg (D.flow (-(κ / 2))) hbox
      rw [D.flow_neg_flow, flow_flow] at this
      rw [← this]; congr 1; ring
    have hinv' := hinv (y', -(κ / 2)) ⟨hy'U, hs'⟩
    dsimp only at hinv'
    have hψu : ψ u = y' := by rw [hψdef]; dsimp only; rw [← hbox, hinv']
    rw [hψu]
    exact ⟨hy'U, hyσ⟩
  set u₀ : EuclideanSpace ℝ (Fin (ℓ + 1)) := ‖z₀‖⁻¹ • z₀ with hu₀def
  have hu₀1 : ‖u₀‖ = 1 := by
    rw [hu₀def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz₀.ne']
  have hu₀ne : u₀ ≠ 0 := by intro h; rw [h, norm_zero] at hu₀1; norm_num at hu₀1
  have hκmem : -(κ / 2) ∈ Ioo (-κ) κ := ⟨by linarith only [hκ], by linarith only [hκ]⟩
  have hGu₀ : D.flow (κ / 2) (σ u₀) = D.flow (-(κ / 2)) (Ch.φ (slidePt (n - 1))) := by
    rw [hzA, flow_flow]; congr 1; ring
  have hB₀ : D.flow (κ / 2) (σ u₀) ∈ B := by
    rw [hBdef]; exact ⟨(slidePt (n - 1), -(κ / 2)), ⟨hPU, hκmem⟩, hGu₀.symm⟩
  have hψu₀ : ψ u₀ = slidePt (n - 1) := by
    have := hinv (slidePt (n - 1), -(κ / 2)) ⟨hPU, hκmem⟩
    dsimp only at this
    rw [hψdef]; dsimp only; rw [hGu₀, this]
  have htrack_if : ∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin (ℓ + 1))) (y : Fin (n - 1) → ℝ),
      y ∈ Ch.U → D.flow (-κ) (Ch.φ y) = σ u →
      D.slideTrack Ch Hs q₁ ℓ ε t u = D.flow κ (Ch.φ (Hs t y)) := by
    intro t u y hy hyu
    rw [hσdef] at hyu
    have hex : ∃ y, y ∈ Ch.U ∧
        D.flow (-κ) (Ch.φ y) = D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u := ⟨y, hy, hyu⟩
    rw [slideTrack, dite_eq_left hex]
    have hc := Classical.choose_spec hex
    have : Classical.choose hex = y := Ch.inj hc.1 hy (D.flow_injective _ (hc.2.trans hyu.symm))
    rw [this]
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] (Fin d₁.k → ℝ),
      ∀ u, R₁ u = Handle.reidx u :=
    ⟨ContinuousLinearMap.pi fun i : Fin d₁.k => if h : (i : ℕ) < ℓ + 1 then
      EuclideanSpace.proj (⟨i, h⟩ : Fin (ℓ + 1)) else 0, fun u => by
        funext i
        by_cases h : (i : ℕ) < ℓ + 1
        · simp only [ContinuousLinearMap.pi_apply, Handle.reidx, dite_eq_left h]; rfl
        · simp only [ContinuousLinearMap.pi_apply, Handle.reidx, dite_eq_right h]; rfl⟩
  have hSmem : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      d₁.sphereParam ε (Handle.reidx u) ∈ Metric.ball (0 : Fin n → ℝ) d₁.R' := fun u hu =>
    d₁.mem_ball_of_le (d₁.morseNorm_sphereParam_le hε.le (hεR q₁ hq₁) (hreidx_ne u hu))
  have hSsrc : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      d₁.χ.symm (d₁.χ (d₁.sphereParam ε (Handle.reidx u))) = d₁.sphereParam ε (Handle.reidx u) :=
    fun u hu => d₁.χ.left_inv (d₁.hball (hSmem u hu))
  have hSC : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) =>
      d₁.sphereParam ε (Handle.reidx u)) u₀ := by
    have e : (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) => d₁.sphereParam ε (Handle.reidx u)) =
        d₁.sphereParam ε ∘ R₁ := by funext u; simp [hR₁]
    rw [e]
    exact ContDiffAt.comp u₀ (by rw [hR₁]; exact d₁.contDiffAt_sphereParam ε (hreidx_ne u₀ hu₀ne))
      R₁.contDiff.contDiffAt
  have hσC : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (ℓ + 1))) I ∞ σ u₀ := by
    have e : σ = D.flow (g q₁ - ε - (c₂ + κ)) ∘ (d₁.χ ∘
        (fun u : EuclideanSpace ℝ (Fin (ℓ + 1)) => d₁.sphereParam ε (Handle.reidx u))) :=
      funext hσeq
    rw [e]
    exact ((D.contMDiff_flow _) _).comp u₀ ((d₁.contMDiffAt_chart (hSmem u₀ hu₀ne)).comp u₀
      (contMDiffAt_iff_contDiffAt.2 hSC))
  have hψC : ContDiffAt ℝ ∞ ψ u₀ := by
    rw [← contMDiffAt_iff_contDiffAt]
    have e : ψ = Prod.fst ∘ (inv ∘ (D.flow (κ / 2) ∘ σ)) := by rw [hψdef]; rfl
    rw [e]
    refine (contDiff_fst.contMDiff _).comp u₀ ?_
    exact (hinvC.contMDiffAt (hBopen.mem_nhds hB₀)).comp u₀ (((D.contMDiff_flow _) _).comp u₀ hσC)
  have hRMS_R : ∀ m ∈ d₂.rightModelSphere ε, morseNorm n m ≤ d₂.R := by
    intro m hm
    refine MorseNormalChart.morseNorm_le_of_sq_le d₂.R_pos.le ?_
    rw [d₂.morseNorm_sq_of_mem_rightModelSphere hm]
    exact hεR q₂ hq₂
  have hRS : ∀ y ∈ Ch.U, y ∈ slideB (n - 1) ℓ → ∃ m ∈ d₂.rightModelSphere ε,
      D.flow (c₂ - (g q₂ + ε)) (Ch.φ y) = d₂.χ m := by
    intro y hyU hyB
    have h1 : Ch.φ y ∈ D.rightSphere q₂ hq₂ ε c₂ :=
      (hCh.2.2 y (by rw [← hCh.1]; exact hyU)).2 hyB
    rw [mem_rightSphere_iff] at h1
    obtain ⟨m, hm, hmx⟩ := h1
    exact ⟨m, hm, hmx.symm⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : (Fin (n - 1) → ℝ) → (Fin n → ℝ),
      Φ = fun w => d₂.χ.symm (D.flow (c₂ - (g q₂ + ε)) (Ch.φ w)) := ⟨_, rfl⟩
  obtain ⟨Φ₁, hΦ₁def⟩ : ∃ Φ₁ : (Fin (n - 1) → ℝ) → (Fin n → ℝ),
      Φ₁ = fun w => d₁.χ.symm (D.flow (-(g q₁ - ε - (c₂ + κ) + κ)) (Ch.φ w)) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : EuclideanSpace ℝ (Fin (ℓ + 1)) → (Fin (n - 1) → ℝ),
      G = fun z => Hs (3 * ‖z‖ - 4) (ψ (‖z‖⁻¹ • z)) := ⟨_, rfl⟩
  set p : Fin (n - 1) → ℝ := Hs t₀ (slidePt (n - 1)) with hpdef
  have hGz₀ : G z₀ = p := by rw [hGdef]; dsimp only; rw [ht₀eq, hψu₀]
  have hpU : p ∈ Ch.U := hKU (hKK t₀ _ hPK)
  obtain ⟨m₀, hm₀, hm₀x⟩ := hRS p hpU hzB
  have hm₀src : m₀ ∈ d₂.χ.source := d₂.hsrc m₀ (hRMS_R m₀ hm₀)
  have hΦp : Φ p = m₀ := by rw [hΦdef]; dsimp only; rw [hm₀x, d₂.χ.left_inv hm₀src]
  have hx₂ : D.flow (c₂ - (g q₂ + ε)) (Ch.φ p) ∈ d₂.χ '' Metric.ball 0 d₂.R' := by
    rw [hm₀x]; exact ⟨m₀, d₂.mem_ball_of_le (hRMS_R m₀ hm₀), rfl⟩
  have hΦM : ContMDiffAt 𝓘(ℝ, Fin (n - 1) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ Φ p := by
    have e : Φ = d₂.χ.symm ∘ (D.flow (c₂ - (g q₂ + ε)) ∘ Ch.φ) := by rw [hΦdef]; rfl
    rw [e]
    exact (d₂.contMDiffAt_symm hx₂).comp p (((D.contMDiff_flow _) _).comp p
      (Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hpU)))
  have hΦC : ContDiffAt ℝ ∞ Φ p := contMDiffAt_iff_contDiffAt.1 hΦM
  have hφP : Ch.φ (slidePt (n - 1)) = D.flow κ (σ u₀) := by rw [hzA, flow_flow_neg]
  have hx₁ : D.flow (-(g q₁ - ε - (c₂ + κ) + κ)) (Ch.φ (slidePt (n - 1))) =
      d₁.χ (d₁.sphereParam ε (Handle.reidx u₀)) := by
    rw [hφP, hσeq, flow_flow, flow_flow, show g q₁ - ε - (c₂ + κ) + (κ + -(g q₁ - ε - (c₂ + κ) + κ))
      = 0 by ring, flow_zero]
  have hΦ₁M : ContMDiffAt 𝓘(ℝ, Fin (n - 1) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ Φ₁ (slidePt (n - 1)) := by
    have e : Φ₁ = d₁.χ.symm ∘ (D.flow (-(g q₁ - ε - (c₂ + κ) + κ)) ∘ Ch.φ) := by rw [hΦ₁def]; rfl
    rw [e]
    refine (d₁.contMDiffAt_symm ?_).comp (slidePt (n - 1)) (((D.contMDiff_flow _) _).comp _
      (Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hPU)))
    simp only [Function.comp_apply]
    rw [hx₁]; exact ⟨_, hSmem u₀ hu₀ne, rfl⟩
  have hΦ₁C : ContDiffAt ℝ ∞ Φ₁ (slidePt (n - 1)) := contMDiffAt_iff_contDiffAt.1 hΦ₁M
  have hNC : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ :=
    ((contDiffAt_norm ℝ hz₀ne).inv hnz₀.ne').smul contDiffAt_id
  have hGC : ContDiffAt ℝ ∞ G z₀ := by
    have e : G = (fun q : ℝ × (Fin (n - 1) → ℝ) => Hs q.1 q.2) ∘
        (fun z => (3 * ‖z‖ - 4, ψ (‖z‖⁻¹ • z))) := by rw [hGdef]; rfl
    rw [e]
    refine hHsC.contDiffAt.comp z₀ (ContDiffAt.prodMk ?_ ?_)
    · exact (contDiffAt_const.mul (contDiffAt_norm ℝ hz₀ne)).sub contDiffAt_const
    · exact ContDiffAt.comp (g := ψ) z₀ hψC hNC
  have hgood : ∀ᶠ z in 𝓝 z₀, 4 / 3 < ‖z‖ ∧ ‖z‖ < 5 / 3 ∧
      D.flow (κ / 2) (σ (‖z‖⁻¹ • z)) ∈ B := by
    have h1 : ∀ᶠ z in 𝓝 z₀, 4 / 3 < ‖z‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds hz₀.1)
    have h2 : ∀ᶠ z in 𝓝 z₀, ‖z‖ < 5 / 3 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hz₀.2)
    have hc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) =>
        D.flow (κ / 2) (σ (‖z‖⁻¹ • z))) z₀ :=
      (D.continuous_flow _).continuousAt.comp
        (ContinuousAt.comp (x := z₀) hσC.continuousAt hNC.continuousAt)
    have h3 := hc.eventually (hBopen.mem_nhds hB₀)
    filter_upwards [h1, h2, h3] with z ha hb hc' using ⟨ha, hb, hc'⟩
  have hunitN : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), 0 < ‖z‖ → ‖‖z‖⁻¹ • z‖ = 1 := by
    intro z hz
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz.ne']
  have hunitN0 : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), 0 < ‖z‖ → ‖z‖⁻¹ • z ≠ 0 := by
    intro z hz h
    have := hunitN z hz
    rw [h, norm_zero] at this
    norm_num at this
  have hann : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), 4 / 3 < ‖z‖ → ‖z‖ < 5 / 3 →
      D.flow (κ / 2) (σ (‖z‖⁻¹ • z)) ∈ B →
      D.slideAnnulus Ch Hs q₁ ℓ ε c z = D.flow κ (Ch.φ (G z)) ∧ G z ∈ Ch.U := by
    intro z h1 h2 h3
    have hz0 : 0 < ‖z‖ := by linarith only [h1]
    obtain ⟨hψU, hψσ⟩ := hψ _ (hunitN0 z hz0) h3
    refine ⟨?_, by rw [hGdef]; exact hHsU _ _ hψU⟩
    rw [slideAnnulus, ite_eq_right (not_le.2 h1), ite_eq_left h2.le, htrack_if _ _ _ hψU hψσ, hGdef]
  obtain ⟨RLc, hRLc⟩ : ∃ RLc : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
      ∀ x, RLc x = WithLp.toLp 2 (fun i : Fin (ℓ + 1) =>
        if h : (i : ℕ) < d₂.k then negPart d₂.hk x ⟨i, h⟩ else 0) :=
    ⟨(EuclideanSpace.equiv (Fin (ℓ + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun i : Fin (ℓ + 1) => if h : (i : ℕ) < d₂.k then
        (EuclideanSpace.proj (⟨i, h⟩ : Fin d₂.k)).comp (ModelField.negPartL d₂.hk) else 0),
      fun x => by
        ext i
        by_cases h : (i : ℕ) < d₂.k
        · simp [h]
        · simp [h]⟩
  have htube : ∀ w ∈ Ch.U, D.tubeCoordE q₂ hq₂ ε (ℓ + 1) (D.flow κ (Ch.φ w)) = RLc (Φ w) := by
    intro w hw
    have hlev : g (D.flow κ (Ch.φ w)) = c₂ - κ := hcol w hw κ ⟨by linarith only [hκ], le_rfl⟩
    have hx : D.flow (g (D.flow κ (Ch.φ w)) - (g q₂ + ε)) (D.flow κ (Ch.φ w)) =
        D.flow (c₂ - (g q₂ + ε)) (Ch.φ w) := by
      rw [hlev, flow_flow]; congr 1; ring
    have hle : g q₂ + ε ≤ g (D.flow κ (Ch.φ w)) := by rw [hlev]; linarith only [hq₂c₂]
    rw [hRLc, hΦdef]
    simp only [tubeCoordE, tubeCoord, ite_eq_left hle, rightCoord, hx]
    rfl
  have hΨeq : (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) =ᶠ[𝓝 z₀]
      (RLc ∘ Φ) ∘ G := by
    filter_upwards [hgood] with z hz
    obtain ⟨h1, h2⟩ := hann z hz.1 hz.2.1 hz.2.2
    simp only [Function.comp_apply]
    rw [h1, htube _ h2]
  have hG' : HasFDerivAt G (fderiv ℝ G z₀) z₀ := (hGC.differentiableAt (by simp)).hasFDerivAt
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ p) p := (hΦC.differentiableAt (by simp)).hasFDerivAt
  have hΦ'' : HasFDerivAt Φ (fderiv ℝ Φ p) (G z₀) := by rw [hGz₀]; exact hΦ'
  have hD1 : Function.Injective (fderiv ℝ Φ p) := by
    have hφd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ p :=
      (Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hpU)).mdifferentiableAt (by simp)
    have hfl : ∀ t : ℝ, ∀ z : M, MDifferentiableAt I I (D.flow t) z :=
      fun t z => (D.contMDiff_flow t z).mdifferentiableAt (by simp)
    have hsd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) d₂.χ.symm
        (D.flow (c₂ - (g q₂ + ε)) (Ch.φ p)) := d₂.mdifferentiableAt_symm hx₂
    have hflinj : ∀ (s : ℝ) (x : M), Function.Injective (mfderiv I I (D.flow s) x) := by
      intro s x
      have hid : (D.flow (-s) ∘ D.flow s) = id := funext fun z => D.flow_neg_flow z s
      have hc := mfderiv_comp x (hfl (-s) (D.flow s x)) (hfl s x)
      rw [hid, mfderiv_id] at hc
      intro u₁ u₂ hu
      have e1 : u₁ = mfderiv I I (D.flow (-s)) (D.flow s x)
          (mfderiv I I (D.flow s) x u₁) := DFunLike.congr_fun hc u₁
      have e2 : u₂ = mfderiv I I (D.flow (-s)) (D.flow s x)
          (mfderiv I I (D.flow s) x u₂) := DFunLike.congr_fun hc u₂
      exact e1.trans ((congrArg (mfderiv I I (D.flow (-s)) (D.flow s x)) hu).trans e2.symm)
    have hsinj : Function.Injective (mfderiv I 𝓘(ℝ, Fin n → ℝ) d₂.χ.symm
        (D.flow (c₂ - (g q₂ + ε)) (Ch.φ p))) := by
      set x := D.flow (c₂ - (g q₂ + ε)) (Ch.φ p) with hxdef
      have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) x
        (d₂.mdifferentiableAt_chart (d₂.symm_mem_ball hx₂)) hsd
      have hev : (d₂.χ ∘ d₂.χ.symm) =ᶠ[𝓝 x] id :=
        eventuallyEq_of_mem (d₂.isOpen_image_ball.mem_nhds hx₂) fun y hy => d₂.symm_image_eq hy
      have h1 := hev.mfderiv_eq (I := I) (I' := I)
      rw [mfderiv_id] at h1
      intro u₁ u₂ hu
      have e1 : (mfderiv 𝓘(ℝ, Fin n → ℝ) I d₂.χ (d₂.χ.symm x))
          ((mfderiv I 𝓘(ℝ, Fin n → ℝ) d₂.χ.symm x) u₁) = u₁ :=
        DFunLike.congr_fun (hcomp.symm.trans h1) u₁
      have e2 : (mfderiv 𝓘(ℝ, Fin n → ℝ) I d₂.χ (d₂.χ.symm x))
          ((mfderiv I 𝓘(ℝ, Fin n → ℝ) d₂.χ.symm x) u₂) = u₂ :=
        DFunLike.congr_fun (hcomp.symm.trans h1) u₂
      rw [← e1, ← e2, hu]
    intro v₁ v₂ hv
    have e : Φ = d₂.χ.symm ∘ (D.flow (c₂ - (g q₂ + ε)) ∘ Ch.φ) := by rw [hΦdef]; rfl
    have hm : ∀ v, fderiv ℝ Φ p v = mfderiv I 𝓘(ℝ, Fin n → ℝ) d₂.χ.symm
        (D.flow (c₂ - (g q₂ + ε)) (Ch.φ p)) (mfderiv I I (D.flow (c₂ - (g q₂ + ε))) (Ch.φ p)
          (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Ch.φ p v)) := by
      intro v
      have h1 := mfderiv_comp (I := 𝓘(ℝ, Fin (n - 1) → ℝ)) (I' := I) (I'' := 𝓘(ℝ, Fin n → ℝ)) p
        hsd ((hfl _ _).comp p hφd)
      have h2 := mfderiv_comp (I := 𝓘(ℝ, Fin (n - 1) → ℝ)) (I' := I) (I'' := I) p
        (hfl (c₂ - (g q₂ + ε)) (Ch.φ p)) hφd
      rw [mfderiv_eq_fderiv] at h1
      rw [e]
      have h3 := DFunLike.congr_fun h1 v
      have h4 := DFunLike.congr_fun h2 v
      exact h3.trans (congrArg _ h4)
    rw [hm, hm] at hv
    exact Ch.immersion p hpU (hflinj _ _ (hsinj hv))
  have hm₀R : morseNorm n m₀ < d₂.R := by
    have h1 := d₂.morseNorm_sq_of_mem_rightModelSphere hm₀
    exact lt_of_pow_lt_pow_left₀ 2 d₂.R_pos.le (by rw [h1]; exact hεR' q₂ hq₂)
  have hΦlev : (morseNormalForm d₂.hk (g q₂) ∘ Φ) =ᶠ[𝓝 p] fun _ => g q₂ + ε := by
    have hc1 : ContinuousAt (fun w => D.flow (c₂ - (g q₂ + ε)) (Ch.φ w)) p :=
      (D.continuous_flow _).continuousAt.comp
        (Ch.smooth.continuousOn.continuousAt (Ch.isOpen_U.mem_nhds hpU))
    have e1 := hc1.eventually (d₂.isOpen_image_ball.mem_nhds hx₂)
    have e2 := hΦC.continuousAt.eventually ((isOpen_morseNorm_lt d₂.R).mem_nhds
      (show Φ p ∈ {y : Fin n → ℝ | morseNorm n y < d₂.R} by rw [hΦp]; exact hm₀R))
    have e3 := Ch.isOpen_U.mem_nhds hpU
    filter_upwards [e1, e2, e3] with w hw1 hw2 hw3
    simp only [Function.comp_apply]
    rw [← d₂.hnorm _ (le_of_lt hw2), hΦdef]
    dsimp only
    rw [d₂.symm_image_eq hw1]
    exact htrans (g q₂ + ε) c₂ le_rfl (by linarith only [hq₂c₂, hκ])
      (by linarith only [hc₂q₁, hκ]) _ (Ch.level w hw3)
  have hD2 : ∀ v, ModelField.nfDeriv d₂.hk m₀ (fderiv ℝ Φ p v) = 0 := by
    have h1 : HasFDerivAt (morseNormalForm d₂.hk (g q₂) ∘ Φ)
        ((ModelField.nfDeriv d₂.hk m₀).comp (fderiv ℝ Φ p)) p := by
      have := (ModelField.hasFDerivAt_nf d₂.hk (g q₂) (Φ p)).comp p hΦ'
      rw [hΦp] at this
      exact this
    have h2 : HasFDerivAt (morseNormalForm d₂.hk (g q₂) ∘ Φ) (0 : (Fin (n - 1) → ℝ) →L[ℝ] ℝ) p :=
      (hasFDerivAt_const _ _).congr_of_eventuallyEq hΦlev
    intro v
    have := h1.unique h2
    exact DFunLike.congr_fun this v
  have hcoordadd : ∀ (y w : Fin (n - 1) → ℝ) (s : ℝ) (j : ℕ),
      coordN (y + s • w) j = coordN y j + s * coordN w j := by
    intro y w s j
    unfold coordN
    split_ifs <;> simp
  have hD3 : ∀ w' : Fin (n - 1) → ℝ, (∀ j, j ≤ ℓ → coordN w' j = 0) →
      ∀ i : Fin n, (i : ℕ) < ℓ + 1 → fderiv ℝ Φ p w' i = 0 := by
    intro w' hw' i hi
    have hline : HasDerivAt (fun s : ℝ => p + s • w') w' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w').const_add p
    have h1 : HasDerivAt (fun s : ℝ => Φ (p + s • w') i) (fderiv ℝ Φ p w' i) 0 := by
      have := hΦ'.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) this
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), p + s • w' ∈ Ch.U := by
      have hc : ContinuousAt (fun s : ℝ => p + s • w') 0 := hline.continuousAt
      have : (fun s : ℝ => p + s • w') 0 = p := by simp
      exact hc.eventually (by rw [this]; exact Ch.isOpen_U.mem_nhds hpU)
    have hik : (i : ℕ) < d₂.k := by rw [hk₂]; exact hi
    have h2 : HasDerivAt (fun s : ℝ => Φ (p + s • w') i) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with s hs
      have hB : p + s • w' ∈ slideB (n - 1) ℓ := by
        refine ⟨?_, fun j hj1 hj2 => ?_⟩
        · rw [hcoordadd, hzB.1, hw' 0 (Nat.zero_le _)]; ring
        · rw [hcoordadd, hzB.2 j hj1 hj2, hw' j hj2]; ring
      obtain ⟨m, hm, hmx⟩ := hRS _ hs hB
      have hm0 : m i = 0 := by
        have := congrArg (fun u : EuclideanSpace ℝ (Fin d₂.k) => u ⟨i, hik⟩) hm.1
        exact this
      rw [hΦdef]
      dsimp only
      rw [hmx, d₂.χ.left_inv (d₂.hsrc m (hRMS_R m hm)), hm0]
    exact h1.unique h2
  have hD4 : ∀ x : Fin (ℓ + 1) → ℝ, ∃ w, ∀ i : Fin (ℓ + 1),
      fderiv ℝ Φ p w ⟨i, hin i⟩ = x i := by
    set L : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      ((fderiv ℝ Φ p : (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      with hL
    set Nf : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      ((ModelField.nfDeriv d₂.hk m₀ : (Fin n → ℝ) →L[ℝ] ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ) with hNf
    have hle : LinearMap.range L ≤ LinearMap.ker Nf := by
      rintro _ ⟨v, rfl⟩
      exact hD2 v
    have hrange : Module.finrank ℝ (LinearMap.range L) = n - 1 := by
      rw [LinearMap.finrank_range_of_inj (f := L) hD1, Module.finrank_fin_fun]
    have hNfm : Nf m₀ = 2 * ε := by
      change ModelField.nfDeriv d₂.hk m₀ m₀ = 2 * ε
      rw [ModelField.nfDeriv_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hm₀.1,
        hm₀.2, norm_zero]
      ring
    have hNf0 : LinearMap.range Nf ≠ ⊥ := by
      intro h
      have h1 : Nf m₀ ∈ LinearMap.range Nf := LinearMap.mem_range_self Nf m₀
      rw [h, Submodule.mem_bot, hNfm] at h1
      linarith only [h1, hε]
    have hker : Module.finrank ℝ (LinearMap.ker Nf) ≤ n - 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker Nf
      rw [Module.finrank_fin_fun] at h1
      have h2 : Module.finrank ℝ (LinearMap.range Nf) ≠ 0 :=
        fun h => hNf0 (Submodule.finrank_eq_zero.1 h)
      omega
    have heq : LinearMap.range L = LinearMap.ker Nf :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hrange]; exact hker)
    intro x
    obtain ⟨w'', hw''⟩ : ∃ w'' : Fin n → ℝ, w'' = fun i : Fin n =>
        if h : (i : ℕ) < ℓ + 1 then x ⟨i, h⟩ else 0 :=
      ⟨_, rfl⟩
    have hpos : posPart d₂.hk w'' = 0 := by
      ext j
      rw [ModelField.posPart_apply, hw'']
      have : ¬ ((DifferentialGeometry.Topology.Morse.CellAttachment.posIdx d₂.hk j : Fin n) : ℕ) < ℓ + 1 := by
        simp only [DifferentialGeometry.Topology.Morse.CellAttachment.posIdx]
        omega
      simp only [this, dite_false]
      rfl
    have hmem : w'' ∈ LinearMap.ker Nf := by
      rw [LinearMap.mem_ker]
      change ModelField.nfDeriv d₂.hk m₀ w'' = 0
      rw [ModelField.nfDeriv_apply, hpos, hm₀.1, inner_zero_left, inner_zero_right, sub_zero]
    rw [← heq] at hmem
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, fun i => ?_⟩
    have hw' : fderiv ℝ Φ p w = w'' := hw
    rw [hw', hw'']
    simp only [i.isLt, dite_true]
  have hcoordFin : ∀ (y : Fin (n - 1) → ℝ) (i : Fin (n - 1)), coordN y i = y i := by
    intro y i
    simp [coordN, i.isLt]
  obtain ⟨Qlin, hQlin⟩ : ∃ Q : (Fin (n - 1) → ℝ) →L[ℝ] (Fin (n - 1) → ℝ),
      ∀ w i, Q w i = if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ ℓ then w i else 0 :=
    ⟨ContinuousLinearMap.pi fun i => if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ ℓ then
      ContinuousLinearMap.proj i else 0, fun w i => by
        by_cases h : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ ℓ
        · simp only [ContinuousLinearMap.pi_apply, ite_eq_left h]; rfl
        · simp only [ContinuousLinearMap.pi_apply, ite_eq_right h]; rfl⟩
  have hJ : ∀ y w : Fin (n - 1) → ℝ, y ∈ slideA (n - 1) ℓ →
      (∀ j, 1 ≤ j → coordN w j = coordN y j) → slidePt (n - 1) + Qlin w = y := by
    intro y w hy hw
    funext i
    rw [Pi.add_apply, hQlin]
    by_cases h0 : (i : ℕ) = 0
    · have e1 : slidePt (n - 1) i = 1 := by simp [slidePt, h0]
      rw [e1, ite_eq_right (fun h => absurd h.1 (by rw [h0]; norm_num)), ← hcoordFin y i, h0,
        hy.1]
      ring
    · have e1 : slidePt (n - 1) i = 0 := by simp [slidePt, h0]
      rw [e1, zero_add]
      by_cases h1 : (i : ℕ) ≤ ℓ
      · rw [ite_eq_left ⟨Nat.one_le_iff_ne_zero.2 h0, h1⟩, ← hcoordFin w i, ← hcoordFin y i,
          hw i (Nat.one_le_iff_ne_zero.2 h0)]
      · rw [ite_eq_right (fun h => h1 h.2), ← hcoordFin y i,
          hy.2 i (Nat.succ_le_of_lt (not_le.1 h1))]
  have hJp : slidePt (n - 1) + Qlin p = slidePt (n - 1) :=
    hJ _ _ hPA fun j hj => hHscoord t₀ _ j hj
  have hnormE : ∀ (k : ℕ) (_hk : k = ℓ + 1) (u : EuclideanSpace ℝ (Fin (ℓ + 1))),
      ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (Handle.reidx u : Fin k → ℝ)‖ = ‖u‖ := by
    intro k hk u
    subst hk
    congr 1
    ext i
    simp [Handle.reidx, i.isLt]
  obtain ⟨Llin, hLlin⟩ : ∃ L : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] (Fin n → ℝ),
      ∀ u, L u = recombine d₁.hk (Real.sqrt (2 * ε) • d₁.toE (Handle.reidx u)) 0 :=
    ⟨(ModelField.recombineL d₁.hk).comp ((ContinuousLinearMap.inl ℝ _ _).comp
      (Real.sqrt (2 * ε) • ((EuclideanSpace.equiv (Fin d₁.k) ℝ).symm.toContinuousLinearMap.comp
        R₁))), fun u => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ModelField.recombineL_apply, smul_apply, hR₁]
        rfl⟩
  have hSL : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖u‖ = 1 →
      d₁.sphereParam ε (Handle.reidx u) = Llin u := by
    intro u hu
    rw [hLlin, MorseNormalChart.sphereParam, MorseNormalChart.toE, hnormE _ hk₁, hu, div_one]
  have hLinj : ∀ u, Llin u = 0 → u = 0 := by
    intro u hu
    have h1 := congrArg (negPart d₁.hk) hu
    rw [hLlin, ModelField.negPart_recombine] at h1
    have h2 : negPart d₁.hk (0 : Fin n → ℝ) = 0 := (ModelField.negPartL d₁.hk).map_zero
    rw [h2] at h1
    have h3 := congrArg norm h1
    rw [norm_smul, norm_zero, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (mul_pos two_pos hε)),
      MorseNormalChart.toE, hnormE _ hk₁ u] at h3
    exact norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (Real.sqrt_pos.2 (mul_pos two_pos hε)).ne')
  have hΦ₁ψ : ∀ u, u ≠ 0 → D.flow (κ / 2) (σ u) ∈ B → Φ₁ (ψ u) = d₁.sphereParam ε (Handle.reidx u) := by
    intro u hu hB
    obtain ⟨_, hψσ⟩ := hψ u hu hB
    have hφψ : Ch.φ (ψ u) = D.flow κ (σ u) := by rw [← hψσ, flow_flow_neg]
    rw [hΦ₁def]
    dsimp only
    rw [hφψ, hσeq, flow_flow, flow_flow, show g q₁ - ε - (c₂ + κ) + (κ + -(g q₁ - ε - (c₂ + κ) + κ))
      = 0 by ring, flow_zero, hSsrc u hu]
  have hψA : ∀ u, u ≠ 0 → D.flow (κ / 2) (σ u) ∈ B → ψ u ∈ slideA (n - 1) ℓ := by
    intro u hu hB
    obtain ⟨hψU, hψσ⟩ := hψ u hu hB
    have hφψ : Ch.φ (ψ u) = D.flow κ (σ u) := by rw [← hψσ, flow_flow_neg]
    have hL : Ch.φ (ψ u) ∈ D.leftSphere q₁ hq₁ ε c₂ := by rw [hφψ]; exact hσL u hu
    exact (hCh.2.1 _ (by rw [← hCh.1]; exact hψU)).1 hL
  have hΦ₁' : HasFDerivAt Φ₁ (fderiv ℝ Φ₁ (slidePt (n - 1)))
      (slidePt (n - 1) + Qlin (G z₀)) := by
    rw [hGz₀, hJp]
    exact (hΦ₁C.differentiableAt (by simp)).hasFDerivAt
  have hN' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z)
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀) z₀ :=
    (hNC.differentiableAt (by simp)).hasFDerivAt
  have hD5 : (fderiv ℝ Φ₁ (slidePt (n - 1))).comp (Qlin.comp (fderiv ℝ G z₀)) =
      Llin.comp (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀) := by
    have hJ' : HasFDerivAt (fun z => slidePt (n - 1) + Qlin (G z)) (Qlin.comp (fderiv ℝ G z₀)) z₀ :=
      (Qlin.hasFDerivAt.comp z₀ hG').const_add _
    have h1 : HasFDerivAt (fun z => Φ₁ (slidePt (n - 1) + Qlin (G z)))
        ((fderiv ℝ Φ₁ (slidePt (n - 1))).comp (Qlin.comp (fderiv ℝ G z₀))) z₀ :=
      hΦ₁'.comp z₀ hJ'
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => Llin (‖z‖⁻¹ • z))
        (Llin.comp (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀)) z₀ :=
      Llin.hasFDerivAt.comp z₀ hN'
    have hev : (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => Llin (‖z‖⁻¹ • z)) =ᶠ[𝓝 z₀]
        (fun z => Φ₁ (slidePt (n - 1) + Qlin (G z))) := by
      filter_upwards [hgood] with z hz
      have hz0 : 0 < ‖z‖ := by linarith only [hz.1]
      have hu0 := hunitN0 z hz0
      have hA := hψA _ hu0 hz.2.2
      have hJz : slidePt (n - 1) + Qlin (G z) = ψ (‖z‖⁻¹ • z) := by
        refine hJ _ _ hA fun j hj => ?_
        rw [hGdef]
        exact hHscoord _ _ j hj
      rw [hJz, hΦ₁ψ _ hu0 hz.2.2, hSL _ (hunitN z hz0)]
    exact (h1.congr_of_eventuallyEq hev).unique h2
  have hD7 : ∀ v, fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ v = 0 →
      v = (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖) z₀ v) • u₀ := by
    intro v hv
    have hn' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖)
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖) z₀) z₀ :=
      ((contDiffAt_norm ℝ hz₀ne (n := 1)).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => z)
        (‖z₀‖ • fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ +
          (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖) z₀).smulRight u₀) z₀ := by
      have h1 := HasFDerivAt.smul (𝕜' := ℝ) hn' hN'
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hnz₀)] with z hz
      change z = ‖z‖ • (‖z‖⁻¹ • z)
      rw [smul_smul, mul_inv_cancel₀ hz.ne', one_smul]
    have h3 := h2.unique (hasFDerivAt_id z₀)
    have h4 := DFunLike.congr_fun h3 v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, hv, smul_zero,
      zero_add] at h4
    exact h4.symm
  have hD6 : 0 < fderiv ℝ G z₀ u₀ ⟨0, hn1⟩ := by
    obtain ⟨h, hhdef⟩ : ∃ h : ℝ → ℝ, h = fun t => Hs t (slidePt (n - 1)) ⟨0, hn1⟩ := ⟨_, rfl⟩
    have hderiv' : 0 < deriv h t₀ := by
      have e : h = fun t => coordN (Hs t (slidePt (n - 1))) 0 := by
        rw [hhdef]; funext t; rw [hcoordFin _ ⟨0, hn1⟩]
      rw [e]; exact hderiv
    have hhd : DifferentiableAt ℝ h t₀ := by
      have h1 : ContDiff ℝ ∞ (fun t => Hs t (slidePt (n - 1))) :=
        hHsC.comp (contDiff_id.prodMk contDiff_const)
      have h2 : ContDiff ℝ ∞ h := by
        rw [hhdef]
        exact (contDiff_apply ℝ ℝ (⟨0, hn1⟩ : Fin (n - 1))).comp h1
      exact h2.contDiffAt.differentiableAt (by simp)
    have hlin : HasDerivAt (fun s : ℝ => t₀ + 3 * s) 3 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (3 : ℝ)).const_add t₀
    have h1 : HasDerivAt (fun s : ℝ => h (t₀ + 3 * s)) (deriv h t₀ * 3) 0 := by
      have hh : HasDerivAt h (deriv h t₀) (t₀ + 3 * 0) := by
        rw [mul_zero, add_zero]; exact hhd.hasDerivAt
      exact hh.comp (0 : ℝ) hlin
    have hline : HasDerivAt (fun s : ℝ => z₀ + s • u₀) u₀ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u₀).const_add z₀
    have h2 : HasDerivAt (fun s : ℝ => G (z₀ + s • u₀) ⟨0, hn1⟩) (fderiv ℝ G z₀ u₀ ⟨0, hn1⟩) 0 := by
      have := hG'.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - 1) => ℝ)
        ⟨0, hn1⟩).hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
    have hz₀u : z₀ = ‖z₀‖ • u₀ := by
      rw [hu₀def, smul_smul, mul_inv_cancel₀ hnz₀.ne', one_smul]
    have hev : (fun s : ℝ => G (z₀ + s • u₀) ⟨0, hn1⟩) =ᶠ[𝓝 0] (fun s => h (t₀ + 3 * s)) := by
      filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 hnz₀)] with s hs
      have hpos : 0 < ‖z₀‖ + s := by
        have : -‖z₀‖ < s := hs
        linarith only [this]
      have hz : z₀ + s • u₀ = (‖z₀‖ + s) • u₀ := by
        rw [add_smul, ← hz₀u]
      have hnorm : ‖z₀ + s • u₀‖ = ‖z₀‖ + s := by
        rw [hz, norm_smul, hu₀1, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
      have hN : ‖z₀ + s • u₀‖⁻¹ • (z₀ + s • u₀) = u₀ := by
        rw [hnorm, hz, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      rw [hGdef, hhdef]
      dsimp only
      rw [hN, hψu₀, hnorm, show 3 * (‖z₀‖ + s) - 4 = t₀ + 3 * s by rw [← ht₀eq]; ring]
    have h3 := h1.congr_of_eventuallyEq hev
    rw [h2.unique h3]
    exact mul_pos hderiv' three_pos
  have hΦC' : ContDiffAt ℝ ∞ Φ (G z₀) := by rw [hGz₀]; exact hΦC
  have hFC : ContDiffAt ℝ ∞ ((RLc ∘ Φ) ∘ G) z₀ :=
    ContDiffAt.comp z₀ (RLc.contDiff.contDiffAt.comp (G z₀) hΦC') hGC
  refine ⟨(hFC.congr_of_eventuallyEq hΨeq).of_le (by simp), ?_⟩
  have hcomp : HasFDerivAt ((RLc ∘ Φ) ∘ G) ((RLc.comp (fderiv ℝ Φ p)).comp (fderiv ℝ G z₀)) z₀ :=
    (RLc.hasFDerivAt.comp (G z₀) hΦ'').comp z₀ hG'
  rw [hΨeq.fderiv_eq, hcomp.fderiv]
  obtain ⟨ιL, hιL⟩ : ∃ ι : (Fin (ℓ + 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ),
      ∀ x (j : Fin (n - 1)), ι x j = if h : (j : ℕ) < ℓ + 1 then x ⟨j, h⟩ else 0 :=
    ⟨{ toFun := fun x j => if h : (j : ℕ) < ℓ + 1 then x ⟨j, h⟩ else 0
       map_add' := fun x y => by
         funext j
         by_cases h : (j : ℕ) < ℓ + 1
         · simp only [Pi.add_apply, dite_eq_left h]
         · simp only [Pi.add_apply, dite_eq_right h, add_zero]
       map_smul' := fun a x => by
         funext j
         by_cases h : (j : ℕ) < ℓ + 1
         · simp only [Pi.smul_apply, RingHom.id_apply, dite_eq_left h]
         · simp only [Pi.smul_apply, RingHom.id_apply, dite_eq_right h, smul_zero] },
      fun x j => rfl⟩
  obtain ⟨TL, hTL⟩ : ∃ T : (Fin (ℓ + 1) → ℝ) →ₗ[ℝ] (Fin (ℓ + 1) → ℝ),
      ∀ x i, T x i = fderiv ℝ Φ p (ιL x) ⟨i, hin i⟩ :=
    ⟨{ toFun := fun x i => fderiv ℝ Φ p (ιL x) ⟨i, hin i⟩
       map_add' := fun x y => by funext i; simp
       map_smul' := fun a x => by funext i; simp },
      fun x i => rfl⟩
  have hkey : ∀ (w : Fin (n - 1) → ℝ) (i : Fin (ℓ + 1)),
      fderiv ℝ Φ p w ⟨i, hin i⟩ = TL (fun i => w ⟨i, hin' i⟩) i := by
    intro w i
    rw [hTL]
    have hw' : ∀ j, j ≤ ℓ → coordN (w - ιL (fun i => w ⟨i, hin' i⟩)) j = 0 := by
      intro j hj
      rw [hcoordFin _ ⟨j, lt_of_le_of_lt hj hℓlt⟩, Pi.sub_apply, hιL,
        dite_eq_left (Nat.lt_succ_of_le hj),
        sub_self]
    have := hD3 _ hw' ⟨i, hin i⟩ i.isLt
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    exact this
  have hTsurj : Function.Surjective TL := by
    intro x
    obtain ⟨w, hw⟩ := hD4 x
    exact ⟨fun i => w ⟨i, hin' i⟩, funext fun i => by rw [← hkey, hw]⟩
  have hTinj : Function.Injective TL := LinearMap.injective_iff_surjective.2 hTsurj
  have hinj : Function.Injective ((RLc.comp (fderiv ℝ Φ p)).comp (fderiv ℝ G z₀)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv1 : ∀ i : Fin (ℓ + 1), fderiv ℝ Φ p (fderiv ℝ G z₀ v) ⟨i, hin i⟩ = 0 := by
      intro i
      have hik : (i : ℕ) < d₂.k := by rw [hk₂]; exact i.isLt
      have := congrArg (fun x : EuclideanSpace ℝ (Fin (ℓ + 1)) => x i) hv
      simp only [ContinuousLinearMap.comp_apply, hRLc, dite_eq_left hik] at this
      exact this
    have hT0 : TL (fun i => fderiv ℝ G z₀ v ⟨i, hin' i⟩) = 0 := by
      funext i
      rw [← hkey, hv1]
      rfl
    have hπ0 : (fun i : Fin (ℓ + 1) => fderiv ℝ G z₀ v ⟨i, hin' i⟩) = 0 :=
      hTinj (hT0.trans (map_zero TL).symm)
    have hQ0 : Qlin (fderiv ℝ G z₀ v) = 0 := by
      funext j
      rw [hQlin]
      by_cases hj : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ ℓ
      · rw [ite_eq_left hj]
        exact congrFun hπ0 ⟨j, Nat.lt_succ_of_le hj.2⟩
      · rw [ite_eq_right hj]
        rfl
    have hL0 : Llin (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ v) = 0 := by
      have := DFunLike.congr_fun hD5 v
      simp only [ContinuousLinearMap.comp_apply, hQ0, map_zero] at this
      exact this.symm
    have hv2 := hD7 v (hLinj _ hL0)
    have hc : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖) z₀ v = 0 := by
      have h0 := congrFun hπ0 ⟨0, Nat.succ_pos ℓ⟩
      have e : fderiv ℝ G z₀ v ⟨0, hn1⟩ = 0 := h0
      rw [hv2, map_smul, Pi.smul_apply, smul_eq_mul] at e
      exact (mul_eq_zero.1 e).resolve_right hD6.ne'
    rw [hv2, hc, zero_smul]
  have hU : IsUnit (((RLc.comp (fderiv ℝ Φ p)).comp (fderiv ℝ G z₀) :
      EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) :
      EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  exact ((LinearMap.isUnit_iff_isUnit_det _).1 hU).ne_zero

theorem slideAnnulus_spec {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ) {η η' : ℝ} (hη' : η' ≤ η)
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ η' K Hs) :
    ContinuousOn (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulus (ℓ + 1)) ∧
      MapsTo (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulus (ℓ + 1)) (g ⁻¹' Icc a (c₂ - κ)) ∧
      MapsTo (D.slideAnnulus Ch Hs q₁ ℓ ε c) (Handle.annulusBdry (ℓ + 1) ∩ Handle.annulus (ℓ + 1))
        (g ⁻¹' Icc a c) ∧
      ∃ z₀ : EuclideanSpace ℝ (Fin (ℓ + 1)), 1 < ‖z₀‖ ∧ ‖z₀‖ < 2 ∧
        (∀ z ∈ Handle.annulus (ℓ + 1), D.slideAnnulus Ch Hs q₁ ℓ ε c z ∈ D.slabCap (g q₂) → z = z₀) ∧
        D.slideAnnulus Ch Hs q₁ ℓ ε c z₀ ∈ D.captured q₂ hq₂ ∧
        ContDiffAt ℝ 1 (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ ∧
        LinearMap.det (fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ :
          EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) ≠ 0 := by
  obtain ⟨hcont, hmaps, hbd⟩ := slideAnnulus_mapsTo hg D hcrit hq₁ hq₂ hS Ch hη' hCh hfin
  obtain ⟨z₀, hz₁, hz₂, hzA, hzB, huniq, hcap⟩ :=
    slideAnnulus_crossing hg D hcrit hq₁ hq₂ hS Ch hη' hCh hfin
  obtain ⟨hdiff, hdet⟩ :=
    slideAnnulus_det hg D hcrit hq₁ hq₂ hS Ch hη' hCh hfin ⟨hz₁, hz₂⟩ hzA hzB
  exact ⟨hcont, hmaps, hbd, z₀, by linarith, by linarith, huniq, hcap, hdiff, hdet⟩

theorem slideAnnulus_boundary {g : M → ℝ} (hg : MorseStrip I g a b)
    (D : GradientLikeStrip I g a b crit) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ}
    {ℓ : ℕ} {c c₂ κ : ℝ} (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ)
    {η η' : ℝ} (hη' : η' ≤ η) (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ η' K Hs)
    {Z : (x : M) → TangentSpace I x} (hZ : Ch.realizes K (Hs 1) Z)
    (E : GradientLikeStrip I g a b crit) (hE : ∀ x, E.V x = D.V x + Z x)
    (hEchart : ∀ x hx, E.chart x hx = D.chart x hx) :
    (∀ z ∈ SingularPair.unitSphere ℓ, D.slideAnnulus Ch Hs q₁ ℓ ε c z = D.leftSphereHit q₁ (ℓ + 1) ε c z) ∧
      ∀ z ∈ SingularPair.unitSphere ℓ,
        D.slideAnnulus Ch Hs q₁ ℓ ε c ((2 : ℝ) • z) = E.leftSphereHit q₁ (ℓ + 1) ε c z := by
  classical
  have hgs : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hnfC : ∀ {k : ℕ} (hk : k ≤ n) (c₀ : ℝ), ContDiff ℝ ∞ (morseNormalForm hk c₀) := by
    intro k hk c₀
    have hmain : morseNormalForm hk c₀ =
        fun z => c₀ + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) :=
      funext (DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split hk c₀)
    rw [hmain]
    exact contDiff_const.add (contDiff_const.mul
      ((DifferentialGeometry.Topology.Morse.CellAttachment.contDiff_posPart_normSq hk).sub
        (DifferentialGeometry.Topology.Morse.CellAttachment.contDiff_negPart_normSq hk)))
  have hnf0 : ∀ {k : ℕ} (hk : k ≤ n) (c₀ : ℝ), fderiv ℝ (morseNormalForm hk c₀) 0 = 0 := by
    intro k hk c₀
    have hmain : morseNormalForm hk c₀ =
        fun z => c₀ + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) :=
      funext (DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split hk c₀)
    have hd1 : DifferentiableAt ℝ (fun z : Fin n → ℝ => ‖posPart hk z‖ ^ 2) 0 :=
      ((DifferentialGeometry.Topology.Morse.CellAttachment.contDiff_posPart_normSq hk).differentiable
        (by simp)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun z : Fin n → ℝ => ‖negPart hk z‖ ^ 2) 0 :=
      ((DifferentialGeometry.Topology.Morse.CellAttachment.contDiff_negPart_normSq hk).differentiable
        (by simp)).differentiableAt
    have hsub : DifferentiableAt ℝ
        (fun z : Fin n → ℝ => ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) 0 := hd1.sub hd2
    rw [hmain, fderiv_const_add]
    rw [show fderiv ℝ (fun z : Fin n → ℝ =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) 0 =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : Fin n → ℝ =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) 0 from fderiv_const_mul hsub (1 / 2 : ℝ)]
    rw [fderiv_fun_sub hd1 hd2]
    refine ContinuousLinearMap.ext fun w => ?_
    rw [smul_apply, sub_apply,
      DifferentialGeometry.Topology.Morse.CellAttachment.fderiv_posPart_normSq,
      DifferentialGeometry.Topology.Morse.CellAttachment.fderiv_negPart_normSq]
    simp [DifferentialGeometry.Topology.Morse.CellAttachment.posPart,
      DifferentialGeometry.Topology.Morse.CellAttachment.negPart]
  have hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro x
    constructor
    · intro hx
      set d := D.chart x hx with hd
      refine ⟨D.inStrip x hx d.p_mem_image_ball, ?_⟩
      have hR := d.R_pos
      have hU : IsOpen (d.χ '' {y | morseNorm n y < d.R}) := d.isOpen_image_of_lt d.hRR'.le
      have hxU : x ∈ d.χ '' {y | morseNorm n y < d.R} := d.p_mem_image_lt hR
      have heq : g =ᶠ[𝓝 x] (morseNormalForm d.hk (g x) ∘ d.χ.symm) := by
        filter_upwards [hU.mem_nhds hxU] with w hw
        exact d.f_eq_nf_symm (image_mono (fun y (hy : morseNorm n y < d.R) => hy.le) hw)
      have hsx : d.χ.symm x = 0 := by
        have h0 := d.χ.left_inv (d.hsrc 0 (by rw [morseNorm_zero]; exact hR.le))
        rwa [d.hχ0] at h0
      rw [MonotoneShift.isCriticalPointAt_congr_nhds heq]
      rw [MorseExistence.isCriticalPointAt_iff_fderiv_of_localInverse I (τ := d.χ) ?_ ?_
        (d.mdifferentiableAt_symm d.p_mem_image_ball) ?_ ?_]
      · rw [hsx]; exact hnf0 d.hk (g x)
      · filter_upwards [d.isOpen_image_ball.mem_nhds d.p_mem_image_ball] with w hw
        exact d.symm_image_eq hw
      · rw [hsx]
        filter_upwards [Metric.isOpen_ball.mem_nhds d.zero_mem_ball] with y hy
        exact d.χ.left_inv (d.hball hy)
      · exact d.mdifferentiableAt_chart (d.symm_mem_ball d.p_mem_image_ball)
      · exact ((hnfC d.hk (g x)).contDiffAt).contMDiffAt
    · rintro ⟨hx, hc⟩
      by_contra hn
      have := D.neg x ⟨hx.1.le, hx.2.le⟩ hn
      unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hc
      rw [hc] at this
      simp at this
  have hε := hS.hε
  have hac := hS.hac
  have hcq₂ := hS.hcq₂
  have hκ := hS.hκ
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hq₁b := hS.hq₁b
  have hfin' := hfin
  obtain ⟨-, hKdom, -, hbij, -, hsupp, h0, -⟩ := hfin'
  have hZ' := hZ
  obtain ⟨-, -, -, hsupZ, hreal⟩ := hZ'
  have hK : K ⊆ Ch.U := by
    rw [hCh.1]
    intro y hy
    have h := hKdom hy
    exact ⟨h.1, h.2.1, fun j hj => (h.2.2 j hj).trans_le hη'⟩
  have hflowZ := CollarChart.flow_of_realizes hgs Ch hZ hK E hE
  have hlev : ∀ x T, 0 ≤ T → g x ≤ g q₁ - ε → g q₂ + ε ≤ g x - T →
      g (D.flow T x) = g x - T := by
    intro x T hT h1 h2
    refine f_flow_eq_sub_of_levels hgs (D := D) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ?_ T right_mem_uIcc
    intro y hy
    rw [uIcc_of_ge (by linarith)] at hy
    exact hS.hunit y (Or.inr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hsupLev : ∀ x ∈ tsupport Z, c₂ - κ < g x ∧ g x < c₂ + κ := by
    intro x hx
    obtain ⟨⟨y, s⟩, ⟨hyK, hs⟩, rfl⟩ := hsupZ hx
    have hy := Ch.level y (hK hyK)
    have hmem := f_flow_mem_uIcc hgs (D := D) (Ch.φ y) s
    rw [hy] at hmem
    rcases mem_uIcc.1 hmem with h | h <;> constructor <;> linarith [hs.1, hs.2, h.1, h.2]
  set σ : ℝ := g q₁ - ε - (c₂ + κ) with hσ
  have hP : ∀ z ∈ SingularPair.unitSphere ℓ,
      g ((D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx z))) = g q₁ - ε := by
    intro z hz
    apply f_chart_of_mem_leftModelSphere' hq₁ (hS.hεr q₁ hq₁).2
    apply MorseNormalChart.sphereParam_mem_leftModelSphere _ hε.le
    intro hzero
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hzne : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz1; norm_num at hz1
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hall
      exact hzne (by ext i; by_contra hne; exact hall ⟨i, hne⟩)
    have hik : (i : ℕ) < (D.chart q₁ hq₁).k := by rw [hS.hk₁]; exact i.2
    have := congrFun hzero ⟨i, hik⟩
    simp only [Handle.reidx, i.2, ↓reduceDIte, Pi.zero_apply] at this
    exact hi this
  have hLSM : ∀ z, D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z =
      D.flow σ ((D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx z))) := by
    intro z
    simp only [leftSphereMap, hq₁, ↓reduceDIte]
    rfl
  have hT0 : ∀ z, D.slideTrack Ch Hs q₁ ℓ ε 0 z =
      D.flow (2 * κ) (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z) := by
    intro z
    unfold slideTrack
    split_ifs with h
    · have hc := Classical.choose_spec h
      have e1 : D.flow κ (Ch.φ (Classical.choose h)) =
          D.flow (2 * κ) (D.flow (-κ) (Ch.φ (Classical.choose h))) := by
        rw [flow_flow]; congr 1; ring
      rw [h0 0 le_rfl, e1, hc.2]
    · rfl
  have hT1 : ∀ z ∈ SingularPair.unitSphere ℓ,
      E.flow (2 * κ) (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z) =
        D.slideTrack Ch Hs q₁ ℓ ε 1 z ∧ g (D.slideTrack Ch Hs q₁ ℓ ε 1 z) = c₂ - κ := by
    intro z hz
    have hPz := hP z hz
    have hLlev : g (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) z) = c₂ + κ := by
      rw [hLSM z, hlev _ _ (by rw [hσ]; linarith) (by rw [hPz]) (by rw [hPz, hσ]; linarith),
        hPz, hσ]
      ring
    unfold slideTrack
    split_ifs with h
    · have hc := Classical.choose_spec h
      refine ⟨?_, ?_⟩
      · have := hreal E hE _ hc.1
        rw [hc.2] at this
        exact this
      · have hw : Hs 1 (Classical.choose h) ∈ Ch.U := by
          by_cases hyK : Classical.choose h ∈ K
          · apply hK
            by_contra hn
            have h2 := hsupp 1 _ hn
            have h3 := (hbij 1).1 h2
            rw [h3] at hn
            exact hn hyK
          · rw [hsupp 1 _ hyK]
            exact hc.1
        have hφ := Ch.level _ hw
        rw [hlev _ _ hκ.le (by rw [hφ]; linarith) (by rw [hφ]; linarith), hφ]
    · refine ⟨?_, ?_⟩
      · refine hflowZ.2 _ hLlev ?_
        rintro ⟨_, ⟨y, hy, rfl⟩, hy'⟩
        exact h ⟨y, hK hy, hy'⟩
      · rw [hlev _ _ (by linarith) (by rw [hLlev]; linarith) (by rw [hLlev]; linarith), hLlev]
        ring
  have hshift : ∀ (F : GradientLikeStrip I g a b crit) (x : M) (s : ℝ), 0 ≤ s →
      c < g (F.flow s x) → (∃ u, 0 ≤ u ∧ g (F.flow u (F.flow s x)) ≤ c) →
      F.descend c x = F.descend c (F.flow s x) := by
    rintro F x s hs hc ⟨u, hu, hur⟩
    have hA : F.hitTime c x = s + F.hitTime c (F.flow s x) := by
      unfold hitTime
      set B := {v : ℝ | 0 ≤ v ∧ g (F.flow v (F.flow s x)) ≤ c} with hB
      have hBne : B.Nonempty := ⟨u, hu, hur⟩
      have hBbdd : BddBelow B := ⟨0, fun v hv => hv.1⟩
      have hAeq : {v : ℝ | 0 ≤ v ∧ g (F.flow v x) ≤ c} = (fun v => s + v) '' B := by
        ext v
        constructor
        · rintro ⟨hv0, hvc⟩
          have hsv : s ≤ v := by
            by_contra hlt
            have := f_flow_antitone hgs (D := F) x (le_of_lt (not_le.1 hlt))
            simp only at this
            linarith
          refine ⟨v - s, ⟨by linarith, ?_⟩, by ring⟩
          rw [flow_flow, add_sub_cancel]
          exact hvc
        · rintro ⟨w, ⟨hw0, hwc⟩, rfl⟩
          refine ⟨by linarith, ?_⟩
          rw [← flow_flow]
          exact hwc
      rw [hAeq]
      exact (Monotone.map_csInf_of_continuousAt (continuous_const.add continuous_id).continuousAt
        (fun v w hvw => by change s + v ≤ s + w; linarith) hBne hBbdd).symm
    unfold descend
    rw [hA, flow_flow]
  have hbelow : ∀ x, g x ≤ c₂ - κ → ∀ u, 0 ≤ u → E.flow u x = D.flow u x := by
    intro x hx u hu
    refine hflowZ.1 x u fun s hs => ?_
    rw [min_eq_left hu] at hs
    intro hmem
    have h1 := (hsupLev _ hmem).1
    have h2 := f_flow_le hgs (D := D) x hs.1
    linarith
  have hdescEq : ∀ x, g x ≤ c₂ - κ → E.descend c x = D.descend c x := by
    intro x hx
    have hset : {s : ℝ | 0 ≤ s ∧ g (E.flow s x) ≤ c} = {s : ℝ | 0 ≤ s ∧ g (D.flow s x) ≤ c} := by
      ext s
      constructor
      · rintro ⟨h0', h1⟩
        exact ⟨h0', by rwa [← hbelow x hx s h0']⟩
      · rintro ⟨h0', h1⟩
        exact ⟨h0', by rwa [hbelow x hx s h0']⟩
    have hts : E.hitTime c x = D.hitTime c x := by
      unfold hitTime
      rw [hset]
    unfold descend
    rw [hts]
    exact hbelow x hx _ (Real.sInf_nonneg fun s hs => hs.1)
  have hmaps := (slideAnnulus_mapsTo hg D hcrit hq₁ hq₂ hS Ch hη' hCh hfin).2.2
  have hhit0 : ∀ x, 0 ≤ D.hitTime c x := fun x => Real.sInf_nonneg fun s hs => hs.1
  have hz1 : ∀ z ∈ SingularPair.unitSphere ℓ, ‖z‖ = 1 := fun z hz => by simpa using hz
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have h1 := hz1 z hz
    have hA : D.slideAnnulus Ch Hs q₁ ℓ ε c z = D.descend c (D.slideTrack Ch Hs q₁ ℓ ε 0 z) := by
      unfold slideAnnulus
      have hc4 : ‖z‖ ≤ 4 / 3 := by rw [h1]; norm_num
      simp only [hc4, ↓reduceIte]
      rw [h1, inv_one, one_smul]
      unfold descend
      norm_num
    set P := (D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx z)) with hPdef
    have hPz : g P = g q₁ - ε := hP z hz
    have htr : D.slideTrack Ch Hs q₁ ℓ ε 0 z = D.flow (σ + 2 * κ) P := by
      rw [hT0 z, hLSM z, flow_flow]
    have hlevT : g (D.flow (σ + 2 * κ) P) = c₂ - κ := by
      rw [hlev _ _ (by rw [hσ]; linarith) (by rw [hPz]) (by rw [hPz, hσ]; linarith), hPz, hσ]
      ring
    have hmem := hmaps (show z ∈ Handle.annulusBdry (ℓ + 1) ∩ Handle.annulus (ℓ + 1) from
      ⟨Or.inl h1, by rw [h1], by rw [h1]; norm_num⟩)
    rw [hA, htr] at hmem
    rw [hA, htr]
    unfold leftSphereHit
    simp only [hq₁, ↓reduceDIte]
    refine (hshift D P (σ + 2 * κ) (by rw [hσ]; linarith) (by rw [hlevT]; linarith) ?_).symm
    exact ⟨D.hitTime c (D.flow (σ + 2 * κ) P), hhit0 _, hmem.2⟩
  · have h1 := hz1 z hz
    have h2 : ‖(2 : ℝ) • z‖ = 2 := by rw [norm_smul, h1]; norm_num
    have hu : ‖(2 : ℝ) • z‖⁻¹ • (2 : ℝ) • z = z := by rw [h2, smul_smul]; norm_num
    have hA : D.slideAnnulus Ch Hs q₁ ℓ ε c ((2 : ℝ) • z) =
        D.descend c (D.slideTrack Ch Hs q₁ ℓ ε 1 z) := by
      unfold slideAnnulus
      have hc4 : ¬ ‖(2 : ℝ) • z‖ ≤ 4 / 3 := by rw [h2]; norm_num
      have hc5 : ¬ ‖(2 : ℝ) • z‖ ≤ 5 / 3 := by rw [h2]; norm_num
      simp only [hc4, hc5, ↓reduceIte]
      rw [hu, h2]
      unfold descend
      norm_num
    set P := (D.chart q₁ hq₁).χ ((D.chart q₁ hq₁).sphereParam ε (Handle.reidx z)) with hPdef
    have hPz : g P = g q₁ - ε := hP z hz
    obtain ⟨hTE, hTlev⟩ := hT1 z hz
    have hEup : E.flow σ P = D.flow σ P := by
      refine hflowZ.1 P σ fun s hs => ?_
      rw [min_eq_left (by rw [hσ]; linarith), max_eq_right (by rw [hσ]; linarith)] at hs
      intro hmemZ
      have h3 := (hsupLev _ hmemZ).2
      have h4 := sub_le_f_flow hgs (D := D) P hs.1
      rw [hPz] at h4
      have h5 := hs.2
      rw [hσ] at h5
      linarith
    have hEtr : E.flow (σ + 2 * κ) P = D.slideTrack Ch Hs q₁ ℓ ε 1 z := by
      rw [← flow_flow, hEup, ← hLSM z, hTE]
    have hmem := hmaps (show (2 : ℝ) • z ∈ Handle.annulusBdry (ℓ + 1) ∩ Handle.annulus (ℓ + 1) from
      ⟨Or.inr h2, by rw [h2]; norm_num, by rw [h2]⟩)
    rw [hA] at hmem
    rw [hA]
    unfold leftSphereHit
    simp only [hq₁, ↓reduceDIte]
    rw [hEchart q₁ hq₁]
    rw [hshift E P (σ + 2 * κ) (by rw [hσ]; linarith) (by rw [hEtr, hTlev]; linarith) ?_, hEtr,
      hdescEq _ hTlev.le]
    refine ⟨D.hitTime c (D.slideTrack Ch Hs q₁ ℓ ε 1 z), hhit0 _, ?_⟩
    rw [hEtr, hbelow _ hTlev.le _ (hhit0 _)]
    exact hmem.2

theorem slide_tubeSign_twist {g : M → ℝ} (hg : MorseStrip I g a b)
    (D : GradientLikeStrip I g a b crit) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ}
    {ℓ : ℕ} {c c₂ κ : ℝ} (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch Ch₂ : D.CollarChart c₂ κ)
    {η : ℝ} (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) (hCh₂ : D.isSlideChart Ch₂ hq₁ hq₂ ε (η / 2) ℓ)
    (htw : ∀ y, Ch₂.φ y = Ch.φ (slideTwist (n - 1) y)) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ (η / 2) K Hs)
    {z₀ : EuclideanSpace ℝ (Fin (ℓ + 1))} (hz₀ : 1 < ‖z₀‖ ∧ ‖z₀‖ < 2)
    (hcap : D.slideAnnulus Ch Hs q₁ ℓ ε c z₀ ∈ D.slabCap (g q₂)) :
    D.slideAnnulus Ch₂ Hs q₁ ℓ ε c z₀ ∈ D.slabCap (g q₂) ∧
      SignType.sign (LinearMap.det
          (fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch₂ Hs q₁ ℓ ε c) z₀ :
            EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) =
        -SignType.sign (LinearMap.det
          (fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ :
            EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) := by
  classical
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hε : 0 < ε := hS.hε
  have hκ : 0 < κ := hS.hκ
  have hq₂c₂ := hS.hq₂c₂
  have hc₂q₁ := hS.hc₂q₁
  have hac := hS.hac
  have hcq₂ := hS.hcq₂
  have hq₁b := hS.hq₁b
  have hℓ := hS.hℓ
  have hℓn := hS.hℓn
  have hunit : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hS.hunit y (Or.inr hy)
  have hRq : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 := (D.hrm x hx).2
    have h3 := D.rm_pos x hx
    nlinarith
  have hrmq : ∀ x (hx : x ∈ crit), 2 * ε < D.rm x hx ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    nlinarith
  obtain ⟨hK, hKdom, hHs, hbij, hdiff, hsupp, h0, h1, hcoord, hend, t₀, ht₀, hcross, huniq,
    hderiv⟩ := hfin
  have hCap : ∀ X : M, g X = c₂ → X ∈ D.captured q₂ hq₂ → X ∈ D.rightSphere q₂ hq₂ ε c₂ := by
    intro X hX hXcap
    rw [mem_rightSphere_iff]
    set d := D.chart q₂ hq₂ with hd
    set s₀ : ℝ := c₂ - (g q₂ + ε) with hs₀
    set Y := D.flow s₀ X with hYdef
    have hY : g Y = g q₂ + ε := by
      have := f_flow_eq_sub_of_levels hf (D := D) (x := X) (T := s₀)
        ⟨by rw [hX]; linarith, by rw [hX]; linarith⟩ ⟨by rw [hX]; linarith, by rw [hX]; linarith⟩
        (by
          intro y hy p hp
          rw [hX, uIcc_of_ge (by linarith)] at hy
          exact hunit y ⟨by linarith [hy.1], by linarith [hy.2]⟩ p hp) s₀ right_mem_uIcc
      rw [hYdef, this, hX, hs₀]; ring
    have hYcap : Y ∈ D.captured q₂ hq₂ := (flow_mem_captured_iff s₀).2 hXcap
    have hsq : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
    obtain ⟨T, hT⟩ := captured_eventually_small hYcap hsq
    obtain ⟨w, ⟨hw1, hw2⟩, hwZ⟩ := hT (max T 0) (le_max_left _ _)
    have hw : w = recombine d.hk 0 (posPart d.hk w) := by
      conv_lhs => rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk w]
      rw [hw2]
    set v := posPart d.hk w with hv
    have hmn : morseNorm n w = ‖v‖ := by
      have h := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart d.hk w
      rw [hw2, norm_zero] at h
      have h' : morseNorm n w ^ 2 = ‖v‖ ^ 2 := by rw [h]; ring
      exact (pow_left_inj₀ (ModelField.morseNorm_nonneg w) (norm_nonneg _) two_ne_zero).1 h'
    have hv0 : v ≠ 0 := by
      intro hv00
      have hw0 : w = 0 := by
        rw [hw, hv00]
        funext i
        simp [recombine]
      rw [hw0, d.hχ0] at hwZ
      have hYq : Y = q₂ := by
        have := congrArg (D.flow (-(max T 0))) hwZ
        rw [flow_neg_flow, D.flow_crit hq₂] at this
        exact this.symm
      have := D.f_mem_Ioo q₂ hq₂
      rw [hYq] at hY
      linarith
    have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    set e := ‖v‖⁻¹ • v with he_def
    have he : ‖e‖ = 1 := by
      rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
    set t := Real.sqrt (2 * ε) with ht_def
    have htrm : t < D.rm q₂ hq₂ := by
      rw [ht_def, Real.sqrt_lt' (D.rm_pos q₂ hq₂)]
      exact hrmq q₂ hq₂
    have hvt : ‖v‖ ∈ Ioc 0 t := ⟨norm_pos_iff.2 hv0, by rw [← hmn]; exact hw1.le⟩
    obtain ⟨s, -, hs⟩ := (CrossField.flow_ray_stable D hf hq₂ he hsq htrm).2 ‖v‖ hvt
    have hve : ‖v‖ • e = v := by rw [he_def, smul_smul, mul_inv_cancel₀ hnv, one_smul]
    rw [hve, ← hw, hwZ] at hs
    set Q := d.χ (recombine d.hk 0 (t • e)) with hQdef
    have hQ : recombine d.hk 0 (t • e) ∈ d.rightModelSphere ε := by
      refine ⟨ModelField.negPart_recombine d.hk _ _, ?_⟩
      rw [ModelField.posPart_recombine, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos hsq, ht_def, Real.sq_sqrt (by linarith)]
    have hgQ : g Q = g q₂ + ε := d.f_chart_of_mem_rightModelSphere (hRq q₂ hq₂) hQ
    have hYQ : Y = D.flow (s + -(max T 0)) Q := by
      rw [← flow_flow, hs, flow_neg_flow]
    have hlev : ∀ y, g y = g q₂ + ε → dfV I g D.V y = -1 := fun y hy =>
      D.dfV_eq_neg_one_of_level ⟨by linarith, by linarith⟩
        (fun p hp z hz hzc => hunit z ⟨by rw [hzc], by rw [hzc]; linarith⟩ p hp hz) hy
    have hst := flow_level_unique hf hlev (x := Q) (t := s + -(max T 0)) (t' := 0)
      (by rw [← hYQ]; exact hY) (by rw [flow_zero]; exact hgQ)
    rw [hst, flow_zero] at hYQ
    exact ⟨_, hQ, hYQ.symm⟩
  have hslabcap : ∀ x, x ∈ D.slabCap (g q₂) → x ∈ D.captured q₂ hq₂ := by
    intro x hx
    simp only [slabCap, mem_iUnion] at hx
    obtain ⟨r, hr, hgr, hxr⟩ := hx
    obtain rfl : r = q₂ := hS.hslab r hr ⟨by rw [hgr]; linarith, by rw [hgr]; linarith⟩
    exact hxr
  have hLS : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) ∈ D.leftSphere q₁ hq₁ ε c₂ := by
    intro u hu
    have hw : Handle.reidx (k := (D.chart q₁ hq₁).k) u ≠ 0 := by
      intro h
      apply hu
      ext i
      have := congrFun h ⟨i.val, by rw [hS.hk₁]; exact i.isLt⟩
      simpa [Handle.reidx, i.isLt] using this
    refine ⟨_, ⟨_, (D.chart q₁ hq₁).sphereParam_mem_leftModelSphere hε.le hw, rfl⟩, ?_⟩
    simp only [leftSphereMap, hq₁, ↓reduceDIte]
    rw [flow_flow]; congr 1; ring
  have hLSlev : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      g (D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u)) = c₂ := by
    intro u hu
    exact D.leftSphere_subset_level hf q₁ hq₁ (hRq q₁ hq₁) ⟨by linarith, by linarith⟩ (by
      intro y hy p hp
      rw [uIcc_of_ge (by linarith)] at hy
      exact hunit y ⟨by linarith [hy.1], hy.2⟩ p hp) (hLS u hu)
  have hφlev : ∀ y ∈ Ch.U, g (Ch.φ y) = c₂ := Ch.level
  have hφκ : ∀ y ∈ Ch.U, g (D.flow κ (Ch.φ y)) = c₂ - κ := by
    intro y hy
    have := f_flow_eq_sub_of_levels hf (D := D) (x := Ch.φ y) (T := κ)
      ⟨by rw [hφlev y hy]; linarith, by rw [hφlev y hy]; linarith⟩
      ⟨by rw [hφlev y hy]; linarith, by rw [hφlev y hy]; linarith⟩
      (by
        intro z hz p hp
        rw [hφlev y hy, uIcc_of_ge (by linarith)] at hz
        exact hunit z ⟨by linarith [hz.1], by linarith [hz.2]⟩ p hp) κ right_mem_uIcc
    rw [this, hφlev y hy]
  have hU : Ch.U = slideDom (n - 1) η := hCh.1
  have hn1 : 1 < n - 1 := by omega
  have hslidePt0 : coordN (slidePt (n - 1)) 0 = 1 := by
    simp [coordN, slidePt, show 0 < n - 1 by omega]
  have hslidePtj : ∀ j, 1 ≤ j → coordN (slidePt (n - 1)) j = 0 := by
    intro j hj
    by_cases h' : j < n - 1
    · simp [coordN, slidePt, h', show j ≠ 0 by omega]
    · simp [coordN, h']
  have hA_B : ∀ y, y ∈ slideA (n - 1) ℓ → y ∉ slideB (n - 1) ℓ := fun y hA hB => by
    have h1' := hA.1
    have h2' := hB.1
    linarith
  have hHsK : ∀ t, ∀ y ∈ K, Hs t y ∈ K := by
    intro t y hy
    by_contra hn
    have h1' := (hbij t).1 (hsupp t (Hs t y) hn)
    exact hn (by rw [h1']; exact hy)
  have hptK : slidePt (n - 1) ∈ K := by
    by_contra hn
    have h1' := hcross.1
    rw [hsupp t₀ _ hn, hslidePt0] at h1'
    norm_num at h1'
  have hη : 0 < η := by
    have h1' := (hKdom hptK).2.2 1 le_rfl
    rw [hslidePtj 1 le_rfl, abs_zero] at h1'
    linarith
  have hdomsub : slideDom (n - 1) (η / 2) ⊆ slideDom (n - 1) η := fun y hy =>
    ⟨hy.1, hy.2.1, fun j hj => (hy.2.2 j hj).trans (by linarith)⟩
  have hHsU : ∀ t, ∀ y ∈ Ch.U, Hs t y ∈ Ch.U := by
    intro t y hy
    by_cases hyK : y ∈ K
    · rw [hU]; exact hdomsub (hKdom (hHsK t y hyK))
    · rw [hsupp t y hyK]; exact hy
  have hTr : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      D.slideTrack Ch Hs q₁ ℓ ε t u ∈ D.captured q₂ hq₂ →
        t = t₀ ∧ D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) = Ch.φ (slidePt (n - 1)) := by
    intro u hu t ht htr
    have hno : D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) ∉ D.captured q₂ hq₂ := by
      intro hc
      exact Set.disjoint_left.1 hS.hdisj (hLS u hu) (hCap _ (hLSlev u hu) hc)
    unfold slideTrack at htr
    split_ifs at htr with h
    · obtain ⟨hyU, hyeq⟩ := Classical.choose_spec h
      set y := Classical.choose h with hy
      have hφy : Ch.φ y = D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) := by
        rw [← hyeq, flow_flow_neg]
      have hyA : y ∈ slideA (n - 1) ℓ :=
        (hCh.2.1 y (hU ▸ hyU)).1 (by rw [hφy]; exact hLS u hu)
      have hc' : Ch.φ (Hs t y) ∈ D.captured q₂ hq₂ := (flow_mem_captured_iff κ).1 htr
      have hB : Hs t y ∈ slideB (n - 1) ℓ :=
        (hCh.2.2 (Hs t y) (hU ▸ hHsU t y hyU)).1 (hCap _ (hφlev _ (hHsU t y hyU)) hc')
      by_cases hyK : y ∈ K
      · obtain ⟨htt, hyp⟩ := huniq t ht y hyA (hKdom hyK) hB
        exact ⟨htt, by rw [← hφy, hyp]⟩
      · rw [hsupp t y hyK] at hB
        exact absurd hB (hA_B y hyA)
    · rw [two_mul, ← flow_flow] at htr
      exact absurd ((flow_mem_captured_iff κ).1 htr) hno
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀
    linarith [hz₀.1]
  set u₀ : EuclideanSpace ℝ (Fin (ℓ + 1)) := ‖z₀‖⁻¹ • z₀ with hu₀
  have hu₀ne : u₀ ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hz₀ne)) hz₀ne
  have hcapq := hslabcap _ hcap
  have hmid : 4 / 3 < ‖z₀‖ ∧ ‖z₀‖ < 5 / 3 ∧ 3 * ‖z₀‖ - 4 = t₀ ∧
      D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u₀) = Ch.φ (slidePt (n - 1)) := by
    unfold slideAnnulus at hcapq
    split_ifs at hcapq with hA1 hA2
    · have h1' := hTr u₀ hu₀ne 0 ⟨le_rfl, zero_le_one⟩ ((flow_mem_captured_iff _).1 hcapq)
      linarith [h1'.1, ht₀.1]
    · have ht : 3 * ‖z₀‖ - 4 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [not_le.1 hA1], by linarith⟩
      obtain ⟨htt, hφ⟩ := hTr u₀ hu₀ne _ ht hcapq
      exact ⟨not_le.1 hA1, by linarith [ht₀.2], htt, hφ⟩
    · have h1' := hTr u₀ hu₀ne 1 ⟨zero_le_one, le_rfl⟩ ((flow_mem_captured_iff _).1 hcapq)
      linarith [h1'.1, ht₀.2]
  obtain ⟨hz43, hz53, hzt, hφpt⟩ := hmid
  obtain ⟨hopen, inv, hinv, hinvφ⟩ := Ch.exists_boxInverse hf
  have hBxopen : IsOpen ((fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) ''
      (Ch.U ×ˢ Ioo (-κ) κ)) := hopen _ subset_rfl (Ch.isOpen_U.prod isOpen_Ioo)
  have hinv0 : ∀ y ∈ Ch.U, inv (Ch.φ y) = (y, 0) := by
    intro y hy
    have h1' := hinvφ (y, 0) ⟨hy, by constructor <;> linarith⟩
    simpa using h1'
  have hφBx : ∀ y ∈ Ch.U, Ch.φ y ∈ (fun p : (Fin (n - 1) → ℝ) × ℝ => D.flow p.2 (Ch.φ p.1)) ''
      (Ch.U ×ˢ Ioo (-κ) κ) := fun y hy =>
    ⟨(y, 0), ⟨hy, by constructor <;> linarith⟩, by simp⟩
  have hreidx : ∀ u : EuclideanSpace ℝ (Fin (ℓ + 1)), u ≠ 0 →
      Handle.reidx (k := (D.chart q₁ hq₁).k) u ≠ 0 := by
    intro u hu h
    apply hu
    ext i
    have := congrFun h ⟨i.val, by rw [hS.hk₁]; exact i.isLt⟩
    simpa [Handle.reidx, i.isLt] using this
  set Φ : EuclideanSpace ℝ (Fin (ℓ + 1)) → M :=
    fun u => D.flow κ (D.leftSphereMap q₁ (ℓ + 1) ε (c₂ + κ) u) with hΦ
  set ψ : EuclideanSpace ℝ (Fin (ℓ + 1)) → (Fin (n - 1) → ℝ) := fun u => (inv (Φ u)).1 with hψ
  have hptU : slidePt (n - 1) ∈ Ch.U := hU ▸ hdomsub (hKdom hptK)
  have hψu₀ : ψ u₀ = slidePt (n - 1) := by
    simp only [hψ, hΦ]
    rw [hφpt, hinv0 _ hptU]
  have hΦsmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (ℓ + 1))) I ∞ Φ u₀ := by
    set d₁ := D.chart q₁ hq₁ with hd₁
    have hre : ContDiff ℝ ∞ (Handle.reidx (k := d₁.k) (μ := ℓ + 1)) := by
      unfold Handle.reidx
      refine contDiff_pi.2 fun i => ?_
      by_cases h : (i : ℕ) < ℓ + 1
      · simp only [h, ↓reduceDIte]
        exact contDiff_pi.1 (EuclideanSpace.equiv (Fin (ℓ + 1)) ℝ).contDiff _
      · simp only [h, ↓reduceDIte]
        exact contDiff_const
    have hw := hreidx u₀ hu₀ne
    have hsp : ContDiffAt ℝ ∞ (fun u => d₁.sphereParam ε (Handle.reidx (k := d₁.k) u)) u₀ :=
      (d₁.contDiffAt_sphereParam ε hw).comp u₀ hre.contDiffAt
    have hmem : d₁.sphereParam ε (Handle.reidx (k := d₁.k) u₀) ∈ Metric.ball 0 d₁.R' :=
      d₁.mem_ball_of_le (d₁.morseNorm_le_R_of_mem_leftModelSphere (hRq q₁ hq₁)
        (d₁.sphereParam_mem_leftModelSphere hε.le hw))
    have hχ : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ d₁.χ (d₁.sphereParam ε (Handle.reidx (k := d₁.k) u₀)) :=
      d₁.hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds hmem)
    have h2 := hχ.comp u₀ hsp.contMDiffAt
    have h3 := (D.contMDiff_flow κ).contMDiffAt.comp u₀
      ((D.contMDiff_flow (g q₁ - ε - (c₂ + κ))).contMDiffAt.comp u₀ h2)
    convert h3 using 1
    funext u
    simp only [hΦ, leftSphereMap, hq₁, ↓reduceDIte, Function.comp]
    rfl
  have hΦu₀ : Φ u₀ = Ch.φ (slidePt (n - 1)) := hφpt
  have hinvsmooth : ContMDiffAt I 𝓘(ℝ, (Fin (n - 1) → ℝ) × ℝ) ∞ inv (Φ u₀) :=
    hinv.contMDiffAt (hBxopen.mem_nhds (by rw [hΦu₀]; exact hφBx _ hptU))
  have hψsmooth : ContDiffAt ℝ ∞ ψ u₀ := by
    have h1' := contMDiffAt_iff_contDiffAt.1 (hinvsmooth.comp u₀ hΦsmooth)
    exact contDiffAt_fst.comp u₀ h1'
  have hN : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ :=
    ((contDiffAt_norm ℝ hz₀ne).inv (norm_ne_zero_iff.2 hz₀ne)).smul contDiffAt_id
  set P : EuclideanSpace ℝ (Fin (ℓ + 1)) → (Fin (n - 1) → ℝ) :=
    fun z => Hs (3 * ‖z‖ - 4) (ψ (‖z‖⁻¹ • z)) with hPdef
  have hPsmooth : ContDiffAt ℝ ∞ P z₀ := by
    have hψ' : ContDiffAt ℝ ∞ ψ ((fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀) := by
      rw [show (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ = u₀ from hu₀.symm]
      exact hψsmooth
    have h1' : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ψ (‖z‖⁻¹ • z)) z₀ :=
      ContDiffAt.comp (g := ψ) (f := fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ hψ' hN
    have h2' : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => 3 * ‖z‖ - 4) z₀ :=
      (contDiffAt_const.mul (contDiffAt_norm ℝ hz₀ne)).sub contDiffAt_const
    exact hHs.contDiffAt.comp z₀ (h2'.prodMk h1')
  set p := Hs t₀ (slidePt (n - 1)) with hp
  have hPz₀ : P z₀ = p := by
    change Hs (3 * ‖z₀‖ - 4) (ψ u₀) = p
    rw [hzt, hψu₀]
  have hcoordN : ∀ (y : Fin (n - 1) → ℝ) (i : Fin (n - 1)), coordN y i = y i := by
    intro y i
    simp [coordN, i.isLt]
  have hpB : p ∈ slideB (n - 1) ℓ := hcross
  have hpj : ∀ j, 1 ≤ j → coordN p j = 0 := fun j hj => by
    rw [hp, hcoord t₀ _ j hj, hslidePtj j hj]
  have hpdom : p ∈ slideDom (n - 1) η :=
    ⟨by rw [hpB.1]; norm_num, by rw [hpB.1]; norm_num, fun j hj => by rw [hpj j hj, abs_zero]; exact hη⟩
  have hpU : p ∈ Ch.U := hU ▸ hpdom
  set F : (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin (ℓ + 1)) :=
    fun y => D.tubeCoordE q₂ hq₂ ε (ℓ + 1) (D.flow κ (Ch.φ y)) with hFdef
  set Tm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)) :=
    (EuclideanSpace.equiv (Fin (ℓ + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun i : Fin (ℓ + 1) =>
        if h : (i : ℕ) < (D.chart q₂ hq₂).k then (EuclideanSpace.proj (⟨i, h⟩ : Fin (D.chart q₂ hq₂).k)) ∘L
          ModelField.negPartL (D.chart q₂ hq₂).hk else 0 with hTm
  set G : (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin (ℓ + 1)) :=
    fun y => Tm ((D.chart q₂ hq₂).χ.symm (D.flow (c₂ - (g q₂ + ε)) (Ch.φ y))) with hGdef
  have hFG : F =ᶠ[𝓝 p] G := by
    filter_upwards [Ch.isOpen_U.mem_nhds hpU] with y hy
    simp only [hFdef, hGdef, tubeCoordE, tubeCoord, rightCoord]
    have hle' : g q₂ + ε ≤ g (D.flow κ (Ch.φ y)) := by rw [hφκ y hy]; linarith
    simp only [hle', ↓reduceIte]
    rw [hφκ y hy, flow_flow, show κ + (c₂ - κ - (g q₂ + ε)) = c₂ - (g q₂ + ε) by ring]
    ext i
    by_cases h : (i : ℕ) < (D.chart q₂ hq₂).k
    · simp [hTm, h]
    · simp [hTm, h]
  have hGsmooth : ContDiffAt ℝ ∞ G p := by
    have hmemR : D.flow (c₂ - (g q₂ + ε)) (Ch.φ p) ∈ (D.chart q₂ hq₂).χ '' (D.chart q₂ hq₂).rightModelSphere ε :=
      (mem_rightSphere_iff _ _ _ _ _).1 ((hCh.2.2 p hpdom).2 hpB)
    have hmemB : D.flow (c₂ - (g q₂ + ε)) (Ch.φ p) ∈ (D.chart q₂ hq₂).χ '' Metric.ball 0 (D.chart q₂ hq₂).R' :=
      image_mono (fun w hw => (D.chart q₂ hq₂).mem_ball_of_le
        ((D.chart q₂ hq₂).morseNorm_le_R_of_mem_rightModelSphere (hRq q₂ hq₂) hw)) hmemR
    have h1' : ContMDiffAt 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ Ch.φ p :=
      Ch.smooth.contMDiffAt (Ch.isOpen_U.mem_nhds hpU)
    have h2' := (D.contMDiff_flow (c₂ - (g q₂ + ε))).contMDiffAt.comp p h1'
    have h3' := ((D.chart q₂ hq₂).hχsymm.contMDiffAt ((D.chart q₂ hq₂).isOpen_image_ball.mem_nhds hmemB)).comp p h2'
    have h4' := contMDiffAt_iff_contDiffAt.1 h3'
    exact Tm.contDiff.contDiffAt.comp p h4'
  have hFd : HasFDerivAt F (fderiv ℝ G p) p :=
    ((hGsmooth.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq hFG
  set Rl : (Fin (n - 1) → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin (n - 1) =>
      if ((i : ℕ) = 1 ∨ (i : ℕ) = n - 1 - 1) then -ContinuousLinearMap.proj i
      else ContinuousLinearMap.proj i with hRl
  have hRl_apply : ∀ (y : Fin (n - 1) → ℝ) (i : Fin (n - 1)),
      Rl y i = if ((i : ℕ) = 1 ∨ (i : ℕ) = n - 1 - 1) then -y i else y i := by
    intro y i
    by_cases h : ((i : ℕ) = 1 ∨ (i : ℕ) = n - 1 - 1)
    · simp [hRl, h]
    · simp [hRl, h]
  have hcoordN' : ∀ (y : Fin (n - 1) → ℝ) (i : Fin (n - 1)) (j : ℕ), (i : ℕ) = j →
      coordN y j = y i := by
    intro y i j h
    subst h
    exact hcoordN y i
  have hΘ1 : ∀ y : Fin (n - 1) → ℝ, coordN y 0 = 1 → slideTwist (n - 1) y = y := by
    intro y hy
    funext i
    have hst : Real.smoothTransition (3 * coordN y 0 - 4) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [hy]; norm_num)
    simp only [slideTwist, hst, mul_zero, Real.cos_zero, Real.sin_zero, one_mul, zero_mul,
      sub_zero, zero_add]
    split_ifs with h1' h2'
    · exact hcoordN' y i 1 h1'
    · exact hcoordN' y i _ h2'
    · rfl
  have hΘ2 : ∀ y : Fin (n - 1) → ℝ, 5 / 3 ≤ coordN y 0 → slideTwist (n - 1) y = Rl y := by
    intro y hy
    funext i
    have hst : Real.smoothTransition (3 * coordN y 0 - 4) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    simp only [slideTwist, hst, mul_one, Real.cos_pi, Real.sin_pi, zero_mul, sub_zero,
      neg_one_mul, zero_add]
    rw [hRl_apply]
    split_ifs with h1' h2' h3' h4' <;>
      first
        | rfl
        | (exfalso; omega)
        | (rw [hcoordN' y i 1 ‹_›])
        | (rw [hcoordN' y i (n - 1 - 1) ‹_›])
  have hRlp : Rl p = p := by
    funext i
    rw [hRl_apply]
    by_cases h : ((i : ℕ) = 1 ∨ (i : ℕ) = n - 1 - 1)
    · have hpi : p i = 0 := by
        rw [← hcoordN p i, hpj _ (by omega)]
      simp [h, hpi]
    · simp [h]
  have hdomnhds : slideDom (n - 1) (η / 2) ∈ 𝓝 (slidePt (n - 1)) := by
    have hδ : 0 < min (1 / 2 : ℝ) (η / 2) := lt_min (by norm_num) (by linarith)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds _ hδ) ?_
    intro y hy
    have hyi : ∀ i : Fin (n - 1), |y i - slidePt (n - 1) i| < min (1 / 2 : ℝ) (η / 2) :=
      fun i => lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist y _ i) hy
    have h0' : coordN y 0 = y ⟨0, by omega⟩ := hcoordN' y ⟨0, by omega⟩ 0 rfl
    have hs0 : slidePt (n - 1) ⟨0, by omega⟩ = 1 := by simp [slidePt]
    have hy0 := hyi ⟨0, by omega⟩
    rw [hs0] at hy0
    have hm1 := min_le_left (1 / 2 : ℝ) (η / 2)
    refine ⟨?_, ?_, ?_⟩
    · rw [h0']; linarith [(abs_lt.1 hy0).1]
    · rw [h0']; linarith [(abs_lt.1 hy0).2]
    · intro j hj
      by_cases hjn : j < n - 1
      · rw [hcoordN' y ⟨j, hjn⟩ j rfl]
        have hyj := hyi ⟨j, hjn⟩
        have hsj : slidePt (n - 1) ⟨j, hjn⟩ = 0 := by simp [slidePt, show j ≠ 0 by omega]
        rw [hsj, sub_zero] at hyj
        exact lt_of_lt_of_le hyj (min_le_right _ _)
      · simp only [coordN, hjn, ↓reduceDIte, abs_zero]
        linarith
  obtain ⟨G', hG'open, hG'eq⟩ := Ch.open_image Ch.U subset_rfl Ch.isOpen_U
  have hΦG' : Φ u₀ ∈ G' := by
    have h1' : Φ u₀ ∈ Ch.φ '' Ch.U := ⟨_, hptU, hΦu₀.symm⟩
    rw [hG'eq] at h1'
    exact h1'.1
  have hNc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z) z₀ :=
    hN.continuousAt
  have hΦc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => Φ (‖z‖⁻¹ • z)) z₀ :=
    ContinuousAt.comp_of_eq (g := Φ) (f := fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z)
      hΦsmooth.continuousAt hNc hu₀.symm
  have hψc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ψ (‖z‖⁻¹ • z)) z₀ :=
    ContinuousAt.comp_of_eq (g := ψ) (f := fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => ‖z‖⁻¹ • z)
      hψsmooth.continuousAt hNc hu₀.symm
  have hPc : ContinuousAt P z₀ := hPsmooth.continuousAt
  have hp0 : p ⟨0, by omega⟩ = 2 := by
    rw [← hcoordN' p ⟨0, by omega⟩ 0 rfl]
    exact hpB.1
  have hev : ∀ᶠ z in 𝓝 z₀, (4 / 3 < ‖z‖ ∧ ‖z‖ < 5 / 3) ∧ Φ (‖z‖⁻¹ • z) ∈ G' ∧
      ψ (‖z‖⁻¹ • z) ∈ slideDom (n - 1) (η / 2) ∧ 5 / 3 < P z ⟨0, by omega⟩ := by
    have e1 : ∀ᶠ z in 𝓝 z₀, ‖z‖ ∈ Ioo (4 / 3 : ℝ) (5 / 3) :=
      continuous_norm.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hz43 hz53)
    have e2 : ∀ᶠ z in 𝓝 z₀, Φ (‖z‖⁻¹ • z) ∈ G' :=
      hΦc.preimage_mem_nhds (hG'open.mem_nhds hΦG')
    have e3 : ∀ᶠ z in 𝓝 z₀, ψ (‖z‖⁻¹ • z) ∈ slideDom (n - 1) (η / 2) := by
      refine hψc.preimage_mem_nhds ?_
      change slideDom (n - 1) (η / 2) ∈ 𝓝 (ψ u₀)
      rw [hψu₀]
      exact hdomnhds
    have e4 : ∀ᶠ z in 𝓝 z₀, 5 / 3 < P z ⟨0, by omega⟩ := by
      refine ((continuous_apply _).continuousAt.comp hPc).preimage_mem_nhds (Ioi_mem_nhds ?_)
      change (5 / 3 : ℝ) < P z₀ ⟨0, by omega⟩
      rw [hPz₀, hp0]
      norm_num
    filter_upwards [e1, e2, e3, e4] with z h1' h2' h3' h4'
    exact ⟨h1', h2', h3', h4'⟩
  have hloc : ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), (4 / 3 < ‖z‖ ∧ ‖z‖ < 5 / 3) →
      Φ (‖z‖⁻¹ • z) ∈ G' → ψ (‖z‖⁻¹ • z) ∈ slideDom (n - 1) (η / 2) →
      D.slideAnnulus Ch Hs q₁ ℓ ε c z = D.flow κ (Ch.φ (P z)) ∧
      D.slideAnnulus Ch₂ Hs q₁ ℓ ε c z = D.flow κ (Ch.φ (slideTwist (n - 1) (P z))) ∧
      ψ (‖z‖⁻¹ • z) ∈ slideA (n - 1) ℓ := by
    intro z hz hzG hzdom
    have hzne : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith [hz.1]
    have hune : ‖z‖⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hzne)) hzne
    have hyU : ψ (‖z‖⁻¹ • z) ∈ Ch.U := hU ▸ hdomsub hzdom
    have hΦim : Φ (‖z‖⁻¹ • z) ∈ Ch.φ '' Ch.U := by
      rw [hG'eq]
      exact ⟨hzG, hLSlev _ hune⟩
    obtain ⟨y', hy'U, hy'φ⟩ := hΦim
    have hyy' : ψ (‖z‖⁻¹ • z) = y' := by
      change (inv (Φ (‖z‖⁻¹ • z))).1 = y'
      rw [← hy'φ, hinv0 y' hy'U]
    have hφy : Ch.φ (ψ (‖z‖⁻¹ • z)) = Φ (‖z‖⁻¹ • z) := by rw [hyy', hy'φ]
    have hyA : ψ (‖z‖⁻¹ • z) ∈ slideA (n - 1) ℓ :=
      (hCh.2.1 _ (hU ▸ hyU)).1 (by rw [hφy]; exact hLS _ hune)
    have hΘy : slideTwist (n - 1) (ψ (‖z‖⁻¹ • z)) = ψ (‖z‖⁻¹ • z) := hΘ1 _ hyA.1
    have hTr1 : ∀ t, D.slideTrack Ch Hs q₁ ℓ ε t (‖z‖⁻¹ • z) =
        D.flow κ (Ch.φ (Hs t (ψ (‖z‖⁻¹ • z)))) := by
      intro t
      unfold slideTrack
      split_ifs with h
      · obtain ⟨hcU, hceq⟩ := Classical.choose_spec h
        have hcφ : Ch.φ (Classical.choose h) = Φ (‖z‖⁻¹ • z) := by
          have h1' := congrArg (D.flow κ) hceq
          rw [flow_flow_neg] at h1'
          exact h1'
        have hc : Classical.choose h = ψ (‖z‖⁻¹ • z) := by
          change _ = (inv (Φ (‖z‖⁻¹ • z))).1
          rw [← hcφ, hinv0 _ hcU]
        rw [hc]
      · exact absurd ⟨_, hyU, by rw [hφy]; exact D.flow_neg_flow _ _⟩ h
    have hTr2 : ∀ t, D.slideTrack Ch₂ Hs q₁ ℓ ε t (‖z‖⁻¹ • z) =
        D.flow κ (Ch.φ (slideTwist (n - 1) (Hs t (ψ (‖z‖⁻¹ • z))))) := by
      intro t
      have hyU₂ : ψ (‖z‖⁻¹ • z) ∈ Ch₂.U := by rw [hCh₂.1]; exact hzdom
      have hφ₂y : Ch₂.φ (ψ (‖z‖⁻¹ • z)) = Φ (‖z‖⁻¹ • z) := by rw [htw, hΘy, hφy]
      unfold slideTrack
      split_ifs with h
      · obtain ⟨hcU, hceq⟩ := Classical.choose_spec h
        have hc₂ : Ch₂.φ (Classical.choose h) = Φ (‖z‖⁻¹ • z) := by
          have h1' := congrArg (D.flow κ) hceq
          rw [flow_flow_neg] at h1'
          exact h1'
        have hcdom : Classical.choose h ∈ slideDom (n - 1) (η / 2) := hCh₂.1 ▸ hcU
        have hcA : Classical.choose h ∈ slideA (n - 1) ℓ :=
          (hCh₂.2.1 _ hcdom).1 (by rw [hc₂]; exact hLS _ hune)
        have hcφ : Ch.φ (Classical.choose h) = Φ (‖z‖⁻¹ • z) := by
          rw [← hc₂, htw, hΘ1 _ hcA.1]
        have hc : Classical.choose h = ψ (‖z‖⁻¹ • z) := by
          change _ = (inv (Φ (‖z‖⁻¹ • z))).1
          rw [← hcφ, hinv0 _ (hU ▸ hdomsub hcdom)]
        rw [hc, htw]
      · exact absurd ⟨_, hyU₂, by rw [hφ₂y]; exact D.flow_neg_flow _ _⟩ h
    have hz1 : ¬ ‖z‖ ≤ 4 / 3 := not_le.2 hz.1
    have hz2 : ‖z‖ ≤ 5 / 3 := hz.2.le
    refine ⟨?_, ?_, hyA⟩
    · simp only [slideAnnulus, hz1, hz2, ↓reduceIte]
      rw [hTr1]
    · simp only [slideAnnulus, hz1, hz2, ↓reduceIte]
      rw [hTr2]
  obtain ⟨hz₀a, hz₀b, hz₀c, -⟩ := hev.self_of_nhds
  obtain ⟨hA₁, hA₂, -⟩ := hloc z₀ hz₀a hz₀b hz₀c
  have hAeq : D.slideAnnulus Ch₂ Hs q₁ ℓ ε c z₀ = D.slideAnnulus Ch Hs q₁ ℓ ε c z₀ := by
    rw [hA₂, hA₁, hPz₀, hΘ2 p (by rw [hpB.1]; norm_num), hRlp]
  refine ⟨by rw [hAeq]; exact hcap, ?_⟩
  have hf1 : (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) =ᶠ[𝓝 z₀]
      F ∘ P := by
    filter_upwards [hev] with z hz
    obtain ⟨h1', -, -⟩ := hloc z hz.1 hz.2.1 hz.2.2.1
    change D.tubeCoordE q₂ hq₂ ε (ℓ + 1) (D.slideAnnulus Ch Hs q₁ ℓ ε c z) = F (P z)
    rw [h1']
  have hf2 : (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch₂ Hs q₁ ℓ ε c) =ᶠ[𝓝 z₀]
      F ∘ (⇑Rl ∘ P) := by
    filter_upwards [hev] with z hz
    obtain ⟨-, h2', -⟩ := hloc z hz.1 hz.2.1 hz.2.2.1
    have h0z : 5 / 3 ≤ coordN (P z) 0 := by
      rw [hcoordN' (P z) ⟨0, by omega⟩ 0 rfl]
      exact hz.2.2.2.le
    change D.tubeCoordE q₂ hq₂ ε (ℓ + 1) (D.slideAnnulus Ch₂ Hs q₁ ℓ ε c z) = F (Rl (P z))
    rw [h2', hΘ2 _ h0z]
  have hPd : HasFDerivAt P (fderiv ℝ P z₀) z₀ :=
    (hPsmooth.differentiableAt (by simp)).hasFDerivAt
  set dP := fderiv ℝ P z₀ with hdP
  set L := fderiv ℝ G p with hL
  have hFd1 : HasFDerivAt F L (P z₀) := by rw [hPz₀]; exact hFd
  have hFd2 : HasFDerivAt F L (Rl (P z₀)) := by rw [hPz₀, hRlp]; exact hFd
  have hd1 : fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ =
      L.comp dP :=
    ((hFd1.comp z₀ hPd).congr_of_eventuallyEq hf1).fderiv
  have hd2 : fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch₂ Hs q₁ ℓ ε c) z₀ =
      L.comp (Rl.comp dP) :=
    ((hFd2.comp z₀ (Rl.hasFDerivAt.comp z₀ hPd)).congr_of_eventuallyEq hf2).fderiv
  have hPA : ∀ᶠ z in 𝓝 z₀, ∀ j : Fin (n - 1), ℓ + 1 ≤ (j : ℕ) → P z j = 0 := by
    filter_upwards [hev] with z hz
    obtain ⟨-, -, hyA⟩ := hloc z hz.1 hz.2.1 hz.2.2.1
    intro j hj
    rw [← hcoordN (P z) j]
    change coordN (Hs (3 * ‖z‖ - 4) (ψ (‖z‖⁻¹ • z))) j = 0
    rw [hcoord _ _ _ (by omega)]
    exact hyA.2 j hj
  have hdPj : ∀ v, ∀ j : Fin (n - 1), ℓ + 1 ≤ (j : ℕ) → dP v j = 0 := by
    intro v j hj
    have e1 : HasFDerivAt (⇑(ContinuousLinearMap.proj j : (Fin (n - 1) → ℝ) →L[ℝ] ℝ) ∘ P)
        ((ContinuousLinearMap.proj j).comp dP) z₀ :=
      (ContinuousLinearMap.proj j).hasFDerivAt.comp z₀ hPd
    have e2 : HasFDerivAt (⇑(ContinuousLinearMap.proj j : (Fin (n - 1) → ℝ) →L[ℝ] ℝ) ∘ P)
        (0 : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] ℝ) z₀ :=
      (hasFDerivAt_const (0 : ℝ) z₀).congr_of_eventuallyEq
        (by filter_upwards [hPA] with z hz; exact hz j hj)
    have h1' := congrArg (fun T : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] ℝ => T v) (e1.unique e2)
    simpa using h1'
  set ι : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] (Fin (n - 1) → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin (n - 1) =>
      if h : (i : ℕ) < ℓ + 1 then EuclideanSpace.proj (⟨i, h⟩ : Fin (ℓ + 1)) else 0 with hι
  set Jm : (Fin (n - 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)) :=
    (EuclideanSpace.equiv (Fin (ℓ + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun i : Fin (ℓ + 1) =>
        ContinuousLinearMap.proj (⟨i, by omega⟩ : Fin (n - 1)) with hJm
  set S : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)) :=
    (EuclideanSpace.equiv (Fin (ℓ + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun i : Fin (ℓ + 1) =>
        if (i : ℕ) = 1 then -EuclideanSpace.proj i else EuclideanSpace.proj i with hS'
  have hιJ : ι.comp (Jm.comp dP) = dP := by
    refine ContinuousLinearMap.ext fun v => ?_
    funext j
    by_cases h : (j : ℕ) ≤ ℓ
    · simp [hι, hJm, h]
    · simpa [hι, h] using (hdPj v j (by omega)).symm
  have hRι : Rl.comp ι = ι.comp S := by
    refine ContinuousLinearMap.ext fun w => ?_
    funext i
    rw [ContinuousLinearMap.comp_apply, hRl_apply]
    by_cases h : (i : ℕ) ≤ ℓ
    · by_cases h1' : (i : ℕ) = 1
      · have h1ℓ : 1 ≤ ℓ := by omega
        simp [hι, hS', h1', h1ℓ]
      · have h2' : (i : ℕ) ≠ n - 1 - 1 := by omega
        simp [hι, hS', h, h1', h2']
    · have h2' : (i : ℕ) ≠ 1 := by omega
      simp [hι, hS', h, h2']
  have hdetS : LinearMap.det
      (S : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) = -1 := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (ℓ + 1)) ℝ).toBasis]
    have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (ℓ + 1)) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin (ℓ + 1)) ℝ).toBasis
        (S : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) =
        Matrix.diagonal (fun i : Fin (ℓ + 1) => if (i : ℕ) = 1 then (-1 : ℝ) else 1) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
      by_cases hij : i = j
      · subst hij
        by_cases h1' : (i : ℕ) = 1 <;> simp [hS', h1']
      · by_cases h1' : (i : ℕ) = 1 <;> simp [hS', h1', hij]
    rw [hM, Matrix.det_diagonal, Finset.prod_eq_single (⟨1, by omega⟩ : Fin (ℓ + 1))]
    · simp
    · intro b _ hb
      have hb' : ¬ ((b : ℕ) = 1) := fun h => hb (Fin.ext h)
      simp only [hb', ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hdet_comp : ∀ X Y : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
      LinearMap.det ((X.comp Y : EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) :
        EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) =
      LinearMap.det (X : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) *
        LinearMap.det (Y : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) := by
    intro X Y
    change LinearMap.det ((X : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))).comp
      (Y : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) = _
    exact LinearMap.det_comp _ _
  have hd1' : L.comp dP = (L.comp ι).comp (Jm.comp dP) := by
    rw [ContinuousLinearMap.comp_assoc, hιJ]
  have hd2' : L.comp (Rl.comp dP) = (L.comp ι).comp (S.comp (Jm.comp dP)) := by
    conv_lhs => rw [← hιJ]
    rw [← ContinuousLinearMap.comp_assoc Rl ι, hRι]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hd2, hd1, hd2', hd1', hdet_comp, hdet_comp, hdet_comp, hdetS,
    show ∀ x y : ℝ, x * (-1 * y) = -(x * y) from fun x y => by ring, Left.sign_neg]

theorem slide_class_change_pair {g : M → ℝ} (hg : MorseStrip I g a b)
    (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch Ch₂ : D.CollarChart c₂ κ) {η : ℝ}
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) (hCh₂ : D.isSlideChart Ch₂ hq₁ hq₂ ε (η / 2) ℓ)
    (htw : ∀ y, Ch₂.φ y = Ch.φ (slideTwist (n - 1) y)) {K : Set (Fin (n - 1) → ℝ)}
    {Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hfin : isSlideFinger (n - 1) ℓ (η / 2) K Hs)
    {Z Z₂ : (x : M) → TangentSpace I x} (hZ : Ch.realizes K (Hs 1) Z)
    (hZ₂ : Ch₂.realizes K (Hs 1) Z₂) (E E₂ : GradientLikeStrip I g a b crit)
    (hE : ∀ x, E.V x = D.V x + Z x) (hE₂ : ∀ x, E₂.V x = D.V x + Z₂ x)
    (hEchart : ∀ x hx, E.chart x hx = D.chart x hx)
    (hE₂chart : ∀ x hx, E₂.chart x hx = D.chart x hx)
    (gD' : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk (ℓ + 1))))
      (ULift.down ⁻¹' diskSphere (ℓ + 1)) (ℓ + 1)) (hgD' : Handle.isGen gD') :
    ∃ m : ℤ, (m = 1 ∨ m = -1) ∧
      Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (E.leftSphereHit q₁ (ℓ + 1) ε c)
          (Handle.boundaryGen gD') =
        Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereHit q₁ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') +
          m • Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereMap q₂ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') ∧
      Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (E₂.leftSphereHit q₁ (ℓ + 1) ε c)
          (Handle.boundaryGen gD') =
        Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereHit q₁ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') -
          m • Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereMap q₂ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') := by
  classical
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hε : 0 < ε := hS.hε
  have hεr := hS.hεr
  have hac : a ≤ c := hS.hac.le
  have hcτ : c < g q₂ - ε := hS.hcq₂
  have hτt' : g q₂ + ε < c₂ - κ := hS.hq₂c₂
  have ht'b : c₂ - κ ≤ b := by linarith [hS.hc₂q₁, hS.hq₁b, hS.hκ, hS.hε]
  have hslab' : ∀ x ∈ crit, g x ∈ Icc c (c₂ - κ) → g x = g q₂ := by
    intro x hx hxI
    have := hS.hslab x hx ⟨hxI.1, by linarith [hxI.2, hS.hc₂q₁, hS.hκ]⟩
    rw [this]
  have hUup : ∀ y, g y ∈ Icc (g q₂ + ε) (c₂ - κ) → ∀ w hw, y ∉ D.smallBall w hw := fun y hy =>
    hS.hunit y (Or.inr ⟨hy.1, by linarith [hy.2, hS.hc₂q₁, hS.hκ]⟩)
  have hUlo : ∀ y, g y ∈ Icc c (g q₂ - ε) → ∀ w hw, y ∉ D.smallBall w hw := fun y hy =>
    hS.hunit y (Or.inl hy)
  have hℓ1 : 1 ≤ ℓ := by linarith [hS.hℓ]
  have hη : 0 < η := by
    obtain ⟨-, hKd, -, -, -, hout, -, -, -, -, t₀, -, hB, -⟩ := hfin
    have hPK : slidePt (n - 1) ∈ K := by
      by_contra hPK
      rw [hout t₀ _ hPK] at hB
      have h0 := hB.1
      simp only [slidePt, coordN] at h0
      split_ifs at h0 <;> norm_num at h0
    have h1 := (hKd hPK).2.2 1 le_rfl
    simp only [slidePt, coordN] at h1
    split_ifs at h1 <;> simp at h1 <;> linarith
  obtain ⟨Γ, s, hs, hΓ⟩ := Handle.exists_annulus_class ℓ hℓ1 (Handle.boundaryGen gD')
    (Handle.isGen_boundaryGen hℓ1 hgD') gD' hgD'
  obtain ⟨hsub, hiso⟩ := D.isIso_inclPair_slab hf hcrit hε hεr hac hcτ hτt' ht'b hslab'
  have hinj := (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (Handle.inclPair (subset_refl (g ⁻¹' Icc a (c₂ - κ))) hsub (ℓ + 1))).1
  have hsphc : MapsTo (D.leftDiscMap q₂ (ℓ + 1) ε c) (Metric.sphere 0 1) (g ⁻¹' Icc a c) := by
    intro y hy
    have hy1 : ‖y‖ = 1 := by simpa using hy
    have hk := hS.hk₂
    have hw : (Handle.reidx y : Fin (D.chart q₂ hq₂).k → ℝ) ≠ 0 := by
      intro h0
      have hy0 : y = 0 := by
        ext j
        have := congrFun h0 ⟨j.1, by rw [hk]; exact j.2⟩
        simp only [Handle.reidx, dite_eq_left j.2, Pi.zero_apply] at this
        simpa using this
      rw [hy0, norm_zero] at hy1
      exact zero_ne_one hy1
    have hε2 : 2 * ε ≤ (D.chart q₂ hq₂).R ^ 2 := by
      have h1 := (hεr q₂ hq₂).2
      have h2 := (D.hrm q₂ hq₂).2
      have h3 := D.rm_pos q₂ hq₂
      nlinarith
    have hmem := (D.chart q₂ hq₂).sphereParam_mem_leftModelSphere hε.le hw
    have hf0 := (D.chart q₂ hq₂).f_chart_of_mem_leftModelSphere hε2 hmem
    have hval : D.leftDiscMap q₂ (ℓ + 1) ε c y = D.flow (g q₂ - ε - c)
        ((D.chart q₂ hq₂).χ ((D.chart q₂ hq₂).sphereParam ε (Handle.reidx y))) := by
      unfold leftDiscMap
      rw [dite_eq_left hq₂, ite_eq_right (by rw [hy1]; norm_num), hy1]
      congr 1
      ring
    have hlev := f_flow_eq_sub_of_levels hf (D := D)
      (x := (D.chart q₂ hq₂).χ ((D.chart q₂ hq₂).sphereParam ε (Handle.reidx y)))
      (T := g q₂ - ε - c)
      (by rw [hf0]; constructor <;> linarith)
      (by rw [hf0]; constructor <;> linarith)
      (fun z hz p hp => by
        rw [hf0] at hz
        have he : g q₂ - ε - (g q₂ - ε - c) = c := by ring
        rw [he, uIcc_of_ge (by linarith)] at hz
        exact hUlo z hz p hp)
      (g q₂ - ε - c) (by rw [uIcc_of_le (by linarith)]; exact right_mem_Icc.2 (by linarith))
    rw [mem_preimage, hval, hlev, hf0]
    constructor <;> linarith
  have hdiscIncl : Handle.inclPair (subset_refl _) hsub (ℓ + 1)
      (Handle.discClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a c) (D.leftDiscMap q₂ (ℓ + 1) ε c)
        gD') =
      Handle.discClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a (c₂ - κ) \ D.slabCap (g q₂))
        (D.leftDiscMap q₂ (ℓ + 1) ε c) gD' := by
    by_cases hcond : ContinuousOn (D.leftDiscMap q₂ (ℓ + 1) ε c) (Metric.closedBall 0 1) ∧
        MapsTo (D.leftDiscMap q₂ (ℓ + 1) ε c) (Metric.closedBall 0 1) (g ⁻¹' Icc a (c₂ - κ))
    · exact Handle.inclPair_discClass _ _ _ hcond.1 hcond.2 hsphc gD'
    · have h1 : Handle.discClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a c)
          (D.leftDiscMap q₂ (ℓ + 1) ε c) gD' = 0 := by
        unfold Handle.discClass
        rw [dite_eq_right (fun h => hcond ⟨h.1, h.2.1⟩)]
      have h2 : Handle.discClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a (c₂ - κ) \ D.slabCap (g q₂))
          (D.leftDiscMap q₂ (ℓ + 1) ε c) gD' = 0 := by
        unfold Handle.discClass
        rw [dite_eq_right (fun h => hcond ⟨h.1, h.2.1⟩)]
      rw [h1, h2, map_zero]
  have hbd := tripleBoundary_leftDisc hf D hq₂ (μ := ℓ) hS.hk₂ hε (hεr q₂ hq₂).2 hac hcτ
    (by linarith) ht'b hUlo gD'
  have key : ∀ (C : D.CollarChart c₂ κ) (θ : ℝ), η / 2 ≤ θ → D.isSlideChart C hq₁ hq₂ ε θ ℓ →
      ∀ (Y : (x : M) → TangentSpace I x), C.realizes K (Hs 1) Y →
      ∀ F : GradientLikeStrip I g a b crit, (∀ x, F.V x = D.V x + Y x) →
      (∀ x hx, F.chart x hx = D.chart x hx) →
      ∃ z₀ : EuclideanSpace ℝ (Fin (ℓ + 1)), 1 < ‖z₀‖ ∧ ‖z₀‖ < 2 ∧
        (∀ z ∈ Handle.annulus (ℓ + 1),
          D.slideAnnulus C Hs q₁ ℓ ε c z ∈ D.slabCap (g q₂) → z = z₀) ∧
        D.slideAnnulus C Hs q₁ ℓ ε c z₀ ∈ D.captured q₂ hq₂ ∧
        LinearMap.det (fderiv ℝ (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus C Hs q₁ ℓ ε c)
          z₀ : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) ≠ 0 ∧
        Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (F.leftSphereHit q₁ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') =
          Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereHit q₁ (ℓ + 1) ε c)
              (Handle.boundaryGen gD') +
            (s * ((SignType.sign (LinearMap.det (fderiv ℝ
              (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus C Hs q₁ ℓ ε c) z₀ :
                EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) :
                  SignType) : ℤ)) •
              Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereMap q₂ (ℓ + 1) ε c)
                (Handle.boundaryGen gD') := by
    intro C θ hθ hC Y hY F hF hFchart
    obtain ⟨hcont, hmaps, hbdm, z₀, hz1, hz2, huniq, hcap, hdiff, hdet⟩ :=
      slideAnnulus_spec hg D hcrit hq₁ hq₂ hS C hθ hC hfin
    refine ⟨z₀, hz1, hz2, huniq, hcap, hdet, ?_⟩
    obtain ⟨hb1, hb2⟩ := slideAnnulus_boundary hg D hq₁ hq₂ hS C hθ hC hfin hY F hF hFchart
    have hT := hΓ.1 (g ⁻¹' {a}) (g ⁻¹' Icc a c) (g ⁻¹' Icc a (c₂ - κ))
      (D.slideAnnulus C Hs q₁ ℓ ε c) hcont hmaps hbdm
    rw [Handle.sphereClass_congr _ _ hb1, Handle.sphereClass_congr _ _ hb2] at hT
    set r₁ : ℝ := min (‖z₀‖ - 1) (2 - ‖z₀‖) / 2 with hr₁def
    have hr₁ : 0 < r₁ := by
      rw [hr₁def]
      have : 0 < min (‖z₀‖ - 1) (2 - ‖z₀‖) := lt_min (by linarith) (by linarith)
      linarith
    have hball : ∀ r, r ≤ r₁ → Metric.closedBall z₀ r ⊆ {z | 1 < ‖z‖ ∧ ‖z‖ < 2} := by
      intro r hr z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hm1 : min (‖z₀‖ - 1) (2 - ‖z₀‖) ≤ ‖z₀‖ - 1 := min_le_left _ _
      have hm2 : min (‖z₀‖ - 1) (2 - ‖z₀‖) ≤ 2 - ‖z₀‖ := min_le_right _ _
      have h1 : ‖z₀‖ ≤ ‖z‖ + ‖z - z₀‖ := by
        have := norm_sub_le z (z - z₀)
        rwa [sub_sub_cancel] at this
      have h2 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
        have := norm_add_le z₀ (z - z₀)
        rwa [add_sub_cancel] at this
      constructor <;> linarith
    have hballA : ∀ r, r ≤ r₁ → Metric.closedBall z₀ r ⊆ Handle.annulus (ℓ + 1) :=
      fun r hr z hz => ⟨(hball r hr hz).1.le, (hball r hr hz).2.le⟩
    obtain ⟨r₀, hr₀, hloc⟩ := D.discClass_tube_local hf hcrit hε hεr hac hcτ hτt' ht'b hslab'
      hUup hq₂ rfl hS.hk₂ (by omega) (D.slideAnnulus C Hs q₁ ℓ ε c) z₀ hr₁
      (hcont.mono (hballA r₁ le_rfl)) (hmaps.mono_left (hballA r₁ le_rfl)) hcap
      (fun y hy hyc => huniq y (hballA r₁ le_rfl hy) hyc) hdiff hdet gD'
    set r : ℝ := min r₀ r₁ / 2 with hrdef
    have hr : 0 < r := by
      rw [hrdef]
      have : 0 < min r₀ r₁ := lt_min hr₀ hr₁
      linarith
    have hrr₀ : r < r₀ := by
      rw [hrdef]
      have : min r₀ r₁ ≤ r₀ := min_le_left _ _
      have : 0 < min r₀ r₁ := lt_min hr₀ hr₁
      linarith
    have hrr₁ : r ≤ r₁ := by
      rw [hrdef]
      have : min r₀ r₁ ≤ r₁ := min_le_right _ _
      have : 0 < min r₀ r₁ := lt_min hr₀ hr₁
      linarith
    have hrm := D.rm_pos q₂ hq₂
    have hloc' := hloc r hr hrr₀ (D.rm q₂ hq₂ / 2) (half_pos hrm) (half_lt_self hrm)
    have hsm := D.discClass_leftDisc_eq_smallDisc hf hcrit hε hεr hac hcτ hτt' ht'b hslab' hUlo
      hq₂ rfl hS.hk₂ (half_pos hrm) (half_lt_self hrm) gD'
    have hL := hΓ.2 (g ⁻¹' Icc a (c₂ - κ)) (D.slabCap (g q₂)) (D.slideAnnulus C Hs q₁ ℓ ε c) z₀ r
      hr (hball r hrr₁) hcont hmaps huniq
    have hAincl := Handle.inclPair_annulusClass (subset_refl _) hsub
      (D.slideAnnulus C Hs q₁ ℓ ε c) hcont hmaps hbdm Γ
    have heq : Handle.annulusClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a c)
        (D.slideAnnulus C Hs q₁ ℓ ε c) Γ =
        (s * ((SignType.sign (LinearMap.det (fderiv ℝ
          (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus C Hs q₁ ℓ ε c) z₀ :
            EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) :
              SignType) : ℤ)) •
          Handle.discClass (g ⁻¹' Icc a (c₂ - κ)) (g ⁻¹' Icc a c) (D.leftDiscMap q₂ (ℓ + 1) ε c)
            gD' := by
      apply hinj
      rw [hAincl, map_zsmul, hdiscIncl, hL, hloc', ← hsm, mul_smul]
    rw [heq, map_zsmul, hbd] at hT
    rw [hT]
    abel
  obtain ⟨z₀, hz1, hz2, -, hcap, hdet, h1⟩ := key Ch η (by linarith) hCh Z hZ E hE hEchart
  obtain ⟨z₀', -, -, huniq', -, -, h2⟩ := key Ch₂ (η / 2) le_rfl hCh₂ Z₂ hZ₂ E₂ hE₂ hE₂chart
  have hcapS : D.slideAnnulus Ch Hs q₁ ℓ ε c z₀ ∈ D.slabCap (g q₂) :=
    mem_iUnion.2 ⟨q₂, mem_iUnion.2 ⟨hq₂, mem_iUnion.2 ⟨rfl, hcap⟩⟩⟩
  obtain ⟨hcap₂, hsgn⟩ :=
    slide_tubeSign_twist hg D hq₁ hq₂ hS Ch Ch₂ hCh hCh₂ htw hfin ⟨hz1, hz2⟩ hcapS
  have hzz : z₀ = z₀' := huniq' z₀ ⟨hz1.le, hz2.le⟩ hcap₂
  subst hzz
  rw [hsgn] at h2
  have hsg : SignType.sign (LinearMap.det (fderiv ℝ
      (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ :
        EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]
    exact hdet
  revert h1 h2 hsg
  generalize SignType.sign (LinearMap.det (fderiv ℝ
      (D.tubeCoordE q₂ hq₂ ε (ℓ + 1) ∘ D.slideAnnulus Ch Hs q₁ ℓ ε c) z₀ :
        EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)))) = σ
  intro h1 h2 hsg
  refine ⟨s * (σ : ℤ), ?_, h1, ?_⟩
  · have hσ : (σ : ℤ) = 1 ∨ (σ : ℤ) = -1 := by
      rcases σ with _ | _ | _
      · exact absurd rfl hsg
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases hs with hs | hs <;> rcases hσ with hσ | hσ <;> rw [hs, hσ] <;> norm_num
  · rw [h2]
    have hneg : ((-σ : SignType) : ℤ) = -(σ : ℤ) := by
      rcases σ with _ | _ | _ <;> rfl
    rw [hneg, mul_neg, neg_zsmul, sub_eq_add_neg]

theorem exists_slideSetup {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hℓn : ℓ + 3 ≤ n) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) (hne : q₁ ≠ q₂)
    (hk₁ : (D.chart q₁ hq₁).k = ℓ + 1) (hk₂ : (D.chart q₂ hq₂).k = ℓ + 1) {c : ℝ} (hac : a < c)
    (hcq₂ : c < g q₂ - ε) (hq₂q₁ : g q₂ + ε < g q₁ - ε) (hq₁b : g q₁ < b)
    (hunit : ∀ y, g y ∈ Icc c (g q₂ - ε) ∪ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hslab : ∀ x ∈ crit, g x ∈ Icc c (g q₁ - ε) → x = q₂)
    (hidxL : ∀ x ∈ crit, g x = g q₁ → morseIndex I g x = ℓ + 1)
    (hidx : ∀ x ∈ crit, g x < g q₁ → 2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n)
    (hnoc : ∀ x (hx : x ∈ crit), g x = g q₁ → ∃ r > 0, D.noCommon x hx q₂ hq₂ r r)
    (hrmgap : ∀ x hx, D.rm x hx ^ 2 < g q₁ - g q₂ - 2 * ε)
    (hV₀ : PathConnectedSpace ↥(g ⁻¹' {a})) :
    ∃ c₂ κ : ℝ, D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ ∧ PathConnectedSpace ↥(g ⁻¹' {c₂}) ∧
      ∀ x (hx : x ∈ crit), g x = g q₁ →
        Disjoint (D.leftSphere x hx ε c₂) (D.rightSphere q₂ hq₂ ε c₂) := by
  have _ := hidxL
  have h8 : 8 * ε < D.rm q₁ hq₁ ^ 2 := (hεr q₁ hq₁).2
  have hgap₁ : D.rm q₁ hq₁ ^ 2 < g q₁ - g q₂ - 2 * ε := hrmgap q₁ hq₁
  have hgap : 10 * ε < g q₁ - g q₂ := by linarith
  refine ⟨(g q₁ + g q₂) / 2 - ε / 2, ε / 4, ?_⟩
  have hc₂lo : g q₂ + ε < (g q₁ + g q₂) / 2 - ε / 2 - ε / 4 := by linarith
  have hc₂hi : (g q₁ + g q₂) / 2 - ε / 2 + ε / 4 < g q₁ - ε := by linarith
  have hc₂mem : (g q₁ + g q₂) / 2 - ε / 2 ∈ Icc (g q₂ + ε) (g q₁ - ε) :=
    ⟨by linarith, by linarith⟩
  have hLR : ∀ x (hx : x ∈ crit), g x = g q₁ →
      Disjoint (D.leftSphere x hx ε ((g q₁ + g q₂) / 2 - ε / 2))
        (D.rightSphere q₂ hq₂ ε ((g q₁ + g q₂) / 2 - ε / 2)) := by
    intro x hx hxq
    obtain ⟨r, hr, hnc⟩ := hnoc x hx hxq
    refine disjoint_spheres_of_noCommon hg.smooth D hx hq₂ hε hεr hr (by linarith)
      (by rw [hxq]; linarith) ⟨by linarith, by linarith⟩ ?_ hnc
    intro z hz w hw
    rw [hxq] at hz
    exact hunit z (Or.inr hz) w hw
  refine ⟨?_, ?_, hLR⟩
  · refine
      { hε := hε
        hεr := hεr
        hℓ := hℓ
        hℓn := hℓn
        hk₁ := hk₁
        hk₂ := hk₂
        hne := hne
        hac := hac
        hcq₂ := hcq₂
        hκ := by linarith
        hq₂c₂ := hc₂lo
        hc₂q₁ := hc₂hi
        hq₁b := hq₁b
        hunit := hunit
        hslab := hslab
        hmodel := ?_
        hdisj := hLR q₁ hq₁ rfl }
    rintro x hx z ⟨w, hw, rfl⟩ hzI
    have hw' : morseNorm n w < D.rm x hx := hw
    have hwR : morseNorm n w ≤ (D.chart x hx).R := hw'.le.trans (D.hrm x hx).2
    have habs := (D.chart x hx).abs_f_chart_sub_le hwR
    have hw0 : 0 ≤ morseNorm n w := ModelField.morseNorm_nonneg w
    have hsq : morseNorm n w ^ 2 < D.rm x hx ^ 2 := by
      have := D.rm_pos x hx
      nlinarith
    have hgx := hrmgap x hx
    rw [abs_le] at habs
    obtain ⟨hz1, hz2⟩ := hzI
    by_cases hlow : g x < c
    · linarith
    by_cases hhigh : g q₁ - ε < g x
    · linarith
    have hxq₂ : x = q₂ := hslab x hx ⟨not_lt.1 hlow, not_lt.1 hhigh⟩
    subst hxq₂
    linarith
  · refine pathConnectedSpace_level hg D hcrit hε hεr (by linarith) (by linarith) ?_ ?_ hV₀
    · intro y hy w hw
      exact hunit y (Or.inr (hy ▸ hc₂mem)) w hw
    · intro x hx hxc
      exact hidx x hx (by linarith)

theorem exists_slide_realization {g : M → ℝ} (hg : MorseStrip I g a b)
    (D : GradientLikeStrip I g a b crit) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ}
    {ℓ : ℕ} {c c₂ κ : ℝ} (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ)
    (hidxL : ∀ x ∈ crit, g x = g q₁ → morseIndex I g x = ℓ + 1)
    (hpc : PathConnectedSpace ↥(g ⁻¹' {c₂}))
    (hLR : ∀ x (hx : x ∈ crit), g x = g q₁ →
      Disjoint (D.leftSphere x hx ε c₂) (D.rightSphere q₂ hq₂ ε c₂)) :
    ∃ η : ℝ, 0 < η ∧ ∃ Ch Ch₂ : D.CollarChart c₂ κ, D.isSlideChart Ch hq₁ hq₂ ε η ℓ ∧
      D.isSlideChart Ch₂ hq₁ hq₂ ε (η / 2) ℓ ∧ (∀ y, Ch₂.φ y = Ch.φ (slideTwist (n - 1) y)) ∧
      (∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₁ →
        Disjoint (D.leftSphere x hx ε c₂) (Ch.φ '' slideDom (n - 1) η) ∧
        Disjoint (D.leftSphere x hx ε c₂) (Ch₂.φ '' slideDom (n - 1) (η / 2))) ∧
      ∃ (K : Set (Fin (n - 1) → ℝ)) (Hs : ℝ → (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)),
        isSlideFinger (n - 1) ℓ (η / 2) K Hs ∧
        ∃ Z Z₂ : (x : M) → TangentSpace I x, Ch.realizes K (Hs 1) Z ∧ Ch₂.realizes K (Hs 1) Z₂ ∧
          ∃ E E₂ : GradientLikeStrip I g a b crit, (∀ x, E.V x = D.V x + Z x) ∧
            (∀ x, E₂.V x = D.V x + Z₂ x) ∧ (∀ x hx, E.chart x hx = D.chart x hx) ∧
            (∀ x hx, E.rm x hx = D.rm x hx) ∧ (∀ x hx, E₂.chart x hx = D.chart x hx) ∧
            ∀ x hx, E₂.rm x hx = D.rm x hx := by
  classical
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  obtain ⟨η, hη, Ch, hCh, hdisjCh⟩ := exists_slideChart hg D hq₁ hq₂ hS
    (crit.filter (fun x => g x = g q₁))
    (by
      intro x hx
      rw [Finset.mem_filter] at hx
      refine ⟨hx.1, ?_, (hidxL x hx.1 hx.2).le⟩
      rw [hx.2]; linarith [hS.hc₂q₁])
    (by
      intro x hx hxL _
      exact hLR x hx (Finset.mem_filter.1 hxL).2)
    hpc
  have hℓ1 : 1 ≤ ℓ := le_trans (by norm_num) hS.hℓ
  obtain ⟨Ch₂, hCh₂, htw⟩ := CollarChart.exists_twist hf Ch hη hS.hℓn hℓ1 hCh
  have hη2 : 0 < η / 2 := by linarith
  have hℓm : ℓ + 2 ≤ n - 1 := by have := hS.hℓn; omega
  obtain ⟨K, Hs, hfin⟩ := exists_finger_isotopy (n - 1) ℓ hℓ1 hℓm hη2
  obtain ⟨hKc, hKdom, hHs, hbij, hdiff, hsupp, h0, h1, -⟩ := id hfin
  have hdomsub : slideDom (n - 1) (η / 2) ⊆ slideDom (n - 1) η := by
    intro y hy
    refine ⟨hy.1, hy.2.1, fun j hj => ?_⟩
    have := hy.2.2 j hj
    linarith
  have hKU : K ⊆ Ch.U := by rw [hCh.1]; exact hKdom.trans hdomsub
  have hKU₂ : K ⊆ Ch₂.U := by rw [hCh₂.1]; exact hKdom
  obtain ⟨Z, hZ⟩ := Ch.exists_realizes hf hKc hKU Hs hHs hbij hdiff hsupp h0 h1
  obtain ⟨Z₂, hZ₂⟩ := Ch₂.exists_realizes hf hKc hKU₂ Hs hHs hbij hdiff hsupp h0 h1
  have hmodel : ∀ (C : D.CollarChart c₂ κ) (W : (x : M) → TangentSpace I x), K ⊆ C.U →
      C.realizes K (Hs 1) W →
      ∀ p hp, ∀ y, morseNorm n y < D.rm p hp → W ((D.chart p hp).χ y) = 0 := by
    intro C W hKC hW p hp y hy
    by_contra hne
    have hmem : (D.chart p hp).χ y ∈ tsupport W := subset_tsupport _ hne
    obtain ⟨⟨y', s⟩, ⟨hy'K, hs⟩, heq⟩ := hW.2.2.2.1 hmem
    exact C.avoid y' (hKC hy'K) s ⟨hs.1.le, hs.2.le⟩ p hp ⟨y, hy, heq.symm⟩
  obtain ⟨E, hE, hEchart, hErm⟩ := D.exists_addLevelField Z hZ.1 hZ.2.1 hZ.2.2.1
    (hmodel Ch Z hKU hZ)
  obtain ⟨E₂, hE₂, hE₂chart, hE₂rm⟩ := D.exists_addLevelField Z₂ hZ₂.1 hZ₂.2.1 hZ₂.2.2.1
    (hmodel Ch₂ Z₂ hKU₂ hZ₂)
  have htwdom : ∀ y ∈ slideDom (n - 1) (η / 2), slideTwist (n - 1) y ∈ slideDom (n - 1) η := by
    intro y hy
    obtain ⟨hy0, hy3, hyj⟩ := hy
    have hm : 4 ≤ n - 1 := by have := hS.hℓ; omega
    set θ := Real.pi * Real.smoothTransition (3 * coordN y 0 - 4) with hθ
    have hc : ∀ j, coordN (slideTwist (n - 1) y) j =
        if j = 1 then Real.cos θ * coordN y 1 - Real.sin θ * coordN y (n - 1 - 1)
        else if j = n - 1 - 1 then Real.sin θ * coordN y 1 + Real.cos θ * coordN y (n - 1 - 1)
        else coordN y j := by
      intro j
      by_cases hj : j < n - 1
      · have hL : coordN (slideTwist (n - 1) y) j = slideTwist (n - 1) y ⟨j, hj⟩ := by
          simp only [coordN, hj, ↓reduceDIte]
        rw [hL]
        unfold slideTwist
        split_ifs with h1 h2
        · rfl
        · rfl
        · simp only [coordN, hj, ↓reduceDIte]
      · have hj1 : j ≠ 1 := by omega
        have hj2 : j ≠ n - 1 - 1 := by omega
        simp only [coordN, hj, hj1, hj2, ↓reduceDIte, ↓reduceIte]
    have hb1 := hyj 1 le_rfl
    have hb2 := hyj (n - 1 - 1) (by omega)
    have hcos := Real.abs_cos_le_one θ
    have hsin := Real.abs_sin_le_one θ
    have key : ∀ u v w z : ℝ, |u| ≤ 1 → |v| ≤ 1 → |w| < η / 2 → |z| < η / 2 →
        |u * w + v * z| < η := by
      intro u v w z hu hv hw hz
      calc |u * w + v * z| ≤ |u * w| + |v * z| := abs_add_le _ _
        _ = |u| * |w| + |v| * |z| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |w| + 1 * |z| := by gcongr
        _ < η / 2 + η / 2 := by linarith
        _ = η := by ring
    have h00 : coordN (slideTwist (n - 1) y) 0 = coordN y 0 := by
      have h01 : (0 : ℕ) ≠ 1 := by omega
      have h02 : (0 : ℕ) ≠ n - 1 - 1 := by omega
      rw [hc 0]
      simp only [h01, h02, ↓reduceIte]
    refine ⟨by rw [h00]; exact hy0, by rw [h00]; exact hy3, fun j hj => ?_⟩
    rw [hc j]
    split_ifs with h1j h2j
    · have := key (Real.cos θ) (-Real.sin θ) (coordN y 1) (coordN y (n - 1 - 1)) hcos
        (by rwa [abs_neg]) hb1 hb2
      simpa [sub_eq_add_neg] using this
    · exact key (Real.sin θ) (Real.cos θ) (coordN y 1) (coordN y (n - 1 - 1)) hsin hcos hb1 hb2
    · have := hyj j hj
      linarith
  have himg : Ch₂.φ '' slideDom (n - 1) (η / 2) ⊆ Ch.φ '' slideDom (n - 1) η := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨slideTwist (n - 1) y, htwdom y hy, (htw y).symm⟩
  refine ⟨η, hη, Ch, Ch₂, hCh, hCh₂, htw, ?_, K, Hs, hfin, Z, Z₂, hZ, hZ₂, E, E₂, hE, hE₂,
    hEchart, hErm, hE₂chart, hE₂rm⟩
  intro x hx hxq hxne
  have h1' := hdisjCh x hx (Finset.mem_filter.2 ⟨hx, hxq⟩) hxne
  exact ⟨h1', h1'.mono_right himg⟩

theorem slide_untouched {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) {ε : ℝ} {ℓ : ℕ} {c c₂ κ : ℝ}
    (hS : D.SlideSetup hq₁ hq₂ ε ℓ c c₂ κ) (Ch : D.CollarChart c₂ κ) {η : ℝ}
    (hCh : D.isSlideChart Ch hq₁ hq₂ ε η ℓ) {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ slideDom (n - 1) η) {H₁ : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)}
    {Z : (x : M) → TangentSpace I x} (hZ : Ch.realizes K H₁ Z)
    (E : GradientLikeStrip I g a b crit) (hE : ∀ x, E.V x = D.V x + Z x)
    (hEchart : ∀ x hx, E.chart x hx = D.chart x hx) :
    (∀ z, g z ∉ Ioo (c₂ - κ) (c₂ + κ) → E.V z = D.V z) ∧
      (∀ x (hx : x ∈ crit), g x = g q₁ →
        Disjoint (D.leftSphere x hx ε c₂) (Ch.φ '' slideDom (n - 1) η) →
        ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          E.leftSphereHit x (ℓ + 1) ε c y = D.leftSphereHit x (ℓ + 1) ε c y) ∧
      ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        E.leftSphereMap q₂ (ℓ + 1) ε c y = D.leftSphereMap q₂ (ℓ + 1) ε c y := by
  have _ := hK
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hg.smooth
  have hKCh : K ⊆ Ch.U := by rw [hCh.1]; exact hKU
  obtain ⟨hflowE, hflowTop⟩ := Ch.flow_of_realizes hf hZ hKCh E hE
  have hbox : ∀ y ∈ K, ∀ s ∈ Ioo (-κ) κ, g (D.flow s (Ch.φ y)) = c₂ - s := by
    intro y hy s hs
    have hyU : y ∈ Ch.U := by rw [hCh.1]; exact hKU hy
    have hlev : g (Ch.φ y) = c₂ := Ch.level y hyU
    have hst := Ch.strip
    have hκ := Ch.hκ
    have h := f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := Ch.φ y) (T := s)
      (by rw [hlev]; exact ⟨by linarith, by linarith⟩)
      (by rw [hlev]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (by
        intro u hu p hp hmem
        have hu' : u ∈ Icc (-κ) κ := by
          rw [mem_uIcc] at hu
          rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
          · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        apply Ch.avoid y hyU u hu' p hp
        obtain ⟨w, hw, hwe⟩ := hmem
        exact ⟨w, lt_trans hw (D.r₀_lt_rm p hp), hwe⟩)
      s right_mem_uIcc
    rw [h, hlev]
  have hsuppLev : ∀ z ∈ tsupport Z, g z ∈ Ioo (c₂ - κ) (c₂ + κ) := by
    intro z hz
    obtain ⟨⟨y, s⟩, ⟨hy, hs⟩, rfl⟩ := hZ.2.2.2.1 hz
    rw [hbox y hy s hs]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hbelow : ∀ w : M, g w ≤ c₂ - κ → ∀ t, 0 ≤ t → E.flow t w = D.flow t w := by
    intro w hw t ht
    apply hflowE w t
    intro s hs hmem
    rw [min_eq_left ht, max_eq_right ht] at hs
    have h1 := hsuppLev _ hmem
    have h2 := f_flow_le (D := D) hf w hs.1
    linarith [h1.1]
  have habove : ∀ w : M, ∀ t, 0 ≤ t → c₂ + κ ≤ g (D.flow t w) → E.flow t w = D.flow t w := by
    intro w t ht hw
    apply hflowE w t
    intro s hs hmem
    rw [min_eq_left ht, max_eq_right ht] at hs
    have h1 := hsuppLev _ hmem
    have h2 := f_flow_antitone (D := D) hf w hs.2
    simp only at h2
    linarith [h1.2]
  have hR : ∀ x (hx : x ∈ crit), 2 * ε ≤ (D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (hS.hεr x hx).2
    have h2 := (D.hrm x hx).2
    have h3 := D.rm_pos x hx
    nlinarith
  have hsp : ∀ x (hx : x ∈ crit) (w : Fin (D.chart x hx).k → ℝ),
      ((D.chart x hx).χ ((D.chart x hx).sphereParam ε w) = x) ∨
      ((D.chart x hx).χ ((D.chart x hx).sphereParam ε w) ∈
          (D.chart x hx).χ '' (D.chart x hx).leftModelSphere ε ∧
        g ((D.chart x hx).χ ((D.chart x hx).sphereParam ε w)) = g x - ε) := by
    intro x hx w
    by_cases hw : w = 0
    · left
      have h0 : (D.chart x hx).sphereParam ε w = 0 := by
        subst hw
        rw [MorseNormalChart.sphereParam, ← ModelField.recombineL_apply]
        simp [MorseNormalChart.toE, Prod.mk_zero_zero]
      rw [h0, (D.chart x hx).hχ0]
    · right
      have hm := (D.chart x hx).sphereParam_mem_leftModelSphere hS.hε.le hw
      exact ⟨⟨_, hm, rfl⟩, (D.chart x hx).f_chart_of_mem_leftModelSphere (hR x hx) hm⟩
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · have hZz : Z z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsuppLev z h))
    rw [hE z, hZz, add_zero]
  · intro x hx hxq hdisj y hy
    simp only [leftSphereHit, hx, ↓reduceDIte]
    rw [hEchart x hx]
    rcases hsp x hx (Handle.reidx y) with hpx | ⟨hpS, hgp⟩
    · rw [hpx]
      unfold descend
      rw [E.flow_crit hx, D.flow_crit hx]
    · set p := (D.chart x hx).χ ((D.chart x hx).sphereParam ε (Handle.reidx y)) with hp
      set T₁ := g x - ε - (c₂ + κ) with hT₁
      have hε := hS.hε
      have hκ := hS.hκ
      have hT₁pos : 0 < T₁ := by rw [hT₁, hxq]; linarith [hS.hc₂q₁]
      have hlev0 := f_flow_eq_sub_of_levels (D := D) hf (x := p) (T := T₁ + 2 * κ)
        (by rw [hgp, hxq]; exact ⟨by linarith [hS.hac, hS.hcq₂, hS.hq₂c₂, hS.hc₂q₁],
          by linarith [hS.hq₁b]⟩)
        (by rw [hgp, hT₁, hxq]; exact ⟨by linarith [hS.hac, hS.hcq₂, hS.hq₂c₂],
          by linarith [hS.hc₂q₁, hS.hq₁b]⟩)
        (by
          intro z hz
          apply hS.hunit z
          right
          rw [hgp, hT₁, hxq, uIcc_of_ge (by linarith)] at hz
          exact ⟨by linarith [hz.1, hS.hq₂c₂], by linarith [hz.2]⟩)
      have hlev : ∀ s ∈ Icc 0 (T₁ + 2 * κ), g (D.flow s p) = g x - ε - s := by
        intro s hs
        rw [hlev0 s (by rw [uIcc_of_le (by linarith)]; exact hs), hgp]
      have hlevT : g (D.flow (T₁ + 2 * κ) p) = c₂ - κ := by
        rw [hlev _ (right_mem_Icc.2 (by linarith)), hT₁]; ring
      have hlevT₁ : g (D.flow T₁ p) = c₂ + κ := by
        rw [hlev _ ⟨hT₁pos.le, by linarith⟩, hT₁]; ring
      have hnot : D.flow T₁ p ∉ D.flow (-κ) '' (Ch.φ '' K) := by
        rintro ⟨_, ⟨k, hk, rfl⟩, hk'⟩
        have h1 : Ch.φ k = D.flow (T₁ + κ) p := by
          have := congrArg (D.flow κ) hk'
          rw [D.flow_flow (Ch.φ k) (-κ) κ, neg_add_cancel, flow_zero,
            D.flow_flow p T₁ κ] at this
          exact this
        have hmem1 : Ch.φ k ∈ D.leftSphere x hx ε c₂ := by
          refine ⟨p, hpS, ?_⟩
          rw [h1, hT₁]
          congr 1
          ring
        have hmem2 : Ch.φ k ∈ Ch.φ '' slideDom (n - 1) η := ⟨k, hKU hk, rfl⟩
        exact Set.disjoint_left.1 hdisj hmem1 hmem2
      have htop : E.flow (2 * κ) (D.flow T₁ p) = D.flow (2 * κ) (D.flow T₁ p) :=
        hflowTop _ hlevT₁ hnot
      have hagreeT₁ : ∀ s, 0 ≤ s → s ≤ T₁ → E.flow s p = D.flow s p := by
        intro s hs hsT
        apply habove p s hs
        rw [hlev s ⟨hs, by linarith⟩]
        linarith
      have hagree : ∀ s, 0 ≤ s → (s ≤ T₁ ∨ T₁ + 2 * κ ≤ s) → E.flow s p = D.flow s p := by
        intro s hs hs'
        rcases hs' with h | h
        · exact hagreeT₁ s hs h
        · have e1 : E.flow s p = E.flow (s - (T₁ + 2 * κ)) (E.flow (2 * κ) (E.flow T₁ p)) := by
            rw [E.flow_flow, E.flow_flow]
            congr 1
            ring
          have e2 : D.flow s p = D.flow (s - (T₁ + 2 * κ)) (D.flow (2 * κ) (D.flow T₁ p)) := by
            rw [D.flow_flow, D.flow_flow]
            congr 1
            ring
          rw [e1, e2, hagreeT₁ T₁ hT₁pos.le le_rfl, htop]
          apply hbelow
          · rw [D.flow_flow, hlevT]
          · linarith
      have hgE : ∀ s, 0 ≤ s → s ≤ T₁ + 2 * κ → c < g (E.flow s p) := by
        intro s _ hs2
        have h1 := f_flow_antitone (D := E) hf p hs2
        simp only at h1
        rw [hagree _ (by linarith) (Or.inr le_rfl), hlevT] at h1
        linarith [hS.hcq₂, hS.hq₂c₂]
      have hgD : ∀ s, 0 ≤ s → s ≤ T₁ + 2 * κ → c < g (D.flow s p) := by
        intro s _ hs2
        have h1 := f_flow_antitone (D := D) hf p hs2
        simp only at h1
        rw [hlevT] at h1
        linarith [hS.hcq₂, hS.hq₂c₂]
      have hset : {s : ℝ | 0 ≤ s ∧ g (E.flow s p) ≤ c} =
          {s : ℝ | 0 ≤ s ∧ g (D.flow s p) ≤ c} := by
        ext s
        constructor
        · rintro ⟨hs, hle⟩
          rcases le_or_gt s (T₁ + 2 * κ) with h | h
          · exact absurd hle (not_le.2 (hgE s hs h))
          · exact ⟨hs, by rw [← hagree s hs (Or.inr h.le)]; exact hle⟩
        · rintro ⟨hs, hle⟩
          rcases le_or_gt s (T₁ + 2 * κ) with h | h
          · exact absurd hle (not_le.2 (hgD s hs h))
          · exact ⟨hs, by rw [hagree s hs (Or.inr h.le)]; exact hle⟩
      have hhit : E.hitTime c p = D.hitTime c p := by
        unfold hitTime
        rw [hset]
      unfold descend
      rw [hhit]
      by_cases hne : ({s : ℝ | 0 ≤ s ∧ g (D.flow s p) ≤ c}).Nonempty
      · have hge : T₁ + 2 * κ ≤ D.hitTime c p := by
          unfold hitTime
          refine le_csInf hne (fun s hs => ?_)
          by_contra h
          exact absurd hs.2 (not_le.2 (hgD s hs.1 (not_le.1 h).le))
        exact hagree _ (by linarith) (Or.inr hge)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have h0 : D.hitTime c p = 0 := by
          unfold hitTime
          rw [hne, Real.sInf_empty]
        rw [h0]
        exact hagree 0 le_rfl (Or.inl hT₁pos.le)
  · intro y hy
    simp only [leftSphereMap, hq₂, ↓reduceDIte]
    rw [hEchart q₂ hq₂]
    have hlt : g ((D.chart q₂ hq₂).χ ((D.chart q₂ hq₂).sphereParam ε (Handle.reidx y))) ≤
        c₂ - κ := by
      rcases hsp q₂ hq₂ (Handle.reidx y) with hpx | ⟨_, hgp⟩
      · rw [hpx]; linarith [hS.hq₂c₂, hS.hε]
      · rw [hgp]; linarith [hS.hq₂c₂, hS.hε]
    exact hbelow _ hlt (g q₂ - ε - c) (by linarith [hS.hcq₂])

theorem exists_slideField {g : M → ℝ} (hg : MorseStrip I g a b) (D : GradientLikeStrip I g a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hℓn : ℓ + 3 ≤ n) {q₁ q₂ : M} (hq₁ : q₁ ∈ crit) (hq₂ : q₂ ∈ crit) (hne : q₁ ≠ q₂)
    (hk₁ : (D.chart q₁ hq₁).k = ℓ + 1) (hk₂ : (D.chart q₂ hq₂).k = ℓ + 1) {c : ℝ} (hac : a < c)
    (hcq₂ : c < g q₂ - ε) (hq₂q₁ : g q₂ + ε < g q₁ - ε) (hq₁b : g q₁ < b)
    (hunit : ∀ y, g y ∈ Icc c (g q₂ - ε) ∪ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx)
    (hslab : ∀ x ∈ crit, g x ∈ Icc c (g q₁ - ε) → x = q₂)
    (hidxL : ∀ x ∈ crit, g x = g q₁ → morseIndex I g x = ℓ + 1)
    (hidx : ∀ x ∈ crit, g x < g q₁ → 2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n)
    (hnoc : ∀ x (hx : x ∈ crit), g x = g q₁ → ∃ r > 0, D.noCommon x hx q₂ hq₂ r r)
    (hrmgap : ∀ x hx, D.rm x hx ^ 2 < g q₁ - g q₂ - 2 * ε)
    (hV₀ : PathConnectedSpace ↥(g ⁻¹' {a})) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (gD' : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk (ℓ + 1))))
      (ULift.down ⁻¹' diskSphere (ℓ + 1)) (ℓ + 1)) (hgD' : Handle.isGen gD') :
    ∃ E : GradientLikeStrip I g a b crit, (∀ x hx, E.chart x hx = D.chart x hx) ∧
      (∀ x hx, E.rm x hx = D.rm x hx) ∧
      (∃ c₂ κ : ℝ, g q₂ + ε < c₂ - κ ∧ c₂ + κ < g q₁ - ε ∧
        ∀ z, g z ∉ Ioo (c₂ - κ) (c₂ + κ) → E.V z = D.V z) ∧
      Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (E.leftSphereHit q₁ (ℓ + 1) ε c)
          (Handle.boundaryGen gD') =
        Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereHit q₁ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') +
          δ • Handle.sphereClass (g ⁻¹' Icc a c) (g ⁻¹' {a}) (D.leftSphereMap q₂ (ℓ + 1) ε c)
            (Handle.boundaryGen gD') ∧
      (∀ x (_hx : x ∈ crit), g x = g q₁ → x ≠ q₁ → ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        E.leftSphereHit x (ℓ + 1) ε c y = D.leftSphereHit x (ℓ + 1) ε c y) ∧
      (∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        E.leftSphereMap q₂ (ℓ + 1) ε c y = D.leftSphereMap q₂ (ℓ + 1) ε c y) ∧
      ∃ ρ > 0, ∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₂ → E.noCommon q₂ hq₂ x hx ρ ρ := by
  obtain ⟨c₂, κ, hS, hpc, hLR⟩ := exists_slideSetup hg D hcrit hε hεr hℓ hℓn hq₁ hq₂ hne hk₁ hk₂
    hac hcq₂ hq₂q₁ hq₁b hunit hslab hidxL hidx hnoc hrmgap hV₀
  obtain ⟨η, hη, Ch, Ch₂, hCh, hCh₂, htw, hLdisj, K, Hs, hfin, Z, Z₂, hZ, hZ₂, E, E₂, hE, hE₂,
    hEchart, hErm, hE₂chart, hE₂rm⟩ := exists_slide_realization hg D hq₁ hq₂ hS hidxL hpc hLR
  obtain ⟨m, hm, hcl₁, hcl₂⟩ := slide_class_change_pair hg D hcrit hq₁ hq₂ hS Ch Ch₂ hCh hCh₂ htw
    hfin hZ hZ₂ E E₂ hE hE₂ hEchart hE₂chart gD' hgD'
  have hK : IsCompact K := hfin.1
  have hKU₂ : K ⊆ slideDom (n - 1) (η / 2) := hfin.2.1
  have hmono : slideDom (n - 1) (η / 2) ⊆ slideDom (n - 1) η := by
    intro y hy
    refine ⟨hy.1, hy.2.1, fun j hj => ?_⟩
    have := hy.2.2 j hj
    linarith
  have hKU : K ⊆ slideDom (n - 1) η := hKU₂.trans hmono
  have hH₁K : ∀ y, y ∉ K → Hs 1 y = y := fun y hy => hfin.2.2.2.2.2.1 1 y hy
  have hH₁bij : Function.Bijective (Hs 1) := hfin.2.2.2.1 1
  have hend : ∀ y ∈ slideA (n - 1) ℓ, y ∈ slideDom (n - 1) (η / 2) →
      Hs 1 y ∉ slideB (n - 1) ℓ := hfin.2.2.2.2.2.2.2.2.2.1
  have hH₁ : ∀ θ : ℝ, K ⊆ slideDom (n - 1) θ → ∀ y ∈ slideA (n - 1) ℓ,
      y ∈ slideDom (n - 1) θ → Hs 1 y ∉ slideB (n - 1) ℓ := by
    intro θ _ y hyA _
    by_cases hyK : y ∈ K
    · exact hend y hyA (hKU₂ hyK)
    · rw [hH₁K y hyK]
      intro hyB
      have h1 := hyA.1
      have h2 := hyB.1
      rw [h1] at h2
      norm_num at h2
  have hunit' : ∀ y, g y ∈ Icc (g q₂ + ε) (g q₁ - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy x hx => hS.hunit y (Or.inr hy) x hx
  have hD : ∀ x (hx : x ∈ crit), g x = g q₁ → x ≠ q₁ →
      Disjoint (D.rightSphere q₂ hq₂ ε c₂) (D.leftSphere x hx ε c₂) :=
    fun x hx hxq _ => (hLR x hx hxq).symm
  rcases hm with hm | hm <;> rcases hδ with hδ | hδ
  · subst hm; subst hδ
    obtain ⟨hVeq, hhit, hsph⟩ := slide_untouched hg D hq₁ hq₂ hS Ch hCh hK hKU hZ E hE hEchart
    obtain ⟨ρ, hρ, hnc⟩ := noCommon_after_slide hg.smooth D hε hεr hq₁ hq₂ Ch hCh.1 hCh.2.1 hCh.2.2
      hS.hq₂c₂ hS.hc₂q₁ hunit' hS.hdisj (fun x hx h1 h2 => (hLdisj x hx h1 h2).1) hD hK hKU hH₁K
      hH₁bij (hH₁ η hKU) hZ E hE hEchart hErm
    exact ⟨E, hEchart, hErm, ⟨c₂, κ, hS.hq₂c₂, hS.hc₂q₁, hVeq⟩, hcl₁,
      fun x hx h1 h2 => hhit x hx h1 (hLdisj x hx h1 h2).1, hsph, ρ, hρ, hnc⟩
  · subst hm; subst hδ
    obtain ⟨hVeq, hhit, hsph⟩ :=
      slide_untouched hg D hq₁ hq₂ hS Ch₂ hCh₂ hK hKU₂ hZ₂ E₂ hE₂ hE₂chart
    obtain ⟨ρ, hρ, hnc⟩ := noCommon_after_slide hg.smooth D hε hεr hq₁ hq₂ Ch₂ hCh₂.1 hCh₂.2.1
      hCh₂.2.2 hS.hq₂c₂ hS.hc₂q₁ hunit' hS.hdisj (fun x hx h1 h2 => (hLdisj x hx h1 h2).2) hD hK
      hKU₂ hH₁K hH₁bij (hH₁ (η / 2) hKU₂) hZ₂ E₂ hE₂ hE₂chart hE₂rm
    refine ⟨E₂, hE₂chart, hE₂rm, ⟨c₂, κ, hS.hq₂c₂, hS.hc₂q₁, hVeq⟩, ?_,
      fun x hx h1 h2 => hhit x hx h1 (hLdisj x hx h1 h2).2, hsph, ρ, hρ, hnc⟩
    rw [hcl₂]; abel
  · subst hm; subst hδ
    obtain ⟨hVeq, hhit, hsph⟩ :=
      slide_untouched hg D hq₁ hq₂ hS Ch₂ hCh₂ hK hKU₂ hZ₂ E₂ hE₂ hE₂chart
    obtain ⟨ρ, hρ, hnc⟩ := noCommon_after_slide hg.smooth D hε hεr hq₁ hq₂ Ch₂ hCh₂.1 hCh₂.2.1
      hCh₂.2.2 hS.hq₂c₂ hS.hc₂q₁ hunit' hS.hdisj (fun x hx h1 h2 => (hLdisj x hx h1 h2).2) hD hK
      hKU₂ hH₁K hH₁bij (hH₁ (η / 2) hKU₂) hZ₂ E₂ hE₂ hE₂chart hE₂rm
    refine ⟨E₂, hE₂chart, hE₂rm, ⟨c₂, κ, hS.hq₂c₂, hS.hc₂q₁, hVeq⟩, ?_,
      fun x hx h1 h2 => hhit x hx h1 (hLdisj x hx h1 h2).2, hsph, ρ, hρ, hnc⟩
    rw [hcl₂]; abel
  · subst hm; subst hδ
    obtain ⟨hVeq, hhit, hsph⟩ := slide_untouched hg D hq₁ hq₂ hS Ch hCh hK hKU hZ E hE hEchart
    obtain ⟨ρ, hρ, hnc⟩ := noCommon_after_slide hg.smooth D hε hεr hq₁ hq₂ Ch hCh.1 hCh.2.1 hCh.2.2
      hS.hq₂c₂ hS.hc₂q₁ hunit' hS.hdisj (fun x hx h1 h2 => (hLdisj x hx h1 h2).1) hD hK hKU hH₁K
      hH₁bij (hH₁ η hKU) hZ E hE hEchart hErm
    exact ⟨E, hEchart, hErm, ⟨c₂, κ, hS.hq₂c₂, hS.hc₂q₁, hVeq⟩, hcl₁,
      fun x hx h1 h2 => hhit x hx h1 (hLdisj x hx h1 h2).1, hsph, ρ, hρ, hnc⟩

end GradientLikeStrip

end

end DifferentialGeometry.Topology
