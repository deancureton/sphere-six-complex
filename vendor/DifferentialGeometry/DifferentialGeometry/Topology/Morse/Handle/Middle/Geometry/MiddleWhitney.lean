module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import DifferentialGeometry.Topology.Morse.Handle.Middle.Geometry.MiddleLevels
public import DifferentialGeometry.Topology.Morse.Handle.Partners.GeneralPosition
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.TietzeExtension

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

def whitneyDom (m : ℕ) (η : ℝ) : Set (Fin m → ℝ) :=
  {y | coordN y 0 ^ 2 + coordN y 1 ^ 2 < (1 + η) ^ 2 ∧ -η < coordN y 1 ∧
    ∀ j, 2 ≤ j → |coordN y j| < η}

def whitneyA (m r : ℕ) : Set (Fin m → ℝ) :=
  {y | coordN y 1 = 0 ∧ ∀ j, r + 1 ≤ j → coordN y j = 0}

def whitneyB (m r : ℕ) : Set (Fin m → ℝ) :=
  {y | coordN y 0 ^ 2 + coordN y 1 ^ 2 = 1 ∧ ∀ j, 2 ≤ j → j ≤ r → coordN y j = 0}

def whitneyPt (m : ℕ) (σ : ℝ) : Fin m → ℝ := fun i => if (i : ℕ) = 0 then σ else 0

theorem exists_whitney_isotopy (m r : ℕ) (hr : 1 ≤ r) (hrm : r + 2 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set (Fin m → ℝ), IsCompact K ∧ K ⊆ whitneyDom m η ∧
      ∃ Hs : ℝ → (Fin m → ℝ) → (Fin m → ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => Hs p.1 p.2) ∧
        (∀ t, Function.Bijective (Hs t)) ∧ (∀ t y, Function.Bijective (fderiv ℝ (Hs t) y)) ∧
        (∀ t y, y ∉ K → Hs t y = y) ∧ (∀ t, t ≤ 0 → ∀ y, Hs t y = y) ∧
        (∀ t, 1 ≤ t → ∀ y, Hs t y = Hs 1 y) ∧
        ∀ y ∈ whitneyA m r, y ∈ whitneyDom m η → Hs 1 y ∉ whitneyB m r := by
  classical
  have hm3 : 3 ≤ m := by omega
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin m, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin m, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have h01 : i₀ ≠ i₁ := by
    intro h; rw [h] at hi₀; omega
  have hc0 : ∀ y : Fin m → ℝ, coordN y 0 = y i₀ := fun y => by
    have h : 0 < m := by omega
    simp only [coordN, h, dite_true]; congr 1; exact Fin.ext hi₀.symm
  have hc1 : ∀ y : Fin m → ℝ, coordN y 1 = y i₁ := fun y => by
    have h : 1 < m := by omega
    simp only [coordN, h, dite_true]; congr 1; exact Fin.ext hi₁.symm
  have hge2 : ∀ i : Fin m, i ≠ i₀ → i ≠ i₁ → 2 ≤ (i : ℕ) := by
    intro i h0 h1
    have h0' : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by rw [h, hi₀]))
    have h1' : (i : ℕ) ≠ 1 := fun h => h1 (Fin.ext (by rw [h, hi₁]))
    omega
  obtain ⟨a, a₂, γ, L, δ, ε, c, ha1, haa₂, ha₂γ, hL1, hLγ, hδ0, hδ1, hδγ, hε0, hεη, hc0', hc1',
      hcγ, hγη⟩ :
      ∃ a a₂ γ L δ ε c : ℝ, 1 < a ∧ a < a₂ ∧ a₂ ^ 2 < γ ∧ 1 < L ∧ L ^ 2 * γ < (1 + η) ^ 2 ∧
        0 < δ ∧ δ ≤ 1 ∧ δ ^ 2 * γ < η ^ 2 ∧ 0 < ε ∧ ε < η ∧ 0 < c ∧ c < 1 ∧ 1 < c ^ 2 * γ ∧
        γ < (1 + η) ^ 2 := by
    set e : ℝ := min η 1 with he
    have he0 : 0 < e := lt_min hη one_pos
    have he1 : e ≤ 1 := min_le_right _ _
    have heη : e ≤ η := min_le_left _ _
    have hpos : 0 < 1 + e / 2 := by linarith
    refine ⟨1 + e / 8, 1 + e / 4, (1 + e / 2) ^ 2, 1 + e / 8, e / 4, e / 2,
      (1 + e / 4) / (1 + e / 2), by linarith, by linarith, ?_, by linarith, ?_, by linarith,
      by linarith, ?_, by linarith, by linarith, by positivity, ?_, ?_, ?_⟩
    · exact pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero
    · have hee : e * e ≤ e * 1 := mul_le_mul_of_nonneg_left he1 he0.le
      have h1 : (1 + e / 8) * (1 + e / 2) < 1 + η := by linarith only [hee, he0, heη]
      have h2 : 0 ≤ (1 + e / 8) * (1 + e / 2) := by positivity
      calc (1 + e / 8) ^ 2 * (1 + e / 2) ^ 2 = ((1 + e / 8) * (1 + e / 2)) ^ 2 := by ring
        _ < (1 + η) ^ 2 := pow_lt_pow_left₀ h1 h2 two_ne_zero
    · have hee : e * e ≤ e * 1 := mul_le_mul_of_nonneg_left he1 he0.le
      have h1 : e / 4 * (1 + e / 2) < η := by linarith only [hee, he0, heη]
      have h2 : 0 ≤ e / 4 * (1 + e / 2) := by positivity
      calc (e / 4) ^ 2 * (1 + e / 2) ^ 2 = (e / 4 * (1 + e / 2)) ^ 2 := by ring
        _ < η ^ 2 := pow_lt_pow_left₀ h1 h2 two_ne_zero
    · rw [div_lt_one hpos]; linarith
    · rw [div_pow, div_mul_cancel₀ _ (by positivity)]
      have : (1 : ℝ) ^ 2 < (1 + e / 4) ^ 2 := pow_lt_pow_left₀ (by linarith) zero_le_one two_ne_zero
      simpa using this
    · exact pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero
  obtain ⟨T, hTs, hTm, hT0, hT1, hTz, hTo⟩ : ∃ T : ℝ → ℝ, ContDiff ℝ ∞ T ∧ Monotone T ∧
      (∀ x, 0 ≤ T x) ∧ (∀ x, T x ≤ 1) ∧ (∀ x, x ≤ 0 → T x = 0) ∧ (∀ x, 1 ≤ x → T x = 1) :=
    ⟨Real.smoothTransition, Real.smoothTransition.contDiff, Real.smoothTransition.monotone,
      Real.smoothTransition.nonneg, Real.smoothTransition.le_one,
      fun _ hx => Real.smoothTransition.zero_of_nonpos hx,
      fun _ hx => Real.smoothTransition.one_of_one_le hx⟩
  obtain ⟨S, hSs, hSm, hSlo, hShi, hS0⟩ : ∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧ Monotone S ∧
      (∀ x, x ≤ -δ → S x = x) ∧ (∀ x, L ≤ x → S x = x) ∧ S 0 = 1 := by
    have hu1 : ∀ x : ℝ, 0 ≤ x → T ((x + δ) / δ) = 1 := fun x hx =>
      hTo _ (by rw [le_div_iff₀ hδ0]; linarith)
    have hw0 : ∀ x : ℝ, x ≤ 1 → T ((x - 1) / (L - 1)) = 0 := fun x hx =>
      hTz _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    have hlo : ∀ x : ℝ, x ≤ 0 → x + T ((x + δ) / δ) * (1 - T ((x - 1) / (L - 1))) * (1 - x) =
        x + T ((x + δ) / δ) * (1 - x) := fun x hx => by rw [hw0 x (by linarith)]; ring
    have hhi : ∀ x : ℝ, 0 ≤ x → x + T ((x + δ) / δ) * (1 - T ((x - 1) / (L - 1))) * (1 - x) =
        1 + T ((x - 1) / (L - 1)) * (x - 1) := fun x hx => by rw [hu1 x hx]; ring
    have hhi1 : ∀ x : ℝ, 0 ≤ x → 1 ≤ 1 + T ((x - 1) / (L - 1)) * (x - 1) := by
      intro x hx
      rcases le_total x 1 with h | h
      · rw [hw0 x h]; simp
      · linarith only [mul_nonneg (hT0 ((x - 1) / (L - 1))) (show (0 : ℝ) ≤ x - 1 by linarith)]
    refine ⟨fun x => x + T ((x + δ) / δ) * (1 - T ((x - 1) / (L - 1))) * (1 - x), by fun_prop,
      ?_, ?_, ?_, ?_⟩
    · intro x x' hxx'
      dsimp only
      rcases le_total x' 0 with h' | h'
      · rw [hlo x (by linarith), hlo x' h']
        have hm : T ((x + δ) / δ) ≤ T ((x' + δ) / δ) :=
          hTm (div_le_div_of_nonneg_right (by linarith) hδ0.le)
        linarith only [mul_nonneg (sub_nonneg.2 hxx') (sub_nonneg.2 (hT1 ((x' + δ) / δ))),
          mul_nonneg (sub_nonneg.2 hm) (show (0 : ℝ) ≤ 1 - x by linarith)]
      · rw [hhi x' h']
        rcases le_total x 0 with h | h
        · rw [hlo x h]
          have := hhi1 x' h'
          linarith only [this, mul_nonneg (sub_nonneg.2 (hT1 ((x + δ) / δ))) (show (0 : ℝ) ≤ 1 - x by linarith)]
        · rw [hhi x h]
          rcases le_total x 1 with h1 | h1
          · rw [hw0 x h1]; have := hhi1 x' h'; linarith
          · have hm : T ((x - 1) / (L - 1)) ≤ T ((x' - 1) / (L - 1)) :=
              hTm (div_le_div_of_nonneg_right (by linarith) (by linarith))
            linarith only [
              mul_le_mul hm (show x - 1 ≤ x' - 1 by linarith) (by linarith)
                (le_trans (hT0 _) hm)]
    · intro x hx
      dsimp only
      rw [hTz ((x + δ) / δ) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ0.le)]; ring
    · intro x hx
      dsimp only
      rw [hTo ((x - 1) / (L - 1)) (by rw [le_div_iff₀ (by linarith)]; linarith)]; ring
    · dsimp only
      rw [hu1 0 le_rfl, hw0 0 (by norm_num)]; ring
  obtain ⟨χ, hχs, hχ0, hχ1, hχsupp, hχone, hχupd⟩ : ∃ χ : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧
      (∀ y, χ y ≠ 0 → y i₀ ^ 2 ≤ a ^ 2 ∧ ∀ i : Fin m, 2 ≤ (i : ℕ) → y i ^ 2 ≤ ε ^ 2) ∧
      (∀ y, y i₀ ^ 2 ≤ 1 → (∀ i : Fin m, 2 ≤ (i : ℕ) → y i = 0) → χ y = 1) ∧
      (∀ y r, χ (Function.update y i₁ r) = χ y) := by
    refine ⟨fun y => (1 - T ((y i₀ ^ 2 - 1) / (a ^ 2 - 1))) *
      ∏ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (i : ℕ)), (1 - T (y i ^ 2 / ε ^ 2)),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ContDiff.mul (by fun_prop) (contDiff_prod fun i _ => by fun_prop)
    · intro y
      exact mul_nonneg (sub_nonneg.2 (hT1 _))
        (Finset.prod_nonneg fun i _ => sub_nonneg.2 (hT1 _))
    · intro y
      have hp0 := Finset.prod_nonneg (s := Finset.univ.filter (fun i : Fin m => 2 ≤ (i : ℕ)))
        fun i _ => sub_nonneg.2 (hT1 (y i ^ 2 / ε ^ 2))
      have hp1 := Finset.prod_le_one₀ (s := Finset.univ.filter (fun i : Fin m => 2 ≤ (i : ℕ)))
        (fun i _ => sub_nonneg.2 (hT1 (y i ^ 2 / ε ^ 2)))
        fun i _ => by linarith [hT0 (y i ^ 2 / ε ^ 2)]
      have hq0 := hT0 ((y i₀ ^ 2 - 1) / (a ^ 2 - 1))
      have hq1 := hT1 ((y i₀ ^ 2 - 1) / (a ^ 2 - 1))
      dsimp only
      linarith only [hp1, mul_le_mul_of_nonneg_right (show 1 - T ((y i₀ ^ 2 - 1) / (a ^ 2 - 1)) ≤ 1 by linarith) hp0]
    · intro y hy
      have hy' := mul_ne_zero_iff.1 hy
      refine ⟨?_, ?_⟩
      · by_contra hlt
        push Not at hlt
        apply hy'.1
        rw [hTo _ (by rw [le_div_iff₀ (by nlinarith only [ha1])]; linarith)]; ring
      · intro i hi
        have := (Finset.prod_ne_zero_iff.1 hy'.2) i (by simp [hi])
        by_contra hlt
        push Not at hlt
        apply this
        rw [hTo _ (by rw [le_div_iff₀ (by positivity)]; linarith)]; ring
    · intro y hy hyi
      dsimp only
      rw [hTz _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith only [ha1])),
        Finset.prod_eq_one fun i hi => by
          rw [hyi i (Finset.mem_filter.1 hi).2]; simp [hTz 0 le_rfl]]
      ring
    · intro y r
      dsimp only
      rw [Function.update_of_ne h01]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi2 : 2 ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2
      have hi' : i ≠ i₁ := by
        intro h; rw [h, hi₁] at hi2; omega
      rw [Function.update_of_ne hi']
  obtain ⟨Rf, hRs, hRpos, hRγ, hReq, hRupd⟩ : ∃ Rf : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ Rf ∧
      (∀ y, 0 < Rf y) ∧ (∀ y, Rf y ^ 2 ≤ γ) ∧
      (∀ y, y i₀ ^ 2 ≤ a ^ 2 → Rf y ^ 2 = γ - y i₀ ^ 2) ∧
      (∀ y r, Rf (Function.update y i₁ r) = Rf y) := by
    have hF : ∀ y : Fin m → ℝ,
        0 < γ - y i₀ ^ 2 * (1 - T ((y i₀ ^ 2 - a ^ 2) / (a₂ ^ 2 - a ^ 2))) := by
      intro y
      have hden : 0 < a₂ ^ 2 - a ^ 2 := by nlinarith only [ha1, haa₂]
      by_cases hv : 1 ≤ (y i₀ ^ 2 - a ^ 2) / (a₂ ^ 2 - a ^ 2)
      · rw [hTo _ hv]; nlinarith only [ha₂γ, sq_nonneg a₂]
      · push Not at hv
        rw [div_lt_one hden] at hv
        linarith only [hv, ha₂γ,
          mul_nonneg (sq_nonneg (y i₀)) (hT0 ((y i₀ ^ 2 - a ^ 2) / (a₂ ^ 2 - a ^ 2)))]
    refine ⟨fun y => Real.sqrt (γ - y i₀ ^ 2 * (1 - T ((y i₀ ^ 2 - a ^ 2) / (a₂ ^ 2 - a ^ 2)))),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact ContDiff.sqrt (by fun_prop) fun y => (hF y).ne'
    · intro y; exact Real.sqrt_pos.2 (hF y)
    · intro y
      dsimp only
      rw [Real.sq_sqrt (hF y).le]
      linarith only [mul_nonneg (sq_nonneg (y i₀)) (sub_nonneg.2 (hT1 ((y i₀ ^ 2 - a ^ 2) / (a₂ ^ 2 - a ^ 2))))]
    · intro y hy
      dsimp only
      rw [Real.sq_sqrt (hF y).le, hTz _ (div_nonpos_of_nonpos_of_nonneg (by linarith)
        (by nlinarith only [ha1, haa₂]))]
      ring
    · intro y r
      dsimp only
      rw [Function.update_of_ne h01]
  have hfix : ∀ k R r : ℝ, 0 < R → (r / R ≤ -δ ∨ L ≤ r / R) →
      (1 - k) * r + k * R * S (r / R) = r := by
    intro k R r hR hr
    have : S (r / R) = r / R := hr.elim (hSlo _) (hShi _)
    rw [this]; field_simp; ring
  have fib : ∀ k R : ℝ, 0 ≤ k → k ≤ c → 0 < R →
      StrictMono (fun r => (1 - k) * r + k * R * S (r / R)) ∧
      Function.Surjective (fun r => (1 - k) * r + k * R * S (r / R)) ∧
      ∀ r d, HasDerivAt (fun r => (1 - k) * r + k * R * S (r / R)) d r → 0 < d := by
    intro k R hk0 hkc hR
    have hmono : Monotone (fun r => k * R * S (r / R)) := by
      intro r r' hrr'
      exact mul_le_mul_of_nonneg_left (hSm (div_le_div_of_nonneg_right hrr' hR.le))
        (mul_nonneg hk0 hR.le)
    refine ⟨?_, ?_, ?_⟩
    · intro r r' hrr'
      have h1 := hmono hrr'.le
      dsimp only at h1 ⊢
      have : (1 - k) * r < (1 - k) * r' := mul_lt_mul_of_pos_left hrr' (by linarith)
      linarith
    · intro z
      by_cases hz : z / R ≤ -δ ∨ L ≤ z / R
      · exact ⟨z, hfix k R z hR hz⟩
      · push Not at hz
        have hcont : Continuous (fun r => (1 - k) * r + k * R * S (r / R)) := by
          have := hSs.continuous; fun_prop
        have hab : -δ * R ≤ L * R := by nlinarith only [hδ0, hL1, hR]
        have hlo : -δ * R / R = -δ := by field_simp
        have hhi : L * R / R = L := by field_simp
        obtain ⟨r, -, hr⟩ := intermediate_value_Icc hab hcont.continuousOn
          (show z ∈ Set.Icc _ _ from ⟨by
            rw [hfix k R _ hR (Or.inl hlo.le)]
            have := (lt_div_iff₀ hR).1 hz.1; linarith, by
            rw [hfix k R _ hR (Or.inr hhi.ge)]
            have := (div_lt_iff₀ hR).1 hz.2; linarith⟩)
        exact ⟨r, hr⟩
    · intro r d hd
      have hd' : HasDerivAt (fun r => k * R * S (r / R)) (d - (1 - k)) r := by
        have := hd.sub ((hasDerivAt_id r).const_mul (1 - k))
        convert this using 1
        · funext x; simp
        · simp
      have := hmono.deriv_nonneg (x := r)
      rw [hd'.deriv] at this
      linarith
  have hκ0 : ∀ t y, 0 ≤ T t * c * χ y := fun t y =>
    mul_nonneg (mul_nonneg (hT0 t) hc0'.le) (hχ0 y)
  have hκc : ∀ t y, T t * c * χ y ≤ c := fun t y => by
    have h1 : T t * χ y ≤ 1 := by
      calc T t * χ y ≤ 1 * χ y := mul_le_mul_of_nonneg_right (hT1 t) (hχ0 y)
        _ ≤ 1 := by linarith [hχ1 y]
    calc T t * c * χ y = c * (T t * χ y) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc0'.le
      _ = c := mul_one c
  obtain ⟨Hs, hHs⟩ : ∃ Hs : ℝ → (Fin m → ℝ) → (Fin m → ℝ), ∀ t y i, Hs t y i =
      if i = i₁ then (1 - T t * c * χ y) * y i₁ + T t * c * χ y * Rf y * S (y i₁ / Rf y)
      else y i := ⟨_, fun _ _ _ => rfl⟩
  have hsmooth : ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => Hs p.1 p.2) := by
    have heq : (fun p : ℝ × (Fin m → ℝ) => Hs p.1 p.2) = fun p i => if i = i₁ then
        (1 - T p.1 * c * χ p.2) * p.2 i₁ + T p.1 * c * χ p.2 * Rf p.2 * S (p.2 i₁ / Rf p.2)
        else p.2 i := by
      funext p i; exact hHs _ _ _
    rw [heq]
    refine contDiff_pi.2 fun i => ?_
    by_cases hi : i = i₁
    · simp only [hi, ite_true]
      fun_prop (disch := exact fun _ => (hRpos _).ne')
    · simp only [hi, ite_false]
      fun_prop
  have hline : ∀ t y r, Hs t (Function.update y i₁ r) i₁ =
      (1 - T t * c * χ y) * r + T t * c * χ y * Rf y * S (r / Rf y) := by
    intro t y r
    rw [hHs, ite_eq_left rfl, hχupd, hRupd, Function.update_self]
  have hoff : ∀ t y i, i ≠ i₁ → Hs t y i = y i := fun t y i hi => by rw [hHs, ite_eq_right hi]
  set K : Set (Fin m → ℝ) := {y | y i₀ ^ 2 ≤ a ^ 2 ∧ (∀ i : Fin m, 2 ≤ (i : ℕ) → y i ^ 2 ≤ ε ^ 2) ∧
    -δ * Rf y ≤ y i₁ ∧ y i₁ ≤ L * Rf y} with hK
  have hKy1 : ∀ y ∈ K, y i₁ ^ 2 ≤ L ^ 2 * γ := by
    rintro y ⟨-, -, h1, h2⟩
    have hR := hRpos y
    have hRg := hRγ y
    have h3 : -(L * Rf y) ≤ y i₁ := by
      linarith [mul_le_mul_of_nonneg_right (show δ ≤ L by linarith) hR.le]
    have : y i₁ ^ 2 ≤ (L * Rf y) ^ 2 := sq_le_sq' h3 h2
    have h4 : (L * Rf y) ^ 2 = L ^ 2 * Rf y ^ 2 := by ring
    have h5 : L ^ 2 * Rf y ^ 2 ≤ L ^ 2 * γ := mul_le_mul_of_nonneg_left hRg (sq_nonneg L)
    linarith
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hRc := hRs.continuous
      simp only [hK, Set.ofPred_and, Set.ofPred_forall]
      refine IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop))
        (IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun _ =>
          isClosed_le (by fun_prop) (by fun_prop))
          (IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop))
            (isClosed_le (by fun_prop) (by fun_prop))))
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨a + 1 + η + ε, fun y hy => ?_⟩
      have hM : 0 ≤ a + 1 + η + ε := by linarith
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hM]
      have hy1 := hKy1 y hy
      obtain ⟨hK0, hK2, -, -⟩ := hy
      intro i
      rw [Real.norm_eq_abs]
      refine abs_le_of_sq_le_sq ?_ hM
      by_cases h0 : i = i₀
      · rw [h0]
        have : a ^ 2 ≤ (a + 1 + η + ε) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith only [this, hK0]
      by_cases h1 : i = i₁
      · rw [h1]
        have : (1 + η) ^ 2 ≤ (a + 1 + η + ε) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith only [this, hy1, hLγ]
      · have := hK2 i (hge2 i h0 h1)
        have h2 : ε ^ 2 ≤ (a + 1 + η + ε) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith only [this, h2]
  have hKdom : K ⊆ whitneyDom m η := by
    intro y hy
    have hR := hRpos y
    have hRe := hReq y hy.1
    have hy1 := hKy1 y hy
    refine ⟨?_, ?_, ?_⟩
    · rw [hc0, hc1]
      have h3 : -(L * Rf y) ≤ y i₁ := by
        linarith only [hy.2.2.1, mul_le_mul_of_nonneg_right (show δ ≤ L by linarith) hR.le]
      have : y i₁ ^ 2 ≤ (L * Rf y) ^ 2 := sq_le_sq' h3 hy.2.2.2
      have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hL1]
      have hLR : (L * Rf y) ^ 2 = L ^ 2 * γ - L ^ 2 * y i₀ ^ 2 := by rw [mul_pow, hRe]; ring
      have h4 := mul_le_mul_of_nonneg_right hL2 (sq_nonneg (y i₀))
      linarith only [this, hLR, h4, hLγ]
    · rw [hc1]
      have hRg := hRγ y
      have : δ * Rf y < η := by
        by_contra hh
        push Not at hh
        have h5 : δ ^ 2 * Rf y ^ 2 ≤ δ ^ 2 * γ := mul_le_mul_of_nonneg_left hRg (sq_nonneg δ)
        have h6 := mul_le_mul hh hh hη.le (by positivity)
        have h7 : δ * Rf y * (δ * Rf y) = δ ^ 2 * Rf y ^ 2 := by ring
        linarith only [h5, h6, h7, hδγ]
      linarith [hy.2.2.1]
    · intro j hj
      unfold coordN
      split_ifs with hjm
      · have := hy.2.1 ⟨j, hjm⟩ hj
        exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt this (pow_lt_pow_left₀ hεη hε0.le two_ne_zero)) hη.le
      · simpa using hη
  refine ⟨K, hKc, hKdom, Hs, hsmooth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    refine ⟨?_, ?_⟩
    · intro y y' h
      have hi : ∀ i, i ≠ i₁ → y i = y' i := fun i hi => by
        have := congrFun h i; rwa [hoff t y i hi, hoff t y' i hi] at this
      have hy' : y' = Function.update y i₁ (y' i₁) := by
        funext i
        by_cases hii : i = i₁
        · rw [hii]; simp
        · rw [Function.update_of_ne hii, hi i hii]
      have h1 := congrFun h i₁
      rw [hy', hline, ← Function.update_eq_self i₁ y, hline, Function.update_eq_self] at h1
      have := (fib (T t * c * χ y) (Rf y) (hκ0 t y) (hκc t y) (hRpos y)).1.injective h1
      rw [hy', ← this, Function.update_eq_self]
    · intro z
      obtain ⟨r, hr⟩ := (fib (T t * c * χ z) (Rf z) (hκ0 t z) (hκc t z) (hRpos z)).2.1 (z i₁)
      refine ⟨Function.update z i₁ r, funext fun i => ?_⟩
      by_cases hii : i = i₁
      · rw [hii, hline]; exact hr
      · rw [hoff t _ i hii, Function.update_of_ne hii]
  · intro t y
    have hsm_t : ContDiff ℝ ∞ (Hs t) := hsmooth.comp (contDiff_const.prodMk contDiff_id)
    have hD : HasFDerivAt (Hs t) (fderiv ℝ (Hs t) y) y :=
      ((hsm_t.differentiable (by simp)) y).hasFDerivAt
    set D := fderiv ℝ (Hs t) y with hDdef
    have hcomp : ∀ i, i ≠ i₁ → ∀ v, D v i = v i := by
      intro i hi v
      have h1 := (hasFDerivAt_pi'.1 hD) i
      have heq : (fun x => Hs t x i) = fun x => x i := funext fun x => hoff t x i hi
      rw [heq] at h1
      have := h1.unique (hasFDerivAt_apply i y)
      exact congrArg (fun φ : (Fin m → ℝ) →L[ℝ] ℝ => φ v) this
    have hD' : HasFDerivAt (Hs t) D (Function.update y i₁ (y i₁)) := by
      rwa [Function.update_eq_self]
    have hl := hD'.comp_hasDerivAt (y i₁) (hasDerivAt_update y i₁ (y i₁))
    have hl1 := (hasDerivAt_pi.1 hl) i₁
    have heq : (fun r => (Hs t ∘ Function.update y i₁) r i₁) =
        fun r => (1 - T t * c * χ y) * r + T t * c * χ y * Rf y * S (r / Rf y) :=
      funext fun r => hline t y r
    rw [heq] at hl1
    have hpos := (fib (T t * c * χ y) (Rf y) (hκ0 t y) (hκc t y) (hRpos y)).2.2 _ _ hl1
    have hinj : Function.Injective D := by
      refine (injective_iff_map_eq_zero D).2 fun v hv => ?_
      have hvi : ∀ i, i ≠ i₁ → v i = 0 := fun i hi => by
        rw [← hcomp i hi v, hv]; rfl
      have hvd : v = v i₁ • Pi.single i₁ 1 := by
        funext i
        by_cases hii : i = i₁
        · rw [hii]; simp
        · rw [hvi i hii]; simp [hii]
      have h2 : D v i₁ = v i₁ * D (Pi.single i₁ 1) i₁ := by
        conv_lhs => rw [hvd]
        simp
      rw [hv] at h2
      have h3 : v i₁ = 0 := by
        rcases mul_eq_zero.1 h2.symm with h | h
        · exact h
        · exact absurd h hpos.ne'
      rw [hvd, h3, zero_smul]
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (D : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))).1 hinj⟩
  · intro t y hy
    by_contra hne
    apply hy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hii : i = i₁ := by
      by_contra hii; exact hi (hoff t y i hii)
    rw [hii, hHs, ite_eq_left rfl] at hi
    have hχne : χ y ≠ 0 := by
      intro h0; apply hi; rw [h0]; ring
    have hS : ¬ (y i₁ / Rf y ≤ -δ ∨ L ≤ y i₁ / Rf y) := fun hh => hi (hfix _ _ _ (hRpos y) hh)
    push Not at hS
    obtain ⟨h1, h2⟩ := hχsupp y hχne
    exact ⟨h1, h2, ((lt_div_iff₀ (hRpos y)).1 hS.1).le, ((div_lt_iff₀ (hRpos y)).1 hS.2).le⟩
  · intro t ht y
    funext i
    by_cases hii : i = i₁
    · rw [hii, hHs, ite_eq_left rfl, hTz t ht]; ring
    · exact hoff t y i hii
  · intro t ht y
    funext i
    rw [hHs, hHs, hTo t ht, hTo 1 le_rfl]
  · intro y hA _ hB
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨hB1, hB2⟩ := hB
    have hy1 : y i₁ = 0 := by rw [← hc1 y]; exact hA1
    have hyi : ∀ i : Fin m, 2 ≤ (i : ℕ) → y i = 0 := by
      intro i hi
      have hne : i ≠ i₁ := by
        intro h; rw [h, hi₁] at hi; omega
      by_cases hir : (i : ℕ) ≤ r
      · have := hB2 i hi hir
        simp only [coordN, dite_eq_left i.isLt, Fin.eta] at this
        rwa [hoff 1 y i hne] at this
      · have := hA2 i (by omega)
        simpa [coordN, dite_eq_left i.isLt] using this
    rw [hc0, hc1, hoff 1 y i₀ h01, hHs, ite_eq_left rfl, hy1, hTo 1 le_rfl, zero_div, hS0] at hB1
    by_cases hy0 : y i₀ ^ 2 ≤ 1
    · rw [hχone y hy0 hyi] at hB1
      have hRe := hReq y (by nlinarith only [hy0, ha1])
      have hc2 : c ^ 2 ≤ 1 := by nlinarith only [hc0', hc1']
      have hcR : (c * Rf y) ^ 2 = c ^ 2 * γ - c ^ 2 * y i₀ ^ 2 := by rw [mul_pow, hRe]; ring
      have h8 := mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg (y i₀))
      have h9 : (1 - 1 * c * 1) * 0 + 1 * c * 1 * Rf y * 1 = c * Rf y := by ring
      rw [h9] at hB1
      linarith only [hB1, hcR, h8, hcγ]
    · push Not at hy0
      have h9 : (1 - 1 * c * χ y) * 0 + 1 * c * χ y * Rf y * 1 = c * χ y * Rf y := by ring
      rw [h9] at hB1
      linarith only [hB1, hy0, sq_nonneg (c * χ y * Rf y)]

theorem exists_sphere_arc {N : ℕ} (hN : 3 ≤ N) (S : Finset (EuclideanSpace ℝ (Fin N)))
    {z₁ z₂ : EuclideanSpace ℝ (Fin N)} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (hne : z₁ ≠ z₂)
    (h₁S : z₁ ∉ S) (h₂S : z₂ ∉ S) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ γ ∧ (∀ t, ‖γ t‖ = 1) ∧ γ (-1) = z₁ ∧
      γ 1 = z₂ ∧ InjOn γ (Icc (-2) 2) ∧ (∀ t, deriv γ t ≠ 0) ∧ ∀ t ∈ Icc (-2 : ℝ) 2, γ t ∉ S := by
  classical
  have hperp : ∀ x y : EuclideanSpace ℝ (Fin N), ∃ u : EuclideanSpace ℝ (Fin N), u ≠ 0 ∧
      inner ℝ x u = 0 ∧ inner ℝ y u = 0 := by
    intro x y
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := Submodule.span ℝ {x, y}
    have hK1 : Module.finrank ℝ K ≤ 2 := by
      have h := finrank_span_le_card (R := ℝ) ({x, y} : Set (EuclideanSpace ℝ (Fin N)))
      refine h.trans ?_
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_le_two
    have hK2 := K.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at hK2
    have hK3 : Kᗮ ≠ ⊥ := by
      intro h
      rw [← Submodule.finrank_eq_zero] at h
      omega
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK3
    rw [Submodule.mem_orthogonal] at hu
    exact ⟨u, hu0, hu x (Submodule.subset_span (by simp)),
      hu y (Submodule.subset_span (by simp))⟩
  obtain ⟨d, hd⟩ : ∃ d : EuclideanSpace ℝ (Fin N), d = (1 / 2 : ℝ) • (z₂ - z₁) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : EuclideanSpace ℝ (Fin N), m = (1 / 2 : ℝ) • (z₁ + z₂) := ⟨_, rfl⟩
  have hdm : inner ℝ d m = 0 := by
    rw [hd, hm, real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_add_right,
      inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h₁, h₂,
      real_inner_comm z₁ z₂]
    ring
  have hd0 : d ≠ 0 := by
    rw [hd]
    intro h
    rw [smul_eq_zero] at h
    rcases h with h | h
    · norm_num at h
    · exact hne (sub_eq_zero.mp h).symm
  obtain ⟨u, hu0, hdu, hmu⟩ := hperp d m
  obtain ⟨w, ρ, hw0, hρ, hmρ, hdw, hwu⟩ : ∃ w : EuclideanSpace ℝ (Fin N), ∃ ρ : ℝ, w ≠ 0 ∧
      0 ≤ ρ ∧ m = ρ • w ∧ inner ℝ d w = 0 ∧ inner ℝ w u = 0 := by
    by_cases hm0 : m = 0
    · obtain ⟨v, hv0, hdv, huv⟩ := hperp d u
      exact ⟨v, 0, hv0, le_rfl, by simp [hm0], hdv, by rw [real_inner_comm]; exact huv⟩
    · exact ⟨m, 1, hm0, zero_le_one, by simp, hdm, hmu⟩
  have hwd : inner ℝ w d = 0 := by rw [real_inner_comm]; exact hdw
  have hud : inner ℝ u d = 0 := by rw [real_inner_comm]; exact hdu
  have huw : inner ℝ u w = 0 := by rw [real_inner_comm]; exact hwu
  have hD : 0 < ‖d‖ ^ 2 := by positivity
  have hW : 0 < ‖w‖ ^ 2 := by positivity
  have hU : 0 < ‖u‖ ^ 2 := by positivity
  let a : ℝ → ℝ → EuclideanSpace ℝ (Fin N) := fun θ t =>
    t • d + (ρ + 1 - t ^ 2) • w + ((1 - t ^ 2) * θ) • u
  have hid : ∀ θ t, inner ℝ (a θ t) d = t * ‖d‖ ^ 2 := by
    intro θ t
    simp only [a, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hwd, hud]
    ring
  have hiw : ∀ θ t, inner ℝ (a θ t) w = (ρ + 1 - t ^ 2) * ‖w‖ ^ 2 := by
    intro θ t
    simp only [a, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hdw, huw]
    ring
  have hiu : ∀ θ t, inner ℝ (a θ t) u = ((1 - t ^ 2) * θ) * ‖u‖ ^ 2 := by
    intro θ t
    simp only [a, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hdu, hwu]
    ring
  have ha0 : ∀ θ t, a θ t ≠ 0 := by
    intro θ t h
    have e1 := hid θ t
    have e2 := hiw θ t
    rw [h, inner_zero_left] at e1 e2
    have ht : t = 0 := by
      rcases mul_eq_zero.mp e1.symm with h' | h'
      · exact h'
      · exact absurd h' hD.ne'
    subst ht
    nlinarith
  have hkey : ∀ θ θ' t t' μ : ℝ, 0 < μ → a θ t = μ • a θ' t' →
      μ = 1 ∧ t = t' ∧ (1 - t ^ 2) * θ = (1 - t ^ 2) * θ' := by
    intro θ θ' t t' μ hμ h
    have e1 := congrArg (fun x => inner ℝ x d) h
    have e2 := congrArg (fun x => inner ℝ x w) h
    have e3 := congrArg (fun x => inner ℝ x u) h
    simp only [real_inner_smul_left, hid, hiw, hiu] at e1 e2 e3
    have f1 : t = μ * t' := by
      have : (t - μ * t') * ‖d‖ ^ 2 = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hD.ne'
    have f2 : ρ + 1 - t ^ 2 = μ * (ρ + 1 - t' ^ 2) := by
      have : (ρ + 1 - t ^ 2 - μ * (ρ + 1 - t' ^ 2)) * ‖w‖ ^ 2 = 0 := by linear_combination e2
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hW.ne'
    have f3 : (1 - μ) * (ρ + 1 + μ * t' ^ 2) = 0 := by
      rw [f1] at f2
      linear_combination f2
    have hμ1 : μ = 1 := by
      rcases mul_eq_zero.mp f3 with h' | h'
      · linarith
      · nlinarith [sq_nonneg t']
    subst hμ1
    have htt : t = t' := by linarith
    subst htt
    refine ⟨rfl, rfl, ?_⟩
    have : ((1 - t ^ 2) * θ - (1 - t ^ 2) * θ') * ‖u‖ ^ 2 = 0 := by linear_combination e3
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hU.ne'
  have haend : ∀ θ, a θ (-1) = z₁ ∧ a θ 1 = z₂ := by
    intro θ
    have e1 : ρ + 1 - (-1 : ℝ) ^ 2 = ρ := by ring
    have e2 : (1 - (-1 : ℝ) ^ 2) * θ = 0 := by ring
    have e3 : ρ + 1 - (1 : ℝ) ^ 2 = ρ := by ring
    have e4 : (1 - (1 : ℝ) ^ 2) * θ = 0 := by ring
    simp only [a, e1, e2, e3, e4, zero_smul, add_zero, ← hmρ]
    rw [hd, hm]
    constructor <;> module
  have hacd : ∀ θ, ContDiff ℝ ∞ (a θ) := by
    intro θ
    simp only [a]
    fun_prop
  let γ : ℝ → ℝ → EuclideanSpace ℝ (Fin N) := fun θ t => ‖a θ t‖⁻¹ • a θ t
  have hnorm0 : ∀ θ t, ‖a θ t‖ ≠ 0 := fun θ t => norm_ne_zero_iff.mpr (ha0 θ t)
  have hγcd : ∀ θ, ContDiff ℝ ∞ (γ θ) := by
    intro θ
    exact ((ContDiff.norm ℝ (hacd θ) (ha0 θ)).inv (hnorm0 θ)).smul (hacd θ)
  have hγn : ∀ θ t, ‖γ θ t‖ = 1 := by
    intro θ t
    simp only [γ, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hnorm0 θ t)
  have hγend : ∀ θ, γ θ (-1) = z₁ ∧ γ θ 1 = z₂ := by
    intro θ
    refine ⟨?_, ?_⟩
    · simp only [γ, (haend θ).1, h₁, inv_one, one_smul]
    · simp only [γ, (haend θ).2, h₂, inv_one, one_smul]
  have hγeq : ∀ θ θ' t t', γ θ t = γ θ' t' →
      a θ t = (‖a θ t‖ * ‖a θ' t'‖⁻¹) • a θ' t' := by
    intro θ θ' t t' h
    have h' : ‖a θ t‖⁻¹ • a θ t = ‖a θ' t'‖⁻¹ • a θ' t' := h
    rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ (hnorm0 θ t), one_smul]
  have hμpos : ∀ θ θ' t t', 0 < ‖a θ t‖ * ‖a θ' t'‖⁻¹ := by
    intro θ θ' t t'
    have := norm_pos_iff.mpr (ha0 θ t)
    have := norm_pos_iff.mpr (ha0 θ' t')
    positivity
  have hsub : ∀ s ∈ (S : Set (EuclideanSpace ℝ (Fin N))),
      {θ : ℝ | ∃ t, γ θ t = s}.Subsingleton := by
    intro s hs θ₁ hθ₁ θ₂ hθ₂
    obtain ⟨t₁, ht₁⟩ := hθ₁
    obtain ⟨t₂, ht₂⟩ := hθ₂
    obtain ⟨-, -, hθθ⟩ := hkey θ₁ θ₂ t₁ t₂ _ (hμpos θ₁ θ₂ t₁ t₂)
      (hγeq θ₁ θ₂ t₁ t₂ (ht₁.trans ht₂.symm))
    by_cases h1 : 1 - t₁ ^ 2 = 0
    · exfalso
      have hs' : s ∈ S := Finset.mem_coe.mp hs
      have : t₁ = -1 ∨ t₁ = 1 := by
        have : (t₁ + 1) * (t₁ - 1) = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp this with h | h
        · left; linarith
        · right; linarith
      rcases this with h | h
      · rw [h, (hγend θ₁).1] at ht₁
        exact h₁S (ht₁ ▸ hs')
      · rw [h, (hγend θ₁).2] at ht₁
        exact h₂S (ht₁ ▸ hs')
    · exact mul_left_cancel₀ h1 hθθ
  have hfin : (⋃ s ∈ (S : Set (EuclideanSpace ℝ (Fin N))), {θ : ℝ | ∃ t, γ θ t = s}).Finite :=
    S.finite_toSet.biUnion fun s hs => (hsub s hs).finite
  obtain ⟨θ, hθ⟩ := hfin.exists_notMem
  refine ⟨γ θ, hγcd θ, hγn θ, (hγend θ).1, (hγend θ).2, ?_, ?_, ?_⟩
  · intro s _ t _ h
    exact (hkey θ θ s t _ (hμpos θ θ s t) (hγeq θ θ s t h)).2.1
  · intro t h0
    have hA : HasDerivAt (a θ) ((1 : ℝ) • d + (-(2 * t)) • w + (-(2 * t) * θ) • u) t := by
      have h1 := (hasDerivAt_id t).smul_const d
      have h2 := ((hasDerivAt_pow 2 t).const_sub (ρ + 1)).smul_const w
      have h3 := (((hasDerivAt_pow 2 t).const_sub 1).mul_const θ).smul_const u
      convert (h1.add h2).add h3 using 1
      · funext y
        simp only [a, Pi.add_apply, id]
      · norm_num
    have hr : DifferentiableAt ℝ (fun t => ‖a θ t‖) t :=
      ((ContDiff.norm ℝ (hacd θ) (ha0 θ)).differentiable (by simp)) t
    have hg : DifferentiableAt ℝ (γ θ) t := ((hγcd θ).differentiable (by simp)) t
    have hB := hr.hasDerivAt.smul hg.hasDerivAt
    have hfun : (fun t => ‖a θ t‖) • γ θ = a θ := by
      funext x
      simp only [Pi.smul_apply', γ, smul_smul, mul_inv_cancel₀ (hnorm0 θ x), one_smul]
    rw [hfun, h0, smul_zero, zero_add] at hB
    have hAB := hA.unique hB
    have hAk : (1 : ℝ) • d + (-(2 * t)) • w + (-(2 * t) * θ) • u =
        (deriv (fun t => ‖a θ t‖) t * ‖a θ t‖⁻¹) • a θ t := by
      rw [hAB, mul_smul]
    have e1 := congrArg (fun x => inner ℝ x d) hAk
    have e2 := congrArg (fun x => inner ℝ x w) hAk
    simp only [real_inner_smul_left, hid, hiw, inner_add_left, real_inner_self_eq_norm_sq, hwd,
      hud, huw, hdw] at e1 e2
    set k := deriv (fun t => ‖a θ t‖) t * ‖a θ t‖⁻¹
    have f1 : 1 = k * t := by
      have : (1 - k * t) * ‖d‖ ^ 2 = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hD.ne'
    have f2 : -(2 * t) = k * (ρ + 1 - t ^ 2) := by
      have : (-(2 * t) - k * (ρ + 1 - t ^ 2)) * ‖w‖ ^ 2 = 0 := by linear_combination e2
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hW.ne'
    have : ρ + 1 + t ^ 2 = 0 := by linear_combination (ρ + 1 - t ^ 2) * f1 - t * f2
    nlinarith [sq_nonneg t]
  · intro t _ ht
    apply hθ
    simp only [mem_iUnion]
    exact ⟨γ θ t, ht, t, rfl⟩

theorem exists_disc_of_simplyConnected {Y : Set M} (hY : SimplyConnectedSpace ↥Y) (γ : ℝ → M)
    (hγ : Continuous γ) (hγY : ∀ θ, γ θ ∈ Y) (hper : ∀ θ, γ (θ + 1) = γ θ) :
    ∃ F : EuclideanSpace ℝ (Fin 2) → M, ContinuousOn F (Metric.closedBall 0 1) ∧
      MapsTo F (Metric.closedBall 0 1) Y ∧
      ∀ θ : ℝ, F (WithLp.toLp 2 ![Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)]) = γ θ := by
  classical
  have h1 : γ 1 = γ 0 := by simpa using hper 0
  let y0 : Y := ⟨γ 0, hγY 0⟩
  let L : Path y0 y0 :=
    { toFun := fun t => ⟨γ t, hγY t⟩
      continuous_toFun := (hγ.comp continuous_subtype_val).subtype_mk _
      source' := by ext; simp [y0]
      target' := by ext; simp [y0, h1] }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic L (Path.refl y0)
  let H' : unitInterval × unitInterval → M := fun p => (H p : M)
  have hH'c : Continuous H' := continuous_subtype_val.comp H.continuous
  have hH'Y : ∀ p, H' p ∈ Y := fun p => (H p).2
  have hH'0 : ∀ t : unitInterval, H' (0, t) = γ t := fun t => by
    have := H.apply_zero t
    exact congrArg Subtype.val this
  have hH'1 : ∀ t : unitInterval, H' (1, t) = γ 0 := fun t => by
    have := H.apply_one t
    exact congrArg Subtype.val this
  have hH'src : ∀ s : unitInterval, H' (s, 0) = γ 0 := fun s => congrArg Subtype.val (H.source s)
  have hH'tgt : ∀ s : unitInterval, H' (s, 1) = γ 0 := fun s => congrArg Subtype.val (H.target s)
  let c : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
    WithLp.toLp 2 ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)]
  have hnorm2 : ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = √(x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
    intro x
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hcn : ∀ t, ‖c t‖ = 1 := by
    intro t
    rw [hnorm2]
    simp [c]
  have hcc : Continuous c := by
    apply (PiLp.continuous_toLp 2 _).comp
    refine continuous_pi fun i => ?_
    fin_cases i
    · change Continuous fun a : ℝ => Real.cos (2 * Real.pi * a)
      fun_prop
    · change Continuous fun a : ℝ => Real.sin (2 * Real.pi * a)
      fun_prop
  have hcper : ∀ t, c (Int.fract t) = c t := by
    intro t
    have e : 2 * Real.pi * Int.fract t = 2 * Real.pi * t - (⌊t⌋ : ℤ) * (2 * Real.pi) := by
      rw [Int.fract]; ring
    simp only [c, e, Real.cos_periodic.sub_int_mul_eq, Real.sin_periodic.sub_int_mul_eq]
  let P : unitInterval × unitInterval → EuclideanSpace ℝ (Fin 2) := fun p =>
    (1 - (p.1 : ℝ)) • c p.2
  have hPn : ∀ p, ‖P p‖ = 1 - (p.1 : ℝ) := by
    intro p
    simp only [P, norm_smul, hcn, mul_one, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith [unitInterval.le_one p.1])
  have hPball : ∀ p, P p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro p
    rw [mem_closedBall_zero_iff, hPn]
    linarith [unitInterval.nonneg p.1]
  let P' : unitInterval × unitInterval → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun p => ⟨P p, hPball p⟩
  have hPc : Continuous P := by
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hcc.comp (continuous_subtype_val.comp continuous_snd))
  have hP'c : Continuous P' := hPc.subtype_mk _
  have hP'surj : Function.Surjective P' := by
    rintro ⟨z, hz⟩
    rw [mem_closedBall_zero_iff] at hz
    by_cases hz0 : z = 0
    · refine ⟨(1, 0), Subtype.ext ?_⟩
      simp [P', P, hz0]
    · let w : ℂ := ⟨z.ofLp 0, z.ofLp 1⟩
      have hwn : ‖w‖ = ‖z‖ := by
        rw [Complex.norm_eq_sqrt_sq_add_sq, hnorm2]
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hwn
        linarith
      let t : ℝ := Int.fract (Complex.arg w / (2 * Real.pi))
      have ht : c t = c (Complex.arg w / (2 * Real.pi)) := hcper _
      have hcos : Real.cos (2 * Real.pi * t) = z.ofLp 0 / ‖z‖ := by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 0) ht
        simp only [c] at this
        simp only [Matrix.cons_val_zero] at this
        rw [this, mul_div_cancel₀ _ (by positivity), Complex.cos_arg hw0, hwn]
      have hsin : Real.sin (2 * Real.pi * t) = z.ofLp 1 / ‖z‖ := by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 1) ht
        simp only [c] at this
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        rw [this, mul_div_cancel₀ _ (by positivity), Complex.sin_arg, hwn]
      refine ⟨(⟨1 - ‖z‖, by constructor <;> linarith⟩,
        ⟨t, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩), Subtype.ext ?_⟩
      ext i
      fin_cases i
      · simp only [P', P, c, sub_sub_cancel, PiLp.smul_apply, smul_eq_mul]
        simp only [Fin.zero_eta, Matrix.cons_val_zero]
        rw [hcos]; field_simp
      · simp only [P', P, c, sub_sub_cancel, PiLp.smul_apply, smul_eq_mul]
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hsin]; field_simp
  have hfib : ∀ p q, P p = P q → H' p = H' q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ hpq
    have hss : s = s' := by
      have := congrArg norm hpq
      rw [hPn, hPn] at this
      exact Subtype.ext (by simpa using this)
    subst hss
    by_cases hs1 : (s : ℝ) = 1
    · have : s = 1 := Subtype.ext hs1
      subst this
      rw [hH'1, hH'1]
    · have hne : (1 - (s : ℝ)) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
      have hct : c t = c t' := smul_right_injective _ hne hpq
      have hc0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 0) hct
      have hc1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 1) hct
      simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one] at hc0 hc1
      obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc0 hc1)
      have hk' : (t : ℝ) - t' = k := by
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        apply mul_left_cancel₀ hpi
        linarith
      have ht0 := unitInterval.nonneg t
      have ht1 := unitInterval.le_one t
      have ht0' := unitInterval.nonneg t'
      have ht1' := unitInterval.le_one t'
      have hkl : (-1 : ℝ) ≤ k := by linarith
      have hku : (k : ℝ) ≤ 1 := by linarith
      have hkl' : (-1 : ℤ) ≤ k := by exact_mod_cast hkl
      have hku' : k ≤ 1 := by exact_mod_cast hku
      obtain hk0 | hk0 | hk0 : k = -1 ∨ k = 0 ∨ k = 1 := by omega
      · subst hk0
        have e1 : t = 0 := Subtype.ext (by push_cast at hk'; change (t : ℝ) = 0; linarith)
        have e2 : t' = 1 := Subtype.ext (by push_cast at hk'; change (t' : ℝ) = 1; linarith)
        subst e1 e2
        rw [hH'src, hH'tgt]
      · subst hk0
        have : t = t' := Subtype.ext (by push_cast at hk'; linarith)
        rw [this]
      · subst hk0
        have e1 : t = 1 := Subtype.ext (by push_cast at hk'; change (t : ℝ) = 1; linarith)
        have e2 : t' = 0 := Subtype.ext (by push_cast at hk'; change (t' : ℝ) = 0; linarith)
        subst e1 e2
        rw [hH'src, hH'tgt]
  have hq : Topology.IsQuotientMap P' := hP'c.isClosedMap.isQuotientMap hP'c hP'surj
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → M :=
    fun x => H' (Classical.choose (hP'surj x))
  have hg : ∀ p, g (P' p) = H' p := fun p =>
    hfib _ _ (congrArg Subtype.val (Classical.choose_spec (hP'surj (P' p))))
  have hgc : Continuous g := by
    rw [hq.continuous_iff]
    have : g ∘ P' = H' := funext hg
    rw [this]
    exact hH'c
  have hgY : ∀ x, g x ∈ Y := fun x => hH'Y _
  refine ⟨fun z => if h : z ∈ Metric.closedBall 0 1 then g ⟨z, h⟩ else γ 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hgc using 1
    funext x
    change (if h : (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall 0 1 then g ⟨x, h⟩
      else γ 0) = g x
    split_ifs with h
    · rfl
    · exact absurd x.2 h
  · intro z hz
    simp only [hz, dite_true]
    exact hgY _
  · intro θ
    have hmem : c θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [mem_closedBall_zero_iff, hcn]
    have hθ : (⟨c θ, hmem⟩ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) =
        P' (0, ⟨Int.fract θ, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩) := by
      apply Subtype.ext
      simp [P', P, hcper]
    change (if h : c θ ∈ Metric.closedBall 0 1 then g ⟨c θ, h⟩ else γ 0) = γ θ
    split_ifs
    rw [hθ, hg, hH'0]
    have e : θ = Int.fract θ + (⌊θ⌋ : ℤ) * 1 := by rw [Int.fract]; ring
    conv_rhs => rw [e]
    exact ((show Function.Periodic γ 1 from hper).int_mul _ _).symm

def frameExtends {k N : ℕ} (F : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N)) :
    Prop :=
  ∃ G : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N),
    ContinuousOn G (Metric.closedBall 0 1) ∧
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (G z)) ∧
    ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, G z = F z

theorem frameExtends_of_homotopy {k N : ℕ}
    (H : ℝ → EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N))
    (hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => H p.1 p.2)
      (Icc 0 1 ×ˢ Metric.sphere 0 1))
    (hind : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      LinearIndependent ℝ (H t z))
    (h0 : frameExtends (H 0)) (F : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N))
    (h1 : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, H 1 z = F z) : frameExtends F := by
  obtain ⟨G₀, hG₀c, hG₀i, hG₀b⟩ := h0
  refine ⟨fun z => if ‖z‖ ≤ 1 / 2 then G₀ ((2 : ℝ) • z) else H (2 * ‖z‖ - 1) (‖z‖⁻¹ • z),
    ?_, ?_, ?_⟩
  · have hfr : frontier {a : EuclideanSpace ℝ (Fin 2) | ‖a‖ ≤ 1 / 2} ⊆
        {a | ‖a‖ = 1 / 2} :=
      frontier_le_subset_eq continuous_norm continuous_const
    have hcl1 : closure {a : EuclideanSpace ℝ (Fin 2) | ‖a‖ ≤ 1 / 2} ⊆
        {a | ‖a‖ ≤ 1 / 2} :=
      (isClosed_le continuous_norm continuous_const).closure_subset
    have hcl2 : closure {a : EuclideanSpace ℝ (Fin 2) | ¬ ‖a‖ ≤ 1 / 2} ⊆
        {a | 1 / 2 ≤ ‖a‖} := by
      have : {a : EuclideanSpace ℝ (Fin 2) | ¬ ‖a‖ ≤ 1 / 2} = {a | 1 / 2 < ‖a‖} := by
        ext a; simp [not_le]
      rw [this]
      exact closure_lt_subset_le continuous_const continuous_norm
    apply ContinuousOn.if
    · intro a ha
      have hn : ‖a‖ = 1 / 2 := hfr ha.2
      have hs : (2 : ℝ) • a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, hn]; norm_num
      rw [hG₀b _ hs, hn]
      have : (1 / 2 : ℝ)⁻¹ • a = (2 : ℝ) • a := by norm_num
      rw [this]
      norm_num
    · have h2 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 2) => (2 : ℝ) • z)
          (Metric.closedBall 0 1 ∩ closure {a | ‖a‖ ≤ 1 / 2}) :=
        (continuous_id.const_smul (2 : ℝ)).continuousOn
      refine hG₀c.comp h2 ?_
      intro a ha
      have hn : ‖a‖ ≤ 1 / 2 := hcl1 ha.2
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      norm_num
      linarith
    · have hmaps : MapsTo
          (fun z : EuclideanSpace ℝ (Fin 2) => ((2 * ‖z‖ - 1 : ℝ), ‖z‖⁻¹ • z))
          (Metric.closedBall 0 1 ∩ closure {a | ¬ ‖a‖ ≤ 1 / 2})
          (Icc 0 1 ×ˢ Metric.sphere 0 1) := by
        intro a ha
        have hn : 1 / 2 ≤ ‖a‖ := hcl2 ha.2
        have hn1 : ‖a‖ ≤ 1 := by
          have := ha.1
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have ha0 : a ≠ 0 := by
          intro h; rw [h, norm_zero] at hn; norm_num at hn
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha0)]
      have hφ : ContinuousOn
          (fun z : EuclideanSpace ℝ (Fin 2) => ((2 * ‖z‖ - 1 : ℝ), ‖z‖⁻¹ • z))
          (Metric.closedBall 0 1 ∩ closure {a | ¬ ‖a‖ ≤ 1 / 2}) := by
        intro a ha
        have hn : 1 / 2 ≤ ‖a‖ := hcl2 ha.2
        have hne : ‖a‖ ≠ 0 := by linarith
        apply ContinuousAt.continuousWithinAt
        refine ContinuousAt.prodMk ?_ ?_
        · exact ((continuous_const.mul continuous_norm).sub continuous_const).continuousAt
        · exact (continuous_norm.continuousAt.inv₀ hne).smul continuousAt_id
      exact hH.comp hφ hmaps
  · intro z hz
    have hz1 : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
    by_cases hn : ‖z‖ ≤ 1 / 2
    · dsimp only
      simp only [hn, ↓reduceIte]
      apply hG₀i
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      norm_num
      linarith
    · dsimp only
      simp only [hn, ↓reduceIte]
      have hn' : 1 / 2 < ‖z‖ := lt_of_not_ge hn
      have hz0 : z ≠ 0 := by
        intro h; rw [h, norm_zero] at hn'; norm_num at hn'
      apply hind
      · constructor <;> linarith
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  · intro z hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hn' : ¬ ‖z‖ ≤ 1 / 2 := by rw [hn]; norm_num
    dsimp only
    simp only [hn', ↓reduceIte]
    rw [hn]
    norm_num
    exact h1 z hz

theorem exists_smooth_frame_near {k N : ℕ}
    (F : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N))
    (hF : ContinuousOn F (Metric.sphere 0 1))
    (hind : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (F z)) :
    ∃ F' : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N), ContDiff ℝ 1 F' ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        LinearIndependent ℝ ((1 - t) • F' z + t • F z) := by
  obtain ⟨δ, hδ, hδO⟩ := ((isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).image_of_continuousOn
    hF).exists_thickening_subset_open
    (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin N)) (ι := Fin k))
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact hind z hz)
  let tS : EuclideanSpace ℝ (Fin 2) → Set (Fin k → EuclideanSpace ℝ (Fin N)) :=
    fun z => {v | z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → dist v (F z) < δ}
  have htS : ∀ z, Convex ℝ (tS z) := fun z => (convex_ball (F z) δ).setOfPred_const_imp
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
    (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (n := 1) htS (by
      intro x
      refine ⟨F x, ?_⟩
      by_cases hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
      · have hc := hF x hx
        have hev : ∀ᶠ y in nhdsWithin x (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
            dist (F y) (F x) < δ := hc (Metric.ball_mem_nhds (F x) hδ)
        rw [eventually_nhdsWithin_iff] at hev
        filter_upwards [hev] with y hy hys
        rw [dist_comm]
        exact hy hys
      · filter_upwards [(Metric.isClosed_sphere).isOpen_compl.mem_nhds hx] with y hy hys
        exact absurd hys hy)
  refine ⟨g, contMDiff_iff_contDiff.mp g.contMDiff, ?_⟩
  intro t ht z hz
  have hmem : (1 - t) • g z + t • F z ∈ Metric.ball (F z) δ :=
    convex_ball (F z) δ (hg z hz) (Metric.mem_ball_self hδ) (by linarith [ht.2]) ht.1
      (by ring)
  exact hδO (Metric.mem_thickening_iff.mpr ⟨F z, ⟨z, hz, rfl⟩, hmem⟩)

theorem exists_vector_notMem_span {k N : ℕ} (hkN : k + 2 ≤ N)
    (F : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ 1 F) :
    ∃ e : EuclideanSpace ℝ (Fin N), ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      e ∉ Submodule.span ℝ (Set.range (F z)) := by
  classical
  set γ : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun θ => WithLp.toLp 2 ![Real.cos θ, Real.sin θ] with hγdef
  have hγ : Differentiable ℝ γ := by
    have h1 : Differentiable ℝ (fun θ : ℝ => (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)) := by
      refine differentiable_pi.2 fun i => ?_
      fin_cases i
      · simp
      · simp
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.differentiable.comp h1
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  set g : ℝ × (Fin k → ℝ) → EuclideanSpace ℝ (Fin N) :=
    fun p => ∑ i, p.2 i • F (γ p.1) i with hgdef
  have hg : Differentiable ℝ g := by
    refine Differentiable.fun_sum fun i _ => ?_
    have h1 : Differentiable ℝ (fun p : ℝ × (Fin k → ℝ) => p.2 i) :=
      by fun_prop
    have h2 : Differentiable ℝ (fun p : ℝ × (Fin k → ℝ) => F (γ p.1) i) :=
      by
        have hFi : Differentiable ℝ (fun x => F x i) := differentiable_pi.1 hFd i
        exact hFi.comp (hγ.comp differentiable_fst)
    exact h1.smul h2
  have hdim : Module.finrank ℝ (ℝ × (Fin k → ℝ)) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, finrank_euclideanSpace_fin,
      Module.finrank_self]
    omega
  obtain ⟨e, he⟩ := (hg.dense_compl_range_of_finrank_lt_finrank hdim).nonempty
  refine ⟨e, fun z hz => ?_⟩
  intro hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hz1 : ‖z‖ = 1 := by simpa using hz
  set w : ℂ := ⟨z 0, z 1⟩ with hwdef
  have hw : ‖w‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hz1
    simpa [hwdef, Real.norm_eq_abs, sq_abs] using hz1
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff w).1 hw
  have hzθ : z = γ θ := by
    have hre := Complex.exp_ofReal_mul_I_re θ
    have him := Complex.exp_ofReal_mul_I_im θ
    rw [hθ] at hre him
    ext i
    fin_cases i
    · simp [hγdef, ← hre, hwdef]
    · simp [hγdef, ← him, hwdef]
  apply he
  refine ⟨(θ, c), ?_⟩
  simp only [hgdef]
  rw [← hzθ]
  exact hc

theorem frameExtends_cons {k N : ℕ}
    (hind : ∀ G : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N),
      ContinuousOn G (Metric.sphere 0 1) →
      (∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (G z)) →
      frameExtends G)
    {e : EuclideanSpace ℝ (Fin (N + 1))} (he : e ≠ 0)
    (F : EuclideanSpace ℝ (Fin 2) → Fin (k + 1) → EuclideanSpace ℝ (Fin (N + 1)))
    (hF : ContinuousOn F (Metric.sphere 0 1))
    (hFi : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (F z))
    (he0 : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, F z 0 = e) : frameExtends F := by
  classical
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) := (ℝ ∙ e)ᗮ with hKdef
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (N + 1))) = N + 1) := ⟨by simp⟩
  have hKrank : Module.finrank ℝ K = N := Submodule.finrank_orthogonal_span_singleton he
  let ψ : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    ((stdOrthonormalBasis ℝ K).reindex (finCongr hKrank)).repr
  let L : EuclideanSpace ℝ (Fin (N + 1)) → EuclideanSpace ℝ (Fin N) :=
    fun v => ψ (K.orthogonalProjectionOnto v)
  let ι : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin (N + 1)) :=
    fun w => ((ψ.symm w : K) : EuclideanSpace ℝ (Fin (N + 1)))
  have hKK : Kᗮ = ℝ ∙ e := by
    rw [hKdef]; exact Submodule.orthogonal_orthogonal _
  have hLcont : Continuous L := ψ.continuous.comp K.orthogonalProjectionOnto.continuous
  have hιcont : Continuous ι := continuous_subtype_val.comp ψ.symm.continuous
  have hLsum : ∀ (g : Fin k → ℝ) (v : Fin k → EuclideanSpace ℝ (Fin (N + 1))),
      L (∑ i, g i • v i) = ∑ i, g i • L (v i) := by
    intro g v
    simp [L, map_sum, map_smul]
  have hιsum : ∀ (g : Fin k → ℝ) (v : Fin k → EuclideanSpace ℝ (Fin N)),
      ι (∑ i, g i • v i) = ∑ i, g i • ι (v i) := by
    intro g v
    simp [ι, map_sum, map_smul]
  have hLker : ∀ v, L v = 0 → ∃ a : ℝ, a • e = v := by
    intro v hv
    have h1 : K.orthogonalProjectionOnto v = 0 := by
      simpa [L] using hv
    have h2 : v ∈ Kᗮ := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp h1
    rw [hKK] at h2
    exact Submodule.mem_span_singleton.mp h2
  have hdec : ∀ v, ∃ a : ℝ, v = ι (L v) + a • e := by
    intro v
    have h1 : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
    rw [hKK] at h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    refine ⟨a, ?_⟩
    have : ι (L v) = K.starProjection v := by
      simp only [ι, L, LinearIsometryEquiv.symm_apply_apply, Submodule.starProjection_apply]
    rw [this, ha]
    abel
  have hperp : ∀ w, inner ℝ e (ι w) = 0 := by
    intro w
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (ψ.symm w).2
  have hιinj : ∀ w, ι w = 0 → w = 0 := by
    intro w hw
    have : ψ.symm w = 0 := Subtype.ext hw
    simpa using this
  have hee : inner ℝ e e ≠ 0 := by
    simpa using he
  let G₀ : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N) :=
    fun z i => L (F z i.succ)
  have hG₀c : ContinuousOn G₀ (Metric.sphere 0 1) := by
    refine continuousOn_pi.2 fun i => ?_
    exact hLcont.comp_continuousOn (continuousOn_pi.1 hF i.succ)
  have hG₀i : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      LinearIndependent ℝ (G₀ z) := by
    intro z hz
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hL0 : L (∑ i, g i • F z i.succ) = 0 := by
      rw [hLsum]; exact hg
    obtain ⟨a, ha⟩ := hLker _ hL0
    have hsum : ∑ j, (Fin.cons (-a) g : Fin (k + 1) → ℝ) j • F z j = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [he0 z hz, ← ha]
      simp
    have h0 := (Fintype.linearIndependent_iff.mp (hFi z hz)) _ hsum
    intro i
    simpa using h0 i.succ
  obtain ⟨G', hG'c, hG'i, hG'eq⟩ := hind G₀ hG₀c hG₀i
  let H : ℝ → EuclideanSpace ℝ (Fin 2) → Fin (k + 1) → EuclideanSpace ℝ (Fin (N + 1)) :=
    fun t z => Fin.cons e (fun i => (1 - t) • ι (L (F z i.succ)) + t • F z i.succ)
  have hHc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => H p.1 p.2)
      (Icc 0 1 ×ˢ Metric.sphere 0 1) := by
    refine continuousOn_pi.2 fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [H, Fin.cons_zero]
      exact continuousOn_const
    · simp only [H, Fin.cons_succ]
      have hFs : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => F p.2 i.succ)
          (Icc 0 1 ×ˢ Metric.sphere 0 1) :=
        (continuousOn_pi.1 hF i.succ).comp continuousOn_snd (fun p hp => hp.2)
      refine ContinuousOn.add ?_ ?_
      · exact (continuousOn_const.sub continuousOn_fst).smul
          ((hιcont.comp hLcont).comp_continuousOn hFs)
      · exact continuousOn_fst.smul hFs
  have hHi : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      LinearIndependent ℝ (H t z) := by
    intro t _ z hz
    choose a ha using fun i : Fin k => hdec (F z i.succ)
    have hHs : ∀ i, H t z i.succ = F z i.succ - ((1 - t) * a i) • e := by
      intro i
      simp only [H, Fin.cons_succ]
      have hai := ha i
      generalize ι (L (F z i.succ)) = u at hai ⊢
      rw [hai]
      module
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [hHs] at hg
    have hH0 : H t z 0 = e := by simp [H]
    rw [hH0] at hg
    let g' : Fin (k + 1) → ℝ :=
      Fin.cons (g 0 - ∑ i, g i.succ * ((1 - t) * a i)) (fun i => g i.succ)
    have hsum : ∑ j, g' j • F z j = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [g', Fin.cons_zero, Fin.cons_succ]
      rw [he0 z hz, ← hg]
      simp only [smul_sub, Finset.sum_sub_distrib, sub_smul, Finset.sum_smul, smul_smul]
      abel
    have h0 := (Fintype.linearIndependent_iff.mp (hFi z hz)) _ hsum
    have hs : ∀ i : Fin k, g i.succ = 0 := fun i => by simpa [g'] using h0 i.succ
    intro j
    refine Fin.cases ?_ (fun i => hs i) j
    have := h0 0
    simpa [g', hs] using this
  let Gext : EuclideanSpace ℝ (Fin 2) → Fin (k + 1) → EuclideanSpace ℝ (Fin (N + 1)) :=
    fun z => Fin.cons e (fun i => ι (G' z i))
  have hH0 : frameExtends (H 0) := by
    refine ⟨Gext, ?_, ?_, ?_⟩
    · refine continuousOn_pi.2 fun j => ?_
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Gext, Fin.cons_zero]
        exact continuousOn_const
      · simp only [Gext, Fin.cons_succ]
        exact hιcont.comp_continuousOn (continuousOn_pi.1 hG'c i)
    · intro z hz
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Gext, Fin.cons_zero, Fin.cons_succ] at hg
      rw [← hιsum] at hg
      have hin : inner ℝ e (g 0 • e + ι (∑ i, g i.succ • G' z i)) = 0 := by
        rw [hg]; simp
      rw [inner_add_right, hperp, inner_smul_right, add_zero] at hin
      have hg0 : g 0 = 0 := by
        rcases mul_eq_zero.mp hin with h | h
        · exact h
        · exact absurd h hee
      rw [hg0, zero_smul, zero_add] at hg
      have h1 := (Fintype.linearIndependent_iff.mp (hG'i z hz)) _ (hιinj _ hg)
      intro j
      exact Fin.cases hg0 (fun i => h1 i) j
    · intro z hz
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [Gext, H]
      · simp only [Gext, H, Fin.cons_succ]
        rw [hG'eq z hz]
        simp [G₀]
  refine frameExtends_of_homotopy H hHc hHi hH0 F ?_
  intro z hz
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [H, he0 z hz]
  · simp [H]

theorem exists_frame_extension {k N : ℕ} (hkN : k + 2 ≤ N)
    (F : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N))
    (hF : ContinuousOn F (Metric.sphere 0 1))
    (hind : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (F z)) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin N),
      ContinuousOn G (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, LinearIndependent ℝ (G z)) ∧
      ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, G z = F z := by
  induction k generalizing N with
  | zero =>
    refine ⟨F, ?_, fun z _ => linearIndependent_empty_type, fun z _ => rfl⟩
    have : F = fun _ => (fun i => Fin.elim0 i) := by
      funext z i; exact Fin.elim0 i
    rw [this]
    exact continuousOn_const
  | succ k ih =>
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hk' : k + 2 ≤ N' := by omega
    obtain ⟨F', hF'C, hF'ind⟩ := exists_smooth_frame_near F hF hind
    have hF'c : Continuous F' := hF'C.continuous
    have hF'lin : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        LinearIndependent ℝ (F' z) := by
      intro z hz
      have h := hF'ind 0 ⟨le_refl _, zero_le_one⟩ z hz
      simpa using h
    obtain ⟨e, he⟩ := exists_vector_notMem_span hkN F' hF'C
    obtain ⟨z₀, hz₀⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have he0 : e ≠ 0 := by
      rintro rfl
      exact he z₀ hz₀ (Submodule.zero_mem _)
    let H2 : ℝ → EuclideanSpace ℝ (Fin 2) → Fin (k + 1) → EuclideanSpace ℝ (Fin (N' + 1)) :=
      fun s z => Fin.cons ((1 - s) • F' z 0 + s • e) (Fin.tail (F' z))
    have hH2c : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => H2 p.1 p.2) := by
      refine Continuous.finCons ?_ ?_
      · exact ((continuous_const.sub continuous_fst).smul
          ((continuous_apply 0).comp (hF'c.comp continuous_snd))).add
          (continuous_fst.smul continuous_const)
      · exact continuous_pi fun i => (continuous_apply i.succ).comp (hF'c.comp continuous_snd)
    have hH2ind : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        LinearIndependent ℝ (H2 s z) := by
      intro s hs z hz
      have hlin := hF'lin z hz
      rw [← Fin.cons_self_tail (F' z), linearIndependent_finCons] at hlin
      obtain ⟨htail, ha⟩ := hlin
      refine linearIndependent_finCons.mpr ⟨htail, ?_⟩
      intro hmem
      by_cases hs0 : s = 0
      · subst hs0
        apply ha
        simpa using hmem
      · apply he z hz
        have hsub : Submodule.span ℝ (Set.range (Fin.tail (F' z))) ≤
            Submodule.span ℝ (Set.range (F' z)) :=
          Submodule.span_mono (Set.range_comp_subset_range Fin.succ (F' z))
        have ha' : F' z 0 ∈ Submodule.span ℝ (Set.range (F' z)) :=
          Submodule.subset_span ⟨0, rfl⟩
        have hw := hsub hmem
        have hkey : e = s⁻¹ • (((1 - s) • F' z 0 + s • e) - (1 - s) • F' z 0) := by
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [hkey]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ ha'))
    have hext1 : frameExtends (H2 1) := by
      refine frameExtends_cons (fun G hG hGi => ih hk' G hG hGi) he0 (H2 1) ?_ ?_ ?_
      · exact (hH2c.comp (Continuous.prodMk_right (1 : ℝ))).continuousOn
      · exact hH2ind 1 ⟨zero_le_one, le_refl _⟩
      · intro z _
        simp [H2]
    have hextF' : frameExtends F' := by
      refine frameExtends_of_homotopy (fun t z => H2 (1 - t) z) ?_ ?_ ?_ F' ?_
      · exact ((hH2c.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd))).continuousOn
      · intro t ht z hz
        exact hH2ind (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ z hz
      · simpa using hext1
      · intro z _
        simp [H2]
    have hextF : frameExtends F := by
      refine frameExtends_of_homotopy (fun t z => (1 - t) • F' z + t • F z) ?_ hF'ind ?_ F ?_
      · refine ContinuousOn.add ?_ ?_
        · exact ((continuous_const.sub continuous_fst).smul (hF'c.comp continuous_snd)).continuousOn
        · exact continuous_fst.continuousOn.smul
            (hF.comp continuous_snd.continuousOn (fun p hp => hp.2))
      · simpa using hextF'
      · intro z _
        simp
    exact hextF

def whitneyHalf : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ 0 ≤ y 1}

def whitneyBdry : Set (Fin 2 → ℝ) := whitneyHalf ∩ {y | y 1 = 0 ∨ y 0 ^ 2 + y 1 ^ 2 = 1}

def whitneyBand (r : ℝ) : Set (Fin 2 → ℝ) :=
  {y | y ∈ whitneyHalf ∧ (y 1 ≤ r ∨ (1 - r) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2)}

def blockMat {m ℓ : ℕ} (A : Fin ℓ → Fin m → ℝ) (B : Fin (m - ℓ) → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) < ℓ then A ⟨j, h⟩ i
    else B ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩ i

def frameVec {d r N : ℕ} (E : (Fin d → ℝ) → Fin r → (Fin N → ℝ)) (y : Fin d → ℝ)
    (c : Fin r → ℝ) : Fin N → ℝ :=
  ∑ k, c k • E y k

structure IsWhitneyFrame {m ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hℓm : ℓ + 2 ≤ m)
    (T : (Fin 2 → ℝ) → Fin 2 → (Fin m → ℝ)) (SL : (Fin 2 → ℝ) → Fin ℓ → (Fin m → ℝ))
    (SR : (Fin 2 → ℝ) → Fin (m - ℓ) → (Fin m → ℝ)) : Prop where
  contT : ContinuousOn T whitneyHalf
  indT : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (T y)
  contL : ContinuousOn SL (whitneyHalf ∩ {y | y 1 = 0})
  contR : ContinuousOn SR (whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1})
  indL : ∀ y ∈ whitneyHalf, y 1 = 0 → LinearIndependent ℝ (Fin.cons (T y 1) (SL y))
  headL : ∀ y ∈ whitneyHalf, y 1 = 0 → SL y ⟨0, by omega⟩ = T y 0
  indR : ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 →
    LinearIndependent ℝ (Fin.cons (y 0 • T y 0 + y 1 • T y 1) (SR y))
  headR : ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 →
    SR y ⟨0, by omega⟩ = (-(y 1)) • T y 0 + y 0 • T y 1
  sign : SignType.sign (blockMat (SL ![-1, 0]) (SR ![-1, 0])).det =
    -SignType.sign (blockMat (SL ![1, 0]) (SR ![1, 0])).det
  det_ne : (blockMat (SL ![-1, 0]) (SR ![-1, 0])).det ≠ 0

theorem exists_normalFrame_boundary {m ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hℓm : ℓ + 2 ≤ m)
    {T : (Fin 2 → ℝ) → Fin 2 → (Fin m → ℝ)} {SL : (Fin 2 → ℝ) → Fin ℓ → (Fin m → ℝ)}
    {SR : (Fin 2 → ℝ) → Fin (m - ℓ) → (Fin m → ℝ)} (hW : IsWhitneyFrame hℓ hℓm T SL SR) :
    ∃ Fb : (Fin 2 → ℝ) → Fin (m - 2) → (Fin m → ℝ), ContinuousOn Fb whitneyBdry ∧
      (∀ y ∈ whitneyBdry, LinearIndependent ℝ (Fin.append (T y) (Fb y))) ∧
      (∀ y ∈ whitneyHalf, y 1 = 0 → ∀ (j : Fin (m - 2)) (hj : (j : ℕ) + 1 < ℓ),
        Fb y j = SL y ⟨(j : ℕ) + 1, hj⟩) ∧
      ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 → ∀ j : Fin (m - 2), ℓ ≤ (j : ℕ) + 1 →
        Fb y j = SR y ⟨(j : ℕ) + 2 - ℓ, by have := j.isLt; omega⟩ := by
  classical
  obtain ⟨contT, indT, contL, contR, indL, headL, indR, headR, hsign, hdetne⟩ := hW
  set K1 : Set (Fin 1 → ℝ) := Icc (fun _ => -1) (fun _ => 1) with hK1def
  have hK1 : IsCompact K1 := isCompact_Icc
  have hK1c : Convex ℝ K1 := convex_Icc _ _
  have hpath : ∀ (S : Set (Fin m)) (Q : (Fin 1 → ℝ) → Fin m → Fin m → ℝ), ContinuousOn Q K1 →
      (∀ y ∈ K1, LinearIndependent ℝ (fun j : {j // j ∉ S} => Q y j)) →
      ∀ Q₀ Q₁ : Fin m → Fin m → ℝ, (∀ j, j ∉ S → Q₀ j = Q (fun _ => -1) j) →
      (∀ j, j ∉ S → Q₁ j = Q (fun _ => 1) j) →
      0 < (Matrix.of Q₀).det * (Matrix.of Q₁).det →
      ∃ N : (Fin 1 → ℝ) → Fin m → Fin m → ℝ, ContinuousOn N K1 ∧ N (fun _ => -1) = Q₀ ∧
        N (fun _ => 1) = Q₁ ∧ (∀ y ∈ K1, ∀ j, j ∉ S → N y j = Q y j) ∧
        ∀ y ∈ K1, LinearIndependent ℝ (N y) := by
    intro S Q hQc hQi Q₀ Q₁ hQ₀ hQ₁ hdet
    let Bm : (Fin 1 → ℝ) → Matrix {j // j ∉ S} (Fin m) ℝ := fun y => Matrix.of fun i => Q y i
    let G : (Fin 1 → ℝ) → Matrix {j // j ∉ S} {j // j ∉ S} ℝ := fun y => Bm y * (Bm y).transpose
    let Gi : (Fin 1 → ℝ) → Matrix {j // j ∉ S} {j // j ∉ S} ℝ :=
      fun y => (G y).det⁻¹ • (G y).adjugate
    let Pm : (Fin 1 → ℝ) → Matrix (Fin m) (Fin m) ℝ := fun y => 1 - (Bm y).transpose * (Gi y * Bm y)
    have hBsum : ∀ y (g : {j // j ∉ S} → ℝ), Matrix.mulVec (Bm y).transpose g = ∑ i, g i • Q y i := by
      intro y g
      funext k
      simp [Bm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have hGdet : ∀ y ∈ K1, (G y).det ≠ 0 := by
      intro y hy h0
      obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have h1 : Matrix.mulVec (Bm y).transpose g = 0 := by
        have h2 : (Matrix.mulVec (Bm y).transpose g) ⬝ᵥ (Matrix.mulVec (Bm y).transpose g) = 0 := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
          have : Matrix.mulVec (G y) g = 0 := hg
          simp only [G] at this
          rw [this, zero_dotProduct]
        exact dotProduct_self_eq_zero.1 h2
      rw [hBsum] at h1
      exact hg0 (funext (Fintype.linearIndependent_iff.1 (hQi y hy) g h1))
    have hGGi : ∀ y ∈ K1, G y * Gi y = 1 := by
      intro y hy
      simp only [Gi, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ (hGdet y hy),
        one_smul]
    have hGiG : ∀ y ∈ K1, Gi y * G y = 1 := by
      intro y hy
      simp only [Gi, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ (hGdet y hy),
        one_smul]
    have hBP : ∀ y ∈ K1, Bm y * Pm y = 0 := by
      intro y hy
      simp only [Pm, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      change Bm y - G y * Gi y * Bm y = 0
      rw [hGGi y hy, Matrix.one_mul, sub_self]
    have hPB : ∀ y ∈ K1, Pm y * (Bm y).transpose = 0 := by
      intro y hy
      simp only [Pm, Matrix.sub_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      change (Bm y).transpose - (Bm y).transpose * (Gi y * G y) = 0
      rw [hGiG y hy, Matrix.mul_one, sub_self]
    have hPP : ∀ y ∈ K1, Pm y * Pm y = Pm y := by
      intro y hy
      conv_lhs => rw [show Pm y * Pm y = Pm y - (Bm y).transpose * (Gi y * (Bm y * Pm y)) by
        simp only [Pm, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]]
      rw [hBP y hy, Matrix.mul_zero, Matrix.mul_zero, sub_zero]
    have hQr : Continuous (fun y : K1 => Q y) := hQc.domRestrict
    have hBc : Continuous (fun y : K1 => Bm y) :=
      continuous_pi fun i => continuous_pi fun k =>
        (continuous_apply k).comp ((continuous_apply (i : Fin m)).comp hQr)
    have hGc : Continuous (fun y : K1 => G y) := hBc.matrix_mul hBc.matrix_transpose
    have hGic : Continuous (fun y : K1 => Gi y) :=
      (hGc.matrix_det.inv₀ (fun y => hGdet y y.2)).smul hGc.matrix_adjugate
    have hPmc : Continuous (fun y : K1 => Pm y) :=
      continuous_const.sub (hBc.matrix_transpose.matrix_mul (hGic.matrix_mul hBc))
    let P : (Fin 1 → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
      LinearMap.toContinuousLinearMap (Matrix.toLin' (Pm y))
    have hPapp : ∀ y v, P y v = Matrix.mulVec (Pm y) v := fun y v => rfl
    have hPc : ContinuousOn P K1 := by
      rw [continuousOn_clm_apply]
      intro v
      simp only [hPapp]
      exact continuousOn_iff_continuous_domRestrict.2 (hPmc.matrix_mulVec continuous_const)
    have hPidem : ∀ y ∈ K1, (P y).comp (P y) = P y := by
      intro y hy
      ext1 v
      rw [ContinuousLinearMap.comp_apply, hPapp, hPapp, Matrix.mulVec_mulVec, hPP y hy]
    have hcard : Fintype.card {j // j ∉ S} + Fintype.card {j // j ∈ S} = m := by
      have h1 := Fintype.card_subtype_compl (fun j : Fin m => j ∈ S)
      have h2 := Fintype.card_subtype_le (fun j : Fin m => j ∈ S)
      simp only [Fintype.card_fin] at h1 h2
      omega
    have hPrank : ∀ y ∈ K1, Module.finrank ℝ
        (LinearMap.range (P y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) = Fintype.card {j // j ∈ S} := by
      intro y hy
      have hcoe : (P y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = Matrix.toLin' (Pm y) := rfl
      have hker : LinearMap.ker (Matrix.toLin' (Pm y)) =
          LinearMap.range (Matrix.toLin' (Bm y).transpose) := by
        ext v
        rw [LinearMap.mem_ker, LinearMap.mem_range, Matrix.toLin'_apply]
        constructor
        · intro hv
          refine ⟨Matrix.mulVec (Gi y) (Matrix.mulVec (Bm y) v), ?_⟩
          rw [Matrix.toLin'_apply]
          have h : Matrix.mulVec (Pm y) v = v - Matrix.mulVec
              ((Bm y).transpose) (Matrix.mulVec (Gi y) (Matrix.mulVec (Bm y) v)) := by
            simp only [Pm, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
          rw [hv] at h
          exact (sub_eq_zero.1 h.symm).symm
        · rintro ⟨c, rfl⟩
          rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPB y hy, Matrix.zero_mulVec]
      have hinj : Function.Injective (Matrix.toLin' (Bm y).transpose) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro c hc
        rw [Matrix.toLin'_apply] at hc
        have h1 : Matrix.mulVec (G y) c = 0 := by
          simp only [G]
          rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
        have h2 := congrArg (Matrix.mulVec (Gi y)) h1
        rwa [Matrix.mulVec_mulVec, hGiG y hy, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Pm y))
      rw [hker, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
        Module.finrank_fin_fun] at h
      rw [hcoe]
      omega
    obtain ⟨E, hEc, hE⟩ := exists_frame_of_projections hK1 hK1c P hPc hPidem hPrank
    have hK1mem : ∀ y : Fin 1 → ℝ, y ∈ K1 ↔ y 0 ∈ Icc (-1 : ℝ) 1 := by
      intro y
      simp only [hK1def, mem_Icc, Pi.le_def, Fin.forall_fin_one]
    have hy₀ : (fun _ : Fin 1 => (-1 : ℝ)) ∈ K1 := (hK1mem _).2 ⟨le_rfl, by norm_num⟩
    have hy₁ : (fun _ : Fin 1 => (1 : ℝ)) ∈ K1 := (hK1mem _).2 ⟨by norm_num, le_rfl⟩
    set eS := Fintype.equivFin {j // j ∈ S} with heS
    let Eh : (Fin 1 → ℝ) → Fin m → Fin m → ℝ := fun y j =>
      if h : j ∈ S then E y (eS ⟨j, h⟩) else Q y j
    have hEperp : ∀ y ∈ K1, ∀ k, Matrix.mulVec (Bm y) (E y k) = 0 := by
      intro y hy k
      obtain ⟨v, hv⟩ := LinearMap.mem_range.1 ((hE y hy).2 k)
      rw [← hv]
      change Matrix.mulVec (Bm y) (Matrix.mulVec (Pm y) v) = 0
      rw [Matrix.mulVec_mulVec, hBP y hy, Matrix.zero_mulVec]
    have hEhi : ∀ y ∈ K1, LinearIndependent ℝ (Eh y) := by
      intro y hy
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ S)] at hc
      have h1 : ∑ i : {j // j ∈ S}, c i • Eh y i = ∑ i : {j // j ∈ S}, c i • E y (eS i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Eh, i.2, ↓reduceDIte]
      have h2 : ∑ i : {j // j ∉ S}, c i • Eh y i = ∑ i : {j // j ∉ S}, c i • Q y i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Eh, i.2, ↓reduceDIte]
      rw [h1, h2] at hc
      set u := ∑ i : {j // j ∉ S}, c i • Q y i with hu
      set w := ∑ i : {j // j ∈ S}, c i • E y (eS i) with hw
      have hBw : Matrix.mulVec (Bm y) w = 0 := by
        simp only [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, hEperp y hy, smul_zero,
          Finset.sum_const_zero]
      have hu0 : u = 0 := by
        have huw : u = -w := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hc
        have hBu : Matrix.mulVec (Bm y) u = 0 := by
          rw [huw, Matrix.mulVec_neg, hBw, neg_zero]
        have hu' : u = Matrix.mulVec (Bm y).transpose (fun i => c i) := by rw [hBsum]
        have h3 : u ⬝ᵥ u = 0 := by
          rw [show u ⬝ᵥ u = Matrix.mulVec (Bm y).transpose (fun i => c i) ⬝ᵥ u from by rw [← hu'],
            dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hBu,
            zero_dotProduct]
        exact dotProduct_self_eq_zero.1 h3
      have hcfix : ∀ i : {j // j ∉ S}, c i = 0 :=
        Fintype.linearIndependent_iff.1 (hQi y hy) (fun i => c i) hu0
      have hw0 : w = 0 := by rw [hu0, add_zero] at hc; exact hc
      have hcfree : ∀ i : {j // j ∈ S}, c i = 0 :=
        Fintype.linearIndependent_iff.1 ((hE y hy).1.comp eS eS.injective) (fun i => c i) hw0
      intro j
      by_cases hj : j ∈ S
      · exact hcfree ⟨j, hj⟩
      · exact hcfix ⟨j, hj⟩
    have hEhc : ContinuousOn Eh K1 := by
      refine continuousOn_pi.2 fun j => ?_
      by_cases hj : j ∈ S
      · simp only [Eh, hj, ↓reduceDIte]
        exact continuousOn_pi.1 hEc _
      · simp only [Eh, hj, ↓reduceDIte]
        exact continuousOn_pi.1 hQc j
    let dE : (Fin 1 → ℝ) → ℝ := fun y => (Matrix.of (Eh y)).det
    have hdEc : ContinuousOn dE K1 :=
      continuousOn_iff_continuous_domRestrict.2
        (Continuous.matrix_det (A := fun y : K1 => Matrix.of (Eh y)) hEhc.domRestrict)
    have hdE0 : ∀ y ∈ K1, dE y ≠ 0 := by
      intro y hy
      have hu : IsUnit (Matrix.of (Eh y)) := Matrix.linearIndependent_rows_iff_isUnit.1 (hEhi y hy)
      exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
    have hdEpos : 0 < dE (fun _ => -1) * dE (fun _ => 1) := by
      let f : ℝ → ℝ := fun s => dE (fun _ => s)
      have hmap : ∀ s ∈ Icc (-1 : ℝ) 1, (fun _ : Fin 1 => s) ∈ K1 := fun s hs => (hK1mem _).2 hs
      have hf : ContinuousOn f (Icc (-1) 1) :=
        hdEc.comp (continuous_pi fun _ => continuous_id).continuousOn hmap
      have hf0 : ∀ s ∈ Icc (-1 : ℝ) 1, f s ≠ 0 := fun s hs => hdE0 _ (hmap s hs)
      rcases lt_or_gt_of_ne (hf0 (-1) ⟨le_rfl, by norm_num⟩) with h1 | h1 <;>
        rcases lt_or_gt_of_ne (hf0 1 ⟨by norm_num, le_rfl⟩) with h2 | h2
      · exact mul_pos_of_neg_of_neg h1 h2
      · exfalso
        obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc (by norm_num) hf ⟨h1.le, h2.le⟩
        exact hf0 s hs hs0
      · exfalso
        obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (by norm_num) hf ⟨h2.le, h1.le⟩
        exact hf0 s hs hs0
      · exact mul_pos h1 h2
    set E₀ : Matrix (Fin m) (Fin m) ℝ := Matrix.of (Eh (fun _ => -1)) with hE₀def
    set E₁ : Matrix (Fin m) (Fin m) ℝ := Matrix.of (Eh (fun _ => 1)) with hE₁def
    have hE₀u : IsUnit E₀.det := isUnit_iff_ne_zero.2 (hdE0 _ hy₀)
    have hE₁u : IsUnit E₁.det := isUnit_iff_ne_zero.2 (hdE0 _ hy₁)
    set W₀ : Matrix (Fin m) (Fin m) ℝ := Matrix.of Q₀ * E₀⁻¹ with hW₀def
    set W₁ : Matrix (Fin m) (Fin m) ℝ := Matrix.of Q₁ * E₁⁻¹ with hW₁def
    have hW₀E : W₀ * E₀ = Matrix.of Q₀ := by
      rw [hW₀def, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE₀u, Matrix.mul_one]
    have hW₁E : W₁ * E₁ = Matrix.of Q₁ := by
      rw [hW₁def, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE₁u, Matrix.mul_one]
    have hW₀fix : ∀ i, i ∉ S → ∀ j, W₀ i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
      intro i hi j
      have hrow : ∀ k, Matrix.of Q₀ i k = E₀ i k := by
        intro k
        simp [hE₀def, Eh, hi, hQ₀ i hi]
      have h : W₀ i j = (E₀ * E₀⁻¹) i j := by
        simp only [hW₀def, Matrix.mul_apply, hrow]
      rw [h, Matrix.mul_nonsing_inv _ hE₀u]
    have hW₁fix : ∀ i, i ∉ S → ∀ j, W₁ i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
      intro i hi j
      have hrow : ∀ k, Matrix.of Q₁ i k = E₁ i k := by
        intro k
        simp [hE₁def, Eh, hi, hQ₁ i hi]
      have h : W₁ i j = (E₁ * E₁⁻¹) i j := by
        simp only [hW₁def, Matrix.mul_apply, hrow]
      rw [h, Matrix.mul_nonsing_inv _ hE₁u]
    have hdetW : ∀ W : Matrix (Fin m) (Fin m) ℝ,
        (∀ i, i ∉ S → ∀ j, W i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j) →
        W.det = (W.toSquareBlockProp (fun j => j ∈ S)).det := by
      intro W hW
      rw [Matrix.twoBlockTriangular_det W (fun j => j ∈ S)]
      · have h1 : W.toSquareBlockProp (fun j => ¬ j ∈ S) = 1 := by
          ext i j
          rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, hW i i.2, Matrix.one_apply,
            Matrix.one_apply]
          simp [Subtype.ext_iff]
        rw [h1, Matrix.det_one, mul_one]
      · intro i hi j hj
        rw [hW i hi, Matrix.one_apply_ne]
        rintro rfl
        exact hi hj
    set Y₀ := W₀.toSquareBlockProp (fun j => j ∈ S) with hY₀def
    set Y₁ := W₁.toSquareBlockProp (fun j => j ∈ S) with hY₁def
    have hY : 0 < Y₀.det * Y₁.det := by
      rw [← hdetW W₀ hW₀fix, ← hdetW W₁ hW₁fix]
      have h : W₀.det * W₁.det =
          ((Matrix.of Q₀).det * (Matrix.of Q₁).det) * (dE (fun _ => -1) * dE (fun _ => 1))⁻¹ := by
        simp only [hW₀def, hW₁def, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          dE, hE₀def, hE₁def, mul_inv]
        ring
      rw [h]
      exact mul_pos hdet (inv_pos.2 hdEpos)
    have hjoinpos : ∀ Y₀ Y₁ : Matrix {j // j ∈ S} {j // j ∈ S} ℝ, 0 < Y₀.det → 0 < Y₁.det →
        ∃ Z : ℝ → Matrix {j // j ∈ S} {j // j ∈ S} ℝ, Continuous Z ∧ Z 0 = Y₀ ∧ Z 1 = Y₁ ∧
          ∀ t, 0 < (Z t).det := by
      intro Y₀ Y₁ h₀ h₁
      have hJ := joinedIn_det_pos (A := Y₀.submatrix eS.symm eS.symm)
        (B := Y₁.submatrix eS.symm eS.symm) (by rwa [Matrix.det_submatrix_equiv_self])
        (by rwa [Matrix.det_submatrix_equiv_self])
      refine ⟨fun t => (hJ.somePath.extend t).submatrix eS eS,
        hJ.somePath.continuous_extend.matrix_submatrix _ _, ?_, ?_, fun t => ?_⟩
      · simp only [Path.extend_zero, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
          Matrix.submatrix_id_id]
      · simp only [Path.extend_one, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
          Matrix.submatrix_id_id]
      · rw [Matrix.det_submatrix_equiv_self]
        exact hJ.somePath_mem _
    have hjoin : ∀ Y₀ Y₁ : Matrix {j // j ∈ S} {j // j ∈ S} ℝ, 0 < Y₀.det * Y₁.det →
        ∃ Z : ℝ → Matrix {j // j ∈ S} {j // j ∈ S} ℝ, Continuous Z ∧ Z 0 = Y₀ ∧ Z 1 = Y₁ ∧
          ∀ t, (Z t).det ≠ 0 := by
      intro Y₀ Y₁ h
      have hne : Y₀.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
      rcases lt_or_gt_of_ne hne with h0 | h0
      · have h1 : Y₁.det < 0 := by
          by_contra hc
          have hc' := not_lt.1 hc
          nlinarith
        obtain ⟨i₀⟩ : Nonempty {j // j ∈ S} := by
          by_contra hn
          rw [not_nonempty_iff] at hn
          rw [Matrix.det_isEmpty] at h0
          norm_num at h0
        let D : Matrix {j // j ∈ S} {j // j ∈ S} ℝ :=
          Matrix.diagonal fun i => if i = i₀ then -1 else 1
        have hDD : D * D = 1 := by
          simp only [D, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext i
          split_ifs <;> norm_num
        have hDdet : D.det = -1 := by
          simp [D, Matrix.det_diagonal, Finset.prod_ite_eq']
        obtain ⟨Z, hZc, hZ0, hZ1, hZd⟩ := hjoinpos (D * Y₀) (D * Y₁)
          (by rw [Matrix.det_mul, hDdet]; linarith) (by rw [Matrix.det_mul, hDdet]; linarith)
        refine ⟨fun t => D * Z t, continuous_const.matrix_mul hZc, ?_, ?_, fun t => ?_⟩
        · simp only [hZ0, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
        · simp only [hZ1, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
        · rw [Matrix.det_mul, hDdet]
          have := hZd t
          intro h'
          linarith
      · have h1 : 0 < Y₁.det := by
          by_contra hc
          have hc' := not_lt.1 hc
          nlinarith
        obtain ⟨Z, hZc, hZ0, hZ1, hZd⟩ := hjoinpos Y₀ Y₁ h0 h1
        exact ⟨Z, hZc, hZ0, hZ1, fun t => (hZd t).ne'⟩
    obtain ⟨Z, hZc, hZ0, hZ1, hZd⟩ := hjoin Y₀ Y₁ hY
    let W : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => Matrix.of fun i j =>
      if hi : i ∈ S then (if hj : j ∈ S then Z t ⟨i, hi⟩ ⟨j, hj⟩ else (1 - t) * W₀ i j + t * W₁ i j)
      else (1 : Matrix (Fin m) (Fin m) ℝ) i j
    have hWfix : ∀ t, ∀ i, i ∉ S → ∀ j, W t i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
      intro t i hi j
      simp [W, hi]
    have hWblock : ∀ t, (W t).toSquareBlockProp (fun j => j ∈ S) = Z t := by
      intro t
      ext i j
      simp [W, Matrix.toSquareBlockProp_def]
    have hWdet : ∀ t, (W t).det ≠ 0 := fun t => by
      rw [hdetW _ (hWfix t), hWblock]
      exact hZd t
    have hW0 : W 0 = W₀ := by
      ext i j
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · simp [W, hi, hj, hZ0, hY₀def, Matrix.toSquareBlockProp_def]
        · simp [W, hi, hj]
      · simp [W, hi, hW₀fix i hi j]
    have hW1 : W 1 = W₁ := by
      ext i j
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · simp [W, hi, hj, hZ1, hY₁def, Matrix.toSquareBlockProp_def]
        · simp [W, hi, hj]
      · simp [W, hi, hW₁fix i hi j]
    have hWc : Continuous W := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · simp only [W, Matrix.of_apply, hi, hj, ↓reduceDIte]
          exact (continuous_apply _).comp ((continuous_apply _).comp hZc)
        · simp only [W, Matrix.of_apply, hi, hj, ↓reduceDIte]
          fun_prop
      · simp only [W, Matrix.of_apply, hi, ↓reduceDIte]
        exact continuous_const
    let tp : (Fin 1 → ℝ) → ℝ := fun y => (y 0 + 1) / 2
    have htp : Continuous tp := by fun_prop
    refine ⟨fun y i j => (W (tp y) * Matrix.of (Eh y)) i j, ?_, ?_, ?_, ?_, ?_⟩
    · refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ ?_
      · exact (((continuous_apply k).comp ((continuous_apply i).comp hWc)).comp htp).continuousOn
      · exact continuousOn_pi.1 (continuousOn_pi.1 hEhc k) j
    · funext i j
      have h : tp (fun _ => -1) = 0 := by simp [tp]
      simp only [h, hW0]
      rw [← hE₀def, hW₀E]
      rfl
    · funext i j
      have h : tp (fun _ => 1) = 1 := by norm_num [tp]
      simp only [h, hW1]
      rw [← hE₁def, hW₁E]
      rfl
    · intro y hy j hj
      funext k
      change (W (tp y) * Matrix.of (Eh y)) j k = Q y j k
      have h : (W (tp y) * Matrix.of (Eh y)) j k = ((1 : Matrix (Fin m) (Fin m) ℝ) * Matrix.of (Eh y)) j k := by
        simp only [Matrix.mul_apply, hWfix _ j hj]
      rw [h, Matrix.one_mul]
      simp [Eh, hj]
    · intro y hy
      have hd : (W (tp y) * Matrix.of (Eh y)).det ≠ 0 := by
        rw [Matrix.det_mul]
        exact mul_ne_zero (hWdet _) (hdE0 y hy)
      exact Matrix.linearIndependent_rows_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
  have hK1mem : ∀ y : Fin 1 → ℝ, y ∈ K1 ↔ y 0 ∈ Icc (-1 : ℝ) 1 := by
    intro y
    simp only [hK1def, mem_Icc, Pi.le_def, Fin.forall_fin_one]
  obtain ⟨cm, hcm⟩ : ∃ c : Fin 2 → ℝ, c = ![-1, 0] := ⟨_, rfl⟩
  obtain ⟨cp, hcp⟩ : ∃ c : Fin 2 → ℝ, c = ![1, 0] := ⟨_, rfl⟩
  rw [← hcm, ← hcp] at hsign
  rw [← hcm] at hdetne
  have hcm0 : cm 0 = -1 := by simp [hcm]
  have hcm1 : cm 1 = 0 := by simp [hcm]
  have hcp0 : cp 0 = 1 := by simp [hcp]
  have hcp1 : cp 1 = 0 := by simp [hcp]
  let pD : (Fin 1 → ℝ) → Fin 2 → ℝ := fun y => ![y 0, 0]
  let pC : (Fin 1 → ℝ) → Fin 2 → ℝ := fun y => ![y 0, Real.sqrt (1 - y 0 ^ 2)]
  have hpDc : Continuous pD := by fun_prop
  have hpCc : Continuous pC := by fun_prop
  have hsq : ∀ y ∈ K1, y 0 ^ 2 ≤ 1 := by
    intro y hy
    rw [hK1mem] at hy
    rw [sq_le_one_iff_abs_le_one, abs_le]
    exact hy
  have hpDK : ∀ y ∈ K1, pD y ∈ whitneyHalf ∧ pD y 1 = 0 := by
    intro y hy
    have := hsq y hy
    have e0 : pD y 0 = y 0 := by simp [pD]
    have e1 : pD y 1 = 0 := by simp [pD]
    refine ⟨⟨?_, ?_⟩, e1⟩
    · rw [e0, e1]; linarith
    · rw [e1]
  have hpCK : ∀ y ∈ K1, pC y ∈ whitneyHalf ∧ pC y 0 ^ 2 + pC y 1 ^ 2 = 1 := by
    intro y hy
    have h1 := hsq y hy
    have h2 : pC y 1 ^ 2 = 1 - y 0 ^ 2 := by
      simp only [pC, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact Real.sq_sqrt (by linarith)
    have h3 : pC y 0 = y 0 := by simp [pC]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h2, h3]; linarith
    · simp only [pC, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact Real.sqrt_nonneg _
    · rw [h2, h3]; ring
  have hpDm : pD (fun _ => -1) = cm := by
    funext i; fin_cases i <;> simp [pD, hcm]
  have hpDp : pD (fun _ => 1) = cp := by
    funext i; fin_cases i <;> simp [pD, hcp]
  have hpCm : pC (fun _ => -1) = cm := by
    funext i; fin_cases i <;> simp [pC, hcm]
  have hpCp : pC (fun _ => 1) = cp := by
    funext i; fin_cases i <;> simp [pC, hcp]
  let R : (Fin 2 → ℝ) → Fin m → Fin m → ℝ := fun c j =>
    if h : (j : ℕ) < ℓ then SL c ⟨j, h⟩ else SR c ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩
  have hR : ∀ c, (Matrix.of (R c)).det = (blockMat (SL c) (SR c)).det := by
    intro c
    rw [← Matrix.det_transpose (blockMat (SL c) (SR c))]
    congr 1
    ext i j
    by_cases h : (i : ℕ) < ℓ <;> simp [R, blockMat, Matrix.transpose_apply, h]
  have hdetrow : ∀ (R₀ R' : Fin m → Fin m → ℝ) (i₀ : Fin m) (a : ℝ),
      (∀ i, i ≠ i₀ → R' i = R₀ i) → R' i₀ = a • R₀ i₀ →
      (Matrix.of R').det = a * (Matrix.of R₀).det := by
    intro R₀ R' i₀ a h1 h2
    have h : Matrix.of R' = (Matrix.of R₀).updateRow i₀ (a • (Matrix.of R₀) i₀) := by
      ext i k
      rw [Matrix.updateRow_apply]
      by_cases h : i = i₀
      · subst h
        simp [h2]
      · simp [h, h1 i h]
    rw [h, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  have hprod : 0 < -(blockMat (SL cm) (SR cm)).det * (blockMat (SL cp) (SR cp)).det := by
    set a := (blockMat (SL cm) (SR cm)).det
    set b := (blockMat (SL cp) (SR cp)).det
    rcases lt_or_gt_of_ne hdetne with ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [sign_neg ha, sign_neg hb] at hsign; exact absurd hsign (by decide)
    · rw [sign_neg ha, hb, sign_zero] at hsign; exact absurd hsign (by decide)
    · nlinarith
    · nlinarith
    · rw [sign_pos ha, hb, sign_zero] at hsign; exact absurd hsign (by decide)
    · rw [sign_pos ha, sign_pos hb] at hsign; exact absurd hsign (by decide)
  have hcmH : cm ∈ whitneyHalf := by
    refine ⟨?_, ?_⟩ <;> simp [hcm0, hcm1]
  have hcpH : cp ∈ whitneyHalf := by
    refine ⟨?_, ?_⟩ <;> simp [hcp0, hcp1]
  let SD : Set (Fin m) := {j | ℓ < (j : ℕ)}
  let QD : (Fin 1 → ℝ) → Fin m → Fin m → ℝ := fun y j =>
    if h : (j : ℕ) < ℓ then SL (pD y) ⟨j, h⟩ else if (j : ℕ) = ℓ then T (pD y) 1 else 0
  let QDe : (Fin 2 → ℝ) → Fin m → Fin m → ℝ := fun c j =>
    if h : (j : ℕ) < ℓ then SL c ⟨j, h⟩ else if (j : ℕ) = ℓ then T c 1
      else SR c ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩
  have hQDc : ContinuousOn QD K1 := by
    refine continuousOn_pi.2 fun j => ?_
    by_cases h : (j : ℕ) < ℓ
    · simp only [QD, h, ↓reduceDIte]
      exact continuousOn_pi.1 (contL.comp hpDc.continuousOn
        (fun y hy => ⟨(hpDK y hy).1, (hpDK y hy).2⟩)) ⟨j, h⟩
    · by_cases h' : (j : ℕ) = ℓ
      · simp only [QD, h, ↓reduceDIte]
        simp only [h', ↓reduceIte]
        exact continuousOn_pi.1 (contT.comp hpDc.continuousOn (fun y hy => (hpDK y hy).1)) 1
      · simp only [QD, h, ↓reduceDIte]
        simp only [h', ↓reduceIte]
        exact continuousOn_const
  have hQDi : ∀ y ∈ K1, LinearIndependent ℝ (fun j : {j // j ∉ SD} => QD y j) := by
    intro y hy
    have hp := hpDK y hy
    have hind := indL (pD y) hp.1 hp.2
    let φ : {j // j ∉ SD} → Fin (ℓ + 1) := fun j =>
      if h : ((j : Fin m) : ℕ) < ℓ then Fin.succ ⟨j, h⟩ else 0
    have hφ : Function.Injective φ := by
      intro a b hab
      have ha : ¬ ℓ < ((a : Fin m) : ℕ) := a.2
      have hb : ¬ ℓ < ((b : Fin m) : ℕ) := b.2
      simp only [φ] at hab
      apply Subtype.ext
      apply Fin.ext
      split_ifs at hab with h1 h2 h2
      · have := congrArg Fin.val hab
        simp at this
        omega
      · exact absurd hab (Fin.succ_ne_zero _)
      · exact absurd hab.symm (Fin.succ_ne_zero _)
      · omega
    have heq : (fun j : {j // j ∉ SD} => QD y j) =
        (Fin.cons (T (pD y) 1) (SL (pD y)) : Fin (ℓ + 1) → Fin m → ℝ) ∘ φ := by
      funext j
      have hj : ¬ ℓ < ((j : Fin m) : ℕ) := j.2
      by_cases h : ((j : Fin m) : ℕ) < ℓ
      · simp only [QD, φ, h, ↓reduceDIte, Function.comp_apply, Fin.cons_succ]
      · have h' : ((j : Fin m) : ℕ) = ℓ := by omega
        simp only [QD, φ, h, ↓reduceDIte, Function.comp_apply, Fin.cons_zero]
        simp only [h', ↓reduceIte]
    rw [heq]
    exact hind.comp φ hφ
  have hQD0 : ∀ j, j ∉ SD → QDe cm j = QD (fun _ => -1) j := by
    intro j hj
    have hj' : ¬ ℓ < (j : ℕ) := hj
    by_cases h : (j : ℕ) < ℓ
    · simp [QDe, QD, h, hpDm]
    · have h' : (j : ℕ) = ℓ := by omega
      simp [QDe, QD, h', hpDm]
  have hQD1 : ∀ j, j ∉ SD → QDe cp j = QD (fun _ => 1) j := by
    intro j hj
    have hj' : ¬ ℓ < (j : ℕ) := hj
    by_cases h : (j : ℕ) < ℓ
    · simp [QDe, QD, h, hpDp]
    · have h' : (j : ℕ) = ℓ := by omega
      simp [QDe, QD, h', hpDp]
  have hQDedet : ∀ c : Fin 2 → ℝ, c ∈ whitneyHalf → c 1 = 0 → c 0 ^ 2 = 1 →
      (Matrix.of (QDe c)).det = c 0 * (blockMat (SL c) (SR c)).det := by
    intro c hc hc1 hc0
    rw [← hR]
    refine hdetrow (R c) (QDe c) ⟨ℓ, by omega⟩ (c 0) (fun i hi => ?_) ?_
    · have hi' : (i : ℕ) ≠ ℓ := fun h => hi (Fin.ext h)
      by_cases h : (i : ℕ) < ℓ
      · simp [QDe, R, h]
      · simp [QDe, R, h, hi']
    · have hh := headR c hc (by rw [hc1]; linarith)
      have hl : ¬ ℓ < ℓ := lt_irrefl ℓ
      simp only [QDe, R, hl, ↓reduceDIte, ↓reduceIte, Nat.sub_self]
      rw [hh, hc1]
      funext k
      simp only [neg_zero, zero_smul, zero_add, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← sq, hc0, one_mul]
  have hDdet : 0 < (Matrix.of (QDe cm)).det * (Matrix.of (QDe cp)).det := by
    rw [hQDedet cm hcmH hcm1 (by rw [hcm0]; norm_num),
      hQDedet cp hcpH hcp1 (by rw [hcp0]; norm_num), hcm0, hcp0]
    linarith
  obtain ⟨ND, hNDc, hND0, hND1, hNDfix, hNDi⟩ :=
    hpath SD QD hQDc hQDi (QDe cm) (QDe cp) hQD0 hQD1 hDdet
  let SC : Set (Fin m) := {j | 0 < (j : ℕ) ∧ (j : ℕ) < ℓ}
  let ρ : (Fin 2 → ℝ) → Fin m → ℝ := fun c => c 0 • T c 0 + c 1 • T c 1
  let QC : (Fin 1 → ℝ) → Fin m → Fin m → ℝ := fun y j =>
    if (j : ℕ) = 0 then ρ (pC y)
      else if h : ℓ ≤ (j : ℕ) then SR (pC y) ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩ else 0
  let QCe : (Fin 2 → ℝ) → Fin m → Fin m → ℝ := fun c j =>
    if (j : ℕ) = 0 then ρ c
      else if h : ℓ ≤ (j : ℕ) then SR c ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩
        else SL c ⟨j, by omega⟩
  have hTC : ContinuousOn (fun y => T (pC y)) K1 :=
    contT.comp hpCc.continuousOn (fun y hy => (hpCK y hy).1)
  have hQCc : ContinuousOn QC K1 := by
    refine continuousOn_pi.2 fun j => ?_
    by_cases h : (j : ℕ) = 0
    · simp only [QC, h, ↓reduceIte, ρ]
      exact ((((continuous_apply 0).comp hpCc).continuousOn).smul (continuousOn_pi.1 hTC 0)).add
        ((((continuous_apply 1).comp hpCc).continuousOn).smul (continuousOn_pi.1 hTC 1))
    · by_cases h' : ℓ ≤ (j : ℕ)
      · simp only [QC, h, h', ↓reduceDIte, ↓reduceIte]
        exact continuousOn_pi.1 (contR.comp hpCc.continuousOn
          (fun y hy => ⟨(hpCK y hy).1, (hpCK y hy).2⟩)) _
      · simp only [QC, h, h', ↓reduceDIte, ↓reduceIte]
        exact continuousOn_const
  have hQCi : ∀ y ∈ K1, LinearIndependent ℝ (fun j : {j // j ∉ SC} => QC y j) := by
    intro y hy
    have hp := hpCK y hy
    have hind := indR (pC y) hp.1 hp.2
    let φ : {j // j ∉ SC} → Fin (m - ℓ + 1) := fun j =>
      if ((j : Fin m) : ℕ) = 0 then 0
        else Fin.succ ⟨((j : Fin m) : ℕ) - ℓ, by have := (j : Fin m).isLt; omega⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      have ha : ¬ (0 < ((a : Fin m) : ℕ) ∧ ((a : Fin m) : ℕ) < ℓ) := a.2
      have hb : ¬ (0 < ((b : Fin m) : ℕ) ∧ ((b : Fin m) : ℕ) < ℓ) := b.2
      simp only [φ] at hab
      apply Subtype.ext
      apply Fin.ext
      split_ifs at hab with h1 h2 h2
      · omega
      · exact absurd hab.symm (Fin.succ_ne_zero _)
      · exact absurd hab (Fin.succ_ne_zero _)
      · have := congrArg Fin.val hab
        simp at this
        omega
    have heq : (fun j : {j // j ∉ SC} => QC y j) =
        (Fin.cons (pC y 0 • T (pC y) 0 + pC y 1 • T (pC y) 1) (SR (pC y)) :
          Fin (m - ℓ + 1) → Fin m → ℝ) ∘ φ := by
      funext j
      have hj : ¬ (0 < ((j : Fin m) : ℕ) ∧ ((j : Fin m) : ℕ) < ℓ) := j.2
      by_cases h : ((j : Fin m) : ℕ) = 0
      · simp only [QC, φ, h, ↓reduceIte, ρ, Function.comp_apply, Fin.cons_zero]
      · have h' : ℓ ≤ ((j : Fin m) : ℕ) := by omega
        simp only [QC, φ, h, h', ↓reduceIte, ↓reduceDIte, Function.comp_apply, Fin.cons_succ]
    rw [heq]
    exact hind.comp φ hφ
  have hQC0 : ∀ j, j ∉ SC → QCe cm j = QC (fun _ => -1) j := by
    intro j hj
    have hj' : ¬ (0 < (j : ℕ) ∧ (j : ℕ) < ℓ) := hj
    by_cases h : (j : ℕ) = 0
    · simp [QCe, QC, h, hpCm]
    · have h' : ℓ ≤ (j : ℕ) := by omega
      simp [QCe, QC, h, h', hpCm]
  have hQC1 : ∀ j, j ∉ SC → QCe cp j = QC (fun _ => 1) j := by
    intro j hj
    have hj' : ¬ (0 < (j : ℕ) ∧ (j : ℕ) < ℓ) := hj
    by_cases h : (j : ℕ) = 0
    · simp [QCe, QC, h, hpCp]
    · have h' : ℓ ≤ (j : ℕ) := by omega
      simp [QCe, QC, h, h', hpCp]
  have hQCedet : ∀ c : Fin 2 → ℝ, c ∈ whitneyHalf → c 1 = 0 →
      (Matrix.of (QCe c)).det = c 0 * (blockMat (SL c) (SR c)).det := by
    intro c hc hc1
    rw [← hR]
    refine hdetrow (R c) (QCe c) ⟨0, by omega⟩ (c 0) (fun i hi => ?_) ?_
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      by_cases h : ℓ ≤ (i : ℕ)
      · have h2 : ¬ (i : ℕ) < ℓ := by omega
        simp [QCe, R, h, hi', h2]
      · have h2 : (i : ℕ) < ℓ := by omega
        simp [QCe, R, h, hi', h2]
    · have hh := headL c hc hc1
      have hl : (0 : ℕ) < ℓ := by omega
      simp only [QCe, R, hl, ↓reduceDIte, ↓reduceIte, ρ]
      rw [hh, hc1, zero_smul, add_zero]
  have hCdet : 0 < (Matrix.of (QCe cm)).det * (Matrix.of (QCe cp)).det := by
    rw [hQCedet cm hcmH hcm1, hQCedet cp hcpH hcp1, hcm0, hcp0]
    linarith
  obtain ⟨NC, hNCc, hNC0, hNC1, hNCfix, hNCi⟩ :=
    hpath SC QC hQCc hQCi (QCe cm) (QCe cp) hQC0 hQC1 hCdet
  let yt : (Fin 2 → ℝ) → Fin 1 → ℝ := fun y _ => y 0
  have hyt : Continuous yt := by fun_prop
  have hytK : ∀ y ∈ whitneyHalf, yt y ∈ K1 := by
    intro y hy
    rw [hK1mem]
    have h1 : y 0 ^ 2 ≤ 1 := by nlinarith [hy.1, sq_nonneg (y 1)]
    rw [sq_le_one_iff_abs_le_one, abs_le] at h1
    exact h1
  have hcorner : ∀ y ∈ whitneyHalf, y 1 = 0 → y 0 ^ 2 + y 1 ^ 2 = 1 →
      (y = cm ∧ yt y = fun _ => -1) ∨ (y = cp ∧ yt y = fun _ => 1) := by
    intro y hy hy1 hyc
    rw [hy1] at hyc
    have h : (y 0 - 1) * (y 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · right
      have h0 : y 0 = 1 := by linarith
      refine ⟨?_, funext fun _ => h0⟩
      funext i; fin_cases i
      · simp [hcp, h0]
      · simp [hcp, hy1]
    · left
      have h0 : y 0 = -1 := by linarith
      refine ⟨?_, funext fun _ => h0⟩
      funext i; fin_cases i
      · simp [hcm, h0]
      · simp [hcm, hy1]
  have hcornerL : ∀ y ∈ whitneyHalf, y 1 = 0 → y 0 ^ 2 + y 1 ^ 2 = 1 →
      ∀ (j : Fin (m - 2)) (h : (j : ℕ) + 1 < ℓ),
        SL y ⟨(j : ℕ) + 1, h⟩ = NC (yt y) ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ := by
    intro y hy hy1 hyc j h
    have h1 : ¬ ((j : ℕ) + 1 = 0) := by omega
    have h2 : ¬ (ℓ ≤ (j : ℕ) + 1) := by omega
    rcases hcorner y hy hy1 hyc with ⟨rfl, hy'⟩ | ⟨rfl, hy'⟩
    · rw [hy', hNC0]
      simp [QCe, h2]
    · rw [hy', hNC1]
      simp [QCe, h2]
  have hcornerR : ∀ y ∈ whitneyHalf, y 1 = 0 → y 0 ^ 2 + y 1 ^ 2 = 1 →
      ∀ (j : Fin (m - 2)), ℓ ≤ (j : ℕ) + 1 →
        ND (yt y) ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩ =
          SR y ⟨(j : ℕ) + 2 - ℓ, by have := j.isLt; omega⟩ := by
    intro y hy hy1 hyc j h
    have h1 : ¬ ((j : ℕ) + 2 < ℓ) := by omega
    have h2 : ¬ ((j : ℕ) + 2 = ℓ) := by omega
    rcases hcorner y hy hy1 hyc with ⟨rfl, hy'⟩ | ⟨rfl, hy'⟩
    · rw [hy', hND0]
      simp [QDe, h1, h2]
    · rw [hy', hND1]
      simp [QDe, h1, h2]
  set Fb : (Fin 2 → ℝ) → Fin (m - 2) → (Fin m → ℝ) := fun y j =>
    if y 1 = 0 then
      (if h : (j : ℕ) + 1 < ℓ then SL y ⟨(j : ℕ) + 1, h⟩
        else ND (yt y) ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩)
    else (if h : (j : ℕ) + 1 < ℓ then NC (yt y) ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
        else SR y ⟨(j : ℕ) + 2 - ℓ, by have := j.isLt; omega⟩) with hFb
  have hHc : IsClosed whitneyHalf := by
    have e : whitneyHalf = {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩ {y | 0 ≤ y 1} := rfl
    rw [e]
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const (by fun_prop))
  refine ⟨Fb, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_pi.2 fun j => ?_
    have hbd : whitneyBdry = (whitneyHalf ∩ {y | y 1 = 0}) ∪
        (whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}) := by
      ext y
      constructor
      · rintro ⟨hH, h | h⟩
        exacts [Or.inl ⟨hH, h⟩, Or.inr ⟨hH, h⟩]
      · rintro (⟨hH, h⟩ | ⟨hH, h⟩)
        exacts [⟨hH, Or.inl h⟩, ⟨hH, Or.inr h⟩]
    rw [hbd]
    refine ContinuousOn.union_of_isClosed ?_ ?_
      (hHc.inter (isClosed_eq (continuous_apply 1) continuous_const))
      (hHc.inter (isClosed_eq (by fun_prop) continuous_const))
    · have hEq : EqOn (fun y => Fb y j) (fun y => if h : (j : ℕ) + 1 < ℓ then SL y ⟨(j : ℕ) + 1, h⟩
          else ND (yt y) ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩)
          (whitneyHalf ∩ {y | y 1 = 0}) := by
        intro y hy
        have hy1 : y 1 = 0 := hy.2
        simp only [hFb, hy1, ↓reduceIte]
      refine ContinuousOn.congr ?_ hEq
      by_cases h : (j : ℕ) + 1 < ℓ
      · simp only [h, ↓reduceDIte]
        exact continuousOn_pi.1 contL _
      · simp only [h, ↓reduceDIte]
        exact (continuousOn_pi.1 hNDc _).comp hyt.continuousOn (fun y hy => hytK y hy.1)
    · have hEq : EqOn (fun y => Fb y j) (fun y => if h : (j : ℕ) + 1 < ℓ then
          NC (yt y) ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
          else SR y ⟨(j : ℕ) + 2 - ℓ, by have := j.isLt; omega⟩)
          (whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}) := by
        intro y hy
        have hyc : y 0 ^ 2 + y 1 ^ 2 = 1 := hy.2
        by_cases hy1 : y 1 = 0
        · by_cases h : (j : ℕ) + 1 < ℓ
          · simp only [hFb, hy1, h, ↓reduceIte, ↓reduceDIte]
            exact hcornerL y hy.1 hy1 hyc j h
          · simp only [hFb, hy1, h, ↓reduceIte, ↓reduceDIte]
            exact hcornerR y hy.1 hy1 hyc j (by omega)
        · simp only [hFb, hy1, ↓reduceIte]
      refine ContinuousOn.congr ?_ hEq
      by_cases h : (j : ℕ) + 1 < ℓ
      · simp only [h, ↓reduceDIte]
        exact (continuousOn_pi.1 hNCc _).comp hyt.continuousOn (fun y hy => hytK y hy.1)
      · simp only [h, ↓reduceDIte]
        exact continuousOn_pi.1 contR _
  · intro y hy
    have hyH : y ∈ whitneyHalf := hy.1
    set V := Submodule.span ℝ (Set.range (Fin.append (T y) (Fb y))) with hV
    have hT0 : T y 0 ∈ V := Submodule.subset_span ⟨Fin.castAdd (m - 2) 0, by simp⟩
    have hT1 : T y 1 ∈ V := Submodule.subset_span ⟨Fin.castAdd (m - 2) 1, by simp⟩
    have hF : ∀ j, Fb y j ∈ V := fun j => Submodule.subset_span ⟨Fin.natAdd 2 j, by simp⟩
    have key : ∀ N : Fin m → Fin m → ℝ, LinearIndependent ℝ N → (∀ i, N i ∈ V) → ⊤ ≤ V := by
      intro N hN hNV
      rw [← hN.span_eq_top_of_card_eq_finrank' (by simp)]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hNV i)
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · by_cases hy1 : y 1 = 0
      · have hyD : pD (yt y) = y := by
          funext i; fin_cases i
          · simp [pD, yt]
          · simp [pD, hy1]
        refine key (ND (yt y)) (hNDi _ (hytK y hyH)) fun i => ?_
        by_cases hi : (i : ℕ) ≤ ℓ
        · rw [hNDfix _ (hytK y hyH) i (by simp [SD]; omega)]
          by_cases h : (i : ℕ) < ℓ
          · simp only [QD, h, ↓reduceDIte, hyD]
            by_cases h0 : (i : ℕ) = 0
            · have e : (⟨i, h⟩ : Fin ℓ) = ⟨0, by omega⟩ := Fin.ext h0
              rw [e, headL y hyH hy1]
              exact hT0
            · have hF' := hF ⟨(i : ℕ) - 1, by omega⟩
              have e : (⟨(i : ℕ) - 1 + 1, by omega⟩ : Fin ℓ) = ⟨i, h⟩ := Fin.ext (by simp; omega)
              have h' : ((i : ℕ) - 1) + 1 < ℓ := by omega
              simp only [hFb, hy1, ↓reduceIte, h', ↓reduceDIte] at hF'
              rw [e] at hF'
              exact hF'
          · have h' : (i : ℕ) = ℓ := by omega
            simp only [QD, h, ↓reduceDIte]
            simp only [h', ↓reduceIte, hyD]
            exact hT1
        · have hF' := hF ⟨(i : ℕ) - 2, by omega⟩
          have h' : ¬ ((i : ℕ) - 2 + 1 < ℓ) := by omega
          have e : (⟨(i : ℕ) - 2 + 2, by omega⟩ : Fin m) = i := Fin.ext (by simp; omega)
          simp only [hFb, hy1, ↓reduceIte, h', ↓reduceDIte] at hF'
          rw [e] at hF'
          exact hF'
      · have hyc : y 0 ^ 2 + y 1 ^ 2 = 1 := by
          rcases hy.2 with h | h
          · exact absurd h hy1
          · exact h
        have hyC : pC (yt y) = y := by
          funext i; fin_cases i
          · simp [pC, yt]
          · simp only [pC, yt, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
            rw [show 1 - y 0 ^ 2 = y 1 ^ 2 by linarith]
            exact Real.sqrt_sq hyH.2
        refine key (NC (yt y)) (hNCi _ (hytK y hyH)) fun i => ?_
        by_cases h0 : (i : ℕ) = 0
        · rw [hNCfix _ (hytK y hyH) i (by simp [SC]; omega)]
          simp only [QC, h0, ↓reduceIte, ρ, hyC]
          exact V.add_mem (V.smul_mem _ hT0) (V.smul_mem _ hT1)
        · by_cases hl : (i : ℕ) < ℓ
          · have hF' := hF ⟨(i : ℕ) - 1, by omega⟩
            have h' : ((i : ℕ) - 1) + 1 < ℓ := by omega
            have e : (⟨(i : ℕ) - 1 + 1, by omega⟩ : Fin m) = i := Fin.ext (by simp; omega)
            simp only [hFb, hy1, ↓reduceIte, h', ↓reduceDIte] at hF'
            rw [e] at hF'
            exact hF'
          · rw [hNCfix _ (hytK y hyH) i (by simp [SC]; omega)]
            have hl' : ℓ ≤ (i : ℕ) := by omega
            simp only [QC, h0, hl', ↓reduceIte, ↓reduceDIte, hyC]
            by_cases hle : (i : ℕ) = ℓ
            · have e : (⟨(i : ℕ) - ℓ, by omega⟩ : Fin (m - ℓ)) = ⟨0, by omega⟩ :=
                Fin.ext (by simp; omega)
              rw [e, headR y hyH hyc]
              exact V.add_mem (V.smul_mem _ hT0) (V.smul_mem _ hT1)
            · have hF' := hF ⟨(i : ℕ) - 2, by omega⟩
              have h' : ¬ ((i : ℕ) - 2 + 1 < ℓ) := by omega
              have e : (⟨(i : ℕ) - 2 + 2 - ℓ, by omega⟩ : Fin (m - ℓ)) =
                  ⟨(i : ℕ) - ℓ, by omega⟩ := Fin.ext (by simp; omega)
              simp only [hFb, hy1, ↓reduceIte, h', ↓reduceDIte] at hF'
              rw [e] at hF'
              exact hF'
    · simp only [Fintype.card_fin, Module.finrank_fin_fun]
      omega
  · intro y hy hy1 j hj
    simp only [hFb, hy1, hj, ↓reduceIte, ↓reduceDIte]
  · intro y hy hyc j hj
    have h : ¬ ((j : ℕ) + 1 < ℓ) := by omega
    by_cases hy1 : y 1 = 0
    · simp only [hFb, hy1, h, ↓reduceIte, ↓reduceDIte]
      exact hcornerR y hy hy1 hyc j hj
    · simp only [hFb, hy1, h, ↓reduceIte, ↓reduceDIte]

theorem exists_normalFrame_euclid {m ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hℓm : ℓ + 2 ≤ m)
    (hext : ℓ + 3 ≤ m ∨ 3 ≤ ℓ) {T : (Fin 2 → ℝ) → Fin 2 → (Fin m → ℝ)}
    (hT : ContinuousOn T whitneyHalf) (hTi : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (T y))
    (Fb : (Fin 2 → ℝ) → Fin (m - 2) → (Fin m → ℝ)) (hFb : ContinuousOn Fb whitneyBdry)
    (hFbi : ∀ y ∈ whitneyBdry, LinearIndependent ℝ (Fin.append (T y) (Fb y))) :
    ∃ Fr : (Fin 2 → ℝ) → Fin (m - 2) → (Fin m → ℝ), ContinuousOn Fr whitneyHalf ∧
      (∀ y ∈ whitneyHalf, LinearIndependent ℝ (Fin.append (T y) (Fr y))) ∧
      (∀ y ∈ whitneyHalf, y 1 = 0 → ∀ j : Fin (m - 2), (j : ℕ) + 1 < ℓ → Fr y j = Fb y j) ∧
      ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 → ∀ j : Fin (m - 2), ℓ ≤ (j : ℕ) + 1 →
        Fr y j = Fb y j := by
  classical
  have hBH : whitneyBdry ⊆ whitneyHalf := fun y hy => hy.1
  have hHcl : IsClosed whitneyHalf := by
    have : whitneyHalf = {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩ {y | 0 ≤ y 1} := rfl
    rw [this]
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const (continuous_apply 1))
  have hBcl : IsClosed whitneyBdry := by
    have : whitneyBdry = whitneyHalf ∩ ({y : Fin 2 → ℝ | y 1 = 0} ∪
        {y | y 0 ^ 2 + y 1 ^ 2 = 1}) := rfl
    rw [this]
    exact hHcl.inter ((isClosed_eq (continuous_apply 1) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const))
  have hHcpt : IsCompact whitneyHalf := by
    refine Metric.isCompact_of_isClosed_isBounded hHcl ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have := hy.1
    fin_cases i
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg (y 1)]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg (y 0)]
  have hHconv : Convex ℝ whitneyHalf := by
    intro a ha b hb s t hs ht hst
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg hs ht, mul_nonneg (mul_nonneg hs ht) (sq_nonneg (a 0 - b 0)),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg (a 1 - b 1))]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
  have triv : ∀ (s : ℕ) (S : (Fin 2 → ℝ) → Fin s → (Fin m → ℝ)), ContinuousOn S whitneyHalf →
      (∀ y ∈ whitneyHalf, LinearIndependent ℝ (S y)) →
      ∃ E : (Fin 2 → ℝ) → Fin (m - s) → (Fin m → ℝ), ContinuousOn E whitneyHalf ∧
        ∀ y ∈ whitneyHalf, LinearIndependent ℝ (Fin.append (S y) (E y)) := by
    intro s S hSc hSi
    let Sm : (Fin 2 → ℝ) → Matrix (Fin m) (Fin s) ℝ := fun y => Matrix.of fun i j => S y j i
    let G : (Fin 2 → ℝ) → Matrix (Fin s) (Fin s) ℝ := fun y => (Sm y).transpose * Sm y
    let Rm : (Fin 2 → ℝ) → Matrix (Fin s) (Fin s) ℝ := fun y => (G y).det⁻¹ • (G y).adjugate
    let Q : (Fin 2 → ℝ) → Matrix (Fin m) (Fin m) ℝ := fun y => Sm y * Rm y * (Sm y).transpose
    let P : (Fin 2 → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
      LinearMap.toContinuousLinearMap (Matrix.toLin' (1 - Q y))
    have hPapp : ∀ y v, P y v = Matrix.mulVec (1 - Q y) v := fun y v => rfl
    have hSmv : ∀ y (c : Fin s → ℝ), Matrix.mulVec (Sm y) c = ∑ j, c j • S y j := by
      intro y c
      ext i
      simp [Sm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have hdet : ∀ y ∈ whitneyHalf, (G y).det ≠ 0 := by
      intro y hy h0
      obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have h1 : Matrix.mulVec (Sm y) g ⬝ᵥ Matrix.mulVec (Sm y) g = 0 := by
        have : g ⬝ᵥ Matrix.mulVec (G y) g = 0 := by rw [hg, dotProduct_zero]
        rw [← this]
        simp only [G, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [dotProduct_self_eq_zero, hSmv] at h1
      exact hg0 (funext (Fintype.linearIndependent_iff.1 (hSi y hy) g h1))
    have hRG : ∀ y ∈ whitneyHalf, Rm y * G y = 1 := by
      intro y hy
      simp only [Rm, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ (hdet y hy),
        one_smul]
    have hGR : ∀ y ∈ whitneyHalf, G y * Rm y = 1 := by
      intro y hy
      simp only [Rm, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ (hdet y hy),
        one_smul]
    have hQQ : ∀ y ∈ whitneyHalf, Q y * Q y = Q y := by
      intro y hy
      have : Q y * Q y = Sm y * (Rm y * G y) * Rm y * (Sm y).transpose := by
        simp only [Q, G, Matrix.mul_assoc]
      rw [this, hRG y hy, Matrix.mul_one]
    have hSQ : ∀ y ∈ whitneyHalf, (Sm y).transpose * (1 - Q y) = 0 := by
      intro y hy
      have : (Sm y).transpose * Q y = (G y * Rm y) * (Sm y).transpose := by
        simp only [Q, G, Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_one, this, hGR y hy, Matrix.one_mul, sub_self]
    have hQS : ∀ y ∈ whitneyHalf, Q y * Sm y = Sm y := by
      intro y hy
      have : Q y * Sm y = Sm y * (Rm y * G y) := by simp only [Q, G, Matrix.mul_assoc]
      rw [this, hRG y hy, Matrix.mul_one]
    have hPc : ContinuousOn P whitneyHalf := by
      rw [continuousOn_clm_apply]
      intro v
      simp only [hPapp]
      rw [continuousOn_iff_continuous_domRestrict] at hSc ⊢
      have hSmc : Continuous fun y : whitneyHalf => Sm y :=
        continuous_pi fun i => continuous_pi fun j =>
          (continuous_apply i).comp ((continuous_apply j).comp hSc)
      have hGc : Continuous fun y : whitneyHalf => G y :=
        hSmc.matrix_transpose.matrix_mul hSmc
      have hRc : Continuous fun y : whitneyHalf => Rm y :=
        (hGc.matrix_det.inv₀ fun y => hdet y y.2).smul hGc.matrix_adjugate
      have hQc : Continuous fun y : whitneyHalf => Q y :=
        (hSmc.matrix_mul hRc).matrix_mul hSmc.matrix_transpose
      exact (continuous_const.sub hQc).matrix_mulVec continuous_const
    have hPidem : ∀ y ∈ whitneyHalf, (P y).comp (P y) = P y := by
      intro y hy
      ext1 v
      rw [ContinuousLinearMap.comp_apply, hPapp, hPapp, Matrix.mulVec_mulVec]
      congr 1
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQQ y hy, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]
      abel
    have hSinj : ∀ y ∈ whitneyHalf, Function.Injective (Matrix.toLin' (Sm y)) := by
      intro y hy
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      rw [Matrix.toLin'_apply, hSmv] at hc
      exact funext (Fintype.linearIndependent_iff.1 (hSi y hy) c hc)
    have hPrank : ∀ y ∈ whitneyHalf,
        Module.finrank ℝ (LinearMap.range (P y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) = m - s := by
      intro y hy
      have hker : LinearMap.ker (P y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
          LinearMap.range (Matrix.toLin' (Sm y)) := by
        ext v
        rw [LinearMap.mem_ker, LinearMap.mem_range]
        change P y v = 0 ↔ _
        rw [hPapp]
        constructor
        · intro hv
          refine ⟨Matrix.mulVec (Rm y * (Sm y).transpose) v, ?_⟩
          rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
          exact hv.symm
        · rintro ⟨c, rfl⟩
          rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul,
            hQS y hy, sub_self, Matrix.zero_mulVec]
      have h := LinearMap.finrank_range_add_finrank_ker
        (P y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
      rw [hker, LinearMap.finrank_range_of_inj (hSinj y hy), Module.finrank_fin_fun,
        Module.finrank_fin_fun] at h
      omega
    obtain ⟨F, hFc, hF⟩ := exists_frame_of_projections hHcpt hHconv P hPc hPidem hPrank
    have hFo : ∀ y ∈ whitneyHalf, ∀ j, Matrix.mulVec (Sm y).transpose (F y j) = 0 := by
      intro y hy j
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 ((hF y hy).2 j)
      rw [← hu]
      change Matrix.mulVec (Sm y).transpose (P y u) = 0
      rw [hPapp, Matrix.mulVec_mulVec, hSQ y hy, Matrix.zero_mulVec]
    refine ⟨F, hFc, fun y hy => ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have hsum : Matrix.mulVec (Sm y) (fun i => g (Fin.castAdd (m - s) i)) +
        ∑ j, g (Fin.natAdd s j) • F y j = 0 := by
      rw [hSmv]; exact hg
    have h1 := congrArg (fun w => Matrix.mulVec (Sm y).transpose w) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h1
    have h2 : Matrix.mulVec (Sm y).transpose (∑ j, g (Fin.natAdd s j) • F y j) = 0 := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.mulVec_smul, hFo y hy j, smul_zero]
    rw [h2, add_zero, Matrix.mulVec_mulVec] at h1
    have ha0 := Matrix.eq_zero_of_mulVec_eq_zero (hdet y hy) h1
    rw [ha0, Matrix.mulVec_zero, zero_add] at hsum
    have hb0 := Fintype.linearIndependent_iff.1 (hF y hy).1 _ hsum
    intro x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · exact congrFun ha0 i
    · exact hb0 j
  have coeff : ∀ (r : ℕ) (s : Set (Fin 2 → ℝ)) (Bs : (Fin 2 → ℝ) → Fin r → (Fin m → ℝ)),
      ContinuousOn Bs s → (∀ y ∈ s, LinearIndependent ℝ (Bs y)) → r = m →
      ∀ v : (Fin 2 → ℝ) → (Fin m → ℝ), ContinuousOn v s →
      ∃ c : (Fin 2 → ℝ) → Fin r → ℝ, ContinuousOn c s ∧ ∀ y ∈ s, ∑ a, c y a • Bs y a = v y := by
    intro r s Bs hBc hBi hr v hv
    have hTB : ∀ w : (Fin 2 → ℝ) → (Fin m → ℝ), ContinuousOn w s →
        ContinuousOn (fun y => (⟨(0 : Fin m → ℝ), w y⟩ :
          TangentBundle 𝓘(ℝ, Fin m → ℝ) (Fin m → ℝ))) s := by
      intro w hw
      have h2 : ContinuousOn (fun y => (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Fin m → ℝ)).symm
          ((0 : Fin m → ℝ), w y)) s :=
        (tangentBundleModelSpaceHomeomorph _).symm.continuous.comp_continuousOn
          (continuousOn_const.prodMk hw)
      exact h2.congr fun y _ => rfl
    obtain ⟨c, hc, hcs⟩ := exists_continuousOn_frameCoeff (I := 𝓘(ℝ, Fin m → ℝ))
      (ψ := fun _ => (0 : Fin m → ℝ)) continuousOn_const
      (fun k => hTB _ ((continuousOn_pi.1 hBc) k)) hBi (hTB v hv)
      (fun y hy => by
        rw [(hBi y hy).span_eq_top_of_card_eq_finrank' (by simp [hr])]
        trivial)
    exact ⟨c, hc, hcs⟩
  let hmap : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    fun y => WithLp.toLp 2 ![y 0, 2 * y 1 - Real.sqrt (1 - y 0 ^ 2)]
  let gmap : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ) :=
    fun z => ![z 0, (z 1 + Real.sqrt (1 - z 0 ^ 2)) / 2]
  have hhc : Continuous hmap := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_apply 0
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (continuous_const.mul (continuous_apply 1)).sub
        (continuous_const.sub ((continuous_apply 0).pow 2)).sqrt
  have hgc : Continuous gmap := by
    have h0 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 0 :=
      (continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)
    have h1 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 1 :=
      (continuous_apply 1).comp (PiLp.continuous_ofLp 2 _)
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [gmap] using h0
    · simp only [gmap, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (h1.add (continuous_const.sub (h0.pow 2)).sqrt).div_const 2
  have hgh : ∀ y, gmap (hmap y) = y := by
    intro y
    funext i
    fin_cases i
    · simp [gmap, hmap]
    · simp [gmap, hmap]
  have hnorm : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
    intro z
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hhball : ∀ y ∈ whitneyHalf, hmap y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y 0 ^ 2 by nlinarith [sq_nonneg (y 1)])
    have hle : y 1 ≤ Real.sqrt (1 - y 0 ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    have hs0 := Real.sqrt_nonneg (1 - y 0 ^ 2)
    rw [mem_closedBall_zero_iff, hnorm, Real.sqrt_le_one]
    simp only [hmap, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  have hhsph : ∀ y ∈ whitneyBdry, hmap y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro y hy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y 0 ^ 2 by nlinarith [sq_nonneg (y 1)])
    rw [mem_sphere_zero_iff_norm, hnorm, Real.sqrt_eq_one]
    simp only [hmap, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases h3 with h3 | h3
    · have h3' : y 1 = 0 := h3
      rw [h3']; nlinarith
    · have h3' : y 0 ^ 2 + y 1 ^ 2 = 1 := h3
      have he : Real.sqrt (1 - y 0 ^ 2) = y 1 := by
        rw [show 1 - y 0 ^ 2 = y 1 ^ 2 by linarith, Real.sqrt_sq h2]
      rw [he]; nlinarith
  have hgB : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, gmap z ∈ whitneyBdry := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, hnorm, Real.sqrt_eq_one] at hz
    have he : Real.sqrt (1 - z 0 ^ 2) = |z 1| := by
      rw [show 1 - z 0 ^ 2 = z 1 ^ 2 by linarith, Real.sqrt_sq_eq_abs]
    simp only [whitneyBdry, whitneyHalf, gmap, mem_inter_iff, mem_ofPred_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, he]
    rcases le_total 0 (z 1) with h | h
    · rw [abs_of_nonneg h]
      refine ⟨⟨by nlinarith, by linarith⟩, Or.inr (by nlinarith)⟩
    · rw [abs_of_nonpos h]
      refine ⟨⟨by nlinarith, by linarith⟩, Or.inl (by ring)⟩
  obtain ⟨E1, hE1c, hE1i⟩ := triv 2 T hT hTi
  have main : ∀ (k : ℕ) (ι : Fin k → Fin (m - 2)), Function.Injective ι → k + 2 ≤ m - 2 →
      ∀ (R : Set (Fin 2 → ℝ)) (ρ : (Fin 2 → ℝ) → (Fin 2 → ℝ)), R ⊆ whitneyBdry →
      ContinuousOn ρ whitneyHalf → MapsTo ρ whitneyHalf R → (∀ y ∈ R, ρ y = y) →
      ∃ Fr : (Fin 2 → ℝ) → Fin (m - 2) → (Fin m → ℝ), ContinuousOn Fr whitneyHalf ∧
        (∀ y ∈ whitneyHalf, LinearIndependent ℝ (Fin.append (T y) (Fr y))) ∧
        (∀ y ∈ whitneyBdry, ∀ i, Fr y (ι i) = Fb y (ι i)) ∧ ∀ y ∈ R, Fr y = Fb y := by
    intro k ι hι hk R ρ hRB hρc hρm hρid
    have stepA : ∃ Fr1 : (Fin 2 → ℝ) → Fin k → (Fin m → ℝ), ContinuousOn Fr1 whitneyHalf ∧
        (∀ y ∈ whitneyHalf, LinearIndependent ℝ (Fin.append (T y) (Fr1 y))) ∧
        ∀ y ∈ whitneyBdry, ∀ i, Fr1 y i = Fb y (ι i) := by
      let B1 : (Fin 2 → ℝ) → Fin (2 + (m - 2)) → (Fin m → ℝ) := fun y => Fin.append (T y) (E1 y)
      have hB1c : ContinuousOn B1 whitneyHalf := by
        refine continuousOn_pi.2 fun x => ?_
        refine Fin.addCases (fun a => ?_) (fun i => ?_) x
        · simp only [B1, Fin.append_left]
          exact continuousOn_pi.1 hT a
        · simp only [B1, Fin.append_right]
          exact continuousOn_pi.1 hE1c i
      have hc : ∀ i : Fin k, ∃ c : (Fin 2 → ℝ) → Fin (2 + (m - 2)) → ℝ,
          ContinuousOn c whitneyBdry ∧ ∀ y ∈ whitneyBdry, ∑ a, c y a • B1 y a = Fb y (ι i) :=
        fun i => coeff _ whitneyBdry B1 (hB1c.mono hBH) (fun y hy => hE1i y (hBH hy)) (by omega)
          (fun y => Fb y (ι i)) (continuousOn_pi.1 hFb (ι i))
      choose c hcc hce using hc
      let Φ1 : (Fin 2 → ℝ) → (Fin (2 + (m - 2)) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
        fun y => Fintype.linearCombination ℝ (B1 y)
      have hΦ1e : ∀ w a, Φ1 w (Pi.single a 1) = B1 w a := by
        intro w a
        simp [Φ1]
      have hΦ1ker : ∀ w ∈ whitneyHalf, LinearMap.ker (Φ1 w) = ⊥ := fun w hw =>
        LinearMap.ker_eq_bot.2
          (linearIndependent_iff_injective_fintypeLinearCombination.1 (hE1i w hw))
      have hsingle : ∀ (a : Fin 2) (b : Fin (m - 2)),
          (Pi.single (Fin.castAdd (m - 2) a) (1 : ℝ) : Fin (2 + (m - 2)) → ℝ)
            (Fin.natAdd 2 b) = 0 := by
        intro a b
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      let nrm : Fin k → (Fin 2 → ℝ) → Fin (m - 2) → ℝ := fun i y b => c i y (Fin.natAdd 2 b)
      have hnrmc : ∀ i, ContinuousOn (nrm i) whitneyBdry := fun i =>
        continuousOn_pi.2 fun b => continuousOn_pi.1 (hcc i) (Fin.natAdd 2 b)
      have hnrmi : ∀ y ∈ whitneyBdry, LinearIndependent ℝ (fun i => nrm i y) := by
        intro y hy
        let e : Fin (2 + k) → Fin (2 + (m - 2)) :=
          Fin.append (Fin.castAdd (m - 2)) (fun i => Fin.natAdd 2 (ι i))
        have he : Function.Injective e := by
          intro x x' hxx
          induction x using Fin.addCases with
          | left a =>
            induction x' using Fin.addCases with
            | left a' =>
              simp only [e, Fin.append_left] at hxx
              rw [Fin.castAdd_injective _ _ hxx]
            | right i' =>
              simp only [e, Fin.append_left, Fin.append_right] at hxx
              have := congrArg Fin.val hxx
              simp at this
              omega
          | right i =>
            induction x' using Fin.addCases with
            | left a' =>
              simp only [e, Fin.append_left, Fin.append_right] at hxx
              have := congrArg Fin.val hxx
              simp at this
              omega
            | right i' =>
              simp only [e, Fin.append_right] at hxx
              rw [hι (Fin.natAdd_injective _ _ hxx)]
        have hind2 : LinearIndependent ℝ (Fin.append (T y) (Fb y) ∘ e) := (hFbi y hy).comp e he
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hw : ∀ b, ∑ i, g i * c i y (Fin.natAdd 2 b) = 0 := by
          intro b
          have := congrFun hg b
          simpa [nrm, Finset.sum_apply] using this
        have hΦw : ∑ a, (∑ i, g i * c i y a) • B1 y a = ∑ i, g i • Fb y (ι i) := by
          simp_rw [Finset.sum_smul, mul_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.smul_sum, hce i y hy]
        have hΦw2 : ∑ a, (∑ i, g i * c i y a) • B1 y a =
            ∑ a : Fin 2, (∑ i, g i * c i y (Fin.castAdd (m - 2) a)) • T y a := by
          rw [Fin.sum_univ_add]
          simp only [hw, zero_smul, Finset.sum_const_zero, add_zero, B1, Fin.append_left]
        have h0 := Fintype.linearIndependent_iff.1 hind2
          (Fin.append (fun a => -(∑ i, g i * c i y (Fin.castAdd (m - 2) a))) g) (by
            rw [Fin.sum_univ_add]
            simp only [Function.comp_apply, e, Fin.append_left, Fin.append_right, neg_smul,
              Finset.sum_neg_distrib]
            rw [← hΦw2, hΦw]
            abel)
        intro i
        simpa using h0 (Fin.natAdd 2 i)
      let Fl : EuclideanSpace ℝ (Fin 2) → Fin k → EuclideanSpace ℝ (Fin (m - 2)) :=
        fun z i => WithLp.toLp 2 (nrm i (gmap z))
      have hFlc : ContinuousOn Fl (Metric.sphere 0 1) := by
        refine continuousOn_pi.2 fun i => ?_
        exact (PiLp.continuous_toLp 2 _).comp_continuousOn
          ((hnrmc i).comp hgc.continuousOn hgB)
      have hFli : ∀ z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          LinearIndependent ℝ (Fl z) := by
        intro z hz
        exact (hnrmi (gmap z) (hgB z hz)).map'
          (WithLp.linearEquiv 2 ℝ (Fin (m - 2) → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
      obtain ⟨Gx, hGxc, hGxi, hGxe⟩ := exists_frame_extension hk Fl hFlc hFli
      let W1 : (Fin 2 → ℝ) → Fin k → Fin (m - 2) → ℝ := fun y i => WithLp.ofLp (Gx (hmap y) i)
      have hW1c : ∀ i b, ContinuousOn (fun y => W1 y i b) whitneyHalf := by
        intro i b
        exact ((continuous_apply b).comp (PiLp.continuous_ofLp 2 _)).comp_continuousOn
          ((continuousOn_pi.1 hGxc i).comp hhc.continuousOn hhball)
      have hW1i : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (W1 y) := by
        intro y hy
        exact (hGxi (hmap y) (hhball y hy)).map'
          (WithLp.linearEquiv 2 ℝ (Fin (m - 2) → ℝ)).toLinearMap (LinearEquiv.ker _)
      have hW1B : ∀ y ∈ whitneyBdry, ∀ i, W1 y i = nrm i y := by
        intro y hy i
        simp only [W1]
        rw [hGxe _ (hhsph y hy)]
        simp only [Fl, hgh]
      let τ0 : (Fin 2 → ℝ) → Fin k → Fin 2 → ℝ := fun y i a => c i y (Fin.castAdd (m - 2) a)
      have hτ0c : ContinuousOn τ0 whitneyBdry :=
        continuousOn_pi.2 fun i => continuousOn_pi.2 fun a =>
          continuousOn_pi.1 (hcc i) (Fin.castAdd (m - 2) a)
      obtain ⟨τg, hτg⟩ := ContinuousMap.exists_restrict_eq hBcl
        ⟨whitneyBdry.domRestrict τ0, hτ0c.domRestrict⟩
      have hτe : ∀ y ∈ whitneyBdry, τg y = τ0 y := by
        intro y hy
        have := congrArg (fun f => f ⟨y, hy⟩) hτg
        exact this
      refine ⟨fun y i => Φ1 y (Fin.append (τg y i) (W1 y i)), ?_, ?_, ?_⟩
      · refine continuousOn_pi.2 fun i => ?_
        simp only [Φ1, Fintype.linearCombination_apply]
        refine continuousOn_finsetSum _ fun x _ => ?_
        have hx : ContinuousOn (fun y => Fin.append (τg y i) (W1 y i) x) whitneyHalf := by
          refine Fin.addCases (fun a => ?_) (fun b => ?_) x
          · simp only [Fin.append_left]
            exact ((continuous_apply a).comp ((continuous_apply i).comp τg.continuous)).continuousOn
          · simp only [Fin.append_right]
            exact hW1c i b
        exact hx.smul (continuousOn_pi.1 hB1c x)
      · intro y hy
        let γ : Fin (2 + k) → (Fin (2 + (m - 2)) → ℝ) :=
          Fin.append (fun a => Pi.single (Fin.castAdd (m - 2) a) 1)
            (fun i => Fin.append (τg y i) (W1 y i))
        have hγ : LinearIndependent ℝ γ := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          have hev : ∀ p, ∑ x, g x * γ x p = 0 := by
            intro p
            have := congrFun hg p
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
            exact this
          have hnat : ∀ i, g (Fin.natAdd 2 i) = 0 := by
            have hW : ∑ i, g (Fin.natAdd 2 i) • W1 y i = 0 := by
              funext b
              have := hev (Fin.natAdd 2 b)
              rw [Fin.sum_univ_add] at this
              simp only [γ, Fin.append_left, Fin.append_right, hsingle, mul_zero,
                Finset.sum_const_zero, zero_add] at this
              simpa [Finset.sum_apply] using this
            exact Fintype.linearIndependent_iff.1 (hW1i y hy) _ hW
          have hcast : ∀ a, g (Fin.castAdd k a) = 0 := by
            intro a
            have := hev (Fin.castAdd (m - 2) a)
            rw [Fin.sum_univ_add] at this
            simp only [γ, Fin.append_left, Fin.append_right, hnat, zero_mul,
              Finset.sum_const_zero, add_zero] at this
            rw [Finset.sum_eq_single a] at this
            · simpa using this
            · intro b _ hb
              rw [Pi.single_eq_of_ne, mul_zero]
              intro h
              exact hb (Fin.castAdd_injective _ _ h).symm
            · simp
          intro x
          exact Fin.addCases (fun a => hcast a) (fun i => hnat i) x
        have hy_eq : Fin.append (T y) (fun i => Φ1 y (Fin.append (τg y i) (W1 y i))) =
            Φ1 y ∘ γ := by
          funext x
          refine Fin.addCases (fun a => ?_) (fun i => ?_) x
          · simp only [Function.comp_apply, γ, Fin.append_left, hΦ1e, B1]
          · simp only [Function.comp_apply, γ, Fin.append_right]
        rw [hy_eq]
        exact hγ.map' _ (hΦ1ker y hy)
      · intro y hy i
        change Φ1 y (Fin.append (τg y i) (W1 y i)) = Fb y (ι i)
        rw [hτe y hy, hW1B y hy i]
        have : Fin.append (τ0 y i) (nrm i y) = c i y := Fin.append_castAdd_natAdd
        rw [this]
        simp only [Φ1, Fintype.linearCombination_apply]
        exact hce i y hy
    obtain ⟨Fr1, hFr1c, hFr1i, hFr1B⟩ := stepA
    let S2 : (Fin 2 → ℝ) → Fin (2 + k) → (Fin m → ℝ) := fun y => Fin.append (T y) (Fr1 y)
    have hS2c : ContinuousOn S2 whitneyHalf := by
      refine continuousOn_pi.2 fun x => ?_
      refine Fin.addCases (fun a => ?_) (fun i => ?_) x
      · simp only [S2, Fin.append_left]
        exact continuousOn_pi.1 hT a
      · simp only [S2, Fin.append_right]
        exact continuousOn_pi.1 hFr1c i
    obtain ⟨E2, hE2c, hE2i⟩ := triv (2 + k) S2 hS2c hFr1i
    let B2 : (Fin 2 → ℝ) → Fin ((2 + k) + (m - (2 + k))) → (Fin m → ℝ) :=
      fun y => Fin.append (S2 y) (E2 y)
    have hB2c : ContinuousOn B2 whitneyHalf := by
      refine continuousOn_pi.2 fun x => ?_
      refine Fin.addCases (fun a => ?_) (fun i => ?_) x
      · simp only [B2, Fin.append_left]
        exact continuousOn_pi.1 hS2c a
      · simp only [B2, Fin.append_right]
        exact continuousOn_pi.1 hE2c i
    have hα : ∀ j : Fin (m - 2), ∃ c : (Fin 2 → ℝ) → Fin ((2 + k) + (m - (2 + k))) → ℝ,
        ContinuousOn c R ∧ ∀ y ∈ R, ∑ a, c y a • B2 y a = Fb y j := fun j =>
      coeff _ R B2 (hB2c.mono (hRB.trans hBH)) (fun y hy => hE2i y (hBH (hRB hy))) (by omega)
        (fun y => Fb y j) ((continuousOn_pi.1 hFb j).mono hRB)
    choose α hαc hαe using hα
    let β : (Fin 2 → ℝ) → Fin (m - 2) → Fin ((2 + k) + (m - (2 + k))) → ℝ := fun y j =>
      if h : ∃ i, ι i = j then Pi.single (Fin.castAdd (m - (2 + k)) (Fin.natAdd 2 h.choose)) 1
      else α j (ρ y)
    let Φ : (Fin 2 → ℝ) → (Fin ((2 + k) + (m - (2 + k))) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      fun y => Fintype.linearCombination ℝ (B2 y)
    have hΦe : ∀ w a, Φ w (Pi.single a 1) = B2 w a := by
      intro w a
      simp [Φ]
    have hΦker : ∀ w ∈ whitneyHalf, LinearMap.ker (Φ w) = ⊥ := fun w hw =>
      LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 (hE2i w hw))
    have hβblock : ∀ y i, β y (ι i) = Pi.single (Fin.castAdd (m - (2 + k)) (Fin.natAdd 2 i)) 1 := by
      intro y i
      have h : ∃ i', ι i' = ι i := ⟨i, rfl⟩
      simp only [β, h, ↓reduceDIte]
      rw [hι h.choose_spec]
    have hΦblock : ∀ y ∈ whitneyBdry, ∀ i, Φ y (β y (ι i)) = Fb y (ι i) := by
      intro y hy i
      rw [hβblock, hΦe]
      simp only [B2, S2, Fin.append_left, Fin.append_right]
      exact hFr1B y hy i
    have hΦrest : ∀ y ∈ R, ∀ w, ∀ j, (¬ ∃ i, ι i = j) → ρ w = y → Φ y (β w j) = Fb y j := by
      intro y hy w j h hw
      simp only [β, h, ↓reduceDIte, hw]
      simp only [Φ, Fintype.linearCombination_apply]
      exact hαe j y hy
    have hβc : ∀ j a, ContinuousOn (fun y => β y j a) whitneyHalf := by
      intro j a
      by_cases h : ∃ i, ι i = j
      · simp only [β, h, ↓reduceDIte]
        exact continuousOn_const
      · simp only [β, h, ↓reduceDIte]
        exact (continuousOn_pi.1 (hαc j) a).comp hρc hρm
    refine ⟨fun y j => Φ y (β y j), ?_, ?_, ?_, ?_⟩
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Φ, Fintype.linearCombination_apply]
      exact continuousOn_finsetSum _ fun a _ => (hβc j a).smul (continuousOn_pi.1 hB2c a)
    · intro y hy
      have hz : ρ y ∈ R := hρm hy
      have hzB : ρ y ∈ whitneyBdry := hRB hz
      let γ : Fin (2 + (m - 2)) → (Fin ((2 + k) + (m - (2 + k))) → ℝ) :=
        Fin.append (fun a => Pi.single (Fin.castAdd (m - (2 + k)) (Fin.castAdd k a)) 1) (β y)
      have hz_eq : Φ (ρ y) ∘ γ = Fin.append (T (ρ y)) (Fb (ρ y)) := by
        funext x
        refine Fin.addCases (fun a => ?_) (fun j => ?_) x
        · simp only [Function.comp_apply, γ, Fin.append_left, hΦe, B2, S2]
        · simp only [Function.comp_apply, γ, Fin.append_right]
          by_cases h : ∃ i, ι i = j
          · obtain ⟨i, rfl⟩ := h
            rw [hβblock, ← hβblock (ρ y) i]
            exact hΦblock _ hzB i
          · exact hΦrest _ hz y j h rfl
      have hγ : LinearIndependent ℝ γ :=
        LinearIndependent.of_comp (Φ (ρ y)) (by rw [hz_eq]; exact hFbi _ hzB)
      have hy_eq : Fin.append (T y) (fun j => Φ y (β y j)) = Φ y ∘ γ := by
        funext x
        refine Fin.addCases (fun a => ?_) (fun j => ?_) x
        · simp only [Function.comp_apply, γ, Fin.append_left, hΦe, B2, S2]
        · simp only [Function.comp_apply, γ, Fin.append_right]
      rw [hy_eq]
      exact hγ.map' _ (hΦker y hy)
    · intro y hy i
      exact hΦblock y hy i
    · intro y hy
      funext j
      by_cases h : ∃ i, ι i = j
      · obtain ⟨i, rfl⟩ := h
        exact hΦblock y (hRB hy) i
      · exact hΦrest y hy y j h (hρid y hy)
  rcases hext with h3 | h3
  · let ι : Fin (ℓ - 1) → Fin (m - 2) := fun i => ⟨i, by have := i.isLt; omega⟩
    have hι : Function.Injective ι := by
      intro a b hab
      exact Fin.ext (by simpa [ι] using congrArg Fin.val hab)
    let R : Set (Fin 2 → ℝ) := whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}
    let ρ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => ![y 0, Real.sqrt (1 - y 0 ^ 2)]
    have hRB : R ⊆ whitneyBdry := fun y hy => ⟨hy.1, Or.inr hy.2⟩
    have hρc : ContinuousOn ρ whitneyHalf := by
      refine Continuous.continuousOn ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · simpa [ρ] using continuous_apply 0
      · simp only [ρ]
        exact (continuous_const.sub ((continuous_apply 0).pow 2)).sqrt
    have hρm : MapsTo ρ whitneyHalf R := by
      intro y hy
      have h1 : y 0 ^ 2 ≤ 1 := by nlinarith [hy.1, sq_nonneg (y 1)]
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y 0 ^ 2 by linarith)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [ρ, hs]
      · simp [ρ, Real.sqrt_nonneg]
      · simp [ρ, hs]
    have hρid : ∀ y ∈ R, ρ y = y := by
      intro y hy
      have h2 : y 0 ^ 2 + y 1 ^ 2 = 1 := hy.2
      have h1 : 1 - y 0 ^ 2 = y 1 ^ 2 := by linarith
      funext i
      fin_cases i
      · simp [ρ]
      · simp [ρ, h1, Real.sqrt_sq hy.1.2]
    obtain ⟨Fr, hFrc, hFri, hFrB, hFrR⟩ :=
      main (ℓ - 1) ι hι (by omega) R ρ hRB hρc hρm hρid
    refine ⟨Fr, hFrc, hFri, ?_, ?_⟩
    · intro y hy hy1 j hj
      have := hFrB y ⟨hy, Or.inl hy1⟩ ⟨j, by omega⟩
      simpa [ι] using this
    · intro y hy hy1 j _
      rw [hFrR y ⟨hy, hy1⟩]
  · let ι : Fin (m - ℓ - 1) → Fin (m - 2) := fun i => ⟨i + (ℓ - 1), by have := i.isLt; omega⟩
    have hι : Function.Injective ι := by
      intro a b hab
      exact Fin.ext (by have := congrArg Fin.val hab; simp [ι] at this; omega)
    let R : Set (Fin 2 → ℝ) := whitneyHalf ∩ {y | y 1 = 0}
    let ρ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => ![y 0, 0]
    have hRB : R ⊆ whitneyBdry := fun y hy => ⟨hy.1, Or.inl hy.2⟩
    have hρc : ContinuousOn ρ whitneyHalf := by
      refine Continuous.continuousOn ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · simpa [ρ] using continuous_apply 0
      · simp only [ρ]
        exact continuous_const
    have hρm : MapsTo ρ whitneyHalf R := by
      intro y hy
      have h1 : y 0 ^ 2 ≤ 1 := by nlinarith [hy.1, sq_nonneg (y 1)]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [ρ] using h1
      · simp [ρ]
      · simp [ρ]
    have hρid : ∀ y ∈ R, ρ y = y := by
      intro y hy
      funext i
      fin_cases i
      · simp [ρ]
      · simp [ρ, show y 1 = 0 from hy.2]
    obtain ⟨Fr, hFrc, hFri, hFrB, hFrR⟩ :=
      main (m - ℓ - 1) ι hι (by omega) R ρ hRB hρc hρm hρid
    refine ⟨Fr, hFrc, hFri, ?_, ?_⟩
    · intro y hy hy1 j _
      rw [hFrR y ⟨hy, hy1⟩]
    · intro y hy hy1 j hj
      have := hFrB y ⟨hy, Or.inr hy1⟩ ⟨(j : ℕ) - (ℓ - 1), by have := j.isLt; omega⟩
      have hj' : ι ⟨(j : ℕ) - (ℓ - 1), by have := j.isLt; omega⟩ = j := by
        ext; simp [ι]; omega
      rwa [hj'] at this

def levelProj (i₀ : Fin n) (v : Fin n → ℝ) : Fin n → ℝ := v - v i₀ • Pi.single i₀ (1 : ℝ)

def whitneyAngle (y : Fin 2 → ℝ) : ℝ :=
  Real.pi / 2 - 2 * Real.arctan (y 0 / (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1))

def isInjImmersionOn (I : ModelWithCorners ℝ (Fin n → ℝ) H) {m : ℕ} (ψ : (Fin m → ℝ) → M)
    (Q : Set (Fin m → ℝ)) : Prop :=
  (∀ y ∈ Q, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I ψ y)) ∧ InjOn ψ Q

theorem dimH_affine_zeros_le {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {S : Submodule ℝ F}
    {Z : Set E} (hZ : IsOpen Z) {Φ₀ : E → F} (hΦ₀ : ContDiffOn ℝ 1 Φ₀ Z)
    {L : E → P →L[ℝ] F} (hL : ContDiffOn ℝ 1 L Z)
    (hrange : ∀ z ∈ Z, LinearMap.range (L z : P →ₗ[ℝ] F) = S) :
    dimH {w : P | ∃ z ∈ Z, Φ₀ z + L z w = 0} ≤
      ((Module.finrank ℝ E + Module.finrank ℝ P - Module.finrank ℝ S : ℕ) : ENNReal) := by
  classical
  have key : ∀ z₀ ∈ Z, ∃ N ∈ 𝓝[Z] z₀, dimH {w : P | ∃ z ∈ N ∩ Z, Φ₀ z + L z w = 0} ≤
      ((Module.finrank ℝ E + Module.finrank ℝ P - Module.finrank ℝ S : ℕ) : ENNReal) := by
    intro z₀ hz₀
    obtain ⟨T, hT⟩ := S.exists_isCompl
    let π : F →L[ℝ] S := LinearMap.toContinuousLinearMap (S.projectionOnto T hT)
    have hπS : ∀ x : S, π (x : F) = x := fun x => Submodule.projectionOnto_apply_left hT x
    let K₀ : Submodule ℝ P := LinearMap.ker (L z₀ : P →ₗ[ℝ] F)
    obtain ⟨C, hC⟩ := K₀.exists_isCompl
    let A : E → C →L[ℝ] S := fun z => (π.comp (L z)).comp C.subtypeL
    have hA1 : ∀ z ∈ Z, ContDiffAt ℝ 1 A z := fun z hz =>
      (contDiffAt_const.clm_comp (hL.contDiffAt (hZ.mem_nhds hz))).clm_comp contDiffAt_const
    have hK₀ : Module.finrank ℝ K₀ + Module.finrank ℝ S = Module.finrank ℝ P := by
      have h := LinearMap.finrank_range_add_finrank_ker (L z₀ : P →ₗ[ℝ] F)
      rw [hrange z₀ hz₀] at h
      change Module.finrank ℝ S + Module.finrank ℝ K₀ = _ at h
      omega
    have hCd : Module.finrank ℝ C = Module.finrank ℝ S := by
      have h := Submodule.finrank_add_eq_of_isCompl hC
      omega
    have hAinj : Function.Injective (A z₀) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have hmem : L z₀ (c : P) ∈ S := by
        rw [← hrange z₀ hz₀]; exact LinearMap.mem_range_self _ _
      have h1 : π (L z₀ (c : P)) = ⟨L z₀ (c : P), hmem⟩ := hπS ⟨_, hmem⟩
      have h2 : π (L z₀ (c : P)) = 0 := hc
      have h3 : L z₀ (c : P) = 0 := by
        have := h1.symm.trans h2
        simpa using congrArg Subtype.val this
      have hcK : (c : P) ∈ K₀ := h3
      have := hC.disjoint.le_bot ⟨hcK, c.2⟩
      exact Subtype.ext ((Submodule.mem_bot ℝ).1 this)
    let e₀ : C ≃L[ℝ] S :=
      (LinearMap.linearEquivOfInjective (A z₀ : C →ₗ[ℝ] S) hAinj hCd).toContinuousLinearEquiv
    have he₀ : (e₀ : C →L[ℝ] S) = A z₀ := by ext; rfl
    have hAc : ContinuousOn A Z := fun z hz => (hA1 z hz).continuousAt.continuousWithinAt
    let N : Set E := Z ∩ A ⁻¹' Set.range (ContinuousLinearEquiv.toContinuousLinearMap)
    have hNo : IsOpen N := hAc.isOpen_inter_preimage hZ ContinuousLinearEquiv.isOpen
    refine ⟨N, mem_nhdsWithin_of_mem_nhds (hNo.mem_nhds ⟨hz₀, e₀, he₀⟩), ?_⟩
    let ψ : E × K₀ → P := fun q =>
      (q.2 : P) - C.subtypeL ((A q.1).inverse (π (Φ₀ q.1 + L q.1 (q.2 : P))))
    have hsub : {w : P | ∃ z ∈ N ∩ Z, Φ₀ z + L z w = 0} ⊆ ψ '' (N ×ˢ Set.univ) := by
      rintro w ⟨z, ⟨hzN, -⟩, hw⟩
      have hwt : w ∈ K₀ ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨k, hk, c, hc, hkc⟩ := Submodule.mem_sup.1 hwt
      refine ⟨(z, ⟨k, hk⟩), ⟨hzN, Set.mem_univ _⟩, ?_⟩
      obtain ⟨e, he⟩ := hzN.2
      have hAz : A z = (e : C →L[ℝ] S) := he.symm
      have hπ : π (Φ₀ z + L z k) = -(A z ⟨c, hc⟩) := by
        have h0 : Φ₀ z + L z k = -(L z c) := by
          rw [← hkc, map_add] at hw
          rw [eq_neg_iff_add_eq_zero, add_assoc]; exact hw
        rw [h0, map_neg]; rfl
      simp only [ψ]
      rw [hπ, hAz, ContinuousLinearMap.inverse_equiv]
      simp only [map_neg, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
        sub_neg_eq_add]
      exact hkc
    have hlip : ∀ q ∈ N ×ˢ (Set.univ : Set K₀), ∃ K, ∃ t ∈ 𝓝[N ×ˢ Set.univ] q,
        LipschitzOnWith K ψ t := by
      rintro ⟨z, u⟩ ⟨hzN, -⟩
      obtain ⟨e, he⟩ := hzN.2
      have hz : z ∈ Z := hzN.1
      have hinv : ContDiffAt ℝ 1 (fun z => (A z).inverse) z := by
        have h := contDiffAt_map_inverse (n := 1) e
        have he' : (e : C →L[ℝ] S) = A z := he
        rw [he'] at h
        exact h.comp z (hA1 z hz)
      have hψ : ContDiffAt ℝ 1 ψ (z, u) := by
        have hsnd : ContDiffAt ℝ 1 (fun q : E × K₀ => (q.2 : P)) (z, u) :=
          (K₀.subtypeL.contDiff.comp contDiff_snd).contDiffAt
        have hΦ : ContDiffAt ℝ 1 (fun q : E × K₀ => Φ₀ q.1) (z, u) :=
          (hΦ₀.contDiffAt (hZ.mem_nhds hz)).comp (z, u) contDiffAt_fst
        have hLq : ContDiffAt ℝ 1 (fun q : E × K₀ => L q.1) (z, u) :=
          (hL.contDiffAt (hZ.mem_nhds hz)).comp (z, u) contDiffAt_fst
        have hIq : ContDiffAt ℝ 1 (fun q : E × K₀ => (A q.1).inverse) (z, u) :=
          hinv.comp (z, u) contDiffAt_fst
        exact hsnd.sub (contDiffAt_const.clm_apply
          (hIq.clm_apply (contDiffAt_const.clm_apply (hΦ.add (hLq.clm_apply hsnd)))))
      obtain ⟨K, t, ht, hK⟩ := hψ.exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
    calc dimH {w : P | ∃ z ∈ N ∩ Z, Φ₀ z + L z w = 0}
        ≤ dimH (ψ '' (N ×ˢ Set.univ)) := dimH_mono hsub
      _ ≤ dimH (N ×ˢ (Set.univ : Set K₀)) := dimH_image_le_of_locally_lipschitzOn hlip
      _ ≤ dimH (Set.univ : Set (E × K₀)) := dimH_mono (Set.subset_univ _)
      _ = ((Module.finrank ℝ (E × K₀) : ℕ) : ENNReal) := Real.dimH_univ_eq_finrank _
      _ = ((Module.finrank ℝ E + Module.finrank ℝ P - Module.finrank ℝ S : ℕ) : ENNReal) := by
        rw [Module.finrank_prod]
        congr 1
        omega
  choose! Nf hNf hdim using key
  obtain ⟨t, htZ, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hNf
  calc dimH {w : P | ∃ z ∈ Z, Φ₀ z + L z w = 0}
      ≤ dimH (⋃ x ∈ t, {w : P | ∃ z ∈ Nf x ∩ Z, Φ₀ z + L z w = 0}) := by
        apply dimH_mono
        rintro w ⟨z, hz, hw⟩
        obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcov hz)
        exact Set.mem_iUnion₂.2 ⟨x, hx, z, ⟨hzx, hz⟩, hw⟩
    _ = ⨆ x ∈ t, dimH {w : P | ∃ z ∈ Nf x ∩ Z, Φ₀ z + L z w = 0} := dimH_bUnion htc _
    _ ≤ _ := iSup₂_le fun x hx => hdim x (htZ hx)

theorem dimH_whitney_bad_params_lt (h6 : 6 ≤ n) (i₀ : Fin n) {Y A : Set (Fin 2 → ℝ)}
    (hY : IsOpen Y) (hA : IsOpen A) (hAY : A ⊆ Y) {G₀ : (Fin 2 → ℝ) → (Fin n → ℝ)}
    (hG₀ : ContDiffOn ℝ ∞ G₀ Y) {β : (Fin 2 → ℝ) → ℝ} (hβ : ContDiff ℝ ∞ β) (hβA : EqOn β 1 A)
    {d : ℕ} (hd : d + 3 < n) {ι : Type} [Countable ι] {U : ι → Set (Fin d → ℝ)}
    {g : ι → (Fin d → ℝ) → (Fin n → ℝ)} (hU : ∀ i, IsOpen (U i))
    (hg : ∀ i, ContDiffOn ℝ 1 (g i) (U i)) :
    dimH ({w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) | ∃ y ∈ A, ¬ Function.Injective
        (fderiv ℝ (fun y' => G₀ y' + β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) y)} ∪
      {w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) | ∃ y ∈ A, ∃ y' ∈ Y, y' ≠ y ∧
        G₀ y + β y • levelProj i₀ (w.1 + ∑ k, y k • w.2 k) =
          G₀ y' + β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)} ∪
      {w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) | ∃ y ∈ A, ∃ i, ∃ u ∈ U i,
        G₀ y + β y • levelProj i₀ (w.1 + ∑ k, y k • w.2 k) = g i u}) <
      Module.finrank ℝ ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hG1 : ContDiffOn ℝ 1 G₀ Y := hG₀.of_le (by exact_mod_cast le_top)
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by exact_mod_cast le_top)
  let ℓL : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.id ℝ (Fin n → ℝ) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀).smulRight
      (Pi.single i₀ (1 : ℝ) : Fin n → ℝ)
  have hℓ : ∀ x, levelProj i₀ x = ℓL x := fun x => by
    simp [ℓL, levelProj]
  let S : Submodule ℝ (Fin n → ℝ) := LinearMap.range (ℓL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have hS : n - 1 ≤ Module.finrank ℝ S := by
    have h := LinearMap.finrank_range_add_finrank_ker (ℓL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have hker : LinearMap.ker (ℓL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤
        ℝ ∙ (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_span_singleton]
      refine ⟨x i₀, ?_⟩
      have hx' : levelProj i₀ x = 0 := by rw [hℓ]; exact hx
      simp only [levelProj, sub_eq_zero] at hx'
      exact hx'.symm
    have h1 : Module.finrank ℝ (LinearMap.ker (ℓL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ≤ 1 :=
      (Submodule.finrank_mono hker).trans (finrank_span_singleton (by simp)).le
    rw [Module.finrank_fin_fun] at h
    change Module.finrank ℝ S + _ = n at h
    omega
  let Mc : ℝ → (Fin 2 → ℝ) → ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    fun c c' => c • ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin 2 → Fin n → ℝ) +
      ∑ k, c' k • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin n → ℝ) k).comp
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin 2 → Fin n → ℝ))
  have hMc : ∀ c c' w, Mc c c' w = c • w.1 + ∑ k, c' k • w.2 k := by
    intro c c' w
    simp [Mc]
  have hrange : ∀ (c : ℝ) (c' : Fin 2 → ℝ), (c ≠ 0 ∨ c' ≠ 0) →
      LinearMap.range ((ℓL.comp (Mc c c') :
        ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) →L[ℝ] (Fin n → ℝ)) :
        ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ)) = S := by
    intro c c' hc
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨Mc c c' w, rfl⟩
    · rintro _ ⟨x, rfl⟩
      rcases hc with hc | hc
      · refine ⟨(c⁻¹ • x, 0), ?_⟩
        simp [hMc, smul_smul, hc]
      · obtain ⟨k, hk⟩ : ∃ k, c' k ≠ 0 := by
          by_contra h
          push Not at h
          exact hc (funext h)
        refine ⟨(0, Pi.single k ((c' k)⁻¹ • x)), ?_⟩
        simp [hMc, Pi.single_apply, smul_smul, hk]
  have hLsmooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E → ℝ)
      (c' : E → Fin 2 → ℝ), ContDiff ℝ 1 c → ContDiff ℝ 1 c' →
      ContDiff ℝ 1 (fun z => ℓL.comp (Mc (c z) (c' z))) := by
    intro E _ _ c c' hc hc'
    refine contDiff_const.clm_comp ?_
    exact (hc.smul contDiff_const).add
      (ContDiff.sum fun k _ => ((contDiff_pi.1 hc') k).smul contDiff_const)
  have hP : Module.finrank ℝ ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) = 3 * n := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp
    ring
  have key : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {Z : Set E}, IsOpen Z → ∀ {Φ₀ : E → (Fin n → ℝ)}, ContDiffOn ℝ 1 Φ₀ Z →
      ∀ {c : E → ℝ} {c' : E → Fin 2 → ℝ}, ContDiff ℝ 1 c → ContDiff ℝ 1 c' →
      (∀ z ∈ Z, c z ≠ 0 ∨ c' z ≠ 0) →
      dimH {w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) | ∃ z ∈ Z,
        Φ₀ z + ℓL (Mc (c z) (c' z) w) = 0} ≤
        ((Module.finrank ℝ E + 2 * n + 1 : ℕ) : ENNReal) := by
    intro E _ _ _ Z hZ Φ₀ hΦ₀ c c' hc hc' hcc
    have h := dimH_affine_zeros_le (S := S) hZ hΦ₀ (hLsmooth c c' hc hc').contDiffOn
      (fun z hz => hrange _ _ (hcc z hz))
    refine h.trans ?_
    rw [hP]
    exact_mod_cast (by omega)
  have hE4 : Module.finrank ℝ ((Fin 2 → ℝ) × (Fin 2 → ℝ)) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  have hEd : Module.finrank ℝ ((Fin 2 → ℝ) × (Fin d → ℝ)) = 2 + d := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  rw [hP, dimH_union, dimH_union, max_lt_iff, max_lt_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hD : ContDiffOn ℝ 1 (fderiv ℝ G₀) Y := hG₀.fderiv_of_isOpen hY (WithTop.coe_le_coe.2 le_top)
    have hΦ : ContDiffOn ℝ 1 (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => fderiv ℝ G₀ z.1 z.2)
        (A ×ˢ {u | u ≠ 0}) :=
      (hD.comp contDiffOn_fst (fun z hz => hAY hz.1)).clm_apply contDiffOn_snd
    refine lt_of_le_of_lt (dimH_mono ?_) ((key (hA.prod isOpen_ne) hΦ (contDiff_const (c := (0 : ℝ))) contDiff_snd
      (fun z hz => Or.inr hz.2)).trans_lt ?_)
    · rintro w ⟨y, hy, hni⟩
      have hy' : y ∈ Y := hAY hy
      have hGd : DifferentiableAt ℝ G₀ y :=
        (hG1.differentiableOn one_ne_zero).differentiableAt (hY.mem_nhds hy')
      let T : (Fin 2 → ℝ) →L[ℝ] (Fin n → ℝ) :=
        ∑ k, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).smulRight (ℓL (w.2 k))
      have hT : ∀ u, T u = ∑ k, u k • ℓL (w.2 k) := by
        intro u
        simp [T]
      have hev : (fun y' => G₀ y' + β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) =ᶠ[𝓝 y]
          (fun y' => G₀ y' + (ℓL w.1 + T y')) := by
        filter_upwards [hA.mem_nhds hy] with y' hy''
        rw [hβA hy'', Pi.one_apply, one_smul, hℓ, map_add, map_sum, hT]
        simp [map_smul]
      have hfd : fderiv ℝ (fun y' => G₀ y' + β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) y =
          fderiv ℝ G₀ y + T := by
        rw [hev.fderiv_eq]
        exact (hGd.hasFDerivAt.add (T.hasFDerivAt.const_add _)).fderiv
      rw [hfd, injective_iff_map_eq_zero] at hni
      push Not at hni
      obtain ⟨u, hu, hu0⟩ := hni
      refine ⟨(y, u), ⟨hy, hu0⟩, ?_⟩
      rw [hMc]
      simp only [map_sum, map_smul, zero_smul, zero_add]
      rw [add_apply, hT] at hu
      simpa using hu
    · rw [hE4]
      exact_mod_cast (by omega)
  · have hZ : IsOpen {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 ∈ A ∧ z.2 ∈ Y ∧ z.2 ≠ z.1} :=
      (hA.preimage continuous_fst).inter
        ((hY.preimage continuous_snd).inter (isOpen_ne_fun continuous_snd continuous_fst))
    have hΦ : ContDiffOn ℝ 1 (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => G₀ z.1 - G₀ z.2)
        {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 ∈ A ∧ z.2 ∈ Y ∧ z.2 ≠ z.1} :=
      (hG1.comp contDiffOn_fst (fun z hz => hAY hz.1)).sub
        (hG1.comp contDiffOn_snd (fun z hz => hz.2.1))
    have hc : ContDiff ℝ 1 (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => β z.1 - β z.2) :=
      (hβ1.comp contDiff_fst).sub (hβ1.comp contDiff_snd)
    have hc' : ContDiff ℝ 1
        (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => β z.1 • z.1 - β z.2 • z.2) :=
      ((hβ1.comp contDiff_fst).smul contDiff_fst).sub ((hβ1.comp contDiff_snd).smul contDiff_snd)
    have hcc : ∀ z ∈ {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 ∈ A ∧ z.2 ∈ Y ∧ z.2 ≠ z.1},
        β z.1 - β z.2 ≠ 0 ∨ β z.1 • z.1 - β z.2 • z.2 ≠ 0 := by
      rintro z ⟨h1, h2, h3⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨ha, hb⟩ := hcon
      have hb1 : β z.1 = 1 := hβA h1
      have hb2 : β z.2 = 1 := by linarith [sub_eq_zero.1 ha]
      rw [hb1, hb2, one_smul, one_smul, sub_eq_zero] at hb
      exact h3 hb.symm
    refine lt_of_le_of_lt (dimH_mono ?_) ((key hZ hΦ hc hc' hcc).trans_lt ?_)
    · rintro w ⟨y, hy, y', hy', hne, heq⟩
      refine ⟨(y, y'), ⟨hy, hy', hne⟩, ?_⟩
      rw [hMc]
      rw [hℓ, hℓ] at heq
      simp only [map_add, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Fin.sum_univ_two] at heq ⊢
      linear_combination (norm := module) heq
    · rw [hE4]
      exact_mod_cast (by omega)
  · refine lt_of_le_of_lt (dimH_mono (t := ⋃ i, {w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) |
      ∃ z ∈ A ×ˢ U i, (G₀ z.1 - g i z.2) + ℓL (Mc (β z.1) (β z.1 • z.1) w) = 0}) ?_) ?_
    · rintro w ⟨y, hy, i, u, hu, heq⟩
      refine Set.mem_iUnion.2 ⟨i, (y, u), ⟨hy, hu⟩, ?_⟩
      rw [hMc]
      rw [hℓ] at heq
      simp only [map_add, map_smul, Pi.smul_apply, smul_eq_mul,
        Fin.sum_univ_two] at heq ⊢
      linear_combination (norm := module) heq
    · rw [dimH_iUnion]
      refine lt_of_le_of_lt (iSup_le fun i => key (hA.prod (hU i))
        ((hG1.comp contDiffOn_fst (fun z hz => hAY hz.1)).sub
          ((hg i).comp contDiffOn_snd (fun z hz => hz.2)))
        (hβ1.comp contDiff_fst) ((hβ1.comp contDiff_fst).smul contDiff_fst)
        (fun z hz => Or.inl (by rw [hβA hz.1]; exact one_ne_zero))) ?_
      rw [hEd]
      exact_mod_cast (by omega)

theorem whitneyAngle_spec :
    ContDiffOn ℝ ∞ whitneyAngle {y | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} ∧
    (∀ y : Fin 2 → ℝ, whitneyAngle ![-y 0, y 1] = Real.pi - whitneyAngle y) ∧
    (∀ y : Fin 2 → ℝ, 0 < y 0 → whitneyAngle y = Real.arctan (y 1 / y 0)) ∧
    (∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      whitneyAngle y ∈ Ioo (-(Real.pi / 2)) (3 * Real.pi / 2) ∧
      y 0 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) * Real.cos (whitneyAngle y) ∧
      y 1 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) * Real.sin (whitneyAngle y)) ∧
    InjOn (fun y : Fin 2 → ℝ => ![whitneyAngle y, Real.sqrt (y 0 ^ 2 + y 1 ^ 2)])
      {y | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} ∧
    ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      Function.Injective (fderiv ℝ (fun y' : Fin 2 → ℝ =>
        ![whitneyAngle y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]) y) ∧
      fderiv ℝ whitneyAngle y y = 0 ∧
      fderiv ℝ whitneyAngle y (Pi.single 1 1) = y 0 / (y 0 ^ 2 + y 1 ^ 2) := by
  have hΩr : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      0 < y 0 ^ 2 + y 1 ^ 2 := by
    intro y hy
    by_contra hle
    push Not at hle
    have h0 : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = 0 := Real.sqrt_eq_zero'.mpr hle
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    rw [h0, h1] at hy
    norm_num at hy
  have hsq : ∀ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 2 = y 0 ^ 2 + y 1 ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  have hCDA : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      ContDiffAt ℝ ∞ whitneyAngle y := by
    intro y hy
    have h0 : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0) := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 1) := contDiff_apply ℝ ℝ 1
    have hs : ContDiffAt ℝ ∞ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) y :=
      ((h0.pow 2).add (h1.pow 2)).contDiffAt.sqrt (hΩr y hy).ne'
    have hq : ContDiffAt ℝ ∞
        (fun y : Fin 2 → ℝ => y 0 / (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1)) y :=
      h0.contDiffAt.div (hs.add h1.contDiffAt) hy.ne'
    exact contDiffAt_const.sub (contDiffAt_const.mul (Real.contDiff_arctan.contDiffAt.comp y hq))
  have hpolar : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      whitneyAngle y ∈ Ioo (-(Real.pi / 2)) (3 * Real.pi / 2) ∧
      y 0 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) * Real.cos (whitneyAngle y) ∧
      y 1 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) * Real.sin (whitneyAngle y) := by
    intro y hy
    have hr2 : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 2 = y 0 ^ 2 + y 1 ^ 2 := hsq y
    have hrpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_pos.mpr (hΩr y hy)
    set r := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hr_def
    set q := y 0 / (r + y 1) with hq_def
    have hθ : whitneyAngle y = Real.pi / 2 - 2 * Real.arctan q := rfl
    have hs1 : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (1 + q ^ 2) ^ 2 = 1 + q ^ 2 := Real.sq_sqrt (by positivity)
    have hkey : (r + y 1) ^ 2 + y 0 ^ 2 = 2 * r * (r + y 1) := by nlinarith
    have h1q : 1 + q ^ 2 = 2 * r / (r + y 1) := by
      rw [hq_def, div_pow]
      field_simp
      linarith [hkey]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hθ]; linarith [Real.arctan_lt_pi_div_two q]
    · rw [hθ]; linarith [Real.neg_pi_div_two_lt_arctan q]
    · rw [hθ, Real.cos_pi_div_two_sub, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
      have : 2 * (q / Real.sqrt (1 + q ^ 2)) * (1 / Real.sqrt (1 + q ^ 2)) = 2 * q / (1 + q ^ 2) := by
        field_simp
        rw [hs2]
      rw [this, h1q, hq_def]
      field_simp
    · rw [hθ, Real.sin_pi_div_two_sub, Real.cos_two_mul, Real.cos_arctan, div_pow, hs2, h1q]
      field_simp
      ring
  have hΩopen : IsOpen {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} :=
    isOpen_lt continuous_const (by fun_prop)
  have hθd : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      DifferentiableAt ℝ whitneyAngle y := fun y hy =>
    (hCDA y hy).differentiableAt (by simp)
  have hrd : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) y := by
    intro y hy
    have h0 : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0) := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 1) := contDiff_apply ℝ ℝ 1
    exact (((h0.pow 2).add (h1.pow 2)).contDiffAt.sqrt (hΩr y hy).ne').differentiableAt
      (by simp)
  refine ⟨fun y hy => (hCDA y hy).contDiffWithinAt, ?_, ?_, hpolar, ?_, ?_⟩
  · intro y
    simp only [whitneyAngle, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_sq, neg_div, Real.arctan_neg]
    ring
  · intro y hy0
    have hr2 := hsq y
    have hr0 : 0 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_nonneg _
    have hy : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 := by
      by_contra hle
      push Not at hle
      nlinarith [mul_nonneg (sub_nonneg.2 hle) hr0]
    obtain ⟨⟨hlo, _⟩, hc, hs⟩ := hpolar y hy
    have hrpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_pos.mpr (hΩr y hy)
    have hcos : 0 < Real.cos (whitneyAngle y) := by
      by_contra hle
      push Not at hle
      nlinarith [mul_nonneg hrpos.le (neg_nonneg.2 hle)]
    have hhi : whitneyAngle y < Real.pi / 2 := by
      by_contra hle
      push Not at hle
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [hpolar y hy |>.1.2])
      linarith
    have htan : y 1 / y 0 = Real.tan (whitneyAngle y) := by
      rw [Real.tan_eq_sin_div_cos]
      set r := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hr_def
      set θ := whitneyAngle y with hθ_def
      rw [hc, hs]
      field_simp
    rw [htan, Real.arctan_tan hlo hhi]
  · intro y hy y' hy' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    obtain ⟨_, hc, hs⟩ := hpolar y hy
    obtain ⟨_, hc', hs'⟩ := hpolar y' hy'
    funext i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [hc, hc', h0, h1]
    · simp only [Fin.mk_one]
      rw [hs, hs', h0, h1]
  · intro y hy
    refine ⟨?_, ?_, ?_⟩
    · let F : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y' =>
        ![whitneyAngle y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]
      let L : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun p =>
        ![p 1 * Real.cos (p 0), p 1 * Real.sin (p 0)]
      have hFd : DifferentiableAt ℝ F y := by
        rw [differentiableAt_pi]
        intro i
        fin_cases i
        · simpa [F] using hθd y hy
        · simpa [F] using hrd y hy
      have hLd : DifferentiableAt ℝ L (F y) := by
        rw [differentiableAt_pi]
        intro i
        fin_cases i
        · simp only [L, Fin.zero_eta, Matrix.cons_val_zero]
          fun_prop
        · simp only [L, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          fun_prop
      have heq : L ∘ F =ᶠ[𝓝 y] id := by
        filter_upwards [hΩopen.mem_nhds hy] with z hz
        obtain ⟨_, hc, hs⟩ := hpolar z hz
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Function.comp_apply, id_eq]
          exact hc.symm
        · simp only [Fin.mk_one, Fin.isValue, Function.comp_apply, id_eq]
          exact hs.symm
      have hcomp : (fderiv ℝ L (F y)).comp (fderiv ℝ F y) = ContinuousLinearMap.id ℝ _ := by
        rw [← fderiv_comp y hLd hFd, heq.fderiv_eq, fderiv_id]
      intro v w hvw
      have := congrArg (fderiv ℝ L (F y)) hvw
      have hv := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T v) hcomp
      have hw := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T w) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv hw
      rw [← hv, ← hw]
      exact this
    · have hhom : ∀ t : ℝ, 0 < t → whitneyAngle (t • y) = whitneyAngle y := by
        intro t ht
        simp only [whitneyAngle, Pi.smul_apply, smul_eq_mul]
        have h1 : (t * y 0) ^ 2 + (t * y 1) ^ 2 = t ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
        rw [h1, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le,
          show t * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + t * y 1 =
            t * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1) by ring, mul_div_mul_left _ _ ht.ne']
      have hθF : HasFDerivAt whitneyAngle (fderiv ℝ whitneyAngle y) ((fun t : ℝ => t • y) 1) := by
        simpa using (hθd y hy).hasFDerivAt
      have hline : HasDerivAt (fun t : ℝ => t • y) y 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
      have h1 := hθF.comp_hasDerivAt (1 : ℝ) hline
      have h2 : HasDerivAt (whitneyAngle ∘ fun t : ℝ => t • y) 0 1 := by
        refine (hasDerivAt_const (1 : ℝ) (whitneyAngle y)).congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds one_pos] with t ht
        exact hhom t ht
      exact h1.unique h2
    · have hr2 := hsq y
      have hrpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_pos.mpr (hΩr y hy)
      have hθF : HasFDerivAt whitneyAngle (fderiv ℝ whitneyAngle y)
          ((fun t : ℝ => y + t • (Pi.single 1 1 : Fin 2 → ℝ)) 0) := by
        simpa using (hθd y hy).hasFDerivAt
      have hline : HasDerivAt (fun t : ℝ => y + t • (Pi.single 1 1 : Fin 2 → ℝ))
          (Pi.single 1 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 1 1 : Fin 2 → ℝ)).const_add y
      have h1 := hθF.comp_hasDerivAt (0 : ℝ) hline
      have hfun : (whitneyAngle ∘ fun t : ℝ => y + t • (Pi.single 1 1 : Fin 2 → ℝ)) =
          fun t : ℝ => Real.pi / 2 - 2 * Real.arctan
            (y 0 / (Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2) + (y 1 + t))) := by
        funext t
        simp [whitneyAngle]
      rw [hfun] at h1
      have hs : HasDerivAt (fun t : ℝ => y 1 + t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 1)
      have hp : HasDerivAt (fun t : ℝ => y 0 ^ 2 + (y 1 + t) ^ 2) (2 * y 1) 0 := by
        simpa using (hs.pow 2).const_add (y 0 ^ 2)
      have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2))
          (2 * y 1 / (2 * Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) 0 := by
        simpa using hp.sqrt (by simpa using (hΩr y hy).ne')
      have hden : HasDerivAt (fun t : ℝ => Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2) + (y 1 + t))
          (2 * y 1 / (2 * Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) + 1) 0 := hsqrt.add hs
      have hq := (hasDerivAt_const (0 : ℝ) (y 0)).div hden (by simpa using hy.ne')
      have h2 := ((hq.arctan).const_mul 2).const_sub (Real.pi / 2)
      have h3 := h1.unique h2
      rw [h3]
      simp only [Pi.div_apply, add_zero, zero_mul, zero_sub]
      set r := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hr_def
      have hD : 0 < r + y 1 := hy
      have hkey : (r + y 1) ^ 2 + y 0 ^ 2 = 2 * r * (r + y 1) := by nlinarith
      rw [← hr2]
      field_simp
      rw [hkey]
      ring

theorem polarCorner_estimates (y : Fin 2 → ℝ) (h0 : |y 0 + 1| < 1 / 4) (h1 : |y 1| < 1 / 4) :
    |-Real.sqrt (y 0 ^ 2 + y 1 ^ 2) - y 0| ≤ y 1 ^ 2 ∧
    |(Real.pi - whitneyAngle y) - y 1| ≤ 2 * |y 1| * (|y 0 + 1| + |y 1|) ∧
    0 ≤ (Real.pi - whitneyAngle y) * y 1 ∧ (Real.pi - whitneyAngle y = 0 ↔ y 1 = 0) ∧
    ‖fderiv ℝ (fun y' : Fin 2 → ℝ =>
        ![-Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2), Real.pi - whitneyAngle y']) y -
      ContinuousLinearMap.id ℝ (Fin 2 → ℝ)‖ ≤ 4 * (|y 0 + 1| + |y 1|) := by
  obtain ⟨-, hrefl, hpos, -⟩ := whitneyAngle_spec
  have hθ : ∀ x : Fin 2 → ℝ, x 0 < 0 →
      Real.pi - whitneyAngle x = Real.arctan (x 1 * (-x 0)⁻¹) := by
    intro x hx
    have h := hpos ![-x 0, x 1] (by simp; linarith)
    rw [hrefl x] at h
    rw [h]
    simp [div_eq_mul_inv]
  have ha : y 0 < -3 / 4 := by
    have := (abs_lt.1 h0).2; linarith
  have ha' : -5 / 4 < y 0 := by
    have := (abs_lt.1 h0).1; linarith
  have hb : |y 1| < 1 / 4 := h1
  set r := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hr
  have hq : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hr2 : r ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hq
  clear_value r
  have hr_ge : -y 0 ≤ r := by
    rw [hr]; exact (Real.le_sqrt (by linarith) hq).2 (by rw [neg_sq]; linarith [sq_nonneg (y 1)])
  have hr_le : r ≤ -y 0 + |y 1| := by
    rw [hr, Real.sqrt_le_left (by linarith [abs_nonneg (y 1)])]
    have e : (-y 0 + |y 1|) ^ 2 - (y 0 ^ 2 + y 1 ^ 2) = 2 * (-y 0 * |y 1|) := by
      rw [← sq_abs (y 1)]; ring
    have := mul_nonneg (show (0 : ℝ) ≤ -y 0 by linarith) (abs_nonneg (y 1))
    linarith
  have hr34 : 3 / 4 < r := by linarith
  have hb2 : y 1 ^ 2 ≤ |y 1| / 4 := by
    rw [← sq_abs, sq]
    have := mul_le_mul_of_nonneg_left h1.le (abs_nonneg (y 1))
    linarith
  have hne0 : y 0 ≠ 0 := by linarith
  set u := y 1 * (-y 0)⁻¹ with hu
  have hθy : Real.pi - whitneyAngle y = Real.arctan u := hθ y (by linarith)
  clear_value u
  have hna : 0 < -y 0 := by linarith
  have hu_abs : |u| ≤ 4 / 3 * |y 1| := by
    rw [hu, abs_mul, abs_inv, abs_of_pos hna]
    rw [← div_eq_mul_inv, div_le_iff₀ hna]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 4 / 3 * -y 0 by linarith) (abs_nonneg (y 1))
    linarith
  have hat : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |Real.arctan t - t| ≤ t ^ 2 := by
    intro t ht0 ht1
    set x := Real.arctan t with hx
    have hx0 : 0 ≤ x := Real.arctan_nonneg.2 ht0
    have hxpi : x < Real.pi / 2 := Real.arctan_lt_pi_div_two t
    have htan : Real.tan x = t := Real.tan_arctan t
    have hle : x ≤ t := htan ▸ Real.le_tan hx0 hxpi
    have hcos : 0 < Real.cos x := Real.cos_arctan_pos t
    have hsin : Real.sin x = t * Real.cos x := by
      rw [← htan, Real.tan_eq_sin_div_cos]; field_simp
    have h1 : Real.sin x ≤ x := Real.sin_le hx0
    have h2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
    have h3 : t * (1 - x ^ 2 / 2) ≤ x := by
      have := mul_le_mul_of_nonneg_left h2 ht0
      linarith
    rw [abs_le]
    constructor
    · have k1 := mul_le_mul hle hle hx0 ht0
      have k2 : t * x ^ 2 ≤ x ^ 2 := mul_le_of_le_one_left (sq_nonneg x) ht1
      rw [sq] at k2 ⊢
      linarith
    · linarith [sq_nonneg t]
  have hat' : |Real.arctan u - u| ≤ u ^ 2 := by
    have hu1 : |u| ≤ 1 := by linarith
    rcases le_total 0 u with hu0 | hu0
    · exact hat u hu0 (by rw [abs_of_nonneg hu0] at hu1; exact hu1)
    · have := hat (-u) (by linarith) (by rw [abs_of_nonpos hu0] at hu1; exact hu1)
      rw [Real.arctan_neg, neg_sq] at this
      rwa [show -Real.arctan u - -u = -(Real.arctan u - u) by ring, abs_neg] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hsum : 0 ≤ r + y 0 := by linarith
    have hprod : (r + y 0) * (r - y 0) = y 1 ^ 2 := by linear_combination hr2
    rw [abs_of_nonpos (by linarith)]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ r - y 0 by linarith) hsum
    linarith
  · rw [hθy]
    have hub : |u - y 1| ≤ 4 / 3 * |y 1| * |y 0 + 1| := by
      have : u - y 1 = y 1 * (y 0 + 1) * (-y 0)⁻¹ := by
        rw [hu]; field_simp; ring
      rw [this, abs_mul, abs_mul, abs_inv, abs_of_pos hna, ← div_eq_mul_inv,
        div_le_iff₀ hna]
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 4 / 3 * -y 0 by linarith)
        (mul_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 0 + 1)))
      linarith
    have hu2 : u ^ 2 ≤ 16 / 9 * y 1 ^ 2 := by
      rw [← sq_abs u, ← sq_abs (y 1)]
      exact (pow_le_pow_left₀ (abs_nonneg u) hu_abs 2).trans_eq (by ring)
    calc |Real.arctan u - y 1| = |(Real.arctan u - u) + (u - y 1)| := by ring_nf
      _ ≤ |Real.arctan u - u| + |u - y 1| := abs_add_le _ _
      _ ≤ 2 * |y 1| * (|y 0 + 1| + |y 1|) := by
        rw [← sq_abs (y 1)] at hu2
        have := mul_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 0 + 1))
        have := sq_nonneg |y 1|
        linarith
  · rw [hθy]
    rcases le_total 0 (y 1) with hb0 | hb0
    · have : 0 ≤ u := by rw [hu]; exact mul_nonneg hb0 (inv_nonneg.2 hna.le)
      exact mul_nonneg (Real.arctan_nonneg.2 this) hb0
    · have : u ≤ 0 := by rw [hu]; exact mul_nonpos_of_nonpos_of_nonneg hb0 (inv_nonneg.2 hna.le)
      exact mul_nonneg_of_nonpos_of_nonpos (Real.arctan_le_zero.2 this) hb0
  · rw [hθy, Real.arctan_eq_zero_iff, hu, mul_eq_zero]
    simp [hne0]
  · have hne' : -y 0 ≠ 0 := by linarith
    have hrpos : 0 < r := by linarith
    have hq0 : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by rw [← hr2]; exact pow_ne_zero 2 hrpos.ne'
    obtain ⟨D0, hD0, hD0v⟩ : ∃ D : (Fin 2 → ℝ) →L[ℝ] ℝ,
        HasFDerivAt (fun x : Fin 2 → ℝ => -Real.sqrt (x 0 ^ 2 + x 1 ^ 2)) D y ∧
        ∀ v, D v = -(y 0 * v 0 + y 1 * v 1) / r := by
      have e0 : HasFDerivAt (fun x : Fin 2 → ℝ => x 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) y :=
        hasFDerivAt_apply (0 : Fin 2) y
      have e1 : HasFDerivAt (fun x : Fin 2 → ℝ => x 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) y :=
        hasFDerivAt_apply (1 : Fin 2) y
      have e2 := (e0.pow 2).add (e1.pow 2)
      have e3 := (e2.sqrt hq0).neg
      refine ⟨_, e3, fun v => ?_⟩
      simp [← hr]
      field_simp
    obtain ⟨D1, hD1, hD1v⟩ : ∃ D : (Fin 2 → ℝ) →L[ℝ] ℝ,
        HasFDerivAt (fun x : Fin 2 → ℝ => Real.pi - whitneyAngle x) D y ∧
        ∀ v, D v = (y 1 * v 0 - y 0 * v 1) / r ^ 2 := by
      have e0 : HasFDerivAt (fun x : Fin 2 → ℝ => x 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) y :=
        hasFDerivAt_apply (0 : Fin 2) y
      have e1 : HasFDerivAt (fun x : Fin 2 → ℝ => x 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) y :=
        hasFDerivAt_apply (1 : Fin 2) y
      have e2 := (hasDerivAt_inv hne').comp_hasFDerivAt y e0.neg
      have e3 := (e1.mul e2).arctan
      refine ⟨_, e3.congr_of_eventuallyEq ?_, fun v => ?_⟩
      · have hopen : IsOpen {x : Fin 2 → ℝ | x 0 < 0} :=
          isOpen_lt (continuous_apply 0) continuous_const
        filter_upwards [hopen.mem_nhds (show y 0 < 0 by linarith)] with x hx
        rw [hθ x hx]
        rfl
      · simp only [Fin.isValue, Pi.mul_apply, Function.comp_apply, Pi.neg_apply, inv_neg, mul_neg, even_two, Even.neg_pow, one_div, smul_neg, neg_smul, neg_neg, smul_add, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, neg_apply]
        rw [hr2]
        field_simp
        ring
    have hF : HasFDerivAt (fun y' : Fin 2 → ℝ =>
        ![-Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2), Real.pi - whitneyAngle y'])
        (ContinuousLinearMap.pi ![D0, D1]) y := by
      refine hasFDerivAt_pi'.2 fun i => ?_
      rw [ContinuousLinearMap.proj_pi]
      fin_cases i
      · simpa using hD0
      · simpa using hD1
    have hFd := hF.fderiv
    rw [hFd]
    have hS : 0 ≤ |y 0 + 1| + |y 1| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hN : 0 ≤ ‖v‖ := norm_nonneg v
    have hv0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
    have hv1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · simp only [sub_apply, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.id_apply, Pi.sub_apply, Real.norm_eq_abs]
      simp only [Fin.zero_eta, Matrix.cons_val_zero, hD0v]
      have hc : |-y 0 - r| ≤ |y 1| := by
        rw [abs_le]; constructor <;> linarith
      rw [show -(y 0 * v 0 + y 1 * v 1) / r - v 0 = ((-y 0 - r) * v 0 - y 1 * v 1) / r by
        field_simp; ring, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
      calc |(-y 0 - r) * v 0 - y 1 * v 1| ≤ |(-y 0 - r) * v 0| + |y 1 * v 1| := abs_sub _ _
        _ = |-y 0 - r| * |v 0| + |y 1| * |v 1| := by rw [abs_mul, abs_mul]
        _ ≤ |y 1| * ‖v‖ + |y 1| * ‖v‖ := by
          gcongr
        _ ≤ 4 * (|y 0 + 1| + |y 1|) * ‖v‖ * r := by
          have k1 : |y 1| * ‖v‖ ≤ (|y 0 + 1| + |y 1|) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (y 0 + 1)]) hN
          have k0 : 0 ≤ (|y 0 + 1| + |y 1|) * ‖v‖ := mul_nonneg hS hN
          have k2 : 0 ≤ (|y 0 + 1| + |y 1|) * ‖v‖ * (r - 3 / 4) :=
            mul_nonneg (mul_nonneg hS hN) (by linarith)
          linarith
    · simp only [sub_apply, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.id_apply, Pi.sub_apply, Real.norm_eq_abs]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hD1v]
      have hr2pos : 0 < r ^ 2 := by positivity
      have hc : |-y 0 - r ^ 2| ≤ 5 / 4 * |y 0 + 1| + |y 1| / 4 := by
        rw [hr2, show -y 0 - (y 0 ^ 2 + y 1 ^ 2) = (-y 0) * (y 0 + 1) - y 1 ^ 2 by ring]
        calc |(-y 0) * (y 0 + 1) - y 1 ^ 2| ≤ |(-y 0) * (y 0 + 1)| + |y 1 ^ 2| := abs_sub _ _
          _ = (-y 0) * |y 0 + 1| + y 1 ^ 2 := by
            rw [abs_mul, abs_of_pos hna, abs_of_nonneg (sq_nonneg (y 1))]
          _ ≤ 5 / 4 * |y 0 + 1| + |y 1| / 4 := by
            have := mul_le_mul_of_nonneg_right (show -y 0 ≤ 5 / 4 by linarith)
              (abs_nonneg (y 0 + 1))
            linarith
      rw [show (y 1 * v 0 - y 0 * v 1) / r ^ 2 - v 1 = (y 1 * v 0 + (-y 0 - r ^ 2) * v 1) / r ^ 2 by
        field_simp; ring, abs_div, abs_of_pos hr2pos, div_le_iff₀ hr2pos]
      calc |y 1 * v 0 + (-y 0 - r ^ 2) * v 1| ≤ |y 1 * v 0| + |(-y 0 - r ^ 2) * v 1| :=
            abs_add_le _ _
        _ = |y 1| * |v 0| + |-y 0 - r ^ 2| * |v 1| := by rw [abs_mul, abs_mul]
        _ ≤ |y 1| * ‖v‖ + (5 / 4 * |y 0 + 1| + |y 1| / 4) * ‖v‖ := by
          gcongr
        _ ≤ 4 * (|y 0 + 1| + |y 1|) * ‖v‖ * r ^ 2 := by
          have hr2b : 9 / 16 ≤ r ^ 2 := by
            have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hr34.le 2
            norm_num at this ⊢; linarith
          have k1 : |y 1| * ‖v‖ ≤ (|y 0 + 1| + |y 1|) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (y 0 + 1)]) hN
          have k1' : |y 0 + 1| * ‖v‖ ≤ (|y 0 + 1| + |y 1|) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (y 1)]) hN
          have k0 : 0 ≤ (|y 0 + 1| + |y 1|) * ‖v‖ := mul_nonneg hS hN
          have k2 : 0 ≤ (|y 0 + 1| + |y 1|) * ‖v‖ * (r ^ 2 - 9 / 16) :=
            mul_nonneg (mul_nonneg hS hN) (by linarith)
          linarith

theorem exists_cornerInterp :
    ∃ r₀ ρ₀ : ℝ, 0 < r₀ ∧ 2 * r₀ < ρ₀ ∧ ρ₀ ≤ 1 / 32 ∧ ∃ g : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      ContDiffOn ℝ ∞ g {y | -1 - r₀ < y 0 ∧ y 0 < 0 ∧ |y 1| < r₀} ∧
      (∀ y : Fin 2 → ℝ, -1 + 2 * ρ₀ ≤ y 0 → g y = y) ∧
      (∀ y : Fin 2 → ℝ, y 0 < -1 + ρ₀ →
        g y = ![-Real.sqrt (y 0 ^ 2 + y 1 ^ 2), Real.pi - whitneyAngle y]) ∧
      (∀ t : ℝ, t < 0 → g ![t, 0] = ![t, 0]) ∧
      ∀ y : Fin 2 → ℝ, -1 - r₀ < y 0 → y 0 < 0 → |y 1| < r₀ →
        |g y 0 - y 0| ≤ |y 1| ∧ |g y 1| ≤ 2 * |y 1| ∧ (g y 1 = 0 ↔ y 1 = 0) ∧
        ‖fderiv ℝ g y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)‖ ≤ 1 / 2 := by
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = 1 / 64 := ⟨_, rfl⟩
  have hρpos : 0 < ρ₀ := by rw [hρ₀]; norm_num
  have hstC : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hstC.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by norm_num))
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = ρ₀ / (4 * (C + 1)) := ⟨_, rfl⟩
  have hrpos : 0 < r₀ := by rw [hr₀]; positivity
  have hr_eq : r₀ * (4 * (C + 1)) = ρ₀ := by rw [hr₀]; field_simp
  have h2r : 2 * r₀ < ρ₀ := by nlinarith
  have hrρ : r₀ ≤ ρ₀ := by nlinarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ → ℝ,
      lam = fun s => Real.smoothTransition ((2 * ρ₀ - s) / ρ₀) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      P = fun y => ![-Real.sqrt (y 0 ^ 2 + y 1 ^ 2), Real.pi - whitneyAngle y] := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      g = fun y => y + lam (y 0 + 1) • (P y - y) := ⟨_, rfl⟩
  have hP0 : ∀ y, P y 0 = -Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := fun y => by simp [hP]
  have hP1 : ∀ y, P y 1 = Real.pi - whitneyAngle y := fun y => by simp [hP]
  have hg0 : ∀ y, g y 0 = y 0 + lam (y 0 + 1) * (P y 0 - y 0) := fun y => by simp [hg]
  have hg1 : ∀ y, g y 1 = y 1 + lam (y 0 + 1) * (P y 1 - y 1) := fun y => by simp [hg]
  have hlam_zero : ∀ s, 2 * ρ₀ ≤ s → lam s = 0 := by
    intro s hs
    rw [hlam]
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hρpos.le)
  have hlam_one : ∀ s, s ≤ ρ₀ → lam s = 1 := by
    intro s hs
    rw [hlam]
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hρpos]
    linarith
  have hlam01 : ∀ s, 0 ≤ lam s ∧ lam s ≤ 1 := fun s => by
    rw [hlam]; exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hlamS : ContDiff ℝ ∞ lam := by
    rw [hlam]
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  have hlamD : ∀ s, HasDerivAt lam
      (deriv Real.smoothTransition ((2 * ρ₀ - s) / ρ₀) * (-1 / ρ₀)) s := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => (2 * ρ₀ - x) / ρ₀) (-1 / ρ₀) s :=
      ((hasDerivAt_id' s).const_sub (2 * ρ₀)).div_const ρ₀
    have h2 : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition ((2 * ρ₀ - s) / ρ₀)) ((2 * ρ₀ - s) / ρ₀) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) _).hasDerivAt
    rw [hlam]
    exact h2.comp s h1
  have hΩ : ∀ y : Fin 2 → ℝ, y 0 < 0 → 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 := by
    intro y hy
    have h1 : |y 1| < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
    linarith [neg_abs_le (y 1)]
  have hΩopen : IsOpen {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} :=
    isOpen_lt continuous_const (by fun_prop)
  have hWsmooth := (whitneyAngle_spec).1
  have hOpenNeg : IsOpen {y : Fin 2 → ℝ | y 0 < 0} :=
    isOpen_lt (continuous_apply 0) continuous_const
  have hPsmooth : ContDiffOn ℝ ∞ P {y | y 0 < 0} := by
    intro y hy
    have hy' : y 0 < 0 := hy
    apply ContDiffAt.contDiffWithinAt
    rw [contDiffAt_pi, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [show (fun x => P x 0) = fun x => -Real.sqrt (x 0 ^ 2 + x 1 ^ 2) from funext hP0]
      refine ContDiffAt.neg (ContDiffAt.sqrt (by fun_prop) ?_)
      have : 0 < y 0 ^ 2 + y 1 ^ 2 := by nlinarith [sq_nonneg (y 1)]
      exact this.ne'
    · rw [show (fun x => P x 1) = fun x => Real.pi - whitneyAngle x from funext hP1]
      exact contDiffAt_const.sub (hWsmooth.contDiffAt (hΩopen.mem_nhds (hΩ y hy')))
  have hgS : ContDiffOn ℝ ∞ g {y : Fin 2 → ℝ | y 0 < 0} := by
    rw [hg]
    exact contDiffOn_id.add
      (((hlamS.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => y 0 + 1)).contDiffOn).smul
        (hPsmooth.sub contDiffOn_id))
  have hg_id : ∀ y : Fin 2 → ℝ, -1 + 2 * ρ₀ ≤ y 0 → g y = y := by
    intro y hy
    rw [hg]
    simp only [hlam_zero (y 0 + 1) (by linarith), zero_smul, add_zero]
  refine ⟨r₀, ρ₀, hrpos, h2r, by rw [hρ₀]; norm_num, g, ?_, hg_id, ?_, ?_, ?_⟩
  · exact hgS.mono fun y hy => hy.2.1
  · intro y hy
    rw [hg, hP]
    simp only [hlam_one (y 0 + 1) (by linarith), one_smul, add_sub_cancel]
  · intro t ht
    have hPt : P ![t, 0] = ![t, 0] := by
      rw [hP]
      ext i
      fin_cases i
      · simp [Real.sqrt_sq_eq_abs, abs_of_neg ht]
      · simp only [whitneyAngle]
        simp [Real.sqrt_sq_eq_abs, abs_of_neg ht, div_neg, div_self ht.ne, Real.arctan_neg,
          Real.arctan_one]
        ring
    rw [hg]
    simp [hPt]
  · intro y hy0 hy0' hy1
    by_cases hA : y 0 + 1 < 3 * ρ₀
    · have hb0 : |y 0 + 1| < 1 / 4 := by
        rw [abs_lt]; constructor <;> [linarith; (rw [hρ₀] at hA; linarith)]
      have hρ4 : 3 * ρ₀ + r₀ ≤ 1 / 16 := by rw [hρ₀] at hrρ ⊢; linarith
      have hb1 : |y 1| < 1 / 4 := by linarith
      have hs : |y 0 + 1| + |y 1| ≤ 3 * ρ₀ + r₀ := by
        have : |y 0 + 1| < 3 * ρ₀ := by rw [abs_lt]; constructor <;> linarith
        linarith
      obtain ⟨E1, E2, -, -, E5⟩ := polarCorner_estimates y hb0 hb1
      rw [← hP0, ← hP1] at *
      rw [← hP] at E5
      have hy1le : y 1 ^ 2 ≤ |y 1| := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (y 1)]
      have hE2' : |P y 1 - y 1| ≤ |y 1| / 8 := by
        refine E2.trans ?_
        nlinarith [abs_nonneg (y 1)]
      obtain ⟨hl0, hl1⟩ := hlam01 (y 0 + 1)
      have hd0 : |g y 0 - y 0| ≤ |y 1| := by
        rw [hg0, add_sub_cancel_left, abs_mul, abs_of_nonneg hl0]
        nlinarith [abs_nonneg (P y 0 - y 0)]
      have hd1 : |g y 1 - y 1| ≤ |y 1| / 8 := by
        rw [hg1, add_sub_cancel_left, abs_mul, abs_of_nonneg hl0]
        nlinarith [abs_nonneg (P y 1 - y 1)]
      refine ⟨hd0, ?_, ?_, ?_⟩
      · have := abs_sub_abs_le_abs_sub (g y 1) (y 1)
        linarith [abs_nonneg (y 1)]
      · constructor
        · intro h0
          rw [h0] at hd1
          by_contra hne
          have := abs_pos.2 hne
          rw [zero_sub, abs_neg] at hd1
          linarith
        · intro h0
          rw [h0, abs_zero, sub_zero] at hd1
          exact abs_nonpos_iff.1 (by linarith)
      · have hyneg : y 0 < 0 := hy0'
        have hPd : HasFDerivAt P (fderiv ℝ P y) y :=
          ((hPsmooth.contDiffAt (hOpenNeg.mem_nhds hyneg)).differentiableAt
            (by simp)).hasFDerivAt
        set L : ℝ := deriv Real.smoothTransition ((2 * ρ₀ - (y 0 + 1)) / ρ₀) * (-1 / ρ₀) with hL
        have hc : HasFDerivAt (fun z : Fin 2 → ℝ => lam (z 0 + 1))
            (L • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) y :=
          (hlamD (y 0 + 1)).comp_hasFDerivAt y ((hasFDerivAt_apply 0 y).add_const 1)
        have hgd : HasFDerivAt g (ContinuousLinearMap.id ℝ (Fin 2 → ℝ) +
            (lam (y 0 + 1) • (fderiv ℝ P y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) +
              (L • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight
                (P y - y))) y := by
          have := (hasFDerivAt_id y).add (hc.smul (hPd.sub (hasFDerivAt_id y)))
          convert this using 1
          · rw [hg]
            rfl
          · rfl
        rw [hgd.fderiv, add_sub_cancel_left]
        have hproj : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
            simpa using norm_le_pi_norm x 0
        have harg : (2 * ρ₀ - (y 0 + 1)) / ρ₀ ∈ Icc (-1 : ℝ) 3 := by
          constructor
          · rw [le_div_iff₀ hρpos]; linarith
          · rw [div_le_iff₀ hρpos]; linarith
        have hLb : |L| ≤ C / ρ₀ := by
          rw [hL, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hρpos]
          have := hC _ harg
          rw [Real.norm_eq_abs] at this
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right this hρpos.le
        have hv : ‖P y - y‖ ≤ |y 1| := by
          rw [pi_norm_le_iff_of_nonneg (abs_nonneg _), Fin.forall_fin_two]
          simp only [Pi.sub_apply, Real.norm_eq_abs]
          exact ⟨by linarith, by linarith [abs_nonneg (y 1)]⟩
        have hDP : ‖fderiv ℝ P y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)‖ ≤ 1 / 4 := by
          rw [hρ₀] at hs hrρ
          linarith
        have hCr : C / ρ₀ * r₀ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hρpos, ← hr_eq]
          nlinarith
        calc ‖lam (y 0 + 1) • (fderiv ℝ P y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) +
              (L • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight
                (P y - y)‖
            ≤ ‖lam (y 0 + 1) • (fderiv ℝ P y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ))‖ +
              ‖(L • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight
                (P y - y)‖ := norm_add_le _ _
          _ = |lam (y 0 + 1)| * ‖fderiv ℝ P y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)‖ +
              |L| * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0‖ *
                ‖P y - y‖ := by
            rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul,
              Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 * (1 / 4) + C / ρ₀ * 1 * r₀ := by
            rw [abs_of_nonneg hl0]
            gcongr
            exact hv.trans hy1.le
          _ ≤ 1 / 2 := by linarith
    · replace hA := not_lt.1 hA
      have hgy : g y = y := hg_id y (by linarith)
      refine ⟨by rw [hgy, sub_self, abs_zero]; exact abs_nonneg _,
        by rw [hgy]; linarith [abs_nonneg (y 1)], by rw [hgy], ?_⟩
      have hev : g =ᶠ[𝓝 y] id := by
        have hopen : IsOpen {z : Fin 2 → ℝ | -1 + 2 * ρ₀ < z 0} :=
          isOpen_lt continuous_const (continuous_apply 0)
        filter_upwards [hopen.mem_nhds (show -1 + 2 * ρ₀ < y 0 by linarith)] with z hz
        exact hg_id z hz.le
      rw [hev.fderiv_eq, fderiv_id, sub_self, norm_zero]
      norm_num

theorem exists_diameterReparam :
    ∃ r₀ ρ₀ : ℝ, 0 < r₀ ∧ 2 * r₀ < ρ₀ ∧ ρ₀ < 1 / 2 ∧ ∃ σ τ : (Fin 2 → ℝ) → ℝ,
      ContDiffOn ℝ ∞ σ {y | |y 0| < 1 + r₀ ∧ |y 1| < r₀} ∧
      ContDiffOn ℝ ∞ τ {y | |y 0| < 1 + r₀ ∧ |y 1| < r₀} ∧
      (∀ y : Fin 2 → ℝ, |y 0| < 1 + r₀ → |y 1| < r₀ → (τ y = 0 ↔ y 1 = 0)) ∧
      (∀ t : ℝ, |t| < 1 + r₀ → σ ![t, 0] = t) ∧
      (∀ y : Fin 2 → ℝ, |y 0| < 1 + r₀ → |y 1| < r₀ →
        |σ y - y 0| ≤ |y 1| ∧ |τ y| ≤ 2 * |y 1|) ∧
      InjOn (fun y => ![σ y, τ y]) {y | |y 0| < 1 + r₀ ∧ |y 1| < r₀} ∧
      (∀ y : Fin 2 → ℝ, |y 0| < 1 + r₀ → |y 1| < r₀ →
        Function.Injective (fderiv ℝ (fun y' : Fin 2 → ℝ => ![σ y', τ y']) y)) ∧
      (∀ y : Fin 2 → ℝ, |y 0| < 1 + r₀ → |y 1| < r₀ → y 0 < -1 + ρ₀ →
        σ y = -Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ∧ τ y = Real.pi - whitneyAngle y) ∧
      ∀ y : Fin 2 → ℝ, |y 0| < 1 + r₀ → |y 1| < r₀ → 1 - ρ₀ < y 0 →
        σ y = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ∧ τ y = whitneyAngle y := by
  obtain ⟨r₀, ρ₀, hr₀, hrρ, hρ, g, hg, hgid, hgpol, hgaxis, hgest⟩ := exists_cornerInterp
  obtain ⟨Rl, hRl⟩ : ∃ Rl : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ), ∀ y, Rl y = ![-y 0, y 1] :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun y => ![-y 0, y 1]
        map_add' := fun x y => by ext i; fin_cases i <;> simp; ring
        map_smul' := fun c x => by ext i; fin_cases i <;> simp }, fun y => rfl⟩
  have hRl0 : ∀ y, Rl y 0 = -y 0 := fun y => by simp [hRl]
  have hRl1 : ∀ y, Rl y 1 = y 1 := fun y => by simp [hRl]
  have hRR : ∀ y, Rl (Rl y) = y := fun y => by ext i; fin_cases i <;> simp [hRl]
  have hRnorm : ‖Rl‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, hRl0, norm_neg]
      exact norm_le_pi_norm v 0
    · simp only [Fin.mk_one, Fin.isValue, hRl1]
      exact norm_le_pi_norm v 1
  obtain ⟨Gm, hGdef⟩ : ∃ Gm : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      ∀ y, Gm y = if y 0 ≤ 0 then g y else Rl (g (Rl y)) := ⟨_, fun y => rfl⟩
  set S : Set (Fin 2 → ℝ) := {y | |y 0| < 1 + r₀ ∧ |y 1| < r₀} with hS
  set Ω : Set (Fin 2 → ℝ) := {y | -1 - r₀ < y 0 ∧ y 0 < 0 ∧ |y 1| < r₀} with hΩ
  have hΩo : IsOpen Ω := by
    refine (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt (continuous_apply 1).abs continuous_const))
  have hSo : IsOpen S :=
    (isOpen_lt (continuous_apply 0).abs continuous_const).inter
      (isOpen_lt (continuous_apply 1).abs continuous_const)
  have hSc : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    have hx0 := abs_lt.1 hx.1
    have hx1 := abs_lt.1 hx.2
    have hy0 := abs_lt.1 hy.1
    have hy1 := abs_lt.1 hy.2
    refine ⟨abs_lt.2 ⟨?_, ?_⟩, abs_lt.2 ⟨?_, ?_⟩⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; linarith
      · nlinarith
    · rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; linarith
      · nlinarith
    · rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; linarith
      · nlinarith
    · rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; linarith
      · nlinarith
  have hgAt : ∀ y ∈ Ω, ContDiffAt ℝ ∞ g y := fun y hy => hg.contDiffAt (hΩo.mem_nhds hy)
  have hGneg : ∀ y, y 0 ≤ 0 → Gm y = g y := fun y hy => by simp [hGdef, hy]
  have hGpos : ∀ y, 0 < y 0 → Gm y = Rl (g (Rl y)) := fun y hy => by simp [hGdef, not_le.2 hy]
  have hGid : ∀ z : Fin 2 → ℝ, |z 0| ≤ 1 - 2 * ρ₀ → Gm z = z := by
    intro z hz
    by_cases h : z 0 ≤ 0
    · rw [hGneg z h]
      exact hgid z (by linarith [neg_abs_le (z 0)])
    · rw [hGpos z (not_le.1 h), hgid (Rl z) (by rw [hRl0]; linarith [le_abs_self (z 0)]), hRR]
  have hmemΩ : ∀ y ∈ S, y 0 < 0 → y ∈ Ω := fun y hy h =>
    ⟨by linarith [neg_abs_le (y 0), hy.1], h, hy.2⟩
  have hmemΩ' : ∀ y ∈ S, 0 < y 0 → Rl y ∈ Ω := fun y hy h =>
    ⟨by rw [hRl0]; linarith [le_abs_self (y 0), hy.1], by rw [hRl0]; linarith,
      by rw [hRl1]; exact hy.2⟩
  have hloc : ∀ y ∈ S, ContDiffAt ℝ ∞ Gm y ∧
      ‖fderiv ℝ Gm y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)‖ ≤ 1 / 2 := by
    intro y hy
    rcases lt_trichotomy (y 0) 0 with h | h | h
    · have hyΩ : y ∈ Ω := hmemΩ y hy h
      have hev : Gm =ᶠ[𝓝 y] g := by
        filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds h] with z hz
        exact hGneg z (le_of_lt hz)
      refine ⟨(hgAt y hyΩ).congr_of_eventuallyEq hev, ?_⟩
      rw [hev.fderiv_eq]
      exact (hgest y hyΩ.1 hyΩ.2.1 hyΩ.2.2).2.2.2
    · have hev : Gm =ᶠ[𝓝 y] id := by
        filter_upwards [(isOpen_lt (continuous_apply 0).abs continuous_const).mem_nhds
          (show |y 0| < 1 - 2 * ρ₀ by rw [h, abs_zero]; linarith)] with z hz
        exact hGid z (le_of_lt hz)
      refine ⟨contDiffAt_id.congr_of_eventuallyEq hev, ?_⟩
      rw [hev.fderiv_eq, fderiv_id, sub_self, norm_zero]
      norm_num
    · have hyΩ : Rl y ∈ Ω := hmemΩ' y hy h
      have hev : Gm =ᶠ[𝓝 y] fun z => Rl (g (Rl z)) := by
        filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds h] with z hz
        exact hGpos z hz
      have hcd : ContDiffAt ℝ ∞ (fun z => Rl (g (Rl z))) y :=
        Rl.contDiff.contDiffAt.comp y ((hgAt _ hyΩ).comp y Rl.contDiff.contDiffAt)
      refine ⟨hcd.congr_of_eventuallyEq hev, ?_⟩
      have hgd : DifferentiableAt ℝ g (Rl y) := (hgAt _ hyΩ).differentiableAt (by simp)
      have hfd : HasFDerivAt (fun z => Rl (g (Rl z)))
          (Rl.comp ((fderiv ℝ g (Rl y)).comp Rl)) y :=
        Rl.hasFDerivAt.comp y (hgd.hasFDerivAt.comp y Rl.hasFDerivAt)
      rw [hev.fderiv_eq, hfd.fderiv]
      have hb := (hgest (Rl y) hyΩ.1 hyΩ.2.1 hyΩ.2.2).2.2.2
      set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
        fderiv ℝ g (Rl y) - ContinuousLinearMap.id ℝ (Fin 2 → ℝ) with hA
      have heq : Rl.comp ((fderiv ℝ g (Rl y)).comp Rl) - ContinuousLinearMap.id ℝ (Fin 2 → ℝ) =
          Rl.comp (A.comp Rl) := by
        ext1 v
        rw [hA]
        simp only [sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, map_sub, hRR]
      rw [heq]
      have h1 := ContinuousLinearMap.opNorm_comp_le Rl (A.comp Rl)
      have h2 := ContinuousLinearMap.opNorm_comp_le A Rl
      have hA0 := norm_nonneg A
      have hR0 := norm_nonneg Rl
      have h3 : ‖A‖ * ‖Rl‖ ≤ 1 / 2 := by nlinarith
      have h4 : ‖Rl‖ * (‖A‖ * ‖Rl‖) ≤ 1 / 2 := by nlinarith [mul_nonneg hA0 hR0]
      have h5 := mul_le_mul_of_nonneg_left h2 hR0
      linarith
  have hbd : ∀ y ∈ S, |Gm y 0 - y 0| ≤ |y 1| ∧ |Gm y 1| ≤ 2 * |y 1| ∧
      (Gm y 1 = 0 ↔ y 1 = 0) := by
    intro y hy
    rcases lt_trichotomy (y 0) 0 with h | h | h
    · have hyΩ : y ∈ Ω := hmemΩ y hy h
      rw [hGneg y h.le]
      exact (hgest y hyΩ.1 hyΩ.2.1 hyΩ.2.2).imp id (fun h' => h'.imp id (fun h'' => h''.1))
    · rw [hGid y (by rw [h, abs_zero]; linarith)]
      refine ⟨by simp, by linarith [abs_nonneg (y 1)], Iff.rfl⟩
    · have hyΩ : Rl y ∈ Ω := hmemΩ' y hy h
      obtain ⟨e1, e2, e3, -⟩ := hgest (Rl y) hyΩ.1 hyΩ.2.1 hyΩ.2.2
      rw [hGpos y h, hRl0, hRl1]
      rw [hRl0, hRl1] at e1
      rw [hRl1] at e2 e3
      refine ⟨?_, e2, e3⟩
      rw [show -g (Rl y) 0 - y 0 = -(g (Rl y) 0 - -y 0) by ring, abs_neg]
      exact e1
  have hGm : ContDiffOn ℝ ∞ Gm S := fun y hy => (hloc y hy).1.contDiffWithinAt
  have hfun : (fun y' : Fin 2 → ℝ => ![Gm y' 0, Gm y' 1]) = Gm := by
    funext y'
    ext i
    fin_cases i <;> rfl
  refine ⟨r₀, ρ₀, hr₀, hrρ, by linarith, fun y => Gm y 0, fun y => Gm y 1,
    contDiffOn_pi.1 hGm 0, contDiffOn_pi.1 hGm 1,
    fun y h0 h1 => (hbd y ⟨h0, h1⟩).2.2, ?_, fun y h0 h1 => ⟨(hbd y ⟨h0, h1⟩).1,
      (hbd y ⟨h0, h1⟩).2.1⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t 0 with h | h | h
    · change Gm ![t, 0] 0 = t
      rw [hGneg _ (by simp only [Fin.isValue, Matrix.cons_val_zero]; exact h.le), hgaxis t h]
      simp
    · change Gm ![t, 0] 0 = t
      rw [hGid _ (by simp [h]; linarith)]
      simp
    · change Gm ![t, 0] 0 = t
      have hR : Rl ![t, 0] = ![-t, 0] := by simp [hRl]
      rw [hGpos _ (by simp only [Fin.isValue, Matrix.cons_val_zero]; exact h), hR, hgaxis (-t) (by linarith)]
      simp [hRl]
  · intro x hx y hy hxy
    have hxy' : Gm x = Gm y := by
      have := hxy
      simp only at this
      rw [← congrFun hfun x, ← congrFun hfun y]
      exact this
    have hdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun w => Gm w - w) z := fun z hz =>
      ((hloc z hz).1.differentiableAt (by simp)).sub differentiableAt_fun_id
    have hbound : ∀ z ∈ S, ‖fderiv ℝ (fun w => Gm w - w) z‖ ≤ 1 / 2 := by
      intro z hz
      rw [fderiv_fun_sub ((hloc z hz).1.differentiableAt (by simp)) differentiableAt_fun_id,
        fderiv_fun_id]
      exact (hloc z hz).2
    have key := hSc.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
    rw [hxy', show Gm y - y - (Gm y - x) = x - y by abel] at key
    have hn : ‖x - y‖ = 0 := by
      have := norm_nonneg (x - y)
      rw [norm_sub_rev y x] at key
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 hn)
  · intro y h0 h1
    have hy : y ∈ S := ⟨h0, h1⟩
    rw [hfun]
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h2 := (hloc y hy).2
    have h3 : ‖(fderiv ℝ Gm y - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) v‖ ≤ 1 / 2 * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    rw [sub_apply, hv, ContinuousLinearMap.id_apply, zero_sub, norm_neg] at h3
    have : ‖v‖ = 0 := by linarith [norm_nonneg v]
    exact norm_eq_zero.1 this
  · intro y h0 h1 hc
    have hneg : y 0 ≤ 0 := by linarith
    change Gm y 0 = _ ∧ Gm y 1 = _
    rw [hGneg y hneg, hgpol y hc]
    simp
  · intro y h0 h1 hc
    have hpos : 0 < y 0 := by linarith
    change Gm y 0 = _ ∧ Gm y 1 = _
    have hc' : Rl y 0 < -1 + ρ₀ := by rw [hRl0]; linarith
    rw [hGpos y hpos, hgpol (Rl y) hc', hRl0, hRl1]
    have hw : whitneyAngle (Rl y) = Real.pi - whitneyAngle y := by
      rw [hRl]
      exact whitneyAngle_spec.2.1 y
    rw [hw]
    simp [hRl]

theorem exists_nonvanishing_path {s : ℕ} (hs : 2 ≤ s) {t₀ t₁ δ : ℝ} (hδ : 0 < δ)
    (ht : t₀ + δ < t₁ - δ) {e₁ e₂ : ℝ → EuclideanSpace ℝ (Fin s)}
    (he₁ : ContinuousOn e₁ (Icc t₀ (t₀ + δ))) (he₂ : ContinuousOn e₂ (Icc (t₁ - δ) t₁))
    (h₁ : ∀ t ∈ Icc t₀ (t₀ + δ), e₁ t ≠ 0) (h₂ : ∀ t ∈ Icc (t₁ - δ) t₁, e₂ t ≠ 0) :
    ∃ e : ℝ → EuclideanSpace ℝ (Fin s), ContinuousOn e (Icc t₀ t₁) ∧
      (∀ t ∈ Icc t₀ t₁, e t ≠ 0) ∧ EqOn e e₁ (Icc t₀ (t₀ + δ)) ∧ EqOn e e₂ (Icc (t₁ - δ) t₁) := by
  set a := t₀ + δ with ha
  set b := t₁ - δ with hb
  have hab : a < b := ht
  have hta : t₀ ≤ a := by rw [ha]; linarith
  have hbt : b ≤ t₁ := by rw [hb]; linarith
  have ha₁ : a ∈ Icc t₀ (t₀ + δ) := ⟨hta, le_rfl⟩
  have hb₂ : b ∈ Icc (t₁ - δ) t₁ := ⟨le_rfl, hbt⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin s)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    omega
  have hpc : IsPathConnected ({0}ᶜ : Set (EuclideanSpace ℝ (Fin s))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  have hjoin : JoinedIn ({0}ᶜ : Set (EuclideanSpace ℝ (Fin s))) (e₁ a) (e₂ b) :=
    hpc.joinedIn _ (h₁ a ha₁) _ (h₂ b hb₂)
  set γ := hjoin.somePath with hγ
  have hγmem : ∀ u, γ u ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin s))) := hjoin.somePath_mem
  let g : ℝ → EuclideanSpace ℝ (Fin s) := fun t => γ.extend ((t - a) / (b - a))
  have hgc : Continuous g :=
    γ.continuous_extend.comp ((continuous_id.sub continuous_const).div_const _)
  have hga : g a = e₁ a := by
    simp only [g, sub_self, zero_div, Path.extend_zero]
  have hgb : g b = e₂ b := by
    simp only [g, div_self (sub_ne_zero.mpr hab.ne'), Path.extend_one]
  have hgne : ∀ t, g t ≠ 0 := by
    intro t
    simp only [g]
    rw [Path.extend]
    exact hγmem _
  refine ⟨fun t => if t ≤ a then e₁ t else if t ≤ b then g t else e₂ t, ?_, ?_, ?_, ?_⟩
  · have hI : Icc t₀ t₁ = (Icc t₀ a ∪ Icc a b) ∪ Icc b t₁ := by
      rw [Icc_union_Icc_eq_Icc hta hab.le, Icc_union_Icc_eq_Icc (hta.trans hab.le) hbt]
    rw [hI]
    refine ContinuousOn.union_of_isClosed
      (ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc) ?_
      (isClosed_Icc.union isClosed_Icc) isClosed_Icc
    · refine (he₁.mono (fun t ht => ⟨ht.1, ht.2⟩)).congr ?_
      intro t ht
      simp only [ite_eq_left ht.2]
    · refine hgc.continuousOn.congr ?_
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        simp only [le_refl, ite_true, hga]
      · simp only [ite_eq_right (not_le.mpr h), ite_eq_left ht.2]
    · refine (he₂.mono (fun t ht => ⟨ht.1, ht.2⟩)).congr ?_
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        simp only [ite_eq_right (not_le.mpr hab), le_refl, ite_true, hgb]
      · simp only [ite_eq_right (not_le.mpr (hab.trans h)), ite_eq_right (not_le.mpr h)]
  · intro t ht
    dsimp only
    split_ifs with h1 h2
    · exact h₁ t ⟨ht.1, h1⟩
    · exact hgne t
    · exact h₂ t ⟨(not_le.mp h2).le, ht.2⟩
  · intro t ht
    simp only [ite_eq_left ht.2]
  · intro t ht
    dsimp only
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      simp only [ite_eq_right (not_le.mpr hab), le_refl, ite_true, hgb]
    · simp only [ite_eq_right (not_le.mpr (hab.trans h)), ite_eq_right (not_le.mpr h)]

section WhitneyGeneric

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ}

omit [T2Space M] [I.Boundaryless] in
theorem eventually_locallyInjective_of_immersion {m : ℕ} {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {W : Set (Fin m → ℝ)} (hW : IsOpen W)
    {Hf : (Fin m → ℝ) → P → M}
    (hH : ContMDiffOn 𝓘(ℝ, (Fin m → ℝ) × P) I ∞ (fun q : (Fin m → ℝ) × P => Hf q.1 q.2)
      (W ×ˢ univ))
    {y₀ : Fin m → ℝ} (hy₀ : y₀ ∈ W)
    (himm : Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I (fun y => Hf y 0) y₀)) :
    ∃ δ > 0, ∀ᶠ w in 𝓝 (0 : P), ∀ y ∈ Metric.ball y₀ δ,
      Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I (fun y' => Hf y' w) y) ∧
      ∀ y' ∈ Metric.ball y₀ δ, Hf y w = Hf y' w → y = y' := by
  classical
  set x₀ : M := Hf y₀ 0 with hx₀
  set Hf' : (Fin m → ℝ) × P → M := fun q => Hf q.1 q.2 with hHf'
  let F : (Fin m → ℝ) × P → (Fin n → ℝ) := fun q => extChartAt I x₀ (Hf q.1 q.2)
  let S : Set ((Fin m → ℝ) × P) := (W ×ˢ univ) ∩ Hf' ⁻¹' (chartAt H x₀).source
  have hWo : IsOpen (W ×ˢ (univ : Set P)) := hW.prod isOpen_univ
  have hSo : IsOpen S := hH.continuousOn.isOpen_inter_preimage hWo (chartAt H x₀).open_source
  have hFS : ContDiffOn ℝ ∞ F S := by
    have h1 : ContMDiffOn 𝓘(ℝ, (Fin m → ℝ) × P) 𝓘(ℝ, Fin n → ℝ) ∞ F S :=
      (contMDiffOn_extChartAt (I := I) (x := x₀)).comp (hH.mono inter_subset_left)
        (fun q hq => hq.2)
    exact contMDiffOn_iff_contDiffOn.mp h1
  have hq₀ : ((y₀, (0 : P)) : (Fin m → ℝ) × P) ∈ S :=
    ⟨⟨hy₀, mem_univ _⟩, mem_chart_source H x₀⟩
  let D : (Fin m → ℝ) × P → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) := fun q =>
    (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) P)
  have hDc : ContinuousAt D (y₀, 0) :=
    ((hFS.continuousOn_fderiv_of_isOpen hSo (by simp)).continuousAt
      (hSo.mem_nhds hq₀)).clm_comp continuousAt_const
  have hDer : ∀ y w, ((y, w) : (Fin m → ℝ) × P) ∈ S →
      HasFDerivAt (fun y' => F (y', w)) (D (y, w)) y := by
    intro y w hS
    have hd : DifferentiableAt ℝ F (y, w) :=
      ((hFS.differentiableOn (by simp)) _ hS).differentiableAt (hSo.mem_nhds hS)
    exact HasFDerivAt.comp (g := F) y hd.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) y w)
  have hmf : ∀ y w, ((y, w) : (Fin m → ℝ) × P) ∈ S →
      D (y, w) = (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf y w)).comp
        (mfderiv 𝓘(ℝ, Fin m → ℝ) I (fun y' => Hf y' w) y) := by
    intro y w hS
    have hat : ContMDiffAt 𝓘(ℝ, (Fin m → ℝ) × P) I ∞ Hf' (y, w) :=
      hH.contMDiffAt (hWo.mem_nhds hS.1)
    have hpair : ContMDiff 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, (Fin m → ℝ) × P) ∞
        (fun y' : Fin m → ℝ => ((y', w) : (Fin m → ℝ) × P)) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    have hg : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) I (fun y' => Hf y' w) y :=
      ((ContMDiffAt.comp y hat hpair.contMDiffAt).mdifferentiableAt (by simp))
    have hφ : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf y w) :=
      mdifferentiableAt_extChartAt hS.2
    rw [← (hDer y w hS).fderiv]
    have hc := mfderiv_comp y hφ hg
    rw [mfderiv_eq_fderiv] at hc
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hc v
  set L := D (y₀, 0) with hL
  have hLinj : Function.Injective L := by
    rw [hL, hmf y₀ 0 hq₀]
    have hinv := isInvertible_mfderiv_extChartAt (I := I) (x := x₀) (y := x₀)
      (mem_extChartAt_source (I := I) x₀)
    obtain ⟨e, he⟩ := hinv
    have hAinj : Function.Injective
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf y₀ 0)) := by
      rw [← he]; exact e.injective
    intro a b hab
    exact himm (hAinj hab)
  obtain ⟨K, hK0, hanti⟩ := (LinearMap.injective_iff_antilipschitz (L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))).mp hLinj
  have hKpos : (0 : ℝ) < K := hK0
  have hK : ∀ v, ‖v‖ ≤ K * ‖L v‖ := by
    intro v
    have := hanti.le_mul_dist v 0
    simpa [dist_zero_right] using this
  set ε : ℝ := 1 / (2 * K) with hε
  have hεpos : 0 < ε := by positivity
  have hzero : ∀ v : Fin m → ℝ, ‖L v‖ ≤ ε * ‖v‖ → v = 0 := by
    intro v hv
    have h1 := hK v
    have h2 : (K : ℝ) * ‖L v‖ ≤ K * (ε * ‖v‖) := mul_le_mul_of_nonneg_left hv hKpos.le
    have h3 : (K : ℝ) * (ε * ‖v‖) = ‖v‖ / 2 := by
      rw [hε]; field_simp
    have h4 : ‖v‖ ≤ 0 := by linarith [norm_nonneg v]
    exact norm_le_zero_iff.mp h4
  have hev : ∀ᶠ q in 𝓝 ((y₀, (0 : P)) : (Fin m → ℝ) × P), q ∈ S ∧ ‖D q - L‖ < ε := by
    filter_upwards [hSo.mem_nhds hq₀, hDc (Metric.ball_mem_nhds L hεpos)] with q hq hq'
    exact ⟨hq, by simpa [dist_eq_norm] using hq'⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : P) hρ] with w hw
  have hmem : ∀ y ∈ Metric.ball y₀ ρ, ((y, w) : (Fin m → ℝ) × P) ∈ Metric.ball (y₀, (0 : P)) ρ := by
    intro y hy
    rw [← ball_prod_same]
    exact ⟨hy, hw⟩
  intro y hy
  obtain ⟨hyS, hyD⟩ := hball _ (hmem y hy)
  refine ⟨?_, ?_⟩
  · have hDinj : Function.Injective (D (y, w)) := by
      intro a b hab
      have hv : D (y, w) (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have : a - b = 0 := by
        apply hzero
        have : L (a - b) = (L - D (y, w)) (a - b) := by
          simp [hv]
        rw [this]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right hyD.le (norm_nonneg _)
      exact sub_eq_zero.mp this
    have hc := hmf y w hyS
    intro a b hab
    apply hDinj
    exact (DFunLike.congr_fun hc a).trans ((congrArg
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf y w)) hab).trans
        (DFunLike.congr_fun hc b).symm)
  · intro y' hy' heq
    have hmv : ‖(F (y', w) - L y') - (F (y, w) - L y)‖ ≤ ε * ‖y' - y‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun z => F (z, w) - L z) (f' := fun z => D (z, w) - L) ?_ ?_
        (convex_ball y₀ ρ) hy hy'
      · intro z hz
        exact ((hDer z w (hball _ (hmem z hz)).1).sub L.hasFDerivAt).hasFDerivWithinAt
      · intro z hz
        exact (hball _ (hmem z hz)).2.le
    have hFeq : F (y, w) = F (y', w) := by
      simp only [F]; rw [heq]
    have : y' - y = 0 := by
      apply hzero
      rw [map_sub]
      rw [hFeq] at hmv
      have : F (y', w) - L y' - (F (y', w) - L y) = -(L y' - L y) := by abel
      rw [this, norm_neg] at hmv
      exact hmv
    exact (sub_eq_zero.mp this).symm

omit [I.Boundaryless] in
theorem eventually_isInjImmersionOn {m : ℕ} {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {W : Set (Fin m → ℝ)} (hW : IsOpen W)
    {Hf : (Fin m → ℝ) → P → M}
    (hH : ContMDiffOn 𝓘(ℝ, (Fin m → ℝ) × P) I ∞ (fun q : (Fin m → ℝ) × P => Hf q.1 q.2)
      (W ×ˢ univ))
    {Q : Set (Fin m → ℝ)} (hQ : IsCompact Q) (hQW : Q ⊆ W)
    (hemb : isInjImmersionOn I (fun y => Hf y 0) Q) :
    ∀ᶠ w in 𝓝 (0 : P), isInjImmersionOn I (fun y => Hf y w) Q := by
  have hg : ∀ y ∈ W, ContinuousAt (fun q : (Fin m → ℝ) × P => Hf q.1 q.2) (y, 0) := by
    intro y hy
    exact hH.continuousOn.continuousAt (prod_mem_nhds (hW.mem_nhds hy) univ_mem)
  have key : ∀ x ∈ Q ×ˢ Q, ∀ᶠ z in 𝓝 ((0 : P), x),
      Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I (fun y => Hf y z.1) z.2.1) ∧
        (Hf z.2.1 z.1 = Hf z.2.2 z.1 → z.2.1 = z.2.2) := by
    rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    obtain ⟨δ, hδ, hev⟩ :=
      eventually_locallyInjective_of_immersion hW hH (hQW hy₁) (hemb.1 y₁ hy₁)
    have hball : ∀ᶠ x : (Fin m → ℝ) × (Fin m → ℝ) in 𝓝 (y₁, y₂),
        x.1 ∈ Metric.ball y₁ δ := by
      have : Metric.ball y₁ δ ∈ 𝓝 y₁ := Metric.ball_mem_nhds y₁ hδ
      exact (continuous_fst.continuousAt (x := (y₁, y₂))).preimage_mem_nhds this
    have h1 := hev.prod_mk hball
    rw [← nhds_prod_eq] at h1
    by_cases hyy : y₁ = y₂
    · subst hyy
      have hball2 : ∀ᶠ x : (Fin m → ℝ) × (Fin m → ℝ) in 𝓝 (y₁, y₁),
          x.2 ∈ Metric.ball y₁ δ := by
        have : Metric.ball y₁ δ ∈ 𝓝 y₁ := Metric.ball_mem_nhds y₁ hδ
        exact (continuous_snd.continuousAt (x := (y₁, y₁))).preimage_mem_nhds this
      have h2 := (Filter.Eventually.of_forall (fun _ => trivial) : ∀ᶠ _w in 𝓝 (0 : P), True).prod_mk hball2
      rw [← nhds_prod_eq] at h2
      filter_upwards [h1, h2] with z hz1 hz2
      exact ⟨(hz1.1 z.2.1 hz1.2).1, fun heq => (hz1.1 z.2.1 hz1.2).2 z.2.2 hz2.2 heq⟩
    · have hc : ContinuousAt (fun z : P × ((Fin m → ℝ) × (Fin m → ℝ)) =>
          (Hf z.2.1 z.1, Hf z.2.2 z.1)) ((0 : P), (y₁, y₂)) := by
        refine ContinuousAt.prodMk ?_ ?_
        · exact (hg y₁ (hQW hy₁)).comp (x := ((0 : P), (y₁, y₂)))
            (f := fun z : P × ((Fin m → ℝ) × (Fin m → ℝ)) => (z.2.1, z.1)) (by fun_prop)
        · exact (hg y₂ (hQW hy₂)).comp (x := ((0 : P), (y₁, y₂)))
            (f := fun z : P × ((Fin m → ℝ) × (Fin m → ℝ)) => (z.2.2, z.1)) (by fun_prop)
      have hoff : (Hf y₁ 0, Hf y₂ 0) ∈ (Set.diagonal M)ᶜ := by
        intro h
        exact hyy (hemb.2 hy₁ hy₂ h)
      have h2 := hc.preimage_mem_nhds (isClosed_diagonal.isOpen_compl.mem_nhds hoff)
      filter_upwards [h1, h2] with z hz1 hz2
      refine ⟨(hz1.1 z.2.1 hz1.2).1, fun heq => ?_⟩
      exact absurd heq hz2
  have hall := (hQ.prod hQ).eventually_forall_of_forall_eventually
    (P := fun (w : P) (x : (Fin m → ℝ) × (Fin m → ℝ)) =>
      Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I (fun y => Hf y w) x.1) ∧
        (Hf x.1 w = Hf x.2 w → x.1 = x.2)) key
  filter_upwards [hall] with w hw
  refine ⟨fun y hy => (hw (y, y) ⟨hy, hy⟩).1, ?_⟩
  intro y hy y' hy' heq
  exact (hw (y, y') ⟨hy, hy'⟩).2 heq

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem exists_whitney_perturbation_family (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {W : Set (Fin 2 → ℝ)} (hW : IsOpen W) {h : (Fin 2 → ℝ) → M}
    (hsm : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h W) (hlev : ∀ y ∈ W, f (h y) = c)
    (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source)
    (hψs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target)
    (hψf : ∀ y ∈ ψ.source, f (ψ y) = c + y i₀)
    {C N : Set (Fin 2 → ℝ)} (hC : IsCompact C) (hN : IsOpen N) (hCN : C ⊆ N)
    (hNc : IsCompact (closure N)) (hNW : closure N ⊆ W)
    (hNψ : ∀ y ∈ closure N, h y ∈ ψ.target)
    {𝒪 : Set ((Fin 2 → ℝ) × M)} (h𝒪 : IsOpen 𝒪) (hgraph : ∀ y ∈ W, (y, h y) ∈ 𝒪) :
    ∃ (Hf : (Fin 2 → ℝ) → (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) → M) (β : (Fin 2 → ℝ) → ℝ)
      (A : Set (Fin 2 → ℝ)) (r : ℝ), 0 < r ∧
      ContMDiffOn 𝓘(ℝ, (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ))) I ∞
        (fun q : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) => Hf q.1 q.2) (W ×ˢ univ) ∧
      (∀ y, Hf y 0 = h y) ∧ (∀ y ∈ W, ∀ w, f (Hf y w) = c) ∧
      (∀ y w, y ∉ N → Hf y w = h y) ∧
      (∀ w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ), ‖w‖ < r → ∀ y ∈ W, (y, Hf y w) ∈ 𝒪) ∧
      (∀ w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ), ‖w‖ < r → ∀ y, h y ∈ ψ.target →
        Hf y w ∈ ψ.target ∧
        ψ.symm (Hf y w) = ψ.symm (h y) + β y • levelProj i₀ (w.1 + ∑ k, y k • w.2 k)) ∧
      ContDiff ℝ ∞ β ∧ IsOpen A ∧ C ⊆ A ∧ A ⊆ N ∧ EqOn β 1 A ∧ (∀ y, y ∉ N → β y = 0) := by
  classical
  have _hf := hf
  obtain ⟨B, hBo, hCB, hBN⟩ := normal_exists_closure_subset hC.isClosed hN hCN
  obtain ⟨A, hAo, hCA, hAB⟩ := normal_exists_closure_subset hC.isClosed hBo hCB
  obtain ⟨β, hβ, -, hβ0, hβ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞))
    hBo.isClosed_compl (isClosed_closure (s := A))
    (Set.disjoint_left.mpr (fun x hx1 hx2 => hx1 (hAB hx2)))
  have hβO : ∀ y, y ∉ closure B → β y = 0 := fun y hy =>
    (hβ0 y).1 (fun hyB => hy (subset_closure hyB))
  have hβN : ∀ y, y ∉ N → β y = 0 := fun y hy => hβO y (fun hyB => hy (hBN hyB))
  have hβA : EqOn β 1 A := fun y hy => (hβ1 y).1 (subset_closure hy)
  have hAN : A ⊆ N := subset_closure.trans (hAB.trans (subset_closure.trans hBN))
  let Φ : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) → (Fin n → ℝ) :=
    fun p => ψ.symm (h p.1) + β p.1 • levelProj i₀ (p.2.1 + ∑ k, p.1 k • p.2.2 k)
  have hlp0 : ∀ x : Fin n → ℝ, levelProj i₀ x i₀ = 0 := by
    intro x
    simp [levelProj]
  have hΦ0 : ∀ y, Φ (y, 0) = ψ.symm (h y) := by
    intro y
    simp [Φ, levelProj]
  have hlp : ContDiff ℝ ∞ (levelProj i₀ : (Fin n → ℝ) → Fin n → ℝ) := by
    unfold levelProj
    exact contDiff_id.sub ((contDiff_apply ℝ ℝ i₀).smul contDiff_const)
  have hL : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) =>
      levelProj i₀ (p.2.1 + ∑ k, p.1 k • p.2.2 k)) := by
    refine hlp.comp ?_
    refine (contDiff_fst.comp contDiff_snd).add ?_
    refine ContDiff.sum (fun k _ => ?_)
    exact ((contDiff_apply ℝ ℝ k).comp contDiff_fst).smul
      ((contDiff_apply ℝ (Fin n → ℝ) k).comp (contDiff_snd.comp contDiff_snd))
  set W' : Set (Fin 2 → ℝ) := W ∩ h ⁻¹' ψ.target with hW'_def
  have hW' : IsOpen W' := hsm.continuousOn.isOpen_inter_preimage hW ψ.open_target
  have hgd : ContDiffOn ℝ ∞ (fun y => ψ.symm (h y)) W' := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hψs.comp (hsm.mono inter_subset_left) (fun y hy => hy.2)
  have hΦ : ContDiffOn ℝ ∞ Φ (W' ×ˢ univ) := by
    have h1 : ContDiffOn ℝ ∞
        (fun p : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) => ψ.symm (h p.1))
        (W' ×ˢ univ) := hgd.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
    exact h1.add ((hβ.comp contDiff_fst).smul hL).contDiffOn
  let F : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) → (Fin 2 → ℝ) × M :=
    fun p => (p.1, ψ (Φ p))
  have hS1 : IsOpen ((W' ×ˢ univ) ∩ Φ ⁻¹' ψ.source) :=
    hΦ.continuousOn.isOpen_inter_preimage (hW'.prod isOpen_univ) ψ.open_source
  have hFc : ContinuousOn F ((W' ×ˢ univ) ∩ Φ ⁻¹' ψ.source) :=
    continuous_fst.continuousOn.prodMk
      (hψ.continuousOn.comp (hΦ.continuousOn.mono inter_subset_left) (fun p hp => hp.2))
  have hS : IsOpen (((W' ×ˢ univ) ∩ Φ ⁻¹' ψ.source) ∩ F ⁻¹' 𝒪) :=
    hFc.isOpen_inter_preimage hS1 h𝒪
  obtain ⟨u, v, -, hv, hNu, h0v, huv⟩ := generalized_tube_lemma hNc
    (isCompact_singleton (x := (0 : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ)))) hS (by
      rintro ⟨y, w⟩ ⟨hy, hw⟩
      rw [mem_singleton_iff] at hw
      subst hw
      have hyt := hNψ y hy
      refine ⟨⟨⟨⟨hNW hy, hyt⟩, trivial⟩, ?_⟩, ?_⟩
      · change Φ (y, 0) ∈ ψ.source
        rw [hΦ0]
        exact ψ.map_target hyt
      · change (y, ψ (Φ (y, 0))) ∈ 𝒪
        rw [hΦ0, ψ.right_inv hyt]
        exact hgraph y (hNW hy))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  let lam : ContDiffBump (0 : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) :=
    ⟨ε / 2, ε, by positivity, by linarith⟩
  let σ : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) → (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) :=
    fun w => lam w • w
  have hσc : ContDiff ℝ ∞ σ := (lam.contDiff (n := ⊤)).smul contDiff_id
  have hσ0 : σ 0 = 0 := smul_zero _
  have hσv : ∀ w, σ w ∈ v := by
    intro w
    by_cases hw : ‖w‖ < ε
    · apply hball
      rw [mem_ball_zero_iff]
      change ‖lam w • w‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg lam.nonneg]
      calc lam w * ‖w‖ ≤ 1 * ‖w‖ :=
            mul_le_mul_of_nonneg_right lam.le_one (norm_nonneg _)
        _ < ε := by rw [one_mul]; exact hw
    · have hl : lam w = 0 := by
        rw [← Function.notMem_support, lam.support_eq]
        intro hm
        exact hw (mem_ball_zero_iff.mp hm)
      change lam w • w ∈ v
      rw [hl, zero_smul]
      exact h0v rfl
  have hσr : ∀ w : (Fin n → ℝ) × (Fin 2 → Fin n → ℝ), ‖w‖ < ε / 2 → σ w = w := by
    intro w hw
    change lam w • w = w
    rw [lam.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hw.le), one_smul]
  have hSmem : ∀ y ∈ closure N, ∀ w, Φ (y, σ w) ∈ ψ.source ∧ (y, ψ (Φ (y, σ w))) ∈ 𝒪 :=
    fun y hy w => by
      have hm := huv (show (y, σ w) ∈ u ×ˢ v from ⟨hNu hy, hσv w⟩)
      exact ⟨hm.1.2, hm.2⟩
  have hsym0 : ∀ y ∈ W, h y ∈ ψ.target → ψ.symm (h y) i₀ = 0 := by
    intro y hy hyt
    have e := hψf _ (ψ.map_target hyt)
    rw [ψ.right_inv hyt, hlev y hy] at e
    linarith
  let Hf : (Fin 2 → ℝ) → (Fin n → ℝ) × (Fin 2 → Fin n → ℝ) → M :=
    fun y w => if y ∈ N then ψ (Φ (y, σ w)) else h y
  refine ⟨Hf, β, A, ε / 2, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, hβ, hAo, hCA, hAN, hβA, hβN⟩
  · rintro ⟨y, w⟩ ⟨hy, -⟩
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hyN : y ∈ N
    · have hs := (hSmem y (subset_closure hyN) w).1
      have hyW' : y ∈ W' := ⟨hNW (subset_closure hyN), hNψ y (subset_closure hyN)⟩
      have hGat : ContDiffAt ℝ ∞
          (fun q : (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)) => Φ (q.1, σ q.2))
          (y, w) := by
        have h1 : ContDiffAt ℝ ∞ Φ (y, σ w) :=
          hΦ.contDiffAt ((hW'.prod isOpen_univ).mem_nhds ⟨hyW', trivial⟩)
        exact h1.comp (y, w) (contDiff_fst.prodMk (hσc.comp contDiff_snd)).contDiffAt
      have hψat : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ ψ (Φ (y, σ w)) :=
        hψ.contMDiffAt (ψ.open_source.mem_nhds hs)
      have hcomp := hψat.comp (y, w) (contMDiffAt_iff_contDiffAt.mpr hGat)
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [(hN.prod isOpen_univ).mem_nhds (show (y, w) ∈ N ×ˢ (univ : Set _) from
        ⟨hyN, trivial⟩)] with q hq
      simp only [Hf, hq.1, ↓reduceIte]
      rfl
    · have hyB : y ∉ closure B := fun hyB => hyN (hBN hyB)
      have hhat : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) I ∞ h y := hsm.contMDiffAt (hW.mem_nhds hy)
      have hcomp := hhat.comp (y, w)
        (contMDiffAt_iff_contDiffAt.mpr
          (contDiff_fst (E := Fin 2 → ℝ) (F := (Fin n → ℝ) × (Fin 2 → Fin n → ℝ))).contDiffAt)
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_closure.isOpen_compl.prod isOpen_univ).mem_nhds
        (show (y, w) ∈ (closure B)ᶜ ×ˢ (univ : Set _) from ⟨hyB, trivial⟩)] with q hq
      by_cases hqN : q.1 ∈ N
      · simp only [Hf, hqN, ↓reduceIte, Function.comp]
        have hΦq : Φ (q.1, σ q.2) = ψ.symm (h q.1) := by
          simp only [Φ, hβO q.1 hq.1, zero_smul, add_zero]
        rw [hΦq, ψ.right_inv (hNψ q.1 (subset_closure hqN))]
      · simp only [Hf, hqN, ↓reduceIte, Function.comp]
  · intro y
    by_cases hyN : y ∈ N
    · simp only [Hf, hyN, ↓reduceIte]
      rw [hσ0, hΦ0, ψ.right_inv (hNψ y (subset_closure hyN))]
    · simp only [Hf, hyN, ↓reduceIte]
  · intro y hy w
    by_cases hyN : y ∈ N
    · simp only [Hf, hyN, ↓reduceIte]
      have hs := (hSmem y (subset_closure hyN) w).1
      rw [hψf _ hs]
      have hy0 := hsym0 y hy (hNψ y (subset_closure hyN))
      simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlp0, mul_zero, add_zero, hy0]
    · simp only [Hf, hyN, ↓reduceIte]
      exact hlev y hy
  · intro y w hy
    simp only [Hf, hy, ↓reduceIte]
  · intro w _ y hy
    by_cases hyN : y ∈ N
    · simp only [Hf, hyN, ↓reduceIte]
      exact (hSmem y (subset_closure hyN) w).2
    · simp only [Hf, hyN, ↓reduceIte]
      exact hgraph y hy
  · intro w hw y hyt
    by_cases hyN : y ∈ N
    · simp only [Hf, hyN, ↓reduceIte]
      have hs := (hSmem y (subset_closure hyN) w).1
      rw [hσr w hw] at hs ⊢
      exact ⟨ψ.map_source hs, ψ.left_inv hs⟩
    · simp only [Hf, hyN, ↓reduceIte]
      exact ⟨hyt, by rw [hβN y hyN, zero_smul, add_zero]⟩

omit [I.Boundaryless] in
theorem exists_whitney_cell_step (h6 : 6 ≤ n) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {W : Set (Fin 2 → ℝ)} (hW : IsOpen W) {h : (Fin 2 → ℝ) → M}
    (hsm : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h W) (hlev : ∀ y ∈ W, f (h y) = c)
    {Q : Set (Fin 2 → ℝ)} (hQ : IsCompact Q) (hQW : Q ⊆ W) (hemb : isInjImmersionOn I h Q)
    (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source)
    (hψs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target)
    (hψf : ∀ y ∈ ψ.source, f (ψ y) = c + y i₀)
    {C N : Set (Fin 2 → ℝ)} (hC : IsCompact C) (hN : IsOpen N) (hCN : C ⊆ N)
    (hNc : IsCompact (closure N)) (hNW : closure N ⊆ W)
    (hNψ : ∀ y ∈ closure N, h y ∈ ψ.target) {T : Set M} {d : ℕ}
    (hT : IndexOnePartner.isThin I d T) (hd : d + 3 < n)
    {𝒪 : Set ((Fin 2 → ℝ) × M)} (h𝒪 : IsOpen 𝒪) (hgraph : ∀ y ∈ W, (y, h y) ∈ 𝒪) :
    ∃ h' : (Fin 2 → ℝ) → M, ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h' W ∧
      (∀ y ∈ W, f (h' y) = c) ∧ (∀ y, y ∉ N → h' y = h y) ∧ (∀ y ∈ W, (y, h' y) ∈ 𝒪) ∧
      isInjImmersionOn I h' (Q ∪ C) ∧ ∀ y ∈ C, h' y ∉ T := by
  classical
  obtain ⟨Hf, β, A, r, hr, hH, hH0, hHlev, hHoff, hH𝒪, hHψ, hβ, hA, hCA, hAN, hβA, -⟩ :=
    exists_whitney_perturbation_family hf hW hsm hlev ψ i₀ hψ hψs hψf hC hN hCN hNc hNW hNψ h𝒪
      hgraph
  have hemb0 : isInjImmersionOn I (fun y => Hf y 0) Q := by
    have hfun : (fun y => Hf y 0) = h := funext hH0
    rw [hfun]
    exact hemb
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.eventually_nhds_iff_ball.1 (eventually_isInjImmersionOn hW hH hQ hQW hemb0)
  obtain ⟨ι, hι, U, g, hU, hg, hTcov⟩ := hT
  have hY : IsOpen (W ∩ h ⁻¹' ψ.target) :=
    hsm.continuousOn.isOpen_inter_preimage hW ψ.open_target
  have hG₀ : ContDiffOn ℝ ∞ (fun y => ψ.symm (h y)) (W ∩ h ⁻¹' ψ.target) := by
    have h1 : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (ψ.symm ∘ h)
        (W ∩ h ⁻¹' ψ.target) :=
      hψs.comp (hsm.mono inter_subset_left) (fun y hy => hy.2)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hAY : A ⊆ W ∩ h ⁻¹' ψ.target := fun y hy =>
    ⟨hNW (subset_closure (hAN hy)), hNψ y (subset_closure (hAN hy))⟩
  have hU' : ∀ i, IsOpen (U i ∩ g i ⁻¹' ψ.target) := fun i =>
    (hg i).continuousOn.isOpen_inter_preimage (hU i) ψ.open_target
  have hg' : ∀ i, ContDiffOn ℝ 1 (fun u => ψ.symm (g i u)) (U i ∩ g i ⁻¹' ψ.target) := by
    intro i
    have h1 : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (ψ.symm ∘ g i)
        (U i ∩ g i ⁻¹' ψ.target) :=
      (hψs.of_le (by exact_mod_cast le_top)).comp ((hg i).mono inter_subset_left) (fun u hu => hu.2)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hdim := dimH_whitney_bad_params_lt h6 i₀ hY hA hAY hG₀ hβ hβA hd hU' hg'
  obtain ⟨w, hwB, hwball⟩ := (dense_compl_of_dimH_lt_finrank hdim).exists_mem_open
    Metric.isOpen_ball (Metric.nonempty_ball.2 (lt_min hr hε))
  have hwn : ‖w‖ < min r ε := mem_ball_zero_iff.1 hwball
  have hwr : ‖w‖ < r := lt_of_lt_of_le hwn (min_le_left _ _)
  have hwQ : isInjImmersionOn I (fun y => Hf y w) Q :=
    hεsub w (mem_ball_zero_iff.2 (lt_of_lt_of_le hwn (min_le_right _ _)))
  have hwB1 : ∀ y ∈ A, Function.Injective (fderiv ℝ (fun y' => ψ.symm (h y') +
      β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) y) := by
    intro y hy
    by_contra hni
    exact hwB (Or.inl (Or.inl ⟨y, hy, hni⟩))
  have hwB2 : ∀ y ∈ A, ∀ y' ∈ W ∩ h ⁻¹' ψ.target, y' ≠ y →
      ψ.symm (h y) + β y • levelProj i₀ (w.1 + ∑ k, y k • w.2 k) ≠
        ψ.symm (h y') + β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k) := by
    intro y hy y' hy' hne heq
    exact hwB (Or.inl (Or.inr ⟨y, hy, y', hy', hne, heq⟩))
  have hwB3 : ∀ y ∈ A, ∀ i, ∀ u ∈ U i ∩ g i ⁻¹' ψ.target,
      ψ.symm (h y) + β y • levelProj i₀ (w.1 + ∑ k, y k • w.2 k) ≠ ψ.symm (g i u) := by
    intro y hy i u hu heq
    exact hwB (Or.inr ⟨y, hy, i, u, hu, heq⟩)
  have hchart := fun y (hy : h y ∈ ψ.target) => hHψ w hwr y hy
  have hsmooth : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ (fun y => Hf y w) W := by
    have hpair : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ((Fin n → ℝ) × (Fin 2 → Fin n → ℝ)))
        ∞ (fun y : Fin 2 → ℝ => (y, w)) W :=
      contMDiffOn_iff_contDiffOn.2 ((contDiff_id.prodMk contDiff_const).contDiffOn)
    exact hH.comp hpair (fun y hy => ⟨hy, mem_univ _⟩)
  refine ⟨fun y => Hf y w, hsmooth, fun y hy => hHlev y hy w, fun y hy => hHoff y w hy,
    fun y hy => hH𝒪 w hwr y hy, ⟨?_, ?_⟩, ?_⟩
  · rintro y (hyQ | hyC)
    · exact hwQ.1 y hyQ
    · have hyA := hCA hyC
      have hyW : y ∈ W := (hAY hyA).1
      have hev : (ψ.symm ∘ fun y' => Hf y' w) =ᶠ[𝓝 y] (fun y' => ψ.symm (h y') +
          β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) := by
        filter_upwards [hA.mem_nhds hyA] with y' hy'
        exact (hchart y' (hAY hy').2).2
      have hHd : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I (fun y' => Hf y' w) y :=
        (hsmooth.contMDiffAt (hW.mem_nhds hyW)).mdifferentiableAt (by simp)
      have hψd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) ψ.symm (Hf y w) :=
        (hψs.contMDiffAt (ψ.open_target.mem_nhds (hchart y (hAY hyA).2).1)).mdifferentiableAt
          (by simp)
      have hcomp := mfderiv_comp y hψd hHd
      have h2 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin n → ℝ) (ψ.symm ∘ fun y' => Hf y' w) y =
          fderiv ℝ (fun y' => ψ.symm (h y') +
            β y' • levelProj i₀ (w.1 + ∑ k, y' k • w.2 k)) y := by
        rw [mfderiv_eq_fderiv]
        exact hev.fderiv_eq
      rw [h2] at hcomp
      intro a b hab
      apply hwB1 y hyA
      rw [hcomp]
      exact congrArg (mfderiv I 𝓘(ℝ, Fin n → ℝ) ψ.symm (Hf y w)) hab
  · have key : ∀ y ∈ C, ∀ y' ∈ Q ∪ C, Hf y w = Hf y' w → y = y' := by
      intro y hyC y' hy' heq
      by_contra hne
      have hyA := hCA hyC
      have hy'W : y' ∈ W := hy'.elim (fun h' => hQW h') (fun h' => (hAY (hCA h')).1)
      obtain ⟨hmem, hφ⟩ := hchart y (hAY hyA).2
      by_cases ht : h y' ∈ ψ.target
      · obtain ⟨-, hφ'⟩ := hchart y' ht
        apply hwB2 y hyA y' ⟨hy'W, ht⟩ (fun e => hne e.symm)
        rw [← hφ, ← hφ', heq]
      · have hy'N : y' ∉ N := fun hN' => ht (hNψ y' (subset_closure hN'))
        rw [hHoff y' w hy'N] at heq
        exact ht (heq ▸ hmem)
    rintro y1 hy1 y2 hy2 heq
    rcases hy1 with hy1Q | hy1C
    · rcases hy2 with hy2Q | hy2C
      · exact hwQ.2 hy1Q hy2Q heq
      · exact (key y2 hy2C y1 (Or.inl hy1Q) heq.symm).symm
    · exact key y1 hy1C y2 hy2 heq
  · intro y hyC hyT
    obtain ⟨i, u, hu, hgu⟩ : ∃ i, ∃ u ∈ U i, g i u = Hf y w := by
      simpa only [mem_iUnion, mem_image] using hTcov hyT
    have hyA := hCA hyC
    obtain ⟨hmem, hφ⟩ := hchart y (hAY hyA).2
    apply hwB3 y hyA i u ⟨hu, show g i u ∈ ψ.target from hgu ▸ hmem⟩
    rw [← hφ, hgu]

omit [I.Boundaryless] in
theorem exists_whitney_cells (h6 : 6 ≤ n) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {T : Set M} (hTc : IsClosed T) {d : ℕ} (hT : IndexOnePartner.isThin I d T) (hd : d + 3 < n)
    {W : Set (Fin 2 → ℝ)} (hW : IsOpen W) {m : ℕ} (C N : Fin m → Set (Fin 2 → ℝ))
    (ψ : Fin m → OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin m → Fin n)
    (hψ : ∀ j, ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ (ψ j) (ψ j).source)
    (hψs : ∀ j, ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ (ψ j).symm (ψ j).target)
    (hψf : ∀ j, ∀ y ∈ (ψ j).source, f (ψ j y) = c + y (i₀ j))
    (hC : ∀ j, IsCompact (C j)) (hN : ∀ j, IsOpen (N j)) (hCN : ∀ j, C j ⊆ N j)
    (hNc : ∀ j, IsCompact (closure (N j))) (hNW : ∀ j, closure (N j) ⊆ W)
    {h : (Fin 2 → ℝ) → M} (hsm : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h W)
    (hlev : ∀ y ∈ W, f (h y) = c) {Q : Set (Fin 2 → ℝ)} (hQ : IsCompact Q) (hQW : Q ⊆ W)
    (hemb : isInjImmersionOn I h Q) {𝒪 : Set ((Fin 2 → ℝ) × M)} (h𝒪 : IsOpen 𝒪)
    (hgraph : ∀ y ∈ W, (y, h y) ∈ 𝒪)
    (h𝒪ψ : ∀ j, ∀ p ∈ 𝒪, p.1 ∈ closure (N j) → p.2 ∈ (ψ j).target) :
    ∃ h' : (Fin 2 → ℝ) → M, ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h' W ∧
      (∀ y ∈ W, f (h' y) = c) ∧ (∀ y, (∀ j, y ∉ N j) → h' y = h y) ∧
      (∀ y ∈ W, (y, h' y) ∈ 𝒪) ∧ isInjImmersionOn I h' (Q ∪ ⋃ j, C j) ∧
      ∀ j, ∀ y ∈ C j, h' y ∉ T := by
  induction m generalizing h Q 𝒪 with
  | zero =>
    refine ⟨h, hsm, hlev, fun _ _ => rfl, hgraph, ?_, fun j => j.elim0⟩
    have hset : Q ∪ ⋃ j : Fin 0, C j = Q := by
      simp
    rw [hset]
    exact hemb
  | succ k ih =>
    have hNψ0 : ∀ y ∈ closure (N 0), h y ∈ (ψ 0).target := fun y hy =>
      h𝒪ψ 0 (y, h y) (hgraph y (hNW 0 hy)) hy
    obtain ⟨h₁, hsm₁, hlev₁, hout₁, hgraph₁, hemb₁, havoid₁⟩ :=
      exists_whitney_cell_step h6 hf hW hsm hlev hQ hQW hemb (ψ 0) (i₀ 0) (hψ 0) (hψs 0)
        (hψf 0) (hC 0) (hN 0) (hCN 0) (hNc 0) (hNW 0) hNψ0 hT hd h𝒪 hgraph
    have hC0W : C 0 ⊆ W := (hCN 0).trans (subset_closure.trans (hNW 0))
    set 𝒪' : Set ((Fin 2 → ℝ) × M) :=
      𝒪 ∩ (Prod.fst ⁻¹' (C 0)ᶜ ∪ Prod.snd ⁻¹' Tᶜ) with h𝒪'_def
    have h𝒪' : IsOpen 𝒪' :=
      h𝒪.inter (((hC 0).isClosed.isOpen_compl.preimage continuous_fst).union
        (hTc.isOpen_compl.preimage continuous_snd))
    have hgraph' : ∀ y ∈ W, (y, h₁ y) ∈ 𝒪' := by
      intro y hy
      refine ⟨hgraph₁ y hy, ?_⟩
      by_cases hyC : y ∈ C 0
      · exact Or.inr (havoid₁ y hyC)
      · exact Or.inl hyC
    have h𝒪ψ' : ∀ j : Fin k, ∀ p ∈ 𝒪', p.1 ∈ closure (N j.succ) → p.2 ∈ (ψ j.succ).target :=
      fun j p hp hp1 => h𝒪ψ j.succ p hp.1 hp1
    obtain ⟨h', hsm', hlev', hout', hgraph'', hemb', havoid'⟩ :=
      ih (fun j => C j.succ) (fun j => N j.succ) (fun j => ψ j.succ) (fun j => i₀ j.succ)
        (fun j => hψ j.succ) (fun j => hψs j.succ) (fun j => hψf j.succ) (fun j => hC j.succ)
        (fun j => hN j.succ) (fun j => hCN j.succ) (fun j => hNc j.succ) (fun j => hNW j.succ)
        hsm₁ hlev₁ (hQ.union (hC 0)) (union_subset hQW hC0W) hemb₁ h𝒪' hgraph' h𝒪ψ'
    refine ⟨h', hsm', hlev', ?_, fun y hy => (hgraph'' y hy).1, ?_, ?_⟩
    · intro y hy
      rw [hout' y (fun j => hy j.succ)]
      exact hout₁ y (hy 0)
    · have hsub : Q ∪ ⋃ j : Fin (k + 1), C j ⊆ (Q ∪ C 0) ∪ ⋃ j : Fin k, C j.succ := by
        intro y hy
        rcases hy with hy | hy
        · exact Or.inl (Or.inl hy)
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
          cases j using Fin.cases with
          | zero => exact Or.inl (Or.inr hj)
          | succ j => exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
      exact ⟨fun y hy => hemb'.1 y (hsub hy), hemb'.2.mono hsub⟩
    · intro j
      cases j using Fin.cases with
      | zero =>
        intro y hy
        have hmem := (hgraph'' y (hC0W hy)).2
        rcases hmem with hm | hm
        · exact absurd hy hm
        · exact hm
      | succ j => exact havoid' j

theorem exists_whitney_generic_position (h6 : 6 ≤ n) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {W : Set (Fin 2 → ℝ)} (hW : IsOpen W) {h : (Fin 2 → ℝ) → M}
    (hsm : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h W) (hlev : ∀ y ∈ W, f (h y) = c)
    (hreg : ∀ y ∈ W, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f (h y)) {Q K U : Set (Fin 2 → ℝ)} (hQ : IsCompact Q)
    (hQW : Q ⊆ W) (hemb : isInjImmersionOn I h Q) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUW : U ⊆ W) {T : Set M} (hTc : IsClosed T) {d : ℕ}
    (hT : IndexOnePartner.isThin I d T) (hd : d + 3 < n)
    {𝒪 : Set ((Fin 2 → ℝ) × M)} (h𝒪 : IsOpen 𝒪) (hgraph : ∀ y ∈ W, (y, h y) ∈ 𝒪) :
    ∃ h' : (Fin 2 → ℝ) → M, ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ h' W ∧
      (∀ y ∈ W, f (h' y) = c) ∧ (∀ y, y ∉ U → h' y = h y) ∧ (∀ y ∈ W, (y, h' y) ∈ 𝒪) ∧
      isInjImmersionOn I h' (Q ∪ K) ∧ ∀ y ∈ K, h' y ∉ T := by
  classical
  have hch : ∀ y : Fin 2 → ℝ, y ∈ U → ∃ (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n),
      h y ∈ ψ.target ∧ ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source ∧
      ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, f (ψ z) = c + z i₀ := by
    intro y hy
    obtain ⟨ψ, i₀, r, hr, hball, hψ0, hψ, hψs, hψf⟩ :=
      IndexOnePartner.exists_levelChart hf (hreg y (hUW hy))
    refine ⟨ψ, i₀, ?_, hψ, hψs, ?_⟩
    · rw [← hψ0]
      exact ψ.map_source (hball (Metric.mem_ball_self hr))
    · intro z hz
      rw [hψf z hz, hlev y (hUW hy)]
  choose ψf i₀f hψft hψf hψfs hψff using hch
  have hcontU : ContinuousOn h U := (hsm.continuousOn).mono hUW
  let G : (Fin 2 → ℝ) → Set (Fin 2 → ℝ) := fun y =>
    if hy : y ∈ U then U ∩ h ⁻¹' (ψf y hy).target else univ
  have hG : ∀ y, IsOpen (G y) ∧ y ∈ G y := by
    intro y
    by_cases hy : y ∈ U
    · simp only [G, hy, ↓reduceDIte]
      exact ⟨hcontU.isOpen_inter_preimage hU (ψf y hy).open_target, hy, hψft y hy⟩
    · simp only [G, hy, ↓reduceDIte]
      exact ⟨isOpen_univ, mem_univ _⟩
  obtain ⟨m, C, N, x, hC, hN, hCN, hNc, hNU, hNG, -, hxK, hKC⟩ :=
    IndexOnePartner.exists_small_cells (F := id) continuous_id G hG hK hU hKU one_pos
  have hxU : ∀ j, x j ∈ U := by
    intro j
    obtain ⟨z, hz, hzx⟩ := hxK j
    rw [← hzx]
    exact hKU hz.1
  have hNG' : ∀ j, closure (N j) ⊆ U ∩ h ⁻¹' (ψf (x j) (hxU j)).target := by
    intro j z hz
    have h1 := hNG j (mem_image_of_mem id hz)
    simp only [G, hxU j, ↓reduceDIte, id] at h1
    exact h1
  let 𝒪' : Set ((Fin 2 → ℝ) × M) :=
    𝒪 ∩ ⋂ j, {p | p.1 ∈ closure (N j) → p.2 ∈ (ψf (x j) (hxU j)).target}
  have h𝒪' : IsOpen 𝒪' := by
    refine h𝒪.inter (isOpen_iInter_of_finite fun j => ?_)
    have heq : {p : (Fin 2 → ℝ) × M | p.1 ∈ closure (N j) → p.2 ∈ (ψf (x j) (hxU j)).target} =
        ((closure (N j))ᶜ ×ˢ univ) ∪ (univ ×ˢ (ψf (x j) (hxU j)).target) := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_prod, mem_compl_iff, mem_univ, and_true,
        true_and]
      tauto
    rw [heq]
    exact (isClosed_closure.isOpen_compl.prod isOpen_univ).union
      (isOpen_univ.prod (ψf (x j) (hxU j)).open_target)
  have hgraph' : ∀ y ∈ W, (y, h y) ∈ 𝒪' := by
    intro y hy
    refine ⟨hgraph y hy, mem_iInter.2 fun j => ?_⟩
    intro hyN
    exact (hNG' j hyN).2
  have h𝒪ψ : ∀ j, ∀ p ∈ 𝒪', p.1 ∈ closure (N j) → p.2 ∈ (ψf (x j) (hxU j)).target := by
    intro j p hp hp1
    exact (mem_iInter.1 hp.2 j) hp1
  obtain ⟨h', hsm', hlev', hfix, hgr', hemb', havoid⟩ :=
    exists_whitney_cells h6 hf hTc hT hd hW C N (fun j => ψf (x j) (hxU j))
      (fun j => i₀f (x j) (hxU j)) (fun j => hψf (x j) (hxU j)) (fun j => hψfs (x j) (hxU j))
      (fun j => hψff (x j) (hxU j)) hC hN hCN hNc (fun j => (hNU j).trans hUW) hsm hlev hQ hQW
      hemb h𝒪' hgraph' h𝒪ψ
  have hKsub : K ⊆ ⋃ j, C j := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKC hy)
    exact mem_iUnion.2 ⟨j, interior_subset hj⟩
  refine ⟨h', hsm', hlev', ?_, fun y hy => (hgr' y hy).1, ?_, ?_⟩
  · intro y hy
    refine hfix y fun j hyN => hy ?_
    exact hNU j (subset_closure hyN)
  · have hsub : Q ∪ K ⊆ Q ∪ ⋃ j, C j := union_subset_union_right Q hKsub
    exact ⟨fun y hy => hemb'.1 y (hsub hy), hemb'.2.mono hsub⟩
  · intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKsub hy)
    exact havoid j y hj

theorem exists_levelField_chartDir (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ} {m : ℕ}
    {φ : (Fin m → ℝ) → M} {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (hφ : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ φ U)
    (himm : ∀ z ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ z)) (hinj : InjOn φ U)
    (hlev : ∀ z ∈ U, f (φ z) = c) (hreg : ∀ z ∈ U, mfderiv I 𝓘(ℝ, ℝ) f (φ z) ≠ 0)
    (hopen : ∀ V ⊆ U, IsOpen V → ∃ G : Set M, IsOpen G ∧ φ '' V = G ∩ f ⁻¹' {c})
    (e : Fin m → ℝ) {K : Set (Fin m → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (X : LevelField I f) (V : Set (Fin m → ℝ)), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ z ∈ V, X.Y (φ z) = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ z e := by
  classical
  have hloc : ∀ z₀ ∈ U, ∃ (O : Set M) (Y : (x : M) → TangentSpace I x), IsOpen O ∧ φ z₀ ∈ O ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) O ∧
      (∀ x ∈ O, dfV I f Y x = 0) ∧
      ∀ w ∈ U, φ w ∈ O → Y (φ w) = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ w e := by
    intro z₀ hz₀
    obtain ⟨ψ, i₀, r, hr, hball, hψ0, hψs, hψis, hψf⟩ :=
      IndexOnePartner.exists_levelChart hf (x₀ := φ z₀) (hreg z₀ hz₀)
    have hfx₀ : f (φ z₀) = c := hlev z₀ hz₀
    set D : Set (Fin m → ℝ) := U ∩ φ ⁻¹' ψ.target with hDdef
    have hDo : IsOpen D := hφ.continuousOn.isOpen_inter_preimage hU ψ.open_target
    have hz₀D : z₀ ∈ D :=
      ⟨hz₀, by rw [mem_preimage, ← hψ0]; exact ψ.map_source (hball (Metric.mem_ball_self hr))⟩
    have hDU : D ⊆ U := inter_subset_left
    set g : (Fin m → ℝ) → (Fin n → ℝ) := fun w => ψ.symm (φ w) with hgdef
    have hgs : ContDiffOn ℝ ∞ g D :=
      contMDiffOn_iff_contDiffOn.1 (hψis.comp (hφ.mono hDU) (fun w hw => hw.2))
    have hgd : ∀ w ∈ D, HasFDerivAt g (fderiv ℝ g w) w := fun w hw =>
      ((hgs.contDiffAt (hDo.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
    have hg0 : ∀ w ∈ D, g w i₀ = 0 := by
      intro w hw
      have h1 := hψf (g w) (ψ.map_target hw.2)
      rw [ψ.right_inv hw.2, hlev w hw.1, hfx₀] at h1
      linarith
    have hgi₀ : ∀ w ∈ D, ∀ a, fderiv ℝ g w a i₀ = 0 := by
      intro w hw a
      have h1 : HasFDerivAt (fun w => g w i₀)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀).comp (fderiv ℝ g w)) w :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀).hasFDerivAt.comp w (hgd w hw)
      have h2 : HasFDerivAt (fun w => g w i₀) (0 : (Fin m → ℝ) →L[ℝ] ℝ) w :=
        (hasFDerivAt_const (0 : ℝ) w).congr_of_eventuallyEq
          (Filter.eventually_of_mem (hDo.mem_nhds hw) fun w' hw' => hg0 w' hw')
      have := congrArg (fun L : (Fin m → ℝ) →L[ℝ] ℝ => L a) (h1.unique h2)
      simpa using this
    have hψd : ∀ y ∈ ψ.source, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I ψ y := fun y hy =>
      (hψs.contMDiffAt (ψ.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    have hdφ : ∀ w ∈ D, ∀ a, mfderiv 𝓘(ℝ, Fin m → ℝ) I φ w a =
        mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (g w) (fderiv ℝ g w a) := by
      intro w hw a
      have h1 : HasMFDerivAt 𝓘(ℝ, Fin m → ℝ) I (ψ ∘ g) w
          ((mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (g w)).comp (fderiv ℝ g w)) :=
        (hψd (g w) (ψ.map_target hw.2)).hasMFDerivAt.comp w (hgd w hw).hasMFDerivAt
      have h2 : HasMFDerivAt 𝓘(ℝ, Fin m → ℝ) I φ w
          ((mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (g w)).comp (fderiv ℝ g w)) :=
        h1.congr_of_eventuallyEq (Filter.eventually_of_mem (hDo.mem_nhds hw) fun w' hw' =>
          (ψ.right_inv hw'.2).symm)
      rw [h2.mfderiv]
      rfl
    set A : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) := fderiv ℝ g z₀ with hAdef
    have hAinj : Function.Injective A := by
      intro a b hab
      apply himm z₀ hz₀
      rw [hdφ z₀ hz₀D a, hdφ z₀ hz₀D b]
      exact congrArg _ hab
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    have : CompleteSpace ((Fin m → ℝ) × C) := FiniteDimensional.complete ℝ _
    set Gf : (Fin m → ℝ) × C → (Fin n → ℝ) := fun p => g p.1 + (p.2 : Fin n → ℝ) with hGfdef
    set Lp : (Fin m → ℝ) × C → ((Fin m → ℝ) × C →L[ℝ] (Fin n → ℝ)) := fun p =>
      (fderiv ℝ g p.1).comp (ContinuousLinearMap.fst ℝ _ _) +
        C.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _) with hLpdef
    have hGd : ∀ p : (Fin m → ℝ) × C, p.1 ∈ D → HasFDerivAt Gf (Lp p) p := by
      intro p hp
      exact ((hgd p.1 hp).comp p (hasFDerivAt_fst)).add
        (C.subtypeL.hasFDerivAt.comp p hasFDerivAt_snd)
    have hD' : IsOpen (Prod.fst ⁻¹' D : Set ((Fin m → ℝ) × C)) := hDo.preimage continuous_fst
    have hGs : ContDiffOn ℝ ∞ Gf (Prod.fst ⁻¹' D) :=
      (hgs.comp contDiff_fst.contDiffOn (fun p hp => hp)).add
        (C.subtypeL.contDiff.comp contDiff_snd).contDiffOn
    have hbij : Function.Bijective (Lp (z₀, 0)) := by
      constructor
      · intro p q hpq
        have h1 : A (p.1 - q.1) = -((p.2 : Fin n → ℝ) - q.2) := by
          simp only [hLpdef, add_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
            Submodule.subtypeL_apply] at hpq
          rw [map_sub]
          change fderiv ℝ g z₀ p.1 + _ = fderiv ℝ g z₀ q.1 + _ at hpq
          linear_combination hpq
        have h2 : A (p.1 - q.1) ∈ LinearMap.range (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⊓ C := by
          refine ⟨⟨p.1 - q.1, rfl⟩, ?_⟩
          rw [h1]
          exact C.neg_mem (C.sub_mem p.2.2 q.2.2)
        rw [hC.inf_eq_bot, Submodule.mem_bot] at h2
        have h3 : p.1 = q.1 := sub_eq_zero.1 (hAinj (by rw [h2, map_zero]))
        have h4 : (p.2 : Fin n → ℝ) = q.2 := by
          rw [h2, eq_comm, neg_eq_zero, sub_eq_zero] at h1
          exact h1
        exact Prod.ext h3 (Subtype.ext h4)
      · intro y
        have hy : y ∈ LinearMap.range (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⊔ C := by
          rw [hC.sup_eq_top]; trivial
        obtain ⟨a, ⟨b, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hy
        exact ⟨(b, ⟨u, hu⟩), rfl⟩
    set Le : ((Fin m → ℝ) × C) ≃L[ℝ] (Fin n → ℝ) :=
      (LinearEquiv.ofBijective ((Lp (z₀, 0)) : ((Fin m → ℝ) × C) →ₗ[ℝ] (Fin n → ℝ))
        hbij).toContinuousLinearEquiv with hLedef
    have hLe : (Le : ((Fin m → ℝ) × C) →L[ℝ] (Fin n → ℝ)) = Lp (z₀, 0) := by
      exact ContinuousLinearMap.ext fun p => rfl
    have hz₀D' : ((z₀, (0 : C)) : (Fin m → ℝ) × C) ∈ Prod.fst ⁻¹' D := hz₀D
    have hGc₀ : ContDiffAt ℝ ∞ Gf (z₀, 0) := hGs.contDiffAt (hD'.mem_nhds hz₀D')
    have hGd₀ : HasFDerivAt Gf (Le : ((Fin m → ℝ) × C) →L[ℝ] (Fin n → ℝ)) (z₀, 0) := by
      rw [hLe]; exact hGd _ hz₀D
    set P := hGc₀.toOpenPartialHomeomorph Gf hGd₀ (by simp) with hPdef
    have hPcoe : (P : (Fin m → ℝ) × C → (Fin n → ℝ)) = Gf := rfl
    have hz₀P : ((z₀, (0 : C)) : (Fin m → ℝ) × C) ∈ P.source :=
      hGc₀.mem_toOpenPartialHomeomorph_source hGd₀ (by simp)
    set S : Set ((Fin m → ℝ) × C) := P.source ∩ (Prod.fst ⁻¹' D ∩
      (fun p => fderiv ℝ Gf p) ⁻¹' range
        (ContinuousLinearEquiv.toContinuousLinearMap (R₁ := ℝ) (R₂ := ℝ)
          (M₁ := (Fin m → ℝ) × C) (M₂ := Fin n → ℝ))) with hSdef
    have hSo : IsOpen S := P.open_source.inter
      ((hGs.continuousOn_fderiv_of_isOpen hD' (by simp)).isOpen_inter_preimage hD'
        ContinuousLinearEquiv.isOpen)
    have hz₀S : ((z₀, (0 : C)) : (Fin m → ℝ) × C) ∈ S :=
      ⟨hz₀P, hz₀D', ⟨Le, (hGd₀.fderiv).symm⟩⟩
    set T : Set (Fin n → ℝ) := P '' S with hTdef
    have hTo : IsOpen T := P.isOpen_image_of_subset_source hSo inter_subset_left
    have hPT : ∀ y ∈ T, P.symm y ∈ S ∧ y ∈ P.target := by
      rintro _ ⟨p, hp, rfl⟩
      rw [P.left_inv hp.1]
      exact ⟨hp, P.map_source hp.1⟩
    have hPsymm : ContDiffOn ℝ ∞ P.symm T := by
      intro y hy
      obtain ⟨hyS, hyt⟩ := hPT y hy
      obtain ⟨L, hL⟩ := hyS.2.2
      refine (P.contDiffAt_symm (f₀' := L) hyt ?_ ?_).contDiffWithinAt
      · rw [hL]
        exact (hGs.contDiffAt (hD'.mem_nhds hyS.2.1)).differentiableAt (by simp) |>.hasFDerivAt
      · exact hGs.contDiffAt (hD'.mem_nhds hyS.2.1)
    set N : Set (Fin m → ℝ) := {w | ((w, (0 : C)) : (Fin m → ℝ) × C) ∈ S} with hNdef
    have hNo : IsOpen N := hSo.preimage (continuous_id.prodMk continuous_const)
    have hND : N ⊆ D := fun w hw => hw.2.1
    obtain ⟨Gs, hGso, hGseq⟩ := hopen N (hND.trans hDU) hNo
    set O₁ : Set M := ψ.target ∩ ψ.symm ⁻¹' T with hO₁def
    have hO₁o : IsOpen O₁ := ψ.isOpen_inter_preimage_symm hTo
    set v : M → (Fin n → ℝ) := fun x => fderiv ℝ g (P.symm (ψ.symm x)).1 e with hvdef
    have hfd : ContDiffOn ℝ ∞ (fun w => fderiv ℝ g w e) D :=
      (hgs.fderiv_of_isOpen hDo (by simp)).clm_apply contDiffOn_const
    have hvT : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g (P.symm y).1 e) T :=
      hfd.comp (contDiff_fst.comp_contDiffOn hPsymm) (fun y hy => (hPT y hy).1.2.1)
    have hv : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ v O₁ :=
      (contMDiffOn_iff_contDiffOn.2 hvT).comp (hψis.mono inter_subset_left) (fun x hx => hx.2)
    have hPw : ∀ w ∈ N, P.symm (g w) = (w, 0) := by
      intro w hw
      have h1 : P (w, 0) = g w := by
        rw [hPcoe]; simp [hGfdef]
      rw [← h1, P.left_inv hw.1]
    refine ⟨O₁ ∩ Gs, fun x => (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (ψ.symm x) (v x) : TangentSpace I x),
      hO₁o.inter hGso, ?_, ?_, ?_, ?_⟩
    · refine ⟨⟨hz₀D.2, ?_⟩, ?_⟩
      · refine ⟨(z₀, 0), hz₀S, ?_⟩
        rw [hPcoe]; simp [hGfdef, hgdef]
      · have h1 : φ z₀ ∈ φ '' N := ⟨z₀, hz₀S, rfl⟩
        rw [hGseq] at h1
        exact h1.1
    · have h1 := hψs.contMDiffOn_tangentMapWithin (m := ∞) (by simp) ψ.open_source.uniqueMDiffOn
      have h2 : ContMDiffOn I (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x =>
          (⟨ψ.symm x, v x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ))) O₁ := by
        intro x hx
        rw [Bundle.contMDiffWithinAt_totalSpace]
        refine ⟨(hψis.mono inter_subset_left) x hx, ?_⟩
        simp only [mfld_simps]
        exact hv x hx
      refine ((h1.comp h2 ?_).congr ?_).mono inter_subset_left
      · intro x hx
        exact ψ.map_target hx.1
      · intro x hx
        have hs : ψ.symm x ∈ ψ.source := ψ.map_target hx.1
        simp only [Function.comp, tangentMapWithin, mfderivWithin_of_isOpen ψ.open_source hs]
        exact Bundle.TotalSpace.ext (ψ.right_inv hx.1).symm HEq.rfl
    · intro x hx
      set y := ψ.symm x with hydef
      have hy : y ∈ ψ.source := ψ.map_target hx.1.1
      have hxy : ψ y = x := ψ.right_inv hx.1.1
      have hwD : (P.symm y).1 ∈ D := (hPT _ hx.1.2).1.2.1
      have hcomp : HasMFDerivAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (f ∘ ψ) y
          ((mfderiv I 𝓘(ℝ, ℝ) f (ψ y)).comp (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ y)) :=
        (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp y (hψd y hy).hasMFDerivAt
      have hlin : HasMFDerivAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (f ∘ ψ) y
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀) := by
        have h1 : HasFDerivAt (fun y : Fin n → ℝ => f (φ z₀) + y i₀)
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀) y :=
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀).hasFDerivAt.const_add _
        exact h1.hasMFDerivAt.congr_of_eventuallyEq
          (Filter.eventually_of_mem (ψ.open_source.mem_nhds hy) fun y' hy' => hψf y' hy')
      have heq := hcomp.mfderiv.symm.trans hlin.mfderiv
      have h2 : mfderiv I 𝓘(ℝ, ℝ) f (ψ y) (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ y (v x)) = 0 :=
        (congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (v x)) heq).trans (hgi₀ _ hwD e)
      unfold dfV
      change NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ, ℝ) f x
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ y (v x))) = 0
      rw [← hxy] at h2 ⊢
      rw [h2]
      simp
    · intro w hw hwO
      have h1 : φ w ∈ φ '' N := by
        rw [hGseq]; exact ⟨hwO.2, hlev w hw⟩
      obtain ⟨w', hw'N, hw'⟩ := h1
      have hww' : w' = w := hinj (hDU (hND hw'N)) hw hw'
      subst hww'
      have hPw' := hPw w' hw'N
      change mfderiv 𝓘(ℝ, Fin n → ℝ) I ψ (g w') (fderiv ℝ g (P.symm (g w')).1 e) = _
      rw [hPw', hdφ w' (hND hw'N) e]
  have hloc' : ∀ z : Fin m → ℝ, ∃ (O : Set M) (Y : (x : M) → TangentSpace I x), IsOpen O ∧
      (z ∈ U → φ z ∈ O) ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) O ∧
      (∀ x ∈ O, dfV I f Y x = 0) ∧
      ∀ w ∈ U, φ w ∈ O → Y (φ w) = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ w e := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨O, Y, h1, h2, h3, h4, h5⟩ := hloc z hz
      exact ⟨O, Y, h1, fun _ => h2, h3, h4, h5⟩
    · exact ⟨∅, fun _ => 0, isOpen_empty, fun h => absurd h hz, contMDiffOn_empty,
        fun x hx => absurd hx (notMem_empty x), fun w _ hw => absurd hw (notMem_empty _)⟩
  choose O Y hO hzO hYs hYl hYe using hloc'
  have hKc : IsCompact (φ '' K) := hK.image_of_continuousOn (hφ.continuousOn.mono hKU)
  obtain ⟨t, χ, hχs, -, hχc, hχO, -, -, hχ1⟩ := exists_finite_smoothPartition (I := I) hKc hO
    (by rintro _ ⟨z, hz, rfl⟩; exact mem_iUnion.2 ⟨z, hzO z (hKU hz)⟩)
  have hZ : ∀ z, ∃ Z : LevelField I f, ∀ x, Z.Y x = χ z x • Y z x := fun z =>
    LevelField.exists_smul_of_contMDiffOn (hO z) (hYs z) (hYl z) (hχs z) (hχc z) (hχO z)
  choose Z hZ using hZ
  obtain ⟨X, hX⟩ := LevelField.exists_sum_smul t (χ := fun _ _ => (1 : ℝ))
    (fun _ _ => contMDiff_const) Z
  obtain ⟨S, hSo, hKS, hS1⟩ := mem_nhdsSet_iff_exists.1 hχ1
  refine ⟨X, U ∩ φ ⁻¹' S, hφ.continuousOn.isOpen_inter_preimage hU hSo,
    fun z hz => ⟨hKU hz, hKS ⟨z, hz, rfl⟩⟩, inter_subset_left, ?_⟩
  rintro z ⟨hzU, hzS⟩
  rw [hX]
  have hterm : ∀ i ∈ t, (1 : ℝ) • (Z i).Y (φ z) =
      χ i (φ z) • (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ z e : TangentSpace I (φ z)) := by
    intro i _
    rw [one_smul, hZ]
    by_cases h : φ z ∈ tsupport (χ i)
    · rw [hYe i z hzU (hχO i h)]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_smul, zero_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, hS1 hzS, one_smul]

theorem LevelField.flow_eq_of_chartDir (X : LevelField I f) {m : ℕ} {φ : (Fin m → ℝ) → M}
    {V : Set (Fin m → ℝ)} (hV : IsOpen V) (hφ : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ φ V)
    {e : Fin m → ℝ} (hX : ∀ z ∈ V, X.Y (φ z) = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ z e)
    {z : Fin m → ℝ} {s : ℝ} (hseg : ∀ τ ∈ uIcc 0 s, z + τ • e ∈ V) :
    X.flow s (φ z) = φ (z + s • e) := by
  classical
  have hAo : IsOpen {τ : ℝ | z + τ • e ∈ V} :=
    hV.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨δ, hδ, hδA⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := s)).exists_thickening_subset_open
    hAo (fun τ hτ => hseg τ hτ)
  have hab : min 0 s ≤ max 0 s := min_le_max
  have hIoo : Ioo (min 0 s - δ) (max 0 s + δ) ⊆ {τ : ℝ | z + τ • e ∈ V} := by
    intro τ hτ
    apply hδA
    rw [Metric.mem_thickening_iff]
    refine ⟨max (min 0 s) (min τ (max 0 s)), ?_, ?_⟩
    · rw [uIcc]
      exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
    · rw [Real.dist_eq, abs_sub_lt_iff]
      obtain ⟨h1, h2⟩ := hτ
      constructor <;> rcases max_cases (min 0 s) (min τ (max 0 s)) with h | h <;>
        rcases min_cases τ (max 0 s) with h' | h' <;> linarith [h.1, h'.1]
  have hγ : IsMIntegralCurveOn (fun τ : ℝ => φ (z + τ • e)) X.Y (Ioo (min 0 s - δ) (max 0 s + δ)) := by
    intro τ hτ
    have hw : z + τ • e ∈ V := hIoo hτ
    have hφd : HasMFDerivAt 𝓘(ℝ, Fin m → ℝ) I φ (z + τ • e)
        (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ (z + τ • e)) :=
      ((hφ.contMDiffAt (hV.mem_nhds hw)).mdifferentiableAt (by simp)).hasMFDerivAt
    have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin m → ℝ) (fun τ : ℝ => z + τ • e) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight e) := by
      have h0 : HasFDerivAt (fun τ : ℝ => z + τ • e) ((1 : ℝ →L[ℝ] ℝ).smulRight e) τ := by
        have h1 := (((hasDerivAt_id τ).smul_const e).const_add z).hasFDerivAt
        simp only [id, one_smul] at h1
        exact h1
      exact hasMFDerivAt_iff_hasFDerivAt.mpr h0
    have hc := hφd.comp τ hlin
    have heq : (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ (z + τ • e)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight e) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (X.Y (φ (z + τ • e))) := by
      rw [hX _ hw]
      ext
      simp only [ContinuousLinearMap.comp_apply]
      refine (congrArg (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ (z + τ • e))
        (show ((1 : ℝ →L[ℝ] ℝ).smulRight e) 1 = e by simp)).trans ?_
      simp
    exact (hc.congr_mfderiv heq).hasMFDerivWithinAt
  have hflow : IsMIntegralCurveOn (fun τ : ℝ => X.flow τ (φ z)) X.Y
      (Ioo (min 0 s - δ) (max 0 s + δ)) :=
    (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X.Y _ (φ z)).isMIntegralCurveOn _
  have h0 : (0 : ℝ) ∈ Ioo (min 0 s - δ) (max 0 s + δ) :=
    ⟨by linarith [min_le_left (0 : ℝ) s], by linarith [le_max_left (0 : ℝ) s]⟩
  have hs : s ∈ Ioo (min 0 s - δ) (max 0 s + δ) :=
    ⟨by linarith [min_le_right (0 : ℝ) s], by linarith [le_max_right (0 : ℝ) s]⟩
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) 1 (fun x => (⟨x, X.Y x⟩ : TangentBundle I M)) :=
    X.smooth.of_le (by norm_num)
  have hEq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0 hv1 hflow hγ
    (by
      simp only [zero_smul, add_zero]
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero X.Y _ (φ z))
  exact hEq hs

theorem LevelField.comp_flow (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X : LevelField I f) (t : ℝ)
    (x : M) : f (X.flow t x) = f x := by
  obtain ⟨-, hlev, -⟩ := flowChart_spec (d := 0) (r := 1) (m := 1) hf rfl ![X]
    (fun _ => x) (Ω := Set.univ) isOpen_univ contMDiffOn_const
  have h := hlev ![t]
  have heq : flowChart 0 1 ![X] (fun _ => x) (m := 1) ![t] = X.flow t x := by
    simp [flowChart, coordN, List.finRange_succ]
  rw [heq] at h
  exact h

theorem LevelField.eventually_flow_eq_of_chartDir (X : LevelField I f) {m : ℕ}
    {φ : (Fin m → ℝ) → M} {V : Set (Fin m → ℝ)} (hV : IsOpen V)
    (hφ : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ φ V) {e : Fin m → ℝ}
    (hX : ∀ z ∈ V, X.Y (φ z) = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ z e) {z₀ : Fin m → ℝ} (hz₀ : z₀ ∈ V) :
    ∀ᶠ p : (Fin m → ℝ) × ℝ in 𝓝 (z₀, 0),
      p.1 + p.2 • e ∈ V ∧ X.flow p.2 (φ p.1) = φ (p.1 + p.2 • e) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
  have hc : (0 : ℝ) < r / 2 / (‖e‖ + 1) := by positivity
  have h1 : ∀ᶠ p : (Fin m → ℝ) × ℝ in 𝓝 (z₀, 0), dist p.1 z₀ < r / 2 :=
    (continuous_fst.tendsto (z₀, (0 : ℝ))) (Metric.ball_mem_nhds z₀ (by positivity))
  have h2 : ∀ᶠ p : (Fin m → ℝ) × ℝ in 𝓝 (z₀, 0), dist p.2 0 < r / 2 / (‖e‖ + 1) :=
    (continuous_snd.tendsto (z₀, (0 : ℝ))) (Metric.ball_mem_nhds (0 : ℝ) hc)
  filter_upwards [h1, h2] with p hp1 hp2
  have hseg : ∀ τ ∈ uIcc 0 p.2, p.1 + τ • e ∈ V := by
    intro τ hτ
    apply hball
    rw [Metric.mem_ball]
    have hτ' : |τ| ≤ |p.2| := by
      rcases le_total 0 p.2 with h | h
      · rw [uIcc_of_le h] at hτ
        rw [abs_of_nonneg hτ.1, abs_of_nonneg h]; exact hτ.2
      · rw [uIcc_of_ge h] at hτ
        rw [abs_of_nonpos hτ.2, abs_of_nonpos h]; linarith [hτ.1]
    have hp2' : |p.2| < r / 2 / (‖e‖ + 1) := by
      simpa [Real.dist_eq] using hp2
    have hne : ‖τ • e‖ < r / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have he : 0 ≤ ‖e‖ := norm_nonneg e
      have hlt : |p.2| * (‖e‖ + 1) < r / 2 := by
        rwa [lt_div_iff₀ (by positivity)] at hp2'
      nlinarith [abs_nonneg τ, abs_nonneg p.2]
    calc dist (p.1 + τ • e) z₀ ≤ dist p.1 z₀ + ‖τ • e‖ := by
          rw [dist_eq_norm, dist_eq_norm]
          calc ‖p.1 + τ • e - z₀‖ = ‖(p.1 - z₀) + τ • e‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hp1 hne
      _ = r := by ring
  refine ⟨hseg p.2 right_mem_uIcc, ?_⟩
  exact X.flow_eq_of_chartDir hV hφ hX hseg

theorem LevelField.exists_flow_mem (X : LevelField I f) {γ : ℝ → M} (hγ : Continuous γ)
    {J : Set ℝ} (hJ : IsCompact J) {O : Set M} (hO : IsOpen O) (hJO : ∀ t ∈ J, γ t ∈ O) :
    ∃ η > 0, ∀ t t' : ℝ, t' ∈ J → |t - t'| < η → ∀ s : ℝ, |s| < η → X.flow s (γ t) ∈ O := by
  have hF : Continuous (fun p : ℝ × ℝ => X.flow p.2 (γ p.1)) := by
    have hΦ := (DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X.Y X.smooth X.compact).continuous
    exact hΦ.comp (continuous_snd.prodMk (hγ.comp continuous_fst))
  have hP : IsOpen ((fun p : ℝ × ℝ => X.flow p.2 (γ p.1)) ⁻¹' O) := hO.preimage hF
  have hK : IsCompact (J ×ˢ ({0} : Set ℝ)) := hJ.prod isCompact_singleton
  have hKP : J ×ˢ ({0} : Set ℝ) ⊆ (fun p : ℝ × ℝ => X.flow p.2 (γ p.1)) ⁻¹' O := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    have h0 : X.flow 0 (γ t) = γ t :=
      DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ (γ t)
    simp only [Set.mem_preimage, h0]
    exact hJO t ht
  obtain ⟨δ, hδ, hδP⟩ := hK.exists_thickening_subset_open hP hKP
  refine ⟨δ, hδ, fun t t' ht' htt' s hs => ?_⟩
  have hmem : (t, s) ∈ Metric.thickening δ (J ×ˢ ({0} : Set ℝ)) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(t', 0), ⟨ht', rfl⟩, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt htt' hs
  exact hδP hmem

theorem exists_flowStrip (X : LevelField I f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hinj : InjOn γ (Icc t₀ t₁))
    (hind : ∀ t ∈ Icc t₀ t₁,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I γ t 1 : TangentSpace I (γ t)), X.Y (γ t)]) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ∞ (fun p : Fin 2 → ℝ => X.flow (p 1) (γ (p 0))) ∧
      (∀ (t : ℝ) (v : Fin 2 → ℝ),
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun p : Fin 2 → ℝ => X.flow (p 1) (γ (p 0))) ![t, 0] v =
          v 0 • (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : TangentSpace I (γ t)) + v 1 • X.Y (γ t)) ∧
      ∃ η > 0, isInjImmersionOn I (fun p : Fin 2 → ℝ => X.flow (p 1) (γ (p 0)))
        {p | p 0 ∈ Ioo (t₀ - η) (t₁ + η) ∧ p 1 ∈ Ioo (-η) η} := by
  classical
  set F : (Fin 2 → ℝ) → M := fun p : Fin 2 → ℝ => X.flow (p 1) (γ (p 0)) with hFdef
  let Φ : ℝ × M → M := fun q => X.flow q.1 q.2
  have hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Φ :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport X.Y
      X.smooth X.compact
  have hΦ0 : ∀ x, X.flow 0 x = x := fun x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hΦcurve : ∀ x, IsMIntegralCurve (fun t => X.flow t x) X.Y := fun x =>
    DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ x
  let π₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
  let π₁ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  have hπ₀ : ∀ p, π₀ p = p 0 := fun p => rfl
  have hπ₁ : ∀ p, π₁ p = p 1 := fun p => rfl
  have hγ₀ : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ∞ (fun p : Fin 2 → ℝ => γ (p 0)) :=
    hγ.comp π₀.contMDiff
  have hpairS : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : Fin 2 → ℝ => (π₁ p, γ (p 0))) :=
    π₁.contMDiff.prodMk hγ₀
  have hFeq : F = Φ ∘ fun p : Fin 2 → ℝ => (π₁ p, γ (p 0)) := rfl
  have hFs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ∞ F := by
    rw [hFeq]; exact hΦ.comp hpairS
  have hderiv : ∀ (t : ℝ) (v : Fin 2 → ℝ),
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I F ![t, 0] v =
        v 0 • (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : TangentSpace I (γ t)) + v 1 • X.Y (γ t) := by
    intro t v
    have hpt : (fun p : Fin 2 → ℝ => (π₁ p, γ (p 0))) ![t, 0] = ((0 : ℝ), γ t) := by simp [hπ₁]
    have hpair : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) (𝓘(ℝ, ℝ).prod I)
        (fun p : Fin 2 → ℝ => (π₁ p, γ (p 0))) ![t, 0] :=
      hpairS.mdifferentiableAt (by simp)
    have hΦd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Φ ((0 : ℝ), γ t) :=
      hΦ.mdifferentiable (by simp) _
    rw [hFeq]
    refine (mfderiv_comp_apply_of_eq ![t, 0] hΦd hpair hpt v).trans ?_
    rw [MDifferentiableAt.mfderiv_prod ((π₁.contMDiff (n := 1)).mdifferentiable one_ne_zero _)
      (hγ₀.mdifferentiableAt (by simp))]
    refine (mfderiv_prod_eq_add_apply hΦd).trans ?_
    have h1 : ∀ a : ℝ, (mfderiv 𝓘(ℝ, ℝ) I (fun z => Φ (z, γ t)) 0 a : Fin n → ℝ) =
        a • X.Y (γ t) := by
      intro a
      have := (hΦcurve (γ t) 0).mfderiv
      simp only [Φ]
      rw [this]
      change (1 : ℝ →L[ℝ] ℝ) a • X.Y (X.flow 0 (γ t)) = a • X.Y (γ t)
      rw [hΦ0]
      rfl
    have h2 : (fun z => Φ (0, z)) = id := funext fun z => hΦ0 z
    have h3 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) π₁ ![t, 0] = π₁ := by
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      apply ContinuousLinearMap.ext
      intro w
      rfl
    have h4 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun p : Fin 2 → ℝ => γ (p 0)) ![t, 0] v =
        v 0 • (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : TangentSpace I (γ t)) := by
      have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := hγ.mdifferentiableAt (by simp)
      have hπd : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) π₀ ![t, 0] :=
        (π₀.contMDiff (n := 1)).mdifferentiable one_ne_zero _
      have hq : π₀ ![t, 0] = t := by simp [hπ₀]
      have e1 := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, Fin 2 → ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
        ![t, 0] (hq ▸ hγd) hπd hq v
      have e2 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) π₀ ![t, 0] = π₀ := by
        rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
        apply ContinuousLinearMap.ext
        intro w
        rfl
      change mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (γ ∘ π₀) ![t, 0] v = _
      rw [e1, e2]
      have h5 : ∀ a : ℝ, (mfderiv 𝓘(ℝ, ℝ) I γ t a : Fin n → ℝ) =
          a • (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : Fin n → ℝ) := fun a => by
        rw [← map_smul]
        exact congrArg (fun w : ℝ => (mfderiv 𝓘(ℝ, ℝ) I γ t w : Fin n → ℝ))
          (by simp : a = a • (1 : ℝ))
      rw [hπ₀]
      exact h5 (v 0)
    dsimp only
    rw [h2, mfderiv_id, h3]
    change (show Fin n → ℝ from mfderiv 𝓘(ℝ, ℝ) I (fun z => Φ (z, γ t)) 0 (π₁ v)) +
      (show Fin n → ℝ from
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun p : Fin 2 → ℝ => γ (p 0)) ![t, 0] v) = _
    rw [h1, h4, hπ₁, add_comm]
    rfl
  refine ⟨hFs, hderiv, ?_⟩
  let ι : ℝ → (Fin 2 → ℝ) := fun s => ![s, 0]
  have hι : Continuous ι := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id
    · exact continuous_const
  set K : Set (Fin 2 → ℝ) := ι '' Icc t₀ t₁ with hKdef
  have hK : IsCompact K := isCompact_Icc.image hι
  have hFι : ∀ s, F (ι s) = γ s := fun s => by
    simp only [hFdef, ι, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hΦ0 (γ s)
  have himmK : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I F y) := by
    rintro _ ⟨s, hs, rfl⟩
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have hv' := hv
    simp only [ι] at hv'
    rw [hderiv s v] at hv'
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 (hind s hs) (v 0) (v 1) hv'
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hinjK : InjOn F K := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hss'
    rw [hFι, hFι] at hss'
    rw [hinj hs hs' hss']
  obtain ⟨U, hUo, hKU, -, hinjU, himmU⟩ := exists_injOn_nhds_of_immersion (I := I) isOpen_univ
    ((hFs.of_le (by norm_num)).contMDiffOn) hK (subset_univ _) himmK hinjK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hUo hKU
  have hbox : {p : Fin 2 → ℝ | p 0 ∈ Ioo (t₀ - δ) (t₁ + δ) ∧ p 1 ∈ Ioo (-δ) δ} ⊆ U := by
    rintro p ⟨⟨hp0, hp0'⟩, ⟨hp1, hp1'⟩⟩
    refine hδU (Metric.mem_thickening_iff.2 ⟨ι (max t₀ (min t₁ (p 0))), ⟨_, ⟨le_max_left _ _,
      max_le ht (min_le_left _ _)⟩, rfl⟩, ?_⟩)
    refine (dist_pi_lt_iff hδ).2 fun i => ?_
    fin_cases i
    · simp only [ι, Real.dist_eq]
      change |p 0 - max t₀ (min t₁ (p 0))| < δ
      rw [abs_sub_lt_iff]
      rcases le_total (p 0) t₁ with h | h
      · rw [min_eq_right h]
        rcases le_total t₀ (p 0) with h' | h'
        · rw [max_eq_right h']; constructor <;> linarith
        · rw [max_eq_left h']; constructor <;> linarith
      · rw [min_eq_left h, max_eq_right ht]; constructor <;> linarith
    · simp only [ι, Real.dist_eq]
      change |p 1 - 0| < δ
      rw [sub_zero, abs_lt]
      exact ⟨hp1, hp1'⟩
  exact ⟨δ, hδ, fun y hy => himmU y (hbox hy), hinjU.mono hbox⟩

theorem exists_flowStrip_zero_iff (X : LevelField I f) {γ : ℝ → M} (hγ : Continuous γ)
    {t₀ t₁ : ℝ} {s : ℕ} {G : M → EuclideanSpace ℝ (Fin s)} {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc t₀ t₁, γ t ∈ O)
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O)
    (hG0 : ∀ t ∈ Icc t₀ t₁, G (γ t) = 0)
    (htr : ∀ t ∈ Icc t₀ t₁,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X.Y (γ t)) ≠ 0) :
    ∃ η > 0, ∀ t ∈ Icc t₀ t₁, ∀ s' ∈ Ioo (-η) η,
      X.flow s' (γ t) ∈ O ∧ (G (X.flow s' (γ t)) = 0 ↔ s' = 0) := by
  classical
  have hΦc : Continuous (fun p : ℝ × M => X.flow p.1 p.2) :=
    DifferentialGeometry.Analysis.ODE.continuous_globalFlow_of_compactSupport X.Y X.smooth
      X.compact
  have hΦ0 : ∀ x, X.flow 0 x = x := fun x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hcurve : ∀ x, IsMIntegralCurve (fun t => X.flow t x) X.Y := fun x =>
    DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ x
  let F : ℝ × ℝ → M := fun q => X.flow q.2 (γ q.1)
  have hFc : Continuous F :=
    hΦc.comp (continuous_snd.prodMk (hγ.comp continuous_fst))
  let dG : M → EuclideanSpace ℝ (Fin s) := fun x =>
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G x (X.Y x) : EuclideanSpace ℝ (Fin s))
  have hdG : ContinuousOn dG O :=
    continuousOn_mfderiv_apply hO (hG.of_le (by simp)) X.smooth.continuous.continuousOn
  let W : Set (ℝ × ℝ) := F ⁻¹' O ∩ (fun q : ℝ × ℝ => γ q.1) ⁻¹' O
  have hW : IsOpen W :=
    (hO.preimage hFc).inter (hO.preimage (hγ.comp continuous_fst))
  let Ψ : ℝ × ℝ → ℝ := fun q => inner ℝ (dG (γ q.1)) (dG (F q))
  have hΨ : ContinuousOn Ψ W := by
    refine ContinuousOn.inner ?_ ?_
    · exact hdG.comp (hγ.comp continuous_fst).continuousOn fun q hq => hq.2
    · exact hdG.comp hFc.continuousOn fun q hq => hq.1
  let P : Set (ℝ × ℝ) := W ∩ Ψ ⁻¹' Ioi 0
  have hP : IsOpen P := hΨ.isOpen_inter_preimage hW isOpen_Ioi
  have hsub : Icc t₀ t₁ ×ˢ ({0} : Set ℝ) ⊆ P := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    simp only [mem_singleton_iff] at hz
    subst hz
    have hF : F (t, 0) = γ t := hΦ0 (γ t)
    refine ⟨⟨?_, hγO t ht⟩, ?_⟩
    · change F (t, 0) ∈ O
      rw [hF]; exact hγO t ht
    · change 0 < inner ℝ (dG (γ t)) (dG (F (t, 0)))
      rw [hF, real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.2 (htr t ht)) 2
  obtain ⟨u, v, -, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hP hsub
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hv 0 (h0v rfl)
  have hgood : ∀ t ∈ Icc t₀ t₁, ∀ s' ∈ Ioo (-η) η, (t, s') ∈ P := by
    intro t ht s' hs'
    refine huv ⟨hu ht, hball ?_⟩
    rw [Real.ball_eq_Ioo]
    simpa using hs'
  refine ⟨η, hη, fun t ht s' hs' => ⟨(hgood t ht s' hs').1.1, ?_⟩⟩
  let h : ℝ → ℝ := fun σ => inner ℝ (dG (γ t)) (G (X.flow σ (γ t)))
  have hderiv : ∀ σ ∈ Ioo (-η) η, HasDerivAt h (Ψ (t, σ)) σ := by
    intro σ hσ
    have hmem : X.flow σ (γ t) ∈ O := (hgood t ht σ hσ).1.1
    have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (X.flow σ (γ t)) :=
      ((hG.contMDiffAt (hO.mem_nhds hmem)).mdifferentiableAt (by simp))
    have hc := (hGd.hasMFDerivAt).comp σ (hcurve (γ t) σ)
    have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hc
    have hf : HasDerivAt (G ∘ fun σ' => X.flow σ' (γ t)) (dG (X.flow σ (γ t))) σ := by
      refine hasDerivAt_iff_hasFDerivAt.2 (hfd.congr_fderiv ?_)
      refine ContinuousLinearMap.ext fun a => ?_
      change (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (X.flow σ (γ t)))
          ((show ℝ from a) • (X.Y (X.flow σ (γ t)) : Fin n → ℝ)) =
            (show ℝ from a) • dG (X.flow σ (γ t))
      rw [ContinuousLinearMap.map_smul]
      rfl
    have hi := (hasDerivAt_const σ (dG (γ t))).inner ℝ hf
    have hΨeq : Ψ (t, σ) = inner ℝ (dG (γ t)) (dG (X.flow σ (γ t))) +
        inner ℝ (0 : EuclideanSpace ℝ (Fin s)) ((G ∘ fun σ' => X.flow σ' (γ t)) σ) := by
      rw [inner_zero_left, add_zero]
    rw [hΨeq]
    exact hi
  have hmono : StrictMonoOn h (Ioo (-η) η) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
    · exact fun σ hσ => (hderiv σ hσ).continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Ioo] at hσ
      rw [(hderiv σ hσ).deriv]
      exact (hgood t ht σ hσ).2
  have h0 : h 0 = 0 := by
    simp only [h, hΦ0, hG0 t ht, inner_zero_right]
  have h0mem : (0 : ℝ) ∈ Ioo (-η) η := ⟨by linarith, hη⟩
  constructor
  · intro hz
    have : h s' = h 0 := by
      rw [h0]; simp only [h, hz, inner_zero_right]
    exact hmono.injOn hs' h0mem this
  · rintro rfl
    rw [hΦ0]; exact hG0 t ht

theorem exists_reparamFlowStrip (X : LevelField I f) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hinj : InjOn γ (Icc t₀ t₁))
    (hind : ∀ t ∈ Icc t₀ t₁,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I γ t 1 : TangentSpace I (γ t)), X.Y (γ t)])
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω) {σ τ : (Fin 2 → ℝ) → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ Ω) (hτ : ContDiffOn ℝ ∞ τ Ω)
    (hστ : InjOn (fun y => ![σ y, τ y]) Ω)
    (hστd : ∀ y ∈ Ω, Function.Injective (fderiv ℝ (fun y' : Fin 2 → ℝ => ![σ y', τ y']) y)) :
    ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ (fun y => X.flow (τ y) (γ (σ y))) Ω ∧
      (∀ y ∈ Ω, τ y = 0 → ∀ v : Fin 2 → ℝ,
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun y' => X.flow (τ y') (γ (σ y'))) y v =
          fderiv ℝ σ y v • (mfderiv 𝓘(ℝ, ℝ) I γ (σ y) 1 : TangentSpace I (γ (σ y))) +
            fderiv ℝ τ y v • X.Y (γ (σ y))) ∧
      ∃ η > 0, isInjImmersionOn I (fun y => X.flow (τ y) (γ (σ y)))
        (Ω ∩ {y | σ y ∈ Ioo (t₀ - η) (t₁ + η) ∧ τ y ∈ Ioo (-η) η}) := by
  obtain ⟨hFs, hdF, η, hη, hFimm, hFinj⟩ := exists_flowStrip X hγ ht hinj hind
  set F : (Fin 2 → ℝ) → M := fun p : Fin 2 → ℝ => X.flow (p 1) (γ (p 0)) with hFdef
  set g : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => ![σ y, τ y] with hgdef
  have hfun : (fun y' => X.flow (τ y') (γ (σ y'))) = F ∘ g := by
    funext y'
    simp [hFdef, hgdef]
  have hg : ContDiffOn ℝ ∞ g Ω := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [hgdef] using hσ
    · simpa [hgdef] using hτ
  have hgd : ∀ y ∈ Ω, DifferentiableAt ℝ g y := fun y hy =>
    (hg.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
  have hσd : ∀ y ∈ Ω, DifferentiableAt ℝ σ y := fun y hy =>
    (hσ.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
  have hτd : ∀ y ∈ Ω, DifferentiableAt ℝ τ y := fun y hy =>
    (hτ.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
  have hmg : ∀ y ∈ Ω, mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) g y = fderiv ℝ g y := fun y _ =>
    mfderiv_eq_fderiv
  have hcomp : ∀ y ∈ Ω, mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (F ∘ g) y =
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I F (g y)).comp (fderiv ℝ g y) := by
    intro y hy
    rw [mfderiv_comp y ((hFs (g y)).mdifferentiableAt (by simp))
      (hgd y hy).mdifferentiableAt, hmg y hy]
    rfl
  refine ⟨?_, ?_, η, hη, ?_, ?_⟩
  · rw [hfun]
    exact hFs.comp_contMDiffOn hg.contMDiffOn
  · intro y hy hτ0 v
    rw [hfun, hcomp y hy]
    have hgy : g y = ![σ y, 0] := by simp [hgdef, hτ0]
    have hgv0 : fderiv ℝ g y v 0 = fderiv ℝ σ y v := by
      have h := (hasFDerivAt_pi'.1 (hgd y hy).hasFDerivAt) 0
      have he : (fun x => g x 0) = σ := by
        funext x
        simp [hgdef]
      rw [he] at h
      rw [h.fderiv]
      rfl
    have hgv1 : fderiv ℝ g y v 1 = fderiv ℝ τ y v := by
      have h := (hasFDerivAt_pi'.1 (hgd y hy).hasFDerivAt) 1
      have he : (fun x => g x 1) = τ := by
        funext x
        simp [hgdef]
      rw [he] at h
      rw [h.fderiv]
      rfl
    change mfderiv 𝓘(ℝ, Fin 2 → ℝ) I F (g y) (fderiv ℝ g y v) = _
    rw [hgy, hdF, hgv0, hgv1]
  · intro y hy
    rw [hfun, hcomp y hy.1]
    have hmem : g y ∈ {p : Fin 2 → ℝ | p 0 ∈ Ioo (t₀ - η) (t₁ + η) ∧ p 1 ∈ Ioo (-η) η} := by
      refine ⟨?_, ?_⟩
      · simpa [hgdef] using hy.2.1
      · simpa [hgdef] using hy.2.2
    exact (hFimm (g y) hmem).comp (hστd y hy.1)
  · rw [hfun]
    refine hFinj.comp (hστ.mono inter_subset_left) ?_
    intro y hy
    refine ⟨?_, ?_⟩
    · simpa [hgdef] using hy.2.1
    · simpa [hgdef] using hy.2.2

theorem exists_levelField_at (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {s : ℕ}
    {G : M → EuclideanSpace ℝ (Fin s)} {O S : Set M} (hO : IsOpen O)
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hsub : ∀ z ∈ S, ∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I z,
      mfderiv I 𝓘(ℝ, ℝ) f z v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z v = w)
    {z₀ : M} (hz₀ : mfderiv I 𝓘(ℝ, ℝ) f z₀ ≠ 0) (v₀ : TangentSpace I z₀)
    (hv₀ : mfderiv I 𝓘(ℝ, ℝ) f z₀ v₀ = 0)
    (hv₀G : z₀ ∈ S → mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z₀ v₀ = 0) :
    ∃ Z : LevelField I f, Z.Y z₀ = v₀ ∧ ∀ z ∈ S, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z' (Z.Y z') = 0 := by
  classical
  have gen : ∀ (s' : ℕ) (G' : M → EuclideanSpace ℝ (Fin s')) (N₀ : Set M), N₀ ∈ 𝓝 z₀ →
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s')) ∞ G' N₀ →
      (∀ w : EuclideanSpace ℝ (Fin s'), ∃ v : TangentSpace I z₀,
        mfderiv I 𝓘(ℝ, ℝ) f z₀ v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s')) G' z₀ v = w) →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s')) G' z₀ v₀ = 0 →
      ∃ (k : ℕ) (Ys : Fin k → LevelField I f) (N : Set M), N ∈ 𝓝 z₀ ∧
        (∀ z ∈ N, ∀ j, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s')) G' z ((Ys j).Y z) = 0) ∧
        ∃ c : Fin k → ℝ, ∑ j, c j • (Ys j).Y z₀ = v₀ := by
    intro s' G' N₀ hN₀ hG' hsub' hv'
    let A : (Fin n → ℝ) →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f z₀
    let B : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin s') :=
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s')) G' z₀
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin s') :=
      LinearMap.prod A.toLinearMap B.toLinearMap
    have hL : ∀ v, L v = (A v, B v) := fun v => rfl
    obtain ⟨u, hu⟩ : ∃ u : Fin n → ℝ, A u = 1 := by
      obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin n → ℝ, A u₀ ≠ 0 := by
        by_contra hC
        exact hz₀ (ContinuousLinearMap.ext fun u₀ => by
          by_contra h
          exact hC ⟨u₀, h⟩)
      refine ⟨(A u₀)⁻¹ • u₀, ?_⟩
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀]
    have hsurj : Function.Surjective L := by
      rintro ⟨a, w⟩
      obtain ⟨v', hv1, hv2⟩ := hsub' (w - a • B u)
      let v : Fin n → ℝ := v'
      refine ⟨a • u + v, ?_⟩
      rw [hL]
      have e1 : A (a • u + v) = a := by
        rw [map_add, map_smul, hu]
        rw [show A v = 0 from hv1]; simp
      have e2 : B (a • u + v) = w := by
        rw [map_add, map_smul]
        rw [show B v = w - a • B u from hv2]; abel
      rw [e1, e2]
    have hrank := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod,
      finrank_euclideanSpace_fin, Module.finrank_self, Module.finrank_fin_fun] at hrank
    obtain ⟨Ys, N, hN, htan, hind⟩ := exists_adaptedFields hf
      (k := Module.finrank ℝ L.ker) (s := s') (by omega) G' z₀ ⟨N₀, hN₀, hG'⟩ hz₀ hsub'
    refine ⟨Module.finrank ℝ L.ker, Ys, N, hN, htan, ?_⟩
    let Yv : Fin (Module.finrank ℝ L.ker) → (Fin n → ℝ) := fun j => (Ys j).Y z₀
    have hind' : LinearIndependent ℝ Yv := hind
    have hmem : ∀ j, Yv j ∈ LinearMap.ker L := by
      intro j
      refine LinearMap.mem_ker.2 ?_
      rw [hL (Yv j)]
      have h1 : A (Yv j) = 0 := (Ys j).level z₀
      have h2 : B (Yv j) = 0 := htan z₀ (mem_of_mem_nhds hN) j
      rw [h1, h2]; rfl
    have hspan : Submodule.span ℝ (Set.range Yv) = LinearMap.ker L := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.2 (Set.range_subset_iff.2 hmem)) ?_
      rw [finrank_span_eq_card hind', Fintype.card_fin]
    let w₀ : Fin n → ℝ := v₀
    have hv₀L : w₀ ∈ LinearMap.ker L := by
      refine LinearMap.mem_ker.2 ?_
      rw [hL w₀]
      have h1 : A w₀ = 0 := hv₀
      have h2 : B w₀ = 0 := hv'
      rw [h1, h2]; rfl
    rw [← hspan] at hv₀L
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv₀L
    exact ⟨c, hc⟩
  have tail : ∀ (k : ℕ) (Ys : Fin k → LevelField I f) (W : Set M), IsOpen W → z₀ ∈ W →
      (∀ z ∈ S ∩ W, ∃ N ∈ 𝓝 z, ∀ z' ∈ N, ∀ j,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z' ((Ys j).Y z') = 0) →
      (∃ c : Fin k → ℝ, ∑ j, c j • (Ys j).Y z₀ = v₀) →
      ∃ Z : LevelField I f, Z.Y z₀ = v₀ ∧ ∀ z ∈ S, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z' (Z.Y z') = 0 := by
    rintro k Ys W hW hz₀W htanW ⟨c, hc⟩
    obtain ⟨t, χ, hχs, -, -, hχW, hχt, -, hχ1⟩ :=
      exists_finite_smoothPartition (I := I) (ι := Unit) (K := {z₀}) isCompact_singleton
        (U := fun _ => W) (fun _ => hW)
        (fun x hx => mem_iUnion.2 ⟨(), by rw [mem_singleton_iff.1 hx]; exact hz₀W⟩)
    have hsum : ∀ x, ∑ i ∈ t, χ i x = χ () x := by
      intro x
      rw [Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by rw [hχt i hi]; rfl),
        Fintype.sum_unique]
    have h1 : χ () z₀ = 1 := by
      rw [← hsum]
      exact (hχ1.filter_mono (nhds_le_nhdsSet (mem_singleton z₀))).self_of_nhds
    obtain ⟨Z, hZ⟩ := LevelField.exists_sum_smul (Finset.univ : Finset (Fin k))
      (χ := fun j x => c j * χ () x) (fun j _ => contMDiff_const.mul (hχs ())) Ys
    refine ⟨Z, ?_, ?_⟩
    · rw [hZ, ← hc]
      simp [h1]
    · intro z hz
      by_cases hzt : z ∈ tsupport (χ ())
      · obtain ⟨N, hN, hNt⟩ := htanW z ⟨hz, hχW () hzt⟩
        refine ⟨N, hN, fun z' hz' => ?_⟩
        rw [hZ, map_sum]
        exact Finset.sum_eq_zero fun j _ => by rw [map_smul, hNt z' hz' j, smul_zero]
      · refine ⟨(tsupport (χ ()))ᶜ, (isClosed_tsupport _).isOpen_compl.mem_nhds hzt,
          fun z' hz' => ?_⟩
        have h0 : χ () z' = 0 := image_eq_zero_of_notMem_tsupport hz'
        rw [hZ]
        simp [h0]
  by_cases hz₀S : z₀ ∈ S
  · obtain ⟨k, Ys, N, hN, htan, hc⟩ :=
      gen s G O (hO.mem_nhds (hSO hz₀S)) hG (hsub z₀ hz₀S) (hv₀G hz₀S)
    exact tail k Ys (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN)
      (fun z hz => ⟨N, mem_interior_iff_mem_nhds.1 hz.2, fun z' hz' j => htan z' hz' j⟩) hc
  · obtain ⟨k, Ys, -, -, -, hc⟩ := gen 0 (fun _ => 0) univ univ_mem contMDiffOn_const
      (fun w => ⟨0, map_zero _, by rw [map_zero]; exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) _ _⟩)
      (by rw [mfderiv_const]; rfl)
    exact tail k Ys Sᶜ hS.isOpen_compl hz₀S (fun z hz => absurd hz.1 hz.2) hc

theorem exists_levelField_approx (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {s : ℕ}
    {G : M → EuclideanSpace ℝ (Fin s)} {O S : Set M} (hO : IsOpen O)
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hsub : ∀ z ∈ S, ∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I z,
      mfderiv I 𝓘(ℝ, ℝ) f z v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z v = w)
    {m r : ℕ} {K : Set (Fin m → ℝ)} (hK : IsCompact K) {ψ : (Fin m → ℝ) → M}
    (hψ : ContinuousOn ψ K) (hψi : InjOn ψ K)
    (hreg : ∀ y ∈ K, mfderiv I 𝓘(ℝ, ℝ) f (ψ y) ≠ 0)
    {E : (Fin m → ℝ) → Fin r → (Fin n → ℝ)}
    (hEc : ∀ k, ContinuousOn (fun y => (⟨ψ y, E y k⟩ : TangentBundle I M)) K)
    (hEf : ∀ y ∈ K, ∀ k, mfderiv I 𝓘(ℝ, ℝ) f (ψ y) (E y k) = 0)
    (hEi : ∀ y ∈ K, LinearIndependent ℝ (E y))
    (hEs : ∀ y ∈ K, ∀ v : TangentSpace I (ψ y), mfderiv I 𝓘(ℝ, ℝ) f (ψ y) v = 0 →
      v ∈ Submodule.span ℝ (Set.range (E y)))
    {cf : (Fin m → ℝ) → Fin r → ℝ} (hcf : ContinuousOn cf K)
    (hcfS : ∀ y ∈ K, ψ y ∈ S →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (ψ y) (frameVec E y (cf y)) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ Y : LevelField I f,
      (∀ z ∈ S, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z' (Y.Y z') = 0) ∧
      ∀ y ∈ K, ∃ c' : Fin r → ℝ, Y.Y (ψ y) = frameVec E y c' ∧ ∀ k, |c' k - cf y k| < η := by
  classical
  have hloc : ∀ y₀ ∈ K, ∃ (Z : LevelField I f) (U : Set M), IsOpen U ∧ ψ y₀ ∈ U ∧
      (∀ z ∈ S, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z' (Z.Y z') = 0) ∧
      ∃ c : (Fin m → ℝ) → Fin r → ℝ, ∀ y ∈ K, Z.Y (ψ y) = frameVec E y (c y) ∧
        (ψ y ∈ U → ∀ k, |c y k - cf y k| < η) := by
    intro y₀ hy₀
    have hv₀ : mfderiv I 𝓘(ℝ, ℝ) f (ψ y₀)
        (frameVec E y₀ (cf y₀) : TangentSpace I (ψ y₀)) = 0 := by
      have h := map_sum (mfderiv I 𝓘(ℝ, ℝ) f (ψ y₀)) (fun k => cf y₀ k • E y₀ k) Finset.univ
      refine h.trans (Finset.sum_eq_zero fun k _ => ?_)
      have h2 := (mfderiv I 𝓘(ℝ, ℝ) f (ψ y₀)).map_smul (cf y₀ k) (E y₀ k)
      refine h2.trans ?_
      rw [hEf y₀ hy₀ k, smul_zero]
    obtain ⟨Z, hZ₀, hZS⟩ := exists_levelField_at hf hO hG hS hSO hsub (hreg y₀ hy₀)
      (frameVec E y₀ (cf y₀) : TangentSpace I (ψ y₀)) hv₀ (hcfS y₀ hy₀)
    have hZc : ContinuousOn (fun y => (⟨ψ y, Z.Y (ψ y)⟩ : TangentBundle I M)) K :=
      Z.smooth.continuous.comp_continuousOn hψ
    have hspan : ∀ y ∈ K, Z.Y (ψ y) ∈ Submodule.span ℝ (Set.range (E y)) := by
      intro y hy
      have h := Z.level (ψ y)
      unfold dfV at h
      exact hEs y hy _ h
    obtain ⟨c, hcc, hcE⟩ := exists_continuousOn_frameCoeff (I := I) hψ hEc hEi
      (v := fun y => Z.Y (ψ y)) hZc hspan
    have hc₀ : c y₀ = cf y₀ := by
      have h1 : ∑ k, (c y₀ k - cf y₀ k) • E y₀ k = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact (hcE y₀ hy₀).trans hZ₀
      funext k
      have := Fintype.linearIndependent_iff.1 (hEi y₀ hy₀) _ h1 k
      linarith
    let T : Set (Fin r → ℝ) := ⋂ k, {d | |d k| < η}
    have hT : IsOpen T := isOpen_iInter_of_finite fun k =>
      isOpen_lt (continuous_abs.comp (continuous_apply k)) continuous_const
    obtain ⟨V, hV, hVK⟩ := (continuousOn_iff'.1 (hcc.sub hcf)) T hT
    have hmemV : ∀ y ∈ K, y ∈ V ↔ ∀ k, |c y k - cf y k| < η := by
      intro y hy
      have h2 : y ∈ (c - cf) ⁻¹' T ∩ K ↔ y ∈ V ∩ K := by rw [hVK]
      simp only [Set.mem_inter_iff, Set.mem_preimage, T, Set.mem_iInter, Set.mem_ofPred_eq,
        Pi.sub_apply, hy, and_true] at h2
      exact h2.symm
    refine ⟨Z, (ψ '' (K \ V))ᶜ, ?_, ?_, hZS, c, fun y hy => ⟨(hcE y hy).symm, fun hyU => ?_⟩⟩
    · exact (((hK.diff hV).image_of_continuousOn (hψ.mono sdiff_subset)).isClosed).isOpen_compl
    · rintro ⟨y, ⟨hyK, hyV⟩, hyψ⟩
      have hyy := hψi hyK hy₀ hyψ
      subst hyy
      exact hyV ((hmemV y hyK).2 (fun k => by rw [hc₀, sub_self, abs_zero]; exact hη))
    · have hyV : y ∈ V := by
        by_contra h
        exact hyU ⟨y, ⟨hy, h⟩, rfl⟩
      exact (hmemV y hy).1 hyV
  choose Z U hUo hψU hZS c hc using hloc
  obtain ⟨t, χ, hχs, hχ0, -, hχU, -, -, hχ1⟩ := exists_finite_smoothPartition (I := I)
    (hK.image_of_continuousOn hψ) (U := fun j : K => U j.1 j.2) (fun j => hUo j.1 j.2) (by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_iUnion.2 ⟨⟨y, hy⟩, hψU y hy⟩)
  obtain ⟨Y, hY⟩ := LevelField.exists_sum_smul t (fun j _ => hχs j) (fun j : K => Z j.1 j.2)
  refine ⟨Y, ?_, ?_⟩
  · intro z hz
    choose N hN hNZ using fun j : K => hZS j.1 j.2 z hz
    refine ⟨⋂ j ∈ t, N j, (Filter.biInter_finset_mem t).2 fun j _ => hN j, fun z' hz' => ?_⟩
    rw [hY, map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [map_smul, hNZ j z' (mem_iInter₂.1 hz' j hj), smul_zero]
  · intro y hy
    have h1 : ∑ j ∈ t, χ j (ψ y) = 1 := hχ1.self_of_nhdsSet (ψ y) ⟨y, hy, rfl⟩
    refine ⟨∑ j ∈ t, χ j (ψ y) • c j.1 j.2 y, ?_, fun k => ?_⟩
    · rw [hY]
      simp only [frameVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul,
        mul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hc j.1 j.2 y hy).1, frameVec]
      exact Finset.smul_sum (N := Fin n → ℝ)
    · have hk : (∑ j ∈ t, χ j (ψ y) • c j.1 j.2 y) k - cf y k =
          ∑ j ∈ t, χ j (ψ y) * (c j.1 j.2 y k - cf y k) := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, h1, one_mul]
      rw [hk]
      obtain ⟨j₀, hj₀t, hj₀⟩ : ∃ j ∈ t, 0 < χ j (ψ y) := by
        by_contra hne
        push Not at hne
        have : ∑ j ∈ t, χ j (ψ y) ≤ 0 := Finset.sum_nonpos hne
        linarith
      have hlt : ∀ j, χ j (ψ y) ≠ 0 → |c j.1 j.2 y k - cf y k| < η := by
        intro j hj
        have hmem : ψ y ∈ U j.1 j.2 := hχU j (subset_tsupport _ (Function.mem_support.2 hj))
        exact (hc j.1 j.2 y hy).2 hmem k
      calc |∑ j ∈ t, χ j (ψ y) * (c j.1 j.2 y k - cf y k)|
          ≤ ∑ j ∈ t, |χ j (ψ y) * (c j.1 j.2 y k - cf y k)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ t, χ j (ψ y) * |c j.1 j.2 y k - cf y k| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hχ0 j (ψ y))]
        _ < ∑ j ∈ t, χ j (ψ y) * η := by
          refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, hj₀t, ?_⟩
          · rcases eq_or_ne (χ j (ψ y)) 0 with h0 | h0
            · rw [h0, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hlt j h0).le (hχ0 j (ψ y))
          · exact mul_lt_mul_of_pos_left (hlt j₀ hj₀.ne') hj₀
        _ = η := by rw [← Finset.sum_mul, h1, one_mul]

theorem exists_levelField_along_arc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {s : ℕ} {γ : ℝ → M}
    (hγ : Continuous γ) {t₀ t₁ : ℝ} (hinj : InjOn γ (Icc t₀ t₁))
    (hreg : ∀ t ∈ Icc t₀ t₁, mfderiv I 𝓘(ℝ, ℝ) f (γ t) ≠ 0)
    {G : M → EuclideanSpace ℝ (Fin s)} {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc t₀ t₁, γ t ∈ O)
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O)
    (hsub : ∀ t ∈ Icc t₀ t₁, ∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I (γ t),
      mfderiv I 𝓘(ℝ, ℝ) f (γ t) v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) v = w)
    {e : ℝ → EuclideanSpace ℝ (Fin s)} (he : ContinuousOn e (Icc t₀ t₁)) {η : ℝ} (hη : 0 < η) :
    ∃ Z : LevelField I f, ∀ t ∈ Icc t₀ t₁,
      ‖(show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (Z.Y (γ t))) - e t‖ < η := by
  classical
  have hZex : ∀ t : Icc t₀ t₁, ∃ Z : LevelField I f,
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (Z.Y (γ t)) :
        EuclideanSpace ℝ (Fin s)) = e t := by
    intro t
    obtain ⟨v, hvf, hvG⟩ := hsub t t.2 (e t)
    obtain ⟨Z, hZ, -⟩ := exists_levelField_at (I := I) (f := f) hf (G := G) (O := O)
      (S := (∅ : Set M)) hO hG isClosed_empty (empty_subset O)
      (fun z hz => absurd hz (notMem_empty z)) (hreg t t.2) v hvf
      (fun h => absurd h (notMem_empty _))
    exact ⟨Z, by rw [hZ]; exact hvG⟩
  choose Z hZ using hZex
  have hG1 : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) 1 G O := hG.of_le (by simp)
  have hcont : ∀ i : Icc t₀ t₁, ContinuousOn (fun t' : ℝ =>
      ‖(show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t') ((Z i).Y (γ t'))) - e t'‖)
      (Icc t₀ t₁) := by
    intro i
    have h1 := continuousOn_mfderiv_apply (I := I) hO hG1
      (Y := (Z i).Y) (Z i).smooth.continuous.continuousOn
    have h2 : ContinuousOn (fun t' : ℝ =>
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t') ((Z i).Y (γ t')) :
          EuclideanSpace ℝ (Fin s))) (Icc t₀ t₁) :=
      h1.comp hγ.continuousOn (fun t' ht' => hγO t' ht')
    exact (h2.sub he).norm
  let C : Icc t₀ t₁ → Set ℝ := fun i => Icc t₀ t₁ ∩ (fun t' : ℝ =>
      ‖(show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t') ((Z i).Y (γ t'))) - e t'‖) ⁻¹'
        (Ici η)
  have hCc : ∀ i, IsCompact (C i) := fun i =>
    isCompact_Icc.of_isClosed_subset
      ((hcont i).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  let V : Icc t₀ t₁ → Set M := fun i => (γ '' C i)ᶜ
  have hVo : ∀ i, IsOpen (V i) := fun i => ((hCc i).image hγ).isClosed.isOpen_compl
  have hV : ∀ i : Icc t₀ t₁, ∀ t' ∈ Icc t₀ t₁, γ t' ∈ V i →
      ‖(show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t') ((Z i).Y (γ t'))) - e t'‖ < η := by
    intro i t' ht' hV
    by_contra hlt
    exact hV ⟨t', ⟨ht', le_of_not_gt hlt⟩, rfl⟩
  have hKV : γ '' Icc t₀ t₁ ⊆ ⋃ i, V i := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_iUnion.2 ⟨⟨t, ht⟩, ?_⟩
    rintro ⟨c, ⟨hc, hcη⟩, hγc⟩
    have hct : c = t := hinj hc ht hγc
    subst hct
    have h0 := hZ ⟨c, ht⟩
    simp only [mem_preimage, mem_Ici] at hcη
    have h0' : (show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ c) ((Z ⟨c, ht⟩).Y (γ c))) = e c := h0
    change η ≤ ‖(show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ c) ((Z ⟨c, ht⟩).Y (γ c))) - e c‖ at hcη
    rw [h0', sub_self, norm_zero] at hcη
    linarith
  obtain ⟨T, χ, hχs, hχ0, -, hχV, -, -, hχ1⟩ :=
    exists_finite_smoothPartition (I := I) (isCompact_Icc.image hγ) hVo hKV
  obtain ⟨Y, hY⟩ := LevelField.exists_sum_smul T (fun i _ => hχs i) Z
  refine ⟨Y, fun t ht => ?_⟩
  have hsum1 : ∑ i ∈ T, χ i (γ t) = 1 := hχ1.self_of_nhdsSet (γ t) ⟨t, ht, rfl⟩
  have hexp : (show EuclideanSpace ℝ (Fin s) from
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (Y.Y (γ t))) - e t =
      ∑ i ∈ T, χ i (γ t) • ((show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) ((Z i).Y (γ t))) - e t) := by
    have halg : ∀ a : Icc t₀ t₁ → EuclideanSpace ℝ (Fin s),
        ∑ i ∈ T, χ i (γ t) • a i - e t = ∑ i ∈ T, χ i (γ t) • (a i - e t) := by
      intro a
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum1, one_smul]
    rw [← halg (fun i => (show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) ((Z i).Y (γ t))))]
    rw [hY (γ t), map_sum]
    simp only [map_smul]
    rfl
  rw [hexp]
  refine lt_of_le_of_lt (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ T, ‖χ i (γ t) • ((show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) ((Z i).Y (γ t))) - e t)‖ ≤
        χ i (γ t) * η := by
    intro i _
    rw [norm_smul, Real.norm_of_nonneg (hχ0 i _)]
    rcases eq_or_lt_of_le (hχ0 i (γ t)) with h | h
    · rw [← h]; simp
    · refine mul_le_mul_of_nonneg_left (hV i t ht (hχV i ?_)).le h.le
      exact subset_tsupport _ (ne_of_gt h)
  have hpos : ∃ i ∈ T, 0 < χ i (γ t) := by
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    have : ∑ i ∈ T, χ i (γ t) ≤ 0 := Finset.sum_nonpos hno
    linarith
  obtain ⟨i₀, hi₀, hi₀p⟩ := hpos
  have hlt : ∑ i ∈ T, ‖χ i (γ t) • ((show EuclideanSpace ℝ (Fin s) from
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) ((Z i).Y (γ t))) - e t)‖ <
        ∑ i ∈ T, χ i (γ t) * η := by
    refine Finset.sum_lt_sum hterm ⟨i₀, hi₀, ?_⟩
    rw [norm_smul, Real.norm_of_nonneg (hχ0 i₀ _)]
    exact mul_lt_mul_of_pos_left (hV i₀ t ht (hχV i₀ (subset_tsupport _ (ne_of_gt hi₀p)))) hi₀p
  rwa [← Finset.sum_mul, hsum1, one_mul] at hlt

theorem exists_levelField_arc (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {s : ℕ} (hs : 2 ≤ s)
    {γ : ℝ → M} (hγ : Continuous γ) {t₀ t₁ δ : ℝ} (hδ : 0 < δ) (ht : t₀ + δ < t₁ - δ)
    (hinj : InjOn γ (Icc t₀ t₁)) (hreg : ∀ t ∈ Icc t₀ t₁, mfderiv I 𝓘(ℝ, ℝ) f (γ t) ≠ 0)
    {G : M → EuclideanSpace ℝ (Fin s)} {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc t₀ t₁, γ t ∈ O)
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O)
    (hsub : ∀ t ∈ Icc t₀ t₁, ∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I (γ t),
      mfderiv I 𝓘(ℝ, ℝ) f (γ t) v = 0 ∧ mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) v = w)
    (X₁ X₂ : LevelField I f)
    (hX₁ : ∀ t ∈ Icc t₀ (t₀ + δ),
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X₁.Y (γ t)) ≠ 0)
    (hX₂ : ∀ t ∈ Icc (t₁ - δ) t₁,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X₂.Y (γ t)) ≠ 0) :
    ∃ X : LevelField I f,
      (∀ t ∈ Icc t₀ t₁, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X.Y (γ t)) ≠ 0) ∧
      (∃ V₁ ∈ nhdsSet (γ '' Icc t₀ (t₀ + δ / 2)), ∀ x ∈ V₁, X.Y x = X₁.Y x) ∧
      ∃ V₂ ∈ nhdsSet (γ '' Icc (t₁ - δ / 2) t₁), ∀ x ∈ V₂, X.Y x = X₂.Y x := by
  classical
  set A : Set ℝ := Icc t₀ t₁ with hA
  have hG1 : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) 1 G O := hG.of_le (by simp)
  set e₁ : ℝ → EuclideanSpace ℝ (Fin s) := fun t =>
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X₁.Y (γ t)) : EuclideanSpace ℝ (Fin s))
    with he₁
  set e₂ : ℝ → EuclideanSpace ℝ (Fin s) := fun t =>
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) (X₂.Y (γ t)) : EuclideanSpace ℝ (Fin s))
    with he₂
  have hsub₁ : Icc t₀ (t₀ + δ) ⊆ A := Icc_subset_Icc le_rfl (by linarith)
  have hsub₂ : Icc (t₁ - δ) t₁ ⊆ A := Icc_subset_Icc (by linarith) le_rfl
  have he₁c : ContinuousOn e₁ (Icc t₀ (t₀ + δ)) := by
    have h := continuousOn_mfderiv_apply hO hG1 (Y := X₁.Y) X₁.smooth.continuous.continuousOn
    exact h.comp hγ.continuousOn (fun t ht => hγO t (hsub₁ ht))
  have he₂c : ContinuousOn e₂ (Icc (t₁ - δ) t₁) := by
    have h := continuousOn_mfderiv_apply hO hG1 (Y := X₂.Y) X₂.smooth.continuous.continuousOn
    exact h.comp hγ.continuousOn (fun t ht => hγO t (hsub₂ ht))
  obtain ⟨e, hec, hene, hee₁, hee₂⟩ :=
    exists_nonvanishing_path hs hδ ht he₁c he₂c hX₁ hX₂
  have hAne : A.Nonempty := ⟨t₀, le_rfl, by linarith⟩
  obtain ⟨tm, htm, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hAne (continuous_norm.comp_continuousOn hec)
  set μ : ℝ := ‖e tm‖ with hμ
  have hμpos : 0 < μ := norm_pos_iff.mpr (hene tm htm)
  have hμle : ∀ t ∈ A, μ ≤ ‖e t‖ := fun t ht => hmin ht
  obtain ⟨Z, hZ⟩ := exists_levelField_along_arc hf hγ hinj hreg hO hγO hG hsub hec hμpos
  set K₁ : Set M := γ '' Icc t₀ (t₀ + δ / 2) with hK₁
  set K₂ : Set M := γ '' Icc (t₁ - δ / 2) t₁ with hK₂
  set L₁ : Set M := γ '' Icc (t₀ + 3 * δ / 4) t₁ with hL₁
  set L₂ : Set M := γ '' Icc t₀ (t₁ - 3 * δ / 4) with hL₂
  have hK₁c : IsCompact K₁ := isCompact_Icc.image hγ
  have hK₂c : IsCompact K₂ := isCompact_Icc.image hγ
  have hL₁c : IsCompact L₁ := isCompact_Icc.image hγ
  have hL₂c : IsCompact L₂ := isCompact_Icc.image hγ
  have hdisj₁ : Disjoint K₁ L₁ := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have := hinj (show b ∈ A from ⟨by linarith [hb.1], hb.2⟩)
      (show a ∈ A from ⟨ha.1, by linarith [ha.2]⟩) hab
    linarith [ha.2, hb.1]
  have hdisj₂ : Disjoint K₂ L₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have := hinj (show b ∈ A from ⟨hb.1, by linarith [hb.2]⟩)
      (show a ∈ A from ⟨by linarith [ha.1], ha.2⟩) hab
    linarith [ha.1, hb.2]
  have hK₂L₁ : K₂ ⊆ L₁ := image_mono (Icc_subset_Icc (by linarith) le_rfl)
  obtain ⟨U₁, U₁', hU₁o, hU₁'o, hKU₁, hLU₁', hUU₁⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK₁c hL₁c hdisj₁
  obtain ⟨U₂, U₂', hU₂o, hU₂'o, hKU₂, hLU₂', hUU₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK₂c hL₂c hdisj₂
  set W₁ : Set M := U₁ with hW₁
  set W₂ : Set M := U₂ ∩ U₁' with hW₂
  have hW₁o : IsOpen W₁ := hU₁o
  have hW₂o : IsOpen W₂ := hU₂o.inter hU₁'o
  have hKW₁ : K₁ ⊆ W₁ := hKU₁
  have hKW₂ : K₂ ⊆ W₂ := subset_inter hKU₂ (hK₂L₁.trans hLU₁')
  have hWW : ∀ x, x ∈ W₁ → x ∉ W₂ := fun x h1 h2 =>
    Set.disjoint_left.mp hUU₁ h1 h2.2
  have hW₁A : ∀ t ∈ A, γ t ∈ W₁ → t ∈ Icc t₀ (t₀ + δ) := by
    intro t ht hγt
    refine ⟨ht.1, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hL : γ t ∈ L₁ := ⟨t, ⟨by linarith, ht.2⟩, rfl⟩
    exact Set.disjoint_left.mp hUU₁ hγt (hLU₁' hL)
  have hW₂A : ∀ t ∈ A, γ t ∈ W₂ → t ∈ Icc (t₁ - δ) t₁ := by
    intro t ht hγt
    refine ⟨?_, ht.2⟩
    by_contra hlt
    rw [not_le] at hlt
    have hL : γ t ∈ L₂ := ⟨t, ⟨ht.1, by linarith⟩, rfl⟩
    exact Set.disjoint_left.mp hUU₂ hγt.1 (hLU₂' hL)
  have hbump : ∀ (K W : Set M), IsCompact K → IsOpen W → K ⊆ W →
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
        (∀ x, x ∉ W → χ x = 0) ∧ ∀ᶠ x in 𝓝ˢ K, χ x = 1 := by
    intro K W hK hW hKW
    obtain ⟨t, χ', hχs, hχn, -, hχW, -, hχ1, hχK⟩ :=
      exists_finite_smoothPartition (I := I) (ι := Unit) hK (U := fun _ => W) (fun _ => hW)
        (fun x hx => mem_iUnion.2 ⟨(), hKW hx⟩)
    refine ⟨fun x => ∑ i ∈ t, χ' i x, contMDiff_finsetSum fun i _ => hχs i,
      fun x => Finset.sum_nonneg fun i _ => hχn i x, hχ1, ?_, hχK⟩
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => hx (hχW i h)
  obtain ⟨χ₁, hχ₁s, hχ₁n, hχ₁1, hχ₁W, hχ₁K⟩ := hbump K₁ W₁ hK₁c hW₁o hKW₁
  obtain ⟨χ₂, hχ₂s, hχ₂n, hχ₂1, hχ₂W, hχ₂K⟩ := hbump K₂ W₂ hK₂c hW₂o hKW₂
  obtain ⟨X, hX⟩ := LevelField.exists_sum_smul (Finset.univ : Finset (Fin 3))
    (χ := ![χ₁, χ₂, fun x => 1 - χ₁ x - χ₂ x]) (by
      intro i _
      fin_cases i
      · exact hχ₁s
      · exact hχ₂s
      · exact (contMDiff_const.sub hχ₁s).sub hχ₂s) ![X₁, X₂, Z]
  have hXe : ∀ x, X.Y x = χ₁ x • X₁.Y x + χ₂ x • X₂.Y x + (1 - χ₁ x - χ₂ x) • Z.Y x := by
    intro x
    rw [hX x, Fin.sum_univ_three]
    rfl
  refine ⟨X, ?_, ?_, ?_⟩
  · intro t ht
    set L := mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (γ t) with hL
    set a := χ₁ (γ t)
    set b := χ₂ (γ t)
    set w : EuclideanSpace ℝ (Fin s) := L (Z.Y (γ t)) with hw
    have hv : (L (X.Y (γ t)) : EuclideanSpace ℝ (Fin s)) = a • e t + b • e t + (1 - a - b) • w := by
      rw [hXe, map_add, map_add, map_smul, map_smul, map_smul]
      have h1 : a • (L (X₁.Y (γ t)) : EuclideanSpace ℝ (Fin s)) = a • e t := by
        by_cases ha : a = 0
        · rw [ha, zero_smul, zero_smul]
          rfl
        · have hmem : γ t ∈ W₁ := by
            by_contra hn
            exact ha (hχ₁W _ hn)
          rw [hee₁ (hW₁A t ht hmem)]
          rfl
      have h2 : b • (L (X₂.Y (γ t)) : EuclideanSpace ℝ (Fin s)) = b • e t := by
        by_cases hb : b = 0
        · rw [hb, zero_smul, zero_smul]
          rfl
        · have hmem : γ t ∈ W₂ := by
            by_contra hn
            exact hb (hχ₂W _ hn)
          rw [hee₂ (hW₂A t ht hmem)]
          rfl
      rw [← h1, ← h2]
      rfl
    have hab : a = 0 ∨ b = 0 := by
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        have hmem : γ t ∈ W₁ := by
          by_contra hn
          exact ha (hχ₁W _ hn)
        exact hχ₂W _ (hWW _ hmem)
    have ha0 : 0 ≤ a := hχ₁n _
    have hb0 : 0 ≤ b := hχ₂n _
    have ha1 : a ≤ 1 := hχ₁1 _
    have hb1 : b ≤ 1 := hχ₂1 _
    have hc0 : 0 ≤ 1 - a - b := by rcases hab with h | h <;> rw [h] <;> linarith
    have hc1 : 1 - a - b ≤ 1 := by linarith
    have hZt : ‖w - e t‖ < μ := hZ t ht
    have hdiff : (a • e t + b • e t + (1 - a - b) • w) - e t = (1 - a - b) • (w - e t) := by
      rw [smul_sub]
      module
    have hnorm : ‖(a • e t + b • e t + (1 - a - b) • w) - e t‖ < ‖e t‖ := by
      rw [hdiff, norm_smul, Real.norm_of_nonneg hc0]
      calc (1 - a - b) * ‖w - e t‖ ≤ 1 * ‖w - e t‖ :=
            mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
        _ = ‖w - e t‖ := one_mul _
        _ < μ := hZt
        _ ≤ ‖e t‖ := hμle t ht
    intro h0
    change (L (X.Y (γ t)) : EuclideanSpace ℝ (Fin s)) = 0 at h0
    rw [hv] at h0
    rw [h0] at hnorm
    have h' : ‖(0 : EuclideanSpace ℝ (Fin s)) - e t‖ < ‖e t‖ := hnorm
    rw [zero_sub, norm_neg] at h'
    exact lt_irrefl _ h'
  · refine ⟨{x | χ₁ x = 1} ∩ W₁, Filter.inter_mem hχ₁K (hW₁o.mem_nhdsSet.2 hKW₁), ?_⟩
    rintro x ⟨hx1, hxW⟩
    have hx2 : χ₂ x = 0 := hχ₂W _ (hWW _ hxW)
    change χ₁ x = 1 at hx1
    rw [hXe, hx1, hx2]
    simp
  · refine ⟨{x | χ₂ x = 1} ∩ W₂, Filter.inter_mem hχ₂K (hW₂o.mem_nhdsSet.2 hKW₂), ?_⟩
    rintro x ⟨hx1, hxW⟩
    have hx2 : χ₁ x = 0 := hχ₁W _ (fun h => hWW _ h hxW)
    change χ₂ x = 1 at hx1
    rw [hXe, hx1, hx2]
    simp

end WhitneyGeneric

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem leftCoord_submersion (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hrm : 2 * ε < D.rm q hq ^ 2) (hac : a ≤ c)
    (hc : c ≤ f q - ε) (hU : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx) :
    ∃ O : Set M, IsOpen O ∧ D.leftSphere q hq ε c ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) ∞
        (D.leftCoord q hq ε) O ∧
      ∀ z ∈ D.leftSphere q hq ε c, mfderiv I 𝓘(ℝ, ℝ) f z ≠ 0 ∧
        ∀ w : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)), ∃ v : TangentSpace I z,
          mfderiv I 𝓘(ℝ, ℝ) f z v = 0 ∧
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z v =
            w := by
  classical
  set d := D.chart q hq with hd
  set c₀ : ℝ := f q - ε with hc₀
  have hRpos : 0 < d.R := d.R_pos
  have hrmR : D.rm q hq ≤ d.R := (D.hrm q hq).2
  have hrmpos : 0 < D.rm q hq := D.rm_pos q hq
  have hεR : 2 * ε ≤ d.R ^ 2 := by nlinarith
  have hq0 : q ∈ d.χ '' Metric.ball 0 d.R' := ⟨0, d.zero_mem_ball, d.hχ0⟩
  have hfq : f q ∈ Ioo a b := D.inStrip q hq hq0
  have hc₀b : c₀ ≤ b := by rw [hc₀]; linarith [hfq.2]
  have hcab : c ∈ Icc a b := ⟨hac, by linarith⟩
  have htrans := (flow_level_transport (D := D) hf (c' := c) (c := c₀) hac hc hc₀b hU).1
  have hlevel : ∀ z ∈ D.leftSphere q hq ε c, f z = c := by
    intro z hz
    have h := D.leftSphere_subset_level hf q hq hεR hcab (by
      rw [uIcc_of_ge hc]
      exact hU) hz
    simpa using h
  set O : Set M := D.π c₀ ⁻¹' (d.χ '' Metric.ball 0 d.R') with hO
  have hOopen : IsOpen O := d.isOpen_image_ball.preimage (D.continuous_π hf c₀)
  have hSO : D.leftSphere q hq ε c ⊆ O := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := (D.mem_leftSphere_iff q hq ε c).1 hz
    change D.flow (f z - c₀) z ∈ d.χ '' Metric.ball 0 d.R'
    rw [hlevel z hz]
    exact ⟨y, d.mem_ball_of_le (d.morseNorm_le_R_of_mem_leftModelSphere hεR hy), hyz⟩
  have hsmooth : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k))) ∞
      (D.leftCoord q hq ε) O := by
    have h1 : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ (fun z => d.χ.symm (D.π c₀ z)) O :=
      d.hχsymm.comp (D.contMDiff_π hf c₀).contMDiffOn (fun z hz => hz)
    exact ((ModelField.posPartL d.hk).contMDiff.comp_contMDiffOn h1 :)
  refine ⟨O, hOopen, hSO, hsmooth, fun z hz => ⟨?_, fun w => ?_⟩⟩
  · have hfz := hlevel z hz
    have hunit := D.unit z (by rw [mem_preimage, hfz]; exact hcab)
      (fun p hp => hU z (by rw [hfz]; exact ⟨le_rfl, hc⟩) p hp)
    intro h0
    rw [h0] at hunit
    simp at hunit
  · obtain ⟨ŷ, hŷ, hŷz⟩ := (D.mem_leftSphere_iff q hq ε c).1 hz
    set u : EuclideanSpace ℝ (Fin d.k) := negPart d.hk ŷ with hu
    have hu2 : ‖u‖ ^ 2 = 2 * ε := hŷ.2
    have hŷpos : posPart d.hk ŷ = 0 := hŷ.1
    set lam : ℝ → ℝ := fun s => Real.sqrt (1 + s ^ 2 * ‖w‖ ^ 2 / (2 * ε)) with hlam
    have hlam_arg : ∀ s : ℝ, 0 < 1 + s ^ 2 * ‖w‖ ^ 2 / (2 * ε) := fun s => by positivity
    set σ : ℝ → (Fin n → ℝ) := fun s => ModelField.recombineL d.hk (lam s • u, s • w) with hσ
    have hσrec : ∀ s, σ s = recombine d.hk (lam s • u) (s • w) := fun s =>
      ModelField.recombineL_apply d.hk _ _
    have hσ0 : σ 0 = ŷ := by
      rw [hσrec]
      have hl0 : lam 0 = 1 := by simp [hlam]
      rw [hl0, one_smul, zero_smul, ← hŷpos, hu]
      exact DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose d.hk ŷ
    have hσc : Continuous σ := by
      have hl : Continuous lam := by
        rw [hlam]; fun_prop
      exact (ModelField.recombineL d.hk).continuous.comp ((hl.smul continuous_const).prodMk
        (continuous_id.smul continuous_const))
    have hσd : DifferentiableAt ℝ σ 0 := by
      have hl : DifferentiableAt ℝ lam 0 :=
        (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 1 + s ^ 2 * ‖w‖ ^ 2 / (2 * ε)) 0).sqrt
          (hlam_arg 0).ne'
      exact (ModelField.recombineL d.hk).differentiableAt.comp 0 ((hl.smul_const u).prodMk
        (differentiableAt_id.smul_const w))
    have hŷR : morseNorm n ŷ < d.R := by
      refine lt_of_pow_lt_pow_left₀ 2 hRpos.le ?_
      rw [d.morseNorm_sq_of_mem_leftModelSphere hŷ]
      nlinarith
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), morseNorm n (σ s) < d.R :=
      hσc.continuousAt.preimage_mem_nhds ((isOpen_morseNorm_lt _).mem_nhds (by
        change morseNorm n (σ 0) < d.R
        rw [hσ0]; exact hŷR))
    have hlevσ : ∀ s, morseNorm n (σ s) < d.R → f (d.χ (σ s)) = c₀ := by
      intro s hs
      rw [d.hnorm _ hs.le,
        DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hσrec, ModelField.posPart_recombine,
        ModelField.negPart_recombine, norm_smul, norm_smul, mul_pow, mul_pow, hu2]
      have hl2 : ‖lam s‖ ^ 2 = 1 + s ^ 2 * ‖w‖ ^ 2 / (2 * ε) := by
        rw [Real.norm_eq_abs, sq_abs]
        exact Real.sq_sqrt (hlam_arg s).le
      have hs2 : ‖s‖ ^ 2 = s ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      rw [hl2, hs2, hc₀]
      field_simp
      ring
    set β : ℝ → M := fun s => D.flow (c₀ - c) (d.χ (σ s)) with hβ
    have hβ0 : β 0 = z := by
      change D.flow (c₀ - c) (d.χ (σ 0)) = z
      rw [hσ0, hŷz, flow_flow, show c - (f q - ε) + (c₀ - c) = 0 by rw [hc₀]; ring, flow_zero]
    have hfβ : ∀ᶠ s in 𝓝 (0 : ℝ), f (β s) = c := by
      filter_upwards [hev] with s hs
      exact (htrans _ (hlevσ s hs)).1
    have hLβ : ∀ᶠ s in 𝓝 (0 : ℝ), D.leftCoord q hq ε (β s) = s • w := by
      filter_upwards [hev] with s hs
      have h1 : f (β s) = c := (htrans _ (hlevσ s hs)).1
      change posPart d.hk (d.χ.symm (D.flow (f (β s) - (f q - ε)) (β s))) = s • w
      rw [h1]
      change posPart d.hk (d.χ.symm (D.flow (c - (f q - ε)) (D.flow (c₀ - c) (d.χ (σ s))))) = s • w
      rw [flow_flow, show c₀ - c + (c - (f q - ε)) = 0 by rw [hc₀]; ring, flow_zero,
        d.χ.left_inv (d.hsrc _ hs.le), hσrec, ModelField.posPart_recombine]
    have hŷball : ŷ ∈ Metric.ball (0 : Fin n → ℝ) d.R' := d.mem_ball_of_le hŷR.le
    have hβd : MDifferentiableAt 𝓘(ℝ, ℝ) I β 0 := by
      have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) σ 0 :=
        mdifferentiableAt_iff_differentiableAt.2 hσd
      have h2 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I d.χ (σ 0) := by
        rw [hσ0]
        exact (d.hχ.contMDiffAt (Metric.isOpen_ball.mem_nhds hŷball)).mdifferentiableAt
          (by simp)
      have h3 : MDifferentiableAt I I (D.flow (c₀ - c)) (d.χ (σ 0)) :=
        (D.contMDiff_flow _ _).mdifferentiableAt (by simp)
      exact h3.comp 0 (h2.comp 0 h1)
    have hLd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k)))
        (D.leftCoord q hq ε) (β 0) := by
      rw [hβ0]
      exact (hsmooth.contMDiffAt (hOopen.mem_nhds (hSO hz))).mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (β 0) := (hf _).mdifferentiableAt (by simp)
    have hA : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ β) 0
        ((mfderiv I 𝓘(ℝ, ℝ) f (β 0)).comp (mfderiv 𝓘(ℝ, ℝ) I β 0)) :=
      hfd.hasMFDerivAt.comp 0 hβd.hasMFDerivAt
    have hA' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ β) 0 0 := by
      have h0 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => c) 0 0 :=
        hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_const c 0)
      exact h0.congr_of_eventuallyEq hfβ
    have hB : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k)))
        (D.leftCoord q hq ε ∘ β) 0
        ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k))) (D.leftCoord q hq ε) (β 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) I β 0)) :=
      hLd.hasMFDerivAt.comp 0 hβd.hasMFDerivAt
    have hB' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k)))
        (D.leftCoord q hq ε ∘ β) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
      have h0 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k)))
          (fun s : ℝ => s • w) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) :=
        hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id (0 : ℝ)).smul_const w)
      exact h0.congr_of_eventuallyEq hLβ
    have eA := hA.mfderiv.symm.trans hA'.mfderiv
    have eB := hB.mfderiv.symm.trans hB'.mfderiv
    have key : mfderiv I 𝓘(ℝ, ℝ) f (β 0) (mfderiv 𝓘(ℝ, ℝ) I β 0 1) = 0 ∧
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - d.k))) (D.leftCoord q hq ε) (β 0)
          (mfderiv 𝓘(ℝ, ℝ) I β 0 1) = w := by
      constructor
      · have := congrArg (fun L => L 1) eA
        simpa using this
      · have := congrArg (fun L => L 1) eB
        simp only [ContinuousLinearMap.comp_apply, Function.comp_apply] at this
        rw [this]
        exact one_smul ℝ w
    rw [hβ0] at key
    exact ⟨_, key⟩

theorem rightCoord_submersion (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p : M} (hp : p ∈ crit) {ε c : ℝ} (hε : 0 < ε) (hrm : 2 * ε < D.rm p hp ^ 2)
    (hc : f p + ε ≤ c) (hcb : c ≤ b)
    (hU : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx) :
    ∃ O : Set M, IsOpen O ∧ D.rightSphere p hp ε c ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) ∞ (D.rightCoord p hp ε) O ∧
      ∀ z ∈ D.rightSphere p hp ε c, mfderiv I 𝓘(ℝ, ℝ) f z ≠ 0 ∧
        ∀ w : EuclideanSpace ℝ (Fin (D.chart p hp).k), ∃ v : TangentSpace I z,
          mfderiv I 𝓘(ℝ, ℝ) f z v = 0 ∧
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z v = w := by
  have hpstrip : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hrmR : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hrm0 : 0 < D.rm p hp := D.rm_pos p hp
  have htr := D.flow_level_transport hf (c' := f p + ε) (c := c) (by linarith [hpstrip.1]) hc hcb hU
  set Φ : M → M := fun z => D.flow (f z - (f p + ε)) z with hΦ
  have hΦs : ContMDiff I I ∞ Φ :=
    D.contMDiff_flow_joint.comp ((hf.sub contMDiff_const).prodMk contMDiff_id)
  set B : Set M := (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' with hB
  have hBo : IsOpen B := (D.chart p hp).isOpen_image_ball
  have hsph : ∀ z ∈ D.rightSphere p hp ε c, ∃ w₀ ∈ (D.chart p hp).rightModelSphere ε,
      morseNorm n w₀ < D.rm p hp ∧ f z = c ∧ Φ z = (D.chart p hp).χ w₀ ∧
      D.flow (f p + ε - c) ((D.chart p hp).χ w₀) = z := by
    rintro z ⟨x, ⟨w₀, hw₀, rfl⟩, rfl⟩
    have hlt : morseNorm n w₀ < D.rm p hp := by
      apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
      rw [(D.chart p hp).morseNorm_sq_of_mem_rightModelSphere hw₀]
      exact hrm
    have hfw : f ((D.chart p hp).χ w₀) = f p + ε := by
      rw [(D.chart p hp).hnorm w₀ (hlt.le.trans hrmR)]
      exact (D.chart p hp).nf_of_mem_rightModelSphere hw₀
    have hfz := (htr.2 _ hfw).1
    refine ⟨w₀, hw₀, hlt, hfz, ?_, rfl⟩
    simp only [hΦ]
    rw [hfz, flow_flow, show f p + ε - c + (c - (f p + ε)) = 0 by ring, flow_zero]
  have hGsm : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) ∞
      (D.rightCoord p hp ε) (Φ ⁻¹' B) := by
    have h1 : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ((D.chart p hp).χ.symm ∘ Φ) (Φ ⁻¹' B) :=
      (D.chart p hp).hχsymm.comp hΦs.contMDiffOn (fun z hz => hz)
    exact (ModelField.negPartL (D.chart p hp).hk).contMDiff.comp_contMDiffOn h1
  have hSO : D.rightSphere p hp ε c ⊆ Φ ⁻¹' B := by
    intro z hz
    obtain ⟨w₀, -, hlt, -, hΦz, -⟩ := hsph z hz
    change Φ z ∈ B
    rw [hΦz]
    exact ⟨w₀, mem_ball_of_morseNorm_lt (hlt.trans (D.rm_lt_R' p hp)), rfl⟩
  refine ⟨Φ ⁻¹' B, hBo.preimage hΦs.continuous, hSO, hGsm, ?_⟩
  intro z hz
  obtain ⟨w₀, hw₀, hlt, hfz, hΦz, hxz⟩ := hsph z hz
  constructor
  · have hunit : dfV I f D.V z = -1 := D.dfV_eq_neg_one_of_mem_unitRegion
      ⟨by rw [hfz]; exact ⟨by linarith [hpstrip.1], hcb⟩,
        fun x hx => hU z (by rw [hfz]; exact ⟨hc, le_rfl⟩) x hx⟩
    intro h0
    rw [dfV, h0] at hunit
    simp at hunit
  intro w
  set v₀ := posPart (D.chart p hp).hk w₀ with hv₀
  have hv₀n : ‖v₀‖ ^ 2 = 2 * ε := hw₀.2
  set α : ℝ := ‖w‖ ^ 2 / (2 * ε) with hα
  have hα0 : 0 ≤ α := by positivity
  have hα2 : α * (2 * ε) = ‖w‖ ^ 2 := div_mul_cancel₀ _ (by positivity)
  have hpos : ∀ s : ℝ, 0 < 1 + α * s ^ 2 := fun s => by
    have := mul_nonneg hα0 (sq_nonneg s)
    linarith
  set σ : ℝ → (Fin n → ℝ) := fun s =>
    ModelField.recombineL (D.chart p hp).hk (s • w, Real.sqrt (1 + α * s ^ 2) • v₀) with hσ
  have hσ0 : σ 0 = w₀ := by
    simp only [hσ, ModelField.recombineL_apply, zero_smul]
    norm_num
    rw [← hw₀.1]
    exact DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose _ w₀
  have hσd : ∀ s, DifferentiableAt ℝ σ s := by
    intro s
    have hq : DifferentiableAt ℝ (fun s : ℝ => 1 + α * s ^ 2) s := by fun_prop
    have hsq : DifferentiableAt ℝ (fun s : ℝ => Real.sqrt (1 + α * s ^ 2) • v₀) s :=
      (hq.sqrt (hpos s).ne').smul_const v₀
    have hl : DifferentiableAt ℝ (fun s : ℝ => s • w) s := by fun_prop
    exact (ModelField.recombineL (D.chart p hp).hk).differentiableAt.comp s (hl.prodMk hsq)
  have hev : ∀ᶠ s in 𝓝 (0:ℝ), morseNorm n (σ s) < D.rm p hp := by
    have hcont : Continuous (fun s => morseNorm n (σ s)) :=
      continuous_morseNorm.comp (continuous_iff_continuousAt.2 fun s => (hσd s).continuousAt)
    exact hcont.continuousAt.eventually_lt continuousAt_const (by simpa [hσ0] using hlt)
  have hlevel : ∀ s, morseNorm n (σ s) < D.rm p hp →
      f ((D.chart p hp).χ (σ s)) = f p + ε := by
    intro s hs
    rw [(D.chart p hp).hnorm _ (hs.le.trans hrmR), DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
    simp only [hσ, ModelField.recombineL_apply, ModelField.negPart_recombine,
      ModelField.posPart_recombine, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hpos s).le, hv₀n]
    linear_combination (1 / 2 * s ^ 2) * hα2
  set γ : ℝ → M := fun s => D.flow (f p + ε - c) ((D.chart p hp).χ (σ s)) with hγ
  have hγ0 : γ 0 = z := by simp only [hγ, hσ0]; exact hxz
  have hfγ : ∀ s, morseNorm n (σ s) < D.rm p hp → f (γ s) = c := fun s hs =>
    (htr.2 _ (hlevel s hs)).1
  have hGγ : ∀ s, morseNorm n (σ s) < D.rm p hp → D.rightCoord p hp ε (γ s) = s • w := by
    intro s hs
    have h1 := hfγ s hs
    unfold rightCoord
    rw [h1]
    simp only [hγ]
    rw [flow_flow, show f p + ε - c + (c - (f p + ε)) = 0 by ring, flow_zero,
      (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc _ (hs.le.trans hrmR))]
    simp only [hσ, ModelField.recombineL_apply, ModelField.negPart_recombine]
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := by
    have hχd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I (D.chart p hp).χ (σ 0) := by
      rw [hσ0]
      exact (D.chart p hp).mdifferentiableAt_chart
        (mem_ball_of_morseNorm_lt (hlt.trans (D.rm_lt_R' p hp)))
    exact ((D.contMDiff_flow _).mdifferentiableAt (by simp)).comp 0
      (hχd.comp 0 (hσd 0).mdifferentiableAt)
  have hzO : γ 0 ∈ Φ ⁻¹' B := by rw [hγ0]; exact hSO hz
  rw [← hγ0]
  refine ⟨mfderiv 𝓘(ℝ, ℝ) I γ 0 1, ?_, ?_⟩
  · have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ 0) := (hf (γ 0)).mdifferentiableAt (by simp)
    have h1 := mfderiv_comp 0 hfd hγd
    have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) 0 = 0 := by
      have heq : (f ∘ γ) =ᶠ[𝓝 0] fun _ => c := hev.mono fun s hs => hfγ s hs
      rw [heq.mfderiv_eq, mfderiv_const]
      simp
    have h3 := congrArg (fun L => L 1) (h1.symm.trans h2)
    simpa using h3
  · have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (γ 0) :=
      (hGsm.contMDiffAt ((hBo.preimage hΦs.continuous).mem_nhds hzO)).mdifferentiableAt
        (by simp)
    have h1 := mfderiv_comp 0 hGd hγd
    have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε ∘ γ) 0 1 = w := by
      have heq : (D.rightCoord p hp ε ∘ γ) =ᶠ[𝓝 0] fun s => s • w :=
        hev.mono fun s hs => hGγ s hs
      have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
          (fun s : ℝ => s • w) 0 ((ContinuousLinearMap.id ℝ ℝ).smulRight w) :=
        hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id (0:ℝ)).smul_const w)
      rw [(hd.congr_of_eventuallyEq heq).mfderiv]
      exact one_smul ℝ w
    have h3 := DFunLike.congr_fun h1 1
    rw [ContinuousLinearMap.comp_apply] at h3
    exact h3.symm.trans h2

theorem isThin_leftSphere (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit) {ε : ℝ}
    (hε : 0 < ε) (hR : 2 * ε < (D.chart q hq).R ^ 2) (c : ℝ) :
    IndexOnePartner.isThin I ((D.chart q hq).k - 1) (D.leftSphere q hq ε c) := by
  classical
  set d := D.chart q hq with hd
  have hεR : 2 * ε ≤ d.R ^ 2 := hR.le
  by_cases hk0 : d.k = 0
  · refine ⟨Empty, inferInstance, fun _ => ∅, fun _ _ => q, fun _ => isOpen_empty,
      fun i => i.elim, ?_⟩
    rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exfalso
    have hz : negPart d.hk y = 0 := by
      ext i
      have := i.isLt
      simp only [hk0] at this
      omega
    have h2 := hy.2
    rw [hz, norm_zero] at h2
    nlinarith
  · let emb : Fin d.k → Bool → (Fin (d.k - 1) → ℝ) → (Fin d.k → ℝ) := fun i s t j =>
      if h : j.val < i.val then t ⟨j.val, by omega⟩
      else if h' : j.val = i.val then (if s then 1 else -1)
      else t ⟨j.val - 1, by omega⟩
    have hemb_ne : ∀ i s t, emb i s t ≠ 0 := by
      intro i s t h
      have := congrFun h i
      cases s <;> simp [emb] at this
    have hemb_smooth : ∀ i s, ContDiff ℝ ∞ (emb i s) := by
      intro i s
      refine contDiff_pi.2 fun j => ?_
      by_cases h1 : j.val < i.val
      · simp only [emb, h1, ↓reduceDIte]
        exact contDiff_apply ℝ ℝ _
      · by_cases h2 : j.val = i.val
        · simp only [emb, h2, lt_self_iff_false, ↓reduceDIte]
          exact contDiff_const
        · simp only [emb, h1, h2, ↓reduceDIte]
          exact contDiff_apply ℝ ℝ _
    refine ⟨Fin d.k × Bool, inferInstance, fun _ => univ,
      fun p t => D.flow (f q - ε - c) (d.χ (d.sphereParam ε (emb p.1 p.2 t))),
      fun _ => isOpen_univ, ?_, ?_⟩
    · intro p
      have hsm : ContMDiff 𝓘(ℝ, Fin (d.k - 1) → ℝ) I ∞
          (fun t => D.flow (f q - ε - c) (d.χ (d.sphereParam ε (emb p.1 p.2 t)))) := by
        intro t
        have hw := hemb_ne p.1 p.2 t
        have hball : d.sphereParam ε (emb p.1 p.2 t) ∈ Metric.ball (0 : Fin n → ℝ) d.R' :=
          d.mem_ball_of_le (d.morseNorm_sphereParam_le hε.le hεR hw)
        have h1 : ContMDiffAt 𝓘(ℝ, Fin (d.k - 1) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
            (fun t => d.sphereParam ε (emb p.1 p.2 t)) t :=
          ((d.contDiffAt_sphereParam ε hw).comp t (hemb_smooth p.1 p.2).contDiffAt).contMDiffAt
        exact (D.contMDiff_flow _).contMDiffAt.comp t ((d.contMDiffAt_chart hball).comp t h1)
      exact (hsm.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contMDiffOn
    · rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨hw0, hwy⟩ := d.sphereParam_of_mem hε hy
      set w := (EuclideanSpace.equiv (Fin d.k) ℝ) (negPart d.hk y) with hw
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
      have hi' : w i ≠ 0 := hi
      set a := |w i| with ha
      have ha0 : 0 < a := abs_pos.2 hi'
      let s : Bool := decide (0 < w i)
      let t : Fin (d.k - 1) → ℝ := fun j =>
        if j.val < i.val then w ⟨j.val, by omega⟩ / a else w ⟨j.val + 1, by omega⟩ / a
      have hemb : emb i s t = a⁻¹ • w := by
        funext j
        rw [Pi.smul_apply, smul_eq_mul]
        by_cases h1 : j.val < i.val
        · simp only [emb, t, h1, ↓reduceDIte, ↓reduceIte]
          rw [div_eq_inv_mul]
        · by_cases h2 : j.val = i.val
          · have hji : j = i := Fin.ext h2
            subst hji
            simp only [emb, h1, ↓reduceDIte, s]
            by_cases hp : 0 < w j
            · rw [ha, abs_of_pos hp, inv_mul_cancel₀ hp.ne']
              simp [hp]
            · have hn : w j < 0 := lt_of_le_of_ne (not_lt.1 hp) hi'
              rw [ha, abs_of_neg hn]
              simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
              field_simp
          · have h3 : ¬ (j.val - 1 < i.val) := by omega
            have hj : (⟨j.val - 1 + 1, by omega⟩ : Fin d.k) = j := Fin.ext (by simp; omega)
            simp only [emb, t, h1, h2, h3, ↓reduceDIte, ↓reduceIte, hj]
            rw [div_eq_inv_mul]
      have hscale : d.sphereParam ε (a⁻¹ • w) = d.sphereParam ε w := by
        unfold MorseNormalChart.sphereParam
        congr 1
        have hE : d.toE (a⁻¹ • w) = a⁻¹ • d.toE w := by
          unfold MorseNormalChart.toE
          exact map_smul _ _ _
        have hv : ‖d.toE w‖ ≠ 0 := norm_ne_zero_iff.2 (d.toE_ne_zero hw0)
        rw [hE, norm_smul, smul_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha0]
        congr 1
        field_simp
      refine mem_iUnion.2 ⟨(i, s), t, mem_univ _, ?_⟩
      change D.flow (f q - ε - c) (d.χ (d.sphereParam ε (emb i s t))) = _
      rw [hemb, hscale, hwy]

theorem isThin_rightSphere (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) {ε : ℝ}
    (hε : 0 < ε) (hR : 2 * ε < (D.chart p hp).R ^ 2) (c : ℝ) :
    IndexOnePartner.isThin I (n - (D.chart p hp).k - 1) (D.rightSphere p hp ε c) := by
  classical
  set d := D.chart p hp with hd
  have hcard : ∀ i : Fin (n - d.k), Fintype.card {j : Fin (n - d.k) // j ≠ i} = n - d.k - 1 := by
    intro i
    simp [Fintype.card_subtype_compl]
  let σ : ∀ i : Fin (n - d.k), {j : Fin (n - d.k) // j ≠ i} ≃ Fin (n - d.k - 1) := fun i =>
    Fintype.equivFinOfCardEq (hcard i)
  let V : Fin (n - d.k) × Bool → (Fin (n - d.k - 1) → ℝ) → Fin (n - d.k) → ℝ := fun ib w j =>
    if h : j = ib.1 then (if ib.2 then (1 : ℝ) else -1) * Real.sqrt (2 * ε - ∑ l, w l ^ 2)
    else w (σ ib.1 ⟨j, h⟩)
  let Y : Fin (n - d.k) × Bool → (Fin (n - d.k - 1) → ℝ) → Fin n → ℝ := fun ib w t =>
    if h : d.k ≤ t.val then V ib w ⟨t.val - d.k, by omega⟩ else 0
  let S : Set (Fin (n - d.k - 1) → ℝ) := {w | ∑ l, w l ^ 2 < 2 * ε}
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hV : ∀ ib j, ContDiffOn ℝ ∞ (fun w => V ib w j) S := by
    intro ib j
    by_cases h : j = ib.1
    · simp only [V, h, ↓reduceDIte]
      refine contDiffOn_const.mul (ContDiffOn.sqrt (by fun_prop) fun w hw => ?_)
      have : ∑ l, w l ^ 2 < 2 * ε := hw
      linarith
    · simp only [V, h, ↓reduceDIte]
      exact (contDiff_apply ℝ ℝ _).contDiffOn
  have hYsm : ∀ ib, ContDiffOn ℝ ∞ (Y ib) S := by
    intro ib
    refine contDiffOn_pi.2 fun t => ?_
    by_cases h : d.k ≤ t.val
    · simp only [Y, h, ↓reduceDIte]
      exact hV ib _
    · simp only [Y, h, ↓reduceDIte]
      exact contDiffOn_const
  refine ⟨Fin (n - d.k) × Bool, inferInstance, fun ib => S ∩ Y ib ⁻¹' Metric.ball 0 d.R',
    fun ib w => D.flow (f p + ε - c) (d.χ (Y ib w)), ?_, ?_, ?_⟩
  · intro ib
    exact (hYsm ib).continuousOn.isOpen_inter_preimage hS Metric.isOpen_ball
  · intro ib
    have h1 : ContMDiffOn 𝓘(ℝ, Fin (n - d.k - 1) → ℝ) I ∞ (fun w => d.χ (Y ib w))
        (S ∩ Y ib ⁻¹' Metric.ball 0 d.R') :=
      d.hχ.comp ((hYsm ib).contMDiffOn.mono inter_subset_left) fun w hw => hw.2
    exact ((D.contMDiff_flow _).comp_contMDiffOn h1).of_le (by simp)
  · rintro x ⟨x', ⟨y, hy, rfl⟩, rfl⟩
    have hv : posPart d.hk y ≠ 0 := by
      intro h
      have h2 := hy.2
      rw [h, norm_zero] at h2
      linarith
    obtain ⟨i, hi⟩ : ∃ i, posPart d.hk y i ≠ 0 := by
      by_contra hcon
      exact hv (by ext j; by_contra hj; exact hcon ⟨j, by simpa using hj⟩)
    let b : Bool := decide (0 < posPart d.hk y i)
    let w : Fin (n - d.k - 1) → ℝ := fun l => posPart d.hk y ((σ i).symm l).1
    have hsum : ∑ l, w l ^ 2 = 2 * ε - posPart d.hk y i ^ 2 := by
      have h1 : ∑ l, w l ^ 2 = ∑ j : {j : Fin (n - d.k) // j ≠ i}, posPart d.hk y j.1 ^ 2 :=
        Equiv.sum_comp (σ i).symm (fun j => posPart d.hk y j.1 ^ 2)
      have h2 : ‖posPart d.hk y‖ ^ 2 = ∑ j, posPart d.hk y j ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      have h3 := Fintype.sum_eq_add_sum_subtype_ne (fun j => posPart d.hk y j ^ 2) i
      have h4 := hy.2
      rw [h1]
      linarith
    have hYw : Y (i, b) w = y := by
      funext t
      by_cases ht : d.k ≤ t.val
      · simp only [Y, ht, ↓reduceDIte]
        have hyt : y t = posPart d.hk y ⟨t.val - d.k, by omega⟩ := by
          rw [ModelField.posPart_apply]
          congr 1
          ext
          simp [DifferentialGeometry.Topology.Morse.CellAttachment.posIdx]
          omega
        rw [hyt]
        by_cases hj : (⟨t.val - d.k, by omega⟩ : Fin (n - d.k)) = i
        · simp only [V, hj, ↓reduceDIte]
          rw [hsum, sub_sub_cancel, Real.sqrt_sq_eq_abs]
          by_cases hpos : 0 < posPart d.hk y i
          · simp [b, hpos, abs_of_pos hpos]
          · have hneg : posPart d.hk y i < 0 := lt_of_le_of_ne (not_lt.1 hpos) hi
            simp [b, hpos, abs_of_neg hneg]
        · simp only [V, hj, ↓reduceDIte, w]
          rw [Equiv.symm_apply_apply]
      · simp only [Y, ht, ↓reduceDIte]
        have ht' : t.val < d.k := by omega
        have h0 : negPart d.hk y ⟨t.val, ht'⟩ = 0 := by rw [hy.1]; rfl
        rw [ModelField.negPart_apply] at h0
        rw [← h0]
        congr 1
    refine mem_iUnion.2 ⟨(i, b), w, ⟨?_, ?_⟩, ?_⟩
    · change ∑ l, w l ^ 2 < 2 * ε
      rw [hsum]
      have := pow_pos (abs_pos.2 hi) 2
      rw [sq_abs] at this
      linarith
    · change Y (i, b) w ∈ Metric.ball 0 d.R'
      rw [hYw]
      exact d.mem_ball_of_le (d.morseNorm_le_R_of_mem_rightModelSphere hR.le hy)
    · simp only [hYw, hd]

structure WhitneyDisc (D : GradientLikeStrip I f a b crit) (c : ℝ) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (ε : ℝ) (x₁ x₂ : M) where
  W : Set (Fin 2 → ℝ)
  isOpen_W : IsOpen W
  half_subset : whitneyHalf ⊆ W
  ψ : (Fin 2 → ℝ) → M
  smooth : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ W
  immersion : ∀ y ∈ W, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ y)
  inj : InjOn ψ W
  level : ∀ y ∈ W, f (ψ y) = c
  memA : ∀ y ∈ W, ψ y ∈ D.leftSphere q hq ε c ↔ y 1 = 0
  memB : ∀ y ∈ W, ψ y ∈ D.rightSphere p hp ε c ↔ y 0 ^ 2 + y 1 ^ 2 = 1
  transA : ∀ y ∈ W, y 1 = 0 →
    fderiv ℝ (fun y => D.leftCoord q hq ε (ψ y)) y (Pi.single 1 1) ≠ 0
  transB : ∀ y ∈ W, y 0 ^ 2 + y 1 ^ 2 = 1 → fderiv ℝ (fun y => D.rightCoord p hp ε (ψ y)) y y ≠ 0
  corner₁ : ψ ![-1, 0] = x₁
  corner₂ : ψ ![1, 0] = x₂

structure IsWhitneyCollar (D : GradientLikeStrip I f a b crit) (c : ℝ) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (ε : ℝ) (x₁ x₂ : M) (N : Set (Fin 2 → ℝ)) (ψ : (Fin 2 → ℝ) → M) : Prop where
  isOpen_N : IsOpen N
  smooth : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ N
  immersion : ∀ y ∈ N, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ y)
  inj : InjOn ψ N
  level : ∀ y ∈ N, f (ψ y) = c
  memA : ∀ y ∈ N, ψ y ∈ D.leftSphere q hq ε c ↔ y 1 = 0
  memB : ∀ y ∈ N, ψ y ∈ D.rightSphere p hp ε c ↔ y 0 ^ 2 + y 1 ^ 2 = 1
  transA : ∀ y ∈ N, y 1 = 0 →
    fderiv ℝ (fun y => D.leftCoord q hq ε (ψ y)) y (Pi.single 1 1) ≠ 0
  transB : ∀ y ∈ N, y 0 ^ 2 + y 1 ^ 2 = 1 → fderiv ℝ (fun y => D.rightCoord p hp ε (ψ y)) y y ≠ 0
  corner₁ : ψ ![-1, 0] = x₁
  corner₂ : ψ ![1, 0] = x₂

structure IsCornerChart (D : GradientLikeStrip I f a b crit) (c : ℝ) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (ε : ℝ) (ℓ : ℕ) (x : M) (U : Set (Fin (n - 1) → ℝ))
    (φ : (Fin (n - 1) → ℝ) → M) : Prop where
  isOpen_U : IsOpen U
  zero_mem : (0 : Fin (n - 1) → ℝ) ∈ U
  smooth : ContMDiffOn 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ φ U
  immersion : ∀ y ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ y)
  inj : InjOn φ U
  level : ∀ y ∈ U, f (φ y) = c
  center : φ 0 = x
  coordR : ∀ y ∈ U, ∀ i : Fin (D.chart p hp).k, D.rightCoord p hp ε (φ y) i = coordN y i
  coordL : ∀ y ∈ U, ∀ i : Fin (n - (D.chart q hq).k), D.leftCoord q hq ε (φ y) i = coordN y (ℓ + i)
  memL : ∀ y ∈ U, φ y ∈ D.leftSphere q hq ε c ↔ ∀ j, ℓ ≤ j → coordN y j = 0
  memR : ∀ y ∈ U, φ y ∈ D.rightSphere p hp ε c ↔ ∀ j, j < ℓ → coordN y j = 0
  open_image : ∀ V ⊆ U, IsOpen V → ∃ G : Set M, IsOpen G ∧ φ '' V = G ∩ f ⁻¹' {c}

structure IsWhitneyArcs (D : GradientLikeStrip I f a b crit) (c : ℝ) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (ε : ℝ) (ℓ : ℕ) (φ₁ φ₂ : (Fin (n - 1) → ℝ) → M) (U₁ U₂ : Set (Fin (n - 1) → ℝ))
    (γA γB : ℝ → M) (a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ) (δ : ℝ) : Prop where
  hδ : 0 < δ
  smoothA : ContMDiff 𝓘(ℝ, ℝ) I ∞ γA
  smoothB : ContMDiff 𝓘(ℝ, ℝ) I ∞ γB
  immA : ∀ t ∈ Icc (-1 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I γA t 1 ≠ 0
  immB : ∀ t ∈ Icc (0 : ℝ) Real.pi, mfderiv 𝓘(ℝ, ℝ) I γB t 1 ≠ 0
  injA : InjOn γA (Icc (-1) 1)
  injB : InjOn γB (Icc 0 Real.pi)
  memA : ∀ t ∈ Icc (-1 : ℝ) 1, γA t ∈ D.leftSphere q hq ε c ∧
    (γA t ∈ D.rightSphere p hp ε c ↔ t = -1 ∨ t = 1)
  memB : ∀ t ∈ Icc (0 : ℝ) Real.pi, γB t ∈ D.rightSphere p hp ε c ∧
    (γB t ∈ D.leftSphere q hq ε c ↔ t = 0 ∨ t = Real.pi)
  dirA : a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ (∀ j, ℓ ≤ j → coordN a₁ j = 0) ∧ ∀ j, ℓ ≤ j → coordN a₂ j = 0
  dirB : b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ (∀ j, j < ℓ → coordN b₁ j = 0) ∧ ∀ j, j < ℓ → coordN b₂ j = 0
  endA₁ : ∀ t, |t + 1| < δ → (t + 1) • a₁ ∈ U₁ ∧ γA t = φ₁ ((t + 1) • a₁)
  endA₂ : ∀ t, |t - 1| < δ → (1 - t) • a₂ ∈ U₂ ∧ γA t = φ₂ ((1 - t) • a₂)
  endB₂ : ∀ t, |t| < δ → t • b₂ ∈ U₂ ∧ γB t = φ₂ (t • b₂)
  endB₁ : ∀ t, |t - Real.pi| < δ → (Real.pi - t) • b₁ ∈ U₁ ∧ γB t = φ₁ ((Real.pi - t) • b₁)

theorem exists_cornerChart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {w : Fin (D.chart q hq).k → ℝ}
    (hw : w ∈ D.sardZeros p hq ε c hp) (htr : D.isSardTransverse p hq ε c hp) :
    ∃ U φ, D.IsCornerChart c hp hq ε ℓ
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) U φ := by
  classical
  have _ : 2 ≤ ℓ := hℓ
  obtain ⟨hε, -, -, hrmp, hrmq, hpq, hU⟩ := hv
  obtain ⟨⟨hw0, hland⟩, -, hSw⟩ := hw
  have hw0' : w ≠ 0 := hw0
  have hpab : f p ∈ Ioo a b := D.f_mem_Ioo p hp
  have hqab : f q ∈ Ioo a b := D.f_mem_Ioo q hq
  have hrmp0 := D.rm_pos p hp
  have hrmq0 := D.rm_pos q hq
  have hrmpR : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hrmqR : D.rm q hq ≤ (D.chart q hq).R := (D.hrm q hq).2
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by nlinarith
  have hRp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by nlinarith
  have hUL : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hU y ⟨by linarith [hy.1], hy.2⟩
  have hUR : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hU y ⟨hy.1, by linarith [hy.2]⟩
  have hac : a ≤ c := by linarith [hpab.1]
  have hcb : c ≤ b := by linarith [hqab.2]
  have hfP : ∀ u : Fin (D.chart q hq).k → ℝ, u ≠ 0 →
      f (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u))) = c := by
    intro u hu
    have hfx₁ : f ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)) = f q - ε :=
      (D.chart q hq).f_chart_of_mem_leftModelSphere hRq
        ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hu)
    have := f_flow_eq_sub_of_levels hf (D := D)
      (x := (D.chart q hq).χ ((D.chart q hq).sphereParam ε u)) (T := f q - ε - c)
      (by rw [hfx₁]; exact ⟨by linarith [hpab.1], by linarith [hqab.2]⟩)
      (by rw [hfx₁, sub_sub_cancel]; exact ⟨hac, hcb⟩) (by
        intro y hy
        rw [hfx₁, sub_sub_cancel, uIcc_of_ge hc₂.le] at hy
        exact hU y ⟨by linarith [hy.1], hy.2⟩) _ right_mem_uIcc
    rw [this, hfx₁]; ring
  have hPL : ∀ u : Fin (D.chart q hq).k → ℝ, u ≠ 0 →
      D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)) ∈
        D.leftSphere q hq ε c := fun u hu =>
    ⟨_, ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hu, rfl⟩, rfl⟩
  have hLP : ∀ u : Fin (D.chart q hq).k → ℝ, u ≠ 0 →
      D.leftCoord q hq ε (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))
        = 0 := fun u hu =>
    ((mem_leftSphere_iff_coord hf D hq hε (by linarith) hac hc₂.le hUL (hfP u hu)).1
      (hPL u hu)).1
  have hRP : ∀ u : Fin (D.chart q hq).k → ℝ, u ≠ 0 →
      D.rightCoord p hp ε (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))
        = negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u)) := by
    intro u hu
    unfold rightCoord landing
    rw [hfP u hu]
  set x := D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) with hx
  have hfx : f x = c := hfP w hw0'
  have hxL : x ∈ D.leftSphere q hq ε c := hPL w hw0'
  have hfland : f (D.landing p hq ε c ε w) = f p + ε :=
    f_landing hp hf hε hε hRq hc₁.le hc₂.le hU hw0'
  obtain ⟨Y, hYR, hYland⟩ := hland
  have hYR' : morseNorm n Y ≤ (D.chart p hp).R := le_of_lt hYR
  have hYsymm : (D.chart p hp).χ.symm (D.landing p hq ε c ε w) = Y := by
    rw [← hYland, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc Y hYR')]
  have hYnf : morseNormalForm (D.chart p hp).hk (f p) Y = f p + ε := by
    rw [← (D.chart p hp).hnorm Y hYR', hYland, hfland]
  have hYv : posPart (D.chart p hp).hk Y ≠ 0 :=
    ModelField.posPart_ne_zero_of_lt_nf (D.chart p hp).hk (c := f p) (by rw [hYnf]; linarith)
  have hYu : negPart (D.chart p hp).hk Y = 0 := by
    have h0 : ModelField.scaledNegativePart (D.chart p hp).hk Y = 0 := by
      have : D.sardMap p hq ε c ε hp w = 0 := hSw
      unfold sardMap at this
      rwa [hYsymm] at this
    exact (ModelField.scaledNegativePart_eq_zero_iff (D.chart p hp).hk hYv).1 h0
  have hYsph : Y ∈ (D.chart p hp).rightModelSphere ε := by
    refine ⟨hYu, ?_⟩
    have := hYnf
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hYu,
      norm_zero] at this
    linarith
  have hxR : x ∈ D.rightSphere p hp ε c := by
    rw [D.mem_rightSphere_iff p hp ε c]
    exact ⟨Y, hYsph, hYland⟩
  have hxL' := (mem_leftSphere_iff_coord hf D hq hε (by linarith) hac hc₂.le hUL hfx).1 hxL
  have hxR' := (mem_rightSphere_iff_coord hf D hp hε (by linarith) hc₁.le hcb hUR hfx).1 hxR
  obtain ⟨OL, hOL, hSL, hLsm, hLd⟩ :=
    D.leftCoord_submersion hf hq hε (by linarith) hac hc₂.le hUL
  obtain ⟨OR, hOR, hSR, hRsm, hRd⟩ :=
    D.rightCoord_submersion hf hp hε (by linarith) hc₁.le hcb hUR
  have hxO : x ∈ OL ∩ OR := ⟨hSL hxL, hSR hxR⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : M → (Fin n → ℝ), ∀ z j, Ψ z j =
      if h : (j : ℕ) < (D.chart p hp).k then D.rightCoord p hp ε z ⟨j, h⟩
      else if h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k then
        D.leftCoord q hq ε z ⟨(j : ℕ) - (D.chart p hp).k, h'⟩
      else f z - c :=
    ⟨fun z j => if h : (j : ℕ) < (D.chart p hp).k then D.rightCoord p hp ε z ⟨j, h⟩
      else if h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k then
        D.leftCoord q hq ε z ⟨(j : ℕ) - (D.chart p hp).k, h'⟩
      else f z - c, fun _ _ => rfl⟩
  have hΨsm : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ Ψ (OL ∩ OR) := by
    refine contMDiffOn_pi_space.2 fun j => ?_
    simp_rw [hΨ]
    by_cases h : (j : ℕ) < (D.chart p hp).k
    · simp only [h, ↓reduceDIte]
      exact (EuclideanSpace.proj (𝕜 := ℝ) (⟨j, h⟩ : Fin (D.chart p hp).k)).contDiff.contMDiff.comp_contMDiffOn
        (hRsm.mono inter_subset_right)
    · simp only [h, ↓reduceDIte]
      by_cases h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k
      · simp only [h', ↓reduceDIte]
        exact (EuclideanSpace.proj (𝕜 := ℝ)
          (⟨(j : ℕ) - (D.chart p hp).k, h'⟩ : Fin (n - (D.chart q hq).k))).contDiff.contMDiff.comp_contMDiffOn
          (hLsm.mono inter_subset_left)
      · simp only [h', ↓reduceDIte]
        exact hf.contMDiffOn.sub contMDiffOn_const
  have hS0 : IsOpen ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      (hOL.inter hOR)
  have hx₀S : extChartAt I x x ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR) :=
    ⟨mem_extChartAt_target x, by rw [mem_preimage, extChartAt_to_inv]; exact hxO⟩
  have hsymmS : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ (extChartAt I x).symm
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    (contMDiffOn_extChartAt_symm x).mono inter_subset_left
  have hmapS : MapsTo (extChartAt I x).symm
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) (OL ∩ OR) :=
    fun z hz => hz.2
  have hΨc : ContDiffOn ℝ ∞ (Ψ ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    contMDiffOn_iff_contDiffOn.1 (hΨsm.comp hsymmS hmapS)
  have hRc : ContDiffOn ℝ ∞ (D.rightCoord p hp ε ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    contMDiffOn_iff_contDiffOn.1 ((hRsm.mono inter_subset_right).comp hsymmS hmapS)
  have hLc : ContDiffOn ℝ ∞ (D.leftCoord q hq ε ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    contMDiffOn_iff_contDiffOn.1 ((hLsm.mono inter_subset_left).comp hsymmS hmapS)
  have hFc : ContDiffOn ℝ ∞ (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) :=
    contMDiffOn_iff_contDiffOn.1 ((hf.contMDiffOn (s := univ)).comp hsymmS (fun _ _ => mem_univ _))
  have hnx₀ := hS0.mem_nhds hx₀S
  have hRcd := (hRc.contDiffAt hnx₀).differentiableAt (by simp)
  have hLcd := (hLc.contDiffAt hnx₀).differentiableAt (by simp)
  have hFcd := (hFc.contDiffAt hnx₀).differentiableAt (by simp)
  have hΨcd := (hΨc.contDiffAt hnx₀).differentiableAt (by simp)
  have hmf : ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (g : M → E'),
      MDifferentiableAt I 𝓘(ℝ, E') g x → ∀ v : Fin n → ℝ,
        mfderiv I 𝓘(ℝ, E') g x v = fderiv ℝ (g ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
    intro E' _ _ g hg v
    rw [hg.mfderiv]
    simp [writtenInExtChartAt, I.range_eq_univ, fderivWithin_univ]
    rfl
  have hFm : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := (hf x).mdifferentiableAt (by simp)
  have hLm : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
      (D.leftCoord q hq ε) x :=
    (hLsm.contMDiffAt (hOL.mem_nhds hxO.1)).mdifferentiableAt (by simp)
  have hRm : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
      (D.rightCoord p hp ε) x :=
    (hRsm.contMDiffAt (hOR.mem_nhds hxO.2)).mdifferentiableAt (by simp)
  have hT2 : ∀ r : EuclideanSpace ℝ (Fin (D.chart p hp).k), ∃ v : Fin n → ℝ,
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v = 0 ∧
      fderiv ℝ (D.leftCoord q hq ε ∘ (extChartAt I x).symm) (extChartAt I x x) v = 0 ∧
      fderiv ℝ (D.rightCoord p hp ε ∘ (extChartAt I x).symm) (extChartAt I x x) v = r := by
    intro r
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((D.chart q hq).sphereParam ε) w :=
      contMDiffAt_iff_contDiffAt.2 ((D.chart q hq).contDiffAt_sphereParam ε hw0')
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart q hq).χ
        ((D.chart q hq).sphereParam ε w) :=
      (D.chart q hq).contMDiffAt_chart
        ((D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq hw0'))
    have hfl1 : ContMDiffAt I I ∞ (D.flow (f q - ε - c))
        ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := (D.contMDiff_flow _).contMDiffAt
    have c1 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (fun u => (D.chart q hq).χ ((D.chart q hq).sphereParam ε u)) w := hχq.comp w hsp
    have hP : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (fun u => D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u))) w :=
      hfl1.comp w c1
    have hfl2 : ContMDiffAt I I ∞ (D.flow (c - (f p + ε))) x := (D.contMDiff_flow _).contMDiffAt
    have hland' : D.landing p hq ε c ε w ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
      (D.chart p hp).image_lt_subset_image_ball (D.chart p hp).hRR'.le ⟨Y, hYR, hYland⟩
    have hsymm : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (D.chart p hp).χ.symm
        (D.flow (c - (f p + ε)) x) := (D.chart p hp).contMDiffAt_symm hland'
    have c3 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (fun u => D.flow (c - (f p + ε))
          (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) w :=
      hfl2.comp w hP
    have c4 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun u => (D.chart p hp).χ.symm (D.landing p hq ε c ε u)) w := hsymm.comp w c3
    have hYd : DifferentiableAt ℝ (fun u => (D.chart p hp).χ.symm (D.landing p hq ε c ε u)) w :=
      (contMDiffAt_iff_contDiffAt.1 c4).differentiableAt (by simp)
    have hNd : DifferentiableAt ℝ
        (fun u => negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u))) w :=
      (ModelField.negPartL (D.chart p hp).hk).differentiableAt.comp w hYd
    have hsd : DifferentiableAt ℝ
        (fun u => ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u))‖) w :=
      DifferentiableAt.norm ℝ ((ModelField.posPartL (D.chart p hp).hk).differentiableAt.comp w hYd)
        (by change posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w)) ≠ 0
            rw [hYsymm]; exact hYv)
    have hSeq : D.sardMap p hq ε c ε hp =
        (fun u => ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u))‖) •
        (fun u => negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u))) := by
      funext u; rfl
    have hdS := fderiv_smul hsd hNd
    rw [← hSeq] at hdS
    have hN0 : negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w)) = 0 := by
      rw [hYsymm]; exact hYu
    simp only [hN0, ContinuousLinearMap.smulRight_zero, add_zero] at hdS
    have hs0 : ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w))‖ ≠ 0 := by
      rw [hYsymm]; exact norm_ne_zero_iff.2 hYv
    obtain ⟨u', hu'⟩ := htr w ⟨hw0, ⟨Y, hYR, hYland⟩⟩ hSw
      (‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε w))‖ • r)
    rw [hdS, smul_apply] at hu'
    have hNu : fderiv ℝ
        (fun u => negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u))) w u'
          = r := smul_right_injective _ hs0 hu'
    have hPcd : DifferentiableAt ℝ (fun u => extChartAt I x
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) w :=
      (contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt (x := x)).comp w hP)).differentiableAt
        (by simp)
    have hev : ∀ᶠ u in 𝓝 w, u ≠ 0 ∧
        D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)) ∈
          (extChartAt I x).source :=
      Filter.Eventually.and (isOpen_ne.mem_nhds hw0')
        (hP.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source x).mem_nhds
          (mem_extChartAt_source x)))
    refine ⟨fderiv ℝ (fun u => extChartAt I x
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) w u', ?_, ?_, ?_⟩
    · have h1 : (f ∘ (extChartAt I x).symm) ∘ (fun u => extChartAt I x
          (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) =ᶠ[𝓝 w]
          fun _ => c := by
        filter_upwards [hev] with u hu
        simp only [Function.comp_apply, (extChartAt I x).left_inv hu.2]
        exact hfP u hu.1
      have h2 := fderiv_comp w hFcd hPcd
      rw [h1.fderiv_eq, fderiv_fun_const, Pi.zero_apply] at h2
      have h3 := DFunLike.congr_fun h2 u'
      simpa using h3.symm
    · have h1 : (D.leftCoord q hq ε ∘ (extChartAt I x).symm) ∘ (fun u => extChartAt I x
          (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) =ᶠ[𝓝 w]
          fun _ => 0 := by
        filter_upwards [hev] with u hu
        simp only [Function.comp_apply, (extChartAt I x).left_inv hu.2]
        exact hLP u hu.1
      have h2 := fderiv_comp w hLcd hPcd
      rw [h1.fderiv_eq, fderiv_fun_const, Pi.zero_apply] at h2
      have h3 := DFunLike.congr_fun h2 u'
      simpa using h3.symm
    · have h1 : (D.rightCoord p hp ε ∘ (extChartAt I x).symm) ∘ (fun u => extChartAt I x
          (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε u)))) =ᶠ[𝓝 w]
          fun u => negPart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq ε c ε u)) := by
        filter_upwards [hev] with u hu
        simp only [Function.comp_apply, (extChartAt I x).left_inv hu.2]
        exact hRP u hu.1
      have h2 := fderiv_comp w hRcd hPcd
      rw [h1.fderiv_eq] at h2
      have h3 := DFunLike.congr_fun h2 u'
      rw [← hNu, h3]
      rfl
  have hAj : ∀ (v : Fin n → ℝ) (j : Fin n),
      fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x) v j =
        if h : (j : ℕ) < (D.chart p hp).k then
          fderiv ℝ (D.rightCoord p hp ε ∘ (extChartAt I x).symm) (extChartAt I x x) v ⟨j, h⟩
        else if h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k then
          fderiv ℝ (D.leftCoord q hq ε ∘ (extChartAt I x).symm) (extChartAt I x x) v
            ⟨(j : ℕ) - (D.chart p hp).k, h'⟩
        else fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
    intro v j
    have hj := (hasFDerivAt_pi'.1 hΨcd.hasFDerivAt) j
    by_cases h : (j : ℕ) < (D.chart p hp).k
    · simp only [h, ↓reduceDIte]
      have hj' : HasFDerivAt (fun z => (Ψ ∘ (extChartAt I x).symm) z j)
          ((EuclideanSpace.proj (𝕜 := ℝ) (⟨j, h⟩ : Fin (D.chart p hp).k)).comp
            (fderiv ℝ (D.rightCoord p hp ε ∘ (extChartAt I x).symm) (extChartAt I x x)))
          (extChartAt I x x) := by
        refine ((EuclideanSpace.proj (𝕜 := ℝ) (⟨j, h⟩ : Fin (D.chart p hp).k)).hasFDerivAt.comp
          (extChartAt I x x) hRcd.hasFDerivAt).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun z => ?_)
        simp only [Function.comp_apply, hΨ, h, ↓reduceDIte]
        rfl
      have := DFunLike.congr_fun (hj.unique hj') v
      simpa using this
    · simp only [h, ↓reduceDIte]
      by_cases h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k
      · simp only [h', ↓reduceDIte]
        have hj' : HasFDerivAt (fun z => (Ψ ∘ (extChartAt I x).symm) z j)
            ((EuclideanSpace.proj (𝕜 := ℝ)
              (⟨(j : ℕ) - (D.chart p hp).k, h'⟩ : Fin (n - (D.chart q hq).k))).comp
              (fderiv ℝ (D.leftCoord q hq ε ∘ (extChartAt I x).symm) (extChartAt I x x)))
            (extChartAt I x x) := by
          refine ((EuclideanSpace.proj (𝕜 := ℝ)
            (⟨(j : ℕ) - (D.chart p hp).k, h'⟩ : Fin (n - (D.chart q hq).k))).hasFDerivAt.comp
            (extChartAt I x x) hLcd.hasFDerivAt).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun z => ?_)
          simp only [Function.comp_apply, hΨ, h, h', ↓reduceDIte]
          rfl
        have := DFunLike.congr_fun (hj.unique hj') v
        simpa using this
      · simp only [h', ↓reduceDIte]
        have hj' : HasFDerivAt (fun z => (Ψ ∘ (extChartAt I x).symm) z j)
            (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)) (extChartAt I x x) := by
          refine (hFcd.hasFDerivAt.sub_const c).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun z => ?_)
          simp only [Function.comp_apply, hΨ, h, h', ↓reduceDIte]
        have := DFunLike.congr_fun (hj.unique hj') v
        simpa using this
  have hsurj : Function.Surjective (fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    intro t
    obtain ⟨hdF0, hLsurj⟩ := hLd x hxL
    have hv0 : ∃ v0 : Fin n → ℝ, fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v0 ≠ 0 := by
      by_contra hcon
      apply hdF0
      ext1 v
      rw [hmf ℝ f hFm v]
      by_contra h'
      exact hcon ⟨v, h'⟩
    obtain ⟨v0, hv0⟩ := hv0
    have hLsurj' : ∀ l : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)), ∃ v : Fin n → ℝ,
        fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v = 0 ∧
        fderiv ℝ (D.leftCoord q hq ε ∘ (extChartAt I x).symm) (extChartAt I x x) v = l := by
      intro l
      obtain ⟨v, h1, h2⟩ := hLsurj l
      rw [hmf ℝ f hFm v] at h1
      rw [hmf _ _ hLm v] at h2
      exact ⟨v, h1, h2⟩
    set Fd := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) with hFd
    set Ld := fderiv ℝ (D.leftCoord q hq ε ∘ (extChartAt I x).symm) (extChartAt I x x) with hLd'
    set Rd := fderiv ℝ (D.rightCoord p hp ε ∘ (extChartAt I x).symm) (extChartAt I x x) with hRd'
    have hv0' : Fd ((Fd v0)⁻¹ • v0) = 1 := by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv0]
    obtain ⟨v2, hv2F, hv2L⟩ := hLsurj' (WithLp.toLp 2 (fun i : Fin (n - (D.chart q hq).k) =>
        t ⟨(D.chart p hp).k + i, by have := i.isLt; omega⟩) -
      t ⟨n - 1, by omega⟩ • Ld ((Fd v0)⁻¹ • v0))
    obtain ⟨v3, hv3F, hv3L, hv3R⟩ := hT2 (WithLp.toLp 2 (fun i : Fin (D.chart p hp).k =>
        t ⟨i, by have := i.isLt; omega⟩) - Rd (t ⟨n - 1, by omega⟩ • ((Fd v0)⁻¹ • v0) + v2))
    refine ⟨t ⟨n - 1, by omega⟩ • ((Fd v0)⁻¹ • v0) + v2 + v3, ?_⟩
    funext j
    rw [hAj]
    by_cases h : (j : ℕ) < (D.chart p hp).k
    · simp only [h, ↓reduceDIte]
      rw [map_add, hv3R]
      simp
    · simp only [h, ↓reduceDIte]
      by_cases h' : (j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k
      · simp only [h', ↓reduceDIte]
        rw [map_add, hv3L, map_add, hv2L, map_smul]
        simp only [add_zero, add_sub_cancel]
        show t _ = t j
        congr 1
        ext
        simp only
        omega
      · simp only [h', ↓reduceDIte]
        rw [map_add, hv3F, map_add, hv2F, map_smul, hv0']
        simp only [add_zero, smul_eq_mul, mul_one]
        congr 1
        ext
        simp only
        omega
  have hinj : Function.Injective (fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x)) :=
    LinearMap.injective_iff_surjective
      (f := ((fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).2 hsurj
  obtain ⟨Aeq, hAeq⟩ : ∃ Aeq : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      (Aeq : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    ⟨(LinearEquiv.ofBijective ((fderiv ℝ (Ψ ∘ (extChartAt I x).symm) (extChartAt I x x) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
        ⟨hinj, hsurj⟩).toContinuousLinearEquiv, by ext1 v; rfl⟩
  have hstrict : HasStrictFDerivAt (Ψ ∘ (extChartAt I x).symm)
      (Aeq : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (extChartAt I x x) := by
    rw [hAeq]; exact (hΨc.contDiffAt hnx₀).hasStrictFDerivAt (by simp)
  obtain ⟨h, hcoe, hx₀h⟩ : ∃ h : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
      (h : (Fin n → ℝ) → (Fin n → ℝ)) = Ψ ∘ (extChartAt I x).symm ∧
        extChartAt I x x ∈ h.source :=
    ⟨_, hstrict.toOpenPartialHomeomorph_coe, hstrict.mem_toOpenPartialHomeomorph_source⟩
  have hΨx : Ψ x = 0 := by
    funext j
    rw [hΨ]
    split_ifs
    · rw [hxR'.1]; rfl
    · rw [hxL'.1]; rfl
    · rw [hfx, sub_self]; rfl
  have hh0 : h (extChartAt I x x) = 0 := by
    rw [hcoe]
    change Ψ ((extChartAt I x).symm (extChartAt I x x)) = 0
    rw [extChartAt_to_inv]; exact hΨx
  have hW : IsOpen (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
      fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u}) :=
    (hΨc.continuousOn_fderiv_of_isOpen hS0 (by simp)).isOpen_inter_preimage hS0 Units.isOpen
  have hx₀W : extChartAt I x x ∈ ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
      fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u} :=
    ⟨hx₀S, by rw [mem_preimage, ← hAeq]; exact ⟨Aeq.toUnit, rfl⟩⟩
  obtain ⟨ιL, hιL⟩ : ∃ ιL : (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ),
      ∀ y (j : Fin n), ιL y j = coordN y j :=
    ⟨ContinuousLinearMap.pi fun j : Fin n => if h : (j : ℕ) < n - 1 then
      ContinuousLinearMap.proj (⟨j, h⟩ : Fin (n - 1)) else 0, fun y j => by
        unfold coordN
        by_cases h : (j : ℕ) < n - 1
        · simp [h]
        · simp [h]⟩
  obtain ⟨π, hπc, hπ⟩ : ∃ π : (Fin n → ℝ) → (Fin (n - 1) → ℝ), Continuous π ∧
      ∀ z (i : Fin (n - 1)), π z i = z ⟨i, by omega⟩ :=
    ⟨fun z i => z ⟨i, by omega⟩, by fun_prop, fun _ _ => rfl⟩
  have hπι : ∀ y, π (ιL y) = y := by
    intro y; funext i
    rw [hπ, hιL]
    unfold coordN
    simp [i.isLt]
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin (n - 1) → ℝ) → M,
      φ = fun y => (extChartAt I x).symm (h.symm (ιL y)) := ⟨_, rfl⟩
  have hU1 : IsOpen (ιL ⁻¹' (h.target ∩ h.symm ⁻¹'
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u}))) :=
    (h.continuousOn_symm.isOpen_inter_preimage h.open_target hW).preimage ιL.continuous
  have hΨφ : ∀ y ∈ ιL ⁻¹' (h.target ∩ h.symm ⁻¹'
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u})), Ψ (φ y) = ιL y := by
    intro y hy
    have := h.right_inv hy.1
    rw [hcoe] at this
    rw [hφ]
    exact this
  have hsymmcd : ∀ a ∈ h.target ∩ h.symm ⁻¹'
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u}), ContDiffAt ℝ ∞ h.symm a := by
    rintro a ⟨ha, haW⟩
    obtain ⟨u, hu⟩ := haW.2
    have hcd : ContDiffAt ℝ ∞ (Ψ ∘ (extChartAt I x).symm) (h.symm a) :=
      hΨc.contDiffAt (hS0.mem_nhds haW.1)
    refine h.contDiffAt_symm ha (f₀' := ContinuousLinearEquiv.unitsEquiv ℝ _ u) ?_ ?_
    · rw [hcoe]
      change HasFDerivAt (Ψ ∘ (extChartAt I x).symm) (u : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) _
      rw [hu]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    · rw [hcoe]; exact hcd
  have hφsm1 : ContMDiffOn 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ φ (ιL ⁻¹' (h.target ∩ h.symm ⁻¹'
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u}))) := by
    rw [hφ]
    have h1 : ContDiffOn ℝ ∞ (fun y => h.symm (ιL y)) (ιL ⁻¹' (h.target ∩ h.symm ⁻¹'
        (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
          fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u}))) := fun y hy =>
      ((hsymmcd _ hy).comp y ιL.contDiff.contDiffAt).contDiffWithinAt
    exact (contMDiffOn_extChartAt_symm x).comp (contMDiffOn_iff_contDiffOn.2 h1)
      (fun y hy => hy.2.1.1)
  have hBq : IsOpen ((D.chart q hq).χ '' {w | morseNorm n w < D.rm q hq}) :=
    (D.chart q hq).isOpen_image_of_lt (D.rm_lt_R' q hq).le
  have hBp : IsOpen ((D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp}) :=
    (D.chart p hp).isOpen_image_of_lt (D.rm_lt_R' p hp).le
  set U1 := ιL ⁻¹' (h.target ∩ h.symm ⁻¹'
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (OL ∩ OR)) ∩
        fderiv ℝ (Ψ ∘ (extChartAt I x).symm) ⁻¹' {u | IsUnit u})) with hU1def
  have hUo : IsOpen ((U1 ∩ φ ⁻¹' (D.flow (c - (f q - ε)) ⁻¹'
      ((D.chart q hq).χ '' {w | morseNorm n w < D.rm q hq}))) ∩
      φ ⁻¹' (D.flow (c - (f p + ε)) ⁻¹' ((D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp}))) :=
    (hφsm1.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hφsm1.continuousOn.isOpen_inter_preimage hU1 (hBq.preimage (D.continuous_flow _)))
      (hBp.preimage (D.continuous_flow _))
  have hφ0 : φ 0 = x := by
    rw [hφ]
    simp only [map_zero]
    rw [← hh0, h.left_inv hx₀h, extChartAt_to_inv]
  have h0U1 : (0 : Fin (n - 1) → ℝ) ∈ U1 := by
    refine ⟨?_, ?_⟩
    · rw [map_zero, ← hh0]; exact h.map_source hx₀h
    · rw [mem_preimage, map_zero, ← hh0, h.left_inv hx₀h]; exact hx₀W
  have hlevel : ∀ y ∈ U1, f (φ y) = c := by
    intro y hy
    have e1 := congrFun (hΨφ y hy) ⟨n - 1, by omega⟩
    rw [hΨ, hιL] at e1
    have h1 : ¬ (n - 1 < (D.chart p hp).k) := by omega
    have h2 : ¬ (n - 1 - (D.chart p hp).k < n - (D.chart q hq).k) := by omega
    simp only [h1, h2, ↓reduceDIte] at e1
    have h3 : coordN y (n - 1) = 0 := by unfold coordN; simp
    rw [h3] at e1
    linarith
  have hcoordR : ∀ y ∈ U1, ∀ i : Fin (D.chart p hp).k,
      D.rightCoord p hp ε (φ y) i = coordN y i := by
    intro y hy i
    have e1 := congrFun (hΨφ y hy) ⟨i, by have := i.isLt; omega⟩
    rw [hΨ, hιL] at e1
    have h1 : (i : ℕ) < (D.chart p hp).k := i.isLt
    simp only [h1, ↓reduceDIte] at e1
    exact e1
  have hcoordL : ∀ y ∈ U1, ∀ i : Fin (n - (D.chart q hq).k),
      D.leftCoord q hq ε (φ y) i = coordN y (ℓ + i) := by
    intro y hy i
    have e1 := congrFun (hΨφ y hy) ⟨ℓ + i, by have := i.isLt; omega⟩
    rw [hΨ, hιL] at e1
    have h1 : ¬ (ℓ + (i : ℕ) < (D.chart p hp).k) := by omega
    have h2 : ℓ + (i : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k := by
      have := i.isLt; omega
    simp only [h1, h2, ↓reduceDIte] at e1
    rw [← e1]
    have h3 : (⟨ℓ + (i : ℕ) - (D.chart p hp).k, h2⟩ : Fin (n - (D.chart q hq).k)) = i :=
      Fin.ext (by simp only; omega)
    rw [h3]
  have hUU1 : (U1 ∩ φ ⁻¹' (D.flow (c - (f q - ε)) ⁻¹'
      ((D.chart q hq).χ '' {w | morseNorm n w < D.rm q hq}))) ∩
      φ ⁻¹' (D.flow (c - (f p + ε)) ⁻¹' ((D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp})) ⊆
      U1 := inter_subset_left.trans inter_subset_left
  have himm : ∀ y ∈ U1, Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ y) := by
    intro y hy
    have hφm : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I φ y :=
      (hφsm1.contMDiffAt (hU1.mem_nhds hy)).mdifferentiableAt (by simp)
    have hφO : φ y ∈ OL ∩ OR := by rw [hφ]; exact hy.2.1.2
    have hΨm : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) Ψ (φ y) :=
      (hΨsm.contMDiffAt ((hOL.inter hOR).mem_nhds hφO)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp y hΨm hφm
    have hev : (Ψ ∘ φ) =ᶠ[𝓝 y] ιL :=
      Filter.eventually_of_mem (hU1.mem_nhds hy) fun y' hy' => hΨφ y' hy'
    have h2 := hev.mfderiv_eq (I := 𝓘(ℝ, Fin (n - 1) → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))
    have h3 : mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) 𝓘(ℝ, Fin n → ℝ) ιL y = ιL := by
      rw [mfderiv_eq_fderiv]; exact ιL.fderiv
    have hkey : ∀ v, mfderiv I 𝓘(ℝ, Fin n → ℝ) Ψ (φ y)
        (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ y v) = ιL v := by
      intro v
      rw [← ContinuousLinearMap.comp_apply, ← hcomp, h2, h3]
      rfl
    intro v₁ v₂ hv
    have := hkey v₁
    rw [hv, hkey v₂] at this
    rw [← hπι v₁, ← hπι v₂, this]
  refine ⟨_, φ,
    { isOpen_U := hUo
      zero_mem := ⟨⟨h0U1, by rw [mem_preimage, hφ0]; exact hxL'.2⟩,
        by rw [mem_preimage, hφ0]; exact hxR'.2⟩
      smooth := hφsm1.mono hUU1
      immersion := fun y hy => himm y (hUU1 hy)
      inj := ?_
      level := fun y hy => hlevel y (hUU1 hy)
      center := hφ0
      coordR := fun y hy => hcoordR y (hUU1 hy)
      coordL := fun y hy => hcoordL y (hUU1 hy)
      memL := ?_
      memR := ?_
      open_image := ?_ }⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    rw [← hπι y₁, ← hπι y₂, ← hΨφ y₁ (hUU1 hy₁), ← hΨφ y₂ (hUU1 hy₂), heq]
  · intro y hy
    rw [mem_leftSphere_iff_coord hf D hq hε (by linarith) hac hc₂.le hUL (hlevel y (hUU1 hy))]
    constructor
    · rintro ⟨h0, -⟩ j hj
      by_cases hjn : j < n - 1
      · have e1 := hcoordL y (hUU1 hy) ⟨j - ℓ, by omega⟩
        rw [h0] at e1
        simp only at e1
        rw [show j = ℓ + (j - ℓ) by omega, ← e1]
        rfl
      · unfold coordN; simp [hjn]
    · intro hj
      refine ⟨?_, hy.1.2⟩
      refine PiLp.ext fun i => ?_
      rw [show (D.leftCoord q hq ε (φ y)).ofLp i = D.leftCoord q hq ε (φ y) i from rfl,
        hcoordL y (hUU1 hy) i, hj _ (by omega)]
      rfl
  · intro y hy
    rw [mem_rightSphere_iff_coord hf D hp hε (by linarith) hc₁.le hcb hUR (hlevel y (hUU1 hy))]
    constructor
    · rintro ⟨h0, -⟩ j hj
      have e1 := hcoordR y (hUU1 hy) ⟨j, by omega⟩
      rw [h0] at e1
      simp only at e1
      rw [← e1]
      rfl
    · intro hj
      refine ⟨?_, hy.2⟩
      refine PiLp.ext fun i => ?_
      rw [show (D.rightCoord p hp ε (φ y)).ofLp i = D.rightCoord p hp ε (φ y) i from rfl,
        hcoordR y (hUU1 hy) i, hj _ (by omega)]
      rfl
  · intro V hVU hV
    refine ⟨(extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (h.source ∩ h ⁻¹' (π ⁻¹' V)),
      (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
        (h.continuousOn.isOpen_inter_preimage h.open_source (hV.preimage hπc)), ?_⟩
    ext z
    constructor
    · rintro ⟨y, hyV, rfl⟩
      have hy1 := hUU1 (hVU hyV)
      have ht : h.symm (ιL y) ∈ (extChartAt I x).target := hy1.2.1.1
      have hez : extChartAt I x (φ y) = h.symm (ιL y) := by
        rw [hφ]; exact (extChartAt I x).right_inv ht
      refine ⟨⟨by rw [hφ]; exact (extChartAt I x).map_target ht, ?_, ?_⟩, hlevel y hy1⟩
      · rw [hez]; exact h.map_target hy1.1
      · rw [hez]
        change π (h (h.symm (ιL y))) ∈ V
        rw [h.right_inv hy1.1, hπι]
        exact hyV
    · rintro ⟨⟨hzs, hzh, hzV⟩, hzc⟩
      refine ⟨π (h (extChartAt I x z)), hzV, ?_⟩
      have hhz : h (extChartAt I x z) = Ψ z := by
        rw [hcoe]
        change Ψ ((extChartAt I x).symm (extChartAt I x z)) = Ψ z
        rw [(extChartAt I x).left_inv hzs]
      have hιeq : ιL (π (h (extChartAt I x z))) = h (extChartAt I x z) := by
        funext j
        rw [hιL]
        by_cases hj : (j : ℕ) < n - 1
        · unfold coordN
          simp only [hj, ↓reduceDIte, hπ]
        · unfold coordN
          simp only [hj, ↓reduceDIte]
          rw [hhz, hΨ]
          have h1 : ¬ ((j : ℕ) < (D.chart p hp).k) := by omega
          have h2 : ¬ ((j : ℕ) - (D.chart p hp).k < n - (D.chart q hq).k) := by omega
          simp only [h1, h2, ↓reduceDIte]
          have : f z = c := hzc
          rw [this, sub_self]
      rw [hφ]
      change (extChartAt I x).symm (h.symm (ιL (π (h (extChartAt I x z))))) = z
      rw [hιeq, h.left_inv hzh, (extChartAt I x).left_inv hzs]

theorem exists_whitney_arcs (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {w₁ w₂ : Fin (D.chart q hq).k → ℝ}
    (hw₁ : w₁ ∈ D.sardZeros p hq ε c hp) (hw₂ : w₂ ∈ D.sardZeros p hq ε c hp) (hne : w₁ ≠ w₂)
    (hfin : (D.sardZeros p hq ε c hp).Finite) {U₁ U₂ : Set (Fin (n - 1) → ℝ)}
    {φ₁ φ₂ : (Fin (n - 1) → ℝ) → M}
    (hφ₁ : D.IsCornerChart c hp hq ε ℓ
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₁))) U₁ φ₁)
    (hφ₂ : D.IsCornerChart c hp hq ε ℓ
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₂))) U₂ φ₂) :
    ∃ (γA γB : ℝ → M) (a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ) (δ : ℝ),
      D.IsWhitneyArcs c hp hq ε ℓ φ₁ φ₂ U₁ U₂ γA γB a₁ a₂ b₁ b₂ δ := by
  have arcGL : ∀ (N : ℕ), 3 ≤ N → ∀ (Φ : EuclideanSpace ℝ (Fin N) → M)
      (G : M → EuclideanSpace ℝ (Fin N)) (O S T F : Set M) (x₁ x₂ : M),
      (∀ v : EuclideanSpace ℝ (Fin N), v ≠ 0 → ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ Φ v) →
      (∀ v : EuclideanSpace ℝ (Fin N), v ≠ 0 → Φ v ∈ S) →
      IsOpen O → S ⊆ O → ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G O →
      (∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → G (Φ v) = v) →
      (∀ z ∈ S, ‖G z‖ = 1 ∧ Φ (G z) = z) →
      x₁ ∈ S → x₂ ∈ S → x₁ ≠ x₂ → x₁ ∈ T → x₂ ∈ T → F.Finite →
      (∀ z ∈ S, z ∈ T → z = x₁ ∨ z = x₂ ∨ z ∈ F) →
      ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ (∀ t ∈ Icc (-1 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I γ t 1 ≠ 0) ∧
        InjOn γ (Icc (-1) 1) ∧ (∀ t, γ t ∈ S) ∧ (∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ T ↔ t = -1 ∨ t = 1) ∧
        γ (-1) = x₁ ∧ γ 1 = x₂ := by
    clear hφ₁ hφ₂ hfin hne hw₁ hw₂ hc₁ hc₂ hv hkp hkq h6 hℓ hℓn hf
    intro N hN Φ G O S T F x₁ x₂ hΦ hΦS hO hSO hG hGΦ hΦG hx₁S hx₂S hx₁₂ hx₁T hx₂T hF hST
    classical
    have hFS : (F ∩ S ∩ {z | z ≠ x₁ ∧ z ≠ x₂}).Finite := hF.subset (fun z hz => hz.1.1)
    set S' : Finset (EuclideanSpace ℝ (Fin N)) := hFS.toFinset.image G with hS'
    have hG1 := hΦG x₁ hx₁S
    have hG2 := hΦG x₂ hx₂S
    have hz₁₂ : G x₁ ≠ G x₂ := fun h => hx₁₂ (by rw [← hG1.2, h, hG2.2])
    have hzS : ∀ x ∈ S, (x = x₁ ∨ x = x₂) → G x ∉ S' := by
      intro x hx hxx hmem
      rw [hS', Finset.mem_image] at hmem
      obtain ⟨z, hz, hzG⟩ := hmem
      rw [Set.Finite.mem_toFinset] at hz
      have : z = x := by rw [← (hΦG z hz.1.2).2, hzG, (hΦG x hx).2]
      subst this
      rcases hxx with h | h
      · exact hz.2.1 h
      · exact hz.2.2 h
    obtain ⟨g, hg, hg1, hgm1, hgp1, hginj, hgd, hgS⟩ := exists_sphere_arc hN S' hG1.1 hG2.1 hz₁₂
      (hzS x₁ hx₁S (Or.inl rfl)) (hzS x₂ hx₂S (Or.inr rfl))
    have hg0 : ∀ t, g t ≠ 0 := fun t h => by
      have := hg1 t
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hγS : ∀ t, Φ (g t) ∈ S := fun t => hΦS _ (hg0 t)
    have hGγ : ∀ t, G (Φ (g t)) = g t := fun t => hGΦ _ (hg1 t)
    have hγsm : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (Φ ∘ g) t := fun t =>
      (hΦ _ (hg0 t)).comp t (contMDiff_iff_contDiff.2 hg).contMDiffAt
    have hIcc : Icc (-1 : ℝ) 1 ⊆ Icc (-2) 2 := Icc_subset_Icc (by norm_num) (by norm_num)
    refine ⟨Φ ∘ g, fun t => hγsm t, ?_, ?_, hγS, ?_, ?_, ?_⟩
    · intro t _ h0
      have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) G (Φ (g t)) :=
        (hG.contMDiffAt (hO.mem_nhds (hSO (hγS t)))).mdifferentiableAt (by simp)
      have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I (Φ ∘ g) t := (hγsm t).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp t hGd hγd
      have heq : G ∘ (Φ ∘ g) = g := funext hGγ
      rw [heq, mfderiv_eq_fderiv] at hcomp
      have h1 : fderiv ℝ g t 1 = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) G (Φ (g t))
          (mfderiv 𝓘(ℝ, ℝ) I (Φ ∘ g) t 1) := by
        exact DFunLike.congr_fun hcomp 1
      have h2 : mfderiv 𝓘(ℝ, ℝ) I (Φ ∘ g) t 1 = 0 := h0
      rw [h2, map_zero] at h1
      apply hgd t
      rw [← fderiv_apply_one_eq_deriv]
      exact h1
    · intro s hs t ht hst
      apply hginj (hIcc hs) (hIcc ht)
      have := congrArg G hst
      simpa only [Function.comp_apply, hGγ] using this
    · intro t ht
      constructor
      · intro hT
        by_cases h1 : (Φ ∘ g) t = x₁
        · left
          apply hginj (hIcc ht) (by norm_num)
          rw [hgm1, ← hGγ t]
          exact congrArg G h1
        by_cases h2 : (Φ ∘ g) t = x₂
        · right
          apply hginj (hIcc ht) (by norm_num)
          rw [hgp1, ← hGγ t]
          exact congrArg G h2
        exfalso
        rcases hST _ (hγS t) hT with h | h | h
        · exact h1 h
        · exact h2 h
        apply hgS t (hIcc ht)
        rw [← hGγ t, hS', Finset.mem_image]
        exact ⟨Φ (g t), (Set.Finite.mem_toFinset _).2 ⟨⟨h, hγS t⟩, h1, h2⟩, rfl⟩
      · rintro (h | h)
        · subst h; simp only [Function.comp_apply, hgm1, hG1.2]; exact hx₁T
        · subst h; simp only [Function.comp_apply, hgp1, hG2.2]; exact hx₂T
    · simp only [Function.comp_apply, hgm1, hG1.2]
    · simp only [Function.comp_apply, hgp1, hG2.2]
  have arcSL : ∀ (m : ℕ) (γ : ℝ → M) (t₀ : ℝ) (φ : (Fin m → ℝ) → M) (U : Set (Fin m → ℝ))
      (Ψ : M → (Fin m → ℝ)) (O W : Set M) (π : Fin m → Prop) (S T : Set M) (ρ₁ : ℝ),
      IsOpen U → (0 : Fin m → ℝ) ∈ U → ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞ φ U →
      (∀ y ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ y)) → InjOn φ U →
      IsOpen O → φ 0 ∈ O → ContMDiffOn I 𝓘(ℝ, Fin m → ℝ) ∞ Ψ O → (∀ y ∈ U, Ψ (φ y) = y) →
      IsOpen W → φ 0 ∈ W → W ∩ S ⊆ φ '' U →
      (∀ y ∈ U, φ y ∈ S ↔ ∀ j, π j → y j = 0) → (∀ y ∈ U, φ y ∈ T ↔ ∀ j, ¬ π j → y j = 0) →
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → (∀ t ∈ Icc (-1 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I γ t 1 ≠ 0) →
      InjOn γ (Icc (-1) 1) → (∀ t, γ t ∈ S) → (∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ T ↔ t = -1 ∨ t = 1) →
      (t₀ = -1 ∨ t₀ = 1) → γ t₀ = φ 0 → 0 < ρ₁ →
      ∃ (γ' : ℝ → M) (a : Fin m → ℝ) (δ : ℝ), ContMDiff 𝓘(ℝ, ℝ) I ∞ γ' ∧
        (∀ t ∈ Icc (-1 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I γ' t 1 ≠ 0) ∧
        InjOn γ' (Icc (-1) 1) ∧ (∀ t, γ' t ∈ S) ∧
        (∀ t ∈ Icc (-1 : ℝ) 1, γ' t ∈ T ↔ t = -1 ∨ t = 1) ∧
        a ≠ 0 ∧ (∀ j, π j → a j = 0) ∧ 0 < δ ∧ 2 * δ ≤ ρ₁ ∧
        (∀ t, |t - t₀| < δ → (t - t₀) • a ∈ U ∧ γ' t = φ ((t - t₀) • a)) ∧
        (∀ t, ρ₁ ≤ |t - t₀| → γ' t = γ t) := by
    clear hφ₁ hφ₂ hfin hne hw₁ hw₂ hc₁ hc₂ hv hkp hkq h6 hℓ hℓn hf arcGL
    intro m γ t₀ φ U Ψ O W π S T ρ₁ hU h0U hφ himm hinj hO hφO hΨ hΨφ hW hφW hWS hPS hQT hγ hγimm
      hγinj hγS hγT ht₀ hγt₀ hρ₁
    classical
    have ht₀I : t₀ ∈ Icc (-1 : ℝ) 1 := by rcases ht₀ with h | h <;> subst h <;> norm_num
    have hOpen : ∀ r : ℝ, IsOpen {t : ℝ | |t - t₀| < r} := fun r =>
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    have hOpen' : ∀ r : ℝ, IsOpen {t : ℝ | r < |t - t₀|} := fun r =>
      isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
    have hself : ∀ r : ℝ, 0 < r → |t₀ - t₀| < r := fun r hr => by simpa using hr
    obtain ⟨r₀, hr₀, hr₀sub⟩ : ∃ r₀ > 0, ∀ t, |t - t₀| < r₀ → γ t ∈ O ∩ W := by
      have hopen : IsOpen (γ ⁻¹' (O ∩ W)) := (hO.inter hW).preimage hγ.continuous
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen t₀
        (by rw [mem_preimage, hγt₀]; exact ⟨hφO, hφW⟩)
      exact ⟨r, hr, fun t ht => hball (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)⟩
    set α : ℝ → (Fin m → ℝ) := fun t => Ψ (γ t) with hαdef
    have hα1 : ∀ t, |t - t₀| < r₀ → ContDiffAt ℝ ∞ α t := by
      intro t ht
      have h1 : ContMDiffAt I 𝓘(ℝ, Fin m → ℝ) ∞ Ψ (γ t) :=
        hΨ.contMDiffAt (hO.mem_nhds (hr₀sub t ht).1)
      exact contMDiffAt_iff_contDiffAt.1 (h1.comp t (hγ t))
    have hα2 : ∀ t, |t - t₀| < r₀ → α t ∈ U ∧ γ t = φ (α t) ∧ ∀ j, π j → α t j = 0 := by
      intro t ht
      obtain ⟨y, hyU, hy⟩ := hWS ⟨(hr₀sub t ht).2, hγS t⟩
      have hαy : α t = y := by simp only [hαdef, ← hy, hΨφ y hyU]
      rw [hαy]
      exact ⟨hyU, hy.symm, (hPS y hyU).1 (by rw [hy]; exact hγS t)⟩
    have hα0 : α t₀ = 0 := by simp only [hαdef, hγt₀, hΨφ 0 h0U]
    obtain ⟨a, ha_def⟩ : ∃ a, a = deriv α t₀ := ⟨_, rfl⟩
    have hαd : ∀ t, |t - t₀| < r₀ → HasDerivAt α (deriv α t) t := fun t ht =>
      ((hα1 t ht).differentiableAt (by simp)).hasDerivAt
    have haP : ∀ j, π j → a j = 0 := by
      intro j hj
      have h1 : HasDerivAt (fun t => α t j) (a j) t₀ := by
        rw [ha_def]; exact (hasDerivAt_pi.1 (hαd t₀ (hself r₀ hr₀))) j
      have hev : (fun t => α t j) =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
        filter_upwards [(hOpen r₀).mem_nhds (hself r₀ hr₀)] with t ht
        exact (hα2 t ht).2.2 j hj
      have h2 : HasDerivAt (fun t => α t j) 0 t₀ :=
        (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hev
      exact h1.unique h2
    have hmf : ∀ (β : ℝ → Fin m → ℝ) (g : ℝ → M) (t : ℝ) (v : Fin m → ℝ), β t ∈ U →
        g =ᶠ[𝓝 t] (fun s => φ (β s)) → HasDerivAt β v t →
        mfderiv 𝓘(ℝ, ℝ) I g t 1 = mfderiv 𝓘(ℝ, Fin m → ℝ) I φ (β t) v := by
      intro β g t v hβU hev hβd
      rw [hev.mfderiv_eq]
      have hφd : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) I φ (β t) :=
        (hφ.contMDiffAt (hU.mem_nhds hβU)).mdifferentiableAt (by simp)
      have hβd' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin m → ℝ) β t :=
        mdifferentiableAt_iff_differentiableAt.2 hβd.differentiableAt
      have hc := mfderiv_comp t hφd hβd'
      change mfderiv 𝓘(ℝ, ℝ) I (φ ∘ β) t 1 = _
      rw [hc, mfderiv_eq_fderiv, hβd.hasFDerivAt.fderiv]
      exact congrArg (mfderiv 𝓘(ℝ, Fin m → ℝ) I φ (β t)) (one_smul ℝ v)
    have ha0 : a ≠ 0 := by
      intro ha
      have hev : γ =ᶠ[𝓝 t₀] fun s => φ (α s) := by
        filter_upwards [(hOpen r₀).mem_nhds (hself r₀ hr₀)] with t ht
        exact (hα2 t ht).2.1
      have h := hmf α γ t₀ a (by rw [hα0]; exact h0U) hev (ha_def ▸ hαd t₀ (hself r₀ hr₀))
      subst ha
      exact hγimm t₀ ht₀I (h.trans (map_zero _))
    obtain ⟨bmp, hbmp⟩ : ∃ b : ContDiffBump (0 : ℝ), b.rIn = 1 ∧ b.rOut = 2 :=
      ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl, rfl⟩
    have hbC : ContDiff ℝ ∞ (bmp : ℝ → ℝ) := bmp.contDiff
    have hbD : Differentiable ℝ (bmp : ℝ → ℝ) := hbC.differentiable (by simp)
    obtain ⟨L, hL⟩ : ∃ L, ∀ s, ‖deriv (bmp : ℝ → ℝ) s‖ ≤ L :=
      (hbC.continuous_deriv (by simp)).bounded_above_of_compact_support bmp.hasCompactSupport.deriv
    have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
    have hb1 : ∀ s : ℝ, |s| ≤ 1 → bmp s = 1 := fun s hs => bmp.one_of_mem_closedBall
      (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, hbmp.1]; exact hs)
    have hb0 : ∀ s : ℝ, 2 ≤ |s| → bmp s = 0 := fun s hs => bmp.zero_of_le_dist
      (by rw [dist_zero_right, Real.norm_eq_abs, hbmp.2]; exact hs)
    have hbLip : ∀ s s' : ℝ, |bmp s - bmp s'| ≤ L * |s - s'| := by
      intro s s'
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := (bmp : ℝ → ℝ)) (s := univ)
        (fun x _ => hbD x) (fun x _ => hL x) convex_univ (mem_univ s') (mem_univ s)
      simpa [Real.norm_eq_abs] using this
    have hbd0 : ∀ s : ℝ, 2 < |s| → deriv (bmp : ℝ → ℝ) s = 0 := by
      intro s hs
      have hev : (bmp : ℝ → ℝ) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        have : {u : ℝ | 2 < |u|} ∈ 𝓝 s := (isOpen_lt continuous_const continuous_abs).mem_nhds hs
        filter_upwards [this] with u hu
        exact hb0 u hu.le
      rw [hev.deriv_eq]
      exact deriv_const s 0
    set A := ‖a‖ with hA
    have hApos : 0 < A := norm_pos_iff.2 ha0
    set η := A / (4 * (1 + 2 * L)) with hη
    have h4L : (0 : ℝ) < 4 * (1 + 2 * L) := by linarith only [hL0]
    have hηpos : 0 < η := div_pos hApos h4L
    have hηL : η + 2 * L * η = A / 4 := by
      have h2 : η * (4 * (1 + 2 * L)) = A := div_mul_cancel₀ A h4L.ne'
      linarith only [h2]
    have hαcont : ContinuousAt (deriv α) t₀ := by
      have hon : ContDiffOn ℝ ∞ α {t | |t - t₀| < r₀} := fun t ht => (hα1 t ht).contDiffWithinAt
      exact (hon.continuousOn_deriv_of_isOpen (hOpen r₀) (by simp)).continuousAt
        ((hOpen r₀).mem_nhds (hself r₀ hr₀))
    obtain ⟨r', hr', hr'd⟩ := Metric.continuousAt_iff.1 hαcont η hηpos
    set r₁ := min r₀ r' with hr₁def
    have hr₁ : 0 < r₁ := lt_min hr₀ hr'
    have hr₁r₀ : ∀ t, |t - t₀| < r₁ → |t - t₀| < r₀ := fun t ht => lt_of_lt_of_le ht (min_le_left _ _)
    have hr₁d : ∀ t, |t - t₀| < r₁ → ‖deriv α t - a‖ ≤ η := by
      intro t ht
      have := hr'd (show dist t t₀ < r' by
        rw [Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_right _ _))
      rw [dist_eq_norm, ← ha_def] at this
      exact this.le
    set rr : ℝ → (Fin m → ℝ) := fun t => α t - (t - t₀) • a with hrr
    have hrrd : ∀ t, |t - t₀| < r₀ → HasDerivAt rr (deriv α t - a) t := by
      intro t ht
      have h := (hαd t ht).sub (((hasDerivAt_id t).sub_const t₀).smul_const a)
      rw [one_smul] at h
      exact h
    have hrr0 : rr t₀ = 0 := by simp [hrr, hα0]
    have hball : {u : ℝ | |u - t₀| < r₁} = Metric.ball t₀ r₁ := by
      ext u; simp [Metric.mem_ball, Real.dist_eq]
    have hrrLip : ∀ s t, |s - t₀| < r₁ → |t - t₀| < r₁ → ‖rr t - rr s‖ ≤ η * |t - s| := by
      intro s t hs ht
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := rr) (s := {u : ℝ | |u - t₀| < r₁})
        (C := η) (fun x hx => (hrrd x (hr₁r₀ x hx)).differentiableAt)
        (fun x hx => by rw [(hrrd x (hr₁r₀ x hx)).deriv]; exact hr₁d x hx)
        (by rw [hball]; exact convex_ball t₀ r₁) hs ht
      simpa [Real.norm_eq_abs] using this
    have hrrb : ∀ t, |t - t₀| < r₁ → ‖rr t‖ ≤ η * |t - t₀| := fun t ht => by
      have := hrrLip t₀ t (hself r₁ hr₁) ht
      rwa [hrr0, sub_zero] at this
    set K := γ '' (Icc (-1 : ℝ) 1 ∩ {t | r₁ ≤ |t - t₀|}) with hK
    have hKc : IsCompact K :=
      (isCompact_Icc.inter_right (isClosed_le continuous_const
        (continuous_abs.comp (continuous_id.sub continuous_const)))).image hγ.continuous
    have h0K : φ 0 ∉ K := by
      rintro ⟨t, ⟨htI, htr⟩, hγt⟩
      have := hγinj htI ht₀I (hγt.trans hγt₀.symm)
      subst this
      simp only [sub_self, abs_zero, Set.mem_ofPred_eq] at htr
      linarith only [htr, hr₁]
    obtain ⟨rs, hrs, hrsU⟩ : ∃ rs > 0, Metric.ball (0 : Fin m → ℝ) rs ⊆ U ∩ φ ⁻¹' Kᶜ := by
      have h1 : U ∩ φ ⁻¹' Kᶜ ∈ 𝓝 (0 : Fin m → ℝ) := Filter.inter_mem (hU.mem_nhds h0U)
        ((hφ.continuousOn.continuousAt (hU.mem_nhds h0U)).preimage_mem_nhds
          (hKc.isClosed.isOpen_compl.mem_nhds h0K))
      exact Metric.mem_nhds_iff.1 h1
    set ρ := min (min (r₁ / 4) (ρ₁ / 2)) (min (rs / (4 * (A + η))) (1 / 2)) with hρ
    have hρpos : 0 < ρ := lt_min (lt_min (div_pos hr₁ four_pos) (div_pos hρ₁ two_pos))
      (lt_min (div_pos hrs (mul_pos four_pos (add_pos hApos hηpos))) (by norm_num))
    have hρr₁ : ρ ≤ r₁ / 4 := (min_le_left _ _).trans (min_le_left _ _)
    have hρρ₁ : ρ ≤ ρ₁ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hρrs : ρ ≤ rs / (4 * (A + η)) := (min_le_right _ _).trans (min_le_left _ _)
    have hρ1 : ρ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hρr₁' : 2 * ρ < r₁ := by linarith only [hρr₁, hr₁]
    have hρr₁'' : ρ < r₁ := by linarith only [hρr₁, hr₁]
    set lam : ℝ → ℝ := fun t => 1 - bmp ((t - t₀) / ρ) with hlam
    have hlam0 : ∀ t, |t - t₀| ≤ ρ → lam t = 0 := by
      intro t ht
      simp only [hlam]
      rw [hb1, sub_self]
      rw [abs_div, abs_of_pos hρpos, div_le_one hρpos]
      exact ht
    have hlam1 : ∀ t, 2 * ρ ≤ |t - t₀| → lam t = 1 := by
      intro t ht
      simp only [hlam]
      rw [hb0, sub_zero]
      rw [abs_div, abs_of_pos hρpos, le_div_iff₀ hρpos]
      exact ht
    have hlamb : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1 := fun t =>
      ⟨by simp only [hlam]; linarith only [bmp.le_one (x := (t - t₀) / ρ)],
       by simp only [hlam]; linarith only [bmp.nonneg (x := (t - t₀) / ρ)]⟩
    have hlamLip : ∀ s t, |lam t - lam s| ≤ L / ρ * |t - s| := by
      intro s t
      simp only [hlam]
      have h := hbLip ((s - t₀) / ρ) ((t - t₀) / ρ)
      have e1 : 1 - bmp ((t - t₀) / ρ) - (1 - bmp ((s - t₀) / ρ)) =
          bmp ((s - t₀) / ρ) - bmp ((t - t₀) / ρ) := by ring
      have e2 : (s - t₀) / ρ - (t - t₀) / ρ = -(t - s) / ρ := by ring
      rw [e1]
      rw [e2, abs_div, abs_neg, abs_of_pos hρpos] at h
      calc _ ≤ L * (|t - s| / ρ) := h
        _ = L / ρ * |t - s| := by ring
    set lamd : ℝ → ℝ := fun t => -(deriv (bmp : ℝ → ℝ) ((t - t₀) / ρ) * (1 / ρ)) with hlamd_def
    have hlamd : ∀ t, HasDerivAt lam (lamd t) t := by
      intro t
      have hb : HasDerivAt (bmp : ℝ → ℝ) (deriv (bmp : ℝ → ℝ) ((t - t₀) / ρ)) ((t - t₀) / ρ) :=
        (hbD _).hasDerivAt
      have hin : HasDerivAt (fun t => (t - t₀) / ρ) (1 / ρ) t :=
        ((hasDerivAt_id t).sub_const t₀).div_const ρ
      exact (hb.comp t hin).const_sub 1
    have hlamdb : ∀ t, |lamd t| ≤ L / ρ := by
      intro t
      simp only [hlamd_def, abs_neg, abs_mul, one_div, abs_inv, abs_of_pos hρpos]
      have := hL ((t - t₀) / ρ)
      rw [Real.norm_eq_abs] at this
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right this (inv_nonneg.2 hρpos.le)
    have hlamd0 : ∀ t, 2 * ρ < |t - t₀| → lamd t = 0 := by
      intro t ht
      simp only [hlamd_def]
      rw [hbd0, zero_mul, neg_zero]
      rw [abs_div, abs_of_pos hρpos, lt_div_iff₀ hρpos]
      exact ht
    have hlamC : ContDiff ℝ ∞ lam :=
      contDiff_const.sub (hbC.comp ((contDiff_id.sub contDiff_const).div_const ρ))
    set β : ℝ → (Fin m → ℝ) := fun t => (t - t₀) • a + lam t • rr t with hβ
    have hβP : ∀ t, |t - t₀| < r₀ → ∀ j, π j → β t j = 0 := by
      intro t ht j hj
      simp only [hβ, hrr, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, haP j hj,
        (hα2 t ht).2.2 j hj]
      ring
    have hβρ : ∀ t, |t - t₀| ≤ ρ → β t = (t - t₀) • a := by
      intro t ht
      simp only [hβ, hlam0 t ht, zero_smul, add_zero]
    have hβα : ∀ t, 2 * ρ ≤ |t - t₀| → β t = α t := by
      intro t ht
      simp only [hβ, hlam1 t ht, one_smul, hrr]
      abel
    have hkey : ∀ s t, |s - t₀| < 2 * ρ → |t - t₀| < r₁ → 3 * A / 4 * |t - s| ≤ ‖β t - β s‖ := by
      intro s t hs ht
      have hs' : |s - t₀| < r₁ := lt_trans hs hρr₁'
      have e1 : β t - β s = (t - s) • a + (lam t • (rr t - rr s) + (lam t - lam s) • rr s) := by
        simp only [hβ, smul_sub, sub_smul]
        abel
      have b1 : ‖lam t • (rr t - rr s)‖ ≤ η * |t - s| := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlamb t).1]
        calc lam t * ‖rr t - rr s‖ ≤ 1 * (η * |t - s|) :=
              mul_le_mul (hlamb t).2 (hrrLip s t hs' ht) (norm_nonneg _) zero_le_one
          _ = η * |t - s| := one_mul _
      have b2 : ‖(lam t - lam s) • rr s‖ ≤ 2 * L * η * |t - s| := by
        rw [norm_smul, Real.norm_eq_abs]
        have h1 : ‖rr s‖ ≤ η * (2 * ρ) :=
          (hrrb s hs').trans (mul_le_mul_of_nonneg_left hs.le hηpos.le)
        calc |lam t - lam s| * ‖rr s‖ ≤ (L / ρ * |t - s|) * (η * (2 * ρ)) :=
              mul_le_mul (hlamLip s t) h1 (norm_nonneg _)
                (mul_nonneg (div_nonneg hL0 hρpos.le) (abs_nonneg _))
          _ = 2 * L * η * |t - s| := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hρpos.ne']; ring
      have hna : ‖(t - s) • a‖ = |t - s| * A := by rw [norm_smul, Real.norm_eq_abs]
      have tri : ‖(t - s) • a‖ ≤ ‖β t - β s‖ +
          ‖lam t • (rr t - rr s) + (lam t - lam s) • rr s‖ := by
        rw [e1]
        calc ‖(t - s) • a‖ = ‖((t - s) • a + (lam t • (rr t - rr s) + (lam t - lam s) • rr s)) -
              (lam t • (rr t - rr s) + (lam t - lam s) • rr s)‖ := by rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
      have tri2 := norm_add_le (lam t • (rr t - rr s)) ((lam t - lam s) • rr s)
      have hts : 0 ≤ |t - s| := abs_nonneg _
      have e3 : η * |t - s| + 2 * L * η * |t - s| = A / 4 * |t - s| := by
        rw [← hηL]; ring
      linarith only [hna, tri, tri2, b1, b2, e3]
    have hβsmall : ∀ s, |s - t₀| < 2 * ρ → ‖β s‖ < rs := by
      intro s hs
      have hs' : |s - t₀| < r₁ := lt_trans hs hρr₁'
      have h1 : ‖β s‖ ≤ |s - t₀| * A + 1 * (η * |s - t₀|) := by
        calc ‖β s‖ ≤ ‖(s - t₀) • a‖ + ‖lam s • rr s‖ := norm_add_le _ _
          _ ≤ |s - t₀| * A + 1 * (η * |s - t₀|) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (hlamb s).1]
            exact add_le_add le_rfl (mul_le_mul (hlamb s).2 (hrrb s hs') (norm_nonneg _) zero_le_one)
      have hAη : 0 < A + η := add_pos hApos hηpos
      have h2 : (A + η) * (2 * ρ) ≤ rs / 2 := by
        have := (le_div_iff₀ (mul_pos four_pos hAη)).1 hρrs
        linarith only [this]
      have h3 : (A + η) * |s - t₀| < (A + η) * (2 * ρ) := mul_lt_mul_of_pos_left hs hAη
      linarith only [h1, h2, h3, hrs]
    have hβU : ∀ t, |t - t₀| < r₁ → β t ∈ U := by
      intro t ht
      by_cases hE : |t - t₀| < 2 * ρ
      · exact (hrsU (mem_ball_zero_iff.2 (hβsmall t hE))).1
      · rw [hβα t (not_lt.1 hE)]
        exact (hα2 t (hr₁r₀ t ht)).1
    have hβd : ∀ t, |t - t₀| < r₀ →
        HasDerivAt β (a + (lam t • (deriv α t - a) + lamd t • rr t)) t := by
      intro t ht
      have h1 := ((hasDerivAt_id t).sub_const t₀).smul_const a
      rw [one_smul] at h1
      exact h1.add ((hlamd t).smul (hrrd t ht))
    have hβne : ∀ t, |t - t₀| < r₁ → a + (lam t • (deriv α t - a) + lamd t • rr t) ≠ 0 := by
      intro t ht h0
      have hb : ‖lam t • (deriv α t - a) + lamd t • rr t‖ ≤ A / 4 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hlamb t).1]
        have h1 : lam t * ‖deriv α t - a‖ ≤ η :=
          (mul_le_mul (hlamb t).2 (hr₁d t ht) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
        have h2 : |lamd t| * ‖rr t‖ ≤ 2 * L * η := by
          by_cases hE : 2 * ρ < |t - t₀|
          · rw [hlamd0 t hE, abs_zero, zero_mul]
            exact mul_nonneg (mul_nonneg zero_le_two hL0) hηpos.le
          · have hr : ‖rr t‖ ≤ η * (2 * ρ) :=
              (hrrb t ht).trans (mul_le_mul_of_nonneg_left (not_lt.1 hE) hηpos.le)
            calc |lamd t| * ‖rr t‖ ≤ L / ρ * (η * (2 * ρ)) :=
                  mul_le_mul (hlamdb t) hr (norm_nonneg _) (div_nonneg hL0 hρpos.le)
              _ = 2 * L * η := by
                rw [div_mul_eq_mul_div, div_eq_iff hρpos.ne']; ring
        linarith only [h1, h2, hηL]
      have : a = -(lam t • (deriv α t - a) + lamd t • rr t) := eq_neg_of_add_eq_zero_left h0
      have hn : A ≤ A / 4 := by
        calc A = ‖a‖ := rfl
          _ = ‖-(lam t • (deriv α t - a) + lamd t • rr t)‖ := by rw [← this]
          _ ≤ A / 4 := by rw [norm_neg]; exact hb
      linarith only [hn, hApos]
    have hβsm : ∀ t, |t - t₀| < r₀ → ContDiffAt ℝ ∞ β t := by
      intro t ht
      have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => (t - t₀) • a) t :=
        (contDiffAt_id.sub contDiffAt_const).smul contDiffAt_const
      exact hlin.add (hlamC.contDiffAt.smul ((hα1 t ht).sub hlin))
    set γ' : ℝ → M := fun t => if |t - t₀| < 2 * ρ then φ (β t) else γ t with hγ'
    have hγ'1 : ∀ t, |t - t₀| < r₁ → γ' t = φ (β t) := by
      intro t ht
      simp only [hγ']
      split_ifs with h
      · rfl
      · rw [(hα2 t (hr₁r₀ t ht)).2.1, hβα t (not_lt.1 h)]
    have hγ'2 : ∀ t, 2 * ρ ≤ |t - t₀| → γ' t = γ t := by
      intro t ht
      simp only [hγ', not_lt.2 ht, ↓reduceIte]
    have hev1 : ∀ t, |t - t₀| < r₁ → γ' =ᶠ[𝓝 t] fun s => φ (β s) := by
      intro t ht
      filter_upwards [(hOpen r₁).mem_nhds ht] with s hs
      exact hγ'1 s hs
    have hev2 : ∀ t, 2 * ρ < |t - t₀| → γ' =ᶠ[𝓝 t] γ := by
      intro t ht
      filter_upwards [(hOpen' (2 * ρ)).mem_nhds ht] with s hs
      exact hγ'2 s (le_of_lt hs)
    have hγ'sm : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ' := by
      intro t
      by_cases ht : |t - t₀| < r₁
      · refine ContMDiffAt.congr_of_eventuallyEq ?_ (hev1 t ht)
        exact (hφ.contMDiffAt (hU.mem_nhds (hβU t ht))).comp t
          (contMDiffAt_iff_contDiffAt.2 (hβsm t (hr₁r₀ t ht)))
      · exact (hγ t).congr_of_eventuallyEq (hev2 t (lt_of_lt_of_le hρr₁' (not_lt.1 ht)))
    have hγ'imm : ∀ t ∈ Icc (-1 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I γ' t 1 ≠ 0 := by
      intro t htI
      by_cases ht : |t - t₀| < r₁
      · rw [hmf β γ' t _ (hβU t ht) (hev1 t ht) (hβd t (hr₁r₀ t ht))]
        intro h0
        exact hβne t ht (himm (β t) (hβU t ht) (h0.trans (map_zero _).symm))
      · rw [(hev2 t (lt_of_lt_of_le hρr₁' (not_lt.1 ht))).mfderiv_eq]
        exact hγimm t htI
    have hβinj : ∀ s t, |s - t₀| < 2 * ρ → |t - t₀| < r₁ → β t = β s → t = s := by
      intro s t hs ht h
      have h1 := hkey s t hs ht
      rw [h, sub_self, norm_zero] at h1
      have h2 : |t - s| ≤ 0 := by
        by_contra h2
        have := mul_pos (by linarith only [hApos] : (0 : ℝ) < 3 * A / 4) (lt_of_not_ge h2)
        linarith only [this, h1]
      have h3 := abs_nonpos_iff.1 h2
      linarith only [h3]
    have hγ'inj : InjOn γ' (Icc (-1) 1) := by
      have main : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1, |s - t₀| < 2 * ρ →
          γ' s = γ' t → s = t := by
        intro s hs t ht hsE hst
        have hsr₁ : |s - t₀| < r₁ := lt_trans hsE hρr₁'
        by_cases htr : |t - t₀| < r₁
        · rw [hγ'1 s hsr₁, hγ'1 t htr] at hst
          exact (hβinj s t hsE htr (hinj (hβU t htr) (hβU s hsr₁) hst.symm)).symm
        · exfalso
          have htK : γ t ∈ K := ⟨t, ⟨ht, not_lt.1 htr⟩, rfl⟩
          have hγ't : γ' t = γ t := hγ'2 t (lt_of_lt_of_le hρr₁' (not_lt.1 htr)).le
          have hsK := (hrsU (mem_ball_zero_iff.2 (hβsmall s hsE))).2
          rw [hγ'1 s hsr₁, hγ't] at hst
          exact hsK (hst ▸ htK)
      intro s hs t ht hst
      by_cases hsE : |s - t₀| < 2 * ρ
      · exact main s hs t ht hsE hst
      by_cases htE : |t - t₀| < 2 * ρ
      · exact (main t ht s hs htE hst.symm).symm
      · rw [hγ'2 s (not_lt.1 hsE), hγ'2 t (not_lt.1 htE)] at hst
        exact hγinj hs ht hst
    have hγ'S : ∀ t, γ' t ∈ S := by
      intro t
      by_cases ht : |t - t₀| < r₁
      · rw [hγ'1 t ht]
        exact (hPS _ (hβU t ht)).2 (hβP t (hr₁r₀ t ht))
      · rw [hγ'2 t (lt_of_lt_of_le hρr₁' (not_lt.1 ht)).le]
        exact hγS t
    have hβt₀ : β t₀ = 0 := by
      rw [hβρ t₀ (by rw [sub_self, abs_zero]; exact hρpos.le), sub_self, zero_smul]
    have hγ'T : ∀ t ∈ Icc (-1 : ℝ) 1, γ' t ∈ T ↔ t = -1 ∨ t = 1 := by
      intro t htI
      by_cases hE : |t - t₀| < 2 * ρ
      · have htr : |t - t₀| < r₁ := lt_trans hE hρr₁'
        rw [hγ'1 t htr, hQT _ (hβU t htr)]
        constructor
        · intro hQ
          have hβ0 : β t = 0 := by
            funext j
            by_cases hj : π j
            · exact hβP t (hr₁r₀ t htr) j hj
            · exact hQ j hj
          have := hβinj t₀ t (hself (2 * ρ) (by linarith only [hρpos])) htr (hβ0.trans hβt₀.symm)
          rw [this]
          exact ht₀
        · intro h
          have htt₀ : t = t₀ := by
            rcases h with h | h <;> rcases ht₀ with h' | h' <;> rw [h, h'] at hE ⊢ <;>
              norm_num at hE ⊢ <;> linarith only [hE, hρ1]
          rw [htt₀, hβt₀]
          intro j _
          rfl
      · rw [hγ'2 t (not_lt.1 hE)]
        exact hγT t htI
    refine ⟨γ', a, ρ, hγ'sm, hγ'imm, hγ'inj, hγ'S, hγ'T, ha0, haP, hρpos, by linarith only [hρρ₁], ?_, ?_⟩
    · intro t ht
      have h1 : |t - t₀| ≤ ρ := ht.le
      have htr : |t - t₀| < r₁ := lt_trans ht hρr₁''
      refine ⟨?_, ?_⟩
      · rw [← hβρ t h1]
        exact hβU t htr
      · rw [hγ'1 t htr, hβρ t h1]
    · intro t ht
      exact hγ'2 t (le_trans (by linarith only [hρρ₁]) ht)
  classical
  obtain ⟨hε, -, -, hrmp, hrmq, -, hfree⟩ := hv
  have hRp : 2 * ε < (D.chart p hp).R ^ 2 := by
    have h1 := pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
    linarith only [h1, hrmp, hε]
  have hRq : 2 * ε < (D.chart q hq).R ^ 2 := by
    have h1 := pow_le_pow_left₀ (D.rm_pos q hq).le (D.hrm q hq).2 2
    linarith only [h1, hrmq, hε]
  have hfp : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hfq : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hac : a ≤ c := by linarith only [hfp.1, hc₁, hε]
  have hcb : c ≤ b := by linarith only [hfq.2, hc₂, hε]
  have hSLlev : D.leftSphere q hq ε c ⊆ f ⁻¹' {c} :=
    D.leftSphere_subset_level hf q hq hRq.le ⟨hac, hcb⟩ (fun y hy x hx => hfree y
      (by rw [uIcc_of_ge hc₂.le] at hy; exact ⟨by linarith only [hy.1, hc₁], hy.2⟩) x hx)
  have hSRlev : D.rightSphere p hp ε c ⊆ f ⁻¹' {c} :=
    D.rightSphere_subset_level hf p hp hRp.le ⟨hac, hcb⟩ (fun y hy x hx => hfree y
      (by rw [uIcc_of_le hc₁.le] at hy; exact ⟨hy.1, by linarith only [hy.2, hc₂]⟩) x hx)
  obtain ⟨OL, hOL, hSLOL, hψL, -⟩ := leftCoord_submersion hf D hq hε
    (by linarith only [hrmq, hε]) hac hc₂.le
    (fun y hy x hx => hfree y ⟨by linarith only [hy.1, hc₁], hy.2⟩ x hx)
  obtain ⟨OR, hOR, hSROR, hψR, -⟩ := rightCoord_submersion hf D hp hε
    (by linarith only [hrmp, hε]) hc₁.le hcb
    (fun y hy x hx => hfree y ⟨hy.1, by linarith only [hy.2, hc₂]⟩ x hx)
  set Ψ : M → (Fin (n - 1) → ℝ) := fun z j =>
    if h : (j : ℕ) < ℓ then D.rightCoord p hp ε z ⟨j, by omega⟩
    else D.leftCoord q hq ε z ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩ with hΨ
  have hΨsm : ContMDiffOn I 𝓘(ℝ, Fin (n - 1) → ℝ) ∞ Ψ (OL ∩ OR) := by
    refine contMDiffOn_pi_space.2 fun j => ?_
    by_cases h : (j : ℕ) < ℓ
    · have e : (fun z => Ψ z j) = fun z => D.rightCoord p hp ε z ⟨j, by omega⟩ := by
        funext z; simp only [hΨ, h, ↓reduceDIte]
      rw [e]
      exact (EuclideanSpace.proj (⟨j, by omega⟩ : Fin (D.chart p hp).k)).contMDiff.comp_contMDiffOn
        (hψR.mono inter_subset_right)
    · have e : (fun z => Ψ z j) = fun z => D.leftCoord q hq ε z
          ⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩ := by
        funext z; simp only [hΨ, h, ↓reduceDIte]
      rw [e]
      exact (EuclideanSpace.proj (⟨(j : ℕ) - ℓ, by have := j.isLt; omega⟩ :
        Fin (n - (D.chart q hq).k))).contMDiff.comp_contMDiffOn (hψL.mono inter_subset_left)
  have hcoord : ∀ (y : Fin (n - 1) → ℝ) (j : Fin (n - 1)), coordN y j = y j := by
    intro y j
    simp [coordN, j.isLt]
  have hconv : ∀ (y : Fin (n - 1) → ℝ) (P : ℕ → Prop),
      (∀ j : ℕ, P j → coordN y j = 0) ↔ (∀ j : Fin (n - 1), P j → y j = 0) := by
    intro y P
    constructor
    · intro h j hj
      rw [← hcoord y j]
      exact h j hj
    · intro h j hj
      by_cases hj' : j < n - 1
      · have := h ⟨j, hj'⟩ hj
        simpa [coordN, hj'] using this
      · simp [coordN, hj']
  have hΨφ : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ → ∀ y ∈ U, Ψ (φ y) = y := by
    intro x U φ hφ y hy
    funext j
    by_cases h : (j : ℕ) < ℓ
    · simp only [hΨ, h, ↓reduceDIte]
      rw [hφ.coordR y hy, hcoord]
    · simp only [hΨ, h, ↓reduceDIte]
      rw [hφ.coordL y hy]
      have e : ℓ + ((j : ℕ) - ℓ) = j := by omega
      rw [e, hcoord]
  have hs2 : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith only [hε])
  have hφ0 : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ →
        φ 0 ∈ D.leftSphere q hq ε c ∧ φ 0 ∈ D.rightSphere p hp ε c := by
    intro x U φ hφ
    exact ⟨(hφ.memL 0 hφ.zero_mem).2 (fun j _ => by simp [coordN]),
      (hφ.memR 0 hφ.zero_mem).2 (fun j _ => by simp [coordN])⟩
  have hx₁ := hφ₁.center
  have hx₂ := hφ₂.center
  have hw₁' : w₁ ∈ D.sardDom p hq ε c ε hp ∧ ‖w₁‖ = 1 ∧ D.sardMap p hq ε c ε hp w₁ = 0 := hw₁
  have hw₂' : w₂ ∈ D.sardDom p hq ε c ε hp ∧ ‖w₂‖ = 1 ∧ D.sardMap p hq ε c ε hp w₂ = 0 := hw₂
  have hw₁0 : w₁ ≠ 0 := hw₁'.1.1
  have hw₂0 : w₂ ≠ 0 := hw₂'.1.1
  set ΦL : EuclideanSpace ℝ (Fin (D.chart q hq).k) → M := fun v =>
    D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε
      ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v))) with hΦL
  set GLf : M → EuclideanSpace ℝ (Fin (D.chart q hq).k) := fun z =>
    (Real.sqrt (2 * ε))⁻¹ • negPart (D.chart q hq).hk
      ((D.chart q hq).χ.symm (D.flow (c - (f q - ε)) z)) with hGLf
  have hflowL : ∀ z : M, D.flow (c - (f q - ε)) (D.flow (f q - ε - c) z) = z := by
    intro z
    rw [D.flow_flow, show f q - ε - c + (c - (f q - ε)) = 0 by ring, D.flow_zero]
  have hΦLsm : ∀ v : EuclideanSpace ℝ (Fin (D.chart q hq).k), v ≠ 0 →
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q hq).k)) I ∞ ΦL v := by
    intro v hv
    have hw : (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v ≠ 0 := by
      intro h; exact hv ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).map_eq_zero_iff.1 h)
    have h1 : ContDiffAt ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (D.chart q hq).k) =>
        (D.chart q hq).sphereParam ε ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v)) v :=
      ((D.chart q hq).contDiffAt_sphereParam ε hw).comp v
        (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).contDiff.contDiffAt
    have h2 := (D.chart q hq).contMDiffAt_chart ((D.chart q hq).mem_ball_of_le
      ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq.le hw))
    exact ((D.contMDiff_flow _) _).comp v (h2.comp v (contMDiffAt_iff_contDiffAt.2 h1))
  have hΦLS : ∀ v : EuclideanSpace ℝ (Fin (D.chart q hq).k), v ≠ 0 →
      ΦL v ∈ D.leftSphere q hq ε c := by
    intro v hv
    have hw : (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v ≠ 0 := by
      intro h; exact hv ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).map_eq_zero_iff.1 h)
    exact ⟨_, ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw, rfl⟩, rfl⟩
  have hOLo : IsOpen (D.flow (c - (f q - ε)) ⁻¹'
      ((D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R')) :=
    (D.chart q hq).isOpen_image_ball.preimage (D.continuous_flow _)
  have hSLO : D.leftSphere q hq ε c ⊆ D.flow (c - (f q - ε)) ⁻¹'
      ((D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R') := by
    intro z hz
    rw [D.mem_leftSphere_iff] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    exact ⟨y, (D.chart q hq).mem_ball_of_le
      ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hRq.le hy), hyz⟩
  have hGLsm : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q hq).k)) ∞ GLf
      (D.flow (c - (f q - ε)) ⁻¹' ((D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R')) := by
    intro z hz
    have h := ((((Real.sqrt (2 * ε))⁻¹ • ModelField.negPartL (D.chart q hq).hk).contMDiff
      (n := ∞)) _).comp z
      (((D.chart q hq).contMDiffAt_symm hz).comp z ((D.contMDiff_flow _) z))
    exact h.contMDiffWithinAt
  have hGΦL : ∀ v : EuclideanSpace ℝ (Fin (D.chart q hq).k), ‖v‖ = 1 → GLf (ΦL v) = v := by
    intro v hv
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
    have hw : (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v ≠ 0 := by
      intro h; exact hv0 ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).map_eq_zero_iff.1 h)
    have htoE : (D.chart q hq).toE ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) v) = v :=
      (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).symm_apply_apply v
    simp only [hGLf, hΦL]
    rw [hflowL, (D.chart q hq).χ.left_inv ((D.chart q hq).hsrc _
      ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq.le hw)),
      (D.chart q hq).negPart_sphereParam, htoE, hv, div_one, smul_smul,
      inv_mul_cancel₀ hs2.ne', one_smul]
  have hΦGL : ∀ z ∈ D.leftSphere q hq ε c, ‖GLf z‖ = 1 ∧ ΦL (GLf z) = z := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyR := (D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hRq.le hy
    have hG : GLf (D.flow (f q - ε - c) ((D.chart q hq).χ y)) =
        (Real.sqrt (2 * ε))⁻¹ • negPart (D.chart q hq).hk y := by
      simp only [hGLf]
      rw [hflowL, (D.chart q hq).χ.left_inv ((D.chart q hq).hsrc y hyR)]
    have hny : ‖negPart (D.chart q hq).hk y‖ = Real.sqrt (2 * ε) := by
      rw [← hy.2, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨?_, ?_⟩
    · rw [hG, norm_smul, hny, norm_inv, Real.norm_eq_abs, abs_of_pos hs2, inv_mul_cancel₀ hs2.ne']
    · rw [hG]
      simp only [hΦL]
      obtain ⟨hw0, hsp⟩ := (D.chart q hq).sphereParam_of_mem hε hy
      rw [map_smul, (D.chart q hq).sphereParam_smul ε (inv_pos.2 hs2) hw0, hsp]
  have hGx : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      GLf (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) =
        ‖(D.chart q hq).toE w‖⁻¹ • (D.chart q hq).toE w := by
    intro w hw
    have hn : 0 < ‖(D.chart q hq).toE w‖ := norm_pos_iff.2 ((D.chart q hq).toE_ne_zero hw)
    simp only [hGLf]
    rw [hflowL, (D.chart q hq).χ.left_inv ((D.chart q hq).hsrc _
      ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq.le hw)),
      (D.chart q hq).negPart_sphereParam, smul_smul]
    congr 1
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
  have hx₁₂ : D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₁)) ≠
      D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₂)) := by
    intro h
    have h' := congrArg GLf h
    rw [hGx w₁ hw₁0, hGx w₂ hw₂0] at h'
    apply hne
    have hc1 : 0 < ‖(D.chart q hq).toE w₁‖ := norm_pos_iff.2 ((D.chart q hq).toE_ne_zero hw₁0)
    have hc2 : 0 < ‖(D.chart q hq).toE w₂‖ := norm_pos_iff.2 ((D.chart q hq).toE_ne_zero hw₂0)
    have e1 : (D.chart q hq).toE w₁ = (‖(D.chart q hq).toE w₁‖ * ‖(D.chart q hq).toE w₂‖⁻¹) •
        (D.chart q hq).toE w₂ := by
      calc (D.chart q hq).toE w₁ = ‖(D.chart q hq).toE w₁‖ •
            (‖(D.chart q hq).toE w₁‖⁻¹ • (D.chart q hq).toE w₁) := by
            rw [smul_smul, mul_inv_cancel₀ hc1.ne', one_smul]
        _ = _ := by rw [h', smul_smul]
    have e2 : w₁ = (‖(D.chart q hq).toE w₁‖ * ‖(D.chart q hq).toE w₂‖⁻¹) • w₂ := by
      rw [← (D.chart q hq).toE_smul] at e1
      exact (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ).symm.injective e1
    have hn := congrArg norm e2
    rw [norm_smul, hw₁'.2.1, hw₂'.2.1, mul_one, Real.norm_eq_abs, abs_of_pos (mul_pos hc1 (inv_pos.2 hc2))] at hn
    rw [e2, ← hn, one_smul]
  set F : Set M := (fun w => D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))
    '' D.sardZeros p hq ε c hp with hF
  have hFfin : F.Finite := hfin.image _
  have hLR : ∀ z ∈ D.leftSphere q hq ε c, z ∈ D.rightSphere p hp ε c → z ∈ F := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hzR
    obtain ⟨hw0, hsp⟩ := (D.chart q hq).sphereParam_of_mem hε hy
    set w' := (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) (negPart (D.chart q hq).hk y) with hw'
    have hn : 0 < ‖w'‖ := norm_pos_iff.2 hw0
    have hsp' : (D.chart q hq).sphereParam ε (‖w'‖⁻¹ • w') = y := by
      rw [(D.chart q hq).sphereParam_smul ε (inv_pos.2 hn) hw0, hsp]
    refine ⟨‖w'‖⁻¹ • w', ?_, ?_⟩
    · have hland : D.landing p hq ε c ε (‖w'‖⁻¹ • w') =
          D.flow (c - (f p + ε)) (D.flow (f q - ε - c) ((D.chart q hq).χ y)) := by
        simp only [GradientLikeStrip.landing]
        rw [hsp']
      rw [D.mem_rightSphere_iff] at hzR
      obtain ⟨yp, hyp, hypz⟩ := hzR
      have hypR : morseNorm n yp < (D.chart p hp).R := by
        have h1 := (D.chart p hp).morseNorm_sq_of_mem_rightModelSphere hyp
        exact lt_of_pow_lt_pow_left₀ 2 (D.chart p hp).R_pos.le (by rw [h1]; exact hRp)
      have hmem : ‖w'‖⁻¹ • w' ∈ D.sardDom p hq ε c ε hp ∧ ‖‖w'‖⁻¹ • w'‖ = 1 ∧
          D.sardMap p hq ε c ε hp (‖w'‖⁻¹ • w') = 0 := by
        refine ⟨⟨smul_ne_zero (inv_ne_zero hn.ne') hw0, ?_⟩, norm_smul_inv_norm hw0, ?_⟩
        · change D.landing p hq ε c ε (‖w'‖⁻¹ • w') ∈
            (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
          rw [hland, ← hypz]
          exact ⟨yp, hypR, rfl⟩
        · change ModelField.scaledNegativePart (D.chart p hp).hk
            ((D.chart p hp).χ.symm (D.landing p hq ε c ε (‖w'‖⁻¹ • w'))) = 0
          rw [hland, ← hypz, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc yp hypR.le)]
          simp [ModelField.scaledNegativePart, hyp.1]
      exact hmem
    · change D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε (‖w'‖⁻¹ • w'))) =
        D.flow (f q - ε - c) ((D.chart q hq).χ y)
      rw [hsp']
  set rP : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)) → (Fin n → ℝ) := fun v =>
    recombine (D.chart p hp).hk 0 ((Real.sqrt (2 * ε) / ‖v‖) • v) with hrP
  set ΦR : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)) → M := fun v =>
    D.flow (f p + ε - c) ((D.chart p hp).χ (rP v)) with hΦR
  set GRf : M → EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)) := fun z =>
    (Real.sqrt (2 * ε))⁻¹ • posPart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) z)) with hGRf
  have hflowR : ∀ z : M, D.flow (c - (f p + ε)) (D.flow (f p + ε - c) z) = z := by
    intro z
    rw [D.flow_flow, show f p + ε - c + (c - (f p + ε)) = 0 by ring, D.flow_zero]
  have hrPmem : ∀ v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)), v ≠ 0 →
      rP v ∈ (D.chart p hp).rightModelSphere ε := by
    intro v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine ⟨ModelField.negPart_recombine (D.chart p hp).hk _ _, ?_⟩
    rw [ModelField.posPart_recombine, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hs2.le hn.le), div_mul_cancel₀ _ hn.ne', Real.sq_sqrt (by linarith only [hε])]
  have hrPR : ∀ v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)), v ≠ 0 →
      morseNorm n (rP v) ≤ (D.chart p hp).R := fun v hv =>
    (D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere hRp.le (hrPmem v hv)
  have hΦRsm : ∀ v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)), v ≠ 0 →
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart p hp).k))) I ∞ ΦR v := by
    intro v hv
    have heq : rP = fun v => ModelField.recombineL (D.chart p hp).hk
        (0, (Real.sqrt (2 * ε) / ‖v‖) • v) :=
      funext fun v => (ModelField.recombineL_apply _ _ _).symm
    have h0 : ContDiffAt ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)) =>
        (Real.sqrt (2 * ε) / ‖v‖) • v) v :=
      (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.2 hv)).smul contDiffAt_id
    have h1 : ContDiffAt ℝ ∞ rP v := by
      rw [heq]
      exact (ModelField.recombineL (D.chart p hp).hk).contDiff.contDiffAt.comp v
        (contDiffAt_const.prodMk h0)
    have h2 := (D.chart p hp).contMDiffAt_chart ((D.chart p hp).mem_ball_of_le (hrPR v hv))
    exact ((D.contMDiff_flow _) _).comp v (h2.comp v (contMDiffAt_iff_contDiffAt.2 h1))
  have hΦRS : ∀ v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)), v ≠ 0 →
      ΦR v ∈ D.rightSphere p hp ε c := fun v hv => ⟨_, ⟨_, hrPmem v hv, rfl⟩, rfl⟩
  have hORo : IsOpen (D.flow (c - (f p + ε)) ⁻¹'
      ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')) :=
    (D.chart p hp).isOpen_image_ball.preimage (D.continuous_flow _)
  have hSRO : D.rightSphere p hp ε c ⊆ D.flow (c - (f p + ε)) ⁻¹'
      ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R') := by
    intro z hz
    rw [D.mem_rightSphere_iff] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    exact ⟨y, (D.chart p hp).mem_ball_of_le
      ((D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere hRp.le hy), hyz⟩
  have hGRsm : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart p hp).k))) ∞ GRf
      (D.flow (c - (f p + ε)) ⁻¹' ((D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R')) := by
    intro z hz
    have h := ((((Real.sqrt (2 * ε))⁻¹ • ModelField.posPartL (D.chart p hp).hk).contMDiff
      (n := ∞)) _).comp z
      (((D.chart p hp).contMDiffAt_symm hz).comp z ((D.contMDiff_flow _) z))
    exact h.contMDiffWithinAt
  have hGΦR : ∀ v : EuclideanSpace ℝ (Fin (n - (D.chart p hp).k)), ‖v‖ = 1 → GRf (ΦR v) = v := by
    intro v hv
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
    simp only [hGRf, hΦR]
    rw [hflowR, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc _ (hrPR v hv0))]
    simp only [hrP]
    rw [ModelField.posPart_recombine, hv, div_one, smul_smul, inv_mul_cancel₀ hs2.ne', one_smul]
  have hΦGR : ∀ z ∈ D.rightSphere p hp ε c, ‖GRf z‖ = 1 ∧ ΦR (GRf z) = z := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyR := (D.chart p hp).morseNorm_le_R_of_mem_rightModelSphere hRp.le hy
    have hG : GRf (D.flow (f p + ε - c) ((D.chart p hp).χ y)) =
        (Real.sqrt (2 * ε))⁻¹ • posPart (D.chart p hp).hk y := by
      simp only [hGRf]
      rw [hflowR, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y hyR)]
    have hny : ‖posPart (D.chart p hp).hk y‖ = Real.sqrt (2 * ε) := by
      rw [← hy.2, Real.sqrt_sq (norm_nonneg _)]
    have hG1 : ‖(Real.sqrt (2 * ε))⁻¹ • posPart (D.chart p hp).hk y‖ = 1 := by
      rw [norm_smul, hny, norm_inv, Real.norm_eq_abs, abs_of_pos hs2, inv_mul_cancel₀ hs2.ne']
    refine ⟨by rw [hG]; exact hG1, ?_⟩
    rw [hG]
    simp only [hΦR, hrP]
    rw [hG1, div_one, smul_smul, mul_inv_cancel₀ hs2.ne', one_smul, ← hy.1,
      DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose]
  have hchart : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ → ∃ W : Set M, IsOpen W ∧ φ 0 ∈ W ∧
        W ∩ D.leftSphere q hq ε c ⊆ φ '' U ∧ W ∩ D.rightSphere p hp ε c ⊆ φ '' U := by
    intro x U φ hφ
    obtain ⟨G, hGo, hG⟩ := hφ.open_image U subset_rfl hφ.isOpen_U
    refine ⟨G, hGo, ?_, ?_, ?_⟩
    · have h : φ 0 ∈ φ '' U := mem_image_of_mem φ hφ.zero_mem
      rw [hG] at h
      exact h.1
    · rintro z ⟨hzG, hzS⟩
      rw [hG]
      exact ⟨hzG, hSLlev hzS⟩
    · rintro z ⟨hzG, hzS⟩
      rw [hG]
      exact ⟨hzG, hSRlev hzS⟩
  have hPL : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ → ∀ y ∈ U,
        (φ y ∈ D.leftSphere q hq ε c ↔ ∀ j : Fin (n - 1), ℓ ≤ (j : ℕ) → y j = 0) ∧
        (φ y ∈ D.rightSphere p hp ε c ↔ ∀ j : Fin (n - 1), (j : ℕ) < ℓ → y j = 0) := by
    intro x U φ hφ y hy
    exact ⟨(hφ.memL y hy).trans (hconv y (fun j => ℓ ≤ j)),
      (hφ.memR y hy).trans (hconv y (fun j => j < ℓ))⟩
  obtain ⟨W₁, hW₁o, hW₁0, hW₁L, hW₁R⟩ := hchart hφ₁
  obtain ⟨W₂, hW₂o, hW₂0, hW₂L, hW₂R⟩ := hchart hφ₂
  have hS₁ := hφ0 hφ₁
  have hS₂ := hφ0 hφ₂
  have hne12 : φ₁ 0 ≠ φ₂ 0 := by rw [hx₁, hx₂]; exact hx₁₂
  have hO₁ : φ₁ 0 ∈ OL ∩ OR := ⟨hSLOL hS₁.1, hSROR hS₁.2⟩
  have hO₂ : φ₂ 0 ∈ OL ∩ OR := ⟨hSLOL hS₂.1, hSROR hS₂.2⟩
  obtain ⟨γ₀, hγ₀sm, hγ₀imm, hγ₀inj, hγ₀S, hγ₀T, hγ₀m, hγ₀p⟩ := arcGL (D.chart q hq).k (by omega)
    ΦL GLf _ _ _ F (φ₁ 0) (φ₂ 0) hΦLsm hΦLS hOLo hSLO hGLsm hGΦL hΦGL hS₁.1 hS₂.1 hne12
    hS₁.2 hS₂.2 hFfin (fun z hz hzT => Or.inr (Or.inr (hLR z hz hzT)))
  obtain ⟨γ₁, a₁, δ₁, hγ₁sm, hγ₁imm, hγ₁inj, hγ₁S, hγ₁T, ha₁0, ha₁P, hδ₁, hδ₁ρ, hγ₁end,
    hγ₁far⟩ := arcSL (n - 1) γ₀ (-1) φ₁ U₁ Ψ (OL ∩ OR) W₁ (fun j => ℓ ≤ (j : ℕ)) _ _ 1
    hφ₁.isOpen_U hφ₁.zero_mem hφ₁.smooth hφ₁.immersion hφ₁.inj (hOL.inter hOR) hO₁ hΨsm
    (hΨφ hφ₁) hW₁o hW₁0 hW₁L (fun y hy => (hPL hφ₁ y hy).1)
    (fun y hy => (hPL hφ₁ y hy).2.trans (by simp only [not_le])) hγ₀sm hγ₀imm hγ₀inj hγ₀S
    hγ₀T (Or.inl rfl) hγ₀m one_pos
  have hγ₁p : γ₁ 1 = φ₂ 0 := by rw [hγ₁far 1 (by norm_num), hγ₀p]
  obtain ⟨γ₂, a₂, δ₂, hγ₂sm, hγ₂imm, hγ₂inj, hγ₂S, hγ₂T, ha₂0, ha₂P, hδ₂, hδ₂ρ, hγ₂end,
    hγ₂far⟩ := arcSL (n - 1) γ₁ 1 φ₂ U₂ Ψ (OL ∩ OR) W₂ (fun j => ℓ ≤ (j : ℕ)) _ _ 1
    hφ₂.isOpen_U hφ₂.zero_mem hφ₂.smooth hφ₂.immersion hφ₂.inj (hOL.inter hOR) hO₂ hΨsm
    (hΨφ hφ₂) hW₂o hW₂0 hW₂L (fun y hy => (hPL hφ₂ y hy).1)
    (fun y hy => (hPL hφ₂ y hy).2.trans (by simp only [not_le])) hγ₁sm hγ₁imm hγ₁inj hγ₁S
    hγ₁T (Or.inr rfl) hγ₁p one_pos
  obtain ⟨η₀, hη₀sm, hη₀imm, hη₀inj, hη₀S, hη₀T, hη₀m, hη₀p⟩ := arcGL (n - (D.chart p hp).k)
    (by omega) ΦR GRf _ _ _ F (φ₂ 0) (φ₁ 0) hΦRsm hΦRS hORo hSRO hGRsm hGΦR hΦGR hS₂.2 hS₁.2
    hne12.symm hS₂.1 hS₁.1 hFfin (fun z hz hzT => Or.inr (Or.inr (hLR z hzT hz)))
  obtain ⟨η₁, c₂, ε₁, hη₁sm, hη₁imm, hη₁inj, hη₁S, hη₁T, hc₂0, hc₂P, hε₁, hε₁ρ, hη₁end,
    hη₁far⟩ := arcSL (n - 1) η₀ (-1) φ₂ U₂ Ψ (OL ∩ OR) W₂ (fun j => (j : ℕ) < ℓ) _ _ 1
    hφ₂.isOpen_U hφ₂.zero_mem hφ₂.smooth hφ₂.immersion hφ₂.inj (hOL.inter hOR) hO₂ hΨsm
    (hΨφ hφ₂) hW₂o hW₂0 hW₂R (fun y hy => (hPL hφ₂ y hy).2)
    (fun y hy => (hPL hφ₂ y hy).1.trans (by simp only [not_lt])) hη₀sm hη₀imm hη₀inj hη₀S
    hη₀T (Or.inl rfl) hη₀m one_pos
  have hη₁p : η₁ 1 = φ₁ 0 := by rw [hη₁far 1 (by norm_num), hη₀p]
  obtain ⟨η₂, c₁, ε₂, hη₂sm, hη₂imm, hη₂inj, hη₂S, hη₂T, hc₁0, hc₁P, hε₂, hε₂ρ, hη₂end,
    hη₂far⟩ := arcSL (n - 1) η₁ 1 φ₁ U₁ Ψ (OL ∩ OR) W₁ (fun j => (j : ℕ) < ℓ) _ _ 1
    hφ₁.isOpen_U hφ₁.zero_mem hφ₁.smooth hφ₁.immersion hφ₁.inj (hOL.inter hOR) hO₁ hΨsm
    (hΨφ hφ₁) hW₁o hW₁0 hW₁R (fun y hy => (hPL hφ₁ y hy).2)
    (fun y hy => (hPL hφ₁ y hy).1.trans (by simp only [not_lt])) hη₁sm hη₁imm hη₁inj hη₁S
    hη₁T (Or.inr rfl) hη₁p one_pos
  have hπ : 0 < Real.pi := Real.pi_pos
  have h2π : 0 < 2 / Real.pi := div_pos two_pos hπ
  have hπ2 : 2 / Real.pi * Real.pi = 2 := div_mul_cancel₀ 2 hπ.ne'
  have hc₀ : ∀ x : ℝ, 2 / Real.pi * (Real.pi / 2 * x) = x := by
    intro x
    rw [← mul_assoc, div_mul_div_comm, mul_comm 2 Real.pi,
      div_self (mul_ne_zero hπ.ne' two_ne_zero), one_mul]
  set hh : ℝ → ℝ := fun t => 2 / Real.pi * t - 1 with hhdef
  have hhI : ∀ t ∈ Icc (0 : ℝ) Real.pi, hh t ∈ Icc (-1 : ℝ) 1 := by
    intro t ht
    have h1 : 0 ≤ 2 / Real.pi * t := mul_nonneg h2π.le ht.1
    have h2 : 2 / Real.pi * t ≤ 2 := by
      calc 2 / Real.pi * t ≤ 2 / Real.pi * Real.pi := mul_le_mul_of_nonneg_left ht.2 h2π.le
        _ = 2 := hπ2
    exact ⟨by simp only [hhdef]; linarith only [h1], by simp only [hhdef]; linarith only [h2]⟩
  have hhm : ∀ t, hh t = -1 ↔ t = 0 := by
    intro t
    simp only [hhdef]
    constructor
    · intro h
      have : 2 / Real.pi * t = 0 := by linarith only [h]
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' h2π.ne'
      · exact h'
    · intro h; rw [h, mul_zero, zero_sub]
  have hhp : ∀ t, hh t = 1 ↔ t = Real.pi := by
    intro t
    simp only [hhdef]
    constructor
    · intro h
      have : 2 / Real.pi * t = 2 / Real.pi * Real.pi := by linarith only [h, hπ2]
      exact mul_left_cancel₀ h2π.ne' this
    · intro h; rw [h, hπ2]; norm_num
  have hhd : ∀ t, HasDerivAt hh (2 / Real.pi) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (2 / Real.pi)).sub_const 1
    rw [mul_one] at this
    exact this
  have hhC : ContDiff ℝ ∞ hh := (contDiff_const.mul contDiff_id).sub contDiff_const
  set δ := min (min δ₁ δ₂) (min (Real.pi / 2 * ε₁) (Real.pi / 2 * ε₂)) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (lt_min (mul_pos (div_pos hπ two_pos) hε₁)
    (mul_pos (div_pos hπ two_pos) hε₂))
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ Real.pi / 2 * ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ Real.pi / 2 * ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨γ₂, η₂ ∘ hh, a₁, -a₂, -((2 / Real.pi) • c₁), (2 / Real.pi) • c₂, δ, ?_⟩
  exact
    { hδ := hδpos
      smoothA := hγ₂sm
      smoothB := hη₂sm.comp (contMDiff_iff_contDiff.2 hhC)
      immA := hγ₂imm
      immB := by
        intro t ht
        have hc := mfderiv_comp t ((hη₂sm (hh t)).mdifferentiableAt (by simp))
          (mdifferentiableAt_iff_differentiableAt.2 (hhd t).differentiableAt)
        rw [hc, mfderiv_eq_fderiv, (hhd t).hasFDerivAt.fderiv]
        have e : (ContinuousLinearMap.toSpanSingleton ℝ (2 / Real.pi)) (1 : ℝ) =
            (2 / Real.pi) • (1 : ℝ) := by simp
        change mfderiv 𝓘(ℝ, ℝ) I η₂ (hh t) (ContinuousLinearMap.toSpanSingleton ℝ (2 / Real.pi) 1) ≠ 0
        rw [e]
        intro h0
        have key := (mfderiv 𝓘(ℝ, ℝ) I η₂ (hh t)).map_smul (2 / Real.pi) 1
        have h1 := key.symm.trans h0
        rcases smul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 h2π.ne'
        · exact hη₂imm (hh t) (hhI t ht) h2
      injA := hγ₂inj
      injB := by
        intro s hs t ht hst
        have h := hη₂inj (hhI s hs) (hhI t ht) hst
        simp only [hhdef] at h
        have : 2 / Real.pi * s = 2 / Real.pi * t := by linarith only [h]
        exact mul_left_cancel₀ h2π.ne' this
      memA := fun t ht => ⟨hγ₂S t, hγ₂T t ht⟩
      memB := by
        intro t ht
        refine ⟨hη₂S (hh t), ?_⟩
        change η₂ (hh t) ∈ _ ↔ _
        rw [hη₂T (hh t) (hhI t ht), hhm, hhp]
      dirA := ⟨ha₁0, neg_ne_zero.2 ha₂0, (hconv a₁ (fun j => ℓ ≤ j)).2 ha₁P,
        (hconv (-a₂) (fun j => ℓ ≤ j)).2 (fun j hj => by simp [ha₂P j hj])⟩
      dirB := ⟨neg_ne_zero.2 (smul_ne_zero h2π.ne' hc₁0),
        smul_ne_zero h2π.ne' hc₂0,
        (hconv _ (fun j => j < ℓ)).2 (fun j hj => by simp [hc₁P j hj]),
        (hconv _ (fun j => j < ℓ)).2 (fun j hj => by simp [hc₂P j hj])⟩
      endA₁ := by
        intro t ht
        have ht1 : |t - -1| < δ₁ := by rw [sub_neg_eq_add]; exact lt_of_lt_of_le ht hδ1
        obtain ⟨hU, heq⟩ := hγ₁end t ht1
        rw [sub_neg_eq_add] at hU heq
        have hfar : 1 ≤ |t - 1| := by
          rw [abs_lt] at ht1
          rw [abs_sub_comm, le_abs]
          left
          linarith only [ht1.2, hδ₁ρ]
        exact ⟨hU, (hγ₂far t hfar).trans heq⟩
      endA₂ := by
        intro t ht
        obtain ⟨hU, heq⟩ := hγ₂end t (lt_of_lt_of_le ht hδ2)
        have e : (1 - t) • -a₂ = (t - 1) • a₂ := by rw [smul_neg, ← neg_smul, neg_sub]
        rw [e]
        exact ⟨hU, heq⟩
      endB₂ := by
        intro t ht
        have hs : |hh t - -1| < ε₁ := by
          simp only [hhdef]
          rw [show 2 / Real.pi * t - 1 - -1 = 2 / Real.pi * t by ring, abs_mul,
            abs_of_pos h2π]
          calc 2 / Real.pi * |t| < 2 / Real.pi * δ :=
                mul_lt_mul_of_pos_left ht h2π
            _ ≤ 2 / Real.pi * (Real.pi / 2 * ε₁) := mul_le_mul_of_nonneg_left hδ3 h2π.le
            _ = ε₁ := hc₀ ε₁
        obtain ⟨hU, heq⟩ := hη₁end (hh t) hs
        have e : (hh t - -1) • c₂ = t • ((2 / Real.pi) • c₂) := by
          rw [smul_smul]
          congr 1
          simp only [hhdef]
          ring
        rw [e] at hU heq
        have hfar : 1 ≤ |hh t - 1| := by
          rw [abs_lt] at hs
          rw [abs_sub_comm, le_abs]
          left
          linarith only [hs.2, hε₁ρ]
        exact ⟨hU, (hη₂far (hh t) hfar).trans heq⟩
      endB₁ := by
        intro t ht
        have hs : |hh t - 1| < ε₂ := by
          simp only [hhdef]
          rw [show 2 / Real.pi * t - 1 - 1 = 2 / Real.pi * (t - Real.pi) by
              rw [mul_sub, hπ2]; ring,
            abs_mul, abs_of_pos h2π]
          calc 2 / Real.pi * |t - Real.pi| < 2 / Real.pi * δ :=
                mul_lt_mul_of_pos_left ht h2π
            _ ≤ 2 / Real.pi * (Real.pi / 2 * ε₂) := mul_le_mul_of_nonneg_left hδ4 h2π.le
            _ = ε₂ := hc₀ ε₂
        obtain ⟨hU, heq⟩ := hη₂end (hh t) hs
        have e : (hh t - 1) • c₁ = (Real.pi - t) • -((2 / Real.pi) • c₁) := by
          rw [smul_neg, smul_smul, ← neg_smul]
          congr 1
          simp only [hhdef]
          rw [mul_comm (Real.pi - t), mul_sub, hπ2]
          ring
        rw [e] at hU heq
        exact ⟨hU, heq⟩ }

theorem isWhitneyCollar_of_local (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) {ε c : ℝ} {x₁ x₂ : M} {N : Set (Fin 2 → ℝ)} {ψ : (Fin 2 → ℝ) → M}
    (hN : IsOpen N) (hinj : InjOn ψ N) (hx₁ : ψ ![-1, 0] = x₁) (hx₂ : ψ ![1, 0] = x₂)
    (hloc : ∀ y ∈ N, ∃ N' : Set (Fin 2 → ℝ), N' ⊆ N ∧ IsOpen N' ∧ y ∈ N' ∧
      D.IsWhitneyCollar c hp hq ε x₁ x₂ N' ψ) :
    D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ := by
  choose! N' hN'N hN'o hyN' hcol using hloc
  exact
    { isOpen_N := hN
      smooth := contMDiffOn_of_locally_contMDiffOn fun y hy =>
        ⟨N' y, hN'o y hy, hyN' y hy,
          (hcol y hy).smooth.mono (inter_subset_right)⟩
      immersion := fun y hy => (hcol y hy).immersion y (hyN' y hy)
      inj := hinj
      level := fun y hy => (hcol y hy).level y (hyN' y hy)
      memA := fun y hy => (hcol y hy).memA y (hyN' y hy)
      memB := fun y hy => (hcol y hy).memB y (hyN' y hy)
      transA := fun y hy h1 => (hcol y hy).transA y (hyN' y hy) h1
      transB := fun y hy h1 => (hcol y hy).transB y (hyN' y hy) h1
      corner₁ := hx₁
      corner₂ := hx₂ }

theorem isWhitneyCollar_of_cornerFormula (D : GradientLikeStrip I f a b crit) {p q : M}
    (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) {ε c : ℝ} {x x₁ x₂ : M} {U : Set (Fin (n - 1) → ℝ)}
    {φ : (Fin (n - 1) → ℝ) → M} (hφ : D.IsCornerChart c hp hq ε ℓ x U φ)
    {a' b' : Fin (n - 1) → ℝ} (ha : a' ≠ 0) (haL : ∀ j, ℓ ≤ j → coordN a' j = 0) (hb : b' ≠ 0)
    (hbR : ∀ j, j < ℓ → coordN b' j = 0) {N : Set (Fin 2 → ℝ)} (hN : IsOpen N)
    (hN0 : ∀ y ∈ N, y ≠ 0) {α : (Fin 2 → ℝ) → ℝ} (hα : ContDiffOn ℝ ∞ α N)
    (hα0 : ∀ y ∈ N, α y = 0 ↔ y 1 = 0)
    (hαd : ∀ y ∈ N, y 1 = 0 → fderiv ℝ α y (Pi.single 1 1) ≠ 0)
    (hinj : InjOn (fun y : Fin 2 → ℝ => ![α y, Real.sqrt (y 0 ^ 2 + y 1 ^ 2)]) N)
    (himm : ∀ y ∈ N, Function.Injective (fderiv ℝ (fun y' : Fin 2 → ℝ =>
      ![α y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]) y))
    (hU : ∀ y ∈ N, (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b' ∈ U)
    {ψ : (Fin 2 → ℝ) → M}
    (hψ : ∀ y ∈ N, ψ y = φ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b'))
    (hx₁ : ψ ![-1, 0] = x₁) (hx₂ : ψ ![1, 0] = x₂) :
    D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ := by
  classical
  have hcoord : ∀ (s t : ℝ) (j : ℕ),
      coordN (s • a' + t • b') j = s * coordN a' j + t * coordN b' j := by
    intro s t j
    unfold coordN
    split_ifs <;> simp
  have hcoordFin : ∀ (v : Fin (n - 1) → ℝ) (i : Fin (n - 1)), coordN v i = v i := by
    intro v i
    simp [coordN, i.isLt]
  have hcoord0 : ∀ j : ℕ, coordN (0 : Fin (n - 1) → ℝ) j = 0 := by
    intro j
    simp [coordN]
  obtain ⟨ja, hja, hja0⟩ : ∃ j, j < ℓ ∧ coordN a' j ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    refine ⟨i, ?_, by rw [hcoordFin]; simpa using hi⟩
    by_contra h
    exact hi (by rw [← hcoordFin a' i]; exact haL _ (not_lt.1 h))
  obtain ⟨jb, hjb, hjb0, hjbn⟩ : ∃ j, ℓ ≤ j ∧ coordN b' j ≠ 0 ∧ j < n - 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
    refine ⟨i, ?_, by rw [hcoordFin]; simpa using hi, i.isLt⟩
    by_contra h
    exact hi (by rw [← hcoordFin b' i]; exact hbR _ (not_le.1 h))
  have hindep : ∀ s t : ℝ, s • a' + t • b' = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h1 := congrArg (fun v => coordN v ja) h
    have h2 := congrArg (fun v => coordN v jb) h
    simp only [hcoord, hcoord0] at h1 h2
    rw [hbR ja hja] at h1
    rw [haL jb hjb] at h2
    constructor
    · have : s * coordN a' ja = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hja0
    · have : t * coordN b' jb = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hjb0
  have hpos : ∀ y ∈ N, 0 < y 0 ^ 2 + y 1 ^ 2 := by
    intro y hy
    rcases (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hN0 y hy
      have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      funext i
      fin_cases i <;> simp [h0, h1]
  have hs : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have hrs : ContDiffOn ℝ ∞ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) N :=
    fun y hy => (hs.contDiffAt.sqrt (hpos y hy).ne').contDiffWithinAt
  have hιs : ContDiffOn ℝ ∞
      (fun y : Fin 2 → ℝ => (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b') N :=
    ((contDiffOn_const.sub hrs).smul contDiffOn_const).add (hα.smul contDiffOn_const)
  set L : (Fin 2 → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) :=
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (-a') +
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight b' with hL
  have hLinj : Function.Injective L := by
    intro z w hzw
    have h0 : (-(z 1 - w 1)) • a' + (z 0 - w 0) • b' = 0 := by
      have : L z - L w = 0 := sub_eq_zero.2 hzw
      rw [← this, hL]
      simp only [add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.proj_apply]
      module
    obtain ⟨e1, e0⟩ := hindep _ _ h0
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
  have hιeq : (fun y : Fin 2 → ℝ => (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b') =
      fun y => a' + L ![α y, Real.sqrt (y 0 ^ 2 + y 1 ^ 2)] := by
    funext y
    rw [hL]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  have hPd : ∀ y ∈ N,
      DifferentiableAt ℝ (fun y' : Fin 2 → ℝ => ![α y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]) y := by
    intro y hy
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · simpa using (hα.contDiffAt (hN.mem_nhds hy)).differentiableAt (by simp)
    · simpa using (hrs.contDiffAt (hN.mem_nhds hy)).differentiableAt (by simp)
  have hιd : ∀ y ∈ N, fderiv ℝ
      (fun y : Fin 2 → ℝ => (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b') y =
      L.comp (fderiv ℝ (fun y' : Fin 2 → ℝ => ![α y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]) y) := by
    intro y hy
    rw [hιeq]
    exact ((L.hasFDerivAt.comp y (hPd y hy).hasFDerivAt).const_add a').fderiv
  refine
    { isOpen_N := hN
      smooth := ?_
      immersion := ?_
      inj := ?_
      level := ?_
      memA := ?_
      memB := ?_
      transA := ?_
      transB := ?_
      corner₁ := hx₁
      corner₂ := hx₂ }
  · exact (hφ.smooth.comp hιs.contMDiffOn (fun y hy => hU y hy)).congr (fun y hy => hψ y hy)
  · intro y hy
    have hev : ψ =ᶠ[𝓝 y]
        (φ ∘ fun y : Fin 2 → ℝ => (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' + α y • b') :=
      Filter.eventually_of_mem (hN.mem_nhds hy) (fun y' hy' => hψ y' hy')
    have hφd := (hφ.smooth.contMDiffAt (hφ.isOpen_U.mem_nhds (hU y hy))).mdifferentiableAt
      (by simp)
    have hιd' := ((hιs.contDiffAt (hN.mem_nhds hy)).differentiableAt (by simp)).mdifferentiableAt
    rw [hev.mfderiv_eq, mfderiv_comp y hφd hιd', mfderiv_eq_fderiv, hιd y hy]
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
    exact (ContinuousLinearEquiv.injective _).comp ((hφ.immersion _ (hU y hy)).comp
      (hLinj.comp (himm y hy)))
  · intro y hy y' hy' h
    rw [hψ y hy, hψ y' hy'] at h
    have h2 := hφ.inj (hU y hy) (hU y' hy') h
    have h3 : (Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a' +
        (α y - α y') • b' = 0 := by
      rw [← sub_eq_zero.2 h2]
      module
    obtain ⟨e1, e2⟩ := hindep _ _ h3
    apply hinj hy hy'
    change ![α y, Real.sqrt (y 0 ^ 2 + y 1 ^ 2)] = ![α y', Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]
    rw [show α y = α y' by linarith,
      show Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) by linarith]
  · intro y hy
    rw [hψ y hy]
    exact hφ.level _ (hU y hy)
  · intro y hy
    rw [hψ y hy, hφ.memL _ (hU y hy), ← hα0 y hy]
    constructor
    · intro h
      have := h jb hjb
      rw [hcoord, haL jb hjb, mul_zero, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_right hjb0
    · intro h j hj
      rw [hcoord, haL j hj, h]
      ring
  · intro y hy
    rw [hψ y hy, hφ.memR _ (hU y hy), ← Real.sqrt_eq_one]
    constructor
    · intro h
      have := h ja hja
      rw [hcoord, hbR ja hja, mul_zero, add_zero] at this
      have := (mul_eq_zero.1 this).resolve_right hja0
      linarith
    · intro h j hj
      rw [hcoord, hbR j hj, h]
      ring
  · intro y hy hy1
    set B : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)) :=
      WithLp.toLp 2 (fun i : Fin (n - (D.chart q hq).k) => coordN b' (ℓ + i)) with hB
    have hev : (fun y => D.leftCoord q hq ε (ψ y)) =ᶠ[𝓝 y] fun y => α y • B := by
      filter_upwards [hN.mem_nhds hy] with y' hy'
      refine PiLp.ext fun i => ?_
      rw [hψ y' hy', hφ.coordL _ (hU y' hy'), hcoord, haL _ (Nat.le_add_right _ _), hB]
      simp
    have hαdiff : DifferentiableAt ℝ α y :=
      (hα.contDiffAt (hN.mem_nhds hy)).differentiableAt (by simp)
    rw [hev.fderiv_eq, fderiv_smul_const hαdiff, ContinuousLinearMap.smulRight_apply]
    refine smul_ne_zero (hαd y hy hy1) ?_
    intro hB0
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)) =>
      v.ofLp ⟨jb - ℓ, by rw [hkq]; omega⟩) hB0
    simp only [hB, PiLp.toLp_apply, PiLp.zero_apply] at this
    rw [Nat.add_sub_cancel' hjb] at this
    exact hjb0 this
  · intro y hy hy1
    set A : EuclideanSpace ℝ (Fin (D.chart p hp).k) :=
      WithLp.toLp 2 (fun i : Fin (D.chart p hp).k => coordN a' i) with hA
    have hev : (fun y => D.rightCoord p hp ε (ψ y)) =ᶠ[𝓝 y]
        fun y => (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • A := by
      filter_upwards [hN.mem_nhds hy] with y' hy'
      refine PiLp.ext fun i => ?_
      rw [hψ y' hy', hφ.coordR _ (hU y' hy'), hcoord, hbR _ (hkp ▸ i.isLt), hA]
      simp
    have hsD : HasFDerivAt (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2)
        ((2 * y 0) • ContinuousLinearMap.proj 0 + (2 * y 1) • ContinuousLinearMap.proj 1 :
          (Fin 2 → ℝ) →L[ℝ] ℝ) y := by
      have := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y).pow 2).add
        ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y).pow 2)
      convert this using 1
      ext v
      simp
    have h1D := (hsD.sqrt (by rw [hy1]; norm_num)).const_sub 1
    have h1d : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) y :=
      h1D.differentiableAt
    rw [hev.fderiv_eq, fderiv_smul_const h1d, ContinuousLinearMap.smulRight_apply, h1D.fderiv]
    refine smul_ne_zero ?_ ?_
    · simp only [neg_apply, smul_apply,
        add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, hy1,
        Real.sqrt_one]
      nlinarith [hy1]
    · intro hA0
      have := congrArg (fun v : EuclideanSpace ℝ (Fin (D.chart p hp).k) =>
        v.ofLp ⟨ja, by rw [hkp]; exact hja⟩) hA0
      simp only [hA, PiLp.toLp_apply, PiLp.zero_apply] at this
      exact hja0 this

theorem diameterStrip_middle (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ε c : ℝ} (hv : D.sardValid ε p hq hp)
    (hc₁ : f p + ε < c) (hc₂ : c < f q - ε) {γA : ℝ → M} (hγA : ContMDiff 𝓘(ℝ, ℝ) I ∞ γA)
    (hmemA : ∀ t ∈ Icc (-1 : ℝ) 1, γA t ∈ D.leftSphere q hq ε c ∧
      (γA t ∈ D.rightSphere p hp ε c ↔ t = -1 ∨ t = 1))
    (X : LevelField I f)
    (htr : ∀ t ∈ Icc (-1 : ℝ) 1,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (γA t)
        (X.Y (γA t)) ≠ 0)
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω) {σ τ : (Fin 2 → ℝ) → ℝ}
    (hψ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ (fun y => X.flow (τ y) (γA (σ y))) Ω)
    (hτ0 : ∀ y ∈ Ω, τ y = 0 ↔ y 1 = 0)
    (hbd : ∀ y ∈ Ω, |σ y - y 0| ≤ |y 1| ∧ |τ y| ≤ 2 * |y 1|)
    (hτd : ∀ y ∈ Ω, y 1 = 0 → fderiv ℝ τ y (Pi.single 1 1) ≠ 0)
    (hder : ∀ y ∈ Ω, τ y = 0 → ∀ v : Fin 2 → ℝ,
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun y' => X.flow (τ y') (γA (σ y'))) y v =
        fderiv ℝ σ y v • (mfderiv 𝓘(ℝ, ℝ) I γA (σ y) 1 : TangentSpace I (γA (σ y))) +
          fderiv ℝ τ y v • X.Y (γA (σ y)))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ y ∈ Ω, |y 0| ≤ 1 - κ → |y 1| < r →
      (X.flow (τ y) (γA (σ y)) ∈ D.leftSphere q hq ε c ↔ y 1 = 0) ∧
      X.flow (τ y) (γA (σ y)) ∉ D.rightSphere p hp ε c ∧ y 0 ^ 2 + y 1 ^ 2 ≠ 1 ∧
      (y 1 = 0 → fderiv ℝ (fun y' => D.leftCoord q hq ε (X.flow (τ y') (γA (σ y')))) y
        (Pi.single 1 1) ≠ 0) := by
  obtain ⟨hε, -, -, hrmp, hrmq, -, hUv⟩ := hv
  have hp0 : f p ∈ Ioo a b :=
    D.inStrip p hp ⟨0, (D.chart p hp).zero_mem_ball, (D.chart p hp).hχ0⟩
  have hq0 : f q ∈ Ioo a b :=
    D.inStrip q hq ⟨0, (D.chart q hq).zero_mem_ball, (D.chart q hq).hχ0⟩
  have hac : a ≤ c := by linarith [hp0.1]
  have hcb : c ≤ b := by linarith [hq0.2]
  have hrmq2 : 2 * ε < D.rm q hq ^ 2 := by linarith
  have hU : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
    hUv y ⟨by linarith [hy.1], hy.2⟩
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 : D.rm q hq ≤ (D.chart q hq).R := (D.hrm q hq).2
    have h0 : 0 < D.rm q hq := D.rm_pos q hq
    nlinarith
  have hRp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by
    have h1 : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
    have h0 : 0 < D.rm p hp := D.rm_pos p hp
    nlinarith
  have hSLlev : D.leftSphere q hq ε c ⊆ f ⁻¹' {c} :=
    D.leftSphere_subset_level hf q hq hRq ⟨hac, hcb⟩ (fun y hy x hx =>
      hU y (by rwa [uIcc_of_ge hc₂.le] at hy) x hx)
  obtain ⟨O, hO, hSO, hG, -⟩ := D.leftCoord_submersion hf hq hε hrmq2 hac hc₂.le hU
  have hG0 : ∀ t ∈ Icc (-1 : ℝ) 1, D.leftCoord q hq ε (γA t) = 0 := fun t ht =>
    ((D.mem_leftSphere_iff_coord hf hq hε hrmq2 hac hc₂.le hU (hSLlev (hmemA t ht).1)).1
      (hmemA t ht).1).1
  have hγO : ∀ t ∈ Icc (-1 : ℝ) 1, γA t ∈ O := fun t ht => hSO (hmemA t ht).1
  obtain ⟨η₁, hη₁, hK5⟩ := exists_flowStrip_zero_iff X hγA.continuous hO hγO hG hG0 htr
  have hSRc : IsClosed (D.rightSphere p hp ε c) := (D.isCompact_rightSphere p hp hRp c).isClosed
  obtain ⟨η₂, hη₂, hK8⟩ := X.exists_flow_mem hγA.continuous
    (isCompact_Icc (a := -1 + κ) (b := 1 - κ)) hSRc.isOpen_compl (fun t ht => by
      have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      intro hmem
      rcases ((hmemA t ht').2).1 hmem with h | h <;> linarith [ht.1, ht.2])
  have hflow0 : ∀ x, X.flow 0 x = x := fun x => by
    unfold LevelField.flow
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  refine ⟨min (κ / 2) (min (η₁ / 2) (η₂ / 2)), by positivity, ?_⟩
  intro y hy hy0 hy1
  have hr1 : |y 1| < κ / 2 := lt_of_lt_of_le hy1 (min_le_left _ _)
  have hr2 : |y 1| < η₁ / 2 :=
    lt_of_lt_of_le hy1 ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : |y 1| < η₂ / 2 :=
    lt_of_lt_of_le hy1 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hbσ, hbτ⟩ := hbd y hy
  have hσ1 := abs_le.1 hbσ
  have hy0' := abs_le.1 hy0
  have hy1' := abs_lt.1 hr1
  have hσo : σ y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hσ : σ y ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hσo
  have hτ : τ y ∈ Ioo (-η₁) η₁ := by
    have := abs_lt.1 (lt_of_le_of_lt hbτ (by linarith : 2 * |y 1| < η₁))
    exact ⟨this.1, this.2⟩
  obtain ⟨hzO, hzG⟩ := hK5 (σ y) hσ (τ y) hτ
  have hfz : f (X.flow (τ y) (γA (σ y))) = c := by
    rw [X.comp_flow hf]
    exact hSLlev (hmemA _ hσ).1
  refine ⟨⟨fun hmem => ?_, fun h1 => ?_⟩, ?_, ?_, fun h1 => ?_⟩
  · have h := ((D.mem_leftSphere_iff_coord hf hq hε hrmq2 hac hc₂.le hU hfz).1 hmem).1
    exact (hτ0 y hy).1 (hzG.1 h)
  · rw [(hτ0 y hy).2 h1, hflow0]
    exact (hmemA _ hσ).1
  · exact hK8 (σ y) (y 0) ⟨by linarith, by linarith⟩ (lt_of_le_of_lt hbσ (by linarith))
      (τ y) (lt_of_le_of_lt hbτ (by linarith))
  · intro hsq
    have h0 : y 0 ^ 2 ≤ (1 - κ) ^ 2 := by nlinarith
    have h1 : y 1 ^ 2 < (κ / 2) ^ 2 := by nlinarith
    nlinarith
  · have hτ0' : τ y = 0 := (hτ0 y hy).2 h1
    have hψy : X.flow (τ y) (γA (σ y)) = γA (σ y) := by rw [hτ0', hflow0]
    have hψd : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I
        (fun y' => X.flow (τ y') (γA (σ y'))) y :=
      (hψ.mdifferentiableOn (by simp)).mdifferentiableAt (hΩ.mem_nhds hy)
    have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
        (D.leftCoord q hq ε) (X.flow (τ y) (γA (σ y))) :=
      (hG.mdifferentiableOn (by simp)).mdifferentiableAt (hO.mem_nhds hzO)
    have hcomp := mfderiv_comp y hGd hψd
    rw [mfderiv_eq_fderiv] at hcomp
    have hval : fderiv ℝ (fun y' => D.leftCoord q hq ε (X.flow (τ y') (γA (σ y')))) y
        (Pi.single 1 1) =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε)
          (X.flow (τ y) (γA (σ y)))
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I (fun y' => X.flow (τ y') (γA (σ y'))) y
            (Pi.single 1 1)) := by
      have := congrArg (fun L => L (Pi.single 1 1)) hcomp
      exact this
    have hγz : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
        (D.leftCoord q hq ε) (γA (σ y))
        (mfderiv 𝓘(ℝ, ℝ) I γA (σ y) 1 : TangentSpace I (γA (σ y))) = 0 := by
      have hGd' : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
          (D.leftCoord q hq ε) (γA (σ y)) :=
        (hG.mdifferentiableOn (by simp)).mdifferentiableAt (hO.mem_nhds (hγO _ hσ))
      have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γA (σ y) := hγA.mdifferentiableAt (by simp)
      have hc := mfderiv_comp (σ y) hGd' hγd
      rw [mfderiv_eq_fderiv] at hc
      have hev : (D.leftCoord q hq ε ∘ γA) =ᶠ[𝓝 (σ y)] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds hσo.1 hσo.2] with t ht
        exact hG0 t (Ioo_subset_Icc_self ht)
      have h0 : fderiv ℝ (D.leftCoord q hq ε ∘ γA) (σ y) = 0 := by
        rw [hev.fderiv_eq]
        exact fderiv_const_apply 0
      have h2 : (fderiv ℝ (D.leftCoord q hq ε ∘ γA) (σ y)) 1 = 0 := by
        rw [h0]
        rfl
      exact (DFunLike.congr_fun hc 1).symm.trans h2
    rw [hval]
    rw [hψy]
    have key : ∀ w : TangentSpace I (γA (σ y)),
        w = fderiv ℝ σ y (Pi.single 1 1) •
            (mfderiv 𝓘(ℝ, ℝ) I γA (σ y) 1 : TangentSpace I (γA (σ y))) +
          fderiv ℝ τ y (Pi.single 1 1) • X.Y (γA (σ y)) →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε)
          (γA (σ y)) w ≠ 0 := by
      rintro w rfl
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
        ContinuousLinearMap.map_smul, hγz, smul_zero, zero_add]
      exact smul_ne_zero (hτd y hy h1) (htr _ hσ)
    exact key _ (hder y hy hτ0' (Pi.single 1 1))

theorem circleStrip_middle (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ε c : ℝ} (hv : D.sardValid ε p hq hp)
    (hc₁ : f p + ε < c) (hc₂ : c < f q - ε) {γB : ℝ → M} (hγB : ContMDiff 𝓘(ℝ, ℝ) I ∞ γB)
    (hmemB : ∀ t ∈ Icc (0 : ℝ) Real.pi, γB t ∈ D.rightSphere p hp ε c ∧
      (γB t ∈ D.leftSphere q hq ε c ↔ t = 0 ∨ t = Real.pi))
    (X' : LevelField I f)
    (htr : ∀ t ∈ Icc (0 : ℝ) Real.pi,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (γB t)
        (X'.Y (γB t)) ≠ 0)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞
      (fun y => X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y)))
      {y | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1})
    (hder : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = 1 → ∀ v : Fin 2 → ℝ,
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I
          (fun y' => X'.flow (1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) (γB (whitneyAngle y'))) y v =
        fderiv ℝ whitneyAngle y v •
            (mfderiv 𝓘(ℝ, ℝ) I γB (whitneyAngle y) 1 : TangentSpace I (γB (whitneyAngle y))) +
          fderiv ℝ (fun y' : Fin 2 → ℝ => 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) y v •
            X'.Y (γB (whitneyAngle y)))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      |1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)| < r → κ ≤ whitneyAngle y →
      whitneyAngle y ≤ Real.pi - κ →
      (X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y)) ∈
          D.rightSphere p hp ε c ↔ y 0 ^ 2 + y 1 ^ 2 = 1) ∧
      X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y)) ∉
        D.leftSphere q hq ε c ∧ y 1 ≠ 0 ∧
      (y 0 ^ 2 + y 1 ^ 2 = 1 → fderiv ℝ (fun y' => D.rightCoord p hp ε
        (X'.flow (1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) (γB (whitneyAngle y')))) y y ≠ 0) := by
  obtain ⟨hε, -, -, hrmp, hrmq, -, hUv⟩ := hv
  have hq0 : f q ∈ Ioo a b :=
    D.inStrip q hq ⟨0, (D.chart q hq).zero_mem_ball, (D.chart q hq).hχ0⟩
  have hp0 : f p ∈ Ioo a b :=
    D.inStrip p hp ⟨0, (D.chart p hp).zero_mem_ball, (D.chart p hp).hχ0⟩
  have hrmRp : D.rm p hp ≤ (D.chart p hp).R := (D.hrm p hp).2
  have hrmRq : D.rm q hq ≤ (D.chart q hq).R := (D.hrm q hq).2
  have hrm0p := D.rm_pos p hp
  have hrm0q := D.rm_pos q hq
  have hRp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by nlinarith
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by nlinarith
  have hU : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
    hUv y ⟨hy.1, hy.2.trans hc₂.le⟩
  have hcb : c ≤ b := by linarith [hq0.2]
  have hlevel : ∀ z ∈ D.rightSphere p hp ε c, f z = c := fun z hz =>
    D.rightSphere_subset_level hf p hp hRp ⟨by linarith [hp0.1], hcb⟩
      (by rw [uIcc_of_le (by linarith)]; exact hU) hz
  obtain ⟨O, hOo, hSO, hGO, -⟩ :=
    D.rightCoord_submersion hf hp hε (by linarith) hc₁.le hcb hU
  have hmemR : ∀ z, f z = c → (z ∈ D.rightSphere p hp ε c ↔ D.rightCoord p hp ε z = 0 ∧
      D.flow (c - (f p + ε)) z ∈ (D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp}) :=
    fun z hz => D.mem_rightSphere_iff_coord hf hp hε (by linarith) hc₁.le hcb hU hz
  have hJsub : ∀ t ∈ Icc κ (Real.pi - κ), t ∈ Icc (0 : ℝ) Real.pi := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hSRγ : ∀ t ∈ Icc κ (Real.pi - κ), γB t ∈ D.rightSphere p hp ε c := fun t ht =>
    (hmemB t (hJsub t ht)).1
  obtain ⟨η₁, hη₁, hK5⟩ := exists_flowStrip_zero_iff X' hγB.continuous hOo
    (fun t ht => hSO (hSRγ t ht)) hGO
    (fun t ht => ((hmemR _ (hlevel _ (hSRγ t ht))).1 (hSRγ t ht)).1)
    (fun t ht => htr t (hJsub t ht))
  obtain ⟨η₂, hη₂, hK8W⟩ := X'.exists_flow_mem hγB.continuous (isCompact_Icc (a := κ)
    (b := Real.pi - κ)) ((D.isOpen_modelBall p hp).preimage (D.continuous_flow _))
    (fun t ht => ((hmemR _ (hlevel _ (hSRγ t ht))).1 (hSRγ t ht)).2)
  obtain ⟨η₃, hη₃, hK8L⟩ := X'.exists_flow_mem hγB.continuous (isCompact_Icc (a := κ)
    (b := Real.pi - κ)) (D.isCompact_leftSphere q hq hRq c).isClosed.isOpen_compl
    (fun t ht => by
      intro hmem
      rcases (hmemB t (hJsub t ht)).2.1 hmem with h | h
      · linarith [ht.1]
      · linarith [ht.2])
  refine ⟨min (min η₁ η₂) (min η₃ (1 / 2)), by positivity, ?_⟩
  intro y hy hr hθ1 hθ2
  have hΩo : IsOpen {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} :=
    isOpen_lt continuous_const (by fun_prop)
  obtain ⟨-, -, -, hpol, -, hθd⟩ := whitneyAngle_spec
  set s := Real.sqrt (y 0 ^ 2 + y 1 ^ 2) with hs_def
  set θ := whitneyAngle y with hθ_def
  have hθJ : θ ∈ Icc κ (Real.pi - κ) := ⟨hθ1, hθ2⟩
  have hr1 : |1 - s| < η₁ := hr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : |1 - s| < η₂ := hr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : |1 - s| < η₃ := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : |1 - s| < 1 / 2 := hr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hK5y := hK5 θ hθJ (1 - s) ⟨(abs_lt.1 hr1).1, (abs_lt.1 hr1).2⟩
  have hflev : f (X'.flow (1 - s) (γB θ)) = c :=
    (X'.comp_flow hf _ _).trans (hlevel _ (hSRγ θ hθJ))
  have hs1 : s = 1 ↔ y 0 ^ 2 + y 1 ^ 2 = 1 := Real.sqrt_eq_one
  have hθ0 : θ ∈ Ioo 0 Real.pi := ⟨by linarith, by linarith⟩
  refine ⟨?_, hK8L θ θ hθJ (by simpa using hη₃) _ hr3, ?_, ?_⟩
  · rw [hmemR _ hflev, ← hs1]
    constructor
    · rintro ⟨h0, -⟩
      have := hK5y.2.1 h0
      linarith
    · intro h
      exact ⟨hK5y.2.2 (by linarith), hK8W θ θ hθJ (by simpa using hη₂) _ hr2⟩
  · have hspos : 0 < s := by
      have := (abs_lt.1 hr4).2
      linarith
    rw [(hpol y hy).2.2]
    exact (mul_pos hspos (Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0.2)).ne'
  · intro h1
    have hs1' : s = 1 := hs1.2 h1
    let ψ' : (Fin 2 → ℝ) → M := fun y' =>
      X'.flow (1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) (γB (whitneyAngle y'))
    have hψy : ψ' y = γB θ := by
      change X'.flow (1 - s) (γB θ) = γB θ
      rw [hs1', sub_self]
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ _
    have hψd : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I ψ' y :=
      (hψ.contMDiffAt (hΩo.mem_nhds hy)).mdifferentiableAt (by simp)
    have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (γB θ) :=
      (hGO.contMDiffAt (hOo.mem_nhds (hSO (hSRγ θ hθJ)))).mdifferentiableAt (by simp)
    have hGd' : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (ψ' y) := hψy ▸ hGd
    have hτd : fderiv ℝ (fun y' : Fin 2 → ℝ => 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) y y = -1 := by
      have hfun : (fun y' : Fin 2 → ℝ => 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) =
          fun y' => 1 - Real.sqrt (y' 0 * y' 0 + y' 1 * y' 1) := by
        funext y'
        ring_nf
      have ha := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 y
      have hb := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 y
      have hsq : HasFDerivAt (fun y' : Fin 2 → ℝ => y' 0 * y' 0 + y' 1 * y' 1) _ y :=
        (ha.mul ha).add (hb.mul hb)
      have h1' : y 0 * y 0 + y 1 * y 1 = 1 := by rw [← h1]; ring
      have hne : y 0 * y 0 + y 1 * y 1 ≠ 0 := by rw [h1']; norm_num
      have hd := ((hsq.sqrt hne).const_sub 1).fderiv
      rw [hfun, hd]
      simp only [neg_apply, smul_apply,
        add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, h1',
        Real.sqrt_one]
      nlinarith [h1']
    have hchain : fderiv ℝ (fun y' => D.rightCoord p hp ε (ψ' y')) y y =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (ψ' y)
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ' y y) := by
      have hc := mfderiv_comp y hGd' hψd
      rw [mfderiv_eq_fderiv] at hc
      exact DFunLike.congr_fun hc y
    change fderiv ℝ (fun y' => D.rightCoord p hp ε (ψ' y')) y y ≠ 0
    rw [hchain, hder y hy hs1' y, (hθd y hy).2.1, hτd, zero_smul, zero_add, neg_one_smul]
    intro h0
    apply htr θ (hJsub θ hθJ)
    have key := (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε)
      (ψ' y)).map_neg (X'.Y (γB θ))
    erw [key, neg_eq_zero] at h0
    rw [hψy] at h0
    exact h0

theorem exists_diameterStrip (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {x₁ x₂ : M} {U₁ U₂ : Set (Fin (n - 1) → ℝ)}
    {φ₁ φ₂ : (Fin (n - 1) → ℝ) → M} (hφ₁ : D.IsCornerChart c hp hq ε ℓ x₁ U₁ φ₁)
    (hφ₂ : D.IsCornerChart c hp hq ε ℓ x₂ U₂ φ₂) {γA γB : ℝ → M} {a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ}
    {δ : ℝ} (harcs : D.IsWhitneyArcs c hp hq ε ℓ φ₁ φ₂ U₁ U₂ γA γB a₁ a₂ b₁ b₂ δ)
    (X : LevelField I f) {V₁ V₂ : Set (Fin (n - 1) → ℝ)} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (h0V₁ : (0 : Fin (n - 1) → ℝ) ∈ V₁) (h0V₂ : (0 : Fin (n - 1) → ℝ) ∈ V₂) (hV₁U : V₁ ⊆ U₁)
    (hV₂U : V₂ ⊆ U₂)
    (hX₁ : ∀ z ∈ V₁, X.Y (φ₁ z) = mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ₁ z b₁)
    (hX₂ : ∀ z ∈ V₂, X.Y (φ₂ z) = mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ₂ z b₂)
    (htr : ∀ t ∈ Icc (-1 : ℝ) 1,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (γA t)
        (X.Y (γA t)) ≠ 0) :
    ∃ ρ r₁ : ℝ, 0 < ρ ∧ 0 < r₁ ∧ ∃ (N : Set (Fin 2 → ℝ)) (ψ : (Fin 2 → ℝ) → M),
      {y | y ∈ whitneyHalf ∧ y 1 ≤ r₁} ⊆ N ∧ D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ ∧
      (∀ y ∈ N, dist y ![-1, 0] < ρ →
        ψ y = φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁)) ∧
      (∀ y ∈ N, dist y ![1, 0] < ρ →
        ψ y = φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂)) ∧
      ∀ O : Set M, IsOpen O → ∀ κ : ℝ, 0 < κ → (∀ t ∈ Icc (-1 + κ) (1 - κ), γA t ∈ O) →
        ∃ r' > 0, ∀ y ∈ N, |y 1| < r' → |y 0| ≤ 1 - 2 * κ → ψ y ∈ O := by
  classical
  have _ : 6 ≤ n ∧ 2 ≤ ℓ ∧ ℓ + 3 ≤ n := ⟨h6, hℓ, hℓn⟩
  obtain ⟨hε, -, -, h8p, h8q, hpq, hU⟩ := id hv
  have hq0 : f q ∈ Ioo a b :=
    D.inStrip q hq ⟨0, (D.chart q hq).zero_mem_ball, (D.chart q hq).hχ0⟩
  have hp0 : f p ∈ Ioo a b :=
    D.inStrip p hp ⟨0, (D.chart p hp).zero_mem_ball, (D.chart p hp).hχ0⟩
  have hac : a ≤ c := by linarith [hp0.1]
  have hcb : c ≤ b := by linarith [hq0.2]
  have hrmq : 2 * ε < D.rm q hq ^ 2 := by linarith
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos q hq).le h1 2
    linarith
  have hUq : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hU y ⟨by linarith [hy.1], hy.2⟩
  have hlevS : D.leftSphere q hq ε c ⊆ f ⁻¹' {c} :=
    D.leftSphere_subset_level hf q hq hRq ⟨hac, hcb⟩ (fun y hy => by
      rw [uIcc_of_ge hc₂.le] at hy
      exact hUq y hy)
  obtain ⟨OL, hOL, hSOL, hGsm, -⟩ := leftCoord_submersion hf D hq hε hrmq hac hc₂.le hUq
  have hδ := harcs.hδ
  have hcoord_smul : ∀ (s : ℝ) (v : Fin (n - 1) → ℝ) (j : ℕ), coordN (s • v) j = s * coordN v j := by
    intro s v j
    unfold coordN
    split_ifs <;> simp
  have hG0 : ∀ t ∈ Ioo (-1 - δ) (1 + δ), D.leftCoord q hq ε (γA t) = 0 := by
    intro t ht
    by_cases h1 : t < -1
    · obtain ⟨hmem, heq⟩ := harcs.endA₁ t (by rw [abs_lt]; constructor <;> linarith [ht.1])
      rw [heq]
      ext i
      rw [hφ₁.coordL _ hmem i, hcoord_smul, harcs.dirA.2.2.1 _ (Nat.le_add_right _ _), mul_zero]
      rfl
    by_cases h2 : 1 < t
    · obtain ⟨hmem, heq⟩ := harcs.endA₂ t (by rw [abs_lt]; constructor <;> linarith [ht.2])
      rw [heq]
      ext i
      rw [hφ₂.coordL _ hmem i, hcoord_smul, harcs.dirA.2.2.2 _ (Nat.le_add_right _ _), mul_zero]
      rfl
    have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨not_lt.1 h1, not_lt.1 h2⟩
    have hS := (harcs.memA t htI).1
    exact ((mem_leftSphere_iff_coord hf D hq hε hrmq hac hc₂.le hUq (hlevS hS)).1 hS).1
  have hdG0 : ∀ t ∈ Icc (-1 : ℝ) 1,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (γA t)
        (mfderiv 𝓘(ℝ, ℝ) I γA t 1) = 0 := by
    intro t ht
    have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
        (D.leftCoord q hq ε) (γA t) :=
      ((hGsm _ (hSOL (harcs.memA t ht).1)).contMDiffAt
        (hOL.mem_nhds (hSOL (harcs.memA t ht).1))).mdifferentiableAt (by simp)
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γA t :=
      (harcs.smoothA t).mdifferentiableAt (by simp)
    have hev : (D.leftCoord q hq ε ∘ γA) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (show -1 - δ < t by linarith [ht.1])
        (show t < 1 + δ by linarith [ht.2])] with s hs
      exact hG0 s hs
    have h1 := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))))
      (0 : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) t).congr_of_eventuallyEq hev
    have h2 := hGd.hasMFDerivAt.comp t hγd.hasMFDerivAt
    have h3 := h2.mfderiv.symm.trans h1.mfderiv
    have h4 := congrArg (fun L => L 1) h3
    simpa using h4
  have hind : ∀ t ∈ Icc (-1 : ℝ) 1,
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I γA t 1 : TangentSpace I (γA t)), X.Y (γA t)] := by
    intro t ht
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have h1 := congrArg (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
      (D.leftCoord q hq ε) (γA t)) hsu
    rw [map_add, map_smul, map_smul, hdG0 t ht, smul_zero, zero_add, map_zero] at h1
    have hu : u = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h (htr t ht)
    rw [hu, zero_smul, add_zero] at hsu
    refine ⟨?_, hu⟩
    rcases smul_eq_zero.1 hsu with h | h
    · exact h
    · exact absurd h (harcs.immA t ht)
  obtain ⟨r₀, ρ₀, hr₀, hr₀ρ₀, hρ₀, σ, τ, hσs, hτs, hτ0, hσline, hbd, hinjστ, himmστ, hcornL,
    hcornR⟩ := exists_diameterReparam
  set Sg : Set (Fin 2 → ℝ) := {y | |y 0| < 1 + r₀ ∧ |y 1| < r₀} with hSgdef
  have hSgo : IsOpen Sg :=
    (isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_apply 1)) continuous_const)
  obtain ⟨hψsm, hder, η, hη, hII⟩ := exists_reparamFlowStrip X harcs.smoothA
    (by norm_num : (-1 : ℝ) ≤ 1) harcs.injA hind hSgo hσs hτs hinjστ
    (fun y hy => himmστ y hy.1 hy.2)
  have hpi : ∀ (u w : (Fin 2 → ℝ) → ℝ) (y : Fin 2 → ℝ), DifferentiableAt ℝ u y →
      DifferentiableAt ℝ w y → ∀ v, fderiv ℝ (fun y' => ![u y', w y']) y v =
        ![fderiv ℝ u y v, fderiv ℝ w y v] := by
    intro u w y hu hw v
    have h : HasFDerivAt (fun y' => ![u y', w y'])
        (ContinuousLinearMap.pi (fun i => ![fderiv ℝ u y, fderiv ℝ w y] i)) y := by
      rw [hasFDerivAt_pi']
      intro i
      fin_cases i
      · simpa using hu.hasFDerivAt
      · simpa using hw.hasFDerivAt
    rw [h.fderiv]
    ext i
    fin_cases i <;> simp
  have hτd : ∀ y ∈ Sg, y 1 = 0 → fderiv ℝ τ y (Pi.single 1 1) ≠ 0 := by
    intro y hy hy1
    have hσd : DifferentiableAt ℝ σ y :=
      (hσs.contDiffAt (hSgo.mem_nhds hy)).differentiableAt (by simp)
    have hτdd : DifferentiableAt ℝ τ y :=
      (hτs.contDiffAt (hSgo.mem_nhds hy)).differentiableAt (by simp)
    have hline : ∀ s : ℝ, y + s • Pi.single 0 1 = ![y 0 + s, 0] := by
      intro s
      ext i
      fin_cases i <;> simp [hy1]
    have hlin : HasDerivAt (fun s : ℝ => y + s • (Pi.single 0 1 : Fin 2 → ℝ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 2 → ℝ)).const_add y
    have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), |y 0 + s| < 1 + r₀ := by
      have hc : Continuous fun s : ℝ => |y 0 + s| := by fun_prop
      have h0 : |y 0 + 0| < 1 + r₀ := by simpa using hy.1
      exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds h0)
    have hτline : fderiv ℝ τ y (Pi.single 0 1) = 0 := by
      have hτ' : HasFDerivAt τ (fderiv ℝ τ y) (y + (0 : ℝ) • (Pi.single 0 1 : Fin 2 → ℝ)) := by
        simpa using hτdd.hasFDerivAt
      have h1 := hτ'.comp_hasDerivAt (0 : ℝ) hlin
      have h2 : HasDerivAt (τ ∘ fun s : ℝ => y + s • (Pi.single 0 1 : Fin 2 → ℝ)) 0 0 := by
        refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [hnear] with s hs
        change τ (y + s • Pi.single 0 1) = 0
        rw [hline s]
        exact (hτ0 _ (by simpa using hs) (by simpa using hr₀)).2 (by simp)
      exact h1.unique h2
    have hσline' : fderiv ℝ σ y (Pi.single 0 1) = 1 := by
      have hσ' : HasFDerivAt σ (fderiv ℝ σ y) (y + (0 : ℝ) • (Pi.single 0 1 : Fin 2 → ℝ)) := by
        simpa using hσd.hasFDerivAt
      have h1 := hσ'.comp_hasDerivAt (0 : ℝ) hlin
      have h2 : HasDerivAt (σ ∘ fun s : ℝ => y + s • (Pi.single 0 1 : Fin 2 → ℝ)) 1 0 := by
        have h3 : HasDerivAt (fun s : ℝ => y 0 + s) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 0)
        refine h3.congr_of_eventuallyEq ?_
        filter_upwards [hnear] with s hs
        change σ (y + s • Pi.single 0 1) = y 0 + s
        rw [hline s]
        exact hσline _ hs
      exact h1.unique h2
    intro h0
    have hv : (Pi.single 1 1 - fderiv ℝ σ y (Pi.single 1 1) • Pi.single 0 1 : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    apply hv
    apply himmστ y hy.1 hy.2
    rw [map_zero, hpi σ τ y hσd hτdd, map_sub, map_smul, map_sub, map_smul, hσline', h0,
      hτline]
    ext i
    fin_cases i <;> simp
  obtain ⟨hθs, hθrefl, hθpos, hθpolar, hθinj, hθd⟩ := whitneyAngle_spec
  have hK1 := LevelField.eventually_flow_eq_of_chartDir X hV₁ (hφ₁.smooth.mono hV₁U) hX₁ h0V₁
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.1 hK1
  have hK2 := LevelField.eventually_flow_eq_of_chartDir X hV₂ (hφ₂.smooth.mono hV₂U) hX₂ h0V₂
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff.1 hK2
  obtain ⟨ρ, hρpos, hρρ₀, hρ14, hρδ, hρ1, hρ2⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ρ ≤ 1 / 4 ∧
      ρ ≤ δ / 2 ∧ 2 * ρ * (‖a₁‖ + 1) ≤ ε₁ ∧ 2 * ρ * (‖a₂‖ + 1) ≤ ε₂ := by
    have hρ₀pos : 0 < ρ₀ := by linarith
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ε₁ / (2 * (‖a₁‖ + 1)) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ε₂ / (2 * (‖a₂‖ + 1)) := ⟨_, rfl⟩
    have hApos : 0 < A := by rw [hA]; positivity
    have hBpos : 0 < B := by rw [hB]; positivity
    have hA' : 2 * A * (‖a₁‖ + 1) = ε₁ := by
      rw [hA]; field_simp
    have hB' : 2 * B * (‖a₂‖ + 1) = ε₂ := by
      rw [hB]; field_simp
    refine ⟨min (min ρ₀ (1 / 4)) (min (δ / 2) (min A B)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min hρ₀pos (by norm_num)) (lt_min (by linarith) (lt_min hApos hBpos))
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · have h : min (min ρ₀ (1 / 4)) (min (δ / 2) (min A B)) ≤ A :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      rw [← hA']
      have h2 : (0 : ℝ) ≤ ‖a₁‖ + 1 := by positivity
      have := mul_le_mul_of_nonneg_right h h2
      linarith
    · have h : min (min ρ₀ (1 / 4)) (min (δ / 2) (min A B)) ≤ B :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [← hB']
      have h2 : (0 : ℝ) ≤ ‖a₂‖ + 1 := by positivity
      have := mul_le_mul_of_nonneg_right h h2
      linarith
  have hdist : ∀ (y : Fin 2 → ℝ) (x0 : ℝ), dist y ![x0, 0] < ρ → |y 0 - x0| < ρ ∧ |y 1| < ρ := by
    intro y x0 h
    rw [dist_pi_lt_iff hρpos] at h
    have h0 := h 0
    have h1 := h 1
    simp only [Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at h0 h1
    exact ⟨h0, h1⟩
  have hcor₁ : ∀ y ∈ Sg, dist y ![-1, 0] < ρ →
      (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁ ∈ V₁ ∧
      X.flow (τ y) (γA (σ y)) =
        φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁) := by
    intro y hy hd
    obtain ⟨hd0, hd1⟩ := hdist y (-1) hd
    have hy0 : y 0 < -1 + ρ₀ := by have := (abs_lt.1 hd0).2; linarith
    obtain ⟨hσy, hτy⟩ := hcornL y hy.1 hy.2 hy0
    obtain ⟨hbd1, hbd2⟩ := hbd y hy.1 hy.2
    have hs1 : |σ y + 1| < 2 * ρ := by
      calc |σ y + 1| = |(σ y - y 0) + (y 0 - -1)| := by ring_nf
        _ ≤ |σ y - y 0| + |y 0 - -1| := abs_add_le _ _
        _ < 2 * ρ := by linarith
    have ht2 : |τ y| < 2 * ρ := by linarith
    obtain ⟨-, hγ⟩ := harcs.endA₁ (σ y) (by linarith)
    have hna : ‖(σ y + 1) • a₁‖ < ε₁ := by
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_right hs1.le (norm_nonneg a₁)
      have h3 : 2 * ρ * 1 ≤ 2 * ρ * (‖a₁‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg a₁]) (by linarith)
      linarith
    have hnt : |τ y| < ε₁ := by
      have h3 : 2 * ρ * 1 ≤ 2 * ρ * (‖a₁‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg a₁]) (by linarith)
      linarith
    have hP := hb₁ (y := ((σ y + 1) • a₁, τ y)) (by
      rw [Prod.dist_eq, dist_zero_right, Real.dist_eq, sub_zero]
      exact max_lt hna hnt)
    have e1 : 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = σ y + 1 := by rw [hσy]; ring
    rw [e1, ← hτy]
    exact ⟨hP.1, by rw [hγ]; exact hP.2⟩
  have hcor₂ : ∀ y ∈ Sg, dist y ![1, 0] < ρ →
      (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂ ∈ V₂ ∧
      X.flow (τ y) (γA (σ y)) =
        φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂) := by
    intro y hy hd
    obtain ⟨hd0, hd1⟩ := hdist y 1 hd
    have hy0 : 1 - ρ₀ < y 0 := by have := (abs_lt.1 hd0).1; linarith
    obtain ⟨hσy, hτy⟩ := hcornR y hy.1 hy.2 hy0
    obtain ⟨hbd1, hbd2⟩ := hbd y hy.1 hy.2
    have hs1 : |σ y - 1| < 2 * ρ := by
      calc |σ y - 1| = |(σ y - y 0) + (y 0 - 1)| := by ring_nf
        _ ≤ |σ y - y 0| + |y 0 - 1| := abs_add_le _ _
        _ < 2 * ρ := by linarith
    have hs1' : |1 - σ y| < 2 * ρ := by rw [abs_sub_comm]; exact hs1
    have ht2 : |τ y| < 2 * ρ := by linarith
    obtain ⟨-, hγ⟩ := harcs.endA₂ (σ y) (by linarith)
    have hna : ‖(1 - σ y) • a₂‖ < ε₂ := by
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_right hs1'.le (norm_nonneg a₂)
      have h3 : 2 * ρ * 1 ≤ 2 * ρ * (‖a₂‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg a₂]) (by linarith)
      linarith
    have hnt : |τ y| < ε₂ := by
      have h3 : 2 * ρ * 1 ≤ 2 * ρ * (‖a₂‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg a₂]) (by linarith)
      linarith
    have hP := hb₂ (y := ((1 - σ y) • a₂, τ y)) (by
      rw [Prod.dist_eq, dist_zero_right, Real.dist_eq, sub_zero]
      exact max_lt hna hnt)
    have e1 : 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = 1 - σ y := by rw [hσy]
    rw [e1, ← hτy]
    exact ⟨hP.1, by rw [hγ]; exact hP.2⟩
  obtain ⟨rm, hrm, hmid⟩ := diameterStrip_middle hf D hp hq hv hc₁ hc₂ harcs.smoothA harcs.memA X
    htr hSgo hψsm (fun y hy => hτ0 y hy.1 hy.2) (fun y hy => hbd y hy.1 hy.2) hτd hder
    (half_pos hρpos)
  obtain ⟨r, hr, hrr₀, hrη, hrm', hrρ⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ r ≤ η / 2 ∧ r ≤ rm ∧
      r ≤ ρ / 2 :=
    ⟨min (min r₀ (η / 2)) (min rm (ρ / 2)),
      lt_min (lt_min hr₀ (by linarith)) (lt_min hrm (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  set N : Set (Fin 2 → ℝ) := {y | |y 0| < 1 + r ∧ |y 1| < r} with hNdef
  have hNo : IsOpen N :=
    (isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_apply 1)) continuous_const)
  have hNSg : N ⊆ Sg := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hNII : N ⊆ Sg ∩ {y | σ y ∈ Ioo (-1 - η) (1 + η) ∧ τ y ∈ Ioo (-η) η} := by
    intro y hy
    obtain ⟨hb1, hb2⟩ := hbd y (hNSg hy).1 (hNSg hy).2
    have h1 := abs_lt.1 hy.1
    have h2 := hy.2
    have h3 := abs_le.1 hb1
    have h4 := abs_le.1 hb2
    refine ⟨hNSg hy, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  have hflow0 : ∀ x : M, X.flow 0 x = x := fun x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hx₁ : X.flow (τ ![-1, 0]) (γA (σ ![-1, 0])) = x₁ := by
    have h1 : σ ![-1, 0] = -1 := hσline (-1) (by rw [abs_neg, abs_one]; linarith)
    have h2 : τ ![-1, 0] = 0 :=
      (hτ0 ![-1, 0] (by simp [hr₀]) (by simpa using hr₀)).2 (by simp)
    rw [h1, h2, hflow0, (harcs.endA₁ (-1) (by simpa using hδ)).2]
    simp [hφ₁.center]
  have hx₂ : X.flow (τ ![1, 0]) (γA (σ ![1, 0])) = x₂ := by
    have h1 : σ ![1, 0] = 1 := hσline 1 (by rw [abs_one]; linarith)
    have h2 : τ ![1, 0] = 0 :=
      (hτ0 ![1, 0] (by simp [hr₀]) (by simpa using hr₀)).2 (by simp)
    rw [h1, h2, hflow0, (harcs.endA₂ 1 (by simpa using hδ)).2]
    simp [hφ₂.center]
  set P : Set (Fin 2 → ℝ) := {y | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} with hPdef
  have hPo : IsOpen P := isOpen_lt continuous_const (by fun_prop)
  have hposP : ∀ z : Fin 2 → ℝ, z 0 ≠ 0 → z ∈ P := by
    intro z hz
    have hz2 : 0 < z 0 ^ 2 := by positivity
    have h1 : |z 1| < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) :=
      (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; linarith)
    change 0 < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) + z 1
    linarith [neg_abs_le (z 1)]
  have hθdiff : ∀ z ∈ P, DifferentiableAt ℝ whitneyAngle z := fun z hz =>
    (hθs.contDiffAt (hPo.mem_nhds hz)).differentiableAt (by simp)
  have hsdiff : ∀ z : Fin 2 → ℝ, z 0 ≠ 0 →
      DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) z := by
    intro z hz
    have hz2 : 0 < z 0 ^ 2 := by positivity
    exact DifferentiableAt.sqrt (by fun_prop) (by positivity)
  have hcollar : D.IsWhitneyCollar c hp hq ε x₁ x₂ N (fun y => X.flow (τ y) (γA (σ y))) := by
    refine isWhitneyCollar_of_local D hp hq hNo (hII.2.mono hNII) hx₁ hx₂ ?_
    intro y hy
    by_cases h1 : dist y ![-1, 0] < ρ
    · refine ⟨N ∩ Metric.ball ![-1, 0] ρ, inter_subset_left, hNo.inter Metric.isOpen_ball,
        ⟨hy, h1⟩, ?_⟩
      have hz : ∀ z ∈ N ∩ Metric.ball ![-1, 0] ρ, z 0 < 0 ∧ z ∈ P ∧ z ∈ Sg ∧
          dist z ![-1, 0] < ρ ∧ z 0 < -1 + ρ₀ := by
        intro z hz
        obtain ⟨hd0, hd1⟩ := hdist z (-1) hz.2
        have := (abs_lt.1 hd0).2
        have hz0 : z 0 < 0 := by linarith
        exact ⟨hz0, hposP z hz0.ne, hNSg hz.1, hz.2, by linarith⟩
      refine isWhitneyCollar_of_cornerFormula D hp hq hkp hkq hφ₁ harcs.dirA.1 harcs.dirA.2.2.1
        harcs.dirB.1 harcs.dirB.2.2.1 (hNo.inter Metric.isOpen_ball) ?_
        (α := fun y => Real.pi - whitneyAngle y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx₁ hx₂
      · intro z hz' h0
        have := (hz z hz').1
        rw [h0] at this
        simp at this
      · exact contDiffOn_const.sub (hθs.mono fun z hz' => (hz z hz').2.1)
      · intro z hz'
        obtain ⟨-, -, hzS, -, hz0⟩ := hz z hz'
        rw [← (hcornL z hzS.1 hzS.2 hz0).2]
        exact hτ0 z hzS.1 hzS.2
      · intro z hz' _
        obtain ⟨hz0, hzP, -, -, -⟩ := hz z hz'
        rw [fderiv_const_sub, neg_apply, (hθd z hzP).2.2, neg_ne_zero]
        have : 0 < z 0 ^ 2 := by have := hz0.ne; positivity
        have h2 : (0 : ℝ) < z 0 ^ 2 + z 1 ^ 2 := by linarith [sq_nonneg (z 1)]
        exact div_ne_zero hz0.ne h2.ne'
      · intro z hz' z' hz'' heq
        have h0 := congrFun heq 0
        have h1 := congrFun heq 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
        apply hθinj (hz z hz').2.1 (hz z' hz'').2.1
        simp only
        rw [show whitneyAngle z = whitneyAngle z' by linarith, h1]
      · intro z hz'
        obtain ⟨hz0, hzP, -, -, -⟩ := hz z hz'
        have hd1 : DifferentiableAt ℝ (fun y => Real.pi - whitneyAngle y) z :=
          (differentiableAt_const _).sub (hθdiff z hzP)
        rw [injective_iff_map_eq_zero]
        intro v hv
        rw [hpi _ _ z hd1 (hsdiff z hz0.ne)] at hv
        have h0 := congrFun hv 0
        have h1 := congrFun hv 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
        rw [fderiv_const_sub, neg_apply, neg_eq_zero] at h0
        apply (injective_iff_map_eq_zero _).1 (hθd z hzP).1 v
        rw [hpi _ _ z (hθdiff z hzP) (hsdiff z hz0.ne)]
        ext i
        fin_cases i <;> simp [h0, h1]
      · intro z hz'
        exact hV₁U (hcor₁ z (hz z hz').2.2.1 (hz z hz').2.2.2.1).1
      · intro z hz'
        exact (hcor₁ z (hz z hz').2.2.1 (hz z hz').2.2.2.1).2
    by_cases h2 : dist y ![1, 0] < ρ
    · refine ⟨N ∩ Metric.ball ![1, 0] ρ, inter_subset_left, hNo.inter Metric.isOpen_ball,
        ⟨hy, h2⟩, ?_⟩
      have hz : ∀ z ∈ N ∩ Metric.ball ![1, 0] ρ, 0 < z 0 ∧ z ∈ P ∧ z ∈ Sg ∧
          dist z ![1, 0] < ρ ∧ 1 - ρ₀ < z 0 := by
        intro z hz
        obtain ⟨hd0, hd1⟩ := hdist z 1 hz.2
        have := (abs_lt.1 hd0).1
        have hz0 : 0 < z 0 := by linarith
        exact ⟨hz0, hposP z hz0.ne', hNSg hz.1, hz.2, by linarith⟩
      refine isWhitneyCollar_of_cornerFormula D hp hq hkp hkq hφ₂ harcs.dirA.2.1
        harcs.dirA.2.2.2 harcs.dirB.2.1 harcs.dirB.2.2.2 (hNo.inter Metric.isOpen_ball) ?_
        (α := whitneyAngle) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx₁ hx₂
      · intro z hz' h0
        have := (hz z hz').1
        rw [h0] at this
        simp at this
      · exact hθs.mono fun z hz' => (hz z hz').2.1
      · intro z hz'
        obtain ⟨-, -, hzS, -, hz0⟩ := hz z hz'
        rw [← (hcornR z hzS.1 hzS.2 hz0).2]
        exact hτ0 z hzS.1 hzS.2
      · intro z hz' _
        obtain ⟨hz0, hzP, -, -, -⟩ := hz z hz'
        rw [(hθd z hzP).2.2]
        have : 0 < z 0 ^ 2 := by positivity
        exact div_ne_zero hz0.ne' (by positivity)
      · exact hθinj.mono fun z hz' => (hz z hz').2.1
      · intro z hz'
        exact (hθd z (hz z hz').2.1).1
      · intro z hz'
        exact hV₂U (hcor₂ z (hz z hz').2.2.1 (hz z hz').2.2.2.1).1
      · intro z hz'
        exact (hcor₂ z (hz z hz').2.2.1 (hz z hz').2.2.2.1).2
    · have hfar : ∀ z ∈ N, ¬ dist z ![-1, 0] < ρ → ¬ dist z ![1, 0] < ρ → |z 0| ≤ 1 - ρ := by
        intro z hz hn1 hn2
        have hz1 : |z 1| < ρ := by linarith [hz.2]
        have hc1 : ρ ≤ |z 0 - -1| := by
          by_contra hc
          apply hn1
          rw [dist_pi_lt_iff hρpos]
          intro b
          fin_cases b
          · simpa [Real.dist_eq] using (not_le.1 hc)
          · simpa [Real.dist_eq] using hz1
        have hc2 : ρ ≤ |z 0 - 1| := by
          by_contra hc
          apply hn2
          rw [dist_pi_lt_iff hρpos]
          intro b
          fin_cases b
          · simpa [Real.dist_eq] using (not_le.1 hc)
          · simpa [Real.dist_eq] using hz1
        have hz0 := abs_lt.1 hz.1
        rw [abs_le]
        rcases le_abs'.1 hc1 with h | h <;> rcases le_abs'.1 hc2 with h' | h' <;>
          constructor <;> linarith
      have hyf := hfar y hy h1 h2
      refine ⟨N ∩ {z | |z 0| < 1 - ρ / 2}, inter_subset_left,
        hNo.inter (isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const),
        ⟨hy, by change |y 0| < 1 - ρ / 2; linarith⟩, ?_⟩
      have hM : ∀ z ∈ N ∩ {z | |z 0| < 1 - ρ / 2}, _ := fun z hz =>
        hmid z (hNSg hz.1) (le_of_lt hz.2) (lt_of_lt_of_le hz.1.2 hrm')
      exact
        { isOpen_N := hNo.inter (isOpen_lt (continuous_abs.comp (continuous_apply 0))
            continuous_const)
          smooth := hψsm.mono fun z hz => hNSg hz.1
          immersion := fun z hz => hII.1 z (hNII hz.1)
          inj := hII.2.mono fun z hz => hNII hz.1
          level := by
            intro z hz
            rw [LevelField.comp_flow hf X]
            obtain ⟨hb1, -⟩ := hbd z (hNSg hz.1).1 (hNSg hz.1).2
            have h3 := abs_le.1 hb1
            have h4 := abs_lt.1 (show |z 0| < 1 - ρ / 2 from hz.2)
            have h5 := hz.1.2
            have hσI : σ z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
            exact hlevS (harcs.memA (σ z) hσI).1
          memA := fun z hz => (hM z hz).1
          memB := fun z hz => ⟨fun h => absurd h (hM z hz).2.1, fun h => absurd h (hM z hz).2.2.1⟩
          transA := fun z hz => (hM z hz).2.2.2
          transB := fun z hz h => absurd h (hM z hz).2.2.1
          corner₁ := hx₁
          corner₂ := hx₂ }
  refine ⟨ρ, r / 2, hρpos, half_pos hr, N, fun y => X.flow (τ y) (γA (σ y)), ?_, hcollar, ?_, ?_,
    ?_⟩
  · rintro y ⟨⟨hy1, hy2⟩, hy3⟩
    have hy0 : y 0 ^ 2 ≤ 1 := by linarith [sq_nonneg (y 1)]
    have hy0' : |y 0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 hy0
    refine ⟨by linarith, ?_⟩
    rw [abs_of_nonneg hy2]
    linarith
  · exact fun y hy hd => (hcor₁ y (hNSg hy) hd).2
  · exact fun y hy hd => (hcor₂ y (hNSg hy) hd).2
  · intro O hO κ hκ hγO
    obtain ⟨ηO, hηO, hflowO⟩ :=
      LevelField.exists_flow_mem X harcs.smoothA.continuous isCompact_Icc hO hγO
    refine ⟨ηO / 2, half_pos hηO, fun y hy hy1 hy0 => ?_⟩
    obtain ⟨hb1, hb2⟩ := hbd y (hNSg hy).1 (hNSg hy).2
    have h0 := abs_le.1 hy0
    exact hflowO (σ y) (y 0) ⟨by linarith, by linarith⟩ (by linarith) (τ y) (by linarith)

theorem exists_circleStrip (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {x₁ x₂ : M} {U₁ U₂ : Set (Fin (n - 1) → ℝ)}
    {φ₁ φ₂ : (Fin (n - 1) → ℝ) → M} (hφ₁ : D.IsCornerChart c hp hq ε ℓ x₁ U₁ φ₁)
    (hφ₂ : D.IsCornerChart c hp hq ε ℓ x₂ U₂ φ₂) {γA γB : ℝ → M} {a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ}
    {δ : ℝ} (harcs : D.IsWhitneyArcs c hp hq ε ℓ φ₁ φ₂ U₁ U₂ γA γB a₁ a₂ b₁ b₂ δ)
    (X' : LevelField I f) {V₁ V₂ : Set (Fin (n - 1) → ℝ)} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (h0V₁ : (0 : Fin (n - 1) → ℝ) ∈ V₁) (h0V₂ : (0 : Fin (n - 1) → ℝ) ∈ V₂) (hV₁U : V₁ ⊆ U₁)
    (hV₂U : V₂ ⊆ U₂)
    (hX₁ : ∀ z ∈ V₁, X'.Y (φ₁ z) = mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ₁ z a₁)
    (hX₂ : ∀ z ∈ V₂, X'.Y (φ₂ z) = mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ₂ z a₂)
    (htr : ∀ t ∈ Icc (0 : ℝ) Real.pi,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (γB t)
        (X'.Y (γB t)) ≠ 0) :
    ∃ ρ r₂ : ℝ, 0 < ρ ∧ 0 < r₂ ∧ r₂ ≤ 1 ∧ ∃ (N : Set (Fin 2 → ℝ)) (ψ : (Fin 2 → ℝ) → M),
      {y | y ∈ whitneyHalf ∧ (1 - r₂) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2} ⊆ N ∧
      D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ ∧
      (∀ y ∈ N, dist y ![-1, 0] < ρ →
        ψ y = φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁)) ∧
      (∀ y ∈ N, dist y ![1, 0] < ρ →
        ψ y = φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂)) ∧
      ∀ O : Set M, IsOpen O → ∀ κ : ℝ, 0 < κ → (∀ t ∈ Icc κ (Real.pi - κ), γB t ∈ O) →
        ∃ r' > 0, ∀ y ∈ N, |1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)| < r' → 2 * κ ≤ whitneyAngle y →
          whitneyAngle y ≤ Real.pi - 2 * κ → ψ y ∈ O := by
  have _ := h6
  have _ := hℓ
  have _ := hℓn
  classical
  obtain ⟨hθsm, hθrefl, hθpos, hθpolar, hθinj, hθd⟩ := whitneyAngle_spec
  have hδ := harcs.hδ
  have hΩo : IsOpen {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} :=
    isOpen_lt continuous_const (by fun_prop)
  have hΩne : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    intro y hy h
    have h1 : y 1 = 0 := by
      have h2 : y 1 ^ 2 = 0 :=
        le_antisymm (by linarith only [h, sq_nonneg (y 0)]) (sq_nonneg _)
      exact (pow_eq_zero_iff two_ne_zero).1 h2
    rw [h, Real.sqrt_zero, h1] at hy
    simp at hy
  have hθcont : ContinuousOn whitneyAngle
      {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := hθsm.continuousOn
  have hθdiff : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      DifferentiableAt ℝ whitneyAngle y := fun y hy =>
    (hθsm.contDiffAt (hΩo.mem_nhds hy)).differentiableAt (by simp)
  have hRdiff : ∀ y : Fin 2 → ℝ, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 →
      DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) y := fun y hy =>
    (by fun_prop : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) y).sqrt
      (hΩne y hy)
  have hRsm : ContDiffOn ℝ ∞ (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
      {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := fun y hy =>
    ((by fun_prop : ContDiffAt ℝ ∞ (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) y).sqrt
      (hΩne y hy)).contDiffWithinAt
  have hvec : ∀ (g h : (Fin 2 → ℝ) → ℝ) (y : Fin 2 → ℝ), DifferentiableAt ℝ g y →
      DifferentiableAt ℝ h y → ∀ v : Fin 2 → ℝ,
      fderiv ℝ (fun x => ![g x, h x]) y v = ![fderiv ℝ g y v, fderiv ℝ h y v] := by
    intro g h y hg hh v
    have hd : DifferentiableAt ℝ (fun x => ![g x, h x]) y := by
      rw [differentiableAt_pi]
      intro i
      fin_cases i
      · simpa using hg
      · simpa using hh
    have key : ∀ i, fderiv ℝ (fun x => ![g x, h x]) y v i =
        fderiv ℝ (fun x => ![g x, h x] i) y v := by
      intro i
      rw [((hasFDerivAt_pi'.1 hd.hasFDerivAt) i).fderiv]
      rfl
    ext i
    rw [key i]
    fin_cases i <;> simp
  have hcoordN_smul : ∀ (s : ℝ) (v : Fin (n - 1) → ℝ) (j : ℕ),
      coordN (s • v) j = s * coordN v j := by
    intro s v j
    unfold coordN
    split_ifs <;> simp
  have hpstrip : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hqstrip : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hv' := hv
  obtain ⟨hε, -, -, hrmp, -, -, hunit⟩ := hv'
  have hU' : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy x hx => hunit y ⟨hy.1, by linarith only [hy.2, hc₂]⟩ x hx
  have hεR : 2 * ε ≤ (D.chart p hp).R ^ 2 := by
    have h2 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
    linarith only [hrmp, h2, hε]
  have hSRlev : D.rightSphere p hp ε c ⊆ f ⁻¹' {c} := by
    refine D.rightSphere_subset_level hf p hp hεR
      ⟨by linarith only [hpstrip.1, hc₁, hε], by linarith only [hqstrip.2, hc₂, hε]⟩ ?_
    intro y hy
    rw [uIcc_of_le (by linarith only [hc₁])] at hy
    exact hunit y ⟨hy.1, by linarith only [hy.2, hc₂]⟩
  have hSR : ∀ s ∈ Ioo (-δ) (Real.pi + δ), γB s ∈ D.rightSphere p hp ε c := by
    intro s hs
    by_cases h0 : s < 0
    · obtain ⟨hmem, heq⟩ := harcs.endB₂ s (by rw [abs_lt]; constructor <;> linarith only [hs.1, h0, hδ])
      rw [heq, hφ₂.memR _ hmem]
      intro j hj
      rw [hcoordN_smul, harcs.dirB.2.2.2 j hj, mul_zero]
    by_cases hπ : Real.pi < s
    · obtain ⟨hmem, heq⟩ := harcs.endB₁ s (by rw [abs_lt]; constructor <;> linarith only [hs.2, hπ, hδ])
      rw [heq, hφ₁.memR _ hmem]
      intro j hj
      rw [hcoordN_smul, harcs.dirB.2.2.1 j hj, mul_zero]
    exact (harcs.memB s ⟨not_lt.1 h0, not_lt.1 hπ⟩).1
  have hlevB : ∀ s ∈ Ioo (-δ) (Real.pi + δ), f (γB s) = c := fun s hs => hSRlev (hSR s hs)
  obtain ⟨O, hOo, hSRO, hOsm, -⟩ := rightCoord_submersion hf D hp hε (by linarith only [hrmp, hε]) hc₁.le
    (by linarith only [hqstrip.2, hc₂, hε]) hU'
  have hind : ∀ t ∈ Icc (0 : ℝ) Real.pi, LinearIndependent ℝ
      ![(mfderiv 𝓘(ℝ, ℝ) I γB t 1 : TangentSpace I (γB t)), X'.Y (γB t)] := by
    intro t ht
    have htI : t ∈ Ioo (-δ) (Real.pi + δ) := ⟨by linarith only [ht.1, hδ], by linarith only [ht.2, hδ]⟩
    have hev : (D.rightCoord p hp ε ∘ γB) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
      exact ((mem_rightSphere_iff_coord hf D hp hε (by linarith only [hrmp, hε]) hc₁.le (by linarith only [hqstrip.2, hc₂, hε])
        hU' (hlevB s hs)).1 (hSR s hs)).1
    have hd0 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε ∘ γB) t = 0 := by
      rw [mfderiv_eq_fderiv, hev.fderiv_eq]
      exact fderiv_const_apply _
    have hmdR : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (γB t) :=
      (hOsm.contMDiffAt (hOo.mem_nhds (hSRO (hSR t htI)))).mdifferentiableAt (by simp)
    have hmdγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γB t :=
      (harcs.smoothB t).mdifferentiableAt (by simp)
    rw [mfderiv_comp t hmdR hmdγ] at hd0
    have hG0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε)
        (γB t) (mfderiv 𝓘(ℝ, ℝ) I γB t 1) = 0 := by
      have := congrArg (fun L => L 1) hd0
      simpa using this
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have h1 := congrArg (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
      (D.rightCoord p hp ε) (γB t)) hsu
    rw [map_add, map_smul, map_smul, hG0, smul_zero, zero_add, map_zero] at h1
    have hu : u = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h (htr t ht)
    refine ⟨?_, hu⟩
    rw [hu, zero_smul, add_zero] at hsu
    rcases smul_eq_zero.1 hsu with h | h
    · exact h
    · exact absurd h (harcs.immB t ht)
  have hτsm : ContDiffOn ℝ ∞ (fun y : Fin 2 → ℝ => 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
      {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := contDiffOn_const.sub hRsm
  have hστ : InjOn (fun y : Fin 2 → ℝ => ![whitneyAngle y, 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)])
      {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := by
    intro y hy y' hy' hyy
    have h0 : whitneyAngle y = whitneyAngle y' := by simpa using congrFun hyy 0
    have h1 : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) := by
      have := congrFun hyy 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      linarith only [this]
    apply hθinj hy hy'
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hστd : ∀ y ∈ {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1},
      Function.Injective (fderiv ℝ (fun y' : Fin 2 → ℝ =>
        ![whitneyAngle y', 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)]) y) := by
    intro y hy
    have hd1 : DifferentiableAt ℝ (fun y' : Fin 2 → ℝ => 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) y :=
      (hRdiff y hy).const_sub 1
    rw [injective_iff_map_eq_zero]
    intro v hv0
    rw [hvec _ _ y (hθdiff y hy) hd1 v] at hv0
    have e0 : fderiv ℝ whitneyAngle y v = 0 := by simpa using congrFun hv0 0
    have e1 : fderiv ℝ (fun y' : Fin 2 → ℝ => 1 - Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) y v = 0 := by
      simpa using congrFun hv0 1
    rw [fderiv_const_sub] at e1
    have e1' : fderiv ℝ (fun y' : Fin 2 → ℝ => Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) y v = 0 := by
      simpa using e1
    apply (hθd y hy).1
    rw [hvec _ _ y (hθdiff y hy) (hRdiff y hy) v, map_zero, e0, e1']
    ext i
    fin_cases i <;> simp
  obtain ⟨hψsm, hψder, η, hη, hψII⟩ := exists_reparamFlowStrip X' harcs.smoothB Real.pi_pos.le
    harcs.injB hind hΩo hθsm hτsm hστ hστd
  have hΩ1 : (![-1, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := by
    simp
  have hΩ2 : (![1, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} := by
    simp
  have hval1 : whitneyAngle ![-1, 0] = Real.pi := by
    simp [whitneyAngle, Real.arctan_neg, Real.arctan_one]
    ring
  have hval2 : whitneyAngle ![1, 0] = 0 := by
    simp [whitneyAngle, Real.arctan_one]
    ring
  have hRcont : Continuous (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) := by fun_prop
  have hK1 := LevelField.eventually_flow_eq_of_chartDir X' hV₁ (hφ₁.smooth.mono hV₁U) hX₁ h0V₁
  have hK2 := LevelField.eventually_flow_eq_of_chartDir X' hV₂ (hφ₂.smooth.mono hV₂U) hX₂ h0V₂
  have hg1 : Tendsto (fun y : Fin 2 → ℝ => ((Real.pi - whitneyAngle y) • b₁,
      1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) (𝓝 ![-1, 0]) (𝓝 ((0 : Fin (n - 1) → ℝ), (0 : ℝ))) := by
    have hc : ContinuousAt (fun y : Fin 2 → ℝ => ((Real.pi - whitneyAngle y) • b₁,
        1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) ![-1, 0] :=
      ((continuousAt_const.sub (hθcont.continuousAt (hΩo.mem_nhds hΩ1))).smul
        continuousAt_const).prodMk (continuousAt_const.sub hRcont.continuousAt)
    convert hc.tendsto using 2
    simp [hval1]
  have hg2 : Tendsto (fun y : Fin 2 → ℝ => (whitneyAngle y • b₂,
      1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) (𝓝 ![1, 0]) (𝓝 ((0 : Fin (n - 1) → ℝ), (0 : ℝ))) := by
    have hc : ContinuousAt (fun y : Fin 2 → ℝ => (whitneyAngle y • b₂,
        1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) ![1, 0] :=
      ((hθcont.continuousAt (hΩo.mem_nhds hΩ2)).smul
        continuousAt_const).prodMk (continuousAt_const.sub hRcont.continuousAt)
    convert hc.tendsto using 2
    simp [hval2]
  have hE1 : ∀ᶠ y in 𝓝 (![-1, 0] : Fin 2 → ℝ),
      (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁ ∈ V₁ ∧
      X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y)) =
        φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁) := by
    have hθπ : ∀ᶠ y in 𝓝 (![-1, 0] : Fin 2 → ℝ), whitneyAngle y ∈ Metric.ball Real.pi δ := by
      have := (hθcont.continuousAt (hΩo.mem_nhds hΩ1)).eventually_mem
        (Metric.ball_mem_nhds (whitneyAngle ![-1, 0]) hδ)
      rwa [hval1] at this
    filter_upwards [hg1.eventually hK1, hθπ] with y h1 h2
    rw [Metric.mem_ball, Real.dist_eq] at h2
    obtain ⟨-, heq⟩ := harcs.endB₁ (whitneyAngle y) h2
    refine ⟨by rw [add_comm]; exact h1.1, ?_⟩
    rw [heq, h1.2, add_comm]
  have hE2 : ∀ᶠ y in 𝓝 (![1, 0] : Fin 2 → ℝ),
      (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂ ∈ V₂ ∧
      X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y)) =
        φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂) := by
    have hθ0 : ∀ᶠ y in 𝓝 (![1, 0] : Fin 2 → ℝ), whitneyAngle y ∈ Metric.ball 0 δ := by
      have := (hθcont.continuousAt (hΩo.mem_nhds hΩ2)).eventually_mem
        (Metric.ball_mem_nhds (whitneyAngle ![1, 0]) hδ)
      rwa [hval2] at this
    filter_upwards [hg2.eventually hK2, hθ0] with y h1 h2
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
    obtain ⟨-, heq⟩ := harcs.endB₂ (whitneyAngle y) h2
    refine ⟨by rw [add_comm]; exact h1.1, ?_⟩
    rw [heq, h1.2, add_comm]
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.eventually_nhds_iff.1 hE1
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.eventually_nhds_iff.1 hE2
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (min ρ₁ ρ₂) (1 / 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min (lt_min hρ₁ hρ₂) (by norm_num)
  have hρ1 : ρ ≤ ρ₁ := by rw [hρdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := by rw [hρdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρh : ρ ≤ 1 / 2 := by rw [hρdef]; exact min_le_right _ _
  have hρ4 : 0 < ρ / 4 := by positivity
  obtain ⟨rm, hrm, hmid⟩ := circleStrip_middle hf D hp hq hv hc₁ hc₂ harcs.smoothB harcs.memB X'
    htr hψsm (fun y hy hR v => hψder y hy (by
      show (1 : ℝ) - Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = 0
      rw [hR, sub_self]) v) hρ4
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min (min η δ) (min rm (ρ / 4)) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; exact lt_min (lt_min hη hδ) (lt_min hrm hρ4)
  have hrη : r ≤ η := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrm' : r ≤ rm := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrκ : r ≤ ρ / 4 := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hNdef⟩ : ∃ N : Set (Fin 2 → ℝ), N =
      ({y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} ∩
        (fun y : Fin 2 → ℝ => 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ⁻¹' Ioo (-r) r) ∩
        whitneyAngle ⁻¹' Ioo (-r) (Real.pi + r) := ⟨_, rfl⟩
  have hNo : IsOpen N := by
    rw [hNdef]
    exact (hθcont.mono inter_subset_left).isOpen_inter_preimage
      ((continuous_const.sub hRcont).continuousOn.isOpen_inter_preimage hΩo isOpen_Ioo) isOpen_Ioo
  have hmemN : ∀ y : Fin 2 → ℝ, y ∈ N ↔ 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 ∧
      |1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)| < r ∧ -r < whitneyAngle y ∧
      whitneyAngle y < Real.pi + r := by
    intro y
    rw [hNdef, abs_lt]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ioo, and_assoc]
  have hNΩ : ∀ y ∈ N, 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 := fun y hy => ((hmemN y).1 hy).1
  have hNII : N ⊆ {y : Fin 2 → ℝ | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1} ∩
      {y | whitneyAngle y ∈ Ioo (0 - η) (Real.pi + η) ∧
        (fun y : Fin 2 → ℝ => 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) y ∈ Ioo (-η) η} := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := (hmemN y).1 hy
    rw [abs_lt] at h2
    refine ⟨h1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith only [h3, hrη]
    · linarith only [h4, hrη]
    · change -η < 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
      linarith only [h2.1, hrη]
    · change 1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2) < η
      linarith only [h2.2, hrη]
  have hlevel : ∀ y ∈ N,
      f (X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (γB (whitneyAngle y))) = c := by
    intro y hy
    obtain ⟨-, -, h3, h4⟩ := (hmemN y).1 hy
    rw [LevelField.comp_flow hf X']
    exact hlevB _ ⟨by linarith only [h3, hrδ], by linarith only [h4, hrδ]⟩
  have hx₁ : (fun y : Fin 2 → ℝ => X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
      (γB (whitneyAngle y))) ![-1, 0] = x₁ := by
    change X'.flow _ _ = x₁
    rw [(hρ₁' (by simpa using hρ₁)).2]
    simp [hval1, hφ₁.center]
  have hx₂ : (fun y : Fin 2 → ℝ => X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
      (γB (whitneyAngle y))) ![1, 0] = x₂ := by
    change X'.flow _ _ = x₂
    rw [(hρ₂' (by simpa using hρ₂)).2]
    simp [hval2, hφ₂.center]
  have hbd : ∀ R u : ℝ, |R - 1| < ρ / 4 → |u| ≤ ρ / 4 →
      |R * Real.cos u - 1| < ρ ∧ |R * Real.sin u| < ρ := by
    intro R u hR hu
    rw [abs_lt] at hR
    have hu2 : u ^ 2 ≤ (ρ / 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg u) hu 2
    have hc1 := Real.one_sub_sq_div_two_le_cos (x := u)
    have hc2 := Real.cos_le_one u
    have hs := Real.abs_sin_le_abs (x := u)
    have hR0 : 0 < R := by linarith only [hR.1, hρh]
    have hR2 : R ≤ 2 := by linarith only [hR.2, hρh]
    have hRu : R * u ^ 2 ≤ 2 * (ρ / 4) ^ 2 :=
      mul_le_mul hR2 hu2 (sq_nonneg _) (by norm_num)
    have hρsq : (ρ / 4) ^ 2 ≤ ρ / 32 := by
      have h := mul_le_mul_of_nonneg_left hρh hρ.le
      have e : (ρ / 4) ^ 2 = ρ * ρ / 16 := by ring
      rw [e]
      linarith only [h]
    have hl := mul_le_mul_of_nonneg_left hc1 hR0.le
    have hu' := mul_le_mul_of_nonneg_left hc2 hR0.le
    have e3 : R * (1 - u ^ 2 / 2) = R - R * u ^ 2 / 2 := by ring
    rw [mul_one] at hu'
    constructor
    · rw [abs_lt]
      constructor
      · linarith only [hl, e3, hRu, hρsq, hR.1, hρ]
      · linarith only [hu', hR.2, hρ]
    · rw [abs_mul, abs_of_pos hR0]
      have h1 : R * |Real.sin u| ≤ R * (ρ / 4) := mul_le_mul_of_nonneg_left (hs.trans hu) hR0.le
      have h2 : R * (ρ / 4) ≤ 2 * (ρ / 4) := mul_le_mul_of_nonneg_right hR2 hρ4.le
      linarith only [h1, h2, hρ]
  refine ⟨ρ, r / 2, hρ, by positivity, by linarith only [hrκ, hρh], N, fun y => X'.flow (1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (γB (whitneyAngle y)), ?_, ?_, fun y _ hy => (hρ₁' (lt_of_lt_of_le hy hρ1)).2,
    fun y _ hy => (hρ₂' (lt_of_lt_of_le hy hρ2)).2, ?_⟩
  · rintro y ⟨⟨hy1, hy2⟩, hy3⟩
    have hRnn := Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)
    have hRsq := Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
    have hRle : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ 1 :=
      (Real.sqrt_le_sqrt hy1).trans_eq Real.sqrt_one
    have hr2 : 0 ≤ 1 - r / 2 := by linarith only [hrκ, hρh]
    have hRge : 1 - r / 2 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) :=
      (Real.sqrt_sq hr2).symm.le.trans (Real.sqrt_le_sqrt hy3)
    have hRpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by linarith only [hRge, hrκ, hρh]
    have hΩy : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + y 1 := by linarith only [hRpos, hy2]
    obtain ⟨hθI, -, hy1p⟩ := hθpolar y hΩy
    have hθ0 : 0 ≤ whitneyAngle y := by
      by_contra h'
      have h := not_le.1 h'
      have hs := Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith only [hθI.1, Real.pi_pos])
      have := mul_neg_of_pos_of_neg hRpos hs
      linarith only [this, hy1p, hy2]
    have hθπ : whitneyAngle y ≤ Real.pi := by
      by_contra h'
      have h := not_le.1 h'
      have hs : 0 < Real.sin (whitneyAngle y - Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith only [h]) (by linarith only [hθI.2, Real.pi_pos])
      rw [Real.sin_sub_pi] at hs
      have := mul_neg_of_pos_of_neg hRpos (neg_pos.1 hs)
      linarith only [this, hy1p, hy2]
    rw [hmemN]
    refine ⟨hΩy, ?_, by linarith only [hθ0, hr], by linarith only [hθπ, hr]⟩
    rw [abs_lt]
    constructor <;> linarith only [hRle, hRge, hr]
  · refine isWhitneyCollar_of_local D hp hq hNo (hψII.2.mono hNII) hx₁ hx₂ ?_
    intro y hy
    obtain ⟨hΩy, hRy, hθy1, hθy2⟩ := (hmemN y).1 hy
    have hNne : ∀ z ∈ N, z ≠ 0 := by
      intro z hz h0
      have := hNΩ z hz
      rw [h0] at this
      simp at this
    by_cases hc1 : dist y ![-1, 0] < ρ
    · refine ⟨N ∩ Metric.ball ![-1, 0] ρ, inter_subset_left, hNo.inter Metric.isOpen_ball,
        ⟨hy, hc1⟩, ?_⟩
      have hneg : ∀ z ∈ N ∩ Metric.ball ![-1, 0] ρ, z 0 < -1 / 2 := by
        intro z hz
        have h := (dist_le_pi_dist z ![-1, 0] 0).trans_lt hz.2
        rw [Real.dist_eq] at h
        simp only [Matrix.cons_val_zero] at h
        rw [abs_lt] at h
        linarith only [h.2, hρh]
      refine isWhitneyCollar_of_cornerFormula D hp hq hkp hkq hφ₁ harcs.dirA.1 harcs.dirA.2.2.1
        harcs.dirB.1 harcs.dirB.2.2.1 (hNo.inter Metric.isOpen_ball)
        (fun z hz => hNne z hz.1) (α := fun z => Real.pi - whitneyAngle z)
        (contDiffOn_const.sub (hθsm.mono fun z hz => hNΩ z hz.1)) ?_ ?_ ?_ ?_
        (fun z hz => hV₁U (hρ₁' (lt_of_lt_of_le hz.2 hρ1)).1)
        (fun z hz => (hρ₁' (lt_of_lt_of_le hz.2 hρ1)).2) hx₁ hx₂
      · intro z hz
        have hz0 := hneg z hz
        have hzΩ := hNΩ z hz.1
        constructor
        · intro h
          have hθ : whitneyAngle z = Real.pi := by linarith only [h]
          rw [(hθpolar z hzΩ).2.2, hθ, Real.sin_pi, mul_zero]
        · intro h
          have h1 := hθrefl z
          have h2 := hθpos ![-z 0, z 1] (by simp; linarith only [hz0])
          rw [h] at h1 h2
          simp at h2
          linarith only [h1, h2]
      · intro z hz h
        have hz0 := hneg z hz
        have hzΩ := hNΩ z hz.1
        rw [fderiv_const_sub]
        change -(fderiv ℝ whitneyAngle z (Pi.single 1 1)) ≠ 0
        rw [(hθd z hzΩ).2.2, h, neg_ne_zero]
        have hz0' : z 0 ≠ 0 := (show z 0 < 0 by linarith only [hz0]).ne
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
        exact div_ne_zero hz0' (pow_ne_zero 2 hz0')
      · intro z hz z' hz' hzz
        have h0 : Real.pi - whitneyAngle z = Real.pi - whitneyAngle z' := by
          simpa using congrFun hzz 0
        have h1 : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) = Real.sqrt (z' 0 ^ 2 + z' 1 ^ 2) := by
          have := congrFun hzz 1
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
          linarith only [this]
        apply hθinj (hNΩ z hz.1) (hNΩ z' hz'.1)
        ext i
        fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          linarith only [h0]
        · simpa using h1
      · intro z hz
        have hzΩ := hNΩ z hz.1
        have hd0 : DifferentiableAt ℝ (fun y' : Fin 2 → ℝ => Real.pi - whitneyAngle y') z :=
          (hθdiff z hzΩ).const_sub _
        rw [injective_iff_map_eq_zero]
        intro v hv0
        rw [hvec _ _ z hd0 (hRdiff z hzΩ) v] at hv0
        have e0 : fderiv ℝ (fun y' : Fin 2 → ℝ => Real.pi - whitneyAngle y') z v = 0 := by
          simpa using congrFun hv0 0
        have e1 : fderiv ℝ (fun y' : Fin 2 → ℝ => Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2)) z v = 0 := by
          simpa using congrFun hv0 1
        rw [fderiv_const_sub] at e0
        have e0' : fderiv ℝ whitneyAngle z v = 0 := by simpa using e0
        apply (hθd z hzΩ).1
        rw [hvec _ _ z (hθdiff z hzΩ) (hRdiff z hzΩ) v, map_zero, e0', e1]
        ext i
        fin_cases i <;> simp
    by_cases hc2 : dist y ![1, 0] < ρ
    · refine ⟨N ∩ Metric.ball ![1, 0] ρ, inter_subset_left, hNo.inter Metric.isOpen_ball,
        ⟨hy, hc2⟩, ?_⟩
      have hpos : ∀ z ∈ N ∩ Metric.ball ![1, 0] ρ, 1 / 2 < z 0 := by
        intro z hz
        have h := (dist_le_pi_dist z ![1, 0] 0).trans_lt hz.2
        rw [Real.dist_eq] at h
        simp only [Matrix.cons_val_zero] at h
        rw [abs_lt] at h
        linarith only [h.1, hρh]
      refine isWhitneyCollar_of_cornerFormula D hp hq hkp hkq hφ₂ harcs.dirA.2.1
        harcs.dirA.2.2.2 harcs.dirB.2.1 harcs.dirB.2.2.2 (hNo.inter Metric.isOpen_ball)
        (fun z hz => hNne z hz.1) (α := whitneyAngle)
        (hθsm.mono fun z hz => hNΩ z hz.1) ?_ ?_
        (hθinj.mono fun z hz => hNΩ z hz.1) (fun z hz => (hθd z (hNΩ z hz.1)).1)
        (fun z hz => hV₂U (hρ₂' (lt_of_lt_of_le hz.2 hρ2)).1)
        (fun z hz => (hρ₂' (lt_of_lt_of_le hz.2 hρ2)).2) hx₁ hx₂
      · intro z hz
        have hz0 := hpos z hz
        have hzΩ := hNΩ z hz.1
        constructor
        · intro h
          rw [(hθpolar z hzΩ).2.2, h, Real.sin_zero, mul_zero]
        · intro h
          rw [hθpos z (by linarith only [hz0]), h, zero_div, Real.arctan_zero]
      · intro z hz h
        have hz0 := hpos z hz
        have hzΩ := hNΩ z hz.1
        rw [(hθd z hzΩ).2.2, h]
        have hz0' : z 0 ≠ 0 := (show 0 < z 0 by linarith only [hz0]).ne'
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
        exact div_ne_zero hz0' (pow_ne_zero 2 hz0')
    · have hRy' : |Real.sqrt (y 0 ^ 2 + y 1 ^ 2) - 1| < ρ / 4 := by
        rw [abs_sub_comm]
        linarith only [hRy, hrκ]
      obtain ⟨-, hy0, hy1⟩ := hθpolar y hΩy
      have hlow : ρ / 4 < whitneyAngle y := by
        by_contra h'
        have h := not_lt.1 h'
        have hu : |whitneyAngle y| ≤ ρ / 4 := abs_le.2 ⟨by linarith only [hθy1, hrκ], h⟩
        obtain ⟨hb1, hb2⟩ := hbd _ _ hRy' hu
        rw [← hy0] at hb1
        rw [← hy1] at hb2
        apply hc2
        rw [dist_pi_lt_iff hρ, Fin.forall_fin_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sub_zero]
        exact ⟨hb1, hb2⟩
      have hhigh : whitneyAngle y < Real.pi - ρ / 4 := by
        by_contra h'
        have h := not_lt.1 h'
        have hu : |Real.pi - whitneyAngle y| ≤ ρ / 4 := abs_le.2 ⟨by linarith only [hθy2, hrκ], by linarith only [h]⟩
        obtain ⟨hb1, hb2⟩ := hbd _ _ hRy' hu
        rw [Real.cos_pi_sub] at hb1
        rw [Real.sin_pi_sub, ← hy1] at hb2
        apply hc1
        rw [dist_pi_lt_iff hρ, Fin.forall_fin_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sub_zero]
        refine ⟨?_, hb2⟩
        have e : y 0 - -1 = -(Real.sqrt (y 0 ^ 2 + y 1 ^ 2) * -Real.cos (whitneyAngle y) - 1) := by
          linear_combination hy0
        rw [e, abs_neg]
        exact hb1
      have hP3o : IsOpen (N ∩ whitneyAngle ⁻¹' Ioo (ρ / 4) (Real.pi - ρ / 4)) :=
        (hθcont.mono hNΩ).isOpen_inter_preimage hNo isOpen_Ioo
      have hm := fun z (hz : z ∈ N ∩ whitneyAngle ⁻¹' Ioo (ρ / 4) (Real.pi - ρ / 4)) =>
        hmid z (hNΩ z hz.1) (lt_of_lt_of_le ((hmemN z).1 hz.1).2.1 hrm') hz.2.1.le hz.2.2.le
      refine ⟨N ∩ whitneyAngle ⁻¹' Ioo (ρ / 4) (Real.pi - ρ / 4), inter_subset_left, hP3o,
        ⟨hy, hlow, hhigh⟩, ?_⟩
      exact ⟨hP3o, hψsm.mono fun z hz => hNΩ z hz.1, fun z hz => hψII.1 z (hNII hz.1),
        hψII.2.mono fun z hz => hNII hz.1, fun z hz => hlevel z hz.1,
        fun z hz => iff_of_false (hm z hz).2.1 (hm z hz).2.2.1, fun z hz => (hm z hz).1,
        fun z hz h => absurd h (hm z hz).2.2.1, fun z hz => (hm z hz).2.2.2, hx₁, hx₂⟩
  · intro O' hO' κ' hκ' hγO
    obtain ⟨η', hη', hη'O⟩ := LevelField.exists_flow_mem X' harcs.smoothB.continuous isCompact_Icc
      hO' hγO
    refine ⟨η', hη', fun y _ h1 h2 h3 => ?_⟩
    have hJ : whitneyAngle y ∈ Icc κ' (Real.pi - κ') := ⟨by linarith only [h2, hκ'], by linarith only [h3, hκ']⟩
    exact hη'O _ _ hJ (by rw [sub_self, abs_zero]; exact hη') _ h1

theorem glue_whitneyCollars (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) {ε c : ℝ} {x₁ x₂ : M} {NA NB A B K : Set (Fin 2 → ℝ)}
    {ψA ψB : (Fin 2 → ℝ) → M} (hA : D.IsWhitneyCollar c hp hq ε x₁ x₂ NA ψA)
    (hB : D.IsWhitneyCollar c hp hq ε x₁ x₂ NB ψB) (hAo : IsOpen A) (hBo : IsOpen B)
    (hANA : A ⊆ NA) (hBNB : B ⊆ NB) (hAB : EqOn ψA ψB (A ∩ B)) (hK : IsCompact K)
    (hKAB : K ⊆ A ∪ B) (hsep : ∀ y ∈ K ∩ A, ∀ y' ∈ K ∩ B, ψA y = ψB y' → y = y') :
    ∃ (N : Set (Fin 2 → ℝ)) (ψ₀ : (Fin 2 → ℝ) → M), K ⊆ N ∧
      D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ₀ := by
  classical
  obtain ⟨ψ₀, hψ₀A, hψ₀B, hψ₀n⟩ : ∃ ψ₀ : (Fin 2 → ℝ) → M, (∀ y ∈ A, ψ₀ y = ψA y) ∧
      (∀ y ∈ B, ψ₀ y = ψB y) ∧ (∀ y, y ∉ A → ψ₀ y = ψB y) := by
    refine ⟨fun y => if y ∈ A then ψA y else ψB y, fun y hy => by simp [hy], ?_,
      fun y hy => by simp [hy]⟩
    intro y hy
    by_cases hyA : y ∈ A
    · simp only [hyA, ite_true]
      exact hAB ⟨hyA, hy⟩
    · simp [hyA]
  have hloc : ∀ y ∈ A ∪ B, ∃ (N' : Set (Fin 2 → ℝ)) (ψ' : (Fin 2 → ℝ) → M),
      D.IsWhitneyCollar c hp hq ε x₁ x₂ N' ψ' ∧ y ∈ N' ∧ ψ₀ =ᶠ[𝓝 y] ψ' ∧ ψ₀ y = ψ' y := by
    rintro y (hy | hy)
    · exact ⟨NA, ψA, hA, hANA hy, Filter.eventually_of_mem (hAo.mem_nhds hy) hψ₀A, hψ₀A y hy⟩
    · exact ⟨NB, ψB, hB, hBNB hy, Filter.eventually_of_mem (hBo.mem_nhds hy) hψ₀B, hψ₀B y hy⟩
  have hW : IsOpen (A ∪ B) := hAo.union hBo
  have hsmooth : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ₀ (A ∪ B) := by
    intro y hy
    obtain ⟨N', ψ', hC, hyN, hev, -⟩ := hloc y hy
    exact ((hC.smooth.contMDiffAt (hC.isOpen_N.mem_nhds hyN)).congr_of_eventuallyEq
      hev).contMDiffWithinAt
  have hmf : ∀ y ∈ A ∪ B, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ₀ y) := by
    intro y hy
    obtain ⟨N', ψ', hC, hyN, hev, -⟩ := hloc y hy
    rw [hev.mfderiv_eq]
    exact hC.immersion y hyN
  have hinjK : InjOn ψ₀ K := by
    intro y hy y' hy' h
    by_cases hyA : y ∈ A <;> by_cases hy'A : y' ∈ A
    · rw [hψ₀A y hyA, hψ₀A y' hy'A] at h
      exact hA.inj (hANA hyA) (hANA hy'A) h
    · have hy'B : y' ∈ B := (hKAB hy').resolve_left hy'A
      rw [hψ₀A y hyA, hψ₀B y' hy'B] at h
      exact hsep y ⟨hy, hyA⟩ y' ⟨hy', hy'B⟩ h
    · have hyB : y ∈ B := (hKAB hy).resolve_left hyA
      rw [hψ₀B y hyB, hψ₀A y' hy'A] at h
      exact (hsep y' ⟨hy', hy'A⟩ y ⟨hy, hyB⟩ h.symm).symm
    · have hyB : y ∈ B := (hKAB hy).resolve_left hyA
      have hy'B : y' ∈ B := (hKAB hy').resolve_left hy'A
      rw [hψ₀B y hyB, hψ₀B y' hy'B] at h
      exact hB.inj (hBNB hyB) (hBNB hy'B) h
  obtain ⟨U, hUo, hKU, hUW, hUinj, hUimm⟩ := exists_injOn_nhds_of_immersion (I := I) hW
    (hsmooth.of_le (by norm_num)) hK hKAB (fun y hy => hmf y (hKAB hy)) hinjK
  have hcorner₁ : ψ₀ ![-1, 0] = x₁ := by
    by_cases h : (![-1, 0] : Fin 2 → ℝ) ∈ A
    · rw [hψ₀A _ h]; exact hA.corner₁
    · rw [hψ₀n _ h]; exact hB.corner₁
  have hcorner₂ : ψ₀ ![1, 0] = x₂ := by
    by_cases h : (![1, 0] : Fin 2 → ℝ) ∈ A
    · rw [hψ₀A _ h]; exact hA.corner₂
    · rw [hψ₀n _ h]; exact hB.corner₂
  refine ⟨U, ψ₀, hKU, ?_⟩
  exact
    { isOpen_N := hUo
      smooth := hsmooth.mono hUW
      immersion := hUimm
      inj := hUinj
      level := fun y hy => by
        obtain ⟨N', ψ', hC, hyN, -, he⟩ := hloc y (hUW hy)
        rw [he]; exact hC.level y hyN
      memA := fun y hy => by
        obtain ⟨N', ψ', hC, hyN, -, he⟩ := hloc y (hUW hy)
        rw [he]; exact hC.memA y hyN
      memB := fun y hy => by
        obtain ⟨N', ψ', hC, hyN, -, he⟩ := hloc y (hUW hy)
        rw [he]; exact hC.memB y hyN
      transA := fun y hy h1 => by
        obtain ⟨N', ψ', hC, hyN, hev, -⟩ := hloc y (hUW hy)
        have hev' : (fun y => D.leftCoord q hq ε (ψ₀ y)) =ᶠ[𝓝 y]
            (fun y => D.leftCoord q hq ε (ψ' y)) := hev.mono fun z hz => by simp only [hz]
        rw [hev'.fderiv_eq]; exact hC.transA y hyN h1
      transB := fun y hy h1 => by
        obtain ⟨N', ψ', hC, hyN, hev, -⟩ := hloc y (hUW hy)
        have hev' : (fun y => D.rightCoord p hp ε (ψ₀ y)) =ᶠ[𝓝 y]
            (fun y => D.rightCoord p hp ε (ψ' y)) := hev.mono fun z hz => by simp only [hz]
        rw [hev'.fderiv_eq]; exact hC.transB y hyN h1
      corner₁ := hcorner₁
      corner₂ := hcorner₂ }

theorem whitneyStrips_separated (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) {ℓ : ℕ} {ε c : ℝ} {x₁ x₂ : M} {U₁ U₂ : Set (Fin (n - 1) → ℝ)}
    {φ₁ φ₂ : (Fin (n - 1) → ℝ) → M} (hφ₁ : D.IsCornerChart c hp hq ε ℓ x₁ U₁ φ₁)
    (hφ₂ : D.IsCornerChart c hp hq ε ℓ x₂ U₂ φ₂) {γA γB : ℝ → M} {a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ}
    {δ : ℝ} (harcs : D.IsWhitneyArcs c hp hq ε ℓ φ₁ φ₂ U₁ U₂ γA γB a₁ a₂ b₁ b₂ δ)
    {ρ r₁ r₂ : ℝ} (hρ : 0 < ρ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₂1 : r₂ ≤ 1)
    {NA NB : Set (Fin 2 → ℝ)} {ψA ψB : (Fin 2 → ℝ) → M}
    (hNA : {y | y ∈ whitneyHalf ∧ y 1 ≤ r₁} ⊆ NA) (hA : D.IsWhitneyCollar c hp hq ε x₁ x₂ NA ψA)
    (hA₁ : ∀ y ∈ NA, dist y ![-1, 0] < ρ →
      ψA y = φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁))
    (hA₂ : ∀ y ∈ NA, dist y ![1, 0] < ρ →
      ψA y = φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂))
    (hAloc : ∀ O : Set M, IsOpen O → ∀ κ : ℝ, 0 < κ → (∀ t ∈ Icc (-1 + κ) (1 - κ), γA t ∈ O) →
      ∃ r' > 0, ∀ y ∈ NA, |y 1| < r' → |y 0| ≤ 1 - 2 * κ → ψA y ∈ O)
    (hNB : {y | y ∈ whitneyHalf ∧ (1 - r₂) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2} ⊆ NB)
    (hB : D.IsWhitneyCollar c hp hq ε x₁ x₂ NB ψB)
    (hB₁ : ∀ y ∈ NB, dist y ![-1, 0] < ρ →
      ψB y = φ₁ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₁ + (Real.pi - whitneyAngle y) • b₁))
    (hB₂ : ∀ y ∈ NB, dist y ![1, 0] < ρ →
      ψB y = φ₂ ((1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • a₂ + whitneyAngle y • b₂))
    (hBloc : ∀ O : Set M, IsOpen O → ∀ κ : ℝ, 0 < κ → (∀ t ∈ Icc κ (Real.pi - κ), γB t ∈ O) →
      ∃ r' > 0, ∀ y ∈ NB, |1 - Real.sqrt (y 0 ^ 2 + y 1 ^ 2)| < r' → 2 * κ ≤ whitneyAngle y →
        whitneyAngle y ≤ Real.pi - 2 * κ → ψB y ∈ O) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧
      whitneyBand r ⊆ (NA ∩ {y | |y 1| < 2 * r}) ∪
        (NB ∩ {y | (1 - 2 * r) ^ 2 < y 0 ^ 2 + y 1 ^ 2 ∧ y 0 ^ 2 + y 1 ^ 2 < (1 + 2 * r) ^ 2 ∧
          -(2 * r) < y 1}) ∧
      EqOn ψA ψB ((NA ∩ {y | |y 1| < 2 * r}) ∩
        (NB ∩ {y | (1 - 2 * r) ^ 2 < y 0 ^ 2 + y 1 ^ 2 ∧ y 0 ^ 2 + y 1 ^ 2 < (1 + 2 * r) ^ 2 ∧
          -(2 * r) < y 1})) ∧
      ∀ y ∈ whitneyBand r ∩ (NA ∩ {y | |y 1| < 2 * r}),
        ∀ y' ∈ whitneyBand r ∩ (NB ∩ {y | (1 - 2 * r) ^ 2 < y 0 ^ 2 + y 1 ^ 2 ∧
          y 0 ^ 2 + y 1 ^ 2 < (1 + 2 * r) ^ 2 ∧ -(2 * r) < y 1}),
          ψA y = ψB y' → y = y' := by
  have _ := hφ₁.zero_mem
  have _ := hφ₂.zero_mem
  set κ : ℝ := min (min r₁ r₂) (min ρ 1) / 4 with hκdef
  have hκ : 0 < κ := by
    have : 0 < min (min r₁ r₂) (min ρ 1) :=
      lt_min (lt_min hr₁ hr₂) (lt_min hρ one_pos)
    positivity
  have hκr₁ : 4 * κ ≤ r₁ := by
    have := min_le_left (min r₁ r₂) (min ρ 1); have := min_le_left r₁ r₂; linarith
  have hκr₂ : 4 * κ ≤ r₂ := by
    have := min_le_left (min r₁ r₂) (min ρ 1); have := min_le_right r₁ r₂; linarith
  have hκρ : 4 * κ ≤ ρ := by
    have := min_le_right (min r₁ r₂) (min ρ 1); have := min_le_left ρ 1; linarith
  have hκ1 : 4 * κ ≤ 1 := by
    have := min_le_right (min r₁ r₂) (min ρ 1); have := min_le_right ρ 1; linarith
  have hκsq : κ ^ 2 ≤ κ / 4 := by
    have := mul_le_mul_of_nonneg_left (show κ ≤ 1 / 4 by linarith) hκ.le
    rw [pow_two]; linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hγA : Continuous γA := harcs.smoothA.continuous
  have hγB : Continuous γB := harcs.smoothB.continuous
  have hdisj : Disjoint (γA '' Icc (-1 + κ) (1 - κ)) (γB '' Icc κ (Real.pi - κ)) := by
    rw [Set.disjoint_left]
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hvI : v ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hL : γB v ∈ D.leftSphere q hq ε c := hvu ▸ (harcs.memA u huI).1
    rcases ((harcs.memB v hvI).2.1 hL) with h | h
    · linarith [hv.1]
    · linarith [hv.2]
  obtain ⟨OA, OB, hOAo, hOBo, hKA, hKB, hOAB⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_Icc.image hγA) (isCompact_Icc.image hγB) hdisj
  obtain ⟨rA, hrA, hlocA⟩ := hAloc OA hOAo κ hκ (fun t ht => hKA ⟨t, ht, rfl⟩)
  obtain ⟨rB, hrB, hlocB⟩ := hBloc OB hOBo κ hκ (fun t ht => hKB ⟨t, ht, rfl⟩)
  set m : ℝ := min (min (min r₁ r₂) (min rA rB)) (min ρ 1) with hmdef
  have hm : 0 < m := lt_min (lt_min (lt_min hr₁ hr₂) (lt_min hrA hrB)) (lt_min hρ one_pos)
  have hmr₁ : m ≤ r₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmr₂ : m ≤ r₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmrA : m ≤ rA := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmrB : m ≤ rB := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmρ : m ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hm1 : m ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  set t : ℝ := m / 8 with htdef
  have ht0 : 0 < t := by positivity
  have ht8 : 8 * t = m := by rw [htdef]; ring
  have hdist : ∀ (z : Fin 2 → ℝ) (e : ℝ), |z 0 - e| < ρ → |z 1| < ρ → dist z ![e, 0] < ρ := by
    intro z e h0 h1
    rw [dist_pi_lt_iff hρ]
    intro i
    fin_cases i
    · simpa [Real.dist_eq] using h0
    · simpa [Real.dist_eq] using h1
  have hcorner : ∀ z : Fin 2 → ℝ, z ∈ NA → z ∈ NB →
      (dist z ![-1, 0] < ρ ∨ dist z ![1, 0] < ρ) → ψA z = ψB z := by
    intro z hzA hzB h
    rcases h with h | h
    · rw [hA₁ z hzA h, hB₁ z hzB h]
    · rw [hA₂ z hzA h, hB₂ z hzB h]
  have hnear : ∀ (z : Fin 2 → ℝ) (e : ℝ), z 0 ^ 2 + z 1 ^ 2 ≤ 1 → 0 ≤ z 1 → 1 - e < |z 0| →
      e < ρ → z 1 < ρ → (dist z ![-1, 0] < ρ ∨ dist z ![1, 0] < ρ) := by
    intro z e hz1 hz0 hze heρ hz1ρ
    have hle : |z 0| ≤ 1 := (sq_le_one_iff_abs_le_one (z 0)).1 (by linarith [sq_nonneg (z 1)])
    have hz1' : |z 1| < ρ := by rw [abs_of_nonneg hz0]; exact hz1ρ
    rcases le_or_gt 0 (z 0) with hnn | hneg
    · rw [abs_of_nonneg hnn] at hze hle
      refine Or.inr (hdist z 1 ?_ hz1')
      rw [abs_lt]; constructor <;> linarith
    · rw [abs_of_neg hneg] at hze hle
      refine Or.inl (hdist z (-1) ?_ hz1')
      rw [abs_lt]; constructor <;> linarith
  refine ⟨t, ht0, by linarith, ?_, ?_, ?_⟩
  · rintro y ⟨hyH, hy⟩
    have hyH' : y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ 0 ≤ y 1 := hyH
    rcases hy with hy | hy
    · left
      refine ⟨hNA ⟨hyH, by linarith⟩, ?_⟩
      change |y 1| < 2 * t
      rw [abs_of_nonneg hyH'.2]
      linarith
    · right
      have h1 : (1 - r₂) ^ 2 ≤ (1 - t) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 : (1 - 2 * t) ^ 2 < (1 - t) ^ 2 :=
        pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
      have h3 : (1 : ℝ) ^ 2 < (1 + 2 * t) ^ 2 :=
        pow_lt_pow_left₀ (by linarith) zero_le_one two_ne_zero
      rw [one_pow] at h3
      exact ⟨hNB ⟨hyH, by linarith⟩, by linarith, by linarith, by linarith [hyH'.2]⟩
  · rintro y ⟨⟨hyA, hy1⟩, ⟨hyB, hs1, hs2, -⟩⟩
    have hy1' : |y 1| < 2 * t := hy1
    have hy1sq : y 1 ^ 2 < (2 * t) ^ 2 := sq_lt_sq' (abs_lt.1 hy1').1 (abs_lt.1 hy1').2
    have hs1' : (1 - 2 * t) ^ 2 < y 0 ^ 2 + y 1 ^ 2 := hs1
    have hs2' : y 0 ^ 2 + y 1 ^ 2 < (1 + 2 * t) ^ 2 := hs2
    have hid : (1 - 2 * t) ^ 2 = 1 - 4 * t + (2 * t) ^ 2 := by ring
    have hy0sq : 1 - 4 * t < y 0 ^ 2 := by linarith
    have h4 : (1 - 4 * t) ^ 2 ≤ 1 - 4 * t := by
      have := mul_le_mul_of_nonneg_left (show 1 - 4 * t ≤ 1 by linarith)
        (show (0 : ℝ) ≤ 1 - 4 * t by linarith)
      rw [pow_two]; linarith
    have hlow : |1 - 4 * t| < |y 0| := sq_lt_sq.1 (by linarith)
    rw [abs_of_nonneg (by linarith)] at hlow
    have hup : |y 0| < 1 + 2 * t :=
      abs_lt_of_sq_lt_sq (by linarith [sq_nonneg (y 1)]) (by linarith)
    refine hcorner y hyA hyB ?_
    rcases le_or_gt 0 (y 0) with hnn | hneg
    · rw [abs_of_nonneg hnn] at hlow hup
      refine Or.inr (hdist y 1 ?_ (by linarith))
      rw [abs_lt]; constructor <;> linarith
    · rw [abs_of_neg hneg] at hlow hup
      refine Or.inl (hdist y (-1) ?_ (by linarith))
      rw [abs_lt]; constructor <;> linarith
  · rintro y ⟨hyband, hyA, hy1⟩ y' ⟨hy'band, hy'B, hs1, hs2, -⟩ heq
    have hyH : y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ 0 ≤ y 1 := hyband.1
    have hy'H : y' 0 ^ 2 + y' 1 ^ 2 ≤ 1 ∧ 0 ≤ y' 1 := hy'band.1
    have hy1' : |y 1| < 2 * t := hy1
    have hy1lt : y 1 < 2 * t := lt_of_le_of_lt (le_abs_self _) hy1'
    have hs1' : (1 - 2 * t) ^ 2 < y' 0 ^ 2 + y' 1 ^ 2 := hs1
    by_cases hmidA : |y 0| ≤ 1 - 2 * κ
    swap
    · push Not at hmidA
      have hy0sq : (1 - 2 * κ) ^ 2 < y 0 ^ 2 := by
        rw [← sq_abs (y 0)]
        exact pow_lt_pow_left₀ hmidA (by linarith) two_ne_zero
      have h1 : (1 - r₂) ^ 2 ≤ (1 - 2 * κ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hyNB : y ∈ NB := hNB ⟨hyband.1, by linarith [sq_nonneg (y 1)]⟩
      have hψ : ψA y = ψB y :=
        hcorner y hyA hyNB (hnear y (2 * κ) hyH.1 hyH.2 hmidA (by linarith) (by linarith))
      exact hB.inj hyNB hy'B (hψ.symm.trans heq)
    by_cases hmidB : 2 * κ ≤ whitneyAngle y' ∧ whitneyAngle y' ≤ Real.pi - 2 * κ
    swap
    · set S := Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) with hSdef
      have hS1 : S ≤ 1 := Real.sqrt_le_one.2 hy'H.1
      have hSlow : 1 - 2 * t < S := (Real.lt_sqrt (by linarith)).2 hs1'
      have hSpos : 0 < S + y' 1 := by linarith [hy'H.2]
      obtain ⟨-, -, -, hpol, -⟩ := whitneyAngle_spec
      obtain ⟨hθ, hy'0, hy'1⟩ := hpol y' hSpos
      set θ := whitneyAngle y' with hθdef
      have hsin : 0 ≤ Real.sin θ := by
        by_contra hcon
        push Not at hcon
        have : S * Real.sin θ < 0 := mul_neg_of_pos_of_neg (by linarith) hcon
        linarith [hy'H.2]
      have hθ0 : 0 ≤ θ := by
        by_contra hcon
        push Not at hcon
        have := Real.sin_neg_of_neg_of_neg_pi_lt hcon (by linarith [hθ.1])
        linarith
      have hθπ : θ ≤ Real.pi := by
        by_contra hcon
        push Not at hcon
        have h1 : 0 < Real.sin (θ - Real.pi) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2])
        rw [Real.sin_sub_pi] at h1
        linarith
      have key : ∀ u : ℝ, 0 ≤ u → u < 2 * κ → y' 1 = S * Real.sin u →
          1 - 2 * t - 2 * κ ^ 2 ≤ S * Real.cos u ∧ S * Real.cos u ≤ 1 ∧ y' 1 < 2 * κ := by
        intro u hu0 hu hy1u
        have hcos := Real.one_sub_sq_div_two_le_cos (x := u)
        have hcos1 := Real.cos_le_one u
        have hu2 : u ^ 2 ≤ (2 * κ) ^ 2 := pow_le_pow_left₀ hu0 hu.le 2
        have hid : (2 * κ) ^ 2 = 4 * κ ^ 2 := by ring
        have hcpos : 0 ≤ 1 - 2 * κ ^ 2 := by linarith
        have hcu : 1 - 2 * κ ^ 2 ≤ Real.cos u := by linarith
        have hsu : 0 ≤ Real.sin u := by
          by_contra hcon
          push Not at hcon
          have : S * Real.sin u < 0 := mul_neg_of_pos_of_neg (by linarith) hcon
          linarith [hy'H.2]
        refine ⟨?_, ?_, ?_⟩
        · have h1 : (1 - 2 * t) * (1 - 2 * κ ^ 2) ≤ S * Real.cos u :=
            mul_le_mul hSlow.le hcu hcpos (by linarith)
          have h2 : (1 - 2 * t) * (1 - 2 * κ ^ 2) = 1 - 2 * t - 2 * κ ^ 2 + 4 * (t * κ ^ 2) := by
            ring
          have h3 : 0 ≤ t * κ ^ 2 := mul_nonneg ht0.le (sq_nonneg κ)
          linarith
        · have h1 : S * Real.cos u ≤ S * 1 :=
            mul_le_mul_of_nonneg_left hcos1 (by linarith)
          linarith
        · have h1 : S * Real.sin u ≤ Real.sin u := mul_le_of_le_one_left hsu hS1
          have h2 := Real.sin_le hu0
          linarith
      have hmκ : 2 * t + 2 * κ ^ 2 < ρ := by linarith
      have hpair : y' ∈ NA ∧ ψA y' = ψB y' := by
        rw [not_and_or] at hmidB
        rcases hmidB with h | h
        · push Not at h
          obtain ⟨hc1, hc2, hc3⟩ := key θ hθ0 h hy'1
          have hy'NA : y' ∈ NA := hNA ⟨hy'band.1, by linarith⟩
          refine ⟨hy'NA, hcorner y' hy'NA hy'B (Or.inr (hdist y' 1 ?_ ?_))⟩
          · rw [abs_lt]; constructor <;> linarith
          · rw [abs_of_nonneg hy'H.2]; linarith
        · push Not at h
          have hsθ : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
          have hcθ : Real.cos θ = -Real.cos (Real.pi - θ) := by rw [Real.cos_pi_sub]; ring
          rw [hsθ] at hy'1
          rw [hcθ] at hy'0
          obtain ⟨hc1, hc2, hc3⟩ := key (Real.pi - θ) (by linarith) (by linarith) hy'1
          have hy'NA : y' ∈ NA := hNA ⟨hy'band.1, by linarith⟩
          refine ⟨hy'NA, hcorner y' hy'NA hy'B (Or.inl (hdist y' (-1) ?_ ?_))⟩
          · rw [abs_lt]; constructor <;> linarith
          · rw [abs_of_nonneg hy'H.2]; linarith
      exact hA.inj hyA hpair.1 (heq.trans hpair.2.symm)
    · exfalso
      have h1 : ψA y ∈ OA := hlocA y hyA (by linarith) hmidA
      have hS1 : Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) ≤ 1 := Real.sqrt_le_one.2 hy'H.1
      have hSlow : 1 - 2 * t < Real.sqrt (y' 0 ^ 2 + y' 1 ^ 2) :=
        (Real.lt_sqrt (by linarith)).2 hs1'
      have h2 : ψB y' ∈ OB := hlocB y' hy'B (by rw [abs_lt]; constructor <;> linarith)
        hmidB.1 hmidB.2
      rw [heq] at h1
      exact Set.disjoint_left.1 hOAB h1 h2

theorem exists_whitneyCollar (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {x₁ x₂ : M} {U₁ U₂ : Set (Fin (n - 1) → ℝ)}
    {φ₁ φ₂ : (Fin (n - 1) → ℝ) → M} (hφ₁ : D.IsCornerChart c hp hq ε ℓ x₁ U₁ φ₁)
    (hφ₂ : D.IsCornerChart c hp hq ε ℓ x₂ U₂ φ₂) {γA γB : ℝ → M} {a₁ a₂ b₁ b₂ : Fin (n - 1) → ℝ}
    {δ : ℝ} (harcs : D.IsWhitneyArcs c hp hq ε ℓ φ₁ φ₂ U₁ U₂ γA γB a₁ a₂ b₁ b₂ δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧ ∃ (N : Set (Fin 2 → ℝ)) (ψ₀ : (Fin 2 → ℝ) → M),
      whitneyBand r ⊆ N ∧ D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ₀ := by
  classical
  obtain ⟨hε, -, -, -, hrmq8, hpq, hball⟩ := id hv
  have hrmp8 : 8 * ε < D.rm p hp ^ 2 := hv.2.2.2.1
  have hfp : f p ∈ Ioo a b := D.inStrip p hp (D.smallBall_subset_image_ball p hp (D.p_mem_smallBall p hp))
  have hfq : f q ∈ Ioo a b := D.inStrip q hq (D.smallBall_subset_image_ball q hq (D.p_mem_smallBall q hq))
  have hac : a ≤ c := by linarith [hfp.1]
  have hcb : c ≤ b := by linarith [hfq.2]
  have hregc : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro x hx h0
    have hu := D.unit x (by rw [mem_preimage, hx]; exact ⟨hac, hcb⟩)
      (fun p' hp' => hball x (by rw [hx]; constructor <;> linarith) p' hp')
    rw [h0] at hu
    simp at hu
  obtain ⟨OL, hOL, hSLO, hGL, hsubL⟩ := D.leftCoord_submersion hf hq hε (by linarith) hac hc₂.le
    (fun y hy x hx => hball y ⟨by linarith [hy.1], hy.2⟩ x hx)
  obtain ⟨OR, hOR, hSRO, hGR, hsubR⟩ := D.rightCoord_submersion hf hp hε (by linarith) hc₁.le hcb
    (fun y hy x hx => hball y ⟨hy.1, by linarith [hy.2]⟩ x hx)
  have hL : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ → ∀ {b' : Fin (n - 1) → ℝ}, b' ≠ 0 →
      (∀ j, j < ℓ → coordN b' j = 0) → ∀ z ∈ U, φ z ∈ OL →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (φ z)
        (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ z b') ≠ 0 := by
    intro x U φ hφ b' hb hbR z hz hzO
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
    have hj' : b' j ≠ 0 := by simpa using hj
    have hcj : coordN b' j = b' j := by simp [coordN]
    have hℓj : ℓ ≤ (j : ℕ) := by
      by_contra hlt
      exact hj' (hcj ▸ hbR j (by omega))
    have hjn := j.isLt
    let i : Fin (n - (D.chart q hq).k) := ⟨(j : ℕ) - ℓ, by rw [hkq]; omega⟩
    have hGmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
        (D.leftCoord q hq ε) (φ z) :=
      (hGL.contMDiffAt (hOL.mem_nhds hzO)).mdifferentiableAt (by simp)
    have hφmd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I φ z :=
      (hφ.smooth.contMDiffAt (hφ.isOpen_U.mem_nhds hz)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp z hGmd hφmd
    rw [mfderiv_eq_fderiv] at hcomp
    have hFd : DifferentiableAt ℝ (D.leftCoord q hq ε ∘ φ) z :=
      (hGmd.comp z hφmd).differentiableAt
    have h1 : HasFDerivAt (fun y : Fin (n - 1) → ℝ => y j)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (D.leftCoord q hq ε ∘ φ) z)) z := by
      refine ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hFd.hasFDerivAt).congr_of_eventuallyEq ?_
      filter_upwards [hφ.isOpen_U.mem_nhds hz] with y hy
      have := hφ.coordL y hy i
      simp only [Function.comp_apply, PiLp.proj_apply]
      rw [this]
      simp only [coordN, i]
      split_ifs with hlt
      · congr 1
        ext
        simp
        omega
      · exfalso
        simp at hlt
        omega
    have h2 := congrArg (fun T => T b') (h1.unique (hasFDerivAt_apply j z))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h2
    intro h0
    apply hj'
    rw [← h2]
    exact (congrArg (EuclideanSpace.proj (𝕜 := ℝ) i)
      (DFunLike.congr_fun hcomp b')).trans
        ((congrArg (EuclideanSpace.proj (𝕜 := ℝ) i) h0).trans (map_zero _))
  have hR : ∀ {x : M} {U : Set (Fin (n - 1) → ℝ)} {φ : (Fin (n - 1) → ℝ) → M},
      D.IsCornerChart c hp hq ε ℓ x U φ → ∀ {a' : Fin (n - 1) → ℝ}, a' ≠ 0 →
      (∀ j, ℓ ≤ j → coordN a' j = 0) → ∀ z ∈ U, φ z ∈ OR →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (φ z)
        (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I φ z a') ≠ 0 := by
    intro x U φ hφ a' ha haL z hz hzO
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    have hj' : a' j ≠ 0 := by simpa using hj
    have hcj : coordN a' j = a' j := by simp [coordN]
    have hℓj : (j : ℕ) < ℓ := by
      by_contra hlt
      exact hj' (hcj ▸ haL j (by omega))
    let i : Fin (D.chart p hp).k := ⟨(j : ℕ), by rw [hkp]; omega⟩
    have hGmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (φ z) :=
      (hGR.contMDiffAt (hOR.mem_nhds hzO)).mdifferentiableAt (by simp)
    have hφmd : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I φ z :=
      (hφ.smooth.contMDiffAt (hφ.isOpen_U.mem_nhds hz)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp z hGmd hφmd
    rw [mfderiv_eq_fderiv] at hcomp
    have hFd : DifferentiableAt ℝ (D.rightCoord p hp ε ∘ φ) z :=
      (hGmd.comp z hφmd).differentiableAt
    have h1 : HasFDerivAt (fun y : Fin (n - 1) → ℝ => y j)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (D.rightCoord p hp ε ∘ φ) z)) z := by
      refine ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hFd.hasFDerivAt).congr_of_eventuallyEq ?_
      filter_upwards [hφ.isOpen_U.mem_nhds hz] with y hy
      have := hφ.coordR y hy i
      simp only [Function.comp_apply, PiLp.proj_apply]
      rw [this]
      simp [coordN, i]
    have h2 := congrArg (fun T => T a') (h1.unique (hasFDerivAt_apply j z))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h2
    intro h0
    apply hj'
    rw [← h2]
    exact (congrArg (EuclideanSpace.proj (𝕜 := ℝ) i)
      (DFunLike.congr_fun hcomp a')).trans
        ((congrArg (EuclideanSpace.proj (𝕜 := ℝ) i) h0).trans (map_zero _))
  have hδ := harcs.hδ
  have hsegcpt : ∀ v : Fin (n - 1) → ℝ, IsCompact ((fun s : ℝ => s • v) '' Icc 0 (δ / 2)) :=
    fun v => isCompact_Icc.image (continuous_id.smul continuous_const)
  have hsegA₁ : (fun s : ℝ => s • a₁) '' Icc 0 (δ / 2) ⊆ U₁ := by
    rintro _ ⟨s, hs, rfl⟩
    have h := (harcs.endA₁ (s - 1) (by rw [sub_add_cancel, abs_lt]; constructor <;> linarith [hs.1, hs.2])).1
    rwa [sub_add_cancel] at h
  have hsegA₂ : (fun s : ℝ => s • a₂) '' Icc 0 (δ / 2) ⊆ U₂ := by
    rintro _ ⟨s, hs, rfl⟩
    have h := (harcs.endA₂ (1 - s) (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])).1
    rwa [sub_sub_cancel] at h
  have hsegB₂ : (fun s : ℝ => s • b₂) '' Icc 0 (δ / 2) ⊆ U₂ := by
    rintro _ ⟨s, hs, rfl⟩
    exact (harcs.endB₂ s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])).1
  have hsegB₁ : (fun s : ℝ => s • b₁) '' Icc 0 (δ / 2) ⊆ U₁ := by
    rintro _ ⟨s, hs, rfl⟩
    have h := (harcs.endB₁ (Real.pi - s) (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])).1
    rwa [sub_sub_cancel] at h
  have hreg₁ : ∀ z ∈ U₁, mfderiv I 𝓘(ℝ, ℝ) f (φ₁ z) ≠ 0 := fun z hz => hregc _ (hφ₁.level z hz)
  have hreg₂ : ∀ z ∈ U₂, mfderiv I 𝓘(ℝ, ℝ) f (φ₂ z) ≠ 0 := fun z hz => hregc _ (hφ₂.level z hz)
  obtain ⟨Xb₁, Vb₁, hVb₁o, hKb₁, hVb₁U, hXb₁⟩ := exists_levelField_chartDir hf hφ₁.isOpen_U
    hφ₁.smooth hφ₁.immersion hφ₁.inj hφ₁.level hreg₁ hφ₁.open_image b₁ (hsegcpt a₁) hsegA₁
  obtain ⟨Xb₂, Vb₂, hVb₂o, hKb₂, hVb₂U, hXb₂⟩ := exists_levelField_chartDir hf hφ₂.isOpen_U
    hφ₂.smooth hφ₂.immersion hφ₂.inj hφ₂.level hreg₂ hφ₂.open_image b₂ (hsegcpt a₂) hsegA₂
  obtain ⟨Xa₂, Va₂, hVa₂o, hKa₂, hVa₂U, hXa₂⟩ := exists_levelField_chartDir hf hφ₂.isOpen_U
    hφ₂.smooth hφ₂.immersion hφ₂.inj hφ₂.level hreg₂ hφ₂.open_image a₂ (hsegcpt b₂) hsegB₂
  obtain ⟨Xa₁, Va₁, hVa₁o, hKa₁, hVa₁U, hXa₁⟩ := exists_levelField_chartDir hf hφ₁.isOpen_U
    hφ₁.smooth hφ₁.immersion hφ₁.inj hφ₁.level hreg₁ hφ₁.open_image a₁ (hsegcpt b₁) hsegB₁
  have hseg : ∀ (v : Fin (n - 1) → ℝ) (s : ℝ), 0 ≤ s → s ≤ δ / 2 →
      s • v ∈ (fun s : ℝ => s • v) '' Icc 0 (δ / 2) := fun v s h0 h1 => ⟨s, ⟨h0, h1⟩, rfl⟩
  set δA : ℝ := min (δ / 2) (1 / 2) with hδA_def
  have hδA : 0 < δA := lt_min (by linarith) (by norm_num)
  have hδA₁ : δA ≤ δ / 2 := min_le_left _ _
  have hδA₂ : δA ≤ 1 / 2 := min_le_right _ _
  obtain ⟨X, hXtr, ⟨W₁, hW₁, hXW₁⟩, ⟨W₂, hW₂, hXW₂⟩⟩ := exists_levelField_arc hf
    (s := n - (D.chart q hq).k) (by rw [hkq]; omega) harcs.smoothA.continuous (t₀ := -1) (t₁ := 1)
    hδA (by linarith) harcs.injA (fun t ht => (hsubL _ (harcs.memA t ht).1).1) hOL
    (fun t ht => hSLO (harcs.memA t ht).1) hGL (fun t ht => (hsubL _ (harcs.memA t ht).1).2)
    Xb₁ Xb₂ (by
      intro t ht
      have hmem := (harcs.memA t ⟨ht.1, by linarith [ht.2]⟩).1
      obtain ⟨hzU, hγ⟩ := harcs.endA₁ t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [hγ] at hmem ⊢
      rw [hXb₁ _ (hKb₁ (hseg a₁ (t + 1) (by linarith [ht.1]) (by linarith [ht.2])))]
      exact hL hφ₁ harcs.dirB.1 harcs.dirB.2.2.1 _ hzU (hSLO hmem))
    (by
      intro t ht
      have hmem := (harcs.memA t ⟨by linarith [ht.1], ht.2⟩).1
      obtain ⟨hzU, hγ⟩ := harcs.endA₂ t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [hγ] at hmem ⊢
      rw [hXb₂ _ (hKb₂ (hseg a₂ (1 - t) (by linarith [ht.2]) (by linarith [ht.1])))]
      exact hL hφ₂ harcs.dirB.2.1 harcs.dirB.2.2.2 _ hzU (hSLO hmem))
  have hpi3 := Real.pi_gt_three
  set δB : ℝ := min (δ / 2) 1 with hδB_def
  have hδB : 0 < δB := lt_min (by linarith) (by norm_num)
  have hδB₁ : δB ≤ δ / 2 := min_le_left _ _
  have hδB₂ : δB ≤ 1 := min_le_right _ _
  obtain ⟨X', hX'tr, ⟨W₁', hW₁', hX'W₁⟩, ⟨W₂', hW₂', hX'W₂⟩⟩ := exists_levelField_arc hf
    (s := (D.chart p hp).k) (by rw [hkp]; omega) harcs.smoothB.continuous (t₀ := 0)
    (t₁ := Real.pi) hδB (by linarith) harcs.injB (fun t ht => (hsubR _ (harcs.memB t ht).1).1) hOR
    (fun t ht => hSRO (harcs.memB t ht).1) hGR (fun t ht => (hsubR _ (harcs.memB t ht).1).2)
    Xa₂ Xa₁ (by
      intro t ht
      have hmem := (harcs.memB t ⟨ht.1, by linarith [ht.2]⟩).1
      obtain ⟨hzU, hγ⟩ := harcs.endB₂ t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [hγ] at hmem ⊢
      rw [hXa₂ _ (hKa₂ (hseg b₂ t (by linarith [ht.1]) (by linarith [ht.2])))]
      exact hR hφ₂ harcs.dirA.2.1 harcs.dirA.2.2.2 _ hzU (hSRO hmem))
    (by
      intro t ht
      have hmem := (harcs.memB t ⟨by linarith [ht.1], ht.2⟩).1
      obtain ⟨hzU, hγ⟩ := harcs.endB₁ t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [hγ] at hmem ⊢
      rw [hXa₁ _ (hKa₁ (hseg b₁ (Real.pi - t) (by linarith [ht.2]) (by linarith [ht.1])))]
      exact hR hφ₁ harcs.dirA.1 harcs.dirA.2.2.1 _ hzU (hSRO hmem))
  have hφ₁c := hφ₁.smooth.continuousOn
  have hφ₂c := hφ₂.smooth.continuousOn
  have hγA₁ : γA (-1) = φ₁ 0 := by
    have h := (harcs.endA₁ (-1) (by norm_num; linarith)).2
    simpa using h
  have hγA₂ : γA 1 = φ₂ 0 := by
    have h := (harcs.endA₂ 1 (by norm_num; linarith)).2
    simpa using h
  have hγB₂ : γB 0 = φ₂ 0 := by
    have h := (harcs.endB₂ 0 (by norm_num; linarith)).2
    simpa using h
  have hγB₁ : γB Real.pi = φ₁ 0 := by
    have h := (harcs.endB₁ Real.pi (by norm_num; linarith)).2
    simpa using h
  have h0mem : ∀ v : Fin (n - 1) → ℝ, (0 : Fin (n - 1) → ℝ) ∈ (fun s : ℝ => s • v) '' Icc 0 (δ / 2) :=
    fun v => ⟨0, ⟨le_refl _, by linarith⟩, zero_smul _ _⟩
  have hint₁ : φ₁ 0 ∈ interior W₁ :=
    subset_interior_iff_mem_nhdsSet.mpr hW₁ ⟨-1, ⟨le_refl _, by linarith⟩, hγA₁⟩
  have hint₂ : φ₂ 0 ∈ interior W₂ :=
    subset_interior_iff_mem_nhdsSet.mpr hW₂ ⟨1, ⟨by linarith, le_refl _⟩, hγA₂⟩
  have hint₁' : φ₂ 0 ∈ interior W₁' :=
    subset_interior_iff_mem_nhdsSet.mpr hW₁' ⟨0, ⟨le_refl _, by linarith⟩, hγB₂⟩
  have hint₂' : φ₁ 0 ∈ interior W₂' :=
    subset_interior_iff_mem_nhdsSet.mpr hW₂' ⟨Real.pi, ⟨by linarith, le_refl _⟩, hγB₁⟩
  obtain ⟨ρA, r₁, hρA, hr₁, NA, ψA, hNA, hA, hA₁, hA₂, hAloc⟩ := D.exists_diameterStrip hf hp hq
    hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hφ₁ hφ₂ harcs X
    (V₁ := Vb₁ ∩ (U₁ ∩ φ₁ ⁻¹' interior W₁)) (V₂ := Vb₂ ∩ (U₂ ∩ φ₂ ⁻¹' interior W₂))
    (hVb₁o.inter (hφ₁c.isOpen_inter_preimage hφ₁.isOpen_U isOpen_interior))
    (hVb₂o.inter (hφ₂c.isOpen_inter_preimage hφ₂.isOpen_U isOpen_interior))
    ⟨hKb₁ (h0mem a₁), hφ₁.zero_mem, hint₁⟩ ⟨hKb₂ (h0mem a₂), hφ₂.zero_mem, hint₂⟩
    (fun z hz => hz.2.1) (fun z hz => hz.2.1)
    (fun z hz => (hXW₁ _ (interior_subset hz.2.2)).trans (hXb₁ z hz.1))
    (fun z hz => (hXW₂ _ (interior_subset hz.2.2)).trans (hXb₂ z hz.1)) hXtr
  obtain ⟨ρB, r₂, hρB, hr₂, hr₂1, NB, ψB, hNB, hB, hB₁, hB₂, hBloc⟩ := D.exists_circleStrip hf hp hq
    hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hφ₁ hφ₂ harcs X'
    (V₁ := Va₁ ∩ (U₁ ∩ φ₁ ⁻¹' interior W₂')) (V₂ := Va₂ ∩ (U₂ ∩ φ₂ ⁻¹' interior W₁'))
    (hVa₁o.inter (hφ₁c.isOpen_inter_preimage hφ₁.isOpen_U isOpen_interior))
    (hVa₂o.inter (hφ₂c.isOpen_inter_preimage hφ₂.isOpen_U isOpen_interior))
    ⟨hKa₁ (h0mem b₁), hφ₁.zero_mem, hint₂'⟩ ⟨hKa₂ (h0mem b₂), hφ₂.zero_mem, hint₁'⟩
    (fun z hz => hz.2.1) (fun z hz => hz.2.1)
    (fun z hz => (hX'W₂ _ (interior_subset hz.2.2)).trans (hXa₁ z hz.1))
    (fun z hz => (hX'W₁ _ (interior_subset hz.2.2)).trans (hXa₂ z hz.1)) hX'tr
  have hρ : 0 < min ρA ρB := lt_min hρA hρB
  obtain ⟨r, hr, hr4, hcov, hEq, hsep⟩ := D.whitneyStrips_separated hp hq hφ₁ hφ₂ harcs hρ hr₁ hr₂
    hr₂1 hNA hA (fun y hy hd => hA₁ y hy (hd.trans_le (min_le_left _ _)))
    (fun y hy hd => hA₂ y hy (hd.trans_le (min_le_left _ _))) hAloc hNB hB
    (fun y hy hd => hB₁ y hy (hd.trans_le (min_le_right _ _)))
    (fun y hy hd => hB₂ y hy (hd.trans_le (min_le_right _ _))) hBloc
  have hAo : IsOpen (NA ∩ {y : Fin 2 → ℝ | |y 1| < 2 * r}) :=
    hA.isOpen_N.inter (isOpen_lt (f := fun y : Fin 2 → ℝ => |y 1|) (by fun_prop) continuous_const)
  have hBo : IsOpen (NB ∩ {y : Fin 2 → ℝ | (1 - 2 * r) ^ 2 < y 0 ^ 2 + y 1 ^ 2 ∧
      y 0 ^ 2 + y 1 ^ 2 < (1 + 2 * r) ^ 2 ∧ -(2 * r) < y 1}) := by
    have hq2 : Continuous fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
    have hy1 : Continuous fun y : Fin 2 → ℝ => y 1 := continuous_apply 1
    exact hB.isOpen_N.inter ((isOpen_lt continuous_const hq2).inter
      ((isOpen_lt hq2 continuous_const).inter (isOpen_lt continuous_const hy1)))
  have hKc : IsCompact (whitneyBand r) := by
    have hq2 : Continuous fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
    have hy1 : Continuous fun y : Fin 2 → ℝ => y 1 := continuous_apply 1
    apply Metric.isCompact_of_isClosed_isBounded
    · have e : whitneyBand r = ({y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩ {y | 0 ≤ y 1}) ∩
          ({y | y 1 ≤ r} ∪ {y | (1 - r) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2}) := by
        ext y
        simp [whitneyBand, whitneyHalf]
      rw [e]
      exact ((isClosed_le hq2 continuous_const).inter (isClosed_le continuous_const hy1)).inter
        ((isClosed_le hy1 continuous_const).union (isClosed_le continuous_const hq2))
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨1, fun y hy => ?_⟩
      obtain ⟨⟨h1, h2⟩, -⟩ := hy
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      · rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  obtain ⟨N, ψ₀, hKN, hcol⟩ := D.glue_whitneyCollars hp hq hA hB hAo hBo inter_subset_left
    inter_subset_left hEq hKc hcov hsep
  exact ⟨r, hr, hr4, N, ψ₀, hKN, hcol⟩

theorem exists_whitney_smoothing (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {c κ : ℝ} (hκ : 0 < κ) (hcκ : a ≤ c - κ ∧ c + κ ≤ b)
    (hU : ∀ y, f y ∈ Icc (c - κ) (c + κ) → ∀ x hx, y ∉ D.smallBall x hx)
    {r : ℝ} (hr : 0 < r) {N : Set (Fin 2 → ℝ)} (hNo : IsOpen N) (hN : whitneyBand r ⊆ N)
    {ψ₀ : (Fin 2 → ℝ) → M} (hψ₀ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ₀ N)
    (hψ₀c : ∀ y ∈ N, f (ψ₀ y) = c) {F : (Fin 2 → ℝ) → M} (hF : ContinuousOn F whitneyHalf)
    (hFc : ∀ y ∈ whitneyHalf, f (F y) = c) (hFψ : ∀ y ∈ whitneyBand (r / 2), F y = ψ₀ y)
    {O : Set M} (hO : IsOpen O)
    (hFO : ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 4) → F y ∈ O) :
    ∃ (W₁ N' : Set (Fin 2 → ℝ)) (ψ₁ : (Fin 2 → ℝ) → M), IsOpen W₁ ∧ whitneyHalf ⊆ W₁ ∧
      ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ₁ W₁ ∧ (∀ y ∈ W₁, f (ψ₁ y) = c) ∧
      IsOpen N' ∧ whitneyBand (r / 4) ⊆ N' ∧ N' ⊆ N ∩ W₁ ∧ (∀ y ∈ N', ψ₁ y = ψ₀ y) ∧
      ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 4) → ψ₁ y ∈ O := by
  classical
  have hfc : Continuous f := hf.continuous
  have hcIcc : c ∈ Icc a b := ⟨by linarith [hcκ.1], by linarith [hcκ.2]⟩
  have hhalf1 : ∀ y ∈ whitneyHalf, 0 ≤ y 1 ∧ y 1 ≤ 1 ∧ |y 0| ≤ 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ 1 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨h2, ?_, ?_, h1⟩
    · nlinarith [sq_nonneg (y 0)]
    · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y 1)]
  have hband_mono : ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → whitneyBand t ⊆ whitneyBand t' := by
    intro t t' ht htt' y hy
    obtain ⟨hyH, hy'⟩ := hy
    obtain ⟨h0, h1, -, h3⟩ := hhalf1 y hyH
    refine ⟨hyH, ?_⟩
    rcases hy' with hy' | hy'
    · exact Or.inl (hy'.trans htt')
    · rcases le_or_gt t' 1 with ht' | ht'
      · right
        have : (1 - t') ^ 2 ≤ (1 - t) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      · left; linarith
  have hhalf_closed : IsClosed whitneyHalf := by
    have h1 : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
    exact (isClosed_le h1 continuous_const).inter (isClosed_le continuous_const (continuous_apply 1))
  have hhalf_cpt : IsCompact whitneyHalf := by
    refine Metric.isCompact_of_isClosed_isBounded hhalf_closed ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_
    intro y hy
    obtain ⟨h0, h1, h2, -⟩ := hhalf1 y hy
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i
    · simpa [Real.norm_eq_abs] using h2
    · simp [Real.norm_eq_abs, abs_of_nonneg h0, h1]
  have hband_closed : ∀ t : ℝ, IsClosed (whitneyBand t) := by
    intro t
    have h1 : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
    exact hhalf_closed.inter ((isClosed_le (continuous_apply 1) continuous_const).union
      (isClosed_le continuous_const h1))
  have hband_cpt : ∀ t : ℝ, IsCompact (whitneyBand t) := fun t =>
    hhalf_cpt.of_isClosed_subset (hband_closed t) (fun y hy => hy.1)
  rcases le_or_gt 2 r with hr2 | hr2
  · have hall : ∀ t, 1 ≤ t → whitneyBand t = whitneyHalf := by
      intro t ht
      ext y
      refine ⟨fun hy => hy.1, fun hy => ⟨hy, Or.inl ?_⟩⟩
      linarith [(hhalf1 y hy).2.1]
    have hHN : whitneyHalf ⊆ N := (hall r (by linarith)) ▸ hN
    refine ⟨N, N, ψ₀, hNo, hHN, hψ₀, hψ₀c, hNo, ?_, fun y hy => ⟨hy, hy⟩, fun _ _ => rfl, ?_⟩
    · exact (fun y hy => hN (hband_mono (r / 4) r (by linarith) (by linarith) hy))
    · intro y hy hy4
      rw [← hFψ y (by rw [hall (r / 2) (by linarith)]; exact hy)]
      exact hFO y hy hy4
  have hnrm : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  set s : ℝ := 7 * r / 16 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : 0 < 1 - s := by rw [hs]; linarith
  set S : Set (Fin 2 → ℝ) := {y | s ≤ y 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ (1 - s) ^ 2} with hSdef
  have hS_closed : IsClosed S :=
    (isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le hnrm continuous_const)
  have hS_half : S ⊆ whitneyHalf := by
    intro y hy
    refine ⟨hy.2.trans ?_, hs0.le.trans hy.1⟩
    exact pow_le_one₀ hs1.le (by linarith)
  have hS_int : {y : Fin 2 → ℝ | s < y 1 ∧ y 0 ^ 2 + y 1 ^ 2 < (1 - s) ^ 2} ⊆ interior S := by
    refine interior_maximal (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_
    exact (isOpen_lt continuous_const (continuous_apply 1)).inter (isOpen_lt hnrm continuous_const)
  have hcore : ∀ y ∈ whitneyHalf, y ∉ interior S → y ∈ whitneyBand (r / 2) := by
    intro y hy hyS
    refine ⟨hy, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hyS
    apply hS_int
    refine ⟨by rw [hs]; linarith [hcon.1], ?_⟩
    have h1 : (1 - r / 2) ^ 2 < (1 - s) ^ 2 := by
      have : 0 < 1 - r / 2 := by linarith
      exact pow_lt_pow_left₀ (by rw [hs]; linarith) this.le two_ne_zero
    linarith [hcon.2]
  set G : (Fin 2 → ℝ) → M := S.piecewise F ψ₀ with hGdef
  set W : Set (Fin 2 → ℝ) := N ∪ interior S with hWdef
  have hWo : IsOpen W := hNo.union isOpen_interior
  have hHW : whitneyHalf ⊆ W := by
    intro y hy
    by_cases hyS : y ∈ interior S
    · exact Or.inr hyS
    · exact Or.inl (hN (hband_mono (r / 2) r (by linarith) (by linarith) (hcore y hy hyS)))
  have hGc : ContinuousOn G W := by
    refine ContinuousOn.piecewise ?_ ?_ ?_
    · intro y hy
      have hyS : y ∈ S := hS_closed.frontier_subset hy.2
      have hyi : y ∉ interior S := fun h => hy.2.2 h
      exact hFψ y (hcore y (hS_half hyS) hyi)
    · rw [hS_closed.closure_eq]
      exact hF.mono (fun y hy => hS_half hy.2)
    · refine hψ₀.continuousOn.mono ?_
      rintro y ⟨hyW, hyc⟩
      rw [closure_compl] at hyc
      rcases hyW with hyN | hyi
      · exact hyN
      · exact absurd hyi hyc
  have hGlev : ∀ y ∈ W, f (G y) = c := by
    intro y hy
    by_cases hyS : y ∈ S
    · rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hyS]; exact hFc y (hS_half hyS)
    · rw [hGdef, Set.piecewise_eq_of_notMem _ _ _ hyS]
      rcases hy with hyN | hyi
      · exact hψ₀c y hyN
      · exact absurd (interior_subset hyi) hyS
  have hGF : ∀ y ∈ whitneyHalf, G y = F y := by
    intro y hy
    by_cases hyS : y ∈ S
    · rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hyS]
    · rw [hGdef, Set.piecewise_eq_of_notMem _ _ _ hyS]
      exact (hFψ y (hcore y hy (fun h => hyS (interior_subset h)))).symm
  have hGψ : ∀ y, y ∉ S → G y = ψ₀ y := fun y hy => by
    rw [hGdef, Set.piecewise_eq_of_notMem _ _ _ hy]
  set Kf : ℝ → Set (Fin 2 → ℝ) := fun η => {y | y 0 ^ 2 + y 1 ^ 2 ≤ (1 + η) ^ 2 ∧ -η ≤ y 1}
    with hKf
  have hKf_closed : ∀ η, IsClosed (Kf η) := fun η =>
    (isClosed_le hnrm continuous_const).inter (isClosed_le continuous_const (continuous_apply 1))
  have hKf_cpt : ∀ η : ℝ, 0 ≤ η → η ≤ 1 → IsCompact (Kf η) := by
    intro η h0 h1
    refine Metric.isCompact_of_isClosed_isBounded (hKf_closed η) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 2)).subset ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have e0 : |y 0| ≤ 2 := abs_le.2 ⟨by nlinarith [sq_nonneg (y 1)], by nlinarith [sq_nonneg (y 1)]⟩
    have e1 : |y 1| ≤ 2 := abs_le.2 ⟨by nlinarith [sq_nonneg (y 0)], by nlinarith [sq_nonneg (y 0)]⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_two]
    intro i
    fin_cases i
    · simpa [Real.norm_eq_abs] using e0
    · simpa [Real.norm_eq_abs] using e1
  obtain ⟨m, hmW⟩ : ∃ m : ℕ, Kf (1 / ((m : ℝ) + 1)) ⊆ W := by
    have hanti : Antitone (fun m : ℕ => Kf (1 / ((m : ℝ) + 1))) := by
      intro i j hij y hy
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
      have hpos : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
      obtain ⟨h1, h2⟩ := hy
      exact ⟨h1.trans (pow_le_pow_left₀ (by linarith) (by linarith) 2), by linarith⟩
    refine exists_subset_nhds_of_isCompact' hanti.directed_ge
      (fun i => hKf_cpt _ (by positivity) ?_) (fun i => hKf_closed _) ?_
    · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · refine hWo.mem_nhdsSet.2 (fun y hy => hHW ?_)
      rw [mem_iInter] at hy
      refine ⟨?_, ?_⟩
      · by_contra hcon
        push Not at hcon
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < (y 0 ^ 2 + y 1 ^ 2 - 1) / 3 by linarith)
        obtain ⟨h1, -⟩ := hy k
        have he0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
        have he1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hsq : (1 / ((k : ℝ) + 1)) ^ 2 ≤ 1 / ((k : ℝ) + 1) :=
          pow_le_of_le_one he0.le he1 two_ne_zero
        have hexp : (1 + 1 / ((k : ℝ) + 1)) ^ 2 =
            1 + 2 * (1 / ((k : ℝ) + 1)) + (1 / ((k : ℝ) + 1)) ^ 2 := by ring
        linarith
      · by_contra hcon
        push Not at hcon
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < -y 1 by linarith)
        obtain ⟨-, h2⟩ := hy k
        linarith
  set η : ℝ := 1 / ((m : ℝ) + 1) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set K : Set (Fin 2 → ℝ) := Kf η with hK
  have hKW : K ⊆ W := hmW
  have hHK : whitneyHalf ⊆ K := by
    intro y hy
    obtain ⟨h0, -, -, h3⟩ := hhalf1 y hy
    exact ⟨h3.trans (one_le_pow₀ (by linarith)), by linarith⟩
  set w : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => y + (max (y 1) (-η) - y 1) • Pi.single 1 1
    with hw
  have hw0 : ∀ y, w y 0 = y 0 := fun y => by simp [hw]
  have hw1 : ∀ y, w y 1 = max (y 1) (-η) := fun y => by simp [hw]
  have hwc : Continuous w := by
    rw [hw]
    exact continuous_id.add
      (((continuous_apply 1).max continuous_const).sub (continuous_apply 1) |>.smul continuous_const)
  set lam : (Fin 2 → ℝ) → ℝ := fun y =>
    (1 + η) / max (1 + η) (Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2)) with hlam
  set ρ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => lam y • w y with hρ
  have hρc : Continuous ρ := by
    have h1 : Continuous (fun y => Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2)) :=
      (((continuous_apply 0).comp hwc).pow 2 |>.add (((continuous_apply 1).comp hwc).pow 2)).sqrt
    have h2 : Continuous lam := continuous_const.div (continuous_const.max h1)
      (fun y => (lt_of_lt_of_le (by linarith) (le_max_left _ _)).ne')
    exact h2.smul hwc
  have hρK : ∀ y, ρ y ∈ K := by
    intro y
    have hm : 0 < max (1 + η) (Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2)) :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg (w y 0)) (sq_nonneg (w y 1)))
    have hsq0 := Real.sqrt_nonneg (w y 0 ^ 2 + w y 1 ^ 2)
    have hle := le_max_right (1 + η) (Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2))
    have hle' := le_max_left (1 + η) (Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2))
    have hl0 : 0 < lam y := div_pos (by linarith) hm
    have hl1 : lam y ≤ 1 := (div_le_one hm).2 hle'
    have hlnw : lam y * Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2) ≤ 1 + η := by
      rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hm]
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    have hwη : -η ≤ w y 1 := by rw [hw1]; exact le_max_right _ _
    refine ⟨?_, ?_⟩
    · change (lam y • w y) 0 ^ 2 + (lam y • w y) 1 ^ 2 ≤ (1 + η) ^ 2
      simp only [Pi.smul_apply, smul_eq_mul]
      have : (lam y * w y 0) ^ 2 + (lam y * w y 1) ^ 2 =
          (lam y * Real.sqrt (w y 0 ^ 2 + w y 1 ^ 2)) ^ 2 := by
        rw [mul_pow (lam y) (Real.sqrt _), hsq]; ring
      rw [this]
      exact pow_le_pow_left₀ (mul_nonneg hl0.le hsq0) hlnw 2
    · change -η ≤ (lam y • w y) 1
      simp only [Pi.smul_apply, smul_eq_mul]
      rcases le_or_gt 0 (w y 1) with h | h
      · linarith [mul_nonneg hl0.le h]
      · linarith [mul_le_mul_of_nonpos_right hl1 h.le]
  have hρid : ∀ y ∈ K, ρ y = y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hwy : w y = y := by
      rw [hw]
      simp only
      rw [max_eq_left h2, sub_self, zero_smul, add_zero]
    have hlam1 : lam y = 1 := by
      rw [hlam]
      simp only
      rw [hwy]
      have : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ 1 + η := by
        rw [Real.sqrt_le_left (by linarith)]
        exact h1
      rw [max_eq_left this, div_self (by linarith)]
    change lam y • w y = y
    rw [hlam1, hwy, one_smul]
  set T : ℝ → ℝ := fun θ => 4 / Real.pi * Real.arcsin (Real.sin (2 * Real.pi * θ)) with hT
  have hTc : Continuous T := by
    rw [hT]
    exact continuous_const.mul (Real.continuous_arcsin.comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  have hTper : ∀ θ, T (θ + 1) = T θ := by
    intro θ
    simp only [hT]
    rw [show 2 * Real.pi * (θ + 1) = 2 * Real.pi * θ + 2 * Real.pi by ring, Real.sin_add_two_pi]
  have hTid : ∀ x : ℝ, |x| ≤ 2 → T (x / 8) = x := by
    intro x hx
    rw [abs_le] at hx
    simp only [hT]
    have hpi := Real.pi_pos
    have e1 := mul_le_mul_of_nonneg_left hx.1 hpi.le
    have e2 := mul_le_mul_of_nonneg_left hx.2 hpi.le
    rw [show 2 * Real.pi * (x / 8) = Real.pi * x / 4 by ring, Real.arcsin_sin
      (by linarith) (by linarith)]
    field_simp
  have hTsm : ∀ θ, |T θ| < 2 → ContDiffAt ℝ ∞ T θ := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hne1 : Real.sin (2 * Real.pi * θ) ≠ 1 := by
      intro h
      simp only [hT, h, Real.arcsin_one] at hθ
      rw [show 4 / Real.pi * (Real.pi / 2) = 2 by field_simp; ring, abs_of_pos two_pos] at hθ
      exact lt_irrefl _ hθ
    have hne2 : Real.sin (2 * Real.pi * θ) ≠ -1 := by
      intro h
      simp only [hT, h, Real.arcsin_neg_one] at hθ
      rw [show 4 / Real.pi * -(Real.pi / 2) = -2 by field_simp; ring, abs_neg,
        abs_of_pos two_pos] at hθ
      exact lt_irrefl _ hθ
    have h1 : ContDiffAt ℝ ∞ (fun θ : ℝ => Real.sin (2 * Real.pi * θ)) θ :=
      Real.contDiff_sin.contDiffAt.comp θ (contDiffAt_const.mul contDiffAt_id)
    have h2 : ContDiffAt ℝ ∞ (fun θ : ℝ => Real.arcsin (Real.sin (2 * Real.pi * θ))) θ :=
      ContDiffAt.comp (g := Real.arcsin) θ (Real.contDiffAt_arcsin hne2 hne1) h1
    exact contDiffAt_const.mul h2
  set h : ℝ → ℝ := fun s => max 0 (min 1 (min (16 * s - 1) (15 - 16 * s))) with hh
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hh1 : ∀ s : ℝ, 1 / 8 ≤ s → s ≤ 7 / 8 → h s = 1 := by
    intro s h1 h2
    simp only [hh]
    rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]
  have hh0 : ∀ s : ℝ, s < 1 / 16 ∨ 15 / 16 < s → h s = 0 := by
    intro s hs'
    simp only [hh]
    apply max_eq_left
    rcases hs' with h1 | h1
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
  set Y : ℝ × ℝ → (Fin 2 → ℝ) := fun q =>
    T q.1 • Pi.single 0 1 + (8 * q.2 - 4) • Pi.single 1 1 with hY
  have hY0 : ∀ q, Y q 0 = T q.1 := fun q => by simp [hY]
  have hY1 : ∀ q, Y q 1 = 8 * q.2 - 4 := fun q => by simp [hY]
  have hYc : Continuous Y := by
    rw [hY]
    exact ((hTc.comp continuous_fst).smul continuous_const).add
      ((continuous_const.mul continuous_snd |>.sub continuous_const).smul continuous_const)
  have hYper : ∀ θ s, Y (θ + 1, s) = Y (θ, s) := fun θ s => by simp only [hY, hTper]
  have hYe : ∀ y : Fin 2 → ℝ, |y 0| ≤ 2 → Y (y 0 / 8, (y 1 + 4) / 8) = y := by
    intro y hy
    funext i
    fin_cases i
    · simp [hY, hTid _ hy]
    · simp [hY]; ring
  set V₀ : Set (Fin 2 → ℝ) := (N \ S) ∩ {y | y 0 ^ 2 + y 1 ^ 2 < (1 + η) ^ 2 ∧ -η < y 1} ∩
    {y | |y 0| < 2 ∧ |y 1| < 3} with hV₀
  have hV₀o : IsOpen V₀ := by
    refine ((hNo.sdiff hS_closed).inter ?_).inter ?_
    · exact (isOpen_lt hnrm continuous_const).inter (isOpen_lt continuous_const (continuous_apply 1))
    · exact (isOpen_lt (continuous_apply 0).abs continuous_const).inter
        (isOpen_lt (continuous_apply 1).abs continuous_const)
  have hV₀K : V₀ ⊆ K := fun y hy => ⟨hy.1.2.1.le, hy.1.2.2.le⟩
  have hbandV₀ : whitneyBand (3 * r / 8) ⊆ V₀ := by
    intro y hy
    obtain ⟨h0, h1, h2, h3⟩ := hhalf1 y hy.1
    refine ⟨⟨⟨hN (hband_mono _ r (by positivity) (by linarith) hy), ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · rintro ⟨hS1, hS2⟩
      rcases hy.2 with h | h
      · rw [hs] at hS1; linarith
      · have : (1 - s) ^ 2 < (1 - 3 * r / 8) ^ 2 :=
          pow_lt_pow_left₀ (by rw [hs]; linarith) hs1.le two_ne_zero
        linarith
    · exact h3.trans_lt (one_lt_pow₀ (by linarith) two_ne_zero)
    · linarith
    · linarith
    · rw [abs_lt]; constructor <;> linarith
  obtain ⟨δ, hδ, hδV⟩ := (hband_cpt (3 * r / 8)).exists_cthickening_subset_open hV₀o hbandV₀
  set Pb : Set (Fin 2 → ℝ) := Metric.cthickening δ (whitneyBand (3 * r / 8)) with hPb
  set Fam : ℝ → ℝ → M := fun θ s => G (ρ (h s • Y (θ, s))) with hFam
  have hFamc : Continuous (Function.uncurry Fam) := by
    have h1 : Continuous (fun q : ℝ × ℝ => ρ (h q.2 • Y q)) :=
      hρc.comp ((hhc.comp continuous_snd).smul hYc)
    exact hGc.comp_continuous h1 (fun q => hKW (hρK _))
  have hFamper : ∀ θ s, Fam (θ + 1) s = Fam θ s := fun θ s => by simp only [hFam, hYper]
  have hFamlev : ∀ θ s, f (Fam θ s) = c := fun θ s => hGlev _ (hKW (hρK _))
  set U₁ : Set (ℝ × ℝ) := {q | q.2 < 1 / 16 ∨ 15 / 16 < q.2} with hU₁
  set U₂ : Set (ℝ × ℝ) := {q | 1 / 8 < q.2 ∧ q.2 < 7 / 8 ∧ Y q ∈ V₀} with hU₂
  have hU₁o : IsOpen U₁ :=
    (isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd)
  have hU₂o : IsOpen U₂ :=
    (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter (hV₀o.preimage hYc))
  have hFamU₁ : ∀ q ∈ U₁, Function.uncurry Fam q = G (ρ 0) := by
    intro q hq
    change G (ρ (h q.2 • Y q)) = G (ρ 0)
    rw [hh0 q.2 hq, zero_smul]
  have hFamU₂ : ∀ q ∈ U₂, Function.uncurry Fam q = ψ₀ (Y q) := by
    intro q hq
    change G (ρ (h q.2 • Y q)) = ψ₀ (Y q)
    rw [hh1 q.2 (by linarith [hq.1]) (by linarith [hq.2.1]), one_smul, hρid _ (hV₀K hq.2.2)]
    exact hGψ _ hq.2.2.1.1.2
  have hYsm : ContDiffOn ℝ ∞ Y U₂ := by
    intro q hq
    have hT2 : |T q.1| < 2 := by rw [← hY0]; exact hq.2.2.2.1
    have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => T q.1) q :=
      ContDiffAt.comp (g := T) q (hTsm _ hT2) contDiffAt_fst
    have h2 : ContDiffAt ℝ ∞ Y q := by
      rw [hY]
      exact (h1.smul contDiffAt_const).add
        (((contDiffAt_const.mul contDiffAt_snd).sub contDiffAt_const).smul contDiffAt_const)
    exact h2.contDiffWithinAt
  have hFamsm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry Fam) (U₁ ∪ U₂) := by
    have hA1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry Fam) U₁ :=
      contMDiffOn_const.congr hFamU₁
    have hA2 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry Fam) U₂ := by
      refine ContMDiffOn.congr ?_ hFamU₂
      exact hψ₀.comp hYsm.contMDiffOn (fun q hq => hq.2.2.1.1.1)
    intro q hq
    rcases hq with hq | hq
    · exact ((hA1.contMDiffAt (hU₁o.mem_nhds hq))).contMDiffWithinAt
    · exact ((hA2.contMDiffAt (hU₂o.mem_nhds hq))).contMDiffWithinAt
  set P : Set (ℝ × ℝ) := {q | q.2 ≤ 0 ∨ 1 ≤ q.2} ∪ Y ⁻¹' Pb with hP
  have hPc : IsClosed P :=
    ((isClosed_le continuous_snd continuous_const).union
      (isClosed_le continuous_const continuous_snd)).union
      (Metric.isClosed_cthickening.preimage hYc)
  have hPU : P ⊆ U₁ ∪ U₂ := by
    rintro q (hq | hq)
    · left
      rcases hq with hq | hq
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · right
      have hq' := hδV hq
      have h3 := hq'.2.2
      rw [hY1, abs_lt] at h3
      exact ⟨by linarith [h3.1], by linarith [h3.2], hq'⟩
  have hUper : ∀ θ s, (θ, s) ∈ U₁ ∪ U₂ ↔ (θ + 1, s) ∈ U₁ ∪ U₂ := by
    intro θ s
    simp only [hU₁, hU₂, mem_union, mem_ofPred_eq, hYper]
  have hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P := by
    intro θ s
    simp only [hP, mem_union, mem_ofPred_eq, mem_preimage, hYper]
  have hPs : ∀ θ s, s ∉ Ioo (0 : ℝ) 1 → (θ, s) ∈ P := by
    intro θ s hs'
    left
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs'
    exact hs'
  have hΩc : ∀ x : M, f x = c → x ∈ D.regularFlowDomain c := by
    have hcIoo : c ∈ Ioo a b := ⟨by linarith [hcκ.1], by linarith [hcκ.2]⟩
    intro x hx
    refine ⟨hx ▸ hcIoo, fun s hs p hp hmem => ?_⟩
    rw [hx, sub_self, uIcc_self, mem_singleton_iff] at hs
    rw [hs, flow_zero] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy' : morseNorm n y ≤ (D.chart p hp).r₀ := hy
    have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) (D.chart p hp).R' :=
      mem_ball_of_morseNorm_lt (hy'.trans_lt (D.r₀_lt_R' p hp))
    have hcont : ContinuousAt (fun t : ℝ => f ((D.chart p hp).χ (t • y))) 1 := by
      have h1 : ContinuousAt (fun t : ℝ => t • y) 1 :=
        (continuous_id.smul continuous_const).continuousAt
      have h2 : ContinuousAt (D.chart p hp).χ ((1 : ℝ) • y) := by
        rw [one_smul]; exact (D.chart p hp).χ.continuousAt ((D.chart p hp).hball hyball)
      exact hfc.continuousAt.comp (ContinuousAt.comp (f := fun t : ℝ => t • y) h2 h1)
    have h1c : f ((D.chart p hp).χ ((1 : ℝ) • y)) = c := by rw [one_smul]; exact hx
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ),
        f ((D.chart p hp).χ (t • y)) ∈ Ioo (c - κ) (c + κ) ∧ t ∈ Ioo 0 1 := by
      refine Filter.Eventually.and ?_ (Ioo_mem_nhdsLT one_pos)
      exact nhdsWithin_le_nhds (hcont.eventually
        (Ioo_mem_nhds
          (by change c - κ < f ((D.chart p hp).χ ((1 : ℝ) • y)); rw [h1c]; linarith)
          (by change f ((D.chart p hp).χ ((1 : ℝ) • y)) < c + κ; rw [h1c]; linarith)))
    obtain ⟨t, ht1, ht2⟩ := hev.exists
    apply hU _ (Ioo_subset_Icc_self ht1) p hp
    refine ⟨t • y, ?_, rfl⟩
    change morseNorm n (t • y) < (D.chart p hp).r₀
    rw [ModelField.morseNorm_smul, abs_of_pos ht2.1]
    have hr₀ := (D.chart p hp).hr₀
    calc t * morseNorm n y ≤ t * (D.chart p hp).r₀ := mul_le_mul_of_nonneg_left hy' ht2.1.le
      _ < (D.chart p hp).r₀ := mul_lt_of_lt_one_left hr₀ ht2.2
  set Kc : Set (Fin 2 → ℝ) :=
    whitneyHalf ∩ {y | 3 * r / 8 ≤ y 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ (1 - 3 * r / 8) ^ 2} with hKc
  have hKc_cpt : IsCompact Kc :=
    hhalf_cpt.inter_right ((isClosed_le continuous_const (continuous_apply 1)).inter
      (isClosed_le hnrm continuous_const))
  have hKc4 : ∀ y ∈ Kc, y ∉ whitneyBand (r / 4) := by
    rintro y ⟨-, h1, h2⟩ ⟨-, h | h⟩
    · linarith
    · have ha : 0 < 1 - 3 * r / 8 := by linarith
      have hb : 1 - 3 * r / 8 < 1 - r / 4 := by linarith
      have : (1 - 3 * r / 8) ^ 2 < (1 - r / 4) ^ 2 := pow_lt_pow_left₀ hb ha.le two_ne_zero
      linarith
  set A : Set M := F '' Kc with hA
  have hA_closed : IsClosed A :=
    (hKc_cpt.image_of_continuousOn (hF.mono (fun y hy => hy.1))).isClosed
  set O' : Set (M × M) := (((f ⁻¹' {c})ᶜ ×ˢ univ) ∪ (univ ×ˢ D.regularFlowDomain c)) ∩
    ((Aᶜ ×ˢ univ) ∪ (univ ×ˢ (D.π c ⁻¹' O))) with hO'
  have hO'o : IsOpen O' := by
    refine IsOpen.inter (IsOpen.union ?_ ?_) (IsOpen.union ?_ ?_)
    · exact ((isClosed_singleton.preimage hfc).isOpen_compl).prod isOpen_univ
    · exact isOpen_univ.prod (D.isOpen_regularFlowDomain hfc c)
    · exact hA_closed.isOpen_compl.prod isOpen_univ
    · exact isOpen_univ.prod (hO.preimage (D.continuous_π hf c))
  have hdiag : ∀ x, (x, x) ∈ O' := by
    intro x
    refine ⟨?_, ?_⟩
    · by_cases hx : f x = c
      · exact Or.inr ⟨mem_univ _, hΩc x hx⟩
      · exact Or.inl ⟨hx, mem_univ _⟩
    · by_cases hx : x ∈ A
      · right
        refine ⟨mem_univ _, ?_⟩
        obtain ⟨y, hy, rfl⟩ := hx
        change D.π c (F y) ∈ O
        rw [π_eq_self_of_level (hFc y hy.1)]
        exact hFO y hy.1 (hKc4 y hy)
      · exact Or.inl ⟨hx, mem_univ _⟩
  obtain ⟨F', hF'sm, -, hF'P, hF'O⟩ := IndexOnePartner.exists_smooth_approx hFamc hFamper
    (hU₁o.union hU₂o) hUper hFamsm hPc hPper hPU hPs hO'o hdiag
  have hFamE : ∀ y : Fin 2 → ℝ, |y 0| ≤ 2 → |y 1| < 3 → y ∈ K →
      Fam (y 0 / 8) ((y 1 + 4) / 8) = G y := by
    intro y h0 h1 hyK
    rw [abs_lt] at h1
    change G (ρ (h ((y 1 + 4) / 8) • Y (y 0 / 8, (y 1 + 4) / 8))) = G y
    rw [hh1 _ (by linarith [h1.1]) (by linarith [h1.2]), one_smul, hYe y h0, hρid y hyK]
  set ψ₁ : (Fin 2 → ℝ) → M := fun y => D.π c (F' (y 0 / 8) ((y 1 + 4) / 8)) with hψ₁
  set N' : Set (Fin 2 → ℝ) := Metric.thickening δ (whitneyBand (3 * r / 8)) with hN'
  have hN'V : N' ⊆ V₀ := fun y hy => hδV (Metric.thickening_subset_cthickening _ _ hy)
  have hψ₁ψ₀ : ∀ y ∈ N', ψ₁ y = ψ₀ y := by
    intro y hy
    have hy' := hN'V hy
    have hy0 : |y 0| ≤ 2 := hy'.2.1.le
    have hP' : (y 0 / 8, (y 1 + 4) / 8) ∈ P := by
      right
      change Y (y 0 / 8, (y 1 + 4) / 8) ∈ Pb
      rw [hYe y hy0]
      exact Metric.thickening_subset_cthickening _ _ hy
    change D.π c (F' (y 0 / 8) ((y 1 + 4) / 8)) = ψ₀ y
    rw [hF'P _ _ hP', hFamE y hy0 hy'.2.2 (hV₀K hy'), hGψ y hy'.1.1.2]
    exact π_eq_self_of_level (hψ₀c y hy'.1.1.1)
  have he : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : Fin 2 → ℝ => (y 0 / 8, (y 1 + 4) / 8)) := by
    refine ContDiff.contMDiff ?_
    exact ((contDiff_apply ℝ ℝ (0 : Fin 2)).div_const 8).prodMk
      (((contDiff_apply ℝ ℝ (1 : Fin 2)).add contDiff_const).div_const 8)
  refine ⟨univ, N', ψ₁, isOpen_univ, subset_univ _, ?_, ?_, Metric.isOpen_thickening, ?_, ?_,
    hψ₁ψ₀, ?_⟩
  · exact ((D.contMDiff_π hf c).comp (hF'sm.comp he)).contMDiffOn
  · intro y _
    rcases (hF'O (y 0 / 8) ((y 1 + 4) / 8)).1 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (hFamlev _ _) h1
    · exact f_π hf hcIcc h2
  · exact (hband_mono (r / 4) (3 * r / 8) (by positivity) (by linarith)).trans
      (Metric.self_subset_thickening hδ _)
  · exact fun y hy => ⟨(hN'V hy).1.1.1, mem_univ _⟩
  · intro y hy hy4
    by_cases hyK : y ∈ Kc
    · obtain ⟨h0, h1, h2, -⟩ := hhalf1 y hy
      have hE : Fam (y 0 / 8) ((y 1 + 4) / 8) = F y := by
        rw [hFamE y (h2.trans (by norm_num)) (by rw [abs_lt]; constructor <;> linarith)
          (hHK hy), hGF y hy]
      rcases (hF'O (y 0 / 8) ((y 1 + 4) / 8)).2 with ⟨h3, -⟩ | ⟨-, h4⟩
      · exact absurd (hE ▸ mem_image_of_mem F hyK) h3
      · exact h4
    · have hyb : y ∈ whitneyBand (3 * r / 8) := by
        refine ⟨hy, ?_⟩
        by_contra hcon
        push Not at hcon
        exact hyK ⟨hy, hcon.1.le, hcon.2.le⟩
      rw [hψ₁ψ₀ y (Metric.self_subset_thickening hδ _ hyb),
        ← hFψ y (hband_mono _ (r / 2) (by positivity) (by linarith) hyb)]
      exact hFO y hy hy4

theorem exists_whitney_embedding (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {x₁ x₂ : M} {r : ℝ} (hr : 0 < r) (hr4 : r < 1 / 4)
    {N : Set (Fin 2 → ℝ)} {ψ₀ : (Fin 2 → ℝ) → M} (hN : whitneyBand r ⊆ N)
    (hcol : D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ₀) {W₁ N' : Set (Fin 2 → ℝ)}
    {ψ₁ : (Fin 2 → ℝ) → M} (hW₁ : IsOpen W₁) (hHW₁ : whitneyHalf ⊆ W₁)
    (hψ₁ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ₁ W₁) (hψ₁c : ∀ y ∈ W₁, f (ψ₁ y) = c)
    (hN'o : IsOpen N') (hN' : whitneyBand (r / 4) ⊆ N') (hN'N : N' ⊆ N ∩ W₁)
    (hψ₁ψ₀ : ∀ y ∈ N', ψ₁ y = ψ₀ y)
    (havoidL : ℓ + 3 = n → ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 4) →
      ψ₁ y ∉ D.leftSphere q hq ε c)
    (havoidR : ℓ = 2 → ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 4) →
      ψ₁ y ∉ D.rightSphere p hp ε c) :
    ∃ (W₂ N'' : Set (Fin 2 → ℝ)) (ψ : (Fin 2 → ℝ) → M), IsOpen W₂ ∧ whitneyHalf ⊆ W₂ ∧
      ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ W₂ ∧ (∀ y ∈ W₂, f (ψ y) = c) ∧
      IsOpen N'' ∧ whitneyBand (r / 8) ⊆ N'' ∧ N'' ⊆ N ∩ W₂ ∧ (∀ y ∈ N'', ψ y = ψ₀ y) ∧
      (∀ y ∈ whitneyHalf, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ y)) ∧
      InjOn ψ whitneyHalf ∧
      ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 8) →
        ψ y ∉ D.leftSphere q hq ε c ∧ ψ y ∉ D.rightSphere p hp ε c := by
  classical
  have _hNr : whitneyBand r ⊆ N := hN
  have hε : 0 < ε := hv.1
  have hRq : 2 * ε < (D.chart q hq).R ^ 2 := by
    have h1 := (D.hrm q hq).2
    have h2 := D.rm_pos q hq
    have h3 := hv.2.2.2.2.1
    nlinarith
  have hRp : 2 * ε < (D.chart p hp).R ^ 2 := by
    have h1 := (D.hrm p hp).2
    have h2 := D.rm_pos p hp
    have h3 := hv.2.2.2.1
    nlinarith
  set SL := D.leftSphere q hq ε c with hSL
  set SR := D.rightSphere p hp ε c with hSR
  have hSLc : IsClosed SL := (D.isCompact_leftSphere q hq hRq.le c).isClosed
  have hSRc : IsClosed SR := (D.isCompact_rightSphere p hp hRp.le c).isClosed
  have hnc : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have h1c : Continuous (fun y : Fin 2 → ℝ => y 1) := continuous_apply 1
  have hHcl : IsClosed whitneyHalf :=
    (isClosed_le hnc continuous_const).inter (isClosed_le continuous_const h1c)
  have hHc : IsCompact whitneyHalf := by
    refine Metric.isCompact_of_isClosed_isBounded hHcl
      ((Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_)
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    have h0 := sq_nonneg (y 0)
    have h1 := sq_nonneg (y 1)
    have hy1 := hy.1
    rw [Fin.forall_fin_two, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨(sq_le_one_iff_abs_le_one _).1 (by linarith),
      (sq_le_one_iff_abs_le_one _).1 (by linarith)⟩
  have hBcl : ∀ s : ℝ, IsClosed (whitneyBand s) := by
    intro s
    exact hHcl.inter ((isClosed_le h1c continuous_const).union (isClosed_le continuous_const hnc))
  have hBH : ∀ s : ℝ, whitneyBand s ⊆ whitneyHalf := fun s y hy => hy.1
  set Q : Set (Fin 2 → ℝ) := whitneyBand (r / 4) with hQdef
  set K : Set (Fin 2 → ℝ) :=
    whitneyHalf ∩ {y | r / 4 ≤ y 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ (1 - r / 4) ^ 2} with hKdef
  set U : Set (Fin 2 → ℝ) :=
    W₁ ∩ {y | r / 6 < y 1 ∧ y 0 ^ 2 + y 1 ^ 2 < (1 - r / 6) ^ 2} with hUdef
  have hQc : IsCompact Q := hHc.of_isClosed_subset (hBcl _) (hBH _)
  have hKcl : IsClosed K :=
    hHcl.inter ((isClosed_le continuous_const h1c).inter (isClosed_le hnc continuous_const))
  have hKc : IsCompact K := hHc.of_isClosed_subset hKcl inter_subset_left
  have hUo : IsOpen U :=
    hW₁.inter ((isOpen_lt continuous_const h1c).inter (isOpen_lt hnc continuous_const))
  have hKU : K ⊆ U := by
    rintro y ⟨hyH, hy1, hy2⟩
    refine ⟨hHW₁ hyH, by linarith, ?_⟩
    have : (1 - r / 4) ^ 2 < (1 - r / 6) ^ 2 := by nlinarith
    linarith
  have hUW : U ⊆ W₁ := inter_subset_left
  have hHQK : whitneyHalf ⊆ Q ∪ K := by
    intro y hy
    by_cases h : y 1 ≤ r / 4 ∨ (1 - r / 4) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2
    · exact Or.inl ⟨hy, h⟩
    · rw [not_or, not_le, not_le] at h
      exact Or.inr ⟨hy, h.1.le, h.2.le⟩
  have hQW : Q ⊆ W₁ := fun y hy => hHW₁ hy.1
  have hemb : isInjImmersionOn I ψ₁ Q := by
    refine ⟨fun y hy => ?_, fun y hy y' hy' hyy => ?_⟩
    · have hyN' : y ∈ N' := hN' hy
      have hev : ψ₁ =ᶠ[𝓝 y] ψ₀ :=
        Filter.eventually_of_mem (hN'o.mem_nhds hyN') fun z hz => hψ₁ψ₀ z hz
      rw [hev.mfderiv_eq]
      exact (tangentSpaceCast I (ψ₀ y) (ψ₁ y)).injective.comp
        (hcol.immersion y (hN'N hyN').1)
    · have h1 := hψ₁ψ₀ y (hN' hy)
      have h2 := hψ₁ψ₀ y' (hN' hy')
      exact hcol.inj (hN'N (hN' hy)).1 (hN'N (hN' hy')).1 (by rw [← h1, ← h2, hyy])
  set T : Set M := (if ℓ + 4 ≤ n then SL else ∅) ∪ (if 3 ≤ ℓ then SR else ∅) with hTdef
  have hTc : IsClosed T := by
    refine IsClosed.union ?_ ?_
    · split_ifs
      · exact hSLc
      · exact isClosed_empty
    · split_ifs
      · exact hSRc
      · exact isClosed_empty
  have hthinL : IndexOnePartner.isThin I ℓ SL := by
    have h := D.isThin_leftSphere q hq hε hRq c
    rw [hkq, Nat.add_sub_cancel] at h
    exact h
  have hthinR : IndexOnePartner.isThin I (n - ℓ - 1) SR := by
    have h := D.isThin_rightSphere p hp hε hRp c
    rw [hkp] at h
    exact h
  have hthin0 : ∀ d : ℕ, IndexOnePartner.isThin I d (∅ : Set M) := by
    intro d
    refine ⟨Empty, inferInstance, fun _ => ∅, fun i => i.elim, fun i => i.elim,
      fun i => i.elim, ?_⟩
    exact empty_subset _
  have hT : IndexOnePartner.isThin I (n - 4) T := by
    have hA : IndexOnePartner.isThin I (n - 4) (if ℓ + 4 ≤ n then SL else ∅) := by
      split_ifs with h
      · have := IndexOnePartner.isThin_union_of_le (d := n - 4) (by omega) (by omega)
          hthinL hthinL
        rwa [union_self] at this
      · exact hthin0 _
    have hB : IndexOnePartner.isThin I (n - 4) (if 3 ≤ ℓ then SR else ∅) := by
      split_ifs with h
      · have := IndexOnePartner.isThin_union_of_le (d := n - 4) (by omega) (by omega)
          hthinR hthinR
        rwa [union_self] at this
      · exact hthin0 _
    exact IndexOnePartner.isThin_union_of_le le_rfl le_rfl hA hB
  have hd : n - 4 + 3 < n := by omega
  set S₂ : Set M := (if ℓ + 3 = n then SL else ∅) ∪ (if ℓ = 2 then SR else ∅) with hS₂def
  have hS₂c : IsClosed S₂ := by
    refine IsClosed.union ?_ ?_
    · split_ifs
      · exact hSLc
      · exact isClosed_empty
    · split_ifs
      · exact hSRc
      · exact isClosed_empty
  have hS₂sub : S₂ ⊆ SL ∪ SR := by
    refine union_subset_union ?_ ?_
    · split_ifs
      · exact subset_rfl
      · exact empty_subset _
    · split_ifs
      · exact subset_rfl
      · exact empty_subset _
  set K₂ : Set (Fin 2 → ℝ) :=
    whitneyHalf ∩ {y | r / 8 ≤ y 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ (1 - r / 8) ^ 2} with hK₂def
  have hK₂cl : IsClosed K₂ :=
    hHcl.inter ((isClosed_le continuous_const h1c).inter (isClosed_le hnc continuous_const))
  set Kb : Set (Fin 2 → ℝ) := K₂ ∩ whitneyBand (r / 4) with hKbdef
  have hKbcl : IsClosed Kb := hK₂cl.inter (hBcl _)
  set 𝒪 : Set ((Fin 2 → ℝ) × M) :=
    {z | z.1 ∈ K₂ → z.2 ∉ S₂} ∩ {z | z.1 ∈ Kb → z.2 ∉ SL ∪ SR} with h𝒪def
  have h𝒪 : IsOpen 𝒪 := by
    have e1 : {z : (Fin 2 → ℝ) × M | z.1 ∈ K₂ → z.2 ∉ S₂} = (K₂ ×ˢ S₂)ᶜ := by
      ext z
      simp [mem_prod]
    have e2 : {z : (Fin 2 → ℝ) × M | z.1 ∈ Kb → z.2 ∉ SL ∪ SR} = (Kb ×ˢ (SL ∪ SR))ᶜ := by
      ext z
      exact ⟨fun h hz => h hz.1 hz.2, fun h h1 h2 => h ⟨h1, h2⟩⟩
    rw [h𝒪def, e1, e2]
    exact (hK₂cl.prod hS₂c).isOpen_compl.inter (hKbcl.prod (hSLc.union hSRc)).isOpen_compl
  have hKb_avoid : ∀ y ∈ Kb, ψ₁ y ∉ SL ∪ SR := by
    rintro y ⟨⟨hyH, hy1, hy2⟩, hyB⟩
    have hyN' : y ∈ N' := hN' hyB
    have hyN : y ∈ N := (hN'N hyN').1
    rw [hψ₁ψ₀ y hyN']
    rintro (hL | hR)
    · have := (hcol.memA y hyN).1 hL
      linarith
    · have := (hcol.memB y hyN).1 hR
      have : (1 - r / 8) ^ 2 < 1 := by nlinarith
      linarith
  have hgraph : ∀ y ∈ W₁, (y, ψ₁ y) ∈ 𝒪 := by
    intro y _
    refine ⟨fun hyK₂ => ?_, fun hyKb => hKb_avoid y hyKb⟩
    by_cases hyB : y ∈ whitneyBand (r / 4)
    · exact fun h => hKb_avoid y ⟨hyK₂, hyB⟩ (hS₂sub h)
    · rintro (hL | hR)
      · split_ifs at hL with h
        · exact havoidL h y hyK₂.1 hyB hL
        · exact hL
      · split_ifs at hR with h
        · exact havoidR h y hyK₂.1 hyB hR
        · exact hR
  have hreg : ∀ y ∈ W₁, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f (ψ₁ y) := by
    intro y hy hcr
    have hfy : f (ψ₁ y) = c := hψ₁c y hy
    have hpI := D.f_mem_Ioo p hp
    have hqI := D.f_mem_Ioo q hq
    have hstrip : ψ₁ y ∈ f ⁻¹' Icc a b := by
      change f (ψ₁ y) ∈ Icc a b
      rw [hfy]
      exact ⟨by linarith [hpI.1], by linarith [hqI.2]⟩
    have hball : ∀ x hx, ψ₁ y ∉ (D.chart x hx).χ '' {z | morseNorm n z < (D.chart x hx).r₀} := by
      intro x hx
      exact hv.2.2.2.2.2.2 (ψ₁ y) (by rw [hfy]; exact ⟨hc₁.le, hc₂.le⟩) x hx
    have h1 := D.unit (ψ₁ y) hstrip hball
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hcr
    rw [hcr] at h1
    simp at h1
  obtain ⟨ψ, hψs, hψc, hψU, hψ𝒪, hψQK, hψT⟩ :=
    exists_whitney_generic_position h6 hf hW₁ hψ₁ hψ₁c hreg hQc hQW hemb hKc hUo hKU hUW hTc hT hd
      h𝒪 hgraph
  refine ⟨W₁, N' ∩ {y | y 1 < r / 6 ∨ (1 - r / 6) ^ 2 < y 0 ^ 2 + y 1 ^ 2}, ψ, hW₁, hHW₁, hψs,
    hψc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hN'o.inter ((isOpen_lt h1c continuous_const).union (isOpen_lt continuous_const hnc))
  · rintro y ⟨hyH, hy⟩
    have h48 : (1 - r / 4) ^ 2 ≤ (1 - r / 8) ^ 2 := by nlinarith
    have h68 : (1 - r / 6) ^ 2 < (1 - r / 8) ^ 2 := by nlinarith
    refine ⟨hN' ⟨hyH, ?_⟩, ?_⟩
    · rcases hy with hy | hy
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rcases hy with hy | hy
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  · rintro y ⟨hy, _⟩
    exact hN'N hy
  · rintro y ⟨hy, hy'⟩
    have hyU : y ∉ U := by
      rintro ⟨_, h1, h2⟩
      rcases hy' with h | h <;> linarith
    rw [hψU y hyU, hψ₁ψ₀ y hy]
  · intro y hy
    exact hψQK.1 y (hHQK hy)
  · exact hψQK.2.mono hHQK
  · intro y hyH hyB
    have hyB' : ¬ (y 1 ≤ r / 8 ∨ (1 - r / 8) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2) := fun h => hyB ⟨hyH, h⟩
    rw [not_or, not_le, not_le] at hyB'
    have hyK₂ : y ∈ K₂ := ⟨hyH, hyB'.1.le, hyB'.2.le⟩
    have hg := hψ𝒪 y (hHW₁ hyH)
    by_cases hy4 : y ∈ whitneyBand (r / 4)
    · have := hg.2 ⟨hyK₂, hy4⟩
      exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
    · have hy4' : ¬ (y 1 ≤ r / 4 ∨ (1 - r / 4) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2) :=
        fun h => hy4 ⟨hyH, h⟩
      rw [not_or, not_le, not_le] at hy4'
      have hyK : y ∈ K := ⟨hyH, hy4'.1.le, hy4'.2.le⟩
      have hnT := hψT y hyK
      have hnS₂ := hg.1 hyK₂
      refine ⟨fun hL => ?_, fun hR => ?_⟩
      · by_cases h : ℓ + 4 ≤ n
        · exact hnT (Or.inl (by simpa [h] using hL))
        · have h' : ℓ + 3 = n := by omega
          exact hnS₂ (Or.inl (by simpa [h'] using hL))
      · by_cases h : 3 ≤ ℓ
        · exact hnT (Or.inr (by simpa [h] using hR))
        · have h' : ℓ = 2 := by omega
          exact hnS₂ (Or.inr (by simpa [h'] using hR))

theorem whitneyDisc_of_embedding (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ε c : ℝ} (hv : D.sardValid ε p hq hp)
    {x₁ x₂ : M} {r : ℝ} (hr : 0 < r) (hr4 : r < 1 / 4) {N : Set (Fin 2 → ℝ)}
    {ψ₀ : (Fin 2 → ℝ) → M} (hN : whitneyBand r ⊆ N)
    (hcol : D.IsWhitneyCollar c hp hq ε x₁ x₂ N ψ₀) {W₂ N'' : Set (Fin 2 → ℝ)}
    {ψ : (Fin 2 → ℝ) → M} (hW₂ : IsOpen W₂) (hHW₂ : whitneyHalf ⊆ W₂)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) I ∞ ψ W₂) (hψc : ∀ y ∈ W₂, f (ψ y) = c)
    (hN''o : IsOpen N'') (hN'' : whitneyBand (r / 8) ⊆ N'') (hN''N : N'' ⊆ N ∩ W₂)
    (hψψ₀ : ∀ y ∈ N'', ψ y = ψ₀ y)
    (himm : ∀ y ∈ whitneyHalf, Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ y))
    (hinj : InjOn ψ whitneyHalf)
    (havoid : ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 8) →
      ψ y ∉ D.leftSphere q hq ε c ∧ ψ y ∉ D.rightSphere p hp ε c) :
    Nonempty (D.WhitneyDisc c hp hq ε x₁ x₂) := by
  classical
  have _hf := hf
  have _hv := hv
  have _hN := hN
  have _hW₂ := hW₂
  set K : Set (Fin 2 → ℝ) := whitneyHalf \ N'' with hKdef
  have hHc : IsCompact whitneyHalf := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} :=
        isClosed_le (by fun_prop) continuous_const
      have h2 : IsClosed {y : Fin 2 → ℝ | 0 ≤ y 1} := isClosed_le continuous_const (by fun_prop)
      exact h1.inter h2
    · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i
      · simp only [Fin.zero_eta]
        constructor <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      · simp only [Fin.mk_one]
        constructor <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have hKc : IsCompact K := hHc.diff hN''o
  have hψcont : ContinuousOn ψ W₂ := hψ.continuousOn
  have hψKc : IsClosed (ψ '' K) :=
    (hKc.image_of_continuousOn (hψcont.mono (fun y hy => hHW₂ hy.1))).isClosed
  have hoff : ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 8) →
      y 0 ^ 2 + y 1 ^ 2 < 1 ∧ 0 < y 1 := by
    intro y hy hyb
    have h' : ¬ (y 1 ≤ r / 8 ∨ (1 - r / 8) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2) := fun h => hyb ⟨hy, h⟩
    simp only [not_or, not_le] at h'
    obtain ⟨ha, hb⟩ := h'
    refine ⟨?_, by linarith⟩
    have : (1 - r / 8) ^ 2 ≤ 1 := by nlinarith
    linarith
  set A : Set (Fin 2 → ℝ) := N'' ∩ ψ ⁻¹' (ψ '' K)ᶜ with hAdef
  set B : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 < 1 ∧ 0 < y 1} with hBdef
  have hAo : IsOpen A :=
    (hψcont.mono (fun y hy => (hN''N hy).2)).isOpen_inter_preimage hN''o hψKc.isOpen_compl
  have hBo : IsOpen B := by
    have h1 : IsOpen {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have h2 : IsOpen {y : Fin 2 → ℝ | 0 < y 1} := isOpen_lt continuous_const (by fun_prop)
    exact h1.inter h2
  have hBH : B ⊆ whitneyHalf := fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hAN : A ⊆ N'' := fun y hy => hy.1
  set W : Set (Fin 2 → ℝ) := A ∪ B with hWdef
  have hWo : IsOpen W := hAo.union hBo
  have hHW : whitneyHalf ⊆ W := by
    intro y hy
    by_cases hyN : y ∈ N''
    · left
      refine ⟨hyN, ?_⟩
      rintro ⟨y', hy'K, hyy'⟩
      have : y' = y := hinj hy'K.1 hy hyy'
      exact hy'K.2 (this ▸ hyN)
    · right
      exact hoff y hy (fun hb => hyN (hN'' hb))
  have hWW₂ : W ⊆ W₂ := by
    rintro y (hy | hy)
    · exact (hN''N hy.1).2
    · exact hHW₂ (hBH hy)
  have hWoff : ∀ y ∈ W, y ∉ N'' → y ∈ B := by
    rintro y (hy | hy) hyN
    · exact absurd hy.1 hyN
    · exact hy
  have hWoffBand : ∀ y ∈ W, y ∉ N'' → y ∉ whitneyBand (r / 8) :=
    fun y _ hyN hb => hyN (hN'' hb)
  have hev : ∀ y ∈ N'', ψ =ᶠ[𝓝 y] ψ₀ := fun y hy =>
    Filter.eventually_of_mem (hN''o.mem_nhds hy) hψψ₀
  have hcorner : ∀ σ : ℝ, σ ^ 2 = 1 → ψ ![σ, 0] = ψ₀ ![σ, 0] := by
    intro σ hσ
    apply hψψ₀
    apply hN''
    refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
    · simp [hσ]
    · simp
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      positivity
  refine ⟨{
    W := W
    isOpen_W := hWo
    half_subset := hHW
    ψ := ψ
    smooth := hψ.mono hWW₂
    immersion := ?_
    inj := ?_
    level := fun y hy => hψc y (hWW₂ hy)
    memA := ?_
    memB := ?_
    transA := ?_
    transB := ?_
    corner₁ := ?_
    corner₂ := ?_ }⟩
  · intro y hy
    by_cases hyN : y ∈ N''
    · have hEq := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, Fin 2 → ℝ)) (I' := I) (hev y hyN)
      intro u v huv
      rw [hEq] at huv
      exact hcol.immersion y (hN''N hyN).1 huv
    · exact himm y (hBH (hWoff y hy hyN))
  · intro y hy y' hy' hyy'
    by_cases hyH : y ∈ whitneyHalf
    · by_cases hy'H : y' ∈ whitneyHalf
      · exact hinj hyH hy'H hyy'
      · have hy'N : y' ∈ N'' := by
          by_contra hy'N
          exact hy'H (hBH (hWoff y' hy' hy'N))
        by_cases hyN : y ∈ N''
        · have := hcol.inj (hN''N hyN).1 (hN''N hy'N).1
            (by rw [← hψψ₀ y hyN, ← hψψ₀ y' hy'N]; exact hyy')
          exact this
        · rcases hy' with hy'A | hy'B
          · exact absurd ⟨y, ⟨hyH, hyN⟩, hyy'⟩ hy'A.2
          · exact absurd (hBH hy'B) hy'H
    · have hyN : y ∈ N'' := by
        by_contra hyN
        exact hyH (hBH (hWoff y hy hyN))
      by_cases hy'N : y' ∈ N''
      · exact hcol.inj (hN''N hyN).1 (hN''N hy'N).1
          (by rw [← hψψ₀ y hyN, ← hψψ₀ y' hy'N]; exact hyy')
      · have hy'H : y' ∈ whitneyHalf := hBH (hWoff y' hy' hy'N)
        rcases hy with hyA | hyB
        · exact absurd ⟨y', ⟨hy'H, hy'N⟩, hyy'.symm⟩ hyA.2
        · exact absurd (hBH hyB) hyH
  · intro y hy
    by_cases hyN : y ∈ N''
    · rw [hψψ₀ y hyN]
      exact hcol.memA y (hN''N hyN).1
    · have hyB := hWoff y hy hyN
      have hav := havoid y (hBH hyB) (hWoffBand y hy hyN)
      constructor
      · intro h; exact absurd h hav.1
      · intro h; exact absurd h (ne_of_gt hyB.2)
  · intro y hy
    by_cases hyN : y ∈ N''
    · rw [hψψ₀ y hyN]
      exact hcol.memB y (hN''N hyN).1
    · have hyB := hWoff y hy hyN
      have hav := havoid y (hBH hyB) (hWoffBand y hy hyN)
      constructor
      · intro h; exact absurd h hav.2
      · intro h; exact absurd h (ne_of_lt hyB.1)
  · intro y hy hy1
    have hyN : y ∈ N'' := by
      by_contra hyN
      have := (hWoff y hy hyN).2
      linarith
    have hEq : (fun y => D.leftCoord q hq ε (ψ y)) =ᶠ[𝓝 y]
        (fun y => D.leftCoord q hq ε (ψ₀ y)) :=
      (hev y hyN).mono (fun z hz => by simp only [hz])
    rw [hEq.fderiv_eq]
    exact hcol.transA y (hN''N hyN).1 hy1
  · intro y hy hy1
    have hyN : y ∈ N'' := by
      by_contra hyN
      have := (hWoff y hy hyN).1
      linarith
    have hEq : (fun y => D.rightCoord p hp ε (ψ y)) =ᶠ[𝓝 y]
        (fun y => D.rightCoord p hp ε (ψ₀ y)) :=
      (hev y hyN).mono (fun z hz => by simp only [hz])
    rw [hEq.fderiv_eq]
    exact hcol.transB y (hN''N hyN).1 hy1
  · rw [hcorner (-1) (by norm_num)]
    exact hcol.corner₁
  · rw [hcorner 1 (by norm_num)]
    exact hcol.corner₂

theorem portPrivate_bdd04f55_exists_continuous_kernel_frame : ∀ {d r' s : ℕ} (K : Set (Fin d → ℝ)), IsCompact K → Convex ℝ K →
    ∀ (B : (Fin d → ℝ) → Matrix (Fin r') (Fin (n - 1)) ℝ), ContinuousOn B K →
    (∀ y ∈ K, Function.Surjective (B y).mulVec) → s + r' = n - 1 →
    ∃ F : (Fin d → ℝ) → Fin s → (Fin (n - 1) → ℝ), ContinuousOn F K ∧
      ∀ y ∈ K, LinearIndependent ℝ (F y) ∧ ∀ i, (B y).mulVec (F y i) = 0 := by
  classical
  intro d r' s K hK hKc B hB hsurj hsN
  have hGpd : ∀ y ∈ K, (B y * (B y).transpose).PosDef := by
    intro y hy
    have h := Matrix.PosDef.mul_conjTranspose_self (B y) ?_
    · rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    · intro x x' hxx'
      have hsub : Matrix.vecMul (x - x') (B y) = 0 := by
        rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hxx'
      obtain ⟨v, hv⟩ := hsurj y hy (x - x')
      have h0 : (x - x') ⬝ᵥ (x - x') = 0 := by
        calc (x - x') ⬝ᵥ (x - x') = (x - x') ⬝ᵥ (B y).mulVec v := by rw [hv]
          _ = Matrix.vecMul (x - x') (B y) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
          _ = 0 := by rw [hsub, zero_dotProduct]
      exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h0)
  have hGdet : ∀ y ∈ K, (B y * (B y).transpose).det ≠ 0 := fun y hy => (hGpd y hy).det_pos.ne'
  let Φ : Matrix (Fin r') (Fin (n - 1)) ℝ → Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun X =>
    1 - X.transpose * (((X * X.transpose).det)⁻¹ • (X * X.transpose).adjugate) * X
  have hΦinv : ∀ X : Matrix (Fin r') (Fin (n - 1)) ℝ, (X * X.transpose).det ≠ 0 →
      Φ X = 1 - X.transpose * (X * X.transpose)⁻¹ * X := by
    intro X hX
    simp only [Φ, Matrix.inv_def, Ring.inverse_eq_inv']
  have hΦc : ContinuousOn Φ {X | (X * X.transpose).det ≠ 0} := by
    have hΨ : Continuous (fun p : ℝ × Matrix (Fin r') (Fin (n - 1)) ℝ =>
        1 - p.2.transpose * (p.1 • (p.2 * p.2.transpose).adjugate) * p.2) := by
      refine continuous_const.sub ?_
      refine Continuous.matrix_mul (Continuous.matrix_mul continuous_snd.matrix_transpose ?_)
        continuous_snd
      exact continuous_fst.smul (Continuous.matrix_adjugate
        (continuous_snd.matrix_mul continuous_snd.matrix_transpose))
    have hc : ContinuousOn (fun X : Matrix (Fin r') (Fin (n - 1)) ℝ => ((X * X.transpose).det)⁻¹)
        {X | (X * X.transpose).det ≠ 0} :=
      ((continuous_id.matrix_mul continuous_id.matrix_transpose).matrix_det).continuousOn.inv₀
        fun X hX => hX
    refine (hΨ.comp_continuousOn (hc.prodMk continuousOn_id)).congr fun X _ => ?_
    simp only [Φ, Function.comp_apply, id]
  let P : (Fin d → ℝ) → (Fin (n - 1) → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) := fun y =>
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Φ (B y)))
  have hPapp : ∀ y v, P y v = (Φ (B y)).mulVec v := fun y v => rfl
  have hPc : ContinuousOn P K := by
    rw [continuousOn_clm_apply]
    intro v
    simp only [hPapp]
    have h1 : ContinuousOn (fun y => Φ (B y)) K := hΦc.comp hB fun y hy => hGdet y hy
    exact (continuous_id.matrix_mulVec continuous_const).comp_continuousOn h1
  have hQ : ∀ y ∈ K, B y * Φ (B y) = 0 := by
    intro y hy
    rw [hΦinv _ (hGdet y hy), Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hGdet y hy)),
      Matrix.one_mul, sub_self]
  have hPidem : ∀ y ∈ K, (P y).comp (P y) = P y := by
    intro y hy
    ext1 v
    rw [ContinuousLinearMap.comp_apply, hPapp, hPapp, Matrix.mulVec_mulVec]
    congr 1
    have h := hQ y hy
    nth_rewrite 1 [hΦinv _ (hGdet y hy)]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (B y), h, Matrix.mul_zero, sub_zero]
  have hrange : ∀ y ∈ K, LinearMap.range (P y : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ)) =
      LinearMap.ker (Matrix.mulVecLin (B y)) := by
    intro y hy
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      change (B y).mulVec ((Φ (B y)).mulVec u) = 0
      rw [Matrix.mulVec_mulVec, hQ y hy, Matrix.zero_mulVec]
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      refine ⟨v, ?_⟩
      change (Φ (B y)).mulVec v = v
      rw [hΦinv _ (hGdet y hy), Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, sub_zero]
  have hrank : ∀ y ∈ K,
      Module.finrank ℝ (LinearMap.range (P y : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ))) = s := by
    intro y hy
    rw [hrange y hy]
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (B y))
    have htop : LinearMap.range (Matrix.mulVecLin (B y)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact hsurj y hy
    rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  obtain ⟨F, hFc, hF⟩ := exists_frame_of_projections hK hKc P hPc hPidem hrank
  refine ⟨F, hFc, fun y hy => ⟨(hF y hy).1, fun i => ?_⟩⟩
  have h := (hF y hy).2 i
  rw [hrange y hy, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
  exact h

theorem portPrivate_bdd04f55_linearIndependent_finCons_of_kernel_and_orthogonal : ∀ {N m' r : ℕ} (hN : N = m' + 1) (A : Matrix (Fin r) (Fin (n - 1)) ℝ)
    (x h : Fin (n - 1) → ℝ) (F : Fin m' → Fin (n - 1) → ℝ) (S : Fin N → Fin (n - 1) → ℝ),
    (∀ i : Fin N, S i = if hi : (i : ℕ) = 0 then h else F ⟨(i : ℕ) - 1, by omega⟩) →
    A.mulVec x ≠ 0 → A.mulVec h = 0 → (∀ i, A.mulVec (F i) = 0) → h ≠ 0 →
    (∀ i, h ⬝ᵥ F i = 0) → LinearIndependent ℝ F →
    LinearIndependent ℝ (Fin.cons x S : Fin (N + 1) → Fin (n - 1) → ℝ) := by
  classical
  intro N m' r hN A x h F S hS hAx hAh hAF hh0 hhF hF
  subst hN
  have hS' : S = Fin.cons h F := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hS]; simp
    · rw [hS]
      simp only [Fin.val_succ, Nat.add_one_ne_zero, ↓reduceDIte, Fin.cons_succ,
        Nat.add_sub_cancel]
  rw [hS', linearIndependent_finCons, linearIndependent_finCons]
  let dl : (Fin (n - 1) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => h ⬝ᵥ v
      map_add' := dotProduct_add _
      map_smul' := fun t v => by simp [dotProduct_smul] }
  refine ⟨⟨hF, fun hmem => ?_⟩, fun hmem => ?_⟩
  · have hle : Submodule.span ℝ (Set.range F) ≤ LinearMap.ker dl := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hhF i
    exact hh0 (dotProduct_self_eq_zero.1 (hle hmem))
  · have hle : Submodule.span ℝ (Set.range (Fin.cons h F : Fin (m' + 1) → Fin (n - 1) → ℝ)) ≤
        LinearMap.ker (Matrix.mulVecLin A) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hAh
      · simpa using hAF j
    exact hAx (by simpa using hle hmem)

theorem portPrivate_bdd04f55_linearIndependent_of_orthogonal_cons : ∀ {d N m' : ℕ} (hN : N = m' + 1) (h : Fin d → ℝ) (F : Fin m' → Fin d → ℝ)
    (S : Fin N → Fin d → ℝ),
    (∀ i : Fin N, S i = if hi : (i : ℕ) = 0 then h else F ⟨(i : ℕ) - 1, by omega⟩) →
    h ≠ 0 → (∀ i, h ⬝ᵥ F i = 0) → LinearIndependent ℝ F → LinearIndependent ℝ S := by
  classical
  intro d N m' hN h F S hS hh0 hhF hF
  subst hN
  have hS' : S = Fin.cons h F := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hS]; simp
    · rw [hS]
      simp only [Fin.val_succ, Nat.add_one_ne_zero, ↓reduceDIte, Fin.cons_succ,
        Nat.add_sub_cancel]
  rw [hS', linearIndependent_finCons]
  let dl : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => h ⬝ᵥ v
      map_add' := dotProduct_add _
      map_smul' := fun t v => by simp [dotProduct_smul] }
  refine ⟨hF, fun hmem => ?_⟩
  have hle : Submodule.span ℝ (Set.range F) ≤ LinearMap.ker dl := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hhF i
  exact hh0 (dotProduct_self_eq_zero.1 (hle hmem))

theorem portPrivate_bdd04f55_sign_eq_of_continuousOn_nonzero : ∀ (φ : ℝ → ℝ) (a' b' : ℝ), a' ≤ b' → ContinuousOn φ (Icc a' b') →
    (∀ t ∈ Icc a' b', φ t ≠ 0) → SignType.sign (φ a') = SignType.sign (φ b') := by
  classical
  intro φ a' b' hab hc h0
  have ha := h0 a' ⟨le_rfl, hab⟩
  have hb := h0 b' ⟨hab, le_rfl⟩
  rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
  · rw [sign_neg ha', sign_neg hb']
  · obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc hab hc ⟨ha'.le, hb'.le⟩
    exact absurd hφt (h0 t ht)
  · obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc' hab hc ⟨hb'.le, ha'.le⟩
    exact absurd hφt (h0 t ht)
  · rw [sign_pos ha', sign_pos hb']

theorem portPrivate_bdd04f55_sign_blockMat_mul_kernel_complement {ℓ k : ℕ} (hℓn : ℓ ≤ n - 1)
    (hk : k = ℓ) (A : Matrix (Fin k) (Fin (n - 1)) ℝ)
    (SL : Fin ℓ → Fin (n - 1) → ℝ) (SR : Fin (n - 1 - ℓ) → Fin (n - 1) → ℝ)
    (hSR : LinearIndependent ℝ SR) (hASR : ∀ i, A.mulVec (SR i) = 0) :
    let Nmat : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
      Matrix.of fun a j => if h : (a : ℕ) < ℓ then A (Fin.cast hk.symm ⟨a, h⟩) j else
        SR ⟨(a : ℕ) - ℓ, by omega⟩ j
    let Qm : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
      Matrix.of fun a b => A.mulVec (SL b) (Fin.cast hk.symm a)
    SignType.sign (blockMat SL SR).det * SignType.sign Nmat.det = SignType.sign Qm.det := by
  classical
  intro Nmat Qm
  let e' : Fin (n - 1) ≃ Fin ℓ ⊕ Fin (n - 1 - ℓ) :=
    (finCongr (by omega : n - 1 = ℓ + (n - 1 - ℓ))).trans finSumFinEquiv.symm
  let Gm : Matrix (Fin (n - 1 - ℓ)) (Fin (n - 1 - ℓ)) ℝ := Matrix.of fun a b => SR a ⬝ᵥ SR b
  let Cm : Matrix (Fin (n - 1 - ℓ)) (Fin ℓ) ℝ := Matrix.of fun a b => SR a ⬝ᵥ SL b
  have hre : Matrix.reindex e' e' (Nmat * blockMat (SL) (SR)) =
      Matrix.fromBlocks (Qm) 0 Cm Gm := by
    have hNr1 : ∀ (i : Fin (n - 1)) (a : Fin ℓ), (i : ℕ) = a →
        (fun k => Nmat i k) = A (Fin.cast hk.symm a) := by
      intro i a hia
      funext k
      have hi : (i : ℕ) < ℓ := by omega
      simp only [Nmat, Matrix.of_apply, hi, ↓reduceDIte]
      congr 2
      exact Fin.ext hia
    have hNr2 : ∀ (i : Fin (n - 1)) (a : Fin (n - 1 - ℓ)), (i : ℕ) = ℓ + a →
        (fun k => Nmat i k) = SR a := by
      intro i a hia
      funext k
      have hi : ¬ (i : ℕ) < ℓ := by omega
      simp only [Nmat, Matrix.of_apply, hi, ↓reduceDIte]
      have hb : (⟨(i : ℕ) - ℓ, by omega⟩ : Fin (n - 1 - ℓ)) = a := Fin.ext (by simp only; omega)
      rw [hb]
    have hXc1 : ∀ (j : Fin (n - 1)) (b : Fin ℓ), (j : ℕ) = b →
        (fun k => blockMat (SL) (SR) k j) = SL b := by
      intro j b hjb
      funext k
      have hj : (j : ℕ) < ℓ := by omega
      simp only [blockMat, Matrix.of_apply, hj, ↓reduceDIte]
      have hb : (⟨(j : ℕ), hj⟩ : Fin ℓ) = b := Fin.ext hjb
      rw [hb]
    have hXc2 : ∀ (j : Fin (n - 1)) (b : Fin (n - 1 - ℓ)), (j : ℕ) = ℓ + b →
        (fun k => blockMat (SL) (SR) k j) = SR b := by
      intro j b hjb
      funext k
      have hj : ¬ (j : ℕ) < ℓ := by omega
      simp only [blockMat, Matrix.of_apply, hj, ↓reduceDIte]
      have hb : (⟨(j : ℕ) - ℓ, by omega⟩ : Fin (n - 1 - ℓ)) = b := Fin.ext (by simp only; omega)
      rw [hb]
    have hmul : ∀ i j, (Nmat * blockMat (SL) (SR)) i j =
        (fun k => Nmat i k) ⬝ᵥ (fun k => blockMat (SL) (SR) k j) := fun i j => rfl
    have hv1 : ∀ a : Fin ℓ, ((e'.symm (Sum.inl a) : Fin (n - 1)) : ℕ) = a := fun a => by simp [e']
    have hv2 : ∀ a : Fin (n - 1 - ℓ), ((e'.symm (Sum.inr a) : Fin (n - 1)) : ℕ) = ℓ + a :=
      fun a => by simp [e']
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hmul, hNr1 _ a (hv1 a), hXc1 _ b (hv1 b),
        Matrix.fromBlocks_apply₁₁]
      rfl
    · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hmul, hNr1 _ a (hv1 a), hXc2 _ b (hv2 b),
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      exact congrFun (hASR b) _
    · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hmul, hNr2 _ a (hv2 a), hXc1 _ b (hv1 b),
        Matrix.fromBlocks_apply₂₁]
      rfl
    · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hmul, hNr2 _ a (hv2 a), hXc2 _ b (hv2 b),
        Matrix.fromBlocks_apply₂₂]
      rfl
  have hGm : 0 < Gm.det := by
    let Sm : Matrix (Fin (n - 1)) (Fin (n - 1 - ℓ)) ℝ := Matrix.of fun k b => SR b k
    have hinj : Function.Injective Sm.mulVec := by
      intro c₁ c₂ h
      have h' : ∑ b, (c₁ - c₂) b • SR b = 0 := by
        funext k
        have := congrFun h k
        simp only [Sm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, sub_mul,
          Finset.sum_sub_distrib, Pi.zero_apply, mul_comm (c₁ _), mul_comm (c₂ _)]
        rw [this, sub_self]
      funext b
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hSR) _ h' b)
    have hpd := Matrix.PosDef.conjTranspose_mul_self Sm hinj
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpd
    have hG : Sm.transpose * Sm = Gm := by
      ext a b
      simp only [Sm, Gm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct]
    rw [← hG]
    exact hpd.det_pos
  have h1 := congrArg Matrix.det hre
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_mul] at h1
  rw [← sign_mul, mul_comm, h1, sign_mul, sign_pos hGm, mul_one]

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem portPrivate_bdd04f55_mfderiv_comp_eq_zero_of_constant_path (ψ : (Fin 2 → ℝ) → M) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : M → F) (C : F)
    (y : Fin 2 → ℝ) (γ : ℝ → Fin 2 → ℝ) (u : Fin 2 → ℝ),
    MDifferentiableAt I 𝓘(ℝ, F) G (ψ y) → MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I ψ y →
    γ 0 = y → HasDerivAt γ u 0 → (∀ᶠ t in 𝓝 (0 : ℝ), G (ψ (γ t)) = C) →
    mfderiv I 𝓘(ℝ, F) G (ψ y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ y u) = 0 := by
  classical
  intro F _ _ G C y γ u hG hψ hγ0 hγ hC
  subst hγ0
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) γ 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight u) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hγ.hasFDerivAt
  have h2 := (hG.hasMFDerivAt.comp (γ 0) hψ.hasMFDerivAt).comp 0 h1
  have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ((G ∘ ψ) ∘ γ) 0 0 := by
    have : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun _ : ℝ => C) 0 0 := hasMFDerivAt_const _ _
    exact this.congr_of_eventuallyEq (hC.mono fun t ht => ht)
  have h4 := h2.mfderiv.symm.trans h3.mfderiv
  have h5 := congrArg (fun L : ℝ →L[ℝ] F => L 1) h4
  have h6 : ((1 : ℝ →L[ℝ] ℝ).smulRight u) 1 = u := by simp
  calc _ = (mfderiv I 𝓘(ℝ, F) G (ψ (γ 0))) ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) I ψ (γ 0))
        (((1 : ℝ →L[ℝ] ℝ).smulRight u) 1)) := by rw [h6]
    _ = 0 := h5

omit [T2Space M] [I.Boundaryless] in
theorem portPrivate_bdd04f55_continuousOn_mfderiv_apply_tangent_family : ∀ {r : ℕ} (G : M → EuclideanSpace ℝ (Fin r)) (O : Set M), IsOpen O →
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ G O → ∀ {d : ℕ} (S : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → M) (v : (Fin d → ℝ) → Fin n → ℝ), MapsTo φ S O →
    ContinuousOn (fun y => (⟨φ y, v y⟩ : TangentBundle I M)) S →
    ContinuousOn (fun y => mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) G (φ y) (v y)) S := by
  classical
  intro r G O hO hG d S φ v hφ hv
  have h1 := hG.continuousOn_tangentMapWithin (by simp) hO.uniqueMDiffOn
  have h2 : ContinuousOn (fun y => tangentMapWithin I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) G O
      (⟨φ y, v y⟩ : TangentBundle I M)) S :=
    h1.comp hv (fun y hy => hφ hy)
  have h3 : ContinuousOn (fun y => (tangentBundleModelSpaceHomeomorph
      𝓘(ℝ, EuclideanSpace ℝ (Fin r)) (tangentMapWithin I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) G O
      (⟨φ y, v y⟩ : TangentBundle I M))).2) S :=
    continuous_snd.comp_continuousOn
      ((tangentBundleModelSpaceHomeomorph _).continuous.comp_continuousOn h2)
  refine h3.congr fun y hy => ?_
  change _ = ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
      (tangentMapWithin I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) G O
      (⟨φ y, v y⟩ : TangentBundle I M))).2
  rw [tangentMapWithin_eq_tangentMap (hO.uniqueMDiffOn _ (hφ hy))
    ((hG.contMDiffAt (hO.mem_nhds (hφ hy))).mdifferentiableAt (by simp))]
  rfl

theorem whitney_corner_frames (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {w₁ w₂ : Fin (D.chart q hq).k → ℝ} (hw₁ : w₁ ∈ D.sardZeros p hq ε c hp)
    (hw₂ : w₂ ∈ D.sardZeros p hq ε c hp) (hs₁ : D.sardSign p hq ε c hp w₁ = 1)
    (hs₂ : D.sardSign p hq ε c hp w₂ = -1)
    (Wd : D.WhitneyDisc c hp hq ε
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₁)))
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₂))))
    (E : (Fin 2 → ℝ) → Fin (n - 1) → (Fin n → ℝ))
    (hEc : ∀ j, ContinuousOn (fun y => (⟨Wd.ψ y, E y j⟩ : TangentBundle I M)) whitneyHalf)
    (hEf : ∀ y ∈ whitneyHalf, ∀ j, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (E y j) = 0)
    (hEi : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (E y)) :
    ∃ (T : (Fin 2 → ℝ) → Fin 2 → (Fin (n - 1) → ℝ)) (SL : (Fin 2 → ℝ) → Fin ℓ → (Fin (n - 1) → ℝ))
      (SR : (Fin 2 → ℝ) → Fin (n - 1 - ℓ) → (Fin (n - 1) → ℝ)),
      IsWhitneyFrame hℓ (by omega) T SL SR ∧
      (∀ y ∈ whitneyHalf, ∀ i, frameVec E y (T y i) =
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (Pi.single i 1) : Fin n → ℝ)) ∧
      (∀ y ∈ whitneyHalf, y 1 = 0 → ∀ i,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (Wd.ψ y)
          (frameVec E y (SL y i)) = 0) ∧
      ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 → ∀ i,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (Wd.ψ y)
          (frameVec E y (SR y i)) = 0 := by
  classical
  have iCSq : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (D.chart q hq).k)) :=
    IsBoundedSMul.continuousSMul
  have iCSp : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (D.chart p hp).k)) :=
    IsBoundedSMul.continuousSMul
  obtain ⟨hε, -, -, hrmp8, hrmq8, -, hU⟩ := id hv
  have hpab : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hqab : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hac : a ≤ c := by linarith only [hpab.1, hε, hc₁]
  have hcb : c ≤ b := by linarith only [hqab.2, hε, hc₂]
  have hUL : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hU y ⟨by linarith only [hy.1, hc₁], hy.2⟩
  have hUR : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx :=
    fun y hy => hU y ⟨hy.1, by linarith only [hy.2, hc₂]⟩
  have hrmp : 2 * ε < D.rm p hp ^ 2 := by linarith only [hrmp8, hε]
  have hrmq : 2 * ε < D.rm q hq ^ 2 := by linarith only [hrmq8, hε]
  obtain ⟨OL, hOL, hSOL, hLCs, hsubL⟩ := leftCoord_submersion hf D hq hε hrmq hac hc₂.le hUL
  obtain ⟨OR, hOR, hSOR, hRCs, hsubR⟩ := rightCoord_submersion hf D hp hε hrmp hc₁.le hcb hUR
  have hHW : ∀ y ∈ whitneyHalf, y ∈ Wd.W := fun y hy => Wd.half_subset hy
  have hψs : ∀ y ∈ Wd.W, ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) I ∞ Wd.ψ y := fun y hy =>
    Wd.smooth.contMDiffAt (Wd.isOpen_W.mem_nhds hy)
  have hψd : ∀ y ∈ Wd.W, MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y := fun y hy =>
    (hψs y hy).mdifferentiableAt (by simp)
  have hψc : ContinuousOn Wd.ψ whitneyHalf := Wd.smooth.continuousOn.mono Wd.half_subset
  have hreg : ∀ y ∈ Wd.W, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) ≠ 0 := by
    intro y hy h0
    have hfy := Wd.level y hy
    have hu := D.unit (Wd.ψ y) (by simp [hfy, hac, hcb])
      (fun x hx => hU _ ⟨by rw [hfy]; exact hc₁.le, by rw [hfy]; exact hc₂.le⟩ x hx)
    rw [h0] at hu
    simp at hu
  have hspanE : ∀ y ∈ whitneyHalf, ∀ v : Fin n → ℝ, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) v = 0 →
      v ∈ Submodule.span ℝ (Set.range (E y)) := by
    intro y hy v hv
    let φ : (Fin n → ℝ) →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y)
    have hφ0 : φ ≠ 0 := hreg y (hHW y hy)
    have hsurj : LinearMap.range (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) = ⊤ := by
      obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
        by_contra h
        exact hφ0 (ContinuousLinearMap.ext fun u => not_not.1 fun hu => h ⟨u, hu⟩)
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨(r / φ u) • u, ?_⟩
      simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      field_simp
    have hker : Module.finrank ℝ (LinearMap.ker (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ)) = n - 1 := by
      have h := LinearMap.finrank_range_add_finrank_ker (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ)
      rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
      omega
    have hle : Submodule.span ℝ (Set.range (E y)) ≤ LinearMap.ker (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hEf y hy j
    have heq : Submodule.span ℝ (Set.range (E y)) = LinearMap.ker (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) :=
      Submodule.eq_of_le_of_finrank_eq hle
        (by rw [finrank_span_eq_card (hEi y hy), Fintype.card_fin, hker])
    rw [heq]
    exact hv
  have hcoef : ∀ y ∈ whitneyHalf, ∀ v : Fin n → ℝ, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) v = 0 →
      ∃ c' : Fin (n - 1) → ℝ, frameVec E y c' = v := fun y hy v hv =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspanE y hy v hv)
  have hfvinj : ∀ y ∈ whitneyHalf, ∀ c₁ c₂ : Fin (n - 1) → ℝ, frameVec E y c₁ = frameVec E y c₂ →
      c₁ = c₂ := by
    intro y hy c₁ c₂ h
    have h' : ∑ k, (c₁ - c₂) k • E y k = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hEi y hy) _ h' k)
  have hfvadd : ∀ y c₁ c₂, frameVec E y (c₁ + c₂) = frameVec E y c₁ + frameVec E y c₂ := by
    intro y c₁ c₂
    simp only [frameVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hfvsmul : ∀ y (t : ℝ) c₁, frameVec E y (t • c₁) = t • frameVec E y c₁ := by
    intro y t c₁
    simp only [frameVec, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hψlev : ∀ y ∈ Wd.W, ∀ u : Fin 2 → ℝ,
      mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y u) = 0 := by
    intro y hy u
    refine portPrivate_bdd04f55_mfderiv_comp_eq_zero_of_constant_path Wd.ψ f c y (fun t => y + t • u) u ((hf.contMDiffAt).mdifferentiableAt (by simp))
      (hψd y hy) (by simp) ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y
    · have hcont : Continuous (fun t : ℝ => y + t • u) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hW : (fun t : ℝ => y + t • u) ⁻¹' Wd.W ∈ 𝓝 (0 : ℝ) :=
        hcont.continuousAt.preimage_mem_nhds (Wd.isOpen_W.mem_nhds (by simpa using hy))
      filter_upwards [hW] with t ht
      exact Wd.level _ ht
  have hψT : ∀ u : Fin 2 → ℝ, ContinuousOn (fun y => (⟨Wd.ψ y,
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y u⟩ : TangentBundle I M)) whitneyHalf := by
    intro u
    have h1 := Wd.smooth.continuousOn_tangentMapWithin (by simp) Wd.isOpen_W.uniqueMDiffOn
    have h2 : Continuous (fun y : Fin 2 → ℝ =>
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Fin 2 → ℝ)).symm (y, u))) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Fin 2 → ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    refine (h1.comp h2.continuousOn (fun y hy => Wd.half_subset hy)).congr fun y hy => ?_
    simp only [Function.comp_apply]
    rw [tangentMapWithin_eq_tangentMap (Wd.isOpen_W.uniqueMDiffOn _ (Wd.half_subset hy))
      (hψd y (Wd.half_subset hy))]
    rfl
  have hTex : ∀ i : Fin 2, ∃ cT : (Fin 2 → ℝ) → Fin (n - 1) → ℝ, ContinuousOn cT whitneyHalf ∧
      ∀ y ∈ whitneyHalf, frameVec E y (cT y) =
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (Pi.single i 1) := by
    intro i
    exact exists_continuousOn_frameCoeff hψc hEc hEi (hψT _)
      (fun y hy => hspanE y hy _ (hψlev y (hHW y hy) _))
  choose cT hcTc hcT using hTex
  let T : (Fin 2 → ℝ) → Fin 2 → (Fin (n - 1) → ℝ) := fun y i => cT i y
  have hTc : ContinuousOn T whitneyHalf := continuousOn_pi.2 fun i => hcTc i
  have hTv : ∀ y ∈ whitneyHalf, ∀ i, frameVec E y (T y i) =
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (Pi.single i 1) := fun y hy i => hcT i y hy
  have hTlin : ∀ y ∈ whitneyHalf, ∀ u : Fin 2 → ℝ, frameVec E y (u 0 • T y 0 + u 1 • T y 1) =
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y u := by
    intro y hy u
    have hu : u = u 0 • (Pi.single 0 1 : Fin 2 → ℝ) + u 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp
    rw [hfvadd, hfvsmul, hfvsmul, hTv y hy, hTv y hy]
    let L : (Fin 2 → ℝ) →L[ℝ] (Fin n → ℝ) := mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y
    conv_rhs => rw [hu]
    have := L.map_add (u 0 • (Pi.single 0 1 : Fin 2 → ℝ)) (u 1 • (Pi.single 1 1 : Fin 2 → ℝ))
    rw [L.map_smul, L.map_smul] at this
    exact this.symm
  have hTi : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (T y) := by
    intro y hy
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have h1 := hTlin y hy g
    rw [hg] at h1
    have h0 : frameVec E y 0 = 0 := by simp [frameVec]
    rw [h0] at h1
    have h2 : g = 0 := Wd.immersion y (hHW y hy)
      (h1.symm.trans (ContinuousLinearMap.map_zero _).symm)
    intro i
    rw [h2]
    rfl
  clear_value T
  let dG : ∀ r : ℕ, (M → EuclideanSpace ℝ (Fin r)) → M →
      (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    fun r G x => mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) G x
  let Arow : ∀ r : ℕ, (M → EuclideanSpace ℝ (Fin r)) → (Fin 2 → ℝ) → Matrix (Fin r) (Fin (n - 1)) ℝ :=
    fun r G y => Matrix.of fun j k => dG r G (Wd.ψ y) (E y k) j
  have hArow : ∀ (r : ℕ) (G : M → EuclideanSpace ℝ (Fin r)) y (c' : Fin (n - 1) → ℝ) (j : Fin r),
      dG r G (Wd.ψ y) (frameVec E y c') j = (Arow r G y).mulVec c' j := by
    intro r G y c' j
    change EuclideanSpace.proj j (dG r G (Wd.ψ y) (∑ k, c' k • E y k)) = ∑ k, Arow r G y j k * c' k
    simp only [map_sum, map_smul, smul_eq_mul, Arow, Matrix.of_apply, mul_comm]
    rfl
  have hArowc : ∀ (r : ℕ) (G : M → EuclideanSpace ℝ (Fin r)) (O : Set M), IsOpen O →
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ G O → ∀ S ⊆ whitneyHalf,
      MapsTo Wd.ψ S O → ContinuousOn (Arow r G) S := by
    intro r G O hO hG S hS hSO
    have h1 : ∀ k, ContinuousOn (fun y => dG r G (Wd.ψ y) (E y k)) S := fun k =>
      portPrivate_bdd04f55_continuousOn_mfderiv_apply_tangent_family G O hO hG S Wd.ψ (fun y => E y k) hSO ((hEc k).mono hS)
    refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun k => ?_
    exact ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ).continuous.comp_continuousOn
      (h1 k))
  clear_value Arow
  have hkerA : ∀ (r : ℕ) (G : M → EuclideanSpace ℝ (Fin r)) y (c' : Fin (n - 1) → ℝ),
      dG r G (Wd.ψ y) (frameVec E y c') = 0 ↔ (Arow r G y).mulVec c' = 0 := by
    intro r G y c'
    constructor
    · intro h
      funext j
      rw [← hArow, h]
      rfl
    · intro h
      refine PiLp.ext fun j => ?_
      have := hArow r G y c' j
      rw [h] at this
      exact this
  let KD : Set (Fin 2 → ℝ) := whitneyHalf ∩ {y | y 1 = 0}
  have hKDmem : ∀ y, y ∈ KD ↔ y 0 ^ 2 ≤ 1 ∧ y 1 = 0 := by
    intro y
    simp only [KD, whitneyHalf, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨(le_add_of_nonneg_right (sq_nonneg (y 1))).trans h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, by rw [h2]⟩, h2⟩
      rw [h2, zero_pow two_ne_zero, add_zero]
      exact h1
  have hKDh : KD ⊆ whitneyHalf := inter_subset_left
  have hKDcpt : IsCompact KD := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have : KD = {y : Fin 2 → ℝ | y 0 ^ 2 ≤ 1} ∩ {y | y 1 = 0} := by
        ext y; rw [hKDmem]; rfl
      rw [this]
      exact (isClosed_le ((continuous_apply 0).pow 2) continuous_const).inter
        (isClosed_eq (continuous_apply 1) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun y hy => ?_
      rw [hKDmem] at hy
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · simp only [Fin.zero_eta]
        exact abs_le_one_iff_mul_self_le_one.2 (by rw [← pow_two]; exact hy.1)
      · simp only [Fin.mk_one, hy.2, abs_zero]
        exact zero_le_one
  have hKDcvx : Convex ℝ KD := by
    intro x hx y hy s t hs ht hst
    rw [hKDmem] at hx hy ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.2, hy.2, mul_zero, add_zero,
      and_true]
    have key : (s * x 0 + t * y 0) ^ 2 =
        s * x 0 ^ 2 + t * y 0 ^ 2 - s * t * (x 0 - y 0) ^ 2 := by
      have ht' : t = 1 - s := by linarith only [hst]
      subst ht'
      ring
    have h1 : s * x 0 ^ 2 ≤ s * 1 := mul_le_mul_of_nonneg_left hx.1 hs
    have h2 : t * y 0 ^ 2 ≤ t * 1 := mul_le_mul_of_nonneg_left hy.1 ht
    rw [key]
    linarith only [h1, h2, mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x 0 - y 0)), hst]
  have hKDW : ∀ y ∈ KD, y ∈ Wd.W := fun y hy => hHW y (hKDh hy)
  have hKDSL : ∀ y ∈ KD, Wd.ψ y ∈ D.leftSphere q hq ε c := fun y hy =>
    (Wd.memA y (hKDW y hy)).2 hy.2
  have hLC0 : ∀ y ∈ Wd.W, y 1 = 0 → D.leftCoord q hq ε (Wd.ψ y) = 0 := fun y hy h1 =>
    ((mem_leftSphere_iff_coord hf D hq hε hrmq hac hc₂.le hUL (Wd.level y hy)).1
      ((Wd.memA y hy).2 h1)).1
  have hLCd : ∀ y ∈ KD, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
      (D.leftCoord q hq ε) (Wd.ψ y) := fun y hy =>
    (hLCs.contMDiffAt (hOL.mem_nhds (hSOL (hKDSL y hy)))).mdifferentiableAt (by simp)
  let AL := Arow (n - (D.chart q hq).k) (D.leftCoord q hq ε)
  have hALc : ContinuousOn AL KD :=
    hArowc _ _ OL hOL hLCs KD hKDh fun y hy => hSOL (hKDSL y hy)
  have hALs : ∀ y ∈ KD, Function.Surjective (AL y).mulVec := by
    intro y hy w
    obtain ⟨v, hv0, hvw⟩ := (hsubL _ (hKDSL y hy)).2 (WithLp.toLp 2 w)
    obtain ⟨c', hc'⟩ := hcoef y (hKDh hy) v hv0
    refine ⟨c', funext fun j => ?_⟩
    rw [← hArow, hc']
    exact congrArg (fun z : EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)) => z j) hvw
  have hALT0 : ∀ y ∈ KD, (AL y).mulVec (T y 0) = 0 := by
    intro y hy
    rw [← hkerA, hTv y (hKDh hy)]
    refine portPrivate_bdd04f55_mfderiv_comp_eq_zero_of_constant_path Wd.ψ (D.leftCoord q hq ε) 0 y (fun t => y + t • Pi.single 0 1) _ (hLCd y hy)
      (hψd y (hKDW y hy)) (by simp) ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 2 → ℝ)).const_add y
    · have hcont : Continuous (fun t : ℝ => y + t • (Pi.single 0 1 : Fin 2 → ℝ)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hW : (fun t : ℝ => y + t • (Pi.single 0 1 : Fin 2 → ℝ)) ⁻¹' Wd.W ∈ 𝓝 (0 : ℝ) :=
        hcont.continuousAt.preimage_mem_nhds (Wd.isOpen_W.mem_nhds (by simpa using hKDW y hy))
      have hy1 : y 1 = 0 := hy.2
      filter_upwards [hW] with t ht
      exact hLC0 _ ht (by simp [hy1])
  have hALT1 : ∀ y ∈ KD, (AL y).mulVec (T y 1) ≠ 0 := by
    intro y hy h0
    rw [← hkerA, hTv y (hKDh hy)] at h0
    apply Wd.transA y (hKDW y hy) hy.2
    have hcomp := mfderiv_comp (I' := I) (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))))
      y (hLCd y hy) (hψd y (hKDW y hy))
    rw [mfderiv_eq_fderiv] at hcomp
    have h1 : fderiv ℝ (fun y => D.leftCoord q hq ε (Wd.ψ y)) y =
        fderiv ℝ (D.leftCoord q hq ε ∘ Wd.ψ) y := rfl
    rw [h1]
    exact (DFunLike.congr_fun hcomp (Pi.single 1 1)).trans h0
  let BL : (Fin 2 → ℝ) → Matrix (Fin (n - (D.chart q hq).k + 1)) (Fin (n - 1)) ℝ := fun y =>
    Matrix.of (Fin.cons (T y 0) (AL y))
  have hBLc : ContinuousOn BL KD := by
    refine continuousOn_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (continuousOn_pi.1 hTc 0).mono hKDh
    · exact continuousOn_pi.1 hALc j
  have hT0ne : ∀ y ∈ whitneyHalf, T y 0 ≠ 0 := fun y hy => (hTi y hy).ne_zero 0
  have hBLs : ∀ y ∈ KD, Function.Surjective (BL y).mulVec := by
    intro y hy w
    obtain ⟨c', hc'⟩ := hALs y hy (Fin.tail w)
    have hTT : T y 0 ⬝ᵥ T y 0 ≠ 0 := fun h => hT0ne y (hKDh hy) (dotProduct_self_eq_zero.1 h)
    refine ⟨c' + ((w 0 - T y 0 ⬝ᵥ c') / (T y 0 ⬝ᵥ T y 0)) • T y 0, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · change T y 0 ⬝ᵥ _ = _
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hTT]
      ring
    · have h1 : (BL y).mulVec (c' + ((w 0 - T y 0 ⬝ᵥ c') / (T y 0 ⬝ᵥ T y 0)) • T y 0) j.succ =
          (AL y).mulVec (c' + ((w 0 - T y 0 ⬝ᵥ c') / (T y 0 ⬝ᵥ T y 0)) • T y 0) j := rfl
      rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul, hALT0 y hy, smul_zero, add_zero, hc']
      rfl
  obtain ⟨FL, hFLc, hFL⟩ := portPrivate_bdd04f55_exists_continuous_kernel_frame (s := (D.chart q hq).k - 1 - 1) KD hKDcpt hKDcvx BL hBLc hBLs
    (by omega)
  have hFLT : ∀ y ∈ KD, ∀ i, T y 0 ⬝ᵥ FL y i = 0 := by
    intro y hy i
    exact congrFun ((hFL y hy).2 i) 0
  have hFLA : ∀ y ∈ KD, ∀ i, (AL y).mulVec (FL y i) = 0 := by
    intro y hy i
    funext j
    exact congrFun ((hFL y hy).2 i) j.succ
  let SL : (Fin 2 → ℝ) → Fin ℓ → (Fin (n - 1) → ℝ) := fun y i =>
    if h : (i : ℕ) = 0 then T y 0 else FL y ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩
  have hSLdef : ∀ y (i : Fin ℓ), SL y i =
      if h : (i : ℕ) = 0 then T y 0 else FL y ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ :=
    fun y i => rfl
  have hSLc : ContinuousOn SL KD := by
    refine continuousOn_pi.2 fun i => ?_
    by_cases h : (i : ℕ) = 0
    · simp only [hSLdef, h, ↓reduceDIte]
      exact (continuousOn_pi.1 hTc 0).mono hKDh
    · simp only [hSLdef, h, ↓reduceDIte]
      exact continuousOn_pi.1 hFLc _
  have hSLA : ∀ y ∈ KD, ∀ i, (AL y).mulVec (SL y i) = 0 := by
    intro y hy i
    by_cases h : (i : ℕ) = 0
    · simp only [hSLdef, h, ↓reduceDIte]
      exact hALT0 y hy
    · simp only [hSLdef, h, ↓reduceDIte]
      exact hFLA y hy _
  have hindL : ∀ y ∈ KD, LinearIndependent ℝ
      (Fin.cons (T y 1) (SL y) : Fin (ℓ + 1) → Fin (n - 1) → ℝ) := fun y hy =>
    portPrivate_bdd04f55_linearIndependent_finCons_of_kernel_and_orthogonal (m' := (D.chart q hq).k - 1 - 1) (by omega) (AL y) (T y 1) (T y 0) (FL y) (SL y)
      (hSLdef y) (hALT1 y hy) (hALT0 y hy) (hFLA y hy) (hT0ne y (hKDh hy)) (hFLT y hy)
      (hFL y hy).1
  clear_value SL BL
  let KA : Set (Fin 2 → ℝ) := whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}
  have hKAh : KA ⊆ whitneyHalf := inter_subset_left
  have hKAW : ∀ y ∈ KA, y ∈ Wd.W := fun y hy => hHW y (hKAh hy)
  have hKASR : ∀ y ∈ KA, Wd.ψ y ∈ D.rightSphere p hp ε c := fun y hy =>
    (Wd.memB y (hKAW y hy)).2 hy.2
  have hRC0 : ∀ y ∈ Wd.W, y 0 ^ 2 + y 1 ^ 2 = 1 → D.rightCoord p hp ε (Wd.ψ y) = 0 :=
    fun y hy h1 => ((mem_rightSphere_iff_coord hf D hp hε hrmp hc₁.le hcb hUR
      (Wd.level y hy)).1 ((Wd.memB y hy).2 h1)).1
  have hRCd : ∀ y ∈ KA, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
      (D.rightCoord p hp ε) (Wd.ψ y) := fun y hy =>
    (hRCs.contMDiffAt (hOR.mem_nhds (hSOR (hKASR y hy)))).mdifferentiableAt (by simp)
  let AR := Arow (D.chart p hp).k (D.rightCoord p hp ε)
  have hARc : ContinuousOn AR KA :=
    hArowc _ _ OR hOR hRCs KA hKAh fun y hy => hSOR (hKASR y hy)
  have hARs : ∀ y ∈ KA, Function.Surjective (AR y).mulVec := by
    intro y hy w
    obtain ⟨v, hv0, hvw⟩ := (hsubR _ (hKASR y hy)).2 (WithLp.toLp 2 w)
    obtain ⟨c', hc'⟩ := hcoef y (hKAh hy) v hv0
    refine ⟨c', funext fun j => ?_⟩
    rw [← hArow, hc']
    exact congrArg (fun z : EuclideanSpace ℝ (Fin (D.chart p hp).k) => z j) hvw
  let hd : (Fin 2 → ℝ) → (Fin (n - 1) → ℝ) := fun y => (-(y 1)) • T y 0 + y 0 • T y 1
  let rad : (Fin 2 → ℝ) → (Fin (n - 1) → ℝ) := fun y => y 0 • T y 0 + y 1 • T y 1
  have hARhd : ∀ y ∈ KA, (AR y).mulVec (hd y) = 0 := by
    intro y hy
    have hu : hd y = (![-(y 1), y 0] : Fin 2 → ℝ) 0 • T y 0 + (![-(y 1), y 0] : Fin 2 → ℝ) 1 • T y 1 := by
      simp [hd]
    rw [← hkerA, hu, hTlin y (hKAh hy)]
    let γ : ℝ → Fin 2 → ℝ := fun t => ![y 0 * Real.cos t - y 1 * Real.sin t,
      y 0 * Real.sin t + y 1 * Real.cos t]
    have hγc : Continuous γ := by
      refine continuous_pi fun i => ?_
      fin_cases i
      · simp only [γ, Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
      · simp only [γ, Fin.mk_one, Matrix.cons_val_one]; fun_prop
    have hγ0 : γ 0 = y := by
      funext i
      fin_cases i <;> simp [γ]
    refine portPrivate_bdd04f55_mfderiv_comp_eq_zero_of_constant_path Wd.ψ (D.rightCoord p hp ε) 0 y γ _ (hRCd y hy) (hψd y (hKAW y hy)) hγ0 ?_ ?_
    · refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i
      · simp only [γ, Fin.zero_eta, Matrix.cons_val_zero]
        have h1 := ((Real.hasDerivAt_cos 0).const_mul (y 0)).sub ((Real.hasDerivAt_sin 0).const_mul (y 1))
        convert h1 using 1
        simp
      · simp only [γ, Fin.mk_one, Matrix.cons_val_one]
        have h1 := ((Real.hasDerivAt_sin 0).const_mul (y 0)).add ((Real.hasDerivAt_cos 0).const_mul (y 1))
        convert h1 using 1 <;> first | rfl | simp
    · have hW : γ ⁻¹' Wd.W ∈ 𝓝 (0 : ℝ) :=
        hγc.continuousAt.preimage_mem_nhds (Wd.isOpen_W.mem_nhds (by rw [hγ0]; exact hKAW y hy))
      have hy1 : y 0 ^ 2 + y 1 ^ 2 = 1 := hy.2
      filter_upwards [hW] with t ht
      refine hRC0 _ ht ?_
      simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one]
      have := Real.sin_sq_add_cos_sq t
      linear_combination (Real.cos t ^ 2 + Real.sin t ^ 2) * hy1 + this
  have hARrad : ∀ y ∈ KA, (AR y).mulVec (rad y) ≠ 0 := by
    intro y hy h0
    rw [← hkerA] at h0
    have hrad : rad y = y 0 • T y 0 + y 1 • T y 1 := rfl
    rw [hrad, hTlin y (hKAh hy)] at h0
    apply Wd.transB y (hKAW y hy) hy.2
    have hcomp := mfderiv_comp (I' := I) (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)))
      y (hRCd y hy) (hψd y (hKAW y hy))
    rw [mfderiv_eq_fderiv] at hcomp
    have h1 : fderiv ℝ (fun y => D.rightCoord p hp ε (Wd.ψ y)) y =
        fderiv ℝ (D.rightCoord p hp ε ∘ Wd.ψ) y := rfl
    rw [h1]
    exact (DFunLike.congr_fun hcomp y).trans h0
  have hhdne : ∀ y ∈ KA, hd y ≠ 0 := by
    intro y hy h0
    have h1 := Fintype.linearIndependent_iff.1 (hTi y (hKAh hy)) ![-(y 1), y 0]
      (by rw [Fin.sum_univ_two]; simpa [hd] using h0)
    have h2 := h1 0
    have h3 := h1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_eq_zero] at h2 h3
    have hy1 : y 0 ^ 2 + y 1 ^ 2 = 1 := hy.2
    rw [h2, h3] at hy1
    norm_num at hy1
  have hhdc : ContinuousOn hd KA := by
    have h0 := (continuousOn_pi.1 hTc 0).mono hKAh
    have h1 := (continuousOn_pi.1 hTc 1).mono hKAh
    exact ((continuous_apply 1).continuousOn.neg.smul h0).add ((continuous_apply 0).continuousOn.smul h1)
  let KΘ : Set (Fin 1 → ℝ) := Icc (fun _ => 0) (fun _ => Real.pi)
  have hKΘmem : ∀ t : Fin 1 → ℝ, t ∈ KΘ ↔ t 0 ∈ Icc (0 : ℝ) Real.pi := by
    intro t
    simp only [KΘ, mem_Icc, Pi.le_def, Fin.forall_fin_one]
  let ζ : (Fin 1 → ℝ) → (Fin 2 → ℝ) := fun t => ![Real.cos (t 0), Real.sin (t 0)]
  have hζc : Continuous ζ := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp only [ζ, Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
    · simp only [ζ, Fin.mk_one, Matrix.cons_val_one]; fun_prop
  have hζKA : MapsTo ζ KΘ KA := by
    intro t ht
    rw [hKΘmem] at ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [ζ, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Real.cos_sq_add_sin_sq]
    · simp only [ζ, Matrix.cons_val_one]
      exact Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    · change (ζ t) 0 ^ 2 + (ζ t) 1 ^ 2 = 1
      simp only [ζ, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Real.cos_sq_add_sin_sq]
  let ϑ : (Fin 2 → ℝ) → (Fin 1 → ℝ) := fun y _ => Real.arccos (y 0)
  have hϑc : Continuous ϑ := continuous_pi fun _ => Real.continuous_arccos.comp (continuous_apply 0)
  have hϑK : MapsTo ϑ KA KΘ := fun y _ =>
    (hKΘmem _).2 ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hζϑ : ∀ y ∈ KA, ζ (ϑ y) = y := by
    intro y hy
    have hy1 : y 0 ^ 2 + y 1 ^ 2 = 1 := hy.2
    have hy2 : 0 ≤ y 1 := hy.1.2
    have hle : -1 ≤ y 0 ∧ y 0 ≤ 1 :=
      abs_le.1 ((sq_le_one_iff_abs_le_one _).1 (by linarith only [sq_nonneg (y 1), hy1]))
    funext i
    fin_cases i
    · simp only [ζ, ϑ, Fin.zero_eta, Matrix.cons_val_zero]
      exact Real.cos_arccos hle.1 hle.2
    · simp only [ζ, ϑ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Real.sin_arccos, show 1 - y 0 ^ 2 = y 1 ^ 2 by linarith only [hy1], Real.sqrt_sq hy2]
  have hζdef : ∀ t, ζ t = ![Real.cos (t 0), Real.sin (t 0)] := fun t => rfl
  clear_value ζ ϑ
  let BR : (Fin 1 → ℝ) → Matrix (Fin ((D.chart p hp).k + 1)) (Fin (n - 1)) ℝ := fun t =>
    Matrix.of (Fin.cons (hd (ζ t)) (AR (ζ t)))
  have hBRc : ContinuousOn BR KΘ := by
    refine continuousOn_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhdc.comp hζc.continuousOn hζKA
    · exact (continuousOn_pi.1 hARc j).comp hζc.continuousOn hζKA
  have hBRs : ∀ t ∈ KΘ, Function.Surjective (BR t).mulVec := by
    intro t ht w
    let y := ζ t
    have hyKA : y ∈ KA := hζKA ht
    obtain ⟨c', hc'⟩ := hARs y hyKA (Fin.tail w)
    have hTT : hd y ⬝ᵥ hd y ≠ 0 := fun h => hhdne y hyKA (dotProduct_self_eq_zero.1 h)
    refine ⟨c' + ((w 0 - hd y ⬝ᵥ c') / (hd y ⬝ᵥ hd y)) • hd y, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · change hd y ⬝ᵥ _ = _
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hTT]
      ring
    · have h1 : (BR t).mulVec (c' + ((w 0 - hd y ⬝ᵥ c') / (hd y ⬝ᵥ hd y)) • hd y) j.succ =
          (AR y).mulVec (c' + ((w 0 - hd y ⬝ᵥ c') / (hd y ⬝ᵥ hd y)) • hd y) j := rfl
      rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul, hARhd y hyKA, smul_zero, add_zero, hc']
      rfl
  have hKΘcpt : IsCompact KΘ := isCompact_Icc
  have hKΘcvx : Convex ℝ KΘ := convex_Icc _ _
  obtain ⟨FR, hFRc, hFR⟩ := portPrivate_bdd04f55_exists_continuous_kernel_frame (s := n - 1 - ℓ - 1) KΘ hKΘcpt hKΘcvx BR hBRc hBRs (by omega)
  have hBRϑ : ∀ y ∈ KA, BR (ϑ y) = Matrix.of (Fin.cons (hd y) (AR y)) := by
    intro y hy
    simp only [BR, hζϑ y hy]
  have hFRT : ∀ y ∈ KA, ∀ i, hd y ⬝ᵥ FR (ϑ y) i = 0 := by
    intro y hy i
    have := congrFun ((hFR (ϑ y) (hϑK hy)).2 i) 0
    rw [hBRϑ y hy] at this
    exact this
  have hFRA : ∀ y ∈ KA, ∀ i, (AR y).mulVec (FR (ϑ y) i) = 0 := by
    intro y hy i
    funext j
    have := congrFun ((hFR (ϑ y) (hϑK hy)).2 i) j.succ
    rw [hBRϑ y hy] at this
    exact this
  let SR : (Fin 2 → ℝ) → Fin (n - 1 - ℓ) → (Fin (n - 1) → ℝ) := fun y i =>
    if h : (i : ℕ) = 0 then hd y else FR (ϑ y) ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩
  have hSRdef : ∀ y (i : Fin (n - 1 - ℓ)), SR y i =
      if h : (i : ℕ) = 0 then hd y else FR (ϑ y) ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ :=
    fun y i => rfl
  have hSRc : ContinuousOn SR KA := by
    refine continuousOn_pi.2 fun i => ?_
    by_cases h : (i : ℕ) = 0
    · simp only [hSRdef, h, ↓reduceDIte]
      exact hhdc
    · simp only [hSRdef, h, ↓reduceDIte]
      exact (continuousOn_pi.1 hFRc _).comp hϑc.continuousOn hϑK
  have hSRA : ∀ y ∈ KA, ∀ i, (AR y).mulVec (SR y i) = 0 := by
    intro y hy i
    by_cases h : (i : ℕ) = 0
    · simp only [hSRdef, h, ↓reduceDIte]
      exact hARhd y hy
    · simp only [hSRdef, h, ↓reduceDIte]
      exact hFRA y hy _
  have hindR : ∀ y ∈ KA, LinearIndependent ℝ
      (Fin.cons (rad y) (SR y) : Fin (n - 1 - ℓ + 1) → Fin (n - 1) → ℝ) := fun y hy =>
    portPrivate_bdd04f55_linearIndependent_finCons_of_kernel_and_orthogonal (m' := n - 1 - ℓ - 1) (by omega) (AR y) (rad y) (hd y) (FR (ϑ y)) (SR y)
      (hSRdef y) (hARrad y hy) (hARhd y hy) (hFRA y hy) (hhdne y hy) (hFRT y hy)
      (hFR (ϑ y) (hϑK hy)).1
  clear_value SR BR
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 :=
    hrmq.le.trans (pow_le_pow_left₀ (D.rm_pos q hq).le (D.hrm q hq).2 2)
  let Sg : (Fin (D.chart q hq).k → ℝ) → M := fun w =>
    D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))
  have hSgs : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞ Sg w := by
    intro w hw
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((D.chart q hq).sphereParam ε) w :=
      contMDiffAt_iff_contDiffAt.2 ((D.chart q hq).contDiffAt_sphereParam ε hw)
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart q hq).χ ((D.chart q hq).sphereParam ε w) :=
      (D.chart q hq).contMDiffAt_chart
        ((D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq hw))
    exact ((D.contMDiff_flow (f q - ε - c)).contMDiffAt).comp w (hχq.comp w hsp)
  have hFT := D.flow_level_transport hf (c' := c) (c := f q - ε) hac hc₂.le
    (by linarith only [hqab.2, hε]) hUL
  have hSgf : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → f (Sg w) = c := fun w hw =>
    (hFT.1 _ ((D.chart q hq).f_chart_of_mem_leftModelSphere hRq
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw))).1
  have hflow1 : ∀ x, D.flow (c - (f q - ε)) (D.flow (f q - ε - c) x) = x := fun x => by
    rw [← D.flow_add, show f q - ε - c + (c - (f q - ε)) = 0 by ring, D.flow_zero]
  have hflow2 : ∀ x, D.flow (f q - ε - c) (D.flow (c - (f q - ε)) x) = x := fun x => by
    rw [← D.flow_add, show c - (f q - ε) + (f q - ε - c) = 0 by ring, D.flow_zero]
  have hSgSL : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → Sg w ∈ D.leftSphere q hq ε c := by
    intro w hw
    rw [D.mem_leftSphere_iff, hflow1]
    exact ⟨_, (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw, rfl⟩
  have hSgLC : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → D.leftCoord q hq ε (Sg w) = 0 :=
    fun w hw => ((mem_leftSphere_iff_coord hf D hq hε hrmq hac hc₂.le hUL (hSgf w hw)).1
      (hSgSL w hw)).1
  let Lq : M → EuclideanSpace ℝ (Fin (D.chart q hq).k) := fun z =>
    ModelField.negPartL (D.chart q hq).hk ((D.chart q hq).χ.symm (D.flow (c - (f q - ε)) z))
  have hLqSg : ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 →
      Lq (Sg w) = (Real.sqrt (2 * ε) / ‖(D.chart q hq).toE w‖) • (D.chart q hq).toE w := by
    intro w hw
    simp only [Lq, Sg, hflow1, ModelField.negPartL_apply]
    rw [(D.chart q hq).χ.left_inv ((D.chart q hq).hsrc _
      ((D.chart q hq).morseNorm_sphereParam_le hε.le hRq hw))]
    exact (D.chart q hq).negPart_sphereParam ε w
  let OLq : Set M := D.flow (c - (f q - ε)) ⁻¹'
    ((D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R')
  have hOLqo : IsOpen OLq := (D.chart q hq).isOpen_image_ball.preimage (D.continuous_flow _)
  have hLqs : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q hq).k)) ∞ Lq OLq :=
    (ModelField.negPartL (D.chart q hq).hk).contMDiff.comp_contMDiffOn
      ((D.chart q hq).hχsymm.comp (D.contMDiff_flow _).contMDiffOn fun x hx => hx)
  have hSLOLq : ∀ x ∈ D.leftSphere q hq ε c, x ∈ OLq := by
    intro x hx
    rw [D.mem_leftSphere_iff] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    exact ⟨z, (D.chart q hq).mem_ball_of_le
      ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hRq hz), hzx⟩
  have hLqinv : ∀ x ∈ D.leftSphere q hq ε c,
      (EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) (Lq x) ≠ 0 ∧
        Sg ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ) (Lq x)) = x := by
    intro x hx
    rw [D.mem_leftSphere_iff] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hzs : z ∈ (D.chart q hq).χ.source := (D.chart q hq).hsrc _
      ((D.chart q hq).morseNorm_le_R_of_mem_leftModelSphere hRq hz)
    have hL : Lq x = negPart (D.chart q hq).hk z := by
      simp only [Lq, ModelField.negPartL_apply]
      rw [← hzx, (D.chart q hq).χ.left_inv hzs]
    obtain ⟨h1, h2⟩ := (D.chart q hq).sphereParam_of_mem hε hz
    refine ⟨by rw [hL]; exact h1, ?_⟩
    simp only [Sg]
    rw [hL, h2, hzx, hflow2]
  clear_value Lq
  have hSLi : ∀ y ∈ KD, LinearIndependent ℝ (SL y) := fun y hy => by
    have h := (hindL y hy).comp Fin.succ (Fin.succ_injective _)
    simpa using h
  have hkerSL : ∀ y ∈ KD, ∀ c' : Fin (n - 1) → ℝ, (AL y).mulVec c' = 0 →
      c' ∈ Submodule.span ℝ (Set.range (SL y)) := by
    intro y hy c' hc'
    have hle : Submodule.span ℝ (Set.range (SL y)) ≤ LinearMap.ker (Matrix.mulVecLin (AL y)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hSLA y hy i
    have hker : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (AL y))) = ℓ := by
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (AL y))
      have htop : LinearMap.range (Matrix.mulVecLin (AL y)) = ⊤ :=
        LinearMap.range_eq_top.2 (hALs y hy)
      rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
      omega
    have heq := Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_eq_card (hSLi y hy), Fintype.card_fin, hker])
    rw [heq]
    exact hc'
  let FV : (Fin 2 → ℝ) → (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := fun y =>
    Fintype.linearCombination ℝ (E y)
  have hFV : ∀ y c', FV y c' = frameVec E y c' := fun y c' => by
    simp only [FV, Fintype.linearCombination_apply, frameVec]
  clear_value FV
  have hconst : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : M → F) (C : F)
      (w : Fin (D.chart q hq).k → ℝ), MDifferentiableAt I 𝓘(ℝ, F) G (Sg w) →
      MDifferentiableAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w →
      (∀ᶠ w' in 𝓝 w, G (Sg w') = C) → ∀ u,
      mfderiv I 𝓘(ℝ, F) G (Sg w) (mfderiv 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w u) = 0 := by
    intro F _ _ G C w hG hS hC u
    have h2 := hG.hasMFDerivAt.comp w hS.hasMFDerivAt
    have h3 : HasMFDerivAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, F) (G ∘ Sg) w 0 := by
      have : HasMFDerivAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, F) (fun _ => C) w 0 :=
        hasMFDerivAt_const _ _
      exact this.congr_of_eventuallyEq (hC.mono fun t ht => ht)
    have h4 := h2.mfderiv.symm.trans h3.mfderiv
    exact congrArg (fun L => L u) h4
  let eqv := EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ
  have hinner : ∀ u u' : Fin (D.chart q hq).k → ℝ, inner ℝ (eqv.symm u) (eqv.symm u') = u ⬝ᵥ u' := by
    intro u u'
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct_comm]
    rfl
  have hU7 : ∀ y ∈ KD, ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → Sg w = Wd.ψ y →
      ∃ u : Fin ℓ → (Fin (D.chart q hq).k → ℝ), (∀ j, w ⬝ᵥ u j = 0) ∧ LinearIndependent ℝ u ∧
        (∀ j, mfderiv 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w (u j) = frameVec E y (SL y j)) ∧
        (∀ j, dG _ Lq (Wd.ψ y) (frameVec E y (SL y j)) =
          (Real.sqrt (2 * ε) / ‖eqv.symm w‖) • eqv.symm (u j)) := by
    intro y hy w hw hSgw
    have hxSL : Wd.ψ y ∈ D.leftSphere q hq ε c := hKDSL y hy
    have hSgd : MDifferentiableAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w :=
      (hSgs w hw).mdifferentiableAt (by simp)
    have hLqd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart q hq).k)) Lq (Sg w) := by
      rw [hSgw]
      exact (hLqs.contMDiffAt (hOLqo.mem_nhds (hSLOLq _ hxSL))).mdifferentiableAt (by simp)
    have hnhds : ∀ᶠ w' in 𝓝 w, w' ≠ 0 := isOpen_ne.mem_nhds hw
    let dSg : (Fin (D.chart q hq).k → ℝ) →L[ℝ] (Fin n → ℝ) :=
      mfderiv 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w
    have hew : eqv.symm w ≠ 0 := (D.chart q hq).toE_ne_zero hw
    have hnw : ‖eqv.symm w‖ ≠ 0 := norm_ne_zero_iff.2 hew
    have hnd : DifferentiableAt ℝ (fun w' : Fin (D.chart q hq).k → ℝ => ‖eqv.symm w'‖) w :=
      (eqv.symm.differentiableAt).norm ℝ hew
    have hgd : DifferentiableAt ℝ
        (fun w' : Fin (D.chart q hq).k → ℝ => Real.sqrt (2 * ε) * ‖eqv.symm w'‖⁻¹) w :=
      (hnd.fun_inv hnw).const_mul _
    let g : (Fin (D.chart q hq).k → ℝ) → ℝ := fun w' => Real.sqrt (2 * ε) * ‖eqv.symm w'‖⁻¹
    let N : (Fin (D.chart q hq).k → ℝ) → EuclideanSpace ℝ (Fin (D.chart q hq).k) :=
      fun w' => g w' • eqv.symm w'
    have hNd : HasFDerivAt N (g w • (eqv.symm : (Fin (D.chart q hq).k → ℝ) →L[ℝ] _) +
        (fderiv ℝ g w).smulRight (eqv.symm w)) w :=
      hgd.hasFDerivAt.smul eqv.symm.hasFDerivAt
    have hsq : ∀ w' : Fin (D.chart q hq).k → ℝ, w' ≠ 0 → ‖N w'‖ ^ 2 = 2 * ε := by
      intro w' hw'
      have hn' : ‖eqv.symm w'‖ ≠ 0 := norm_ne_zero_iff.2 ((D.chart q hq).toE_ne_zero hw')
      simp only [N, g, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
        Real.sq_sqrt (mul_pos two_pos hε).le]
      field_simp
    have hD : ∀ u, w ⬝ᵥ u = 0 → fderiv ℝ N w u = g w • eqv.symm u := by
      intro u hu
      have h1 := hNd.norm_sq
      have h2 : HasFDerivAt (fun w' => ‖N w'‖ ^ 2) (0 : (Fin (D.chart q hq).k → ℝ) →L[ℝ] ℝ) w :=
        (hasFDerivAt_const (2 * ε) w).congr_of_eventuallyEq (hnhds.mono fun w' hw' => hsq w' hw')
      have h3 := congrArg (fun L : (Fin (D.chart q hq).k → ℝ) →L[ℝ] ℝ => L u) (h1.unique h2)
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, add_apply, ContinuousLinearMap.smulRight_apply,
        zero_apply, two_smul, ContinuousLinearEquiv.coe_coe] at h3
      rw [hNd.fderiv]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe]
      have hww : w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.1 h)
      have hg0 : g w ≠ 0 := mul_ne_zero (Real.sqrt_ne_zero'.2 (mul_pos two_pos hε)) (inv_ne_zero hnw)
      have h4 : g w * (g w * (w ⬝ᵥ u) + fderiv ℝ g w u * (w ⬝ᵥ w)) = 0 := by
        have h5 : inner ℝ (N w) (g w • eqv.symm u + fderiv ℝ g w u • eqv.symm w) =
            g w * (g w * (w ⬝ᵥ u) + fderiv ℝ g w u * (w ⬝ᵥ w)) := by
          simp only [N, inner_add_right, inner_smul_left, inner_smul_right, hinner,
            RCLike.conj_to_real]
          ring
        rw [← h5]
        linarith only [h3]
      rw [hu, mul_zero, zero_add] at h4
      have hβ : fderiv ℝ g w u = 0 := by
        rcases mul_eq_zero.1 h4 with h | h
        · exact absurd h hg0
        · rcases mul_eq_zero.1 h with h | h
          · exact h
          · exact absurd h hww
      rw [hβ, zero_smul, add_zero]
    have hLqSgN : Lq ∘ Sg =ᶠ[𝓝 w] N := hnhds.mono fun w' hw' => by
      change Lq (Sg w') = N w'
      rw [hLqSg w' hw', div_eq_mul_inv]
      rfl
    have hchain : ∀ u, dG _ Lq (Sg w) (dSg u) = fderiv ℝ N w u := by
      intro u
      have hA := (hLqd.hasMFDerivAt.comp w hSgd.hasMFDerivAt).mfderiv
      have hB := ((hasMFDerivAt_iff_hasFDerivAt.2 hNd).congr_of_eventuallyEq hLqSgN).mfderiv
      rw [hNd.fderiv]
      exact congrArg (fun L => L u) (hA.symm.trans hB)
    have hdSgf : ∀ u, mfderiv I 𝓘(ℝ, ℝ) f (Sg w) (dSg u) = 0 :=
      hconst f c w (hf.mdifferentiableAt (by simp)) hSgd (hnhds.mono fun w' hw' => hSgf w' hw')
    have hLCd' : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k)))
        (D.leftCoord q hq ε) (Sg w) := by rw [hSgw]; exact hLCd y hy
    have hdSgL : ∀ u, dG _ (D.leftCoord q hq ε) (Sg w) (dSg u) = 0 :=
      hconst (D.leftCoord q hq ε) 0 w hLCd' hSgd (hnhds.mono fun w' hw' => hSgLC w' hw')
    let v : Fin ℓ → (Fin n → ℝ) := fun j => frameVec E y (SL y j)
    have hdSgsp : ∀ u, dSg u ∈ Submodule.span ℝ (Set.range v) := by
      intro u
      obtain ⟨c', hc'⟩ := hcoef y (hKDh hy) (dSg u) (by rw [← hSgw]; exact hdSgf u)
      have hA : (AL y).mulVec c' = 0 := by
        rw [← hkerA, hc', ← hSgw]
        exact hdSgL u
      have h1 := Submodule.mem_map_of_mem (f := FV y) (hkerSL y hy c' hA)
      rw [Submodule.map_span, ← Set.range_comp, hFV] at h1
      have hv : (FV y) ∘ (SL y) = v := funext fun j => hFV y _
      rw [hv] at h1
      rw [← hc']
      exact h1
    let φw : (Fin (D.chart q hq).k → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun u => w ⬝ᵥ u
        map_add' := dotProduct_add _
        map_smul' := fun t u => by simp [dotProduct_smul] }
    have hww : w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.1 h)
    have hperp : Module.finrank ℝ (LinearMap.ker φw) = ℓ := by
      have h := LinearMap.finrank_range_add_finrank_ker φw
      have htop : LinearMap.range φw = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro r
        refine ⟨(r / (w ⬝ᵥ w)) • w, ?_⟩
        change w ⬝ᵥ ((r / (w ⬝ᵥ w)) • w) = r
        rw [dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hww]
      rw [htop, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
      omega
    have hvi : LinearIndependent ℝ v := by
      have hker : LinearMap.ker (FV y) = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro c' hc'
        have := hfvinj y (hKDh hy) c' 0 (by rw [← hFV, ← hFV, hc', map_zero])
        exact this
      have h := (hSLi y hy).map' (FV y) hker
      have hv : (FV y) ∘ (SL y) = v := funext fun j => hFV y _
      rwa [hv] at h
    have hVr : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = ℓ := by
      rw [finrank_span_eq_card hvi, Fintype.card_fin]
    let gm : LinearMap.ker φw →ₗ[ℝ] Submodule.span ℝ (Set.range v) :=
      LinearMap.codRestrict _ ((dSg : (Fin (D.chart q hq).k → ℝ) →ₗ[ℝ] (Fin n → ℝ)).domRestrict
        (LinearMap.ker φw)) fun u => hdSgsp u
    have hgm : Function.Injective gm := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have h1 : dSg u = 0 := congrArg Subtype.val hu
      have h2 := hchain u
      rw [h1, map_zero, hD u u.2] at h2
      have h3 : eqv.symm u = 0 := by
        rcases smul_eq_zero.1 h2.symm with h | h
        · exact absurd h (mul_ne_zero (Real.sqrt_ne_zero'.2 (mul_pos two_pos hε)) (inv_ne_zero hnw))
        · exact h
      exact Subtype.ext (eqv.symm.map_eq_zero_iff.1 h3)
    have hgs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hperp, hVr])).1 hgm
    choose uu huu using fun j => hgs ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
    have hdu : ∀ j, dSg (uu j) = v j := fun j => congrArg Subtype.val (huu j)
    refine ⟨fun j => (uu j : Fin (D.chart q hq).k → ℝ), fun j => (uu j).2, ?_, hdu, fun j => ?_⟩
    · apply LinearIndependent.of_comp (dSg : (Fin (D.chart q hq).k → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      have h : (dSg : (Fin (D.chart q hq).k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘
          (fun j => (uu j : Fin (D.chart q hq).k → ℝ)) = v := funext fun j => hdu j
      rw [h]
      exact hvi
    · have h := hchain (uu j)
      rw [hdu j, hD _ (uu j).2, hSgw] at h
      rw [h, div_eq_mul_inv]
  let ALq := Arow (D.chart q hq).k Lq
  have hALqc : ContinuousOn ALq KD :=
    hArowc _ _ OLq hOLqo hLqs KD hKDh fun y hy => hSLOLq _ (hKDSL y hy)
  let Umat : (Fin (D.chart q hq).k → ℝ) → (Fin ℓ → Fin (D.chart q hq).k → ℝ) →
      Matrix (Fin (D.chart q hq).k) (Fin (D.chart q hq).k) ℝ := fun w u =>
    Matrix.of fun i j => if h : (j : ℕ) = 0 then w i else u ⟨(j : ℕ) - 1, by omega⟩ i
  let Omat : (Fin 2 → ℝ) → Matrix (Fin (D.chart q hq).k) (Fin (D.chart q hq).k) ℝ := fun y =>
    Matrix.of fun i j => if h : (j : ℕ) = 0 then Lq (Wd.ψ y) i else
      (ALq y).mulVec (SL y ⟨(j : ℕ) - 1, by omega⟩) i
  have hUdet : ∀ (w : Fin (D.chart q hq).k → ℝ) (u : Fin ℓ → Fin (D.chart q hq).k → ℝ),
      w ≠ 0 → (∀ j, w ⬝ᵥ u j = 0) → LinearIndependent ℝ u → (Umat w u).det ≠ 0 := by
    intro w u hw hwu hu
    have hcols : LinearIndependent ℝ (Umat w u).col :=
      portPrivate_bdd04f55_linearIndependent_of_orthogonal_cons (m' := ℓ) hkq w u (Umat w u).col (fun i => by
        funext k
        by_cases h : (i : ℕ) = 0 <;> simp [Umat, h]) hw hwu hu
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hcols)
      |>.ne_zero
  have hOU : ∀ y ∈ KD, ∀ w : Fin (D.chart q hq).k → ℝ, w ≠ 0 → Sg w = Wd.ψ y →
      ∃ u : Fin ℓ → (Fin (D.chart q hq).k → ℝ), (∀ j, w ⬝ᵥ u j = 0) ∧ LinearIndependent ℝ u ∧
        (∀ j, mfderiv 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w (u j) = frameVec E y (SL y j)) ∧
        Omat y = (Real.sqrt (2 * ε) / ‖eqv.symm w‖) • Umat w u := by
    intro y hy w hw hSgw
    obtain ⟨u, hwu, hu, hdu, hdL⟩ := hU7 y hy w hw hSgw
    refine ⟨u, hwu, hu, hdu, ?_⟩
    ext i j
    simp only [Omat, Umat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, ↓reduceDIte]
      rw [← hSgw, hLqSg w hw]
      rfl
    · simp only [hj, ↓reduceDIte]
      rw [← hArow, hdL]
      rfl
  have hOdet : ∀ y ∈ KD, (Omat y).det ≠ 0 := by
    intro y hy
    obtain ⟨hw0, hSgw⟩ := hLqinv _ (hKDSL y hy)
    obtain ⟨u, hwu, hu, -, hO⟩ := hOU y hy _ hw0 hSgw
    rw [hO, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (div_ne_zero (Real.sqrt_ne_zero'.2 (mul_pos two_pos hε))
      (norm_ne_zero_iff.2 ((D.chart q hq).toE_ne_zero hw0)))) (hUdet _ _ hw0 hwu hu)
  have hOc : ContinuousOn (fun y => (Omat y).det) KD := by
    have hLqψ : ContinuousOn (fun y => Lq (Wd.ψ y)) KD :=
      hLqs.continuousOn.comp (hψc.mono hKDh) fun y hy => hSLOLq _ (hKDSL y hy)
    have hmv : ∀ j : Fin ℓ, ContinuousOn (fun y => (ALq y).mulVec (SL y j)) KD := by
      intro j
      refine continuousOn_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finsetSum _ fun k _ =>
        (continuousOn_pi.1 (continuousOn_pi.1 hALqc i) k).mul
          (continuousOn_pi.1 (continuousOn_pi.1 hSLc j) k)
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    by_cases hj : (j : ℕ) = 0
    · simp only [Matrix.of_apply, hj, ↓reduceDIte]
      exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (D.chart q hq).k) →L[ℝ] ℝ).continuous
        |>.comp_continuousOn hLqψ
    · simp only [Matrix.of_apply, hj, ↓reduceDIte]
      exact (continuous_apply i).comp_continuousOn (hmv _)
  have hy₁KD : (![-1, 0] : Fin 2 → ℝ) ∈ KD := (hKDmem _).2 ⟨by norm_num, rfl⟩
  have hy₂KD : (![1, 0] : Fin 2 → ℝ) ∈ KD := (hKDmem _).2 ⟨by norm_num, rfl⟩
  have hOsgn : SignType.sign (Omat ![-1, 0]).det = SignType.sign (Omat ![1, 0]).det := by
    have hmaps : ∀ t ∈ Icc (-1 : ℝ) 1, (![t, 0] : Fin 2 → ℝ) ∈ KD := fun t ht =>
      (hKDmem _).2 ⟨(sq_le_one_iff_abs_le_one _).2 (abs_le.2 ht), rfl⟩
    have hct : Continuous (fun t : ℝ => (![t, 0] : Fin 2 → ℝ)) := by
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact continuous_id
      · exact continuous_const
    exact portPrivate_bdd04f55_sign_eq_of_continuousOn_nonzero (fun t => (Omat ![t, 0]).det) (-1) 1 (by norm_num)
      (hOc.comp hct.continuousOn hmaps) fun t ht => hOdet _ (hmaps t ht)
  let Qm : (Fin 2 → ℝ) → Matrix (Fin ℓ) (Fin ℓ) ℝ := fun y =>
    Matrix.of fun a b => (AR y).mulVec (SL y b) (Fin.cast hkp.symm a)
  have hlin : ∀ (φ : (Fin (D.chart q hq).k → ℝ) →L[ℝ] ℝ) (v' : Fin (D.chart q hq).k → ℝ),
      ∑ k, φ (Pi.single k 1) * v' k = φ v' := by
    intro φ v'
    conv_rhs => rw [← Finset.univ_sum_single v']
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (v' k) : Fin (D.chart q hq).k → ℝ) = v' k • Pi.single k 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], φ.map_smul, smul_eq_mul, mul_comm]
  have hcorner : ∀ (y : Fin 2 → ℝ) (w : Fin (D.chart q hq).k → ℝ), y ∈ KD → y ∈ KA →
      w ∈ D.sardZeros p hq ε c hp → Sg w = Wd.ψ y →
      SignType.sign (Omat y).det *
        SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w).det =
        SignType.sign (Qm y).det := by
    intro y w hyD hyA hwZ hSgw
    obtain ⟨⟨hw0, hland⟩, -, hzero⟩ := hwZ
    have hw0' : w ≠ 0 := hw0
    obtain ⟨u, hwu, hu, hdu, hO⟩ := hOU y hyD w hw0' hSgw
    have hland' : D.landing p hq ε c ε w ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
      (D.chart p hp).image_lt_subset_image_ball (D.chart p hp).hRR'.le hland
    let X : (Fin (D.chart q hq).k → ℝ) → (Fin n → ℝ) :=
      fun w => (D.chart p hp).χ.symm (D.landing p hq ε c ε w)
    have hXd : DifferentiableAt ℝ X w := by
      have c3 := ((D.contMDiff_flow (c - (f p + ε))).contMDiffAt).comp w (hSgs w hw0')
      have c4 := ((D.chart p hp).contMDiffAt_symm hland').comp w c3
      exact (contMDiffAt_iff_contDiffAt.1 c4).differentiableAt (by simp)
    have hv0 : posPart (D.chart p hp).hk (X w) ≠ 0 := by
      apply ModelField.posPart_ne_zero_of_lt_nf (D.chart p hp).hk (c := f p)
      have hland2 : D.landing p hq ε c ε w ∈
          (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).R} :=
        image_mono (fun y (hy : morseNorm n y < (D.chart p hp).R) => le_of_lt hy) hland
      rw [← (D.chart p hp).f_eq_nf_symm hland2,
        GradientLikeStrip.f_landing hp hf hε hε hRq hc₁.le hc₂.le hU hw0']
      linarith only [hε]
    have hn0 : negPart (D.chart p hp).hk (X w) = 0 :=
      (ModelField.scaledNegativePart_eq_zero_iff (D.chart p hp).hk hv0).1 hzero
    have hS : HasFDerivAt (D.sardMap p hq ε c ε hp)
        (‖posPart (D.chart p hp).hk (X w)‖ •
          ((ModelField.negPartL (D.chart p hp).hk).comp (fderiv ℝ X w))) w := by
      have h1 := (ModelField.hasFDerivAt_scaledNegativePart (D.chart p hp).hk hv0).comp w hXd.hasFDerivAt
      refine h1.congr_fderiv ?_
      ext1 v'
      simp [ModelField.scaledNegativePartDeriv_apply, hn0]
    have hSray : fderiv ℝ (D.sardMap p hq ε c ε hp) w w = 0 := by
      have h1 : HasDerivAt (fun t : ℝ => D.sardMap p hq ε c ε hp (t • w))
          (fderiv ℝ (D.sardMap p hq ε c ε hp) w w) 1 := by
        have h2 : HasDerivAt (fun t : ℝ => t • w) w 1 := by
          simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
        have h3 : HasFDerivAt (D.sardMap p hq ε c ε hp) (fderiv ℝ (D.sardMap p hq ε c ε hp) w)
            ((1 : ℝ) • w) := by
          rw [one_smul]; exact hS.differentiableAt.hasFDerivAt
        exact h3.comp_hasDerivAt (1 : ℝ) h2
      have h4 : HasDerivAt (fun t : ℝ => D.sardMap p hq ε c ε hp (t • w)) 0 1 := by
        refine (hasDerivAt_const (1 : ℝ) (D.sardMap p hq ε c ε hp w)).congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
        change ModelField.scaledNegativePart _ ((D.chart p hp).χ.symm (D.landing p hq ε c ε (t • w))) =
          ModelField.scaledNegativePart _ ((D.chart p hp).χ.symm (D.landing p hq ε c ε w))
        rw [D.landing_smul p hq ε c ε ht hw0']
      exact h1.unique h4
    have hRCd' : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k))
        (D.rightCoord p hp ε) (Sg w) := by rw [hSgw]; exact hRCd y hyA
    have hnhds : ∀ᶠ w' in 𝓝 w, w' ≠ 0 := isOpen_ne.mem_nhds hw0'
    have hRCSg : HasFDerivAt (fun w' => D.rightCoord p hp ε (Sg w'))
        ((ModelField.negPartL (D.chart p hp).hk).comp (fderiv ℝ X w)) w := by
      refine ((ModelField.negPartL _).hasFDerivAt.comp w hXd.hasFDerivAt).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with w' hw'
      change negPart (D.chart p hp).hk ((D.chart p hp).χ.symm
        (D.flow (f (Sg w') - (f p + ε)) (Sg w'))) = _
      rw [hSgf w' hw']
      rfl
    have hRCchain : ∀ v', dG _ (D.rightCoord p hp ε) (Wd.ψ y)
        (mfderiv 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I Sg w v') =
        (ModelField.negPartL (D.chart p hp).hk) (fderiv ℝ X w v') := by
      intro v'
      have hA := (hRCd'.hasMFDerivAt.comp w
        ((hSgs w hw0').mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv
      have hB := (hasMFDerivAt_iff_hasFDerivAt.2 hRCSg).mfderiv
      have := congrArg (fun L => L v') (hA.symm.trans hB)
      rw [← hSgw]
      exact this
    have hSu : ∀ j, fderiv ℝ (D.sardMap p hq ε c ε hp) w (u j) =
        ‖posPart (D.chart p hp).hk (X w)‖ •
          dG _ (D.rightCoord p hp ε) (Wd.ψ y) (frameVec E y (SL y j)) := by
      intro j
      have h1 := hRCchain (u j)
      rw [hdu j] at h1
      rw [hS.fderiv, h1]
      rfl
    have hκ : 0 < Real.sqrt (2 * ε) / ‖eqv.symm w‖ :=
      div_pos (Real.sqrt_pos.2 (mul_pos two_pos hε)) (norm_pos_iff.2 ((D.chart q hq).toE_ne_zero hw0'))
    rw [hO, Matrix.det_smul, sign_mul, sign_pow, sign_pos hκ, one_pow, one_mul, mul_comm,
      ← sign_mul, ← Matrix.det_mul]
    obtain ⟨SM, hSM⟩ : ∃ M, M = SardData.matrix (D.sardMap p hq ε c ε hp) w := ⟨_, rfl⟩
    rw [← hSM]
    have hProw : ∀ i j : Fin (D.chart q hq).k, (SM * Umat w u) i j =
        if (i : ℕ) = 0 then w ⬝ᵥ (fun k => Umat w u k j) else
          if h : (i : ℕ) - 1 < (D.chart p hp).k then
            fderiv ℝ (D.sardMap p hq ε c ε hp) w (fun k => Umat w u k j) ⟨(i : ℕ) - 1, h⟩ else 0 := by
      intro i j
      rw [Matrix.mul_apply]
      by_cases hi : (i : ℕ) = 0
      · simp only [hSM, SardData.matrix, Matrix.of_apply, hi, ↓reduceIte, dotProduct]
      · by_cases h2 : (i : ℕ) - 1 < (D.chart p hp).k
        · simp only [hSM, SardData.matrix, Matrix.of_apply, hi, ↓reduceIte, h2, ↓reduceDIte]
          exact hlin ((EuclideanSpace.proj (⟨(i : ℕ) - 1, h2⟩ : Fin (D.chart p hp).k)).comp
            (fderiv ℝ (D.sardMap p hq ε c ε hp) w)) _
        · simp only [hSM, SardData.matrix, Matrix.of_apply, hi, ↓reduceIte, h2, ↓reduceDIte,
            zero_mul, Finset.sum_const_zero]
    have hcol0 : ∀ j : Fin (D.chart q hq).k, (j : ℕ) = 0 → (fun k => Umat w u k j) = w := by
      intro j hj
      funext k
      simp only [Umat, Matrix.of_apply, hj, ↓reduceDIte]
    have hcols : ∀ j : Fin (D.chart q hq).k, ∀ b : Fin ℓ, (j : ℕ) = b + 1 →
        (fun k => Umat w u k j) = u b := by
      intro j b hj
      funext k
      have hj0 : (j : ℕ) ≠ 0 := by omega
      simp only [Umat, Matrix.of_apply, hj0, ↓reduceDIte]
      have hb : (⟨(j : ℕ) - 1, by omega⟩ : Fin ℓ) = b := Fin.ext (Nat.sub_eq_of_eq_add hj)
      rw [hb]
    let e : Fin (D.chart q hq).k ≃ Fin (ℓ + 1) := finCongr hkq
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hzero_col : ∀ i : Fin ℓ, (SM * Umat w u).submatrix e.symm e.symm i.succ 0 = 0 := by
      intro i
      simp only [Matrix.submatrix_apply]
      rw [hProw]
      have h1 : ((e.symm i.succ : Fin (D.chart q hq).k) : ℕ) = i + 1 := by simp [e]
      have h2 : ((e.symm 0 : Fin (D.chart q hq).k) : ℕ) = 0 := by simp [e]
      have h3 : (i : ℕ) + 1 - 1 < (D.chart p hp).k := by omega
      simp only [h1, Nat.add_one_ne_zero, ↓reduceIte]
      rw [dite_eq_left (by omega), hcol0 _ h2, hSray]
      rfl
    simp only [hzero_col, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have h00 : (SM * Umat w u).submatrix e.symm e.symm 0 0 = w ⬝ᵥ w := by
      simp only [Matrix.submatrix_apply]
      rw [hProw]
      have h2 : ((e.symm 0 : Fin (D.chart q hq).k) : ℕ) = 0 := by simp [e]
      simp only [h2, ↓reduceIte]
      rw [hcol0 _ h2]
    have hsub : ((SM * Umat w u).submatrix e.symm e.symm).submatrix (Fin.succAbove 0) Fin.succ =
        ‖posPart (D.chart p hp).hk (X w)‖ • Qm y := by
      ext a b
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Matrix.smul_apply, smul_eq_mul]
      rw [hProw]
      have h1 : ((e.symm a.succ : Fin (D.chart q hq).k) : ℕ) = a + 1 := by simp [e]
      have h2 : ((e.symm b.succ : Fin (D.chart q hq).k) : ℕ) = b + 1 := by simp [e]
      simp only [h1, Nat.add_one_ne_zero, ↓reduceIte]
      rw [dite_eq_left (by omega), hcols _ b h2, hSu b]
      have h4 : (⟨(a : ℕ) + 1 - 1, by omega⟩ : Fin (D.chart p hp).k) = Fin.cast hkp.symm a :=
        Fin.ext (by simp)
      simp only [h4]
      change ‖_‖ * _ = ‖_‖ * (AR y).mulVec (SL y b) (Fin.cast hkp.symm a)
      rw [← hArow]
      rfl
    have hww : 0 < w ⬝ᵥ w := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
      (Ne.symm fun h => hw0' (dotProduct_self_eq_zero.1 h))
    rw [h00, hsub, Matrix.det_smul, Fintype.card_fin, Fin.val_zero, pow_zero, one_mul, sign_mul,
      sign_mul, sign_pow, sign_pos hww, sign_pos (norm_pos_iff.2 hv0), one_pow, one_mul, one_mul]
  have hSRi : ∀ y ∈ KA, LinearIndependent ℝ (SR y) := fun y hy => by
    have h := (hindR y hy).comp Fin.succ (Fin.succ_injective _)
    simpa using h
  have hkerSR : ∀ y ∈ KA, ∀ c' : Fin (n - 1) → ℝ, (AR y).mulVec c' = 0 →
      c' ∈ Submodule.span ℝ (Set.range (SR y)) := by
    intro y hy c' hc'
    have hle : Submodule.span ℝ (Set.range (SR y)) ≤ LinearMap.ker (Matrix.mulVecLin (AR y)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hSRA y hy i
    have hker : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (AR y))) = n - 1 - ℓ := by
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (AR y))
      have htop : LinearMap.range (Matrix.mulVecLin (AR y)) = ⊤ :=
        LinearMap.range_eq_top.2 (hARs y hy)
      rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
      omega
    have heq := Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_eq_card (hSRi y hy), Fintype.card_fin, hker])
    rw [heq]
    exact hc'
  let Nmat : (Fin 2 → ℝ) → Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun y =>
    Matrix.of fun a k => if h : (a : ℕ) < ℓ then AR y (Fin.cast hkp.symm ⟨a, h⟩) k else
      SR y ⟨(a : ℕ) - ℓ, by omega⟩ k
  have hNdet : ∀ y ∈ KA, (Nmat y).det ≠ 0 := by
    intro y hy h0
    obtain ⟨c', hc0, hc'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc0
    have hA : (AR y).mulVec c' = 0 := by
      funext a
      have := congrFun hc' ⟨a, by have := a.isLt; omega⟩
      have ha : (a : ℕ) < ℓ := by have := a.isLt; omega
      simp only [Matrix.mulVec, Nmat, dotProduct, Matrix.of_apply, ha, ↓reduceDIte, Fin.cast_mk,
        Fin.eta, Pi.zero_apply] at this
      exact this
    have hB : ∀ b, SR y b ⬝ᵥ c' = 0 := by
      intro b
      have := congrFun hc' ⟨ℓ + b, by have := b.isLt; omega⟩
      have hb : ¬ (ℓ + (b : ℕ) < ℓ) := by omega
      simp only [Matrix.mulVec, Nmat, dotProduct, Matrix.of_apply, hb, ↓reduceDIte,
        Nat.add_sub_cancel_left, Fin.eta, Pi.zero_apply] at this
      exact this
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hkerSR y hy c' hA)
    have hcc : c' ⬝ᵥ c' = 0 := by
      conv_lhs => arg 1; rw [← hβ]
      rw [sum_dotProduct]
      exact Finset.sum_eq_zero fun b _ => by rw [smul_dotProduct, hB b, smul_zero]
    exact dotProduct_self_eq_zero.1 hcc
  have hNc : ContinuousOn (fun y => (Nmat y).det) KA := by
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun k => ?_
    by_cases ha : (a : ℕ) < ℓ
    · simp only [Matrix.of_apply, ha, ↓reduceDIte]
      exact continuousOn_pi.1 (continuousOn_pi.1 hARc _) k
    · simp only [Matrix.of_apply, ha, ↓reduceDIte]
      exact continuousOn_pi.1 (continuousOn_pi.1 hSRc _) k
  have hy₁KA : (![-1, 0] : Fin 2 → ℝ) ∈ KA := by
    change (![-1, 0] : Fin 2 → ℝ) ∈ whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> norm_num
  have hy₂KA : (![1, 0] : Fin 2 → ℝ) ∈ KA := by
    change (![1, 0] : Fin 2 → ℝ) ∈ whitneyHalf ∩ {y | y 0 ^ 2 + y 1 ^ 2 = 1}
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> norm_num
  have hNsgn : SignType.sign (Nmat ![-1, 0]).det = SignType.sign (Nmat ![1, 0]).det := by
    have hmaps : ∀ t ∈ Icc (0 : ℝ) Real.pi, ζ (fun _ => t) ∈ KA :=
      fun t ht => @hζKA (fun _ => t) ((hKΘmem (fun _ => t)).2 ht)
    have hct : Continuous (fun t : ℝ => ζ (fun _ => t)) :=
      hζc.comp (continuous_pi fun _ => continuous_id)
    have h := portPrivate_bdd04f55_sign_eq_of_continuousOn_nonzero (fun t => (Nmat (ζ (fun _ => t))).det) 0 Real.pi Real.pi_pos.le
      (hNc.comp hct.continuousOn hmaps) fun t ht => hNdet _ (hmaps t ht)
    have hz0 : ζ (fun _ => 0) = ![1, 0] := by
      rw [hζdef]; simp only [Real.cos_zero, Real.sin_zero]
    have hzπ : ζ (fun _ => Real.pi) = ![-1, 0] := by
      rw [hζdef]; simp only [Real.cos_pi, Real.sin_pi]
    rw [hz0, hzπ] at h
    exact h.symm
  have hC1 : ∀ y ∈ KD, y ∈ KA → SignType.sign (blockMat (SL y) (SR y)).det *
      SignType.sign (Nmat y).det = SignType.sign (Qm y).det := by
    intro y _ hyA
    exact portPrivate_bdd04f55_sign_blockMat_mul_kernel_complement (by omega) hkp (AR y) (SL y) (SR y)
      (hSRi y hyA) (hSRA y hyA)
  have hcs₁ := hcorner ![-1, 0] w₁ hy₁KD hy₁KA hw₁ Wd.corner₁.symm
  have hcs₂ := hcorner ![1, 0] w₂ hy₂KD hy₂KA hw₂ Wd.corner₂.symm
  have hC₁ := hC1 ![-1, 0] hy₁KD hy₁KA
  have hC₂ := hC1 ![1, 0] hy₂KD hy₂KA
  have hs₁' : SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w₁).det = 1 := by
    have h := hs₁
    unfold sardSign SardData.sign at h
    generalize SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w₁).det = σ at h ⊢
    revert h
    cases σ <;> decide
  have hs₂' : SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w₂).det = -1 := by
    have h := hs₂
    unfold sardSign SardData.sign at h
    generalize SignType.sign (SardData.matrix (D.sardMap p hq ε c ε hp) w₂).det = σ at h ⊢
    revert h
    cases σ <;> decide
  have hOne : SignType.sign (Omat ![-1, 0]).det ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]; exact hOdet _ hy₁KD
  have hNne : SignType.sign (Nmat ![-1, 0]).det ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]; exact hNdet _ hy₁KA
  have key : ∀ x₁ x₂ o nn : SignType, x₁ * nn = o * 1 → x₂ * nn = o * (-1) → o ≠ 0 → nn ≠ 0 →
      x₁ = -x₂ ∧ x₁ ≠ 0 := by decide
  rw [hs₁'] at hcs₁
  rw [hs₂', ← hOsgn] at hcs₂
  rw [← hNsgn] at hC₂
  obtain ⟨hsign, hne⟩ := key _ _ _ _ (hC₁.trans hcs₁.symm) (hC₂.trans hcs₂.symm) hOne hNne
  have hdetne : (blockMat (SL ![-1, 0]) (SR ![-1, 0])).det ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hne
    exact hne rfl
  refine ⟨T, SL, SR, ⟨hTc, hTi, hSLc, hSRc, fun y hy h1 => hindL y ⟨hy, h1⟩, fun y hy h1 => ?_,
    fun y hy h1 => hindR y ⟨hy, h1⟩, fun y hy h1 => ?_, hsign, hdetne⟩,
    hTv, fun y hy h1 i => (hkerA _ _ y _).2 (hSLA y ⟨hy, h1⟩ i),
    fun y hy h1 i => (hkerA _ _ y _).2 (hSRA y ⟨hy, h1⟩ i)⟩
  · simp only [hSLdef, ↓reduceDIte]
  · simp only [hSRdef, ↓reduceDIte]
    rfl

theorem levelFields_of_normalFrame (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {x₁ x₂ : M} (Wd : D.WhitneyDisc c hp hq ε x₁ x₂)
    (Fr : (Fin 2 → ℝ) → Fin (n - 3) → (Fin n → ℝ))
    (hFc : ∀ j, ContinuousOn (fun y => (⟨Wd.ψ y, Fr y j⟩ : TangentBundle I M)) whitneyHalf)
    (hFf : ∀ y ∈ whitneyHalf, ∀ j, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (Fr y j) = 0)
    (hFr : ∀ y ∈ whitneyHalf, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
          ∑ j : Fin (n - 3), coordN v (2 + j) • (id (Fr y j) : TangentSpace I (Wd.ψ y))))
    (hFA : ∀ y ∈ whitneyHalf, y 1 = 0 → ∀ j : Fin (n - 3), (j : ℕ) + 1 < ℓ →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (Wd.ψ y)
        (Fr y j) = 0)
    (hFB : ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 → ∀ j : Fin (n - 3), ℓ ≤ (j : ℕ) + 1 →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (Wd.ψ y)
        (Fr y j) = 0) :
    ∃ Ys : Fin (n - 3) → LevelField I f,
      (∀ y ∈ whitneyHalf, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
          ∑ j : Fin (n - 3), coordN v (2 + j) • (Ys j).Y (Wd.ψ y))) ∧
      (∀ y ∈ Wd.W, y 1 = 0 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3), (j : ℕ) + 1 < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z
          ((Ys j).Y z) = 0) ∧
      ∀ y ∈ Wd.W, y 0 ^ 2 + y 1 ^ 2 = 1 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3),
        ℓ ≤ (j : ℕ) + 1 →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z
          ((Ys j).Y z) = 0 := by
  classical
  have _hidx : (D.chart p hp).k = ℓ ∧ 2 ≤ ℓ ∧ ℓ + 3 ≤ n := ⟨hkp, hℓ, hℓn⟩
  have hn3 : 3 ≤ n := by omega
  have hKW : whitneyHalf ⊆ Wd.W := Wd.half_subset
  have hK : IsCompact whitneyHalf := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · change IsClosed ({y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩ {y | 0 ≤ y 1})
      exact (isClosed_le (f := fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) (by fun_prop)
        continuous_const).inter (isClosed_le (f := fun _ : Fin 2 → ℝ => (0 : ℝ))
        (g := fun y : Fin 2 → ℝ => y 1) continuous_const (by fun_prop))
    · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_
      intro y hy
      obtain ⟨h1, h2⟩ := hy
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      rw [Fin.forall_fin_two, Real.norm_eq_abs, Real.norm_eq_abs]
      constructor
      · exact abs_le.2 ⟨by nlinarith [sq_nonneg (y 1)], by nlinarith [sq_nonneg (y 1)]⟩
      · exact abs_le.2 ⟨by nlinarith [sq_nonneg (y 0)], by nlinarith [sq_nonneg (y 0)]⟩
  have hKc : Convex ℝ whitneyHalf := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg hs ht, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
  have hψK : ContinuousOn Wd.ψ whitneyHalf := Wd.smooth.continuousOn.mono hKW
  obtain ⟨hε, -, -, hrmp, hrmq, -, hU⟩ := hv
  have hfp : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hfq : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hreg : ∀ y ∈ whitneyHalf, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) ≠ 0 := by
    intro y hy h0
    have hc : f (Wd.ψ y) = c := Wd.level y (hKW hy)
    have hu := D.unit (Wd.ψ y) (by
        simp only [mem_preimage, mem_Icc, hc]
        constructor <;> linarith [hfp.1, hfq.2])
      (fun x hx => hU (Wd.ψ y) ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩ x hx)
    rw [h0] at hu
    simp at hu
  obtain ⟨E, hEc, hE⟩ := exists_levelFrame_along (I := I) hf hK hKc hψK hreg
  have hEf : ∀ y ∈ whitneyHalf, ∀ j, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (E y j) = 0 :=
    fun y hy => (hE y hy).1
  have hEi : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (E y) := fun y hy => (hE y hy).2
  have hEs : ∀ y ∈ whitneyHalf, ∀ v : TangentSpace I (Wd.ψ y),
      mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) v = 0 → v ∈ Submodule.span ℝ (Set.range (E y)) := by
    intro y hy v hv
    let Lc : (Fin n → ℝ) →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y)
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := Lc.toLinearMap
    have hle : Submodule.span ℝ (Set.range (E y)) ≤ LinearMap.ker L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact LinearMap.mem_ker.2 (hEf y hy k)
    have hL0 : L ≠ 0 := by
      intro h0
      apply hreg y hy
      have h1 : Lc = 0 :=
        ContinuousLinearMap.coe_injective (h0.trans ContinuousLinearMap.toLinearMap_zero.symm)
      exact h1
    have hr1 : Module.finrank ℝ (LinearMap.range L) = 1 := by
      have h1 : Module.finrank ℝ (LinearMap.range L) ≤ 1 :=
        (Submodule.finrank_le _).trans (Module.finrank_self ℝ).le
      have h2 : Module.finrank ℝ (LinearMap.range L) ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
        exact hL0
      omega
    have hker : Module.finrank ℝ (LinearMap.ker L) = n - 1 := by
      have := LinearMap.finrank_range_add_finrank_ker L
      rw [Module.finrank_fin_fun, hr1] at this
      omega
    have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range (E y))) = n - 1 := by
      rw [finrank_span_eq_card (hEi y hy), Fintype.card_fin]
    have heq := Submodule.eq_of_le_of_finrank_eq hle (hspan.trans hker.symm)
    have hv' : (show Fin n → ℝ from v) ∈ LinearMap.ker L := LinearMap.mem_ker.2 hv
    rw [← heq] at hv'
    exact hv'
  have hcoefF : ∀ j : Fin (n - 3), ∃ cf : (Fin 2 → ℝ) → Fin (n - 1) → ℝ,
      ContinuousOn cf whitneyHalf ∧ ∀ y ∈ whitneyHalf, ∑ k, cf y k • E y k = Fr y j := fun j =>
    exists_continuousOn_frameCoeff hψK hEc hEi (hFc j) (fun y hy => hEs y hy _ (hFf y hy j))
  choose cF hcFc hcFe using hcoefF
  have hdψc : ∀ i : Fin 2, ContinuousOn (fun y => (⟨Wd.ψ y,
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (Pi.single i 1) : Fin n → ℝ)⟩ : TangentBundle I M))
      whitneyHalf := by
    intro i
    have hT := Wd.smooth.continuousOn_tangentMapWithin (by simp) Wd.isOpen_W.uniqueMDiffOn
    have hin : ContinuousOn (fun y : Fin 2 → ℝ =>
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Fin 2 → ℝ)).symm (y, Pi.single i 1) :
          TangentBundle 𝓘(ℝ, Fin 2 → ℝ) (Fin 2 → ℝ))) Wd.W :=
      ((tangentBundleModelSpaceHomeomorph _).symm.continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn
    have hcomp := hT.comp hin (fun y hy => hy)
    refine (hcomp.congr fun y hy => ?_).mono hKW
    change _ = (⟨Wd.ψ y, mfderivWithin 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ Wd.W y (Pi.single i 1)⟩ :
      TangentBundle I M)
    rw [mfderivWithin_of_isOpen Wd.isOpen_W hy]
  have hdψf : ∀ y ∈ whitneyHalf, ∀ w : Fin 2 → ℝ,
      mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y w) = 0 := by
    intro y hy w
    have hyW := hKW hy
    have hψd : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y :=
      ((Wd.smooth y hyW).contMDiffAt (Wd.isOpen_W.mem_nhds hyW)).mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Wd.ψ y) := (hf (Wd.ψ y)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp y hfd hψd
    have hev : (f ∘ Wd.ψ) =ᶠ[𝓝 y] fun _ => c := by
      filter_upwards [Wd.isOpen_W.mem_nhds hyW] with z hz using Wd.level z hz
    have h0 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (f ∘ Wd.ψ) y = 0 := by
      rw [hev.mfderiv_eq]
      simp
    have := congrArg (fun L => L w) (hcomp.symm.trans h0)
    exact this
  have hcoefT : ∀ i : Fin 2, ∃ cf : (Fin 2 → ℝ) → Fin (n - 1) → ℝ,
      ContinuousOn cf whitneyHalf ∧ ∀ y ∈ whitneyHalf, ∑ k, cf y k • E y k =
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (Pi.single i 1) : Fin n → ℝ) := fun i =>
    exists_continuousOn_frameCoeff hψK hEc hEi (hdψc i) (fun y hy => hEs y hy _ (hdψf y hy _))
  choose cT hcTc hcTe using hcoefT
  let Φ : (Fin 2 → Fin (n - 1) → ℝ) × (Fin (n - 3) → Fin (n - 1) → ℝ) →
      (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ) := fun P v =>
    ∑ i : Fin 2, coordN v i • P.1 i + ∑ j : Fin (n - 3), coordN v (2 + j) • P.2 j
  have hcoord : ∀ (v : Fin (n - 1) → ℝ) (m : ℕ),
      coordN v m = ∑ t, v t * coordN (Pi.single t (1 : ℝ)) m := by
    intro v m
    unfold coordN
    split_ifs with h
    · simp [Pi.single_apply]
    · simp
  have hΦlin : ∀ P (v : Fin (n - 1) → ℝ), Φ P v = ∑ t, v t • Φ P (Pi.single t 1) := by
    intro P v
    simp only [Φ, hcoord v, Finset.sum_smul, smul_add, Finset.smul_sum, smul_smul,
      Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_comm
  have hΦ0 : ∀ P, Φ P 0 = 0 := by
    intro P
    simp [Φ, coordN]
  have hinjiff : ∀ P, Function.Injective (Φ P) ↔
      LinearIndependent ℝ (fun t : Fin (n - 1) => Φ P (Pi.single t 1)) := by
    intro P
    rw [Fintype.linearIndependent_iff]
    constructor
    · intro hP g hg
      have : Φ P g = Φ P 0 := by rw [hΦlin, hg, hΦ0]
      intro t
      exact congrFun (hP this) t
    · intro hP v w hvw
      have h1 : ∑ t, (v t - w t) • Φ P (Pi.single t 1) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hΦlin, hvw, sub_self]
      funext t
      exact sub_eq_zero.1 (hP _ h1 t)
  let U := {P : (Fin 2 → Fin (n - 1) → ℝ) × (Fin (n - 3) → Fin (n - 1) → ℝ) |
    Function.Injective (Φ P)}
  have hUo : IsOpen U := by
    have hc : Continuous fun P : (Fin 2 → Fin (n - 1) → ℝ) × (Fin (n - 3) → Fin (n - 1) → ℝ) =>
        fun t : Fin (n - 1) => Φ P (Pi.single t 1) := by
      refine continuous_pi fun t => ?_
      simp only [Φ]
      fun_prop
    have : U = (fun P => fun t : Fin (n - 1) => Φ P (Pi.single t 1)) ⁻¹'
        {g | LinearIndependent ℝ g} := by
      ext P
      exact hinjiff P
    rw [this]
    exact isOpen_setOfPred_linearIndependent.preimage hc
  have hfv : ∀ y, frameVec E y = Fintype.linearCombination ℝ (E y) := by
    intro y
    funext cc
    simp [frameVec, Fintype.linearCombination_apply]
  have hfvinj : ∀ y ∈ whitneyHalf, Function.Injective (frameVec E y) := by
    intro y hy a' b' hab
    have h1 : ∑ k, (a' k - b' k) • E y k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hab
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hEi y hy) _ h1 k)
  have hmap : ∀ y ∈ whitneyHalf, ∀ (C : Fin (n - 3) → Fin (n - 1) → ℝ)
      (Z : Fin (n - 3) → TangentSpace I (Wd.ψ y)), (∀ j, Z j = frameVec E y (C j)) →
      ∀ v : Fin (n - 1) → ℝ,
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
        ∑ j : Fin (n - 3), coordN v (2 + (j : ℕ)) • Z j =
        frameVec E y (Φ (fun i => cT i y, C) v) := by
    intro y hy C Z hZ v
    have he : (fun i : Fin 2 => coordN v i) =
        ∑ i : Fin 2, coordN v i • (Pi.single i (1 : ℝ) : Fin 2 → ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    let Dψ : (Fin 2 → ℝ) →L[ℝ] (Fin n → ℝ) := mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y
    let Z' : Fin (n - 3) → Fin n → ℝ := Z
    change Dψ (fun i => coordN v i) + ∑ j : Fin (n - 3), coordN v (2 + (j : ℕ)) • Z' j = _
    rw [he, map_sum]
    simp only [map_smul]
    rw [hfv y]
    simp only [Φ, map_add, map_sum, map_smul]
    rw [← hfv y]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact (hcTe i y hy).symm
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      exact hZ j
  let Pm : (Fin 2 → ℝ) → (Fin 2 → Fin (n - 1) → ℝ) × (Fin (n - 3) → Fin (n - 1) → ℝ) :=
    fun y => (fun i => cT i y, fun j => cF j y)
  have hPc : ContinuousOn Pm whitneyHalf :=
    (continuousOn_pi.2 hcTc).prodMk (continuousOn_pi.2 hcFc)
  have hPU : Pm '' whitneyHalf ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    have hZ : ∀ j, (id (Fr y j) : TangentSpace I (Wd.ψ y)) = frameVec E y (cF j y) :=
      fun j => (hcFe j y hy).symm
    have h2 : Function.Injective (frameVec E y ∘ Φ (Pm y)) := by
      intro v w hvw
      apply hFr y hy
      exact (hmap y hy (fun j => cF j y) _ hZ v).trans
        (hvw.trans (hmap y hy (fun j => cF j y) _ hZ w).symm)
    exact h2.of_comp
  obtain ⟨δ, hδ, hδU⟩ := (hK.image_of_continuousOn hPc).exists_thickening_subset_open hUo hPU
  have hRq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    nlinarith [(D.hrm q hq).2, D.rm_pos q hq]
  have hac : a ≤ c := by linarith [hfp.1]
  have hcb : c ≤ b := by linarith [hfq.2]
  have hRp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by
    nlinarith [(D.hrm p hp).2, D.rm_pos p hp]
  obtain ⟨OL, hOL, hSOL, hGL, hsubL⟩ := leftCoord_submersion hf D hq hε (by linarith) hac hc₂.le
    (fun z hz x hx => hU z ⟨by linarith [hz.1], hz.2⟩ x hx)
  obtain ⟨OR, hOR, hSOR, hGR, hsubR⟩ := rightCoord_submersion hf D hp hε (by linarith) hc₁.le hcb
    (fun z hz x hx => hU z ⟨hz.1, by linarith [hz.2]⟩ x hx)
  have hYex : ∀ j : Fin (n - 3), ∃ Y : LevelField I f,
      (∀ y ∈ whitneyHalf, ∃ c' : Fin (n - 1) → ℝ, Y.Y (Wd.ψ y) = frameVec E y c' ∧
        ∀ k, |c' k - cF j y k| < δ) ∧
      ((j : ℕ) + 1 < ℓ → ∀ z ∈ D.leftSphere q hq ε c, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z'
          (Y.Y z') = 0) ∧
      (ℓ ≤ (j : ℕ) + 1 → ∀ z ∈ D.rightSphere p hp ε c, ∃ N ∈ 𝓝 z, ∀ z' ∈ N,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z'
          (Y.Y z') = 0) := by
    intro j
    by_cases hj : (j : ℕ) + 1 < ℓ
    · obtain ⟨Y, hYt, hYa⟩ := exists_levelField_approx hf hOL hGL
        (D.isCompact_leftSphere q hq hRq c).isClosed hSOL (fun z hz => (hsubL z hz).2) hK hψK
        (Wd.inj.mono hKW) hreg hEc hEf hEi hEs (hcFc j) (fun y hy hS => by
          rw [show frameVec E y (cF j y) = Fr y j from hcFe j y hy]
          exact hFA y hy ((Wd.memA y (hKW hy)).1 hS) j hj) hδ
      exact ⟨Y, hYa, fun _ => hYt, fun h => absurd h (by omega)⟩
    · obtain ⟨Y, hYt, hYa⟩ := exists_levelField_approx hf hOR hGR
        (D.isCompact_rightSphere p hp hRp c).isClosed hSOR (fun z hz => (hsubR z hz).2) hK hψK
        (Wd.inj.mono hKW) hreg hEc hEf hEi hEs (hcFc j) (fun y hy hS => by
          rw [show frameVec E y (cF j y) = Fr y j from hcFe j y hy]
          exact hFB y hy ((Wd.memB y (hKW hy)).1 hS) j (by omega)) hδ
      exact ⟨Y, hYa, fun h => absurd h hj, fun _ => hYt⟩
  choose Ys hYa hYL hYR using hYex
  refine ⟨Ys, ?_, ?_, ?_⟩
  · intro y hy
    choose c' hc'e hc'c using fun j => hYa j y hy
    have hin : ((fun i => cT i y, c') :
        (Fin 2 → Fin (n - 1) → ℝ) × (Fin (n - 3) → Fin (n - 1) → ℝ)) ∈ U := by
      apply hδU
      rw [Metric.mem_thickening_iff]
      refine ⟨Pm y, mem_image_of_mem Pm hy, ?_⟩
      rw [Prod.dist_eq, dist_self, max_lt_iff]
      refine ⟨hδ, ?_⟩
      rw [dist_pi_lt_iff hδ]
      intro j
      rw [dist_pi_lt_iff hδ]
      intro k
      rw [Real.dist_eq]
      exact hc'c j k
    have h2 : Function.Injective (frameVec E y ∘ Φ (fun i => cT i y, c')) :=
      (hfvinj y hy).comp hin
    intro v w hvw
    apply h2
    exact (hmap y hy c' (fun j => (Ys j).Y (Wd.ψ y)) hc'e v).symm.trans
      (hvw.trans (hmap y hy c' _ hc'e w))
  · intro y hy h1
    have hmem := (Wd.memA y hy).2 h1
    have hev : ∀ j : Fin (n - 3), ∀ᶠ z in 𝓝 (Wd.ψ y), (j : ℕ) + 1 < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z
          ((Ys j).Y z) = 0 := by
      intro j
      by_cases hj : (j : ℕ) + 1 < ℓ
      · obtain ⟨N, hN, hNz⟩ := hYL j hj _ hmem
        filter_upwards [hN] with z hz _ using hNz z hz
      · exact Filter.Eventually.of_forall fun z h => absurd h hj
    exact ⟨_, Filter.eventually_all.2 hev, fun z hz j hj => hz j hj⟩
  · intro y hy h1
    have hmem := (Wd.memB y hy).2 h1
    have hev : ∀ j : Fin (n - 3), ∀ᶠ z in 𝓝 (Wd.ψ y), ℓ ≤ (j : ℕ) + 1 →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z
          ((Ys j).Y z) = 0 := by
      intro j
      by_cases hj : ℓ ≤ (j : ℕ) + 1
      · obtain ⟨N, hN, hNz⟩ := hYR j hj _ hmem
        filter_upwards [hN] with z hz _ using hNz z hz
      · exact Filter.Eventually.of_forall fun z h => absurd h hj
    exact ⟨_, Filter.eventually_all.2 hev, fun z hz j hj => hz j hj⟩

theorem exists_whitneyFrame (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    {w₁ w₂ : Fin (D.chart q hq).k → ℝ} (hw₁ : w₁ ∈ D.sardZeros p hq ε c hp)
    (hw₂ : w₂ ∈ D.sardZeros p hq ε c hp) (hs₁ : D.sardSign p hq ε c hp w₁ = 1)
    (hs₂ : D.sardSign p hq ε c hp w₂ = -1)
    (Wd : D.WhitneyDisc c hp hq ε
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₁)))
      (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w₂)))) :
    ∃ Ys : Fin (n - 3) → LevelField I f,
      (∀ y ∈ whitneyHalf, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
          ∑ j : Fin (n - 3), coordN v (2 + j) • (Ys j).Y (Wd.ψ y))) ∧
      (∀ y ∈ Wd.W, y 1 = 0 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3), (j : ℕ) + 1 < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z
          ((Ys j).Y z) = 0) ∧
      ∀ y ∈ Wd.W, y 0 ^ 2 + y 1 ^ 2 = 1 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3),
        ℓ ≤ (j : ℕ) + 1 →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z
          ((Ys j).Y z) = 0 := by
  classical
  have hHc : IsCompact whitneyHalf := by
    have hcl : IsClosed whitneyHalf := by
      have h1 : IsClosed {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} :=
        isClosed_le (by fun_prop) continuous_const
      have h2 : IsClosed {y : Fin 2 → ℝ | 0 ≤ y 1} :=
        isClosed_le continuous_const (continuous_apply 1)
      exact h1.inter h2
    refine (isCompact_closedBall (0 : Fin 2 → ℝ) 1).of_isClosed_subset hcl ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |y 0| ≤ 1
      have h0 : y 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 1)]
      exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
    · change |y 1| ≤ 1
      have h0 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0)]
      exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hHconv : Convex ℝ whitneyHalf := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg hs ht, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x 0 - y 0)),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x 1 - y 1))]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
  have hψc : ContinuousOn Wd.ψ whitneyHalf := Wd.smooth.continuousOn.mono Wd.half_subset
  have hfp : f p ∈ Ioo a b := D.inStrip p hp (D.chart p hp).p_mem_image_ball
  have hfq : f q ∈ Ioo a b := D.inStrip q hq (D.chart q hq).p_mem_image_ball
  have hreg : ∀ y ∈ whitneyHalf, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) ≠ 0 := by
    intro y hy h0
    have hlev : f (Wd.ψ y) = c := Wd.level y (Wd.half_subset hy)
    have hcIcc : c ∈ Icc a b := ⟨by linarith [hfp.1, hv.1], by linarith [hfq.2, hv.1]⟩
    have hcU : ∀ x hx, ∀ z ∈ D.smallBall x hx, f z ≠ c := by
      intro x hx z hz hzc
      exact hv.2.2.2.2.2.2 z (by rw [hzc]; exact ⟨hc₁.le, hc₂.le⟩) x hx hz
    have h1 := D.dfV_eq_neg_one_of_level hcIcc hcU hlev
    rw [dfV, h0] at h1
    simp at h1
  obtain ⟨E, hEc, hE⟩ := exists_levelFrame_along (I := I) hf hHc hHconv hψc hreg
  have hEf : ∀ y ∈ whitneyHalf, ∀ j, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (E y j) = 0 :=
    fun y hy => (hE y hy).1
  have hEi : ∀ y ∈ whitneyHalf, LinearIndependent ℝ (E y) := fun y hy => (hE y hy).2
  obtain ⟨T, SL, SR, hW, hT, hSL, hSR⟩ := whitney_corner_frames hf D hp hq hkp hkq h6 hℓ hℓn hv
    hc₁ hc₂ hw₁ hw₂ hs₁ hs₂ Wd E hEc hEf hEi
  obtain ⟨Fb, hFbc, hFbi, hFbL, hFbR⟩ := exists_normalFrame_boundary hℓ (by omega) hW
  obtain ⟨Fr', hFr'c, hFr'i, hFr'L, hFr'R⟩ := exists_normalFrame_euclid hℓ (by omega)
    (by omega) hW.contT hW.indT Fb hFbc hFbi
  let Fr : (Fin 2 → ℝ) → Fin (n - 3) → (Fin n → ℝ) := fun y j => frameVec E y (Fr' y j)
  have hFc : ∀ j, ContinuousOn (fun y => (⟨Wd.ψ y, Fr y j⟩ : TangentBundle I M)) whitneyHalf := by
    intro j
    have hcj : ContinuousOn (fun y => Fr' y j) whitneyHalf :=
      (continuous_apply j).comp_continuousOn hFr'c
    exact continuousOn_frameVec_tangentBundle hψc hEc hcj
  have hFf : ∀ y ∈ whitneyHalf, ∀ j, mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (Fr y j) = 0 := by
    intro y hy j
    refine (map_sum (mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y)).toLinearMap (fun k => Fr' y j k • E y k)
      Finset.univ).trans (Finset.sum_eq_zero fun k _ => ?_)
    refine (map_smul (mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y)).toLinearMap (Fr' y j k) (E y k)).trans ?_
    have h0 := hEf y hy k
    change Fr' y j k • mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ y) (E y k) = 0
    rw [h0, smul_zero]
  have hFA : ∀ y ∈ whitneyHalf, y 1 = 0 → ∀ j : Fin (n - 3), (j : ℕ) + 1 < ℓ →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) (Wd.ψ y)
        (Fr y j) = 0 := by
    intro y hy hy1 j hj
    change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε)
      (Wd.ψ y) (frameVec E y (Fr' y j)) = 0
    rw [hFr'L y hy hy1 j hj, hFbL y hy hy1 j hj]
    exact hSL y hy hy1 _
  have hFB : ∀ y ∈ whitneyHalf, y 0 ^ 2 + y 1 ^ 2 = 1 → ∀ j : Fin (n - 3), ℓ ≤ (j : ℕ) + 1 →
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) (Wd.ψ y)
        (Fr y j) = 0 := by
    intro y hy hy1 j hj
    change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε)
      (Wd.ψ y) (frameVec E y (Fr' y j)) = 0
    rw [hFr'R y hy hy1 j hj, hFbR y hy hy1 j hj]
    exact hSR y hy hy1 _
  have hFr : ∀ y ∈ whitneyHalf, Function.Injective (fun v : Fin (n - 1) → ℝ =>
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
        ∑ j : Fin (n - 3), coordN v (2 + j) • (id (Fr y j) : TangentSpace I (Wd.ψ y))) := by
    intro y hy
    set L := mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y with hLdef
    have hL : ∀ v : Fin (n - 1) → ℝ, (id (L (fun i => coordN v i)) : Fin n → ℝ) =
        ∑ i : Fin 2, coordN v i • frameVec E y (T y i) := by
      intro v
      have h1 : (fun i : Fin 2 => coordN v i) =
          ∑ i : Fin 2, coordN v i • (Pi.single i 1 : Fin 2 → ℝ) := by
        ext t
        fin_cases t <;> simp [Fin.sum_univ_two]
      rw [h1]
      refine (map_sum L.toLinearMap _ Finset.univ).trans (Finset.sum_congr rfl fun i _ => ?_)
      refine (map_smul L.toLinearMap _ _).trans ?_
      rw [hT y hy i]
      rfl
    have hexp : ∀ v : Fin (n - 1) → ℝ,
        (id (L (fun i => coordN v i)) : Fin n → ℝ) +
          ∑ j : Fin (n - 3), coordN v (2 + j) • frameVec E y (Fr' y j) =
        ∑ k, (∑ i : Fin 2, coordN v i * T y i k +
          ∑ j : Fin (n - 3), coordN v (2 + j) * Fr' y j k) • E y k := by
      intro v
      rw [hL v]
      simp only [frameVec, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul,
        Finset.sum_add_distrib]
      congr 1 <;> exact Finset.sum_comm
    intro v w hvw
    have h1 : ∑ k, (∑ i : Fin 2, coordN v i * T y i k +
          ∑ j : Fin (n - 3), coordN v (2 + j) * Fr' y j k) • E y k =
        ∑ k, (∑ i : Fin 2, coordN w i * T y i k +
          ∑ j : Fin (n - 3), coordN w (2 + j) * Fr' y j k) • E y k := by
      rw [← hexp v, ← hexp w]
      exact hvw
    have hc := Fintype.linearIndependent_iff.1 (hEi y hy)
      (fun k => (∑ i : Fin 2, coordN v i * T y i k +
          ∑ j : Fin (n - 3), coordN v (2 + j) * Fr' y j k) -
        (∑ i : Fin 2, coordN w i * T y i k +
          ∑ j : Fin (n - 3), coordN w (2 + j) * Fr' y j k))
      (by simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self])
    let g : Fin (2 + (n - 1 - 2)) → ℝ :=
      Fin.append (fun i : Fin 2 => coordN v i - coordN w i)
        (fun j : Fin (n - 1 - 2) => coordN v (2 + j) - coordN w (2 + j))
    have hg : ∑ i, g i • Fin.append (T y) (Fr' y) i = 0 := by
      rw [Fin.sum_univ_add]
      simp only [g, Fin.append_left, Fin.append_right]
      ext t
      have ht : (∑ i : Fin 2, coordN v i * T y i t +
          ∑ j : Fin (n - 1 - 2), coordN v (2 + j) * Fr' y j t) -
        (∑ i : Fin 2, coordN w i * T y i t +
          ∑ j : Fin (n - 1 - 2), coordN w (2 + j) * Fr' y j t) = 0 := hc t
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        sub_mul, Finset.sum_sub_distrib]
      linarith
    have hg0 := Fintype.linearIndependent_iff.1 (hFr'i y hy) g hg
    funext k
    have hvk : coordN v k = v k := by simp [coordN]
    have hwk : coordN w k = w k := by simp [coordN]
    by_cases hk : (k : ℕ) < 2
    · have h2 := hg0 (Fin.castAdd (n - 1 - 2) ⟨k, hk⟩)
      simp only [g, Fin.append_left] at h2
      linarith
    · have h2 := hg0 (Fin.natAdd 2 ⟨(k : ℕ) - 2, by have := k.isLt; omega⟩)
      simp only [g, Fin.append_right] at h2
      have e : 2 + ((k : ℕ) - 2) = k := by omega
      rw [e] at h2
      linarith
  exact levelFields_of_normalFrame hf D hp hq hkp hkq h6 hℓ hℓn hv hc₁ hc₂ Wd Fr hFc hFf hFr
    hFA hFB

theorem whitneyChart_of_frame (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ℓ : ℕ} (hkp : (D.chart p hp).k = ℓ)
    (hkq : (D.chart q hq).k = ℓ + 1) (h6 : 6 ≤ n) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    {ε c : ℝ} (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    (hrm : ∀ x hx, D.rm x hx ^ 2 < 2 * |f x - c|) {x₁ x₂ : M}
    (Wd : D.WhitneyDisc c hp hq ε x₁ x₂) (Ys : Fin (n - 3) → LevelField I f)
    (hframe : ∀ y ∈ whitneyHalf, Function.Injective (fun v : Fin (n - 1) → ℝ =>
        mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ y (fun i => coordN v i) +
          ∑ j : Fin (n - 3), coordN v (2 + j) • (Ys j).Y (Wd.ψ y)))
    (hA : ∀ y ∈ Wd.W, y 1 = 0 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3), (j : ℕ) + 1 < ℓ →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - (D.chart q hq).k))) (D.leftCoord q hq ε) z
          ((Ys j).Y z) = 0)
    (hB : ∀ y ∈ Wd.W, y 0 ^ 2 + y 1 ^ 2 = 1 → ∃ N ∈ 𝓝 (Wd.ψ y), ∀ z ∈ N, ∀ j : Fin (n - 3),
        ℓ ≤ (j : ℕ) + 1 →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (D.chart p hp).k)) (D.rightCoord p hp ε) z
          ((Ys j).Y z) = 0) :
    ∃ η κ : ℝ, 0 < η ∧ ∃ Ch : D.CollarChart c κ, Ch.U = whitneyDom (n - 1) η ∧
      (∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ D.leftSphere q hq ε c ↔ y ∈ whitneyA (n - 1) ℓ) ∧
      (∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ D.rightSphere p hp ε c ↔ y ∈ whitneyB (n - 1) ℓ) ∧
      Ch.φ (whitneyPt (n - 1) (-1)) = x₁ ∧ Ch.φ (whitneyPt (n - 1) 1) = x₂ := by
  classical
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
  have hcoordc : ∀ j, Continuous (fun y : Fin (n - 1) → ℝ => coordN y j) := by
    intro j
    unfold coordN
    split_ifs with h
    · exact continuous_apply _
    · exact continuous_const
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin 2 → ℝ) → (Fin (n - 1) → ℝ), ∀ u (i : Fin (n - 1)),
      emb u i = if (i : ℕ) = 0 then u 0 else if (i : ℕ) = 1 then u 1 else 0 :=
    ⟨fun u i => if (i : ℕ) = 0 then u 0 else if (i : ℕ) = 1 then u 1 else 0, fun _ _ => rfl⟩
  have hemb0 : ∀ u, coordN (emb u) 0 = u 0 := by
    intro u; simp [coordN, hemb, show 0 < n - 1 by omega]
  have hemb1 : ∀ u, coordN (emb u) 1 = u 1 := by
    intro u; simp [coordN, hemb, show 1 < n - 1 by omega]
  have hembj : ∀ u (j : ℕ), 2 ≤ j → coordN (emb u) j = 0 := by
    intro u j hj
    unfold coordN
    split_ifs with h
    · rw [hemb]; simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, ↓reduceIte]
    · rfl
  have hembb : ∀ u, (fun i : Fin 2 => coordN (emb u) i) = u := by
    intro u
    funext i
    fin_cases i
    · exact hemb0 u
    · exact hemb1 u
  have hembc : Continuous emb := by
    apply continuous_pi
    intro i
    have : (fun u => emb u i) = fun u : Fin 2 → ℝ =>
        if (i : ℕ) = 0 then u 0 else if (i : ℕ) = 1 then u 1 else 0 := funext fun u => hemb u i
    rw [this]
    split_ifs
    · exact continuous_apply _
    · exact continuous_apply _
    · exact continuous_const
  have hHc : IsCompact whitneyHalf := by
    apply Metric.isCompact_of_isClosed_isBounded
    · change IsClosed {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ 0 ≤ y 1}
      exact (isClosed_le (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
        continuous_const).inter (isClosed_le continuous_const (continuous_apply 1))
    · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset ?_
      intro y hy
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      have h := hy.1
      have h0 := sq_nonneg (y 0)
      have h1 := sq_nonneg (y 1)
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one] <;>
        linarith only [h, h0, h1]
  have hcN : ∀ (z : Fin (n - 1) → ℝ) (k : ℕ) (hk : k < n - 1), coordN z k = z ⟨k, hk⟩ := by
    intro z k hk
    simp [coordN, hk]
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (n - 1), (i0 : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin (n - 1), (i1 : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hc0 : ∀ z : Fin (n - 1) → ℝ, coordN z 0 = z i0 := fun z => by
    rw [hcN z 0 (by omega)]; congr 1; exact Fin.ext hi0.symm
  have hc1 : ∀ z : Fin (n - 1) → ℝ, coordN z 1 = z i1 := fun z => by
    rw [hcN z 1 (by omega)]; congr 1; exact Fin.ext hi1.symm
  have hcases : ∀ i : Fin (n - 1), i = i0 ∨ i = i1 ∨ 2 ≤ (i : ℕ) := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) 2 with h | h
    · rcases Nat.lt_or_ge (i : ℕ) 1 with h' | h'
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · exact Or.inr (Or.inr h)
  have hwp : ∀ σ : ℝ, whitneyPt (n - 1) σ = emb ![σ, 0] := by
    intro σ
    funext i
    rw [hemb]
    simp only [whitneyPt]
    by_cases h0 : (i : ℕ) = 0
    · simp only [h0, ↓reduceIte, Matrix.cons_val_zero]
    · by_cases h1 : (i : ℕ) = 1
      · simp only [h1, one_ne_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      · simp only [h0, h1, ↓reduceIte]
  have happrox : ∀ η : ℝ, 0 < η → ∀ y ∈ whitneyDom (n - 1) η, ∃ u ∈ whitneyHalf, dist y (emb u) < η ∧
      (coordN y 1 = 0 → u 1 = 0) := by
    intro η hη y hy
    obtain ⟨hy01, hy1, hyj⟩ := hy
    have hr0 : 0 < 1 + η := by linarith only [hη]
    have hy0a : |coordN y 0| < 1 + η :=
      abs_lt_of_sq_lt_sq (by linarith only [hy01, sq_nonneg (coordN y 1)]) hr0.le
    have hy1a : |coordN y 1| < 1 + η :=
      abs_lt_of_sq_lt_sq (by linarith only [hy01, sq_nonneg (coordN y 0)]) hr0.le
    have hshrink : ∀ x : ℝ, |x| < 1 + η → |x - x / (1 + η)| < η := by
      intro x hx
      have e1 : x - x / (1 + η) = x * (η / (1 + η)) := by field_simp; ring
      have hq : 0 < η / (1 + η) := div_pos hη hr0
      rw [e1, abs_mul, abs_of_pos hq]
      calc |x| * (η / (1 + η)) < (1 + η) * (η / (1 + η)) := mul_lt_mul_of_pos_right hx hq
        _ = η := by field_simp
    refine ⟨![coordN y 0 / (1 + η), max (coordN y 1) 0 / (1 + η)], ?_, ?_, ?_⟩
    · change (coordN y 0 / (1 + η)) ^ 2 + (max (coordN y 1) 0 / (1 + η)) ^ 2 ≤ 1 ∧
        0 ≤ max (coordN y 1) 0 / (1 + η)
      have hm : max (coordN y 1) 0 ^ 2 ≤ coordN y 1 ^ 2 := by
        rcases le_total (coordN y 1) 0 with h | h
        · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg _
        · rw [max_eq_left h]
      constructor
      · rw [div_pow, div_pow, ← add_div, div_le_one (by positivity)]
        linarith only [hm, hy01]
      · exact div_nonneg (le_max_right _ _) hr0.le
    · rw [dist_pi_lt_iff hη]
      intro i
      rw [hemb, Real.dist_eq]
      rcases hcases i with rfl | rfl | hi
      · simp only [hi0, ↓reduceIte, Matrix.cons_val_zero]
        rw [← hc0 y]
        exact hshrink _ hy0a
      · simp only [hi1, one_ne_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← hc1 y]
        rcases le_total (coordN y 1) 0 with h | h
        · rw [max_eq_right h, zero_div, sub_zero, abs_of_nonpos h]
          linarith only [hy1]
        · rw [max_eq_left h]
          exact hshrink _ hy1a
      · simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte, sub_zero]
        rw [← hcoordF y i]
        exact hyj i hi
    · intro h
      change max (coordN y 1) 0 / (1 + η) = 0
      rw [h, max_self, zero_div]
  have happroxB : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ y ∈ whitneyDom (n - 1) η, y ∈ whitneyB (n - 1) ℓ →
      ∃ u ∈ whitneyHalf, u 0 ^ 2 + u 1 ^ 2 = 1 ∧ dist y (emb u) < η := by
    intro η hη hη1 y hy hyB
    obtain ⟨hy01, hy1, hyj⟩ := hy
    have hcirc : coordN y 0 ^ 2 + coordN y 1 ^ 2 = 1 := hyB.1
    have hfar : ∀ i : Fin (n - 1), 2 ≤ (i : ℕ) → |y i - emb ![0, 0] i| < η := by
      intro i hi
      rw [hemb]
      simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte, sub_zero]
      rw [← hcoordF y i]
      exact hyj i hi
    have hfar' : ∀ u : Fin 2 → ℝ, ∀ i : Fin (n - 1), 2 ≤ (i : ℕ) → |y i - emb u i| < η := by
      intro u i hi
      have h := hfar i hi
      rw [hemb] at h ⊢
      simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte] at h ⊢
      exact h
    rcases le_total 0 (coordN y 1) with h1 | h1
    · refine ⟨![coordN y 0, coordN y 1], (by change _ ≤ _ ∧ _; exact ⟨hcirc.le, h1⟩), hcirc, ?_⟩
      rw [dist_pi_lt_iff hη]
      intro i
      rw [Real.dist_eq]
      rcases hcases i with rfl | rfl | hi
      · rw [hemb]; simp only [hi0, ↓reduceIte, Matrix.cons_val_zero]
        rw [← hc0 y, sub_self, abs_zero]; exact hη
      · rw [hemb]; simp only [hi1, one_ne_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← hc1 y, sub_self, abs_zero]; exact hη
      · exact hfar' _ i hi
    · have hy1sq : coordN y 1 ^ 2 < η := by
        have h2 : coordN y 1 ^ 2 < η ^ 2 := by
          rw [sq_lt_sq, abs_of_pos hη, abs_lt]; exact ⟨hy1, by linarith only [h1, hη]⟩
        have h3 : η ^ 2 ≤ η := by rw [sq]; exact mul_le_of_le_one_right hη.le hη1
        linarith only [h2, h3]
      have hy0le : |coordN y 0| ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).1 (by linarith only [hcirc, sq_nonneg (coordN y 1)])
      have hy0sq : coordN y 0 ^ 2 ≤ |coordN y 0| := by
        rw [← sq_abs]
        have := mul_le_mul_of_nonneg_left hy0le (abs_nonneg (coordN y 0))
        rw [mul_one] at this
        rw [sq]; exact this
      set σ : ℝ := if 0 ≤ coordN y 0 then 1 else -1 with hσ
      have hσ1 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
      have hσd : |coordN y 0 - σ| < η := by
        rw [hσ]
        split_ifs with h0
        · rw [abs_of_nonneg h0] at hy0sq hy0le
          rw [abs_of_nonpos (by linarith only [hy0le])]
          linarith only [hy0sq, hcirc, hy1sq]
        · rw [abs_of_neg (not_le.1 h0)] at hy0sq hy0le
          rw [abs_of_nonneg (by linarith only [hy0le])]
          linarith only [hy0sq, hcirc, hy1sq]
      refine ⟨![σ, 0], (by change σ ^ 2 + (0 : ℝ) ^ 2 ≤ 1 ∧ (0 : ℝ) ≤ 0; constructor <;> linarith only [hσ1]),
        by change σ ^ 2 + (0 : ℝ) ^ 2 = 1; linarith only [hσ1], ?_⟩
      rw [dist_pi_lt_iff hη]
      intro i
      rw [Real.dist_eq]
      rcases hcases i with rfl | rfl | hi
      · rw [hemb]; simp only [hi0, ↓reduceIte, Matrix.cons_val_zero]
        rw [← hc0 y]; exact hσd
      · rw [hemb]; simp only [hi1, one_ne_zero, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← hc1 y, sub_zero, abs_of_nonpos h1]; linarith only [hy1]
      · exact hfar' _ i hi
  have hdomo : ∀ η : ℝ, 0 < η → IsOpen (whitneyDom (n - 1) η) := by
    intro η hη
    have e1 : whitneyDom (n - 1) η =
        {y | coordN y 0 ^ 2 + coordN y 1 ^ 2 < (1 + η) ^ 2} ∩ {y | -η < coordN y 1} ∩
          ⋂ i : Fin (n - 1), {y | 2 ≤ (i : ℕ) → |y i| < η} := by
      ext y
      simp only [whitneyDom, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h0, h1, hj⟩
        exact ⟨⟨h0, h1⟩, fun i hi => by rw [← hcoordF y i]; exact hj i hi⟩
      · rintro ⟨⟨h0, h1⟩, hi⟩
        refine ⟨h0, h1, fun j hj => ?_⟩
        by_cases h : j < n - 1
        · rw [hcN y j h]; exact hi ⟨j, h⟩ hj
        · simp only [coordN, h, ↓reduceDIte, abs_zero]; exact hη
    rw [e1]
    refine ((isOpen_lt (((hcoordc 0).pow 2).add ((hcoordc 1).pow 2)) continuous_const).inter
      (isOpen_lt continuous_const (hcoordc 1))).inter (isOpen_iInter_of_finite fun i => ?_)
    by_cases hi : 2 ≤ (i : ℕ)
    · simp only [hi, true_implies]
      exact isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const
    · simp only [hi, false_implies, ofPred_true]
      exact isOpen_univ
  have hε : 0 < ε := hv.1
  have hrmp : 2 * ε < D.rm p hp ^ 2 := by linarith only [hv.2.2.2.1, hε]
  have hrmq : 2 * ε < D.rm q hq ^ 2 := by linarith only [hv.2.2.2.2.1, hε]
  have hUall := hv.2.2.2.2.2.2
  have hpS : f p ∈ Ioo a b :=
    D.inStrip p hp ⟨0, (D.chart p hp).zero_mem_ball, (D.chart p hp).hχ0⟩
  have hqS : f q ∈ Ioo a b :=
    D.inStrip q hq ⟨0, (D.chart q hq).zero_mem_ball, (D.chart q hq).hχ0⟩
  have hac : a ≤ c := by linarith only [hpS.1, hc₁, hε]
  have hcb : c ≤ b := by linarith only [hqS.2, hc₂, hε]
  have hcq : c ≤ f q - ε := hc₂.le
  have hpc : f p + ε ≤ c := hc₁.le
  have hUL : ∀ y, f y ∈ Icc c (f q - ε) → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
    hUall y ⟨by linarith only [hy.1, hc₁], hy.2⟩
  have hUR : ∀ y, f y ∈ Icc (f p + ε) c → ∀ x hx, y ∉ D.smallBall x hx := fun y hy =>
    hUall y ⟨hy.1, by linarith only [hy.2, hc₂]⟩
  obtain ⟨κ, hκ, hκa, hκb, hκrm⟩ : ∃ κ : ℝ, 0 < κ ∧ a ≤ c - κ ∧ c + κ ≤ b ∧
      ∀ x (hx : x ∈ crit), D.rm x hx ^ 2 / 2 + κ < |f x - c| := by
    have h1 : ∀ x ∈ crit, ∀ᶠ κ in 𝓝 (0 : ℝ), ∀ hx : x ∈ crit,
        D.rm x hx ^ 2 / 2 + κ < |f x - c| := by
      intro x hx
      have h0 : D.rm x hx ^ 2 / 2 + 0 < |f x - c| := by linarith only [hrm x hx]
      have hc : Continuous (fun κ : ℝ => D.rm x hx ^ 2 / 2 + κ) := by fun_prop
      filter_upwards [(hc.tendsto 0).eventually (gt_mem_nhds h0)] with κ hκ _
      exact hκ
    have h2 := (Filter.eventually_all_finset crit).2 h1
    have h3 : ∀ᶠ κ in 𝓝 (0 : ℝ), κ < c - a ∧ κ < b - c :=
      (gt_mem_nhds (by linarith only [hpS.1, hc₁, hε] : (0 : ℝ) < c - a)).and
        (gt_mem_nhds (by linarith only [hqS.2, hc₂, hε] : (0 : ℝ) < b - c))
    obtain ⟨κ, ⟨hκ2, hκ3⟩, hκ0⟩ :=
      (((h2.and h3).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
        ∀ᶠ κ in 𝓝[>] (0 : ℝ), _ ∧ κ ∈ Ioi 0).exists
    exact ⟨κ, hκ0, by linarith only [hκ3.1], by linarith only [hκ3.2], fun x hx => hκ2 x hx hx⟩
  have hstrip : a ≤ c - κ ∧ c + κ ≤ b := ⟨hκa, hκb⟩
  have hmodel : ∀ x (hx : x ∈ crit), ∀ z ∈ (D.chart x hx).χ '' {w | morseNorm n w < D.rm x hx},
      f z ∉ Icc (c - κ) (c + κ) := by
    rintro x hx _ ⟨w, hw, rfl⟩ hz
    have hwR : morseNorm n w ≤ (D.chart x hx).R := (show morseNorm n w < D.rm x hx from hw).le.trans
      (D.hrm x hx).2
    have hfz := (D.chart x hx).hnorm w hwR
    rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split] at hfz
    have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
      (D.chart x hx).hk w
    have hw0 : 0 ≤ morseNorm n w := ModelField.morseNorm_nonneg w
    have hwlt : morseNorm n w ^ 2 < D.rm x hx ^ 2 :=
      pow_lt_pow_left₀ (show morseNorm n w < D.rm x hx from hw) hw0 two_ne_zero
    have hdiff : |f ((D.chart x hx).χ w) - f x| < D.rm x hx ^ 2 / 2 := by
      have hP0 := sq_nonneg ‖negPart (D.chart x hx).hk w‖
      have hN0 := sq_nonneg ‖posPart (D.chart x hx).hk w‖
      rw [hfz, abs_lt]
      constructor <;> linarith only [hsq, hwlt, hP0, hN0]
    have h1 := hκrm x hx
    have h2 : |f x - c| ≤ |f x - f ((D.chart x hx).χ w)| + |f ((D.chart x hx).χ w) - c| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm (f x) (f ((D.chart x hx).χ w))] at h2
    have h3 : |f ((D.chart x hx).χ w) - c| ≤ κ := abs_le.2 ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
    linarith only [h1, h2, h3, hdiff]
  have hflow0 : ∀ (Z : LevelField I f) (x : M), Z.flow 0 x = x := fun Z x =>
    DifferentialGeometry.Analysis.ODE.curveAt_zero _ _ x
  have hflowC : ∀ (Z : LevelField I f) (x : M), IsMIntegralCurve (fun t => Z.flow t x) Z.Y :=
    fun Z x => DifferentialGeometry.Analysis.ODE.curveAt_integralCurve _ _ x
  have hFL : ∀ (s : ℕ) (G : M → EuclideanSpace ℝ (Fin s)) (R : Set M),
      (∀ z ∈ R, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z) →
      ∀ (r : ℕ) (Z : Fin r → LevelField I f) (t : ℕ → ℝ) (x : M),
      (∀ s' : ℕ → ℝ, (∀ j, s' j ∈ uIcc 0 (t j)) →
        (List.finRange r).foldl (fun x j => (Z j).flow (s' j) x) x ∈ R) →
      (∀ j : Fin r, t j ≠ 0 → ∀ z ∈ R,
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z ((Z j).Y z) = 0) →
      G ((List.finRange r).foldl (fun x j => (Z j).flow (t j) x) x) = G x := by
    intro s G R hGR r
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin s)) := IsBoundedSMul.continuousSMul
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
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin (n - 1) → ℝ) → M, Φ = flowChart 2 (n - 3) Ys Wd.ψ := ⟨_, rfl⟩
  obtain ⟨hsm, hlev, hder⟩ := flowChart_spec (m := n - 1) hf (show n - 1 = 2 + (n - 3) by omega)
    Ys Wd.ψ Wd.isOpen_W Wd.smooth
  set W' : Set (Fin (n - 1) → ℝ) := {y | (fun i : Fin 2 => coordN y i) ∈ Wd.W} with hW'
  have hbasec : Continuous (fun y : Fin (n - 1) → ℝ => fun i : Fin 2 => coordN y i) :=
    continuous_pi fun i => hcoordc i
  have hW'o : IsOpen W' := Wd.isOpen_W.preimage hbasec
  have hΦsm : ContMDiffOn 𝓘(ℝ, Fin (n - 1) → ℝ) I ∞ Φ W' := by rw [hΦ]; exact hsm
  have hΦcont : ContinuousOn Φ W' := hΦsm.continuousOn
  have hΦlevW : ∀ y ∈ W', f (Φ y) = c := fun y hy => by rw [hΦ, hlev]; exact Wd.level _ hy
  have hΦfold : ∀ y, Φ y = (List.finRange (n - 3)).foldl
      (fun x j => (Ys j).flow (coordN y (2 + j)) x) (Wd.ψ fun i => coordN y i) := fun y => by
    rw [hΦ]; rfl
  have hfold0 : ∀ (l : List (Fin (n - 3))) (x : M), l.foldl (fun x j => (Ys j).flow 0 x) x = x := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons j l ih => intro x; rw [List.foldl_cons, hflow0]; exact ih x
  have hΦemb : ∀ u, Φ (emb u) = Wd.ψ u := by
    intro u
    rw [hΦfold, hembb]
    have : (fun x (j : Fin (n - 3)) => (Ys j).flow (coordN (emb u) (2 + j)) x) =
        fun x j => (Ys j).flow 0 x := by
      funext x j; rw [hembj u _ (by omega)]
    rw [this, hfold0]
  have hembW' : ∀ u ∈ Wd.W, emb u ∈ W' := fun u hu => by
    change (fun i : Fin 2 => coordN (emb u) i) ∈ Wd.W
    rw [hembb]; exact hu
  have hΦd : ∀ u ∈ Wd.W, ∀ v, mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u) v =
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) I Wd.ψ u (fun i => coordN v i) +
        ∑ j : Fin (n - 3), coordN v (2 + j) • (Ys j).Y (Wd.ψ u) := by
    intro u hu v
    have h := hder (emb u) (hembW' u hu) (fun j hj => hembj u j hj) v
    rw [hembb] at h
    rw [hΦ]
    exact h
  have hΦimm : ∀ u ∈ whitneyHalf,
      Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u)) := by
    intro u hu v w hvw
    apply hframe u hu
    have h1 := hΦd u (Wd.half_subset hu) v
    have h2 := hΦd u (Wd.half_subset hu) w
    simp only
    rw [← h1, ← h2]
    exact hvw
  have hK₀c : IsCompact (emb '' whitneyHalf) := hHc.image hembc
  have hK₀W' : emb '' whitneyHalf ⊆ W' := by
    rintro _ ⟨u, hu, rfl⟩; exact hembW' u (Wd.half_subset hu)
  obtain ⟨U₀, hU₀o, hK₀U₀, hU₀W', hU₀ch⟩ := D.exists_collarChart_of_injOn hf hκ hstrip hmodel Φ
    hW'o hΦsm hΦlevW hK₀c hK₀W' (by rintro _ ⟨u, hu, rfl⟩; exact hΦimm u hu)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ h
      rw [hΦemb, hΦemb] at h
      rw [Wd.inj (Wd.half_subset hu) (Wd.half_subset hu') h])
  obtain ⟨δU, hδU, hUsub⟩ := hK₀c.exists_thickening_subset_open hU₀o hK₀U₀
  clear hsm hlev hder hΦ hmodel hκrm hframe
  have hblock : ∀ (s : ℕ) (G : M → EuclideanSpace ℝ (Fin s)) (O : Set M), IsOpen O →
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G O →
      ∀ (P : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)) (z₀ : Fin (n - 1) → ℝ) (u₀ : Fin 2 → ℝ),
      Continuous P → ContDiffAt ℝ 1 P z₀ → Function.Injective (fderiv ℝ P z₀) →
      P z₀ = emb u₀ → u₀ ∈ whitneyHalf → Wd.ψ u₀ ∈ O →
      mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ u₀) ≠ 0 →
      (∀ w : EuclideanSpace ℝ (Fin s), ∃ v : TangentSpace I (Wd.ψ u₀),
        mfderiv I 𝓘(ℝ, ℝ) f (Wd.ψ u₀) v = 0 ∧
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Wd.ψ u₀) v = w) →
      ∀ (T : Fin (n - 3) → Prop),
      (∃ N ∈ 𝓝 (Wd.ψ u₀), ∀ z ∈ N, ∀ j, T j →
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z ((Ys j).Y z) = 0) →
      ∀ e : Fin s → Fin (n - 1), Function.Injective e →
      (∀ᶠ z in 𝓝 z₀, (∀ i, z (e i) = z₀ (e i)) →
        (fun i : Fin 2 => coordN (P z) i) ∈ Wd.W ∧
          G (Wd.ψ (fun i : Fin 2 => coordN (P z) i)) = 0 ∧
          ∀ j : Fin (n - 3), coordN (P z) (2 + j) ≠ 0 → T j) →
      ∀ᶠ z in 𝓝 z₀, (G (Φ (P z)) = 0 ↔ ∀ i, z (e i) = z₀ (e i)) := by
    intro s G O hO hGs P z₀ u₀ hPc hPd hPinj hPz₀ hu₀ hψO hdg hsurj T hN e he hPlane
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin s)) := IsBoundedSMul.continuousSMul
    have : ContinuousSMul ℝ (Fin (n - 1) → ℝ) := IsBoundedSMul.continuousSMul
    obtain ⟨N, hNn, hNt⟩ := hN
    have hu₀W : u₀ ∈ Wd.W := Wd.half_subset hu₀
    have hy0W' : emb u₀ ∈ W' := hembW' u₀ hu₀W
    have hΦp : Φ (emb u₀) = Wd.ψ u₀ := hΦemb u₀
    have hRo : IsOpen (O ∩ interior N) := hO.inter isOpen_interior
    have hψR : Wd.ψ u₀ ∈ O ∩ interior N := ⟨hψO, mem_interior_iff_mem_nhds.2 hNn⟩
    have hGR : ∀ z ∈ O ∩ interior N, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G z :=
      fun z hz => ((hGs z hz.1).contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)
    have hΦca : ContinuousAt Φ (emb u₀) := hΦcont.continuousAt (hW'o.mem_nhds hy0W')
    have hpre : Φ ⁻¹' (O ∩ interior N) ∩ W' ∈ 𝓝 (emb u₀) :=
      Filter.inter_mem (hΦca.preimage_mem_nhds (by rw [hΦp]; exact hRo.mem_nhds hψR))
        (hW'o.mem_nhds hy0W')
    obtain ⟨ρ₀, hρ₀, hρ₀R⟩ := Metric.mem_nhds_iff.1 hpre
    have hy0j : ∀ i : Fin (n - 1), 2 ≤ (i : ℕ) → emb u₀ i = 0 := by
      intro i hi
      rw [hemb]
      simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte]
    set F : (Fin (n - 1) → ℝ) → EuclideanSpace ℝ (Fin s) := fun z => G (Φ (P z)) with hFdef
    have hP : ∀ᶠ z in 𝓝 z₀, (∀ j ∈ Finset.univ.image e, z j = z₀ j) → F z = 0 := by
      filter_upwards [hPlane, hPc.continuousAt.preimage_mem_nhds (by rw [hPz₀]; exact Metric.ball_mem_nhds (emb u₀) hρ₀)]
        with z hz hzb hplane'
      have hplane : ∀ i, z (e i) = z₀ (e i) := fun i =>
        hplane' (e i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      obtain ⟨hbW, hG0, hT⟩ := hz hplane
      change G (Φ (P z)) = 0
      rw [hΦfold]
      refine (hFL s G (O ∩ interior N) hGR (n - 3) Ys (fun k => coordN (P z) (2 + k))
        (Wd.ψ fun i => coordN (P z) i) ?_ ?_).trans hG0
      · intro s' hs'
        let y' : Fin (n - 1) → ℝ := fun i => if (i : ℕ) < 2 then P z i else s' ((i : ℕ) - 2)
        have hy'b : ∀ i : ℕ, i < 2 → coordN y' i = coordN (P z) i := by
          intro i hi
          simp [y', coordN, show i ≤ 1 by omega]
        have hy'j : ∀ k : ℕ, k < n - 3 → coordN y' (2 + k) = s' k := by
          intro k hk
          simp [y', coordN, show 2 + k < n - 1 by omega, show ¬ 2 + k ≤ 1 by omega]
        have hmem : y' ∈ Φ ⁻¹' (O ∩ interior N) ∩ W' := hρ₀R (by
          rw [Metric.mem_ball, dist_pi_lt_iff hρ₀]
          intro i
          have h3 := (dist_pi_lt_iff hρ₀).1 (Metric.mem_ball.1 hzb) i
          simp only [y']
          split_ifs with hi
          · exact h3
          · rw [hy0j i (by omega), Real.dist_eq, sub_zero]
            rw [hy0j i (by omega), Real.dist_eq, sub_zero] at h3
            have h1 := habs _ _ (hs' ((i : ℕ) - 2))
            have h2 : coordN (P z) (2 + ((i : ℕ) - 2)) = P z i := by
              rw [show 2 + ((i : ℕ) - 2) = (i : ℕ) by omega, hcoordF]
            simp only [h2] at h1
            linarith only [h1, h3])
        have hb' : (fun i : Fin 2 => coordN y' i) = fun i : Fin 2 => coordN (P z) i := by
          funext i; exact hy'b i i.isLt
        have h1 := hmem.1
        rw [mem_preimage, hΦfold, hb'] at h1
        have hfun : (fun x (j : Fin (n - 3)) => (Ys j).flow (coordN y' (2 + j)) x) =
            fun x j => (Ys j).flow (s' j) x := by
          funext x j
          rw [hy'j j j.isLt]
        rw [hfun] at h1
        exact h1
      · intro j hj z' hz'
        exact hNt z' (interior_subset hz'.2) j (hT j hj)
    have hΦdiff : MDifferentiableAt 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀) :=
      ((hΦsm _ hy0W').contMDiffAt (hW'o.mem_nhds hy0W')).mdifferentiableAt (by simp)
    have hGd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀)) := by
      rw [hΦp]; exact hGR _ hψR
    have hGΦ : ContMDiffAt 𝓘(ℝ, Fin (n - 1) → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ (G ∘ Φ)
        (emb u₀) := by
      have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) ∞ G (Φ (emb u₀)) := by
        rw [hΦp]; exact (hGs _ hψO).contMDiffAt (hO.mem_nhds hψO)
      exact h1.comp (emb u₀) ((hΦsm _ hy0W').contMDiffAt (hW'o.mem_nhds hy0W'))
    have hGΦd : ContDiffAt ℝ 1 (G ∘ Φ) (P z₀) := by
      rw [hPz₀]; exact (contMDiffAt_iff_contDiffAt.1 hGΦ).of_le (by simp)
    have hF : ContDiffAt ℝ 1 F z₀ := hGΦd.comp z₀ hPd
    have hFdiff : DifferentiableAt ℝ ((G ∘ Φ) ∘ P) z₀ := (hGΦd.comp z₀ hPd).differentiableAt one_ne_zero
    have hvan : ∀ u : Fin (n - 1) → ℝ, (∀ i, u (e i) = 0) → fderiv ℝ F z₀ u = 0 := by
      intro u hu
      have hline : HasDerivAt (fun t : ℝ => z₀ + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z₀
      have h1 : HasDerivAt (fun t : ℝ => F (z₀ + t • u)) (fderiv ℝ F z₀ u) 0 := by
        have hFd : HasFDerivAt F (fderiv ℝ F z₀) (z₀ + (0 : ℝ) • u) := by
          rw [zero_smul, add_zero]; exact hFdiff.hasFDerivAt
        exact hFd.comp_hasDerivAt 0 hline
      have hc0 : Tendsto (fun t : ℝ => z₀ + t • u) (𝓝 0) (𝓝 z₀) :=
        (by fun_prop : Continuous fun t : ℝ => z₀ + t • u).tendsto' 0 z₀ (by simp)
      have h2 : (fun t : ℝ => F (z₀ + t • u)) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [hc0.eventually hP] with t ht
        apply ht
        intro j hj
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
        simp [hu i]
      exact h1.unique ((hasDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ (Fin s))).congr_of_eventuallyEq h2)
    have hchain : ∀ v, fderiv ℝ F z₀ v = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀))
        (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀) (fderiv ℝ P z₀ v)) := by
      intro v
      have hGΦdiff : DifferentiableAt ℝ (G ∘ Φ) (P z₀) := hGΦd.differentiableAt one_ne_zero
      have e1 : F = (G ∘ Φ) ∘ P := rfl
      rw [e1, fderiv_comp z₀ hGΦdiff (hPd.differentiableAt one_ne_zero)]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [hPz₀]
      have hc := mfderiv_comp (emb u₀) hGd hΦdiff
      rw [mfderiv_eq_fderiv] at hc
      exact DFunLike.congr_fun hc (fderiv ℝ P z₀ v)
    have hgd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ (emb u₀)) := (hf _).mdifferentiableAt (by simp)
    have hloc : (f ∘ Φ) =ᶠ[𝓝 (emb u₀)] fun _ => c := by
      filter_upwards [hW'o.mem_nhds hy0W'] with y hy using hΦlevW y hy
    have hdgA : ∀ u, mfderiv I 𝓘(ℝ, ℝ) f (Φ (emb u₀))
        (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀) u) = 0 := by
      intro u
      have h1 := mfderiv_comp (emb u₀) hgd hΦdiff
      rw [hloc.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero] at h1
      have h2 := DFunLike.congr_fun h1 u
      exact h2.symm
    have hinj : ∀ v : Fin (n - 1) → ℝ, (∀ j, j ∉ Finset.univ.image e → v j = 0) →
        fderiv ℝ F z₀ v = 0 → v = 0 := by
      intro v hv hFv
      have hdg' : mfderiv I 𝓘(ℝ, ℝ) f (Φ (emb u₀)) ≠ 0 := by rw [hΦp]; exact hdg
      have hsurj' : ∀ w : EuclideanSpace ℝ (Fin s), ∃ v' : TangentSpace I (Φ (emb u₀)),
          mfderiv I 𝓘(ℝ, ℝ) f (Φ (emb u₀)) v' = 0 ∧
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀)) v' = w := by
        rw [hΦp]; exact hsurj
      have hAinj : Function.Injective
          ((mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀)).toLinearMap ∘ₗ
            (fderiv ℝ P z₀).toLinearMap) :=
        (hΦimm u₀ hu₀).comp hPinj
      refine hLA s ((mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀)).toLinearMap ∘ₗ
            (fderiv ℝ P z₀).toLinearMap)
        (mfderiv I 𝓘(ℝ, ℝ) f (Φ (emb u₀))).toLinearMap
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀))).toLinearMap
        hAinj (fun u => hdgA _) ?_ hsurj' e he ?_ v hv ?_
      · intro h
        apply hdg'
        exact ContinuousLinearMap.coe_injective h
      · intro q hq
        change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀))
          (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀)
            (fderiv ℝ P z₀ (fun j => if q = j then 1 else 0))) = 0
        rw [← hchain]
        apply hvan
        intro i
        rw [ite_eq_right_iff]
        rintro rfl
        exact absurd ⟨i, rfl⟩ hq
      · change mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin s)) G (Φ (emb u₀))
          (mfderiv 𝓘(ℝ, Fin (n - 1) → ℝ) I Φ (emb u₀) (fderiv ℝ P z₀ v)) = 0
        rw [← hchain]
        exact hFv
    filter_upwards [zero_set_eq_of_fderiv F z₀ hF (Finset.univ.image e) hP hinj] with z hz
    change F z = 0 ↔ _
    rw [hz]
    simp
  clear hFL hLA hΦfold
  have hLnear : ∀ t ∈ Icc (-1 : ℝ) 1, ∃ ρ > 0, ∀ y, dist y (emb ![t, 0]) < ρ →
      (Φ y ∈ D.leftSphere q hq ε c ↔ y ∈ whitneyA (n - 1) ℓ) := by
    intro t ht
    set u₀ : Fin 2 → ℝ := ![t, 0] with hu₀def
    have hu₀1 : u₀ 1 = 0 := rfl
    have hu₀ : u₀ ∈ whitneyHalf := by
      change t ^ 2 + (0 : ℝ) ^ 2 ≤ 1 ∧ (0 : ℝ) ≤ 0
      have := (sq_le_one_iff_abs_le_one t).2 (abs_le.2 ⟨ht.1, ht.2⟩)
      constructor
      · linarith only [this]
      · exact le_rfl
    have hu₀W := Wd.half_subset hu₀
    have hψL : Wd.ψ u₀ ∈ D.leftSphere q hq ε c := (Wd.memA u₀ hu₀W).2 hu₀1
    obtain ⟨O, hO, hSO, hGs, hsub⟩ := leftCoord_submersion hf D hq hε hrmq hac hcq hUL
    obtain ⟨-, hLball⟩ :=
      (mem_leftSphere_iff_coord hf D hq hε hrmq hac hcq hUL (Wd.level u₀ hu₀W)).1 hψL
    let e : Fin (n - (D.chart q hq).k) → Fin (n - 1) :=
      fun i => ⟨if (i : ℕ) = 0 then 1 else i + ℓ, by have := i.isLt; split_ifs <;> omega⟩
    have he : Function.Injective e := by
      intro i i' h
      have h' := congrArg Fin.val h
      simp only [e] at h'
      apply Fin.ext
      split_ifs at h' <;> omega
    have he0 : ∀ i : Fin (n - (D.chart q hq).k), (i : ℕ) = 0 → ((e i : Fin (n - 1)) : ℕ) = 1 := by
      intro i hi; simp [e, hi]
    have he1 : ∀ i : Fin (n - (D.chart q hq).k), (i : ℕ) ≠ 0 →
        ((e i : Fin (n - 1)) : ℕ) = i + ℓ := by
      intro i hi; simp [e, hi]
    have hembe : ∀ i, emb u₀ (e i) = 0 := by
      intro i
      rw [hemb]
      by_cases hi : (i : ℕ) = 0
      · simp only [he0 i hi, one_ne_zero, ↓reduceIte]
        exact hu₀1
      · simp only [he1 i hi, show (i : ℕ) + ℓ ≠ 0 by omega, show (i : ℕ) + ℓ ≠ 1 by omega,
          ↓reduceIte]
    have hy0W' := hembW' u₀ hu₀W
    have hPlane : ∀ᶠ z in 𝓝 (emb u₀), (∀ i, z (e i) = emb u₀ (e i)) →
        (fun i : Fin 2 => coordN (id z) i) ∈ Wd.W ∧
          D.leftCoord q hq ε (Wd.ψ (fun i : Fin 2 => coordN (id z) i)) = 0 ∧
          ∀ j : Fin (n - 3), coordN (id z) (2 + j) ≠ 0 → (j : ℕ) + 1 < ℓ := by
      filter_upwards [hW'o.mem_nhds hy0W'] with z hz hpl
      simp only [hembe] at hpl
      simp only [id]
      have hz1 : coordN z 1 = 0 := by
        have h := hpl ⟨0, by omega⟩
        rw [hcN z 1 (by omega)]
        have h2 : e ⟨0, by omega⟩ = ⟨1, by omega⟩ := Fin.ext (he0 _ rfl)
        rw [h2] at h
        exact h
      have hbW : (fun i : Fin 2 => coordN z i) ∈ Wd.W := hz
      refine ⟨hbW, ?_, ?_⟩
      · have hmem : Wd.ψ (fun i : Fin 2 => coordN z i) ∈ D.leftSphere q hq ε c :=
          (Wd.memA _ hbW).2 hz1
        exact ((mem_leftSphere_iff_coord hf D hq hε hrmq hac hcq hUL (Wd.level _ hbW)).1 hmem).1
      · intro j hj
        by_contra hjl
        apply hj
        have := j.isLt
        have h := hpl ⟨2 + j - ℓ, by omega⟩
        have h2 : e ⟨2 + j - ℓ, by omega⟩ = ⟨2 + j, by omega⟩ :=
          Fin.ext (by rw [he1 _ (by change 2 + (j : ℕ) - ℓ ≠ 0; omega)]; change 2 + (j : ℕ) - ℓ + ℓ = 2 + j; omega)
        rw [h2] at h
        rw [hcN z _ (by omega)]
        exact h
    have hblk := hblock _ (D.leftCoord q hq ε) O hO hGs id (emb u₀) u₀ continuous_id contDiffAt_id
      (by rw [fderiv_id]; exact fun a b h => h) rfl hu₀ (hSO hψL) (hsub _ hψL).1 (hsub _ hψL).2
      (fun j => (j : ℕ) + 1 < ℓ) (hA u₀ hu₀W hu₀1) e he hPlane
    have hball : ∀ᶠ z in 𝓝 (emb u₀), D.flow (c - (f q - ε)) (Φ z) ∈
        (D.chart q hq).χ '' {w | morseNorm n w < D.rm q hq} := by
      have hopen := (D.chart q hq).isOpen_image_of_lt (D.rm_lt_R' q hq).le
      have hca : ContinuousAt (fun z => D.flow (c - (f q - ε)) (Φ z)) (emb u₀) :=
        (D.continuous_flow _).continuousAt.comp (hΦcont.continuousAt (hW'o.mem_nhds hy0W'))
      exact hca.preimage_mem_nhds (hopen.mem_nhds (by simp only [hΦemb]; exact hLball))
    have hlev0 : ∀ᶠ z in 𝓝 (emb u₀), f (Φ z) = c := by
      filter_upwards [hW'o.mem_nhds hy0W'] with z hz using hΦlevW z hz
    have hev : ∀ᶠ z in 𝓝 (emb u₀),
        (Φ z ∈ D.leftSphere q hq ε c ↔ z ∈ whitneyA (n - 1) ℓ) := by
      filter_upwards [hblk, hball, hlev0] with z hz1 hz2 hz3
      rw [mem_leftSphere_iff_coord hf D hq hε hrmq hac hcq hUL hz3, and_iff_left hz2]
      simp only [id] at hz1
      rw [hz1]
      simp only [hembe]
      change (∀ i, z (e i) = 0) ↔ coordN z 1 = 0 ∧ ∀ j, ℓ + 1 ≤ j → coordN z j = 0
      constructor
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · have h1 := h ⟨0, by omega⟩
          rw [hcN z 1 (by omega)]
          have h2 : e ⟨0, by omega⟩ = ⟨1, by omega⟩ := Fin.ext (he0 _ rfl)
          rw [h2] at h1
          exact h1
        · by_cases hjn : j < n - 1
          · have h1 := h ⟨j - ℓ, by omega⟩
            have h2 : e ⟨j - ℓ, by omega⟩ = ⟨j, hjn⟩ :=
              Fin.ext (by rw [he1 _ (by change j - ℓ ≠ 0; omega)]; change j - ℓ + ℓ = j; omega)
            rw [h2] at h1
            rw [hcN z j hjn]
            exact h1
          · simp [coordN, hjn]
      · rintro ⟨h1, hj⟩ i
        by_cases hi : (i : ℕ) = 0
        · have h2 : e i = ⟨1, by omega⟩ := Fin.ext (he0 i hi)
          rw [h2, ← hcN z 1]
          exact h1
        · have h2 : e i = ⟨i + ℓ, by have := i.isLt; omega⟩ := Fin.ext (he1 i hi)
          rw [h2, ← hcN z]
          exact hj _ (by omega)
    obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ρ, hρ, fun y hy => hρs hy⟩
  have hRnear : ∀ u₀ ∈ whitneyHalf, u₀ 0 ^ 2 + u₀ 1 ^ 2 = 1 → ∃ ρ > 0, ∀ y,
      dist y (emb u₀) < ρ → (Φ y ∈ D.rightSphere p hp ε c ↔ y ∈ whitneyB (n - 1) ℓ) := by
    intro u₀ hu₀ hcirc
    have hu₀W := Wd.half_subset hu₀
    have hy0W' := hembW' u₀ hu₀W
    have hψR : Wd.ψ u₀ ∈ D.rightSphere p hp ε c := (Wd.memB u₀ hu₀W).2 hcirc
    obtain ⟨O, hO, hSO, hGs, hsub⟩ := rightCoord_submersion hf D hp hε hrmp hpc hcb hUR
    obtain ⟨-, hRball⟩ :=
      (mem_rightSphere_iff_coord hf D hp hε hrmp hpc hcb hUR (Wd.level u₀ hu₀W)).1 hψR
    obtain ⟨P, hP⟩ : ∃ P : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ), ∀ z i, P z i =
        if (i : ℕ) = 0 then u₀ 0 * (z i0 + √(1 - z i1 ^ 2)) - u₀ 1 * z i1
        else if (i : ℕ) = 1 then u₀ 1 * (z i0 + √(1 - z i1 ^ 2)) + u₀ 0 * z i1 else z i :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ), ∀ y i, Q y i =
        if (i : ℕ) = 0 then (u₀ 0 * y i0 + u₀ 1 * y i1) - √(1 - (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2)
        else if (i : ℕ) = 1 then -u₀ 1 * y i0 + u₀ 0 * y i1 else y i :=
      ⟨_, fun _ _ => rfl⟩
    have hP0 : ∀ z, P z i0 = u₀ 0 * (z i0 + √(1 - z i1 ^ 2)) - u₀ 1 * z i1 := fun z => by
      rw [hP]; simp only [hi0, ↓reduceIte]
    have hP1 : ∀ z, P z i1 = u₀ 1 * (z i0 + √(1 - z i1 ^ 2)) + u₀ 0 * z i1 := fun z => by
      rw [hP]; simp only [hi1, one_ne_zero, ↓reduceIte]
    have hPj : ∀ z (i : Fin (n - 1)), 2 ≤ (i : ℕ) → P z i = z i := fun z i hi => by
      rw [hP]; simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte]
    have hQ0 : ∀ y, Q y i0 = (u₀ 0 * y i0 + u₀ 1 * y i1) -
        √(1 - (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2) := fun y => by
      rw [hQ]; simp only [hi0, ↓reduceIte]
    have hQ1 : ∀ y, Q y i1 = -u₀ 1 * y i0 + u₀ 0 * y i1 := fun y => by
      rw [hQ]; simp only [hi1, one_ne_zero, ↓reduceIte]
    have hQj : ∀ y (i : Fin (n - 1)), 2 ≤ (i : ℕ) → Q y i = y i := fun y i hi => by
      rw [hQ]; simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte]
    have hQP : ∀ z, Q (P z) = z := by
      intro z
      have h1 : u₀ 0 * P z i0 + u₀ 1 * P z i1 = z i0 + √(1 - z i1 ^ 2) := by
        rw [hP0, hP1]; linear_combination (z i0 + √(1 - z i1 ^ 2)) * hcirc
      have h2 : -u₀ 1 * P z i0 + u₀ 0 * P z i1 = z i1 := by
        rw [hP0, hP1]; linear_combination (z i1) * hcirc
      funext i
      rcases hcases i with rfl | rfl | hi
      · rw [hQ0, h1, h2]; ring
      · rw [hQ1, h2]
      · rw [hQj _ _ hi, hPj _ _ hi]
    have hPQ : ∀ y, P (Q y) = y := by
      intro y
      have h1 : Q y i0 + √(1 - Q y i1 ^ 2) = u₀ 0 * y i0 + u₀ 1 * y i1 := by
        rw [hQ0, hQ1]; ring
      funext i
      rcases hcases i with rfl | rfl | hi
      · rw [hP0, h1, hQ1]; linear_combination (y i) * hcirc
      · rw [hP1, h1, hQ1]; linear_combination (y i) * hcirc
      · rw [hPj _ _ hi, hQj _ _ hi]
    have hPz : P 0 = emb u₀ := by
      funext i
      rw [hemb]
      rcases hcases i with rfl | rfl | hi
      · rw [hP0]; simp [hi0]
      · rw [hP1]; simp [hi1]
      · rw [hPj _ _ hi]
        simp only [show (i : ℕ) ≠ 0 by omega, show (i : ℕ) ≠ 1 by omega, ↓reduceIte, Pi.zero_apply]
    have hQz : Q (emb u₀) = 0 := by rw [← hPz, hQP]
    have hPc : Continuous P := by
      apply continuous_pi
      intro i
      rcases hcases i with rfl | rfl | hi
      · simp only [hP0]; fun_prop
      · simp only [hP1]; fun_prop
      · simp only [hPj _ _ hi]; fun_prop
    have hQc : Continuous Q := by
      apply continuous_pi
      intro i
      rcases hcases i with rfl | rfl | hi
      · simp only [hQ0]; fun_prop
      · simp only [hQ1]; fun_prop
      · simp only [hQj _ _ hi]; fun_prop
    have ha0 : ∀ x : Fin (n - 1) → ℝ, ContDiffAt ℝ 1 (fun z : Fin (n - 1) → ℝ => z i0) x :=
      fun x => (contDiff_apply ℝ ℝ i0).contDiffAt
    have ha1 : ∀ x : Fin (n - 1) → ℝ, ContDiffAt ℝ 1 (fun z : Fin (n - 1) → ℝ => z i1) x :=
      fun x => (contDiff_apply ℝ ℝ i1).contDiffAt
    have hsqd : ContDiffAt ℝ 1 (fun z : Fin (n - 1) → ℝ => √(1 - z i1 ^ 2)) 0 :=
      (contDiffAt_const.sub ((ha1 0).pow 2)).sqrt (by simp)
    have hPd : ContDiffAt ℝ 1 P 0 := by
      apply contDiffAt_pi.2
      intro i
      rcases hcases i with rfl | rfl | hi
      · simp only [hP0]
        exact (contDiffAt_const.mul ((ha0 0).add hsqd)).sub (contDiffAt_const.mul (ha1 0))
      · simp only [hP1]
        exact (contDiffAt_const.mul ((ha0 0).add hsqd)).add (contDiffAt_const.mul (ha1 0))
      · simp only [hPj _ _ hi]
        exact (contDiff_apply ℝ ℝ i).contDiffAt
    have hQd : DifferentiableAt ℝ Q (P 0) := by
      have hw1 : ContDiffAt ℝ 1 (fun y : Fin (n - 1) → ℝ => -u₀ 1 * y i0 + u₀ 0 * y i1) (P 0) :=
        (contDiffAt_const.mul (ha0 _)).add (contDiffAt_const.mul (ha1 _))
      have hs : ContDiffAt ℝ 1 (fun y : Fin (n - 1) → ℝ =>
          √(1 - (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2)) (P 0) := by
        refine (contDiffAt_const.sub (hw1.pow 2)).sqrt ?_
        have e1 : -u₀ 1 * P 0 i0 + u₀ 0 * P 0 i1 = 0 := by
          have := congrArg (fun y => y i1) (hQP 0)
          simp only [hQ1] at this
          rw [this]; rfl
        rw [e1]; norm_num
      apply differentiableAt_pi.2
      intro i
      rcases hcases i with rfl | rfl | hi
      · simp only [hQ0]
        exact (((contDiffAt_const.mul (ha0 _)).add (contDiffAt_const.mul (ha1 _))).sub
          hs).differentiableAt one_ne_zero
      · simp only [hQ1]
        exact hw1.differentiableAt one_ne_zero
      · simp only [hQj _ _ hi]
        exact ((contDiff_apply ℝ ℝ i).contDiffAt (x := P 0) (n := 1)).differentiableAt one_ne_zero
    have hPinj : Function.Injective (fderiv ℝ P 0) := by
      have hcomp := fderiv_comp (0 : Fin (n - 1) → ℝ) hQd (hPd.differentiableAt one_ne_zero)
      have hid : Q ∘ P = id := funext hQP
      rw [hid, fderiv_id] at hcomp
      intro v w hvw
      have h3 := congrArg (fderiv ℝ Q (P 0)) hvw
      have h1 := DFunLike.congr_fun hcomp v
      have h2 := DFunLike.congr_fun hcomp w
      simp only [ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.coe_comp,
        Function.comp_apply] at h1 h2
      rw [h1, h2]
      exact h3
    let e : Fin (D.chart p hp).k → Fin (n - 1) :=
      fun i => ⟨if (i : ℕ) = 0 then 0 else i + 1, by have := i.isLt; split_ifs <;> omega⟩
    have he : Function.Injective e := by
      intro i i' h
      have h' := congrArg Fin.val h
      simp only [e] at h'
      apply Fin.ext
      split_ifs at h' <;> omega
    have he0 : ∀ i : Fin (D.chart p hp).k, (i : ℕ) = 0 → e i = i0 := fun i hi =>
      Fin.ext (by simp [e, hi, hi0])
    have he1 : ∀ i : Fin (D.chart p hp).k, (i : ℕ) ≠ 0 → ((e i : Fin (n - 1)) : ℕ) = i + 1 := by
      intro i hi; simp [e, hi]
    have hPlane : ∀ᶠ z in 𝓝 (0 : Fin (n - 1) → ℝ),
        (∀ i, z (e i) = (0 : Fin (n - 1) → ℝ) (e i)) →
        (fun i : Fin 2 => coordN (P z) i) ∈ Wd.W ∧
          D.rightCoord p hp ε (Wd.ψ (fun i : Fin 2 => coordN (P z) i)) = 0 ∧
          ∀ j : Fin (n - 3), coordN (P z) (2 + j) ≠ 0 → ℓ ≤ (j : ℕ) + 1 := by
      have hPt : Tendsto P (𝓝 0) (𝓝 (emb u₀)) := hPc.tendsto' 0 _ hPz
      have hit : Tendsto (fun z : Fin (n - 1) → ℝ => z i1) (𝓝 0) (𝓝 0) :=
        (continuous_apply i1).tendsto' 0 0 rfl
      filter_upwards [hPt.eventually (hW'o.mem_nhds hy0W'),
        hit.eventually (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))]
        with z hzW hz1 hpl
      have hz0 : z i0 = 0 := by
        have h := hpl ⟨0, by omega⟩
        rw [he0 _ rfl] at h
        exact h
      have hbW : (fun i : Fin 2 => coordN (P z) i) ∈ Wd.W := hzW
      have hz1' : 0 ≤ 1 - z i1 ^ 2 := by
        have := (sq_le_one_iff_abs_le_one (z i1)).2 (abs_le.2 ⟨hz1.1.le, hz1.2.le⟩)
        linarith only [this]
      have hcircz : (fun i : Fin 2 => coordN (P z) i) 0 ^ 2 +
          (fun i : Fin 2 => coordN (P z) i) 1 ^ 2 = 1 := by
        change coordN (P z) 0 ^ 2 + coordN (P z) 1 ^ 2 = 1
        rw [hc0, hc1, hP0, hP1, hz0, zero_add]
        have hs := Real.sq_sqrt hz1'
        linear_combination (√(1 - z i1 ^ 2) ^ 2 + z i1 ^ 2) * hcirc + hs
      refine ⟨hbW, ?_, ?_⟩
      · have hmem := (Wd.memB _ hbW).2 hcircz
        exact ((mem_rightSphere_iff_coord hf D hp hε hrmp hpc hcb hUR (Wd.level _ hbW)).1 hmem).1
      · intro j hj
        by_contra hjl
        apply hj
        have := j.isLt
        have h := hpl ⟨1 + j, by omega⟩
        have h2 : e ⟨1 + j, by omega⟩ = ⟨2 + j, by omega⟩ :=
          Fin.ext (by rw [he1 _ (by change 1 + (j : ℕ) ≠ 0; omega)]; change 1 + (j : ℕ) + 1 = 2 + j; omega)
        rw [h2] at h
        rw [hcN (P z) _ (by omega), hPj _ _ (by change 2 ≤ 2 + (j : ℕ); omega)]
        exact h
    have hblk := hblock _ (D.rightCoord p hp ε) O hO hGs P 0 u₀ hPc hPd hPinj hPz hu₀ (hSO hψR)
      (hsub _ hψR).1 (hsub _ hψR).2 (fun j => ℓ ≤ (j : ℕ) + 1) (hB u₀ hu₀W hcirc) e he hPlane
    have hQt : Tendsto Q (𝓝 (emb u₀)) (𝓝 0) := hQc.tendsto' _ _ hQz
    have hembi0 : emb u₀ i0 = u₀ 0 := by rw [hemb]; simp [hi0]
    have hembi1 : emb u₀ i1 = u₀ 1 := by rw [hemb]; simp [hi1]
    have hw0 : ∀ᶠ y in 𝓝 (emb u₀), 0 < u₀ 0 * y i0 + u₀ 1 * y i1 := by
      have hcont : Continuous (fun y : Fin (n - 1) → ℝ => u₀ 0 * y i0 + u₀ 1 * y i1) := by fun_prop
      have hval : u₀ 0 * emb u₀ i0 + u₀ 1 * emb u₀ i1 = 1 := by
        rw [hembi0, hembi1]; linear_combination hcirc
      exact (hcont.tendsto' _ 1 hval).eventually (lt_mem_nhds zero_lt_one)
    have hw1 : ∀ᶠ y in 𝓝 (emb u₀), (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2 < 1 := by
      have hcont : Continuous (fun y : Fin (n - 1) → ℝ => (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2) := by
        fun_prop
      have hval : (-u₀ 1 * emb u₀ i0 + u₀ 0 * emb u₀ i1) ^ 2 = 0 := by
        rw [hembi0, hembi1]; ring
      exact (hcont.tendsto' _ 0 hval).eventually (gt_mem_nhds zero_lt_one)
    have hball : ∀ᶠ z in 𝓝 (emb u₀), D.flow (c - (f p + ε)) (Φ z) ∈
        (D.chart p hp).χ '' {w | morseNorm n w < D.rm p hp} := by
      have hopen := (D.chart p hp).isOpen_image_of_lt (D.rm_lt_R' p hp).le
      have hca : ContinuousAt (fun z => D.flow (c - (f p + ε)) (Φ z)) (emb u₀) :=
        (D.continuous_flow _).continuousAt.comp (hΦcont.continuousAt (hW'o.mem_nhds hy0W'))
      exact hca.preimage_mem_nhds (hopen.mem_nhds (by simp only [hΦemb]; exact hRball))
    have hlev0 : ∀ᶠ z in 𝓝 (emb u₀), f (Φ z) = c := by
      filter_upwards [hW'o.mem_nhds hy0W'] with z hz using hΦlevW z hz
    have hev : ∀ᶠ y in 𝓝 (emb u₀),
        (Φ y ∈ D.rightSphere p hp ε c ↔ y ∈ whitneyB (n - 1) ℓ) := by
      filter_upwards [hQt.eventually hblk, hw0, hw1, hball, hlev0] with y h1 h2 h3 h4 h5
      rw [hPQ y] at h1
      rw [mem_rightSphere_iff_coord hf D hp hε hrmp hpc hcb hUR h5, and_iff_left h4, h1]
      simp only [Pi.zero_apply]
      change _ ↔ coordN y 0 ^ 2 + coordN y 1 ^ 2 = 1 ∧ ∀ j, 2 ≤ j → j ≤ ℓ → coordN y j = 0
      rw [hc0, hc1]
      have hkey : Q y i0 = 0 ↔ y i0 ^ 2 + y i1 ^ 2 = 1 := by
        rw [hQ0, sub_eq_zero]
        have hww : (u₀ 0 * y i0 + u₀ 1 * y i1) ^ 2 + (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2 =
            y i0 ^ 2 + y i1 ^ 2 := by
          linear_combination (y i0 ^ 2 + y i1 ^ 2) * hcirc
        constructor
        · intro h
          rw [← hww, h, Real.sq_sqrt (by linarith only [h3])]
          ring
        · intro h
          rw [show 1 - (-u₀ 1 * y i0 + u₀ 0 * y i1) ^ 2 = (u₀ 0 * y i0 + u₀ 1 * y i1) ^ 2 by
            linarith only [hww, h], Real.sqrt_sq h2.le]
      constructor
      · intro h
        refine ⟨hkey.1 (by have h' := h ⟨0, by omega⟩; rwa [he0 _ rfl] at h'), fun j hj2 hjl => ?_⟩
        have h' := h ⟨j - 1, by omega⟩
        have he' : e ⟨j - 1, by omega⟩ = ⟨j, by omega⟩ :=
          Fin.ext (by rw [he1 _ (by change j - 1 ≠ 0; omega)]; change j - 1 + 1 = j; omega)
        rw [he', hQj _ _ (by change 2 ≤ j; omega)] at h'
        rw [hcN y j (by omega)]
        exact h'
      · rintro ⟨h0, hj⟩ i
        by_cases hi : (i : ℕ) = 0
        · rw [he0 i hi]
          exact hkey.2 h0
        · have he' : e i = ⟨i + 1, by have := i.isLt; omega⟩ := Fin.ext (he1 i hi)
          rw [he', hQj _ _ (by change 2 ≤ (i : ℕ) + 1; omega), ← hcN y]
          exact hj _ (by omega) (by have := i.isLt; omega)
    obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ρ, hρ, fun y hy => hρs hy⟩
  clear hblock hA hB hΦd hΦimm hUL hUR hUall hflow0 hflowC hfold0 hcN hcases hc0 hc1 hemb0 hemb1 hembj hembb habs
  have hSLc : IsClosed (D.leftSphere q hq ε c) :=
    (D.isCompact_leftSphere q hq (hrmq.le.trans (pow_le_pow_left₀ (D.rm_pos q hq).le (D.hrm q hq).2 2)) c).isClosed
  have hSRc : IsClosed (D.rightSphere p hp ε c) :=
    (D.isCompact_rightSphere p hp (hrmp.le.trans (pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2)) c).isClosed
  have hu2 : ∀ u : Fin 2 → ℝ, u = ![u 0, u 1] := by
    intro u; funext i; fin_cases i <;> rfl
  set KA := emb '' (whitneyHalf ∩ {u | u 1 = 0}) with hKA
  set KB := emb '' (whitneyHalf ∩ {u | u 0 ^ 2 + u 1 ^ 2 = 1}) with hKB
  have hKAc : IsCompact KA :=
    (hHc.inter_right (isClosed_eq (continuous_apply 1) continuous_const)).image hembc
  have hKBc : IsCompact KB :=
    (hHc.inter_right (isClosed_eq (by fun_prop) continuous_const)).image hembc
  have hKAi : KA ⊆ interior {y | Φ y ∈ D.leftSphere q hq ε c ↔ y ∈ whitneyA (n - 1) ℓ} := by
    rintro _ ⟨u, ⟨hu, hu1⟩, rfl⟩
    have ht : u 0 ∈ Icc (-1 : ℝ) 1 := by
      have h := hu.1
      have h1 : u 1 = 0 := hu1
      rw [h1] at h
      have := (sq_le_one_iff_abs_le_one (u 0)).1 (by linarith only [h])
      exact abs_le.1 this
    obtain ⟨ρ, hρ, hρs⟩ := hLnear (u 0) ht
    have hue : emb ![u 0, 0] = emb u := by rw [← (show u 1 = 0 from hu1), ← hu2]
    rw [hue] at hρs
    exact mem_interior_iff_mem_nhds.2 (Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun y hy => hρs y hy⟩)
  have hKBi : KB ⊆ interior {y | Φ y ∈ D.rightSphere p hp ε c ↔ y ∈ whitneyB (n - 1) ℓ} := by
    rintro _ ⟨u, ⟨hu, hu1⟩, rfl⟩
    obtain ⟨ρ, hρ, hρs⟩ := hRnear u hu hu1
    exact mem_interior_iff_mem_nhds.2 (Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun y hy => hρs y hy⟩)
  obtain ⟨δA, hδA, hAsub⟩ := hKAc.exists_thickening_subset_open isOpen_interior hKAi
  obtain ⟨δB, hδB, hBsub⟩ := hKBc.exists_thickening_subset_open isOpen_interior hKBi
  clear hLnear hRnear hKAi hKBi
  have hVAo : IsOpen (W' ∩ Φ ⁻¹' (D.leftSphere q hq ε c)ᶜ) :=
    hΦcont.isOpen_inter_preimage hW'o hSLc.isOpen_compl
  have hVBo : IsOpen (W' ∩ Φ ⁻¹' (D.rightSphere p hp ε c)ᶜ) :=
    hΦcont.isOpen_inter_preimage hW'o hSRc.isOpen_compl
  have hFA : emb '' whitneyHalf \ Metric.thickening (δA / 2) KA ⊆
      W' ∩ Φ ⁻¹' (D.leftSphere q hq ε c)ᶜ := by
    rintro _ ⟨⟨u, hu, rfl⟩, hnot⟩
    refine ⟨hK₀W' ⟨u, hu, rfl⟩, fun hmem => hnot ?_⟩
    rw [hΦemb] at hmem
    have hu1 := (Wd.memA u (Wd.half_subset hu)).1 hmem
    exact Metric.self_subset_thickening (by positivity) _ ⟨u, ⟨hu, hu1⟩, rfl⟩
  have hFB : emb '' whitneyHalf \ Metric.thickening (δB / 2) KB ⊆
      W' ∩ Φ ⁻¹' (D.rightSphere p hp ε c)ᶜ := by
    rintro _ ⟨⟨u, hu, rfl⟩, hnot⟩
    refine ⟨hK₀W' ⟨u, hu, rfl⟩, fun hmem => hnot ?_⟩
    rw [hΦemb] at hmem
    have hu1 := (Wd.memB u (Wd.half_subset hu)).1 hmem
    exact Metric.self_subset_thickening (by positivity) _ ⟨u, ⟨hu, hu1⟩, rfl⟩
  obtain ⟨δA', hδA', hA'sub⟩ :=
    (hK₀c.diff Metric.isOpen_thickening).exists_thickening_subset_open hVAo hFA
  obtain ⟨δB', hδB', hB'sub⟩ :=
    (hK₀c.diff Metric.isOpen_thickening).exists_thickening_subset_open hVBo hFB
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min δU (min (δA / 2) (min (δB / 2) (min δA' (min δB' 1)))) :=
    ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]
    exact lt_min hδU (lt_min (half_pos hδA) (lt_min (half_pos hδB) (lt_min hδA' (lt_min hδB' one_pos))))
  obtain ⟨hηU, h'⟩ := le_min_iff.1 (hηdef.le)
  obtain ⟨hηA, h'⟩ := le_min_iff.1 h'
  obtain ⟨hηB, h'⟩ := le_min_iff.1 h'
  obtain ⟨hηA', h'⟩ := le_min_iff.1 h'
  obtain ⟨hηB', hη1⟩ := le_min_iff.1 h'
  have hdomU : whitneyDom (n - 1) η ⊆ U₀ := fun y hy => by
    obtain ⟨u, hu, hdist, -⟩ := happrox η hη y hy
    exact hUsub (Metric.mem_thickening_iff.2 ⟨emb u, ⟨u, hu, rfl⟩, hdist.trans_le hηU⟩)
  obtain ⟨Ch, hChU, hChφ⟩ := hU₀ch _ hdomU (hdomo η hη)
  refine ⟨η, κ, hη, Ch, hChU, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hChφ]
    by_cases hyA : y ∈ Metric.thickening δA KA
    · have h := interior_subset (hAsub hyA)
      exact h
    · obtain ⟨u, hu, hdist, hu1⟩ := happrox η hη y hy
      have hnotA : y ∉ whitneyA (n - 1) ℓ := by
        intro hA'
        exact hyA (Metric.mem_thickening_iff.2
          ⟨emb u, ⟨u, ⟨hu, hu1 hA'.1⟩, rfl⟩, hdist.trans_le (by linarith only [hηA, hδA])⟩)
      have hz : emb u ∉ Metric.thickening (δA / 2) KA := by
        intro hz
        obtain ⟨a', ha', hda⟩ := Metric.mem_thickening_iff.1 hz
        exact hyA (Metric.mem_thickening_iff.2
          ⟨a', ha', by linarith only [dist_triangle y (emb u) a', hdist, hda, hηA]⟩)
      have hnotS : Φ y ∉ D.leftSphere q hq ε c :=
        (hA'sub (Metric.mem_thickening_iff.2
          ⟨emb u, ⟨⟨u, hu, rfl⟩, hz⟩, hdist.trans_le hηA'⟩)).2
      exact iff_of_false hnotS hnotA
  · intro y hy
    rw [hChφ]
    by_cases hyB : y ∈ Metric.thickening δB KB
    · have h := interior_subset (hBsub hyB)
      exact h
    · obtain ⟨u, hu, hdist, -⟩ := happrox η hη y hy
      have hnotB : y ∉ whitneyB (n - 1) ℓ := by
        intro hB'
        obtain ⟨u', hu', hc', hd'⟩ := happroxB η hη hη1 y hy hB'
        exact hyB (Metric.mem_thickening_iff.2
          ⟨emb u', ⟨u', ⟨hu', hc'⟩, rfl⟩, hd'.trans_le (by linarith only [hηB, hδB])⟩)
      have hz : emb u ∉ Metric.thickening (δB / 2) KB := by
        intro hz
        obtain ⟨a', ha', hda⟩ := Metric.mem_thickening_iff.1 hz
        exact hyB (Metric.mem_thickening_iff.2
          ⟨a', ha', by linarith only [dist_triangle y (emb u) a', hdist, hda, hηB]⟩)
      have hnotS : Φ y ∉ D.rightSphere p hp ε c :=
        (hB'sub (Metric.mem_thickening_iff.2
          ⟨emb u, ⟨⟨u, hu, rfl⟩, hz⟩, hdist.trans_le hηB'⟩)).2
      exact iff_of_false hnotS hnotB
  · rw [hChφ, hwp, hΦemb, Wd.corner₁]
  · rw [hChφ, hwp, hΦemb, Wd.corner₂]

end GradientLikeStrip

namespace BlockConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ}

theorem exists_whitney_filling (h6 : 6 ≤ n) (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) {x₁ x₂ : M} {r : ℝ}
    (hr : 0 < r) (hr4 : r < 1 / 4) {N : Set (Fin 2 → ℝ)} {ψ₀ : (Fin 2 → ℝ) → M}
    (hN : whitneyBand r ⊆ N)
    (hcol : B.D.IsWhitneyCollar B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε x₁ x₂ N ψ₀)
    (hπ : SimplyConnectedSpace (f ⁻¹' {B.c}))
    (hπR : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p))
    (hπL : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q)) :
    ∃ F : (Fin 2 → ℝ) → M, ContinuousOn F whitneyHalf ∧ (∀ y ∈ whitneyHalf, f (F y) = B.c) ∧
      (∀ y ∈ whitneyBand (r / 2), F y = ψ₀ y) ∧
      (ℓ = 2 → ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 2) → F y ∉ B.rightSphere p) ∧
      (ℓ + 3 = n → ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 2) → F y ∉ B.leftSphere q) := by
  classical
  have _ := hf
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hRS : B.rightSphere p = B.D.rightSphere p hpc B.ε B.c := by
    simp [BlockConfig.rightSphere, hpc]
  have hLS : B.leftSphere q = B.D.leftSphere q hqc B.ε B.c := by
    simp [BlockConfig.leftSphere, hqc]
  obtain ⟨Y, hY, hYc, hYR, hYL, hYmem⟩ : ∃ Y : Set M, SimplyConnectedSpace ↥Y ∧
      (∀ x ∈ Y, f x = B.c) ∧ (ℓ = 2 → ∀ x ∈ Y, x ∉ B.rightSphere p) ∧
      (ℓ + 3 = n → ∀ x ∈ Y, x ∉ B.leftSphere q) ∧
      (∀ x, f x = B.c → x ∉ B.rightSphere p → x ∉ B.leftSphere q → x ∈ Y) := by
    by_cases h2 : ℓ = 2
    · exact ⟨f ⁻¹' {B.c} \ B.rightSphere p, hπR h2, fun x hx => hx.1, fun _ x hx => hx.2,
        fun h => absurd h (by have := hℓ; have := hℓn; omega), fun x hx hR _ => ⟨hx, hR⟩⟩
    · by_cases h3 : ℓ + 3 = n
      · exact ⟨f ⁻¹' {B.c} \ B.leftSphere q, hπL h3, fun x hx => hx.1,
          fun h => absurd h h2, fun _ x hx => hx.2, fun x hx _ hL => ⟨hx, hL⟩⟩
      · exact ⟨f ⁻¹' {B.c}, hπ, fun x hx => hx, fun h => absurd h h2, fun h => absurd h h3,
          fun x hx _ _ => hx⟩
  set R : ℝ := 1 - r / 2 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hR1 : R < 1 := by rw [hRdef]; linarith
  have hnsq : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ^ 2 = z.ofLp 0 ^ 2 + z.ofLp 1 ^ 2 := by
    intro z
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  set S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | r / 2 ≤ z.ofLp 1} ∩ Metric.closedBall 0 R with hSdef
  have hS_closed : IsClosed S := by
    refine IsClosed.inter ?_ Metric.isClosed_closedBall
    exact isClosed_le continuous_const
      ((continuous_apply 1).comp (PiLp.continuous_ofLp 2 _))
  have hS_mem : ∀ z : EuclideanSpace ℝ (Fin 2), z ∈ S ↔ r / 2 ≤ z.ofLp 1 ∧ ‖z‖ ≤ R := by
    intro z
    simp [hSdef]
  have hint : ∀ z : EuclideanSpace ℝ (Fin 2), z ∈ interior S ↔ r / 2 < z.ofLp 1 ∧ ‖z‖ < R := by
    intro z
    constructor
    · intro hz
      have hz' : S ∈ 𝓝 z := mem_interior_iff_mem_nhds.1 hz
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hz'
      constructor
      · let v : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 (1 : Fin 2) (δ / 2)
        have hv : ‖v‖ = δ / 2 := by
          simp only [v, PiLp.norm_single, Real.norm_eq_abs]
          exact abs_of_pos (by linarith)
        have hmem : z - v ∈ S := by
          apply hball
          rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hv]
          linarith
        have h1 := ((hS_mem _).1 hmem).1
        have : (z - v).ofLp 1 = z.ofLp 1 - δ / 2 := by
          simp [v]
        linarith
      · have hzS : z ∈ S := interior_subset hz
        have hzR := ((hS_mem z).1 hzS).2
        rcases lt_or_eq_of_le hzR with h | h
        · exact h
        · exfalso
          have hmem : (1 + δ / (2 * R)) • z ∈ S := by
            apply hball
            rw [Metric.mem_ball, dist_eq_norm]
            have : (1 + δ / (2 * R)) • z - z = (δ / (2 * R)) • z := by
              rw [add_smul, one_smul]; abel
            rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), h]
            field_simp
            linarith
          have h2 := ((hS_mem _).1 hmem).2
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), h] at h2
          have : 0 < δ / (2 * R) * R := by positivity
          nlinarith
    · rintro ⟨h1, h2⟩
      have hO : IsOpen {z : EuclideanSpace ℝ (Fin 2) | r / 2 < z.ofLp 1 ∧ ‖z‖ < R} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_lt continuous_const
            ((continuous_apply 1).comp (PiLp.continuous_ofLp 2 _))
        · exact isOpen_lt continuous_norm continuous_const
      refine interior_maximal ?_ hO ⟨h1, h2⟩
      rintro w ⟨hw1, hw2⟩
      exact (hS_mem w).2 ⟨hw1.le, hw2.le⟩
  have hS_conv : Convex ℝ S := by
    refine Convex.inter ?_ (convex_closedBall 0 R)
    exact convex_halfSpace_ge
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).isLinear) (r / 2)
  have hS_bdd : Bornology.IsBounded S :=
    Metric.isBounded_closedBall.subset inter_subset_right
  have hS_ne : (interior S).Nonempty := by
    refine ⟨WithLp.toLp 2 ![0, 1 / 2], (hint _).2 ⟨?_, ?_⟩⟩
    · simp; linarith
    · rw [← sq_lt_sq₀ (norm_nonneg _) hR0.le, hnsq]
      simp; nlinarith
  obtain ⟨h, hhi, hhc, hhf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    hS_conv hS_ne hS_bdd
  rw [hS_closed.closure_eq] at hhc
  rw [hS_closed.frontier_eq] at hhf
  have hsqy : ∀ y : Fin 2 → ℝ, ‖WithLp.toLp 2 y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    intro y; rw [hnsq]
  have hSy : ∀ y : Fin 2 → ℝ, WithLp.toLp 2 y ∈ S ↔ r / 2 ≤ y 1 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ R ^ 2 := by
    intro y
    rw [hS_mem, ← hsqy, sq_le_sq₀ (norm_nonneg _) hR0.le]
  have hinty : ∀ y : Fin 2 → ℝ,
      WithLp.toLp 2 y ∈ interior S ↔ r / 2 < y 1 ∧ y 0 ^ 2 + y 1 ^ 2 < R ^ 2 := by
    intro y
    rw [hint, ← hsqy, sq_lt_sq₀ (norm_nonneg _) hR0.le]
  have hband_out : ∀ y ∈ whitneyBand (r / 2), WithLp.toLp 2 y ∉ interior S := by
    intro y hy hin
    rw [hinty] at hin
    rcases hy.2 with h1 | h1
    · linarith [hin.1]
    · rw [hRdef] at hin; linarith [hin.2]
  have hin_of : ∀ y ∈ whitneyHalf, WithLp.toLp 2 y ∉ interior S → y ∈ whitneyBand (r / 2) := by
    intro y hy hin
    refine ⟨hy, ?_⟩
    rw [hinty, not_and_or, not_lt, not_lt] at hin
    rcases hin with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [hRdef] at h1; exact h1)
  have hband_mono : whitneyBand (r / 2) ⊆ whitneyBand r := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    rcases hy.2 with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (le_trans (by nlinarith) h1)
  have hψc : ContinuousOn ψ₀ N := hcol.smooth.continuousOn
  have hfr : ∀ w ∈ S \ interior S, w.ofLp ∈ whitneyBand (r / 2) ∧ r / 2 ≤ w.ofLp 1 ∧
      w.ofLp 0 ^ 2 + w.ofLp 1 ^ 2 ≤ R ^ 2 := by
    intro w hw
    rw [← WithLp.toLp_ofLp 2 w] at hw
    have h1 := (hSy _).1 hw.1
    refine ⟨hin_of _ ⟨by nlinarith, by linarith⟩ hw.2, h1⟩
  have hfrψ : ∀ w ∈ S \ interior S, f (ψ₀ w.ofLp) = B.c ∧ ψ₀ w.ofLp ∉ B.rightSphere p ∧
      ψ₀ w.ofLp ∉ B.leftSphere q := by
    intro w hw
    obtain ⟨hb, h1, h2⟩ := hfr w hw
    have hwN : w.ofLp ∈ N := hN (hband_mono hb)
    refine ⟨hcol.level _ hwN, ?_, ?_⟩
    · rw [hRS, hcol.memB _ hwN]
      intro h
      nlinarith
    · rw [hLS, hcol.memA _ hwN]
      intro h
      linarith
  let e : ℝ → EuclideanSpace ℝ (Fin 2) := fun θ =>
    WithLp.toLp 2 ![Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)]
  have he_cont : Continuous e := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  have he_sph : ∀ θ, e θ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro θ
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, hnsq]
    simp [e]
  have he_surj : ∀ w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∃ θ, e θ = w := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    have hw2 : w.ofLp 0 ^ 2 + w.ofLp 1 ^ 2 = 1 := by rw [← hnsq, hw]; norm_num
    let ζ : ℂ := ⟨w.ofLp 0, w.ofLp 1⟩
    have hζ : ‖ζ‖ = 1 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply]
      simp only [ζ]; nlinarith
    have hζ0 : ζ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hζ; norm_num at hζ
    refine ⟨ζ.arg / (2 * Real.pi), ?_⟩
    have harg : 2 * Real.pi * (ζ.arg / (2 * Real.pi)) = ζ.arg := by
      field_simp
    ext i
    fin_cases i
    · simp [e, harg, Complex.cos_arg hζ0, hζ, ζ]
    · simp [e, harg, Complex.sin_arg, hζ, ζ]
  have he_per : ∀ θ, e (θ + 1) = e θ := by
    intro θ
    have h1 : 2 * Real.pi * (θ + 1) = 2 * Real.pi * θ + 2 * Real.pi := by ring
    simp only [e, h1, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hsymm : ∀ θ, h.symm (e θ) ∈ S \ interior S := by
    intro θ
    have : e θ ∈ h '' (S \ interior S) := by rw [hhf]; exact he_sph θ
    obtain ⟨w, hw, hwe⟩ := this
    rw [← hwe, Homeomorph.symm_apply_apply]
    exact hw
  let γ : ℝ → M := fun θ => ψ₀ (h.symm (e θ)).ofLp
  have hγc : Continuous γ := by
    refine hψc.comp_continuous ((PiLp.continuous_ofLp 2 _).comp
      (h.symm.continuous.comp he_cont)) fun θ => ?_
    exact hN (hband_mono (hfr _ (hsymm θ)).1)
  have hγY : ∀ θ, γ θ ∈ Y := by
    intro θ
    obtain ⟨h1, h2, h3⟩ := hfrψ _ (hsymm θ)
    exact hYmem _ h1 h2 h3
  have hγper : ∀ θ, γ (θ + 1) = γ θ := by
    intro θ
    simp only [γ, he_per]
  obtain ⟨F₀, hF₀c, hF₀Y, hF₀e⟩ := exists_disc_of_simplyConnected hY γ hγc hγY hγper
  have hbdry : ∀ y : Fin 2 → ℝ, WithLp.toLp 2 y ∈ S \ interior S →
      F₀ (h (WithLp.toLp 2 y)) = ψ₀ y := by
    intro y hy
    have hsph : h (WithLp.toLp 2 y) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [← hhf]; exact mem_image_of_mem _ hy
    obtain ⟨θ, hθ⟩ := he_surj _ hsph
    have := hF₀e θ
    change F₀ (e θ) = γ θ at this
    rw [← hθ, this]
    simp only [γ, hθ, Homeomorph.symm_apply_apply, WithLp.ofLp_toLp]
  have hmapsS : ∀ y : Fin 2 → ℝ, WithLp.toLp 2 y ∈ S →
      h (WithLp.toLp 2 y) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro y hy
    rw [← hhc]; exact mem_image_of_mem _ hy
  let F : (Fin 2 → ℝ) → M := fun y =>
    if WithLp.toLp 2 y ∈ interior S then F₀ (h (WithLp.toLp 2 y)) else ψ₀ y
  have hFint : ∀ y : Fin 2 → ℝ, WithLp.toLp 2 y ∈ interior S → F y ∈ Y := by
    intro y hy
    simp only [F, hy, ↓reduceIte]
    exact hF₀Y (hmapsS y (interior_subset hy))
  have hFband : ∀ y ∈ whitneyBand (r / 2), F y = ψ₀ y := by
    intro y hy
    simp only [F, hband_out y hy, ↓reduceIte]
  have hA_closed : IsClosed (whitneyBand (r / 2)) := by
    have : whitneyBand (r / 2) = ({y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩ {y | 0 ≤ y 1}) ∩
        ({y | y 1 ≤ r / 2} ∪ {y | (1 - r / 2) ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2}) := by
      ext y; simp [whitneyBand, whitneyHalf]
    rw [this]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.union ?_ ?_)
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le continuous_const (by fun_prop)
  have hB_closed : IsClosed {y : Fin 2 → ℝ | WithLp.toLp 2 y ∈ S} :=
    hS_closed.preimage (PiLp.continuous_toLp 2 _)
  have hcover : whitneyHalf ⊆ whitneyBand (r / 2) ∪ {y : Fin 2 → ℝ | WithLp.toLp 2 y ∈ S} := by
    intro y hy
    by_cases hin : WithLp.toLp 2 y ∈ interior S
    · exact Or.inr (show WithLp.toLp 2 y ∈ S from interior_subset hin)
    · exact Or.inl (hin_of y hy hin)
  have hFcA : ContinuousOn F (whitneyBand (r / 2)) :=
    (hψc.mono (hband_mono.trans hN)).congr hFband
  have hFcB : ContinuousOn F {y : Fin 2 → ℝ | WithLp.toLp 2 y ∈ S} := by
    have hG : ContinuousOn (fun y : Fin 2 → ℝ => F₀ (h (WithLp.toLp 2 y)))
        {y : Fin 2 → ℝ | WithLp.toLp 2 y ∈ S} :=
      hF₀c.comp (h.continuous.comp (PiLp.continuous_toLp 2 _)).continuousOn
        (fun y hy => hmapsS y hy)
    refine hG.congr fun y hy => ?_
    by_cases hin : WithLp.toLp 2 y ∈ interior S
    · simp only [F, hin, ↓reduceIte]
    · simp only [F, hin, ↓reduceIte]
      exact (hbdry y ⟨hy, hin⟩).symm
  refine ⟨F, ((hFcA.union_of_isClosed hFcB hA_closed hB_closed).mono hcover), ?_, hFband, ?_, ?_⟩
  · intro y hy
    by_cases hin : WithLp.toLp 2 y ∈ interior S
    · exact hYc _ (hFint y hin)
    · rw [hFband y (hin_of y hy hin)]
      exact hcol.level _ (hN (hband_mono (hin_of y hy hin)))
  · intro h2 y hy hyb
    have hin : WithLp.toLp 2 y ∈ interior S := by
      by_contra hin; exact hyb (hin_of y hy hin)
    exact hYR h2 _ (hFint y hin)
  · intro h3 y hy hyb
    have hin : WithLp.toLp 2 y ∈ interior S := by
      by_contra hin; exact hyb (hin_of y hy hin)
    exact hYL h3 _ (hFint y hin)

theorem exists_whitneyDisc (h6 : 6 ≤ n) (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q) {w₁ w₂ : Fin (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).k → ℝ}
    (hw₁ : w₁ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hw₂ : w₂ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1) (hne : w₁ ≠ w₂)
    (hπ : SimplyConnectedSpace (f ⁻¹' {B.c}))
    (hπR : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p))
    (hπL : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q)) :
    Nonempty (B.D.WhitneyDisc B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε
      (B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
        ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₁)))
      (B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
        ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₂)))) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hkp : (B.D.chart p hpc).k = ℓ := by
    rw [← (B.D.chart p hpc).hkidx]; exact (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by
    rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hfp : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hfq : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
  have hv : B.D.sardValid B.ε p hqc hpc := B.sardValid hp hq
  have hc₁ : f p + B.ε < B.c := by rw [hfp]; exact B.hαc
  have hc₂ : B.c < f q - B.ε := by rw [hfq]; exact B.hcβ
  have htr' : B.D.isSardTransverse p hqc B.ε B.c hpc := by
    obtain ⟨_, _, h⟩ := htr
    exact h
  have hεR : ∀ x (hx : x ∈ B.crit), 2 * B.ε ≤ (B.D.chart x hx).R ^ 2 := by
    intro x hx
    have h1 := (B.D.hrm x hx).2
    have h2 := B.D.rm_pos x hx
    have h3 := B.hrm x hx
    have h4 : B.D.rm x hx ^ 2 ≤ (B.D.chart x hx).R ^ 2 := pow_le_pow_left₀ h2.le h1 2
    linarith [B.hε]
  obtain ⟨U₁, φ₁, hφ₁⟩ := GradientLikeStrip.exists_cornerChart hfs B.D hpc hqc hkp hkq h6 hℓ hℓn
    hv hc₁ hc₂ hw₁ htr'
  obtain ⟨U₂, φ₂, hφ₂⟩ := GradientLikeStrip.exists_cornerChart hfs B.D hpc hqc hkp hkq h6 hℓ hℓn
    hv hc₁ hc₂ hw₂ htr'
  obtain ⟨γA, γB, a₁, a₂, b₁, b₂, δ, harcs⟩ := GradientLikeStrip.exists_whitney_arcs hfs B.D
    hpc hqc hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hw₁ hw₂ hne (sardZeros_finite hf B hp hq htr) hφ₁ hφ₂
  obtain ⟨r, hr, hr4, N, ψ₀, hN, hcol⟩ := GradientLikeStrip.exists_whitneyCollar hfs B.D hpc hqc
    hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hφ₁ hφ₂ harcs
  obtain ⟨F, hF, hFc, hFψ, hFR, hFL⟩ :=
    exists_whitney_filling h6 hf B hℓ hℓn hp hq hr hr4 hN hcol hπ hπR hπL
  have hRS : B.rightSphere p = B.D.rightSphere p hpc B.ε B.c := by
    simp only [BlockConfig.rightSphere, hpc, ↓reduceDIte]
  have hLS : B.leftSphere q = B.D.leftSphere q hqc B.ε B.c := by
    simp only [BlockConfig.leftSphere, hqc, ↓reduceDIte]
  rw [hRS] at hFR
  rw [hLS] at hFL
  set SR := B.D.rightSphere p hpc B.ε B.c with hSR
  set SL := B.D.leftSphere q hqc B.ε B.c with hSL
  have hSRc : IsClosed SR := (B.D.isCompact_rightSphere p hpc (hεR p hpc) B.c).isClosed
  have hSLc : IsClosed SL := (B.D.isCompact_leftSphere q hqc (hεR q hqc) B.c).isClosed
  set O : Set M := {x | (ℓ = 2 → x ∉ SR) ∧ (ℓ + 3 = n → x ∉ SL)} with hOdef
  have hO : IsOpen O := by
    have e : O = {x | ℓ = 2 → x ∉ SR} ∩ {x | ℓ + 3 = n → x ∉ SL} := rfl
    rw [e]
    refine IsOpen.inter ?_ ?_
    · by_cases h : ℓ = 2
      · have e' : {x | ℓ = 2 → x ∉ SR} = SRᶜ := by
          ext x; simp [h]
        rw [e']; exact hSRc.isOpen_compl
      · have e' : {x | ℓ = 2 → x ∉ SR} = univ := by
          ext x; simp [h]
        rw [e']; exact isOpen_univ
    · by_cases h : ℓ + 3 = n
      · have e' : {x | ℓ + 3 = n → x ∉ SL} = SLᶜ := by
          ext x; simp [h]
        rw [e']; exact hSLc.isOpen_compl
      · have e' : {x | ℓ + 3 = n → x ∉ SL} = univ := by
          ext x; simp [h]
        rw [e']; exact isOpen_univ
  have hband : whitneyBand (r / 2) ⊆ whitneyBand r := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    rcases hy.2 with h | h
    · left; linarith
    · right
      have : (1 - r) ^ 2 ≤ (1 - r / 2) ^ 2 := by nlinarith
      linarith
  have hFO : ∀ y ∈ whitneyHalf, y ∉ whitneyBand (r / 4) → F y ∈ O := by
    intro y hy hy4
    have hy1 : r / 4 < y 1 := by
      by_contra h
      exact hy4 ⟨hy, Or.inl (not_lt.1 h)⟩
    have hy2 : y 0 ^ 2 + y 1 ^ 2 < (1 - r / 4) ^ 2 := by
      by_contra h
      exact hy4 ⟨hy, Or.inr (not_lt.1 h)⟩
    by_cases hb : y ∈ whitneyBand (r / 2)
    · rw [hFψ y hb]
      have hyN : y ∈ N := hN (hband hb)
      have hA : ψ₀ y ∉ SL := by
        intro hmem
        have := (hcol.memA y hyN).1 hmem
        linarith
      have hB : ψ₀ y ∉ SR := by
        intro hmem
        have := (hcol.memB y hyN).1 hmem
        have : (1 - r / 4) ^ 2 < 1 := by nlinarith
        linarith
      exact ⟨fun _ => hB, fun _ => hA⟩
    · exact ⟨fun h2 => hFR h2 y hy hb, fun h3 => hFL h3 y hy hb⟩
  set κ : ℝ := min (B.c - (B.α + B.ε)) (B.β - B.ε - B.c) with hκdef
  have hκ : 0 < κ := lt_min (by linarith [B.hαc]) (by linarith [B.hcβ])
  have hκ1 : κ ≤ B.c - (B.α + B.ε) := min_le_left _ _
  have hκ2 : κ ≤ B.β - B.ε - B.c := min_le_right _ _
  have hcκ : a ≤ B.c - κ ∧ B.c + κ ≤ b := by
    constructor
    · linarith [B.haα, B.hε]
    · linarith [B.hβb, B.hε]
  have hU : ∀ y, f y ∈ Icc (B.c - κ) (B.c + κ) → ∀ x hx, y ∉ B.D.smallBall x hx := by
    intro y hy x hx
    exact B.hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x hx
  obtain ⟨W₁, N', ψ₁, hW₁, hHW₁, hψ₁, hψ₁c, hN'o, hN', hN'N, hψ₁ψ₀, hψ₁O⟩ :=
    GradientLikeStrip.exists_whitney_smoothing hfs B.D hκ hcκ hU hr hcol.isOpen_N hN
      hcol.smooth hcol.level hF hFc hFψ hO hFO
  obtain ⟨W₂, N'', ψ, hW₂, hHW₂, hψ, hψc, hN''o, hN'', hN''N, hψψ₀, himm, hinj, havoid⟩ :=
    GradientLikeStrip.exists_whitney_embedding hfs B.D hpc hqc hkp hkq h6 hℓ hℓn hv hc₁ hc₂
      hr hr4 hN hcol hW₁ hHW₁ hψ₁ hψ₁c hN'o hN' hN'N hψ₁ψ₀
      (fun h3 y hy hy4 => (hψ₁O y hy hy4).2 h3) (fun h2 y hy hy4 => (hψ₁O y hy hy4).1 h2)
  exact GradientLikeStrip.whitneyDisc_of_embedding hfs B.D hpc hqc hv hr hr4 hN hcol hW₂ hHW₂ hψ
    hψc hN''o hN'' hN''N hψψ₀ himm hinj havoid

theorem exists_whitneyChart (h6 : 6 ≤ n) (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q) {w₁ w₂ : Fin (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).k → ℝ}
    (hw₁ : w₁ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hw₂ : w₂ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hs₁ : B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 w₁ = 1)
    (hs₂ : B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 w₂ = -1)
    (hrm : ∀ x hx, B.D.rm x hx ^ 2 < B.c - B.α ∧ B.D.rm x hx ^ 2 < B.β - B.c)
    (hπ : SimplyConnectedSpace (f ⁻¹' {B.c}))
    (hπR : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p))
    (hπL : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q)) :
    ∃ η κ : ℝ, 0 < η ∧ ∃ Ch : B.D.CollarChart B.c κ, Ch.U = whitneyDom (n - 1) η ∧
      (∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ B.leftSphere q ↔ y ∈ whitneyA (n - 1) ℓ) ∧
      (∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ B.rightSphere p ↔ y ∈ whitneyB (n - 1) ℓ) ∧
      Ch.φ (whitneyPt (n - 1) (-1)) =
        B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
          ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₁)) ∧
      Ch.φ (whitneyPt (n - 1) 1) =
        B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
          ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₂)) := by
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hkp : (B.D.chart p hpc).k = ℓ := by
    rw [← (B.D.chart p hpc).hkidx]; exact (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hkq : (B.D.chart q hqc).k = ℓ + 1 := by
    rw [← (B.D.chart q hqc).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
  have hc₁ : f p + B.ε < B.c := by rw [hpα]; exact B.hαc
  have hc₂ : B.c < f q - B.ε := by rw [hqβ]; exact B.hcβ
  have hv : B.D.sardValid B.ε p hqc hpc := B.sardValid hp hq
  have hrm' : ∀ x hx, B.D.rm x hx ^ 2 < 2 * |f x - B.c| := by
    intro x hx
    obtain ⟨h1, h2⟩ := hrm x hx
    have hsq := sq_nonneg (B.D.rm x hx)
    have hmin := B.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with hlt | hle
    · have hfx := B.hhigh x hx hlt
      rw [abs_of_pos (by linarith)]
      linarith
    · rcases Nat.eq_or_lt_of_le hmin with heq | hlt
      · have hfx := B.hP x hx heq.symm
        rw [hfx, abs_of_neg (by linarith [B.hαc, B.hε])]
        linarith
      · have heq : morseIndex I f x = ℓ + 1 := by omega
        have hfx := B.hQ x hx heq
        rw [hfx, abs_of_pos (by linarith [B.hcβ, B.hε])]
        linarith
  have hne : w₁ ≠ w₂ := by
    intro heq
    have h := hs₁
    rw [heq, hs₂] at h
    norm_num at h
  obtain ⟨Wd⟩ := B.exists_whitneyDisc h6 hf hℓ hℓn hp hq htr hw₁ hw₂ hne hπ hπR hπL
  obtain ⟨Ys, hframe, hA, hB⟩ := GradientLikeStrip.exists_whitneyFrame hf.smooth B.D hpc hqc
    hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hw₁ hw₂ hs₁ hs₂ Wd
  obtain ⟨η, κ, hη, Ch, hU, hAs, hBs, hx₁, hx₂⟩ := GradientLikeStrip.whitneyChart_of_frame
    hf.smooth B.D hpc hqc hkp hkq h6 hℓ hℓn hv hc₁ hc₂ hrm' Wd Ys hframe hA hB
  have hL : B.leftSphere q = B.D.leftSphere q hqc B.ε B.c := by
    simp only [BlockConfig.leftSphere, hqc, ↓reduceDIte]
  have hR : B.rightSphere p = B.D.rightSphere p hpc B.ε B.c := by
    simp only [BlockConfig.rightSphere, hpc, ↓reduceDIte]
  refine ⟨η, κ, hη, Ch, hU, ?_, ?_, hx₁, hx₂⟩
  · rw [hL]; exact hAs
  · rw [hR]; exact hBs

theorem whitney_removes_pair (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {p q : M}
    (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) (htr : B.pairTransverse p q)
    {w₁ w₂ : Fin (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).k → ℝ}
    (hw₁ : w₁ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hw₂ : w₂ ∈ B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1)
    (hs₁ : B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 w₁ = 1)
    (hs₂ : B.D.sardSign p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 w₂ = -1)
    {η κ : ℝ} (hη : 0 < η) (Ch : B.D.CollarChart B.c κ) (hU : Ch.U = whitneyDom (n - 1) η)
    (hA : ∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ B.leftSphere q ↔ y ∈ whitneyA (n - 1) ℓ)
    (hB : ∀ y ∈ whitneyDom (n - 1) η, Ch.φ y ∈ B.rightSphere p ↔ y ∈ whitneyB (n - 1) ℓ)
    (hx₁ : Ch.φ (whitneyPt (n - 1) (-1)) =
      B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
        ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₁)))
    (hx₂ : Ch.φ (whitneyPt (n - 1) 1) =
      B.D.flow (f q - B.ε - B.c) ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).χ
        ((B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).sphereParam B.ε w₂)))
    {K : Set (Fin (n - 1) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ whitneyDom (n - 1) η)
    {H₁ : (Fin (n - 1) → ℝ) → (Fin (n - 1) → ℝ)} (hH₁K : ∀ y, y ∉ K → H₁ y = y)
    (hH₁bij : Function.Bijective H₁)
    (hH₁ : ∀ y ∈ whitneyA (n - 1) ℓ, y ∈ whitneyDom (n - 1) η → H₁ y ∉ whitneyB (n - 1) ℓ)
    {Z : (x : M) → TangentSpace I x} (hZ : Ch.realizes K H₁ Z)
    (E : GradientLikeStrip I f a b B.crit) (hE : ∀ x, E.V x = B.D.V x + Z x)
    (hEchart : ∀ x hx, E.chart x hx = B.D.chart x hx) (hErm : ∀ x hx, E.rm x hx = B.D.rm x hx) :
    E.isSardTransverse p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 ∧
      E.sardCount p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 =
        B.D.sardCount p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1 ∧
      (E.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1).ncard + 2 =
        (B.D.sardZeros p (B.mem_upperIndexCriticalPoints.1 hq).1 B.ε B.c (B.mem_lowerIndexCriticalPoints.1 hp).1).ncard := by
  classical
  have _ := hErm
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hqc : q ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq).1
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hqβ : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
  have hε := B.hε
  have hαc := B.hαc
  have hcβ := B.hcβ
  have haα := B.haα
  have hβb := B.hβb
  have hεR : 2 * B.ε ≤ (B.D.chart q hqc).R ^ 2 := by
    have h1 := (B.D.hrm q hqc).2
    have h2 := B.D.rm_pos q hqc
    have h3 := B.hrm q hqc
    nlinarith
  have hεRp : 2 * B.ε ≤ (B.D.chart p hpc).R ^ 2 := by
    have h1 := (B.D.hrm p hpc).2
    have h2 := B.D.rm_pos p hpc
    have h3 := B.hrm p hpc
    nlinarith
  have hlevel : ∀ (x : M) (t : ℝ), f x ∈ Icc (B.α + B.ε) (B.β - B.ε) →
      f x - t ∈ Icc (B.α + B.ε) (B.β - B.ε) → f (B.D.flow t x) = f x - t := by
    intro x t hx hxt
    refine GradientLikeStrip.f_flow_eq_sub_of_levels (D := B.D) hfs
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hxt.1], by linarith [hxt.2]⟩
      (fun y hy => B.hlev y (Set.uIcc_subset_Icc hx hxt hy)) t right_mem_uIcc
  set T₁ : ℝ := f q - B.ε - B.c with hT₁
  set T₂ : ℝ := B.c - (f p + B.ε) with hT₂
  have hT₁0 : 0 < T₁ := by rw [hT₁, hqβ]; linarith
  have hT₂0 : 0 < T₂ := by rw [hT₂, hpα]; linarith
  set x₁ : (Fin (B.D.chart q hqc).k → ℝ) → M :=
    fun w => (B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε w) with hx₁def
  set z : (Fin (B.D.chart q hqc).k → ℝ) → M := fun w => B.D.flow T₁ (x₁ w) with hzdef
  have hfx₁ : ∀ w, w ≠ 0 → f (x₁ w) = f q - B.ε := fun w hw =>
    (B.D.chart q hqc).f_chart_of_mem_leftModelSphere hεR
      ((B.D.chart q hqc).sphereParam_mem_leftModelSphere hε.le hw)
  have hfz : ∀ w, w ≠ 0 → f (z w) = B.c := by
    intro w hw
    have h := hlevel (x₁ w) T₁ (by rw [hfx₁ w hw, hqβ]; constructor <;> linarith)
      (by rw [hfx₁ w hw, show f q - B.ε - T₁ = B.c by rw [hT₁]; ring]; constructor <;> linarith)
    change f (B.D.flow T₁ (x₁ w)) = B.c
    rw [h, hfx₁ w hw, hT₁]; ring
  have hLdef : ∀ w, B.D.landing p hqc B.ε B.c B.ε w = B.D.flow T₂ (z w) := fun w => rfl
  have hLS : ∀ w, w ≠ 0 → z w ∈ B.leftSphere q := by
    intro w hw
    have hL : B.leftSphere q = B.D.leftSphere q hqc B.ε B.c := by
      simp only [BlockConfig.leftSphere, hqc, ↓reduceDIte]
    rw [hL]
    exact ⟨x₁ w, ⟨_, (B.D.chart q hqc).sphereParam_mem_leftModelSphere hε.le hw, rfl⟩, rfl⟩
  have hRS : ∀ X, B.D.flow T₂ X ∈ (B.D.chart p hpc).χ '' (B.D.chart p hpc).rightModelSphere B.ε →
      X ∈ B.rightSphere p := by
    intro X hX
    have hR : B.rightSphere p = B.D.rightSphere p hpc B.ε B.c := by
      simp only [BlockConfig.rightSphere, hpc, ↓reduceDIte]
    rw [hR]
    refine ⟨_, hX, ?_⟩
    rw [GradientLikeStrip.flow_flow, show T₂ + (f p + B.ε - B.c) = 0 by rw [hT₂]; ring,
      GradientLikeStrip.flow_zero]
  have hright : ∀ X, X ∈ (B.D.chart p hpc).χ '' {y | morseNorm n y < (B.D.chart p hpc).R} →
      f X = f p + B.ε → ModelField.scaledNegativePart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm X) = 0 →
      X ∈ (B.D.chart p hpc).χ '' (B.D.chart p hpc).rightModelSphere B.ε := by
    rintro _ ⟨y, hyR, rfl⟩ hfl hJ
    have hyR' : morseNorm n y < (B.D.chart p hpc).R := hyR
    rw [(B.D.chart p hpc).χ.left_inv ((B.D.chart p hpc).hsrc y hyR'.le)] at hJ
    rw [(B.D.chart p hpc).hnorm y hyR'.le] at hfl
    have hv : posPart (B.D.chart p hpc).hk y ≠ 0 :=
      ModelField.posPart_ne_zero_of_lt_nf _ (c := f p) (by rw [hfl]; linarith)
    have hu : negPart (B.D.chart p hpc).hk y = 0 := (ModelField.scaledNegativePart_eq_zero_iff _ hv).1 hJ
    have hn := ModelField.nf_sub_eq (B.D.chart p hpc).hk (f p) y
    rw [hfl, hu, norm_zero] at hn
    refine ⟨y, ⟨hu, ?_⟩, rfl⟩
    linarith
  have hfland : ∀ ζ, f ζ = B.c → f (B.D.flow T₂ ζ) = f p + B.ε := by
    intro ζ hζ
    rw [hlevel ζ T₂ (by rw [hζ]; constructor <;> linarith)
      (by rw [hζ, show B.c - T₂ = f p + B.ε by rw [hT₂]; ring, hpα]; constructor <;> linarith), hζ]
    rw [hT₂]; ring
  have hDzeroR : ∀ v, v ∈ B.D.sardDom p hqc B.ε B.c B.ε hpc →
      B.D.sardMap p hqc B.ε B.c B.ε hpc v = 0 →
      B.D.flow T₂ (z v) ∈ (B.D.chart p hpc).χ '' (B.D.chart p hpc).rightModelSphere B.ε := by
    rintro v ⟨hv0, hvL⟩ hS
    exact hright _ hvL (hfland _ (hfz v hv0)) hS
  obtain ⟨hw₁D, hw₁n, hw₁S⟩ := hw₁
  obtain ⟨hw₂D, hw₂n, hw₂S⟩ := hw₂
  have hw₁0 : w₁ ≠ 0 := hw₁D.1
  have hw₂0 : w₂ ≠ 0 := hw₂D.1
  have hx₁' : Ch.φ (whitneyPt (n - 1) (-1)) = z w₁ := hx₁
  have hx₂' : Ch.φ (whitneyPt (n - 1) 1) = z w₂ := hx₂
  have hcw : ∀ (σ : ℝ) (j : ℕ), 1 ≤ j → coordN (whitneyPt (n - 1) σ) j = 0 := by
    intro σ j hj
    unfold coordN whitneyPt
    split_ifs with h1 h2
    · simp at h2; omega
    · rfl
    · rfl
  have hcw0 : ∀ σ : ℝ, coordN (whitneyPt (n - 1) σ) 0 ^ 2 ≤ σ ^ 2 := by
    intro σ
    unfold coordN whitneyPt
    split_ifs with h1 h2
    · exact le_rfl
    · simp at h2
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  have hPdom : ∀ σ : ℝ, σ ^ 2 = 1 → whitneyPt (n - 1) σ ∈ whitneyDom (n - 1) η := by
    intro σ hσ
    refine ⟨?_, ?_, ?_⟩
    · rw [hcw σ 1 le_rfl]
      have := hcw0 σ
      nlinarith
    · rw [hcw σ 1 le_rfl]; linarith
    · intro j hj
      rw [hcw σ j (by omega), abs_zero]; exact hη
  have hP₁dom := hPdom (-1) (by norm_num)
  have hP₂dom := hPdom 1 (by norm_num)
  have hKU' : K ⊆ Ch.U := by rw [hU]; exact hKU
  have hP₁A : whitneyPt (n - 1) (-1) ∈ whitneyA (n - 1) ℓ :=
    (hA _ hP₁dom).1 (by rw [hx₁']; exact hLS w₁ hw₁0)
  have hP₂A : whitneyPt (n - 1) 1 ∈ whitneyA (n - 1) ℓ :=
    (hA _ hP₂dom).1 (by rw [hx₂']; exact hLS w₂ hw₂0)
  have hP₁B : whitneyPt (n - 1) (-1) ∈ whitneyB (n - 1) ℓ :=
    (hB _ hP₁dom).1 (by rw [hx₁']; exact hRS _ (hDzeroR w₁ hw₁D hw₁S))
  have hP₂B : whitneyPt (n - 1) 1 ∈ whitneyB (n - 1) ℓ :=
    (hB _ hP₂dom).1 (by rw [hx₂']; exact hRS _ (hDzeroR w₂ hw₂D hw₂S))
  have hP₁K : whitneyPt (n - 1) (-1) ∈ K := by
    by_contra h
    exact hH₁ _ hP₁A hP₁dom (by rw [hH₁K _ h]; exact hP₁B)
  have hP₂K : whitneyPt (n - 1) 1 ∈ K := by
    by_contra h
    exact hH₁ _ hP₂A hP₂dom (by rw [hH₁K _ h]; exact hP₂B)
  have hH₁KK : ∀ y ∈ K, H₁ y ∈ K := by
    intro y hy
    by_contra h
    have h' := hH₁K _ h
    rw [hH₁bij.1 h'] at h
    exact h hy
  have hmodel : ∀ x (hx : x ∈ B.crit) (y : Fin n → ℝ), morseNorm n y ^ 2 = 2 * B.ε →
      (B.D.chart x hx).χ y ∈ (B.D.chart x hx).χ '' {u | morseNorm n u < B.D.rm x hx} := by
    intro x hx y hy
    refine ⟨y, ?_, rfl⟩
    have h1 := B.hrm x hx
    have h2 := B.D.rm_pos x hx
    change morseNorm n y < B.D.rm x hx
    exact lt_of_pow_lt_pow_left₀ 2 h2.le (by rw [hy]; linarith)
  have hκ₁ : κ < T₁ := by
    by_contra h
    push Not at h
    refine Ch.avoid _ (by rw [hU]; exact hP₁dom) (-T₁) ⟨by linarith, by linarith⟩ q hqc ?_
    rw [hx₁', GradientLikeStrip.flow_neg_flow]
    exact hmodel q hqc _ ((B.D.chart q hqc).morseNorm_sq_of_mem_leftModelSphere
      ((B.D.chart q hqc).sphereParam_mem_leftModelSphere hε.le hw₁0))
  have hκ₂ : κ < T₂ := by
    by_contra h
    push Not at h
    refine Ch.avoid _ (by rw [hU]; exact hP₂dom) T₂ ⟨by linarith, h⟩ p hpc ?_
    rw [hx₂']
    obtain ⟨y, hy, hyeq⟩ := hDzeroR w₂ hw₂D hw₂S
    rw [← hyeq]
    exact hmodel p hpc y ((B.D.chart p hpc).morseNorm_sq_of_mem_rightModelSphere hy)
  have hκ := Ch.hκ
  have hsuppZ : ∀ x ∈ tsupport Z, f x ∈ Ioo (B.c - κ) (B.c + κ) := by
    intro x hx
    obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩ := hZ.2.2.2.1 hx
    have hyc : f (Ch.φ y) = B.c := Ch.level y (hKU' hy)
    have hft := hlevel (Ch.φ y) t (by rw [hyc]; constructor <;> linarith)
      (by rw [hyc]; constructor <;> linarith [ht.1, ht.2, hpα, hqβ])
    change f (B.D.flow t (Ch.φ y)) ∈ Ioo (B.c - κ) (B.c + κ)
    rw [hft, hyc]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨hfl1, hfl2⟩ := Ch.flow_of_realizes hfs hZ hKU' E hE
  have hbelow : ∀ u, f u ≤ B.c - κ → ∀ t, 0 ≤ t → E.flow t u = B.D.flow t u := by
    intro u hu t ht
    refine hfl1 u t fun s hs hsZ => ?_
    rw [min_eq_left ht, max_eq_right ht] at hs
    have h1 := GradientLikeStrip.f_flow_le (D := B.D) hfs u hs.1
    have h2 := hsuppZ _ hsZ
    linarith [h2.1]
  have habove : ∀ w, w ≠ 0 → E.flow (T₁ - κ) (x₁ w) = B.D.flow (-κ) (z w) := by
    intro w hw
    rw [hfl1 (x₁ w) (T₁ - κ) fun s hs hsZ => ?_]
    · change B.D.flow (T₁ - κ) (x₁ w) = B.D.flow (-κ) (B.D.flow T₁ (x₁ w))
      rw [GradientLikeStrip.flow_flow]; ring_nf
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hs
      have h1 := hlevel (x₁ w) s (by rw [hfx₁ w hw, hqβ]; constructor <;> linarith)
        (by rw [hfx₁ w hw]; constructor <;> linarith [hs.1, hs.2, hpα, hqβ])
      have h2 := hsuppZ _ hsZ
      rw [h1, hfx₁ w hw] at h2
      linarith [h2.2, hs.2]
  have hEsplit : ∀ w, E.flow T₂ (E.flow T₁ (x₁ w)) =
      E.flow (T₂ - κ) (E.flow (2 * κ) (E.flow (T₁ - κ) (x₁ w))) := by
    intro w
    simp only [GradientLikeStrip.flow_flow]
    ring_nf
  have hEout : ∀ w, w ≠ 0 → z w ∉ Ch.φ '' K →
      E.flow T₂ (E.flow T₁ (x₁ w)) = B.D.flow T₂ (z w) := by
    intro w hw hzK
    rw [hEsplit, habove w hw]
    have hlev' : f (B.D.flow (-κ) (z w)) = B.c + κ := by
      rw [hlevel (z w) (-κ) (by rw [hfz w hw]; constructor <;> linarith)
        (by rw [hfz w hw]; constructor <;> linarith [hpα, hqβ]), hfz w hw]; ring
    rw [hfl2 _ hlev' (by
      rintro ⟨_, ⟨y, hy, rfl⟩, hyz⟩
      exact hzK ⟨y, hy, B.D.flow_injective _ hyz⟩)]
    rw [GradientLikeStrip.flow_flow, show -κ + 2 * κ = κ by ring]
    have hlevκ : f (B.D.flow κ (z w)) = B.c - κ := by
      rw [hlevel (z w) κ (by rw [hfz w hw]; constructor <;> linarith)
        (by rw [hfz w hw]; constructor <;> linarith [hpα, hqβ]), hfz w hw]
    rw [hbelow _ hlevκ.le _ (by linarith), GradientLikeStrip.flow_flow]
    ring_nf
  have hEin : ∀ w, w ≠ 0 → ∀ y ∈ K, z w = Ch.φ y →
      E.flow T₂ (E.flow T₁ (x₁ w)) = B.D.flow T₂ (Ch.φ (H₁ y)) := by
    intro w hw y hy hzy
    rw [hEsplit, habove w hw, hzy, hZ.2.2.2.2 E hE y (hKU' hy)]
    have hyc : f (Ch.φ (H₁ y)) = B.c := Ch.level _ (hKU' (hH₁KK y hy))
    have hlevκ : f (B.D.flow κ (Ch.φ (H₁ y))) = B.c - κ := by
      rw [hlevel _ κ (by rw [hyc]; constructor <;> linarith)
        (by rw [hyc]; constructor <;> linarith [hpα, hqβ]), hyc]
    rw [hbelow _ hlevκ.le _ (by linarith), GradientLikeStrip.flow_flow]
    ring_nf
  have hAB : ∀ y, y ∈ whitneyA (n - 1) ℓ → y ∈ whitneyB (n - 1) ℓ →
      y = whitneyPt (n - 1) 1 ∨ y = whitneyPt (n - 1) (-1) := by
    rintro y ⟨hA1, hAj⟩ ⟨hB0, hBj⟩
    have hz : ∀ j, 1 ≤ j → coordN y j = 0 := by
      intro j hj
      rcases Nat.lt_or_ge j 2 with h2 | h2
      · rw [show j = 1 by omega]; exact hA1
      · rcases Nat.lt_or_ge ℓ j with h3 | h3
        · exact hAj j (by omega)
        · exact hBj j h2 h3
    have hci : ∀ i : Fin (n - 1), coordN y i = y i := fun i => by simp [coordN, i.isLt]
    have h0 : coordN y 0 = 1 ∨ coordN y 0 = -1 := by
      rw [hA1] at hB0
      have : (coordN y 0 - 1) * (coordN y 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    have hgen : ∀ σ : ℝ, coordN y 0 = σ → y = whitneyPt (n - 1) σ := by
      intro σ hσ
      funext i
      simp only [whitneyPt]
      split_ifs with hi
      · rw [← hci i, hi, hσ]
      · rw [← hci i, hz i (by omega)]
    rcases h0 with h | h
    · exact Or.inl (hgen 1 h)
    · exact Or.inr (hgen (-1) h)
  have hzinj : ∀ v v', v ≠ 0 → v' ≠ 0 → ‖v‖ = 1 → ‖v'‖ = 1 → z v = z v' → v = v' := by
    intro v v' hv hv' hn hn' h
    have h1 : x₁ v = x₁ v' := B.D.flow_injective T₁ h
    have h2 : (B.D.chart q hqc).sphereParam B.ε v = (B.D.chart q hqc).sphereParam B.ε v' :=
      (B.D.chart q hqc).χ.injOn
        ((B.D.chart q hqc).hsrc _ ((B.D.chart q hqc).morseNorm_sphereParam_le hε.le hεR hv))
        ((B.D.chart q hqc).hsrc _ ((B.D.chart q hqc).morseNorm_sphereParam_le hε.le hεR hv')) h1
    have h3 := congrArg (negPart (B.D.chart q hqc).hk) h2
    rw [(B.D.chart q hqc).negPart_sphereParam, (B.D.chart q hqc).negPart_sphereParam] at h3
    have hs : 0 < Real.sqrt (2 * B.ε) := Real.sqrt_pos.2 (by linarith)
    have hE0 : 0 < ‖(B.D.chart q hqc).toE v‖ :=
      norm_pos_iff.2 ((B.D.chart q hqc).toE_ne_zero hv)
    have hE0' : 0 < ‖(B.D.chart q hqc).toE v'‖ :=
      norm_pos_iff.2 ((B.D.chart q hqc).toE_ne_zero hv')
    set A := Real.sqrt (2 * B.ε) / ‖(B.D.chart q hqc).toE v‖ with hAdef
    set A' := Real.sqrt (2 * B.ε) / ‖(B.D.chart q hqc).toE v'‖ with hA'def
    have hA0 : 0 < A := div_pos hs hE0
    have hA0' : 0 < A' := div_pos hs hE0'
    have h4 : (B.D.chart q hqc).toE v' = (B.D.chart q hqc).toE ((A / A') • v) := by
      rw [(B.D.chart q hqc).toE_smul, div_eq_inv_mul, ← smul_smul, h3, smul_smul,
        inv_mul_cancel₀ hA0'.ne', one_smul]
    have h5 : v' = (A / A') • v :=
      (EuclideanSpace.equiv (Fin (B.D.chart q hqc).k) ℝ).symm.injective h4
    have h6 : A / A' = 1 := by
      have := congrArg norm h5
      rw [norm_smul, hn, hn', mul_one, Real.norm_eq_abs, abs_of_pos (div_pos hA0 hA0')] at this
      exact this.symm
    rw [h5, h6, one_smul]
  have hKc : IsClosed (Ch.φ '' K) := (hK.image_of_continuousOn (Ch.smooth.continuousOn.mono hKU')).isClosed
  set G : Set (Fin (B.D.chart q hqc).k → ℝ) := {v | v ≠ 0} ∩ z ⁻¹' (Ch.φ '' K)ᶜ with hGdef
  have hzc : ContinuousOn z {v | v ≠ 0} := by
    have h := (B.D.continuous_flow (-T₂)).comp_continuousOn
      (GradientLikeStrip.continuousOn_landing (D := B.D) (p := p) (c := B.c) (η := B.ε) hε.le hεR)
    refine h.congr fun v _ => ?_
    change B.D.flow T₁ (x₁ v) = B.D.flow (-T₂) (B.D.flow T₂ (z v))
    rw [GradientLikeStrip.flow_neg_flow]
  have hGo : IsOpen G := hzc.isOpen_inter_preimage isOpen_ne hKc.isOpen_compl
  set S := B.D.sardMap p hqc B.ε B.c B.ε hpc with hSdef
  set Dom := B.D.sardDom p hqc B.ε B.c B.ε hpc with hDomdef
  have hDomo : IsOpen Dom := GradientLikeStrip.isOpen_sardDom hε.le hεR
  set U₀ := Dom ∩ G with hU₀def
  have hU₀o : IsOpen U₀ := hDomo.inter hGo
  have hk : (E.chart q hqc).k = (B.D.chart q hqc).k := by rw [hEchart]
  have hl : (E.chart p hpc).k = (B.D.chart p hpc).k := by rw [hEchart]
  have hgenq : ∀ (d d' : MorseNormalChart I f q) (_ : d' = d) (hk : d'.k = d.k)
      (w : Fin d.k → ℝ), d'.χ (d'.sphereParam B.ε (w ∘ Fin.cast hk)) = d.χ (d.sphereParam B.ε w) ∧
        (w ∘ Fin.cast hk = 0 ↔ w = 0) := by
    intro d d' h hk w
    subst h
    exact ⟨rfl, Iff.rfl⟩
  have hgenp : ∀ (d d' : MorseNormalChart I f p) (_ : d' = d) (hl : d'.k = d.k) (X : M)
      (j : Fin d'.k), ModelField.scaledNegativePart d'.hk (d'.χ.symm X) j =
        ModelField.scaledNegativePart d.hk (d.χ.symm X) (Fin.cast hl j) := by
    intro d d' h hl X j
    subst h
    rfl
  have hball : (E.chart p hpc).χ '' {y | morseNorm n y < (E.chart p hpc).R} =
      (B.D.chart p hpc).χ '' {y | morseNorm n y < (B.D.chart p hpc).R} := by rw [hEchart]
  have hEland : ∀ w, E.landing p hqc B.ε B.c B.ε (w ∘ Fin.cast hk) =
      E.flow T₂ (E.flow T₁ (x₁ w)) := by
    intro w
    unfold GradientLikeStrip.landing
    rw [(hgenq _ _ (hEchart q hqc) hk w).1]
  have hE0 : ∀ w, (w ∘ Fin.cast hk = 0 ↔ w = 0) := fun w => (hgenq _ _ (hEchart q hqc) hk w).2
  have hEmap : ∀ w (j : Fin (E.chart p hpc).k),
      (E.sardMap p hqc B.ε B.c B.ε hpc (w ∘ Fin.cast hk)) j =
        ModelField.scaledNegativePart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm (E.flow T₂ (E.flow T₁ (x₁ w))))
          (Fin.cast hl j) := by
    intro w j
    unfold GradientLikeStrip.sardMap
    rw [hEland w]
    exact hgenp _ _ (hEchart p hpc) hl _ j
  have hEdom : ∀ w, w ∘ Fin.cast hk ∈ E.sardDom p hqc B.ε B.c B.ε hpc ↔
      w ≠ 0 ∧ E.flow T₂ (E.flow T₁ (x₁ w)) ∈
        (B.D.chart p hpc).χ '' {y | morseNorm n y < (B.D.chart p hpc).R} := by
    intro w
    change (w ∘ Fin.cast hk ≠ 0 ∧ E.landing p hqc B.ε B.c B.ε (w ∘ Fin.cast hk) ∈
        (E.chart p hpc).χ '' {y | morseNorm n y < (E.chart p hpc).R}) ↔ _
    rw [hEland w, hball, Ne, hE0 w]
  have hJzero : ∀ (X : M), (∀ j : Fin (E.chart p hpc).k,
      ModelField.scaledNegativePart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm X) (Fin.cast hl j) = 0) ↔
      ModelField.scaledNegativePart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm X) = 0 := by
    intro X
    constructor
    · intro h
      ext i
      have := h (Fin.cast hl.symm i)
      simpa using this
    · intro h j
      rw [h]; rfl
  have hagreeG : ∀ v ∈ G, (v ∈ Dom ↔ v ∘ Fin.cast hk ∈ E.sardDom p hqc B.ε B.c B.ε hpc) ∧
      ∀ j, (E.sardMap p hqc B.ε B.c B.ε hpc (v ∘ Fin.cast hk)) j = (S v) (Fin.cast hl j) := by
    rintro v ⟨hv0, hvK⟩
    have hL := hEout v hv0 hvK
    refine ⟨?_, fun j => ?_⟩
    · rw [hEdom v, hL]
      exact ⟨fun h => ⟨hv0, h.2⟩, fun h => ⟨hv0, h.2⟩⟩
    · rw [hEmap v j, hL]
      rfl
  have hSz : ∀ v ∈ G, (E.sardMap p hqc B.ε B.c B.ε hpc (v ∘ Fin.cast hk) = 0 ↔ S v = 0) := by
    intro v hv
    have h := (hagreeG v hv).2
    constructor
    · intro h0
      ext i
      have := h (Fin.cast hl.symm i)
      rw [h0] at this
      simpa using this.symm
    · intro h0
      ext j
      rw [h j, h0]
      rfl
  have hEG : ∀ v, v ∘ Fin.cast hk ∈ E.sardDom p hqc B.ε B.c B.ε hpc →
      E.sardMap p hqc B.ε B.c B.ε hpc (v ∘ Fin.cast hk) = 0 → v ∈ G := by
    intro v hvD hvS
    obtain ⟨hv0, hvL⟩ := (hEdom v).1 hvD
    refine ⟨hv0, fun hvK => ?_⟩
    obtain ⟨y, hy, hyz⟩ := hvK
    have hL := hEin v hv0 y hy hyz.symm
    have hJ : ModelField.scaledNegativePart (B.D.chart p hpc).hk ((B.D.chart p hpc).χ.symm
        (B.D.flow T₂ (Ch.φ (H₁ y)))) = 0 := by
      rw [← hJzero, ← hL]
      intro j
      rw [← hEmap v j, hvS]
      rfl
    have hH₁y := hH₁KK y hy
    have hmem := hright _ (hL ▸ hvL) (hfland _ (Ch.level _ (hKU' hH₁y))) hJ
    have hyA : y ∈ whitneyA (n - 1) ℓ := (hA y (hKU hy)).1 (by rw [hyz]; exact hLS v hv0)
    exact hH₁ y hyA (hKU hy) ((hB _ (hKU hH₁y)).1 (hRS _ hmem))
  have hcd := SardData.congr_data hk hl hU₀o (S := S) (U := U₀)
    (S' := E.sardMap p hqc B.ε B.c B.ε hpc) (U' := E.sardDom p hqc B.ε B.c B.ε hpc)
    (fun w => ⟨fun h => ⟨(hagreeG w h.1.2).1.1 h.1.1, (hSz w h.1.2).2 h.2⟩,
      fun h => by
        have hG := hEG w h.1 h.2
        exact ⟨⟨(hagreeG w hG).1.2 h.1, hG⟩, (hSz w hG).1 h.2⟩⟩)
    (fun w hw _ => Filter.mem_of_superset (hU₀o.mem_nhds hw)
      (fun v hv => ⟨(hagreeG v hv.2).1.1 hv.1, (hagreeG v hv.2).2⟩))
  have hw₁Z : w₁ ∈ SardData.zeros S Dom := ⟨hw₁D, hw₁n, hw₁S⟩
  have hw₂Z : w₂ ∈ SardData.zeros S Dom := ⟨hw₂D, hw₂n, hw₂S⟩
  have hw₁K : z w₁ ∈ Ch.φ '' K := ⟨_, hP₁K, hx₁'⟩
  have hw₂K : z w₂ ∈ Ch.φ '' K := ⟨_, hP₂K, hx₂'⟩
  have hne : w₁ ≠ w₂ := by
    intro heq
    have h := hs₁
    rw [heq, hs₂] at h
    norm_num at h
  have hZset : SardData.zeros S U₀ = SardData.zeros S Dom \ {w₁, w₂} := by
    ext v
    constructor
    · rintro ⟨⟨hvD, hvG⟩, hvn, hvS⟩
      refine ⟨⟨hvD, hvn, hvS⟩, ?_⟩
      rintro (rfl | rfl)
      · exact hvG.2 hw₁K
      · exact hvG.2 hw₂K
    · rintro ⟨⟨hvD, hvn, hvS⟩, hvw⟩
      have hv0 : v ≠ 0 := hvD.1
      refine ⟨⟨hvD, hv0, fun hvK => ?_⟩, hvn, hvS⟩
      obtain ⟨y, hy, hyz⟩ := hvK
      have hyA : y ∈ whitneyA (n - 1) ℓ := (hA y (hKU hy)).1 (by rw [hyz]; exact hLS v hv0)
      have hyB : y ∈ whitneyB (n - 1) ℓ :=
        (hB y (hKU hy)).1 (by rw [hyz]; exact hRS _ (hDzeroR v hvD hvS))
      apply hvw
      rcases hAB y hyA hyB with rfl | rfl
      · right
        exact hzinj v w₂ hv0 hw₂0 hvn hw₂n (hyz.symm.trans hx₂')
      · left
        exact hzinj v w₁ hv0 hw₁0 hvn hw₁n (hyz.symm.trans hx₁')
  have hfin : (SardData.zeros S Dom).Finite := B.sardZeros_finite hf hp hq htr
  have hdecomp : SardData.zeros S Dom =
      insert w₁ (insert w₂ (SardData.zeros S Dom \ {w₁, w₂})) := by
    ext v
    simp only [mem_insert_iff, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · intro hv
      by_cases h1 : v = w₁
      · exact Or.inl h1
      · by_cases h2 : v = w₂
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hv, by rintro (h | h) <;> contradiction⟩)
    · rintro (rfl | rfl | ⟨hv, -⟩)
      · exact hw₁Z
      · exact hw₂Z
      · exact hv
  have hfin' : (SardData.zeros S Dom \ {w₁, w₂}).Finite := hfin.subset sdiff_subset
  have hn₂ : w₂ ∉ SardData.zeros S Dom \ {w₁, w₂} := fun h => h.2 (Or.inr rfl)
  have hn₁ : w₁ ∉ insert w₂ (SardData.zeros S Dom \ {w₁, w₂}) := by
    rintro (h | h)
    · exact hne h
    · exact h.2 (Or.inl rfl)
  obtain ⟨_, _, htr'⟩ := htr
  have htrS : SardData.transverse S Dom := htr'
  change SardData.transverse (E.sardMap p hqc B.ε B.c B.ε hpc) (E.sardDom p hqc B.ε B.c B.ε hpc) ∧
    SardData.count (E.sardMap p hqc B.ε B.c B.ε hpc) (E.sardDom p hqc B.ε B.c B.ε hpc) =
      SardData.count S Dom ∧
    (SardData.zeros (E.sardMap p hqc B.ε B.c B.ε hpc) (E.sardDom p hqc B.ε B.c B.ε hpc)).ncard + 2 =
      (SardData.zeros S Dom).ncard
  refine ⟨hcd.1.2 fun w hw hSw => htrS w hw.1 hSw, ?_, ?_⟩
  · rw [hcd.2.1]
    unfold SardData.count
    rw [hZset]
    conv_rhs => rw [hdecomp, finsum_mem_insert _ hn₁ (hfin'.insert w₂), finsum_mem_insert _ hn₂ hfin']
    have h1 : SardData.sign S w₁ = 1 := hs₁
    have h2 : SardData.sign S w₂ = -1 := hs₂
    rw [h1, h2]
    ring
  · rw [hcd.2.2, hZset]
    conv_rhs => rw [hdecomp, Set.ncard_insert_of_notMem hn₁ (hfin'.insert w₂),
      Set.ncard_insert_of_notMem hn₂ hfin']

end BlockConfig

end

end DifferentialGeometry.Topology
