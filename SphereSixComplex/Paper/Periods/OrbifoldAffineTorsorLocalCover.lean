module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorCuspSections

@[expose] public section
noncomputable section
open SphereSixComplex.TriangleGroup
open scoped Manifold
namespace SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem

public theorem exists_local_equivariant_cover
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    ∃ (U : Option ℂ → Set ℂ) (s : Option ℂ → UpperHalfPlane → ℂ),
      (∀ i, IsOpen (U i)) ∧ (∀ q, q ∈ U (some q)) ∧
      (∀ i z, P.quotient.coordinate z ∈ U i → MDiffAt (s i) z) ∧
      (∀ i h z, P.quotient.coordinate z ∈ U i →
        s i (fuchsianSourceAction h • z) = (P.affineTransport h (z, s i z)).2) ∧
      (∀ i, 0 ∈ U i → i = some 0) ∧ (∀ i, 1 ∈ U i → i = some 1) ∧
      (∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ U none) ∧
      ∀ z, 1 < z.im → s none z = P.cuspSection z := by
  classical
  have hlocal (q : ℂ) : ∃ (W : Set ℂ) (t : UpperHalfPlane → ℂ),
      IsOpen W ∧ q ∈ W ∧
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt t z) ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        t (fuchsianSourceAction h • z) = (P.affineTransport h (z, t z)).2) := by
    by_cases hq0 : q = 0
    · subst q
      obtain ⟨W, hW, h0, t, ht, _, heq⟩ := P.exists_ellipticOne_local_equivariant_section
      exact ⟨W, t, hW, h0, ht, heq⟩
    by_cases hq1 : q = 1
    · subst q
      obtain ⟨W, hW, h1, t, ht, _, heq⟩ := P.exists_ellipticTwo_local_equivariant_section
      exact ⟨W, t, hW, h1, ht, heq⟩
    obtain ⟨z, hz⟩ := P.quotient.coordinate_isQuotientMap.surjective q
    have hreg : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ) := by
      simpa only [hz, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using ⟨hq0, hq1⟩
    obtain ⟨W, hW, hq, _, t, ht, _, heq⟩ := P.exists_regular_local_equivariant_section hreg
    exact ⟨W, t, hW, hz ▸ hq, ht, heq⟩
  choose W t hW hq ht heq using hlocal
  obtain ⟨V, hV, ⟨R, hR, hRV⟩, c, hc, hc0, hceq⟩ := P.exists_cusp_local_equivariant_section
  let U : Option ℂ → Set ℂ
    | none => V ∩ ({0, 1} : Set ℂ)ᶜ
    | some q => W q ∩ (if q = 0 then Set.univ else {0}ᶜ) ∩
        (if q = 1 then Set.univ else {1}ᶜ)
  let s : Option ℂ → UpperHalfPlane → ℂ
    | none => c
    | some q => t q
  have hsub (q : ℂ) : U (some q) ⊆ W q := fun _ hz ↦ hz.1.1
  refine ⟨U, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc0⟩
  · intro i
    cases i with
    | none => exact hV.inter (isClosed_singleton.union isClosed_singleton).isOpen_compl
    | some q =>
      apply IsOpen.inter
      · apply (hW q).inter
        split_ifs <;> first | exact isOpen_univ | exact isOpen_compl_singleton
      · split_ifs <;> first | exact isOpen_univ | exact isOpen_compl_singleton
  · intro q
    refine ⟨⟨hq q, ?_⟩, ?_⟩ <;> simp
  · intro i z hz
    cases i with
    | none => exact hc z hz.1
    | some q => exact ht q z (hsub q hz)
  · intro i g z hz
    cases i with
    | none => exact hceq g z hz.1
    | some q => exact heq q g z (hsub q hz)
  · intro i hi
    cases i with
    | none => exact False.elim (hi.2 (by simp))
    | some q =>
      have hq0 : q = 0 := by
        by_contra hne
        simpa only [U, ite_eq_right hne, Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] using hi.1.2
      exact congrArg some hq0
  · intro i hi
    cases i with
    | none => exact False.elim (hi.2 (by simp))
    | some q =>
      have hq1 : q = 1 := by
        by_contra hne
        simpa only [U, ite_eq_right hne, Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] using hi.2
      exact congrArg some hq1
  · refine ⟨max R 2, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
    intro q hqout
    have hnorm : max R 2 ≤ ‖q‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hqout
    have hqV : q ∈ V := hRV (by
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using
        (le_max_left R 2).trans hnorm)
    refine ⟨hqV, ?_⟩
    have htwo : 2 ≤ ‖q‖ := (le_max_right R 2).trans hnorm
    intro hmem
    rcases hmem with h0 | h1
    · simp only [h0, norm_zero] at htwo
      norm_num at htwo
    · have heq : q = 1 := h1
      simp only [heq, norm_one] at htwo
      norm_num at htwo

public theorem distinct_overlap_regular {U : Option ℂ → Set ℂ}
    (hzero : ∀ i, 0 ∈ U i → i = some 0) (hone : ∀ i, 1 ∈ U i → i = some 1)
    {i j : Option ℂ} (hij : i ≠ j) : U i ∩ U j ⊆ ({0, 1} : Set ℂ)ᶜ := by
  rintro q ⟨hi, hj⟩ (hq | hq)
  · subst q
    exact hij ((hzero i hi).trans (hzero j hj).symm)
  · have hq' : q = 1 := hq
    subst q
    exact hij ((hone i hi).trans (hone j hj).symm)

end SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem
