module

public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# The integer core of elliptic adjacency

The product equation and the strict trace bound leave only the three smallest positive
factorizations.  This arithmetic lemma is independent of the modular and Fuchsian geometry.
-/

namespace SphereSixComplex.Periods.IntegerEllipticAdjacency

/-- Positive integers satisfying the elliptic determinant equation and the strict adjacency
bound are one of the three elementary triples. -/
theorem integer_elliptic_adjacency_cases {m n r : ℤ}
    (hm : 0 < m) (hn : 0 < n)
    (hdet : m * n = r ^ 2 + 1) (hadj : m + n - r < 4) :
    (m = 1 ∧ n = 1 ∧ r = 0) ∨
      (m = 1 ∧ n = 2 ∧ r = 1) ∨
      (m = 2 ∧ n = 1 ∧ r = 1) := by
  have hr : 0 ≤ r := by
    by_contra hr
    have hm1 : m = 1 := by omega
    have hn1 : n = 1 := by omega
    have hr1 : r = -1 := by omega
    rw [hm1, hn1, hr1] at hdet
    norm_num at hdet
  by_cases hm1 : m = 1
  · subst m
    have hrlt : r < 2 := by
      by_contra hrlt
      have hrtwo : 2 ≤ r := by omega
      nlinarith
    interval_cases r
    · left
      norm_num at hdet
      exact ⟨rfl, hdet, rfl⟩
    · right
      left
      norm_num at hdet
      exact ⟨rfl, hdet, rfl⟩
  by_cases hn1 : n = 1
  · subst n
    have hrlt : r < 2 := by
      by_contra hrlt
      have hrtwo : 2 ≤ r := by omega
      nlinarith
    interval_cases r
    · norm_num at hdet
      exact (hm1 hdet).elim
    · right
      right
      norm_num at hdet
      exact ⟨hdet, rfl, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hrLower : m + n - 3 ≤ r := by omega
  have hbaseNonneg : 0 ≤ m + n - 3 := by omega
  have hsumNonneg : 0 ≤ r + (m + n - 3) := by omega
  have hsquare : (m + n - 3) ^ 2 ≤ r ^ 2 := by
    have hmul : 0 ≤ (r - (m + n - 3)) * (r + (m + n - 3)) :=
      mul_nonneg (sub_nonneg.mpr hrLower) hsumNonneg
    nlinarith
  have hquadratic :
      m ^ 2 + m * n + n ^ 2 - 6 * m - 6 * n + 10 ≤ 0 := by
    nlinarith
  have hmUpper : m ≤ 3 := by
    by_contra hmUpper
    have hm4 : 4 ≤ m := by omega
    have hcross : 0 ≤ (m - 4) * (n - 2) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (m - 4), sq_nonneg (n - 2)]
  have hnUpper : n ≤ 3 := by
    by_contra hnUpper
    have hn4 : 4 ≤ n := by omega
    have hcross : 0 ≤ (m - 2) * (n - 4) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (m - 2), sq_nonneg (n - 4)]
  have hrUpper : r ≤ 2 := by
    by_contra hrUpper
    have hr3 : 3 ≤ r := by omega
    nlinarith
  interval_cases m <;> interval_cases n <;> interval_cases r <;>
    norm_num at hdet


end SphereSixComplex.Periods.IntegerEllipticAdjacency
