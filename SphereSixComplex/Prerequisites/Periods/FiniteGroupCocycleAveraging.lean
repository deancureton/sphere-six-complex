module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Averaging one-cocycles of finite groups

For a finite group acting linearly on a module over a characteristic-zero division ring, every
additive one-cocycle is a coboundary.  The proof is the classical averaging argument.
-/

open scoped BigOperators

noncomputable section

namespace groupCohomology

variable {K G E : Type*} [DivisionRing K] [CharZero K] [Group G] [Fintype G]
  [AddCommGroup E] [Module K E] [DistribMulAction G E] [SMulCommClass G K E]

include K

/-- A one-cocycle of a finite group over a characteristic-zero division ring is explicitly the
difference between a vector and its translates. -/
public theorem finite_oneCocycle_eq_sub_smul (c : G → E) (hc : IsCocycle₁ c) :
    ∃ v : E, ∀ g, c g = v - g • v := by
  have hc' : ∀ g h, c (g * h) = c g + g • c h := by
    intro g h
    rw [hc]
    exact add_comm _ _
  let n : K := Fintype.card G
  let S : E := ∑ h : G, c h
  refine ⟨n⁻¹ • S, ?_⟩
  intro g
  have hperm : (∑ h : G, c (g * h)) = S := by
    simpa [S] using Equiv.sum_comp (Equiv.mulLeft g) c
  have hsum :
      (∑ h : G, c (g * h)) =
        (Fintype.card G : ℕ) • c g + g • S := by
    simp_rw [hc']
    rw [Finset.sum_add_distrib]
    simp [S, Finset.smul_sum]
  have hn : n ≠ 0 := by
    simp [n, Fintype.card_ne_zero]
  rw [hsum] at hperm
  have hcard : (Fintype.card G : ℕ) • c g = n • c g := by
    simp [n, Nat.cast_smul_eq_nsmul]
  rw [hcard] at hperm
  apply smul_right_injective E hn
  simp only [smul_sub, smul_smul]
  rw [mul_inv_cancel₀ hn, one_smul]
  rw [← smul_comm g n (n⁻¹ • S)]
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  exact eq_sub_iff_add_eq.mpr hperm

/-- The first cohomology cocycle of a finite group with coefficients over a characteristic-zero
division ring is a coboundary. -/
public theorem finite_oneCocycle_isCoboundary (c : G → E) (hc : IsCocycle₁ c) :
    IsCoboundary₁ c := by
  obtain ⟨v, hv⟩ := finite_oneCocycle_eq_sub_smul (K := K) c hc
  refine ⟨-v, ?_⟩
  intro g
  rw [smul_neg, hv g]
  abel

/-- An affine action of a finite group whose translation part is a one-cocycle has a fixed
point. -/
public theorem finite_affineAction_has_fixedPoint (c : G → E) (hc : IsCocycle₁ c) :
    ∃ v : E, ∀ g, g • v + c g = v := by
  obtain ⟨v, hv⟩ := finite_oneCocycle_eq_sub_smul (K := K) c hc
  exact ⟨v, fun g ↦ by rw [hv g]; abel⟩

end groupCohomology
