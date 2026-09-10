module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorCuspFrameBounds
import all SphereSixComplex.Paper.Periods.Functions
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section
noncomputable section

open Filter Set SphereSixComplex.TriangleGroup
open scoped Manifold

namespace SphereSixComplex.Periods.OrbifoldAffineDescentData

public theorem cusp_difference_zpow_invariant (P : OrbifoldAffineDescentData)
    (s : UpperHalfPlane → ℂ)
    (hs : ∀ z, s (fuchsianSourceAction g₀ • z) = P.affineCusp z (s z))
    (n : ℤ) (z : UpperHalfPlane) :
    s (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) -
      P.cuspSection (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) = s z - P.cuspSection z := by
  let d : UpperHalfPlane → ℂ := fun z ↦ s z - P.cuspSection z
  have hcusp (z : UpperHalfPlane) : d (fuchsianSourceAction g₀ • z) = d z := by
    dsimp only [d]
    rw [hs, P.cuspSection_equivariant, P.affineCusp_sub]
  have hprod (z : UpperHalfPlane) : d (fuchsianSourceAction (g₁ * g₂) • z) = d z := by
    have h := hcusp (fuchsianSourceAction (g₁ * g₂) • z)
    have hrel : g₀ * (g₁ * g₂) = 1 := mul_eq_one_comm.mp g₁_mul_g₂_mul_g₀
    simpa only [← mul_smul, ← map_mul, hrel, map_one, one_smul] using h.symm
  have hnat (m : ℕ) (z : UpperHalfPlane) :
      d (fuchsianSourceAction ((g₁ * g₂) ^ m) • z) = d z := by
    induction m with
    | zero => simp
    | succ m hm => rw [pow_succ', map_mul, mul_smul, hprod, hm]
  change d (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) = d z
  cases n with
  | ofNat m => simpa using hnat m z
  | negSucc m =>
    have h := hnat (m + 1) (fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z)
    have hcancel : fuchsianSourceAction ((g₁ * g₂) ^ (m + 1)) •
        (fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z) = z := by
      rw [← mul_smul, ← map_mul]
      simp [zpow_negSucc]
    rw [hcancel] at h
    exact h.symm

public theorem cusp_difference_bounded_of_infinity_germ
    (P : OrbifoldAffineDescentData) (s : UpperHalfPlane → ℂ)
    (hs : MDiff s)
    (hseq : ∀ z, s (fuchsianSourceAction g₀ • z) = P.affineCusp z (s z))
    (f : ℂ → ℂ) (hf : ContinuousAt f 0)
    (heq : ∀ᶠ z in upperHalfPlaneAtInfinity,
      s z - P.cuspSection z = P.frameInfinity z * f ((P.quotient.coordinate z)⁻¹)) :
    BoundedOn (fun z ↦ s z - P.cuspSection z) fuchsianCuspRegion := by
  obtain ⟨B, hB, hframe⟩ := P.frameInfinity_cusp_bounded
  have hgerm : ∀ᶠ z in upperHalfPlaneAtInfinity,
      ‖f ((P.quotient.coordinate z)⁻¹)‖ < ‖f 0‖ + 1 :=
    (hf.norm.tendsto.comp P.quotient.inverse_coordinate_tendsto_zero).eventually
      (gt_mem_nhds (lt_add_one _))
  have hcusp : ∀ᶠ z in upperHalfPlaneAtInfinity, z ∈ fuchsianCuspRegion :=
    (eventually_ge_atTop (1 : ℝ)).comap UpperHalfPlane.im
  apply boundedOn_cusp_of_eventually_bounded (fun z ↦ s z - P.cuspSection z)
    (hs.continuous.sub P.cuspSection_holomorphic.continuous).continuousOn
    (fun n z _ ↦ P.cusp_difference_zpow_invariant s hseq n z)
    (mul_nonneg hB (by positivity : 0 ≤ ‖f 0‖ + 1))
  filter_upwards [heq, hgerm, hcusp] with z hz hzg hzc
  rw [hz, norm_mul]
  exact mul_le_mul (hframe z hzc) hzg.le (norm_nonneg _) hB

end SphereSixComplex.Periods.OrbifoldAffineDescentData
