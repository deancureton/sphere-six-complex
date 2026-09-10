module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorSingularSections
public import SphereSixComplex.Paper.Geometry.EstablishedFuchsianCuspNeighborhoodProof
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section
noncomputable section

open SphereSixComplex.TriangleGroup SphereSixComplex.Geometry
open SphereSixComplex.Geometry.FuchsianCuspNeighborhoodProof
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open scoped Manifold

namespace SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem

public theorem affineTransport_cusp (P : OrbifoldAffineLineTorsorDescentProblem)
    (z : UpperHalfPlane) (u : ℂ) :
    P.affineTransport g₀ (z, u) = (fuchsianSourceAction g₀ • z, P.affineCusp z u) := by
  apply (P.affineTransport (g₁ * g₂)).injective
  have hprod : P.affineTransport (g₁ * g₂)
      (fuchsianSourceAction g₀ • z, P.affineCusp z u) = (z, u) := by
    apply Prod.ext
    · rw [P.affineTransport_fst, ← mul_smul, ← map_mul, g₁_mul_g₂_mul_g₀]
      simp
    · rw [map_mul, Equiv.Perm.mul_apply, P.affineTransport_one, P.affineTransport_two]
      change P.affineOne (fuchsianSourceAction g₂ • (fuchsianSourceAction g₀ • z))
        (P.affineTwo (fuchsianSourceAction g₀ • z) (P.affineCusp z u)) = u
      simpa only [← mul_smul, ← map_mul] using P.cusp_product z u
  rw [hprod, ← Equiv.Perm.mul_apply, ← map_mul, g₁_mul_g₂_mul_g₀, map_one]
  rfl

public theorem transportSection_inv_fixed (P : OrbifoldAffineLineTorsorDescentProblem)
    {g : Delta} {t : UpperHalfPlane → ℂ} (ht : P.transportSection g t = t) :
    P.transportSection g⁻¹ t = t := by
  have h := congrArg (P.transportSection g⁻¹) ht
  rw [← P.transportSection_mul, inv_mul_cancel, P.transportSection_one] at h
  exact h.symm

public theorem transportSection_zpow_fixed (P : OrbifoldAffineLineTorsorDescentProblem)
    {g : Delta} {t : UpperHalfPlane → ℂ} (ht : P.transportSection g t = t) (n : ℤ) :
    P.transportSection (g ^ n) t = t := by
  cases n with
  | ofNat n => simpa using P.transportSection_pow_fixed ht n
  | negSucc n =>
      simpa only [zpow_negSucc] using
        P.transportSection_inv_fixed (P.transportSection_pow_fixed ht (n + 1))

public theorem transportSection_cusp_fixed (P : OrbifoldAffineLineTorsorDescentProblem)
    (n : ℤ) : P.transportSection (g₀ ^ n) P.cuspSection = P.cuspSection := by
  apply P.transportSection_zpow_fixed
  funext z
  simp only [transportSection, P.affineTransport_cusp]
  simpa only [map_inv, smul_inv_smul] using
    (P.cuspSection_equivariant (fuchsianSourceAction g₀⁻¹ • z)).symm

public theorem deep_cusp_translate_power {g : Delta} {z : UpperHalfPlane}
    (hz : 1 < z.im) (hgz : 1 < (fuchsianSourceAction g • z).im) :
    ∃ n : ℤ, g = g₀ ^ n := by
  by_cases hc : (deltaBottomRow g).1 = 0
  · obtain ⟨B, _, hB⟩ := exists_isTranslationBy_of_bottomLeft_eq_zero hc
    exact exists_zpow_g₀_of_isTranslationBy hB
  · have hle := im_smul_le_one_div_im hc z
    have hlt : 1 / z.im < 1 := (div_lt_one z.im_pos).mpr hz
    exact False.elim ((not_lt_of_ge (hle.trans hlt.le)) hgz)

public theorem exists_cusp_local_equivariant_section
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    ∃ W : Set ℂ, IsOpen W ∧
      (∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ W) ∧
      ∃ s : UpperHalfPlane → ℂ,
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z) ∧
      (∀ z, 1 < z.im → s z = P.cuspSection z) ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  let S : Set UpperHalfPlane := {z | 1 < z.im}
  have hS : IsOpen S := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  have hprecise : ∀ g x, x ∈ S → fuchsianSourceAction g • x ∈ S →
      P.transportSection g P.cuspSection = P.cuspSection := by
    intro g x hx hgx
    obtain ⟨n, rfl⟩ := deep_cusp_translate_power hx hgx
    exact P.transportSection_cusp_fixed n
  obtain ⟨s, hdiff, heq, hequiv⟩ := P.exists_equivariant_section_on_precise_saturation
    hS P.cuspSection P.cuspSection_holomorphic hprecise
  have hcompact := orientedFuchsianCompactCore_isCompact.image
    P.quotient.coordinate_holomorphic.continuous
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hexterior : (Metric.ball (0 : ℂ) R)ᶜ ⊆ P.quotient.coordinate '' S := by
    intro q hq
    obtain ⟨z, rfl⟩ := P.quotient.coordinate_isQuotientMap.surjective q
    obtain ⟨g, hg⟩ := exists_smul_mem_orientedFundamentalRegion z
    by_cases hdeep : 1 < (fuchsianSourceAction g • z).im
    · exact ⟨_, hdeep, P.quotient.coordinate_invariant g z⟩
    · have hcore : fuchsianSourceAction g • z ∈ orientedFuchsianCompactCore := by
        rcases orientedFundamentalRegion_mem_cusp_or_compactCore hg with hcusp | hcore
        · exact ⟨abs_re_le_two_of_mem_orientedFundamentalRegion hg,
            le_trans (by norm_num) hcusp, le_of_not_gt hdeep⟩
        · exact hcore
      have hqball := hbound ⟨_, hcore, P.quotient.coordinate_invariant g z⟩
      exact False.elim (hq hqball)
  exact ⟨P.quotient.coordinate '' S, P.coordinate_isOpenMap S hS, ⟨R, hR, hexterior⟩,
    s, fun z hz ↦ hdiff z ((P.coordinate_image_mem_iff_saturation S z).mp hz),
    heq, fun h z hz ↦ hequiv h z ((P.coordinate_image_mem_iff_saturation S z).mp hz)⟩

end SphereSixComplex.Periods.OrbifoldAffineLineTorsorDescentProblem
