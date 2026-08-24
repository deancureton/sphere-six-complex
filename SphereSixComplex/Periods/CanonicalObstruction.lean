module

public import SphereSixComplex.Periods.Functions

/-!
# Obstruction to the identity-source period model

The triangle-group upper half-plane in the paper cannot be identified with the modular-parameter
upper half-plane.  Under `rhoTauReal`, the square of the order-four generator acts trivially, but
the affine transformation law for `mu` has order four rather than two.  Consequently the current
identity-source `CanonicalMuBetaEquivariantData` contract has no inhabitants.
-/

open UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- The modular image of the order-four generator has order two on the upper half-plane. -/
public theorem rhoTauReal_g2_smul_twice (z : UpperHalfPlane) :
    rhoTauReal g₂ • (rhoTauReal g₂ • z) = z := by
  apply UpperHalfPlane.coe_injective
  rw [rhoTauReal_g2_smul, rhoTauReal_g2_smul]
  field_simp [z.ne_zero]

/-- Iterating the claimed order-four affine law twice forces an explicit global formula. -/
public theorem mu_eq_localMuTwo_of_transform_two
    (mu : UpperHalfPlane → ℂ)
    (hmu : ∀ z, mu (rhoTauReal g₂ • z) = 1 + mu z / z) (z : UpperHalfPlane) :
    mu z = (1 - (z : ℂ)) / 2 := by
  have h₁ := hmu z
  have h₂ := hmu (rhoTauReal g₂ • z)
  rw [rhoTauReal_g2_smul_twice] at h₂
  rw [h₁, rhoTauReal_g2_smul] at h₂
  field_simp [z.ne_zero] at h₂
  linear_combination h₂ / 2

/-- The same forced formula holds for an arbitrary equivariant modular-parameter map. -/
public theorem mu_eq_localMuTwo_of_tau_transform_two
    (tau : UpperHalfPlane → UpperHalfPlane) (mu : UpperHalfPlane → ℂ)
    (htau : ∀ z, (tau (rhoTauReal g₂ • z) : ℂ) = -1 / tau z)
    (hmu : ∀ z, mu (rhoTauReal g₂ • z) = 1 + mu z / tau z)
    (z : UpperHalfPlane) : mu z = (1 - (tau z : ℂ)) / 2 := by
  have ht₁ := htau z
  have ht₂ := htau (rhoTauReal g₂ • z)
  have hm₁ := hmu z
  have hm₂ := hmu (rhoTauReal g₂ • z)
  rw [rhoTauReal_g2_smul_twice] at ht₂ hm₂
  rw [ht₁, hm₁] at hm₂
  field_simp [(tau z).ne_zero] at hm₂
  linear_combination hm₂ / 2

/-- No function satisfies both affine generator laws after identifying the source action with
the modular action. -/
public theorem not_exists_mu_for_rhoTauReal :
    ¬ ∃ mu : UpperHalfPlane → ℂ,
      (∀ z, mu (rhoTauReal g₁ • z) = (1 - mu z) / z) ∧
      (∀ z, mu (rhoTauReal g₂ • z) = 1 + mu z / z) := by
  rintro ⟨mu, hOne, hTwo⟩
  let z : UpperHalfPlane := UpperHalfPlane.I
  have hz := mu_eq_localMuTwo_of_transform_two mu hTwo z
  have hgz := mu_eq_localMuTwo_of_transform_two mu hTwo (rhoTauReal g₁ • z)
  have h := hOne z
  rw [hz, hgz, rhoTauReal_g1_smul] at h
  have hne : (z : ℂ) ≠ 0 := z.ne_zero
  field_simp [hne] at h
  ring_nf at h
  have hz0 : (z : ℂ) = 0 := by
    apply add_left_cancel (a := (1 : ℂ))
    simpa using h.symm
  exact hne hz0

/-- Collapsing the order-four source action to the order-two modular action is incompatible with
the `tau` and `mu` transformation laws, independently of holomorphy or cusp regularity. -/
public theorem not_exists_tau_mu_for_rhoTauReal :
    ¬ ∃ (tau : UpperHalfPlane → UpperHalfPlane) (mu : UpperHalfPlane → ℂ),
      (∀ z, (tau (rhoTauReal g₁ • z) : ℂ) = ((tau z : ℂ) - 1) / tau z) ∧
      (∀ z, (tau (rhoTauReal g₂ • z) : ℂ) = -1 / tau z) ∧
      (∀ z, mu (rhoTauReal g₁ • z) = (1 - mu z) / tau z) ∧
      (∀ z, mu (rhoTauReal g₂ • z) = 1 + mu z / tau z) := by
  rintro ⟨tau, mu, hTauOne, hTauTwo, hMuOne, hMuTwo⟩
  let z : UpperHalfPlane := UpperHalfPlane.I
  have hz := mu_eq_localMuTwo_of_tau_transform_two tau mu hTauTwo hMuTwo z
  have hgz := mu_eq_localMuTwo_of_tau_transform_two tau mu hTauTwo hMuTwo
    (rhoTauReal g₁ • z)
  have ht := hTauOne z
  have hm := hMuOne z
  rw [hz, hgz, ht] at hm
  have hne : (tau z : ℂ) ≠ 0 := (tau z).ne_zero
  field_simp [hne] at hm
  ring_nf at hm
  have hz0 : (tau z : ℂ) = 0 := by
    apply add_left_cancel (a := (1 : ℂ))
    simpa using hm.symm
  exact hne hz0

/-- The current identity-source canonical `mu, beta` contract is inconsistent. -/
public theorem not_nonempty_canonicalMuBetaEquivariantData :
    ¬ Nonempty CanonicalMuBetaEquivariantData := by
  rintro ⟨D⟩
  exact not_exists_mu_for_rhoTauReal
    ⟨D.mu, D.mu_transform_one, D.mu_transform_two⟩

/-- In particular, neither the pre-data nor the nondegenerate canonical data can be constructed
without replacing the identity-source uniformization. -/
public theorem not_nonempty_canonicalMuBetaPreData : ¬ Nonempty CanonicalMuBetaPreData := by
  rintro ⟨D⟩
  exact not_nonempty_canonicalMuBetaEquivariantData
    ⟨D.toCanonicalMuBetaEquivariantData⟩

public theorem not_nonempty_canonicalMuBetaData : ¬ Nonempty CanonicalMuBetaData := by
  rintro ⟨D⟩
  exact not_nonempty_canonicalMuBetaEquivariantData
    ⟨D.toCanonicalMuBetaEquivariantData⟩

end SphereSixComplex.Periods
