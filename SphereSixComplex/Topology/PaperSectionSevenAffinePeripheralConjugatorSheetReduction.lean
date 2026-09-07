module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandBasepointReduction
public import SphereSixComplex.Topology.PaperGeometricCentralCore

/-!
# Peripheral-conjugator reduction for the affine named sheets

The geometric finite meridians are conjugates of the standard elliptic generators by one
common cusp power.  An entering sheet acts from the left on the named lift, so its local
elliptic meridian has deck label `g⁻¹ * gᵢ * g`.  Hence such a sheet differs from the inverse
common cusp power only by the relevant finite stabilizer on the left.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- An entering sheet realizing the geometric order-three meridian belongs to the left
order-three-stabilizer coset of the inverse common peripheral conjugator. -/
public theorem orderThree_enteringSheet_eq_stabilizer_mul_cuspConjugator_inv
    (g : Delta)
    (hmeridian :
      g⁻¹ * g₁ * g = A.geometricCentralClockwiseOneDeck) :
    ∃ a : CyclicThree,
      g = Monoid.Coprod.inl a *
        ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₁ * g = q * g₁ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseOneDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₁ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₁ = g * (q * g₁ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₁ * g) * q := by rw [hconj]
      _ = g₁ * (g * q) := by group
  obtain ⟨a, ha⟩ := eq_inl_of_commute_g₁ (g * q) hcomm
  refine ⟨a, ?_⟩
  calc
    g = (g * q) * q⁻¹ := by group
    _ = Monoid.Coprod.inl a * q⁻¹ := by rw [ha]

/-- An entering sheet realizing the geometric order-four meridian belongs to the left
order-four-stabilizer coset of the same inverse common peripheral conjugator. -/
public theorem orderFour_enteringSheet_eq_stabilizer_mul_cuspConjugator_inv
    (g : Delta)
    (hmeridian :
      g⁻¹ * g₂ * g = A.geometricCentralClockwiseTwoDeck) :
    ∃ a : CyclicFour,
      g = Monoid.Coprod.inr a *
        ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹ := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₂ * g = q * g₂ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₂ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₂ = g * (q * g₂ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₂ * g) * q := by rw [hconj]
      _ = g₂ * (g * q) := by group
  obtain ⟨a, ha⟩ := eq_inr_of_commute_g₂ (g * q) hcomm
  refine ⟨a, ?_⟩
  calc
    g = (g * q) * q⁻¹ := by group
    _ = Monoid.Coprod.inr a * q⁻¹ := by rw [ha]

end SphereSixComplex.Geometry.PaperAnalyticData

end
