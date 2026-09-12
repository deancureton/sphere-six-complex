module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralCoverProductLiftComparison
import all SphereSixComplex.Paper.TriangleGroup.Representation

/-!
# The order-four boundary deck evaluation

The order-four cyclic-affine boundary deck group maps to the global affine deck group by
sending its positive meridian to the second free meridian and reversing lattice translations.
This computes the complete filling relation in the based-path orientation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.TriangleGroup

open LatticeData

public theorem rhoLambda_inr_epsilon' (a : CyclicFour) :
    rhoLambda (Monoid.Coprod.inr a) epsilon' = epsilon' := by
  have ha : a = Multiplicative.ofAdd (1 : ZMod 4) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  change rhoLambda (g₂ ^ a.toAdd.val) epsilon' = epsilon'
  generalize a.toAdd.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul]
    change rhoLambda (g₂ ^ n) (rhoLambda g₂ epsilon') = epsilon'
    rw [rhoLambda_g₂_apply, A₂_epsilon', ih]

public theorem rhoLambda_epsilon'_eq_of_commute_g₂ (g : Delta) (h : Commute g g₂) :
    rhoLambda g epsilon' = epsilon' := by
  obtain ⟨a, rfl⟩ := eq_inr_of_commute_g₂ g h
  exact rhoLambda_inr_epsilon' a

end SphereSixComplex.TriangleGroup

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex.TriangleGroup

variable (A : AnalyticData)

/-- Matching the first-power meridian determines the transported twist even when the entering
sheet is only known up to the finite elliptic stabilizer. -/
public theorem orderFour_enteringSheet_inverse_transports_epsilon'
    (g : Delta)
    (hmeridian : g⁻¹ * g₂ * g = A.geometricCentralClockwiseTwoDeck) :
    rhoLambda g⁻¹ epsilon' =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon' := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₂ * g = q * g₂ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseTwoDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₂ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₂ = g * (q * g₂ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₂ * g) * q := by rw [hconj]
      _ = g₂ * (g * q) := by group
  apply (rhoLambda g).injective
  rw [map_inv]
  change (rhoLambda g) ((rhoLambda g).symm epsilon') = _
  rw [LinearEquiv.apply_symm_apply]
  simpa only [map_mul, LinearEquiv.mul_apply] using
    (rhoLambda_epsilon'_eq_of_commute_g₂ (g * q) hcomm).symm














end SphereSixComplex.Geometry.AnalyticData

end

end
