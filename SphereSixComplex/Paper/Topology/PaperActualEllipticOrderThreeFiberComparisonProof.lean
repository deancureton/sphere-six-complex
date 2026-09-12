module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseFactorHomotopyProof
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.TriangleGroup

open LatticeData

public theorem rhoLambda_inl_epsilon (a : CyclicThree) :
    rhoLambda (Monoid.Coprod.inl a) epsilon = epsilon := by
  have ha : a = Multiplicative.ofAdd (1 : ZMod 3) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  change rhoLambda (g₁ ^ a.toAdd.val) epsilon = epsilon
  generalize a.toAdd.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul]
    change rhoLambda (g₁ ^ n) (rhoLambda g₁ epsilon) = epsilon
    rw [rhoLambda_g₁_apply, A₁_epsilon, ih]

public theorem rhoLambda_epsilon_eq_of_commute_g₁ (g : Delta) (h : Commute g g₁) :
    rhoLambda g epsilon = epsilon := by
  obtain ⟨a, rfl⟩ := eq_inl_of_commute_g₁ g h
  exact rhoLambda_inl_epsilon a

end SphereSixComplex.TriangleGroup

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.TriangleGroup

variable (A : AnalyticData)

/-- The first-power meridian determines the corrected twist label without choosing a unique
sheet inside the finite elliptic stabilizer. -/
public theorem orderThree_enteringSheet_inverse_transports_epsilon
    (g : Delta)
    (hmeridian : g⁻¹ * g₁ * g = A.geometricCentralClockwiseOneDeck) :
    rhoLambda g⁻¹ epsilon =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₁ * g = q * g₁ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseOneDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₁ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₁ = g * (q * g₁ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₁ * g) * q := by rw [hconj]
      _ = g₁ * (g * q) := by group
  apply (rhoLambda g).injective
  rw [map_inv]
  change (rhoLambda g) ((rhoLambda g).symm epsilon) = _
  rw [LinearEquiv.apply_symm_apply]
  simpa only [map_mul, LinearEquiv.mul_apply] using
    (rhoLambda_epsilon_eq_of_commute_g₁ (g * q) hcomm).symm
























end SphereSixComplex.Geometry.AnalyticData

end

end
