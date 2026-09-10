module
public import SphereSixComplex.Paper.TriangleGroup.Representation
import all SphereSixComplex.Paper.TriangleGroup.Representation
public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorMayerVietorisBases
/-! These identities audit the lattice classes in a signed two-slice comparison. They do not
assert that either signed difference is the actual geometric cusp boundary. -/

@[expose] public section
namespace SphereSixComplex.TriangleGroup
open LatticeData Matrix

public theorem rhoLambda_fourthBasis (g : Delta) :
    rhoLambda g ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
  have h₁ : ∀ a : CyclicThree,
      rhoLambda (Monoid.Coprod.inl a) ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    intro a
    have ha : a = Multiplicative.ofAdd (1 : ZMod 3) ^ a.toAdd.val := by
      apply Multiplicative.toAdd.injective
      simp
    rw [ha, map_pow]
    change rhoLambda (g₁ ^ a.toAdd.val) ![0, 0, 0, 1] = ![0, 0, 0, 1]
    generalize a.toAdd.val = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul]
      change rhoLambda (g₁ ^ n) (rhoLambda g₁ ![0, 0, 0, 1]) = ![0, 0, 0, 1]
      rw [rhoLambda_g₁_apply]
      have he : A₁ *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
        ext i
        fin_cases i <;> norm_num [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      rw [he, ih]
  have h₂ : ∀ a : CyclicFour,
      rhoLambda (Monoid.Coprod.inr a) ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    intro a
    have ha : a = Multiplicative.ofAdd (1 : ZMod 4) ^ a.toAdd.val := by
      apply Multiplicative.toAdd.injective
      simp
    rw [ha, map_pow]
    change rhoLambda (g₂ ^ a.toAdd.val) ![0, 0, 0, 1] = ![0, 0, 0, 1]
    generalize a.toAdd.val = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul]
      change rhoLambda (g₂ ^ n) (rhoLambda g₂ ![0, 0, 0, 1]) = ![0, 0, 0, 1]
      rw [rhoLambda_g₂_apply]
      have he : A₂ *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
        ext i
        fin_cases i <;> norm_num [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      rw [he, ih]
  induction g using Monoid.Coprod.induction_on with
  | inl a => exact h₁ a
  | inr a => exact h₂ a
  | mul a b ha hb =>
    rw [map_mul]
    exact (congrArg (rhoLambda a) hb).trans ha
public theorem inverse_orderThree_thirdBasis_difference :
    rhoLambda g₁⁻¹ ![0, 0, 1, 0] - ![0, 0, 1, 0] =
      SphereSixComplex.alphaOneKernelGenerator := by
  have hi : rhoLambda g₁⁻¹ ![0, 0, 1, 0] = ![0, -1, 0, 1] := by
    apply (rhoLambda g₁).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rw [rhoLambda_g₁_apply]
    ext i
    fin_cases i <;> norm_num [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hi]
  ext i
  fin_cases i <;> norm_num [SphereSixComplex.alphaOneKernelGenerator]

public theorem inverse_orderThree_fourthBasis_difference :
    rhoLambda g₁⁻¹ ![0, 0, 0, 1] - ![0, 0, 0, 1] = 0 := by
  rw [rhoLambda_fourthBasis, sub_self]

end SphereSixComplex.TriangleGroup
end