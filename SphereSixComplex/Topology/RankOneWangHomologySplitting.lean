module

public import SphereSixComplex.Topology.NormalizedWangHomologySplitting

/-!
# Rank-one Wang splittings

A lift of a positive generator of the invariant quotient canonically normalizes a Wang splitting
when both end terms have rank one.  The resulting two coordinates are ordered with the invariant
coordinate first and the coinvariant coordinate second.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- The normalized Wang section determined by a lift of the positive invariant generator. -/
public def rankOneNormalizedSplitting
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (invariants : P.Invariants ≃ₗ[ℤ] ℤ) (s : Total)
    (hs : invariants (P.totalToInvariants s) = 1) : P.NormalizedSplitting where
  sweptSection := invariants.toLinearMap.smulRight s
  rightInverse := by
    apply LinearMap.ext
    intro x
    apply invariants.injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, map_smul, hs, smul_eq_mul, mul_one]
    rfl

/-- Swap a pair of integer coordinates into a rank-two vector. -/
public def coinvariantInvariantPairEquiv : (ℤ × ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x.2, x.1]
  invFun x := (x 1, x 0)
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' n x := by
    funext i
    fin_cases i <;> simp
  left_inv x := by
    ext <;> simp
  right_inv x := by
    funext i
    fin_cases i <;> simp

/-- Rank-two Wang coordinates normalized by a chosen invariant generator lift.

Coordinate zero is the invariant coordinate and coordinate one is the coinvariant coordinate.
-/
public def rankOneTotalLinearEquiv
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] ℤ) (invariants : P.Invariants ≃ₗ[ℤ] ℤ)
    (s : Total) (hs : invariants (P.totalToInvariants s) = 1) :
    Total ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (NormalizedSplitting.totalLinearEquivOfEndCoordinates P
      (rankOneNormalizedSplitting P invariants s hs) coinvariants invariants).trans
    coinvariantInvariantPairEquiv

/-- The additive equivalence underlying the normalized rank-two Wang coordinates. -/
public def rankOneTotalAddEquiv
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] ℤ) (invariants : P.Invariants ≃ₗ[ℤ] ℤ)
    (s : Total) (hs : invariants (P.totalToInvariants s) = 1) :
    Total ≃+ (Fin 2 → ℤ) :=
  (rankOneTotalLinearEquiv P coinvariants invariants s hs).toAddEquiv

/-- The chosen lift is the first standard basis vector. -/
public theorem rankOneTotalAddEquiv_apply_generator
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] ℤ) (invariants : P.Invariants ≃ₗ[ℤ] ℤ)
    (s : Total) (hs : invariants (P.totalToInvariants s) = 1) :
    rankOneTotalAddEquiv P coinvariants invariants s hs s = ![1, 0] := by
  change rankOneTotalLinearEquiv P coinvariants invariants s hs s = ![1, 0]
  let S := rankOneNormalizedSplitting P invariants s hs
  have hswept : S.sweptSection (P.totalToInvariants s) = s := by
    dsimp [S, rankOneNormalizedSplitting]
    calc
      _ = invariants (P.totalToInvariants s) • s := rfl
      _ = (1 : ℤ) • s := congrArg (fun n : ℤ ↦ n • s) hs
      _ = s := one_zsmul s
  have h := NormalizedSplitting.totalLinearEquiv_sweptSection
    P S (P.totalToInvariants s)
  rw [hswept] at h
  change coinvariantInvariantPairEquiv
    ((coinvariants.prodCongr invariants)
      (NormalizedSplitting.totalLinearEquiv P S s)) = ![1, 0]
  rw [h]
  funext i
  fin_cases i
  · change invariants (P.totalToInvariants s) = 1
    exact hs
  · change coinvariants 0 = 0
    exact map_zero coinvariants

/-- A fibre coinvariant is the second coordinate with zero invariant coordinate. -/
public theorem rankOneTotalAddEquiv_coinvariantsToTotal
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] ℤ) (invariants : P.Invariants ≃ₗ[ℤ] ℤ)
    (s : Total) (hs : invariants (P.totalToInvariants s) = 1) (q : P.Coinvariants) :
    rankOneTotalAddEquiv P coinvariants invariants s hs (P.coinvariantsToTotal q) =
      ![0, coinvariants q] := by
  change rankOneTotalLinearEquiv P coinvariants invariants s hs (P.coinvariantsToTotal q) =
    ![0, coinvariants q]
  let S := rankOneNormalizedSplitting P invariants s hs
  have h := NormalizedSplitting.totalLinearEquiv_coinvariantsToTotal P S q
  change coinvariantInvariantPairEquiv
    ((coinvariants.prodCongr invariants)
      (NormalizedSplitting.totalLinearEquiv P S (P.coinvariantsToTotal q))) =
    ![0, coinvariants q]
  rw [h]
  funext i
  fin_cases i
  · change invariants 0 = 0
    exact map_zero invariants
  · rfl

end SphereSixComplex.WangHomologyPresentation
