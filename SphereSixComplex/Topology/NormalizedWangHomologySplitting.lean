module

public import SphereSixComplex.Topology.CircleMappingTorusHomologyBases

/-!
# Normalized splittings of Wang presentations

A projective splitting proves the rank of the middle homology group but is not canonical.  For
geometric cycle calculations one instead supplies an explicit section of the boundary map.  This
module constructs the resulting coordinates and proves their normalization on fibre inclusions
and swept cycles.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]
  (P : WangHomologyPresentation HighRelations High Total LowRelations Low)

/-- A geometrically normalized section of the invariant quotient in a Wang presentation. -/
public structure NormalizedSplitting where
  sweptSection : P.Invariants →ₗ[ℤ] Total
  rightInverse : P.totalToInvariants.comp sweptSection = LinearMap.id

namespace NormalizedSplitting

variable (S : NormalizedSplitting P)

public def residual : Total →ₗ[ℤ] Total :=
  LinearMap.id - S.sweptSection.comp P.totalToInvariants

public theorem residual_mem_range (x : Total) :
    residual P S x ∈ LinearMap.range P.coinvariantsToTotal := by
  apply (P.exact_coinvariantsToTotal_totalToInvariants (residual P S x)).mp
  have h := DFunLike.congr_fun S.rightInverse (P.totalToInvariants x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
  change P.totalToInvariants (x - S.sweptSection (P.totalToInvariants x)) = 0
  rw [map_sub, h, sub_self]

public noncomputable def residualCoordinate : Total →ₗ[ℤ] P.Coinvariants :=
  let e : P.Coinvariants ≃ₗ[ℤ] LinearMap.range P.coinvariantsToTotal :=
    LinearEquiv.ofInjective P.coinvariantsToTotal P.coinvariantsToTotal_injective
  e.symm.toLinearMap.comp
    ((residual P S).codRestrict (LinearMap.range P.coinvariantsToTotal)
      (residual_mem_range P S))

/-- Coordinates determined by the chosen swept-cycle section. -/
public noncomputable def totalLinearEquiv :
    Total ≃ₗ[ℤ] P.Coinvariants × P.Invariants := by
  let forward : Total →ₗ[ℤ] P.Coinvariants × P.Invariants :=
    (residualCoordinate P S).prod P.totalToInvariants
  let inverse : P.Coinvariants × P.Invariants →ₗ[ℤ] Total :=
    LinearMap.coprod P.coinvariantsToTotal S.sweptSection
  refine LinearEquiv.ofLinearMap forward inverse ?_ ?_
  · apply LinearMap.ext
    rintro ⟨y, z⟩
    have hboundaryCoinvariant (y : P.Coinvariants) :
        P.totalToInvariants (P.coinvariantsToTotal y) = 0 :=
      P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero y
    have hboundarySection (z : P.Invariants) :
        P.totalToInvariants (S.sweptSection z) = z := by
      have h := DFunLike.congr_fun S.rightInverse z
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using h
    apply Prod.ext
    · let e : P.Coinvariants ≃ₗ[ℤ] LinearMap.range P.coinvariantsToTotal :=
        LinearEquiv.ofInjective P.coinvariantsToTotal P.coinvariantsToTotal_injective
      apply e.injective
      apply Subtype.ext
      change P.coinvariantsToTotal
          (residualCoordinate P S (P.coinvariantsToTotal y + S.sweptSection z)) =
        P.coinvariantsToTotal y
      have hresidual :
          P.coinvariantsToTotal
              (residualCoordinate P S (P.coinvariantsToTotal y + S.sweptSection z)) =
            residual P S (P.coinvariantsToTotal y + S.sweptSection z) := by
        exact congrArg Subtype.val
          (e.apply_symm_apply
            ((residual P S).codRestrict (LinearMap.range P.coinvariantsToTotal)
              (residual_mem_range P S) (P.coinvariantsToTotal y + S.sweptSection z)))
      rw [hresidual]
      change P.coinvariantsToTotal y + S.sweptSection z -
          S.sweptSection (P.totalToInvariants
            (P.coinvariantsToTotal y + S.sweptSection z)) = P.coinvariantsToTotal y
      rw [map_add, hboundaryCoinvariant, hboundarySection, zero_add]
      abel
    · change P.totalToInvariants (P.coinvariantsToTotal y + S.sweptSection z) = z
      rw [map_add, hboundaryCoinvariant, hboundarySection, zero_add]
  · apply LinearMap.ext
    intro x
    have hresidual :
        P.coinvariantsToTotal (residualCoordinate P S x) = residual P S x := by
      let e : P.Coinvariants ≃ₗ[ℤ] LinearMap.range P.coinvariantsToTotal :=
        LinearEquiv.ofInjective P.coinvariantsToTotal P.coinvariantsToTotal_injective
      exact congrArg Subtype.val
        (e.apply_symm_apply
          ((residual P S).codRestrict (LinearMap.range P.coinvariantsToTotal)
            (residual_mem_range P S) x))
    change P.coinvariantsToTotal (residualCoordinate P S x) +
        S.sweptSection (P.totalToInvariants x) = x
    rw [hresidual]
    change x - S.sweptSection (P.totalToInvariants x) +
      S.sweptSection (P.totalToInvariants x) = x
    abel

/-- Fibre classes have zero swept-cycle coordinate. -/
public theorem totalLinearEquiv_coinvariantsToTotal (x : P.Coinvariants) :
    totalLinearEquiv P S (P.coinvariantsToTotal x) = (x, 0) := by
  apply Prod.ext
  · apply P.coinvariantsToTotal_injective
    have hboundary :=
      P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero x
    change P.coinvariantsToTotal
        (residualCoordinate P S (P.coinvariantsToTotal x)) = P.coinvariantsToTotal x
    have hresidual :
        P.coinvariantsToTotal (residualCoordinate P S (P.coinvariantsToTotal x)) =
          residual P S (P.coinvariantsToTotal x) := by
      let e : P.Coinvariants ≃ₗ[ℤ] LinearMap.range P.coinvariantsToTotal :=
        LinearEquiv.ofInjective P.coinvariantsToTotal P.coinvariantsToTotal_injective
      exact congrArg Subtype.val
        (e.apply_symm_apply
          ((residual P S).codRestrict (LinearMap.range P.coinvariantsToTotal)
            (residual_mem_range P S) (P.coinvariantsToTotal x)))
    rw [hresidual]
    change P.coinvariantsToTotal x -
        S.sweptSection (P.totalToInvariants (P.coinvariantsToTotal x)) =
      P.coinvariantsToTotal x
    rw [hboundary, map_zero, sub_zero]
  · exact P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero x

/-- The chosen swept cycles have zero fibre coordinate and their prescribed invariant
coordinate. -/
public theorem totalLinearEquiv_sweptSection (x : P.Invariants) :
    totalLinearEquiv P S (S.sweptSection x) = (0, x) := by
  apply Prod.ext
  · change residualCoordinate P S (S.sweptSection x) = 0
    apply P.coinvariantsToTotal_injective
    have hresidual :
        P.coinvariantsToTotal (residualCoordinate P S (S.sweptSection x)) =
          residual P S (S.sweptSection x) := by
      let e : P.Coinvariants ≃ₗ[ℤ] LinearMap.range P.coinvariantsToTotal :=
        LinearEquiv.ofInjective P.coinvariantsToTotal P.coinvariantsToTotal_injective
      exact congrArg Subtype.val
        (e.apply_symm_apply
          ((residual P S).codRestrict (LinearMap.range P.coinvariantsToTotal)
            (residual_mem_range P S) (S.sweptSection x)))
    rw [hresidual]
    rw [map_zero]
    change S.sweptSection x -
      S.sweptSection (P.totalToInvariants (S.sweptSection x)) = 0
    have h := DFunLike.congr_fun S.rightInverse x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
    rw [h, sub_self]
  · change P.totalToInvariants (S.sweptSection x) = x
    have h := DFunLike.congr_fun S.rightInverse x
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using h

/-- Apply selected coordinate equivalences after the normalized splitting. -/
public noncomputable def totalLinearEquivOfEndCoordinates
    {CoinvariantCoordinates InvariantCoordinates : Type*}
    [AddCommGroup CoinvariantCoordinates] [AddCommGroup InvariantCoordinates]
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] CoinvariantCoordinates)
    (invariants : P.Invariants ≃ₗ[ℤ] InvariantCoordinates) :
    Total ≃ₗ[ℤ] CoinvariantCoordinates × InvariantCoordinates :=
  (totalLinearEquiv P S).trans (coinvariants.prodCongr invariants)

end NormalizedSplitting

end SphereSixComplex.WangHomologyPresentation
