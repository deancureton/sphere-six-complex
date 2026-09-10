module

public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentation
public import Mathlib.Algebra.Module.Projective

@[expose] public section
noncomputable section
namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- A Wang presentation splits as its coinvariants times its invariants whenever the latter are
projective. -/
public noncomputable def linearEquiv
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Module.Projective ℤ P.Invariants] :
    Total ≃ₗ[ℤ] P.Coinvariants × P.Invariants := by
  let i := P.coinvariantsToTotal
  let p := P.totalToInvariants
  let splitting := Module.projective_lifting_property p LinearMap.id
    P.totalToInvariants_surjective
  let s := Classical.choose splitting
  have hs := Classical.choose_spec splitting
  let residual : Total →ₗ[ℤ] Total := LinearMap.id - s.comp p
  have hresidual (x : Total) : residual x ∈ LinearMap.range i := by
    apply (P.exact_coinvariantsToTotal_totalToInvariants (residual x)).mp
    have hsx := DFunLike.congr_fun hs (p x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hsx
    change p (x - s (p x)) = 0
    rw [map_sub, hsx, sub_self]
  let residualRange : Total →ₗ[ℤ] LinearMap.range i :=
    residual.codRestrict (LinearMap.range i) hresidual
  let iEquivRange : P.Coinvariants ≃ₗ[ℤ] LinearMap.range i :=
    LinearEquiv.ofInjective i P.coinvariantsToTotal_injective
  let r : Total →ₗ[ℤ] P.Coinvariants := iEquivRange.symm.toLinearMap.comp residualRange
  let forward : Total →ₗ[ℤ] P.Coinvariants × P.Invariants := r.prod p
  let inverse : P.Coinvariants × P.Invariants →ₗ[ℤ] Total := LinearMap.coprod i s
  refine LinearEquiv.ofLinearMap forward inverse ?_ ?_
  · apply LinearMap.ext
    rintro ⟨y, z⟩
    have hpi (y : P.Coinvariants) : p (i y) = 0 := by
      exact P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero y
    have hps (y : P.Invariants) : p (s y) = y := by
      have hsy := DFunLike.congr_fun hs y
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using hsy
    have hr : r (i y + s z) = y := by
      apply iEquivRange.injective
      apply Subtype.ext
      change i (r (i y + s z)) = i y
      have hir : i (r (i y + s z)) = residual (i y + s z) := by
        change i (iEquivRange.symm (residualRange (i y + s z))) = residual (i y + s z)
        exact congrArg Subtype.val
          (iEquivRange.apply_symm_apply (residualRange (i y + s z)))
      rw [hir]
      change i y + s z - s (p (i y + s z)) = i y
      rw [map_add, hpi, hps, map_add, map_zero, zero_add]
      abel
    apply Prod.ext
    · exact hr
    · change p (i y + s z) = z
      rw [map_add, hpi, hps, zero_add]
  · apply LinearMap.ext
    intro x
    have hi : i (r x) = residual x := by
      change i (iEquivRange.symm (residualRange x)) = residual x
      exact congrArg Subtype.val (iEquivRange.apply_symm_apply (residualRange x))
    simp only [LinearMap.comp_apply]
    change i (r x) + s (p x) = x
    rw [hi]
    change x - s (p x) + s (p x) = x
    abel

/-- Split a Wang presentation and then apply chosen coordinates on its two ends. -/
public noncomputable def linearEquivOfCoordinates
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    {CoinvariantCoordinates InvariantCoordinates : Type*}
    [AddCommGroup CoinvariantCoordinates] [AddCommGroup InvariantCoordinates]
    [Module.Projective ℤ InvariantCoordinates]
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] CoinvariantCoordinates)
    (invariants : P.Invariants ≃ₗ[ℤ] InvariantCoordinates) :
    Total ≃ₗ[ℤ] CoinvariantCoordinates × InvariantCoordinates := by
  letI : Module.Projective ℤ P.Invariants :=
    Module.Projective.of_equiv' invariants.symm
  exact P.linearEquiv.trans
    (coinvariants.prodCongr invariants)

end WangHomologyPresentation

namespace CircleMappingTorusHomologyBases


variable {E C : Type*} [AddCommGroup E] [AddCommGroup C]

public theorem map_range_eq_of_conjugates (e : E ≃ₗ[ℤ] C) (d : E →ₗ[ℤ] E)
    (D : C →ₗ[ℤ] C) (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (LinearMap.range d).map e.toLinearMap = LinearMap.range D := by
  rw [← LinearMap.range_comp, h, LinearMap.range_comp]
  simp

public theorem map_ker_eq_of_conjugates (e : E ≃ₗ[ℤ] C) (d : E →ₗ[ℤ] E)
    (D : C →ₗ[ℤ] C) (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (LinearMap.ker d).map e.toLinearMap = LinearMap.ker D := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hx' := LinearMap.mem_ker.mp hx
    have hpoint := DFunLike.congr_fun h x
    simp only [LinearMap.coe_comp, Function.comp_apply] at hpoint
    rw [← hpoint, hx', map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply LinearMap.mem_ker.mpr
    apply e.injective
    have hpoint := DFunLike.congr_fun h (e.symm y)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hpoint
    rw [e.map_zero]
    calc
      e.toLinearMap (d (e.symm y)) = D (e.toLinearMap (e.symm y)) := hpoint
      _ = D y := congrArg D (e.apply_symm_apply y)
      _ = 0 := LinearMap.mem_ker.mp hy

public theorem circleDifference_conjugacy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (k : ℕ)
    (e : IntegralSingularHomology k F ≃ₗ[ℤ] C) (monodromy : C →ₗ[ℤ] C)
    (hmonodromy : ∀ x, e (integralSingularHomologyMap k phi x) = monodromy (e x)) :
    e.toLinearMap.comp (circleMonodromyDifference phi k).toIntLinearMap =
      (monodromy - LinearMap.id).comp e.toLinearMap := by
  ext x
  simp [circleMonodromyDifference, hmonodromy]

public noncomputable def coinvariantsEquivOfConjugacy (e : E ≃ₗ[ℤ] C)
    (d : E →ₗ[ℤ] E) (D : C →ₗ[ℤ] C)
    (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (E ⧸ LinearMap.range d) ≃ₗ[ℤ] C ⧸ LinearMap.range D :=
  Submodule.Quotient.equiv _ _ e (map_range_eq_of_conjugates e d D h)

public def invariantsEquivOfConjugacy (e : E ≃ₗ[ℤ] C)
    (d : E →ₗ[ℤ] E) (D : C →ₗ[ℤ] C)
    (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    LinearMap.ker d ≃ₗ[ℤ] LinearMap.ker D :=
  e.ofSubmodules _ _ (map_ker_eq_of_conjugates e d D h)

end CircleMappingTorusHomologyBases
end SphereSixComplex
end
end
