module

public import SphereSixComplex.Topology.PaperCuspSpecializationAlgebra
public import Mathlib.Algebra.Module.Projective

/-!
# Homology bases for a circle mapping torus

This module splits the Wang short exact sequence when its invariant term is projective, then
specializes the construction to the cusp monodromy matrices in degrees zero, one, and two.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- A Wang presentation splits as its coinvariants times its invariants whenever the latter are
projective. -/
public noncomputable def totalLinearEquivCoinvariantsProdInvariants
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
public noncomputable def totalLinearEquivOfEndCoordinates
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    {CoinvariantCoordinates InvariantCoordinates : Type*}
    [AddCommGroup CoinvariantCoordinates] [AddCommGroup InvariantCoordinates]
    [Module.Projective ℤ InvariantCoordinates]
    (coinvariants : P.Coinvariants ≃ₗ[ℤ] CoinvariantCoordinates)
    (invariants : P.Invariants ≃ₗ[ℤ] InvariantCoordinates) :
    Total ≃ₗ[ℤ] CoinvariantCoordinates × InvariantCoordinates := by
  letI : Module.Projective ℤ P.Invariants :=
    Module.Projective.of_equiv' invariants.symm
  exact P.totalLinearEquivCoinvariantsProdInvariants.trans
    (coinvariants.prodCongr invariants)

end WangHomologyPresentation

namespace CircleMappingTorusHomologyBases

open LatticeData
open LatticeWangAlgebra
open Topology.PaperCuspSpecializationAlgebra

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

/-- Fiber coordinates through degree two that identify monodromy with the cusp matrices. -/
public structure CuspMonodromyCoordinates
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) where
  degreeZero : IntegralSingularHomology 0 F ≃+ ℤ
  degreeOne : IntegralSingularHomology 1 F ≃+ Lattice
  degreeTwo : IntegralSingularHomology 2 F ≃+ ExteriorTwoLattice
  degreeZero_monodromy : ∀ x,
    degreeZero (integralSingularHomologyMap 0 phi x) = degreeZero x
  degreeOne_monodromy : ∀ x,
    degreeOne (integralSingularHomologyMap 1 phi x) = M₀ *ᵥ degreeOne x
  degreeTwo_monodromy : ∀ x,
    degreeTwo (integralSingularHomologyMap 2 phi x) =
      mZeroExteriorTwoMatrix *ᵥ degreeTwo x

public def zeroKernelEquivInt : LinearMap.ker (0 : ℤ →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ where
  toFun x := x.1
  invFun x := ⟨x, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

public def finTwoProdIntLinearEquiv : ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.2]
  invFun x := (![x 0, x 1], x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' n x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

public def finFourProdFinTwoLinearEquiv :
    ((Fin 4 → ℤ) × (Fin 2 → ℤ)) ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.1 2, x.1 3, x.2 0, x.2 1]
  invFun x := (![x 0, x 1, x 2, x 3], ![x 4, x 5])
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' n x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

namespace CuspMonodromyCoordinates

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}

public theorem degreeZeroDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeZero.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 0).toIntLinearMap =
      (0 : ℤ →ₗ[ℤ] ℤ).comp B.degreeZero.toIntLinearEquiv.toLinearMap := by
  simpa using circleDifference_conjugacy phi 0 B.degreeZero.toIntLinearEquiv LinearMap.id
    (fun x ↦ by simpa using B.degreeZero_monodromy x)

public theorem degreeOneDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeOne.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 1).toIntLinearMap =
      mZeroDifference.comp B.degreeOne.toIntLinearEquiv.toLinearMap := by
  exact circleDifference_conjugacy phi 1 B.degreeOne.toIntLinearEquiv M₀.mulVecLin
    B.degreeOne_monodromy

public theorem degreeTwoDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeTwo.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 2).toIntLinearMap =
      mZeroExteriorTwoDifference.comp B.degreeTwo.toIntLinearEquiv.toLinearMap := by
  exact circleDifference_conjugacy phi 2 B.degreeTwo.toIntLinearEquiv
    mZeroExteriorTwoMatrix.mulVecLin B.degreeTwo_monodromy

/-- The first homology of the cusp circle mapping torus is free of rank three. -/
public noncomputable def circleMappingTorusHOneLinearEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 3 → ℤ) := by
  let P := circleMappingTorusHOnePresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroCoinvariantsEquivIntSquared
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
      (circleMonodromyDifference phi 0).toIntLinearMap 0
      B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt
  exact (P.totalLinearEquivOfEndCoordinates coinvariants invariants).trans
    finTwoProdIntLinearEquiv

/-- The second homology of the cusp circle mapping torus is free of rank six. -/
public noncomputable def circleMappingTorusHTwoLinearEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 6 → ℤ) := by
  let P := circleMappingTorusHTwoPresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeTwo.toIntLinearEquiv
      (circleMonodromyDifference phi 2).toIntLinearMap mZeroExteriorTwoDifference
      B.degreeTwoDifference_conjugacy).trans mZeroExteriorTwoCoinvariantsEquivIntFourth
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  exact (P.totalLinearEquivOfEndCoordinates coinvariants invariants).trans
    finFourProdFinTwoLinearEquiv

/-- Additive coordinates on first homology, for direct use with singular homology APIs. -/
public noncomputable def circleMappingTorusHOneAddEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃+ (Fin 3 → ℤ) :=
  B.circleMappingTorusHOneLinearEquiv.toAddEquiv

/-- Additive coordinates on second homology, for direct use with singular homology APIs. -/
public noncomputable def circleMappingTorusHTwoAddEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃+ (Fin 6 → ℤ) :=
  B.circleMappingTorusHTwoLinearEquiv.toAddEquiv

end CuspMonodromyCoordinates

end CircleMappingTorusHomologyBases

end SphereSixComplex
