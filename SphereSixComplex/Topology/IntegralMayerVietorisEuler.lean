module

public import SphereSixComplex.Topology.FiniteExactSequenceEuler
public import SphereSixComplex.Topology.IntegralHomologyEuler
public import SphereSixComplex.Topology.MayerVietoris

/-!
# Integral Mayer--Vietoris Euler additivity

This file contains the dimensionally sound form of Euler additivity needed by Section 7.  If the
two open pieces and their intersection have no homology above degree six, their union can acquire
degree-seven homology.  We therefore propagate finiteness through degree seven and use the
degree-seven truncated Euler characteristic.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex

private noncomputable abbrev mvDifferenceLinearMap
    {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :=
  (IntegralMayerVietoris.differenceMap U V k).toIntLinearMap

private noncomputable abbrev mvSumLinearMap
    {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :=
  (IntegralMayerVietoris.sumMap U V k).toIntLinearMap

private theorem linearMap_eq_zero_of_subsingleton_domain
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [Subsingleton M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) : f = 0 := by
  apply LinearMap.ext
  intro x
  rw [show x = 0 from Subsingleton.elim x 0]
  simp only [map_zero]

/-- Exact Mayer--Vietoris data and the degree-zero endpoint propagate finite generation to the
union and show that no homology above degree seven can be created. -/
public theorem integralHomologyFiniteSeven_union_of_mayerVietoris
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUFinite : IntegralHomologyFiniteSeven U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X))
    (hExact : IntegralMayerVietoris.ExactSequence U V)
    (hZero : Function.Surjective (IntegralMayerVietoris.sumMap U V 0)) :
    IntegralHomologyFiniteSeven (U ∪ V : Set X) := by
  obtain ⟨boundary, hExactAt⟩ := hExact
  constructor
  · intro k
    by_cases hk : k = 0
    · subst k
      let _ : Module.Finite ℤ (IntegralSingularHomology 0 U) :=
        hUFinite.finiteHomology 0
      let _ : Module.Finite ℤ (IntegralSingularHomology 0 V) :=
        hVFinite.finiteHomology 0
      exact Module.Finite.of_surjective (mvSumLinearMap U V 0) hZero
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      let _ : Module.Finite ℤ (IntegralSingularHomology (j + 1) U) :=
        hUFinite.finiteHomology (j + 1)
      let _ : Module.Finite ℤ (IntegralSingularHomology (j + 1) V) :=
        hVFinite.finiteHomology (j + 1)
      let _ : Module.Finite ℤ (IntegralSingularHomology j (U ∩ V : Set X)) :=
        hInterFinite.finiteHomology j
      apply integral_module_finite_of_exact (mvSumLinearMap U V (j + 1))
        (boundary j).toIntLinearMap
      simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt j).1
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    let _ : Subsingleton (IntegralSingularHomology (j + 1) U) :=
      hUFinite.homologyAboveDimension (j + 1) (by omega)
    let _ : Subsingleton (IntegralSingularHomology (j + 1) V) :=
      hVFinite.homologyAboveDimension (j + 1) (by omega)
    let _ : Subsingleton (IntegralSingularHomology j (U ∩ V : Set X)) :=
      hInterFinite.homologyAboveDimension j (by omega)
    have hSumZero : mvSumLinearMap U V (j + 1) = 0 :=
      linearMap_eq_zero_of_subsingleton_domain (mvSumLinearMap U V (j + 1))
    have hExactLinear : Function.Exact (mvSumLinearMap U V (j + 1))
        (boundary j).toIntLinearMap := by
      simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt j).1
    have hBoundaryInjective : Function.Injective (boundary j).toIntLinearMap :=
      (LinearMap.injective_iff_eq_zero_of_exact hExactLinear).2 hSumZero
    exact ⟨fun x y ↦ hBoundaryInjective (Subsingleton.elim _ _)⟩

/-- The sound Mayer--Vietoris Euler formula.  The union is allowed to have degree-seven homology;
the three other spaces vanish above degree six. -/
public theorem integralMayerVietorisEulerAdditivitySeven
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUFinite : IntegralHomologyFiniteSeven U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X))
    (hExact : IntegralMayerVietoris.ExactSequence U V)
    (hZero : Function.Surjective (IntegralMayerVietoris.sumMap U V 0)) :
    IntegralHomologyFiniteSeven (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSeven (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSeven U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) := by
  obtain ⟨boundary, hExactAt⟩ := hExact
  have hUnionFinite : IntegralHomologyFiniteSeven (U ∪ V : Set X) :=
    integralHomologyFiniteSeven_union_of_mayerVietoris U V hUFinite hVFinite
      hInterFinite ⟨boundary, hExactAt⟩ hZero
  refine ⟨hUnionFinite, ?_⟩
  let _ (k : ℕ) : Module.Finite ℤ (IntegralSingularHomology k U) :=
    hUFinite.finiteHomology k
  let _ (k : ℕ) : Module.Finite ℤ (IntegralSingularHomology k V) :=
    hVFinite.finiteHomology k
  let _ (k : ℕ) : Module.Finite ℤ
      (IntegralSingularHomology k (U ∩ V : Set X)) :=
    hInterFinite.finiteHomology k
  let _ (k : ℕ) : Module.Finite ℤ
      (IntegralSingularHomology k (U ∪ V : Set X)) :=
    hUnionFinite.finiteHomology k
  have hStep (k : ℕ) :
      (Module.finrank ℤ (IntegralSingularHomology (k + 1) (U ∪ V : Set X)) : ℤ) -
          Module.finrank ℤ (IntegralSingularHomology k (U ∩ V : Set X)) +
          Module.finrank ℤ
            (IntegralSingularHomology k U × IntegralSingularHomology k V) =
        Module.finrank ℤ (mvSumLinearMap U V (k + 1)).range +
          Module.finrank ℤ (mvSumLinearMap U V k).range := by
    apply integral_finrank_alternating_step_of_exact
      (mvSumLinearMap U V (k + 1)) (boundary k).toIntLinearMap
      (mvDifferenceLinearMap U V k) (mvSumLinearMap U V k)
    · simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt k).1
    · simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt k).2.1
    · simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt k).2.2
  have hStep₀ := hStep 0
  have hStep₁ := hStep 1
  have hStep₂ := hStep 2
  have hStep₃ := hStep 3
  have hStep₄ := hStep 4
  have hStep₅ := hStep 5
  have hStep₆ := hStep 6
  rw [integral_finrank_prod] at hStep₀ hStep₁ hStep₂ hStep₃ hStep₄ hStep₅ hStep₆
  have hRangeZero : Module.finrank ℤ (mvSumLinearMap U V 0).range =
      Module.finrank ℤ (IntegralSingularHomology 0 (U ∪ V : Set X)) :=
    integral_finrank_range_eq_of_surjective (mvSumLinearMap U V 0) hZero
  have hRangeSeven : Module.finrank ℤ (mvSumLinearMap U V 7).range =
      Module.finrank ℤ (IntegralSingularHomology 7 U) := by
    let _ : Subsingleton (IntegralSingularHomology 7 V) :=
      hVFinite.homologyAboveDimension 7 (by omega)
    let _ : Subsingleton (IntegralSingularHomology 7 (U ∩ V : Set X)) :=
      hInterFinite.homologyAboveDimension 7 (by omega)
    have hDifferenceZero : mvDifferenceLinearMap U V 7 = 0 :=
      linearMap_eq_zero_of_subsingleton_domain (mvDifferenceLinearMap U V 7)
    have hExactLinear : Function.Exact (mvDifferenceLinearMap U V 7)
        (mvSumLinearMap U V 7) := by
      simpa only [AddMonoidHom.coe_toIntLinearMap] using (hExactAt 7).2.2
    have hSumInjective : Function.Injective (mvSumLinearMap U V 7) :=
      (LinearMap.injective_iff_eq_zero_of_exact hExactLinear).2 hDifferenceZero
    rw [integral_finrank_range_eq_of_injective _ hSumInjective,
      integral_finrank_prod]
    simp only [Module.finrank_zero_of_subsingleton, Nat.add_zero]
  have hRangeZeroInt :
      (Module.finrank ℤ (mvSumLinearMap U V 0).range : ℤ) =
        (Module.finrank ℤ (IntegralSingularHomology 0 (U ∪ V : Set X)) : ℤ) := by
    exact_mod_cast hRangeZero
  have hRangeSevenInt :
      (Module.finrank ℤ (mvSumLinearMap U V 7).range : ℤ) =
        (Module.finrank ℤ (IntegralSingularHomology 7 U) : ℤ) := by
    exact_mod_cast hRangeSeven
  simp only [Nat.cast_add] at hStep₀ hStep₁ hStep₂ hStep₃ hStep₄ hStep₅ hStep₆
  unfold integralHomologyEulerCharacteristicSeven
  unfold integralHomologyEulerCharacteristicSix
  linear_combination -hStep₀ + hStep₁ - hStep₂ + hStep₃ - hStep₄ + hStep₅ -
    hStep₆ - hRangeZeroInt - hRangeSevenInt

/-- When both pieces and their intersection vanish above degree six, the asymmetric theorem starts
with the ordinary six-dimensional Euler characteristic on the left piece. -/
public theorem integralMayerVietorisEulerAdditivitySeven_of_finiteSix
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hUFinite : IntegralHomologyFiniteSix U)
    (hVFinite : IntegralHomologyFiniteSix V)
    (hInterFinite : IntegralHomologyFiniteSix (U ∩ V : Set X))
    (hExact : IntegralMayerVietoris.ExactSequence U V)
    (hZero : Function.Surjective (IntegralMayerVietoris.sumMap U V 0)) :
    IntegralHomologyFiniteSeven (U ∪ V : Set X) ∧
      integralHomologyEulerCharacteristicSeven (U ∪ V : Set X) =
        integralHomologyEulerCharacteristicSix U +
        integralHomologyEulerCharacteristicSix V -
        integralHomologyEulerCharacteristicSix (U ∩ V : Set X) := by
  have hSevenZero : Module.finrank ℤ (IntegralSingularHomology 7 U) = 0 := by
    let _ := hUFinite.homologyAboveDimension 7 (by omega)
    exact Module.finrank_zero_of_subsingleton
  have hEulerU : integralHomologyEulerCharacteristicSeven U =
      integralHomologyEulerCharacteristicSix U := by
    unfold integralHomologyEulerCharacteristicSeven
    rw [hSevenZero]
    omega
  obtain ⟨hUnionFinite, hAdd⟩ :=
    integralMayerVietorisEulerAdditivitySeven U V
      (IntegralHomologyFiniteSeven.ofFiniteSix hUFinite)
      hVFinite hInterFinite hExact hZero
  exact ⟨hUnionFinite, by simpa only [hEulerU] using hAdd⟩

end SphereSixComplex
