module

public import SphereSixComplex.Topology.FiniteBouquetMappingTorusEuler

/-!
# Generic algebra for circle mapping-torus Wang presentations

This module records the two presentation-independent facts used after identifying a space with a
circle mapping torus: its Euler characteristic vanishes under finite, bounded fibre homology, and
maps of the upper two stages of Wang presentations descend naturally to monodromy coinvariants.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  {HighRelations' High' Total' LowRelations' Low' : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]
  [AddCommGroup HighRelations'] [AddCommGroup High'] [AddCommGroup Total']
  [AddCommGroup LowRelations'] [AddCommGroup Low']

/-- The part of a morphism of Wang presentations controlling the inclusion of upper-degree
coinvariants into total-space homology. -/
public structure CoinvariantsToTotalHom
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (Q : WangHomologyPresentation HighRelations' High' Total' LowRelations' Low') where
  highRelations : HighRelations →ₗ[ℤ] HighRelations'
  high : High →ₗ[ℤ] High'
  total : Total →ₗ[ℤ] Total'
  highDifference_naturality :
    high.comp P.highDifference.toIntLinearMap =
      Q.highDifference.toIntLinearMap.comp highRelations
  inclusion_naturality :
    total.comp P.inclusion.toIntLinearMap = Q.inclusion.toIntLinearMap.comp high

namespace CoinvariantsToTotalHom

variable
  {P : WangHomologyPresentation HighRelations High Total LowRelations Low}
  {Q : WangHomologyPresentation HighRelations' High' Total' LowRelations' Low'}
  (N : CoinvariantsToTotalHom P Q)

/-- A morphism of the upper Wang square induces the corresponding map on monodromy
coinvariants. -/
public def coinvariantsMap : P.Coinvariants →ₗ[ℤ] Q.Coinvariants :=
  (LinearMap.range P.highDifference.toIntLinearMap).liftQ
    ((LinearMap.range Q.highDifference.toIntLinearMap).mkQ.comp N.high) fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      change (LinearMap.range Q.highDifference.toIntLinearMap).mkQ
        (N.high (P.highDifference y)) = 0
      have h := DFunLike.congr_fun N.highDifference_naturality y
      change N.high (P.highDifference y) = Q.highDifference (N.highRelations y) at h
      rw [h]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨N.highRelations y, rfl⟩

@[simp]
public theorem coinvariantsMap_mk (x : High) :
    N.coinvariantsMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (N.high x) := by
  rfl

/-- The map induced on coinvariants commutes with the canonical injections into the total terms. -/
public theorem coinvariantsToTotal_naturality (x : P.Coinvariants) :
    Q.coinvariantsToTotal (N.coinvariantsMap x) =
      N.total (P.coinvariantsToTotal x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range P.highDifference.toIntLinearMap) x
  change Q.inclusion (N.high x) = N.total (P.inclusion x)
  have h := DFunLike.congr_fun N.inclusion_naturality x
  change N.total (P.inclusion x) = Q.inclusion (N.high x) at h
  exact h.symm

end CoinvariantsToTotalHom

end WangHomologyPresentation

variable {F : Type} [TopologicalSpace F]

/-- A circle mapping torus has Euler characteristic zero whenever the fibre has finitely
generated integral homology and vanishing homology above degree five. -/
public theorem circleMappingTorus_euler_eq_zero_of_finiteHomology
    [PathConnectedSpace F] (φ : F ≃ₜ F)
    (finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k F))
    (homologyAboveFive : ∀ k, 5 < k →
      Subsingleton (IntegralSingularHomology k F)) :
    integralHomologyEulerCharacteristicSix (CircleMappingTorus φ) = 0 := by
  let _ : PathConnectedSpace (CircleMappingTorus φ) :=
    pathConnectedSpace_circleMappingTorus φ
  let fiberFinite (k : ℕ) : Module.Finite ℤ (IntegralSingularHomology k F) :=
    finiteHomology k
  let totalFiniteSucc (k : ℕ) : Module.Finite ℤ
      (IntegralSingularHomology (k + 1) (CircleMappingTorus φ)) :=
    finite_homology_succ_finiteBouquetMappingTorus (fun _ : Unit ↦ φ) k
  have h₀ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 0
  have h₁ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 1
  have h₂ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 2
  have h₃ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 3
  have h₄ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 4
  have h₅ := finiteBouquetMappingTorus_rank_step (fun _ : Unit ↦ φ) 5
  have finrankUnit (k : ℕ) :
      Module.finrank ℤ (Unit → IntegralSingularHomology k F) =
        Module.finrank ℤ (IntegralSingularHomology k F) :=
    (LinearEquiv.piUnique ℤ (fun _ : Unit ↦
      IntegralSingularHomology k F)).finrank_eq
  rw [finrankUnit 0] at h₀
  rw [finrankUnit 1] at h₁
  rw [finrankUnit 2] at h₂
  rw [finrankUnit 3] at h₃
  rw [finrankUnit 4] at h₄
  rw [finrankUnit 5] at h₅
  have hDifferenceZero :
      finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 0 = 0 :=
    finiteBouquetMonodromyDifference_zero_eq_zero (fun _ : Unit ↦ φ)
  have hDifferenceSix :
      finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 6 = 0 := by
    ext x
    exact @Subsingleton.elim _ (homologyAboveFive 6 (by omega)) _ _
  rw [hDifferenceZero] at h₀
  rw [hDifferenceSix] at h₅
  change (Module.finrank ℤ (IntegralSingularHomology 1 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 1 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 0 F) =
    Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 1).toIntLinearMap.range +
      Module.finrank ℤ
        (0 : (Unit → IntegralSingularHomology 0 F) →+
          IntegralSingularHomology 0 F).toIntLinearMap.range at h₀
  change (Module.finrank ℤ (IntegralSingularHomology 2 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 2 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 1 F) =
    Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 2).toIntLinearMap.range +
      Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 1).toIntLinearMap.range at h₁
  change (Module.finrank ℤ (IntegralSingularHomology 3 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 3 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 2 F) =
    Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 3).toIntLinearMap.range +
      Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 2).toIntLinearMap.range at h₂
  change (Module.finrank ℤ (IntegralSingularHomology 4 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 4 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 3 F) =
    Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 4).toIntLinearMap.range +
      Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 3).toIntLinearMap.range at h₃
  change (Module.finrank ℤ (IntegralSingularHomology 5 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 5 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 4 F) =
    Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 5).toIntLinearMap.range +
      Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 4).toIntLinearMap.range at h₄
  change (Module.finrank ℤ (IntegralSingularHomology 6 F) : ℤ) -
      Module.finrank ℤ (IntegralSingularHomology 6 (CircleMappingTorus φ)) +
      Module.finrank ℤ (IntegralSingularHomology 5 F) =
    Module.finrank ℤ
        (0 : (Unit → IntegralSingularHomology 6 F) →+
          IntegralSingularHomology 6 F).toIntLinearMap.range +
      Module.finrank ℤ
        (finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) 5).toIntLinearMap.range at h₅
  have hFiberZero : Module.finrank ℤ (IntegralSingularHomology 0 F) = 1 := by
    rw [(pathConnectedIntegralHomologyZeroEquivInteger F).toIntLinearEquiv.finrank_eq]
    norm_num
  have hFiberSix : Module.finrank ℤ (IntegralSingularHomology 6 F) = 0 := by
    let _ := homologyAboveFive 6 (by omega)
    exact Module.finrank_zero_of_subsingleton
  have hTotalZero :
      Module.finrank ℤ (IntegralSingularHomology 0 (CircleMappingTorus φ)) = 1 := by
    rw [(pathConnectedIntegralHomologyZeroEquivInteger
      (CircleMappingTorus φ)).toIntLinearEquiv.finrank_eq]
    norm_num
  unfold integralHomologyEulerCharacteristicSix
  rw [hTotalZero]
  have hLinearZero₀ :
      (0 : (Unit → IntegralSingularHomology 0 F) →+
        IntegralSingularHomology 0 F).toIntLinearMap = 0 := rfl
  have hLinearZero₆ :
      (0 : (Unit → IntegralSingularHomology 6 F) →+
        IntegralSingularHomology 6 F).toIntLinearMap = 0 := rfl
  rw [hLinearZero₀, LinearMap.range_zero, finrank_bot] at h₀
  rw [hLinearZero₆, LinearMap.range_zero, finrank_bot] at h₅
  rw [hFiberZero] at h₀
  rw [hFiberSix] at h₅
  omega

end SphereSixComplex
