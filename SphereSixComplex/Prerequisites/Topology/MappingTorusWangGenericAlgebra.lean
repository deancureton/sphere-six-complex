module

public import SphereSixComplex.Prerequisites.Topology.FiniteBouquetMappingTorusEuler

/-!
# Generic algebra for circle mapping-torus Wang presentations

This module records the two presentation-independent facts used after identifying a space with a
circle mapping torus: its Euler characteristic vanishes under finite, bounded fibre homology, and
maps of the upper two stages of Wang presentations descend naturally to monodromy coinvariants.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

variable {F : Type} [TopologicalSpace F]

/-- A circle mapping torus has finitely generated integral homology through all degrees and
vanishing homology above degree six whenever the fibre has finitely generated integral homology
and vanishing homology above degree five. -/
public theorem circleMappingTorus_integralHomologyFiniteSix_of_finiteHomology
    [PathConnectedSpace F] (φ : F ≃ₜ F)
    (finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k F))
    (homologyAboveFive : ∀ k, 5 < k →
      Subsingleton (IntegralSingularHomology k F)) :
    IntegralHomologyFiniteSix (CircleMappingTorus φ) := by
  let _ : PathConnectedSpace (CircleMappingTorus φ) :=
    pathConnectedSpace_circleMappingTorus φ
  constructor
  · intro k
    cases k with
    | zero =>
        let _ : Module.Finite ℤ ℤ := inferInstance
        exact Module.Finite.equiv
          (pathConnectedIntegralHomologyZeroEquivInteger
            (CircleMappingTorus φ)).symm.toIntLinearEquiv
    | succ k =>
        let _ : Module.Finite ℤ (IntegralSingularHomology (k + 1) F) :=
          finiteHomology (k + 1)
        let _ : Module.Finite ℤ (IntegralSingularHomology k F) := finiteHomology k
        exact finite_homology_succ_finiteBouquetMappingTorus (fun _ : Unit ↦ φ) k
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact subsingleton_homology_succ_finiteBouquetMappingTorus_of_wang
      (fun _ : Unit ↦ φ) j
      (homologyAboveFive (j + 1) (by omega))
      (homologyAboveFive j (by omega))

/-- Homological finiteness transported from a circle mapping-torus model with finite, bounded
fibre homology. -/
public theorem circleMappingTorus_integralHomologyFiniteSix_of_homeomorph
    {X : Type} [TopologicalSpace X] [PathConnectedSpace F]
    (φ : F ≃ₜ F)
    (finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k F))
    (homologyAboveFive : ∀ k, 5 < k →
      Subsingleton (IntegralSingularHomology k F))
    (e : X ≃ₜ CircleMappingTorus φ) :
    IntegralHomologyFiniteSix X := by
  let hT := circleMappingTorus_integralHomologyFiniteSix_of_finiteHomology φ
    finiteHomology homologyAboveFive
  constructor
  · intro k
    let _ : Module.Finite ℤ
        (IntegralSingularHomology k (CircleMappingTorus φ)) := hT.finite_homology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquiv k e).symm.toIntLinearEquiv
  · intro k hk
    let h := hT.subsingleton_homology_of_six_lt k hk
    let eH := integralSingularHomologyEquiv k e
    exact ⟨fun x y ↦ eH.injective (@Subsingleton.elim _ h _ _)⟩

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

/-- Euler characteristic zero transported from a circle mapping-torus model with finite, bounded
fibre homology. -/
public theorem circleMappingTorus_euler_eq_zero_of_homeomorph
    {X : Type} [TopologicalSpace X] [PathConnectedSpace F]
    (φ : F ≃ₜ F)
    (finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k F))
    (homologyAboveFive : ∀ k, 5 < k →
      Subsingleton (IntegralSingularHomology k F))
    (e : X ≃ₜ CircleMappingTorus φ) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(integralSingularHomologyEquiv 0 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 1 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 2 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 3 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 4 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 5 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 6 e).toIntLinearEquiv.finrank_eq]
  exact circleMappingTorus_euler_eq_zero_of_finiteHomology φ finiteHomology
    homologyAboveFive

end SphereSixComplex
