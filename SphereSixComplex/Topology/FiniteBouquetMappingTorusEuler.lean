module

public import SphereSixComplex.Topology.FiniteExactSequenceEuler
public import SphereSixComplex.Topology.StandardFourTorusHomologicalModel
public import SphereSixComplex.Topology.WangHomologyPresentation
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Euler characteristic of finite-bouquet mapping tori

The Wang sequence computes the Euler characteristic of a finite-bouquet mapping torus directly.
The specialization to a four-torus fibre is the local calculation needed for the central and
collar pieces in Section 7.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

variable {ι F : Type}
  [Fintype ι] [TopologicalSpace F]

/-- The Wang sequence forces mapping-torus homology to vanish when its two adjacent fibre groups
vanish. -/
public theorem subsingleton_homology_succ_finiteBouquetMappingTorus_of_wang
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (φ : ι → F ≃ₜ F) (k : ℕ)
    (hsucc : Subsingleton (IntegralSingularHomology (k + 1) F))
    (hk : Subsingleton (IntegralSingularHomology k F)) :
    Subsingleton (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ)) := by
  let _ := hsucc
  let _ := hk
  let W := finiteBouquetMappingTorusWangSequenceOfCover φ k
  have key : ∀ z : IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ), z = 0 := by
    intro z
    have hz : W.boundary z = 0 := Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := (W.exact_inclusion_boundary z).mp hz
    rw [← hw, show w = 0 from Subsingleton.elim _ _, map_zero]
  exact ⟨fun x y ↦ by rw [key x, key y]⟩

/-- Finite fibre homology in adjacent degrees makes the corresponding mapping-torus homology
group finitely generated. -/
public theorem finite_homology_succ_finiteBouquetMappingTorus
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (φ : ι → F ≃ₜ F) (k : ℕ)
    [Module.Finite ℤ (IntegralSingularHomology (k + 1) F)]
    [Module.Finite ℤ (IntegralSingularHomology k F)] :
    Module.Finite ℤ
      (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ)) := by
  let P := finiteBouquetMappingTorusWangPresentation φ k
  exact integral_module_finite_of_exact
    P.inclusion.toIntLinearMap P.boundary.toIntLinearMap P.exact_inclusion_boundary

/-- The four consecutive Wang maps give the rank identity used to telescope the Euler sum. -/
public theorem finiteBouquetMappingTorus_rank_step
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (φ : ι → F ≃ₜ F) (k : ℕ)
    [Module.Finite ℤ (IntegralSingularHomology (k + 1) F)]
    [Module.Finite ℤ (IntegralSingularHomology k F)]
    [Module.Finite ℤ
      (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ))] :
    (Module.finrank ℤ (IntegralSingularHomology (k + 1) F) : ℤ) -
          Module.finrank ℤ
            (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ)) +
          Module.finrank ℤ (ι → IntegralSingularHomology k F) =
        Module.finrank ℤ
            (finiteBouquetMonodromyDifference φ (k + 1)).toIntLinearMap.range +
          Module.finrank ℤ
            (finiteBouquetMonodromyDifference φ k).toIntLinearMap.range := by
  let P := finiteBouquetMappingTorusWangPresentation φ k
  exact integral_finrank_alternating_step_of_exact
    P.highDifference.toIntLinearMap P.inclusion.toIntLinearMap
    P.boundary.toIntLinearMap P.lowDifference.toIntLinearMap
    P.exact_highDifference_inclusion P.exact_inclusion_boundary
    P.exact_boundary_lowDifference

/-- The degree-zero monodromy difference vanishes on a path-connected fibre. -/
public theorem finiteBouquetMonodromyDifference_zero_eq_zero
    [PathConnectedSpace F] (φ : ι → F ≃ₜ F) :
    finiteBouquetMonodromyDifference φ 0 = 0 := by
  ext x
  apply (pathConnectedIntegralHomologyZeroEquivInteger F).injective
  simp only [finiteBouquetMonodromyDifference, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, AddMonoidHom.zero_apply, map_sum, map_sub]
  simp only [pathConnectedIntegralHomologyZeroEquivInteger_naturality, sub_self,
    Finset.sum_const_zero, map_zero]

/-- A circle mapping torus of a path-connected fibre is path-connected. -/
public theorem pathConnectedSpace_circleMappingTorus
    [PathConnectedSpace F] (φ : F ≃ₜ F) : PathConnectedSpace (CircleMappingTorus φ) := by
  let _ : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (𝕜 := ℝ) 0 1).isPathConnected ⟨0, by simp⟩)
  let _ : PathConnectedSpace (Unit × unitInterval × F) := inferInstance
  change PathConnectedSpace
    (Quotient (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ)))
  infer_instance

/-- A finite-bouquet mapping torus with four-torus fibre has finite homology and no homology above
degree six. -/
public theorem finiteBouquetMappingTorus_integralHomologyFiniteSix
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (M : FourTorusHomologicalModel F) (φ : ι → F ≃ₜ F)
    [PathConnectedSpace (FiniteBouquetMappingTorus φ)] :
    IntegralHomologyFiniteSix (FiniteBouquetMappingTorus φ) where
  finiteHomology k := by
    cases k with
    | zero =>
        let _ : Module.Finite ℤ ℤ := inferInstance
        exact Module.Finite.equiv
          (pathConnectedIntegralHomologyZeroEquivInteger
            (FiniteBouquetMappingTorus φ)).symm.toIntLinearEquiv
    | succ k =>
        let _ : Module.Finite ℤ (IntegralSingularHomology (k + 1) F) :=
          M.finiteHomology (k + 1)
        let _ : Module.Finite ℤ (IntegralSingularHomology k F) := M.finiteHomology k
        exact finite_homology_succ_finiteBouquetMappingTorus φ k
  homologyAboveDimension k hk := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact subsingleton_homology_succ_finiteBouquetMappingTorus_of_wang φ j
      (M.subsingleton_homology_of_four_lt (j + 1) (by omega))
      (M.subsingleton_homology_of_four_lt j (by omega))

/-- Homological finiteness transported from an explicit finite-bouquet mapping-torus model. -/
public theorem finiteBouquetMappingTorus_integralHomologyFiniteSix_of_homotopyEquiv
    {X : Type} [TopologicalSpace X]
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (M : FourTorusHomologicalModel F) (φ : ι → F ≃ₜ F)
    [PathConnectedSpace (FiniteBouquetMappingTorus φ)]
    (e : X ≃ₕ FiniteBouquetMappingTorus φ) :
    IntegralHomologyFiniteSix X := by
  let hT := finiteBouquetMappingTorus_integralHomologyFiniteSix M φ
  constructor
  · intro k
    let _ : Module.Finite ℤ
        (IntegralSingularHomology k (FiniteBouquetMappingTorus φ)) := hT.finiteHomology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k e).symm.toIntLinearEquiv
  · intro k hk
    let h := hT.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
    exact ⟨fun x y ↦ eH.injective (@Subsingleton.elim _ h _ _)⟩

/-- A finite-bouquet mapping torus with four-torus fibre has Euler characteristic zero. -/
public theorem finiteBouquetMappingTorus_euler_eq_zero
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι] [PathConnectedSpace F]
    (M : FourTorusHomologicalModel F) (φ : ι → F ≃ₜ F)
    [PathConnectedSpace (FiniteBouquetMappingTorus φ)] :
    integralHomologyEulerCharacteristicSix (FiniteBouquetMappingTorus φ) = 0 := by
  let fiberFinite (k : ℕ) : Module.Finite ℤ (IntegralSingularHomology k F) :=
    M.finiteHomology k
  let fiberFree (k : ℕ) : Module.Free ℤ (IntegralSingularHomology k F) :=
    Module.Free.of_equiv' (inferInstance : Module.Free ℤ (Fin (Nat.choose 4 k) → ℤ))
      (M.homologyEquiv k).symm.toIntLinearEquiv
  let totalFiniteSucc (k : ℕ) : Module.Finite ℤ
      (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ)) :=
    finite_homology_succ_finiteBouquetMappingTorus φ k
  have h₀ := finiteBouquetMappingTorus_rank_step φ 0
  have h₁ := finiteBouquetMappingTorus_rank_step φ 1
  have h₂ := finiteBouquetMappingTorus_rank_step φ 2
  have h₃ := finiteBouquetMappingTorus_rank_step φ 3
  have h₄ := finiteBouquetMappingTorus_rank_step φ 4
  have h₅ := finiteBouquetMappingTorus_rank_step φ 5
  simp only [Module.finrank_pi_fintype, Finset.sum_const] at h₀ h₁ h₂ h₃ h₄ h₅
  rw [(M.homologyEquiv 0).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 1).toIntLinearEquiv.finrank_eq] at h₀
  rw [(M.homologyEquiv 1).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 2).toIntLinearEquiv.finrank_eq] at h₁
  rw [(M.homologyEquiv 2).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 3).toIntLinearEquiv.finrank_eq] at h₂
  rw [(M.homologyEquiv 3).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 4).toIntLinearEquiv.finrank_eq] at h₃
  rw [(M.homologyEquiv 4).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 5).toIntLinearEquiv.finrank_eq] at h₄
  rw [(M.homologyEquiv 5).toIntLinearEquiv.finrank_eq,
    (M.homologyEquiv 6).toIntLinearEquiv.finrank_eq] at h₅
  have hDifferenceZero : finiteBouquetMonodromyDifference φ 0 = 0 :=
    finiteBouquetMonodromyDifference_zero_eq_zero φ
  have hDifferenceSix : finiteBouquetMonodromyDifference φ 6 = 0 := by
    ext x
    exact @Subsingleton.elim _ (M.subsingleton_homology_six) _ _
  rw [hDifferenceZero] at h₀
  rw [hDifferenceSix] at h₅
  have hTotalZero :
      Module.finrank ℤ
        (IntegralSingularHomology 0 (FiniteBouquetMappingTorus φ)) = 1 := by
    rw [(pathConnectedIntegralHomologyZeroEquivInteger
      (FiniteBouquetMappingTorus φ)).toIntLinearEquiv.finrank_eq]
    norm_num
  unfold integralHomologyEulerCharacteristicSix
  rw [hTotalZero]
  norm_num [Nat.choose] at h₀ h₁ h₂ h₃ h₄ h₅ ⊢
  change (4 : ℤ) - Module.finrank ℤ
      (IntegralSingularHomology 1 (FiniteBouquetMappingTorus φ)) + Fintype.card ι =
    Module.finrank ℤ (finiteBouquetMonodromyDifference φ 1).toIntLinearMap.range +
      Module.finrank ℤ (0 :
        (ι → IntegralSingularHomology 0 F) →+ IntegralSingularHomology 0 F).toIntLinearMap.range
    at h₀
  change (6 : ℤ) - Module.finrank ℤ
      (IntegralSingularHomology 2 (FiniteBouquetMappingTorus φ)) + Fintype.card ι * 4 =
    Module.finrank ℤ (finiteBouquetMonodromyDifference φ 2).toIntLinearMap.range +
      Module.finrank ℤ (finiteBouquetMonodromyDifference φ 1).toIntLinearMap.range at h₁
  change (4 : ℤ) - Module.finrank ℤ
      (IntegralSingularHomology 3 (FiniteBouquetMappingTorus φ)) + Fintype.card ι * 6 =
    Module.finrank ℤ (finiteBouquetMonodromyDifference φ 3).toIntLinearMap.range +
      Module.finrank ℤ (finiteBouquetMonodromyDifference φ 2).toIntLinearMap.range at h₂
  change (1 : ℤ) - Module.finrank ℤ
      (IntegralSingularHomology 4 (FiniteBouquetMappingTorus φ)) + Fintype.card ι * 4 =
    Module.finrank ℤ (finiteBouquetMonodromyDifference φ 4).toIntLinearMap.range +
      Module.finrank ℤ (finiteBouquetMonodromyDifference φ 3).toIntLinearMap.range at h₃
  change -(Module.finrank ℤ
      (IntegralSingularHomology 5 (FiniteBouquetMappingTorus φ)) : ℤ) + Fintype.card ι =
    Module.finrank ℤ (finiteBouquetMonodromyDifference φ 5).toIntLinearMap.range +
      Module.finrank ℤ (finiteBouquetMonodromyDifference φ 4).toIntLinearMap.range at h₄
  change -(Module.finrank ℤ
      (IntegralSingularHomology 6 (FiniteBouquetMappingTorus φ)) : ℤ) =
    Module.finrank ℤ (0 :
        (ι → IntegralSingularHomology 6 F) →+ IntegralSingularHomology 6 F).toIntLinearMap.range +
      Module.finrank ℤ (finiteBouquetMonodromyDifference φ 5).toIntLinearMap.range at h₅
  have hLinearZero₀ :
      (0 : (ι → IntegralSingularHomology 0 F) →+
        IntegralSingularHomology 0 F).toIntLinearMap = 0 := rfl
  have hLinearZero₆ :
      (0 : (ι → IntegralSingularHomology 6 F) →+
        IntegralSingularHomology 6 F).toIntLinearMap = 0 := rfl
  rw [hLinearZero₀, LinearMap.range_zero, finrank_bot] at h₀
  rw [hLinearZero₆, LinearMap.range_zero, finrank_bot] at h₅
  omega

/-- Euler zero transported from an explicit finite-bouquet mapping-torus model. -/
public theorem finiteBouquetMappingTorus_euler_eq_zero_of_homotopyEquiv
    {X : Type} [TopologicalSpace X]
    [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι] [PathConnectedSpace F]
    (M : FourTorusHomologicalModel F) (φ : ι → F ≃ₜ F)
    [PathConnectedSpace (FiniteBouquetMappingTorus φ)]
    (e : X ≃ₕ FiniteBouquetMappingTorus φ) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(integralSingularHomologyEquivOfHomotopyEquiv 0 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 1 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 2 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 3 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 4 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 5 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquivOfHomotopyEquiv 6 e).toIntLinearEquiv.finrank_eq]
  exact finiteBouquetMappingTorus_euler_eq_zero M φ

/-- A geometric homotopy model by a circle mapping torus with four-torus fibre. -/
public structure FourTorusCircleMappingTorusModel
    (X : Type) [TopologicalSpace X] where
  Fiber : Type
  fiberTopology : TopologicalSpace Fiber
  fiberPathConnected : let _ := fiberTopology; PathConnectedSpace Fiber
  clutching : let _ := fiberTopology; Fiber ≃ₜ Fiber
  totalPathConnected : let _ := fiberTopology
    PathConnectedSpace (CircleMappingTorus clutching)
  fiberHomology : let _ := fiberTopology; FourTorusHomologicalModel Fiber
  totalHomotopyEquiv : let _ := fiberTopology; X ≃ₕ CircleMappingTorus clutching

namespace FourTorusCircleMappingTorusModel

variable {X : Type} [TopologicalSpace X]

/-- The explicit circle mapping-torus model supplies finite homology through dimension six. -/
public theorem integralHomologyFiniteSix (M : FourTorusCircleMappingTorusModel X) :
    IntegralHomologyFiniteSix X := by
  let _ := M.fiberTopology
  let _ := M.fiberPathConnected
  let _ := M.totalPathConnected
  exact finiteBouquetMappingTorus_integralHomologyFiniteSix_of_homotopyEquiv
    M.fiberHomology (fun _ : Unit ↦ M.clutching) M.totalHomotopyEquiv

/-- The explicit circle mapping-torus model has Euler characteristic zero. -/
public theorem euler_eq_zero (M : FourTorusCircleMappingTorusModel X) :
    integralHomologyEulerCharacteristicSix X = 0 := by
  let _ := M.fiberTopology
  let _ := M.fiberPathConnected
  let _ := M.totalPathConnected
  exact finiteBouquetMappingTorus_euler_eq_zero_of_homotopyEquiv
    M.fiberHomology (fun _ : Unit ↦ M.clutching) M.totalHomotopyEquiv

end FourTorusCircleMappingTorusModel

end SphereSixComplex

end

end
