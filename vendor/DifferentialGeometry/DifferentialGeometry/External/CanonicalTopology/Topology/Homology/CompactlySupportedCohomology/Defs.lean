module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Topology.Sets.Compacts

@[expose] public section
noncomputable section

open TopologicalSpace Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def compactSupportCohomologyMap (n : ℕ) (K L : Compacts X) (h : K ≤ L) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ]
      integralRelativeCohomology n (L : Set X)ᶜ :=
  integralRelativeCohomologyMap n (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr h)

instance Defs.compactSupportCohomologyDirectedSystem (n : ℕ) :
    DirectedSystem (fun K : Compacts X => integralRelativeCohomology n (K : Set X)ᶜ)
      (fun K L h => compactSupportCohomologyMap n K L h) where
  map_self := by
    intro K α
    exact LinearMap.congr_fun (integralRelativeCohomologyMap_id n (K : Set X)ᶜ) α
  map_map := by
    intro N L K hKL hLN α
    exact (LinearMap.congr_fun (integralRelativeCohomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) (N : Set X)ᶜ (L : Set X)ᶜ from
        compl_subset_compl.mpr hLN)
      (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
        compl_subset_compl.mpr hKL)) α).symm

def integralCompactlySupportedCohomology (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ := by
  classical
  exact (ModuleCat.directLimitCocone
    (fun K : Compacts X => integralRelativeCohomology n (K : Set X)ᶜ)
    (compactSupportCohomologyMap n)).pt

def integralRelativeToCompactlySupportedCohomology (n : ℕ) (K : Compacts X) :
    integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ]
      integralCompactlySupportedCohomology n X := by
  classical
  exact ((ModuleCat.directLimitCocone
    (fun L : Compacts X => integralRelativeCohomology n (L : Set X)ᶜ)
    (compactSupportCohomologyMap n)).ι.app K).hom

theorem integralRelativeToCompactlySupportedCohomology_map
    (n : ℕ) (K L : Compacts X) (h : K ≤ L)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralRelativeToCompactlySupportedCohomology n L
        (integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) α) =
      integralRelativeToCompactlySupportedCohomology n K α := by
  classical
  exact Module.DirectLimit.of_f (R := ℤ) (ι := Compacts X)
    (f := compactSupportCohomologyMap n) (hij := h)

theorem integralCompactlySupportedCohomology_exists_representative
    (n : ℕ) (α : integralCompactlySupportedCohomology n X) :
    ∃ (K : Compacts X) (β : integralRelativeCohomology n (K : Set X)ᶜ),
      integralRelativeToCompactlySupportedCohomology n K β = α := by
  classical
  change ∃ (K : Compacts X) (β : integralRelativeCohomology n (K : Set X)ᶜ),
    Module.DirectLimit.of ℤ (Compacts X)
      (fun L : Compacts X => integralRelativeCohomology n (L : Set X)ᶜ)
      (compactSupportCohomologyMap n) K β = α
  exact Module.DirectLimit.exists_of α

theorem integralRelativeToCompactlySupportedCohomology_eq_zero_iff
    (n : ℕ) (K : Compacts X) (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralRelativeToCompactlySupportedCohomology n K α = 0 ↔
      ∃ (L : Compacts X) (h : K ≤ L),
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) α = 0 := by
  classical
  constructor
  · exact Module.DirectLimit.of.zero_exact (R := ℤ) (ι := Compacts X)
      (f := compactSupportCohomologyMap n)
  · rintro ⟨L, h, hα⟩
    rw [← integralRelativeToCompactlySupportedCohomology_map n K L h α, hα, map_zero]

theorem integralCompactlySupportedCohomology_hom_ext
    (n : ℕ) {P : Type*} [AddCommMonoid P] [Module ℤ P]
    {f g : integralCompactlySupportedCohomology n X →ₗ[ℤ] P}
    (h : ∀ (K : Compacts X) (α : integralRelativeCohomology n (K : Set X)ᶜ),
      f (integralRelativeToCompactlySupportedCohomology n K α) =
        g (integralRelativeToCompactlySupportedCohomology n K α)) : f = g := by
  ext α
  obtain ⟨K, β, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
  exact h K β

def integralCompactlySupportedCohomologyDesc (n : ℕ) {P : Type u}
    [AddCommGroup P] [Module ℤ P]
    (g : ∀ K : Compacts X, integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ] P)
    (hg : ∀ (K L : Compacts X) (h : K ≤ L)
      (α : integralRelativeCohomology n (K : Set X)ᶜ),
      g L (integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) α) = g K α) :
    integralCompactlySupportedCohomology n X →ₗ[ℤ] P := by
  classical
  let s : CategoryTheory.Limits.Cocone (ModuleCat.directLimitDiagram
      (fun K : Compacts X => integralRelativeCohomology n (K : Set X)ᶜ)
      (compactSupportCohomologyMap n)) :=
    { pt := ModuleCat.of ℤ P
      ι :=
        { app := fun K => ModuleCat.ofHom (g K)
          naturality := by
            intro K L h
            ext α
            exact hg K L h.le α } }
  exact ((ModuleCat.directLimitIsColimit
    (fun K : Compacts X => integralRelativeCohomology n (K : Set X)ᶜ)
    (compactSupportCohomologyMap n)).desc s).hom

theorem integralCompactlySupportedCohomologyDesc_representative (n : ℕ) {P : Type u}
    [AddCommGroup P] [Module ℤ P]
    (g : ∀ K : Compacts X, integralRelativeCohomology n (K : Set X)ᶜ →ₗ[ℤ] P)
    (hg : ∀ (K L : Compacts X) (h : K ≤ L)
      (α : integralRelativeCohomology n (K : Set X)ᶜ),
      g L (integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) α) = g K α)
    (K : Compacts X) (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedCohomologyDesc n g hg (integralRelativeToCompactlySupportedCohomology n K α) =
      g K α := by
  classical
  exact Module.DirectLimit.lift_of g hg α

def integralCompactlySupportedToSingularCohomology (n : ℕ) (X : Type u)
    [TopologicalSpace X] :
    integralCompactlySupportedCohomology n X →ₗ[ℤ] integralSingularCohomology n X := by
  classical
  refine integralCompactlySupportedCohomologyDesc n
    (fun K => integralRelativeToAbsoluteCohomology n (K : Set X)ᶜ) ?_
  intro K L h α
  have hn := LinearMap.congr_fun (integralRelativeToAbsoluteCohomology_natural n
    (ContinuousMap.id X)
    (show MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr h)) α
  simpa only [LinearMap.comp_apply, integralSingularCohomologyMap_id,
    LinearMap.id_apply] using hn

theorem integralCompactlySupportedToSingularCohomology_representative
    (n : ℕ) (K : Compacts X) (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedToSingularCohomology n X
        (integralRelativeToCompactlySupportedCohomology n K α) =
      integralRelativeToAbsoluteCohomology n (K : Set X)ᶜ α := by
  classical
  exact integralCompactlySupportedCohomologyDesc_representative n _ _ K α

private theorem integralRelativeToAbsoluteCohomology_bijective_of_isEmpty
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) [IsEmpty A] :
    Function.Bijective (integralRelativeToAbsoluteCohomology n A) := by
  rw [Set.eq_empty_of_isEmpty A,
    ← integralRelativeToAbsoluteCohomologyEmptyEquiv_toLinearMap n X]
  exact (integralRelativeToAbsoluteCohomologyEmptyEquiv n X).bijective

theorem integralCompactlySupportedToSingularCohomology_bijective
    [CompactSpace X] (n : ℕ) :
    Function.Bijective (integralCompactlySupportedToSingularCohomology n X) := by
  let K : Compacts X := ⊤
  let _ : IsEmpty ↥((K : Set X)ᶜ) :=
    ⟨fun x => x.property (show x.val ∈ (K : Set X) from mem_univ _)⟩
  have hbij := integralRelativeToAbsoluteCohomology_bijective_of_isEmpty n (K : Set X)ᶜ
  have htop (α : integralCompactlySupportedCohomology n X) :
      ∃ β : integralRelativeCohomology n (K : Set X)ᶜ,
        integralRelativeToCompactlySupportedCohomology n K β = α := by
    obtain ⟨L, β, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
    refine ⟨integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show MapsTo (ContinuousMap.id X) (K : Set X)ᶜ (L : Set X)ᶜ from
        compl_subset_compl.mpr (show L ≤ K from le_top)) β, ?_⟩
    exact integralRelativeToCompactlySupportedCohomology_map n L K le_top β
  constructor
  · intro α β h
    obtain ⟨α, rfl⟩ := htop α
    obtain ⟨β, rfl⟩ := htop β
    rw [integralCompactlySupportedToSingularCohomology_representative,
      integralCompactlySupportedToSingularCohomology_representative] at h
    exact congrArg (integralRelativeToCompactlySupportedCohomology n K) (hbij.injective h)
  · intro α
    obtain ⟨β, hβ⟩ := hbij.surjective α
    exact ⟨integralRelativeToCompactlySupportedCohomology n K β,
      (integralCompactlySupportedToSingularCohomology_representative n K β).trans hβ⟩

end DifferentialGeometry.Topology

end
