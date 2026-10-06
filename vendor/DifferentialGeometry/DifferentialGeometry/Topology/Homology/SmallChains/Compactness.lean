module

public import DifferentialGeometry.Topology.Homology.SmallChains
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import DifferentialGeometry.Topology.Simplex.Coordinates

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

theorem exists_small_precomp_radius {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (op ⦋m⦌)).symm
          ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp τ)) ∈
            (smallSingularSimplices X U).obj (op ⦋m⦌) := by
  let f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) := X.toSSetObjEquiv (op ⦋n⦌) σ
  have hUopen : ∀ i, IsOpen (f ⁻¹' U i) := fun i ↦ (hopen i).preimage f.continuous
  have hUcover : Set.univ ⊆ ⋃ i, f ⁻¹' U i := by
    intro x _
    exact Set.mem_iUnion.mpr (hcover (f x))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (Convexity.StdSimplex ℝ (Fin (n + 1)))))
    hUopen hUcover
  refine ⟨δ, hδ, ?_⟩
  intro m τ hτ
  let a : Convexity.StdSimplex ℝ (Fin (m + 1)) :=
    Convexity.StdSimplex.single 0
  obtain ⟨i, hi⟩ := hball (τ a) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact hi (hτ b a)

theorem exists_uniform_small_precomp_radius {n : ℕ}
    (F : Finset (TopCat.toSSet.obj X _⦋n⦌)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ F, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (op ⦋m⦌)).symm
          ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp τ)) ∈
            (smallSingularSimplices X U).obj (op ⦋m⦌) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert σ F hσ hF =>
    obtain ⟨δ, hδ, hδF⟩ := hF
    obtain ⟨ε, hε, hεσ⟩ := exists_small_precomp_radius X U hopen hcover σ
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro ρ hρ m τ hτ
    obtain rfl | hρ := Finset.mem_insert.mp hρ
    · exact hεσ m τ (fun a b ↦ (hτ a b).trans_le (min_le_right _ _))
    · exact hδF ρ hρ m τ (fun a b ↦ (hτ a b).trans_le (min_le_left _ _))

end DifferentialGeometry.Homology
