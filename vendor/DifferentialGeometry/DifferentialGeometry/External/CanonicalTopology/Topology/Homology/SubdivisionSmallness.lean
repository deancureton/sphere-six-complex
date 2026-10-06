module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.FineAffineImages
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.UniversalSubdivisionIteration
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

/-! # Actual singular chains become small for every open cover -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Compactness of the SAME original simplex and its actual evaluation
give a small subdivision of every original singular simplex. -/
theorem exists_integralSingularSubdivisionIterate_simplex_small (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (σ : integralSingularSimplex n X) :
    ∃ k : ℕ, integralSingularSubdivisionIterate n k (integralSimplexChain n σ) ∈
      integralSingularSmallChains n U := by
  let : CompactSpace (liftedSimplexBody.{u} n) := (liftedSimplexHomeomorph.{u} n).compactSpace
  let f := singularSimplexEvaluation n σ
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := (univ : Set (liftedSimplexBody.{u} n)))
    (c := fun i => f ⁻¹' U i) isCompact_univ (fun i => (hU i).preimage f.continuous)
    (by intro x _; exact mem_iUnion.mpr (hcover (f x)))
  obtain ⟨k, hk⟩ := exists_affineSubdivisionIterate_fine n (convex_liftedSimplexBody n)
    (liftedSimplexChain_mem n) (half_pos hδ)
  refine ⟨k, ?_⟩
  rw [integralSingularSubdivisionIterate_simplex]
  exact fineAffineChain_image_small n (convex_liftedSimplexBody n) f U (half_lt_self hδ)
    (fun a => by
      obtain ⟨i, hi⟩ := hball a (mem_univ a)
      exact ⟨i, fun b hb => hi hb⟩) hk _

/-- Addition of iteration counts applies the SAME later subdivision to
the SAME preceding original chain. -/
theorem integralSingularSubdivisionIterate_add (n k l : ℕ) (c : (integralSingularChains X).X n) :
    integralSingularSubdivisionIterate n (k + l) c =
      integralSingularSubdivisionIterate n l (integralSingularSubdivisionIterate n k c) := by
  unfold integralSingularSubdivisionIterate
  rw [Nat.add_comm k l, pow_add]
  rfl

/-- Once an original chain is small, every later subdivision remains
small for the SAME family. -/
theorem integralSingularSubdivisionIterate_small_of_le (n k l : ℕ) (U : ι → Set X)
    (hkl : k ≤ l) {c : (integralSingularChains X).X n}
    (hc : integralSingularSubdivisionIterate n k c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivisionIterate n l c ∈ integralSingularSmallChains n U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [integralSingularSubdivisionIterate_add]
  exact integralSingularSubdivisionIterate_small n m U hc

/-- Every original singular chain becomes small after a finite number of
subdivisions, and stays small at every later iteration. Finite linear
generation supplies ONE count for the SAME chain and open cover. -/
theorem exists_integralSingularSubdivisionIterate_small (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (c : (integralSingularChains X).X n) :
    ∃ N : ℕ, ∀ k ≥ N, integralSingularSubdivisionIterate n k c ∈ integralSingularSmallChains n U := by
  have hc : c ∈ Submodule.span ℤ (range (integralSingularChainBasis n X)) := by
    rw [(integralSingularChainBasis n X).span_eq]
    exact Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨σ, rfl⟩ := hc
    rw [integralSingularChainBasis_apply]
    obtain ⟨N, hN⟩ := exists_integralSingularSubdivisionIterate_simplex_small n U hU hcover σ
    exact ⟨N, fun k hk => integralSingularSubdivisionIterate_small_of_le n N k U hk hN⟩
  | zero =>
    refine ⟨0, fun k _ => ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem _
  | add c d _ _ hc hd =>
    obtain ⟨N, hN⟩ := hc
    obtain ⟨M, hM⟩ := hd
    refine ⟨max N M, fun k hk => ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hN k ((le_max_left N M).trans hk))
      (hM k ((le_max_right N M).trans hk))
  | smul a c _ hc =>
    obtain ⟨N, hN⟩ := hc
    refine ⟨N, fun k hk => ?_⟩
    rw [(integralSingularSubdivisionIterate n k).map_smul]
    exact Submodule.smul_mem _ a (hN k hk)

end DifferentialGeometry.Topology
