module

public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivision
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Lebesgue numbers for pullbacks along singular simplices

For an open cover of a space, every singular simplex pulls the cover back to an open cover of its
compact standard-simplex domain.  This file packages the resulting Lebesgue number independently
of the barycentric mesh estimate.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex

/-- The pullback of an open cover along one singular simplex has a positive Lebesgue number. -/
public theorem singularSimplex_openCover_lebesgueNumber
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ δ > 0, ∀ w : stdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball w δ ⊆ (X.toSSetObjEquiv _ x) ⁻¹' U i := by
  let f := X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) x
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) isCompact_univ
    (fun i ↦ (hUopen i).preimage f.continuous) (by
      intro w _
      rw [Set.mem_iUnion]
      have hw : f w ∈ ⋃ i, U i := by rw [hUcover]; exact Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
      exact ⟨i, hi⟩)
  exact ⟨δ, hδ, fun w ↦ hLeb w (Set.mem_univ w)⟩


end SphereSixComplex
