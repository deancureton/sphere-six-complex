module

public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Data.Finset.Sort

/-!
# Positive-support compression for a standard simplex

Every point of a finite real standard simplex is the image of a point with strictly positive
coordinates on a uniquely ordered list of its positive coordinates.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex

/-- The finite set of coordinates at which a standard-simplex point is strictly positive. -/
public def standardSimplexPositiveSupport {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i ↦ 0 < w i

@[simp]
public theorem mem_standardSimplexPositiveSupport_iff {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    i ∈ standardSimplexPositiveSupport w ↔ 0 < w i := by
  simp [standardSimplexPositiveSupport]

/-- A standard-simplex point has at least one strictly positive coordinate. -/
public theorem standardSimplexPositiveSupport_nonempty {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    (standardSimplexPositiveSupport w).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hzero : ∀ i, w i = 0 := by
    intro i
    have hnpos : ¬ 0 < w i := by
      intro hi
      have : i ∈ standardSimplexPositiveSupport w :=
        (mem_standardSimplexPositiveSupport_iff w i).2 hi
      rw [h] at this
      simp at this
    exact le_antisymm (le_of_not_gt hnpos) (w.2.1 i)
  have hsum : (∑ i, w i) = 0 := Finset.sum_eq_zero fun i _ ↦ hzero i
  have hone : (1 : ℝ) = 0 := w.2.2.symm.trans hsum
  norm_num at hone

/-- The dimension of the simplex spanned by the positive support. -/
public def standardSimplexPositiveSupportDimension {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) : ℕ :=
  (standardSimplexPositiveSupport w).card - 1

/-- The positive support has one more vertex than its dimension. -/
public theorem standardSimplexPositiveSupport_card {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    (standardSimplexPositiveSupport w).card =
      standardSimplexPositiveSupportDimension w + 1 := by
  unfold standardSimplexPositiveSupportDimension
  exact (Nat.sub_add_cancel (standardSimplexPositiveSupport_nonempty w).card_pos).symm

/-- The increasing enumeration of the positive coordinates. -/
public noncomputable def standardSimplexPositiveSupportIndex {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    Fin (standardSimplexPositiveSupportDimension w + 1) ↪o Fin (n + 1) :=
  (standardSimplexPositiveSupport w).orderEmbOfFin
    (standardSimplexPositiveSupport_card w)

/-- The ordered positive-support enumeration is strictly increasing. -/
public theorem standardSimplexPositiveSupportIndex_strictMono {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    StrictMono (standardSimplexPositiveSupportIndex w) :=
  (standardSimplexPositiveSupportIndex w).strictMono

/-- The ordered positive-support enumeration is injective. -/
public theorem standardSimplexPositiveSupportIndex_injective {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    Function.Injective (standardSimplexPositiveSupportIndex w) :=
  (standardSimplexPositiveSupportIndex w).injective

@[simp]
public theorem standardSimplexPositiveSupportIndex_mem {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1)))
    (j : Fin (standardSimplexPositiveSupportDimension w + 1)) :
    0 < w (standardSimplexPositiveSupportIndex w j) := by
  rw [← mem_standardSimplexPositiveSupport_iff]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- The increasing enumeration has exactly the positive coordinates as its range. -/
public theorem range_standardSimplexPositiveSupportIndex {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    Set.range (standardSimplexPositiveSupportIndex w) = {i | 0 < w i} := by
  rw [standardSimplexPositiveSupportIndex, Finset.range_orderEmbOfFin]
  ext i
  simp

/-- A coordinate is positive exactly when it occurs in the ordered support enumeration. -/
public theorem exists_standardSimplexPositiveSupportIndex_iff {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (∃ j, standardSimplexPositiveSupportIndex w j = i) ↔ 0 < w i := by
  change i ∈ Set.range (standardSimplexPositiveSupportIndex w) ↔ 0 < w i
  rw [range_standardSimplexPositiveSupportIndex]
  rfl

/-- The simplex point obtained by retaining precisely the positive coordinates. -/
public noncomputable def standardSimplexPositiveSupportCompressed {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex ℝ (Fin (standardSimplexPositiveSupportDimension w + 1)) := by
  let s := standardSimplexPositiveSupport w
  let hcard := standardSimplexPositiveSupport_card w
  let e : Fin (standardSimplexPositiveSupportDimension w + 1) ≃o s :=
    s.orderIsoOfFin hcard
  refine ⟨fun j ↦ w (e j), fun j ↦ w.2.1 _, ?_⟩
  calc
    (∑ j, w (e j)) = ∑ i : s, w i := by
      change (∑ j, w (e.toEquiv j)) = ∑ i : s, w i
      exact Equiv.sum_comp e.toEquiv (fun i : s ↦ w i)
    _ = ∑ i ∈ s, w i := Finset.sum_coe_sort s (fun i ↦ w i)
    _ = ∑ i, w i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hnpos : ¬ 0 < w i := by
        simpa [s, standardSimplexPositiveSupport] using hi
      exact le_antisymm (le_of_not_gt hnpos) (w.2.1 i)
    _ = 1 := w.2.2

@[simp]
public theorem standardSimplexPositiveSupportCompressed_apply {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1)))
    (j : Fin (standardSimplexPositiveSupportDimension w + 1)) :
    standardSimplexPositiveSupportCompressed w j =
      w (standardSimplexPositiveSupportIndex w j) := by
  rfl

/-- Every coordinate of the compressed simplex point is strictly positive. -/
public theorem standardSimplexPositiveSupportCompressed_pos {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1)))
    (j : Fin (standardSimplexPositiveSupportDimension w + 1)) :
    0 < standardSimplexPositiveSupportCompressed w j := by
  rw [standardSimplexPositiveSupportCompressed_apply]
  exact standardSimplexPositiveSupportIndex_mem w j

/-- Expanding the compressed point along its ordered positive support recovers the original
standard-simplex point. -/
public theorem standardSimplex_map_positiveSupportCompressed {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map (standardSimplexPositiveSupportIndex w)
        (standardSimplexPositiveSupportCompressed w) = w := by
  apply stdSimplex.ext
  funext i
  classical
  by_cases hi : 0 < w i
  · have hirange : i ∈ Set.range (standardSimplexPositiveSupportIndex w) := by
      rw [range_standardSimplexPositiveSupportIndex]
      exact hi
    obtain ⟨j, hj⟩ := hirange
    subst i
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
      (standardSimplexPositiveSupportIndex w).injective.eq_iff]
    rw [Finset.sum_eq_single j]
    · exact standardSimplexPositiveSupportCompressed_apply w j
    · simp
    · simp
  · have hwi : w i = 0 := le_antisymm (le_of_not_gt hi) (w.2.1 i)
    simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_eq_zero]
    · exact hwi.symm
    · intro j hj
      have hne : standardSimplexPositiveSupportIndex w j ≠ i := by
        intro h
        apply hi
        simpa [h] using standardSimplexPositiveSupportIndex_mem w j
      simp only [Finset.mem_filter] at hj
      exact (hne hj.2).elim

/-- Fully packaged positive-support compression data. -/
public structure StandardSimplexPositiveSupportData {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) where
  dimension : ℕ
  index : Fin (dimension + 1) ↪o Fin (n + 1)
  index_range : Set.range index = {i | 0 < w i}
  compressed : stdSimplex ℝ (Fin (dimension + 1))
  compressed_pos : ∀ j, 0 < compressed j
  map_compressed : stdSimplex.map index compressed = w

/-- Canonical packaged positive-support compression of a standard-simplex point. -/
public noncomputable def standardSimplexPositiveSupportData {n : ℕ}
    (w : stdSimplex ℝ (Fin (n + 1))) :
    StandardSimplexPositiveSupportData w where
  dimension := standardSimplexPositiveSupportDimension w
  index := standardSimplexPositiveSupportIndex w
  index_range := range_standardSimplexPositiveSupportIndex w
  compressed := standardSimplexPositiveSupportCompressed w
  compressed_pos := standardSimplexPositiveSupportCompressed_pos w
  map_compressed := standardSimplex_map_positiveSupportCompressed w

end SphereSixComplex
