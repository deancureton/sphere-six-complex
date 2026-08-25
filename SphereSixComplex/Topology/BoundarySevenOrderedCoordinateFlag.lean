module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealization
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Ordered-coordinate flags in the boundary of the seven-simplex

Sorting the eight barycentric coordinates of a boundary point gives seven nonempty proper
suffixes.  Read in reverse order, these suffixes form a strict flag.  Consecutive coordinate
differences, multiplied by the size of the corresponding suffix, are its simplex weights.
-/

@[expose] public section

noncomputable section

open CategoryTheory Finset PartialOrder Simplicial

namespace SphereSixComplex

/-- A permutation which puts the barycentric coordinates in increasing order. -/
public noncomputable def boundarySevenCoordinateSort
    (w : StandardSimplexBoundary 7) : Equiv.Perm (Fin 8) :=
  Tuple.sort (fun i ↦ (w.1 : Fin 8 → ℝ) i)

public theorem boundarySevenCoordinateSort_monotone
    (w : StandardSimplexBoundary 7) :
    Monotone (fun i ↦ w.1 (boundarySevenCoordinateSort w i)) :=
  Tuple.monotone_sort _

/-- The positions bounding the `j`th suffix.  They are respectively `7-j` and `6-j`. -/
public def boundarySevenOrderedFacePosition (j : Fin 7) : Fin 8 :=
  Fin.rev j.castSucc

public def boundarySevenOrderedFacePreviousPosition (j : Fin 7) : Fin 8 :=
  Fin.rev j.succ

public theorem boundarySevenOrderedFacePreviousPosition_lt (j : Fin 7) :
    boundarySevenOrderedFacePreviousPosition j < boundarySevenOrderedFacePosition j := by
  simp [boundarySevenOrderedFacePreviousPosition, boundarySevenOrderedFacePosition]

/-- The suffix of sorted vertices beginning at position `7-j`. -/
public noncomputable def boundarySevenOrderedFaceFinset
    (w : StandardSimplexBoundary 7) (j : Fin 7) : Finset (Fin 8) :=
  (Finset.Ici (boundarySevenOrderedFacePosition j)).map
    (boundarySevenCoordinateSort w).toEmbedding

public theorem boundarySevenOrderedFaceFinset_nonempty
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    (boundarySevenOrderedFaceFinset w j).Nonempty := by
  refine ⟨boundarySevenCoordinateSort w (boundarySevenOrderedFacePosition j), ?_⟩
  simp [boundarySevenOrderedFaceFinset]

public theorem boundarySevenOrderedFaceFinset_ne_univ
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    boundarySevenOrderedFaceFinset w j ≠ Finset.univ := by
  intro h
  have hz : boundarySevenCoordinateSort w 0 ∈
      boundarySevenOrderedFaceFinset w j := by rw [h]; simp
  simp only [boundarySevenOrderedFaceFinset, Finset.mem_map] at hz
  obtain ⟨k, hk, heq⟩ := hz
  have hk0 : k = 0 := (boundarySevenCoordinateSort w).injective heq
  subst k
  have hpos : 0 < boundarySevenOrderedFacePosition j := by
    apply Fin.pos_iff_ne_zero.mpr
    intro hzero
    have hv := congrArg Fin.val hzero
    simp [boundarySevenOrderedFacePosition, Fin.rev] at hv
    omega
  have hk' := Finset.mem_Ici.mp hk
  exact (not_le_of_gt hpos) hk'

/-- The `j`th suffix as a nonempty proper face. -/
public noncomputable def boundarySevenOrderedFace
    (w : StandardSimplexBoundary 7) (j : Fin 7) : BoundarySevenProperFace :=
  ⟨boundarySevenOrderedFaceFinset w j,
    boundarySevenOrderedFaceFinset_nonempty w j,
    boundarySevenOrderedFaceFinset_ne_univ w j⟩

@[simp]
public theorem boundarySevenOrderedFace_card
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    (boundarySevenOrderedFace w j).1.card = j.val + 1 := by
  simp only [boundarySevenOrderedFace, boundarySevenOrderedFaceFinset,
    Finset.card_map, Fin.card_Ici, boundarySevenOrderedFacePosition]
  rw [Fin.val_rev, Fin.val_castSucc]
  omega

@[simp]
public theorem boundarySevenCoordinateSort_mem_orderedFace_iff
    (w : StandardSimplexBoundary 7) (j : Fin 7) (i : Fin 8) :
    boundarySevenCoordinateSort w i ∈ (boundarySevenOrderedFace w j).1 ↔
      boundarySevenOrderedFacePosition j ≤ i := by
  simp [boundarySevenOrderedFace, boundarySevenOrderedFaceFinset]

/-- The ordered suffix faces are strictly nested. -/
public theorem boundarySevenOrderedFace_strictMono
    (w : StandardSimplexBoundary 7) :
    StrictMono (boundarySevenOrderedFace w) := by
  intro j k hjk
  change boundarySevenOrderedFaceFinset w j < boundarySevenOrderedFaceFinset w k
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro i hi
    simp only [boundarySevenOrderedFaceFinset,
      Finset.mem_map] at hi ⊢
    obtain ⟨p, hp, rfl⟩ := hi
    refine ⟨p, ?_, rfl⟩
    apply Finset.mem_Ici.mpr
    have hpos : boundarySevenOrderedFacePosition k ≤
        boundarySevenOrderedFacePosition j := by
      simp only [boundarySevenOrderedFacePosition, Fin.rev_le_rev]
      exact Fin.castSucc_le_castSucc_iff.mpr hjk.le
    exact hpos.trans (Finset.mem_Ici.mp hp)
  · intro heq
    let p := boundarySevenOrderedFacePosition k
    have hmemk : boundarySevenCoordinateSort w p ∈
        boundarySevenOrderedFaceFinset w k := by
      simp [boundarySevenOrderedFaceFinset, p]
    have hmemj : boundarySevenCoordinateSort w p ∈
        boundarySevenOrderedFaceFinset w j := by rwa [heq]
    simp only [boundarySevenOrderedFaceFinset, Finset.mem_map] at hmemj
    obtain ⟨q, hq, heqp⟩ := hmemj
    have hqp : q = p := (boundarySevenCoordinateSort w).injective heqp
    subst q
    have hrev : boundarySevenOrderedFacePosition k <
        boundarySevenOrderedFacePosition j := by
      simp only [boundarySevenOrderedFacePosition, Fin.rev_lt_rev]
      exact Fin.castSucc_lt_castSucc_iff.mpr hjk
    exact (not_le_of_gt hrev) (Finset.mem_Ici.mp hq)

/-- The seven strictly nested suffixes, packaged as a six-simplex of the proper-face nerve. -/
public noncomputable def boundarySevenOrderedFlag
    (w : StandardSimplexBoundary 7) :
    ComposableArrows BoundarySevenProperFace 6 where
  obj := boundarySevenOrderedFace w
  map f := homOfLE ((boundarySevenOrderedFace_strictMono w).monotone (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
public theorem boundarySevenOrderedFlag_obj
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    (boundarySevenOrderedFlag w).obj j = boundarySevenOrderedFace w j :=
  rfl

public theorem boundarySevenOrderedFlag_strictMono
    (w : StandardSimplexBoundary 7) :
    StrictMono (boundarySevenOrderedFlag w).obj :=
  boundarySevenOrderedFace_strictMono w

/-- Consecutive-difference weight of the `j`th suffix face. -/
public noncomputable def boundarySevenOrderedWeight
    (w : StandardSimplexBoundary 7) (j : Fin 7) : ℝ :=
  (j.val + 1 : ℝ) *
    (w.1 (boundarySevenCoordinateSort w (boundarySevenOrderedFacePosition j)) -
      w.1 (boundarySevenCoordinateSort w
        (boundarySevenOrderedFacePreviousPosition j)))

public theorem boundarySevenOrderedWeight_nonneg
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    0 ≤ boundarySevenOrderedWeight w j := by
  apply mul_nonneg (by positivity)
  exact sub_nonneg.mpr (boundarySevenCoordinateSort_monotone w
    (boundarySevenOrderedFacePreviousPosition_lt j).le)

/-- The least sorted coordinate vanishes because the point lies in the simplex boundary. -/
public theorem boundarySevenCoordinateSort_zero
    (w : StandardSimplexBoundary 7) :
    w.1 (boundarySevenCoordinateSort w 0) = 0 := by
  obtain ⟨i, hi⟩ := w.2
  let p : Fin 8 := (boundarySevenCoordinateSort w).symm i
  have hle := boundarySevenCoordinateSort_monotone w (Fin.zero_le p)
  have hp : boundarySevenCoordinateSort w p = i := by
    simp [p]
  change w.1 (boundarySevenCoordinateSort w 0) ≤
      w.1 (boundarySevenCoordinateSort w p) at hle
  rw [hp, hi] at hle
  exact le_antisymm hle (w.1.2.1 _)

/-- The seven consecutive-difference coefficients have total mass one. -/
public theorem boundarySevenOrderedWeight_sum
    (w : StandardSimplexBoundary 7) :
    ∑ j : Fin 7, boundarySevenOrderedWeight w j = 1 := by
  have hsum : ∑ i : Fin 8, w.1 (boundarySevenCoordinateSort w i) = 1 := by
    calc
      _ = ∑ i : Fin 8, w.1 i :=
        Equiv.sum_comp (boundarySevenCoordinateSort w) (fun i ↦ w.1 i)
      _ = 1 := w.1.2.2
  have hzero := boundarySevenCoordinateSort_zero w
  simp only [boundarySevenOrderedWeight, boundarySevenOrderedFacePosition,
    boundarySevenOrderedFacePreviousPosition, Fin.sum_univ_succ,
    Fin.val_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    zero_add, Fin.rev, Fin.castSucc, Fin.succ] at hsum ⊢
  norm_num at hsum ⊢
  linarith

/-- The ordered-coordinate differences as a point of the coefficient simplex. -/
public noncomputable def boundarySevenOrderedWeights
    (w : StandardSimplexBoundary 7) : stdSimplex ℝ (Fin 7) :=
  ⟨boundarySevenOrderedWeight w,
    boundarySevenOrderedWeight_nonneg w,
    boundarySevenOrderedWeight_sum w⟩

@[simp]
public theorem boundarySevenOrderedWeights_apply
    (w : StandardSimplexBoundary 7) (j : Fin 7) :
    boundarySevenOrderedWeights w j = boundarySevenOrderedWeight w j :=
  rfl

/-- Coordinatewise layer-cake reconstruction, stated at a sorted vertex. -/
public theorem boundarySevenOrderedAffineCombination_apply_sorted
    (w : StandardSimplexBoundary 7) (i : Fin 8) :
    stdSimplexAffineCombination
        (fun j ↦ boundarySevenProperFaceBarycenter
          (boundarySevenOrderedFace w j))
        (boundarySevenOrderedWeights w)
        (boundarySevenCoordinateSort w i) =
      w.1 (boundarySevenCoordinateSort w i) := by
  rw [stdSimplexAffineCombination_apply]
  simp only [boundarySevenOrderedWeights_apply,
    boundarySevenProperFaceBarycenter_apply,
    boundarySevenCoordinateSort_mem_orderedFace_iff,
    boundarySevenOrderedFace_card]
  have hzero := boundarySevenCoordinateSort_zero w
  fin_cases i <;>
    simp [boundarySevenOrderedWeight,
      boundarySevenOrderedFacePosition,
      boundarySevenOrderedFacePreviousPosition, Fin.sum_univ_succ,
      Fin.rev, Fin.castSucc, Fin.succ, hzero] <;>
    ring

/-- Every boundary point is the affine combination of the barycenters in its explicit strict
ordered-coordinate flag. -/
public theorem boundarySevenOrderedAffineCombination_eq
    (w : StandardSimplexBoundary 7) :
    stdSimplexAffineCombination
        (fun j ↦ boundarySevenProperFaceBarycenter
          (boundarySevenOrderedFace w j))
        (boundarySevenOrderedWeights w) = w.1 := by
  ext x
  let i : Fin 8 := (boundarySevenCoordinateSort w).symm x
  have hxi : boundarySevenCoordinateSort w i = x := by simp [i]
  rw [← hxi]
  exact boundarySevenOrderedAffineCombination_apply_sorted w i

/-- Endpoint form: the affine realization of the explicit strict flag at its explicit simplex
weights is the original boundary point. -/
public theorem boundarySevenProperFaceAffineFlagMap_orderedFlag
    (w : StandardSimplexBoundary 7) :
    boundarySevenProperFaceAffineFlagMap 6
        (boundarySevenOrderedFlag w) (boundarySevenOrderedWeights w) = w := by
  apply Subtype.ext
  exact boundarySevenOrderedAffineCombination_eq w

end SphereSixComplex
