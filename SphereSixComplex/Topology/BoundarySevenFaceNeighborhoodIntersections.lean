module

public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodDeformation

/-!
# Intersections of the boundary-seven face neighbourhoods

Every nonempty proper intersection of the affine open sets `x i < 1 / 8` retracts onto
the face on which all of the indexed coordinates vanish.  The retraction simultaneously
sets those coordinates to zero and renormalizes the complementary coordinates.
-/

@[expose] public section

noncomputable section

open ContinuousMap Set Simplicial

namespace SphereSixComplex

/-- The barycentric model of an intersection of face neighbourhoods. -/
public def standardBoundarySevenFaceNeighborhoodIntersection (s : Finset (Fin 8)) :
    Set (StandardSimplexBoundary 7) :=
  {w | ∀ i ∈ s, w.1 i < (1 : ℝ) / 8}

/-- The affine face on which every coordinate indexed by `s` vanishes. -/
public def standardBoundarySevenAffineFace (s : Finset (Fin 8)) :
    Set (StandardSimplexBoundary 7) :=
  {w | ∀ i ∈ s, w.1 i = 0}

/-- A proper subset of the eight coordinates contains at most seven coordinates. -/
public theorem boundarySeven_finset_card_le_seven
    {s : Finset (Fin 8)} (hs : s ≠ Finset.univ) : s.card ≤ 7 := by
  have hss : s ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hs
  have hc := Finset.card_lt_card hss
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- The complementary mass used in simultaneous normalization is positive. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersection_one_sub_sum_pos
    {s : Finset (Fin 8)} (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    0 < 1 - ∑ i ∈ s, w.1.1 i := by
  have hlt : (∑ i ∈ s, w.1.1 i) < ∑ _i ∈ s, (1 : ℝ) / 8 := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (w.2 i hi).le
    · obtain ⟨i, hi⟩ := hsne
      exact ⟨i, hi, w.2 i hi⟩
  have hc : s.card ≤ 7 := boundarySeven_finset_card_le_seven hs
  have hconst : (∑ _i ∈ s, (1 : ℝ) / 8) ≤ (7 : ℝ) / 8 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc' : (s.card : ℝ) ≤ 7 := by exact_mod_cast hc
    calc
      (s.card : ℝ) * ((1 : ℝ) / 8) ≤
          7 * ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right hc' (by norm_num)
      _ = (7 : ℝ) / 8 := by ring
  linarith

/-- Simultaneously set the coordinates in `s` to zero and renormalize the complement. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodIntersectionProjection
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    StandardSimplexBoundary 7 := by
  let d : ℝ := 1 - ∑ i ∈ s, w.1.1 i
  have hd : 0 < d :=
    standardBoundarySevenFaceNeighborhoodIntersection_one_sub_sum_pos hsne hs w
  let z : Fin 8 → ℝ := fun k ↦ if k ∈ s then 0 else w.1.1 k / d
  have hz_nonneg : ∀ k, 0 ≤ z k := by
    intro k
    dsimp [z]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (w.1.1.2.1 k) hd.le
  have hpartition :
      (∑ k ∈ s, w.1.1 k) + (∑ k ∈ Finset.univ.filter (· ∉ s), w.1.1 k) = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin 8 ↦ k ∈ s) (fun k ↦ w.1.1 k)
    rw [show Finset.univ.filter (fun k ↦ k ∈ s) = s by ext; simp] at hsplit
    exact hsplit.trans w.1.1.2.2
  have hother : (∑ k ∈ Finset.univ.filter (· ∉ s), w.1.1 k) = d := by
    dsimp [d]
    linarith
  have hz_sum : ∑ k, z k = 1 := by
    dsimp [z]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, ← Finset.sum_div]
    rw [hother, div_self hd.ne']
  let zs : stdSimplex ℝ (Fin 8) := ⟨z, ⟨hz_nonneg, hz_sum⟩⟩
  refine ⟨zs, ?_⟩
  obtain ⟨i, hi⟩ := hsne
  refine ⟨i, ?_⟩
  change z i = 0
  simp [z, hi]

@[simp]
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s)
    {i : Fin 8} (hi : i ∈ s) :
    (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 i = 0 := by
  change (if i ∈ s then 0 else
    w.1.1 i / (1 - ∑ j ∈ s, w.1.1 j)) = 0
  rw [if_pos hi]

@[simp]
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_not_mem
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s)
    {i : Fin 8} (hi : i ∉ s) :
    (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 i =
      w.1.1 i / (1 - ∑ j ∈ s, w.1.1 j) := by
  change (if i ∈ s then 0 else
    w.1.1 i / (1 - ∑ j ∈ s, w.1.1 j)) = _
  rw [if_neg hi]

/-- The simultaneous projection lands in the common affine face. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_mem_face
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w ∈
      standardBoundarySevenAffineFace s := by
  intro i hi
  exact standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
    s hsne hs w hi

/-- The simultaneous projection also remains in the open intersection. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_mem
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w ∈
      standardBoundarySevenFaceNeighborhoodIntersection s := by
  intro i hi
  rw [standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
    s hsne hs w hi]
  norm_num

/-- The simultaneous normalization varies continuously. -/
public theorem continuous_standardBoundarySevenFaceNeighborhoodIntersectionProjection
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    Continuous (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  by_cases hk : k ∈ s
  · simp only [if_pos hk]
    exact continuous_const
  · simp only [if_neg hk]
    have ck : Continuous (fun w : standardBoundarySevenFaceNeighborhoodIntersection s ↦
        w.1.1 k) :=
      (((continuous_apply k).comp continuous_subtype_val).comp
        continuous_subtype_val).comp continuous_subtype_val
    have csum : Continuous (fun w : standardBoundarySevenFaceNeighborhoodIntersection s ↦
        ∑ i ∈ s, w.1.1 i) := by
      apply continuous_finsetSum
      intro i _hi
      exact (((continuous_apply i).comp continuous_subtype_val).comp
        continuous_subtype_val).comp continuous_subtype_val
    exact ck.div (continuous_const.sub csum) fun w ↦
      (standardBoundarySevenFaceNeighborhoodIntersection_one_sub_sum_pos
        hsne hs w).ne'

/-- Simultaneous normalization as a map to the common affine face. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodIntersectionRetraction
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    C(standardBoundarySevenFaceNeighborhoodIntersection s,
      standardBoundarySevenAffineFace s) :=
  ⟨fun w ↦ ⟨standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w,
      standardBoundarySevenFaceNeighborhoodIntersectionProjection_mem_face s hsne hs w⟩,
    (continuous_standardBoundarySevenFaceNeighborhoodIntersectionProjection
      s hsne hs).subtype_mk _⟩

/-- Inclusion of the common affine face into the open intersection. -/
public noncomputable def standardBoundarySevenAffineFaceInclusion
    (s : Finset (Fin 8)) :
    C(standardBoundarySevenAffineFace s,
      standardBoundarySevenFaceNeighborhoodIntersection s) := by
  refine ⟨fun w ↦ ⟨w.1, ?_⟩, continuous_subtype_val.subtype_mk _⟩
  intro i hi
  rw [w.2 i hi]
  norm_num

/-- Every zero coordinate remains zero under simultaneous normalization. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_eq_zero
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) (k : Fin 8)
    (hk : w.1.1 k = 0) :
    (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 k = 0 := by
  by_cases hks : k ∈ s
  · exact standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
      s hsne hs w hks
  · rw [standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_not_mem
      s hsne hs w hks, hk, zero_div]

/-- The affine interpolation from a point to its simultaneous normalized projection. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (q : unitInterval × standardBoundarySevenFaceNeighborhoodIntersection s) :
    standardBoundarySevenFaceNeighborhoodIntersection s := by
  let t : ℝ := q.1
  let w := q.2
  let p := standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w
  let z : Fin 8 → ℝ := fun k ↦ (1 - t) * w.1.1 k + t * p.1 k
  have hz_nonneg : ∀ k, 0 ≤ z k := by
    intro k
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr q.1.2.2) (w.1.1.2.1 k))
      (mul_nonneg q.1.2.1 (p.1.2.1 k))
  have hz_sum : ∑ k, z k = 1 := by
    dsimp [z]
    have hw_sum : (∑ k : Fin 8, w.1.1 k) = 1 := w.1.1.2.2
    have hp_sum : (∑ k : Fin 8, p.1 k) = 1 := p.1.2.2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hw_sum, hp_sum]
    ring
  have hz_boundary : ∃ k, z k = 0 := by
    obtain ⟨k, hk⟩ := w.1.2
    refine ⟨k, ?_⟩
    dsimp [z]
    rw [hk, standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_eq_zero
      s hsne hs w k hk]
    ring
  let zs : stdSimplex ℝ (Fin 8) := ⟨z, ⟨hz_nonneg, hz_sum⟩⟩
  let zb : StandardSimplexBoundary 7 := ⟨zs, hz_boundary⟩
  refine ⟨zb, ?_⟩
  intro i hi
  have hpi : p.1 i = 0 :=
    standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
      s hsne hs w hi
  have hwi_nonneg : 0 ≤ w.1.1 i := w.1.1.2.1 i
  have hwi_lt : w.1.1 i < (1 : ℝ) / 8 := w.2 i hi
  have ht0 : 0 ≤ t := q.1.2.1
  have ht1 : t ≤ 1 := q.1.2.2
  change z i < (1 : ℝ) / 8
  dsimp [z]
  rw [hpi, mul_zero, add_zero]
  nlinarith

/-- The simultaneous affine deformation is continuous. -/
public theorem continuous_standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    Continuous
      (standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  change Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhoodIntersection s ↦
        (1 - (q.1 : ℝ)) * q.2.1.1 k +
          (q.1 : ℝ) *
            (standardBoundarySevenFaceNeighborhoodIntersectionProjection
              s hsne hs q.2).1 k)
  have ct : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhoodIntersection s ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have cw : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhoodIntersection s ↦ q.2.1.1 k) :=
    ((((continuous_apply k).comp continuous_subtype_val).comp
      continuous_subtype_val).comp continuous_subtype_val).comp continuous_snd
  have cp : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhoodIntersection s ↦
        (standardBoundarySevenFaceNeighborhoodIntersectionProjection
          s hsne hs q.2).1 k) :=
    (((continuous_apply k).comp continuous_subtype_val).comp
      continuous_subtype_val).comp
        ((continuous_standardBoundarySevenFaceNeighborhoodIntersectionProjection
          s hsne hs).comp continuous_snd)
  exact (continuous_const.sub ct).mul cw |>.add (ct.mul cp)

@[simp]
public theorem standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_zero
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs (0, w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (0 : ℝ)) * w.1.1 k + 0 *
      (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 k =
    w.1.1 k
  ring

@[simp]
public theorem standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_one
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenFaceNeighborhoodIntersection s) :
    standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs (1, w) =
      standardBoundarySevenAffineFaceInclusion s
        (standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs w) := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (1 : ℝ)) * w.1.1 k + 1 *
      (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 k =
        (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs w).1 k
  ring

/-- The simultaneous affine deformation, from the identity to inclusion after retraction. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodIntersectionHomotopy
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      ((standardBoundarySevenAffineFaceInclusion s).comp
        (standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs)) where
  toFun := standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
  continuous_toFun :=
    continuous_standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
  map_zero_left :=
    standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_zero s hsne hs
  map_one_left :=
    standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_one s hsne hs

/-- Normalization is the identity on the common affine face. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionProjection_face
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenAffineFace s) :
    standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs
        (standardBoundarySevenAffineFaceInclusion s w) = w.1 := by
  have hsum :
      (∑ i ∈ s, (standardBoundarySevenAffineFaceInclusion s w).1.1 i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact w.2 i hi
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  by_cases hk : k ∈ s
  · rw [standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_mem
      s hsne hs _ hk, w.2 k hk]
  · rw [standardBoundarySevenFaceNeighborhoodIntersectionProjection_apply_of_not_mem
      s hsne hs _ hk, hsum]
    change w.1.1 k / (1 - 0) = w.1.1 k
    ring

/-- The normalization map is a strict retraction of the face inclusion. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionRetraction_comp_inclusion
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    (standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs).comp
        (standardBoundarySevenAffineFaceInclusion s) =
      ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  exact standardBoundarySevenFaceNeighborhoodIntersectionProjection_face s hsne hs w

/-- The deformation fixes the affine face pointwise at every time. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_fixed
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (t : unitInterval) (w : standardBoundarySevenAffineFace s) :
    standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
        (t, standardBoundarySevenAffineFaceInclusion s w) =
      standardBoundarySevenAffineFaceInclusion s w := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  have hp := standardBoundarySevenFaceNeighborhoodIntersectionProjection_face
    s hsne hs w
  have hpk :
      (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs
        (standardBoundarySevenAffineFaceInclusion s w)).1 k = w.1.1 k := by
    rw [hp]
  change (1 - (t : ℝ)) * w.1.1 k + (t : ℝ) *
      (standardBoundarySevenFaceNeighborhoodIntersectionProjection s hsne hs
        (standardBoundarySevenAffineFaceInclusion s w)).1 k = w.1.1 k
  rw [hpk]
  ring

/-- A nonempty proper intersection is homotopy equivalent to its common affine face.  The
forward map is the literal face inclusion and the inverse is simultaneous normalization. -/
public noncomputable def standardBoundarySevenAffineFaceIntersectionHomotopyEquiv
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    standardBoundarySevenAffineFace s ≃ₕ
      standardBoundarySevenFaceNeighborhoodIntersection s where
  toFun := standardBoundarySevenAffineFaceInclusion s
  invFun := standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs
  left_inv := by
    rw [standardBoundarySevenFaceNeighborhoodIntersectionRetraction_comp_inclusion]
  right_inv := ⟨(standardBoundarySevenFaceNeighborhoodIntersectionHomotopy
    s hsne hs).symm⟩

/-! ## Contractibility of the common affine face -/

/-- A chosen coordinate outside a proper set of coordinates. -/
public noncomputable def boundarySevenCoordinateOutside
    (s : Finset (Fin 8)) (hs : s ≠ Finset.univ) : Fin 8 :=
  Classical.choose (show ∃ i, i ∉ s by
    by_contra h
    apply hs
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact h ⟨i, hi⟩)

@[simp]
public theorem boundarySevenCoordinateOutside_not_mem
    (s : Finset (Fin 8)) (hs : s ≠ Finset.univ) :
    boundarySevenCoordinateOutside s hs ∉ s :=
  Classical.choose_spec (show ∃ i, i ∉ s by
    by_contra h
    apply hs
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact h ⟨i, hi⟩)

/-- The complementary vertex used as a contraction point for the common face. -/
public noncomputable def standardBoundarySevenAffineFaceVertex
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    standardBoundarySevenAffineFace s := by
  let j := boundarySevenCoordinateOutside s hs
  let z : Fin 8 → ℝ := fun k ↦ if k = j then 1 else 0
  have hz_nonneg : ∀ k, 0 ≤ z k := by
    intro k
    dsimp [z]
    split_ifs <;> norm_num
  have hz_sum : ∑ k, z k = 1 := by
    dsimp [z]
    simp
  let zs : stdSimplex ℝ (Fin 8) := ⟨z, ⟨hz_nonneg, hz_sum⟩⟩
  have hj : j ∉ s := boundarySevenCoordinateOutside_not_mem s hs
  have hz_face : ∀ i ∈ s, zs i = 0 := by
    intro i hi
    change (if i = j then 1 else 0) = 0
    rw [if_neg]
    intro hij
    subst i
    exact hj hi
  have hz_boundary : ∃ i, zs i = 0 := by
    obtain ⟨i, hi⟩ := hsne
    exact ⟨i, hz_face i hi⟩
  exact ⟨⟨zs, hz_boundary⟩, hz_face⟩

/-- Linear contraction of the common affine face to a complementary vertex. -/
public noncomputable def standardBoundarySevenAffineFaceContractionPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (q : unitInterval × standardBoundarySevenAffineFace s) :
    standardBoundarySevenAffineFace s := by
  let t : ℝ := q.1
  let w := q.2
  let v := standardBoundarySevenAffineFaceVertex s hsne hs
  let z : Fin 8 → ℝ := fun k ↦ (1 - t) * w.1.1 k + t * v.1.1 k
  have hz_nonneg : ∀ k, 0 ≤ z k := by
    intro k
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr q.1.2.2) (w.1.1.2.1 k))
      (mul_nonneg q.1.2.1 (v.1.1.2.1 k))
  have hz_sum : ∑ k, z k = 1 := by
    dsimp [z]
    have hw_sum : (∑ k : Fin 8, w.1.1 k) = 1 := w.1.1.2.2
    have hv_sum : (∑ k : Fin 8, v.1.1 k) = 1 := v.1.1.2.2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hw_sum, hv_sum]
    ring
  have hz_face : ∀ i ∈ s, z i = 0 := by
    intro i hi
    dsimp [z]
    rw [w.2 i hi, v.2 i hi]
    ring
  have hz_boundary : ∃ i, z i = 0 := by
    obtain ⟨i, hi⟩ := hsne
    exact ⟨i, hz_face i hi⟩
  exact ⟨⟨⟨z, ⟨hz_nonneg, hz_sum⟩⟩, hz_boundary⟩, hz_face⟩

/-- The explicit contraction of the common face is continuous. -/
public theorem continuous_standardBoundarySevenAffineFaceContractionPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    Continuous (standardBoundarySevenAffineFaceContractionPoint s hsne hs) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  change Continuous (fun q : unitInterval × standardBoundarySevenAffineFace s ↦
    (1 - (q.1 : ℝ)) * q.2.1.1 k + (q.1 : ℝ) *
      (standardBoundarySevenAffineFaceVertex s hsne hs).1.1 k)
  have ct : Continuous (fun q : unitInterval × standardBoundarySevenAffineFace s ↦
      (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have cw : Continuous (fun q : unitInterval × standardBoundarySevenAffineFace s ↦
      q.2.1.1 k) :=
    ((((continuous_apply k).comp continuous_subtype_val).comp
      continuous_subtype_val).comp continuous_subtype_val).comp continuous_snd
  exact (continuous_const.sub ct).mul cw |>.add (ct.mul continuous_const)

@[simp]
public theorem standardBoundarySevenAffineFaceContractionPoint_zero
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenAffineFace s) :
    standardBoundarySevenAffineFaceContractionPoint s hsne hs (0, w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (0 : ℝ)) * w.1.1 k + 0 *
      (standardBoundarySevenAffineFaceVertex s hsne hs).1.1 k = w.1.1 k
  ring

@[simp]
public theorem standardBoundarySevenAffineFaceContractionPoint_one
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (w : standardBoundarySevenAffineFace s) :
    standardBoundarySevenAffineFaceContractionPoint s hsne hs (1, w) =
      standardBoundarySevenAffineFaceVertex s hsne hs := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (1 : ℝ)) * w.1.1 k + 1 *
      (standardBoundarySevenAffineFaceVertex s hsne hs).1.1 k = _
  ring

/-- The common affine face is contractible. -/
public theorem standardBoundarySevenAffineFace_contractibleSpace
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContractibleSpace (standardBoundarySevenAffineFace s) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨standardBoundarySevenAffineFaceVertex s hsne hs, ⟨?_⟩⟩
  exact
    { toFun := standardBoundarySevenAffineFaceContractionPoint s hsne hs
      continuous_toFun := continuous_standardBoundarySevenAffineFaceContractionPoint s hsne hs
      map_zero_left := standardBoundarySevenAffineFaceContractionPoint_zero s hsne hs
      map_one_left := standardBoundarySevenAffineFaceContractionPoint_one s hsne hs }

/-- Every nonempty proper standard affine neighbourhood intersection is contractible. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersection_contractibleSpace
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContractibleSpace (standardBoundarySevenFaceNeighborhoodIntersection s) := by
  let _ : ContractibleSpace (standardBoundarySevenAffineFace s) :=
    standardBoundarySevenAffineFace_contractibleSpace s hsne hs
  exact (standardBoundarySevenAffineFaceIntersectionHomotopyEquiv
    s hsne hs).symm.contractibleSpace

/-- Hence every nonempty proper standard intersection is path connected. -/
public theorem standardBoundarySevenFaceNeighborhoodIntersection_pathConnectedSpace
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    PathConnectedSpace (standardBoundarySevenFaceNeighborhoodIntersection s) := by
  let _ : ContractibleSpace
      (standardBoundarySevenFaceNeighborhoodIntersection s) :=
    standardBoundarySevenFaceNeighborhoodIntersection_contractibleSpace s hsne hs
  infer_instance

/-! ## Transport to the geometric realization -/

/-- The common affine face inside the geometric realization. -/
public def boundarySevenAffineFaceIntersection (s : Finset (Fin 8)) :
    Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})) :=
  {x | ∀ i ∈ s, boundarySevenRealizationToStdSimplex x i = 0}

/-- The canonical barycentric homeomorphism restricted to an intersection of face
neighbourhoods. -/
public noncomputable def boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard
    (s : Finset (Fin 8)) :
    boundarySevenFaceNeighborhoodIntersection s ≃ₜ
      standardBoundarySevenFaceNeighborhoodIntersection s :=
  boundarySevenRealizationHomeomorphStandardBoundary.subtype fun x ↦ by
    rw [mem_boundarySevenFaceNeighborhoodIntersection_iff]
    change (∀ i ∈ s, boundarySevenRealizationToStdSimplex x i < (1 : ℝ) / 8) ↔
      ∀ i ∈ s,
        (boundarySevenRealizationHomeomorphStandardBoundary x :
          stdSimplex ℝ (Fin 8)) i < (1 : ℝ) / 8
    rw [boundarySevenRealizationHomeomorphStandardBoundary_apply_val]

/-- The canonical barycentric homeomorphism restricted to the common affine face. -/
public noncomputable def boundarySevenAffineFaceIntersectionHomeomorphStandard
    (s : Finset (Fin 8)) :
    boundarySevenAffineFaceIntersection s ≃ₜ standardBoundarySevenAffineFace s :=
  boundarySevenRealizationHomeomorphStandardBoundary.subtype fun x ↦ by
    change (∀ i ∈ s, boundarySevenRealizationToStdSimplex x i = 0) ↔
      ∀ i ∈ s,
        (boundarySevenRealizationHomeomorphStandardBoundary x :
          stdSimplex ℝ (Fin 8)) i = 0
    rw [boundarySevenRealizationHomeomorphStandardBoundary_apply_val]

/-- Every nonempty proper realized intersection is homotopy equivalent to its literal common
affine face. -/
public noncomputable def boundarySevenAffineFaceIntersectionHomotopyEquiv
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    boundarySevenAffineFaceIntersection s ≃ₕ
      boundarySevenFaceNeighborhoodIntersection s :=
  (boundarySevenAffineFaceIntersectionHomeomorphStandard s).toHomotopyEquiv |>.trans
    (standardBoundarySevenAffineFaceIntersectionHomotopyEquiv s hsne hs) |>.trans
      (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm.toHomotopyEquiv

/-- The forward map of the transported equivalence is the literal inclusion of the common face
in the neighbourhood intersection. -/
public theorem boundarySevenAffineFaceIntersectionHomotopyEquiv_apply
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (x : boundarySevenAffineFaceIntersection s) :
    (boundarySevenAffineFaceIntersectionHomotopyEquiv s hsne hs x).1 = x.1 := by
  change (boundarySevenRealizationHomeomorphStandardBoundary).symm
      (boundarySevenRealizationHomeomorphStandardBoundary x.1) = x.1
  exact Homeomorph.symm_apply_apply _ _

/-- Literal inclusion of the realized common affine face into the neighbourhood intersection. -/
public noncomputable def boundarySevenAffineFaceIntersectionInclusion
    (s : Finset (Fin 8)) :
    C(boundarySevenAffineFaceIntersection s,
      boundarySevenFaceNeighborhoodIntersection s) := by
  refine ⟨fun x ↦ ⟨x.1, ?_⟩, continuous_subtype_val.subtype_mk _⟩
  rw [mem_boundarySevenFaceNeighborhoodIntersection_iff]
  intro i hi
  rw [x.2 i hi]
  norm_num

/-- The inverse of the realized face/intersection homotopy equivalence is the simultaneous
normalization retraction. -/
public noncomputable def boundarySevenFaceNeighborhoodIntersectionRetraction
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    C(boundarySevenFaceNeighborhoodIntersection s,
      boundarySevenAffineFaceIntersection s) :=
  (boundarySevenAffineFaceIntersectionHomotopyEquiv s hsne hs).invFun

/-- The forward map used in the realized equivalence is exactly the literal inclusion. -/
public theorem boundarySevenAffineFaceIntersectionHomotopyEquiv_toFun
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    (boundarySevenAffineFaceIntersectionHomotopyEquiv s hsne hs).toFun =
      boundarySevenAffineFaceIntersectionInclusion s := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact boundarySevenAffineFaceIntersectionHomotopyEquiv_apply s hsne hs x

/-- The realized simultaneous normalization is a strict left inverse to face inclusion. -/
public theorem boundarySevenFaceNeighborhoodIntersectionRetraction_comp_inclusion
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    (boundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs).comp
        (boundarySevenAffineFaceIntersectionInclusion s) =
      ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro x
  change (boundarySevenAffineFaceIntersectionHomeomorphStandard s).symm
      ((standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs)
        ((boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s)
          (boundarySevenAffineFaceIntersectionInclusion s x))) = x
  apply (boundarySevenAffineFaceIntersectionHomeomorphStandard s).injective
  rw [Homeomorph.apply_symm_apply]
  exact ContinuousMap.congr_fun
    (standardBoundarySevenFaceNeighborhoodIntersectionRetraction_comp_inclusion
      s hsne hs) ((boundarySevenAffineFaceIntersectionHomeomorphStandard s) x)

/-- The affine homotopy transported explicitly to the geometric realization. -/
public noncomputable def boundarySevenFaceNeighborhoodIntersectionHomotopyPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (q : unitInterval × boundarySevenFaceNeighborhoodIntersection s) :
    boundarySevenFaceNeighborhoodIntersection s :=
  (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm
    (standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
      (q.1, boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s q.2))

/-- The transported affine homotopy is continuous. -/
public theorem continuous_boundarySevenFaceNeighborhoodIntersectionHomotopyPoint
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    Continuous (boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs) := by
  exact (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm.continuous.comp
    ((continuous_standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint
      s hsne hs).comp
        (continuous_fst.prodMk
          ((boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).continuous.comp
            continuous_snd)))

@[simp]
public theorem boundarySevenFaceNeighborhoodIntersectionHomotopyPoint_zero
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (x : boundarySevenFaceNeighborhoodIntersection s) :
    boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs (0, x) = x := by
  change (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm
      (standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
        (0, boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s x)) = x
  rw [standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_zero,
    Homeomorph.symm_apply_apply]

@[simp]
public theorem boundarySevenFaceNeighborhoodIntersectionHomotopyPoint_one
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (x : boundarySevenFaceNeighborhoodIntersection s) :
    boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs (1, x) =
      boundarySevenAffineFaceIntersectionInclusion s
        (boundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs x) := by
  change (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm
      (standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
        (1, boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s x)) =
    boundarySevenAffineFaceIntersectionInclusion s
      (boundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs x)
  apply (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).injective
  rw [Homeomorph.apply_symm_apply]
  rw [standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_one]
  apply Subtype.ext
  have hr := Homeomorph.apply_symm_apply
    (boundarySevenAffineFaceIntersectionHomeomorphStandard s)
    ((standardBoundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs)
      (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s x))
  exact (congrArg Subtype.val hr).symm

/-- The transported homotopy from the identity to inclusion after normalization. -/
public noncomputable def boundarySevenFaceNeighborhoodIntersectionHomotopy
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      ((boundarySevenAffineFaceIntersectionInclusion s).comp
        (boundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs)) where
  toFun := boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
  continuous_toFun :=
    continuous_boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
  map_zero_left := boundarySevenFaceNeighborhoodIntersectionHomotopyPoint_zero s hsne hs
  map_one_left := boundarySevenFaceNeighborhoodIntersectionHomotopyPoint_one s hsne hs

/-- The transported deformation fixes the common affine face pointwise. -/
public theorem boundarySevenFaceNeighborhoodIntersectionHomotopyPoint_fixed
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ)
    (t : unitInterval) (x : boundarySevenAffineFaceIntersection s) :
    boundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
        (t, boundarySevenAffineFaceIntersectionInclusion s x) =
      boundarySevenAffineFaceIntersectionInclusion s x := by
  change (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).symm
      (standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
        (t, boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s
          (boundarySevenAffineFaceIntersectionInclusion s x))) =
    boundarySevenAffineFaceIntersectionInclusion s x
  apply (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).injective
  rw [Homeomorph.apply_symm_apply]
  change standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint s hsne hs
      (t, standardBoundarySevenAffineFaceInclusion s
        (boundarySevenAffineFaceIntersectionHomeomorphStandard s x)) =
    standardBoundarySevenAffineFaceInclusion s
      (boundarySevenAffineFaceIntersectionHomeomorphStandard s x)
  exact standardBoundarySevenFaceNeighborhoodIntersectionHomotopyPoint_fixed
    s hsne hs t _

/-- The reverse affine homotopy is the deformation from inclusion after simultaneous
normalization to the identity on the realized intersection. -/
public noncomputable def boundarySevenFaceNeighborhoodIntersectionDeformation
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContinuousMap.Homotopy
      ((boundarySevenAffineFaceIntersectionInclusion s).comp
        (boundarySevenFaceNeighborhoodIntersectionRetraction s hsne hs))
      (ContinuousMap.id _) :=
  (boundarySevenFaceNeighborhoodIntersectionHomotopy s hsne hs).symm

/-- Every nonempty proper intersection of the actual face-neighbourhood cover is contractible. -/
public theorem boundarySevenFaceNeighborhoodIntersection_contractibleSpace
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    ContractibleSpace (boundarySevenFaceNeighborhoodIntersection s) := by
  let _ : ContractibleSpace
      (standardBoundarySevenFaceNeighborhoodIntersection s) :=
    standardBoundarySevenFaceNeighborhoodIntersection_contractibleSpace s hsne hs
  exact (boundarySevenFaceNeighborhoodIntersectionHomeomorphStandard s).contractibleSpace

/-- Every nonempty proper intersection of the actual cover is path connected. -/
public theorem boundarySevenFaceNeighborhoodIntersection_pathConnectedSpace
    (s : Finset (Fin 8)) (hsne : s.Nonempty) (hs : s ≠ Finset.univ) :
    PathConnectedSpace (boundarySevenFaceNeighborhoodIntersection s) := by
  let _ : ContractibleSpace (boundarySevenFaceNeighborhoodIntersection s) :=
    boundarySevenFaceNeighborhoodIntersection_contractibleSpace s hsne hs
  infer_instance

end SphereSixComplex
