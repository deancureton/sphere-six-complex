module

public import SphereSixComplex.Topology.BoundarySevenStrictFlagAffineInjective

/-!
# Overlap invariants for strict proper-face flags

A positive coefficient at a face in a strict flag produces a genuine gap in the eight affine
coordinates.  Consequently that face can be recovered from the represented boundary point as
a superlevel set.  This is the main algebraic uniqueness input for comparing two flag charts.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Finset PartialOrder Set Simplicial

namespace SphereSixComplex

/-- Every level of a strict flag has a vertex which first occurs at that level. -/
public theorem boundarySevenStrictFlag_exists_levelVertex'
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (hF : StrictMono F.obj) (j : Fin (k + 1)) :
    ∃ a : Fin 8, ∀ l : Fin (k + 1),
      (a ∈ (F.obj l).1 ↔ j ≤ l) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · obtain ⟨a, ha⟩ := (F.obj (0 : Fin (k + 1))).2.1
    refine ⟨a, fun l ↦ ⟨fun _ ↦ Fin.zero_le l, fun _ ↦ ?_⟩⟩
    exact leOfHom (F.map (homOfLE (Fin.zero_le l))) ha
  · have hlt : F.obj i.castSucc < F.obj i.succ := hF i.castSucc_lt_succ
    have hsub : (F.obj i.castSucc).1 ⊆ (F.obj i.succ).1 := hlt.le
    have hex : ∃ a, a ∈ (F.obj i.succ).1 ∧ a ∉ (F.obj i.castSucc).1 := by
      by_contra h
      push Not at h
      apply hlt.ne
      apply Subtype.ext
      exact Finset.Subset.antisymm hsub (fun a ha ↦ h a ha)
    obtain ⟨a, haNow, haBefore⟩ := hex
    refine ⟨a, fun l ↦ ⟨?_, ?_⟩⟩
    · intro hal
      by_contra hle
      have hli : l ≤ i.castSucc := by
        change ¬ (i.val + 1 ≤ l.val) at hle
        change l.val ≤ i.val
        omega
      exact haBefore (leOfHom (F.map (homOfLE hli)) hal)
    · intro hil
      exact leOfHom (F.map (homOfLE hil)) haNow

/-- The contribution at and above a level of a flag. -/
public noncomputable def boundarySevenStrictFlagTail
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1)) : ℝ :=
  ∑ l : Fin (k + 1), if j ≤ l then
    w l * (((F.obj l).1.card : ℝ)⁻¹) else 0

/-- Coordinate expansion of an affine flag point. -/
public theorem boundarySevenProperFaceAffineFlagMap_apply_eq_sum
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (a : Fin 8) :
    (boundarySevenProperFaceAffineFlagMap k F w).1 a =
      ∑ l : Fin (k + 1),
        w l * (if a ∈ (F.obj l).1 then
          (((F.obj l).1.card : ℝ)⁻¹) else 0) := by
  change (∑ l, w l * boundarySevenProperFaceBarycenter (F.obj l) a) = _
  simp only [boundarySevenProperFaceBarycenter_apply]

/-- A vertex which first occurs at level `j` has coordinate equal to the tail at `j`. -/
public theorem boundarySevenStrictFlag_levelVertex_coordinate
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1))
    (a : Fin 8) (ha : ∀ l : Fin (k + 1), (a ∈ (F.obj l).1 ↔ j ≤ l)) :
    (boundarySevenProperFaceAffineFlagMap k F w).1 a =
      boundarySevenStrictFlagTail k F w j := by
  rw [boundarySevenProperFaceAffineFlagMap_apply_eq_sum,
    boundarySevenStrictFlagTail]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hjl : j ≤ l
  · simp [hjl, (ha l).mpr hjl]
  · have hal : a ∉ (F.obj l).1 := fun hal ↦ hjl ((ha l).mp hal)
    simp [hjl, hal]

/-- Membership in a flag is monotone with the level. -/
public theorem boundarySevenStrictFlag_obj_mono
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    {i j : Fin (k + 1)} (hij : i ≤ j) :
    (F.obj i).1 ⊆ (F.obj j).1 :=
  leOfHom (F.map (homOfLE hij))

/-- If `a` already belongs at level `j`, its coordinate is at least the `j`-tail. -/
public theorem boundarySevenStrictFlagTail_le_coordinate_of_mem
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1))
    (a : Fin 8) (ha : a ∈ (F.obj j).1) :
    boundarySevenStrictFlagTail k F w j ≤
      (boundarySevenProperFaceAffineFlagMap k F w).1 a := by
  rw [boundarySevenStrictFlagTail,
    boundarySevenProperFaceAffineFlagMap_apply_eq_sum]
  apply Finset.sum_le_sum
  intro l hl
  by_cases hjl : j ≤ l
  · have hal : a ∈ (F.obj l).1 :=
      boundarySevenStrictFlag_obj_mono k F hjl ha
    simp [hjl, hal]
  · simp only [if_neg hjl]
    exact mul_nonneg (w.2.1 l) (by positivity)

/-- Outside the level-`j` face the coordinate is strictly below the `j`-tail whenever its
coefficient is positive. -/
public theorem boundarySevenStrictFlag_coordinate_lt_tail_of_not_mem
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1))
    (a : Fin 8) (ha : a ∉ (F.obj j).1) (hw : 0 < w j) :
    (boundarySevenProperFaceAffineFlagMap k F w).1 a <
      boundarySevenStrictFlagTail k F w j := by
  rw [boundarySevenStrictFlagTail,
    boundarySevenProperFaceAffineFlagMap_apply_eq_sum]
  apply Finset.sum_lt_sum
  · intro l hl
    by_cases hal : a ∈ (F.obj l).1
    · have hjl : j ≤ l := by
        by_contra h
        have hlj : l ≤ j := le_of_not_ge h
        exact ha (boundarySevenStrictFlag_obj_mono k F hlj hal)
      simp [hal, hjl]
    · by_cases hjl : j ≤ l
      · simp only [if_neg hal, if_pos hjl, mul_zero]
        exact mul_nonneg (w.2.1 l) (by positivity)
      · simp [hal, hjl]
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [if_neg ha, if_pos le_rfl]
    simp only [mul_zero]
    have hcard : 0 < (((F.obj j).1.card : ℝ)⁻¹) := by
      apply inv_pos.mpr
      exact_mod_cast (F.obj j).2.1.card_pos
    exact mul_pos hw hcard

/-- A positive-weight face is recovered intrinsically as a superlevel set of the represented
point. -/
public theorem boundarySevenStrictFlag_face_eq_superlevel
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1))
    (hw : 0 < w j) :
    (F.obj j).1 = Finset.univ.filter (fun a : Fin 8 ↦
      boundarySevenStrictFlagTail k F w j ≤
        (boundarySevenProperFaceAffineFlagMap k F w).1 a) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact boundarySevenStrictFlagTail_le_coordinate_of_mem k F w j a
  · intro hcoord
    by_contra ha
    exact (not_lt_of_ge hcoord)
      (boundarySevenStrictFlag_coordinate_lt_tail_of_not_mem k F w j a ha hw)

/-- A positive coefficient makes its tail strictly positive. -/
public theorem boundarySevenStrictFlagTail_pos
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) (j : Fin (k + 1))
    (hw : 0 < w j) :
    0 < boundarySevenStrictFlagTail k F w j := by
  rw [boundarySevenStrictFlagTail]
  apply (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) ?_).mpr
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [if_pos le_rfl]
    apply mul_pos hw
    apply inv_pos.mpr
    exact_mod_cast (F.obj j).2.1.card_pos
  · intro l hl
    split_ifs
    · exact mul_nonneg (w.2.1 l) (by positivity)
    · exact le_rfl

/-- A positive face in one strict presentation occurs as a positive face in any other equal
strict presentation.  Zero coefficients in the second flag are skipped by taking the first
positive level at or above the first occurrence of a suitable level vertex. -/
public theorem boundarySevenStrictFlag_overlap_exists_positive_face_eq
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (hF : StrictMono F.obj) (_hG : StrictMono G.obj)
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v)
    (j : Fin (k + 1)) (hj : 0 < w j) :
    ∃ l : Fin (m + 1), 0 < v l ∧ F.obj j = G.obj l := by
  obtain ⟨a, haF⟩ := boundarySevenStrictFlag_exists_levelVertex' k F hF j
  have haFcoord := boundarySevenStrictFlag_levelVertex_coordinate k F w j a haF
  have hcoord :
      (boundarySevenProperFaceAffineFlagMap m G v).1 a =
        boundarySevenStrictFlagTail k F w j := by
    rw [← haFcoord]
    exact congrArg (fun z : StandardSimplexBoundary 7 ↦ z.1 a) h.symm
  have hcoordpos : 0 < (boundarySevenProperFaceAffineFlagMap m G v).1 a := by
    rw [hcoord]
    exact boundarySevenStrictFlagTail_pos k F w j hj
  let s : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun l ↦ a ∈ (G.obj l).1)
  have hs : s.Nonempty := by
    by_contra hs0
    have hnone : ∀ l : Fin (m + 1), a ∉ (G.obj l).1 := by
      intro l hal
      apply hs0
      exact ⟨l, by simp [s, hal]⟩
    rw [boundarySevenProperFaceAffineFlagMap_apply_eq_sum] at hcoordpos
    simp [hnone] at hcoordpos
  let q : Fin (m + 1) := s.min' hs
  have hqmem : a ∈ (G.obj q).1 := by
    have := s.min'_mem hs
    simpa [s, q] using this
  have haG : ∀ l : Fin (m + 1), (a ∈ (G.obj l).1 ↔ q ≤ l) := by
    intro l
    constructor
    · intro hal
      apply Finset.min'_le s l
      simp [s, hal]
    · intro hql
      exact boundarySevenStrictFlag_obj_mono m G hql hqmem
  have hqcoord := boundarySevenStrictFlag_levelVertex_coordinate m G v q a haG
  have htailqpos : 0 < boundarySevenStrictFlagTail m G v q := by
    rw [← hqcoord]
    exact hcoordpos
  let pset : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun l ↦ q ≤ l ∧ 0 < v l)
  have hpset : pset.Nonempty := by
    rw [boundarySevenStrictFlagTail] at htailqpos
    have hex := (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (fun l hl ↦ by
      split_ifs
      · exact mul_nonneg (v.2.1 l)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      · exact le_rfl)).mp htailqpos
    obtain ⟨l, hl, hlpos⟩ := hex
    have hql : q ≤ l := by
      by_contra hql
      simp [hql] at hlpos
    have hvl : 0 < v l := by
      rw [if_pos hql] at hlpos
      rcases mul_pos_iff.mp hlpos with hpos | hneg
      · exact hpos.1
      · exact (not_lt_of_ge (v.2.1 l) hneg.1).elim
    exact ⟨l, by simp [pset, hql, hvl]⟩
  let p : Fin (m + 1) := pset.min' hpset
  have hpdata : q ≤ p ∧ 0 < v p := by
    have := pset.min'_mem hpset
    simpa [pset, p] using this
  have htailqp : boundarySevenStrictFlagTail m G v q =
      boundarySevenStrictFlagTail m G v p := by
    rw [boundarySevenStrictFlagTail, boundarySevenStrictFlagTail]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hpl : p ≤ l
    · simp [hpl, hpdata.1.trans hpl]
    · by_cases hql : q ≤ l
      · have hvlnpos : ¬ 0 < v l := by
          intro hvl
          have hlmem : l ∈ pset := by simp [pset, hql, hvl]
          exact hpl (Finset.min'_le pset l hlmem)
        have hvl0 : v l = 0 := le_antisymm (le_of_not_gt hvlnpos) (v.2.1 l)
        simp [hql, hpl, hvl0]
      · simp [hql, hpl]
  refine ⟨p, hpdata.2, ?_⟩
  apply Subtype.ext
  have htails : boundarySevenStrictFlagTail k F w j =
      boundarySevenStrictFlagTail m G v p := by
    rw [← htailqp, ← hqcoord, hcoord]
  rw [boundarySevenStrictFlag_face_eq_superlevel k F w j hj,
    boundarySevenStrictFlag_face_eq_superlevel m G v p hpdata.2]
  apply Finset.filter_congr
  intro x hx
  rw [htails]
  rw [congrArg (fun z : StandardSimplexBoundary 7 ↦ z.1 x) h]

/-- Cross-flag invariant: under equality of affine points, every positive face of either flag is
literally a coordinate superlevel set of the common point. -/
public theorem boundarySevenStrictFlag_overlap_positive_faces_superlevel
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v) :
    (∀ j, 0 < w j →
      (F.obj j).1 = Finset.univ.filter (fun a : Fin 8 ↦
        boundarySevenStrictFlagTail k F w j ≤
          (boundarySevenProperFaceAffineFlagMap m G v).1 a)) ∧
    (∀ l, 0 < v l →
      (G.obj l).1 = Finset.univ.filter (fun a : Fin 8 ↦
        boundarySevenStrictFlagTail m G v l ≤
          (boundarySevenProperFaceAffineFlagMap k F w).1 a)) := by
  constructor
  · intro j hj
    rw [boundarySevenStrictFlag_face_eq_superlevel k F w j hj, h]
  · intro l hl
    rw [boundarySevenStrictFlag_face_eq_superlevel m G v l hl, ← h]

/-- Positive faces occurring in two equal affine strict-flag presentations are comparable.
This proves that their union is again a chain, the finite-order fact needed to construct a
common refinement. -/
public theorem boundarySevenStrictFlag_overlap_positive_faces_comparable
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v)
    (j : Fin (k + 1)) (l : Fin (m + 1))
    (hj : 0 < w j) (hl : 0 < v l) :
    F.obj j ≤ G.obj l ∨ G.obj l ≤ F.obj j := by
  have hF := boundarySevenStrictFlag_face_eq_superlevel k F w j hj
  have hG := boundarySevenStrictFlag_face_eq_superlevel m G v l hl
  have hcoord (a : Fin 8) :
      (boundarySevenProperFaceAffineFlagMap k F w).1 a =
        (boundarySevenProperFaceAffineFlagMap m G v).1 a :=
    congrArg (fun z : StandardSimplexBoundary 7 ↦ z.1 a) h
  rcases le_total (boundarySevenStrictFlagTail k F w j)
      (boundarySevenStrictFlagTail m G v l) with htail | htail
  · right
    change (G.obj l).1 ⊆ (F.obj j).1
    rw [hF, hG]
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hcoord a]
    exact htail.trans ha
  · left
    change (F.obj j).1 ⊆ (G.obj l).1
    rw [hF, hG]
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← hcoord a]
    exact htail.trans ha

/-- The positive levels in two equal strict-flag presentations are order-isomorphic, and the
isomorphism matches literally equal faces. -/
public theorem boundarySevenStrictFlag_overlap_positiveFaceOrderIso
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (hF : StrictMono F.obj) (hG : StrictMono G.obj)
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v) :
    ∃ e : {j : Fin (k + 1) // 0 < w j} ≃o
        {l : Fin (m + 1) // 0 < v l},
      ∀ j, F.obj j.1 = G.obj (e j).1 := by
  let matchFG : {j : Fin (k + 1) // 0 < w j} →
      {l : Fin (m + 1) // 0 < v l} := fun j ↦
    ⟨Classical.choose
      (boundarySevenStrictFlag_overlap_exists_positive_face_eq
        k m F G w v hF hG h j.1 j.2),
      (Classical.choose_spec
        (boundarySevenStrictFlag_overlap_exists_positive_face_eq
          k m F G w v hF hG h j.1 j.2)).1⟩
  have hmatchFG (j : {j : Fin (k + 1) // 0 < w j}) :
      F.obj j.1 = G.obj (matchFG j).1 :=
    (Classical.choose_spec
      (boundarySevenStrictFlag_overlap_exists_positive_face_eq
        k m F G w v hF hG h j.1 j.2)).2
  let matchGF : {l : Fin (m + 1) // 0 < v l} →
      {j : Fin (k + 1) // 0 < w j} := fun l ↦
    ⟨Classical.choose
      (boundarySevenStrictFlag_overlap_exists_positive_face_eq
        m k G F v w hG hF h.symm l.1 l.2),
      (Classical.choose_spec
        (boundarySevenStrictFlag_overlap_exists_positive_face_eq
          m k G F v w hG hF h.symm l.1 l.2)).1⟩
  have hmatchGF (l : {l : Fin (m + 1) // 0 < v l}) :
      G.obj l.1 = F.obj (matchGF l).1 :=
    (Classical.choose_spec
      (boundarySevenStrictFlag_overlap_exists_positive_face_eq
        m k G F v w hG hF h.symm l.1 l.2)).2
  have hFGGF (l : {l : Fin (m + 1) // 0 < v l}) :
      matchFG (matchGF l) = l := by
    apply Subtype.ext
    apply hG.injective
    exact (hmatchFG (matchGF l)).symm.trans (hmatchGF l).symm
  have hGFFG (j : {j : Fin (k + 1) // 0 < w j}) :
      matchGF (matchFG j) = j := by
    apply Subtype.ext
    apply hF.injective
    exact (hmatchGF (matchFG j)).symm.trans (hmatchFG j).symm
  have hmonoFG : Monotone matchFG := by
    intro i j hij
    apply (OrderEmbedding.ofStrictMono G.obj hG).le_iff_le.mp
    change G.obj (matchFG i).1 ≤ G.obj (matchFG j).1
    rw [← hmatchFG i, ← hmatchFG j]
    exact hF.monotone hij
  have hmonoGF : Monotone matchGF := by
    intro i j hij
    apply (OrderEmbedding.ofStrictMono F.obj hF).le_iff_le.mp
    change F.obj (matchGF i).1 ≤ F.obj (matchGF j).1
    rw [← hmatchGF i, ← hmatchGF j]
    exact hG.monotone hij
  let f : {j : Fin (k + 1) // 0 < w j} →o
      {l : Fin (m + 1) // 0 < v l} := ⟨matchFG, hmonoFG⟩
  let g : {l : Fin (m + 1) // 0 < v l} →o
      {j : Fin (k + 1) // 0 < w j} := ⟨matchGF, hmonoGF⟩
  let e := OrderIso.ofHomInv f g (by
    ext l
    exact congrArg (fun z ↦ z.1.1) (hFGGF l)) (by
    ext j
    exact congrArg (fun z ↦ z.1.1) (hGFFG j))
  exact ⟨e, fun j ↦ hmatchFG j⟩

/-- Exact remaining finite-order packaging: the positive levels of two equal strict-flag
representations must be matched, in order, by equality of their recovered superlevel faces. -/
public def BoundarySevenStrictFlagPositiveFaceOrderMatching : Prop :=
  ∀ (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1))),
    StrictMono F.obj → StrictMono G.obj →
    boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v →
    ∃ e : {j : Fin (k + 1) // 0 < w j} ≃o
        {l : Fin (m + 1) // 0 < v l},
      ∀ j, F.obj j.1 = G.obj (e j).1

public theorem boundarySevenStrictFlagPositiveFaceOrderMatching :
    BoundarySevenStrictFlagPositiveFaceOrderMatching := by
  intro k m F G w v hF hG h
  exact boundarySevenStrictFlag_overlap_positiveFaceOrderIso
    k m F G w v hF hG h

/-- Deleting the zero coordinates of a simplex preserves total mass. -/
public theorem stdSimplex_sum_positive_subtype
    {n : ℕ} (w : stdSimplex ℝ (Fin (n + 1))) :
    ∑ j : {j : Fin (n + 1) // 0 < w j}, w j.1 = 1 := by
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ 0 < w j), w j := by
      symm
      apply Finset.sum_subtype
      intro j
      simp
    _ = ∑ j : Fin (n + 1), w j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hpos : 0 < w j
      · simp [hpos]
      · have hz : w j = 0 := le_antisymm (le_of_not_gt hpos) (w.2.1 j)
        simp [hz]
    _ = 1 := w.2.2

/-- The exact common-restriction endpoint consumed by geometric-realization functoriality. -/
public def BoundarySevenStrictFlagCommonRestriction : Prop :=
  ∀ (k l : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace l)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (l + 1))),
    StrictMono F.obj → StrictMono G.obj →
    boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap l G v →
    ∃ (r : ℕ) (f : SimplexCategory.mk r ⟶ SimplexCategory.mk k)
      (g : SimplexCategory.mk r ⟶ SimplexCategory.mk l)
      (u : stdSimplex ℝ (Fin (r + 1))),
      stdSimplex.map f u = w ∧
      stdSimplex.map g u = v ∧
      BoundarySevenProperFaceNerve.map f.op F =
        BoundarySevenProperFaceNerve.map g.op G

end SphereSixComplex
