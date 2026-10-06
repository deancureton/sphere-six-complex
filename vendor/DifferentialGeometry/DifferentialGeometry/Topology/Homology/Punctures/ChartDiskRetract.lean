module

public import DifferentialGeometry.Topology.Continuous.ClosedCover
public import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction
public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric Set _root_.Topology unitInterval
open scoped ContinuousMap

section Generic

variable {X : Type*} [TopologicalSpace X]

theorem isHomotopyEquivInclusion_of_deformation {A B : Set X} (hAB : A ⊆ B) (H : I × X → X)
    (hc : ContinuousOn H (univ ×ˢ B)) (h0 : ∀ x ∈ B, H (0, x) = x)
    (h1 : ∀ x ∈ B, H (1, x) ∈ A) (hB : ∀ t, ∀ x ∈ B, H (t, x) ∈ B)
    (hA : ∀ t, ∀ x ∈ A, H (t, x) = x) : isHomotopyEquivInclusion A B := by
  have hcont : Continuous fun p : I × B => H (p.1, (p.2 : X)) :=
    hc.comp_continuous (by fun_prop) fun p => ⟨mem_univ _, p.2.2⟩
  let r : C(B, A) :=
    ⟨fun x => ⟨H (1, x), h1 x x.2⟩,
      (hcont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let i : C(A, B) := ⟨fun a => ⟨a, hAB a.2⟩, by fun_prop⟩
  refine ⟨⟨i, r, ?_, ?_⟩, fun _ => rfl⟩
  · have : r.comp i = ContinuousMap.id A := by
      ext a
      exact hA 1 a a.2
    rw [this]
  · refine ContinuousMap.Homotopic.symm ⟨?_⟩
    exact
      { toFun := fun p => ⟨H (p.1, p.2), hB p.1 p.2 p.2.2⟩
        continuous_toFun := hcont.subtype_mk _
        map_zero_left := fun x => Subtype.ext (h0 x x.2)
        map_one_left := fun _ => rfl }

end Generic

section Disk

variable {n : ℕ}

def diskCenter (n : ℕ) : Disk n := ⟨0, mem_closedBall_self zero_le_one⟩

@[simp] theorem coe_diskCenter : ((diskCenter n : Disk n) : EuclideanSpace ℝ (Fin n)) = 0 := rfl

theorem diskCenter_mem_diskInterior : diskCenter n ∈ diskInterior n := by
  rw [mem_diskInterior, coe_diskCenter, norm_zero]
  exact zero_lt_one

def halfDisk (n : ℕ) : Set (Disk n) := {v | ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2}

theorem mem_halfDisk {v : Disk n} : v ∈ halfDisk n ↔ ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 :=
  Iff.rfl

theorem halfDisk_eq_preimage :
    halfDisk n = Subtype.val ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
  ext v
  simp [mem_halfDisk]

theorem halfDisk_subset_diskInterior : halfDisk n ⊆ diskInterior n := fun v hv =>
  mem_diskInterior.2 (by rw [mem_halfDisk] at hv; linarith)

theorem image_halfDisk_subset_image_diskInterior {M : Type*} (e : Disk n → M) :
    e '' halfDisk n ⊆ e '' diskInterior n :=
  image_mono halfDisk_subset_diskInterior

theorem isClosed_halfDisk : IsClosed (halfDisk n) :=
  isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

instance compactSpace_disk : CompactSpace (Disk n) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)

theorem isCompact_halfDisk : IsCompact (halfDisk n) := isClosed_halfDisk.isCompact

theorem contractibleSpace_disk : ContractibleSpace (Disk n) :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩

theorem norm_radialProj_le_one (v : EuclideanSpace ℝ (Fin n)) : ‖radialProj v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [radialProj, hv]
  · exact (norm_radialProj hv).le

noncomputable def annulusDeform (n : ℕ) (p : I × Disk n) : Disk n :=
  ⟨(1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n)) +
      (p.1 : ℝ) • radialProj (p.2 : EuclideanSpace ℝ (Fin n)), by
    rw [mem_closedBall_zero_iff]
    calc ‖(1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n)) +
          (p.1 : ℝ) • radialProj (p.2 : EuclideanSpace ℝ (Fin n))‖
        ≤ ‖(1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n))‖ +
          ‖(p.1 : ℝ) • radialProj (p.2 : EuclideanSpace ℝ (Fin n))‖ := norm_add_le _ _
      _ = (1 - (p.1 : ℝ)) * ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ +
          (p.1 : ℝ) * ‖radialProj (p.2 : EuclideanSpace ℝ (Fin n))‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (one_minus_nonneg _),
          Real.norm_of_nonneg (nonneg _)]
      _ ≤ (1 - (p.1 : ℝ)) * 1 + (p.1 : ℝ) * 1 := by
        gcongr
        · exact one_minus_nonneg _
        · exact mem_closedBall_zero_iff.1 p.2.2
        · exact nonneg _
        · exact norm_radialProj_le_one _
      _ = 1 := by ring⟩

@[simp] theorem coe_annulusDeform (p : I × Disk n) :
    (annulusDeform n p : EuclideanSpace ℝ (Fin n)) =
      (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n)) +
        (p.1 : ℝ) • radialProj (p.2 : EuclideanSpace ℝ (Fin n)) := rfl

theorem annulusDeform_zero (v : Disk n) : annulusDeform n (0, v) = v :=
  Subtype.ext (by simp)

theorem annulusDeform_of_norm_eq_one {t : I} {v : Disk n}
    (hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1) : annulusDeform n (t, v) = v := by
  apply Subtype.ext
  rw [coe_annulusDeform, radialProj_of_norm_eq_one hv, ← add_smul, sub_add_cancel, one_smul]

theorem norm_annulusDeform (t : I) {v : Disk n} (hv : (v : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    ‖(annulusDeform n (t, v) : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * ‖(v : EuclideanSpace ℝ (Fin n))‖ + t := by
  have hn : 0 < ‖(v : EuclideanSpace ℝ (Fin n))‖ := norm_pos_iff.2 hv
  have hnn : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ‖(v : EuclideanSpace ℝ (Fin n))‖⁻¹ := by
    have := one_minus_nonneg t
    have := nonneg t
    positivity
  rw [coe_annulusDeform, radialProj, smul_smul, ← add_smul, norm_smul, Real.norm_of_nonneg hnn,
    add_mul, mul_assoc, inv_mul_cancel₀ hn.ne', mul_one]

theorem norm_le_norm_annulusDeform (t : I) {v : Disk n}
    (hv : (v : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ ‖(annulusDeform n (t, v) : EuclideanSpace ℝ (Fin n))‖ := by
  rw [norm_annulusDeform t hv]
  have h1 := mem_closedBall_zero_iff.1 v.2
  have h2 := nonneg t
  nlinarith

theorem norm_annulusDeform_one {v : Disk n} (hv : (v : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    ‖(annulusDeform n (1, v) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [norm_annulusDeform 1 hv]
  simp

theorem continuousOn_annulusDeform (n : ℕ) :
    ContinuousOn (annulusDeform n) {p : I × Disk n | (p.2 : EuclideanSpace ℝ (Fin n)) ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_induced_rng.2 ?_
  have h1 : Continuous fun q : {p : I × Disk n | (p.2 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      ((q : I × Disk n).2 : EuclideanSpace ℝ (Fin n)) := by fun_prop
  have h2 : Continuous fun q : {p : I × Disk n | (p.2 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      ((q : I × Disk n).1 : ℝ) := by fun_prop
  exact ((continuous_const.sub h2).smul h1).add
    (h2.smul (continuous_radialProj_comp h1 fun q => q.2))

end Disk

section ChartDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {e : Disk n → M}

noncomputable def isChartDisk.rangeHomeomorph (he : isChartDisk e) : Disk n ≃ₜ range e :=
  he.isClosedEmbedding.isEmbedding.toHomeomorph

@[simp] theorem isChartDisk.rangeHomeomorph_symm_apply (he : isChartDisk e) (v : Disk n) :
    he.rangeHomeomorph.symm ⟨e v, mem_range_self v⟩ = v :=
  _root_.Topology.IsEmbedding.toHomeomorph_symm_apply _ v

noncomputable def isChartDisk.annulusHomotopy (he : isChartDisk e) (p : I × M) : M := by
  classical
  exact if hx : p.2 ∈ range e then
    e (annulusDeform n (p.1, he.rangeHomeomorph.symm ⟨p.2, hx⟩)) else p.2

theorem isChartDisk.annulusHomotopy_apply (he : isChartDisk e) (t : I) (v : Disk n) :
    he.annulusHomotopy (t, e v) = e (annulusDeform n (t, v)) := by
  simp [isChartDisk.annulusHomotopy, mem_range_self v]

theorem isChartDisk.annulusHomotopy_of_notMem (he : isChartDisk e) (t : I) {x : M}
    (hx : x ∉ range e) : he.annulusHomotopy (t, x) = x := by
  simp [isChartDisk.annulusHomotopy, hx]

theorem isChartDisk.annulusHomotopy_zero (he : isChartDisk e) (x : M) :
    he.annulusHomotopy (0, x) = x := by
  by_cases hx : x ∈ range e
  · obtain ⟨v, rfl⟩ := hx
    rw [he.annulusHomotopy_apply, annulusDeform_zero]
  · exact he.annulusHomotopy_of_notMem 0 hx

theorem isChartDisk.annulusHomotopy_of_notMem_image_diskInterior (he : isChartDisk e) (t : I)
    {x : M} (hx : x ∉ e '' diskInterior n) : he.annulusHomotopy (t, x) = x := by
  by_cases hx' : x ∈ range e
  · obtain ⟨v, rfl⟩ := hx'
    rw [he.injective.mem_set_image, mem_diskInterior, not_lt] at hx
    rw [he.annulusHomotopy_apply,
      annulusDeform_of_norm_eq_one (le_antisymm (mem_closedBall_zero_iff.1 v.2) hx)]
  · exact he.annulusHomotopy_of_notMem t hx'

theorem isChartDisk.continuousOn_annulusHomotopy (he : isChartDisk e) {S : Set (Disk n)}
    (hS : ∀ v ∈ S, (v : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    ContinuousOn he.annulusHomotopy (univ ×ˢ (e '' S)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmem : ∀ q : ↥((univ : Set I) ×ˢ (e '' S)), (q : I × M).2 ∈ range e := by
    intro q
    have h := q.2
    exact image_subset_range e S h.2
  have heq : ((univ : Set I) ×ˢ (e '' S)).domRestrict he.annulusHomotopy =
      fun q : ↥((univ : Set I) ×ˢ (e '' S)) =>
        e (annulusDeform n ((q : I × M).1, he.rangeHomeomorph.symm ⟨(q : I × M).2, hmem q⟩)) := by
    funext q
    simp [domRestrict, isChartDisk.annulusHomotopy, hmem q]
  rw [heq]
  refine he.continuous.comp ((continuousOn_annulusDeform n).comp_continuous ?_ ?_)
  · exact (by fun_prop : Continuous fun q : ↥((univ : Set I) ×ˢ (e '' S)) => (q : I × M).1).prodMk
      (he.rangeHomeomorph.symm.continuous.comp ((by fun_prop :
        Continuous fun q : ↥((univ : Set I) ×ˢ (e '' S)) => (q : I × M).2).subtype_mk hmem))
  · intro q
    obtain ⟨v, hv, hq⟩ := q.2.2
    have : (⟨(q : I × M).2, hmem q⟩ : range e) = ⟨e v, mem_range_self v⟩ := Subtype.ext hq.symm
    change (he.rangeHomeomorph.symm ⟨(q : I × M).2, hmem q⟩ : EuclideanSpace ℝ (Fin n)) ≠ 0
    rw [this, he.rangeHomeomorph_symm_apply]
    exact hS v hv

theorem isChartDisk.isHomotopyEquivInclusion_annulus (he : isChartDisk e) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {B : Set M} (hB₁ : e '' {v | ρ < ‖(v : EuclideanSpace ℝ (Fin n))‖} ⊆ B)
    (hB₂ : Disjoint B (e '' {v | ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ ρ})) :
    isHomotopyEquivInclusion
      (B \ e '' {v | ρ < ‖(v : EuclideanSpace ℝ (Fin n))‖ ∧
        ‖(v : EuclideanSpace ℝ (Fin n))‖ < 1}) B := by
  have hBv : ∀ v : Disk n, e v ∈ B → ρ < ‖(v : EuclideanSpace ℝ (Fin n))‖ := fun v hv =>
    not_le.1 fun h => Set.disjoint_left.1 hB₂ hv ⟨v, h, rfl⟩
  have hne : ∀ v : Disk n, e v ∈ B → (v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro v hv h
    have := hBv v hv
    rw [h, norm_zero] at this
    exact absurd hρ (not_le.2 this)
  have hpres : ∀ t, ∀ x ∈ B, he.annulusHomotopy (t, x) ∈ B := by
    intro t x hx
    by_cases hx' : x ∈ range e
    · obtain ⟨v, rfl⟩ := hx'
      rw [he.annulusHomotopy_apply]
      exact hB₁ ⟨_, lt_of_lt_of_le (hBv v hx) (norm_le_norm_annulusDeform t (hne v hx)), rfl⟩
    · rw [he.annulusHomotopy_of_notMem t hx']
      exact hx
  refine isHomotopyEquivInclusion_of_deformation sdiff_subset he.annulusHomotopy ?_
    (fun x _ => he.annulusHomotopy_zero x) ?_ hpres ?_
  · refine continuousOn_of_isClosed_cover
      (s := univ ×ˢ (e '' {v | ρ ≤ ‖(v : EuclideanSpace ℝ (Fin n))‖}))
      (t := univ ×ˢ (e '' diskInterior n)ᶜ) ?_ ?_ ?_ ?_ ?_
    · exact isClosed_univ.prod (he.isClosedEmbedding.isClosedMap _
        (isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)))
    · exact isClosed_univ.prod he.isOpen_image_diskInterior.isClosed_compl
    · rintro ⟨t, x⟩ ⟨-, hx⟩
      by_cases h : x ∈ e '' diskInterior n
      · obtain ⟨v, -, rfl⟩ := h
        exact Or.inl ⟨mem_univ _, v, (hBv v hx).le, rfl⟩
      · exact Or.inr ⟨mem_univ _, h⟩
    · refine (he.continuousOn_annulusHomotopy (S := {v | e v ∈ B}) hne).mono ?_
      rintro ⟨t, x⟩ ⟨⟨-, hxB⟩, -, v, -, rfl⟩
      exact ⟨mem_univ _, v, hxB, rfl⟩
    · refine continuous_snd.continuousOn.congr ?_
      rintro ⟨t, x⟩ ⟨-, -, hx⟩
      exact he.annulusHomotopy_of_notMem_image_diskInterior t hx
  · intro x hx
    refine ⟨hpres 1 x hx, ?_⟩
    by_cases hx' : x ∈ range e
    · obtain ⟨v, rfl⟩ := hx'
      rw [he.annulusHomotopy_apply, he.injective.mem_set_image]
      intro h
      exact h.2.ne (norm_annulusDeform_one (hne v hx))
    · rw [he.annulusHomotopy_of_notMem 1 hx']
      exact fun h => hx' (image_subset_range _ _ h)
  · rintro t x ⟨hxB, hx⟩
    by_cases hx' : x ∈ e '' diskInterior n
    · obtain ⟨v, hv, rfl⟩ := hx'
      exact absurd ⟨v, ⟨hBv v hxB, mem_diskInterior.1 hv⟩, rfl⟩ hx
    · exact he.annulusHomotopy_of_notMem_image_diskInterior t hx'

theorem isChartDisk.isHomotopyEquivInclusion_compl_diskInterior (he : isChartDisk e) :
    isHomotopyEquivInclusion ((e '' diskInterior n)ᶜ) ({e (diskCenter n)}ᶜ) := by
  have h := he.isHomotopyEquivInclusion_annulus (ρ := 0) le_rfl (B := {e (diskCenter n)}ᶜ) ?_ ?_
  · convert h using 1
    ext x
    simp only [mem_sdiff, mem_compl_iff, mem_singleton_iff]
    constructor
    · intro hx
      refine ⟨fun h => hx ⟨diskCenter n, diskCenter_mem_diskInterior, h.symm⟩, ?_⟩
      rintro ⟨v, hv, rfl⟩
      exact hx ⟨v, mem_diskInterior.2 hv.2, rfl⟩
    · rintro ⟨h1, h2⟩ ⟨v, hv, rfl⟩
      rw [mem_diskInterior] at hv
      by_cases hv0 : (v : EuclideanSpace ℝ (Fin n)) = 0
      · exact h1 (congrArg e (Subtype.ext hv0))
      · exact h2 ⟨v, ⟨norm_pos_iff.2 hv0, hv⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩ h
    rw [mem_singleton_iff] at h
    have := congrArg (fun w : Disk n => ‖(w : EuclideanSpace ℝ (Fin n))‖) (he.injective h)
    simp only [coe_diskCenter, norm_zero] at this
    have hv' : 0 < ‖(v : EuclideanSpace ℝ (Fin n))‖ := hv
    rw [this] at hv'
    exact lt_irrefl 0 hv'
  · rw [Set.disjoint_left]
    rintro x hx ⟨v, hv, rfl⟩
    apply hx
    rw [mem_singleton_iff]
    exact congrArg e (Subtype.ext (norm_le_zero_iff.1 hv))

omit [T2Space M] in
theorem isChartDisk.isCompact_image_halfDisk (he : isChartDisk e) :
    IsCompact (e '' halfDisk n) :=
  isCompact_halfDisk.image he.continuous

theorem isChartDisk.isClosed_image_halfDisk (he : isChartDisk e) :
    IsClosed (e '' halfDisk n) :=
  he.isCompact_image_halfDisk.isClosed

theorem isHomotopyEquivInclusion_compl_halfDisk_union {e₀ e₁ : Disk n → M}
    (h₀ : isChartDisk e₀) (hdisj : Disjoint (range e₀) (range e₁)) :
    isHomotopyEquivInclusion ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ)
      ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ) := by
  have h := h₀.isHomotopyEquivInclusion_annulus (ρ := 1 / 2) (by norm_num)
    (B := (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ) ?_ ?_
  · convert h using 1
    ext x
    simp only [mem_sdiff, mem_compl_iff, mem_union, not_or]
    constructor
    · rintro ⟨hU0, hU1⟩
      refine ⟨⟨fun h => hU0 (image_halfDisk_subset_image_diskInterior e₀ h), hU1⟩, ?_⟩
      rintro ⟨v, hv, rfl⟩
      exact hU0 ⟨v, mem_diskInterior.2 hv.2, rfl⟩
    · rintro ⟨⟨hH, hU1⟩, hann⟩
      refine ⟨?_, hU1⟩
      rintro ⟨v, hv, rfl⟩
      rw [mem_diskInterior] at hv
      by_cases h : ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2
      · exact hH ⟨v, h, rfl⟩
      · exact hann ⟨v, ⟨not_le.1 h, hv⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩ h
    rcases h with h | h
    · rw [h₀.injective.mem_set_image, mem_halfDisk] at h
      exact absurd hv (not_lt.2 h)
    · exact Set.disjoint_left.1 hdisj (mem_range_self v) (image_subset_range _ _ h)
  · exact disjoint_compl_left.mono_right subset_union_left

theorem isChartDisk.isHomotopyEquivInclusion_image_diskSphere (he : isChartDisk e) :
    isHomotopyEquivInclusion (e '' diskSphere n) (range e \ e '' halfDisk n) := by
  have h := he.isHomotopyEquivInclusion_annulus (ρ := 1 / 2) (by norm_num)
    (B := range e \ e '' halfDisk n) ?_ ?_
  · convert h using 1
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_diskSphere] at hv
      refine ⟨⟨mem_range_self _, fun h => ?_⟩, fun h => ?_⟩
      · rw [he.injective.mem_set_image, mem_halfDisk] at h
        linarith
      · rw [he.injective.mem_set_image] at h
        exact h.2.ne hv
    · rintro ⟨⟨⟨v, rfl⟩, hH⟩, hann⟩
      refine ⟨v, mem_diskSphere.2 ?_, rfl⟩
      have h1 : ¬ ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 := fun h => hH ⟨v, h, rfl⟩
      have h2 : ¬ (1 / 2 < ‖(v : EuclideanSpace ℝ (Fin n))‖ ∧
          ‖(v : EuclideanSpace ℝ (Fin n))‖ < 1) := fun h => hann ⟨v, h, rfl⟩
      have hle := mem_closedBall_zero_iff.1 v.2
      exact le_antisymm hle (not_lt.1 (not_and.1 h2 (not_le.1 h1)))
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨mem_range_self v, fun h => ?_⟩
    rw [he.injective.mem_set_image, mem_halfDisk] at h
    exact absurd hv (not_lt.2 h)
  · exact disjoint_sdiff_left

theorem isChartDisk.contractibleSpace_range (he : isChartDisk e) :
    ContractibleSpace (range e) :=
  have := contractibleSpace_disk (n := n)
  he.rangeHomeomorph.symm.contractibleSpace

end ChartDisk

end DifferentialGeometry.Topology
