module

public import DifferentialGeometry.Topology.Homology.Punctures.ChartDiskRetract
public import DifferentialGeometry.Topology.Homology.Relative.HomotopyInvariance
public import DifferentialGeometry.Topology.Homology.Relative.DeltaIso

@[expose] public section

open CategoryTheory Limits Set

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section chartDisks

variable {n : ℕ} {M : Type u}

section sets

variable {e₀ e₁ : Disk n → M}

theorem range_sdiff_halfDisk_subset_compl_union (hdisj : Disjoint (range e₀) (range e₁)) :
    range e₀ \ e₀ '' halfDisk n ⊆ (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ := by
  rintro x ⟨hx, hH⟩ (h | h)
  · exact hH h
  · exact Set.disjoint_left.1 hdisj hx (image_subset_range _ _ h)

theorem compl_union_subset_compl_halfDisk_union :
    (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ ⊆
      (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ :=
  compl_subset_compl.2 (union_subset_union_left _ (image_halfDisk_subset_image_diskInterior e₀))

theorem compl_halfDisk_union_subset_compl :
    (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ ⊆ (e₁ '' diskInterior n)ᶜ :=
  compl_subset_compl.2 subset_union_right

theorem preimage_val_range_sdiff_halfDisk :
    (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n) :
        Set ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M)) =
      Subtype.val ⁻¹' (range e₀) := by
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_sdiff, and_iff_left_iff_imp]
  intro _ h
  exact hx (Or.inl h)

theorem compl_preimage_val_halfDisk_eq :
    ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ : Set ((e₁ '' diskInterior n)ᶜ : Set M)) =
      Subtype.val ⁻¹' (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ := by
  ext ⟨x, hx⟩
  simp only [mem_compl_iff, mem_preimage, mem_union, not_or]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

end sets

section topology

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e₀ e₁ : Disk n → M}

omit [T2Space M] in
theorem image_diskSphere_subset_compl_union (h₀ : isChartDisk e₀)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    e₀ '' diskSphere n ⊆ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := by
  rintro _ ⟨v, hv, rfl⟩ (h | h)
  · rw [h₀.injective.mem_set_image] at h
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv h
  · exact Set.disjoint_left.1 hdisj (mem_range_self v) (image_subset_range _ _ h)

omit [T2Space M] in
theorem image_diskSphere_subset_range_sdiff_halfDisk (h₀ : isChartDisk e₀) :
    e₀ '' diskSphere n ⊆ range e₀ \ e₀ '' halfDisk n := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨mem_range_self v, fun h => ?_⟩
  rw [h₀.injective.mem_set_image, mem_halfDisk] at h
  rw [mem_diskSphere] at hv
  linarith

theorem closure_preimage_val_halfDisk_subset (h₀ : isChartDisk e₀) :
    closure (Subtype.val ⁻¹' (e₀ '' halfDisk n) : Set ((e₁ '' diskInterior n)ᶜ : Set M)) ⊆
      interior (Subtype.val ⁻¹' (range e₀)) := by
  rw [(h₀.isClosed_image_halfDisk.preimage continuous_subtype_val).closure_eq]
  exact (preimage_mono (image_halfDisk_subset_image_diskInterior e₀)).trans
    (interior_maximal (preimage_mono (image_subset_range _ _))
      (h₀.isOpen_image_diskInterior.preimage continuous_subtype_val))

def portPrivate_d8191ebf_relativeHomologyDiskCollarExpansionIso (h₀ : isChartDisk e₀) (hdisj : Disjoint (range e₀) (range e₁)) (k : ℕ) :
    relativeHomology R (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k ≅
      relativeHomology R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n)) k :=
  relativeHomologyIsoOfHomotopyEquivInclusion R (image_diskSphere_subset_compl_union h₀ hdisj)
    (range_sdiff_halfDisk_subset_compl_union hdisj) compl_union_subset_compl_halfDisk_union
    (image_diskSphere_subset_range_sdiff_halfDisk h₀)
    (isHomotopyEquivInclusion_compl_halfDisk_union h₀ hdisj)
    h₀.isHomotopyEquivInclusion_image_diskSphere k

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
def portPrivate_d8191ebf_relativeHomologyHalfDiskRangeIso (k : ℕ) :
    relativeHomology R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n)) k ≅
      relativeHomology R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀)) k :=
  relativeHomologyIsoOfEq R _ preimage_val_range_sdiff_halfDisk k

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
def portPrivate_d8191ebf_relativeHomologyHalfDiskComplementIso (k : ℕ) :
    relativeHomology R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀)) k ≅
      relativeHomology R (TopCat.of ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e₀))) k :=
  (relativeHomologyIsoOfSubtypeSubtype R compl_halfDisk_union_subset_compl (range e₀) k).symm ≪≫
    relativeHomologyIsoOfHomeomorphMemIff R
      (Homeomorph.setCongr
        (s := (Subtype.val ⁻¹' (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (t := ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ : Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        compl_preimage_val_halfDisk_eq.symm)
      (fun _ => by exact Iff.rfl) k

def portPrivate_d8191ebf_relativeHomologyHalfDiskExcisionIso (h₀ : isChartDisk e₀) (k : ℕ) :
    relativeHomology R (TopCat.of ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e₀))) k ≅
      relativeHomology R (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) (Subtype.val ⁻¹' (range e₀)) k :=
  excisionClosedIso R (X := TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M))
    (Subtype.val ⁻¹' (e₀ '' halfDisk n)) (Subtype.val ⁻¹' (range e₀))
    (closure_preimage_val_halfDisk_subset h₀) k

def relativeHomologyTwoDiskComplementIso (h₀ : isChartDisk e₀) (hdisj : Disjoint (range e₀) (range e₁)) (k : ℕ) :
    relativeHomology R (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k ≅
      relativeHomology R (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) (Subtype.val ⁻¹' (range e₀)) k :=
  portPrivate_d8191ebf_relativeHomologyDiskCollarExpansionIso R h₀ hdisj k ≪≫ portPrivate_d8191ebf_relativeHomologyHalfDiskRangeIso R k ≪≫ portPrivate_d8191ebf_relativeHomologyHalfDiskComplementIso R k ≪≫ portPrivate_d8191ebf_relativeHomologyHalfDiskExcisionIso R h₀ k

end topology

end chartDisks

end DifferentialGeometry.Topology.SingularPair

end
