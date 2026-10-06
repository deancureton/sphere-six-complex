module

public import DifferentialGeometry.Topology.Homology.Punctures.ChartDiskRetract
public import DifferentialGeometry.Topology.Homology.Punctures.DiskExcision
public import DifferentialGeometry.Topology.Homology.Punctures.PuncturedAcyclic
public import DifferentialGeometry.Topology.Homology.Punctures.FundamentalClass
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing

@[expose] public section

open CategoryTheory Limits Set
open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Topology.SingularPair

section chartDisks

variable {n : ℕ} {M : Type u} {e₀ e₁ : Disk n → M}

theorem range_subset_compl_image_diskInterior (hdisj : Disjoint (range e₀) (range e₁)) :
    range e₀ ⊆ (e₁ '' diskInterior n)ᶜ :=
  fun _ hx h => Set.disjoint_left.1 hdisj hx (image_subset_range _ _ h)

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem contractibleSpace_preimage_val_range (h₀ : isChartDisk e₀)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    ContractibleSpace (Subtype.val ⁻¹' (range e₀) : Set ((e₁ '' diskInterior n)ᶜ : Set M)) :=
  have := h₀.contractibleSpace_range
  (homeomorphPreimageVal (range_subset_compl_image_diskInterior hdisj)).contractibleSpace

variable [CompactSpace M]

theorem acyclic_compl_image_diskInterior_integerCoefficients (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n)
    (h₁ : isChartDisk e₁) :
    acyclic integerCoefficients.{u} (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) :=
  acyclic_of_homotopyEquivInclusion integerCoefficients h₁.isHomotopyEquivInclusion_compl_diskInterior
    (acyclic_compl_singleton_integerCoefficients hn e (e₁ (diskCenter n)))

theorem isZero_relativeHomology_compl_image_diskInterior_range (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n)
    (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁))
    (k : ℕ) :
    IsZero (relativeHomology integerCoefficients.{u} (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M))
      (Subtype.val ⁻¹' (range e₀)) k) :=
  have := contractibleSpace_preimage_val_range h₀ hdisj
  isZero_relativeHomology_of_contractible_of_acyclic' integerCoefficients (acyclic_compl_image_diskInterior_integerCoefficients hn e h₁) k

theorem isZero_relativeHomology_compl_chartDisks (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n)
    (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁))
    (k : ℕ) :
    IsZero (relativeHomology integerCoefficients.{u} (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k) :=
  (isZero_relativeHomology_compl_image_diskInterior_range hn e h₀ h₁ hdisj k).of_iso
    (relativeHomologyTwoDiskComplementIso integerCoefficients h₀ hdisj k)

theorem relHomologyVanishes_compl_chartDisks (hn : 2 ≤ n) (e : M ≃ₕ unitSphere n)
    (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁)) :
    relHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) :=
  fun k => isZero_relativeHomology_compl_chartDisks hn e h₀ h₁ hdisj k

end chartDisks

end DifferentialGeometry.Topology.SingularPair
