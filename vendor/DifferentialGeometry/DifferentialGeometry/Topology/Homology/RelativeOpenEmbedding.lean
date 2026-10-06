module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

noncomputable section

open CategoryTheory Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Set X) (hK : IsClosed (f '' K)) :
    Function.Bijective (integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
        MapsTo f Kᶜ (f '' K)ᶜ)) := by
  let A : Set Y := (f '' K)ᶜ
  let B : Set Y := range f
  let e : X ≃ₜ B := hf.isEmbedding.toHomeomorph
  let g : ContinuousMap X B := ⟨e, e.continuous⟩
  have hg : MapsTo g Kᶜ (subspaceIntersection A B) := by
    intro x hx
    exact image_compl_subset hf.injective ⟨x, hx, rfl⟩
  have hg' : MapsTo e.symm (subspaceIntersection A B) Kᶜ := by
    intro y hy hx
    apply hy
    refine ⟨e.symm y, hx, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have hgbij : Function.Bijective (integralRelativeHomologyMap n g hg) := by
    let E := integralRelativeHomologyHomeomorphIso n e Kᶜ (subspaceIntersection A B) hg hg'
    exact ⟨(ModuleCat.mono_iff_injective E.hom).mp inferInstance,
      (ModuleCat.epi_iff_surjective E.hom).mp inferInstance⟩
  have hcover : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hy
      exact Or.inr ⟨x, rfl⟩
    · exact Or.inl hy
  have hibij : Function.Bijective (integralRelativeHomologyMap n (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
    let E := integralRelativeOpenExcisionIso n A B hK.isOpen_compl hf.isOpen_range hcover
    exact ⟨(ModuleCat.mono_iff_injective E.hom).mp inferInstance,
      (ModuleCat.epi_iff_surjective E.hom).mp inferInstance⟩
  have heq := integralRelativeHomologyMap_comp n g (singularSubspaceInclusion B)
    hg (subspaceIntersection_mapsTo A B)
  change integralRelativeHomologyMap n f _ = _ at heq
  rw [heq]
  exact hibij.comp hgbij

theorem integralRelativeHomologyMap_bijective_of_isOpenEmbedding [T2Space Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Compacts X) :
    Function.Bijective (integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
        MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ)) :=
  integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image n f hf
    (K : Set X) (K.isCompact.image f.continuous).isClosed

end DifferentialGeometry.Topology

end
