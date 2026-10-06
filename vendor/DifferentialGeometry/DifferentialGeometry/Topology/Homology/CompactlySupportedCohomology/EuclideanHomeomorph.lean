module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Euclidean
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.CapNaturality
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Homeomorph
public import DifferentialGeometry.Topology.Homology.CompactHomologyOpenEmbedding

@[expose] public section

noncomputable section

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_homeomorph_of_local_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Type u} [TopologicalSpace Y] (e : E ≃ₜ Y)
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E) (p : E)
    (cY : ∀ K : Compacts Y, integralRelativeHomology (k + m) (K : Set Y)ᶜ)
    (hY : ∀ (K L : Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id Y)
        (show MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ from
          compl_subset_compl.mpr h) (cY L) = cY K)
    (hp : Function.Bijective (fun z : ℤ => z • cY {e p})) :
    ∃! D : integralCompactlySupportedCohomology k Y →ₗ[ℤ] integralSingularHomology m Y,
      (∀ (K : Compacts Y) (α : integralRelativeCohomology k (K : Set Y)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set Y)ᶜ k m α (cY K)) ∧
      Function.Bijective D := by
  let : T2Space Y := e.t2Space
  let f : C(E, Y) := ⟨e, e.continuous⟩
  obtain ⟨cE, ⟨hE, htransport⟩, _⟩ :=
    exists_unique_compact_homology_family_of_isOpenEmbedding (k + m) f e.isOpenEmbedding cY hY
  have hpE : Function.Bijective (fun z : ℤ => z • cE {p}) := by
    have hrel := integralRelativeHomologyMap_bijective_of_isOpenEmbedding
      (k + m) f e.isOpenEmbedding {p}
    apply (hrel.of_comp_iff' (fun z : ℤ => z • cE {p})).mp
    have heq : integralRelativeHomologyMap (k + m) f
        (mapsTo_iff_image_subset.mpr (image_compl_subset e.injective)) ∘
          (fun z : ℤ => z • cE {p}) =
        (fun z : ℤ => z • cY (({p} : Compacts E).map f f.continuous)) := by
      funext z
      rw [Function.comp_apply, map_zsmul, htransport]
      rfl
    rw [heq]
    have hpMap (L : Compacts Y) (hL : L = {e p}) :
        Function.Bijective (fun z : ℤ => z • cY L) := by
      subst L
      exact hp
    exact hpMap _ (Compacts.map_singleton f.continuous p)
  obtain ⟨DE, ⟨hDE, hbijE⟩, _⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq
      k m hkm p cE hE hpE
  obtain ⟨DX, DY, hDX, hDY, hnat⟩ :=
    exists_integralCompactlySupportedCohomology_cap_natural
      k m f e.isOpenEmbedding cE cY hE hY htransport
  have hDXeq : DX = DE := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hDX K α).trans (hDE K α).symm)
  subst DX
  have hhom : Function.Bijective (integralSingularHomologyMap m f) := by
    exact ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) m).obj
      integralSingularCoefficients).mapIso
        (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of Y) e)).toLinearEquiv).bijective
  have hbijY : Function.Bijective DY := by
    apply (Function.Bijective.of_comp_iff DY
      (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective k e)).mp
    have hbij := hhom.comp hbijE
    change Function.Bijective ((integralSingularHomologyMap m f).comp DE) at hbij
    rw [hnat] at hbij
    exact hbij
  refine ⟨DY, ⟨hDY, hbijY⟩, ?_⟩
  intro D hD
  exact integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hD.1 K α).trans (hDY K α).symm)

end DifferentialGeometry.Topology

end

universe u

namespace DifferentialGeometry.Topology

theorem integralCompactlySupportedCohomology_subsingleton_of_homeomorph_of_ne_finrank
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Type u} [TopologicalSpace Y] (e : E ≃ₜ Y) (n : ℕ)
    (hn : n ≠ Module.finrank ℝ E) :
    Subsingleton (integralCompactlySupportedCohomology n Y) := by
  let _ := integralCompactlySupportedCohomology_subsingleton_of_ne_finrank n E hn
  exact (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective
    n e.symm).injective.subsingleton

end DifferentialGeometry.Topology
