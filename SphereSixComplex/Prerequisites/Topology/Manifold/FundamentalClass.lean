module

public import DifferentialGeometry.Topology.Homology.CompactHomologyFamily
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.RelativeComparison

/-! # Global fundamental classes generate local top homology -/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open CategoryTheory
open scoped Manifold

namespace SphereSixComplex

open DifferentialGeometry.Topology

theorem integralAbsoluteToRelative_surjective_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M] [CompactSpace M] (p : M) :
    Function.Surjective
      (integralAbsoluteToRelative (Module.finrank ℝ E) ({p}ᶜ : Set M)) := by
  obtain ⟨c, hc, hgen⟩ := exists_compact_homology_family_of_simplyConnected (E := E) (M := M)
  let K : Compacts M := ⟨univ, isCompact_univ⟩
  have hK : Function.Surjective
      (integralAbsoluteToRelative (Module.finrank ℝ E) (K : Set M)ᶜ) := by
    change Function.Surjective (integralAbsoluteToRelative _ (univᶜ : Set M))
    rw [compl_univ]
    exact (integralAbsoluteToRelative_empty_bijective M (Module.finrank ℝ E)).surjective
  obtain ⟨a, ha⟩ := hK (c K)
  have hlocal : integralAbsoluteToRelative (Module.finrank ℝ E) ({p}ᶜ : Set M) a = c {p} := by
    have hnat := LinearMap.congr_fun
      (integralAbsoluteToRelative_natural (Module.finrank ℝ E) (ContinuousMap.id M)
        (show MapsTo (ContinuousMap.id M) (K : Set M)ᶜ ({p}ᶜ : Set M) from
          compl_subset_compl.mpr (by intro x hx; trivial))) a
    simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id, LinearMap.id_apply,
      ha, hc {p} K (by intro x hx; trivial)] using hnat
  intro y
  obtain ⟨z, rfl⟩ := (hgen p).surjective y
  refine ⟨z • a, ?_⟩
  exact ((integralAbsoluteToRelative (Module.finrank ℝ E) ({p}ᶜ : Set M)).toAddMonoidHom.map_zsmul
    z a).trans (congrArg (z • ·) hlocal)

theorem epi_relπ_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M] [CompactSpace M] (p : M) :
    Epi (SingularPair.relπ SingularPair.integerCoefficients (TopCat.of M)
      ({p}ᶜ : Set M) (Module.finrank ℝ E)) := by
  let e := IntegralSingularComparison.relativeHomologyIso ({p}ᶜ : Set M) (Module.finrank ℝ E)
  rw [← IntegralSingularComparison.relativeHomologyIso_π]
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact e.toLinearEquiv.surjective.comp
    (integralAbsoluteToRelative_surjective_of_simplyConnected (E := E) p)

end SphereSixComplex
