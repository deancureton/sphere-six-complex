module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldCompactHomology
public import DifferentialGeometry.Topology.Homology.LocalOrientation
public import DifferentialGeometry.Topology.Homology.EuclideanLocalTop
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

noncomputable section

open Bundle Set TopologicalSpace Module
open scoped Manifold

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_compact_homology_family_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃! c : ∀ K : Compacts X, integralRelativeHomology n (K : Set X)ᶜ,
      (∀ (K L : Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      ∀ (K : Compacts X) (x : X) (hx : x ∈ K),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) (c K) = μ x := by
  have hex (K : Compacts X) := exists_unique_compact_class_of_locally_realized_family
    (E := E) n hn (K : Set X) K.isCompact μ (fun x _ => by
      obtain ⟨L, hL, hx, a, ha⟩ := hlocal x
      exact ⟨L, hL, hx, a, fun y hy => ha y hy.2⟩)
  choose c hc huniq using hex
  refine ⟨c, ⟨?_, hc⟩, ?_⟩
  · intro K L hKL
    apply huniq K
    intro x hx
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X)
      (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr hKL)
      (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx))) (c L)
    exact hcomp.symm.trans (hc L x (hKL hx))
  · intro d hd
    funext K
    exact huniq K (d K) (hd.2 K)

theorem exists_compact_homology_family_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M] :
    ∃ c : ∀ K : Compacts M, integralRelativeHomology (Module.finrank ℝ E) (K : Set M)ᶜ,
      (∀ (K L : Compacts M) (h : K ≤ L),
        integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
          (show (L : Set M)ᶜ ⊆ (K : Set M)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      ∀ p : M, Function.Bijective (fun z : ℤ => z • c {p}) := by
  let p := Classical.arbitrary M
  let ω := (Module.finBasis ℝ E).orientation
  let ωp := Orientation.map (Fin (Module.finrank ℝ E))
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using
        mem_chart_source E p)).symm.toLinearEquiv ω
  obtain ⟨o, _, hlocal⟩ := exists_tangent_orientation_locality_of_simplyConnected p ωp
  obtain ⟨a, ha⟩ := exists_integralLocalHomology_generator (0 : E)
  obtain ⟨μ, ⟨hmaps, hreal⟩, _⟩ :=
    exists_locally_realized_family_of_tangent_orientation_locality o ω a hlocal
  obtain ⟨c, ⟨hc, hpoints⟩, _⟩ :=
    exists_unique_compact_homology_family_of_locally_realized_family
      (E := E) (Module.finrank ℝ E) le_rfl μ hreal
  refine ⟨c, hc, ?_⟩
  intro x
  have hpoint := hpoints {x} x (by simp)
  rw [integralRelativeHomologyMap_id] at hpoint
  simp only [LinearMap.id_apply] at hpoint
  rw [hpoint]
  exact integralLocalHomology_generator_of_orientation_coordinates
    x x (mem_chart_source E x) (o x) ω a ha (μ x) (hmaps x x (mem_chart_source E x))

end DifferentialGeometry.Topology
