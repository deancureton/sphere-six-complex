module

public import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction
public import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
public import DifferentialGeometry.Topology.Manifold.GeneralPosition.PushOff
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing
public import DifferentialGeometry.Topology.Homology.Punctures.DiskComplement
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff ContinuousMap
open Metric Set _root_.Topology unitInterval

theorem nonempty_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] (e : X ≃ₕ Y) : Nonempty X :=
  ⟨e.invFun (Classical.arbitrary Y)⟩

theorem simplyConnectedSpace_sphere {k : ℕ} (hk : 2 ≤ k) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  simplyConnectedSpace_sphere_of_two_le hk

theorem isChartDisk.simplyConnectedSpace_image_diskSphere {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : isChartDisk e) : SimplyConnectedSpace (e '' diskSphere n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  obtain ⟨φ⟩ := he.nonempty_homeomorph_image_diskSphere
  have := simplyConnectedSpace_sphere hk
  exact φ.toHomotopyEquiv.simplyConnectedSpace

theorem isPathConnected_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [PathConnectedSpace M]
    {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    IsPathConnected ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · have hi : (0 : ℕ) < n := by omega
    let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hi⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e₀ w, ?_⟩
    simp only [mem_compl_iff, mem_union, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h₀.injective.mem_set_image, mem_diskInterior] at h
      exact absurd h (by simp [w, hv])
    · exact Set.disjoint_left.1 hdisj ⟨w, rfl⟩ (image_subset_range _ _ h)
  · set γ := PathConnectedSpace.somePath x y with hγ
    obtain ⟨F', hF', hmem, hfix⟩ := exists_push_off_two hn h₀ h₁ hdisj
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩,
      fun t => hmem (0, t)⟩
    · change F' (0, 0) = x
      rw [hfix (0, 0) (by change γ 0 ∈ _; rw [γ.source]; exact hx)]
      exact γ.source
    · change F' (0, 1) = y
      rw [hfix (0, 1) (by change γ 1 ∈ _; rw [γ.target]; exact hy)]
      exact γ.target

theorem exists_homotopy_refl_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) (x : M) (p : Path x x)
    (hp : ∀ t, p t ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ) :
    ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := by
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  obtain ⟨F', hF', hmem, hfix⟩ := exists_push_off_two hn h₀ h₁ hdisj
    (F := fun z : I × I => G z) G.continuous
  have hx : x ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := p.source ▸ hp 0
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by rw [G.apply_zero]; exact hp s)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · change F' (t, 0) = p 0
      rw [hfix (t, 0) (by rw [G.source]; exact hx)]
      rw [G.source, p.source]
    · change F' (t, 1) = p 1
      rw [hfix (t, 1) (by rw [G.target]; exact hx)]
      rw [G.target, p.target]

theorem simplyConnectedSpace_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (Set.range e₀) (Set.range e₁)) :
    SimplyConnectedSpace ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) := by
  change IsSimplyConnected _
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  exact ⟨isPathConnected_compl_chartDisks hn h₀ h₁ hdisj,
    exists_homotopy_refl_compl_chartDisks hn h₀ h₁ hdisj⟩

theorem relHomologyVanishes_compl_chartDisks {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    relHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) :=
  SingularPair.relHomologyVanishes_compl_chartDisks (by omega) e h₀ h₁ hdisj

theorem hcobordism_input_of_homotopy_sphere {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {e₀ e₁ : Disk n → M} (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    SimplyConnectedSpace ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M) ∧
      relHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := simplyConnectedSpace_sphere (by omega : 2 ≤ k + 1)
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  exact ⟨simplyConnectedSpace_compl_chartDisks hn h₀ h₁ hdisj,
    relHomologyVanishes_compl_chartDisks hn e h₀ h₁ hdisj⟩

end DifferentialGeometry.Topology
