module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanCompactHomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.NormedLocalCapDuality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Cap

@[expose] public section
noncomputable section

open TopologicalSpace Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_compact_superset_with_bijective_point_map
    (n : ℕ) (p : E) (K : Compacts E) :
    ∃ L : Compacts E, K ≤ L ∧ ∃ hpL : ({p} : Compacts E) ≤ L,
      Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ ({p}ᶜ : Set E) from
          compl_subset_compl.mpr hpL)) := by
  obtain ⟨r, hr, hKr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 p
  let L : Compacts E := ⟨closedBall p r, isCompact_closedBall p r⟩
  have hp : p ∈ closedBall p r := mem_closedBall_self hr.le
  refine ⟨L, hKr, singleton_subset_iff.mpr hp, ?_⟩
  exact integralRelativeCohomologyMap_boundedStarConvex_bijective n hp
    ((convex_closedBall p r).starConvex hp) isBounded_closedBall

theorem integralRelativeToCompactlySupportedCohomology_singleton_bijective
    (n : ℕ) (p : E) :
    Function.Bijective (integralRelativeToCompactlySupportedCohomology n
      ({p} : Compacts E)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro α hα
    obtain ⟨K, hpK, hK⟩ :=
      (integralRelativeToCompactlySupportedCohomology_eq_zero_iff n {p} α).mp hα
    obtain ⟨L, hKL, hpL, hL⟩ := exists_compact_superset_with_bijective_point_map n p K
    apply hL.injective
    have hcomp := LinearMap.congr_fun (integralRelativeCohomologyMap_comp n
      (ContinuousMap.id E) (ContinuousMap.id E)
      (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKL)
      (show MapsTo (ContinuousMap.id E) (K : Set E)ᶜ ({p}ᶜ : Set E) from
        compl_subset_compl.mpr hpK)) α
    simp only [LinearMap.comp_apply] at hcomp
    rw [hK, map_zero] at hcomp
    exact hcomp.trans (map_zero _).symm
  · intro α
    obtain ⟨K, β, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
    obtain ⟨L, hKL, hpL, hL⟩ := exists_compact_superset_with_bijective_point_map n p K
    obtain ⟨γ, hγ⟩ := hL.surjective (integralRelativeCohomologyMap n
      (ContinuousMap.id E)
      (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKL) β)
    refine ⟨γ, ?_⟩
    rw [← integralRelativeToCompactlySupportedCohomology_map n {p} L hpL γ, hγ]
    exact integralRelativeToCompactlySupportedCohomology_map n K L hKL β

end DifferentialGeometry.Topology

end

noncomputable section

open Metric Module Set

universe u

namespace DifferentialGeometry.Topology

private theorem integralInnerProductRelativeCohomology_subsingleton
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : n ≠ finrank ℝ E) :
    Subsingleton (integralRelativeCohomology n ({0}ᶜ : Set E)) := by
  by_cases hlarge : 2 ≤ finrank ℝ E
  · have hd : finrank ℝ E = (finrank ℝ E - 2) + 2 := by omega
    exact integralEuclideanRelativeCohomology_subsingleton (finrank ℝ E - 2) n E hd (by omega)
  by_cases hzero : finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    rw [hempty]
    let _ := integralSingularCohomology_subsingleton_of_contractibleSpace E n (by omega)
    exact ⟨fun α β => (integralRelativeToAbsoluteCohomologyEmptyEquiv n E).injective
      (Subsingleton.elim _ _)⟩
  have hone : finrank ℝ E = 1 := by omega
  cases n with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      exact integralRelativeCohomology_zero_subsingleton_of_pathConnectedSpace
        ({0}ᶜ : Set E) ⟨(v : E), ne_zero_of_mem_unit_sphere v⟩
  | succ n =>
      cases n with
      | zero => exact (hn hone.symm).elim
      | succ n =>
          let _ := integralSphereCohomology_subsingleton 0 (n + 1) E hone (by omega) (by omega)
          let e := puncturedSpaceSphereHomotopyEquiv E
          have hs :=
            (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
              (n + 1) (by omega) ({0}ᶜ : Set E)).surjective.comp
                (integralSingularCohomologyMap_bijective_of_homotopyEquiv e (n + 1)).surjective
          have hz (α : integralRelativeCohomology (n + 2) ({0}ᶜ : Set E)) : α = 0 := by
            obtain ⟨β, rfl⟩ := hs α
            change integralRelativeCohomologyConnecting (n + 1) ({0}ᶜ : Set E)
              (integralSingularCohomologyMap (n + 1) e.toFun β) = 0
            rw [Subsingleton.elim β 0, map_zero, map_zero]
          exact ⟨fun α β => (hz α).trans (hz β).symm⟩

private theorem integralRelativeCohomology_point_compl_subsingleton
    (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : E) (hn : n ≠ finrank ℝ E) :
    Subsingleton (integralRelativeCohomology n ({p}ᶜ : Set E)) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.symm.toHomeomorph.trans (Homeomorph.addRight p)
  have hp : h 0 = p := by
    change e.symm 0 + p = p
    rw [map_zero, zero_add]
  have hd : n ≠ finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact hn
  let _ := integralInnerProductRelativeCohomology_subsingleton n (EuclideanSpace ℝ ι) hd
  let f : ContinuousMap (EuclideanSpace ℝ ι) E := ⟨h, h.continuous⟩
  have hf : MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ({h 0}ᶜ : Set E) :=
    fun _ hx => h.injective.ne hx
  let g := h.subtype (p := fun x : EuclideanSpace ℝ ι => x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)))
    (q := fun y : E => y ∈ ({h 0}ᶜ : Set E)) (fun x => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap n f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv k
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv k
  have hout : Subsingleton (integralRelativeCohomology n ({h 0}ᶜ : Set E)) :=
    ⟨fun α β => hcoh.injective (Subsingleton.elim _ _)⟩
  rwa [hp] at hout

theorem integralCompactlySupportedCohomology_subsingleton_of_ne_finrank
    (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : n ≠ finrank ℝ E) :
    Subsingleton (integralCompactlySupportedCohomology n E) := by
  let _ := integralRelativeCohomology_point_compl_subsingleton n (0 : E) hn
  have hs := (integralRelativeToCompactlySupportedCohomology_singleton_bijective n (0 : E)).surjective
  have hz (α : integralCompactlySupportedCohomology n E) : α = 0 := by
    obtain ⟨β, rfl⟩ := hs α
    rw [Subsingleton.elim β 0, map_zero]
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end DifferentialGeometry.Topology

end

noncomputable section

open TopologicalSpace Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator
    (p : E) (c : ∀ K : Compacts E, integralRelativeHomology (finrank ℝ E) (K : Set E)ᶜ)
    (hc : ∀ (K L : Compacts E) (h : K ≤ L),
      integralRelativeHomologyMap (finrank ℝ E) (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr h) (c L) = c K)
    (hp : Function.Bijective (fun z : ℤ => z • c {p})) :
    ∃! D : integralCompactlySupportedCohomology (finrank ℝ E) E →ₗ[ℤ]
        integralSingularHomology 0 E,
      (∀ (K : Compacts E) (α : integralRelativeCohomology (finrank ℝ E) (K : Set E)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology (finrank ℝ E) K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ (finrank ℝ E) 0 α (c K)) ∧
      Function.Bijective D := by
  obtain ⟨D, hD, huniq⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap (finrank ℝ E) 0 c hc
  have hcomp : Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
      ({p}ᶜ : Set E) =>
        D (integralRelativeToCompactlySupportedCohomology (finrank ℝ E) {p} α)) := by
    have heq : (fun α : integralRelativeCohomology (finrank ℝ E) ({p}ᶜ : Set E) =>
        D (integralRelativeToCompactlySupportedCohomology (finrank ℝ E) {p} α)) =
        fun α => integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E)
          (finrank ℝ E) 0 α (c {p}) := funext (hD {p})
    rw [heq]
    exact integralLocalHomology_cap_bijective_of_generator p (c {p}) hp
  have hbij : Function.Bijective D :=
    (Function.Bijective.of_comp_iff D
      (integralRelativeToCompactlySupportedCohomology_singleton_bijective
        (finrank ℝ E) p)).mp hcomp
  exact ⟨D, ⟨hD, hbij⟩, fun D' hD' => huniq D' hD'.1⟩

end DifferentialGeometry.Topology

end

noncomputable section

open TopologicalSpace Set Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k m : ℕ) (hkm : k + m = finrank ℝ E) (p : E)
    (c : ∀ K : Compacts E, integralRelativeHomology (k + m) (K : Set E)ᶜ)
    (hc : ∀ (K L : Compacts E) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr h) (c L) = c K)
    (hp : Function.Bijective (fun z : ℤ => z • c {p})) :
    ∃! D : integralCompactlySupportedCohomology k E →ₗ[ℤ] integralSingularHomology m E,
      (∀ (K : Compacts E) (α : integralRelativeCohomology k (K : Set E)ᶜ),
        D (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ k m α (c K)) ∧
      Function.Bijective D := by
  by_cases hm : m = 0
  · subst m
    have hk : k = finrank ℝ E := by simpa only [Nat.add_zero] using hkm
    subst k
    exact exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator
      p c hc hp
  obtain ⟨D, hD, huniq⟩ := exists_unique_integralCompactlySupportedCohomology_cap k m c hc
  let _ := integralCompactlySupportedCohomology_subsingleton_of_ne_finrank k E (by omega)
  let _ := integralSingularHomology_subsingleton_of_contractible m hm E
  have hbij : Function.Bijective D :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun β => ⟨0, Subsingleton.elim _ β⟩⟩
  exact ⟨D, ⟨hD, hbij⟩, fun D' hD' => huniq D' hD'.1⟩

end DifferentialGeometry.Topology

end

noncomputable section

open TopologicalSpace Set Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_integralCompactlySupportedCohomology_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k m : ℕ) (hkm : k + m = finrank ℝ E) :
    ∃ c : ∀ K : Compacts E, integralRelativeHomology (k + m) (K : Set E)ᶜ,
      (∀ (K L : Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id E)
          (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧
      Function.Bijective (fun z : ℤ => z • c {0}) ∧
      ∃! D : integralCompactlySupportedCohomology k E →ₗ[ℤ] integralSingularHomology m E,
        (∀ (K : Compacts E) (α : integralRelativeCohomology k (K : Set E)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology k K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ k m α (c K)) ∧
        Function.Bijective D := by
  have hpoint := exists_integralLocalHomology_generator (0 : E)
  rw [← hkm] at hpoint
  obtain ⟨a, ha⟩ := hpoint
  obtain ⟨c, ⟨hc, hc0⟩, _⟩ :=
    exists_unique_compact_homology_family_of_local_class (k + m) (0 : E) a
  have hgen : Function.Bijective (fun z : ℤ => z • c {0}) := by
    rw [hc0]
    exact ha
  exact ⟨c, hc, hgen,
    exists_unique_integralCompactlySupportedCohomology_cap_bijective_of_local_generator_of_add_eq
      k m hkm (0 : E) c hc hgen⟩

end DifferentialGeometry.Topology

end

noncomputable section

open TopologicalSpace Set Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_integralCompactlySupportedCohomology_top_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ c : ∀ K : Compacts E, integralRelativeHomology (finrank ℝ E) (K : Set E)ᶜ,
      (∀ (K L : Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap (finrank ℝ E) (ContinuousMap.id E)
          (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧
      Function.Bijective (fun z : ℤ => z • c {0}) ∧
      ∃! D : integralCompactlySupportedCohomology (finrank ℝ E) E →ₗ[ℤ]
          integralSingularHomology 0 E,
        (∀ (K : Compacts E) (α : integralRelativeCohomology (finrank ℝ E) (K : Set E)ᶜ),
          D (integralRelativeToCompactlySupportedCohomology (finrank ℝ E) K α) =
            integralRelativeCohomologyCapToAbsolute (K : Set E)ᶜ (finrank ℝ E) 0 α (c K)) ∧
        Function.Bijective D := by
  exact exists_integralCompactlySupportedCohomology_cap_bijective E (finrank ℝ E) 0
    (Nat.add_zero (finrank ℝ E))

end DifferentialGeometry.Topology

end
