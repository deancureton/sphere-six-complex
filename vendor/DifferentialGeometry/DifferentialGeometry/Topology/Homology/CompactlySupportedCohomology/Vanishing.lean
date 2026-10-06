module

public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.MayerVietoris
public import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.DirectedUnion
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CohomologyVanishing

@[expose] public section

noncomputable section

open Set

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralCompactlySupportedCohomology_subsingleton_of_isEmpty
    [IsEmpty X] (n : ℕ) : Subsingleton (integralCompactlySupportedCohomology n X) := by
  let _ := integralSingularCohomology_subsingleton_of_isEmpty X n
  exact (integralCompactlySupportedToSingularCohomology_bijective n).injective.subsingleton

variable [T2Space X]

theorem integralCompactlySupportedCohomology_subsingleton_union
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [Subsingleton (integralCompactlySupportedCohomology n U)]
    [Subsingleton (integralCompactlySupportedCohomology n V)]
    [Subsingleton (integralCompactlySupportedCohomology (n + 1) ↥(U ∩ V))] :
    Subsingleton (integralCompactlySupportedCohomology n ↥(U ∪ V)) := by
  apply (subsingleton_iff_forall_eq 0).mpr
  intro α
  obtain ⟨a, b, hab⟩ :=
    (integralCompactlySupportedCohomology_mayerVietoris_exact_union n U V hU hV α).mp
      (Subsingleton.elim _ _)
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0, map_zero, map_zero, add_zero] at hab
  exact hab.symm

theorem integralCompactlySupportedCohomology_subsingleton_of_directed_open_cover
    {ι : Type v} (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = univ)
    (hvan : ∀ i, Subsingleton (integralCompactlySupportedCohomology n (U i))) :
    Subsingleton (integralCompactlySupportedCohomology n X) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ : IsEmpty X := ⟨fun x => by
      have hx : x ∈ ⋃ i, U i := hcover ▸ mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact isEmptyElim i⟩
    exact integralCompactlySupportedCohomology_subsingleton_of_isEmpty n
  | inr hι =>
    apply (subsingleton_iff_forall_eq 0).mpr
    intro α
    obtain ⟨i, β, rfl⟩ :=
      integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover
        n U hU hdir hcover α
    let _ := hvan i
    rw [Subsingleton.elim β 0, map_zero]

end DifferentialGeometry.Topology

end
